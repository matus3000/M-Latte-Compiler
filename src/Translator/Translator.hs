module Translator.Translator(Translator,
                            setMember,
                            getMember,
                            setVariable,
                            getVariable,
                            declareVariable,
                            universalReference,
                            newTranslatorState,
                            withOpenBlock,
                            withinConditionalBlock,
                            newClass,
                            evalTranslator,
                            MemoryState(..),
                            VariableState) where

import Translator.Definitions
import Translator.TranslatorEnvironment
    ( getFunctionEnvironment,
      getStructureEnvironment,
      StructureEnvironment,
      FunctionEnvironment,
      TranslationEnvironment )

import qualified Translator.TranslatorEnvironment as TE
import Translator.ClassRepresentation(ClassRepresentation(..))
import qualified Translator.ClassRepresentation as TCR
import qualified Data.Functor

import VariableEnvironment(CVariableEnvironment(..), VarEnv(..), newVarEnv)
import qualified VariableEnvironment as VE
import Data.List (foldl')
import Data.Foldable (Foldable(toList))
import Data.Maybe (fromMaybe, fromJust, isNothing)
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import Data.List as DL (find)
import Data.Containers.ListUtils (nubOrd)
import Control.Monad.State.Strict
import Control.Monad.Reader
import IDefinition
import CompilationError
import Control.Monad.Except (throwError, Except)
import CompilationError (SemanticError(SemanticError))


type StateStrMap x = State (DM.Map String x)
data ArrayRepresentation = ArrayRepresentation (DM.Map Int IValue) IValue


data Allocator = Allocator {alNextArray :: Int,
                           alNextStructure :: Int}

allocateArray :: Allocator -> (Allocator, Reference)
allocateArray allocator = (Allocator (alNextArray allocator+ 1) (alNextStructure allocator),
                           alNextArray allocator)
allocateStruct :: Allocator -> (Allocator, Reference)
allocateStruct allocator =(Allocator (alNextArray allocator) (alNextStructure allocator + 1),
                           alNextStructure allocator)
data MemoryState = MemoryState {msArrays :: DM.Map Reference ArrayRepresentation,
                                msStructures :: DM.Map Reference ClassRepresentation,
                                msReferenceToType :: DM.Map Reference String,
                                msAllocator :: Allocator }
type VariableState = VE.VarEnv String (IType, IValue)

type ChangedReferences = DS.Set (Reference, String)

data TranslatorState = TSRoot {memoryState::MemoryState, varState::VariableState} | TSCondition {memoryState::MemoryState, varState::VariableState, referenceTracker :: ChangedReferences}

type Translator = ReaderT TranslationEnvironment (StateT TranslatorState CompilerExcept)

newTranslatorState :: TranslatorState
newTranslatorState = TSRoot (MemoryState DM.empty DM.empty DM.empty (Allocator 0 0)) VE.newVarEnv
throwErrorInContext :: SemanticErrorType -> Translator a
throwErrorInContext errtype  =
  do
    (a,b, pos) <- asks TE.getContext
    throwError $ SemanticError pos errtype

modifyMemoryState :: (MemoryState -> MemoryState) -> Translator ()
modifyMemoryState f = do
  state <- get
  let newMemoryState = f (memoryState state)
      x =case state of
        TSRoot ms ve -> (`TSRoot` ve)
        TSCondition ms ve set -> \x -> TSCondition x ve set
  put (x newMemoryState)

modifyVarState :: (VariableState -> VariableState) -> Translator ()
modifyVarState f = do
  state <- get
  let newVarState = f (varState state)
      constr = case state of
        TSRoot ms ve -> TSRoot ms
        TSCondition ms ve set -> \x -> TSCondition ms x set
  put (constr newVarState)

modifyRefTracker :: (ChangedReferences -> ChangedReferences) -> Translator ()
modifyRefTracker = undefined

newClass :: String -> IValue -> Translator Reference
newClass className defaultValue = do
  case defaultValue of
    Undefined -> return ()
    RunTimeValue -> return ()
    _ -> undefined
  memory <- gets memoryState
  mClassData <- asks $ TE.lookupClass className
  let struct = ClassRepresentation DM.empty (fromJust mClassData) defaultValue
      (allocator', reference) = allocateStruct $ msAllocator memory
      referenceMap = DM.insert reference className $ msReferenceToType memory
      structuresMap = DM.insert reference struct $ msStructures memory
  modifyMemoryState (const (MemoryState (msArrays memory) structuresMap referenceMap allocator'))
  return reference

msModifyReferenceUnsafe :: Reference -> String -> IValue -> MemoryState -> MemoryState
msModifyReferenceUnsafe ref member ivalue (MemoryState arr classes referenceTypes allocator) =
  let x = fromJust $ DM.lookup ref classes
      x' = fromJust $ TCR.setFieldUnsafe member ivalue x
  in
    MemoryState arr (DM.insert ref x' classes) referenceTypes allocator

getMember :: (Int, Int) -> Reference -> String -> Translator (IType, IValue)
getMember pos ref member = do
  memoryState <- gets memoryState
  let object@(ClassRepresentation map sd defaultValue) = fromJust $ DM.lookup ref $ msStructures memoryState
  let memberType = TE.sdFieldType member sd
  case (DM.lookup member map, memberType, defaultValue) of
    (_, Nothing, _) -> throwErrorInContext $ UndefinedField pos member
    (Just x, Just itype, _) -> return (itype, x)
    (Nothing, Just (LClass className), RunTimeValue) -> do
      memberReference <- newClass className RunTimeValue
      let ivalue = OwningReference memberReference
          -- updatedParent = fromJust $ TCR.setField member ivalue object
      modifyMemoryState (msModifyReferenceUnsafe ref member ivalue)
      return (LClass className, ivalue)
    (Nothing, Just itype, defaultValue) -> return (itype, defaultValue)

universalReference :: LType
universalReference = LClass ""

setMember :: (Int,Int) -> Reference -> String -> (IType, IValue) -> Translator ()
setMember pos ref memberName (itype, ivalue) = do
  _ <- getMember pos ref memberName
  memory <- gets memoryState
  let (ClassRepresentation map sd _default) = fromJust $ DM.lookup ref (msStructures memory)
      memberType = TE.sdFieldType memberName sd
      correct :: IType -> Bool
      correct = \x -> (x `same` itype ||
                       case x of
                          LClass s -> itype == universalReference
                          _ -> False)
  case correct <$> memberType of
    Nothing -> throwErrorInContext $ UndefinedField pos memberName
    Just False -> throwErrorInContext $ TypeConflict pos (fromJust memberType) itype
    Just True -> modifyMemoryState (msModifyReferenceUnsafe ref memberName ivalue)

setVariable :: (Int, Int) -> (Int, Int) -> String -> (IType, IValue) -> Translator ()
setVariable varpos eqpos varname (itype', ivalue') = do
  varstate <- gets varState
  let x = varname `VE.lookupVar` varstate
  case x of
    Nothing -> throwErrorInContext (UndefinedVar varpos varname)
    Just (itype, ivalue) -> do
      let correctType = case itype of
            LClass s -> itype `same` itype' || itype' == universalReference
            _ -> itype `same` itype'
      unless correctType (throwErrorInContext $
                           TypeConflict eqpos (cast itype) (cast itype'))
      modifyVarState (VE.setVar varname (itype', ivalue'))
getVariable :: (Int, Int) -> String -> Translator (IType, IValue)
getVariable pos varName = do
  venv <- gets varState
  case varName `lookupVar` venv of
    Nothing -> throwError $ SemanticError pos (UndefinedVar pos varName)
    Just (itype, ivalue) -> case (itype, ivalue) of
      (LClass className, RunTimeValue) -> do
        newReference <-  newClass className RunTimeValue
        let ivalue = OwningReference newReference
        modifyVarState (VE.setVar varName (itype, ivalue))
        return (itype, ivalue)
      _ -> return (itype, ivalue)

declareVariable :: (Int, Int) -> String -> (IType, IValue) -> Translator ()
declareVariable pos id itv@(itype, ivalue)= do
  varstate <- gets varState
  if id `DS.member` head (redeclaredVars varstate)
    then throwErrorInContext $ RedefinitionOfVariable pos pos id
    else do
    modifyVarState (VE.declareVar id itv)

withOpenBlock :: Translator a -> Translator a
withOpenBlock f = do
  modifyVarState VE.openClosure
  res <- f
  modifyVarState VE.closeClosure
  return res

withinConditionalBlock :: Translator a -> Translator a
withinConditionalBlock f = do
  state <- get
  res <- f
  put state
  return res

evalTranslator :: TranslationEnvironment -> TranslatorState -> Translator a -> CompilerExcept a
evalTranslator te ts = flip evalStateT ts . flip runReaderT te
-- setVariables :: [((Int,Int), String, IValue)] -> Translator ()
-- setVariables = undefined
