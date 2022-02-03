{-# LANGUAGE LambdaCase #-}
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
                            castClassUnsafe,
                            setReferenceRecursivelyToRunTime,
                            isReferenceRunTime,
                            isIValueRunTime,
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
import qualified Translator.StructureData as SD

import qualified Data.Functor
import VariableEnvironment(CVariableEnvironment(..), VarEnv(..), newVarEnv)
import qualified VariableEnvironment as VE
import Data.List (foldl')
import Data.Foldable (Foldable(toList))
import Data.Maybe (fromMaybe, fromJust, isNothing, isJust, catMaybes)
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
import Class (Class(className))


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

isTranslatingMethod :: Translator  Bool
isTranslatingMethod = do
  (_, _, _, ms) <- asks TE.getContext
  return $ isJust ms

isReferenceRunTime :: Reference -> Translator Bool
isReferenceRunTime ref = do
  x  <- gets $ fromJust . DM.lookup ref . msStructures . memoryState
  return $ RunTimeValue == TCR.getDefault x

isIValueRunTime :: IValue -> Translator Bool
isIValueRunTime = \case
  IValueInt n -> return False
  IValueBool b -> return False
  IValueString s -> return False
  Null -> return False
  Undefined -> return False
  RunTimeValue -> return True
  OwningReference n -> isReferenceRunTime n

newTranslatorState :: TranslatorState
newTranslatorState = TSRoot (MemoryState DM.empty DM.empty DM.empty (Allocator 0 0)) VE.newVarEnv

throwErrorInContext :: SemanticErrorType -> Translator a
throwErrorInContext errtype  =
  do
    (a,b, pos, _) <- asks TE.getContext
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

castClassUnsafe :: Reference -> String -> Translator ()
castClassUnsafe ref className = do
  memory <- gets memoryState
  mClassData <- asks $ fromJust . TE.lookupClass className
  let old@(ClassRepresentation _map _sd _default) = fromJust $ DM.lookup ref $ msStructures memory
      new = ClassRepresentation _map mClassData _default
      referenceMap = DM.insert ref className $ msReferenceToType memory
      structuresMap = DM.insert ref new $ msStructures memory
  modifyMemoryState (const (MemoryState (msArrays memory) structuresMap referenceMap (msAllocator memory)))

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
  let memberType = SD.lookupField member sd
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

setMember :: (Int,Int) -> Reference -> String -> (IType, IValue) -> Translator ()
setMember pos ref memberName (itype, ivalue) = do
  _ <- getMember pos ref memberName
  memory <- gets memoryState
  let (ClassRepresentation map sd _default) = fromJust $ DM.lookup ref (msStructures memory)
      memberType = SD.lookupField memberName sd
  case memberType of
    Nothing -> throwErrorInContext $ UndefinedField pos memberName
    Just memberType -> do
      isSubClass <- asks $ TE.isSubClass itype memberType
      (_, newval) <- if memberType `same` itype then return (memberType, ivalue)
                     else if isSubClass then castIValue (itype, ivalue) memberType
                     else throwErrorInContext $
                          TypeConflict pos (cast memberType) (cast itype)
      modifyMemoryState (msModifyReferenceUnsafe ref memberName newval)

setReferenceRecursivelyToRunTime :: Reference -> Translator ()
setReferenceRecursivelyToRunTime reference = do
  memory <- gets memoryState
  let (ClassRepresentation structmap sd _default) = fromJust $ DM.lookup reference (msStructures memory)
      refs = foldl (\refs (key, ivalue) -> let
                            mref = case ivalue of
                              OwningReference n -> Just n
                              _ -> Nothing
                              in
                              (mref:refs))
                     []
                     (DM.toList structmap)
      structmap' = DM.empty
      classrepr' = ClassRepresentation structmap' sd RunTimeValue
      references = catMaybes refs
      memory' = MemoryState (msArrays memory) (DM.insert reference classrepr' (msStructures memory))
        (msReferenceToType memory) (msAllocator memory)
  modifyMemoryState (const memory')
  mapM_ setReferenceRecursivelyToRunTime references

castIValue :: (IType,IValue) -> IType -> Translator (IType, IValue)
castIValue (it1, iv) it2 = do
  memory <- gets memoryState
  case (it1, it2) of
    (LClass s1, LClass s2) -> do
      -- case iv of 
        -- OwningReference n -> do
        --   _sd2 <- asks $ fromJust . TE.lookupClass  s2
        --   let old@(ClassRepresentation _map _sd _default )  = fromJust $ DM.lookup n $ msStructures memory
        --       new = ClassRepresentation _map _sd2 _default
        --   (allocator', ref) <- gets (allocateStruct . msAllocator . memoryState)
      return (it2, iv)
        -- _ -> Prelude.error $  "Unexcpected value of "
    (_, _) -> Prelude.error "Cast is not allowed"

setVariable :: (Int, Int) -> (Int, Int) -> String -> (IType, IValue) -> Translator ()
setVariable varpos eqpos varname (itype', ivalue') = do
  varstate <- gets varState
  let x = varname `VE.lookupVar` varstate
  case x of
    Nothing -> throwErrorInContext (UndefinedVar varpos varname)
    Just (itype, ivalue) -> do
      isSubClass <- asks $ TE.isSubClass itype' itype
      newval <- if itype `same` itype' then return (itype', ivalue')
           else if isSubClass then castIValue (itype', ivalue') itype
                else throwErrorInContext $
                           TypeConflict eqpos (cast itype) (cast itype')
      modifyVarState (VE.setVar varname newval)

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

