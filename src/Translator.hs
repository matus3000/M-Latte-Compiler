{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LambdaCase #-}

module Translator(
  programToInternal,
    CompilerExcept,
    IFun(..),
    IBlock(..),
    IStmt(..),
    IExpr(..),
    IItem(..),
    Convertable(..),
    IRelOp(..),
    IAddOp(..),
    IMulOp(..),
    MetaData(..),
    IType,
    ILValue(..),
    Reference,
    stmtsToInternal,
    functionMetaDataNew,
    FunctionMetadata(..),
    IProgram(..),
    IClass(..),
  ) where

import IDefinition hiding (Array)


import CompilationError

import Prelude
import Data.Foldable (Foldable(toList))
import Data.Maybe (fromMaybe, fromJust, isNothing)
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import Data.List as DL (find)
import Data.Containers.ListUtils (nubOrd)

import Control.Monad.Except (Except, throwError, catchError, runExcept, MonadError)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad(void)
import qualified Data.Bifunctor
import Data.Bifunctor (Bifunctor(first))
import qualified Control.Arrow as BiFunctor
import qualified Control.Arrow as Data.BiFunctor

import VariableEnvironment(CVariableEnvironment(..), VarEnv(..), newVarEnv)
import qualified VariableEnvironment as VE
import Data.List (foldl')

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
import Translator.Translator

-- type TranslatorState = (MemoryState, VariableState)
type StateStrMap x = State (DM.Map String x)
data ArrayRepresentation = ArrayRepresentation (DM.Map Int IValue) IValue


-- data Allocator = Allocator {alNextArray :: Int,
--                            alNextStructure :: Int}

-- allocateArray :: Allocator -> (Allocator, Reference)
-- allocateArray allocator = (Allocator (alNextArray allocator+ 1) (alNextStructure allocator),
--                            alNextArray allocator)
-- allocateStruct :: Allocator -> (Allocator, Reference)
-- allocateStruct allocator =(Allocator (alNextArray allocator) (alNextStructure allocator + 1),
--                            alNextStructure allocator)
-- data MemoryState = MemoryState {msArrays :: DM.Map Reference ArrayRepresentation,
--                                 msStructures :: DM.Map Reference ClassRepresentation,
--                                 msReferenceToType :: DM.Map Reference String,
--                                 msAllocator :: Allocator }
-- type VariableState = VE.VarEnv String (IType, IValue)

-- tsInit :: TranslatorState
-- tsInit = (MemoryState DM.empty DM.empty DM.empty (Allocator 0 0), VE.newVarEnv)
-- tsSetMemState :: MemoryState -> TranslatorState  -> TranslatorState
-- tsSetMemState mem (x, y) = (mem, y)
-- tsSetVarState :: VariableState -> TranslatorState  -> TranslatorState
-- tsSetVarState varst (x, s)= (x, varst)
-- tsModifyVarState :: (VariableState -> VariableState) -> TranslatorState -> TranslatorState
-- tsModifyVarState f (mem, vars) = (mem, f vars)
-- tsModifyMemory :: (MemoryState -> MemoryState) -> TranslatorState -> TranslatorState
-- tsModifyMemory f (mem, vars) = (f mem, vars)
-- tsMemory :: TranslatorState -> MemoryState
-- tsMemory (mem, _) = mem
-- tsVarState :: TranslatorState -> VariableState
-- tsVarState (_, var) = var

-- universalReference :: LType
-- universalReference = LClass ""

defaultValue :: IType -> IValue
defaultValue itype = case itype of
  LInt -> IValueInt 0
  LString -> IValueString ""
  LBool -> IValueBool False
  LVoid -> undefined
  LFun lt lts -> undefined
  LArray lt -> Null
  LClass s -> Null
  LGenericClass s lts -> Null

-- type Compiler varEnv = ReaderT TranslationEnvironment  (StateT varEnv CompilerExcept)



lTypeToIType :: LType -> IType
lTypeToIType = id
-- lTypeToIType LInt = DynamicInt
-- lTypeToIType LBool = DynamicBool
-- lTypeToIType LString = DynamicString
-- lTypeToIType _ = undefined


_strle :: IExpr -> IExpr -> IExpr
_strle ie1 ie2 = IApp "_strle" [ie1, ie2]
_strlt :: IExpr -> IExpr -> IExpr
_strlt ie1 ie2 = IApp "_strlt" [ie1, ie2]
_strge :: IExpr -> IExpr -> IExpr
_strge ie1 ie2 = IApp "_strge" [ie1, ie2]
_strgt :: IExpr -> IExpr -> IExpr
_strgt ie1 ie2 = IApp "_strgt" [ie1, ie2]
_streq :: IExpr -> IExpr -> IExpr
_streq ie1 ie2 = IApp "_streq" [ie1, ie2]
_strneq :: IExpr -> IExpr -> IExpr
_strneq ie1 ie2 = IApp "_strneq" [ie1, ie2]
_strconcat :: IExpr -> IExpr -> IExpr
_strconcat ie1 ie2 = IApp "_strconcat" [ie1, ie2]


type Bindable = Either String (Reference, String)

simpleLvalueToInernal :: LValue' a -> ILValue
simpleLvalueToInernal = \case
  LVar ma (Ident id) -> IVar id
  LVarMem ma lv (Ident id) -> let
    ilv = simpleLvalueToInernal lv
    in
    IMember ilv id
  LVarArr ma lv ex -> undefined

lvalueToBindable :: LValue -> Translator ((Int,Int),Bindable)
lvalueToBindable = \case
  LVar ma (Ident id) -> return ((-1,-1) `fromMaybe` ma, Left id)
  LVarMem ma lv (Ident id) -> do
    (itype, ivalue, _)<- lvalueToInternal lv
    reference <-case ivalue of
      Null -> throwErrorInContext $ NullDereference (fromJust ma)
      Undefined -> throwErrorInContext $ UndefinedDerefence (fromJust ma)
      RunTimeValue -> undefined
      OwningReference n -> return n
      _ -> throwErrorInContext $ ExpectedClass (fromJust ma) itype
    return (fromJust ma, (Right (reference, id)))
  LVarArr ma lv ex -> undefined

setLvaluesToRuntime :: Traversable a => a LValue -> Translator ()
setLvaluesToRuntime lvalues = do
  x <- mapM lvalueToBindable lvalues
  mapM_ (\ (pos, x) ->
           case x of
             Left s -> do
               (itype, ivalue) <- getVariable pos s
               newvalue <- case itype of
                             LInt -> return RunTimeValue
                             LString -> return RunTimeValue
                             LBool -> return RunTimeValue
                             LVoid -> undefined
                             LFun lt lts -> undefined
                             LArray lt -> undefined
                             LClass str -> OwningReference <$> newClass str RunTimeValue
                             LGenericClass str lts -> undefined
               setVariable pos pos s (itype, newvalue)
             Right (ref, member) -> do
               (itype, ivalue) <- getMember pos ref member
               newvalue <- case itype of
                             LInt -> return RunTimeValue
                             LString -> return RunTimeValue
                             LBool -> return RunTimeValue
                             LVoid -> undefined
                             LFun lt lts -> undefined
                             LArray lt -> undefined
                             LClass str -> OwningReference <$> newClass str RunTimeValue
                             LGenericClass str lts -> undefined
               setMember pos ref member (itype, newvalue)) x

-- setMemberUnsafe ::  Reference -> String -> IValue -> Translator ()
-- setMemberUnsafe ref member ivalue = do
--   z <- gets tsMemory
--   let x = fromJust $ DM.lookup ref (msStructures z)
--       (ClassRepresentation map sd _ivalue) = x
--       newvalue = ClassRepresentation (DM.insert member ivalue map) sd _ivalue
--       newMemory = MemoryState (msArrays z) (DM.insert ref newvalue (msStructures z))
--         (msReferenceToType z) (msAllocator z)
--   modify $ tsSetMemState newMemory
--   return ()

-- getMemberUnsafe :: Reference -> String -> Translator IValue
-- getMemberUnsafe ref member = do
--   struct <- gets (DM.lookup ref . msStructures . tsMemory)
--   case struct of
--     Just struct@(ClassRepresentation map sd defaultValue) -> do
--       let memberType = fromJust $ TE.sdFieldType member sd
--       case (DM.lookup member map, memberType, defaultValue) of
--         (Just x, _, _) -> return x
--         (Nothing, LClass className, RunTimeValue) -> do
--           memberReference <- newStruct className RunTimeValue
--           let ivalue = OwningReference memberReference
--               updatedParent = fromJust $ TCR.setField member ivalue struct
--           (MemoryState ma ms mr malloc)<- gets tsMemory
--           modify $ tsSetMemState (MemoryState ma (DM.insert ref updatedParent ms) mr malloc)
--           return ivalue
--         (Nothing, _, _) -> return defaultValue
--     Nothing -> undefined

lvalueToInternal :: LValue -> Translator (IType, IValue, ILValue)
lvalueToInternal lvalue = let
  pos = getPosition lvalue
  in
    case lvalue of
      LVar ma (Ident id) -> do
        (itype, ivalue) <- getVariable (fromJust ma) id
        return (itype, ivalue, IVar id)
      LVarMem ma lv (Ident fieldName) -> do
        (itype, ivalue, ilvalue) <- lvalueToInternal lv
        className <-case itype of
          LClass s -> return s
          _ -> throwErrorInContext (NotClass (fromJust ma) "")
        case ivalue of
          OwningReference ref -> do
            (itype, ivalue) <- getMember (fromJust ma) ref fieldName
            return (itype, ivalue, IMember ilvalue fieldName)
          Undefined -> throwErrorInContext $ UndefinedDerefence (fromJust ma)
          Null -> throwErrorInContext $ NullDereference (fromJust ma)
          RunTimeValue  -> undefined
          _ -> undefined
      LVarArr ma lv ex -> undefined

f :: Expr -> Translator (IType, IValue, IExpr)
f (ELitInt _ x) = return (LInt , IValueInt x, ILitInt x)
f (ELitTrue _) = return (LBool, IValueBool True, ILitBool True)
f (ELitFalse _) = return (LBool, IValueBool False, ILitBool False)
f (EString _ str) = return (LString, IValueString str, IString str)
f e@(Not pos expr) = do
  (itype, ivalue ,iexp) <- exprToInternal expr
  unless (itype `same` LBool) $ throwErrorInContext (TypeConflict (getPosition e) LBool (cast itype))
  let res = case iexp of
              INot iexp' -> iexp'
              IRel op ie1 ie2 -> let
                op' = case op of
                  ILTH -> IGE
                  ILE -> IGTH
                  IGTH -> ILE
                  IGE -> ILTH
                  IEQU -> INE
                  INE -> IEQU
                in
                IRel op' ie1 ie2
              ILitBool x -> ILitBool (not x)
              _ -> INot iexp
      ivalue' = case ivalue of
                  IValueBool x -> IValueBool (not x)
                  _ -> ivalue
  return (itype, ivalue', res)
f (EOr pos e1 e2) = let
  x :: (IType, IValue, IExpr) -> Expr -> Translator (IType, IValue, IExpr)
  x (LBool,IValueBool False, _) exp =
    do
      (itype, ivalue, iExp) <- exprToInternal exp
      unless (itype `same` LBool) $ throwErrorInContext (TypeConflict ((-1, -1) `fromMaybe` pos) LBool (cast itype))
      return (itype, ivalue, iExp)
  x left@(LBool, RunTimeValue, iLeft) exp =
    do
      (itype, ivalue, iRight) <- exprToInternal exp
      case (itype, ivalue) of
        -- (StaticBool True) -> return (DynamicBool, IOr iLeft iRight) -- 30.12 Przed optymalizacją
        (LBool, IValueBool True) -> return (LBool, RunTimeValue, IOr [iLeft, ILitBool True])
        (LBool, IValueBool False) -> return left
        (LBool, RunTimeValue)  -> case iRight of
          IOr ies -> return (LBool, RunTimeValue ,IOr (iLeft:ies))
          _ -> return (LBool, RunTimeValue ,IOr [iLeft, iRight])
        _ -> throwErrorInContext (TypeConflict (getPosition e2) LBool (cast itype))
  x left@(LBool, IValueBool True, _) _ = return left
  x (ltype, _, _) _ = throwErrorInContext (TypeConflict (getPosition e1) LBool (cast ltype))
  in
    exprToInternal e1 >>= flip x e2
f (EAnd pos e1 e2) =
  let
      x :: (IType, IValue, IExpr) -> Expr -> Translator (IType, IValue, IExpr)
      x left@(LBool, IValueBool False, _) _ = return left
      x (LBool, IValueBool True, _) exp =
        do
          (itype, ivalue, iExp) <- exprToInternal exp
          unless (itype `same` LBool) $ throwErrorInContext (TypeConflict (getPosition e2) LBool (cast itype))
          return (itype, ivalue, iExp)
      x left@(LBool, RunTimeValue, iLeft) exp =
        do
          (itype, ivalue, iRight) <- exprToInternal exp
          case (itype, ivalue) of
            (LBool, IValueBool True) -> return left
            (LBool, RunTimeValue) -> case iRight of
              IAnd ies -> return (LBool, RunTimeValue, IAnd (iLeft:ies))
              _ -> return (LBool, RunTimeValue ,IAnd [iLeft, iRight])
            _ -> throwErrorInContext (TypeConflict (getPosition e2) LBool (cast itype))
      x (ltype,_,_) _ = throwErrorInContext (TypeConflict (getPosition e1) LBool (cast ltype))
  in
    exprToInternal e1 >>= flip x e2
f (EMul pos e1 op e2) = do
  (type1, ivalue1, ie1) <- f e1
  (type2, ivalue2, ie2) <- f e2
  assertOpType op type1 type2
  case (op, ivalue2) of
    (Div _, IValueInt 0) -> errorDivisonByZero op
    (Mod _, IValueInt 0) -> errorDivisonByZero op
    _ -> return ()
  case (ie1, ie2) of
    (ILitInt x, ILitInt y) -> let
      res = appOp op x y
      in
      return (LInt, IValueInt res, ILitInt res)
    _ -> return (LInt, RunTimeValue, IMul (mulToIMul op) ie1 ie2)
f (EAdd pos e1 op e2) =
  let
    helper :: (IType, IValue,IExpr) -> (IType, IValue, IExpr) -> AddOp ->
      Translator (IType, IValue, IExpr)
    helper (LString, _, IString x) (LString, _ , IString y) (Plus pos) = do
      return $ (\z -> (LString, IValueString z ,IString z)) (x ++ y)
    helper (_,_, ILitInt x) (_, _,ILitInt y) op =
      return $ (\z -> (LInt, IValueInt z, ILitInt z)) $ appOp op x y
    helper (itype1, _, iexp1) (itype2, _, iexp2) op = do
      assertOpType op itype1 itype2
      let retfun = if itype1 `same` LInt then IAdd (addtoIAdd op) else _strconcat
      return (itype1, RunTimeValue, retfun iexp1 iexp2)
  in
    do
      result1 <- f e1
      result2 <- f e2
      helper result1 result2 op
f (ERel pos e1 op e2) = let
  g :: RelOp -> (IType, IValue ,IExpr) -> (IType, IValue, IExpr) -> (IType, IValue, IExpr)
  g op (t1,iv1, ie1) (t2, iv2, ie2) =
    let fun = (case op of
                  LTH ma -> (IRel (reltoIRel op), _strlt)
                  LE ma -> (IRel (reltoIRel op), _strle)
                  GTH ma -> (IRel (reltoIRel op), _strgt)
                  GE ma -> (IRel (reltoIRel op), _strge)
                  EQU ma -> (IRel (reltoIRel op), _streq)
                  NE ma -> (IRel (reltoIRel op), _strneq))
        x = case (t1, t2) of
          (LString, _) -> snd
          (_, LString) -> snd
          _ -> fst
    in
      (LBool, RunTimeValue, x fun ie1 ie2)
  helper :: RelOp -> (IType,IValue, IExpr) -> (IType, IValue, IExpr) -> (IType, IValue, IExpr)
  helper op (LInt, IValueInt x, _ ) (LInt, IValueInt y, _) =
    (\boolean -> (LBool, IValueBool boolean, ILitBool boolean)) (appOp op x y)
  helper op (LBool, IValueBool x, _) (LBool, IValueBool y, _) =
    (\boolean -> (LBool, IValueBool boolean, ILitBool boolean)) (appOp op x y)
  helper op (LString, IValueString x, _) (LString, IValueString y, _) =
    (\boolean -> (LBool, IValueBool boolean, ILitBool boolean)) (appOp op x y)
  helper op ie1 ie2  = g op ie1 ie2
  in
    do
      r1@(it1, _, _) <- exprToInternal e1
      r2@(it2, _, _) <- exprToInternal e2
      assertOpType op it1 it2
      return $ helper op r1 r2
f (EVar _ lvalue) = do
  (itype, ivalue, ilvalue) <- lvalueToInternal lvalue
  let iexpr =case ivalue of
        IValueInt n -> ILitInt n
        IValueBool b -> ILitBool b
        IValueString s -> IString s
        _ -> ILValue ilvalue
  return (itype, ivalue, iexpr)
f (EApp pos (Ident funId) exps) = do
  fEnv <- asks TE.getFunEnv
  let funData = funId `DM.lookup` fEnv
      errPos = (-1, -1) `fromMaybe` pos
  case funData of
    Nothing -> throwErrorInContext (UndefinedFun ((-1, -1) `fromMaybe` pos) funId)
    Just (rType, argTypes) -> do
      tmp <- exprToInternal `mapM` exps
      iArgs <- foldr (\(dType, (iType, iValue, iExpr)) monad ->
               do
                 list <- monad
                 if (dType `same` iType) then return $ iExpr:list
                   else do
                   isSub <- asks $ iType `TE.isSubClass` dType
                   unless (isSub) $ throwErrorInContext (TypeConflict errPos dType (cast iType))
                   return $ (ICast dType iExpr):list
            )(return []) (zip argTypes tmp)
      unless (length argTypes == length tmp) $ throwErrorInContext (WrongArgumentCount errPos)
      return (lTypeToIType rType, RunTimeValue, IApp funId iArgs)
f e0@(Neg pos expr) = do
  (itype, ivalue, iexpr) <- f expr
  unless (itype `same` LInt) $ throwErrorInContext (TypeConflict (getPosition e0) LInt (cast itype))
  return $
    case ivalue of
      (IValueInt x) -> (LInt, IValueInt (-x), ILitInt (-x))
      _ -> (LInt, RunTimeValue , INeg iexpr)
f (ENull _) = return (universalReference, Null, INull)
f (ENewClass pos parserType) = do
  let itype = convertType parserType
  reference <- case itype of
    LInt -> throwErrorInContext $ PrimitiveType (fromJust pos) LInt
    LString -> throwErrorInContext $ PrimitiveType (fromJust pos) LString
    LBool -> throwErrorInContext $ PrimitiveType (fromJust pos) LBool
    LVoid -> throwErrorInContext $ UnhappyCompiler (fromJust pos)
    LFun lt lts -> throwErrorInContext $ UnhappyCompiler (fromJust pos)
    LArray lt -> undefined
    LGenericClass s lts -> undefined
    LClass s -> do
      x <- asks $ TE.lookupClass s
      when (isNothing x) (throwErrorInContext $ UndefinedClass (fromJust pos) (show itype))
      newClass s Undefined
  return (itype, OwningReference reference, INew itype)
f ENewArray {} = undefined "Placeholder"

simplify :: (IType, IValue, IExpr) -> (IType, IValue, IExpr)
simplify pair = pair

exprToInternal :: Expr -> Translator (IType, IValue, IExpr)
exprToInternal expr@(Neg _ subexp) = simplify <$>f expr
exprToInternal expr@(EMul pos e1 op e2) =  simplify <$> f expr
exprToInternal expr@(EAdd pos e1 op e2) = simplify <$> f expr
exprToInternal expr = f expr


emptyBNFC'Pos :: BNFC'Position
emptyBNFC'Pos = Just (-1, -1)

defaultExpr :: LType -> Expr
defaultExpr LBool = ELitFalse emptyBNFC'Pos
defaultExpr LInt = ELitInt emptyBNFC'Pos 0
defaultExpr LString = EString emptyBNFC'Pos ""
defaultExpr (LClass _) = ENull emptyBNFC'Pos
defaultExpr _ = undefined

throwErrorInContext :: SemanticErrorType -> Translator a
throwErrorInContext errtype  =
  do
    (a,b, pos) <- asks TE.getContext
    throwError $ SemanticError pos errtype

itemToInternal :: LType -> Item -> Translator IItem
itemToInternal varType item = do
  let id = getIdStr item
  let expr = case item of
        NoInit _ _ -> defaultExpr varType
        Init _ _ ex -> ex
  (itype, ivalue ,iexpr) <- exprToInternal expr
  let correctType = (varType `same` itype) || case varType of
                                                LClass s -> itype == universalReference
                                                _ -> False
  unless correctType (throwErrorInContext $ TypeConflict (getPosition item) varType (cast itype))
  declareVariable (getPosition item) id (itype, ivalue)
  return (IItem id iexpr)

-- Przed zmianami
-- itemToInternal varType item =
--   do
--     let id = getIdStr item
--     context@(ltype, funName, pos) <- asks TE.getContext
--     (_, venv) <- get
--     if id `DS.member` head (redeclaredVars venv)
--       then throwError $ SemanticError pos (RedefinitionOfVariable (getPosition item) (getPosition item) id)
--       else
--       do
--         let expr = case item of
--               NoInit _ _ -> defaultExpr varType
--               Init _ _ ex -> ex
--         (itype, ivalue ,iexpr) <- exprToInternal expr
--         unless (varType `same` itype) (throwErrorInContext $ TypeConflict (getPosition item) varType (cast itype))
--         (c, venv) <- get
--         put (c, declareVar id itype venv)
--         return (IItem id iexpr)

itemsToInternals :: LType -> [Item] -> Translator [IItem]
itemsToInternals _ [] = return []
itemsToInternals ltype (item:rest) =
  do
    head <- itemToInternal ltype item
    tail <- itemsToInternals ltype rest
    return $ head:tail

-- -- stmtToInternal (BStmt _ block) = do
-- --   (iBlock, returned) <- (\(retType, VEnv set map) -> (retType,VEnv DS.empty map)) `local` blockToInternal block
-- --   return (IBStmt iBlock, returned)

-- referenceGetField ::
-- referenceGetFieldType :: Reference -> String -> Translator (Maybe IType)
-- referenceGetFieldType ref memberName = do
--   z <- gets tsMemory
--   let classRepr = fromJust $ DM.lookup ref (msStructures z)
--       sd = TCR.getStructureData classRepr
--   return $ TE.sdFieldType memberName sd

assertType :: IType -> IType -> (Int, Int) -> Translator ()
assertType left right pos = do
  let simpleCheck = left `same` right
      complexCheck = case left of
        LClass s -> right == universalReference
        _ -> False
  unless (simpleCheck || complexCheck) (throwErrorInContext $ TypeConflict pos left right)

stmtsToInternal :: [Stmt] -> Translator ([IStmt], Bool)
stmtsToInternal [] = return ([], False)
stmtsToInternal ((BStmt _ block):rest) = do
  (iBlock, returned) <-  blockToInternal block
  let iStmt = IBStmt iBlock
  if returned
    then return ([iStmt], True)
    else stmtsToInternal rest Data.Functor.<&> Data.Bifunctor.first (iStmt:)
stmtsToInternal ((Decl pos dtype items):rest) = do
  let ltype = convertType dtype
  items <- itemsToInternals ltype items
  (istmts, ret) <- stmtsToInternal rest
  return (IDecl items:istmts, ret)
stmtsToInternal (stm@(Ass pos lvalue expr):rest) = do
  (itype', ivalue', irexp) <- exprToInternal expr
  istmt <- case lvalue of
    LVar ma (Ident varname) -> do
      let varpos = undefined `fromMaybe` ma
      setVariable (fromJust ma) (fromJust pos) varname (itype', ivalue')
      return $ IAss (IVar varname) irexp
    LVarMem ma lv (Ident memberName) -> do
      (itype, ivalue, ilvalue)<- lvalueToInternal lv
      reference <- case ivalue of
        Null -> throwErrorInContext $ NullDereference (fromJust ma)
        Undefined -> throwErrorInContext $ UndefinedDerefence (fromJust ma)
        OwningReference n -> return n
        _ -> undefined
      setMember (fromJust pos) reference memberName (itype', ivalue')
      return $ IAss (IMember ilvalue memberName) irexp
    LVarArr ma lv ex -> undefined
  stmtsToInternal rest Data.Functor.<&> Data.BiFunctor.first (istmt:)
stmtsToInternal ((Incr mpos lvalue):rest) =
  let
    expr = EAdd mpos (EVar mpos lvalue) (Plus mpos) (ELitInt mpos 1)
    stmt' = Ass mpos lvalue expr
  in
    stmtsToInternal (stmt':rest)
stmtsToInternal ((Decr mpos lvalue):rest) =
  let
    expr = EAdd mpos (EVar mpos lvalue) (Minus mpos) (ELitInt mpos 1)
    stmt' = Ass mpos lvalue expr
  in
    stmtsToInternal (stmt':rest)

-- stmtsToInternal ((Incr mpos lvalue):rest) = do
--   let pos = (-1,-1) `fromMaybe` mpos
--   case lvalue of
--     LVar ma (Ident varName) -> do
--       (itype, ivalue, ilvalue) <- lvalueToInternal lvalue
--       unless (itype `same` LInt) $ throwErrorInContext (TypeConflict pos LInt (cast itype))
--       let modifyFun = case ivalue of
--             IValueInt val -> do
--               let itv = (LInt, IValueInt (val + 1))
--               setVariable (pos) (getPosition lvalue) (varName) itv
--               return itv
--             _ -> return (LInt, RunTimeValue)
--       (itype, ivalue) <- modifyFun
--       return (itype, ivalue, IIncr ilvalue)
--     LVarMem ma lv (Ident member) -> do
--       (iptype, ipvalue, ipl) <- lvalueToInternal lv
--       myclass <- case (iptype, ipvalue) of
--         (LClass _, OwningReference reference) -> return reference
--         (LClass _, _) -> undefined
--         (_, _) -> throwErrorInContext $ ExpectedClass pos iptype
--       (itype, ivalue) <- getMember pos myclass member
--       unless (itype `same` LInt) $ throwErrorInContext (TypeConflict pos LInt (cast itype))
--       let modifyFun = case ivalue of
--             IValueInt val -> do
--               let itv = (LInt, IValueInt (val + 1))
--               setMember pos myclass member itv
--               return itv
--             RunTimeValue  -> return (LInt, RunTimeValue)
--             _ -> throwErrorInContext (TypeConflict pos LInt (cast itype))
--       (itype', ivalue') <- modifyFun
--       return (itype', ivalue', IIncr (IMember ipl member))
--     LVarArr ma lv ex -> undefined
--   undefined

stmtsToInternal ((Ret pos expr):rest) =
  do
    (funType, _, _) <- asks TE.getContext
    (itype, ivalue, iexpr) <- exprToInternal expr
    unless (itype `same` funType) (throwErrorInContext
                                   (WrongReturnType ((-1,-1) `fromMaybe` pos) funType (cast itype)))
    return ([IRet iexpr], True)
stmtsToInternal ((VRet pos):rest) = do
  (funType, _, _) <- asks TE.getContext
  unless (funType `same` LVoid) $ throwErrorInContext
    (WrongReturnType ((-1,-1) `fromMaybe` pos) funType LVoid)
  return ([IVRet], True)
stmtsToInternal ((Cond pos expr stmt md): rest) =
  let
    stmt' :: Stmt
    stmt' = Empty Nothing
  in
    stmtsToInternal (CondElse pos expr stmt stmt' md:rest)
  -- Legacy
  -- do
  -- (itype, ivalue, iexpr) <- exprToInternal expr
  -- unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
  -- case ivalue of
  --   (IValueBool False) -> stmtsToInternal rest
  --   (IValueBool True) -> stmtsToInternal (BStmt pos (Block pos [stmt]):rest)
  --   _ -> do
  --     (iblock, returnBoolean) <- withinConditionalBlock $  blockToInternal $ VirtualBlock [stmt]
  --     undefined "Należy zmienić struktury na runtime"
  --     (irest, restBool) <- stmtsToInternal rest
  --     let icond = ICondElse iexpr iblock (IBlock []) (MD md)
  --     return (icond:irest, restBool)
stmtsToInternal ((CondElse pos expr stmt1 stmt2 md):rest) =
  do
    (itype, ivalue, iexpr) <- exprToInternal expr
    unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
    case ivalue of
      (IValueBool False) -> stmtsToInternal (BStmt pos (Block pos [stmt2]):rest)
      (IValueBool True) -> stmtsToInternal (BStmt pos (Block pos [stmt1]):rest)
      _ -> do
        (iblock1, returnBoolean1) <- withinConditionalBlock $ blockToInternal (VirtualBlock [stmt1])
        (iblock2, returnBoolean2) <- withinConditionalBlock $ blockToInternal (VirtualBlock [stmt2])
        setLvaluesToRuntime md
        let icond = ICondElse iexpr iblock1 iblock2 (MD $ map simpleLvalueToInernal md)
        if returnBoolean1 && returnBoolean2
          then return ([icond], True)
          else BiFunctor.first (icond:) <$> stmtsToInternal rest
-- Legacy --
stmtsToInternal ((While pos expr stmt md):rest) = do
  let ascmd =  md

  setLvaluesToRuntime md

  (itype, ivalue, iexpr) <- exprToInternal expr
  unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
  case ivalue of
    (IValueBool False) -> stmtsToInternal rest
    _ -> do
      (iblock, returnBoolean) <- withinConditionalBlock $ blockToInternal (VirtualBlock [stmt])
      BiFunctor.first (IWhile iexpr iblock (MD $ map simpleLvalueToInernal md):) <$> stmtsToInternal rest
  where
    makeDynamic :: [String] -> VariableState -> VariableState
    makeDynamic s venv = foldl (\venv (key, val) -> VE.setVar key val venv) venv (zip s t)
      where
        t = toDynamic s venv
    toDynamic :: [String] -> VariableState -> [(IType, IValue)]
    toDynamic ss venv = map
      (\key ->
          case lookupVar key venv of
            Just (itype, ivalue) -> (itype, RunTimeValue)
            Nothing -> (LVoid, RunTimeValue))
      ss
stmtsToInternal ((SExp _ expr):rest) =
  do
    (_, _, iexpr) <- exprToInternal expr
    BiFunctor.first (ISExp iexpr:) <$> stmtsToInternal rest
stmtsToInternal ((Empty pos):rest) = stmtsToInternal rest


blockToInternal :: Block -> Translator (IBlock, Bool)
blockToInternal block =
  let
    stmts = case block of
      Block pos stmts -> stmts
      VirtualBlock stmts -> stmts
  in
    do
      result <- withOpenBlock $ stmtsToInternal stmts
      return $ Data.BiFunctor.first
        (\case
            [IBStmt iblock] -> iblock
            list -> IBlock list)
        result

topDefToInternal :: TopDef -> FunctionEnvironment -> StructureEnvironment -> CompilerExcept IFun
topDefToInternal fDef fEnv sEnv = let
  funName = getIdStr fDef
  funArgs = [(getIdStr i, getArgLType i) | i <- topDefArgs fDef]
  retType = fst $ (LVoid, []) `fromMaybe` DM.lookup funName fEnv
  block = topDefBlock fDef
  -- newVarState = foldl (\vEnv (id, ltype) ->
  --                        declareVar id (ltype, RunTimeValue) vEnv)
  --               (openClosure newVarEnv) funArgs
  tsEnv :: TranslationEnvironment
  tsEnv = (fEnv, sEnv, (retType, funName, getPosition fDef))
  x :: Translator (IBlock, Bool)
  x = do
    withOpenBlock $ do
      mapM_ (\(id,ltype) -> declareVariable (0,0) id (ltype, RunTimeValue)) funArgs
      blockToInternal block
  res = evalTranslator tsEnv newTranslatorState x
  in
    do
      x <- res
      unless (snd x || retType == LVoid) (throwError $ SemanticError (getPosition fDef) (NoReturnValue retType))
      return $ IFun funName retType funArgs (fst x)

classDefToInternal :: ClassDef -> FunctionEnvironment -> StructureEnvironment -> CompilerExcept IClass
classDefToInternal cdef fEnv sEnv = let
  className = case cdef of
    ClassDef ma (Ident id) cmds -> id
    ClassDefExtends ma (Ident id) id' cmds -> id
  in do
  return $ IClass className []

assertMain :: FunctionEnvironment -> CompilerExcept ()
assertMain fEnv =
  let
    main = DM.lookup "main" fEnv
    in
    case main of
      Just (LInt, _) -> return ()
      _ -> throwError $ SemanticError (0,0) NoMain

data IProgram = IProgram [IFun] [IClass] StructureEnvironment

data IClass = IClass {icName :: String,
                     icDefinedMethods :: [()]}

programToInternal :: Program -> CompilerExcept IProgram
programToInternal program@(Program _ topDefs classDefs) =
  let
    x :: CompilerExcept ()
    x = return ()
    -- fun :: FunctionEnvironment -> CompilerExcept () -> TopDef -> CompilerExcept ()
    -- fun fEnv monad topDef = do
    --   topDefToInternal topDef fEnv
    --   monad
  in
    do
      fEnv <- getFunctionEnvironment program
      sEnv <- getStructureEnvironment program
      assertMain fEnv
      ifuns <- mapM (\x -> topDefToInternal x fEnv sEnv) topDefs
      iclasses <- mapM (\x -> classDefToInternal x fEnv sEnv) classDefs
      return $ IProgram ifuns iclasses sEnv

class Castable a b where
  cast_ :: a -> b

class Convertable a b where
  convert :: a -> b

class TypedBiOperator a b where
  assertOpType :: a -> b -> b -> Translator ()

instance TypedBiOperator AddOp IType where
  assertOpType op@(Plus _) left right = do
    (_,_,pos) <- asks TE.getContext
    unless ((left `same` right) && ((left `same` LInt)  || (left `same` LString))) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))
  assertOpType op@(Minus _) left right = do
    (_,_,pos) <- asks TE.getContext
    unless ((left `same` right) && (left `same` LInt)) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))

errorDivisonByZero :: MulOp -> Translator ()
errorDivisonByZero op = do
  (_, _, pos) <- asks TE.getContext
  throwError $ SemanticError pos (DivisionByZero (getPosition op))
-- assertDivision :: MulOp -> IExpr -> Compiler FunTranslationEnvironment ()
-- assertDivision op@(Div pos) (ILitInt 0) = errorDivisonByZero op
-- assertDivision op@(Mod pos) (ILitInt 0) = errorDivisonByZero op
-- assertDivision _ _= return ()


instance TypedBiOperator MulOp IType where
  assertOpType op left right = do
    (a,b,pos) <- asks TE.getContext
    unless ((left `same` right) && (left `same` LInt)) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))

instance TypedBiOperator RelOp IType where
  assertOpType op x y = let
    errorFun :: (Int, Int) -> IType -> IType -> Translator ()
    errorFun pos ltype rtype = do
      (_, _, context) <- asks TE.getContext
      throwError (SemanticError context $BinaryTypeConflict pos (ltype, rtype))
    tmp :: RelOp -> IType -> IType -> Translator ()
    tmp op@(EQU _) x y = do
      unless ((x `same` y) && (x `same` LInt || x `same` LString || x `same` LBool)) $ errorFun (getPosition op) x y
    tmp (NE pos) x y = tmp (EQU pos) x y
    tmp (LTH pos) x y = do
      unless (x `same` LInt && (x `same` y)) $ errorFun (getPosition op) x y
    tmp op x y = assertOpType (LTH $ hasPosition op) x y
    in
      tmp op x y

mulToIMul :: MulOp -> IMulOp
mulToIMul (Times _) = ITimes
mulToIMul (Div _)  = IDiv
mulToIMul (Mod _) = IMod

addtoIAdd :: AddOp -> IAddOp
addtoIAdd (Plus _) = IPlus
addtoIAdd (Minus _) = IMinus

reltoIRel :: RelOp -> IRelOp
reltoIRel x = case x of
  LTH ma -> ILTH
  LE ma -> ILE
  GTH ma -> IGTH
  GE ma -> IGE
  EQU ma -> IEQU
  NE ma -> INE


getCalledFunctions :: IFun -> DS.Set String
getCalledFunctions (IFun _ _ _ iblock) =
  getCalledFunctionB iblock DS.empty
  where
    getCalledFunctionB :: IBlock -> DS.Set String -> DS.Set String
    getCalledFunctionB (IBlock stmts) set =
      foldl (flip getCalledFunctionInstr) set stmts
    getCalledFunctionInstr :: IStmt -> DS.Set String -> DS.Set String
    getCalledFunctionInstr is set = case is of
      IBStmt ib -> getCalledFunctionB ib set
      IDecl iis -> getCalledFunctionsItems iis set
      IAss s ie -> getCalledFunctionExpr ie set
      IIncr s -> set
      IDecr s -> set
      IRet ie -> getCalledFunctionExpr ie set
      IVRet -> set
      ICond ie ib md -> getCalledFunctionB ib $ getCalledFunctionExpr ie set
      ICondElse ie ib ib' md -> getCalledFunctionB ib' $ getCalledFunctionB ib $ getCalledFunctionExpr ie set
      IWhile ie ib md -> getCalledFunctionB ib $ getCalledFunctionExpr ie set
      ISExp ie -> getCalledFunctionExpr ie set
      IStmtEmpty -> set
    getCalledFunctionExpr :: IExpr -> DS.Set String -> DS.Set String
    getCalledFunctionExpr ie set = case ie of
      ILValue _ -> set
      ILitInt n -> set
      ILitBool b -> set
      IApp s ies -> foldl (flip getCalledFunctionExpr) (s `DS.insert` set) ies
      IString s -> set
      INeg ie' -> getCalledFunctionExpr ie' set
      INot ie' -> getCalledFunctionExpr ie' set
      IAnd ies -> foldl (flip getCalledFunctionExpr) set ies
      IOr ies -> foldl (flip getCalledFunctionExpr) set ies
      IAdd iao ie' ie2 -> getCalledFunctionExpr ie2 $ getCalledFunctionExpr ie' set
      IMul imo ie' ie2 -> getCalledFunctionExpr ie2 $ getCalledFunctionExpr ie' set
      IRel iro ie' ie2 -> getCalledFunctionExpr ie2 $ getCalledFunctionExpr ie' set
      INew {} -> DS.insert "_new" set
      INull {} -> set
      ICast {} -> set
    getCalledFunctionsItems :: [IItem] -> DS.Set String ->DS.Set String
    getCalledFunctionsItems items set = foldl (flip x) set items
      where
      x :: IItem -> DS.Set String -> DS.Set String
      x (IItem _ iexp) set = getCalledFunctionExpr iexp set


containsPossiblyEndlessLoop :: IFun -> Bool
containsPossiblyEndlessLoop (IFun _ _ _ iblock) =
  f1 iblock
  where
    f1 :: IBlock -> Bool
    f1 (IBlock istmts) = any f2 istmts
    f2 :: IStmt -> Bool
    f2 istmt = case istmt of
      IBStmt ib -> f1 ib
      IDecl iis -> False
      IAss s ie -> False
      IIncr s -> False
      IDecr s -> False
      IRet ie -> False
      IVRet -> False
      ICond ie ib md -> f1 ib
      ICondElse ie ib ib' md -> any f1 [ib, ib']
      IWhile ie ib md -> True
      ISExp ie -> False
      IStmtEmpty -> False

-- _getNamesOfStateChangingFunctions :: DS.Set String -> [IFun] -> DS.Set String
-- _getNamesOfStateChangingFunctions seed ifuns = let
--   x = map (const DS.empty) ifuns
--   y = map (\fun@(IFun fname _ _ _) -> (fname, getCalledFunctions fun)) ifuns

--   initDepMap = foldl (\map (IFun fname _ _ _) -> DM.insert fname DS.empty map) DM.empty ifuns
--   buildDepMap :: [(String, DS.Set String)] -> DM.Map String (DS.Set String)
--   buildDepMap list = foldr f initDepMap list
--     where
--           f :: (String, DS.Set String) -> DM.Map String (DS.Set String) -> DM.Map String (DS.Set String)
--           f (fname, set) map = foldl (\map pname -> DM.insert
--                                                     pname
--                                                     (DS.insert fname (DS.empty `fromMaybe`DM.lookup pname map)) map)
--                                map set
--   loopingFunctions = foldl' (\set ifun@(IFun fname _ _ _) ->
--                                    if containsPossiblyEndlessLoop ifun
--                                    then DS.insert fname set
--                                    else set) DS.empty ifuns
--   buildDynamic :: DM.Map String (DS.Set String) -> DS.Set String -> DS.Set String -> DS.Set String
--   buildDynamic map emplaced set = if null emplaced then set else
--     let  emplaced' = foldl (\emplaced' name ->
--                                   DS.union emplaced'
--                                   (DS.difference (DS.empty `fromMaybe` DM.lookup name map) set))
--                          DS.empty emplaced
--     in
--       buildDynamic map emplaced' (DS.union emplaced' set)
--   _depMap = buildDepMap y
--   _externalDyn = ["printInt", "printString", "error", "readInt", "readString"]
--   _externalFun = ["printInt", "printString", "error", "readInt", "readString",
--                    "_strconcat", "_strle", "_strlt", "_strge", "_strgt", "_streq",
--                    "_strneq", "_new"]
--   _externalFunDSet = DS.union loopingFunctions (DS.fromList _externalDyn)
--   _dynamicFunctions = buildDynamic _depMap _externalFunDSet _externalFunDSet
--   _somehowCalledFun = DS.intersection (DS.fromList _externalFun) $
--                           foldl (\set pair -> set `DS.union` snd pair) DS.empty y
--   in
--     _dynamicFunctions


functionMetaDataNew :: [IFun] -> FunctionMetadata
functionMetaDataNew ifuns =
  let x = map (const DS.empty) ifuns
      y = map (\fun@(IFun fname _ _ _) -> (fname, getCalledFunctions fun)) ifuns

      initDepMap = foldl (\map (IFun fname _ _ _) -> DM.insert fname DS.empty map) DM.empty ifuns
      buildDepMap :: [(String, DS.Set String)] -> DM.Map String (DS.Set String)
      buildDepMap list = foldr f initDepMap list
        where
          f :: (String, DS.Set String) -> DM.Map String (DS.Set String) -> DM.Map String (DS.Set String)
          f (fname, set) map = foldl (\map pname -> DM.insert
                                                    pname
                                                    (DS.insert fname (DS.empty `fromMaybe`DM.lookup pname map)) map)
                               map set
      loopingFunctions = foldl' (\set ifun@(IFun fname _ _ _) ->
                                   if containsPossiblyEndlessLoop ifun
                                   then DS.insert fname set
                                   else set) DS.empty ifuns
      buildDynamic :: DM.Map String (DS.Set String) -> DS.Set String -> DS.Set String -> DS.Set String
      buildDynamic map emplaced set = if null emplaced then set else
        let  emplaced' = foldl (\emplaced' name ->
                                  DS.union emplaced'
                                  (DS.difference (DS.empty `fromMaybe` DM.lookup name map) set))
                         DS.empty emplaced
        in
          buildDynamic map emplaced' (DS.union emplaced' set)
      _depMap = buildDepMap y
      _externalDyn = ["printInt", "printString", "error", "readInt", "readString"]
      _externalFun = ["printInt", "printString", "error", "readInt", "readString",
                      "_strconcat", "_strle", "_strlt", "_strge", "_strgt", "_streq",
                      "_strneq", "_new"]
      _externalFunDSet = DS.union loopingFunctions (DS.fromList _externalDyn)
      _dynamicFunctions = buildDynamic _depMap _externalFunDSet _externalFunDSet
      _somehowCalledFun = DS.intersection (DS.fromList _externalFun) $
                          foldl (\set pair -> set `DS.union` snd pair) DS.empty y
      _mutargs :: DM.Map String [Bool]
      _mutargs = DM.fromList (foldl (\result (IFun fname _ args _) ->
                                    (fname, (map (\(_, ltype) ->
                                                    case ltype of
                                                      LArray lt -> True
                                                      LClass s -> True
                                                      _ -> False) args)):result) [] ifuns)
      _mutargs' = DS.foldl (\_map name -> let
                               (_, x) = fromJust $ DM.lookup name TE.initialEnvironment
                               in
                               DM.insert name (map (const False) x) _map) _mutargs _somehowCalledFun
  in
    FM _somehowCalledFun _dynamicFunctions _mutargs'

data FunctionMetadata = FM {usedExternal :: DS.Set String,
                            dynamicFunctions :: DS.Set String,
                            mutableArgs :: DM.Map String [Bool]}

--------------------------------------------------------------------------------------------------

-- trOptimizeLoop :: DynamicFunction -> IBlock -> IBlock

-- type DynamicFunction = DS.Set String
-- type DynamicVariables = VE.VarEnv String Bool
-- type OptimizeLoopEnv = DynamicFunction
-- type OptimizeLoopSt = (Int, DM.Map String String, DynamicVariables, DummyAssignments)
-- type DummyAssignments = [(String, IExpr)]
-- type LoopOptimizer = ReaderT OptimizeLoopEnv (State OptimizeLoopSt)



-- oleIsFunStatic:: String -> OptimizeLoopEnv -> Bool
-- oleIsFunStatic s env = not $ DS.member s env

-- olsInit :: [String] -> OptimizeLoopSt
-- olsInit vars = (0, DM.empty,
--                 foldr (\x -> VE.declareVar x True) (VE.openClosure newVarEnv) vars,
--                 [])
-- olsLookup :: String -> OptimizeLoopSt -> Maybe String
-- olsLookup s (_, venv, _, _) = DM.lookup s venv
-- olsIsDynamic :: String -> OptimizeLoopSt -> Bool
-- olsIsDynamic s (_, _, set, _) = False `fromMaybe` VE.lookupVar s set

-- olsAddMap :: String -> String -> OptimizeLoopSt -> OptimizeLoopSt
-- olsAddMap x y (m1, venv, m2, m3) = (m1, DM.insert x y venv, m2, m3)
-- olsDeclareAsDynamic :: String -> OptimizeLoopSt -> OptimizeLoopSt
-- olsDeclareAsDynamic s (m1, m2, set, m3) = (m1, m2, DS.declareVar s True set, m3)
-- olsDeclareAsStatic :: String -> OptimizeLoopSt -> OptimizeLoopSt
-- olsDeclareAsStatic s (m1, m2, set, m3) = (m1, m2, DS.declareVar s False set, m3)

-- olsSetAsDynamic :: String -> OptimizeLoopSt -> OptimizeLoopSt
-- olsSetAsDynamic s (m1, m2, set, m3) = (m1, m2, DS.setVar s True set, m3)
-- olsSetAsStatic :: String -> OptimizeLoopSt -> OptimizeLoopSt
-- olsSetAsStatic s (m1, m2, set, m3) = (m1, m2, DS.setVar s False set, m3)


-- olsAddIe :: IExpr -> OptimizeLoopSt -> (String, OptimizeLoopSt)
-- olsAddIe ie (x, v, d, da) = let
--   dummyvar = "_y" ++ show x
--   in
--   (dummyvar, (x + 1, v, d, (dummyvar, ie):da))

-- olsOpenBlock :: OptimizeLoopSt -> OptimizeLoopSt
-- olsOpenBlock (m1, m2, m3, m4) = (m1, m2, VE.openClosure m3, m4)
-- olsCloseBlock :: OptimizeLoopSt -> OptimizeLoopSt
-- olsCloseBlock (m1, m2, m3, m4) = (m1, m2, VE.closeClosure m3, m4)
-- -- olsProtecttVars :: [String] -> OptimizeLoopSt -> OptimizeLoopSt
-- -- olsProtectVars vars (m1, m2, m3, m4) = (m1, m2, VE.protectVars_ vars m3, m4)
-- -- olsEndProtection :: OptimizeLoopSt -> OptimizeLoopSt
-- -- olsEndProtection (m1, m2, m3, m4) = (m1,  m2, VE.endProtection m3, m4)
-- loWithOpenBlock :: LoopOptimizer a -> LoopOptimizer a
-- loWithOpenBlock f = do
--   modify olsOpenBlock
--   res<-f
--   modify olsCloseBlock
--   return res

-- loWithProtectedVars :: LoopOptimizer a -> LoopOptimizer a
-- loWithProtectedVars f = do
--   (_, m2, m3, _)<- get
--   res <- f
--   (m1, _, _, m4) <- get
--   put (m1, m2, m3,m4)
--   return res

-- trOptimizeIE :: (IExpr, Bool)  -> LoopOptimizer (IExpr)
-- trOptimizeIE (ie, x) =
--   if x then
--     do
--       state <- get
--       let (name, ols) = olsAddIe ie state
--       put ols
--       return $ IVar name
--   else
--     return ie

-- trOptimizeLoopBlockIL :: IBlock -> LoopOptimizer IBlock
-- trOptimizeLoopBlockIL (IBlock instr) = do
--   loWithOpenBlock $ IBlock <$> mapM trOptimizeLoopIstmIL instr

-- trOptimizeLoopIItem :: IItem -> LoopOptimizer IItem
-- trOptimizeLoopIItem (IItem s ie) = do
--   (ie', x) <- trOptimizeLoopIExprIl ie
--   if x then do
--       ols <- get
--       let (s', ols') = olsAddIe ie ols
--       put (olsAddMap s s'$ olsDeclareAsStatic s ols')
--       return (IItem s (IVar s'))
--     else do
--     modify $ olsDeclareAsDynamic s
--     return (IItem s ie')

-- trOptimizeLoopIstmIL :: IStmt -> LoopOptimizer IStmt
-- trOptimizeLoopIstmIL istmt =
--   case istmt of
--     IBStmt iblock -> IBStmt <$> trOptimizeLoopBlockIL iblock
--     IDecl iis -> IDecl <$> mapM trOptimizeLoopIItem iis
--     IAss s ie -> do
--       (ie', x) <- trOptimizeLoopIExprIl ie
--       if x then do
--         ols <- get
--         let (s', ols') = olsAddIe ie ols
--         put (olsAddMap s s' $ olsSetAsStatic s ols')
--         return $ IAss s (IVar s')
--         else do
--         modify $ olsSetAsDynamic s
--         return $ IAss s ie'
--     IIncr s -> do
--       modify $ olsDeclareAsDynamic s
--       return istmt
--     IDecr s -> do
--       modify $ olsDeclareAsDynamic s
--       return istmt
--     IRet ie -> IRet <$> (trOptimizeLoopIExprIl ie >>= trOptimizeIE)
--     IVRet -> return istmt
--     ICond ie ib md -> undefined
--     --   ie' <- (trOptimizeLoopIExprIl ie >>= trOptimizeIE)
--     --   (IBStmt ib') <- trOptimizeLoopIstmIL (IBStmt ib)
--     --   return $ ICond ie' ib' md
--     ICondElse ie ib1 ib2 (MD md) -> do
--       ie' <- trOptimizeLoopIExprIl ie >>= trOptimizeIE
--       ib1' <- loWithProtectedVars $ trOptimizeLoopBlockIL ib1
--       ib2' <- loWithProtectedVars $ trOptimizeLoopBlockIL ib2
--       ols <- get
--       put $ DS.foldr olsSetAsDynamic ols md
--       return $ ICondElse ie' ib1' ib2' (MD md)
--     IWhile ie ib md -> return istmt
--     ISExp ie -> ISExp <$> (trOptimizeLoopIExprIl ie >>= trOptimizeIE)
--     IStmtEmpty -> undefined

-- olsIsStatic :: String -> OptimizeLoopSt -> Bool
-- olsIsStatic x y = not (olsIsDynamic x y)

-- trOptimizeLoopIExprIl :: IExpr -> LoopOptimizer (IExpr, Bool)
-- trOptimizeLoopIExprIl  iexp = do
--   env   <- ask
--   state <- get

--   case iexp of
--       IVar s -> if olsIsDynamic s state then return (iexp, False)
--         else return (IVar (s`fromMaybe` olsLookup s state), True)
--       ILitInt n -> return (iexp, True)
--       ILitBool b -> return (iexp, True)
--       IApp s ies -> do
--         x <- mapM  trOptimizeLoopIExprIl ies
--         let static = all snd x
--         if static && oleIsFunStatic s env
--           then return (iexp, True)
--           else
--           do
--             ies' <- mapM trOptimizeIE x
--             return (IApp s ies', False)
--       IString s -> return (iexp, True)
--       INeg ie -> do
--         (ie', x) <- trOptimizeLoopIExprIl ie
--         return (INeg ie', x)
--       INot ie -> do
--         (ie', x) <- trOptimizeLoopIExprIl ie
--         return (INot ie', x)
--       IAnd ies -> do
--         list <- mapM trOptimizeLoopIExprIl ies
--         let ok = all snd list
--         if ok
--           then return (iexp, True)
--           else
--           mapM trOptimizeIE list >>= (\ies -> return (IAnd ies, False))
--       IOr ies -> do
--         list <- mapM trOptimizeLoopIExprIl ies
--         let ok = all snd list
--         if ok
--           then return (iexp, True)
--           else
--           mapM trOptimizeIE list >>= (\ies -> return (IOr ies, False))
--       IAdd iao ie1 ie2 -> do
--         x1 <- trOptimizeLoopIExprIl ie1
--         x2 <- trOptimizeLoopIExprIl ie2
--         if snd x1 && snd x2
--           then return (iexp, True)
--           else do
--           ie1' <- trOptimizeIE x1
--           ie2' <- trOptimizeIE x2
--           return (IAdd iao ie1' ie2', False)
--       IMul imo ie1 ie2 ->  do
--         x1 <- trOptimizeLoopIExprIl ie1
--         x2 <- trOptimizeLoopIExprIl ie2
--         if snd x1 && snd x2
--           then return (iexp, True)
--           else do
--           ie1' <- trOptimizeIE x1
--           ie2' <- trOptimizeIE x2
--           return (IMul imo ie1' ie2', False)
--       IRel iro ie1 ie2 -> do
--         x1 <- trOptimizeLoopIExprIl ie1
--         x2 <- trOptimizeLoopIExprIl ie2
--         if snd x1 && snd x2
--           then return (iexp, True)
--           else do
--           ie1' <- trOptimizeIE x1
--           ie2' <- trOptimizeIE x2
--           return (IRel iro ie1' ie2', False)


-- trOptimizeLoop dfuns (IBlock stmts) =
--   IBlock $ map f stmts
--   where
--     f :: IStmt-> IStmt
--     f stmt = case stmt of
--       IBStmt ib -> IBStmt $ trOptimizeLoop dfuns ib
--       ICond ie ib md -> let
--         ib' = trOptimizeLoop dfuns ib
--         in
--         ICond ie ib md
--       ICondElse ie ibs ibf md -> let
--         ibs' = trOptimizeLoop dfuns ibs
--         ibf' = trOptimizeLoop dfuns ibf
--         in
--         ICondElse ie ibs' ibf' md
--       IWhile ie ib (MD md) ->
--         let
--           monad = do
--             ie' <- trOptimizeLoopIExprIl ie >>= trOptimizeIE
--             ib' <- trOptimizeLoopBlockIL (trOptimizeLoop dfuns ib)
--             return (ie', ib')
--           ((ie', ib'), (_,_,_, da)) = flip runState (olsInit (DS.toList md)) $ runReaderT monad dfuns
--           newWhile = IWhile ie' ib' (MD md)

--           -- z = IBStmt $ IBlock $ map (\(s, iexp) ->IDecl [IItem s iexp] ) (reverse da)
--           z = undefined  -- To powinno być if else
--           newStmt = if null da
--             then newWhile
--             else IBStmt $ IBlock [z, newWhile]
--         in
--           newStmt
--       _ -> stmt
