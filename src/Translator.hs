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
    FunctionMetadata(..)
  ) where

import IDefinition hiding (Array)


import CompilationError

import Prelude
import Data.Foldable (Foldable(toList))
import Data.Maybe (fromMaybe)
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
import qualified Control.Monad as DS
import qualified VariableEnvironment as VE
import qualified VariableEnvironment as DS
import Data.List (foldl')

import Translator.Definitions
import Translator.TranslatorEnvironment

type FunctionContext = (LType, String, (Int, Int))
type StateStrMap x = State (DM.Map String x)

data ArrayRepresentation = ArrayRepresentation (DM.Map Int IValue) IValue
data ClassRepresentation = ClassRepresentation (DM.Map String IValue) IValue

data Allocator = Allocator {alNextArray :: Int,
                           alNextStructure :: Int}

allocateArray :: Allocator -> (Allocator, Reference)
allocateArray allocator = (Allocator (alNextArray allocator+ 1) (alNextStructure allocator),
                           alNextArray allocator)
allocateStruct :: Allocator -> (Allocator, Reference)
allocateStruct allocator =(Allocator (alNextArray allocator) (alNextStructure allocator + 1),
                           alNextStructure allocator)
data MemoryState = MemoryState {msArrays ::DM.Map Reference ArrayRepresentation,
                                msStructures::DM.Map Reference ClassRepresentation,
                                msAllocator :: Allocator}
type VariableState = VE.VarEnv String (IType, IValue)
type TranslatorState = (MemoryState, VariableState)

tsInit :: TranslatorState
tsInit = (MemoryState DM.empty DM.empty (Allocator 0 0), VE.newVarEnv)
tsSetMemState :: MemoryState -> TranslatorState  -> TranslatorState
tsSetMemState mem (x, y) = (mem, y)
tsSetVarState :: VariableState -> TranslatorState  -> TranslatorState
tsSetVarState varst (x, s)= (x, varst)
tsModifyVarState :: (VariableState -> VariableState) -> TranslatorState -> TranslatorState
tsModifyVarState f (mem, vars) = (mem, f vars)
tsMemory :: TranslatorState -> MemoryState
tsMemory (mem, _) = mem
tsVarState :: TranslatorState -> VariableState
tsVarState (_, var) = var

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

type TranslatorEnvironment = (FunctionEnvironment, FunctionContext)
teFunctionEnvironment :: TranslatorEnvironment -> FunctionEnvironment
teFunctionEnvironment = fst
teFunctionContext :: TranslatorEnvironment -> FunctionContext
teFunctionContext = snd

type Compiler varEnv = ReaderT TranslatorEnvironment (StateT varEnv CompilerExcept)

withOpenBlock :: Compiler TranslatorState a -> Compiler TranslatorState a
withOpenBlock f = do
  varst <- gets tsVarState
  modify (tsSetVarState $ VE.openClosure varst)
  res <- f
  varst' <- gets tsVarState
  modify (tsSetVarState $ VE.closeClosure varst')
  return res

withinConditionalBlock :: Compiler TranslatorState a -> Compiler TranslatorState a
withinConditionalBlock f = do
  state <- get
  res <- f
  put state
  return res


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


lvalueToInternal :: LValue -> Compiler TranslatorState (IType, IValue, IExpr)
lvalueToInternal lvalue = let
  pos = getPosition lvalue
  in
    case lvalue of
      LVar ma (Ident id) -> do
        venv <- gets tsVarState
        case id `lookupVar` venv of
          Nothing -> throwError $ SemanticError pos (UndefinedVar pos id)
          _ -> undefined
      LVarMem ma lv id -> undefined
      LVarArr ma lv ex -> undefined



f :: Expr -> Compiler TranslatorState (IType, IValue, IExpr)
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
  x :: (IType, IValue, IExpr) -> Expr -> Compiler TranslatorState (IType, IValue, IExpr)
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
        (LBool, (IValueBool True)) -> return (LBool, RunTimeValue, IOr [iLeft, (ILitBool True)])
        (LBool, (IValueBool False)) -> return left
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
      x :: (IType, IValue, IExpr) -> Expr -> Compiler TranslatorState (IType, IValue, IExpr)
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
      Compiler TranslatorState (IType, IValue, IExpr)
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
      (LBool, RunTimeValue, (x fun) ie1 ie2)
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
f (EVar pos lvalue) = do
  case lvalue of
    LVar ma (Ident varname) -> do
      state <- get
      let varst = tsVarState state
          x = VE.lookupVar varname varst
      case x of
        Nothing -> throwErrorInContext $ UndefinedVar (getPosition lvalue) varname
        Just (itype, ivalue) -> case ivalue of
          IValueBool x -> return (itype, ivalue, ILitBool x)
          IValueInt x -> return (itype, ivalue, ILitInt x)
          IValueString x -> return (itype, ivalue, IString x)
          _ -> return (itype, ivalue, ILValue $ IVar varname)
    LVarMem ma lv id -> undefined
    LVarArr ma lv ex -> do
      iexp <- f ex
      undefined
f (EApp pos (Ident funId) exps) = do
  fEnv <- asks teFunctionEnvironment
  let funData = funId `DM.lookup` fEnv
      errPos = (-1, -1) `fromMaybe` pos
  case funData of
    Nothing -> throwErrorInContext (UndefinedFun ((-1, -1) `fromMaybe` pos) funId)
    Just (rType, argTypes) -> do
      tmp <- exprToInternal `mapM` exps
      iArgs <- foldr (\(dType, (iType, iValue, iExpr)) monad ->
               do
                 list <- monad
                 unless (dType `same` iType) $ throwErrorInContext (TypeConflict errPos dType (cast iType))
                 return $ iExpr:list
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

simplify :: (IType, IValue, IExpr) -> (IType, IValue, IExpr)
simplify pair = pair

exprToInternal :: Expr -> Compiler TranslatorState (IType, IValue, IExpr)
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
defaultExpr _ = undefined

-- iTypeStatic :: IType -> Bool
-- iTypeStatic (StaticInt _) = True
-- iTypeStatic (StaticBool _) = True
-- iTypeStatic (StaticString _) = True
-- iTypeStatic _ = False

throwErrorInContext :: SemanticErrorType -> Compiler b a
throwErrorInContext errtype  =
  do
    (a,b, pos) <- asks teFunctionContext
    throwError $ SemanticError pos errtype


itemToInternal :: LType -> Item -> Compiler TranslatorState IItem
itemToInternal varType item = do
  let id = getIdStr item
  (_, _, pos) <- asks teFunctionContext
  varstate <- gets tsVarState
  if id `DS.member` head (redeclaredVars varstate)
    then throwErrorInContext $ RedefinitionOfVariable (getPosition item) (getPosition item) id
    else do
    let expr = case item of
          NoInit _ _ -> defaultExpr varType
          Init _ _ ex -> ex
    (itype, ivalue ,iexpr) <- exprToInternal expr
    unless (varType `same` itype) (throwErrorInContext $ TypeConflict (getPosition item) varType (cast itype))
    modify (\state -> tsSetVarState (declareVar id (itype, ivalue) (tsVarState state)) state)
    return (IItem id iexpr)

-- Przed zmianami
-- itemToInternal varType item =
--   do
--     let id = getIdStr item
--     context@(ltype, funName, pos) <- asks teFunctionContext
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

itemsToInternals :: LType -> [Item] -> Compiler TranslatorState [IItem]
itemsToInternals _ [] = return []
itemsToInternals ltype (item:rest) =
  do
    head <- itemToInternal ltype item
    tail <- itemsToInternals ltype rest
    return $ head:tail

-- -- stmtToInternal (BStmt _ block) = do
-- --   (iBlock, returned) <- (\(retType, VEnv set map) -> (retType,VEnv DS.empty map)) `local` blockToInternal block
-- --   return (IBStmt iBlock, returned)

stmtsToInternal :: [Stmt] -> Compiler TranslatorState ([IStmt], Bool)
stmtsToInternal [] = return ([], False)
stmtsToInternal ((BStmt _ block):rest) = do
  (iBlock, returned) <-  blockToInternal block
  let iStmt = IBStmt iBlock
  if returned
    then return ([iStmt], True)
    else stmtsToInternal rest >>= (return . Data.Bifunctor.first (iStmt:))
stmtsToInternal ((Decl pos dtype items):rest) = do
  let ltype = convertType dtype
  items <- itemsToInternals ltype items
  (istmts, ret) <- stmtsToInternal rest
  return (IDecl items:istmts, ret)
stmtsToInternal (stm@(Ass pos lvalue expr):rest) = do
  varstate <- gets tsVarState
  (irtype, irvalue, irexp) <- exprToInternal expr
  istmt <- case lvalue of
    LVar ma (Ident varname) -> do
      let varpos = undefined `fromMaybe` ma
          x = varname `VE.lookupVar` varstate
      case x of
        Nothing -> throwErrorInContext (UndefinedVar varpos varname)
        Just (itype, ivalue) -> do
          unless (itype `same` irtype) (throwErrorInContext $
                                         TypeConflict (getPosition stm) (cast itype) (cast irtype))
          modify $ tsModifyVarState (VE.setVar varname (irtype, irvalue))
          return $ IAss (IVar varname) irexp
    LVarMem ma lv id -> undefined
    LVarArr ma lv ex -> undefined
  stmtsToInternal rest >>= (return . Data.BiFunctor.first (istmt:))
stmtsToInternal ((Incr _ (LVar pos (Ident varId))):rest) = do
  varstate <- gets tsVarState
  let x =  varId `lookupVar` varstate
      stmtpos = (-1,-1) `fromMaybe` pos
  case x of
    Nothing -> throwErrorInContext (UndefinedVar stmtpos varId)
    Just (xType, ivalue) -> do
      unless (xType `same` LInt) $ throwErrorInContext (TypeConflict stmtpos LInt (cast xType))
      let modifyFun = case ivalue of
            IValueInt val -> tsModifyVarState (VE.setVar varId (LInt, IValueInt (val + 1)))
            _ -> id
      modify modifyFun
      (irest, returnBool) <- stmtsToInternal rest
      return (IIncr (IVar varId):irest, returnBool)
stmtsToInternal ((Decr _ (LVar pos (Ident varId))):rest) = do
  env@(context, vEnv) <- get
  let x =  varId `lookupVar` vEnv
      stmtpos = undefined `fromMaybe` pos
  case x of
        Nothing -> throwErrorInContext (UndefinedVar stmtpos varId)
        Just (xType, ivalue) -> do
          unless (xType `same` LInt) $ throwErrorInContext (TypeConflict stmtpos LInt (cast xType))
          let modifyFun = case ivalue of
                IValueInt val -> tsModifyVarState (VE.setVar varId (LInt, IValueInt (val - 1)))
                _ -> id
          modify modifyFun
          (irest, returnBool) <- stmtsToInternal rest
          return (IDecr (IVar varId):irest, returnBool)
stmtsToInternal ((Ret pos expr):rest) =
  do
    (funType, _, _) <- asks teFunctionContext
    (itype, ivalue, iexpr) <- exprToInternal expr
    unless (itype `same` funType) (throwErrorInContext
                                   (WrongReturnType ((-1,-1) `fromMaybe` pos) funType (cast itype)))
    return ([IRet iexpr], True)
stmtsToInternal ((VRet pos):rest) = do
  (funType, _, _) <- asks teFunctionContext
  unless (funType `same` LVoid) $ throwErrorInContext
    (WrongReturnType ((-1,-1) `fromMaybe` pos) funType LVoid)
  return ([IVRet], True)
stmtsToInternal ((Cond pos expr stmt md): rest) = do
  (itype, ivalue, iexpr) <- exprToInternal expr
  unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
  case ivalue of
    (IValueBool False) -> stmtsToInternal rest
    (IValueBool True) -> stmtsToInternal (BStmt pos (Block pos [stmt]):rest)
    _ -> do
      (iblock, returnBoolean) <- withinConditionalBlock $  blockToInternal $ VirtualBlock [stmt]
      (irest, restBool) <- stmtsToInternal rest
      let icond = ICondElse iexpr iblock (IBlock []) (MD md)
      return (icond:irest, restBool)
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

        let icond = ICondElse iexpr iblock1 iblock2 (MD md)
        if returnBoolean1 && returnBoolean2
          then return ([icond], True)
          else BiFunctor.first (icond:) <$> stmtsToInternal rest
-- Legacy --
stmtsToInternal ((While pos expr stmt md):rest) = do
  let ascmd = DS.toAscList  md
  venv<- gets tsVarState
  let venv' = makeDynamic ascmd venv
  modify $ tsModifyVarState (const venv')
  modify $ tsModifyVarState (protectVars_ ascmd)

  (itype, ivalue, iexpr) <- exprToInternal expr
  unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
  case ivalue of
    (IValueBool False) -> modify (tsModifyVarState endProtection) >> stmtsToInternal rest
    _ -> do
      (iblock, returnBoolean) <- blockToInternal $ VirtualBlock [stmt]
      modify $ tsModifyVarState endProtection
      BiFunctor.first (IWhile iexpr iblock (MD md):) <$> stmtsToInternal rest
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
-- -- New Version --
-- stmtsToInternal ((While pos expr stmt md):rest) = do
--   undefined
stmtsToInternal ((SExp _ expr):rest) =
  do
    (_, _, iexpr) <- exprToInternal expr
    BiFunctor.first (ISExp iexpr:) <$> stmtsToInternal rest
stmtsToInternal ((Empty pos):rest) = stmtsToInternal rest


blockToInternal :: Block -> Compiler TranslatorState (IBlock, Bool)
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

topDefToInternal :: TopDef -> FunctionEnvironment -> CompilerExcept IFun
topDefToInternal fDef fEnv = let
  funName = getIdStr fDef
  funArgs = [(getIdStr i, getArgLType i) | i <- topDefArgs fDef]
  retType = fst $ (LVoid, []) `fromMaybe` DM.lookup funName fEnv
  block = topDefBlock fDef
  newVarState = foldl (\vEnv (id, ltype) ->
                         declareVar id (ltype, RunTimeValue) vEnv)
                (openClosure newVarEnv) funArgs
  tsEnv :: TranslatorEnvironment
  tsEnv = (fEnv, (retType, funName, getPosition fDef))
  res = (`evalStateT` tsSetVarState newVarState tsInit) $ runReaderT (blockToInternal block) tsEnv
  in
    do
      x <- res
      unless (snd x || retType == LVoid) (throwError $ SemanticError (getPosition fDef) (NoReturnValue retType))
      return $ IFun funName retType funArgs (fst x)

assertMain :: FunctionEnvironment -> CompilerExcept ()
assertMain fEnv =
  let
    main = DM.lookup "main" fEnv
    in
    case main of
      Just (LInt, _) -> return ()
      _ -> throwError $ SemanticError (0,0) NoMain

programToInternal :: Program -> CompilerExcept [IFun]
programToInternal program@(Program _ topDefs) =
  let
    x :: CompilerExcept ()
    x = return ()
    fun :: FunctionEnvironment -> CompilerExcept () -> TopDef -> CompilerExcept ()
    fun fEnv monad topDef = do
      topDefToInternal topDef fEnv
      monad
  in
    do
      fEnv <- getFunctionEnvironment program
      assertMain fEnv
      mapM (`topDefToInternal` fEnv) topDefs

class Castable a b where
  cast_ :: a -> b

class Convertable a b where
  convert :: a -> b

class TypedBiOperator a b where
  assertOpType :: a -> b -> b -> Compiler c ()

instance TypedBiOperator AddOp IType where
  assertOpType op@(Plus _) left right = do
    (_,_,pos) <- asks teFunctionContext
    unless ((left `same` right) && ((left `same` LInt)  || (left `same` LString))) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))
  assertOpType op@(Minus _) left right = do
    (_,_,pos) <- asks teFunctionContext
    unless ((left `same` right) && (left `same` LInt)) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))

errorDivisonByZero :: MulOp -> Compiler a ()
errorDivisonByZero op = do
  (_, _, pos) <- asks teFunctionContext
  throwError $ SemanticError pos (DivisionByZero (getPosition op))
-- assertDivision :: MulOp -> IExpr -> Compiler FunTranslationEnvironment ()
-- assertDivision op@(Div pos) (ILitInt 0) = errorDivisonByZero op
-- assertDivision op@(Mod pos) (ILitInt 0) = errorDivisonByZero op
-- assertDivision _ _= return ()


instance TypedBiOperator MulOp IType where
  assertOpType op left right = do
    (a,b,pos) <- asks teFunctionContext
    unless ((left `same` right) && (left `same` LInt)) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))

-- instance TypedBiOperator MulOp IType where
--   assertOpType op@(Div pos) _ (StaticInt 0) = errorDivisonByZero op
--   assertOpType op@(Mod pos) _ (StaticInt 0) = errorDivisonByZero op
--   assertOpType op left right = assertOpType op (cast left) (cast right)

instance TypedBiOperator RelOp IType where
  assertOpType op x y = let
    errorFun :: (Int, Int) -> IType -> IType -> Compiler a ()
    errorFun pos ltype rtype = do
      (_, _, context) <- asks teFunctionContext
      throwError (SemanticError context $BinaryTypeConflict pos (ltype, rtype))
    tmp :: RelOp -> IType -> IType -> Compiler a ()
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
      foldl (\set instr -> getCalledFunctionInstr instr set) set stmts
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
                      "_strneq"]
      _externalFunDSet = DS.union loopingFunctions (DS.fromList _externalDyn)
      _dynamicFunctions = buildDynamic _depMap _externalFunDSet _externalFunDSet
      _somehowCalledFun = DS.intersection (DS.fromList _externalFun) $
                          foldl (\set pair -> set `DS.union` snd pair) DS.empty y
  in
    FM _somehowCalledFun _dynamicFunctions

data FunctionMetadata = FM {usedExternal :: DS.Set String,
                            dynamicFunctions :: DS.Set String}

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
