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
    stmtsToInternal,
    functionMetaDataNew,
    FunctionMetadata(..)
  ) where

import IDefinition


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
import DynFlags (GeneralFlag(Opt_BuildDynamicToo))
import qualified Control.Monad as DS
import qualified VariableEnvironment as VE
import qualified VariableEnvironment as DS

type VariableEnvironment = VarEnv String IType

data IType = StaticInt Integer | DynamicInt | StaticBool Bool | DynamicBool |
              StaticString String | DynamicString | IVoid

data MetaData = MD {modVars :: DS.Set String}

data IStmt =  IBStmt IBlock |
  IDecl [IItem] |
  IAss String IExpr |
  IIncr String |
  IDecr String |
  IRet IExpr |
  IVRet |
  ICond IExpr IBlock MetaData |
  ICondElse IExpr IBlock IBlock MetaData |
  IWhile IExpr IBlock MetaData|
  ISExp IExpr |
  IStmtEmpty

newtype IBlock = IBlock [IStmt]

data IItem = IItem String IExpr

data IMulOp = ITimes | IDiv | IMod
  deriving Eq
data IAddOp = IPlus | IMinus
  deriving Eq
data IRelOp = ILTH | ILE | IGTH | IGE | IEQU | INE
  deriving Eq

data IExpr = IVar String |
  ILitInt Integer |
  ILitBool Bool |
  IApp String [IExpr] |
  IString String |
  INeg IExpr |
  INot IExpr |
  IAnd [IExpr] |
  IOr [IExpr] |
  IAdd IAddOp IExpr IExpr |
  IMul IMulOp IExpr IExpr |
  IRel IRelOp IExpr IExpr
  deriving Eq

data IFun = IFun String LType [(String, LType)] IBlock
type FunctionData = (LType, [LType])
type FunctionEnvironment = DM.Map String FunctionData
type FunContext = (LType, String, (Int, Int))
type FunTranslationEnvironment = (FunContext, VariableEnvironment)
type CompilerExcept = Except SemanticError
type StateStrMap x = State (DM.Map String x)
type Compiler varEnv = ReaderT FunctionEnvironment (StateT varEnv CompilerExcept)

getFunctionEnvironment :: Program -> CompilerExcept FunctionEnvironment
getFunctionEnvironment (Program _ topDef) =
  let
    getFunctionData :: TopDef -> CompilerExcept FunctionData
    getFunctionData f@(FnDef pos returnType id args _) =
      let
        argsLTypeList :: [LType]
        argsLTypeList = Prelude.map getArgLType args
        returnLtype = convertType returnType
        getRedefinedArg :: [Arg] -> [Arg] -> Maybe(Arg, Arg)
        getRedefinedArg x [] = Nothing
        getRedefinedArg x (y@(Arg _ _ (Ident yid)):ys) =
          case DL.find (\arg -> yid == getIdStr arg) x of
            (Just leftMost) -> Just (leftMost, y)
            Nothing -> getRedefinedArg (y:x) ys
        redefinedArg = getRedefinedArg [] args
      in
        case redefinedArg of
          Nothing -> return (returnLtype, argsLTypeList)
          Just (old, new) ->
            let
              x :: SemanticErrorType
              x = RedefinitionOfVariable (getPosition new) (getPosition old) (getIdStr old)
            in
              throwError $ SemanticError (getPosition f) x
    checkFunction :: TopDef -> StateStrMap (Int,Int) (CompilerExcept FunctionEnvironment)
      -> StateStrMap (Int,Int) (CompilerExcept FunctionEnvironment)
    checkFunction topDef monad =
      let topName = getIdStr topDef in
      monad >>= (\fe ->
                    do
                      map <- get
                      if DM.member topName map then
                        return $ throwError (SemanticError (getPosition topDef)
                                             (RedefinitionOfFunction (getPosition topDef)
                                              ((-1, -1) `fromMaybe` DM.lookup topName map) topName))
                        else
                        do
                          put (DM.insert topName (getPosition topDef) map)
                          return $ do
                              fd <- getFunctionData topDef;
                              DM.insert topName fd <$> fe)
    initialEnvironment :: FunctionEnvironment
    initialEnvironment = DM.fromList [("printInt", (LVoid, [LInt])), ("printString", (LVoid, [LString])),
                                     ("error", (LVoid, [])), ("readInt", (LInt, [])), ("readString", (LString, []))]
    result = Prelude.foldl (flip checkFunction) (return $ return initialEnvironment) topDef
  in
    evalState result DM.empty

lTypeToIType :: LType -> IType
lTypeToIType LInt = DynamicInt
lTypeToIType LBool = DynamicBool
lTypeToIType LString = DynamicString
lTypeToIType _ = undefined

f :: Expr -> Compiler FunTranslationEnvironment (IType, IExpr)
f (ELitInt _ x) = return (StaticInt x, ILitInt x)
f (ELitTrue _) = return (StaticBool True, ILitBool True)
f (ELitFalse _) = return (StaticBool False, ILitBool False)
f (EString _ str) = return (StaticString str, IString str)
f e@(Not pos expr) = do
  (etype, iexp) <- exprToInternal expr
  unless (etype `same` LBool) $ throwErrorInContext (TypeConflict (getPosition e) LBool (cast etype))
  return (etype, INot iexp)
f (EOr pos e1 e2) = let
  x :: (IType, IExpr) -> Expr -> Compiler FunTranslationEnvironment (IType, IExpr)
  x (StaticBool False, _) exp =
    do
      (itype, iExp) <- exprToInternal exp
      unless (itype `same` LBool) $ throwErrorInContext (TypeConflict ((-1, -1) `fromMaybe` pos) LBool (cast itype))
      return (itype, iExp)
  x left@(DynamicBool, iLeft) exp =
    do
      (itype, iRight) <- exprToInternal exp
      case itype of
        -- (StaticBool True) -> return (DynamicBool, IOr iLeft iRight) -- 30.12 Przed optymalizacją
        (StaticBool True) -> return (DynamicBool, iLeft) -- 30.12 Po optymalizacją
        (StaticBool False) -> return left
        DynamicBool -> case iRight of
          IOr ies -> return $ (DynamicBool, IOr (iLeft:ies))
          _ -> return (DynamicBool, IOr [iLeft, iRight])
        _ -> throwErrorInContext (TypeConflict (getPosition e2) LBool (cast itype))
  x left@(StaticBool True, _) _ = return left
  x (ltype, _) _ = throwErrorInContext (TypeConflict (getPosition e1) LBool (cast ltype))
  in
    exprToInternal e1 >>= flip x e2
f (EAnd pos e1 e2) =
  let
      x :: (IType, IExpr) -> Expr -> Compiler FunTranslationEnvironment (IType, IExpr)
      x (StaticBool True, _) exp =
        do
          (itype, iExp) <- exprToInternal exp
          unless (itype `same` LBool) $ throwErrorInContext (TypeConflict (getPosition e2) LBool (cast itype))
          return (itype, iExp)
      x left@(DynamicBool, iLeft) exp =
        do
          (itype, iRight) <- exprToInternal exp
          case itype of
            (StaticBool False) -> return (StaticBool False, ILitBool False)
            (StaticBool True) -> return left
            DynamicBool -> case iRight of
              IAnd ies -> return (DynamicBool, IAnd (iLeft:ies))
              _ -> return (DynamicBool, IAnd [iLeft, iRight])
            _ -> throwErrorInContext (TypeConflict (getPosition e2) LBool (cast itype))
      x left@(StaticBool False, _) _ = return left
      x (ltype, _) _ = throwErrorInContext (TypeConflict (getPosition e1) LBool (cast ltype))
  in
    exprToInternal e1 >>= flip x e2
f (EMul pos e1 op e2) = do
  (type1, ie1) <- f e1
  (type2, ie2) <- f e2
  assertOp op type1 type2
  if iTypeStatic type1 && iTypeStatic type2
    then
    let (StaticInt x) = type1
        (StaticInt y) = type2
        res = appOp op x y
        in
        return (StaticInt res, ILitInt res)
    else
    return (DynamicInt, IMul (mulToIMul op) ie1 ie2)
f (EAdd pos e1 op e2) =
  let
    helper :: (IType, IExpr) -> (IType, IExpr) -> AddOp -> Compiler FunTranslationEnvironment (IType, IExpr)
    helper (StaticString x, _) (StaticString y, _) (Plus pos) = do
      return $ (\z -> (StaticString z, IString z)) (x ++ y)
    helper (StaticInt x, _) (StaticInt y, _) op =
      return $ (\z -> (StaticInt z, ILitInt z)) $ appOp op x y
    helper left right op = do
      assertOp op (fst left) (fst right)
      return (if fst left `same` LInt then DynamicInt else DynamicString,
              IAdd (addtoIAdd op) (snd left) (snd right))
  in
    do
      result1 <- f e1
      result2 <- f e2
      helper result1 result2 op

f (ERel pos e1 op e2) = let
  helper :: RelOp -> (IType, IExpr) -> (IType, IExpr) -> (IType, IExpr)
  helper op (StaticInt x, _) (StaticInt y, _) =
    (\boolean -> (StaticBool boolean, ILitBool boolean)) (appOp op x y)
  helper op (StaticBool x, _) (StaticBool y, _) =
    (\boolean -> (StaticBool boolean, ILitBool boolean)) (appOp op x y)
  helper op (StaticString x, _) (StaticString y, _) =
    (\boolean -> (StaticBool boolean, ILitBool boolean)) (appOp op x y)
  helper op (_, left) (_, right)  = (DynamicBool, IRel (reltoIRel op) left right)
  in
    do
      r1@(it1, ie1) <- exprToInternal e1
      r2@(it2, ie2) <- exprToInternal e2
      assertOp op it1 it2
      return $ helper op r1 r2
f (EVar pos (Ident varId)) = do
  (_, vEnv) <- get
  let var = varId `lookupVar` vEnv
  case var of
    Nothing -> throwErrorInContext (UndefinedVar ((-1, -1) `fromMaybe` pos) varId)
    Just itype -> return
      (case itype of
        (StaticInt x) -> (itype, ILitInt x)
        (StaticBool x) -> (itype, ILitBool x)
        (StaticString x) -> (itype, IString x)
        _ -> (itype, IVar varId))
f (EApp pos (Ident funId) exps) = do
  fEnv <- ask
  let funData = funId `DM.lookup` fEnv
      errPos = (-1, -1) `fromMaybe` pos
  case funData of
    Nothing -> throwErrorInContext (UndefinedFun ((-1, -1) `fromMaybe` pos) funId)
    Just (rType, argTypes) -> do
      tmp <- exprToInternal `mapM` exps
      iArgs <- foldr (\(dType, (iType, iExpr)) monad ->
               do
                 list <- monad
                 unless (dType `same` iType) $ throwErrorInContext (TypeConflict errPos dType (cast iType))
                 return $ iExpr:list
            )(return []) (zip argTypes tmp)
      unless (length argTypes == length tmp) $ throwErrorInContext (WrongArgumentCount errPos)
      return (lTypeToIType rType, IApp funId iArgs)
f e0@(Neg pos expr) = do
  (itype, iexpr) <- f expr
  unless (itype `same` LInt) $ throwErrorInContext (TypeConflict (getPosition e0) LInt (cast itype))
  return $
    case itype of
      (StaticInt x) -> (StaticInt (-x), ILitInt (-x))
      _ -> (DynamicInt, INeg iexpr)

simplify :: (IType, IExpr) -> (IType, IExpr)
simplify pair = pair

exprToInternal :: Expr -> Compiler FunTranslationEnvironment (IType, IExpr)
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

iTypeStatic :: IType -> Bool
iTypeStatic (StaticInt _) = True
iTypeStatic (StaticBool _) = True
iTypeStatic (StaticString _) = True
iTypeStatic _ = False

throwErrorInContext :: SemanticErrorType -> Compiler FunTranslationEnvironment a
throwErrorInContext errtype  =
  do
    (a,b, pos) <- gets fst
    throwError $ SemanticError pos errtype


itemToInternal :: LType -> Item -> Compiler FunTranslationEnvironment IItem
itemToInternal varType item =
  do
    let id = getIdStr item
    ftEnv@(context@(ltype, funName, pos), venv) <- get
    if id `DS.member` head (redeclaredVars venv)
      then throwError $ SemanticError pos (RedefinitionOfVariable (getPosition item) (getPosition item) id)
      else
      do
        let expr = case item of
              NoInit _ _ -> defaultExpr varType
              Init _ _ ex -> ex
        (itype, iexpr) <- exprToInternal expr
        unless (varType `same` itype) (throwErrorInContext $ TypeConflict (getPosition item) varType (cast itype))
        (c, venv) <- get
        put (c, declareVar id itype venv)
        return (IItem id iexpr)

itemsToInternals :: LType -> [Item] -> Compiler FunTranslationEnvironment [IItem]
itemsToInternals _ [] = return []
itemsToInternals ltype (item:rest) =
  do
    head <- itemToInternal ltype item
    tail <- itemsToInternals ltype rest
    return $ head:tail

-- stmtToInternal (BStmt _ block) = do
--   (iBlock, returned) <- (\(retType, VEnv set map) -> (retType,VEnv DS.empty map)) `local` blockToInternal block
--   return (IBStmt iBlock, returned)

stmtsToInternal :: [Stmt] -> Compiler FunTranslationEnvironment ([IStmt], Bool)
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
stmtsToInternal (stm@(Ass pos ident expr):rest) = do
  env@(context, vEnv) <- get
  let (Ident id)= ident
      x =  id `lookupVar` vEnv
  case x of
        Nothing -> throwErrorInContext (UndefinedVar (getPosition stm) id)
        Just xType ->
          do
            (assType, assIExpr) <- exprToInternal expr
            unless (xType `same` assType) $ throwErrorInContext
              (TypeConflict (getPosition stm) (cast xType) (cast assType))
            modify $ Data.Bifunctor.second (setVar id assType)
            (irest, returnBool) <-  stmtsToInternal rest
            return (IAss id assIExpr:irest, returnBool)
stmtsToInternal ((Incr pos (Ident varId)):rest) = do
  env@(context, vEnv) <- get
  let x =  varId `lookupVar` vEnv
      stmtpos = (-1,-1) `fromMaybe` pos
  case x of
        Nothing -> throwErrorInContext (UndefinedVar stmtpos varId)
        Just xType -> do
          unless (xType `same` LInt) $ throwErrorInContext (TypeConflict stmtpos LInt (cast xType))
          let
            modifyFun = case xType of
                StaticInt val -> Data.Bifunctor.second (setVar varId (StaticInt (val + 1)))
                _ -> id
          modify modifyFun
          (irest, returnBool) <- stmtsToInternal rest
          return (IIncr varId:irest, returnBool)
stmtsToInternal ((Decr pos (Ident varId)):rest) = do
  env@(context, vEnv) <- get
  let x =  varId `lookupVar` vEnv
      stmtpos = (-1,-1) `fromMaybe` pos
  case x of
        Nothing -> throwErrorInContext (UndefinedVar stmtpos varId)
        Just xType -> do
          unless (xType `same` LInt) $ throwErrorInContext (TypeConflict stmtpos LInt (cast xType))
          let
            modifyFun = case xType of
              StaticInt val -> Data.Bifunctor.second (setVar varId (StaticInt (val - 1)))
              _ -> id
          modify modifyFun
          (irest, returnBool) <- stmtsToInternal rest
          return (IDecr varId:irest, returnBool)
stmtsToInternal ((Ret pos expr):rest) =
  do
    ((funType, _, _), _) <- get
    (itype, iexpr) <- exprToInternal expr
    unless (itype `same` funType) (throwErrorInContext
      (WrongReturnType ((-1,-1) `fromMaybe` pos) funType (cast itype)))
    return ([IRet iexpr], True)
stmtsToInternal ((VRet pos):rest) =   do
  ((funType, _, _), _) <- get
  unless (funType `same` LVoid) $ throwErrorInContext
    (WrongReturnType ((-1,-1) `fromMaybe` pos) funType LVoid)
  return ([IVRet], True)
stmtsToInternal ((Cond pos expr stmt md): rest) = do
  (itype, iexpr) <- exprToInternal expr
  unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
  case itype of
    (StaticBool False) -> stmtsToInternal rest
    (StaticBool True) -> stmtsToInternal (BStmt pos (Block pos [stmt]):rest)
    _ -> do
      modify $ BiFunctor.second (protectVars_ md)
      (iblock, returnBoolean) <- blockToInternal $ VirtualBlock [stmt]
      modify $ BiFunctor.second endProtection
      (irest, restBool) <- stmtsToInternal rest
      let icond = ICondElse iexpr iblock (IBlock []) (MD md)
      return (icond:irest, restBool)

stmtsToInternal ((CondElse pos expr stmt1 stmt2 md):rest) =
  do
    (itype, iexpr) <- exprToInternal expr
    unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
    case itype of
      (StaticBool False) -> stmtsToInternal (BStmt pos (Block pos [stmt2]):rest)
      (StaticBool True) -> stmtsToInternal (BStmt pos (Block pos [stmt1]):rest)
      _ -> do

        modify $ BiFunctor.second (protectVars_ md)
        (iblock1, returnBoolean1) <- blockToInternal $ VirtualBlock [stmt1]
        modify $ BiFunctor.second endProtection

        modify $ BiFunctor.second (protectVars_ md)
        (iblock2, returnBoolean2) <- blockToInternal $ VirtualBlock [stmt2]
        modify $ BiFunctor.second endProtection

        let icond = ICondElse iexpr iblock1 iblock2 (MD md)
        if returnBoolean1 && returnBoolean2
          then return ([icond], True)
          else BiFunctor.first (icond:) <$> stmtsToInternal rest

stmtsToInternal ((While pos expr stmt md):rest) = do
  (itype, iexpr) <- exprToInternal expr
  unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
  case itype of
    (StaticBool False) -> stmtsToInternal rest
    _ -> do
      (_, venv)<- get
      let ascmd = toList md
      modify $ BiFunctor.second (protectVars ascmd (toDynamic ascmd venv))
      (iblock, returnBoolean) <- blockToInternal $ VirtualBlock [stmt]
      modify $ BiFunctor.second endProtection
      BiFunctor.first (IWhile iexpr iblock (MD md):) <$> stmtsToInternal rest
  where
    toDynamic :: [String] -> VariableEnvironment -> [IType]
    toDynamic ss venv = map
      (\key ->
          case lookupVar key venv of
            Just x -> case x of
              StaticInt n -> DynamicInt
              DynamicInt -> DynamicInt
              StaticBool b -> DynamicBool
              DynamicBool -> DynamicBool
              StaticString s -> DynamicString
              DynamicString -> DynamicString
            Nothing -> IVoid)
      ss
stmtsToInternal ((SExp _ expr):rest) =
  do
    (_, iexpr) <- exprToInternal expr
    BiFunctor.first (ISExp iexpr:) <$> stmtsToInternal rest
stmtsToInternal ((Empty pos):rest) = stmtsToInternal rest

blockToInternal :: Block -> Compiler FunTranslationEnvironment (IBlock, Bool)
blockToInternal block =
  let
    stmts = case block of
      Block pos stmts -> stmts
      VirtualBlock stmts -> stmts
  in
    do
      modify (BiFunctor.second openClosure)
      result <- stmtsToInternal stmts
      modify (BiFunctor.second closeClosure)
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
  nvEnv = foldl (\vEnv (id, ltype) -> declareVar id (lTypeToIType ltype) vEnv) (openClosure newVarEnv) funArgs
  res = (`evalStateT` ((retType, funName, getPosition fDef), nvEnv)) $ runReaderT (blockToInternal block) fEnv
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

instance TypeClass IType where
  cast (StaticInt _) = LInt
  cast DynamicInt = LInt
  cast (StaticBool _) = LBool
  cast DynamicBool = LBool
  cast (StaticString _) = LString
  cast DynamicString = LString

class IItemValue a where
  defaultValue :: a -> IExpr

class Convertable a b where
  convert :: a -> b

class ApplicativeBiOperator a b c where
  appOp :: a -> b -> b -> c

instance Integral a => ApplicativeBiOperator AddOp a a where
  appOp (Plus _) = (+)
  appOp (Minus _) = (-)

instance ApplicativeBiOperator MulOp Integer Integer where
  appOp (Times _) = (*)
  appOp (Div _) = div
  appOp (Mod _) = mod

instance Ord a => ApplicativeBiOperator RelOp a Bool where
  appOp (LTH _)  = (<)
  appOp (LE _)   = (<=)
  appOp (EQU _)  = (==)
  appOp (NE _)   = (/=)
  appOp (GTH _)  = (>=)
  appOp (GE _)   = (>)

instance ApplicativeBiOperator IAddOp Integer Integer where
  appOp IPlus = (+)
  appOp IMinus = (-)

instance ApplicativeBiOperator IMulOp Integer Integer where
  appOp ITimes = (*)
  appOp IDiv = div
  appOp IMod = mod

instance Ord a => ApplicativeBiOperator IRelOp a Bool where
  appOp ILTH  = (<)
  appOp ILE   = (<=)
  appOp IEQU  = (==)
  appOp INE   = (/=)
  appOp IGTH  = (>=)
  appOp IGE   = (>)

class TypedBiOperator a b where
  assertOp :: a -> b -> b -> Compiler FunTranslationEnvironment ()


instance TypedBiOperator AddOp LType where
  assertOp op@(Plus _) left right = do
    (a,b,pos) <- gets fst
    unless ((left `same` right) && ((left `same` LInt)  || (left `same` LString))) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))
  assertOp op@(Minus _) left right = do
    (a,b,pos) <- gets fst
    unless ((left `same` right) && (left `same` LInt)) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))

instance TypedBiOperator AddOp IType where
  assertOp op left right = assertOp op (cast left) (cast right)

errorDivisonByZero :: MulOp -> Compiler FunTranslationEnvironment ()
errorDivisonByZero op = do
  ((_, _, pos), _) <- get
  throwError $ SemanticError pos (DivisionByZero (getPosition op))
assertDivision :: MulOp -> IExpr -> Compiler FunTranslationEnvironment ()
assertDivision op@(Div pos) (ILitInt 0) = errorDivisonByZero op
assertDivision op@(Mod pos) (ILitInt 0) = errorDivisonByZero op
assertDivision _ _= return ()


instance TypedBiOperator MulOp LType where
  assertOp op left right = do
    (a,b,pos) <- gets fst
    unless ((left `same` right) && (left `same` LInt)) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))
instance TypedBiOperator MulOp IType where
  assertOp op@(Div pos) _ (StaticInt 0) = errorDivisonByZero op
  assertOp op@(Mod pos) _ (StaticInt 0) = errorDivisonByZero op
  assertOp op left right = assertOp op (cast left) (cast right)

instance TypedBiOperator RelOp LType where
  assertOp op x y = let
    errorFun :: (Int, Int) -> LType -> LType -> Compiler FunTranslationEnvironment ()
    errorFun pos ltype rtype = do
      (a, b, context) <- gets fst
      throwError (SemanticError pos $BinaryTypeConflict pos (ltype, rtype))
    tmp :: RelOp -> LType -> LType -> Compiler FunTranslationEnvironment ()
    tmp op@(EQU _) x y = do
      unless ((x `same` y) && (x `same` LInt || x `same` LString || x `same` LBool)) $ errorFun (getPosition op) x y
    tmp (NE pos) x y = tmp (EQU pos) x y
    tmp (LTH pos) x y = do
      unless (x `same` LInt && (x `same` y)) $ errorFun (getPosition op) x y
    tmp op x y = assertOp (LTH $ hasPosition op) x y
    in
      tmp op x y

instance TypedBiOperator RelOp IType where
  assertOp op x y = assertOp op (cast x) (cast y)


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
      IVar s -> set
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
      buildDynamic :: DM.Map String (DS.Set String) -> DS.Set String -> DS.Set String -> DS.Set String
      buildDynamic map emplaced set = if null emplaced then set else
        let  emplaced' = foldl (\emplaced' name ->
                                  DS.union emplaced'
                                  (DS.difference (DS.empty `fromMaybe` DM.lookup name map) set))
                         DS.empty emplaced
        in
          buildDynamic map emplaced' (DS.union emplaced' set)
      _depMap = buildDepMap y
      _external = ["printInt", "printString", "error", "readInt", "readString"]
      _externalFunSet = DS.fromList _external
      _dynamicFunctions = buildDynamic _depMap _externalFunSet _externalFunSet
      _somehowCalledFun = DS.intersection _externalFunSet $
                          foldl (\set pair -> set `DS.union` snd pair) DS.empty y
  in
    FM _somehowCalledFun _dynamicFunctions

data FunctionMetadata = FM {usedExternal :: DS.Set String,
                            dynamicFunctions :: DS.Set String}

--------------------------------------------------------------------------------------------------

trOptimizeLoop :: DynamicFunction -> IBlock -> IBlock

type DynamicFunction = DS.Set String
type DynamicVariables = VE.VarEnv String Bool
type OptimizeLoopEnv = DynamicFunction
type OptimizeLoopSt = (Int, DM.Map String String, DynamicVariables, DummyAssignments)
type DummyAssignments = [(String, IExpr)]
type LoopOptimizer = ReaderT OptimizeLoopEnv (State OptimizeLoopSt)



oleIsFunStatic:: String -> OptimizeLoopEnv -> Bool
oleIsFunStatic s env = not $ DS.member s env

olsInit :: [String] -> OptimizeLoopSt
olsInit vars = (0, DM.empty,
                foldr (\x -> VE.declareVar x True) (VE.openClosure newVarEnv) vars,
                [])
olsLookup :: String -> OptimizeLoopSt -> Maybe String
olsLookup s (_, venv, _, _) = DM.lookup s venv
olsIsDynamic :: String -> OptimizeLoopSt -> Bool
olsIsDynamic s (_, _, set, _) = False `fromMaybe` VE.lookupVar s set

olsAddMap :: String -> String -> OptimizeLoopSt -> OptimizeLoopSt
olsAddMap x y (m1, venv, m2, m3) = (m1, DM.insert x y venv, m2, m3)
olsDeclareAsDynamic :: String -> OptimizeLoopSt -> OptimizeLoopSt
olsDeclareAsDynamic s (m1, m2, set, m3) = (m1, m2, DS.declareVar s True set, m3)
olsDeclareAsStatic :: String -> OptimizeLoopSt -> OptimizeLoopSt
olsDeclareAsStatic s (m1, m2, set, m3) = (m1, m2, DS.declareVar s False set, m3)

olsSetAsDynamic :: String -> OptimizeLoopSt -> OptimizeLoopSt
olsSetAsDynamic s (m1, m2, set, m3) = (m1, m2, DS.setVar s True set, m3)
olsSetAsStatic :: String -> OptimizeLoopSt -> OptimizeLoopSt
olsSetAsStatic s (m1, m2, set, m3) = (m1, m2, DS.setVar s False set, m3)


olsAddIe :: IExpr -> OptimizeLoopSt -> (String, OptimizeLoopSt)
olsAddIe ie (x, v, d, da) = let
  dummyvar = "_y" ++ show x
  in
  (dummyvar, (x + 1, v, d, (dummyvar, ie):da))

olsOpenBlock :: OptimizeLoopSt -> OptimizeLoopSt
olsOpenBlock (m1, m2, m3, m4) = (m1, m2, VE.openClosure m3, m4)
olsCloseBlock :: OptimizeLoopSt -> OptimizeLoopSt
olsCloseBlock (m1, m2, m3, m4) = (m1, m2, VE.closeClosure m3, m4)
-- olsProtectVars :: [String] -> OptimizeLoopSt -> OptimizeLoopSt
-- olsProtectVars vars (m1, m2, m3, m4) = (m1, m2, VE.protectVars_ vars m3, m4)
-- olsEndProtection :: OptimizeLoopSt -> OptimizeLoopSt
-- olsEndProtection (m1, m2, m3, m4) = (m1,  m2, VE.endProtection m3, m4)
loWithOpenBlock :: LoopOptimizer a -> LoopOptimizer a
loWithOpenBlock f = do
  modify olsOpenBlock
  res<-f
  modify olsCloseBlock
  return res

loWithProtectedVars :: LoopOptimizer a -> LoopOptimizer a
loWithProtectedVars f = do
  (_, m2, m3, _)<- get
  res <- f
  (m1, _, _, m4) <- get
  put (m1, m2, m3,m4)
  return res

trOptimizeIE :: (IExpr, Bool)  -> LoopOptimizer (IExpr)
trOptimizeIE (ie, x) =
  if x then
    do
      state <- get
      let (name, ols) = olsAddIe ie state
      put ols
      return $ IVar name
  else
    return ie

trOptimizeLoopBlockIL :: IBlock -> LoopOptimizer IBlock
trOptimizeLoopBlockIL (IBlock instr) = do
  loWithOpenBlock $ IBlock <$> mapM trOptimizeLoopIstmIL instr

trOptimizeLoopIItem :: IItem -> LoopOptimizer IItem
trOptimizeLoopIItem (IItem s ie) = do
  (ie', x) <- trOptimizeLoopIExprIl ie
  if x then do
      ols <- get
      let (s', ols') = olsAddIe ie ols
      put (olsAddMap s s'$ olsDeclareAsStatic s ols')
      return (IItem s (IVar s'))
    else do
    modify $ olsDeclareAsDynamic s
    return (IItem s ie')

trOptimizeLoopIstmIL :: IStmt -> LoopOptimizer IStmt
trOptimizeLoopIstmIL istmt =
  case istmt of
    IBStmt iblock -> IBStmt <$> trOptimizeLoopBlockIL iblock
    IDecl iis -> IDecl <$> mapM trOptimizeLoopIItem iis
    IAss s ie -> do
      (ie', x) <- trOptimizeLoopIExprIl ie
      if x then do
        ols <- get
        let (s', ols') = olsAddIe ie ols
        put (olsAddMap s s' $ olsSetAsStatic s ols')
        return $ IAss s (IVar s')
        else do
        modify $ olsSetAsDynamic s
        return $ IAss s ie'
    IIncr s -> do
      modify $ olsDeclareAsDynamic s
      return istmt
    IDecr s -> do
      modify $ olsDeclareAsDynamic s
      return istmt
    IRet ie -> IRet <$> (trOptimizeLoopIExprIl ie >>= trOptimizeIE)
    IVRet -> return istmt
    ICond ie ib md -> undefined
    --   ie' <- (trOptimizeLoopIExprIl ie >>= trOptimizeIE)
    --   (IBStmt ib') <- trOptimizeLoopIstmIL (IBStmt ib)
    --   return $ ICond ie' ib' md
    ICondElse ie ib1 ib2 (MD md) -> do
      ie' <- trOptimizeLoopIExprIl ie >>= trOptimizeIE
      ib1' <- loWithProtectedVars $ trOptimizeLoopBlockIL ib1
      ib2' <- loWithProtectedVars $ trOptimizeLoopBlockIL ib2
      ols <- get
      put $ DS.foldr olsSetAsDynamic ols md
      return $ ICondElse ie' ib1' ib2' (MD md)
    IWhile ie ib md -> return istmt
    ISExp ie -> ISExp <$> (trOptimizeLoopIExprIl ie >>= trOptimizeIE)
    IStmtEmpty -> undefined

olsIsStatic :: String -> OptimizeLoopSt -> Bool
olsIsStatic x y = not (olsIsDynamic x y)

trOptimizeLoopIExprIl :: IExpr -> LoopOptimizer (IExpr, Bool)
trOptimizeLoopIExprIl  iexp = do
  env   <- ask
  state <- get

  case iexp of
      IVar s -> if olsIsDynamic s state then return (iexp, False)
        else return (IVar (s`fromMaybe` olsLookup s state), True)
      ILitInt n -> return (iexp, True)
      ILitBool b -> return (iexp, True)
      IApp s ies -> do
        x <- mapM  trOptimizeLoopIExprIl ies
        let static = all snd x
        if static && oleIsFunStatic s env
          then return (iexp, True)
          else
          do
            ies' <- mapM trOptimizeIE x
            return (IApp s ies', False)
      IString s -> return (iexp, True)
      INeg ie -> do
        (ie', x) <- trOptimizeLoopIExprIl ie
        return (INeg ie', x)
      INot ie -> do
        (ie', x) <- trOptimizeLoopIExprIl ie
        return (INot ie', x)
      IAnd ies -> do
        list <- mapM trOptimizeLoopIExprIl ies
        let ok = all snd list
        if ok
          then return (iexp, True)
          else
          mapM trOptimizeIE list >>= (\ies -> return (IAnd ies, False))
      IOr ies -> do
        list <- mapM trOptimizeLoopIExprIl ies
        let ok = all snd list
        if ok
          then return (iexp, True)
          else
          mapM trOptimizeIE list >>= (\ies -> return (IOr ies, False))
      IAdd iao ie1 ie2 -> do
        x1 <- trOptimizeLoopIExprIl ie1
        x2 <- trOptimizeLoopIExprIl ie2
        if snd x1 && snd x2
          then return (iexp, True)
          else do
          ie1' <- trOptimizeIE x1
          ie2' <- trOptimizeIE x2
          return (IAdd iao ie1' ie2', False)
      IMul imo ie1 ie2 ->  do
        x1 <- trOptimizeLoopIExprIl ie1
        x2 <- trOptimizeLoopIExprIl ie2
        if snd x1 && snd x2
          then return (iexp, True)
          else do
          ie1' <- trOptimizeIE x1
          ie2' <- trOptimizeIE x2
          return (IMul imo ie1' ie2', False)
      IRel iro ie1 ie2 -> do
        x1 <- trOptimizeLoopIExprIl ie1
        x2 <- trOptimizeLoopIExprIl ie2
        if snd x1 && snd x2
          then return (iexp, True)
          else do
          ie1' <- trOptimizeIE x1
          ie2' <- trOptimizeIE x2
          return (IRel iro ie1' ie2', False)


trOptimizeLoop dfuns (IBlock stmts) =
  IBlock $ map f stmts
  where
    f :: IStmt-> IStmt
    f stmt = case stmt of
      IBStmt ib -> IBStmt $ trOptimizeLoop dfuns ib
      ICond ie ib md -> let
        ib' = trOptimizeLoop dfuns ib
        in
        ICond ie ib md
      ICondElse ie ibs ibf md -> let
        ibs' = trOptimizeLoop dfuns ibs
        ibf' = trOptimizeLoop dfuns ibf
        in
        ICondElse ie ibs' ibf' md
      IWhile ie ib (MD md) ->
        let
          monad = do
            ie' <- trOptimizeLoopIExprIl ie >>= trOptimizeIE
            ib' <- trOptimizeLoopBlockIL (trOptimizeLoop dfuns ib)
            return (ie', ib')
          ((ie', ib'), (_,_,_, da)) = flip runState (olsInit (DS.toList md)) $ runReaderT monad dfuns
          newWhile = IWhile ie' ib' (MD md)
          
          -- z = IBStmt $ IBlock $ map (\(s, iexp) ->IDecl [IItem s iexp] ) (reverse da)
          z = undefined  -- To powinno być if else
          newStmt = if null da
            then newWhile
            else IBStmt $ IBlock [z, newWhile]
        in
          newStmt
      _ -> stmt
