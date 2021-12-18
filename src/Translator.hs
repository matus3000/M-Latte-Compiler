{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Translator(programToInternal,
                  CompilerExcept,
                  IFun(..),
                  IBlock(..),
                  IStmt(..),
                  IExpr(..),
                  IItem(..),
                  Convertable(..),
                  IRelOp(..),
                  IAddOp(..),
                  IMulOp(..)) where


import IDefinition(LType(..), Indexed(..), getArgLType, convertType, topDefBlock, topDefArgs, getPosition, TypeClass (..), VarType ())
import CompilationError
import Latte.Abs

import Prelude
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
import Lexer (PState(context))

data VariableEnvironment = VEnv (DS.Set String) (DM.Map String [IType])

vEnvLookup :: String -> VariableEnvironment -> Maybe IType
vEnvLookup str (VEnv _ map) =
  case DM.lookup str map
  of
    Nothing -> Nothing
    Just [] -> Nothing
    Just (x:xs) -> Just x
vEnvUpdate ::  String -> IType -> VariableEnvironment ->  VariableEnvironment
vEnvUpdate str itype vEnv@(VEnv set map) =
  case DM.lookup str map
  of
    Just (x:xs) -> VEnv set $ DM.insert str (itype:xs) map
    _ -> vEnv
vEnvPush :: String -> IType -> VariableEnvironment ->  VariableEnvironment
vEnvPush str itype vEnv@(VEnv set map) = let oldValue = [] `fromMaybe` DM.lookup str map
  in
  if DS.member str set
  then vEnv
  else VEnv (DS.insert str set) (DM.insert str (itype:oldValue) map)
vEnvPop :: String -> VariableEnvironment -> VariableEnvironment
vEnvPop str vEnv@(VEnv set map) = let oldValue = [] `fromMaybe` DM.lookup str map
  in
  if DS.member str set
  then VEnv (DS.delete str set) $ DM.insert str (if null oldValue then oldValue else tail oldValue) map
  else vEnv
-- vEnvAddBlock :: VariableEnvironment ->  VariableEnvironment
-- vEnvRemoveBlock :: VariableEnvironment -> VariableEnvironment


data IType = StaticInt Integer | DynamicInt | StaticBool Bool | DynamicBool |
              StaticString String | DynamicString

data IStmt =  IBStmt IBlock |
  IDecl [IItem] |
  IAss String IExpr |
  IIncr String |
  IDecr String |
  IRet IExpr |
  IVRet |
  ICond IExpr IStmt |
  ICondElse IExpr IStmt IStmt |
  IWhile IExpr IStmt |
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
  IAnd IExpr IExpr |
  IOr IExpr IExpr |
  IAdd IAddOp IExpr IExpr |
  IMul IMulOp IExpr IExpr |
  IRel IRelOp IExpr IExpr
  deriving Eq

data IFun = IFun String LType [LType] IBlock
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
        (StaticBool True) -> return (DynamicBool, IOr iLeft iRight) -- Tu jest miejsce na optymalizację
        (StaticBool False) -> return left
        DynamicBool -> return (DynamicBool, IOr iLeft iRight)
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
            DynamicBool -> return (DynamicBool, IAnd iLeft iRight)
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
  let var = varId `vEnvLookup` vEnv
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
      errPos = ((-1, -1) `fromMaybe` pos)
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
      _ -> (DynamicInt, iexpr)

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
    ftEnv@(context@(ltype, funName, pos), VEnv set map) <- get
    if id `DS.member` set
      then throwError $ SemanticError pos (RedefinitionOfVariable (getPosition item) (getPosition item) id)
      else
      do
        let expr = case item of
              NoInit _ _ -> defaultExpr varType
              Init _ _ ex -> ex
        (itype, iexpr) <- exprToInternal expr
        unless (varType `same` itype) (throwErrorInContext $ TypeConflict (getPosition item) varType (cast itype))
        modify $ Data.BiFunctor.second (vEnvPush id itype)
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
  env@(context, vEnv) <- get
  let ltype = convertType dtype
  items <- itemsToInternals ltype items
  (istmts, ret) <- stmtsToInternal rest
  return (IDecl items:istmts, ret)
stmtsToInternal (stm@(Ass pos ident expr):rest) = do
  env@(context, vEnv) <- get
  let (Ident id)= ident
      x =  id `vEnvLookup` vEnv
  case x of
        Nothing -> throwErrorInContext (UndefinedVar (getPosition stm) id)
        Just xType ->
          do
            (assType, assIExpr) <- exprToInternal expr
            unless (xType `same` assType) $ throwErrorInContext
              (TypeConflict (getPosition stm) (cast xType) (cast assType))
            modify $ Data.Bifunctor.second (vEnvUpdate id assType)
            (irest, returnBool) <-  stmtsToInternal rest
            return (IAss id assIExpr:irest, returnBool)
stmtsToInternal ((Incr pos (Ident varId)):rest) = do
  env@(context, vEnv) <- get
  let x =  varId `vEnvLookup` vEnv
      stmtpos = (-1,-1) `fromMaybe` pos
  case x of
        Nothing -> throwErrorInContext (UndefinedVar stmtpos varId)
        Just xType -> do
          unless (xType `same` LInt) $ throwErrorInContext (TypeConflict stmtpos LInt (cast xType))
          let
            modifyFun = case xType of
                StaticInt val -> Data.Bifunctor.second (vEnvUpdate varId (StaticInt (val + 1)))
                _ -> id
          modify modifyFun
          (irest, returnBool) <- stmtsToInternal rest
          return (IIncr varId:irest, returnBool)
stmtsToInternal ((Decr pos (Ident varId)):rest) = do
  env@(context, vEnv) <- get
  let x =  varId `vEnvLookup` vEnv
      stmtpos = (-1,-1) `fromMaybe` pos
  case x of
        Nothing -> throwErrorInContext (UndefinedVar stmtpos varId)
        Just xType -> do
          unless (xType `same` LInt) $ throwErrorInContext (TypeConflict stmtpos LInt (cast xType))
          let
            modifyFun = case xType of
              StaticInt val -> Data.Bifunctor.second (vEnvUpdate varId (StaticInt (val - 1)))
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
stmtsToInternal ((Cond pos expr stmt): rest) = do
  (itype, iexpr) <- exprToInternal expr
  unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
  case itype of
    (StaticBool False) -> stmtsToInternal rest
    (StaticBool True) -> stmtsToInternal (stmt:rest)
    _ -> do
      (istmt, returnBoolean) <- stmtsToInternal [stmt]
      (irest, restBool) <- stmtsToInternal rest
      return ((head istmt):irest, restBool)
      
stmtsToInternal ((CondElse pos expr stmt1 stmt2):rest) =
  do
    (itype, iexpr) <- exprToInternal expr
    unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
    case itype of
      (StaticBool False) -> stmtsToInternal (stmt2:rest)
      (StaticBool True) -> stmtsToInternal (stmt1:rest)
      _ -> do
        (istmt1, returnBoolean1) <- stmtsToInternal [stmt1]
        (istmt2, returnBoolean2) <- stmtsToInternal [stmt2]
        if returnBoolean1 && returnBoolean2
          then return ([ICondElse iexpr (head istmt1) (head istmt2)], True)
          else BiFunctor.first (ICondElse iexpr (head istmt1) (head istmt2):) <$> stmtsToInternal rest
stmtsToInternal ((While pos expr stmt):rest) = do
  (itype, iexpr) <- exprToInternal expr
  unless (itype `same` LBool) (throwErrorInContext (TypeConflict ((-1,-1) `fromMaybe` pos) LBool (cast itype)))
  case itype of
    (StaticBool False) -> stmtsToInternal rest
    -- (StaticBool True) ->
    --   do
    --     (istmts, returnBoolean) <- stmtsToInternal [stmt]
    --     return ([IWhile iexpr (head istmts)], returnBoolean)
    _ -> do
      (istmts, returnBoolean) <- stmtsToInternal [stmt]
      BiFunctor.first (IWhile iexpr (head istmts):) <$> stmtsToInternal rest
stmtsToInternal ((SExp _ expr):rest) =
  do
    (_, iexpr) <- exprToInternal expr
    BiFunctor.first (ISExp iexpr:) <$> stmtsToInternal rest
stmtsToInternal ((Empty pos):rest) = stmtsToInternal rest

blockToInternal :: Block -> Compiler FunTranslationEnvironment (IBlock, Bool)
blockToInternal block@(Block x stmts) =
  let
    startBlock :: FunTranslationEnvironment -> FunTranslationEnvironment
    endBlock :: FunTranslationEnvironment -> FunTranslationEnvironment
    startBlock = (\(context, VEnv set map) -> (context, VEnv DS.empty map))
    endBlock (context, vEnv@(VEnv set map)) = (context, foldl (flip vEnvPop) vEnv set)
  in
    do
      oldState <- get
      modify startBlock
      result <- stmtsToInternal stmts
      modify endBlock
      return $ Data.BiFunctor.first IBlock result


topDefToInternal :: TopDef -> FunctionEnvironment -> CompilerExcept IFun
topDefToInternal fDef fEnv = let
  funName = getIdStr fDef
  funArgs = [(getIdStr i, getArgLType i) | i <- topDefArgs fDef]
  retType = fst $ (LVoid, []) `fromMaybe` DM.lookup funName fEnv
  block = topDefBlock fDef
  vEnv :: VariableEnvironment
  vEnv = VEnv DS.empty DM.empty
  nvEnv = foldl (\vEnv (id, ltype) -> vEnvPush id (lTypeToIType ltype) vEnv) vEnv funArgs
  res = (`evalStateT` ((retType, funName, getPosition fDef), nvEnv)) $ runReaderT (blockToInternal block) fEnv
  in
    do
      x <- res
      unless (snd x || retType == LVoid) (throwError $ SemanticError (getPosition fDef) (NoReturnValue retType))
      return $ IFun funName retType (snd `map` funArgs) (fst x)

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
    (a,b,pos) <- fst <$> get
    unless ((left `same` right) && ((left `same` LInt)  || (left `same` LString))) $
      throwError (SemanticError pos $ BinaryTypeConflict (getPosition op) (left, right))
  assertOp op@(Minus _) left right = do
    (a,b,pos) <- fst <$> get
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
    (a,b,pos) <- fst <$> get
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
      (a, b, context) <- fst <$> get
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
