{-# LANGUAGE MultiParamTypeClasses #-}

module Translator(programToInternal, CompilerExcept) where


import IDefinition(LType(..), Indexed(..), getArgLType, convertType, topDefBlock, topDefArgs, getPosition, TypeClass (..), VarType ())
import CompilationError
import Latte.Abs

import Data.Maybe (fromMaybe)
import Data.Set as DS hiding (foldl, foldr)
import Data.Map.Strict as DM hiding (foldl, foldr)
import Data.List as DL (find)
import Data.Containers.ListUtils (nubOrd)

import Control.Monad.Except (Except, throwError, catchError, runExcept)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad(void)
import qualified Data.Bifunctor
import Data.Bifunctor (Bifunctor(first))

data VariableEnvironment = VEnv (Set String) (Map String IType)

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

type FunctionData = (LType, [LType])
type FunctionEnvironment = Map String FunctionData
type CompilerExcept = Except SemanticError
type StateStrMap x = State (Map String x)
type Compiler a = ReaderT a CompilerExcept

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
    result = Prelude.foldl (flip checkFunction) (return $ return DM.empty) topDef
  in
    evalState result DM.empty

lTypeToIType :: LType -> IType
lTypeToIType LInt = DynamicInt
lTypeToIType LBool = DynamicBool
lTypeToIType LString = DynamicString
lTypeToIType _ = undefined

evalStaticMul :: MulOp -> Integer -> Integer -> Integer
evalStaticMul (Times _) a b = a * b
evalStaticMul (Div _) a b = a `div` b
evalStaticMul (Mod _) a b = a `mod` b

mulToIMul :: MulOp -> IMulOp
mulToIMul (Times _) = ITimes
mulToIMul (Div _)  = IDiv
mulToIMul (Mod _) = IMod

addtoIAdd :: AddOp -> IAddOp
addtoIAdd (Plus _) = IPlus
addtoIAdd (Minus _) = IMinus

evalStaticAdd :: AddOp -> Integer -> Integer -> Integer
evalStaticAdd (Plus _) a b = a + b
evalStaticAdd (Minus _) a b = a - b

assertDivision :: MulOp -> IExpr -> Compiler FunTranslationEnvironment ()
assertDivision (Div pos) (ILitInt 0) = throwError PlaceHolder
assertDivision (Mod pos) (ILitInt 0) = throwError PlaceHolder
assertDivision _ _= return ()

f :: Expr -> Compiler FunTranslationEnvironment (IType, IExpr)

exprToInternal :: Expr -> Compiler FunTranslationEnvironment (IType, IExpr)
exprToInternal (ELitInt _ x) = return (StaticInt x, ILitInt x)
exprToInternal (ELitTrue _) = return (StaticBool True, ILitBool True)
exprToInternal (ELitFalse _) = return (StaticBool False, ILitBool False)
exprToInternal (EString _ str) = return (StaticString str, IString str)
exprToInternal expr@(Neg _ subexp) = do
  (etype, iexp) <- exprToInternal subexp
  if  not (etype `same` LInt)
    then throwError PlaceHolder
    else case etype of
           (StaticInt x) -> return (StaticInt (-x), ILitInt (-x))
           DynamicInt -> return (DynamicInt, INeg iexp)
           _ -> throwError PlaceHolder
exprToInternal (Not pos expr) = do
  (etype, iexp) <- exprToInternal expr
  unless (etype `same` LBool) $ throwError PlaceHolder
  return (etype, INot iexp)
exprToInternal (EMul pos e1 op e2) = do
  (type1, ie1) <- exprToInternal e1
  (type2, ie2) <- exprToInternal e2
  unless (type1 `same` LInt) $ throwError PlaceHolder
  unless (type2 `same` LInt) $ throwError PlaceHolder
  assertDivision op ie2
  if iTypeStatic type1 && iTypeStatic type2
    then
    let (StaticInt x) = type1
        (StaticInt y) = type2
        res = evalStaticMul op x y
        in
        return (StaticInt res, ILitInt res)
    else
    return (DynamicInt, IMul (mulToIMul op) ie1 ie2)

exprToInternal (EAdd pos e1 op e2) =
  let
    assertTypeCorrectness :: IType -> IType -> AddOp -> CompilerExcept ()
    assertTypeCorrectness t1 t2 (Minus pos) =
      unless (t1 `same` t2 && t1 `same` LInt) $ throwError PlaceHolder
    assertTypeCorrectness t1 t2 (Plus pos) =
      unless (t1 `same` t2 && (t1 `same` LInt || t1 `same` t2)) $ throwError PlaceHolder
    helper :: (IType, IExpr) -> (IType, IExpr) -> AddOp -> CompilerExcept (IType, IExpr)
    helper left right op = do
      assertTypeCorrectness (fst left) (fst right) op
      return (DynamicInt, IAdd (addtoIAdd op) (snd left) (snd right))
  in
    do
      result1 <- exprToInternal e1
      result2 <- exprToInternal e2
      lift $ helper result1 result2 op

exprToInternal (ERel pos e1 op e2) = undefined

exprToInternal (EAnd pos e1 e2) =
  let
      x :: (IType, IExpr) -> Expr -> Compiler FunTranslationEnvironment (IType, IExpr)
      x (StaticBool True, _) exp =
        do
          (itype, iExp) <- exprToInternal exp
          unless (itype `same` LBool) $ throwError PlaceHolder
          return (itype, iExp)
      x left@(DynamicBool, iLeft) exp =
        do
          (itype, iRight) <- exprToInternal exp
          case itype of
            (StaticBool False) -> return (StaticBool False, ILitBool False)
            (StaticBool True) -> return left
            DynamicBool -> return (DynamicBool, IAnd iLeft iRight)
            _ -> throwError PlaceHolder
      x left@(StaticBool False, _) _ = return left
      x _ _ = throwError PlaceHolder
  in
    exprToInternal e1 >>= flip x e2

exprToInternal (EOr pos e1 e2) = let
  x :: (IType, IExpr) -> Expr -> Compiler FunTranslationEnvironment (IType, IExpr)
  x (StaticBool False, _) exp =
    do
      (itype, iExp) <- exprToInternal exp
      unless (itype `same` LBool) $ throwError PlaceHolder
      return (itype, iExp)
  x left@(DynamicBool, iLeft) exp =
    do
      (itype, iRight) <- exprToInternal exp
      case itype of
        (StaticBool True) -> return (DynamicBool, IOr iLeft iRight) -- Tu jest miejsce na optymalizację
        (StaticBool False) -> return left
        DynamicBool -> return (DynamicBool, IOr iLeft iRight)
        _ -> throwError PlaceHolder
  x left@(StaticBool True, _) _ = return left
  x _ _ = throwError $ PlaceHolder
  in
    exprToInternal e1 >>= flip x e2


emptyBNFC'Pos :: BNFC'Position
emptyBNFC'Pos = Just (-1, -1)

defaultExpr :: LType -> Expr
defaultExpr LBool = ELitFalse emptyBNFC'Pos
defaultExpr LInt = ELitInt emptyBNFC'Pos 0
defaultExpr LString = EString emptyBNFC'Pos ""
defaultExpr _ = undefined

type ItemCompiler a = StateT a CompilerExcept

iTypeStatic :: IType -> Bool
iTypeStatic (StaticInt _) = True
iTypeStatic (StaticBool _) = True
iTypeStatic (StaticString _) = True
iTypeStatic _ = False


type FunContext = (LType, String, (Int, Int))
type FunTranslationEnvironment = (FunContext, VariableEnvironment)

itemToInternal :: LType -> Item -> ItemCompiler FunTranslationEnvironment IItem
itemToInternal varType item =
  do
    let id = getIdStr item
    ftEnv@(context@(ltype, funName, pos), VEnv set map) <- get
    if id `DS.member` set
      then throwError $ SemanticError pos (RedefinitionOfVariable (getPosition item) (getPosition item) id)
      else
      do
        let expr =case item of
              NoInit _ _ -> defaultExpr ltype
              Init _ _ ex -> ex
        (itype, iexpr) <- lift $ runReaderT (exprToInternal expr) ftEnv
        unless (varType `same` itype) (throwError PlaceHolder)
        put (context, VEnv (DS.insert id set) (DM.insert id itype map))
        return (IItem id iexpr)


itemsToInternals :: LType -> [Item] -> ItemCompiler FunTranslationEnvironment [IItem]
itemsToInternals _ [] = return []
itemsToInternals ltype (item:rest) =
  do
    head <- itemToInternal ltype item
    tail <- itemsToInternals ltype rest
    return $ head:tail


stmtToInternal (BStmt _ block) = do
  (iBlock, returned) <- (\(retType, VEnv set map) -> (retType,VEnv DS.empty map)) `local` blockToInternal block
  return (IBStmt iBlock, returned)

stmtsToInternal :: [Stmt] -> Compiler FunTranslationEnvironment ([IStmt], Bool)
stmtsToInternal [] = return ([], False)
stmtsToInternal ((BStmt _ block):rest) = do
  (iBlock, returned) <- (\(retType, VEnv set map) -> (retType,VEnv DS.empty map)) `local` blockToInternal block
  let iStmt = IBStmt iBlock
  if returned
    then return ([iStmt], True)
    else stmtsToInternal rest >>= (return . Data.Bifunctor.first (iStmt:))
stmtsToInternal ((Decl pos dtype items):rest) = do
  env@(context, vEnv) <- ask
  let ltype = convertType dtype
  (items, state) <- lift $ runStateT (itemsToInternals ltype items) env
  (istmts, ret) <- const state `local` stmtsToInternal rest
  return (IDecl items:istmts, ret)


blockToInternal :: Block -> Compiler FunTranslationEnvironment (IBlock, Bool)
blockToInternal block@(Block x stmts) =
  let
    fun :: [Stmt] -> Compiler FunTranslationEnvironment ([IStmt], Bool)
    fun [] = return ([], False)
    fun (x:xs) = stmtToInternal x >>=
      (\head -> fun xs >>=
        \rest -> return (Data.Bifunctor.bimap (fst head :) (snd head ||) rest))
  in
    fun stmts >>= \res -> return $ Data.Bifunctor.first IBlock res

topDefToInternal :: TopDef -> FunctionEnvironment -> CompilerExcept ()
topDefToInternal fDef fEnv =
  let
    funName = getIdStr fDef
    funArgs = [(getIdStr i, getArgLType i) | i <- topDefArgs fDef]
    retType = fst $ (LVoid, []) `fromMaybe` DM.lookup funName fEnv
    block = topDefBlock fDef
    vEnv :: VariableEnvironment
    vEnv = VEnv DS.empty DM.empty
    nvEnv = foldl (\(VEnv set map) (id, ltype) -> VEnv (DS.insert id set) (DM.insert id (lTypeToIType ltype) map)) vEnv funArgs
  in
    void $ runReaderT (blockToInternal block) ((retType, funName, getPosition fDef), nvEnv)

assertMain :: FunctionEnvironment -> CompilerExcept ()
assertMain fEnv =
  let
    main = DM.lookup "main" fEnv
    in
    case main of
      Just (LInt, _) -> return ()
      _ -> throwError $ SemanticError (0,0) NoMain

programToInternal :: Program -> CompilerExcept()
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
      foldl (fun fEnv) x topDefs

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


