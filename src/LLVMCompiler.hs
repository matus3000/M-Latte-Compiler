{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
module LLVMCompiler (FCBinaryOperator(..),
                     FCRegister(..),
                     FCRValue(..),
                     FCInstr(..),
                     compileToFC) where
import Prelude

import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as DM
import Control.Monad.State.Strict
import Control.Monad.Except (Except, MonadError)

import CompilationError(SemanticError, SemanticError(CompilationError))
import Translator(CompilerExcept, Convertable(..))
import LLCompilerDefs
import qualified Translator as Tr
import LLCompilerDefs (FCRValue(ConstValue, FCUnOp))
import qualified Data.Functor

data FCCompilationState =  FCCompilationState {nextRegisterNum :: Int}

type FCC = StateT FCCompilationState CompilerExcept

-- type NormaliziedFCRValue = FCRValue

-- data ExpressionMap = ExpressionMap {expToReg:: DM.Map NormaliziedFCRValue FCRegister,
--                                     regToExp:: DM.Map FCRegister NormaliziedFCRValue }

-- normalizeExpression :: FCRValue -> ExpressionMap -> NormaliziedFCRValue
-- normalizeExpression expr eMap = undefined

-- expressionMapEmplace :: ExpressionMap -> FCRegister -> FCRValue -> (ExpressionMap, FCRegister)
-- expressionMapEmplace eMap reg rvalue = let
--   expMap = expToReg eMap
--   rMap = regToExp eMap
--   normalizedRValue = normalizeExpression rvalue eMap
--   searchResult = DM.lookup normalizedRValue expMap
--   in
--   case searchResult of
--     Just fr -> (eMap, fr)
--     Nothing -> (ExpressionMap (DM.insert normalizedRValue reg expMap) (DM.insert reg normalizedRValue rMap), reg)

data FCBOType = Arithmetic | Boolean | Relation | Bitwise

binOpGetType :: FCBinaryOperator  -> FCBOType
binOpGetType x = case x of
  Add -> Arithmetic
  Sub -> Arithmetic
  Div -> Arithmetic
  Mul -> Arithmetic
  Mod -> Arithmetic
  LShift -> Arithmetic
  RShif -> Arithmetic
  ByteAnd -> Bitwise
  ByteOr -> Bitwise
  ByteXor -> Bitwise
  BoolAnd -> Boolean
  BoolOr -> Boolean
  BoolXor -> Boolean
  Test -> Boolean


translateExpr :: (ExpToFCStateMonad a) => Tr.IExpr -> Bool -> a FCRegister
translateExpr x save =
  let
    translateExprAddMull x save =
      let
        u :: (FCBinaryOperator, Tr.IExpr, Tr.IExpr)
        u@(op, ie1, ie2) = case x of
          Tr.IAdd iao ie1 ie2 -> (convert iao, ie1, ie2)
          Tr.IMul imo ie1 ie2 -> (convert imo, ie1, ie2)
          _ -> undefined
      in
        do
          r1 <- translateExpr ie2 True
          r2 <- translateExpr ie1 True
          prependFCRValue RNormal $ FCBinOp op r1 r2
  in
    case x of
      Tr.ILitInt n -> return $ (LitInt . fromInteger) n
      Tr.ILitBool b -> return $ LitBool b
      Tr.IString s -> do
        constEt <- lookupStringName s
        prependFCRValue RNormal $ GetPointer (Et constEt) (LitInt 0)
      Tr.IVar s -> getVariable s Data.Functor.<&> fromMaybe undefined
      addInstr@(Tr.IAdd iao ie ie') -> translateExprAddMull addInstr save
      mulInstr@(Tr.IMul imo ie ie') -> translateExprAddMull mulInstr save
      Tr.INeg ie -> do
        reg <- translateExpr ie True
        prependFCRValue RNormal $ FCUnOp Neg reg
      Tr.INot ie -> do
        reg <- translateExpr ie True
        prependFCRValue RNormal $ FCUnOp BoolNeg reg
      Tr.IAnd ie ie' -> do
        r2 <- translateExpr ie' True
        r1 <- translateExpr ie True
        prependFCRValue RNormal $ FCBinOp BoolAnd  r1 r2
      Tr.IOr ie ie' -> do
        r2 <- translateExpr ie' True
        r1 <- translateExpr ie True
        prependFCRValue RNormal $ FCBinOp BoolAnd  r1 r2
      Tr.IApp fun ies -> let
        r ::(ExpToFCStateMonad a) =>  Bool -> Bool -> a FCRegister
        r returnValues staticFun = if staticFun && not returnValues then return VoidReg else
          do
            args <- mapM (`translateExpr` True) (reverse ies)
            prependFCRValue (if staticFun then RNormal else (if returnValues then RDynamic else RVoid))  $
              FunCall fun args
        in
        isFunStatic fun >>= r True
      Tr.IRel iro ie ie' -> do
        r2 <- translateExpr ie' True
        r1 <- translateExpr ie True
        prependFCRValue RNormal $ FCBinOp (convert iro) r1 r2

translateIItem :: (InstrToFCStateMonad a) => Tr.IItem -> a ()
translateIItem (Tr.IItem s expr) = void $
  do
    mreg <- getVariable s
    case mreg of
      Just reg -> setVariable s reg
      Nothing -> undefined

translateInstr :: (InstrToFCStateMonad a) => Tr.IStmt -> a ()
translateInstr stmt = case stmt of
  Tr.IBStmt ib -> translateBlock ib
  Tr.IDecl iis -> void $ do
    iis <- mapM translateIItem (reverse iis)
    return  ()
  Tr.IAss s ie -> void $ do
    mreg <- getVariable s
    case mreg of
      Just reg -> setVariable s reg
      Nothing -> undefined
  Tr.IIncr s -> translateInstr (Tr.IAss s (Tr.IAdd Tr.IPlus (Tr.IVar s) (Tr.ILitInt 1)))
  Tr.IDecr s -> translateInstr (Tr.IAss s (Tr.IAdd Tr.IMinus (Tr.IVar s) (Tr.ILitInt 1)))
  Tr.IRet ie -> void $ do
    r <- translateExpr ie True
    prependFCRValue RVoid $ Return (Just r)
  Tr.IVRet -> void $ prependFCRValue RVoid (Return Nothing)
  Tr.ICond ie is -> undefined
  Tr.ICondElse ie is is' -> undefined
  Tr.IWhile ie is -> undefined
  Tr.ISExp ie -> void $ translateExpr ie False
  Tr.IStmtEmpty -> return ()

translateBlock :: (InstrToFCStateMonad a) => Tr.IBlock -> a ()
translateBlock = undefined

compileBlock :: Tr.IBlock -> CompilerExcept [FCBlock]
compileBlock = undefined
compileFun :: Tr.IFun -> CompilerExcept ()
compileFun = undefined
compileToFC :: [Tr.IFun] -> CompilerExcept ()
compileToFC = undefined


instance Convertable Tr.IRelOp FCBinaryOperator where
  convert x = case x of
    Tr.ILTH -> Lth
    Tr.ILE -> Le
    Tr.IGTH -> Gth
    Tr.IGE -> Ge
    Tr.IEQU -> Equ
    Tr.INE -> Neq

-- class (ExpToFCStateMonad a) => FCTranslationStateMonad a where
--   currentBlock
