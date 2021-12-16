{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
module LLVMCompiler (FCBinaryOperator(..),
                     FCRegister(..),
                     FCRValue(..),
                     FCInstr(..),
                     compileToFC) where
import Prelude
import qualified Data.Map.Strict as DM
import Control.Monad.State.Strict
import Control.Monad.Except (Except, MonadError)

import CompilationError(SemanticError)
import Translator(CompilerExcept, Convertable)
import qualified Translator as Tr

data FCBinaryOperator = Add | Sub | Div | Mul | Mod | LShift | RShif | ByteAnd | ByteOr | ByteXor |
                     BoolAnd | BoolOr | BoolXor | BoolNeg | Test | CMP
  deriving (Eq, Ord)

data FCRegister = VoidReg | Reg String | LitInt Int | LitBool Bool | LitString String
  deriving (Eq, Ord)

data FCRValue = FunCall String [FCRegister] | FCBinOp FCBinaryOperator FCRegister FCRegister | FCRegister
  deriving (Eq, Ord)

type FCInstr = (FCRegister, FCRValue)

type FCBlock = (String, [FCInstr])

type FCFun = (String, [FCBlock])

data FCCompilationState =  FCCompilationState {nextRegisterNum :: Int}

type FCC = StateT FCCompilationState CompilerExcept

lookupVar :: String -> FCC FCRegister
lookupVar = undefined

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



compileExpr :: (ExpToFCStateMonad a) => Tr.IExpr -> Bool -> a FCRegister
compileExpr x save =
  let
    compileExprAddMull :: (ExpToFCStateMonad a) => Tr.IExpr -> Bool -> a FCRegister
    compileExprAddMull = undefined 
    in
    case x of
      Tr.IApp fun ies -> undefined
      Tr.IAdd iao ie ie' -> undefined
      Tr.IMul imo ie ie' -> undefined
    -- Tr.IAnd ie ie' -> undefined
      _ -> undefined
--   Tr.IString s -> _
--   Tr.INeg ie -> _
--   Tr.INot ie -> _
--   Tr.IOr ie ie' -> _
--   Tr.IRel iro ie ie' -> _
--   Tr.IVar s -> _
--   Tr.ILitInt n -> _
--   Tr.ILitBool b -> _    
  

compileInstrs :: [Tr.IStmt] -> CompilerExcept [FCBlock]
compileInstrs =
  let x = 0
  in
  undefined
compileBlock :: Tr.IBlock -> CompilerExcept [FCBlock]
compileBlock = undefined
compileFun :: Tr.IFun -> CompilerExcept ()
compileFun = undefined
compileToFC :: [Tr.IFun] -> CompilerExcept ()
compileToFC = undefined

instance Show FCRegister where
  showsPrec _ VoidReg = showString ""
  showsPrec _ (Reg str) = showString str
  showsPrec y (LitBool x) = showsPrec y x
  showsPrec y (LitInt x) = showsPrec y x
  showsPrec y (LitString x) = showString x

instance Convertable Tr.IAddOp FCBinaryOperator where
  convert x = case x of
    Tr.IPlus -> Add
    Tr.IMinus -> Sub

instance Convertable Tr.IMulOp FCBinaryOperator where
  convert x = case x of
    Tr.ITimes -> Mul
    Tr.IDiv -> Div
    Tr.IMod -> Mod

-- instance Convertable Tr.IRelOp FCBinaryOperator where
--   convert x = case x of
--     Tr.ILTH -> CMP
--     Tr.ILE -> CMP
--     Tr.IGTH -> CMP
--     Tr.IGE -> CMP
--     Tr.IEQU -> CMP
--     Tr.INE -> CMP

class (MonadError SemanticError a) => ExpToFCStateMonad a where
  lookupNextNRegister  :: a FCRegister
  nextNRegiter         :: a FCRegister
  nextPRegisert        :: a FCRegister
  setRegister          :: FCRegister -> FCRValue -> a ()
  getRegister          :: FCRegister -> a FCRValue
  fCRValToReg          :: FCRValue -> a (Maybe FCRegister)
  prependFCInstr       :: FCInstr -> a ()
  getVariable          :: String -> a (Maybe FCRegister) -- Maybe is somehow redundant but it's a good practice to dobule check
  isFunStatic             :: String -> a Bool


-- class (ExpToFCStateMonad a) => FCTranslationStateMonad a where
--   currentBlock
