{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module LLCompilerDefs (
  ExpToFCStateMonad(prependFCRValue,
                    getVariable,
                    lookupStringName,
                    isFunStatic),
  FCUnaryOperator(..),
  FCBinaryOperator(..),
  FCRegister(..),
  FCRValue(..),
  FCInstr(..),
  FCBlock,
  FCFun,
  RegType(..))
where

import Control.Monad.Except (Except, MonadError)

import CompilationError(SemanticError, SemanticError(CompilationError))
import Translator(CompilerExcept, Convertable(..))
import qualified Translator as Tr

data FCUnaryOperator = Neg | BoolNeg
  deriving (Eq, Ord)

data FCBinaryOperator = Add | Sub | Div | Mul | Mod | LShift | RShif | ByteAnd | ByteOr | ByteXor |
                     BoolAnd | BoolOr | BoolXor  | Test | Le | Equ | Neq | Lth | Gth | Ge
  deriving (Eq, Ord)

data FCRegister = VoidReg | Reg String | LitInt Int | LitBool Bool | Et String
  deriving (Eq, Ord)

data FCRValue = FunCall String [FCRegister] | FCBinOp FCBinaryOperator FCRegister FCRegister |
                FCUnOp FCUnaryOperator FCRegister | ConstValue FCRegister |
                GetPointer FCRegister FCRegister
  deriving (Eq, Ord)

type FCInstr = (FCRegister, FCRValue)

type FCBlock = (String, [FCInstr])

type FCFun = (String, [FCBlock])

data RegType = RNormal | RDynamic | RPhi | RVoid

class (MonadError SemanticError a) => ExpToFCStateMonad a where
  lookupStringName     :: String -> a String
  lookupNextNRegister  :: a FCRegister
  nextNRegiter         :: a FCRegister
  nextPRegisert        :: a FCRegister
  setRegister          :: FCRegister -> FCRValue -> a ()
  getRegister          :: FCRegister -> a FCRValue
  fCRValToReg          :: FCRValue -> a (Maybe FCRegister)
  prependFCRValue      :: RegType -> FCRValue -> a FCRegister
  getVariable          :: String -> a (Maybe FCRegister) -- Maybe is somehow redundant but it's a good practice to dobule check
  isFunStatic          :: String -> a Bool
  
instance Show FCRegister where
  showsPrec _ VoidReg = showString ""
  showsPrec _ (Reg str) = showString str
  showsPrec y (LitBool x) = showsPrec y x
  showsPrec y (LitInt x) = showsPrec y x


instance Convertable Tr.IAddOp FCBinaryOperator where
  convert x = case x of
    Tr.IPlus -> Add
    Tr.IMinus -> Sub

instance Convertable Tr.IMulOp FCBinaryOperator where
  convert x = case x of
    Tr.ITimes -> Mul
    Tr.IDiv -> Div
    Tr.IMod -> Mod
