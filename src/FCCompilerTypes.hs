{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
-- Zmienić Post na SimpleBlock
module FCCompilerTypes (
  FCUnaryOperator(..),
  FCBinaryOperator(..),
  FCClass(..),
  FCRegister(..),
  FCRValue(..),
  FCInstr(..),
  FCBlock'(..),
  FCBlock,
  FCSimpleBlock,
  FCFun(..),
  FCFun'(..),
  FCType(..),
  RegType(..),
  BlockType(..),
  FCProg(..),
  derefencePointerType,
  fCRValueType,
  jump,
  conditionalJump,
  universalPointer)
where

import Control.Monad.Except (Except, MonadError)
import Control.Monad.State.Strict (MonadState, StateT, State, get, put, modify, execState)
import Translator(CompilerExcept, Convertable(..))
import Control.Monad.Reader
import qualified Translator as Tr
import qualified Data.Map as DM
import qualified IDefinition as IDef
import qualified Data.Foldable

universalPointer :: FCType
universalPointer = FCPointer (Class "")

data FCControlFlowOp = Jmp

data FCUnaryOperator = Neg | BoolNeg
  deriving (Eq, Ord)


data FCType = Int | Bool | DynamicStringPtr | Void | ConstStringPtr Int | Class String | FCPointer FCType |
  UniversalPointer
  deriving (Eq, Ord, Show)

data FCBinaryOperator = Add | Sub | Div | Mul | Mod | LShift | RShif | ByteAnd | ByteOr | ByteXor |
                        BoolAnd | BoolOr | BoolXor | Le | Equ | Neq | Lth | Gth | Ge
  deriving (Eq, Ord)

data FCOperatorType = FArithmetic | FBoolean

binOpType :: FCBinaryOperator -> FCOperatorType
binOpType x = case x of
  Add -> FArithmetic
  Sub -> FArithmetic
  Div -> FArithmetic
  Mul -> FArithmetic
  Mod -> FArithmetic
  LShift -> FArithmetic
  RShif -> FArithmetic
  ByteAnd -> FBoolean
  ByteOr -> FBoolean
  ByteXor -> FBoolean
  BoolAnd -> FBoolean
  BoolOr -> FBoolean
  BoolXor -> FBoolean
  Le -> FBoolean
  Equ -> FBoolean
  Neq -> FBoolean
  Lth -> FBoolean
  Gth -> FBoolean
  Ge -> FBoolean

data FCRegister = VoidReg | Reg String | ConstString Int | LitInt Int
                | LitBool Bool | Et String | FCNull FCType
  deriving (Eq, Ord)

type PhiFrom = FCRegister
type PhiValue = FCRegister

data FCRValue = FunCall FCType String [(FCType, FCRegister)] |
                FCBinOp FCType FCBinaryOperator FCRegister FCRegister |
                FCUnOp FCType FCUnaryOperator FCRegister |
                FCPhi FCType [(PhiValue, PhiFrom)] |
                BitCast FCType FCType FCRegister |
                Return FCType (Maybe FCRegister) |
                FCEmptyExpr |
                FCFunArg FCType String Int |
                FCJump FCRegister |
                FCCondJump FCRegister FCRegister FCRegister |
                GetField FCType String FCType FCRegister |
                GetElementPtr FCType Int FCType FCRegister |
                GetElementPtrArr FCType Int FCType FCRegister |
                FCLoad FCType FCType FCRegister |
                FCStore FCType FCRegister FCType FCRegister |
                FCSizeOf FCType 
  deriving (Eq, Ord)

type FCInstr = (FCRegister, FCRValue)

type FCSimpleBlock = FCSimpleBlock' FCInstr
type FCSimpleBlock' a = [a]

type FCBlock = FCBlock' FCInstr ()

data FCBlock' a b =
  FCNamedSBlock {bname ::String, instrs :: FCSimpleBlock' a, addition::b}|
  FCComplexBlock {bname :: String, blocks :: [FCBlock' a b], addition::b} |
  FCCondBlock {
  bname     :: String,
  condEval  :: FCBlock' a b,
  jmpReg    :: FCRegister,
  success   :: FCBlock' a b,
  failure   :: FCBlock' a b,
  post      :: FCBlock' a b,
  addition  :: b
  } |
  FCPartialCond {
  bname :: String,
  condEval :: FCBlock' a b,
  jmpReg :: FCRegister,
  success :: FCBlock' a b,
  failure :: FCBlock' a b,
  addition  :: b
               } |
  FCWhileBlock {
  bname :: String,
  post :: FCBlock' a b,
  condEval :: FCBlock' a b,
  jmpReg :: FCRegister,
  success :: FCBlock' a b,
  epilogueLabel :: String,
  addition  :: b}


data FCFun' a b = FCFun'
  { name :: String,
    retType :: FCType,
    args :: [(FCType, FCRegister)],
    body :: FCBlock' a b
  }
type FCFun = FCFun' FCInstr ()

data FCClass = FCClass
  { className :: String,
    parentName :: Maybe String,
    inheritedFields :: [(String, FCType)],
    definedFields :: [(String, FCType)]
  }

data FCProg = FCProg [(String, (FCType, [FCType]))] [(FCRegister, String)] [FCFun] [FCClass]

data RegType = RNormal | RDynamic | RPhi | RVoid

data BlockType = FunBody | Normal | BoolExp | Cond | While | Check | Success | Failure | Post | BTPlacceHolder

instance Convertable IDef.LType FCType where
  convert x = case x of
    IDef.LBool            -> Bool
    IDef.LInt             -> Int
    IDef.LString          -> DynamicStringPtr
    IDef.LVoid            -> Void
    IDef.LFun{}           -> undefined
    IDef.LArray{}         -> undefined
    IDef.LClass name      -> FCPointer (Class name)
    IDef.LGenericClass {} -> undefined
instance Convertable Tr.IRelOp FCBinaryOperator where
  convert x = case x of
    Tr.ILTH -> Lth
    Tr.ILE -> Le
    Tr.IGTH -> Gth
    Tr.IGE -> Ge
    Tr.IEQU -> Equ
    Tr.INE -> Neq

instance Convertable Tr.IAddOp FCBinaryOperator where
  convert x = case x of
    Tr.IPlus -> Add
    Tr.IMinus -> Sub

instance Convertable Tr.IMulOp FCBinaryOperator where
  convert x = case x of
    Tr.ITimes -> Mul
    Tr.IDiv -> Div
    Tr.IMod -> Mod


jump :: String -> FCRValue
jump = FCJump . Et
conditionalJump :: FCRegister -> FCRegister -> FCRegister -> FCRValue
conditionalJump = FCCondJump
derefencePointerType :: FCType -> FCType
derefencePointerType = \case
  Int -> undefined
  Bool -> undefined
  DynamicStringPtr -> undefined
  Void -> undefined
  ConstStringPtr n -> undefined
  Class s -> undefined
  FCPointer ft -> ft
  UniversalPointer -> undefined

fCRValueType :: FCRValue -> FCType
fCRValueType x = case x of
  FunCall ft s frs -> ft
  FCBinOp ft fbo fr fr' -> case binOpType fbo of
    FArithmetic -> ft
    FBoolean -> Bool
  FCUnOp ft fuo fr -> ft
  Return ft m_fr -> ft
  FCEmptyExpr -> Void
  FCFunArg ft s n -> ft
  FCPhi ft _ -> ft
  FCJump _ -> Void
  FCCondJump{} -> Void
  BitCast ft ft' fr -> ft
  GetField ft s ft' fr -> ft
  FCLoad ft ft' fr -> ft
  FCStore ft fr ft' fr' -> Void
  FCSizeOf ft -> Int
  _ -> error "Internal"

