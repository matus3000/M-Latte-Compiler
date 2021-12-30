{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module FCCompilerTypes (
  FCUnaryOperator(..),
  FCBinaryOperator(..),
  FCRegister(..),
  FCRValue(..),
  FCInstr(..),
  FCBlock(..),
  FCFun(..),
  FCType(..),
  RegType(..),
  BlockType(..),
  FCProg(..),
  ShowWithIndent(..),
  fCRValueType,
  runIndentMonad)
where

import Control.Monad.Except (Except, MonadError)
import Control.Monad.State.Strict (MonadState)
import CompilationError(SemanticError, SemanticError(CompilationError))
import Translator(CompilerExcept, Convertable(..))
import Control.Monad.Reader
import qualified Translator as Tr
import qualified Data.Map as DM
import qualified IDefinition as IDef
import qualified Data.Foldable
import System.Posix (sleep)



data FCUnaryOperator = Neg | BoolNeg
  deriving (Eq, Ord)

data FCType = Int | Bool | String | Void
  deriving (Eq, Ord)

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
  
data FCRegister = VoidReg | Reg String | DReg Integer| LitInt Int | LitBool Bool | Et String
  deriving (Eq, Ord)

data FCRValue = FunCall FCType String [FCRegister] |
                FCBinOp FCType FCBinaryOperator FCRegister FCRegister |
                FCUnOp FCType FCUnaryOperator FCRegister |
                ConstValue FCType FCRegister |
                GetPointer FCType FCRegister FCRegister |
                Return FCType (Maybe FCRegister) |
                FCEmptyExpr |
                FCFunArg FCType String Int
  deriving (Eq, Ord)

type FCInstr = (FCRegister, FCRValue)

type FCSimpleBlock = [FCInstr]

data FCBlock = FCSimpleBlock String FCSimpleBlock |
               FCComplexBlock String [FCBlock] |
               FCCondBlock {
                 -- | 
                 condition  :: FCBlock,
                 -- | 
                 onSuccess  :: FCBlock,
                 -- |
                 postFactum :: FCBlock} |
               FCCondElseBlock {
                 -- | 
                 condition :: FCBlock,
                 -- | 
                 onSuccess :: FCBlock,
                 -- | 
                 onFail :: FCBlock,
                 -- |
                 postFactum::FCBlock} |
               FCWhileBlock {
                 -- | 
                 condition :: FCBlock,
                 -- | 
                 onSuccess :: FCBlock,
                 -- |
                 postFactum :: FCBlock
                 }

data FCFun = FCFun
  { name :: String,
    retType :: FCType,
    args :: [(FCType, FCRegister)],
    body :: FCBlock
  }

data FCProg = FCProg [FCFun]

data RegType = RNormal | RDynamic | RPhi | RVoid

data BlockType = FunBody | Normal | Cond | While | Check | Success | Failure | Post | BTPlacceHolder

instance Show FCRegister where
  showsPrec _ VoidReg = showString ""
  showsPrec _ (Reg str) = showString "%" . showString str
  showsPrec _ (DReg int) = showString "%" . shows int
  showsPrec y (LitBool x) = showsPrec y (if x then 1 else 0)
  showsPrec y (LitInt x) = showsPrec y x
  showsPrec _ (Et et) = showString et

instance Convertable IDef.LType FCType where
  convert x = case x of
    IDef.LBool  -> Bool
    IDef.LInt  -> Int
    IDef.LString -> String
    IDef.LVoid  -> Void
    _ -> undefined

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

fCRValueType :: FCRValue -> FCType
fCRValueType x = case x of
  FunCall ft s frs -> ft
  FCBinOp ft fbo fr fr' -> case binOpType fbo of
    FArithmetic -> ft
    FBoolean -> Bool
  FCUnOp ft fuo fr -> ft
  ConstValue ft fr -> ft
  GetPointer ft fr fr' -> ft
  Return ft m_fr -> ft
  FCEmptyExpr -> Void
  FCFunArg ft s n -> ft

--INDENTATION MONAD --

type IndentationType = String
type Indentation = (Int, IndentationType,String)
type IndentMonad = Reader Indentation

instance Show FCType where
  show Int = "i32"
  show Bool = "i1"
  show String = "i8*"
  show Void = "void"

runIndentMonad :: IndentMonad a -> Int -> IndentationType -> a
runIndentMonad a n s =
  runReader a (n, s, s')
  where
    s' = foldl (\rest _ -> s ++ rest) "" [1..n]

addIndentation :: IndentMonad a -> IndentMonad a
addIndentation = local (\(n, s, s') -> (n, s, _indentFun n s ++ s'))
    where
      _indentFun n s = foldl (\rest _ -> s ++ rest) "" [1..n]

indent :: String -> IndentMonad String
indent s = do
  (_, _, c') <- ask
  return $ c' ++ s

instance Show FCBinaryOperator where
  show x =
    case x of
      Add -> "add"
      Sub -> "sub"
      Mul -> "mul"
      Div -> "sdiv"
      Mod -> "srem"
      Lth -> "icmp slt"
      Le  -> "icmp sle"
      Equ -> "icmp eq"
      Neq -> "icmp ne"
      Gth -> "icmp sgt"
      Ge  -> "icmp sge"
      _ -> error "show FCBinOP undefined"


instance Show FCRValue where
  showsPrec _ (FCBinOp ftype fbop r1 r2) s =
    show fbop ++ " " ++ show ftype ++ " " ++ show r1 ++ ", "
    ++ show r2 ++ s
  showsPrec _ (Return ftype m_fcr) s = "ret " ++ show ftype ++
    (case m_fcr of
      Just val -> " " ++ show val
      Nothing -> "") ++ s
  showsPrec _ (FCUnOp ftype fuop r1) s = case fuop of
    Neg -> "sub " ++ show ftype ++ " 0, " ++ show r1 ++ s
    BoolNeg -> error "Instancja Show dla FCRValue(BoolNeg) niezdefiniowana"
    -- show fuop ++
  showsPrec _ _ s = error "Instancja Show dla FCRValue niezdefiniowana"

class ShowWithIndent a where
  showIndent :: a -> IndentMonad String
  showsIndent :: a -> String -> IndentMonad String
  showIndent = flip showsIndent ""

instance ShowWithIndent FCInstr where
  showsIndent (reg, rval@(Return _ _)) rest = indent (show rval ++ rest)
  showsIndent (reg, instr) rest = indent (show reg ++ " = " ++ show instr ++ rest)
  showIndent x = showsIndent x ""
  
instance ShowWithIndent FCBlock where
  showsIndent (FCSimpleBlock _ linstr) rest =
    Data.Foldable.foldrM (\instr s -> showsIndent instr ("\n" ++ s)) rest linstr
  showsIndent _ rest = error "Unimplemented instance of showWithIndent for FCBlock"

instance ShowWithIndent FCFun where
  showsIndent (FCFun name rt args body) s = do
    (length, ident, current) <- ask
    sbody <- addIndentation $ showsIndent body ("}" ++ s)
    indent $ "define " ++ show rt ++ " @" ++ name ++
      "(" ++ showArgs args ++ ") {\n" ++ sbody
      where
        showArgs :: [(FCType, FCRegister)] -> String
        showArgs = foldr (\(ftype, freg) s -> show ftype ++ " " ++ show freg ++ (if null s then "" else ", ") ++ s) ""
  showIndent = flip showsIndent ""

instance ShowWithIndent FCProg where
  showsIndent (FCProg list) s =
    do
      foldr (\a x -> do
                str <- x
                showsIndent a ("\n" ++ str)) (return s) list
  showIndent = flip showsIndent ""
  
