{-# LANGUAGE MultiParamTypeClasses #-}
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


data FCUnaryOperator = Neg | BoolNeg
  deriving (Eq, Ord)

data FCType = Int | Bool | String | Void
  deriving (Eq, Ord)

data FCBinaryOperator = Add | Sub | Div | Mul | Mod | LShift | RShif | ByteAnd | ByteOr | ByteXor |
                     BoolAnd | BoolOr | BoolXor  | Test | Le | Equ | Neq | Lth | Gth | Ge
  deriving (Eq, Ord)

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
  showsPrec y (LitBool x) = showsPrec y x
  showsPrec y (LitInt x) = showsPrec y x
  showsPrec _ (Et et) = showString et

instance Convertable IDef.LType FCType where
  convert x = case x of
    IDef.LBool  -> Bool
    IDef.LInt  -> Int
    IDef.LString -> String
    IDef.LVoid  -> Void
    _ -> undefined


instance Convertable Tr.IAddOp FCBinaryOperator where
  convert x = case x of
    Tr.IPlus -> Add
    Tr.IMinus -> Sub

instance Convertable Tr.IMulOp FCBinaryOperator where
  convert x = case x of
    Tr.ITimes -> Mul
    Tr.IDiv -> Div
    Tr.IMod -> Mod

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

class ShowWithIndent a where
  showIndent :: a -> IndentMonad String
  showsIndent :: a -> String -> IndentMonad String
  showIndent = flip showsIndent ""

instance ShowWithIndent FCBlock where
  showIndent _ = indent "Unimplemented\n"
  showsIndent _ rest = indent ("Unimplemented\n" ++ rest)

instance ShowWithIndent FCFun where
  showsIndent (FCFun name rt args body) s = do
    (length, ident, current) <- ask
    sbody <- addIndentation $ showsIndent body ("}" ++ s)
    indent $ "declare " ++ show rt ++ " @" ++ name ++
      "(" ++ showArgs args ++ "){\n" ++ sbody
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
  
