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
  fCRValueType,
  jump,
  conditionalJump,
  showFCProg,
  buildIndentMonad,
  printIndentMonad)
where

import Control.Monad.Except (Except, MonadError)
import Control.Monad.State.Strict (MonadState, StateT, State, get, put, modify, execState)
import CompilationError(SemanticError, SemanticError(CompilationError))
import Translator(CompilerExcept, Convertable(..))
import Control.Monad.Reader
import qualified Translator as Tr
import qualified Data.Map as DM
import qualified IDefinition as IDef
import qualified Data.Foldable


data FCControlFlowOp = Jmp

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

type PhiFrom = FCRegister
type PhiValue = FCRegister

data FCRValue = FunCall FCType String [FCRegister] |
                FCBinOp FCType FCBinaryOperator FCRegister FCRegister |
                FCUnOp FCType FCUnaryOperator FCRegister |
                FCPhi FCType [(PhiValue, PhiFrom)] |
                ConstValue FCType FCRegister |
                GetPointer FCType FCRegister FCRegister |
                Return FCType (Maybe FCRegister) |
                FCEmptyExpr |
                FCFunArg FCType String Int |
                FCJump FCRegister |
                FCCondJump FCRegister FCRegister FCRegister
  deriving (Eq, Ord)

type FCInstr = (FCRegister, FCRValue)

type FCSimpleBlock = [FCInstr]

data FCBlock =
  FCNamedSBlock {bname ::String, instrs :: FCSimpleBlock}|
  FCComplexBlock {bname :: String, blocks :: [FCBlock]} |
  FCCondBlock {
  bname     :: String,
  condEval  :: FCBlock,
  jmpReg    :: FCRegister,
  success   :: FCBlock,
  failure   :: FCBlock,
  post      :: FCBlock
  } |
               FCPartialCond {
                 bname :: String,
                 condEval :: FCBlock,
                 jmpReg :: FCRegister,
                 success :: FCBlock,
                 failure :: FCBlock
               } |
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

data BlockType = FunBody | Normal | BoolExp | Cond | While | Check | Success | Failure | Post | BTPlacceHolder

instance Show FCRegister where
  showsPrec _ VoidReg = showString ""
  showsPrec _ (Reg str) = showString "%" . showString str
  showsPrec _ (DReg int) = showString "%" . shows int
  showsPrec y (LitBool x) = showsPrec y (if x then 1 else 0)
  showsPrec y (LitInt x) = showsPrec y x
  showsPrec _ (Et et) = showString "%" . showString et

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


jump :: String -> (FCRValue)
jump = FCJump . Et
conditionalJump :: FCRegister -> FCRegister -> FCRegister -> FCRValue
conditionalJump = FCCondJump

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

instance Show FCType where
  show Int = "i32"
  show Bool = "i1"
  show String = "i8*"
  show Void = "void"

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
  showsPrec _ (FCPhi _ []) s = error "Malformed (empty) PHI"
  showsPrec _ (FCPhi x list) s = "phi " ++ show x ++ " " ++
    foldr (\(rvalue, rfrom) rest -> showPhiArg rvalue rfrom ++
              if null rest then ""
               else ", ") "" list ++ s
    where
      showPhiArg :: FCRegister -> FCRegister -> String
      showPhiArg rval rfrom = "[" ++ show rval ++", " ++ show rfrom ++ "]"
  showsPrec _ _ s = error "Instancja Show dla FCRValue niezdefiniowana"

    -- PRINT MONAD

type StringBuilder = State [String]
type IndentMonad = ReaderT AltIndentation StringBuilder ()
type AltIndentation = (String, String)

pmPutLine :: String -> IndentMonad
pmPutLine s = do
  (_, cind) <- ask
  hist <- get
  put $ "\n":s:cind:hist
pmPutString :: String -> IndentMonad
pmPutString s = do
  (_, cind) <- ask
  hist <- get
  put $ s:cind:hist
pmNewLine :: IndentMonad
pmNewLine = modify ("\n":)
withIndent :: IndentMonad -> IndentMonad
withIndent f = (\(indent, oldIndent) -> (indent, indent ++ oldIndent)) `local` f

buildIndentMonad :: String -> Int -> Int -> IndentMonad -> String
buildIndentMonad indentType len init monad =
  let
    indentFun n s = foldl (\rest _ -> s ++ rest) "" [1..n]
    indent = indentFun len indentType
    initIndent = indentFun init indent
    list = execState (runReaderT monad (indent, initIndent)) []
  in
    concat (reverse list)

printIndentMonad :: String -> Int -> Int -> IndentMonad -> IO ()
printIndentMonad indentType len init monad =
  let
    indentFun n s = foldl (\rest _ -> s ++ rest) "" [1..n]
    indent = indentFun len indentType
    initIndent = indentFun init indent
    list = execState (runReaderT monad (indent, initIndent)) []
  in
    mapM_ putStr (reverse list)


printFCInstr :: FCInstr -> IndentMonad
printFCInstr (reg, instr) = do
  pmPutLine $ showedReg ++ show instr
  where
    showedReg = case reg of
      VoidReg -> ""
      reg -> show reg ++ " = "

showFCLabel :: String -> String
showFCLabel x = "label %" ++ x

printFCBlock :: FCBlock -> IndentMonad
printFCBlock (FCNamedSBlock name instr) = do
  unless (null name) (pmPutLine $ name ++ ":")
  mapM_ printFCInstr instr
printFCBlock (FCComplexBlock name blocks) = do
  unless (null name) (pmPutLine $ name ++ ":")
  mapM_ printFCBlock blocks
printFCBlock fcblock@FCCondBlock {} = do
  printFCBlock (condEval fcblock)
  pmPutLine $ "br i1 " ++ show (jmpReg fcblock) ++ ", " ++  showBlockLabel successBlock ++ ", "
    ++ showBlockLabel failureBlock
  printFCBlock successBlock
  printFCBlock failureBlock
  printFCBlock (post fcblock)
  where
    successBlock = success fcblock
    failureBlock = failure fcblock
    showBlockLabel = showFCLabel . bname
printFCBlock fcblock@FCPartialCond{} = do
  printFCBlock (condEval fcblock)
  pmPutLine $ "br i1 " ++ show (jmpReg fcblock) ++ ", " ++  showBlockLabel successBlock ++ ", "
    ++ showBlockLabel failureBlock
  printFCBlock successBlock
  printFCBlock failureBlock
    where
    successBlock = success fcblock
    failureBlock = failure fcblock
    showBlockLabel = showFCLabel . bname


printFCFun :: FCFun -> IndentMonad
printFCFun (FCFun name rt args body) = do
  pmPutLine $ "define " ++ show rt ++ " @" ++ name ++ "(" ++ showArgs args ++ ") {"
  withIndent $ printFCBlock body
  pmPutLine "}"
  where
    showArgs :: [(FCType, FCRegister)] -> String
    showArgs = foldr (\(ftype, freg) s ->
                        show ftype ++ " " ++ show freg ++ (if null s then "" else ", ") ++ s) ""


showFCProg :: FCProg -> IndentMonad
showFCProg (FCProg list) = do
  pmNewLine
  mapM_ (\fun -> printFCFun fun >> pmNewLine) list
