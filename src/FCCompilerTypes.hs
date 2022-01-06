{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
-- Zmienić Post na SimpleBlock
module FCCompilerTypes (
  FCUnaryOperator(..),
  FCBinaryOperator(..),
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

data FCType = Int | Bool | DynamicStringPtr | Void | ConstStringPtr Int
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

data FCRegister = VoidReg | Reg String | ConstString Int | LitInt Int | LitBool Bool | Et String
  deriving (Eq, Ord)

type PhiFrom = FCRegister
type PhiValue = FCRegister

data FCRValue = FunCall FCType String [(FCType, FCRegister)] |
                FCBinOp FCType FCBinaryOperator FCRegister FCRegister |
                FCUnOp FCType FCUnaryOperator FCRegister |
                FCPhi FCType [(PhiValue, PhiFrom)] |
                BitCast FCType FCRegister FCType |
                GetPointer FCType FCRegister FCRegister |
                Return FCType (Maybe FCRegister) |
                FCEmptyExpr |
                FCFunArg FCType String Int |
                FCJump FCRegister |
                FCCondJump FCRegister FCRegister FCRegister
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

data FCProg = FCProg [(String, (FCType, [FCType]))] [(FCRegister, String)] [FCFun]

data RegType = RNormal | RDynamic | RPhi | RVoid

data BlockType = FunBody | Normal | BoolExp | Cond | While | Check | Success | Failure | Post | BTPlacceHolder

instance Show FCRegister where
  showsPrec _ VoidReg = showString ""
  showsPrec _ (Reg str) = showString "%R" . showString str
  showsPrec y (LitBool x) = showsPrec y (if x then 1 else 0)
  showsPrec y (LitInt x) = showsPrec y x
  showsPrec y (ConstString x) = showString "@S" . showsPrec y x
  showsPrec _ (Et et) = showString "%" . showString et

instance Convertable IDef.LType FCType where
  convert x = case x of
    IDef.LBool  -> Bool
    IDef.LInt  -> Int
    IDef.LString -> DynamicStringPtr
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
  BitCast ftfrom _ ftto -> ftto
  GetPointer ft fr fr' -> ft
  Return ft m_fr -> ft
  FCEmptyExpr -> Void
  FCFunArg ft s n -> ft
  FCPhi ft _ -> ft
  FCJump _ -> Void
  FCCondJump{} -> Void
--INDENTATION MONAD --

instance Show FCType where
  show Int = "i32"
  show Bool = "i1"
  show DynamicStringPtr = "i8*"
  show (ConstStringPtr x) = "[" ++ show x ++ " x i8 ]*"
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


showFun :: String -> FCType -> [(FCType, FCRegister)] -> String
showFun name rt args = show rt ++ " @" ++ name ++ "(" ++ showArgs args ++ ")"
  where
    showArgs :: [(FCType, FCRegister)] -> String
    showArgs = foldr (\(ftype, freg) s ->
                        show ftype ++ " " ++ show freg ++ (if null s then "" else ", ") ++ s) ""
            
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
  showsPrec _ (BitCast ftf r ftt) s = "bitcast " ++ show ftf ++ " " ++ show r ++ " to " ++ show ftt ++ s
  showsPrec _ (FCPhi _ []) s = error "Malformed (empty) PHI"
  showsPrec _ (FCPhi x list) s = "phi " ++ show x ++ " " ++
    foldr (\(rvalue, rfrom) rest ->
             showPhiArg rvalue rfrom ++ (if null rest then "" else ", ")
             ++ rest)
    ""
    list
    ++ s
    where
      showPhiArg :: FCRegister -> FCRegister -> String
      showPhiArg rval rfrom = "[" ++ show rval ++", " ++ show rfrom ++ "]"
  showsPrec _ (FCJump register) s = "br label " ++ show register ++ s
  showsPrec _ (FCCondJump c1 s f) str = "br i8 " ++ show c1 ++ ", label "
    ++ show s ++ ", label " ++ show f ++ str
  showsPrec _ (FunCall rtype fname args) str = "call " ++ showFun fname rtype args ++ str
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

printFCBlockName :: FCBlock -> IndentMonad
printFCBlockName fcblock = do
  unless (null (bname fcblock)) (pmPutLine $ bname fcblock ++ ":")
printFCBlock :: FCBlock -> IndentMonad
printFCBlock fcblock@(FCNamedSBlock name instr _) = do
  printFCBlockName fcblock
  mapM_ printFCInstr instr
printFCBlock fcblock@(FCComplexBlock name blocks _) = do
  printFCBlockName fcblock
  mapM_ printFCBlock blocks
printFCBlock fcblock@FCCondBlock {} = do
  printFCBlockName fcblock
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
  printFCBlockName fcblock
  printFCBlock (condEval fcblock)
  pmPutLine $ "br i1 " ++ show (jmpReg fcblock) ++ ", " ++  showBlockLabel successBlock ++ ", "
    ++ showBlockLabel failureBlock
  printFCBlock successBlock
  printFCBlock failureBlock
    where
    successBlock = success fcblock
    failureBlock = failure fcblock
    showBlockLabel = showFCLabel . bname
printFCBlock fcblock@FCWhileBlock{} = do
  printFCBlockName fcblock
  printFCInstr (VoidReg, jump (bname $ post fcblock))
  printFCBlock successBlock
  printFCBlock (post fcblock)
  printFCBlock (condEval fcblock)
  pmPutLine $ "br i1 " ++ show (jmpReg fcblock) ++ ", " ++ showBlockLabel successBlock ++ ", " ++ "%" ++(epilogueLabel fcblock)
  where
    successBlock = succeess fcblock
    showBlockLabel = showFCLabel . bname


printFCFun :: FCFun -> IndentMonad
printFCFun (FCFun' name rt args body) = do
  pmPutLine $ "define " ++ show rt ++ " @" ++ name ++ "(" ++ showArgs args ++ ") {"
  withIndent $ printFCBlock body
  pmPutLine "}"
  where
    showArgs :: [(FCType, FCRegister)] -> String
    showArgs = foldr (\(ftype, freg) s ->
                        show ftype ++ " " ++ show freg ++ (if null s then "" else ", ") ++ s) ""

showFCProg :: FCProg -> IndentMonad
showFCProg (FCProg exts consts list) = do
  mapM_ (\(reg,str)-> pmPutLine $ showConstant reg str) consts
  unless (null consts) pmNewLine
  mapM_ (\(name, (rtype, args))-> printExternalFunction name rtype args) exts
  unless (null list) pmNewLine
  mapM_ (\fun -> printFCFun fun >> pmNewLine) list
  pmNewLine
  where
    printExternalFunction :: String -> FCType -> [FCType] -> IndentMonad
    printExternalFunction name rtype list = do
      pmPutLine $ "declare " ++ show rtype ++ " @" ++ name ++ "(" ++ f list ++ ")"
        where
        f :: [FCType] -> String
        f = foldr (\ftype s ->
                        show ftype ++ (if null s then "" else ", ") ++ s) ""
    showConstant :: FCRegister -> String -> String 
    showConstant freg@(ConstString x) str = show freg ++ " = internal constant "
      ++ "[" ++ show (1 + length str) ++ "x i8" ++ "] c" ++ "\"" ++ str' ++ "\""
      where
        str' = str ++ "\\00"
    showConstant _ _ = undefined
