{-# LANGUAGE LambdaCase #-}
module LLVMCompiler where

import Prelude
import Data.List (foldl')
import FCCompilerTypes
import FCCompiler (bbaddInstr)
import Control.Monad.State (modify, State, MonadState(put, get), execState)
import Control.Monad.Reader (ReaderT, ask, asks, local, runReaderT)
import Control.Monad.State (unless)

type ExternalImport = (String, (FCType, [FCType]))
data LLVMInstr = FC_ FCInstr | LL String
data LLVMFunDecl = LLVMFunDecl String FCType [(FCType, FCRegister)] [LLVMInstr]
data LLVMModule = LLVMModule {externalImports::[ExternalImport],
                              constants::[(FCRegister, String)],
                              functions::[LLVMFunDecl]}
type LLVMBlockBuilder = [LLVMInstr]

dummyReturn :: FCType -> LLVMInstr
dummyReturn = \case
  Int -> FC_ (VoidReg, Return Int (Just (LitInt 0)))
  Bool -> FC_ (VoidReg, Return Bool (Just $ LitBool False))
  DynamicStringPtr -> FC_ (VoidReg, Return DynamicStringPtr $ Just (FCNull DynamicStringPtr))
  Void -> FC_ (VoidReg, Return Void Nothing)

changesFlow :: LLVMInstr->Bool
changesFlow x = case x of
  FC_ (fr, fv) -> case fv of
    Return {} -> True
    FCJump {} -> True
    FCCondJump {} -> True
    _ -> False
  LL s -> False

bbAddInstr :: LLVMBlockBuilder -> LLVMInstr -> LLVMBlockBuilder
bbAddInstr = flip (:)

toLLVMBuilder :: LLVMBlockBuilder -> FCBlock -> LLVMBlockBuilder
toLLVMBuilder up block = case block of
  FCNamedSBlock s x0 x1 -> foldl' bbAddInstr up' (map convert x0)
  FCComplexBlock s fbs x0 -> foldl' toLLVMBuilder up' fbs
  FCCondBlock s fc fr fs ff fp x0 -> let
    bbc = toLLVMBuilder up' fc
    bbfr = bbAddInstr bbc (FC_ (VoidReg, conditionalJump fr (Et (bname fs)) (Et (bname ff))))
    bbfs = toLLVMBuilder bbfr fs
    bbff = toLLVMBuilder bbfs ff
    in
    toLLVMBuilder bbff fp
  FCPartialCond s fc fr fs ff x0 -> let
    bbc = toLLVMBuilder up' fc
    bbfr = bbAddInstr bbc (FC_ (VoidReg, conditionalJump fr (Et (bname fs)) (Et (bname ff))))
    bbfs = toLLVMBuilder bbfr fs
    bbff = toLLVMBuilder bbfs ff
    in
    bbff
  FCWhileBlock s fp fc fr fs str x0 -> let
    bbw = bbAddInstr up' (FC_ (VoidReg, jump (bname fp)))
    bbfs = bbAddInstr (toLLVMBuilder bbw fs) (FC_ (VoidReg, jump (bname fp)))
    bbfp = toLLVMBuilder bbfs fp
    bbfc = toLLVMBuilder bbfp fc
    res = bbAddInstr bbfc (FC_ (VoidReg, conditionalJump fr (Et $ bname fs) (Et str)))
    in
    res
  where
    up' = if null (bname block) then up else bbAddInstr up (LL (bname block))
    convert :: FCInstr -> LLVMInstr
    convert = FC_



llvmBuildBuilder :: FCType -> LLVMBlockBuilder -> [LLVMInstr]
llvmBuildBuilder rettype bb = let
  bb' = bbAddInstr bb (dummyReturn rettype)
  in
    f bb' []
  where
    f :: LLVMBlockBuilder -> [LLVMInstr] -> [LLVMInstr]
    f bb rest = case bb of
      [] -> rest
      [l1] -> l1:rest
      (l1:l2:l3) ->
        case (l1, l2) of
          (LL s1, l2) -> flip f (l1:rest) $
                         if not (changesFlow l2)
                         then  FC_ (VoidReg, jump s1):l2:l3
                         else  l2:l3
          _ -> if changesFlow l1 && changesFlow l2
               then f (l2:l3) rest
               else f (l2:l3) (l1:rest)

class Outputable a where
  output :: a -> String

instance Outputable FCType where
  output Int = "i32"
  output Bool = "i1"
  output DynamicStringPtr = "i8*"
  output (ConstStringPtr x) = "[" ++ show x ++ " x i8 ]*"
  output Void = "void"

instance Outputable FCBinaryOperator where
  output x =
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

instance Outputable FCRegister where
  output VoidReg = ""
  output FCNull {} = "null"
  output (Reg str) = "%R" ++ str
  output (LitBool x) = show (if x then 1 else 0)
  output (LitInt x) = show x
  output (ConstString x) = "@S" ++ show x
  output (Et et) =  "%" ++ et

instance Outputable FCRValue where
  output (FCBinOp ftype fbop r1 r2) =
    output fbop ++ " " ++ output ftype ++ " " ++ output r1 ++ ", "
    ++ output r2
  output (Return ftype m_fcr) = "ret " ++ output ftype ++
    (case m_fcr of
      Just val -> " " ++ output val
      Nothing -> "")
  output (FCUnOp ftype fuop r1) = case fuop of
    Neg -> "sub " ++ output ftype ++ " 0, " ++ output r1
    BoolNeg -> error "Instancja Show dla FCRValue(BoolNeg) niezdefiniowana"
  output (BitCast ftf r ftt) = "bitcast " ++ output ftf ++ " " ++ output r ++ " to " ++ output ftt
  output (FCPhi _ []) = error "Malformed (empty) PHI"
  output (FCPhi x list) = "phi " ++ output x ++ " " ++
    foldr (\(rvalue, rfrom) rest ->
             outputPhiArg rvalue rfrom ++ (if null rest then "" else ", ")
             ++ rest)
    ""
    list
    where
      outputPhiArg :: FCRegister -> FCRegister -> String
      outputPhiArg rval rfrom = "[" ++ output rval ++", " ++ output rfrom ++ "]"
  output (FCJump register) = "br label " ++ output register
  output (FCCondJump c1 s f) = "br i1 " ++ output c1 ++ ", label "
    ++ output s ++ ", label " ++ output f
  output (FunCall rtype fname args) = "call " ++ outputFun fname rtype args
  output (GetPointer{}) = "Obecnie nie zdefiniowana"
  output _ = error "Instancja Output dla FCRValue niezdefiniowana"

instance Outputable LLVMInstr where
  output (LL s) = s ++ ":"
  output (FC_ (reg, rval)) = left ++ output rval
    where
      left = case reg of
        VoidReg -> ""
        reg -> output reg ++ " = "


outputFun :: String -> FCType -> [(FCType, FCRegister)] -> String
outputFun name rt args = output rt ++ " @" ++ name ++ "(" ++ outputArgs args ++ ")"
  where
    outputArgs :: [(FCType, FCRegister)] -> String
    outputArgs = foldr (\(ftype, freg) s ->
                        output ftype ++ " " ++ output freg ++ (if null s then "" else ", ") ++ s) ""

instance Outputable LLVMFunDecl where
  output (LLVMFunDecl name rt args body) =
    "define " ++ output rt ++ " @" ++ name ++ "(" ++ outputArgs args ++ ") {\n" ++
    concatMap (\x -> "  " ++ output x ++ "\n") body
    ++ "}"
    where
      outputArgs :: [(FCType, FCRegister)] -> String
      outputArgs = foldr (\(ftype, freg) s ->
                        output ftype ++ " " ++ output freg ++ (if null s then "" else ", ") ++ s) ""

instance Outputable LLVMModule where
  output (LLVMModule exts consts list) =
    concatMap (\(reg,str)-> outputConstant reg str ++ "\n") consts
    ++ (if null consts then "" else "\n") ++
    concatMap (\(name, (rtype, args))-> outputExternalFunction name rtype args ++ "\n") exts
    ++ (if null consts then "" else "\n") ++
    concatMap (\x -> output x ++ "\n\n") list
    where
    outputExternalFunction :: String -> FCType -> [FCType] -> String
    outputExternalFunction name rtype list =
      "declare " ++ output rtype ++ " @" ++ name ++ "(" ++ f list ++ ")"
        where
        f :: [FCType] -> String
        f = foldr (\ftype s ->
                        output ftype ++ (if null s then "" else ", ") ++ s) ""
    outputConstant :: FCRegister -> String -> String
    outputConstant freg@(ConstString x) str = output freg ++ " = internal constant "
      ++ "[" ++ show (1 + length str) ++ "x i8" ++ "] c" ++ "\"" ++ str' ++ "\""
      where
        str' = str ++ "\\00"
    outputConstant _ _ = undefined

compile :: FCProg -> String
compile (FCProg exts consts list) =
  output (LLVMModule exts consts (map f list))
  where
    f :: FCFun -> LLVMFunDecl
    f (FCFun' fname ftype args iblock) = LLVMFunDecl fname ftype args
      (llvmBuildBuilder ftype $ toLLVMBuilder [] iblock)

-- --     -- PRINT MONAD

-- type StringBuilder = State [String]
-- type IndentMonad = ReaderT AltIndentation StringBuilder ()
-- type AltIndentation = (String, String)

-- pmPutLine :: String -> IndentMonad
-- pmPutLine s = do
--   (_, cind) <- ask
--   hist <- get
--   put $ "\n":s:cind:hist
-- pmPutString :: String -> IndentMonad
-- pmPutString s = do
--   (_, cind) <- ask
--   hist <- get
--   put $ s:cind:hist
-- pmNewLine :: IndentMonad
-- pmNewLine = modify ("\n":)
-- withIndent :: IndentMonad -> IndentMonad
-- withIndent f = (\(indent, oldIndent) -> (indent, indent ++ oldIndent)) `local` f

-- buildIndentMonad :: String -> Int -> Int -> IndentMonad -> String
-- buildIndentMonad indentType len init monad =
--   let
--     indentFun n s = foldl (\rest _ -> s ++ rest) "" [1..n]
--     indent = indentFun len indentType
--     initIndent = indentFun init indent
--     list = execState (runReaderT monad (indent, initIndent)) []
--   in
--     concat (reverse list)

-- printIndentMonad :: String -> Int -> Int -> IndentMonad -> IO ()
-- printIndentMonad indentType len init monad =
--   let
--     indentFun n s = foldl (\rest _ -> s ++ rest) "" [1..n]
--     indent = indentFun len indentType
--     initIndent = indentFun init indent
--     list = execState (runReaderT monad (indent, initIndent)) []
--   in
--     mapM_ putStr (reverse list)


-- outputFCFun :: LLVMFunDecl -> IndentMonad
-- outputFCFun (LLVMFunDecl name rt args body) = do
--   pmPutLine $ "define " ++ show rt ++ " @" ++ name ++ "(" ++ showArgs args ++ ") {"
--   withIndent $ mapM_ (\x -> do
--                          pmPutLine $ output x
--                      ) body
--   pmPutLine "}"
--   where
--     showArgs :: [(FCType, FCRegister)] -> String
--     showArgs = foldr (\(ftype, freg) s ->
--                         show ftype ++ " " ++ show freg ++ (if null s then "" else ", ") ++ s) ""

-- outputLLVMModuleWithIndent :: LLVMModule -> IndentMonad
-- outputLLVMModuleWithIndent (LLVMModule exts consts list) = do
--   mapM_ (\(reg,str)-> pmPutLine $ outputConstant reg str) consts
--   unless (null consts) pmNewLine
--   mapM_ (\(name, (rtype, args))-> printExternalFunction name rtype args) exts
--   unless (null list) pmNewLine
--   mapM_ (\fun -> outputFCFun fun >> pmNewLine) list
--   pmNewLine
--   where
--     printExternalFunction :: String -> FCType -> [FCType] -> IndentMonad
--     printExternalFunction name rtype list = do
--       pmPutLine $ "declare " ++ output rtype ++ " @" ++ name ++ "(" ++ f list ++ ")"
--         where
--         f :: [FCType] -> String
--         f = foldr (\ftype s ->
--                         output ftype ++ (if null s then "" else ", ") ++ s) ""
--     outputConstant :: FCRegister -> String -> String 
--     outputConstant freg@(ConstString x) str = output freg ++ " = internal constant "
--       ++ "[" ++ show (1 + length str) ++ "x i8" ++ "] c" ++ "\"" ++ str' ++ "\""
--       where
--         str' = str ++ "\\00"
--     outputConstant _ _ = undefined
