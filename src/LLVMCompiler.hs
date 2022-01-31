{-# LANGUAGE LambdaCase #-}
module LLVMCompiler where

import Prelude
import Data.List (foldl')
import qualified Data.Map as DM
import FCCompilerTypes
import FCCompiler (bbaddInstr)
import Control.Monad.State.Strict (modify, State, MonadState(put, get), execState)
import Control.Monad.Reader (ReaderT, ask, asks, local, runReaderT)
import Control.Monad.State (unless)

import Data.List as DL
import Numeric(showHex)
import qualified Control.Arrow as BiFunctor
import Data.Maybe (fromMaybe, isNothing, fromJust)
import Data.Char (ord)

import LLVMCompiler.FunctionTable (FunctionTable, MethodInfo(..))
import qualified LLVMCompiler.FunctionTable as FT
import LLVMCompiler.Outputable
import qualified Data.Bifunctor as BiFunctor

type ExternalImport = (String, (FCType, [FCType]))
data LLVMInstr = FC_ FCInstr | LL String | LLInstr (FCRegister, LLVMInternalInstr)

data LLVMInternalInstr = PtrToInt FCType FCRegister

data LLVMFunDecl = LLVMFunDecl String FCType [(FCType, FCRegister)] [LLVMInstr]

data LLVMClassDecl = LLVMClassDecl {llClassName :: String,
                                    llFieldsMap :: DM.Map String Int,
                                    llFields :: [FCType],
                                    llNextId :: Int,
                                    llFunctionTable :: Maybe FunctionTable}

data LLVMModule = LLVMModule {externalImports::[ExternalImport],
                              constants::[(FCRegister, String)],
                              functions::[LLVMFunDecl],
                              classes :: [LLVMClassDecl],
                              vtables :: [FunctionTable]}
type LLVMBlockBuilder = [LLVMInstr]

dummyReturn :: FCType -> LLVMInstr
dummyReturn = \case
  Int -> FC_ (VoidReg, Return Int (Just (LitInt 0)))
  Bool -> FC_ (VoidReg, Return Bool (Just $ LitBool False))
  DynamicStringPtr -> FC_ (VoidReg, Return DynamicStringPtr $ Just (FCNull DynamicStringPtr))
  Void -> FC_ (VoidReg, Return Void Nothing)
  fctype -> FC_ (VoidReg, Return fctype (Just $ FCNull fctype))

changesFlow :: LLVMInstr->Bool
changesFlow x = case x of
  FC_ (fr, fv) -> case fv of
    Return {} -> True
    FCJump {} -> True
    FCCondJump {} -> True
    _ -> False
  LL s -> False
  LLInstr (fr, fv) -> case fv of
     PtrToInt ft fr' -> False

type LLVMClassEnv = DM.Map String LLVMClassDecl
type LLVMEnv = LLVMClassEnv

llEnvFieldMapping :: String -> String -> LLVMEnv -> Int
llEnvFieldMapping className fieldName env = let
  sEnv = env
  classData = error ("Class " ++ className ++ " not found") `fromMaybe` DM.lookup className sEnv
  fieldIndex = error ("No mapping of field " ++ fieldName ++ "for class " ++ className)
               `fromMaybe`
               DM.lookup fieldName (llFieldsMap classData)
  in
  fieldIndex

llEnvMethodMapping :: String -> String -> LLVMEnv -> Int
llEnvMethodMapping = undefined

vtablename = "_vtable"

toLLVMStructs :: [FCClass] -> (LLVMClassEnv, [LLVMClassDecl],  [FunctionTable])
toLLVMStructs fcclasses = (\(res, vtables) -> (DM.fromList (map (\x -> (llClassName x, x)) res), res, vtables))
  $ BiFunctor.bimap reverse reverse (foldl f ([],[]) fcclasses)
  where
    defineFields ::  [(String, FCType)]->LLVMClassDecl -> LLVMClassDecl
    defineFields fields lcd = let
      (_llFieldsMap, _llFields, _llNextId) = (\(x,y,z) -> (x, llFields lcd ++ reverse y,z)) $ foldl
        (\(map,res,id) (fname, ftype)->
            (DM.insert fname id map, ftype:res, id+1))
        (llFieldsMap lcd, [], llNextId lcd)
        fields
      in
        LLVMClassDecl (llClassName lcd) _llFieldsMap _llFields _llNextId (llFunctionTable lcd)
    defineMethods :: [FCFun] -> LLVMClassDecl -> LLVMClassDecl
    defineMethods methods lcd = let
      f :: FunctionTable -> FCFun -> FunctionTable
      f vtable fcfun = let fun = case FT.lookupMethod (name fcfun) vtable of
                             Nothing -> FT.declareMethod (name fcfun) (FunType (retType fcfun)
                                                                        ((map fst . args) fcfun))
                             Just n -> FT.overrideMethod (name fcfun)
                       in
                         fun vtable
      vtable' = case llFunctionTable lcd of
        Just vtable -> Just $ foldl f vtable methods
        Nothing -> Nothing
      in
      LLVMClassDecl (llClassName lcd) (llFieldsMap lcd) (llFields lcd) (llNextId lcd) vtable'
    overrideTypeOfVirtualTable :: String -> [FCType] -> [FCType]
    overrideTypeOfVirtualTable name list = map (\ y -> case y of
                                                    FCPointer (FCMethodsTable s)->FCPointer (FCMethodsTable name)
                                                    FCMethodsTable s -> FCMethodsTable name
                                                    _-> y) list
    f :: ([LLVMClassDecl], [FunctionTable]) -> FCClass
      -> ([LLVMClassDecl], [FunctionTable])
    f (res, vtables) fcclass = let
      name = className fcclass
      superclass = parentName fcclass
      parent = case superclass of
        Just name -> Just $ error "Something is wrong here" `fromMaybe` DL.find ((name ==) . llClassName) res
        _ -> Nothing
      seed@(inheritedMap, inheritedFields, inheritedIndex, inheritedTable) = case parent of
        Nothing -> (DM.empty, [], 0, Nothing)
        Just lcd -> (llFieldsMap lcd, llFields lcd, llNextId lcd, llFunctionTable lcd)
      -- fieldMapper :: (DM.Map String Int, [FCType], Int) ->
      (table, declared, redefined)
        | (null $ implementedMethods fcclass) = (inheritedTable, False, False)
        | isNothing inheritedTable = (Just $ FT.new name, True, False)
        | otherwise = (Just $ FT.newInherited name (fromJust inheritedTable), False, True)
      fields = (if declared then ((vtablename, FCPointer $ FT.getType (fromJust table)):) else id)
        (definedFields  fcclass)
      inheritedFields'
        | redefined = overrideTypeOfVirtualTable name inheritedFields
        | otherwise = inheritedFields
      resultLCD = defineMethods (implementedMethods fcclass) $ defineFields fields $
        LLVMClassDecl name inheritedMap inheritedFields' inheritedIndex table
      in
      (resultLCD : res, if declared || redefined then fromJust (llFunctionTable resultLCD):vtables
                        else vtables)

bbAddInstr :: LLVMEnv -> LLVMBlockBuilder -> LLVMInstr -> LLVMBlockBuilder
bbAddInstr env bb linstr = case linstr of
  FC_ inst@(reg, fcinstr) -> case fcinstr of
    GetMethod _ methodName ft fr -> let
      className = case ft of
        FCPointer (FCMethodsTable s) -> s
        _ -> error $ show ft
      ftres = fCRValueType fcinstr
      index = llEnvMethodMapping className methodName env
      in
      FC_ (reg, GetElementPtr ftres index ft fr) : bb
    GetMethodTable className ft fr ->
       let ftres = fCRValueType fcinstr
           index = llEnvFieldMapping className vtablename env
       in
         FC_ (reg, GetElementPtr ftres index ft fr) : bb
    GetField ft s ft' fr ->
      let
        className = case ft' of
          FCPointer (Class className) -> className
          _ -> error "Malformed"
        index = llEnvFieldMapping className s env
      in
        FC_ (reg, GetElementPtr ft index ft' fr):bb
    FCSizeOf fctype ->
      let
        _reg = Reg $ case reg of
          Reg s -> "_" ++ s
          _ -> undefined
        sizeofTrick = FC_ (_reg, GetElementPtrArr (FCPointer fctype) 1 (FCPointer fctype) (FCNull fctype))
        bb' = sizeofTrick : bb
        bb'' = LLInstr (reg, PtrToInt (FCPointer fctype) _reg) : bb'
        in
        bb''
    _ -> linstr : bb
  LL s -> linstr : bb
  LLInstr {} -> linstr : bb

toLLVMBuilder :: LLVMEnv -> LLVMBlockBuilder -> FCBlock -> LLVMBlockBuilder
toLLVMBuilder env up block = case block of
  FCNamedSBlock s x0 x1 -> foldl' bbAddInstr' up' (map convert x0)
  FCComplexBlock s fbs x0 -> foldl' toLLVMBuilder' up' fbs
  FCCondBlock s fc fr fs ff fp x0 -> let
    bbc = toLLVMBuilder' up' fc
    bbfr = bbAddInstr' bbc (FC_ (VoidReg, conditionalJump fr (Et (bname fs)) (Et (bname ff))))
    bbfs = toLLVMBuilder' bbfr fs
    bbff = toLLVMBuilder' bbfs ff
    in
    toLLVMBuilder' bbff fp
  FCPartialCond s fc fr fs ff x0 -> let
    bbc = toLLVMBuilder' up' fc
    bbfr = bbAddInstr' bbc (FC_ (VoidReg, conditionalJump fr (Et (bname fs)) (Et (bname ff))))
    bbfs = toLLVMBuilder' bbfr fs
    bbff = toLLVMBuilder' bbfs ff
    in
    bbff
  FCWhileBlock s fp fc fr fs str x0 -> let
    bbw = bbAddInstr' up' (FC_ (VoidReg, jump (bname fp)))
    bbfs = bbAddInstr' (toLLVMBuilder' bbw fs) (FC_ (VoidReg, jump (bname fp)))
    bbfp = toLLVMBuilder' bbfs fp
    bbfc = toLLVMBuilder' bbfp fc
    res = bbAddInstr' bbfc (FC_ (VoidReg, conditionalJump fr (Et $ bname fs) (Et str)))
    in
    res
  where
    up' = if null (bname block) then up else bbAddInstr' up (LL (bname block))
    convert :: FCInstr -> LLVMInstr
    convert = FC_
    bbAddInstr' = bbAddInstr env
    toLLVMBuilder' = toLLVMBuilder env



llvmBuildBuilder :: LLVMEnv -> FCType -> LLVMBlockBuilder -> [LLVMInstr]
llvmBuildBuilder env rettype bb = let
  bb' = bbAddInstr env bb (dummyReturn rettype)
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
  output (BitCast ftf ftt r) = "bitcast " ++ output ftt ++ " " ++ output r ++ " to " ++ output ftf
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
  output (FunCallDynamic rt reg args) = "call " ++ output rt ++ " " ++ output reg
    ++ "("++ intercalate ", " (map (\(x, y) -> output x ++" "++ output y) args) ++ ")" 
  output GetField {} = error "This one is internal."
  output (GetElementPtr ft x fc r) = "getelementptr " ++ output (derefencePointerType fc) ++ ", "
    ++ output fc ++ " " ++ output r ++ ", i32 0, i32 " ++ show x
  output (GetElementPtrArr ft x ft' reg) = "getelementptr " ++ output (derefencePointerType ft) ++ ", "
    ++ output ft' ++ " " ++ output reg ++ ", i32 " ++ show x
  output (FCLoad ft ft' r) = "load " ++ output ft ++ ", " ++ output ft' ++ " " ++output r
  output (FCStore ft value ftp ptr) = "store " ++ output ft ++ " " ++ output value ++ ","
    ++ output ftp ++ " " ++ output ptr
  output (FCSizeOf f) = error "This one is a macro"
  output FCEmptyExpr = ""

  -- output _ = error "Instancja Output dla FCRValue niezdefiniowana"

instance Outputable LLVMInternalInstr where
  output x = case x of
     PtrToInt ft fr -> "ptrtoint " ++ output ft ++ " " ++ output fr ++" to i32"

instance Outputable LLVMInstr where
  output (LL s) = s ++ ":"
  output (FC_ (reg, rval)) = left ++ output rval
    where
      left = case reg of
        VoidReg -> ""
        reg -> output reg ++ " = "
  output (LLInstr (reg, rval)) = left ++ output rval
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

instance Outputable LLVMClassDecl where
  output (LLVMClassDecl _className _ _llFields _ _) =
    "%" ++ _className ++ " = type {" ++ outputFields _llFields ++ "}"
    where
      outputFields :: [FCType] -> String
      outputFields [] = ""
      outputFields (x:xs) = output x ++ (if null xs then "" else "," ++ outputFields xs)

instance Outputable LLVMModule where
  output (LLVMModule exts consts funs classes vtables) =
    concatMap (\(reg,str)-> outputConstant reg str ++ "\n") consts
    ++ (if null consts then "" else "\n") ++
    concatMap (\(name, (rtype, args))-> outputExternalFunction name rtype args ++ "\n") exts
    ++ (if null consts then "" else "\n") ++
    concatMap (\x -> output x ++ "\n\n") vtables ++
    concatMap (\x -> output x ++ "\n\n") classes ++
    concatMap (\x -> output x ++ "\n\n") funs
    where
    outputExternalFunction :: String -> FCType -> [FCType] -> String
    outputExternalFunction name rtype funs =
      "declare " ++ output rtype ++ " @" ++ name ++ "(" ++ f funs ++ ")"
        where
        f :: [FCType] -> String
        f = foldr (\ftype s ->
                        output ftype ++ (if null s then "" else ", ") ++ s) ""
    outputConstant :: FCRegister -> String -> String
    outputConstant freg@(ConstString x) str = output freg ++ " = internal constant "
      ++ "[" ++ show (1 + length str) ++ "x i8" ++ "] c" ++ "\"" ++ str' ++ "\""
      where
        escapecharacter :: Char -> [Char]
        escapecharacter c
          | ord c < 15 = "\\0" ++ showHex (ord c) ""
          | ord c < 31 = "\\" ++ showHex (ord c) ""
          | c == '\'' || c =='\"' = "\\" ++ showHex (ord c) ""
          | ord c == 127 = "\\"  ++ showHex (ord c) ""
          | otherwise  = [c]
        escapestring :: String -> [Char]
        escapestring s = foldr (\c res -> escapecharacter c ++ res) "" s
        str' = escapestring str ++ "\\00"
    outputConstant _ _ = undefined

compile :: FCProg -> String
compile (FCProg exts consts funs classes) =
  output (LLVMModule exts consts (map f
                                  funs) llvmClasses llvmVTables)
  where
    (llvmStructEnv, llvmClasses, llvmVTables) = toLLVMStructs classes
    llvmEnv = llvmStructEnv
    f :: FCFun -> LLVMFunDecl
    f (FCFun' fname ftype args iblock) = LLVMFunDecl fname ftype args
      (llvmBuildBuilder llvmEnv ftype $ toLLVMBuilder llvmEnv [] iblock)
