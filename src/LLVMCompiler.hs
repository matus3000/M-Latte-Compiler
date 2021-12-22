{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module LLVMCompiler (FCBinaryOperator(..),
                     FCRegister(..),
                     FCRValue(..),
                     FCInstr(..),) where
import Prelude

import Data.Maybe (fromMaybe)
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import Control.Monad.State.Strict
import Control.Monad.Except (Except, MonadError)

import CompilationError(SemanticError, SemanticError(CompilationError))
import Translator(CompilerExcept, Convertable(..))
import FCCompilerTypes
import qualified Translator as Tr
import qualified Data.Functor
import FCCompilerState (VariableEnvironment(..),
                        LLRegisterState(..),
                        ConstantsEnvironment(..),
                        BlockBuilder(..))

data VarEnv = VarEnv { varmap :: DM.Map String [FCRegister],
                       modifiedVariables :: [DS.Set String],
                       redeclaredVariables :: [DS.Set String]
                     }

data RegSt = RegSt { regMap :: DM.Map FCRegister FCRValue ,
                     rvalueMap :: DM.Map FCRValue FCRegister,
                     nextNormalId :: Int}

data CompileTimeConstants = CTC {constMap :: DM.Map String String,
                                 nextEtId :: Int}

data CurrentSubblock = ConditionB | SuccessB | FailureB
data BlockState = BlockState { blockName::String,
                               nextBlockId::Int,
                               stmtsList :: [FCInstr],
                               blockList :: [FCBlock]} |
                  CondBlockState {blockName :: String,
                                   conditionBlock :: Maybe FCBlock,
                                   success :: Maybe FCBlock,
                                   failure :: Maybe FCBlock,
                                   post :: Maybe FCBlock,
                                   current :: BlockType} |
                  WhileBlockState {blockName :: String,
                                   conditionBlock :: Maybe FCBlock,
                                   success :: Maybe FCBlock,
                                   post :: Maybe FCBlock,
                                   current :: BlockType
                                  }


-- data FCCState = FCCState {regSt :: RegSt,
--                           varSt :: VarSt,
--                           constEnv :: ConstStringEnv,
--                           blockSt :: BlockState}

-- type FCC = StateT FCCState CompilerExcept

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


-- translateExpr :: (ExpToFCStateMonad a) => Tr.IExpr -> Bool -> a FCRegister
-- translateExpr x save =
--   let
--     translateExprAddMull x save =
--       let
--         u :: (FCBinaryOperator, Tr.IExpr, Tr.IExpr)
--         u@(op, ie1, ie2) = case x of
--           Tr.IAdd iao ie1 ie2 -> (convert iao, ie1, ie2)
--           Tr.IMul imo ie1 ie2 -> (convert imo, ie1, ie2)
--           _ -> undefined
--       in
--         do
--           r1 <- translateExpr ie2 True
--           r2 <- translateExpr ie1 True
--           prependFCRValue RNormal $ FCBinOp op r1 r2
--   in
--     case x of
--       Tr.ILitInt n -> return $ (LitInt . fromInteger) n
--       Tr.ILitBool b -> return $ LitBool b
--       Tr.IString s -> do
--         constEt <- lookupStringName s
--         prependFCRValue RNormal $ GetPointer (Et constEt) (LitInt 0)
--       Tr.IVar s -> getVariable s Data.Functor.<&> fromMaybe undefined
--       addInstr@(Tr.IAdd iao ie ie') -> translateExprAddMull addInstr save
--       mulInstr@(Tr.IMul imo ie ie') -> translateExprAddMull mulInstr save
--       Tr.INeg ie -> do
--         reg <- translateExpr ie True
--         prependFCRValue RNormal $ FCUnOp Neg reg
--       Tr.INot ie -> do
--         reg <- translateExpr ie True
--         prependFCRValue RNormal $ FCUnOp BoolNeg reg
--       Tr.IAnd ie ie' -> do
--         r2 <- translateExpr ie' True
--         r1 <- translateExpr ie True
--         prependFCRValue RNormal $ FCBinOp BoolAnd  r1 r2
--       Tr.IOr ie ie' -> do
--         r2 <- translateExpr ie' True
--         r1 <- translateExpr ie True
--         prependFCRValue RNormal $ FCBinOp BoolAnd  r1 r2
--       Tr.IApp fun ies -> let
--         r ::(ExpToFCStateMonad a) =>  Bool -> Bool -> a FCRegister
--         r returnValues staticFun = if staticFun && not returnValues then return VoidReg else
--           do
--             args <- mapM (`translateExpr` True) (reverse ies)
--             prependFCRValue (if staticFun then RNormal else (if returnValues then RDynamic else RVoid))  $
--               FunCall fun args
--         in
--         isFunStatic fun >>= r True
--       Tr.IRel iro ie ie' -> do
--         r2 <- translateExpr ie' True
--         r1 <- translateExpr ie True
--         prependFCRValue RNormal $ FCBinOp (convert iro) r1 r2

-- translateIItem :: (InstrToFCStateMonad a) => Tr.IItem -> a ()
-- translateIItem (Tr.IItem s expr) = void $
--   do
--     mreg <- getVariable s
--     case mreg of
--       Just reg -> setVariable s reg
--       Nothing -> undefined

-- translateInstr :: (InstrToFCStateMonad a) => Tr.IStmt -> a ()
-- translateInstr stmt = case stmt of
--   Tr.IBStmt ib -> translateBlock ib
--   Tr.IDecl iis -> void $ do
--     iis <- mapM translateIItem (reverse iis)
--     return  ()
--   Tr.IAss s ie -> void $ do
--     mreg <- getVariable s
--     case mreg of
--       Just reg -> declareVariable s reg
--       Nothing -> undefined
--   Tr.IIncr s -> translateInstr (Tr.IAss s (Tr.IAdd Tr.IPlus (Tr.IVar s) (Tr.ILitInt 1)))
--   Tr.IDecr s -> translateInstr (Tr.IAss s (Tr.IAdd Tr.IMinus (Tr.IVar s) (Tr.ILitInt 1)))
--   Tr.IRet ie -> void $ do
--     r <- translateExpr ie True
--     prependFCRValue RVoid $ Return (Just r)
--   Tr.IVRet -> void $ prependFCRValue RVoid (Return Nothing)
--   Tr.ICond ie is -> do
--     addIfBlock (ie, is) (`translateExpr` True) translateInstr
--   Tr.ICondElse ie is is' -> addIfElseBlock (ie, is, is') (`translateExpr` True) translateInstr
--   Tr.IWhile ie is -> addWhileBlock (ie, is) (`translateExpr` True) translateInstr
--   Tr.ISExp ie -> void $ translateExpr ie False
--   Tr.IStmtEmpty -> return ()

-- translateBlock :: (InstrToFCStateMonad a) => Tr.IBlock -> a ()
-- translateBlock (Tr.IBlock stmts) = do
--   addBlock (reverse stmts) (mapM_ translateInstr)

-- compileBlock :: Tr.IBlock -> CompilerExcept [FCBlock]
-- compileBlock = undefined
-- compileFun :: Tr.IFun -> CompilerExcept ()
-- compileFun = undefined
-- compileToFC :: [Tr.IFun] -> CompilerExcept ()
-- compileToFC = undefined


instance Convertable Tr.IRelOp FCBinaryOperator where
  convert x = case x of
    Tr.ILTH -> Lth
    Tr.ILE -> Le
    Tr.IGTH -> Gth
    Tr.IGE -> Ge
    Tr.IEQU -> Equ
    Tr.INE -> Neq


-- putConstState :: ConstStringEnv -> FCC ()
-- putConstState newEnv = modifyConstState (const newEnv)
-- modifyConstState :: (ConstStringEnv -> ConstStringEnv) -> FCC ()
-- modifyConstState fun = modify (\(FCCState regst varst constenv blockst) -> FCCState regst varst (fun constenv) blockst)

-- fccEmplaceConstString :: String -> FCC String
-- fccEmplaceConstString x = do
--   constenv <- constEnv <$> get
--   let et = x `DM.lookup` stringMap constenv
--       nextid = nextEtId constenv
--   case et of
--     Nothing -> putConstState (ConstStringEnv (DM.insert x nextid (stringMap constenv)) (1 + nextid)) >>
--       return ("C" ++ show nextid)
--     Just n -> return $ "C" ++ show n

-- instance ExpToFCStateMonad FCC where
--   lookupStringName x = fccEmplaceConstString x


instance VariableEnvironment VarEnv String FCRegister where
  _setVariable key value (VarEnv vmap modvars redvars) =
    let x = [] `fromMaybe` DM.lookup key vmap
    in
      if null x
      then
        undefined
      else
        VarEnv (DM.insert key (value:tail x) vmap) (DS.insert key (head modvars) : tail modvars) redvars
  _declareVariable key value (VarEnv vmap modvars redvars) = let
    x = [] `fromMaybe` DM.lookup key vmap
    in
      if not (DS.member key (head redvars)) then
        VarEnv (DM.insert key (value:tail x) vmap) (DS.insert key (head modvars) : tail modvars) redvars
      else
        undefined
  _lookupVariable key (VarEnv vmap modvars redvars) = DM.member key vmap
  _getManyVariables keys (VarEnv vmap modvars redvars) = map (\key -> head <$> DM.lookup key vmap) keys
  _getVariable key (VarEnv vmap modvars redvars) = head <$> DM.lookup key vmap
  _openClosure (VarEnv vmap modvars redvars) = VarEnv vmap (DS.empty : modvars) (DS.empty : redvars)
  _closeClosure (VarEnv vmap modvars redvars) =
    let
      snd :: [a] -> Maybe a
      snd (x:y:rest) = Just y
      snd _ = Nothing
      modified = head modvars
      parent = DS.empty `fromMaybe` snd modvars
      popKey :: String -> DM.Map String [a] -> DM.Map String [a]
      popKey x map = DM.insert x vs map
        where
          (v:vs) = [] `fromMaybe` DM.lookup x map
    in
      VarEnv (foldl (\ map key -> undefined ) vmap (head redvars))
      (DS.union modified parent:(tail.tail$modvars)) (tail redvars)

instance LLRegisterState RegSt where
  _lookupRegister reg (RegSt regMap rvalueMap nextNormalIbd) = DM.lookup reg regMap
  _normalizeFCRValue fcrValue (RegSt regMap rvalueMap nextNormalIbd) =
    case fcrValue of
      original@(FCBinOp fbo fr fr') -> let norg = original in case fbo of
        Add -> undefined
        Sub -> original
        Div -> undefined
        Mul -> original
        Mod -> original
        LShift -> original
        RShif -> original
        ByteAnd -> original
        ByteOr -> original
        ByteXor -> original
        BoolAnd -> original
        BoolOr -> original
        BoolXor -> original
        Test -> undefined
        Le -> original
        Equ -> undefined
        Neq -> undefined
        Lth -> original
        Gth -> original
        Ge -> original
      _ -> fcrValue
  _mapFCRValue fcrValue regstate@(RegSt regMap rvalueMap nextNormalId) = case fcrValue' `DM.lookup` rvalueMap of
    Nothing -> let
      fr = Reg $ "%R" ++ show nextNormalId
      regMap' = DM.insert fr fcrValue' regMap
      rvalueMap' = DM.insert fcrValue' fr rvalueMap
      in
      (RegSt regMap' rvalueMap' (1 + nextNormalId), Right fr)
    Just fr -> (regstate, Left fr)
    where fcrValue' = _normalizeFCRValue fcrValue regstate

instance ConstantsEnvironment CompileTimeConstants String String where
  _getPointer str ctc@(CTC cmap next) = case DM.lookup str cmap of
      Just v -> (ctc, v)
      Nothing -> (CTC (DM.insert str ("C" ++ show next) cmap ) (next + 1), "C" ++ show next)

instance BlockBuilder BlockState FCInstr FCBlock where
--   _prependStmt fci (BlockState bN nBI sL bL) = BlockState bN nBI (fci:sL) bL
--   _prependBlock fcb (BlockState bn nbi sl bl) = BlockState bn nbi [] bl'
--     where
--       bl' = fcb : (if null sl then bl else FCSimpleBlock ("Placeholder", sl) : bl)
--   _build (BlockState bn nbi sl bl) = undefined

data FCC = FCC {venv::VarEnv, regenv::RegSt, constants::CompileTimeConstants, blocks::[BlockState]}
type FCCompiler = State FCC
fccPutVenv :: VarEnv -> FCC -> FCC
fccPutVenv ve' (FCC ve re c b) = FCC ve' re c b
fccPutRegenv :: RegSt -> FCC -> FCC
fccPutRegenv re' (FCC ve re c b) = FCC ve re' c b
fccPutConstants :: CompileTimeConstants -> FCC -> FCC
fccPutBlock :: [BlockState] -> FCC -> FCC
fccPutConstants c' (FCC ve re c b) = FCC ve re c' b
fccPutBlock b' (FCC ve re c b) = FCC ve re c b'

blockStatePutCurrent :: BlockType -> BlockState -> BlockState
blockStatePutCurrent st BlockState {} = undefined
blockStatePutCurrent c' (CondBlockState bn cb s f p c) = CondBlockState bn cb s f p c'
blockStatePutCurrent c' (WhileBlockState bn cb s p c) = WhileBlockState bn cb s p c'

newSimpleBlock :: String -> Int -> BlockState
newSimpleBlock s n = BlockState s n [] []

prependFCRValue :: RegType -> FCRValue -> FCCompiler FCRegister
prependFCRValue r rvalue = do
  result <- _mapFCRValueRegType r rvalue . regenv <$> get
  case snd result of
    Left r' -> return r'
    Right r' -> modify (fccPutRegenv $ fst result) >> return r'
getConstStringEt :: String -> FCCompiler String
getConstStringEt s = do
  (consEnb, et) <- _getPointer s . constants <$> get
  modify (fccPutConstants consEnb)
  return et
openBlock :: BlockType-> FCCompiler ()
openBlock bt = do
  _blocks <- blocks <$> get
  let (b:rest) = _blocks
      (nb, b') = case bt of
        Normal -> (newSimpleBlock "placeholder" 0, b)
        Cond -> (CondBlockState "placeholder" Nothing Nothing Nothing Nothing Check, b)
        While -> (WhileBlockState "placeholder" Nothing Nothing Nothing Check, b)
        rest -> case b of
          BlockState{} -> undefined
          b -> (newSimpleBlock "placeholder" 0, blockStatePutCurrent rest b)
  modify (fccPutBlock (nb:b':rest))
closeBlock :: FCCompiler ()
closeBlock = do
  fcc <- get
  let ve' = _closeClosure . venv $ fcc
      (h:p:tail) = blocks fcc
      bl' = _build h
      p' = _prependBlock bl' p
  modify $ fccPutBlock (p':tail)
protectVariables :: [String] -> FCCompiler ()
protectVariables vars = do
  ve <- venv <$> get
  let ve' = foldl (\ve var ->
                   case _getVariable var ve of
                     Just val -> _declareVariable var val ve
                     Nothing -> ve)
          (_openClosure ve) vars
  modify (fccPutVenv ve')
endprotection :: FCCompiler ()
endprotection = do
  modify (\fcc -> fccPutVenv (_closeClosure $ venv fcc) fcc)

