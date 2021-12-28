{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
-- TO DO:
-- a) Zamienić mapM getVar foldable na getVars
module LLVMCompiler (FCBinaryOperator(..),
                     FCRegister(..),
                     FCRValue(..),
                     FCInstr(..)) where
import Prelude

import Data.Maybe (fromMaybe)
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import Control.Monad.State.Strict
import Control.Monad.Except (Except, MonadError)

import CompilationError(SemanticError, SemanticError(CompilationError))
import Translator(CompilerExcept, Convertable(..))
import FCCompilerTypes as FCT
import qualified Translator as Tr
import qualified Data.Functor
import FCCompilerState (VariableEnvironment(..),
                        LLRegisterState(..),
                        ConstantsEnvironment(..),
                        BlockBuilder(..))
import FCCompilerTypes (FCRValue(FCEmptyExpr))

data VarEnv = VarEnv { varmap :: DM.Map String [FCRegister],
                       modifiedVariables :: [DS.Set String],
                       redeclaredVariables :: [DS.Set String]
                     }

data RegSt = RegSt { regMap :: DM.Map FCRegister FCRValue ,
                     rvalueMap :: DM.Map FCRValue FCRegister,
                     nextNormalId :: Int}

data CompileTimeConstants = CTC {constMap :: DM.Map String String,
                                 nextEtId :: Int}

data BlockState = BlockState { blockName::String,
                               nextBlockId::Int,
                               openedSimpleBlocks :: Int,
                               stmtsList :: [FCInstr],
                               blockList :: [FCBlock]} |
                  CondBlockState {blockName :: String,
                                   openedSimpleBlocks :: Int,
                                   conditionBlock :: Maybe FCBlock,
                                   conditionReg :: Maybe FCRegister,
                                   success :: Maybe FCBlock,
                                   failure :: Maybe FCBlock,
                                   post :: Maybe FCBlock,
                                   current :: BlockType} |
                  WhileBlockState {blockName :: String,
                                   openedSimpleBlocks :: Int,
                                   conditionBlock :: Maybe FCBlock,
                                   success :: Maybe FCBlock,
                                   post :: Maybe FCBlock,
                                   current :: BlockType
                                  } |
                  FunBlockState { blockName :: String,
                                  body :: FCBlock
                                }

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


translateExpr :: Tr.IExpr -> Bool -> FCCompiler FCRegister
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
--         constEt <- getConstStringEt s
--         prependFCRValue RNormal $ GetPointer (Et constEt) (LitInt 0)
--       Tr.IVar s -> getVar s
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
--         r ::  Bool -> Bool -> FCCompiler FCRegister
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
translateExpr x save = return VoidReg

translateIItem :: Tr.IItem -> FCCompiler ()
translateIItem (Tr.IItem s ie) = void $
  do
    reg <- translateExpr ie True
    declVar s reg

translateInstr :: Tr.IStmt -> FCCompiler ()
translateInstr _ = return ()
-- translateInstr stmt = case stmt of
--   Tr.IBStmt ib -> translateBlock ib
--   Tr.IDecl iis -> void $ do
--     iis <- mapM translateIItem (reverse iis)
--     return  ()
--   Tr.IAss s ie -> do
--     reg <- translateExpr ie True
--     setVar s reg
--   Tr.IIncr s -> translateInstr (Tr.IAss s (Tr.IAdd Tr.IPlus (Tr.IVar s) (Tr.ILitInt 1)))
--   Tr.IDecr s -> translateInstr (Tr.IAss s (Tr.IAdd Tr.IMinus (Tr.IVar s) (Tr.ILitInt 1)))
--   Tr.IRet ie -> void $ do
--     r <- translateExpr ie True
--     prependFCRValue RVoid $ Return (Just r)
--   Tr.IVRet -> void $ prependFCRValue RVoid (Return Nothing)
  -- Tr.ICond ie iblock (Tr.MD md) -> do
  --   let ascmd = DS.toAscList md
  --   parname <- getBlockName
  --   openBlock Cond


  --   oldVal <- mapM getVar ascmd
  --   openBlock Check
  --   r <- translateExpr ie True
  --   closeBlock

  --   openBlock Success
  --   protectVariablesCond ascmd
  --   sname <- getBlockName
  --   translateBlock iblock
  --   smd <- mapM getVar ascmd
  --   endprotection
  --   closeBlock

  --   openBlock Post
  --   phi ascmd (parname, oldVal) (sname, smd)
  --   closeBlock

  --   closeBlock
  -- Tr.ICondElse ie ib ib' (Tr.MD md) -> do
  --   let ascmd = DS.toAscList md
  --   openBlock Cond

  --   openBlock Check
  --   r <- translateExpr ie True
  --   closeBlock

  --   openBlock Success
  --   protectVariablesCond ascmd
  --   sname <- getBlockName
  --   translateBlock ib
  --   smd <- mapM getVar ascmd
  --   endprotection
  --   closeBlock

  --   openBlock Failure
  --   protectVariablesCond ascmd
  --   fname <- getBlockName
  --   translateBlock ib'
  --   fmd <- mapM getVar ascmd
  --   endprotection
  --   closeBlock

  --   openBlock Post
  --   phi ascmd (sname, smd) (fname, fmd)
  --   closeBlock

  --   closeBlock
  -- Tr.IWhile ie ib (Tr.MD md) -> do
  --   let ascmd = DS.toAscList md
  --   parName <- getBlockName
  --   oldValues <- mapM getVar ascmd

  --   openBlock While

  --   openBlock Check
  --   r <- translateExpr ie True
  --   closeBlock

  --   openBlock Success
  --   protectVariablesWhile ascmd
  --   sname <- getBlockName
  --   translateBlock ib
  --   smd <- mapM getVar ascmd
  --   endprotection
  --   closeBlock

  --   openBlock Post
  --   phi ascmd (parName, oldValues) (sname, smd)
  --   closeBlock

  --   closeBlock

  -- Tr.ISExp ie -> void $ translateExpr ie False
  -- Tr.IStmtEmpty -> return ()

translateBlock :: Tr.IBlock -> FCCompiler ()
translateBlock (Tr.IBlock stmts) = do
  openBlock Normal
  mapM_ translateInstr stmts
  closeBlock

translateFun :: Tr.IFun -> FCCompiler FCFun
translateFun (Tr.IFun s lt lts ib) = do
  openFunBlock s
  FCFun (convert lt) s (map convert lts) <$> closeFunBlock
translateProg :: [Tr.IFun] -> FCCompiler [FCFun]
translateProg = mapM translateFun
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
  _normalizeFCRValue fcrValue (RegSt regMap rvalueMap nextNormalIbd) = undefined
    -- case fcrValue of
    --   original@(FCBinOp fbo fr fr') -> let norg = original in case fbo of
    --     Add -> undefined
    --     Sub -> original
    --     Div -> undefined
    --     Mul -> original
    --     Mod -> original
    --     LShift -> original
    --     RShif -> original
    --     ByteAnd -> original
    --     ByteOr -> original
    --     ByteXor -> original
    --     BoolAnd -> original
    --     BoolOr -> original
    --     BoolXor -> original
    --     Test -> undefined
    --     Le -> original
    --     Equ -> undefined
    --     Neq -> undefined
    --     Lth -> original
    --     Gth -> original
    --     Ge -> original
    --   _ -> fcrValue
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
  _build (BlockState bn nbi 0 sl bl) = FCComplexBlock bn (FCSimpleBlock "PlaceHolder" sl : bl)
  _build BlockState {} = undefined
  _build (CondBlockState bname _ (Just conBlock) _ (Just successBlock) Nothing (Just postBlock) _) =
    FCCondBlock conBlock successBlock postBlock
  _build (CondBlockState bname _ (Just conBlock) _ (Just successBlock) (Just failureBlock) (Just postBlock) _) =
    FCCondElseBlock conBlock successBlock failureBlock postBlock
  _build CondBlockState{} = undefined
  _build (WhileBlockState bname _ (Just cb) (Just s) (Just p) _) =
    FCWhileBlock cb s p
  _build WhileBlockState{} = undefined


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

-- blockStatePutCurrent :: BlockType -> BlockState -> BlockState
-- blockStatePutCurrent st BlockState {} = undefined
-- blockStatePutCurrent c' (CondBlockState bn x cb s f p c) = CondBlockState bn x cb s f p c' --TO DO 
-- blockStatePutCurrent c' (WhileBlockState bn cb s p c) = WhileBlockState bn cb s p c'

newSimpleBlock :: String -> Int -> BlockState
newSimpleBlock s n = BlockState s n 0 [] []

newCondBlockSt :: String -> BlockState
newCondBlockSt name = CondBlockState name 0 Nothing Nothing Nothing Nothing Nothing BTPlacceHolder
newWhileBlockSt :: String -> BlockState
newWhileBlockSt name = WhileBlockState name 0 Nothing Nothing Nothing BTPlacceHolder

isFunStatic :: String -> FCCompiler Bool
isFunStatic _ = return False

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

openFunBlock :: String -> FCCompiler ()
openFunBlock fname =
  do
    list <- gets ((newSimpleBlock (fname ++ "b") 0 :) . blocks)
    modify (fccPutBlock list)
closeFunBlock :: FCCompiler FCBlock
closeFunBlock = undefined

openBlock :: BlockType -> FCCompiler ()
openBlock bt = do
  fcc <- get
  let ve' = _openClosure $ venv fcc
      (parent:rest) = blocks fcc
      newBlocks = case parent of
        (BlockState bN nBI oSB sL bL) ->
          case bt of
            Normal -> BlockState bN nBI (oSB + 1) sL bL:rest
            Cond -> newCondBlockSt (bN ++ show nBI):(BlockState bN nBI oSB [] (FCSimpleBlock "" sL:bL):rest)
            While -> newWhileBlockSt(bN ++ show nBI):(BlockState bN nBI oSB [] (FCSimpleBlock "" sL:bL):rest)
            _ -> undefined
        (CondBlockState bn osb cb cr s f p c) ->
          case bt of
            Check -> BlockState bn 0 0 [] [] :CondBlockState bn osb cb cr s f p bt :rest
            Success -> BlockState bn' 0 0 [] [] :CondBlockState bn osb cb cr s f p bt :rest
              where
                bn' = bn ++ "s"
            Failure -> BlockState bn' 0 0 [] [] :CondBlockState bn osb cb cr s f p bt :rest
              where
                bn' = bn ++ "f"
            Post -> BlockState bn' 0 0 [] [] :CondBlockState bn osb cb cr s f p bt :rest
              where
                bn' = bn ++ "p"
            _ -> undefined
        (WhileBlockState bn osb cb s p c) ->
          case bt of
            Check -> BlockState bn' 0 0 [] [] :WhileBlockState bn osb cb s p bt: rest
              where
                bn' = bn
            Success -> BlockState bn' 0 0 [] [] :WhileBlockState bn osb cb s p bt: rest
              where
                bn' = bn ++ "s"
            Post -> BlockState bn' 0 0 [] [] :WhileBlockState bn osb cb s p bt: rest
              where
                bn' = bn ++ "p"
            _ -> undefined
  modify $ fccPutVenv ve' . fccPutBlock newBlocks
closeBlock :: FCCompiler ()
closeBlock = do
  fcc <- get
  let ve' = _closeClosure . venv $ fcc
      newBlocks = []
  modify $ fccPutVenv ve' . fccPutBlock newBlocks
  where
    f :: [BlockState] -> [BlockState]
    f (blockSt@(BlockState _ _ 0 _ _) : CondBlockState bn osb cb cr s f p c : rest) =
      case c of
        Check -> CondBlockState bn osb (Just block) cr s f p c' : rest
        Success -> CondBlockState bn osb cb cr (Just block) f p c' : rest
        Failure -> CondBlockState bn osb cb cr s (Just block) p c' : rest
        Post -> CondBlockState bn osb cb cr s f (Just block) c' : rest
        _ -> undefined
        where
          block = _build blockSt
          c' = BTPlacceHolder
    f (blockSt@(BlockState _ _ 0 _ _) : WhileBlockState bn osb cb s p c : rest) =
      case c of
        Check -> WhileBlockState bn osb cb s p c' : rest
        Success -> WhileBlockState bn osb cb s p c' : rest
        Post -> WhileBlockState bn osb cb s p c' : rest
        _ -> undefined
        where
          block = _build blockSt
          c' = BTPlacceHolder
    f (blockSt@(BlockState _ _ 0 _ _) : (BlockState bn nbi osb sl bl) : rest) =
      BlockState bn nbi osb sl (_build blockSt:bl):rest
    f (BlockState bn nBI r sL bL : rest) = BlockState bn nBI (r - 1) sL bL : rest
    f _ = undefined

protectVariablesCond :: [String] -> FCCompiler ()
protectVariablesCond vars = do
  ve <- venv <$> get
  let ve' = foldl (\ve var ->
                   case _getVariable var ve of
                     Just val -> _declareVariable var val ve
                     Nothing -> ve)
          (_openClosure ve) vars
  modify (fccPutVenv ve')
protectVariablesWhile :: [String] -> FCCompiler ()
protectVariablesWhile = undefined
endprotection :: FCCompiler ()
endprotection = do
  modify (\fcc -> fccPutVenv (_closeClosure $ venv fcc) fcc)

getBlockName :: FCCompiler String
getBlockName =
  do
    x <- gets blocks
    return $ case x of
      (BlockState name _ _ _ _):rest -> name
      (CondBlockState name _ _ _ _ _ _ _):rest -> name
      (WhileBlockState name _ _ _ _ _):rest -> name
      _ -> undefined

getVar :: String -> FCCompiler FCRegister
getVar var = do
  value <- gets (_getVariable var . venv)
  return $ undefined `fromMaybe` value
setVar :: String -> FCRegister -> FCCompiler ()
setVar var value = do
  vars' <- gets $ _setVariable var value . venv
  modify $ fccPutVenv vars'

declVar :: String -> FCRegister -> FCCompiler ()
declVar var value = do
  vars' <- gets $ _declareVariable var value . venv
  modify $ fccPutVenv vars'

phi :: [String] -> (String, [FCRegister]) -> (String, [FCRegister]) -> FCCompiler ()
phi = undefined
