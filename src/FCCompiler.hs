{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

-- TO DO:
-- a) Zamienić mapM getVar foldable na getVars
-- b) Sprawić, żeby return nie otrzymawało normalnego rejestru, tylko rejestr typu void.
module FCCompiler where

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
                        ConstantsEnvironment(..))
import FCCompilerTypes (FCRValue(FCEmptyExpr, FCPhi),
                        FCType(..),
                        FCBlock(..))
import VariableEnvironment(VarEnv(..), newVarEnv)
import qualified VariableEnvironment as VE
import qualified IDefinition as IDef
import Data.Foldable (foldlM)
import qualified VariableEnvironment as VC
import DynFlags (ContainsDynFlags)
import qualified Control.Arrow as BiFunctor

type FCVarEnv = VarEnv String FCRegister

data RegSt = RegSt { regMap :: DM.Map FCRegister FCRValue ,
                     rvalueMap :: DM.Map FCRValue FCRegister,
                     nextNormalId :: Int}

regStNew :: RegSt
regStNew = RegSt {regMap = DM.empty ,
                  rvalueMap=DM.empty,
                  nextNormalId=0}

data CompileTimeConstants = CTC {constMap :: DM.Map String String,
                                 nextEtId :: Int}
ctcNew = CTC DM.empty 0

data BlockBuilder = BB {instrAcc::[FCInstr], blockAcc::[FCBlock]}

bbaddBlock :: FCBlock -> BlockBuilder -> BlockBuilder
bbaddBlock block bb = BB []
  (block:(
      case instrAcc bb of
        [] -> blockAcc bb
        instrs -> FCNamedSBlock "" (reverse instrs): blockAcc bb))
bbaddInstr :: FCInstr -> BlockBuilder -> BlockBuilder
bbaddInstr instr bb = BB (instr:instrAcc bb) (blockAcc bb)
bbBuildAnonymous :: BlockBuilder -> FCBlock
bbBuildAnonymous bb = FCComplexBlock
  ""
  (reverse $
    case instrAcc bb of
      [] -> blockAcc bb
      intrs -> FCNamedSBlock "" (reverse intrs):blockAcc bb)
bbBuildNamed :: BlockBuilder -> String  -> FCBlock
bbBuildNamed bb name = let
  instrs = instrAcc bb
  blocks = blockAcc bb
  in
  case (instrs, blocks) of
    ([], []) -> FCComplexBlock name []
    ([], [block]) -> case block of
      (FCNamedSBlock " "fcabi) -> FCNamedSBlock name fcabi
      _ -> FCComplexBlock name [block]
    ([], blocks) -> FCComplexBlock name (reverse blocks)
    (instrs, blocks) -> FCComplexBlock name (reverse $ FCNamedSBlock "" (reverse instrs):blocks)
bbNew :: BlockBuilder
bbNew = BB [] []

fccNew :: FCC
fccNew = FCC newVarEnv regStNew ctcNew []
data FCC = FCC {fccVenv::FCVarEnv, fccRegEnv::RegSt, fccConstants::CompileTimeConstants, fccBlocksCounts::[Int]}
type FCCompiler = State FCC
fccPutVenv :: FCVarEnv -> FCC -> FCC
fccPutVenv ve' (FCC ve re c b) = FCC ve' re c b
fccPutRegenv :: RegSt -> FCC -> FCC
fccPutRegenv re' (FCC ve re c b) = FCC ve re' c b
fccPutConstants :: CompileTimeConstants -> FCC -> FCC
fccPutConstants c' (FCC ve re c b) = FCC ve re c' b
fccPutBlocksCounts fbc' (FCC ve re c fbc) = FCC ve re c fbc'


translateAndExpr :: String -> BlockBuilder -> Tr.IExpr -> Bool -> FCCompiler (BlockBuilder, (FCType, FCRegister))
translateAndExpr bn bb (Tr.IAnd (ie:ies)) save =
  g bn bb ie ies
  where
    g :: String-> BlockBuilder ->Tr.IExpr -> [Tr.IExpr] -> FCCompiler (BlockBuilder, (FCType, FCRegister))
    g bname bb ie rest = do
      withOpenBlock bname BoolExp $ \bname -> do

        blocks <- gets fccBlocksCounts

        let block = if null blocks then undefined else head blocks
            failureEt = nextBlockName bname block Failure
            postEt = nextBlockName bname block Post

        (cb, (_, jreg)) <- withOpenBlock bname Check $ \bname ->
          BiFunctor.first bbBuildAnonymous <$> translateExpr bname bbNew  ie True

        (sb, sreg, sbn) <- withOpenBlock bname Success $
          \bname -> f bname bbNew ies (failureEt, postEt)

        (fb, (_, _)) <- withOpenBlock bname Failure $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump postEt) bbNew) bname,
                  (Void, VoidReg))

        (pb, res) <- withOpenBlock bname Post $ \bname -> do
          rtype <- getRegisterType sreg
          let phi = FCPhi rtype [(sreg, Et sbn), (LitBool False, Et failureEt)]
          (bb', r)<- emplaceFCRValue RNormal phi bbNew
          return (bbBuildNamed bb' bname, r)

        let returnBlock = FCCondBlock bname cb jreg sb fb pb
        return (bbaddBlock returnBlock bb, (Bool, res))

    f :: String -> BlockBuilder -> [Tr.IExpr] -> (String, String) -> FCCompiler (FCBlock, FCRegister, String)
    f bn bb [ie] (_, postEt) = do
      withOpenBlock bn Normal $ \bname -> do
        (cbb, (ftype, reg)) <- translateExpr bname bbNew  ie True -- Można zmienić na BIFunctor
        return (bbBuildNamed (bbaddInstr (VoidReg, jump postEt) cbb) bname, reg, bname)
    f bn bb (ie:rest) (failureEt, postEt) = do

        (cb, (_, jreg)) <- withOpenBlock bn Check $ \bname ->
          (bbBuildAnonymous `BiFunctor.first`) <$> translateExpr bname bbNew  ie True

        (sb, r, bn') <- withOpenBlock bn BoolExp $ \bname -> do
          f bname bbNew rest (failureEt, postEt)

        (fb, (_, _)) <- withOpenBlock bn Failure $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump failureEt) bbNew) bname, (Void, VoidReg))

        let returnBlock = FCPartialCond bn cb jreg sb fb

        return (returnBlock, r, bn')
translateOrExpr :: String -> BlockBuilder -> Tr.IExpr -> Bool
  -> FCCompiler (BlockBuilder, (FCType, FCRegister))
translateOrExpr bn bb (Tr.IOr (ie:ies)) save =
  g bn bb ie ies
  where
    g :: String-> BlockBuilder ->Tr.IExpr -> [Tr.IExpr] -> FCCompiler (BlockBuilder, (FCType, FCRegister))
    g bname bb ie rest = do
      withOpenBlock bname BoolExp $ \bname -> do

        blocks <- gets fccBlocksCounts

        let block = if null blocks then undefined else head blocks
            successEt = nextBlockName bname block Success
            postEt = nextBlockName bname block Post

        (cb, (_, jreg)) <- withOpenBlock bname Check $ \bname ->
          BiFunctor.first bbBuildAnonymous <$> translateExpr bname bbNew  ie True

        (sb, (_, _)) <- withOpenBlock bname Success $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump postEt) bbNew) bname,
                  (Void, VoidReg))

        (fb, sreg, sbn) <- withOpenBlock bname Failure $
          \bname -> f bname bbNew ies (successEt, postEt)

        (pb, res) <- withOpenBlock bname Post $ \bname -> do
          rtype <- getRegisterType sreg
          let phi = FCPhi rtype [(sreg, Et sbn), (LitBool True, Et successEt)]
          (bb', r)<- emplaceFCRValue RNormal phi bbNew
          return (bbBuildNamed bb' bname, r)

        let returnBlock = FCCondBlock bname cb jreg sb fb pb
        return (bbaddBlock returnBlock bb, (Bool, res))

    f :: String -> BlockBuilder -> [Tr.IExpr] -> (String, String) -> FCCompiler (FCBlock, FCRegister, String)
    f bn bb [ie] (_, postEt) = do
      withOpenBlock bn Normal $ \bname -> do
        (cbb, (ftype, reg)) <- translateExpr bname bbNew  ie True -- Można zmienić na BIFunctor
        return (bbBuildNamed (bbaddInstr (VoidReg, jump postEt) cbb) bname, reg, bname)
    f bn bb (ie:rest) (successEt, postEt) = do

        (cb, (_, jreg)) <- withOpenBlock bn Check $ \bname ->
          (bbBuildAnonymous `BiFunctor.first`) <$> translateExpr bname bbNew  ie True

        (sb, (_, _)) <- withOpenBlock bn Success $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump successEt) bbNew) bname, (Void, VoidReg))

        (fb, r, bn') <- withOpenBlock bn BoolExp $ \bname -> do
          f bname bbNew rest (successEt, postEt)

        let returnBlock = FCPartialCond bn cb jreg sb fb

        return (returnBlock, r, bn')


translateExpr :: String -> BlockBuilder -> Tr.IExpr -> Bool -> FCCompiler (BlockBuilder, (FCType, FCRegister))
translateExpr bname bb ie save =
  let
    translateExprAddMull :: Tr.IExpr -> BlockBuilder -> Bool -> FCCompiler (BlockBuilder, (FCType, FCRegister))
    translateExprAddMull ie bb save =
      let
        u :: (FCBinaryOperator, Tr.IExpr, Tr.IExpr)
        u@(op, ie1, ie2) = case ie of
          Tr.IAdd iao ie1 ie2 -> (convert iao, ie1, ie2)
          Tr.IMul imo ie1 ie2 -> (convert imo, ie1, ie2)
          _ -> undefined
      in
        do
          (bb', (t1, r1)) <- translateExpr bname bb ie1 True
          (bb'', (t2, r2)) <- translateExpr bname bb' ie2 True
          (b''', r) <- emplaceFCRValue RNormal (FCBinOp t1 op r1 r2) bb''
          return (b''', (t1, r))
  in
    case ie of
      Tr.ILitInt n -> return  (bb, (Int , LitInt $ fromInteger n))
      Tr.ILitBool b -> return (bb, (Bool, LitBool b))
       -- Tr.IString s -> do
       --   constEt <- getConstStringEt s
       --   prependFCRValue RNormal $ GetPointer (Et constEt) (LitInt 0)
      Tr.IVar s -> (bb, ) <$> getVar s
      addInstr@(Tr.IAdd iao ie ie') -> translateExprAddMull addInstr bb save
      mulInstr@(Tr.IMul imo ie ie') -> translateExprAddMull mulInstr bb save
      Tr.INeg ie ->  do
        (bb', (ftype, reg)) <- translateExpr' bb ie True
        (bb'', reg') <- emplaceFCRValue RNormal (FCUnOp ftype Neg reg) bb'
        return (bb'', (ftype, reg'))
       -- Tr.INot ie -> do
       --   reg <- translateExpr ie True
       --   prependFCRValue RNormal $ FCUnOp BoolNeg reg
      Tr.IAnd _ -> do
        translateAndExpr bname bb ie True
      Tr.IOr _ -> do
        translateOrExpr bname bb ie True
       -- Tr.IApp fun ies -> let
       --   r ::  Bool -> Bool -> FCCompiler FCRegister
       --   r returnValues staticFun = if staticFun && not returnValues then return VoidReg else
       --     do
       --       args <- mapM (`translateExpr` True) (reverse ies)
       --       prependFCRValue (if staticFun then RNormal else (if returnValues then RDynamic else RVoid))  $
       --         FunCall fun args
       --   in
       --   isFunStatic fun >>= r True
      Tr.IRel iro ie ie' -> do
        (bb', (ftype1, r1)) <- translateExpr' bb ie True
        (bb'', (ftype2, r2)) <- translateExpr' bb' ie' True
        (bb''', reg) <- emplaceFCRValue RNormal (FCBinOp ftype1 (convert iro) r1 r2) bb''
        return (bb''', (Bool, reg))
      _ -> error "Unimplemented TR.Expr for TranslateExpr"
  where
    translateExpr' = translateExpr bname
translateIItem :: String -> Tr.IItem -> BlockBuilder -> FCCompiler BlockBuilder
translateIItem bname (Tr.IItem s ie) bb=
  do
    (bb',(ftype, reg)) <- translateExpr bname bb ie True
    declVar s reg
    return bb'

translateInstr :: String -> BlockBuilder -> Tr.IStmt -> FCCompiler BlockBuilder
translateInstr name bb stmt = case stmt of
  Tr.IBStmt ib -> translateBlock name ib bb
  Tr.IDecl iis -> foldlM translateIItem' bb iis
  Tr.IAss s ie -> do
    (bb', (ftype, reg)) <- translateExpr' bb ie True
    setVar s reg
    return bb'
  Tr.IIncr s -> translateInstr' (Tr.IAss s (Tr.IAdd Tr.IPlus (Tr.IVar s) (Tr.ILitInt 1)))
  Tr.IDecr s -> translateInstr' (Tr.IAss s (Tr.IAdd Tr.IMinus (Tr.IVar s) (Tr.ILitInt 1)))
  Tr.IRet ie -> do
    (bb', (ft, r)) <- translateExpr' bb ie True
    return $ bbaddInstr (VoidReg, Return ft (Just r)) bb'
  Tr.IVRet -> return $ bbaddInstr (VoidReg, Return Void Nothing) bb
  Tr.ICond ie iblock (Tr.MD md) ->
    withOpenBlock name Cond $ \name -> do
    let ascmd = DS.toAscList md
        postEtStr = ""
        successEt = Et ""
        failureEt = Et ""

    oldVals <- mapM getVar ascmd

    (cb, jr) <- withOpenBlock name Check $ (\name -> (do
                                                         (bb, (_, reg)) <- translateExpr name bbNew ie True
                                                         return (bbBuildNamed bb name , reg)))

    (newVals, sb) <- withOpenBlock name Success $ (\name ->
                                                     withProtectedVars ascmd $ do
                                                      sbb <- translateBlock name iblock bbNew
                                                      newVal <- mapM getVar ascmd
                                                      return (newVal, bbBuildNamed sbb name))

    fb <- withOpenBlock name Failure $ (\name -> do
                                           return $ bbBuildNamed (bbaddInstr (VoidReg, jump postEtStr) bbNew) name)
        
    pb <- withOpenBlock name Post $ \name -> (do
                                                 pbb <- phi (zip ascmd (zip newVals oldVals)) successEt failureEt
                                                 return (bbBuildNamed pbb name))

    return $ bbaddBlock (FCCondBlock name cb jr sb fb pb) bb
--   -- Tr.ICondElse ie ib ib' (Tr.MD md) -> do
--   --   let ascmd = DS.toAscList md
--   --   openBlock Cond

--   --   openBlock Check
--   --   r <- translateExpr ie True
--   --   closeBlock

--   --   openBlock Success
--   --   protectVariablesCond ascmd
--   --   sname <- getBlockName
--   --   translateBlock ib
--   --   smd <- mapM getVar ascmd
--   --   endprotection
--   --   closeBlock

--   --   openBlock Failure
--   --   protectVariablesCond ascmd
--   --   fname <- getBlockName
--   --   translateBlock ib'
--   --   fmd <- mapM getVar ascmd
--   --   endprotection
--   --   closeBlock

--   --   openBlock Post
--   --   phi ascmd (sname, smd) (fname, fmd)
--   --   closeBlock

--   --   closeBlock
--   -- Tr.IWhile ie ib (Tr.MD md) -> do
--   --   let ascmd = DS.toAscList md
--   --   parName <- getBlockName
--   --   oldValues <- mapM getVar ascmd

--   --   openBlock While

--   --   openBlock Check
--   --   r <- translateExpr ie True
--   --   closeBlock

--   --   openBlock Success
--   --   protectVariablesWhile ascmd
--   --   sname <- getBlockName
--   --   translateBlock ib
--   --   smd <- mapM getVar ascmd
--   --   endprotection
--   --   closeBlock

--   --   openBlock Post
--   --   phi ascmd (parName, oldValues) (sname, smd)
--   --   closeBlock

--   --   closeBlock
  Tr.ISExp ie -> fst <$> translateExpr' bb ie False
  Tr.IStmtEmpty -> return bb
  _ -> error  "TranslateInstr: WIP"
  where
    translateIItem' = flip $ translateIItem name
    translateExpr' = translateExpr name
    translateInstr' = translateInstr name bb
    phi :: [(String,((FCType, FCRegister),(FCType, FCRegister)))] -> FCRegister -> FCRegister -> FCCompiler BlockBuilder
    phi list successEt failureEt = foldlM (\bb (var, ((st, sval),(ft, fval))) ->
                         do
                           (bb, r) <- emplaceFCRValue
                                      RPhi (FCPhi ft [(sval, successEt), (fval, failureEt)]) bb
                           setVar var r
                           return bb) bbNew list

translateBlock :: String -> Tr.IBlock -> BlockBuilder -> FCCompiler BlockBuilder
translateBlock blockName (Tr.IBlock stmts) rest =
  withOpenBlock blockName Normal $ (\blockName ->foldlM (translateInstr blockName) rest stmts)

translateFun :: Tr.IFun -> FCCompiler FCFun
translateFun (Tr.IFun s lt lts ib) = do
  withOpenFunBlock s lt lts $ \res ->
    do
      fbody <- translateBlock s ib bbNew
      return $ FCFun {name = s, retType = convert lt, args = res, FCT.body = bbBuildAnonymous fbody}

-- translateFunTest :: Tr.IFun -> FCCompiler FCFun
-- translateFunTest (Tr.IFun s lt lts ib) = do
--   withOpenFunBlock s lt lts $ \res ->
--     (do
--         x <- mapM (getVar . fst) lts
--         return FCFun {name = s, retType = convert lt, args = res, FCT.body = bbBuild bbNew}
--     )

translateProg :: [Tr.IFun] -> FCCompiler FCProg
translateProg list = do
  fbodies <- mapM
    ( \ifun ->
        do
          translateFun ifun
    ) list
  return $ FCProg fbodies

compileProg :: [Tr.IFun] -> FCProg
compileProg ifun = let
  (s, a) = runState (translateProg ifun) initialFcc
  in
  s
  where
    initialFcc = fccPutVenv (VE.openClosure $ fccVenv fccNew) fccNew
-- compileBlock :: Tr.IBlock -> CompilerExcept [FCBlock]
-- compileBlock = undefined
-- compileFun :: Tr.IFun -> CompilerExcept ()
-- compileFun = undefined
-- compileToFC :: [Tr.IFun] -> CompilerExcept ()
-- compileToFC = undefined


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

-- lookupRegister :: FCRegister -> FCCompiler FCType

_nextNormalRegister :: RegSt -> (RegSt, FCRegister)
_nextNormalRegister (RegSt regMap rvalueMap nextNormalId) =
  (RegSt regMap rvalueMap (nextNormalId + 1), Reg $ "R" ++ show nextNormalId)
_putRegisterValue :: FCRegister -> FCRValue -> RegSt -> RegSt
_putRegisterValue = undefined
instance LLRegisterState RegSt where
  _lookupRegister reg (RegSt regMap rvalueMap nextNormalIbd) = DM.lookup reg regMap
  _normalizeFCRValue fcrValue (RegSt regMap rvalueMap nextNormalIbd) = fcrValue
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
  _mapFCRValue fcrValue regstate@(RegSt regMap rvalueMap nextNormalId) = case fcrValue `DM.lookup` rvalueMap of
    Nothing -> let
      fr = Reg $ "R" ++ show nextNormalId
      regMap' = DM.insert fr fcrValue' regMap
      rvalueMap' = DM.insert fcrValue' fr rvalueMap
      in
      (RegSt regMap' rvalueMap' (1 + nextNormalId), Right fr)
    Just fr -> (regstate, Left fr)
    where fcrValue' = _normalizeFCRValue fcrValue regstate
  _mapFCRValueRegType _ fcr regst = _mapFCRValue fcr regst

instance ConstantsEnvironment CompileTimeConstants String String where
  _getPointer str ctc@(CTC cmap next) = case DM.lookup str cmap of
      Just v -> (ctc, v)
      Nothing -> (CTC (DM.insert str ("C" ++ show next) cmap ) (next + 1), "C" ++ show next)

-- instance BlockBuilder BlockState FCInstr FCBlock where
--   _build (FunBlockState fname body) = case body of
--     Just x -> x
--     Nothing -> error "FunBlockState musi mieć syna"
--   _build (BlockState bn nbi 0 sl bl) = let
--     slBlock = FCSimpleBlock bn (reverse sl)
--     in
--     if null bl then slBlock else FCComplexBlock bn (reverse (slBlock:bl))
--   _build BlockState {} = error "Cannot build block which have an opened simple block."
--   -- _build (CondBlockState bname _ (Just conBlock) _ (Just successBlock) Nothing (Just postBlock) _) =
--   --   FCCondBlock conBlock successBlock postBlock
--   -- _build (CondBlockState bname _ (Just conBlock) _ (Just successBlock) (Just failureBlock) (Just postBlock) _) =
--   --   FCCondElseBlock conBlock successBlock failureBlock postBlock
--   -- _build CondBlockState{} = undefined
--   -- _build (WhileBlockState bname _ (Just cb) (Just s) (Just p) _) =
--   --   FCWhileBlock cb s p
--   -- _build WhileBlockState{} = undefined
--   _build _ = error "_build: WIP"
--   _prependStmt stmt block = case block of
--     BlockState s n i fis fbs -> BlockState s n i (stmt:fis) fbs
--     FunBlockState {} -> error "_prependStmt dla FunBlock"
--     _ -> error "Pojedyncze akcje powinny być prependowane jedynie do zwykłego bloku"
--   _prependBlock a block = case block of
--     BlockState s n i fci fbs -> BlockState s n i [] (a:FCSimpleBlock s fci:fbs)
--     CondBlockState s n m_fb m_fr ma m_fb' ma' bt -> error "_preprend CondBlockState: unimplemented"
--     WhileBlockState s n m_fb ma m_fb' bt -> error "_preprend WhileBlockState: unimplemented"
--     FunBlockState s m_fb -> case m_fb of
--       Just _ -> error "FunBlockState może posiadać tylko jedno dziecko"
--       Nothing -> FunBlockState s (Just a)


-- newSimpleBlock :: String -> Int -> BlockState
-- newSimpleBlock s n = BlockState s n 0 [] []

-- newCondBlockSt :: String -> BlockState
-- newCondBlockSt name = CondBlockState name 0 Nothing Nothing Nothing Nothing Nothing BTPlacceHolder
-- newWhileBlockSt :: String -> BlockState
-- newWhileBlockSt name = WhileBlockState name 0 Nothing Nothing Nothing BTPlacceHolder

-- isFunStatic :: String -> FCCompiler Bool
-- isFunStatic _ = return False

emplaceFCRValue :: RegType -> FCRValue -> BlockBuilder -> FCCompiler (BlockBuilder, FCRegister)
emplaceFCRValue r rvalue bb = do
  result <- _mapFCRValueRegType r rvalue . fccRegEnv <$> get
  case snd result of
    Left r' -> return (bb, r')
    Right r' -> modify (fccPutRegenv $ fst result) >> return (bbaddInstr (r', rvalue) bb, r')

-- getConstStringEt :: String -> FCCompiler String
-- getConstStringEt s = do
--   (consEnb, et) <- _getPointer s . fccConstants <$> get
--   modify (fccPutConstants consEnb)
--   return et

openFunBlock :: String -> IDef.LType -> [(String, IDef.LType)] -> FCCompiler [(FCType, FCRegister)]
openFunBlock fname lret args =
  do
    fcc <- get
    let
      blockStates = [0]
      regst = fccRegEnv fcc
      varenv = VC.openClosure $ fccVenv fcc
      len = length args
      (rs, regst') = foldr
        (\((var, ltyp), i) (list,regst) ->
           let
             ityp :: FCType
             ityp = convert ltyp
             (regst', ereg) = _mapFCRValue (FCFunArg ityp fname i) regst
             reg = case ereg of
                     Left _ -> error "OpenFunBlock: FCFunArg musi być unique"
                     Right r -> r
           in
             (reg:list, regst'))
        ([], regst)
        (zip args [1..len])
      varenv' = foldl
        (\varenv (var, reg) -> VE.declareVar var reg varenv)
        varenv
        (zip (fst <$> args) rs)
    put (FCC varenv' regst' (fccConstants fcc) [0])
    return $ zip (map convert (snd <$> args)) rs

closeFunBlock :: FCCompiler ()
closeFunBlock = do
  fcc <- get
  let ve' = VE.closeClosure (fccVenv fcc)
      bc' = if null (fccBlocksCounts fcc) then error " " else tail (fccBlocksCounts fcc)
  checkVarEnv ve'
  checkBlocks bc'
  modify (fccPutVenv ve' . fccPutBlocksCounts bc')
  where
    checkVarEnv :: FCVarEnv -> FCCompiler ()
    checkVarEnv  (VE.VarEnv map s1 s2) = do
      when (length s1 /= 1) (error $ "Lenght of modified variables does not equals to 1: " ++ show (length s1))
      when (length s2 /= 1) (error $ "Lenght of redeclared variables does not equals to 1: " ++ show (length s2))
    checkBlocks :: [Int] -> FCCompiler ()
    checkBlocks list = unless (null list) (error $ "Length of ids should be 0 is: " ++ show (length list))

withOpenFunBlock :: String -> IDef.LType -> [(String, IDef.LType)] ->
  ([(FCType, FCRegister)] -> FCCompiler a) -> FCCompiler a
withOpenFunBlock s rt slts f = do
  r <- openFunBlock s rt slts
  result <- f r
  closeFunBlock
  return result


nextBlockName :: String -> Int ->BlockType -> String
nextBlockName blockname x bt =
  let
  btSuf = case bt of
    Normal -> ""
    BoolExp -> (show x) ++ "B"
    Cond -> (show x) ++ "I"
    While -> (show x) ++ "W"
    Check -> "C"
    Success -> "S"
    Failure -> "F"
    Post -> "P"
    _ -> error "nextBlockName: PartialFunction"
  in
    blockname ++ btSuf

-- getnextBlockNameM :: String -> BlockType -> FCCompiler String
-- getnextBlockNameM s bt = do
--   blocks <- gets fccBlocksCounts
--   when (null blocks) (error "Somehow blocks are malformed")
--   modify (fccPutBlocksCounts (1 + head blocks : tail blocks))
--   return $ nextBlockName s (head blocks) bt
--   where
--     increaseCounter = case bt of
--       BoolExp -> True
--       Cond -> True
--       While -> True
--       _ -> False


openBlock :: BlockType -> FCCompiler ()
openBlock bt = do
  fcc <- get
  let ve' = VE.openClosure $ fccVenv fcc
      fccbc = fccBlocksCounts fcc
      fccbc' =case bt of
        FunBody -> error "OpenBlock FunBody"
        Normal -> fccbc
        BoolExp -> (1 + head fccbc):tail fccbc
        Cond -> (1 + head fccbc):tail fccbc
        While -> (1 + head fccbc):tail fccbc
        Check -> 0:fccbc
        Success -> 0:fccbc
        Failure -> 0:fccbc
        Post -> 0:fccbc
        BTPlacceHolder -> error "OpenBlock PlaceHolder"
  modify (fccPutBlocksCounts fccbc' . fccPutVenv ve')

closeBlock :: BlockType -> FCCompiler ()
closeBlock bt = do
  fcc <- get
  let ve' = VE.closeClosure $ fccVenv fcc
      bc = fccBlocksCounts fcc
      bc' = case bt of
        FunBody -> error "OpenBlock FunBody"
        Normal -> bc
        BoolExp -> bc
        Cond -> bc
        While -> bc
        Check -> tail bc
        Success -> tail bc
        Failure -> tail bc
        Post -> tail bc
        BTPlacceHolder -> error "OpenBlock PlaceHolder"
  modify (fccPutVenv ve' . fccPutBlocksCounts bc')

withOpenBlock :: String -> BlockType -> (String -> FCCompiler a )-> FCCompiler a
withOpenBlock bname bt f = do
  blocks <- gets fccBlocksCounts
  openBlock bt
  let bname' = nextBlockName bname (head blocks) bt
  res <- f bname'
  closeBlock bt
  return res

protectVariables :: [String] -> FCCompiler ()
protectVariables vars = do
  ve <- fccVenv <$> get
  let ve' = foldl (\ve var ->
                   case VE.lookupVar var ve of
                     Just val -> VE.declareVar var val ve
                     Nothing -> ve)
          (VE.openClosure ve) vars
  modify (fccPutVenv ve')
protectVariablesWhile :: [String] -> FCCompiler ()
protectVariablesWhile = error "protectVariablesWhile: undefined"

endprotection :: FCCompiler ()
endprotection = do
  modify (\fcc -> fccPutVenv (VE.closeClosure $ fccVenv fcc) fcc)

withProtectedVars :: [String] -> FCCompiler a -> FCCompiler a
withProtectedVars vars f = do
  protectVariables vars
  res <- f
  endprotection
  return res

getBlockName :: FCCompiler String
getBlockName = error "GetBlockName: undefined case"
  -- do
  --   x <- gets f
  --   return $ case x of
  --     (BlockState name _ _ _ _):rest -> name
  --     (CondBlockState name _ _ _ _ _ _ _):rest -> name
  --     (WhileBlockState name _ _ _ _ _):rest -> name
      -- _ -> error "GetBlockName: undefined case"

getRegisterType :: FCRegister -- ^ 
  -> FCCompiler FCType
getRegisterType r = do
   rtype <- gets (_lookupRegister r . fccRegEnv)
   return $ case rtype of
             Just rtype -> (fCRValueType rtype)
             _ -> error "Could not find type of register"
getVar :: String -> FCCompiler (FCType, FCRegister)
getVar var = do
  mvalue <- gets (VE.lookupVar var . fccVenv)
  let value = error "GetVar: Could not find variable" `fromMaybe` mvalue
  rtype <- gets (_lookupRegister value . fccRegEnv)
  return $ case rtype of
             Just rtype -> (fCRValueType rtype, value)
             _ -> error "GetVar: Could not find type of Register"

setVar :: String -> FCRegister -> FCCompiler ()
setVar var value = do
  vars <- gets fccVenv
  modify $ fccPutVenv (VE.setVar var value vars)

declVar :: String -> FCRegister -> FCCompiler ()
declVar var value = do
  vars <- gets fccVenv
  modify $ fccPutVenv (VE.declareVar var value vars)

phi :: [String] -> (String, [FCRegister]) -> (String, [FCRegister]) -> FCCompiler ()
phi = undefined

