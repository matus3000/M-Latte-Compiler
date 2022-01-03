{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

-- TO DO:
-- a) Zamienić mapM getVar foldable na getVars
-- b) Sprawić, żeby return nie otrzymawało normalnego rejestru, tylko rejestr typu void.
-- c) Zmienić COND na CONDElse gdzie jedynyną instrukcją jest instrukcja pusta. W Translator.hs
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
import qualified VariableEnvironment as Ve


type FCVarEnv = VarEnv String FCRegister

data FCRegMap = FCRegMap {_regMap::VE.VarEnv FCRegister FCRValue,
                          _rvalueMap:: VE.VarEnv FCRValue FCRegister}

type SSARegisterAllocator = Int

ssaRegAllocNew :: SSARegisterAllocator
ssaRegAllocNew = 0

fcRegMapNew :: FCRegMap
fcRegMapNew = FCRegMap (VE.openClosure VE.newVarEnv) (VE.openClosure VE.newVarEnv)

-- regStNew :: RegSt
-- regStNew = RegSt {regMap = DM.empty ,
--                   rvalueMap=DM.empty,
--                   nextNormalId=0}

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
fccNew = FCC newVarEnv 0 fcRegMapNew ctcNew []
data FCC = FCC {fccVenv::FCVarEnv, fccSSAAloc::SSARegisterAllocator,
                fccRegMap::FCRegMap, fccConstants::CompileTimeConstants,
                fccBlocksCounts::[Int]}
type FCCompiler = State FCC
fccPutVenv :: FCVarEnv -> FCC -> FCC
fccPutVenv ve' (FCC ve ssa rm c b) = FCC ve' ssa rm c b
fccPutRegMap :: FCRegMap -> FCC -> FCC
fccPutRegMap re' (FCC ve ssa re c b) = FCC ve ssa re' c b
fccPutSSAAloc ssa' (FCC ve ssa re c b) = FCC ve ssa' re c b 
fccPutConstants :: CompileTimeConstants -> FCC -> FCC
fccPutConstants c' (FCC ve ssa re c b) = FCC ve ssa re c' b
fccPutBlocksCounts fbc' (FCC ve ssa re c fbc) = FCC ve ssa re c fbc'


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
          (bb', r)<- emplaceFCRValue phi bbNew
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
          (bb', r)<- emplaceFCRValue phi bbNew
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
          (b''', r) <- emplaceFCRValue (FCBinOp t1 op r1 r2) bb''
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
        (bb'', reg') <- emplaceFCRValue (FCUnOp ftype Neg reg) bb'
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
        (bb''', reg) <- emplaceFCRValue (FCBinOp ftype1 (convert iro) r1 r2) bb''
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

    x <- getBlockCount
    let ascmd = DS.toAscList md
        postEtStr = nextBlockName name x Post
        successEt = Et $ nextBlockName name x Success
        failureEt = Et $ nextBlockName name x Failure

    oldVals <- mapM getVar ascmd

    (cb, jr) <- withOpenBlock name Check $ (\name -> (do
                                                         (bb, (_, reg)) <- translateExpr name bbNew ie True
                                                         return (bbBuildAnonymous bb, reg)))

    (newVals, sb) <- withOpenBlock name Success $ (\name ->
                                                     withProtectedVars ascmd $ do
                                                      sbb <- translateBlock name iblock bbNew
                                                      newVal <- mapM getVar ascmd
                                                      let sbb' = bbaddInstr (VoidReg, jump postEtStr) sbb
                                                      return (newVal, bbBuildNamed sbb' name))

    fb <- withOpenBlock name Failure $ (\name -> do
                                           return $ bbBuildNamed (bbaddInstr (VoidReg, jump postEtStr) bbNew) name)

    pb <- withOpenBlock name Post $ \name -> (do
                                                 pbb <- phi (zip ascmd (zip newVals oldVals)) successEt failureEt
                                                 return (bbBuildNamed pbb name))

    return $ bbaddBlock (FCCondBlock name cb jr sb fb pb) bb
  Tr.ICondElse ie ib ib' (Tr.MD md) ->
    withOpenBlock name Cond $ \name -> do
    x <- getBlockCount
    let ascmd = DS.toAscList md
        postEtStr = nextBlockName name x Post
        successEt = Et $ nextBlockName name x Success
        failureEt = Et $ nextBlockName name x Failure


    (cb, jr) <- withOpenBlock name Check $ (\name -> (do
                                                         (bb, (_, reg)) <- translateExpr name bbNew ie True
                                                         return (bbBuildAnonymous bb, reg)))

    (sVals, sb) <- withOpenBlock name Success $ (\name ->
                                                     withProtectedVars ascmd $ do
                                                      sbb <- translateBlock name ib bbNew
                                                      sVal <- mapM getVar ascmd
                                                      let sbb' = bbaddInstr (VoidReg, jump postEtStr) sbb
                                                      return (sVal, bbBuildNamed sbb' name))

    (fVals, fb) <- withOpenBlock name Failure $ (\name ->
                                           withProtectedVars ascmd $ do
                                           sbb <- translateBlock name ib' bbNew
                                           fVals <- mapM getVar ascmd
                                           let sbb' = bbaddInstr (VoidReg, jump postEtStr) sbb
                                           return (fVals, bbBuildNamed sbb' name))

    pb <- withOpenBlock name Post $ \name -> (do
                                                 pbb <- phi (zip ascmd (zip sVals fVals)) successEt failureEt
                                                 return (bbBuildNamed pbb name))
    return $ bbaddBlock (FCCondBlock name cb jr sb fb pb) bb
  Tr.IWhile ie ib (Tr.MD md) -> withOpenBlock name While $ \wname -> do
    x <- getBlockCount
    let ascmd = DS.toAscList md
        postEtStr = nextBlockName wname x Post
        successEt = Et $ nextBlockName wname x Success
        postpostEtStr = postEtStr ++ "E"
    oldVals <- getVars ascmd
    reg_ft <- preallocRegisters (zip ascmd (map fst oldVals))


    (cb, jr)<- withOpenBlock wname Check $ \name -> do
      (bb, (_, reg)) <- translateExpr name bbNew ie True
      return (bbBuildNamed bb name, reg)

    (sVals, sb) <- withOpenBlock wname Success $
      \name ->
        withProtectedVars ascmd $ do
        sbb <- translateBlock name ib bbNew
        sVal <- mapM getVar ascmd
        let sbb' = bbaddInstr (VoidReg, jump postEtStr) sbb
        return (sVal, bbBuildNamed sbb' name)
        
    pb <- withOpenBlock wname Post $ \name -> do
      regenv <- gets fccRegMap
      let x = zip reg_ft (zip oldVals sVals)
          (regenv', bb) = foldl (\(regenv, bb) ((r, t), ((_, sr), (_, fr))) ->
                                   let phiValue = FCPhi t [(sr, successEt), (fr, Et wname)]
                                   in
                                     (_setOnlyRValue phiValue r regenv,
                                     bbaddInstr (r, phiValue) bb))
                          (regenv, bbNew) x
      modify (fccPutRegMap regenv')
      return (bbBuildNamed bb name)

    return $ bbaddBlock (FCWhileBlock wname pb cb jr sb) bb
    where
      preallocRegisters :: [(String, FCType)] -> FCCompiler [(FCRegister, FCType)]
      preallocRegisters names = do
        fcc <- get
        let venv = fccVenv fcc
            (ssaa', regmap', venv', list) = foldl
              (\(ssaa, regmap, venv, list) (var, rtype) -> let
                  (ssaa', r') = _nextRegister ssaa
                  venv' = VE.setVar var r' venv
                  regmap' = _setOnlyRegister r' (FCPhi rtype []) regmap
                  in
                  (ssaa', regmap', venv', (r', rtype):list)) (fccSSAAloc fcc, fccRegMap fcc, venv, []) names
        modify (fccPutSSAAloc ssaa' . fccPutVenv venv . fccPutRegMap regmap')
        return list

  Tr.ISExp ie -> fst <$> translateExpr' bb ie False
  Tr.IStmtEmpty -> return bb
  where
    translateIItem' = flip $ translateIItem name
    translateExpr' = translateExpr name
    translateInstr' = translateInstr name bb
    phi :: [(String,((FCType, FCRegister),(FCType, FCRegister)))] -> FCRegister -> FCRegister -> FCCompiler BlockBuilder
    phi list successEt failureEt = foldlM (\bb (var, ((st, sval),(ft, fval))) ->
                         do
                           (bb, r) <- emplaceFCRValue
                                      (FCPhi ft [(sval, successEt), (fval, failureEt)]) bb
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

_nextRegister :: SSARegisterAllocator -> (SSARegisterAllocator, FCRegister)
_nextRegister x = (x+1, Reg (show x))

_setOnlyRegister :: FCRegister -> FCRValue -> FCRegMap ->  FCRegMap
_setOnlyRegister reg val (FCRegMap rmap rvmap) = FCRegMap (VE.declareVar reg val rmap) rvmap
_setOnlyRValue :: FCRValue -> FCRegister -> FCRegMap ->  FCRegMap
_setOnlyRValue val reg (FCRegMap rmap rvmap) = FCRegMap rmap (VE.declareVar val reg rvmap)
_putRegisterValue :: FCRegister -> FCRValue -> FCRegMap -> FCRegMap
_putRegisterValue reg val (FCRegMap rmap rvmap)  = FCRegMap (VE.declareVar reg val rmap) (VE.declareVar  val reg rvmap)
_redeclareRegisterValue reg val (FCRegMap rmap rvmap) = FCRegMap (VE.setVar reg val rmap) (VE.setVar val reg rvmap)
_lookupRValue :: FCRValue -> FCRegMap -> Maybe FCRegister
_lookupRValue rval (FCRegMap _ rvalueMap) = VE.lookupVar rval rvalueMap
_lookupRegister reg (FCRegMap rmap _) = VE.lookupVar reg rmap
_mapFCRValue :: FCRValue -> SSARegisterAllocator -> FCRegMap -> ((SSARegisterAllocator, FCRegMap), Either FCRegister FCRegister )
_mapFCRValue fcrValue ssa regmap = case fcrValue `_lookupRValue` regmap of
    Nothing -> let
      (ssa', r) = _nextRegister ssa
      regmap' = _putRegisterValue r fcrValue regmap
      in
      ((ssa', regmap'), Right r)
    Just r -> ((ssa, regmap), Left r)

_openClosureRM :: FCRegMap -> FCRegMap
_openClosureRM (FCRegMap regmap rvalmap) = FCRegMap (VE.openClosure  regmap) (VE.openClosure rvalmap)
_closeClosureRM  :: FCRegMap -> FCRegMap
_closeClosureRM (FCRegMap regmap rvalmap) = FCRegMap (VE.closeClosure  regmap) (VE.closeClosure rvalmap)

instance ConstantsEnvironment CompileTimeConstants String String where
  _getPointer str ctc@(CTC cmap next) = case DM.lookup str cmap of
      Just v -> (ctc, v)
      Nothing -> (CTC (DM.insert str ("C" ++ show next) cmap ) (next + 1), "C" ++ show next)

emplaceFCRValue :: FCRValue -> BlockBuilder -> FCCompiler (BlockBuilder, FCRegister)
emplaceFCRValue rvalue bb = do
  fcc <- get
  let ((ssa,regmap), r) = _mapFCRValue rvalue (fccSSAAloc fcc) (fccRegMap fcc)
  case r of
    Left r' -> return (bb, r')
    Right r' -> modify (fccPutRegMap regmap . fccPutSSAAloc ssa) >> return (bbaddInstr (r', rvalue) bb, r')

-- getConstStringEt :: String -> FCCompiler String
-- getConstStringEt s = do
--   (consEnb, et) <- _getPointer s . fccConstants <$> get
--   modify (fccPutConstants consEnb)
--   return et

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


openFunBlock :: String -> IDef.LType -> [(String, IDef.LType)] -> FCCompiler [(FCType, FCRegister)]
openFunBlock fname lret args =
  do
    fcc <- get
    let
      blockStates = [0]
      regst = fccRegMap fcc
      ssa = fccSSAAloc fcc
      varenv = VC.openClosure $ fccVenv fcc
      len = length args
      (rs, ssa', regst') = foldr
        (\((var, ltyp), i) (list, ssa, regst) ->
           let
             ityp :: FCType
             ityp = convert ltyp
             ((ssa', regst'), ereg) = _mapFCRValue (FCFunArg ityp fname i) ssa regst
             reg = case ereg of
                     Left _ -> error "OpenFunBlock: FCFunArg musi być unique"
                     Right r -> r
           in
             (reg:list, ssa', regst'))
        ([], ssa, regst)
        (zip args [1..len])
      varenv' = foldl
        (\varenv (var, reg) -> VE.declareVar var reg varenv)
        varenv
        (zip (fst <$> args) rs)
    put (FCC varenv' ssa' regst' (fccConstants fcc) [0])
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

openBlock :: BlockType -> FCCompiler ()
openBlock bt = do
  fcc <- get
  let ve = fccVenv fcc
      re = fccRegMap fcc
      fccbc = fccBlocksCounts fcc
      re' = _openClosureRM re
      (ve',re'', fccbc') =case bt of
        FunBody -> error "OpenBlock FunBody"
        Normal -> (VE.openClosure ve,re,fccbc)
        BoolExp -> (VE.openClosure ve, re, (1 + head fccbc):tail fccbc)
        Cond -> (VE.openClosure ve, re, (1 + head fccbc):tail fccbc)
        While -> (VE.openClosure ve, re, (1 + head fccbc):tail fccbc)
        Check -> (VE.openClosure ve, re, 0:fccbc)
        Success -> (VE.openClosure ve, re', 0:fccbc)
        Failure -> (VE.openClosure ve, re', 0:fccbc)
        Post -> (VE.openClosure ve, re,  0:fccbc)
        BTPlacceHolder -> error "OpenBlock PlaceHolder"
  modify (fccPutBlocksCounts fccbc' . fccPutVenv ve' . fccPutRegMap re'')

closeBlock :: BlockType -> FCCompiler ()
closeBlock bt = do
  fcc <- get
  let
    ve = fccVenv fcc
    bc = fccBlocksCounts fcc
    re = fccRegMap fcc
    (ve', re', bc') = case bt of
        FunBody -> error "OpenBlock FunBody"
        Normal -> (VE.closeClosure ve, re, bc)
        BoolExp -> (VE.closeClosure ve, re, bc)
        Cond -> (VE.closeClosure ve, re, bc)
        While -> (VE.closeClosure ve, re, bc)
        Check -> (VE.closeClosure ve, re, tail bc)
        Success -> (VE.closeClosure ve, _closeClosureRM re, tail bc)
        Failure -> (VE.closeClosure ve, _closeClosureRM re, tail bc)
        Post -> (VE.closeClosure ve, re, tail bc)
        BTPlacceHolder -> error "OpenBlock PlaceHolder"
  modify (fccPutVenv ve' . fccPutBlocksCounts bc' . fccPutRegMap re')

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

getBlockCount :: FCCompiler Int
getBlockCount = do
  blockCounts <- gets fccBlocksCounts
  case blockCounts of
    [] -> error "BlockCounts is empty"
    (x:xs) -> return x

unpackMaybe :: Maybe a -> a
unpackMaybe x = error "Expected Just got Nothing" `fromMaybe` x

_getRegisterType :: FCRegister -> FCRegMap -> Maybe FCType
_getRegisterType reg regenv = case reg of
  VoidReg -> Just Void
  Reg _ -> x reg regenv
  DReg n -> error "This one is not neeed"
  LitInt n -> Just Int
  LitBool b -> Just Bool
  Et s -> Just Void
  where
    x :: FCRegister -> FCRegMap -> Maybe FCType
    x r regenv= fCRValueType <$> _lookupRegister r regenv

getRegisterType :: FCRegister -- ^ 
  -> FCCompiler FCType
getRegisterType r = do
  x <- _getRegisterType r <$> gets fccRegMap
  return $ unpackMaybe x

getVar :: String -> FCCompiler (FCType, FCRegister)
getVar var = do
  mvalue <- gets (VE.lookupVar var . fccVenv)
  let reg = unpackMaybe mvalue
  rtype<- getRegisterType reg
  return (rtype, reg)

getVars :: [String] -> FCCompiler [(FCType, FCRegister)]
getVars  = mapM getVar

setVar :: String -> FCRegister -> FCCompiler ()
setVar var value = do
  vars <- gets fccVenv
  modify $ fccPutVenv (VE.setVar var value vars)

declVar :: String -> FCRegister -> FCCompiler ()
declVar var value = do
  vars <- gets fccVenv
  modify $ fccPutVenv (VE.declareVar var value vars)
