{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

-- TO DO:
-- a) Zamienić mapM getVar foldable na getVars
-- b) Sprawić, żeby return nie otrzymawało normalnego rejestru, tylko rejestr typu void.
module FCCompiler where

import Prelude

import Data.Maybe (fromMaybe, maybeToList)
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import Control.Monad.State.Strict
import Control.Monad.Except (Except, MonadError)

import Translator(CompilerExcept, Convertable(..))
import FCCompilerTypes as FCT
import qualified Translator as Tr
import qualified Data.Functor
import FCCompilerState (VariableEnvironment(..),
                        ConstantsEnvironment(..))
import FCCompilerTypes (FCRValue(FCEmptyExpr, FCPhi), FCRegister(..),
                        FCType(..),
                        FCBlock(..))
import VariableEnvironment(VarEnv(..), newVarEnv)
import qualified VariableEnvironment as VE
import qualified IDefinition as IDef
import Data.Foldable (foldlM, foldl', foldrM)
import qualified VariableEnvironment as VC
import qualified Control.Arrow as BiFunctor
import qualified VariableEnvironment as Ve
import Control.Monad.Reader (ReaderT (runReaderT), asks, ask)
import Data.List (nub)
import Gsce (gcseOptimize)
import DeadCodeRemoval (removeDeadCode)

externalFunctions :: [([Char], (FCType, [FCType]))]
externalFunctions = [("printString", (Void, [DynamicStringPtr])),
                     ("printInt", (Void, [Int])),
                     ("error", (Void, [])),
                     ("readInt", (Int, [])),
                     ("readString", (DynamicStringPtr, [])),
                     ("_strconcat", (DynamicStringPtr, [DynamicStringPtr, DynamicStringPtr])),
                     ("_strle", (Bool, [DynamicStringPtr, DynamicStringPtr])),
                     ("_strlt", (Bool, [DynamicStringPtr, DynamicStringPtr])),
                      ("_strge", (Bool, [DynamicStringPtr, DynamicStringPtr])),
                      ("_strgt", (Bool, [DynamicStringPtr, DynamicStringPtr])),
                      ("_streq", (Bool, [DynamicStringPtr, DynamicStringPtr])),
                      ("_strneq", (Bool, [DynamicStringPtr, DynamicStringPtr]))]

type FCVarEnv = VarEnv String FCRegister

data FCRegMap = FCRegMap {_regMap::VE.VarEnv FCRegister FCRValue,
                          _rvalueMap:: VE.VarEnv FCRValue FCRegister}

type SSARegisterAllocator = Int

data LabelAllocator = LA {laNextId::Int, laNameRequired::Bool}

laNew :: LabelAllocator
laNew = LA 0 False
laNextLabel :: LabelAllocator -> (LabelAllocator, String)
laNextLabel la = (LA (1+laNextId la) False, "L" ++ show (laNextId la))
laLookupNextLabel :: LabelAllocator -> (LabelAllocator, String)
laLookupNextLabel la = (LA (laNextId la) True, "L" ++ show (laNextId la))

ssaRegAllocNew :: SSARegisterAllocator
ssaRegAllocNew = 0

fcRegMapNew :: FCRegMap
fcRegMapNew = FCRegMap (VE.openClosure VE.newVarEnv) (VE.openClosure VE.newVarEnv)

data CompileTimeConstants = CTC {constMap :: DM.Map String Int,
                                 nextEtId :: Int}
ctcNew = CTC DM.empty 0
ctcEmplaceString :: String -> CompileTimeConstants -> (CompileTimeConstants, FCRegister)
ctcEmplaceString str ctc = case str `DM.lookup` constMap ctc of
  Just x -> (ctc, ConstString x)
  Nothing -> (ctc', ConstString x')
    where
      x' = nextEtId ctc
      ctc' = CTC (DM.insert str (nextEtId ctc) (constMap ctc)) (1 + nextEtId ctc)


data BlockBuilder = BB {instrAcc::[FCInstr], subBlockName:: String,  blockAcc::[FCBlock]}

bbaddBlock :: FCBlock -> BlockBuilder -> BlockBuilder
bbaddBlock block bb = case (instrAcc bb, subBlockName bb) of
  ([], "") -> BB [] "" (block:blockAcc bb)
  -- ([], str) -> error "I haven't thought out that one yet."
  (list, str) -> BB [] "" (block:FCNamedSBlock str (reverse list) ():blockAcc bb)

bbaddInstr :: FCInstr -> BlockBuilder -> BlockBuilder
bbaddInstr instr bb = BB (instr:instrAcc bb) (subBlockName bb) (blockAcc bb)
bbBuildAnonymous :: BlockBuilder -> FCBlock
bbBuildAnonymous = flip bbBuildNamed ""
bbBuildNamed :: BlockBuilder -> String  -> FCBlock
bbBuildNamed bb name = let
  instrs = instrAcc bb
  blocks = blockAcc bb
  subName = subBlockName bb
  in
  if null blocks && subName /= "" && name /= ""
  then error $ "Malformed BlockBuilder subName:" ++
         subName ++ " name: " ++ name
  else
    case (instrs, blocks) of
      ([], []) -> FCComplexBlock name [] ()
      ([], [block]) -> case block of
        (FCNamedSBlock "" fcabi _)-> FCNamedSBlock name fcabi ()
        _ -> FCComplexBlock name [block] ()
      ([], blocks) -> FCComplexBlock name (reverse blocks) ()
      (instrs, blocks) -> FCComplexBlock name (reverse $
                                               (FCNamedSBlock
                                               (subBlockName bb)
                                                (reverse instrs) ()):blocks) ()
bbNew :: BlockBuilder
bbNew = BB [] "" []

fccNew :: FCC
fccNew = FCC newVarEnv 0 fcRegMapNew ctcNew laNew
data FCC = FCC {fccVenv::FCVarEnv, fccSSAAloc::SSARegisterAllocator,
                fccRegMap::FCRegMap, fccConstants::CompileTimeConstants,
                fccLabelAlloc::LabelAllocator}

type FCCStateMonad = State FCC
type FCCompiler = ReaderT FCCFunEnv FCCStateMonad

fccPutVenv :: FCVarEnv -> FCC -> FCC
fccPutVenv ve' (FCC ve ssa rm c b) = FCC ve' ssa rm c b
fccPutRegMap :: FCRegMap -> FCC -> FCC
fccPutRegMap re' (FCC ve ssa re c b) = FCC ve ssa re' c b
fccPutSSAAloc ssa' (FCC ve ssa re c b) = FCC ve ssa' re c b
fccPutConstants :: CompileTimeConstants -> FCC -> FCC
fccPutConstants c' (FCC ve ssa re c b) = FCC ve ssa re c' b
fccPutLabelAlloc fbc' (FCC ve ssa re c fbc) = FCC ve ssa re c fbc'


translateAndExpr :: String -> BlockBuilder -> Tr.IExpr -> Bool -> FCCompiler (BlockBuilder, (FCType, FCRegister))
translateAndExpr bn bb (Tr.IAnd (ie:ies)) save =
  g bn bb ie ies
  where
    g :: String-> BlockBuilder ->Tr.IExpr -> [Tr.IExpr] -> FCCompiler (BlockBuilder, (FCType, FCRegister))
    g bname bb ie rest = do
      withOpenBlock BoolExp $ \bname -> do

        list <- generateLabels 4
        let [successEt, failureEt, finalSuccessEt, postEt] = list


        (cb, (_, jreg)) <- withOpenBlock Check $ \bname ->
          BiFunctor.first bbBuildAnonymous <$> translateExpr bname bbNew  ie True

        (sb, sreg) <- withPrenamedOpenBlock successEt Success $
          \bname -> do
            (successBlock, reg) <- f "" bbNew ies (failureEt, finalSuccessEt)
            let sb' = flip bbBuildNamed bname $ bbaddBlock (flip bbBuildNamed finalSuccessEt $
                                 bbaddInstr (VoidReg, jump postEt) bbNew)
                      (bbaddBlock successBlock bbNew)
                  
            return (sb', reg)

        (fb, (_, _)) <- withPrenamedOpenBlock failureEt Failure $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump postEt) bbNew) bname,
                  (Void, VoidReg))

        (pb, res) <- withPrenamedOpenBlock postEt Post $ \bname -> do
          let phi = FCPhi Bool [(sreg, Et finalSuccessEt), (LitBool False, Et failureEt)]
          (bb', r)<- emplaceFCRValue phi bbNew
          return (bbBuildNamed bb' bname, r)

        let returnBlock = FCCondBlock bname cb jreg sb fb pb ()
        return (bbaddBlock returnBlock bb, (Bool, res))

    f :: String -> BlockBuilder -> [Tr.IExpr] -> (String, String) -> FCCompiler (FCBlock, FCRegister)
    f bn bb [ie] (_, postEt) = do
      withPrenamedOpenBlock bn Normal $ \bname -> do
        (cbb, (ftype, reg)) <- translateExpr bname bbNew  ie True -- Można zmienić na BIFunctor
        return (bbBuildNamed (bbaddInstr (VoidReg, jump postEt) cbb) bname, reg)
    f bn bb (ie:rest) (failureEt, postEt) = do

        (cb, (_, jreg)) <- withOpenBlock Check $ \bname ->
          (bbBuildAnonymous `BiFunctor.first`) <$> translateExpr bname bbNew  ie True

        (sb, r) <- withOpenBlock Success $ \bname -> do
          f bname bbNew rest (failureEt, postEt)

        (fb, (_, _)) <- withOpenBlock Failure $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump failureEt) bbNew) bname, (Void, VoidReg))

        let returnBlock = FCPartialCond bn cb jreg sb fb ()

        return (returnBlock, r)
translateOrExpr :: String -> BlockBuilder -> Tr.IExpr -> Bool
  -> FCCompiler (BlockBuilder, (FCType, FCRegister))
translateOrExpr bn bb (Tr.IOr (ie:ies)) save =
  g bn bb ie ies
  where
    g :: String-> BlockBuilder ->Tr.IExpr -> [Tr.IExpr] -> FCCompiler (BlockBuilder, (FCType, FCRegister))
    g bname bb ie rest = do
      withOpenBlock BoolExp $ \bname -> do

        list <- generateLabels 4
        let [successEt, failureEt, finalFailure, postEt] = list

        (cb, (_, jreg)) <- withOpenBlock Check $ \bname ->
          BiFunctor.first bbBuildAnonymous <$> translateExpr bname bbNew  ie True

        (sb, (_, _)) <- withPrenamedOpenBlock successEt Success $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump postEt) bbNew) bname,
                  (Void, VoidReg))

        (fb, sreg) <- withPrenamedOpenBlock failureEt Failure $
          \bname -> do
            (failure, sreg) <- f "" bbNew ies (successEt, finalFailure)
            let fb' = flip bbBuildNamed bname $ bbaddBlock (flip bbBuildNamed finalFailure $
                                                     bbaddInstr (VoidReg, jump postEt) bbNew)
                      (bbaddBlock failure bbNew)
            return (fb', sreg)

        (pb, res) <- withPrenamedOpenBlock postEt Post $ \bname -> do
          let phi = FCPhi Bool [(LitBool True, Et successEt), (sreg, Et finalFailure)]
          (bb', r)<- emplaceFCRValue phi bbNew
          return (bbBuildNamed bb' bname, r)

        let returnBlock = FCCondBlock bname cb jreg sb fb pb ()
        return (bbaddBlock returnBlock bb, (Bool, res))

    f :: String -> BlockBuilder -> [Tr.IExpr] -> (String, String) -> FCCompiler (FCBlock, FCRegister)
    f bn bb [ie] (_, postEt) = do
      withPrenamedOpenBlock bn Normal $ \bname -> do
        (cbb, (ftype, reg)) <- translateExpr bname bbNew  ie True -- Można zmienić na BIFunctor
        return (bbBuildNamed (bbaddInstr (VoidReg, jump postEt) cbb) bname, reg)

    f bn bb (ie:rest) (successEt, postEt) = do

        (cb, (_, jreg)) <- withOpenBlock Check $ \bname ->
          (bbBuildAnonymous `BiFunctor.first`) <$> translateExpr bname bbNew  ie True

        (sb, (_, _)) <- withOpenBlock Success $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump successEt) bbNew) bname, (Void, VoidReg))

        (fb, r) <- withOpenBlock Failure $ \bname -> do
          f bname bbNew rest (successEt, postEt)

        let returnBlock = FCPartialCond bn cb jreg sb fb ()

        return (returnBlock, r)


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
      Tr.IString s -> do
         constEt <- getConstStringReg s
         (bb',r) <- emplaceFCRValue (BitCast (ConstStringPtr (1 + length s))
                                           constEt DynamicStringPtr) bb
         return (bb', (DynamicStringPtr, r))
      Tr.IVar s -> (bb, ) <$> getVar s
      addInstr@(Tr.IAdd iao ie ie') -> translateExprAddMull addInstr bb save
      mulInstr@(Tr.IMul imo ie ie') -> translateExprAddMull mulInstr bb save
      Tr.INeg ie ->  do
        (bb', (ftype, reg)) <- translateExpr' bb ie True
        (bb'', reg') <- emplaceFCRValue (FCUnOp ftype Neg reg) bb'
        return (bb'', (ftype, reg'))
      Tr.INot ie -> case ie of
        Tr.INot ie' -> undefined -- translateExpr bname bb ie' save
        _ -> do
          labels <- generateLabels 3
          ssa <- gets fccSSAAloc
          let [post, success, failure] = labels
              phirval=FCPhi Bool [((LitBool False), Et success), ((LitBool True), Et failure)]
              (ssa', newReg) = _nextRegister ssa
          modify $ fccPutSSAAloc ssa'
          
          (bb', (_, reg)) <- translateExpr bname bbNew ie True

          let res = FCCondBlock "" (bbBuildAnonymous bb') reg (FCNamedSBlock success [(VoidReg, jump post)] ())
                    (FCNamedSBlock failure [(VoidReg, jump post)] ()) (FCNamedSBlock post [(newReg, phirval)] ()) ()
          return (bbaddBlock res bb, (Bool, newReg))
      Tr.IAnd _ -> do
        translateAndExpr bname bb ie True
      Tr.IOr _ -> do
        translateOrExpr bname bb ie True
      Tr.IApp fun ies -> do
        (bb', rargs) <- foldlM
          (\(bb, acc) ie -> BiFunctor.second (:acc) <$> translateExpr' bb ie True)
          (bb,[])
          ies
        rtype <- askFunType fun
        let args = reverse rargs
        (bb, reg)<- emplaceFCRValue (FunCall rtype fun args) bb'
        return (bb, (rtype, reg))


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
  Tr.ICondElse ie ib ib' (Tr.MD md) ->
    case ie of
      Tr.INot ie' -> translateInstr name bb (Tr.ICondElse ie' ib' ib (Tr.MD md))
      _ ->
        withOpenBlock Cond $ \name -> do
        labels <- generateLabels 3
        let ascmd = DS.toAscList md
            [postLabel, successLabel, failureLabel] = labels
            successEt = Et successLabel
            failureEt = Et failureLabel


        (cb, jr) <- withOpenBlock  Check $ (\name -> (do
                                                         (bb, (_, reg)) <- translateExpr name bbNew ie True
                                                         return (bbBuildAnonymous bb, reg)))

        (sVals, sb) <- withPrenamedOpenBlock successLabel Success $ (\name ->
                                                     withProtectedVars ascmd $ do
                                                      sbb <- translateBlock name ib bbNew
                                                      sVal <- mapM getVar ascmd
                                                      let sbb' = bbaddInstr (VoidReg, jump postLabel) sbb
                                                      return (sVal, bbBuildNamed sbb' name))

        (fVals, fb) <- withPrenamedOpenBlock failureLabel Failure $ (\name ->
                                           withProtectedVars ascmd $ do
                                           sbb <- translateBlock name ib' bbNew
                                           fVals <- mapM getVar ascmd
                                           let sbb' = bbaddInstr (VoidReg, jump postLabel) sbb
                                           return (fVals, bbBuildNamed sbb' name))

        pb <- withPrenamedOpenBlock postLabel Post $ \name -> (do
                                                 pbb <- phi (zip ascmd (zip sVals fVals)) successEt failureEt
                                                 return (bbBuildNamed pbb name))
        return $ bbaddBlock (FCCondBlock name cb jr sb fb pb ()) bb
  Tr.IWhile ie ib (Tr.MD md) -> withOpenBlock While $ \wname -> do
    labels <- generateLabels 4
    let [postEtStr, checkEtStr, successEndStr, epilogueEndStr] = labels
        ascmd = DS.toAscList md

    oldVals <- mapM getVar ascmd
    reg_ft <- preallocRegisters (zip ascmd (map fst oldVals))
    setVars ascmd (map fst reg_ft)

    (sVals, sb) <- withOpenBlock Success $
      \name ->
        withProtectedVars ascmd $ do
        sbb <- translateBlock name ib bbNew
        sVal <- getVars ascmd
        let sbb' = bbaddInstr (VoidReg, jump successEndStr) sbb
            epilogue = bbBuildNamed (bbaddInstr (VoidReg, jump postEtStr) bbNew) successEndStr
            sbb'' = bbaddBlock epilogue sbb'

        return (sVal, bbBuildNamed sbb'' name)

    (cb, jr)<- withPrenamedOpenBlock checkEtStr Check $ \name -> do
      (bb, (_, reg)) <- translateExpr name bbNew ie True
      return (bbBuildNamed bb name, reg)

    let successEt = Et $ bname sb

    pb <- withPrenamedOpenBlock postEtStr Post $ \name -> do
      regenv <- gets fccRegMap
      let x = zip reg_ft (zip sVals oldVals)
          (regenv', bb) = foldl (\(regenv, bb) ((r, t), ((_, sr), (_, fr))) ->
                                   let phiValue = FCPhi t [(sr, Et successEndStr), (fr, Et wname)]
                                   in
                                     (_setOnlyRValue phiValue r regenv,
                                     bbaddInstr (r, phiValue) bb))
                          (regenv, bbNew) x
      modify (fccPutRegMap regenv')
      return (bbBuildNamed bb name)

    return $ bbaddBlock (FCNamedSBlock epilogueEndStr [] ()) (bbaddBlock (FCWhileBlock wname pb cb jr sb epilogueEndStr ()) bb)
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
        return (reverse list)

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
  withOpenBlock Normal $ (\blockName ->foldlM (translateInstr blockName) rest stmts)

translateFun :: Tr.IFun -> FCCompiler FCFun
translateFun (Tr.IFun s lt lts ib) = do
  withOpenFunBlock s lt lts $ \res ->
    do
      fbodyBB <- translateBlock s ib bbNew
      dynamicFuns <- asks fccfeDynamicFuns
      let
        optimize :: FCBlock -> FCBlock
        optimize = snd . removeDeadCode dynamicFuns DS.empty
        -- optimize=id
        fbody = bbBuildAnonymous fbodyBB
        fbody' = optimize fbody
      return $ FCFun' {name = s, retType = convert lt, args = res, FCT.body = fbody'}


translateProg :: [Tr.IFun] -> FCCompiler [FCFun]
translateProg list = do
  fbodies <- mapM
    ( \ifun ->
        do
          translateFun ifun
    ) list
  return fbodies

compileProg :: [Tr.IFun] -> FCProg
compileProg ifun = let
  funMetadata = Tr.functionMetaDataNew ifun
  _usedExternals = foldr (\r -> (if fst r `DS.member` Tr.usedExternal funMetadata
                                then (r:)
                                else id))
                  [] externalFunctions
  _ftypeMapInit = DM.fromList (map (BiFunctor.second fst) externalFunctions)
  _ftypeMap :: DM.Map String FCType
  _ftypeMap = foldl' (\map (Tr.IFun fname ltype _ _) -> DM.insert fname (convert ltype) map) _ftypeMapInit ifun
  funEnv = FCCFE _ftypeMap (Tr.dynamicFunctions funMetadata)
  (funBodies, a) = runState (runReaderT (translateProg ifun) funEnv) initialFcc
  constants :: [(FCRegister, String)]
  constants = DM.foldrWithKey (\ string i -> ((ConstString i, string):)) [] (constMap $ fccConstants a)
  in
    FCProg _usedExternals constants funBodies
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
      (ssa', r) = if (fCRValueType fcrValue == Void) then (ssa, VoidReg) else _nextRegister ssa
      regmap' = if (r == VoidReg) then regmap else _putRegisterValue r fcrValue regmap
      in
      ((ssa', regmap'), Right r)
    Just r -> ((ssa, regmap), Left r)

_openClosureRM :: FCRegMap -> FCRegMap
_openClosureRM (FCRegMap regmap rvalmap) = FCRegMap regmap (VE.openClosure rvalmap)
_closeClosureRM  :: FCRegMap -> FCRegMap
_closeClosureRM (FCRegMap regmap rvalmap) = FCRegMap regmap (VE.closeClosure rvalmap)

emplaceFCRValue :: FCRValue -> BlockBuilder -> FCCompiler (BlockBuilder, FCRegister)
emplaceFCRValue rvalue bb = do
  case rvalue of
    FunCall ft fname x0 -> do
      dynamicFun <- not <$> isFunStatic fname
      if dynamicFun
        then g rvalue bb
        else f rvalue bb
    _ -> f rvalue bb
  where
    f :: FCRValue -> BlockBuilder -> FCCompiler (BlockBuilder, FCRegister)
    f rvalue bb = do
      fcc <- get
      let ((ssa,regmap), r) = _mapFCRValue rvalue (fccSSAAloc fcc) (fccRegMap fcc)
      case r of
        Left r' -> return (bb, r')
        Right r' -> modify (fccPutRegMap regmap . fccPutSSAAloc ssa) >> return (bbaddInstr (r', rvalue) bb, r')
    g :: FCRValue -> BlockBuilder -> FCCompiler (BlockBuilder, FCRegister)
    g rvalue bb = do
      fcc <- get
      let ssa = fccSSAAloc fcc
          regmap = fccRegMap fcc
          (ssa', r) = if fCRValueType rvalue == Void then (ssa, VoidReg ) else _nextRegister ssa
          regmap' = _setOnlyRegister r rvalue regmap
      modify (fccPutRegMap regmap' . fccPutSSAAloc ssa')
      return (bbaddInstr (r, rvalue) bb, r)


getConstStringReg :: String -> FCCompiler FCRegister
getConstStringReg s = do
  (consEnb, et) <- ctcEmplaceString s . fccConstants <$> get
  modify (fccPutConstants consEnb)
  return et

openFunBlock :: String -> IDef.LType -> [(String, IDef.LType)] -> FCCompiler [(FCType, FCRegister)]
openFunBlock fname lret args =
  do
    fcc <- get
    let
      blockStates = [0]
      (FCRegMap regval valreg) = fccRegMap fcc
      regst = _openClosureRM (FCRegMap (VE.openClosure VE.newVarEnv) valreg)
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
    put (FCC varenv' ssa' regst' (fccConstants fcc) (fccLabelAlloc fcc))
    return $ zip (map convert (snd <$> args)) rs

closeFunBlock :: FCCompiler ()
closeFunBlock = do
  fcc <- get
  let ve' = VE.closeClosure (fccVenv fcc)
      regmap' = _closeClosureRM (fccRegMap fcc)
  checkVarEnv ve'
  modify $ fccPutVenv ve' . fccPutRegMap regmap'
  where
    checkVarEnv :: FCVarEnv -> FCCompiler ()
    checkVarEnv  (VE.VarEnv map s1 s2) = do
      when (length s1 /= 1) (error $ "Lenght of modified variables does not equals to 1: " ++ show (length s1))
      when (length s2 /= 1) (error $ "Lenght of redeclared variables does not equals to 1: " ++ show (length s2))

withOpenFunBlock :: String -> IDef.LType -> [(String, IDef.LType)] ->
  ([(FCType, FCRegister)] -> FCCompiler a) -> FCCompiler a
withOpenFunBlock s rt slts f = do
  r <- openFunBlock s rt slts
  result <- f r
  closeFunBlock
  return result


openBlock :: BlockType -> FCCompiler ()
openBlock bt = do
  fcc <- get
  let ve = fccVenv fcc
      re = fccRegMap fcc
      la = fccLabelAlloc fcc
      re' = _openClosureRM re
      (ve',re'') =case bt of
        FunBody -> error "OpenBlock FunBody"
        Normal -> (VE.openClosure ve,re)
        BoolExp -> (VE.openClosure ve, re)
        Cond -> (VE.openClosure ve, re)
        While -> (VE.openClosure ve, re)
        Check -> (VE.openClosure ve, re)
        Success -> (VE.openClosure ve, re')
        Failure -> (VE.openClosure ve, re')
        Post -> (VE.openClosure ve, re)
        BTPlacceHolder -> error "OpenBlock PlaceHolder"
  modify (fccPutVenv ve' . fccPutRegMap re'')

closeBlock :: BlockType -> FCCompiler ()
closeBlock bt = do
  fcc <- get
  let
    ve = fccVenv fcc
    re = fccRegMap fcc
    (ve', re') = case bt of
        FunBody -> error "OpenBlock FunBody"
        Normal -> (VE.closeClosure ve, re)
        BoolExp -> (VE.closeClosure ve, re)
        Cond -> (VE.closeClosure ve, re)
        While -> (VE.closeClosure ve, re)
        Check -> (VE.closeClosure ve, re)
        Success -> (VE.closeClosure ve, _closeClosureRM re)
        Failure -> (VE.closeClosure ve, _closeClosureRM re)
        Post -> (VE.closeClosure ve, re)
        BTPlacceHolder -> error "OpenBlock PlaceHolder"
  modify (fccPutVenv ve' . fccPutRegMap re')

withPrenamedOpenBlock :: String -> BlockType -> (String -> FCCompiler a )-> FCCompiler a
withPrenamedOpenBlock bname bt f = do
  openBlock bt
  res <- f bname
  closeBlock bt
  return res

withOpenBlock :: BlockType -> (String -> FCCompiler a )-> FCCompiler a
withOpenBlock bt f = do
  bname <- nextBlockName
  withPrenamedOpenBlock bname bt f
  where
    nextBlockName :: FCCompiler String
    nextBlockName = do
      la <- gets fccLabelAlloc
      let (la', str) =
            if laNameRequired la then laNextLabel la
            else
              case bt of
                Normal -> (la, "")
                BoolExp -> (la, "")
                Cond -> (la, "")
                While -> laNextLabel la
                Check -> laNextLabel la
                Success -> laNextLabel la
                Failure -> laNextLabel la
                Post -> laNextLabel la
                _ -> error "nextBlockName: PartialFunction"
      modify (fccPutLabelAlloc la')
      return str


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

generateLabel :: FCCompiler String
generateLabel = do
  la <- gets fccLabelAlloc
  let (la', res) = laNextLabel la
  modify (fccPutLabelAlloc la')
  return res
generateLabels :: Int -> FCCompiler [String]
generateLabels n =  do
  la <- gets fccLabelAlloc
  let (la', res) = foldl (\(la, res) _ -> BiFunctor.second (:res) (laNextLabel la)) (la, []) [1..n]
  modify (fccPutLabelAlloc la')
  return (reverse res)

unpackMaybe :: Maybe a -> a
unpackMaybe x = error "Expected Just got Nothing" `fromMaybe` x

_getRegisterType :: FCRegister -> FCRegMap -> Maybe FCType
_getRegisterType reg regenv = case reg of
  VoidReg -> Just Void
  Reg _ -> x reg regenv
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

setVars :: [String] -> [FCRegister] -> FCCompiler ()
setVars vars vals = do
  venv <- gets fccVenv
  modify $ fccPutVenv (foldl (\venv (var, val) -> VE.setVar var val venv) venv (zip vars vals))

setVar :: String -> FCRegister -> FCCompiler ()
setVar var value = do
  vars <- gets fccVenv
  modify $ fccPutVenv (VE.setVar var value vars)

declVar :: String -> FCRegister -> FCCompiler ()
declVar var value = do
  vars <- gets fccVenv
  modify $ fccPutVenv (VE.declareVar var value vars)

isFunStatic :: String -> FCCompiler Bool
isFunStatic str = do
  asks (feIsFunStatic str)
askFunType :: String -> FCCompiler FCType
askFunType fname = do
  asks (unpackMaybe . feGetFunType fname)
feGetFunType :: String -> FCCFunEnv -> Maybe FCType
feGetFunType str fe = str `DM.lookup` fccfeRetTypes fe
feIsFunStatic :: String -> FCCFunEnv -> Bool
feIsFunStatic str fe = not $ str `DS.member` fccfeDynamicFuns fe
data FCCFunEnv = FCCFE {fccfeRetTypes :: DM.Map String FCType,
                       fccfeDynamicFuns :: DS.Set String}

               -------------- Loop Optimization ---------------

isInstrDynamic :: DS.Set String -> DS.Set FCRegister -> FCInstr -> Bool
isInstrDynamic dfuns dregs (reg, instr) = case instr of
  FunCall ft fname args -> fname `DS.member` dfuns || any ((`DS.member` dregs). snd) args
  FCBinOp ft fbo fr fr' -> fr `DS.member` dregs || fr' `DS.member` dregs
  FCUnOp ft fuo fr -> fr `DS.member` dregs
  FCPhi ft x0 -> True
  BitCast ft fr ft' -> fr `DS.member` dregs
  GetPointer ft fr fr' -> fr `DS.member` dregs || fr' `DS.member` dregs
  Return ft m_fr -> True
  FCEmptyExpr -> False
  FCFunArg ft s n -> error "FCFunArg"
  FCJump fr -> True
  FCCondJump fr fr' fr2 -> True

optimizeLoop :: DS.Set String -> FCBlock' FCInstr a -> FCBlock' FCInstr a
optimizeLoop dfuns fcblock  = case fcblock of
  FCNamedSBlock{} -> fcblock
  FCComplexBlock s fbs x0 -> FCComplexBlock s (map optimizeLoop' fbs) x0
  FCCondBlock s fc fr fs ff fp x0 -> FCCondBlock s fc fr (optimizeLoop' fs) (optimizeLoop' ff) fp x0
  FCPartialCond {} -> fcblock
  FCWhileBlock {} ->
    let
      (postB, successB, condB) = (\x -> (post x, success x, condEval x)) fcblock
      successB' = optimizeLoop' successB
      (_, res') = foldl' (gBlock dfuns) (DS.empty, []) [postB, condB, successB']
      whileBlock = FCWhileBlock { bname = bname fcblock, post = postB,
                                  condEval = condB, jmpReg = jmpReg fcblock,
                                  success=successB', epilogueLabel = epilogueLabel fcblock,
                                  addition = addition fcblock}
      my_undef = error "OptimizeLoopPlaceholder"
    in
      if null res' then whileBlock
      else FCComplexBlock "" [FCNamedSBlock "" (reverse res') my_undef, whileBlock] my_undef
  where
    optimizeLoop' = optimizeLoop dfuns
    g :: DS.Set String -> (DS.Set FCRegister, [FCInstr]) -> [FCInstr] -> (DS.Set FCRegister, [FCInstr])
    g dynfun (set, res) list = case list of
      [] -> (set, res)
      (x:xs) -> let
        (reg, rval) = x
        in
        if isInstrDynamic' set x
        then g' (DS.insert reg set, res) xs
        else g' (set, x:res) xs
      where
        g' = g dynfun
        isInstrDynamic' = isInstrDynamic dynfun
    gBlock :: DS.Set String -> (DS.Set FCRegister, [FCInstr]) -> FCBlock' FCInstr a  ->
      (DS.Set FCRegister, [FCInstr])
    gBlock dynfun (set, rest) fcblock = case fcblock of
      FCNamedSBlock s x0 a -> g' (set, rest) x0
      FCComplexBlock s fbs a -> foldl' gBlock' (set, rest) fbs
      FCCondBlock s fb fr fb' fb2 fb3 a -> foldl' gBlock' (set, rest) [fb, fb', fb2, fb3]
      FCPartialCond s fb fr fb' fb2 a -> foldl' gBlock' (set, rest) [fb, fb', fb2]
      FCWhileBlock s fb fb' fr fb2 str a -> (set, rest)
      where
        g' = g dynfun
        gBlock' = gBlock dynfun

               ------------- LCSE - GCSE ------------

-- data GSCEInternalVal = GSCEIVFCR FCRValue
--   deriving (Eq, Ord)

-- type FCInternal1 = FCBlock' (FCInstr) ((DS.Set GSCEInternalVal))

-- type DependantRegisters = DS.Set FCRegister
-- type GSCERegDefMap = DM.Map FCRegister FCRValue
-- type GSCEValRegMap = DM.Map GSCEInternalVal [FCRegister]
-- type GSCERegToDepsMap = DM.Map FCRegister DependantRegisters
-- type GSCERegToRegMap = DM.Map FCRegister FCRegister


-- type GSCEFCBlock1 = FCBlock' FCInstr (DS.Set GSCEInternalVal)
-- type GSCEFCBlock2 = FCBlock' FCInstr (DS.Set GSCEInternalVal, DS.Set GSCEInternalVal)
-- type GSCEMonad2State = (GSCERegDefMap, GSCEValRegMap, GSCERegToDepsMap,
--                         GSCERegToRegMap, SSARegisterAllocator)
-- type GSCEMonad2 = State GSCEMonad2State

-- swapRegister :: FCRegister -> FCRegister -> FCRValue -> FCRValue
-- swapRegister r1 r2 instr = case instr of
--   FunCall ft s x0 -> FunCall ft s (map (BiFunctor.second subst) x0)
--   FCBinOp ft fbo fr fr' -> FCBinOp ft fbo (subst fr) (subst fr')
--   FCUnOp ft fuo fr -> FCUnOp ft fuo (subst fr)
--   FCPhi ft x0 -> FCPhi ft (map (BiFunctor.first subst) x0)
--   BitCast ft fr ft' -> BitCast ft fr ft'
--   GetPointer ft fr fr' -> GetPointer ft fr fr'
--   Return ft m_fr -> Return ft (subst <$> m_fr)
--   FCEmptyExpr -> FCEmptyExpr
--   FCFunArg ft s n -> error "FCFunArg"
--   FCJump fr -> error "FCJump"
--   FCCondJump fr fr' fr2 -> error "FCJump"
--   where
--     subst x = if x == r1 then r2 else x

-- gsceFCRValToInVal :: FCRValue -> GSCEInternalVal
-- gsceFCRValToInVal = undefined

-- convertBlock :: b -> FCBlock' a c -> FCBlock' a b
-- convertBlock = undefined

-- joinBlock :: FCBlock' a b ->  FCBlock' a b ->  FCBlock' a b
-- joinBlock = undefined

-- gsceBlock :: DS.Set GSCEInternalVal -> FCBlock' FCInstr a -> GSCEMonad2 GSCEFCBlock2
-- gsceBlock set fcblock = case fcblock of
--   FCNamedSBlock s x0 a -> do
--     vals <- h x0
--     return $ FCNamedSBlock s x0 (vals, set)
--   FCComplexBlock s fbs a -> do
--     (vals, fbs') <- gsceBlockList set fbs
--     return $ FCComplexBlock s fbs' (vals, set)
--   FCCondBlock s fc fr fs ff fp a -> do
--     (set', list) <- gsceBlockList DS.empty [fs, ff]
--     (vals, (fc', fs', ff')) <- case list of
--       [fs', ff'] -> do
--         fc' <- gsceBlock DS.empty fc
--         return (DS.union (fst $ addition fc') set', (fc', fs', ff'))
--       [fx', fs', ff'] -> do
--         fc' <- gsceBlock DS.empty fc
--         return (DS.union (fst $ addition fc') set', ( joinBlock fx' fc', fs', ff' ))
--       _ -> error $ "List has length: " ++ show (length list)
--     return $ FCCondBlock s fc' fr fs' ff' (convertBlock (DS.empty, DS.empty) fp) (vals, set)
--   FCPartialCond s fc fr fs ff a -> do
--     (set', list) <- gsceBlockList DS.empty [fs, ff]
--     (vals, (fc', fs', ff')) <- case list of
--       [fs', ff'] -> do
--         fc' <- gsceBlock DS.empty fc
--         return (DS.union (fst $ addition fc') set', (fc', fs', ff'))
--       [fx', fs', ff'] -> do
--         fc' <- gsceBlock DS.empty fc
--         return (DS.union (fst $ addition fc') set', ( joinBlock fx' fc', fs', ff' ))
--       _ -> error $ "List has length: " ++ show (length list)
--     return $ FCPartialCond s fc' fr fs' ff' (vals, set)
--   FCWhileBlock s fp fce fr fs str a -> do
--     fce' <- gsceBlock DS.empty fce
--     fs' <- gsceBlock DS.empty fs
--     return $ FCWhileBlock s (convertBlock (DS.empty, DS.empty) fp) fce' fr fs' str (DS.empty, set)
--   where
--       h :: FCSimpleBlock -> GSCEMonad2 (DS.Set GSCEInternalVal)
--       h instr = do
--         (regdef, valreg, regtdeps, regreg, ssa) <- get
--         let (regdef', valreg', set) = foldl'
--               f1
--               (regdef, valreg, DS.empty)
--               instr
--         put (regdef, valreg', regtdeps, regreg, ssa)
--         return set
--           where
--             f1 :: (GSCERegDefMap, GSCEValRegMap, DS.Set GSCEInternalVal) ->
--               FCInstr -> (GSCERegDefMap, GSCEValRegMap, DS.Set GSCEInternalVal)
--             f1 (!regdef, !rvmap, !set) fi@(reg, inst) =
--               if reg == VoidReg then (regdef, rvmap, set)
--                 else let
--                 inval = gsceFCRValToInVal inst
--                 regdef' = DM.insert reg inst regdef
--                 set' = DS.insert inval set
--                 rvmap' = DM.insert inval
--                          (reg:([]`fromMaybe` DM.lookup inval rvmap)) rvmap
--                 in
--                   (regdef', rvmap', set')
-- gsceBlockList :: DS.Set GSCEInternalVal -> [FCBlock' FCInstr a] -> GSCEMonad2 (DS.Set GSCEInternalVal, [GSCEFCBlock2])

-- gsceBlockList initSet = foldrM (flip f) (initSet , [])
--   where
--     f :: (DS.Set GSCEInternalVal, [GSCEFCBlock2]) -> (FCBlock' FCInstr a)
--       -> GSCEMonad2 (DS.Set GSCEInternalVal, [GSCEFCBlock2])
--     f (set, rest) fblock = do
--       fblock' <- gsceBlock set fblock
--       let fblockvals = fst $ addition fblock'
--           common = DS.intersection common set
--       if null common
--         then return (DS.union fblockvals set, fblock':rest)
--         else gsceOptimize common (DS.union fblockvals set) (fblock':rest)

-- gsceOptimize :: DS.Set GSCEInternalVal -> DS.Set GSCEInternalVal
--              -> [GSCEFCBlock2] ->  GSCEMonad2 (DS.Set GSCEInternalVal, [GSCEFCBlock2])
-- gsceOptimize common prev z = do
--   bb <- f1 (DS.toList common) []
--   let newBlock = FCNamedSBlock "" (reverse bb) (common, prev)
--   return (prev, newBlock:z)
--   where
--     f1 :: [GSCEInternalVal] -> [FCInstr] ->GSCEMonad2 [FCInstr]
--     f1 list bb = do
--       (regdef, valreg, regtdeps, regreg, ssa) <- get
--       let
--         (regdef', regreg', ssa', bb') = foldl
--           (\(regdef, regreg, ssa, bb) val->
--              let
--                regs = unpackMaybe $ val `DM.lookup` valreg
--                (fst, rest) = case regs of
--                  (fst:snd:rest) -> (fst, snd:rest)
--                  _ -> error "List has less than two elements"
--                (ssa', reg) = _nextRegister ssa
--                definition = unpackMaybe $ DM.lookup fst regdef
--                bb' = (reg, definition):bb
--                regdef' = DM.insert reg definition regdef
--                regreg' = foldl (\regreg old -> DM.insert old reg regreg') regreg regs
--                in
--                (regdef, regreg', ssa', bb')
--               ) (regdef, regreg, ssa, bb) list
--       put (regdef', valreg, regtdeps, regreg', ssa')
--       return bb'

------------------------------ Loop power reduction -----------------------------------------------

reduce :: (DS.Set SRExprAtom, FCBlock) -> (DS.Set SRExprAtom, FCBlock)
reduce (set, block) = case block of
  FCNamedSBlock s instrs x1 -> (foldl' getAtoms set instrs, block)
  FCComplexBlock s fbs x0 -> let
    (set', fbs') = foldl' (\(!set, blockList) block ->
                  BiFunctor.second (:blockList) (reduce (set, block)))
        (set, []) fbs
    in
    (set', FCComplexBlock s (reverse fbs') x0)
  FCCondBlock s fc fr fs ff fp x0 ->
    let
      (_, fs') = reduce (set, fs)
      (_, ff') = reduce (set, ff)
      set'     = getAtomsBlock set fc
      set''     = getAtomsBlock set' fp
    in
      (set'', FCCondBlock s fc fr fs' ff' fp x0)
  FCPartialCond s fc fr fs ff x0 ->
    let
      (_, fs') = reduce (set, fs)
      (_, ff') = reduce (set, ff)
      set'     = getAtomsBlock set fc
    in
      (set', FCPartialCond s fc fr fs' ff' x0)
  FCWhileBlock s fpost feval fr fsuccess str x0 ->
    let
      setForLoop = getAtomsBlock set fpost
      setForfsuccess = getAtomsBlock setForLoop feval
      (_, fsuccess') = reduce (setForfsuccess, fsuccess)
      r1 = applyConvertToBlock setForLoop DM.empty feval
      r2 = applyConvertToBlock setForLoop r1 fsuccess
      -- substitutions = 
      in
      undefined
  where
    firstPhi :: DM.Map FCRegister SRExpr -> [(FCRegister, SRExpr)] ->
      FCInstr -> [(FCRegister, SRExpr)]
    firstPhi map res (i0, rval) = case rval of
      FCPhi ft list -> let
        i1 = fst $ head (if not (null list) then list else error "Empty phi list")
        i0Val = ST (DM.fromList ([(i0,1)])) 0
        i1Val = error "1018 pusta mapa" `fromMaybe` DM.lookup i1 map
        diff = srsub i1Val i0Val
        in
        case diff of
          ST map n -> if DM.null map then (i0, (ST (DM.fromList [(i0,1)]) n)):res else (i0, SRDynamic):res
          _ -> (i0, SRDynamic):res
      _ -> res
    getPhi :: FCBlock -> [FCRegister] -> [FCRegister]
    getPhi fcblock rest = case fcblock of
      FCNamedSBlock s x0 x1 -> foldr (\(reg,instr) rest ->
                                        case instr of
                                          FCPhi{} -> reg:rest
                                          _ -> rest ) rest x0
      FCComplexBlock s fbs x0 -> foldr getPhi rest fbs
      _ -> error "Malformed block with PHI"
    convertFCReg  :: DS.Set SRExprAtom -> DM.Map FCRegister SRExpr ->
      FCRegister -> SRExpr
    convertFCReg set map fcreg = case fcreg of
      VoidReg -> error "ConvertFCReg"
      Reg s -> if DS.member fcreg set
        then ST (DM.fromList [(fcreg, 1)]) 0
        else SRDynamic `fromMaybe` DM.lookup fcreg map
      ConstString n -> error "Nonsense"
      LitInt n -> ST DM.empty n
      LitBool b -> error "Nonsene"
      Et s -> error "Nonsense"
    convertInstr :: DS.Set SRExprAtom -> DM.Map FCRegister SRExpr ->
      FCInstr -> DM.Map FCRegister SRExpr
    convertInstr atoms map (reg, instr)  = case (reg, instr) of
      (VoidReg, _) -> map
      (Reg _, instr) -> case instr of
        FunCall ft s x0 -> DM.insert reg SRDynamic map
        FCBinOp ft fbo fr fr' -> case fbo of
          Add -> DM.insert reg (sradd (convertFCReg' fr) (convertFCReg' fr')) map
          Sub -> DM.insert reg (srsub (convertFCReg' fr) (convertFCReg' fr')) map
          Div -> DM.insert reg (srdiv (convertFCReg' fr) (convertFCReg' fr')) map
          Mul -> DM.insert reg (srmul (convertFCReg' fr) (convertFCReg' fr')) map
          Mod -> DM.insert reg SRDynamic map
          _ -> map
        FCUnOp ft fuo fr -> case fuo of
          Neg -> DM.insert reg (srimul (-1) (convertFCReg' reg)) map
          BoolNeg -> map
        FCPhi ft x0 -> DM.insert reg SRDynamic map
        BitCast ft fr ft' -> map
        GetPointer ft fr fr' -> map
        Return ft m_fr -> map
        FCEmptyExpr -> map
        FCFunArg ft s n -> map
        FCJump fr -> map
        FCCondJump fr fr' fr2 -> map
        where
          convertFCReg' = convertFCReg atoms map
    applyConvertToBlock :: DS.Set SRExprAtom -> DM.Map FCRegister SRExpr ->
      FCBlock -> DM.Map FCRegister SRExpr
    applyConvertToBlock set map fcblock = case fcblock of
      FCNamedSBlock s x0 x1 -> foldl' (convertInstr set) map x0
      FCComplexBlock s fbs x0 -> foldl' applyConvertToBlock' map fbs
      FCCondBlock s fc fr fs ff fb3 x0 -> foldl' applyConvertToBlock' map [fc, fs, ff]
      FCPartialCond s fc fr fs ff x0 -> foldl' applyConvertToBlock' map [fc, fs, ff]
      FCWhileBlock s fb fb' fr fb2 str x0 -> map
      where
        applyConvertToBlock' = applyConvertToBlock set
    getAtoms :: DS.Set SRExprAtom -> FCInstr -> DS.Set SRExprAtom
    getAtoms !set (reg, instr) = DS.insert reg set
    getAtomsBlock :: DS.Set SRExprAtom -> FCBlock -> DS.Set SRExprAtom
    getAtomsBlock set block = case block of
      FCNamedSBlock s instrs x1 -> foldl' getAtoms set instrs
      FCComplexBlock s fbs x0 -> foldl' getAtomsBlock set fbs
      FCCondBlock s fb fr fb' fb2 fb3 x0 -> foldl' getAtomsBlock set [fb, fb', fb2, fb3]
      FCPartialCond s fb fr fb' fb2 x0 -> foldl' getAtomsBlock set [fb, fb', fb2]
      FCWhileBlock s fb fb' fr fb2 str x0 -> error "Muszę się zastanowić"

------------------------------ MyExpr --------------------------------------------------------------

srexprToFCR :: SSARegisterAllocator -> SRExpr -> (SSARegisterAllocator, FCRegister, [FCInstr])
srexprToFCR ssa srexpr =
  case srexpr of
    SRDynamic -> error "This should not happen"
    ST map n -> foldl'
      (\(ssa,prevreg, rest) (reg, mul) ->
          let
            fcr = fcmul reg mul
            (ssa', resReg) = _nextRegister ssa
            rest' = (resReg, fcr):rest
            (ssa'', resReg') = _nextRegister ssa
            rest'' = (resReg', fcradd prevreg resReg):rest'
          in
            if prevreg == (LitInt 0)
            then (ssa', resReg, rest')
            else (ssa'', resReg', rest''))
      (ssa,(LitInt n), []) (DM.toList map)

  where
    fcmul :: FCRegister -> Int -> FCRValue
    fcmul x y = FCBinOp Int Mul x (LitInt y)
    fcradd x y = FCBinOp Int Add x y

data SRExpr' a = ST (DM.Map a Int) Int | SRDynamic
  deriving (Eq, Ord)
type SRExpr = SRExpr' FCRegister

f :: (Int -> Int -> Int) -> SRExpr -> SRExpr -> SRExpr
f op s1 s2 = case (s1, s2) of
  (ST m1 i1, ST m2 i2) ->
    let
      (m1',m2') = if DM.size m1 < DM.size m2 then (m1, m2) else (m2, m1)
      i3 = i1 `op` i2
      m3 =
        foldl'
          ( \map (key, val) ->
              let x = (i1 `op` (0 `fromMaybe` DM.lookup key map))
               in if x == 0
                    then DM.delete key map
                    else DM.insert key x map
          )
          m2'
          (DM.toList m1')
    in
      ST m3 i3
  _ -> SRDynamic

sradd :: SRExpr -> SRExpr -> SRExpr
srsub :: SRExpr -> SRExpr -> SRExpr
sradd = f (+)
srsub = f (-)

srdiv :: SRExpr -> SRExpr -> SRExpr
srdiv x@(ST m1 i1) y@(ST m2 i2) = SRDynamic
srdiv x y = SRDynamic
srmul :: SRExpr -> SRExpr -> SRExpr
srmul x@(ST m1 i1) y@(ST m2 i2) =
  if (DM.null m1)
  then srimul i1 y
  else
    if (DM.null m2)
    then srimul i2 x
    else SRDynamic
srmul _ _ = SRDynamic
srimul :: Int -> SRExpr -> SRExpr
srimul n = f (*) (ST DM.empty n)

sreq :: SRExpr -> SRExpr -> Bool
sreq s1 s2 = case (s1, s2) of
  (ST m1 i1, ST m2 i2) -> i1 == i2 && m1 == m2
  _ -> False


substitute :: (Ord a ) => SRExprAtom' a -> SRExpr' (SRExprAtom' a) -> SRExpr' (SRExprAtom' a) -> SRExpr' (SRExprAtom' a)
substitute atom subst srexpr = case (subst, srexpr) of
  (SRDynamic, _) -> SRDynamic
  (_, SRDynamic) -> SRDynamic
  (ST m1 i1, ST m2 i2) ->
    case DM.lookup atom m2 of
      Nothing -> srexpr
      Just multiplier -> ST newMap (i1 * multiplier + i2)
        where
          newMap =
            foldl' (\map (key,value) ->
                             let nv = ((value * multiplier) + (0 `fromMaybe` DM.lookup key map))
                             in if nv == 0
                                then DM.delete key map
                                else DM.insert key nv map) m2 (DM.toList m1)
type SRExprAtom' a = a
type SRExprAtom = SRExprAtom' FCRegister

-- convertFCInstr :: DS.Set SRExprAtom -> DM.Map FCRegister SRExpr -> FCInstr -> SRExpr
