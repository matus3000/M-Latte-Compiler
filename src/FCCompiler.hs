{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

-- TO DO:
-- a) Zamienić mapM getVar foldable na getVars
-- b) Sprawić, żeby return nie otrzymawało normalnego rejestru, tylko rejestr typu void.
-- c) Zmienić COND na CONDElse gdzie jedynyną instrukcją jest instrukcja pusta. W Translator.hs
module FCCompiler where

import Prelude

import Data.Maybe (fromMaybe, maybeToList)
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import Control.Monad.State.Strict
import Control.Monad.Except (Except, MonadError)

import CompilationError(SemanticError, SemanticError(CompilationError), SemanticErrorType (oldDefinition))
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
import Data.Foldable (foldlM, foldl', foldrM)
import qualified VariableEnvironment as VC
import qualified Control.Arrow as BiFunctor
import qualified VariableEnvironment as Ve
import Control.Monad.Reader (ReaderT (runReaderT), asks, ask)
import Data.List (nub)

externalFunctions :: [([Char], (FCType, [FCType]))]
externalFunctions = [("printString", (Void, [DynamicStringPtr])),
                     ("printInt", (Void, [Int])),
                     ("error", (Void, [])),
                     ("readInt", (Int, [])),
                     ("readString", (DynamicStringPtr, []))]

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
  ([], str) -> error "I haven't thought out that one yet."
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
bbNameSub :: BlockBuilder -> String -> BlockBuilder
bbNameSub (BB is _ bs) str = BB is str bs
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

        list <- generateLabels 3
        let [successEt, failureEt, postEt] = list


        (cb, (_, jreg)) <- withOpenBlock Check $ \bname ->
          BiFunctor.first bbBuildAnonymous <$> translateExpr bname bbNew  ie True

        (sb, sreg, sbn) <- withPrenamedOpenBlock successEt Success $
          \bname -> f bname bbNew ies (failureEt, postEt)

        (fb, (_, _)) <- withPrenamedOpenBlock failureEt Failure $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump postEt) bbNew) bname,
                  (Void, VoidReg))

        (pb, res) <- withPrenamedOpenBlock postEt Post $ \bname -> do
          let phi = FCPhi Bool [(sreg, Et sbn), (LitBool False, Et failureEt)]
          (bb', r)<- emplaceFCRValue phi bbNew
          return (bbBuildNamed bb' bname, r)

        let returnBlock = FCCondBlock bname cb jreg sb fb pb ()
        return (bbaddBlock returnBlock bb, (Bool, res))

    f :: String -> BlockBuilder -> [Tr.IExpr] -> (String, String) -> FCCompiler (FCBlock, FCRegister, String)
    f bn bb [ie] (_, postEt) = do
      withPrenamedOpenBlock bn Normal $ \bname -> do
        (cbb, (ftype, reg)) <- translateExpr bname bbNew  ie True -- Można zmienić na BIFunctor
        return (bbBuildNamed (bbaddInstr (VoidReg, jump postEt) cbb) bname, reg, bname)
    f bn bb (ie:rest) (failureEt, postEt) = do

        (cb, (_, jreg)) <- withOpenBlock Check $ \bname ->
          (bbBuildAnonymous `BiFunctor.first`) <$> translateExpr bname bbNew  ie True

        (sb, r, bn') <- withOpenBlock Success $ \bname -> do
          f bname bbNew rest (failureEt, postEt)

        (fb, (_, _)) <- withOpenBlock Failure $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump failureEt) bbNew) bname, (Void, VoidReg))

        let returnBlock = FCPartialCond bn cb jreg sb fb ()

        return (returnBlock, r, bn')
translateOrExpr :: String -> BlockBuilder -> Tr.IExpr -> Bool
  -> FCCompiler (BlockBuilder, (FCType, FCRegister))
translateOrExpr bn bb (Tr.IOr (ie:ies)) save =
  g bn bb ie ies
  where
    g :: String-> BlockBuilder ->Tr.IExpr -> [Tr.IExpr] -> FCCompiler (BlockBuilder, (FCType, FCRegister))
    g bname bb ie rest = do
      withOpenBlock BoolExp $ \bname -> do

        list <- generateLabels 3
        let [successEt, failureEt, postEt] = list

        (cb, (_, jreg)) <- withOpenBlock Check $ \bname ->
          BiFunctor.first bbBuildAnonymous <$> translateExpr bname bbNew  ie True

        (sb, (_, _)) <- withPrenamedOpenBlock successEt Success $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump postEt) bbNew) bname,
                  (Void, VoidReg))

        (fb, sreg, sbn) <- withPrenamedOpenBlock failureEt Failure $
          \bname -> f bname bbNew ies (successEt, postEt)

        (pb, res) <- withPrenamedOpenBlock postEt Post $ \bname -> do
          let phi = FCPhi Bool [(sreg, Et sbn), (LitBool True, Et successEt)]
          (bb', r)<- emplaceFCRValue phi bbNew
          return (bbBuildNamed bb' bname, r)

        let returnBlock = FCCondBlock bname cb jreg sb fb pb ()
        return (bbaddBlock returnBlock bb, (Bool, res))

    f :: String -> BlockBuilder -> [Tr.IExpr] -> (String, String) -> FCCompiler (FCBlock, FCRegister, String)
    f bn bb [ie] (_, postEt) = do
      withPrenamedOpenBlock bn Normal $ \bname -> do
        (cbb, (ftype, reg)) <- translateExpr bname bbNew  ie True -- Można zmienić na BIFunctor
        return (bbBuildNamed (bbaddInstr (VoidReg, jump postEt) cbb) bname, reg, bname)

    f bn bb (ie:rest) (successEt, postEt) = do

        (cb, (_, jreg)) <- withOpenBlock Check $ \bname ->
          (bbBuildAnonymous `BiFunctor.first`) <$> translateExpr bname bbNew  ie True

        (sb, (_, _)) <- withOpenBlock Success $ \bname -> do
          return (bbBuildNamed (bbaddInstr (VoidReg , jump successEt) bbNew) bname, (Void, VoidReg))

        (fb, r, bn') <- withOpenBlock Failure $ \bname -> do
          f bname bbNew rest (successEt, postEt)

        let returnBlock = FCPartialCond bn cb jreg sb fb ()

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
       -- Tr.INot ie -> do
       --   reg <- translateExpr ie True
       --   prependFCRValue RNormal $ FCUnOp BoolNeg reg
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

    oldVals <- getVars ascmd
    reg_ft <- preallocRegisters (zip ascmd (map fst oldVals))
    setVars ascmd (map fst reg_ft)

    (sVals, sb) <- withOpenBlock Success $
      \name ->
        withProtectedVars ascmd $ do
        sbb <- translateBlock name ib bbNew
        sVal <- mapM getVar ascmd
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

    return $ bbNameSub (bbaddBlock (FCWhileBlock wname pb cb jr sb epilogueEndStr ()) bb) epilogueEndStr
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
  withOpenBlock Normal $ (\blockName ->foldlM (translateInstr blockName) rest stmts)

translateFun :: Tr.IFun -> FCCompiler FCFun
translateFun (Tr.IFun s lt lts ib) = do
  withOpenFunBlock s lt lts $ \res ->
    do
      fbody <- translateBlock s ib bbNew
      return $ FCFun' {name = s, retType = convert lt, args = res, FCT.body = bbBuildAnonymous fbody}


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
  _ftypeMapInit = DM.fromList [("printInt", Void), ("printString", Void),
                               ("readInt", Int), ("readString", DynamicStringPtr),
                               ("error", Void)]
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
    put (FCC varenv' ssa' regst' (fccConstants fcc) (fccLabelAlloc fcc))
    return $ zip (map convert (snd <$> args)) rs

closeFunBlock :: FCCompiler ()
closeFunBlock = do
  fcc <- get
  let ve' = VE.closeClosure (fccVenv fcc)
  checkVarEnv ve'
  modify $ fccPutVenv ve'
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

isFunctionStatic :: String -> FCCompiler Bool
isFunctionStatic fname = error "Unimplemented"
getFunctionType :: String -> FCCompiler FCType
getFunctionType fname = error "Unimplemented"

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



               ------------- LCSE - GCSE ------------

data GSCEInternalVal = GSCEIVFCR FCRValue
  deriving (Eq, Ord)

type FCInternal1 = FCBlock' (FCInstr) ((DS.Set GSCEInternalVal))

type DependantRegisters = DS.Set FCRegister
type GSCERegDefMap = DM.Map FCRegister FCRValue
type GSCEValRegMap = DM.Map GSCEInternalVal [FCRegister]
type GSCERegToDepsMap = DM.Map FCRegister DependantRegisters
type GSCERegToRegMap = DM.Map FCRegister FCRegister

type GSCEMonad1State = (GSCEValRegMap, GSCERegToDepsMap)
type GSCEMonad1 = State GSCEMonad1State
type GSCEFCFun1 = FCFun' FCInstr (DS.Set GSCEInternalVal)

type GSCEFCBlock1 = FCBlock' FCInstr (DS.Set GSCEInternalVal)
type GSCEFCBlock2 = FCBlock' FCInstr (DS.Set GSCEInternalVal, DS.Set GSCEInternalVal)
type GSCEMonad2State = (GSCERegDefMap, GSCEValRegMap, GSCERegToDepsMap,
                        GSCERegToRegMap, SSARegisterAllocator)
type GSCEMonad2 = State GSCEMonad2State

swapRegister :: FCRegister -> FCRegister -> FCRValue -> FCRValue
swapRegister r1 r2 instr = case instr of
  FunCall ft s x0 -> FunCall ft s (map (BiFunctor.second subst) x0)
  FCBinOp ft fbo fr fr' -> FCBinOp ft fbo (subst fr) (subst fr')
  FCUnOp ft fuo fr -> FCUnOp ft fuo (subst fr)
  FCPhi ft x0 -> FCPhi ft (map (BiFunctor.first subst) x0)
  ConstValue ft fr -> ConstValue ft fr
  BitCast ft fr ft' -> BitCast ft fr ft'
  GetPointer ft fr fr' -> GetPointer ft fr fr'
  Return ft m_fr -> Return ft (subst <$> m_fr)
  FCEmptyExpr -> FCEmptyExpr
  FCFunArg ft s n -> error "FCFunArg"
  FCJump fr -> error "FCJump"
  FCCondJump fr fr' fr2 -> error "FCJump"
  where
    subst x = if x == r1 then r2 else x

gsceBlock :: FCBlock' FCInstr a -> GSCEMonad2 GSCEFCBlock2
gsceBlock fcblock = case fcblock of
  FCNamedSBlock s x0 a -> undefined
  FCComplexBlock s fbs a -> undefined
  FCCondBlock s fb fr fb' fb2 fb3 a -> undefined
  FCPartialCond s fb fr fb' fb2 a -> undefined
  FCWhileBlock s fb fb' fr fb2 str a -> undefined
  where
      h :: FCSimpleBlock -> GSCEMonad1 (DS.Set GSCEInternalVal)
      h instr = do
      gsceState1 <- get
      let (regvalmap, set) = foldl'
            f1
            (gsceS1RegValMap gsceState1, gsceS1RegToDepsMap gsceState1, DS.empty)
            instr
      put (regvalmap, gsceS1RegToDepsMap gsceState1)
      return set
      where
        f1 :: (GSCEValRegMap, DS.Set GSCEInternalVal) ->
          FCInstr -> (GSCEValRegMap, DS.Set GSCEInternalVal)
        f1 (!rvmap, !set) fi@(reg, inst) = let
          reg = fst fi
          f_ :: GSCERegToDepsMap -> FCRegister -> GSCERegToDepsMap
          f_ !rdmap !fr = DM.insert fr (DS.insert reg (DS.empty `fromMaybe` DM.lookup fr rdmap)) rdmap
          inval = gsceFCRValToInVal inst
          set' = if fst fi /= VoidReg then DS.insert inval set else set
          rvmap' = if fst fi /= VoidReg then DM.insert reg (gsceFCRValToInVal inst) rvmap else rvmap
          in
          (rvmap', rdmap', set')
        f2 :: FCInstr -> [FCRegister]
        f2 (fr, fv) = case fv of
          FunCall ft s x0 -> if ft /= Void then [] else snd `map` nub x0
          FCBinOp ft fbo fr fr' -> [fr, fr']
          FCUnOp ft fuo fr -> [fr]
          FCPhi ft x0 -> []
          ConstValue ft fr -> []
          BitCast ft fr ft' -> []
          GetPointer ft fr fr' -> []
          Return ft m_fr -> maybeToList m_fr
          FCEmptyExpr -> []
          FCFunArg ft s n -> []
          FCJump fr -> []
          FCCondJump fr fr' fr2 -> []

  
gsceBlockList :: [FCBlock' FCInstr a] -> GSCEMonad2 (DS.Set GSCEInternalVal, [GSCEFCBlock2])
-- gsceBlock fcblock = case fcblock of 
--   FCNamedSBlock s x0 x1 -> _
--   FCComplexBlock s fbs x0 -> _
--   FCCondBlock s fb fr fb' fb2 fb3 x0 -> _
--   FCPartialCond s fb fr fb' fb2 x0 -> _
--   FCWhileBlock s fb fb' fr fb2 str x0 -> _

gsceBlockList = foldrM (flip f) (DS.empty , [])
  where
    f :: (DS.Set GSCEInternalVal, [GSCEFCBlock2]) -> (FCBlock' FCInstr a)
      -> GSCEMonad2 (DS.Set GSCEInternalVal, [GSCEFCBlock2])
    f (set, rest) fblock = do
      fblock' <- gsceBlock fblock
      let fblockvals = fst $ addition fblock'
          common = DS.intersection common set
      if null common
        then return (DS.union fblockvals set, fblock':rest)
        else gsceOptimize common (DS.union fblockvals set) (fblock':rest)

gsceOptimize :: DS.Set GSCEInternalVal -> DS.Set GSCEInternalVal
             -> [GSCEFCBlock2] ->  GSCEMonad2 (DS.Set GSCEInternalVal, [GSCEFCBlock2])
gsceOptimize common prev z = do
  bb <- f1 (DS.toList common) []
  let newBlock = FCNamedSBlock "" (reverse bb) (common, prev)
  return (prev, newBlock:z)
  where
    f1 :: [GSCEInternalVal] -> [FCInstr] ->GSCEMonad2 [FCInstr]
    f1 list bb = do
      (regdef, valreg, regtdeps, regreg, ssa) <- get
      let
        (regdef', regreg', ssa', bb') = foldl
          (\(regdef, regreg, ssa, bb) val->
             let
               regs = unpackMaybe $ val `DM.lookup` valreg
               (fst, rest) = case regs of
                 (fst:snd:rest) -> (fst, snd:rest)
                 _ -> error "List has less than two elements"
               (ssa', reg) = _nextRegister ssa
               definition = unpackMaybe $ DM.lookup fst regdef
               bb' = (reg, definition):bb
               regdef' = DM.insert reg definition regdef
               regreg' = foldl (\regreg old -> DM.insert old reg regreg') regreg regs
               in
               (regdef, regreg', ssa', bb')
              ) (regdef, regreg, ssa, bb) list
      put (regdef', valreg, regtdeps, regreg', ssa')
      return bb'
-- gsce funs = do
--   rmap <- _regMap . fccRegMap <$> get
--   undefined
--   where
--     -- f :: FCFun -> GSCEMonad1 ()
--     -- f fun = g (block fun)
--     gsceS1RegValMap :: GSCEMonad1State -> GSCERegValueMap
--     gsceS1RegValMap = fst
--     gsceS1RegToDepsMap :: GSCEMonad1State -> GSCERegToDepsMap
--     gsceS1RegToDepsMap = snd
--     gsceFCRValToInVal :: FCRValue -> GSCEInternalVal
--     gsceFCRValToInVal = undefined
--     g' :: DS.Set GSCEInternalVal -> GSCEFCBlock1 -> GSCEFCBlock2
--     g' set fcblock = case fcblock of
--       FCNamedSBlock s x0 set' -> FCNamedSBlock s x0 (set', set)
--       FCComplexBlock s fbs set' -> undefined
--       FCCondBlock s fb fr fb' fb2 fb3 set' -> undefined
--       FCPartialCond s fb fr fb' fb2 set' -> undefined
--       FCWhileBlock s fb fb' fr fb2 str set' -> undefined
--       where
--         g'folded :: DS.Set GSCEInternalVal ->[GSCEFCBlock1] -> [GSCEFCBlock2]
--         g'folded set x = foldr (\block (set, rest) ->
--                                    case block of 
--           FCNamedSBlock {} -> g' set block
--           FCComplexBlock s fbs set' -> _
--           FCCondBlock s fb fr fb' fb2 fb3 set' -> _
--           FCPartialCond s fb fr fb' fb2 set' -> _
--           FCWhileBlock s fb fb' fr fb2 str set' -> _
--                                      ) (set, undefined) x
--     g :: FCBlock -> GSCEMonad1 GSCEFCBlock1
--     g block = do
--       case block of
--                FCNamedSBlock s x0 _ -> do
--                  set <- h x0
--                  return $ FCNamedSBlock s x0 set
--                FCComplexBlock s fbs _ -> do
--                  fbs' <- mapM g fbs
--                  let set = foldl' (\(!set) fb -> DS.union set (addition fb)) DS.empty fbs'
--                  return $ FCComplexBlock s fbs' set
--                FCCondBlock s fb fr fb' fb2 fb3 _ -> do
--                  fbs' <- mapM g [fb, fb', fb2, fb3]
--                  let set = foldl' (\(!set) fb -> DS.union set (addition fb)) DS.empty fbs'
--                      [gfb, gfb', gfb2, gfb3] = fbs'
--                  return $ FCCondBlock s gfb fr gfb' gfb2 gfb3 set
--                FCPartialCond s fb fr fb' fb2 _ ->  do
--                  fbs' <- mapM g [fb, fb', fb2]
--                  let set = foldl' (\(!set) fb -> DS.union set (addition fb)) DS.empty fbs'
--                      [gfb, gfb', gfb2] = fbs'
--                  return $ FCPartialCond s gfb fr gfb' gfb2 set
--                FCWhileBlock s fb fb' fr fb2 str _ -> do
--                  fbs' <- mapM g [fb, fb', fb2]
--                  let set = foldl' (\(!set) fb -> DS.union set (addition fb)) DS.empty fbs'
--                      [gfb, gfb', gfb2] = fbs'
--                  return $ FCWhileBlock s gfb gfb' fr gfb2 str set

