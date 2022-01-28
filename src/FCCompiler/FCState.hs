module FCCompiler.FCState (FCState(fcsConstants),
                           OnRValueConflict(..),
                           new,
                           addFCRValue,
                           clearRValue,
                           setVar,
                           declareVar,
                           lookupVar,
                           isVarDeclared,
                           openBlock,
                           closeBlock,
                           openConditionalBlock,
                           closeConditionalBlock,
                           getRegisterType,
                           nextLabel,
                           generateLabels,
                           CompileTimeConstants(constMap),
                           protectVars,
                           endProtection,
                           lookupConstString,
                           addConstString
                           ) where
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import qualified Control.Arrow as BiFunctor

import FCCompilerTypes (FCRValue, FCRegister (Reg, ConstString, VoidReg, LitInt, LitBool, Et, FCNull), FCSimpleBlock, fCRValueType, FCType (Void, Int, Bool, ConstStringPtr))
import VariableEnvironment(VarEnv(..), newVarEnv)
import qualified VariableEnvironment as VE
import Data.Maybe (isJust)

  -- Internal Types --
type FCVarEnv = VarEnv String FCRegister
data FCRegMap = FCRegMap {_regMap::DM.Map FCRegister FCRValue,
                          _rvalueMap:: VE.VarEnv FCRValue FCRegister}
type SSARegisterAllocator = Int
data LabelAllocator = LA {laNextId::Int, laNameRequired::Bool}

  -- Exported Types
data CompileTimeConstants = CTC {constMap :: DM.Map String Int,
                                 nextEtId :: Int}


data FCState = FCState {fcsVenv::FCVarEnv, fcsSSAAloc::SSARegisterAllocator,
                        fcsRegMap::FCRegMap, fcsConstants::CompileTimeConstants,
                        fcsLabelAlloc::LabelAllocator}
data OnRValueConflict = RegisterToRValue | TwoWay

  -- Internal functions

ctcNew = CTC DM.empty 0
ctcEmplaceString :: String -> CompileTimeConstants -> (CompileTimeConstants, FCRegister)
ctcEmplaceString str ctc = case str `DM.lookup` constMap ctc of
  Just x -> (ctc, ConstString x)
  Nothing -> (ctc', ConstString x')
    where
      x' = nextEtId ctc
      ctc' = CTC (DM.insert str (nextEtId ctc) (constMap ctc)) (1 + nextEtId ctc)

laNew :: LabelAllocator
laNew = LA 0 False
laNextLabel :: LabelAllocator -> (LabelAllocator, String)
laNextLabel la = (LA (1+laNextId la) False, "L" ++ show (laNextId la))
laLookupNextLabel :: LabelAllocator -> (LabelAllocator, String)
laLookupNextLabel la = (LA (laNextId la) True, "L" ++ show (laNextId la))

ssaRegAllocNew :: SSARegisterAllocator
ssaRegAllocNew = 0
ssaNext :: SSARegisterAllocator -> (SSARegisterAllocator, Int)
ssaNext x = (x+1, x)

regmapOpenConditionalBlock :: FCRegMap -> FCRegMap
regmapOpenConditionalBlock (FCRegMap m1 m2) = FCRegMap m1 (VE.openClosure m2)
regmapCloseConditionalBlock (FCRegMap m1 m2) = FCRegMap m1 (VE.closeClosure m2)
regmapLookupRegister :: FCRegister -> FCRegMap -> Maybe FCRValue
regmapLookupRegister x regmap = case x of
  Reg{} -> DM.lookup x (_regMap regmap)
  _ -> error "Real undefined behaviour"

fcRegMapNew = FCRegMap DM.empty (VE.openClosure VE.newVarEnv)

fcsPutVenv :: FCVarEnv -> FCState -> FCState
fcsPutVenv ve' (FCState ve ssa rm c b) = FCState ve' ssa rm c b
fcsPutRegMap :: FCRegMap -> FCState -> FCState
fcsPutRegMap re' (FCState ve ssa re c b) = FCState ve ssa re' c b
fcsPutSSAAloc :: SSARegisterAllocator -> FCState -> FCState
fcsPutSSAAloc ssa' (FCState ve ssa re c b) = FCState ve ssa' re c b
fcsPutConstants :: CompileTimeConstants -> FCState -> FCState
fcsPutConstants c' (FCState ve ssa re c b) = FCState ve ssa re c' b
fcsPutLabelAlloc :: LabelAllocator -> FCState -> FCState
fcsPutLabelAlloc fbc' (FCState ve ssa re c fbc) = FCState ve ssa re c fbc'

fcsModifyVenv :: (FCVarEnv -> FCVarEnv) -> FCState -> FCState
fcsModifyVenv f x = fcsPutVenv (f (fcsVenv x)) x
fcsModifyRegMap :: (FCRegMap -> FCRegMap) -> FCState -> FCState
fcsModifyRegMap f x = fcsPutRegMap (f (fcsRegMap x)) x
  -- Exported functions

new :: FCState
new = FCState newVarEnv ssaRegAllocNew fcRegMapNew ctcNew laNew

allocateRegister :: FCType -> FCState -> (FCState, FCRegister)
allocateRegister = undefined

addFCRValue :: FCRValue -> OnRValueConflict -> FCState -> (FCState, Either FCRegister FCRegister)
addFCRValue fcrval onconflict fcstate = let
  (regmap, rvaluemap) = (_regMap (fcsRegMap fcstate), _rvalueMap (fcsRegMap fcstate))
  ssa = fcsSSAAloc fcstate
  in
   if fCRValueType fcrval == Void then (fcstate, Right VoidReg)
   else case fcrval `VE.lookupVar` rvaluemap of
      Nothing -> let
        (ssa', r) = if fCRValueType fcrval == Void
          then (ssa, VoidReg)
          else BiFunctor.second (Reg . show) (ssaNext ssa)
        fstate' =  fcsPutSSAAloc ssa' $
                   fcsPutRegMap (FCRegMap
                                 (DM.insert r fcrval regmap)
                                 (case onconflict of
                                   TwoWay -> VE.declareVar fcrval r rvaluemap
                                   RegisterToRValue -> rvaluemap))
                   fcstate
        in
        (fstate', Right r)
      Just fr -> case onconflict of
        TwoWay -> (fcstate, Left fr)
        RegisterToRValue -> error "WIP"

getRegisterType :: FCRegister -> FCState -> Maybe FCType
getRegisterType reg fstate = case reg of
  VoidReg -> Just Void
  Reg _ -> x reg regenv
  LitInt n -> Just Int
  LitBool b -> Just Bool
  Et s -> Just Void
  FCNull x -> Just (error "I need to think that one out")
  ConstString x -> Just $ ConstStringPtr x
  where
    regenv = fcsRegMap fstate
    x :: FCRegister -> FCRegMap -> Maybe FCType
    x r regenv= fCRValueType <$> regmapLookupRegister r regenv



clearRValue :: FCRValue -> FCState -> FCState
clearRValue = undefined

setVar :: String -> FCRegister -> FCState -> FCState
setVar var reg = fcsModifyVenv (VE.setVar var reg)
declareVar :: String -> FCRegister -> FCState -> FCState
declareVar var reg  = fcsModifyVenv (VE.declareVar var reg)
lookupVar ::  String -> FCState -> Maybe FCRegister
lookupVar var = VE.lookupVar var . fcsVenv
isVarDeclared :: String -> FCState -> Bool
isVarDeclared var = isJust . lookupVar var
protectVars :: [String] -> FCState -> FCState
protectVars vars = let
  f :: FCVarEnv -> FCVarEnv
  f = \ve -> foldl (\ve var ->
               case VE.lookupVar var ve of
                 Just val -> VE.declareVar var val ve
                 Nothing -> ve) (VE.openClosure ve) vars
  in
  fcsModifyVenv f

endProtection :: FCState -> FCState
endProtection = fcsModifyVenv VE.closeClosure

openFunBlock :: FCState -> FCState
openFunBlock fstate = FCState newVarEnv ssaRegAllocNew fcRegMapNew (fcsConstants fstate)  (fcsLabelAlloc fstate)
openBlock :: FCState -> FCState
openBlock x = fcsPutVenv (VE.openClosure (fcsVenv x)) x
closeBlock :: FCState -> FCState
closeBlock x = fcsPutVenv (VE.closeClosure (fcsVenv x)) x

openConditionalBlock :: FCState -> FCState
openConditionalBlock = openBlock . fcsModifyRegMap regmapOpenConditionalBlock
closeConditionalBlock :: FCState -> FCState
closeConditionalBlock = closeBlock . fcsModifyRegMap regmapCloseConditionalBlock

nextLabel :: FCState -> (FCState, String)
nextLabel fstate = let
  la = fcsLabelAlloc fstate
  (la', label) = laNextLabel la
  in
  (fcsPutLabelAlloc la' fstate, label)

generateLabels :: Int -> FCState -> (FCState, [String])
generateLabels n fstate = BiFunctor.second reverse $ foldl
                          (\(fstate, rest) _ -> BiFunctor.second (:rest) (nextLabel fstate))
                          (fstate, [])
                          [1..n]

lookupConstString :: String -> FCState -> Maybe FCRegister
lookupConstString string fstate = ConstString <$> DM.lookup string (constMap $ fcsConstants fstate)
addConstString :: String -> FCState -> (FCState, FCRegister)
addConstString string fstate = BiFunctor.first (`fcsPutConstants` fstate) (ctcEmplaceString string fstate)
