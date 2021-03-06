module Gsce (gcseOptimize) where


-- TO DO
-- Optymalizacja polegająca na korzystaniu z poprzednich args. Czyli nie bezwarukowy insert do RegDef

import Prelude

import Data.Maybe (fromMaybe, maybeToList, fromJust)
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import Control.Monad.State.Strict
import Control.Monad.Except (Except, MonadError)

import FCCompilerTypes as FCT
import qualified Translator as Tr
import qualified Data.Functor
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
import FCCompiler.FCEnvironment (FCEnvironment)
import qualified FCCompiler.FCEnvironment as Fce
import qualified DeadCodeRemoval as Fce

data InternalVal = IVFCR FCRValue
  deriving (Eq, Ord)

type FCInternal1 = FCBlock' FCInstr (DS.Set InternalVal)
type RegDefMap = DM.Map FCRegister FCRValue
type ValRegMap = DM.Map InternalVal [FCRegister]
type Substitution = DM.Map FCRegister FCRegister

type Arg = (RegDefMap, ValRegMap, Substitution)
type ValuesInsideBlock = DS.Set InternalVal
type ValuesBeforeBlock = DS.Set InternalVal
type CommonValues = (ValuesInsideBlock, ValuesBeforeBlock)

type Environment = (FCEnvironment, DS.Set FCRegister)
isFunDynamic ::  Environment -> String-> Bool
isFunDynamic env fun = let
  x = fromJust $ Fce.isIoFunction fun (fst env)
  y = case fromJust $ Fce.functionType fun (fst env) of
    FCPointer ft -> True
    UniversalPointer -> True
    _ -> False
  in
  x || y
isRegisterDynamic :: Environment -> FCRegister ->  Bool
isRegisterDynamic env = flip DS.member (snd env)

isRValueDynamic :: Environment -> FCRValue -> Bool
isRValueDynamic env fcr = case fcr of
  FunCall ft s x0 ->  isFunDynamic' s || any (isRegisterDynamic' . snd) x0
  FCBinOp ft fbo fr fr' -> any isRegisterDynamic' [fr, fr']
  FCUnOp ft fuo fr -> isRegisterDynamic' fr
  FCPhi ft x0 -> True
  BitCast ft ft' fr -> isRegisterDynamic' fr
  Return ft m_fr ->True
  FCEmptyExpr -> True
  FCFunArg ft s n ->True
  FCJump fr -> True
  FCCondJump fr fr' fr2 -> True
  GetField ft s ft' fr -> isRegisterDynamic' fr
  FCLoad ft ft' fr -> isRegisterDynamic' fr
  FCStore ft fr ft' fr' -> any isRegisterDynamic' [fr, fr']
  GetElementPtr {} -> True
  FCSizeOf _ -> False
  FunCallDynamic ft fr x0 -> True
  GetMethod ft s ft' fr -> isRegisterDynamic' fr
  GetMethodTable s ft fr -> isRegisterDynamic' fr
  GetElementPtrArr ft n ft' fr -> isRegisterDynamic' fr
  FCInitObject ft ft' fr -> isRegisterDynamic' fr
  where
    isFunDynamic' = isFunDynamic env
    isRegisterDynamic' = isRegisterDynamic env


convertRValue :: Environment -> FCRValue -> Maybe InternalVal
convertRValue env fcr = if isRValueDynamic env fcr
  then Nothing
  else Just $ IVFCR fcr

_arg :: RegDefMap -> ValRegMap -> Substitution -> Arg
_arg rm vm s = (rm, vm, s)

argInit :: Arg
argInit = _arg DM.empty DM.empty DM.empty
-- substituteRegister :: FCRegister -> FCRegister -> Arg -> Arg
lookupInValue :: InternalVal -> Arg -> Maybe [FCRegister]
lookupInValue inval (_, valreg, _) = DM.lookup inval valreg
addInternalVal :: FCRegister -> InternalVal -> Arg -> Arg
addInternalVal r val (rd, valreg, subs) = (rd,
  DM.insert val (r:[] `fromMaybe` DM.lookup val valreg) valreg,
  subs)
addRegisterDef :: FCRegister -> FCRValue -> Arg -> Arg
addRegisterDef r def (rd, valreg, subs)= _arg (DM.insert r def rd) valreg subs

getValue :: Environment -> (Arg, ValuesInsideBlock) -> FCInstr ->(Arg, ValuesInsideBlock)
getValue env (arg, vib) (reg, fcrvalue) =
  if reg == VoidReg then (arg, vib)
  else
    case convertRValue env fcrvalue of
      Nothing -> (arg, vib)
      Just iv -> (addRegisterDef reg fcrvalue $ addInternalVal reg iv arg,
                  DS.insert iv vib)

substituteRegisters :: Substitution -> FCRValue -> FCRValue
substituteRegisters substitution fcrvalue = case fcrvalue of
  FunCall ft s x0 -> FunCall ft s (map (BiFunctor.second subst) x0)
  FCBinOp ft fbo fr fr' -> FCBinOp ft fbo (subst fr) (subst fr')
  FCUnOp ft fuo fr -> FCUnOp ft fuo (subst fr)
  FCPhi ft x0 -> FCPhi ft (map (BiFunctor.first subst) x0)
  Return ft m_fr -> Return ft (subst <$> m_fr)
  FCEmptyExpr -> FCEmptyExpr
  FCFunArg ft s n -> fcrvalue
  FCJump fr -> FCJump (subst fr)
  FCCondJump fr fr' fr2 ->  FCCondJump (subst fr) (subst fr') (subst fr2)
  BitCast ft ft' fr -> BitCast ft ft' (subst fr)
  GetField ft s ft' fr -> GetField ft s ft' (subst fr)
  FCLoad ft ft' fr -> FCLoad ft ft' (subst fr)
  FCStore ft fr ft' fr' -> FCStore ft (subst fr) ft' (subst fr')
  GetElementPtr ft x ft' fr' -> GetElementPtr ft x ft' (subst fr')
  FCSizeOf _ -> fcrvalue
  FunCallDynamic ft fr x0 -> FunCallDynamic ft (subst fr) x0
  GetMethod ft s ft' fr -> GetMethod ft s ft' (subst fr)
  GetMethodTable s ft fr -> GetMethodTable s ft (subst fr)
  GetElementPtrArr ft n ft' fr -> GetElementPtrArr ft n ft' (subst fr)
  FCInitObject ft ft' fr -> FCInitObject ft ft' (subst fr)
  where
    subst :: FCRegister -> FCRegister
    subst reg = reg `fromMaybe` DM.lookup reg  substitution

type InternalValEnv = DM.Map InternalVal FCRegister
type LcseArg = (InternalValEnv, Substitution)


lcseInstr :: Environment -> [FCInstr] -> (LcseArg, [FCInstr]) -> (LcseArg, [FCInstr])
lcseInstr env instrs (lcsearg, res) = case instrs of
  [] -> (lcsearg, res)
  ((reg, rvalue):xs) ->
    lcseInstr env xs
      (case convertRValue env rvalue' of
          Nothing -> (lcsearg, (reg, rvalue'):res)
          Just iv -> case iv `DM.lookup` map of
            Nothing -> ((DM.insert iv reg map, substitution), (reg, rvalue'):res)
            Just reg' -> ((map, DM.insert reg reg' substitution), res))
    where
      (map, substitution) = lcsearg
      rvalue' = substituteRegisters substitution rvalue

lcseBlock :: Environment -> FCBlock -> LcseArg -> (LcseArg, FCBlock)
lcseBlock env block arg = case block of
  FCNamedSBlock s x0 x1 -> (lcsearg', FCNamedSBlock s x0'' x1)
    where
      (lcsearg', x0') = lcseInstr env x0 (arg, [])
      x0'' = reverse x0'
  FCComplexBlock s fbs x0 -> let
    (lcseargs', fbs') = foldl' (\(lcsearg, rest) block -> BiFunctor.second (:rest) (lcseBlock env block lcsearg))
      (arg, []) fbs
    fbs'' = reverse fbs'
    in
    (lcseargs', FCComplexBlock s fbs'' x0)
  FCCondBlock s fc fr fs ff fp x0 -> let
    (arg', fc') = lcseBlock env fc arg
    (valenv, subs) = arg'
    (_, fs') = lcseBlock env fs arg'
    (_, ff') = lcseBlock env ff arg'
    in
      (arg', FCCondBlock s fc' fr fs' ff' fp x0)
  FCPartialCond s fc fr fs ff x0 -> let
      (arg', fc') = lcseBlock env fc arg
      (_, fs') = lcseBlock env fs arg'
      (_, ff') = lcseBlock env ff arg'
    in
      (arg', FCPartialCond s fc' fr fs' ff' x0)
  FCWhileBlock s fp fc fr fs str x0 -> let
    (arg', fp') = lcseBlock env fp arg
    (arg'', fc') = lcseBlock env fc arg
    (_, fs') = lcseBlock env fs arg''
    in
    (arg'', FCWhileBlock s fp' fc' fr fs' str x0)

gcse :: Environment -> (Arg,CommonValues, FCBlock) -> (Arg, CommonValues, FCBlock)
gcse env (args, (vib, vbb), block) =
  case block of
    FCNamedSBlock s x0 x1 -> let
      (args', vib') = foldl' getValue' (args, vib) x0
      in
      (args', (vib', vbb), block)
    FCComplexBlock s fbs x0 ->
      let
        rfbs = reverse fbs
        (arg', (acc, vib',vbb'), fbs') = foldl' (\(args, (acc, _ ,vbb), res) block ->
                 let
                   (args', (vib', _), block') = gcse' (args, (DS.empty, vbb), block)
                 in
                   (args', (DS.union acc vib', undefined, DS.union vib' vbb), block':res))
               (args, (DS.empty, DS.empty, vbb), []) rfbs
        in
        (arg', (acc, vbb'), FCComplexBlock s fbs' x0)
    FCCondBlock s fc fr fs ff fp x0 ->
      let
        (argsf, (vibf, _), ff') = gcse' (args, (DS.empty, DS.empty), ff)
        (argss, (vibs, _), fs') = gcse' (argsf, (DS.empty, DS.empty), fs)
        (argsc, (vibc, _), fc') = gcse' (argss, (DS.empty, DS.empty), fc)
        vib' = DS.union vibf $ DS.union vibs vibc
        (args', list) = DS.foldl' eliminate (argsc, []) (DS.intersection vbb vib')
        (args'', list') = DS.foldl' eliminate (args', list) (DS.intersection vibs vibf)
        newCondBlock = FCCondBlock (if null list' then s else "") fc' fr fs' ff' fp x0
        newBlock = if null list' then newCondBlock
          else
          FCComplexBlock s [FCNamedSBlock "" list' (), newCondBlock] ()
      in
        (args'', (vibc, vbb), newBlock)
    FCPartialCond s fc fr fs ff x0 -> let
        (argsf, (vibf, _), _) = gcse' (args, (DS.empty, DS.empty), ff)
        (argss, (vibs, _), _) = gcse' (argsf, (DS.empty, DS.empty), fs)
        (argsc, (vibc, _), _) = gcse' (argss, (DS.empty, DS.empty), fc)
        vib' = DS.union vibf $ DS.union vibs vibc
      in
      (argsc, (vib', vbb), block)
    FCWhileBlock s fp fc fr fs str x0 -> let
      (args', _, fs') = gcse' (args, (DS.empty , DS.empty), fs)
      block' = FCWhileBlock s fp fc fr fs' str x0
      in
      (args', (vib, vbb), block')
  where
    getValue' = getValue env
    gcse' = gcse env
    eliminate :: (Arg, [FCInstr]) -> InternalVal -> (Arg, [FCInstr])
    eliminate (arg, list) val =
      let
      (rd, valreg, subs) = arg
      regs =  error "Value in set not in map" `fromMaybe` (val `DM.lookup` valreg)
      (firstR, rest) = case regs of
                 (r1:r2:rest) -> (r1, r2:rest)
                 _ -> error "List has less than two elements"
      definition = error "Value in set not in map" `fromMaybe` DM.lookup firstR rd
      reg' = case firstR of
        (Reg s) -> Reg ("g" ++ s)
        _ -> undefined
      arg' = _arg
        (DM.insert reg' definition rd)
        (DM.insert val [reg'] valreg)
        (foldl' (\map r -> DM.insert r reg' map) subs regs)
      list' = (reg', definition):list
      in
      (arg', list')


getDynamicRegisters :: FCEnvironment -> DS.Set FCRegister -> FCBlock -> DS.Set FCRegister
getDynamicRegisters _ _ _ = DS.empty

gcseOptimizeProd :: FCEnvironment -> FCBlock -> FCBlock
gcseOptimizeProd dynFun block =
  snd (gcse' (argInit,block))
  where
    env = (dynFun, getDynamicRegisters dynFun DS.empty block)
    gcse' :: (Arg, FCBlock) -> (Arg, FCBlock)
    gcse' (args, block) =
      let
        (args', _, block') = gcse env (args, (DS.empty, DS.empty), block)
        (_, _, subs) = args'
      in
        if DM.null subs then (args', block')
        else
          let
            lcseArgs :: LcseArg
            lcseArgs = (DM.empty, subs)
            (_, block) = lcseBlock env block' lcseArgs
            in
            gcse' (argInit, block)

gcseOptimizeTest :: DS.Set String-> FCBlock -> FCBlock
gcseOptimizeTest x = id

gcseOptimize = gcseOptimizeProd
