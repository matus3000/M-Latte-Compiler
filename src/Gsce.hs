module Gsce where

-- TO DO
-- Zamienić Venv na zwykłą mapę

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


data InternalVal = IVFCR FCRValue
  deriving (Eq, Ord)

type FCInternal1 = FCBlock' (FCInstr) ((DS.Set InternalVal))
type RegDefMap = DM.Map FCRegister FCRValue
type ValRegMap = DM.Map InternalVal [FCRegister]
type Substitution = DM.Map FCRegister FCRegister

type Arg = (RegDefMap, ValRegMap, Substitution)
type ValuesInsideBlock = DS.Set InternalVal
type ValuesBeforeBlock = DS.Set InternalVal
type CommonValues = (ValuesInsideBlock, ValuesBeforeBlock)

type Environment = (DS.Set String, DS.Set FCRegister)
isFunDynamic ::  Environment -> String-> Bool
isFunDynamic env fun = DS.member fun (fst env)
isRegisterDynamic :: Environment -> FCRegister ->  Bool
isRegisterDynamic env = flip DS.member (snd env)

isRValueDynamic :: Environment -> FCRValue -> Bool
isRValueDynamic env fcr = case fcr of
  FunCall ft s x0 ->  (isFunDynamic' s || any (isRegisterDynamic' . snd) x0)
  FCBinOp ft fbo fr fr' -> any isRegisterDynamic' [fr, fr']
  FCUnOp ft fuo fr -> isRegisterDynamic' fr
  FCPhi ft x0 -> True
  BitCast ft fr ft' -> isRegisterDynamic' fr
  GetPointer ft fr fr' -> any isRegisterDynamic' [fr, fr']
  Return ft m_fr ->True
  FCEmptyExpr -> True
  FCFunArg ft s n ->True
  FCJump fr -> True
  FCCondJump fr fr' fr2 -> True
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
  where
    isRValueDynamic' = isRValueDynamic env

substituteRegisters :: Substitution -> FCRValue -> FCRValue
substituteRegisters substitution fcrvalue = case fcrvalue of
  FunCall ft s x0 -> FunCall ft s (map (BiFunctor.second subst) x0)
  FCBinOp ft fbo fr fr' -> FCBinOp ft fbo (subst fr) (subst fr')
  FCUnOp ft fuo fr -> FCUnOp ft fuo (subst fr)
  FCPhi ft x0 -> FCPhi ft (map (BiFunctor.first subst) x0)
  BitCast ft fr ft' -> BitCast ft (subst fr) ft'
  GetPointer ft fr fr' -> GetPointer ft (subst fr) (subst fr')
  Return ft m_fr -> Return ft (subst <$> m_fr)
  FCEmptyExpr -> FCEmptyExpr
  FCFunArg ft s n -> fcrvalue
  FCJump fr -> FCJump (subst fr)
  FCCondJump fr fr' fr2 ->  FCCondJump (subst fr) (subst fr') (subst fr2)
  where
    subst :: FCRegister -> FCRegister
    subst reg = reg `fromMaybe` DM.lookup reg  substitution

type InternalValEnv = VE.VarEnv InternalVal FCRegister
type LsceArg = (InternalValEnv, Substitution)


lsceInstr :: Environment -> [FCInstr] -> (LsceArg, [FCInstr]) -> (LsceArg, [FCInstr])
lsceInstr env instrs (lscearg, res) = case instrs of
  [] -> (lscearg, res)
  ((reg, rvalue):xs) ->
    lsceInstr env xs
      (case convertRValue env rvalue' of
          Nothing -> (lscearg, (reg, rvalue'):res)
          Just iv -> case iv `VE.lookupVar` map of
            Nothing -> ((VE.declareVar iv reg map, substitution), (reg, rvalue'):res)
            Just reg' -> ((map, DM.insert reg reg' substitution), res))
    where
      (map, substitution) = lscearg
      rvalue' = substituteRegisters substitution rvalue

lsceBlock :: Environment -> FCBlock -> LsceArg -> (LsceArg, FCBlock)
lsceBlock env block arg = case block of
  FCNamedSBlock s x0 x1 -> (lscearg', FCNamedSBlock s x0' x1)
    where
      (lscearg', x0') = lsceInstr env x0' (arg, [])
      x0'' = reverse x0'
  FCComplexBlock s fbs x0 -> let
    (lsceargs', fbs') = foldl' (\(lscearg, rest) block -> BiFunctor.second (:rest) (lsceBlock env block lscearg))
      (arg, []) fbs
    fbs'' = reverse fbs'
    in
    (lsceargs', FCComplexBlock s fbs'' x0)
  FCCondBlock s fc fr fs ff fp x0 -> let
    (arg', fc') = lsceBlock env fc arg
    (valenv, subs) = arg'
    (_, fs') = lsceBlock env fs arg'
    (_, ff') = lsceBlock env ff arg'
    in
      (arg', FCCondBlock s fc' fr fs' ff' fp x0)
  FCPartialCond s fc fr fs ff x0 -> let
      (arg', fc') = lsceBlock env fc arg
      (valenv, subs) = arg'
      (_, fs') = lsceBlock env fs arg'
      (_, ff') = lsceBlock env ff arg'
    in
      (arg', FCPartialCond s fc' fr fs' ff' x0)
  FCWhileBlock s fb fb' fr fb2 str x0 -> (arg, block)
      
gsce :: Environment -> (Arg,CommonValues, FCBlock) -> (Arg, CommonValues, FCBlock)
gsce env (args, (vib, vbb), block) =
  case block of
    FCNamedSBlock s x0 x1 -> let
      (args, vib) = foldl' getValue' (args, vib) x0
      (args', list) = DS.foldl' eliminate (args, []) (DS.intersection vib vbb)
      newblock = FCNamedSBlock (if null list then s else "") x0 x1
      in
      if null list
      then (args', (vib, vbb), newblock)
      else (args', (vib, vbb), FCComplexBlock "" (FCNamedSBlock "" list ():[newblock]) ())
    FCComplexBlock s fbs x0 ->
      let
        rfbs = reverse fbs
        (arg', (vib',vbb'), fbs') = foldl' (\(args, (vib,vbb), res) block ->
                 let
                   (args', (vib', vbb'), block') = gsce' (args, (vib, vbb), block)
                 in
                   (args', (DS.empty, DS.union vib' vbb), block':res))
               (args, (vib, vbb), []) rfbs
        in
        (arg', (vib',vbb'), FCComplexBlock s fbs' x0)
    FCCondBlock s fc fr fs ff fp x0 ->
      let
        (argsf, (vibf, _), ff') = gsce' (args, (DS.empty, DS.empty), ff)
        (argss, (vibs, _), fs') = gsce' (argsf, (DS.empty, DS.empty), fs)
        (argsc, (vibc, _), fc') = gsce' (argss, (DS.empty, DS.empty), fc)
        vib' = DS.union vibf $ DS.union vibs vibc
        (args', list) = DS.foldl' eliminate (argsc, [])
          (DS.intersection vbb vib')
        newCondBlock = FCCondBlock (if null list then s else "") fc' fr fs' ff' fp x0
        newBlock = if null list then newCondBlock
          else
          FCComplexBlock s [FCNamedSBlock "" list (), newCondBlock] ()
      in
        (args', (vib', vbb), newBlock)
    FCPartialCond s fc fr fs ff x0 -> let
        (argsf, (vibf, _), ff') = gsce' (args, (DS.empty, DS.empty), ff)
        (argss, (vibs, _), fs') = gsce' (argsf, (DS.empty, DS.empty), fs)
        (argsc, (vibc, _), fc') = gsce' (argss, (DS.empty, DS.empty), fc)
        vib' = DS.union vibf $ DS.union vibs vibc
        newCondBlock = FCPartialCond (if null list then s else "") fc' fr fs' ff' x0
        (args', list) = DS.foldl' eliminate (argsc, [])
          (DS.intersection vbb vib')
        newBlock = if null list then newCondBlock
          else
          FCComplexBlock s [FCNamedSBlock "" list (), newCondBlock] ()
      in
        (args', (vib', vbb), newBlock)

    FCWhileBlock s fb fb' fr fb2 str x0 -> (args, (vib, vbb), block)
  where
    getValue' = getValue env
    gsce' = gsce env
    eliminate :: (Arg, [FCInstr]) -> InternalVal -> (Arg, [FCInstr])
    eliminate (arg, list) val = let
      (rd, valreg, subs) = arg
      regs =  error "Value in set not in map" `fromMaybe` (val `DM.lookup` valreg)
      (fst, rest) = case regs of
                 (fst:snd:rest) -> (fst, snd:rest)
                 _ -> error "List has less than two elements"
      definition = error "Value in set not in map" $ DM.lookup fst rd
      reg' = case fst of
        (Reg s) -> Reg ("g" ++ s)
        _ -> undefined
      arg' = _arg
        (DM.insert reg' definition rd)
        (DM.delete val valreg)
        (foldl' (\map r -> DM.insert r reg' map) subs regs)
      list' = (reg', definition):list
      in
      (arg', list')


getDynamicRegisters :: (DS.Set String)-> DS.Set FCRegister -> (FCBlock) -> DS.Set FCRegister

getDynamicRegisters dfuns set block = case block of
  FCNamedSBlock s x0 x1 -> foldl' (\set (reg, fcrvalue) ->
                                     if reg == VoidReg then set
                                     else if isRValueDynamic (dfuns, set) fcrvalue
                                          then DS.insert reg set
                                          else set) (set) x0
  FCComplexBlock s fbs x0 -> foldl' getDynamicRegisters' set fbs
  FCCondBlock s fb fr fb' fb2 fb3 x0 -> foldl' getDynamicRegisters' set [fb, fb', fb2, fb3]
  FCPartialCond s fb fr fb' fb2 x0 -> foldl' getDynamicRegisters' set [fb, fb', fb2]
  FCWhileBlock s fb fb' fr fb2 str x0 -> set
  where
    getDynamicRegisters' = getDynamicRegisters dfuns

gsceOptimize :: DS.Set String-> FCBlock -> FCBlock
gsceOptimize dynFun block =
  undefined
  where
    env = (dynFun, getDynamicRegisters dynFun DS.empty block)
    gsce' :: (Arg, FCBlock) -> (Arg, FCBlock)
    gsce' (args, block) =
      let
        (args, _, block') = gsce env (args, (DS.empty, DS.empty), block)
        (_, _, subs) = args
      in
        if DM.null subs then (args, block')
        else undefined
