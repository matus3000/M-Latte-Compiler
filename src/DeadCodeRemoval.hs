{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
module DeadCodeRemoval where

import Data.List (foldl', foldr, insert)
import qualified Data.Set as DS
import FCCompilerTypes
import Data.Maybe (fromMaybe, fromJust, catMaybes, mapMaybe)
import qualified Control.Arrow as BiFunctor
import qualified Data.Bifunctor
import FCCompiler.FCEnvironment (FCEnvironment)
import FCCompiler.FCEnvironment as Fce

type DynamicFunctions = FCEnvironment
-- type LoopInfo
type Environment = (DynamicFunctions)


isRValDynamic :: DynamicFunctions -> DS.Set FCRegister -> FCRValue -> Bool
isRValDynamic env set fcrval = case fcrval of
  FunCall ft s x1 -> isPointer ft || fromJust (Fce.isIoFunction s env) || modifiesImportantThings s x1
  FCStore ft fr ft' fr' -> True
  Return ft m_fr -> True
  FCJump fr -> True
  FCCondJump fr fr' fr2 -> True
  _ -> False
  where
    isPointer :: FCType -> Bool
    isPointer = \case
      FCPointer ft -> True
      UniversalPointer -> True
      _ -> False
    modifiesImportantThings :: String -> [(FCType, FCRegister)] -> Bool
    modifiesImportantThings s args =
      let
        x = fromJust $ Fce.getMutabaleArgsOfFunction s env
        x' = zip args x
        modifiedArgs = mapMaybe (\(x,y)-> if y then Just x else Nothing) x'
      in
        (not $ null modifiedArgs)
-- modifiesVar 

isBlockDynamic :: DynamicFunctions -> DS.Set FCRegister -> FCBlock -> Bool
isBlockDynamic env regs = \case
  FCNamedSBlock s x0 x1 -> any (\(reg, x) -> reg `DS.member` regs || isRValDynamic env regs x) x0
  FCComplexBlock s fbs x0 -> any (isBlockDynamic env regs) fbs
  FCCondBlock s fb fr fb' fb2 fb3 x0 -> any (isBlockDynamic env regs) [fb, fb', fb2, fb3]
  FCPartialCond s fb fr fb' fb2 x0 -> any (isBlockDynamic env regs) [fb, fb', fb2]
  FCWhileBlock s fb fb' fr fb2 str x0 -> True


insertReg :: DS.Set FCRegister -> FCRegister -> DS.Set FCRegister
insertReg set x = case x of
  Reg s -> DS.insert x set
  _ -> set

getVars :: DS.Set FCRegister -> FCRValue -> DS.Set FCRegister
getVars set fcrvalue = case fcrvalue of
  FunCall ft s x1 -> foldl' insertReg set (map snd x1)
  FCBinOp ft fbo fr fr' -> foldl' insertReg set [fr, fr']
  FCUnOp ft fuo fr -> insertReg set fr
  FCPhi ft x1 -> foldl' insertReg set (map fst x1)
  Return ft m_fr -> insertReg set (VoidReg `fromMaybe` m_fr)
  FCEmptyExpr -> set
  FCFunArg ft s n -> undefined
  FCJump fr -> insertReg set fr
  FCCondJump fr fr' fr2 -> foldl' insertReg set [fr, fr', fr2]
  BitCast ft ft' fr -> insertReg set fr
  GetField ft s ft' fr -> insertReg set fr
  FCLoad ft ft' fr -> insertReg set fr
  FCStore ft fr ft' fr' -> foldl' insertReg set [fr, fr']

getNewDynamicVars :: DynamicFunctions -> (DS.Set FCRegister, DS.Set FCRegister) -> FCBlock
      -> (DS.Set FCRegister, DS.Set FCRegister)
getNewDynamicVars env sets block =
  let
    f :: (DS.Set FCRegister, DS.Set FCRegister) -> FCInstr -> (DS.Set FCRegister, DS.Set FCRegister)
    f (whole, new) instr@(reg, x)
      | DS.member reg whole =
        (let
            helper = getVars DS.empty x
            new' = DS.union new (DS.difference helper whole)
          in
            (DS.union whole new', new'))
      | isRValDynamic env whole x =
        (let
            helper = getVars (insertReg DS.empty reg) x
            new' = DS.union new (DS.difference helper whole)
          in
            (DS.union whole new', new'))
      | otherwise =
        (whole, new)
  in case block of
       FCNamedSBlock s x0 x1 -> foldl' f sets (reverse x0)
       FCComplexBlock s fbs x0 -> foldl' (getNewDynamicVars env) sets (reverse fbs)
       FCCondBlock s fb fr fb' fb2 fb3 x0 -> let
         init = if not (DS.member fr (fst sets)) &&
                    any (isBlockDynamic env (fst sets)) [fb3, fb2, fb', fb]
            then Data.Bifunctor.bimap (DS.insert fr) (DS.insert fr) sets
            else sets
          in
            foldl' (getNewDynamicVars env) init [fb3, fb2, fb', fb]
       FCPartialCond s fb fr fb' fb2 x0 -> let
          init = if not (DS.member fr (fst sets)) &&
            any (isBlockDynamic env (fst sets)) [fb2, fb', fb]
            then Data.Bifunctor.bimap (DS.insert fr) (DS.insert fr) sets
            else sets
          in
            foldl' (getNewDynamicVars env) init [fb2, fb', fb]
       FCWhileBlock s fb fb' fr fb2 str x0 -> let
         init :: (DS.Set FCRegister, DS.Set FCRegister)
         init = if not (DS.member fr (fst sets))
           then Data.Bifunctor.bimap (DS.insert fr) (DS.insert fr) sets
           else sets
         (nwhole, nnew) = foldl' (getNewDynamicVars env) init [fb, fb', fb2]
          in
            if DS.null nnew then (nwhole, nnew)
            else getNewDynamicVars env (nwhole, DS.empty) block

removeDeadCodeInstr2 :: DynamicFunctions -> DS.Set FCRegister -> [FCInstr] -> ([FCInstr])
removeDeadCodeInstr2 env set x = foldl'
  (\(rest) instr@(reg, x) ->
      if DS.member reg set || isRValDynamic env set x then instr:rest else rest)
  []
  (reverse x)


removeDeadCode2 :: DynamicFunctions -> DS.Set FCRegister -> FCBlock -> FCBlock
removeDeadCode2 env set block = case block of
  FCNamedSBlock s x0 x1 -> (\x0 -> FCNamedSBlock s x0 x1) (removeDeadCodeInstr2 env set x0)
  FCComplexBlock s fbs x0 -> (\fbs -> FCComplexBlock s fbs x0) $
                                map (removeDeadCode2 env set) fbs
  FCCondBlock s fc fr fs ff fp x0 -> let
      fc' = removeDeadCode2 env set fc
      fs'  = removeDeadCode2 env set fs
      ff' = removeDeadCode2 env set ff
      fp' = removeDeadCode2 env set fp
    in
      if not (sensiblePhiBlock fp) && not (any importantBlock [fs, ff]) then
        if importantBlock fc then fc' else FCNamedSBlock s [] x0
      else
        FCCondBlock s fc' fr fs' ff' fp' x0
  FCPartialCond s fc fr fs ff x0 -> let
      fc' = removeDeadCode2 env set fc
      fs'  = removeDeadCode2 env set fs
      ff' = removeDeadCode2 env set ff
      in
        FCPartialCond s fc' fr fs' ff' x0
  FCWhileBlock s fp fc fr fs str x0 -> let
      fc' = removeDeadCode2 env set fc
      fs'  = removeDeadCode2 env set fs
      fp' = removeDeadCode2 env set fp
    in
      FCWhileBlock s fp' fc' fr fs' str x0
  where
    sensiblePhiBlock :: FCBlock -> Bool
    sensiblePhiBlock block = case block of
      FCNamedSBlock s x0 x1 -> any (\(x,y) -> case y of
        FunCall ft str x3 -> False
        FCBinOp ft fbo fr fr' -> False
        FCUnOp ft fuo fr -> False
        FCPhi ft x3 -> True
        BitCast ft fr ft' -> False
        -- GetPointer ft fr fr' -> False
        Return ft m_fr -> error "Ret in Phi"
        FCEmptyExpr -> False
        FCFunArg ft str n -> False
        FCJump fr -> False
        FCCondJump fr fr' fr2 -> False
        _ -> False
        ) x0
      FCComplexBlock s fbs x0 -> any sensiblePhiBlock fbs
      _ -> error "uselessPhiBlock"
    importantBlock :: FCBlock -> Bool
    importantBlock block = case block of
      FCNamedSBlock s x0 x1 -> any (\(x,y)-> case y of
        FCEmptyExpr -> False
        FCFunArg ft str n -> False
        FCJump fr -> False
        FCCondJump fr fr' fr2 -> False
        _ -> True) x0
      FCComplexBlock s fbs x0 -> any importantBlock fbs
      FCCondBlock s fb fr fb' fb2 fb3 x0 -> True -- Idziemy od dołu ku górze. Stąd gdy ponownie zstąpimy to wiemy, że nie jest pusty.
      FCPartialCond s fb fr fb' fb2 x0 -> True
      FCWhileBlock s fb fb' fr fb2 str x0 -> True

removeDeadCode :: DynamicFunctions -> DS.Set FCRegister -> FCBlock -> (DS.Set FCRegister, FCBlock)
removeDeadCode env _ block =
  let
    (dynamicRegisters, _) = getNewDynamicVars env (DS.empty, DS.empty) block
  in
    (DS.empty, removeDeadCode2 env dynamicRegisters block)
