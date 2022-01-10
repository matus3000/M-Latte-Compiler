{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
module DeadCodeRemoval where

import Data.List (foldl', foldr)
import qualified Data.Set as DS
import FCCompilerTypes
import Data.Maybe (fromMaybe)
import qualified Control.Arrow as BiFunctor
import qualified Data.Bifunctor

type DynamicFunctions = DS.Set String
-- type LoopInfo
type Environment = (DynamicFunctions)

isRValDynamic :: DynamicFunctions -> FCRValue -> Bool
isRValDynamic env fcrval = case fcrval of
  FunCall ft s x1 -> DS.member s env
  Return ft m_fr -> True
  FCJump fr -> True
  FCCondJump fr fr' fr2 -> True
  _ -> False

isBlockDynamic :: DynamicFunctions -> DS.Set FCRegister -> FCBlock -> Bool
isBlockDynamic env regs = \case
  FCNamedSBlock s x0 x1 -> any (\(reg, x) -> reg `DS.member` regs || isRValDynamic env x) x0
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
      BitCast ft fr ft' -> insertReg set fr
      GetPointer ft fr fr' -> foldl' insertReg set  [fr, fr']
      Return ft m_fr -> insertReg set (VoidReg `fromMaybe` m_fr)
      FCEmptyExpr -> set
      FCFunArg ft s n -> undefined
      FCJump fr -> insertReg set fr
      FCCondJump fr fr' fr2 -> foldl' insertReg set [fr, fr', fr2]



removeDeadCodeInstr :: DynamicFunctions -> DS.Set FCRegister -> [FCInstr] -> (DS.Set FCRegister, [FCInstr])
removeDeadCodeInstr env set x = foldl'
  (\(!set, rest) instr@(reg, x) ->
      if DS.member reg set then (getVars set x, instr:rest)
      else
        if isRValDynamic env x
        then (f  (getVars set x) reg,instr:rest)
        else (set, rest))
  (set, [])
  (reverse x)
  where
    f :: DS.Set FCRegister -> FCRegister -> DS.Set FCRegister
    f set x = case x of
      Reg s -> DS.insert x set
      _ -> set


removeUselessBlocks :: DynamicFunctions -> DS.Set FCRegister  -> FCBlock -> (DS.Set FCRegister, FCBlock)
removeUselessBlocks env set block = case block of
  FCCondBlock s fc fr fs ff fp x0 ->
    if not (sensiblePhiBlock fp) && not (any importantBlock [fs, ff]) then
      let
        (set', fc') = removeDeadCode env set fc
      in
        if (importantBlock fc') then (set', fc')
        else (set', FCNamedSBlock s [] x0)
    else
      let
        (set', fc') = removeDeadCode env (DS.insert fr set) fc
      in
        (set', FCCondBlock s fc' fr fs ff fp x0)
  where
    sensiblePhiBlock :: FCBlock -> Bool
    sensiblePhiBlock block = case block of
      FCNamedSBlock s x0 x1 -> any (\(x,y) -> case y of
        FunCall ft str x3 -> False
        FCBinOp ft fbo fr fr' -> False
        FCUnOp ft fuo fr -> False
        FCPhi ft x3 -> True
        BitCast ft fr ft' -> False
        GetPointer ft fr fr' -> False
        Return ft m_fr -> error "Ret in Phi"
        FCEmptyExpr -> False
        FCFunArg ft str n -> False
        FCJump fr -> False
        FCCondJump fr fr' fr2 -> False
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

-- removeDeadCode :: DynamicFunctions -> DS.Set FCRegister -> FCBlock -> (DS.Set FCRegister, FCBlock)
-- removeDeadCode env set block = case block of
--   FCNamedSBlock s x0 x1 -> BiFunctor.second (\x0 -> FCNamedSBlock s x0 x1) (removeDeadCodeInstr env set x0)
--   FCComplexBlock s fbs x0 -> BiFunctor.second (\fbs -> FCComplexBlock s fbs x0) $
--      foldl' f (set, []) (reverse fbs)
--   FCCondBlock s fc fr fs ff fp x0 -> let
--     (setFP, fp') = removeDeadCode env set fp
--     setfp' = applyToBlockFC getPhiArgs setFP fp'
--     (setfs, fs') = removeDeadCode env setfp' fs
--     (setff, ff') = removeDeadCode env setfp' ff
--     set' = DS.union setfs setff
--     in
--       removeUselessBlocks env set' (FCCondBlock s fc fr fs' ff' fp' x0)
--   FCPartialCond s fc fr fs ff x0 -> let
--     (setfs, fs') = removeDeadCode env set fs
--     (setff, ff') = removeDeadCode env set ff
--     set' = DS.insert fr $ DS.union setfs setff
--     (res, fc') = removeDeadCode env set' fc
--     in
--     (res, FCPartialCond s fc' fr fs' ff' x0)
--   FCWhileBlock s fp fc fr fs str x0 -> let
--     set' = DS.insert fr set
--     (setFC,fc') = removeDeadCode env set' fc
--     (setFP, fp') = removeDeadCode env setFC fp
--     setFC' = applyToBlockFC getPhiArgs setFC fp'
--     (setFS, fs') = removeDeadCode env setFC' fs
--     in
--     (setFS, FCWhileBlock s fp' fc' fr fs' str x0)
--   where
--     f :: (DS.Set FCRegister, [FCBlock]) -> FCBlock -> (DS.Set FCRegister, [FCBlock])
--     f (set, rest) block = BiFunctor.second (:rest) $ removeDeadCode env set block
--     getPhiArgs ::  DS.Set FCRegister -> FCRValue -> DS.Set FCRegister
--     getPhiArgs set x = case x of
--       FCPhi ft x1 -> foldl' (\set (x, y) -> DS.insert x set) set x1
--       _ -> set
--     applyToBlockFC :: (a -> FCRValue -> a) -> a -> FCBlock -> a
--     applyToBlockFC f a block = case block of
--       FCNamedSBlock s x1 x2 -> foldl f' a x1
--       FCComplexBlock s fbs x1 -> foldl (applyToBlockFC f) a fbs
--       _ -> error "applyToBlockFC"
--       where
--         f' = \x y -> f x (snd y)
--     buildDynamic :: FCBlock -> FCBlock -> DS.Set String -> DS.Set String
--     buildDynamic block1 block2 set = undefined

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
      | isRValDynamic env x =
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
      if DS.member reg set then (instr:rest)
      else
        if isRValDynamic env x
        then (instr:rest)
        else rest)
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
        GetPointer ft fr fr' -> False
        Return ft m_fr -> error "Ret in Phi"
        FCEmptyExpr -> False
        FCFunArg ft str n -> False
        FCJump fr -> False
        FCCondJump fr fr' fr2 -> False
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
