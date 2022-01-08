module LLVMCompiler where

import Prelude
import Data.List (foldl')
import FCCompilerTypes
import FCCompiler (bbaddInstr)

data LLVMInstr = FC_ FCInstr | LL String
data LLVMFunDecl = LLVMFunDecl String FCType [(FCType, FCRegister)] [LLVMInstr]
data LLVMModule = {functions::LLVMFunDecl}
type LLVMBlockBuilder = [LLVMInstr]

dummyReturn :: FCType -> LLVMInstr
dummyReturn = undefined

changesFlow :: LLVMInstr->Bool
changesFlow x = case x of
  FC_ (fr, fv) -> case fv of
    Return {} -> True
    FCJump {} -> True
    FCCondJump {} -> True
    _ -> False
  LL s -> False

bbAddInstr :: LLVMBlockBuilder -> LLVMInstr -> LLVMBlockBuilder
bbAddInstr = flip (:)

toLLVMBuilder :: LLVMBlockBuilder -> FCBlock -> LLVMBlockBuilder
toLLVMBuilder up block = case block of
  FCNamedSBlock s x0 x1 -> foldl' bbAddInstr up' (map convert x0)
  FCComplexBlock s fbs x0 -> foldl' toLLVMBuilder up' fbs
  FCCondBlock s fc fr fs ff fp x0 -> let
    bbc = toLLVMBuilder up' fc
    bbfr = bbAddInstr bbc (FC_ (VoidReg, conditionalJump fr (Et (bname fs)) (Et (bname ff))))
    bbfs = toLLVMBuilder bbfr fs
    bbff = toLLVMBuilder bbfs ff
    in
    toLLVMBuilder bbff fp
  FCPartialCond s fc fr fs ff x0 -> let
    bbc = toLLVMBuilder up' fc
    bbfr = bbAddInstr bbc (FC_ (VoidReg, conditionalJump fr (Et (bname fs)) (Et (bname ff))))
    bbfs = toLLVMBuilder bbfr fs
    bbff = toLLVMBuilder bbfs ff
    in
    bbff
  FCWhileBlock s fp fc fr fs str x0 -> let
    bbw = bbAddInstr up' (FC_ (VoidReg, jump (bname fp)))
    bbfs = bbAddInstr (toLLVMBuilder bbw fs) (FC_ (VoidReg, jump (bname fp)))
    bbfp = toLLVMBuilder bbfs fp
    bbfc = toLLVMBuilder bbfp fc
    res = bbAddInstr bbfc (FC_ (VoidReg, conditionalJump fr (Et $ bname fs) (Et str)))
    in
    res
  where
    up' = bbAddInstr up (LL (bname block))
    convert :: FCInstr -> LLVMInstr
    convert = FC_



llvmBuildBuilder :: FCType -> LLVMBlockBuilder -> [LLVMInstr]
llvmBuildBuilder rettype bb = let
  bb' = bbAddInstr bb (dummyReturn rettype)
  in
    f bb' []
  where
    f :: LLVMBlockBuilder -> [LLVMInstr] -> [LLVMInstr]
    f bb rest = case bb of
      [] -> rest
      [l1] -> l1:rest
      (l1:l2:l3) ->
        case (l1, l2) of
          (LL s1, LL s2) -> f (FC_ (VoidReg, jump s1):l2:l3) (l1:rest)
          _ -> if changesFlow l1 && changesFlow l2
               then f (l2:l3) rest
               else f (l2:l3) (l1:rest)
