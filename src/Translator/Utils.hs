{-# LANGUAGE LambdaCase #-}
module Translator.Utils (preprocessMethodsInClasses) where

import IDefinition
import Translator.TranslatorEnvironment
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM

preprocessMethodsInClasses :: DM.Map String FunctionData -> ClassDef -> ClassDef
preprocessMethodsInClasses senv classdef = let
  cmethods = case classdef of
    ClassDef ma id cmds cmethods -> cmethods
    ClassDefExtends ma id id' cmds cmdethods -> cmdethods
  cmethods' = map (\(MethodDecl ma ty id args iblock) -> MethodDecl ma ty id args (f iblock)) cmethods
  f :: Block -> Block
  f iblock = let
    f' :: Stmt -> Stmt
    f' s = case s of
      Empty ma -> s
      BStmt ma eb -> BStmt ma (f eb)
      Decl ma ty its -> Decl ma ty (map i its)
      Ass ma lv ex -> Ass ma lv (e ex)
      Incr ma lv -> s
      Decr ma lv -> s
      Ret ma ex -> Ret ma (e ex)
      VRet ma -> s
      Cond ma ex es lvs -> Cond ma (e ex) (f' es) lvs
      CondElse ma ex es es' lvs -> CondElse ma (e ex) (f' es) (f' es') lvs
      While ma ex es lvs -> While ma (e ex) (f' es) lvs
      SExp ma ex -> SExp ma (e ex)
    e :: Expr -> Expr
    e expr = case expr of
      EVar ma lv -> expr
      ELitInt ma n -> expr
      ELitTrue ma -> expr
      ELitFalse ma -> expr
      ENull ma -> expr
      EApp ma (Ident id) exs -> if DM.member id senv
        then EMethod ma (LVar ma (Ident "this")) (Ident id) (map e exs)
        else expr
      EMethod ma lval id exs -> EMethod ma lval id (map e exs)
      EString ma s -> expr
      ENewArray ma ty ex -> expr
      ENewClass ma ty -> expr
      Neg ma ex -> Neg ma (e ex)
      Not ma ex -> Not ma (e ex)
      EMul ma ex mo ex' -> EMul ma (e ex) mo (e ex')
      EAdd ma ex ao ex' -> EAdd ma (e ex) ao (e ex')
      ERel ma ex ro ex' -> ERel ma (e ex) ro (e ex')
      EAnd ma ex ex' -> EAnd ma (e ex) (e ex')
      EOr ma ex ex' ->  EOr ma (e ex) (e ex')
      ECast ma t ex -> ECast ma t (e ex)
    i :: Item -> Item
    i = \case
      NoInit ma id -> NoInit ma id
      Init ma id ex -> Init ma id (e ex)
    in case iblock of
         Block ma ess -> Block ma (map f' ess)
         VirtualBlock ess -> VirtualBlock (map f' ess)
  in case classdef of
       ClassDef ma id cmds cmds' -> ClassDef ma id cmds cmethods'
       ClassDefExtends ma id id' cmds cmds' -> ClassDefExtends ma id id' cmds cmethods'
