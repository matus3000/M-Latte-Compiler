{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
-- TO DO: USUNĄĆ MODVARS
module VariableEnvironment where

import qualified Data.Map.Strict as DM
import qualified Data.Set as DS
import Prelude
import Data.Maybe (fromMaybe)
import CompilationError(SemanticError)
import Control.Monad.Error.Class (MonadError)
import Control.Monad.Except (Except, unless)

class (Ord key) => CVariableEnvironment a key value | a -> key value where
  setVar :: key -> value -> a -> a
  declareVar :: key -> value -> a -> a
  containsVar :: key -> a -> Bool
  lookupVar :: key -> a -> Maybe value
  lookupVars :: [key] -> a -> [Maybe value]
  openClosure :: a -> a
  closeClosure :: a -> a
  protectVars_ :: (Foldable t) => t key -> a -> a
  protectVars :: [key] -> [value] -> a -> a
  endProtection :: a -> a

newVarEnv :: (Ord vartype) => VarEnv vartype value
newVarEnv = VarEnv DM.empty [] []

data VarEnv vartype value = VarEnv {varmap :: DM.Map vartype [value],
                                         modifiedVars :: [DS.Set vartype],
                                         redeclaredVars :: [DS.Set vartype]
                                       }
instance (Ord key) => CVariableEnvironment (VarEnv key value) key value where
  setVar key value (VarEnv vmap modvars redvars) =
    let x = [] `fromMaybe` DM.lookup key vmap
        hmod = if (null modvars) then error "XX" else (head modvars)
    in
      VarEnv (DM.insert key (value:tail x) vmap) (DS.insert key hmod : tail modvars) redvars
  declareVar key value venv@(VarEnv vmap [] _) = error "VE.DeclareVar: modifiedVars are empty List"
  declareVar key value venv@(VarEnv vmap _ []) = error "VE.DeclareVar: redifinedVars are empty List"
  declareVar key value venv@(VarEnv vmap modvars redvars) =
    let
      x = [] `fromMaybe` DM.lookup key vmap
      currentRed = head (redeclaredVars venv)
    in
      if not (DS.member key currentRed) then
        VarEnv (DM.insert key (value:x) vmap) modvars (DS.insert key currentRed : tail redvars)
      else
        venv
  containsVar key (VarEnv vmap modvars redvars) = DM.member key vmap
  lookupVars keys (VarEnv vmap modvars redvars) = map (\key -> head <$> DM.lookup key vmap) keys
  lookupVar key (VarEnv vmap modvars redvars) = case DM.lookup key vmap of
    Nothing -> Nothing
    Just (x:xs) -> Just x
    Just [] -> Nothing
  openClosure (VarEnv vmap modvars redvars) = VarEnv vmap (DS.empty : modvars) (DS.empty : redvars)
  closeClosure (VarEnv vmap modvars redvars) =
    let
      popKey :: (Ord key) => key -> DM.Map key [a] -> DM.Map key [a]
      popKey x map = DM.insert x vs map
        where
          (v:vs) = [] `fromMaybe` DM.lookup x map
    in
      if length modvars /= length redvars then
        error "Modvars does not equals to redvars"
      else
        case (modvars, redvars) of
          ([modSet], [redSet]) -> VarEnv (foldl (flip popKey) vmap redSet) [] []
          ([], []) -> error "CloseClosure on closed var environment"
          _ -> VarEnv (foldl (flip popKey) vmap (head redvars))
            (DS.union (head modvars) (head $ tail modvars): tail (tail modvars))
            (tail redvars)

  protectVars keys  vals  venv = foldl
    (\venv (key, val) -> if containsVar key venv then declareVar key val venv else venv)
    (openClosure venv)
    [(key, val) | key <- keys, val <- vals]
  protectVars_ keys  venv = foldl
    (\venv key -> case lookupVar key venv of
        Just val -> declareVar key val venv
        Nothing -> venv)
    (openClosure venv)
    keys
  endProtection venv = closeClosure venv
