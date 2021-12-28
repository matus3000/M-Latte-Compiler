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
import Control.Monad.Except (Except)

class (Ord key) => VariableEnvironment a key value | a -> key value where
  setVar :: key -> value -> a -> a
  declareVar :: key -> value -> a -> a
  containsVar :: key -> a -> Bool
  getVar :: key -> a -> Maybe value
  getVars :: [key] -> a -> [Maybe value]
  openClosure :: a -> a
  closeClosure :: a -> a
  protectVars_ :: [key] -> a -> a
  protectVars :: [key] -> [value] -> a -> a
  endProtection :: [key] -> a -> a

data VarEnv vartype value = VarEnv {varmap :: DM.Map vartype [value],
                                         modifiedVars :: [DS.Set vartype],
                                         redeclaredVars :: [DS.Set vartype]
                                       }
instance (Ord key) => VariableEnvironment (VarEnv key value) key value where
  setVar key value (VarEnv vmap modvars redvars) =
    let x = [] `fromMaybe` DM.lookup key vmap
    in
      VarEnv (DM.insert key (value:tail x) vmap) (DS.insert key (head modvars) : tail modvars) redvars
  declareVar key value venv@(VarEnv vmap modvars redvars) = let
    x = [] `fromMaybe` DM.lookup key vmap
    in
      if not (DS.member key (head redvars)) then
        VarEnv (DM.insert key (value:tail x) vmap) (DS.insert key (head modvars) : tail modvars) redvars
      else
        venv
  containsVar key (VarEnv vmap modvars redvars) = DM.member key vmap
  getVars keys (VarEnv vmap modvars redvars) = map (\key -> head <$> DM.lookup key vmap) keys
  getVar key (VarEnv vmap modvars redvars) = head <$> DM.lookup key vmap
  openClosure (VarEnv vmap modvars redvars) = VarEnv vmap (DS.empty : modvars) (DS.empty : redvars)
  closeClosure (VarEnv vmap modvars redvars) =
    let
      snd :: [a] -> Maybe a
      snd (x:y:rest) = Just y
      snd _ = Nothing
      modified = head modvars
      parent = DS.empty `fromMaybe` snd modvars
      popKey :: String -> DM.Map String [a] -> DM.Map String [a]
      popKey x map = DM.insert x vs map
        where
          (v:vs) = [] `fromMaybe` DM.lookup x map
    in
      VarEnv (foldl (\ map key -> undefined ) vmap (head redvars))
      (DS.union modified parent:(tail.tail$modvars)) (tail redvars)
  protectVars keys  vals  venv = foldl
    (\venv (key, val) -> declareVar key val venv)
    (openClosure venv)
    [(key, val) | key <- keys, val <- vals]
  endProtection keys venv = closeClosure venv
