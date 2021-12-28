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
newVarEnv = openClosure (VarEnv DM.empty [] [])

data VarEnv vartype value = VarEnv {varmap :: DM.Map vartype [value],
                                         modifiedVars :: [DS.Set vartype],
                                         redeclaredVars :: [DS.Set vartype]
                                       }
instance (Ord key) => CVariableEnvironment (VarEnv key value) key value where
  setVar key value (VarEnv vmap modvars redvars) =
    let x = [] `fromMaybe` DM.lookup key vmap
    in
      VarEnv (DM.insert key (value:tail x) vmap) (DS.insert key (head modvars) : tail modvars) redvars
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
    Just [] -> error "Not so sure if that's an error"
  openClosure (VarEnv vmap modvars redvars) = VarEnv vmap (DS.empty : modvars) (DS.empty : redvars)
  closeClosure (VarEnv vmap modvars redvars) =
    let
      snd :: [a] -> Maybe a
      snd (x:y:rest) = Just y
      snd _ = Nothing
      modified = head modvars
      parent = DS.empty `fromMaybe` snd modvars
      popKey :: (Ord key) => key -> DM.Map key [a] -> DM.Map key [a]
      popKey x map = DM.insert x vs map
        where
          (v:vs) = [] `fromMaybe` DM.lookup x map
    in
      VarEnv (foldl (flip popKey) vmap (head redvars))
      (DS.union modified parent:(tail.tail$modvars)) (tail redvars)
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
