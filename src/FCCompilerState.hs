{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification#-}

module FCCompilerState (VariableEnvironment(..),
                        -- LLRegisterState(..),
                        ConstantsEnvironment(..)) where

import FCCompilerTypes
-- import Control.Monad.State.Strict
-- import Data.Map.Strict (Map)


-- class (Ord key) => Environment a key value | a -> key value where
--   _declareMapping :: key -> value -> a -> a
--   _getMapping :: key -> a -> Maybe value
--   _lookupMapping :: key -> a -> Bool

class ConstantsEnvironment a key value | a -> key value where
  _getPointer :: key -> a -> (a, value)

 -- (Environment a key value) =>
class VariableEnvironment a key value | a -> key value where
  _setVariable :: key -> value -> a -> a
  _declareVariable :: key -> value -> a -> a
  _lookupVariable :: key -> a -> Bool
  _getManyVariables :: [key] -> a -> [Maybe value]
  _openClosure :: a -> a
  _closeClosure :: a -> a
  _getVariable :: key -> a -> Maybe value

-- class LLRegisterState a where
--   _lookupRegister :: FCRegister -> a -> Maybe FCRValue
--   _normalizeFCRValue :: FCRValue -> a -> FCRValue
--   _mapFCRValue    :: FCRValue -> a -> (a, Either FCRegister FCRegister)
--   _mapFCRValueRegType :: RegType -> FCRValue -> a -> (a, Either FCRegister FCRegister)

class BlockBuilder a stmtType blockType | a -> stmtType blockType where
  -- _openNewBlock :: a -> a
  -- _closeBlock :: a -> a
  _prependStmt :: stmtType -> a -> a
  _prependBlock :: blockType -> a -> a
  _build :: a -> blockType 

-- data FCC venvData blockData regData constants =
--   (VariableEnvironment venvData String FCRegister,
--    BlockBuilder blockData FCInstr FCBlock,
--    LLRegisterState regData,
--    Environment constants String String) => FCC {
--     venv :: venvData,
--     blockstate :: blockData,
--     registerState:: regData,
--     consts :: constants}

-- fccPutVenv :: FCC venvData blockData regData constants -> venvData -> FCC venvData blockData regData constants
-- fccPutVenv (FCC v b r c) v' = FCC v' b r c
-- fccPutBlockBuilder :: FCC venvData blockData regData constants -> blockData -> FCC venvData blockData regData constants
-- fccPutBlockBuilder (FCC v b r c) b' = FCC v b' r c
-- fccPutRegState :: LLRegisterState p => FCC venvData blockData regData constants -> p -> FCC venvData blockData p constants
-- fccPutRegState (FCC v b r c) r' = FCC v b r' c
-- fccPutConstState :: Environment p String String => FCC venvData blockData regData constants -> p -> FCC venvData blockData regData p
-- fccPutConstState (FCC v b r c) = FCC v b r

-- fccPutVenv :: FCC venvData blockData regData constants -> venvData -> FCC venvData blockData regData constants

-- fccPutVenv :: FCC venvData blockData regData constants -> venvData -> FCC venvData blockData regData constants


-- class (VariableEnvironment v varType regType,
--    BlockBuilder b instType blockType,
--    LLRegisterState regType,
--    Environment c etType String,
--    MonadState s) => CompilationState s varType regType v b r c where
--   setVariable :: v' -> s

-- type CompilationState venvType blockStateType regData constantsStateType = State (FCC venvType blockStateType regData constantsStateType)

-- setVariable :: (VariableEnvironment v String FCRegister) => String -> FCRegister -> CompilationState v b r c ()
-- setVariable key value = modify (\fcc -> fccPutVenv fcc $ _setVariable key value (venv fcc))
-- declareVariable :: (VariableEnvironment v String FCRegister) =>
--   String -> FCRegister -> CompilationState v b r c ()
-- declareVariable key value = modify (\fcc -> fccPutVenv fcc $ _setVariable key value (venv fcc))
-- lookupVariable :: (VariableEnvironment v String FCRegister) => String -> CompilationState v b r c ()
-- lookupVariable :: 
-- getManyVariables :: (VariableEnvironment venvType String FCRegister) => [key] -> a -> [Maybe value]
-- newClosure :: (VariableEnvironment venvType String FCRegister) => a -> a
-- oldClosure :: (VariableEnvironment venvType String FCRegister) => a -> a
-- getVariable :: (VariableEnvironment venvType String FCRegister) => key -> a -> Maybe value

-- runCompilationState 
