{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification#-}

module FCCompilerState (VariableEnvironment(..),
                        ConstantsEnvironment(..)) where

import FCCompilerTypes

class ConstantsEnvironment a key value | a -> key value where
  _getPointer :: key -> a -> (a, value)

class VariableEnvironment a key value | a -> key value where
  _setVariable :: key -> value -> a -> a
  _declareVariable :: key -> value -> a -> a
  _lookupVariable :: key -> a -> Bool
  _getManyVariables :: [key] -> a -> [Maybe value]
  _openClosure :: a -> a
  _closeClosure :: a -> a
  _getVariable :: key -> a -> Maybe value

class BlockBuilder a stmtType blockType | a -> stmtType blockType where
  _prependStmt :: stmtType -> a -> a
  _prependBlock :: blockType -> a -> a
  _build :: a -> blockType 
