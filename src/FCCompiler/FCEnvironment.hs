{-# LANGUAGE LambdaCase #-}
module FCCompiler.FCEnvironment (FCEnvironment,
                                functionType,
                                isIoFunction,
                                getMutabaleArgsOfFunction,
                                hasMutableArgs,
                                getClassData,
                                new,
                                StructureData(..)) where

import Translator.TranslatorEnvironment (StructureData(..), StructureEnvironment(..))
import FCCompilerTypes (FCType (FCPointer, UniversalPointer), FCFun, FCFun' (retType), FCRValue(..), FCRegister, FCClass (className))

import qualified Data.Map as DM
import qualified Data.Set as DS
import Data.Maybe (fromJust)

data FCFunEnv = FCFunEnv {retTypes :: DM.Map String FCType,
                          ioFuns :: DS.Set String}

data FCEnvironment = FCEnv {fEnv :: FCFunEnv,
                            sEnv :: StructureEnvironment}

new :: DM.Map String FCType -> DS.Set String -> StructureEnvironment -> FCEnvironment
new retTypes ioFuns = FCEnv (FCFunEnv retTypes ioFuns)
functionType :: String -> FCEnvironment -> Maybe FCType
functionType fname fcenv = DM.lookup fname $ (retTypes . fEnv) fcenv
isIoFunction :: String -> FCEnvironment -> Maybe Bool
isIoFunction fname fcenv = Just $ DS.member fname $ (ioFuns . fEnv) fcenv
hasMutableArgs :: String -> FCEnvironment -> Maybe Bool
hasMutableArgs = undefined
getMutabaleArgsOfFunction :: String -> FCEnvironment -> Maybe [Int]
getMutabaleArgsOfFunction = undefined
getClassData :: String -> FCEnvironment -> Maybe StructureData
getClassData className fcenv = DM.lookup className $ (classMap . sEnv) fcenv

isRValueRunTime :: FCRValue -> FCEnvironment -> Bool
isRValueRunTime fcrval env = case fcrval of
  FunCall ft s x1 -> isPointer ft || fromJust (isIoFunction s env) || fromJust (hasMutableArgs s env)
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
