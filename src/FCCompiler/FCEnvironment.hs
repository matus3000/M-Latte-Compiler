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
                          mutableArgs :: DM.Map String [Bool],
                          ioFuns :: DS.Set String}

data FCEnvironment = FCEnv {fEnv :: FCFunEnv,
                            sEnv :: StructureEnvironment}

new :: DM.Map String FCType -> DS.Set String  -> DM.Map String [Bool]-> StructureEnvironment -> FCEnvironment
new retTypes ioFuns mutargs = FCEnv (FCFunEnv retTypes mutargs ioFuns)
functionType :: String -> FCEnvironment -> Maybe FCType
functionType fname fcenv = DM.lookup fname $ (retTypes . fEnv) fcenv
isIoFunction :: String -> FCEnvironment -> Maybe Bool
isIoFunction fname fcenv = Just $ DS.member fname $ (ioFuns . fEnv) fcenv
hasMutableArgs :: String -> FCEnvironment -> Maybe Bool
hasMutableArgs funName fcenv = or <$> DM.lookup funName ((mutableArgs.fEnv) fcenv)
getMutabaleArgsOfFunction :: String -> FCEnvironment -> Maybe [Bool]
getMutabaleArgsOfFunction funname = DM.lookup funname . mutableArgs . fEnv
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
