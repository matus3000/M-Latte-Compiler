{-# LANGUAGE LambdaCase #-}
module FCCompiler.FCEnvironment (FCEnvironment,
                                functionType,
                                isIoFunction,
                                getMutabaleArgsOfFunction,
                                hasMutableArgs,
                                getMethodFCFunData,
                                getClassData,
                                new,
                                StructureData(..)) where

import Translator.StructureData(StructureData(..))
import qualified Translator.StructureData as SD
import Translator.TranslatorEnvironment (StructureEnvironment(..), FunctionData)
import FCCompilerTypes (FCType (FCPointer, UniversalPointer), FCFun, FCFun' (retType), FCRValue(..), FCRegister, FCClass (className))

import qualified Data.Map as DM
import qualified Data.Set as DS
import Data.Maybe (fromJust)
import Translator (Convertable(convert))
import qualified IDefinition as IDef

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

getMethodFCFunData :: String -> String -> FCEnvironment -> Maybe (FCType, [FCType])
getMethodFCFunData className methodName fcenv =
  let
    cd = fromJust $ getClassData className fcenv
    (parent, (retType, fundata)) = fromJust $ SD.lookupMethod methodName cd
    fcRet :: FCType
    fcRet = convert retType
    fcFunData :: [FCType]
    fcFunData = map convert (IDef.LClass parent:fundata)
  in
    Just (fcRet, fcFunData)

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
