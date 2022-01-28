module FCCompiler.FCEnvironment (FCEnvironment,
                                functionType,
                                isIoFunction,
                                hasMutableArgs,
                                getClassData,
                                new) where 

import Translator.TranslatorEnvironment (StructureData(..), StructureEnvironment())
import FCCompilerTypes (FCType, FCFun, FCFun' (retType))

import qualified Data.Map as DM
import qualified Data.Set as DS

data FCFunEnv = FCFunEnv {retTypes :: DM.Map String FCType,
                          ioFuns :: DS.Set String}

data FCEnvironment = FCEnv {fEnv :: FCFunEnv,
                            sEnv :: StructureEnvironment}

new :: DM.Map String FCType -> DS.Set String -> StructureEnvironment -> FCEnvironment
new retTypes ioFuns = FCEnv (FCFunEnv retTypes ioFuns)
functionType :: String -> FCEnvironment -> Maybe FCType
functionType fname fcenv = DM.lookup fname $ (retTypes . fEnv) fcenv
isIoFunction :: String -> FCEnvironment -> Maybe Bool
isIoFunction fname fcenb = Just $ DS.member fname $ (ioFuns . fEnv) fcenb
hasMutableArgs :: String -> FCEnvironment -> Maybe Bool
hasMutableArgs = undefined
getMutabaleArgsOfFunction :: String -> FCEnvironment -> Maybe [Int]
getMutabaleArgsOfFunction = undefined
getClassData :: String -> FCEnvironment -> Maybe StructureData
getClassData = undefined
