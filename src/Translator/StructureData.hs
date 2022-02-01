module Translator.StructureData(
  StructureData(..),
  lookupMethod,
  lookupField) where

import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import IDefinition
import Translator.FunctionData

data StructureData = StructureData {fields :: [(String, LType)],
                                    superclass :: Maybe String,
                                    definedFields :: [(String, LType)],
                                    inheritedFields :: [(String, LType)],
                                    methods :: DM.Map String FunctionData,
                                    methodsParents :: DM.Map String String}

lookupMethod :: String -> StructureData ->  Maybe (String, FunctionData)
lookupMethod methodName sd = do
  announcer <- DM.lookup methodName (methodsParents sd)
  functionData <- DM.lookup methodName (methods sd)
  return (announcer, functionData)

lookupField :: String -> StructureData ->  Maybe LType
lookupField fieldName sd =  DL.lookup fieldName (fields sd)

instance Show StructureData where
  show sd = show (fields sd) ++ "," ++ show (definedFields sd)
