module Translator.ClassRepresentation (ClassRepresentation(..),
                                       setField,
                                       setFieldUnsafe,
                                       getField,
                                       setDefault,
                                       getDefault,
                                       getStructureData) where

import qualified Data.Map.Strict as DM
import Translator.Definitions(IValue)
import Translator.TranslatorEnvironment(StructureData, sdFieldType)

data ClassRepresentation = ClassRepresentation (DM.Map String IValue) StructureData IValue

setFieldUnsafe :: String -> IValue -> ClassRepresentation -> Maybe ClassRepresentation
setFieldUnsafe member ivalue (ClassRepresentation map sd def) = do
  _ <- sdFieldType member sd
  return $ ClassRepresentation (DM.insert member ivalue map) sd def

setField :: String -> IValue -> ClassRepresentation -> Maybe ClassRepresentation
setField field ivalue (ClassRepresentation map sd def) =
  let
    memberType = sdFieldType field sd
  in
    undefined
getField :: String -> ClassRepresentation -> Maybe IValue
getField = undefined
getDefault :: ClassRepresentation -> IValue
getDefault = undefined
setDefault :: ClassRepresentation -> IValue
setDefault = undefined
getStructureData :: ClassRepresentation -> StructureData
getStructureData (ClassRepresentation _ sd _) = sd
