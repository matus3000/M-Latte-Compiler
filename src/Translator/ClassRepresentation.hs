module Translator.ClassRepresentation (ClassRepresentation(..),
                                       setField,
                                       getField,
                                       setDefault,
                                       getDefault,
                                       getStructureData) where

import Data.Map.Strict as DM
import Translator.Definitions(IValue)
import Translator.TranslatorEnvironment(StructureData)

data ClassRepresentation = ClassRepresentation (DM.Map String IValue) StructureData IValue

setField :: String -> IValue -> ClassRepresentation -> Maybe ClassRepresentation
setField = undefined 
getField :: String -> ClassRepresentation -> Maybe IValue
getField = undefined
getDefault :: ClassRepresentation -> IValue
getDefault = undefined
setDefault :: ClassRepresentation -> IValue
setDefault = undefined
getStructureData :: ClassRepresentation -> StructureData
getStructureData (ClassRepresentation _ sd _) = sd
