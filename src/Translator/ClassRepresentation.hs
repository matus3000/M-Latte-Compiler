module Translator.ClassRepresentation (ClassRepresentation(..),
                                       setField,
                                       setFieldUnsafe,
                                       lookupField,
                                       getDefault,
                                       getStructureData) where

import qualified Data.Map.Strict as DM
import Translator.Definitions(IValue)
import Translator.TranslatorEnvironment(StructureData)
import qualified Translator.StructureData as SD

data ClassRepresentation = ClassRepresentation (DM.Map String IValue) StructureData IValue

fieldMap :: ClassRepresentation -> DM.Map String IValue
fieldMap (ClassRepresentation x y z) = x

setFieldUnsafe :: String -> IValue -> ClassRepresentation -> Maybe ClassRepresentation
setFieldUnsafe member ivalue (ClassRepresentation map sd def) = do
  _ <- SD.lookupField member sd
  return $ ClassRepresentation (DM.insert member ivalue map) sd def

setField :: String -> IValue -> ClassRepresentation -> Maybe ClassRepresentation
setField field ivalue (ClassRepresentation map sd def) =
  let
    memberType = SD.lookupField field sd
  in
    undefined

lookupField :: String -> ClassRepresentation -> Maybe IValue
lookupField field = DM.lookup field . fieldMap

getDefault :: ClassRepresentation -> IValue
getDefault (ClassRepresentation x y z) = z
-- setDefault :: ClassRepresentation -> IValue
-- setDefault = undefined
getStructureData :: ClassRepresentation -> StructureData
getStructureData (ClassRepresentation _ sd _) = sd
