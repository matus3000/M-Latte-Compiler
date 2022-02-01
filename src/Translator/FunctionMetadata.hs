module Translator.FunctionMetadata (FunctionInfo(..),
                                    putFname,
                                    putRetType,
                                    putIo,
                                    putIndicesofMuts) where
import Translator.Definitions (IType)

data FunctionInfo = FunctionInfo {
  fname::String,
  retType :: IType,
  indicesOfMuts :: [Int],
  isIO :: Bool
  }

putFname :: String -> FunctionInfo -> FunctionInfo
putFname s (FunctionInfo old i list io) = FunctionInfo old i list io
putRetType  :: IType -> FunctionInfo -> FunctionInfo
putRetType i' (FunctionInfo old i list io) = FunctionInfo old i' list io
putIo :: Bool -> FunctionInfo -> FunctionInfo
putIo io' (FunctionInfo old i list io) = FunctionInfo old i list io'
putIndicesofMuts :: [Int] -> FunctionInfo -> FunctionInfo
putIndicesofMuts list' (FunctionInfo old i list io) = FunctionInfo old i list' io

-- isIO :: FunctionInfo -> Bool
-- getReturnType :: FunctionInfo -> IType
-- getIndicesOfMutableArguments :: FunctionInfo -> [Int]
