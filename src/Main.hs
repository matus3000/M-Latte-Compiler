module Main where
import Prelude

import Data.Map.Strict as DM
import Data.Containers.ListUtils (nubOrd)

import Control.Monad.Except (Except, throwError, catchError)
import Control.Monad.Identity

import System.Environment (getArgs)
import System.Exit

import IDefinition

import Latte.Abs
import Latte.Lex (Token)
import Latte.Par (myLexer, pProgram)

type Err = Either String
type ParseFun a = [Token] -> Err a

type FunctionData = (LType, [LType])
type FunctionEnvironment = DM.Map Ident FunctionData

getFunctionEnvironment :: Program -> Except String FunctionEnvironment
getFunctionEnvironment (Program _ topDef) =
  let
    argsListLType :: [Arg] -> Except String [LType]
    argsListLType =
      foldr (\arg list -> list >>= (getArgLType arg:)) (return [])
    getFunctionData :: TopDef -> Except String FunctionData
    getFunctionData (FnDef _ returnType id args _) = throwError "Alice"
  in
    throwError "Alice"

argumentError = 1
grammarError = 2

runCompiler :: ParseFun Program -> String -> IO ()
runCompiler p s =
  case p ts of
    Left err -> do
      exitWith (ExitFailure grammarError)
    Right (Program program s) -> do
      exitSuccess
  where
    ts = myLexer s

runFile :: ParseFun Program -> FilePath  -> IO()
runFile p f = readFile f >>= runCompiler p 

run :: [String] -> IO()
run [] = exitWith (ExitFailure argumentError)
run [a] = runFile pProgram a
run _ = exitWith (ExitFailure argumentError)

main :: IO ()
main = do
  args <- getArgs
  run args
