module Main where
import Prelude

import Data.Maybe (fromMaybe)
import Data.Set as DS hiding (foldl, foldr)
import Data.Map.Strict as DM hiding (foldl, foldr)
import Data.List as DL hiding (foldl, foldr)
import Data.Containers.ListUtils (nubOrd)

import Control.Monad.Except (Except, throwError, catchError, runExcept)
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad(void)

import System.Environment (getArgs)
import System.Exit

import IDefinition as IDef

import Latte.Abs
    (
      HasPosition(..),
      Ident(Ident),
      Arg'(Arg),
      Arg,
      TopDef'(FnDef),
      TopDef,
      Program'(Program),
      Program, Item, Block(..), Stmt, Block' (Block), Stmt' (BStmt) )
import Latte.Lex (Token)
import Latte.Par (myLexer, pProgram)

import Translator

type Err = Either String
type ParseFun a = [Token] -> Err a

compile :: Program -> CompilerExcept ()
compile program =
  do
    programToInternal program

argumentError = 1
grammarError = 2

runCompiler :: ParseFun Program -> String -> IO ()
runCompiler p s =
  case p ts of
    Left err -> do
      exitWith (ExitFailure grammarError)
    Right program -> do
      case runExcept $ compile program of
        Left err -> exitWith (ExitFailure argumentError)
        Right _ -> exitSuccess
  where
    ts = myLexer s

runFile :: ParseFun Program -> FilePath  -> IO()
runFile p f = readFile f >>= runCompiler p

run :: [String] -> IO()
run [] = exitWith (ExitFailure argumentError)
run [a] = runFile pProgram a
run _ = exitWith (ExitFailure argumentError)

add :: Num a => a -> a
add x = x + 3

main :: IO ()
main = do
  args <- getArgs
  run args
