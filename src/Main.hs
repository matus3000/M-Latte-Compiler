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
import System.IO (stderr, hPutStrLn)
import System.Exit

import qualified IDefinition as IDef

import qualified Latte.Abs as Lt
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
import CompilationError (errorToString)

type Err = Either String
type ParseFun a = [Token] -> Err a

compile :: Lt.Program -> CompilerExcept ()
compile program =
  do
    void $ (programToInternal . IDef.preprocessProgram)  program

argumentError = 1
grammarError = 2

putStrLnStderr :: String -> IO()
putStrLnStderr = hPutStrLn stderr

runCompiler :: ParseFun Lt.Program -> String -> IO ()
runCompiler p s =
  case p ts of
    Left err -> do
      putStrLnStderr "ERROR"
      putStrLnStderr err
      exitWith (ExitFailure grammarError)
    Right program -> do
      case runExcept $ compile program of
        Left err -> do
          putStrLnStderr "ERROR"
          putStrLnStderr $ errorToString err
          exitWith (ExitFailure argumentError)
        Right _ -> exitSuccess
  where
    ts = myLexer s

runFile :: ParseFun Lt.Program -> FilePath  -> IO()
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
