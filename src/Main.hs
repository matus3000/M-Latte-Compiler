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
import FCCompiler(compileProg)
import qualified LLVMCompiler as LLVM (compile)

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
import CompilationError (errorToString, errorToStringExtended)

type Err = Either String
type ParseFun a = [Token] -> Err a

compile :: Lt.Program -> CompilerExcept String
compile program =
  do
    iprogram <- (programToInternal . IDef.preprocessProgram) program
    return $ LLVM.compile (compileProg  iprogram)

translate :: Lt.Program  -> CompilerExcept IProgram
translate program =
  do
    (programToInternal . IDef.preprocessProgram) program

argumentError = 1
grammarError = 2

putStrLnStderr :: String -> IO()
putStrLnStderr = hPutStrLn stderr

test :: Bool
test = False

runCompiler :: ParseFun Lt.Program -> String -> IO ()
runCompiler p s =
  case p ts of
    Left err -> do
      putStrLnStderr "ERROR"
      putStrLnStderr err
      exitWith (ExitFailure grammarError)
    Right program -> do
      case runExcept $ translate program of
        Left err -> do
          putStrLnStderr "ERROR"
          putStrLnStderr $ errorToStringExtended err s
          exitWith (ExitFailure argumentError)
        Right tcode ->
          do
            let fccode = compileProg tcode
                code  = LLVM.compile fccode
            putStrLnStderr "OK"
            if test then  showClasses tcode
              else putStr code
            exitSuccess
  where
    ts = myLexer s
    showClasses :: IProgram -> IO ()
    showClasses tcode = do
      let (IProgram z v se _) = tcode
      print v
    -- showMetaData :: IProgram -> IO ()
    -- showMetaData tcode = do
    --   let (IProgram z v se ex) = tcode
    --   print ex
    showStructureData tcode = do
      let (IProgram z v se _) = tcode
      print se
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
