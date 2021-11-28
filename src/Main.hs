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

type Err = Either String
type ParseFun a = [Token] -> Err a

type FunctionData = (LType, [LType])
type FunctionEnvironment = DM.Map String FunctionData
type CompilerExcept = Except SemanticError
type StateStrMap x = State (DM.Map String x)

getFunctionEnvironment :: Program -> CompilerExcept FunctionEnvironment
getFunctionEnvironment (Program _ topDef) =
  let
    getPosition :: (HasPosition a) => a -> (Int, Int)
    getPosition a = (-1, -1) `fromMaybe` hasPosition a
    getFunctionData :: TopDef -> CompilerExcept FunctionData
    getFunctionData f@(FnDef pos returnType id args _) =
      let
        argsLTypeList :: [LType]
        argsLTypeList = Prelude.map getArgLType args
        returnLtype = convertType returnType
        getRedefinedArg :: [Arg] -> [Arg] -> Maybe(Arg, Arg)
        getRedefinedArg x [] = Nothing
        getRedefinedArg x (y@(Arg _ _ (Ident yid)):ys) =
          case DL.find (\arg -> yid == getIdStr arg) x of
            (Just leftMost) -> Just (leftMost, y)
            Nothing -> getRedefinedArg (y:x) ys
        redefinedArg = getRedefinedArg [] args
      in
        case redefinedArg of
          Nothing -> return (returnLtype, argsLTypeList)
          Just (old, new) ->
            let
              x :: IDef.SemanticErrorType
              x = IDef.RedefinitionOfVariable (getPosition new) (getPosition old) (getIdStr old)
            in
              throwError $ IDef.SemanticError (getPosition f) x
    checkFunction :: TopDef -> StateStrMap (Int,Int) (CompilerExcept FunctionEnvironment)
      -> StateStrMap (Int,Int) (CompilerExcept FunctionEnvironment)
    checkFunction topDef monad =
      let topName = getIdStr topDef in
      monad >>= (\fe ->
                    do
                      map <- get
                      if DM.member topName map then
                        return $ throwError (SemanticError (getPosition topDef)
                                             (RedefinitionOfFunction (getPosition topDef)
                                              ((-1, -1) `fromMaybe` DM.lookup topName map) topName))
                        else
                        do
                          put (DM.insert topName (getPosition topDef) map)
                          return $ do
                              fd <- getFunctionData topDef;
                              DM.insert topName fd <$> fe)
    result = Prelude.foldl (flip checkFunction) (return $ return DM.empty) topDef
  in
    evalState result DM.empty

itemToInternal :: LType -> Item -> LItem
itemToInternal y x = undefined



stmtToInternal :: Stmt -> Compiler VariableEnvironment LStmt
stmtToInternal (BStmt _ block) = do
  lBlock <- (\(VEnv set map) -> VEnv DS.empty map) `local` blockToInternal block
  return $ LBStmt lBlock
stmtToInternal stmt@(Decl _ argType items_) = undefined 
stmtToInternal x = return LStmtEmpty 



lTypeToVarType :: LType -> VarType
lTypeToVarType LInt = DynamicInt
lTypeToVarType LBool = DynamicBool
lTypeToVarType LString = DynamicString
lTypeToVarType _ = undefined


type Compiler a = ReaderT a CompilerExcept


blockToInternal :: Block -> Compiler VariableEnvironment LBlock
blockToInternal block@(Block x stmts) =
  let
    fun :: [Stmt] -> Compiler VariableEnvironment [LStmt]
    fun [] = return []
    fun (x:xs) = stmtToInternal x >>= (\head -> fun xs >>= \rest -> return $ head:rest)
  in
    fun stmts >>= \res -> return $ LBlock res


topDefToInternal :: TopDef -> FunctionEnvironment -> CompilerExcept ()
topDefToInternal fDef fEnv =
  let
    funName = getIdStr fDef
    funArgs = [(getIdStr i, getArgLType i) | i <- topDefArgs fDef]
    block = topDefBlock fDef
    vEnv :: VariableEnvironment
    vEnv = VEnv DS.empty DM.empty
    nvEnv = foldl (\(VEnv set map) (id, ltype) -> VEnv (DS.insert id set) (DM.insert id (lTypeToVarType ltype) map)) vEnv funArgs
  in
    Control.Monad.void (runReaderT (blockToInternal block) nvEnv)

programToInternal :: Program -> FunctionEnvironment -> CompilerExcept()
programToInternal (Program _ topDefs) fEnv =
  let
    x :: CompilerExcept ()
    x = return ()
    fun :: CompilerExcept () -> TopDef -> CompilerExcept ()
    fun monad topDef = do
      topDefToInternal topDef fEnv
      monad
  in
    foldl fun x topDefs

assertMain :: FunctionEnvironment -> CompilerExcept ()
assertMain fEnv =
  let
    main = DM.lookup "main" fEnv
    in
    case main of
      Just (LInt, _) -> return ()
      _ -> throwError $ SemanticError (0,0) NoMain

compile :: Program -> CompilerExcept ()
compile program =
  do
    fEnv <- getFunctionEnvironment program
    assertMain fEnv
    programToInternal program fEnv

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
