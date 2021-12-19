{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification#-}
module LLCompilerDefs (
  -- ExpToFCStateMonad(prependFCRValue,
  --                   getVariable,
  --                   lookupStringName,
  --                   isFunStatic),
  -- InstrToFCStateMonad(setVariable,
  --                     declareVariable,
  --                     addBlock,
  --                     addIfBlock,
  --                     addIfElseBlock,
  --                     addWhileBlock),
  -- FCUnaryOperator(..),
  -- FCBinaryOperator(..),
  -- FCRegister(..),
  -- FCRValue(..),
  -- FCInstr(..),
  -- FCBlock,
  -- FCFun,
  RegType(..))
where

import Control.Monad.Except (Except, MonadError)
import Control.Monad.State.Strict (MonadState)
import CompilationError(SemanticError, SemanticError(CompilationError))
import Translator(CompilerExcept, Convertable(..))
import qualified Translator as Tr
import SPARC.CodeGen.Base (Register)
import System.Process.Internals (translate)
import qualified Data.Map as DM

data FCUnaryOperator = Neg | BoolNeg
  deriving (Eq, Ord)

data FCBinaryOperator = Add | Sub | Div | Mul | Mod | LShift | RShif | ByteAnd | ByteOr | ByteXor |
                     BoolAnd | BoolOr | BoolXor  | Test | Le | Equ | Neq | Lth | Gth | Ge
  deriving (Eq, Ord)

data FCRegister = VoidReg | Reg String | LitInt Int | LitBool Bool | Et String
  deriving (Eq, Ord)

data FCRValue = FunCall String [FCRegister] | FCBinOp FCBinaryOperator FCRegister FCRegister |
                FCUnOp FCUnaryOperator FCRegister | ConstValue FCRegister |
                GetPointer FCRegister FCRegister | Return (Maybe FCRegister)
  deriving (Eq, Ord)

type FCInstr = (FCRegister, FCRValue)

type FCSimpleBlock = (String, [FCInstr])

data FCBlock = FCSimpleBlock FCSimpleBlock |
               FCComplexBlock [FCBlock] |
               FCCondBlock {
                 -- | 
                 condition ::FCSimpleBlock,
                 -- | 
                 onSuccess::FCBlock} |
               FCCondElseBlock {
                 -- | 
                 condition :: FCSimpleBlock,
                 -- | 
                 onSuccess :: FCBlock,
                 -- | 
                 onFail :: FCBlock} |
               FCWhileBlock {
                 -- | 
                 condition :: FCSimpleBlock,
                 -- | 
                 onSuccess :: FCBlock}
  

type FCFun = (String, [FCBlock])

class (Ord key) => Environment a key value | a -> key value where
  declareMapping :: key -> value -> a -> a
  getMapping :: key -> a -> Maybe value
  lookupMapping :: key -> a -> Bool
  
class (Environment a key value) => VariableEnvironment a key value | a -> key value where
  setVariable :: key -> value -> a -> a
  declareVariable :: key -> value -> a -> a
  lookupVariable :: key -> a -> Bool
  getManyVariables :: [key] -> a -> [Maybe value]
  newClosure :: a -> a
  oldClosure :: a -> a
  getVariable :: key -> a -> Maybe value

class LLRegisterState a where
  nextNRegiter         ::  a -> a
  nextPRegisert        ::  a -> a
  lookupNextNRegister  ::  a -> FCRegister
  lookupNextPRegister  :: a -> FCRegister

class BlockBuilder a stmtType blockType | a -> stmtType blockType where
  openNewBlock :: a -> a
  closeBlock :: a -> a
  prependStmt :: stmtType -> a -> a
  prependBlock :: blockType -> a -> a
  buildCurrentBlock :: a -> (a, blockType)
  build :: a -> blockType

data FCC venvData blockData regData constants=
  (VariableEnvironment venvData String FCRegister,
   BlockBuilder blockData FCInstr FCBlock,
   LLRegisterState regData,
   Environment constants String String) => FCC {regst:: regData, venv :: venvData, blockstate :: blockData, consts :: constants}
  
data RegType = RNormal | RDynamic | RPhi | RVoid

data BlockType = Normal | Cond | CondElse | While

-- class (MonadError SemanticError a) => ExpToFCStateMonad a where
--   lookupStringName     :: String -> a String
--   lookupNextNRegister  :: a FCRegister
--   nextNRegiter         :: a FCRegister
--   nextPRegisert        :: a FCRegister
--   setRegister          :: FCRegister -> FCRValue -> a ()
--   getRegister          :: FCRegister -> a FCRValue
--   fCRValToReg          :: FCRValue -> a (Maybe FCRegister)
--   prependFCRValue      :: RegType -> FCRValue -> a FCRegister
--   getVariable          :: String -> a (Maybe FCRegister) -- Maybe is somehow redundant but it's a good practice to dobule check
--   isFunStatic          :: String -> a Bool


-- class (ExpToFCStateMonad a) => InstrToFCStateMonad a where
--   -- | Ustawia wartość zmiennej na wartość rejestru i ją przekazuje
--   setVariable :: String -> FCRegister -> a FCRegister
--   declareVariable :: String -> FCRegister -> a FCRegister
--   -- getVEnv :: a (DM.Map String FCRegister)
--   getRedeclaredVariables :: a [String]
--   getModifiedVariables :: a [String]

--   openNewBlock :: BlockType -> a ()
--   closeBlock :: a FCBlock
--   appendBlock :: FCBlock -> a()

--   addBlock :: stmts -> (stmts -> a ()) -> a ()

--   addBlock stms translate = do
--     openNewBlock Normal
--     translate stms
--     res <- closeBlock
--     appendBlock res
    
    
--   addIfBlock:: (expr, stmts) -> (expr -> a FCRegister) -> (stmts -> a()) -> a()
--   addIfBlock (condition, success) t1 t2 = do
--     openNewBlock Normal
--     t1 condition
--     condBlock <- closeBlock
--     openNewBlock Cond
--     t2 success
--     modifiedVar <- getModifiedVariables
    
--     return ()
--   addIfBlockSimp :: a FCRegister -> a () -> a()
--   addIfElseBlock :: (expr, stmts, stmts) -> (expr -> a FCRegister) -> (stmts -> a()) -> a()
--   addWhileBlock :: (expr, stmts) -> (expr -> a FCRegister) -> (stmts -> a()) -> a()
-- -- class (ExpToFCStateMonad m) => BlockToFCStateMonad m where
-- --   setVariable_ :: String -> FCRegister -> m FCRegister



-- instance Show FCRegister where
--   showsPrec _ VoidReg = showString ""
--   showsPrec _ (Reg str) = showString str
--   showsPrec y (LitBool x) = showsPrec y x
--   showsPrec y (LitInt x) = showsPrec y x


-- instance Convertable Tr.IAddOp FCBinaryOperator where
--   convert x = case x of
--     Tr.IPlus -> Add
--     Tr.IMinus -> Sub

-- instance Convertable Tr.IMulOp FCBinaryOperator where
--   convert x = case x of
--     Tr.ITimes -> Mul
--     Tr.IDiv -> Div
--     Tr.IMod -> Mod
