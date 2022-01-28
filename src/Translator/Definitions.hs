{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Translator.Definitions where

import IDefinition (LType(..), EnrichedClassDef')
import qualified Data.Set as DS
import Latte.Abs
import Control.Monad.Except (Except)
import CompilationError (SemanticError)

type CompilerExcept = Except SemanticError

type IType = LType

data MetaData = MD {modVars :: [ILValue]}

instance Show MetaData where
  show (MD md) = "(MD $ DS.fromList " ++ show md ++ ")"

data IStmt =  IBStmt IBlock |
  IDecl [IItem] |
  IAss ILValue IExpr |
  IIncr ILValue |
  IDecr ILValue |
  IRet IExpr |
  IVRet |
  ICond IExpr IBlock MetaData |
  ICondElse IExpr IBlock IBlock MetaData |
  IWhile IExpr IBlock MetaData |
  ISExp IExpr |
  IStmtEmpty 
  deriving Show

newtype IBlock = IBlock [IStmt]
  deriving Show

data IItem = IItem String IExpr
  deriving Show

data ILValue = IVar String | IMember ILValue String | IBracketOp String IExpr
  deriving (Eq, Show)

data IExpr = ILitInt Integer |
  ILitBool Bool |
  IApp String [IExpr] |
  ILValue ILValue |
  IString String |
  INeg IExpr |
  INot IExpr |
  IAnd [IExpr] |
  IOr [IExpr] |
  IAdd IAddOp IExpr IExpr |
  IMul IMulOp IExpr IExpr |
  IRel IRelOp IExpr IExpr |
  INull |
  INew LType |
  ICast LType IExpr -- Tu powinien być jakiś typ przechodni.
  deriving (Eq, Show)

data IMulOp = ITimes | IDiv | IMod
  deriving (Eq, Show)
data IAddOp = IPlus | IMinus
  deriving (Eq, Show)
data IRelOp = ILTH | ILE | IGTH | IGE | IEQU | INE
  deriving (Eq, Show)

type Reference = Int

data IValue = IValueInt Integer | IValueBool Bool | IValueString String | Null | Undefined |
              RunTimeValue | OwningReference Reference
  deriving Eq

data IFun = IFun String LType [(String, LType)] IBlock
  deriving Show

class ApplicativeBiOperator a b c where
  appOp :: a -> b -> b -> c

instance Integral a => ApplicativeBiOperator AddOp a a where
  appOp (Plus _) = (+)
  appOp (Minus _) = (-)

instance ApplicativeBiOperator MulOp Integer Integer where
  appOp (Times _) = (*)
  appOp (Div _) = div
  appOp (Mod _) = mod

instance Ord a => ApplicativeBiOperator RelOp a Bool where
  appOp (LTH _)  = (<)
  appOp (LE _)   = (<=)
  appOp (EQU _)  = (==)
  appOp (NE _)   = (/=)
  appOp (GTH _)  = (>)
  appOp (GE _)   = (>=)

instance ApplicativeBiOperator IAddOp Integer Integer where
  appOp IPlus = (+)
  appOp IMinus = (-)

instance ApplicativeBiOperator IMulOp Integer Integer where
  appOp ITimes = (*)
  appOp IDiv = div
  appOp IMod = mod

instance Ord a => ApplicativeBiOperator IRelOp a Bool where
  appOp ILTH  = (<)
  appOp ILE   = (<=)
  appOp IEQU  = (==)
  appOp INE   = (/=)
  appOp IGTH  = (>)
  appOp IGE   = (>=)

