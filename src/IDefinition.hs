
{-# LANGUAGE FlexibleInstances #-}
module IDefinition (LType(..), VarType(..), convertType, getArgLType,
                   SemanticError (..), SemanticErrorType (..), topDefArgs, topDefBlock,
                   VariableEnvironment (..), Indexed(..),
                   LItem(..), LBlock(..), LStmt(..), IFun(..)
                   ) where

import Prelude
import Data.Set (Set)
import Data.Map (Map)
import Latte.Abs
    ( TopDef,
      Arg,
      Arg'(Arg),
      Ident(..),
      Type'(Fun, Int, Str, Bool, Void),
      TopDef'(FnDef),
      Block,
      Item,
      Item'(Init, NoInit),
      Type )

data LType = LInt | LString | LBool | LVoid | LFun LType [LType]

data VarType = StaticInt Int | DynamicInt | StaticBool Bool | DynamicBool |
              StaticString String | DynamicString

data SemanticErrorType = WrongReturnType {position:: (Int, Int), expected :: LType, got :: LType} |
                         RedefinitionOfVariable {position :: (Int, Int), oldDefinition :: (Int, Int),
                                                 name :: String} |
                         RedefinitionOfFunction {position :: (Int, Int), oldDefinition :: (Int, Int),
                                                 name :: String} |
                         NoReturnValueInBlock {position :: (Int, Int), blockPosition :: (Int, Int),
                                               returnType :: LType} |
                         NoMain 

data SemanticError = SemanticError {functionPosition :: (Int, Int),
                                    error :: SemanticErrorType} | PlaceHolder

data VariableEnvironment = VEnv (Set String) (Map String VarType)

convertType :: Type -> LType
convertType (Int _) = LInt
convertType (Str _) = LString
convertType (Bool _) = LBool
convertType (Void _) = LVoid
convertType (Fun _ x y) = LFun (convertType x) $ map convertType y


getArgLType :: Arg -> LType
getArgLType (Arg _ aType _) = convertType aType

topDefArgs :: TopDef -> [Arg]
topDefArgs (FnDef _ _ _ args _) = args

topDefBlock :: TopDef -> Block
topDefBlock (FnDef _ _ _ _ block) = block


data LItem = XXXX

data LExpr = XXXXX

data LStmt = LBStmt LBlock |
  LDecl [LItem] |
  LAss String LExpr |
  LIncr String |
  LDecr String |
  LRet LExpr |
  LVRet |
  LCond LExpr LStmt |
  LCondElse LExpr LStmt LStmt |
  LWhile LExpr LStmt |
  LSExp LExpr |
  LStmtEmpty
  
newtype LBlock = LBlock [LStmt]

newtype IFun = IFun LBlock



class Indexed a where
  getId :: a -> Ident
  getIdStr :: a -> String
  getIdStr x = id
    where (Ident id) = getId x

instance Indexed Arg where
  getId (Arg _ _ id) = id

instance Indexed TopDef where
  getId (FnDef _ _ id _ _ ) = id

instance Indexed Item where
  getId (NoInit _ id) = id
  getId (Init _ id _) = id
