
{-# LANGUAGE FlexibleInstances #-}
module IDefinition (LType(..), VarType(..), convertType, getArgLType,
                   topDefArgs, topDefBlock,
                   Indexed(..), getPosition, TypeClass(..)
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
      Type, HasPosition (hasPosition) )
import Data.Maybe (fromMaybe)

data LType = LInt | LString | LBool | LVoid | LFun LType [LType]
  deriving Eq

data VarType = StaticInt Int | DynamicInt | StaticBool Bool | DynamicBool |
              StaticString String | DynamicString


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

getPosition :: (HasPosition a) => a -> (Int, Int)
getPosition a = (-1, -1) `fromMaybe` hasPosition a

class TypeClass a where
  cast :: a -> LType
  same :: (TypeClass b) => a -> b -> Bool
  same a b = cast a == cast b

instance TypeClass LType where
  cast x = x

instance Show LType where
  showsPrec x LInt = showString "Int"
  showsPrec x LBool = showString "Bool"
  showsPrec x LVoid = showString "Void"
  showsPrec x LString = showString "String"
