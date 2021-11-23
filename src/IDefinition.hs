module IDefinition (LType, convertType, getArgLType) where

import Prelude
import Latte.Abs

data LType = LInt | LString | LBool | LVoid | LFun LType [LType]

data SemanticErrorType = WrongReturnType {position:: (Int, Int), expected :: LType, got :: LType} |
                         RedefinitionOfVariable {position :: (Int, Int), oldDefinition :: (Int, Int),
                                                 name :: Ident} |
                         RedefinitionOfFunction {position :: (Int, Int), oldDefinition :: (Int, Int),
                                                 name :: Ident} |
                         NoReturnValueInBlock {position :: (Int, Int), blockPosition :: (Int, Int),
                                               returnType :: LType}

data SemanticError = SemanticError {functionPosition :: (Int, Int),
                                    error :: SemanticErrorType}

convertType :: Type -> LType
convertType (Int _) = LInt
convertType (Str _) = LString
convertType (Bool _) = LBool
convertType (Void _) = LVoid
convertType (Fun _ x y) = LFun (convertType x) $ map convertType y

getArgLType :: Arg -> LType
getArgLType (Arg _ aType _) = convertType aType

getArgId :: Arg -> Ident
getArgId (Arg _ _ id) = id
