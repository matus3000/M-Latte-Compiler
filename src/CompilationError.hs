{-# LANGUAGE LambdaCase #-}
module CompilationError (SemanticError(..), SemanticErrorType(..), errorToString, errorToStringExtended) where
import IDefinition (LType (LVoid), LValue)
import Prelude hiding (error)

data SemanticErrorType = WrongReturnType {position:: (Int, Int), expected :: LType, got :: LType} |
                         RedefinitionOfVariable {position :: (Int, Int), oldDefinition :: (Int, Int),
                                                 name :: String} |
                         RedefinitionOfFunction {position :: (Int, Int), oldDefinition :: (Int, Int),
                                                 name :: String} |
                         RedefinitionOfStructure {position :: (Int, Int), name :: String} |
                         RedefinitionOfField {position :: (Int, Int), name :: String } |
                         SuperclassNonexisting {name :: String , superclass :: String} |
                         NotClass {pos :: (Int, Int), name :: String} |
                         ExpectedClass {pos :: (Int, Int), got :: LType } |
                         NoReturnValue {returnType :: LType} |
                         NullDereference {position :: (Int, Int)} |
                         UndefinedDerefence {positiont :: (Int, Int)} |
                         UndefinedVar {position:: (Int, Int), name :: String} |
                         UndefinedFun {position:: (Int, Int), name :: String} |
                         UndefinedClass {position:: (Int, Int), name :: String} |
                         UndefinedField {position:: (Int, Int), name :: String} |
                         WrongArgumentCount {position::(Int, Int)} |
                         CircularInheritence |
                         NoMain |
                         PrimitiveType {position::(Int, Int), got :: LType} |
                         DivisionByZero {position:: (Int, Int)} |
                         TypeConflict {position :: (Int, Int), expected:: LType, got :: LType} |
                         BinaryTypeConflict {position :: (Int, Int),
                                            gotPair :: (LType, LType)} |
                         UnhappyCompiler {position :: (Int, Int)}

data SemanticError = SemanticError {functionPosition :: (Int, Int),
                                    error :: SemanticErrorType}

errorInsideStructure :: SemanticErrorType -> Bool
errorInsideStructure = \case
  RedefinitionOfStructure {} -> True
  RedefinitionOfField {} -> True
  SuperclassNonexisting {} -> True
  _ -> False

errorInsideFunction :: SemanticErrorType -> Bool
errorInsideFunction = \case
  RedefinitionOfFunction x0 x1 s -> True
  NoMain -> False
  RedefinitionOfStructure {} -> False
  RedefinitionOfField {} -> False
  SuperclassNonexisting {} -> False
  _ -> True

msg :: (Int, Int) -> String
msg (line, col) = "Error in position (" ++ show line ++ ", " ++ show col ++ "): \n"

printArrow :: Int -> String
printArrow x = "\ESC[91m" ++ map (const '_') [1..(x-1)] ++ "^\n" -- ++ map (const '_') [1..(x-1)] ++ "|\n"
  ++ "\ESC[0m"

msgExtended :: (Int, Int) -> [String] -> String
msgExtended (line, col) _lines = "Error in position (" ++ show line ++ ", " ++ show col ++ "): \n" ++
  (_lines !! (line - 1)) ++"\n" ++ printArrow col

errorToString (SemanticError pos NoMain) = "No main function"
errorToString err@(SemanticError pos errorType) = let
  (line, col) = functionPosition err
  preambule = if errorInsideStructure (error err) then "Error in structure definition" else "Error in function"
  in
  preambule ++ " starting at line: " ++ show line ++ " and column " ++ show col ++ "\n  " ++ show (error err)

errorToStringExtended :: SemanticError -> String -> String
errorToStringExtended (SemanticError pos NoMain) _ = "No main function"
errorToStringExtended err text_of_program =
  let
    by_line = lines text_of_program
    (line, col) = functionPosition err
    funname_ = by_line !! (line - 1)
    funname = funname_
    -- funname = -- if (length funname_ < 40) then funname_ ++ "{...}" else funname_ 
  in
    "Error in function starting at line: " ++ show line ++ " and column " ++ show col ++ "\n  " ++
    funname ++ "\n" ++
    (case err of
        SemanticError x0 error -> case error of
          WrongReturnType pos l1 l2 -> msgExtended' pos ++ "Wrong return type - Expected: " ++ show l1 ++ ", got: " ++ show l2
          RedefinitionOfVariable pos _ x -> msgExtended' pos ++ "Redeclaration of variable: " ++ x
          RedefinitionOfFunction pos _ x -> msgExtended' pos ++ "Redeclaration of function: " ++ x
          NoReturnValue lt -> "Lack of return or existence of possible execution path without return. "
          UndefinedVar pos x -> msgExtended' pos ++ "Undefined variable: " ++  x
          UndefinedFun pos x -> msgExtended' pos ++ "Undefined function: " ++  x
          UndefinedField pos x -> msgExtended' pos ++ "Undefined field: " ++  x
          UndefinedClass pos x -> msgExtended' pos ++ "Undefined class: " ++ x
          WrongArgumentCount pos -> msgExtended' pos ++ "Wrong number of arguments to function call"
          NoMain -> "No main function."
          CircularInheritence -> "CircularInheritence."
          DivisionByZero pos -> msgExtended' pos ++ "Division by zero"
          TypeConflict pos l1 l2 -> msgExtended' pos ++ "TypeConflict - Expected: "
            ++ show l1 ++ ", got: " ++ show l2
          BinaryTypeConflict pos pair -> msgExtended' pos ++
            "TypeConflict - Types do not match binary operator - Got: " ++ show pair
          NullDereference pos -> msgExtended' pos ++ "Null derefernce error: Acquiring field of NULL"
          PrimitiveType {} -> msgExtended' (position error) ++ "New operator is not allowed for a primitive type: "
            ++ show (got error)
          UnhappyCompiler pos -> msgExtended' pos ++ "Why would you do that? Are you insane?"
          UndefinedDerefence pos -> msgExtended' pos ++ "Read from unintialized value"
          where
            msgExtended' = flip msgExtended by_line)


instance Show SemanticErrorType where
  showsPrec _ err = showString
    (case err of
      WrongReturnType pos l1 l2 -> msg pos ++ "Wrong return type - Expected: " ++ show l1 ++ ", got: " ++ show l2
      RedefinitionOfVariable pos _ x -> msg pos ++ "Redeclaration of variable: " ++ x
      RedefinitionOfFunction pos _ x -> msg pos ++ "Redeclaration of function: " ++ x
      NoReturnValue lt -> "Wrong return type - Expected: " ++ show lt ++ ", got: " ++ show LVoid
      UndefinedVar pos x -> msg pos ++ "Undefined variable: " ++  x
      UndefinedFun pos x -> msg pos ++ "Undefined function: " ++  x
      WrongArgumentCount pos -> msg pos ++ "Wrong number of arguments to function call"
      NoMain -> "No main function"
      DivisionByZero pos -> msg pos ++ "Division by zero"
      TypeConflict pos l1 l2 -> msg pos ++ "TypeConflict - Expected: " ++ show l1 ++ ", got: " ++ show l2
      BinaryTypeConflict pos pair -> msg pos ++
        "TypeConflict - Types do not match binary operator - Got: " ++ show pair)
