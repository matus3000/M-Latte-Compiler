module CompilationError (SemanticError(..), SemanticErrorType(..), errorToString) where
import IDefinition (LType (LVoid))
import Prelude hiding (error)

data SemanticErrorType = WrongReturnType {position:: (Int, Int), expected :: LType, got :: LType} |
                         RedefinitionOfVariable {position :: (Int, Int), oldDefinition :: (Int, Int),
                                                 name :: String} |
                         RedefinitionOfFunction {position :: (Int, Int), oldDefinition :: (Int, Int),
                                                 name :: String} |
                         NoReturnValue {returnType :: LType} |
                         UndefinedVar {position:: (Int, Int), name:: String} |
                         UndefinedFun {position:: (Int, Int), name:: String} |
                         WrongArgumentCount {position::(Int, Int)} |
                         NoMain |
                         DivisionByZero {position:: (Int, Int)} |
                         TypeConflict {position :: (Int, Int), expected:: LType, got :: LType} |
                         BinaryTypeConflict {position :: (Int, Int),
                                            gotPair :: (LType, LType)}

data SemanticError = SemanticError {functionPosition :: (Int, Int),
                                    error :: SemanticErrorType} |
                     CompilationError

msg :: (Int, Int) -> String
msg (line, col) = "Error in position (" ++ show line ++ ", " ++ show col ++ "): "

errorToString :: SemanticError -> String
errorToString (SemanticError pos NoMain) = "No main function"
errorToString err = let
  (line, col) = functionPosition err
  in
  "Error in function starting at line: " ++ show line ++ " and column " ++ show col ++ "\n" ++ show (error err)

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
