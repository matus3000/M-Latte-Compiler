{-# LANGUAGE LambdaCase #-}
module Translator.TranslatorEnvironment(FunctionData,
                                        FunctionEnvironment,
                                        StructureEnvironment,
                                        StructureData(..),
                                        getStructureEnvironment,
                                        getFunctionEnvironment,
                                        TranslationEnvironment,
                                        sdFieldType,
                                        sdHasField,
                                        getFunEnv,
                                        hasField,
                                        fieldType,
                                        lookupClass,
                                        getClassEnv,
                                        getContext) where

import Translator.Definitions
import IDefinition
import CompilationError
import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import qualified Data.Set as DS
import qualified Data.Ord as DO
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Maybe (fromMaybe, isNothing, isJust)
import Data.Foldable (foldlM)
import Latte.Abs (ClassMemberDef' (FieldDecl), ClassMemberDef, FieldDeclItem' (FieldDeclItem))

type FunctionData = (LType, [LType])
data StructureData = StructureData {fields :: [(String, LType)],
                                    superclass :: Maybe String}
type FunctionEnvironment = DM.Map String FunctionData
type StructureEnvironment = DM.Map String StructureData
type FunctionContext = (LType, String, (Int, Int))

type TranslationEnvironment = (FunctionEnvironment, StructureEnvironment, FunctionContext)

getFunEnv :: TranslationEnvironment -> FunctionEnvironment
getFunEnv (x, y, z) = x
getContext :: TranslationEnvironment -> FunctionContext
getContext (x, y, z) = z
getClassEnv :: TranslationEnvironment -> StructureEnvironment
getClassEnv (x, y, z) = y

lookupClass :: String -> TranslationEnvironment -> Maybe StructureData
lookupClass className te = DM.lookup className $ getClassEnv te

type StateStrMap x = State (DM.Map String x)

sdHasField :: String -> StructureData -> Bool
sdHasField fieldName sd = case sdFieldType fieldName sd of
  Just _ -> True
  Nothing -> False
sdFieldType :: String -> StructureData -> Maybe LType
sdFieldType fieldName sd = snd <$> DL.find ((fieldName==).fst) (fields sd)

hasField :: String -> String -> TranslationEnvironment -> Bool
hasField  structure field tEnv = isJust $ fieldType structure field tEnv
fieldType :: String -> String -> TranslationEnvironment -> Maybe LType
fieldType structure fieldName tEnv = DM.lookup structure (getClassEnv tEnv) >>=  (DL.lookup fieldName . fields)

type TemporalStructureEnvironment = DS.Set String
getStructureEnvironment :: Program -> CompilerExcept StructureEnvironment
getStructureEnvironment (Program _ _ structDefs) = do
  _ <- structNames structDefs
  foldlM buildEnv DM.empty (sortClassDefs structDefs)
  where
    buildEnv :: StructureEnvironment -> ClassDef -> CompilerExcept StructureEnvironment
    buildEnv map  classDef = do
      (className, superclass, initial, cmds) <- case classDef of
        ClassDef ma (Ident className) cmds -> return (className, Nothing, [], cmds)
        ClassDefExtends ma (Ident className) (Ident parent) cmds -> do
          let parentDef = DM.lookup parent map
          case parentDef of
            Nothing -> throwError $ SemanticError (undefined `fromMaybe` ma)
                                         (SuperclassNonexisting className parent)
            Just sd -> return (className, Just parent, fields sd, cmds)
      fields <- foldlM (structureDataBuildFields (getPosition classDef)) initial cmds
      return $ DM.insert className (StructureData fields superclass) map
    structureDataBuildFields :: (Int, Int) -> [(String, LType)] -> ClassMemberDef ->
      CompilerExcept [(String, LType)]
    structureDataBuildFields pos rest x = let
      FieldDecl ma ty fdis = x
      ltype = convertType ty
      in
      foldlM (\list (FieldDeclItem pos' (Ident id)) ->
                do
                  let previousDef = DL.lookup id list
                  if maybe False (ltype /=) previousDef
                    then throwError $ SemanticError pos (RedefinitionOfField ((-1,-1) `fromMaybe` pos') id)
                    else return ((id, ltype):list)
                  ) rest fdis
    sortClassDefs :: [ClassDef] -> [ClassDef]
    sortClassDefs  = DL.sortOn f
      where
        f :: ClassDef -> String
        f = \case
          ClassDef _ (Ident id) _ -> "0_" ++ id
          ClassDefExtends _ (Ident name) (Ident parent) _ -> "1_" ++ parent ++ "_" ++ name
    structNames :: [ClassDef] -> CompilerExcept (DS.Set String)
    structNames = foldlM
          (\set def ->
             (do
                 let sName = getIdStr def
                 when (DS.member sName set) (throwError (SemanticError (getPosition def) (RedefinitionOfStructure (getPosition def) sName)))
                 return (DS.insert sName set)))
          DS.empty

getFunctionEnvironment :: Program -> CompilerExcept FunctionEnvironment
getFunctionEnvironment (Program _ topDef structDef) =
  let
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
              x :: SemanticErrorType
              x = RedefinitionOfVariable (getPosition new) (getPosition old) (getIdStr old)
            in
              throwError $ SemanticError (getPosition f) x
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
    initialEnvironment :: FunctionEnvironment
    initialEnvironment = DM.fromList [("printInt", (LVoid, [LInt])),
                                      ("printString", (LVoid, [LString])),
                                     ("error", (LVoid, [])),
                                     ("readInt", (LInt, [])),
                                     ("readString", (LString, [])),
                                     ("_strconcat", (LString, [LString, LString])),
                                     ("_strle", (LBool, [LString, LString])),
                                     ("_strlt", (LBool, [LString, LString])),
                                     ("_strge", (LBool, [LString, LString])),
                                     ("_strgt", (LBool, [LString, LString])),
                                     ("_streq", (LBool, [LString, LString])),
                                     ("_strneq", (LBool, [LString, LString]))]
    result = Prelude.foldl (flip checkFunction) (return $ return initialEnvironment) topDef
  in
    evalState result DM.empty
