{-# LANGUAGE LambdaCase #-}
module Translator.TranslatorEnvironment(FunctionData,
                                        FunctionEnvironment,
                                        StructureEnvironment(..),
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
                                        isSubClass,
                                        getClassEnv,
                                        getContext,
                                        initialEnvironment) where

import Translator.Definitions
import IDefinition
import CompilationError
import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import qualified Data.Set as DS
import qualified Data.Ord as DO
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Maybe (fromMaybe, isNothing, isJust, fromJust)
import Data.Foldable (foldlM)
import Latte.Abs (FieldDeclItem' (FieldDeclItem),
                  FieldDeclItem)
import Control.Monad.Reader
import Class (Class(className))

type FunctionData = (LType, [LType])
data StructureData = StructureData {fields :: [(String, LType)],
                                    superclass :: Maybe String,
                                    definedFields :: [(String, LType)],
                                    inheritedFields :: [(String, LType)],
                                    methods :: DM.Map String FunctionData,
                                    methodsParents :: DM.Map String String}


type FunctionEnvironment = DM.Map String FunctionData
type StructureDataMap = DM.Map String StructureData

data StructureEnvironment = StructureEnvironment {
  classMap :: StructureDataMap,
  inheritanceInfo :: InheritenceHierarchy
  }

instance Show StructureEnvironment where
  show senv = show $ DM.toList (classMap senv)

instance Show StructureData where
  show sd = show (fields sd) ++ "," ++ show (definedFields sd)

type FunctionContext = (LType, String, (Int, Int), Maybe String)

type TranslationEnvironment = (FunctionEnvironment, StructureEnvironment, FunctionContext)

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
                                     ("_strneq", (LBool, [LString, LString])),
                                     ("_new", (LClass "" ,[LInt]))]


getFunEnv :: TranslationEnvironment -> FunctionEnvironment
getFunEnv (x, y, z) = x
getContext :: TranslationEnvironment -> FunctionContext
getContext (x, y, z) = z
getClassEnv :: TranslationEnvironment -> StructureEnvironment
getClassEnv (x, y, z) = y

lookupClass :: String -> TranslationEnvironment -> Maybe StructureData
lookupClass className te = DM.lookup className $ (classMap . getClassEnv) te

type StateStrMap x = State (DM.Map String x)

isSubClass ::  LType -> LType -> TranslationEnvironment -> Bool
isSubClass x y (_, se,_ ) = seIsSubclass x y se
seIsSubclass :: LType -> LType -> StructureEnvironment -> Bool
seIsSubclass type1 type2 se= case (type1, type2) of
  (LClass sub, LClass c) -> let
    noAncestors = Prelude.error $ "Not even an empty list of ancestors for class: " ++ sub
    ancestors = fromMaybe noAncestors $ DM.lookup sub (ihAncestors $ inheritanceInfo se)
    in
    DL.elem c ancestors
  _ -> False

sdHasField :: String -> StructureData -> Bool
sdHasField fieldName sd = case sdFieldType fieldName sd of
  Just _ -> True
  Nothing -> False
sdFieldType :: String -> StructureData -> Maybe LType
sdFieldType fieldName sd = snd <$> DL.find ((fieldName==).fst) (fields sd)
sdHasMethod :: String -> StructureData -> Bool
hasField :: String -> String -> TranslationEnvironment -> Bool
hasField  structure field tEnv = isJust $ fieldType structure field tEnv
fieldType :: String -> String -> TranslationEnvironment -> Maybe LType
fieldType structure fieldName tEnv = DM.lookup structure (classMap $ getClassEnv tEnv) >>=  DL.lookup fieldName . fields

-- type TemporalStructureEnvironment = DS.Set String
-- getStructureEnvironment :: Program -> CompilerExcept StructureEnvironment
-- getStructureEnvironment (Program _ _ structDefs) = do
--   _ <- structNames structDefs
--   foldlM buildEnv DM.empty (sortClassDefs structDefs)
--   where
--     buildEnv :: StructureEnvironment -> ClassDef -> CompilerExcept StructureEnvironment
--     buildEnv map  classDef = do
--       (className, superclass, initial, cmds) <- case classDef of
--         ClassDef ma (Ident className) cmds -> return (className, Nothing, [], cmds)
--         ClassDefExtends ma (Ident className) (Ident parent) cmds -> do
--           let parentDef = DM.lookup parent map
--           case parentDef of
--             Nothing -> throwError $ SemanticError (undefined `fromMaybe` ma)
--                                          (SuperclassNonexisting className parent)
--             Just sd -> return (className, Just parent, fields sd, cmds)
--       fields <- foldlM (structureDataBuildFields (getPosition classDef)) initial cmds
--       return $ DM.insert className (StructureData fields superclass undefined undefined) map
--     structureDataBuildFields :: (Int, Int) -> [(String, LType)] -> ClassMemberDef ->
--       CompilerExcept [(String, LType)]
--     structureDataBuildFields pos rest x = let
--       FieldDecl ma ty fdis = x
--       ltype = convertType ty
--       in
--       foldlM (\list (FieldDeclItem pos' (Ident id)) ->
--                 do
--                   let previousDef = DL.lookup id list
--                   if maybe False (ltype /=) previousDef
--                     then throwError $ SemanticError pos (RedefinitionOfField ((-1,-1) `fromMaybe` pos') id)
--                     else return ((id, ltype):list)
--                   ) rest fdis
--     sortClassDefs :: [ClassDef] -> [ClassDef]
--     sortClassDefs  = DL.sortOn f
--       where
--         f :: ClassDef -> String
--         f = \case
--           ClassDef _ (Ident id) _ -> "0_" ++ id
--           ClassDefExtends _ (Ident name) (Ident parent) _ -> "1_" ++ parent ++ "_" ++ name
--     structNames :: [ClassDef] -> CompilerExcept (DS.Set String)
--     structNames = foldlM
--           (\set def ->
--              (do
--                  let sName = getIdStr def
--                  when (DS.member sName set) (throwError (SemanticError (getPosition def) (RedefinitionOfStructure (getPosition def) sName)))
--                  return (DS.insert sName set)))
--           DS.empty

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
    result = Prelude.foldl (flip checkFunction) (return $ return initialEnvironment) topDef
  in
    evalState result DM.empty



classParsingPhase1 :: [ClassDef] -> CompilerExcept (DS.Set String)
classParsingPhase1 = foldlM
  (\set def ->
      (do
          let sName = getIdStr def
          when (DS.member sName set) (throwError (SemanticError (getPosition def) (RedefinitionOfStructure (getPosition def) sName)))
          return (DS.insert sName set)))
          DS.empty

data InheritenceHierarchy = InheritenceHierarchy {
  ihChildren :: DM.Map String [String],
  ihDescendants :: DM.Map String [String],
  ihAncestors :: DM.Map String [String],
  ihBaseClasses :: DS.Set String }


ihAddBaseClass :: String -> InheritenceHierarchy -> InheritenceHierarchy
ihAddBaseClass string (InheritenceHierarchy ihc ihd iha ibc) =  InheritenceHierarchy (DM.insert string [] ihc)
  (DM.insert string [] ihd) (DM.insert string [] iha) (DS.insert string ibc)
ihAddClassInheritence :: String -> String -> InheritenceHierarchy -> InheritenceHierarchy
ihAddClassInheritence className parentName ih = let
  noAncestors = Prelude.error $ "Not even an empty list of ancestors for parentclass: " ++ parentName
  ancestors = parentName : noAncestors `fromMaybe` DM.lookup parentName (ihAncestors ih)
  in
  InheritenceHierarchy { ihChildren=ihChildren ih,
                         ihDescendants=ihDescendants ih,
                         ihAncestors=DM.insert className ancestors (ihAncestors ih),
                         ihBaseClasses=ihBaseClasses ih}

ihIsAncestor :: String -> String -> InheritenceHierarchy -> Bool
ihIsAncestor potentialAncestor className ih =
  let
    x = (potentialAncestor `DL.elem`) <$> DM.lookup className (ihAncestors ih)
  in
    Just True == x

classParsingPhase2 :: DS.Set String -> [ClassDef] -> CompilerExcept InheritenceHierarchy
classParsingPhase2 set defs = runReaderT (classParsingPhase2' defs) set
  where
    classParsingPhase2' :: [ClassDef] -> (ReaderT (DS.Set String) CompilerExcept) InheritenceHierarchy
    classParsingPhase2' = foldM f (InheritenceHierarchy DM.empty DM.empty DM.empty DS.empty)
      where
        f :: InheritenceHierarchy -> ClassDef -> (ReaderT (DS.Set String) CompilerExcept) InheritenceHierarchy
        f ih x = case x of
          ClassDef ma (Ident id) cmds methods-> return $ ihAddBaseClass id ih
          ClassDefExtends ma (Ident className) (Ident parentName) cmds methods -> do
            realClass <- asks $ DS.member parentName
            unless realClass (throwError (SemanticError
                                             (fromJust ma)
                                             (SuperclassNonexisting className parentName)))
            when (ihIsAncestor className parentName ih) (throwError (SemanticError
                                                                     (fromJust ma)
                                                                     CircularInheritence))
            return $ ihAddClassInheritence className parentName ih

classParsingPhase3 :: InheritenceHierarchy -> [ClassDef] -> CompilerExcept StructureDataMap
classParsingPhase3 ih defs = runReaderT (foldM f DM.empty defs) ih
  where
    f :: StructureDataMap -> ClassDef ->
         (ReaderT InheritenceHierarchy CompilerExcept) StructureDataMap
    f se classdef = do
      (initFields, inheritedMethods, methodToDeclaration) <- case classdef of
                      ClassDef {} -> return ([], DM.empty, DM.empty)
                      ClassDefExtends _ _ (Ident parent) _  _ ->
                        let
                          parentSD = fromJust (DM.lookup parent se)
                          in
                          return (fields parentSD, methods parentSD, methodsParents parentSD)
      let (className, parent, cmds, _methods) =case classdef of
            ClassDef ma (Ident id) cmds methods -> (id, Nothing, cmds, methods)
            ClassDefExtends ma (Ident id) (Ident parentName) cmds methods -> (id, Just parentName, cmds, methods)


      -- Now we parse methods --
      (_methods, _parentsMethods, _) <- foldlM
        (\(mMap, declMap, alreadyDeclared) method -> do
            let MethodDecl ma ty (Ident id) ars eb = method
            case DM.lookup id mMap of
              Nothing -> return (DM.insert id (convertType ty, map (\(Arg _ t _) -> convertType t) ars) mMap,
                                 DM.insert id className declMap,
                                 DS.insert id alreadyDeclared)
              Just (ty', ars') -> if DS.member id alreadyDeclared then Prelude.error "WIP-Redefinicja metody"
                else do
                unless (ty' `same` convertType ty) $ throwError undefined
                mapM_ (\(x,y)-> unless (x `same` (\(Arg _ t _) -> convertType t) y) (throwError undefined)) (zip ars' ars)
                return (mMap, declMap, DS.insert id alreadyDeclared)
            )
        (inheritedMethods, methodToDeclaration, DS.empty) _methods
      -- --


      (inherited, rdefined) <- foldlM buildField (initFields, []) cmds
      let defined = reverse rdefined


      return (DM.insert className (StructureData (inherited ++ defined) parent defined inherited _methods _parentsMethods) se)
    _convertType :: Type -> (ReaderT InheritenceHierarchy CompilerExcept) LType
    _convertType ptype = do
      let converted = convertType ptype
          pos = getPosition ptype
      case converted of
        LFun lt lts -> undefined
        LClass s -> do
          issubclass <- asks $ DM.member s . ihAncestors
          isbaseclass <- asks $ DS.member s . ihBaseClasses
          unless (issubclass || isbaseclass) (throwError (SemanticError pos $ UndefinedClass pos s))
        _ -> return ()
      return converted
    buildField :: ([(String, LType)], [(String, LType)]) -> ClassMemberDef
      -> (ReaderT InheritenceHierarchy CompilerExcept)
      ([(String, LType)], [(String, LType)])
    buildField result = \case
      FieldDecl ma ty fdis -> do
        ltype <- _convertType ty
        (l1, l2)<- foldM (f ltype) result fdis
        return (l1, l2)
      where
        f :: LType -> ([(String, LType)], [(String, LType)])
          -> FieldDeclItem
          -> (ReaderT InheritenceHierarchy CompilerExcept)
          ([(String, LType)], [(String, LType)])
        f ltype res@(inh, def) = \case
          FieldDeclItem ma (Ident id) -> do
            if isJust (DL.lookup id def) || isJust (DL.lookup id inh)
              then throwError $
                     SemanticError (fromJust ma) (RedefinitionOfField (fromJust ma) id)
              else return (inh, (id, ltype):def)

getStructureEnvironment :: Program -> CompilerExcept StructureEnvironment
getStructureEnvironment (Program _ _ structDefs) = do
  x <- classParsingPhase1 structDefs
  y <- classParsingPhase2 x structDefs
  z <- classParsingPhase3 y structDefs
  return (StructureEnvironment z y)
