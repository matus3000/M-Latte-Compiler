
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module IDefinition (LType(..),
                    -- VarType(..),
                    Program,
                    EnrichedProgram'(..),
                    Block,
                    TopDef,
                    EnrichedTopDef'(..),
                    Arg,
                    Arg'(..),
                    EnrichedBlock'(..),
                    Stmt,
                    EnrichedStmt' (..),
                    Item,
                    Item'(..),
                    Type,
                    Type'(..),
                    Expr,
                    Expr'(..),
                    AddOp,
                    AddOp'(..),
                    MulOp,
                    MulOp'(..),
                    RelOp,
                    RelOp'(..),
                    Ident(..),
                    BNFC'Position(..),
                    ClassDef(..),
                    EnrichedClassDef'(..),
                    LValue'(..),
                    LValue,
                    convertType,
                    getArgLType,
                    topDefArgs,
                    topDefBlock,
                    topDefReturnType,
                    Indexed(..),
                    getPosition,
                    TypeClass(..),
                    HasPosition(..),
                    ClassMethodDef,
                    ClassMethodDef'(..),
                    ClassMemberDef,
                    ClassMemberDef'(..),
                    preprocessProgram
                   ) where

import Prelude
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import Latte.Abs
    ( Arg,
      Arg'(Arg),
      AddOp,
      AddOp'(..),
      MulOp,
      MulOp'(..),
      RelOp,
      RelOp'(..),
      Ident(..),
      Type'(Fun, Int, Str, Bool, Void),
      Item,
      Item'(Init, NoInit),
      Type,
      HasPosition (..),
      BNFC'Position(..),
      Expr,
      LValue,
      Expr'(..), LValue' (LVarMem, LVar, LVarArr))
import qualified Latte.Abs as Lt
import Data.Maybe (fromMaybe, isJust, fromJust, catMaybes)
import Data.Maybe (mapMaybe)
import Data.Ord
import qualified Control.Arrow as Data.BiFunctor
import qualified Data.Bifunctor
import qualified Data.List as DL
import qualified Class as LT

import Control.Monad.State.Strict
import qualified Control.Arrow

data LType = LInt | LString | LBool | LVoid | LFun LType [LType] | LArray LType | LClass String |
  LGenericClass String [LType]
  deriving Eq

-- data VarType = StaticInt Int | DynamicInt | StaticBool Bool | DynamicBool |
--               StaticString String | DynamicString

type UnifiedLValue = (String, LValue)
type ModifiedLValues = [(LValue, Bool)]
data ModifiedLvaluesBuilder = MLB (DM.Map UnifiedLValue (LValue, Bool, Int))
                              (DM.Map (String, Bool) (LValue, Bool, Int)) Int
type DeclaredLvalues = (DS.Set String)

lvalueToUnified :: LValue -> UnifiedLValue
lvalueToUnified  = pruneLValue
  where
    pruneLValue :: LValue -> (String, LValue)
    pruneLValue = \case
      LVar ma id@(Ident name) -> (name, LVar Nothing id)
      LVarMem ma lv id -> Data.BiFunctor.second (\x -> LVarMem Nothing x id)(pruneLValue lv)
      LVarArr ma lv ex -> undefined

result :: ModifiedLvaluesBuilder -> [(LValue, Bool)]
result mlb@(MLB map vars x)= DL.map (\(x,y,z)->(x,y)) $ DL.sortOn (\(x,y,z) -> z) (DM.elems vars++ DM.elems map)

mlbInsert :: LValue -> ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder
mlbInsert lvalue = mlbInsertUnified (lvalueToUnified lvalue, lvalue)

mlbNextIndex :: ModifiedLvaluesBuilder -> Int
mlbNextIndex (MLB x var y) = y

mlbIsMember :: Bool -> UnifiedLValue -> ModifiedLvaluesBuilder -> Bool
mlbIsMember recursive unified@(parent, ulval) mlb@(MLB x var y) = case ulval of
  LVar ma id -> DM.member (parent, recursive) var
  LVarMem ma lv id -> any (`DM.member` var) [(parent,True), (parent, False)] || any (`DM.member` x) (ancestors unified)
  LVarArr ma lv ex -> undefined
  where
    ancestors :: UnifiedLValue -> [UnifiedLValue]
    ancestors = \case (s, lv) ->
                        case lv of
                        LVar ma id -> [(s, LVar ma id)]
                        LVarMem ma lv' id -> (s, LVarMem ma lv' id):ancestors (s, lv')
                        LVarArr ma lv' ex -> undefined

mlbInsertUnified :: (UnifiedLValue, LValue) -> ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder
mlbInsertUnified (unified@(s, ulval), lvalue) original@(MLB x var y) =
  if mlbIsMember False unified original then original else case ulval of
    LVar ma id -> MLB x (DM.insert (s, False) (lvalue, False, y) var) (y+1)
    LVarMem ma lv id -> MLB (DM.insert unified (lvalue, False, y) x) var (y+1)
    LVarArr ma lv ex -> undefined

mlbInsertUnifiedRec :: (UnifiedLValue, LValue) -> ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder
mlbInsertUnifiedRec (unified@(s, ulval), lvalue) original@(MLB x var y) =
  if mlbIsMember True unified original then original else case ulval of
    LVar ma id -> MLB x (DM.insert (s, True) (lvalue, True, y) var) (y+1)
    LVarMem ma lv id -> MLB (DM.insert unified (lvalue, True, y) x) var (y+1)
    LVarArr ma lv ex -> undefined

mlbUnion :: ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder
mlbUnion mlb@(MLB map var y) mlb'@(MLB map' var' y') = DL.foldl' f (MLB map (foldl faddVars var (DM.toList var')) (max y y')) (DM.toList map')
  where
    _mlbUnion :: ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder
    _mlbUnion (MLB map var y) (MLB map' var' y') = foldl f (MLB map (foldl faddVars var (DM.toList var')) (max y y')) (DM.toList map')
    faddVars :: DM.Map (String,Bool) (LValue, Bool, Int) -> ((String, Bool), (LValue, Bool, Int)) ->
      DM.Map (String, Bool) (LValue, Bool, Int)
    faddVars map1 (u, t) = if DM.member u map1 then map1 else DM.insert u t map1
    f :: ModifiedLvaluesBuilder -> (UnifiedLValue, (LValue, Bool, Int))
      -> ModifiedLvaluesBuilder
    f (MLB map var y) (u@(s, ulval), t1@(lval, recursive, id))= case DM.lookup u map of
      Nothing -> MLB (DM.insert u t1 map) var y
      Just t2@(lval', recursive', id') -> MLB (DM.insert u (if not recursive' || recursive then t1 else t2) map) var y

mlbEmpty :: Int -> ModifiedLvaluesBuilder
mlbEmpty = MLB DM.empty DM.empty

dlContains :: UnifiedLValue -> DeclaredLvalues -> Bool
dlContains ul dl = DS.member (fst ul) dl
dlInsert ::  UnifiedLValue -> DeclaredLvalues -> DeclaredLvalues
dlInsert ul = DS.insert (fst ul)
dlUnion :: DeclaredLvalues -> DeclaredLvalues -> DeclaredLvalues
dlUnion ul1@s1 ul2@s1' = DS.union s1 s1'
dlEmpty :: DeclaredLvalues
dlEmpty = DS.empty
type Program = EnrichedProgram' BNFC'Position
data EnrichedProgram' a = Program a [EnrichedTopDef' a] [EnrichedClassDef' a]

type TopDef = EnrichedTopDef' BNFC'Position
data EnrichedTopDef' a = FnDef a (Type' a) Ident [Arg' a] (EnrichedBlock' a)

type ClassDef = EnrichedClassDef' BNFC'Position
data EnrichedClassDef' a = ClassDef a Ident [ClassMemberDef' a] [ClassMethodDef' a] |
  ClassDefExtends a Ident Ident [ClassMemberDef' a] [ClassMethodDef' a]

type ClassMemberDef = ClassMemberDef' BNFC'Position
data ClassMemberDef' a = FieldDecl a (Type' a) [Lt.FieldDeclItem' a]

type ClassMethodDef = ClassMethodDef' BNFC'Position
data ClassMethodDef' a = MethodDecl a (Lt.Type' a) Ident [Lt.Arg' a] (EnrichedBlock' a)

type Block = EnrichedBlock' BNFC'Position
data EnrichedBlock' a = Block a [EnrichedStmt' a] |
                        VirtualBlock [EnrichedStmt' a]

type Stmt = EnrichedStmt' BNFC'Position
data EnrichedStmt' a
    = Empty a
    | BStmt a (EnrichedBlock' a)
    | Decl a (Type' a) [Item' a]
    | Ass a (LValue' a) (Expr' a)
    | Incr a (LValue' a)
    | Decr a (LValue' a)
    | Ret a (Expr' a)
    | VRet a
    | Cond a (Expr' a) (EnrichedStmt' a) ModifiedLValues
    | CondElse a (Expr' a) (EnrichedStmt' a) (EnrichedStmt' a) ModifiedLValues
    | While a (Expr' a) (EnrichedStmt' a) ModifiedLValues
    | SExp a (Expr' a)

type DeclaredVars = DS.Set String
addThisEverywhere :: DeclaredVars -> Lt.Block -> Lt.Block
addThisEverywhere decl (Lt.Block ma sts)= Lt.Block ma sts'
  where
    sts' = reverse . snd $
      foldl (\(decl,list) stmt ->
                Control.Arrow.second (:list) (f decl stmt))
      (decl, []) sts
    f :: DeclaredVars -> Lt.Stmt -> (DeclaredVars, Lt.Stmt)
    f decl s = case s of
      Lt.Empty ma' -> (decl, s)
      Lt.BStmt ma' bl -> (decl, Lt.BStmt ma' bl')
        where
          bl' = addThisEverywhere decl bl
      Lt.Decl ma' ty its -> (decl', Lt.Decl ma' ty its')
        where
          (decl', its') = Control.Arrow.second reverse $
               foldl (\(decl, its) it -> Control.Arrow.second (:its) (getDeclared decl it)) (decl, []) its
      Lt.Ass ma' lv ex -> (decl,  Lt.Ass ma' (h decl lv) (g decl ex))
      Lt.Incr ma' lv -> (decl, Lt.Incr ma' (h decl lv))
      Lt.Decr ma' lv -> (decl, Lt.Decr ma' (h decl lv))
      Lt.Ret ma' ex -> (decl, Lt.Ret ma' (g decl ex))
      Lt.VRet ma' -> (decl, s)
      Lt.Cond ma' ex st -> (decl, Lt.Cond ma' (g decl ex) (snd $ f decl st))
      Lt.CondElse ma' ex st st' -> (decl, Lt.CondElse ma' (g decl ex) (snd $ f decl st) (snd $ f decl st'))
      Lt.While ma' ex st -> (decl, Lt.While ma' (g decl ex) (snd $ f decl st))
      Lt.SExp ma' ex -> (decl, Lt.SExp ma' (g decl ex))
    g :: DeclaredVars -> Lt.Expr -> Lt.Expr
    g decl expr = case expr of
      Lt.EMethod ma lv id x0 -> Lt.EMethod ma (h' lv) id (map (g decl) x0)
      Lt.EVar ma' lv -> Lt.EVar ma' (h' lv)
      Lt.ELitInt ma' n -> expr
      Lt.ELitTrue ma' -> expr
      Lt.ELitFalse ma' -> expr
      Lt.ENull ma' -> expr
      Lt.EApp ma' id exs -> Lt.EApp ma' id (map (g decl) exs)
      Lt.EString ma' s -> expr
      Lt.ENewArray ma' ty ex -> undefined
      Lt.ENewClass ma' ty -> expr
      Lt.Neg ma' ex -> Lt.Neg ma' (g decl ex)
      Lt.Not ma' ex -> Not ma' (g decl ex)
      Lt.EMul ma' ex mo ex' -> Lt.EMul ma' (g' ex) mo (g' ex')
      Lt.EAdd ma' ex ao ex' -> Lt.EAdd ma' (g' ex) ao (g' ex')
      Lt.ERel ma' ex ro ex' -> Lt.ERel ma' (g' ex) ro (g' ex')
      Lt.EAnd ma' ex ex' -> Lt.EAnd ma' (g' ex) (g' ex')
      Lt.EOr ma' ex ex' -> Lt.EOr ma' (g' ex) (g' ex')
      Lt.ECast ma' t ex -> Lt.ECast ma' t (g' ex)
      where
        g' = g decl
        h' = h decl
    h :: DeclaredVars -> Lt.LValue -> Lt.LValue
    h decl lval = case lval of
      Lt.LVar ma' (Ident id) -> if DS.member id decl
        then lval
        else Lt.LVarMem ma' (Lt.LVar ma' (Ident "this")) (Ident id)
      Lt.LVarMem ma' lv id -> Lt.LVarMem ma' (h decl lv) id
      Lt.LVarArr ma' lv ex -> undefined
    getDeclared :: DeclaredVars -> Item -> (DeclaredVars, Item)
    getDeclared decl item = case item of
      NoInit ma' (Ident id) -> (DS.insert id decl, item)
      Init ma' (Ident id) ex -> (decl', Init ma' (Ident id) (g decl ex))
        where
          decl' = DS.insert id decl

preprocessMembers :: [Lt.ClassMemberDef] -> ([ClassMemberDef], [ClassMethodDef])
preprocessMembers members =  (f members, g members)
  where
    f :: [Lt.ClassMemberDef] -> [ClassMemberDef]
    f x = reverse $ foldl f' [] x
      where
        f' :: [ClassMemberDef] -> Lt.ClassMemberDef -> [ClassMemberDef]
        f' res = \case
          Lt.FieldDecl ma ty fdis -> FieldDecl ma ty fdis:res
          Lt.MemthodDecl {} -> res
    g :: [Lt.ClassMemberDef] -> [ClassMethodDef]
    g x = reverse $ foldl g' [] x
      where
        g' :: [ClassMethodDef] -> Lt.ClassMemberDef -> [ClassMethodDef]
        g' res = \case
          Lt.FieldDecl ma ty fdis -> res
          Lt.MemthodDecl ma ty name args block -> MethodDecl ma ty name args block' : res
            where
              initiallyDeclared = DS.fromList $ "this":map getIdStr args
              (BStmt a block', _, _) = stmtToEnrichedStmt
                (Lt.BStmt a (addThisEverywhere initiallyDeclared block)) (mlbEmpty 0) dlEmpty

preprocessProgram :: Lt.Program -> Program
preprocessProgram (Lt.Program a topdefs) = Program a topdefs' classdefs
  where
    topdefs' = mapMaybe f topdefs
    classdefs = DL.sortOn classToString $ mapMaybe f' topdefs
    classToString :: ClassDef -> String
    classToString = \case
      ClassDef ma (Ident id) cmds _-> "00_" ++ id
      ClassDefExtends ma (Ident id) (Ident id') cmds _ -> "01_" ++ id' ++ "_" ++ "id"
    f' :: Lt.TopDef -> Maybe ClassDef
    f' (Lt.ClassDef a id members) = Just $ uncurry (ClassDef a id)
      (preprocessMembers members)
    f' (Lt.ClassDefExtends a id id2 members) = Just $ uncurry (ClassDefExtends a id id2)
      (preprocessMembers members)
    f' _ = Nothing
    f :: Lt.TopDef -> Maybe TopDef
    f (Lt.FnDef a _type id args block) = Just $ FnDef a _type id args (g block)
    f Lt.ClassDef{} = Nothing
    f Lt.ClassDefExtends {} = Nothing
    g :: Lt.Block  -> Block
    g block@(Lt.Block a _) = block'
      where
        (BStmt a block', _, _) = stmtToEnrichedStmt (Lt.BStmt a block) (mlbEmpty 0) dlEmpty

stmtToEnrichedStmt :: Lt.Stmt -> ModifiedLvaluesBuilder ->
                      DeclaredLvalues -> (Stmt, ModifiedLvaluesBuilder, DeclaredLvalues)
stmtToEnrichedStmt stmt md rd = case stmt of
  Lt.Empty a -> (Empty a, md, rd)
  Lt.Ass a lvalue rest -> let md' =
                                let
                                  ulv = lvalueToUnified lvalue
                                  in
                                  if dlContains ulv rd then md else mlbInsertUnified (ulv, lvalue) md
                          in
                            (Ass a lvalue rest, md', rd)
  Lt.Incr a lvalue -> let md' = let
                            ulv = lvalueToUnified lvalue
                            in
                              if dlContains ulv rd then md else mlbInsertUnified (ulv, lvalue) md
                      in
                        (Incr a lvalue, md', rd)
  Lt.Decr a lvalue -> let md' =
                            let ulv = lvalueToUnified lvalue
                             in if dlContains ulv rd then md else mlbInsertUnified (ulv, lvalue) md
                          in
                        (Decr a lvalue, md', rd)
  Lt.Decl a dtype items -> (Decl a dtype items, md', rd')
    where
    (rd', md') = itemListToRedeclared items md rd
    itemListToRedeclared :: [Item] -> ModifiedLvaluesBuilder ->DeclaredLvalues
      -> (DeclaredLvalues, ModifiedLvaluesBuilder)
    itemListToRedeclared list mlb dl = foldl f (dl, mlb) list
      where
        f :: (DeclaredLvalues,ModifiedLvaluesBuilder) -> Item -> (DeclaredLvalues,ModifiedLvaluesBuilder)
        f (dl, md) (NoInit pos (Ident x)) = (dlInsert (lvalueToUnified (LVar pos (Ident x))) dl, md)
        f (dl, md) (Init pos (Ident x) expr) = let
          dl' = dlInsert (lvalueToUnified (LVar pos (Ident x))) dl
          in
            (dl', exprGetModifiedVars False expr md dl)
  Lt.SExp a expr -> (SExp a expr, md', rd)
    where
    md' = exprGetModifiedVars False expr md rd
  Lt.BStmt a block -> (BStmt a newBlock, modified, rd)
    where
      (Lt.Block b stmts) = block
      f :: [Lt.Stmt]  -> ([EnrichedStmt' BNFC'Position], ModifiedLvaluesBuilder, DeclaredLvalues)
      f list = foldl
        (\(list, md, rd) stmt ->
           let
             (stmt', md', rd') = stmtToEnrichedStmt stmt md rd
           in
             (stmt':list, md', rd))
        ([], md , rd)
        list
      (stmts', modified, _) = f stmts
      newBlock = Block b (reverse stmts')
  Lt.VRet a -> (VRet a, md, rd)
  Lt.Ret a expr -> (Ret a expr, md', rd)
    where
      md' = exprGetModifiedVars False expr md rd
  Lt.Cond a expr stmt -> (Cond a expr stmt' (result md'), newmd, rd)
    where
      _md = exprGetModifiedVars False expr md rd
      (stmt', md', rd') = stmtToEnrichedStmt stmt (mlbEmpty (mlbNextIndex _md)) dlEmpty
      newmd = mlbUnion _md md'
  Lt.CondElse a expr stmt1 stmt2 -> (CondElse a expr stmt1' stmt2' (result md'''), newmd, rd)
    where
      _md = exprGetModifiedVars False expr md rd
      (stmt1', md', rd') = stmtToEnrichedStmt stmt1 (mlbEmpty $ mlbNextIndex _md) dlEmpty
      (stmt2', md'', rd'') = stmtToEnrichedStmt stmt2 (mlbEmpty $ mlbNextIndex _md) dlEmpty
      md'''= mlbUnion md' md''
      newmd = mlbUnion _md md'''
  Lt.While a expr stmt -> (While a expr stmt' (result md''), newmd, rd)
    where
      md' = exprGetModifiedVars False expr (mlbEmpty $ mlbNextIndex md) rd
      (stmt', md'', rd') = stmtToEnrichedStmt stmt md' dlEmpty
      newmd = mlbUnion md md''
  where
    exprGetModifiedVars :: Bool -> Lt.Expr -> ModifiedLvaluesBuilder -> DeclaredLvalues -> ModifiedLvaluesBuilder
    exprGetModifiedVars funArg expr mlb decl= case expr of
      EVar ma lv -> if funArg then
        let ulv=lvalueToUnified lv
        in
          if dlContains ulv decl then mlb
          else mlbInsertUnifiedRec (ulv, lv) mlb
        else mlb
      ELitInt ma n -> mlb
      ELitTrue ma -> mlb
      ELitFalse ma -> mlb
      ENull ma -> mlb
      EApp ma id exs -> foldl (\mlb expr -> exprGetModifiedVars True expr mlb decl) mlb exs
      EMethod ma lv id exs -> foldl (\mlb expr -> exprGetModifiedVars True expr mlb decl) mlb (EVar ma lv:exs)
      EString ma s -> mlb
      ENewArray ma ty ex -> mlb
      ENewClass ma ty -> mlb
      Neg ma ex -> mlb
      Not ma ex -> mlb
      EMul ma ex mo ex' -> mlb
      EAdd ma ex ao ex' -> mlb
      ERel ma ex ro ex' -> mlb
      EAnd ma ex ex' -> mlb
      EOr ma ex ex' -> mlb
      EInternalCast ma ty ex -> mlb
      ECast ma _ _ -> mlb
convertType :: Type -> LType
convertType (Int _) = LInt
convertType (Str _) = LString
convertType (Bool _) = LBool
convertType (Void _) = LVoid
convertType (Fun _ x y) = LFun (convertType x) $ map convertType y
convertType (Lt.Class _ (Ident id)) = LClass id

getArgLType :: Arg -> LType
getArgLType (Arg _ aType _) = convertType aType

topDefArgs :: TopDef -> [Arg]
topDefArgs (FnDef _ _ _ args _) = args
topDefBlock :: TopDef -> Block
topDefBlock (FnDef _ _ _ _ block) = block
topDefReturnType :: TopDef -> Type
topDefReturnType (FnDef _ t _ _ _) = t

instance HasPosition TopDef where
  hasPosition = \case
    FnDef p _ _ _ _ -> p

instance HasPosition Block where
  hasPosition = \case
    Block p _ -> p

instance HasPosition Stmt where
  hasPosition = \case
    Empty p -> p
    BStmt p _ -> p
    Decl p _ _ -> p
    Ass p _ _ -> p
    Incr p _ -> p
    Decr p _ -> p
    Ret p _ -> p
    VRet p -> p
    Cond p _ _ _ -> p
    CondElse p _ _ _ _ -> p
    While p _ _ _ -> p
    SExp p _ -> p

instance HasPosition ClassDef where
  hasPosition = \case
    ClassDef ma id cmds _ -> ma
    ClassDefExtends ma id id' cmds _ -> ma


class Indexed a where
  getId :: a -> Ident
  getIdStr :: a -> String
  getIdStr x = id
    where (Ident id) = getId x

instance Indexed Arg where
  getId (Arg _ _ id) = id

instance Indexed Lt.TopDef where
  getId (Lt.FnDef _ _ id _ _ ) = id
  getId x = case x of
    Lt.FnDef _ _ id _ _ -> id
    Lt.ClassDef _ id _ -> id
    Lt.ClassDefExtends _ id _ _ -> id

instance Indexed (EnrichedClassDef' a) where
    getId = \case
      ClassDef a id cmds _ -> id
      ClassDefExtends a id id' cmds _ -> id

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
  showsPrec x (LClass string) = showString string

