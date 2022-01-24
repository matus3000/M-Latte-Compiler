
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
                    Indexed(..),
                    getPosition,
                    TypeClass(..),
                    HasPosition(..),
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
      Expr'(..), LValue' (LVarMem, LVar, LVarArr), ClassMemberDef')
import qualified Latte.Abs as Lt
import Data.Maybe (fromMaybe, isJust, fromJust, catMaybes)
import Data.Maybe (mapMaybe)
import Data.Ord
import qualified Control.Arrow as Data.BiFunctor
import qualified Data.Bifunctor

data LType = LInt | LString | LBool | LVoid | LFun LType [LType] | LArray LType | LClass String |
  LGenericClass String [LType]
  deriving Eq

-- data VarType = StaticInt Int | DynamicInt | StaticBool Bool | DynamicBool |
--               StaticString String | DynamicString

type UnifiedLValue = (String, LValue)
type ModifiedLValues = [LValue]
data ModifiedLvaluesBuilder = MLB (DM.Map UnifiedLValue LValue)
type DeclaredLvalues = (DS.Set LValue, DS.Set String)

lvalueToUnified :: LValue -> UnifiedLValue
lvalueToUnified  = pruneLValue
  where
    pruneLValue :: LValue -> (String, LValue)
    pruneLValue = \case
      LVar ma id@(Ident name) -> (name, LVar Nothing id)
      LVarMem ma lv id -> Data.BiFunctor.second (\x -> LVarMem Nothing x id)(pruneLValue lv)
      LVarArr ma lv ex -> undefined

result :: ModifiedLvaluesBuilder -> [LValue]
result mlb@(MLB map)= DM.elems map

mlbInsert :: LValue -> ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder
mlbInsert lvalue = mlbInsertUnified (lvalueToUnified lvalue, lvalue)

mlbInsertUnified :: (UnifiedLValue, LValue) -> ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder
mlbInsertUnified (unified, lvalue) original@(MLB x) =
  if DM.member unified x then original else MLB (DM.insert unified lvalue x)

mlbUnion :: ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder -> ModifiedLvaluesBuilder
mlbUnion mlb@(MLB map) mlb'@(MLB map') = MLB $ DM.union map map'

mlbEmpty :: ModifiedLvaluesBuilder
mlbEmpty = MLB DM.empty

dlContains :: UnifiedLValue -> DeclaredLvalues -> Bool
dlContains ul dl = DS.member (fst ul) (snd dl) || DS.member (snd ul) (fst dl)
dlInsert ::  UnifiedLValue -> DeclaredLvalues -> DeclaredLvalues
dlInsert ul = Data.Bifunctor.bimap (DS.insert (snd ul)) (DS.insert (fst ul))
dlUnion :: DeclaredLvalues -> DeclaredLvalues -> DeclaredLvalues
dlUnion ul1@(s1, s2) ul2@(s1', s2') = (DS.union s1 s1', DS.union s2 s2')
dlEmpty :: DeclaredLvalues
dlEmpty = (DS.empty , DS.empty)
type Program = EnrichedProgram' BNFC'Position
data EnrichedProgram' a = Program a [EnrichedTopDef' a] [EnrichedClassDef' a]

type TopDef = EnrichedTopDef' BNFC'Position
data EnrichedTopDef' a = FnDef a (Type' a) Ident [Arg' a] (EnrichedBlock' a)

type ClassDef = EnrichedClassDef' BNFC'Position
data EnrichedClassDef' a = ClassDef a Ident [ClassMemberDef' a] |
  ClassDefExtends a Ident Ident [ClassMemberDef' a]

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


preprocessProgram :: Lt.Program -> Program
preprocessProgram (Lt.Program a topdefs) = Program a topdefs' classdefs
  where
    topdefs' = mapMaybe f topdefs
    classdefs = mapMaybe f' topdefs
    f' :: Lt.TopDef -> Maybe ClassDef
    f' (Lt.ClassDef a id members) = Just $ ClassDef a id members
    f' (Lt.ClassDefExtends a id id2 members) = Just $ ClassDefExtends a id id2 members
    f' _ = Nothing
    f :: Lt.TopDef -> Maybe TopDef
    f (Lt.FnDef a _type id args block) = Just $ FnDef a _type id args (g block)
    f Lt.ClassDef{} = Nothing
    f Lt.ClassDefExtends {} = Nothing
    g :: Lt.Block  -> Block
    g block@(Lt.Block a _) = block'
      where
        (BStmt a block', _, _) = stmtToEnrichedStmt (Lt.BStmt a block) mlbEmpty dlEmpty

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
  Lt.Decl a dtype items -> (Decl a dtype items, md, itemListToRedeclared items rd)
    where
    itemListToRedeclared :: [Item] -> DeclaredLvalues -> DeclaredLvalues
    itemListToRedeclared list set = foldl f set list
      where
        f :: DeclaredLvalues -> Item -> DeclaredLvalues
        f set (NoInit pos (Ident x)) = dlInsert (lvalueToUnified (LVar pos (Ident x))) set
        f set (Init pos (Ident x) _) = dlInsert (lvalueToUnified (LVar pos (Ident x))) set
  Lt.SExp a expr -> (SExp a expr, md, rd)
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
  Lt.Ret a expr -> (Ret a expr, md, rd)
  Lt.Cond a expr stmt -> (Cond a expr stmt' (result md'), newmd, newrd)
    where
      (stmt', md', rd') = stmtToEnrichedStmt stmt mlbEmpty dlEmpty
      newmd = mlbUnion md md'
      newrd = dlUnion rd rd' 
  Lt.CondElse a expr stmt1 stmt2 -> (CondElse a expr stmt1' stmt2' (result md'''), newmd, newrd)
    where
      (stmt1', md', rd') = stmtToEnrichedStmt stmt1 mlbEmpty dlEmpty
      (stmt2', md'', rd'') = stmtToEnrichedStmt stmt2 mlbEmpty dlEmpty
      md'''= mlbUnion md' md''
      newmd = mlbUnion md md'''
      newrd = dlUnion rd $ dlUnion rd' rd''
  Lt.While a expr stmt -> (While a expr stmt' (result md'), newmd, newrd)
    where
      (stmt', md', rd') = stmtToEnrichedStmt stmt mlbEmpty dlEmpty
      newmd = mlbUnion md md'
      newrd = dlUnion rd' rd

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
    ClassDef ma id cmds -> ma
    ClassDefExtends ma id id' cmds -> ma


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
      ClassDef a id cmds -> id
      ClassDefExtends a id id' cmds -> id

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
