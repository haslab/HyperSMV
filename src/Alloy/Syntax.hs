{-# LANGUAGE ViewPatterns #-}

module Alloy.Syntax where

import Data.Set (Set(..))
import qualified Data.Set as Set
import GHC.Generics
import Data.Hashable

import Utils

data Alloy = Alloy { imports :: [Import], items :: [Item] }
  deriving (Eq,Ord,Show)

data Import = Import String (Maybe String) deriving (Eq,Ord,Show)

data Item
    = ItemPred Pred
    | ItemFun Fun
    | ItemFact Fact
    | ItemComment String
    | ItemSig Sig
    deriving (Eq,Ord,Show)

data Sig
    = EnumSig SigName [String]
    | StructSig IsAbstract IsTrace (Maybe Multiplicity) SigNames Extends [Field]
    | DefSig SigName Expr
  deriving (Eq,Ord,Show)

type SigName = String
type SigNames = [SigName]
type Extends = Maybe String

type IsAbstract = Bool

type IsTrace = Bool

type IsVar = Bool
  
data Field
    = Field IsVar String (Maybe Multiplicity) Relation
  deriving (Eq,Ord,Show)
    
data Relation = Relation [(Expr,Maybe Multiplicity)] deriving (Eq,Ord,Show)
  
data Multiplicity = MOne | MSome | MSet | MLone deriving (Eq,Ord,Show)

data Fact = Fact Expr deriving (Eq,Ord,Show)

data Pred = Pred String [(String,Relation)] [Expr] deriving (Eq,Ord,Show)

data Fun = Fun String [(String,Relation)] Relation Expr deriving (Eq,Ord,Show)

data Op1 = OpAlways | OpEventually | OpNo | OpSome | OpNot
  deriving (Eq,Ord,Show,Generic)

instance Hashable Op1

data Op2 = OpUnion | OpOr | OpAnd | OpIff | OpImplies | OpIn | OpComp | OpEq | OpArrow
    deriving (Eq,Ord,Show,Generic)
    
instance Hashable Op2

isCommutative :: Op2 -> Bool
isCommutative OpOr = True
isCommutative OpUnion = True
isCommutative OpAnd = True
isCommutative OpComp = True
isCommutative OpArrow = True
isCommutative _ = False

data Expr
    = Expr1 Op1 Expr
    | Expr2 Expr Op2 Expr
    | ExprBool Bool
    | NextExpr String
    | VarExpr String
    | ExprNone -- empty relation
    | ApplyExpr Expr [Expr]
  deriving (Eq,Ord,Show,Generic)
  
instance Hashable Expr
  
--itemName :: Item -> String
--itemName (ItemPred p) = predName p
--itemName (ItemFun f) = funName f
--itemName (ItemSig s) = sigName s

predName :: Pred -> String
predName (Pred n _ _) = n

funName :: Fun -> String
funName (Fun n _ _ _) = n

sigNames :: Sig -> [String]
sigNames (EnumSig n _) = [n]
sigNames (StructSig _ _ _ ns _ _) = ns
sigNames (DefSig n _) = [n]

simpleRelation :: String -> Relation
simpleRelation n = Relation [(VarExpr n,Nothing)]

ands :: [Expr] -> Expr
ands [] = VarExpr "true"
ands [e] = e
ands (e:es) = Expr2 e OpAnd $ ands es

ors :: [Expr] -> Expr
ors [] = VarExpr "true"
ors [e] = e
ors (e:es) = Expr2 e OpOr $ ors es

unions :: [Expr] -> Expr
unions [] = ExprNone
unions [e] = e
unions (e:es) = Expr2 e OpUnion $ unions es

arrows :: [Expr] -> Expr
arrows [] = ExprNone
arrows [e] = e
arrows (e:es) = Expr2 e OpArrow $ arrows es


