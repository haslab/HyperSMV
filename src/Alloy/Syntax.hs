-- | The Alloy-language AST.
module Alloy.Syntax where

import GHC.Generics
import Data.Hashable


-- | A complete Alloy module.
data Alloy = Alloy { imports :: [Import], items :: [Item] }
  deriving (Eq,Ord,Show)

-- | An Alloy import: a module name, plus an optional local alias (\"open X as Y\", needed when a
-- formula spans several distinct models and must disambiguate their same-named predicates).
data Import = Import String (Maybe String) deriving (Eq,Ord,Show)

-- | One top-level item of an Alloy module.
data Item
    = ItemPred Pred
    | ItemFun Fun
    | ItemFact Fact
    | ItemComment String
    | ItemSig Sig
    | ItemCheck String Expr Int Int -- ^ name, body, scope (\"for N steps\"), expect bit
    deriving (Eq,Ord,Show)

-- | An Alloy signature declaration.
data Sig
    = EnumSig SigName [String]
    | StructSig IsAbstract IsTrace (Maybe Multiplicity) SigNames Extends [Field]
    | DefSig SigName Expr
  deriving (Eq,Ord,Show)

-- | A signature's name.
type SigName = String
-- | Signature names declared together.
type SigNames = [SigName]
-- | A signature's optional parent.
type Extends = Maybe String

-- | Whether a signature is abstract.
type IsAbstract = Bool

-- | Whether a signature is a trace.
type IsTrace = Bool

-- | Whether a field is mutable ('var').
type IsVar = Bool
  
-- | One field of a signature.
data Field
    = Field IsVar String (Maybe Multiplicity) Relation
  deriving (Eq,Ord,Show)
    
-- | A relation type as arrow-joined columns.
data Relation = Relation [(Expr,Maybe Multiplicity)] deriving (Eq,Ord,Show)
  
-- | An Alloy multiplicity keyword.
data Multiplicity = MOne | MSome | MSet | MLone deriving (Eq,Ord,Show)

-- | A globally asserted expression.
data Fact = Fact Expr deriving (Eq,Ord,Show)

-- | A predicate declaration.
data Pred = Pred String [(String,Relation)] [Expr] deriving (Eq,Ord,Show)

-- | A function declaration.
data Fun = Fun String [(String,Relation)] Relation Expr deriving (Eq,Ord,Show)

-- | A unary Alloy operator.
data Op1 = OpAlways | OpEventually | OpNo | OpSome | OpNot
  deriving (Eq,Ord,Show,Generic)

instance Hashable Op1

-- | A binary Alloy operator.
data Op2 = OpUnion | OpOr | OpAnd | OpIff | OpImplies | OpIn | OpComp | OpEq | OpArrow | OpUntil
    deriving (Eq,Ord,Show,Generic)

instance Hashable Op2

-- | A trace-quantifier kind.
data Quant = QSome | QAll deriving (Eq,Ord,Show,Generic)

instance Hashable Quant

-- | Whether an operator's operands may be reassociated.
isCommutative :: Op2 -> Bool
isCommutative OpOr = True
isCommutative OpUnion = True
isCommutative OpAnd = True
isCommutative OpComp = True
isCommutative OpArrow = True
isCommutative _ = False

-- | An Alloy expression.
data Expr
    = Expr1 Op1 Expr
    | Expr2 Expr Op2 Expr
    | ExprBool Bool
    | NextExpr String
    | VarExpr String
    | ExprNone -- empty relation
    | ApplyExpr Expr [Expr]
    | QuantExpr Quant String String Expr -- ^ some/all <var>:<sig> | <body>
  deriving (Eq,Ord,Show,Generic)
  
instance Hashable Expr

-- | A predicate's name.
predName :: Pred -> String
predName (Pred n _ _) = n

-- | A function's name.
funName :: Fun -> String
funName (Fun n _ _ _) = n

-- | The name(s) declared by a signature.
sigNames :: Sig -> [String]
sigNames (EnumSig n _) = [n]
sigNames (StructSig _ _ _ ns _ _) = ns
sigNames (DefSig n _) = [n]

-- | A one-column relation naming a signature.
simpleRelation :: String -> Relation
simpleRelation n = Relation [(VarExpr n,Nothing)]

-- | Conjoin a list of expressions.
ands :: [Expr] -> Expr
ands [] = VarExpr "true"
ands [e] = e
ands (e:es) = Expr2 e OpAnd $ ands es

-- | Disjoin a list of expressions.
ors :: [Expr] -> Expr
ors [] = VarExpr "true"
ors [e] = e
ors (e:es) = Expr2 e OpOr $ ors es

-- | Union a list of expressions.
unions :: [Expr] -> Expr
unions [] = ExprNone
unions [e] = e
unions (e:es) = Expr2 e OpUnion $ unions es

-- | Combine expressions into an arrow product.
arrows :: [Expr] -> Expr
arrows [] = ExprNone
arrows [e] = e
arrows (e:es) = Expr2 e OpArrow $ arrows es


