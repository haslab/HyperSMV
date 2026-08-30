-- | The core SMV and HyperLTL abstract syntax.
module Smv.Syntax where

import Control.Monad
import Data.List as List
import Data.Hashable
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import GHC.Generics

import Utils
import Location as L

-- an hyperLTL formula
data Pformula
    = Pfexists String Pformula
    | Pfforall String Pformula
    | Pfltl Pexpr
    deriving (Eq,Ord,Show)

-- | An SMV module: name plus items.
data Pmodule = Pmodule { p_name :: String, p_items :: [Located Pitem] }
    deriving (Eq,Ord,Show)

-- | A variable or definition identifier.
data Pident = Pident String Pdims deriving (Eq,Ord,Show)

-- | A 'Pident' with a next-state flag.
type DualPident = (Pident,Bool) -- for next variables

-- | Whether a VAR is a FROZENVAR.
type IsFrozen = Bool

-- | A single SMV module item.
data Pitem
    = Pivar [Located Pvar] IsFrozen
    | Pijustice Pexpr
    | Pidefine [Located Pdefine]
    | Piinit Pexpr
    | Piinvar Pexpr
    | Pitrans Pexpr
    | Piltlspec Pexpr
    | Piassign [Located Passign]
    deriving (Eq,Ord,Show)

-- | An SMV variable type.
data Ptype
    = Pboolean
    | Pint Int Int
    | Penum IntSet
    | Parray Int Int Ptype
    deriving (Eq,Ord,Show)

-- | A declared variable: name and type.
data Pvar = Pvar { pvar_name :: Pident, pvar_type :: Ptype }
    deriving (Eq,Ord,Show)

-- | A DEFINE entry: name bound to an expression.
data Pdefine = Pdefine { pdef_lhs :: String, pdef_rhs :: Pexpr }
    deriving (Eq,Ord,Show)

-- | The n-ary operators: AND, OR, set.
data Popn = Pand | Por | Pset deriving (Eq,Ord,Show,Generic)
-- | The unary operators.
data Pop1 = Pnot | Pf | Pg | Px | Py | Pz | Ph | Pnext | Patom {-used only for autohyper formulas-} deriving (Eq,Ord,Show,Generic)
-- | The binary operators.
data Pop2 = Pin | Pequiv | Pimplies | Pplus | Pminus | Ptimes | Punion | Peq | Pneq | Plt | Pleq | Pgt | Pgeq | Pu | Pv deriving (Eq,Ord,Show,Generic)

instance Hashable Pop1
instance Hashable Pop2
instance Hashable Popn

-- | Whether a unary operator is temporal.
isLTLOp1 :: Pop1 -> Bool
isLTLOp1 Pf = True
isLTLOp1 Pg = True
isLTLOp1 Px = True
isLTLOp1 Py = True
isLTLOp1 Pz = True
isLTLOp1 Ph = True
isLTLOp1 _ = False

-- | Whether a binary operator is temporal.
isLTLOp2 :: Pop2 -> Bool
isLTLOp2 Pu = True
isLTLOp2 Pv = True
isLTLOp2 _ = False

-- | Array dimension subscripts.
type Pdims = [Pexpr]

-- | The SMV and HyperLTL expression language.
data Pexpr
    = Peident Pident ExprType
    | Pebool Bool
    | Peint Int
    | Peop1 Pop1 Pexpr
    | Peop2 Pop2 Pexpr Pexpr
    | Peopn Popn [Pexpr]
--    | Peproj Pident [Pexpr] ExprType
    | Pecase [(Pexpr,Pexpr)]
    | Pedemorgan Pexpr Pexpr Pexpr
    deriving (Eq,Ord,Show,Generic)

instance Hashable Pexpr

-- | An ASSIGN clause.
data Passign = Passign Passign_lhs Pexpr deriving (Eq,Ord,Show,Generic)

-- | An ASSIGN left-hand side: init or next.
data Passign_lhs
    = Painit Pident
    | Panext Pident
    deriving (Eq,Ord,Show,Generic)
    
-- | Extract the identifier of an init assignment.
isLhsInit :: Passign_lhs -> Maybe Pident
isLhsInit (Painit n) = Just n
isLhsInit (Panext n) = Nothing

-- | Extract the identifier of a next assignment.
isLhsNext :: Passign_lhs -> Maybe Pident
isLhsNext (Panext n) = Just n
isLhsNext (Painit n) = Nothing
    
-- | Count a formula's leading quantifiers.
numQuantifiers :: Pformula -> Int
numQuantifiers (Pfforall _ f) = numQuantifiers f + 1
numQuantifiers (Pfexists _ f) = numQuantifiers f + 1
numQuantifiers (Pfltl _) = 0
    
-- | Smart constructor for implication.
pimplies :: Pexpr -> Pexpr -> Pexpr
pimplies e1 e2
    | e1 == ptrue = e2
    | e1 == pfalse = ptrue
    | e2 == ptrue = ptrue
    | e2 == pfalse = pnot e1
    | otherwise = Peop2 Pimplies e1 e2
    
-- | Smart constructor for negation.
pnot :: Pexpr -> Pexpr
pnot (Pebool b) = Pebool (not b)
pnot e = Peop1 Pnot e
    
-- | The literal TRUE.
ptrue :: Pexpr
ptrue = Pebool True

-- | The literal FALSE.
pfalse :: Pexpr
pfalse = Pebool False

-- | Conjoin two optional expressions.
pandMaybe :: Maybe Pexpr -> Maybe Pexpr -> Maybe Pexpr
pandMaybe Nothing r = r
pandMaybe l Nothing = l
pandMaybe (Just l) (Just r) = Just $ pand l r

-- | Smart constructor for conjunction.
pand :: Pexpr -> Pexpr -> Pexpr
pand e1 e2 = pands [e1,e2]
    
-- | Conjoin a list of expressions, or Nothing if trivial.
pandsMaybe :: [Pexpr] -> Maybe Pexpr
pandsMaybe es = let es' = pands es in if es' == Pebool True then Nothing else Just es'

-- | Smart constructor for n-ary conjunction.
pands :: [Pexpr] -> Pexpr
pands = pands' []

-- | Worker for 'pands'.
pands' :: [Pexpr] -> [Pexpr] -> Pexpr
pands' [] [] = Pebool True
pands' [y] [] = y
pands' acc [] = Peopn Pand acc
pands' acc ((vands -> Just es1) : es2) = pands' acc (es1 ++ es2)
pands' acc (e@(vands -> Nothing) : es) = case e of
    ((==ptrue) -> True) -> pands' acc es
    ((==pfalse) -> True) -> pfalse
    otherwise -> pands' (e : acc) es

-- | Disjoin two optional expressions.
porMaybe :: Maybe Pexpr -> Maybe Pexpr -> Maybe Pexpr
porMaybe Nothing r = r
porMaybe l Nothing = l
porMaybe (Just l) (Just r) = Just $ por l r

-- | Smart constructor for disjunction.
por :: Pexpr -> Pexpr -> Pexpr
por e1 e2 = pors [e1,e2]

-- | Disjoin a list of expressions, or Nothing if trivial.
porsMaybe :: [Pexpr] -> Maybe Pexpr
porsMaybe es = let es' = pors es in if es' == Pebool False then Nothing else Just es'

-- | Smart constructor for n-ary disjunction.
pors :: [Pexpr] -> Pexpr
pors = pors' []

-- | Worker for 'pors'.
pors' :: [Pexpr] -> [Pexpr] -> Pexpr
pors' [] [] = Pebool False
pors' [y] [] = y
pors' acc [] = Peopn Por acc
pors' acc ((vors -> Just es1) : es2) = pors' acc (es1 ++ es2)
pors' acc (e@(vors -> Nothing) : es) = case e of
    ((==pfalse) -> True) -> pors' acc es
    ((==ptrue) -> True) -> ptrue
    otherwise -> pors' (e : acc) es
    
-- | Dispatch to the n-ary smart constructor for a 'Popn'.
peopn :: Popn -> [Pexpr] -> Pexpr
peopn Pand = pands
peopn Por = pors
peopn Pset = pset
    
-- | Build an INIT item from conjuncts.
piinit :: [Pexpr] -> Maybe Pitem
piinit [] = Nothing
piinit es = Just $ Piinit $ pands es

-- | Build an INVAR item from conjuncts.
piinvar :: [Pexpr] -> Maybe Pitem
piinvar [] = Nothing
piinvar es = Just $ Piinvar $ pands es

-- | Build a TRANS item from conjuncts.
pitrans :: [Pexpr] -> Maybe Pitem
pitrans [] = Nothing
pitrans es = Just $ Pitrans $ pands es
    
-- | Build a VAR item.
pivar :: [L.Located (Pident,Ptype)] -> Bool -> Pitem
pivar xs isFrozen = Pivar (map pvar xs) isFrozen
    where pvar l = let (x,y) = unloc l in mk_loc (loc l) (Pvar x y)
    
-- | Build a JUSTICE item.
pijustice :: L.Located Pexpr -> Pitem
pijustice e = Pijustice (unloc e)
    
-- | Build a DEFINE item.
pidefine :: [L.Located (String,Pexpr)] -> Pitem
pidefine xs = Pidefine (map pdefine xs)
    where pdefine l = let (x,y) = unloc l in mk_loc (loc l) (Pdefine x y)
    
-- | Merge two n-ary applications of the same operator.
peopn2 :: Popn -> Pexpr -> Pexpr -> Pexpr
peopn2 o (Peopn o1 es1) (Peopn o2 es2) | o == o1 && o == o2 = Peopn o (es1 ++ es2)
peopn2 o (Peopn o1 es1) e2 | o == o1 = Peopn o (e2 : es1)
peopn2 o e1 (Peopn o2 es2) | o == o2 = Peopn o (e1 : es2)
peopn2 o e1 e2 = Peopn o [e1,e2]

-- | View an expression as a variable reference.
vvar :: Pexpr -> Maybe DualPident
vvar (Peident n t) = Just (n,False)
vvar (Peop1 Pnext (Peident n t)) = Just (n,True)
vvar e = Nothing

-- | Build a variable reference expression.
pvar :: DualPident -> ExprType -> Pexpr
pvar (n,False) t = Peident n t
pvar (n,True) t = pnext $ Peident n t

-- | View an expression as a negation.
vnot :: Pexpr -> Maybe Pexpr
vnot (Peop1 Pnot e) = Just e
vnot _ = Nothing

-- | View an expression as a disjunction.
vors :: Pexpr -> Maybe [Pexpr]
vors (Peopn Por es) = Just es
vors _ = Nothing

-- | View an expression's disjuncts, singleton otherwise.
vors' :: Pexpr -> [Pexpr]
vors' (Peopn Por es) = es
vors' e = [e]

-- | View an expression as a conjunction.
vands :: Pexpr -> Maybe [Pexpr]
vands (Peopn Pand es) = Just es
vands _ = Nothing

-- | View an expression's conjuncts, singleton otherwise.
vands' :: Pexpr -> [Pexpr]
vands' (Peopn Pand es) = es
vands' e = [e]
    
-- | View an expression as a double negation.
vnotnot :: Pexpr -> Maybe Pexpr
vnotnot = vnot >=> vnot

-- | View an expression as a negated disjunction.
vnotors :: Pexpr -> Maybe [Pexpr]
vnotors = vnot >=> vors

-- | View an expression as a negated conjunction.
vnotands :: Pexpr -> Maybe [Pexpr]
vnotands = vnot >=> vands

-- | View an expression as guard/branch pairs.
vcase :: Pexpr -> Maybe [(Pexpr,Pexpr)]
vcase (Pecase cs) = Just cs
vcase (Pedemorgan c te fe) = Just [(c,te),(pnot c,fe)]
vcase e = Nothing

-- | View an expression as a next application.
vnext :: Pexpr -> Maybe Pexpr
vnext (Peop1 Pnext e) = Just e
vnext _ = Nothing

-- | Smart constructor for next.
pnext :: Pexpr -> Pexpr
pnext e@(Pebool {}) = e
pnext e@(Peint {}) = e
pnext e = Peop1 Pnext e

-- | Collect all DEFINE entries in a module.
moduleDefines :: Pmodule -> [Located Pdefine]
moduleDefines (Pmodule _ is) = concat $ map itemDefines $ map unloc is

-- | Collect the DEFINE entries of an item.
itemDefines :: Pitem -> [Located Pdefine]
itemDefines (Pidefine ds) = ds
itemDefines _ = []

-- | Whether an item is a VAR block.
isPivar :: Pitem -> Bool
isPivar (Pivar {}) = True
isPivar _ = False

-- | Whether an item is a DEFINE block.
isPidefine :: Pitem -> Bool
isPidefine (Pidefine _) = True
isPidefine _ = False

-- | The name bound by a DEFINE entry.
pdefineName :: Pdefine -> String
pdefineName (Pdefine n _) = n

-- | Collect DEFINE entries from module items.
collectDefines :: [L.Located Pitem] -> [L.Located Pdefine]
collectDefines [] = []
collectDefines (L.Located _ (Pidefine ds):defs) = ds ++ collectDefines defs

-- | Partition assignments into init and next.
splitPassigns :: [L.Located Passign] -> ([L.Located Passign],[L.Located Passign])
splitPassigns [] = ([],[])
splitPassigns (a@(L.unloc -> Passign l r):ps) = case l of
        Painit n -> (a:xs,ys)
        Panext n -> (xs,a:ys)
    where
    (xs,ys) = splitPassigns ps

-- | Smart constructor for equality.
peq :: Pexpr -> Pexpr -> Pexpr
peq e1 e2 = Peop2 Peq e1 e2

-- | Smart constructor for disequality.
pneq :: Pexpr -> Pexpr -> Pexpr
pneq e1 e2 = pnot $ Peop2 Peq e1 e2

-- | Smart constructor for a set literal.
pset :: [Pexpr] -> Pexpr
pset [x] = x
pset xs = Peopn Pset xs

-- | A brace group.
pbraces :: [Pexpr] -> Pexpr
pbraces [x] = Peop1 Patom x
pbraces xs  = pset xs

-- | The set literal {FALSE,TRUE}.
pbools :: Pexpr
pbools = pset [Pebool False,Pebool True]

-- | Smart constructor for F/G, with constant-folding.
peop1 :: Pop1 -> Pexpr -> Pexpr
peop1 Pf (Pebool b) = Pebool b
peop1 Pg (Pebool b) = Pebool b
peop1 o e1 = Peop1 o e1

-- | Smart constructor for binary operators.
peop2 :: Pop2 -> Pexpr -> Pexpr -> Pexpr
peop2 Pu e1 (Pebool b) = Pebool b
peop2 Pv e1 (Pebool b) = Pebool b
peop2 Pplus e1 e2 = pplus e1 e2
peop2 Pin e1 e2 = pin e1 e2
peop2 o e1 e2 = Peop2 o e1 e2

-- | Whether an operator is a comparison.
isCmpOp2 :: Pop2 -> Bool
isCmpOp2 Peq = True
isCmpOp2 Pneq = True
isCmpOp2 Plt = True
isCmpOp2 Pleq = True
isCmpOp2 Pgt = True
isCmpOp2 Pgeq = True
isCmpOp2 o = False

-- | The integer-arithmetic binary operators.
isArithOp2 :: Pop2 -> Bool
isArithOp2 Pplus = True
isArithOp2 Pminus = True
isArithOp2 Ptimes = True
isArithOp2 _ = False

-- | Whether an operator is a boolean connective.
isBoolOp2 :: Pop2 -> Bool
isBoolOp2 Pequiv = True
isBoolOp2 Pimplies = True
isBoolOp2 _ = False

-- | Negate a comparison operator.
negCmpOp2 :: Pop2 -> Pop2
negCmpOp2 Peq = Pneq
negCmpOp2 Pneq = Peq
negCmpOp2 Plt = Pgeq
negCmpOp2 Pleq = Pgt
negCmpOp2 Pgt = Pleq
negCmpOp2 Pgeq = Plt
negCmpOp2 o = error $ "negCmpOp2: " ++ show o

-- | Invert a comparison operator's operand order.
invCmpOp2 :: Pop2 -> Pop2
invCmpOp2 Peq = Peq
invCmpOp2 Pneq = Pneq
invCmpOp2 Plt = Pgt
invCmpOp2 Pleq = Pgeq
invCmpOp2 Pgt = Plt
invCmpOp2 Pgeq = Pleq
invCmpOp2 o = error $ "invCmpOp2: " ++ show o

-- | Whether an n-ary operator is a boolean connective.
isBoolOpn :: Popn -> Bool
isBoolOpn Pset = False
isBoolOpn Pand = True
isBoolOpn Por = True

-- | Smart constructor for addition.
pplus :: Pexpr -> Pexpr -> Pexpr
pplus (Peint i) (Peint j) = Peint (i+j)
pplus e1 e2 = Peop2 Pplus e1 e2

-- | Smart constructor for set membership.
pin :: Pexpr -> Pexpr -> Pexpr
pin e1 e2@(vset -> Just is) = if List.null is then Pebool False else Peop2 Pin e1 e2
pin e1 e2@(Pebool {}) = peop2 Peq e1 e2
pin e1 e2@(Peint {}) = peop2 Peq e1 e2
pin e1 e2 = Peop2 Pin e1 e2

-- | View an expression as a flattened set.
vset :: Pexpr -> Maybe [Pexpr]
vset = vset' False
    where
    vset' b (Peopn Pset es) = liftM concat $ mapM (vset' True) es
    vset' b (Peop2 Punion e1 e2) = do
        is1 <- vset' True e1
        is2 <- vset' True e2
        return $ is1 ++ is2
    vset' False e = Nothing
    vset' True e = Just [e]

-- | View an expression as a set of integers.
vsetint :: Pexpr -> Maybe IntSet
vsetint (Peint i) = Just $ IntSet.singleton i
vsetint (Peopn Pset es) = liftM unionsIntSet $ mapHashSetM vsetint $ HashSet.fromList es
vsetint (Peop2 Punion e1 e2) = do
    is1 <- vsetint e1
    is2 <- vsetint e2
    return $ IntSet.union is1 is2
vsetint e = Nothing

-- | View an expression as a set of booleans.
vsetbool :: Pexpr -> Maybe (HashSet Bool)
vsetbool (Pebool b) = Just $ HashSet.singleton b
vsetbool (Peopn Pset es) = liftM unionsHashSet $ mapHashSetM vsetbool $ HashSet.fromList es
vsetbool (Peop2 Punion e1 e2) = do
    is1 <- vsetbool e1
    is2 <- vsetbool e2
    return $ HashSet.union is1 is2
vsetbool e = Nothing


-- | An identifier's bare name.
pidentName :: Pident -> String
pidentName (Pident n _) = n

instance Hashable Pident where
    hashWithSalt i (Pident x es) = hashWithSalt i x

-- | An expression's type: int, bool, or unknown.
data ExprType = EInt | EBool | EUnknown deriving (Eq,Ord,Show,Generic)

instance Hashable ExprType

-- | Convert a variable type to an expression type.
toExprType :: Ptype -> ExprType
toExprType Pboolean = EBool
toExprType (Pint {}) = EInt
toExprType (Penum {}) = EInt
toExprType (Parray i j t) = toExprType t

-- | Append an array dimension index.
addDimPident :: Pident -> Pexpr -> Pident
addDimPident (Pident n dims) dim = Pident n (dims++[dim])

-- | Drop an identifier's last array dimension.
remDimPident :: Pident -> Pident
remDimPident pn@(Pident n []) = pn
remDimPident (Pident n dims) = Pident n (init dims)

-- | Build a quantifier-dimension identifier expression.
mkQuantDim :: String -> Pexpr
mkQuantDim n = Peident (Pident n []) EUnknown

-- | Build a set literal from an IntSet.
psetint :: IntSet -> Pexpr
psetint (isSingletonIntSet -> Just i) = Peint i
psetint is = Peopn Pset $ map (\i -> Peint i) $ IntSet.toList is

