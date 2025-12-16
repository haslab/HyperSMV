module Smv.Syntax where

import Control.Monad
import Data.List as List
import Data.Foldable
import Data.Hashable
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import GHC.Generics

import Utils
import Location as L

-- an hyperLTL formula
data Pformula
    = Pfexists String Pformula
    | Pfforall String Pformula
    | Pfltl Pexpr
    deriving (Eq,Ord,Show)

data Pmodule = Pmodule { p_name :: String, p_items :: [Located Pitem] }
    deriving (Eq,Ord,Show)

data Pident = Pident String Pdims deriving (Eq,Ord,Show)

type DualPident = (Pident,Bool) -- for next variables

type IsFrozen = Bool

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

data Ptype
    = Pboolean
    | Pint Int Int
    | Penum IntSet
    | Parray Int Int Ptype
    deriving (Eq,Ord,Show)

data Pvar = Pvar { pvar_name :: Pident, pvar_type :: Ptype }
    deriving (Eq,Ord,Show)

data Pdefine = Pdefine { pdef_lhs :: String, pdef_rhs :: Pexpr }
    deriving (Eq,Ord,Show)

data Popn = Pand | Por | Pset deriving (Eq,Ord,Show,Generic)
data Pop1 = Pnot | Pf | Pg | Px | Py | Pz | Ph | Pnext | Patom {-used only for autohyper formulas-} deriving (Eq,Ord,Show,Generic)
data Pop2 = Pin | Pequiv | Pimplies | Pplus | Pminus | Ptimes | Punion | Peq | Pneq | Plt | Pleq | Pgt | Pgeq | Pu | Pv deriving (Eq,Ord,Show,Generic)

instance Hashable Pop1
instance Hashable Pop2
instance Hashable Popn

isLTLOp1 :: Pop1 -> Bool
isLTLOp1 Pf = True
isLTLOp1 Pg = True
isLTLOp1 Px = True
isLTLOp1 Py = True
isLTLOp1 Pz = True
isLTLOp1 Ph = True
isLTLOp1 _ = False

isLTLOp2 :: Pop2 -> Bool
isLTLOp2 Pu = True
isLTLOp2 Pv = True
isLTLOp2 _ = False

type Pdims = [Pexpr]

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

data Passign = Passign Passign_lhs Pexpr deriving (Eq,Ord,Show,Generic)

data Passign_lhs
    = Painit Pident
    | Panext Pident
    deriving (Eq,Ord,Show,Generic)
    
isLhsInit :: Passign_lhs -> Maybe Pident
isLhsInit (Painit n) = Just n
isLhsInit (Panext n) = Nothing

isLhsNext :: Passign_lhs -> Maybe Pident
isLhsNext (Panext n) = Just n
isLhsNext (Painit n) = Nothing
    
numQuantifiers :: Pformula -> Int
numQuantifiers (Pfforall _ f) = numQuantifiers f + 1
numQuantifiers (Pfexists _ f) = numQuantifiers f + 1
numQuantifiers (Pfltl _) = 0
    
pimplies :: Pexpr -> Pexpr -> Pexpr
pimplies e1 e2
    | e1 == ptrue = e2
    | e1 == pfalse = ptrue
    | e2 == ptrue = ptrue
    | e2 == pfalse = pnot e1
    | otherwise = Peop2 Pimplies e1 e2
    
pnot :: Pexpr -> Pexpr
pnot (Pebool b) = Pebool (not b)
pnot e = Peop1 Pnot e
    
ptrue :: Pexpr
ptrue = Pebool True

pfalse :: Pexpr
pfalse = Pebool False

pandMaybe :: Maybe Pexpr -> Maybe Pexpr -> Maybe Pexpr
pandMaybe Nothing r = r
pandMaybe l Nothing = l
pandMaybe (Just l) (Just r) = Just $ pand l r

pand :: Pexpr -> Pexpr -> Pexpr
pand e1 e2 = pands [e1,e2]
    
pandsMaybe :: [Pexpr] -> Maybe Pexpr
pandsMaybe es = let es' = pands es in if es' == Pebool True then Nothing else Just es'

pands :: [Pexpr] -> Pexpr
pands = pands' []

pands' :: [Pexpr] -> [Pexpr] -> Pexpr
pands' [] [] = Pebool True
pands' [y] [] = y
pands' acc [] = Peopn Pand acc
pands' acc ((vands -> Just es1) : es2) = pands' acc (es1 ++ es2)
pands' acc (e@(vands -> Nothing) : es) = case e of
    ((==ptrue) -> True) -> pands' acc es
    ((==pfalse) -> True) -> pfalse
    otherwise -> pands' (e : acc) es

porMaybe :: Maybe Pexpr -> Maybe Pexpr -> Maybe Pexpr
porMaybe Nothing r = r
porMaybe l Nothing = l
porMaybe (Just l) (Just r) = Just $ por l r

por :: Pexpr -> Pexpr -> Pexpr
por e1 e2 = pors [e1,e2]

porsMaybe :: [Pexpr] -> Maybe Pexpr
porsMaybe es = let es' = pors es in if es' == Pebool False then Nothing else Just es'

pors :: [Pexpr] -> Pexpr
pors = pors' []

pors' :: [Pexpr] -> [Pexpr] -> Pexpr
pors' [] [] = Pebool False
pors' [y] [] = y
pors' acc [] = Peopn Por acc
pors' acc ((vors -> Just es1) : es2) = pors' acc (es1 ++ es2)
pors' acc (e@(vors -> Nothing) : es) = case e of
    ((==pfalse) -> True) -> pors' acc es
    ((==ptrue) -> True) -> ptrue
    otherwise -> pors' (e : acc) es
    
peopn :: Popn -> [Pexpr] -> Pexpr
peopn Pand = pands
peopn Por = pors
peopn Pset = pset
    
piinit :: [Pexpr] -> Maybe Pitem
piinit [] = Nothing
piinit es = Just $ Piinit $ pands es

piinvar :: [Pexpr] -> Maybe Pitem
piinvar [] = Nothing
piinvar es = Just $ Piinvar $ pands es

pitrans :: [Pexpr] -> Maybe Pitem
pitrans [] = Nothing
pitrans es = Just $ Pitrans $ pands es
    
pivar :: [L.Located (Pident,Ptype)] -> Bool -> Pitem
pivar xs isFrozen = Pivar (map pvar xs) isFrozen
    where pvar l = let (x,y) = unloc l in mk_loc (loc l) (Pvar x y)
    
pijustice :: L.Located Pexpr -> Pitem
pijustice e = Pijustice (unloc e)
    
pidefine :: [L.Located (String,Pexpr)] -> Pitem
pidefine xs = Pidefine (map pdefine xs)
    where pdefine l = let (x,y) = unloc l in mk_loc (loc l) (Pdefine x y)
    
peopn2 :: Popn -> Pexpr -> Pexpr -> Pexpr
peopn2 o (Peopn o1 es1) (Peopn o2 es2) | o == o1 && o == o2 = Peopn o (es1 ++ es2)
peopn2 o (Peopn o1 es1) e2 | o == o1 = Peopn o (e2 : es1)
peopn2 o e1 (Peopn o2 es2) | o == o2 = Peopn o (e1 : es2)
peopn2 o e1 e2 = Peopn o [e1,e2]

vvar :: Pexpr -> Maybe DualPident
vvar (Peident n t) = Just (n,False)
vvar (Peop1 Pnext (Peident n t)) = Just (n,True)
vvar e = Nothing

pvar :: DualPident -> ExprType -> Pexpr
pvar (n,False) t = Peident n t
pvar (n,True) t = pnext $ Peident n t

vnot :: Pexpr -> Maybe Pexpr
vnot (Peop1 Pnot e) = Just e
vnot _ = Nothing

vors :: Pexpr -> Maybe [Pexpr]
vors (Peopn Por es) = Just es
vors _ = Nothing

vors' :: Pexpr -> [Pexpr]
vors' (Peopn Por es) = es
vors' e = [e]

vands :: Pexpr -> Maybe [Pexpr]
vands (Peopn Pand es) = Just es
vands _ = Nothing

vands' :: Pexpr -> [Pexpr]
vands' (Peopn Pand es) = es
vands' e = [e]
    
vnotnot :: Pexpr -> Maybe Pexpr
vnotnot = vnot >=> vnot

vnotors :: Pexpr -> Maybe [Pexpr]
vnotors = vnot >=> vors

vnotands :: Pexpr -> Maybe [Pexpr]
vnotands = vnot >=> vands

vcase :: Pexpr -> Maybe [(Pexpr,Pexpr)]
vcase (Pecase cs) = Just cs
vcase (Pedemorgan c te fe) = Just [(c,te),(pnot c,fe)]
vcase e = Nothing

vnext :: Pexpr -> Maybe Pexpr
vnext (Peop1 Pnext e) = Just e
vnext _ = Nothing

pnext :: Pexpr -> Pexpr
pnext e@(Pebool {}) = e
pnext e@(Peint {}) = e
pnext e = Peop1 Pnext e

moduleDefines :: Pmodule -> [Located Pdefine]
moduleDefines (Pmodule _ is) = concat $ map itemDefines $ map unloc is

itemDefines :: Pitem -> [Located Pdefine]
itemDefines (Pidefine ds) = ds
itemDefines _ = []

isPivar :: Pitem -> Bool
isPivar (Pivar {}) = True
isPivar _ = False

isPidefine :: Pitem -> Bool
isPidefine (Pidefine _) = True
isPidefine _ = False

pdefineName :: Pdefine -> String
pdefineName (Pdefine n _) = n

collectDefines :: [L.Located Pitem] -> [L.Located Pdefine]
collectDefines [] = []
collectDefines (L.Located _ (Pidefine ds):defs) = ds ++ collectDefines defs

splitPassigns :: [L.Located Passign] -> ([L.Located Passign],[L.Located Passign])
splitPassigns [] = ([],[])
splitPassigns (a@(L.unloc -> Passign l r):ps) = case l of
        Painit n -> (a:xs,ys)
        Panext n -> (xs,a:ys)
    where
    (xs,ys) = splitPassigns ps

peq :: Pexpr -> Pexpr -> Pexpr
peq e1 e2 = Peop2 Peq e1 e2

pneq :: Pexpr -> Pexpr -> Pexpr
pneq e1 e2 = pnot $ Peop2 Peq e1 e2

pset :: [Pexpr] -> Pexpr
pset [x] = x
pset xs = Peopn Pset xs

pbools :: Pexpr
pbools = pset [Pebool False,Pebool True]

peop1 :: Pop1 -> Pexpr -> Pexpr
peop1 Pf (Pebool b) = Pebool b
peop1 Pg (Pebool b) = Pebool b
peop1 o e1 = Peop1 o e1

peop2 :: Pop2 -> Pexpr -> Pexpr -> Pexpr
peop2 Pu e1 (Pebool b) = Pebool b
peop2 Pv e1 (Pebool b) = Pebool b
peop2 Pplus e1 e2 = pplus e1 e2
peop2 Pin e1 e2 = pin e1 e2
peop2 o e1 e2 = Peop2 o e1 e2

isCmpOp2 :: Pop2 -> Bool
isCmpOp2 Peq = True
isCmpOp2 Pneq = True
isCmpOp2 Plt = True
isCmpOp2 Pleq = True
isCmpOp2 Pgt = True
isCmpOp2 Pgeq = True
isCmpOp2 o = False

isBoolOp2 :: Pop2 -> Bool
isBoolOp2 Pequiv = True
isBoolOp2 Pimplies = True
isBoolOp2 _ = False

negCmpOp2 :: Pop2 -> Pop2
negCmpOp2 Peq = Pneq
negCmpOp2 Pneq = Peq
negCmpOp2 Plt = Pgeq
negCmpOp2 Pleq = Pgt
negCmpOp2 Pgt = Pleq
negCmpOp2 Pgeq = Plt
negCmpOp2 o = error $ "negCmpOp2: " ++ show o

invCmpOp2 :: Pop2 -> Pop2
invCmpOp2 Peq = Peq
invCmpOp2 Pneq = Pneq
invCmpOp2 Plt = Pgt
invCmpOp2 Pleq = Pgeq
invCmpOp2 Pgt = Plt
invCmpOp2 Pgeq = Pleq
invCmpOp2 o = error $ "invCmpOp2: " ++ show o

isBoolOpn :: Popn -> Bool
isBoolOpn Pset = False
isBoolOpn Pand = True
isBoolOpn Por = True

pplus :: Pexpr -> Pexpr -> Pexpr
pplus (Peint i) (Peint j) = Peint (i+j)
pplus e1 e2 = Peop2 Pplus e1 e2

pin :: Pexpr -> Pexpr -> Pexpr
pin e1 e2@(vset -> Just is) = if List.null is then Pebool False else Peop2 Pin e1 e2
pin e1 e2@(Pebool {}) = peop2 Peq e1 e2
pin e1 e2@(Peint {}) = peop2 Peq e1 e2
pin e1 e2 = Peop2 Pin e1 e2

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

vsetint :: Pexpr -> Maybe IntSet
vsetint (Peint i) = Just $ IntSet.singleton i
vsetint (Peopn Pset es) = liftM unionsIntSet $ mapHashSetM vsetint $ HashSet.fromList es
vsetint (Peop2 Punion e1 e2) = do
    is1 <- vsetint e1
    is2 <- vsetint e2
    return $ IntSet.union is1 is2
vsetint e = Nothing

vsetbool :: Pexpr -> Maybe (HashSet Bool)
vsetbool (Pebool b) = Just $ HashSet.singleton b
vsetbool (Peopn Pset es) = liftM unionsHashSet $ mapHashSetM vsetbool $ HashSet.fromList es
vsetbool (Peop2 Punion e1 e2) = do
    is1 <- vsetbool e1
    is2 <- vsetbool e2
    return $ HashSet.union is1 is2
vsetbool e = Nothing


pidentName :: Pident -> String
pidentName (Pident n _) = n

instance Hashable Pident where
    hashWithSalt i (Pident x es) = hashWithSalt i x

data ExprType = EInt | EBool | EUnknown deriving (Eq,Ord,Show,Generic)

instance Hashable ExprType

toExprType :: Ptype -> ExprType
toExprType Pboolean = EBool
toExprType (Pint {}) = EInt
toExprType (Penum {}) = EInt
toExprType (Parray i j t) = toExprType t

addDimPident :: Pident -> Pexpr -> Pident
addDimPident (Pident n dims) dim = Pident n (dims++[dim])

remDimPident :: Pident -> Pident
remDimPident pn@(Pident n []) = pn
remDimPident (Pident n dims) = Pident n (init dims)

mkQuantDim :: String -> Pexpr
mkQuantDim n = Peident (Pident n []) EUnknown

psetint :: IntSet -> Pexpr
psetint (isSingletonIntSet -> Just i) = Peint i
psetint is = Peopn Pset $ map (\i -> Peint i) $ IntSet.toList is

