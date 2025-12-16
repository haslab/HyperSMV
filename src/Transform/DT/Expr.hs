module Transform.DT.Expr where

import qualified Data.IntSet as IntSet
import Data.List as List
import Data.Massiv.Array
import Data.Massiv.Array.Unsafe
import qualified Data.Vector as V

import Utils
import Smv.Syntax
import Smv.Typing
import Transform.Pexpr
import Data.DT
import Data.DD

data ExprFeature
    = LtFeature Int Int -- x_i < x_j
    | GtFeature Int Int -- x_i > x_j
    | EqFeature Int Int -- x_i = x_j
    | EqIntFeature Int Int -- x_i = val
    | EquivFeature Int Int -- x_i <-> x_j
    | BoolFeature Int -- x_i
    deriving (Eq,Ord,Show)

instance IsVal val => IsFeature (Pident,VarType) ExprFeature val where
    
    allFeatures (names,dataset,out) = List.map (,1) (boolfeatures ++ intfeatures)
        where
        (V.toList -> bools,V.toList -> ints) = V.partition ((==VBool) . snd . snd) (V.imap (,) names)
        boolfeatures
            =  [ EquivFeature i j | (i,_) <- bools, (j,_) <- bools, i /= j ]
            ++ [ BoolFeature i | (i,_) <- bools ]
        intfeatures
            =  [ cmp i j | (i,_) <- ints, (j,_) <- ints, i /= j, cmp <- cmps ]
            ++ [ intcmp i v | (i,(_,VInt vs)) <- ints, v <- IntSet.toList vs, intcmp <- intcmps ]
        cmps = [LtFeature,GtFeature,EqFeature]
        intcmps = [EqIntFeature]
    evalFeature (LtFeature i j) ((ns,t,out),row) = (mIndex "evalFeature" t (row :. i)) < (mIndex "evalFeature" t (row :. j))
    evalFeature (GtFeature i j) ((ns,t,out),row) = (mIndex "evalFeature" t (row :. i)) > (mIndex "evalFeature" t (row :. j))
    evalFeature (EqFeature i j) ((ns,t,out),row) = (mIndex "evalFeature" t (row :. i)) == (mIndex "evalFeature" t (row :. j))
    evalFeature (EqIntFeature i v) ((ns,t,out),row) = (valToInt $ mIndex "evalFeature" t (row :. i)) == v
    evalFeature (EquivFeature i j) ((ns,t,out),row) = (mIndex "evalFeature" t (row :. i)) == (mIndex "evalFeature" t (row :. j))
    evalFeature (BoolFeature i) ((ns,t,out),row) = (valToBool $ mIndex "evalFeature" t (row :. i))

featureToExpr :: V.Vector (Pident,VarType) -> ExprFeature -> Pexpr
featureToExpr ns (LtFeature i j) = Peop2 Plt (Peident ni $ exprOfVarType ti) (Peident nj $ exprOfVarType tj)
    where ((ni,ti),(nj,tj)) = ((vIndex "featureToExpr" ns i),(vIndex "featureToExpr" ns j))
featureToExpr ns (GtFeature i j) = Peop2 Pgt (Peident ni $ exprOfVarType ti) (Peident nj $ exprOfVarType tj)
    where ((ni,ti),(nj,tj)) = ((vIndex "featureToExpr" ns i),(vIndex "featureToExpr" ns j))
featureToExpr ns (EqFeature i j) = Peop2 Peq (Peident ni $ exprOfVarType ti) (Peident nj $ exprOfVarType tj)
    where ((ni,ti),(nj,tj)) = ((vIndex "featureToExpr" ns i),(vIndex "featureToExpr" ns j))
featureToExpr ns (EqIntFeature i v) = Peop2 Peq (Peident ni $ exprOfVarType ti) (Peint v)
    where (ni,ti) = (vIndex "featureToExpr" ns i)
featureToExpr ns (EquivFeature i j) = Peop2 Pequiv (Peident ni $ exprOfVarType ti) (Peident nj $ exprOfVarType tj)
    where ((ni,ti),(nj,tj)) = ((vIndex "featureToExpr" ns i),(vIndex "featureToExpr" ns j))
featureToExpr ns (BoolFeature i) = Peident ni $ exprOfVarType ti
    where (ni,ti) = (vIndex "featureToExpr" ns i)

treeToExpr :: V.Vector (Pident,VarType) -> DecisionTree ExprFeature -> Pexpr
treeToExpr ns (Leaf b) = Pebool b
treeToExpr ns (Node f l r) = iteExpr (featureToExpr ns f) (treeToExpr ns l) (treeToExpr ns r)

synthesizeExpr :: IsVal val => Table (Pident,VarType) val -> Pexpr
synthesizeExpr dataset = treeToExpr (fst3 dataset) (classifyId3 dataset)
