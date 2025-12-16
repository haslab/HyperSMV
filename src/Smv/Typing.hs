module Smv.Typing where

import Data.List as List
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import qualified Data.HashSet as HashSet
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Hashable
import GHC.Generics

import Pretty
import Utils
import qualified Location as L
import Smv.Syntax
import Smv.Packed
import Smv.Pretty
import Transform.Substitute
import Transform.Pexpr
import Pretty

addModuleTypes :: PackedPmodule -> PackedPmodule
addModuleTypes p = p
    { p_defines = ds
    , p_init = (addExprTypes ss) (p_init p)
    , p_invar = (addExprTypes ss) (p_invar p)
    , p_trans = (addExprTypes ss) (p_trans p)
    , p_assigns = addAssignTypes ss (p_assigns p)
    , p_ltlspec = fmap (addExprTypes ss) (p_ltlspec p)
    }  
  where
    vs = Map.map toExprType (p_vars p)
    (ss,ds) = addDefineTypes vs (p_defines p)

type PackedPtypes = Map Pident ExprType

addDefineTypes :: PackedPtypes -> PackedPdefs -> (PackedPtypes,PackedPdefs)
addDefineTypes vs ds = addDefineTypes' vs (Map.toList ds)
    where
    addDefineTypes' :: PackedPtypes -> [(Pident,Pexpr)] -> (PackedPtypes,PackedPdefs)
    addDefineTypes' vs [] = (vs,Map.empty)
    addDefineTypes' vs ds = case filter (isResolved vs . snd) ds of
        (ok@(n,e):_) -> (vs',Map.insert n e' ds')
            where
            e' = addExprTypes vs e
            (vs',ds') = addDefineTypes' (Map.insert n (typecheckExpr e') vs) (List.delete ok ds)
        [] -> error $ "addDefineTypes: unable to resolve defines\n" ++ show vs ++ "\n" ++ unlines (map (\(x,y) -> prettyprint x ++ " := " ++ prettyprint y) ds)
    isResolved :: PackedPtypes -> Pexpr -> Bool
    isResolved vs e = varSet e `Set.isSubsetOf` (Map.keysSet vs)

addAssignTypes :: PackedPtypes -> PackedPassigns -> PackedPassigns
addAssignTypes vs (PackedPassigns xs ys) = PackedPassigns (addDefs xs) (addDefs ys)
    where
    addDefs :: PackedPdefs -> PackedPdefs
    addDefs = Map.map (addExprTypes vs)

addExprTypes :: PackedPtypes -> Pexpr -> Pexpr
addExprTypes vs e@(Peident n _) = case Map.lookup n vs of
    Just t -> Peident n t
    Nothing -> error $ "addExprTypes: " ++ show e ++ " " ++ show vs
addExprTypes vs e@(Pebool _) = e
addExprTypes vs e@(Peint _) = e
addExprTypes vs e@(Peop1 o e1) = Peop1 o (addExprTypes vs e1)
addExprTypes vs e@(Peop2 o e1 e2) = Peop2 o (addExprTypes vs e1) (addExprTypes vs e2)
addExprTypes vs e@(Peopn o es) = Peopn o $ map (addExprTypes vs) es
addExprTypes vs e@(Pecase es) = Pecase $ map (addExprTypes vs >< addExprTypes vs) es
addExprTypes vs e@(Pedemorgan c e1 e2) = Pedemorgan (addExprTypes vs c) (addExprTypes vs e1) (addExprTypes vs e2)

joinHyperPtypes :: [(String,PackedPtypes)] -> PackedPtypes
joinHyperPtypes = Map.unions . map (uncurry toHyperPackedPtypes)

toHyperPackedPtypes :: String -> PackedPtypes -> PackedPtypes
toHyperPackedPtypes h s = Map.foldrWithKey (\n t -> Map.insert (toHyperPident h n) t) Map.empty s

addFormulaTypes :: [PackedPtypes] -> Pformula -> Pformula
addFormulaTypes = addFormulaTypes' Map.empty
    where
    addFormulaTypes' :: PackedPtypes -> [PackedPtypes] -> Pformula -> Pformula
    addFormulaTypes' acc (ss:sss) (Pfexists n f) = Pfexists n $ addFormulaTypes' (Map.union acc $ toHyperPackedPtypes n ss) sss f
    addFormulaTypes' acc (ss:sss) (Pfforall n f) = Pfforall n $ addFormulaTypes' (Map.union acc $ toHyperPackedPtypes n ss) sss f
    addFormulaTypes' acc [] (Pfltl e) = Pfltl $ addExprTypes acc e
    addFormulaTypes' acc ss f = error $ "addFormulaTypes " ++ unwords (map show ss) ++ " " ++ prettySMV Default f

isPint :: Ptype -> Maybe IntSet
isPint t = case toVarType t of
    VInt is -> Just is
    VBool -> Nothing

data VarType = VInt IntSet | VBool deriving (Eq,Ord,Show,Generic)

instance Hashable VarType

toVarType :: Ptype -> VarType
toVarType Pboolean = VBool
toVarType (Pint i j) = VInt $ IntSet.fromList [i..j]
toVarType (Penum is) = VInt is
toVarType (Parray _ _ t) = toVarType t

fromVarType :: VarType -> Ptype
fromVarType (VInt is) = Penum is
fromVarType VBool = Pboolean

sizeOfVarType :: VarType -> Int
sizeOfVarType (VInt is) = IntSet.size is
sizeOfVarType VBool = 2

exprOfVarType :: VarType -> ExprType
exprOfVarType (VInt is) = EInt
exprOfVarType VBool = EBool

typecheckExpr :: Pexpr -> ExprType
typecheckExpr (Peident n t) = t
typecheckExpr (Pebool b) = EBool
typecheckExpr (Peint i) = EInt
typecheckExpr (Peop1 o e1) = typecheckPop1 o (typecheckExpr e1)
typecheckExpr (Peop2 o e1 e2) = typecheckPop2 o (typecheckExpr e1) (typecheckExpr e2)
typecheckExpr (Peopn Pand es) | typecheckAll EBool (map typecheckExpr es) = EBool
typecheckExpr (Peopn Por es) | typecheckAll EBool (map typecheckExpr es) = EBool
typecheckExpr (Peopn Pset []) = EUnknown
typecheckExpr (Peopn Pset (e:es)) | typecheckAll (typecheckExpr e) (map typecheckExpr es) = typecheckExpr e
typecheckExpr (Pecase []) = EUnknown
typecheckExpr (Pecase ((c,e):ces)) | typecheck EBool c && typecheckAll EBool (map (typecheckExpr . fst) ces) && typecheckAll (typecheckExpr e) (map (typecheckExpr . snd) ces) = typecheckExpr e
typecheckExpr (Pedemorgan c e1 e2) | typecheck EBool c && typecheck2 (typecheckExpr e1) (typecheckExpr e2) = typecheckExpr e1
typecheckExpr e = error $ "typecheckExpr: " ++ show e

typecheck :: ExprType -> Pexpr -> Bool
typecheck t e = t == typecheckExpr e

typecheck2 :: ExprType -> ExprType -> Bool
typecheck2 t1 t2 = t1 == t2

typecheckAll :: Foldable t => ExprType -> t ExprType -> Bool
typecheckAll t es = all (==t) es

-- performs no typechecking, trusts that types are correctly assigned
typeOfExpr :: Pexpr -> ExprType
typeOfExpr (Peident n t) = t
typeOfExpr (Pebool b) = EBool
typeOfExpr (Peint i) = EInt
typeOfExpr (Peop1 o e1) = typeOfPop1 o (typeOfExpr e1)
typeOfExpr (Peop2 o e1 e2) = typeOfPop2 o (typeOfExpr e1) (typeOfExpr e2)
typeOfExpr (Peopn Pand es) = EBool
typeOfExpr (Peopn Por es) = EBool
typeOfExpr (Peopn Pset (e:es)) = typeOfExpr e
--typeOfExpr (Peproj n _ t) = t
typeOfExpr (Pecase (c:cs)) = typeOfExpr (snd c)
typeOfExpr (Pedemorgan c e1 e2) = typeOfExpr e1
typeOfExpr e = error $ "typeOfExpr: " ++ show e

typecheckPop1 :: Pop1 -> ExprType -> ExprType
typecheckPop1 Pnot EBool = EBool
typecheckPop1 o EBool | isLTLOp1 o = EBool
typecheckPop1 Patom t1 = t1
typecheckPop1 Pnext t1 = t1

typeOfPop1 :: Pop1 -> ExprType -> ExprType
typeOfPop1 Pnot t1 = EBool
typeOfPop1 o t1 | isLTLOp1 o = EBool
typeOfPop1 Patom t1 = t1
typeOfPop1 Pnext t1 = t1

varTypeOfPop1 :: Pop1 -> VarType -> VarType
varTypeOfPop1 Pnot t1 = VBool
varTypeOfPop1 o t1 | isLTLOp1 o = VBool
varTypeOfPop1 Patom t1 = t1
varTypeOfPop1 Pnext t1 = t1

typecheckPop2 :: Pop2 -> ExprType -> ExprType -> ExprType
typecheckPop2 Pequiv t1 t2 | typecheckAll EBool [t1,t2] = EBool
typecheckPop2 Pplus t1 t2 | typecheckAll EInt [t1,t2] = EInt
typecheckPop2 Pminus t1 t2 | typecheckAll EInt [t1,t2] = EInt
typecheckPop2 Ptimes t1 t2 | typecheckAll EInt [t1,t2] = EInt
typecheckPop2 Pimplies t1 t2 | typecheckAll EBool [t1,t2] = EBool
typecheckPop2 Punion t1 t2 | typecheck2 t1 t2 = t1
typecheckPop2 Peq t1 t2 | typecheck2 t1 t2 = EBool
typecheckPop2 Pneq t1 t2 | typecheck2 t1 t2 = EBool
typecheckPop2 Plt t1 t2 | typecheckAll EInt [t1,t2] = EBool
typecheckPop2 Pleq t1 t2 | typecheckAll EInt [t1,t2] = EBool
typecheckPop2 Pgt t1 t2 | typecheckAll EInt [t1,t2] = EBool
typecheckPop2 Pu t1 t2 | typecheckAll EBool [t1,t2] = EBool
typecheckPop2 Pv t1 t2 | typecheckAll EBool [t1,t2] = EBool
typecheckPop2 Pin t1 t2 | typecheck2 t1 t2 = EBool
typecheckPop2 o t1 t2 = error $ "typecheckPop2: " ++ show o ++" "++ show t1 ++" "++ show t2

typeOfPop2 :: Pop2 -> ExprType -> ExprType -> ExprType
typeOfPop2 Pequiv t1 t2 = EBool
typeOfPop2 Pplus t1 t2 = EInt
typeOfPop2 Pminus t1 t2 = EInt
typeOfPop2 Ptimes t1 t2 = EInt
typeOfPop2 Pimplies t1 t2 = EBool
typeOfPop2 Punion t1 t2 = t1
typeOfPop2 Peq t1 t2 = EBool
typeOfPop2 Pneq t1 t2 = EBool
typeOfPop2 Plt t1 t2 = EBool
typeOfPop2 Pleq t1 t2 = EBool
typeOfPop2 Pgt t1 t2 = EBool
typeOfPop2 Pu t1 t2 = EBool
typeOfPop2 Pv t1 t2 = EBool
typeOfPop2 Pin t1 t2 = EBool
typeOfPop2 o t1 t2 = error $ "typeOfPop2: " ++ show o

unionVarType :: VarType -> VarType -> VarType
unionVarType VBool VBool = VBool
unionVarType (VInt is) (VInt js) = VInt (IntSet.union is js)

varTypeOfPop2 :: Pop2 -> VarType -> VarType -> VarType
varTypeOfPop2 Pequiv t1 t2 = VBool
varTypeOfPop2 Pimplies t1 t2 = VBool
varTypeOfPop2 Punion t1 t2 = unionVarType t1 t2
varTypeOfPop2 Peq t1 t2 = VBool
varTypeOfPop2 Pneq t1 t2 = VBool
varTypeOfPop2 Plt t1 t2 = VBool
varTypeOfPop2 Pleq t1 t2 = VBool
varTypeOfPop2 Pgt t1 t2 = VBool
varTypeOfPop2 Pu t1 t2 = VBool
varTypeOfPop2 Pv t1 t2 = VBool
varTypeOfPop2 Pin t1 t2 = VBool
varTypeOfPop2 Pplus (VInt is) (VInt js) = VInt $ IntSet.fromList [ i + j | i <- IntSet.toList is, j <- IntSet.toList js ]
varTypeOfPop2 Pminus (VInt is) (VInt js) = VInt $ IntSet.fromList [ i - j | i <- IntSet.toList is, j <- IntSet.toList js ]
varTypeOfPop2 Ptimes (VInt is) (VInt js) = VInt $ IntSet.fromList [ i * j | i <- IntSet.toList is, j <- IntSet.toList js ]
varTypeOfPop2 o t1 t2 = error $ "varTypeOfPop2: " ++ prettyprint o ++ " " ++ show t1 ++ " " ++ show t2

isBoolExpr :: Pexpr -> Bool
isBoolExpr e = typeOfExpr e == EBool

substTypes :: Subst -> PackedPtypes
substTypes ss = Map.map typeOfExpr ss

moduleTypes :: PackedPmodule -> PackedPtypes
moduleTypes p = Map.map typeOfExpr (p_defines p) `Map.union` Map.map toExprType (p_vars p)

simplifyType :: Ptype -> Ptype
simplifyType t@(Penum is) = case isRange (IntSet.toList is) of
    Just (i,j) -> Pint i j
    Nothing -> t
simplifyType t = t

iteExpr :: Pexpr -> Pexpr -> Pexpr -> Pexpr
iteExpr c e1 e2 | isBoolExpr e1 = pand c e1 `por` pand (pnot c) e2
iteExpr c e1 e2 = Pedemorgan c e1 e2

