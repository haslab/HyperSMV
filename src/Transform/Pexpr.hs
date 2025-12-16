module Transform.Pexpr where

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Control.Monad
import Data.Hashable
import GHC.Generics
import Prettyprinter

import Pretty
import Utils
import Smv.Syntax
import Smv.Pretty

data Quant = Qforall | Qexists
    deriving (Eq,Ord,Show,Generic)
    
instance Pretty Quant where
    pretty Qforall = "forall"
    pretty Qexists = "exists"
    
instance Hashable Quant

mapFormula :: Monad m => (Pexpr -> m Pexpr) -> Pformula -> m Pformula
mapFormula r (Pfforall n f) = liftM (Pfforall n) $ mapFormula r f
mapFormula r (Pfexists n f) = liftM (Pfexists n) $ mapFormula r f
mapFormula r (Pfltl e) = liftM Pfltl $ r e

exprPformula :: Pformula -> Pexpr
exprPformula (Pfexists n f) = exprPformula f
exprPformula (Pfforall n f) = exprPformula f
exprPformula (Pfltl e) = e

quantStringFormula :: Pformula -> String
quantStringFormula (Pfexists n f) = 'E' : quantStringFormula f
quantStringFormula (Pfforall n f) = 'A' : quantStringFormula f
quantStringFormula (Pfltl e) = []

quantsPformula :: Pformula -> [(String,Quant)]
quantsPformula (Pfexists n f) = (n,Qexists) : quantsPformula f
quantsPformula (Pfforall n f) = (n,Qforall) : quantsPformula f
quantsPformula (Pfltl e) = []

applyQuantsExpr :: [(String,Quant)] -> Pexpr -> Pformula
applyQuantsExpr [] e = Pfltl e
applyQuantsExpr (q:qs) e = applyQuantFormula q (applyQuantsExpr qs e)
    
applyQuantFormula :: (String,Quant) -> Pformula -> Pformula
applyQuantFormula (n,Qforall) f = Pfforall n f 
applyQuantFormula (n,Qexists) f = Pfexists n f 

varsFormula :: Pformula -> Set Pident
varsFormula (Pfforall n f) = varsFormula f
varsFormula (Pfexists n f) = varsFormula f
varsFormula (Pfltl e) = varSet e

isFreeExpr :: Pexpr -> Bool
isFreeExpr e = not $ Set.null (varSet e)

varSet :: Pexpr -> Set Pident
varSet (Peident n t) = Set.singleton n
varSet (Pebool _) = Set.empty
varSet (Peint _) = Set.empty
varSet (Peop1 o e) = varSet e
varSet (Peop2 o e1 e2) = varSet e1 `Set.union` varSet e2
varSet (Peopn o es) = unionsSet $ map varSet es
varSet (Pecase cs) = unionsSet $ map (uncurry Set.union . (varSet >< varSet)) cs
varSet (Pedemorgan c e1 e2) = Set.unions [varSet c,varSet e1,varSet e2]
varSet e = error $ "doubleVarSet: " ++ prettySMV Default e

varsSet :: HashSet Pexpr -> Set Pident
varsSet = unionsSet . HashSet.map varSet

isSingleDimExpr :: Pexpr -> Maybe String
isSingleDimExpr e = isSingletonSet u
    where
    u = Set.unions (Set.map dimsPident (varSet e))
    
inlineCaseExprBool :: [(Pexpr,Pexpr)] -> Pexpr
inlineCaseExprBool cs = inlineCases [] cs
    where
    inlineCases pres [] = pfalse
    inlineCases pres ((c,e):cs) = (pands $ [c,pnot $ pors pres,e]) `por` inlineCases (c : pres) cs

mkOrIntExpr :: Pident -> IntSet -> IntSet -> Pexpr
mkOrIntExpr n is ts
    | IntSet.size is == 0 = pfalse
    | is == ts = ptrue
    | IntSet.size (IntSet.difference ts is) < IntSet.size is = pnot $ mkOrIntExpr' (IntSet.toList $ IntSet.difference ts is)
    | otherwise = mkOrIntExpr' (IntSet.toList is)
  where
    v = pvar (n,False) EInt
    mint = IntSet.findMin ts
    maxt = IntSet.findMax ts
    mkOrIntExpr' :: [Int] -> Pexpr
    mkOrIntExpr' [i] = peq v (Peint i)
    mkOrIntExpr' [i,j] = peq v (Peint i) `por` peq v (Peint j)
    mkOrIntExpr' is = case isRange is of
        Just (i,j) -> (if mint==i then Pebool True else Peop2 Pleq (Peint i) v) `pand` (if maxt==j then Pebool True else Peop2 Pleq v (Peint j))
        Nothing -> pors $ map (\i -> peq v (Peint i)) is

removeDimPident :: Pident -> Pident
removeDimPident (Pident n []) = Pident n []
removeDimPident (Pident n dims) = Pident n (init dims)

removeDimExpr :: Pexpr -> Pexpr
removeDimExpr e@(Pebool {}) = e
removeDimExpr e@(Peint {}) = e
removeDimExpr (Peident n t) = Peident (removeDimPident n) t
removeDimExpr (Peop1 o e1) = Peop1 o (removeDimExpr e1)
removeDimExpr (Peop2 o e1 e2) = Peop2 o (removeDimExpr e1) (removeDimExpr e2)
removeDimExpr (Peopn o es) = Peopn o $ map removeDimExpr es
removeDimExpr e = error $ "removeDimExpr " ++ prettyprint e

dimString :: Pexpr -> Maybe String
dimString (Peident (Pident n []) EUnknown) = Just n
dimString e = Nothing

dimsPident :: Pident -> Set String
dimsPident (Pident n []) = Set.empty
dimsPident (Pident n dims) = case dimString (last dims) of
    Just d -> Set.singleton d
    Nothing -> Set.empty

isSingleDimsPident :: Pident -> Maybe String
isSingleDimsPident = isSingletonSet . dimsPident

isLTLExpr :: Pexpr -> Bool
isLTLExpr (Pebool {}) = False
isLTLExpr (Peint {}) = False
isLTLExpr (Peident {}) = False
isLTLExpr (Peop1 o e1) = isLTLOp1 o || isLTLExpr e1
isLTLExpr (Peop2 o e1 e2) = isLTLOp2 o || isLTLExpr e1 || isLTLExpr e2
isLTLExpr (Peopn o es) = or $ map isLTLExpr es
isLTLExpr (Pecase cs) = any (\(x,y) -> isLTLExpr x || isLTLExpr y) cs
isLTLExpr (Pedemorgan c e1 e2) = isLTLExpr c || isLTLExpr e1 || isLTLExpr e2
isLTLExpr e = error $ "isLTLExpr: " ++ show e

sizeExpr :: (Pident -> Int) -> Pexpr -> Int
sizeExpr szOf = go
    where
    go (Pebool {}) = 1
    go (Peint {}) = 1
    go (Peident n t) = szOf n
    go (Peop1 o e1) = 1 + go e1
    go (Peop2 o e1 e2) = 1 + go e1 + go e2
    go (Peopn o es) = 1 + sum (map go es)
    go (Pecase cs) = sum $ map (\(x,y) -> go x + go y) cs
    go (Pedemorgan c e1 e2) = go c + go e1 + go e2

occurrencesFormula :: Pformula -> Map Pident Int
occurrencesFormula (Pfforall n f) = occurrencesFormula f
occurrencesFormula (Pfexists n f) = occurrencesFormula f
occurrencesFormula (Pfltl e) = occurrencesExpr e

occurrencesExpr :: Pexpr -> Map Pident Int
occurrencesExpr (Pebool {}) = Map.empty
occurrencesExpr (Peint {}) = Map.empty
occurrencesExpr (Peident n t) = Map.singleton n 1
occurrencesExpr (Peop1 o e1) = occurrencesExpr e1
occurrencesExpr (Peop2 o e1 e2) = Map.unionWith (+) (occurrencesExpr e1) (occurrencesExpr e2)
occurrencesExpr (Peopn o es) = Map.unionsWith (+) $ map occurrencesExpr es
occurrencesExpr (Pecase cs) = Map.unionsWith (+) $ map (\(x,y) -> Map.unionWith (+) (occurrencesExpr x) (occurrencesExpr y)) cs
occurrencesExpr (Pedemorgan c e1 e2) = Map.unionsWith (+) [occurrencesExpr c,occurrencesExpr e1,occurrencesExpr e2]

isConstantExpr :: Pexpr -> Bool
isConstantExpr (Pebool {}) = True
isConstantExpr (Peint {}) = True
isConstantExpr e = False

isSimpleExpr :: Pexpr -> Bool
isSimpleExpr (Pebool {}) = True
isSimpleExpr (Peint {}) = True
isSimpleExpr (Peident {}) = True
isSimpleExpr e = False

isSingleDimPident :: Pident -> Maybe String
isSingleDimPident = maybeFromSet . dimsPident

