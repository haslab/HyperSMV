-- | Infers every AP boundary in a formula before any decision diagram is built.
module ExplicitState.APInference where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Either (partitionEithers)
import Data.List as List
import Control.Monad

import Smv.Syntax
import Smv.Typing
import Transform.Pexpr
import Transform.Bexpr

-- AP inference procedure.
inferCompactAPs :: Bformula -> Bformula
inferCompactAPs (Bforall n f) = Bforall n (inferCompactAPs f)
inferCompactAPs (Bexists n f) = Bexists n (inferCompactAPs f)
inferCompactAPs (Bltl e) = Bltl (inferCompactAPsExpr e)

-- | Tag atom boundaries in one model's expression.
inferCompactAPsExpr :: Bexpr -> Bexpr
inferCompactAPsExpr = go
  where
    go e
        -- a declared atom is already a boundary; never re-tag inside or around it
        | hasAtomBexpr e = descend e
        | Prelude.not (isLTLBexpr e) = leaf e
        | otherwise = descend e
    descend (Bopn o es) = Bopn o (HashSet.map go es)
    descend (Bop1 o e1) = Bop1 o (go e1)
    descend (Bop2 o e1 e2) = Bop2 o (go e1) (go e2)
    descend e = e
    -- a maximal non-temporal, atom-free region
    leaf e = case isSingleDimBexpr e of
        Just _ -> batom1 e
        Nothing -> mixed e
    -- one atom, but never wrap constants or non-boolean operands
    batom1 e@(Bbool {}) = e
    batom1 e@(Bints {}) = e
    batom1 e | isBoolBexpr e = Bop1 Patom e
             | otherwise = e
    -- a non-temporal region spanning several traces
    mixed (Bopn Pand es) =
        let (collapsed,rest0) = recognizeEqFamilies (HashSet.toList es)
            (covered,rest) = recognizeCoverFamilies rest0
        in Bopn Pand (HashSet.fromList (collapsed ++ covered ++ groupByDim Pand rest))
    mixed (Bopn Por es) =
        let (collapsed,rest0) = recognizeNeqFamilies (HashSet.toList es)
            (ordered,rest) = recognizeOrderFamilies rest0
        in Bopn Por (HashSet.fromList (collapsed ++ ordered ++ map mixedChild rest))
    mixed u@(Bop2 o l r)
        | isJust (isSingleDimBexpr l), isJust (isSingleDimBexpr r) = batom1 u
        | otherwise = Bop2 o (mixedChild l) (mixedChild r)
    mixed (Bop1 o e1) = Bop1 o (mixedChild e1)
    mixed e = e
    mixedChild e = case isSingleDimBexpr e of
        Just _ -> batom1 e
        Nothing -> mixed e
    -- Siblings that live in one trace are grouped into a single atom per trace rather than wrapped one by one.
    groupByDim o rest =
        let keyed = [ (isSingleDimBexpr e,e) | e <- rest ]
            singles = Map.fromListWith (flip (++)) [ (d,[e]) | (Just d,e) <- keyed ]
            others = [ mixedChild e | (Nothing,e) <- keyed ]
            wrap [e] = batom1 e
            wrap g = batom1 (Bopn o (HashSet.fromList g))
        in map wrap (Map.elems singles) ++ others

-- | A membership test @x in S@ over one variable.
data VTest = VTest { vtVar :: DualPident, vtType :: VarType, vtSet :: IntSet }

-- | Recognize a membership test.
vTest :: Bexpr -> Maybe VTest
vTest (Bop2 Pin (Bvar n t) (Bints s)) = Just (VTest n t s)
vTest (Bop2 Pin (Bints s) (Bvar n t)) = Just (VTest n t s)
vTest (Bop2 Peq (Bvar n t) (Bints s)) = Just (VTest n t s)
vTest (Bop2 Peq (Bints s) (Bvar n t)) = Just (VTest n t s)
vTest _ = Nothing

-- | A variable's value domain.
famDomOf :: VarType -> IntSet
famDomOf (VInt is) = is
famDomOf VBool = IntSet.fromList [0,1]

-- | A variable's trace dimension, if single.
famDimOf :: DualPident -> Maybe String
famDimOf = isSingleDimPident . fst

-- | The (variable, type) pair key of a family, canonically ordered by trace dimension.
type FamKey = ((DualPident,VarType),(DualPident,VarType))

-- | Build a family key from two cross-trace tests, if their dims differ.
famKey :: VTest -> VTest -> Maybe (FamKey,(VTest,VTest))
famKey a b = do
    da <- famDimOf (vtVar a)
    db <- famDimOf (vtVar b)
    guard (da /= db)
    return $ if da <= db then (((vtVar a,vtType a),(vtVar b,vtType b)),(a,b))
                         else (((vtVar b,vtType b),(vtVar a,vtType a)),(b,a))

-- | Whether a family's covered values make it a complete equality.
famComplete :: FamKey -> IntSet -> Bool
famComplete ((_,tx),(_,ty)) s =
    let rx = famDomOf tx `IntSet.difference` s
        ry = famDomOf ty `IntSet.difference` s
    in rx == ry && IntSet.size rx <= 1

-- | Build the native cross-trace equality atom for a family.
famEqAtom :: FamKey -> Bexpr
famEqAtom ((x,tx),(y,ty)) = Bop1 Patom (Bop2 Peq (Bvar x tx) (Bvar y ty))

-- | Two membership tests joined by a connective, as (key, shared value v, shape) evidence.
famPair :: Bexpr -> Bexpr -> Maybe (FamKey,Int,Maybe Bool,Bool)
famPair l r = do
    a0 <- vTest l
    b0 <- vTest r
    (k,(a,b)) <- famKey a0 b0
    let sing t = if IntSet.size (vtSet t) == 1 then Just (IntSet.findMin (vtSet t)) else Nothing
        compOf t v = vtSet t == IntSet.delete v (famDomOf (vtType t))
    case (sing a,sing b) of
        (Just va,Just vb) | va == vb -> return (k,va,Just True,True)
        (Nothing,Nothing) -> do
            -- both complements of the same value
            let cand = famDomOf (vtType a) `IntSet.difference` vtSet a
            guard (IntSet.size cand == 1)
            let v = IntSet.findMin cand
            guard (compOf b v)
            return (k,v,Just False,True)
        (Just va,Nothing) | compOf b va -> return (k,va,Nothing,True)   -- x=v & y/=v
        (Nothing,Just vb) | compOf a vb -> return (k,vb,Nothing,False)  -- x/=v & y=v
        _ -> mzero

-- | Collapse complete one-hot equality families among a conjunction's conjuncts into native cross-trace equality atoms @{x = y}@; return (collapsed atoms, untouched conjuncts).
recognizeEqFamilies :: [Bexpr] -> ([Bexpr],[Bexpr])
recognizeEqFamilies conjs = (map famEqAtom (Map.keys ok), rest ++ concatMap (map snd) (Map.elems bad))
  where
    classify c = maybe (Right c) Left $ case c of
        Bopn Por (HashSet.toList -> [d1,d2]) -> do
            (k1,v1,s1) <- gadget d1
            (k2,v2,s2) <- gadget d2
            guard (k1 == k2 && v1 == v2 && s1 /= s2)
            return (k1,(v1,c))
        Bop2 Pequiv l r -> do
            (k,v,Just True,_) <- famPair l r
            return (k,(v,c))
        _ -> mzero
    gadget (Bopn Pand (HashSet.toList -> [l,r])) = do
        (k,v,Just shape,_) <- famPair l r
        return (k,v,shape)
    gadget _ = mzero
    (fams,rest) = partitionEithers (map classify conjs)
    grouped = Map.fromListWith (++) [ (k,[vc]) | (k,vc) <- fams ]
    (ok,bad) = Map.partitionWithKey (\k vcs -> famComplete k (IntSet.fromList (map fst vcs))) grouped

-- | One conjunct of cover evidence for value @v@:
--
--       x in D\{v}  |  y1 in {v}  |  ...  |  yn in {v}
--
-- i.e. the unrolled "if x = v then some y_i equals v". Returns the family key (x and the y's),
-- the value, and the original conjunct.
coverConj :: Bexpr -> Maybe (((DualPident,VarType),[(DualPident,VarType)]),Int,Bexpr)
coverConj c@(Bopn Por (HashSet.toList -> ds)) = do
    ts <- mapM vTest ds
    let sing t = if IntSet.size (vtSet t) == 1 then Just (IntSet.findMin (vtSet t)) else Nothing
        singles = [ (t,v) | t <- ts, Just v <- [sing t] ]
    guard (Prelude.not (null singles))
    let v = snd (head singles)
    guard (all ((== v) . snd) singles)
    let comps = [ t | t <- ts, isNothing (sing t)
                    , vtSet t == IntSet.delete v (famDomOf (vtType t)) ]
    guard (length comps == 1 && length singles + 1 == length ts)
    let x = head comps
        ys = map fst singles
    dx <- famDimOf (vtVar x)
    dys <- mapM (famDimOf . vtVar) ys
    guard (all (/= dx) dys)
    return ((((vtVar x,vtType x)), List.sortOn (show . fst) [ (vtVar y,vtType y) | y <- ys ]),v,c)
coverConj _ = Nothing

-- | Collapse per-value cover families in a conjunction.
recognizeCoverFamilies :: [Bexpr] -> ([Bexpr],[Bexpr])
recognizeCoverFamilies conjs = (map mk (Map.toList fam), rest ++ concatMap (map snd) (Map.elems solo))
  where
    classify c = maybe (Right c) (\(k,v,e) -> Left (k,(v,e))) (coverConj c)
    (fams,rest) = partitionEithers (map classify conjs)
    grouped = Map.fromListWith (++) [ (k,[ve]) | (k,ve) <- fams ]
    -- a lone conjunct is not a family; collapsing it would only rename it
    (fam,solo) = Map.partition ((>= 2) . length) grouped
    mk (((xn,xt),ys),ves) =
        let s = IntSet.fromList (map fst ves)
            outside = famDomOf xt `IntSet.difference` s
            oa = [ Bop1 Patom (Bop2 Pin (Bvar xn xt) (Bints outside)) | Prelude.not (IntSet.null outside) ]
            eqs = [ Bop1 Patom (Bop2 Peq (Bvar yn yt) (Bvar xn xt)) | (yn,yt) <- ys ]
        in Bopn Por (HashSet.fromList (oa ++ eqs))

-- | Collapse complete one-hot inequality families among a disjunction's disjuncts into a negated native equality atom @!{x = y}@; return (collapsed atoms, untouched disjuncts).
recognizeNeqFamilies :: [Bexpr] -> ([Bexpr],[Bexpr])
recognizeNeqFamilies disjs = (map mkNeq (Map.keys ok), rest ++ concatMap (map snd) (Map.elems bad))
  where
    -- One disjunct of inequality evidence.
    classify d = maybe (Right d) Left $ case d of
        Bopn Pand (HashSet.toList -> [l,r]) -> do
            (k,v,Nothing,orient) <- famPair l r
            return (k,((v,Just orient),d))
        Bop1 Pnot (Bop2 Pequiv l r) -> do
            (k,v,Just True,_) <- famPair l r
            return (k,((v,Nothing),d))
        _ -> mzero
    (fams,rest) = partitionEithers (map classify disjs)
    grouped = Map.fromListWith (++) [ (k,[vc]) | (k,vc) <- fams ]
    -- a value v is covered by one whole-xor disjunct, or by BOTH half-xor orientations
    covered vcs =
        let vs = map fst vcs
            both v = ((v,Nothing) `elem` vs)
                  || (((v,Just True) `elem` vs) && ((v,Just False) `elem` vs))
        in IntSet.fromList [ v | (v,_) <- vs, both v ]
    -- every classified disjunct must belong to a covered value, else leave the family alone
    (ok,bad) = Map.partitionWithKey
        (\k vcs -> let cov = covered vcs
                   in famComplete k cov && all (\((v,_),_) -> IntSet.member v cov) vcs)
        grouped
    mkNeq k = bnot (famEqAtom k)

-- | Collapse a per-value unrolling of a cross-trace order comparison into one relational atom.
recognizeOrderFamilies :: [Bexpr] -> ([Bexpr],[Bexpr])
recognizeOrderFamilies disjs = go (Map.toList grouped) [] disjs
  where
    singletonOf t = if IntSet.size (vtSet t) == 1 then Just (IntSet.findMin (vtSet t)) else Nothing
    key x y = ((vtVar x, vtType x), (vtVar y, vtType y))

    -- every reading of a disjunct as "x is pinned to v, y is confined to S_v"
    interps d = case d of
        Bopn Pand (HashSet.toList -> [l,r]) ->
            case (vTest l, vTest r) of
                (Just a, Just b)
                    | Just da <- famDimOf (vtVar a), Just db <- famDimOf (vtVar b), da /= db ->
                        [ (key a b,(v,vtSet b,d)) | Just v <- [singletonOf a] ]
                     ++ [ (key b a,(v,vtSet a,d)) | Just v <- [singletonOf b] ]
                _ -> []
        _ -> []
    grouped = Map.fromListWith (++) [ (k,[e]) | (k,e) <- concatMap interps disjs ]

    bareFor (xk,_) avail =
        [ (v,d) | d <- avail, Just t <- [vTest d], (vtVar t, vtType t) == xk
                , Just v <- [singletonOf t] ]

    relFun Pleq = (<=)
    relFun Plt  = (<)
    relFun Pgeq = (>=)
    relFun Pgt  = (>)
    relFun _    = \_ _ -> False

    go [] acc leftover = (acc, leftover)
    go ((k@((_,tx),(_,ty)), es) : ks) acc leftover =
        case tryFamily k es leftover of
            Just (o,used) -> go ks (mkOrd k o : acc) (leftover List.\\ used)
            Nothing       -> go ks acc leftover
      where
        tryFamily _ entries avail = do
            -- only disjuncts still unclaimed by an earlier family may be used
            let ents  = [ e | e@(_,_,d) <- entries, d `elem` avail ]
                bares = bareFor k avail
                byV   = Map.fromListWith (++) $ [ (v,[(sv,d)]) | (v,sv,d) <- ents ]
                                             ++ [ (v,[(famDomOf ty,d)]) | (v,d) <- bares ]
                dx    = famDomOf tx
                dy    = famDomOf ty
            -- exactly one reading per value, covering dom(x)
            guard (Map.keysSet byV == Set.fromList (IntSet.toList dx))
            let pick o = mapM (\(v,cands) ->
                                 case [ d | (sv,d) <- cands, sv == IntSet.filter (\w -> relFun o w v) dy ] of
                                     (d:_) -> Just d
                                     []    -> Nothing)
                              (Map.toList byV)
            case [ (o,ds) | o <- [Pleq,Plt,Pgeq,Pgt], Just ds <- [pick o] ] of
                ((o,ds):_) -> Just (o, List.nub ds)
                []         -> Nothing

    -- the family is @OR_v (x=v & y REL v)@, i.e. @y REL x@
    mkOrd ((x,tx),(y,ty)) o = Bop1 Patom (Bop2 o (Bvar y ty) (Bvar x tx))
