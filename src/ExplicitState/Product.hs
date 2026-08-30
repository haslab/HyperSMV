-- | Product construction of explicit-state systems with NBAs.
module ExplicitState.Product where

import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Set (Set(..))
import qualified Data.Set as Set
import qualified Data.HashSet as HashSet
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.Hashable as Hashable

import Utils
import Smv.Syntax
import ExplicitState.Syntax

-- | Product of several systems' states into one flat row set.
productNExplicitStates :: (Hashable base,UV.Unbox base) => [(String,ExplicitStateSystem Pident base)] -> ExplicitStates Pident base
productNExplicitStates exps = ExplicitStates varsN valuesN
    where
    addDim d vs = V.map (\(n,t) -> (addDimPident n $ mkQuantDim d,t)) vs
    varsN = foldl (V.++) V.empty $ map (\(dim,s) -> addDim dim (exp_vars s)) exps
    initsN = intSetNProductHash $ map (exp_inits . snd) exps
    valuesN = buildValues initsN HashSet.empty HashSet.empty
    
    buildValues xs dones acc = case isConsHashSet xs of
        Nothing -> acc
        Just (is,ys) -> if HashSet.member is dones
            then buildValues ys dones acc
            else let (valsN,nextsN) = unzip $ map (\(i,(_,exp)) -> unsafeIntLookupNote ("productNExplicitStates "++show i) i (exp_states exp)) $ zip is exps
                     vals = UV.concat valsN
                     nexts = intSetNProductHash nextsN
                 in buildValues (ys `HashSet.union` nexts) (HashSet.insert is dones) (HashSet.insert vals acc)
        
-- | Product of several systems' states into one sparse row set.
productNExplicitStatesView :: (Hashable base,UV.Unbox base) => (String -> Int -> Int) -> [(String,ExplicitStateSystem Pident base)] -> ExplicitStatesView Pident base
productNExplicitStatesView colMapper exps = ExplicitStatesView varsN valuesN
    where
    addDim d vs acc = V.ifoldl (\m i (n,t) -> IntMap.insert (colMapper d i) (addDimPident n $ mkQuantDim d,t) m) acc vs
    varsN = foldl (\acc (dim,s) -> addDim dim (exp_vars s) acc) IntMap.empty exps
    initsN = intSetNProductHash $ map (exp_inits . snd) exps
    valuesN = buildValuesView initsN HashSet.empty HashSet.empty
    
    buildValuesView xs dones acc = case isConsHashSet xs of
        Nothing -> acc
        Just (is,ys) -> if HashSet.member is dones
            then buildValuesView ys dones acc
            else let (valsN,nextsN) = unzip $ map (\(i,(s,exp)) -> let (vs,nexts) = unsafeIntLookupNote "productNExplicitStatesView" i (exp_states exp) in ((s,vs),nexts)) $ zip is exps
                     vals = concatValuesToView valsN
                     nexts = intSetNProductHash nextsN
                 in buildValuesView (ys `HashSet.union` nexts) (HashSet.insert is dones) (HashSet.insert vals acc)

    concatValuesToView = foldl go IntMap.empty
        where
        go (m) (s,vs) = (UV.ifoldl (\m i x -> IntMap.insert (colMapper s i) x m) m vs)

-- | Exact restriction of an explicit system by an NBA.
productExplicitStateSystemNBAExact :: ExplicitStateSystem n base -> ExplicitStateNBA base -> ExplicitStateSystem n base
productExplicitStateSystemNBAExact sys nba =
    case productExplicitStateSystemNBAExactBounded maxBound sys nba of
        Just r -> r
        Nothing -> error "productExplicitStateSystemNBAExact: budget maxBound cannot be exceeded"

-- | Exact restriction, giving up (returning 'Nothing') once the product exceeds @budget@ states.
productExplicitStateSystemNBAExactBounded :: Int -> ExplicitStateSystem n base -> ExplicitStateNBA base -> Maybe (ExplicitStateSystem n base)
productExplicitStateSystemNBAExactBounded budget sys nba = case reachWithin budget of
    Nothing -> Nothing
    Just _ -> Just (removeDeadlockExplicitStateSystem (ExplicitStateSystem (exp_vars sys) inits' accepting' states'))
    where
    states = exp_states sys
    trans2 = exp_nba_transitions nba

    flagBySource :: Bool
    flagBySource = all ok (IntMap.elems states)
        where
        ok (vals_i,_) = all (agree . enabledFlags vals_i) (IntMap.elems trans2)
        agree bs = case bs of { [] -> True ; (b:bs') -> all (== b) bs' }

    enabledFlags :: Values base -> IntMap (IsAccepting,Values base -> Bool) -> [IsAccepting]
    enabledFlags vals_i trans_j = [ acc | (acc,p) <- IntMap.elems trans_j, p vals_i ]

    accAtSource :: Int -> Int -> Bool
    accAtSource i j = case (IntMap.lookup i states, IntMap.lookup j trans2) of
        (Just (vals_i,_), Just trans_j) -> case enabledFlags vals_i trans_j of
            (b:_) -> b
            []    -> False
        _ -> False

    hasSysAcc :: Bool
    hasSysAcc = case exp_accepting sys of { Nothing -> False; Just _ -> True }

    sysAccepting :: Int -> Bool
    sysAccepting i = isAcceptingExplicitState i sys

    starts :: [(Int,Int,Bool,Int)]
    starts =
        [ (i,j,False,0)
        | i <- IntSet.toList (exp_inits sys)
        , IntMap.member i states
        , j <- IntSet.toList (exp_nba_inits nba)
        ]

    nbaAcc :: (Int,Int,Bool,Int) -> Bool
    nbaAcc (i,j,b,_) = if flagBySource then accAtSource i j else b

    succsOf :: (Int,Int,Bool,Int) -> [(Int,Int,Bool,Int)]
    succsOf x@(i,j,_,ph) = case (IntMap.lookup i states,IntMap.lookup j trans2) of
        (Just (vals_i,nexts_i),Just trans_j) ->
            [ (i',j',flag',phase')
            | (j',(acc,p)) <- IntMap.toList trans_j
            , p vals_i -- only edges enabled by the CURRENT state's valuation
            , i' <- IntSet.toList nexts_i
            , IntMap.member i' states -- never emit a successor we cannot look up (no dangling ids)
            , let flag' = if flagBySource then False else acc
            , let phase' = nextPhase (i',j',flag',ph)
            ]
        _ -> []
      where
        nextPhase (i',j',flag',p0)
            | not hasSysAcc = 0
            | p0 == 0 = if sysAccepting i' then 1 else 0
            | otherwise = if nbaAcc (i',j',flag',p0) then 0 else 1

    reach :: Set (Int,Int,Bool,Int)
    reach = maybe (go Set.empty starts) id (reachWithin maxBound)
        where
        go done [] = done
        go done (x:xs)
            | Set.member x done = go done xs
            | otherwise = go (Set.insert x done) (succsOf x ++ xs)

    reachWithin :: Int -> Maybe (Set (Int,Int,Bool,Int))
    reachWithin budget = go Set.empty starts
        where
        go done [] = Just done
        go done (x:xs)
            | Set.member x done = go done xs
            | Set.size done >= budget = Nothing
            | otherwise = go (Set.insert x done) (succsOf x ++ xs)

    ids :: Map (Int,Int,Bool,Int) Int
    ids = Map.fromList $ zip (Set.toList reach) [0..]

    idOf :: (Int,Int,Bool,Int) -> Int
    idOf x = unsafeLookupNote "productExplicitStateSystemNBAExact" x ids

    inits' = IntSet.fromList $ map idOf $ filter (`Set.member` reach) starts

    states' = IntMap.fromList
        [ (idOf x,(vals_i,IntSet.fromList $ map idOf $ succsOf x))
        | x@(i,_,_,_) <- Set.toList reach
        , Just (vals_i,_) <- [IntMap.lookup i states]
        ]

    accepts = IntSet.fromList
        [ idOf x
        | x@(_,_,_,ph) <- Set.toList reach
        , if hasSysAcc then ph == 1 && nbaAcc x else nbaAcc x
        ]
    accepting' = if accepts == IntMap.keysSet states' then Nothing else Just accepts

