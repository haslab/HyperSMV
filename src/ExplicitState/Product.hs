module ExplicitState.Product where

import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.Hashable as Hashable

import Error
import Utils
import Smv.Syntax
import ExplicitState.Syntax

--productExplicitStateSystem :: (Ord a,Ord b) => ExplicitStateSystem na a -> ExplicitStateSystem nb b -> ExplicitStateSystem (Either na nb) (a,b)
--productExplicitStateSystem s1 s2 = ExplicitStateSystem vars2 inits2 states2
--    where
--    vars2 = V.map (Left >< id) (exp_vars s1) V.++ V.map (Right >< id) (exp_vars s2)
--    inits2 = setProduct (exp_inits s1) (exp_inits s2)
--    states2 = buildStates (Set.toList inits2) Map.empty
--    
--    --buildStates :: [(a,b)] -> Map (a,b) ([Either Int Bool],Set (a,b)) -> Map (a,b) ([Either Int Bool],Set (a,b))
--    buildStates [] acc = acc
--    buildStates (x@(i,j):xs) acc = case Map.lookup x acc of
--        Just _ -> buildStates xs acc
--        Nothing -> buildStates (Set.toList ijnexts ++ xs) (Map.insert x (ival UV.++ jval,ijnexts) acc)
--      where
--        Just (ival,inexts) = Map.lookup i (exp_states s1)
--        Just (jval,jnexts) = Map.lookup j (exp_states s2)
--        ijnexts = setProduct inexts jnexts
--
--productNExplicitStateSystem :: Ord a => [(String,ExplicitStateSystem Pident)] -> ExplicitStateSystem Pident [a]
--productNExplicitStateSystem = productNExplicitStateSystem' . map mk
--    where
--    mk :: Ord a => (String,ExplicitStateSystem Pident a) -> ExplicitStateSystem Pident [a]
--    mk (dim,s) = mapExplicitStateSystem (\n -> addDimPident n $ mkQuantDim dim) (:[]) s
--    
--    productNExplicitStateSystem' :: Ord a => [ExplicitStateSystem Pident [a]] -> ExplicitStateSystem Pident [a]
--    productNExplicitStateSystem' [x] = x
--    productNExplicitStateSystem' (x1:x2:xs) = productNExplicitStateSystem' (x12:xs)
--        where
--        x12 = mapExplicitStateSystem (either id id) (uncurry (++)) $ productExplicitStateSystem x1 x2

productNExplicitStates :: (Hashable base,UV.Unbox base) => [(String,ExplicitStateSystem Pident base)] -> ExplicitStates Pident base
productNExplicitStates exps = ExplicitStates varsN valuesN
    where
    addDim d vs = V.map (\(n,t) -> (addDimPident n $ mkQuantDim d,t)) vs
    varsN = foldl (V.++) V.empty $ map (\(dim,s) -> addDim dim (exp_vars s)) exps
    initsN = intSetNProductHash $ map (exp_inits . snd) exps
    valuesN = buildValues initsN HashSet.empty HashSet.empty
    
--    buildValues :: HashSet [Int] -> HashSet [Int] -> HashSet (Values base) -> HashSet (Values base)
    buildValues xs dones acc = case isConsHashSet xs of
        Nothing -> acc
        Just (is,ys) -> if HashSet.member is dones
            then buildValues ys dones acc
            else let (valsN,nextsN) = unzip $ map (\(i,(_,exp)) -> unsafeIntLookupNote ("productNExplicitStates "++show i) i (exp_states exp)) $ zip is exps
                     vals = UV.concat valsN
                     nexts = intSetNProductHash nextsN
                 in buildValues (ys `HashSet.union` nexts) (HashSet.insert is dones) (HashSet.insert vals acc)
        
productNExplicitStatesView :: (Hashable base,UV.Unbox base) => (String -> Int -> Int) -> [(String,ExplicitStateSystem Pident base)] -> ExplicitStatesView Pident base
productNExplicitStatesView colMapper exps = ExplicitStatesView varsN valuesN
    where
    addDim d vs acc = V.ifoldl (\m i (n,t) -> IntMap.insert (colMapper d i) (addDimPident n $ mkQuantDim d,t) m) acc vs
    varsN = foldl (\acc (dim,s) -> addDim dim (exp_vars s) acc) IntMap.empty exps
    initsN = intSetNProductHash $ map (exp_inits . snd) exps
    valuesN = buildValuesView initsN HashSet.empty HashSet.empty
    
--    buildValuesView :: HashSet [Int] -> HashSet [Int] -> HashSet (ValuesView base) -> HashSet (ValuesView base)
    buildValuesView xs dones acc = case isConsHashSet xs of
        Nothing -> acc
        Just (is,ys) -> if HashSet.member is dones
            then buildValuesView ys dones acc
            else let (valsN,nextsN) = unzip $ map (\(i,(s,exp)) -> let (vs,nexts) = unsafeIntLookupNote "productNExplicitStatesView" i (exp_states exp) in ((s,vs),nexts)) $ zip is exps
                     vals = concatValuesToView valsN
                     nexts = intSetNProductHash nextsN
                 in buildValuesView (ys `HashSet.union` nexts) (HashSet.insert is dones) (HashSet.insert vals acc)

--    concatValuesToView :: [(String,Values base)] -> ValuesView base
    concatValuesToView = foldl go IntMap.empty
        where
        go (m) (s,vs) = (UV.ifoldl (\m i x -> IntMap.insert (colMapper s i) x m) m vs)

-- performs a filtering of the original explicit system using the NBA constraints
-- returns a subset of the original explicit system, with the same variables
productExplicitStateSystemNBA :: ExplicitStateSystem n base -> ExplicitStateNBA base -> ExplicitStateSystem n base
productExplicitStateSystemNBA sys nba = ExplicitStateSystem vars inits' accepting' states'
    where
    vars = exp_vars sys
    inits = exp_inits sys
    states = exp_states sys
    inits2 = exp_nba_inits nba
    trans2 = exp_nba_transitions nba
    (_,newstates) = buildStates (Set.empty,IntMap.empty) (intSetProduct inits inits2) 
    newstatesSet = IntMap.keysSet newstates
    inits' = IntSet.intersection inits newstatesSet
    states' = IntSet.foldl insert IntMap.empty newstatesSet
    insert acc i = case IntMap.lookup i states of
        Nothing -> acc
        Just (vals,nexts) -> IntMap.insert i (vals,IntSet.intersection nexts newstatesSet) acc
    newaccepts = IntMap.keysSet (IntMap.filter id newstates)
    accepting' = if newaccepts == newstatesSet then Nothing else Just newaccepts
    
    buildStates :: (Set (Int,Int),IntMap IsAccepting) -> Set (Int,Int) -> (Set (Int,Int),IntMap IsAccepting)
    buildStates = Set.foldl buildState
    
    buildState :: (Set (Int,Int),IntMap IsAccepting) -> (Int,Int) -> (Set (Int,Int),IntMap IsAccepting)
    buildState acc@(dones,news) ij | Set.member ij dones = acc
    buildState (dones,news) ij@(i,j) = case (IntMap.lookup i states,IntMap.lookup j trans2) of
        (Just (vals_i,nexts_i),Just trans_j) -> 
            let trans_j' = IntMap.filter ((\p -> p vals_i) . snd) trans_j
                accept_i = isAcceptingExplicitState i sys && any fst trans_j
            in buildStates (Set.insert ij dones,IntMap.insertWith (||) i accept_i news) (intSetProduct nexts_i (IntMap.keysSet trans_j'))
        otherwise -> (dones,news)
        

        

