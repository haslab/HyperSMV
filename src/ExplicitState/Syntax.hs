-- | Core explicit-state-system representation and its bisimulation quotient/deadlock/extension operations.
module ExplicitState.Syntax where

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Safe
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.Hashable as Hashable
import Data.Vector.Instances ()
import Control.DeepSeq (NFData)
import GHC.Generics
import Prettyprinter

import Utils
import Smv.Syntax
import Smv.Typing
import Smv.Packed

-- | A row of column values.
type Values base = UV.Vector base

-- | An explicit-state transition system.
data ExplicitStateSystem n base = ExplicitStateSystem
    { exp_vars :: V.Vector (n,VarType) -- int or bool
    , exp_inits :: IntSet
    , exp_accepting :: Maybe IntSet
    , exp_states :: IntMap (Values base,IntSet)
    } deriving (Eq,Ord,Show,Generic)

instance (NFData n, NFData base, UV.Unbox base) => NFData (ExplicitStateSystem n base)

-- | The system's variables as packed SMV var types.
exp_packedPvars :: ExplicitStateSystem Pident base -> PackedPvars
exp_packedPvars = Map.map fromVarType . Map.fromList . V.toList . exp_vars

-- | Map each variable name to its column index and type.
exp_varindices :: Ord n => ExplicitStateSystem n base -> Map n (Int,VarType)
exp_varindices s = Map.fromList $ map (\(i,(n,t)) -> (n,(i,t))) $ zip [0..] $ V.toList $ exp_vars s

-- | Look up a state by id.
exp_state :: ExplicitStateSystem n base -> Int -> (Values base,IntSet)
exp_state s i = unsafeIntLookupNote "exp_state" i (exp_states s)

-- | The empty explicit-state system.
emptyExplicitStateSystem :: ExplicitStateSystem n base
emptyExplicitStateSystem = ExplicitStateSystem V.empty IntSet.empty (Just IntSet.empty) IntMap.empty

-- | Number of states.
sizeExplicitStateSystem :: ExplicitStateSystem n base -> Int
sizeExplicitStateSystem s = IntMap.size (exp_states s)
    
-- | Rename variables via a function.
mapExplicitStateSystem :: (na -> nb) -> ExplicitStateSystem na base -> ExplicitStateSystem nb base
mapExplicitStateSystem f (ExplicitStateSystem vs is as ss) = ExplicitStateSystem vs' is as ss
    where
    vs' = V.map (f >< id) vs

-- | Whether every state has a successor.
isTotalExplicitStateSystem :: ExplicitStateSystem n base -> Bool
isTotalExplicitStateSystem s = IntSet.null $ deadlocksExplicitStateSystem s

-- | The states with no successors.
deadlocksExplicitStateSystem :: ExplicitStateSystem n base -> IntSet
deadlocksExplicitStateSystem s = IntMap.keysSet $ IntMap.filter (IntSet.null . snd) (exp_states s)

-- | Remove deadlock states, and states left deadlocked as a result.
removeDeadlockExplicitStateSystem :: ExplicitStateSystem n base -> ExplicitStateSystem n base
removeDeadlockExplicitStateSystem s = if IntSet.null deads
    then ExplicitStateSystem (exp_vars s) (IntSet.intersection lives $ exp_inits s) (fmap (IntSet.intersection lives) $ exp_accepting s) (exp_states s)
    else removeDeadlockExplicitStateSystem (s { exp_states = IntMap.map (\(vs,nexts) -> (vs,IntSet.intersection (IntSet.difference nexts deads) lives)) ts'})
  where
    (IntMap.keysSet -> deads,ts') = IntMap.partition (IntSet.null . snd) (exp_states s)
    lives = IntMap.keysSet (exp_states s)

-- | Accumulator for building a state partition.
data PartitionState = PartitionState { nextPartition :: Int, partitionIds :: IntMap Int, partitionMap :: IntMap IntSet }
    deriving (Eq,Ord,Show)

-- | Merges states up to bisimulation, observing the PROJECTED VARIABLE VALUES.
projectExplicitStateSystem :: (Hashable base,UV.Unbox base,Ord base,Ord n,Pretty n) => Set n -> ExplicitStateSystem n base -> (ExplicitStateSystem n base,IntMap Int)
projectExplicitStateSystem = projectExplicitStateSystemBy (\_ pvals -> pvals)

-- | 'projectExplicitStateSystem' with the observation supplied by the caller.
projectExplicitStateSystemBy :: (Hashable base,UV.Unbox base,Ord base,Ord n,Pretty n,Ord key)
                             => (Int -> Values base -> key)
                             -> Set n -> ExplicitStateSystem n base
                             -> (ExplicitStateSystem n base,IntMap Int)
projectExplicitStateSystemBy obs ns s = (quotiented,renames)
    where
    -- Skip the restate when the quotient is the identity.
    quotiented
        | length partitions == IntMap.size states' = s'
        | otherwise = restateExplicitStateSystem renames s'

    s' = ExplicitStateSystem vars' (exp_inits s) (exp_accepting s) states'
        
    -- map variable names to indices
    is = IntSet.fromList $ map (\n -> fromJustNote "projectExplicitState" $ V.findIndex ((==n) . fst) (exp_vars s)) $ Set.toList ns
    vars' = V.ifilter (\i n -> IntSet.member i is) (exp_vars s)
    
    -- project states for selected vars
    states' = IntMap.map (projectVals >< id) (exp_states s)
    projectVals vals = UV.ifilter (\i _ -> IntSet.member i is) vals
        
    -- compute initial partition with equivalent states
    partitions0 = Map.elems $ groupIntMapKeysOn partitionState states'
    partitionState k (pvals,nexts) =
        let accepting = maybe True (IntSet.member k) (exp_accepting s) in
        (obs k pvals,accepting)
        
    -- Moore rounds, not single-split-and-restart.
    partitionMap0 = IntMap.fromList $ zip [0..] partitions0
    partitionIds0 = IntMap.foldlWithKey (\acc p is -> IntSet.foldl (\acc i -> IntMap.insert i p acc) acc is) IntMap.empty partitionMap0

    partitions = go partitionIds0 (IntMap.size partitionMap0)
        where
        go ids n =
            let sigOf i =
                    let (_, nexts_i) = unsafeIntLookupNote "mooreSig" i states'
                    in ( unsafeIntLookupNote "mooreSelf" i ids
                       , IntSet.map (\j -> unsafeIntLookupNote "mooreSucc" j ids) nexts_i
                       )

                -- fresh ids by first occurence in ascending state order.
                (_, ids') =
                    IntMap.foldlWithKey
                        (\(tbl, acc) i _ ->
                            let sig = sigOf i
                            in case Map.lookup sig tbl of
                                Just b -> (tbl, IntMap.insert i b acc)
                                Nothing ->
                                    let b = Map.size tbl
                                    in (Map.insert sig b tbl, IntMap.insert i b acc))
                        (Map.empty, IntMap.empty)
                        states'

                n' = IntSet.size (IntSet.fromList (IntMap.elems ids'))
            in if n' == n then
                   Map.elems (groupIntMapKeysOn (\i _ -> unsafeIntLookupNote "mooreOut" i ids) states')
               else
                   go ids' n'
    
    -- rename explicit state using final partition
    renames = foldl renamePartition IntMap.empty partitions
    renamePartition acc is = case IntSet.toList is of
        [] -> acc
        (i:js) -> foldl (\acc j -> IntMap.insert j i acc) (IntMap.insert i i acc) js

-- | Rename states according to a partition map.
restateExplicitStateSystem :: IntMap Int -> ExplicitStateSystem n base -> ExplicitStateSystem n base
restateExplicitStateSystem m s = ExplicitStateSystem (exp_vars s) inits' accepting' states'
    where
    newstates = IntMap.intersection (exp_states s) (flipIntMapInt m)
    mapStates = IntSet.map mapState
    mapState k = unsafeIntLookupNote "restateExplicitState" k m
    inits' = mapStates (exp_inits s)
    accepting' = fmap mapStates (exp_accepting s)
    states' = IntMap.map (id >< mapStates) newstates

-- | Add derived columns to every state.
extendExplicitStateSystem :: (Hashable base,UV.Unbox base,Ord n) => [((n,VarType),(Values base) -> base)] -> ExplicitStateSystem n base -> ExplicitStateSystem n base
extendExplicitStateSystem ext s = ExplicitStateSystem vars' inits' accepting' states'
    where
    vars = exp_vars s
    vars' = vars V.++ V.fromList (map fst ext)
    inits' = exp_inits s
    accepting' = exp_accepting s
    states' = IntMap.map (extendVals >< id) (exp_states s)
    extendVals vs = vs UV.++ UV.fromList (map (extendVal vs) ext)
    extendVal old ((n,ty),eval) = eval old

-- | A system's states as a flat set of value rows.
data ExplicitStates n base = ExplicitStates
    { expss_vars :: V.Vector (n,VarType) -- int or bool
    , expss_vals :: HashSet (Values base)
    } deriving (Eq,Ord,Show)

-- | Extract a system's states as a flat row set.
getExplicitStates :: (Hashable base,UV.Unbox base) => ExplicitStateSystem n base -> ExplicitStates n base
getExplicitStates s = ExplicitStates vars' vals'
    where
    vars' = exp_vars s
    vals' = HashSet.fromList $ map fst $ IntMap.elems $ exp_states s

-- | Number of distinct rows.
sizeExplicitStates :: ExplicitStates n base -> Int
sizeExplicitStates s = HashSet.size (expss_vals s)

-- | Restrict rows to the given variables.
projectExplicitStates :: (Hashable base,UV.Unbox base,Ord n) => Set n -> ExplicitStates n base -> ExplicitStates n base
projectExplicitStates ns s = projectExplicitStatesIx is s
    where
    m = vectorIndices (V.map fst $ expss_vars s)
    is = IntSet.fromList $ map (\n -> unsafeLookupNote "projectExplicitStates" n m) $ Set.toList ns

-- | Restrict rows to the given column indices.
projectExplicitStatesIx :: (Hashable base,UV.Unbox base) => IntSet -> ExplicitStates n base -> ExplicitStates n base
projectExplicitStatesIx is s = ExplicitStates vars' vals'
    where
    vars = expss_vars s
    vars' = V.ifilter (\i n -> IntSet.member i is) vars
    vals' = HashSet.map projetValues (expss_vals s)
    projetValues vs = UV.ifilter (\i _ -> IntSet.member i is) vs

-- | Drop the given column indices.
projectAwayExplicitStatesIx :: (Hashable base,UV.Unbox base) => IntSet -> ExplicitStates n base -> ExplicitStates n base
projectAwayExplicitStatesIx is s = if IntSet.null is then s else ExplicitStates vars' vals'
    where
    vars = expss_vars s
    vars' = V.ifilter (\i n -> not $ IntSet.member i is) vars
    vals' = HashSet.map projetValues (expss_vals s)
    projetValues vs = UV.ifilter (\i _ -> not $ IntSet.member i is) vs

-- the function that generates each element may depend on the previously-generated elements
extendExplicitStates :: (Hashable base,UV.Unbox base,Ord n) => V.Vector ((n,VarType),(Values base) -> base) -> ExplicitStates n base -> ExplicitStates n base
extendExplicitStates ext s = ExplicitStates vars' vals'
    where
    vars = expss_vars s
    vars' = vars V.++ V.map fst ext
    vals' = HashSet.map extendValues (expss_vals s)
    extendValues vs = UV.constructN (V.length vars') (extendVal vs)
    oldsize = V.length vars
    
    extendVal old prev = if i < oldsize
        then uvIndex "extendExplicitStates" old i
        else let ((n,ty),eval) = vIndex "extendExplicitStates" ext (i - oldsize) in eval prev
      where
        i = UV.length prev 

-- | A sparse row, keyed by column index.
type ValuesView base = IntMap base -- map from column index to value

-- | A row set with sparse (column-indexed) rows.
data ExplicitStatesView n base = ExplicitStatesView
    { expsv_vars :: IntMap (n,VarType) -- map of column indexes to column description
    , expsv_vals :: HashSet (ValuesView base) -- set of rows,
    } deriving (Eq,Ord,Show)

-- | Restrict a row set to the given columns.
projectExplicitStatesView :: Hashable base => IntSet -> ExplicitStatesView n base -> ExplicitStatesView n base
projectExplicitStatesView is s = ExplicitStatesView vars' vals'
    where
    vars' = project (expsv_vars s)
    vals' = HashSet.map project (expsv_vals s)
    project :: IntMap a -> IntMap a
    project = IntMap.filterWithKey (\k _ -> IntSet.member k is)

-- | Drop the given columns from a row set.
projectAwayExplicitStatesView :: Hashable base => IntSet -> ExplicitStatesView n base -> ExplicitStatesView n base
projectAwayExplicitStatesView is s = ExplicitStatesView vars' vals'
    where
    vars' = project (expsv_vars s)
    vals' = HashSet.map project (expsv_vals s)
    project :: IntMap a -> IntMap a
    project = IntMap.filterWithKey (\k _ -> not $ IntSet.member k is)

-- the function that generates each element may depend on the previously-generated elements
extendExplicitStatesView :: (Hashable base,Ord n) => [((Int,(n,VarType)),(ValuesView base) -> base)] -> ExplicitStatesView n base -> ExplicitStatesView n base
extendExplicitStatesView ext s = ExplicitStatesView vars' vals'
    where
    vars = expsv_vars s
    vars' = IntMap.union vars $ IntMap.fromList $ map fst ext
    vals' = HashSet.map extendValues (expsv_vals s)
    extendValues vs = foldl extendVal vs ext
    
    extendVal prev ((i,(n,t)),eval) = IntMap.insert i (eval prev) prev

-- | Whether a state is accepting.
isAcceptingExplicitState :: Int -> ExplicitStateSystem n base -> Bool
isAcceptingExplicitState i s = case exp_accepting s of
    Nothing -> True
    Just js -> IntSet.member i js

-- | Whether an NBA edge is accepting.
type IsAccepting = Bool 

-- | A Buchi automaton with guarded transitions.
data ExplicitStateNBA base = ExplicitStateNBA
    { exp_nba_inits :: IntSet -- initial states
    , exp_nba_transitions :: IntMap (IntMap (IsAccepting,Values base -> Bool))
    } deriving (Generic)



    






