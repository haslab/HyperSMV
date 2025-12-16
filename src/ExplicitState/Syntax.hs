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
import qualified Data.IntMap.Internal as IntMap
import Safe
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.Vector.Instances
import Data.Hashable as Hashable
import GHC.Generics
import Control.Monad.State (State(..))
import qualified Control.Monad.State as State
import Control.Monad
import Data.Maybe
import Prettyprinter

import Utils
import Smv.Syntax
import Smv.Typing
import Smv.Packed
import Smv.Pretty
import Pretty

--import Debug.Trace as Trace

type Values base = UV.Vector base

data ExplicitStateSystem n base = ExplicitStateSystem
    { exp_vars :: V.Vector (n,VarType) -- int or bool
    , exp_inits :: IntSet
    , exp_accepting :: Maybe IntSet
    , exp_states :: IntMap (Values base,IntSet)
    } deriving (Eq,Ord,Show,Generic)

exp_packedPvars :: ExplicitStateSystem Pident base -> PackedPvars
exp_packedPvars = Map.map fromVarType . Map.fromList . V.toList . exp_vars

exp_varindices :: Ord n => ExplicitStateSystem n base -> Map n (Int,VarType)
exp_varindices s = Map.fromList $ map (\(i,(n,t)) -> (n,(i,t))) $ zip [0..] $ V.toList $ exp_vars s

exp_state :: ExplicitStateSystem n base -> Int -> (Values base,IntSet)
exp_state s i = unsafeIntLookupNote "exp_state" i (exp_states s)

emptyExplicitStateSystem :: ExplicitStateSystem n base
emptyExplicitStateSystem = ExplicitStateSystem V.empty IntSet.empty (Just IntSet.empty) IntMap.empty

sizeExplicitStateSystem :: ExplicitStateSystem n base -> Int
sizeExplicitStateSystem s = IntMap.size (exp_states s)
    
mapExplicitStateSystem :: (na -> nb) -> ExplicitStateSystem na base -> ExplicitStateSystem nb base
mapExplicitStateSystem f (ExplicitStateSystem vs is as ss) = ExplicitStateSystem vs' is as ss
    where
    vs' = V.map (f >< id) vs

isTotalExplicitStateSystem :: ExplicitStateSystem n base -> Bool
isTotalExplicitStateSystem s = IntSet.null $ deadlocksExplicitStateSystem s

deadlocksExplicitStateSystem :: ExplicitStateSystem n base -> IntSet
deadlocksExplicitStateSystem s = IntMap.keysSet $ IntMap.filter (IntSet.null . snd) (exp_states s)

removeDeadlockExplicitStateSystem :: ExplicitStateSystem n base -> ExplicitStateSystem n base
removeDeadlockExplicitStateSystem s = if IntSet.null deads
    then ExplicitStateSystem (exp_vars s) (IntSet.intersection lives $ exp_inits s) (fmap (IntSet.intersection lives) $ exp_accepting s) (exp_states s)
    else removeDeadlockExplicitStateSystem (s { exp_states = IntMap.map (\(vs,nexts) -> (vs,IntSet.intersection (IntSet.difference nexts deads) lives)) ts'})
  where
    (IntMap.keysSet -> deads,ts') = IntMap.partition (IntSet.null . snd) (exp_states s)
    lives = IntMap.keysSet (exp_states s)

data PartitionState = PartitionState { nextPartition :: Int, partitionIds :: IntMap Int, partitionMap :: IntMap IntSet }
    deriving (Eq,Ord,Show)

-- merges states up to bissimulation
projectExplicitStateSystem :: (Hashable base,UV.Unbox base,Ord base,Ord n,Pretty n) => Set n -> ExplicitStateSystem n base -> (ExplicitStateSystem n base,IntMap Int)
projectExplicitStateSystem ns s = (restateExplicitStateSystem renames s',renames)
    where
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
        (pvals,accepting)
        
    -- iteratively split partitions
    partitionMap0 = IntMap.fromList $ zip [0..] partitions0
    partitionIds0 = IntMap.foldlWithKey (\acc p is -> IntSet.foldl (\acc i -> IntMap.insert i p acc) acc is) IntMap.empty partitionMap0
    st0 = PartitionState (IntMap.size partitionMap0) partitionIds0 partitionMap0
    partitions = State.evalState splitPartitions st0
    splitPartitions :: State PartitionState [IntSet]
    splitPartitions = do
        st <- State.get
        let ps = partitionMap st
        case headMay (catMaybes $ map (splitPartition st) $ IntMap.toList ps) of
            Nothing -> return $ IntMap.elems ps
            Just (pi,p') -> do
                let next = nextPartition st
                let ps' = zip [next..] p'
                let ps'' = IntMap.fromList ps'
                let next' = IntMap.size ps'' + next
                let ids' = foldl (\acc (pj,js) -> IntSet.foldl (\acc j -> IntMap.insert j pj acc) acc js) (partitionIds st) ps'
                let map' = IntMap.union ps'' (IntMap.delete pi $ partitionMap st)
                State.put $ PartitionState next' ids' map'
                splitPartitions
    
    splitPartition :: PartitionState -> (Int,IntSet) -> Maybe (Int,[IntSet])
    splitPartition st (pi,is) = do
        guard $ IntSet.size is > 1 -- more than one state
        let ps = groupIntSetOn (nextPartitionsOfState st) is
        guard $ Map.size ps > 1 -- more than one set of target blocks
        return (pi,Map.elems ps)
    
    nextPartitionsOfState :: PartitionState -> Int -> IntSet
    nextPartitionsOfState st i = IntSet.map partitionOfState nexts_i
        where
        (_,nexts_i) = unsafeIntLookupNote "nextPartitionsOfState" i states'
        partitionOfState j = unsafeIntLookupNote "partitionOfState" j (partitionIds st)
    
    -- rename explicit state using final partition
    renames = foldl renamePartition IntMap.empty partitions
    renamePartition acc is = case IntSet.toList is of
        [] -> acc
        (i:js) -> foldl (\acc j -> IntMap.insert j i acc) (IntMap.insert i i acc) js

restateExplicitStateSystem :: IntMap Int -> ExplicitStateSystem n base -> ExplicitStateSystem n base
restateExplicitStateSystem m s = ExplicitStateSystem (exp_vars s) inits' accepting' states'
    where
    newstates = IntMap.intersection (exp_states s) (flipIntMapInt m)
    mapStates = IntSet.map mapState
    mapState k = unsafeIntLookupNote "restateExplicitState" k m
    inits' = mapStates (exp_inits s)
    accepting' = fmap mapStates (exp_accepting s)
    states' = IntMap.map (id >< mapStates) newstates

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

data ExplicitStates n base = ExplicitStates
    { expss_vars :: V.Vector (n,VarType) -- int or bool
    , expss_vals :: HashSet (Values base)
    } deriving (Eq,Ord,Show)

getExplicitStates :: (Hashable base,UV.Unbox base) => ExplicitStateSystem n base -> ExplicitStates n base
getExplicitStates s = ExplicitStates vars' vals'
    where
    vars' = exp_vars s
    vals' = HashSet.fromList $ map fst $ IntMap.elems $ exp_states s

sizeExplicitStates :: ExplicitStates n base -> Int
sizeExplicitStates s = HashSet.size (expss_vals s)

projectExplicitStates :: (Hashable base,UV.Unbox base,Ord n) => Set n -> ExplicitStates n base -> ExplicitStates n base
projectExplicitStates ns s = projectExplicitStatesIx is s
    where
    m = vectorIndices (V.map fst $ expss_vars s)
    is = IntSet.fromList $ map (\n -> unsafeLookupNote "projectExplicitStates" n m) $ Set.toList ns

projectExplicitStatesIx :: (Hashable base,UV.Unbox base) => IntSet -> ExplicitStates n base -> ExplicitStates n base
projectExplicitStatesIx is s = ExplicitStates vars' vals'
    where
    vars = expss_vars s
    vars' = V.ifilter (\i n -> IntSet.member i is) vars
    vals' = HashSet.map projetValues (expss_vals s)
    projetValues vs = UV.ifilter (\i _ -> IntSet.member i is) vs

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
    
--    extendVal :: Values base -> Values base -> Int
    extendVal old prev = if i < oldsize
        then uvIndex "extendExplicitStates" old i
        else let ((n,ty),eval) = vIndex "extendExplicitStates" ext (i - oldsize) in eval prev
      where
        i = UV.length prev 

type ValuesView base = IntMap base -- map from column index to value

data ExplicitStatesView n base = ExplicitStatesView
    { expsv_vars :: IntMap (n,VarType) -- map of column indexes to column description
    , expsv_vals :: HashSet (ValuesView base) -- set of rows,
    } deriving (Eq,Ord,Show)

projectExplicitStatesView :: Hashable base => IntSet -> ExplicitStatesView n base -> ExplicitStatesView n base
projectExplicitStatesView is s = ExplicitStatesView vars' vals'
    where
    vars' = project (expsv_vars s)
    vals' = HashSet.map project (expsv_vals s)
    project :: IntMap a -> IntMap a
    project = IntMap.filterWithKey (\k _ -> IntSet.member k is)

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

isAcceptingExplicitState :: Int -> ExplicitStateSystem n base -> Bool
isAcceptingExplicitState i s = case exp_accepting s of
    Nothing -> True
    Just js -> IntSet.member i js

type IsAccepting = Bool 

data ExplicitStateNBA base = ExplicitStateNBA
    { exp_nba_inits :: IntSet -- initial states
    , exp_nba_transitions :: IntMap (IntMap (IsAccepting,Values base -> Bool))
    } deriving (Generic)



    






