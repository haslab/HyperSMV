-- | The explicit-state enumeration engine.
module ExplicitState.Enumerate where

import qualified Data.HashMap.Strict as HashMap
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Sequence (Seq, ViewL(..))
import qualified Data.Sequence as Seq
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Internal as IntMap
import qualified Control.Monad.Reader as Reader
import Control.Monad
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.List as List
import Data.Proxy
import Control.Monad.Trans
import Data.IORef
import qualified Control.Exception as CE

import Utils
import Smv.Syntax
import qualified Data.DD as DD
import Data.DDs (AndDDs(..),NextDDs(..),TreeDDs(..))
import qualified Data.DDs as DDs
import Transform.DD.Build
import Transform.DD.Split

-- safe because names are already sorted by DD indices
completeToState :: BuildDD dd => DD.CompleteState dd -> State dd
completeToState = UV.fromList . IntMap.elems

-- | Merge registered states with their transitions.
mergeModel :: BuildDD dd => IntSet -> IntMap (State dd) -> Transitions -> (IntSet,IntMap (DD.Vals dd,IntSet))
mergeModel inits sts ts = (IntSet.intersection inits (IntMap.keysSet states),states)
    where
    states = IntMap.merge whenL whenR whenLR sts ts
    whenL = IntMap.dropMissing 
    whenR = IntMap.dropMissing
    whenLR = IntMap.WhenMatched $ \k x y -> return $ Just (x,y)

-- | Remove deadlock states and their incoming edges.
dropDeadlockTransitions :: Transitions -> Transitions
dropDeadlockTransitions ts = if IntSet.null deads
    then ts'
    else dropDeadlockTransitions $ IntMap.map (\nexts -> IntSet.difference nexts deads) ts'
  where
    (IntMap.keysSet -> deads,ts') = IntMap.partition (IntSet.null) ts

-- | A state's full value assignment.
type State dd = DD.Vals dd
-- | Candidate states discovered but not yet registered.
type ProspectiveStates dd = Set (State dd)

-- | Enumerate and register the initial states.
initDDToStates :: (ExplicitInitDDs dd sinvar,ExplicitInitDDs dd sinit,BuildDDs dd sinvar,Monad m) => sinit -> sinvar -> DDM m (States dd)
initDDToStates e invar = do
    liftM (registerStates 0 . Set.map completeToState) $ expandPartialStates =<< initDDToStates' e invar

-- | Enumerate the initial states as partial assignments.
initDDToStates' :: (ExplicitInitDDs dd sinvar,ExplicitInitDDs dd sinit,BuildDDs dd sinvar,Monad m) => sinit -> sinvar -> DDM m (DD.PartialStates dd)
initDDToStates' inits invar = ioReader $ do
    st <- initStatesDDs inits (Set.singleton IntMap.empty)
    st' <- initStatesDDs invar st
    return st'

-- | Decision-diagram representations that can enumerate initial states.
class BuildDDs dd s => ExplicitInitDDs dd s where
    initStatesDDs :: (Monad m) => s -> DD.PartialStates dd -> DDM m (DD.PartialStates dd)
    monoDDsInit :: Integer -> s -> DDM IO s
    monoDDsInit _ = return

instance BuildDD dd => ExplicitInitDDs dd (AndDDs dd) where
    initStatesDDs (AndDDs dds) acc = foldMapCPSM (const initDDStates) acc return dds    

instance BuildDD dd => ExplicitInitDDs dd (NextDDs dd) where
    initStatesDDs (NextDDs dds) acc = foldMapCPSM (const initDDStates) acc return dds  
    
instance BuildDD dd => ExplicitInitDDs dd (TreeDDs dd) where
    monoDDsInit budget t = maybe t id <$> DDs.monoTreeDDsBounded budget t
    initStatesDDs (NodeAndDDs dds) sts = foldMultiMapCPSM (const initStatesDDs) sts return dds
    initStatesDDs (NodeOrDDs dds) sts = liftM DD.orsPartialStates $ mapM (flip initStatesDDs sts) dds
    initStatesDDs (LeafDDs sup dd) sts = initDDStates dd sts

-- | Extend a set of partial states with one diagram's satisfying assignments.
initDDStates :: (BuildDD dd,Monad m) => dd -> DD.PartialStates dd -> DDM m (DD.PartialStates dd)
initDDStates dd sts = liftM Set.unions $ traverseSet (initDDState dd) sts

-- | Extend one partial state with one diagram's satisfying assignments.
initDDState :: (BuildDD dd,Monad m) => dd -> DD.PartialState dd -> DDM m (DD.PartialStates dd)
initDDState dd st0 = ioReader $ do
    r <- Reader.ask
    DD.accum (goBranch r) (goLeaf) (Just st0) dd
  where
    goLeaf st b = if b then maybeToSet st else Set.empty
    goBranch r Nothing dd_i = V.empty
    goBranch r (Just st) dd_i = V.map (\val -> DD.insertPartialState dd_i val st) (UV.convert vals)
      where vals = runReaderIO r (DD.vals dd_i)

-- map of states and number of states
type States dd = (Map (State dd) Int,Int)
-- map of state to next state
type Transitions = IntMap IntSet

-- convert transitions to next states to transitions to previous states
reverseTransitions :: Transitions -> Transitions
reverseTransitions ts = IntMap.foldlWithKey go1 IntMap.empty ts
    where
    go1 :: Transitions -> Int -> IntSet -> Transitions
    go1 acc i js = IntSet.foldl go2 acc js
        where
        go2 :: Transitions -> Int -> Transitions
        go2 acc j = IntMap.insertWith IntSet.union j (IntSet.singleton i) acc

-- | Registered states with their transitions.
type ExplicitSystem dd = (States dd,Transitions)

-- recursively find transitions, and possibly new states
transDDToStates :: (ExplicitInitDDs dd sinvar,ExplicitTransDDs dd strans,BuildDDs dd sinvar) => strans -> sinvar -> Map Pident Int -> States dd -> DDM IO (ExplicitSystem dd)
transDDToStates e invar ns sts = do
    succF <- prepareSuccStates ns e
    let upgrade = do
            eC <- ioReader (clusterTransDDs explicitClusterBudget e)
            prepareSuccStates ns eC
    transDDToStates2 0 succF (Just upgrade) invar ns (Seq.fromList $ Map.toList $ fst sts) (sts,IntMap.empty)

-- Per-cluster node budget for `clusterTreeDDs` at the explicit site: bounds each bounded apply, so a failed merge costs at most this many nodes of wasted work.
explicitClusterBudget :: Integer
explicitClusterBudget = 65536

-- Cluster only once the enumeration has proved it will amortize the merge: clustering is a fixed up-front cost that pays back per state. 
explicitClusterAfter :: Int
explicitClusterAfter = 1024

-- (existing states,new states,next state number)
-- we can reuse previously seen states (with the same values), since we are only handling INIT/INVAR/TRANS formulas. no further state context is needed.
type States2 dd = (Map (State dd) Int,Map (State dd) Int,Int)
-- | States (existing/new split) with their transitions.
type ExplicitSystem2 dd = (States2 dd,Transitions)

-- the recursive procedure
transDDToStates2 :: (ExplicitInitDDs dd sinvar,BuildDDs dd sinvar) => Int -> (State dd -> DDM IO (DD.PartialStates dd)) -> Maybe (DDM IO (State dd -> DDM IO (DD.PartialStates dd))) -> sinvar -> Map Pident Int -> Seq (State dd,Int) -> ExplicitSystem dd -> DDM IO (ExplicitSystem dd)
-- 'Seq' rather than a list: appending to a list is quadratic here.
transDDToStates2 done succF upg invar ns (Seq.viewl -> EmptyL) acc = return acc
transDDToStates2 done succF upg invar ns (Seq.viewl -> (st,i) :< sts') acc@((acc_sts,acc_num),acc_trans) = do
    cands <- transDDToStates3 succF invar ns st
    news <- expandPartialStates cands
    let acc'@((olds',news',num'),ts') = linkNextStates i (Set.map completeToState news) acc
    -- Force the newly registered states here.
    _ <- liftIO (CE.evaluate (num' `seq` Map.size news'))
    -- Deferred clustering: the enumeration has now proved it is large enough to amortize the merge, so force the clustered successor function once and continue with it. 
    (succF',upg') <-
        case upg of
            Just act | done + 1 >= explicitClusterAfter -> do
                succC <- act
                return (succC,Nothing)
            _ -> return (succF,upg)
    transDDToStates2 (done + 1) succF' upg' invar ns (sts' Seq.>< Seq.fromList (Map.toList news')) ((Map.union olds' news',num'),ts')

-- adds new states and transitions to them
linkNextStates :: BuildDD dd => Int -> ProspectiveStates dd -> ExplicitSystem dd -> ExplicitSystem2 dd
linkNextStates i cands ((sts,num),ts) = Set.foldl' linkNextState ((sts,Map.empty,num),ts) cands
    where
    linkNextState ((olds,news,num),ts) x = case Map.lookup x olds of
        Just j -> ((olds,news,num),addTransition i j ts)
        Nothing -> ((olds,Map.insert x num news,num+1),addTransition i num $ IntMap.insert num IntSet.empty ts) -- to make sure that states with empty transitions appear in the map
  
-- | Add one edge to a transition map.
addTransition :: Int -> Int -> Transitions -> Transitions
addTransition i j ts = IntMap.insertWith IntSet.union i (IntSet.singleton j) ts
  
-- | Assign fresh ids to a set of states, starting from a given number.
registerStates :: BuildDD dd => Int -> ProspectiveStates dd -> States dd
registerStates n xs = Set.foldl' go (Map.empty,n) xs
    where
    go (ys,n) x = (Map.insert x n ys,n+1)

-- | A part flattened once for per-state cofactoring. The tree shape is fixed for the whole run, so walking the 'TreeDDs' on every cache miss just re-ran the same interpretation.
data PreparedPart dd = PLeaf !dd | PAnd ![PreparedPart dd] | POr ![PreparedPart dd]

-- | Flatten a tree of diagrams into a prepared part.
preparePart :: TreeDDs dd -> PreparedPart dd
preparePart (LeafDDs _ dd) = PLeaf dd
preparePart (NodeAndDDs m) = PAnd (map preparePart (multiMapElems m))
preparePart (NodeOrDDs m) = POr (map preparePart (multiMapElems m))

-- | Node budget for the per-part bounded collapse in 'prepareSuccStates'.
explicitPartMonoBudget :: Integer
explicitPartMonoBudget = 65536

class BuildDDs dd strans => ExplicitTransDDs dd strans where
    transStatesDDs :: (Monad m) => Map Pident Int -> State dd -> strans -> DD.PartialStates dd -> DDM m (DD.PartialStates dd)
    monoDDsTrans :: Integer -> strans -> DDM IO strans
    monoDDsTrans _ = return

    -- | Bounded clustering of a partitioned relation.
    clusterTransDDs :: Integer -> strans -> DDM IO strans
    clusterTransDDs _ = return

    -- | The per-state successor function, prepared once per system.
    prepareSuccStates :: Map Pident Int -> strans -> DDM IO (State dd -> DDM IO (DD.PartialStates dd))
    prepareSuccStates ns tr = return (\pre_st -> transStatesDDs ns pre_st tr (Set.singleton IntMap.empty))

instance BuildDD dd => ExplicitTransDDs dd (AndDDs dd) where
    transStatesDDs ns pre_st (AndDDs dds) acc = foldMapCPSM (\_ dd -> transDDStates ns dd pre_st) acc return dds    

instance BuildDD dd => ExplicitTransDDs dd (NextDDs dd) where
    transStatesDDs ns pre_st (NextDDs dds) acc = foldMapCPSM (\_ dd -> transDDStates ns dd pre_st) acc return dds    

instance BuildDD dd => ExplicitTransDDs dd (TreeDDs dd) where
    monoDDsTrans budget t = maybe t id <$> DDs.monoTreeDDsBounded budget t
    transStatesDDs ns pre_st (NodeAndDDs dds) sts = foldMultiMapCPSM (\_ -> transStatesDDs ns pre_st) sts return dds 
    transStatesDDs ns pre_st (NodeOrDDs dds) sts = liftM DD.orsPartialStates $ mapM (\dd -> transStatesDDs ns pre_st dd sts) dds
    transStatesDDs ns pre_st (LeafDDs sup (dd)) sts = transDDStates ns dd pre_st sts

    clusterTransDDs budget t = ioReader (DDs.clusterTreeDDs budget t)

    prepareSuccStates ns tree = do
        ids <- Reader.asks varIds

        let colOf =
                IntMap.fromList
                    [ (i, col) | ((n, isNext), i) <- Map.toList ids, not isNext, Just col <- [Map.lookup n ns] ]

        let n2c =
                IntMap.fromList
                    [ (iN, iC) | ((n, True), iN) <- Map.toList ids, Just iC <- [Map.lookup (n, False) ids] ]

        -- The And's direct children are the cache units; anything else is a single unit.
        let rawParts =
                case tree of
                    NodeAndDDs m -> multiMapElems m
                    other -> [ other ]

        -- Top-down partial collapse under a node budget.
        let partialCollapse t = do
                mono <- DDs.monoTreeDDsBounded explicitPartMonoBudget t
                case mono of
                    Just t' -> return t'
                    Nothing -> case t of
                        NodeAndDDs m -> liftM NodeAndDDs (mapM partialCollapse m)
                        NodeOrDDs m -> liftM NodeOrDDs (mapM partialCollapse m)
                        leaf -> return leaf

        parts <- forM (zip [0 :: Int ..] rawParts) $ \(pIdx, part) -> do
            part' <- partialCollapse part
            return part'

        -- Per part: the exp columns of its current-support variables, ascending.
        let partCols =
                [ List.sort
                    [ col | i <- IntMap.keys (DDs.supportTreeDDs part), Just col <- [IntMap.lookup i colOf] ]
                | part <- parts
                ]

        caches <- liftIO (mapM (\_ -> newIORef HashMap.empty) parts)

        let preparedParts = map preparePart parts

        let cofactorPart fixVal part =
                let go t =
                        case t of
                            PLeaf dd -> DD.restrictWith fixVal dd
                            PAnd ks0 -> do
                                let goA acc ks =
                                        case ks of
                                            [] -> DD.ands (List.reverse acc)
                                            k : rest -> do
                                                d <- go k

                                                if DD.isLeaf (Proxy :: Proxy (DDM IO)) d == Just False then
                                                    DD.false
                                                else
                                                    goA (d : acc) rest

                                goA [] ks0
                            POr ks0 -> do
                                let goO acc ks =
                                        case ks of
                                            [] -> DD.ors (List.reverse acc)
                                            k : rest -> do
                                                d <- go k

                                                if DD.isLeaf (Proxy :: Proxy (DDM IO)) d == Just True then
                                                    DD.true
                                                else
                                                    goO (d : acc) rest

                                goO [] ks0
                in go part

        let succF pre_st = do
                let fixVal ddId =
                        case IntMap.lookup ddId colOf of
                            Just col -> Just (pre_st UV.! col)
                            Nothing -> Nothing

                -- Returns Nothing on the False short-circuit
                let goParts acc quads =
                        case quads of
                            [] -> return (Just acc)
                            (part, cols, cacheRef) : rest -> do
                                let key = map (pre_st UV.!) cols
                                cache <- liftIO (readIORef cacheRef)

                                d <-
                                    case HashMap.lookup key cache of
                                        Just d -> return d
                                        Nothing -> do
                                            d <- cofactorPart fixVal part
                                            liftIO (modifyIORef' cacheRef (HashMap.insert key d))
                                            return d

                                if DD.isLeaf (Proxy :: Proxy (DDM IO)) d == Just False then
                                    return Nothing
                                else
                                    goParts (d : acc) rest

                mbAcc <- goParts [] (List.zip3 preparedParts partCols caches)
                nextOnly <-
                    case mbAcc of
                        Nothing -> DD.false
                        Just acc -> DD.ands (List.reverse acc)
                partials <- DD.allSat nextOnly
                return (Set.map (IntMap.mapKeys (\i -> IntMap.findWithDefault i i n2c)) partials)

        return succF

-- | Compute one state's successors, filtered by the invariant.
transDDToStates3 :: (ExplicitInitDDs dd sinvar,BuildDDs dd sinvar) => (State dd -> DDM IO (DD.PartialStates dd)) -> sinvar -> Map Pident Int -> State dd -> DDM IO (DD.PartialStates dd)
transDDToStates3 succF invar ns pre_st = do
    st <- succF pre_st
    initStatesDDs invar st

-- | Extend a set of partial states via one transition diagram.
transDDStates :: (BuildDD dd,Monad m) => Map Pident Int -> dd -> State dd -> DD.PartialStates dd -> DDM m (DD.PartialStates dd)
transDDStates exp_ns dd pre_st sts = liftM Set.unions $ traverseSet (transDDState exp_ns dd pre_st) sts
    
-- | Extend one partial state via one transition diagram.
transDDState :: (BuildDD dd,Monad m) => Map Pident Int -> dd -> State dd -> DD.PartialState dd -> DDM m (DD.PartialStates dd)
transDDState exp_ns dd pre_st st0 = ioReader $ do
    r <- Reader.ask
    DD.accum (goBranch r) goLeaf (Just st0) dd 
  where
    goLeaf st b = if b then maybeToSet st else Set.empty
    goBranch r Nothing v = V.empty
    goBranch r (Just st) v = V.map apply (UV.convert vals)
        where
        vals = runReaderIO r (DD.vals v)
        (n,isNext) = Reader.runReader (varName v) r
        dd_i = if isNext then Reader.runReader (varId (n,False)) r else v
        Just exp_i = Map.lookup n exp_ns
        apply val = if isNext then DD.insertPartialState dd_i val st else checkPartialState pre_st exp_i val st

-- | Keep a next-state assignment only if it agrees with the source state.
checkPartialState :: BuildDD dd => State dd -> Int -> DD.Val dd -> DD.PartialState dd -> Maybe (DD.PartialState dd)
checkPartialState pre_st exp_i next_val next_st = if checkState exp_i next_val pre_st
    then Just next_st
    else Nothing

-- | Whether a column's value matches a state.
checkState :: BuildDD dd => Int -> DD.Val dd -> State dd -> Bool
checkState exp_i next_val st = next_val == (uvIndex "checkState" st exp_i)

