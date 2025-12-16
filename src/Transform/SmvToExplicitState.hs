module Transform.SmvToExplicitState where

import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.Map.Internal as Map
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Internal as IntMap
import Control.Monad.Reader (Reader(..),ReaderT(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Control.Monad
import Control.Monad.Identity
import Data.Vector (Vector(..))
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.List as List
import Data.Proxy
import Control.Monad.Trans
import Safe

import Utils
import Pretty
import Smv.Pretty
import Smv.Typing
import Smv.Syntax
import Smv.Packed
import ExplicitState.Syntax
import ExplicitState.Pretty
import Transform.Smv
import Transform.Bexpr
import Transform.Bpacked
import Transform.Substitute
import Data.DD (DD)
import qualified Data.DD as DD
import Data.DDs (DDstructure,AndDDs(..),NextDDs(..),TreeDDs(..))
import qualified Data.DDs as DDs
import Transform.DDs
import Transform.DDpacked
import HOA.LTL
import ExplicitState.Product
import ExplicitState.Eval
import Transform.Pexpr
import Transform.Split

--import Debug.Trace as Trace

transformToFixedExplicitState :: (BuildDD dd) => Proxy dd -> Integer -> Bool -> Bool -> Bool -> Maybe String -> PackedBmodule -> IO (DDExplicitStateSystem dd)
transformToFixedExplicitState dd maxddsize removeDeadlocks doRemoveTemps debug docker p = do
    let tree = DDs.proxyTreeDDs dd
    let and = DDs.proxyAndDDs dd
    let next = DDs.proxyNextDDs dd
    if maxddsize > 0
        then transformBSmvToExplicitStateSystem tree tree tree tree maxddsize removeDeadlocks doRemoveTemps debug docker p
        else transformBSmvToExplicitStateSystem and and next and maxddsize removeDeadlocks doRemoveTemps debug docker p

transformBSmvToExplicitStateSystem :: (ExplicitInitDDs dd sinit,BuildDDs dd sinvar,ExplicitTransDDs dd strans,BuildDDs dd sltl,MonadIO m) => Proxy sinit -> Proxy sinvar -> Proxy strans -> Proxy sltl -> Integer -> Bool -> Bool -> Bool -> Maybe String -> PackedBmodule -> m (DDExplicitStateSystem dd)
transformBSmvToExplicitStateSystem s1 s2 s3 s4 maxSize removeDeadlocks doRemoveTemps isDebug container b = withPackedDDmodule maxSize b (transformDDSmvToExplicitState s1 s2 s3 s4 removeDeadlocks doRemoveTemps isDebug container)

transformDDSmvToExplicitState :: (ExplicitInitDDs dd sinit,BuildDDs dd sinvar,ExplicitTransDDs dd strans,BuildDDs dd sltl,MonadIO m) => Proxy sinit -> Proxy sinvar -> Proxy strans -> Proxy sltl -> Bool -> Bool -> Bool -> Maybe String -> PackedDDmodule sinit sinvar strans sltl dd -> DDM m (DDExplicitStateSystem dd)
transformDDSmvToExplicitState s1 s2 s3 s4 removeDeadlocks doRemoveTemps isDebug container p = do
        ddnames <- Reader.asks varNames
        ddsizes <- Reader.asks (IntMap.map sizeOfVarType . varSizes)
        let ddsize = product ddsizes
        ns <- liftM (V.fromList . nub . map (fst >< id)) $ sortedTypes -- we only use non-next names, and follow the dd order
        sys <- identityReader $ do
--            liftIO $ putStrLn (show ddsize++"\ninitDDs\n"++show ddnames++"\n"++unlines (map show $ Map.elems $ unAndDDs $ dd_init p))
            initStates <- initDDToStates (dd_init p) (dd_invar p)
--            liftIO $ putStrLn $ "invarDD " ++ show (dd_invar p)
            --liftIO $ putStrLn $ "trans dd " ++ show (dd_trans p) ++ "\ntrans dd"
--            liftIO $ putStrLn $ (show ns ++"\nnum init states "++ show (Map.size $ fst $ initStates) ++"\n" ++ unlines (map (\(x,y) -> show x) $ Map.toList $ fst initStates) ++ " initStates")
            (states,trans) <- transDDToStates (dd_trans p) (dd_invar p) (vectorIndices $ V.map fst ns) initStates
            let inits' = IntSet.fromList $ Map.elems $ fst initStates
            let (sysInits,sysTrans) = mergeModel inits' (flipMapInt $ fst states) trans
            let sysAccepts = Nothing
            let sys = ExplicitStateSystem ns sysInits sysAccepts sysTrans
            return sys
        res <- {-trace ("system size" ++ show (sizeExplicitStateSystem sys)) $-} case dd_ltlspec p of
            Nothing -> return sys
            Just ltl -> restrictLTLSpec doRemoveTemps isDebug container ltl sys
        --trace "deadlocks" $
        let res' = if removeDeadlocks then removeDeadlockExplicitStateSystem res else res
        return res'

restrictLTLSpec :: (BuildDDs dd sltl,MonadIO m) => Bool -> Bool -> Maybe String -> DDltl sltl dd -> DDExplicitStateSystem dd -> DDM m (DDExplicitStateSystem dd)
restrictLTLSpec doRemoveTemps isDebug container ltl sys = {-trace ("restricting ltl " ++ show ltl ++ "\nover\n" ++ show (prettyExplicitStateSystem sys)) $-} doHOAM $ do
    hoa <- {-trace "converting ltl to HOA" $-} ltlToHOA doRemoveTemps isDebug container ltl
    dd_names <- lift $ Reader.asks varNames
    let dd_map = mkDDMap dd_names (exp_vars sys)
    nba <- {-trace "converting HOA to NBA" $-} State.mapStateT (identityReader) $ hoaToNBA hoa dd_map
    let sys' = {-trace (show $ IntMap.keys $ exp_nba_transitions nba) $-} productExplicitStateSystemNBA sys nba
    return sys'

mergeModel :: BuildDD dd => IntSet -> IntMap (State dd) -> Transitions -> (IntSet,IntMap (DD.Vals dd,IntSet))
mergeModel inits sts ts = (IntSet.intersection inits (IntMap.keysSet states),states)
    where
--    tsNoDead = dropDeadlockTransitions ts
    states = IntMap.merge whenL whenR whenLR sts ts
    whenL = IntMap.dropMissing 
    whenR = IntMap.dropMissing
    whenLR = IntMap.WhenMatched $ \k x y -> return $ Just (x,y)

dropDeadlockTransitions :: Transitions -> Transitions
dropDeadlockTransitions ts = if IntSet.null deads
    then ts'
    else dropDeadlockTransitions $ IntMap.map (\nexts -> IntSet.difference nexts deads) ts'
  where
    (IntMap.keysSet -> deads,ts') = IntMap.partition (IntSet.null) ts

type State dd = DD.Vals dd
type ProspectiveStates dd = Set (State dd)

initDDToStates :: (ExplicitInitDDs dd sinit,BuildDDs dd sinvar,Monad m) => sinit -> sinvar -> DDM m (States dd)
initDDToStates e invar = do
    liftM (registerStates 0 . Set.map completeToState) $ expandPartialStates =<< initDDStates e invar

initDDStates :: (ExplicitInitDDs dd sinit,BuildDDs dd sinvar,Monad m) => sinit -> sinvar -> DDM m (DD.PartialStates dd)
initDDStates inits invar = identityReader $ do
--    st <- DDs.allSat inits
    st <- initStatesDDs inits
    invarPartialStates invar st

class BuildDDs dd s => ExplicitInitDDs dd s where
    initStatesDDs :: (Monad m) => s -> DDM m (DD.PartialStates dd)

instance BuildDD dd => ExplicitInitDDs dd (AndDDs dd) where
    initStatesDDs (AndDDs dds) = liftM DD.andsPartialStates $ mapM initDDState dds

instance BuildDD dd => ExplicitInitDDs dd (NextDDs dd) where
    initStatesDDs (NextDDs dds) = liftM DD.andsPartialStates $ mapM initDDState dds
    
instance BuildDD dd => ExplicitInitDDs dd (TreeDDs dd) where
    initStatesDDs (NodeAndDDs dds) = liftM DD.andsPartialStates $ mapM (initStatesDDs . snd) dds
    initStatesDDs (NodeOrDDs dds) = liftM DD.orsPartialStates $ mapM (initStatesDDs . snd) dds
    initStatesDDs (LeafDDs sup (_,dd)) = initDDState dd

initDDState :: (BuildDD dd,Monad m) => dd -> DDM m (DD.PartialStates dd)
initDDState dd = identityReader $ do
    r <- Reader.ask
    DD.accum (goBranch r) (goLeaf) IntMap.empty dd
  where
--    goLeaf :: PartialState dd -> Bool -> (PartialStates dd)
    goLeaf st b = if b then Set.singleton st else Set.empty
--    goBranch :: DDReader -> PartialState dd -> Int -> Vector (PartialState dd)
    goBranch r st dd_i = V.map (\val -> insertPartialState dd_i val st) (UV.convert vals)
        where vals = Reader.runReader (DD.vals dd_i) r

--initDDStates' :: (DD dd,Monad m) => dd -> DDM m (PartialStates dd)
--initDDStates' dd = do
--    r <- Reader.ask
--    return $ DD.fold' (goBranch r) (goLeaf) dd
--  where
----    goLeaf :: Bool -> PartialStates dd
--    goLeaf b = if b then truePartialStates else falsePartialStates
----    goBranch :: DDReader -> Int -> Vector (PartialStates dd) -> PartialStates dd
--    goBranch r dd_i cs = orsPartialStates $ V.map (\(val,sts) -> Set.map (\st -> insertPartialState dd_i val st) sts) (V.zip (UV.convert vals) cs)
--        where vals = Reader.runReader (valuesOf dd_i) r

insertPartialState :: BuildDD dd => Int -> DD.Val dd -> DD.PartialState dd -> DD.PartialState dd
insertPartialState dd_i val st = IntMap.insertWith (error "insertPartialState") dd_i val st

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

type ExplicitSystem dd = (States dd,Transitions)

-- recursively find transitions, and possibly new states
transDDToStates :: (ExplicitTransDDs dd strans,BuildDDs dd sinvar,Monad m) => strans -> sinvar -> Map Pident Int -> States dd -> DDM m (ExplicitSystem dd)
transDDToStates e invar ns sts = transDDToStates2 e invar ns (Map.toList $ fst sts) (sts,IntMap.empty)

-- (existing states,new states,next state number)
type States2 dd = (Map (State dd) Int,Map (State dd) Int,Int)
type ExplicitSystem2 dd = (States2 dd,Transitions)

transDDToStates2 :: (ExplicitTransDDs dd strans,BuildDDs dd sinvar,Monad m) => strans -> sinvar -> Map Pident Int -> [(State dd,Int)] -> ExplicitSystem dd -> DDM m (ExplicitSystem dd)
transDDToStates2 e invar ns [] acc = return acc
transDDToStates2 e invar ns ((st,i):sts') acc@((acc_sts,acc_num),acc_trans) = {-trace ("processing trans state " ++ show i) $ -} do
    cands <- transDDStates e invar ns st
    news <- {-trace (show cands ++ " transStates") $-} expandPartialStates cands
    let ((olds',news',num'),ts') = linkNextStates i (Set.map completeToState news) acc
    --trace (show num' ++ "\n" ++ show news') $
    transDDToStates2 e invar ns (sts' ++ Map.toList news') ((Map.union olds' news',num'),ts')

-- adds new states and transitions to them
linkNextStates :: BuildDD dd => Int -> ProspectiveStates dd -> ExplicitSystem dd -> ExplicitSystem2 dd
linkNextStates i cands ((sts,num),ts) = Set.foldl linkNextState ((sts,Map.empty,num),ts) cands
    where
--    linkNextState :: ExplicitSystem2 dd -> State dd -> ExplicitSystem2 dd
    linkNextState ((olds,news,num),ts) x = case Map.lookup x olds of
        Just j -> ((olds,news,num),addTransition i j ts)
        Nothing -> ((olds,Map.insert x num news,num+1),addTransition i num $ IntMap.insert num IntSet.empty ts) -- to make sure that states with empty transitions appear in the map
  
addTransition :: Int -> Int -> Transitions -> Transitions
addTransition i j ts = IntMap.insertWith IntSet.union i (IntSet.singleton j) ts
  
registerStates :: BuildDD dd => Int -> ProspectiveStates dd -> States dd
registerStates n xs = Set.foldl go (Map.empty,n) xs
    where
--    go :: Dd dd => States dd -> State dd -> States dd
    go (ys,n) x = (Map.insert x n ys,n+1)
    
class BuildDDs dd strans => ExplicitTransDDs dd strans where
    transStatesDDs :: (Monad m) => Map Pident Int -> State dd -> strans -> DDM m (DD.PartialStates dd)

instance BuildDD dd => ExplicitTransDDs dd (AndDDs dd) where
    transStatesDDs ns pre_st (AndDDs dds) = do
        dds' <- mapM (\dd -> transDDState ns dd pre_st) dds
        return $ DD.andsPartialStates dds'

instance BuildDD dd => ExplicitTransDDs dd (NextDDs dd) where
    transStatesDDs ns pre_st (NextDDs dds) = do
        dds' <- mapM (\dd -> transDDState ns dd pre_st) dds
        return $ DD.andsPartialStates dds'
 
instance BuildDD dd => ExplicitTransDDs dd (TreeDDs dd) where
    transStatesDDs ns pre_st (NodeAndDDs dds) = liftM DD.andsPartialStates $ mapM (transStatesDDs ns pre_st . snd) dds
    transStatesDDs ns pre_st (NodeOrDDs dds) = liftM DD.orsPartialStates $ mapM (transStatesDDs ns pre_st . snd) dds
    transStatesDDs ns pre_st (LeafDDs sup (sz,dd)) = transDDState ns dd pre_st
    
transDDStates :: (ExplicitTransDDs dd strans,BuildDDs dd sinvar,Monad m) => strans -> sinvar -> Map Pident Int -> State dd -> DDM m (DD.PartialStates dd)
transDDStates dds invar ns pre_st = do
    st <- transStatesDDs ns pre_st dds
    --trace ("applying invar to " ++ show st) $
    invarPartialStates invar st

--transDDStates' :: (BuildDD dd,Monad m) => Map Pident Int -> dd -> State dd -> DDM m (DD.PartialStates dd)
--transDDStates' exp_ns (dd::dd) pre_st = identityReader $ do
--    r <- Reader.ask
--    DD.foldCPS (goBranch r) goLeaf id dd 
--  where
--    goLeaf b = if b then DD.truePartialStates else DD.falsePartialStates
--    goBranch r v cs = checks
--        where
--        vals = Reader.runReader (DD.vals v) r
--        (n,isNext) = Reader.runReader (varName v) r
--        dd_i = if isNext then Reader.runReader (varId (n,False)) r else v
--        Just exp_i = Map.lookup n exp_ns
--        apply :: (DD.Val dd,DD.PartialStates dd) -> DD.PartialStates dd
--        apply (val,st) = if isNext
--            then Set.map (insertPartialState dd_i val) st
--            else if checkState exp_i val pre_st then st else DD.falsePartialStates
--        checks :: DD.PartialStates dd = DD.orsPartialStates $ V.map apply (V.zip (UV.convert vals) cs)
    
transDDState :: (BuildDD dd,Monad m) => Map Pident Int -> dd -> State dd -> DDM m (DD.PartialStates dd)
transDDState exp_ns dd pre_st = identityReader $ do
    r <- Reader.ask
    DD.accum (goBranch r) goLeaf (Just IntMap.empty) dd 
  where
--    goLeaf :: BuildDD dd => Maybe (PartialState dd) -> Bool -> PartialStates dd
    goLeaf st b = if b then maybeToSet st else Set.empty
--    goBranch :: BuildDD dd => DDReader -> Maybe (PartialState dd) -> Int -> Vector (Maybe (PartialState dd))
    goBranch r Nothing v = V.empty
    goBranch r (Just st) v = V.map apply (UV.convert vals)
        where
        vals = Reader.runReader (DD.vals v) r
        (n,isNext) = Reader.runReader (varName v) r
        dd_i = if isNext then Reader.runReader (varId (n,False)) r else v
        Just exp_i = Map.lookup n exp_ns
        apply val = if isNext then Just (insertPartialState dd_i val st) else checkPartialState pre_st exp_i val st

--transDDStates' :: (DD dd,Monad m) => Map Pident Int -> dd -> State dd -> DDM m (PartialStates dd)
--transDDStates' exp_ns dd pre_st = do
--    r <- Reader.ask
--    return $ DD.fold' (goBranch r) goLeaf dd 
--  where
----    goLeaf :: DD dd => Bool -> PartialStates dd
--    goLeaf b = if b then truePartialStates else falsePartialStates
----    goBranch :: DD dd => DDReader -> Int -> Vector (PartialStates dd) -> PartialStates dd
--    goBranch r v cs = orsPartialStates $ V.map apply (V.zip (UV.convert vals) cs)
--        where
--        vals = Reader.runReader (valuesOf v) r
--        (n,isNext) = Reader.runReader (varName v) r
--        dd_i = if isNext then Reader.runReader (varId (n,False)) r else v
--        Just exp_i = Map.lookup n exp_ns
--        apply (val,sts) = if isNext
--            then Set.map (\st -> insertPartialState dd_i val st) sts
--            else if checkState exp_i val pre_st then truePartialStates else falsePartialStates

--restrictPartialState :: (DD dd,Monad m) => PartialState dd -> dd -> DDM m (PartialStates dd)
--restrictPartialState st invar = do
--    r <- Reader.ask
--    return $ DD.fold' (goBranch r) goLeaf invar
--  where
----    goLeaf :: Bool -> PartialStates dd
--    goLeaf b = if b then Set.singleton st else falsePartialStates
----    goBranch :: DDReader -> Int -> Vector (PartialStates dd) -> PartialStates dd
--    goBranch r dd_i cs = orsPartialStates $ V.map restrict (V.zip (UV.convert vals) cs)
--        where
--        vals = Reader.runReader (valuesOf dd_i) r
--        (n,False) = Reader.runReader (varName dd_i) r
--        restrict (val,sts) = case IntMap.lookup dd_i st of -- this is safe because variables are ordered in the DD
--            Just val' -> if val==val' then sts else falsePartialStates
--            Nothing -> Set.map (\st -> IntMap.insertWith (error "restrictPartialState") dd_i val st) sts

checkPartialState :: BuildDD dd => State dd -> Int -> DD.Val dd -> DD.PartialState dd -> Maybe (DD.PartialState dd)
checkPartialState pre_st exp_i next_val next_st = if checkState exp_i next_val pre_st
    then Just next_st
    else Nothing

checkState :: BuildDD dd => Int -> DD.Val dd -> State dd -> Bool
checkState exp_i next_val st = next_val == (uvIndex "checkState" st exp_i)

splitBformulaExplicit :: (BuildDD dd,MonadIO m) => SplitFormulaMode -> Bool -> Bool -> Maybe String -> ([(String,DDExplicitStateSystem dd)],Bformula) -> DDM m ([(String,DDExplicitStateSystem dd)],Bformula)
splitBformulaExplicit mode doRemoveTemps isDebug container (exps,f) = do
    let (mexps',f') = splitBformula (restrictM mode) (map return exps,f)
    exps' <- mapM id mexps'
    return (exps',normalizeBformula f')
  where
    restrictM :: (BuildDD dd,MonadIO m) => SplitFormulaMode -> Bexpr -> DDM m (String,DDExplicitStateSystem dd) -> Maybe (DDM m (String,DDExplicitStateSystem dd))
    restrictM NoSplitFormula e m = Nothing
    restrictM Invar e m | not (isInvar e) = Nothing
    restrictM mode e m = Just $ m >>= \(dim,sys) -> withDDM (toLocalPident dim) $ do
        ltl :: DDltl (AndDDs dd) dd <- identityReader $ buildDDltl e
        sys' <- restrictLTLSpec doRemoveTemps isDebug container ltl sys
        --trace ("restrict explicit " ++ dim ++ "\n" ++ prettyprint e ++ " \n" ++ show (prettyExplicitStateSystem sys')) $
        return (dim,sys')
    isInvar (Bop1 Pg e) = True
    isInvar _ = False

toLocalPident :: String -> DualPident -> Maybe DualPident
toLocalPident dim (n,isNext) = case isSingleDimsPident n of
    Just dim_n -> if dim==dim_n then Just (remDimPident n,isNext) else Nothing
    Nothing -> Nothing

-- safe because names are already sorted by DD indices
completeToState :: BuildDD dd => DD.CompleteState dd -> State dd
completeToState = UV.fromList . IntMap.elems

-- projection can collapse several states into the same state. thus, for a transition in the target trace we search for possibly several transitions in the source trace
-- WARNING: this stuttering-expansion is local for each model and may not be consistent for multiple traces from different models. it should be sound in practice assuming that we self-compose outermost similar quantifiers, and witnesses are only generated for the outermost quantifier
findTrace :: ([DDExplicitPred dd],[DDExplicitPred dd]) -> DDExplicitStateSystem dd -> Maybe ([Int],[Int])
findTrace (prefix,lasso) exp = headMay $ do
    let is = IntSet.toList $ exp_inits exp
    (prefix',j) <- msum $ map (findStates False IntSet.empty prefix) is
    (lasso',k) <- findStates False (IntSet.fromList prefix') lasso j
    (prefix'',lasso'') <- findLasso lasso' k
    guard $ case exp_accepting exp of
        Nothing -> True
        Just accepts -> not $ IntSet.null $ IntSet.intersection accepts $ IntSet.fromList lasso''
    return (prefix'++prefix'',lasso'')
  where
    -- make sure that we do not visit repeated states to ensure progress
--    findStates :: MonadPlus m => [DDExplicitPred dd] -> Int -> m ([Int],Int)
    findStates checkVisited visited [] i = {-Trace.trace "done"-} return ([],i)
    findStates checkVisited visited (p:ps) i = {-Trace.trace ("trace " ++ show visited ++" "++ show i)-} do
        when checkVisited $ guard $ not $ IntSet.member i visited
        let (vals_i,nexts_i) = exp_state exp i
        guard $ p i vals_i
        let visited' = IntSet.insert i visited
        let js = IntSet.toList nexts_i
        let next = msum $ map (findStates False visited' ps) js
        let stutter = msum $ map (findStates True visited' (p:ps)) js
        liftM ((i:) >< id) $ next `mplus` stutter
    findLasso :: MonadPlus m => [Int] -> Int -> m ([Int],[Int])
    findLasso [] k = mzero
    findLasso (x:xs) k = do
        let (vals_k,nexts_k) = exp_state exp k
        let found = guard (IntSet.member x nexts_k) >> return ([],x:xs)
        let continue = liftM ((x:) >< id) $ findLasso xs k
        found `mplus` continue
        
----    findStates :: [DDExplicitPred dd] -> [DDExplicitPred dd] -> [Int] -> [Int] -> Int -> Maybe ([Int],[Int])
--    findStates (p:ps) ls prefixes lassos i = let (vals_i,nexts_i) = exp_state exp i in if p vals_i
--        then msum $ map (findStates ps ls (prefixes++[i]) lassos) $ IntSet.toList nexts_i
--        else Nothing
--    findStates [] (l:ls) prefixes lassos i = let (vals_i,nexts_i) = exp_state exp i in if l vals_i
--        then msum $ map (findStates [] ls prefixes (lassos++[i])) $ IntSet.toList nexts_i
--        else Nothing
--    findStates [] [] prefixes lassos i = do
--        let (vals_i,nexts_i) = exp_state exp i
--        j <- headMay lassos
--        let hasAccepting = case exp_accepting exp of
--                Nothing -> True
--                Just accepts -> not $ IntSet.null $ IntSet.intersection accepts $ IntSet.fromList lassos
--        if IntSet.member j nexts_i && hasAccepting
--            then return (prefixes,lassos)
--            else Nothing

findAnyTrace :: DDExplicitStateSystem dd -> Maybe ([Int],[Int])
findAnyTrace = findTrace ([],[\i vals -> True])

checkEmptyExplicits :: MonadIO m => Bool -> ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pformula) -> m ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pformula)
checkEmptyExplicits isDebug (exps,f) = do
    (exps',qe') <- check (zip qs exps) qe
    return (exps',applyQuantsExpr qs qe')
  where
    qs = quantsPformula f
    qe = exprPformula f
    check :: MonadIO m => [((String,Quant),(DDExplicitStateSystem dd,IntMap Int,BSubst))] -> Pexpr -> m ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pexpr)
    check [] qe = return ([],qe)
    check (((dim,Qforall),exp):xs) qe = liftM ((exp:) >< id) (check xs qe)
    check (((dim,Qexists),(exp,renames,aps)):xs) qe = case findAnyTrace exp of
        Nothing -> do
            liftIO $ when isDebug $ putStrLn $ "WARNING: explicit state system " ++ dim ++ " is empty"
            return ((emptyExplicitStateSystem,IntMap.empty,aps):map snd xs,Pebool False)
        Just _ -> liftM (((exp,renames,aps):) >< id) (check xs qe)
    

