module Transform.Exhaustive where

import Data.Foldable
import Shelly
import Control.Monad
import Control.Monad.Identity
import Control.Monad.IO.Class
import Control.Monad.Trans
import qualified Data.Text as T
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (ReaderT(..))
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.RWS.CPS as RWS
import Safe
import Control.Monad.Trans.Maybe
import Data.Maybe
import Prettyprinter
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Key as K
import qualified Data.Array as A
import qualified Data.Graph as Graph
import Data.List as List
import qualified Data.Heap as Heap
import Data.Proxy
import Data.Hashable as Hashable

import Pretty
import Utils
import Error
import Smv.Syntax
import Smv.Parser
import Smv.Packed
import Smv.Pretty
import Smv.Typing
import Transform.Bexpr
import Transform.Bpacked
import Transform.Pexpr
import Data.DD (DD(..))
import qualified Data.DD as DD
import Transform.DDs
import Transform.DDpacked
import Transform.Substitute
import Transform.Normalize
import Transform.CSE
import Data.DT
import Transform.DT.Expr
import ExplicitState.Syntax
import ExplicitState.Product
import ExplicitState.Eval
import qualified Location as L
import Data.DDs (DDstructure,AndDDs(..),NextDDs(..))
import qualified Data.DDs as DDs
import Transform.SmvToExplicitState
import Transform.Rename

--import Debug.Trace as Trace

--optimizeBformulaForSmv :: Monad m => PackedPvars -> Bformula -> m (Pformula,[BSubst])
--optimizeBformulaForSmv vars formula = do
--    let qs = quantsBformula formula
--    (formula',(substs)) <- transformCSEFormula HyperQubeCSE formula
--    let dvars = Map.union vars (Map.map (const Pboolean) substs)
--    let str = "CSE: " ++ prettyprint formula' ++ "\n" ++ unlines (map (\(x,y) -> prettyprint x ++ "\n" ++ prettyprint y) $ Map.toList substs) ++ "endCSE"
--    Trace.trace (str ++ "\n" ) $ runDDM dvars False $ do
--        dsubsts <- mapM buildDDs substs
--        isubsts :: IntMap (Pident,AndDDs) <- K.foldlWithKeyM (\m n e -> varId (n,False) >>= \i -> return $ IntMap.insert i (n,e) m) IntMap.empty dsubsts
--        graph <- buildGraphDDs isubsts
--        let revorder = independenceTopoSort isubsts graph
--        
--        let roots = mapWithKey fst id $ occurrencesBformula formula'
--        (isubsts',used') <- optimizeSubsts revorder roots Nothing isubsts
--        
--        (outFormula,outBSubst) <- doBM (Map.map toVarType dvars) $ do
--            formula'' <- fromBformula formula'
--            (outFormula,outSubst) <- buildSubst HyperQubeCSE used' (formula'',Map.fromList $ IntMap.elems isubsts')
--            outBSubst <- toBSubst outSubst
--            return (outFormula,outBSubst)
--        
--        retFormula <- mapFormula (return . normalizeExpr) outFormula
--        retBSubsts <- groupBSubst qs outBSubst
--        return (retFormula,retBSubsts)

optimizeBformulaForSmv :: Monad m => PackedPvars -> Bformula -> m (Pformula,[Subst])
optimizeBformulaForSmv vars formula = do
    let qs = map fst $ quantsBformula formula
    (formula',substs) <- transformCSEFormula HyperQubeCSE formula
    let dvars = Map.union vars (Map.map (const Pboolean) substs)
    --let str = "CSE: " ++ prettyprint formula' ++ "\n" ++ unlines (map (\(x,y) -> prettyprint x ++ "\n" ++ prettyprint y) $ Map.toList substs) ++ "endCSE"
    --Trace.trace (str ++ "\n" ) $
    do
        (outFormula,outSubst) <- doBM (Map.map toVarType dvars) $ do
            dsubsts <- mapM fromBexpr substs
            formula'' <- fromBformula formula'
            (outFormula,outSubst) <- buildSubst HyperQubeCSE Map.empty (formula'',dsubsts)
            return (outFormula,outSubst)
        
        retFormula <- mapFormula (return . normalizeExpr) outFormula
        retSubsts <- groupSubst qs outSubst
        return (retFormula,retSubsts)

optimizeBformulaForExplicitStateDD :: (BuildDD dd,MonadIO m) => Proxy dd -> Integer -> Bool -> Bool -> Maybe String -> SplitFormulaMode -> Bool -> Bool -> Bool -> [DDExplicitStateSystem dd] -> Bformula -> m ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pformula)
optimizeBformulaForExplicitStateDD (dd :: Proxy dd) maxSize doRemoveTemps isDebug container doSplitFormula doSingles doBisim largeAPs exps formula = {-Trace.trace ("optimize formula " ++ prettyprint formula) $-} do
    let qs = quantsBformula formula
    let vars = joinHyperPvars $ map (id >< exp_packedPvars) (zip (map fst qs) exps)
    (exps::[(DDExplicitStateSystem dd,BSubst)],formula) <- runDDM vars False maxSize $ {-Trace.trace ("orivars " ++ show vars) $-} do
        liftM (map snd >< id) (splitBformulaExplicit doSplitFormula doRemoveTemps isDebug container (zip (map fst qs) exps,formula)) >>= if doSingles then mkSinglesExplicitFormula else return . (map (,Map.empty) >< id)
    let vars = joinHyperPvars $ map (id >< exp_packedPvars) (zip (map fst qs) (map fst exps))
    runDDM vars False maxSize $ do
        let e = exprBformula formula 
        --liftIO $ putStrLn $ "formula " ++ prettyprint e
        ltl <- identityReader $ buildDDltlProxy dd e
        --liftIO $ putStrLn $ "ddltl " ++ show ltl
        e' <- ddltlToExprWith (mkExpr) ltl
        --liftIO $ putStrLn $ "expr " ++ prettySMV (AutoHyper Hyper) e'
        let f' = applyQuantsExpr qs e'
        let vvs = map snd $ groupVarSet (map fst qs) $ varsFormula f'
        let project (vs,(e,aps)) = if doBisim
                then let (e',renames) = projectExplicitStateSystem vs e in (e',renames,aps)
                else (e,IntMap.mapWithKey (\k _ -> k) (exp_states e),aps)
        let exps' = map project (zip vvs exps)
        return (exps',f')
  where
    mkAtom = if largeAPs then patomUnsafe else atomifyExpr
    mkExpr :: (BuildDD dd,Monad m) => AndDDs dd -> DDM m Pexpr
    mkExpr (AndDDs dds) = liftM (Peopn Pand) $ mapM (liftM mkAtom . ddToExpr) $ Map.elems dds

mkSinglesExplicitFormula :: (BuildDD dd,Monad m) => ([DDExplicitStateSystem dd],Bformula) -> DDM m ([(DDExplicitStateSystem dd,BSubst)],Bformula)
mkSinglesExplicitFormula (exps,formula) = do
    let qs = quantsBformula formula
    let e = exprBformula formula 
    (e,ss) <- transformSingles e
    qss <- {-Trace.trace ("singles " ++ prettyprint e ++ unlines (map (\(x,y) -> prettyprint x ++":"++prettyprint y) $ Map.toList ss)) $-} groupBSubst (map fst qs) ss
    r <- Reader.ask
    let extend (dim,s,ss::BSubst) = withDDM (toLocalPident dim) $ {-Trace.trace ("extending " ++ unlines (map (\(x,y) -> prettyprint x ++":"++prettyprint y) $ Map.toList ss)) $-} do
            dss :: Map Pident (AndDDs dd) <- identityReader $ mapM buildDDs ss
            let go (l,r) n dds = case DDs.isLeaf (Proxy :: Proxy (DDM Identity)) dds of
                    Nothing -> (l,Map.insert n dds r)
                    Just b -> (Map.insert n (Bbool b) l,r)
            let (constss :: BSubst,compoundss :: Map Pident (AndDDs dd)) = K.foldlWithKey go (Map.empty,Map.empty) dss
            ddnames <- Reader.asks varNames
            let dd_map = mkDDMap ddnames (exp_vars s)
            let ctx = map (\(n,e) -> ((n,VBool),DD.boolToVal . evalExplicitDDs' r dd_map e)) $ Map.toList compoundss
            let compounddss :: BSubst = Map.intersectionWith (\l r -> r) compoundss ss
            return ((extendExplicitStateSystem ctx s,compounddss),constss)
            
    (exps,qconsts) <- liftM unzip $ mapM extend (zip3 (map fst qs) exps qss)
    consts <- ungroupBSubst (map fst qs) qconsts
    e <- substBexpr consts consts True e
    return (exps,applyQuantsBexpr qs e)

optimizeBformulaForExplicitStateDT :: (BuildDD dd,MonadIO m) => Proxy dd -> Integer -> Bool -> Bool -> Maybe String -> SplitFormulaMode -> Bool -> Bool -> [DDExplicitStateSystem dd] -> Bformula -> m ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pformula)
optimizeBformulaForExplicitStateDT dd maxSize doRemoveTemps isDebug container doSplitFormula doSingles doBisim exps formula = do
    let qs = quantsBformula formula
    let vars = joinHyperPvars $ map (id >< exp_packedPvars) (zip (map fst qs) exps)
    (exps::[(DDExplicitStateSystem dd,BSubst)],formula) <- runDDM vars False maxSize $ do
        liftM (map snd >< id) (splitBformulaExplicit doSplitFormula doRemoveTemps isDebug container (zip (map fst qs) exps,formula)) >>= if doSingles then mkSinglesExplicitFormula else return . (map (,Map.empty) >< id)
    let vars = joinHyperPvars $ map (id >< exp_packedPvars) (zip (map fst qs) (map fst exps))
    return $ runIdentity $ do
        let p = Just $ productNExplicitStates (zip (map fst qs) (map fst exps))
        (formula',substs) <- {-Trace.trace (show vars) $-} transformCSEFormula AutoHyperCSE formula
        let dvars = Map.union vars (Map.map (const Pboolean) substs)
        --Trace.trace ("CSE " ++ prettyprint formula' ++"\n"++ unlines (map (\(x,y) -> prettyprint x ++ ": " ++ prettyprint y) $ Map.toList substs)) $
        runDDM dvars False maxSize $ do
            dsubsts <- mapM buildDDs substs
            isubsts :: IntMap (Pident,AndDDs dd) <- K.foldlWithKeyM (\m n e -> varId (n,False) >>= \i -> return $ IntMap.insert i (n,e) m) IntMap.empty dsubsts
            graph <- buildGraphDDs isubsts
            let revorder = independenceTopoSort isubsts graph
            let inorder = reverse revorder
            names <- Reader.asks varNames
            synth <- forM p $ \p -> do
                let dd_map = mkDDMap names (expss_vars p)
                extendBatch inorder (p,dd_map) isubsts
            let roots = mapWithKey fst id $ occurrencesBformula formula'
            (isubsts',used') <- optimizeSubsts revorder roots synth isubsts 
            formula'' <- doBM (Map.map toVarType dvars) $ fromBformula formula'
            (outFormula,outSubst) <- buildSubst AutoHyperCSE used' (formula'',Map.fromList $ IntMap.elems isubsts')
            let atomSubst = Map.map patom outSubst
            f' <- mapFormula (liftM (normalizeExpr . atomifyExpr) . substExpr atomSubst atomSubst True) outFormula
            let vvs :: [Set Pident] = map snd $ groupVarSet (map fst qs) $ varsFormula f'
            let project (vs,(e,aps)) = if doBisim
                    then let (e',renames) = projectExplicitStateSystem vs e in (e',renames,aps)
                    else (e,IntMap.empty,aps)
            let exps' = map project (zip vvs exps)
            return (exps',f')

buildSubst :: (Monad m) => ModeCSE -> Map Pident Int -> (Pformula,Subst) -> m (Pformula,Subst)
buildSubst mode uses (formula,is) = do
    let keepMode n = case mode of { HyperQubeCSE -> isJust (isSingleDimPident n); AutoHyperCSE -> True }
    let isFreq n e = case mode of { AutoHyperCSE -> case Map.lookup n uses of { Just u -> u > 1; Nothing -> False }; HyperQubeCSE -> True }
    let (keeps,drops) = Map.partitionWithKey (\n e -> Prelude.not (isSimpleExpr e) && isFreq n e && keepMode n) is
    keeps' <- mapM (substExpr drops drops True) keeps
    formula' <- mapFormula (substExpr drops drops True) formula
    return $ inlineNonFormulaSubst (formula',keeps')

inlineNonFormulaSubst :: (Pformula,Subst) -> (Pformula,Subst)
inlineNonFormulaSubst (f,ss) = (f',ss')
    where
    vs = varsFormula f
    (keeps,drops) = Map.partitionWithKey (\k e -> Set.member k vs) ss
    f' = runIdentity $ mapFormula (substExpr drops drops True) f
    ss' = runIdentity $ mapM (substExpr drops drops True) keeps

-- a graph with directed edges from DD expressions to variables that they use
buildGraphDDs :: (BuildDDs dd s,Monad m) => IntMap (Pident,s) -> DDM m Graph.Graph
buildGraphDDs iss = do
    names <- Reader.asks varNames
    let (minVertex,_) = IntMap.findMin names
    let (maxVertex,_) = IntMap.findMax names
    r <- Reader.ask
    let edges = IntMap.foldlWithKey (\acc i (n,dds) -> buildEdgesDDs r n i dds ++ acc) [] iss
    return $ Graph.buildG (minVertex,maxVertex) edges
  where
--    buildEdgesDDs :: DDstructure (DDM m) dd s => DDReader -> Pident -> Int -> s -> [Graph.Edge]
    buildEdgesDDs r dd_n dd_i dds = IntSet.foldl (\acc v_i -> (dd_i,v_i) : acc) [] sup
        where sup = Reader.runReader (DDs.support dds) r

extendBatch :: (BuildDDs dd s,Monad m) => [Int] -> DDExplicitStates dd -> IntMap (Pident,s) -> DDM m (DDExplicitStates dd)
extendBatch vertices (p,dd_map) iss = do
    r <- Reader.ask
    let missings = filter (\i -> isNothing $ IntMap.lookup i dd_map) vertices
    let dd_map' = IntMap.union dd_map $ IntMap.fromList $ zip missings [V.length (expss_vars p)..]
    let ctx = V.fromList $ map (\dd_i -> let (dd_n,dds) = unsafeIntLookupNote "extendBatch" dd_i iss in ((dd_n,VBool),DD.boolToVal . evalExplicitDDs' r dd_map' dds)) missings
    return (extendExplicitStates ctx p,dd_map')

-- computes a topological sort, prioritizing DD vertices with lower out-degree (uses less other expressions, as a metric of independence; give priority to core variables)
independenceTopoSort :: IntMap b -> Graph.Graph -> [Graph.Vertex]
independenceTopoSort idds g = priorityTopoSort getOutDeg g
    where
    outDegMap = intMapFromArray $ Graph.outdegree g
    getOutDeg k = (isJust $ IntMap.lookup k idds,unsafeIntLookupNote "getOutDeg" k outDegMap)

priorityTopoSort :: Ord p => (Graph.Vertex -> p) -> Graph.Graph -> [Graph.Vertex]
priorityTopoSort priority g = go initialHeap inDegMap
    where
    inDegMap = intMapFromArray $ Graph.indegree g 
    
    -- Initialize priority queue with all nodes that have in-degree 0
    initialHeap = Heap.fromList [ Heap.Entry (priority v) v | v <- Graph.vertices g , unsafeIntLookupNote "initialHeap" v inDegMap == 0 ]

    go heap inDegs = if Heap.null heap then [] else v : go heapNext inDegs'
        where
        Heap.Entry _ v = Heap.minimum heap
        heap' = Heap.deleteMin heap
        (heapNext, inDegs') = foldl (updateNeighbor v) (heap', inDegs) (g A.! v)

    -- Reduce in-degree of neighbors; add to heap if in-degree becomes 0
    updateNeighbor fromV (h,indegs) toV = if d == 0 then (Heap.insert (Heap.Entry (priority toV) toV) h,indegs') else (h,indegs')
        where
        d = unsafeIntLookupNote "updateNeighbor" toV indegs - 1
        indegs' = IntMap.insert toV d indegs

optimizeSubsts :: (BuildDD dd,Monad m) => [Int] -> Map Pident Int -> Maybe (DDExplicitStates dd) -> IntMap (Pident,AndDDs dd) -> DDM m (IntMap (Pident,Pexpr),Map Pident Int)
optimizeSubsts vertices seen explicit iss = liftM thr3 $ foldM optimizeVertex (fmap (,IntSet.empty) explicit,iss,(IntMap.empty,seen)) vertices
    where
    optimizeVertex acc@(explicit,is,(ss,seen)) dd_i = do
        --n <- varName dd_i
        {-Trace.trace ("optimizeVertex " ++ show dd_i ++ " " ++ show n) $-}
        if IntMap.null is then return acc else do
            let is' = IntMap.delete dd_i is
            let skip_explicit = fmap (\((p,dd_map),projs) -> 
                    let exp_i = unsafeIntLookupNote "optimizeVertex" dd_i dd_map
                    in ((p,IntMap.delete dd_i dd_map),IntSet.insert exp_i projs)) explicit
            let skip = return (skip_explicit,is',(ss,seen))
            case IntMap.lookup dd_i is of
                Nothing -> skip
                Just (dd_n,dds) -> if isNothing (Map.lookup dd_n seen) then skip else do
                    let (explicit',synth) = case explicit of
                            Nothing -> (Nothing,Nothing)
                            Just ((p,dd_map),projs) -> 
                                let exp_i = unsafeIntLookupNote "optimizeVertex" dd_i dd_map
                                    pprojs = projectAwayExplicitStatesIx projs p
                                    dd_map_projs = foldl (\m exp_i -> IntMap.map (\exp_j -> if exp_j > exp_i then exp_j - 1 else exp_j) m) dd_map (IntSet.toDescList projs)
                                    e = ((pprojs,IntMap.delete dd_i dd_map_projs),IntSet.singleton exp_i)
                                    s = dtExprSynthesizer (pprojs,dd_map_projs)
                                in  (Just e,Just s)
                    e <- optimizeAndDDs synth dds
                    let eseen = occurrencesExpr e
                    return (explicit',is',(IntMap.insert dd_i (dd_n,e) ss,Map.unionWith (+) seen eseen))

optimizeAndDDs :: (BuildDD dd,Monad m) => Maybe (ExprSynthesizer dd m) -> AndDDs dd -> DDM m Pexpr
optimizeAndDDs synth (AndDDs dds) = liftM (pands . Map.elems) $
    mapM (\dd -> {-Trace.trace ("optimizing DD "++show dd) $-} optimizeDD synth dd >>= \e -> {-Trace.trace ("optimized DD " ++ prettyprint e) $-} return e) dds

optimizeDD :: (BuildDD dd,Monad m) => Maybe (ExprSynthesizer dd m) -> dd -> DDM m Pexpr
optimizeDD Nothing dd = ddToExpr dd
optimizeDD (Just synth) dd = do
    sup <- identityReader $ DD.support dd
    if IntSet.size sup <= 1
        then ddToExpr dd
        else synth dd

type ExprSynthesizer e m = e -> DDM m Pexpr

liftExprSynthesizer :: (Monad m,MonadTrans t) => ExprSynthesizer e m -> ExprSynthesizer e (t m)
liftExprSynthesizer f dd = Reader.mapReaderT lift (f dd)

dtExprSynthesizer :: (BuildDD dd,Monad m) => DDExplicitStates dd -> ExprSynthesizer dd m
dtExprSynthesizer (pp,dd_map) dd = {-Trace.trace "synthesizing" $-} identityReader $ do
    --e <- ddToExpr dd
    names <- Reader.asks varNames
    r <- Reader.ask
    sup <- DD.support dd
    let ns = Set.map (\n -> fst $ unsafeIntLookupNote "dtExprSynthesizer" n names) $ fromIntSet sup
    let m = vectorIndices (V.map fst $ expss_vars pp)
    let is = IntSet.fromList $ map (\n -> unsafeLookupNote ("projectExplicitStates " ++ show n ++ " " ++ show m) n m) $ Set.toList ns
    let pE = projectExplicitStatesIx is pp
    let dd_mapE = dd_map `composeIntMapInt` IntMap.fromList (zip (IntSet.toList is) [0..])  --mkDDMap names pE
--    let dd_mapE = dd_map `composeIntMapInt` IntMap.fromList (zip (IntSet.toList is) [0..])  
--    dataset <- Trace.trace ("dt " ++ show sup) $ evalExplicitStatesToTableOri pE (evalDD dd_mapE dd)
    let dataset = evalExplicitStatesToTable pE (evalExplicitDD' r dd_mapE dd)
    let tye = synthesizeExpr dataset
    --Trace.trace ({-"optimizing: " ++ prettySMV Default e ++ "\n"-}"optimized: " ++ prettySMV Default tye) $
    return tye

-- (explicit states,mapping from dd vars to exp vars)
type DDExplicitStates dd = (ExplicitStates Pident (DD.Val dd),IntMap Int)

-- extracts ((global initial conditions,global invariants),formula) from a formula
extractInvariantsBformula :: Bformula -> ((Bexpr,Bexpr),Bformula)
extractInvariantsBformula = extractInvariantsBformula' True
    where
    extractInvariantsBformula' isAll (Bforall n f) = let (l,r) = extractInvariantsBformula' True f in (l,Bforall n r)
    extractInvariantsBformula' isAll (Bexists n f) = let (l,r) = extractInvariantsBformula' False f in (l,Bexists n r)
    extractInvariantsBformula' isAll (Bltl e) = let (l,r) = extractInvariantsBexpr' isAll e in (l,Bltl r)

    extractInvariantsBexpr' :: Bool -> Bexpr -> ((Bexpr,Bexpr),Bexpr)
    extractInvariantsBexpr' True (Bopn Pand es) = foldl collectOrInvars ((Bbool False,Bbool False),Bbool False) es
    extractInvariantsBexpr' False (Bopn Por es) = foldl collectAndInvars ((Bbool True,Bbool True),Bbool True) es
    extractInvariantsBexpr' isAll e = ((Bbool True,Bbool True),e)
        
    collectAndInvars ((init,invar),f) (Bop1 Pg e) = ((init,band invar e),f)
    collectAndInvars ((init,invar),f) e | Prelude.not (isLTLBexpr e) = ((band init e,invar),f)
    collectAndInvars ((init,invar),f) e = ((init,invar),band f e)
    
    collectOrInvars ((init,invar),f) (Bop1 Pg e) = ((init,band invar e),f)
    collectOrInvars ((init,invar),f) e | Prelude.not (isLTLBexpr e) = ((band init e,invar),f)
    collectOrInvars ((init,invar),f) e = ((init,invar),band f e)


