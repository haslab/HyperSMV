-- | Structured combinations of DDs.
module Data.DDs where
    
import Prelude hiding (not,or,and)
import qualified Prelude
import Control.Monad
import qualified Data.Foldable as Foldable
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.Hashable as Hashable
import GHC.Generics as Generics
import Data.Proxy
import qualified Data.Key as K
import qualified Data.Vector.Unboxed as UV
import Prettyprinter

import Data.DD (DD)
import qualified Data.DD as DD
import Utils

-- | Boolean structure built from and reducible to a 'DD'.
class (DD m dd,Show s) => DDstructure m dd s | s -> dd where
    isLeaf :: Proxy m -> s -> (Maybe Bool)
    
    singleton :: dd -> m s
    
    flatten :: s -> m dd
    
    and, andDefault :: s -> s -> m s
    and = andDefault
    andDefault x y = do
        x' <- flatten x
        y' <- flatten y
        singleton =<< (x' `DD.and` y')
        
    or, orDefault :: s -> s -> m s
    or = orDefault
    orDefault x y = do
        x' <- flatten x
        y' <- flatten y
        singleton =<< (x' `DD.or` y')
        
    not, notDefault :: s -> m s
    not = notDefault
    notDefault x = do
        x' <- flatten x
        singleton =<< (DD.not $ x')
        
    equiv, equivDefault :: s -> s -> m s
    equiv = equivDefault
    equivDefault x y = do
        x' <- flatten x
        y' <- flatten y
        singleton =<< (x' `DD.equiv` y')
        
    implies, impliesDefault ::s -> s -> m s
    implies = impliesDefault
    impliesDefault x y = do
        x' <- flatten x
        y' <- flatten y
        singleton =<< (x' `DD.implies` y')
    evaluate, evaluateDefault :: (Int -> DD.Val dd) -> s -> m Bool
    evaluate = evaluateDefault
    evaluateDefault f x = do
        x' <- flatten x
        DD.evaluate f x'
        
    support, supportDefault :: s -> m IntSet
    support = supportDefault
    supportDefault = DD.support <=< flatten 
    
    allSat, allSatDefault :: s -> m (DD.PartialStates dd)
    allSat = allSatDefault
    allSatDefault = DD.allSat <=< flatten 
    
    allSatComplete, allSatCompleteDefault :: s -> m (DD.CompleteStates dd)
    allSatComplete = allSatCompleteDefault
    allSatCompleteDefault = DD.allSatComplete <=< flatten 
    
    ands, andsDefault :: (DDstructure m dd s,Foldable t) => t s -> m s
    ands xs = DD.true >>= singleton >>= \z -> Foldable.foldlM and z xs
    andsDefault xs = DD.true >>= singleton >>= \z -> Foldable.foldlM andDefault z xs

    ors, orsDefault :: (DDstructure m dd s,Foldable t) => t s -> m s
    ors xs = DD.false >>= singleton >>= \z -> Foldable.foldlM or z xs
    orsDefault xs = DD.false >>= singleton >>= \z -> Foldable.foldlM orDefault z xs
    
    foldCPS :: (b -> b -> m b) -> (b -> b -> m b) -> (dd -> m b) -> (b -> m r) -> s -> m r
    
-- | Conjunction of independent DDs (map of used variables to DD)
newtype AndDDs dd = AndDDs { unAndDDs :: Map IntSet dd } deriving (Eq,Show,Generic,Hashable)

instance Pretty dd => Pretty (AndDDs dd) where
    pretty (AndDDs dds) = vcat $ pretty "&" : (map pretty $ Map.elems dds)

instance (DD m dd) => DDstructure m dd (AndDDs dd) where
    isLeaf proxy (AndDDs dds) = isLeaf' proxy (Just True) (Map.elems dds)
        where
        isLeaf' proxy term [] = term
        isLeaf' proxy term ((DD.isLeaf proxy -> Just True):dds) = isLeaf' proxy term dds
        isLeaf' proxy term ((DD.isLeaf proxy -> Just False):dds) = Just False
        isLeaf' proxy term (dd:dds) = isLeaf' proxy Nothing dds
    singleton dd = do
        sup <- DD.support dd
        return $ AndDDs $ Map.singleton sup dd
    flatten = DD.ands . unAndDDs
    and (AndDDs xs) (AndDDs ys) = normalizeAndDDs $ Map.toList xs ++ Map.toList ys
    or (AndDDs xs) (AndDDs ys) = normalizeAndDDs =<< sequence [ orPair x y | x <- Map.toList xs, y <- Map.toList ys ]
        where orPair (x1,x2) (y1,y2) = DD.or x2 y2 >>= \xy2 -> return (IntSet.union x1 y1,xy2)
    not (AndDDs xs) = ors =<< mapM (singleton <=< DD.not) xs
    evaluate eval (AndDDs x) = liftM Prelude.and $ mapM (DD.evaluate eval) x
    support (AndDDs x) = return $ IntSet.unions $ Map.keys x
    allSat (AndDDs xs) = liftM DD.andsPartialStates $ mapM DD.allSat xs
    allSatComplete (AndDDs xs) = liftM DD.andsPartialStates $ mapM DD.allSatComplete xs
    
    foldCPS ands ors leaf cont (AndDDs xs) = do
        tt <- leaf =<< DD.true
        foldMapCPSM (\i dd b -> ands b =<< leaf dd) tt cont xs

-- | Normalise a list of (support, DD) pairs into an 'AndDDs'.
normalizeAndDDs :: DD m dd => [(IntSet,dd)] -> m (AndDDs dd)
normalizeAndDDs = liftM (AndDDs . Map.fromList) . foldM (insertDD Proxy) []
    where
    insertDD :: DD m dd => Proxy m -> [(IntSet,dd)] -> (IntSet,dd) -> m [(IntSet,dd)]
    insertDD proxy acc s@(_,DD.isLeaf proxy -> Just b) = if b then return acc else return [s]
    insertDD proxy [] (s2,t2) = return [(s2,t2)]
    insertDD proxy ((s1,t1):m) (s2,t2) = if IntSet.disjoint s1 s2
        then liftM ((s1,t1):) (insertDD proxy m (s2,t2))
        else DD.and t1 t2 >>= \t12 -> insertDD proxy m (IntSet.union s1 s2,t12)

-- Conjunction of assignments to independent next variables (map of used next variables to DD)
newtype NextDDs dd = NextDDs { unNextDDs :: Map IntSet dd } deriving (Eq,Show,Generic,Hashable)

instance Pretty dd => Pretty (NextDDs dd) where
    pretty (NextDDs dds) = vcat $ pretty "&" : (map pretty $ Map.elems dds)

-- | Monads tracking next-to-current variable mappings.
class Monad m => NextDDsMonad m where
    dd_nexts :: m (IntMap Int) -- mapping from next ids to past ids
    dd_nextIds :: m IntSet
    dd_nextIds = liftM IntMap.keysSet dd_nexts

instance (DD m dd,NextDDsMonad m) => DDstructure m dd (NextDDs dd) where
    isLeaf proxy (NextDDs dds) = isLeaf' proxy (Just True) (Map.elems dds)
        where
        isLeaf' proxy term [] = term
        isLeaf' proxy term ((DD.isLeaf proxy -> Just True):dds) = isLeaf' proxy term dds
        isLeaf' proxy term ((DD.isLeaf proxy -> Just False):dds) = Just False
        isLeaf' proxy term (dd:dds) = isLeaf' proxy Nothing dds
    singleton dd = do
        nexts <- dd_nextIds
        sup <- DD.support dd
        return $ NextDDs $ Map.singleton (nexts `IntSet.intersection` sup) dd
    flatten = DD.ands . unNextDDs
    and (NextDDs xs) (NextDDs ys) = normalizeNextDDs $ Map.toList xs ++ Map.toList ys
    or (NextDDs xs) (NextDDs ys) = normalizeNextDDs =<< sequence [ orPair x y | x <- Map.toList xs, y <- Map.toList ys ]
        where orPair (x1,x2) (y1,y2) = DD.or x2 y2 >>= \xy2 -> return (IntSet.union x1 y1,xy2)
    not (NextDDs xs) = ors =<< mapM (singleton <=< DD.not) xs
    evaluate eval (NextDDs x) = liftM Prelude.and $ mapM (DD.evaluate eval) x
    support (NextDDs x) = liftM (IntSet.unions . Map.elems) $ mapM DD.support x
    allSat (NextDDs xs) = liftM DD.andsPartialStates $ mapM DD.allSat xs
    allSatComplete (NextDDs xs) = liftM DD.andsPartialStates $ mapM DD.allSatComplete xs
    
    foldCPS ands ors leaf cont (NextDDs xs) = do
        tt <- leaf =<< DD.true
        foldMapCPSM (\i dd b -> ands b =<< leaf dd) tt cont xs

-- | Normalise a list of (support, DD) pairs into a 'NextDDs'.
normalizeNextDDs :: DD m dd => [(IntSet,dd)] -> m (NextDDs dd)
normalizeNextDDs = liftM (NextDDs . Map.fromList) . foldM (insertDD Proxy) []
    where
    insertDD :: DD m dd => Proxy m -> [(IntSet,dd)] -> (IntSet,dd) -> m [(IntSet,dd)]
    insertDD proxy acc s@(_,DD.isLeaf proxy -> Just b) = if b then return acc else return [s]
    insertDD proxy [] (s2,t2) = return [(s2,t2)]
    insertDD proxy ((s1,t1):m) (s2,t2) = if (IntSet.disjoint s1 s2 && Prelude.not (IntSet.null s1 && IntSet.null s2))
        then liftM ((s1,t1):) (insertDD proxy m (s2,t2))
        else DD.and t1 t2 >>= \t12 -> insertDD proxy m (IntSet.union s1 s2,t12)

-- | Variables whose next and current value agree in every solution.
frozenDDs :: (DDstructure m dd s,NextDDsMonad m) => s -> m IntSet
frozenDDs s = do
    vs :: [(Int,Int)] <- liftM IntMap.toList dd_nexts
    sats <- allSat s
    liftM IntSet.unions $ forM vs $ \(next,ori) -> do
        let is = IntSet.fromList [next,ori]
        if all (sameValue next ori) sats
            then return is
            else return IntSet.empty
  where
    sameValue i j m = case (IntMap.lookup i m,IntMap.lookup j m) of
        (Just x,Just y) -> x == y
        otherwise -> False

-- | Identity relation over next/current variable pairs.
dd_identity :: (DDstructure m dd s,NextDDsMonad m) => m s
dd_identity = dd_identity' Proxy

-- | 'dd_identity' with an explicit diagram-type proxy.
dd_identity' :: (DDstructure m dd s,NextDDsMonad m) => Proxy dd -> m s
dd_identity' (proxy::Proxy dd) = do
    nexts <- dd_nexts
    let mkId :: (DDstructure m dd s,NextDDsMonad m) => Int -> Int -> m s
        mkId next ori = do
            vals <- DD.vals next
            eqs <- forM (UV.toList vals) $ \val -> do
                next_i <- DD.var next val
                ori_i <- DD.var ori val
                DD.and next_i ori_i
            singleton =<< DD.ors eqs
    ands =<< K.mapWithKeyM mkId nexts

-- | A tree of And/Or DD partitions, collapsible to a single diagram.
data TreeDDs dd
    = NodeAndDDs (MultiMap (IntMap Int) (TreeDDs dd))
    | NodeOrDDs (MultiMap (IntMap Int) (TreeDDs dd))
    | LeafDDs (IntMap Int) dd
    deriving (Eq,Show,Generic)
    
instance Pretty dd => Pretty (TreeDDs dd) where
    pretty (NodeAndDDs dds) = vcat $ pretty "&" : (map (nest 2 . pretty) $ multiMapElems dds)
    pretty (NodeOrDDs dds) = vcat $ pretty "|" : (map (nest 2 . pretty) $ multiMapElems dds)
    pretty (LeafDDs _ dd) = pretty dd
    
instance Hashable dd => Hashable (TreeDDs dd)

-- | The variables a 'TreeDDs' depends on.
supportTreeDDs :: TreeDDs dd -> IntMap Int
supportTreeDDs (NodeAndDDs dds) = IntMap.unions $ multiMapKeys dds
supportTreeDDs (NodeOrDDs dds) = IntMap.unions $ multiMapKeys dds
supportTreeDDs (LeafDDs vs _) = vs

-- | Number of valuations over the given variable domain sizes.
sizeTrees :: IntMap Int -> Integer
sizeTrees is = if IntMap.null js then 1 else product js
    where js = IntMap.filter (>0) $ IntMap.map toEnum is

-- | Number of valuations a 'TreeDDs' ranges over.
sizeTreeDDs :: TreeDDs dd -> Integer
sizeTreeDDs = sizeTrees . supportTreeDDs

-- | Collapse subtrees under the support-accept budget into leaves.
normalizeTreeDDs :: (DD m dd,TreeDDsMonad m) => TreeDDs dd -> m (TreeDDs dd)
normalizeTreeDDs t = go t
    where
    go :: (DD m dd,TreeDDsMonad m) => TreeDDs dd -> m (TreeDDs dd)
    go x = do
        acc <- treeSupportAccept
        if sizeTreeDDs x <= acc then liftM (uncurry LeafDDs) (flattenTreeDDs x) else go' x
    go' :: (DD m dd,TreeDDsMonad m) => TreeDDs dd -> m (TreeDDs dd)
    go' (NodeAndDDs dds) = liftM NodeAndDDs $ mapM go dds
    go' (NodeOrDDs dds) = liftM NodeOrDDs $ mapM go dds
    go' x@(LeafDDs {}) = return x

-- | Flatten a 'TreeDDs' into a single (support, DD) pair.
flattenTreeDDs :: (DD m dd,TreeDDsMonad m) => TreeDDs dd -> m (IntMap Int,dd)
flattenTreeDDs (NodeAndDDs dds) = do
    dds1 <- mapM (flatten) dds
    let (sups,dds2) = unzip $ multiMapToList dds1
    dd <- DD.ands dds2
    return (IntMap.unions sups,(dd))
flattenTreeDDs (NodeOrDDs dds) = do
    dds1 <- mapM (flatten) dds
    let (sups,dds2) = unzip $ multiMapToList dds1
    dd <- DD.ors dds2
    return (IntMap.unions sups,(dd))
flattenTreeDDs (LeafDDs sup dd) = return (sup,dd)

-- | Monads that can build 'TreeDDs', exposing the support-accept budget a merge may accept.
class TreeDDsMonad (m :: * -> *) where
    treeSupportAccept :: m Integer

-- Try to collapse a whole TreeDDs to one monolithic BDD, respecting its And/Or structure, aborting to Nothing once the attempt would materialise more than `budget` fresh nodes in total.
monoBounded :: (DD m dd,TreeDDsMonad m) => Integer -> TreeDDs dd -> m (Maybe dd)
monoBounded budget t = liftM (fmap fst) (monoBoundedFrom budget t)

-- | 'monoBounded' threading a shared remaining allowance, and returning what is left of it.
monoBoundedFrom :: (DD m dd,TreeDDsMonad m) => Integer -> TreeDDs dd -> m (Maybe (dd,Integer))
monoBoundedFrom remaining (LeafDDs _ dd) = return (Just (dd,remaining))
monoBoundedFrom remaining (NodeAndDDs dds) = combineBounded remaining DD.true DD.andBounded (multiMapElems dds)
monoBoundedFrom remaining (NodeOrDDs dds) = combineBounded remaining DD.false DD.orBounded (multiMapElems dds)

-- | Fold a bounded binary operation over a list of trees.
combineBounded :: (DD m dd,TreeDDsMonad m)
    => Integer -> m dd -> (Integer -> dd -> dd -> m (Maybe dd)) -> [TreeDDs dd] -> m (Maybe (dd,Integer))
combineBounded remaining0 idElem bounded kids = do
    z <- idElem
    nz <- DD.nodecount z
    go (Just (z,nz,remaining0)) kids
    where
    go Nothing _ = return Nothing
    go (Just (acc,_,remaining)) [] = return (Just (acc,remaining))
    go (Just (acc,nacc,remaining)) (k:ks)
        | remaining <= 0 = return Nothing
        | otherwise = do
            -- the child spends from the SAME allowance, and hands back what it did not use
            mk <- monoBoundedFrom remaining k
            case mk of
                Nothing -> return Nothing
                Just (kd,remaining') | remaining' <= 0 -> return Nothing
                                     | otherwise -> do
                    nkd <- DD.nodecount kd
                    mb <- bounded remaining' acc kd
                    case mb of
                        Nothing -> return Nothing
                        Just acc' -> do
                            nacc' <- DD.nodecount acc'
                            let spent = Prelude.max 0 (nacc' - Prelude.max nacc nkd)
                            go (Just (acc',nacc',remaining' - spent)) ks

-- | Cluster a partitioned And-tree: greedily merge children whose supports overlap, each merge accepted only when the bounded apply stays under `budget`.
clusterTreeDDs :: (DD m dd,TreeDDsMonad m) => Integer -> TreeDDs dd -> m (TreeDDs dd)
clusterTreeDDs budget t =
    case t of
        NodeAndDDs m -> do
            let kids = multiMapElems m
            merged <- go [] kids
            case merged of
                [ one ] -> return one
                many -> return (nodeAndDDs many)
        _ -> return t
    where
    supOf = supportTreeDDs

    overlaps a b = IntMap.foldrWithKey (\k _ acc -> acc || IntMap.member k b) False a

    go acc [] = return (reverse acc)
    go acc (k : ks) = do
        acc' <- tryMerge [] acc k
        go acc' ks

    tryMerge tried [] k = return (reverse tried ++ [ k ])
    tryMerge tried (c : cs) k =
        if overlaps (supOf c) (supOf k) then do
            mflat <- monoBounded budget (nodeAndDDs [ c, k ])

            case mflat of
                Just dd -> do
                    sup <- DD.sizes dd
                    return (reverse tried ++ (LeafDDs sup dd : cs))
                Nothing -> tryMerge (c : tried) cs k
        else
            tryMerge (c : tried) cs k

-- | Collapse to a single monolithic leaf if it fits the budget, else Nothing (keep partitioned).
monoTreeDDsBounded :: (DD m dd,TreeDDsMonad m) => Integer -> TreeDDs dd -> m (Maybe (TreeDDs dd))
monoTreeDDsBounded budget0 t = do
    let budget = if budget0 <= 0 then (2 Prelude.^ (40 :: Int)) else budget0
    mb <- monoBounded budget t
    case mb of
        Nothing -> return Nothing
        Just dd -> do { sup <- DD.sizes dd; return (Just (LeafDDs sup dd)) }

-- | Build an And-node from a list of trees, collapsing a singleton.
nodeAndDDs :: [TreeDDs dd] -> (TreeDDs dd)
nodeAndDDs xs = nodeAndDDs' $ multiMapFromList $ map (\x -> (supportTreeDDs x,x)) xs

-- | Build an And-node from a support-keyed multimap, collapsing a singleton.
nodeAndDDs' :: MultiMap (IntMap Int) (TreeDDs dd) -> TreeDDs dd
nodeAndDDs' m = case isSingletonMultiMap m of
    Just (_,y) -> y
    Nothing -> NodeAndDDs m

-- | Build an Or-node from a list of trees, collapsing a singleton.
nodeOrDDs :: [TreeDDs dd] -> (TreeDDs dd)
nodeOrDDs xs = nodeOrDDs' $ multiMapFromList $ map (\x -> (supportTreeDDs x,x)) xs

-- | Build an Or-node from a support-keyed multimap, collapsing a singleton.
nodeOrDDs' :: MultiMap (IntMap Int) (TreeDDs dd) -> TreeDDs dd
nodeOrDDs' m = case isSingletonMultiMap m of
    Just (_,y) -> y
    Nothing -> NodeOrDDs m

-- | Joins TreeDDs with the same support set
joinMultiTreeDDs :: (DD m dd,TreeDDsMonad m) => ([TreeDDs dd] -> m (TreeDDs dd)) -> IntMap Int -> [TreeDDs dd] -> m [TreeDDs dd]
joinMultiTreeDDs join sup xs = do
    acc <- treeSupportAccept
    if sizeTrees sup > acc
        then return xs
        else liftM (:[]) $ join xs

-- | Conjoin two trees, merging supports under the budget.
andTreeDDs :: forall m dd . (DD m dd,TreeDDsMonad m) => TreeDDs dd -> TreeDDs dd -> m (TreeDDs dd)
andTreeDDs x y = do
    let supx = supportTreeDDs x
    let supy = supportTreeDDs y
    if IntMap.disjoint supx supy
        then andTreeDDs' x y -- disjoint supports never merge: the free decomposition win
        else do
            let sup = IntMap.union supx supy
            acc <- treeSupportAccept
            if sizeTrees sup <= acc
                then andDefault x y
                else andTreeDDs' x y

-- | Conjoin two trees without a merge-budget check.
andTreeDDs' :: forall m dd . (DD m dd,TreeDDsMonad m) => TreeDDs dd -> TreeDDs dd -> m (TreeDDs dd)
andTreeDDs' xs@(isLeaf (Proxy @m) -> Just True) ys = return ys
andTreeDDs' xs@(isLeaf (Proxy @m) -> Just False) ys = return xs
andTreeDDs' xs ys@(isLeaf (Proxy @m) -> Just True) = return xs
andTreeDDs' xs ys@(isLeaf (Proxy @m) -> Just False) = return ys
andTreeDDs' (NodeAndDDs xs) (NodeAndDDs ys) = liftM NodeAndDDs $ multiMapUnionWithKeyM (joinMultiTreeDDs andsDefault) xs ys
andTreeDDs' (NodeAndDDs xs) y = liftM NodeAndDDs $ multiMapInsertWithKeyM (joinMultiTreeDDs andsDefault) (supportTreeDDs y) (y) xs
andTreeDDs' x (NodeAndDDs ys) = liftM NodeAndDDs $ multiMapInsertWithKeyM (joinMultiTreeDDs andsDefault) (supportTreeDDs x) (x) ys
andTreeDDs' x y = do
    x' <- normalizeTreeDDs x
    y' <- normalizeTreeDDs y
    return $ nodeAndDDs [x',y']

-- | Disjoin two trees, merging supports under the budget.
orTreeDDs :: forall m dd . (DD m dd,TreeDDsMonad m) => TreeDDs dd -> TreeDDs dd -> m (TreeDDs dd)
orTreeDDs x y = do
    let supx = supportTreeDDs x
    let supy = supportTreeDDs y
    if IntMap.disjoint supx supy
        then orTreeDDs' x y
        else do
            let sup = IntMap.union supx supy
            acc <- treeSupportAccept
            if sizeTrees sup <= acc
                then orDefault x y
                else orTreeDDs' x y

-- | Disjoin two trees without a merge-budget check.
orTreeDDs' :: forall m dd . (DD m dd,TreeDDsMonad m) => TreeDDs dd -> TreeDDs dd -> m (TreeDDs dd)
orTreeDDs' xs@(isLeaf (Proxy @m) -> Just True) ys = return xs
orTreeDDs' xs@(isLeaf (Proxy @m) -> Just False) ys = return ys
orTreeDDs' xs ys@(isLeaf (Proxy @m) -> Just True) = return ys
orTreeDDs' xs ys@(isLeaf (Proxy @m) -> Just False) = return xs
orTreeDDs' (NodeOrDDs xs) (NodeOrDDs ys) = liftM NodeOrDDs $ multiMapUnionWithKeyM (joinMultiTreeDDs orsDefault) xs ys
orTreeDDs' (NodeOrDDs xs) y = liftM NodeOrDDs $ multiMapInsertWithKeyM (joinMultiTreeDDs orsDefault) (supportTreeDDs y) (y) xs
orTreeDDs' x (NodeOrDDs ys) = liftM NodeOrDDs $ multiMapInsertWithKeyM (joinMultiTreeDDs orsDefault) (supportTreeDDs x) (x) ys
orTreeDDs' x y = do
    x' <- normalizeTreeDDs x
    y' <- normalizeTreeDDs y
    return $ nodeOrDDs [x',y']

instance (DD m dd,TreeDDsMonad m) => DDstructure m dd (TreeDDs dd) where
    isLeaf proxy (LeafDDs vs (dd)) = DD.isLeaf proxy dd
    isLeaf proxy _ = Nothing
    
    singleton dd = do
        sup <- DD.sizes dd
        return $ LeafDDs sup (dd)
        
    flatten = liftM (snd) . flattenTreeDDs 
    
    and = andTreeDDs
    or = orTreeDDs
    
    not (NodeAndDDs xs) = liftM NodeOrDDs $ mapM (not) xs
    not (NodeOrDDs xs) = liftM NodeAndDDs $ mapM (not) xs
    not (LeafDDs sup (dd)) = do
        dd' <- DD.not dd
        return $ LeafDDs sup (dd')
    
    equiv x y = do
        nx <- not x
        ny <- not y
        xy <- and x y
        nxy <- and nx ny
        or xy nxy
    
    implies x y = do
        nx <- not x
        or nx y
        
    evaluate eval (NodeAndDDs xs) = liftM Prelude.and $ mapM (evaluate eval) xs
    evaluate eval (NodeOrDDs xs) = liftM Prelude.or $ mapM (evaluate eval ) xs
    evaluate eval (LeafDDs sup (dd)) = DD.evaluate eval dd
    
    support = return . IntMap.keysSet . supportTreeDDs
    
    allSat (NodeAndDDs xs) = liftM DD.andsPartialStates $ mapM (allSat) xs
    allSat (NodeOrDDs xs) = liftM DD.orsPartialStates $ mapM (allSat) xs
    allSat (LeafDDs sup (dd)) = DD.allSat dd
    
    allSatComplete (NodeAndDDs xs) = liftM DD.andsPartialStates $ mapM (allSatComplete) xs
    allSatComplete (NodeOrDDs xs) = liftM DD.orsPartialStates $ mapM (allSatComplete ) xs
    allSatComplete (LeafDDs sup dd) = DD.allSatComplete dd
    
    foldCPS ands ors leaf cont (NodeAndDDs xs) = do
        tt <- leaf =<< DD.true
        foldMultiMapCPSM (\_ dds y -> ands y =<< foldCPS ands ors leaf return dds) tt cont xs
    foldCPS ands ors leaf cont (NodeOrDDs xs) = do
        ff <- leaf =<< DD.false
        foldMultiMapCPSM (\_ dds y -> ors y =<< foldCPS ands ors leaf return dds) ff cont xs
    foldCPS ands ors leaf cont (LeafDDs sup dd) = cont =<< leaf dd

-- | A 'TreeDDs' proxy for a given diagram-type proxy.
proxyTreeDDs :: Proxy dd -> Proxy (TreeDDs dd)
proxyTreeDDs _ = Proxy

-- | An 'AndDDs' proxy for a given diagram-type proxy.
proxyAndDDs :: Proxy dd -> Proxy (AndDDs dd)
proxyAndDDs _ = Proxy

-- | A 'NextDDs' proxy for a given diagram-type proxy.
proxyNextDDs :: Proxy dd -> Proxy (NextDDs dd)
proxyNextDDs _ = Proxy

