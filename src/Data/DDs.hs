module Data.DDs where
    
import Prelude hiding (not,or,and)
import qualified Prelude
import Control.Monad
import Data.Maybe
import qualified Data.Foldable as Foldable
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Merge.Lazy as IntMap
import Control.Monad.Reader (MonadReader(..))
import qualified Control.Monad.Reader as Reader
import qualified Data.Foldable as Foldable
import Data.Hashable as Hashable
import GHC.Generics as Generics
import Data.Proxy
import qualified Data.Key as K
import qualified Data.Vector.Unboxed as UV
import Prettyprinter

import Data.DD (DD)
import qualified Data.DD as DD
import Utils
import Pretty

--import Debug.Trace as Trace

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
    
    -- ands,ors,leaf,cont
    foldCPS :: (b -> b -> m b) -> (b -> b -> m b) -> (dd -> m b) -> (b -> m r) -> s -> m r
    
-- conjunction of independent DDs (map of used variables to DD)
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

normalizeAndDDs :: DD m dd => [(IntSet,dd)] -> m (AndDDs dd)
normalizeAndDDs = liftM (AndDDs . Map.fromList) . foldM (insertDD Proxy) []
    where
    insertDD :: DD m dd => Proxy m -> [(IntSet,dd)] -> (IntSet,dd) -> m [(IntSet,dd)]
    insertDD proxy acc s@(_,DD.isLeaf proxy -> Just b) = if b then return acc else return [s]
    insertDD proxy [] (s2,t2) = return [(s2,t2)]
    insertDD proxy ((s1,t1):m) (s2,t2) = if IntSet.disjoint s1 s2
        then liftM ((s1,t1):) (insertDD proxy m (s2,t2))
        else DD.and t1 t2 >>= \t12 -> insertDD proxy m (IntSet.union s1 s2,t12)

-- conjunction of assignments to independent next variables (map of used next variables to DD)
newtype NextDDs dd = NextDDs { unNextDDs :: Map IntSet dd } deriving (Eq,Show,Generic,Hashable)

instance Pretty dd => Pretty (NextDDs dd) where
    pretty (NextDDs dds) = vcat $ pretty "&" : (map pretty $ Map.elems dds)

--joinAssigns :: Eq v => IntMap v -> IntMap v -> [IntMap v]
--joinAssigns xs ys = IntMap.mergeA whenL whenR whenLR xs ys
--    where
--    whenL = IntMap.traverseMissing (\i x -> [x])
--    whenR = IntMap.traverseMissing (\i y -> [y])
--    whenLR = IntMap.zipWithAMatched (\i x y -> if x == y then [x] else [])

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

normalizeNextDDs :: DD m dd => [(IntSet,dd)] -> m (NextDDs dd)
normalizeNextDDs = liftM (NextDDs . Map.fromList) . foldM (insertDD Proxy) []
    where
    insertDD :: DD m dd => Proxy m -> [(IntSet,dd)] -> (IntSet,dd) -> m [(IntSet,dd)]
    insertDD proxy acc s@(_,DD.isLeaf proxy -> Just b) = if b then return acc else return [s]
    insertDD proxy [] (s2,t2) = return [(s2,t2)]
    insertDD proxy ((s1,t1):m) (s2,t2) = if (IntSet.disjoint s1 s2 && Prelude.not (IntSet.null s1 && IntSet.null s2))
        then liftM ((s1,t1):) (insertDD proxy m (s2,t2))
        else DD.and t1 t2 >>= \t12 -> insertDD proxy m (IntSet.union s1 s2,t12)

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

dd_identity :: (DDstructure m dd s,NextDDsMonad m) => m s
dd_identity = dd_identity' Proxy

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

supportTreeDDs :: TreeDDs dd -> IntMap Int
supportTreeDDs (NodeAndDDs dds) = IntMap.unions $ multiMapKeys dds
supportTreeDDs (NodeOrDDs dds) = IntMap.unions $ multiMapKeys dds
supportTreeDDs (LeafDDs vs _) = vs

sizeTrees :: IntMap Int -> Integer
sizeTrees is = if IntMap.null js then 1 else product js
    where js = IntMap.filter (>0) $ IntMap.map toEnum is

sizeTreeDDs :: TreeDDs dd -> Integer
sizeTreeDDs = sizeTrees . supportTreeDDs

normalizeTreeDDs :: (DD m dd,TreeDDsMonad m) => TreeDDs dd -> m (TreeDDs dd)
normalizeTreeDDs t = maxTreeDDsSize >>= \maxSize -> normalizeTreeDDs' maxSize t
    where
    normalizeTreeDDs' :: (DD m dd,TreeDDsMonad m) => Integer -> TreeDDs dd -> m (TreeDDs dd)
    normalizeTreeDDs' maxSize x | sizeTreeDDs x <= maxSize = liftM (uncurry LeafDDs) $ flattenTreeDDs x
    normalizeTreeDDs' maxSize (NodeAndDDs dds) = liftM NodeAndDDs $ mapM ((normalizeTreeDDs' maxSize)) dds
    normalizeTreeDDs' maxSize (NodeOrDDs dds) = liftM NodeOrDDs $ mapM ((normalizeTreeDDs' maxSize)) dds
    normalizeTreeDDs' maxSize x@(LeafDDs {}) = return x

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

class TreeDDsMonad m where
    maxTreeDDsSize :: m Integer

nodeAndDDs :: [TreeDDs dd] -> (TreeDDs dd)
nodeAndDDs xs = nodeAndDDs' $ multiMapFromList $ map (\x -> (supportTreeDDs x,x)) xs

nodeAndDDs' :: MultiMap (IntMap Int) (TreeDDs dd) -> TreeDDs dd
nodeAndDDs' m = case isSingletonMultiMap m of
    Just (_,y) -> y
    Nothing -> NodeAndDDs m

nodeOrDDs :: [TreeDDs dd] -> (TreeDDs dd)
nodeOrDDs xs = nodeOrDDs' $ multiMapFromList $ map (\x -> (supportTreeDDs x,x)) xs

nodeOrDDs' :: MultiMap (IntMap Int) (TreeDDs dd) -> TreeDDs dd
nodeOrDDs' m = case isSingletonMultiMap m of
    Just (_,y) -> y
    Nothing -> NodeOrDDs m

-- joins TreeDDs with the same support set
joinMultiTreeDDs :: (DD m dd,TreeDDsMonad m) => ([TreeDDs dd] -> m (TreeDDs dd)) -> IntMap Int -> [TreeDDs dd] -> m [TreeDDs dd]
joinMultiTreeDDs join sup xs = do
    maxSize <- maxTreeDDsSize
    if sizeTrees sup > maxSize
        then return xs
        else liftM (:[]) $ join xs

andTreeDDs :: forall m dd . (DD m dd,TreeDDsMonad m) => TreeDDs dd -> TreeDDs dd -> m (TreeDDs dd)
andTreeDDs x y = do
    maxSize <- maxTreeDDsSize
    let supx = supportTreeDDs x
    let supy = supportTreeDDs y
    let supxy = IntMap.union supx supy
    let sizexy = sizeTrees supxy
    if Prelude.not (IntMap.disjoint supx supy) && sizexy <= maxSize
        then andDefault x y
        else andTreeDDs' x y

andTreeDDs' :: forall m dd . (DD m dd,TreeDDsMonad m) => TreeDDs dd -> TreeDDs dd -> m (TreeDDs dd)
andTreeDDs' xs@(isLeaf (Proxy @m) -> Just True) ys = return ys
andTreeDDs' xs@(isLeaf (Proxy @m) -> Just False) ys = return xs
andTreeDDs' xs ys@(isLeaf (Proxy @m) -> Just True) = return xs
andTreeDDs' xs ys@(isLeaf (Proxy @m) -> Just False) = return ys
andTreeDDs' (NodeAndDDs xs) (NodeAndDDs ys) = liftM NodeAndDDs $ multiMapUnionWithKeyM (joinMultiTreeDDs andsDefault) xs ys
andTreeDDs' (NodeAndDDs xs) y = liftM NodeAndDDs $ multiMapInsertWithKeyM (joinMultiTreeDDs andsDefault) (supportTreeDDs y) (y) xs
andTreeDDs' x (NodeAndDDs ys) = liftM NodeAndDDs $ multiMapInsertWithKeyM (joinMultiTreeDDs andsDefault) (supportTreeDDs x) (x) ys
--andTreeDDs' x@(NodeOrDDs xs) y | supportTreeDDs y `IntMap.isSubmapOf` supportTreeDDs x = liftM nodeOrDDs' $ mapM (\x -> andTreeDDs x y) xs
--andTreeDDs' x y@(NodeOrDDs ys) | supportTreeDDs x `IntMap.isSubmapOf` supportTreeDDs y = liftM nodeOrDDs' $ mapM (\y -> andTreeDDs x y) ys
andTreeDDs' x y = do
    x' <- normalizeTreeDDs x
    y' <- normalizeTreeDDs y
    return $ nodeAndDDs [x',y']

orTreeDDs :: forall m dd . (DD m dd,TreeDDsMonad m) => TreeDDs dd -> TreeDDs dd -> m (TreeDDs dd)
orTreeDDs x y = do
    let supx = supportTreeDDs x
    let supy = supportTreeDDs y
    let supxy = IntMap.union supx supy
    let sizexy = sizeTrees supxy
    maxSize <- maxTreeDDsSize
    if Prelude.not (IntMap.disjoint supx supy) && sizexy <= maxSize
        then orDefault x y
        else orTreeDDs' x y

orTreeDDs' :: forall m dd . (DD m dd,TreeDDsMonad m) => TreeDDs dd -> TreeDDs dd -> m (TreeDDs dd)
orTreeDDs' xs@(isLeaf (Proxy @m) -> Just True) ys = return xs
orTreeDDs' xs@(isLeaf (Proxy @m) -> Just False) ys = return ys
orTreeDDs' xs ys@(isLeaf (Proxy @m) -> Just True) = return ys
orTreeDDs' xs ys@(isLeaf (Proxy @m) -> Just False) = return xs
orTreeDDs' (NodeOrDDs xs) (NodeOrDDs ys) = liftM NodeOrDDs $ multiMapUnionWithKeyM (joinMultiTreeDDs orsDefault) xs ys
orTreeDDs' (NodeOrDDs xs) y = liftM NodeOrDDs $ multiMapInsertWithKeyM (joinMultiTreeDDs orsDefault) (supportTreeDDs y) (y) xs
orTreeDDs' x (NodeOrDDs ys) = liftM NodeOrDDs $ multiMapInsertWithKeyM (joinMultiTreeDDs orsDefault) (supportTreeDDs x) (x) ys
--orTreeDDs' x@(NodeAndDDs xs) y | supportTreeDDs y `IntMap.isSubmapOf` supportTreeDDs x = liftM nodeAndDDs' $ mapM (\x -> orTreeDDs x y) xs
--orTreeDDs' x y@(NodeAndDDs ys) | supportTreeDDs x `IntMap.isSubmapOf` supportTreeDDs y = liftM nodeAndDDs' $ mapM (\y -> orTreeDDs x y) ys
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

proxyTreeDDs :: Proxy dd -> Proxy (TreeDDs dd)
proxyTreeDDs _ = Proxy

proxyAndDDs :: Proxy dd -> Proxy (AndDDs dd)
proxyAndDDs _ = Proxy

proxyNextDDs :: Proxy dd -> Proxy (NextDDs dd)
proxyNextDDs _ = Proxy

