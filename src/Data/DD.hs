-- | Backend-agnostic interface to interned decision diagrams.
module Data.DD where

import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector as V
import Data.Foldable as Foldable
import Data.Bit
import Data.Hashable as Hashable
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Merge.Lazy as IntMap
import Data.Set (Set(..))
import qualified Data.Set as Set
import Control.Monad
import qualified Data.Key as K
import Data.Proxy
import Control.DeepSeq (NFData(..))

import Data.IDD (IDD)
import qualified Data.IDD as IDD
import Data.BDD (BDD)
import qualified Data.BDD as BDD
import Utils

-- | Values a diagram variable can take.
type Vals dd = UV.Vector (Val dd)

-- | Values usable as decision-diagram edge labels.
class (Show val,Eq val,Ord val,UV.Unbox val,Hashable val) => IsVal val where
    valToInt :: val -> Int
    valToBool :: val -> Bool
    intToVal :: Int -> val
    boolToVal :: Bool -> val

instance IsVal Int where
    valToInt = id
    {-# INLINE valToInt #-}
    valToBool i = i /= 0
    {-# INLINE valToBool #-}
    intToVal = id
    {-# INLINE intToVal #-}
    boolToVal b = if b then 1 else 0
    {-# INLINE boolToVal #-}

instance IsVal Bool where
    valToInt = boolToInt
    {-# INLINE valToInt #-}
    valToBool = id
    {-# INLINE valToBool #-}
    intToVal 0 = False
    intToVal 1 = True
    intToVal i = error $ "intToValBool: int unsupported " ++ show i
    {-# INLINE intToVal #-}
    boolToVal = id
    {-# INLINE boolToVal #-}
    
instance IsVal Bit where
    valToInt = boolToInt . unBit
    {-# INLINE valToInt #-}
    valToBool = unBit
    {-# INLINE valToBool #-}
    intToVal 0 = Bit False
    intToVal 1 = Bit True
    intToVal i = error $ "intToVal Bit: int unsupported " ++ show i
    {-# INLINE intToVal #-}
    boolToVal = Bit
    {-# INLINE boolToVal #-}

instance Hashable Bit where
    hashWithSalt salt (Bit b) = hashWithSalt salt b
    {-# INLINE hashWithSalt #-}


-- | A one-level view of a decision-diagram node. Children are in value order (binary DDs give
-- @[low,high]@). For complement-edge backends the complement is pushed into the children, so a
-- returned handle is self-contained.
data DDView dd = DDViewLeaf !Bool | DDViewBranch !Int [dd]
    deriving (Eq,Show)

-- | ONE satisfying assignment, as a root-to-leaf descent.
pickSatNode :: DDNode dd => dd -> Maybe (IntMap Int)
pickSatNode = go IntMap.empty
  where
    go acc x = case ddView x of
        DDViewLeaf False -> Nothing
        DDViewLeaf True  -> Just acc
        DDViewBranch v cs -> firstJust [ go (IntMap.insert v k acc) c
                                       | (k, c) <- zip [0 ..] cs, Prelude.not (isFalseLeaf c) ]
    isFalseLeaf c = case ddView c of { DDViewLeaf False -> True ; _ -> False }
    firstJust xs = case [ r | Just r <- xs ] of { (r : _) -> Just r ; [] -> Nothing }

instance NFData GIDD      where rnf x = x `seq` ()
instance NFData BDD.BDD   where rnf x = x `seq` ()

-- | Structural access to a diagram node's shape and identity.
class (Eq dd,Hashable dd,Show dd) => DDNode dd where
    ddView :: dd -> DDView dd
    ddNodeId :: dd -> Int
    ddFalse :: dd
    ddTrue :: dd

instance DDNode BDD where
    ddView (BDD.Leaf b) = DDViewLeaf b
    ddView (BDD.Branch i lo hi) = DDViewBranch i [lo,hi]
    {-# INLINE ddView #-}
    ddNodeId = BDD.nodeId
    {-# INLINE ddNodeId #-}
    ddFalse = BDD.false
    ddTrue = BDD.true

instance DDNode GIDD where
    ddView (GIDD (IDD.Leaf b)) = DDViewLeaf b
    ddView (GIDD (IDD.Branch i bs)) = DDViewBranch i (map GIDD $ V.toList bs)
    {-# INLINE ddView #-}
    ddNodeId (GIDD dd) = IDD.nodeId dd
    {-# INLINE ddNodeId #-}
    ddFalse = GIDD IDD.false
    ddTrue = GIDD IDD.true


-- | Backend-specific value type for a diagram's branches.
type family Val dd = r | r -> dd where
    Val BDD = Bit
    Val GIDD = Int

-- | Monadic decision-diagram backend operations.
class (IsVal (Val dd),Eq dd,Hashable dd,Show dd,Monad m) => DD m dd where
    
    isLeaf :: Proxy m -> dd -> (Maybe Bool)
    false :: m dd
    true :: m dd
    bool :: Bool -> m dd
    bool True = true
    bool False = false
    and :: dd -> dd -> m dd
    or :: dd -> dd -> m dd
    ands :: Foldable.Foldable f => f dd -> m dd
    ands es = true >>= \t -> foldM Data.DD.and t es
    ors :: Foldable.Foldable f => f dd -> m dd
    ors es = false >>= \f -> foldM Data.DD.or f es
    not :: dd -> m dd
    equiv :: dd -> dd -> m dd
    implies :: dd -> dd -> m dd
    support :: dd -> m IntSet
    evaluate :: (Int -> Val dd) -> dd -> m Bool
    accum :: Monoid b => (a -> Int -> V.Vector a) -> (a -> Bool -> b) -> a -> dd -> m b
    foldCPS :: (Int -> V.Vector b -> b) -> (Bool -> b) -> (b -> r) -> dd -> m r
    
    allSat :: dd -> m (PartialStates dd)
    allSatComplete :: dd -> m (CompleteStates dd)
    
    var :: Int -> Val dd -> m dd
    var dd_i v = var' dd_i (Set.singleton v)
    var' :: Int -> Set (Val dd) -> m dd
    vals :: Int -> m (Vals dd)
    sizes :: dd -> m (IntMap Int)
    size :: dd -> m Integer
    -- | Actual number of DD nodes.
    nodecount :: dd -> m Integer
    nodecount = size
    -- Bounded conjunction: Nothing when the result would exceed the node budget.
    andBounded :: Integer -> dd -> dd -> m (Maybe dd)
    andBounded _ x y = Just <$> Data.DD.and x y
    -- Bounded disjunction: Nothing when the result would exceed the node budget.
    orBounded :: Integer -> dd -> dd -> m (Maybe dd)
    orBounded _ x y = Just <$> Data.DD.or x y

    -- | Existential quantification over a set of variables.
    exists :: IntSet -> dd -> m dd
    exists _ _ = error "Data.DD.exists: backend does not implement existential quantification"
    -- | Universal quantification over a set of variables.
    forAll :: IntSet -> dd -> m dd
    forAll _ _ = error "Data.DD.forAll: backend does not implement universal quantification"
    -- | Fused relational product @exists vs. (x AND y)@.
    andExists :: IntSet -> dd -> dd -> m dd
    andExists vs x y = Data.DD.and x y >>= Data.DD.exists vs

    -- | Cofactor under a PARTIAL assignment.
    restrictWith :: (Int -> Maybe (Val dd)) -> dd -> m dd
    restrictWith _ _ = error "Data.DD.restrictWith: backend does not implement restriction"

    -- | Build the node "variable @i@ takes its @k@-th value and then behaves as @cs !! k@".
    ddBranch :: Int -> [dd] -> m dd
    ddBranch i cs = do
        vs <- Data.DD.vals i
        Data.DD.ors =<< sequence [ Data.DD.and c =<< Data.DD.var i v
                                 | (v, c) <- zip (UV.toList vs) cs ]

-- | Supplies each GIDD variable's domain.
class Monad m => GIDDMonad m where
    gidd_sizes :: m (IntMap IntSet) -- each variable has an arbirary set of possible values
    gidd_val2idx :: Int -> m (Int -> Int)
    gidd_val2idx i = do
        szs <- gidd_sizes
        let is = unsafeIntLookupNote "gidd_val2idx" i szs
        return $ \i -> unsafeIntLookupNote "gidd_val2idx" i $ IntMap.fromList $ zip (IntSet.toList is) [0..]
    gidd_idx2val :: Int -> m (Int -> Int)
    gidd_idx2val i = do
        szs <- gidd_sizes
        let is = unsafeIntLookupNote "gidd_idx2val" i szs
        return $ \i -> unsafeIntLookupNote "gidd_idx2val" i $ IntMap.fromList $ zip [0..] (IntSet.toList is)
    gidd_vals2idxs :: IntMap Int -> m (IntMap Int)
    gidd_vals2idxs is = K.mapWithKeyM (\dd_i val -> gidd_val2idx dd_i >>= \f -> return $ f val) is
    gidd_idxs2vals :: IntMap Int -> m (IntMap Int)
    gidd_idxs2vals is = K.mapWithKeyM (\dd_i idx -> gidd_idx2val dd_i >>= \f -> return $ f idx) is
    gidd_vals2idxs' :: m (Int -> Int -> Int)
    gidd_vals2idxs' = do
        szs <- gidd_sizes
        let vals = IntMap.map (\is i -> unsafeIntLookupNote "gidd_vals2idxs'" i $ IntMap.fromList $ zip (IntSet.toList is) [0..]) szs
        return $ \dd_i -> unsafeIntLookupNote "gidd_vals2idxs'" dd_i vals
    gidd_idxs2vals' :: m (Int -> Int -> Int)
    gidd_idxs2vals' = do
        szs <- gidd_sizes
        let idxs = IntMap.map (\is i -> unsafeIntLookupNote "gidd_idxs2vals'" i $ IntMap.fromList $ zip [0..] (IntSet.toList is)) szs
        return $ \dd_i -> unsafeIntLookupNote "gidd_idxs2vals'" dd_i idxs

-- | A generalized (non-binary) interned decision diagram.
newtype GIDD = GIDD { unGIDD :: IDD }
    deriving (Eq,Show,Hashable)

instance GIDDMonad m => DD m GIDD where
    
    isLeaf _ (GIDD (IDD.Leaf b)) = Just b
    isLeaf _ _ = Nothing
    {-# INLINE isLeaf #-}
    false = return $ GIDD IDD.false
    {-# INLINE false #-}
    true = return $ GIDD IDD.true
    {-# INLINE true #-}
    and (GIDD x) (GIDD y) = return (GIDD $ x IDD..&&. y)
    {-# INLINE and #-}
    or (GIDD x) (GIDD y) = return (GIDD $ x IDD..||. y)
    {-# INLINE or #-}
    ands es = return $ GIDD $ IDD.and (map unGIDD $ Foldable.toList es)
    {-# INLINE ands #-}
    ors es = return $ GIDD $ IDD.or (map unGIDD $ Foldable.toList es)
    {-# INLINE ors #-}
    not (GIDD x) = return (GIDD $ IDD.not x)
    {-# INLINE not #-}
    equiv (GIDD x) (GIDD y) = return (GIDD $ x IDD..<=>. y)
    {-# INLINE equiv #-}
    implies (GIDD x) (GIDD y) = return (GIDD $ x IDD..=>. y)
    {-# INLINE implies #-}
    support (GIDD idd) = return $ IDD.support idd
    {-# INLINE support #-}
    evaluate map_vals (GIDD dd) = do
        f <- gidd_vals2idxs'
        let map_idxs dd_i = f dd_i $ map_vals dd_i
        return $ IDD.evaluate map_idxs dd
    {-# INLINE evaluate #-}
    accum f g h (GIDD idd) = return $ IDD.accum f g h idd
    {-# INLINE accum #-}
    foldCPS f g k (GIDD idd) = return $ IDD.foldCPS f g k idd
    {-# INLINE foldCPS #-}
    allSat (GIDD idd) = do
        conv <- gidd_idxs2vals'
        return $ Set.fromList $ IDD.allSatWith conv idd
    {-# INLINE allSat #-}
    allSatComplete (GIDD idd) = do
        szs <- gidd_sizes
        liftM Set.fromList $ mapM gidd_idxs2vals $ IDD.allSatComplete (IntMap.map IntSet.size szs) idd
    {-# INLINE allSatComplete #-}
    var' dd_i vs = do
        szs <- gidd_sizes
        let sz = unsafeIntLookupNote "varGIDD" dd_i szs
        let vs' = IntSet.intersection (toIntSet vs) sz
        if IntSet.null vs'
            then return $ GIDD IDD.false
            else do
                let fromVals = IntMap.fromList $ zip (IntSet.toList sz) [0..]
                let fromVal v = unsafeIntLookupNote "varGIDD" v fromVals
                return $ GIDD $ IDD.var dd_i (IntSet.size sz,IntSet.map fromVal vs')
    {-# INLINE var' #-}
    vals dd_i = do
        szs <- gidd_sizes
        let sz = unsafeIntLookupNote "valsGIDD" dd_i szs
        return $ UV.fromList $ IntSet.toList sz
    {-# INLINE vals #-}
    sizes (GIDD dd) = do
        szs <- gidd_sizes
        let vs = IDD.support dd
        return $ IntMap.fromSet (\dd_i -> IntSet.size $ unsafeIntLookupNote "sizeGIDD" dd_i szs) vs
    {-# INLINE sizes #-}
    size (GIDD dd) = do
        szs <- gidd_sizes
        let vs = IDD.support dd
        return $ product $ filter (>0) $ map (\dd_i -> toEnum $ IntSet.size $ unsafeIntLookupNote "sizeGIDD" dd_i szs) (IntSet.toList vs)
    {-# INLINE size #-}
    nodecount (GIDD dd) = return $ toInteger $ IDD.numNodes dd
    exists vs (GIDD dd) = return $ GIDD (IDD.existsSet vs dd)
    {-# INLINE exists #-}
    forAll vs (GIDD dd) = return $ GIDD (IDD.forAllSet vs dd)
    {-# INLINE forAll #-}
    andExists vs (GIDD x) (GIDD y) = return $ GIDD (IDD.andExistsSet vs x y)

    ddBranch i cs = return $ GIDD (IDD.Branch i (V.fromList (map unGIDD cs)))
    {-# INLINE andExists #-}
    {-# INLINE nodecount #-}
    andBounded budget (GIDD x) (GIDD y) = return $ fmap GIDD $ IDD.andBounded (fromInteger budget) x y
    {-# INLINE andBounded #-}
    orBounded budget (GIDD x) (GIDD y) = return $ fmap GIDD $ IDD.orBounded (fromInteger budget) x y
    {-# INLINE orBounded #-}
    restrictWith f (GIDD dd) = do
        v2i <- gidd_vals2idxs'
        return $ GIDD $ IDD.restrictWithIdx (\i -> fmap (v2i i) (f i)) dd

-- | Supplies the set of variable ids in scope.
class Monad m => BDDMonad m where
    bdd_ids :: m IntSet -- all variables

instance BDDMonad m => DD m BDD where
    
    isLeaf _ (BDD.Leaf b) = Just b
    isLeaf _ _ = Nothing
    {-# INLINE isLeaf #-}
    false = return BDD.false
    {-# INLINE false #-}
    true = return BDD.true
    {-# INLINE true #-}
    and x y = return (x BDD..&&. y)
    {-# INLINE and #-}
    or x y = return (x BDD..||. y)
    {-# INLINE or #-}
    ands = return . BDD.and . Foldable.toList
    {-# INLINE ands #-}
    ors = return . BDD.or . Foldable.toList
    {-# INLINE ors #-}
    not = return . BDD.not
    restrictWith f = return . BDD.restrictWith (\i -> fmap (\(Bit b) -> b) (f i))
    {-# INLINE restrictWith #-}
    {-# INLINE not #-}
    equiv x y = return (x BDD..<=>. y)
    {-# INLINE equiv #-}
    implies x y = return (x BDD..=>. y)
    {-# INLINE implies #-}
    support = return . BDD.support
    {-# INLINE support #-}
    evaluate f = return . BDD.evaluate (unBit . f)
    {-# INLINE evaluate #-}
    accum f g h = return . BDD.accum f g h
    {-# INLINE accum #-}
    foldCPS f b k = return . BDD.foldCPS (\i lo hi -> f i $ V.fromList [lo,hi]) b k
    {-# INLINE foldCPS #-}
    allSat = return . Set.fromList . map (IntMap.map Bit) . BDD.allSat
    {-# INLINE allSat #-}
    allSatComplete bdd = do
        is <- bdd_ids
        return $ Set.fromList $ map (IntMap.map Bit) $ BDD.allSatComplete is bdd
    {-# INLINE allSatComplete #-}
    var dd_i (Bit b) = return $ (if b then id else BDD.not) (BDD.var dd_i)
    {-# INLINE var #-}
    var' dd_i vs = case Set.toList vs of
        [] -> return BDD.false
        [v] -> var dd_i v
        otherwise -> return BDD.true
    vals dd_i = return $ UV.fromList [Bit False,Bit True]
    {-# INLINE vals #-}
    sizes dd = do
        let vs = BDD.support dd
        return $ IntMap.fromSet (const 2) vs
    {-# INLINE sizes #-}
    size dd = do
        let vs = BDD.support dd
        return $ product $ map (const 2) (IntSet.toList vs)
    {-# INLINE size #-}
    nodecount dd = return $ toInteger $ BDD.numNodes dd
    {-# INLINE nodecount #-}
    andBounded budget x y = return $ BDD.andBounded (fromInteger budget) x y
    orBounded budget x y = return $ BDD.orBounded (fromInteger budget) x y
    exists vs dd = return $ BDD.existsSet vs dd
    {-# INLINE exists #-}
    forAll vs dd = return $ BDD.forAllSet vs dd
    {-# INLINE forAll #-}
    andExists vs x y = return $ BDD.andExistsSet vs x y

    ddBranch i [lo,hi] = return $ BDD.Branch i lo hi
    ddBranch i cs = error $ "Data.DD.ddBranch: BDD is binary, got "
                         ++ show (length cs) ++ " children for variable " ++ show i
    {-# INLINE andExists #-}


-- | A partial variable assignment.
type PartialState dd = IntMap (Val dd)
-- | A set of partial states.
type PartialStates dd = Set (PartialState dd)
-- | A complete variable assignment.
type CompleteState dd = PartialState dd
-- | A set of complete states.
type CompleteStates dd = Set (CompleteState dd)

-- | The always-true partial-state set.
truePartialStates :: IsVal (Val dd) => PartialStates dd
truePartialStates = Set.singleton IntMap.empty

-- | The always-false partial-state set.
falsePartialStates :: IsVal (Val dd) => PartialStates dd
falsePartialStates = Set.empty 

-- | Conjoin partial-state sets.
andsPartialStates :: (IsVal (Val dd),Foldable t) => t (PartialStates dd) -> (PartialStates dd)
andsPartialStates = foldl andPartialStates truePartialStates

-- | Disjoin partial-state sets.
orsPartialStates :: (IsVal (Val dd),Foldable t) => t (PartialStates dd) -> PartialStates dd
orsPartialStates = foldl orPartialStates falsePartialStates

-- | Conjoin two partial-state sets.
andPartialStates :: IsVal (Val dd) => PartialStates dd -> PartialStates dd -> PartialStates dd
andPartialStates xs ys = crossSetProduct (\x y -> maybeToSet $ andPartialState x y) xs ys

-- | Merge two partial states, or 'Nothing' on conflict.
andPartialState :: IsVal (Val dd) => PartialState dd -> PartialState dd -> Maybe (PartialState dd)
andPartialState x y =
    IntMap.mergeA IntMap.preserveMissing IntMap.preserveMissing match x y
  where
    match = IntMap.zipWithAMatched $ \k vx vy -> if vx==vy
        then Just vx
        else Nothing

-- | Union two partial-state sets.
orPartialStates :: IsVal (Val dd) => PartialStates dd -> PartialStates dd -> PartialStates dd
orPartialStates = Set.union 

-- | Add a binding to a partial state, or 'Nothing' on conflict.
insertPartialState :: IsVal (Val dd) => Int -> Val dd -> PartialState dd -> Maybe (PartialState dd)
insertPartialState dd_i val st = case IntMap.lookup dd_i st of
    Nothing -> Just $ IntMap.insert dd_i val st
    Just v -> if val==v then Just st else Nothing

-- | Proxy for the 'BDD' backend.
proxyBDD :: Proxy BDD
proxyBDD = Proxy

-- | Proxy for the 'GIDD' backend.
proxyGIDD :: Proxy GIDD
proxyGIDD = Proxy

