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

import Data.IDD (IDD)
import qualified Data.IDD as IDD
import Data.BDD (BDD)
import qualified Data.BDD as BDD
import Utils

--import Debug.Trace as Trace

type Vals dd = UV.Vector (Val dd)

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

type family Val dd = r | r -> dd where
    Val BDD = Bit
    Val GIDD = Int

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
    --fold :: (Int -> V.Vector b -> b) -> (Bool -> b) -> dd -> m b
    --fold' :: (Int -> V.Vector b -> b) -> (Bool -> b) -> dd -> m b
    foldCPS :: (Int -> V.Vector b -> b) -> (Bool -> b) -> (b -> r) -> dd -> m r
    
    allSat :: dd -> m (PartialStates dd)
    allSatComplete :: dd -> m (CompleteStates dd)
    
    var :: Int -> Val dd -> m dd
    var dd_i v = var' dd_i (Set.singleton v)
    var' :: Int -> Set (Val dd) -> m dd
    vals :: Int -> m (Vals dd)
    size :: dd -> m Integer
    
--class Monad m => IDDMonad m where
--    idd_sizes :: m (IntMap Int) -- each variable goes from 0..sz
    
--instance IDDMonad m => DD m IDD where
--    
--    isLeaf _ (IDD.Leaf b) = Just b
--    isLeaf _ _ = Nothing
--    {-# INLINE isLeaf #-}
--    false = return IDD.false
--    {-# INLINE false #-}
--    true = return IDD.true
--    {-# INLINE true #-}
--    and x y = return (x IDD..&&. y)
--    {-# INLINE and #-}
--    or x y = return (x IDD..||. y)
--    {-# INLINE or #-}
--    not = return . IDD.not
--    {-# INLINE not #-}
--    equiv x y = return (x IDD..<=>. y)
--    {-# INLINE equiv #-}
--    implies x y = return (x IDD..=>. y)
--    {-# INLINE implies #-}
--    support = return . IDD.support
--    {-# INLINE support #-}
--    evaluate f = return . IDD.evaluate f
--    {-# INLINE evaluate #-}
--    accum f g h = return . IDD.accum f g h
--    {-# INLINE accum #-}
--    fold f g = return . IDD.fold f g
--    {-# INLINE fold #-}
--    fold' f g = return . IDD.fold' f g
--    {-# INLINE fold' #-}
--    allSat = return . Set.fromList . IDD.allSat
--    {-# INLINE allSat #-}
--    allSatComplete idd = do
--        szs <- idd_sizes
--        return $ Set.fromList $ IDD.allSatComplete szs idd
--    {-# INLINE allSatComplete #-}
--    var' dd_i vs = do
--        szs <- idd_sizes
--        let is = IntSet.fromList [0..unsafeIntLookupNote "varGIDD" dd_i szs]
--        let vs' = IntSet.intersection (toIntSet vs) is
--        if IntSet.null vs'
--            then return IDD.false
--            else return $ IDD.var dd_i (IntSet.size is,vs')
--    {-# INLINE var' #-}
--    vals _ dd_i = do
--        szs <- idd_sizes
--        let sz = unsafeIntLookupNote "valsGIDD" dd_i szs
--        return $ UV.fromList [0..sz]
--    {-# INLINE vals #-}

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
    --fold f g (GIDD idd) = return $ IDD.fold f g idd
    --{-# INLINE fold #-}
    --fold' f g (GIDD idd) = return $ IDD.fold' f g idd
    --{-# INLINE fold' #-}
    foldCPS f g k (GIDD idd) = return $ IDD.foldCPS f g k idd
    {-# INLINE foldCPS #-}
    allSat (GIDD idd) = liftM Set.fromList $ mapM gidd_idxs2vals $ IDD.allSat idd
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
    size (GIDD dd) = do
        szs <- gidd_sizes
        let vs = IDD.support dd
        return $ product $ filter (>0) $ map (\dd_i -> toEnum $ IntSet.size $ unsafeIntLookupNote "sizeGIDD" dd_i szs) (IntSet.toList vs)
    {-# INLINE size #-}

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
    not = return . BDD.not
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
    --fold f b = return . BDD.fold (\i lo hi -> f i $ V.fromList [lo,hi]) b
    --{-# INLINE fold #-}
    --fold' f b = return . BDD.fold' (\i lo hi -> f i $ V.fromList [lo,hi]) b
    --{-# INLINE fold' #-}
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
    size dd = do
        let vs = BDD.support dd
        return $ product $ map (const 2) (IntSet.toList vs)
    {-# INLINE size #-}

type PartialState dd = IntMap (Val dd)
type PartialStates dd = Set (PartialState dd)
type CompleteState dd = PartialState dd
type CompleteStates dd = Set (CompleteState dd)

truePartialStates :: IsVal (Val dd) => PartialStates dd
truePartialStates = Set.singleton IntMap.empty

falsePartialStates :: IsVal (Val dd) => PartialStates dd
falsePartialStates = Set.empty 

andsPartialStates :: (IsVal (Val dd),Foldable t) => t (PartialStates dd) -> (PartialStates dd)
andsPartialStates = foldl andPartialStates truePartialStates

orsPartialStates :: (IsVal (Val dd),Foldable t) => t (PartialStates dd) -> PartialStates dd
orsPartialStates = foldl orPartialStates falsePartialStates

andPartialStates :: IsVal (Val dd) => PartialStates dd -> PartialStates dd -> PartialStates dd
andPartialStates = crossSetProduct (\x y -> maybeToSet $ andPartialState x y)

andPartialState :: IsVal (Val dd) => PartialState dd -> PartialState dd -> Maybe (PartialState dd)
andPartialState x y =
    IntMap.mergeA IntMap.preserveMissing IntMap.preserveMissing match x y
  where
    match = IntMap.zipWithAMatched $ \k vx vy -> if vx==vy
        then Just vx
        else Nothing

orPartialStates :: IsVal (Val dd) => PartialStates dd -> PartialStates dd -> PartialStates dd
orPartialStates = Set.union 

proxyBDD :: Proxy BDD
proxyBDD = Proxy

proxyGIDD :: Proxy GIDD
proxyGIDD = Proxy
