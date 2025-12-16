module Utils where

import Control.Concurrent
import Safe
import System.IO
import System.Exit
import System.Process
import Prettyprinter
import Data.List as List
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Hashable
import Data.Hashable.Lifted
import Data.Foldable
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.RWS.CPS (RWST(..))
import qualified Control.Monad.Trans.RWS.CPS as RWST
import System.IO.Temp
import System.Directory
import System.FilePath.Posix
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import qualified Data.ByteString.Lazy as BL
import Data.Vector (Vector(..))
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Key as K
import qualified Data.Array as A
import qualified Data.Massiv.Array as M
import qualified Data.Massiv.Array.Unsafe as M
import qualified Shelly
import GHC.Generics
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import qualified Control.Monad.State.Strict as StrictState
import System.FilePath.Posix
import qualified Data.ByteString.Char8 as BS
import Data.IORef
import Data.Proxy
import Control.Monad.Reader (Reader(..),ReaderT(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.Identity

import Pretty

intersections :: Ord a => [Set a] -> Set a
intersections [] = Set.empty
intersections [x] = x
intersections (x:xs) = Set.intersection x (intersections xs)

{-# INLINE foldlWithKeyM #-}
foldlWithKeyM :: (Ord k,Monad m) => (x -> k -> v -> m x) -> x -> Map k v -> m x
foldlWithKeyM f x m = Map.foldlWithKey (\mx k v -> mx >>= \x -> f x k v) (return x) m

{-# INLINE foldrWithKeyM #-}
foldrWithKeyM :: (Ord k,Monad m) => (k -> v -> x -> m x) -> x -> Map k v -> m x
foldrWithKeyM f x m = Map.foldrWithKey (\k v mx -> mx >>= \x -> f k v x) (return x) m

{-# INLINE mapWithKey #-}
mapWithKey :: (Ord k,Ord k') => (k -> k') -> (v -> v') -> Map k v -> (Map k' v')
mapWithKey fk fv m = Map.foldlWithKey go Map.empty m
    where
    go xs k v = Map.insert (fk k) (fv v) xs

{-# INLINE tupleM #-}
tupleM :: Monad m => (a -> m c) -> (b -> m d) -> (a,b) -> m (c,d)
tupleM f g (a,b) = f a >>= \c -> g b >>= \d -> return (c,d)

{-# INLINE tuple3M #-}
tuple3M :: Monad m => (a -> m c) -> (b -> m d) -> (x -> m y) -> (a,b,x) -> m (c,d,y)
tuple3M f g h (a,b,x) = f a >>= \c -> g b >>= \d -> h x >>= \y -> return (c,d,y)

{-# INLINE (-|-) #-}
(-|-) :: (a -> b) -> (c -> d) -> Either a c -> Either b d
(f -|- g) (Left a) = Left (f a)
(f -|- g) (Right c) = Right (g c)

{-# INLINE (><) #-}
(><) :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
(f >< g) (a,b) = (f a,g b)

{-# INLINE swap #-}
swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

allEq :: Eq a => [a] -> Bool
allEq [] = True
allEq [x] = True
allEq (x:y:xs) = x==y && allEq (y:xs)

maybeCons :: a -> Maybe [a] -> Maybe [a]
maybeCons x Nothing = Just [x]
maybeCons x (Just xs) = Just (x : xs)

maybeMap :: (Map k v -> Map k v) -> Maybe (Map k v) -> Maybe (Map k v)
maybeMap f Nothing = Just $ f Map.empty
maybeMap f (Just m) = Just $ f m

{-# INLINE implies #-}
implies :: Bool -> Bool -> Bool
implies a b = (a<=b)

{-# INLINE isSingletonMap #-}
isSingletonMap :: Map k v -> Maybe (k,v)
isSingletonMap m = if Map.size m == 1
    then case Map.toList m of
        [x] -> Just x
    else Nothing
    
{-# INLINE isSingletonIntMap #-}
isSingletonIntMap :: IntMap v -> Maybe (Int,v)
isSingletonIntMap m = if IntMap.size m == 1
    then case IntMap.toList m of
        [x] -> Just x
    else Nothing
    
{-# INLINE isConsSet #-}
isConsSet :: Set a -> Maybe (a,Set a)
isConsSet xs = case Set.lookupMin xs of
    Nothing -> Nothing
    Just x -> Just (x,Set.deleteMin xs)
    
{-# INLINE isConsHashSet #-}
isConsHashSet :: Hashable a => HashSet a -> Maybe (a,HashSet a)
isConsHashSet xs = case HashSet.toList xs of
    [] -> Nothing
    (x:_) -> Just (x,HashSet.delete x xs)
    
{-# INLINE isSingletonSet #-}
isSingletonSet :: Set a -> Maybe a
isSingletonSet xs = if Set.size xs == 1
    then case Set.toList xs of
        [x] -> Just x
    else Nothing
    
{-# INLINE popSet #-}
popSet :: Set a -> a
popSet xs = case Set.toList xs of
    (x:xs) -> x

{-# INLINE popIntSet #-}
popIntSet :: IntSet -> Int
popIntSet xs = case IntSet.toList xs of
    (x:xs) -> x

{-# INLINE popMap #-}
popMap :: Map k v -> (k,v)
popMap = Map.findMin

{-# INLINE popIntMap #-}
popIntMap :: IntMap v -> (Int,v)
popIntMap = IntMap.findMin

{-# INLINE popHashSet #-}
popHashSet :: HashSet a -> a
popHashSet xs = case HashSet.toList xs of
    (x:xs) -> x

{-# INLINE isSingletonHashSet #-}
isSingletonHashSet :: HashSet a -> Maybe a
isSingletonHashSet xs = if HashSet.size xs == 1
    then case HashSet.toList xs of
        [x] -> Just x
    else Nothing

{-# INLINE isSingletonIntSet #-}
isSingletonIntSet :: IntSet -> Maybe Int
isSingletonIntSet xs = if IntSet.size xs == 1
    then case IntSet.toList xs of
        [x] -> Just x
    else Nothing

catMaybesMap :: Ord k => Map k (Maybe v) -> Map k v
catMaybesMap = Map.foldrWithKey go Map.empty
    where go k mb acc = case mb of
            Nothing -> acc
            Just v -> Map.insert k v acc
    
{-# INLINE unsafeLookup #-}
unsafeLookup :: Ord k => k -> Map k v -> v
unsafeLookup k = fromJustNote "unsafeLookup" . Map.lookup k

{-# INLINE unsafeListLookupNote #-}
unsafeListLookupNote :: Ord k => String -> k -> [(k,v)] -> v
unsafeListLookupNote str k = fromJustNote ("unsafeListLookupNote: " ++ str) . List.lookup k

{-# INLINE unsafeIntLookup #-}
unsafeIntLookup :: Int -> IntMap v -> v
unsafeIntLookup k = fromJustNote "unsafeIntLookup" . IntMap.lookup k

{-# INLINE unsafeLookupNote #-}
unsafeLookupNote :: Ord k => String -> k -> Map k v -> v
unsafeLookupNote str k = fromJustNote ("unsafeLookup: " ++ str) . Map.lookup k

{-# INLINE unsafeIntLookupNote #-}
unsafeIntLookupNote :: String -> Int -> IntMap v -> v
unsafeIntLookupNote str k = fromJustNote ("unsafeIntLookup: " ++ str) . IntMap.lookup k

nestMap :: (Ord a,Ord b) => Map a (Map b v) -> Map (a,b) v
nestMap m = Map.foldrWithKey go Map.empty m
    where
    go a mb r = Map.foldrWithKey (\b v r -> Map.insert (a,b) v r) r mb

unnestMap :: (Ord a,Ord b) => Map (a,b) v -> Map a (Map b v)
unnestMap m = Map.foldrWithKey go Map.empty m
    where
    go (a,b) v r = Map.insertWith (Map.union) a (Map.singleton b v) r

deleteAt :: Int -> [a] -> [a]
deleteAt i [] | i < 0 = error "deleteAt: negative"
deleteAt 0 (x:xs) = xs
deleteAt i (x:xs) = x : deleteAt (i-1) xs

modifyAt :: Int -> (a -> a) -> [a] -> [a]
modifyAt i f [] = if i < 0 then error "modifyAt: negative" else error ("modifyAt: position "++show i++" not found")
modifyAt 0 f (x:xs) = f x : xs
modifyAt i f (x:xs) = x : modifyAt (i-1) f xs

deletesMap :: Ord k => [k] -> Map k v -> Map k v
deletesMap ks m = foldr Map.delete m ks

flipMap :: (Ord k,Ord v) => Map k v -> Map v k
flipMap = Map.foldlWithKey (\xs k v -> Map.insert v k xs) Map.empty

flipIntMap :: (Ord v) => IntMap v -> Map v Int
flipIntMap = IntMap.foldlWithKey (\xs k v -> Map.insert v k xs) Map.empty

flipMapInt :: (Ord k) => Map k Int -> IntMap k
flipMapInt = Map.foldlWithKey (\xs k v -> IntMap.insert v k xs) IntMap.empty

flipMapSafe :: (Ord k,Ord v) => Map k v -> Map v (Set k)
flipMapSafe = Map.foldrWithKey (\i e -> Map.insertWith Set.union e (Set.singleton i)) Map.empty

flipIntMapInt :: IntMap Int -> IntMap Int
flipIntMapInt = IntMap.foldlWithKey (\xs k v -> IntMap.insert v k xs) IntMap.empty

flipIntMapIntSafe :: IntMap Int -> IntMap IntSet
flipIntMapIntSafe = IntMap.foldrWithKey (\i e -> IntMap.insertWith IntSet.union e (IntSet.singleton i)) IntMap.empty

isRange :: [Int] -> Maybe (Int,Int)
isRange [] = Nothing
isRange [x] = Just (x,x)
isRange (x:xs) = isRange xs >>= \(i,j) -> if i==x+1 then Just (x,j) else Nothing

fromBoolMap :: Map Bool a -> (a,a)
fromBoolMap m = (fromJustNote "fromBoolMap" $ Map.lookup False m,fromJustNote "fromBoolMap" $ Map.lookup True m)

fromBoolMapNote :: String -> Map Bool a -> (a,a)
fromBoolMapNote s m = (fromJustNote ("fromBoolMapFalse: "++s) $ Map.lookup False m,fromJustNote ("fromBoolMapTrue: "++s) $ Map.lookup True m)

passRWST :: (Monad m,Monoid w,Monoid w') => (w -> w') -> RWST r w s m a -> RWST r w' s m a
passRWST f = RWST.mapRWST (liftM (\(a,s,w) -> (a,s,f w)))

withReaderRWST :: Monad m => (r' -> r) -> RWST r w s m a -> RWST r' w s m a
withReaderRWST f = RWST.withRWST (\r' s -> (f r',s))

runWriterRWST :: (Monoid w,Monad m) => RWST r w s m a -> RWST r w s m (a,w)
runWriterRWST m = do
    r <- RWST.ask
    s <- RWST.get
    (a,s',w') <- lift $! RWST.runRWST m r s
    RWST.put s'
    return $! (a,w')

{-# INLINE fst3 #-}
fst3 :: (a,b,c) -> a
fst3 (a,b,c) = a

{-# INLINE snd3 #-}
snd3 :: (a,b,c) -> b
snd3 (a,b,c) = b

{-# INLINE thr3 #-}
thr3 :: (a,b,c) -> c
thr3 (a,b,c) = c

{-# INLINE snd4 #-}
snd4 :: (a,b,c,d) -> b
snd4 (a,b,c,d) = b

{-# INLINE mpair #-}
mpair :: Monad m => m a -> m b -> m (a,b)
mpair ma mb = ma >>= \a -> mb >>= \b -> return (a,b)

--instance Hashable1 NEIntMap where
--    liftHashWithSalt h s m = NEIntMap.foldlWithKey'
--        (\s' k v -> h (hashWithSalt s' k) v)
--        (hashWithSalt s (NEIntMap.size m))
--        m
--instance Hashable v => Hashable (NEIntMap v) where
--    hashWithSalt = hashWithSalt1

digitToBool :: Int -> Bool
digitToBool 0 = False
digitToBool 1 = True
digitToBool i = error $ "digitToBool " ++ show i

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither a Nothing = Left a
maybeToEither a (Just b) = Right b

{-# INLINE mapSetM #-}
mapSetM :: (Ord b,Monad m) => (a -> m b) -> Set a -> m (Set b)
mapSetM f = traverseSet f

traverseSet :: (Ord b,Applicative f) => (a -> f b) -> Set a -> f (Set b)
traverseSet f xs = Set.foldl go (pure Set.empty) xs
    where go ys x = liftA2 Set.insert (f x) ys
    
{-# INLINE mapHashSetM #-}
mapHashSetMProxy :: (Eq b,Hashable b,Monad m) => Proxy m -> (a -> m b) -> HashSet a -> m (HashSet b)
mapHashSetMProxy _ = mapHashSetM

{-# INLINE mapHashSetMProxy #-}
mapHashSetM :: (Eq b,Hashable b,Monad m) => (a -> m b) -> HashSet a -> m (HashSet b)
mapHashSetM f = traverseHashSet f

{-# INLINE traverseHashSet #-}
traverseHashSet :: (Eq b,Hashable b,Applicative f) => (a -> f b) -> HashSet a -> f (HashSet b)
traverseHashSet f xs = foldl go (pure HashSet.empty) xs
    where go ys x = liftA2 HashSet.insert (f x) ys

{-# INLINE sequenceHashSet #-}
sequenceHashSet :: (Applicative f,Hashable a) => HashSet (f a) -> f (HashSet a)
sequenceHashSet = traverseHashSet id

{-# INLINE toIntMap #-}
toIntMap :: Map Int v -> IntMap v 
toIntMap = Map.foldlWithKey (\xs k v -> IntMap.insert k v xs) IntMap.empty
     
{-# INLINE fromIntMap #-}
fromIntMap :: IntMap v -> Map Int v
fromIntMap = IntMap.foldlWithKey (\xs k v -> Map.insert k v xs) Map.empty
        
{-# INLINE fromIntSet #-}
fromIntSet :: IntSet -> Set Int
fromIntSet = IntSet.foldl (\xs k -> Set.insert k xs) Set.empty

{-# INLINE toIntSet #-}
toIntSet :: Set Int -> IntSet
toIntSet = Set.foldl (\xs k -> IntSet.insert k xs) IntSet.empty

{-# INLINE mapSetInt #-}
mapSetInt :: (a -> Int) -> Set a -> IntSet
mapSetInt f = Set.foldl (\xs k -> IntSet.insert (f k) xs) IntSet.empty

{-# INLINE fmap2 #-}
fmap2 :: (Functor f,Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 f = fmap (fmap f)

maybeToSet :: Ord a => Maybe a -> Set a
maybeToSet Nothing = Set.empty
maybeToSet (Just a) = Set.singleton a

maybeFromSet :: Set a -> Maybe a
maybeFromSet = isSingletonSet

withSystemTempUnlessError :: MonadIO m => Bool -> Bool -> FilePath -> (FilePath -> m a) -> m a
withSystemTempUnlessError doRemoveTemps isDebug template go = do
    file <- liftIO $ emptySystemTempFile template
    liftIO $ when isDebug $ putStrLn $ "Created system temp file " ++ show file
    x <- go file
    when doRemoveTemps $ do
        liftIO $ removeFile file
        liftIO $ when isDebug $ putStrLn $ "Removed system temp file " ++ show file
    return x

createSystemTemp :: MonadIO m => Bool -> Bool -> FilePath -> (FilePath -> m a) -> m (a,IO ())
createSystemTemp doRemoveTemps isDebug template go = do
    file <- liftIO $ emptySystemTempFile template
    liftIO $ when isDebug $ putStrLn $ "Created system temp file " ++ show file
    x <- go file
    let finish = when doRemoveTemps $ do
            removeFile file
            when isDebug $ putStrLn $ "Removed system temp file " ++ show file
    return (x,finish)

filterSortedIndices :: [Int] -> [a] -> [a]
filterSortedIndices [] xs = []
filterSortedIndices is [] = error $ "filterSortedIndices: indices not found in list " ++ show is
filterSortedIndices (0:is) (x:xs) = x : filterSortedIndices (map pred is) xs
filterSortedIndices is (x:xs) = filterSortedIndices (map pred is) xs

{-# INLINE setUnions #-}
setUnions :: Ord a => Set (Set a) -> Set a
setUnions = Set.foldl Set.union Set.empty 

{-# INLINE crossSetProduct #-}
crossSetProduct :: (Ord c) => (a -> b -> Set c) -> Set a -> Set b -> Set c
crossSetProduct f xs ys = Set.foldl go1 Set.empty xs
    where
--    go1 :: Set c -> a -> Set c
    go1 zs x = Set.foldl (go2 x) zs ys
--    go2 :: a -> Set c -> b -> Set c
    go2 x zs y = Set.union zs (f x y)

{-# INLINE crossIntSetsProduct #-}
crossIntSetsProduct :: (Ord c) => (Int -> Int -> Set c) -> IntSet -> IntSet -> Set c
crossIntSetsProduct f xs ys = IntSet.foldl go1 Set.empty xs
    where
--    go1 :: Set c -> a -> Set c
    go1 zs x = IntSet.foldl (go2 x) zs ys
--    go2 :: a -> Set c -> b -> Set c
    go2 x zs y = Set.union zs (f x y)

{-# INLINE crossIntSetProduct #-}
crossIntSetProduct :: (Ord b,Ord c) => (Int -> b -> Set c) -> IntSet -> Set b -> Set c
crossIntSetProduct f xs ys = IntSet.foldl go1 Set.empty xs
    where
--    go1 :: Set c -> a -> Set c
    go1 zs x = Set.foldl (go2 x) zs ys
--    go2 :: a -> Set c -> b -> Set c
    go2 x zs y = Set.union zs (f x y)
    
{-# INLINE crossIntSetProductHash #-}
crossIntSetProductHash :: (Hashable b,Eq b,Hashable c,Eq c) => (Int -> b -> HashSet c) -> IntSet -> HashSet b -> HashSet c
crossIntSetProductHash f xs ys = IntSet.foldl go1 HashSet.empty xs
    where
--    go1 :: Set c -> a -> Set c
    go1 zs x = foldl (go2 x) zs ys
--    go2 :: a -> Set c -> b -> Set c
    go2 x zs y = HashSet.union zs (f x y)

{-# INLINE setProduct #-}
setProduct :: (Ord a,Ord b) => Set a -> Set b -> Set (a,b)
setProduct = crossSetProduct (\x y -> Set.singleton (x,y)) 

{-# INLINE intSetProduct #-}
intSetProduct :: IntSet -> IntSet -> Set (Int,Int)
intSetProduct = crossIntSetsProduct (\x y -> Set.singleton (x,y)) 

setNProduct :: (Ord a) => [Set a] -> Set [a]
setNProduct [] = Set.empty
setNProduct [x] = Set.map (:[]) x
setNProduct (x:xs) = crossSetProduct (\a b -> Set.singleton (a : b)) x (setNProduct xs)

intSetNProduct :: [IntSet] -> Set [Int]
intSetNProduct [] = Set.empty
intSetNProduct [x] = IntSet.foldl (\acc i -> Set.insert [i] acc) Set.empty x
intSetNProduct (x:xs) = crossIntSetProduct (\a b -> Set.singleton (a : b)) x (intSetNProduct xs)

intSetNProductHash :: [IntSet] -> HashSet [Int]
intSetNProductHash [] = HashSet.empty
intSetNProductHash [x] = IntSet.foldl (\acc i -> HashSet.insert [i] acc) HashSet.empty x
intSetNProductHash (x:xs) = crossIntSetProductHash (\a b -> HashSet.singleton (a : b)) x (intSetNProductHash xs)

{-# INLINE lazyByteStringToString #-}
lazyByteStringToString :: BL.ByteString -> String
lazyByteStringToString bs =
  case TLE.decodeUtf8' bs of
    Left err   -> error (show err)
    Right text -> TL.unpack text

{-# INLINE textToLazyByteString #-}
textToLazyByteString :: TL.Text -> BL.ByteString
textToLazyByteString = TLE.encodeUtf8

{-# INLINE stringToLazyByteString #-}
stringToLazyByteString :: String -> BL.ByteString
stringToLazyByteString = textToLazyByteString . TL.pack

{-# INLINE strictTextToLazyByteString #-}
strictTextToLazyByteString :: T.Text -> BL.ByteString
strictTextToLazyByteString = textToLazyByteString . TL.fromStrict

{-# INLINE zipWithSnd #-}
zipWithSnd :: [(a,b)] -> [c] -> [(a,(b,c))]
zipWithSnd xys zs = let (xs,ys) = unzip xys in zip xs (zip ys zs)

updateAssoc :: Eq k => (v -> v -> v) -> k -> v -> [(k,v)] -> [(k,v)]
updateAssoc merge k v [] = [(k,v)]
updateAssoc merge k v ((xk,xv):xs) = if k==xk then (k,merge v xv) : xs else (xk,xv) : updateAssoc merge k v xs

{-# INLINE toHashSet #-}
toHashSet :: (Hashable a,Eq a) => Set a -> HashSet a
toHashSet = Set.foldl (flip HashSet.insert) HashSet.empty

{-# INLINE boolToInt #-}
boolToInt :: Bool -> Int
boolToInt = fromEnum

{-# INLINE intToBool #-}
intToBool :: Int -> Bool
intToBool = (/=0)

{-# INLINE allEqual #-}
allEqual :: Eq a => Vector a -> Bool
allEqual xs = case V.uncons xs of
    Nothing -> False
    Just (x,xs) -> V.foldl (\b a -> b && a==x) True xs
    
{-# INLINE composeMap #-}
composeMap :: (Ord a,Ord b) => Map a b -> Map b c -> Map a c
composeMap xs ys = Map.foldlWithKey go Map.empty xs
    where
    go acc x y = case Map.lookup y ys of
        Just z -> Map.insert x z acc
        Nothing -> acc

{-# INLINE composeIntMap #-}
composeIntMap :: (Ord b) => IntMap b -> Map b c -> IntMap c
composeIntMap xs ys = IntMap.foldlWithKey go IntMap.empty xs
    where
    go acc x y = case Map.lookup y ys of
        Just z -> IntMap.insert x z acc
        Nothing -> acc

{-# INLINE composeMapInt #-}
composeMapInt :: (Ord a) => Map a Int -> IntMap c -> Map a c
composeMapInt xs ys = Map.foldlWithKey go Map.empty xs
    where
    go acc x y = case IntMap.lookup y ys of
        Just z -> Map.insert x z acc
        Nothing -> acc

{-# INLINE composeIntMapInt #-}
composeIntMapInt :: IntMap Int -> IntMap c -> IntMap c
composeIntMapInt xs ys = IntMap.foldlWithKey go IntMap.empty xs
    where
    go acc x y = case IntMap.lookup y ys of
        Just z -> IntMap.insert x z acc
        Nothing -> acc

{-# INLINE groupHashSetOn #-}
groupHashSetOn :: (Hashable a,Ord b) => (a -> b) -> HashSet a -> Map b (HashSet a)
groupHashSetOn f xs = foldl (\m x -> Map.insertWith HashSet.union (f x) (HashSet.singleton x) m) Map.empty xs 

{-# INLINE groupIntSetOn #-}
groupIntSetOn :: (Ord b) => (Int -> b) -> IntSet -> Map b IntSet
groupIntSetOn f xs = IntSet.foldl (\m x -> Map.insertWith IntSet.union (f x) (IntSet.singleton x) m) Map.empty xs 

{-# INLINE groupIntMapKeysOn #-}
groupIntMapKeysOn :: Ord b => (Int -> a -> b) -> IntMap a -> Map b IntSet
groupIntMapKeysOn f xs = IntMap.foldlWithKey go Map.empty xs
    where
    go acc i a = Map.insertWith IntSet.union (f i a) (IntSet.singleton i) acc

{-# INLINE vectorIndices #-}
vectorIndices :: Ord a => Vector a -> Map a Int
vectorIndices = V.ifoldl (\m i x -> Map.insertWith (error "vectorIndices: duplicated values") x i m) Map.empty

{-# INLINE intMapFromVector #-}
intMapFromVector :: Vector a -> IntMap a
intMapFromVector = V.ifoldl (\m i x -> IntMap.insert i x m) IntMap.empty
    
{-# INLINE intMapFromUVector #-}
intMapFromUVector :: UV.Unbox a => UV.Vector a -> IntMap a
intMapFromUVector = UV.ifoldl (\m i x -> IntMap.insert i x m) IntMap.empty

{-# INLINE intMapFromArray #-}
intMapFromArray :: A.Array Int v -> IntMap v
intMapFromArray = K.foldlWithKey (\acc i v -> IntMap.insert i v acc) IntMap.empty

{-# INLINE mapFromArray #-}
mapFromArray :: (A.Ix k,Ord k) => A.Array k v -> Map k v
mapFromArray = K.foldlWithKey (\acc i v -> Map.insert i v acc) Map.empty

unionsHashSet :: Eq a => Foldable t => t (HashSet a) -> HashSet a
unionsHashSet = foldl HashSet.union HashSet.empty

unionsWithHashMap :: (Eq k,Foldable t) => (v -> v -> v) -> t (HashMap k v) -> HashMap k v
unionsWithHashMap f = foldl (HashMap.unionWith f) HashMap.empty

unionsSet :: Ord a => Foldable t => t (Set a) -> Set a
unionsSet = foldl Set.union Set.empty

unionsIntSet :: Foldable t => t (IntSet) -> IntSet
unionsIntSet = foldl IntSet.union IntSet.empty

forIntSetM_ :: Monad m => IntSet -> (Int -> m ()) -> m ()
forIntSetM_ is go = IntSet.foldl (\m i -> m >> go i) (return ()) is

maximumOn :: (Ord b,Foldable t) => (a -> b) -> t a -> a
maximumOn f = snd . fromJustNote "maximumOn". foldl go Nothing
    where
    go Nothing x = Just (f x,x)
    go (Just (fy,y)) x = Just $ let fx = f x in if fx > fy then (fx,x) else (fy,y)

isLeft :: Either a b -> Bool
isLeft (Left a) = True
isLeft (Right b) = False

isRight :: Either a b -> Bool
isRight (Left a) = False
isRight (Right b) = True

unLeft :: Either a b -> a
unLeft (Left a) = a
unLeft (Right b) = error "unLeft"

unRight :: Either a b -> b
unRight (Left a) = error "unRight"
unRight (Right b) = b

deleteOn :: Eq b => (a -> b) -> a -> [a] -> [a]
deleteOn g x xs = deleteBy f x xs
    where
    f x y = g x == g y

partitionEither :: [Either a b] -> ([a],[b])
partitionEither [] = ([],[])
partitionEither (e:xys) = case e of
        Left x -> (x:xs,ys)
        Right y -> (xs,y:ys)
    where (xs,ys) = partitionEither xys

{-# INLINE assocl #-}
assocl :: (a, (b, c)) -> ((a, b), c)
assocl (a, (b, c)) = ((a, b), c)

{-# INLINE assocr #-}
assocr :: ((a, b), c) -> (a, (b, c))
assocr ((a, b), c) = (a, (b, c))

{-# INLINE vIndex #-}
vIndex :: String -> V.Vector a -> Int -> a
--vIndex msg v i = fromJustNote ("vIndex " ++ msg) (v V.!? i)
vIndex msg = V.unsafeIndex

{-# INLINE uvIndex #-}
uvIndex :: UV.Unbox a => String -> UV.Vector a -> Int -> a
--uvIndex msg v i = fromJustNote ("uvIndex " ++ msg) (v UV.!? i)
uvIndex msg = UV.unsafeIndex

{-# INLINE mIndex #-}
mIndex :: (M.Manifest r e,M.Source r e) => String -> M.Index ix => M.Array r ix e -> ix -> e
--mIndex msg m i = fromJustNote ("mIndex " ++ msg) $ M.index m i
mIndex msg = M.unsafeIndex

mapDigestM :: (Eq digest,Monad m) => (a -> m b) -> [(digest,a)] -> m [(digest,b)]
mapDigestM f xs = liftM reverse $ foldM go [] xs
    where
    go acc (h,a) = case List.lookup h acc of
        Just b -> return $ (h,b) : acc
        Nothing -> f a >>= \b -> return $ (h,b) : acc

foldDigestM :: (Ord digest,Monad m) => (a -> b -> m b) -> b -> [(digest,a)] -> m b
foldDigestM f z = go Map.empty
    where
    go acc [] = return z
    go acc ((d,x):xs) = case Map.lookup d acc of
        Just fx -> fx =<< go acc xs
        Nothing -> let fx = f x in fx =<< go (Map.insert d fx acc) xs

shellyMode :: Bool -> Shelly.Sh a -> Shelly.Sh a
shellyMode isDebug = if isDebug then id else Shelly.silently

-- a simple trick to compare strings in reverse order
newtype NegString = NegString String deriving (Eq,Show,Generic,Hashable)
instance Ord NegString where
    compare (NegString x) (NegString y) = compare y x

data Command = Command String [CommandArg]
    deriving (Eq,Ord,Show,Generic)
type CommandArg = Either String FilePath

instance Pretty Command where
    pretty (Command name args) = pretty name <+> hsep (map (either pretty pretty) args)

rawCommand :: Bool -> String -> [String] -> IO String
rawCommand isDebug name args = do
    when isDebug $ putStrLn $ "Running command: " ++ prettyprint (Command name $ map Left args)
    (exit,stdout,stderr) <- if isDebug
        then runProcessWithLiveOutput name args
        else readProcessWithExitCode name args ""
    return stdout

runCommand :: Bool -> Command -> IO String
runCommand isDebug (Command name args) = rawCommand isDebug name (map (either id id) args)

runDockerCommand :: Bool -> Maybe String -> Command -> IO String
runDockerCommand isDebug Nothing cmd = Utils.runCommand isDebug cmd
runDockerCommand isDebug (Just container) cmd = do
    (cmd',mounts) <- remountCommand cmd
    let drawMounts = concatMap (\(f,mf) -> ["-v",f++":"++mf]) mounts
    rawCommand isDebug "docker" $ ["run","--rm"] ++ drawMounts ++ [container,"/bin/sh","-c",prettyprint cmd']

--shellyCommand :: Bool -> Command -> Shelly.Sh String
--shellyCommand isDebug (Command name args) = shellyMode isDebug $ liftM T.unpack $ Shelly.run name (map (either T.pack T.pack) args)
--
--shellyDockerCommand :: Bool -> Maybe String -> Command -> Shelly.Sh String
--shellyDockerCommand isDebug Nothing cmd = shellyCommand isDebug cmd
--shellyDockerCommand isDebug (Just container) cmd = shellyMode isDebug $ Shelly.escaping False $ do
--    (cmd',mounts) <- remountCommand cmd
--    when isDebug $ do
--        err <- Shelly.lastStderr
--        liftIO $ T.putStrLn err
--    let drawMounts = concatMap (\(f,mf) -> ["-v",T.pack $ f++":"++mf]) mounts
--    txt <- Shelly.run "docker" $ ["run","--rm"] ++ drawMounts ++ [T.pack container,"/bin/sh","-c",T.pack $ prettyprint cmd']
--    return $ T.unpack txt

type Mounts = [(FilePath,FilePath)]

remountCommand :: Command -> IO (Command,Mounts)
remountCommand (Command name args) = do
    (args',mounts) <- runStateT (mapM remountCommandArg args) []
    return (Command name args',mounts)
  where
    remountCommandArg :: CommandArg -> StateT Mounts IO CommandArg
    remountCommandArg (Left s) = return (Left s)
    remountCommandArg (Right f) = do
        f' <- lift $ canonicalizePath f
        let mntf' = "/mnt" ++ f'
        State.modify $ ((f',mntf'):)
        return $ Right $ mntf'

runProcessWithLiveOutput :: FilePath -> [String] -> IO (ExitCode, String, String)
runProcessWithLiveOutput cmd args = do
    -- Launch the process
    (Just hin, Just hout, Just herr, ph) <- createProcess (proc cmd args)
        { std_in  = CreatePipe
        , std_out = CreatePipe
        , std_err = CreatePipe
        }

    hSetBuffering hout NoBuffering
    hSetBuffering herr NoBuffering

    -- Output accumulators
    outRef <- newIORef BS.empty
    errRef <- newIORef BS.empty

    -- Completion MVars for synchronization
    outDone <- newEmptyMVar
    errDone <- newEmptyMVar

    -- Stdout reader thread
    _ <- forkIO $ do
        let loop = do
                isEOF <- hIsEOF hout
                unless isEOF $ do
                    line <- BS.hGetLine hout
                    BS.putStrLn line
                    hFlush stdout
                    modifyIORef' outRef (\r -> BS.append r $ BS.append line $ BS.pack "\n")
                    loop
        loop
        putMVar outDone ()

    -- Stderr reader thread
    _ <- forkIO $ do
        let loop = do
                isEOF <- hIsEOF herr
                unless isEOF $ do
                    line <- BS.hGetLine herr
                    BS.hPutStrLn stderr line
                    hFlush stderr
                    modifyIORef' errRef (\r -> BS.append r $ BS.append line $ BS.pack "\n")
                    loop
        loop
        putMVar errDone ()

    -- Wait for process to finish
    exitCode <- waitForProcess ph

    -- Wait for output readers to finish
    takeMVar outDone
    takeMVar errDone

    -- Read final accumulated outputs
    out <- BS.unpack <$> readIORef outRef
    err <- BS.unpack <$> readIORef errRef

    return (exitCode, out, err)

strictState :: (Monad m,MonadTrans t,State.MonadState s (t m)) => StrictState.StateT s m a -> t m a
strictState m = do
    s <- State.get
    (a,s') <- lift $ StrictState.runStateT m s
    State.put s'
    return a

foldVectorCPS :: (a -> b -> b) -> b -> (b -> r) -> V.Vector a -> r
foldVectorCPS f z k vec = go 0 k
  where
    len = V.length vec
    go i cont
      | i >= len  = cont z
      | otherwise = go (i + 1) (cont . f (V.unsafeIndex vec i))
      
foldIntMapCPS :: (Int -> a -> b -> b) -> b -> (b -> r) -> IntMap a -> r
foldIntMapCPS f z k xs = go (IntMap.toList xs) k
  where
    go [] cont = cont z
    go ((i,x):xs) cont = go xs (cont . f i x)

foldIntMapCPSM :: Monad m => (Int -> a -> b -> m b) -> b -> (b -> m r) -> IntMap a -> m r
foldIntMapCPSM f z k xs = go (IntMap.toList xs) k
  where
    go [] cont = cont z
    go ((i,x):xs) cont = go xs (cont <=< f i x)

foldMapCPS :: (k -> a -> b -> b) -> b -> (b -> r) -> Map k a -> r
foldMapCPS f z k xs = go (Map.toList xs) k
  where
    go [] cont = cont z
    go ((i,x):xs) cont = go xs (cont . f i x)
    
foldMapCPSM :: Monad m => (k -> a -> b -> m b) -> b -> (b -> m r) -> Map k a -> m r
foldMapCPSM f z k xs = go (Map.toList xs) k
  where
    go [] cont = cont z
    go ((i,x):xs) cont = go xs (cont <=< f i x)

foldListCPS :: (a -> b -> b) -> b -> (b -> r) -> [a] -> r
foldListCPS f z k [] = k z
foldListCPS f z k (x:xs) = foldListCPS f z (k . f x) xs

foldListCPSM :: Monad m => (a -> b -> m b) -> b -> (b -> m r) -> [a] -> m r
foldListCPSM f z k [] = k z
foldListCPSM f z k (x:xs) = foldListCPSM f z (k <=< f x) xs

mapSet2 :: Ord c => (a -> b -> c) -> (Set a -> Set b -> Set c)
mapSet2 f xs ys = Set.fromList $ do
    x <- Set.toList xs
    y <- Set.toList ys
    return $ f x y
    
identityReader :: Monad m => Reader r a -> ReaderT r m a
identityReader m = Reader.mapReaderT (return . runIdentity) m

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

newtype MultiMap a b = MultiMap { unMultiMap :: Map a [b] }
    deriving (Eq,Ord,Show,Generic,Hashable,Functor,Foldable,Traversable)

multiMapFromList :: Ord a => [(a,b)] -> MultiMap a b
multiMapFromList xs = MultiMap $ Map.fromListWith (++) $ map (id >< (:[])) xs

multiMapUnion :: Ord a => MultiMap a b -> MultiMap a b -> MultiMap a b
multiMapUnion (MultiMap xs) (MultiMap ys) = MultiMap $ Map.unionWith (++) xs ys

multiMapToList :: MultiMap a b -> [(a,b)]
multiMapToList (MultiMap xs) = concatMap (\(a,bs) -> map (a,) bs) $ Map.toList xs 

multiMapKeys :: MultiMap a b -> [a]
multiMapKeys (MultiMap xs) = Map.keys xs

multiMapElems :: MultiMap a b -> [b]
multiMapElems (MultiMap xs) = concat $ Map.elems xs

foldMultiMapCPS :: (k -> a -> b -> b) -> b -> (b -> r) -> MultiMap k a -> r
foldMultiMapCPS f z k (MultiMap xs) = foldMapCPS go z k xs
    where
    go i ys b = foldListCPS (f i) z id ys

foldMultiMapCPSM :: Monad m => (k -> a -> b -> m b) -> b -> (b -> m r) -> MultiMap k a -> m r
foldMultiMapCPSM f z k (MultiMap xs) = foldMapCPSM go z k xs
    where
    go i ys b = foldListCPSM (f i) z return ys

formatBytes :: Integer -> String
formatBytes bytes
    | bytes' < kb = show bytes ++ " B"
    | bytes' < mb = showOne (bytes' / kb) ++ " KB"
    | bytes' < gb = showOne (bytes' / mb) ++ " MB"
    | bytes' < tb = showOne (bytes' / gb) ++ " GB"
    | otherwise  = showOne (bytes' / tb) ++ " TB"
  where
    bytes', kb, mb, gb, tb :: Double
    bytes' = fromIntegral bytes
    kb = 1024
    mb = kb * 1024
    gb = mb * 1024
    tb = gb * 1024
    -- show with one decimal (e.g., "1.4")
    showOne :: Double -> String
    showOne x = show (fromIntegral (round (x * 10)) / 10 :: Double)

sepString :: String -> [String] -> String
sepString sep [] = ""
sepString sep [x] = x
sepString sep (x:xs) = x ++ sep ++ sepString sep xs


