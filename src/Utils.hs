-- | Grab-bag of generic helpers.
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
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.Hashable
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.Map.Strict as MapS
import Data.Set (Set(..))
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans
import System.IO.Temp
import System.Directory
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import qualified Data.ByteString.Lazy as BL
import Data.Vector (Vector(..))
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Shelly
import GHC.Generics
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import qualified Data.ByteString.Char8 as BS
import Data.IORef
import Data.Proxy
import Control.Monad.Reader (Reader(..),ReaderT(..))
import qualified Control.Monad.Reader as Reader
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.Identity

import Pretty

-- | Applies f to the last element of a list.
mapLast :: (a -> a) -> [a] -> [a]
mapLast f [] = []
mapLast f [x] = [f x]
mapLast f (x:xs) = x : mapLast f xs

-- | Left fold over a 'Map' with a monadic step function.
{-# INLINE foldlWithKeyM #-}
foldlWithKeyM :: (Ord k,Monad m) => (x -> k -> v -> m x) -> x -> Map k v -> m x
foldlWithKeyM f x m = Map.foldlWithKey (\mx k v -> mx >>= \x -> f x k v) (return x) m

-- | Right fold over a 'Map' with a monadic step function.
{-# INLINE foldrWithKeyM #-}
foldrWithKeyM :: (Ord k,Monad m) => (k -> v -> x -> m x) -> x -> Map k v -> m x
foldrWithKeyM f x m = Map.foldrWithKey (\k v mx -> mx >>= \x -> f k v x) (return x) m

-- | Maps both keys and values of a 'Map'.
{-# INLINE mapWithKey #-}
mapWithKey :: (Ord k,Ord k') => (k -> k') -> (v -> v') -> Map k v -> (Map k' v')
mapWithKey fk fv m = Map.foldlWithKey go Map.empty m
    where
    go xs k v = Map.insert (fk k) (fv v) xs

-- | Maps both components of a pair monadically.
{-# INLINE tupleM #-}
tupleM :: Monad m => (a -> m c) -> (b -> m d) -> (a,b) -> m (c,d)
tupleM f g (a,b) = f a >>= \c -> g b >>= \d -> return (c,d)

-- | Maps all three components of a triple monadically.
{-# INLINE tuple3M #-}
tuple3M :: Monad m => (a -> m c) -> (b -> m d) -> (x -> m y) -> (a,b,x) -> m (c,d,y)
tuple3M f g h (a,b,x) = f a >>= \c -> g b >>= \d -> h x >>= \y -> return (c,d,y)

-- | Maps both sides of an 'Either'.
{-# INLINE (-|-) #-}
(-|-) :: (a -> b) -> (c -> d) -> Either a c -> Either b d
(f -|- g) (Left a) = Left (f a)
(f -|- g) (Right c) = Right (g c)

-- | Maps both components of a pair.
{-# INLINE (><) #-}
(><) :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
(f >< g) (a,b) = (f a,g b)

-- | Swaps a pair's components.
{-# INLINE swap #-}
swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

-- | Boolean implication.
{-# INLINE implies #-}
implies :: Bool -> Bool -> Bool
implies a b = (a<=b)

-- | Returns a 'Map's sole entry, if it has exactly one.
{-# INLINE isSingletonMap #-}
isSingletonMap :: Map k v -> Maybe (k,v)
isSingletonMap m = if Map.size m == 1
    then case Map.toList m of
        [x] -> Just x
    else Nothing
    
-- | Returns an 'IntMap's sole entry, if it has exactly one.
{-# INLINE isSingletonIntMap #-}
isSingletonIntMap :: IntMap v -> Maybe (Int,v)
isSingletonIntMap m = if IntMap.size m == 1
    then case IntMap.toList m of
        [x] -> Just x
    else Nothing
    
-- | Returns a 'MultiMap's sole entry, if it has exactly one.
isSingletonMultiMap :: MultiMap a b -> Maybe (a,b)
isSingletonMultiMap (MultiMap m) = do
    (a,bs) <- isSingletonMap m
    case bs of
        [b] -> Just (a,b)
        otherwise -> Nothing
    
-- | Splits the minimum element off a 'Set'.
{-# INLINE isConsSet #-}
isConsSet :: Set a -> Maybe (a,Set a)
isConsSet xs = case Set.lookupMin xs of
    Nothing -> Nothing
    Just x -> Just (x,Set.deleteMin xs)
    
-- | Splits an element off a 'HashSet'.
{-# INLINE isConsHashSet #-}
isConsHashSet :: Hashable a => HashSet a -> Maybe (a,HashSet a)
isConsHashSet xs = case HashSet.toList xs of
    [] -> Nothing
    (x:_) -> Just (x,HashSet.delete x xs)
    
-- | Returns a 'Set's sole element, if it has exactly one.
{-# INLINE isSingletonSet #-}
isSingletonSet :: Set a -> Maybe a
isSingletonSet xs = if Set.size xs == 1
    then case Set.toList xs of
        [x] -> Just x
    else Nothing
    
-- | An arbitrary element of a 'Set'.
{-# INLINE popSet #-}
popSet :: Set a -> a
popSet xs = case Set.toList xs of
    (x:xs) -> x

-- | An arbitrary element of an 'IntSet'.
{-# INLINE popIntSet #-}
popIntSet :: IntSet -> Int
popIntSet xs = case IntSet.toList xs of
    (x:xs) -> x

-- | The minimum entry of a 'Map'.
{-# INLINE popMap #-}
popMap :: Map k v -> (k,v)
popMap = Map.findMin

-- | The minimum entry of an 'IntMap'.
{-# INLINE popIntMap #-}
popIntMap :: IntMap v -> (Int,v)
popIntMap = IntMap.findMin

-- | An arbitrary element of a 'HashSet'.
{-# INLINE popHashSet #-}
popHashSet :: HashSet a -> a
popHashSet xs = case HashSet.toList xs of
    (x:xs) -> x

-- | Returns a 'HashSet's sole element, if it has exactly one.
{-# INLINE isSingletonHashSet #-}
isSingletonHashSet :: HashSet a -> Maybe a
isSingletonHashSet xs = if HashSet.size xs == 1
    then case HashSet.toList xs of
        [x] -> Just x
    else Nothing

-- | Returns an 'IntSet's sole element, if it has exactly one.
{-# INLINE isSingletonIntSet #-}
isSingletonIntSet :: IntSet -> Maybe Int
isSingletonIntSet xs = if IntSet.size xs == 1
    then case IntSet.toList xs of
        [x] -> Just x
    else Nothing

-- | Looks up a key, crashing if absent.
{-# INLINE unsafeLookup #-}
unsafeLookup :: Ord k => k -> Map k v -> v
unsafeLookup k = fromJustNote "unsafeLookup" . Map.lookup k

-- | Looks up a key in an assoc list, crashing with a note if absent.
{-# INLINE unsafeListLookupNote #-}
unsafeListLookupNote :: Ord k => String -> k -> [(k,v)] -> v
unsafeListLookupNote str k = fromJustNote ("unsafeListLookupNote: " ++ str) . List.lookup k

-- | Looks up a key in an 'IntMap', crashing if absent.
{-# INLINE unsafeIntLookup #-}
unsafeIntLookup :: Int -> IntMap v -> v
unsafeIntLookup k = fromJustNote "unsafeIntLookup" . IntMap.lookup k

-- | Looks up a key, crashing with a note if absent.
{-# INLINE unsafeLookupNote #-}
unsafeLookupNote :: Ord k => String -> k -> Map k v -> v
unsafeLookupNote str k = fromJustNote ("unsafeLookup: " ++ str) . Map.lookup k

-- | Looks up a key in an 'IntMap', crashing with a note if absent.
{-# INLINE unsafeIntLookupNote #-}
unsafeIntLookupNote :: String -> Int -> IntMap v -> v
unsafeIntLookupNote str k = fromJustNote ("unsafeIntLookup: " ++ str) . IntMap.lookup k

-- | Swaps an 'IntMap's keys and values.
flipIntMap :: (Ord v) => IntMap v -> Map v Int
flipIntMap = IntMap.foldlWithKey (\xs k v -> Map.insert v k xs) Map.empty

-- | Swaps a 'Map's keys and values.
flipMapInt :: (Ord k) => Map k Int -> IntMap k
flipMapInt = Map.foldlWithKey (\xs k v -> IntMap.insert v k xs) IntMap.empty

-- | Swaps an 'IntMap Int's keys and values.
flipIntMapInt :: IntMap Int -> IntMap Int
flipIntMapInt = IntMap.foldlWithKey (\xs k v -> IntMap.insert v k xs) IntMap.empty

-- | Inverts an 'IntMap Int', grouping colliding keys.
flipIntMapIntSafe :: IntMap Int -> IntMap IntSet
flipIntMapIntSafe = IntMap.foldrWithKey (\i e -> IntMap.insertWith IntSet.union e (IntSet.singleton i)) IntMap.empty

-- | Unions two 'Map's with a monadic merge function.
mapUnionWithKeyM :: (Monad m,Ord a) => (a -> b -> b -> m b) -> Map a b -> Map a b -> m (Map a b)
mapUnionWithKeyM merge xs ys = foldMapCPSM (\a b m -> mapInsertWithKeyM merge a b m) xs return ys

-- | Insert with a monadic merge.
mapInsertWithKeyM :: (Monad m,Ord a) => (a -> b -> b -> m b) -> a -> b -> Map a b -> m (Map a b)
mapInsertWithKeyM merge a b = MapS.alterF f a
    where
    f Nothing     = return (Just b)
    f (Just bOld) = liftM Just (merge a bOld b)

-- | Whether a list of consecutive integers forms a contiguous range.
isRange :: [Int] -> Maybe (Int,Int)
isRange [] = Nothing
isRange [x] = Just (x,x)
isRange (x:xs) = isRange xs >>= \(i,j) -> if i==x+1 then Just (x,j) else Nothing

-- | First component of a triple.
{-# INLINE fst3 #-}
fst3 :: (a,b,c) -> a
fst3 (a,b,c) = a

-- | Second component of a triple.
{-# INLINE snd3 #-}
snd3 :: (a,b,c) -> b
snd3 (a,b,c) = b

-- | Third component of a triple.
{-# INLINE thr3 #-}
thr3 :: (a,b,c) -> c
thr3 (a,b,c) = c

-- | Second component of a 4-tuple.
{-# INLINE snd4 #-}
snd4 :: (a,b,c,d) -> b
snd4 (a,b,c,d) = b

-- | Combines two monadic actions into a pair.
{-# INLINE mpair #-}
mpair :: Monad m => m a -> m b -> m (a,b)
mpair ma mb = ma >>= \a -> mb >>= \b -> return (a,b)

-- | Maps a 'Set' monadically.
{-# INLINE mapSetM #-}
mapSetM :: (Ord b,Monad m) => (a -> m b) -> Set a -> m (Set b)
mapSetM f = traverseSet f

-- | Traverses a 'Set' with an applicative function.
traverseSet :: (Ord b,Applicative f) => (a -> f b) -> Set a -> f (Set b)
traverseSet f xs = Set.foldl go (pure Set.empty) xs
    where go ys x = liftA2 Set.insert (f x) ys
    
-- | 'mapHashSetM' with an explicit monad proxy.
{-# INLINE mapHashSetM #-}
mapHashSetMProxy :: (Eq b,Hashable b,Monad m) => Proxy m -> (a -> m b) -> HashSet a -> m (HashSet b)
mapHashSetMProxy _ = mapHashSetM

-- | Maps a 'HashSet' monadically.
{-# INLINE mapHashSetMProxy #-}
mapHashSetM :: (Eq b,Hashable b,Monad m) => (a -> m b) -> HashSet a -> m (HashSet b)
mapHashSetM f = traverseHashSet f

-- | Traverses a 'HashSet' with an applicative function.
{-# INLINE traverseHashSet #-}
traverseHashSet :: (Eq b,Hashable b,Applicative f) => (a -> f b) -> HashSet a -> f (HashSet b)
traverseHashSet f xs = foldl go (pure HashSet.empty) xs
    where go ys x = liftA2 HashSet.insert (f x) ys

-- | Sequences a 'HashSet' of applicative actions.
{-# INLINE sequenceHashSet #-}
sequenceHashSet :: (Applicative f,Hashable a) => HashSet (f a) -> f (HashSet a)
sequenceHashSet = traverseHashSet id

-- | Converts a 'Map' 'Int' to an 'IntMap'.
{-# INLINE toIntMap #-}
toIntMap :: Map Int v -> IntMap v 
toIntMap = Map.foldlWithKey (\xs k v -> IntMap.insert k v xs) IntMap.empty
     
-- | Converts an 'IntMap' to a 'Map' 'Int'.
{-# INLINE fromIntMap #-}
fromIntMap :: IntMap v -> Map Int v
fromIntMap = IntMap.foldlWithKey (\xs k v -> Map.insert k v xs) Map.empty
        
-- | Converts an 'IntSet' to a 'Set' 'Int'.
{-# INLINE fromIntSet #-}
fromIntSet :: IntSet -> Set Int
fromIntSet = IntSet.foldl (\xs k -> Set.insert k xs) Set.empty

-- | Converts a 'Set' 'Int' to an 'IntSet'.
{-# INLINE toIntSet #-}
toIntSet :: Set Int -> IntSet
toIntSet = Set.foldl (\xs k -> IntSet.insert k xs) IntSet.empty

-- | Maps a 'Set' to an 'IntSet' with a key function.
{-# INLINE mapSetInt #-}
mapSetInt :: (a -> Int) -> Set a -> IntSet
mapSetInt f = Set.foldl (\xs k -> IntSet.insert (f k) xs) IntSet.empty

-- | Maps under two nested functors.
{-# INLINE fmap2 #-}
fmap2 :: (Functor f,Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 f = fmap (fmap f)

-- | Converts a 'Maybe' to a 'Set'.
maybeToSet :: Ord a => Maybe a -> Set a
maybeToSet Nothing = Set.empty
maybeToSet (Just a) = Set.singleton a

-- | Converts a singleton 'Set' to a 'Maybe'.
maybeFromSet :: Set a -> Maybe a
maybeFromSet = isSingletonSet

-- | Runs an action with a fresh temp file, removing it unless told not to.
withSystemTempUnlessError :: MonadIO m => Bool -> Bool -> FilePath -> (FilePath -> m a) -> m a
withSystemTempUnlessError doRemoveTemps isDebug template go = do
    file <- liftIO $ emptySystemTempFile template
    liftIO $ when isDebug $ putStrLn $ "Created system temp file " ++ show file
    x <- go file
    when doRemoveTemps $ do
        liftIO $ removeFile file
        liftIO $ when isDebug $ putStrLn $ "Removed system temp file " ++ show file
    return x

-- | Creates a temp file and returns a cleanup action for it.
createSystemTemp :: MonadIO m => Bool -> Bool -> FilePath -> (FilePath -> m a) -> m (a,IO ())
createSystemTemp doRemoveTemps isDebug template go = do
    file <- liftIO $ emptySystemTempFile template
    liftIO $ when isDebug $ putStrLn $ "Created system temp file " ++ show file
    x <- go file
    let finish = when doRemoveTemps $ do
            removeFile file
            when isDebug $ putStrLn $ "Removed system temp file " ++ show file
    return (x,finish)

-- | Unions a 'Set' of 'Set's.
{-# INLINE setUnions #-}
setUnions :: Ord a => Set (Set a) -> Set a
setUnions = Set.foldl Set.union Set.empty 

-- | Cross product of two 'Set's, combined by a function.
{-# INLINE crossSetProduct #-}
crossSetProduct :: (Ord c) => (a -> b -> Set c) -> Set a -> Set b -> Set c
crossSetProduct f xs ys = Set.foldl go1 Set.empty xs
    where
    go1 zs x = Set.foldl (go2 x) zs ys
    go2 x zs y = Set.union zs (f x y)

-- | Cross product of two 'IntSet's, combined by a function.
{-# INLINE crossIntSetsProduct #-}
crossIntSetsProduct :: (Ord c) => (Int -> Int -> Set c) -> IntSet -> IntSet -> Set c
crossIntSetsProduct f xs ys = IntSet.foldl go1 Set.empty xs
    where
    go1 zs x = IntSet.foldl (go2 x) zs ys
    go2 x zs y = Set.union zs (f x y)

-- | Cross product of an 'IntSet' and a 'Set', combined by a function.
{-# INLINE crossIntSetProduct #-}
crossIntSetProduct :: (Ord b,Ord c) => (Int -> b -> Set c) -> IntSet -> Set b -> Set c
crossIntSetProduct f xs ys = IntSet.foldl go1 Set.empty xs
    where
    go1 zs x = Set.foldl (go2 x) zs ys
    go2 x zs y = Set.union zs (f x y)
    
-- | Cross product of an 'IntSet' and a 'HashSet', combined by a function.
{-# INLINE crossIntSetProductHash #-}
crossIntSetProductHash :: (Hashable b,Eq b,Hashable c,Eq c) => (Int -> b -> HashSet c) -> IntSet -> HashSet b -> HashSet c
crossIntSetProductHash f xs ys = IntSet.foldl go1 HashSet.empty xs
    where
    go1 zs x = foldl (go2 x) zs ys
    go2 x zs y = HashSet.union zs (f x y)

-- | Cartesian product of two 'Set's.
{-# INLINE setProduct #-}
setProduct :: (Ord a,Ord b) => Set a -> Set b -> Set (a,b)
setProduct = crossSetProduct (\x y -> Set.singleton (x,y)) 

-- | Cartesian product of two 'IntSet's.
{-# INLINE intSetProduct #-}
intSetProduct :: IntSet -> IntSet -> Set (Int,Int)
intSetProduct = crossIntSetsProduct (\x y -> Set.singleton (x,y)) 

-- | Cartesian product of a list of 'IntSet's.
intSetNProductHash :: [IntSet] -> HashSet [Int]
intSetNProductHash [] = HashSet.empty
intSetNProductHash [x] = IntSet.foldl (\acc i -> HashSet.insert [i] acc) HashSet.empty x
intSetNProductHash (x:xs) = crossIntSetProductHash (\a b -> HashSet.singleton (a : b)) x (intSetNProductHash xs)

-- | Decodes a UTF-8 lazy 'ByteString' to a 'String'.
{-# INLINE lazyByteStringToString #-}
lazyByteStringToString :: BL.ByteString -> String
lazyByteStringToString bs =
  case TLE.decodeUtf8' bs of
    Left err   -> error (show err)
    Right text -> TL.unpack text

-- | Encodes lazy 'Text' as UTF-8.
{-# INLINE textToLazyByteString #-}
textToLazyByteString :: TL.Text -> BL.ByteString
textToLazyByteString = TLE.encodeUtf8

-- | Encodes a 'String' as UTF-8.
{-# INLINE stringToLazyByteString #-}
stringToLazyByteString :: String -> BL.ByteString
stringToLazyByteString = textToLazyByteString . TL.pack

-- | Encodes strict 'Text' as UTF-8.
{-# INLINE strictTextToLazyByteString #-}
strictTextToLazyByteString :: T.Text -> BL.ByteString
strictTextToLazyByteString = textToLazyByteString . TL.fromStrict

-- | Zips a list of pairs with a third list, in the second position.
{-# INLINE zipWithSnd #-}
zipWithSnd :: [(a,b)] -> [c] -> [(a,(b,c))]
zipWithSnd xys zs = let (xs,ys) = unzip xys in zip xs (zip ys zs)

-- | Inserts or merges an entry into an assoc list.
updateAssoc :: Eq k => (v -> v -> v) -> k -> v -> [(k,v)] -> [(k,v)]
updateAssoc merge k v [] = [(k,v)]
updateAssoc merge k v ((xk,xv):xs) = if k==xk then (k,merge v xv) : xs else (xk,xv) : updateAssoc merge k v xs

-- | Converts a 'Set' to a 'HashSet'.
{-# INLINE toHashSet #-}
toHashSet :: (Hashable a,Eq a) => Set a -> HashSet a
toHashSet = Set.foldl (flip HashSet.insert) HashSet.empty

-- | Converts 'Bool' to 'Int'.
{-# INLINE boolToInt #-}
boolToInt :: Bool -> Int
boolToInt = fromEnum

-- | Converts 'Int' to 'Bool'.
{-# INLINE intToBool #-}
intToBool :: Int -> Bool
intToBool = (/=0)

-- | Whether all elements of a 'Vector' are equal.
{-# INLINE allEqual #-}
allEqual :: Eq a => Vector a -> Bool
allEqual xs = case V.uncons xs of
    Nothing -> False
    Just (x,xs) -> V.foldl (\b a -> b && a==x) True xs
    
-- | Composes two 'Map's.
{-# INLINE composeMap #-}
composeMap :: (Ord a,Ord b) => Map a b -> Map b c -> Map a c
composeMap xs ys = Map.foldlWithKey go Map.empty xs
    where
    go acc x y = case Map.lookup y ys of
        Just z -> Map.insert x z acc
        Nothing -> acc

-- | Composes an 'IntMap' with a 'Map'.
{-# INLINE composeIntMap #-}
composeIntMap :: (Ord b) => IntMap b -> Map b c -> IntMap c
composeIntMap xs ys = IntMap.foldlWithKey go IntMap.empty xs
    where
    go acc x y = case Map.lookup y ys of
        Just z -> IntMap.insert x z acc
        Nothing -> acc

-- | Composes a 'Map' with an 'IntMap'.
{-# INLINE composeMapInt #-}
composeMapInt :: (Ord a) => Map a Int -> IntMap c -> Map a c
composeMapInt xs ys = Map.foldlWithKey go Map.empty xs
    where
    go acc x y = case IntMap.lookup y ys of
        Just z -> Map.insert x z acc
        Nothing -> acc

-- | Composes two 'IntMap's.
{-# INLINE composeIntMapInt #-}
composeIntMapInt :: IntMap Int -> IntMap c -> IntMap c
composeIntMapInt xs ys = IntMap.foldlWithKey go IntMap.empty xs
    where
    go acc x y = case IntMap.lookup y ys of
        Just z -> IntMap.insert x z acc
        Nothing -> acc

-- | Groups a 'HashSet' by a key function.
{-# INLINE groupHashSetOn #-}
groupHashSetOn :: (Hashable a,Ord b) => (a -> b) -> HashSet a -> Map b (HashSet a)
groupHashSetOn f xs = foldl (\m x -> Map.insertWith HashSet.union (f x) (HashSet.singleton x) m) Map.empty xs 

-- | Groups an 'IntSet' by a key function.
{-# INLINE groupIntSetOn #-}
groupIntSetOn :: (Ord b) => (Int -> b) -> IntSet -> Map b IntSet
groupIntSetOn f xs = IntSet.foldl (\m x -> Map.insertWith IntSet.union (f x) (IntSet.singleton x) m) Map.empty xs 

-- | Groups an 'IntMap's keys by a key function.
{-# INLINE groupIntMapKeysOn #-}
groupIntMapKeysOn :: Ord b => (Int -> a -> b) -> IntMap a -> Map b IntSet
groupIntMapKeysOn f xs = IntMap.foldlWithKey go Map.empty xs
    where
    go acc i a = Map.insertWith IntSet.union (f i a) (IntSet.singleton i) acc

-- | Maps a 'Vector's elements to their indices.
{-# INLINE vectorIndices #-}
vectorIndices :: Ord a => Vector a -> Map a Int
vectorIndices = V.ifoldl (\m i x -> Map.insertWith (error "vectorIndices: duplicated values") x i m) Map.empty

-- | Converts a 'Vector' to an 'IntMap' by index.
{-# INLINE intMapFromVector #-}
intMapFromVector :: Vector a -> IntMap a
intMapFromVector = V.ifoldl (\m i x -> IntMap.insert i x m) IntMap.empty
    
-- | Unions a foldable of 'HashSet's.
unionsHashSet :: Eq a => Foldable t => t (HashSet a) -> HashSet a
unionsHashSet = foldl HashSet.union HashSet.empty

-- | Unions a foldable of 'Set's.
unionsSet :: Ord a => Foldable t => t (Set a) -> Set a
unionsSet = foldl Set.union Set.empty

-- | Unions a foldable of 'IntSet's.
unionsIntSet :: Foldable t => t (IntSet) -> IntSet
unionsIntSet = foldl IntSet.union IntSet.empty

-- | Maximum element by a key function.
maximumOn :: (Ord b,Foldable t) => (a -> b) -> t a -> a
maximumOn f = snd . fromJustNote "maximumOn". foldl go Nothing
    where
    go Nothing x = Just (f x,x)
    go (Just (fy,y)) x = Just $ let fx = f x in if fx > fy then (fx,x) else (fy,y)

-- | Deletes the first element matching a key function.
deleteOn :: Eq b => (a -> b) -> a -> [a] -> [a]
deleteOn g x xs = deleteBy f x xs
    where
    f x y = g x == g y

-- | Left-associates a nested pair.
{-# INLINE assocl #-}
assocl :: (a, (b, c)) -> ((a, b), c)
assocl (a, (b, c)) = ((a, b), c)

-- | Right-associates a nested pair.
{-# INLINE assocr #-}
assocr :: ((a, b), c) -> (a, (b, c))
assocr ((a, b), c) = (a, (b, c))

-- | Unchecked 'Vector' indexing.
{-# INLINE vIndex #-}
vIndex :: String -> V.Vector a -> Int -> a
vIndex msg = V.unsafeIndex

-- | Unchecked unboxed 'Vector' indexing.
{-# INLINE uvIndex #-}
uvIndex :: UV.Unbox a => String -> UV.Vector a -> Int -> a
uvIndex msg = UV.unsafeIndex

-- | Maps values monadically, reusing results for repeated digests.
mapDigestM :: (Eq digest,Monad m) => (a -> m b) -> [(digest,a)] -> m [(digest,b)]
mapDigestM f xs = liftM reverse $ foldM go [] xs
    where
    go acc (h,a) = case List.lookup h acc of
        Just b -> return $ (h,b) : acc
        Nothing -> f a >>= \b -> return $ (h,b) : acc

-- | Runs a Shelly action silently unless debugging.
shellyMode :: Bool -> Shelly.Sh a -> Shelly.Sh a
shellyMode isDebug = if isDebug then id else Shelly.silently

-- a simple trick to compare strings in reverse order
newtype NegString = NegString String deriving (Eq,Show,Generic,Hashable)
instance Ord NegString where
    compare (NegString x) (NegString y) = compare y x

-- | A shell command name with its arguments.
data Command = Command String [CommandArg]
    deriving (Eq,Ord,Show,Generic)
-- | A command argument: a literal or a file path.
type CommandArg = Either String FilePath

instance Pretty Command where
    pretty (Command name args) = pretty name <+> hsep (map (either pretty pretty) args)

-- | Runs a command and returns its stdout.
rawCommand :: Bool -> String -> [String] -> IO String
rawCommand isDebug name args = do
    when isDebug $ putStrLn $ "Running command: " ++ prettyprint (Command name $ map Left args)
    (exit,stdout,stderr) <- if isDebug
        then runProcessWithLiveOutput name args
        else readProcessWithExitCode name args ""
    return stdout

-- | Runs a 'Command' and returns its stdout.
runCommand :: Bool -> Command -> IO String
runCommand isDebug (Command name args) = rawCommand isDebug name (map (either id id) args)

-- | Runs a 'Command', optionally inside a docker container.
runDockerCommand :: Bool -> Maybe String -> Command -> IO String
runDockerCommand isDebug Nothing cmd = Utils.runCommand isDebug cmd
runDockerCommand isDebug (Just container) cmd = do
    (cmd',mounts) <- remountCommand cmd
    let drawMounts = concatMap (\(f,mf) -> ["-v",f++":"++mf]) mounts
    rawCommand isDebug "docker" $ ["run","--rm"] ++ drawMounts ++ [container,"/bin/sh","-c",prettyprint cmd']


-- | Host-to-container path mounts for a docker run.
type Mounts = [(FilePath,FilePath)]

-- | Rewrites a 'Command's file arguments to container-mounted paths.
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

-- | Runs a process, streaming its output live while capturing it.
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

-- | CPS fold over a 'Map' with a monadic step function.
foldMapCPSM :: Monad m => (k -> a -> b -> m b) -> b -> (b -> m r) -> Map k a -> m r
foldMapCPSM f z k xs = go (Map.toList xs) k
  where
    go [] cont = cont z
    go ((i,x):xs) cont = go xs (cont <=< f i x)

-- | CPS fold over a list with a monadic step function.
foldListCPSM :: Monad m => (a -> b -> m b) -> b -> (b -> m r) -> [a] -> m r
foldListCPSM f z k [] = k z
foldListCPSM f z k (x:xs) = foldListCPSM f z (k <=< f x) xs

-- | Lifts a pure 'Reader' into a 'ReaderT'.
identityReader :: Monad m => Reader r a -> ReaderT r m a
identityReader m = Reader.mapReaderT (return . runIdentity) m

-- | Like 'identityReader' but for a computation whose base is IO (run purely). 
ioReader :: Monad m => ReaderT r IO a -> ReaderT r m a
ioReader m = Reader.mapReaderT (return . unsafePerformIO) m

-- | Run an IO-based Reader computation purely (deterministic hash-consed DD ops).
runReaderIO :: r -> ReaderT r IO a -> a
runReaderIO r m = unsafePerformIO (Reader.runReaderT m r)

-- | A map from keys to a group of values.
newtype MultiMap a b = MultiMap { unMultiMap :: Map a [b] }
    deriving (Eq,Ord,Show,Generic,Hashable,Functor,Foldable,Traversable)

-- Groups by key, keeping each group in reverse order of appearance.
multiMapFromList :: Ord a => [(a,b)] -> MultiMap a b
multiMapFromList xs = MultiMap $ MapS.fromListWith (++) $ map (id >< (:[])) xs

-- | Merge sees @right ++ left@: the left map is folded into the right one, one key at a time.
multiMapUnionWithKeyM :: (Monad m,Ord a) => (a -> [b] -> m [b]) -> MultiMap a b -> MultiMap a b -> m (MultiMap a b)
multiMapUnionWithKeyM merge (MultiMap xs) (MultiMap ys) = liftM MultiMap $ mapUnionWithKeyM mergeL xs ys
    where
    mergeL k xs ys = merge k (xs ++ ys)

-- | Merge sees @old ++ [new]@.
multiMapInsertWithKeyM :: (Monad m,Ord a) => (a -> [b] -> m [b]) -> a -> b -> MultiMap a b -> m (MultiMap a b)
multiMapInsertWithKeyM merge a b (MultiMap m) = liftM MultiMap $ mapInsertWithKeyM mergeL a [b] m
    where
    mergeL k xs ys = merge k (xs ++ ys)

-- Built as single right folds.
multiMapToList :: MultiMap a b -> [(a,b)]
multiMapToList (MultiMap xs) = Map.foldrWithKey (\a bs r -> foldr (\b r' -> (a,b) : r') r bs) [] xs

-- | A 'MultiMap's keys.
multiMapKeys :: MultiMap a b -> [a]
multiMapKeys (MultiMap xs) = Map.keys xs

-- | A 'MultiMap's values.
multiMapElems :: MultiMap a b -> [b]
multiMapElems (MultiMap xs) = Map.foldr (\bs r -> bs ++ r) [] xs

-- | CPS fold over a 'MultiMap' with a monadic step function.
foldMultiMapCPSM :: Monad m => (k -> a -> b -> m b) -> b -> (b -> m r) -> MultiMap k a -> m r
foldMultiMapCPSM f z k (MultiMap xs) = foldMapCPSM go z k xs
    where
    go i ys b = foldListCPSM (f i) b return ys

-- | Formats a byte count in human-readable units.
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

-- | Joins strings with a separator.
sepString :: String -> [String] -> String
sepString sep [] = ""
sepString sep [x] = x
sepString sep (x:xs) = x ++ sep ++ sepString sep xs
