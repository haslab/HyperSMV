-- | Hash-consed IDD node type, its 'Sig' functor, memoising folds, and graph conversion.
module Data.IDD.Internal
  (
  -- * Low level node type
    Node (Leaf, Branch)
  , nodeId
  , numNodes

  -- * Fold
  , fold
  , fold'
  , mkFold'Op
  , accum
  , foldCPS, mkFoldCPSOp

  -- * (Co)algebraic structure
  , Sig (..)

  -- * Graph
  , Graph
  , toGraph
  , toGraph'
  , foldGraph
  , foldGraphNodes
  ) where

import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.Functor.Identity
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.Interned
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.STRef
import GHC.Generics
import GHC.Stack
import Data.Vector (Vector(..))
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.IntSet as IntSet
import Data.Vector.Instances ()


-- ------------------------------------------------------------------------

-- | Hash-consed node types in IDD 
data Node = Node {-# UNPACK #-} !Id (UNode)
  deriving (Show)

instance Eq (Node) where
  Node i _ == Node j _ = i == j

instance Hashable (Node) where
  hashWithSalt s (Node i _) = hashWithSalt s i

pattern Leaf :: Bool -> Node
pattern Leaf b <- (unintern -> ULeaf b) where
  Leaf b = intern (ULeaf b)

pattern Branch :: Int -> Vector Node -> Node
pattern Branch ind bs <- (unintern -> UBranch ind bs) where
  Branch ind bs = intern (UBranch ind bs)

{-# COMPLETE Leaf, Branch #-}

-- | Uninterned representation of a 'Node'.
data UNode
  = ULeaf {-# UNPACK #-} !Bool
  | UBranch {-# UNPACK #-} !Int (Vector Node)
  deriving (Show)

instance Interned (Node) where
  type Uninterned (Node) = UNode
  data Description (Node)
    = DLeaf {-# UNPACK #-} !Bool
    | DBranch {-# UNPACK #-} !Int !(UV.Vector Id)
    deriving (Eq, Generic)
  describe (ULeaf b) = DLeaf b
  describe (UBranch x bs) = DBranch x (UV.convert $ V.map nodeId bs)
  identify = Node
  cache = nodeCache

instance Hashable (Description (Node))

instance Uninternable (Node) where
  unintern (Node _ uformula) = uformula

-- | One global intern table per Node type. Sound because 'describe' is TOTAL (every field of 'UNode' reaches the 'Description') and exactly one wrapper chain interprets these nodes.
nodeCache :: Cache (Node)
nodeCache = mkCache
{-# NOINLINE nodeCache #-}

-- | The interned identifier of a node.
nodeId :: Node -> Id
nodeId (Node id_ _) = id_

-- | Number of distinct nodes viewed as a rooted DAG (hash-consed, counted by Id).
numNodes :: Node -> Int
numNodes root = IntSet.size (go IntSet.empty root)
  where
    go seen (Node i u)
      | i `IntSet.member` seen = seen
      | otherwise = case u of
          ULeaf _        -> IntSet.insert i seen
          UBranch _ kids -> V.foldl' go (IntSet.insert i seen) kids

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Signature functor of binary decision trees, GIDD b, and ZIDD.
data Sig a
  = SLeaf !Bool
  | SBranch !Int (Vector a)
  deriving (Eq,Ord,Read,Show,Generic,Functor,Traversable,Foldable)

instance (Hashable a) => Hashable (Sig a)

-- ------------------------------------------------------------------------

-- | Fold over the graph structure of Node.
--
-- It takes two functions that substitute 'Branch'  and 'Leaf' respectively.
--
-- Note that its type is isomorphic to @('Sig' a -> a) -> 'Node' -> a@.
fold :: (Int -> Vector a -> a) -> (Bool -> a) -> Node -> a
fold br lf bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f p = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> case p of
            (Leaf b) -> return (lf b)
            (Branch top cs) -> do
                  rs <- traverse (unsafeInterleaveST . f) cs
                  let ret = br top rs
                  H.insert h p ret  -- Note that H.insert is value-strict
                  return ret
  f bdd

-- | Strict version of 'fold'
fold' :: (Int -> Vector a -> a) -> (Bool -> a) -> Node -> a
fold' br lf dd = runST $ do
  op <- mkFold'Op br lf
  op dd

-- | Build a strict memoising fold over a 'Node'.
mkFold'Op :: (Int -> Vector a -> a) -> (Bool -> a) -> ST s (Node -> ST s a)
mkFold'Op br lf = do
  h <- C.newSized defaultTableSize
  let f p = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> case p of
            (Leaf b) -> return $! lf b
            (Branch top cs) -> do
                  rs <- traverse f cs
                  let ret = br top rs
                  H.insert h p ret  -- Note that H.insert is value-strict
                  return ret
  return f

-- | CPS version of a memoising fold over a 'Node'.
foldCPS :: (Int -> Vector b -> b) -> (Bool -> b) -> (b -> r) -> Node -> r
foldCPS br lf k bdd = runST $ do
    op <- mkFoldCPSOp (\i cs -> return $! br i cs) (\b -> return $! lf b) (\b -> return $! k b)
    op bdd

-- | Build a CPS memoising fold over a 'Node'.
mkFoldCPSOp :: (Int -> Vector b -> ST s b) -> (Bool -> ST s b) -> (b -> ST s r) -> ST s (Node -> ST s r)
mkFoldCPSOp br lf k = do
    h <- C.newSized defaultTableSize
    let f (Leaf b) k = k =<< lf b
        f p@(Branch top cs) k = do
            m <- H.lookup h p
            case m of
              Just r -> k $! r
              Nothing -> do
                  let sz = V.length cs
                  let go i acc = if i >= sz
                          then do r <- br top acc
                                  H.insert h p r
                                  k $! r
                          else f (V.unsafeIndex cs i) $ \c' -> go (i+1) (V.snoc acc c')
                  go 0 V.empty
    return $! flip f k

-- | Fold a 'Node' top-down, combining leaf values.
accum :: Monoid b => (a -> Int -> Vector a) -> (a -> Bool -> b) -> a -> Node -> b
accum br lf a dd = runST $ do
    op <- mkAccum br lf a
    op dd

-- | Build the ST operation underlying 'accum'.
mkAccum :: Monoid b => (a -> Int -> Vector a) -> (a -> Bool -> b) -> a -> ST s (Node -> ST s b)
mkAccum br lf a = do
    ref <- newSTRef mempty
    let f a p = case p of
            Leaf b -> modifySTRef' ref (`mappend` lf a b)
            Branch top cs -> do
                mapM_ (\(a,c) -> f a c) $ V.zip (br a top) cs
    return (\p -> f a p >> readSTRef ref)

-- ------------------------------------------------------------------------

-- | Graph where nodes are decorated using a functor @f@.
--
-- The occurrences of the parameter of @f@ represent out-going edges.
type Graph f = IntMap (f Int)

-- | Convert a node into a pointed graph
--
-- Nodes @0@ and @1@ are reserved for @SLeaf False@ and @SLeaf True@ even if
-- they are not actually used. Therefore the result may be larger than
-- 'numNodes' if the leaf nodes are not used.
toGraph :: Node -> (Graph (Sig), Int)
toGraph bdd =
  case toGraph' (Identity bdd) of
    (g, Identity v) -> (g, v)

-- | Convert multiple nodes into a graph
toGraph' :: (Traversable t) => t (Node) -> (Graph (Sig), t Int)
toGraph' bs = runST $ do
  h <- C.newSized defaultTableSize
  counter <- newSTRef 0
  ref <- newSTRef $ IntMap.empty

  let f p@(Leaf x) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            n <- readSTRef counter
            writeSTRef counter $! n+1
            H.insert h p n
            modifySTRef' ref (IntMap.insert n (SLeaf x))
            return n
      f p@(Branch x cs) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            rs <- traverse f cs
            n <- readSTRef counter
            writeSTRef counter $! n+1
            H.insert h p n
            modifySTRef' ref (IntMap.insert n (SBranch x rs))
            return n

  vs <- mapM f bs
  g <- readSTRef ref
  return (g, vs)

-- | Fold over pointed graph
foldGraph :: (Functor f, HasCallStack) => (f a -> a) -> (Graph f, Int) -> a
foldGraph f (g, v) =
  case IntMap.lookup v (foldGraphNodes f g) of
    Just x -> x
    Nothing -> error ("foldGraphNodes: invalid node id " ++ show v)

-- | Fold over graph nodes
foldGraphNodes :: (Functor f, HasCallStack) => (f a -> a) -> Graph f -> IntMap a
foldGraphNodes f m = ret
  where
    ret = IntMap.map (f . fmap h) m
    h v =
      case IntMap.lookup v ret of
        Just x -> x
        Nothing -> error ("foldGraphNodes: invalid node id " ++ show v)

-- ------------------------------------------------------------------------
