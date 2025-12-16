-- An implementation of Multi-way decision diagrams (MIDDs) with int or bool variables.
-- Code adapted from the package decision-diagrams on hackage.

module Data.IDD
  (
  -- * The IDD type
    IDD (Leaf, Branch)

  -- * Item ordering
  
  , apply

  -- * Boolean operations
  , true
  , false
  , not
  , var
  , (.&&.)
  , (.||.)
  , (.=>.)
  , (.<=>.)
  , and
  , or
  -- * (Co)algebraic structure
  , Sig (..)
  , inSig
  , outSig

  -- * Fold
  , fold
  , fold'
  , foldM, foldM'
  , accum
  , foldCPS, foldCPSM

  -- * Unfold
  , unfoldHashable
  , unfoldOrd
  
  , support
  , evaluate
  
  -- * Satisfiability
  , anySat
  , allSat
  , anySatComplete
  , allSatComplete

  -- * Conversion from/to graphs
  , Graph
  , toGraph
  , toGraph'
  , fromGraph
  , fromGraph'
  ) where

import Safe
import Prelude hiding (and,or,not)
import qualified Prelude
import Control.Exception (assert)
import Control.Monad hiding (foldM)
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.Bits (Bits (shiftL))
import qualified Data.Foldable as Foldable
import Data.Hashable
import qualified Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Merge.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Proxy
import Data.Ratio
import qualified Data.Vector as V
import GHC.Stack
import Numeric.Natural
import System.Random.MWC (Uniform (..))
import System.Random.Stateful (StatefulGen (..))
import System.Random.MWC.Distributions (bernoulli)
import Text.Read
import Data.Vector (Vector(..))
import qualified Data.Vector as V

import Utils
import Data.IDD.Internal (Sig (..), Graph)
import qualified Data.IDD.Internal as Node

infixr 3 .&&.
infixr 2 .||.

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Reduced ordered binary decision diagram representing boolean function
newtype IDD = IDD { unIDD :: (Node.Node) }
  deriving (Eq, Hashable)

pattern Leaf ::  Bool -> IDD
pattern Leaf b = IDD (Node.Leaf b)

-- | Smart constructor that takes the IDD reduction rules into account
pattern Branch :: Int -> Vector IDD -> IDD
pattern Branch x bs <- IDD (Node.Branch x (fmap IDD -> bs)) where
  Branch x (fmap unIDD -> bs)
    | allEqual bs = IDD (V.head bs)
    | otherwise = IDD (Node.Branch x bs)

{-# COMPLETE Leaf, Branch #-}

nodeId :: IDD -> Int
nodeId (IDD node) = Node.nodeId node

data IDDCase2
  = IDDCase2LT Int (Vector IDD)
  | IDDCase2GT Int (Vector IDD)
  | IDDCase2EQ Int (Vector IDD) (Vector IDD)
  | IDDCase2EQ2 Bool Bool

ddCase2 ::  IDD -> IDD -> IDDCase2
ddCase2 (Branch ptop ps) (Branch qtop qs) =
  case compare ptop qtop of
    LT -> IDDCase2LT ptop ps
    GT -> IDDCase2GT qtop qs
    EQ -> IDDCase2EQ ptop ps qs
ddCase2 (Branch ptop ps) _ = IDDCase2LT ptop ps
ddCase2 _ (Branch qtop qs) = IDDCase2GT qtop qs
ddCase2 (Leaf b1) (Leaf b2) = IDDCase2EQ2 b1 b2

-- ------------------------------------------------------------------------

instance Show (IDD) where
  showsPrec d a   = showParen (d > 10) $
    showString "fromGraph " . shows (toGraph a)

instance Read (IDD) where
  readPrec = parens $ prec 10 $ do
    Ident "fromGraph" <- lexP
    fromGraph <$> readPrec

  readListPrec = readListPrecDefault

-- ------------------------------------------------------------------------

false :: IDD
false = Leaf False

true :: IDD
true = Leaf True

-- | Negation of a boolean function
not :: IDD -> IDD
not bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f (Leaf b) = return (Leaf (Prelude.not b))
      f n@(Branch ind cs) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- Branch ind <$> mapM f cs
            H.insert h n ret
            return ret
  f bdd

-- (int size,int vals)
var :: Int -> (Int,IntSet) -> IDD
var i (sz,vs) = Branch i $ V.generate sz $ \v -> if IntSet.member v vs then true else false

apply :: Bool -> (IDD -> IDD -> Maybe (IDD)) -> IDD -> IDD -> IDD
apply isCommutative func bdd1 bdd2 = runST $ do
  op <- mkApplyOp isCommutative func
  op bdd1 bdd2

mkApplyOp :: forall s. Bool -> (IDD -> IDD -> Maybe (IDD)) -> ST s (IDD -> IDD -> ST s (IDD))
mkApplyOp isCommutative func = do
  h <- C.newSized defaultTableSize
  let f a b | Just c <- func a b = return c
      f n1 n2 = do
        let key = if isCommutative && nodeId n2 < nodeId n1 then (n2, n1) else (n1, n2)
        m <- H.lookup h key
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case ddCase2 n1 n2 of
              IDDCase2GT x2 bs2 -> Branch x2 <$> traverse (f n1) bs2
              IDDCase2LT x1 bs1 -> Branch x1 <$> traverse (flip f n2) bs1
              IDDCase2EQ x bs1 bs2 -> Branch x <$> V.zipWithM f bs1 bs2
              IDDCase2EQ2 _ _ -> error "apply: should not happen"
            H.insert h key ret
            return ret
  return f

-- | Conjunction of two boolean function
(.&&.) :: IDD -> IDD -> IDD
(.&&.) = apply True join
    where
    join :: IDD -> IDD -> Maybe IDD
    join (Leaf True) b = Just b
    join a@(Leaf False) _ = Just a
    join a (Leaf True) = Just a
    join _ b@(Leaf False) = Just b
    join a b | a == b = Just a
    join _ _ = Nothing
    
-- | Disjunction of two boolean function
(.||.) :: IDD -> IDD -> IDD
(.||.) = apply True join
    where
    join :: IDD -> IDD -> Maybe IDD
    join a@(Leaf True) _ = Just a
    join (Leaf False) b = Just b
    join _ b@(Leaf True) = Just b
    join a (Leaf False) = Just a
    join a b | a == b = Just a
    join _ _ = Nothing

-- | Implication
(.=>.) :: IDD -> IDD -> IDD
(.=>.) = apply False f
  where
    f (Leaf False) _ = Just $ Leaf True
    f (Leaf True) b = Just b
    f _ b@(Leaf True) = Just b
    f a b | a == b = Just (Leaf True)
    f _ _ = Nothing

-- | Equivalence
(.<=>.) :: IDD -> IDD -> IDD
(.<=>.) = apply True f
  where
    f (Leaf b1) (Leaf b2) = Just (Leaf (b1 == b2))
    f a b | a == b = Just (Leaf True)
    f _ _ = Nothing

-- | Conjunction of a list of IDDs.
and :: Foldable.Foldable f => f IDD -> IDD
and es = Foldable.foldl (.&&.) true es

-- | Disjunction of a list of IDDs.
or :: Foldable.Foldable f => f IDD -> IDD
or es = Foldable.foldl (.||.) false es

------------------------------------------------------------------------

-- | Fold over the graph structure of the IDD.

-- It takes two functions that substitute 'Branch'  and 'Leaf' respectively.

-- Note that its type is isomorphic to @('Sig' b -> b) -> IDD -> b@.
fold :: (Int -> Vector b -> b) -> (Bool -> b) -> IDD -> b
fold br lf (IDD node) = Node.fold br lf node

foldM :: Monad m => (Int -> Vector b -> m b) -> (Bool -> m b) -> IDD -> m b
foldM br lf = fold (\i ms -> V.sequence ms >>= br i) lf

-- | Strict version of 'fold'
fold' :: (Int -> Vector b -> b) -> (Bool -> b) -> IDD -> b
fold' br lf (IDD node) = Node.fold' br lf node

foldM' :: Monad m => (Int -> Vector b -> m b) -> (Bool -> m b) -> IDD -> m b
foldM' bf lf = fold' (\i ms -> V.sequence ms >>= bf i) lf

mkFold'Op :: (Int -> Vector b -> b) -> (Bool -> b) -> ST s (IDD -> ST s b)
mkFold'Op br lf = do
  op <- Node.mkFold'Op br lf
  return $ \(IDD node) -> op node

accum :: Monoid b => (a -> Int -> Vector a) -> (a -> Bool -> b) -> a -> IDD -> b
accum br lf z (IDD node) = Node.accum br lf z node

foldCPS :: (Int -> Vector b -> b) -> (Bool -> b) -> (b -> r) -> IDD -> r
foldCPS br lf k (IDD node) = Node.foldCPS br lf k node

foldCPSM :: Monad m => (Int -> Vector b -> m b) -> (Bool -> m b) -> (b -> m r) -> IDD -> m r
foldCPSM br lf k (IDD node) = Node.foldCPS (\i ms -> V.sequence ms >>= br i) lf (\mb -> mb >>= k) node

------------------------------------------------------------------------

-- | Top-down construction of IDD, memoising internal states using 'Hashable' instance.
unfoldHashable :: forall b. (Eq b, Hashable b) => (b -> Sig b) -> b -> IDD
unfoldHashable f b = runST $ do
  h <- C.newSized defaultTableSize
  let g [] = return ()
      g (x : xs) = do
        r <- H.lookup h x
        case r of
          Just _ -> g xs
          Nothing -> do
            let fx = f x
            H.insert h x fx
            g (xs ++ Foldable.toList fx)
  g [b]
  xs <- H.toList h
  let h2 = HashMap.fromList [(x, inSig (fmap (h2 HashMap.!) s)) | (x,s) <- xs]
  return $ h2 HashMap.! b

-- | Top-down construction of IDD, memoising internal states using 'Ord' instance.
unfoldOrd :: forall b. (Ord b) => (b -> Sig b) -> b -> IDD
unfoldOrd f b = m2 Map.! b
  where
    m1 :: Map b (Sig b)
    m1 = g Map.empty [b]

    m2 :: Map b (IDD)
    m2 = Map.map (inSig . fmap (m2 Map.!)) m1

    g m [] = m
    g m (x : xs) =
      case Map.lookup x m of
        Just _ -> g m xs
        Nothing ->
          let fx = f x
           in g (Map.insert x fx m) (xs ++ Foldable.toList fx)

------------------------------------------------------------------------

-- | All the variables that this IDD depends on.
support :: IDD -> IntSet
support bdd = runST $ do
  op <- mkSupportOp
  op bdd

mkSupportOp :: ST s (IDD -> ST s IntSet)
mkSupportOp = mkFold'Op f g
  where
    f x cs = IntSet.insert x $ IntSet.unions cs
    g _ = IntSet.empty

-- | Evaluate a boolean function represented as IDD under the valuation
-- given by @(Int -> Int)@, i.e. it lifts a valuation function from
-- variables to IDDs.
evaluate :: (Int -> Int) -> IDD -> Bool
evaluate f = g
  where
    g (Leaf b) = b
    g (Branch x cs) = g $ (vIndex "evaluate") cs $ f x

-- ------------------------------------------------------------------------

findSatM :: IDD -> [IntMap Int]
findSatM = foldCPS f g id
  where
    f x cs = msum (V.imap (\i c -> IntMap.insert x i <$> c) cs)
    g b = if b then return IntMap.empty else mzero

-- | Find one satisfying partial assignment
anySat :: IDD -> Maybe (IntMap Int)
anySat = headMay . findSatM

-- | Enumerate all satisfying partial assignments
allSat :: IDD -> [IntMap Int]
allSat = findSatM

findSatCompleteM :: IntMap Int -> IDD -> [IntMap Int]
findSatCompleteM sizes bdd = expandPartial =<< findSatM bdd
    where
    expandPartial :: IntMap Int -> [IntMap Int]
    expandPartial vs = IntMap.mergeA missL missR matchLR vs sizes
        where
        missL = IntMap.traverseMissing (\k x -> [x])
        missR = IntMap.traverseMissing (\k sz -> [0..sz-1])
        matchLR = IntMap.zipWithAMatched (\k x sz -> [x])
    
-- | Find one satisfying (complete) assignment over a given set of variables

-- The set of variables must be a superset of 'support'.
anySatComplete :: IntMap Int -> IDD -> Maybe (IntMap Int)
anySatComplete is = headMay . findSatCompleteM is

-- | Enumerate all satisfying (complete) assignment over a given set of variables
--
-- The set of variables must be a superset of 'support'.
allSatComplete :: IntMap Int -> IDD -> [IntMap Int]
allSatComplete = findSatCompleteM

-- ------------------------------------------------------------------------

-- | 'Sig'-algebra stucture of 'IDD', \(\mathrm{in}_\mathrm{Sig}\).
inSig :: Sig (IDD) -> IDD
inSig (SLeaf b) = Leaf b
inSig (SBranch x cs) = Branch x cs

-- | 'Sig'-coalgebra stucture of 'IDD', \(\mathrm{out}_\mathrm{Sig}\).
outSig :: IDD -> Sig (IDD)
outSig (Leaf b) = SLeaf b
outSig (Branch x cs) = SBranch x cs

-- ------------------------------------------------------------------------

-- | Convert a IDD into a pointed graph
--
-- Nodes @0@ and @1@ are reserved for @SLeaf False@ and @SLeaf True@
-- even if they are not actually used. Therefore the result may be
-- larger than 'numNodes' if the leaf nodes are not used.
toGraph :: IDD -> (Graph (Sig), Int)
toGraph (IDD node) = Node.toGraph node

-- | Convert multiple IDDs into a graph
toGraph' :: (Traversable t) => t (IDD) -> (Graph (Sig), t Int)
toGraph' bs = Node.toGraph' (fmap (\(IDD node) -> node) bs)

-- | Convert a pointed graph into a IDD
fromGraph :: (HasCallStack) => (Graph (Sig), Int) -> IDD
fromGraph = Node.foldGraph inSig

-- | Convert nodes of a graph into IDDs
fromGraph' :: (HasCallStack) => Graph (Sig) -> IntMap (IDD)
fromGraph' = Node.foldGraphNodes inSig

-- ------------------------------------------------------------------------

