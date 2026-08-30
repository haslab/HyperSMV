{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.DecisionDiagram.BDD
-- Copyright   :  (c) Masahiro Sakai 2021
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable
--
-- Reduced Ordered Binary Decision Diagrams (ROBDD).
--
-- References:
--
-- * Bryant, "Graph-Based Algorithms for Boolean Function Manipulation,"
--   in IEEE Transactions on Computers, vol. C-35, no. 8, pp. 677-691,
--   Aug. 1986, doi: [10.1109/TC.1986.1676819](https://doi.org/10.1109/TC.1986.1676819).
--   <https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf>
--
----------------------------------------------------------------------
module Data.BDD
  (
  -- * The BDD type
    BDD (Leaf, Branch)

  -- * Boolean operations
  , true
  , false
  , var
  , not
  , restrictWith
  , (.&&.)
  , (.||.)
  , xor
  , (.=>.)
  , (.<=>.)
--  , ite
  , and
  , or
  , andBounded
  , existsSet
  , renameSet
  , forAllSet
  , andExistsSet
  , orBounded

  -- * Query
  , support
  , evaluate
  , numNodes
  , nodeId

  -- * Satisfiability
  , anySat
  , allSat
  , findSatDFS
  , findSatM
  , anySatComplete
  , allSatComplete

  -- * (Co)algebraic structure
  , Sig (..)
  , inSig
  , outSig

  -- * Fold
  , fold
  , foldM
  , fold'
  , foldM'
  , foldCPS
  , foldCPSM
  , accum
  , accumM

  -- * Unfold
  , unfoldHashable
  , unfoldOrd

  -- * Conversion from/to graphs
  , Graph
  , toGraph
  , toGraph'
  , fromGraph
  , fromGraph'
  ) where

import Safe
import qualified Prelude
import Prelude hiding (not,and,or)
import qualified Control.Monad as Monad
#if !MIN_VERSION_mwc_random(0,15,0)
import Control.Monad.Primitive
#endif
import Control.Monad.ST
import Data.STRef
import qualified Data.Foldable as Foldable
import Data.Hashable
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
import qualified Data.Vector as V
import GHC.Stack
#if MIN_VERSION_mwc_random(0,15,0)
#else
import System.Random.MWC (Gen, Variate (..))
#endif
import Text.Read

import Data.BDD.Internal (Sig (..), Graph)
import qualified Data.BDD.Internal as Node


infixr 3 .&&.
infixr 2 .||.
infixr 1 .=>.
infix 1 .<=>.

-- ------------------------------------------------------------------------

-- | Initial size for per-call operation hash tables.
defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Reduced ordered binary decision diagram representing boolean function
newtype BDD = BDD Node.Node
  deriving (Eq, Hashable)

pattern F :: BDD
pattern F = Leaf False

pattern T :: BDD
pattern T = Leaf True

pattern Leaf :: Bool -> BDD
pattern Leaf b = BDD (Node.Leaf b)

-- | Smart constructor that takes the BDD reduction rules into account
pattern Branch :: Int -> BDD -> BDD -> BDD
pattern Branch x lo hi <- BDD (Node.Branch x (BDD -> lo) (BDD -> hi)) where
  Branch x (BDD lo) (BDD hi)
    | lo == hi = BDD lo
    | otherwise = BDD (Node.Branch x lo hi)

{-# COMPLETE T, F, Branch #-}
{-# COMPLETE Leaf, Branch #-}

-- | The node's unique interned id.
nodeId :: BDD -> Int
nodeId (BDD node) = Node.nodeId node

-- | How the top variables of two BDD nodes compare.
data BDDCase2
  = BDDCase2LT Int (BDD) (BDD)
  | BDDCase2GT Int (BDD) (BDD)
  | BDDCase2EQ Int (BDD) (BDD) (BDD) (BDD)
  | BDDCase2EQ2 Bool Bool

-- | Classify two nodes by top variable, for binary apply.
bddCase2 :: BDD -> BDD -> BDDCase2
bddCase2 (Branch ptop p0 p1) (Branch qtop q0 q1) =
  case compare ptop qtop of
    LT -> BDDCase2LT ptop p0 p1
    GT -> BDDCase2GT qtop q0 q1
    EQ -> BDDCase2EQ ptop p0 p1 q0 q1
bddCase2 (Branch ptop p0 p1) _ = BDDCase2LT ptop p0 p1
bddCase2 _ (Branch qtop q0 q1) = BDDCase2GT qtop q0 q1
bddCase2 (Leaf b1) (Leaf b2) = BDDCase2EQ2 b1 b2

-- ------------------------------------------------------------------------

instance Show (BDD) where
  showsPrec d a   = showParen (d > 10) $
    showString "fromGraph " . shows (toGraph a)

instance Read (BDD) where
  readPrec = parens $ prec 10 $ do
    Ident "fromGraph" <- lexP
    fromGraph <$> readPrec

  readListPrec = readListPrecDefault

-- ------------------------------------------------------------------------

-- | True
true :: BDD
true = T

-- | False
false :: BDD
false = F

-- | A variable \(x_i\)
var :: Int -> BDD
var ind = Branch ind F T

-- | Negation of a boolean function
not :: BDD -> BDD
not bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f (Leaf b) = return (Leaf (Prelude.not b))
      f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- Branch ind <$> f lo <*> f hi
            H.insert h n ret
            return ret
  f bdd

-- | Cofactor under a partial assignment. Memoised on the node.
restrictWith :: (Int -> Maybe Bool) -> BDD -> BDD
restrictWith f bdd = runST $ do
  h <- C.newSized defaultTableSize
  let go n@(Leaf _) = return n
      go n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case f ind of
              Just b -> go (if b then hi else lo)
              Nothing -> do
                lo' <- go lo
                hi' <- go hi
                return $ if lo' == lo && hi' == hi then n else Branch ind lo' hi'
            H.insert h n ret
            return ret
  go bdd

-- | Apply a binary operator to two BDDs, memoised.
apply :: Bool -> (BDD -> BDD -> Maybe (BDD)) -> BDD -> BDD -> BDD
apply isCommutative func bdd1 bdd2 = runST $ do
  op <- mkApplyOp isCommutative func
  op bdd1 bdd2

-- | Build a memoised binary-apply operator.
mkApplyOp :: forall s. Bool -> (BDD -> BDD -> Maybe (BDD)) -> ST s (BDD -> BDD -> ST s (BDD))
mkApplyOp isCommutative func = do
  h <- C.newSized defaultTableSize
  let f a b | Just c <- func a b = return c
      f n1 n2 = do
        let key = if isCommutative && nodeId n2 < nodeId n1 then (n2, n1) else (n1, n2)
        m <- H.lookup h key
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case bddCase2 n1 n2 of
              BDDCase2GT x2 lo2 hi2 -> Branch x2 <$> f n1 lo2 <*> f n1 hi2
              BDDCase2LT x1 lo1 hi1 -> Branch x1 <$> f lo1 n2 <*> f hi1 n2
              BDDCase2EQ x lo1 hi1 lo2 hi2 -> Branch x <$> f lo1 lo2 <*> f hi1 hi2
              BDDCase2EQ2 _ _ -> error "apply: should not happen"
            H.insert h key ret
            return ret
  return f

-- | Conjunction of two boolean function
(.&&.) ::  BDD -> BDD -> BDD
(.&&.) bdd1 bdd2 = runST $ do
  op <- mkAndOp
  op bdd1 bdd2

-- | Build a memoised conjunction operator.
mkAndOp :: forall s. ST s (BDD -> BDD -> ST s (BDD))
mkAndOp = mkApplyOp True f
  where
    f T b = Just b
    f F _ = Just F
    f a T = Just a
    f _ F = Just F
    f a b | a == b = Just a
    f _ _ = Nothing

-- | Disjunction of two boolean function
(.||.) :: BDD -> BDD -> BDD
(.||.) bdd1 bdd2 = runST $ do
  op <- mkOrOp
  op bdd1 bdd2

-- | Build a memoised disjunction operator.
mkOrOp :: forall s. ST s (BDD -> BDD -> ST s (BDD))
mkOrOp = mkApplyOp True f
  where
    f T _ = Just T
    f F b = Just b
    f _ T = Just T
    f a F = Just a
    f a b | a == b = Just a
    f _ _ = Nothing

-- | Bounded apply: like 'mkApplyOp' but aborts once more than @budget@ result nodes have been created, returning 'Nothing'.
mkApplyOpBounded :: forall s. Int -> Bool -> (BDD -> BDD -> Maybe BDD) -> ST s (BDD -> BDD -> ST s (Maybe BDD))
mkApplyOpBounded budget isCommutative func = do
  h <- C.newSized defaultTableSize
  cnt <- newSTRef (0 :: Int)
  let f a b | Just c <- func a b = return c
      f n1 n2 = do
        k <- readSTRef cnt
        if k > budget then return F
        else do
          let key = if isCommutative && nodeId n2 < nodeId n1 then (n2, n1) else (n1, n2)
          m <- H.lookup h key
          case m of
            Just y -> return y
            Nothing -> do
              writeSTRef cnt (k + 1)
              ret <- case bddCase2 n1 n2 of
                BDDCase2GT x2 lo2 hi2 -> Branch x2 <$> f n1 lo2 <*> f n1 hi2
                BDDCase2LT x1 lo1 hi1 -> Branch x1 <$> f lo1 n2 <*> f hi1 n2
                BDDCase2EQ x lo1 hi1 lo2 hi2 -> Branch x <$> f lo1 lo2 <*> f hi1 hi2
                BDDCase2EQ2 _ _ -> error "applyBounded: should not happen"
              H.insert h key ret
              return ret
  return $ \a b -> do
    writeSTRef cnt 0
    r <- f a b
    k <- readSTRef cnt
    return $ if k > budget then Nothing else Just r

-- | Conjunction, aborting to 'Nothing' if the result would exceed @budget@ nodes.
andBounded :: Int -> BDD -> BDD -> Maybe BDD
andBounded budget bdd1 bdd2 = runST $ mkApplyOpBounded budget True f >>= \op -> op bdd1 bdd2
  where f T b = Just b; f F _ = Just F; f a T = Just a; f _ F = Just F; f a b | a == b = Just a; f _ _ = Nothing

-- | Disjunction, aborting to 'Nothing' if the result would exceed @budget@ nodes.
orBounded :: Int -> BDD -> BDD -> Maybe BDD
orBounded budget bdd1 bdd2 = runST $ mkApplyOpBounded budget True f >>= \op -> op bdd1 bdd2
  where f T _ = Just T; f F b = Just b; f _ T = Just T; f a F = Just a; f a b | a == b = Just a; f _ _ = Nothing

-- | XOR
xor ::  BDD -> BDD -> BDD
xor bdd1 bdd2 = runST $ do
  op <- mkXOROp
  op bdd1 bdd2

-- | Build a memoised XOR operator.
mkXOROp :: forall s.  ST s (BDD -> BDD -> ST s (BDD))
mkXOROp = mkApplyOp True f
  where
    f F b = Just b
    f a F = Just a
    f a b | a == b = Just F
    f _ _ = Nothing

-- | Implication
(.=>.) ::  BDD -> BDD -> BDD
(.=>.) = apply False f
  where
    f F _ = Just T
    f T b = Just b
    f _ T = Just T
    f a b | a == b = Just T
    f _ _ = Nothing

-- | Equivalence
(.<=>.) ::  BDD -> BDD -> BDD
(.<=>.) = apply True f
  where
    f (Leaf b1) (Leaf b2) = Just (Leaf (b1 == b2))
    f a b | a == b = Just T
    f _ _ = Nothing

-- | Conjunction of a list of BDDs.
and :: forall f. (Foldable f) => f (BDD) -> BDD
and xs = runST $ do
  op <- mkAndOp
  Monad.foldM op true xs

-- | Disjunction of a list of BDDs.
or :: forall f. (Foldable f) => f (BDD) -> BDD
or xs = runST $ do
  op <- mkOrOp
  Monad.foldM op false xs

-- | Rename support.
renameSet :: IntMap Int -> BDD -> BDD
renameSet m bdd = runST $ do
    h <- C.newSized defaultTableSize
    let f n@(Leaf _) = return n
        f n@(Branch x lo hi) = do
            hit <- H.lookup h (nodeId n)
            case hit of
              Just y -> return y
              Nothing -> do
                lo' <- f lo
                hi' <- f hi
                let r = Branch (IntMap.findWithDefault x x m) lo' hi'
                H.insert h (nodeId n) r
                return r
    f bdd

-- | Existentially quantify a set of variables.
existsSet :: IntSet -> BDD -> BDD
existsSet vars bdd = runST $ mkQuantOp mkOrOp vars bdd

-- | Universal quantification over a set of variables.
forAllSet :: IntSet -> BDD -> BDD
forAllSet vars bdd = runST $ mkQuantOp mkAndOp vars bdd

-- | Fused relational product @exists vars. (a AND b)@.
andExistsSet :: IntSet -> BDD -> BDD -> BDD
andExistsSet vars a0 b0 = runST $ do
    orOp <- mkOrOp
    hEx  <- C.newSized defaultTableSize
    hAE  <- C.newSized defaultTableSize
    let ex n@(Leaf _) = return n
        ex n@(Branch x lo hi) = do
            m <- H.lookup hEx (nodeId n)
            case m of
              Just y -> return y
              Nothing -> do
                lo' <- ex lo
                hi' <- ex hi
                r <- if IntSet.member x vars then orOp lo' hi' else return (Branch x lo' hi')
                H.insert hEx (nodeId n) r
                return r
    let quantOr mlo mhi = do
            lo' <- mlo
            if lo' == T then return T else orOp lo' =<< mhi     -- short-circuit on true
        f F _ = return F
        f _ F = return F
        f T b = ex b
        f a T = ex a
        f a b | a == b = ex a
        f n1 n2 = do
            let key = if nodeId n2 < nodeId n1 then (n2, n1) else (n1, n2)   -- AND is commutative
            m <- H.lookup hAE key
            case m of
              Just y -> return y
              Nothing -> do
                r <- case bddCase2 n1 n2 of
                 BDDCase2GT x2 lo2 hi2
                     | IntSet.member x2 vars -> quantOr (f n1 lo2) (f n1 hi2)
                     | otherwise -> Branch x2 <$> f n1 lo2 <*> f n1 hi2
                 BDDCase2LT x1 lo1 hi1
                     | IntSet.member x1 vars -> quantOr (f lo1 n2) (f hi1 n2)
                     | otherwise -> Branch x1 <$> f lo1 n2 <*> f hi1 n2
                 BDDCase2EQ x lo1 hi1 lo2 hi2
                     | IntSet.member x vars -> quantOr (f lo1 lo2) (f hi1 hi2)
                     | otherwise -> Branch x <$> f lo1 lo2 <*> f hi1 hi2
                 BDDCase2EQ2 _ _ -> error "andExistsSet: should not happen"
                H.insert hAE key r
                return r
    f a0 b0

-- | Shared skeleton for existsSet/forAllSet.
mkQuantOp :: forall s. (forall s'. ST s' (BDD -> BDD -> ST s' BDD)) -> IntSet -> BDD -> ST s BDD
mkQuantOp mkOp vars bdd = do
    op <- mkOp
    h <- C.newSized defaultTableSize
    let f n@(Leaf _) = return n
        f n@(Branch x lo hi) = do
            m <- H.lookup h (nodeId n)
            case m of
                Just y -> return y
                Nothing -> do
                    lo' <- f lo
                    hi' <- f hi
                    ret <- if IntSet.member x vars
                             then op lo' hi'
                             else return (Branch x lo' hi')
                    H.insert h (nodeId n) ret
                    return ret
    f bdd

-- ------------------------------------------------------------------------

-- | Fold over the graph structure of the BDD.
--
-- It takes two functions that substitute 'Branch'  and 'Leaf' respectively.
--
-- Note that its type is isomorphic to @('Sig' b -> b) -> BDD -> b@.
fold :: (Int -> b -> b -> b) -> (Bool -> b) -> BDD -> b
fold br lf (BDD node) = Node.fold br lf node

-- | Monadic version of 'fold'.
foldM :: Monad m => (Int -> b -> b -> m b) -> (Bool -> m b) -> BDD -> m b
foldM bf lf = fold (\i mlo mhi -> mlo >>= \lo -> mhi >>= \hi -> bf i lo hi) lf

-- | Strict version of 'fold'
fold' :: (Int -> b -> b -> b) -> (Bool -> b) -> BDD -> b
fold' br lf (BDD node) = Node.fold' br lf node

-- | Monadic version of 'fold''.
foldM' :: Monad m => (Int -> b -> b -> m b) -> (Bool -> m b) -> BDD -> m b
foldM' br lf = fold' (\i mlo mhi -> mlo >>= \lo -> mhi >>= \hi -> br i lo hi) lf

-- | Build a memoised strict fold operator.
mkFold'Op :: (Int -> b -> b -> b) -> (Bool -> b) -> ST s (BDD -> ST s b)
mkFold'Op br lf = do
  op <- Node.mkFold'Op br lf
  return $ \(BDD node) -> op node
  
-- | Fold in continuation-passing style.
foldCPS :: (Int -> b -> b -> b) -> (Bool -> b) -> (b -> r) -> BDD -> r
foldCPS br lf k (BDD node) = Node.foldCPS br lf k node

-- | Monadic version of 'foldCPS'.
foldCPSM :: Monad m => (Int -> b -> b -> m b) -> (Bool -> m b) -> (b -> m r) -> BDD -> m r
foldCPSM br lf k (BDD node) = Node.foldCPS (\i ml mr -> ml >>= \l -> mr >>= \r -> br i l r) lf (\mb -> mb >>= k) node

-- | Fold threading an accumulator top-down.
accum :: Monoid b => (a -> Int -> V.Vector a) -> (a -> Bool -> b) -> a -> BDD -> b
accum br lf z (BDD node) = Node.accum br lf z node

-- | Monadic version of 'accum'.
accumM :: (Monad m,Monoid b) => (a -> Int -> V.Vector a) -> (a -> Bool -> m b) -> a -> BDD -> m b
accumM br lf z (BDD node) = Node.accumM br lf z node

-- ------------------------------------------------------------------------

-- | Top-down construction of BDD, memoising internal states using 'Hashable' instance.
unfoldHashable :: forall b. ( Eq b, Hashable b) => (b -> Sig b) -> b -> BDD
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

-- | Top-down construction of BDD, memoising internal states using 'Ord' instance.
unfoldOrd :: forall b. ( Ord b) => (b -> Sig b) -> b -> BDD
unfoldOrd f b = m2 Map.! b
  where
    m1 :: Map b (Sig b)
    m1 = g Map.empty [b]

    m2 :: Map b (BDD)
    m2 = Map.map (inSig . fmap (m2 Map.!)) m1

    g m [] = m
    g m (x : xs) =
      case Map.lookup x m of
        Just _ -> g m xs
        Nothing ->
          let fx = f x
           in g (Map.insert x fx m) (xs ++ Foldable.toList fx)

-- ------------------------------------------------------------------------

-- | All the variables that this BDD depends on.
support :: BDD -> IntSet
support bdd = runST $ do
  op <- mkSupportOp
  op bdd

-- | Build a memoised support operator.
mkSupportOp :: ST s (BDD -> ST s IntSet)
mkSupportOp = mkFold'Op f g
  where
    f x lo hi = IntSet.insert x (lo `IntSet.union` hi)
    g _ = IntSet.empty

-- | Evaluate a boolean function represented as BDD under the valuation
-- given by @(Int -> Bool)@, i.e. it lifts a valuation function from
-- variables to BDDs.
evaluate :: (Int -> Bool) -> BDD -> Bool
evaluate f = g
  where
    g (Leaf b) = b
    g (Branch x lo hi)
      | f x = g hi
      | otherwise = g lo

-- | Count the number of nodes in a BDD viewed as a rooted directed acyclic graph.
--
-- See also 'toGraph'.
numNodes :: BDD -> Int
numNodes (BDD node) = Node.numNodes node

-- ------------------------------------------------------------------------

-- | Enumerate the satisfying partial assignments by DIRECT DFS, output-sensitively.
findSatDFS :: BDD -> [IntMap Bool]
findSatDFS bdd0 = go bdd0 IntMap.empty []
  where
    go b acc rest = case b of
        Leaf v -> if v then acc : rest else rest
        Branch x lo hi ->
            go lo (IntMap.insert x False acc) (go hi (IntMap.insert x True acc) rest)

-- | The memoising fold variant of 'findSatDFS'.
findSatM :: BDD -> [IntMap Bool]
findSatM = foldCPS f g id
  where
    f x lo hi = (IntMap.insert x False <$> lo) ++ (IntMap.insert x True <$> hi)
    g b = if b then [IntMap.empty] else []

-- | Find one satisfying partial assignment
anySat :: BDD -> Maybe (IntMap Bool)
anySat = headMay . findSatDFS

-- | Enumerate all satisfying partial assignments
allSat :: BDD -> [IntMap Bool]
allSat = findSatDFS

-- | Enumerate satisfying assignments completed over a variable set.
findSatCompleteM :: IntSet -> BDD -> [IntMap Bool]
findSatCompleteM is bdd = expandPartial =<< findSatDFS bdd
    where
    expandPartial :: IntMap Bool -> [IntMap Bool]
    expandPartial vs = IntMap.mergeA missL missR matchLR vs (IntMap.fromSet (const ()) is)
        where
        missL = IntMap.traverseMissing (\k x -> [x])
        missR = IntMap.traverseMissing (\k _ -> [False,True])
        matchLR = IntMap.zipWithAMatched (\k x y -> [x])
    
-- | Find one satisfying (complete) assignment over a given set of variables
--
-- The set of variables must be a superset of 'support'.
anySatComplete :: IntSet -> BDD -> Maybe (IntMap Bool)
anySatComplete is = headMay . findSatCompleteM is

-- | Enumerate all satisfying (complete) assignment over a given set of variables
--
-- The set of variables must be a superset of 'support'.
allSatComplete :: IntSet -> BDD -> [IntMap Bool]
allSatComplete = findSatCompleteM

-- ------------------------------------------------------------------------

-- | 'Sig'-algebra stucture of 'BDD', \(\mathrm{in}_\mathrm{Sig}\).
inSig :: Sig (BDD) -> BDD
inSig (SLeaf b) = Leaf b
inSig (SBranch x lo hi) = Branch x lo hi

-- | 'Sig'-coalgebra stucture of 'BDD', \(\mathrm{out}_\mathrm{Sig}\).
outSig :: BDD -> Sig (BDD)
outSig (Leaf b) = SLeaf b
outSig (Branch x lo hi) = SBranch x lo hi

-- ------------------------------------------------------------------------

-- | Convert a BDD into a pointed graph
--
-- Nodes @0@ and @1@ are reserved for @SLeaf False@ and @SLeaf True@
-- even if they are not actually used. Therefore the result may be
-- larger than 'numNodes' if the leaf nodes are not used.
toGraph :: BDD -> (Graph Sig, Int)
toGraph (BDD node) = Node.toGraph node

-- | Convert multiple BDDs into a graph
toGraph' :: Traversable t => t (BDD) -> (Graph Sig, t Int)
toGraph' bs = Node.toGraph' (fmap (\(BDD node) -> node) bs)

-- | Convert a pointed graph into a BDD
fromGraph :: HasCallStack => (Graph Sig, Int) -> BDD
fromGraph = Node.foldGraph inSig

-- | Convert nodes of a graph into BDDs
fromGraph' :: HasCallStack => Graph Sig -> IntMap (BDD)
fromGraph' = Node.foldGraphNodes inSig

-- ------------------------------------------------------------------------
