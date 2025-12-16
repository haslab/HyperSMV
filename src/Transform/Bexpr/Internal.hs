module Transform.Bexpr.Internal
      (
      -- * Low level node type
        Node (Bbool, Bints, Bvar, Bop1, Bop2, Bopn)
      , nodeId

      ) where

import Data.Interned
import Data.Hashable
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import GHC.Generics

import Smv.Syntax
import Smv.Typing

data Node = Node {-# UNPACK #-} !Id (UNode)
  deriving (Show)

instance Eq Node where
  Node i _ == Node j _ = i == j

instance Hashable Node where
  hashWithSalt s (Node i _) = hashWithSalt s i

pattern Bbool :: Bool -> Node
pattern Bbool b <- (unintern -> Ubool b) where
  Bbool b = intern (Ubool b)
  
pattern Bints :: IntSet -> Node
pattern Bints b <- (unintern -> Uints b) where
  Bints b = intern (Uints b)
  
pattern Bvar :: DualPident -> VarType -> Node
pattern Bvar b t <- (unintern -> Uvar b t) where
  Bvar b t = intern (Uvar b t)

pattern Bop1 :: Pop1 -> Node -> Node
pattern Bop1 o b <- (unintern -> Uop1 o b) where
  Bop1 o b = intern (Uop1 o b)

pattern Bop2 :: Pop2 -> Node -> Node -> Node
pattern Bop2 o b1 b2 <- (unintern -> Uop2 o b1 b2) where
  Bop2 o b1 b2 = intern (Uop2 o b1 b2)

pattern Bopn :: Popn -> HashSet Node -> Node
pattern Bopn o bs <- (unintern -> Uopn o bs) where
  Bopn o bs = intern (Uopn o bs)

{-# COMPLETE Bbool, Bints, Bvar, Bop1, Bop2, Bopn #-}

data UNode
  = Ubool {-# UNPACK #-} !Bool
  | Uints {-# UNPACK #-} !IntSet
  | Uvar DualPident VarType
  | Uop1 Pop1 Node
  | Uop2 Pop2 Node Node
  | Uopn Popn (HashSet Node)
  
  deriving (Show)

instance Interned Node where
  type Uninterned Node = UNode
  data Description Node
    = Dbool {-# UNPACK #-} !Bool
    | Dints {-# UNPACK #-} !IntSet
    | Dvar DualPident VarType
    | Dop1 Pop1 Id
    | Dop2 Pop2 Id Id
    | Dopn Popn !IntSet
    deriving (Eq, Generic)
  describe (Ubool b) = Dbool b
  describe (Uints b) = Dints b
  describe (Uvar v i) = Dvar v i
  describe (Uop1 o v1) = Dop1 o (nodeId v1)
  describe (Uop2 o v1 v2) = Dop2 o (nodeId v1) (nodeId v2)
  describe (Uopn o vs) = Dopn o (foldl (\m n -> IntSet.insert (nodeId n) m) IntSet.empty vs)
  identify = Node
  cache = nodeCache

instance Hashable (Description Node)

instance Uninternable Node where
  unintern (Node _ uformula) = uformula


nodeCache :: Cache Node
nodeCache = mkCache
{-# NOINLINE nodeCache #-}



nodeId :: Node -> Id
nodeId (Node id_ _) = id_

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256