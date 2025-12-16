module HOA.Syntax where

import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import GHC.Generics
import Data.Hashable

data HOA = HOA
    { hoa_starts :: IntSet
    , hoa_aps :: [String]
    , hoa_acceptance :: Maybe [HOAacceptance]
    , hoa_states :: HOAstates
    } deriving (Eq,Ord,Show,Generic)
    
instance Hashable HOA

instance Semigroup HOA where
    x <> y = mappend x y

instance Monoid HOA where
    mempty = HOA IntSet.empty [] Nothing IntMap.empty
    mappend (HOA s1 ap1 ac1 st1) (HOA s2 ap2 ac2 st2) = HOA (IntSet.union s1 s2) (ap1++ap2) (joinAc ac1 ac2) (IntMap.union st1 st2)
        where
        joinAc Nothing Nothing = Nothing
        joinAc Nothing (Just ac2) = Just ac2
        joinAc (Just ac1) Nothing = Just ac1
        joinAc (Just ac1) (Just ac2) = Just (ac1++ac2)

data HOAstate = HOAstate { hoa_state_acceptance :: HOAacceptances, hoa_state_trans :: HOAtransitions }
    deriving (Eq,Ord,Show,Generic)
    
instance Hashable HOAstate

type HOAstates = IntMap HOAstate

type HOAtransitions = HashMap APexpr HOAnext

data HOAnext = HOAnext { hoa_next_state :: Int, hoa_next_acceptance :: HOAacceptances }
    deriving (Eq,Ord,Show,Generic)

instance Hashable HOAnext

data HOAacceptance = Inf Int
    deriving (Eq,Ord,Show,Generic)
    
instance Hashable HOAacceptance
    
type HOAacceptances = IntSet

type IsNegated = Bool

data APexpr
    = APbool Bool
    | APand (HashSet APexpr)
    | APor (HashSet APexpr)
    | APnot APexpr
    | APvar Int
    deriving (Eq,Ord,Show,Generic)

instance Hashable APexpr

apand2 :: APexpr -> APexpr -> APexpr
apand2 e1 e2 = APand $ HashSet.fromList [e1,e2]

apor2 :: APexpr -> APexpr -> APexpr
apor2 e1 e2 = APor $ HashSet.fromList [e1,e2]
