module QCIR.Syntax where

import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import GHC.Generics
import Data.Hashable
import Data.List as List

data QCIR = QCIR { qcir_quantifiers :: [Quantifier], qcir_output :: GateId, qcir_gates :: IntMap GateExpr }
    deriving (Eq,Ord,Show,Generic)

instance Hashable QCIR

data Quantifier
    = QForall [GateId]
    | QExists [GateId]
    deriving (Eq,Ord,Show,Generic)
    
instance Hashable Quantifier
    
type GateId = Int
type IsNegated = Bool

data GateExpr
    = GateAnd (IntMap IsNegated)
    | GateOr (IntMap IsNegated)
    deriving (Eq,Ord,Show,Generic)

instance Hashable GateExpr

sizeQuantifier :: Quantifier -> Int
sizeQuantifier (QForall is) = List.length is
sizeQuantifier (QExists is) = List.length is

sizeQCIR :: QCIR -> Int
sizeQCIR (QCIR qs _ gs) = j
    where
    i = sum $ map sizeQuantifier qs
    j = IntMap.foldl (\acc g -> acc + sizeGateExpr g) i gs
    
sizeGateExpr :: GateExpr -> Int
sizeGateExpr (GateAnd is) = IntMap.size is
sizeGateExpr (GateOr is) = IntMap.size is