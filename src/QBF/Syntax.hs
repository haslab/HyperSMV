-- | The QCIR file-format AST.
module QBF.Syntax where

import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import GHC.Generics
import Data.Hashable
import Data.List as List

-- | A QCIR circuit.
data QCIR = QCIR { qcir_quantifiers :: [Quantifier], qcir_output :: GateId, qcir_gates :: IntMap GateExpr }
    deriving (Eq,Ord,Show,Generic)

instance Hashable QCIR

-- | One quantifier-prefix block.
data Quantifier
    = QForall [GateId]
    | QExists [GateId]
    deriving (Eq,Ord,Show,Generic)
    
instance Hashable Quantifier
    
-- | A gate's numeric id.
type GateId = Int
-- | Whether a gate reference is negated.
type IsNegated = Bool

-- | A gate's AND/OR definition.
data GateExpr
    = GateAnd (IntMap IsNegated)
    | GateOr (IntMap IsNegated)
    deriving (Eq,Ord,Show,Generic)

instance Hashable GateExpr

-- | Number of variables in a quantifier block.
sizeQuantifier :: Quantifier -> Int
sizeQuantifier (QForall is) = List.length is
sizeQuantifier (QExists is) = List.length is

-- | Total size of a QCIR circuit.
sizeQCIR :: QCIR -> Int
sizeQCIR (QCIR qs _ gs) = j
    where
    i = sum $ map sizeQuantifier qs
    j = IntMap.foldl (\acc g -> acc + sizeGateExpr g) i gs
    
-- | Number of inputs to a gate.
sizeGateExpr :: GateExpr -> Int
sizeGateExpr (GateAnd is) = IntMap.size is
sizeGateExpr (GateOr is) = IntMap.size is