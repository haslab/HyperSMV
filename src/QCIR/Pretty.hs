module QCIR.Pretty where

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Key as K

import Utils
import Pretty
import Prettyprinter
import QCIR.Syntax

instance Pretty QCIR where
    pretty = prettyQCIR

prettyQCIR :: QCIR -> Doc ann
prettyQCIR qcir = vcat $ header : quants ++ output : gates
    where
    header = "#QCIR-G14"
    quants = map pretty (qcir_quantifiers qcir)
    output = pretty "output" <> parens (pretty $ qcir_output qcir)
    gates = IntMap.elems $ K.mapWithKey (\k e -> pretty k <+> pretty "=" <+> pretty e) (qcir_gates qcir)
    
instance Pretty Quantifier where
    pretty (QForall vs) = pretty "forall" <> parens (sepBy (pretty ",") $ map pretty vs)
    pretty (QExists vs) = pretty "exists" <> parens (sepBy (pretty ",") $ map pretty vs)

prettyIsNegated :: IsNegated -> Doc ann
prettyIsNegated True = pretty "-"
prettyIsNegated False = emptyDoc

instance Pretty GateExpr where
    pretty (GateAnd gs) = pretty "and" <> parens (sepBy "," $ IntMap.elems $ K.mapWithKey (\k isNeg -> prettyIsNegated isNeg <> pretty k) gs)
    pretty (GateOr gs) = pretty "or" <> parens (sepBy "," $ IntMap.elems $ K.mapWithKey (\k isNeg -> prettyIsNegated isNeg <> pretty k) gs)

    