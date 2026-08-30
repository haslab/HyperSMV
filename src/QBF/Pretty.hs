-- | Pretty-printer for the QCIR AST.
module QBF.Pretty where

import qualified Data.IntMap as IntMap
import qualified Data.Key as K

import qualified Data.ByteString.Builder as BB
import Prettyprinter

import Pretty
import QBF.Syntax

instance Pretty QCIR where
    pretty = prettyQCIR

-- | Render a QCIR circuit as a document.
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

-- | Render a negation flag.
prettyIsNegated :: IsNegated -> Doc ann
prettyIsNegated True = pretty "-"
prettyIsNegated False = emptyDoc

instance Pretty GateExpr where
    pretty (GateAnd gs) = pretty "and" <> parens (sepBy "," $ IntMap.elems $ K.mapWithKey (\k isNeg -> prettyIsNegated isNeg <> pretty k) gs)
    pretty (GateOr gs) = pretty "or" <> parens (sepBy "," $ IntMap.elems $ K.mapWithKey (\k isNeg -> prettyIsNegated isNeg <> pretty k) gs)

    

-- | Direct ByteString-Builder emitter for QCIR ('qcirBuilder'), byte-identical to 'prettyQCIR' but without
-- building a Doc tree or running the layout algorithm.
qcirBuilder :: QCIR -> BB.Builder
qcirBuilder qcir =
       BB.byteString "#QCIR-G14"
    <> foldMap (\q -> nl <> buildQuant q) (qcir_quantifiers qcir)
    <> nl <> BB.byteString "output(" <> BB.intDec (qcir_output qcir) <> BB.char7 ')'
    <> foldMap buildGateLine (IntMap.toAscList (qcir_gates qcir))
  where
    nl = BB.char7 '\n'
    sep = BB.byteString " , "
    joinWith f xs = mconcat (intersperseB sep (map f xs))
    intersperseB _ [] = []
    intersperseB _ [x] = [x]
    intersperseB d (x:xs) = x : d : intersperseB d xs
    buildQuant (QForall vs) = BB.byteString "forall(" <> joinWith BB.intDec vs <> BB.char7 ')'
    buildQuant (QExists vs) = BB.byteString "exists(" <> joinWith BB.intDec vs <> BB.char7 ')'
    buildGateLine (k,e) =
        nl <> BB.intDec k <> BB.byteString " = " <> buildGate e
    buildGate (GateAnd gs) = BB.byteString "and(" <> lits gs <> BB.char7 ')'
    buildGate (GateOr  gs) = BB.byteString "or("  <> lits gs <> BB.char7 ')'
    lits gs = joinWith lit (IntMap.toAscList gs)
    lit (k,isNeg) = (if isNeg then BB.char7 '-' else mempty) <> BB.intDec k
