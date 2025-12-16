module ExplicitState.Pretty where

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

import Utils
import Pretty
import Prettyprinter
import ExplicitState.Syntax
import Smv.Typing
import qualified Data.DD as DD

prettyExplicitStateSystem :: (DD.IsVal base,Pretty n) => ExplicitStateSystem n base -> Doc ann
prettyExplicitStateSystem s = vcat $ header ++ pstates ++ footer
    where
    prettyAsString = show . prettyprint
    typeOf (VInt _) = "Int"
    typeOf (VBool) = "Bool"
    showBool True = "true"
    showBool False = "false"
    header = [pretty "Variables:" <+> pvars, pretty "Init:" <+> pinits] ++ paccepts ++ [pretty "--BODY--"]
    footer = [pretty "--END--"]
    ns = V.toList (exp_vars s)
    pvars = sepBy emptyDoc $ map (\(n,t) -> parens $ pretty (prettyAsString n) <+> pretty (typeOf t)) ns
    pinits = sepBy emptyDoc $ map pretty $ IntSet.toList (exp_inits s)
    paccepts = case exp_accepting s of
        Nothing -> []
        Just as -> [pretty "Accepting: " <+> (sepBy emptyDoc $ map pretty $ IntSet.toList as)]
    pstates = concatMap drawState $ IntMap.toList $ exp_states s
    drawState (i,(vs,ts)) = [pretty "State:" <+> pretty i <+> braces (drawValues vs),drawNexts ts]
    drawValues vs = sepBy emptyDoc $ map drawValue $ zip ns (UV.toList vs)
    drawValue ((var,VInt _),val) = parens $ pretty (prettyAsString var) <+> pretty (show $ DD.valToInt val)
    drawValue ((var,VBool),val) = parens $ pretty (prettyAsString var) <+> pretty (showBool $ DD.valToBool val)
    drawNexts ts = sepBy emptyDoc $ map pretty $ IntSet.toList ts