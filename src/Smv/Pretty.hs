module Smv.Pretty where
    
import Prettyprinter
import Prelude hiding ((<>))
import Data.Set (Set(..))
import qualified Data.Set as Set
import qualified Data.HashSet as HashSet
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet

import Pretty
import qualified Location as L
import Smv.Syntax
import Utils

data SmvMode = Default | HyperQube SmvKind | AutoHyper SmvKind | GenQBF SmvKind deriving (Eq,Show)
data SmvKind = Smv | Hyper deriving (Eq,Show)

smvKind :: SmvMode -> SmvKind
smvKind Default = Smv
smvKind (HyperQube k) = k
smvKind (AutoHyper k) = k
smvKind (GenQBF k) = k

class SmvPretty a where
    pp :: SmvMode -> a -> Doc ann

instance SmvPretty a => SmvPretty (L.Located a) where
    pp m (L.Located _ x) = pp m x

instance SmvPretty Pformula where
    pp m (Pfexists n e) = pretty "exists" <+> pretty n <> pretty "." <+> pp m e
    pp m (Pfforall n e) = pretty "forall" <+> pretty n <> pretty "." <+> pp m e
    pp m (Pfltl e) = pretty "\n" <> pp m e

instance SmvPretty Pmodule where
    pp m (Pmodule n is) = vcat $ (pretty "MODULE" <+> ppName m n) : map (pp m) is

instance SmvPretty Pitem where
    pp m (Pivar vs False) = vcat $ (pretty "VAR") : map (pp m) vs
    pp m (Pivar vs True) = vcat $ (pretty "FROZENVAR") : map (pp m) vs
    pp m (Pidefine ds) = vcat (pretty "DEFINE" : map (pp m) ds)
    pp m (Piinit i) = vcat [pretty "INIT",pp m i]
    pp m (Piinvar i) = vcat [pretty "INVAR",pp m i]
    pp m (Pitrans i) = vcat [pretty "TRANS",pp m i]
    pp m (Piltlspec i) = vcat [pretty "LTLSPEC",pp m i,pretty ";"]
    pp m (Piassign a) = nest 4 $ vcat (pretty "ASSIGN":map (pp m) a)
    
instance SmvPretty Ptype where
    pp m Pboolean = pretty "boolean"
    pp m (Pint i j) = pretty i <> pretty ".." <> pretty j
    pp m (Parray i j t) = pretty "array" <+> pretty i <> pretty ".." <> pretty j <+> pretty "of" <+> pp m t
    pp m (Penum is) = pretty '{' <> sepBy (pretty ',') (map pretty $ IntSet.toList is) <> pretty '}'

instance SmvPretty Pvar where
    pp m (Pvar n t) = pclose False (ppIdent m n) <+> pretty ':' <+> pp m t <> pretty ';'
    
ppDims :: SmvMode -> Pdims -> Doc ann
ppDims m@(GenQBF Hyper) dims = hcat (map (\dim -> pretty "_" <> (ppClosedExpr m False dim)) dims)
ppDims m dims = hcat (map (\dim -> brackets (ppClosedExpr m False dim)) dims)
    
instance SmvPretty Pdefine where
    pp m (Pdefine l r) = ppName m l <+> pretty ":=" <+> pp m r <> pretty ';'

instance SmvPretty Passign where
    pp m (Passign l r) = pp m l <+> pretty ":=" <+> pp m r <> pretty ';'

instance SmvPretty Passign_lhs where
    pp m (Painit p) = pretty "init" <> (pclose True $ ppIdent m p)
    pp m (Panext p) = pretty "next" <> (pclose True $ ppIdent m p)

instance SmvPretty Popn where
    pp (HyperQube Hyper) Pand = pretty "/\\"
    pp (HyperQube Hyper) Por = pretty "\\/"
    pp (GenQBF _) Pand = pretty "/\\"
    pp (GenQBF _) Por = pretty "\\/"
    pp m Pand = pretty '&'
    pp m Por = pretty '|'
    pp m Pset = pretty ','
    pp m o = error $ "no pretty for Popn " ++ show o

instance Pretty Popn where
    pretty = pp Default

instance SmvPretty Pop1 where
    pp (HyperQube Hyper) Pnot = pretty '~'
    pp (GenQBF _) Pnot = pretty '~'
    pp _ Pnot = pretty '!'
    pp m Pf = pretty 'F'
    pp m Pg = pretty 'G'
    pp m Px = pretty 'X'
    pp m Py = pretty 'Y'
    pp m Pz = pretty 'Z'
    pp m Ph = pretty 'H'
    pp m Pnext = pretty "next"
    pp m o = error $ "no pretty for Pop1 " ++ show o

instance Pretty Pop1 where
    pretty = pp Default

instance SmvPretty Pop2 where
    pp m Pequiv = pretty "<->"
    pp m Pimplies = pretty "->"
    pp m Peq = pretty "="
    pp m Pneq = pretty "!="
    pp _ Pplus = pretty '+'
    pp _ Pminus = pretty '-'
    pp _ Ptimes = pretty '*'
    pp _ Pleq = pretty "<="
    pp _ Plt = pretty "<"
    pp _ Pgeq = pretty ">="
    pp _ Pgt = pretty ">"
    pp _ Punion = pretty "union"
    pp _ Pin = pretty "in"
    pp m Pu = pretty 'U'
    pp m@(HyperQube Hyper) Pv = pretty 'R'
    pp m@(GenQBF Hyper) Pv = pretty 'R'
    pp m@(AutoHyper Hyper) Pv = pretty 'R'
    pp m Pv = pretty 'V'
    pp m o = error $ "no pretty for Pop2 " ++ show o

instance Pretty Pop2 where
    pretty = pp Default
    
instance SmvPretty Pexpr where
    pp m e = pclose False $ ppExpr m e
    
instance Pretty Pexpr where
    pretty e = pp Default e
    
instance Pretty Pformula where
    pretty e = pp Default e

data PDoc ann = PClosed Bool (Doc ann) | PDoc (Doc ann)

unPDoc :: PDoc ann -> Doc ann
unPDoc (PClosed _ p) = p
unPDoc (PDoc p) = p

pclose :: Bool -> PDoc ann -> Doc ann
pclose True (PClosed True p) = p
pclose True (PClosed False p) = parens p
pclose True (PDoc p) = parens p
pclose False (PClosed _ p) = p
pclose False (PDoc p) = parens p

ppClosedExpr :: SmvMode -> Bool -> Pexpr -> Doc ann
ppClosedExpr m withParens e = pclose withParens $ ppExpr m e

ppExpr :: SmvMode -> Pexpr -> PDoc ann
ppExpr m (Peident n t) = ppIdent m n
ppExpr (AutoHyper _) (Pebool True) = PClosed False $ pretty "true"
ppExpr (AutoHyper _) (Pebool False) = PClosed False $ pretty "false"
ppExpr (HyperQube Hyper) (Pebool True) = PClosed False $ pretty "true"
ppExpr (HyperQube Hyper) (Pebool False) = PClosed False $ pretty "false"
ppExpr (GenQBF _) (Pebool True) = PClosed False $ pretty "true"
ppExpr (GenQBF _) (Pebool False) = PClosed False $ pretty "false"
ppExpr m (Pebool True) = PClosed False $ pretty "TRUE"
ppExpr m (Pebool False) = PClosed False $ pretty "FALSE"
ppExpr m (Peint i) = PClosed False $ pretty i
ppExpr m@(AutoHyper Hyper) (Peop1 Patom e) = PClosed False $ braces $ ppClosedExpr m False e
ppExpr m@(GenQBF _) (Peop1 Pnext e) = PDoc $ ppClosedExpr m False e <> pretty "'"
ppExpr m (Peop1 Pnext e) = PDoc $ pp m Pnext <+> ppClosedExpr m True e
ppExpr m@(HyperQube Hyper) (Peop1 o e) | isLTLOp1 o = PDoc $ pp m o <+> parens (unPDoc $ ppExpr m e)
ppExpr m@(GenQBF _) (Peop1 o e) | isLTLOp1 o = PDoc $ pp m o <+> parens (unPDoc $ ppExpr m e)
ppExpr m (Peop1 o e) = PDoc $ pp m o <+> ppClosedExpr m False e
ppExpr m@(HyperQube Hyper) e@(Peop2 o@(isCmpOp2 -> True) e1 e2) = ppCmp2HyperQubeFormula o e1 e2
ppExpr m (Peop2 o e1 e2) = PDoc $ ppClosedExpr m False e1 <+> pp m o <+> ppClosedExpr m False e2
ppExpr m (Peopn Pset es) = PClosed False $ braces $ sepBy (pp m Pset) (map (ppClosedExpr m False) es)
ppExpr m (Peopn o es) = PDoc $ sepBy (pp m o) (map (ppClosedExpr m False) es)
--ppExpr m@(HyperQube Hyper) (Peproj n es t) = PClosed True $ parens $ pclose False (ppIdent m n) <> hcat (map ppProj es)
--    where ppProj e = pretty '[' <> ppClosedExpr m False e <> pretty ']'
--ppExpr m (Peproj n es t) = PClosed False $ pclose False (ppIdent m n) <> hcat (map ppProj es)
--    where ppProj e = pretty '[' <> ppClosedExpr m False e <> pretty ']'
ppExpr m (Pecase cases) = PClosed False $ nest 4 $ vcat (pretty "case":map printCase cases ++ [pretty "esac"])
    where
    printCase (l,r) = ppClosedExpr m True l <+> pretty ":" <+> pp m r <> pretty ';'
ppExpr m (Pedemorgan c e1 e2) = PDoc $ ppClosedExpr m False c <+> pretty '?' <+> ppClosedExpr m False e1 <+> pretty ':' <+> ppClosedExpr m False e2 
      
ppCmp2HyperQubeFormula :: Pop2 -> Pexpr -> Pexpr -> PDoc ann
ppCmp2HyperQubeFormula Peq e1 e2 = PClosed False $ pretty "*" <> ppClosedExpr (HyperQube Hyper) False e1 <+> pp (HyperQube Hyper) Peq <+> ppClosedExpr (HyperQube Hyper) False e2 <> pretty "*"
ppCmp2HyperQubeFormula Pneq e1 e2 = ppExpr (HyperQube Hyper) (Peop1 Pnot $ Peop2 Peq e1 e2)
ppCmp2HyperQubeFormula o e1 e2 = error $ "ppOp2HyperQube: " ++ prettyprint (Peop2 o e1 e2)
      
instance Pretty Pident where
    pretty = pclose False . ppIdent Default
      
prettyPident :: Pident -> String
prettyPident = show . pclose False . ppIdent Default
      
ppIdent :: SmvMode -> Pident -> PDoc ann
ppIdent m (Pident n dims) = ppIdent' m n dims

ppIdent' :: SmvMode -> String -> Pdims -> PDoc ann
ppIdent' m n dims | smvKind m == Smv = PClosed False $ ppName m n <> hcat (map (\dim -> pretty "[" <> ppClosedExpr m False dim <> pretty "]") dims)
ppIdent' m@Default n dims = PClosed False $ ppName m n <> ppDims m dims
ppIdent' m@(HyperQube Hyper) n dims = PClosed True $ ppName m n <> ppDims Default dims
ppIdent' m@(GenQBF _) n dims = PClosed True $ ppName m n <> ppDims m dims
ppIdent' m@(AutoHyper Hyper) n [] = PClosed True $ ppName m n
ppIdent' m@(AutoHyper Hyper) n dims = PClosed False $ pretty '\"' <> pretty (Pident n $ init dims) <> pretty '\"' <> pretty '_' <> ppClosedExpr Default False (last dims)
ppIdent' m n dims = error $ "ppIdent': " ++ show m ++ " " ++ show n ++ " " ++ show dims

prettySMV :: SmvPretty a => SmvMode -> a -> String
prettySMV m = show . pp m
 
-- identifier characters accepted by hyperqube           
hyperQubeChars :: Char -> Bool
hyperQubeChars '#' = False
hyperQubeChars '_' = False
hyperQubeChars c = True

autoHyperChars :: Char -> Bool
autoHyperChars '#' = False
autoHyperChars c = True

ppName :: SmvMode -> String -> Doc ann
ppName Default n = pretty n
ppName (HyperQube _) n = pretty $ filter hyperQubeChars n
ppName (GenQBF _) n = pretty n
ppName (AutoHyper _) n = pretty $ filter autoHyperChars n

