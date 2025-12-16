module Alloy.Pretty where

import Prettyprinter
import Prelude hiding ((<>))

import Pretty
import Alloy.Syntax
import Utils

instance Pretty Alloy where
    pretty (Alloy imports items) = vcat (map pretty imports ++ map pretty items)

instance Pretty Item where
    pretty (ItemPred p) = pretty p
    pretty (ItemFun p) = pretty p
    pretty (ItemFact p) = pretty p
    pretty (ItemComment s) = case lines s of
        [] -> pretty ""
        [l] -> pretty "//" <+> pretty l
        (l:ls) -> nest 2 $ vcat (pretty "/*" <+> pretty l : map pretty ls ++ [pretty "*/"])
    pretty (ItemSig s) = pretty s

instance Pretty Import where
    pretty (Import n Nothing) = pretty "open" <+> pretty "module" <+> pretty n
    pretty (Import n (Just s)) = pretty "open" <+> pretty "module" <> pretty n <> pretty '[' <> pretty n <> pretty ']'

instance Pretty Sig where
    pretty (DefSig n e) = pretty "sig" <+> pretty n <+> pretty "=" <+> pretty e <+> pretty "{}"
    pretty (EnumSig n opts) = pretty "enum" <+> pretty n <+> pretty '{' <+> sepBy (pretty ',') (map pretty opts) <+> pretty '}' 
    pretty (StructSig isAbstract isTrace mult ns ext fields) = nest 2 $ vcat $
        (prettyIsAbstract isAbstract $ prettyIstrace isTrace $ prettyMult mult (pretty "sig") <+> sepBy (pretty ",") (map pretty ns) <+> prettyExtends ext (pretty '{'))
        : prettyFields fields
      where
        prettyFields [] = [pretty '}']
        prettyFields [f] = [pretty f <+> pretty '}']
        prettyFields (f:fs) = (pretty f <> pretty ',') : prettyFields fs

instance Pretty Field where
    pretty (Field True n mult rel) = pretty "var" <+> pretty n <+> pretty ':' <+> prettyMult mult (pretty rel)
    pretty (Field False n mult rel) = pretty n <+> pretty ':' <+> prettyMult mult (pretty rel)
    
prettyMult :: Maybe Multiplicity -> Doc ann -> Doc ann
prettyMult Nothing doc = doc
prettyMult (Just m) doc = pretty m <+> doc

prettyExtends :: Extends -> Doc ann -> Doc ann
prettyExtends Nothing doc = doc
prettyExtends (Just e) doc = pretty "extends" <+> pretty e <+> doc

prettyIsAbstract :: Bool -> Doc ann -> Doc ann
prettyIsAbstract False doc = doc
prettyIsAbstract True doc = pretty "abstract" <+> doc

prettyIstrace :: Bool -> Doc ann -> Doc ann
prettyIstrace False doc = doc
prettyIstrace True doc = pretty "trace" <+> doc
    
instance Pretty Relation where
    pretty (Relation xs) = prettyRelation xs
    
prettyRelation :: [(Expr,Maybe Multiplicity)] -> Doc ann
prettyRelation [(e,mult)] = prettyMult mult (pretty e)
prettyRelation ((e,mult):es) = pretty e <+> prettyMult mult (pretty "->") <+> prettyRelation es
    
instance Pretty Multiplicity where
    pretty MOne = pretty "one"
    pretty MSome = pretty "some"
    pretty MSet = pretty "set"
    pretty MLone = pretty "lone"
    
instance Pretty Fact where
    pretty (Fact f) = nest 2 $ vcat [pretty "fact" <+> pretty '{',pretty f,pretty '}']
    
instance Pretty Pred where
    pretty (Pred n args f) = nest 2 $ vcat (pretty "pred" <+> pretty n <> prettyArgs args <+> pretty '{' : map pretty f++[pretty '}'])

instance Pretty Fun where
    pretty (Fun n args ret f) = nest 2 $ vcat [pretty "fun" <+> pretty n <> prettyArgs args <+> pretty ':' <+> pretty ret <+> pretty '{' , pretty f , pretty '}']
        
prettyArgs :: [(String,Relation)] -> Doc ann
prettyArgs [] = pretty ""
prettyArgs args = pretty '[' <> sepBy (pretty ',') (map prettyArg args) <> pretty ']'
prettyArg :: (String,Relation) -> Doc ann
prettyArg (n,r) = pretty n <+> pretty ':' <+> pretty r

prettyExpr :: Expr -> Doc ann
prettyExpr (Expr1 o e2) = pretty o <+> parens (prettyExpr e2)
prettyExpr (Expr2 e1 o e2) = sepBy (pretty o) (map pParensPrintExpr $ flattenExpr2 o [e1,e2])
prettyExpr (ExprBool True) = pretty "true"
prettyExpr (ExprBool False) = pretty "false"
prettyExpr (NextExpr n) = pretty n <> pretty '\''
prettyExpr (VarExpr n) = pretty n
prettyExpr (ExprNone) = pretty "none"
prettyExpr (ApplyExpr (VarExpr n) es) = pretty n <> pretty '[' <> sepBy (pretty ',') (map pretty es) <> pretty ']'
prettyExpr (ApplyExpr e es) = parens (pretty e) <> pretty '[' <> sepBy (pretty ',') (map pretty es) <> pretty ']'

pParensPrintExpr :: Expr -> Doc ann
pParensPrintExpr e@(VarExpr {}) = prettyExpr e
pParensPrintExpr e@(ExprBool {}) = prettyExpr e
pParensPrintExpr e@(NextExpr {}) = prettyExpr e
pParensPrintExpr e@(ExprNone {}) = prettyExpr e
pParensPrintExpr e = parens (prettyExpr e)

flattenExpr2 :: Op2 -> [Expr] -> [Expr]
flattenExpr2 op [] = []
flattenExpr2 op (Expr2 e1 op' e2:es) | isCommutative op && op == op' = flattenExpr2 op (e1:e2:es)
flattenExpr2 op (e:es) = e : flattenExpr2 op es

instance Pretty Expr where
    pretty e = prettyExpr e
        
instance Pretty Op1 where
    pretty OpNo = pretty "no"
    pretty OpNot = pretty "not"
    pretty OpSome = pretty "some"
    pretty OpAlways = pretty "always"
    pretty OpEventually = pretty "eventually"
    
instance Pretty Op2 where
    pretty OpIn = pretty "in"
    pretty OpEq = pretty "="
    pretty OpComp = pretty "."
    pretty OpUnion = pretty "+"
    pretty OpAnd = pretty "and"
    pretty OpOr = pretty "or"
    pretty OpIff = pretty "iff"
    pretty OpArrow = pretty "->"
    pretty OpImplies = pretty "implies"


