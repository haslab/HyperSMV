{

module Smv.Parser where

import Control.Monad.Except
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.HashSet as HashSet
import qualified Data.IntSet as IntSet
import Data.ByteString.Lazy (ByteString(..))
import qualified Data.ByteString.Lazy as BS

import Smv.Syntax as S
import qualified Smv.Lexer as L
import Location as L

}

%name smvParser pmodule
%name exprParser pexpr
%name formulaParser pformula
%name identParser pident
%tokentype { Located L.Token }

%monad { L.Alex } { (>>=) } { pure }
%lexer { L.lexer } { Located _ L.T_EOF }

%token AHSTART          { Located _ L.T_AHSTART }
%token AHEND            { Located _ L.T_AHEND }
%token COMMA            { Located _ L.T_COMMA }
%token LPAREN           { Located _ L.T_LPAREN }
%token RPAREN           { Located _ L.T_RPAREN }
%token LBRACK           { Located _ L.T_LBRACK }
%token RBRACK           { Located _ L.T_RBRACK }
%token LBRACE           { Located _ L.T_LBRACE }
%token RBRACE           { Located _ L.T_RBRACE }
%token SEMICOLON        { Located _ L.T_SEMICOLON }
%token ATTRIB           { Located _ L.T_ATTRIB  }
%token COLON            { Located _ L.T_COLON }
%token IMPLIES          { Located _ L.T_IMPLIES }
%token EQUIV            { Located _ L.T_EQUIV }                                  
%token NOT              { Located _ L.T_NOT }
%token PLUS              { Located _ L.T_PLUS }
%token MINUS              { Located _ L.T_MINUS }
%token TIMES              { Located _ L.T_TIMES }
%token INITVAR          { Located _ L.T_INITVAR }
%token NEXT             { Located _ L.T_NEXT }
%token OR               { Located _ L.T_OR }
%token AND              { Located _ L.T_AND }
%token EQ               { Located _ L.T_EQ }
%token NEQ              { Located _ L.T_NEQ }
%token LT              { Located _ L.T_LT }
%token LEQ              { Located _ L.T_LEQ }
%token GT              { Located _ L.T_GT }
%token GEQ              { Located _ L.T_GEQ }
%token TRUE             { Located _ L.T_TRUE }
%token FALSE            { Located _ L.T_FALSE }
%token BOOLEAN          { Located _ L.T_BOOLEAN }
%token CASE_START          { Located _ L.T_CASE_START }
%token CASE_END          { Located _ L.T_CASE_END }
%token IN         { Located _ L.T_IN }
%token F          { Located _ L.T_F }
%token G          { Located _ L.T_G }
%token X          { Located _ L.T_X }
%token U          { Located _ L.T_U }
%token V          { Located _ L.T_V }
%token Y          { Located _ L.T_Y }
%token Z          { Located _ L.T_Z }
%token H          { Located _ L.T_H }

%token MODULE           { Located _ L.T_MODULE }
%token JUSTICE           { Located _ L.T_JUSTICE }
%token VAR              { Located _ L.T_VAR    }
%token FROZENVAR        { Located _ L.T_FROZENVAR    }
%token DEFINE           { Located _ L.T_DEFINE  }
%token INIT             { Located _ L.T_INIT }
%token ASSIGN           { Located _ L.T_ASSIGN }
%token INVAR            { Located _ L.T_INVAR }
%token TRANS            { Located _ L.T_TRANS }
%token LTLSPEC          { Located _ L.T_LTLSPEC  }
%token RANGE          { Located _ L.T_RANGE  }
%token ARRAY          { Located _ L.T_ARRAY  }
%token OF          { Located _ L.T_OF  }
%token UNION          { Located _ L.T_UNION  }
%token QUESTION          { Located _ L.T_QUESTION  }
%token EXISTS          { Located _ L.T_EXISTS }
%token FORALL          { Located _ L.T_FORALL  }

%token NID              { (locatedNID -> Just $$) }
%token INT              { (locatedINT -> Just $$) }

-- later means higher precedence (bind more tightly)
%nonassoc NEXT ATTRIB QUESTION COLON
%left OR
%left AND
%right IMPLIES EQUIV
%nonassoc EQ NEQ LT LEQ GT GEQ
%nonassoc U V
%left IN
%left PLUS MINUS TIMES UNION

%%

ident :: { Located String }
    : NID { $1 }
    
--  * -------------------------------------------------------------------- *)

dims :: { Located Pdims }
    : list(dim) { mk_loc _dummy $ map unloc $1 }
    
dim :: { Located Pexpr }
    : LBRACK pexpr RBRACK { mk_loc (loc $1) (unloc $2) }

pident :: { Located Pident }
    : ident dims { mk_loc (loc $1) $ Pident (unloc $1) (unloc $2) }
    | AHSTART pident AHEND ident { mk_loc (loc $1) $ addDimPident (unloc $2) (mkQuantDim (unloc $4)) }

pterm :: { Located Pexpr }
    : pident { lmap (\n -> Peident n EUnknown) $1 }
    | NEXT LPAREN pexpr RPAREN { mk_loc (loc $1) (Peop1 Pnext (unloc $3)) }
    | TRUE { mk_loc (loc $1) (Pebool True) }
    | FALSE { mk_loc (loc $1) (Pebool False) }
    | INT { mk_loc (loc $1) (Peint $ unloc $1) }
    | parens(pexpr) { $1 }
    | LBRACE rtuple(pexpr) RBRACE { mk_loc (loc $1) (pset $ map unloc $ unloc $2) }
    | CASE_START list(pcase) CASE_END { mk_loc (loc $1) $ Pecase $ map unloc $2 }
    
    | X   pterm { mk_loc (loc $1) (Peop1 Px (unloc $2)) }
    | G   pterm { mk_loc (loc $1) (Peop1 Pg (unloc $2)) }
    | F   pterm { mk_loc (loc $1) (Peop1 Pf (unloc $2)) }
    | Y   pterm { mk_loc (loc $1) (Peop1 Py (unloc $2)) }
    | Z   pterm { mk_loc (loc $1) (Peop1 Pz (unloc $2)) }
    | H   pterm { mk_loc (loc $1) (Peop1 Ph (unloc $2)) }
    | NOT pterm { mk_loc (loc $1) (Peop1 Pnot (unloc $2)) }

penext :: { Pexpr -> Located Pexpr }
    : EQ pexpr      { \e -> mk_loc (loc $1) (Peop2 Peq e (unloc $2)) }
    | NEQ pexpr     { \e -> mk_loc (loc $1) (Peop2 Pneq e (unloc $2)) }
    | LT  pexpr     { \e -> mk_loc (loc $1) (Peop2 Plt e (unloc $2)) }
    | LEQ pexpr     { \e -> mk_loc (loc $1) (Peop2 Pleq e (unloc $2)) }
    | GT pexpr      { \e -> mk_loc (loc $1) (Peop2 Pgt e (unloc $2)) }
    | GEQ pexpr     { \e -> mk_loc (loc $1) (Peop2 Pgeq e (unloc $2)) }
    | PLUS pexpr    { \e -> mk_loc (loc $1) (Peop2 Pplus e (unloc $2)) }
    | MINUS pexpr   { \e -> mk_loc (loc $1) (Peop2 Pminus e (unloc $2)) }
    | TIMES pexpr   { \e -> mk_loc (loc $1) (Peop2 Ptimes e (unloc $2)) }
    | UNION pexpr   { \e -> mk_loc (loc $1) (Peop2 Punion e (unloc $2)) }
    | IN pexpr      { \e -> mk_loc (loc $1) (Peop2 Pin e (unloc $2)) }
    | U pexpr       { \e -> mk_loc (loc $1) (Peop2 Pu e (unloc $2)) }
    | V pexpr       { \e -> mk_loc (loc $1) (Peop2 Pv e (unloc $2)) }
    
    | IMPLIES pexpr { \e -> mk_loc (loc $1) (Peop2 Pimplies e (unloc $2)) }
    | EQUIV pexpr   { \e -> mk_loc (loc $1) (Peop2 Pequiv e (unloc $2)) }
    
    | AND pexpr     { \e -> mk_loc (loc $1) (peopn2 Pand e (unloc $2)) }
    | OR pexpr      { \e -> mk_loc (loc $1) (peopn2 Por e (unloc $2)) }
    
    | QUESTION pexpr COLON pexpr { \e -> mk_loc (loc $1) $ Pedemorgan e (unloc $2) (unloc $4) }

pexpr :: { Located Pexpr }
    : pterm { $1 }
    | pexpr penext { $2 (unloc $1) }

-- (* -------------------------------------------------------------------- *)

ptype :: { Located Ptype }
    : BOOLEAN { mk_loc (loc $1) Pboolean }
    | INT RANGE INT { mk_loc (loc $1) (Pint (unloc $1) (unloc $3)) }
    | ARRAY INT RANGE INT OF ptype { mk_loc (loc $1) (Parray (unloc $2) (unloc $4) (unloc $6)) }
    | LBRACE rtuple(INT) RBRACE { mk_loc (loc $1) $ Penum (IntSet.fromList $ map unloc $ unloc $2)  }

-- (* -------------------------------------------------------------------- *)

pvar :: { Located (Pident,Ptype) }
    : pident COLON ptype SEMICOLON        { mk_loc (loc $1) (unloc $1,unloc $3) }

pjustice :: { Located Pexpr }
    : JUSTICE pexpr SEMICOLON { mk_loc (loc $1) (unloc $2) }
    | JUSTICE pexpr { mk_loc (loc $1) (unloc $2) }
    
pdefine :: { Located (String,Pexpr) }
    : ident ATTRIB pexpr SEMICOLON { mk_loc (loc $1) (unloc $1,unloc $3) }

piassign :: { Located [Located Passign] }
    : ASSIGN list(passign) { mk_loc (loc $1) $2 }

passign :: { Located Passign }
    : INITVAR LPAREN pident RPAREN ATTRIB pexpr SEMICOLON { mk_loc (loc $1) $ Passign (Painit $ unloc $3) (unloc $6) }
    | NEXT LPAREN pident RPAREN ATTRIB pexpr SEMICOLON { mk_loc (loc $1) $ Passign (Panext (unloc $3)) (unloc $6) }

pcase :: {Located (Pexpr,Pexpr) }
    : pexpr COLON pexpr SEMICOLON { mk_loc (loc $1) (unloc $1,unloc $3) }

pinit :: { Located Pexpr }
    : INIT pexpr SEMICOLON { mk_loc (loc $1) (unloc $2) }
    | INIT pexpr { mk_loc (loc $1) (unloc $2) }

pinvar :: { Located Pexpr }
    : INVAR pexpr SEMICOLON { mk_loc (loc $1) (unloc $2) }
    | INVAR pexpr { mk_loc (loc $1) (unloc $2) }
    
ptrans :: { Located Pexpr }
    : TRANS pexpr SEMICOLON { mk_loc (loc $1) (unloc $2) }
    | TRANS pexpr { mk_loc (loc $1) (unloc $2) }
    
pltlspec :: { Located Pexpr }
    : LTLSPEC pexpr SEMICOLON { mk_loc (loc $1) (unloc $2) }
    | LTLSPEC pexpr { mk_loc (loc $1) (unloc $2) }

-- (* -------------------------------------------------------------------- *)

pitem :: { Located Pitem }
    : VAR list(pvar) { mk_loc (loc $1) (pivar $2 False) }
    | FROZENVAR list(pvar) { mk_loc (loc $1) (pivar $2 True) }
    | DEFINE list(pdefine)   { mk_loc (loc $1) (pidefine $2) }
    | pjustice { (lmap Pijustice $1) }
    | pinit     { lmap Piinit $1 }
    | piassign   { lmap Piassign $1 }
    | pinvar    { lmap Piinvar $1 }
    | ptrans    { lmap Pitrans $1 }
    | pltlspec  { lmap Piltlspec $1 }

-- (* -------------------------------------------------------------------- *)

pmodule :: { Located Pmodule }
    : MODULE ident list(pitem) { mk_loc (loc $1) (Pmodule (unloc $2) $3) }

-- (* -------------------------------------------------------------------- *)

pformula :: { Located Pformula }
    : EXISTS ident pformula { mk_loc (loc $1) $ Pfexists (init $ unloc $2) (unloc $3) }
    | FORALL ident pformula { mk_loc (loc $1) $ Pfforall (init $ unloc $2) (unloc $3) }
    | pexpr { lmap Pfltl $1 }

--  * -------------------------------------------------------------------- *)

plist1(X, S)
    : separated_nonempty_list(S, X) { $1 }

prefix(S, X)
    : S X { lmerge $1 $2 }

postfix(X, S)
    : X S { lmerge $2 $1 }

parens(X)
    : delimited(LPAREN, X, RPAREN) { $1 }

brackets(X)
    : delimited(LBRACKET, X, RBRACKET) { $1 }

braces(X)
    : delimited(LBRACE, X, RBRACE) { $1 }

rtuple(X)
    : separated_list(COMMA, X) { $1 }

rtuple1(X)
    : separated_nonempty_list(COMMA, X) { $1 }

tuple(X)
    : parens(rtuple(X)) { $1 }
    | rtuple(X) { $1 }

tuple1(X)
    : parens(rtuple1(X)) { $1 }
    | rtuple1(X) { $1 }

parens_tuple(X)
    : parens(rtuple(X)) { $1 }

brackets_tuple(X)
    : brackets(rtuple(X)) { $1 }

delimited(X,Y,Z)
    : X Y Z { lmk2 $1 $3 (unloc $2) }

separated_nonempty_list(s,p)
    : p list(snd(s,p)) { let xs = $1 : $2 in mk_loc (locCat xs) xs }

separated_list(s,p)
    : p list(snd(s,p))             { let xs = ($1:$2) in mk_loc (locCat xs) xs }
    |                              { mk_loc _dummy [] }

nonempty_list(p) : list1(p) { mk_loc (locCat $1) $1 }

empty_list(p)   : list1(p)            { mk_loc (locCat $1) $1 }
                |                     { mk_loc _dummy [] }

option(p)       : p                   { mk_loc (loc $1) (Just $1) }
                |                     { mk_loc _dummy Nothing }

-- happy rules

fst(p,q)        : p q                 { $1 }
snd(p,q)        : p q                 { $2 }
both(p,q)       : p q                 { ($1,$2) }

rev_list1(p)    : p                   { [$1] }
                | rev_list1(p) p      { $2 : $1 }
list1(p)        : rev_list1(p)        { reverse $1 }
list(p)         : list1(p)            { ($1) }
                |                     { [] }

{

locatedNID :: Located L.Token -> Maybe (Located String)
locatedNID (Located sp (L.T_NID v)) = Just (Located sp v)
locatedNID _ = Nothing

locatedINT :: Located L.Token -> Maybe (Located Int)
locatedINT (Located sp (L.T_INT v)) = Just (Located sp v)
locatedINT _ = Nothing

happyError = do
  input <- L.alexGetInput
  sp <- L.l_of_lexbuf input
  throwError $ L.ParseError sp (Just "unknown happy error")

runSMVParser :: String -> ByteString -> Either String (Located Pmodule)
runSMVParser fn str = L.runLexerM fn str smvParser

runFormulaParser :: String -> ByteString -> Either String (Located Pformula)
runFormulaParser fn str = L.runLexerM fn str formulaParser

runExprParser :: String -> ByteString -> Either String (Located Pexpr)
runExprParser fn str = L.runLexerM fn str exprParser

runIdentParser :: String -> ByteString -> Either String (Located Pident)
runIdentParser fn str = L.runLexerM fn str identParser

}