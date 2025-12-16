{

module Smv.Lexer where

import Prelude hiding (LT,GT,EQ)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State as State
import Data.Digits (digits, unDigits)
import Data.List as List
import qualified Data.Map as Map
import Safe
import Data.Maybe as Maybe
import Text.Printf
import Data.ByteString.Lazy (ByteString(..))
import qualified Data.ByteString.Lazy as BS

import Utils
import Location as L
import qualified Smv.Syntax as S

}

%wrapper "monadUserState-bytestring"

$blank      = [\ \t\r]
$newline    = [\n]
$digit      = [0-9]
$lower      = [a-z]
$upper      = [A-Z]
@letter     = ($lower|$upper)
@idletter   = (@letter|_)
@ident      = @idletter(@idletter|\-|\.|\#|$digit)*
@int        = [\-]?($digit)+

tokens :-

<0>     $newline                                { skip }
<0>     $blank+                                 { skip }
<0>     "--" [^\n]* $newline                  { skip }
<0>     "--" [^\n]*/{ eof }                   { skip }
<0>     @int                                  { lexInt }
<0>     \"_                                    { lexToken T_AHEND }
<0>     \"                                     { lexToken T_AHSTART }
<0>     "+"                                     { lexToken T_PLUS    }
<0>     "-"                                     { lexToken T_MINUS    }
<0>     "*"                                     { lexToken T_TIMES      }
<0>     @ident                                  { lexTokenWith (\s -> fromMaybe (T_NID s) $ Map.lookup s keywords) }
<0>     "("                                     { lexToken T_LPAREN     }
<0>     ")"                                     { lexToken T_RPAREN     }
<0>     ";"                                     { lexToken T_SEMICOLON  }
<0>     ":="                                     { lexToken T_ATTRIB  }
<0>     ":"                                     { lexToken T_COLON  }
<0>     ","                                     { lexToken T_COMMA  }

<0>     "["                                    { lexToken T_LBRACK     }  
<0>     "]"                                    { lexToken T_RBRACK     }      
<0>     "{"                                     { lexToken T_LBRACE     }
<0>     "}"                                     { lexToken T_RBRACE     }                                             
<0>     "->"                                    { lexToken T_IMPLIES     }  
<0>     "<->"                                   { lexToken T_EQUIV     }                                                
<0>     "!"                                     { lexToken T_NOT     }
<0>     "|"                                     { lexToken T_OR     }
<0>     "&"                                     { lexToken T_AND    }
<0>     "="                                     { lexToken T_EQ       }
<0>     "!="                                    { lexToken T_NEQ   }
<0>     "<="                                    { lexToken T_LEQ   }
<0>     ">="                                    { lexToken T_GEQ   }
<0>     "<"                                    { lexToken T_LT   }
<0>     ">"                                    { lexToken T_GT   }
<0>     ".."                                    { lexToken T_RANGE }
<0>     "?"                                    { lexToken T_QUESTION }
                                                
<0>     .                                       { \input@(_,_,s,_) len -> flip invalid_char s =<< l_of_lexbuf input }
<0>     ()/{ eof }                              { lexToken T_EOF }

{

-- Auxiliary structures

readInteger :: String -> Integer
readInteger = readNote "read Integer"

convertBase :: Integral a => a -> a -> [a] -> [a]
convertBase from to = digits to . unDigits from

convert_to_base :: Int -> String -> Integer
convert_to_base base input = unDigits (toEnum base) $ convertBase 10 (toEnum base) $ digits 10 $ readInteger input

invalid_char loc (c :: ByteString) = do
    let msg = printf "invalid char: `%s'" (lazyByteStringToString c)
    throwError $ ParseError loc (Just msg)

keywordSet = Map.keysSet keywords

keywords = Map.fromList
    [("MODULE"    , T_MODULE   )
    ,("VAR"   , T_VAR  )
    ,("FROZENVAR"   , T_FROZENVAR  )
    ,("JUSTICE"   , T_JUSTICE  )
    ,("DEFINE"   , T_DEFINE  )
    ,("INIT"  , T_INIT )
    ,("ASSIGN"  , T_ASSIGN )
    ,("INVAR"  , T_INVAR )
    ,("TRANS"  , T_TRANS )
    ,("LTLSPEC"   , T_LTLSPEC  )
    ,("TRUE"   , T_TRUE  )
    ,("FALSE"   , T_FALSE  )
    ,("boolean"   , T_BOOLEAN  )
    ,("bool"   , T_BOOL  )
    ,("init"   , T_INITVAR  )
    ,("next"   , T_NEXT  )
    ,("case"   , T_CASE_START  )
    ,("esac"   , T_CASE_END  )
    ,("array"   , T_ARRAY  )
    ,("union"   , T_UNION )
    ,("exists"   , T_EXISTS )
    ,("forall"   , T_FORALL )
    ,("of"   , T_OF  )
    ,("in"   , T_IN  )
    ,("mod",T_MOD)
    ,("xor",T_XOR)
    ,("F",T_F)
    ,("X",T_X)
    ,("G",T_G)
    ,("U",T_U)
    ,("Y",T_Y)
    ,("Z",T_Z)
    ,("H",T_H)
    ,("V",T_V)]

data Token
    = T_NID String
    | T_AHSTART
    | T_AHEND
    | T_INT Int
    | T_MODULE
    | T_VAR
    | T_FROZENVAR
    | T_JUSTICE
    | T_DEFINE
    | T_INIT
    | T_ASSIGN
    | T_INVAR
    | T_TRANS
    | T_LTLSPEC
    | T_TRUE
    | T_FALSE
    | T_BOOLEAN
    | T_BOOL
    | T_MOD
    | T_XOR
    | T_INITVAR
    | T_NEXT
    | T_CASE_START
    | T_CASE_END
    | T_PLUS
    | T_MINUS
    | T_TIMES
    | T_COMMA
    | T_ARRAY
    | T_UNION
    | T_QUESTION
    | T_OF
    | T_IN
    | T_F
    | T_X
    | T_G
    | T_U
    | T_V
    | T_Y
    | T_Z
    | T_H
    | T_EXISTS
    | T_FORALL
 
    | T_LPAREN     
    | T_RPAREN   
    | T_LBRACK
    | T_RBRACK  
    | T_LBRACE
    | T_RBRACE
    | T_SEMICOLON  
    | T_ATTRIB  
    | T_COLON  
    | T_IMPLIES     
    | T_EQUIV                                                
    | T_NOT    
    | T_OR     
    | T_AND    
    | T_EQ     
    | T_NEQ 
    | T_LT
    | T_LEQ
    | T_GT
    | T_GEQ
    | T_RANGE  
    
    | T_EOF
    deriving (Eq,Show)

-- Location functions

pos_cnum :: AlexPosn -> Int
pos_cnum (AlexPn o l c) = o

pos_lnum :: AlexPosn -> Int
pos_lnum (AlexPn o l c) = l

pos_bol :: AlexPosn -> Int
pos_bol (AlexPn o l c) = o - c

lexeme_start_p, lexeme_end_p :: AlexInput -> Alex AlexPosn
lexeme_start_p lb@(alexStartPos,_,_,_) = return alexStartPos
lexeme_end_p lb = alexGetPos

l_make :: String -> AlexPosn -> AlexPosn -> L.T
l_make fname p1 p2 =
  let mkpos p = (pos_lnum p, pos_cnum p - pos_bol p)
  in
    L.T { loc_fname = fname,
      loc_start = mkpos p1    ,
      loc_end   = mkpos p2    ,
      loc_bchar = pos_cnum p1 ,
      loc_echar = pos_cnum p2 }

l_of_lexbuf :: AlexInput -> Alex L.T
l_of_lexbuf lb = do
  fn <- alexGetFilename
  p1 <- lexeme_start_p lb 
  p2 <- lexeme_end_p lb 
  return $ l_make fn p1 p2

-- Lexer functions

eof :: user -> AlexInput -> Int -> AlexInput -> Bool
eof _ input1 len (_,_,s,_) = BS.null s

lexInt :: AlexInput -> Int64 -> Alex (Located Token)
lexInt = lexTokenWith (T_INT . fromEnum . convert_to_base 10)

lexToken :: Token -> AlexInput -> Int64 -> Alex (Located Token)
lexToken t = lexTokenWith (const t)

lexTokenWith :: (String -> Token) -> AlexInput -> Int64 -> Alex (Located Token)
lexTokenWith f inp@(_,_,s,_) l = do
    loc <- l_of_lexbuf inp
    let s1 = BS.take l s
    return $ Located loc (f $ lazyByteStringToString s1)

-- Alex functions

data AlexUserState = AlexUserState 
    { filename     :: !String
    }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState "" 

alexGetFilename :: Alex String
alexGetFilename = State.gets filename

instance MonadState AlexUserState Alex where
    get = alexGetUserState
    put = alexSetUserState

alexEOF :: Alex (Located Token)
alexEOF = do 
    inp <- alexGetInput
    loc <- l_of_lexbuf inp
    return $ Located loc T_EOF

lexer :: (Located Token -> Alex a) -> Alex a
lexer cont = alexMonadScan >>= cont

alexGetPos :: Alex AlexPosn
alexGetPos = do
    (p,_,_,_) <- alexGetInput
    return p

alexSetPos :: AlexPosn -> Alex ()
alexSetPos p = do
    (_,x,y,z) <- alexGetInput
    alexSetInput (p,x,y,z)

instance MonadError ParseError Alex where
    throwError e = Alex $ \ s -> Left (show e)
    catchError (Alex un) f = Alex $ \ s -> either (catchMe s) Right (un s)
        where 
        catchMe s x = fmap (\x -> (s,x)) $ runAlex "" $ f $ ParseError (L._dummy) (Just x)

getTokens :: Alex [Located Token]
getTokens = do 
    tok <- alexMonadScan
    case pl_desc tok of
        T_EOF -> return [tok]
        _ -> liftM (tok:) getTokens

runLexerM :: String -> ByteString -> (Alex a) -> Either String a
runLexerM fn str parse = runAlex str $ do
    alexSetPos alexStartPos
    put (alexInitUserState { filename = fn })
    parse

runLexerWith :: String -> ByteString -> ([Located Token] -> Alex a) -> Either String a
runLexerWith fn str parse = runLexerM fn str (getTokens >>= parse)

runLexer :: String -> ByteString -> Either String [Located Token]
runLexer fn str = runLexerWith fn str return

data ParseError = ParseError L.T (Maybe String) deriving (Eq,Show)

}
