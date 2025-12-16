module QCIR.Parser where

import Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Text.Parsec as Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Char as Parsec
import qualified Text.Parsec.String as Parsec
import qualified Text.Parsec.Token as Parsec
import qualified Text.Parsec.Language as Parsec
import qualified Text.Parsec.Expr as Parsec
import Control.Monad
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV

import Utils
import Error
import QCIR.Syntax
import Smv.Typing
import Parser

sep :: Parser Char
sep = (Parsec.satisfy (\c -> c == ',' || isHspace c)) Parsec.<?> "sep"
seps :: Parser ()
seps = (Parsec.skipMany sep) Parsec.<?> "seps"

quantifierParser :: Parser Quantifier
quantifierParser = forallParser Parsec.<|> existsParser
    where
    forallParser = do
        Parsec.string "forall("
        (is,_) <- manyTill (intParser <* seps) (Parsec.string ")")
        Parsec.endOfLine
        return $ QForall is
    existsParser = do
        Parsec.string "exists("
        (is,_) <- manyTill (intParser <* seps) (Parsec.string ")")
        Parsec.endOfLine
        return $ QExists is

outputParser :: Parser GateId
outputParser = do
    Parsec.string "output"
    out <- parensParser intParser
    Parsec.endOfLine
    return out

gateExprParser :: Parser GateExpr
gateExprParser = andParser Parsec.<|> orParser
    where
    andParser = do
        Parsec.string "and("
        (is,_) <- manyTill (negIntParser <* seps) (Parsec.string ")")
        let e = foldl (\acc (i,isPos) -> IntMap.insert i (not isPos) acc) IntMap.empty is
        return $ GateAnd e
    orParser = do
        Parsec.string "or("
        (is,_) <- manyTill (negIntParser <* seps) (Parsec.string ")")
        let e :: IntMap IsNegated = foldl (\acc (i,isPos) -> IntMap.insert i (not isPos) acc) IntMap.empty is
        return $ GateOr e

gateParser :: Parser (Int,GateExpr)
gateParser = do
    i <- intParser
    hspaces
    Parsec.string "="
    hspaces
    g <- gateExprParser
    return (i,g)

qcirParser :: Parser QCIR
qcirParser = do
    Parsec.string "#QCIR-G14"
    Parsec.endOfLine
    
    qs <- many1Till quantifierParser (Parsec.lookAhead $ Parsec.string "output")
    out <- outputParser
    gates <- sepByParser gateParser Parsec.endOfLine
    Parsec.spaces
    Parsec.eof
    
    return $ QCIR qs out (IntMap.fromList gates)

parseQCIR :: FilePath -> IO QCIR
parseQCIR path = do
    res <- Parsec.parseFromFile qcirParser path
    case res of
        Left err -> error $ show err 
        Right parsed -> return parsed

