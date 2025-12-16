module Parser where

import qualified Text.Parsec as Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Char as Parsec
import qualified Text.Parsec.String as Parsec
import qualified Text.Parsec.Token as Parsec
import qualified Text.Parsec.Language as Parsec
import Data.List as List
import Control.Monad

lexer = Parsec.makeTokenParser Parsec.emptyDef

sepByParser :: Parser a -> Parser b -> Parser [a]
sepByParser p s = go <||> (return [])
    where
    go = do
        x <- p
        continue x <||> (return [x])
    continue x = do
        s
        xs <- sepByParser p s
        return (x:xs)

parensParser :: Parser a -> Parser a
parensParser p = (Parsec.char '(' *> p <* Parsec.char ')') Parsec.<?> "parens"

bracesParser :: Parser a -> Parser a
bracesParser p = (Parsec.char '{' *> p <* Parsec.char '}') Parsec.<?> "braces"

stringLiteralParser :: Parser String
stringLiteralParser = (Parsec.stringLiteral lexer) Parsec.<?> "string literal"

negIntParser :: Parser (Int,Bool)
negIntParser =
    (liftM (,False) (Parsec.char '-' *> intParser))
    Parsec.<|>
    (liftM (,True) intParser)

intParser :: Parser Int
intParser = (fromInteger <$> Parsec.decimal lexer) Parsec.<?> "int"

integerParser :: Parser Integer
integerParser = (Parsec.integer lexer) Parsec.<?> "integer"

many1Till :: Parser a -> Parser end -> Parser [a]
many1Till p end = (do
  first <- p
  rest  <- Parsec.manyTill p end
  return (first : rest)) Parsec.<?> "many1Till"
  
(<||>) :: Parser a -> Parser a -> Parser a
x <||> y = (Parsec.try x) Parsec.<|> y

manyTill :: Parser a -> Parser end -> Parser ([a],end)
manyTill p end = (liftM ([],) end) <||> (p >>= \x -> manyTill p end >>= \(xs,e) -> return (x:xs,e))

bracketsParser :: Parser a -> Parser a
bracketsParser p = (Parsec.char '[' *> p <* Parsec.char ']') Parsec.<?> "brackets"

simpleStringLiteralParser :: Parser String
simpleStringLiteralParser = (aspa *> Parsec.manyTill Parsec.anyChar aspa) Parsec.<?> "string literal"
    where aspa = Parsec.char '\"'

hspace :: Parser Char
hspace = (Parsec.satisfy isHspace) Parsec.<?> "horizontal space"

isHspace :: Char -> Bool
isHspace c = List.elem c " \t"

hspaces :: Parser ()
hspaces = (Parsec.skipMany hspace) Parsec.<?> "horizontal spaces"

hspaces1 :: Parser ()
hspaces1 = (Parsec.skipMany1 hspace) Parsec.<?> "horizontal spaces"

boundedParser :: Int -> Parser a -> Parser [a]
boundedParser i p | i <= 0 = return []
boundedParser i p = do
    x <- p
    xs <- boundedParser (i-1) p
    return (x:xs)

removeHspace :: Parser a -> Parser a
removeHspace m = do
    inp <- Parsec.getInput
    Parsec.setInput $ filter (not . isHspace) inp
    m
