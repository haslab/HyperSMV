-- | Generic Parsec helpers.
module Parser where

import qualified Text.Parsec as Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Token as Parsec
import qualified Text.Parsec.Language as Parsec
import Data.List as List
import Control.Monad

lexer = Parsec.makeTokenParser Parsec.emptyDef

-- | Parses items separated by a separator.
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

-- | Parses inside parentheses.
parensParser :: Parser a -> Parser a
parensParser p = (Parsec.char '(' *> p <* Parsec.char ')') Parsec.<?> "parens"

-- | Parses inside braces.
bracesParser :: Parser a -> Parser a
bracesParser p = (Parsec.char '{' *> p <* Parsec.char '}') Parsec.<?> "braces"

-- | Parses a quoted string literal.
stringLiteralParser :: Parser String
stringLiteralParser = (Parsec.stringLiteral lexer) Parsec.<?> "string literal"

-- | Parses an integer with an optional leading minus sign.
negIntParser :: Parser (Int,Bool)
negIntParser =
    (liftM (,False) (Parsec.char '-' *> intParser))
    Parsec.<|>
    (liftM (,True) intParser)

-- | Parses an integer.
intParser :: Parser Int
intParser = (fromInteger <$> Parsec.decimal lexer) Parsec.<?> "int"

-- | Parses an integer literal.
integerParser :: Parser Integer
integerParser = (Parsec.integer lexer) Parsec.<?> "integer"

-- | Parses one or more items until a terminator.
many1Till :: Parser a -> Parser end -> Parser [a]
many1Till p end = (do
  first <- p
  rest  <- Parsec.manyTill p end
  return (first : rest)) Parsec.<?> "many1Till"
  
-- | Backtracking alternative.
(<||>) :: Parser a -> Parser a -> Parser a
x <||> y = (Parsec.try x) Parsec.<|> y

-- | Parses items until a terminator, keeping the terminator's result.
manyTill :: Parser a -> Parser end -> Parser ([a],end)
manyTill p end = (liftM ([],) end) <||> (p >>= \x -> manyTill p end >>= \(xs,e) -> return (x:xs,e))

-- | Parses inside brackets.
bracketsParser :: Parser a -> Parser a
bracketsParser p = (Parsec.char '[' *> p <* Parsec.char ']') Parsec.<?> "brackets"

-- | Parses a double-quoted string literal.
simpleStringLiteralParser :: Parser String
simpleStringLiteralParser = (aspa *> Parsec.manyTill Parsec.anyChar aspa) Parsec.<?> "string literal"
    where aspa = Parsec.char '\"'

-- | Parses a horizontal space character.
hspace :: Parser Char
hspace = (Parsec.satisfy isHspace) Parsec.<?> "horizontal space"

-- | Whether a character is a horizontal space.
isHspace :: Char -> Bool
isHspace c = List.elem c " \t"

-- | Skips zero or more horizontal spaces.
hspaces :: Parser ()
hspaces = (Parsec.skipMany hspace) Parsec.<?> "horizontal spaces"

-- | Skips one or more horizontal spaces.
hspaces1 :: Parser ()
hspaces1 = (Parsec.skipMany1 hspace) Parsec.<?> "horizontal spaces"

-- | Parses exactly n items.
boundedParser :: Int -> Parser a -> Parser [a]
boundedParser i p | i <= 0 = return []
boundedParser i p = do
    x <- p
    xs <- boundedParser (i-1) p
    return (x:xs)

-- | Runs a parser with horizontal spaces stripped from the input.
removeHspace :: Parser a -> Parser a
removeHspace m = do
    inp <- Parsec.getInput
    Parsec.setInput $ filter (not . isHspace) inp
    m
