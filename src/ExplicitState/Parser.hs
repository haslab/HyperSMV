module ExplicitState.Parser where

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
import Control.Monad
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV

import Utils
import Error
import ExplicitState.Syntax
import Smv.Typing
import Parser

variableParser :: Parser (Either String String)
variableParser = (parensParser $ do
  name <- stringLiteralParser
  hspaces
  (liftM (const $ Left name) $ Parsec.string "Int") Parsec.<|> (liftM (const $ Right name) $ Parsec.string "Bool")
  ) Parsec.<?> "variable"
  
variablesParser :: Parser (V.Vector (Either String String))
variablesParser = (do
  Parsec.string "Variables:"
  hspaces
  xs <- many1Till (variableParser <* hspaces) Parsec.endOfLine
  return $ V.fromList xs) Parsec.<?> "variables"

initsParser :: Parser (IntSet)
initsParser = (do
  Parsec.string "Init:"
  hspaces
  is <- many1Till (intParser <* hspaces) Parsec.endOfLine
  return $ IntSet.fromList is) Parsec.<?> "inits"
 
acceptingParser :: Parser (IntSet)
acceptingParser = (do
  Parsec.string "Accepting:"
  hspaces
  is <- many1Till (intParser <* hspaces) Parsec.endOfLine
  return $ IntSet.fromList is) Parsec.<?> "accepts"

stateParser :: Parser (Int,(Values Int,IntSet))
stateParser = (do
    Parsec.string "State:"
    hspaces
    stateId <- intParser
    hspaces
    let assignParser = do
            name <- stringLiteralParser
            hspaces
            val <- (intParser) Parsec.<|> (liftM boolToInt boolParser)
            return val
    Parsec.char '{'
    hspaces
    varVals <- many1Till ((parensParser assignParser) <* hspaces) (Parsec.char '}')
    Parsec.endOfLine
    nexts <- many1Till (intParser <* hspaces) Parsec.endOfLine
    return (stateId, (UV.fromList varVals, IntSet.fromList nexts))) Parsec.<?> "state"

statesParser :: Parser (IntMap (Values Int,IntSet))
statesParser = (do
    Parsec.string "--BODY--"
    Parsec.endOfLine
    let end = Parsec.string "--END--"
    xs <- many1Till stateParser end
    return $ IntMap.fromList xs) Parsec.<?> "states"

fileParser :: Parser (ExplicitStateSystem String Int)
fileParser = do
    vars <- variablesParser
    initVals <- initsParser
    acceptVals <- liftM Just acceptingParser Parsec.<|> (return Nothing)
    sts <- statesParser
    Parsec.spaces
    Parsec.eof
    let vals = map fst $ IntMap.elems sts
    return $ ExplicitStateSystem (buildVarsTypes vars vals) initVals acceptVals sts

buildVarsTypes :: V.Vector (Either String String) -> [Values Int] -> V.Vector (String,VarType)
buildVarsTypes ns vs = V.imap (\i n -> either (mkint i) (mkbool i) n) ns
    where
    is = joinValues vs
    mkint i n = (n,VInt $ unsafeIntLookupNote "buildVarsTypes" i is)
    mkbool i n = (n,VBool)

joinValues :: [Values Int] -> IntMap IntSet
joinValues = foldl (\acc x -> IntMap.unionWith IntSet.union (joinValue x) acc) IntMap.empty
joinValue :: Values Int -> IntMap IntSet
joinValue vs = UV.ifoldl (\acc i v -> IntMap.insert i (IntSet.singleton v) acc) IntMap.empty vs

parseExplicitStateSystem :: FilePath -> IO (ExplicitStateSystem String Int)
parseExplicitStateSystem path = do
    res <- Parsec.parseFromFile fileParser path
    case res of
        Left err -> error $ show err 
        Right parsed -> return parsed

boolParser :: Parser Bool
boolParser = (
    (liftM (const False) $ Parsec.string "false")
    Parsec.<|>
    (liftM (const True) $ Parsec.string "true")
    ) Parsec.<?> "bool"