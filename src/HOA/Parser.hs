module HOA.Parser where

import Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
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
import HOA.Syntax
import Parser

apexprParser :: Parser APexpr
apexprParser =
    removeHspace (Parsec.buildExpressionParser apexprOps apexprTerm)
    Parsec.<?> "expression"
  where
    apexprTerm =
        parensParser apexprParser
        Parsec.<|> (liftM APvar intParser)
        Parsec.<|> (liftM APbool boolParser)
        Parsec.<?> "simple expression"

    apexprOps =
        [ [prefix "!" APnot ]
        , [binary "&" apand2 Parsec.AssocLeft]
        , [binary "|" apor2 Parsec.AssocLeft]
        ]

    binary  name fun assoc = Parsec.Infix (Parsec.string name >> return fun) assoc
    prefix  name fun       = Parsec.Prefix (Parsec.string name >> return fun)
    postfix name fun       = Parsec.Postfix (Parsec.string name >> return fun)

hacceptancesParser :: Parser HOAacceptances
hacceptancesParser = parser Parsec.<|> return IntSet.empty
    where
    parser = liftM IntSet.fromList $ do
        Parsec.char '{'
        hspaces
        many1Till (intParser <* hspaces) (Parsec.char '}')

stateParser :: Parser (Int,HOAstate)
stateParser = do
    Parsec.string "State:"
    hspaces
    stateId <- intParser
    hspaces
    stateAccepts <- hacceptancesParser
    hspaces
    Parsec.endOfLine
    trans <- transitionsParser
    return (stateId,HOAstate stateAccepts trans)

transitionsParser :: Parser HOAtransitions
transitionsParser = do
    let stop = Parsec.lookAhead (Parsec.string "State:" Parsec.<|> Parsec.string "--END--")
    liftM HashMap.fromList $ Parsec.manyTill transitionParser stop

transitionParser :: Parser (APexpr,HOAnext)
transitionParser = do
    apexpr <- bracketsParser apexprParser
    hspaces
    nextId <- intParser
    hspaces
    nextAccepts <- hacceptancesParser
    hspaces
    Parsec.endOfLine
    return (apexpr,HOAnext nextId nextAccepts)

bodyParser :: Parser HOAstates
bodyParser = (do
    Parsec.string "--BODY--"
    Parsec.endOfLine
    let end = Parsec.string "--END--"
    xs <- many1Till stateParser end
    return $ IntMap.fromList xs) Parsec.<?> "states"   

fileParser :: Parser HOA
fileParser = do
    hoa <- sectionsParser
    body <- bodyParser
    Parsec.spaces
    Parsec.eof
    return $ hoa { hoa_states = body }

sectionsParser :: Parser HOA
sectionsParser = do
    let body = Parsec.lookAhead (Parsec.string "--BODY--")
    liftM mconcat $ Parsec.manyTill sectionParser body
    
sectionParser :: Parser HOA
sectionParser = do
    let ignore = (Parsec.manyTill Parsec.anyChar Parsec.endOfLine) >> return mempty
    let hoaSec = Parsec.string "HOA:" >> ignore
    let nameSec = Parsec.string "name:" >> ignore
    let statesSec = Parsec.string "States:" >> ignore
    let startSec = Parsec.string "Start:" >> hspaces >> Parsec.manyTill (intParser <* hspaces) Parsec.endOfLine >>= \is -> return $ mempty { hoa_starts = IntSet.fromList is }
    let apSec = Parsec.string "AP:" >> hspaces >> intParser >>= \i -> hspaces >> boundedParser i (simpleStringLiteralParser <* hspaces) >>= \aps -> Parsec.endOfLine >> return (mempty { hoa_aps = aps })
    let accnameSec = Parsec.string "acc-name:" >> ignore
    let acceptanceSec = Parsec.string "Acceptance:" >> hspaces >> intParser >>= \i -> hspaces >> acceptancesParser i >>= \acs -> Parsec.endOfLine >> return (mempty { hoa_acceptance = acs })
    let propertiesSec = Parsec.string "properties:" >> ignore
    hoaSec <||> nameSec <||> statesSec <||> startSec <||> apSec <||> accnameSec <||> acceptanceSec <||> propertiesSec

acceptancesParser :: Int -> Parser (Maybe [HOAacceptance])
acceptancesParser 0 = do
    Parsec.string "t"
    hspaces
    return Nothing
acceptancesParser i = liftM Just $ boundedParser i (acceptanceParser <* hspaces)

acceptanceParser :: Parser HOAacceptance
acceptanceParser = do
    Parsec.string "Inf"
    i <- parensParser intParser
    return (Inf i)

parseHOA :: FilePath -> IO HOA
parseHOA path = do
    res <- Parsec.parseFromFile fileParser path
    case res of
        Left err -> error $ show err 
        Right parsed -> return parsed

boolParser :: Parser Bool
boolParser = (
    (liftM (const False) $ Parsec.string "f")
    Parsec.<|>
    (liftM (const True) $ Parsec.string "t")
    ) Parsec.<?> "bool"


