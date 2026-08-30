-- | External QBF solver interface and result parser.
module QBF.Solver where

import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Text.Parsec as Parsec
import Text.Parsec.String (Parser)
import GHC.Generics
import Prettyprinter
import Data.Data

import Utils
import Parser

-- | Supported external QBF solvers.
data Solver = Quabs
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
-- | Whether a literal is negated.
type IsNegative = Bool
    
-- | A solver verdict plus its assignment.
data Result = Result { result_type :: ResultType, result_vals :: ResultValues }
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
-- | A solver assignment: gate id to negation flag.
type ResultValues = IntMap IsNegative
    
-- | A solver's satisfiability verdict.
data ResultType = SAT | UNSAT
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
instance Pretty ResultType where
    pretty SAT = pretty "SAT"
    pretty UNSAT = pretty "UNSAT"

-- | Parse a SAT/UNSAT token.
resultTypeParser :: Parser ResultType
resultTypeParser = (Parsec.string "SAT" >> return SAT) <||> (Parsec.string "UNSAT" >> return UNSAT)
    
-- | Run a solver on a QCIR file and parse its result.
solve :: Bool -> Solver -> Bool -> Maybe String -> FilePath -> IO Result
solve isDebug Quabs witness container file = do
    let doWitness = if witness then [Left "--partial-assignment"] else []
    out <- runDockerCommand isDebug container $ Command "quabs" $ doWitness ++ [Right file] 
    return $ parseQuabs out
    
-- | Parse a full quabs result.
quabsParser :: Parser Result
quabsParser = do
    vs <- quabsValuesParser <||> return IntMap.empty
    r <- quabsTypeParser
    Parsec.spaces
    Parsec.eof
    return $ Result r vs
    
-- | Parse a quabs assignment line.
quabsValuesParser :: Parser (IntMap IsNegative)
quabsValuesParser = do
    Parsec.string "V"
    hspaces
    is <- Parsec.manyTill (negIntParser <* hspaces) (Parsec.string "0")
    hspaces
    Parsec.endOfLine
    return $ IntMap.fromList is
   
-- | Parse the quabs verdict line.
quabsTypeParser :: Parser ResultType
quabsTypeParser = do
    Parsec.string "r"
    hspaces
    res <- resultTypeParser
    return res
    
-- | Parse quabs' stdout.
parseQuabs :: String -> Result
parseQuabs str =
    let res = Parsec.parse quabsParser "quabs" str in
    case res of
        Left err -> error $ show err 
        Right parsed -> parsed

