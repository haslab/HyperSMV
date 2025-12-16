module QCIR.Solver where

import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.List.Split
import qualified Shelly
import qualified Text.Parsec as Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Char as Parsec
import qualified Text.Parsec.String as Parsec
import qualified Text.Parsec.Token as Parsec
import qualified Text.Parsec.Language as Parsec
import GHC.Generics
import Prettyprinter
import Control.Monad.IO.Class
import Data.Data
import Data.Typeable

import Utils
import Parser

data Solver = Quabs
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
type IsNegative = Bool
    
data Result = Result { result_type :: ResultType, result_vals :: ResultValues }
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
type ResultValues = IntMap IsNegative
    
data ResultType = SAT | UNSAT
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
instance Pretty ResultType where
    pretty SAT = pretty "SAT"
    pretty UNSAT = pretty "UNSAT"

resultTypeParser :: Parser ResultType
resultTypeParser = (Parsec.string "SAT" >> return SAT) <||> (Parsec.string "UNSAT" >> return UNSAT)
    
solve :: Bool -> Solver -> Bool -> Maybe String -> FilePath -> IO Result
solve isDebug Quabs witness container file = do
    let doWitness = if witness then [Left "--partial-assignment"] else []
    out <- runDockerCommand isDebug container $ Command "quabs" $ doWitness ++ [Right file] 
    return $ parseQuabs out
    
quabsParser :: Parser Result
quabsParser = do
    vs <- quabsValuesParser <||> return IntMap.empty
    r <- quabsTypeParser
    Parsec.spaces
    Parsec.eof
    return $ Result r vs
    
quabsValuesParser :: Parser (IntMap IsNegative)
quabsValuesParser = do
    Parsec.string "V"
    hspaces
    is <- Parsec.manyTill (negIntParser <* hspaces) (Parsec.string "0")
    hspaces
    Parsec.endOfLine
    return $ IntMap.fromList is
   
quabsTypeParser :: Parser ResultType
quabsTypeParser = do
    Parsec.string "r"
    hspaces
    res <- resultTypeParser
    return res
    
parseQuabs :: String -> Result
parseQuabs str =
    let res = Parsec.parse quabsParser "quabs" str in
    case res of
        Left err -> error $ show err 
        Right parsed -> parsed

