-- | AutoHyper backend glue: invoking the solver, parsing its output, and back-projecting witnesses.
module ExplicitState.AutoHyper where

import Control.Applicative ((<|>))
import Data.Char (isSpace)
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Text.Parsec as Parsec
import Text.Parsec.String (Parser)
import Control.Monad
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Prettyprinter
import GHC.Generics
import Data.Data
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Safe
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap

import Pretty
import qualified Data.DD as DD
import Transform.Pexpr
import Transform.Bexpr
import Transform.Substitute
import Transform.DD.Build
import Transform.Bexpr.Packed
import ExplicitState.Witness
import Smv.Syntax
import Smv.Typing
import Smv.Trace
import ExplicitState.Eval
import ExplicitState.Syntax
import ExplicitState.Pretty
import Utils
import Parser

-- | The AutoHyper inclusion/complementation backend to run.
data Solver = Spot | Forq | Forklift | Roll | Rabit | Bait | Comp
    deriving (Data,Typeable,Eq,Ord,Show,Generic)

-- | An AutoHyper verdict and its per-dimension witnesses.
data Result = Result { result_type :: ResultType, result_vals :: Witnesses }
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
-- | Per-dimension witness traces, as (prefix,lasso) state-id lists.
type Witnesses = Map String ([Int],[Int])
    
-- | The SAT/UNSAT verdict.
data ResultType = SAT | UNSAT
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
instance Pretty ResultType where
    pretty SAT = pretty "SAT"
    pretty UNSAT = pretty "UNSAT"

-- | Run AutoHyper on the given explicit-state files and formula.
solve :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Maybe String -> Solver -> [FilePath] -> FilePath -> IO Result
solve isDebug bisim observeAtoms valueAPs domainFold witness container solver exps formula = do
    let doLog = if isDebug then [Left "--log"] else []
    let doWitness = if witness then [Left "--witness"] else []
    let doSolver = case solver of
            Spot -> [Left "--incl-spot"]
            Forq -> [Left "--incl-forq"]
            Forklift -> [Left "--incl-forklift"]
            Roll -> [Left "--incl-roll"]
            Rabit -> [Left "--incl-rabit"]
            Bait -> [Left "--incl-bait"]
            Comp -> [Left "--comp"]
    let doBisim = if bisim then [] else [Left "--no-bisim"]
    let doObserve = [Left (if observeAtoms then "--observe-atoms" else "--observe-vars")]
    let doValueAPs = if valueAPs then [] else [Left "--no-value-aps"]
    let doDomainFold = if domainFold then [] else [Left "--no-domain-fold"]
    let args = doLog ++ doWitness ++ doSolver ++ doBisim ++ doObserve ++ doValueAPs ++ doDomainFold ++ [Left "--explicit"] ++ map Right exps ++ [Right formula]
    out <- runDockerCommand isDebug container $ Command "AutoHyper" args
    return $ parseAutoHyper out

-- | Parse AutoHyper's stdout into a 'Result'.
parseAutoHyper :: String -> Result
parseAutoHyper str | all isSpace str = error $ "AutoHyper produced no output."
parseAutoHyper str =
    let res = Parsec.parse (autohyperParser) "autohyper" str in
    case res of
        Left err -> error $ show err ++ "\nAutoHyper output was:\n" ++ str
        Right parsed -> parsed

-- | Parser for an AutoHyper result block.
autohyperParser :: Parser Result
autohyperParser = do
    let startWitnesses = Parsec.string "======= Witnesses ======="
    let stop = (liftM Left startWitnesses) <||> (liftM Right resultTypeParser)
    (_,end) <- manyTill Parsec.anyChar stop
    case end of
        Left _ -> do
            witnesses <- witnessesParser
            (_,res) <- manyTill Parsec.anyChar resultTypeParser
            Parsec.spaces
            Parsec.eof
            return $ Result res witnesses
        Right res -> do
            Parsec.spaces
            Parsec.eof
            return $ Result res Map.empty

-- | Parser for the SAT/UNSAT verdict.
resultTypeParser :: Parser ResultType
resultTypeParser = (Parsec.string "SAT" >> return SAT) <||> (Parsec.string "UNSAT" >> return UNSAT)

-- | Parser for one dimension's witness line.
witnessParser :: Parser (String,([Int],[Int]))
witnessParser = do
    dim <- many1Till Parsec.anyChar (Parsec.string ":")
    hspaces
    Parsec.string "("
    (prefix,_) <- manyTill (intParser <* hspaces) (Parsec.string ")")
    hspaces
    Parsec.string "("
    (lasso,_) <- manyTill (intParser <* hspaces) (Parsec.string ")")
    hspaces
    Parsec.endOfLine
    return (dim,(prefix,lasso))

-- | Parser for the whole witnesses block.
witnessesParser :: Parser Witnesses
witnessesParser = do
--    Parsec.string "======= Witnesses ======="
    Parsec.endOfLine
    witnesses <- many1Till witnessParser (Parsec.string "=========================")
    Parsec.endOfLine
    return $ Map.fromList witnesses

-- | A chain of quotient projections from an original system down to the one AutoHyper solved.
data DDExplicitHistory dd
    = DDExplicitProjection (DDExplicitStateSystem dd) (IntMap Int) BSubst (DDExplicitHistory dd)
    | DDExplicitLeaf (DDExplicitStateSystem dd)
    -- we don't need to keep track of restrictions or extensions, as backward mapping traces is identity

-- | The original (pre-quotient) system.
sourceDDExplicitHistory :: DDExplicitHistory dd -> DDExplicitStateSystem dd
sourceDDExplicitHistory (DDExplicitProjection e renames aps h) = e
sourceDDExplicitHistory (DDExplicitLeaf e) = e

-- | The final (solved) system.
targetDDExplicitHistory :: DDExplicitHistory dd -> DDExplicitStateSystem dd
targetDDExplicitHistory (DDExplicitProjection e renames aps h) = targetDDExplicitHistory h
targetDDExplicitHistory (DDExplicitLeaf e) = e

-- | Lift witnesses on the quotiented systems back to traces of the original systems.
backtraceWitnesses :: BuildDD dd => [(String,DDExplicitHistory dd)] -> Witnesses -> Witnesses
backtraceWitnesses hists ws = Map.mapWithKey expandWitness ws
    where
    expandWitness dim trace = fst $ expandHistory (unsafeListLookupNote ("expandWitness " ++ dim) dim hists) trace
    expandHistory (DDExplicitProjection e renames aps h) trace' =  (trace,e)
        where
        -- equivalence class on target states
        equivs :: IntMap IntSet
        equivs = flipIntMapIntSafe renames
        equivOf :: Int -> IntSet
        equivOf j = case IntMap.lookup j renames of
            Nothing -> error $ "backtraceWitnesses did not find rename of " ++ show j ++ " in " ++ show renames
            Just k -> case IntMap.lookup k equivs of
                Nothing -> error $ "backtraceWitnesses did not find equiv of " ++ show k ++ " in " ++ show equivs
                Just ls -> ls
            
        msg = "expandWitnesses no trace for\n" ++ show (prettyExplicitStateSystem e) ++ "\n <- " ++ show prefix' ++" "++ show lasso' ++ "\n" ++ show (prettyExplicitStateSystem e') ++ "\n" ++ show aps
        ((prefix',lasso'),e') = expandHistory h trace'
        
        looseP i' i _ = IntSet.member i (equivOf i')
        trace = fromJustNote msg $
                    findTrace (map mkPred prefix',map mkPred lasso') e
                <|> findTrace (map looseP prefix',map looseP lasso') e
        mkPred i' i vals = IntSet.member i (equivOf i') && all checkTargetVal nvals'
            where
            (vals',_) = unsafeIntLookupNote ("expandWitness no target state " ++ show i') i' (exp_states e')
            nvals' = zip (map fst $ V.toList $ exp_vars e') (UV.toList vals')
            nvals = Map.fromList $ zip (map fst $ V.toList $ exp_vars e) (UV.toList vals)
            checkTargetVal (n,v') = case Map.lookup n nvals of
                Just v -> v == v'
                Nothing -> case Map.lookup n aps of
                    Nothing -> error $ "expandWitness no var" ++ prettyprint n
                    Just ap -> interpretBexpr nvals ap == v'
    expandHistory (DDExplicitLeaf e) trace = (trace,e)

-- | Turn AutoHyper witnesses into SMV counterexample/example traces.
constructSmvTraces :: BuildDD dd => [(String,Quant)] -> [Subst] -> Witnesses -> [DDExplicitStateSystem dd] -> [Maybe Trace]
constructSmvTraces qs names ws exps = map constructSmvTrace (zip3 qs names exps)
    where
    mkValPexpr VBool val = Pebool $ DD.valToBool val
    mkValPexpr (VInt {}) val = Peint $ DD.valToInt val
    constructSmvTrace ((dim,q),ss,exp) = case Map.lookup dim ws of
        Nothing -> Nothing
        Just (prefix,loop:lasso) -> do
            let desc = prettyprint q ++" "++ dim
            let ty = case q of { Qforall -> Counterexample; Qexists -> Example }
            let idxs = exp_varindices exp
            let mkState isLoop i =
                    let (st,_) = unsafeIntLookupNote "constructSmvTraces" i (exp_states exp)
                        vals :: Subst = Map.map (\(idx,ty) -> mkValPexpr ty $ uvIndex "constructSmvTrace" st idx) idxs
                    in State (show i) isLoop (composeSubst ss vals)
            return $ Trace desc ty (map (mkState False) prefix ++ mkState True loop : map (mkState False) lasso)

-- | Evaluate a boolean expression under a state's values.
interpretBexpr :: BuildDD dd => Map Pident (DD.Val dd) -> Bexpr -> DD.Val dd
interpretBexpr ss (Bbool b) = DD.boolToVal b
interpretBexpr ss (Bint i) = DD.intToVal i
interpretBexpr ss (Bvar (n,False) t) = unsafeLookupNote "interpretBexpr" n ss
interpretBexpr ss (Bop1 o e1) = interpretOp1 o (interpretBexpr ss e1)
interpretBexpr ss (Bop2 Pin e1 e2) = DD.boolToVal $ (interpretBexpr ss e1) `Set.member` (interpretBexprMulti ss e2)
interpretBexpr ss (Bop2 o e1 e2) = interpretOp2 o (interpretBexpr ss e1) (interpretBexpr ss e2)
interpretBexpr ss (Bopn o es) = interpretOpn o (HashSet.map (interpretBexpr ss) es)
interpretBexpr ss e = error $ "interpretBexpr " ++ show e

-- | Evaluate a set-valued expression under a state's values.
interpretBexprMulti :: BuildDD dd => Map Pident (DD.Val dd) -> Bexpr -> Set (DD.Val dd)
interpretBexprMulti ss (Bints is) = Set.map DD.intToVal $ fromIntSet is
interpretBexprMulti ss (Bopn Pset es) = Set.unions $ map (interpretBexprMulti ss) (HashSet.toList es)

-- | Evaluate a unary operator.
interpretOp1 :: BuildDD dd => Pop1 -> DD.Val dd -> DD.Val dd
interpretOp1 Pnot v = DD.boolToVal $ not $ DD.valToBool v
interpretOp1 o v = error $ "interpretOp1 " ++ show o

-- | Evaluate a binary operator.
interpretOp2 :: BuildDD dd => Pop2 -> DD.Val dd -> DD.Val dd -> DD.Val dd
interpretOp2 Pequiv v1 v2 = DD.boolToVal $ v1 == v2
interpretOp2 Peq v1 v2 = DD.boolToVal $ v1 == v2
interpretOp2 Pgeq v1 v2 = DD.boolToVal $ v1 >= v2
interpretOp2 Pgt v1 v2 = DD.boolToVal $ v1 > v2
interpretOp2 Pleq v1 v2 = DD.boolToVal $ v1 <= v2
interpretOp2 Plt v1 v2 = DD.boolToVal $ v1 < v2
interpretOp2 Pplus v1 v2 = DD.intToVal $ (DD.valToInt v1) + (DD.valToInt v2)
interpretOp2 o v1 v2 = error $ "interpretOp2 " ++ show o

-- | Evaluate an n-ary operator.
interpretOpn :: BuildDD dd => Popn -> HashSet (DD.Val dd) -> DD.Val dd
interpretOpn Pand vs = DD.boolToVal $ and $ HashSet.map DD.valToBool vs
interpretOpn Por vs = DD.boolToVal $ or $ HashSet.map DD.valToBool vs
interpretOpn o vs = error $ "interpretOpn " ++ show o

