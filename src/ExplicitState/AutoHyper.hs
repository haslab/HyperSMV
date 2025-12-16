module ExplicitState.AutoHyper where

import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Map (Map(..))
import qualified Data.Map as Map
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
import Prettyprinter
import GHC.Generics
import Data.Data
import Data.Typeable
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
import Transform.DDs
import Transform.Bpacked
import Transform.SmvToExplicitState
import Smv.Syntax
import Smv.Typing
import Smv.Trace
import ExplicitState.Eval
import ExplicitState.Syntax
import ExplicitState.Pretty
import Utils
import Parser

--import Debug.Trace as Trace

data Solver = Spot | Forq | Forklift | Roll | Rabit | Bait
    deriving (Data,Typeable,Eq,Ord,Show,Generic)

data Result = Result { result_type :: ResultType, result_vals :: Witnesses }
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
type Witnesses = Map String ([Int],[Int])
    
data ResultType = SAT | UNSAT
    deriving (Data,Typeable,Eq,Ord,Show,Generic)
    
instance Pretty ResultType where
    pretty SAT = pretty "SAT"
    pretty UNSAT = pretty "UNSAT"

solve :: Bool -> Bool -> Bool -> Maybe String -> Solver -> [FilePath] -> FilePath -> IO Result
solve isDebug bisim witness container solver exps formula = do
    let doLog = if isDebug then [Left "--log"] else []
    let doWitness = if witness then [Left "--witness"] else []
    let doSolver = case solver of
            Spot -> [Left "--incl-spot"]
            Forq -> [Left "--incl-forq"]
            Forklift -> [Left "--incl-forklift"]
            Roll -> [Left "--incl-roll"]
            Rabit -> [Left "--incl-rabit"]
            Bait -> [Left "--incl-bait"]
    let doBisim = if bisim then [] else [Left "--no-bisim"] 
    let args = doLog ++ doWitness ++ doSolver ++ doBisim ++ [Left "--explicit"] ++ map Right exps ++ [Right formula]
    out <- runDockerCommand isDebug container $ Command "AutoHyper" args
    return $ parseAutoHyper out

parseAutoHyper :: String -> Result
parseAutoHyper str =
    let res = Parsec.parse (autohyperParser) "autohyper" str in
    case res of
        Left err -> error $ show err 
        Right parsed -> parsed

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

resultTypeParser :: Parser ResultType
resultTypeParser = (Parsec.string "SAT" >> return SAT) <||> (Parsec.string "UNSAT" >> return UNSAT)

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

witnessesParser :: Parser Witnesses
witnessesParser = do
--    Parsec.string "======= Witnesses ======="
    Parsec.endOfLine
    witnesses <- many1Till witnessParser (Parsec.string "=========================")
    Parsec.endOfLine
    return $ Map.fromList witnesses

data DDExplicitHistory dd
    = DDExplicitProjection (DDExplicitStateSystem dd) (IntMap Int) BSubst (DDExplicitHistory dd)
    | DDExplicitLeaf (DDExplicitStateSystem dd)
    -- we don't need to keep track of restrictions or extensions, as backward mapping traces is identity

sourceDDExplicitHistory :: DDExplicitHistory dd -> DDExplicitStateSystem dd
sourceDDExplicitHistory (DDExplicitProjection e renames aps h) = e
sourceDDExplicitHistory (DDExplicitLeaf e) = e

targetDDExplicitHistory :: DDExplicitHistory dd -> DDExplicitStateSystem dd
targetDDExplicitHistory (DDExplicitProjection e renames aps h) = targetDDExplicitHistory h
targetDDExplicitHistory (DDExplicitLeaf e) = e

--mkDDExplicitHistories :: [[(DDExplicitStateSystem dd,BSubst)]] -> [DDExplicitHistory dd]
--mkDDExplicitHistories [] = []
--mkDDExplicitHistories [xs] = map DDExplicitLeaf xs
--mkDDExplicitHistories (xs:xss) = map (\((e,aps),h) -> DDExplicitProjection e aps h) $ zip xs (mkDDExplicitHistories xss)

backtraceWitnesses :: BuildDD dd => [(String,DDExplicitHistory dd)] -> Witnesses -> Witnesses
backtraceWitnesses hists ws = Map.mapWithKey expandWitness ws
    where
--    expandWitness :: String -> ([Int],[Int]) -> ([Int],[Int])
    expandWitness dim trace = fst $ expandHistory (unsafeListLookupNote ("expandWitness " ++ dim) dim hists) trace
    expandHistory (DDExplicitProjection e renames aps h) trace' = {-Trace.trace (msg)-} (trace,e)
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
        trace = fromJustNote msg $ findTrace (map mkPred prefix',map mkPred lasso') e
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

--expandWitnesses :: BuildDD dd => [String] -> [DDExplicitStateSystem dd] -> [DDExplicitStateSystem dd] -> [BSubst] -> Witnesses -> Witnesses
--expandWitnesses qs fullexps exps apss ws = Map.mapWithKey expandWitness ws
--    where
--    xs3 = zip qs $ zip3 fullexps exps apss
----    expandWitness :: String -> ([Int],[Int]) -> ([Int],[Int])
--    expandWitness dim (prefix,lasso) = fromJustNote "expandWitnesses no trace" $ findTrace (map mkPred prefix,map mkPred lasso) fullexp
--        where
--        (fullexp,exp,aps) = unsafeListLookupNote ("expandWitness " ++ dim) dim xs3
----        mkPred :: Int -> Values (DD.Val dd) -> DDExplicitPred dd
--        mkPred i fullvals = all checkVal nvals
--            where
--            (vals,_) = unsafeIntLookupNote ("expandWitness no state " ++ show i) i (exp_states exp)
--            nvals = zip (map fst $ V.toList $ exp_vars exp) (UV.toList vals)
--            fullnvals = Map.fromList $ zip (map fst $ V.toList $ exp_vars fullexp) (UV.toList fullvals)
--            checkVal (n,v) = case Map.lookup n fullnvals of
--                Just v' -> v == v'
--                Nothing -> case Map.lookup n aps of
--                    Just e -> v == interpretBexpr fullnvals e
--                    Nothing -> error $ "expandWitness no var" ++ prettyprint n

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

interpretBexpr :: BuildDD dd => Map Pident (DD.Val dd) -> Bexpr -> DD.Val dd
interpretBexpr ss (Bbool b) = DD.boolToVal b
interpretBexpr ss (Bint i) = DD.intToVal i
interpretBexpr ss (Bvar (n,False) t) = unsafeLookupNote "interpretBexpr" n ss
interpretBexpr ss (Bop1 o e1) = interpretOp1 o (interpretBexpr ss e1)
interpretBexpr ss (Bop2 Pin e1 e2) = DD.boolToVal $ (interpretBexpr ss e1) `Set.member` (interpretBexprMulti ss e2)
interpretBexpr ss (Bop2 o e1 e2) = interpretOp2 o (interpretBexpr ss e1) (interpretBexpr ss e2)
interpretBexpr ss (Bopn o es) = interpretOpn o (HashSet.map (interpretBexpr ss) es)
interpretBexpr ss e = error $ "interpretBexpr " ++ show e

interpretBexprMulti :: BuildDD dd => Map Pident (DD.Val dd) -> Bexpr -> Set (DD.Val dd)
interpretBexprMulti ss (Bints is) = Set.map DD.intToVal $ fromIntSet is
interpretBexprMulti ss (Bopn Pset es) = Set.unions $ map (interpretBexprMulti ss) (HashSet.toList es)

interpretOp1 :: BuildDD dd => Pop1 -> DD.Val dd -> DD.Val dd
interpretOp1 Pnot v = DD.boolToVal $ not $ DD.valToBool v
interpretOp1 o v = error $ "interpretOp1 " ++ show o

interpretOp2 :: BuildDD dd => Pop2 -> DD.Val dd -> DD.Val dd -> DD.Val dd
interpretOp2 Pequiv v1 v2 = DD.boolToVal $ v1 == v2
interpretOp2 Peq v1 v2 = DD.boolToVal $ v1 == v2
interpretOp2 Pgeq v1 v2 = DD.boolToVal $ v1 >= v2
interpretOp2 Pgt v1 v2 = DD.boolToVal $ v1 > v2
interpretOp2 Pleq v1 v2 = DD.boolToVal $ v1 <= v2
interpretOp2 Plt v1 v2 = DD.boolToVal $ v1 < v2
interpretOp2 Pplus v1 v2 = DD.intToVal $ (DD.valToInt v1) + (DD.valToInt v2)
interpretOp2 o v1 v2 = error $ "interpretOp2 " ++ show o

interpretOpn :: BuildDD dd => Popn -> HashSet (DD.Val dd) -> DD.Val dd
interpretOpn Pand vs = DD.boolToVal $ and $ HashSet.map DD.valToBool vs
interpretOpn Por vs = DD.boolToVal $ or $ HashSet.map DD.valToBool vs
interpretOpn o vs = error $ "interpretOpn " ++ show o

