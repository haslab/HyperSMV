-- | Turning a solver's boolean assignment back into SMV traces.
module QBF.Witness where

import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Identity

import Utils
import Pretty
import Smv.Syntax
import Smv.Pretty
import Transform.Pexpr
import Transform.Substitute
import Smv.Trace
import Transform.Normalize
import QBF.Gates (identName)
import QBF.Solver (ResultValues)

-- | Build SMV traces from a solver assignment.
constructSmvTraces :: Bool -> Bool -> [(String,Quant)] -> [IntMap Subst] -> ResultValues -> IO [Maybe Trace]
constructSmvTraces isDebug doSelfLoops dims names res = mapM constructSmvTrace $ zip dims names
    where
    ress :: Subst
    ress = IntMap.foldlWithKey (\acc i b -> Map.insert (identName i) (Pebool b) acc) Map.empty res
    constructSmvTrace :: ((String,Quant),IntMap Subst) -> IO (Maybe Trace)
    constructSmvTrace ((dim,q),vs) = traverse (fillSmvTrace isDebug doSelfLoops) $ checkStaticTrace $ Trace desc ty (map mkState $ IntMap.toList vs)
        where
        ty = case q of { Qforall -> Counterexample; Qexists -> Example }
        desc = prettyprint q ++" "++ dim
        mkState (i,ss) = State (show i) False (fmap evaluateExpr $ composeSubst ss ress)

-- | Fill unbounded variables and mark self-loops.
fillSmvTrace :: Bool -> Bool -> Trace -> IO Trace
fillSmvTrace isDebug doSelfLoops (Trace desc ty sts) = do
    sts' <- mapM fillState sts
    let sts'' = if doSelfLoops then mapLast mkSelfLoop sts' else sts'
    return $ Trace desc ty sts''
  where
    mkSelfLoop :: State -> State
    mkSelfLoop (State n _ ss) = State n True ss

    fillState :: State -> IO State
    fillState (State n l ss) = do
        ss' <- traverse fillExpr ss
        return $ State n l ss'
    fillExpr :: Pexpr -> IO Pexpr
    fillExpr e = do
        let vs = varSet e
        let blanks = Map.fromSet (const $ Pebool True) vs
        if Map.null blanks
            then return e
            else do
                when isDebug $ putStrLn $ "Warning: filling unbounded QCIR variables " ++ (unwords $ map prettyPident $ Set.toList vs)
                return $ evaluateExpr $ runIdentity $ substExpr blanks blanks True e

-- | Discard a trace that is entirely free.
checkStaticTrace :: Trace -> Maybe Trace
checkStaticTrace t@(Trace desc ty sts) = if all isFreeState sts then Nothing else Just t

-- | Whether a state is entirely unconstrained.
isFreeState :: State -> Bool
isFreeState s = all isFreeExpr (state_vars s)
