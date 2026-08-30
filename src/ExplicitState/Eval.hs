-- | Evaluating and tightening explicit-state systems against decision diagrams.
module ExplicitState.Eval where

import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Control.Monad.Reader as Reader
import qualified Data.Key as K

import Utils
import Smv.Typing
import ExplicitState.Syntax
import Transform.DD.Build
import qualified Data.DD as DD
import Smv.Syntax
import Transform.Substitute

-- | An explicit-state system over decision-diagram values.
type DDExplicitStateSystem dd = ExplicitStateSystem Pident (DD.Val dd)    
-- | A per-state predicate over decision-diagram values.
type DDExplicitPred dd = Int -> Values (DD.Val dd) -> Bool

-- | Drop columns constant across all states, returning the shrunk system and their substitution.
tightDDExplicitStateSystem :: (BuildDD dd,Monad m) => DDExplicitStateSystem dd -> m (DDExplicitStateSystem dd,Subst)
tightDDExplicitStateSystem (s :: DDExplicitStateSystem dd) = do
    let vars = exp_vars s
    -- per-variable value bounds over all states.
    let upd v Nothing = Just $! IntSet.singleton (DD.valToInt v)
        upd v (Just is) = let is' = IntSet.insert (DD.valToInt v) is in is' `seq` Just is'
    let go acc (vs,_) = UV.ifoldl' (\m i v -> IntMap.alter (upd v) i m) acc vs
    let bounds = IntMap.foldl' go IntMap.empty (exp_states s)
    let (singles,compound) = IntMap.partition ((==1) . IntSet.size) bounds
    let (singlesubst :: IntMap (DD.Val dd)) = IntMap.map (DD.intToVal . popIntSet) singles
    let tonames im = vectorIndices vars `composeMapInt` im
    let retype VBool _ = VBool
        retype (VInt {}) js = VInt js
    let vars' = V.imapMaybe (\i (n,ty) -> fmap (\js -> (n,retype ty js)) $ IntMap.lookup i compound) vars    
    let states' = IntMap.map (UV.ifilter (\i _ -> IntMap.member i compound) >< id) (exp_states s)
    let s' = s { exp_vars = vars', exp_states = states' }
    let exprty VBool v = Pebool (DD.valToBool v)
        exprty (VInt {}) v = Peint (DD.valToInt v)
    let ss = K.foldlWithKey (\acc (n,ty) v -> Map.insert n (exprty ty v) acc) Map.empty (tonames singlesubst)
    return (s',ss)
    
-- | Build the decision diagram whose satisfying assignments are the system's states.
explicitStateSystemToDD :: (BuildDD dd,Monad m) => (Pident -> Pident) -> DDExplicitStateSystem dd -> DDM m dd
explicitStateSystemToDD mapP s = ioReader $ do
    r <- Reader.ask
    ff <- DD.false
    tt <- DD.true
    names <- Reader.asks varNames
    let exp_map = mkExpMap names (V.map (mapP >< id) $ exp_vars s)
    let valueToDD exp_i v =
            let dd_i = unsafeIntLookupNote "explicitStateSystemToDD" exp_i exp_map
            in runReaderIO r (DD.var dd_i v)
    let valuesToDD vs = UV.ifoldl (\acc i v -> runReaderIO r $ DD.and acc (valueToDD i v)) tt vs
    let go acc (vs,_) = runReaderIO r $ DD.or acc (valuesToDD vs)
    return $ IntMap.foldl go ff (exp_states s)
            

