-- | Splits a 'PackedDDmodule' into several modules by its initial states.
module Transform.DD.Split where

import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Merge.Lazy as IntMap
import qualified Control.Monad.Reader as Reader
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector as V
import qualified Data.Key as K
import Data.Typeable
import Data.Data
import Control.Monad

import Transform.DD.Build
import Transform.DD.Packed
import qualified Data.DD as DD
import qualified Data.DDs as DDs
import Smv.Typing
import Utils

-- | Strategy for splitting a module's initial states.
data SplitInitsMode
    = Frozen -- splits all valuations of frozen variables
    | Partial -- splits all possible initial states using partial assignments
    | Complete -- splits all possible initial states using complete assignments
    | NoSplitInits
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

-- | Splits a packed DD module's initial states per the given strategy.
splitPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => SplitInitsMode -> PackedDDmodule s1 s2 s3 s4 dd -> DDM m [PackedDDmodule s1 s2 s3 s4 dd]
splitPackedDDmodule Frozen p = ioReader $ do
    frozens <- DDs.frozenDDs (dd_trans p)
    inits <- invarPartialStates (dd_invar p) =<< DDs.allSat (dd_init p)
    groups <- groupFrozens frozens inits
    if Map.null groups
        then return [p]
        else forM (Map.elems groups) $ \init_dd -> do
            return $ p { dd_init = init_dd }
splitPackedDDmodule Partial p = ioReader $ do
    inits <- invarPartialStates (dd_invar p) =<< DDs.allSat (dd_init p)
    if Set.null inits
        then return [p]
        else forM (Set.toList inits) $ \init -> do
            init_dd <- partialStateToDDs init
            return $ p { dd_init = init_dd }
splitPackedDDmodule Complete p = ioReader $ do
    inits <- invarPartialStates (dd_invar p) =<< DDs.allSat (dd_init p)
    inits' <- expandPartialStates inits
    if Set.null inits'
        then return [p]
        else forM (Set.toList inits') $ \init' -> do
            init_dd <- partialStateToDDs init'
            return $ p { dd_init = init_dd }
splitPackedDDmodule NoSplitInits p = return [p]

-- | Groups partial states by their frozen-variable valuation.
groupFrozens :: (BuildDDs dd s,Monad m) => IntSet -> DD.PartialStates dd -> DDM m (Map (DD.PartialState dd) s)
groupFrozens fs st = foldM (go fs) Map.empty st
    where
    go :: (BuildDDs dd s,Monad m) => IntSet -> Map (DD.PartialState dd) s -> DD.PartialState dd -> DDM m (Map (DD.PartialState dd) s)
    go fs acc st = do
        r <- Reader.ask
        let ref = IntMap.filterWithKey (\k _ -> k `IntSet.member` fs) st
        dd <- partialStateToDDs st
        return $ Map.insertWith (\x y -> runReaderIO r (DDs.or x y)) ref dd acc

-- | Builds the DD conjunction of a partial state's assignments.
partialStateToDDs :: (Monad m,BuildDDs dd s) => DD.PartialState dd -> DDM m s
partialStateToDDs vs = ioReader $ do
    t <- DDs.singleton =<< DD.true
    K.foldlWithKeyM go t vs
  where
    go dd i v = (DDs.singleton =<< DD.var i v) >>= DDs.and dd

-- | Expands partial states into all consistent complete states.
expandPartialStates :: (Monad m,BuildDD dd) => DD.PartialStates dd -> DDM m (DD.CompleteStates dd)
expandPartialStates xs = do
    vars <- Reader.asks $ \s ->
        let isDual k = snd (unsafeIntLookupNote "expandPartialStates" k (varNames s))
        in IntMap.filterWithKey (\k v -> not (isDual k)) (varSizes s)
    return $ Set.foldl (\acc -> Set.union acc . expandPartialState vars) Set.empty xs
    
-- | Expands a partial state into all consistent complete states.
expandPartialState :: BuildDD dd => IntMap VarType -> DD.PartialState dd -> DD.CompleteStates dd
expandPartialState vars x = Set.fromList $ 
    IntMap.mergeA IntMap.preserveMissing expandMissing match x vars
  where
    expandMissing = IntMap.traverseMissing $ \n sz -> expand sz
    match = IntMap.zipWithAMatched $ \n v sz -> [v]
    expand (VInt sz) = map DD.intToVal $ IntSet.toList sz
    expand VBool = map DD.intToVal [0,1]

-- | Restricts partial states to those satisfying the invariant.
invarPartialStates :: (BuildDDs dd s,Monad m) => s -> DD.PartialStates dd -> DDM m (DD.PartialStates dd)
invarPartialStates invar sts = foldM restrictPartialStates sts =<< ddsToConjunction invar

-- | Restricts each partial state against a DD, unioning the results.
restrictPartialStates :: (BuildDD dd,Monad m) => DD.PartialStates dd -> dd -> DDM m (DD.PartialStates dd)
restrictPartialStates sts invar = liftM DD.orsPartialStates $ mapM (\st -> restrictPartialState st invar) (Set.toList sts)

-- | Restricts a partial state by walking a DD.
restrictPartialState :: (BuildDD dd,Monad m) => DD.PartialState dd -> dd -> DDM m (DD.PartialStates dd)
restrictPartialState st invar = ioReader $ do
    r <- Reader.ask
    DD.accum (goBranch r) goLeaf (Just st) invar
  where
    goLeaf st b = if b then maybeToSet st else DD.falsePartialStates
    goBranch r Nothing dd_i = V.empty
    goBranch r (Just st) dd_i = V.map restrict (UV.convert vals)
        where
        vals = runReaderIO r (DD.vals dd_i)
        (n,False) = Reader.runReader (varName dd_i) r
        restrict val = case IntMap.lookup dd_i st of
            Just val' -> if val==val' then Just st else Nothing
            Nothing -> Just $ IntMap.insertWith (error "restrictPartialState") dd_i val st



