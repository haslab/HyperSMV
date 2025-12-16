module Transform.Split where

import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Merge.Lazy as IntMap
import qualified Control.Monad.Reader as Reader
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector as V
import Data.Vector (Vector(..))
import qualified Data.Key as K
import Data.Typeable
import Data.Data
import Control.Monad
import Data.Maybe
import Control.Monad.Identity

import Transform.Pexpr
import Transform.DDs
import Transform.DDpacked
import Data.DD (DD)
import qualified Data.DD as DD
import Data.DDs (AndDDs(..),NextDDs(..))
import qualified Data.DDs as DDs
import Smv.Syntax
import Smv.Typing
import Utils

--import Debug.Trace as Trace

data SplitInitsMode
    = Frozen -- splits all valuations of frozen variables
    | Partial -- splits all possible initial states using partial assignments
    | Complete -- splits all possible initial states using complete assignments
    | NoSplitInits
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

splitPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => SplitInitsMode -> PackedDDmodule s1 s2 s3 s4 dd -> DDM m [PackedDDmodule s1 s2 s3 s4 dd]
splitPackedDDmodule Frozen p = identityReader $ do
    frozens <- DDs.frozenDDs (dd_trans p)
    inits <- invarPartialStates (dd_invar p) =<< DDs.allSat (dd_init p)
    groups <- groupFrozens frozens inits
    if Map.null groups
        then return [p]
        else forM (Map.elems groups) $ \init_dd -> do
            return $ p { dd_init = init_dd }
splitPackedDDmodule Partial p = {-trace ("ddinit " ++ show (dd_init p)) $-} identityReader $ do
    inits <- invarPartialStates (dd_invar p) =<< DDs.allSat (dd_init p)
    if Set.null inits
        then return [p]
        else forM (Set.toList inits) $ \init -> do
            init_dd <- {-trace ("partial state " ++ show init) $-} partialStateToDDs init
            return $ p { dd_init = init_dd }
splitPackedDDmodule Complete p = identityReader $ do
    inits <- invarPartialStates (dd_invar p) =<< DDs.allSat (dd_init p)
    inits' <- expandPartialStates inits
    if Set.null inits'
        then return [p]
        else forM (Set.toList inits') $ \init' -> do
            init_dd <- partialStateToDDs init'
            return $ p { dd_init = init_dd }
splitPackedDDmodule NoSplitInits p = return [p]

groupFrozens :: (BuildDDs dd s,Monad m) => IntSet -> DD.PartialStates dd -> DDM m (Map (DD.PartialState dd) s)
groupFrozens fs st = foldM (go fs) Map.empty st
    where
    go :: (BuildDDs dd s,Monad m) => IntSet -> Map (DD.PartialState dd) s -> DD.PartialState dd -> DDM m (Map (DD.PartialState dd) s)
    go fs acc st = do
        r <- Reader.ask
        let ref = IntMap.filterWithKey (\k _ -> k `IntSet.member` fs) st
        dd <- partialStateToDDs st
        return $ Map.insertWith (\x y -> Reader.runReader (DDs.or x y) r) ref dd acc

partialStateToDDs :: (Monad m,BuildDDs dd s) => DD.PartialState dd -> DDM m s
partialStateToDDs vs = identityReader $ do
    t <- DDs.singleton =<< DD.true
    K.foldlWithKeyM go t vs
  where
    go dd i v = (DDs.singleton =<< DD.var i v) >>= DDs.and dd

expandPartialStates :: (Monad m,BuildDD dd) => DD.PartialStates dd -> DDM m (DD.CompleteStates dd)
expandPartialStates xs = do
    vars <- Reader.asks $ \s ->
        let isDual k = snd (unsafeIntLookupNote "expandPartialStates" k (varNames s))
        in IntMap.filterWithKey (\k v -> not (isDual k)) (varSizes s)
    return $ Set.foldl (\acc -> Set.union acc . expandPartialState vars) Set.empty xs
    
expandPartialState :: BuildDD dd => IntMap VarType -> DD.PartialState dd -> DD.CompleteStates dd
expandPartialState vars x = Set.fromList $ 
    IntMap.mergeA IntMap.preserveMissing expandMissing match x vars
  where
    expandMissing = IntMap.traverseMissing $ \n sz -> expand sz
    match = IntMap.zipWithAMatched $ \n v sz -> [v]
    expand (VInt sz) = map DD.intToVal $ IntSet.toList sz
    expand VBool = map DD.intToVal [0,1]

invarPartialStates :: (BuildDDs dd s,Monad m) => s -> DD.PartialStates dd -> DDM m (DD.PartialStates dd)
invarPartialStates invar sts = foldM restrictPartialStates sts =<< ddsToConjunction invar

restrictPartialStates :: (BuildDD dd,Monad m) => DD.PartialStates dd -> dd -> DDM m (DD.PartialStates dd)
restrictPartialStates sts invar = liftM DD.orsPartialStates $ mapM (\st -> restrictPartialState st invar) (Set.toList sts)

restrictPartialState :: (BuildDD dd,Monad m) => DD.PartialState dd -> dd -> DDM m (DD.PartialStates dd)
restrictPartialState st invar = identityReader $ do
    r <- Reader.ask
    DD.accum (goBranch r) goLeaf (Just st) invar
  where
--    goLeaf :: Maybe (PartialState dd) -> Bool -> PartialStates dd
    goLeaf st b = if b then maybeToSet st else DD.falsePartialStates
--    goBranch :: DDReader -> Maybe (PartialState dd) -> Int -> Vector (Maybe (PartialState dd))
    goBranch r Nothing dd_i = V.empty
    goBranch r (Just st) dd_i = V.map restrict (UV.convert vals)
        where
        vals = Reader.runReader (DD.vals dd_i) r
        (n,False) = Reader.runReader (varName dd_i) r
        restrict val = case IntMap.lookup dd_i st of
            Just val' -> if val==val' then Just st else Nothing
            Nothing -> Just $ IntMap.insertWith (error "restrictPartialState") dd_i val st



