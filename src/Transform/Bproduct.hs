module Transform.Bproduct where

import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Control.Monad
import Data.Maybe

import Pretty
import Smv.Syntax hiding (p_name)
import Smv.Typing
import Smv.Packed
import Transform.Bexpr
import Transform.Smv
import Transform.Substitute
import Utils
import Transform.Bpacked
import Transform.Rename

transformBproduct :: Monad m => [(String,PackedBmodule)] -> m PackedBmodule
transformBproduct smvs = do
    (hsmvs,_) <- liftM unzip $ mapM (\(dim,smv) -> transformBrename (addDim dim $ b_vars smv) smv) smvs
    doProductB hsmvs
  where
    addDim :: String -> PackedBvars -> NameSubst
    addDim dim vs = Map.mapWithKey (\n t -> (addDimPident n $ mkQuantDim dim,toExprType t)) vs
    
    doProductB :: Monad m => [PackedBmodule] -> m PackedBmodule
    doProductB hsmvs = do
        let hname = concatMap b_name hsmvs
        let hvars = Map.unionsWith (error "unsupported") $ map b_vars hsmvs
        let hdefines = Map.unionsWith (error "unsupported") $ map b_defines hsmvs
        let hinit = bands $ HashSet.fromList $ map b_init hsmvs
        let hinvar = bands $ HashSet.fromList $ map b_invar hsmvs
        let htrans = bands $ HashSet.fromList $ map b_trans hsmvs
        let hltl = Just $ bands $ HashSet.fromList $ catMaybes $ map b_ltlspec hsmvs
        return $ PackedBmodule hname hvars hdefines hinit hinvar htrans hltl