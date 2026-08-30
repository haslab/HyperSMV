-- | The QBF encoder's model-level types.
module QBF.Model where

import qualified Data.HashSet as HashSet
import qualified Data.HashMap.Lazy as HashMap
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.Set (Set(..))
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Control.Monad.Reader as Reader
import Control.Monad
import Data.Hashable
import Data.Data
import GHC.Generics

import Utils
import Smv.Syntax
import Smv.Typing (VarType(..))
import Transform.Pexpr
import Smv.Packed
import Transform.Bexpr
import Transform.Bexpr.Packed
import qualified Data.DDs as DDs
import Transform.DD.Build
import Transform.DD.Packed
import QBF.Gates

-- | Unrolling semantics: pessimistic/optimistic, halting or not.
data Sem = Pes | Opt | Hpes | Hopt
    deriving (Eq,Ord,Show,Data,Generic,Enum,Bounded)

instance Hashable Sem

-- | Whether a semantics is optimistic.
isOptimisticSem :: Sem -> Bool
isOptimisticSem Hopt = True
isOptimisticSem Opt = True
isOptimisticSem _ = False

-- | Whether a semantics is halting.
isHaltingSem :: Sem -> Bool
isHaltingSem Hpes = True
isHaltingSem Hopt = True
isHaltingSem _ = False

-- | One trace's decision-diagram bundle.
data BDDmodel s1 s2 s3 s4 = BDDmodel { bdd_model_init :: s1, bdd_model_invar :: s2, bdd_model_trans :: s3, bdd_model_iden :: s3, bdd_model_ltl :: Maybe (DDltl s4 (LeafDD s4)),  bdd_model_st :: DDReader }
    deriving (Eq,Show,Generic)

instance (Hashable s1,Hashable s2,Hashable s3,Hashable s4,Hashable (LeafDD s4)) => Hashable (BDDmodel s1 s2 s3 s4)

-- | Transform a sequente of models to BDDs.
transformBsToBDD :: (QBFDDs4 dd s1 s2 s3 s4) => Proxy s1 -> Proxy s2 -> Proxy s3 -> Proxy s4 -> Integer -> PackedPvars -> [PackedBmodule] -> Bformula -> IO ([BDDmodel s1 s2 s3 s4],BDDformula s4)
transformBsToBDD s1 s2 s3 s4 acc vars bsmvs formula = do
    runDDM vars True $ withSupportAccept acc $ do
        let qs = quantsBformula formula
        ddmodels <- mapM (\(m,d) -> transformBmoduleToBDD d m) (zip bsmvs qs)
        ddformula <- transformBformulaToBDD formula
        return (ddmodels,ddformula)
        
-- | Build one trace's 'BDDmodel' from its SMV module.
transformBmoduleToBDD :: (QBFDDs4 dd s1 s2 s3 s4) => (String,Quant) -> PackedBmodule -> DDM IO (BDDmodel s1 s2 s3 s4)
transformBmoduleToBDD (dim,quant) p = withDDM isLocal $ toPackedDDmodule p >>= \dd -> do
    st <- Reader.ask
    let init' = dd_init dd
    let invar' = dd_invar dd
    let trans' = dd_trans dd
    iden' <- ioReader $ DDs.dd_identity
    let ltl' = dd_ltlspec dd
    let model = BDDmodel init' invar' trans' iden' ltl' st
    return model
  where
    pvars = Map.fromList $ map (\n -> (addDimPident n (mkQuantDim dim),n)) $ Map.keys $ b_vars p
    isLocal (n,isNext) = fmap (,isNext) (Map.lookup n pvars)

-- | Build the formula's decision-diagram bundle.
transformBformulaToBDD :: (QBFDDs s) => Bformula -> DDM IO (BDDformula s)
transformBformulaToBDD f = do
    let qs = quantsBformula f
    let e = exprBformula f
    ltl <- buildDDltl e
    ddvars <- Reader.asks varNames
    ddszs <- Reader.asks varSizes
    st <- Reader.ask
    return $ BDDformula qs ltl (IntMap.map fst ddvars) ddszs st

-- | The dimensioned variables the formula's atoms actually read.
formulaRefs :: (QBFDDs s) => DDReader -> DDltl s (LeafDD s) -> IntMap Pident -> IO (Set Pident)
formulaRefs rdr ltl vars = do
    sup <- Reader.runReaderT (go ltl) rdr
    return $ Set.fromList [ n | i <- IntSet.toList sup, Just n <- [IntMap.lookup i vars] ]
  where
    go (DDand es) = liftM IntSet.unions $ mapM go (HashSet.toList es)
    go (DDor es) = liftM IntSet.unions $ mapM go (HashSet.toList es)
    go (DDnot e) = go e
    go (DDop1 _ e) = go e
    go (DDop2 _ e1 e2) = liftM IntSet.union (go e1) <*> go e2
    go (DDexpr dds) = DDs.support dds

-- | The formula's atoms, each paired with the DD variable indices it reads.
formulaAtoms :: (QBFDDs s, Hashable s) => DDReader -> DDltl s (LeafDD s) -> IO [(s,IntSet)]
formulaAtoms rdr ltl = do
    as <- Reader.runReaderT (go ltl) rdr
    return (HashMap.toList (HashMap.fromList as))
  where
    go (DDand es) = liftM concat $ mapM go (HashSet.toList es)
    go (DDor es) = liftM concat $ mapM go (HashSet.toList es)
    go (DDnot e) = go e
    go (DDop1 _ e) = go e
    go (DDop2 _ e1 e2) = liftM (++) (go e1) <*> go e2
    go (DDexpr dds) = do { sup <- DDs.support dds; return [(dds,sup)] }

-- The formula has its own 'DDReader'.
data BDDformula s = BDDformula { bdd_formula_quantifiers :: [(String,Quant)], bdd_formula_ltl :: DDltl s (LeafDD s), bdd_formula_vars :: IntMap Pident, bdd_formula_sizes :: IntMap VarType, bdd_formula_st :: DDReader }
    deriving (Eq,Show,Generic)
    
instance (Hashable s,Hashable (LeafDD s)) => Hashable (BDDformula s)
