module Transform.CSE where

import Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Trans.Maybe
import Data.Maybe
import Control.Monad
import Prettyprinter
import qualified Data.Key as K

import Utils
import Pretty
import Smv.Syntax
import Smv.Packed
import Smv.Typing
import Smv.Pretty
import Transform.Pexpr
import Transform.Bexpr
import Transform.Substitute
import Transform.Bpacked
import Transform.Rename

--import Debug.Trace

type CriteriaCSE = Bexpr -> Bool

data ModeCSE = AutoHyperCSE | HyperQubeCSE deriving (Eq,Ord,Show)

transformCSEFormula :: Monad m => ModeCSE -> Bformula -> m (Bformula,BSubst)
transformCSEFormula mode = go
    where
    go :: Monad m => Bformula -> m (Bformula,(BSubst))
    go (Bforall n f) = liftM (Bforall n >< id) $ go f
    go (Bexists n f) = liftM (Bexists n >< id) $ go f
    go (Bltl e) = do
        (e',ss) <- transformCSE mode e
        return (Bltl e',ss)

-- Common Subexpression Elimination
transformCSE :: Monad m => ModeCSE -> Bexpr -> m (Bexpr,BSubst)
transformCSE mode e = doSubstT True $ do
    e1 <- groupSimilarExprs "S" mode e
    occurs <- countOccurrences (cseCriteria mode) e1
    let frequents = case mode of
            AutoHyperCSE -> HashMap.keys $ HashMap.filterWithKey ahFrequent occurs
            HyperQubeCSE -> HashMap.keys occurs
    e2 <- defineSubExprs mode frequents e1
    defineTopLevels mode e2

transformSingles :: Monad m => Bexpr -> m (Bexpr,BSubst)
transformSingles = doSubstT False . State.mapStateT (liftM fromJust . runMaybeT) . mapBexprWith mkSingle
    where
    mkSingle :: Monad m => Bexpr -> SubstT (MaybeT m) Bexpr
    mkSingle e | hqCSECriteria e = mkSubst HyperQubeCSE "AP" Nothing e
    mkSingle e = mzero

ahFrequent :: Bexpr -> Int -> Bool
ahFrequent e n = n > 1 -- || (isJust (isSingleDimBexpr e) && ahCSECriteria e)

cseCriteria :: ModeCSE -> CriteriaCSE
cseCriteria AutoHyperCSE = ahCSECriteria
cseCriteria HyperQubeCSE = hqCSECriteria

ahCSECriteria :: CriteriaCSE
ahCSECriteria e = sizeBexpr e > 3 && isBoolBexpr e && not (isLTLBexpr e)

hqCSECriteria :: CriteriaCSE
hqCSECriteria e = (sizeBexpr e > 4 || bvarCount e > 1) && isBoolBexpr e && not (isLTLBexpr e) && isJust (isSingleDimBexpr e)

-- count occurrence of non-trivial subexpressions (we only consider non-LTL expressions and that only mention one model)
countOccurrences :: Monad m => CriteriaCSE -> Bexpr -> SubstT m (HashMap Bexpr Int)
countOccurrences criteria e = if criteria e then liftM (HashMap.insertWith (+) e 1) (go e) else go e
  where
--    go :: Monad m => Bexpr -> SubstT m (HashMap Bexpr Int)
    go (Bbool {}) = return HashMap.empty
    go (Bints {}) = return HashMap.empty
    go (Bvar {}) = return HashMap.empty
    go (Bop1 o e1) = countOccurrences criteria e1
    go (Bop2 o e1 e2) = liftA2 (HashMap.unionWith (+)) (countOccurrences criteria e1) (countOccurrences criteria e2)
    go (Bopn o es) = liftM (foldl (HashMap.unionWith (+)) HashMap.empty) (mapM (countOccurrences criteria) $ HashSet.toList es)

-- substitute a set of subexpressions in a larger expression
defineSubExprs :: Monad m => ModeCSE -> [Bexpr] -> Bexpr -> SubstT m Bexpr
defineSubExprs mode subs e = State.mapStateT (liftM fromJust . runMaybeT) $ do
    mapM (\sub -> mkSubst mode "K" Nothing sub) subs
    mapBexprWith (findSubst Nothing) e

doSubstT :: Monad m => Bool -> SubstT m a -> m (a,BSubst)
doSubstT doSharing m = do
    ((a,defs),(_,_)) <- flip State.runStateT (0,HashMap.empty) $ do
        a <- m
        (_,ss) <- State.get
        let defs = Map.fromList $ map swap $ HashMap.toList ss
        defs' <- if doSharing
            then K.mapWithKeyM (\n -> State.mapStateT (liftM fromJust . runMaybeT) . mapBexprWith (findSubst (Just n))) defs
            else return defs
        return (a,defs')
    return (a,defs)

type SubstT = StateT (Int,HashMap Bexpr Pident)

groupCriteria :: ModeCSE -> CriteriaCSE
groupCriteria mode@AutoHyperCSE e = cseCriteria mode e && not (hasRelBexpr e)
groupCriteria mode@HyperQubeCSE e = cseCriteria mode e

groupSimilarExprs :: Monad m => String -> ModeCSE -> Bexpr -> SubstT m Bexpr
groupSimilarExprs prefix mode = State.mapStateT (liftM fromJust . runMaybeT) . mapBexprWith (\e -> findSubst Nothing e `mplus` rule e)
    where
    rule e@(Bopn o es) = do
        es' <- mapHashSetM (groupSimilarExprs prefix mode) es
        case mode of
            AutoHyperCSE -> groupOn bvarSet o es'
            HyperQubeCSE -> groupOn bdimSet o es'
    rule bE = mzero
    
    groupOn :: (Ord b,MonadPlus m) => (Bexpr -> b) -> Popn -> HashSet Bexpr -> SubstT m Bexpr
    groupOn f o es = liftM (bopn o) $ foldM (\acc g -> mkGroup o g >>= \e -> return $ HashSet.insert e acc) HashSet.empty $ groupHashSetOn f es

    mkGroup :: MonadPlus m => Popn -> HashSet Bexpr -> SubstT m Bexpr
    mkGroup o es = let oes = bopn o es in if HashSet.size es > 1 && groupCriteria mode oes
        then mkSubst mode prefix Nothing oes
        else return oes

findSubst :: MonadPlus m => Maybe Pident -> Bexpr -> SubstT m Bexpr
findSubst mbLabel e = do
    (i,ss) <- State.get
    case HashMap.lookup e ss of
        ((==mbLabel) -> True) -> mzero
        Just n -> do
            State.put (i,ss)
            return $ Bvar (n,False) VBool -- we only define substs for boolean exprs
        Nothing -> mzero

mkident :: ModeCSE -> String -> Int -> Bexpr -> Pident
mkident mode prefix i e = case mode of
    HyperQubeCSE -> case isSingleDimBexpr e of
        Just dim -> addDimPident n (mkQuantDim dim)
        Nothing -> n
    AutoHyperCSE -> n
  where
    n = Pident (prefix++show i) []

mkSubst :: MonadPlus m => ModeCSE -> String -> Maybe Pident -> Bexpr -> SubstT m Bexpr
mkSubst mode prefix mbLabel e = findSubst mbLabel e `mplus` do
    (i,ss) <- State.get
    let (n,i') = case mbLabel of { Just n -> (n,i); Nothing -> (mkident mode prefix i e,i+1) }
    State.put (i',HashMap.insert e n ss)
    return $ Bvar (n,False) VBool -- we only define substs for boolean exprs

-- work-around to make sure that all top-level expressions in a formula appear as substitutions
-- this allows to unify and simplify optimization of expressions
defineTopLevels :: Monad m => ModeCSE -> Bexpr -> SubstT m Bexpr
defineTopLevels mode = State.mapStateT (liftM fromJust . runMaybeT) . mapBexprWith mkTop
    where
    mkTop e = if isLTLBexpr e
        then mzero
        else mkSubst mode "T" Nothing e

hasRelBexpr :: Bexpr -> Bool
hasRelBexpr (Bbool {}) = False
hasRelBexpr (Bints {}) = False
hasRelBexpr (Bvar {}) = False
hasRelBexpr (Bop1 o e1) = hasRelBexpr e1
hasRelBexpr (Bop2 o (Bvar {}) (Bvar {})) = True
hasRelBexpr (Bop2 o e1 e2) = hasRelBexpr e1 || hasRelBexpr e2
hasRelBexpr (Bopn o es) = any hasRelBexpr es
