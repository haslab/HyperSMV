-- | Common-subexpression elimination.
module Transform.Bexpr.CSE where

import qualified Data.Set as Set
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
import Control.Monad.Identity
import qualified Data.Key as K

import Utils
import Smv.Syntax
import Smv.Packed
import Smv.Typing
import Transform.Pexpr
import Transform.Bexpr
import Transform.Substitute
import Transform.Bexpr.Packed
import Transform.Normalize

-- | Predicate for choosing CSE candidates.
type CriteriaCSE = Bexpr -> Bool

-- | Runs CSE over a 'Bformula'.
transformCSEFormula :: Monad m => Bformula -> m (Bformula,BSubst)
transformCSEFormula = go
    where
    go :: Monad m => Bformula -> m (Bformula,(BSubst))
    go (Bforall n f) = liftM (Bforall n >< id) $ go f
    go (Bexists n f) = liftM (Bexists n >< id) $ go f
    go (Bltl e) = do
        (e',ss) <- transformCSE e
        return (Bltl e',ss)

-- Common Subexpression Elimination
transformCSE :: Monad m => Bexpr -> m (Bexpr,BSubst)
transformCSE e = doSubstT True $ do
    e1 <- groupSimilarExprs "S" e
    occurs <- countOccurrences cseCriteria e1
    let frequents = HashMap.keys occurs
    e2 <- defineSubExprs frequents e1
    defineTopLevels e2

-- | Candidate predicate: which subexpressions are worth naming.
cseCriteria :: CriteriaCSE
cseCriteria e = (sizeBexpr e > 4 || bvarCount e > 1) && isBoolBexpr e && not (isLTLBexpr e) && isJust (isSingleDimBexpr e)

-- count occurrence of non-trivial subexpressions (we only consider non-LTL expressions and that only mention one model)
countOccurrences :: Monad m => CriteriaCSE -> Bexpr -> SubstT m (HashMap Bexpr Int)
countOccurrences criteria e = if criteria e then liftM (HashMap.insertWith (+) e 1) (go e) else go e
  where
    go (Bbool {}) = return HashMap.empty
    go (Bints {}) = return HashMap.empty
    go (Bvar {}) = return HashMap.empty
    go (Bop1 o e1) = countOccurrences criteria e1
    go (Bop2 o e1 e2) = liftA2 (HashMap.unionWith (+)) (countOccurrences criteria e1) (countOccurrences criteria e2)
    go (Bopn o es) = liftM (foldl (HashMap.unionWith (+)) HashMap.empty) (mapM (countOccurrences criteria) $ HashSet.toList es)

-- substitute a set of subexpressions in a larger expression
defineSubExprs :: Monad m => [Bexpr] -> Bexpr -> SubstT m Bexpr
defineSubExprs subs e = State.mapStateT (liftM fromJust . runMaybeT) $ do
    mapM (\sub -> mkSubst "K" Nothing sub) subs
    mapBexprWith (findSubst Nothing) e

-- | Runs a CSE substitution pass.
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

-- | Monad threading fresh names and substitutions.
type SubstT = StateT (Int,HashMap Bexpr Pident)

-- | Groups and substitutes similar subexpressions.
groupSimilarExprs :: Monad m => String -> Bexpr -> SubstT m Bexpr
groupSimilarExprs prefix = State.mapStateT (liftM fromJust . runMaybeT) . mapBexprWith (\e -> findSubst Nothing e `mplus` rule e)
    where
    rule e@(Bopn o es) = do
        es' <- mapHashSetM (groupSimilarExprs prefix) es
        groupOn bdimSet o es'
    rule bE = mzero
    
    groupOn :: (Ord b,MonadPlus m) => (Bexpr -> b) -> Popn -> HashSet Bexpr -> SubstT m Bexpr
    groupOn f o es = liftM (bopn o) $ foldM (\acc g -> mkGroup o g >>= \e -> return $ HashSet.insert e acc) HashSet.empty $ groupHashSetOn f es

    mkGroup :: MonadPlus m => Popn -> HashSet Bexpr -> SubstT m Bexpr
    mkGroup o es = let oes = bopn o es in if HashSet.size es > 1 && cseCriteria oes
        then mkSubst prefix Nothing oes
        else return oes

-- | Looks up an existing substitution for a 'Bexpr'.
findSubst :: MonadPlus m => Maybe Pident -> Bexpr -> SubstT m Bexpr
findSubst mbLabel e = do
    (i,ss) <- State.get
    case HashMap.lookup e ss of
        ((==mbLabel) -> True) -> mzero
        Just n -> do
            State.put (i,ss)
            return $ Bvar (n,False) VBool -- we only define substs for boolean exprs
        Nothing -> mzero

-- | Fresh identifier for a substituted subexpression.
mkident :: String -> Int -> Bexpr -> Pident
mkident prefix i e = case isSingleDimBexpr e of
    Just dim -> addDimPident n (mkQuantDim dim)
    Nothing -> n
  where
    n = Pident (prefix++show i) []

-- | Introduces (or reuses) a substitution for a 'Bexpr'.
mkSubst :: MonadPlus m => String -> Maybe Pident -> Bexpr -> SubstT m Bexpr
mkSubst prefix mbLabel e = findSubst mbLabel e `mplus` do
    (i,ss) <- State.get
    let (n,i') = case mbLabel of { Just n -> (n,i); Nothing -> (mkident prefix i e,i+1) }
    State.put (i',HashMap.insert e n ss)
    return $ Bvar (n,False) VBool -- we only define substs for boolean exprs

-- work-around to make sure that all top-level expressions in a formula appear as substitutions
-- this allows to unify and simplify optimization of expressions
defineTopLevels :: Monad m => Bexpr -> SubstT m Bexpr
defineTopLevels = State.mapStateT (liftM fromJust . runMaybeT) . mapBexprWith mkTop
    where
    mkTop e = if isLTLBexpr e
        then mzero
        else mkSubst "T" Nothing e

-- | Common-subexpression-eliminate an SMV/HyperQube formula and its variable declarations together, returning the CSE'd formula alongside the substitutions it introduced.
optimizeBformulaForSmv :: Monad m => PackedPvars -> Bformula -> m (Pformula,[Subst])
optimizeBformulaForSmv vars formula = do
    let qs = map fst $ quantsBformula formula
    (formula',substs) <- transformCSEFormula formula
    let dvars = Map.union vars (Map.map (const Pboolean) substs)
    do
        (outFormula,outSubst) <- doBM (Map.map toVarType dvars) $ do
            dsubsts <- mapM fromBexpr substs
            formula'' <- fromBformula formula'
            (outFormula,outSubst) <- buildSubst (formula'',dsubsts)
            return (outFormula,outSubst)

        retFormula <- mapFormula (return . normalizeExpr) outFormula
        retSubsts <- groupSubst qs outSubst
        return (retFormula,retSubsts)

-- | Keep only the frequently-referenced, single-dimension substitutions of a CSE pass; the rest get inlined at their use sites.
buildSubst :: (Monad m) => (Pformula,Subst) -> m (Pformula,Subst)
buildSubst (formula,is) = do
    let (keeps,drops) = Map.partitionWithKey
            (\n e -> Prelude.not (isSimpleExpr e) && isJust (isSingleDimPident n)) is
    keeps' <- mapM (substExpr drops drops True) keeps
    formula' <- mapFormula (substExpr drops drops True) formula
    return $ inlineNonFormulaSubst (formula',keeps')

-- | Drop any kept substitution whose name is not actually referenced by the formula, inlining it away instead.
inlineNonFormulaSubst :: (Pformula,Subst) -> (Pformula,Subst)
inlineNonFormulaSubst (f,ss) = (f',ss')
    where
    vs = varsFormula f
    (keeps,drops) = Map.partitionWithKey (\k e -> Set.member k vs) ss
    f' = runIdentity $ mapFormula (substExpr drops drops True) f
    ss' = runIdentity $ mapM (substExpr drops drops True) keeps
