module Transform.Rename where

import Control.Monad
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import Safe
import Control.Monad.State(StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Identity
import qualified Data.Key as K

import Utils
import Smv.Syntax
import Smv.Packed
import Smv.Typing
import Transform.Substitute
import Transform.Pexpr
import Transform.Bexpr
import Transform.Bpacked
import Pretty

type NameSubst = Map Pident (Pident,ExprType)

idNameSubst :: PackedPvars -> NameSubst
idNameSubst vs = Map.mapWithKey (\k t -> (k,toExprType t)) vs

fromNameSubst :: NameSubst -> Subst
fromNameSubst = Map.map (\(n,t) -> Peident n t)

joinHyperNameSubst :: [(String,NameSubst)] -> NameSubst
joinHyperNameSubst = Map.unions . map (uncurry toHyperNameSubst)

toHyperNameSubst :: String -> NameSubst -> NameSubst
toHyperNameSubst h xs = Map.foldrWithKey (\n1 (n2,t) -> Map.insert (toHyperPident h n1) (toHyperPident h n2,t)) Map.empty xs

renamePackedPvars :: NameSubst -> PackedPvars -> PackedPvars
renamePackedPvars ns m = mapWithKey (renamePident ns) id m

renamePident :: NameSubst -> Pident -> Pident
renamePident ss n = case Map.lookup n ss of
    Just (n',t') -> n'
    Nothing -> n

renameFormula :: NameSubst -> Pformula -> Pformula
renameFormula names (Pfforall n f) = Pfforall n $ renameFormula names f
renameFormula names (Pfexists n f) = Pfexists n $ renameFormula names f
renameFormula names (Pfltl e) = Pfltl $ renameExpr names e

renameExpr :: NameSubst -> Pexpr -> Pexpr
renameExpr names e = case e of
    (Peident n t) -> case Map.lookup n names of
        Just (e',t') -> Peident e' t'
        Nothing -> go e
    otherwise -> go e
  where
    go :: Pexpr -> Pexpr
    go e@(Pebool {}) = e
    go e@(Peint {}) = e
    go e@(Peident {}) = e
    go (Peop1 o e1) = Peop1 o (renameExpr names e1)
    go (Peop2 o e1 e2) = Peop2 o (renameExpr names e1) (renameExpr names e2)
    go (Peopn o es) = Peopn o (map (renameExpr names) es)
    go (Pecase cs) = Pecase $ map (renameExpr names >< renameExpr names) cs
    go (Pedemorgan c e1 e2) = Pedemorgan (renameExpr names c) (renameExpr names e1) (renameExpr names e2)

-- renames the quantifiers (HyperQube expects them in the specific order A,B,C,...)
sortFormula :: Pformula -> Pformula
sortFormula = go 'A' Map.empty
    where
    go c ss (Pfforall n f) = Pfforall [c] $ go (succ c) (Map.insert n [c] ss) f
    go c ss (Pfexists n f) = Pfexists [c] $ go (succ c) (Map.insert n [c] ss) f
    go c ss (Pfltl e) = Pfltl $ sortExpr e
        where
        sortExpr :: Pexpr -> Pexpr
        sortExpr (Peident n t) = Peident (sortPident n) t
        sortExpr e@(Pebool _) = e
        sortExpr e@(Peint _) = e
        sortExpr (Peop1 o e1) = Peop1 o $ sortExpr e1
        sortExpr (Peop2 o e1 e2) = Peop2 o (sortExpr e1) (sortExpr e2)
        sortExpr (Peopn o es) = Peopn o $ map sortExpr es
        sortExpr (Pecase cs) = Pecase $ map (sortExpr >< sortExpr) cs
        sortExpr (Pedemorgan c e1 e2) = Pedemorgan (sortExpr c) (sortExpr e1) (sortExpr e2)
        
        sortPident :: Pident -> Pident
        sortPident (Pident n dims) = Pident n (init dims ++ [sortDim $ last dims])
        
        sortDim :: Pexpr -> Pexpr
        sortDim d@(Peident (Pident n []) EUnknown) = case Map.lookup n ss of
            Just n' -> (Peident (Pident n' []) EUnknown)
            Nothing -> error $ "sortformula: " ++ show d
        sortDim d = error $ "sortformula: " ++ show d

renameBformula :: Monad m => NameSubst -> Bformula -> StateT BSubstState m Bformula
renameBformula names (Bforall n f) = liftM (Bforall n) $ renameBformula names f
renameBformula names (Bexists n f) = liftM (Bexists n) $ renameBformula names f
renameBformula names (Bltl e) = liftM Bltl $ renameBexpr names e

renameBexpr :: Monad m => NameSubst -> Bexpr -> StateT BSubstState m Bexpr
renameBexpr names e = do
    h <- State.get
    case HashMap.lookup e h of
        Just e' -> return e'
        Nothing -> go e
  where
    go e@(Bbool {}) = return e
    go e@(Bints {}) = return e
    go (Bvar (n,isNext) t) = return $ Bvar (renamePident names n,isNext) t
    go (Bop1 o e1) = do
        e1' <- renameBexpr names e1
        return $ Bop1 o e1'
    go (Bop2 o e1 e2) = do
        e1' <- renameBexpr names e1
        e2' <- renameBexpr names e2
        return $ Bop2 o e1' e2'
    go (Bopn o es) = do
        es' <- mapHashSetM (renameBexpr names) es
        return $ Bopn o es'
        
retypeBformula :: Monad m => Map Pident VarType -> Bformula -> StateT BSubstState m Bformula
retypeBformula tys (Bforall n f) = liftM (Bforall n) $ retypeBformula tys f
retypeBformula tys (Bexists n f) = liftM (Bexists n) $ retypeBformula tys f
retypeBformula tys (Bltl e) = liftM Bltl $ retypeBexpr tys e

retypeBexpr :: Monad m => Map Pident VarType -> Bexpr -> StateT BSubstState m Bexpr
retypeBexpr tys e = do
    h <- State.get
    case HashMap.lookup e h of
        Just e' -> return e'
        Nothing -> go e
  where
    go e@(Bbool {}) = return e
    go e@(Bints {}) = return e
    go (Bvar (n,isNext) t) = case Map.lookup n tys of
        Just ty -> return $ Bvar (n,isNext) ty
        Nothing -> error $ "retypeBexpr " ++ show tys ++ prettyprint e
    go (Bop1 o e1) = do
        e1' <- retypeBexpr tys e1
        return $ Bop1 o e1'
    go (Bop2 o e1 e2) = do
        e1' <- retypeBexpr tys e1
        e2' <- retypeBexpr tys e2
        return $ Bop2 o e1' e2'
    go (Bopn o es) = do
        es' <- mapHashSetM (retypeBexpr tys) es
        return $ Bopn o es'

type BSubstState = HashMap Bexpr Bexpr

newBSubstState :: BSubstState
newBSubstState = HashMap.empty

doBSubst :: Monad m => StateT BSubstState m a -> m a
doBSubst m = State.evalStateT m newBSubstState

transformBrename :: Monad m => NameSubst -> PackedBmodule -> m (PackedBmodule,NameSubst)
transformBrename names bimodule = do
    let name = b_name bimodule
    let vars = b_vars bimodule
    let vars' = renamePackedPvars names vars
    doBSubst $ do
        defs' <- mapM (renameBexpr names) $ b_defines bimodule
        init' <- renameBexpr names $ b_init bimodule
        invar' <- renameBexpr names $ b_invar bimodule
        trans' <- renameBexpr names $ b_trans bimodule
        ltl' <- mapM (renameBexpr names) $ b_ltlspec bimodule
        return (PackedBmodule name vars' defs' init' invar' trans' ltl',names)

groupVarSet :: [String] -> Set Pident -> [(String,Set Pident)]
groupVarSet dims ss = runIdentity $ do
    let acc :: Map String (Set Pident) = Map.fromList $ map (,Set.empty) dims
    acc' :: Map String (Set Pident) <- State.execStateT (forM_ ss go) acc
    return $ map (\dim -> (dim,unsafeLookupNote "groupVarSet" dim acc')) dims
  where
    go :: Monad m => Pident -> StateT (Map String (Set Pident)) m ()
    go n = case isSingletonSet (dimsPident n) of
            Just dim -> addToState dim (removeDimPident n)
            Nothing -> error $ "groupVarSet multiple dims " 
    addToState :: Monad m => String -> Pident -> StateT (Map String (Set Pident)) m ()
    addToState dim n = State.modify $ Map.insertWith Set.union dim (Set.singleton n)

groupBSubst :: Monad m => [String] -> BSubst -> m [BSubst]
groupBSubst dims ss = do
    let acc = Map.fromList $ map (,Map.empty) dims
    acc' <- State.execStateT (K.forWithKeyM_ ss go) acc
    return $ map (flip (unsafeLookupNote "groupBSubst") acc') dims
  where
    go :: Monad m => Pident -> Bexpr -> StateT (Map String BSubst) m ()
    go n e = case isSingletonSet (dimsPident n) of
            Just dim -> addToState dim (removeDimPident n) (removeDimBexpr e)
            Nothing -> error $ "groupBSubst multiple dims " ++ show e
    addToState :: Monad m => String -> Pident -> Bexpr -> StateT (Map String BSubst) m ()
    addToState dim n e = State.modify $ Map.insertWith Map.union dim (Map.singleton n e)

ungroupBSubst :: Monad m => [String] -> [BSubst] -> m BSubst
ungroupBSubst dims qss = doBSubst $ do
    let mkdim dim n = addDimPident n (mkQuantDim dim)
    let renames = Map.fromList $ concatMap (\(dim,ss) -> map (\(n,e) -> (n,(mkdim dim n,typeOfBexpr e))) $ Map.toList ss) $ zip dims qss
    let godim dim acc n e = do
            let n' = mkdim dim n
            e' <- renameBexpr renames e
            return $ Map.insert n' e' acc
    let go acc (dim,ss) = K.foldlWithKeyM (godim dim) acc ss
    foldM go Map.empty (zip dims qss)    