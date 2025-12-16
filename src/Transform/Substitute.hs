module Transform.Substitute where

import Data.Set (Set(..))
import qualified Data.Set as Set
import qualified Data.HashSet as HashSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Control.Monad
import Control.Monad.State(StateT(..))
import qualified Control.Monad.State as State
import qualified Data.Key as K
import Control.Monad.Identity

import Smv.Syntax
import Smv.Packed
import Utils
import Transform.Pexpr

type Subst = Map Pident Pexpr

substFormula :: Monad m => [Subst] -> Bool -> Pformula -> m Pformula
substFormula sss recurse = substFormula' Map.empty sss
    where
    substFormula' :: Monad m => Subst -> [Subst] -> Pformula -> m Pformula
    substFormula' acc (ss:sss) (Pfexists n f) = liftM (Pfexists n) $ substFormula' (Map.union acc $ toHyperSubst n ss) sss f
    substFormula' acc (ss:sss) (Pfforall n f) = liftM (Pfforall n) $ substFormula' (Map.union acc $ toHyperSubst n ss) sss f
    substFormula' acc [] (Pfltl e) = liftM Pfltl $ substExpr acc acc recurse e

-- apply a different substitution to left and right expressions (always more substitutions on the right)
substExpr :: Monad m => Subst -> Subst -> Bool -> Pexpr -> m Pexpr
substExpr mleft mright recurse (Peident p t) = case Map.lookup p mright of
    Just e -> if recurse then substExpr mleft mright recurse e else return e
    Nothing -> return $ Peident p t
substExpr mleft mright recurse e@(Pebool _) = return e
substExpr mleft mright recurse e@(Peint _) = return e
substExpr mleft mright recurse (Peop1 o e) = do
    e' <- substExpr mleft mright recurse e
    return $ Peop1 o e'
substExpr mleft mright recurse (Peop2 o e1 e2) = do
    e1' <- substExpr mleft mright recurse e1
    e2' <- substExpr mleft mright recurse e2
    return $ Peop2 o e1' e2'
substExpr mleft mright recurse (Peopn Pand es) = do
    es' <- mapM (substExpr mleft mright recurse) es
    return $ pands es'
substExpr mleft mright recurse (Peopn Por es)  = do
    es' <- mapM (substExpr mleft mright recurse) es
    return $ pors es'
substExpr mleft mright recurse (Peopn Pset es)  = do
    es' <- mapM (substExpr mleft mright recurse) es
    return $ Peopn Pset es'
substExpr mleft mright recurse (Pecase cs) = do
    cs' <- mapM (tupleM (substExpr mleft mleft recurse) (substExpr mleft mright recurse)) cs
    return $ Pecase cs'
substExpr mleft mright recurse (Pedemorgan c e1 e2) = do
    c' <- substExpr mleft mleft recurse c
    e1' <- substExpr mleft mright recurse e1
    e2' <- substExpr mleft mright recurse e2
    return $ Pedemorgan c' e1' e2'

moduleSubst :: PackedPmodule -> Subst
moduleSubst smv = p_defines smv

toHyperSubst :: String -> Subst -> Subst
toHyperSubst h s = Map.foldrWithKey (\n e -> Map.insert (toHyperPident h n) (toHyperExpr h e)) Map.empty s

toHyperPident :: String -> Pident -> Pident
toHyperPident h (Pident n dims) = Pident n (dims++[Peident (Pident h []) EUnknown])

toHyperExpr :: String -> Pexpr -> Pexpr
toHyperExpr h (Peident n t) = Peident (toHyperPident h n) t
toHyperExpr h (Pebool b) = Pebool b
toHyperExpr h (Peint i) = Peint i
toHyperExpr h (Peop1 o e) = Peop1 o (toHyperExpr h e)
toHyperExpr h (Peop2 o e1 e2) = Peop2 o (toHyperExpr h e1) (toHyperExpr h e2)
toHyperExpr h (Peopn o es) = Peopn o (map (toHyperExpr h) es)
--toHyperExpr h (Peproj n es t) = Peproj (toHyperPident h n) (map (toHyperExpr h) es) t
toHyperExpr h (Pecase cs) = Pecase $ map (toHyperExpr h >< toHyperExpr h) cs
toHyperExpr h (Pedemorgan c e1 e2) = Pedemorgan (toHyperExpr h c) (toHyperExpr h e1) (toHyperExpr h e2)

joinHyperPvars :: [(String,PackedPvars)] -> PackedPvars
joinHyperPvars = Map.unions . map (uncurry toHyperPackedPvars)

toHyperPackedPvars :: String -> PackedPvars -> PackedPvars
toHyperPackedPvars h xs = Map.foldrWithKey (\n t -> Map.insert (toHyperPident h n) t) Map.empty xs

groupSubst :: Monad m => [String] -> Subst -> m [Subst]
groupSubst dims ss = do
    let acc = Map.fromList $ map (,Map.empty) dims
    acc' <- State.execStateT (K.forWithKeyM_ ss go) acc
    return $ map (flip (unsafeLookupNote "groupSubst") acc') dims
  where
    go :: Monad m => Pident -> Pexpr -> StateT (Map String Subst) m ()
    go n e = case isSingletonSet (dimsPident n) of
            Just dim -> addToState dim (removeDimPident n) (removeDimExpr e)
            Nothing -> error $ "groupSubst multiple dims " ++ show e
    addToState :: Monad m => String -> Pident -> Pexpr -> StateT (Map String Subst) m ()
    addToState dim n e = State.modify $ Map.insertWith Map.union dim (Map.singleton n e)

maybeComposeSubsts :: Maybe [Subst] -> [Subst] -> [Subst]
maybeComposeSubsts Nothing s2 = s2
maybeComposeSubsts (Just s1) s2 = composeSubsts s1 s2

composeSubsts :: [Subst] -> [Subst] -> [Subst]
composeSubsts s1 s2 = map (uncurry composeSubst) (zip s1 s2)

maybeComposeSubst :: Maybe Subst -> Subst -> Subst
maybeComposeSubst Nothing s2 = s2
maybeComposeSubst (Just s1) s2 = composeSubst s1 s2

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = runIdentity $ mapM (substExpr s2 s2 False) s1

composeIntSubsts :: [Subst] -> [IntMap Subst] -> [IntMap Subst]
composeIntSubsts s1 s2 = map (uncurry composeIntSubst) (zip s1 s2)

composeIntSubst :: Subst -> IntMap Subst -> IntMap Subst
composeIntSubst s1 ss2 = IntMap.map (composeSubst s1) ss2