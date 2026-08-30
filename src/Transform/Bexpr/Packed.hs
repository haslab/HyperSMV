-- | A 'Bexpr'-based packed SMV module representation.
module Transform.Bexpr.Packed where

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.HashMap.Lazy as HashMap
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Control.Monad
import Data.List as List
import Data.Hashable
import Control.Monad.Identity
import Data.Data

import Smv.Syntax hiding (p_name)
import Smv.Typing
import Smv.Packed
import Transform.Pexpr
import Transform.Bexpr
import Smv.Declarative
import Transform.Substitute
import Utils

-- | An SMV module with 'Bexpr' fields.
data PackedBmodule = PackedBmodule
    { b_name    :: String
    , b_vars    :: PackedBvars
    , b_defines :: BSubst
    , b_init    :: Bexpr
    , b_invar   :: Bexpr
    , b_trans   :: Bexpr
    , b_ltlspec :: Maybe Bexpr
    } deriving (Eq,Show)

-- | Drops variables unused elsewhere.
dropUnusedBmoduleVars :: Set Pident -> PackedBmodule -> PackedBmodule
dropUnusedBmoduleVars other_used p = p { b_vars = vars' }
    where
    ss = b_defines p
    used_vars = Set.unions $ map bvarSet (Map.elems $ b_defines p) ++ [bvarSet (b_init p),bvarSet (b_invar p),bvarSet (b_trans p),maybe Set.empty bvarSet (b_ltlspec p),other_used]
    vars' = Map.filterWithKey (\n t -> Set.member n used_vars) (b_vars p)
    
-- | Clears a module's LTLSPEC.
dropBLTLSpec :: PackedBmodule -> PackedBmodule
dropBLTLSpec p = p { b_ltlspec = Nothing }

-- | Conjoins a formula into a module's LTLSPEC.
addBLTLSpec :: Bexpr -> PackedBmodule -> PackedBmodule
addBLTLSpec (Bop1 Pg e1) p | not (isLTLBexpr e1) = p { b_invar = band (b_invar p) e1 }
addBLTLSpec e p = p { b_ltlspec = add (b_ltlspec p) e }
    where
    add Nothing y = Just y
    add (Just x) y = Just (band x y)
    
-- | Folds a G-formula into INVAR, if possible.
addBLTLSpecInvar :: Bexpr -> PackedBmodule -> Maybe PackedBmodule
addBLTLSpecInvar (Bop1 Pg e1) p | not (isLTLBexpr e1) = Just $ p { b_invar = band (b_invar p) e1 }
addBLTLSpecInvar e p = Nothing
    
-- | Variable declarations of a 'PackedBmodule'.
type PackedBvars = PackedPvars

-- | A substitution mapping names to 'Bexpr's.
type BSubst = Map Pident Bexpr

-- | Converts a 'Subst' to a 'BSubst'.
toBSubst :: Monad m => Subst -> BM m BSubst
toBSubst ss = mapM toBexpr ss

-- | Identity 'BSubst' over a variable set.
packedBSubst :: PackedBvars -> BSubst
packedBSubst = Map.mapWithKey (\n t -> Bvar (n,False) $ toVarType t)

-- | Converts and inlines a 'PackedPmodule'.
toInlinedPackedBmodule :: Monad m => PackedPmodule -> StateT BState m PackedBmodule
toInlinedPackedBmodule = toPackedBmodule >=> inlinePackedBmodule

-- | Inlines a module's definitions into its fields.
inlinePackedBmodule :: Monad m => PackedBmodule -> StateT BState m PackedBmodule
inlinePackedBmodule b = do
    let name = b_name b
    let vars = b_vars b
    runBM (Map.map toVarType vars) $ do
        let ss = b_defines b
        init' <- substBexpr ss ss True (b_init b)
        invar' <- substBexpr ss ss True (b_invar b)
        trans' <- substBexpr ss ss True (b_trans b)
        ltlspec' <- mapM (substBexpr ss ss True) (b_ltlspec b)
        --trace ("invar "++prettyprint invar')
        return $ PackedBmodule name vars Map.empty init' invar' trans' ltlspec'
    
-- | Converts a 'PackedPmodule' to a 'PackedBmodule'.
toPackedBmodule :: Monad m => PackedPmodule -> StateT BState m PackedBmodule
toPackedBmodule p0 = transformDeclarative p0 >>= \p -> do
    let name = p_name p
    let vars = p_vars p
    let ss = moduleSubst p
    let (boolss,intss) = Map.partition isBoolExpr ss -- because we don't know how to convert some int case exprs to Bexprs
    b <- runBM (Map.map toVarType vars `Map.union` Map.map (const VBool) ss) $ do
        defs' <- toBSubst =<< forM boolss (substExpr intss intss True)
        init' <- toBexpr =<< (substExpr intss intss True $ p_init p)
        invar' <- toBexpr =<< (substExpr intss intss True $ p_invar p)
        trans' <- toBexpr =<< (substExpr intss intss True $ p_trans p)
        ltlspec' <- mapM (\ltl -> toBexpr =<< (substExpr intss intss True ltl)) (p_ltlspec p)
        return $ PackedBmodule name vars defs' init' invar' trans' ltlspec'
    return b

-- | Adds definitions to a 'PackedBmodule'.
addBmoduleDefines :: BSubst -> PackedBmodule -> PackedBmodule
addBmoduleDefines ss b = b { b_defines = Map.union (b_defines b) ss }
    
-- | Converts a 'PackedBmodule' back to a 'PackedPmodule'.
fromPackedBmodule :: Monad m => PackedBmodule -> StateT BState m PackedPmodule
fromPackedBmodule b = do
    let name = b_name b
    let vars = b_vars b
    p <- runBM (Map.map toVarType vars) $ do
        defines' <- fromBSubst $ b_defines b
        init' <- fromBexpr $ b_init b
        invar' <- fromBexpr $ b_invar b
        trans' <- fromBexpr $ b_trans b
        ltlspec' <- mapM fromBexpr $ b_ltlspec b
        return $ PackedPmodule name vars defines' init' invar' trans' noPackedPassigns ltlspec' []
    return p

-- | Converts a 'BSubst' to a 'Subst'.
unsafeFromBSubst :: BSubst -> Subst
unsafeFromBSubst ss = runIdentity $ doBM Map.empty (fromBSubst ss)

-- attempts to substitute definitions inside definitions
fromBSubst :: Monad m => BSubst -> BM m PackedPdefs
fromBSubst biss = do
    foldlWithKeyM register () biss
    foldlWithKeyM add Map.empty biss
  where
    register :: Monad m => () -> Pident -> (Bexpr) -> BM m ()
    register _ n (e) = do
        State.modify $ id >< HashMap.insert e (Peident n $ typeOfBexpr e)
    add :: Monad m => PackedPdefs -> Pident -> Bexpr -> BM m PackedPdefs
    add acc n e = do
        State.modify $ id >< HashMap.delete e -- avoid using the definition on itself
        e' <- fromBexpr e
        State.modify $ id >< HashMap.insert e (Peident n $ typeOfBexpr e) -- restore the definition
        return $ Map.insert n e' acc

-- | Converts a 'Subst' to 'PackedPdefs'.
fromSubst :: Monad m => Subst -> BM m PackedPdefs
fromSubst ss = toBSubst ss >>= fromBSubst

-- | Folds INVAR into INIT\/TRANS.
transformNoInvarB :: Monad m => PackedBmodule -> m PackedBmodule
transformNoInvarB p = do
    let definedVars = Map.keysSet (b_vars p)
    let init' = bands $ HashSet.fromList [b_init p,b_invar p]
    let trans' = bands $ HashSet.fromList [b_trans p,bnext (b_invar p)] -- we could but don't apply the invar to the pre-state, to keep the formula more general
    return $ p { b_init = init', b_invar = Bbool True, b_trans = trans' }

-- | Prefixes a 'BSubst' for one trace.
toHyperBSubst :: String -> BSubst -> BSubst
toHyperBSubst h s = Map.foldrWithKey (\n e -> Map.insert (toHyperPident h n) (toHyperBexpr h e)) Map.empty s

-- | Prefixes a 'Bexpr''s variables for one trace.
toHyperBexpr :: String -> Bexpr -> Bexpr
toHyperBexpr h e@(Bbool {}) = e
toHyperBexpr h e@(Bints {}) = e
toHyperBexpr h (Bvar (n,isNext) t) = Bvar (toHyperPident h n,isNext) t
toHyperBexpr h (Bop1 o e1) = Bop1 o (toHyperBexpr h e1)
toHyperBexpr h (Bop2 o e1 e2) = Bop2 o (toHyperBexpr h e1) (toHyperBexpr h e2)
toHyperBexpr h (Bopn o es) = Bopn o (HashSet.map (toHyperBexpr h) es)

-- | Substitutes per-trace 'BSubst's into a 'Bformula'.
substBformula :: Monad m => [BSubst] -> Bool -> Bformula -> m Bformula
substBformula sss recurse = substBformula' Map.empty sss
    where
    substBformula' :: Monad m => BSubst -> [BSubst] -> Bformula -> m Bformula
    substBformula' acc (ss:sss) (Bexists n f) = liftM (Bexists n) $ substBformula' (Map.union acc $ toHyperBSubst n ss) sss f
    substBformula' acc (ss:sss) (Bforall n f) = liftM (Bforall n) $ substBformula' (Map.union acc $ toHyperBSubst n ss) sss f
    substBformula' acc [] (Bltl e) = liftM Bltl $ substBexpr acc acc recurse e

-- apply a different substitution to left and right expressions (always more substitutions on the right)
substBexpr :: Monad m => BSubst -> BSubst -> Bool -> Bexpr -> m Bexpr
substBexpr mleft mright recurse (Bvar (n,isNext) t) = case Map.lookup n mright of
    Just e -> do
        let mkNext = if isNext then bnext else id
        liftM mkNext $ if recurse then substBexpr mleft mright recurse e else return e
    Nothing -> return $ Bvar (n,isNext) t
substBexpr mleft mright recurse e@(Bbool {}) = return e
substBexpr mleft mright recurse e@(Bints {}) = return e
substBexpr mleft mright recurse (Bop1 o e) = do
    e' <- substBexpr mleft mright recurse e
    return $ Bop1 o e'
substBexpr mleft mright recurse (Bop2 o e1 e2) = do
    e1' <- substBexpr mleft mright recurse e1
    e2' <- substBexpr mleft mright recurse e2
    return $ Bop2 o e1' e2'
substBexpr mleft mright recurse (Bopn o es) = do
    es' <- mapHashSetM (substBexpr mleft mright recurse) es
    return $ bopn o es'

-- | Conjoins init\/invar into a module.
addBmoduleInvariants :: (Bexpr,Bexpr) -> PackedBmodule -> PackedBmodule
addBmoduleInvariants (init,invar) p = p { b_init = b_init p `band` init, b_invar = b_invar p `band` invar }

-- | Push single-trace subformulas into the models' LTLSPEC, declining pure liveness under 'LTL'.
splitBformulaDigestBmoduleM :: Monad m => (PackedBvars -> Bexpr -> m Bool) -> SplitFormulaMode
                            -> ([(digest,PackedBmodule)],Bformula)
                            -> m ([((digest,Int),PackedBmodule)],Bformula)
splitBformulaDigestBmoduleM memoryless mode = splitBformulaDigestM restrict (hash . b_ltlspec)
    where
    restrict e p = case mode of
        LTL -> do
            -- the free invariant shape never reaches an automaton
            ok <- if isFreeInvarShape e then return True else memoryless (b_vars p) e
            return $ if ok then Just (addBLTLSpec e p) else Nothing
        Invar -> return (addBLTLSpecInvar e p)
        NoSplitFormula -> return Nothing

-- | @G e@ with @e@ non-temporal: 'addBLTLSpec' folds it into `b_invar`, so it costs nothing.
isFreeInvarShape :: Bexpr -> Bool
isFreeInvarShape (Bop1 Pg e1) = not (isLTLBexpr e1)
isFreeInvarShape _ = False

-- | Digest-rehashing wrapper over 'splitBformulaM'.
splitBformulaDigestM :: Monad m => (Bexpr -> model -> m (Maybe model)) -> (model -> Int)
                     -> ([(digest,model)],Bformula) -> m ([((digest,Int),model)],Bformula)
splitBformulaDigestM restrict rehash (smvs,f) = do
    let (digests,bsmvs) = unzip smvs
    (bsmvs',f') <- splitBformulaM restrict (bsmvs,f)
    return (map (\(d,b) -> ((d,rehash b),b)) (zip digests bsmvs'),f')

-- | Pure digest-rehashing wrapper over 'splitBformula'.
splitBformulaDigest :: (Bexpr -> model -> Maybe model) -> (model -> Int) -> ([(digest,model)],Bformula) -> ([((digest,Int),model)],Bformula)
splitBformulaDigest restrict rehash (smvs,f) = (map addLTLHash $ zip digests bsmvs',f')
    where
    (digests,bsmvs) = unzip smvs
    (bsmvs',f') = splitBformula restrict (bsmvs,f)
    addLTLHash (d,b) = ((d,rehash b),b)

-- | How to push single-trace subformulas out.
data SplitFormulaMode
    = Invar 
    | LTL 
    | NoSplitFormula
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

-- note: need to check that exists are non-empty for prenex NF
splitBformula :: (Bexpr -> model -> Maybe model) -> ([model],Bformula) -> ([model],Bformula)
splitBformula restrict x = runIdentity $ splitBformulaM (\e m -> Identity (restrict e m)) x

-- | Push single-trace subformulas into the corresponding model, in a monad.
splitBformulaM :: Monad m => (Bexpr -> model -> m (Maybe model)) -> ([model],Bformula) -> m ([model],Bformula)
splitBformulaM restrict (smvs,f) = do
    (e',st') <- State.runStateT (splitBexpr e) st0
    let (qs',smvs') = unzip $ map assocl st'
    return (smvs',applyQuantsBexpr qs' e')
    where
    qs = quantsBformula f
    e = exprBformula f
    st0 = map assocr $ zip qs smvs
    
    -- Re-split to a fixpoint: pushing a subformula in rewrites the residual and can expose further
    -- splits. 
    splitBexpr e@(Bopn Por es) = do
        (acc,didSplit) <- foldM splitForall (HashSet.empty,False) es
        let e' = bfor acc
        if didSplit then splitBexpr e' else return e'
    splitBexpr e@(Bopn Pand es) = do
        (acc,didSplit) <- foldM splitExists (HashSet.empty,False) es
        let e' = bgand acc
        if didSplit then splitBexpr e' else return e'
    splitBexpr e = return e
    
    bfor :: HashSet Bexpr -> Bexpr
    bfor es = bors (HashSet.insert (bf $ bors r) l)
        where
        (l,r) = foldl go (HashSet.empty,HashSet.empty) es
        go (l,r) (Bop1 Pf e) = (l,HashSet.insert e r)
        go (l,r) e = (HashSet.insert e l,r)
        
    bgand :: HashSet Bexpr -> Bexpr
    bgand es = bands (HashSet.insert (bg $ bands r) l)
        where
        (l,r) = foldl go (HashSet.empty,HashSet.empty) es
        go (l,r) (Bop1 Pg e) = (l,HashSet.insert e r)
        go (l,r) e = (HashSet.insert e l,r)
    
    splitForall (acc,ch) e@(isSingleDimBexpr -> Just dim) = do
        st <- State.get
        case List.lookup dim st of
            Just (Qforall,smv) -> do
                r <- State.lift $ restrict (bnot $ removeDimBexpr e) smv
                case r of
                    Just smv' -> do
                        State.put $ updateAssoc (\v _ -> v) dim (Qforall,smv') st
                        return (acc,True)
                    Nothing -> return (HashSet.insert e acc,ch)
            otherwise -> return (HashSet.insert e acc,ch)
    splitForall acc (Bop1 Pf (Bopn Por es)) = foldM splitForall acc (HashSet.map (Bop1 Pf) es)
    splitForall (acc,ch) e = return (HashSet.insert e acc,ch)
    
    splitExists (acc,ch) e@(isSingleDimBexpr -> Just dim) = do
        st <- State.get
        case List.lookup dim st of
            Just (Qexists,smv) -> do
                r <- State.lift $ restrict (removeDimBexpr e) smv
                case r of
                    Just smv' -> do
                        State.put $ updateAssoc (\v _ -> v) dim (Qexists,smv') st
                        return (acc,True)
                    Nothing -> return (HashSet.insert e acc,ch)
            otherwise -> return (HashSet.insert e acc,ch)
    splitExists acc (Bop1 Pg (Bopn Pand es)) = foldM splitExists acc (HashSet.map (Bop1 Pg) es)
    splitExists (acc,ch) e = return (HashSet.insert e acc,ch)
    



