-- | Optimizing an hyperformula against its enumerated explicit-state systems.
module ExplicitState.FormulaOptimize where

import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Control.Monad
import Control.Monad.IO.Class
import qualified Control.Monad.Reader as Reader
import Data.Proxy
import qualified Data.Key as K
import qualified Data.Vector as V

import Utils
import Smv.Syntax
import Smv.Typing
import Transform.Pexpr
import Transform.Bexpr
import Transform.Bexpr.Packed
import Transform.Bexpr.Rename
import Transform.DD.Build
import Transform.DD.Packed
import Transform.Normalize
import Data.DDs (AndDDs(..))
import qualified Data.DDs as DDs
import ExplicitState.Syntax
import ExplicitState.Eval
import ExplicitState.APAbstract (transformSingles)
import Transform.Substitute
import ExplicitState.Translate (splitBformulaExplicit,toLocalPident)

-- | Optimize a hyperformula for driving explicit-state enumeration: split it across the quantified models, infer atom boundaries, and fold away trace-local constants.
optimizeBformulaForExplicitStateDD :: (BuildDD dd,MonadIO m) => Proxy dd -> Bool -> Bool -> Maybe String -> SplitFormulaMode -> Bool -> Bool -> Bool -> [DDExplicitStateSystem dd] -> Bformula -> m ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pformula)
optimizeBformulaForExplicitStateDD (dd :: Proxy dd) doRemoveTemps isDebug container doSplitFormula srcDeclaresAPs doBisim obsAtoms exps formula = do
    let qs = quantsBformula formula
    let vars = joinHyperPvars $ map (id >< exp_packedPvars) (zip (map fst qs) exps)
    (exps::[(DDExplicitStateSystem dd,BSubst)],formula) <- runDDM vars False $ do
        liftM (map snd >< id) (splitBformulaExplicit doSplitFormula doRemoveTemps isDebug container (zip (map fst qs) exps,formula)) >>= foldConstantSinglesFormula
    let vars = joinHyperPvars $ map (id >< exp_packedPvars) (zip (map fst qs) (map fst exps))
    runDDM vars False $ do
        let e = exprBformula formula
        ltl <- ioReader $ buildDDltlProxy dd e
        -- Honour the APs the formula declares, and re-derive only when it declares none. 
        e' <- liftM (canonAtomBodies . unnegateAtoms) $ if hasAtomDDltl ltl
            then liftM atomifyExpr (doBM (Map.map toVarType vars) (fromBexpr e))
            -- Derive them: atomise coarsely, then refine the WHOLE formula if its largest atom is
            -- too big (mixing coarse and fine atoms is worse than either strategy alone).
            else do
                coarse <- ddltlToExprWith (mkExprWith patomUnsafe) ltl
                return $ if maxAtomIdentsOf coarse <= maxAtomIdents
                    then coarse
                    else refineAtoms coarse
        let f' = applyQuantsExpr qs e'
        -- dedup once: 'atomExprs' returns every occurrence, and everything downstream is per-atom
        let atomsE' = Set.toList (Set.fromList (atomExprs e'))
        let vvs = map snd $ groupVarSet (map fst qs) $ varsFormula f'
        
        let isLocalTo dim pe = let vs' = Set.toList (varSet pe)
                               in Prelude.not (null vs')
                                  && all (\n -> isSingleDimsPident n == Just dim) vs'
            localAtoms dim = filter (isLocalTo dim) atomsE'
            
            maximalLocalSubs dim e
                | isLocalTo dim e = [e]                      -- maximal: do not descend further
                | otherwise = case e of
                    Peop1 _ a         -> maximalLocalSubs dim a
                    Peop2 _ a b       -> maximalLocalSubs dim a ++ maximalLocalSubs dim b
                    Peopn _ es        -> concatMap (maximalLocalSubs dim) es
                    Pecase cs         -> concatMap (\(a,b) -> maximalLocalSubs dim a
                                                              ++ maximalLocalSubs dim b) cs
                    Pedemorgan a b c  -> concatMap (maximalLocalSubs dim) [a,b,c]
                    _                 -> []
            mixedSubs dim = Set.toList $ Set.fromList $ concatMap (maximalLocalSubs dim)
                                                 (filter (Prelude.not . isLocalTo dim) atomsE')
            -- a boolean sub-expression is observed as an atom
            obsAtomExprs dim = Set.toList (Set.fromList (localAtoms dim ++ filter isBoolExpr (mixedSubs dim)))
            mixedLocalVars dim =
                Set.fromList [ remDimPident n
                             | sub <- mixedSubs dim, Prelude.not (isBoolExpr sub)
                             , n <- Set.toList (varSet sub), isSingleDimsPident n == Just dim ]
        exps' <- forM (zip3 (map fst qs) vvs exps) $ \(dim,vs,(e,aps)) ->
            if Prelude.not doBisim
              then return (e,IntMap.mapWithKey (\k _ -> k) (exp_states e),aps)
              else if Prelude.not obsAtoms
                then let (e2,renames) = projectExplicitStateSystem vs e in return (e2,renames,aps)
                else withDDM (toLocalPident dim) $ do
                    r <- Reader.ask
                    (atomDDs :: [AndDDs dd]) <- mapM
                        (\pe -> ioReader . buildDDs
                                  =<< doBM (Map.map toVarType (exp_packedPvars e))
                                           (toBexpr (mapVarSetExpr remDimPident pe)))
                        (obsAtomExprs dim)
                    let dd_map = mkDDMap (varNames r) (exp_vars e)
                        mixed = mixedLocalVars dim
                        mixedIdxs = [ i | (i,(n,_)) <- zip [0..] (V.toList (exp_vars e))
                                        , Set.member n mixed ]
                        key k _ = let vals = fst (exp_state e k)
                                  in ( map (\ad -> evalExplicitDDs' r dd_map ad vals) atomDDs
                                     , map (uvIndex "obsAtoms" vals) mixedIdxs )
                        (e2,renames) = projectExplicitStateSystemBy key vs e
                    return (e2,renames,aps)
        return (exps',f')
  where
    mkExprWith :: (BuildDD dd,Monad m) => (Pexpr -> Pexpr) -> AndDDs dd -> DDM m Pexpr
    mkExprWith atomify (AndDDs dds) =
        liftM (Peopn Pand) $ mapM (liftM atomify . ddToExpr) $ Map.elems dds

-- | Replace every maximal single-trace sub-formula that is constant over its trace's variable domains by @Bbool@, leaving every other sub-formula exactly as written.
foldConstantSinglesFormula :: forall dd m. (BuildDD dd,Monad m) => ([DDExplicitStateSystem dd],Bformula) -> DDM m ([(DDExplicitStateSystem dd,BSubst)],Bformula)
foldConstantSinglesFormula (exps,formula) = do
    let qs = quantsBformula formula
    let e = exprBformula formula
    (e,ss) <- transformSingles e
    qss <- groupBSubst (map fst qs) ss
    let fold1 (dim,ss'::BSubst) = withDDM (toLocalPident dim) $ do
            dss :: Map Pident (AndDDs dd) <- ioReader $ mapM buildDDs ss'
            -- Re-wrap the constant in any 'Patom' marker it replaced.
            let retag (Bop1 Patom x) b = Bop1 Patom (retag x b)
                retag _ b = Bbool b
            let go l n dds = case DDs.isLeaf (Proxy :: Proxy (DDM IO)) dds of
                    Nothing -> l
                    Just b -> Map.insert n (maybe (Bbool b) (\o -> retag o b) (Map.lookup n ss')) l
            return (K.foldlWithKey go Map.empty dss :: BSubst)
    qconsts <- mapM fold1 (zip (map fst qs) qss)
    consts <- ungroupBSubst (map fst qs) qconsts
    -- constants win; every other name goes back to the expression it stood for
    let subs = Map.union consts ss
    e <- substBexpr subs subs True e
    return (map (,Map.empty) exps,applyQuantsBexpr qs (evaluateBexpr e))

-- | Strip the trace-variable dimension from every identifier, turning a trace-qualified atom (@b[A]@) into the model-local form (@b@) that an explicit system's columns use.
mapVarSetExpr :: (Pident -> Pident) -> Pexpr -> Pexpr
mapVarSetExpr f = go
  where
    go (Peident n t)      = Peident (f n) t
    go (Peop1 o e)        = Peop1 o (go e)
    go (Peop2 o a b)      = Peop2 o (go a) (go b)
    go (Peopn o es)       = Peopn o (map go es)
    go (Pecase cs)        = Pecase (map (\(a,b) -> (go a, go b)) cs)
    go (Pedemorgan a b c) = Pedemorgan (go a) (go b) (go c)
    go e                  = e
