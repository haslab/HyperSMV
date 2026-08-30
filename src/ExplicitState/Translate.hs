-- | Translating an SMV module into an explicit-state system.
module ExplicitState.Translate where

import qualified Data.HashSet as HashSet
import qualified Data.Map as Map
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State
import Control.Monad
import qualified Data.Vector as V
import Data.List as List
import Data.Proxy
import Control.Monad.Trans

import Utils
import Smv.Typing
import Smv.Syntax
import Transform.Pexpr
import ExplicitState.Syntax
import ExplicitState.Eval
import ExplicitState.Product
import ExplicitState.Enumerate
import ExplicitState.Witness (findAnyTrace)
import Transform.Bexpr
import Transform.Bexpr.Packed
import qualified Data.DD as DD
import Data.DDs (AndDDs(..))
import qualified Data.DDs as DDs
import Transform.DD.Build
import Transform.DD.Packed
import HOA.LTL

-- | Build an explicit-state system for a module, using one diagram representation throughout.
transformToFixedExplicitState :: (BuildDD dd) => Proxy dd -> Integer -> Bool -> Bool -> Bool -> Maybe String -> PackedBmodule -> IO (DDExplicitStateSystem dd)
transformToFixedExplicitState dd supportAccept removeDeadlocks doRemoveTemps debug docker p = do
    let tree = DDs.proxyTreeDDs dd
    transformBSmvToExplicitStateSystem tree tree tree tree supportAccept removeDeadlocks doRemoveTemps debug docker p

-- | Build an explicit-state system for an SMV module.
transformBSmvToExplicitStateSystem :: (ExplicitInitDDs dd sinvar,ExplicitInitDDs dd sinit,BuildDDs dd sinvar,ExplicitTransDDs dd strans,BuildDDs dd sltl,MonadIO m) => Proxy sinit -> Proxy sinvar -> Proxy strans -> Proxy sltl -> Integer -> Bool -> Bool -> Bool -> Maybe String -> PackedBmodule -> m (DDExplicitStateSystem dd)
transformBSmvToExplicitStateSystem s1 s2 s3 s4 supportAccept removeDeadlocks doRemoveTemps isDebug container b = liftIO $ do
    -- lazy restriction.
    b' <- composeLTLSpecIntoModule s4 doRemoveTemps isDebug container b
    withPackedDDmodule supportAccept b' (transformDDSmvToExplicitState s1 s2 s3 s4 removeDeadlocks doRemoveTemps isDebug container)

-- | Does this single-trace subformula's automaton need no memory (one NBA state)?
isMemorylessBexpr :: forall dd sltl. (BuildDDs dd sltl)
                  => Proxy sltl -> Bool -> Bool -> Maybe String -> PackedBvars -> Bexpr -> IO Bool
isMemorylessBexpr (_::Proxy sltl) doRemoveTemps isDebug container vars e =
    runDDM vars True $ doHOAM $ do
        ltl :: DDltl sltl dd <- lift $ ioReader $ buildDDltl e
        hoa <- ltlToHOA doRemoveTemps isDebug container ltl
        (starts,trans) <- hoaToNBABexpr hoa
        return (IntSet.size (IntSet.union starts (IntMap.keysSet trans)) <= 1)

-- | Turn a module's LTLSPEC into model state, so the restriction happens during construction.
composeLTLSpecIntoModule :: (BuildDDs dd sltl) => Proxy sltl -> Bool -> Bool -> Maybe String -> PackedBmodule -> IO PackedBmodule
composeLTLSpecIntoModule (_::Proxy sltl) doRemoveTemps isDebug container b = case b_ltlspec b of
    Nothing -> return b
    Just e -> runDDM (b_vars b) True $ doHOAM $ do
        ltl :: DDltl sltl dd <- lift $ ioReader $ buildDDltl e
        hoa <- ltlToHOA doRemoveTemps isDebug container ltl
        (starts,trans) <- hoaToNBABexpr hoa
        return $ composeNBAIntoModule starts trans b

-- | Enumerate a packed module's states and restrict by its LTLSPEC.
transformDDSmvToExplicitState :: (ExplicitInitDDs dd sinvar,ExplicitInitDDs dd sinit,BuildDDs dd sinvar,ExplicitTransDDs dd strans,BuildDDs dd sltl,MonadIO m) => Proxy sinit -> Proxy sinvar -> Proxy strans -> Proxy sltl -> Bool -> Bool -> Bool -> Maybe String -> PackedDDmodule sinit sinvar strans sltl dd -> DDM m (DDExplicitStateSystem dd)
transformDDSmvToExplicitState s1 s2 s3 s4 removeDeadlocks doRemoveTemps isDebug container p = do
        ddnames <- Reader.asks varNames
        ddsizes <- Reader.asks (IntMap.map sizeOfVarType . varSizes)
        let ddsize = product ddsizes
        ns <- liftM (V.fromList . nub . map (fst >< id)) $ sortedTypes -- we only use non-next names, and follow the dd order
        sys <- ioReader $ do
            initStates <- initDDToStates (dd_init p) (dd_invar p)
            (states,trans) <- transDDToStates (dd_trans p) (dd_invar p) (vectorIndices $ V.map fst ns) initStates
            let inits' = IntSet.fromList $ Map.elems $ fst initStates
            let (sysInits,sysTrans) = mergeModel inits' (flipMapInt $ fst states) trans
            
            let sys = acceptingFromNBAMarker (ExplicitStateSystem ns sysInits Nothing sysTrans)
            return sys
        res <- case dd_ltlspec p of
            Nothing -> return sys
            Just ltl -> restrictLTLSpec doRemoveTemps isDebug container ltl sys
        return $ if removeDeadlocks then removeDeadlockExplicitStateSystem res else res

-- | Restrict a system by its module's own LTLSPEC.
restrictLTLSpec :: (BuildDDs dd sltl,MonadIO m) => Bool -> Bool -> Maybe String -> DDltl sltl dd -> DDExplicitStateSystem dd -> DDM m (DDExplicitStateSystem dd)
restrictLTLSpec doRemoveTemps isDebug container ltl sys =
    liftM (maybe sys id) $ restrictLTLSpecIf doRemoveTemps isDebug container maxBound maxBound ltl sys

-- | Number of states of a parsed NBA.
nbaStateCount :: ExplicitStateNBA base -> Int
nbaStateCount nba = IntSet.size (IntSet.union (exp_nba_inits nba) (IntMap.keysSet (exp_nba_transitions nba)))

-- | Restrict @sys@ by the LTL formula @ltl@, but only if the NBA passes @accept@.
restrictLTLSpecIf :: (BuildDDs dd sltl,MonadIO m) => Bool -> Bool -> Maybe String -> Int -> Int -> DDltl sltl dd -> DDExplicitStateSystem dd -> DDM m (Maybe (DDExplicitStateSystem dd))
restrictLTLSpecIf doRemoveTemps isDebug container maxNbaStates budget ltl sys = doHOAM $ do
    hoa <- ltlToHOA doRemoveTemps isDebug container ltl
    dd_names <- lift $ Reader.asks varNames
    let dd_map = mkDDMap dd_names (exp_vars sys)
    nba <- State.mapStateT (identityReader) $ hoaToNBA hoa dd_map
    return $ if nbaStateCount nba > maxNbaStates
        then Nothing
        else productExplicitStateSystemNBAExactBounded budget sys nba

-- | Push cheap single-trace subformulas into their models' explicit systems.
splitBformulaExplicit :: (BuildDD dd,MonadIO m) => SplitFormulaMode -> Bool -> Bool -> Maybe String -> ([(String,DDExplicitStateSystem dd)],Bformula) -> DDM m ([(String,DDExplicitStateSystem dd)],Bformula)
splitBformulaExplicit mode doRemoveTemps isDebug container (exps,f) = do
    (exps',f') <- splitBformulaM (restrictM mode) (exps,f)
    return (exps',normalizeBformula f')
  where
    buildRestrictionIf :: (BuildDD dd,MonadIO m) => Int -> String -> DDExplicitStateSystem dd -> Bexpr -> DDM m (Maybe (DDExplicitStateSystem dd))
    buildRestrictionIf budget dim sys e = withDDM (toLocalPident dim) $ do
        ltl :: DDltl (AndDDs dd) dd <- ioReader $ buildDDltl e
        restrictLTLSpecIf doRemoveTemps isDebug container 1 budget ltl sys

    -- Push a single-trace subformula into a model only when that cannot grow it, decided without building a product.
    restrictM :: (BuildDD dd,MonadIO m) => SplitFormulaMode -> Bexpr -> (String,DDExplicitStateSystem dd) -> DDM m (Maybe (String,DDExplicitStateSystem dd))
    restrictM NoSplitFormula _ _ = return Nothing
    restrictM mode e (dim,sys)
        | Invar <- mode = return Nothing
        | otherwise = merge
      where
        merge = fmap (fmap (dim,)) $ buildRestrictionIf maxBound dim sys e
    -- Cheap to push = the NBA state does not stay live across the whole system.
    isCheapSplit (Bop1 Pg e1) = not (isLTLBexpr e1)
    isCheapSplit e = not (isLTLBexpr e)

-- | Strip a trace dimension, keeping only names belonging to it.
toLocalPident :: String -> DualPident -> Maybe DualPident
toLocalPident dim (n,isNext) = case isSingleDimsPident n of
    Just dim_n -> if dim==dim_n then Just (remDimPident n,isNext) else Nothing
    Nothing -> Nothing

-- | Collapse an existentially-quantified empty system's formula to False.
checkEmptyExplicits :: MonadIO m => Bool -> ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pformula) -> m ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pformula)
checkEmptyExplicits isDebug (exps,f) = do
    (exps',qe') <- check (zip qs exps) qe
    return (exps',applyQuantsExpr qs qe')
  where
    qs = quantsPformula f
    qe = exprPformula f
    check :: MonadIO m => [((String,Quant),(DDExplicitStateSystem dd,IntMap Int,BSubst))] -> Pexpr -> m ([(DDExplicitStateSystem dd,IntMap Int,BSubst)],Pexpr)
    check [] qe = return ([],qe)
    check (((dim,Qforall),exp):xs) qe = liftM ((exp:) >< id) (check xs qe)
    check (((dim,Qexists),(exp,renames,aps)):xs) qe = case findAnyTrace exp of
        Nothing -> do
            liftIO $ when isDebug $ putStrLn $ "WARNING: explicit state system " ++ dim ++ " is empty"
            return ((emptyExplicitStateSystem,IntMap.empty,aps):map snd xs,Pebool False)
        Just _ -> liftM (((exp,renames,aps):) >< id) (check xs qe)

-- | Name of the automaton-state variable introduced by 'composeNBAIntoModule'.
nbaStateVar :: Pident
nbaStateVar = Pident "__nba" []

-- | Name of the boolean marker recording that the transition just taken was an accepting edge of the composed automaton.
nbaAccVar :: Pident
nbaAccVar = Pident "__nbaacc" []

-- | Compose an NBA (with Bexpr guards) into a module.
composeNBAIntoModule :: IntSet -> IntMap (IntMap (IsAccepting,Bexpr)) -> PackedBmodule -> PackedBmodule
composeNBAIntoModule starts trans p | uniformOut = p
    { b_vars = Map.insert nbaStateVar (Penum nbaStates) $ Map.insert nbaAccVar Pboolean $ b_vars p
    , b_init = bands $ HashSet.fromList [b_init p,initE]
    , b_invar = bands $ HashSet.fromList [b_invar p,Bop2 Pequiv accNow accSrc]
    , b_trans = bands $ HashSet.fromList [b_trans p,transE]
    , b_ltlspec = Nothing
    }
    where
    nbaStates = IntSet.union starts (IntMap.keysSet trans)
    nbaTy = VInt nbaStates
    nbaAt isNext j = Bop2 Pin (Bvar (nbaStateVar,isNext) nbaTy) (Bint j)
    accNow = Bvar (nbaAccVar,False) VBool
    -- every outgoing edge of an NBA state agrees on its flag, so one edge decides the state
    uniformOut = all agree (IntMap.elems trans)
        where agree es = case map fst (IntMap.elems es) of
                            []     -> True
                            (a:as) -> all (== a) as
    -- an NBA state with no outgoing edges is not accepting
    accSrc = bors $ HashSet.fromList
        [ nbaAt False j | (j,es) <- IntMap.toList trans
                        , not (IntMap.null es), fst (head (IntMap.elems es)) ]
    initE = bors $ HashSet.fromList $ map (nbaAt False) $ IntSet.toList starts
    transE = bors $ HashSet.fromList
        [ bands $ HashSet.fromList [nbaAt False j,g,nbaAt True j']
        | (j,es) <- IntMap.toList trans, (j',(_,g)) <- IntMap.toList es ]
composeNBAIntoModule starts trans p = p
    { b_vars = Map.insert nbaStateVar (Penum nbaStates) $ Map.insert nbaAccVar Pboolean $ b_vars p
    , b_init = bands $ HashSet.fromList [b_init p,initE,bnot accNow]
    , b_trans = bands $ HashSet.fromList [b_trans p,transE,accE]
    , b_ltlspec = Nothing
    }
    where
    nbaStates = IntSet.union starts (IntMap.keysSet trans)
    nbaTy = VInt nbaStates
    nbaAt isNext j = Bop2 Pin (Bvar (nbaStateVar,isNext) nbaTy) (Bint j)
    accNow = Bvar (nbaAccVar,False) VBool
    accNext = Bvar (nbaAccVar,True) VBool

    edges = [ (j,j',acc,g) | (j,es) <- IntMap.toList trans, (j',(acc,g)) <- IntMap.toList es ]
    step (j,j',_,g) = bands $ HashSet.fromList [nbaAt False j,g,nbaAt True j']

    initE = bors $ HashSet.fromList $ map (nbaAt False) $ IntSet.toList starts
    -- every step must follow some enabled edge
    transE = bors $ HashSet.fromList $ map step edges
    -- the marker is true exactly when the traversed edge was accepting
    accE = Bop2 Pequiv accNext (bors $ HashSet.fromList $ map step $ filter (\(_,_,acc,_) -> acc) edges)

-- | Recover the Buchi acceptance set left by 'composeNBAIntoModule'.
acceptingFromNBAMarker :: BuildDD dd => DDExplicitStateSystem dd -> DDExplicitStateSystem dd
acceptingFromNBAMarker sys = case V.findIndex ((== nbaAccVar) . fst) (exp_vars sys) of
    Nothing -> sys
    Just i -> sys { exp_accepting = Just accs }
        where
        accs = IntMap.keysSet $ IntMap.filter (\(vals,_) -> DD.valToBool (uvIndex "acceptingFromNBAMarker" vals i)) (exp_states sys)

