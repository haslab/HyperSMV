-- | The top-level QBF unrolling driver.
module QBF.Unroll where

import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.HashMap.Lazy as HashMap
import qualified Control.Monad.State.Strict as StrictState
import Control.Monad

import Utils
import Smv.Syntax
import Transform.Pexpr
import Transform.Substitute
import Transform.DD.Build
import Transform.DD.Packed
import QBF.Syntax
import QBF.Gates
import QBF.Model
import QBF.BitBlast

-- | Register a model's per-step prefix bits.
bddModelToQCIRVars :: (QBFDDs4 dd s1 s2 s3 s4,Monad m) => Int -> Bool -> ((String,Quant),BDDmodel s1 s2 s3 s4) -> QCIRM m [GateId]
bddModelToQCIRVars k isHalting ((dim,quant),model) = do
    let st = bdd_model_st model
    let vars = varNames st
    let szs = varSizes st
    let limit = if isHalting then k+1 else k
    -- One prefix entry per bit
    let bitsOf dd_i n = let w = varBits (unsafeIntLookupNote "bddModelToQCIRVars" dd_i szs)
                        in [ bitPident w j n | j <- [0 .. w-1] ]
    liftM concat $ forM [0..limit] $ \i ->
        liftM concat $ forM (IntMap.toList vars) $ \(dd_i,(n,isNext)) ->
            if isNext then return [] else do
                let ty = unsafeIntLookupNote "bddModelToQCIRVars/type" dd_i szs
                    w = varBits ty
                gids <- mapM (registerModelPident dim i) (bitsOf dd_i n)
                recordDecode dim i n ty gids
                return gids

-- unrolls model
bddModelToQCIR :: (QBFDDs4 dd s1 s2 s3 s4,Monad m) => Int -> Bool -> (((String,Quant),BDDmodel s1 s2 s3 s4),[GateId]) -> QCIRM m ((Quant,QCIRgate),QCIRgate)
bddModelToQCIR k isHalting (((q,quant),model),newgates) = do
    let st = bdd_model_st model
    let vars = varNames st
    addQuantifierQCIR quant newgates
    let szs = varSizes st
    let widthOf dd_i = varBits (unsafeIntLookupNote "bddModelToQCIR/size" dd_i szs)
    let render i dd_i = renderModelPident q (widthOf dd_i) i (unsafeIntLookupNote "bddModelToQCIR" dd_i vars)
    let init = bdd_model_init model
    let invar = bdd_model_invar model
    let trans = bdd_model_trans model
    let iden = bdd_model_iden model
    let ltl = bdd_model_ltl model
    
    inits <- bddsToQCIR 0 (render 0) init
    let maxk = if isHalting then k+1 else k
    invars <- forM [0..maxk] $ \i -> bddsToQCIR i (render i) invar
    transs <- forM [0..maxk-1] $ \i -> bddsToQCIR i (render i) trans
    ltls <- case ltl of
        Nothing -> return []
        Just ltl -> do
            let renderLTL i dd_i names =
                    let dd_n = unsafeIntLookupNote "transformBDDToQCIR" dd_i vars
                    in renderModelPident q (widthOf dd_i) i dd_n names
            r <- bddLtlToQCIR maxk Nothing renderLTL (Qbool True) ltl
            return [r]
    
    halted <- if isHalting
        then do
            let trans_k_k1 = last transs
            let invar_k1 = last invars
            step_k_k1 <- andQCIR trans_k_k1 invar_k1
            iden_k_k1 <- bddsToQCIR k (render k) iden
            equivQCIR step_k_k1 iden_k_k1
        else return (Qbool True)
    
    res <- liftM (quant,) $ andsQCIR (inits : invars ++ transs ++ ltls)
    return (res,halted)

-- when nothing assume mixed semantics (consider evidence only for bound k)
bddLtlToQCIR :: (QBFDDs s,Monad m) => Int -> Maybe Sem -> (Int -> Int -> QCIRnames -> [GateId]) -> QCIRgate -> DDltl s (LeafDD s) -> QCIRM m QCIRgate
bddLtlToQCIR k sem render halted ltl = unroll 0 ltl
    where
    unroll :: (QBFDDs s,Monad m) => Int -> DDltl s (LeafDD s) -> QCIRM m QCIRgate
    unroll i (DDand es) = andsQCIR =<< mapHashSetM (unroll i) es
    unroll i (DDor es) = orsQCIR =<< mapHashSetM (unroll i) es
    unroll i (DDexpr dds) = bddsToQCIR i (\dd_i names -> render i dd_i names) dds
    unroll i (DDop1 Pf e1) = unroll i $ DDop2 Pu (boolBDD True) e1
    
    unroll i ltl | i > k = if isTemporalDDltl ltl
        then case sem of -- only for temporal operators
            Nothing -> case ltl of
                DDop1 Pg _ -> boolQCIR True
                DDop1 Px _ -> boolQCIR False
                DDop2 Pu e1 e2 -> boolQCIR False
                DDop2 Pv e1 e2 -> boolQCIR True
                otherwise -> error $ "bddLtlToQCIR: " ++ show i ++" "++ show ltl ++ " " ++ show sem
            Just Pes -> boolQCIR False
            Just Opt -> boolQCIR True
            Just Hpes -> case ltl of
                DDop1 Pg e1 -> return halted
                DDop1 Px e1 -> andQCIR halted =<< unroll (i-1) e1
                DDop2 Pu e1 e2 -> boolQCIR False
                DDop2 Pv e1 e2 -> return halted
                otherwise -> error $ "bddLtlToQCIR: " ++ show i ++" "++ show ltl ++ " " ++ show sem
            Just Hopt -> case ltl of
                DDop1 Pg e1 -> boolQCIR True
                DDop1 Px e1 -> do
                    nothalted <- notQCIR halted
                    orQCIR nothalted =<< unroll (i-1) e1
                DDop2 Pu e1 e2 -> notQCIR halted
                DDop2 Pv e1 e2 -> boolQCIR True
                otherwise -> error $ "bddLtlToQCIR: " ++ show i ++" "++ show ltl ++ " " ++ show sem
        else error $ "bddLtlToQCIR: " ++ show i ++" "++ show ltl ++ " " ++ show sem
    unroll i e@(DDop1 Pg e1) = do
        qe1 <- unroll i e1
        andQCIR qe1 =<< unroll (i+1) e
    unroll i (DDop1 Px e1) = if (i+1) > k
        then case sem of
            Nothing -> boolQCIR False
            Just Pes -> boolQCIR False
            Just Opt -> boolQCIR True
            Just Hpes -> andQCIR halted =<< unroll i e1
            Just Hopt -> do
                nothalted <- notQCIR halted
                orQCIR nothalted =<< unroll i e1
        else unroll (i+1) e1
    unroll i e@(DDop2 Pu e1 e2) = do
        qe1 <- unroll i e1
        qe2 <- unroll i e2
        r <- andQCIR qe1 =<< unroll (i+1) e
        orQCIR qe2 r
    unroll i e@(DDop2 Pv e1 e2) = do
        qe1 <- unroll i e1
        qe2 <- unroll i e2
        r <- orQCIR qe1 =<< unroll (i+1) e
        andQCIR qe2 r
    -- 'DDnot' cannot occur: 'buildDDltl' keeps this IR in negation normal form by pushing negations in with 'bnot'.
    unroll _ (DDnot _) = error "bddLtlToQCIR: DDnot in a supposedly NNF DDltl (buildDDltl invariant broken)"
    unroll i (DDop1 Patom e1) = unroll i e1
    unroll _ (DDop1 o _) | o `elem` [Py,Pz,Ph] =
        error $ "bddLtlToQCIR: past-time operator " ++ show o ++ " is not supported by the QBF encoding"
    unroll i ltl = error $ "bddLtlToQCIR: unsupported " ++ show i ++ " " ++ show ltl

-- | Run gate-building to a finished QCIR circuit.
buildQCIR :: Monad m => QCIRM m QCIRgate -> m (QCIR,[IntMap Subst],Int)
buildQCIR m = do
    (out,QCIRstate qs _ gs cache names decode orConflicts _) <- StrictState.runStateT (m >>= newNonNegGate) (QCIRstate [] 1 [] HashMap.empty Map.empty Map.empty 0 HashMap.empty)
    let ss = buildSubsts qs decode
    -- ids were generated strictly increasing, so the reversed accumulator is already ascending
    return (QCIR qs out (IntMap.fromDistinctAscList (reverse gs)),ss,orConflicts)

-- | Per quantifier block, the substitution that turns a solver assignment back into model values.
buildSubsts :: [Quantifier] -> Map (Pident,Int) (Pexpr,[GateId]) -> [IntMap Subst]
buildSubsts qs decode = map build qs
  where
    build q =
        let gids = IntSet.fromList (quantifierGates q)
        in IntMap.fromListWith Map.union
             [ (i, Map.singleton (remDimPident n) e)
             | ((n,i),(e,gs)) <- Map.toList decode
             , Prelude.not (null gs)
             , all (`IntSet.member` gids) gs ]

-- | The gate ids bound by a quantifier block.
quantifierGates :: Quantifier -> [GateId]
quantifierGates (QForall gids) = gids
quantifierGates (QExists gids) = gids

-- | Encode models and formula into one QCIR circuit.
transformBDDToQCIR :: (QBFDDs4 dd s1 s2 s3 s4,Monad m) => Int -> Sem -> [BDDmodel s1 s2 s3 s4] -> BDDformula s4 -> m (QCIR,[IntMap Subst],Int)
transformBDDToQCIR k sem models formula = buildQCIR $ do
    let qs = bdd_formula_quantifiers formula
    let vars = bdd_formula_vars formula
    let qmodels = zip qs models
    let isHalt = isHaltingSem sem
    modelvars <- forM qmodels $ bddModelToQCIRVars k isHalt
    (qfsms,halteds) <- liftM unzip $ forM (zip qmodels modelvars) $ \(qm,newgates) ->
        bddModelToQCIR k isHalt (qm,newgates)
    halted <- andsQCIR halteds
    let fwidthOf dd_i = varBits (unsafeIntLookupNote "transformBDDToQCIR/size" dd_i (bdd_formula_sizes formula))
    let renderLTL i dd_i names =
            let dd_n = unsafeIntLookupNote "transformBDDToQCIR" dd_i vars
            in renderFormulaPident (fwidthOf dd_i) i dd_n names
    qformula <- bddLtlToQCIR k (Just sem) renderLTL halted (bdd_formula_ltl formula)
    createFinalProperty qfsms qformula

-- | Fold quantifier blocks and formula into the final property.
createFinalProperty :: Monad m => [(Quant,QCIRgate)] -> QCIRgate -> QCIRM m QCIRgate
createFinalProperty [] gf = return gf
createFinalProperty ((Qforall,gm):xs) gf = do
    notgm <- notQCIR gm
    orQCIR notgm =<< createFinalProperty xs gf
createFinalProperty ((Qexists,gm):xs) gf = andQCIR gm =<< createFinalProperty xs gf

