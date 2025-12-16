module Transform.SmvToQBF where

import GHC.Generics
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Merge.Lazy as IntMap
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import qualified Control.Monad.State.Strict as StrictState
import qualified Control.Monad.Reader as Reader
import Control.Monad.Trans
import Control.Monad
import Data.Hashable
import Crypto.Hash (Digest, SHA256, hash)
import Data.Data
import Control.Monad.Identity
import qualified Data.Vector as V
import qualified Data.Key as K

import Data.BDD (BDD)
import qualified Data.BDD as BDD
import Data.DDs (AndDDs(..),NextDDs(..),TreeDDs(..))
import qualified Data.DDs as DDs
import Smv.Syntax
import Smv.Pretty
import Smv.Packed
import Smv.Trace
import Transform.Pexpr
import Transform.Bexpr
import Transform.Bpacked
import Transform.DDpacked
import Transform.DDs
import QCIR.Syntax
import QCIR.Solver
import Utils
import Error
import Pretty
import Transform.Substitute
import Transform.Normalize
import Transform.Rename

--import Debug.Trace as Trace

data Sem = Pes | Opt | Hpes | Hopt
    deriving (Eq,Ord,Show,Data,Generic,Enum,Bounded)

instance Hashable Sem

isOptimisticSem :: Sem -> Bool
isOptimisticSem Hopt = True
isOptimisticSem Opt = True
isOptimisticSem _ = False

isHaltingSem :: Sem -> Bool
isHaltingSem Hpes = True
isHaltingSem Hopt = True
isHaltingSem _ = False

data BDDmodel s1 s2 s3 s4 = BDDmodel { bdd_model_init :: s1, bdd_model_invar :: s2, bdd_model_trans :: s3, bdd_model_iden :: s3, bdd_model_ltl :: Maybe (DDltl s4 BDD),  bdd_model_st :: DDReader }
    deriving (Eq,Show,Generic)

instance (Hashable s1,Hashable s2,Hashable s3,Hashable s4) => Hashable (BDDmodel s1 s2 s3 s4)

transformBsToBDD :: (QBFDDs s1,QBFDDs s2,QBFDDs s3,QBFDDs s4,Monad m) => Proxy s1 -> Proxy s2 -> Proxy s3 -> Proxy s4 -> Integer -> PackedPvars -> [PackedBmodule] -> Bformula -> m ([BDDmodel s1 s2 s3 s4],BDDformula s4)
transformBsToBDD s1 s2 s3 s4 maxSize vars bsmvs formula = do
    runDDM vars True maxSize $ do
        let qs = quantsBformula formula
        ddmodels <- mapM (\(m,d) -> transformBmoduleToBDD d m) (zip bsmvs qs)
        ddformula <- transformBformulaToBDD formula
        return (ddmodels,ddformula)
        
transformBmoduleToBDD :: (QBFDDs s1,QBFDDs s2,QBFDDs s3,QBFDDs s4,Monad m) => (String,Quant) -> PackedBmodule -> DDM m (BDDmodel s1 s2 s3 s4)
transformBmoduleToBDD (dim,quant) p = withDDM isLocal $ toPackedDDmodule p >>= \dd -> {-trace (dim ++ ": " ++ show dd) $-} do
    st <- {-Trace.trace (show dim) $-} Reader.ask
    let init' = dd_init dd
    let invar' = {-Trace.trace ("init\n"++prettyprint (b_init p) ++ "\n" ++ show init'++"init") $-} dd_invar dd
    let trans' = {-Trace.trace ("invar\n"++prettyprint (b_invar p) ++ "\n" ++ show invar'++"invar") $-} dd_trans dd
    iden' <- {-Trace.trace ("trans\n"++show trans'++"trans") $-} identityReader $ DDs.dd_identity
    let ltl' = dd_ltlspec dd
    let model = BDDmodel init' invar' trans' iden' ltl' st
    return model
  where
    pvars = Map.fromList $ map (\n -> (addDimPident n (mkQuantDim dim),n)) $ Map.keys $ b_vars p
    isLocal (n,isNext) = fmap (,isNext) (Map.lookup n pvars)

transformBformulaToBDD :: (QBFDDs s,Monad m) => Bformula -> DDM m (BDDformula s)
transformBformulaToBDD f = {-trace ("formula: " ++ prettyprint f ++ "formula") $-} do
    let qs = quantsBformula f
    let e = exprBformula f
    ltl <- buildDDltl e
    ddvars <- Reader.asks varNames
    --Trace.trace ("formula dd " ++ show ltl ++"formula") $
    return $ BDDformula qs ltl (IntMap.map fst ddvars)

data BDDformula s = BDDformula { bdd_formula_quantifiers :: [(String,Quant)], bdd_formula_ltl :: DDltl s BDD, bdd_formula_vars :: IntMap Pident }
    deriving (Eq,Show,Generic)
    
instance Hashable s => Hashable (BDDformula s)

data QCIRstate = QCIRstate
    { qcir_st_quantifiers :: [Quantifier]
    , qcir_st_num_gates :: Int
    , qcir_st_gates :: IntMap GateExpr
    , qcir_st_cache :: HashMap (Int,BDD) QCIRgate
    , qcir_st_names :: QCIRnames
    } deriving (Eq,Show,Generic)
    
instance Hashable QCIRstate

type QCIRnames = Map (Pident,Int) GateId

type QCIRM = StrictState.StateT QCIRstate

data QCIRgate
    = Qand (IntMap IsNegated)
    | Qor (IntMap IsNegated)
    | Qbool Bool
    | Qid GateId IsNegated
    deriving (Eq,Ord,Show,Generic)
    
instance Hashable QCIRgate

lookupShowGate :: Monad m => Int -> QCIRM m String
lookupShowGate i = do
    st <- StrictState.get
    let gates = qcir_st_gates st
    let nums = qcir_st_num_gates st
    case IntMap.lookup i gates of
        Nothing -> case IntMap.lookup i (flipMapInt $ qcir_st_names st) of
            Nothing -> error $ "lookupGateExpr " ++ show i ++ " out of " ++ show nums
            Just (n,depth) -> return $ prettyPident n ++ "@" ++ show depth
        Just g -> showGateExpr g

showGateExpr :: Monad m => GateExpr -> QCIRM m String
showGateExpr g@(GateAnd is) = do
    ss <- liftM unlines $ mapM (\k -> lookupShowGate k >>= \sg -> return $ show k ++ ": " ++ sg) $ IntMap.keys is
    let s = show g
    return $ ss ++ "\n" ++ s
showGateExpr g@(GateAnd is) = do
    ss <- liftM unlines $ mapM (\k -> lookupShowGate k >>= \sg -> return $ show k ++ ": " ++ sg) $ IntMap.keys is
    let s = show g
    return $ ss ++ "\n" ++ s

showQCIRgate :: Monad m => QCIRgate -> QCIRM m String
showQCIRgate g@(Qand is) = do
    ss <- liftM unlines $ mapM (\k -> lookupShowGate k >>= \sg -> return $ show k ++ ": " ++ sg) $ IntMap.keys is
    let s = show g
    return $ ss ++ "\n" ++ s
showQCIRgate g@(Qor is) = do
    ss <- liftM unlines $ mapM (\k -> lookupShowGate k >>= \sg -> return $ show k ++ ": " ++ sg) $ IntMap.keys is
    let s = show g
    return $ ss ++ "\n" ++ s
showQCIRgate g@(Qbool b) = return $ show g
showQCIRgate g@(Qid k neg) = do
    sg <- lookupShowGate k
    return $ show k ++ ": " ++ sg ++ "\n" ++ show g

qand :: (IntMap IsNegated) -> QCIRgate
qand m = case IntMap.size m of
    0 -> Qbool True
    1 -> let (gid,isNeg) = popIntMap m in Qid gid isNeg
    _ -> Qand m

qor :: (IntMap IsNegated) -> QCIRgate
qor m = case IntMap.size m of
    0 -> Qbool False
    1 -> let (gid,isNeg) = popIntMap m in Qid gid isNeg
    _ -> Qor m

qcirToGate :: QCIRgate -> GateExpr
qcirToGate (Qand gs) = GateAnd gs
qcirToGate (Qor gs) = GateOr gs
qcirToGate (Qbool False) =  GateOr IntMap.empty
qcirToGate (Qbool True) = GateAnd IntMap.empty
qcirToGate (Qid g isNeg) = GateAnd $ IntMap.singleton g isNeg

newNonNegGate :: (Monad m) => QCIRgate -> QCIRM m GateId
newNonNegGate (Qid g False) = return g
newNonNegGate qg = mkNewGate qg

newNegGate :: (Monad m) => QCIRgate -> QCIRM m (GateId,IsNegated)
newNegGate (Qid g isNeg) = return (g,isNeg)
newNegGate qg = do
    gid <- mkNewGate qg
    return (gid,False)

mkNewGate :: (Monad m) => QCIRgate -> QCIRM m GateId
mkNewGate qg = do
    st <- StrictState.get
    let num = qcir_st_num_gates st
    let gates = qcir_st_gates st
    StrictState.put $ st { qcir_st_num_gates = succ num, qcir_st_gates = IntMap.insert num (qcirToGate qg) gates }
    return num

andQCIR :: (Monad m) => QCIRgate -> QCIRgate -> QCIRM m QCIRgate
andQCIR (Qbool True) y = return y
andQCIR (Qbool False) y = return $ Qbool False
andQCIR x (Qbool True) = return x
andQCIR x (Qbool False) = return $ Qbool False
andQCIR (Qand xs) (Qand ys) = case joinAnds xs ys of
    Nothing -> return $ Qbool False
    Just zs -> return $ qand zs
andQCIR (Qand xs) y = do
    (gy,yIsNeg) <- newNegGate y
    case insertAnd gy yIsNeg xs of
        Nothing -> return $ Qbool False
        Just zs -> return $ qand zs  
andQCIR x (Qand ys) = do
    (gx,xIsNeg) <- newNegGate x
    case insertAnd gx xIsNeg ys of
        Nothing -> return $ Qbool False
        Just zs -> return $ qand zs
andQCIR x y = do
    (gx,xIsNeg) <- newNegGate x
    (gy,yIsNeg) <- newNegGate y
    case toAnd [(gx,xIsNeg),(gy,yIsNeg)] of
        Nothing -> return $ Qbool False
        Just zs -> return $ qand zs

toAnd :: [(Int,IsNegated)] -> Maybe (IntMap IsNegated)
toAnd = foldM (\m (x,xIsNeg) -> insertAnd x xIsNeg m) IntMap.empty

insertAnd :: Int -> IsNegated -> IntMap IsNegated -> Maybe (IntMap IsNegated)
insertAnd gx xIsNeg ys = IntMap.alterF (insertIsNegatedF xIsNeg) gx ys

joinAnds :: IntMap IsNegated -> IntMap IsNegated -> Maybe (IntMap IsNegated)
joinAnds xs ys = do
    let keep = IntMap.preserveMissing
    let match = IntMap.zipWithAMatched $ \k x y -> mergeIsNegated x y
    IntMap.mergeA keep keep match xs ys

orQCIR :: (Monad m) => QCIRgate -> QCIRgate -> QCIRM m QCIRgate
orQCIR (Qbool False) y = return y
orQCIR (Qbool True) y = return $ Qbool True
orQCIR x (Qbool False) = return x
orQCIR x (Qbool True) = return $ Qbool True
orQCIR (Qor xs) (Qor ys) = return $ qor $ joinOrs xs ys
orQCIR (Qor xs) y = do
    (gy,yIsNeg) <- newNegGate y
    return $ qor $ insertOr gy yIsNeg xs
orQCIR x (Qor ys) = do
    (gx,xIsNeg) <- newNegGate x
    return $ qor $ insertOr gx xIsNeg ys
orQCIR x y = do
    (gx,xIsNeg) <- newNegGate x
    (gy,yIsNeg) <- newNegGate y
    return $ qor $ toOr [(gx,xIsNeg),(gy,yIsNeg)]

toOr :: [(Int,IsNegated)] -> IntMap IsNegated
toOr = foldl (\m (x,xIsNeg) -> insertOr x xIsNeg m) IntMap.empty

insertOr :: Int -> IsNegated -> IntMap IsNegated -> IntMap IsNegated
insertOr gx xIsNeg ys = IntMap.alter (insertIsNegated xIsNeg) gx ys

joinOrs :: IntMap IsNegated -> IntMap IsNegated -> IntMap IsNegated
joinOrs xs ys =
    let keep = IntMap.preserveMissing in
    let match = IntMap.zipWithMaybeAMatched $ \k x y -> return $ mergeIsNegated x y in
    IntMap.merge keep keep match xs ys 

insertIsNegatedF :: IsNegated -> Maybe IsNegated -> Maybe (Maybe IsNegated)
insertIsNegatedF isNeg mb = fmap Just $ insertIsNegated isNeg mb

insertIsNegated :: IsNegated -> Maybe IsNegated -> Maybe IsNegated
insertIsNegated x Nothing = Just x
insertIsNegated x (Just y) = mergeIsNegated x y

mergeIsNegated :: IsNegated -> IsNegated -> Maybe IsNegated
mergeIsNegated False False = Just False
mergeIsNegated True True = Just True
mergeIsNegated _ _ = Nothing

andsQCIR :: (Monad m,Foldable f) => f QCIRgate -> QCIRM m QCIRgate
andsQCIR = foldM andQCIR (Qbool True)

orsQCIR :: (Monad m,Foldable f) => f QCIRgate -> QCIRM m QCIRgate
orsQCIR = foldM orQCIR (Qbool False)

boolQCIR :: (Monad m) => Bool -> QCIRM m QCIRgate
boolQCIR = return . Qbool

notQCIR :: (Monad m) => QCIRgate -> QCIRM m QCIRgate
notQCIR (Qand gs) = return $ Qor $ IntMap.map not gs
notQCIR (Qor gs) = return $ Qand $ IntMap.map not gs
notQCIR (Qbool b) = return $ Qbool $ not b
notQCIR (Qid g isNeg) = return $ Qid g $ not isNeg

equivQCIR :: (Monad m) => QCIRgate -> QCIRgate -> QCIRM m QCIRgate
equivQCIR x y = do
    notx <- notQCIR x
    noty <- notQCIR y
    trues <- andQCIR x y
    falses <- andQCIR notx noty
    orQCIR trues falses    

bddToQCIR :: (Monad m) => Int -> (Int -> QCIRnames -> GateId) -> BDD -> QCIRM m QCIRgate
bddToQCIR depth render bdd = {-trace ("bddToQCIR " ++ show bdd) $-} do
    names <- StrictState.gets qcir_st_names
    let foldCPS :: Monad m => BDD -> (QCIRgate -> QCIRM m QCIRgate) -> QCIRM m QCIRgate
        foldCPS (BDD.Leaf b) k = k $ Qbool b
        foldCPS p@(BDD.Branch dd_i lo hi) k = do
            h <- StrictState.gets qcir_st_cache
            case HashMap.lookup (depth,p) h of
                Just g -> k g
                Nothing -> foldCPS lo $ \blo -> foldCPS hi $ \bhi -> do
                    let dd_n = render dd_i names
                    let v = Qid dd_n False
                    let notv = Qid dd_n True
                    elo <- andQCIR notv blo
                    ehi <- andQCIR v bhi
                    e <- orQCIR elo ehi
                    StrictState.modify $ \st -> 
                        let newCache = HashMap.insert (depth,p) e (qcir_st_cache st)
                        in newCache `seq` st { qcir_st_cache = newCache }
                    k e
    foldCPS bdd return
    --showg <- showQCIRgate g
    --trace (showg) $ return g

--bddToQCIR :: (Monad m) => Int -> (Int -> QCIRnames -> GateId) -> BDD -> QCIRM m QCIRgate
--bddToQCIR depth render (BDD.Leaf b) = return $ Qbool b
--bddToQCIR depth render p@(BDD.Branch dd_i lo hi) = do
--    h <- StrictState.gets qcir_st_cache
--    case HashMap.lookup (depth,p) h of
--        Just g -> return g
--        Nothing -> do
--            names <- StrictState.gets qcir_st_names
--            let dd_n = render dd_i names
--            let v = Qid dd_n False
--            let notv = Qid dd_n True
--            blo <- bddToQCIR depth render lo
--            elo <- andQCIR notv blo
--            bhi <- bddToQCIR depth render hi
--            ehi <- andQCIR v bhi
--            e <- orQCIR elo ehi
--            StrictState.modify $ \st -> st { qcir_st_cache = HashMap.insert (depth,p) e (qcir_st_cache st) }
--            return e

--bddToQCIR :: Monad m => Int -> (Int -> QCIRnames -> GateId) -> BDD -> QCIRM m QCIRgate
--bddToQCIR depth render bdd = do
--    names <- State.gets qcir_st_names
--    let goLeaf :: Monad m => IntMap IsNegated -> Bool -> QCIRM m (IntMap IsNegated)
--        goLeaf a True = newNegGate (Qand a) >>= \(gid,isNeg) -> return $ IntMap.singleton gid isNeg
--        goLeaf a False = return IntMap.empty
--        mkVar dd_i isNegated = let dd_n = render dd_i names in (dd_n,isNegated)
--        goBranch :: IntMap IsNegated -> Int -> V.Vector (IntMap IsNegated)
--        goBranch a dd_i = V.map go (V.fromList [mkVar dd_i True,mkVar dd_i False])
--            where go (v,isNeg) = IntMap.insert v isNeg a
--    dnfs <- BDD.accumM goBranch goLeaf IntMap.empty bdd
--    return $ Qor dnfs

class BuildDDs BDD s => QBFDDs s where
    bddsToQCIR :: (Monad m) => Int -> (Int -> QCIRnames -> GateId) -> s -> QCIRM m QCIRgate
    boolBDD :: Bool -> DDltl s BDD
    
instance QBFDDs (AndDDs BDD) where
    bddsToQCIR depth render (AndDDs bdds) = andsQCIR =<< mapM (bddToQCIR depth render) (Map.elems bdds)
    boolBDD False = DDexpr $ AndDDs $ Map.singleton IntSet.empty BDD.false
    boolBDD True = DDexpr $ AndDDs $ Map.singleton IntSet.empty BDD.true

instance QBFDDs (NextDDs BDD) where
    bddsToQCIR depth render (NextDDs bdds) = andsQCIR =<< mapM (bddToQCIR depth render) (Map.elems bdds)
    boolBDD False = DDexpr $ NextDDs $ Map.singleton IntSet.empty BDD.false
    boolBDD True = DDexpr $ NextDDs $ Map.singleton IntSet.empty BDD.true

instance QBFDDs (TreeDDs BDD) where
    bddsToQCIR depth render (NodeAndDDs xs) = andsQCIR =<< mapM (bddsToQCIR depth render . snd) xs
    bddsToQCIR depth render (NodeOrDDs xs) = orsQCIR =<< mapM (bddsToQCIR depth render . snd) xs
    bddsToQCIR depth render (LeafDDs sup (sz,bdd)) = bddToQCIR depth render bdd
    boolBDD False = DDexpr $ LeafDDs IntSet.empty (1,BDD.false)
    boolBDD True = DDexpr $ LeafDDs IntSet.empty (1,BDD.true)

registerModelPident :: Monad m => String -> Int -> Pident -> QCIRM m GateId
registerModelPident dim i n = do
    st <- StrictState.get
    let num = qcir_st_num_gates st
    let names = qcir_st_names st
    let qn = addDimPident n (mkQuantDim dim)
    StrictState.modify $ \st -> st { qcir_st_num_gates = succ num, qcir_st_names = Map.insert (qn,i) num names }
    return num

renderModelPident :: String -> Int -> DualPident -> QCIRnames -> GateId
renderModelPident dim i (n,isNext) names =
    let qn = addDimPident n (mkQuantDim dim) in
    case Map.lookup (qn,if isNext then i+1 else i) names of
        Just gid -> gid
        Nothing -> error $ "renderModelPident: gate for name not found " ++ show dim ++ " " ++ show i ++ " " ++ show (n,isNext)

renderFormulaPident :: Int -> Pident -> QCIRnames -> GateId
renderFormulaPident i n names =
    case Map.lookup (n,i) names of
        Just gid -> gid
        Nothing -> error $ "renderFormulaPident: gate for name not found " ++ show i ++" "++ show n

renderFormulaPidentM :: Monad m => Int -> Pident -> QCIRM m GateId
renderFormulaPidentM i n = StrictState.gets qcir_st_names >>= return . (renderFormulaPident i n)

addQuantifierQCIR :: Monad m => Quant -> [GateId] -> QCIRM m ()
addQuantifierQCIR q vs =
    StrictState.modify $ \st -> st { qcir_st_quantifiers = qcir_st_quantifiers st ++ [mkQuantifier q] }
  where
    mkQuantifier Qforall = QForall vs
    mkQuantifier Qexists = QExists vs

-- registers variables
bddModelToQCIRVars :: (QBFDDs s1,QBFDDs s2,QBFDDs s3,QBFDDs s4,Monad m) => Int -> Bool -> ((String,Quant),BDDmodel s1 s2 s3 s4) -> QCIRM m [GateId]
bddModelToQCIRVars k isHalting ((dim,quant),model) = do
    let st = bdd_model_st model
    let vars = varNames st
    let limit = if isHalting then k+1 else k
    liftM concat $ forM [0..limit] $ \i -> mapM (registerModelPident dim i) $ map fst $ filter (not . snd) $ IntMap.elems vars 

-- unrolls model
bddModelToQCIR :: (QBFDDs s1,QBFDDs s2,QBFDDs s3,QBFDDs s4,Monad m) => Int -> Bool -> (((String,Quant),BDDmodel s1 s2 s3 s4),[GateId]) -> QCIRM m ((Quant,QCIRgate),QCIRgate)
bddModelToQCIR k isHalting (((q,quant),model),newgates) = do
    let st = bdd_model_st model
    let vars = varNames st
    addQuantifierQCIR quant newgates
    let render i dd_i = renderModelPident q i (unsafeIntLookupNote "bddModelToQCIR" dd_i vars)
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
                    in renderModelPident q i dd_n names
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
    --trace ("model " ++ show res ++ " model" ++ show quant) $
    return (res,halted)

-- when nothing assume mixed semantics (consider evidence only for bound k)
bddLtlToQCIR :: (QBFDDs s,Monad m) => Int -> Maybe Sem -> (Int -> Int -> QCIRnames -> GateId) -> QCIRgate -> DDltl s BDD -> QCIRM m QCIRgate
bddLtlToQCIR k sem render halted ltl = unroll 0 ltl
    where
    unroll :: (QBFDDs s,Monad m) => Int -> DDltl s BDD -> QCIRM m QCIRgate
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
                DDop2 Pv e1 e2 -> error "release TDB"
                otherwise -> error $ "bddLtlToQCIR: " ++ show i ++" "++ show ltl ++ " " ++ show sem
            Just Pes -> boolQCIR False
            Just Opt -> boolQCIR True
            Just Hpes -> case ltl of
                DDop1 Pg e1 -> return halted
                DDop1 Px e1 -> andQCIR halted =<< unroll (i-1) e1
                DDop2 Pu e1 e2 -> boolQCIR False
                DDop2 Pv e1 e2 -> error "release TDB"
                otherwise -> error $ "bddLtlToQCIR: " ++ show i ++" "++ show ltl ++ " " ++ show sem
            Just Hopt -> case ltl of
                DDop1 Pg e1 -> boolQCIR True
                DDop1 Px e1 -> do
                    nothalted <- notQCIR halted
                    orQCIR nothalted =<< unroll (i-1) e1
                DDop2 Pu e1 e2 -> notQCIR halted
                DDop2 Pv e1 e2 -> error "release TBD"
                otherwise -> error $ "bddLtlToQCIR: " ++ show i ++" "++ show ltl ++ " " ++ show sem
        else error $ "bddLtlToQCIR: " ++ show i ++" "++ show ltl ++ " " ++ show sem
    unroll i e@(DDop1 Pg e1) = do
        qe1 <- unroll i e1
        andQCIR qe1 =<< unroll (i+1) e
    unroll i (DDop1 Px e1) = unroll (i+1) e1
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

buildQCIR :: Monad m => QCIRM m QCIRgate -> m (QCIR,[IntMap NameSubst])
buildQCIR m = do
    (out,QCIRstate qs _ gs cache names) <- StrictState.runStateT (m >>= newNonNegGate) (QCIRstate [] 1 IntMap.empty HashMap.empty Map.empty)
    let ss = map (fmap fromQCIRNameSubst) $ buildNameSubsts qs names
    return (QCIR qs out gs,ss)

type QCIRNameSubst = Map Pident GateId

fromQCIRNameSubst :: QCIRNameSubst -> NameSubst
fromQCIRNameSubst = fmap identGate

identGate :: GateId -> (Pident,ExprType)
identGate i = (identName i,EBool)

identName :: GateId -> Pident
identName i = Pident ("x"++show i) []

buildNameSubsts :: [Quantifier] -> QCIRnames -> [IntMap QCIRNameSubst]
buildNameSubsts qs names = map buildNameSubst qs
    where
    gates :: IntMap (Pident,Int)
    gates = flipMapInt names
    
    build :: [GateId] -> IntMap QCIRNameSubst
    build gids = IntMap.foldlWithKey go IntMap.empty gates'
        where
        gates' = IntMap.filterWithKey (\k v -> k `IntSet.member` (IntSet.fromList gids)) gates
        go :: IntMap QCIRNameSubst -> GateId -> (Pident,Int) -> IntMap QCIRNameSubst 
        go acc gid (n,i) = IntMap.insertWith Map.union i (Map.singleton (remDimPident n) gid) acc
    buildNameSubst :: Quantifier -> IntMap QCIRNameSubst
    buildNameSubst (QForall gids) = build gids
    buildNameSubst (QExists gids) = build gids

transformBDDToQCIR :: (QBFDDs s1,QBFDDs s2,QBFDDs s3,QBFDDs s4,Monad m) => Int -> Sem -> [BDDmodel s1 s2 s3 s4] -> BDDformula s4 -> m (QCIR,[IntMap NameSubst])
transformBDDToQCIR k sem models formula = buildQCIR $ do
    let qs = bdd_formula_quantifiers formula
    let vars = bdd_formula_vars formula
    let qmodels = zip qs models
    let isHalt = isHaltingSem sem
    modelvars <- mapM (bddModelToQCIRVars k isHalt) qmodels
    (qfsms,halteds) <- liftM unzip $ mapM (bddModelToQCIR k isHalt) (zip qmodels modelvars)
    halted <- andsQCIR halteds
    let renderLTL i dd_i names = 
            let dd_n = unsafeIntLookupNote "transformBDDToQCIR" dd_i vars
            in renderFormulaPident i dd_n names
    qformula <- bddLtlToQCIR k (Just sem) renderLTL halted (bdd_formula_ltl formula)
    --trace ("models\n"++ unlines (map show qfsms) ++ "\nformula: " ++ show qformula ++ "modelsformula") $
    createFinalProperty qfsms qformula

createFinalProperty :: Monad m => [(Quant,QCIRgate)] -> QCIRgate -> QCIRM m QCIRgate
createFinalProperty [] gf = return gf
createFinalProperty ((Qforall,gm):xs) gf = do
    notgm <- notQCIR gm
    orQCIR notgm =<< createFinalProperty xs gf
createFinalProperty ((Qexists,gm):xs) gf = andQCIR gm =<< createFinalProperty xs gf

constructSmvTraces :: [(String,Quant)] -> [IntMap Subst] -> ResultValues -> [Maybe Trace]
constructSmvTraces dims names res = map constructSmvTrace $ zip dims names
    where
    ress :: Subst
    ress = IntMap.foldlWithKey (\acc i b -> Map.insert (identName i) (Pebool b) acc) Map.empty res
    constructSmvTrace :: ((String,Quant),IntMap Subst) -> Maybe Trace
    constructSmvTrace ((dim,q),vs) = checkStaticTrace $ Trace desc ty (map mkState $ IntMap.toList vs)
        where
        ty = case q of { Qforall -> Counterexample; Qexists -> Example }
        desc = prettyprint q ++" "++ dim
        mkState (i,ss) = State (show i) False (fmap evaluateExpr $ composeSubst ss ress)

checkStaticTrace :: Trace -> Maybe Trace
checkStaticTrace t@(Trace desc ty sts) = if all isFreeState sts then Nothing else Just t
    where
    isFreeState :: State -> Bool
    isFreeState s = all isFreeExpr (state_vars s)



