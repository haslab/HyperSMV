module Transform.DDs where

import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (ReaderT(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad
import Control.Monad.Trans
import Data.Vector (Vector(..))
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Safe
import Data.List as List
import qualified Data.Foldable as Foldable
import Control.Monad.Identity
import GHC.Generics
import qualified Data.Bit as Bit
import Data.Proxy
import Data.Hashable

import Utils
import Pretty
import Smv.Typing
import Smv.Syntax
import Smv.Packed
import Data.IDD (IDD)
import qualified Data.IDD as IDD
import Data.BDD (BDD)
import qualified Data.BDD as BDD
import Data.DD (DD(..))
import qualified Data.DD as DD
import Data.DDs (DDstructure,AndDDs(..),NextDDs(..))
import qualified Data.DDs as DDs
import Transform.Bexpr
import Transform.Pexpr

--import Debug.Trace as Trace

extendDDM :: Monad m => Map DualPident VarType -> DDM m a -> DDM m a
extendDDM exts m = Reader.local withDDReader m
    where
    withDDReader :: DDReader -> DDReader
    withDDReader (DDReader names ids szs maxSize) = DDReader names' (flipIntMap names') szs' maxSize
        where
        next = succ $ fst $ IntMap.findMax names
        extnames = IntMap.fromList $ zip [next..] (Map.keys exts)
        names' = IntMap.union names extnames
        extszs = IntMap.fromList $ zip [next..] (Map.elems exts)
        szs' = IntMap.union szs extszs

withDDM :: Monad m => (DualPident -> Maybe DualPident) -> DDM m a -> DDM m a
withDDM p m = Reader.local withDDReader m
    where
    withDDReader :: DDReader -> DDReader
    withDDReader (DDReader names ids szs maxSize ) = DDReader names' (flipIntMap names') szs' maxSize
        where
        names' = (IntMap.mapMaybeWithKey (\k n -> p n) names)
        szs' = IntMap.intersection szs names'

data DDReader = DDReader { varNames :: IntMap DualPident, varIds :: Map DualPident Int, varSizes :: IntMap VarType, maxDDSize :: Integer }
    deriving (Eq,Ord,Show,Generic)
type DDM m = ReaderT DDReader m 
type DDState s = HashMap Bexpr s

instance Hashable DDReader

instance Monad m => DDs.NextDDsMonad (DDM m) where
    dd_nextIds = Reader.asks (IntMap.keysSet . IntMap.filter snd . varNames)
    dd_nexts = do
        nexts <- Reader.asks (IntMap.toList . IntMap.filter snd . varNames)
        liftM IntMap.fromList $ forM nexts $ \(next_i,(next_n,_)) -> do
            prev_i <- varId (next_n,False)
            return (next_i,prev_i)

sortedTypes :: Monad m => DDM m [(DualPident,VarType)]
sortedTypes = do
    names <- Reader.asks varNames
    szs <- Reader.asks varSizes
    return $ map ((\i -> unsafeIntLookupNote "sortedTypes" i names) >< id) $ IntMap.toList szs

typeOf :: Monad m => Int -> DDM m VarType
typeOf i = Reader.asks (unsafeIntLookupNote "typeOf" i . varSizes)

varPtypes :: Monad m => DDM m PackedPtypes
varPtypes = Reader.asks (\s -> mapWithKey fst exprOfVarType $ varIds s `composeMap` (fromIntMap $ varSizes s))

varTypes :: Monad m => DDM m (Map Pident VarType)
varTypes = Reader.asks (\s -> mapWithKey fst id $ varIds s `composeMap` (fromIntMap $ varSizes s))

--valuesOf :: (DD dd,Monad m) => Int -> DDM m (DD.Vals dd)
--valuesOf v = liftM (fromJustNote "valuesOf" . IntMap.lookup v) values

--values :: (DD dd,Monad m) => DDM m (IntMap (DD.Vals dd))
--values = Reader.asks (IntMap.map toValues . varSizes)
--    where
--    toValues :: (DD dd) => VarType -> DD.Vals dd
--    toValues VBool = UV.fromList $ map DD.intToVal [0,1]
--    toValues (VInt is) = UV.fromList $ map DD.intToVal $ IntSet.toList is

--indexesOf :: Monad m => Int -> DDM m (Map (Either Int Bool) Int)
--indexesOf v = liftM (fromJustNote "indexesOf" . IntMap.lookup v) indexes
--
--indexes :: Monad m => DDM m (IntMap (Map (Either Int Bool) Int))
--indexes = Reader.asks (IntMap.map toIndexes . varSizes)
--    where
--    toIndexes :: VarType -> Map (Either Int Bool) Int
--    toIndexes VBool = Map.fromList [(Right False,0),(Right True,1)]
--    toIndexes (VInt is) = Map.fromList $ zip (map Left $ IntSet.toList is) [0..]

--valIndexes :: (DD dd,Monad m) => DDM m (IntMap (Map (DD.Val dd) Int))
--valIndexes = Reader.asks (IntMap.map toIndexes . varSizes)
--    where
--    toIndexes :: DD dd => VarType -> Map (DD.Val dd) Int
--    toIndexes VBool = Map.fromList [(DD.boolToVal False,0),(DD.boolToVal True,1)]
--    toIndexes (VInt is) = Map.fromList $ zip (map DD.intToVal $ IntSet.toList is) [0..]

sortedVars :: Monad m => DDM m [DualPident]
sortedVars = Reader.asks (IntMap.elems . varNames)

varId :: Monad m => DualPident -> DDM m Int
varId n = Reader.asks (\r -> fromJustNote ("varId " ++ prettyprint n ++ " " ++ show r) $ Map.lookup n $ varIds r)

varName :: Monad m => Int -> DDM m DualPident
varName i = Reader.asks (fromJustNote "varName" . IntMap.lookup i . varNames)

varSize :: Monad m => DualPident -> DDM m VarType
varSize n = Reader.asks (\s -> fromJustNote "varSize" $ Map.lookup n (varIds s) >>= \i -> IntMap.lookup i (varSizes s))

newDDState :: DDState s
newDDState = HashMap.empty

newDDReader :: PackedPvars -> Bool -> Integer -> DDReader
newDDReader vars isDual maxSize = DDReader names ids sizes maxSize
    where
    sides = if isDual then [False,True] else [False]
    allvars = [ ((n,side),toVarType t) | side <- sides, (n,t) <- Map.toList vars ]
    cmp ((n,side),t) = (Set.map NegString (dimsPident n),sizeOfVarType t,n,side)
    sorted = zip [0..] $ sortBy (\x y -> compare (cmp x) (cmp y)) allvars
    names = IntMap.fromList $ map (id >< fst) sorted
    ids = flipIntMap names
    sizes = IntMap.fromList $ map (id >< snd) sorted

runDDM :: Monad m => PackedPvars -> Bool -> Integer -> DDM m a -> m a
runDDM vars isDual maxSize m = Reader.runReaderT m (newDDReader vars isDual maxSize )

--buildDD :: (BuildDD dd,Monad m) => Bexpr -> DDM m dd
--buildDD e = identityReader $ do
--    dds :: AndDDs dd <- buildDDs e
--    DDs.flatten dds

buildDDs :: (BuildDDs dd s,Monad m) => Bexpr -> DDM m s
buildDDs e = {-trace ("buildDDs " ++ prettyprint e) $-} State.evalStateT (State.mapStateT identityReader $ bexprToDDs e) newDDState
  where
    bexprToDDs :: (BuildDDs dd s) => Bexpr -> StateT (DDState s) (DDM Identity) s
    bexprToDDs e = {-trace ("bexprToDDs " ++ prettyprint e) $-} do
        h <- State.get
        case HashMap.lookup e h of
            Just i -> {-trace ("bexprToDDs cache " ++ show i) $-} return i
            Nothing -> do
                i <- bexprToDDs' e
                State.modify $ \h -> HashMap.insert e i h
                {-trace ("bexprToDDs output " ++ show i) $-}
                return i

    bexprToDDs' :: (BuildDDs dd s) => Bexpr -> StateT (DDState s) (DDM Identity) s
    bexprToDDs' (Bbool b) = lift $ DDs.singleton =<< DD.bool b
    bexprToDDs' (Bvar n VBool) = lift $ DDs.singleton =<< buildVarDD n VBool (Right True)
    bexprToDDs' (Bopn Pand es) = lift . DDs.ands =<< mapM bexprToDDs (HashSet.toList es)
    bexprToDDs' (Bopn Por es) = lift . DDs.ors =<< mapM bexprToDDs (HashSet.toList es)
    bexprToDDs' (Bop1 o e1) = bexprToDDs1 o e1
    bexprToDDs' (Bop2 o e1 e2) = bexprToDDs2 o e1 e2
    bexprToDDs' e = error $ "bexprToDDs': " ++ prettyprint e
    
    bexprToDDs1 :: (BuildDDs dd s) => Pop1 -> Bexpr -> StateT (DDState s) (DDM Identity) s
    bexprToDDs1 Patom e1 = bexprToDDs e1
    bexprToDDs1 Pnot (Bvar n VBool) = lift $ DDs.singleton =<< buildVarDD n VBool (Right False)
    bexprToDDs1 Pnot e1 = lift . DDs.not =<< bexprToDDs e1
    bexprToDDs1 o e1 = error $ "bexprToDDs1: " ++ show o ++ " " ++ show e1
    
    bexprToDDs2 :: (BuildDDs dd s) => Pop2 -> Bexpr -> Bexpr -> StateT (DDState s) (DDM Identity) s
    bexprToDDs2 Pequiv (Bvar n t) (Bbool b) = lift $ DDs.singleton =<< buildVarDD n t (Right b)
    bexprToDDs2 Pequiv e1 e2 = do
        dd1 <- bexprToDDs e1
        dd2 <- bexprToDDs e2
        lift $ DDs.equiv dd1 dd2  
    bexprToDDs2 Pimplies e1 (Bbool False) = bexprToDDs $ bnot e1
    bexprToDDs2 Pimplies e1 (Bbool True) = lift $ DDs.singleton =<< DD.true
    bexprToDDs2 Pimplies e1 e2 = do
        dd1 <- bexprToDDs e1
        dd2 <- bexprToDDs e2
        lift $ DDs.implies dd1 dd2
    bexprToDDs2 Peq (Bbool b1) (Bbool b2) = bexprToDDs $ Bbool (b1==b2) 
    bexprToDDs2 Peq (Bint i1) (Bint i2) = bexprToDDs $ Bbool (i1==i2) 
    bexprToDDs2 Pneq (Bbool b1) (Bbool b2) = bexprToDDs $ Bbool (b1/=b2) 
    bexprToDDs2 Pneq (Bint i1) (Bint i2) = bexprToDDs $ Bbool (i1/=i2) 
    bexprToDDs2 Plt (Bint i1) (Bint i2) = bexprToDDs $ Bbool (i1<i2) 
    bexprToDDs2 Pleq (Bint i1) (Bint i2) = bexprToDDs $ Bbool (i1<=i2) 
    bexprToDDs2 Pgt (Bint i1) (Bint i2) = bexprToDDs $ Bbool (i1>i2) 
    bexprToDDs2 Pgeq (Bint i1) (Bint i2) = bexprToDDs $ Bbool (i1>=i2)
    bexprToDDs2 Peq (Bbool True) e2 = bexprToDDs e2
    bexprToDDs2 Peq (Bbool False) e2 = bexprToDDs $ Bop1 Pnot e2
    bexprToDDs2 Peq e1 (Bbool True) = bexprToDDs e1
    bexprToDDs2 Peq e1 (Bbool False) = bexprToDDs $ Bop1 Pnot e1
    bexprToDDs2 Pin (Bints is1) (Bints is2) = bexprToDDs $ Bbool (IntSet.isSubsetOf is1 is2)
    bexprToDDs2 Peq (Bint i1) (Bop2 Pplus (Bint i21) e22) = bexprToDDs $ Bop2 Peq e22 (Bint $ i1 - i21)
    bexprToDDs2 Peq (Bint i1) (Bop2 Pplus e21 (Bint i22)) = bexprToDDs $ Bop2 Peq e21 (Bint $ i1 - i22)
    bexprToDDs2 Peq (Bint i1) (Bop2 Pminus (Bint i21) e22) = bexprToDDs $ Bop2 Peq e22 (Bint $ i21 - i1)
    bexprToDDs2 Peq (Bint i1) (Bop2 Pminus e21 (Bint i22)) = bexprToDDs $ Bop2 Peq e21 (Bint $ i1 + i22)
    bexprToDDs2 Peq e1@(Bvar n1 t1) e2@(Bbool b2) = lift $ DDs.singleton =<< buildVarDD n1 t1 (Right b2)
    bexprToDDs2 Peq e1@(Bvar n1 t1) e2@(Bint i2) = lift $ DDs.singleton =<< buildVarDD n1 t1 (Left $ IntSet.singleton i2)
    bexprToDDs2 Peq e1@(Bbool b1) e2@(Bvar n2 t2) = lift $ DDs.singleton =<< buildVarDD n2 t2 (Right b1)
    bexprToDDs2 Peq e1@(Bint i1) e2@(Bvar n2 t2) = lift $ DDs.singleton =<< buildVarDD n2 t2 (Left $ IntSet.singleton i1)
    bexprToDDs2 Pin e1@(Bvar n1 t1) e2@(Bbool b2) = lift $ DDs.singleton =<< buildVarDD n1 t1 (Right b2)
    bexprToDDs2 Pin e1@(Bvar n1 t1) e2@(Bints is2) = lift $ DDs.singleton =<< buildVarDD n1 t1 (Left is2)
    bexprToDDs2 Pin e1 e2 | Prelude.not (isNonDetBexpr e2) = bexprToDDs2 Peq e1 e2
    --bexprToDDs2 o@(isCmpOp2 -> True) e1@(Bvar n1 _) e2@(Bint i2) = do
    --    lift $ DDs.singleton =<< evaluateIntVar o n1 i2
    --bexprToDDs2 o@(isCmpOp2 -> True) e1@(Bint i1) e2@(Bvar n2 _) = do
    --    lift $ DDs.singleton =<< evaluateIntVar (invCmpOp2 o) n2 i1
    bexprToDDs2 o@(isCmpOp2 -> True) e1 e2@(Bvar n2 t2) = do
        vs2 <- lift $ expandVar n2 t2
        bexprToDDs $ bors $ HashSet.map (\v2 -> Bop2 Pin e2 v2 `band` Bop2 o e1 v2) vs2    
    bexprToDDs2 o@(isCmpOp2 -> True) e1@(Bvar n1 t1) e2 = do
        vs1 <- lift $ expandVar n1 t1
        bexprToDDs $ bors $ HashSet.map (\v1 -> Bop2 Pin e1 v1 `band` Bop2 o v1 e2) vs1
    bexprToDDs2 o e1 e2 = error $ "bexprToDDs2: " ++ show o ++ " " ++ show e1 ++ " " ++ show e2

--evaluateIntVar :: Monad m => Pop2 -> DualPident -> Int -> DDM m DD 
--evaluateIntVar Peq n i = buildVarDD n (Left $ IntSet.singleton i)
--evaluateIntVar o n i = do
--    sz <- varSize n
--    case sz of
--        VInt szs -> evaluateInt szs o i
--        _ -> error "evaluateIntVar"
--  where
--    evaluateInt :: Monad m => IntSet -> Pop2 -> Int -> DDM m DD
--    evaluateInt sz Pneq i = buildVarDD n $ Left $ IntSet.delete i sz
--    evaluateInt sz Plt i = buildVarDD n $ Left $ IntSet.filter (< i) sz
--    evaluateInt sz Pleq i = buildVarDD n $ Left $ IntSet.filter (<= i) sz
--    evaluateInt sz Pgt i = buildVarDD n $ Left $ IntSet.filter (> i) sz
--    evaluateInt sz Pgeq i = buildVarDD n $ Left $ IntSet.filter (>= i) sz

expandVar :: Monad m => DualPident -> VarType -> DDM m (HashSet Bexpr)
expandVar n sz = do
    let vs = case sz of
            VInt is -> map Bint $ IntSet.toList is
            VBool -> [Bbool False,Bbool True]
    return $ HashSet.fromList vs

class (Hashable s,DDstructure (DDM Identity) dd s,BuildDD dd) => BuildDDs dd s | s -> dd where
    ddsToBexpr :: Monad m => s -> BM (DDM m) Bexpr
    ddsToExpr :: Monad m => s -> DDM m Pexpr
    ddsToConjunction :: Monad m => s -> DDM m [dd]

instance (BuildDD dd) => BuildDDs dd (DDs.AndDDs dd) where
    
    ddsToBexpr (DDs.AndDDs dds) = liftM (Bopn Pand . HashSet.fromList) $ mapM ddToBexpr $ Map.elems dds
    
    ddsToExpr (DDs.AndDDs dds) = liftM (Peopn Pand) $ mapM ddToExpr $ Map.elems dds
    
    ddsToConjunction (AndDDs dds) = return $ Map.elems dds
    
instance (BuildDD dd) => BuildDDs dd (DDs.NextDDs dd) where
    
    ddsToBexpr (DDs.NextDDs dds) = liftM (Bopn Pand . HashSet.fromList) $ mapM ddToBexpr $ Map.elems dds   
    
    ddsToExpr (DDs.NextDDs dds) = liftM (Peopn Pand) $ mapM ddToExpr $ Map.elems dds   
    
    ddsToConjunction (NextDDs dds) = return $ Map.elems dds
    
instance (BuildDD dd) => BuildDDs dd (DDs.TreeDDs dd) where
    
    ddsToBexpr (DDs.NodeAndDDs dds) = liftM (Bopn Pand . HashSet.fromList) $ mapM (ddsToBexpr . snd) $ multiMapElems dds
    ddsToBexpr (DDs.NodeOrDDs dds) = liftM (Bopn Por . HashSet.fromList) $ mapM (ddsToBexpr . snd) $ multiMapElems dds
    ddsToBexpr (DDs.LeafDDs sup (sz,dd)) = ddToBexpr dd
    
    ddsToExpr (DDs.NodeAndDDs dds) = liftM (Peopn Pand) $ mapM (ddsToExpr . snd) $ multiMapElems dds
    ddsToExpr (DDs.NodeOrDDs dds) = liftM (Peopn Por) $ mapM (ddsToExpr . snd) $ multiMapElems dds
    ddsToExpr (DDs.LeafDDs sup (sz,dd)) = ddToExpr dd
    
    ddsToConjunction (DDs.NodeAndDDs dds) = do
        dds' <- mapM (ddsToConjunction . snd) $ multiMapElems dds
        return $ concat dds'
    ddsToConjunction (DDs.LeafDDs sup (sz,dd)) = return [dd]
    ddsToConjunction dds = identityReader $ do
        dd <- DDs.flatten dds
        return [dd]

class (Hashable dd,DD (DDM Identity) dd) => BuildDD dd where
    buildVarDD :: Monad m => DualPident -> VarType -> Either IntSet Bool -> DDM m dd
--    buildValDD :: Monad m => Int -> DD.Val dd -> DDM m dd
    ddToBexpr :: Monad m => dd -> BM (DDM m) Bexpr
    ddToExpr :: Monad m => dd -> DDM m Pexpr
    ddToExpr dd = bmInDDM (ddToBexpr dd >>= fromBexpr)
   
instance BuildDD DD.GIDD where
     buildVarDD = buildVarGIDD
     ddToBexpr = giddToBexpr
     ddToExpr = giddToExpr

buildVarGIDD :: (Monad m) => DualPident -> VarType -> Either IntSet Bool -> DDM m DD.GIDD
buildVarGIDD n ty vs = do
    ni <- varId n
    case vs of
        Left is -> DD.var' ni (Set.map DD.intToVal $ fromIntSet is)
        Right b -> DD.var ni (DD.boolToVal b)
    
--    let num = sizeOfVarType ty
--    idxs <- indexesOf ni 
--    r <- Reader.ask
--    let project v = case (ty,v) of
--            (VBool,Right b) -> IntSet.singleton (unsafeLookupNote ("buildVarIDD " ++ show n ++ " " ++ show b ++ " " ++ show idxs) (Right b) idxs)
--            (VInt szs,Left is) -> IntSet.map (\i -> unsafeLookupNote ("buildVarIDD " ++ show r ++ "\n" ++ show n ++ " " ++ show ty ++ " " ++ show i ++ " " ++ show idxs) (Left i) idxs) (IntSet.intersection is szs)
--    let res = IDD.var ni (num,project vs)
--    --trace ("buildVarIDD " ++ show n ++" "++ show ty ++" "++ show vs ++ " " ++ show ni) $
--    return $ res

giddToExpr :: (Monad m) => DD.GIDD -> DDM m Pexpr
giddToExpr (DD.GIDD dd) = IDD.foldM goBranch goLeaf dd
  where
    goLeaf :: Monad m => Bool -> DDM m Pexpr
    goLeaf b = return $ Pebool b
    goBranch :: Monad m => Int -> Vector Pexpr -> DDM m Pexpr
    goBranch ni cs = do
        n <- varName ni
        t <- typeOf ni
        vals <- DD.vals ni
        let mkintval i = Peop2 Peq (pvar n $ exprOfVarType t) (Peint i) 
        let mkboolval b = if b then pvar n EBool else pnot (pvar n EBool) 
        let mkval i = case t of { VInt _ -> mkintval i; VBool -> mkboolval (intToBool i) } 
        return $ pors $ V.toList $ V.map (\(v,c) -> pands [mkval v,c]) (V.zip (UV.convert vals) cs)

giddToBexpr :: Monad m => DD.GIDD -> BM (DDM m) Bexpr
giddToBexpr (DD.GIDD dd) = IDD.foldM goBranch goLeaf dd
  where
    goLeaf :: Monad m => Bool -> BM (DDM m) Bexpr
    goLeaf b = return $ Bbool b
    goBranch :: Monad m => Int -> Vector Bexpr -> BM (DDM m) Bexpr
    goBranch ni cs = do
        n <- lift $ varName ni
        t <- lift $ typeOf ni
        vals <- lift $ DD.vals ni
        let mkintval i = Bop2 Peq (Bvar n t) (Bint i) 
        let mkboolval b = if b then Bvar n VBool else bnot (Bvar n VBool) 
        let mkval i = case t of { VInt _ -> mkintval i; VBool -> mkboolval (intToBool i) } 
        return $ bors $ HashSet.fromList $ V.toList $ V.map (\(v,c) -> mkval v `band` c) (V.zip (UV.convert vals) cs)
    
instance BuildDD BDD where
     buildVarDD = buildVarBDD
     ddToBexpr = bddToBexpr
     ddToExpr = bddToExpr

--buildValBDD :: Monad m => Int -> Bit.Bit -> DDM m BDD
--buildValBDD dd_i (Bit.Bit b) = do
--    return $ (if b then id else BDD.not) (BDD.var dd_i)
--
buildVarBDD :: (Monad m) => DualPident -> VarType -> Either IntSet Bool -> DDM m BDD
buildVarBDD n ty vs = do
    ni <- varId n
    case vs of
        Left _ -> error "buildVarBDD int"
        Right b -> DD.var ni (DD.boolToVal b)

bddToExpr :: (Monad m) => BDD -> (DDM m) Pexpr
bddToExpr dd = BDD.foldCPSM goBranch goLeaf return dd
    where
    goLeaf :: Monad m => Bool -> (DDM m) Pexpr
    goLeaf b = return $ Pebool b
    goBranch :: Monad m => Int -> Pexpr -> Pexpr -> (DDM m) Pexpr
    goBranch ni lo hi = do
        n <- varName ni
        let ff = pands [pnot $ pvar n EBool,lo]
        let tt = pands [pvar n EBool,hi]
        return $ pors [ff,tt]

bddToBexpr :: (Monad m) => BDD -> BM (DDM m) Bexpr
bddToBexpr dd = BDD.foldCPSM goBranch goLeaf return dd
    where
    goLeaf :: Monad m => Bool -> BM (DDM m) Bexpr
    goLeaf b = return $ Bbool b
    goBranch :: Monad m => Int -> Bexpr -> Bexpr -> BM (DDM m) Bexpr
    goBranch ni lo hi = do
        n <- lift $ varName ni
        let ff = (bnot $ Bvar n VBool) `band` lo
        let tt = (Bvar n VBool) `band` hi
        return $ ff `bor` tt

--bddToBexpr :: (Monad m) => BDD -> BM (DDM m) Bexpr
--bddToBexpr (BDD.Leaf b) = return $ Bbool b
--bddToBexpr (BDD.Branch ni lo hi) = do
--    n <- lift $ varName ni
--    elo <- bddToBexpr lo
--    ehi <- bddToBexpr hi
--    let ff = (bnot $ Bvar n VBool) `band2` elo
--    let tt = (Bvar n VBool) `band2` ehi
--    return $ ff `bor2` tt

--bddToBexpr :: (Monad m) => BDD -> BM (DDM m) Bexpr
--bddToBexpr dd = do
--    r <- lift $ Reader.ask
--    return $ BDD.accum (goBranch r) goLeaf (Bbool True) dd
--  where
--    goLeaf e False = Bbool False
--    goLeaf e True = e
--    goBranch r e ni = V.fromList [band2 e (bnot $ Bvar n VBool),band2 e (Bvar n VBool)]
--        where
--        n = Reader.runReader (varName ni) r

bReaderDDM :: Monad m => DDM m BReader
bReaderDDM = varTypes

bmInDDM :: Monad m => BM (DDM m) a -> DDM m a
bmInDDM m = bReaderDDM >>= \r -> doBM r m

{-# INLINE mkDDMap #-}
-- mapping from dd indices to explicit state indices
mkDDMap :: IntMap DualPident -> V.Vector (Pident,VarType) -> IntMap Int
mkDDMap dd_names exp_ns = IntMap.map fst dd_names `composeIntMap` pe_map
    where pe_map = vectorIndices (V.map fst $ exp_ns)
    
{-# INLINE mkExpMap #-}
-- mapping from explicit state indices to dd indices
mkExpMap :: IntMap DualPident -> V.Vector (Pident,VarType) -> IntMap Int
mkExpMap dd_names exp_ns = flipIntMapInt (mkDDMap dd_names exp_ns)

{-# INLINE evalExplicitDDs #-}
evalExplicitDDs :: (BuildDDs dd s,Monad m) => IntMap Int -> s -> DD.Vals dd -> DDM m Bool
evalExplicitDDs dd_map dds exp_vals = identityReader $ do
    r <- Reader.ask
    flip DDs.evaluate dds $ \dd_i ->
        let dd_n = Reader.runReader (varName dd_i) r
            exp_i = unsafeIntLookupNote ("evalDDs " ++ show dd_i ++ " " ++ prettyprint dd_n ++ " " ++ show dd_map) dd_i dd_map
        in uvIndex "evalDDs" exp_vals exp_i

evalExplicitDDs' :: BuildDDs dd s => DDReader -> IntMap Int -> s -> DD.Vals dd -> Bool
evalExplicitDDs' r dd_map dds st = Reader.runReader (evalExplicitDDs dd_map dds st) r

{-# INLINE evalExplicitDD #-}
evalExplicitDD :: (BuildDD dd,Monad m) => IntMap Int -> dd -> DD.Vals dd -> DDM m Bool
evalExplicitDD dd_map dd exp_vals = identityReader $ flip DD.evaluate dd $ \dd_i -> 
    let Just exp_i = IntMap.lookup dd_i dd_map
    in uvIndex "evalDD" exp_vals exp_i

evalExplicitDD' :: (BuildDD dd) => DDReader -> IntMap Int -> dd -> DD.Vals dd -> Bool
evalExplicitDD' r dd_map dd exp_vals = Reader.runReader (evalExplicitDD dd_map dd exp_vals) r

andDDsToExpr :: (BuildDD dd,Monad m) => AndDDs dd -> DDM m Pexpr
andDDsToExpr (AndDDs dds) = liftM (Peopn Pand) $ mapM ddToExpr $ Map.elems dds

instance Monad m => DD.BDDMonad (ReaderT DDReader m) where
    bdd_ids = Reader.asks (IntMap.keysSet . varNames)

instance Monad m => DD.GIDDMonad (ReaderT DDReader m) where
    gidd_sizes = Reader.asks (IntMap.map toInts . varSizes)
        where
        toInts (VInt is) = is
        toInts VBool = IntSet.fromList [0,1]

proxyDDM :: Proxy m -> Proxy (DDM m)
proxyDDM _ = Proxy

instance Monad m => DDs.TreeDDsMonad (ReaderT DDReader m) where
    maxTreeDDsSize = Reader.asks maxDDSize
    
chooseDD :: Bool -> (forall dd . BuildDD dd => Proxy dd -> res) -> res
chooseDD doBoolean go = if doBoolean then go (Proxy :: Proxy BDD.BDD) else go (Proxy :: Proxy DD.GIDD)