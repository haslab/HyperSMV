-- | Builds decision diagrams from the 'Bexpr' IR.
module Transform.DD.Build where

import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
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
import Control.DeepSeq (NFData)
import Data.List as List
import GHC.Generics
import Data.Proxy
import Data.Hashable
import Prettyprinter

import Utils
import Pretty
import Smv.Typing
import Smv.Syntax
import Smv.Packed
import qualified Data.IDD as IDD
import Data.BDD (BDD)
import qualified Data.BDD as BDD
import Data.DD (DD(..))
import qualified Data.DD as DD
import Data.DDs (DDstructure,AndDDs(..),NextDDs(..))
import qualified Data.DDs as DDs
import Transform.Bexpr
import Transform.Pexpr

-- | Runs a DD computation with extra variables in scope.
extendDDM :: Monad m => Map DualPident VarType -> DDM m a -> DDM m a
extendDDM exts m = Reader.local withDDReader m
    where
    withDDReader :: DDReader -> DDReader
    withDDReader (DDReader names ids szs _ acc) = DDReader names' (flipIntMap names') szs' (mkConvTables szs') acc
        where
        next = succ $ fst $ IntMap.findMax names
        extnames = IntMap.fromList $ zip [next..] (Map.keys exts)
        names' = IntMap.union names extnames
        extszs = IntMap.fromList $ zip [next..] (Map.elems exts)
        szs' = IntMap.union szs extszs

-- | Runs a DD computation with variables filtered/renamed.
withDDM :: Monad m => (DualPident -> Maybe DualPident) -> DDM m a -> DDM m a
withDDM p m = Reader.local withDDReader m
    where
    withDDReader :: DDReader -> DDReader
    withDDReader (DDReader names ids szs _ acc) = DDReader names' (flipIntMap names') szs' (mkConvTables szs') acc
        where
        names' = (IntMap.mapMaybeWithKey (\k n -> p n) names)
        szs' = IntMap.intersection szs names'

-- | Environment for DD construction: variable names, ids, sizes.
data DDReader = DDReader { varNames :: IntMap DualPident, varIds :: Map DualPident Int, varSizes :: IntMap VarType, varTables :: ConvTables, varSupportAccept :: Integer }
    deriving (Eq,Ord,Show,Generic)
-- | Monad for DD construction, reading a 'DDReader'.
type DDM m = ReaderT DDReader m
-- | Cache of already-built DDs keyed by 'Bexpr'.
type DDState s = HashMap Bexpr s

instance Hashable DDReader

-- Prepared per-variable idx<->val conversion tables, derived from `varSizes` once per reader.
data Val2Idx = V2IIdentity | V2IMap !(IntMap Int)

-- | Prepared per-variable index/value conversion tables.
data ConvTables = ConvTables { ctIdx2Val :: IntMap (UV.Vector Int), ctVal2Idx :: IntMap Val2Idx }

instance Eq ConvTables where _ == _ = True
instance Ord ConvTables where compare _ _ = EQ
instance Show ConvTables where show _ = "<ConvTables>"
instance Hashable ConvTables where hashWithSalt s _ = s

-- | Builds 'ConvTables' from variable sizes.
mkConvTables :: IntMap VarType -> ConvTables
mkConvTables szs = ConvTables (IntMap.map i2v szs) (IntMap.map v2i szs)
    where
    valsOf VBool = [0,1]
    valsOf (VInt is) = IntSet.toAscList is
    i2v t = UV.fromList (valsOf t)
    v2i t = let vs = valsOf t in
        if List.and (zipWith (==) vs [0..])
            then V2IIdentity
            else V2IMap (IntMap.fromList (zip vs [0..]))

-- | Applies a value-to-index conversion.
applyVal2Idx :: Val2Idx -> Int -> Int
applyVal2Idx V2IIdentity v = v
applyVal2Idx (V2IMap m) v = unsafeIntLookupNote "applyVal2Idx" v m
{-# INLINE applyVal2Idx #-}

instance Monad m => DDs.NextDDsMonad (DDM m) where
    dd_nextIds = Reader.asks (IntMap.keysSet . IntMap.filter snd . varNames)
    dd_nexts = do
        nexts <- Reader.asks (IntMap.toList . IntMap.filter snd . varNames)
        liftM IntMap.fromList $ forM nexts $ \(next_i,(next_n,_)) -> do
            prev_i <- varId (next_n,False)
            return (next_i,prev_i)

-- | Variables and their types, in DD index order.
sortedTypes :: Monad m => DDM m [(DualPident,VarType)]
sortedTypes = do
    names <- Reader.asks varNames
    szs <- Reader.asks varSizes
    return $ map ((\i -> unsafeIntLookupNote "sortedTypes" i names) >< id) $ IntMap.toList szs

-- | Looks up a variable's type by DD index.
typeOf :: Monad m => Int -> DDM m VarType
typeOf i = Reader.asks (unsafeIntLookupNote "typeOf" i . varSizes)

-- | Variable types as a 'PackedPtypes'.
varPtypes :: Monad m => DDM m PackedPtypes
varPtypes = Reader.asks (\s -> mapWithKey fst exprOfVarType $ varIds s `composeMap` (fromIntMap $ varSizes s))

-- | Variable types keyed by 'Pident'.
varTypes :: Monad m => DDM m (Map Pident VarType)
varTypes = Reader.asks (\s -> mapWithKey fst id $ varIds s `composeMap` (fromIntMap $ varSizes s))

-- | Variable names, in DD index order.
sortedVars :: Monad m => DDM m [DualPident]
sortedVars = Reader.asks (IntMap.elems . varNames)

-- | Looks up a variable's DD index by name.
varId :: Monad m => DualPident -> DDM m Int
varId n = Reader.asks (\r -> fromJustNote ("varId " ++ prettyprint n ++ " " ++ show r) $ Map.lookup n $ varIds r)

-- | Looks up a variable's name by DD index.
varName :: Monad m => Int -> DDM m DualPident
varName i = Reader.asks (fromJustNote "varName" . IntMap.lookup i . varNames)

-- | Looks up a variable's type by name.
varSize :: Monad m => DualPident -> DDM m VarType
varSize n = Reader.asks (\s -> fromJustNote "varSize" $ Map.lookup n (varIds s) >>= \i -> IntMap.lookup i (varSizes s))

-- | An empty DD build cache.
newDDState :: DDState s
newDDState = HashMap.empty

-- The support-accept budget starts at this conservative default and is overridden per-backend.
unscopedSupportAccept :: Integer
unscopedSupportAccept = 2048

-- | Builds a 'DDReader' from a module's variables.
newDDReader :: PackedPvars -> Bool -> DDReader
newDDReader vars isDual = DDReader names ids sizes (mkConvTables sizes) unscopedSupportAccept
    where
    sides = if isDual then [False,True] else [False]
    allvars = [ ((n,side),toVarType t) | side <- sides, (n,t) <- Map.toList vars ]
    cmp ((n,side),t) = (Set.map NegString (dimsPident n),sizeOfVarType t,n,side)
    sorted = zip [0..] $ sortBy (\x y -> compare (cmp x) (cmp y)) allvars
    names = IntMap.fromList $ map (id >< fst) sorted
    ids = flipIntMap names
    sizes = IntMap.fromList $ map (id >< snd) sorted

-- | Runs a DD computation with a fresh 'DDReader'.
runDDM :: Monad m => PackedPvars -> Bool -> DDM m a -> m a
runDDM vars isDual m = Reader.runReaderT m (newDDReader vars isDual)

-- | Builds a DD structure from a 'Bexpr', caching subexpressions.
buildDDs :: (BuildDDs dd s) => Bexpr -> DDM IO s
buildDDs e = State.evalStateT (bexprToDDs e) newDDState
  where
    bexprToDDs :: (BuildDDs dd s) => Bexpr -> StateT (DDState s) (DDM IO) s
    bexprToDDs e = do
        h <- State.get
        case HashMap.lookup e h of
            Just i -> return i
            Nothing -> do
                i <- bexprToDDs' e
                State.modify $ \h -> HashMap.insert e i h
                return i

    bexprToDDs' :: (BuildDDs dd s) => Bexpr -> StateT (DDState s) (DDM IO) s
    bexprToDDs' (Bbool b) = lift $ DDs.singleton =<< DD.bool b
    bexprToDDs' (Bvar n VBool) = lift $ DDs.singleton =<< buildVarDD n VBool (Right True)
    bexprToDDs' (Bopn Pand es) = lift . DDs.ands =<< mapM bexprToDDs (HashSet.toList es)
    bexprToDDs' (Bopn Por es) = lift . DDs.ors =<< mapM bexprToDDs (HashSet.toList es)
    bexprToDDs' (Bop1 o e1) = bexprToDDs1 o e1
    bexprToDDs' (Bop2 o e1 e2) = bexprToDDs2 o e1 e2
    bexprToDDs' e = error $ "bexprToDDs': " ++ prettyprint e
    
    bexprToDDs1 :: (BuildDDs dd s) => Pop1 -> Bexpr -> StateT (DDState s) (DDM IO) s
    bexprToDDs1 Patom e1 = bexprToDDs e1
    bexprToDDs1 Pnot (Bvar n VBool) = lift $ DDs.singleton =<< buildVarDD n VBool (Right False)
    bexprToDDs1 Pnot e1 = lift . DDs.not =<< bexprToDDs e1
    bexprToDDs1 o e1 = error $ "bexprToDDs1: " ++ show o ++ " " ++ show e1
    
    bexprToDDs2 :: (BuildDDs dd s) => Pop2 -> Bexpr -> Bexpr -> StateT (DDState s) (DDM IO) s
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
    bexprToDDs2 Peq e1@(Bvar n1 t1) e2@(Bint i2) = lift $ DDs.singleton =<< buildVarDD n1 t1 (Left $ IntSet.singleton i2)
    bexprToDDs2 Peq e1@(Bint i1) e2@(Bvar n2 t2) = lift $ DDs.singleton =<< buildVarDD n2 t2 (Left $ IntSet.singleton i1)
    bexprToDDs2 Pin e1@(Bvar n1 t1) e2@(Bbool b2) = lift $ DDs.singleton =<< buildVarDD n1 t1 (Right b2)
    bexprToDDs2 Pin e1@(Bvar n1 t1) e2@(Bints is2) = lift $ DDs.singleton =<< buildVarDD n1 t1 (Left is2)
    bexprToDDs2 Pin e1 e2 | Prelude.not (isNonDetBexpr e2) = bexprToDDs2 Peq e1 e2
    bexprToDDs2 o@(isCmpOp2 -> True) e1 e2
        | Just e1' <- foldBArith e1 = bexprToDDs2 o e1' e2
        | Just e2' <- foldBArith e2 = bexprToDDs2 o e1 e2'
    bexprToDDs2 o@(isCmpOp2 -> True) e1 e2@(Bvar n2 t2) = do
        vs2 <- lift $ expandVar n2 t2
        bexprToDDs $ bors $ HashSet.map (\v2 -> Bop2 Pin e2 v2 `band` Bop2 o e1 v2) vs2    
    bexprToDDs2 o@(isCmpOp2 -> True) e1@(Bvar n1 t1) e2 = do
        vs1 <- lift $ expandVar n1 t1
        bexprToDDs $ bors $ HashSet.map (\v1 -> Bop2 Pin e1 v1 `band` Bop2 o v1 e2) vs1
    bexprToDDs2 o@(isCmpOp2 -> True) e1 e2 | Just ((n1,t1),rebuild) <- findVarInArith e1 = do
        vs1 <- lift $ expandVar n1 t1
        bexprToDDs $ bors $ HashSet.map (\v1 -> Bop2 Pin (Bvar n1 t1) v1 `band` Bop2 o (rebuild v1) e2) vs1
    bexprToDDs2 o@(isCmpOp2 -> True) e1 e2 | Just ((n2,t2),rebuild) <- findVarInArith e2 = do
        vs2 <- lift $ expandVar n2 t2
        bexprToDDs $ bors $ HashSet.map (\v2 -> Bop2 Pin (Bvar n2 t2) v2 `band` Bop2 o e1 (rebuild v2)) vs2
    bexprToDDs2 o e1 e2 = error $ "bexprToDDs2: " ++ show o ++ " " ++ show e1 ++ " " ++ show e2

-- | Bottom-up constant folding along the integer-arithmetic spine; 'Nothing' when nothing folded.
foldBArith :: Bexpr -> Maybe Bexpr
foldBArith e = let e' = go e in if e' == e then Nothing else Just e'
  where
    go (Bop2 o a b) | isArithOp2 o = case (go a,go b) of
        (Bint i,Bint j) -> Bint (arith o i j)
        (a',b')         -> Bop2 o a' b'
    go x = x
    arith Pplus  = (+)
    arith Pminus = (-)
    arith Ptimes = (*)
    arith o      = error $ "foldBArith: " ++ show o

-- | The leftmost variable reachable through integer arithmetic, with the context to rebuild the surrounding expression around a chosen value. 
findVarInArith :: Bexpr -> Maybe ((DualPident,VarType), Bexpr -> Bexpr)
findVarInArith (Bvar n t) = Just ((n,t), id)
findVarInArith (Bop2 o e1 e2) | isArithOp2 o =
    case findVarInArith e1 of
        Just (v,k) -> Just (v, \x -> Bop2 o (k x) e2)
        Nothing    -> fmap (\(v,k) -> (v, \x -> Bop2 o e1 (k x))) (findVarInArith e2)
findVarInArith _ = Nothing

-- | All values a variable can take, as 'Bexpr's.
expandVar :: Monad m => DualPident -> VarType -> DDM m (HashSet Bexpr)
expandVar n sz = do
    let vs = case sz of
            VInt is -> map Bint $ IntSet.toList is
            VBool -> [Bbool False,Bbool True]
    return $ HashSet.fromList vs

-- | Types convertible to/from a DD-structured 'Bexpr'/'Pexpr'.
class (Hashable s,DDstructure (DDM IO) dd s,BuildDD dd,Pretty s) => BuildDDs dd s | s -> dd where
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
    
    ddsToBexpr (DDs.NodeAndDDs dds) = liftM (Bopn Pand . HashSet.fromList) $ mapM (ddsToBexpr ) $ multiMapElems dds
    ddsToBexpr (DDs.NodeOrDDs dds) = liftM (Bopn Por . HashSet.fromList) $ mapM (ddsToBexpr ) $ multiMapElems dds
    ddsToBexpr (DDs.LeafDDs sup (dd)) = ddToBexpr dd
    
    ddsToExpr (DDs.NodeAndDDs dds) = liftM (Peopn Pand) $ mapM (ddsToExpr) $ multiMapElems dds
    ddsToExpr (DDs.NodeOrDDs dds) = liftM (Peopn Por) $ mapM (ddsToExpr ) $ multiMapElems dds
    ddsToExpr (DDs.LeafDDs sup (dd)) = ddToExpr dd
    
    ddsToConjunction (DDs.NodeAndDDs dds) = do
        dds' <- mapM (ddsToConjunction) $ multiMapElems dds
        return $ concat dds'
    ddsToConjunction (DDs.LeafDDs sup (dd)) = return [dd]
    ddsToConjunction dds = ioReader $ do
        dd <- DDs.flatten dds
        return [dd]

class (Hashable dd,DD (DDM IO) dd,Pretty dd,NFData dd,DD.DDNode dd) => BuildDD dd where
    buildVarDD :: Monad m => DualPident -> VarType -> Either IntSet Bool -> DDM m dd
    ddToBexpr :: Monad m => dd -> BM (DDM m) Bexpr
    ddToExpr :: Monad m => dd -> DDM m Pexpr
    ddToExpr dd = bmInDDM (ddToBexpr dd >>= fromBexpr)
   
instance Pretty DD.GIDD where
    pretty = prettyGIDD
   
instance BuildDD DD.GIDD where
     buildVarDD = buildVarGIDD
     ddToBexpr = giddToBexpr
     ddToExpr = giddToExpr

-- | Builds a GIDD for a variable's value(s).
buildVarGIDD :: (Monad m) => DualPident -> VarType -> Either IntSet Bool -> DDM m DD.GIDD
buildVarGIDD n ty vs = do
    ni <- varId n
    case vs of
        Left is -> DD.var' ni (Set.map DD.intToVal $ fromIntSet is)
        Right b -> DD.var ni (DD.boolToVal b)
    

-- | Pretty-prints a GIDD's branch structure.
prettyGIDD :: DD.GIDD -> Doc ann
prettyGIDD (DD.GIDD dd) = IDD.fold goBranch goLeaf dd
  where
    goLeaf :: Bool -> Doc ann
    goLeaf b = pretty b
    goBranch :: Int -> Vector (Doc ann) -> Doc ann
    goBranch ni cs = parens $ sepBy (pretty "|") $ V.toList (V.imap (\i str -> parens (pretty "v" <> pretty ni <+> pretty "=" <+> pretty "i" <> pretty i <+> pretty "&" <+> str)) cs)

-- | Converts a GIDD to a 'Pexpr'.
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

-- | Converts a GIDD to a 'Bexpr'.
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

instance Pretty BDD where
    pretty = prettyBDD

instance BuildDD BDD where
     buildVarDD = buildVarBDD
     ddToBexpr = bddToBexpr
     ddToExpr = bddToExpr


buildVarBDD :: (Monad m) => DualPident -> VarType -> Either IntSet Bool -> DDM m BDD
buildVarBDD n ty vs = do
    ni <- varId n
    case vs of
        Left _ -> error "buildVarBDD int"
        Right b -> DD.var ni (DD.boolToVal b)

-- | Pretty-prints a BDD's branch structure.
prettyBDD :: BDD -> Doc ann
prettyBDD dd = BDD.fold goBranch goLeaf dd
  where
    goLeaf :: Bool -> Doc ann
    goLeaf b = pretty b
    goBranch :: Int -> Doc ann -> Doc ann -> Doc ann
    goBranch ni lo hi = parens $
        parens (pretty "!v" <> pretty ni <+> pretty "&" <+> lo)
        <+> pretty "|" <+>
        parens (pretty "v" <> pretty ni <+> pretty "&" <+> hi)

-- | Converts a BDD to a 'Pexpr'.
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

-- | Converts a BDD to a 'Bexpr'.
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



-- | A 'BReader' derived from the current DD variables.
bReaderDDM :: Monad m => DDM m BReader
bReaderDDM = varTypes

-- | Runs a 'BM' computation inside 'DDM'.
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

-- | Evaluates a DD structure against an explicit-state assignment.
{-# INLINE evalExplicitDDs #-}
evalExplicitDDs :: (BuildDDs dd s,Monad m) => IntMap Int -> s -> DD.Vals dd -> DDM m Bool
evalExplicitDDs dd_map dds exp_vals = ioReader $ do
    r <- Reader.ask
    flip DDs.evaluate dds $ \dd_i ->
        let dd_n = Reader.runReader (varName dd_i) r
            exp_i = unsafeIntLookupNote ("evalDDs " ++ show dd_i ++ " " ++ prettyprint dd_n ++ " " ++ show dd_map) dd_i dd_map
        in uvIndex "evalDDs" exp_vals exp_i

-- | Pure form of 'evalExplicitDDs'.
evalExplicitDDs' :: BuildDDs dd s => DDReader -> IntMap Int -> s -> DD.Vals dd -> Bool
evalExplicitDDs' r dd_map dds st = Reader.runReader (evalExplicitDDs dd_map dds st) r

-- | Evaluates a DD against an explicit-state assignment.
{-# INLINE evalExplicitDD #-}
evalExplicitDD :: (BuildDD dd,Monad m) => IntMap Int -> dd -> DD.Vals dd -> DDM m Bool
evalExplicitDD dd_map dd exp_vals = ioReader $ flip DD.evaluate dd $ \dd_i -> 
    let Just exp_i = IntMap.lookup dd_i dd_map
    in uvIndex "evalDD" exp_vals exp_i

-- | Pure form of 'evalExplicitDD'.
evalExplicitDD' :: (BuildDD dd) => DDReader -> IntMap Int -> dd -> DD.Vals dd -> Bool
evalExplicitDD' r dd_map dd exp_vals = Reader.runReader (evalExplicitDD dd_map dd exp_vals) r

-- | Converts an 'AndDDs' to a 'Pexpr'.
andDDsToExpr :: (BuildDD dd,Monad m) => AndDDs dd -> DDM m Pexpr
andDDsToExpr (AndDDs dds) = liftM (Peopn Pand) $ mapM ddToExpr $ Map.elems dds

instance Monad m => DD.BDDMonad (ReaderT DDReader m) where
    bdd_ids = Reader.asks (IntMap.keysSet . varNames)

instance Monad m => DD.GIDDMonad (ReaderT DDReader m) where
    gidd_sizes = Reader.asks (IntMap.map toInts . varSizes)
        where
        toInts (VInt is) = is
        toInts VBool = IntSet.fromList [0,1]
    -- Prepared-table overrides (ConvTables)
    gidd_val2idx i = Reader.asks (\r ->
        let v2i = unsafeIntLookupNote "gidd_val2idx" i (ctVal2Idx (varTables r))
        in applyVal2Idx v2i)
    gidd_idx2val i = Reader.asks (\r ->
        let tbl = unsafeIntLookupNote "gidd_idx2val" i (ctIdx2Val (varTables r))
        in \idx -> tbl UV.! idx)
    gidd_vals2idxs is = Reader.asks (\r ->
        let v2is = ctVal2Idx (varTables r)
        in IntMap.mapWithKey (\i v -> applyVal2Idx (unsafeIntLookupNote "gidd_vals2idxs" i v2is) v) is)
    gidd_idxs2vals is = Reader.asks (\r ->
        let i2vs = ctIdx2Val (varTables r)
        in IntMap.mapWithKey (\i idx -> unsafeIntLookupNote "gidd_idxs2vals" i i2vs UV.! idx) is)
    gidd_vals2idxs' = Reader.asks (\r ->
        let v2is = ctVal2Idx (varTables r)
        in \dd_i -> applyVal2Idx (unsafeIntLookupNote "gidd_vals2idxs'" dd_i v2is))
    gidd_idxs2vals' = Reader.asks (\r ->
        let i2vs = ctIdx2Val (varTables r)
        in \dd_i idx -> unsafeIntLookupNote "gidd_idxs2vals'" dd_i i2vs UV.! idx)

-- | Lifts a monad proxy to a 'DDM' proxy.
proxyDDM :: Proxy m -> Proxy (DDM m)
proxyDDM _ = Proxy

-- | Run a DD computation under a specific support-accept budget.
withSupportAccept :: Monad m => Integer -> DDM m a -> DDM m a
withSupportAccept acc = Reader.local (\r -> r { varSupportAccept = acc })

instance Monad m => DDs.TreeDDsMonad (ReaderT DDReader m) where
    treeSupportAccept = Reader.asks varSupportAccept

    
-- | Pick the leaf DD backend of the hand-rolled DD library.
chooseDD :: Bool -> (forall dd . BuildDD dd => Proxy dd -> res) -> res
chooseDD doBoolean go
    | doBoolean             = go (Proxy :: Proxy BDD.BDD)
    | otherwise             = go (Proxy :: Proxy DD.GIDD)