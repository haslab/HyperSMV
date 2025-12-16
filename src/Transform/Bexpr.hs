module Transform.Bexpr
    (
      Bformula(..), toBformula, fromBformula
    , fromBformulaWith, fromBexprWith, fromBexpr, FromBexprRule(..), withoutFromBexprRule, noFromBexprRule, toBexpr
    , Bexpr (Bbool, Bints, Bint, Bvar, Bop1, Bop2, Bopn), nodeId, typeOfBexpr, isBoolBexpr, isSimpleBexpr
    , BM(..), BReader, doBMState, doBM, runBM, BState(..)
    , bvarSet, bvarsSet, bdualvarSet, bdualvarsSet, bdimSet, removeDimBexpr, isLTLBexpr, bexprTypes,  band, bor, bset, bopn
    , MapBexprRule(..), mapBexprWith, mapBexprWith', mapBformulaWith, mapBformula, quantsBformula, exprBformula, applyQuantsBexpr, applyQuantBformula
    , varsBformula, vbsetint, bands, bors, bnot, sizeBexpr, occurrencesBformula, occurrencesBexpr, bnext, isSingleDimBexpr, bvarCount, varTypeOfBexpr, vbvarin
    , normalizeBformula, normalizeBexpr, evaluateBexpr, isNonDetBexpr, unfoldBequiv
    , bf, bg
    ) where
    
import Data.Hashable
import Control.Monad.Identity
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (ReaderT(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.RWS.CPS (RWST(..))
import qualified Control.Monad.RWS.CPS as RWS
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Safe
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.Trans
import Data.Maybe
import GHC.Generics
import Prettyprinter
    
import Utils
import Pretty
import Smv.Pretty
import Smv.Syntax
import Smv.Packed
import Smv.Typing
import Transform.Pexpr
import Transform.Normalize
import qualified Transform.Bexpr.Internal as Internal

--import Debug.Trace

quantsBformula :: Bformula -> [(String,Quant)]
quantsBformula (Bforall n f) = (n,Qforall) : quantsBformula f
quantsBformula (Bexists n f) = (n,Qexists) : quantsBformula f
quantsBformula (Bltl e) = []

applyQuantsBexpr :: [(String,Quant)] -> Bexpr -> Bformula
applyQuantsBexpr [] e = Bltl e
applyQuantsBexpr (q:qs) e = applyQuantBformula q (applyQuantsBexpr qs e)
    
applyQuantBformula :: (String,Quant) -> Bformula -> Bformula
applyQuantBformula (n,Qforall) f = Bforall n f 
applyQuantBformula (n,Qexists) f = Bexists n f 

data Bformula
    = Bexists String Bformula
    | Bforall String Bformula
    | Bltl Bexpr
    deriving (Eq,Show,Generic)

instance Pretty Bformula where
    pretty f = pretty $ runIdentity $ doBM Map.empty $ fromBformula f

instance Hashable Bformula

exprBformula :: Bformula -> Bexpr
exprBformula (Bexists n f) = exprBformula f
exprBformula (Bforall n f) = exprBformula f
exprBformula (Bltl e) = e

mapBformula :: Monad m => MapBexprRule m -> Bformula -> m Bformula
mapBformula r (Bforall n f) = liftM (Bforall n) $ mapBformula r f
mapBformula r (Bexists n f) = liftM (Bexists n) $ mapBformula r f
mapBformula r (Bltl e) = liftM Bltl $ r e

mapBformulaWith :: MonadPlus m => MapBexprRule m -> Bformula -> m Bformula
mapBformulaWith r (Bforall n f) = liftM (Bforall n) $ mapBformulaWith r f
mapBformulaWith r (Bexists n f) = liftM (Bexists n) $ mapBformulaWith r f
mapBformulaWith r (Bltl e) = liftM Bltl $ mapBexprWith r e

toBformula :: Monad m => Pformula -> BM m Bformula
toBformula (Pfforall n f) = liftM (Bforall n) $ toBformula f
toBformula (Pfexists n f) = liftM (Bexists n) $ toBformula f
toBformula (Pfltl e) = liftM Bltl $ toBexpr e

fromBformula :: Monad m => Bformula -> BM m Pformula
fromBformula = withoutFromBexprRule fromBformulaWith

fromBformulaWith :: MonadPlus m => FromBexprRule m -> Bformula -> BM m Pformula
fromBformulaWith r (Bforall n f) = liftM (Pfforall n) $ fromBformulaWith r f
fromBformulaWith r (Bexists n f) = liftM (Pfexists n) $ fromBformulaWith r f
fromBformulaWith r (Bltl e) = liftM Pfltl $ fromBexprWith r e

-- simple bool expr
newtype Bexpr = Bexpr { unBexpr :: (Internal.Node) }
  deriving (Hashable)

instance Eq Bexpr where
    (==) = eqBexpr
  
eqBexpr :: Bexpr -> Bexpr -> Bool
eqBexpr e1 e2 = unBexpr e1 == unBexpr e2 || eqBexpr' e1 e2
    where
    eqBexpr' :: Bexpr -> Bexpr -> Bool
    eqBexpr' (Bbool b1) (Bbool b2) = b1 == b2
    eqBexpr' (Bints i1) (Bints i2) = i1 == i2
    eqBexpr' (Bvar n1 t1) (Bvar n2 t2) = n1 == n2 && t1 == t2
    eqBexpr' (Bop1 o1 e1) (Bop1 o2 e2) = o1 == o2 && eqBexpr e1 e2
    eqBexpr' (Bop2 o1 e11 e12) (Bop2 o2 e21 e22) = o1 == o2 && eqBexpr e11 e21 && eqBexpr e12 e22
    eqBexpr' (Bopn o1 es1) (Bopn o2 es2) = o1 == o2 && es1 == es2
    eqBexpr' _ _ = False

instance Show Bexpr where
    show (Bbool b) = "Bbool " ++ show b
    show (Bints i) = "Bints " ++ show i
    show (Bvar n t) = "(Bvar " ++ show n ++ " " ++ show t ++ ")"
    show (Bop1 o x) = "(Bop1 " ++ show o ++ " " ++ show x ++ ")" 
    show (Bop2 o x y) = "(Bop2 " ++ show o ++ " " ++ show x ++ " " ++ show y ++ ")" 
    show (Bopn o xs) = "(Bopn " ++ show o ++ " " ++ unwords (map show $ HashSet.toList xs) ++ ")"

instance Pretty Bexpr where
    pretty e = pretty $ runIdentity $ doBM Map.empty $ fromBexpr e

pattern Bbool :: Bool -> Bexpr
pattern Bbool b = Bexpr (Internal.Bbool b)

pattern Bints :: IntSet -> Bexpr
pattern Bints b = Bexpr (Internal.Bints b)

pattern Bint :: Int -> Bexpr
pattern Bint i <- Bexpr (Internal.Bints (isSingletonIntSet -> Just i)) where
    Bint i = Bexpr (Internal.Bints $ IntSet.singleton i)

pattern Bvar :: DualPident -> VarType -> Bexpr
pattern Bvar x t = Bexpr (Internal.Bvar x t)

pattern Bop1 :: Pop1 -> Bexpr -> Bexpr
pattern Bop1 o x <- Bexpr (Internal.Bop1 o (Bexpr -> x)) where
    Bop1 o (unBexpr -> x) = Bexpr (Internal.Bop1 o x)

pattern Bop2 :: Pop2 -> Bexpr -> Bexpr -> Bexpr
pattern Bop2 o x y <- Bexpr (Internal.Bop2 o (Bexpr -> x) (Bexpr -> y)) where
    Bop2 o (unBexpr -> x) (unBexpr -> y) = Bexpr (Internal.Bop2 o x y)

pattern Bopn :: Popn -> HashSet Bexpr -> Bexpr
pattern Bopn o bs <- Bexpr (Internal.Bopn o (HashSet.map Bexpr -> bs)) where
  Bopn o (HashSet.map unBexpr -> bs)
    | HashSet.size bs == 1 = Bexpr (head $ HashSet.toList bs)
    | otherwise = Bexpr (Internal.Bopn o bs)

{-# COMPLETE Bbool, Bints, Bvar, Bop1, Bop2, Bopn #-}

nodeId :: Bexpr -> Int
nodeId (Bexpr node) = Internal.nodeId node

type BReader = Map Pident VarType
type BState = (Map Pexpr Bexpr,HashMap Bexpr Pexpr)

type BM m = RWST BReader () BState m

{-# INLINE newBState #-}
newBState :: BState
newBState = (Map.empty,HashMap.empty)

doBMState :: Monad m => StateT BState m a -> m a
doBMState m = State.evalStateT m newBState

doBM :: Monad m => BReader -> BM m a -> m a
doBM r m = liftM fst $ runBM' r newBState m

{-# INLINE runBM #-}
runBM :: Monad m => BReader -> BM m a -> StateT BState m a
runBM vars m = do
    s <-State.get
    (a,s') <- lift $ runBM' vars s m
    State.put s'
    return a

{-# INLINE runBM' #-}
runBM' :: Monad m => BReader -> BState -> BM m a -> m (a,BState)
runBM' vars s m = do
    (a,s,_) <- RWS.runRWST m vars s
    return (a,s)

fromBexpr :: Monad m => Bexpr -> BM m Pexpr
fromBexpr = withoutFromBexprRule fromBexprWith

withoutFromBexprRule :: Monad m => (forall n . MonadPlus n => FromBexprRule n -> a -> BM n b) -> a -> BM m b
withoutFromBexprRule f e = RWS.mapRWST (liftM fromJust . runMaybeT) (f noFromBexprRule e)

type FromBexprRule m = Bexpr -> BM m Pexpr

noFromBexprRule :: Monad m => Bexpr -> BM (MaybeT m) Pexpr 
noFromBexprRule _ = lift $ hoistMaybe Nothing

fromBexprWith :: MonadPlus m => FromBexprRule m -> Bexpr -> BM m Pexpr
fromBexprWith r e = do
    h <- State.gets snd
    case HashMap.lookup e h of
        Just e' -> return e'
        Nothing -> r e `mplus` go e
  where
    go (Bbool b) = return $ Pebool b
    go (Bints i) = return $ psetint i
    go (Bvar (n,False) t) = return $ Peident n (exprOfVarType t)
    go (Bvar (n,True) t) = return $ pnext $ Peident n (exprOfVarType t)
    go (vbvarin -> Just ((n,isNext),VInt t,is)) = return $ (if isNext then pnext else id) $ mkOrIntExpr n is t
    go (Bop1 o e1) = liftM (peop1 o) $ fromBexprWith r e1
    go (Bop2 o e1 e2) = do
        e1' <- fromBexprWith r e1
        e2' <- fromBexprWith r e2
        return $ peop2 o e1' e2'
    go (Bopn o es) = do
        es' <- mapHashSetM (fromBexprWith r) es
        return $ peopn o $ HashSet.toList es'

sizeBexpr :: Bexpr -> Int
sizeBexpr e = State.evalState (recurse e) HashMap.empty
    where
    recurse, go :: Bexpr -> State (HashMap Bexpr Int) Int
    
    recurse e = do
        m <- State.get
        case HashMap.lookup e m of
            Just i -> return i
            Nothing -> go e

    go (Bbool b) = return 1
    go (Bints is) = return $ IntSet.size is
    go (Bvar n t) = return 1
    go (Bop1 o e1) = liftM succ (recurse e1)
    go (Bop2 o e1 e2) = liftM succ $ liftA2 (+) (recurse e1) (recurse e2)
    go (Bopn o es) = liftM (succ . sum) (mapM recurse $ HashSet.toList es)

type MapBexprRule m = Bexpr -> m Bexpr      

mapBexprWith :: MonadPlus m => MapBexprRule m -> Bexpr -> m Bexpr
mapBexprWith r e = State.evalStateT (mapBexprWith' r e) HashMap.empty

mapBexprWith' :: MonadPlus m => MapBexprRule m -> Bexpr -> StateT (HashMap Bexpr Bexpr) m Bexpr
mapBexprWith' r e = do
    h <- State.get
    case HashMap.lookup e h of
        Just e' -> return e'
        Nothing -> lift (r e) `mplus` go e
  where
    go (Bbool b) = return $ Bbool b
    go (Bints i) = return $ Bints i
    go (Bvar n t) = return $ Bvar n t
    go (Bop1 o e1) = liftM (Bop1 o) $ mapBexprWith' r e1
    go (Bop2 o e1 e2) = do
        e1' <- mapBexprWith' r e1
        e2' <- mapBexprWith' r e2
        return $ Bop2 o e1' e2'
    go (Bopn o es) = do
        es' <- mapHashSetM (mapBexprWith' r) es
        return $ Bopn o es'

toBexpr :: Monad m => Pexpr -> BM m Bexpr
toBexpr e = {-trace ("toBexpr: " ++ prettySMV Default (normalizeExpr e)) $-} coreToBexpr (normalizeExpr e)

coreToBexpr :: Monad m => Pexpr -> BM m Bexpr
coreToBexpr e = do
    h <- State.gets fst
    case Map.lookup e h of
        Just e' -> return e'
        Nothing -> do
            e' <- coreToBexpr' e
            State.modify (Map.insert e e' >< id)
            return e'
  where
    coreToBexpr' :: Monad m =>  Pexpr -> BM m Bexpr
    coreToBexpr' (Pebool b) = return $ Bbool b
    coreToBexpr' (vsetint -> Just i) = return $ Bints i
    coreToBexpr' (Peident n _) = do
        t <- Reader.asks (unsafeLookupNote ("coreToBexpr " ++ prettyPident n) n)
        return $ Bvar (n,False) t
    coreToBexpr' (Peop1 o e1) = coreToBexpr1 o e1
    coreToBexpr' (Peop2 o e1 e2) = coreToBexpr2 o e1 e2
    coreToBexpr' (Peopn o es) = coreToBexprn o $ HashSet.fromList es
    coreToBexpr' e = error $ "toBexpr: " ++ prettySMV Default e

coreToBexpr1 :: Monad m => Pop1 -> Pexpr -> BM m Bexpr
coreToBexpr1 Patom e = coreToBexpr e
coreToBexpr1 Pnext (Peident n _) = do
    t <- Reader.asks (unsafeLookupNote ("coreToBexpr1 " ++ prettyPident n) n)
    return $ Bvar (n,True) t
coreToBexpr1 o e1 = do
    e1' <- coreToBexpr e1
    return $ Bop1 o e1'

coreToBexpr2 :: Monad m => Pop2 -> Pexpr -> Pexpr -> BM m Bexpr
coreToBexpr2 o e1 e2 = do
    e1' <- coreToBexpr e1
    e2' <- coreToBexpr e2
    return $ Bop2 o e1' e2'

coreToBexprn :: Monad m => Popn -> HashSet Pexpr -> BM m Bexpr
coreToBexprn Pset es = liftM bset $ mapHashSetM coreToBexpr es
coreToBexprn Pand es = coreToBand =<< mapHashSetM coreToBexpr es
coreToBexprn Por es = coreToBor =<< mapHashSetM coreToBexpr es
    
type Bacc = Either Bool (HashSet Bexpr,Map DualPident (VarType,IntSet))

coreToBand :: Monad m => HashSet Bexpr -> BM m Bexpr
coreToBand xs = do
    r <- foldM (\acc e -> go acc e) (Left True) xs
    case r of
        Left b -> return $ Bbool b
        Right (xs,ys) -> liftM bands $ foldlWithKeyM (\acc v (t,is) -> return $ HashSet.insert (bvarin v t is) acc) xs ys
  where
    go :: Monad m => Bacc -> Bexpr -> BM m Bacc
    go acc (Bbool False) = return $ Left False
    go acc (Bbool True) = return acc
    go acc (Bopn Pand ys) = foldM go acc ys
    go acc (vbvarin -> Just (n,t,is)) = return $ insertbvar n t is acc
    go acc x = return $ insertbexpr x acc
    
    insertbexpr :: Bexpr -> Bacc -> Bacc
    insertbexpr e (Left True) = Right (HashSet.singleton e,Map.empty)
    insertbexpr e (Left False) = Left False
    insertbexpr e (Right (es,vs)) = Right (HashSet.insert e es,vs)
    
    insertbvar :: DualPident -> VarType -> IntSet -> Bacc -> Bacc
    insertbvar n t is (Left True) = Right (HashSet.empty,Map.singleton n (t,is))
    insertbvar n t is (Left False) = Left False
    insertbvar n t is (Right (es,vs)) = Right (es,Map.insertWith andVals n (t,is) vs)
    andVals (t,x) (_,y) = (t,IntSet.intersection x y)

coreToBor :: Monad m => HashSet Bexpr -> BM m Bexpr
coreToBor xs = do
    r <- foldM (\acc e -> go acc e) (Left False) xs
    case r of
        Left b -> return $ Bbool b
        Right (xs,ys) -> liftM bors $ foldlWithKeyM (\acc v (t,is) -> return $ HashSet.insert (bvarin v t is) acc) xs ys
  where
    go :: Monad m => Bacc -> Bexpr -> BM m Bacc
    go acc (Bbool True) = return $ Left True
    go acc (Bbool False) = return acc
    go acc (Bopn Por ys) = foldM go acc ys
    go acc (vbvarin -> Just (n,t,is)) = return $ insertbvar n t is acc
    go acc x = return $ insertbexpr x acc
    
    insertbexpr :: Bexpr -> Bacc -> Bacc
    insertbexpr e (Left False) = Right (HashSet.singleton e,Map.empty)
    insertbexpr e (Left True) = Left True
    insertbexpr e (Right (es,vs)) = Right (HashSet.insert e es,vs)
    
    insertbvar :: DualPident -> VarType -> IntSet -> Bacc -> Bacc
    insertbvar n t is (Left False) = Right (HashSet.empty,Map.singleton n (t,is))
    insertbvar n t is (Left True) = Left True
    insertbvar n t is (Right (es,vs)) = Right (es,Map.insertWith orVals n (t,is) vs)
    orVals (t,x) (_,y) = (t,IntSet.union x y)

bvarin :: DualPident -> VarType -> IntSet -> Bexpr
bvarin n t@(VInt ts) is
    | IntSet.null is = Bbool False
    | ts == is = Bbool True
    | otherwise = Bop2 Pin (Bvar n t) (Bints is)

vbvarin :: Bexpr -> Maybe (DualPident,VarType,IntSet)
vbvarin (Bop2 Pin (Bvar n t@(VInt sz)) (vbsetint -> Just is)) = Just (n,t,IntSet.intersection sz is)
vbvarin (Bop2 o (Bvar n t@(VInt sz)) (Bint i)) | isCmpOp2 o = Just (n,t,mkin o)
    where
    mkin Peq = IntSet.intersection (IntSet.singleton i) sz
    mkin Pneq = IntSet.delete i sz
    mkin Pgt = IntSet.filter (>i) sz
    mkin Pgeq = IntSet.filter (>=i) sz
    mkin Plt = IntSet.filter (<i) sz
    mkin Pleq = IntSet.filter (<=i) sz
vbvarin e = Nothing

typeOfBexpr :: Bexpr -> ExprType
typeOfBexpr (Bvar n t) = exprOfVarType t
typeOfBexpr (Bbool b) = EBool
typeOfBexpr (Bints i) = EInt
typeOfBexpr (Bop1 o e1) = typeOfPop1 o (typeOfBexpr e1)
typeOfBexpr (Bop2 o e1 e2) = typeOfPop2 o (typeOfBexpr e1) (typeOfBexpr e2)
typeOfBexpr (Bopn Pand es) = EBool
typeOfBexpr (Bopn Por es) = EBool
typeOfBexpr (Bopn Pset (isConsHashSet -> Just (e,es))) = typeOfBexpr e

varTypeOfBexpr :: Bexpr -> VarType
varTypeOfBexpr (Bvar n t) = t
varTypeOfBexpr (Bbool b) = VBool
varTypeOfBexpr (Bints is) = VInt is
varTypeOfBexpr (Bop1 o e1) = varTypeOfPop1 o (varTypeOfBexpr e1)
varTypeOfBexpr (Bop2 o e1 e2) = varTypeOfPop2 o (varTypeOfBexpr e1) (varTypeOfBexpr e2)
varTypeOfBexpr (Bopn Pand es) = VBool
varTypeOfBexpr (Bopn Por es) = VBool
varTypeOfBexpr (Bopn Pset (HashSet.null -> True)) = error $ "varTypeOfBexpr: empty set"
varTypeOfBexpr (Bopn Pset es) = foldl1 unionVarType (HashSet.map varTypeOfBexpr es)

isBoolBexpr :: Bexpr -> Bool
isBoolBexpr e = typeOfBexpr e == EBool

isSimpleBexpr :: Bexpr -> Bool
isSimpleBexpr (Bbool {}) = True
isSimpleBexpr (Bints {}) = True
isSimpleBexpr (Bvar {}) = True
isSimpleBexpr e = False

bvarCount :: Bexpr -> Int
bvarCount (Bvar n _) = 1
bvarCount (Bbool {}) = 0
bvarCount (Bints {}) = 0
bvarCount (Bop1 o e1) = bvarCount e1
bvarCount (Bop2 o e1 e2) = bvarCount e1 + bvarCount e2
bvarCount (Bopn o es) = sum $ map bvarCount $ HashSet.toList es

varsBformula :: Bformula -> Set Pident
varsBformula (Bforall n f) = varsBformula f
varsBformula (Bexists n f) = varsBformula f
varsBformula (Bltl e) = bvarSet e

bvarSet :: Bexpr -> Set Pident
bvarSet = Set.map fst . bdualvarSet

bdualvarSet :: Bexpr -> Set DualPident
bdualvarSet (Bvar n _) = Set.singleton n
bdualvarSet (Bbool {}) = Set.empty
bdualvarSet (Bints {}) = Set.empty
bdualvarSet (Bop1 o e1) = bdualvarSet e1
bdualvarSet (Bop2 o e1 e2) = bdualvarSet e1 `Set.union` bdualvarSet e2
bdualvarSet (Bopn o es) = Set.unions $ HashSet.map bdualvarSet es

bvarsSet :: HashSet Bexpr -> Set Pident
bvarsSet = Set.map fst . bdualvarsSet

bdualvarsSet :: HashSet Bexpr -> Set DualPident
bdualvarsSet es = Set.unions $ map bdualvarSet $ HashSet.toList es

bdimSet :: Bexpr -> Set String
bdimSet (Bbool {}) = Set.empty
bdimSet (Bints {}) = Set.empty
bdimSet (Bvar (n,_) t) = dimsPident n
bdimSet (Bop1 o e1) = bdimSet e1
bdimSet (Bop2 o e1 e2) = bdimSet e1 `Set.union` bdimSet e2
bdimSet (Bopn o es) = Set.unions $ map bdimSet $ HashSet.toList es

removeDimBexpr :: Bexpr -> Bexpr
removeDimBexpr e@(Bbool {}) = e
removeDimBexpr e@(Bints {}) = e
removeDimBexpr (Bvar (n,isNext) v) = Bvar (removeDimPident n,isNext) v
removeDimBexpr (Bop1 o e1) = Bop1 o (removeDimBexpr e1)
removeDimBexpr (Bop2 o e1 e2) = Bop2 o (removeDimBexpr e1) (removeDimBexpr e2)
removeDimBexpr (Bopn o es) = Bopn o $ HashSet.map removeDimBexpr es

isLTLBexpr :: Bexpr -> Bool
isLTLBexpr (Bbool {}) = False
isLTLBexpr (Bints {}) = False
isLTLBexpr (Bvar {}) = False
isLTLBexpr (Bop1 o e1) = isLTLOp1 o || isLTLBexpr e1
isLTLBexpr (Bop2 o e1 e2) = isLTLOp2 o || isLTLBexpr e1 || isLTLBexpr e2
isLTLBexpr (Bopn o es) = or $ map isLTLBexpr (HashSet.toList es)

bexprTypes :: Bexpr -> BReader
bexprTypes (Bbool {}) = Map.empty
bexprTypes (Bints {}) = Map.empty
bexprTypes (Bvar n t) = Map.singleton (fst n) t
bexprTypes (Bop1 o e1) = bexprTypes e1
bexprTypes (Bop2 o e1 e2) = bexprTypes e1 `Map.union` bexprTypes e2
bexprTypes (Bopn o es) = Map.unions $ map bexprTypes $ HashSet.toList es

bands :: HashSet Bexpr -> Bexpr
bands = bands' [] . HashSet.toList

bands' :: [Bexpr] -> [Bexpr] -> Bexpr
bands' [] [] = Bbool True
bands' [y] [] = y
bands' acc [] = Bopn Pand $ HashSet.fromList acc
bands' acc ((Bopn Pand es1) : es2) = bands' acc (HashSet.toList es1 ++ es2)
bands' acc (e : es) = case e of
    ((==Bbool True) -> True) -> bands' acc es
    ((==Bbool False) -> True) -> Bbool False
    otherwise -> bands' (e : acc) es

bors :: HashSet Bexpr -> Bexpr
bors = bors' [] . HashSet.toList

bors' :: [Bexpr] -> [Bexpr] -> Bexpr
bors' [] [] = Bbool False
bors' [y] [] = y
bors' acc [] = Bopn Por $ HashSet.fromList acc
bors' acc ((Bopn Por es1) : es2) = bors' acc (HashSet.toList es1 ++ es2)
bors' acc (e : es) = case e of
    ((==Bbool False) -> True) -> bors' acc es
    ((==Bbool True) -> True) -> Bbool True
    otherwise -> bors' (e : acc) es

bset :: HashSet Bexpr -> Bexpr
bset (isSingletonHashSet -> Just e) = e
bset es = case mapHashSetM vbsetint es of
    Just is -> Bints $ IntSet.unions is
    Nothing -> Bopn Pset es

bopn :: Popn -> HashSet Bexpr -> Bexpr
bopn Pand = bands
bopn Por = bors
bopn Pset = bset

vbsetint :: Bexpr -> Maybe IntSet
vbsetint (Bints i) = Just i
vbsetint (Bopn Pset es) = liftM IntSet.unions $ mapM vbsetint $ HashSet.toList es
vbsetint (Bop2 Punion e1 e2) = do
    is1 <- vbsetint e1
    is2 <- vbsetint e2
    return $ IntSet.union is1 is2
vbsetint e = Nothing

band :: Bexpr -> Bexpr -> Bexpr
band e1 e2 = bands $ HashSet.fromList [e1,e2]

bor :: Bexpr -> Bexpr -> Bexpr
bor e1 e2 = bors $ HashSet.fromList [e1,e2]

bnot :: Bexpr -> Bexpr
bnot (Bbool b) = Bbool (not b)
bnot (Bopn Por es) = Bopn Pand $ HashSet.map bnot es
bnot (Bopn Pand es) = Bopn Por $ HashSet.map bnot es
bnot (Bop1 Pnot e1) = e1
bnot (Bop2 o@(isCmpOp2 -> True) e1 e2) = Bop2 (negCmpOp2 o) e1 e2
bnot (Bop2 Pin v@(Bvar n (VInt ts)) (Bints is)) = Bop2 Pin v (Bints $ IntSet.difference ts is)
bnot (Bop2 Pequiv e1 e2) = band e1 (bnot e2) `bor` band (bnot e1) e2
bnot (Bop2 Pimplies e1 e2) = band e1 (bnot e2)
bnot e@(Bvar n t) = Bop1 Pnot e
bnot (Bop1 Pg e1) = Bop1 Pf $ bnot e1
bnot (Bop1 Pf e1) = Bop1 Pg $ bnot e1
bnot (Bop1 Px e1) = Bop1 Px $ bnot e1
bnot e = error $ "bnot: " ++ show e    

occurrencesBformula :: Bformula -> Map DualPident Int
occurrencesBformula (Bforall n f) = occurrencesBformula f
occurrencesBformula (Bexists n f) = occurrencesBformula f
occurrencesBformula (Bltl e) = occurrencesBexpr e

occurrencesBexpr :: Bexpr -> Map DualPident Int
occurrencesBexpr (Bbool {}) = Map.empty
occurrencesBexpr (Bints {}) = Map.empty
occurrencesBexpr (Bvar n t) = Map.singleton n 1
occurrencesBexpr (Bop1 o e1) = occurrencesBexpr e1
occurrencesBexpr (Bop2 o e1 e2) = Map.unionWith (+) (occurrencesBexpr e1) (occurrencesBexpr e2)
occurrencesBexpr (Bopn o es) = Map.unionsWith (+) $ map occurrencesBexpr $ HashSet.toList es

bnext :: Bexpr -> Bexpr
bnext e@(Bbool {}) = e
bnext e@(Bints {}) = e
bnext (Bvar (n,_) t) = Bvar (n,True) t
bnext (Bop1 o e1) = Bop1 o (bnext e1)
bnext (Bop2 o e1 e2) = Bop2 o (bnext e1) (bnext e2)
bnext (Bopn o es) = Bopn o (HashSet.map bnext es)

isSingleDimBexpr :: Bexpr -> Maybe String
isSingleDimBexpr e = maybe Nothing maybeFromSet (go e)
    where
    go :: Bexpr -> Maybe (Set String)
    go (Bbool {}) = return Set.empty
    go (Bints {}) = return Set.empty
    go (Bvar (n,_) t) = fmap Set.singleton $ isSingleDimPident n
    go (Bop1 o e1) = go e1
    go (Bop2 o e1 e2) = liftA2 Set.union (go e1) (go e2)
    go (Bopn o es) = liftM Set.unions (mapHashSetM go es)

instance Semigroup Bexpr where
    x <> y = bor x y

instance Monoid Bexpr where
    mempty = Bbool True
    mappend x y = bor x y

normalizeBformula :: Bformula -> Bformula
normalizeBformula (Bforall n f) = Bforall n (normalizeBformula f)
normalizeBformula (Bexists n f) = Bexists n (normalizeBformula f)
normalizeBformula (Bltl e) = Bltl (normalizeBexpr e)

normalizeBexpr :: Bexpr -> Bexpr
normalizeBexpr = outermostBexpr . evaluateBexpr . nnfBexpr

outermostBexpr :: Bexpr -> Bexpr
outermostBexpr (Bopn Pand (mapHashSetM vbx -> Just es)) = Bop1 Px $ outermostBexpr $ Bopn Pand es
outermostBexpr (Bopn Por (mapHashSetM vbx -> Just es)) = Bop1 Px $ outermostBexpr $ Bopn Por es
outermostBexpr (Bopn Pand (mapHashSetM vbg -> Just es)) = Bop1 Pg $ outermostBexpr $ Bopn Pand es
outermostBexpr (Bopn Por (mapHashSetM vbf -> Just es)) = Bop1 Pf $ outermostBexpr $ Bopn Por es
outermostBexpr (Bop1 o e1) = Bop1 o (outermostBexpr e1)
outermostBexpr (Bop2 o e1 e2) = Bop2 o (outermostBexpr e1) (outermostBexpr e2)
outermostBexpr (Bopn o es) = Bopn o (HashSet.map outermostBexpr es)
outermostBexpr e = e

unfoldBexpr :: Bexpr -> Bexpr
unfoldBexpr (Bop1 o e1) = Bop1 o (unfoldBexpr e1)
unfoldBexpr (Bop2 Pequiv e1 e2) = unfoldBexpr $ unfoldBequiv e1 e2
unfoldBexpr (Bop2 Pimplies e1 e2) = unfoldBexpr $ bnot e1 `bor` e2
unfoldBexpr (Bop2 o e1 e2) = Bop2 o (unfoldBexpr e1) (unfoldBexpr e2)
unfoldBexpr (Bopn o es) = Bopn o (HashSet.map unfoldBexpr es)
unfoldBexpr e = e

unfoldBequiv :: Bexpr -> Bexpr -> Bexpr
unfoldBequiv e1 e2 = band e1 e2 `bor` band (bnot e1) (bnot e2)

vbx :: Bexpr -> Maybe Bexpr
vbx (Bop1 Px e) = Just e
vbx e | not (isLTLBexpr e) && Set.null (bvarSet e) = Just e
vbx e = Nothing

vbg :: Bexpr -> Maybe Bexpr
vbg (Bop1 Pg e) = Just e
vbg e = Nothing

vbf :: Bexpr -> Maybe Bexpr
vbf (Bop1 Pf e) = Just e
vbf e = Nothing

evaluateBexpr :: Bexpr -> Bexpr
evaluateBexpr (Bop1 o e1) = case (o,evaluateBexpr e1) of
    (Pnot,Bbool b) -> Bbool (not b)
    (o,e1) -> Bop1 o e1
evaluateBexpr (Bop2 o e1 e2) = case (o,evaluateBexpr e1,evaluateBexpr e2) of
    (Pimplies,e1,Bbool False) -> evaluateBexpr (nnfBexpr $ Bop1 Pnot e1)
    (Pimplies,e1,Bbool True) -> Bbool True
    (Peq,Bbool b1,Bbool b2) -> Bbool (b1==b2) 
    (Peq,Bint i1,Bint i2) -> Bbool (i1==i2) 
    (Pneq,Bbool b1,Bbool b2) -> Bbool (b1/=b2) 
    (Pneq,Bint i1,Bint i2) -> Bbool (i1/=i2) 
    (Plt,Bint i1,Bint i2) -> Bbool (i1<i2) 
    (Pleq,Bint i1,Bint i2) -> Bbool (i1<=i2) 
    (Pgt,Bint i1,Bint i2) -> Bbool (i1>i2) 
    (Pgeq,Bint i1,Bint i2) -> Bbool (i1>=i2)
    (Peq,e1@(isBoolBexpr -> True),e2@(isBoolBexpr -> True)) -> evaluateBexpr (Bop2 Pequiv e1 e2)
    (Pequiv,Bbool True,e2) -> e2
    (Pequiv,Bbool False,e2) -> evaluateBexpr (nnfBexpr $ Bop1 Pnot e2)
    (Pequiv,e1,Bbool True) -> e1
    (Pequiv,e1,Bbool False) -> evaluateBexpr (nnfBexpr $ Bop1 Pnot e1)    
    (Pin,Bints is1,Bints is2) -> Bbool (IntSet.isSubsetOf is1 is2)
    (o,e1,e2) -> Bop2 o e1 e2
evaluateBexpr (Bopn o es) = bopn o (HashSet.map evaluateBexpr es)
evaluateBexpr e = e

nnfBexpr :: Bexpr -> Bexpr
nnfBexpr (Bop1 Pnot e1) = case e1 of
    (Bopn Pand es) -> nnfBexpr $ Bopn Por $ HashSet.map (Bop1 Pnot) es
    (Bopn Por es) -> nnfBexpr $ Bopn Pand $ HashSet.map (Bop1 Pnot) es
    (Bop1 Pnot e) -> e
    (Bop2 o@(isCmpOp2 -> True) e1 e2) -> nnfBexpr $ Bop2 (negCmpOp2 o) e1 e2
    (Bbool b) -> Bbool (not b)
    otherwise -> Bop1 Pnot e1
nnfBexpr (Bop2 Pin e1 e2) | isBoolBexpr e1 && Prelude.not (isNonDetBexpr e2) = nnfBexpr $ Bop2 Pequiv e1 e2
nnfBexpr (Bop2 Pin e1 e2) | Prelude.not (isNonDetBexpr e2) = nnfBexpr $ Bop2 Peq e1 e2
nnfBexpr (Bop2 o e1 e2) = Bop2 o (nnfBexpr e1) (nnfBexpr e2)
nnfBexpr (Bopn o es) = Bopn o (HashSet.map nnfBexpr es) 
nnfBexpr e = e

isNonDetBexpr :: Bexpr -> Bool
isNonDetBexpr (Bbool {}) = False
isNonDetBexpr (Bint {}) = False
isNonDetBexpr (Bints {}) = True
isNonDetBexpr (Bvar {}) = False -- we assume that defined variables cannot be sets
isNonDetBexpr (Bop1 o e1) = isNonDetBexpr e1
isNonDetBexpr (Bop2 Punion e1 e2) = True
isNonDetBexpr (Bop2 Pin e1 e2) = isNonDetBexpr e1 -- we don't care that there is non-determinism in the right side, since the result is a bool
isNonDetBexpr (Bop2 o e1 e2) = isNonDetBexpr e1 || isNonDetBexpr e2
isNonDetBexpr (Bopn Pset es) = HashSet.size es /= 1
isNonDetBexpr (Bopn o es) = any isNonDetBexpr es

bf :: Bexpr -> Bexpr
bf (Bbool b) = Bbool b
bf e = Bop1 Pf e

bg :: Bexpr -> Bexpr
bg (Bbool b) = Bbool b
bg e = Bop1 Pg e

