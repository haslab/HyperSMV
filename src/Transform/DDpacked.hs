module Transform.DDpacked where

import qualified Control.Monad.Reader as Reader
import qualified Data.Map as Map
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.Proxy
import Control.Monad
import Data.Hashable
import GHC.Generics
import Control.Monad.Identity
import Control.Monad.IO.Class

import Pretty
import Smv.Packed
import Smv.Syntax
import Transform.Bexpr
import Transform.Bpacked
import Transform.DDs
import Data.DDs as DDs
import Utils

--import Debug.Trace

data DDltl s dd
    = DDand (HashSet (DDltl s dd))
    | DDor (HashSet (DDltl s dd))
    | DDnot (DDltl s dd)
    | DDop1 Pop1 (DDltl s dd)
    | DDop2 Pop2 (DDltl s dd) (DDltl s dd)
    | DDexpr s
    deriving (Eq,Show,Generic)
    
instance (Hashable s,Hashable dd) => Hashable (DDltl s dd)

isTemporalDDltl :: DDltl s dd -> Bool
isTemporalDDltl (DDop1 {}) = True
isTemporalDDltl (DDop2 {}) = True
isTemporalDDltl _ = False

data PackedDDmodule sinit sinvar strans sltl dd = PackedDDmodule
    { dd_name    :: String
    , dd_vars    :: PackedBvars
    , dd_init    :: sinit
    , dd_invar   :: sinvar
    , dd_trans   :: strans
    , dd_ltlspec :: Maybe (DDltl sltl dd)
    } deriving (Eq,Show)

ddltlToBexpr :: (BuildDDs dd s,Monad m) => DDltl s dd -> BM (DDM m) Bexpr
ddltlToBexpr (DDand es) = liftM (Bopn Pand) $ mapHashSetM ddltlToBexpr es    
ddltlToBexpr (DDor es) = liftM (Bopn Por) $ mapHashSetM ddltlToBexpr es 
ddltlToBexpr (DDnot e1) = liftM (Bop1 Pnot) $ ddltlToBexpr e1
ddltlToBexpr (DDop1 o e1) = liftM (Bop1 o) $ ddltlToBexpr e1
ddltlToBexpr (DDop2 o e1 e2) = do
    e1' <- ddltlToBexpr e1
    e2' <- ddltlToBexpr e2
    return (Bop2 o e1' e2')
ddltlToBexpr (DDexpr dds) = ddsToBexpr dds

ddltlToExpr :: (BuildDDs dd s,Monad m) => DDltl s dd -> DDM m Pexpr
ddltlToExpr = ddltlToExprWith ddsToExpr

ddltlToExprWith :: (BuildDDs dd s,Monad m) => (s -> DDM m Pexpr) -> DDltl s dd -> DDM m Pexpr
ddltlToExprWith f (DDand es) = liftM (Peopn Pand) $ mapM (ddltlToExprWith f) $ HashSet.toList es
ddltlToExprWith f (DDor es) = liftM (Peopn Por) $ mapM (ddltlToExprWith f) $ HashSet.toList es
ddltlToExprWith f (DDnot e1) = liftM (Peop1 Pnot) $ ddltlToExprWith f e1
ddltlToExprWith f (DDop1 o e1) = liftM (Peop1 o) $ ddltlToExprWith f e1
ddltlToExprWith f (DDop2 o e1 e2) = do
    e1' <- ddltlToExprWith f e1
    e2' <- ddltlToExprWith f e2
    return $ Peop2 o e1' e2'
ddltlToExprWith f (DDexpr dds) = f dds

buildDDltlProxy :: (BuildDDs dd s,Monad m) => Proxy dd -> Bexpr -> DDM m (DDltl s dd)
buildDDltlProxy _ = buildDDltl

buildDDltl :: (BuildDDs dd s,Monad m) => Bexpr -> DDM m (DDltl s dd)
buildDDltl e | Prelude.not (isLTLBexpr e) = do
    res <- {-trace ("build " ++ prettyprint e) $-} liftM DDexpr (buildDDs e)
    --trace ("built " ++ show res) $
    return res
buildDDltl (Bopn Pand es) = liftM DDand $ mapHashSetM buildDDltl es
buildDDltl (Bopn Por es) = liftM DDor $ mapHashSetM buildDDltl es
buildDDltl (Bop1 Pnot e1) = liftM DDnot $ buildDDltl e1
buildDDltl (Bop1 o e1) | isLTLOp1 o = liftM (DDop1 o) $ buildDDltl e1
buildDDltl (Bop2 Pequiv e1 e2) = buildDDltl $ unfoldBequiv e1 e2
buildDDltl (Bop2 o e1 e2) | isLTLOp2 o = do
    e1' <- buildDDltl e1
    e2' <- buildDDltl e2
    return (DDop2 o e1' e2')
buildDDltl e = error $ "buildDDltl: unsupported " ++ show e 

withPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => Integer -> PackedBmodule -> (PackedDDmodule s1 s2 s3 s4 dd -> DDM m res) -> m res
withPackedDDmodule maxSize p go = do
    let vars = b_vars p
    runDDM vars True maxSize $ do
        dd <- toPackedDDmodule p
        go dd

withPackedDDmoduleProxy :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => Proxy s1 -> Proxy s2 -> Proxy s3 -> Proxy s4 -> Integer -> PackedBmodule -> (PackedDDmodule s1 s2 s3 s4 dd -> DDM m res) -> m res
withPackedDDmoduleProxy s1 s2 s3 s4 = withPackedDDmodule

toPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => PackedBmodule -> DDM m (PackedDDmodule s1 s2 s3 s4 dd)
toPackedDDmodule p = do
        let name = b_name p
        let vars = b_vars p
--        names <- Reader.asks varNames
        initDD <- {-trace (show names ++ " DD")-} buildDDs (b_init p)
        invarDD <- {-trace (show initDD ++ " initDD\n" {- ++ prettyprint (b_trans p) ++ " trans\n"-}) $-} buildDDs (b_invar p)
        transDD <- {-trace (show invarDD ++ " invarDD\n" ) $-} buildDDs (b_trans p)
        ltlDD <- {-trace (show invarDD ++ " invarDD\n" ) $-} mapM buildDDltl (b_ltlspec p)
        let dd = PackedDDmodule name vars initDD invarDD transDD ltlDD
        --trace ((unlines $ map (\(x,y) -> show x ++ ": " ++ show y) $ Map.toList $ unNextDDs transDD) ++ " transDD\n") $
        return dd

fromPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => PackedDDmodule s1 s2 s3 s4 dd -> DDM m PackedBmodule
fromPackedDDmodule (PackedDDmodule name vars init invar trans ltl) = bmInDDM $ do
    init'  <- ddsToBexpr init
    invar' <- ddsToBexpr invar
    trans' <- ddsToBexpr trans
    ltl' <- mapM ddltlToBexpr ltl
    return (PackedBmodule name vars Map.empty init' invar' trans' ltl')
    
fromPackedDDmoduleProxy :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => Proxy dd -> PackedDDmodule s1 s2 s3 s4 dd -> DDM m PackedBmodule
fromPackedDDmoduleProxy dd = fromPackedDDmodule

--viaPackedDDmodule :: (BuildDD dd,Monad m) => Proxy dd -> PackedBmodule -> m PackedBmodule
--viaPackedDDmodule dd pb = withPackedDDmodule pb (fromPackedDDmoduleProxy dd)

renderPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => PackedDDmodule s1 s2 s3 s4 dd -> DDM m PackedPmodule
renderPackedDDmodule (PackedDDmodule name vars init invar trans ltl) = do
    init'  <- ddsToExpr init
    invar' <- ddsToExpr invar
    trans' <- ddsToExpr trans
    ltl' <- mapM ddltlToExpr ltl
    return (PackedPmodule name vars Map.empty init' invar' trans' noPackedPassigns ltl')

renderPackedDDmoduleProxy :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => Proxy s1 -> Proxy s2 -> Proxy s3 -> Proxy s4 -> Proxy dd -> PackedDDmodule s1 s2 s3 s4 dd -> DDM m PackedPmodule
renderPackedDDmoduleProxy s1 s2 s3 s4 dd = renderPackedDDmodule

--renderViaPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => Proxy s1 -> Proxy s2 -> Proxy s3 -> Proxy s4 -> Proxy dd -> Integer -> PackedBmodule -> m PackedPmodule
--renderViaPackedDDmodule s1 s2 s3 s4 dd maxSize pb = withPackedDDmodule maxSize pb (renderPackedDDmoduleProxy s1 s2 s3 s4 dd)






