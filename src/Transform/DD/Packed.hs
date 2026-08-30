-- | A packed multi-DD bundle for one module's init/invar/trans/LTL.
module Transform.DD.Packed where

import qualified Data.Map as Map
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.Proxy
import Control.Monad
import Data.Hashable
import GHC.Generics

import Smv.Packed
import Smv.Syntax
import Transform.Bexpr
import Transform.Bexpr.Packed
import Transform.DD.Build
import Utils

-- | LTL formula tree over DD-backed leaves.
data DDltl s dd
    = DDand (HashSet (DDltl s dd))
    | DDor (HashSet (DDltl s dd))
    | DDnot (DDltl s dd)
    | DDop1 Pop1 (DDltl s dd)
    | DDop2 Pop2 (DDltl s dd) (DDltl s dd)
    | DDexpr s
    deriving (Eq,Show,Generic)
    
instance (Hashable s,Hashable dd) => Hashable (DDltl s dd)

-- | Does this formula declare its own atomic propositions?
hasAtomDDltl :: DDltl s dd -> Bool
hasAtomDDltl (DDop1 Patom _) = True
hasAtomDDltl (DDand es) = any hasAtomDDltl (HashSet.toList es)
hasAtomDDltl (DDor es) = any hasAtomDDltl (HashSet.toList es)
hasAtomDDltl (DDnot e) = hasAtomDDltl e
hasAtomDDltl (DDop1 _ e) = hasAtomDDltl e
hasAtomDDltl (DDop2 _ e1 e2) = hasAtomDDltl e1 || hasAtomDDltl e2
hasAtomDDltl (DDexpr _) = False

-- | Checks whether a node is a temporal operator.
isTemporalDDltl :: DDltl s dd -> Bool
isTemporalDDltl (DDop1 Patom _) = False
isTemporalDDltl (DDop1 {}) = True
isTemporalDDltl (DDop2 {}) = True
isTemporalDDltl _ = False

-- | A module's init/invar/trans/LTL as decision diagrams.
data PackedDDmodule sinit sinvar strans sltl dd = PackedDDmodule
    { dd_name    :: String
    , dd_vars    :: PackedBvars
    , dd_init    :: sinit
    , dd_invar   :: sinvar
    , dd_trans   :: strans
    , dd_ltlspec :: Maybe (DDltl sltl dd)
    } deriving (Eq,Show)

-- | Converts a 'DDltl' formula to a 'Bexpr'.
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

-- | Converts a 'DDltl' formula to a 'Pexpr'.
ddltlToExpr :: (BuildDDs dd s,Monad m) => DDltl s dd -> DDM m Pexpr
ddltlToExpr = ddltlToExprWith ddsToExpr

-- | Converts a 'DDltl' formula to a 'Pexpr', given a leaf converter.
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

-- | 'buildDDltl' with an explicit DD-type proxy.
buildDDltlProxy :: (BuildDDs dd s) => Proxy dd -> Bexpr -> DDM IO (DDltl s dd)
buildDDltlProxy _ = buildDDltl

-- | Builds a 'DDltl' formula from a 'Bexpr'.
buildDDltl :: (BuildDDs dd s) => Bexpr -> DDM IO (DDltl s dd)
buildDDltl (Bop1 Patom e1) = liftM (DDop1 Patom) $ buildDDltl e1
buildDDltl e | Prelude.not (isLTLBexpr e) Prelude.&& Prelude.not (hasAtomBexpr e) =
    liftM DDexpr (buildDDs e)
buildDDltl (Bopn Pand es) = liftM DDand $ mapHashSetM buildDDltl es
buildDDltl (Bopn Por es) = liftM DDor $ mapHashSetM buildDDltl es
buildDDltl (Bop1 Pnot e1) = buildDDltl (bnot e1)
buildDDltl (Bop1 o e1) | isLTLOp1 o = liftM (DDop1 o) $ buildDDltl e1
buildDDltl (Bop2 Pequiv e1 e2) = buildDDltl $ unfoldBequiv e1 e2
buildDDltl (Bop2 o e1 e2) | isLTLOp2 o = do
    e1' <- buildDDltl e1
    e2' <- buildDDltl e2
    return (DDop2 o e1' e2')
buildDDltl e = error $ "buildDDltl: unsupported " ++ show e 

-- | Build a 'PackedDDmodule' under an explicit support-accept budget.
withPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4) => Integer -> PackedBmodule -> (PackedDDmodule s1 s2 s3 s4 dd -> DDM IO res) -> IO res
withPackedDDmodule acc p go = do
    let vars = b_vars p
    runDDM vars True $ withSupportAccept acc $ do
        dd <- toPackedDDmodule p
        go dd

-- | Builds a 'PackedDDmodule' from a 'PackedBmodule'.
toPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4) => PackedBmodule -> DDM IO (PackedDDmodule s1 s2 s3 s4 dd)
toPackedDDmodule p = do
        let name = b_name p
        let vars = b_vars p
        initDD <- buildDDs (b_init p)
        invarDD <- buildDDs (b_invar p)
        transDD <- buildDDs (b_trans p)
        ltlDD <- mapM buildDDltl (b_ltlspec p)
        let dd = PackedDDmodule name vars initDD invarDD transDD ltlDD
        return dd

-- | Converts a 'PackedDDmodule' back to a 'PackedBmodule'.
fromPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => PackedDDmodule s1 s2 s3 s4 dd -> DDM m PackedBmodule
fromPackedDDmodule (PackedDDmodule name vars init invar trans ltl) = bmInDDM $ do
    init'  <- ddsToBexpr init
    invar' <- ddsToBexpr invar
    trans' <- ddsToBexpr trans
    ltl' <- mapM ddltlToBexpr ltl
    return (PackedBmodule name vars Map.empty init' invar' trans' ltl')
    
-- | 'fromPackedDDmodule' with an explicit DD-type proxy.
fromPackedDDmoduleProxy :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => Proxy dd -> PackedDDmodule s1 s2 s3 s4 dd -> DDM m PackedBmodule
fromPackedDDmoduleProxy dd = fromPackedDDmodule

-- | Renders a 'PackedDDmodule' as a 'PackedPmodule'.
renderPackedDDmodule :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => PackedDDmodule s1 s2 s3 s4 dd -> DDM m PackedPmodule
renderPackedDDmodule (PackedDDmodule name vars init invar trans ltl) = do
    init'  <- ddsToExpr init
    invar' <- ddsToExpr invar
    trans' <- ddsToExpr trans
    ltl' <- mapM ddltlToExpr ltl
    return (PackedPmodule name vars Map.empty init' invar' trans' noPackedPassigns ltl' [])

-- | 'renderPackedDDmodule' with explicit type proxies.
renderPackedDDmoduleProxy :: (BuildDDs dd s1,BuildDDs dd s2,BuildDDs dd s3,BuildDDs dd s4,Monad m) => Proxy s1 -> Proxy s2 -> Proxy s3 -> Proxy s4 -> Proxy dd -> PackedDDmodule s1 s2 s3 s4 dd -> DDM m PackedPmodule
renderPackedDDmoduleProxy s1 s2 s3 s4 dd = renderPackedDDmodule







