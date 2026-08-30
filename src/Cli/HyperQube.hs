-- | The HyperQube-backend driver.
module Cli.HyperQube where

import Control.Monad.IO.Class
import Control.Monad.Identity
import qualified Data.Map as Map

import Smv.Syntax
import Smv.Typing
import Smv.Packed
import Transform.Bexpr
import Transform.Bexpr.Packed
import Transform.Pexpr
import Transform.Substitute
import Transform.Bexpr.CSE

import Cli.Args
import Cli.Common

-- | Write the formula and SMV models in HyperQube's expected format.
doHyperQube :: Eq digest => Args -> ([PackedPmodule],[(digest,PackedBmodule)],Bformula,[Subst]) -> IO ()
doHyperQube args (insmvs,smvs,formula,names) = do

    let qs = map fst $ quantsBformula formula
    let vars = map (b_vars . snd) smvs
    let hvars = joinHyperPvars $ zip qs vars

    fdefs <- timeIt "Generating output formula" $ doBM (Map.map toVarType hvars) $ do
        (formula2,fdefs) <- optimizeBformulaForSmv hvars formula
        formula3 <- mapFormula (return . ensureHyperQubeTemporal) formula2
        liftIO $ writeFormula args (globalOutformula args) HyperQube formula3
        return fdefs

    timeIt "Generating output SMVs" $ do
        let outsmvs = map (doOutputSmv) $ zip (map snd smvs) fdefs
        mapM_ (\(f,s) -> writeSMV args f (Just HyperQube) s) $ zip (output args) outsmvs
    writeSubsts args names

-- | Does a 'Pexpr' contain a temporal operator anywhere.
isLTLPexpr :: Pexpr -> Bool
isLTLPexpr (Peop1 o e1) = isLTLOp1 o || isLTLPexpr e1
isLTLPexpr (Peop2 o e1 e2) = isLTLOp2 o || isLTLPexpr e1 || isLTLPexpr e2
isLTLPexpr (Peopn _ es) = or (map isLTLPexpr es)
isLTLPexpr (Pecase cs) = or (concatMap (\(c,e) -> [isLTLPexpr c,isLTLPexpr e]) cs)
isLTLPexpr (Pedemorgan e1 e2 e3) = or (map isLTLPexpr [e1,e2,e3])
isLTLPexpr _ = False

-- | HyperQube's genqbf parser requires every leaf reachable from the top through and/or to be temporal.
-- The neutral fix: @p U p@ is exactly @p@ evaluated now.
ensureHyperQubeTemporal :: Pexpr -> Pexpr
ensureHyperQubeTemporal e@(Peopn o es) | (o == Pand || o == Por) && isLTLPexpr e =
    Peopn o (map ensureHyperQubeTemporal es)
ensureHyperQubeTemporal e
    | isTopLTL e = e
    | otherwise = Peop2 Pu e e
  where
    isTopLTL (Peop1 o1 _) = isLTLOp1 o1
    isTopLTL (Peop2 o2 _ _) = isLTLOp2 o2
    isTopLTL _ = False

-- | Unpack a boolean module and add its formula-derived defines.
doOutputSmv :: (PackedBmodule,Subst) -> PackedPmodule
doOutputSmv (p,ss) = runIdentity $ doBMState $ do
    p1 <- fromPackedBmodule p
    return $ addPmoduleDefines ss p1

