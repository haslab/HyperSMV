module Transform.Smv where

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import qualified Data.HashSet as HashSet
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.Key as K
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Data.List as List

import Smv.Syntax
import Smv.Pretty
import Smv.Packed
import Smv.Typing
import qualified Location as L

transformDeclarative :: Monad m => PackedPmodule -> m PackedPmodule
transformDeclarative pmodule@(PackedPmodule name vars defines init invar trans assigns ltlspec) = do
    let (initAss,transAss) = assignsToExprs assigns
    let init' = pands [init,initAss]
    let trans' = pands [trans,transAss]
    let vars' = Map.map simplifyType vars
    return (PackedPmodule name vars' defines init' invar trans' noPackedPassigns ltlspec)

transformNoInvar :: Monad m => PackedPmodule -> m PackedPmodule
transformNoInvar p = transformDeclarative p >>= \pmodule -> do
    let definedVars = Map.keysSet (p_vars pmodule)
    let init' = pands [p_invar pmodule,p_init pmodule]
    let trans' = pands [p_invar pmodule,Peop1 Pnext (p_invar pmodule),p_trans pmodule]
    return $ pmodule { p_init = init', p_trans = trans' }

assignsToExprs :: PackedPassigns -> (Pexpr,Pexpr)
assignsToExprs (PackedPassigns i n) = (initsToExpr i,nextsToExpr n)

initsToExpr :: PackedPdefs -> Pexpr
initsToExpr = pands . Map.foldrWithKey go []
    where go n e acc = (Peop2 Pin (Peident n (typeOfExpr e)) e) : acc

nextsToExpr :: PackedPdefs -> Pexpr
nextsToExpr = pands . Map.foldrWithKey go []
    where go n e acc = (Peop2 Pin (Peop1 Pnext $ Peident n (typeOfExpr e)) e) : acc

nextPowerOf2 :: Int -> Int
nextPowerOf2 n
  | n <= 1    = 1
  | otherwise = 2 ^ ceiling (logBase 2 (fromIntegral n :: Double))

mkBooleanVar :: Monad m => Pident -> Ptype -> StateT Pexpr m Ptype
mkBooleanVar n t = case toVarType t of
    VBool -> return Pboolean
    VInt is -> do
        State.modify $ \inv -> pand inv (Peop2 Pin (Peident n EInt) $ psetint is)
        return $ Penum $ IntSet.fromList $ extend (IntSet.toList is) (nextPowerOf2 $ IntSet.size is)
  where extend is n = take n $ is ++ ([0..] List.\\ is)

-- makes sure that all variables have a range that is a power of 2
transformBooleanDomains :: Monad m => PackedPmodule -> m PackedPmodule
transformBooleanDomains (PackedPmodule name vars defines init invar trans assigns ltlspec) = do
    (vars',vars_invar') <- State.runStateT (K.mapWithKeyM mkBooleanVar vars) ptrue
    return (PackedPmodule name vars' defines init (pand invar vars_invar') trans assigns ltlspec)


      