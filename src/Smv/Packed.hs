module Smv.Packed where

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Trans
import Control.Monad

import Pretty
import Smv.Syntax
import Smv.Pretty
import qualified Location as L
import Transform.Pexpr

--import Debug.Trace

data PackedPmodule = PackedPmodule
    { p_name    :: String
    , p_vars    :: PackedPvars
    , p_defines :: PackedPdefs
    , p_init    :: Pexpr
    , p_invar   :: Pexpr
    , p_trans   :: Pexpr
    , p_assigns :: PackedPassigns
    , p_ltlspec :: Maybe Pexpr
    } deriving (Eq,Ord,Show)

dropLTLSpec :: PackedPmodule -> PackedPmodule
dropLTLSpec p = p { p_ltlspec = Nothing }

addLTLSpec :: Pexpr -> PackedPmodule -> PackedPmodule
addLTLSpec (Peop1 Pg e1) p | not (isLTLExpr e1) = p { p_invar = pand (p_invar p) e1 }
addLTLSpec e p = p { p_ltlspec = add (p_ltlspec p) e }
    where
    add Nothing y = Just y
    add (Just x) y = Just (pand x y)

data PackedPassigns = PackedPassigns { p_inits :: PackedPdefs, p_nexts :: PackedPdefs }
    deriving (Eq,Ord,Show)

type PackedPdefs = Map Pident Pexpr

type PackedPvars = Map Pident Ptype

instance SmvPretty PackedPdefs where
    pp m x = pp m (Pidefine $ map L.dummyLoc $ unpackPdefines x)

instance (SmvPretty PackedPmodule) where
    pp m x = case unpackPmodule x of
        Left err -> error "unexpected unpacking pmodule error"
        Right y -> pp m y

noPackedPdefs :: PackedPdefs
noPackedPdefs = Map.empty

noPackedPassigns :: PackedPassigns
noPackedPassigns = PackedPassigns Map.empty Map.empty

-- * packing / unpacking

packPmodule :: Monad m => Pmodule -> m PackedPmodule
packPmodule (Pmodule name defs) = State.execStateT (mapM_ packPitem defs) st
    where
    st = PackedPmodule name Map.empty Map.empty ptrue ptrue ptrue noPackedPassigns Nothing
    
    addLTLSpec :: Pexpr -> Maybe Pexpr -> Maybe Pexpr
    addLTLSpec e Nothing = Just e
    addLTLSpec e (Just ltl) = Just (pand e ltl)

    packPitem :: Monad m => L.Located Pitem -> StateT PackedPmodule m ()
    packPitem (L.Located l d) = case d of
        Pivar vs isFrozen -> do
            State.modify $ \st -> st { p_vars = Map.union (p_vars st) (packPvars $ map L.unloc vs) }
            when isFrozen $ forM_ vs $ \(L.Located _ (Pvar n t)) -> do
                let vass = Passign (Panext n) (Peident n $ toExprType t)
                assigns <- State.gets p_assigns
                assigns' <- lift $ packPassignsWith [vass] assigns
                State.modify $ \st -> st { p_assigns = assigns' }
        Piltlspec e -> State.modify $ \st -> st { p_ltlspec = addLTLSpec e (p_ltlspec st) }
        Pidefine ds -> State.modify $ \st -> st { p_defines = p_defines st `Map.union` packPdefines (map L.unloc ds) }
        Piinit i -> State.modify $ \st -> st { p_init = pand (p_init st) i }
        Piinvar i -> State.modify $ \st -> st { p_invar = pand (p_invar st) i }
        Pitrans i -> State.modify $ \st -> st { p_trans = pand (p_trans st) i }
        Piassign as -> do
            assigns <- State.gets p_assigns
            assigns' <- lift $ packPassignsWith (map L.unloc as) assigns
            State.modify $ \st -> st { p_assigns = assigns' }
        Pijustice e -> return () -- ignore

unpackPmodule :: Monad m => PackedPmodule -> m Pmodule
unpackPmodule (PackedPmodule name vars defines init invar trans assigns ltlspec) = do
    let vars' = [L.dummyLoc $ Pivar (map L.dummyLoc $ unpackPvars vars) False]
    let defines' = if Map.size defines == 0 then [] else [L.dummyLoc $ Pidefine $ map L.dummyLoc $ unpackPdefines defines]
    let init' = exprToItem init Piinit
    let invar' = exprToItem invar Piinvar
    let trans' = exprToItem trans Pitrans
    let ltlspec' = case ltlspec of { Nothing -> []; Just e -> [L.dummyLoc $ Piltlspec e] }
    assigns' <- unpackPassigns assigns
    let assigns'' = if (Map.size (p_inits assigns) == 0 && Map.size (p_nexts assigns) == 0) then [] else [L.dummyLoc $ Piassign $ map L.dummyLoc assigns']
    let defs' = vars'++defines'++init'++invar'++trans'++assigns''++ltlspec'
    return $ Pmodule name defs'
  where
    exprToItem :: Pexpr -> (Pexpr -> Pitem) -> [L.Located Pitem]
    exprToItem e mk = if e==ptrue then [] else [L.dummyLoc $ mk e]

packPvars :: [Pvar] -> PackedPvars
packPvars = Map.fromList . map (\(Pvar v t) -> (v,t))

unpackPvars :: PackedPvars -> [Pvar]
unpackPvars vs = map (\(n,t) -> Pvar n t) $ Map.toList vs

packPdefines :: [Pdefine] -> PackedPdefs
packPdefines ds = Map.fromList $ map (\(Pdefine n e) -> (Pident n [],e)) ds

unpackPdefines :: PackedPdefs -> [Pdefine]
unpackPdefines ds = map unIdent $ Map.toList ds
    where
    unIdent ((Pident n []),e) = (Pdefine n e)
    unIdent (n,e) = error $ "unpackPdefines: " ++ show n

packPassigns :: Monad m => [Passign] -> m PackedPassigns
packPassigns as = packPassignsWith as (PackedPassigns Map.empty Map.empty)

packPassignsWith :: Monad m => [Passign] -> PackedPassigns -> m PackedPassigns
packPassignsWith as st = State.execStateT (mapM_ packPassign as) st
    where
    packPassign :: Monad m => Passign -> StateT PackedPassigns m ()
    packPassign (Passign (Painit n) e) = do
        inits <- State.gets p_inits
        case Map.lookup n inits of
            Just e -> error $ "duplicated inits for " ++ prettyPident n
            Nothing -> State.modify $ \st -> st { p_inits = Map.insert n e inits }
    packPassign (Passign (Panext n) e) = do
        nexts <- State.gets p_nexts
        case Map.lookup n nexts of
            Just e -> error $ "duplicated nexts for " ++ prettyPident n
            Nothing -> State.modify $ \st -> st { p_nexts = Map.insert n e nexts }

unpackPassigns :: Monad m => PackedPassigns -> m [Passign]
unpackPassigns (PackedPassigns inits nexts) = do
    let inits' = unpack inits Painit
    let nexts' = unpack nexts Panext
    return $ inits' ++ nexts'
  where
    unpack :: PackedPdefs -> (Pident -> Passign_lhs) -> [Passign]
    unpack ds mk = map (\(n,e) -> (Passign (mk n) e)) $ Map.toList ds

-- * extraction

pmoduleNames :: PackedPmodule -> Set Pident
pmoduleNames pmodule = Set.union vars defs
    where
    vars = Map.keysSet (p_vars pmodule)
    defs = Map.keysSet (p_defines pmodule)

addPmoduleDefines :: PackedPdefs -> PackedPmodule -> PackedPmodule
addPmoduleDefines ss b = b { p_defines = Map.union (p_defines b) ss }

