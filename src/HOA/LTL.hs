-- | Converts DD-based LTL formulas to HOA automata and HOA automata to explicit-state NBAs.
module HOA.LTL where

import Prettyprinter
import Control.Monad.IO.Class
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.HashSet as HashSet
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import qualified Control.Monad.Reader as Reader
import Control.Monad.Trans
import qualified Data.Key as K

import qualified Data.DD as DD
import Transform.DD.Packed
import Transform.Minimize
import Transform.DD.Build
import Transform.Bexpr
import Smv.Syntax (Pop1(Patom))
import ExplicitState.Syntax
import HOA.Syntax
import HOA.Parser
import Pretty
import Utils

-- | DD atoms to their assigned AP names.
type APnames dd s = (HashMap s String)

-- | Look up or register a DD atom's AP name.
registerAP :: (BuildDDs dd s,Monad m) => s -> HOAM dd s m String
registerAP dd = do
    (num,st) <- State.get
    case HashMap.lookup dd st of
        Just s -> return s
        Nothing -> do
            let n = (namify num)
            State.put (succ num,HashMap.insert dd n st)
            return n

-- | Monad for LTL/HOA translation: name counter plus AP registry.
type HOAM dd s m = StateT (Int,APnames dd s) m

-- | Runs a 'HOAM' computation with an empty AP registry.
doHOAM :: Monad m => HOAM dd s m a -> m a
doHOAM m = State.evalStateT m (0,HashMap.empty)

-- | Renders a DD-based LTL formula as spot's LTL syntax.
prettyLTLToHOA :: (BuildDDs dd s,Monad m) => DDltl s dd -> HOAM dd s m (Doc ann)
prettyLTLToHOA (DDand es) = do
    es' <- mapM prettyLTLToHOA (HashSet.toList es)
    return $ parens (sepBy (pretty "&") es')
prettyLTLToHOA (DDor es) = do
    es' <- mapM prettyLTLToHOA (HashSet.toList es)
    return $ parens (sepBy (pretty "|") es')
prettyLTLToHOA (DDnot e1) = do
    e1' <- prettyLTLToHOA e1
    return (parens $ pretty "!" <> e1')
prettyLTLToHOA (DDop1 Patom e1) = prettyLTLToHOA e1
prettyLTLToHOA (DDop1 o e1) = do
    e1' <- prettyLTLToHOA e1
    return (parens $ pretty o <> e1')
prettyLTLToHOA (DDop2 o e1 e2) = do
    e1' <- prettyLTLToHOA e1
    e2' <- prettyLTLToHOA e2
    return $ parens $ e1' <+> pretty o <+> e2'
prettyLTLToHOA (DDexpr dd) = do
    n <- registerAP dd
    return $ pretty n

-- | The exact @ltl2tgba@ invocation. 
ltl2tgbaArgs :: FilePath -> FilePath -> [CommandArg]
ltl2tgbaArgs infile outfile = [Left "--hoaf=t",Left "-B",Left "-F",Right infile,Left "-o",Right outfile]

-- | Translates an LTL formula to HOA via @ltl2tgba@.
ltlToHOA :: (BuildDDs dd s,MonadIO m) => Bool -> Bool -> Maybe String -> DDltl s dd -> HOAM dd s m HOA
ltlToHOA doRemoveTemps isDebug container ltl = do
    doc <- prettyLTLToHOA ltl
    let formula = show doc
    withSystemTempUnlessError doRemoveTemps isDebug "formula.ltl" $ \infile -> do
        liftIO $ writeFile infile formula
        withSystemTempUnlessError doRemoveTemps isDebug "formula.hoa" $ \outfile -> do
            -- -B (state-based Buechi) is required: without it spot emits generalized Buechi.
            let args = ltl2tgbaArgs infile outfile
            liftIO $ runDockerCommand isDebug container $ Command "ltl2tgba" args
            liftIO $ parseHOA outfile

-- | Converts a parsed HOA automaton into a closure-guarded explicit-state NBA.
hoaToNBA :: (BuildDDs dd s,Monad m) => HOA -> IntMap Int -> HOAM dd s (DDM m) (ExplicitStateNBA (DD.Val dd))
hoaToNBA (HOA starts aps acceptance states) dd_map = do
    aps' <- convertAPs aps
    let accept = fmap acceptanceSets acceptance
    trans <- mapM (convertState accept aps') states
    return $ ExplicitStateNBA starts trans
  where
    acceptanceSets :: [HOAacceptance] -> IntSet
    acceptanceSets [] = IntSet.empty
    acceptanceSets [Inf i] = IntSet.singleton i
    acceptanceSets as = error "hoaToNBA we support only one acceptance set"
      
    convertAPs :: (BuildDDs dd s,Monad m) => [String] -> HOAM dd s (DDM m) (IntMap (DD.Vals dd -> Bool))
    convertAPs aps = do
        apnames <- State.gets snd
        apfuns  <- K.foldlWithKeyM convertAP Map.empty apnames
        return $ IntMap.fromList $ map (\(i,ap) -> (i,unsafeLookupNote "convertAPs" ap apfuns)) (zip [0..] aps)
        
    convertAP :: (BuildDDs dd s,Monad m) => Map String (DD.Vals dd -> Bool) -> s -> String -> HOAM dd s (DDM m) (Map String (DD.Vals dd -> Bool))
    convertAP acc dds ap = do
        r <- lift Reader.ask
        let evalAP = evalExplicitDDs' r dd_map dds
        return $ Map.insert ap evalAP acc
    
    convertState :: Monad m => Maybe IntSet -> (IntMap (DD.Vals dd -> Bool)) -> HOAstate -> HOAM dd s (DDM m) (IntMap (IsAccepting,DD.Vals dd -> Bool))
    convertState accept aps (HOAstate (IntSet.null -> True) trans) = do
        let joinTrans (b1,f1) (b2,f2) = (b1 || b2,\vs -> f1 vs || f2 vs)
        let convert acc ae (HOAnext i js) = IntMap.insertWith joinTrans i (accept_js,convertAPexpr aps ae) acc
                where accept_js = maybe True (\a -> not $ IntSet.null $ IntSet.intersection a js) accept
        return $ K.foldlWithKey convert IntMap.empty trans
    convertState accept aps hoa = error $ "convertState: state acceptance unsupported"

    convertAPexpr :: (IntMap (DD.Vals dd -> Bool)) -> APexpr -> DD.Vals dd -> Bool
    convertAPexpr aps (APbool b) vals = b
    convertAPexpr aps (APand es) vals = all (\e -> convertAPexpr aps e vals) es
    convertAPexpr aps (APor es) vals = any (\e -> convertAPexpr aps e vals) es
    convertAPexpr aps (APnot e) vals = not $ convertAPexpr aps e vals
    convertAPexpr aps (APvar v) vals = (unsafeIntLookupNote "convertAPexpr" v aps) vals

-- | Like 'hoaToNBA', but yields each edge guard as a 'Bexpr' over the model's own variables instead of an opaque predicate closure.
hoaToNBABexpr :: (BuildDDs dd s,Monad m) => HOA -> HOAM dd s (DDM m) (IntSet,IntMap (IntMap (IsAccepting,Bexpr)))
hoaToNBABexpr (HOA starts aps acceptance states) = do
    aps' <- convertAPsB aps
    let accept = fmap acceptanceSetsB acceptance
    trans <- mapM (convertStateB accept aps') states
    return (starts,trans)
  where
    acceptanceSetsB :: [HOAacceptance] -> IntSet
    acceptanceSetsB [] = IntSet.empty
    acceptanceSetsB [Inf i] = IntSet.singleton i
    acceptanceSetsB as = error "hoaToNBABexpr: we support only one acceptance set"

    convertAPsB aps = do
        apnames <- State.gets snd
        apbs <- K.foldlWithKeyM convertAPB Map.empty apnames
        return $ IntMap.fromList $ map (\(i,ap) -> (i,unsafeLookupNote "convertAPsB" ap apbs)) (zip [0..] aps)

    convertAPB acc dds ap = do
        b <- lift $ bmInDDM (ddsToBexpr dds)
        return $ Map.insert ap b acc

    convertStateB accept aps (HOAstate (IntSet.null -> True) trans) = do
        let joinTrans (b1,g1) (b2,g2) = (b1 || b2,bor g1 g2)
        let convert acc ae (HOAnext i js) = IntMap.insertWith joinTrans i (accept_js,convertAPexprB aps ae) acc
                where accept_js = maybe True (\a -> not $ IntSet.null $ IntSet.intersection a js) accept
        return $ K.foldlWithKey convert IntMap.empty trans
    convertStateB accept aps hoa = error "hoaToNBABexpr: state acceptance unsupported"

    convertAPexprB aps (APbool b) = Bbool b
    convertAPexprB aps (APand es) = bands (HashSet.map (convertAPexprB aps) es)
    convertAPexprB aps (APor es) = bors (HashSet.map (convertAPexprB aps) es)
    convertAPexprB aps (APnot e) = bnot (convertAPexprB aps e)
    convertAPexprB aps (APvar v) = unsafeIntLookupNote "convertAPexprB" v aps
