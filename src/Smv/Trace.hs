-- | Witness and counterexample traces.
module Smv.Trace where

import Prettyprinter
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics

import Pretty
import Transform.Substitute
import Smv.Syntax
import Smv.Typing

-- | A named sequence of states, marked as example or counterexample.
data Trace = Trace { trace_description :: String, trace_type :: TraceType, trace_states :: [State] }
    deriving (Eq,Ord,Show,Generic)

-- | Whether a trace is a positive example or a counterexample.
data TraceType = Example | Counterexample
    deriving (Eq,Ord,Show,Generic)

-- if a state is the target of a loop from the last reported state
type IsLoopTarget = Bool

-- | One trace state: its name, loop marker, and variable valuation.
data State = State { state_name :: String, state_loop :: IsLoopTarget, state_vars :: Subst }
    deriving (Eq,Ord,Show,Generic)

instance Pretty TraceType where
    pretty Example = pretty "Example"
    pretty Counterexample = pretty "Counterexample"

instance Pretty Trace where
    pretty (Trace desc ty sts) = vcat [pretty "Trace Description:" <+> pretty desc , pretty "Trace Type:" <+> pretty ty , nestvcat 2 (concatMap prettyState sts)]

prettyState (State name loop vars) = ploop ++ [pst , nestvcat 2 pvs]
    where
    ploop = if loop then [pretty "-- Loop starts here"] else []
    pst = pretty "-> State:" <+> pretty name <+> pretty "<-"
    pvs = map drawState $ Map.toList vars
    drawState (n,e) = pretty n <+> pretty "=" <+> pretty e
    
-- | Parse a nuXmv counterexample trace.
parseNuXmvTrace :: Map String Pident -> Text -> Maybe Trace
parseNuXmvTrace names txt = case blocks of
    [] -> Nothing
    _  -> Just $ Trace "nuXmv counterexample" Counterexample (accum Map.empty blocks)
  where
    blocks = go False Nothing (T.lines txt)
    -- go pendingLoop currentBlock: blocks carry reversed assignment lists
    go :: Bool -> Maybe (String,Bool,[(Pident,Pexpr)]) -> [Text] -> [(String,Bool,[(Pident,Pexpr)])]
    go _ cur [] = flush cur
    go pending cur (l:ls)
        | T.isInfixOf "Loop starts here" l = go True cur ls
        | Just nm <- stateName l = flush cur ++ go False (Just (nm,pending,[])) ls
        | Just (n,e) <- assign l, Just (nm,lp,as) <- cur = go pending (Just (nm,lp,(n,e):as)) ls
        | otherwise = go pending cur ls
    flush Nothing = []
    flush (Just (nm,lp,as)) = [(nm,lp,reverse as)]
    stateName l = do
        rest <- T.stripPrefix "-> State:" =<< pure (snd (T.breakOn "-> State:" l))
        let nm = T.strip $ fst $ T.breakOn "<-" rest
        if T.null nm then Nothing else Just (T.unpack nm)
    assign l = case T.breakOn " = " (T.strip l) of
        (lhs,rest) | Just rhs <- T.stripPrefix " = " rest
                   , not (T.null lhs), not ("--" `T.isPrefixOf` lhs)
                   , Just n <- Map.lookup (T.unpack lhs) names
                   , Just e <- value (T.strip rhs) -> Just (n,e)
        _ -> Nothing
    value v
        | v == "TRUE" = Just $ Pebool True
        | v == "FALSE" = Just $ Pebool False
        | otherwise = case reads (T.unpack v) :: [(Int,String)] of
            [(i,"")] -> Just $ Peint i
            _ -> Nothing
    -- nuXmv only prints changed variables: carry the previous state's valuation forward
    accum _ [] = []
    accum prev ((nm,lp,as):rest) = State nm lp vs : accum vs rest
        where vs = Map.union (Map.fromList as) prev

-- | Encode a trace as an LTL formula it uniquely satisfies.
traceToLTLSpec :: Trace -> Pexpr
traceToLTLSpec tr = pands $ map go $ zip [0..] $ trace_states tr
    where
    go :: (Int,State) -> Pexpr
    go (i,State _ _ vs) = nexts i $ pands $ map (\(n,e) -> Peop2 Peq (Peident n (typeOfExpr e)) e) $ Map.toList vs
    nexts :: Int -> Pexpr -> Pexpr
    nexts i e | i <= 0 = e
    nexts i e = Peop1 Px $ nexts (i-1) e
    
    

