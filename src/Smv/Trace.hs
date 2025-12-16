module Smv.Trace where

import Prettyprinter
import Data.Map (Map(..))
import qualified Data.Map as Map
import GHC.Generics

import Pretty
import Transform.Substitute
import Smv.Syntax
import Smv.Typing
import Transform.Pexpr

data Trace = Trace { trace_description :: String, trace_type :: TraceType, trace_states :: [State] }
    deriving (Eq,Ord,Show,Generic)

data TraceType = Example | Counterexample
    deriving (Eq,Ord,Show,Generic)

-- if a state is the target of a loop from the last reported state
type IsLoopTarget = Bool

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
    
traceToLTLSpec :: Trace -> Pexpr
traceToLTLSpec tr = pands $ map go $ zip [0..] $ trace_states tr
    where
    go :: (Int,State) -> Pexpr
    go (i,State _ _ vs) = nexts i $ pands $ map (\(n,e) -> Peop2 Peq (Peident n (typeOfExpr e)) e) $ Map.toList vs
    nexts :: Int -> Pexpr -> Pexpr
    nexts i e | i <= 0 = e
    nexts i e = Peop1 Px $ nexts (i-1) e
    
    

