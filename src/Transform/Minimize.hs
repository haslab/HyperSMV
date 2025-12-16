module Transform.Minimize where

import Data.Set (Set(..))
import qualified Data.Set as Set    
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Char
import Data.Digits
import Control.Monad
import Control.Monad.State(State(..),StateT(..))
import qualified Control.Monad.State as State
import qualified Data.Vector as V
    
import Smv.Lexer as Lexer
import Smv.Syntax
import Smv.Packed
import Smv.Typing
import Transform.Substitute
import Transform.Rename
import Transform.Bpacked
import ExplicitState.Syntax
import Utils

minimizeExplicitState :: ExplicitStateSystem Pident base -> (ExplicitStateSystem Pident base,NameSubst)
minimizeExplicitState e = (e { exp_vars = vars' },names)
    where
    vars = exp_vars e
    pident n = Pident n []
    pnamify = pident . namify
    vars' = V.imap (\i (n,t) -> (pnamify i,t)) vars
    names = Map.fromList $ map (\((n,t),(n',t')) -> (n,(n',exprOfVarType t))) $ V.toList $ V.zip vars vars'

-- converts each integer to a unique name
namify :: Int -> String
namify i = case digits 26 i of
    [] -> "a"
    ds -> map (\i -> chr $ i + ord 'a') ds

generateSmvNames :: Int -> [String]
generateSmvNames n = State.evalState (replicateM n go) 0
    where
    reserved = Lexer.keywordSet
    go :: State Int String
    go = do
        i <- State.get
        let n = namify i
        if Set.member n reserved
            then State.modify succ >> go
            else State.modify succ >> return n

transformBminimize :: Monad m => PackedBmodule -> m (PackedBmodule,NameSubst)
transformBminimize bimodule = do
    let name = b_name bimodule
    let vars = b_vars bimodule
    let newnames = generateSmvNames (Map.size vars)
    let rename ((n,t),n') = (n,(Pident n' [],toExprType t))
    let names :: NameSubst = Map.fromList $ map rename $ zip (Map.toList vars) newnames
    transformBrename names bimodule 


