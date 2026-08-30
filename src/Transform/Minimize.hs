-- | Renames SMV module variables to short, keyword-safe names.
module Transform.Minimize where

import qualified Data.Set as Set    
import qualified Data.Map as Map
import Data.Char
import Data.Digits
import Control.Monad
import Control.Monad.State(State(..))
import qualified Control.Monad.State as State

import Smv.Lexer as Lexer
import Smv.Syntax
import Transform.Bexpr.Rename
import Transform.Bexpr.Packed

-- converts each integer to a unique name
namify :: Int -> String
namify i = case digits 26 i of
    [] -> "a"
    ds -> map (\i -> chr $ i + ord 'a') ds

-- | Generates n unique names avoiding SMV keywords.
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

-- | Renames a module's variables to minimized names.
transformBminimize :: Monad m => PackedBmodule -> m (PackedBmodule,NameSubst)
transformBminimize bimodule = do
    let name = b_name bimodule
    let vars = b_vars bimodule
    let newnames = generateSmvNames (Map.size vars)
    let rename ((n,t),n') = (n,(Pident n' [],toExprType t))
    let names :: NameSubst = Map.fromList $ map rename $ zip (Map.toList vars) newnames
    transformBrename names bimodule 


