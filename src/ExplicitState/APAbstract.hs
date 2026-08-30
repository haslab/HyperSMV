-- | AP abstraction for the AutoHyper back end.
module ExplicitState.APAbstract
    ( transformSingles
    , apCriteria
    ) where

import           Control.Monad
import           Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import           Control.Monad.Trans.Maybe
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Map as Map
import           Data.Maybe

import Utils (swap)
import Smv.Syntax (Pident(..), addDimPident, mkQuantDim)
import Smv.Typing (VarType(..))
import Transform.Bexpr
import Transform.Bexpr.Packed (BSubst)

-- | Next free index, and the propositions minted so far, keyed on the defined expression.
type APState = (Int, HashMap Bexpr Pident)

-- | Returns the expression with each maximal single-trace boolean sub-formula replaced by a fresh trace-qualified boolean variable, together with the definitions of those variables.
transformSingles :: Monad m => Bexpr -> m (Bexpr, BSubst)
transformSingles e0 = do
    (e1, (_, ss)) <- State.runStateT (total (mapBexprWith mkAP e0)) (0, HashMap.empty)
    return (e1, Map.fromList (map swap (HashMap.toList ss)))
  where
    total :: Monad m => StateT APState (MaybeT m) a -> StateT APState m a
    total = State.mapStateT (liftM fromJust . runMaybeT)

    mkAP :: Monad m => Bexpr -> StateT APState (MaybeT m) Bexpr
    mkAP e = case apCriteria e of
        Nothing  -> mzero
        Just dim -> do
            (i, ss) <- State.get
            case HashMap.lookup e ss of
                Just n  -> return (apVar n)
                Nothing -> case HashMap.lookup (bnot e) ss of
                    Just n  -> return (bnot (apVar n))
                    Nothing -> do
                        let n = addDimPident (Pident (apPrefix ++ show i) []) (mkQuantDim dim)
                        State.put (i + 1, HashMap.insert e n ss)
                        return (apVar n)

    apVar n = Bvar (n, False) VBool

apPrefix :: String
apPrefix = "AP"

apCriteria :: Bexpr -> Maybe String
apCriteria e
    | isSimpleBexpr e     = Nothing
    | not (isBoolBexpr e) = Nothing
    | isLTLBexpr e        = Nothing
    | otherwise           = isSingleDimBexpr e
