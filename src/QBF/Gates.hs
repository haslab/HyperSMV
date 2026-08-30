-- | Gate-level QCIR/QBF circuit algebra.
module QBF.Gates where

import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Merge.Lazy as IntMap
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.HashMap.Lazy (HashMap(..))
import qualified Data.HashMap.Lazy as HashMap
import qualified Control.Monad.State.Strict as StrictState
import Control.Monad
import GHC.Generics
import Data.Hashable

import Utils
import Smv.Syntax
import Data.DD (DDNode(..),DDView(..))
import Data.DDs (AndDDs(..),NextDDs(..),TreeDDs(..))
import Transform.DD.Build
import Transform.DD.Packed
import QBF.Syntax

-- | Gate-emission state.
data QCIRstate = QCIRstate
    { qcir_st_quantifiers :: [Quantifier]
    , qcir_st_num_gates :: Int
    , qcir_st_gates :: [(GateId,GateExpr)]
    , qcir_st_cache :: HashMap (Int,Int) QCIRgate   -- (depth, ddNodeId)
    , qcir_st_names :: QCIRnames
    , qcir_st_decode :: Map (Pident,Int) (Pexpr,[GateId])
    -- counts complementary-literal OR merges (x ∨ ¬x ∨ rest)
    , qcir_st_orconflicts :: Int
    , qcir_st_hashcons :: HashMap QCIRgate GateId
    } deriving (Eq,Show,Generic)
    
instance Hashable QCIRstate

-- | Name-to-gate-id table.
type QCIRnames = Map (Pident,Int) GateId

-- | The gate-emission monad.
type QCIRM = StrictState.StateT QCIRstate

-- | A gate expression under construction.
data QCIRgate
    = Qand (IntMap IsNegated)
    | Qor (IntMap IsNegated)
    | Qbool Bool
    | Qid GateId IsNegated
    deriving (Eq,Ord,Show,Generic)
    
instance Hashable QCIRgate

-- | Build an AND gate, folding trivial cases.
qand :: (IntMap IsNegated) -> QCIRgate
qand m = case IntMap.size m of
    0 -> Qbool True
    1 -> let (gid,isNeg) = popIntMap m in Qid gid isNeg
    _ -> Qand m

-- | Build an OR gate, folding trivial cases.
qor :: (IntMap IsNegated) -> QCIRgate
qor m = case IntMap.size m of
    0 -> Qbool False
    1 -> let (gid,isNeg) = popIntMap m in Qid gid isNeg
    _ -> Qor m

-- | Convert a 'QCIRgate' to a stored 'GateExpr'.
qcirToGate :: QCIRgate -> GateExpr
qcirToGate (Qand gs) = GateAnd gs
qcirToGate (Qor gs) = GateOr gs
qcirToGate (Qbool False) =  GateOr IntMap.empty
qcirToGate (Qbool True) = GateAnd IntMap.empty
qcirToGate (Qid g isNeg) = GateAnd $ IntMap.singleton g isNeg

-- | Materialise a gate as a plain (non-negated) id.
newNonNegGate :: (Monad m) => QCIRgate -> QCIRM m GateId
newNonNegGate (Qid g False) = return g
newNonNegGate qg = mkNewGate qg

-- | Materialise a gate as a (possibly negated) reference.
newNegGate :: (Monad m) => QCIRgate -> QCIRM m (GateId,IsNegated)
newNegGate (Qid g isNeg) = return (g,isNeg)
newNegGate qg = do
    gid <- mkNewGate qg
    return (gid,False)

mkNewGate :: (Monad m) => QCIRgate -> QCIRM m GateId
mkNewGate qg = do
    st <- StrictState.get
    let num = qcir_st_num_gates st
    let gates = qcir_st_gates st
    StrictState.put $ st { qcir_st_num_gates = succ num, qcir_st_gates = (num,qcirToGate qg) : gates }
    return num

-- | Conjoin two gate expressions.
andQCIR :: (Monad m) => QCIRgate -> QCIRgate -> QCIRM m QCIRgate
andQCIR (Qbool True) y = return y
andQCIR (Qbool False) y = return $ Qbool False
andQCIR x (Qbool True) = return x
andQCIR x (Qbool False) = return $ Qbool False
andQCIR (Qand xs) (Qand ys) = case joinAnds xs ys of
    Nothing -> return $ Qbool False
    Just zs -> return $ qand zs
andQCIR (Qand xs) y = do
    (gy,yIsNeg) <- newNegGate y
    case insertAnd gy yIsNeg xs of
        Nothing -> return $ Qbool False
        Just zs -> return $ qand zs  
andQCIR x (Qand ys) = do
    (gx,xIsNeg) <- newNegGate x
    case insertAnd gx xIsNeg ys of
        Nothing -> return $ Qbool False
        Just zs -> return $ qand zs
andQCIR x y = do
    (gx,xIsNeg) <- newNegGate x
    (gy,yIsNeg) <- newNegGate y
    case toAnd [(gx,xIsNeg),(gy,yIsNeg)] of
        Nothing -> return $ Qbool False
        Just zs -> return $ qand zs

-- | Build an AND literal map from (id, negation) pairs.
toAnd :: [(Int,IsNegated)] -> Maybe (IntMap IsNegated)
toAnd = foldM (\m (x,xIsNeg) -> insertAnd x xIsNeg m) IntMap.empty

-- | Insert one literal into an AND map.
insertAnd :: Int -> IsNegated -> IntMap IsNegated -> Maybe (IntMap IsNegated)
insertAnd gx xIsNeg ys = IntMap.alterF (insertIsNegatedF xIsNeg) gx ys

-- | Merge two AND literal maps.
joinAnds :: IntMap IsNegated -> IntMap IsNegated -> Maybe (IntMap IsNegated)
joinAnds xs ys = do
    let keep = IntMap.preserveMissing
    let match = IntMap.zipWithAMatched $ \k x y -> mergeIsNegated x y
    IntMap.mergeA keep keep match xs ys

-- | Disjoin two gate expressions.
orQCIR :: (Monad m) => QCIRgate -> QCIRgate -> QCIRM m QCIRgate
orQCIR (Qbool False) y = return y
orQCIR (Qbool True) y = return $ Qbool True
orQCIR x (Qbool False) = return x
orQCIR x (Qbool True) = return $ Qbool True
orQCIR (Qor xs) (Qor ys) = case joinOrs xs ys of
    Nothing -> orConflictTrue
    Just zs -> return $ qor zs
orQCIR (Qor xs) y = do
    (gy,yIsNeg) <- newNegGate y
    case insertOr gy yIsNeg xs of
        Nothing -> orConflictTrue
        Just zs -> return $ qor zs
orQCIR x (Qor ys) = do
    (gx,xIsNeg) <- newNegGate x
    case insertOr gx xIsNeg ys of
        Nothing -> orConflictTrue
        Just zs -> return $ qor zs
orQCIR x y = do
    (gx,xIsNeg) <- newNegGate x
    (gy,yIsNeg) <- newNegGate y
    case toOr [(gx,xIsNeg),(gy,yIsNeg)] of
        Nothing -> orConflictTrue
        Just zs -> return $ qor zs

-- x ∨ ¬x ∨ rest is a tautology: the whole disjunction is TRUE (dual of insertAnd's x ∧ ¬x → FALSE).
orConflictTrue :: (Monad m) => QCIRM m QCIRgate
orConflictTrue = do
    StrictState.modify' $ \st -> st { qcir_st_orconflicts = succ (qcir_st_orconflicts st) }
    return $ Qbool True

-- | Build an OR literal map from (id, negation) pairs.
toOr :: [(Int,IsNegated)] -> Maybe (IntMap IsNegated)
toOr = foldM (\m (x,xIsNeg) -> insertOr x xIsNeg m) IntMap.empty

-- | Insert one literal into an OR map.
insertOr :: Int -> IsNegated -> IntMap IsNegated -> Maybe (IntMap IsNegated)
insertOr gx xIsNeg ys = IntMap.alterF (insertIsNegatedF xIsNeg) gx ys

-- | Merge two OR literal maps.
joinOrs :: IntMap IsNegated -> IntMap IsNegated -> Maybe (IntMap IsNegated)
joinOrs xs ys = do
    let keep = IntMap.preserveMissing
    let match = IntMap.zipWithAMatched $ \k x y -> mergeIsNegated x y
    IntMap.mergeA keep keep match xs ys

-- | 'alterF'-shaped wrapper around 'insertIsNegated'.
insertIsNegatedF :: IsNegated -> Maybe IsNegated -> Maybe (Maybe IsNegated)
insertIsNegatedF isNeg mb = fmap Just $ insertIsNegated isNeg mb

-- | Insert a negation flag into a map slot.
insertIsNegated :: IsNegated -> Maybe IsNegated -> Maybe IsNegated
insertIsNegated x Nothing = Just x
insertIsNegated x (Just y) = mergeIsNegated x y

-- | Merge two negation flags for one gate id.
mergeIsNegated :: IsNegated -> IsNegated -> Maybe IsNegated
mergeIsNegated False False = Just False
mergeIsNegated True True = Just True
mergeIsNegated _ _ = Nothing

-- | Fold gate expressions with 'andQCIR'.
andsQCIR :: (Monad m,Foldable f) => f QCIRgate -> QCIRM m QCIRgate
andsQCIR = foldM andQCIR (Qbool True)

-- | Fold gate expressions with 'orQCIR'.
orsQCIR :: (Monad m,Foldable f) => f QCIRgate -> QCIRM m QCIRgate
orsQCIR = foldM orQCIR (Qbool False)

-- | Lift a boolean constant to a gate expression.
boolQCIR :: (Monad m) => Bool -> QCIRM m QCIRgate
boolQCIR = return . Qbool

-- | Negate a gate expression.
notQCIR :: (Monad m) => QCIRgate -> QCIRM m QCIRgate
notQCIR (Qand gs) = return $ Qor $ IntMap.map not gs
notQCIR (Qor gs) = return $ Qand $ IntMap.map not gs
notQCIR (Qbool b) = return $ Qbool $ not b
notQCIR (Qid g isNeg) = return $ Qid g $ not isNeg

-- | Build an equivalence gate expression.
equivQCIR :: (Monad m) => QCIRgate -> QCIRgate -> QCIRM m QCIRgate
equivQCIR x y = do
    notx <- notQCIR x
    noty <- notQCIR y
    trues <- andQCIR x y
    falses <- andQCIR notx noty
    orQCIR trues falses    

-- | Emit a decision diagram as QCIR gates. 
ddToQCIR :: (DDNode dd,Monad m) => Int -> (Int -> QCIRnames -> [GateId]) -> dd -> QCIRM m QCIRgate
ddToQCIR depth render bdd = do
    names <- StrictState.gets qcir_st_names
    let goAll :: (DDNode dd,Monad m) => [dd] -> [QCIRgate] -> ([QCIRgate] -> QCIRM m QCIRgate) -> QCIRM m QCIRgate
        goAll [] acc k = k (reverse acc)
        goAll (c:cs) acc k = go c (\b -> goAll cs (b:acc) k)
        go :: (DDNode dd,Monad m) => dd -> (QCIRgate -> QCIRM m QCIRgate) -> QCIRM m QCIRgate
        go p k = case ddView p of
          DDViewLeaf b -> k $ Qbool b
          DDViewBranch dd_i cs -> do
            let key = (depth,ddNodeId p)
            h <- StrictState.gets qcir_st_cache
            case HashMap.lookup key h of
                Just g -> k g
                Nothing -> goAll cs [] $ \bs -> do
                    -- Bit-blast n-ary nodes, so the QBF path can consume a MULTI-VALUED diagram rather than requiring a booleanised model. 
                    let bits = render dd_i names
                        w = length bits
                        -- MSB first
                        lit ix (j,g) = Qid g (Prelude.not (odd (ix `div` (2 ^ (w - 1 - j)))))
                    disjs <- forM (zip [0..] bs) $ \(ix,b) -> do
                        cube <- andsQCIR (map (lit ix) (zip [0..] bits))
                        andQCIR cube b
                    e0 <- orsQCIR disjs
                    -- Materialise the node's gate once and cache the reference (@Qid gid@).
                    e <- case e0 of
                            Qid {} -> return e0
                            Qbool {} -> return e0
                            _ -> do
                                gid <- mkNewGate e0
                                return (Qid gid False)
                    StrictState.modify $ \st ->
                        let newCache = HashMap.insert key e (qcir_st_cache st)
                        in newCache `seq` st { qcir_st_cache = newCache }
                    k e
    go bdd return

-- | The leaf decision-diagram type carried by a DD structure.
type family LeafDD s where
    LeafDD (AndDDs dd) = dd
    LeafDD (NextDDs dd) = dd
    LeafDD (TreeDDs dd) = dd

-- | All four DD structures of a QBF model share one leaf backend. 
type QBFDDs4 dd s1 s2 s3 s4 =
    (QBFDDs s1,QBFDDs s2,QBFDDs s3,QBFDDs s4
    ,LeafDD s1 ~ dd,LeafDD s2 ~ dd,LeafDD s3 ~ dd,LeafDD s4 ~ dd)

-- | Per-backend interface for emitting gates from a DD.
class (BuildDDs (LeafDD s) s,DDNode (LeafDD s)) => QBFDDs s where
    bddsToQCIR :: (Monad m) => Int -> (Int -> QCIRnames -> [GateId]) -> s -> QCIRM m QCIRgate
    boolBDD :: Bool -> DDltl s (LeafDD s)

instance (BuildDD dd,DDNode dd) => QBFDDs (AndDDs dd) where
    bddsToQCIR depth render (AndDDs bdds) = andsQCIR =<< mapM (ddToQCIR depth render) (Map.elems bdds)
    boolBDD False = DDexpr $ AndDDs $ Map.singleton IntSet.empty ddFalse
    boolBDD True = DDexpr $ AndDDs $ Map.singleton IntSet.empty ddTrue

instance (BuildDD dd,DDNode dd) => QBFDDs (NextDDs dd) where
    bddsToQCIR depth render (NextDDs bdds) = andsQCIR =<< mapM (ddToQCIR depth render) (Map.elems bdds)
    boolBDD False = DDexpr $ NextDDs $ Map.singleton IntSet.empty ddFalse
    boolBDD True = DDexpr $ NextDDs $ Map.singleton IntSet.empty ddTrue

instance (BuildDD dd,DDNode dd) => QBFDDs (TreeDDs dd) where
    bddsToQCIR depth render (NodeAndDDs xs) = andsQCIR =<< mapM (bddsToQCIR depth render ) xs
    bddsToQCIR depth render (NodeOrDDs xs) = orsQCIR =<< mapM (bddsToQCIR depth render ) xs
    bddsToQCIR depth render (LeafDDs sup (bdd)) = ddToQCIR depth render bdd
    boolBDD False = DDexpr $ LeafDDs IntMap.empty ddFalse
    boolBDD True = DDexpr $ LeafDDs IntMap.empty ddTrue

-- | Render a gate id as the boolean variable name emitted for it.
identName :: GateId -> Pident
identName i = Pident ("x"++show i) []
