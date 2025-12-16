module ExplicitState.Eval where

import Data.Foldable
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Merge.Lazy as IntMap
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import qualified Data.Vector as V
--import qualified Data.Csv as Csv
import qualified Data.ByteString.Lazy as BL
import Data.String
import qualified Data.Massiv.Array as M
import qualified Data.Massiv.Array.Manifest.Vector as M
import qualified Data.Massiv.Array.Unsafe as M
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as MUV
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Safe
import Data.STRef
import Control.Monad.ST as ST
import qualified Control.Monad.Reader as Reader
import qualified Data.Key as K
import Control.Monad.Identity

import Utils
import Smv.Typing
import ExplicitState.Syntax
import Data.DT
import Transform.DDs
import Data.DD (DD)
import qualified Data.DD as DD
import Smv.Syntax
import Transform.Substitute

--import Debug.Trace

type DDExplicitStateSystem dd = ExplicitStateSystem Pident (DD.Val dd)    
type DDExplicitPred dd = Int -> Values (DD.Val dd) -> Bool

tightDDExplicitStateSystem :: (BuildDD dd,Monad m) => DDExplicitStateSystem dd -> m (DDExplicitStateSystem dd,Subst)
tightDDExplicitStateSystem (s :: DDExplicitStateSystem dd) = do
    let vars = exp_vars s
    let left = IntMap.preserveMissing
    let right = IntMap.traverseMissing $ \k x -> return $ IntSet.singleton $ DD.valToInt x
    let match = IntMap.zipWithMaybeAMatched $ \_ xs x -> return $ Just $ IntSet.insert (DD.valToInt x) xs
    let go acc (vs,_) = IntMap.merge left right match acc (intMapFromUVector vs)
    let bounds = IntMap.foldl go IntMap.empty (exp_states s)
    let (singles,compound) = IntMap.partition ((==1) . IntSet.size) bounds
    let (singlesubst :: IntMap (DD.Val dd)) = IntMap.map (DD.intToVal . popIntSet) singles
    let tonames im = vectorIndices vars `composeMapInt` im
    let retype VBool _ = VBool
        retype (VInt {}) js = VInt js
    let vars' = V.imapMaybe (\i (n,ty) -> fmap (\js -> (n,retype ty js)) $ IntMap.lookup i compound) vars    
    let states' = IntMap.map (UV.ifilter (\i _ -> IntMap.member i compound) >< id) (exp_states s)
    let s' = s { exp_vars = vars', exp_states = states' }
    let exprty VBool v = Pebool (DD.valToBool v)
        exprty (VInt {}) v = Peint (DD.valToInt v)
    let ss = K.foldlWithKey (\acc (n,ty) v -> Map.insert n (exprty ty v) acc) Map.empty (tonames singlesubst)
    return (s',ss)
    
explicitStateSystemToDD :: (BuildDD dd,Monad m) => (Pident -> Pident) -> DDExplicitStateSystem dd -> DDM m dd
explicitStateSystemToDD mapP s = identityReader $ do
    r <- Reader.ask
    ff <- DD.false
    tt <- DD.true
    names <- Reader.asks varNames
    let exp_map = mkExpMap names (V.map (mapP >< id) $ exp_vars s)
    let valueToDD exp_i v =
            let dd_i = unsafeIntLookupNote "explicitStateSystemToDD" exp_i exp_map
            in Reader.runReader (DD.var dd_i v) r
    let valuesToDD vs = UV.ifoldl (\acc i v -> flip Reader.runReader r $ DD.and acc (valueToDD i v)) tt vs
    let go acc (vs,_) = flip Reader.runReader r $ DD.or acc (valuesToDD vs)
    return $ IntMap.foldl go ff (exp_states s)
            

--evalExplicitStatesToCSV :: Ord n => FilePath -> (n -> String) -> ExplicitStates n -> (Values -> Bool) -> IO ()
--evalExplicitStatesToCSV csvfile pp s f = do
--    let (vars,tys) = V.unzip $ expss_vars s
--    let header = V.map pp vars `V.snoc` "output"
--    let showVal (ty,val) = case ty of { VInt _ -> show val; VBool -> show (intToBool val)}
--    let showVals vs = map showVal $ zip (V.toList tys) (UV.toList vs)
--    let mkRow vals = Map.fromList $ zip (V.toList header) $ showVals vals ++ [show $ f vals]
--    let rows = map mkRow $ HashSet.toList (expss_vals s)
--    BL.writeFile csvfile (Csv.encodeByName (V.map fromString header) rows)
    
--evalExplicitStatesToTableOri :: (Monad m,Ord n) => ExplicitStates n -> (Values -> Bool) -> m (Table (n,VarType))
--evalExplicitStatesToTableOri s f = do
--    let vars = expss_vars s
--    let mkRow vals = UV.toList $ vals 
--    let rowdata = HashSet.toList (expss_vals s)
--    let rows = map mkRow rowdata
--    let dta = M.fromLists' @M.U @M.Ix2 @Int M.Seq rows
--    let out = UV.fromList $ map f rowdata
--    return (vars,dta,out)
   
evalExplicitStatesToTable :: (MUV.Unbox base,Ord n) => ExplicitStates n base -> (Values base -> Bool) -> Table (n,VarType) base
evalExplicitStatesToTable s f = runST $ do
    let vars = (expss_vars s)
    let rows = expss_vals s
    let rowdata = HashSet.toList rows
    let numRows = HashSet.size rows
    dta <- M.stackSlicesM (M.Dim 2) $ map vectorToMassic1D rowdata
    
    iRow <- newSTRef 0
    mOut <- MUV.unsafeNew numRows
    forM_ rowdata $ \row -> do
        i <- readSTRef iRow
        MUV.unsafeWrite mOut i (f row)
        modifySTRef' iRow (+1)
    out <- UV.unsafeFreeze mOut
    
    let res = (vars,M.convert dta,out)
    --trace ("massiv\n"++show res) $
    return res
    
--evalExplicitStatesToTable :: Ord n => ExplicitStates n -> (Values -> Bool) -> Table (n,VarType)
--evalExplicitStatesToTable s f = runST $ trace ("start evalExplicitStatesToTable") $ do
--    let vars = (expss_vars s)
--    iRow <- newSTRef 0
--    jCol <- newSTRef 0
--    let rows = expss_vals s
--    let numRows = HashSet.size rows
--    let numCols = UV.length (popHashSet rows) + 1
--    mArr <- M.unsafeNew (M.Sz2 numRows numCols)
--    forM_ rows $ \row -> do
--        i <- readSTRef iRow
--        forM_ [0..numCols-1] $ \col -> do
--            let val = row `uvIndex` col
--            j <- readSTRef jCol
--            M.unsafeWrite mArr (M.Ix2 i j) val
--            modifySTRef' jCol (+1)
--        j <- readSTRef jCol
--        M.unsafeWrite mArr (M.Ix2 i j) (boolToInt $ f row)
--        modifySTRef' iRow (+1)
--        writeSTRef jCol 0
--    dta <- M.unsafeFreeze M.Seq mArr
--    return $ trace ("end evalExplicitStatesToTable") (vars,dta)

--evalExplicitStatesViewToTable :: (Monad m,Ord n) => ExplicitStatesView n -> (ValuesView -> Bool) -> m (Table (n,VarType))
--evalExplicitStatesViewToTable s f = do
--    let vars = V.fromList $ IntMap.elems $ expsv_vars s
--    let (maxCol,_) = IntMap.findMax $ expsv_vars s
--    let mkRow vals = IntMap.elems $ IntMap.insert (maxCol+1) (boolToInt $ f vals) vals
--    let rows = map mkRow $ HashSet.toList (expsv_vals s)
--    let dta = M.fromLists' @M.U @M.Ix2 @Int M.Seq rows
--    return (vars,dta)
--
vectorToMassic1D :: UV.Unbox a => UV.Vector a -> M.Array M.U M.Ix1 a
vectorToMassic1D xs = fromJustNote "vectorToMassic1D" $ M.castFromVector M.Seq (M.Sz1 $ UV.length xs) xs

--rowsToMassiv2D
--  :: (UV.Unbox e,Foldable t) => HashSet (UV.Vector e) -> M.Array M.U M.Ix2 e
--rowsToMassiv2D set = runST $ do
--    let rows = hashSet.size set
--    let cols = fromMaybe 0 (UV.length <$> HashSet.lookupMin set)
--    mArr <- A.newMArray (Sz2 rows cols)
--    forM_ (zip [0..] (Set.toAscList set)) $ \(i, vec) ->
--      forM_ [0 .. cols - 1] $ \j -> do
--        let val = vec VU.! j
--        writeM mArr (Ix2 i j) val
--    unsafeFreeze mArr
 