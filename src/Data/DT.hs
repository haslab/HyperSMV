
-- | Decision tree classifier with int variables and boolean output (represented as an int)

module Data.DT where

import qualified Data.List as List
import Data.Ord
import Data.Maybe

import Data.Massiv.Array
import Data.Massiv.Array.Unsafe
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV

import Utils

type Label = Bool -- actually a bool
type Table a val = (V.Vector a,Array U Ix2 val,UV.Vector Bool) -- a matrix of int values with row names + an output column
type View a val = (Table a val,UV.Vector Int) -- a table and a list of selected rows
type Row a val = (Table a val,Int) -- a view and a selected row
type Output a val = View a val -- a view (of which we only want the output column)

class (Show a,Eq f,Show f) => IsFeature a f val where
    allFeatures :: Table a val -> [(f,Double)] -- features with priority
    evalFeature :: f -> Row a val -> Bool

data DecisionTree f
  = Leaf Bool
  | Node f (DecisionTree f) (DecisionTree f)
  deriving Show

{-# INLINE tableView #-}
tableView :: Table a val -> View a val
tableView t@(ns,dta,out) = (t,UV.generate i id)
    where
    Sz2 i j = size dta

{-# INLINE isNullView #-}
isNullView :: View a val -> Bool
isNullView (t,rows) = UV.null rows

{-# INLINE sizeView #-}
sizeView :: View a val -> Int
sizeView (t,rows) = UV.length rows

{-# INLINE sizeOutput #-}
sizeOutput :: Output a val -> Int
sizeOutput v = sizeView v

{-# INLINE allOutput #-}
allOutput :: (Bool -> Bool) -> Output a val -> Bool
allOutput p ((ns,t,out),rows) = UV.all (\row -> p (uvIndex "allOutput" out row)) rows

{-# INLINE filterTrues #-}
filterTrues :: Output a val -> Output a val
filterTrues ((ns,t,out),rows) = ((ns,t,out),rows')
    where
    rows' = UV.filter (\row -> uvIndex "filterTrues" out row) rows

{-# INLINE getOutput #-}
getOutput :: View a val -> Output a val
getOutput v = v

-- Entropy calculation
entropy :: Output a val -> Double
entropy labels =
  let p = fromIntegral (sizeOutput (filterTrues labels)) / fromIntegral (sizeOutput labels)
  in if p == 0 || p == 1 then 0 else -p * logBase 2 p - (1 - p) * logBase 2 (1 - p)

-- Split dataset by feature
splitByFeature :: IsFeature a f val => f -> View a val -> (View a val,View a val)
splitByFeature f (t,rows) = ((t,l),(t,r))
    where
    (l,r) = UV.partition (\row -> evalFeature f (t,row)) rows

-- Information Gain computation
infoGain :: View a val -> (View a val,View a val) -> Double
infoGain total (left, right) =
  let totalEntropy = entropy (getOutput total)
      lRatio = fromIntegral (sizeView left) / fromIntegral (sizeView total)
      rRatio = fromIntegral (sizeView right) / fromIntegral (sizeView total)
  in totalEntropy - (lRatio * entropy (getOutput left) + rRatio * entropy (getOutput right))

-- Find the best feature based on Information Gain (with priorities)
bestFeature :: IsFeature a f val => [(f,Double)] -> View a val -> Maybe (f,Double)
bestFeature [] dataset = Nothing
bestFeature features dataset = Just $
  let score (c,priority) = realToFrac priority * infoGain dataset (splitByFeature c dataset)
  in  maximumOn score features

-- Majority class label
majorityLabel :: View a val -> Label
majorityLabel dp = 
  let out = getOutput dp
      trues = sizeOutput (filterTrues out)
      falses = sizeOutput out - trues
  in (trues >= falses)

-- Recursive ID3 algorithm
id3 :: IsFeature a f val => [(f,Double)] -> View a val -> (DecisionTree f)
id3 fs dataset
  | isNullView dataset = Leaf True -- if no data, return True as fallback
  | allOutput (==True) (getOutput dataset) = Leaf True  -- all True labels
  | allOutput (==False) (getOutput dataset) = Leaf False -- all False labels
  | otherwise = case bestFeature fs dataset of
      Nothing -> error $ "imprecise\n" ++ show fs ++ "\n" ++ show (snd $ dataset) --Leaf (majorityLabel dataset)  -- if no split possible, return majority label
      Just fi@(f,_) ->
        let (left, right) = splitByFeature f dataset
        in Node f (id3 (deleteOn fst fi fs) left) (id3 (deleteOn fst fi fs) right)

{-# INLINE classifyId3 #-}
classifyId3 :: IsFeature a f val => Table a val -> DecisionTree f
classifyId3 dataset = id3 (allFeatures dataset) (tableView dataset)

