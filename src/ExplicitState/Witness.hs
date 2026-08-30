-- | Witness search over an already-built explicit-state system.
module ExplicitState.Witness where

import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.List as List
import qualified Data.Graph as Graph
import Safe

import ExplicitState.Syntax
import ExplicitState.Eval

-- | Find a lasso-shaped run realising a prefix/lasso predicate word.
findTrace :: ([DDExplicitPred dd],[DDExplicitPred dd]) -> DDExplicitStateSystem dd -> Maybe ([Int],[Int])
findTrace (prefix,lasso) exp
    | null lasso = Nothing
    | otherwise = do
        (members,a,u,v) <- headMay targets
        let loopNodes = bfsIn members v a ++ drop 1 (bfsIn members a u)
        let stem = backtrackTop [] v
        return (map stateOf (Prelude.init stem),map stateOf loopNodes)
  where
    plen = length prefix
    llen = length lasso
    posCount = plen + llen
    predAt = IntMap.fromList (zip [0..] (prefix ++ lasso))
    stride = case IntMap.lookupMax (exp_states exp) of
        Nothing -> 1
        Just (k,_) -> k + 1
    stateOf node = node `Prelude.mod` stride
    posOf node = node `Prelude.div` stride
    valid pos i = case IntMap.lookup i (exp_states exp) of
        Nothing -> False
        Just (vals,_) -> (predAt IntMap.! pos) i vals
    -- successors of a node, with a wrap flag.
    succs node =
        let pos = posOf node
            i = stateOf node
            nexts = IntSet.toList $ snd $ exp_state exp i
            isLast = pos == posCount - 1
            advPos = if isLast then plen else pos + 1
            advs = [ (advPos * stride + j,isLast) | j <- nexts, valid advPos j ]
            stutters = if isLast && llen == 1 then []
                       else [ (pos * stride + j,False) | j <- nexts, valid pos j ]
        in advs ++ stutters
    -- reachability from the initial layer; any spanning tree serves as parent structure
    roots = [ i | i <- IntSet.toList (exp_inits exp), valid 0 i ]
    parents :: IntMap Int
    parents = grow (IntMap.fromList [ (r,r) | r <- roots ]) roots
      where
        grow par [] = par
        grow par (x:queue) =
            let fresh = [ y | (y,_) <- succs x, Prelude.not (IntMap.member y par) ]
                (par',added) = List.foldl'
                    (\(m,acc) y -> if IntMap.member y m then (m,acc) else (IntMap.insert y x m,y:acc))
                    (par,[]) fresh
            in grow par' (added ++ queue)
    backtrackTop acc x | parents IntMap.! x == x = x : acc
                       | otherwise = backtrackTop (x : acc) (parents IntMap.! x)
    -- SCCs of the reachable subgraph; singletons only count when self-looping 
    sccs :: [[Int]]
    sccs = [ vs | Graph.CyclicSCC vs <- Graph.stronglyConnComp
                    [ (node,node,map fst (succs node)) | node <- IntMap.keys parents ] ]
    targets =
        [ (members,a,u,v)
        | scc <- sccs
        , let members = IntSet.fromList scc
        , (u,v) : _ <- [ [ (u,v) | u <- scc, (v,True) <- succs u, IntSet.member v members ] ]
        , a : _ <- [ case exp_accepting exp of
                        Nothing -> [v]
                        Just accs -> [ w | w <- scc, IntSet.member (stateOf w) accs ] ]
        ]
    -- BFS from src to dst restricted to one SCC; returns the node path src..dst inclusive
    bfsIn members src dst
        | src == dst = [src]
        | otherwise = go (IntMap.singleton src src) [src]
      where
        go _ [] = Prelude.error "findTrace: strongly connected component was not"
        go par (x:queue)
            | x == dst = back par [] dst
            | otherwise =
                let fresh = [ y | (y,_) <- succs x, IntSet.member y members
                                , Prelude.not (IntMap.member y par) ]
                    par' = List.foldl' (\m y -> IntMap.insert y x m) par fresh
                in go par' (queue ++ fresh)
        back par acc x | par IntMap.! x == x = x : acc
                       | otherwise = back par (x : acc) (par IntMap.! x)


-- | Find any accepting lasso-shaped run of the system.
findAnyTrace :: DDExplicitStateSystem dd -> Maybe ([Int],[Int])
findAnyTrace = findTrace ([],[\i vals -> True])

