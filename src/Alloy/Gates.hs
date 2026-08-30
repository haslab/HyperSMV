-- | The Alloy-emission monad and utilities.
module Alloy.Gates where

import Control.Monad
import Control.Monad.State (State(..))
import qualified Control.Monad.State as State
import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.List as List
import Data.Char
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet

import Pretty
import Smv.Syntax
import Smv.Pretty ()
import Alloy.Syntax
import Utils

-- | A name unique within the emitted module.
type UniqueName = String

-- | Needed to distinguish how to handle boolean variables
data ExprMode
    = Value -- when generating values (int or bool)
    | Expression -- when generating boolean expressions
    deriving (Eq,Ord,Show)

-- | Alloy-emission state.
data AlloySt = AlloySt
    { main_ :: UniqueName
    , names_ :: Map Pident (UniqueName,Maybe String)
    , imports_ :: [Import]
    , min_int_ :: Int
    , max_int_ :: Int
    , ints_ :: Map String IntSet
    , inits_ :: [Item]
    , invars_ ::[Item]
    , transs_ :: [Item]
    , fsm_    :: Set UniqueName
    , defines_ :: [Item]
    , decls_ :: Map Pident ExprMode -- defined variables
    , used_ops_ :: Set String -- used bool/int operations
    }

-- | The Alloy-emission monad.
newtype AlloyM a = AlloyM { unAlloyM :: State AlloySt a }

instance Functor AlloyM where
    fmap f (AlloyM m) = AlloyM $ fmap f m
instance Applicative AlloyM where
    pure = return
    mf <*> ma = mf >>= \f -> ma >>= \a -> return (f a)
instance Monad AlloyM where
    (AlloyM m) >>= f = AlloyM $ m >>= unAlloyM . f
    return = AlloyM . return
instance State.MonadState AlloySt AlloyM where
    state = AlloyM . State.state
instance MonadFail AlloyM where
    fail msg = error msg

boolName = "B"
intName = "I"

-- | Run an Alloy-emission computation.
runAlloyM :: AlloyM a -> a
runAlloyM = fst . runAlloyM'

-- | Run an Alloy-emission computation, also returning its final state -- needed when a caller
-- (the multi-model formula translator) must look up names/decls after the fact, once per model.
runAlloyM' :: AlloyM a -> (a,AlloySt)
runAlloyM' m = State.runState (unAlloyM m) st
    where
    intOps = map (++intName) ["plus","minus","times","lt","leq","gt","geq","eq"]
    st = AlloySt
        { names_ = Map.fromList $ map (\x -> (Pident x [],(x,Nothing))) (["W","FSM","true","false",boolName,"T","F"]++[intName]++intOps++["_i1","_i2"])
        , imports_ = []
        , min_int_ = 0
        , max_int_ = 0
        , ints_ = Map.empty
        , inits_ = []
        , invars_ = []
        , transs_ = []
        , defines_ = []
        , decls_ = Map.empty
        , used_ops_ = Set.empty
        , main_ = ""
        , fsm_ = Set.empty
        }

-- | Render an int as an Alloy-safe fragment.
showInt :: Int -> String
showInt i | i >= 0 = show i
showInt i | i < 0 = "m"++show (-i)

-- | Emit the boolean signature and operators.
mkSigBool :: AlloyM [Item]
mkSigBool = do
    let sig = ItemSig $ EnumSig boolName ["T","F"]
    let bs = [False,True]
    d1 <- genBoolDef   "or"    (orTT     bs)
    d2 <- genBoolDef   "and"   (andTT    bs)
    return (sig:d1++d2)
    
-- | Emit the integer signatures.
mkSigInts :: AlloyM [Item]
mkSigInts = do
    coreInt <- mkSigInt
    ints <- State.gets ints_
    let aliasInts = map (\(n,is) -> ItemSig $ DefSig n (unions $ map intVal $ IntSet.toList is)) (Map.toList ints)
    return $ coreInt ++ aliasInts
    
-- | Emit the core integer signature and operators.
mkSigInt :: AlloyM [Item]
mkSigInt = do
    i <- State.gets (min_int_)
    j <- State.gets (max_int_)
    let is = [i..j]
    ints <- forM is $ \n -> do
        let VarExpr vn = intVal n
        newSigName $ Pident vn []
    -- abstract sig I {}
    let asig = ItemSig $ StructSig True False Nothing [intName] Nothing []
    -- one sig I1, I2, I3, I4, I5 extends I {}
    let sigs = ItemSig $ StructSig False False (Just MOne) (map intValString is) (Just intName) []
    d1 <-  genCompDef   "lt"    (ltTT        is)
    d2 <-  genCompDef   "leq"   (leqTT       is)
    d3 <-  genCompDef   "gt"    (gtTT        is)
    d4 <-  genCompDef   "geq"   (geqTT       is)
    d5 <-  genCompDef   "eq"    (eqIntTT     is)
    d6 <-  genArithDef  "plus"  (plusTT      is)
    d7 <-  genArithDef  "minus" (minusTT     is)
    d8 <-  genArithDef  "times" (timesTT     is)
    return (asig:sigs:d1++d2++d3++d4++d5++d6++d7++d8) 

-- | A unique name for an integer set.
mkIntName :: IntSet -> UniqueName
mkIntName is = case isRange (IntSet.toList is) of
    Just (i,j) -> intName ++ "_" ++ show i ++ "_" ++ show j
    Nothing -> intName ++ IntSet.foldl (\s i -> s ++ "_" ++ showInt i) "" is

-- | Emit a comparison operator's definition, if used.
genCompDef :: String -> TT Int -> AlloyM [Item]
genCompDef op tt = do
    main <- State.gets main_
    let opname = op++intName
    used <- State.gets (Set.member opname . used_ops_)
    if used then do
        let opRel = compTTExpr tt
        let opDef = Pred opname (genOpArgs intName 2) [opRel]
        return [ItemPred opDef]
    else return []

-- | Emit an arithmetic operator's definition, if used.
genArithDef :: String -> TT Int -> AlloyM [Item]
genArithDef op tt = do
    main <- State.gets main_
    let opname = op++intName
    used <- State.gets (Set.member opname . used_ops_)
    if used then do
        let opRel = arithTTExpr tt
        let opDef = Fun opname (genOpArgs intName 2) (simpleRelation intName) opRel
        return [ItemFun opDef]
    else return []
    
-- | Emit a boolean operator's definition, if used.
genBoolDef :: String -> TT Bool -> AlloyM [Item]
genBoolDef op tt = do
    main <- State.gets main_
    let opname = op++boolName
    used <- State.gets (Set.member opname . used_ops_)
    if used then do
        let opRel = boolTTExpr tt
        let opDef = Fun opname (genOpArgs boolName 2) (simpleRelation boolName) opRel
        return [ItemFun opDef]
    else return []

-- | n numbered argument declarations of a type.
genOpArgs :: String -> Int -> [(String,Relation)]
genOpArgs typeName n = map (\i -> ("_i"++show i,simpleRelation typeName)) [1..n]

-- | The Alloy expression for a boolean constant.
boolVal :: Bool -> Expr
boolVal True = VarExpr "T"
boolVal False = VarExpr "F"

-- | The Alloy expression for an integer constant.
intVal :: Int -> Expr
intVal n = VarExpr $ intValString n

-- | An integer constant's signature name.
intValString :: Int -> String
intValString n = intName ++ showInt n

-- | Allocate a fresh capitalised signature name.
newSigName :: Pident -> AlloyM UniqueName
newSigName name = newName' name n Nothing
    where
    n = upper (flattenPident name)
    upper [] = "??"
    upper (x:xs) = toUpper x : xs

-- can start with lower letter
newName :: Pident -> Maybe String -> AlloyM UniqueName
newName p main = newName' p (flattenPident p) main

-- | Render a 'Pident' as a flat identifier string.
flattenPident :: Pident -> String
flattenPident (Pident n dims) = sanitize n ++ flatdims dims
    where
    flatdims [] = ""
    flatdims (d:ds) = "_" ++ prettyprint d ++ flatdims ds
    sanitize [] = []
    sanitize ('-':xs) = '_' : sanitize xs
    sanitize ('.':xs) = '_' : sanitize xs
    sanitize (x:xs) = x : sanitize xs

-- | Allocate a fresh unique name.
newName' :: Pident -> String -> Maybe String -> AlloyM UniqueName
newName' original n main = do
    ns <- State.gets names_
    if List.elem n (map fst $ Map.elems ns) -- if the proposed name already exists
        then newName' original (n++"_") main
        else do
            State.modify $ \st -> st { names_ = Map.insert original (n,main) (names_ st) }
            return n
    
-- | Look up a variable's allocated name.
getName :: Pident -> AlloyM (UniqueName,Maybe String)
getName n = do
    ns <- State.gets names_
    case Map.lookup n ns of
        Just (n',main) -> return (n',main)
        Nothing -> error $ "no name found for " ++ prettyprint n

-- | Look up a variable's declared expression mode.
getDecl :: Pident -> AlloyM ExprMode
getDecl n = do
    mb <- State.gets (Map.lookup n . decls_)
    case mb of
        Just exprMode -> return exprMode
        Nothing -> error $ "no declaration found for " ++ prettyprint n

-- | A truth table of satisfying tuples.
type TT a = [[a]]

-- | Truth table for integer less-than.
ltTT :: [Int] -> TT Int
ltTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 < _i2 ]

-- | Truth table for integer less-or-equal.
leqTT :: [Int] -> TT Int
leqTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 <= _i2 ]

-- | Truth table for integer greater-than.
gtTT :: [Int] -> TT Int
gtTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 > _i2 ]

-- | Truth table for integer greater-or-equal.
geqTT :: [Int] -> TT Int
geqTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 >= _i2 ]

-- | Truth table for integer equality.
eqIntTT :: [Int] -> TT Int
eqIntTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 == _i2 ]


-- | Truth table for integer addition.
plusTT :: [Int] -> TT Int
plusTT is = [ [_i1,_i2,_i3] | _i1 <- is, _i2 <- is, _i3 <- is, _i1 + _i2 == _i3 ]

-- | Truth table for integer subtraction.
minusTT :: [Int] -> TT Int
minusTT is = [ [_i1,_i2,_i3] | _i1 <- is, _i2 <- is, _i3 <- is, _i1 - _i2 == _i3 ]

-- | Truth table for integer multiplication.
timesTT :: [Int] -> TT Int
timesTT is = [ [_i1,_i2,_i3] | _i1 <- is, _i2 <- is, _i3 <- is, _i1 * _i2 == _i3 ]

-- | Truth table for boolean or.
orTT :: [Bool] -> TT Bool
orTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 || _i2 ]

-- | Truth table for boolean and.
andTT :: [Bool] -> TT Bool
andTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 && _i2 ]

-- | Render an integer truth table as a union.
ttIntExpr :: TT Int -> Expr
ttIntExpr tt = unions (map go tt)
    where go = arrows . map intVal
    
-- | Render a boolean truth table as a union.
ttBoolExpr :: TT Bool -> Expr
ttBoolExpr tt = unions (map go tt)
    where go = arrows . map boolVal

-- | Render a comparison table as a predicate body.
compTTExpr :: TT Int -> Expr
compTTExpr tt = Expr2 i12 OpIn tte
    where
    tte = ttIntExpr tt
    i12 = arrows (genVarArgs 2)
    
-- | Render an arithmetic table as a function body.
arithTTExpr :: TT Int -> Expr
arithTTExpr tt = ApplyExpr tte (genVarArgs 2)
    where
    tte = ttIntExpr tt

-- | Render a boolean-op table as a function body.
boolTTExpr :: TT Bool -> Expr
boolTTExpr tt = ApplyExpr tte (genVarArgs 2)
    where
    tte = ttBoolExpr tt

-- | n numbered argument variables.
genVarArgs :: Int -> [Expr]
genVarArgs n = map (\i -> VarExpr $ "_i"++show i) [1..n]

