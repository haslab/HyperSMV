{-# LANGUAGE ViewPatterns, TupleSections, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}

module Transform.SmvToAlloy where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.List as List
import Data.Maybe
import Data.Char
import qualified Location as L
import Prettyprinter
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Typeable
import Data.Data

import Transform.Bpacked
import Transform.Bexpr
import Smv.Typing
import Smv.Packed
import Smv.Pretty
import Pretty
import Alloy.Syntax
import Smv.Syntax
import Utils

data DefineMode
    = AsPred 
    | AsField 
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

showDefineModes :: String
showDefineModes = show $ parens $ sepBy (pretty ",") $ map (pretty . show) [(minBound::DefineMode)..maxBound]

type UniqueName = String

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

runAlloyM :: AlloyM a -> a
runAlloyM m = State.evalState (unAlloyM m) st
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

smvToAlloy :: DefineMode -> PackedBmodule -> AlloyM Alloy
smvToAlloy defineMode (PackedBmodule moduleName vars defines init invar trans ltlspec) = do
    -- process variable declarations
    main <- newSigName (Pident moduleName [])
    State.modify $ \st -> st { main_ = main }
    mainFields <- varsToFields main (unpackPvars vars)
    -- processes defines
    defineFields <- case defineMode of
        AsPred -> definesToAlloyPreds (Map.toList defines) >> return []
        AsField -> definesToAlloyFields (Map.toList defines)
    let mainSig = StructSig False True Nothing [main] Nothing (mainFields++defineFields)
    -- processes other items
    initToAlloy init
    invarToAlloy invar
    transToAlloy trans
    -- generates alloy module
    opens <- State.gets imports_
    let true = Pred "true" [] [Expr1 OpNo ExprNone]
    let false = Pred "false" [] [Expr1 OpSome ExprNone]
    initDefs <- State.gets inits_
    invarDefs <- State.gets invars_
    transDefs <- State.gets transs_
    defineDefs <- State.gets defines_
    fsmDefs <- mkFSM
    boolDefs <- mkSigBool
    intDefs <- mkSigInts
    let items = [ItemComment "\n********** Alloy utilities **********\n"]
             ++ [ItemComment "\nBoolean signatures and operations\n"]++boolDefs++[ItemPred true,ItemPred false]
             ++ [ItemComment "\nInteger signatures and operations\n"]++intDefs
             ++ [ItemComment "\n********** Model starts here **********\n"]
             ++ [ItemComment "\nModel\n",ItemSig mainSig]
             ++ [ItemComment "\nInitial states\n"]++initDefs
             ++ [ItemComment "\nInvariants\n"]++invarDefs
             ++ [ItemComment "\nState transitions\n"]++transDefs
             ++ [ItemComment "\nState machine\n"]++fsmDefs
             ++ [ItemComment "\nAuxiliary model definitions\n"]++defineDefs
    return $ Alloy opens items

mkFSM :: AlloyM [Item]
mkFSM = do
    ns <- State.gets fsm_
    marg <- mainArg
    let w = VarExpr (fst marg)
    let call n = ApplyExpr (VarExpr n) [w]
    let fsmDefs = [ItemPred $ Pred "FSM" [marg] [ands $ map call $ Set.toList ns]]
    return fsmDefs

initToAlloy :: Bexpr -> AlloyM ()
initToAlloy e = do
    e' <- exprToAlloy Expression e
    st <- State.get
    predName <- newName (Pident ("init_"++show(length $ inits_ st)) []) Nothing
    marg <- mainArg
    State.modify $ \st -> st { inits_ = inits_ st ++ [ItemPred $ Pred predName [marg] [e']], fsm_ = Set.insert predName (fsm_ st) }
    
invarToAlloy :: Bexpr -> AlloyM ()
invarToAlloy e = do
    marg <- mainArg
    e' <- exprToAlloy Expression e
    st <- State.get
    predName <- newName (Pident ("invar"++show(length $ invars_ st)) []) Nothing
    State.modify $ \st -> st { invars_ = invars_ st ++ [ItemPred $ Pred predName [marg] [Expr1 OpAlways e']], fsm_ = Set.insert predName (fsm_ st) }
   
transToAlloy :: Bexpr -> AlloyM () 
transToAlloy e = do
    marg <- mainArg
    e' <- exprToAlloy Expression e
    st <- State.get
    predName <- newName (Pident ("trans"++show(length $ transs_ st)) []) Nothing
    State.modify $ \st -> st { transs_ = transs_ st ++ [ItemPred $ Pred predName [marg] [Expr1 OpAlways e']], fsm_ = Set.insert predName (fsm_ st) }

definesToAlloyPreds :: [(Pident,Bexpr)] -> AlloyM ()
definesToAlloyPreds [] = return ()
definesToAlloyPreds ds = do
    oks <- filterM (hasDeps) ds
    case oks of
        (ok@(n,e):_) -> do
            d' <- defineToAlloyPred ok
            State.modify $ \st -> st { defines_ = defines_ st ++ [ItemPred d'], decls_ = Map.insert n Expression (decls_ st) }
            definesToAlloyPreds (List.delete ok ds)
        [] -> do
            decls <- State.gets decls_
            error $ "cannot resolve defines \n" ++ unlines (map prettyprint ds) ++ "\n under \n" ++ unlines (map prettyprint $ Map.keys decls)
  where
    hasDeps :: (Pident,Bexpr) -> AlloyM Bool
    hasDeps (n,e) = liftM (bvarSet e `Set.isSubsetOf`) (State.gets (Map.keysSet . decls_))

defineToAlloyPred :: (Pident,Bexpr) -> AlloyM Pred
defineToAlloyPred (l,e) = do
    marg <- mainArg
    main <- State.gets main_
    l' <- newName l (Just main)
    e' <- exprToAlloy Expression e
    return $ Pred l' [marg] [e']

definesToAlloyFields :: [(Pident,Bexpr)] -> AlloyM [Field]
definesToAlloyFields [] = return []
definesToAlloyFields ds = do
    oks <- filterM (hasDeps) ds
    case oks of
        (ok@(n,e):_) -> do
            field' <- defineToAlloyField ok
            liftM (field':) $ definesToAlloyFields (List.delete ok ds)
        [] -> do
            decls <- State.gets decls_
            error $ "cannot resolve defines \n" ++ unlines (map prettyprint ds) ++ "\n under \n" ++ unlines (map prettyprint $ Map.keys decls)
  where
    hasDeps :: (Pident,Bexpr) -> AlloyM Bool
    hasDeps (n,e) = liftM (bvarSet e `Set.isSubsetOf`) (State.gets (Map.keysSet . decls_))

defineToAlloyField :: (Pident,Bexpr) -> AlloyM Field
defineToAlloyField (l,e) = do
    marg <- mainArg
    main <- State.gets main_
    l' <- newName l (Just main)
    State.modify $ \st -> st { decls_ = Map.insert l Value (decls_ st) }
    -- add invariant encoding the define
    invar' <- exprToAlloy Expression (Bop2 Pequiv (Bvar (l,False) VBool) e)
    predName <- newName (Pident ("define_"++prettyPident l) []) Nothing
    State.modify $ \st -> st { invars_ = invars_ st ++ [ItemPred $ Pred predName [marg] [Expr1 OpAlways invar']], fsm_ = Set.insert predName (fsm_ st) }
    -- return abstract field
    tt <- typeToSig VBool
    return $ Field True l' (Just MOne) $ Relation [(VarExpr tt,Nothing)]

expandArrays :: Pvar -> AlloyM [Pvar]
expandArrays (Pvar (Pident n dims) (Parray i j t)) = do
    vs <- forM [i..j] $ \k -> expandArrays $ Pvar (Pident n (dims++[Peint k])) t
    return $ concat vs
expandArrays pvar = return [pvar]

varsToFields :: String -> [Pvar] -> AlloyM [Field]
varsToFields main vs = do
    vs' <- liftM concat $ mapM expandArrays vs
    fields <- mapM (varToField main) vs'
    return fields

varToField :: String -> Pvar -> AlloyM Field
varToField main  (Pvar n t)  = do
    n' <- newName n (Just main)
    let ty = toVarType t
    tt <- typeToSig ty
    addTypeRestrictions main n' ty
    State.modify $ \st -> st { decls_ = Map.insert n (Value) (decls_ st) }
    return $ Field True n' (Just MOne) $ Relation [(VarExpr tt,Nothing)]

addTypeRestrictions :: String -> String -> VarType -> AlloyM ()
addTypeRestrictions main n (VBool) = return ()
addTypeRestrictions main n (VInt is) = do
    let eis = map intVal (IntSet.toList is)
    mn <- mainDot (Just main) $ VarExpr n
    let e = Expr2 mn OpIn $ unions eis
    marg <- mainArg
    predName <- newName (Pident ("range_"++n) []) Nothing
    State.modify $ \st -> st { invars_ = invars_ st ++ [ItemPred $ Pred predName [marg] [Expr1 OpAlways e]], fsm_ = Set.insert predName (fsm_ st) }

typeToSig :: VarType -> AlloyM UniqueName
typeToSig VBool = return boolName
typeToSig (VInt is) = do
    let nis = mkIntName is
    registerInts is
    State.modify $ \st -> st { ints_ = Map.insert nis is (ints_ st) }
    return nis

-- needed to distinguish how to handle boolean variables
data ExprMode
    = Value -- when generating values (int or bool)
    | Expression -- when generating boolean expressions
    deriving (Eq,Ord,Show)

exprToAlloy :: ExprMode -> Bexpr -> AlloyM Expr
exprToAlloy exprMode (Bvar (n,isNext) t) = do
    (n',main) <- getName n
    mn <- mainDot main $ if isNext then NextExpr n' else VarExpr n'
    declMode <- getDecl n
    if (declMode==exprMode)
        then return mn
        else case (t,declMode,exprMode) of
            (VBool,Value,Expression) -> do
                let true = boolVal True
                return (Expr2 mn OpEq true)
            _ -> error $ "cannot interpret variable " ++ prettyprint n  ++ " with " ++ show declMode ++ " as " ++ show exprMode
--exprToAlloy exprMode (Bvar (n,True) _) = case exprMode of
--    Value -> do
--        (n',main) <- getName n
--        mn <- mainDot main $ NextExpr n'
--        return mn
--    Expression -> error $ "cannot evaluate next in boolean expression mode for " ++ prettyprint n 
exprToAlloy exprMode (Bbool b) = case exprMode of
    Value -> return $ boolVal b
    Expression -> return $ ExprBool b
exprToAlloy exprMode (Bints js) = case exprMode of
    Value -> return $ unions $ map intVal (IntSet.toList js)
    Expression -> error $ "cannot evaluate int in boolean expression mode for " ++ show js
exprToAlloy Expression (vbvarin -> Just ((n,isNext),t,is)) = do
    (n',main) <- getName n
    mn <- mainDot main $ if isNext then NextExpr n' else VarExpr n'
    return $ mkOrIntAlloy mn t is
exprToAlloy exprMode (Bop1 o e1) = expr1ToAlloy exprMode o e1
exprToAlloy exprMode (Bop2 o e1 e2) = expr2ToAlloy exprMode o e1 e2
exprToAlloy exprMode (Bopn o es) = do
    es' <- mapHashSetM (exprToAlloy exprMode) es
    exprNToAlloy exprMode o es'

mkOrIntAlloy :: Expr -> VarType -> IntSet -> Expr
mkOrIntAlloy v t@(VInt ts) is
    | IntSet.size is == 0 = ExprBool False
    | is == ts = ExprBool True
    | IntSet.size (IntSet.difference ts is) < IntSet.size is = Expr1 OpNot $
        mkOrIntAlloy' (IntSet.toList $ IntSet.difference ts is)
    | otherwise = mkOrIntAlloy' (IntSet.toList is)
  where   
    mkOrIntAlloy' :: [Int] -> Expr
    mkOrIntAlloy' [i] = Expr2 v OpEq (intVal i)
    mkOrIntAlloy' is = Expr2 v OpIn (unions $ map intVal is)

mainDot :: Maybe String -> Expr -> AlloyM Expr
mainDot Nothing e = return e
mainDot (Just main) e = return $ Expr2 (VarExpr "W") OpComp e

expr1ToAlloy :: ExprMode -> Pop1 -> Bexpr -> AlloyM Expr
expr1ToAlloy exprMode Pnot e = do
    e' <- exprToAlloy exprMode e
    case exprMode of
        Value -> error $ "unsupported not value expr"
        Expression -> return (Expr1 OpNot e')
expr1ToAlloy exprMode o e = error $ "unsupported op expr" ++ show o

expr2ToAlloy :: ExprMode -> Pop2 -> Bexpr -> Bexpr -> AlloyM Expr
expr2ToAlloy exprMode Pneq e1 e2 = exprToAlloy exprMode (Bop1 Pnot $ Bop2 Peq e1 e2)
expr2ToAlloy exprMode op e1 e2 = case exprMode of
    Value -> do
        case varTypeOfBexpr (Bop2 op e1 e2) of
            VBool -> return ()
            VInt is -> registerInts is
        valueMode2ToAlloy op e1 e2
    Expression -> exprMode2ToAlloy op e1 e2

registerInts :: IntSet -> AlloyM ()
registerInts is = State.modify $ \st -> do
    let lis = IntSet.toList is
    st { min_int_ = minimum (min_int_ st : lis), max_int_ = maximum (max_int_ st : lis) }

exprMode2ToAlloy :: Pop2 -> Bexpr -> Bexpr -> AlloyM Expr
exprMode2ToAlloy Pin e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    return $ Expr2 e1' OpIn e2'
exprMode2ToAlloy Peq e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    return (Expr2 e1' OpEq e2')
exprMode2ToAlloy Pequiv e1 e2 = do
    e1' <- exprToAlloy Expression e1
    e2' <- exprToAlloy Expression e2
    return (Expr2 e1' OpIff e2')
exprMode2ToAlloy Pimplies e1 e2 = do
    e1' <- exprToAlloy Expression e1
    e2' <- exprToAlloy Expression e2
    return (Expr2 e1' OpImplies e2')
exprMode2ToAlloy Plt e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    getIntOp2 "lt" e1' e2'
exprMode2ToAlloy Pleq e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    getIntOp2 "leq" e1' e2'
exprMode2ToAlloy Pgt e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    getIntOp2 "gt" e1' e2'
exprMode2ToAlloy Pgeq e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    getIntOp2 "geq" e1' e2'
exprMode2ToAlloy op e1 e2 = error $ "unsupported expression mode for " ++ show op ++ " " ++ show e1 ++ " " ++ show e2
    
valueMode2ToAlloy :: Pop2 -> Bexpr -> Bexpr -> AlloyM Expr
valueMode2ToAlloy Pplus e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    getIntOp2 "plus" e1' e2'
valueMode2ToAlloy Pminus e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    getIntOp2 "minus" e1' e2'
valueMode2ToAlloy Ptimes e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    getIntOp2 "times" e1' e2'
valueMode2ToAlloy Punion e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    return $ unions [e1',e2']
--valueMode2ToAlloy B Peq e1 e2 = do
--    t <- typecheckExpr e1
--    e1' <- exprToAlloy (Value t) e1
--    e2' <- exprToAlloy (Value t) e2
--    case t of
--        B -> getBoolOp2 "eq" e1' e2'
--        I -> getIntBoolOp2 "eq" e1' e2'
valueMode2ToAlloy op e1 e2 = error $ "unsupported value mode for " ++ show op ++ " " ++ show e1 ++ " " ++ show e2

--getBoolOp1 :: String -> Expr -> AlloyM Expr
--getBoolOp1 op e1 = do
--    let opName = op++boolName
--    State.modify $ \st -> st { used_ops_ = Set.insert opName (used_ops_ st) }
--    return (ApplyExpr (VarExpr opName) [e1])
--
getBoolOp2 :: String -> Expr -> Expr -> AlloyM Expr
getBoolOp2 op e1 e2 = do
    let opName = op++boolName
    State.modify $ \st -> st { used_ops_ = Set.insert opName (used_ops_ st) }
    return (ApplyExpr (VarExpr opName) [e1,e1])

getIntOp2 :: String -> Expr -> Expr -> AlloyM Expr
getIntOp2 op e1 e2 = do
    let opName = op++intName
    State.modify $ \st -> st { used_ops_ = Set.insert opName (used_ops_ st) }
    return (ApplyExpr (VarExpr opName) [e1,e2])

--getIntBoolOp2 :: String -> Expr -> Expr -> AlloyM Expr
--getIntBoolOp2 op e1 e2 = do
--    let opName = op++intName++boolName
--    State.modify $ \st -> st { used_ops_ = Set.insert opName (used_ops_ st) }
--    return (ApplyExpr (VarExpr opName) [e1,e2])

valueOrsToAlloy :: [Expr] -> AlloyM Expr
valueOrsToAlloy [] = return $ boolVal True
valueOrsToAlloy [e] = return e
valueOrsToAlloy (e:es) = do
    es' <- valueOrsToAlloy es
    getBoolOp2 "or" e es'

valueAndsToAlloy :: [Expr] -> AlloyM Expr
valueAndsToAlloy [] = return $ boolVal False
valueAndsToAlloy [e] = return e
valueAndsToAlloy (e:es) = do
    es' <- valueAndsToAlloy es
    getBoolOp2 "and" e es'

exprNToAlloy :: ExprMode -> Popn -> HashSet Expr -> AlloyM Expr
exprNToAlloy exprMode Pand es = case exprMode of
    Value -> valueOrsToAlloy (HashSet.toList es)
    Expression -> return (ands $ HashSet.toList es)
exprNToAlloy exprMode Por es = case exprMode of
    Value -> valueAndsToAlloy (HashSet.toList es)
    Expression -> return (ors $ HashSet.toList es)
exprNToAlloy exprMode Pset es = case exprMode of
    Value -> return (unions $ HashSet.toList es)
    Expression -> error $ "unsupported pset boolean expression " ++ show es 

showInt :: Int -> String
showInt i | i >= 0 = show i
showInt i | i < 0 = "m"++show (-i)

mkSigBool :: AlloyM [Item]
mkSigBool = do
    let sig = ItemSig $ EnumSig boolName ["T","F"]
    let bs = [False,True]
    d1 <- genBoolDef   "or"    (orTT     bs)
    d2 <- genBoolDef   "and"   (andTT    bs)
    return (sig:d1++d2)
    
mkSigInts :: AlloyM [Item]
mkSigInts = do
    coreInt <- mkSigInt
    ints <- State.gets ints_
    let aliasInts = map (\(n,is) -> ItemSig $ DefSig n (unions $ map intVal $ IntSet.toList is)) (Map.toList ints)
    return $ coreInt ++ aliasInts
    
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

mkIntName :: IntSet -> UniqueName
mkIntName is = case isRange (IntSet.toList is) of
    Just (i,j) -> intName ++ "_" ++ show i ++ "_" ++ show j
    Nothing -> intName ++ IntSet.foldl (\s i -> s ++ "_" ++ showInt i) "" is

mainArg :: AlloyM (String,Relation)
mainArg = do
    main <- State.gets main_
    return ("W",Relation [(VarExpr main,Nothing)])

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

genOpArgs :: String -> Int -> [(String,Relation)]
genOpArgs typeName n = map (\i -> ("_i"++show i,simpleRelation typeName)) [1..n]

boolVal :: Bool -> Expr
boolVal True = VarExpr "T"
boolVal False = VarExpr "F"

intVal :: Int -> Expr
intVal n = VarExpr $ intValString n

intValString :: Int -> String
intValString n = intName ++ showInt n

-- has to start with upper letter
newSigName :: Pident -> AlloyM UniqueName
newSigName name = newName' name n Nothing
    where
    n = upper (flattenPident name)
    upper [] = "??"
    upper (x:xs) = toUpper x : xs

-- can start with lower letter
newName :: Pident -> Maybe String -> AlloyM UniqueName
newName p main = newName' p (flattenPident p) main

flattenPident :: Pident -> String
flattenPident (Pident n dims) = sanitize n ++ flatdims dims
    where
    flatdims [] = ""
    flatdims (d:ds) = "_" ++ prettyprint d ++ flatdims ds
    sanitize [] = []
    sanitize ('-':xs) = '_' : sanitize xs
    sanitize ('.':xs) = '_' : sanitize xs
    sanitize (x:xs) = x : sanitize xs

newName' :: Pident -> String -> Maybe String -> AlloyM UniqueName
newName' original n main = do
    ns <- State.gets names_
    if List.elem n (map fst $ Map.elems ns) -- if the proposed name already exists
        then newName' original (n++"_") main
        else do
            State.modify $ \st -> st { names_ = Map.insert original (n,main) (names_ st) }
            return n
    
getName :: Pident -> AlloyM (UniqueName,Maybe String)
getName n = do
    ns <- State.gets names_
    case Map.lookup n ns of
        Just (n',main) -> return (n',main)
        Nothing -> error $ "no name found for " ++ prettyprint n

getDecl :: Pident -> AlloyM ExprMode
getDecl n = do
    mb <- State.gets (Map.lookup n . decls_)
    case mb of
        Just exprMode -> return exprMode
        Nothing -> error $ "no declaration found for " ++ prettyprint n

type TT a = [[a]]

ltTT :: [Int] -> TT Int
ltTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 < _i2 ]

leqTT :: [Int] -> TT Int
leqTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 <= _i2 ]

gtTT :: [Int] -> TT Int
gtTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 > _i2 ]

geqTT :: [Int] -> TT Int
geqTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 >= _i2 ]

eqIntTT :: [Int] -> TT Int
eqIntTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 == _i2 ]

eqIntBoolTT :: [Int] -> [(Int,Int,Bool)]
eqIntBoolTT is = [ (_i1,_i2,_i3) | _i1 <- is, _i2 <- is, _i3 <- [False,True], (_i1 == _i2) == _i3 ]
    
plusTT :: [Int] -> TT Int
plusTT is = [ [_i1,_i2,_i3] | _i1 <- is, _i2 <- is, _i3 <- is, _i1 + _i2 == _i3 ]

minusTT :: [Int] -> TT Int
minusTT is = [ [_i1,_i2,_i3] | _i1 <- is, _i2 <- is, _i3 <- is, _i1 - _i2 == _i3 ]

timesTT :: [Int] -> TT Int
timesTT is = [ [_i1,_i2,_i3] | _i1 <- is, _i2 <- is, _i3 <- is, _i1 * _i2 == _i3 ]

orTT :: [Bool] -> TT Bool
orTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 || _i2 ]

andTT :: [Bool] -> TT Bool
andTT is = [ [_i1,_i2] | _i1 <- is, _i2 <- is, _i1 && _i2 ]

ttIntExpr :: TT Int -> Expr
ttIntExpr tt = unions (map go tt)
    where go = arrows . map intVal
    
ttBoolExpr :: TT Bool -> Expr
ttBoolExpr tt = unions (map go tt)
    where go = arrows . map boolVal

compTTExpr :: TT Int -> Expr
compTTExpr tt = Expr2 i12 OpIn tte
    where
    tte = ttIntExpr tt
    i12 = arrows (genVarArgs 2)
    
arithTTExpr :: TT Int -> Expr
arithTTExpr tt = ApplyExpr tte (genVarArgs 2)
    where
    tte = ttIntExpr tt

boolTTExpr :: TT Bool -> Expr
boolTTExpr tt = ApplyExpr tte (genVarArgs 2)
    where
    tte = ttBoolExpr tt

genVarArgs :: Int -> [Expr]
genVarArgs n = map (\i -> VarExpr $ "_i"++show i) [1..n]
