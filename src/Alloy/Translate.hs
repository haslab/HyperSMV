-- | Translate an SMV module into an Alloy model, and a HyperLTL formula into an Alloy check block.
module Alloy.Translate where

import Control.Monad
import qualified Control.Monad.State as State
import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.HashSet (HashSet(..))
import qualified Data.HashSet as HashSet
import Data.List as List
import Data.IntSet (IntSet(..))
import qualified Data.IntSet as IntSet
import Data.Typeable
import Data.Data
import Prettyprinter

import Transform.Bexpr.Packed
import Transform.Bexpr
import Smv.Typing
import Smv.Packed
import Smv.Pretty
import Pretty
import Alloy.Syntax
import Alloy.Gates
import Smv.Syntax
import Utils

-- * SMV translation

-- | How a define is translated: predicate or field.
data DefineMode
    = AsPred
    | AsField
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

-- | 'DefineMode' constructor names for CLI help.
showDefineModes :: String
showDefineModes = show $ parens $ sepBy (pretty ",") $ map (pretty . show) [(minBound::DefineMode)..maxBound]

-- | Translate a packed SMV module into an Alloy module.
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

-- | Emit the FSM predicate over all registered predicates.
mkFSM :: AlloyM [Item]
mkFSM = do
    ns <- State.gets fsm_
    marg <- mainArg
    let w = VarExpr (fst marg)
    let call n = ApplyExpr (VarExpr n) [w]
    let fsmDefs = [ItemPred $ Pred "FSM" [marg] [ands $ map call $ Set.toList ns]]
    return fsmDefs

-- | Translate init into a named predicate.
initToAlloy :: Bexpr -> AlloyM ()
initToAlloy e = do
    e' <- exprToAlloy Expression e
    st <- State.get
    predName <- newName (Pident ("init_"++show(length $ inits_ st)) []) Nothing
    marg <- mainArg
    State.modify $ \st -> st { inits_ = inits_ st ++ [ItemPred $ Pred predName [marg] [e']], fsm_ = Set.insert predName (fsm_ st) }

-- | Translate invar into an always-quantified predicate.
invarToAlloy :: Bexpr -> AlloyM ()
invarToAlloy e = do
    marg <- mainArg
    e' <- exprToAlloy Expression e
    st <- State.get
    predName <- newName (Pident ("invar"++show(length $ invars_ st)) []) Nothing
    State.modify $ \st -> st { invars_ = invars_ st ++ [ItemPred $ Pred predName [marg] [Expr1 OpAlways e']], fsm_ = Set.insert predName (fsm_ st) }

-- | Translate trans into an always-quantified predicate.
transToAlloy :: Bexpr -> AlloyM ()
transToAlloy e = do
    marg <- mainArg
    e' <- exprToAlloy Expression e
    st <- State.get
    predName <- newName (Pident ("trans"++show(length $ transs_ st)) []) Nothing
    State.modify $ \st -> st { transs_ = transs_ st ++ [ItemPred $ Pred predName [marg] [Expr1 OpAlways e']], fsm_ = Set.insert predName (fsm_ st) }

-- | Translate defines into predicates, in dependency order.
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

-- | Translate one define into a predicate.
defineToAlloyPred :: (Pident,Bexpr) -> AlloyM Pred
defineToAlloyPred (l,e) = do
    marg <- mainArg
    main <- State.gets main_
    l' <- newName l (Just main)
    e' <- exprToAlloy Expression e
    return $ Pred l' [marg] [e']

-- | Translate defines into fields, in dependency order.
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

-- | Translate one define into a field plus invariant.
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

-- | Expand an array variable into one declaration per index.
expandArrays :: Pvar -> AlloyM [Pvar]
expandArrays (Pvar (Pident n dims) (Parray i j t)) = do
    vs <- forM [i..j] $ \k -> expandArrays $ Pvar (Pident n (dims++[Peint k])) t
    return $ concat vs
expandArrays pvar = return [pvar]

-- | Translate variable declarations into fields.
varsToFields :: String -> [Pvar] -> AlloyM [Field]
varsToFields main vs = do
    vs' <- liftM concat $ mapM expandArrays vs
    fields <- mapM (varToField main) vs'
    return fields

-- | Translate one variable declaration into a field.
varToField :: String -> Pvar -> AlloyM Field
varToField main  (Pvar n t)  = do
    n' <- newName n (Just main)
    let ty = toVarType t
    tt <- typeToSig ty
    addTypeRestrictions main n' ty
    State.modify $ \st -> st { decls_ = Map.insert n (Value) (decls_ st) }
    return $ Field True n' (Just MOne) $ Relation [(VarExpr tt,Nothing)]

-- | Register an integer field's value-range invariant.
addTypeRestrictions :: String -> String -> VarType -> AlloyM ()
addTypeRestrictions main n (VBool) = return ()
addTypeRestrictions main n (VInt is) = do
    let eis = map intVal (IntSet.toList is)
    mn <- mainDot (Just main) $ VarExpr n
    let e = Expr2 mn OpIn $ unions eis
    marg <- mainArg
    predName <- newName (Pident ("range_"++n) []) Nothing
    State.modify $ \st -> st { invars_ = invars_ st ++ [ItemPred $ Pred predName [marg] [Expr1 OpAlways e]], fsm_ = Set.insert predName (fsm_ st) }

-- | The signature name for a variable type.
typeToSig :: VarType -> AlloyM UniqueName
typeToSig VBool = return boolName
typeToSig (VInt is) = do
    let nis = mkIntName is
    registerInts is
    State.modify $ \st -> st { ints_ = Map.insert nis is (ints_ st) }
    return nis

-- | Translate a boolean expression into Alloy.
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

-- | Render an integer-membership test compactly.
mkOrIntAlloy :: Expr -> VarType -> IntSet -> Expr
mkOrIntAlloy v t@(VInt ts) is
    | IntSet.size is == 0 = ExprBool False
    | is == ts = ExprBool True
    | IntSet.size (IntSet.difference ts is) < IntSet.size is = Expr1 OpNot $
        mkInEqAlloy v (unions $ map intVal $ IntSet.toList $ IntSet.difference ts is)
    | otherwise = mkInEqAlloy v (unions $ map intVal $ IntSet.toList is)
mkOrIntAlloy v t is = error $ "mkOrIntAlloy: " ++ show v ++ " " ++ show t ++ " " ++ show is

-- | Membership test: equality against a single value, 'in' against a union of several.
mkInEqAlloy :: Expr -> Expr -> Expr
mkInEqAlloy e1 e2@(Expr2 _ OpUnion _) = Expr2 e1 OpIn e2
mkInEqAlloy e1 e2 = Expr2 e1 OpEq e2

-- | Prefix an expression with the main-signature dot.
mainDot :: Maybe String -> Expr -> AlloyM Expr
mainDot Nothing e = return e
mainDot (Just main) e = return $ Expr2 (VarExpr "W") OpComp e

-- | Translate a unary operator expression.
expr1ToAlloy :: ExprMode -> Pop1 -> Bexpr -> AlloyM Expr
expr1ToAlloy exprMode Pnot e = do
    e' <- exprToAlloy exprMode e
    case exprMode of
        Value -> error $ "unsupported not value expr"
        Expression -> return (Expr1 OpNot e')
expr1ToAlloy exprMode o e = error $ "unsupported op expr" ++ show o

-- | Translate a binary operator expression.
expr2ToAlloy :: ExprMode -> Pop2 -> Bexpr -> Bexpr -> AlloyM Expr
expr2ToAlloy exprMode Pneq e1 e2 = exprToAlloy exprMode (Bop1 Pnot $ Bop2 Peq e1 e2)
expr2ToAlloy exprMode op e1 e2 = case exprMode of
    Value -> do
        case varTypeOfBexpr (Bop2 op e1 e2) of
            VBool -> return ()
            VInt is -> registerInts is
        valueMode2ToAlloy op e1 e2
    Expression -> exprMode2ToAlloy op e1 e2

-- | Extend the tracked integer range.
registerInts :: IntSet -> AlloyM ()
registerInts is = State.modify $ \st -> do
    let lis = IntSet.toList is
    st { min_int_ = minimum (min_int_ st : lis), max_int_ = maximum (max_int_ st : lis) }

-- | Translate a binary comparison operator.
exprMode2ToAlloy :: Pop2 -> Bexpr -> Bexpr -> AlloyM Expr
exprMode2ToAlloy Pin e1 e2 = do
    e1' <- exprToAlloy (Value) e1
    e2' <- exprToAlloy (Value) e2
    return $ mkInEqAlloy e1' e2'
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

-- | Translate a binary arithmetic operator.
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

valueMode2ToAlloy op e1 e2 = error $ "unsupported value mode for " ++ show op ++ " " ++ show e1 ++ " " ++ show e2

-- | Apply a boolean operator, marking it used.
getBoolOp2 :: String -> Expr -> Expr -> AlloyM Expr
getBoolOp2 op e1 e2 = do
    let opName = op++boolName
    State.modify $ \st -> st { used_ops_ = Set.insert opName (used_ops_ st) }
    return (ApplyExpr (VarExpr opName) [e1,e1])

-- | Apply an integer operator, marking it used.
getIntOp2 :: String -> Expr -> Expr -> AlloyM Expr
getIntOp2 op e1 e2 = do
    let opName = op++intName
    State.modify $ \st -> st { used_ops_ = Set.insert opName (used_ops_ st) }
    return (ApplyExpr (VarExpr opName) [e1,e2])

-- | Fold value-mode expressions with boolean-or.
valueOrsToAlloy :: [Expr] -> AlloyM Expr
valueOrsToAlloy [] = return $ boolVal True
valueOrsToAlloy [e] = return e
valueOrsToAlloy (e:es) = do
    es' <- valueOrsToAlloy es
    getBoolOp2 "or" e es'

-- | Fold value-mode expressions with boolean-and.
valueAndsToAlloy :: [Expr] -> AlloyM Expr
valueAndsToAlloy [] = return $ boolVal False
valueAndsToAlloy [e] = return e
valueAndsToAlloy (e:es) = do
    es' <- valueAndsToAlloy es
    getBoolOp2 "and" e es'

-- | Translate an n-ary and/or/set expression.
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

-- | The standard 'W : Main' argument declaration.
mainArg :: AlloyM (String,Relation)
mainArg = do
    main <- State.gets main_
    return ("W",Relation [(VarExpr main,Nothing)])

-- * Formula translation

-- | A model's registered names/decls plus its Alloy sig alias.
data ModelCtx = ModelCtx
    { mctxAlias :: Maybe String
    , mctxNames :: Map Pident (UniqueName,Maybe String)
    , mctxDecls :: Map Pident ExprMode
    }

-- | A model's Alloy sig name for its own trace quantifier.
mctxSig :: ModelCtx -> String
mctxSig m = maybe "Main" (++"/Main") (mctxAlias m)

-- | Qualify a top-level name (FSM, or a predicate-mode define) with the model's alias, if any.
mctxQualify :: ModelCtx -> String -> Expr
mctxQualify m n = VarExpr $ maybe n (\a -> a++"/"++n) (mctxAlias m)

-- | One input model's Alloy name and 'AlloyM' end state.
mkModelCtx :: Maybe String -> AlloySt -> ModelCtx
mkModelCtx alias st = ModelCtx alias (names_ st) (decls_ st)

-- | Translate a HyperLTL formula into an Alloy 'check' item.
formulaToAlloyCheck :: String -> Int -> Int -> [ModelCtx] -> Pformula -> Item
formulaToAlloyCheck name steps expect models f = ItemCheck name (quantsToAlloy models Map.empty f) steps expect

-- | Translate the quantifier prefix, then the LTL body.
quantsToAlloy :: [ModelCtx] -> Map String ModelCtx -> Pformula -> Expr
quantsToAlloy (m:ms) env (Pfexists v f) =
    QuantExpr QSome v (mctxSig m) (Expr2 (ApplyExpr (mctxQualify m "FSM") [VarExpr v]) OpAnd (quantsToAlloy ms (Map.insert v m env) f))
quantsToAlloy (m:ms) env (Pfforall v f) =
    QuantExpr QAll v (mctxSig m) (Expr2 (ApplyExpr (mctxQualify m "FSM") [VarExpr v]) OpImplies (quantsToAlloy ms (Map.insert v m env) f))
quantsToAlloy [] env (Pfltl e) = ltlToAlloy env e
quantsToAlloy _ _ f = error "quantsToAlloy: formula quantifiers don't match the given models"

-- | Translate a HyperLTL formula body.
ltlToAlloy :: Map String ModelCtx -> Pexpr -> Expr
ltlToAlloy env (Peop1 Patom e) = ltlToAlloy env e
ltlToAlloy env (Peop2 Peq e1 e2) = Expr2 (traceValueToAlloy env e1) OpEq (traceValueToAlloy env e2)
ltlToAlloy env e@(Peident {}) =
    let (trace,base) = splitTraceIdent e
        m = lookupTrace env trace
        (name,_) = getNameM m base
    in case getDeclM m base of
        Value -> Expr2 (Expr2 (VarExpr trace) OpComp (VarExpr name)) OpEq (boolVal True)
        Expression -> ApplyExpr (mctxQualify m name) [VarExpr trace]
ltlToAlloy env (Peop1 Pnot e) = Expr1 OpNot (ltlToAlloy env e)
ltlToAlloy env (Peop1 Pg e) = Expr1 OpAlways (ltlToAlloy env e)
ltlToAlloy env (Peop1 Pf e) = Expr1 OpEventually (ltlToAlloy env e)
ltlToAlloy env (Peop2 Pu e1 e2) = Expr2 (ltlToAlloy env e1) OpUntil (ltlToAlloy env e2)
ltlToAlloy env (Peop2 Pequiv e1 e2) = Expr2 (ltlToAlloy env e1) OpIff (ltlToAlloy env e2)
ltlToAlloy env (Peop2 Pimplies e1 e2) = Expr2 (ltlToAlloy env e1) OpImplies (ltlToAlloy env e2)
ltlToAlloy env (Peopn Pand es) = ands (map (ltlToAlloy env) es)
ltlToAlloy env (Peopn Por es) = ors (map (ltlToAlloy env) es)
ltlToAlloy env (Pebool b) = ExprBool b
ltlToAlloy env e = error $ "ltlToAlloy: unsupported hyperformula operator " ++ show e

-- | Translate one trace-qualified value.
traceValueToAlloy :: Map String ModelCtx -> Pexpr -> Expr
traceValueToAlloy _ (Peint n) = intVal n
traceValueToAlloy env e@(Peident {}) =
    let (trace,base) = splitTraceIdent e
        m = lookupTrace env trace
        (name,_) = getNameM m base
    in case getDeclM m base of
        Value -> Expr2 (VarExpr trace) OpComp (VarExpr name)
        Expression -> error $ "traceValueToAlloy: cannot use predicate-mode define " ++ name ++ " as a value"
traceValueToAlloy _ e = error $ "traceValueToAlloy: unsupported hyperformula value " ++ show e

-- | Look up the model context a formula quantifier bound to this trace variable.
lookupTrace :: Map String ModelCtx -> String -> ModelCtx
lookupTrace env trace = case Map.lookup trace env of
    Just m -> m
    Nothing -> error $ "no model bound for trace variable " ++ trace

-- | Look up a variable's allocated name in one model's context.
getNameM :: ModelCtx -> Pident -> (UniqueName,Maybe String)
getNameM m n = case Map.lookup n (mctxNames m) of
    Just r -> r
    Nothing -> error $ "no name found for " ++ prettyprint n

-- | Look up a variable's declared expression mode in one model's context.
getDeclM :: ModelCtx -> Pident -> ExprMode
getDeclM m n = case Map.lookup n (mctxDecls m) of
    Just r -> r
    Nothing -> error $ "no declaration found for " ++ prettyprint n

-- | Split a trace-quantified 'Peident' into its trace variable and base identifier.
splitTraceIdent :: Pexpr -> (String,Pident)
splitTraceIdent (Peident (Pident n dims) _) | not (List.null dims) = case List.last dims of
    Peident (Pident trace []) _ -> (trace,Pident n (List.init dims))
    _ -> error $ "splitTraceIdent: not a trace-quantified identifier: " ++ n
splitTraceIdent e = error $ "splitTraceIdent: not a trace-quantified identifier: " ++ show e
