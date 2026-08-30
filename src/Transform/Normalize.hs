-- | Normalizes Pexpr/LTL formulas and selects atomisation strategies.
module Transform.Normalize where

import qualified Data.HashSet as HashSet
import Data.List as List

import Utils
import Smv.Syntax
import Smv.Typing
import Transform.Pexpr

-- | Hoists nested 'next' operators to an outer wrapping.
outerNext :: Pexpr -> Pexpr
outerNext e = mknext (go e)
    where
    mknext (e@(Pebool {}),isNext) = e
    mknext (e@(Peint {}),isNext) = e
    mknext (e,isNext) = if isNext then pnext e else e
    go :: Pexpr -> (Pexpr,Bool)
    go e@(Peident {}) = (e,False)
    go e@(Pebool {}) = (e,True)
    go e@(Peint {}) = (e,True)
    go (Peop1 Pnext e) = (e,True)
    go (Peop1 o e1) | isLTLOp1 o = (Peop1 o $ outerNext e1,False)
    go (Peop1 o e1) = 
        let (e1',isNext1) = go e1 in
        (Peop1 o e1',isNext1) 
    go (Peop2 o e1 e2) | isLTLOp2 o = (Peop2 o (outerNext e1) (outerNext e2),False)
    go (Peop2 o e1 e2) =
        let r1@(e1',isNext1) = go e1 in
        let r2@(e2',isNext2) = go e2 in 
        if isNext1 && isNext2 then (Peop2 o e1' e2',True) else (Peop2 o (mknext r1) (mknext r2),False)
    go (Peopn o es) = 
        let rs = map go es in
        let (es',isNexts) = unzip rs in
        if all id isNexts then (Peopn o es',True) else (Peopn o $ map mknext rs,False)
    go e@(Pecase cs) =
        let (ls,rs) = unzip $ map (id >< go) cs in
        let (es,isNexts) = unzip rs in
        if all id isNexts then (Pecase $ zip ls es,True) else (Pecase $ zip ls (map mknext rs),False)
    go e@(Pedemorgan c e1 e2) = 
        let r1@(e1',isNext1) = go e1 in
        let r2@(e2',isNext2) = go e2 in
        if isNext1 && isNext2 then (Pedemorgan c e1' e2',True) else (Pedemorgan c (mknext r1) (mknext r2),False)

-- innerNext needs to be called first, otherwise unfolding case expressions is unsound
normalizeExpr :: Pexpr -> Pexpr
normalizeExpr = evaluateExpr . nnfExpr . unfoldExpr . innerNext

-- | Normalizes every LTL expression in a formula.
normalizeFormula :: Pformula -> Pformula
normalizeFormula (Pfforall n f) = Pfforall n $ normalizeFormula f
normalizeFormula (Pfexists n f) = Pfexists n $ normalizeFormula f
normalizeFormula (Pfltl e) = Pfltl $ normalizeExpr e

-- | Pushes a 'next' operator inward through an expression.
innerNext :: Pexpr -> Pexpr
innerNext (vnext -> Just e@(Pebool {})) = e
innerNext (vnext -> Just e@(Peint {})) = e
innerNext (vnext -> Just (Peop1 o e1)) = Peop1 o $ innerNext $ pnext e1
innerNext (vnext -> Just (Peop2 o e1 e2)) = Peop2 o (innerNext $ pnext e1) (innerNext $ pnext e2)
innerNext (vnext -> Just (Peopn o es)) = Peopn o $ map (innerNext . pnext) es
innerNext (vnext -> Just (Pecase cs)) = Pecase $ map (id >< (innerNext . pnext)) cs
innerNext (vnext -> Just (Pedemorgan c e1 e2)) = Pedemorgan c (innerNext $ pnext e1) (innerNext $ pnext e2)
innerNext e@(Pebool {}) = e
innerNext e@(Peint {}) = e
innerNext e@(Peident {}) = e
innerNext (Peop1 o e1) = Peop1 o (innerNext e1)
innerNext (Peop2 o e1 e2) = Peop2 o (innerNext e1) (innerNext e2)
innerNext (Peopn o es) = Peopn o (map innerNext es)
innerNext (Pecase cs) = Pecase $ map (id >< innerNext) cs
innerNext (Pedemorgan c e1 e2) = Pedemorgan c (innerNext e1) (innerNext e2)

-- | Rewrites derived operators into core expression forms.
unfoldExpr :: Pexpr -> Pexpr
unfoldExpr (Peop2 Pimplies e1 e2) = unfoldExpr $ unfoldImplies e1 e2
unfoldExpr (Peop2 Pin e1 (vset -> Just is)) | List.null is = Pebool False
unfoldExpr (Peop2 Pin e1 (vset -> Just [e2])) = unfoldExpr $ Peop2 Peq e1 e2
unfoldExpr (Peop2 Pin e1 e2) | isConstantExpr e2 = unfoldExpr $ Peop2 Peq e1 e2
unfoldExpr (Peop2 Pin e1 (vsetbool -> Just bs)) = case HashSet.size bs of
    0 -> Pebool False
    1 -> if popHashSet bs then unfoldExpr e1 else unfoldExpr (pnot e1) 
    2 -> Pebool True
unfoldExpr (Peop2 Pin e1@(vcase -> Just cs1) (vset -> Just is)) = unfoldExpr $ pors $ map (Peop2 Peq e1) is
unfoldExpr (Peop2 Peq e1 e2) | isBoolExpr e1 && isBoolExpr e2 = unfoldExpr $ Peop2 Pequiv e1 e2 
unfoldExpr e@(Pebool {}) = e
unfoldExpr e@(Peint {}) = e
unfoldExpr e@(Peident {}) = e
unfoldExpr (Peop1 o e1) = Peop1 o (unfoldExpr e1)
unfoldExpr (Peop2 Punion e1 e2) = unfoldExpr $ Peopn Pset $ joinUnions [e1,e2]
unfoldExpr e@(Peop2 o e1 (vcase -> Just cs2)) | isBoolExpr e = unfoldExpr $ inlineCaseExprBool $ map (id >< peop2 o e1) cs2
unfoldExpr e@(Peop2 o (vcase -> Just cs1) e2) | isBoolExpr e = unfoldExpr $ inlineCaseExprBool $ map (id >< (\e1 -> peop2 o e1 e2)) cs1
unfoldExpr (Peop2 o e1 e2) = peop2 o (unfoldExpr e1) (unfoldExpr e2)
unfoldExpr (Peopn o es) = peopn o (map unfoldExpr es)
unfoldExpr e@(Pecase cases) | isBoolExpr e = unfoldExpr $ inlineCaseExprBool cases
unfoldExpr (Pecase cs) = Pecase $ map (unfoldExpr >< unfoldExpr) cs
unfoldExpr (Pedemorgan c te fe) = unfoldExpr $ Pecase [(c,te),(pnot c,fe)]

unfoldEquiv e1 e2 = (e1 `pand` e2) `por` (pnot e1 `pand` pnot e2)
unfoldImplies e1 e2 = pnot e1 `por` e2

-- | Flattens nested set unions into a flat list.
joinUnions :: [Pexpr] -> [Pexpr]
joinUnions [] = []
joinUnions (Peop2 Punion x1 x2:xs) = joinUnions (x1 : x2 : xs)
joinUnions (x:xs) = x : joinUnions xs

-- | Converts an expression to negation normal form.
nnfExpr :: Pexpr -> Pexpr    
nnfExpr (Peop1 Patom e) | isConstantExpr e = e
nnfExpr e@(vnot -> Just (Peop1 Patom _)) = e
nnfExpr (vnotnot -> Just e) = nnfExpr e
nnfExpr (vnotors -> Just es) = pands $ map (nnfExpr . pnot) es
nnfExpr (vnotands -> Just es) = pors $ map (nnfExpr . pnot) es
nnfExpr (vnot -> Just (Peop2 Pimplies e1 (Pebool False))) = nnfExpr e1
nnfExpr (vnot -> Just (Peop2 Pimplies e1 e2)) = nnfExpr $ e1 `pand` pnot e2
nnfExpr (vnot -> Just (Peop1 Pf e1)) = nnfExpr $ Peop1 Pg $ pnot e1
nnfExpr (vnot -> Just (Peop1 Pg e1)) = nnfExpr $ Peop1 Pf $ pnot e1
nnfExpr (vnot -> Just (Peop1 Px e1)) = nnfExpr $ Peop1 Px $ pnot e1
nnfExpr (vnot -> Just (Peop2 Pu e1 e2)) = nnfExpr $ peop2 Pv (pnot e1) (pnot e2)
nnfExpr (vnot -> Just (Peop2 Pv e1 e2)) = nnfExpr $ peop2 Pu (pnot e1) (pnot e2)
nnfExpr (vnot -> Just (Peop2 o e1 e2)) | isCmpOp2 o = nnfExpr $ peop2 (negCmpOp2 o) e1 e2
nnfExpr (vnot -> Just e1) = case nnfExpr e1 of
    Pebool b -> Pebool $ not b
    e1' -> pnot e1'
nnfExpr e@(Peop1 o e1) = case (o,nnfExpr e1) of
    (Pf,Pebool b) -> Pebool b
    (Pg,Pebool b) -> Pebool b
    (o,e1') -> Peop1 o e1'
nnfExpr (Peop2 Peq (Pebool b1) (Pebool b2)) = Pebool (b1==b2)
nnfExpr (Peop2 Peq (Peint i1) (Peint i2)) = Pebool (i1==i2)
nnfExpr e@(Peop2 o e1 (Pecase cs2)) | isBoolExpr e = nnfExpr $ fst $ foldl caseOp (pfalse,pfalse) cs2
    where caseOp (acc,pre) (c2,e2) = (por acc $ pands $ [pnot pre,c2,peop2 o e1 e2],por pre c2)
nnfExpr e@(Peop2 o (Pecase cs1) e2) | isBoolExpr e = nnfExpr $ fst $ foldl caseOp (pfalse,pfalse) cs1
    where caseOp (acc,pre) (c1,e1) = (por acc $ pands $ [pnot pre,c1,peop2 o e1 e2],por pre c1)
nnfExpr e@(Peop2 o e1 e2) | isBoolExpr e, Just (cs, rebuild) <- findArithCase e2 =
    let step (acc,pre) (c,b) = (por acc $ pands [pnot pre,c,peop2 o e1 (rebuild b)],por pre c)
    in nnfExpr $ fst $ foldl step (pfalse,pfalse) cs
nnfExpr e@(Peop2 o e1 e2) | isBoolExpr e, Just (cs, rebuild) <- findArithCase e1 =
    let step (acc,pre) (c,b) = (por acc $ pands [pnot pre,c,peop2 o (rebuild b) e2],por pre c)
    in nnfExpr $ fst $ foldl step (pfalse,pfalse) cs
nnfExpr (Peop2 Peq e1@(isBoolExpr -> True) e2@(isBoolExpr -> True)) = nnfExpr $ peop2 Pequiv e1 e2 
nnfExpr (Peop2 Pimplies (Pebool True) e2) = nnfExpr e2
nnfExpr (Peop2 Pimplies e1 (Pebool False)) = nnfExpr $ pnot e1
nnfExpr (Peop2 Pequiv e1 (Pebool False)) = nnfExpr $ pnot e1
nnfExpr (Peop2 Pequiv e1 (Pebool True)) = nnfExpr e1
nnfExpr (Peop2 Pequiv (Pebool False) e2) = nnfExpr $ pnot e2
nnfExpr (Peop2 Pequiv (Pebool True) e2) = nnfExpr e2
nnfExpr (Peop2 Pimplies (Pebool False) e2) = Pebool True
nnfExpr (Peop2 Pimplies e1 (Pebool True)) = Pebool True
nnfExpr e@(Peident n t) = e
nnfExpr e@(Pebool _) = e
nnfExpr e@(Peint _) = e
nnfExpr e@(Peop2 o e1 e2) = Peop2 o (nnfExpr e1) (nnfExpr e2)
nnfExpr (Peopn o es) = peopn o $ map nnfExpr es
nnfExpr (Pecase cs) = Pecase $ map (\(x,y) -> (nnfExpr x,nnfExpr y)) cs
nnfExpr (Pedemorgan c e1 e2) = Pecase [(nnfExpr c,nnfExpr e1),(ptrue,nnfExpr e2)]

-- | The outermost @case@ nested inside an arithmetic expression, with the context needed to rebuild the surrounding expression around a chosen branch.
findArithCase :: Pexpr -> Maybe ([(Pexpr,Pexpr)], Pexpr -> Pexpr)
findArithCase (Pecase cs) = Just (cs, id)
findArithCase (Peop2 o e1 e2) | isArithOp2 o =
    case findArithCase e1 of
        Just (cs,k) -> Just (cs, \x -> Peop2 o (k x) e2)
        Nothing     -> fmap (\(cs,k) -> (cs, \x -> Peop2 o e1 (k x))) (findArithCase e2)
findArithCase _ = Nothing

-- | Checks whether an expression contains a declared atom.
hasAtomic :: Pexpr -> Bool
hasAtomic (Pebool {}) = False
hasAtomic (Peint {}) = False
hasAtomic (Peident {}) = False
hasAtomic (Peop1 Patom e) = True
hasAtomic (Peop1 o e1) = hasAtomic e1
hasAtomic (Peop2 o e1 e2) = hasAtomic e1 || hasAtomic e2
hasAtomic (Peopn o es) = any hasAtomic es
hasAtomic (Pecase cs) = any (\(x,y) -> hasAtomic x || hasAtomic y) cs
hasAtomic (Pedemorgan c e1 e2) = hasAtomic c || hasAtomic e1 || hasAtomic e2

-- | Wraps each minimal boolean subexpression in an atom.
atomifyExpr :: Pexpr -> Pexpr
atomifyExpr e@(Pebool {}) = e
atomifyExpr e@(Peint {}) = e
atomifyExpr e@(Peident {}) | isBoolExpr e = patom e
atomifyExpr e@(Peop1 Patom e1) = patom e1 -- to normalize eventually multiple clustered atoms
atomifyExpr (Peop1 o1 e1) = Peop1 o1 (atomifyExpr e1)
atomifyExpr e@(Peop2 o2 e1 e2) | isCmpOp2 o2 && not (hasAtomic e) && not (isLTLExpr e) = patom e
atomifyExpr (Peop2 o2 e1 e2) = Peop2 o2 (atomifyExpr e1) (atomifyExpr e2)
atomifyExpr (Peopn on es) = Peopn on $ map atomifyExpr es
atomifyExpr (Pecase cs) = Pecase $ map (atomifyExpr >< atomifyExpr) cs
atomifyExpr (Pedemorgan c e1 e2) = Pedemorgan (atomifyExpr c) (atomifyExpr e1) (atomifyExpr e2)
atomifyExpr e = error $ "cannot atomifyExpr " ++ show e

-- | Number of identifier occurrences an expression would bury inside one opaque atom.
atomIdents :: Pexpr -> Int
atomIdents (Pebool {}) = 0
atomIdents (Peint {}) = 0
atomIdents (Peident {}) = 1
atomIdents (Peop1 _ e1) = atomIdents e1
atomIdents (Peop2 _ e1 e2) = atomIdents e1 + atomIdents e2
atomIdents (Peopn _ es) = sum (map atomIdents es)
atomIdents (Pecase cs) = sum (map (\(c,e) -> atomIdents c + atomIdents e) cs)
atomIdents (Pedemorgan c e1 e2) = atomIdents c + atomIdents e1 + atomIdents e2
atomIdents _ = 1

-- | Above this, the whole formula is atomised finely instead of coarsely.
maxAtomIdents :: Int
maxAtomIdents = 47

-- | Turn a coarse atomisation into the fine one, in place.
refineAtoms :: Pexpr -> Pexpr
refineAtoms (Peop1 Patom e) = atomifyExpr e
refineAtoms e@(Pebool {}) = e
refineAtoms e@(Peint {}) = e
refineAtoms e@(Peident {}) = e
refineAtoms (Peop1 o e) = Peop1 o (refineAtoms e)
refineAtoms (Peop2 o e1 e2) = Peop2 o (refineAtoms e1) (refineAtoms e2)
refineAtoms (Peopn o es) = Peopn o (map refineAtoms es)
refineAtoms (Pecase cs) = Pecase (map (refineAtoms >< refineAtoms) cs)
refineAtoms (Pedemorgan c e1 e2) = Pedemorgan (refineAtoms c) (refineAtoms e1) (refineAtoms e2)
refineAtoms e = e

-- | Largest atom (in identifier occurrences) anywhere in an already-atomised expression.
maxAtomIdentsOf :: Pexpr -> Int
maxAtomIdentsOf (Peop1 Patom e1) = atomIdents e1
maxAtomIdentsOf (Peop1 _ e1) = maxAtomIdentsOf e1
maxAtomIdentsOf (Peop2 _ e1 e2) = max (maxAtomIdentsOf e1) (maxAtomIdentsOf e2)
maxAtomIdentsOf (Peopn _ es) = maximum (0 : map maxAtomIdentsOf es)
maxAtomIdentsOf (Pecase cs) = maximum (0 : map (\(c,e) -> max (maxAtomIdentsOf c) (maxAtomIdentsOf e)) cs)
maxAtomIdentsOf (Pedemorgan c e1 e2) = maximum [maxAtomIdentsOf c, maxAtomIdentsOf e1, maxAtomIdentsOf e2]
maxAtomIdentsOf _ = 0

-- | Applies 'atomifyExpr' to a formula's LTL body.
atomifyFormula :: Pformula -> Pformula
atomifyFormula (Pfexists n f) = Pfexists n $ atomifyFormula f
atomifyFormula (Pfforall n f) = Pfforall n $ atomifyFormula f
atomifyFormula (Pfltl e) = Pfltl $ atomifyExpr e

-- | Ensures every boolean subexpression carries an atom marker.
ensurePatom :: Pexpr -> Pexpr
ensurePatom e@(Pebool {}) = e
ensurePatom e@(Peint {}) = e
ensurePatom e@(Peident {}) | isBoolExpr e = patom e
ensurePatom e@(Peop1 Patom e1) = patom e1
ensurePatom e@(Peop1 o1 e1) | isBoolExpr e = if hasAtomic e then peop1 o1 e1 else patom e
ensurePatom e@(Peop2 o2 e1 e2) | isBoolExpr e = if hasAtomic e then peop2 o2 (ensurePatom e1) (ensurePatom e2) else patom e
ensurePatom e@(Peopn on es) | isBoolExpr e = if hasAtomic e then peopn on (map ensurePatom es) else patom e
ensurePatom e = error $ "ensurePatom: " ++ show e

-- | Wraps an expression in a single atom marker.
patom :: Pexpr -> Pexpr
patom e@(Pebool {}) = e
patom e@(Peint {}) = e
patom e = Peop1 Patom (noatom e)

-- | Wraps an expression in an atom marker without stripping nested atoms.
patomUnsafe :: Pexpr -> Pexpr
patomUnsafe e@(Pebool {}) = e
patomUnsafe e@(Peint {}) = e
patomUnsafe e = Peop1 Patom e

-- | Strips atom markers from an expression.
noatom :: Pexpr -> Pexpr
noatom e@(Pebool {}) = e
noatom e@(Peint {}) = e
noatom e@(Peident {}) = e
noatom e@(Peop1 Patom e1) = noatom e1
noatom e@(Peop1 o1 e1) = Peop1 o1 (noatom e1)
noatom (Peop2 Pequiv e1 e2) = noatom $ unfoldEquiv e1 e2 -- AH does not support this in atomic exprs
noatom (Peop2 Pimplies e1 e2) = noatom $ unfoldImplies e1 e2 -- AH does not support this in atomic exprs
noatom e@(Peop2 o2 e1 e2) = Peop2 o2 (noatom e1) (noatom e2)
noatom e@(Peopn opn es) = Peopn opn (map noatom es)
noatom e@(Pecase cs) = Pecase $ map (noatom >< noatom) cs
noatom e@(Pedemorgan c e1 e2) = Pedemorgan (noatom c) (noatom e1) (noatom e2)
noatom e = error $ "noatom: " ++ show e

-- | Constant-folds and simplifies an expression.
evaluateExpr :: Pexpr -> Pexpr
evaluateExpr (Peop1 o e1) =
    case (o,evaluateExpr e1) of
        (Pnot,Pebool b) -> Pebool $ not b
        (Pf,Pebool b) -> Pebool b
        (Pg,Pebool b) -> Pebool b
        (Px,Pebool b) -> Pebool b
        (o,e1') -> Peop1 o e1'
evaluateExpr (Peop2 o e1 e2) = 
    case (o,evaluateExpr e1,evaluateExpr e2) of
        (Pequiv,e1,Pebool False) -> nnfExpr $ pnot e1
        (Pequiv,e1,Pebool True) -> e1
        (Pequiv,Pebool False,e2) -> nnfExpr $ pnot e1
        (Pequiv,Pebool True,e2) -> e2
        (Pplus,Peint i,Peint j) -> Peint (i+j)
        (Pminus,Peint i,Peint j) -> Peint (i-j)
        (Ptimes,Peint i,Peint j) -> Peint (i*j)
        (Peq,Peint i,Peint j) -> Pebool (i==j)
        (Pneq,Peint i,Peint j) -> Pebool (i/=j)
        (Pgt,Peint i,Peint j) -> Pebool (i>j)
        (Pgeq,Peint i,Peint j) -> Pebool (i>=j)
        (Plt,Peint i,Peint j) -> Pebool (i<j)
        (Pleq,Peint i,Peint j) -> Pebool (i<=j)
        (o,e1',e2') -> Peop2 o e1' e2'
evaluateExpr e@(Peident _ t) = e
evaluateExpr e@(Pebool _) = e
evaluateExpr e@(Peint _) = e
evaluateExpr (Peopn Pand es) = pands (map evaluateExpr es)
evaluateExpr (Peopn Por es) = pors (map evaluateExpr es)
evaluateExpr (Peopn Pset es) = pset (map evaluateExpr es)
evaluateExpr (Pecase cs) = caseOf (map (evaluateExpr >< evaluateExpr) cs)
  where
    caseOf cs' = case dropWhile ((== Pebool False) . fst) cs' of
                   ((Pebool True,v):_) -> v
                   rest -> Pecase rest
evaluateExpr (Pedemorgan (Pebool b) e1 e2) = if b then evaluateExpr e1 else evaluateExpr e2
evaluateExpr e = e
