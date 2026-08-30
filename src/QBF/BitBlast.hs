-- | Bit-blasting a multi-valued model into boolean gates.
module QBF.BitBlast where

import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import qualified Control.Monad.State.Strict as StrictState

import Smv.Syntax
import Smv.Typing (VarType(..),sizeOfVarType)
import Transform.Pexpr
import QBF.Syntax
import QBF.Gates

-- | Bits needed to index @m@ things (at least 1, so a singleton still has a variable).
bitsFor :: Int -> Int
bitsFor m
    | m <= 1 = 1
    | otherwise = length (takeWhile (< m) (iterate (* 2) 1))

-- | Bits needed to encode a variable's domain. A boolean (or any 2-valued) variable is ONE bit.
varBits :: VarType -> Int
varBits = bitsFor . fromIntegral . sizeOfVarType

-- | The name of bit @j@ (MSB first) of variable @n@ encoded in @w@ bits.
bitPident :: Int -> Int -> Pident -> Pident
bitPident 1 _ n = n
bitPident _ j (Pident str dims) = Pident (str ++ "#b" ++ show j) dims

-- | The value-index selected by a bit pattern, MSB first.
bitOfIdx :: Int -> Int -> Int -> Bool
bitOfIdx w j ix = odd (ix `div` (2 ^ (w - 1 - j)))

-- | Allocate a fresh prefix gate id and register its name.
registerModelPident :: Monad m => String -> Int -> Pident -> QCIRM m GateId
registerModelPident dim i n = do
    st <- StrictState.get
    let num = qcir_st_num_gates st
    let names = qcir_st_names st
    let qn = addDimPident n (mkQuantDim dim)
    StrictState.modify $ \st -> st { qcir_st_num_gates = succ num, qcir_st_names = Map.insert (qn,i) num names }
    return num

-- | Record how to rebuild variable @n@'s VALUE from the bit gates just registered for it.
recordDecode :: Monad m => String -> Int -> Pident -> VarType -> [GateId] -> QCIRM m ()
recordDecode dim i n t gids = StrictState.modify $ \st ->
    st { qcir_st_decode = Map.insert (addDimPident n (mkQuantDim dim), i) (expr,gids) (qcir_st_decode st) }
  where
    w = length gids
    vals = case t of
             VBool -> [Pebool False,Pebool True]
             VInt is -> map Peint (IntSet.toList is)
    expr = case gids of
             [g] | w == 1, VBool <- t -> Peident (identName g) EBool
             _ -> Pecase [ (cube ix, v) | (ix,v) <- zip [0..] vals ]
    cube ix = Peopn Pand
        [ let b = Peident (identName g) EBool
          in if bitOfIdx w j ix then b else Peop1 Pnot b
        | (j,g) <- zip [0..] gids ]

-- | Look up a model variable's bit gate ids at a step.
renderModelPident :: String -> Int -> Int -> DualPident -> QCIRnames -> [GateId]
renderModelPident dim w i (n,isNext) names =
    [ let qn = addDimPident (bitPident w j n) (mkQuantDim dim) in
      case Map.lookup (qn,if isNext then i+1 else i) names of
        Just gid -> gid
        Nothing -> error $ "renderModelPident: gate for name not found " ++ show dim ++ " " ++ show i ++ " " ++ show (bitPident w j n,isNext)
    | j <- [0 .. w-1] ]

-- | Look up a formula variable's bit gate ids at a step.
renderFormulaPident :: Int -> Int -> Pident -> QCIRnames -> [GateId]
renderFormulaPident w i n names =
    [ case Map.lookup (bitPident w j n,i) names of
        Just gid -> gid
        Nothing -> error $ "renderFormulaPident: gate for name not found " ++ show i ++" "++ show (bitPident w j n) ++ "in \n" ++ unlines (map show $ Map.toList names)
    | j <- [0 .. w-1] ]

-- | Monadic version of 'renderFormulaPident'.
renderFormulaPidentM :: Monad m => Int -> Int -> Pident -> QCIRM m [GateId]
renderFormulaPidentM w i n = StrictState.gets qcir_st_names >>= return . (renderFormulaPident w i n)

-- | Append a quantifier block over the given gate ids.
addQuantifierQCIR :: Monad m => Quant -> [GateId] -> QCIRM m ()
addQuantifierQCIR q vs =
    StrictState.modify $ \st -> st { qcir_st_quantifiers = qcir_st_quantifiers st ++ [mkQuantifier q] }
  where
    mkQuantifier Qforall = QForall vs
    mkQuantifier Qexists = QExists vs
