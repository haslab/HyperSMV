-- | The AutoHyper-backend driver.
module Cli.AH where

import Control.Monad.IO.Class
import Data.Typeable
import Data.List as List
import Control.Monad
import Control.Monad.Identity
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.Set (Set(..))

import Utils
import Pretty
import Smv.Syntax
import Smv.Typing
import Smv.Packed
import ExplicitState.Syntax
import ExplicitState.Pretty
import ExplicitState.Eval
import qualified ExplicitState.AutoHyper as AutoHyper
import Transform.Bexpr
import Transform.Bexpr.Packed
import Transform.DD.Packed
import Transform.Pexpr
import Transform.Substitute
import Transform.Bexpr.Rename
import Transform.DD.Split
import ExplicitState.Translate
import ExplicitState.APInference
import ExplicitState.FormulaOptimize
import qualified Data.DD as DD
import qualified Data.DDs as DDs
import Transform.DD.Build

import Cli.Args
import Cli.Common

-- | Build explicit-state systems from the input SMVs/formula and run AutoHyper.
doAutoHyper :: Eq digest => Args -> ([PackedPmodule],[(digest,PackedBmodule)],Bformula,[Subst]) -> IO ()
doAutoHyper args (insmvs,smvs,formula,names) = do
    
    let qs = quantsBformula formula
    let qvars = groupVarSet (map fst qs) $ varsBformula formula
    
    chooseDD (globalBoolean args) $ \(dd :: Proxy dd) -> do
        splits <- timeIt "Converting input SMVs to explicit state" $
            doExplicitStatesWithSplitInits dd args qvars smvs
        
        let solveRec :: Int -> [[(DDExplicitStateSystem dd,IntMap Int,DDExplicitStateSystem dd,Subst)]] -> IO ()
            solveRec i xs = case xs of
                [] -> return ()
                ((unzip4 -> (fullexps,fullrenames,exps,ess)) : ys) -> do
                    when (globalSplitInits args /= NoSplitInits) $ putStrLn $ "Processing split " ++ show i ++ " / " ++ show (length splits)
                    expres <- timeIt ("Generating output formula") $ do
                        let qvars = map (id >< exp_packedPvars) (zip (map fst qs) exps)
                        let hvars = joinHyperPvars qvars
                        doBM (Map.map toVarType hvars) $ do
                            
                            let srcDeclaresAPs = hasAtomBexpr (exprBformula formula)
                            formula4 <- do
                                bess <- mapM toBSubst ess
                                formula2 <- substBformula bess True formula
                                formula3 <- doBSubst $ retypeBformula (Map.map toVarType hvars) formula2
                                
                                let formulaC = if compactaps args then inferCompactAPs formula3 else formula3
                                return $! normalizeBformula formulaC
                            
                            opt <- optimizeBformulaForExplicitStateDD dd (removeTemps args) (debug args) (docker args) (globalSplitFormula args) srcDeclaresAPs (globalBisimMode args) (observe args == Atoms) exps formula4
                            (exps2,formula5) <- checkEmptyExplicits (debug args) opt
                            liftIO $ writeFormula args (globalOutformula args) AutoHyper formula5
                            let hist0 = map (\(e1,(e2,renames,aps)) -> AutoHyper.DDExplicitProjection e1 renames aps $ AutoHyper.DDExplicitLeaf e2) $ zip exps exps2
                            let hist1 = map (\(e1,rens1,h) -> AutoHyper.DDExplicitProjection e1 rens1 Map.empty h) $ zip3 fullexps fullrenames hist0
                            return hist1
                            
                    timeIt "Writing output explicit states" $ writeExplicitStateSystems args (globalOutput args qs) (map AutoHyper.targetDDExplicitHistory expres)
                    
                    if globalSolve args
                        then do
                            res@(AutoHyper.Result ty ws) <- solveAutoHyper args qs
                            case (ys,snd (head qs),ty) of
                                ([],_,_) -> writeAutoHyper args qs names res expres
                                (_,Qforall,AutoHyper.UNSAT) -> writeAutoHyper args qs names res expres
                                (_,Qexists,AutoHyper.SAT) -> writeAutoHyper args qs names res expres
                                otherwise -> solveRec (succ i) ys
                        else writeSubsts args names
        solveRec 1 splits

-- | Run the AutoHyper solver on the written-out explicit state systems.
solveAutoHyper :: Args -> [(String,Quant)] -> IO AutoHyper.Result
solveAutoHyper args qs = timeIt "Running AutoHyper" $ do
    AutoHyper.solve (debug args) (ahbisim args) (ahobserve args == Atoms) (ahvalueaps args) (ahdomainfold args) (globalWitness args) (docker args) (ahsolver args) (globalOutput args qs) (globalOutformula args)

-- | Print the AutoHyper verdict and write witness traces if requested.
writeAutoHyper :: BuildDD dd => Args -> [(String,Quant)] -> [Subst] -> AutoHyper.Result -> [AutoHyper.DDExplicitHistory dd] -> IO ()
writeAutoHyper args qs names (AutoHyper.Result ty ws) hists = do
    when (globalWitness args) $ do
        let fullws = AutoHyper.backtraceWitnesses (zip (map fst qs) hists) ws
        let fullexps = map AutoHyper.sourceDDExplicitHistory hists
        let traces = AutoHyper.constructSmvTraces qs names fullws fullexps
        writeTraces args qs traces
    putStrLn $ prettyprint ty

-- | Write each explicit state system to its output file.
writeExplicitStateSystems :: BuildDD dd => Args -> [FilePath] -> [DDExplicitStateSystem dd] -> IO ()
writeExplicitStateSystems args outs exps = do
    liftIO $ mapM_ (\(out,e) -> writeExplicitStateSystem args out e) $ zip outs exps
    when (debug args) $ do
        putStrLn $ "Wrote explicit state systems"
        putStrLn $ "Model size " ++ sepString "x" (map (show . sizeExplicitStateSystem) exps)

-- | Write one explicit state system to a file.
writeExplicitStateSystem :: DD.IsVal val => Args -> FilePath -> ExplicitStateSystem Pident val -> IO ()
writeExplicitStateSystem args f explicit = do
    writeFile f $ show $ prettyExplicitStateSystem explicit
    when (debug args) $ putStrLn $ "Wrote explicit state file " ++ f

doBisim :: BuildDD dd => Proxy dd -> Args -> (String,Set Pident) -> DDExplicitStateSystem dd -> (DDExplicitStateSystem dd,IntMap Int,DDExplicitStateSystem dd,Subst)
doBisim dd args (dim,vs) e = if globalBisimMode args
    then
        let (e1,renames) = projectExplicitStateSystem vs e
            (e',ss) = runIdentity $ tightDDExplicitStateSystem e1
        in (e,renames,e',ss)
    else (e,IntMap.mapWithKey (\k _ -> k) (exp_states e) ,e,Map.empty)

-- | Build explicit-state systems, splitting the outermost model's inits if requested.
doExplicitStatesWithSplitInits :: (Eq digest,BuildDD dd) => Proxy dd -> Args -> [(String,Set Pident)] -> [(digest,PackedBmodule)] -> IO [[(DDExplicitStateSystem dd,IntMap Int,DDExplicitStateSystem dd,Subst)]]
doExplicitStatesWithSplitInits dd args (vs:vars) ((_,bsmv):bsmvs) = do
    ddsmv <- splitToFixedExplicitState dd args vs bsmv
    ddsmvs <- doExplicitStates dd args vars bsmvs
    return $ map (\e -> doBisim dd args vs e : ddsmvs) ddsmv
doExplicitStatesWithSplitInits dd args vars bsmvs = liftM (:[]) $ doExplicitStates dd args vars bsmvs

-- | Split a model's initial states and build an explicit state system per split.
splitToFixedExplicitState :: BuildDD dd => Proxy dd -> Args -> (String,Set Pident) -> PackedBmodule -> IO [DDExplicitStateSystem dd]
splitToFixedExplicitState dd args (_,vs) bsmv = do
    let mode = globalSplitInits args
    let tree = DDs.proxyTreeDDs dd
    withPackedDDmodule explicitSupportAccept bsmv $ splitPackedDDmodule mode
        >=> mapM (transformDDSmvToExplicitState tree tree tree tree True (removeTemps args) (debug args) (docker args))

doExplicitStates :: (Eq digest,BuildDD dd) => Proxy dd -> Args -> [(String,Set Pident)] -> [(digest,PackedBmodule)] -> IO [(DDExplicitStateSystem dd,IntMap Int,DDExplicitStateSystem dd,Subst)]
doExplicitStates dd args vars bsmvs = do
    exps <- mapDigestM (transformToFixedExplicitState dd explicitSupportAccept True (removeTemps args) (debug args) (docker args)) bsmvs
    let refine (e,vs) = return $ doBisim dd args vs e
    liftM (map snd) $ mapDigestM refine $ map (\((d,e),vs) -> ((d,vs),(e,vs))) (zip exps vars)

