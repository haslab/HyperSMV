-- | The QBF-backend driver.
module Cli.QBF where

import Control.Monad.IO.Class
import System.Directory
import System.FilePath
import System.IO
import qualified Data.ByteString.Builder as BB
import Data.Typeable
import Data.List as List
import Control.Monad
import Control.Monad.Trans
import Prettyprinter
import Data.Maybe
import Control.Monad.Identity
import qualified Data.Map as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import qualified Data.Key as K

import Error
import Utils
import Pretty
import Smv.Syntax
import Smv.Pretty hiding (SmvMode(..))
import Smv.Packed
import Smv.Solver as Smv
import Smv.Trace as Smv
import ExplicitState.Syntax
import Transform.Bexpr
import Transform.Bexpr.Packed
import Transform.Pexpr
import Transform.Substitute
import ExplicitState.Translate
import qualified Data.DD as DD
import qualified Data.DDs as DDs
import Transform.DD.Build
import qualified QBF.Syntax as QBF
import qualified QBF.Pretty as QBF
import qualified QBF.Solver as QBF
import qualified QBF.Gates as QBF
import qualified QBF.Model as QBF
import qualified QBF.Unroll as QBF
import qualified QBF.Witness as QBF

import Cli.Args
import Cli.Common

-- | Encode and solve the QBF instance, picking the DD backend first.
doQBF :: (Eq digest) => Args -> [FilePath] -> ([PackedPmodule],[(digest,PackedBmodule)],Bformula,[Subst]) -> IO ()
doQBF args infiles inps = chooseDD (globalBoolean args) $ \ddp -> doQBFWith ddp args infiles inps

-- | Encode the models/formula as BDDs, then dispatch to the QCIR-building continuation.
doQBFWith :: (Eq digest,BuildDD dd,DD.DDNode dd) => Proxy dd -> Args -> [FilePath] -> ([PackedPmodule],[(digest,PackedBmodule)],Bformula,[Subst]) -> IO ()
doQBFWith ddp args infiles (insmvs,smvs,formula,names) = do
    
    let tree = DDs.proxyTreeDDs ddp
    bdds <- timeIt "Encoding input SMVs and formula as BDDs" $ do
        QBF.transformBsToBDD tree tree tree tree qbfSupportAccept hvars (map snd smvs) formula
    doFixedQBF bdds

  where
    qs = quantsBformula formula
    vars = map (b_vars . snd) smvs
    hvars = joinHyperPvars $ zip (map fst qs) vars
      
    doFixedQBF :: forall dd s1 s2 s3 s4. (QBF.QBFDDs4 dd s1 s2 s3 s4)
               => ([QBF.BDDmodel s1 s2 s3 s4],QBF.BDDformula s4) -> IO ()
    doFixedQBF bdds = do

        qcirnames <- timeIt "Generating output QCIR" $ do
            (qcir,qcirnames,orConflicts) <- timeIt "  .. building QCIR gates" $ do
                let r@(q,_,_) = runIdentity $ QBF.transformBDDToQCIR (k args) (sem args)
                                                (fst bdds) (snd bdds)
                q `seq` return r
            putStrLn $ "  [qcir] prefix=" ++ show (map QBF.sizeQuantifier (QBF.qcir_quantifiers qcir))
                     ++ " blocks=" ++ show (length (QBF.qcir_quantifiers qcir))
                     ++ " gates=" ++ show (IntMap.size (QBF.qcir_gates qcir))
                     ++ " size=" ++ show (QBF.sizeQCIR qcir)
                     ++ " orconflicts=" ++ show orConflicts
            timeIt "  .. rendering+writing QCIR" $ liftIO $ writeQCIR args (globalOutformula args) qcir
            return qcirnames

        let names' = names `composeIntSubsts` qcirnames
        
        if globalSolve args
            then solveQBF args qs infiles (zip (map fst smvs) insmvs) names' (QBF.bdd_formula_vars $ snd bdds)
            else writeIntSubsts args names'

-- | Check the QBF verdict against the BMC semantics and totality assumptions.
verdictQBF :: (Eq digest) => Args -> [(String,Quant)] -> [FilePath] -> [(digest,PackedPmodule)] -> QBF.ResultType -> [Maybe Trace] -> ErrorT IO [String]
verdictQBF args qs infiles insmvs ty traces = do
    
    -- check semantics
    case (QBF.isOptimisticSem (sem args),ty) of
        (True,QBF.SAT) -> do
            lift $ writeTraces args qs traces
            throwErrorT $ "optimistic semantics"
        (True,QBF.UNSAT) -> return ()
        (False,QBF.SAT) -> return ()
        (False,QBF.UNSAT) -> do
            lift $ writeTraces args qs traces
            throwErrorT $ "pessimistic semantics"
    
    -- check infinite lifting for existing traces
    fulltraces <- doInfiniteTraces args qs (map snd insmvs) traces
    
    -- check deadlocks for remaining models
    let remaining = catMaybes $ map (\((dim,q),f,(d,smv),tr) -> if tr then Nothing else Just (d,(dim,f))) $ zip4 qs infiles insmvs fulltraces
    doNoDeadlocks args remaining

-- | Run the QBF solver, build witness traces, and print the verdict.
solveQBF :: (Eq digest) => Args -> [(String,Quant)] -> [FilePath] -> [(digest,PackedPmodule)] -> [IntMap Subst] -> IntMap Pident -> IO ()
solveQBF args qs infiles insmvs names qcirvars = timeIt "Running QBF solver" $ do
    QBF.Result ty vals <- QBF.solve (debug args) (qbfsolver args) (globalWitness args) (docker args) (globalOutformula args)
    traces <- if globalWitness args
        then QBF.constructSmvTraces (debug args) (selfLoops args) qs names vals
        else return $ map (const Nothing) qs
    verdict <- runErrorT $ verdictQBF args qs infiles insmvs ty traces
    putStrLn $ show $ pretty ty <+> parens (printVerdict verdict)

-- | Check and write witness traces, optionally verifying they lift to infinite traces.
doInfiniteTraces :: Args -> [(String,Quant)] -> [PackedPmodule] -> [Maybe Trace] -> ErrorT IO [Bool]
doInfiniteTraces args qs insmvs [] = return []
doInfiniteTraces args ((dim,q):qs) (insmv:insmvs) (Nothing:trs) = liftM (False:) $ doInfiniteTraces args qs insmvs trs
doInfiniteTraces args ((dim,q):qs) (insmv:insmvs) (Just tr:trs) = do
    let tracefile = addExtension dim "witness"
    res <- case checkTotality args of
        Just mode -> do
            (res,finalizer) <- createSystemTemp (removeTemps args) (debug args) "trace.smv" $ \smvfile -> do
                let smv' = addLTLSpec (pnot $ Smv.traceToLTLSpec tr) insmv
                lift $ writeSMV args smvfile Nothing smv'
                let smvnames = Map.fromList [ (prettyPident n, n) | n <- Map.keys (p_vars insmv) ]
                res <- lift $ doFindTrace (debug args) smvnames smvfile
                case res of
                    Just counterexample -> do
                        let tr' = tr { trace_states = trace_states counterexample }
                        lift $ writeFile tracefile $ prettyprint tr'
                        liftM (True:) $ doInfiniteTraces args qs insmvs trs
                    Nothing -> do
                        lift $ writeTraces args ((dim,q):qs) (Just tr:trs)
                        throwErrorT $ "witness for model " ++ dim ++ " has no infinite trace"
            lift finalizer
            return res
        Nothing -> do
            lift $ writeFile tracefile (prettyprint tr)
            liftM (False:) $ doInfiniteTraces args qs insmvs trs
    when (debug args) $ lift $ putStrLn $ "Wrote witness file " ++ tracefile    
    return res
doInfiniteTraces _ _ _ _ = error $ "doInfiniteTraces: mismatch traces"

-- | Check the remaining models for deadlocks (totality).
doNoDeadlocks :: (Eq digest) => Args -> [(digest,(String,FilePath))] -> ErrorT IO [String]
doNoDeadlocks args infiles = do
    oks <- mapDigestM check infiles
    return $ catMaybes $ map snd oks
  where
    check :: (String,FilePath) -> ErrorT IO (Maybe String)
    check (dim,infile) = case checkTotality args of
        Just mode -> do
            ok <- lift $ doCheckSmvTotality args mode infile
            if ok
                then return Nothing
                else throwErrorT $ "model " ++ dim ++ " has deadlocks"
        Nothing -> return $ Just dim

-- | Render a verdict, noting any totality assumptions it relies on.
printVerdict :: Either String [String] -> Doc ann
printVerdict (Right []) = pretty "conclusive"
printVerdict (Right dims) = pretty "conclusive" <+> pretty "-" <+> "assuming totality of" <+> hsep (map pretty dims)
printVerdict (Left str) = pretty "inconclusive" <+> pretty "-" <+> pretty str

-- | Write a QCIR instance to a file.
writeQCIR :: Args -> FilePath -> QBF.QCIR -> IO ()
writeQCIR args f qcir = do
    -- render straight to lazy Text.
    withFile f WriteMode $ \h -> BB.hPutBuilder h (QBF.qcirBuilder qcir)
    when (debug args) $ do
        putStrLn $ "Wrote QCIR file " ++ f
        getFileSize f >>= \sz -> putStrLn $ "Model size " ++ formatBytes sz

-- | Write each input file's per-step substitutions to a @.names.N@ file.
writeIntSubsts :: Args -> [IntMap Subst] -> IO ()
writeIntSubsts args ssss = forM_ (zip (input args) ssss) $ \(infile,sss) -> do
    K.forWithKeyM_ sss $ \i ss -> do
        let f = addExtension (addExtension infile "names") (show i)
        writeFile f $ unlines $ map (\(n,e) -> prettyprint n ++ " := " ++ prettyprint e) $ Map.toList ss
        when (debug args) $ putStrLn $ "Wrote names file " ++ f

-- | Check a single SMV file for totality using the given method.
doCheckSmvTotality :: Args -> CheckTotalityMode -> FilePath -> IO Bool
doCheckSmvTotality args mode file = do
    when (debug args) $ putStrLn $ "Reading SMV file " ++ show file ++ " for totality check " ++ show mode
    case mode of
        CheckFsmNuXmv -> Smv.doCheckFsmNuXMV (debug args) file
        CheckSpecNuXmv -> Smv.doCheckSpecTotalNuXMV (debug args) file
        CheckTotalExplicitState -> chooseDD (globalBoolean args) $ \dd -> do
            pmodule <- readSMV file
            bmodule <- doBMState $ toInlinedPackedBmodule pmodule
            exps <- transformToFixedExplicitState dd explicitSupportAccept False (removeTemps args) (debug args) (docker args) bmodule
            return $ isTotalExplicitStateSystem exps

