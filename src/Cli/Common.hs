-- | Shared IO helpers for the @hypersmv@ backends.
module Cli.Common where

import Control.Monad.IO.Class
import System.FilePath
import System.Clock
import Data.Typeable
import Crypto.Hash (Digest, SHA256)
import qualified Data.ByteString.Lazy as BS
import Control.Monad
import Data.Maybe
import Control.Monad.Identity
import qualified Data.Map as Map
import Data.Set (Set(..))

import Error
import Utils
import Pretty
import qualified Location as L
import Smv.Syntax
import Smv.Typing
import Smv.Pretty hiding (SmvMode(..))
import qualified Smv.Pretty as Smv
import Smv.Parser
import Smv.Packed
import Smv.Solver as Smv
import Smv.Trace as Smv
import Transform.Bexpr
import Transform.Bexpr.Packed
import Transform.Pexpr
import Transform.Substitute
import Transform.Minimize
import Transform.Bexpr.Rename
import Smv.Declarative
import ExplicitState.Translate
import Transform.Normalize
import qualified Data.DD as DD
import qualified Data.DDs as DDs

import Cli.Args

-- | Optionally flatten input SMVs via nuXmv, then run the continuation.
doFlatten :: Args -> [FilePath] -> ([FilePath] -> IO a) -> IO a
doFlatten args infiles go = do
    (infiles1,finalizers1) <- if flatten args
        then timeIt "Flattening and optimizing input SMVs" $ do
            liftM unzip $ mapM (createSystemTemp (removeTemps args) (debug args) "flat.smv" . doOptimizeNuXMV (debug args)) infiles
        else return (infiles,[])
    res <- go infiles1
    mapM_ id finalizers1
    return res

-- | Optionally booleanise input SMVs via nuXmv, then run the continuation.
doBoolean :: Args -> [FilePath] -> ([FilePath] -> Maybe [Subst] -> IO a) -> IO a
doBoolean args infiles go = if globalBoolean args
    then timeIt "Converting input SMVs to boolean" $ do
        (infiles1,finalizers1) <- if globalExplicit args
            then liftM unzip $ mapM (createSystemTemp (removeTemps args) (debug args) "bool-pre.smv" . doBooleanDomains args) infiles
            else return (infiles,[])
        ((infiles2,boolNames),finalizers2) <- do
            liftM ((((id >< Just) . unzip) >< id) . unzip) $ mapM (createSystemTemp (removeTemps args) (debug args) "bool-post.smv" . doBooleanNuXMV (debug args)) infiles1
        res <- go infiles2 boolNames
        mapM_ id finalizers1
        mapM_ id finalizers2
        return res
    else go infiles Nothing

-- | Rewrite an SMV file's variable domains into boolean encodings.
doBooleanDomains :: Args -> FilePath -> FilePath -> IO FilePath
doBooleanDomains args infile outfile = do
    insmv <- readSMV infile
    outsmv <- transformBooleanDomains insmv
    writeSMV args outfile Nothing outsmv
    return outfile

-- honor JUSTICE fairness by turning it into a GF LTLSPEC on the system (unless dropped)
honorJustice :: Bool -> PackedPmodule -> PackedPmodule
honorJustice dropit p
    | dropit || null js = p { p_justice = [] }
    | otherwise = p { p_ltlspec = Just (pands (maybe id (:) (p_ltlspec p) [ Peop1 Pg (Peop1 Pf e) | e <- js ])), p_justice = [] }
  where
    js = filter (/= Pebool True) (p_justice p)

-- | Parse the input SMVs and formula, process them, and run the continuation.
doInputs :: Args -> [FilePath] -> Maybe [Subst] -> ([FilePath] -> ([PackedPmodule],[((Digest SHA256,Int),PackedBmodule)],Bformula,[Subst]) -> IO a) -> IO a
doInputs args infiles boolNames go = do
    (infiles',finalizers,insmvs,qvars,formula) <- timeIt "Parsing input SMVs and Hyper formula" $ do
        insmvs <- liftM (map (id >< (honorJustice (globalDropltlspec args) . dropLTLSpec))) $ readSMVs infiles
        (infiles',finalizers) <- liftM unzip $ forM (zip infiles insmvs) $ \(infile,(_,insmv)) -> do
            createSystemTemp (removeTemps args) (debug args) (takeFileName infile) $ \infile' -> do
                writeSMV args infile' Nothing insmv
                return infile'
        
        let tys = map (moduleTypes . snd) insmvs
        let sss = map (moduleSubst . snd) insmvs
        formula <- liftM (runIdentity . substFormula sss True . sortFormula) $ readFormula args (fromJust $ informula args) tys
        let qs = quantsPformula formula
        let qvars = map snd $ groupVarSet (map fst qs) $ varsFormula formula
        when (length qs /= length insmvs) $ exitWithErrorMessage "Please provide same number of models and formula quantifiers"
        return (infiles',finalizers,insmvs,qvars,formula)
    
    (midsmvs,names) <- timeIt "Processing input SMVs" $ liftM (unzip . map assocl) $ do
        mapDigestM (doSmv args) $ map assocr $ zip insmvs qvars
    
    (outsmvs,outformula) <- timeIt "Processing input formula" $ do
        let qs = quantsPformula formula
        let vars = map (b_vars . snd) midsmvs
        let hnames = joinHyperNameSubst $ zip (map fst qs) names
        let nformula = renameFormula hnames formula
        bformula <- doBM (Map.map toVarType $ joinHyperPvars $ zip (map fst qs) vars) $ toBformula nformula
        -- Under `--splitformula=ltl` a subformula is pushed into a model only if its automaton needs no memory; pure liveness stays in the matrix, where one automaton covers the whole product instead of being duplicated per model and multiplied across the prefix.
        splits <- liftIO $ splitBformulaDigestBmoduleM
                    (isMemorylessBexpr (DDs.proxyTreeDDs (Proxy :: Proxy DD.GIDD))
                                       (removeTemps args) (debug args) (docker args))
                    (globalSplitFormula args) (midsmvs,bformula)
        return splits
    
    let names' = boolNames `maybeComposeSubsts` (map fromNameSubst names)
    ret <- go infiles' (map snd insmvs,outsmvs,outformula,names')
    mapM_ id finalizers
    return ret

-- | Inline and minimize a single SMV module.
doSmv :: Args -> (PackedPmodule,Set Pident) -> IO (PackedBmodule,NameSubst)
doSmv args (smv,used) = doBMState $ do
    smv1 <- toInlinedPackedBmodule smv
    let smv2 = dropUnusedBmoduleVars used smv1
    if globalMinimize args
        then transformBminimize smv2
        else return (smv2,idNameSubst $ b_vars smv2)

-- | Default any undeclared formula variable to FALSE.
doFillFormulaVars :: Args -> [PackedPtypes] -> Pformula -> IO Pformula
doFillFormulaVars args tys f = do
    let qs = quantsPformula f
    let e = exprPformula f
    let vs = varsFormula f
    let ty = joinHyperPtypes $ zip (map fst qs) tys
    let fillVar :: Subst -> Pident -> IO Subst
        fillVar ss v = case Map.lookup v ty of
            Just _ -> return ss
            Nothing -> do
                when (debug args) $ putStrLn $ "WARNING: setting unknown formula variable " ++ prettyPident v ++ " to FALSE"
                return $ Map.insert v (Pebool False) ss
    ss <- foldM fillVar Map.empty vs
    e' <- substExpr ss ss False e
    return $ applyQuantsExpr qs e'

-- | Parse a Hyper formula file and type its variables.
readFormula :: Args -> FilePath -> [PackedPtypes] -> IO Pformula
readFormula args fn tys = do
    txt <- BS.readFile fn
    f <- ioErrorM $ runFormulaParser fn txt >>= return . L.unloc
    f <- doFillFormulaVars args tys f
    return $ addFormulaTypes tys f

-- | Write an SMV module to a file.
writeSMV :: Args -> FilePath -> Maybe HyperTool -> PackedPmodule -> IO ()
writeSMV args f tool smv = do
    writeFile f $ prettySMV (mkSmvMode False tool) smv
    when (debug args) $ putStrLn $ "Wrote SMV file " ++ f

-- | Write a Hyper formula to a file.
writeFormula :: Args -> FilePath -> HyperTool -> Pformula -> IO ()
writeFormula args fn tool formula = do
    writeFile fn $ prettySMV (mkSmvMode True $ Just tool) $ runIdentity (mapFormula (Identity . canonAtomBodies . unnegateAtoms) (normalizeFormula formula))
    when (debug args) $ putStrLn $ "Wrote formula file " ++ fn

-- | Announce a stage and report its wall-clock duration.
timeIt :: MonadIO m => String -> m a -> m a
timeIt msg m = do
    liftIO $ putStrLn msg
    (a,seconds) <- measureTime m
    liftIO $ putStrLn $ "Took " ++ show seconds ++ "s"
    return a

-- | Run an action and return its result with elapsed seconds.
measureTime :: MonadIO m => m a -> m (a,Double)
measureTime action = do
  start <- liftIO $ getTime Monotonic
  result <- action
  end <- liftIO $ getTime Monotonic
  let diff = fromIntegral (toNanoSecs (diffTimeSpec end start)) / 1e9
  return (result, diff)

-- | Pick the SMV pretty-printing mode for a hyper tool.
mkSmvMode :: Bool -> Maybe HyperTool -> Smv.SmvMode
mkSmvMode _ Nothing = Smv.Default
mkSmvMode isFormula (Just AutoHyper) = Smv.AutoHyper (if isFormula then Smv.Hyper else Smv.Smv)
mkSmvMode isFormula (Just HyperQube) = Smv.HyperQube (if isFormula then Smv.Hyper else Smv.Smv)
mkSmvMode isFormula (Just QCIR) = Smv.Default

-- | Write each input file's variable substitutions to a @.names@ file.
writeSubsts :: Args -> [Subst] -> IO ()
writeSubsts args sss = forM_ (zip (input args) sss) $ \(infile,ss) -> do
    let f = addExtension infile "names"
    writeFile f $ unlines $ map (\(n,e) -> prettyprint n ++ " := " ++ prettyprint e) $ Map.toList ss
    when (debug args) $ putStrLn $ "Wrote names file " ++ f

-- | Write each dimension's witness trace to a @.witness@ file.
writeTraces :: Args -> [(String,Quant)] -> [Maybe Smv.Trace] -> IO ()
writeTraces args qs traces = forM_ (zip qs traces) $ \((dim,_),mbtrace) -> forM_ mbtrace $ \trace -> do
    let f = addExtension dim "witness"
    writeFile f $ prettyprint trace
    when (debug args) $ putStrLn $ "Wrote witness file " ++ f

