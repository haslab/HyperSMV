module Main where

import Control.Monad.IO.Class
import qualified Shelly
import Data.Text (Text(..))
import qualified Data.Text as T
import System.Console.CmdArgs
import System.Environment
import System.Directory
import System.FilePath
import System.IO
import System.Clock
import Data.Typeable
import Crypto.Hash (Digest, SHA256)
import qualified Crypto.Hash as Crypto
import Data.List as List
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Data.ByteString.Lazy (ByteString(..))
import qualified Data.ByteString.Lazy as BS
import Control.Monad
import Control.Monad.Trans
import Prettyprinter
import Data.Maybe
import Control.Monad.Trans.Maybe
import Control.Monad.Identity
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Data.IntMap (IntMap(..))
import qualified Data.IntMap as IntMap
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Proxy
import qualified Data.Key as K
import Data.Hashable

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
import ExplicitState.Syntax
import ExplicitState.Pretty
import ExplicitState.Eval
import qualified ExplicitState.AutoHyper as AutoHyper
import Transform.Bexpr
import Transform.Bpacked
import Transform.DDpacked
import Transform.Pexpr
import Transform.Substitute
import Transform.Minimize
import Transform.Rename
import Transform.CSE
import Transform.Smv
import Transform.Split
import Transform.SmvToExplicitState
import Transform.Exhaustive
import Transform.Normalize
import Transform.Bproduct
import qualified Alloy.Syntax as Alloy
import qualified Alloy.Pretty as Alloy
import qualified Transform.SmvToAlloy as Alloy
import qualified Data.DD as DD
import qualified Data.DDs as DDs
import qualified Data.IDD as IDD
import qualified Data.BDD as BDD
import Transform.DDs
import qualified Transform.SmvToQBF as QCIR
import qualified QCIR.Syntax as QCIR
import qualified QCIR.Pretty as QCIR
import qualified QCIR.Solver as QCIR

--import Debug.Trace as Trace

data Args
    = ToMC
    { input :: [FilePath]
    , output :: [FilePath]
    , informula :: Maybe FilePath
    , outformula :: Maybe FilePath
    , hypertool :: Maybe HyperTool
    , flatten :: Bool
    , boolean :: Bool
    , aps :: APMode
    , explicitsingles :: Bool
    , bisim :: Bool
    , splitFormula :: Maybe SplitFormulaMode
    , k :: Int
    , sem :: QCIR.Sem
    , minimize :: Maybe Bool
    , maxddsize :: Integer
    , debug :: Bool
    , removeTemps :: Bool
    }
    | AH
    { input :: [FilePath]
    , informula :: Maybe FilePath
    , flatten :: Bool
    , boolean :: Bool
    , aps :: APMode
    , explicitsingles :: Bool
    , bisim :: Bool
    , witness :: Bool
    , splitInits :: Maybe SplitInitsMode
    , splitFormula :: Maybe SplitFormulaMode
    , ahsolver :: AutoHyper.Solver
    , ahbisim :: Bool
    , docker :: Maybe String
    , minimize :: Maybe Bool
    , maxddsize :: Integer
    , debug :: Bool
    , removeTemps :: Bool
    }
    | QBF
    { input :: [FilePath]
    , informula :: Maybe FilePath
    , flatten :: Bool
    , k :: Int
    , sem :: QCIR.Sem
    , qbfsolver :: QCIR.Solver
    , splitFormula :: Maybe SplitFormulaMode
    , witness :: Bool
    , checkTotality :: Maybe CheckTotalityMode
    , docker :: Maybe String
    , minimize :: Maybe Bool
    , maxddsize :: Integer
    , debug :: Bool
    , removeTemps :: Bool
    }
    | ToAlloy
    { input :: [FilePath]
    , output :: [FilePath]
    , defines :: Alloy.DefineMode
    , debug :: Bool
    , removeTemps :: Bool
    }
    deriving (Data,Typeable,Show,Eq)

data APMode
    = DTProduct 
    | DDLarge 
    | DDSmall
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

showAPModes :: String
showAPModes = show $ parens $ sepBy (pretty ",") $ map (pretty . show) [(minBound::APMode)..maxBound]

--apModeArgs :: APMode
--apModeArgs = enum
--    [ DDLarge &= help "consider the largest possible expressions (best for inner quantifiers)"
--    , DDSmall &= help "consider the smallest possible expressions (best for outer quantifiers)"
--    , DTProduct &= help "apply decision trees to simplify formula expressions (requires computing the product of explicit states)"
--    ]

data HyperTool = AutoHyper | HyperQube | QCIR deriving (Data,Typeable,Show,Eq,Enum,Bounded)

showHyperTools :: String
showHyperTools = show $ parens $ sepBy (pretty ",") $ map (pretty . show) [(minBound::HyperTool)..maxBound]

isBooleanHyperTool :: HyperTool -> Bool
isBooleanHyperTool QCIR = True
isBooleanHyperTool _ = False

globalBoolean :: Args -> Bool
globalBoolean args@(ToMC {}) = boolean args || maybe False isBooleanHyperTool (hypertool args)
globalBoolean args@(AH {}) = boolean args
globalBoolean args@(QBF {}) = True
globalBoolean args@(ToAlloy {}) = False

globalMinimize :: Args -> Bool
globalMinimize args@(ToMC {}) = maybe True id (minimize args)
globalMinimize args@(AH {}) = maybe True id (minimize args)
globalMinimize args@(QBF {}) = maybe True id (minimize args)
globalMinimize args@(ToAlloy {}) = False

globalExplicit :: Args -> Bool
globalExplicit args@(ToMC {}) = hypertool args == Just AutoHyper
globalExplicit args@(AH {}) = True
globalExplicit args = False

defaultToMCArgs :: Args
defaultToMCArgs = ToMC
    { input = [] &= help "input SMV files" &= name "i"
    , output = [] &= help "output files for tool"  &= name "o"
    , informula = Nothing &= help "input Hyper formula (quantifiers match the order of input SMV files)" &= name "I"
    , outformula = Nothing &= help "output Hyper formula for tool" &= name "O"
    , hypertool = Nothing &= help ("the Hyper tool to format the output for "++showHyperTools) &= name "H"
    , flatten = False &= help ("flatten and optimize SMV files via nuXmv") &= name "f"
    , boolean = False &= help ("convert to boolean SMV models via nuXmv") &= name "b"
    , aps = DDLarge &= help ("strategy to mark APs in the hyper formula (only for AutoHyper)") &= name "a"
    , explicitsingles = False &= help ("convert sub-expressions that mention only one model into variables (only for AutoHyper)") &= name "es"
    , bisim = True &= help "reduce the size of the models up to bisimulation (only for AutoHyper)"
    , splitFormula = Nothing &= help "split and send subexpressions of the formula to the LTLSPEC of each model"
    , k = 1 &= help ("number of unrolls (QCIR only)") &= name "k"
    , sem = QCIR.Pes &= help ("BMC semantics (QCIR only)") &= name "s"
    , minimize = Nothing &= help ("minimize variable names") &= name "m"
    , maxddsize = 0 &= help "set a limit to the maximum size of each in-memory DD block (0 default to no limit)"
    , debug = False &= help ("debug mode") &= name "d"
    , removeTemps = True &= help ("remove temporary files") &= name "rem"
    } &= details ["Hyper SMV to Hyper Model Checkers"] 
    
defaultAHArgs :: Args
defaultAHArgs = AH
    { input = [] &= help "input SMV files" &= name "i"
    , informula = Nothing &= help "input Hyper formula (quantifiers match the order of input SMV files)" &= name "I"
    , flatten = False &= help "flatten and optimize SMV files via nuXmv" &= name "f"
    , boolean = False &= help ("convert to boolean SMV models via nuXmv") &= name "b"
    , aps = DDLarge &= help ("strategy to mark APs in the hyper formula") &= name "a"
    , explicitsingles = False &= help ("convert sub-expressions that mention only one model into variables") &= name "es"
    , bisim = True &= help "reduce the size of the models up to bisimulation"
    , witness = False &= help "compute witnesses for outermost quantifier block" &= name "w"
    , splitInits = Nothing &= help "split the initial states of the outermost model into smaller models and solve them independently"
    , splitFormula = Nothing &= help "split and send subexpressions of the formula to the LTLSPEC of each model"
    , ahsolver = AutoHyper.Spot &= help "backend solver for automaton inclusion checking"
    , ahbisim = False &= help "compute bisimulation quotients at the AutoHyper level"
    , docker = Nothing &= help "run solver installed inside a docker container"
    , minimize = Nothing &= help ("minimize variable names") &= name "m"
    , maxddsize = 0 &= help "set a limit to the maximum size of each in-memory DD block (0 default to no limit)"
    , debug = False &= help "debug mode" &= name "d"
    , removeTemps = True &= help ("remove temporary files") &= name "rem"
    } &= details ["Hyper SMV Model Checking - AutoHyper backend"] 
    
defaultQBFArgs :: Args
defaultQBFArgs = QBF
    { input = [] &= help "input SMV files" &= name "i"
    , informula = Nothing &= help "input Hyper formula (quantifiers match the order of input SMV files)" &= name "I"
    , flatten = False &= help "flatten and optimize SMV files via nuXmv" &= name "f"
    , k = 1 &= help "number of unrolls" &= name "k"
    , sem = QCIR.Pes &= help "BMC semantics" &= name "s"
    , witness = False &= help "compute witnesses for outermost quantifier block" &= name "w"
    , checkTotality = Nothing &= help "check generated SMV models for totality"
    , qbfsolver = QCIR.Quabs &= help "QCIR solver to use" &= name "o"
    , splitFormula = Nothing &= help "split and send subexpressions of the formula to the LTLSPEC of each model (affects semantics!)"
    , docker = Nothing &= help "run solver installed inside a docker container"
    , minimize = Nothing &= help ("minimize variable names") &= name "m"
    , maxddsize = 0 &= help "set a limit to the maximum size of each in-memory DD block (0 default to no limit)"
    , debug = False &= help "debug mode" &= name "d"
    , removeTemps = True &= help ("remove temporary files") &= name "rem"
    } &= details ["Hyper SMV Model Checking - QBF backend"] 

--qcirSemArgs :: QCIR.Sem
--qcirSemArgs = enum
--    [ QCIR.Pes &= help "optimistic semantics"
--    , QCIR.Opt &= help "pessimistic semantics"
--    ]

defaultToAlloyArgs :: Args
defaultToAlloyArgs = ToAlloy
    { input = [] &= help "input SMV file" &= name "i"
    , output = [] &= help "output Alloy file" &= name "o"
    , defines = Alloy.AsPred &= help ("convert SMV defines to Alloy using one of " ++ Alloy.showDefineModes)
    , debug = False &= help "debug mode" &= name "d"
    } &= details ["Hyper SMV to Hyper Alloy"]

modeArgs :: Mode (CmdArgs Args)
modeArgs = cmdArgsMode $ modes [defaultToMCArgs, defaultAHArgs, defaultQBFArgs, defaultToAlloyArgs]
    &= summary "Hyper SMV tool"

main :: IO ()
main = do
    args <- cmdArgsRun modeArgs
    when (debug args) $ putStrLn $ "Running with arguments " ++ show args
    case args of
        ToMC {} -> mainForward args
        AH {} -> mainAH args
        QBF {} -> mainQBF args
        ToAlloy {} -> mainToAlloy args

mainForward :: Args -> IO ()
mainForward args = do
    if (hypertool args == Just QCIR)
        then when (length (output args) > 0) $ exitWithErrorMessage "Please provide only output formula filename"
        else when (length (input args) /= length (output args)) $ exitWithErrorMessage "Please provide the same number of inputs and outputs"
    when (isNothing (informula args) || isNothing (outformula args)) $ exitWithErrorMessage "Please specify input and output formula files"
    doFlatten args (input args) $ \infiles1 -> doBoolean args infiles1 $ \infiles2 boolNames -> do
        inps <- doInputs args infiles2 boolNames
        
        case hypertool args of
            Nothing -> error "please select a hyper tool"
            Just AutoHyper -> doAutoHyper args inps
            Just HyperQube -> doHyperQube args inps
            Just QCIR -> doQBF args infiles2 inps

mainAH :: Args -> IO ()
mainAH args = do
    when (isNothing (informula args)) $ exitWithErrorMessage "Please specify input formula file"
    doFlatten args (input args) $ \infiles1 -> doBoolean args infiles1 $ \infiles2 boolNames -> do
        inps <- doInputs args infiles2 boolNames
        doAutoHyper args inps

mainQBF :: Args -> IO ()
mainQBF args = do
    when (isNothing (informula args)) $ exitWithErrorMessage "Please specify input formula file"
    doFlatten args (input args) $ \infiles1 -> doBoolean args infiles1 $ \infiles2 boolNames -> do
        inps <- doInputs args infiles2 boolNames
        doQBF args infiles2 inps

doFlatten :: Args -> [FilePath] -> ([FilePath] -> IO a) -> IO a
doFlatten args infiles go = do
    (infiles1,finalizers1) <- if flatten args
        then timeIt "Flattening and optimizing input SMVs" $ do
            liftM unzip $ mapM (createSystemTemp (removeTemps args) (debug args) "flat.smv" . doOptimizeNuXMV (debug args)) infiles
        else return (infiles,[])
    res <- go infiles1
    mapM_ id finalizers1
    return res

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

doBooleanDomains :: Args -> FilePath -> FilePath -> IO FilePath
doBooleanDomains args infile outfile = do
    insmv <- readSMV infile
    outsmv <- transformBooleanDomains insmv
    writeSMV args outfile Nothing outsmv
    return outfile

mainToAlloy :: Args -> IO ()
mainToAlloy args = do
    when (length (input args) /= 1 || length (output args) /= 1) $ exitWithErrorMessage "Please specify input and output files"
    let [infile] = input args
    smv <- readSMV infile
    bsmv <- doBMState $ toPackedBmodule smv
    let alloy = Alloy.runAlloyM $ Alloy.smvToAlloy (defines args) bsmv
    let [outfile] = output args
    writeAlloy args outfile alloy

-- when to attempt to send expressions from the formula to the ltlspec of each model
globalSplitFormula :: Args -> SplitFormulaMode
globalSplitFormula args@(AH {}) = maybe LTL id (splitFormula args)
globalSplitFormula args@(ToMC {}) = maybe ifAH id (splitFormula args)
    where
    ifAH = case hypertool args of
        Just AutoHyper -> LTL
        otherwise -> NoSplitFormula
globalSplitFormula args@(QBF {}) = maybe NoSplitFormula id (splitFormula args)
globalSplitFormula args = NoSplitFormula

-- input files come with a dummy ltlspec, which we ignore
doInputs :: Args -> [FilePath] -> Maybe [Subst] -> IO ([PackedPmodule],[((Digest SHA256,Int),PackedBmodule)],Bformula,[Subst])
doInputs args infiles boolNames = do
    (insmvs,qvars,formula) <- timeIt "Parsing input SMVs and Hyper formula" $ do
        insmvs <- liftM (map (id >< dropLTLSpec)) $ readSMVs infiles
        forM (zip infiles insmvs) $ \(infile,(_,insmv)) -> do
            writeSMV args infile Nothing insmv
        
        let tys = map (moduleTypes . snd) insmvs
        let sss = map (moduleSubst . snd) insmvs
        formula <- liftM (runIdentity . substFormula sss True . sortFormula) $ readFormula args (fromJust $ informula args) tys
        let qs = quantsPformula formula
        let qvars = map snd $ groupVarSet (map fst qs) $ varsFormula formula
        when (length qs /= length insmvs) $ exitWithErrorMessage "Please provide same number of models and formula quantifiers"
        return (insmvs,qvars,formula)
    
    (midsmvs,names) <- timeIt "Processing input SMVs" $ liftM (unzip . map assocl) $ do
        mapDigestM (doSmv args) $ map assocr $ zip insmvs qvars
    
    (outsmvs,outformula) <- timeIt "Processing input formula" $ do
        let qs = quantsPformula formula
        let vars = map (b_vars . snd) midsmvs
        let hnames = joinHyperNameSubst $ zip (map fst qs) names
        let nformula = renameFormula hnames formula
        bformula <- doBM (Map.map toVarType $ joinHyperPvars $ zip (map fst qs) vars) $ toBformula nformula
        let splits = splitBformulaDigestBmodule (globalSplitFormula args) (midsmvs,bformula)
        return splits
    
    let names' = boolNames `maybeComposeSubsts` (map fromNameSubst names)
    return (map snd insmvs,outsmvs,outformula,names')

doAutoHyper :: Eq digest => Args -> ([PackedPmodule],[(digest,PackedBmodule)],Bformula,[Subst]) -> IO ()
doAutoHyper args (insmvs,smvs,formula,names) = do
    
    let qs = quantsBformula formula
    let qvars = groupVarSet (map fst qs) $ varsBformula formula
    
    chooseDD (globalBoolean args) $ \(dd :: Proxy dd) -> do
        splits <- timeIt "Converting input SMVs to explicit state" $ do
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
                            bess <- mapM toBSubst ess
                            formula2 <- substBformula bess True formula
                            formula3 <- doBSubst $ retypeBformula (Map.map toVarType hvars) formula2
                            let formula4 = normalizeBformula formula3
                            (exps2,formula5) <- checkEmptyExplicits (debug args) =<< case aps args of
                                DTProduct -> optimizeBformulaForExplicitStateDT dd (maxddsize args) (removeTemps args) (debug args) (docker args) (globalSplitFormula args) (explicitsingles args) (bisim args) exps formula4
                                DDLarge -> optimizeBformulaForExplicitStateDD dd (maxddsize args) (removeTemps args) (debug args) (docker args) (globalSplitFormula args) (explicitsingles args) (bisim args) True exps formula4
                                DDSmall -> optimizeBformulaForExplicitStateDD dd (maxddsize args) (removeTemps args) (debug args) (docker args) (globalSplitFormula args) (explicitsingles args) (bisim args) False exps formula4
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

solveAutoHyper :: Args -> [(String,Quant)] -> IO AutoHyper.Result
solveAutoHyper args qs = timeIt "Running AutoHyper" $ do
    AutoHyper.solve (debug args) (ahbisim args) (globalWitness args) (docker args) (ahsolver args) (globalOutput args qs) (globalOutformula args)
    
writeAutoHyper :: BuildDD dd => Args -> [(String,Quant)] -> [Subst] -> AutoHyper.Result -> [AutoHyper.DDExplicitHistory dd] -> IO ()
writeAutoHyper args qs names (AutoHyper.Result ty ws) hists = do
    when (globalWitness args) $ do
        let fullws = AutoHyper.backtraceWitnesses (zip (map fst qs) hists) ws
        let fullexps = map AutoHyper.sourceDDExplicitHistory hists
        let traces = AutoHyper.constructSmvTraces qs names fullws fullexps
        --let exps = map AutoHyper.targetDDExplicitHistory hists
        --let traces = AutoHyper.constructSmvTraces qs names ws exps
        writeTraces args qs traces
    putStrLn $ prettyprint ty

writeExplicitStateSystems :: BuildDD dd => Args -> [FilePath] -> [DDExplicitStateSystem dd] -> IO ()
writeExplicitStateSystems args outs exps = do
    liftIO $ mapM_ (\(out,e) -> writeExplicitStateSystem args out e) $ zip outs exps
    when (debug args) $ do
        putStrLn $ "Wrote explicit state systems"
        putStrLn $ "Model size " ++ sepString "x" (map (show . sizeExplicitStateSystem) exps)

globalSplitInits :: Args -> SplitInitsMode
globalSplitInits args = if globalSolve args then maybe NoSplitInits id (splitInits args) else NoSplitInits

doBisim :: BuildDD dd => Proxy dd -> Args -> (String,Set Pident) -> DDExplicitStateSystem dd -> (DDExplicitStateSystem dd,IntMap Int,DDExplicitStateSystem dd,Subst)
doBisim dd args (dim,vs) e = if bisim args
    then
        let (e1,renames) = projectExplicitStateSystem vs e
            (e',ss) = runIdentity $ tightDDExplicitStateSystem e1
        in (e,renames,e',ss)
    else (e,IntMap.mapWithKey (\k _ -> k) (exp_states e) ,e,Map.empty)

-- only splits outermost model
doExplicitStatesWithSplitInits :: (Eq digest,BuildDD dd) => Proxy dd -> Args -> [(String,Set Pident)] -> [(digest,PackedBmodule)] -> IO [[(DDExplicitStateSystem dd,IntMap Int,DDExplicitStateSystem dd,Subst)]]
doExplicitStatesWithSplitInits dd args (vs:vars) ((_,bsmv):bsmvs) = do
    --runDDM (b_vars bsmv) True $ testBase (b_trans bsmv)
    --liftIO $ putStrLn $ "binit " ++ prettyprint (b_init bsmv)
    ddsmv <- splitToFixedExplicitState dd args bsmv
    --forM_ ddsmv $ \x -> putStrLn $ show $ prettyExplicitStateSystem x
    ddsmvs <- doExplicitStates dd args vars bsmvs
    return $ map (\e -> doBisim dd args vs e : ddsmvs) ddsmv
doExplicitStatesWithSplitInits dd args vars bsmvs = liftM (:[]) $ doExplicitStates dd args vars bsmvs
    
splitToFixedExplicitState :: BuildDD dd => Proxy dd -> Args -> PackedBmodule -> IO [DDExplicitStateSystem dd]
splitToFixedExplicitState dd args bsmv = do
    let mode = globalSplitInits args
    let tree = DDs.proxyTreeDDs dd
    let and = DDs.proxyAndDDs dd
    let next = DDs.proxyNextDDs dd
    if maxddsize args > 0
        then withPackedDDmodule (maxddsize args) bsmv $ splitPackedDDmodule mode >=> mapM (transformDDSmvToExplicitState tree tree tree tree True (removeTemps args) (debug args) (docker args))
        else withPackedDDmodule (maxddsize args) bsmv $ splitPackedDDmodule mode >=> mapM (transformDDSmvToExplicitState and and next and True (removeTemps args) (debug args) (docker args))

doExplicitStates :: (Eq digest,BuildDD dd) => Proxy dd -> Args -> [(String,Set Pident)] -> [(digest,PackedBmodule)] -> IO [(DDExplicitStateSystem dd,IntMap Int,DDExplicitStateSystem dd,Subst)]
doExplicitStates dd args vars bsmvs = do
    exps <- mapDigestM (transformToFixedExplicitState dd (maxddsize args) True (removeTemps args) (debug args) (docker args)) bsmvs
    let refine (e,vs) = return $ doBisim dd args vs e
    liftM (map snd) $ mapDigestM refine $ map (\((d,e),vs) -> ((d,vs),(e,vs))) (zip exps vars)

doHyperQube :: Eq digest => Args -> ([PackedPmodule],[(digest,PackedBmodule)],Bformula,[Subst]) -> IO ()
doHyperQube args (insmvs,smvs,formula,names) = do
    
    let qs = map fst $ quantsBformula formula
    let vars = map (b_vars . snd) smvs
    let hvars = joinHyperPvars $ zip qs vars
    
    fdefs <- timeIt "Generating output formula" $ doBM (Map.map toVarType hvars) $ do 
        (formula2,fdefs) <- optimizeBformulaForSmv hvars formula
        liftIO $ writeFormula args (globalOutformula args) HyperQube formula2
        return fdefs
        
    timeIt "Generating output SMVs" $ do
        let outsmvs = map (doOutputSmv) $ zip (map snd smvs) fdefs
        mapM_ (\(f,s) -> writeSMV args f (Just HyperQube) s) $ zip (output args) outsmvs
    writeSubsts args names
    
doQBF :: (Eq digest) => Args -> [FilePath] -> ([PackedPmodule],[(digest,PackedBmodule)],Bformula,[Subst]) -> IO ()
doQBF args infiles (insmvs,smvs,formula,names) = do
    
    if maxddsize args > 0
        then do
            let tree = DDs.proxyTreeDDs DD.proxyBDD
            bdds <- timeIt "Encoding input SMVs and formula as BDDs" $ do
                QCIR.transformBsToBDD tree tree tree tree (maxddsize args) hvars (map snd smvs) formula
            doFixedQBF bdds
        else do
            let and = DDs.proxyAndDDs DD.proxyBDD
            let next = DDs.proxyNextDDs DD.proxyBDD
            bdds <- timeIt "Encoding input SMVs and formula as BDDs" $ do
                QCIR.transformBsToBDD and and next and (maxddsize args) hvars (map snd smvs) formula
            doFixedQBF bdds
    
  where
    qs = quantsBformula formula
    vars = map (b_vars . snd) smvs
    hvars = joinHyperPvars $ zip (map fst qs) vars
      
    doFixedQBF :: (QCIR.QBFDDs s1,QCIR.QBFDDs s2,QCIR.QBFDDs s3,QCIR.QBFDDs s4) => ([QCIR.BDDmodel s1 s2 s3 s4],QCIR.BDDformula s4) -> IO ()
    doFixedQBF bdds = do
    
        qcirnames <- timeIt "Generating output QCIR" $ do
            let (qcir,qcirnames) = runIdentity $ uncurry (QCIR.transformBDDToQCIR (k args) (sem args)) bdds
            liftIO $ writeQCIR args (globalOutformula args) qcir
            return qcirnames
        
        let names' = names `composeIntSubsts` (map (IntMap.map fromNameSubst) qcirnames)
        
        if globalSolve args
            then solveQBF args qs infiles (zip (map fst smvs) insmvs) names'
            else writeIntSubsts args names'

verdictQBF :: (Eq digest) => Args -> [(String,Quant)] -> [FilePath] -> [(digest,PackedPmodule)] -> QCIR.ResultType -> [Maybe Trace] -> ErrorT IO [String]
verdictQBF args qs infiles insmvs ty traces = do
    
    -- check semantics
    case (QCIR.isOptimisticSem (sem args),ty) of
        (True,QCIR.SAT) -> do
            lift $ writeTraces args qs traces
            throwErrorT $ "optimistic semantics"
        (True,QCIR.UNSAT) -> return ()
        (False,QCIR.SAT) -> return ()
        (False,QCIR.UNSAT) -> do
            lift $ writeTraces args qs traces
            throwErrorT $ "pessimistic semantics"
    
    -- check infinite lifting for existing traces
    fulltraces <- doInfiniteTraces args qs (map snd insmvs) traces
    
    -- check deadlocks for remaining models
    let remaining = catMaybes $ map (\((dim,q),f,(d,smv),tr) -> if tr then Nothing else Just (d,(dim,f))) $ zip4 qs infiles insmvs fulltraces
    doNoDeadlocks args remaining

solveQBF :: (Eq digest) => Args -> [(String,Quant)] -> [FilePath] -> [(digest,PackedPmodule)] -> [IntMap Subst] -> IO ()
solveQBF args qs infiles insmvs names = timeIt "Running QBF solver" $ do
    QCIR.Result ty vals <- QCIR.solve (debug args) (qbfsolver args) (globalWitness args) (docker args) (globalOutformula args)
    traces <- if globalWitness args
        then return $ QCIR.constructSmvTraces qs names vals
        else return $ map (const Nothing) qs
    verdict <- runErrorT $ verdictQBF args qs infiles insmvs ty traces
    putStrLn $ show $ pretty ty <+> parens (printVerdict verdict)

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
                res <- lift $ doFindTrace (debug args) smvfile
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

printVerdict :: Either String [String] -> Doc ann
printVerdict (Right []) = pretty "conclusive"
printVerdict (Right dims) = pretty "conclusive" <+> pretty "-" <+> "assuming totality of" <+> hsep (map pretty dims)
printVerdict (Left str) = pretty "inconclusive" <+> pretty "-" <+> pretty str

globalWitness :: Args -> Bool
globalWitness args@(AH {}) = witness args
globalWitness args@(QBF {}) = witness args
globalWitness args = False

globalOutput :: Args -> [(String,Quant)] -> [FilePath]
globalOutput args@(AH {}) qs = map (\(dim,_) -> "out"++dim++".exp") qs
globalOutput args qs = output args

globalOutformula :: Args -> FilePath
globalOutformula args@(ToMC {}) = maybe "out.formula" id (outformula args)
globalOutformula args@(AH {}) = "out.ah"
globalOutformula args@(QBF {}) = "out.qcir"

globalSolve :: Args -> Bool
globalSolve args@(AH {}) = True
globalSolve args@(QBF {}) = True
globalSolve args = False

doSmv :: Args -> (PackedPmodule,Set Pident) -> IO (PackedBmodule,NameSubst)
doSmv args (smv,used) = doBMState $ do
    smv1 <- toInlinedPackedBmodule smv
    let smv2 = dropUnusedBmoduleVars used smv1
    if globalMinimize args
        then transformBminimize smv2
        else return (smv2,idNameSubst $ b_vars smv2)

doOutputSmv :: (PackedBmodule,Subst) -> PackedPmodule
doOutputSmv (p,ss) = runIdentity $ doBMState $ do
    p1 <- fromPackedBmodule p
    return $ addPmoduleDefines ss p1

writeSMV :: Args -> FilePath -> Maybe HyperTool -> PackedPmodule -> IO ()
writeSMV args f tool smv = do
    writeFile f $ prettySMV (mkSmvMode False tool) smv
    when (debug args) $ putStrLn $ "Wrote SMV file " ++ f

writeExplicitStateSystem :: DD.IsVal val => Args -> FilePath -> ExplicitStateSystem Pident val -> IO ()
writeExplicitStateSystem args f explicit = do
    writeFile f $ show $ prettyExplicitStateSystem explicit
    when (debug args) $ putStrLn $ "Wrote explicit state file " ++ f

-- currently alloy/eletrod may not generate some variables used in the formula since they are trivially false
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

readFormula :: Args -> FilePath -> [PackedPtypes] -> IO Pformula
readFormula args fn tys = do
    txt <- BS.readFile fn
    f <- ioErrorM $ runFormulaParser fn txt >>= return . L.unloc
    f <- doFillFormulaVars args tys f
    return $ addFormulaTypes tys f

writeFormula :: Args -> FilePath -> HyperTool -> Pformula -> IO ()
writeFormula args fn tool formula = do
    writeFile fn $ prettySMV (mkSmvMode True $ Just tool) $ normalizeFormula formula
    when (debug args) $ putStrLn $ "Wrote formula file " ++ fn

writeAlloy :: Args -> FilePath -> Alloy.Alloy -> IO ()
writeAlloy args f alloy = do
    writeFile f $ prettyprint alloy
    when (debug args) $ putStrLn $ "Wrote Alloy file " ++ f

writeQCIR :: Args -> FilePath -> QCIR.QCIR -> IO ()
writeQCIR args f qcir = do
    writeFile f $ prettyprint qcir
    when (debug args) $ do
        putStrLn $ "Wrote QCIR file " ++ f
        getFileSize f >>= \sz -> putStrLn $ "Model size " ++ formatBytes sz

timeIt :: MonadIO m => String -> m a -> m a
timeIt msg m = do
    liftIO $ putStrLn msg
    (a,seconds) <- measureTime m
    liftIO $ putStrLn $ "Took " ++ show seconds ++ "s"
    return a

measureTime :: MonadIO m => m a -> m (a,Double)
measureTime action = do
  start <- liftIO $ getTime Monotonic
  result <- action
  end <- liftIO $ getTime Monotonic
  let diff = fromIntegral (toNanoSecs (diffTimeSpec end start)) / 1e9
  return (result, diff)

mkSmvMode :: Bool -> Maybe HyperTool -> Smv.SmvMode
mkSmvMode _ Nothing = Smv.Default
mkSmvMode isFormula (Just AutoHyper) = Smv.AutoHyper (if isFormula then Smv.Hyper else Smv.Smv)
mkSmvMode isFormula (Just HyperQube) = Smv.HyperQube (if isFormula then Smv.Hyper else Smv.Smv)
    
writeSubsts :: Args -> [Subst] -> IO ()
writeSubsts args sss = forM_ (zip (input args) sss) $ \(infile,ss) -> do
    let f = addExtension infile "names"
    writeFile f $ unlines $ map (\(n,e) -> prettyprint n ++ " := " ++ prettyprint e) $ Map.toList ss
    when (debug args) $ putStrLn $ "Wrote names file " ++ f

writeIntSubsts :: Args -> [IntMap Subst] -> IO ()
writeIntSubsts args ssss = forM_ (zip (input args) ssss) $ \(infile,sss) -> do
    K.forWithKeyM_ sss $ \i ss -> do
        let f = addExtension (addExtension infile "names") (show i)
        writeFile f $ unlines $ map (\(n,e) -> prettyprint n ++ " := " ++ prettyprint e) $ Map.toList ss
        when (debug args) $ putStrLn $ "Wrote names file " ++ f

writeTraces :: Args -> [(String,Quant)] -> [Maybe Smv.Trace] -> IO ()
writeTraces args qs traces = forM_ (zip qs traces) $ \((dim,_),mbtrace) -> forM_ mbtrace $ \trace -> do
    let f = addExtension dim "witness"
    writeFile f $ prettyprint trace
    when (debug args) $ putStrLn $ "Wrote witness file " ++ f

data CheckTotalityMode
    = CheckFsmNuXmv 
    | CheckSpecNuXmv
    | CheckTotalExplicitState
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

doCheckSmvTotality :: Args -> CheckTotalityMode -> FilePath -> IO Bool
doCheckSmvTotality args mode file = do
    when (debug args) $ putStrLn $ "Reading SMV file " ++ show file ++ " for totality check " ++ show mode
    case mode of
        CheckFsmNuXmv -> Smv.doCheckFsmNuXMV (debug args) file
        CheckSpecNuXmv -> Smv.doCheckSpecTotalNuXMV (debug args) file
        CheckTotalExplicitState -> chooseDD (globalBoolean args) $ \dd -> do
            pmodule <- readSMV file
            bmodule <- doBMState $ toInlinedPackedBmodule pmodule
            exps <- transformToFixedExplicitState dd (maxddsize args) False (removeTemps args) (debug args) (docker args) bmodule
            return $ isTotalExplicitStateSystem exps
    
