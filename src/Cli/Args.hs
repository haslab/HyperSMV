-- | CLI argument types, defaults, and accessors for @hypersmv@'s four run modes.
module Cli.Args where

import System.Console.CmdArgs
import Prettyprinter

import Pretty
import qualified ExplicitState.AutoHyper as AutoHyper
import Transform.Bexpr.Packed
import Transform.Pexpr
import Transform.DD.Split
import qualified Alloy.Translate as Alloy
import qualified QBF.Solver as QBF
import qualified QBF.Model as QBF

-- | How to check a model for totality (no deadlocks).
data CheckTotalityMode
    = CheckFsmNuXmv
    | CheckSpecNuXmv
    | CheckTotalExplicitState
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

-- | Parsed CLI arguments, one record per run mode.
data Args
    = ToMC
    { input :: [FilePath]
    , output :: [FilePath]
    , informula :: Maybe FilePath
    , outformula :: Maybe FilePath
    , hypertool :: Maybe HyperTool
    , flatten :: Bool
    , boolean :: Bool
    , observe :: ObserveMode
    , compactaps :: Bool
    , bisim :: Bool
    , splitFormula :: Maybe SplitFormulaMode
    , k :: Int
    , sem :: QBF.Sem
    , docker :: Maybe String
    , minimize :: Maybe Bool
    , debug :: Bool
    , removeTemps :: Bool
    }
    | AH
    { input :: [FilePath]
    , informula :: Maybe FilePath
    , flatten :: Bool
    , boolean :: Bool
    , observe :: ObserveMode
    , compactaps :: Bool
    , bisim :: Bool
    , witness :: Bool
    , splitInits :: Maybe SplitInitsMode
    , splitFormula :: Maybe SplitFormulaMode
    , ahsolver :: AutoHyper.Solver
    , ahbisim :: Bool
    , ahobserve :: ObserveMode
    , ahvalueaps :: Bool
    , ahdomainfold :: Bool
    , docker :: Maybe String
    , minimize :: Maybe Bool
    , debug :: Bool
    , removeTemps :: Bool
    , dropltlspec :: Bool
    }
    | QBF
    { input :: [FilePath]
    , informula :: Maybe FilePath
    , flatten :: Bool
    , boolean :: Bool
    , k :: Int
    , sem :: QBF.Sem
    , qbfsolver :: QBF.Solver
    , splitFormula :: Maybe SplitFormulaMode
    , witness :: Bool
    , checkTotality :: Maybe CheckTotalityMode
    , selfLoops :: Bool
    , docker :: Maybe String
    , minimize :: Maybe Bool
    , debug :: Bool
    , removeTemps :: Bool
    }
    | ToAlloy
    { input :: [FilePath]
    , output :: [FilePath]
    , defines :: Alloy.DefineMode
    , informula :: Maybe FilePath
    , outformula :: Maybe FilePath
    , k :: Int
    , alloyExpect :: Int
    , debug :: Bool
    , removeTemps :: Bool
    }
    deriving (Data,Typeable,Show,Eq)

-- | What a bisimulation quotient observes: atoms or variables.
data ObserveMode
    = Vars
    | Atoms
    deriving (Data,Typeable,Show,Eq,Enum,Bounded)

-- | Target hyperproperty checker for ToMC mode.
data HyperTool = AutoHyper | HyperQube | QCIR deriving (Data,Typeable,Show,Eq,Enum,Bounded)

-- | List supported 'HyperTool' names for help text.
showHyperTools :: String
showHyperTools = show $ parens $ sepBy (pretty ",") $ map (pretty . show) [(minBound::HyperTool)..maxBound]

-- | Whether a 'HyperTool' requires a booleanised model.
isBooleanHyperTool :: HyperTool -> Bool
isBooleanHyperTool QCIR = True
isBooleanHyperTool _ = False

-- | Whether to booleanise input SMVs.
globalBoolean :: Args -> Bool
globalBoolean args@(ToMC {}) = boolean args || maybe False isBooleanHyperTool (hypertool args)
globalBoolean args@(AH {}) = boolean args
globalBoolean args@(QBF {}) = boolean args -- boolean stays the default because it is usually faster
globalBoolean args@(ToAlloy {}) = False

-- | Whether to quotient the models up to bisimulation before building the explicit-state systems.
globalBisimMode :: Args -> Bool
globalBisimMode args@(ToMC {}) = bisim args
globalBisimMode args@(AH {}) = bisim args
globalBisimMode _ = False

-- | TreeDDs support-accept budget for the explicit encoder.
explicitSupportAccept :: Integer
explicitSupportAccept = 65536

-- | TreeDDs support-accept budget for the symbolic encoder.
qbfSupportAccept :: Integer
qbfSupportAccept = 8192

-- | Whether to minimize variable names.
globalMinimize :: Args -> Bool
globalMinimize args@(ToMC {}) = maybe True id (minimize args)
globalMinimize args@(AH {}) = maybe True id (minimize args)
globalMinimize args@(QBF {}) = maybe True id (minimize args)
globalMinimize args@(ToAlloy {}) = False

-- | Whether this mode builds an explicit-state system.
globalExplicit :: Args -> Bool
globalExplicit args@(ToMC {}) = hypertool args == Just AutoHyper
globalExplicit args@(AH {}) = True
globalExplicit args = False

-- | Whether to drop JUSTICE fairness (AH mode only).
globalDropltlspec :: Args -> Bool
globalDropltlspec args@(AH {}) = dropltlspec args
globalDropltlspec _ = False

-- | Default CLI arguments for ToMC mode.
defaultToMCArgs :: Args
defaultToMCArgs = ToMC
    { input = [] &= help "input SMV files" &= name "i"
    , output = [] &= help "output files for tool"  &= name "o"
    , informula = Nothing &= help "input Hyper formula (quantifiers match the order of input SMV files)" &= name "I"
    , outformula = Nothing &= help "output Hyper formula for tool" &= name "O"
    , hypertool = Nothing &= help ("the Hyper tool to format the output for "++showHyperTools) &= name "H"
    , flatten = False &= help ("flatten and optimize SMV files via nuXmv") &= name "f"
    , boolean = False &= help ("convert to boolean SMV models via nuXmv") &= name "b"
    , observe = Atoms &= help "what the bisimulation observes (AutoHyper only)"
    , compactaps = True &= help "collapse APs (AutoHyper only)" &= name "caps"
    , bisim = True &= help "reduce the models up to bisimulation before building explicit-state systems (AutoHyper only)"
    , splitFormula = Nothing &= help "split and send subexpressions of the formula to the LTLSPEC of each model"
    , k = 1 &= help ("number of unrolls (QCIR only)") &= name "k"
    , sem = QBF.Pes &= help ("BMC semantics (QCIR only)") &= name "s"
    , docker = Nothing &= help "run solver installed inside a docker container"
    , minimize = Nothing &= help ("minimize variable names") &= name "m"
    , debug = False &= help ("debug mode") &= name "d"
    , removeTemps = True &= help ("remove temporary files") &= name "rem"
    } &= details ["Hyper SMV to Hyper Model Checkers"] 
    
-- | Default CLI arguments for AH mode.
defaultAHArgs :: Args
defaultAHArgs = AH
    { input = [] &= help "input SMV files" &= name "i"
    , informula = Nothing &= help "input Hyper formula (quantifiers match the order of input SMV files)" &= name "I"
    , flatten = False &= help "flatten and optimize SMV files via nuXmv" &= name "f"
    , boolean = False &= help ("convert to boolean SMV models via nuXmv") &= name "b"
    , observe = Atoms &= help "what the bisimulation observes"
    , compactaps = True &= help "collapse APs" &= name "caps"
    , bisim = True &= help "reduce the models up to bisimulation before building explicit-state systems"
    , witness = False &= help "compute witnesses for outermost quantifier block" &= name "w"
    , splitInits = Nothing &= help "split the initial states of the outermost model into smaller models and solve them independently"
    , splitFormula = Nothing &= help "split and send subexpressions of the formula to the LTLSPEC of each model"
    , ahsolver = AutoHyper.Spot &= help "backend solver for automaton inclusion checking"
    , ahbisim = False &= help "compute bisimulation quotients at the AutoHyper level"
    , ahobserve = Atoms &= help "AutoHyper bisimulation observations" &= name "ahobs"
    , ahvalueaps = True &= help "AutoHyper AP compaction" &= name "ahvaps"
    , ahdomainfold = True &= help "AutoHyper AP folding" &= name "ahdf"
    , docker = Nothing &= help "run solver installed inside a docker container"
    , minimize = Nothing &= help ("minimize variable names") &= name "m"
    , debug = False &= help "debug mode" &= name "d"
    , removeTemps = True &= help ("remove temporary files") &= name "rem"
    , dropltlspec = False &= help "drop LTLSPEC (only sensible for Alloy/electrod-generated SMV)"
    } &= details ["Hyper SMV Model Checking - AutoHyper backend"]
    
-- | Default CLI arguments for QBF mode.
defaultQBFArgs :: Args
defaultQBFArgs = QBF
    { input = [] &= help "input SMV files" &= name "i"
    , informula = Nothing &= help "input Hyper formula (quantifiers match the order of input SMV files)" &= name "I"
    , flatten = False &= help "flatten and optimize SMV files via nuXmv" &= name "f"
    , boolean = True &= help "convert to boolean SMV models via nuXmv"
    , k = 1 &= help "number of unrolls" &= name "k"
    , sem = QBF.Pes &= help "BMC semantics" &= name "s"
    , witness = False &= help "compute witnesses for outermost quantifier block" &= name "w"
    , checkTotality = Nothing &= help "check generated SMV models for totality"
    , selfLoops = False &= help "since bounded semantics has no loops, invent dummy loops at the end of witness traces. these loops are not validated, so this is easily unsound."
    , qbfsolver = QBF.Quabs &= help "QCIR solver to use" &= name "o"
    , splitFormula = Nothing &= help "split and send subexpressions of the formula to the LTLSPEC of each model (MAY affect semantics!)"
    , docker = Nothing &= help "run solver installed inside a docker container"
    , minimize = Nothing &= help ("minimize variable names") &= name "m"
    , debug = False &= help "debug mode" &= name "d"
    , removeTemps = True &= help ("remove temporary files") &= name "rem"
    } &= details ["Hyper SMV Model Checking - QBF backend"] 

-- | Default CLI arguments for ToAlloy mode.
defaultToAlloyArgs :: Args
defaultToAlloyArgs = ToAlloy
    { input = [] &= help "input SMV file" &= name "i"
    , output = [] &= help "output Alloy file" &= name "o"
    , defines = Alloy.AsPred &= help ("convert SMV defines to Alloy using one of " ++ Alloy.showDefineModes)
    , informula = Nothing &= help "input Hyper formula to translate to an Alloy check block" &= name "I"
    , outformula = Nothing &= help "output Alloy check-block file" &= name "O"
    , k = 10 &= help "Alloy 'for N steps' scope" &= name "k"
    , alloyExpect = 0 &= help "Alloy 'expect' bit" &= name "e"
    , debug = False &= help "debug mode" &= name "d"
    , removeTemps = True &= help ("remove temporary files") &= name "rem"
    } &= details ["Hyper SMV to Hyper Alloy"]

-- | Combined 'cmdargs' mode for parsing @argv@ into 'Args'.
modeArgs :: Mode (CmdArgs Args)
modeArgs = cmdArgsMode $ modes [defaultToMCArgs, defaultAHArgs, defaultQBFArgs, defaultToAlloyArgs]
    &= summary "Hyper SMV tool"

-- | The formula splitting mode to use.
globalSplitFormula :: Args -> SplitFormulaMode
globalSplitFormula args@(AH {}) = maybe LTL id (splitFormula args)
globalSplitFormula args@(ToMC {}) = maybe ifAH id (splitFormula args)
    where
    ifAH = case hypertool args of
        Just AutoHyper -> LTL
        otherwise -> NoSplitFormula
globalSplitFormula args@(QBF {}) = maybe NoSplitFormula id (splitFormula args)
globalSplitFormula args = NoSplitFormula

-- | The initial-state splitting mode to use.
globalSplitInits :: Args -> SplitInitsMode
globalSplitInits args = if globalSolve args then maybe NoSplitInits id (splitInits args) else NoSplitInits

-- | Whether to compute witnesses.
globalWitness :: Args -> Bool
globalWitness args@(AH {}) = witness args
globalWitness args@(QBF {}) = witness args
globalWitness args = False

-- | Output file paths per quantified dimension.
globalOutput :: Args -> [(String,Quant)] -> [FilePath]
globalOutput args@(AH {}) qs = map (\(dim,_) -> "out"++dim++".exp") qs
globalOutput args qs = output args

-- | The output formula file path.
globalOutformula :: Args -> FilePath
globalOutformula args@(ToMC {}) = maybe "out.formula" id (outformula args)
globalOutformula args@(AH {}) = "out.ah"
globalOutformula args@(QBF {}) = "out.qcir"
globalOutformula args@(ToAlloy {}) = "out.als"

-- | Whether this mode invokes a solver.
globalSolve :: Args -> Bool
globalSolve args@(AH {}) = True
globalSolve args@(QBF {}) = True
globalSolve args = False

