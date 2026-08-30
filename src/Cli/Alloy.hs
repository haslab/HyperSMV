-- | The SMV-to-Alloy export driver.
module Cli.Alloy where

import System.FilePath
import Data.List as List
import qualified Data.ByteString.Lazy as BS
import Control.Monad
import Data.Maybe
import qualified Data.Map as Map

import Error
import Pretty
import qualified Location as L
import Smv.Syntax
import Smv.Parser
import Smv.Solver as Smv
import Transform.Bexpr
import Transform.Bexpr.Packed
import qualified Alloy.Syntax as Alloy
import qualified Alloy.Gates as Alloy
import qualified Alloy.Translate as Alloy
import Alloy.Pretty ()

import Cli.Args

-- | Read one or more SMV files; translate each to an Alloy model, translate a HyperLTL formula over all of them into an Alloy 'check' block.
mainToAlloy :: Args -> IO ()
mainToAlloy args = do
    when (null (input args)) $ exitWithErrorMessage "Please specify at least one input SMV file"
    when (not (null (output args)) && length (output args) /= length (input args)) $
        exitWithErrorMessage "Please specify one output file per input SMV file"
    when (null (output args) && isNothing (informula args)) $
        exitWithErrorMessage "Please specify --output and/or --informula"
    forM_ (zip (input args) (output args)) $ \(infile,outfile) -> do
        smv <- readSMV infile
        bsmv <- doBMState $ toPackedBmodule smv
        writeAlloy args outfile $ Alloy.runAlloyM $ Alloy.smvToAlloy (defines args) bsmv
    case informula args of
        Nothing -> return ()
        Just informulaFile -> do
            outformulaFile <- maybe (exitWithErrorMessage "Please specify --outformula") return (outformula args)
            txt <- BS.readFile informulaFile
            pformula <- ioErrorM $ liftM L.unloc $ runFormulaParser informulaFile txt
            when (numQuantifiers pformula /= length (input args)) $
                exitWithErrorMessage "Please provide the same number of models and formula quantifiers"
            let distinctInputs = List.nub (input args)
            let aliasOf = Map.fromList $ if length distinctInputs <= 1
                    then [ (f,Nothing) | f <- distinctInputs ]
                    else zip distinctInputs (map (Just . ("M"++) . show) [1..])
            ctxOf <- liftM Map.fromList $ forM distinctInputs $ \infile -> do
                smv <- readSMV infile
                bsmv <- doBMState $ toPackedBmodule smv
                let (_,st) = Alloy.runAlloyM' $ Alloy.smvToAlloy (defines args) bsmv
                return (infile, Alloy.mkModelCtx (aliasOf Map.! infile) st)
            let checkName = takeBaseName outformulaFile
            let models = [ ctxOf Map.! infile | infile <- input args ]
            let imports = [ Alloy.Import (takeBaseName infile) (aliasOf Map.! infile) | infile <- distinctInputs ]
            let item = Alloy.formulaToAlloyCheck checkName (k args) (alloyExpect args) models pformula
            writeAlloy args outformulaFile $ Alloy.Alloy imports [item]

-- | Write an Alloy model to a file.
writeAlloy :: Args -> FilePath -> Alloy.Alloy -> IO ()
writeAlloy args f alloy = do
    writeFile f $ prettyprint alloy
    when (debug args) $ putStrLn $ "Wrote Alloy file " ++ f

