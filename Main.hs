-- | Entry point for @hypersmv@.
module Main where

import System.Console.CmdArgs
import System.Directory
import System.Environment (getExecutablePath)
import System.IO
import Control.Monad
import Data.Maybe

import Error
import Cli.Args
import Cli.Common
import Cli.AH
import Cli.QBF
import Cli.HyperQube
import Cli.Alloy

-- | Parse CLI arguments and dispatch to the selected mode-
main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    args <- cmdArgsRun modeArgs
    when (debug args) $ do
        putStrLn $ "Running with arguments " ++ show args
        exe <- getExecutablePath
        mt <- getModificationTime exe
        putStrLn $ "Binary " ++ exe ++ " (built " ++ show mt ++ ")"
    case args of
        ToMC {} -> mainForward args
        AH {} -> mainAH args
        QBF {} -> mainQBF args
        ToAlloy {} -> mainToAlloy args

-- | Run ToMC mode.
mainForward :: Args -> IO ()
mainForward args = do
    if (hypertool args == Just QCIR)
        then when (length (output args) > 0) $ exitWithErrorMessage "Please provide only output formula filename"
        else when (length (input args) /= length (output args)) $ exitWithErrorMessage "Please provide the same number of inputs and outputs"
    when (isNothing (informula args) || isNothing (outformula args)) $ exitWithErrorMessage "Please specify input and output formula files"
    doFlatten args (input args) $ \infiles1 -> doBoolean args infiles1 $ \infiles2 boolNames -> do
        doInputs args infiles2 boolNames $ \infiles3 inps ->
            case hypertool args of
                Nothing -> error "please select a hyper tool"
                Just AutoHyper -> doAutoHyper args inps
                Just HyperQube -> doHyperQube args inps
                Just QCIR -> doQBF args infiles3 inps

-- | Run AH mode.
mainAH :: Args -> IO ()
mainAH args = do
    when (isNothing (informula args)) $ exitWithErrorMessage "Please specify input formula file"
    doFlatten args (input args) $ \infiles1 -> doBoolean args infiles1 $ \infiles2 boolNames -> do
        doInputs args infiles2 boolNames $ \infiles3 inps ->
            doAutoHyper args inps

-- | Run QBF mode.
mainQBF :: Args -> IO ()
mainQBF args = do
    when (isNothing (informula args)) $ exitWithErrorMessage "Please specify input formula file"
    doFlatten args (input args) $ \infiles1 -> doBoolean args infiles1 $ \infiles2 boolNames -> do
        doInputs args infiles2 boolNames $ \infiles3 inps ->
            doQBF args infiles3 inps
