module Smv.Solver where

import qualified Shelly
import Data.Text (Text(..))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Map (Map(..))
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Control.Monad
import Data.ByteString.Lazy (ByteString(..))
import qualified Data.ByteString.Lazy as BS
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import Data.List as List
import Crypto.Hash (Digest, SHA256)
import qualified Crypto.Hash as Crypto
import Control.Monad.IO.Class

import Utils
import Error
import qualified Location as L
import Transform.Bpacked
import Transform.Substitute
import Smv.Trace as Smv
import Smv.Syntax
import Smv.Parser
import Smv.Typing
import Smv.Packed
import Smv.Pretty hiding (SmvMode(..))
import qualified Smv.Pretty as Smv

doOptimizeNuXMV :: Bool -> FilePath -> FilePath -> IO FilePath
doOptimizeNuXMV isDebug infile outfile = Shelly.shelly $ shellyMode isDebug $ do
    Shelly.setStdin $ nuXmvOptimizeScript infile outfile
    Shelly.run_ "nuXmv" ["-int"] 
    return outfile
    
nuXmvOptimizeScript :: FilePath -> FilePath -> Text
nuXmvOptimizeScript infile outfile = T.unlines
    ["read_model -i " <> T.pack infile <> ";"
    ,"flatten_hierarchy;"
    ,"encode_variables;"
    ,"build_flat_model;"
    ,"write_simplified_model_rel -o " <> T.pack outfile <> ";"
    ,"quit;"]

doCheckFsmNuXMV :: Bool -> FilePath -> IO Bool
doCheckFsmNuXMV isDebug infile = Shelly.shelly $ shellyMode isDebug $ do
    Shelly.setStdin $ nuXmvCheckFSMScript infile
    out <- Shelly.run "nuXmv" ["-int"] 
    return $ (not $ T.isInfixOf "finite state machine is empty" out) && T.isInfixOf "No deadlock state exists" out
    
nuXmvCheckFSMScript :: FilePath -> Text
nuXmvCheckFSMScript infile = T.unlines
    ["read_model -i " <> T.pack infile <> ";"
    ,"flatten_hierarchy;"
    ,"encode_variables;"
    ,"build_model;"
    ,"check_fsm;"
    ,"quit;"]
    
doCheckSpecTotalNuXMV :: Bool -> FilePath -> IO Bool
doCheckSpecTotalNuXMV isDebug infile = Shelly.shelly $ shellyMode isDebug $ do
    Shelly.setStdin $ nuXmvCheckSpecTotalScript infile
    out <- Shelly.run "nuXmv" ["-int"] 
    let ls = T.lines out
    case find (T.isInfixOf "specification AG (EX TRUE)") ls of
        Nothing -> error $ "doCheckSpecTotalNuXMV unexpected output" 
        Just l ->
            if T.isInfixOf "is true" l then return True
            else if T.isInfixOf "is false" l then return False
            else error $ "doCheckSpecTotalNuXMV unexpected boolean output" 
    
nuXmvCheckSpecTotalScript :: FilePath -> Text
nuXmvCheckSpecTotalScript infile = T.unlines
    ["read_model -i " <> T.pack infile <> ";"
    ,"flatten_hierarchy;"
    ,"encode_variables;"
    ,"build_model;"
    ,"check_ctlspec -p \"AG EX TRUE\";"
    ,"quit;"]

-- we make sure that this transformation does not drop original defines, since they may be used in the formula
doBooleanNuXMV :: Bool -> FilePath -> FilePath -> IO (FilePath,Subst)
doBooleanNuXMV isDebug infile outfile = do
    smv <- readSMV infile
    let invars = p_vars smv
    let indefs = p_defines smv
    Shelly.shelly $ shellyMode isDebug $ do
        Shelly.setStdin $ nuXmvBooleanScript infile outfile
        Shelly.run_ "nuXmv" ["-int"] 
    let left = Map.traverseMissing $ \v t -> return $ Peident v $ toExprType t
    let right = Map.dropMissing
    let match = Map.zipWithMaybeAMatched $ \k x y -> return $ Just y
    let mkBoolNames outdefs = Map.merge left right match invars outdefs
    boolNames <- liftM (mkBoolNames . moduleSubst) $ readSMV outfile
    appendFile outfile $ "\n" ++ (Smv.prettySMV Smv.Default $ Pidefine $ map L.dummyLoc $ unpackPdefines indefs)
    return (outfile,boolNames)
    
nuXmvBooleanScript :: FilePath -> FilePath -> Text
nuXmvBooleanScript infile outfile = T.unlines
    ["read_model -i " <> T.pack infile <> ";"
    ,"flatten_hierarchy;"
    ,"encode_variables;"
    ,"build_boolean_model;"
    ,"write_boolean_model -o " <> T.pack outfile <> ";"
    ,"quit;"]

doFindTraceK :: Bool -> FilePath -> Int -> IO (Maybe Trace)
doFindTraceK isDebug infile k = do
    out <- Shelly.shelly $ shellyMode isDebug $ do
        Shelly.setStdin $ nuXmvFindKScript infile k
        Shelly.run "nuXmv" ["-int"]
    return (error "doFindTraceK") -- TODO

nuXmvFindKScript :: FilePath -> Int -> Text
nuXmvFindKScript infile k = T.unlines
    ["read_model -i " <> T.pack infile <> ";"
    ,"go_bmc;"
    ,"check_ltlspec_bmc -k " <> T.pack (show k) <> ";"
    ,"quit;"]

doFindTrace :: Bool -> FilePath -> IO (Maybe Trace)
doFindTrace isDebug infile = do
    out <- Shelly.shelly $ shellyMode isDebug $ do
        Shelly.setStdin $ nuXmvFindScript infile
        Shelly.run "nuXmv" ["-int"]
    return (error "doFindTrace") -- TODO

nuXmvFindScript :: FilePath -> Text
nuXmvFindScript infile = T.unlines
    ["read_model -i " <> T.pack infile <> ";"
    ,"check_ltlspec -n 1;"
    ,"quit;"]

readSMV :: FilePath -> IO PackedPmodule
readSMV f = do
    txt <- BS.readFile f
    parseSMV f txt

readSMVs :: [FilePath] -> IO [(Digest SHA256,PackedPmodule)]
readSMVs fs = liftM (map (id >< snd)) $ State.execStateT (mapM go fs) []
    where
    go :: FilePath -> StateT [(Digest SHA256,(FilePath,PackedPmodule))] IO ()
    go path = do
        m <- State.get
        let swapl (x,(y,z)) = (y,(x,z))
        (h,smv) <- case List.lookup path (map swapl m) of
            Just (h,smv) -> return (h,smv)
            Nothing -> do
                txt <- liftIO $ BS.readFile path
                let h = Crypto.hash $ BS.toStrict txt
                case List.lookup h m of
                    Just (_,smv) -> return (h,smv)
                    Nothing -> liftM (h,) $ liftIO $ parseSMV path txt
        State.modify $ \m -> m ++ [(h,(path,smv))]

parseSMV :: FilePath -> ByteString -> IO PackedPmodule
parseSMV f txt = do
    m <- ioErrorM $ runSMVParser f txt >>= packPmodule . L.unloc
    return $ addModuleTypes m