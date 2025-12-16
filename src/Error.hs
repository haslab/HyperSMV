module Error where

import System.Exit
import System.IO
import Control.Monad.Except
import Control.Monad.Trans.Except
import Control.Monad.Fail
import Prettyprinter

import qualified Location as L

type ErrorM = (Either String)

instance MonadFail ErrorM where
    fail = throwErrorM

successErrorM :: ErrorM a -> a
successErrorM (Left err) = error err
successErrorM (Right v) = v

throwErrorM :: String -> ErrorM a
throwErrorM msg = throwError msg

ioErrorM :: ErrorM a -> IO a
ioErrorM (Left err) = exitWithErrorMessage err
ioErrorM (Right a) = return a

exitWithErrorMessage :: String -> IO a
exitWithErrorMessage msg = hPutStrLn stderr msg >> exitFailure

type ErrorT m = ExceptT String m

throwErrorT :: Monad m => String -> ErrorT m a
throwErrorT msg = throwError msg

runErrorT :: Monad m => ErrorT m a -> m (Either String a)
runErrorT = runExceptT

ioErrorT :: ErrorT IO a -> IO a
ioErrorT m = do
    e <- runExceptT m
    ioErrorM e
