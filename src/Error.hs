-- | Error-handling helpers.
module Error where

import System.Exit
import System.IO
import Control.Monad.Except


-- | A computation that may fail with an error message.
type ErrorM = (Either String)

instance MonadFail ErrorM where
    fail = throwErrorM

-- | Unwraps a successful 'ErrorM', crashing otherwise.
successErrorM :: ErrorM a -> a
successErrorM (Left err) = error err
successErrorM (Right v) = v

-- | Fails with an error message.
throwErrorM :: String -> ErrorM a
throwErrorM msg = throwError msg

-- | Runs an 'ErrorM' in 'IO', exiting on failure.
ioErrorM :: ErrorM a -> IO a
ioErrorM (Left err) = exitWithErrorMessage err
ioErrorM (Right a) = return a

-- | Prints an error to stderr and exits.
exitWithErrorMessage :: String -> IO a
exitWithErrorMessage msg = hPutStrLn stderr msg >> exitFailure

-- | Monad transformer adding error-message failure.
type ErrorT m = ExceptT String m

-- | Fails with an error message.
throwErrorT :: Monad m => String -> ErrorT m a
throwErrorT msg = throwError msg

-- | Runs an 'ErrorT' computation.
runErrorT :: Monad m => ErrorT m a -> m (Either String a)
runErrorT = runExceptT

-- | Runs an 'ErrorT' in 'IO', exiting on failure.
ioErrorT :: ErrorT IO a -> IO a
ioErrorT m = do
    e <- runExceptT m
    ioErrorM e
