module Main where
import GHC
import Control.Monad.IO.Class (liftIO)
import GHC.Platform (platformArchOS)
import GHC.Driver.Session (defaultFatalMessager, defaultFlushOut)
import System.Environment (getArgs)

-- Compile a Haskell file with GHC's own API, running inside JavaScript.
-- argv: <libdir> [source.hs]
main :: IO ()
main = do
  args <- getArgs
  case args of
    (libdir : rest) -> defaultErrorHandler defaultFatalMessager defaultFlushOut $
      runGhc (Just libdir) $ do
        df <- getSessionDynFlags
        _ <- setSessionDynFlags df
        liftIO (putStrLn ("target platform: " ++ show (platformArchOS (targetPlatform df))))
        case rest of
          [] -> liftIO (putStrLn "no source given; session started cleanly")
          (src : _) -> do
            t <- guessTarget src Nothing Nothing
            setTargets [t]
            ok <- load LoadAllTargets
            liftIO (putStrLn ("load: " ++ (case ok of Succeeded -> "succeeded"; Failed -> "failed")))
    _ -> putStrLn "usage: driver <libdir> [source.hs]"
