-- GHC's driver, compiled to JavaScript.
--
-- This is the whole compiler front end: everything below is GHC's own API,
-- and the compiler this links into is GHC's compiler library built for the
-- JavaScript target. Output is byte-identical to a native cross compiler's.
--
--   node ghc.cjs <libdir> [ghc flags] Source.hs ...
module Main where

import Control.Monad.IO.Class (liftIO)
import GHC
import GHC.Driver.Phases (StopPhase (NoStop))
import GHC.Driver.Pipeline (oneShot)
import GHC.Driver.Session (defaultFatalMessager, defaultFlushOut, parseDynamicFlagsCmdLine)
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  argv <- getArgs
  case argv of
    [] -> putStrLn "usage: driver <libdir> [ghc flags] Source.hs"
    (libdir : rest) -> defaultErrorHandler defaultFatalMessager defaultFlushOut $
      runGhc (Just libdir) $ do
        df0 <- getSessionDynFlags
        -- `-c` is a *mode*, not a dynamic flag: GHC's own driver reads it
        -- before this point, so it has to come out of the argument list here
        -- or the flag parser hands it back as if it were a source file.
        let oneshot = "-c" `elem` rest
            flags = filter (/= "-c") rest
        (df1, leftover, _warns) <- parseDynamicFlagsCmdLine df0 (map (mkGeneralLocated "flag") flags)
        _ <- setSessionDynFlags df1
        let files = map unLoc leftover
        if oneshot
          then do
            env <- getSession
            liftIO (oneShot env NoStop [(f, Nothing) | f <- files])
          else do
            targets <- mapM (\f -> guessTarget f Nothing Nothing) files
            setTargets targets
            ok <- load LoadAllTargets
            case ok of
              Succeeded -> liftIO (putStrLn "compilation succeeded")
              Failed -> liftIO (putStrLn "compilation failed" >> exitFailure)
