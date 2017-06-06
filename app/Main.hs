module Main where

import System.Environment
import System.Exit
import Control.Monad
import Language.IceT.VCGen

main :: IO ()
main = do args <- getArgs
          case args of
            []  -> do progstr <- getContents
                      verifyProgram progstr >>= exit
            [f] -> verifyFile f >>= exit
            _   -> exitFailure
  where exit True = do putStrLn "✓ SAFE"
                       exitSuccess
        exit _    = do putStrLn "✗ UNSAFE"
                       exitFailure
