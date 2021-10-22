{-# LANGUAGE TupleSections #-}
module Main where

-- import Control.Exception
-- import System.Environment
-- import System.Exit

-- import CoreTypes
-- import Common
-- import Cxt
-- import Exceptions
-- import Evaluation
-- import Parser
-- import Elaboration

-- import qualified Presyntax as P

import Test

--------------------------------------------------------------------------------

main :: IO ()
main = t2

-- helpMsg = unlines [
--   "usage: elabzoo-first-class-poly [--help|nf|type]",
--   "  --help : display this message",
--   "  elab   : read & elaborate expression from stdin",
--   "  nf     : read & typecheck expression from stdin, print its normal form and type",
--   "  type   : read & typecheck expression from stdin, print its type"]

-- mainWith :: IO [String] -> IO (P.Tm, String) -> IO ()
-- mainWith getOpt getRaw = do

--   let elab = do
--         _
--         -- (t, file) <- getRaw
--         -- res <- (infer (emptyCxt (initialPos file)) t <* checkEverything)
--         --        `catch` \e -> displayError file e >> exitSuccess
--         -- putStrLn ("\n" ++ replicate 80 '-' ++ "\n")
--         -- pure res

--   getOpt >>= \case
--     ["--help"] -> putStrLn helpMsg
--     ["nf"]   -> do
--       (t, a) <- elab
--       putStrLn $ showTm0 $ nf [] t
--       putStrLn "  :"
--       putStrLn $ showTm0 $ quote 0 a
--     ["type"] -> do
--       (t, a) <- elab
--       putStrLn $ showTm0 $ quote 0 a
--     ["elab"] -> do
--       (t, a) <- elab
--       displayMetas
--       putStrLn $ showTm0 t
--     _ -> putStrLn helpMsg

-- main :: IO ()
-- main = mainWith getArgs parseStdin

-- -- | Run main with inputs as function arguments.
-- main' :: String -> String -> IO ()
-- main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
