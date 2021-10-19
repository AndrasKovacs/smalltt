
module Test where

import qualified Data.ByteString as B
import FlatParse.Stateful (packUTF8)
import System.Exit

import qualified Data.Array.Dynamic.L as ADL

import Common
import CoreTypes
import Elaboration
import Evaluation
import Parser
import Lexer
import Exceptions
import MetaCxt

test :: B.ByteString -> IO ()
test src = standardize do
  top <- case parse src of
    OK top _ _ -> pure top
    Fail       -> putStrLn "parse error" >> exitSuccess
    Err e      -> putStrLn (prettyError src e) >> exitSuccess

  -- print top

  (ms, top) <- checkProg src top

  putStrLn (replicate 80 '-')
  ADL.forIx ms \i e -> case e of
    MEUnsolved -> putStrLn $ show i ++ "?"
    MESolved v -> putStrLn $ show i ++ "? = " ++ showTm0 src top (quote0 ms UnfoldNone v)

  let goTop = \case
        Nil -> pure ()
        Definition x a t top -> do
          goTop top
          putStrLn ""
          putStrLn $ showSpan src x ++ " : " ++ showTm0 src top a
          putStrLn $ "  = " ++ showTm0 src top t
  goTop top

t1 = test $ packUTF8 $ unlines [

  -- "Nat = (N : U) → (N → N) → N → N",
  "zero = λ N s z. z"
  -- "suc : Nat → Nat = λ n N s z. s (n N s z)"
  ]
