
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

  (ms, len, top) <- checkProg src top

  putStrLn (replicate 80 '-')
  ADL.forIx ms \i e -> case e of
    MEUnsolved -> putStrLn $ show i ++ "?"
    MESolved v -> putStrLn $ show i ++ "? = " ++ showTm0 src len top (quote0 ms UnfoldNone v)

  let goTop (pred -> len) = \case
        Nil -> pure ()
        Definition x a t top -> do
          goTop len top
          putStrLn ""
          putStrLn $ showSpan src x ++ " : " ++ showTm0 src len top a
          putStrLn $ "  = " ++ showTm0 src len top t
  goTop len top

t1 = test $ packUTF8 $ unlines [

  "Nat  : U   = (N : U) → (N → N) → N → N",
  "zero : Nat = λ N s z. z",
  "foo  = zero"
  -- "suc  : Nat → Nat = λ n N s z. s (n N s z)",
  -- "add  : Nat → Nat → Nat = λ a b N s z. a N s (b N s z)",
  -- "mul  : Nat → Nat → Nat = λ a b N s. a N (b N s)",
  -- "n5   : Nat = λ N s z. s (s (s (s (s z))))",
  -- "n2 : Nat = λ N s z. s (s z)",
  -- "n4       = add n2 n2"
  -- "n10b  = mul n5 n2"
  -- "n100  = mul n10 n10",
  -- "n100b = mul n10b n10b"
  ]
