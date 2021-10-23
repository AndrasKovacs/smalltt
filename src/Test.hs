
module Test where

import qualified Data.ByteString as B
import FlatParse.Stateful (packUTF8)
import System.Exit

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Array.LM as ALM

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

  putStrLn ""
  putStrLn (replicate 80 '-')
  putStrLn ""
  ADL.forIx ms \i e -> case e of
    MEUnsolved -> putStrLn $ '?':show i ++ " unsolved"
    MESolved v -> putStrLn $ '?':show i ++ " = " ++ showTm0 src top (quote0 ms UnfoldNone v)

  ALM.for (topDefs top) \(TopEntry x a t) -> do
    putStrLn ""
    putStrLn $ showSpan src x ++ " : " ++ showTm0 src top a
    putStrLn $ "  = " ++ showTm0 src top t

t2 = test $ packUTF8 $ unlines [
  "Nat  : U   = (N : U) → (N → N) → N → N",
  "zero : Nat = λ N s z. z",
  "suc  : Nat → Nat = λ n N s z. s (n N s z)",
  "add  : Nat → Nat → Nat = λ a b N s z. a N s (b N s z)",
  "foo = λ x. add (suc (suc x)) (suc zero)",
  "the  : (A : U) → A → A = λ A x. x",
  "Eq   : {A} → A → A → U = λ {A} x y. (P : A → U) → P x → P y",
  "refl : {A x} → Eq {A} x x = λ P px. px",
  "p1   = λ (A : U) (B : U). refl {x = A}"
  ]

t1 = test $ packUTF8 $ unlines [
  "Nat  : U   = (N : U)(s : N → N)(z : N) → N",
  "zero : Nat = λ N s z. z",
  "suc  : Nat → Nat = λ n N s z. s (n N s z)",
  "add  : Nat → Nat → Nat = λ a b N s z. a N s (b N s z)",
  "mul  : Nat → Nat → Nat = λ a b N s. a N (b N s)",
  "n5   : Nat = λ N s z. s (s (s (s (s z))))",
  "n2   : Nat = λ N s z. s (s z)",
  "n10   = add n5 n5",
  "n10b  = mul n5 n2",
  "n100  = mul n10 n10",
  "n100b = mul n10b n10b"
  ]
