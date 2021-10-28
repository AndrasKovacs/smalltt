
module Test where

import qualified Data.ByteString as B
import System.Exit

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Array.LM as ALM

import Common
import CoreTypes
import Elaboration
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

  (tbl, top, ms) <- checkProg src top >>= \case
    Left e  -> putStrLn (showException src e) >> exitSuccess
    Right x -> pure x

  putStrLn ""
  putStrLn (replicate 80 '-')
  putStrLn ""
  ADL.forIx ms \i e -> case e of
    MEUnsolved     -> putStrLn $ '?':show i ++ " unsolved"
    MESolved _ t _ -> putStrLn $ '?':show i ++ " = " ++ showTm0 src top t

  ALM.for (topDefs top) \(TopEntry x a t) -> do
    putStrLn ""
    putStrLn $ showSpan src x ++ " : " ++ showTm0 src top a
    putStrLn $ "  = " ++ showTm0 src top t

t2 = test $ packUTF8 $ unlines [
  "id : {A:U} → A → A = λ x. x",
  "idTest : {A:U} → A → A = id id id id id id id id"
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

--------------------------------------------------------------------------------

testsrc :: Int -> String
testsrc n = let x = show n in
  unlines [
  "id"++x++" : {A} → A → A",
  " = λ x. x",
  "",
  "id"++x++"Test : {A} → A → A",
  "  = id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++"",
  "    id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++" id"++x++"",
  "",
  "Nat"++x++" : U",
  " = (n : U) → (n → n) → n → n",
  "",
  "zero"++x++" : Nat"++x++"",
  " = λ n s z. z",
  "",
  "suc"++x++" : Nat"++x++" → Nat"++x++"",
  " = λ a n s z. s (a n s z)",
  "",
  "add"++x++" : Nat"++x++" → Nat"++x++" → Nat"++x++"",
  " = λ a b n s z. a n s (b n s z)",
  "",
  "mul"++x++" : Nat"++x++" → Nat"++x++" → Nat"++x++"",
  " = λ a b n s. a n (b n s)",
  "",
  "Eq"++x++" : {A} → A → A → U",
  " = λ {A} x y. (P : A → U) → P x → P y",
  "",
  "refl"++x++" : {A}{x : A} → Eq"++x++" x x",
  " = λ P px. px",
  "",
  "two"++x++"   : Nat"++x++" = λ N s z. s (s z)",
  "five"++x++"  : Nat"++x++" = λ N s z. s (s (s (s (s z))))",
  "n10"++x++"    = mul"++x++" two"++x++"  five"++x++"",
  "n10b"++x++"   = mul"++x++" five"++x++" two"++x++"",
  "n20"++x++"    = mul"++x++" two"++x++"  n10"++x++"",
  "n20b"++x++"   = mul"++x++" two"++x++"  n10b"++x++"",
  "n21"++x++"    = suc"++x++" n20"++x++"",
  "n21b"++x++"   = suc"++x++" n20b"++x++"",
  "n22"++x++"    = suc"++x++" n21"++x++"",
  "n22b"++x++"   = suc"++x++" n21b"++x++"",
  "n100"++x++"   = mul"++x++" n10"++x++"   n10"++x++"",
  "n100b"++x++"  = mul"++x++" n10b"++x++"  n10b"++x++"",
  "n10k"++x++"   = mul"++x++" n100"++x++"  n100"++x++"",
  "n10kb"++x++"  = mul"++x++" n100b"++x++" n100b"++x++"",
  "n100k"++x++"  = mul"++x++" n10k"++x++"  n10"++x++"",
  "n100kb"++x++" = mul"++x++" n10kb"++x++" n10b"++x++"",
  "n1M"++x++"    = mul"++x++" n10k"++x++"  n100"++x++"",
  "n1Mb"++x++"   = mul"++x++" n10kb"++x++" n100b"++x++"",
  "n5M"++x++"    = mul"++x++" n1M"++x++"   five"++x++"",
  "n5Mb"++x++"   = mul"++x++" n1Mb"++x++"  five"++x++"",
  "n10M"++x++"   = mul"++x++" n5M"++x++"   two"++x++"",
  "n10Mb"++x++"  = mul"++x++" n5Mb"++x++"  two"++x++"",
  "",
  "--------------------------------------------------------------------------------",
  "",
  "Vec"++x++" : U → Nat"++x++" → U",
  " = λ a n. (V : Nat"++x++" → U) → V zero"++x++" → ({n} → a → V n → V (suc"++x++" n)) → V n",
  "",
  "vnil"++x++" : {a} → Vec"++x++" a zero"++x++"",
  " = λ V n c. n",
  "",
  "vcons"++x++" : {a n} → a → Vec"++x++" a n → Vec"++x++" a (suc"++x++" n)",
  " = λ a as V n c. c a (as V n c)",
  "",
  "vec1"++x++" = (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++"",
  "       (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++"",
  "       (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++"",
  "       (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++"",
  "       (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++"",
  "       (vcons"++x++" zero"++x++" (vcons"++x++" zero"++x++" vnil"++x++"))))))))))))))))))))))))))))))))",
  "",
  "Pair"++x++" : U → U → U",
  " = λ A B. (Pair"++x++" : U)(pair : A → B → Pair"++x++") → Pair"++x++"",
  "",
  "pair"++x++" : {A B} → A → B → Pair"++x++" A B",
  " = λ a b Pair"++x++" pair. pair a b",
  "",
  "proj1"++x++" : {A B} → Pair"++x++" A B → A",
  " = λ p. p _ (λ x y. x)",
  "",
  "proj2"++x++" : {A B} → Pair"++x++" A B → B",
  " = λ p. p _ (λ x y. y)",
  "",
  "Top"++x++" : U",
  " = (Top : U)(tt : Top) → Top",
  "",
  "tt"++x++" : Top"++x++"",
  " = λ Top tt. tt",
  "",
  "Bot"++x++" : U",
  " = (Bot : U) → Bot",
  "",
  "Ty"++x++" : U",
  " = (Ty  : U)",
  "   (ι   : Ty)",
  "   (fun : Ty → Ty → Ty)",
  " → Ty",
  "",
  "ι"++x++" : Ty"++x++"",
  " = λ _ ι _. ι",
  "",
  "fun"++x++" : Ty"++x++" → Ty"++x++" → Ty"++x++"",
  " = λ A B Ty ι fun. fun (A Ty ι fun) (B Ty ι fun)",
  "",
  "Con"++x++" : U",
  " = (Con : U)",
  "   (nil  : Con)",
  "   (cons : Con → Ty"++x++" → Con)",
  " → Con",
  "",
  "nil"++x++" : Con"++x++"",
  " = λ Con nil cons. nil",
  "",
  "cons"++x++" : Con"++x++" → Ty"++x++" → Con"++x++"",
  " = λ Γ A Con nil cons. cons (Γ Con nil cons) A",
  "",
  "Var"++x++" : Con"++x++" → Ty"++x++" → U",
  " = λ Γ A.",
  "   (Var : Con"++x++" → Ty"++x++" → U)",
  "   (vz  : {Γ A} → Var (cons"++x++" Γ A) A)",
  "   (vs  : {Γ B A} → Var Γ A → Var (cons"++x++" Γ B) A)",
  " → Var Γ A",
  "",
  "vz"++x++" : {Γ A} → Var"++x++" (cons"++x++" Γ A) A",
  " = λ Var vz vs. vz",
  "",
  "vs"++x++" : {Γ B A} → Var"++x++" Γ A → Var"++x++" (cons"++x++" Γ B) A",
  " = λ x Var vz vs. vs (x Var vz vs)",
  "",
  "Tm"++x++" : Con"++x++" → Ty"++x++" → U",
  " = λ Γ A.",
  "   (Tm  : Con"++x++" → Ty"++x++" → U)",
  "   (var : {Γ A} → Var"++x++" Γ A → Tm Γ A)",
  "   (lam : {Γ A B} → Tm (cons"++x++" Γ A) B → Tm Γ (fun"++x++" A B))",
  "   (app : {Γ A B} → Tm Γ (fun"++x++" A B) → Tm Γ A → Tm Γ B)",
  " → Tm Γ A",
  "",
  "var"++x++" : {Γ A} → Var"++x++" Γ A → Tm"++x++" Γ A",
  " = λ x Tm var lam app. var x",
  "",
  "lam"++x++" : {Γ A B} → Tm"++x++" (cons"++x++" Γ A) B → Tm"++x++" Γ (fun"++x++" A B)",
  " = λ t Tm var lam app. lam (t Tm var lam app)",
  "",
  "app"++x++" : {Γ A B} → Tm"++x++" Γ (fun"++x++" A B) → Tm"++x++" Γ A → Tm"++x++" Γ B",
  " = λ t u Tm var lam app. app (t Tm var lam app) (u Tm var lam app)",
  "",
  "EvalTy"++x++" : Ty"++x++" → U",
  " = λ A. A _ Bot"++x++" (λ A B. A → B)",
  "",
  "EvalCon"++x++" : Con"++x++" → U",
  " = λ Γ. Γ _ Top"++x++" (λ Δ A. Pair"++x++" Δ (EvalTy"++x++" A))",
  "",
  "EvalVar"++x++" : {Γ A} → Var"++x++" Γ A → EvalCon"++x++" Γ → EvalTy"++x++" A",
  " = λ x. x (λ Γ A. EvalCon"++x++" Γ → EvalTy"++x++" A)",
  "          (λ env. proj2"++x++" env)",
  "          (λ rec env. rec (proj1"++x++" env))",
  "",
  "EvalTm"++x++" : {Γ A} → Tm"++x++" Γ A → EvalCon"++x++" Γ → EvalTy"++x++" A",
  " = λ t. t _",
  "          EvalVar"++x++"",
  "          (λ t env α. t (pair"++x++" env α))",
  "          (λ t u env. t env (u env))",
  "",
  "test"++x++" : Tm"++x++" nil"++x++" (fun"++x++" (fun"++x++" ι"++x++" ι"++x++") (fun"++x++" ι"++x++" ι"++x++"))",
  "  = lam"++x++" (lam"++x++" (app"++x++" (var"++x++" (vs"++x++" vz"++x++")) (app"++x++" (var"++x++" (vs"++x++" vz"++x++"))",
  "             (app"++x++" (var"++x++" (vs"++x++" vz"++x++")) (app"++x++" (var"++x++" (vs"++x++" vz"++x++"))",
  "             (app"++x++" (var"++x++" (vs"++x++" vz"++x++")) (app"++x++" (var"++x++" (vs"++x++" vz"++x++")) (var"++x++" vz"++x++"))))))))"

  ]

manysrc :: Int -> String
manysrc n = unlines [testsrc x | x <- [0..n]]

srctofile :: Int -> IO ()
srctofile n = writeFile "test3.stt" $ manysrc n
