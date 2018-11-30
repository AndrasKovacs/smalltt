{-# options_ghc -Wno-unused-imports #-}

{-|
TODO

- short term
  - more tests
  - CLI
  - print elab output for demonstration
  - minor fixes
  - error messages (more principled, display line cursors on error, etc.)
  - benchmarks
  - speed: known call insertion, Box in eval

- medium term
  - Reader monads, refactors, logging/debug infrastructure
  - elab optimization passes (let-motion, environment trimming,
    convert metas to vars, array chunks in local environments)
  - serialization
     - compact regions?
  - pruning, intersections
  - modules
     - elab with linearization
     - relocation tables for modules?
  - equality reflection
     - beta rewrites: like in Agda, but match lhs by unification
     - undirected reflection: don't reduce, match only during stuck conversion
       checking

-}

module Test where

{-| Quick and dirty feature test -}

import qualified Data.Text as T
import Text.Megaparsec.Error

import Common
import Elaboration
import Evaluation
import Parser
import Syntax
import Values
import Pretty

t = T.unlines [
  "id  : {A} → A → A = λ x. x",
  "id2 : {A} → A → A = id (id!)",
  "id3 : {A} → A → A = λ x. id x",
  "the : (A : _) → A → A = λ _ x. x",

  "constTy = {A B} → A → B → A",

  "const : constTy = λ x y. x",

  "constU = const {U} !",

  "namedArgTest  = const {B = U} U",
  "namedArgTest2 = the constTy (λ x y. x) {B = U} U",

  "Bool = (B : U) → B → B → B",
  "true  : Bool = λ _ t f. t",
  "false : Bool = λ _ t f . f",

  "Nat  : U = (n : U) → (n → n) → n → n",
  "zero : Nat = λ n s z. z",
  "suc  : Nat → Nat = λ a n s z. s (a n s z)",

  "n2 : Nat = λ n s z. s (s z)",
  "n5 : Nat = λ n s z. s (s (s (s (s z))))",
  "mul : Nat → Nat → Nat = λ a b n s z. a n (b n s) z",
  "n10 = mul n2 n5",
  "n100 = mul n10 n10",
  "n10k = mul n100 n100",
  "n10kb = mul n100 (mul n10 n10)",
  "n1M = mul n10k n100",

  "List : U → U = λ a. (l : U) → (a → l → l) → l → l",
  "nil  : {a} → List a = λ l c n. n",
  "cons : {a} → a → List a → List a = λ a as l c n. c a (as l c n)",

  "list1 = cons true (cons false (cons false nil))",

  "map : {a b} → (a → b) → List a → List b",
  " = λ f as l c. as l (λ a. c (f a))",

  "Vec : U → Nat → U",
  " = λ a n. (V : Nat → U) → V zero → ({n} → a → V n → V (suc n)) → V n",

  "vnil : {a} → Vec a zero",
  " = λ V n c. n",

  "vcons : {a n} → a → Vec a n → Vec a (suc n)",
  " = λ a as V n c. c a (as V n c)",

  "vec1 = vcons true (vcons false (vcons true vnil))",

  "Eq : {A} → A → A → U",
  " = λ {A} x y. (P : A → U) → P x → P y",

  "refl : {A}{x : A} → Eq x x",
  " = λ P px. px",

  "trans : {A}{x y z : A} → Eq x y → Eq y z → Eq x z",
  " = λ {x = x} p q. q _ p",

  "sym : {A}{x y : A} → Eq x y → Eq y x",
  " = λ {x = x}{y} p. p (λ y. Eq y x) refl",

  "ap : {A B}(f : A → B){x y : A} → Eq x y → Eq (f x) (f y)",
  " = λ f {x}{y} p. p (λ y. Eq (f x) (f y)) refl",

  "comp :",
  "  {A}",
  "  {B : A → U}",
  "  {C : {a} → B a → U}",
  "  (f : {a}(b : B a) → C b)",
  "  (g : (a : A) → B a)",
  "  (x : A)",
  "  → C (g x)",
  " = λ f g a. f (g a)",

  "compTest1 : Nat → Nat = comp suc suc",

  "compTest2 : {m A} → A → Vec A m → Vec A (suc (suc m))",
  " = λ a. comp (vcons a) (vcons a)",

  "nfun : Nat → U",
  " = λ n. n U (λ A. U → A) U",

  "localtest1 : nfun n10k → nfun n10k = λ x. x"

  ]

test :: IO ()
test = either (putStrLn . errorBundlePretty)
              (\t -> checkProgram t)
              (parseFile "" t)
