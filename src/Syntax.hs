
module Syntax where

import Prelude hiding (lookup)
import Data.List hiding (lookup)

import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.IntMap.Strict (IntMap)
import qualified Data.HashSet as HS

import Presyntax

--------------------------------------------------------------------------------

type Meta   = Int
type Gen    = Int
type Ty     = Val
type Sub a  = [(Name, a)]
type Vals   = Sub (Maybe Val)        -- Nothing: bound, Just: defined
type Tys    = Sub (Either Ty Ty)     -- Left: bound, Right: defined
type Metas  = IntMap Val
type Ren    = HashMap (Either Name Gen) Name
type Spine  = Sub (Val, Icit)

data MetaInsertion
  = MIYes
  | MINo
  | MIUntilName Name
  deriving (Show)

data Tm
  = Var Name
  | Gen Gen
  | Let Name Tm Tm Tm
  | App Tm Tm Name Icit
  | Lam Name Icit Tm
  | Pi Name Icit Tm Tm
  | U
  | Meta Meta

data Head
  = Metaʰ Meta
  | Varʰ Name
  | Genʰ Gen

data Val
  = Neu Head Spine
  | Lamᵛ Name Icit (Val → Val)
  | Piᵛ Name Icit Val (Val → Val)
  | Uᵛ

--------------------------------------------------------------------------------

lookup ∷ String → Name → Sub a → a
lookup msg x ((x', a):as) = if x == x' then a else lookup msg x as
lookup msg x _            = error msg

lams ∷ Spine → Tm → Tm
lams sp t = foldl' (\t (x, (u, i)) → Lam x i t) t sp

genᵛ ∷ Gen → Val
genᵛ g = Neu (Genʰ g) []

varᵛ ∷ Name → Val
varᵛ x = Neu (Varʰ x) []

metaᵛ ∷ Meta → Val
metaᵛ m = Neu (Metaʰ m) []

hashNub ∷ (Eq a, Hashable a) => [a] → [a]
hashNub = snd . foldr go (HS.empty, []) where
  go a (!seen, !as) | HS.member a seen = (seen, as)
  go a (seen, as) = (HS.insert a seen, a:as)

splitSpine ∷ Tm → (Tm, Sub (Tm, Icit))
splitSpine = \case
  App f a x i → ((x, (a, i)):) <$> splitSpine f
  t           → (t, [])

-- Printing
--------------------------------------------------------------------------------

freeInTm :: Name → Tm → Bool
freeInTm x = \case
  Var x'         → x == x'
  App f a _ i    → freeInTm x f || freeInTm x a
  Lam x' i t     → if x == x' then False else freeInTm x t
  Pi x' i a b    → freeInTm x a || if x == x' then False else freeInTm x b
  Let x' a t u   → freeInTm x a || freeInTm x t || if x == x' then False else freeInTm x u
  Gen _          → error "freeInTm: impossible Gen"
  Meta _         → False
  U              → False

prettyTm :: Int → Tm → ShowS
prettyTm prec = go (prec /= 0) where

  unwords' :: [ShowS] → ShowS
  unwords' = foldr1 (\x acc → x . (' ':) . acc)

  lams :: (Name, Icit) → Tm → ([(Name, Icit)], Tm)
  lams xi t = go [xi] t where
    go xs (Lam x i t) = go ((x,i):xs) t
    go xs t           = (xs, t)

  bracket :: ShowS → ShowS
  bracket s = ('{':).s.('}':)

  icit :: Icit → a → a → a
  icit Impl i e = i
  icit Expl i e = e

  -- TODO: printing is kinda slow (make tmSpine return in reverse, optimize App case)
  go :: Bool → Tm → ShowS
  go p = \case
    Var x → (x++)
    t@App{} → let (h, sp) = splitSpine t
      in showParen p $
         unwords' $
         go True h :
         reverse (map (\(_, (t, i)) → icit i (bracket (go False t)) (go True t)) sp)

    Lam x i t → case lams (x, i) t of
      (xis, t) → showParen p (("λ "++) . params . (". "++) . go False t)
        where params = unwords' $ reverse $ map (\(x, i) → icit i bracket id (x++)) xis

    Pi x i a b → showParen p (arg . (" → "++) . go False b)
      where
        arg = if freeInTm x b
                then (icit i bracket (showParen True)) ((x++) . (" : "++) . go False a)
                else go True a

    Let x a t u →
      ("let "++).(x++) . (" : "++) . go False a . ("\n"++) .
      ("   "++) . (" = "++) . go False t  . ("\nin\n"++) .
      go False u
    U      → ('*':)
    Meta m → (("?"++).(show m++))
    Gen g  → showParen p (("gen " ++ show g)++)

instance Show Tm where showsPrec = prettyTm
