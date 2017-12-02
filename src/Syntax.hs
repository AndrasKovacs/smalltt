
module Syntax where

import Data.List
import Data.Maybe
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Presyntax

--------------------------------------------------------------------------------

type Meta  = Int
type Ty    = Val
type Spine = [(Val, Icit)]
type Var   = (Name, Int)

data Tm
  = Var {-# unpack #-} Var
  | Let Name Tm Tm Tm
  | App Tm Tm Icit
  | Lam Name Icit Tm
  | Pi Name Icit Tm Tm
  | U
  | Meta Meta

data Head
  = Metaʰ Meta
  | Varʰ {-# unpack #-} Var

data Val
  = Neu Head Spine
  | Lamᵛ Name Icit (Val → Val)
  | Piᵛ Name Icit Val (Val → Val)
  | Uᵛ

-- Printing
--------------------------------------------------------------------------------

-- | Eliminate name shadowing, mark non-dependent Pi binders as such.
--   TODO: faster occurrence check.
elucidate ∷ Int → HashMap Name [Int] → Tm → Tm
elucidate = go where

  varOccurs ∷ Int → Tm → Bool
  varOccurs x = go where
    go = \case
      Var (_, x') → x == x'
      App f a _   → go f || go a
      Lam _ i t   → go t
      Pi _ _ a b  → go a || go b
      Let _ a t u → go a || go t || go u
      Meta _      → False
      U           → False

  renVar ∷ Name → Int → HashMap Name [Int] → Name
  renVar x i m | Just is ← HM.lookup x m,
                 j ← fromJust (elemIndex i is),
                 j /= 0 = x ++ "_" ++ show j
               | otherwise = x

  renBind ∷ Int → HashMap Name [Int] → Name → (HashMap Name [Int], Name)
  renBind i m x = case HM.lookup x m of
    Just is → (HM.insert x (is ++ [i]) m, x ++ "_" ++ show (length is))
    _       → (HM.insert x [i] m, x)

  go ∷ Int → HashMap String [Int] → Tm → Tm
  go g m = \case
    Var (x, i)  → Var (renVar x i m, i)
    Let x a t u →
      let (m', x') = renBind g m x in
      Let x' (go g m a) (go g m t) (go (g + 1) m' u)
    App t u i   → App (go g m t) (go g m u) i
    Lam x i t   →
      let (m', x') = renBind g m x in
      Lam x' i (go (g + 1) m' t)
    Pi x i a b | x /= "_" && varOccurs g b →
      let (m', x') = renBind g m x in
      Pi x' i (go g m a) (go (g + 1) m' b)
    Pi x i a b  → Pi "_" i (go g m a) (go (g + 1) m b)
    U           → U
    Meta i      → Meta i

-- | This only prints names (no indices) as they are.
--   Only works nicely on elucidated terms.
prettyTm ∷ Int → Tm → ShowS
prettyTm prec = go (prec /= 0) where

  bracket ∷ ShowS → ShowS
  bracket s = ('{':).s.('}':)

  goArg ∷ Tm → Icit → ShowS
  goArg t i = icit i (bracket (go False t)) (go True t)

  goPiBind ∷ Name → Icit → Tm → ShowS
  goPiBind x i a =
    icit i bracket (showParen True) ((x++) . (" : "++) . go False a)

  goLamBind ∷ Name → Icit  → ShowS
  goLamBind x i = icit i bracket id (x++)

  goLam ∷ Tm → ShowS
  goLam (Lam x i t) = (' ':) . goLamBind x i . goLam t
  goLam t           = (". "++) . go False t

  goPi ∷ Bool → Tm → ShowS
  goPi p (Pi x i a b)
    | i == Impl || x /= "_" = goPiBind x i a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} → False; _ → True) a .
       (" → "++) . go False b
  goPi p t = (if p then (" → "++) else id) . go False t

  go ∷ Bool → Tm → ShowS
  go p = \case
    Var (x, i) → (x++)

    App (App t u i) u' i' →
      showParen p (go False t . (' ':) . goArg u i . (' ':) . goArg u' i')

    App t u i  → showParen p (go True t . (' ':) . goArg u i)
    Lam x i t  → showParen p (("λ "++) . goLamBind x i . goLam t)
    Pi x i a b → showParen p (goPi False (Pi x i a b))

    Let x a t u →
      ("let "++) . (x++) . (" : "++) . go False a . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False  u

    U      → ('*':)
    Meta m → (("?"++).(show m++))

instance Show Tm where showsPrec = prettyTm

elucidate₀ ∷ Tm → Tm
elucidate₀ = elucidate 0 HM.empty

printTm₀ ∷ Tm → IO ()
printTm₀ t = putStrLn (prettyTm 0 (elucidate₀ t) [])
