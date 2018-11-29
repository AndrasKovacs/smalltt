{-|

Preliminary pretty printing, to be replaced by more sophisticated solutions.

-}

module Pretty (
    prettyTm
  , showTm
  , showTm0
  ) where

import qualified Data.Array.Dynamic as A
import qualified Data.Text.Short as T
import ElabState
import Syntax
import Common

showTm0 :: Tm -> String
showTm0 = showTm NENil

showTm :: NameEnv -> Tm -> String
showTm ns t = prettyTm 0 ns t ""

prettyTm :: Int -> NameEnv -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  go :: Bool -> NameEnv -> Tm -> ShowS
  go p ns = \case
    LocalVar x -> ((T.unpack $ lookupNameEnv ns x)++)
    TopVar x -> runIO $ do {T2 _ n <- _entryName <$> A.read top x; pure (T.unpack n++)}
    MetaVar (MetaIx i j) -> (("?"++).(show i++)).('.':).(show j++)
    Let x a t u ->
      ("let "++) . (T.unpack x++) . (" : "++) . go False ns a . ("\n    = "++)
      . go False ns t  . ("\nin\n"++) . go False (NESnoc ns x) u
    App (App t u i) u' i' ->
      showParen p (go False ns t . (' ':) . goArg ns u i . (' ':) . goArg ns u' i')

    App t u i      -> showParen p (go True ns t . (' ':) . goArg ns u i)
    Lam (NI x i) t -> showParen p (("λ "++) . goLamBind x i . goLam (NESnoc ns x) t)
    t@Pi{}         -> showParen p (goPi False ns t)
    U              -> ("U"++)
    Irrelevant     -> ("Irr"++)

  goArg :: NameEnv -> Tm -> Icit -> ShowS
  goArg ns t i = icit i (bracket (go False ns t)) (go True ns t)

  bracket :: ShowS -> ShowS
  bracket s = ('{':).s.('}':)

  goPiBind :: Name -> Icit -> NameEnv -> Tm -> ShowS
  goPiBind x i ns a =
    icit i bracket (showParen True) ((T.unpack x++) . (" : "++) . go False ns a)

  goPi :: Bool -> NameEnv -> Tm -> ShowS
  goPi p ns (Pi (NI x i) a b)
    | i == Impl || x /= "" = goPiBind x i ns a . goPi True (NESnoc ns x) b
    | otherwise =
       (if p then (" -> "++) else id) .
       go (case a of App{} -> False; _ -> True) ns a .
       (" -> "++) . go False ns b
  goPi p ns t = (if p then (" -> "++) else id) . go False ns t

  goLamBind :: Name -> Icit -> ShowS
  goLamBind x i = icit i bracket id (T.unpack x++)

  goLam :: NameEnv -> Tm -> ShowS
  goLam ns (Lam (NI x i) t) = (' ':) . goLamBind x i . goLam (NESnoc ns x) t
  goLam ns t                = (". "++) . go False ns t
