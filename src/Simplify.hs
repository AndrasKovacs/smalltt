
module Simplify where

import Common
import Values
import Syntax
import ElabState
import Evaluation

zonkSp :: Lvl -> VEnv -> Tm -> Either Val Tm
zonkSp l vs = go where
  go (MetaVar x) = case lookupMeta x of
    MESolved _ True t _ -> Left (vEval ENil t)
    _                   -> Right (MetaVar x)
  go (AppI t u)  = either (\v -> Left (vAppI v (vEval vs u)))
                          (\t -> Right (AppI t (zonk l vs u)))
                          (go t)
  go (AppE t u)  = either (\v -> Left (vAppE v (vEval vs u)))
                          (\t -> Right (AppE t (zonk l vs u)))
                          (go t)
  go t           = Right (zonk l vs t)

zonk :: Lvl -> VEnv -> Tm -> Tm
zonk l vs = \case
  LocalVar x -> LocalVar x
  TopVar x   -> TopVar x
  MetaVar x  -> case lookupMeta x of
    MESolved _ True t _ -> vQuote l (vEval ENil t)
    _                   -> MetaVar x
  Let (Named x a) t u -> Let (Named x (zonk l vs a)) (zonk l vs t) (zonk (l + 1) (ESkip vs) u)
  AppI t u   -> either (\v -> vQuote l (vAppI v (vEval vs u)))
                       (\t -> AppI t (zonk l vs u))
                       (zonkSp l vs t)
  AppE t u   -> either (\v -> vQuote l (vAppE v (vEval vs u)))
                       (\t -> AppE t (zonk l vs u))
                       (zonkSp l vs t)
  Lam ni t   -> Lam ni (zonk (l + 1) (ESkip vs) t)
  Fun a b    -> Fun (zonk l vs a) (zonk l vs b)
  Pi ni a b  -> Pi ni (zonk l vs a) (zonk (l + 1) (ESkip vs) b)
  U          -> U
  Irrelevant -> Irrelevant
