{-|
Core syntax. Note that this is only used as executable code for the evaluator,
and not during conversion checking or scope checking. Accordingly, the
constructors are optimized for evaluation.
-}

module Syntax where

import Common
import LvlSet

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl
  | MetaVar Meta
  | Let (Named Ty) Tm Tm
  | AppI Tm Tm
  | AppE Tm Tm
  | Lam (Named Icit) Tm
  | Pi (Named Icit) Ty Ty
  | Fun Tm Tm
  | Irrelevant
  | U
  deriving Show

app :: Icit -> Tm -> Tm -> Tm
app Impl = AppI
app Expl = AppE
{-# inline app #-}

isInlinable :: Tm -> Bool
isInlinable t = go t where
  go LocalVar{} = True
  go MetaVar{}  = True
  go TopVar{}   = True
  go (Lam _ t)  = go t
  go U          = True
  go _          = False

-- | Return the set of free local variables as de Bruijn *levels*.
freeLocalVars :: Lvl -> Tm -> LvlSet
freeLocalVars = go where
  go l = \case
    LocalVar x -> singleton (l - x - 1)
    TopVar{}   -> mempty
    MetaVar{}  -> mempty
    Let _ t u  -> go l t <> delete l (go (l + 1) u)
    AppI t u   -> go l t <> go l u
    AppE t u   -> go l t <> go l u
    Lam _ t    -> delete l (go (l + 1) t)
    Pi _ a b   -> go l a <> delete l (go (l + 1) b)
    Fun a b    -> go l a <> go l b
    Irrelevant -> mempty
    U          -> mempty
