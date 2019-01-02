{-|
Core syntax. Note that this is only used as executable code for the evaluator,
and not during conversion checking or scope checking. Accordingly, the
constructors are optimized for evaluation.
-}

module Syntax where

import Common

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl
  | MetaVar Meta
  | RuleVar Lvl
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
