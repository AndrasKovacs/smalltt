
module Syntax where

import Common

data Spanned a = Spanned {-# unpack #-} Span a

data Val

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl
  | MetaVar MetaVar
  | Let (Spanned Ty) Tm Tm
  | AppI Tm Tm
  | AppE Tm Tm
  | Lam (Spanned Icit) Tm
  | Pi (Spanned Icit) Ty Ty
  | Fun Tm Tm
  | Irrelevant
  | U
--  deriving Show
