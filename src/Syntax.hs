
module Syntax where

import Common

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Ix
  | Let Name Ty Tm Tm
  | App Tm Tm Icit
  | Lam {-# unpack #-} (T2 Name Icit) Tm
  | Pi {-# unpack #-} (T2 Name Icit) Ty Tm
  | Irrelevant
  | U
