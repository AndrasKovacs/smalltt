
module Syntax where

import Common

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Ix
  | MetaVar MetaIx
  | Let Name Ty Tm Tm
  | App Tm Tm Icit
  | Lam NameIcit Tm
  | Pi NameIcit Ty Tm
  | Irrelevant
  | U
