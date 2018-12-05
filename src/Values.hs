
module Values where

import Common
import Syntax

data Spine a = SNil | SAppI (Spine a) ~a | SAppE (Spine a) ~a
data Env a = ENil | EDef (Env a) ~a | ESkip (Env a)

type GEnv   = Env Glued
type VEnv   = Env Val
type GSpine = Spine Glued
type VSpine = Spine Val
type VTy    = Val
type GTy    = Glued
type GVTy   = GV

data GV = GV ~Glued ~Val

data GCl = GCl GEnv VEnv Tm
data VCl = VCl VEnv Tm

data Head
  = HMeta Meta
  | HLocal Lvl
  | HTop Lvl

data Val
  = VNe Head VSpine
  | VLam (Named Icit) {-# unpack #-} VCl
  | VPi (Named Icit) ~VTy {-# unpack #-} VCl
  | VU
  | VIrrelevant

data Glued
  = GNe Head GSpine VSpine
  | GLam (Named Icit) {-# unpack #-} GCl
  | GPi (Named Icit)  {-# unpack #-} GVTy {-# unpack #-} GCl
  | GU
  | GIrrelevant

pattern GLocal :: Ix -> Glued
pattern GLocal x = GNe (HLocal x) SNil SNil

gvLocal :: Ix -> GV
gvLocal x = GV (GLocal x) (VLocal x)
{-# inline gvLocal #-}

pattern VLocal :: Ix -> Val
pattern VLocal x = VNe (HLocal x) SNil

pattern GTop :: Ix -> Glued
pattern GTop x = GNe (HTop x) SNil SNil

pattern VTop :: Ix -> Val
pattern VTop x = VNe (HTop x) SNil

pattern VMeta :: Meta -> Val
pattern VMeta x = VNe (HMeta x) SNil

pattern GMeta :: Meta -> Glued
pattern GMeta x = GNe (HMeta x) SNil SNil

gvU :: GVTy
gvU = GV GU VU
