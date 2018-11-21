
module Values where

import Common
import Syntax

data Env   a = ENil  | ESnoc (Env a) ~a
data Env'  a = ENil' | ESnoc' (Env' a) a
data Spine a = SNil  | SApp (Spine a) ~a Icit

type GEnv   = Env' (Maybe Glued)
type VEnv   = Env' (Maybe Val)
type GSpine = Spine Glued
type VSpine = Spine Val
type VTy    = Val
type GTy    = Glued
type GVTy   = GV

data GV = GV ~Glued ~Val

data GCl = GCl Int GEnv VEnv Tm
data VCl = VCl Int VEnv Tm

data Head
  = HMeta MetaIx
  | HLocal Ix
  | HTop Ix

data Val
  = VNe Head VSpine
  | VLam (T2 Name Icit) {-# unpack #-} VCl
  | VPi (T2 Name Icit) ~VTy {-# unpack #-} VCl
  | VU
  | VIrrelevant

data Glued
  = GNe Head GSpine VSpine
  | GLam (T2 Name Icit) {-# unpack #-} GCl
  | GPi (T2 Name Icit) {-# unpack #-} GVTy {-# unpack #-} GCl
  | GU
  | GIrrelevant

pattern GLocal :: Ix -> Glued
pattern GLocal x = GNe (HLocal x) SNil SNil

pattern VLocal :: Ix -> Val
pattern VLocal x = VNe (HLocal x) SNil

pattern GTop :: Ix -> Glued
pattern GTop x = GNe (HTop x) SNil SNil

pattern VTop :: Ix -> Val
pattern VTop x = VNe (HTop x) SNil
