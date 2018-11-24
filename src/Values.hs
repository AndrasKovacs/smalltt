
module Values where

import Common
import Syntax

data Env   a = ENil  | ESnoc (Env a) ~a       deriving (Functor, Foldable, Traversable)
data Env'  a = ENil' | ESnoc' (Env' a) a      deriving (Functor, Foldable, Traversable)
data Spine a = SNil  | SApp (Spine a) ~a Icit deriving (Functor, Foldable, Traversable)

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
  | VLam NameIcit {-# unpack #-} VCl
  | VPi NameIcit ~VTy {-# unpack #-} VCl
  | VU
  | VIrrelevant

data Glued
  = GNe Head GSpine VSpine
  | GLam NameIcit {-# unpack #-} GCl
  | GPi NameIcit  {-# unpack #-} GVTy {-# unpack #-} GCl
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

pattern VMeta :: MetaIx -> Val
pattern VMeta x = VNe (HMeta x) SNil

pattern GMeta :: MetaIx -> Glued
pattern GMeta x = GNe (HMeta x) SNil SNil
