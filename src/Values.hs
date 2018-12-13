
module Values where

import Data.Bits
import Data.Coerce

import Common
import Syntax

data Spine a = SNil | SAppI (Spine a) ~a | SAppE (Spine a) ~a
data Env a = ENil | EDef (Env a) ~a | ESkip (Env a)

envLength :: Env a -> Int
envLength = go 0 where
  go acc ENil       = acc
  go acc (EDef e _) = go (acc + 1) e
  go acc (ESkip e)  = go (acc + 1) e

type GEnv   = Env Glued
type VEnv   = Env Val
type GSpine = Spine Glued
type VSpine = Spine Val
type VTy    = Val
type GTy    = Glued
type GVTy   = GV

data GV  = GV ~Glued ~Val
data GCl = GCl GEnv VEnv Tm
data VCl = VCl VEnv Tm


newtype Head = Head Int deriving (Eq, Ord)

instance Show Head where
  show (HMeta x)  = "HMeta " ++ show x
  show (HLocal x) = "HLocal " ++ show x
  show (HTop x)   = "HTop " ++ show x

unpackHead :: Head -> (Int, Int)
unpackHead (Head n) = (n .&. 3, unsafeShiftR n 2)
{-# inline unpackHead #-}

pattern HMeta :: Meta -> Head
pattern HMeta x <- (unpackHead -> (0, coerce -> x)) where
  HMeta (MkMeta x) = Head (unsafeShiftL x 2)

pattern HLocal :: Ix -> Head
pattern HLocal x <- (unpackHead -> (1, x)) where
  HLocal x = Head (unsafeShiftL x 2 .|. 1)

pattern HTop :: Lvl -> Head
pattern HTop x <- (unpackHead -> (2, x)) where
  HTop x = Head (unsafeShiftL x 2 .|. 2)
{-# complete HMeta, HLocal, HTop #-}


data Val
  = VNe Head VSpine
  | VLam (Named Icit) {-# unpack #-} VCl
  | VPi (Named Icit) ~VTy {-# unpack #-} VCl
  | VFun ~VTy ~VTy
  | VU
  | VIrrelevant

data Glued
  = GNe Head GSpine VSpine
  | GLam (Named Icit) {-# unpack #-} GCl
  | GPi (Named Icit)  {-# unpack #-} GVTy {-# unpack #-} GCl
  | GFun {-# unpack #-} GVTy {-# unpack #-} GVTy
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
