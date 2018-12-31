
module Values where

import Data.Bits
import Data.Coerce
import Text.Printf

import Common
import Syntax

data Spine a = SNil | SAppI (Spine a) ~a | SAppE (Spine a) ~a

data Env a = ENil | EDef (Env a) ~a | ESkip (Env a)
  deriving (Functor)

envLength :: Env a -> Int
envLength = go 0 where
  go acc ENil       = acc
  go acc (EDef e _) = go (acc + 1) e
  go acc (ESkip e)  = go (acc + 1) e

spineLength :: Spine a -> Int
spineLength = go 0 where
  go l SNil         = l
  go l (SAppI sp _) = go (l + 1) sp
  go l (SAppE sp _) = go (l + 1) sp

takeSpine :: Int -> Spine a -> Spine a
takeSpine 0 sp           = SNil
takeSpine i (SAppI sp a) = SAppI (takeSpine (i - 1) sp) a
takeSpine i (SAppE sp a) = SAppE (takeSpine (i - 1) sp) a
takeSpine _ _            = error "takeSpine: impossible"

dropSpine :: Int -> Spine a -> Spine a
dropSpine 0 sp           = sp
dropSpine i (SAppI sp _) = dropSpine (i - 1) sp
dropSpine i (SAppE sp _) = dropSpine (i - 1) sp
dropSpine _ _            = error "dropSpine: impossible"

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


-- Bitpacked definition, with 3 bits for tags.


newtype Head = Head Int deriving (Eq)

unpackHead :: Head -> (Int, Int)
unpackHead (Head x) = (x .&. 7, unsafeShiftR x 3)
{-# inline unpackHead #-}

-- | Head with local (bound) variable.
pattern HLocal :: Lvl -> Head
pattern HLocal x <- (unpackHead -> (0, x)) where
  HLocal x = Head (unsafeShiftL x 3)

-- | Head with meta.
pattern HMeta :: Meta -> Head
pattern HMeta x <- (unpackHead -> (1, coerce -> x)) where
  HMeta x = Head (unsafeShiftL (coerce x) 3 .|. 1)

-- | Top head with rewrite rule, but applied to too few arguments
--   for any rule to fire.
pattern HTopUnderapplied :: Int2 -> Head
pattern HTopUnderapplied x <- (unpackHead -> (2, coerce -> x)) where
  HTopUnderapplied x = Head (unsafeShiftL (coerce x) 3 .|. 2)

-- | Top head with rewrite rule, such that a rewrite previously
--   got stuck on a metavariable.
pattern HTopBlockedOnMeta :: Int2 -> Head
pattern HTopBlockedOnMeta x <- (unpackHead -> (3, coerce -> x)) where
  HTopBlockedOnMeta x = Head (unsafeShiftL (coerce x) 3 .|. 3)

-- | Head with a top-level postulate such there was no matching rewrite rule at
--   the time of the forcing. The second field is the number of rewrite rules attached
--   to the name. We use this to check for new rewrite rules when forcing.
pattern HTopRigid :: Int2 -> Head
pattern HTopRigid x <- (unpackHead -> (4, coerce -> x)) where
  HTopRigid x = Head (unsafeShiftL (coerce x) 3 .|. 4)

-- | Head with a variable coming from a rewrite LHS rule.
pattern HRuleVar :: Lvl -> Head
pattern HRuleVar x <- (unpackHead -> (5, x)) where
  HRuleVar x = Head (unsafeShiftL x 3 .|. 5)
{-# complete HLocal, HMeta, HTopUnderapplied,  HTopBlockedOnMeta, HTopRigid, HRuleVar #-}


instance Show Head where
  show (HLocal x)    = "local " ++ show x
  show (HMeta  x)    = show x
  show (HTopRigid x) = "rigid " ++ show x
  show (HTopBlockedOnMeta (Int2 top mj)) =
    printf "%d blocked on %d" top mj
  show (HTopUnderapplied (Int2 top arity)) =
    printf "%d underapplied by %d" top arity
  show (HRuleVar x) = "RuleVar " ++ show x

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------


pattern GLocal :: Ix -> Glued
pattern GLocal x = GNe (HLocal x) SNil SNil

pattern GMeta :: Meta -> Glued
pattern GMeta x = GNe (HMeta x) SNil SNil

pattern GRuleVar :: Lvl -> Glued
pattern GRuleVar x = GNe (HRuleVar x) SNil SNil

pattern VLocal :: Ix -> Val
pattern VLocal x = VNe (HLocal x) SNil

pattern VTop :: Int2 -> Val
pattern VTop x = VNe (HTopRigid x) SNil

pattern VMeta :: Meta -> Val
pattern VMeta x = VNe (HMeta x) SNil

pattern VRuleVar :: Lvl -> Val
pattern VRuleVar x = VNe (HRuleVar x) SNil

gvLocal :: Ix -> GV
gvLocal x = GV (GLocal x) (VLocal x)
{-# inline gvLocal #-}

gvU :: GVTy
gvU = GV GU VU
