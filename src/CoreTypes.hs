{-# language UnboxedTuples #-}
{-# options_ghc -funbox-strict-fields #-}

module CoreTypes where

import GHC.Exts
import qualified UIO
import Common
import EnvMask

#include "deriveCanIO.h"

data Spine
  = SId
  | SApp Spine Val Icit

CAN_IO(Spine, LiftedRep, Spine, x, CoeSpine)

data Closure
  = Closure Env Tm

CAN_IO2(Closure, TupleRep [ LiftedRep COMMA LiftedRep ], (# Env, Tm #), Closure x y, CoeClosure)

data Env
  = ENil
  | EDef Env ~Val

type VTy = Val

data Val
  = VLocalVar Lvl Spine
  | VFlex MetaVar Spine
  | VUnfold UnfoldHead Spine ~Val
  | VLam Name Icit Closure
  | VPi Name Icit VTy Closure
  | VU
  | VIrrelevant

------------------------------------------------------------

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl ~Val
  | Let Span Tm Tm Tm
  | App Tm Tm Icit
  | Lam Name Icit Tm
  | Meta MetaVar
  | InsertedMeta MetaVar EnvMask
  | Pi Name Icit Ty Ty
  | Irrelevant
  | U

CAN_IO(Tm, LiftedRep, Tm, x, CoeTm)
CAN_IO(Val, LiftedRep, Val, x, CoeVal)

------------------------------------------------------------

-- data UnfoldHead = UHTopVar Lvl | UHSolved MetaVar
newtype UnfoldHead = UnfoldHead# Int
  deriving Eq via Int

unpackUH# :: UnfoldHead -> (# Lvl | MetaVar #)
unpackUH# (UnfoldHead# (I# i)) = case i <=# 0# of
  1# -> (# Lvl (I# (negateInt# i)) | #)
  _  -> (# | MkMetaVar (I# i) #)
{-# inline unpackUH# #-}

pattern UHTopVar :: Lvl -> UnfoldHead
pattern UHTopVar x <- (unpackUH# -> (# x | #)) where
  UHTopVar (Lvl x) = UnfoldHead# (negate x)

pattern UHSolved :: MetaVar -> UnfoldHead
pattern UHSolved x <- (unpackUH# -> (# | x #)) where
  UHSolved (MkMetaVar x) = UnfoldHead# x
