{-# language UnboxedTuples #-}
{-# options_ghc -funbox-strict-fields #-}

module CoreTypes where

import qualified UIO
import Common
import EnvMask

#include "deriveCanIO.h"

data Spine
  = SId
  | SApp Spine Val Icit

data Closure
  = Closure Env Tm

data Env
  = ENil
  | EDef Env ~Val

type VTy = Val

data Val
  = VLocalVar Lvl Spine
  | VMeta MetaVar Spine
  | VTopVar Lvl Spine ~Val
  | VLam Name Icit Closure
  | VPi Name Icit VTy Closure
  | VU
  | VIrrelevant

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
