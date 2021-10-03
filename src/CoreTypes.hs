{-# options_ghc -funbox-strict-fields #-}

module CoreTypes where

import Common
import EnvMask

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
  | VLam Span Icit Closure
  | VPi Span Icit VTy Closure
  | VU
  | VIrrelevant

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl ~Val
  | Meta MetaVar
  | InsertedMeta MetaVar EnvMask
  | Let Span Tm Tm
  | App Tm Tm Icit
  | Lam Span Icit Tm
  | Pi Span Icit Ty Ty
  | Irrelevant
  | U
