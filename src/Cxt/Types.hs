{-# language UnboxedTuples #-}

module Cxt.Types where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Array.UM        as AUM
import qualified Data.Ref.UU          as RUU
import qualified Data.Ref.UUU         as RUUU
import GHC.Exts

import qualified UIO
import qualified SymTable as ST

import Common
import CoreTypes
import LvlSet (LvlSet(..))
import SymTable (SymTable(..))
import MetaCxt

#include "../deriveCanIO.h"

data Cxt = Cxt {
    lvl     :: Lvl
  , env     :: Env
  , mask    :: LvlSet
  , tbl     :: SymTable
  , mcxt    :: MetaCxt
  , names   :: Names
  }

instance Show Cxt where
  show _ = "<cxt>"

CAN_IO6(
  Cxt,

  IntRep, LiftedRep, IntRep,
    UnliftedRep, UnliftedRep, LiftedRep,

  Int#, Env, Int#,
    MutableArrayArray# RealWorld, MutableArrayArray# RealWorld,
      Names,

  Cxt (Lvl (I# a)) b (LvlSet (I# c))
    (ST.SymTable (RUUU.Ref (AUM.Array d))) (ADL.Array (RUU.Ref (AUM.Array e))) f,

  CoeCxt)
