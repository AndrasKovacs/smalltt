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

#include "../deriveCanIO.h"

data Cxt = Cxt {
    lvl     :: Lvl       -- ^ Size of local context.
  , env     :: Env       -- ^ Local evaluation environment.
  , mask    :: LvlSet    -- ^ Masks bound vars in local context.
  , tbl     :: SymTable  -- ^ Symbol table for all names (top + local).
  , mcxt    :: MetaCxt   -- ^ Metacontext.
  , names   :: Names     -- ^ Compact list of local names, for error printing.
  , frz     :: MetaVar   -- ^ Every metavar smaller than frz is frozen.
  }

instance Show Cxt where
  show _ = "<cxt>"

CAN_IO7(
  Cxt,

  IntRep, LiftedRep, IntRep,
    UnliftedRep, UnliftedRep, LiftedRep, IntRep,

  Int#, Env, Int#,
    MutableArrayArray# RealWorld, MutableArrayArray# RealWorld,
      Names, Int#,

  Cxt (Lvl (I# a)) b (LvlSet (I# c))
    (ST.SymTable (RUUU.Ref (AUM.Array d))) (ADL.Array (RUU.Ref (AUM.Array e))) f
      (MkMetaVar (I# g)),

  CoeCxt)
