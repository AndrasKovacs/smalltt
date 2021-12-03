{-# language UnboxedTuples #-}

module TopCxt where

import qualified Data.ByteString      as B
import qualified Data.Array.LM        as ALM
import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Array.UM        as AUM
import qualified Data.Ref.UU          as RUU
import qualified Data.Ref.UUU         as RUUU
import GHC.Exts

import qualified UIO
import qualified UIO as U
import qualified Evaluation as E
import qualified SymTable as ST
import qualified MetaCxt as MC
import Common
import CoreTypes

#include "deriveCanIO.h"

-- | Top-level elaboration context.
data Cxt = Cxt {
  lvl    :: Lvl,         -- ^ Size of context.
  info   :: TopInfo,     -- ^ Span, term, type for each definition.
  tbl    :: ST.SymTable, -- ^ Symbol table.
  mcxt   :: MetaCxt,     -- ^ Metacontext.
  frz    :: MetaVar      -- ^ All metavars small than frz are frozen.
  }

CAN_IO5(
  Cxt,

  IntRep, UnliftedRep, UnliftedRep, UnliftedRep, IntRep,

  Int#, MutableArray# RealWorld TopEntry,
    MutableArrayArray# RealWorld, MutableArrayArray# RealWorld, Int#,

  Cxt (Lvl (I# a)) (ALM.Array b) (ST.SymTable (RUUU.Ref (AUM.Array c)))
      (ADL.Array (RUU.Ref (AUM.Array d))) (MkMetaVar (I# e)),

  CoeTop)

-- | New top context from a source file and the number of top defs.
new :: B.ByteString -> Int -> U.IO Cxt
new src len = U.do
  info   <- U.io $ ALM.new len (error "undefined top entry")
  tbl    <- ST.new src
  ms     <- U.io $ ADL.empty
  U.pure (Cxt 0 info tbl ms 0)
{-# inline new #-}

-- | Extend cxt with a top-level definition. Updates destructively. Freezes all
--   current metavariables.
define :: Span -> Ty -> GTy -> Tm -> Cxt -> U.IO Cxt
define x a ga t (Cxt len info tbl ms _) = U.do
  let ~vt = E.eval ms ENil t
  frz <- coerce U.<$> MC.size ms
  U.io $ ALM.write info (coerce len) (TopEntry x a t frz)
  ST.insert x (ST.Top a ga t (TopVar len (coerce vt))) tbl
  U.pure (Cxt (len + 1) info tbl ms frz)
{-# inline define #-}
