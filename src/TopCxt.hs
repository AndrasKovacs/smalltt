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
import Common
import CoreTypes

#include "deriveCanIO.h"

-- | Top-level elaboration context.
data Cxt = Cxt {
  lvl    :: Lvl,         -- size of cxt
  info   :: TopInfo,     -- span, term, ty for each def
  tbl    :: ST.SymTable, -- symtable
  mcxt   :: MetaCxt      -- metacontext
  }

CAN_IO4(
  Cxt,

  IntRep, UnliftedRep, UnliftedRep, UnliftedRep,

  Int#, MutableArray# RealWorld TopEntry,
    MutableArrayArray# RealWorld, MutableArrayArray# RealWorld,

  Cxt (Lvl (I# a)) (ALM.Array b) (ST.SymTable (RUUU.Ref (AUM.Array c)))
      (ADL.Array (RUU.Ref (AUM.Array d))),

  CoeTop)

-- | New top context from a source file and the number of top defs.
new :: B.ByteString -> Int -> U.IO Cxt
new src len = U.do
  info   <- U.io $ ALM.new len (error "undefined top entry")
  tbl    <- ST.new src
  ms     <- U.io $ ADL.empty
  U.pure (Cxt 0 info tbl ms)
{-# inline new #-}

-- | Extend cxt with a top-level definition. Updates destructively.
define :: Span -> Ty -> GTy -> Tm -> MetaVar -> Cxt -> U.IO Cxt
define x a ga t frz (Cxt len info tbl ms) = U.do
  let ~vt = E.eval ms ENil t
  U.io $ ALM.write info (coerce len) (TopEntry x a t frz)
  ST.insert x (ST.Top a ga t (TopVar len vt)) tbl
  U.pure (Cxt (len + 1) info tbl ms)
{-# inline define #-}
