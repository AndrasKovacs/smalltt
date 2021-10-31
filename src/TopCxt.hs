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
import qualified Region as R
import qualified Evaluation as E
import qualified SymTable as ST
import Common
import CoreTypes
import MetaCxt
import ElabState

#include "deriveCanIO.h"

-- | Top-level elaboration context.
data Cxt = Cxt {
  lvl    :: Lvl,         -- size of cxt
  info   :: TopInfo,     -- span, term, ty for each def
  vals   :: TopVals,     -- lazy val for each def
  tbl    :: ST.SymTable, -- symtable
  mcxt   :: MetaCxt      -- metacontext
  }

CAN_IO5(
  Cxt,

  IntRep, UnliftedRep, UnliftedRep, UnliftedRep, UnliftedRep,

  Int#, MutableArray# RealWorld TopEntry, MutableArray# RealWorld Val,
    MutableArrayArray# RealWorld, MutableArrayArray# RealWorld,

  Cxt (Lvl (I# a)) (ALM.Array b) (ALM.Array c) (ST.SymTable (RUUU.Ref (AUM.Array d)))
      (ADL.Array (RUU.Ref (AUM.Array e))),

  CoeTop)

-- | New top context from a source file and the number of top defs.
new :: B.ByteString -> Int -> U.IO Cxt
new src len = U.do
  info   <- U.io $ ALM.new len (error "undefined top-level entry")
  vals   <- U.io $ ALM.new len (error "undefined top-level entry")
  tbl    <- ST.new src
  ms     <- U.io $ ADL.empty
  U.pure (Cxt 0 info vals tbl ms)
{-# inline new #-}

-- | Extend cxt with a top-level definition. Updates destructively.
define :: Span -> Ty -> GTy -> Tm -> Cxt -> U.IO Cxt
define x a ga t (Cxt len info vals tbl ms) = U.do
  r     <- U.io getRegion
  a     <- R.copyTo r a
  t     <- R.copyTo r t
  entry <- R.copyTo r (TopEntry x a t)
  let ~vt = E.eval (E.Cxt ms vals) ENil t
  U.io $ ALM.write info (coerce len) entry
  U.io $ ALM.write vals (coerce len) vt
  ST.insert x (ST.Top len a ga t) tbl
  U.pure (Cxt (len + 1) info vals tbl ms)
{-# inline define #-}
