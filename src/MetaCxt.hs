{-# language UnboxedTuples #-}

module MetaCxt where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Array.UM        as AUM
import qualified Data.Ref.UU          as RUU
import qualified Data.Ref.F           as RF

import GHC.Exts

import qualified UIO as U
import qualified UIO
import Common
import CoreTypes

#include "deriveCanIO.h"

data MetaEntry = MEUnsolved | MESolved (RF.Ref MetaVar) Tm ~Val
type MetaCxt = ADL.Array MetaEntry

CAN_IO(MetaEntry, LiftedRep, MetaEntry, x, CoeMetaEntry)

CAN_IO(MetaCxt, UnliftedRep, MutableArrayArray# RealWorld,
       ADL.Array (RUU.Ref (AUM.Array x)), CoeMetaCxt)

size :: MetaCxt -> U.IO Lvl
size ms = coerce U.<$> U.io (ADL.size ms)
{-# inline size #-}

new :: U.IO MetaCxt
new = U.io (ADL.empty)
{-# inline new #-}

fresh :: MetaCxt -> U.IO Int
fresh ms = U.do
  x <- U.io $ ADL.size ms
  U.io $ ADL.push ms MEUnsolved
  U.pure x
{-# inlinable fresh #-}

read :: MetaCxt -> MetaVar -> U.IO MetaEntry
read ms x = U.io $ ADL.unsafeRead ms (coerce x)
{-# inline read #-}

solve :: MetaCxt -> MetaVar -> Tm -> Val -> U.IO ()
solve ms x t ~v = U.io $ do
  U.toIO (MetaCxt.read ms x) >>= \case
    MESolved _ _ _ -> impossible
    _              -> do
      ref <- RF.new (-1)
      ADL.write ms (coerce x) (MESolved ref t v)
{-# inline solve #-}
