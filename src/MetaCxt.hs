{-# language UnboxedTuples #-}

module MetaCxt where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Ref.F           as RF
import GHC.Exts

import qualified UIO as U
import LvlSet
import Common
import CoreTypes

--------------------------------------------------------------------------------

size :: MetaCxt -> U.IO Lvl
size ms = coerce U.<$> U.io (ADL.size ms)
{-# inline size #-}

fresh :: MetaCxt -> LvlSet -> U.IO Int
fresh ms mask = U.do
  x <- U.io $ ADL.size ms
  U.io $ ADL.push ms (Unsolved mask)
  U.pure x
{-# inlinable fresh #-}

read :: MetaCxt -> MetaVar -> U.IO MetaEntry
read ms x = U.io $ ADL.unsafeRead ms (coerce x)
{-# inline read #-}

solve :: MetaCxt -> MetaVar -> Tm -> Val -> U.IO ()
solve ms x t ~v = U.io $ do
  ADL.read ms (coerce x) >>= \case
    Solved{} -> impossible
    Unsolved mask -> do
      ref <- RF.new (-1)
      ADL.write ms (coerce x) (Solved ref mask t v)
{-# inline solve #-}
