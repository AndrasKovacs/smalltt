
module MetaCxt where

import Common
import CoreTypes
import qualified Data.Array.Dynamic.L as ADL
import qualified UIO as U

data MetaEntry = MEUnsolved | MESolved ~Val
type MetaCxt = ADL.Array MetaEntry

new :: IO MetaCxt
new = ADL.empty
{-# inline new #-}

fresh :: MetaCxt -> U.IO Int
fresh ms = U.do
  x <- U.io $ ADL.size ms
  U.io $ ADL.push ms MEUnsolved
  U.pure x
{-# inlinable fresh #-}

solve :: MetaCxt -> MetaVar -> Val -> U.IO ()
solve ms x ~v = U.io $ do
  ADL.read ms (coerce x) >>= \case
    MESolved _ -> impossible
    _          -> ADL.write ms (coerce x) (MESolved v)
{-# inline solve #-}
