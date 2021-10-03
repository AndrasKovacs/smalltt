
module MetaCxt where

import CoreTypes
import qualified Data.Array.Dynamic.L as ADL

data MetaEntry = MEUnsolved | MESolved ~Val
type MetaCxt = ADL.Array MetaEntry

new :: IO MetaCxt
new = ADL.empty
{-# inline new #-}
