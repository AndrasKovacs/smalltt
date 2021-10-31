{-# language UnboxedTuples #-}

module Region where

import Data.Proxy
import Data.Unlifted
import GHC.Prim
import GHC.Types

import qualified UIO
import qualified UIO as U

#include "deriveCanIO.h"

-- | Pinned memory region, only for single-threaded allocation.
data Region = Region# Compact#

CAN_IO(Region, UnliftedRep, Compact#, Region# x, CoeRegion)

instance Unlifted Region where
  type Rep Region = Compact#
  to# (Region# c) = c; {-# inline to# #-}
  from# = Region#; {-# inline from# #-}
  defaultElem = undefined

maxBlockSize :: Int
maxBlockSize = 1032192
{-# inline maxBlockSize #-}

-- | Create new pinned region with given block size.
newSized :: Int -> U.IO Region
newSized (I# blocksize) = U.IO (compactNew# (int2Word# blocksize))
{-# inline newSized #-}

-- | Create new pinned region with 1MB block size.
new :: U.IO Region
new = newSized maxBlockSize
{-# inline new #-}

-- | Copy an object to a region, return reference to copy.
copyTo :: U.CanIO a => Region -> a -> U.IO a
copyTo (Region# c) a = U.IO \s -> case compactAdd# c a s of
  (# s , a #) -> U.pure# a s
{-# inline copyTo #-}

contains :: Region -> a -> U.IO Bool
contains (Region# c) a = U.IO \s -> case compactContains# c a s of
  (# s, b #) -> U.pure# (isTrue# b) s
{-# inline contains #-}

size :: Region -> U.IO Int
size (Region# c) = U.IO \s -> case compactSize# c s of
  (# s, n #) -> U.pure# (I# (word2Int# n)) s
{-# inline size #-}
