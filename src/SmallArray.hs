
module SmallArray (
    type Array
  , type MArray
  , type IOArray
  , SmallArray.read
  , new
  , unsafeFreeze
  , write
  , size
  , index
  , sizeM
  ) where

import Control.Monad.Primitive
import qualified Data.Primitive.SmallArray as SA

type Array = SA.SmallArray
type MArray = SA.SmallMutableArray
type IOArray = MArray RealWorld

-- read
--   :: PrimMonad m =>
--      SA.SmallMutableArray (PrimState m) a -> Int -> m a
-- read = SA.readSmallArray
-- {-# inline read #-}

read
  :: PrimMonad m =>
     SA.SmallMutableArray (PrimState m) a -> Int -> m a
read arr i | i >= 0 && i < SA.sizeofSmallMutableArray arr = SA.readSmallArray arr i
           | otherwise = error "SmallArray.read: index out of bounds"
{-# inline read #-}

-- write
--   :: PrimMonad m =>
--      SA.SmallMutableArray (PrimState m) a -> Int -> a -> m ()
-- write = SA.writeSmallArray
-- {-# inline write #-}

write
  :: PrimMonad m =>
     SA.SmallMutableArray (PrimState m) a -> Int -> a -> m ()
write arr i ~a | i >= 0 && i < SA.sizeofSmallMutableArray arr = SA.writeSmallArray arr i a
               | otherwise = error "SmallArray.write: index out of bounds"
{-# inline write #-}

new
  :: PrimMonad m =>
     Int -> a -> m (SA.SmallMutableArray (PrimState m) a)
new = SA.newSmallArray
{-# inline new #-}

unsafeFreeze
  :: PrimMonad m =>
     SA.SmallMutableArray (PrimState m) a -> m (SA.SmallArray a)
unsafeFreeze = SA.unsafeFreezeSmallArray
{-# inline unsafeFreeze #-}

size :: SA.SmallArray a -> Int
size = SA.sizeofSmallArray
{-# inline size #-}

-- index :: SA.SmallArray a -> Int -> a
-- index = SA.indexSmallArray
-- {-# inline index #-}

index :: SA.SmallArray a -> Int -> a
index arr i | i >= 0 && i < size arr = SA.indexSmallArray arr i
            | otherwise = error "SmallArray.index: index out of bounds"
{-# inline index #-}


sizeM :: SA.SmallMutableArray s a -> Int
sizeM = SA.sizeofSmallMutableArray
{-# inline sizeM #-}
