

module PrimArray (
    type Array
  , type MArray
  , type IOArray
  , PrimArray.read
  , new
  , unsafeFreeze
  , write
  , size
  , index
  , sizeM
  ) where

import Control.Monad.Primitive
import qualified Data.Primitive.PrimArray as PA
import Data.Primitive.Types

type Array   = PA.PrimArray
type MArray  = PA.MutablePrimArray
type IOArray = MArray RealWorld

-- read
--   :: (PrimMonad m, Prim a) =>
--      PA.MutablePrimArray (PrimState m) a -> Int -> m a
-- read = PA.readPrimArray
-- {-# inline read #-}


read
  :: (Prim a, PrimMonad m) =>
     PA.MutablePrimArray (PrimState m) a -> Int -> m a
read arr i | i >= 0 && i < PA.sizeofMutablePrimArray arr = PA.readPrimArray arr i
           | otherwise = error "PrimArray.read: index out of bounds"
{-# inline read #-}

-- write
--   :: (PrimMonad m, Prim a) =>
--      PA.MutablePrimArray (PrimState m) a -> Int -> a -> m ()
-- write = PA.writePrimArray
-- {-# inline write #-}

write
  :: (Prim a, PrimMonad m) =>
     PA.MutablePrimArray (PrimState m) a -> Int -> a -> m ()
write arr i ~a | i >= 0 && i < PA.sizeofMutablePrimArray arr = PA.writePrimArray arr i a
               | otherwise = error "PrimArray.write: index out of bounds"
{-# inline write #-}

new
  :: (PrimMonad m, Prim a) =>
     Int -> m (PA.MutablePrimArray (PrimState m) a)
new = PA.newPrimArray
{-# inline new #-}

unsafeFreeze
  :: PrimMonad m =>
     PA.MutablePrimArray (PrimState m) a -> m (PA.PrimArray a)
unsafeFreeze = PA.unsafeFreezePrimArray
{-# inline unsafeFreeze #-}

size :: Prim a => PA.PrimArray a -> Int
size = PA.sizeofPrimArray
{-# inline size #-}

-- index :: Prim a => PA.PrimArray a -> Int -> a
-- index = PA.indexPrimArray
-- {-# inline index #-}

index :: Prim a => PA.PrimArray a -> Int -> a
index arr i | i >= 0 && i < size arr = PA.indexPrimArray arr i
            | otherwise = error "PrimArray.index: index out of bounds"
{-# inline index #-}


sizeM :: Prim a => PA.MutablePrimArray s a -> Int
sizeM = PA.sizeofMutablePrimArray
{-# inline sizeM #-}
