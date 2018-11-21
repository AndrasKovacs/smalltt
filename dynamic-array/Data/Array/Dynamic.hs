
module Data.Array.Dynamic (
    empty
  , Array
  , clear
  , push
  , Data.Array.Dynamic.read
  , read'
  , showArray
  , size
  , unsafeRead
  , unsafeRead'
  ) where

import qualified Data.Primitive.PrimArray     as PA
import qualified Data.Primitive.Array         as A
import qualified Data.Primitive.UnliftedArray as UA

import GHC.Types
import GHC.Prim
import Data.Functor.Identity

type role Array representational
data Array (a :: *) = Array (UA.MutableUnliftedArray RealWorld
                            (A.MutableArray RealWorld a))

defaultCapacity :: Int
defaultCapacity = 5
{-# inline defaultCapacity #-}

-- outOfBounds :: a
-- outOfBounds = error "Data.Array.Dynamic: out-of bounds access"
-- {-# noinline outOfBounds #-}

undefinedElement :: a
undefinedElement = error "Data.Array.Dynamic: undefined element"
{-# noinline undefinedElement #-}

empty :: forall a. IO (Array a)
empty = do
  (sizeRef :: PA.MutablePrimArray _ Int) <- PA.newPrimArray 1
  PA.writePrimArray sizeRef 0 0
  elems <- A.newArray defaultCapacity (undefinedElement :: a)
  struct <- UA.newUnliftedArray 2 (unsafeCoerce# sizeRef)
  UA.writeUnliftedArray struct 1 elems
  pure (Array struct)

unsafeRead' :: Array a -> Int -> IO (Identity a)
unsafeRead' (Array arr) (I# i) = do
  A.MutableArray elems <- UA.readUnliftedArray arr 1
  IO $ \s -> case readArray# elems i s of
    (# s, a #) -> (# s, Identity a #)
{-# inline unsafeRead' #-}

unsafeRead :: Array a -> Int -> IO a
unsafeRead arr i = do
  Identity a <- unsafeRead' arr i
  pure a
{-# inline unsafeRead #-}

read' :: Array a -> Int -> IO (Identity a)
read' arr i = do
  s <- size arr
  if i < s
    then unsafeRead' arr i
    else error "Data.Array.Dynamic.read': out of bounds"
{-# inline read' #-}

read :: Array a -> Int -> IO a
read arr i = do
  s <- size arr
  if i < s
    then unsafeRead arr i
    else error "Data.Array.Dynamic.read: out of bounds"
{-# inline read #-}

getSizeRef :: UA.MutableUnliftedArray RealWorld (A.MutableArray RealWorld a)
       -> IO (PA.MutablePrimArray RealWorld Int)
getSizeRef arr = do
  x <- UA.readUnliftedArray arr 0
  pure (unsafeCoerce# x)
{-# inline getSizeRef #-}

getElems :: UA.MutableUnliftedArray RealWorld (A.MutableArray RealWorld a)
       -> IO (A.MutableArray RealWorld a)
getElems arr = UA.readUnliftedArray arr 1
{-# inline getElems #-}

push :: Array a -> a -> IO ()
push (Array arr) ~a = do
  sizeRef <- getSizeRef arr
  elems <- getElems arr
  size <- PA.readPrimArray sizeRef 0
  let cap = A.sizeofMutableArray elems
  PA.writePrimArray sizeRef 0 (size + 1)
  if (size == cap) then do
    let cap' = 2 * cap
    elems' <- A.newArray cap' (undefinedElement :: a)
    A.copyMutableArray elems' 0 elems 0 size
    A.writeArray elems' size a
    UA.writeUnliftedArray arr 1 elems'
  else do
    A.writeArray elems size a

clear :: Array a -> IO ()
clear (Array arr) = do
  (sizeRef :: PA.MutablePrimArray _ Int) <- PA.newPrimArray 1
  PA.writePrimArray sizeRef 0 0
  elems <- A.newArray defaultCapacity (undefinedElement :: a)
  UA.writeUnliftedArray arr 0 (unsafeCoerce# sizeRef)
  UA.writeUnliftedArray arr 1 elems

size :: Array a -> IO Int
size (Array arr) = do
  sizeRef <- getSizeRef arr
  PA.readPrimArray sizeRef 0
{-# inline size #-}

showArray :: Show a => Array a -> IO String
showArray (Array arr) = do
  elems   <- getElems arr
  sizeRef <- getSizeRef arr
  size    <- PA.readPrimArray sizeRef 0
  elems'  <- A.freezeArray elems 0 size
  pure (show elems')
