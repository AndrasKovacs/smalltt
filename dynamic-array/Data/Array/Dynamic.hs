
module Data.Array.Dynamic (
    empty
  , Array
  , clear
  , push
  , Data.Array.Dynamic.read
  , showArray
  , size
  , unsafeRead
  , unsafeWrite
  , write
  , unsafeLast
  , Data.Array.Dynamic.last
  , isEmpty
  , foldl'
  , foldlIx'
  , foldr'
  , foldrIx'
  , Data.Array.Dynamic.any
  , Data.Array.Dynamic.all
  , allIx
  , anyIx
  ) where

import qualified Data.Primitive.PrimArray     as PA
import qualified Data.Primitive.Array         as A
import qualified Data.Primitive.UnliftedArray as UA

import GHC.Types
import GHC.Prim

type role Array representational
data Array (a :: *) = Array (UA.MutableUnliftedArray RealWorld
                            (A.MutableArray RealWorld a))

instance UA.PrimUnlifted (Array a) where
  toArrayArray# (Array arr) = unsafeCoerce# arr
  {-# inline toArrayArray# #-}
  fromArrayArray# arr = Array (unsafeCoerce# arr)
  {-# inline fromArrayArray# #-}

defaultCapacity :: Int
defaultCapacity = 5
{-# inline defaultCapacity #-}

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

unsafeRead :: Array a -> Int -> IO a
unsafeRead (Array arr) (I# i) = do
  A.MutableArray elems <- UA.readUnliftedArray arr 1
  IO $ \s -> case readArray# elems i s of
    (# s, a #) -> (# s, a #)
{-# inline unsafeRead #-}

read :: Array a -> Int -> IO a
read arr i = do
  s <- size arr
  if i < s
    then unsafeRead arr i
    else error "Data.Array.Dynamic.read: out of bounds"
{-# inline read #-}

unsafeWrite :: Array a -> Int -> a -> IO ()
unsafeWrite (Array arr) (I# i) ~a = do
  A.MutableArray elems <- UA.readUnliftedArray arr 1
  IO $ \s -> case writeArray# elems i a s of
    s -> (# s, () #)
{-# inline unsafeWrite #-}

write :: Array a -> Int -> a -> IO ()
write arr i ~a = do
  s <- size arr
  if i < s
    then unsafeWrite arr i a
    else error "Data.Array.Dynamic.write: out of bounds"
{-#  inline write #-}

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

unsafeLast :: Array a -> IO a
unsafeLast arr = do
  i <- size arr
  Data.Array.Dynamic.unsafeRead arr (i - 1)
{-# inline unsafeLast #-}

isEmpty :: Array a -> IO Bool
isEmpty arr = (==0) <$> size arr
{-# inline isEmpty #-}

last :: Array a -> IO a
last arr = do
  i <- size arr
  isEmpty arr >>= \case
    True -> error "Data.Array.Dynamic.last: empty array"
    _    -> Data.Array.Dynamic.unsafeRead arr (i - 1)
{-# inline last #-}

showArray :: Show a => Array a -> IO String
showArray (Array arr) = do
  elems   <- getElems arr
  sizeRef <- getSizeRef arr
  size    <- PA.readPrimArray sizeRef 0
  elems'  <- A.freezeArray elems 0 size
  pure (show elems')

foldl' :: (b -> a -> b) -> b -> Array a -> IO b
foldl' f b = \arr -> do
  s <- size arr
  let go i b | i == s    = pure b
             | otherwise = do
                 a <- unsafeRead arr i
                 go (i + 1) (f b a)
  go 0 b
{-# inline foldl' #-}

foldlIx' :: (Int -> b -> a -> b) -> b -> Array a -> IO b
foldlIx' f b = \arr -> do
  s <- size arr
  let go i b | i == s    = pure b
             | otherwise = do
                 a <- unsafeRead arr i
                 go (i + 1) (f i b a)
  go 0 b
{-# inline foldlIx' #-}

foldr' :: (a -> b -> b) -> b -> Array a -> IO b
foldr' f b = \arr -> do
  s <- size arr
  let go i b | i == (-1) = pure b
             | otherwise = do
                 a <- unsafeRead arr i
                 go (i - 1) (f a b)
  go (s - 1) b
{-# inline foldr' #-}

foldrIx' :: (Int -> a -> b -> b) -> b -> Array a -> IO b
foldrIx' f b = \arr -> do
  s <- size arr
  let go i b | i == (-1) = pure b
             | otherwise = do
                 a <- unsafeRead arr i
                 go (i - 1) (f i a b)
  go (s - 1) b
{-# inline foldrIx' #-}

any :: (a -> Bool) -> Array a -> IO Bool
any f = foldl' (\b a -> f a || b) False
{-# inline any #-}

all :: (a -> Bool) -> Array a -> IO Bool
all f = foldl' (\b a -> f a && b) True
{-# inline all #-}

anyIx :: (Int -> a -> Bool) -> Array a -> IO Bool
anyIx f = foldlIx' (\i b a -> f i a || b) False
{-# inline anyIx #-}

allIx :: (Int -> a -> Bool) -> Array a -> IO Bool
allIx f = foldlIx' (\i b a -> f i a && b) True
{-# inline allIx #-}
