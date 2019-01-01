
module Data.Array.Dynamic (
    empty
  , Array
  , clear
  , push
  , pushN
  , popN
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
  , forM_
  , forMIx_
  ) where

import qualified Data.Primitive.PrimArray     as PA
import qualified Data.Primitive.Array         as A
import qualified Data.Primitive.UnliftedArray as UA

import GHC.Types
import GHC.Prim
import Data.Bits

type role Array representational
data Array (a :: *) = Array (UA.MutableUnliftedArray RealWorld
                            (A.MutableArray RealWorld a))

instance UA.PrimUnlifted (Array a) where
  toArrayArray# (Array arr) = unsafeCoerce# arr
  {-# inline toArrayArray# #-}
  fromArrayArray# arr = Array (unsafeCoerce# arr)
  {-# inline fromArrayArray# #-}

defaultCapacity :: Int
defaultCapacity = 32
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
    let cap' = unsafeShiftL cap 1
    elems' <- A.newArray cap' (undefinedElement :: a)
    A.copyMutableArray elems' 0 elems 0 size
    A.writeArray elems' size a
    UA.writeUnliftedArray arr 1 elems'
  else do
    A.writeArray elems size a

pushN :: Array a -> a -> Int -> IO ()
pushN _           ~_ 0 = pure ()
pushN (Array arr) ~a n = do
  if (n < 0) then error "Data.Array.Dynamic.pushN: negative input"
             else pure ()
  sizeRef   <- getSizeRef arr
  elems     <- getElems arr
  size      <- PA.readPrimArray sizeRef 0
  let cap   = A.sizeofMutableArray elems
  let size' = size + n
  PA.writePrimArray sizeRef 0 size'
  let set dst i | i == size' = pure ()
      set dst i = A.writeArray dst i a >> set dst (i + 1)
  if (size' > cap) then do
    let cap' = unsafeShiftL size' 1
    elems' <- A.newArray cap' (undefinedElement :: a)
    A.copyMutableArray elems' 0 elems 0 size
    set elems' size
    UA.writeUnliftedArray arr 1 elems'
  else do
    set elems size
{-# inline pushN #-}

-- | Pop given number of elements. Overwrites popped elements with
--   undefined value, only deallocates array if the new array is empty
--   and the capacity is higher than the default capacity.
popN :: Array a -> Int -> IO ()
popN _           0 = pure ()
popN (Array arr) n = do
  if (n < 0) then error "Data.Array.Dynamic.popN: negative input"
             else pure ()
  sizeRef   <- getSizeRef arr
  elems     <- getElems arr
  size      <- PA.readPrimArray sizeRef 0
  let cap   = A.sizeofMutableArray elems
  let size' = size - n
  if size' < 0 then error "Data.Array.Dynamic.popN: empty array"
               else pure ()
  PA.writePrimArray sizeRef 0 size'
  if size' == 0 && cap > defaultCapacity then do
    elems <- A.newArray defaultCapacity (undefinedElement :: a)
    UA.writeUnliftedArray arr 1 elems
  else do
    let unset i | i == size = pure ()
        unset i = A.writeArray elems i undefinedElement >> unset (i + 1)
    unset size'
{-# inline popN #-}

clear :: Array a -> IO ()
clear (Array arr) = do
  sizeRef <- getSizeRef arr
  PA.writePrimArray sizeRef 0 0
  elems <- A.newArray defaultCapacity (undefinedElement :: a)
  UA.writeUnliftedArray arr 1 elems
{-# inline clear #-}

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

forM_ :: Array a -> (a -> IO b) -> IO ()
forM_ arr f = go (0 :: Int) where
  go i = do
    s <- size arr
    if i == s then pure () else do {x <- unsafeRead arr i; f x; go (i + 1)}
{-# inline forM_ #-}

forMIx_ :: Array a -> (Int -> a -> IO b) -> IO ()
forMIx_ arr f = go (0 :: Int) where
  go i = do
    s <- size arr
    if i == s then pure () else do {x <- unsafeRead arr i; f i x; go (i + 1)}
{-# inline forMIx_ #-}
