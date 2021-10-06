{-# language UnboxedTuples, OverloadedStrings #-}

module SymTable (
    SymTable(..)
  , new
  , SymTable.lookup
  , delete
  , insert
  , size
  , eob
  , Entry(..)
  , modify) where

import qualified Data.Ref.UUU    as RUUU
import qualified Data.Ref.FF     as RFF
import qualified Data.Ref.L      as RL
import qualified Data.Array.LM   as ALM
import qualified Data.Array.LI   as ALI
import qualified Data.Array.UM   as AUM

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import qualified Data.ByteString.Unsafe as B

import Data.Bits
import GHC.Exts
import GHC.ForeignPtr
import Data.Word

import IO
import Common
import CoreTypes

import qualified UIO
import qualified UIO as U

#include "deriveCanIO.h"

-- Symtable entries
--------------------------------------------------------------------------------

data Entry
  = Top Lvl Ty ~VTy Tm ~Val  -- level, type, type val, def, def val
  | Local Lvl ~VTy           -- level, type val

-- instance Show Entry where
--   show (Local x _) = show x
--   show (Top x _ _ _ _) = show x

-- Span hashing
--------------------------------------------------------------------------------

newtype Hash = Hash {unHash :: Word}
  deriving (Eq, Show, Ord, Num, Bits) via Word

hashToInt :: Hash -> Int
hashToInt (Hash w) = fromIntegral w
{-# inline hashToInt #-}

unW# :: Word -> Word#
unW# (W# x) = x
{-# inline unW# #-}

foldedMultiply# :: Word# -> Word# -> Word#
foldedMultiply# x y = case timesWord2# x y of
  (# hi, lo #) -> xor# hi lo
{-# inline foldedMultiply# #-}

multiple :: Word
multiple = 11400714819323198549
{-# inline multiple #-}

salt :: Word
salt = 3032525626373534813
{-# inline salt #-}

combine# :: Word# -> Word# -> Word#
combine# x y = foldedMultiply# (xor# x y) (unW# multiple)
{-# inline combine# #-}

hash :: Addr# -> Span -> Hash
hash eob (Span (Pos (I# x)) (Pos (I# y))) = let
  start = plusAddr# eob (negateInt# x)
  len   = x -# y

  go :: Word# -> Addr# -> Int# -> Word#
  go hash ptr len = case len <# 8# of
    1# -> case len of
      0# -> hash
      _  -> combine# hash (indexPartialWord# len ptr)
    _  -> go (combine# hash (indexWordOffAddr# ptr 0#)) (plusAddr# ptr 8#) (len -# 8#)

  go' :: Word# -> Addr# -> Int# -> Word#
  go' hash ptr len = case len <# 8# of
    1# -> case len of
      0# -> hash
      _  -> combine# hash (indexPartialWord'# len ptr)
    _  -> go (combine# hash (indexWordOffAddr# ptr 0#)) (plusAddr# ptr 8#) (len -# 8#)

  in case y <# 8# of
    1# -> Hash (W# (go' (unW# salt) start len))
    _  -> Hash (W# (go  (unW# salt) start len))
{-# inline hash #-}

-- Buckets
--------------------------------------------------------------------------------

data Bucket = Empty | Cons Hash {-# unpack #-} Span Entry Bucket

CAN_IO(Bucket, LiftedRep, Bucket, x, CoeBucket)

foldlBucket :: (b -> Hash -> Span -> Entry -> b) -> b -> Bucket -> b
foldlBucket f acc b = go acc b where
  go acc Empty          = acc
  go acc (Cons h k v b) = let acc' = f acc h k v in go acc' b
{-# inline foldlBucket #-}

deleteFromBucket :: Addr# -> Int# -> Span -> Bucket -> (# Bucket, Int# #)
deleteFromBucket = go where
  go src size k topB = case topB of
    Empty -> (# Empty, size #)
    Cons h' k' v' b
      | eqSpan# src k k' -> let size' = size -# 1# in (# b, size' #)
      | otherwise ->
         let !(# !b', size' #) = go src size k b
         in if ptrEq b b' then (# topB, size #) else (# Cons h' k' v' b', size' #)

lookedFromBucket :: forall a. Addr# -> Span -> Bucket -> U.IO a -> (Entry -> U.IO a) -> U.IO a
lookedFromBucket src k b notfound found = go src k b where
  go src k Empty = notfound
  go src k (Cons h' k' v' b)
    | eqSpan# src k k' = found v'
    | otherwise       = go src k b
{-# inline lookedFromBucket #-}

modifyBucket :: Addr# -> Span -> (Entry -> Entry) -> Bucket -> Bucket
modifyBucket src k f b = go src k b where
  go src k Empty = Empty
  go src k this@(Cons h' k' v' b)
    | eqSpan# src k k' = Cons h' k' (f v') b
    | otherwise       =
      let b' = go src k b
      in if ptrEq b b' then this else Cons h' k' v' b'
{-# inline modifyBucket #-}

writeBucketAtIx :: Int -> Hash -> Span -> Entry -> Bucket -> Bucket
writeBucketAtIx 0 h k v (Cons _ _ _ b)    = Cons h k v b
writeBucketAtIx i h k v (Cons h' k' v' b) = Cons h' k' v' (writeBucketAtIx (i - 1) h k v b)
writeBucketAtIx i h k v _                 = undefined

insertToBucket :: Addr# -> Int# -> Hash -> Span -> Entry -> Bucket -> (# Bucket, Int# #)
insertToBucket src size h k ~v ~b = go src size 0 h k v b b where
  go :: Addr# -> Int# -> Int -> Hash -> Span -> Entry -> Bucket -> Bucket -> (# Bucket, Int# #)
  go src size i h k ~v ~topB b = case b of
    Empty               -> let size' = size +# 1#; c = Cons h k v topB in (# c, size' #)
    Cons h' k' v' b
      | eqSpan# src k k' -> let b = writeBucketAtIx i h k v topB in (# b, size #)
      | otherwise       -> go src size (i + 1) h k v topB b


-- SymTable
--------------------------------------------------------------------------------

newtype SymTable = SymTable
  (RUUU.Ref (RFF.Ref Int (Ptr Word8))
            (ALM.Array Bucket)
            (RL.Ref ForeignPtrContents))

CAN_IO(SymTable, UnliftedRep, MutableArrayArray# RealWorld,
       SymTable (RUUU.Ref (AUM.Array x)), CoeSymTable)

--------------------------------------------------------------------------------

initSlotsBits :: Int
initSlotsBits = 5
{-# inline initSlotsBits #-}

initSlots :: Int
initSlots = unsafeShiftL 1 initSlotsBits
{-# inline initSlots #-}

eob :: SymTable -> IO (Ptr Word8)
eob (SymTable tbl) = do
  ref <- RUUU.readFst tbl
  RFF.readSnd ref
{-# inline eob #-}

new'# :: Int -> Ptr Word8 -> ForeignPtrContents -> U.IO SymTable
new'# slots eob fpc = U.do
  ref        <- U.io $ RFF.new 0 eob
  fpcr       <- U.io $ RL.new fpc
  buckets    <- U.io $ ALM.new slots Empty
  table      <- U.io $ RUUU.new ref buckets fpcr
  U.pure $ SymTable table

new# :: Ptr Word8 -> ForeignPtrContents -> U.IO SymTable
new# = new'# initSlots
{-# inline new# #-}

new :: B.ByteString -> U.IO SymTable
new (B.BS (ForeignPtr base ftc) (I# len)) = new# (Ptr (plusAddr# base len)) ftc

lookup :: Span -> SymTable -> U.IO (UMaybe Entry)
lookup k (SymTable tbl) = U.do
  buckets  <- U.io $ RUUU.readSnd tbl
  Ptr src  <- U.io $ RFF.readSnd =<< RUUU.readFst tbl
  let bucketsSize = ALM.size buckets
      shift       = 64 - ctzInt bucketsSize
      h           = hash src k
      ix          = hashToInt (unsafeShiftR h shift)
  b <- U.io $ ALM.read buckets ix
  lookedFromBucket src k b (U.pure UNothing) (\a -> U.pure (UJust a))

delete# :: RFF.Ref Int (Ptr Word8) -> Int# -> Addr# -> ALM.Array Bucket
           -> Span -> Hash -> SymTable -> U.IO ()
delete# ref size src buckets k h (SymTable tbl) = U.do
  let bucketsSize = ALM.size buckets
      shift       = 64 - ctzInt bucketsSize
      ix          = hashToInt (unsafeShiftR h shift)
  b <- U.io $ ALM.read buckets ix
  let !(# !b', size' #) = deleteFromBucket src size k b
  U.io $ ALM.write buckets ix b'
  U.io $ RFF.writeFst ref (I# size')
  let downsize = unsafeShiftR bucketsSize 3
  if (I# size') <= downsize && downsize >= initSlots then
    unsafeResize (unsafeShiftR bucketsSize 1) (SymTable tbl)
  else
    U.pure ()

delete :: Span -> SymTable -> U.IO ()
delete k (SymTable tbl) = U.do
  ref      <- U.io $ RUUU.readFst tbl
  I# size  <- U.io $ RFF.readFst ref
  Ptr src  <- U.io $ RFF.readSnd ref
  buckets  <- U.io $ RUUU.readSnd tbl
  let h = hash src k
  delete# ref size src buckets k h (SymTable tbl)

unsafeResize :: Int -> SymTable -> U.IO ()
unsafeResize bucketsSize' (SymTable tbl) = U.do
  buckets  <- U.io $ RUUU.readSnd tbl
  buckets' <- U.io $ ALM.new bucketsSize' Empty
  let shift = 64 - ctzInt bucketsSize'
  U.io $ ALM.for buckets \b ->
    let go Empty          =
          pure ()
        go (Cons h k v b) = do
          ALM.modify' buckets' (hashToInt (unsafeShiftR h shift)) (Cons h k v)
          go b
    in go b
  U.io $ RUUU.writeSnd tbl buckets'
{-# noinline unsafeResize #-}

insert# :: RFF.Ref Int (Ptr Word8) -> Int# -> Addr# -> ALM.Array Bucket
        -> Span -> Hash -> Entry -> SymTable -> U.IO ()
insert# ref size src buckets k h v (SymTable tbl) = U.do
  let bucketsSize = ALM.size buckets
      shift       = 64 - ctzInt bucketsSize
      ix          = hashToInt (unsafeShiftR h shift)
  b <- U.io $ ALM.read buckets ix
  let !(# !b', !size' #) = insertToBucket src size h k v b
  U.io $ ALM.write buckets ix b'
  U.io $ RFF.writeFst ref (I# size')
  if I# size' >= unsafeShiftR bucketsSize 1 then
    unsafeResize (unsafeShiftL bucketsSize 1) (SymTable tbl)
  else
    U.pure ()

insert :: Span -> Entry -> SymTable -> U.IO ()
insert k v (SymTable tbl) = U.do
  ref      <- U.io $ RUUU.readFst tbl
  I# size  <- U.io $ RFF.readFst ref
  Ptr src  <- U.io $ RFF.readSnd ref
  buckets  <- U.io $ RUUU.readSnd tbl
  let h = hash src k
  insert# ref size src buckets k h v (SymTable tbl)

size :: SymTable -> U.IO Int
size (SymTable tbl) = U.io $ RFF.readFst =<< RUUU.readFst tbl
{-# inline size #-}

modify :: Span -> (Entry -> Entry) -> SymTable -> U.IO ()
modify k f (SymTable tbl) = U.do
  buckets <- U.io $ RUUU.readSnd tbl
  Ptr src <- U.io $ RFF.readSnd =<< RUUU.readFst tbl
  let bucketsSize = ALM.size buckets
      shift       = 64 - ctzInt bucketsSize
      h           = hash src k
      ix          = hashToInt (unsafeShiftR h shift)
  U.io $ ALM.modify' buckets ix (modifyBucket src k f)
{-# inline modify #-}

-- testing
--------------------------------------------------------------------------------

assocs :: SymTable -> IO [(Span, Entry)]
assocs (SymTable tbl) = do
  buckets <- ALM.unsafeFreeze =<< RUUU.readSnd tbl
  pure $ ALI.foldl'
    (\acc b -> foldlBucket (\acc _ k v -> (k, v):acc) acc b) [] buckets

buckets :: SymTable -> IO [[(Hash, Span, Entry)]]
buckets (SymTable tbl) = do
  buckets <- ALM.unsafeFreeze =<< RUUU.readSnd tbl
  pure $ ALI.foldl'
    (\acc b -> foldlBucket (\acc h k v -> (h, k, v):acc) [] b : acc) [] buckets

testHash :: B.ByteString -> Span -> Hash
testHash str s = runIO $ B.unsafeUseAsCString str \(Ptr addr) -> do
  let !(I# l) = B.length str
      eob = plusAddr# addr l
  pure $ hash eob s

testEqSpan :: B.ByteString -> Span -> Span -> Bool
testEqSpan str s s' = runIO $ B.unsafeUseAsCString str \(Ptr addr) -> do
  let !(I# l) = B.length str
      eob = plusAddr# addr l
  pure $ eqSpan# eob s s'

-- test = do
--   tbl <- U.toIO $ new "xxy"
--   U.toIO $ insert (Span (Pos 3) (Pos 2)) (Local 10 VU) tbl
--   U.toIO $ insert (Span (Pos 2) (Pos 1)) (Local 20 VU) tbl
--   mapM_ print =<< buckets tbl
