{-# language UnboxedTuples, OverloadedStrings #-}

{-|
A `SymTable` is a custom mutable hash table which is keyed by spans pointing to
a particular `ByteString`. Every `SymTable` is initialized from a `ByteString`.
The components of the `ByteString` are stored losslessly besides the table (but
in a different layout).

It is important that we get rid of unnecessary copying on common table
operations. A table is defined as a nesting of mutable references. Writing the
table size or modifying the underlying array of buckets requires no heap
allocation.
-}

module SymTable (
    SymTable(..)
  , new
  , SymTable.lookup
  , deleteWithHash
  , insertWithHash
  , updateWithHash
  , insert
  , delete
  , size
  , eob
  , hash
  , byteString
  , spanToString
  , spanToByteString
  , assocs
  , buckets
  -- , test
  , Entry(..)) where

import qualified FlatParse.Basic as FP
import qualified Data.Ref.UUU    as RUUU
import qualified Data.Ref.FFF    as RFFF
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

instance Show Entry where
  show (Local x _)     = "Loc " ++ show x
  show (Top x _ _ _ _) = "Top " ++ show x

-- Span hashing
--------------------------------------------------------------------------------

newtype Hash = Hash {unHash :: Word}
  deriving (Eq, Show, Ord, Num, Bits) via Word

CAN_IO(Hash, WordRep, Word#, Hash (W# x), CoeHash)

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

goHash :: Word# -> Addr# -> Int# -> Word#
goHash hash ptr len = case len <# 8# of
  1# -> case len of
    0# -> hash
    _  -> combine# hash (indexPartialWord# len ptr)
  _  -> goHash (combine# hash (indexWordOffAddr# ptr 0#)) (plusAddr# ptr 8#) (len -# 8#)

goHash' :: Word# -> Addr# -> Int# -> Word#
goHash' hash ptr len = case len <# 8# of
  1# -> case len of
    0# -> hash
    _  -> combine# hash (indexPartialWord'# len ptr)
  _  -> goHash' (combine# hash (indexWordOffAddr# ptr 0#)) (plusAddr# ptr 8#) (len -# 8#)

hash# :: Addr# -> Span -> Hash
hash# eob (Span (Pos (I# x)) (Pos (I# y))) = let
  start = plusAddr# eob (negateInt# x)
  len   = x -# y
  in case y <# 8# of
    1# -> Hash (W# (goHash' (unW# salt) start len))
    _  -> Hash (W# (goHash (unW# salt) start len))
{-# inline hash# #-}

hash :: SymTable -> Span -> U.IO Hash
hash (SymTable tbl) k = U.do
  Ptr src  <- U.io $ RFFF.readSnd =<< RUUU.readFst tbl
  U.pure (hash# src k)
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

deleteFromBucket :: Addr# -> Span -> Bucket -> (# Bucket, (# Entry | (# #) #) #)
deleteFromBucket = go where
  go src k topB = case topB of
    Empty -> (# Empty, (# | (# #) #) #)
    Cons h' k' v' b
      | 1# <- eqSpan# src k k' -> (# b, (# v' | #) #)
      | otherwise ->
         let !(# !b', del #) = go src k b
         in if ptrEq b b' then (# topB, del #) else (# Cons h' k' v' b', del #)

lookupBucket :: Addr# -> Span -> Bucket -> (# Entry | (# #) #)
lookupBucket src k = \case
  Empty -> (# | (# #) #)
  Cons h' k' v' b
    | 1# <- eqSpan# src k k' -> (# v' | #)
    | otherwise              -> lookupBucket src k b

writeBucketAtIx :: Int -> Hash -> Span -> Entry -> Bucket -> Bucket
writeBucketAtIx i h k v e = case (,) $$! i $$! e of
  (0, Cons _ _ _ b   ) -> Cons h k v b
  (i, Cons h' k' v' b) -> Cons h' k' v' (writeBucketAtIx (i - 1) h k v b)
  (_, _              ) -> undefined

insertToBucket
  :: Addr# -> Hash -> Span -> Entry -> Bucket -> (# Bucket, (# Entry | (# #) #) #)
insertToBucket src h k ~v ~b = go src 0 h k v b b where
  go :: Addr# -> Int -> Hash -> Span -> Entry -> Bucket -> Bucket -> (# Bucket, (# Entry | (# #) #) #)
  go src i h k ~v ~topB b = case b of
    Empty                -> let c = Cons h k v topB in (# c, (# | (# #) #) #)
    Cons h' k' v' b
      | 1# <- eqSpan# src k k' -> let b = writeBucketAtIx i h k v topB in (# b, (# v' | #) #)
      | otherwise              -> go src (i + 1) h k v topB b

-- SymTable
--------------------------------------------------------------------------------

newtype SymTable = SymTable
  (RUUU.Ref (RFFF.Ref Int (Ptr Word8) Int)
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
  RFFF.readSnd ref
{-# inline eob #-}

new'# :: Int -> Ptr Word8 -> Int -> ForeignPtrContents -> U.IO SymTable
new'# slots eob len fpc = U.do
  ref        <- U.io $ RFFF.new 0 eob len
  fpcr       <- U.io $ RL.new fpc
  buckets    <- U.io $ ALM.new slots Empty
  table      <- U.io $ RUUU.new ref buckets fpcr
  U.pure $ SymTable table

new# :: Ptr Word8 -> Int -> ForeignPtrContents -> U.IO SymTable
new# = new'# initSlots
{-# inline new# #-}

new :: B.ByteString -> U.IO SymTable
new (B.BS (ForeignPtr base ftc) (I# len)) =
  new# (Ptr (plusAddr# base len)) (I# len) ftc

lookup :: Span -> SymTable -> U.IO (UMaybe Entry)
lookup k (SymTable tbl) = U.do
  buckets  <- U.io $ RUUU.readSnd tbl
  Ptr src  <- U.io $ RFFF.readSnd =<< RUUU.readFst tbl
  let bucketsSize = ALM.size buckets
      shift       = 64 - ctzInt bucketsSize
      h           = hash# src k
      ix          = hashToInt (unsafeShiftR h shift)
  b <- U.io $ ALM.read buckets ix
  U.pure (UMaybe# (lookupBucket src k b))

resize# :: Int -> SymTable -> U.IO ()
resize# bucketsSize' (SymTable tbl) = U.do
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
{-# noinline resize# #-}

deleteWithHash :: Span -> Hash -> SymTable -> U.IO (UMaybe Entry)
deleteWithHash k h (SymTable tbl) = U.do
  ref      <- U.io $ RUUU.readFst tbl
  I# size  <- U.io $ RFFF.readFst ref
  Ptr src  <- U.io $ RFFF.readSnd ref
  buckets  <- U.io $ RUUU.readSnd tbl
  let bucketsSize = ALM.size buckets
      shift       = 64 - ctzInt bucketsSize
      ix          = hashToInt (unsafeShiftR h shift)
  b <- U.io $ ALM.read buckets ix
  let !(# !b', old #) = deleteFromBucket src k b
  let size' = I# size + tag (UMaybe# old) - 1
  U.io $ ALM.write buckets ix b'
  U.io $ RFFF.writeFst ref size'
  let downsize = unsafeShiftR bucketsSize 3
  U.when (size' <= downsize && downsize >= initSlots) $
    resize# (unsafeShiftR bucketsSize 1) (SymTable tbl)
  U.pure (UMaybe# old)

insertWithHash :: Span -> Hash -> Entry -> SymTable -> U.IO (UMaybe Entry)
insertWithHash k h v (SymTable tbl) = U.do
  ref      <- U.io $ RUUU.readFst tbl
  I# size  <- U.io $ RFFF.readFst ref
  Ptr src  <- U.io $ RFFF.readSnd ref
  buckets  <- U.io $ RUUU.readSnd tbl
  let bucketsSize = ALM.size buckets
      shift       = 64 - ctzInt bucketsSize
      ix          = hashToInt (unsafeShiftR h shift)
  b <- U.io $ ALM.read buckets ix
  let !(# b', old #) = insertToBucket src h k v b
  let size' = I# size + tag (UMaybe# old) - 1
  U.io $ ALM.write buckets ix b'
  U.io $ RFFF.writeFst ref size'
  U.when (size' >= unsafeShiftR bucketsSize 1) $
    resize# (unsafeShiftL bucketsSize 1) (SymTable tbl)
  U.pure (UMaybe# old)

updateWithHash :: Span -> Hash -> UMaybe Entry -> SymTable -> U.IO (UMaybe Entry)
updateWithHash k h mv tbl = case mv of
  UNothing -> deleteWithHash k h tbl
  UJust v  -> insertWithHash k h v tbl
{-# inline updateWithHash #-}

insert :: Span -> Entry -> SymTable -> U.IO (UMaybe Entry)
insert k v tbl = U.do
  h <- hash tbl k
  insertWithHash k h v tbl

delete :: Span -> SymTable -> U.IO (UMaybe Entry)
delete k tbl = U.do
  h <- hash tbl k
  deleteWithHash k h tbl

size :: SymTable -> U.IO Int
size (SymTable tbl) = U.io $ RFFF.readFst =<< RUUU.readFst tbl
{-# inline size #-}

byteString :: SymTable -> B.ByteString
byteString (SymTable tbl) = runIO do
  ref     <- RUUU.readFst tbl
  Ptr end <- RFFF.readSnd ref
  I# len  <- RFFF.readThd ref
  fptr    <- RL.read =<< RUUU.readThd tbl
  let start = plusAddr# end (negateInt# len)
  pure $ B.BS (ForeignPtr start fptr) (I# len)

spanToByteString :: SymTable -> Span -> B.ByteString
spanToByteString (SymTable tbl) (Span (Pos (I# x)) (Pos (I# y))) = runIO do
  Ptr end <- RFFF.readSnd =<< RUUU.readFst tbl
  fptr    <- RL.read =<< RUUU.readThd tbl
  let start = plusAddr# end (negateInt# x)
      len   = x -# y
  pure $ B.BS (ForeignPtr start fptr) (I# len)

spanToString :: SymTable -> Span -> String
spanToString tbl s = FP.unpackUTF8 (spanToByteString tbl s)


-- testing
--------------------------------------------------------------------------------


assocs :: SymTable -> IO [(String, Entry)]
assocs stbl@(SymTable tbl) = do
  buckets <- ALM.unsafeFreeze =<< RUUU.readSnd tbl
  pure $ ALI.foldl'
    (\acc b -> foldlBucket
      (\acc _ k v -> (spanToString stbl k, v):acc) acc b)
      [] buckets

buckets :: SymTable -> IO [[(Hash, String, Entry)]]
buckets stbl@(SymTable tbl) = do
  buckets <- ALM.unsafeFreeze =<< RUUU.readSnd tbl
  pure $ ALI.foldl'
    (\acc b -> foldlBucket
        (\acc h k v -> (h, spanToString stbl k, v):acc) [] b : acc)
        [] buckets

testHash :: B.ByteString -> Span -> Hash
testHash str s = runIO $ B.unsafeUseAsCString str \(Ptr addr) -> do
  let !(I# l) = B.length str
      eob = plusAddr# addr l
  pure $ hash# eob s

testEqSpan :: B.ByteString -> Span -> Span -> Bool
testEqSpan str s s' = runIO $ B.unsafeUseAsCString str \(Ptr addr) -> do
  let !(I# l) = B.length str
      eob = plusAddr# addr l
  pure $ isTrue# (eqSpan# eob s s')

-- test = do
--   tbl <- U.toIO $ new ""
--   U.toIO $ insert (Span (Pos 4) (Pos 2)) (Local 10 VU) tbl
--   U.toIO $ insert (Span (Pos 2) (Pos 0)) (Local 20 VU) tbl
--   mapM_ print =<< buckets tbl
