{-# language UnboxedTuples, UnboxedSums #-}

module Common (
    module Common
  , Span(..)
  , Pos(..)
  , Result(..)
  , coerce
  , TYPE
  , RuntimeRep(..)
  , unpackUTF8
  , packUTF8
  , HasCallStack) where

import Prelude hiding (Monad(..), Applicative(..), IO)
import qualified Prelude as P

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B

import Data.Bits
import Data.Flat
import Data.List
import Data.Time.Clock
import FlatParse.Stateful (Span(..), Pos(..), Result(..), unsafeSlice, unpackUTF8, packUTF8)
import GHC.Exts
import GHC.ForeignPtr
import GHC.Stack
import GHC.Int

import qualified UIO as U
import qualified UIO

#include "deriveCanIO.h"

-- debug printing, toggled by "debug" cabal flag
--------------------------------------------------------------------------------

-- define DEBUG

#ifdef DEBUG
type Dbg = HasCallStack

debug :: [String] -> UIO.IO ()
debug strs = U.io $ putStrLn (intercalate " | " strs ++ " END")

debugging :: UIO.IO () -> UIO.IO ()
debugging act = act
{-# inline debugging #-}
#else
type Dbg = () :: Constraint

debug :: [String] -> UIO.IO ()
debug strs = U.pure ()
{-# inline debug #-}

debugging :: UIO.IO () -> UIO.IO ()
debugging _ = U.pure ()
{-# inline debugging #-}
#endif

debug' :: [String] -> UIO.IO ()
debug' strs = U.io $ putStrLn (intercalate " | " strs ++ " END")

debugging' :: UIO.IO () -> UIO.IO ()
debugging' act = act
{-# inline debugging' #-}

--------------------------------------------------------------------------------

type Src = B.ByteString

uf :: Dbg => a
uf = undefined
{-# noinline uf #-}

infix 2 //
(//) :: a -> b -> (a, b)
a // b = (a, b)
{-# inline (//) #-}

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}

ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

ctzInt :: Int -> Int
ctzInt (I# n) = I# (word2Int# (ctz# (int2Word# n)))
{-# inline ctzInt #-}

infixl 0 $$!
($$!) :: (a -> b) -> a -> b
($$!) f x = f x
{-# inline ($$!) #-}

-- | Maximum number of allowed local binders.
maxLocals :: Lvl
maxLocals = 64; {-# inline maxLocals #-}

-- Unboxed Maybe
--------------------------------------------------------------------------------

data UMaybe a = UMaybe# (# a | (# #) #)
pattern UNothing :: UMaybe a
pattern UNothing = UMaybe# (# | (# #) #)
pattern UJust :: a -> UMaybe a
pattern UJust a <- UMaybe# (# a | #) where
  UJust !a = UMaybe# (# a | #)
{-# complete UNothing, UJust #-}

type UMaybeRepRep = SumRep [ LiftedRep, TupleRep '[]]
type UMaybeRep a  = (# a | (# #) #)
CAN_IO(UMaybe a, UMaybeRepRep, UMaybeRep a, UMaybe# x, CoeUMaybe)

uMaybe :: b -> (a -> b) -> UMaybe a -> b
uMaybe n j UNothing  = n
uMaybe n j (UJust a) = j a
{-# inline uMaybe #-}

-- | Returns 1 for `UJust`, 2 for `UNothing`.
tag :: UMaybe a -> Int
tag (UMaybe# x) = case unsafeCoerce# x :: (# Int#, () #) of
  (# t, _ #) -> I# t
{-# inline tag #-}

instance Eq a => Eq (UMaybe a) where
  UNothing == UNothing = True
  UJust a == UJust a' = a == a'
  _ == _ = False
  {-# inline (==) #-}

boxUMaybe :: UMaybe a -> Maybe a
boxUMaybe = uMaybe Nothing Just
{-# inline boxUMaybe #-}

instance Show a => Show (UMaybe a) where
  showsPrec n = showsPrec n . boxUMaybe

--------------------------------------------------------------------------------

-- | States for approximate scope/conversion checking.
newtype ConvState = ConvState# Int deriving Eq via Int
pattern CSRigid :: ConvState
pattern CSRigid = ConvState# 0
pattern CSFlex :: ConvState
pattern CSFlex = ConvState# 1
pattern CSFull :: ConvState
pattern CSFull = ConvState# 2
{-# complete CSRigid, CSFlex, CSFull #-}

instance Show ConvState where
  show CSRigid = "Rigid"
  show CSFlex  = "Flex"
  show CSFull  = "Full"

--------------------------------------------------------------------------------

newtype QuoteOption = QuoteOption# Int deriving Eq via Int
pattern UnfoldAll :: QuoteOption
pattern UnfoldAll  = QuoteOption# 0
pattern UnfoldFlex :: QuoteOption
pattern UnfoldFlex = QuoteOption# 1
pattern UnfoldNone :: QuoteOption
pattern UnfoldNone = QuoteOption# 2
{-# complete UnfoldAll, UnfoldFlex, UnfoldNone #-}

instance Show QuoteOption where
  show UnfoldAll  = "UnfoldAll"
  show UnfoldFlex = "UnfoldFlex"
  show UnfoldNone = "UnfoldNone"

--------------------------------------------------------------------------------

-- WARNING: EnvMask.looked depends on internals below!
newtype Icit = Icit# Int deriving Eq
pattern Impl :: Icit
pattern Impl = Icit# (-1)
pattern Expl :: Icit
pattern Expl = Icit# (-2)
{-# complete Impl, Expl #-}

CAN_IO(Icit, IntRep, Int#, Icit# (I# x), CoeIcit)

instance Show Icit where
  show Impl = "Impl"
  show Expl = "Expl"

icit :: Icit -> a -> a -> a
icit Impl x y = x
icit Expl x y = y
{-# inline icit #-}


-- De Bruijn
--------------------------------------------------------------------------------

newtype Ix = Ix {unIx :: Int}
  deriving (Eq, Ord, Show, Num, Enum, Bits) via Int

newtype Lvl = Lvl {unLvl :: Int}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Flat) via Int

lvlToInt8 :: Lvl -> Int8
lvlToInt8 (Lvl (I# x)) = I8# x
{-# inline lvlToInt8 #-}

int8ToLvl :: Int8 -> Lvl
int8ToLvl (I8# x) = Lvl (I# x)
{-# inline int8ToLvl #-}

CAN_IO(Lvl, IntRep, Int#, Lvl (I# x), CoeLvl)

newtype MetaVar = MkMetaVar Int
  deriving (Eq, Ord, Num, Flat) via Int

instance Show MetaVar where
  show (MkMetaVar x) = '?':show x

CAN_IO(MetaVar, IntRep, Int#, MkMetaVar (I# x), CoeMetaVar)

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl x) = Ix (envl - x - 1)
{-# inline lvlToIx #-}


-- Names
--------------------------------------------------------------------------------

-- data Name = NEmpty | NX | NSpan Span
data Name = Name# Int Int

unName# :: Name -> (# (# #) | (# #) | Span #)
unName# (Name# (-1) _) = (# (# #) | | #)
unName# (Name# (-2) _) = (# | (# #) | #)
unName# (Name# x y   ) = (# | | Span (Pos x) (Pos y) #)
{-# inline unName# #-}

pattern NEmpty :: Name
pattern NEmpty <- (unName# -> (# (# #) | | #))  where
  NEmpty = Name# (-1) 0

pattern NX :: Name
pattern NX <- (unName# -> (# | (# #) | #)) where
  NX = Name# (-2) 0

pattern NSpan :: Span -> Name
pattern NSpan sp <- (unName# -> (# | | sp #)) where
  NSpan (Span (Pos x) (Pos y)) = Name# x y
{-# complete NX, NEmpty, NSpan #-}

instance Show Name where
  showsPrec d NEmpty    = ('_':)
  showsPrec d NX        = ('x':)
  showsPrec d (NSpan x) = showsPrec d x

showSpan :: B.ByteString -> Span -> String
showSpan src s = unpackUTF8 $ unsafeSlice src s

showName :: B.ByteString -> Name -> String
showName src = \case
  NEmpty  -> "_"
  NX      -> "x"
  NSpan s -> showSpan src s


-- Binders
--------------------------------------------------------------------------------

-- data Bind = BEmpty | BSpan Span
data Bind = Bind# Int Int

unBind# :: Bind -> (# (# #) | Span #)
unBind# (Bind# (-1) _) = (# (# #) | #)
unBind# (Bind# x y   ) = (# | Span (Pos x) (Pos y) #)
{-# inline unBind# #-}

pattern BEmpty :: Bind
pattern BEmpty <- (unBind# -> (# (# #) | #))  where
  BEmpty = Bind# (-1) 0

pattern BSpan :: Span -> Bind
pattern BSpan sp <- (unBind# -> (# | sp #)) where
  BSpan (Span (Pos x) (Pos y)) = Bind# x y
{-# complete BEmpty, BSpan #-}

instance Show Bind where
  showsPrec d BEmpty    = ('_':)
  showsPrec d (BSpan x) = showsPrec d x

bind :: Bind -> Name
bind (Bind# x y) = Name# x y
{-# inline bind #-}

showBind :: B.ByteString -> Bind -> String
showBind src BEmpty    = "_"
showBind src (BSpan x) = showSpan src x


-- Span equality
--------------------------------------------------------------------------------

-- | Read between 1 and 7 bytes from an address.
indexPartialWord# :: Int# -> Addr# -> Word#
indexPartialWord# len addr =
  case indexWordOffAddr# addr 0# of
    w -> case uncheckedIShiftL# (8# -# len) 3# of
      sh -> case uncheckedShiftL# w sh of
        w -> uncheckedShiftRL# w sh
{-# inline indexPartialWord# #-}

-- little endian!
indexPartialWord'# :: Int# -> Addr# -> Word#
indexPartialWord'# = go 0## 0# where
  go acc shift 0# _  = acc
  go acc shift l ptr =
    go (or# acc (uncheckedShiftL# (indexWord8OffAddr# ptr 0#) shift))
       (shift +# 8#)
       (l -# 1#)
       (plusAddr# ptr 1#)

eqSpanGo :: Addr# -> Addr# -> Int# -> Int#
eqSpanGo p p' len = case len <# 8# of
  1# -> case len of
    0# -> 1#
    _  -> eqWord# (indexPartialWord# len p) (indexPartialWord# len p')
  _  -> case eqWord# (indexWordOffAddr# p 0#) (indexWordOffAddr# p' 0#) of
    1# -> eqSpanGo (plusAddr# p 8#) (plusAddr# p' 8#) (len -# 8#)
    _  -> 0#

eqSpanGo' :: Addr# -> Addr# -> Int# -> Int#
eqSpanGo' p p' len = case len <# 8# of
  1# -> case len of
    0# -> 1#
    _  -> case eqWord# (indexWord8OffAddr# p 0#) (indexWord8OffAddr# p' 0#) of
      1# -> eqSpanGo' (plusAddr# p 1#) (plusAddr# p' 1#) (len -# 1#)
      _  -> 0#
  _  -> case eqWord# (indexWordOffAddr# p 0#) (indexWordOffAddr# p' 0#) of
    1# -> eqSpanGo' (plusAddr# p 8#) (plusAddr# p' 8#) (len -# 8#)
    _  -> 0#

-- | Compare spans with the same base address.
eqSpan# :: Addr# -> Span -> Span -> Int#
eqSpan# _   s s' | s == s' = 1#
eqSpan# eob (Span (Pos (I# x)) (Pos (I# y))) (Span (Pos (I# x')) (Pos (I# y'))) = let
  len  = x -# y
  len' = x' -# y'
  in case len ==# len' of
    1# -> let
      start  = plusAddr# eob (negateInt# x )
      start' = plusAddr# eob (negateInt# x')
      in case orI# (y <# 8#) (y' <# 8#) of
        1# -> eqSpanGo' start start' len
        _  -> eqSpanGo  start start' len
    _  -> 0#
{-# inline eqSpan# #-}

-- | Compare spans with different base addresses.
eqBasedSpan# :: Addr# -> Span -> Addr# -> Span -> Int#
eqBasedSpan# eob  (Span (Pos (I# x))  (Pos (I# y)))
         eob' (Span (Pos (I# x')) (Pos (I# y'))) = let
  len  = x -# y
  len' = x' -# y'
  in case len ==# len' of
    1# -> let
      go p p' l = case l of
        0# -> 1#
        _  -> case eqWord# (indexWord8OffAddr# p 0#) (indexWord8OffAddr# p' 0#) of
          1# -> go (plusAddr# p 1#) (plusAddr# p' 1#) (l -# 1#)
          _  -> 0#
      in go (plusAddr# eob (negateInt# x))
            (plusAddr# eob' (negateInt# x')) len
    _  -> 0#

eqSpan :: B.ByteString -> Span -> Span -> Bool
eqSpan (B.BS (ForeignPtr base _) (I# len)) s s' =
  isTrue# (eqSpan# (plusAddr# base len) s s')
{-# inline eqSpan #-}

--------------------------------------------------------------------------------

-- | Time an IO computation. Result is forced to whnf.
timed :: P.IO a -> P.IO (a, NominalDiffTime)
timed a = do
  t1  <- getCurrentTime
  res <- a
  t2  <- getCurrentTime
  P.pure (res, diffUTCTime t2 t1)
{-# inline timed #-}

-- | Time a lazy pure value. Result is forced to whnf.
timedPure :: a -> P.IO (a, NominalDiffTime)
timedPure ~a = do
  t1  <- getCurrentTime
  let res = a
  t2  <- getCurrentTime
  P.pure (res, diffUTCTime t2 t1)
{-# noinline timedPure #-}
