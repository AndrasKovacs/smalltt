{-# language UnboxedTuples, UnboxedSums #-}

module Common (
    module Common
  , Span(..)
  , Pos(..)
  , Result(..)
  , coerce
  , HasCallStack
  , module IO ) where

import Data.Bits
import FlatParse.Stateful (Span(..), Pos(..), Result(..))
import GHC.Exts
import GHC.Stack
import IO

import qualified Data.ByteString      as B

--------------------------------------------------------------------------------

-- type Dbg = () :: Constraint
type Dbg = HasCallStack
type Src = B.ByteString

uf :: a
uf = undefined

impossible :: Dbg => a
impossible = error "impossible"
{-# inline impossible #-}

infixl 9 $$!
($$!) :: (a -> b) -> a -> b
($$!) f a = f $! a
{-# inline ($$!) #-}

infixl 4 <*!>
(<*!>) :: Monad m => m (a -> b) -> m a -> m b
(<*!>) mf ma = do
  f <- mf
  a <- ma
  pure $! f a
{-# inline (<*!>) #-}

infixl 4 <$!>
(<$!>) :: Monad f => (a -> b) -> f a -> f b
(<$!>) f fa = do
  a <- fa
  pure $! f a
{-# inline (<$!>) #-}

ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

ctzInt :: Int -> Int
ctzInt (I# n) = I# (word2Int# (ctz# (int2Word# n)))
{-# inline ctzInt #-}

-- Unboxed Maybe
--------------------------------------------------------------------------------

data UMaybe a = UMaybe# (# a | (# #) #)
pattern UNothing :: UMaybe a
pattern UNothing = UMaybe# (# | (# #) #)
pattern UJust :: a -> UMaybe a
pattern UJust a <- UMaybe# (# a | #) where
  UJust !a = UMaybe# (# a | #)
{-# complete UNothing, UJust #-}

uMaybe :: b -> (a -> b) -> UMaybe a -> b
uMaybe n j UNothing  = n
uMaybe n j (UJust a) = j a
{-# inline uMaybe #-}

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

-- States for approximate scope/conversion checking
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

newtype Icit = Icit# Int deriving Eq
pattern Impl :: Icit
pattern Impl = Icit# 0
pattern Expl :: Icit
pattern Expl = Icit# 1
{-# complete Impl, Expl #-}

instance Show Icit where
  show Impl = "Impl"
  show Expl = "Expl"

icit :: Icit -> a -> a -> a
icit Impl x y = x
icit Expl x y = y
{-# inline icit #-}

newtype Ix = Ix Int
  deriving (Eq, Ord, Show, Num, Enum, Bits) via Int

newtype Lvl = Lvl Int
  deriving (Eq, Ord, Show, Num, Enum, Bits) via Int

newtype MetaVar = MkMetaVar Int
  deriving (Eq, Ord, Show, Num) via Int

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl l) = Ix (envl - l - 1)
{-# inline lvlToIx #-}
