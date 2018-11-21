
module Common where

import Data.Bits
import Data.Text.Short (ShortText)
import Text.Megaparsec.Pos (SourcePos)

import GHC.Types (IO(..))
import GHC.Magic (runRW#)

-- | Strict pair type.
data T2 a b = T2 a b deriving (Eq, Show)

proj1 (T2 a _) = a
proj2 (T2 _ b) = b
{-# inline proj1 #-}
{-# inline proj2 #-}

data T3 a b c = T3 a b c deriving (Eq, Show)
data T4 a b c d = T4 a b c d deriving (Eq, Show)
data T5 a b c d e = T5 a b c d deriving (Eq, Show)

-- | Strict sum type.
data Sum a b = Inl a | Inr b deriving (Eq, Show)

-- | Values annotation with source position.
type Posed a = T2 SourcePos a

-- | Names used for definitions and binders.
type Name = ShortText

-- | De Bruijn levels.
type Ix = Int

-- | Indices for metavariables. Consists of two 32-bit numbers, one is an index
--   for the top context, the other indexes the meta context at that entry.
newtype MetaIx = MkMetaIx Int deriving (Eq)

unpack :: MetaIx -> (Int, Int)
unpack (MkMetaIx n) = (unsafeShiftR n 32, n .&. 0xFFFFFFFF)
{-# inline unpack #-}

pattern MetaIx :: Int -> Int -> MetaIx
pattern MetaIx i j <- (unpack -> (i, j)) where
  MetaIx i j = MkMetaIx (unsafeShiftL i 32 .|. j)
{-# complete MetaIx #-}

instance Show MetaIx where show = show . unpack

data Icit = Expl | Impl deriving (Eq)

instance Show Icit where
  show Expl = "explicit"
  show Impl = "implicit"

runIO :: IO a -> a
runIO (IO f) = runRW# (\s -> case f s of (# _, a #) -> a)
{-# inline runIO #-}
