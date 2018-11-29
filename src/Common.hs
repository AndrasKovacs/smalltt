
module Common where

import Data.Bits
import Data.Text.Short (ShortText)
import Text.Megaparsec.Pos (SourcePos)
import Data.Nullable

import GHC.Types (IO(..))
import GHC.Magic (runRW#)

-- | Lazy boxed identity, used for controlled thunk creation.
data Box a = Box ~a

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
data Sum a b = Inl a | Inr b deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Values annotation with source position.
type Posed a = T2 SourcePos a

instance {-# OVERLAPS #-} Show a => Show (Posed a) where
  showsPrec d (T2 _ b) = showsPrec d b

-- | Names used for definitions and binders.
type Name = ShortText

-- | De Bruijn levels.
type Ix = Int

-- | Indices for metavariables. Consists of two 32-bit numbers, one is an index
--   for the top context, the other indexes the meta context at that entry.
newtype MetaIx = MkMetaIx Int deriving (Eq, Ord)

unpackMetaIx :: MetaIx -> (Int, Int)
unpackMetaIx (MkMetaIx n) = (unsafeShiftR n 32, n .&. 0xFFFFFFFF)
{-# inline unpackMetaIx #-}

pattern MetaIx :: Int -> Int -> MetaIx
pattern MetaIx i j <- (unpackMetaIx -> (i, j)) where
  MetaIx i j = MkMetaIx (unsafeShiftL i 32 .|. j)
{-# complete MetaIx #-}

instance Show MetaIx where show = show . unpackMetaIx

data Icit = Expl | Impl deriving (Eq)

icit :: Icit → a → a → a
icit Impl i e = i
icit Expl i e = e
{-# inline icit #-}

instance Show Icit where
  show Expl = "explicit"
  show Impl = "implicit"

runIO :: IO a -> a
runIO (IO f) = runRW# (\s -> case f s of (# _, a #) -> a)
{-# inline runIO #-}

data NameIcit = NI Name Icit deriving Show

data NameEnv = NENil | NESnoc NameEnv {-# unpack #-} Name deriving Show

-- TODO: Renaming can be simpler and probably faster.
data Renaming = RNil | RCons Ix Ix Renaming

lookupRen :: Renaming -> Ix -> Nullable Ix
lookupRen (RCons k v ren) x
  | x == k    = Some v
  | otherwise = lookupRen ren x
lookupRen RNil _ = Null

-- | TODO: length is pretty ugly.
lookupNameEnv :: NameEnv -> Ix -> Name
lookupNameEnv ns i = go ns (len ns - i - 1) where
  go NENil         _ = error "lookupNameEnv: impossible"
  go (NESnoc ns n) 0 = n
  go (NESnoc ns n) x = go ns (x - 1)

  len = go 0 where
    go l NENil         = l
    go l (NESnoc ns _) = go (l + 1) ns
