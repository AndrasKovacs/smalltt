{-| Common data types and combinators. We declare a fair number of monomorphic
    types because otherwise fields cannot be unpacked.
-}

module Common where

import Data.Bits
import Data.Text.Short (ShortText)
import Text.Megaparsec.Pos (SourcePos)
import GHC.Types (IO(..))
import GHC.Magic (runRW#)

data Icit = Expl | Impl deriving (Eq, Show)

-- | If-then-else for 'Icit'.
icit :: Icit → a → a → a
icit Impl i e = i
icit Expl i e = e
{-# inline icit #-}

-- | Lazy boxed identity monad, used for controlled thunk creation.
data Box a = Box ~a

-- | Names used for definitions and binders.
type Name = ShortText

-- | De Bruijn indices. Used in syntax.
type Ix = Int

-- | De Bruijn levels. Used in values.
type Lvl = Int

data NameOrIcit = NOName {-# unpack #-} Name | NOImpl | NOExpl deriving Show

data Posed a = Posed SourcePos a

posOf (Posed p _) = p
unPosed (Posed _ a) = a
{-# inline posOf #-}
{-# inline unPosed #-}

instance Show a => Show (Posed a) where
  showsPrec d (Posed _ b) = showsPrec d b

data Named a = Named {-# unpack #-} Name a deriving Show
nameOf (Named x _) = x
unNamed (Named _ a) = a
{-# inline nameOf #-}
{-# inline unNamed #-}

-- | Indices for metavariables. Consists of two 32-bit numbers, one is an index
--   for the top context, the other indexes the meta context at that
--   entry. NOTE: the following only works on 64-bit systems. TODO: rewrite in
--   32-bit compatible way.
newtype Meta = MkMeta Int deriving (Eq, Ord)

unpackMeta :: Meta -> (Int, Int)
unpackMeta (MkMeta n) = (unsafeShiftR n 32, n .&. 0xFFFFFFFF)
{-# inline unpackMeta #-}

pattern Meta :: Int -> Int -> Meta
pattern Meta i j <- (unpackMeta -> (i, j)) where
  Meta i j = MkMeta (unsafeShiftL i 32 .|. j)
{-# complete Meta #-}

instance Show Meta where show = show . unpackMeta

data Names = NNil | NSnoc Names {-# unpack #-} Name deriving Show

-- | The same as 'unsafeDupablePerformIO'.
runIO :: IO a -> a
runIO (IO f) = runRW# (\s -> case f s of (# _, a #) -> a)
{-# inline runIO #-}

-- | A partial mapping from local levels to local levels.
data Renaming = RNil | RCons Lvl Lvl Renaming

-- | Returns (-1) on error.
applyRen :: Renaming -> Ix -> Ix
applyRen (RCons k v ren) x
  | x == k    = v
  | otherwise = applyRen ren x
applyRen RNil _ = (-1)


data Rigidity = Rigid | Flex deriving Show

meld :: Rigidity -> Rigidity -> Rigidity
meld Flex  _ = Flex
meld Rigid r = r
{-# inline meld #-}

-- | Strict pair type.
data T2 a b = T2 a b deriving (Eq, Show)

proj1 (T2 a _) = a
proj2 (T2 _ b) = b
{-# inline proj1 #-}
{-# inline proj2 #-}

data T3 a b c = T3 a b c deriving (Eq, Show)




-- data List a = LNil | LCons (List a) ~a
--   deriving (Eq, Show, Functor, Foldable, Traversable)

-- data List' a = LNil' | LCons' (List' a) a
--   deriving (Eq, Show, Functor, Foldable, Traversable)

-- data T3 a b c = T3 a b c deriving (Eq, Show)
-- data T4 a b c d = T4 a b c d deriving (Eq, Show)

-- Strict sum type.
-- data Sum a b = Inl a | Inr b deriving (Eq, Show, Functor, Foldable, Traversable)

--   -- | TODO: length is pretty ugly. Also, shadowed names are not distinguished in
--   --         output.
-- lookupNameEnv :: NameEnv -> Ix -> Name
-- lookupNameEnv ns i = go ns (len ns - i - 1) where
--   go NENil         _ = error "lookupNameEnv: impossible"

--   go (NESnoc ns n) 0 = case n of "" -> "_"; _ -> n
--   go (NESnoc ns n) x = go ns (x - 1)

--   len :: NameEnv -> Int
--   len = go 0 where
--     go l NENil         = l
--     go l (NESnoc ns _) = go (l + 1) ns
