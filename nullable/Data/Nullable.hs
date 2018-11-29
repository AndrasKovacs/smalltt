
{-|
A hacky minimum-overhead error representation, intended for monomorphic
usage. An error value is represented as a pointer to a static object,
while a non-error value is a regular GHC pointer. Note: you shouldn't
put a `Nullable` in `Nullable`, because two layers of errors immediately
collapse; hence my "intended for monomorphic usage".
-}

module Data.Nullable (
    Nullable
  , pattern Null
  , pattern Some
  , nullable
  , isSome
  , isNull
  ) where

import Control.Applicative
import Control.Monad
import GHC.Prim
import GHC.Types
import GHC.Read
import GHC.Show
import Text.ParserCombinators.ReadPrec
import qualified Text.Read.Lex as L

type role Nullable nominal
newtype Nullable (a :: *) = Nullable Any

data Null# = Null#

null# :: Null#
null# = Null#
{-# noinline null# #-}

isNull# :: Nullable a -> Int#
isNull# (Nullable !any) = reallyUnsafePtrEquality# (unsafeCoerce# any) null#
{-# inline isNull# #-}

isSome# :: Nullable a -> (# Int#, a #)
isSome# (Nullable !any) =
  (# reallyUnsafePtrEquality# (unsafeCoerce# any) null#, unsafeCoerce# any #)
{-# inline isSome# #-}

pattern Null :: Nullable a
pattern Null <- (isNull# -> 1#) where
  Null = (unsafeCoerce# null# :: Nullable a)

pattern Some :: a -> Nullable a
pattern Some a <- (isSome# -> (# 0#, a #)) where
  Some (a :: a) = (unsafeCoerce# a :: Nullable a)
{-# complete Null, Some #-}

nullable :: b -> (a -> b) -> Nullable a -> b
nullable b f (Some a) = f a
nullable b f _        = b
{-# inline nullable #-}

isSome :: Nullable a -> Bool
isSome Some{} = True
isSome _      = False
{-# inline isSome #-}

isNull :: Nullable a -> Bool
isNull Null = True
isNull _    = False
{-# inline isNull #-}

instance Functor Nullable where
  fmap f (Some a) = Some (f a)
  fmap f x        = unsafeCoerce# x
  {-# inline fmap #-}

instance Foldable Nullable where
  foldr f z (Some a) = f a z
  foldr f z _        = z
  {-# inline foldr #-}

  foldl f = foldr (flip f)

  foldMap f (Some a) = f a
  foldMap f _        = mempty
  {-# inline foldMap #-}

instance Traversable Nullable where
  traverse f (Some a) = Some <$> f a
  traverse f x        = pure (unsafeCoerce# x)
  {-# inline traverse #-}

instance Eq a => Eq (Nullable a) where
  Some a == Some b = a == b
  _      == _      = False
  {-# inline (==) #-}

instance Semigroup a => Semigroup (Nullable a) where
  Some a <> Some b = Some (a <> b)
  Null   <> b      = b
  a      <> _      = a
  {-# inline (<>) #-}

instance Semigroup a => Monoid (Nullable a) where
  mempty = Null
  Some m1 `mappend` Some m2 = Some (m1 <> m2)
  Null    `mappend` m       = m
  m       `mappend` _       = m
  {-# inline mempty #-}
  {-# inline mappend #-}

instance Ord a => Ord (Nullable a) where
  compare (Some a) (Some b) = compare a b
  compare Null  (Some _) = LT
  compare (Some _) Null  = GT
  compare _        _     = EQ
  {-# inline compare #-}

instance Show a => Show (Nullable a) where
    showsPrec p (Some a) s =
      (showParen (p > appPrec) $
        showString "Some " .
        showsPrec appPrec1 a) s
    showsPrec _ _ s = showString "Null" s


instance Read a => Read (Nullable a) where
  readPrec =
    parens
    (do expectP (L.Ident "Null")
        return Null
     +++
     prec appPrec (
        do expectP (L.Ident "Some")
           x <- step readPrec
           return (Some x))
    )

instance Applicative Nullable where
    pure = Some

    Some f  <*> m       = fmap f m
    x       <*> _m      = unsafeCoerce# x

    Some _m1 *> m2      = m2
    x        *> _m2     = unsafeCoerce# x
    {-# inline pure #-}
    {-# inline (<*>) #-}
    {-# inline (*>) #-}

instance  Monad Nullable  where
    (Some x) >>= k      = k x
    x        >>= _      = unsafeCoerce# x

    (>>) = (*>)

    return              = Some
    fail _              = Null
    {-# inline (>>=) #-}
    {-# inline (>>) #-}
    {-# inline return #-}

instance Alternative Nullable where
    empty = Null
    Null <|> r = r
    l    <|> _ = l
    {-# inline empty #-}
    {-# inline (<|>) #-}

instance MonadPlus Nullable
