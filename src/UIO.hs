{-# language UnboxedTuples #-}

{-|
An alternative IO implementation, working around GHC's inability to unbox through standard IO.
-}

module UIO where

import Prelude hiding (
  Functor(..), (<$>), (<$), Applicative(..), (<*), (*>), Monad(..), IO)

import GHC.Exts
import qualified "primdata" IO as StdIO

import qualified Data.Ref.UUU    as RUUU
import qualified Data.Ref.FF     as RFF
import qualified Data.Ref.L      as RL
import qualified Data.Array.LM   as ALM
import qualified Data.Array.UM   as AUM

#include "deriveCanIO.h"

--------------------------------------------------------------------------------

type RW = State# RealWorld

type family RepRep a = (res :: RuntimeRep)
type family Rep a    = (res :: TYPE (RepRep a))

class CanIO a where
  bind  :: forall r (b :: TYPE r). (RW -> (# RW, Rep a #)) -> (a -> RW -> (# RW, b #)) -> RW -> (# RW, b #)
  pure# :: a -> RW -> (# RW, Rep a #)

newtype IO a = IO {unIO :: RW -> (# RW, Rep a #)}

type instance RepRep (a -> b) = LiftedRep
type instance Rep    (a -> b) = (a -> b)

instance CanIO (a -> b) where
  bind :: forall r (c :: TYPE r). (RW -> (# RW, (a -> b) #))
       -> ((a -> b) -> RW -> (# RW, c #)) -> RW -> (# RW, c #)
  bind f g s = case f s of (# s, x #) -> g x s

  pure#  :: (a -> b) -> RW -> (# RW, (a -> b) #)
  pure# x s = (# s, x #)
  {-# inline bind #-}
  {-# inline pure# #-}

infixl 1 >>=
(>>=) :: CanIO a => IO a -> (a -> IO b) -> IO b
(>>=) f g = IO (bind (unIO f) (\a -> unIO (g a)))
{-# inline (>>=) #-}

infixl 1 >>
(>>) :: CanIO a => IO a -> IO b -> IO b
(>>) ma mb = ma >>= \_ -> mb
{-# inline (>>) #-}

pure :: CanIO a => a -> IO a
pure a = IO (pure# a)
{-# inline pure #-}

infixl 4 <$>
(<$>) :: (CanIO a, CanIO b) => (a -> b) -> IO a -> IO b
(<$>) f ma = ma >>= \a -> pure $! f a
{-# inline (<$>) #-}

infixl 4 <$
(<$) :: (CanIO a, CanIO b) => a -> IO b -> IO a
(<$) a mb = (\_ -> a) <$> mb
{-# inline (<$) #-}

infixl 4 <*>
(<*>) :: (CanIO a, CanIO b) => IO (a -> b) -> IO a -> IO b
(<*>) mf ma = mf >>= \f -> ma >>= \a -> pure $! f a
{-# inline (<*>) #-}

io :: CanIO a => StdIO.IO a -> IO a
io (StdIO.IO f) = IO \s -> case f s of (# s, a #) -> pure# a s
{-# inline io #-}

toIO :: forall a. CanIO a => IO a -> StdIO.IO a
toIO (IO f) = StdIO.IO \s -> bind @a f (\a s -> (# s , a #)) s
{-# inline toIO #-}

run :: forall a. CanIO a => IO a -> a
run (IO f) = runRW# \s -> case bind @a f (\a s -> (# s, a #)) s of
  (# s, a #) -> a
{-# inline run #-}

fail :: String -> a
fail = error
{-# inline fail #-}

-- Instances
--------------------------------------------------------------------------------

CAN_IO(Int, IntRep, Int#, I# x, CoeInt)
CAN_IO(RUUU.Ref a b c, UnliftedRep, MutableArrayArray# RealWorld, RUUU.Ref (AUM.Array x), CoeRUU)
CAN_IO(RFF.Ref a b, UnliftedRep, MutableByteArray# RealWorld, RFF.Ref x, CoeRFF)
CAN_IO(RL.Ref a, UnliftedRep, MutVar# RealWorld a, RL.Ref x, CoeRL)
CAN_IO(ALM.Array a, UnliftedRep, MutableArray# RealWorld a, ALM.Array x, CoeALM)
CAN_IO(Ptr a, AddrRep, Addr#, Ptr x, CoePtr)

type instance RepRep () = TupleRep '[]
type instance Rep ()    = (# #)

instance CanIO () where
  bind  :: forall r (b :: TYPE r). (RW -> (# RW, (# #) #)) -> (() -> RW -> (# RW, b #)) -> RW -> (# RW, b #)
  bind f g s = case f s of (# s, _ #) -> g () s

  pure# :: () -> RW -> (# RW, (# #) #)
  pure# _ s = (# s, (# #) #)
  {-# inline bind #-}
  {-# inline pure# #-}