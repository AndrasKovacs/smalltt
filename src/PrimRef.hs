
module PrimRef (
    PrimRef(..)
  , type IOPrimRef
  , PrimRef.read
  , new
  , write
  , modify
  ) where

import Control.Monad.Primitive
import Data.Primitive.Types
import Data.Primitive.UnliftedArray (PrimUnlifted)
import qualified PrimArray as PA
import GHC.Prim

newtype PrimRef s a = PrimRef (PA.MArray s a) deriving (PrimUnlifted)
type IOPrimRef = PrimRef RealWorld

read :: forall a m. (PrimMonad m, Prim a) => PrimRef (PrimState m) a -> m a
read ref = PA.read (coerce ref) 0
{-# inline read #-}

write
  :: forall a m.
     (PrimMonad m, Prim a) =>
     PrimRef (PrimState m) a -> a -> m ()
write ref a = PA.write (coerce ref) 0 a
{-# inline write #-}

new
  :: forall a m.
     (PrimMonad m, Prim a) => a -> m (PrimRef (PrimState m) a)
new a = do
  arr <- PA.new 1
  PA.write arr 0 a
  pure (coerce arr)
{-# inline new #-}

modify ::
  forall a m.
  (PrimMonad m, Prim a) => PrimRef (PrimState m) a -> (a -> a) -> m ()
modify ref f = do
  a <- PrimRef.read ref
  write ref (f a)
{-# inline modify #-}
