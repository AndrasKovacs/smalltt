{-# language UnboxedTuples #-}

module Exceptions where

import GHC.Exts
import qualified Control.Exception as E

import qualified UIO as U

--------------------------------------------------------------------------------

data Exception = Exception

--------------------------------------------------------------------------------

data Exception#
  = forall e. E.Exception e => SomeException e
  | Exception# Exception

catch :: forall a. U.CanIO a => U.IO a -> (Exception -> U.IO a) -> U.IO a
catch (U.IO f) k = U.IO \s ->
  case catch# (U.bind @a f (\a s -> (# s , a #)))
              (\e s -> case e of
                  SomeException _ -> raiseIO# e s
                  Exception# e    -> U.bind @a (U.unIO (k e)) (\a s -> (# s , a #)) s)
              s of
    (# s, a #) -> U.pure# @a a s
{-# inline catch #-}

throw :: forall a. U.CanIO a => Exception -> U.IO a
throw e = U.IO \s -> case raiseIO# e s of (# s, a #) -> U.pure# @a a s
{-# inline throw #-}

-- | Converts all unhandled custom exceptions to standard exceptions.
standardize :: forall a. U.CanIO a => U.IO a -> U.IO a
standardize ma = catch ma (\_ -> error "unhandled custom exception")
{-# inline standardize #-}
