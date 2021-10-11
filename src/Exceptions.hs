{-# language UnboxedTuples #-}

module Exceptions where

import GHC.Exts
import qualified Control.Exception as E

import qualified UIO as U
import IO

--------------------------------------------------------------------------------

data Exception = CantUnify | Exception | CSFlexSolution

--------------------------------------------------------------------------------

data Exception#
  = forall e. E.Exception e => SomeException e
  | Exception# Exception

catchIO :: forall a. IO a -> (Exception -> IO a) -> IO a
catchIO (IO f) k = IO (catch# f (\case e@(SomeException _) -> raiseIO# e
                                       Exception# e        -> unIO (k e)))
{-# inline catchIO #-}

catch :: forall a. U.CanIO a => U.IO a -> (Exception -> U.IO a) -> U.IO a
catch ma k = U.io $ catchIO (U.toIO ma) (\e -> U.toIO (k e))
{-# inline catch #-}

throw :: forall a. U.CanIO a => Exception -> U.IO a
throw e = U.IO \s -> case raiseIO# (Exception# e) s of (# s, a #) -> U.pure# @a a s
{-# inline throw #-}

-- | Converts all unhandled custom exceptions to standard exceptions.
standardize :: forall a. U.CanIO a => U.IO a -> U.IO a
standardize ma = catch ma (\_ -> error "unhandled custom exception")
{-# inline standardize #-}
