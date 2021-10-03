{-# language UnboxedTuples #-}

module Exceptions where

import GHC.Exts
import Common
-- import CoreTypes
import qualified Control.Exception as E

--------------------------------------------------------------------------------

data Exception = Exception



--------------------------------------------------------------------------------

data Exception#
  = forall e. E.Exception e => SomeException e
  | Exception# Exception

-- TODO: extremely dodgy, let's hope for the best!
catch :: a -> (Exception -> a) -> a
catch ~a k = runIO (IO \s ->
  catch# (\s -> let res = a in (# s, res #))
         (\e s -> case e of
             SomeException _ -> raise# e
             Exception# e    -> let a = k e in (# s, a #)) s)
{-# inline catch #-}

throw :: Exception -> a
throw e = raise# (Exception# e)
{-# inline throw #-}

-- | Converts all unhandled custom exceptions to standard exceptions.
standardize :: a -> a
standardize ~a = catch a (\_ -> error "unhandled exception")
{-# inline standardize #-}
