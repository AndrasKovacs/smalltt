{-# language UnboxedSums, NoStrict #-}

{-# options_ghc -Wno-unused-imports #-}

module Main where

import Data.Nullable
import Gauge
import Control.Exception
import Data.Bits

import GHC.Types
import GHC.Prim

data MyError = MyError deriving Show
instance Exception MyError

main :: IO ()
main = defaultMain [
  bench "test"  $ whnfAppIO (\(I# n) -> test  n) 1000001,
  bench "test'" $ whnfAppIO (\(I# n) -> test' n) 1000001
  ]

-- throw' e = putStrLn "throw" >> throw e
-- catch' f g = catch f (\x -> putStrLn "catch" >> g x)

test :: Int# -> IO ()
test n = case n of
  0# -> pure ()
  _  -> case andI# n 1# of
    0# -> test (n -# 1#) >> throw MyError
    _  -> catch (test (n -# 1#)) (\MyError -> pure ())

test' :: Int# -> IO ()
test' n = case n of
  0# -> pure ()
  _  -> case andI# n 1# of
    0# -> test' (n -# 1#)
    _  -> test' (n -# 1#)


-- test' :: Int -> IO ()
-- test' n | n == 0       = pure ()
--         | n .&. 1 == 0 = test' (n - 1)
--         | otherwise    = test' (n - 1)






{-

Error handling:
- Maybe
- Either
- Maybe and Either implemented as flat unboxable sigma-type
- Nullable
- IO exceptions
- Nullable combined with IORef for storing thrown error

Scenarios:
- Several scenarios from no throw, to lots of throws and lots of handling
-}

--------------------------------------------------------------------------------

-- data Maybe' a = Maybe' (# (# #) | a #)

-- pattern Nothing' :: Maybe' a
-- pattern Nothing' = Maybe' (# (# #) | #)

-- pattern Just' :: a -> Maybe' a
-- pattern Just' a = Maybe' (# | a #)
-- {-# complete Nothing', Just' #-}

-- instance Show a => Show (Maybe' a) where
--   showsPrec d Nothing' = ("Nothing'"++)
--   showsPrec d (Just' a) = showParen (d > 10) (("Just' "++).showsPrec 11 a)

-- instance Functor Maybe' where
--   fmap f = \case (Just' a) -> Just' (f a); _ -> Nothing'
--   {-# inline fmap #-}

-- instance Applicative Maybe' where
--   pure = Just'
--   {-# inline pure #-}
--   Just' f <*> Just' a = Just' (f a)
--   _       <*> _       = Nothing'
--   {-# inline (<*>) #-}

-- instance Monad Maybe' where
--   return = pure
--   {-# inline return #-}
--   Just' a >>= f = f a
--   _       >>= _ = Nothing'
--   {-# inline (>>=) #-}


--------------------------------------------------------------------------------

-- data Either' a b = Either' (# a | b #)

-- pattern Left' :: a -> Either' a b
-- pattern Left' a = Either' (# a | #)

-- pattern Right' :: b -> Either' a b
-- pattern Right' b = Either' (# | b #)
-- {-# complete Left', Right' #-}

-- instance (Show a, Show b) => Show (Either' a b) where
--   showsPrec d (Left' a)  = showParen (d > 10) (("Left' "++).showsPrec 11 a)
--   showsPrec d (Right' b) = showParen (d > 10) (("Right' "++).showsPrec 11 b)

-- instance Functor (Either' a) where
--   fmap f = \case Right' b -> Right' (f b); Left' a -> Left' a
--   {-# inline fmap #-}

-- instance Applicative (Either' a) where
--   pure = Right'
--   {-# inline pure #-}
--   Right' f <*> Right' a = Right' (f a)
--   Right' f <*> Left' a  = Left' a
--   Left' a  <*> _        = Left' a
--   {-# inline (<*>) #-}

-- instance Monad (Either' a) where
--   return = Right'
--   {-# inline return #-}
--   Right' a >>= f = f a
--   Left' a  >>= _ = Left' a
--   {-# inline (>>=) #-}

--------------------------------------------------------------------------------




-- test1M :: Int -> Int
-- test1M n = go 0 (replicate n (Just 100)) where
--   go !acc (Just x:xs) = go (acc + x) xs
--   go acc  (_     :xs) = go acc xs
--   go acc  _           = acc

-- test1M' :: Int -> Int
-- test1M' n = go 0 (replicate n (Just' 100)) where
--   go !acc (Just' x:xs) = go (acc + x) xs
--   go acc  (_     :xs)  = go acc xs
--   go acc  _           = acc

-- test1N :: Int -> Int
-- test1N n = go 0 (replicate n (Some 100)) where
--   go !acc (Some x:xs) = go (acc + x) xs
--   go acc  (_     :xs) = go acc xs
--   go acc  _           = acc

-- test1 :: Int -> Int
-- test1 n = go 0 (replicate n 100) where
--   go !acc (x:xs) = go (acc + x) xs
--   go acc  _      = acc

-- test1M :: Int -> Maybe Int
-- test1M n = go (Just n) n where
--   go (Just x) y | y == 0                = Just x
--                 | rem x y == 1000000000 = go Nothing (y - 1)
--                 | otherwise             = go (Just (x + y)) (y - 1)
--   go Nothing 0 = Just 0
--   go Nothing y = go (Just 100) (y - 1)

-- test1M' :: Int -> Maybe' Int
-- test1M' n = go (Just' n) n where
--   go (Just' x) y | y == 0                = Just' x
--                  | rem x y == 1000000000 = go Nothing' (y - 1)
--                  | otherwise             = go (Just' (x + y)) (y - 1)
--   go Nothing' 0 = Just' 0
--   go Nothing' y = go (Just' 100) (y - 1)

-- test1N :: Int -> Nullable Int
-- test1N n = go (Some n) n where
--   go (Some x) y | y == 0                = Some x
--                 | rem x y == 1000000000 = go Null (y - 1)
--                 | otherwise             = go (Some (x + y)) (y - 1)
--   go Null 0 = Some 0
--   go Null y = go (Some 100) (y - 1)

-- main :: IO ()
-- main = defaultMain [
--   bench "test1M"   $ whnf test1M  1000000,
--   bench "test1M'"  $ whnf test1M' 1000000,
--   bench "test1N"   $ whnf test1N  1000000
--   ]
