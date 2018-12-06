{-# language RankNTypes #-}

import Data.Time.Clock

timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1 <- getCurrentTime
  res <- a
  t2 <- getCurrentTime
  pure (res, diffUTCTime t2 t1)

newtype Nat = Nat (forall n. (n -> n) -> n -> n)

n2 = Nat $ \s z -> s (s z)
n5 = Nat $ \s z -> s (s (s (s (s z))))

mul :: Nat -> Nat -> Nat
mul (Nat a) (Nat b) = Nat (\s z -> a (b s) z)

n10   = mul n2 n5
n100  = mul n10 n10
n10k  = mul n100 n100
n10kb = mul n100 (mul n10 n10)
n1M   = mul n10k n100
n1Mb  = mul n100 n10k
n10M  = mul n1M n10
n10Mb = mul n10 n1M

forceNat :: Nat -> Bool
forceNat (Nat a) = a (\x -> x) True

computeTest = forceNat n10M

-- runs in 1.6s
main :: IO ()
main = do
  (_, t) <- timed $ print computeTest
  print t
