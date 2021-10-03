{-# language RebindableSyntax #-}

module MIO where

import GHC.Exts
import Data.Kind


-- newtype MIO r (a :: TYPE r) = MIO {runMIO :: forall s. State# s -> (#


-- forall s. State# s -> res s


-- proj1 :: forall s. res s -> State# s
-- proj2 :: forall s. res s -> a
-- mkRes :: forall s. State# s -> a -> res s

class Stateful a where
  data Pair s a
  proj1  :: Pair s a -> State# s
  proj2  :: Pair s a -> a
  mkPair :: State# s -> a -> Pair s a

instance Stateful Int where
  data Pair s Int = PairInt (State# s) Int
  proj1 (PairInt s _) = s
  proj2 (PairInt _ a) = a
  mkPair = PairInt
  {-# inline proj1 #-}
  {-# inline proj2 #-}
  {-# inline mkPair #-}

instance Stateful Word where
  data Pair s Word = PairWord (State# s) Word
  proj1 (PairWord s _) = s
  proj2 (PairWord _ a) = a
  mkPair = PairWord
  {-# inline proj1 #-}
  {-# inline proj2 #-}
  {-# inline mkPair #-}
