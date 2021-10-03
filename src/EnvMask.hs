
module EnvMask where

import Common
import LvlSet (LvlSet(..))
import qualified LvlSet as LS
import Data.Foldable (foldl')

data EnvMask = EnvMask LvlSet LvlSet

insert :: Lvl -> Icit -> EnvMask -> EnvMask
insert x i (EnvMask xs is) = EnvMask (LS.insert x xs) (LS.set' x (coerce i) is)
{-# inline insert #-}

looked :: Lvl -> EnvMask -> a -> (Icit -> a) -> a
looked x (EnvMask xs is) notfound found
  | LS.member x xs = found (coerce (LS.test' x is))
  | otherwise      = notfound
{-# inline looked #-}

assocs :: EnvMask -> [(Lvl, Icit)]
assocs mask = do
  x <- [0..63::Lvl]
  looked x mask [] (\i -> pure (x, i))

empty :: EnvMask
empty = EnvMask mempty mempty
{-# inline empty #-}

instance Show EnvMask where
  show = show . assocs

fromList :: [(Lvl, Icit)] -> EnvMask
fromList = foldl' (\mask (!x, !i) -> insert x i mask) empty
