
module LvlSet where

{-|
Sets of De Bruijn levels. Currently this is just a 64 bit mask, and we limit
local scopes to 64 entries. This is checked in `Cxt.Extension`.
-}

import Common
import Data.Bits
import Data.Foldable (foldl')

newtype LvlSet = LvlSet Int deriving (Eq, Bits) via Int

instance Semigroup LvlSet where
  (<>) = (.|.)
  {-# inline (<>) #-}

instance Monoid LvlSet where
  mempty = LvlSet 0
  {-# inline mempty #-}

insert :: Lvl -> LvlSet -> LvlSet
insert (Lvl x) (LvlSet s) = LvlSet (unsafeShiftL 1 x .|. s)
{-# inline insert #-}

member :: Lvl -> LvlSet -> Bool
member (Lvl x) (LvlSet s) = (unsafeShiftL 1 x .&. s) /= 0
{-# inline member #-}

toList :: LvlSet -> [Lvl]
toList s = filter (`member` s) (coerce [0..63::Int])

fromList :: [Lvl] -> LvlSet
fromList = foldl' (flip insert) mempty

instance Show LvlSet where
  show = show . toList
