
module LvlSet where

import Common
import Data.Bits
import Data.Foldable (foldl')

-- Lvl sets
--------------------------------------------------------------------------------

newtype LvlSet = LvlSet Int deriving (Eq, Bits) via Int

outOfRange :: HasCallStack => a
outOfRange = error "element out of range"
{-# noinline outOfRange #-}

instance Semigroup LvlSet where
  (<>) = (.|.)
  {-# inline (<>) #-}

instance Monoid LvlSet where
  mempty = LvlSet 0
  {-# inline mempty #-}

-- insert :: Lvl -> LvlSet -> LvlSet
-- insert (Lvl x) (LvlSet s)
--   | x > 63    = outOfRange
--   | otherwise = LvlSet (unsafeShiftL 1 x .|. s)
-- {-# inline insert #-}

insert :: Lvl -> LvlSet -> LvlSet
insert (Lvl x) (LvlSet s) = LvlSet (unsafeShiftL 1 x .|. s)
{-# inline insert #-}

single :: Lvl -> LvlSet
single x = insert x mempty
{-# inline single #-}

delete :: Lvl -> LvlSet -> LvlSet
delete (Lvl x) (LvlSet s)
  | x > 63    = outOfRange
  | otherwise = LvlSet (complement (unsafeShiftL 1 x) .&. s)
{-# inline delete #-}

set' :: Lvl -> Int -> LvlSet -> LvlSet
set' (Lvl x) b (LvlSet s) =
  LvlSet (unsafeShiftL b x .|. (complement (unsafeShiftL 1 x) .&. s))
{-# inline set' #-}

test' :: Lvl -> LvlSet -> Int
test' (Lvl x) (LvlSet s) = unsafeShiftR (unsafeShiftL 1 x .&. s) x
{-# inline test' #-}

set :: Lvl -> Bool -> LvlSet -> LvlSet
set (Lvl x) b (LvlSet s)
  | x > 63    = outOfRange
  | otherwise = LvlSet (unsafeShiftL (fromEnum b) x
                        .|. (complement (unsafeShiftL 1 x) .&. s))
{-# inline set #-}

member :: Lvl -> LvlSet -> Bool
member (Lvl x) (LvlSet s)
  | x > 63    = outOfRange
  | otherwise = (unsafeShiftL 1 x .&. s) /= 0
{-# inline member #-}

toList :: LvlSet -> [Lvl]
toList s = filter (`member` s) (coerce [0..63::Int])

fromList :: [Lvl] -> LvlSet
fromList = foldl' (flip insert) mempty

instance Show LvlSet where
  show = show . toList
