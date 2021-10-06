{-# options_ghc -funbox-strict-fields #-}
{-# language UnboxedSums #-}

module Presyntax where

import Common

--------------------------------------------------------------------------------

-- data ArgInfo = NoName Icit | Named Span
data ArgInfo = ArgInfo# Int Int

unArgInfo# :: ArgInfo -> (# Icit | Span #)
unArgInfo# (ArgInfo# x y)
  | x < 0     = (# Icit# x | #)
  | otherwise = (# | Span (Pos x) (Pos y) #)
{-# inline unArgInfo# #-}

pattern NoName :: Icit -> ArgInfo
pattern NoName i <- (unArgInfo# -> (# i | #)) where
  NoName (Icit# i) = ArgInfo# i 0

pattern Named :: Span -> ArgInfo
pattern Named sp <- (unArgInfo# -> (# | sp #)) where
  Named (Span (Pos x) (Pos y)) = ArgInfo# x y
{-# complete NoName, Named #-}

instance Show ArgInfo where
  showsPrec n (NoName i) = showParen (n > 10) (showString "NoName " . showsPrec (n + 1) i)
  showsPrec n (Named sp) = showParen (n > 10) (showString "Name " . showsPrec (n + 1) sp)

--------------------------------------------------------------------------------

data TopLevel
  = Nil
  | Definition Span (UMaybe Tm) Tm TopLevel
  deriving Show

data Tm
  = Var Span
  | Let Pos Span (UMaybe Tm) Tm Tm
  | Pi Pos Name Icit Tm Tm
  | Lam Pos Name ArgInfo (UMaybe Tm) Tm
  | App Tm Tm ArgInfo
  | U Pos
  | Hole Pos
  deriving Show

-- | Length of top scope, used to sanity check parsing output.
topLen :: TopLevel -> Int
topLen = go 0 where
  go acc Nil = acc
  go acc (Definition _ _ _ t) = go (acc+1) t
