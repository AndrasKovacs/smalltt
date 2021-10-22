{-# options_ghc -funbox-strict-fields #-}
{-# language UnboxedSums, UnboxedTuples #-}

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
  showsPrec n (NoName i) = showParen (n > 10) (showString "NoName " . showsPrec 11 i)
  showsPrec n (Named sp) = showParen (n > 10) (showString "Named "  . showsPrec 11 sp)

--------------------------------------------------------------------------------

data TopLevel
  = Nil
  | Definition Span (UMaybe Tm) Tm TopLevel
  deriving Show

data Tm
  = Var Span
  | Let Pos Span (UMaybe Tm) Tm Tm
  | Pi Pos Bind Icit Tm Tm
  | Lam Pos Bind ArgInfo (UMaybe Tm) Tm
  | App Tm Tm ArgInfo
  | U Pos
  | Hole Pos
  deriving Show

-- | Length of top scope, used to sanity check parsing output.
topLen :: TopLevel -> Int
topLen = go 0 where
  go acc Nil = acc
  go acc (Definition _ _ _ t) = go (acc+1) t

span :: Tm -> Span
span t = Span (left t) (right t) where

  left = \case
    Var (Span l r) -> l
    Let l x ma t u -> l
    Pi l x i a b   -> l
    Lam l x i ma t -> l
    App t u i      -> left t
    U p            -> p
    Hole p         -> p

  right = \case
    Var (Span l r) -> r
    Let l x ma t u -> right u
    Pi l x i a b   -> right b
    Lam l x i ma t -> right t
    App t u i      -> right u
    U (Pos p)      -> Pos (p - 1)
    Hole p         -> p
