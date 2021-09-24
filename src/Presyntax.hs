{-# options_ghc -funbox-strict-fields #-}
{-# language UnboxedTuples, UnboxedSums #-}

module Presyntax where

import GHC.Exts
import Common

--------------------------------------------------------------------------------

-- data ArgInfo = NoName Icit | Named Span
data ArgInfo = ArgInfo# (# Int# | (# Int#, Int# #) #)

pattern NoName :: Icit -> ArgInfo
pattern NoName n <- ArgInfo# (# (\x -> Icit# (I# x)) -> n | #) where
  NoName (Icit# (I# n)) = ArgInfo# (# n | #)
pattern Named :: Span -> ArgInfo
pattern Named sp <- ArgInfo# (# | (\(# x, y #) -> Span (Pos (I# x)) (Pos (I# y))) -> sp #) where
  Named (Span (Pos (I# x)) (Pos (I# y))) = ArgInfo# (# | (# x , y #) #)
{-# complete NoName, Named #-}

instance Show ArgInfo where
  showsPrec n (NoName i) = showParen (n > 10) (showString "NoName " . showsPrec (n + 1) i)
  showsPrec n (Named sp) = showParen (n > 10) (showString "Name " . showsPrec (n + 1) sp)

--------------------------------------------------------------------------------

-- data Bind = DontBind | Bind Span
data Bind = Bind# (# (# #) | (# Int#, Int# #) #)

pattern DontBind :: Bind
pattern DontBind = Bind# (# (# #) | #)
pattern Bind :: Span -> Bind
pattern Bind sp <- Bind# (# | (\(# x, y #) -> Span (Pos (I# x)) (Pos (I# y))) -> sp #) where
  Bind (Span (Pos (I# x)) (Pos (I# y))) = Bind# (# | (# x, y #) #)
{-# complete Bind, DontBind #-}

instance Show Bind where
  show DontBind = "_"
  show (Bind x) = show x

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
