{-# language UnboxedTuples #-}
{-# options_ghc -funbox-strict-fields #-}

module CoreTypes (
    Spine(..)
  , Closure(..)
  , Env(..)
  , Ty
  , VTy
  , Val(..)
  , Tm(..)
  , TopLevel(..)
  , topSpan
  , UnfoldHead
  , pattern UHTopVar
  , pattern UHSolved
  , Names(..)
  , prettyTm
  , showTm0
  ) where

import qualified Data.ByteString as B
import GHC.Exts

import qualified UIO
import Common
import EnvMask (EnvMask)
import qualified EnvMask as EM
import Data.Bits

#include "deriveCanIO.h"

data Spine
  = SId
  | SApp Spine Val Icit
  deriving Show

CAN_IO(Spine, LiftedRep, Spine, x, CoeSpine)

data Closure
  = Closure Env Tm
  deriving Show

CAN_IO2(Closure, TupleRep [ LiftedRep COMMA LiftedRep ], (# Env, Tm #), Closure x y, CoeClosure)

data Env
  = ENil
  | EDef Env ~Val
  deriving Show

type VTy = Val

data Val
  = VLocalVar Lvl Spine
  | VFlex MetaVar Spine
  | VUnfold UnfoldHead Spine ~Val
  | VLam Name Icit Closure
  | VPi Name Icit VTy Closure
  | VU
  | VIrrelevant
  deriving Show

CAN_IO(Val, LiftedRep, Val, x, CoeVal)

------------------------------------------------------------

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl ~Val
  | Let Span Tm Tm Tm
  | App Tm Tm Icit
  | Lam Name Icit Tm
  | InsertedMeta MetaVar EnvMask
  | Meta MetaVar
  | Pi Name Icit Ty Ty
  | Irrelevant
  | U
  deriving Show

CAN_IO(Tm, LiftedRep, Tm, x, CoeTm)

data TopLevel
  = Nil
  | Definition Span Tm Tm TopLevel
  deriving Show

CAN_IO(TopLevel, LiftedRep, TopLevel, x, CoeTopLevel)

topSpan :: Lvl -> TopLevel -> Span
topSpan 0 (Definition x _ _ _) = x
topSpan x (Definition _ _ _ top) = topSpan (x - 1) top
topSpan _ _ = impossible

------------------------------------------------------------

-- data UnfoldHead = UHTopVar Lvl ~Val | UHSolved MetaVar
data UnfoldHead = UnfoldHead# Int ~Val

instance Eq UnfoldHead where
  UnfoldHead# x _ == UnfoldHead# x' _ = x == x'
  {-# inline (==) #-}

unpackUH# :: UnfoldHead -> (# (# Lvl, Val #) | MetaVar #)
unpackUH# (UnfoldHead# x v) = case x .&. 1 of
  0 -> (# (# Lvl (unsafeShiftR x 1), v #) | #)
  _ -> (# | MkMetaVar (unsafeShiftR x 1) #)
{-# inline unpackUH# #-}

pattern UHTopVar :: Lvl -> Val -> UnfoldHead
pattern UHTopVar x v <- (unpackUH# -> (# (# x, v #) | #)) where
  UHTopVar (Lvl x) ~v = UnfoldHead# (unsafeShiftL x 1) v

pattern UHSolved :: MetaVar -> UnfoldHead
pattern UHSolved x <- (unpackUH# -> (# | x #)) where
  UHSolved (MkMetaVar x) = UnfoldHead# (unsafeShiftL x 1 + 1) undefined
{-# complete UHTopVar, UHSolved #-}

instance Show UnfoldHead where
  show (UHTopVar x _) = "(TopVar " ++ show x ++ ")"
  show (UHSolved x  ) = "(Solved " ++ show x ++ ")"


--------------------------------------------------------------------------------

data Names
  = NNil TopLevel
  | NCons Names {-# unpack #-} Name

showLocal :: B.ByteString -> Names -> Ix -> String
showLocal src (NCons _ x)  0 = showName src x
showLocal src (NCons ns _) l = showLocal src ns (l - 1)
showLocal _   _            _ = impossible

getTop :: Names -> TopLevel
getTop (NNil top)   = top
getTop (NCons ns _) = getTop ns

showTop :: B.ByteString -> Names -> Lvl -> String
showTop src ns x = showSpan src (topSpan x (getTop ns))


-- Pretty printing
--------------------------------------------------------------------------------

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> B.ByteString -> Names -> [String] -> Tm -> ShowS
prettyTm prec src ns = go prec where

  fresh :: [String] -> String -> String
  fresh ns "_" = "_"
  fresh ns x | elem x ns = fresh ns (x ++ "'")
             | otherwise = x

  freshN :: [String] -> Name -> String
  freshN ns = fresh ns . showName src

  freshS :: [String] -> Span -> String
  freshS ns = fresh ns . showSpan src

  bracket :: ShowS -> ShowS
  bracket ss = ('{':).ss.('}':)

  piBind ns x Expl a = showParen True ((x++) . (" : "++) . go letp ns a)
  piBind ns x Impl a = bracket        ((x++) . (" : "++) . go letp ns a)

  lamBind x Impl = bracket (x++)
  lamBind x Expl = (x++)

  goMask :: Int -> [String] -> MetaVar -> EM.EnvMask -> ShowS
  goMask p ns m mask = fst (go ns) where
    go :: [String] -> (ShowS, Lvl)
    go []     = (((show m ++) . ('?':)), 0)
    go (x:xs) = case go xs of
      (s, l) -> EM.looked l mask (s, l + 1) (\_ -> ((par p appp $ s . (' ':) . (x++)), l + 1))

  go :: Int -> [String] -> Tm -> ShowS
  go p ns = \case
    LocalVar x                 -> ((ns !! coerce x)++)

    App t u Expl               -> par p appp $ go appp ns t . (' ':) . go atomp ns u
    App t u Impl               -> par p appp $ go appp ns t . (' ':) . bracket (go letp ns u)

    Lam (freshN ns -> x) i t   -> par p letp $ ("λ "++) . lamBind x i . goLam (x:ns) t where
                                    goLam ns (Lam (freshN ns -> x) i t) = (' ':) . lamBind x i . goLam (x:ns) t
                                    goLam ns t                          = (". "++) . go letp ns t

    U                          -> ("U"++)

    Pi NEmpty Expl a b         -> par p pip $ go appp ns a . (" → "++) . go pip ("_":ns) b

    Pi (freshN ns -> x) i a b  -> par p pip $ piBind ns x i a . goPi (x:ns) b where
                                   goPi ns (Pi (freshN ns -> x) i a b)
                                     | x /= "_" = piBind ns x i a . goPi (x:ns) b
                                   goPi ns b = (" → "++) . go pip ns b

    Let (freshS ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n  = "++) . go letp ns t . (";\n\n"++) . go letp (x:ns) u

    Meta m                     -> (show m ++) . ('?':)
    InsertedMeta m mask        -> goMask p ns m mask
    TopVar x _                 -> uf -- showTop src _ _ -- (showSpan src (topSpan x top) ++)
    Irrelevant                 -> ("Irrelevant"++)


showTm :: Cxt -> Tm -> String
showTm cxt t = uf

showTm0 :: B.ByteString -> Tm -> String
showTm0 src t = prettyTm 0 src top [] t []
