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
  , TopInfo
  , TopVals
  , TopEntry(..)
  , UnfoldHead
  , pattern UHTopVar
  , pattern UHSolved
  , G(..)
  , GTy
  , gjoin
  , eqUH
  , Names(..)
  , prettyTm
  , showTm0
  ) where

import qualified Data.ByteString as B
import qualified Data.Array.LM   as ALM
import IO (runIO)
import GHC.Exts

import qualified UIO
import qualified LvlSet as LS
import Common
import Data.Bits

#include "deriveCanIO.h"

--------------------------------------------------------------------------------

data Spine
  = SId
  | SApp Spine Val Icit
  deriving Show

CAN_IO(Spine, LiftedRep, Spine, x, CoeSpine)

data Closure
  = Closure Env Tm
  deriving Show

CAN_IO2(Closure, LiftedRep, LiftedRep, Env, Tm, Closure x y, CoeClosure)

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

type Ty = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl
  | Let Span Tm Tm Tm
  | App Tm Tm Icit
  | Lam Name Icit Tm
  | InsertedMeta MetaVar LS.LvlSet
  | Meta MetaVar
  | Pi Name Icit Ty Ty
  | Irrelevant
  | U
  deriving Show

CAN_IO(Tm, LiftedRep, Tm, x, CoeTm)

data G   = G {g1, g2 :: ~Val}
type GTy = G

gjoin :: Val -> G
gjoin ~v = G v v
{-# inline gjoin #-}

CAN_IO2(G, LiftedRep, LiftedRep, Val, Val, G x y, CoeG)

------------------------------------------------------------

-- data UnfoldHead = UHTopVar Lvl | UHSolved MetaVar
data UnfoldHead = UnfoldHead# Int

eqUH :: UnfoldHead -> UnfoldHead -> Bool
eqUH (UnfoldHead# x) (UnfoldHead# x') = x == x'
{-# inline eqUH #-}

unpackUH# :: UnfoldHead -> (# Lvl | MetaVar #)
unpackUH# (UnfoldHead# x) = case x .&. 1 of
  0 -> (# Lvl (unsafeShiftR x 1) | #)
  _ -> (# | MkMetaVar (unsafeShiftR x 1) #)
{-# inline unpackUH# #-}

pattern UHTopVar :: Lvl -> UnfoldHead
pattern UHTopVar x <- (unpackUH# -> (# x | #)) where
  UHTopVar (Lvl x) = UnfoldHead# (unsafeShiftL x 1)

pattern UHSolved :: MetaVar -> UnfoldHead
pattern UHSolved x <- (unpackUH# -> (# | x #)) where
  UHSolved (MkMetaVar x) = UnfoldHead# (unsafeShiftL x 1 + 1)
{-# complete UHTopVar, UHSolved #-}

instance Show UnfoldHead where
  show (UHTopVar x) = "(TopVar " ++ show x ++ ")"
  show (UHSolved x) = "(Solved " ++ show x ++ ")"


--------------------------------------------------------------------------------

data TopEntry = TopEntry {-# unpack #-} Span Tm Tm  -- name, type, definition

CAN_IO(TopEntry, LiftedRep, TopEntry, x, CoeTopEntry)

type TopInfo = ALM.Array TopEntry
type TopVals = ALM.Array Val

--------------------------------------------------------------------------------

-- | Data structure holding enough name information to pretty print things.
--   This is a bit peculiar, because it is optimized for fast extension during
--   elaboration. The top env is stored at the end, and we can extend it with
--   local names with just single NCons.
data Names
  = NNil TopInfo
  | NCons Names {-# unpack #-} Name

showLocal :: B.ByteString -> Names -> Ix -> String
showLocal src (NCons _ x)  0 = showName src x
showLocal src (NCons ns _) l = showLocal src ns (l - 1)
showLocal _   _            _ = impossible

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

prettyTm :: Int -> B.ByteString -> Names -> Tm -> ShowS
prettyTm prec src ns t = go prec ns t where

  topInfo :: TopInfo
  topInfo = go ns where
    go (NNil inf) = inf
    go (NCons ns _) = go ns

  eqName :: Name -> Name -> Bool
  eqName (NSpan x) (NSpan x') = eqSpan src x x'
  eqName NX        NX         = True
  eqName NEmpty    NEmpty     = True
  eqName _         _          = False

  count :: Names -> Name -> Int
  count ns n = go ns 0 where
    go NNil{}        acc = acc
    go (NCons ns n') acc
      | eqName n n' = go ns (acc + 1)
      | otherwise   = go ns acc

  counted :: String -> Int -> String
  counted x 0 = x
  counted x n = x ++ show n

  fresh :: Names -> Name -> (Name, String)
  fresh ns NEmpty    = (NEmpty, "_")
  fresh ns NX        = (NX, counted "x" (count ns NX))
  fresh ns (NSpan x) = (NSpan x, counted (showSpan src x) (count ns (NSpan x)))

  freshS ns x = fresh ns (NSpan x)

  local :: Names -> Ix -> String
  local ns topIx = go ns topIx where
    go (NCons ns n) 0 = case n of NEmpty -> '@':show topIx
                                  n      -> snd (fresh ns n)
    go (NCons ns n) x = go ns (x - 1)
    go _            _ = impossible

  bracket :: ShowS -> ShowS
  bracket ss = ('{':).ss.('}':)

  piBind ns x Expl a = showParen True ((x++) . (" : "++) . go letp ns a)
  piBind ns x Impl a = bracket        ((x++) . (" : "++) . go letp ns a)

  lamBind x Impl = bracket (x++)
  lamBind x Expl = (x++)

  goMask :: Int -> Names -> MetaVar -> LS.LvlSet -> ShowS
  goMask p ns m mask = fst (go ns) where
    go :: Names -> (ShowS, Lvl)
    go NNil{} =
      ((show m++), 0)
    go (NCons ns (fresh ns -> (n, x))) = case go ns of
      (s, l) | LS.member l mask -> ((par p appp $ s . (' ':) . (x++)), l + 1)
             | otherwise        -> (s, l + 1)

  goTop :: Lvl -> ShowS
  goTop x s = let
    x' = runIO do
      TopEntry x _ _ <- ALM.read topInfo (coerce x)
      pure x
    in showSpan src x' ++ s

  go :: Int -> Names -> Tm -> ShowS
  go p ns = \case
    LocalVar x   -> (local ns x++)
    App t u Expl -> par p appp $ go appp ns t . (' ':) . go atomp ns u
    App t u Impl -> par p appp $ go appp ns t . (' ':) . bracket (go letp ns u)

    Lam (fresh ns -> (n, x)) i t ->
      par p letp $ ("λ "++) . lamBind x i . goLam (NCons ns n) t where
        goLam ns (Lam (fresh ns -> (n, x)) i t) =
          (' ':) . lamBind x i . goLam (NCons ns n) t
        goLam ns t =
          (". "++) . go letp ns t

    U                   -> ("U"++)
    Pi NEmpty Expl a b  -> par p pip $ go appp ns a . (" → "++) . go pip (NCons ns NEmpty) b

    Pi (fresh ns -> (n, x)) i a b ->
      par p pip $ piBind ns x i a . goPi (NCons ns n) b where
        goPi ns (Pi (fresh ns -> (n, x)) i a b)
          | x /= "_" = piBind ns x i a . goPi (NCons ns n) b
        goPi ns b = (" → "++) . go pip ns b

    Let (freshS ns -> (n, x)) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
      . (" = "++) . go letp ns t . ("; "++) . go letp (NCons ns n) u

    Meta m              -> (show m ++)
    InsertedMeta m mask -> goMask p ns m mask
    TopVar x            -> goTop x
    Irrelevant          -> ("Irrelevant"++)

showTm0 :: B.ByteString -> TopInfo -> Tm -> String
showTm0 src topinfo t = prettyTm 0 src (NNil topinfo) t []
