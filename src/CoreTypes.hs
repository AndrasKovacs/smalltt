{-# language UnboxedTuples  #-}
{-# options_ghc -funbox-strict-fields #-}

{-|



-}

module CoreTypes where

import qualified Data.Array.LM        as ALM
import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Ref.F           as RF
import qualified Data.Array.UM        as AUM
import qualified Data.Ref.UU          as RUU
import IO (runIO)
import GHC.Exts

import qualified UIO as U
import qualified UIO
import qualified LvlSet as LS
import Common
import Data.Bits

#include "deriveCanIO.h"

-- Metacxt
--------------------------------------------------------------------------------

data MetaEntry = Unsolved LS.LvlSet | Solved (RF.Ref MetaVar) LS.LvlSet Tm ~Val
type MetaCxt = ADL.Array MetaEntry

CAN_IO(MetaEntry, LiftedRep, MetaEntry, x, CoeMetaEntry)

CAN_IO(MetaCxt, UnliftedRep, MutableArrayArray# RealWorld,
       ADL.Array (RUU.Ref (AUM.Array x)), CoeMetaCxt)

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
  | VLam NameIcit Closure
  | VPi NameIcit VTy Closure
  | VU
  | VIrrelevant
  deriving Show

CAN_IO(Val, LiftedRep, Val, x, CoeVal)

type Ty = Tm

newtype DontPrint a = DontPrint a

instance Show (DontPrint a) where
  showsPrec _ _ x = x

data Tm
  = LocalVar Ix
  | TopVar Lvl ~(DontPrint Val)
  | Let Span Tm Tm Tm
  | App Tm Tm Icit
  | Lam NameIcit Tm
  | InsertedMeta MetaVar
  | Meta MetaVar
  | Pi NameIcit Ty Ty
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

-- data UnfoldHead = UHTopVar Lvl ~Val | UHSolved MetaVar
-- | Top-level things whose unfolding can be delayed.
data UnfoldHead = UnfoldHead# Int ~Val

eqUH :: UnfoldHead -> UnfoldHead -> Bool
eqUH (UnfoldHead# x _) (UnfoldHead# x' _) = x == x'
{-# inline eqUH #-}

unpackUH# :: UnfoldHead -> (# (# Lvl, Val #) | MetaVar #)
unpackUH# (UnfoldHead# x v) = case x .&. 1 of
  0 -> (# (# Lvl (unsafeShiftR x 1), v #) | #)
  _ -> (# | MkMetaVar (unsafeShiftR x 1) #)
{-# inline unpackUH# #-}

-- | A top-level variable.
pattern UHTopVar :: Lvl -> Val -> UnfoldHead
pattern UHTopVar x v <- (unpackUH# -> (# (# x, v #) | #)) where
  UHTopVar (Lvl x) ~v = UnfoldHead# (unsafeShiftL x 1) v

-- | A solved metavariable.
pattern UHSolved :: MetaVar -> UnfoldHead
pattern UHSolved x <- (unpackUH# -> (# | x #)) where
  UHSolved (MkMetaVar x) = UnfoldHead# (unsafeShiftL x 1 + 1) undefined
{-# complete UHTopVar, UHSolved #-}

instance Show UnfoldHead where
  show (UHTopVar x _) = "(TopVar " ++ show x ++ ")"
  show (UHSolved x)   = "(Solved " ++ show x ++ ")"

--------------------------------------------------------------------------------

data TopEntry
  -- ^ Name, type, definition, bound for frozen metas.
  = TopEntry {-# unpack #-} Span Tm Tm MetaVar

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

namesLen :: Names -> Lvl
namesLen = go 0 where
  go acc NNil{} = acc
  go acc (NCons ns _) = go (acc + 1) ns

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

prettyTm :: MetaCxt -> Int -> Src -> Names -> Tm -> ShowS
prettyTm ms prec src ns t = go prec ns t where

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

  -- prints full inserted spine, right now this is not used!
  -- we instead just print ?X(..)
  goInserted :: Int -> Names -> MetaVar -> ShowS
  goInserted p topNs m = go p topNs 0 where

    topL = namesLen topNs

    mask = runIO do
      ADL.unsafeRead ms (coerce m) >>= \case
        Unsolved mask     -> pure mask
        Solved _ mask _ _ -> pure mask

    go :: Int -> Names -> Ix -> ShowS
    go p NNil{} i = (show m++)
    go p (NCons ns _) i
      | LS.member (topL - coerce i - 1) mask =
          par p appp (go appp ns (i + 1) . (' ':) . (local topNs i ++))
      | otherwise =
          go p ns (i + 1)

  goTop :: Lvl -> ShowS
  goTop x s = let
    x' = runIO do
      TopEntry x _ _ _ <- ALM.read topInfo (coerce x)
      pure x
    in showSpan src x' ++ s

  go :: Int -> Names -> Tm -> ShowS
  go p ns = \case
    LocalVar x   -> (local ns x++)
    App t u Expl -> par p appp $ go appp ns t . (' ':) . go atomp ns u
    App t u Impl -> par p appp $ go appp ns t . (' ':) . bracket (go letp ns u)

    Lam (NI (fresh ns -> (n, x)) i) t ->
      par p letp $ ("λ "++) . lamBind x i . goLam (NCons ns n) t where
        goLam ns (Lam (NI (fresh ns -> (n, x)) i) t) =
          (' ':) . lamBind x i . goLam (NCons ns n) t
        goLam ns t =
          (". "++) . go letp ns t

    U                   -> ("U"++)
    Pi (NI NEmpty Expl) a b  -> par p pip $ go appp ns a . (" → "++) . go pip (NCons ns NEmpty) b

    Pi (NI (fresh ns -> (n, x)) i) a b ->
      par p pip $ piBind ns x i a . goPi (NCons ns n) b where
        goPi ns (Pi (NI (fresh ns -> (n, x)) i) a b)
          | x /= "_" = piBind ns x i a . goPi (NCons ns n) b
        goPi ns b = (" → "++) . go pip ns b

    Let (freshS ns -> (n, x)) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
      . (" = "++) . go letp ns t . ("; "++) . go letp (NCons ns n) u

    Meta m              -> (show m ++)
    InsertedMeta m      -> (show m ++).("(..)"++)
    TopVar x _          -> goTop x
    Irrelevant          -> ("Irrelevant"++)

showTm0 :: MetaCxt -> Src -> TopInfo -> Tm -> String
showTm0 ms src topinfo t = prettyTm ms 0 src (NNil topinfo) t []
