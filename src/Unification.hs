{-# language UnboxedTuples #-}
{-# options_ghc -Wno-orphans #-}

module Unification (unify, solve) where

import qualified Data.Array.FM as AFM
import qualified Data.Ref.F as RF
import IO
import GHC.Exts
import Data.Bits

import Common
import CoreTypes
import Evaluation
import MetaCxt (MetaCxt)
import qualified MetaCxt as MC
import qualified UIO as U
import qualified UIO
import Exceptions

#include "deriveCanIO.h"

--------------------------------------------------------------------------------

-- TODO: meta freezing
--       glued renaming
--       occurs caching
--       organize args in records

-- store frozenness to MetaCxt?


--------------------------------------------------------------------------------

{-
- Occurs check:
  - approximate, only visits active solved metas
  - we cache the last occurs check result

- renaming:
  - returns an extra flag for whether renaming result is legal, or it's possibly illegal
  - 2 states, flex + rigid
  - doesn't force scrutinee

  - rigid:
    - illegal head: error
    - unfold frozen solved or let definition:
      - rename flex sp, if illegal scopecheck rigid whole unfold
    - unfold active solved:
      - occurs check meta, rename flex sp, if illegal rigid scopecheck whole unfold

  - flex
    - illegal head: return Irrelevant
    - unfold frozen solved or let definition:
      - rename flex sp, propagate illegal
    - unfold active solved:
      - occurs check meta, rename flex sp, propagate illegal

- scopecheck:
  - fully forces everything




  ALT:
  - takes partial renaming as arg
  - states: Rigid, Flex, Full

  - Rigid:
    - doesn't force scrutinee
    - illegal head: error
    - defs: scopecheck flex spine, if fails retry full
    - active solved: scopecheck flex spine + occurs check, if fails retry full

  - Flex, same as rigid, doesn't retry

  - Full: fully forces scrutinee, works in the evident way

-}

--------------------------------------------------------------------------------

data PartialRenaming = PRen {
    occ :: MetaVar
  , dom :: Lvl
  , cod :: Lvl
  , ren :: AFM.Array Lvl
  }

instance Show PartialRenaming where
  show (PRen occ dom cod ren) = runIO do
    ren <- AFM.unsafeFreeze ren
    pure $ show (occ, dom, cod, ren)

CAN_IO4(PartialRenaming
     , IntRep, IntRep, IntRep, UnliftedRep
     , Int#, Int#, Int#, MutableByteArray# RealWorld
     , PRen (MkMetaVar (I# a)) (Lvl (I# b)) (Lvl (I# c)) (AFM.Array d)
     , CoePartialRenaming)

lift :: PartialRenaming -> PartialRenaming
lift (PRen m dom cod ren) = PRen m (dom + 1) (cod + 1) ren
{-# inline lift #-}


-- SOLUTION CHECKING
--------------------------------------------------------------------------------

newtype UBool = UBool# Int deriving Eq via Int
pattern UTrue, UFalse :: UBool
pattern UTrue = UBool# 0
pattern UFalse = UBool# 1
{-# complete UTrue, UFalse #-}

instance Semigroup UBool where
  (<>) (UBool# x) (UBool# y) = UBool# (x .&. y)
  {-# inline (<>) #-}

CAN_IO(UBool, IntRep, Int#, UBool# (I# x), CoeUBool)

instance Show UBool where
  show UTrue = "True"
  show _     = "False"

CAN_IO2((Tm,UBool), LiftedRep, IntRep, Tm, Int#, (x, UBool# (I# y)), CoeTmUBool)

type RenState  = UBool
pattern RRigid, RFlex :: UBool
pattern RRigid = UTrue
pattern RFlex  = UFalse

occurs' :: MetaCxt -> MetaVar -> MetaVar -> MetaVar -> U.IO UBool
occurs' ms frz occ x
  | x < frz   = U.pure UTrue
  | otherwise = MC.read ms x U.>>= \case
      MC.MEUnsolved | occ == x  -> U.pure UFalse
                    | otherwise -> U.pure UTrue
      MC.MESolved cache t _ -> U.do
        cached <- U.io $ RF.read cache
        if cached == occ then
          U.pure UTrue
        else U.do
          res <- occurs ms frz occ t
          U.when (res == UTrue) (U.io $ RF.write cache occ)
          U.pure res

occurs :: MetaCxt -> MetaVar -> MetaVar -> Tm -> U.IO UBool
occurs ms frz occ t = let
  go = occurs ms frz occ; {-# inline go #-}
  in case t of
    LocalVar x          -> U.pure UTrue
    TopVar x v          -> U.pure UTrue
    Let x a t u         -> (\x y z -> x <> y <> z) U.<$> go a U.<*> go t U.<*> go u
    App t u i           -> (<>) U.<$> go t U.<*> go u
    Lam x i t           -> go t
    InsertedMeta x mask -> occurs' ms frz occ x
    Meta x              -> occurs' ms frz occ x
    Pi x i a b          -> (<>) U.<$> go a U.<*> go b
    Irrelevant          -> U.pure UTrue
    U                   -> U.pure UTrue

renameSp' :: MetaCxt -> MetaVar -> PartialRenaming -> RenState -> (Tm, UBool) -> Spine -> U.IO (Tm, UBool)
renameSp' ms frz pren rs hd = \case
  SId         -> U.pure hd
  SApp sp t i -> U.do
    (sp, spf) <- renameSp' ms frz pren rs hd sp
    (t, tf)   <- rename' ms frz pren rs t
    U.pure (App sp t i // spf <> tf)

rename' :: MetaCxt -> MetaVar -> PartialRenaming -> RenState -> Val -> U.IO (Tm, UBool)
rename' ms frz pren rs t = let
  go       = rename'   ms frz pren rs; {-# inline go #-}
  goSp rs  = renameSp' ms frz pren rs; {-# inline goSp #-}
  goBind t = rename' ms frz (lift pren) rs (appCl' ms t (VLocalVar (cod pren) SId))
  {-# inline goBind #-}

  in forceF ms t U.>>= \case
    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        U.io (AFM.read (ren pren) (coerce x)) U.>>= \case
          (-1) -> case rs of
            RRigid -> throw $ UnifyEx Conversion
            _      -> U.pure (Irrelevant, UFalse)
          y -> goSp rs (LocalVar (lvlToIx (dom pren) y) // UTrue) sp
      | otherwise ->
        -- TODO: simplify arith expr here
        goSp rs (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren))) // UTrue) sp

    VFlex x sp
      | occ pren == x -> case rs of
          RRigid -> throw $ UnifyEx Conversion
          _      -> U.pure (Irrelevant, UFalse)
      | otherwise -> goSp rs (Meta x // UTrue) sp

    topt@(VUnfold h sp t) -> U.do
      (t, tf) <- case h of                       -- TODO: check Core for crap
        UHTopVar x xv -> U.do
          goSp RFlex (TopVar x xv // UTrue) sp
        UHSolved x -> U.do
          xf <- occurs' ms frz (occ pren) x
          goSp RFlex (Meta x // xf) sp
      if tf == UFalse then U.do
        tf <- fullcheck ms frz pren topt
        U.pure (t // tf)
      else
        U.pure (t // tf)

    VLam x i t -> U.do
      (t, tf) <- goBind t
      U.pure (Lam x i t // tf)

    VPi x i a b -> U.do
      (a, af) <- go a
      (b, bf) <- goBind b
      U.pure (Pi x i a b // af <> bf)

    VU ->
      U.pure (U // UTrue)

    VIrrelevant ->
      U.pure (Irrelevant // UTrue)

rename :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> U.IO Tm
rename ms frz pren t = U.do
  (t, tf) <- rename' ms frz pren RRigid t
  U.when (tf == UFalse) $ throw $ UnifyEx Conversion
  U.pure t
{-# inline rename #-}

fullcheckSp :: MetaCxt -> MetaVar -> PartialRenaming -> Spine -> U.IO UBool
fullcheckSp ms frz pren = \case
  SId         -> U.pure UTrue
  SApp sp t i -> (<>) U.<$> fullcheckSp ms frz pren sp
                      U.<*> fullcheck ms frz pren t

fullcheck :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> U.IO UBool
fullcheck ms frz pren v = U.do
  let go       = fullcheck ms frz pren;   {-# inline go #-}
      goSp     = fullcheckSp ms frz pren; {-# inline goSp #-}
      goBind t = fullcheck ms frz (lift pren)
                    (appCl' ms t (VLocalVar (cod pren) SId))
      {-# inline goBind #-}

  forceFU ms v U.>>= \case

    VFlex m' sp | occ pren == m' -> U.pure UFalse -- occurs check
                | otherwise      -> goSp sp

    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        U.io (AFM.read (ren pren) (coerce x)) U.>>= \case
          (-1) -> U.pure UFalse -- scope error
          y    -> goSp sp
      | otherwise ->
        goSp sp

    VLam x i t  -> goBind t
    VPi x i a b -> (<>) U.<$> go a U.<*> goBind b
    VUnfold{}   -> impossible
    VU          -> U.pure UTrue
    VIrrelevant -> U.pure UTrue


-- UNIFICATION
--------------------------------------------------------------------------------

invertSp :: MetaCxt -> Lvl -> MetaVar -> Spine -> U.IO PartialRenaming
invertSp ms gamma m sp = U.do
  ren <- U.io $ AFM.new @Lvl (coerce gamma)
  U.io $ AFM.set ren (-1)

  let go :: MetaCxt -> AFM.Array Lvl -> Spine -> U.IO Lvl
      go ms ren = \case
        SId         -> U.pure 0
        SApp sp t _ -> U.do
          dom <- go ms ren sp
          forceFU ms t U.>>= \case
            VLocalVar x SId -> U.do
              y <- U.io $ AFM.read ren (coerce x)
              case y of
                (-1) -> U.do
                  U.io $ AFM.write ren (coerce x) dom
                  U.pure (dom + 1)
                y    -> throw $ UnifyEx Conversion -- non-linear
            _ ->
              throw $ UnifyEx Conversion -- non-var in spine

  dom <- go ms ren sp
  U.pure (PRen m dom gamma ren)

lams :: Spine -> Tm -> Tm
lams SId           acc = acc
lams (SApp sp t i) acc = lams sp (Lam NX i acc)

guardSolution :: ConvState -> U.IO ()
guardSolution = \case
  CSFlex -> throw $ UnifyEx CSFlexSolution
  _      -> U.pure ()
{-# inline guardSolution #-}

solve :: MetaCxt -> Lvl -> MetaVar -> MetaVar -> Spine -> Val -> U.IO ()
solve ms l frz x ~sp ~rhs = U.do
  debug ["attempt solve", show (VFlex x sp), show rhs]
  U.when (x < frz) $ throw $ UnifyEx (FrozenSolution x)
  pren <- invertSp ms l x sp
  rhs <- lams sp U.<$> rename ms frz pren rhs
  debug ["solve", show x, show pren, show rhs]
  MC.solve ms x rhs (eval ms ENil rhs)

flexFlex :: MetaCxt -> Lvl -> MetaVar -> MetaVar -> Spine -> MetaVar -> Spine -> U.IO ()
flexFlex ms l frz x ~sp x' ~sp' =
  solve ms l frz x sp (VFlex x' sp') `catch` \_ ->
  solve ms l frz x' sp' (VFlex x sp)

solveLong :: MetaCxt -> Lvl -> MetaVar -> MetaVar -> Spine -> Val -> U.IO ()
solveLong ms l frz x sp rhs = forceFU ms rhs U.>>= \case
  VLam _ i t ->
    let v = VLocalVar l SId
    in solveLong ms (l + 1) frz x (SApp sp v i) (appCl' ms t v)
  VFlex x' sp' | x == x'   -> unifySp ms l frz CSFull sp sp'
               | otherwise -> flexFlex ms l frz x sp x' sp'
  rhs ->
    solve ms l frz x sp rhs

rigidEtaSp :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Lvl -> Spine -> Val -> U.IO ()
rigidEtaSp ms l frz cs x sp v = forceCS ms cs v U.>>= \case
  VLam _ i t' ->
    let v = VLocalVar l SId
    in rigidEtaSp ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  VLocalVar x' sp' | x == x' ->
    unifySp ms l frz cs sp sp'
  _ ->
    throw (UnifyEx Conversion)

rigidEta :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Val -> Val -> U.IO ()
rigidEta ms l frz cs ~t ~t' = case (t, t') of
  (VLocalVar x sp, VLam _ i t')  ->
    let v = VLocalVar l SId
    in rigidEtaSp ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  (VLam _ i t, VLocalVar x' sp') ->
    let v = VLocalVar l SId
    in rigidEtaSp ms (l + 1) frz cs x' (SApp sp' v i) (appCl' ms t v)
  _ ->
    throw (UnifyEx Conversion)
{-# noinline rigidEta #-}

unifySp :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Spine -> Spine -> U.IO ()
unifySp ms l frz cs sp sp' = case (sp, sp') of
  (SId,         SId          ) -> U.pure ()
  (SApp sp t _, SApp sp' t' _) -> unifySp ms l frz cs sp sp' U.>> unify ms l frz cs t t'
  _                            -> throw $ UnifyEx Conversion

unify :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Val -> Val -> U.IO ()
unify ms l frz cs ~topt ~topt' = let
  go   = unify ms l frz cs;          {-# inline go #-}
  err  = throw (UnifyEx Conversion); {-# inline err #-}

  goBind t t' =
    let v = VLocalVar l SId
    in unify ms (l + 1) frz cs (appCl' ms t v) (appCl' ms t' v)
  {-# inline goBind #-}

  in U.do
    t  <- forceCS ms cs topt
    t' <- forceCS ms cs topt'
    case (t, t') of

      -- rigid, canonical
      (VLocalVar x sp, VLocalVar x' sp') | x == x' -> unifySp ms l frz cs sp sp'
      (VLam _ _ t    , VLam _ _ t'     )           -> goBind t t'
      (VPi _ i a b   , VPi _ i' a' b'  ) | i == i' -> go a a' U.>> goBind b b'
      (VU            , VU              )           -> U.pure ()

      (VFlex x sp, VFlex x' sp')
        | x == x'   -> unifySp ms l frz cs sp sp'
        | otherwise -> guardSolution cs U.>> flexFlex ms l frz x sp x' sp'

      (VUnfold h sp t, VUnfold h' sp' t') -> case cs of
        CSRigid | eqUH h h' -> unifySp ms l frz CSFlex sp sp'
                                 `catch` \_ -> unify ms l frz CSFull t t'
                | otherwise -> unify ms l frz CSFull t t'
        CSFlex  | eqUH h h' -> unifySp ms l frz CSFlex sp sp'
                | otherwise -> err
        _       -> impossible

      (VIrrelevant, _          ) -> U.pure ()
      (_          , VIrrelevant) -> U.pure ()

      (VFlex x sp, t') -> U.do
        guardSolution cs
        solve ms l frz x sp topt' `catch` \_ -> solveLong ms l frz x sp t'

      (t, VFlex x' sp') -> U.do
        guardSolution cs
        solve ms l frz x' sp' topt `catch` \_ -> solveLong ms l frz x' sp' t

      (VUnfold h sp t, t') -> case cs of
        CSRigid -> go t t'
        CSFlex  -> err
        _       -> impossible
      (t, VUnfold h' sp' t') -> case cs of
        CSRigid -> go t t'
        CSFlex  -> err
        _       -> impossible

      (t, t') -> rigidEta ms l frz cs t t'
