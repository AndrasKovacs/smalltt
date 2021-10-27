{-# language UnboxedTuples #-}

module Unification (unify, solve) where

import IO
import GHC.Exts
import qualified Data.Array.FM as AFM

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

- scopecheck
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
    occurs :: MetaVar
  , dom    :: Lvl
  , cod    :: Lvl
  , ren    :: AFM.Array Lvl
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

renameSp :: MetaCxt -> PartialRenaming -> Tm -> Spine -> U.IO Tm
renameSp ms pren ~hd = \case
  SId         -> U.pure hd
  SApp sp t i -> App U.<$> renameSp ms pren hd sp
                     U.<*> rename ms pren t
                     U.<*> U.pure i

-- TODO: approx unfolding, occurs caching
rename :: MetaCxt -> PartialRenaming -> Val -> U.IO Tm
rename ms pren v = U.do
  let go       = rename ms pren;   {-# inline go #-}
      goSp     = renameSp ms pren; {-# inline goSp #-}
      goBind t = rename ms (lift pren)
                           (appCl' ms t (VLocalVar (cod pren) SId))
      {-# inline goBind #-}

  forceFU ms v U.>>= \case

    VFlex m' sp | occurs pren == m' -> throw $ UnifyEx Conversion -- occurs check
                | otherwise         -> goSp (Meta m') sp

    VLocalVar x sp -> U.do
      if x < coerce (AFM.size (ren pren)) then U.do
        y <- U.io $ AFM.read (ren pren) (coerce x)
        case y of
          (-1) -> throw $ UnifyEx Conversion -- scope error
          y    -> goSp (LocalVar (lvlToIx (dom pren) y)) sp
      else
        goSp (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren)))) sp

    VLam x i t  -> Lam x i U.<$> goBind t
    VPi x i a b -> Pi x i U.<$> go a U.<*> goBind b
    VUnfold{}   -> impossible
    VU          -> U.pure U
    VIrrelevant -> U.pure Irrelevant

lams :: Spine -> Tm -> Tm
lams SId           acc = acc
lams (SApp sp t i) acc = lams sp (Lam NX i acc)

guardSolution :: ConvState -> U.IO ()
guardSolution = \case
  CSFlex -> throw $ UnifyEx CSFlexSolution
  _      -> U.pure ()
{-# inline guardSolution #-}

solve :: MetaCxt -> Lvl -> MetaVar -> Spine -> Val -> U.IO ()
solve ms l x ~sp ~rhs = U.do
  debug ["attempt solve", show (VFlex x sp), show rhs]
  pren <- invertSp ms l x sp
  rhs <- lams sp U.<$> rename ms pren rhs
  debug ["solve", show x, show pren, show rhs]
  MC.solve ms x (eval ms ENil rhs)

flexFlex :: MetaCxt -> Lvl -> MetaVar -> Spine -> MetaVar -> Spine -> U.IO ()
flexFlex ms l x ~sp x' ~sp' =
  solve ms l x sp (VFlex x' sp') `catch` \_ ->
  solve ms l x' sp' (VFlex x sp)

solveLong :: MetaCxt -> Lvl -> Lvl -> MetaVar -> Spine -> Val -> U.IO ()
solveLong ms l frz x sp rhs = forceFU ms rhs U.>>= \case
  VLam _ i t ->
    let v = VLocalVar l SId
    in solveLong ms (l + 1) frz x (SApp sp v i) (appCl' ms t v)
  VFlex x' sp' | x == x'   -> unifySp ms l frz CSFull sp sp'
               | otherwise -> flexFlex ms l x sp x' sp'
  rhs ->
    solve ms l x sp rhs

rigidEtaSp :: MetaCxt -> Lvl -> Lvl -> ConvState -> Lvl -> Spine -> Val -> U.IO ()
rigidEtaSp ms l frz cs x sp v = forceCS ms cs v U.>>= \case
  VLam _ i t' ->
    let v = VLocalVar l SId
    in rigidEtaSp ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  VLocalVar x' sp' | x == x' ->
    unifySp ms l frz cs sp sp'
  _ ->
    throw (UnifyEx Conversion)

rigidEta :: MetaCxt -> Lvl -> Lvl -> ConvState -> Val -> Val -> U.IO ()
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

unifySp :: MetaCxt -> Lvl -> Lvl -> ConvState -> Spine -> Spine -> U.IO ()
unifySp ms l frz cs sp sp' = case (sp, sp') of
  (SId,         SId          ) -> U.pure ()
  (SApp sp t _, SApp sp' t' _) -> unifySp ms l frz cs sp sp' U.>> unify ms l frz cs t t'
  _                            -> throw $ UnifyEx Conversion

unify :: MetaCxt -> Lvl -> Lvl -> ConvState -> Val -> Val -> U.IO ()
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
        | otherwise -> guardSolution cs U.>> flexFlex ms l x sp x' sp'

      (VUnfold h sp t, VUnfold h' sp' t') -> case cs of
        CSRigid | h == h'   -> unifySp ms l frz CSFlex sp sp'
                                 `catch` \_ -> unify ms l frz CSFull t t'
                | otherwise -> unify ms l frz CSFull t t'
        CSFlex  | h == h'   -> unifySp ms l frz CSFlex sp sp'
                | otherwise -> err
        _       -> impossible

      (VIrrelevant, _          ) -> U.pure ()
      (_          , VIrrelevant) -> U.pure ()

      (VFlex x sp, t') -> U.do
        guardSolution cs
        solve ms l x sp t' `catch` \_ -> solveLong ms l frz x sp t'

      (t, VFlex x' sp') -> U.do
        guardSolution cs
        solve ms l x' sp' t `catch` \_ -> solveLong ms l frz x' sp' t

      (VUnfold h sp t, t') -> case cs of
        CSRigid -> go t t'
        CSFlex  -> err
        _       -> impossible
      (t, VUnfold h' sp' t') -> case cs of
        CSRigid -> go t t'
        CSFlex  -> err
        _       -> impossible

      (t, t') -> rigidEta ms l frz cs t t'
