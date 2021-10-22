{-# language UnboxedTuples #-}

module Unification where

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


-- TODO: organize modules somehow

-- TODO: eta-short solution + long retry
--       flex-flex
--       meta freezing
--       glued renaming
--       occurs caching

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
     , TupleRep [ IntRep COMMA IntRep COMMA IntRep COMMA UnliftedRep ]
     , (# Int#, Int#, Int#, MutableByteArray# RealWorld #)
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
          forceFUM ms t U.>>= \case
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
renameSp ms pren hd = \case
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

  forceFUM ms v U.>>= \case

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

solve :: MetaCxt -> Lvl -> ConvState -> MetaVar -> Spine -> Val -> U.IO ()
solve ms l cs x sp rhs = U.do
  U.when (cs == CSFlex) $ throw $ UnifyEx CSFlexSolution
  pren <- invertSp ms l x sp
  rhs <- lams sp U.<$> rename ms pren rhs
  debug ["solve", show x, show pren, show rhs]
  MC.solve ms x (eval ms ENil rhs)

unifySp :: MetaCxt -> Lvl -> ConvState -> Spine -> Spine -> U.IO ()
unifySp ms l cs sp sp' = case (sp, sp') of
  (SId,         SId          ) -> U.pure ()
  (SApp sp t _, SApp sp' t' _) -> unifySp ms l cs sp sp' U.>> unify ms l cs t t'
  _                            -> throw $ UnifyEx Conversion

unify :: MetaCxt -> Lvl -> ConvState -> Val -> Val -> U.IO ()
unify ms l cs t t' = U.do
  let
    go = unify ms l cs
    {-# inline go #-}

    goBind t t' =
      let v = VLocalVar l SId
      in  unify ms (l + 1) cs (appCl ms t v) (appCl ms t' v)
    {-# inline goBind #-}

    goSp = unifySp ms l cs
    {-# inline goSp #-}

    err = throw $ UnifyEx Conversion
    {-# inline err #-}

    goEq :: forall a. Eq a => a -> a -> U.IO ()
    goEq x x' | x == x'   = U.pure()
              | otherwise = err
    {-# inline goEq #-}

    force t = case cs of CSFull -> forceFUM ms t
                         _      -> forceFM  ms t
    {-# inline force #-}

  t  <- force t
  t' <- force t'

  case (t, t') of

    (VIrrelevant, _) -> U.pure ()
    (_, VIrrelevant) -> U.pure ()

    -- TODO: eta-short meta solutions here!

    -- unfoldings
    (VUnfold h sp t, VUnfold h' sp' t') -> case cs of
      CSRigid -> (goEq h h' U.>> unifySp ms l CSFlex sp sp')
                 `catch` \case UnifyEx{} -> unify ms l CSFull t t'
                               e         -> throw e
      CSFlex  -> err
      _       -> impossible
    (VUnfold h sp t, t') -> case cs of
      CSRigid -> go t t'
      CSFlex  -> err
      _       -> impossible
    (t, VUnfold h' sp' t') -> case cs of
      CSRigid -> go t t'
      CSFlex  -> err
      _       -> impossible

    -- rigid & canonical
    (VLocalVar x sp, VLocalVar x' sp') | x == x' -> goSp sp sp'
    (VLam _ _ t    , VLam _ _ t'     )           -> goBind t t'
    (VPi _ i a b   , VPi _ i' a' b'  ) | i == i' -> go a a' U.>> goBind b b'
    (VU            , VU              )           -> U.pure ()

    -- eta
    (t, VLam _ i t') ->
      let v = VLocalVar l SId in unify ms (l + 1) cs (app ms t v i) (appCl' ms t' v)
    (VLam _ i t, t') ->
      let v = VLocalVar l SId in unify ms (l + 1) cs (appCl' ms t v) (app ms t' v i)

    -- flex
    (VFlex x sp, VFlex x' sp') | x == x' -> goSp sp sp'
    (VFlex x sp, t')  -> U.do
       solve ms l cs x sp t'
    (t, VFlex x' sp') -> solve ms l cs x' sp' t

    _ -> err
