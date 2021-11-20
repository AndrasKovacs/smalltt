{-# language UnboxedTuples #-}
{-# options_ghc -Wno-orphans #-}

module Unification (unify, solve) where

import qualified Data.Array.FM as AFM
import qualified Data.Ref.F as RF
import IO
import GHC.Exts
import Data.Bits


import qualified MetaCxt as MC
import qualified UIO as U
import qualified UIO
import qualified LvlSet as LS
import Common
import CoreTypes
import Evaluation
import Exceptions
import ElabState

#include "deriveCanIO.h"

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
      - rename flex sp, if illegal fullcheck whole unfold
    - unfold active solved:
      - occurs check meta, rename flex sp, if illegal fullcheck whole unfold

  - flex
    - illegal head: return Irrelevant
    - unfold frozen solved or let definition:
      - rename flex sp, propagate illegal
    - unfold active solved:
      - occurs check meta, rename flex sp, propagate illegal

- fullcheck
  - fully forces everything, no faffing around

-}

-- PARTIAL RENAMINGS
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
      Unsolved _ | occ == x  -> U.pure UFalse
                 | otherwise -> U.pure UTrue
      Solved cache _ t _ -> U.do
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
    LocalVar x     -> U.pure UTrue
    TopVar x _     -> U.pure UTrue
    Let x a t u    -> (\x y z -> x <> y <> z) U.<$> go a U.<*> go t U.<*> go u
    App t u i      -> (<>) U.<$> go t U.<*> go u
    Lam x i t      -> go t
    InsertedMeta x -> occurs' ms frz occ x
    Meta x         -> occurs' ms frz occ x
    Pi x i a b     -> (<>) U.<$> go a U.<*> go b
    Irrelevant     -> U.pure UTrue
    U              -> U.pure UTrue

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
        -- TODO: simplify arith expr here (LocalVar (cod pren - x - 1))
        goSp rs (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren))) // UTrue) sp

    VFlex x sp
      | occ pren == x -> case rs of
          RRigid -> throw $ UnifyEx Conversion
          _      -> U.pure (Irrelevant, UFalse)
      | otherwise -> goSp rs (Meta x // UTrue) sp

    topt@(VUnfold h sp t) -> U.do
      (t, tf) <- case h of    -- WARNING: Core was fine here, but should be checked on ghc change
        UHTopVar x v -> U.do
          goSp RFlex (TopVar x v // UTrue) sp
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
  debug ["rename", show t]
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

invertSp :: MetaCxt -> Lvl -> MetaVar -> Spine -> LS.LvlSet -> U.IO PartialRenaming
invertSp cxt gamma m sp trim = U.do
  ren <- U.io $ AFM.new @Lvl (coerce gamma)
  U.io $ AFM.set ren (-1)

  let go :: MetaCxt -> AFM.Array Lvl -> LS.LvlSet -> Spine -> U.IO Lvl
      go ms ren trim = \case
        SId         -> U.pure 0
        SApp sp t _ -> U.do
          dom <- go ms ren trim sp
          forceFU ms t U.>>= \case
            VLocalVar x SId -> U.do

              -- non-linear: variable was previously trimmed by eta-contraction
              U.when (LS.member x trim) (throw $ UnifyEx Conversion)

              y <- U.io $ AFM.read ren (coerce x)
              case y of
                (-1) -> U.do
                  U.io $ AFM.write ren (coerce x) dom
                  U.pure (dom + 1)

                -- non-linear: variable already mapped
                y -> throw $ UnifyEx Conversion
            _ ->
              throw $ UnifyEx Conversion -- non-var in spine

  dom <- go cxt ren trim sp
  U.pure (PRen m dom gamma ren)

lams :: Spine -> Tm -> Tm
lams SId           acc = acc
lams (SApp sp t i) acc = lams sp (Lam NX i acc)

guardCS :: ConvState -> U.IO ()
guardCS cs = U.when (cs == CSFlex) $ throw $ UnifyEx CSFlexSolution
{-# inline guardCS #-}


data SSLS = SSLS Spine Spine LS.LvlSet
CAN_IO3(SSLS, LiftedRep, LiftedRep, IntRep, Spine, Spine, Int#, SSLS x y (LS.LvlSet (I# z)), CoeSSLS)

-- Try to eta contract both sides, return trimmed lhs, rhs, and the set of
-- variables that were trimmed.
etaContract :: Spine -> Val -> (Spine -> Val -> LS.LvlSet -> U.IO a) -> U.IO a
etaContract sp rhs cont = let

  go :: Spine -> Spine -> LS.LvlSet -> U.IO SSLS
  go sp sp' trim = case (sp, sp') of
    (left@(SApp sp (VLocalVar x SId) i), right@(SApp sp' (VLocalVar x' SId) i')) -> U.do
      U.when (LS.member x trim) (throw $ UnifyEx Conversion) -- non-linear spine
      if x == x' then go sp sp' (LS.insert x trim)
                 else U.pure (SSLS left right trim)
    (sp, sp') -> U.pure (SSLS sp sp' trim)

  in case rhs of
    VFlex x sp'     -> go sp sp' mempty U.>>= \case
                         SSLS sp sp' trim -> cont sp (VFlex x sp') trim
    VLocalVar x sp' -> go sp sp' mempty U.>>= \case
                         SSLS sp sp' trim -> cont sp (VLocalVar x sp') trim
    VUnfold h sp' v -> go sp sp' mempty U.>>= \case
                         SSLS sp sp' trim -> cont sp (VUnfold h sp' v) trim
    _               -> cont sp rhs mempty
{-# inline etaContract #-}

solve :: MetaCxt -> Lvl -> MetaVar -> Spine -> Val -> U.IO ()
solve cxt l x ~sp ~rhs = U.do
  debug ["attempt solve", show (VFlex x sp), show rhs]
  frz <- U.io getFrozen
  U.when (x < frz) $ throw $ UnifyEx $ FrozenSolution x
  etaContract sp rhs \sp rhs trim -> U.do
    pren <- invertSp cxt l x sp trim
    rhs <- lams sp U.<$> rename cxt frz pren rhs
    debug ["renamed", show rhs]
    debug ["solve", show x, show pren, show rhs]
    MC.solve cxt x rhs (eval cxt ENil rhs)

solveLong :: MetaCxt -> Lvl -> MetaVar -> Spine -> Val -> U.IO ()
solveLong cxt l x sp rhs = forceFU cxt rhs U.>>= \case
  VLam _ i t ->
    let v = VLocalVar l SId
    in solveLong cxt (l + 1) x (SApp sp v i) (appCl' cxt t v)
  VFlex x' sp' | x == x'   -> unifySp cxt l CSFull sp sp'
               | otherwise -> flexFlex cxt l (VFlex x sp) x sp rhs x' sp'
  _ ->
    solve cxt l x sp rhs

flexFlex :: MetaCxt -> Lvl -> Val -> MetaVar -> Spine -> Val -> MetaVar -> Spine -> U.IO ()
flexFlex cxt l t x ~sp t' x' ~sp' =
  solve cxt l x sp t' `catch` \_ ->
  solve cxt l x' sp' t

rigidEtaSp :: MetaCxt -> Lvl -> ConvState -> Lvl -> Spine -> Val -> U.IO ()
rigidEtaSp cxt l cs x sp v = forceCS cxt cs v U.>>= \case
  VLam _ i t' ->
    let v = VLocalVar l SId
    in rigidEtaSp cxt (l + 1) cs x (SApp sp v i) (appCl' cxt t' v)
  VLocalVar x' sp' | x == x' ->
    unifySp cxt l cs sp sp'
  _ ->
    throw (UnifyEx Conversion)

rigidEta :: MetaCxt -> Lvl -> ConvState -> Val -> Val -> U.IO ()
rigidEta cxt l cs ~t ~t' = case (t, t') of
  (VLocalVar x sp, VLam _ i t')  ->
    let v = VLocalVar l SId
    in rigidEtaSp cxt (l + 1) cs x (SApp sp v i) (appCl' cxt t' v)
  (VLam _ i t, VLocalVar x' sp') ->
    let v = VLocalVar l SId
    in rigidEtaSp cxt (l + 1) cs x' (SApp sp' v i) (appCl' cxt t v)
  _ ->
    throw (UnifyEx Conversion)
{-# noinline rigidEta #-}

unifySp :: MetaCxt -> Lvl -> ConvState -> Spine -> Spine -> U.IO ()
unifySp cxt l cs sp sp' = case (sp, sp') of
  (SId,         SId          ) -> U.pure ()
  (SApp sp t _, SApp sp' t' _) -> unifySp cxt l cs sp sp' U.>>
                                  unify cxt l cs (gjoin t) (gjoin t')
  _                            -> throw $ UnifyEx Conversion

unify :: MetaCxt -> Lvl -> ConvState -> G -> G -> U.IO ()
unify cxt l cs (G topt ftopt) (G topt' ftopt') = let
  go       = unify cxt l cs; {-# inline go #-}
  go' t t' = go (gjoin t) (gjoin t'); {-# inline go' #-}
  err      = throw (UnifyEx Conversion); {-# inline err #-}

  goBind t t' =
    let v = VLocalVar l SId
    in unify cxt (l + 1) cs (gjoin $! appCl' cxt t v)
                               (gjoin $! appCl' cxt t' v)
  {-# inline goBind #-}

  in U.do
    t  <- forceCS cxt cs ftopt
    t' <- forceCS cxt cs ftopt'
    case (t, t') of

      -- rigid, canonical
      (VLocalVar x sp, VLocalVar x' sp') | x == x' -> unifySp cxt l cs sp sp'
      (VLam _ _ t    , VLam _ _ t'     )           -> goBind t t'
      (VPi _ i a b   , VPi _ i' a' b'  ) | i == i' -> go' a a' U.>> goBind b b'
      (VU            , VU              )           -> U.pure ()

      (VFlex x sp, VFlex x' sp')
        | x == x'   -> unifySp cxt l cs sp sp'
        | otherwise -> guardCS cs U.>> flexFlex cxt l topt x sp topt' x' sp'

      (VUnfold h sp t, VUnfold h' sp' t') -> case cs of
        CSRigid | eqUH h h' -> unifySp cxt l CSFlex sp sp'
                                 `catch` \_ -> unify cxt l CSFull (gjoin t) (gjoin t')
                | otherwise -> unify cxt l CSFull (gjoin t) (gjoin t')
        CSFlex  | eqUH h h' -> unifySp cxt l CSFlex sp sp'
                | otherwise -> err
        _       -> impossible

      (VIrrelevant, _          ) -> U.pure ()
      (_          , VIrrelevant) -> U.pure ()

      (VFlex x sp, t') -> U.do
        guardCS cs
        solve cxt l x sp topt' `catch` \_ ->
          solveLong cxt l x sp t'

      (t, VFlex x' sp') -> U.do
        guardCS cs
        solve cxt l x' sp' topt `catch` \_ ->
          solveLong cxt l x' sp' t

      (VUnfold h sp t, t') -> case cs of
        CSRigid -> go (G topt t) (G topt' t')
        CSFlex  -> err
        _       -> impossible
      (t, VUnfold h' sp' t') -> case cs of
        CSRigid -> go (G topt t) (G topt' t')
        CSFlex  -> err
        _       -> impossible

      (t, t') -> rigidEta cxt l cs t t'
