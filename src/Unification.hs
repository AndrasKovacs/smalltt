{-# language UnboxedTuples #-}
{-# options_ghc -Wno-orphans #-}

module Unification (unify, solve, unifySp) where

import qualified Data.Array.FM as AFM
import qualified Data.Ref.F as RF
import IO
import GHC.Exts

import qualified MetaCxt as MC
import qualified UIO as U
import qualified UIO
import qualified LvlSet as LS
import Common
import CoreTypes
import Evaluation
import Exceptions

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

--------------------------------------------------------------------------------

-- | Forcing depending on conversion state.
forceCS :: MetaCxt -> ConvState -> Val -> U.IO Val
forceCS cxt cs v = case cs of
  CSFull -> forceAll cxt v
  _      -> force    cxt v
{-# inline forceCS #-}

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

CAN_IO2((Tm,UBool), LiftedRep, IntRep, Tm, Int#, (x, UBool# (I# y)), CoeTmUBool)

newtype RenState = RenState# Int
pattern RRigid, RFlex :: RenState
pattern RRigid = RenState# 0
pattern RFlex  = RenState# 1

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
    Let x a t u    -> (\x y z -> x &&# y &&# z) U.<$> go a U.<*> go t U.<*> go u
    App t u i      -> (&&#) U.<$> go t U.<*> go u
    Lam _ t        -> go t
    InsertedMeta x -> occurs' ms frz occ x
    Meta x         -> occurs' ms frz occ x
    Pi _ a b       -> (&&#) U.<$> go a U.<*> go b
    Irrelevant     -> U.pure UTrue
    U              -> U.pure UTrue

renameSp' :: MetaCxt -> MetaVar -> PartialRenaming -> RenState -> (Tm, UBool) -> Spine -> U.IO (Tm, UBool)
renameSp' ms frz pren rs hd = \case
  SId         -> U.pure hd
  SApp sp t i -> U.do
    (sp, spf) <- renameSp' ms frz pren rs hd sp
    (t, tf)   <- rename' ms frz pren rs t
    U.pure (App sp t i // spf &&# tf)

rename' :: MetaCxt -> MetaVar -> PartialRenaming -> RenState -> Val -> U.IO (Tm, UBool)
rename' ms frz pren rs t = let
  go       = rename'   ms frz pren rs; {-# inline go #-}
  goSp rs  = renameSp' ms frz pren rs; {-# inline goSp #-}
  goBind t = rename' ms frz (lift pren) rs (appCl' ms t (VLocalVar (cod pren) SId))
  {-# inline goBind #-}

  in force ms t U.>>= \case
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
          goSp RFlex (TopVar x (coerce v) // UTrue) sp
        UHSolved x -> U.do
          xf <- occurs' ms frz (occ pren) x
          goSp RFlex (Meta x // xf) sp
      if tf == UFalse then U.do
        tf <- fullScopeCheck ms frz pren topt
        U.pure (t // tf)
      else
        U.pure (t // tf)

    VLam xi t -> U.do
      (t, tf) <- goBind t
      U.pure (Lam xi t // tf)

    VPi xi a b -> U.do
      (a, af) <- go a
      (b, bf) <- goBind b
      U.pure (Pi xi a b // af &&# bf)

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

fullScopeCheckSp :: MetaCxt -> MetaVar -> PartialRenaming -> Spine -> U.IO UBool
fullScopeCheckSp ms frz pren = \case
  SId         -> U.pure UTrue
  SApp sp t i -> (&&#) U.<$> fullScopeCheckSp ms frz pren sp
                       U.<*> fullScopeCheck ms frz pren t

fullScopeCheck :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> U.IO UBool
fullScopeCheck ms frz pren v = U.do
  let go       = fullScopeCheck ms frz pren;   {-# inline go #-}
      goSp     = fullScopeCheckSp ms frz pren; {-# inline goSp #-}
      goBind t = fullScopeCheck ms frz (lift pren)
                    (appCl' ms t (VLocalVar (cod pren) SId))
      {-# inline goBind #-}

  forceAll ms v U.>>= \case

    VFlex m' sp | occ pren == m' -> U.pure UFalse -- occurs check
                | otherwise      -> goSp sp

    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        U.io (AFM.read (ren pren) (coerce x)) U.>>= \case
          (-1) -> U.pure UFalse -- scope error
          y    -> goSp sp
      | otherwise ->
        goSp sp

    VLam _ t    -> goBind t
    VPi _ a b   -> (&&#) U.<$> go a U.<*> goBind b
    VUnfold{}   -> impossible
    VU          -> U.pure UTrue
    VIrrelevant -> U.pure UTrue


-- UNIFICATION
--------------------------------------------------------------------------------

invertSp :: MetaCxt -> Lvl -> MetaVar -> Spine -> LS.LvlSet -> U.IO PartialRenaming
invertSp ms gamma m sp trim = U.do
  ren <- U.io $ AFM.new @Lvl (coerce gamma)
  U.io $ AFM.set ren (-1)

  let go :: MetaCxt -> AFM.Array Lvl -> LS.LvlSet -> Spine -> U.IO Lvl
      go ms ren trim = \case
        SId         -> U.pure 0
        SApp sp t _ -> U.do
          dom <- go ms ren trim sp
          forceAll ms t U.>>= \case
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

  dom <- go ms ren trim sp
  U.pure (PRen m dom gamma ren)

lams :: Spine -> Tm -> Tm
lams SId           acc = acc
lams (SApp sp t i) acc = lams sp (Lam (NI NX i) acc)

data SSLS = SSLS Spine Spine LS.LvlSet
CAN_IO3(SSLS, LiftedRep, LiftedRep, IntRep, Spine, Spine, Int#,
        SSLS x y (LS.LvlSet (I# z)), CoeSSLS)

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

solve :: MetaCxt -> Lvl -> MetaVar -> MetaVar -> Spine -> Val -> U.IO ()
solve ms l frz x ~sp ~rhs = U.do
  -- debug ["attempt solve", show (VFlex x sp), show rhs]
  U.when (x < frz) $ throw $ UnifyEx $ FrozenSolution x

  -- TURN OFF eta-contraction here

  etaContract sp rhs \sp rhs trim -> U.do

  -- U.do
  --   let trim = mempty

    pren <- invertSp ms l x sp trim
    rhs <- lams sp U.<$> rename ms frz pren rhs
    debug ["renamed", show rhs]
    debug ["solve", show x, show pren, show rhs]
    MC.solve ms x rhs (eval ms ENil rhs)

solveLong :: MetaCxt -> Lvl -> MetaVar -> MetaVar -> Spine -> Val -> U.IO ()
solveLong ms l frz x sp rhs = forceAll ms rhs U.>>= \case
  VLam (NI _ i) t ->
    let v = VLocalVar l SId
    in solveLong ms (l + 1) frz x (SApp sp v i) (appCl' ms t v)
  VFlex x' sp' | x == x'   -> unifySp ms l frz CSFull sp sp'
               | otherwise -> flexFlex ms l frz (VFlex x sp) x sp rhs x' sp'
  _ ->
    solve ms l frz x sp rhs

flexFlex :: MetaCxt -> Lvl -> MetaVar -> Val -> MetaVar -> Spine -> Val -> MetaVar -> Spine -> U.IO ()
flexFlex ms l frz t x ~sp t' x' ~sp' =
  solve ms l frz x sp t' `catch` \_ ->
  solve ms l frz x' sp' t

rigidEtaSp :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Lvl -> Spine -> Val -> U.IO ()
rigidEtaSp ms l frz cs x sp v = forceCS ms cs v U.>>= \case
  VLam (NI _ i) t' ->
    let v = VLocalVar l SId
    in rigidEtaSp ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  VLocalVar x' sp' | x == x' ->
    unifySp ms l frz cs sp sp'
  _ ->
    throw (UnifyEx Conversion)

rigidEta :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Val -> Val -> U.IO ()
rigidEta ms l frz cs ~t ~t' = case (t, t') of
  (VLocalVar x sp, VLam (NI _ i) t')  ->
    let v = VLocalVar l SId
    in rigidEtaSp ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  (VLam (NI _ i) t, VLocalVar x' sp') ->
    let v = VLocalVar l SId
    in rigidEtaSp ms (l + 1) frz cs x' (SApp sp' v i) (appCl' ms t v)
  _ ->
    throw (UnifyEx Conversion)
{-# noinline rigidEta #-}

unifySp :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Spine -> Spine -> U.IO ()
unifySp ms l frz cs sp sp' = case (sp, sp') of
  (SId,         SId          ) -> U.pure ()
  (SApp sp t _, SApp sp' t' _) -> unifySp ms l frz cs sp sp' U.>>
                                  unify ms l frz cs (gjoin t) (gjoin t')
  _                            -> throw $ UnifyEx Conversion

unify :: MetaCxt -> Lvl -> MetaVar -> ConvState -> G -> G -> U.IO ()
unify ms l frz cs (G topt ftopt) (G topt' ftopt') = let
  go       = unify ms l frz cs; {-# inline go #-}
  go' t t' = go (gjoin t) (gjoin t'); {-# inline go' #-}
  err      = throw (UnifyEx Conversion); {-# inline err #-}

  goBind t t' =
    let v = VLocalVar l SId
    in unify ms (l + 1) frz cs (gjoin $! appCl' ms t v)
                               (gjoin $! appCl' ms t' v)
  {-# inline goBind #-}

  guardCS cs = U.when (cs == CSFlex) $ throw $ UnifyEx CSFlexSolution
  {-# inline guardCS #-}

  in U.do
    -- turn off speculative conversion

    -- t  <- forceAll ms ftopt
    -- t' <- forceAll ms ftopt'
    t  <- forceCS ms cs ftopt
    t' <- forceCS ms cs ftopt'
    case (t, t') of

      -- rigid, canonical
      (VLocalVar x sp  , VLocalVar x' sp'   ) | x == x' -> unifySp ms l frz cs sp sp'
      (VLam _ t        , VLam _ t'          )           -> goBind t t'
      (VPi (NI _ i) a b, VPi (NI _ i') a' b') | i == i' -> go' a a' U.>> goBind b b'
      (VU              , VU                 )           -> U.pure ()

      (VFlex x sp, VFlex x' sp')
        | x == x'   -> unifySp ms l frz cs sp sp'
        | otherwise -> guardCS cs U.>> flexFlex ms l frz topt x sp topt' x' sp'

      (VUnfold h sp t, VUnfold h' sp' t') -> case cs of
        CSRigid | eqUH h h' -> unifySp ms l frz CSFlex sp sp'
                                 `catch` \_ -> unify ms l frz CSFull (gjoin t) (gjoin t')
                | otherwise -> unify ms l frz CSRigid (gjoin t) (gjoin t')
        CSFlex  | eqUH h h' -> unifySp ms l frz CSFlex sp sp'
                | otherwise -> err
        _       -> impossible

      (VIrrelevant, _          ) -> U.pure ()
      (_          , VIrrelevant) -> U.pure ()

      (VFlex x sp, t') -> U.do
        guardCS cs
        solve ms l frz x sp topt' `catch` \_ ->
          solveLong ms l frz x sp t'

      (t, VFlex x' sp') -> U.do
        guardCS cs
        solve ms l frz x' sp' topt `catch` \_ ->
          solveLong ms l frz x' sp' t

      (VUnfold h sp t, t') -> case cs of
        CSRigid -> go (G topt t) (G topt' t')
        CSFlex  -> err
        _       -> impossible
      (t, VUnfold h' sp' t') -> case cs of
        CSRigid -> go (G topt t) (G topt' t')
        CSFlex  -> err
        _       -> impossible

      (t, t') -> rigidEta ms l frz cs t t'
