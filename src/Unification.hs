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

-- | Forcing depending on conversion state.
forceCS :: MetaCxt -> ConvState -> Val -> U.IO Val
forceCS cxt cs v = case cs of
  Full -> forceAll cxt v
  _    -> force    cxt v
{-# inline forceCS #-}


-- PARTIAL RENAMINGS
--------------------------------------------------------------------------------

data PartialRenaming = PRen {
    occ :: MetaVar          -- ^ Occurring meta to be checked.
  , dom :: Lvl              -- ^ Domain context size (context of output term)
  , cod :: Lvl              -- ^ Codomain context size (context of input value)
  , ren :: AFM.Array Lvl    -- ^ Partial mapping from cod vars to dom vars,
                            --   (-1) denotes an undefined value. Indices above the
                            --   array length are considered to be mapped to themselves.
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

-- | Lift a renaming over a bound variable. The new var is mapped to itself.
lift :: PartialRenaming -> PartialRenaming
lift (PRen m dom cod ren) = PRen m (dom + 1) (cod + 1) ren
{-# inline lift #-}


-- SOLUTION CHECKING
--------------------------------------------------------------------------------

CAN_IO2((Tm,UBool), LiftedRep, IntRep, Tm, Int#, (x, UBool# (I# y)), CoeTmUBool)

approxOccursInSolution :: MetaCxt -> MetaVar -> MetaVar -> MetaVar -> U.IO UBool
approxOccursInSolution ms frz occ x
  | x < frz   = U.pure UTrue
  | otherwise = MC.read ms x U.>>= \case
      Unsolved _ | occ == x  -> U.pure UFalse
                 | otherwise -> U.pure UTrue
      Solved cache _ t _ -> U.do
        cached <- U.io $ RF.read cache
        if cached == occ then
          U.pure UTrue
        else U.do
          res <- approxOccurs ms frz occ t
          U.when (res == UTrue) (U.io $ RF.write cache occ)
          U.pure res

approxOccurs :: MetaCxt -> MetaVar -> MetaVar -> Tm -> U.IO UBool
approxOccurs ms frz occ t = let
  go = approxOccurs ms frz occ; {-# inline go #-}
  in case t of
    LocalVar x     -> U.pure UTrue
    TopVar x _     -> U.pure UTrue
    Let x a t u    -> (\x y z -> x &&# y &&# z) U.<$> go a U.<*> go t U.<*> go u
    App t u i      -> (&&#) U.<$> go t U.<*> go u
    Lam _ t        -> go t
    InsertedMeta x -> approxOccursInSolution ms frz occ x
    Meta x         -> approxOccursInSolution ms frz occ x
    Pi _ a b       -> (&&#) U.<$> go a U.<*> go b
    Irrelevant     -> U.pure UTrue
    U              -> U.pure UTrue

rigidQuoteSp :: MetaCxt -> MetaVar -> PartialRenaming -> Tm -> Spine -> U.IO Tm
rigidQuoteSp ms frz pren hd = \case
  SId         -> U.pure hd
  SApp sp t i -> App U.<$> rigidQuoteSp ms frz pren hd sp
                     U.<*> rigidQuote ms frz pren t
                     U.<*> U.pure i

rigidQuote :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> U.IO Tm
rigidQuote ms frz pren t = let
  go       = rigidQuote ms frz pren; {-# inline go #-}
  goSp     = rigidQuoteSp ms frz pren; {-# inline goSp #-}
  goSpFlex = flexQuoteSp ms frz pren; {-# inline goSpFlex #-}
  goBind t = rigidQuote ms frz (lift pren) (appCl' ms t (VLocalVar (cod pren) SId))
  {-# inline goBind #-}

  in force ms t U.>>= \case
    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        U.io (AFM.read (ren pren) (coerce x)) U.>>= \case
          (-1) -> throw $ UnifyEx Conversion -- scope check
          y    -> goSp (LocalVar (lvlToIx (dom pren) y)) sp
      | otherwise ->
        -- TODO: simplify arith expr here (LocalVar (cod pren - x - 1))
        goSp (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren)))) sp

    VFlex x sp
      | occ pren == x -> throw $ UnifyEx Conversion -- occurs check
      | otherwise     -> goSp (Meta x) sp

    topt@(VUnfold h sp t) -> U.do
      (t, tValid) <- case h of    -- WARNING: Core was fine here, but should be checked on ghc change
        UHTopVar x v -> U.do
          goSpFlex (TopVar x (coerce v) // UTrue) sp
        UHSolved x -> U.do
          xValid <- approxOccursInSolution ms frz (occ pren) x
          goSpFlex (Meta x // xValid) sp

      U.when (tValid == UFalse) $
        fullCheckRhs ms frz pren topt

      U.pure t

    VLam xi t   -> Lam xi U.<$> goBind t
    VPi xi a b  -> Pi xi U.<$> go a U.<*> goBind b
    VU          -> U.pure U
    VIrrelevant -> U.pure Irrelevant

flexQuoteSp :: MetaCxt -> MetaVar -> PartialRenaming -> (Tm, UBool) -> Spine -> U.IO (Tm, UBool)
flexQuoteSp ms frz pren hd@(t, !tValid) = \case
  SId         -> U.pure hd
  SApp sp t i -> U.do
    (sp, spValid) <- flexQuoteSp ms frz pren hd sp
    (t, tValid)   <- flexQuote   ms frz pren t
    U.pure (App sp t i // spValid &&# tValid)

flexQuote :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> U.IO (Tm, UBool)
flexQuote ms frz pren t = let
  go       = flexQuote ms frz pren; {-# inline go #-}
  goSp     = flexQuoteSp ms frz pren; {-# inline goSp #-}
  goBind t = flexQuote ms frz (lift pren) (appCl' ms t (VLocalVar (cod pren) SId))
  {-# inline goBind #-}

  in force ms t U.>>= \case
    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        U.io (AFM.read (ren pren) (coerce x)) U.>>= \case
          (-1) -> U.pure (Irrelevant, UFalse)
          y    -> goSp (LocalVar (lvlToIx (dom pren) y) // UTrue) sp
      | otherwise ->
        -- TODO: simplify arith expr here (LocalVar (cod pren - x - 1))
        goSp (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren))) // UTrue) sp

    VFlex x sp
      | occ pren == x -> U.pure (Irrelevant, UFalse)
      | otherwise     -> goSp (Meta x // UTrue) sp

    topt@(VUnfold h sp t) -> U.do
      (t, tf) <- case h of    -- WARNING: Core was fine here, but should be checked on ghc change
        UHTopVar x v -> U.do
          goSp (TopVar x (coerce v) // UTrue) sp
        UHSolved x -> U.do
          xf <- approxOccursInSolution ms frz (occ pren) x
          goSp (Meta x // xf) sp

      U.when (tf == UFalse) $
        fullCheckRhs ms frz pren topt

      U.pure (t // UTrue)

    VLam xi t -> U.do
      (t, tValid) <- goBind t
      U.pure (Lam xi t // tValid)

    VPi xi a b -> U.do
      (a, aValid) <- go a
      (b, bValid) <- goBind b
      U.pure (Pi xi a b // aValid &&# bValid)

    VU          -> U.pure (U // UTrue)
    VIrrelevant -> U.pure (Irrelevant // UTrue)

fullCheckSp :: MetaCxt -> MetaVar -> PartialRenaming -> Spine -> U.IO ()
fullCheckSp ms frz pren = \case
  SId         -> U.pure ()
  SApp sp t i -> fullCheckSp ms frz pren sp U.>> fullCheckRhs ms frz pren t

fullCheckRhs :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> U.IO ()
fullCheckRhs ms frz pren v = U.do
  let go       = fullCheckRhs ms frz pren;  {-# inline go #-}
      goSp     = fullCheckSp ms frz pren;   {-# inline goSp #-}
      goBind t = fullCheckRhs ms frz (lift pren)
                    (appCl' ms t (VLocalVar (cod pren) SId))
      {-# inline goBind #-}

  forceAll ms v U.>>= \case

    VFlex m' sp | occ pren == m' -> throw $ UnifyEx Conversion -- occurs check
                | otherwise      -> goSp sp

    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        U.io (AFM.read (ren pren) (coerce x)) U.>>= \case
          (-1) -> throw $ UnifyEx Conversion -- scope check
          y    -> goSp sp
      | otherwise ->
        goSp sp

    VLam _ t    -> goBind t
    VPi _ a b   -> go a U.>> goBind b
    VUnfold{}   -> impossible
    VU          -> U.pure ()
    VIrrelevant -> U.pure ()


-- UNIFICATION
--------------------------------------------------------------------------------

-- | Invert a spine, producing a partial renaming. The "trim" argument is the
--   set of vars that we already dropped by eta-contracting the two sides.
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

-- | Try to eta contract both sides, bind trimmed lhs, rhs, and the set of
--   variables that were trimmed.
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
    rhs <- lams sp U.<$> rigidQuote ms frz pren rhs
    debug ["renamed", show rhs]
    debug ["solve", show x, show pren, show rhs]
    MC.solve ms x rhs (eval ms ENil rhs)

-- | Try to solve a meta, but fully eta-expand sides.
solveLong :: MetaCxt -> Lvl -> MetaVar -> MetaVar -> Spine -> Val -> U.IO ()
solveLong ms l frz x sp rhs = forceAll ms rhs U.>>= \case
  VLam (NI _ i) t ->
    let v = VLocalVar l SId
    in solveLong ms (l + 1) frz x (SApp sp v i) (appCl' ms t v)
  VFlex x' sp' | x == x'   -> unifySp ms l frz Full sp sp'
               | otherwise -> flexFlex ms l frz (VFlex x sp) x sp rhs x' sp'
  _ ->
    solve ms l frz x sp rhs

flexFlex :: MetaCxt -> Lvl -> MetaVar -> Val -> MetaVar -> Spine -> Val -> MetaVar -> Spine -> U.IO ()
flexFlex ms l frz t x ~sp t' x' ~sp' =
  solve ms l frz x sp t' `catch` \_ ->
  solve ms l frz x' sp' t

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

  guardCS cs = U.when (cs == Flex) $ throw $ UnifyEx FlexSolution
  {-# inline guardCS #-}

  in U.do
    -- turn off speculative conversion here:

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
        Rigid | eqUH h h' -> unifySp ms l frz Flex sp sp'
                                `catch` \_ -> unify ms l frz Full (gjoin t) (gjoin t')
              | otherwise -> unify ms l frz Rigid (gjoin t) (gjoin t')
        Flex  | eqUH h h' -> unifySp ms l frz Flex sp sp'
              | otherwise -> err
        _                 -> impossible

      (VFlex x sp, t') -> U.do
        guardCS cs
        solve ms l frz x sp topt' `catch` \_ ->
          solveLong ms l frz x sp t'

      (t, VFlex x' sp') -> U.do
        guardCS cs
        solve ms l frz x' sp' topt `catch` \_ ->
          solveLong ms l frz x' sp' t

      (VUnfold h sp t, t') -> case cs of
        Rigid -> go (G topt t) (G topt' t')
        Flex  -> err
        _     -> impossible
      (t, VUnfold h' sp' t') -> case cs of
        Rigid -> go (G topt t) (G topt' t')
        Flex  -> err
        _     -> impossible

      (t, t') -> unifyCold ms l frz cs t t'


-- | Function factored out to handle `Irrelevant` values and eta-conversion
--   cases. These are quite rare, so it seems to be a good idea to remove them
--   from hot code.
unifyCold :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Val -> Val -> U.IO ()
unifyCold ms l frz cs ~t ~t' = case (t, t') of

  (VIrrelevant, _          ) -> U.pure ()
  (_          , VIrrelevant) -> U.pure ()

  (VLocalVar x sp, VLam (NI _ i) t')  ->
    let v = VLocalVar l SId
    in unifySpCold ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  (VLam (NI _ i) t, VLocalVar x' sp') ->
    let v = VLocalVar l SId
    in unifySpCold ms (l + 1) frz cs x' (SApp sp' v i) (appCl' ms t v)
  _ ->
    throw (UnifyEx Conversion)
{-# noinline unifyCold #-}

unifySpCold :: MetaCxt -> Lvl -> MetaVar -> ConvState -> Lvl -> Spine -> Val -> U.IO ()
unifySpCold ms l frz cs x sp v = forceCS ms cs v U.>>= \case
  VIrrelevant ->
    U.pure ()
  VLam (NI _ i) t' ->
    let v = VLocalVar l SId
    in unifySpCold ms (l + 1) frz cs x (SApp sp v i) (appCl' ms t' v)
  VLocalVar x' sp' | x == x' ->
    unifySp ms l frz cs sp sp'
  _ ->
    throw (UnifyEx Conversion)
