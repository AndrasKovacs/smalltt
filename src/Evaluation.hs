{-# language UnboxedTuples, UnboxedSums #-}

module Evaluation (
  app, inlApp, appSp, eval, forceCS,
  forceF, forceFU, appCl, appCl', quote, quote0, eval0, nf0) where

import qualified LvlSet as LS
import qualified MetaCxt as MC
import qualified UIO as U
import Common
import CoreTypes

--------------------------------------------------------------------------------

-- TODO: inserted meta better evaluation (dep on solved/unsolved)

--------------------------------------------------------------------------------

localVar :: Env -> Ix -> Val
localVar (EDef _ v) 0 = v
localVar (EDef e _) x = localVar e (x - 1)
localVar _          _ = impossible

meta :: MetaCxt -> MetaVar -> Val
meta cxt x = U.run U.do
  MC.read cxt x U.>>= \case
    Unsolved _     -> U.pure (VFlex x SId)
    Solved _ _ _ v -> U.pure (VUnfold (UHSolved x) SId v)
{-# inline meta #-}

appCl' :: MetaCxt -> Closure -> Val -> Val
appCl' cxt (Closure e t) u = let e' = EDef e u in eval' cxt e' t
{-# inline appCl' #-}

appCl :: MetaCxt -> Closure -> Val -> Val
appCl cxt (Closure e t) ~u = let e' = EDef e u in eval' cxt e' t
{-# inline appCl #-}

app :: MetaCxt -> Val -> Val -> Icit -> Val
app cxt t u i = case t of
  VLocalVar x sp   -> VLocalVar x (SApp sp u i)
  VUnfold   h sp v -> VUnfold h (SApp sp u i) (app cxt v u i)
  VFlex     x sp   -> VFlex x (SApp sp u i)
  VLam _ t         -> appCl' cxt t u
  VIrrelevant      -> VIrrelevant
  _                -> impossible

inlApp :: MetaCxt -> Val -> Val -> Icit -> Val
inlApp cxt t u i = case t of
  VLocalVar x sp   -> VLocalVar x (SApp sp u i)
  VUnfold   h sp v -> VUnfold h (SApp sp u i) (app cxt v u i)
  VFlex     x sp   -> VFlex x (SApp sp u i)
  VLam _ t         -> appCl' cxt t u
  VIrrelevant      -> VIrrelevant
  _                -> impossible
{-# inline inlApp #-}

appSp :: MetaCxt -> Val -> Spine -> Val
appSp cxt t = \case
  SId         -> t
  SApp sp u i -> inlApp cxt (appSp cxt t sp) u i

data SpineLvl = SpineLvl Spine Lvl

maskEnv :: Env -> LS.LvlSet -> Spine
maskEnv e mask = (case go e mask of SpineLvl sp _ -> sp) where
  go :: Env -> LS.LvlSet -> SpineLvl
  go ENil        mask = SpineLvl SId 0
  go (EDef e v') mask = case go e mask of
    SpineLvl sp l | LS.member l mask -> SpineLvl (SApp sp v' Expl) (l + 1)
                  | otherwise        -> SpineLvl sp (l + 1)

-- -- In this case we know that there must be enough lambdas to eat the whole spine
-- -- EDIT: but with eta contracted meta solutions, we don't necessarily have!
-- appMaskedEnv :: MetaCxt -> Tm -> Val -> Spine -> Val
-- appMaskedEnv ms t ~v sp = let
--   go t           SId           = Closure ENil t
--   go (Lam _ _ t) (SApp sp u _) = case go t sp of
--     Closure env t -> Closure (EDef env u) t
--   go _ _ = impossible

--   in case sp of
--     SId -> v
--     sp  -> case go t sp of Closure env t -> eval ms env t

insertedMeta :: MetaCxt -> Env -> MetaVar -> Val
insertedMeta cxt ~e x = U.run do
  MC.read cxt x U.>>= \case
    Unsolved mask     ->
      U.pure (VFlex x (maskEnv e mask))
    Solved _ mask t v ->
      let sp = maskEnv e mask
      in U.pure (VUnfold (UHSolved x) sp (appSp cxt v sp))
{-# inline insertedMeta #-}

eval' :: MetaCxt -> Env -> Tm -> Val
eval' cxt ~e = \case
  LocalVar x     -> localVar e x
  TopVar x v     -> VUnfold (UHTopVar x v) SId v
  Meta x         -> meta cxt x
  App t u i      -> inlApp cxt (eval' cxt e t) (eval' cxt e u) i
  Let _ _ t u    -> let ~vt = eval' cxt e t; e' = EDef e vt in eval' cxt e' u
  InsertedMeta x -> insertedMeta cxt e x
  Lam xi t       -> VLam xi (Closure e t)
  Pi xi a b      -> VPi xi (eval' cxt e a) (Closure e b)
  Irrelevant     -> VIrrelevant
  U              -> VU

eval :: MetaCxt -> Env -> Tm -> Val
eval cxt e t = eval' cxt e t
{-# inline eval #-}

-- | Force metas only.
forceF :: MetaCxt -> Val -> U.IO Val
forceF cxt = \case
  t@(VFlex x sp) -> forceFFlex cxt t x sp
  t              -> U.pure t
{-# inline forceF #-}

forceFFlex :: MetaCxt -> Val -> MetaVar -> Spine -> U.IO Val
forceFFlex cxt t x sp =
  MC.read cxt x U.>>= \case
    Unsolved _     -> U.pure t
    Solved _ _ _ v -> U.pure (VUnfold (UHSolved x) sp (appSp cxt v sp))
{-# noinline forceFFlex #-}

-- | Force both metas and top unfoldings.
forceFU :: MetaCxt -> Val -> U.IO Val
forceFU cxt = \case
  VFlex x sp     -> forceFUFlex cxt x sp
  VUnfold _ sp v -> forceFU' cxt v
  t              -> U.pure t
{-# inline forceFU #-}

forceFU' :: MetaCxt -> Val -> U.IO Val
forceFU' cxt = \case
  VFlex x sp     -> forceFUFlex cxt x sp
  VUnfold _ sp v -> forceFU' cxt v
  t              -> U.pure t

forceFUFlex :: MetaCxt -> MetaVar -> Spine -> U.IO Val
forceFUFlex cxt x sp =
  MC.read cxt x U.>>= \case
    Unsolved _     -> U.pure (VFlex x sp)
    Solved _ _ _ v -> forceFU' cxt $! appSp cxt v sp
{-# noinline forceFUFlex #-}

forceCS :: MetaCxt -> ConvState -> Val -> U.IO Val
forceCS cxt cs v = case cs of
  CSFull -> forceFU cxt v
  _      -> forceF  cxt v
{-# inline forceCS #-}

--------------------------------------------------------------------------------

quoteSp :: MetaCxt -> Lvl -> QuoteOption -> Tm -> Spine -> Tm
quoteSp cxt l opt hd = \case
  SId         -> hd
  SApp sp t i -> App (quoteSp cxt l opt hd sp) (quote cxt l opt t) i

quote :: MetaCxt -> Lvl -> QuoteOption -> Val -> Tm
quote cxt l opt t = let
  go       = quote cxt l opt; {-# inline go #-}
  goSp     = quoteSp cxt l opt; {-# inline goSp #-}
  goBind t = quote cxt (l + 1) opt (appCl' cxt t (VLocalVar l SId)); {-# inline goBind #-}

  cont = \case
    VFlex x sp                  -> goSp (Meta x) sp
    VUnfold (UHSolved x)   sp _ -> goSp (Meta x) sp
    VUnfold (UHTopVar x v) sp _ -> goSp (TopVar x v) sp
    VLocalVar x sp              -> goSp (LocalVar (lvlToIx l x)) sp
    VLam xi t                   -> Lam xi (goBind t)
    VPi xi a b                  -> Pi xi (go a) (goBind b)
    VU                          -> U
    VIrrelevant                 -> Irrelevant

  in case opt of
    UnfoldAll  -> cont (U.run (forceFU cxt t))
    UnfoldFlex -> cont (U.run (forceF  cxt t))
    _          -> cont t

--------------------------------------------------------------------------------

eval0 :: MetaCxt -> Tm -> Val
eval0 cxt = eval cxt ENil
{-# inline eval0 #-}

quote0 :: MetaCxt -> QuoteOption -> Val -> Tm
quote0 cxt = quote cxt 0
{-# inline quote0 #-}

nf0 :: MetaCxt -> QuoteOption -> Tm -> Tm
nf0 cxt opt t = quote0 cxt opt (eval0 cxt t)
{-# inline nf0 #-}
