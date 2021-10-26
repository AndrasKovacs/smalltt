{-# language UnboxedTuples, UnboxedSums #-}

module Evaluation (
  app, inlApp, appSp, appMask, eval, forceCS,
  forceF, forceFU, appCl, appCl', quote, quote0, eval0, nf0) where

import qualified Data.Array.Dynamic.L as ADL

import qualified UIO as U
import qualified LvlSet as LS
import Common
import CoreTypes
import IO
import MetaCxt

--------------------------------------------------------------------------------

-- TODO: inserted meta better evaluation (dep on solved/unsolved)

--------------------------------------------------------------------------------

localVar :: Env -> Ix -> Val
localVar (EDef _ v) 0 = v
localVar (EDef e _) x = localVar e (x - 1)
localVar _          _ = impossible

meta :: MetaCxt -> MetaVar -> Val
meta ms x = runIO do
  ADL.unsafeRead ms (coerce x) >>= \case
    MEUnsolved -> pure (VFlex x SId)
    MESolved v -> pure (VUnfold (UHSolved x) SId v)
{-# inline meta #-}

appCl' :: MetaCxt -> Closure -> Val -> Val
appCl' ms (Closure e t) u = let e' = EDef e u in eval' ms e' t
{-# inline appCl' #-}

appCl :: MetaCxt -> Closure -> Val -> Val
appCl ms (Closure e t) ~u = let e' = EDef e u in eval' ms e' t
{-# inline appCl #-}

app :: MetaCxt -> Val -> Val -> Icit -> Val
app ms t u i = case t of
  VLocalVar x sp   -> VLocalVar x (SApp sp u i)
  VUnfold   h sp v -> VUnfold h (SApp sp u i) (app ms v u i)
  VFlex     x sp   -> VFlex x (SApp sp u i)
  VLam _ _ t       -> appCl' ms t u
  _                -> impossible

inlApp :: MetaCxt -> Val -> Val -> Icit -> Val
inlApp ms t u i = case t of
  VLocalVar x sp   -> VLocalVar x (SApp sp u i)
  VUnfold   h sp v -> VUnfold h (SApp sp u i) (app ms v u i)
  VFlex     x sp   -> VFlex x (SApp sp u i)
  VLam _ _ t       -> appCl' ms t u
  _                -> impossible
{-# inline inlApp #-}

appSp :: MetaCxt -> Val -> Spine -> Val
appSp ms t = \case
  SId         -> t
  SApp sp u i -> inlApp ms (appSp ms t sp) u i

data ValLvl = ValLvl Val Lvl

appMask :: MetaCxt -> Env -> Val -> LS.LvlSet -> Val
appMask ms ~e v mask = (case go ms e v mask of ValLvl v _ -> v) where
  go :: MetaCxt -> Env -> Val -> LS.LvlSet -> ValLvl
  go ms ENil        v m = ValLvl v 0
  go ms (EDef e v') v m = case go ms e v m of
    ValLvl v i | LS.member i m -> ValLvl (inlApp ms v v' Expl) (i + 1)
               | otherwise     -> ValLvl v (i + 1)

data SpineLvl = SpineLvl Spine Lvl

maskEnv :: Env -> LS.LvlSet -> Spine
maskEnv e mask = (case go e mask of SpineLvl sp _ -> sp) where
  go :: Env -> LS.LvlSet -> SpineLvl
  go ENil        mask = SpineLvl SId 0
  go (EDef e v') mask = case go e mask of
    SpineLvl sp l | LS.member l mask -> SpineLvl (SApp sp v' Expl) (l + 1)
                  | otherwise        -> SpineLvl sp (l + 1)

insertedMeta :: MetaCxt -> Env -> MetaVar -> LS.LvlSet -> Val
insertedMeta ms ~e x mask = runIO do
  ADL.unsafeRead ms (coerce x) >>= \case
    MEUnsolved -> pure $! VFlex x (maskEnv e mask)
    MESolved v -> let sp = maskEnv e mask in pure $! VUnfold (UHSolved x) sp (appSp ms v sp)
{-# inline insertedMeta #-}

eval' :: MetaCxt -> Env -> Tm -> Val
eval' ms ~e = \case
  LocalVar x          -> localVar e x
  TopVar x v          -> VUnfold (UHTopVar x v) SId v
  Meta x              -> meta ms x
  App t u i           -> inlApp ms (eval' ms e t) (eval' ms e u) i
  Let _ _ t u         -> let ~vt = eval' ms e t; e' = EDef e vt in eval' ms e' u
  InsertedMeta x mask -> insertedMeta ms e x mask
  Lam x i t           -> VLam x i (Closure e t)
  Pi x i a b          -> VPi x i (eval' ms e a) (Closure e b)
  Irrelevant          -> VIrrelevant
  U                   -> VU

eval :: MetaCxt -> Env -> Tm -> Val
eval ms e t = eval' ms e t
{-# inline eval #-}

-- | Force metas only.
forceF :: MetaCxt -> Val -> U.IO Val
forceF ms = \case
  VFlex x sp -> forceFFlex ms x sp
  t          -> U.pure t
{-# inline forceF #-}

forceFFlex :: MetaCxt -> MetaVar -> Spine -> U.IO Val
forceFFlex ms x sp =
  U.io (ADL.read ms (coerce x)) U.>>= \case
    MEUnsolved -> U.pure (VFlex x sp)
    MESolved v -> case appSp ms v sp of
      VFlex x sp -> forceFFlex ms x sp
      v          -> U.pure v

-- | Force both metas and top unfoldings.
forceFU :: MetaCxt -> Val -> U.IO Val
forceFU ms = \case
  VFlex x sp     -> forceFUFlex ms x sp
  VUnfold _ sp v -> forceFU' ms v
  t              -> U.pure t
{-# inline forceFU #-}

forceFU' :: MetaCxt -> Val -> U.IO Val
forceFU' ms = \case
  VFlex x sp     -> forceFUFlex ms x sp
  VUnfold _ sp v -> forceFU' ms v
  t              -> U.pure t

forceFUFlex :: MetaCxt -> MetaVar -> Spine -> U.IO Val
forceFUFlex ms x sp =
  U.io (ADL.read ms (coerce x)) U.>>= \case
    MEUnsolved -> U.pure (VFlex x sp)
    MESolved v -> forceFU' ms $! appSp ms v sp
{-# noinline forceFUFlex #-}

forceCS :: MetaCxt -> ConvState -> Val -> U.IO Val
forceCS ms cs v = case cs of
  CSFull -> forceFU ms v
  _      -> forceF  ms v
{-# inline forceCS #-}

--------------------------------------------------------------------------------

quoteSp :: MetaCxt -> Lvl -> QuoteOption -> Tm -> Spine -> Tm
quoteSp ms l opt hd = \case
  SId         -> hd
  SApp sp t i -> App (quoteSp ms l opt hd sp) (quote ms l opt t) i

quote :: MetaCxt -> Lvl -> QuoteOption -> Val -> Tm
quote ms l opt t = let
  go       = quote ms l opt; {-# inline go #-}
  goSp     = quoteSp ms l opt; {-# inline goSp #-}
  goBind t = quote ms (l + 1) opt (appCl' ms t (VLocalVar l SId)); {-# inline goBind #-}

  cont = \case
    VFlex x sp                  -> goSp (Meta x) sp
    VUnfold (UHSolved x)   sp _ -> goSp (Meta x) sp
    VUnfold (UHTopVar x v) sp _ -> goSp (TopVar x v) sp
    VLocalVar x sp              -> goSp (LocalVar (lvlToIx l x)) sp
    VLam x i t                  -> Lam x i (goBind t)
    VPi x i a b                 -> Pi x i (go a) (goBind b)
    VU                          -> U
    VIrrelevant                 -> Irrelevant

  in case opt of
    UnfoldAll  -> cont (U.run (forceFU ms t))
    UnfoldFlex -> cont (U.run (forceF  ms t))
    _          -> cont t

--------------------------------------------------------------------------------

eval0 :: MetaCxt -> Tm -> Val
eval0 ms = eval ms ENil
{-# inline eval0 #-}

quote0 :: MetaCxt -> QuoteOption -> Val -> Tm
quote0 ms = quote ms 0
{-# inline quote0 #-}

nf0 :: MetaCxt -> QuoteOption -> Tm -> Tm
nf0 ms opt t = quote0 ms opt (eval0 ms t)
{-# inline nf0 #-}
