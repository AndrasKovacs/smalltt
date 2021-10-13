{-# language UnboxedTuples, UnboxedSums #-}

module Evaluation (
  app, inlApp, appSp, appMask, eval,
  forceF, forceFU, appCl, appCl', quote, quote0) where

import qualified Data.Array.Dynamic.L as ADL
import qualified EnvMask as EM

import Common
import CoreTypes
import IO
import MetaCxt

--------------------------------------------------------------------------------

localVar :: Env -> Ix -> Val
localVar (EDef _ v) 0 = v
localVar (EDef e _) x = localVar e (x - 1)
localVar _          _ = impossible

meta :: MetaCxt -> MetaVar -> Val
meta ms x = runIO do
  ADL.read ms (coerce x) >>= \case
    MEUnsolved -> pure (VFlex x SId)
    MESolved v -> pure (VUnfold (UHSolved x) SId v)
{-# inline meta #-}

appCl' :: MetaCxt -> Closure -> Val -> Val
appCl' ms (Closure e t) u = eval ms (EDef e u) t
{-# inline appCl' #-}

appCl :: MetaCxt -> Closure -> Val -> Val
appCl ms (Closure e t) ~u = eval ms (EDef e u) t
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

appMask :: MetaCxt -> Env -> Val -> EM.EnvMask -> Val
appMask ms e v mask = (case go ms e v mask of ValLvl v _ -> v) where
  go :: MetaCxt -> Env -> Val -> EM.EnvMask -> ValLvl
  go ms ENil        v m = ValLvl v 0
  go ms (EDef e v') v m = case go ms e v m of
    ValLvl v i -> EM.looked i m
      (ValLvl v (i + 1))
      (\icit -> ValLvl (inlApp ms v v' icit) (i + 1))

eval :: MetaCxt -> Env -> Tm -> Val
eval ms e = \case
  LocalVar x          -> localVar e x
  TopVar x v          -> VUnfold (UHTopVar x v) SId v
  Meta x              -> meta ms x
  App t u i           -> inlApp ms (eval ms e t) (eval ms e u) i
  Let _ _ t u         -> let ~vt = eval ms e t in eval ms (EDef e vt) u
  InsertedMeta x mask -> appMask ms e $$! meta ms x $$! mask
  Lam x i t           -> VLam x i (Closure e t)
  Pi x i a b          -> VPi x i (eval ms e a) (Closure e b)
  Irrelevant          -> VIrrelevant
  U                   -> VU

-- | Force metas only.
forceF :: MetaCxt -> Val -> Val
forceF ms = \case
  VFlex x sp -> forceFFlex ms x sp
  t          -> t
{-# inline forceF #-}

forceFFlex :: MetaCxt -> MetaVar -> Spine -> Val
forceFFlex ms x sp = runIO do
  ADL.read ms (coerce x) >>= \case
    MEUnsolved -> pure $! VFlex x sp
    MESolved v -> case appSp ms v sp of
      VFlex x sp -> pure $! forceFFlex ms x sp
      v          -> pure v

-- | Force both metas and top unfoldings.
forceFU :: MetaCxt -> Val -> Val
forceFU ms = \case
  VFlex x sp     -> forceFUFlex ms x sp
  VUnfold _ sp v -> forceFU' ms v
  t              -> t
{-# inline forceFU #-}

forceFU' :: MetaCxt -> Val -> Val
forceFU' ms = \case
  VFlex x sp     -> forceFUFlex ms x sp
  VUnfold _ sp v -> forceFU' ms v
  t              -> t

forceFUFlex :: MetaCxt -> MetaVar -> Spine -> Val
forceFUFlex ms x sp = runIO do
  ADL.read ms (coerce x) >>= \case
    MEUnsolved -> pure $ VFlex x sp
    MESolved v -> pure $! forceFU' ms $! appSp ms v sp
{-# noinline forceFUFlex #-}

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

  force t = case opt of UnfoldAll  -> forceFU ms t
                        UnfoldFlex -> forceF ms t
                        _          -> t
  {-# inline force #-}

  in case force t of
    VFlex x sp                  -> goSp (Meta x) sp
    VUnfold (UHSolved x)   sp _ -> goSp (Meta x) sp
    VUnfold (UHTopVar x v) sp _ -> goSp (TopVar x v) sp
    VLocalVar x sp              -> goSp (LocalVar (lvlToIx l x)) sp
    VLam x i t                  -> Lam x i (goBind t)
    VPi x i a b                 -> Pi x i (go a) (goBind b)
    VU                          -> U
    VIrrelevant                 -> Irrelevant

quote0 :: MetaCxt -> QuoteOption -> Val -> Tm
quote0 ms opt v = quote ms 0 opt v
{-# inline quote0 #-}
