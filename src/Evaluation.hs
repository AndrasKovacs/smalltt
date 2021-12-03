{-# language UnboxedTuples, UnboxedSums #-}

module Evaluation (
  app, inlApp, appSp, eval, force, forceAll, forceMetas, forceTop, appCl,
  appCl', quote, quote0, eval0, nf0, zonk
  ) where

import qualified LvlSet as LS
import qualified MetaCxt as MC
import qualified UIO as U
import Common
import CoreTypes

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
  TopVar x v     -> VUnfold (UHTopVar x (coerce v)) SId (coerce v)
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

--------------------------------------------------------------------------------

-- | Eliminate newly solved VFlex-es from the head.
force :: MetaCxt -> Val -> U.IO Val
force cxt = \case
  xsp@(VFlex x sp) -> force' cxt x sp xsp
  t                -> U.pure t
{-# inline force #-}

force' :: MetaCxt -> MetaVar -> Spine -> Val -> U.IO Val
force' cxt x sp ~xsp =
  MC.read cxt x U.>>= \case
    Unsolved _     -> U.pure xsp
    Solved _ _ _ v -> U.pure (VUnfold (UHSolved x) sp (appSp cxt v sp))
{-# noinline force' #-}

-- | Force + eliminate all unfoldings from the head.
forceAll :: MetaCxt -> Val -> U.IO Val
forceAll cxt = \case
  xsp@(VFlex x sp)-> forceAllFlex cxt x sp xsp
  VUnfold _ sp v  -> forceAll' cxt v
  t               -> U.pure t
{-# inline forceAll #-}

forceAll' :: MetaCxt -> Val -> U.IO Val
forceAll' cxt = \case
  xsp@(VFlex x sp) -> forceAllFlex cxt x sp xsp
  VUnfold _ sp v   -> forceAll' cxt v
  t                -> U.pure t

forceAllFlex :: MetaCxt -> MetaVar -> Spine -> Val -> U.IO Val
forceAllFlex cxt x sp ~xsp =
  MC.read cxt x U.>>= \case
    Unsolved _     -> U.pure xsp
    Solved _ _ _ v -> forceAll' cxt $! appSp cxt v sp
{-# noinline forceAllFlex #-}

-- | Force + eliminate all top def unfolding from the head.
forceTop :: MetaCxt -> Val -> U.IO Val
forceTop cxt = \case
  xsp@(VFlex x sp)        -> forceTopFlex cxt x sp xsp
  VUnfold UHTopVar{} sp v -> forceTop' cxt v
  t                       -> U.pure t
{-# inline forceTop #-}

forceTop' :: MetaCxt -> Val -> U.IO Val
forceTop' cxt = \case
  xsp@(VFlex x sp)       -> forceTopFlex cxt x sp xsp
  VUnfold UHTopVar{} _ v -> forceTop' cxt v
  t                      -> U.pure t

forceTopFlex :: MetaCxt -> MetaVar -> Spine -> Val -> U.IO Val
forceTopFlex cxt x sp ~xsp =
  MC.read cxt x U.>>= \case
    Unsolved _     -> U.pure xsp
    Solved _ _ _ v -> forceTop' cxt $! appSp cxt v sp
{-# noinline forceTopFlex #-}

-- | Force + eliminate all top def unfolding from the head.
forceMetas :: MetaCxt -> Val -> U.IO Val
forceMetas cxt = \case
  xsp@(VFlex x sp)        -> forceMetasFlex cxt x sp xsp
  VUnfold UHSolved{} sp v -> forceMetas' cxt v
  t                       -> U.pure t
{-# inline forceMetas #-}

forceMetas' :: MetaCxt -> Val -> U.IO Val
forceMetas' cxt = \case
  xsp@(VFlex x sp)       -> forceMetasFlex cxt x sp xsp
  VUnfold UHSolved{} _ v -> forceMetas' cxt v
  t                      -> U.pure t

forceMetasFlex :: MetaCxt -> MetaVar -> Spine -> Val -> U.IO Val
forceMetasFlex cxt x sp ~xsp =
  MC.read cxt x U.>>= \case
    Unsolved _     -> U.pure xsp
    Solved _ _ _ v -> forceMetas' cxt $! appSp cxt v sp
{-# noinline forceMetasFlex #-}

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
    VUnfold (UHTopVar x v) sp _ -> goSp (TopVar x (coerce v)) sp
    VLocalVar x sp              -> goSp (LocalVar (lvlToIx l x)) sp
    VLam xi t                   -> Lam xi (goBind t)
    VPi xi a b                  -> Pi xi (go a) (goBind b)
    VU                          -> U
    VIrrelevant                 -> Irrelevant

  in case opt of
    UnfoldAll   -> cont (U.run (forceAll   cxt t))
    UnfoldTop   -> cont (U.run (forceTop   cxt t))
    UnfoldMetas -> cont (U.run (forceMetas cxt t))
    _           -> cont t

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


-- Zonking (unfolding all metas in terms, but otherwise trying to minimize output)
--------------------------------------------------------------------------------

zonkApps :: MetaCxt -> Env -> Lvl -> Tm -> (# Tm | Val #)
zonkApps ms env l = \case
  Meta x    -> let t = meta ms x in (# | t #)
  App t u i -> case zonkApps ms env l t of
                 (# t | #) -> let u' = zonk ms env l u in (# App t u' i | #)
                 (# | t #) -> let t' = inlApp ms t (eval ms env u) i in (# | t' #)
  t         -> let t' = zonk ms env l t in (# t' | #)

zonk :: MetaCxt -> Env -> Lvl -> Tm -> Tm
zonk ms env l t = let
  go     = zonk ms env l; {-# inline go #-}
  goBind = zonk ms (EDef env (VLocalVar l SId)) (l + 1); {-# inline goBind #-}
  goApps = zonkApps ms env l; {-# inline goApps #-}
  quote  = Evaluation.quote ms l UnfoldMetas; {-# inline quote #-}
  in case t of
    LocalVar x     -> LocalVar x
    TopVar x v     -> TopVar x v
    Let x a t u    -> Let x (go a) (go t) (goBind u)
    App t u i      -> case goApps t of
                        (# t | #) -> App t (go u) i
                        (# | t #) -> quote $ inlApp ms t (eval ms env u) i
    Lam xi t       -> Lam xi (goBind t)
    InsertedMeta x -> U.run $ MC.read ms x U.>>= \case
                        Unsolved _     ->
                          U.pure (InsertedMeta x)
                        Solved _ mask _ v ->
                          U.pure $ quote $ appSp ms v (maskEnv env mask)
    Meta x         -> quote $ meta ms x
    Pi xi a b      -> Pi xi (go a) (goBind b)
    Irrelevant     -> Irrelevant
    U              -> U
