
module Evaluation (
  app, inlApp, appSp, eval, force, forceAll, forceMetas, appCl,
  appCl', quote, quote0, eval0, nf0, zonk
  ) where

import qualified LvlSet as LS
import qualified MetaCxt as MC
import Common
import CoreTypes

--------------------------------------------------------------------------------

localVar :: Env -> Ix -> Val
localVar (EDef _ v) 0 = v
localVar (EDef e _) x = localVar e (x - 1)
localVar _          _ = impossible

meta :: MetaCxt -> MetaVar -> Val
meta ms x = runIO do
  MC.read ms x >>= \case
    Unsolved _     -> pure (VFlex x SId)
    Solved _ _ _ v -> pure (VUnfold (UHSolved x) SId v)
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
  VLam _ t         -> appCl' ms t u
  VIrrelevant      -> VIrrelevant
  _                -> impossible

inlApp :: MetaCxt -> Val -> Val -> Icit -> Val
inlApp ms t u i = case t of
  VLocalVar x sp   -> VLocalVar x (SApp sp u i)
  VUnfold   h sp v -> VUnfold h (SApp sp u i) (app ms v u i)
  VFlex     x sp   -> VFlex x (SApp sp u i)
  VLam _ t         -> appCl' ms t u
  VIrrelevant      -> VIrrelevant
  _                -> impossible
{-# inline inlApp #-}

appSp :: MetaCxt -> Val -> Spine -> Val
appSp ms t = \case
  SId         -> t
  SApp sp u i -> inlApp ms (appSp ms t sp) u i

data SpineLvl = SpineLvl Spine Lvl

-- | Pick the values from an `Env` which are in a `LS.LvlSet`.
maskEnv :: Env -> LS.LvlSet -> Spine
maskEnv e mask = (case go e mask of SpineLvl sp _ -> sp) where
  go :: Env -> LS.LvlSet -> SpineLvl
  go ENil        mask = SpineLvl SId 0
  go (EDef e v') mask = case go e mask of
    SpineLvl sp l | LS.member l mask -> SpineLvl (SApp sp v' Expl) (l + 1)
                  | otherwise        -> SpineLvl sp (l + 1)

insertedMeta :: MetaCxt -> Env -> MetaVar -> Val
insertedMeta ms ~e x = runIO do
  MC.read ms x >>= \case
    Unsolved mask     ->
      pure (VFlex x (maskEnv e mask))
    Solved _ mask t v ->
      let sp = maskEnv e mask
      in pure (VUnfold (UHSolved x) sp (appSp ms v sp))
{-# inline insertedMeta #-}

eval' :: MetaCxt -> Env -> Tm -> Val
eval' ms ~e = \case
  LocalVar x     -> localVar e x
  TopVar x v     -> VUnfold (UHTopVar x (coerce v)) SId (coerce v)
  Meta x         -> meta ms x
  App t u i      -> inlApp ms (eval' ms e t) (eval' ms e u) i
  Let _ _ t u    -> let ~vt = eval' ms e t; e' = EDef e vt in eval' ms e' u
  InsertedMeta x -> insertedMeta ms e x
  Lam xi t       -> VLam xi (Closure e t)
  Pi xi a b      -> VPi xi (eval' ms e a) (Closure e b)
  Irrelevant     -> VIrrelevant
  U              -> VU

eval :: MetaCxt -> Env -> Tm -> Val
eval ms e t = eval' ms e t
{-# inline eval #-}

-- Forcing
--------------------------------------------------------------------------------

-- | Convert solved VFlex-es to Unfold in the head.
force :: MetaCxt -> Val -> IO Val
force ms = \case
  xsp@(VFlex x sp) -> force' ms x sp xsp
  t                -> pure t
{-# inline force #-}

force' :: MetaCxt -> MetaVar -> Spine -> Val -> IO Val
force' ms x sp ~xsp =
  MC.read ms x >>= \case
    Unsolved _     -> pure xsp
    Solved _ _ _ v -> pure (VUnfold (UHSolved x) sp (appSp ms v sp))
{-# noinline force' #-}

-- | Eliminate all unfoldings from the head.
forceAll :: MetaCxt -> Val -> IO Val
forceAll ms = \case
  xsp@(VFlex x sp)-> forceAllFlex ms x sp xsp
  VUnfold _ sp v  -> forceAll' ms v
  t               -> pure t
{-# inline forceAll #-}

forceAll' :: MetaCxt -> Val -> IO Val
forceAll' ms = \case
  xsp@(VFlex x sp) -> forceAllFlex ms x sp xsp
  VUnfold _ sp v   -> forceAll' ms v
  t                -> pure t

forceAllFlex :: MetaCxt -> MetaVar -> Spine -> Val -> IO Val
forceAllFlex ms x sp ~xsp =
  MC.read ms x >>= \case
    Unsolved _     -> pure xsp
    Solved _ _ _ v -> forceAll' ms $! appSp ms v sp
{-# noinline forceAllFlex #-}

-- | Eliminate all meta unfoldings from the head.
forceMetas :: MetaCxt -> Val -> IO Val
forceMetas ms = \case
  xsp@(VFlex x sp)        -> forceMetasFlex ms x sp xsp
  VUnfold UHSolved{} sp v -> forceMetas' ms v
  t                       -> pure t
{-# inline forceMetas #-}

forceMetas' :: MetaCxt -> Val -> IO Val
forceMetas' ms = \case
  xsp@(VFlex x sp)       -> forceMetasFlex ms x sp xsp
  VUnfold UHSolved{} _ v -> forceMetas' ms v
  t                      -> pure t

forceMetasFlex :: MetaCxt -> MetaVar -> Spine -> Val -> IO Val
forceMetasFlex ms x sp ~xsp =
  MC.read ms x >>= \case
    Unsolved _     -> pure xsp
    Solved _ _ _ v -> forceMetas' ms $! appSp ms v sp
{-# noinline forceMetasFlex #-}

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
    VUnfold (UHTopVar x v) sp _ -> goSp (TopVar x (coerce v)) sp
    VLocalVar x sp              -> goSp (LocalVar (lvlToIx l x)) sp
    VLam xi t                   -> Lam xi (goBind t)
    VPi xi a b                  -> Pi xi (go a) (goBind b)
    VU                          -> U
    VIrrelevant                 -> Irrelevant

  in case opt of
    UnfoldAll   -> cont (runIO (forceAll   ms t))
    UnfoldMetas -> cont (runIO (forceMetas ms t))
    UnfoldNone  -> cont (runIO (force      ms t))

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


-- Zonking (unfolding all metas in terms, but otherwise trying to minimize output)
--------------------------------------------------------------------------------

zonkApps :: MetaCxt -> Env -> Lvl -> Tm -> (# Tm | Val #)
zonkApps ms env l = \case
  Meta x    -> let t = meta ms x in (# | t #)
  App t u i -> case zonkApps ms env l t of
                 (# t | #) -> let u' = zonk ms env l u in (# App t u' i | #)
                 (# | t #) -> let t' = inlApp ms t (eval ms env u) i in (# | t' #)
  t         -> let t' = zonk ms env l t in (# t' | #)

-- | Unfold all solved metas in a term.
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
    InsertedMeta x -> runIO $ MC.read ms x >>= \case
                        Unsolved _     ->
                          pure (InsertedMeta x)
                        Solved _ mask _ v ->
                          pure $ quote $ appSp ms v (maskEnv env mask)
    Meta x         -> quote $ meta ms x
    Pi xi a b      -> Pi xi (go a) (goBind b)
    Irrelevant     -> Irrelevant
    U              -> U
