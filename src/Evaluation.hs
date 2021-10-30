{-# language UnboxedTuples, UnboxedSums #-}

module Evaluation (
  app, inlApp, appSp, appMask, eval, forceCS, Cxt(..),
  forceF, forceFU, appCl, appCl', quote, quote0, eval0, nf0) where

import qualified Data.Array.LM as ALM
import IO

import qualified LvlSet as LS
import qualified MetaCxt as MC
import qualified UIO as U
import Common
import CoreTypes
import MetaCxt

--------------------------------------------------------------------------------

-- TODO: inserted meta better evaluation (dep on solved/unsolved)

--------------------------------------------------------------------------------

data Cxt = Cxt {mcxt :: MetaCxt, top :: ALM.Array Val}

localVar :: Env -> Ix -> Val
localVar (EDef _ v) 0 = v
localVar (EDef e _) x = localVar e (x - 1)
localVar _          _ = impossible

meta :: Cxt -> MetaVar -> Val
meta cxt x = U.run U.do
  MC.read (mcxt cxt) x U.>>= \case
    MEUnsolved     -> U.pure (VFlex x SId)
    MESolved _ _ v -> U.pure (VUnfold (UHSolved x) SId v)
{-# inline meta #-}

appCl' :: Cxt -> Closure -> Val -> Val
appCl' cxt (Closure e t) u = let e' = EDef e u in eval' cxt e' t
{-# inline appCl' #-}

appCl :: Cxt -> Closure -> Val -> Val
appCl cxt (Closure e t) ~u = let e' = EDef e u in eval' cxt e' t
{-# inline appCl #-}

app :: Cxt -> Val -> Val -> Icit -> Val
app cxt t u i = case t of
  VLocalVar x sp   -> VLocalVar x (SApp sp u i)
  VUnfold   h sp v -> VUnfold h (SApp sp u i) (app cxt v u i)
  VFlex     x sp   -> VFlex x (SApp sp u i)
  VLam _ _ t       -> appCl' cxt t u
  VIrrelevant      -> VIrrelevant
  _                -> impossible

inlApp :: Cxt -> Val -> Val -> Icit -> Val
inlApp cxt t u i = case t of
  VLocalVar x sp   -> VLocalVar x (SApp sp u i)
  VUnfold   h sp v -> VUnfold h (SApp sp u i) (app cxt v u i)
  VFlex     x sp   -> VFlex x (SApp sp u i)
  VLam _ _ t       -> appCl' cxt t u
  VIrrelevant      -> VIrrelevant
  _                -> impossible
{-# inline inlApp #-}

appSp :: Cxt -> Val -> Spine -> Val
appSp cxt t = \case
  SId         -> t
  SApp sp u i -> inlApp cxt (appSp cxt t sp) u i

data ValLvl = ValLvl Val Lvl

appMask :: Cxt -> Env -> Val -> LS.LvlSet -> Val
appMask cxt ~e v mask = (case go cxt e v mask of ValLvl v _ -> v) where
  go :: Cxt -> Env -> Val -> LS.LvlSet -> ValLvl
  go cxt ENil        v m = ValLvl v 0
  go cxt (EDef e v') v m = case go cxt e v m of
    ValLvl v i | LS.member i m -> ValLvl (inlApp cxt v v' Expl) (i + 1)
               | otherwise     -> ValLvl v (i + 1)

data SpineLvl = SpineLvl Spine Lvl

maskEnv :: Env -> LS.LvlSet -> Spine
maskEnv e mask = (case go e mask of SpineLvl sp _ -> sp) where
  go :: Env -> LS.LvlSet -> SpineLvl
  go ENil        mask = SpineLvl SId 0
  go (EDef e v') mask = case go e mask of
    SpineLvl sp l | LS.member l mask -> SpineLvl (SApp sp v' Expl) (l + 1)
                  | otherwise        -> SpineLvl sp (l + 1)

insertedMeta :: Cxt -> Env -> MetaVar -> LS.LvlSet -> Val
insertedMeta cxt ~e x mask = U.run do
  MC.read (mcxt cxt) x U.>>= \case
    MEUnsolved     -> U.pure (VFlex x (maskEnv e mask))
    MESolved _ _ v -> let sp = maskEnv e mask in U.pure (VUnfold (UHSolved x) sp (appSp cxt v sp))
{-# inline insertedMeta #-}

topVar :: Cxt -> Lvl -> Val
topVar cxt x = runIO (ALM.read (top cxt) (coerce x))
{-# inline topVar #-}

eval' :: Cxt -> Env -> Tm -> Val
eval' cxt ~e = \case
  LocalVar x          -> localVar e x
  TopVar x            -> let v = topVar cxt x in VUnfold (UHTopVar x) SId v
  Meta x              -> meta cxt x
  App t u i           -> inlApp cxt (eval' cxt e t) (eval' cxt e u) i
  Let _ _ t u         -> let ~vt = eval' cxt e t; e' = EDef e vt in eval' cxt e' u
  InsertedMeta x mask -> insertedMeta cxt e x mask
  Lam x i t           -> VLam x i (Closure e t)
  Pi x i a b          -> VPi x i (eval' cxt e a) (Closure e b)
  Irrelevant          -> VIrrelevant
  U                   -> VU

eval :: Cxt -> Env -> Tm -> Val
eval cxt e t = eval' cxt e t
{-# inline eval #-}

-- | Force metas only.
forceF :: Cxt -> Val -> U.IO Val
forceF cxt = \case
  t@(VFlex x sp) -> forceFFlex cxt t x sp
  t              -> U.pure t
{-# inline forceF #-}

forceFFlex :: Cxt -> Val -> MetaVar -> Spine -> U.IO Val
forceFFlex cxt t x sp =
  MC.read (mcxt cxt) x U.>>= \case
    MEUnsolved     -> U.pure t
    MESolved _ _ v -> U.pure (VUnfold (UHSolved x) sp (appSp cxt v sp))
{-# noinline forceFFlex #-}

-- | Force both metas and top unfoldings.
forceFU :: Cxt -> Val -> U.IO Val
forceFU cxt = \case
  VFlex x sp     -> forceFUFlex cxt x sp
  VUnfold _ sp v -> forceFU' cxt v
  t              -> U.pure t
{-# inline forceFU #-}

forceFU' :: Cxt -> Val -> U.IO Val
forceFU' cxt = \case
  VFlex x sp     -> forceFUFlex cxt x sp
  VUnfold _ sp v -> forceFU' cxt v
  t              -> U.pure t

forceFUFlex :: Cxt -> MetaVar -> Spine -> U.IO Val
forceFUFlex cxt x sp =
  MC.read (mcxt cxt) x U.>>= \case
    MEUnsolved     -> U.pure (VFlex x sp)
    MESolved _ _ v -> forceFU' cxt $! appSp cxt v sp
{-# noinline forceFUFlex #-}

forceCS :: Cxt -> ConvState -> Val -> U.IO Val
forceCS cxt cs v = case cs of
  CSFull -> forceFU cxt v
  _      -> forceF  cxt v
{-# inline forceCS #-}

--------------------------------------------------------------------------------

quoteSp :: Cxt -> Lvl -> QuoteOption -> Tm -> Spine -> Tm
quoteSp cxt l opt hd = \case
  SId         -> hd
  SApp sp t i -> App (quoteSp cxt l opt hd sp) (quote cxt l opt t) i

quote :: Cxt -> Lvl -> QuoteOption -> Val -> Tm
quote cxt l opt t = let
  go       = quote cxt l opt; {-# inline go #-}
  goSp     = quoteSp cxt l opt; {-# inline goSp #-}
  goBind t = quote cxt (l + 1) opt (appCl' cxt t (VLocalVar l SId)); {-# inline goBind #-}

  cont = \case
    VFlex x sp                  -> goSp (Meta x) sp
    VUnfold (UHSolved x) sp _   -> goSp (Meta x) sp
    VUnfold (UHTopVar x) sp _   -> goSp (TopVar x) sp
    VLocalVar x sp              -> goSp (LocalVar (lvlToIx l x)) sp
    VLam x i t                  -> Lam x i (goBind t)
    VPi x i a b                 -> Pi x i (go a) (goBind b)
    VU                          -> U
    VIrrelevant                 -> Irrelevant

  in case opt of
    UnfoldAll  -> cont (U.run (forceFU cxt t))
    UnfoldFlex -> cont (U.run (forceF  cxt t))
    _          -> cont t

--------------------------------------------------------------------------------

eval0 :: Cxt -> Tm -> Val
eval0 cxt = eval cxt ENil
{-# inline eval0 #-}

quote0 :: Cxt -> QuoteOption -> Val -> Tm
quote0 cxt = quote cxt 0
{-# inline quote0 #-}

nf0 :: Cxt -> QuoteOption -> Tm -> Tm
nf0 cxt opt t = quote0 cxt opt (eval0 cxt t)
{-# inline nf0 #-}
