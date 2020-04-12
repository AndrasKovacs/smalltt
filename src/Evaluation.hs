
module Evaluation where

import Common
import ElabState
import Syntax
import Values

--------------------------------------------------------------------------------

vLocal :: VEnv -> Ix -> Box Val
vLocal = go where
  go (EDef vs v) 0 = Box v
  go (ESkip vs)  0 = let l = envLength vs in Box (VLocal l)
  go (EDef vs _) x = go vs (x - 1)
  go (ESkip vs)  x = go vs (x - 1)
  go ENil        x = error "vLocal: impossible"

vMetaVar :: Meta -> Box Val
vMetaVar x = case lookupMeta x of
  MESolved v _ _ _ -> Box (VGlueMeta x SNil v)
  _                -> Box (VMeta x)
{-# inline vMetaVar #-}

vTop :: Lvl -> Box Val
vTop x = case _entryDef (lookupTop x) of
  EDPostulate      -> Box (VTop x)
  EDDefinition _ v -> Box (VGlueTop x SNil v)
{-# inline vTop #-}

-- | We use this to avoid allocating useless thunks for looking up variables
--   from environments.
vEvalBox :: VEnv -> Tm -> Box Val
vEvalBox vs = \case
  LocalVar x -> vLocal vs x
  TopVar x   -> vTop x
  MetaVar x  -> vMetaVar x
  t          -> Box (vEval vs t)
{-# inline vEvalBox #-}

vEval :: VEnv -> Tm -> Val
vEval vs = \case
  LocalVar x  -> let Box v = vLocal vs x in v
  TopVar x    -> let Box v = vTop x in v
  MetaVar x   -> let Box v = vMetaVar x in v
  AppI t u    -> let Box vu = vEvalBox vs u in vAppI (vEval vs t) vu
  AppE t u    -> let Box vu = vEvalBox vs u in vAppE (vEval vs t) vu
  Lam x t     -> VLam x (Cl vs t)
  Pi x a b    -> let Box va = vEvalBox vs a in VPi x va (Cl vs b)
  Fun t u     -> let Box vt = vEvalBox vs t; Box vu = vEvalBox vs u
                 in VFun vt vu
  U           -> VU
  Let _   t u -> let ~vt = vEval vs t in vEval (EDef vs vt) u
  Irrelevant  -> VIrrelevant

vInst :: Cl -> Val -> Val
vInst (Cl vs t) ~u = vEval (EDef vs u) t
{-# inline vInst #-}

vAppI :: Val -> Val -> Val
vAppI (VLam _ t)     ~u = vInst t u
vAppI (VNe h vs)     ~u = VNe h (SAppI vs u)
vAppI (VGlueTop x sp t) ~u = VGlueTop x (SAppI sp u) (vAppI t u)
vAppI (VGlueMeta x sp t) ~u = VGlueMeta x (SAppI sp u) (vAppI t u)
vAppI _ ~_ = error "vAppI: impossible"

vAppE :: Val -> Val -> Val
vAppE (VLam _ t)     ~u = vInst t u
vAppE (VNe h vs)     ~u = VNe h (SAppE vs u)
vAppE (VGlueTop x sp t) ~u = VGlueTop x (SAppE sp u) (vAppE t u)
vAppE (VGlueMeta x sp t) ~u = VGlueMeta x (SAppE sp u) (vAppE t u)
vAppE _ ~_ = error "vAppE: impossible"

vApp :: Icit -> Val -> Val -> Val
vApp i (VLam _ t) ~u = vInst t u
vApp i (VNe h vs) ~u = case i of Impl -> VNe h (SAppI vs u)
                                 Expl -> VNe h (SAppE vs u)
vApp i (VGlueTop x sp t) ~u = case i of Impl -> VGlueTop x (SAppI sp u) (vAppI t u)
                                        Expl -> VGlueTop x (SAppE sp u) (vAppE t u)
vApp i (VGlueMeta x sp t) ~u = case i of Impl -> VGlueMeta x (SAppI sp u) (vAppI t u)
                                         Expl -> VGlueMeta x (SAppE sp u) (vAppE t u)
vApp _ _ _ = error "vApp: impossible"
-- {-# inline vApp #-}

vAppSpine :: Val -> VSpine -> Val
vAppSpine v (SAppI vs v') = vAppI (vAppSpine v vs) v'
vAppSpine v (SAppE vs v') = vAppE (vAppSpine v vs) v'
vAppSpine v SNil          = v

vForce :: Val -> Val
vForce = \case
  VNe (HMeta x) vs
    | MESolved v _ _ _ <- lookupMeta x -> vForce (vAppSpine v vs)
  VGlueTop _ _ v -> vForce v
  VGlueMeta _ _ v -> vForce v
  v           -> v

-- Quoting
--------------------------------------------------------------------------------

-- | Quote local value.
lQuote :: Lvl -> Val -> Tm
lQuote = go where
  goSp l h SNil = case h of
    HMeta x  -> MetaVar x
    HLocal x -> LocalVar (l - x - 1)
    HTop x   -> TopVar x
  goSp l h (SAppI vsp t) = AppI (goSp l h vsp) (go l t)
  goSp l h (SAppE vsp t) = AppE (goSp l h vsp) (go l t)

  go l = \case
    VNe h vsp    -> goSp l h vsp where
    VLam ni t    -> Lam ni (go (l + 1) (vInst t (VLocal l)))
    VPi ni a b   -> Pi ni (go l a) (go (l + 1) (vInst b (VLocal l)))
    VFun a b     -> Fun (go l a) (go l b)
    VGlueTop x sp t -> goSp l (HTop x) sp
    VGlueMeta x sp t -> goSp l (HMeta x) sp
    VU           -> U
    VIrrelevant  -> Irrelevant

-- | Quote glued value to full normal form.
nfQuote :: Lvl -> Val -> Tm
nfQuote = go where
  goSp l h SNil = case h of
    HMeta x  -> MetaVar x
    HLocal x -> LocalVar (l - x - 1)
    HTop x   -> TopVar x
  goSp l h (SAppI vsp t) = AppI (goSp l h vsp) (go l t)
  goSp l h (SAppE vsp t) = AppE (goSp l h vsp) (go l t)

  go l g = case vForce g of
    VNe h sp     -> goSp l h sp
    VLam ni t    -> Lam ni (go (l + 1) (vInst t (VLocal l)))
    VPi ni a b   -> Pi ni (go l a) (go (l + 1) (vInst b (VLocal l)))
    VFun a b     -> Fun (go l a) (go l b)
    VU           -> U
    VIrrelevant  -> Irrelevant

-- | Quote local value while unfolding all metas.
lQuoteMetaless :: Lvl -> Val -> Tm
lQuoteMetaless = go where
  go l = \case
    VNe h vsp    -> case h of
                      HMeta x | MESolved vt _ _ _ <- lookupMeta x
                        -> go l (vAppSpine vt vsp)
                      HMeta x  -> goSp l (MetaVar x) vsp
                      HLocal x -> goSp l (LocalVar (l - x - 1)) vsp
                      HTop   x -> goSp l (TopVar x) vsp
    VLam ni t    -> Lam ni (go (l + 1) (vInst t (VLocal l)))
    VPi ni a b   -> Pi ni (go l a) (go (l + 1) (vInst b (VLocal l)))
    VFun a b     -> Fun (go l a) (go l b)
    VGlueTop x sp _ -> goSp l (TopVar x) sp
    VGlueMeta x sp _ -> goSp l (MetaVar x) sp
    VU           -> U
    VIrrelevant  -> Irrelevant

  goSp l h SNil          = h
  goSp l h (SAppI vsp t) = AppI (goSp l h vsp) (go l t)
  goSp l h (SAppE vsp t) = AppE (goSp l h vsp) (go l t)
