
module Evaluation where

{-|
TODO:
  - known call optimization for syntax
  - environment trimming
  - meta solution lowering, inlining and arg trimming
    - (general optimization, after top-level group elaboration)
-}

import Common
import ElabState
import Syntax
import Values

--------------------------------------------------------------------------------

envLength :: Env a -> Int
envLength = go 0 where
  go acc ENil       = acc
  go acc (EDef e _) = go (acc + 1) e
  go acc (ESkip e)  = go (acc + 1) e

--------------------------------------------------------------------------------

gLocal :: GEnv -> Ix -> Box Glued
gLocal = go where
  go (EDef gs g) 0 = Box g
  go (ESkip gs)  0 = let l = envLength gs in Box (GLocal l)
  go (EDef gs _) x = go gs (x - 1)
  go (ESkip gs)  x = go gs (x - 1)
  go ENil        x = error "gLocal: impossible"

gTop :: Lvl -> Box Glued
gTop x = case _entryDef (lookupTop x) of
  EDPostulate             -> Box (GTop x)
  EDDefinition _ (GV g _) -> Box g
{-# inline gTop #-}

-- | We use this to avoid allocating useless thunks for looking up variables
--   from environments.
gEvalBox :: GEnv -> VEnv -> Tm -> Box Glued
gEvalBox gs vs = \case
  LocalVar x  -> gLocal gs x
  TopVar   x  -> gTop x
  MetaVar  x  -> case lookupMeta x of MESolved (GV g _) _ _ -> Box g; _ -> Box (GMeta x)
  t           -> Box (gEval gs vs t)
{-# inline gEvalBox #-}

gEval :: GEnv -> VEnv -> Tm -> Glued
gEval gs vs = \case
  LocalVar x  -> let Box g = gLocal gs x in g
  TopVar   x  -> let Box g = gTop x in g
  MetaVar  x  -> case lookupMeta x of MESolved (GV g _) _ _ -> g; _ -> GMeta x
  AppI t u    -> let Box gu = gEvalBox gs vs u
                 in gAppI (gEval gs vs t) (GV gu (vEval vs u))
  AppE t u    -> let Box gu = gEvalBox gs vs u
                 in gAppE (gEval gs vs t) (GV gu (vEval vs u))
  Lam x t     -> GLam x (GCl gs vs t)
  Pi x a b    -> let Box ga = gEvalBox gs vs a
                 in GPi x (GV ga (vEval vs a)) (GCl gs vs b)
  Fun t u     -> let Box gt = gEvalBox gs vs t; Box gu = gEvalBox gs vs u
                 in GFun (GV gt (vEval vs t)) (GV gu (vEval vs u))
  U           -> GU
  Let _ t u   -> let Box gt = gEvalBox gs vs t
                 in gEval (EDef gs gt) (EDef vs (vEval vs u)) u
  Irrelevant  -> GIrrelevant

gInst :: GCl -> GV -> Glued
gInst (GCl gs vs t) (GV g v) = gEval (EDef gs g) (EDef vs v) t
{-# inline gInst #-}

gAppI :: Glued -> GV -> Glued
gAppI (GLam _ t)    gv       = gInst t gv
gAppI (GNe h gs vs) (GV g v) = GNe h (SAppI gs g) (SAppI vs v)
gAppI _             _        = error "gAppI: impossible"
{-# inline gAppI #-}

gAppE :: Glued -> GV -> Glued
gAppE (GLam _ t)    gv       = gInst t gv
gAppE (GNe h gs vs) (GV g v) = GNe h (SAppE gs g) (SAppE vs v)
gAppE _             _        = error "gAppE: impossible"
{-# inline gAppE #-}

gAppSpine :: Glued -> GSpine -> VSpine -> Glued
gAppSpine g (SAppI gs g') (SAppI vs v) = gAppI (gAppSpine g gs vs) (GV g' v)
gAppSpine g (SAppE gs g') (SAppE vs v) = gAppE (gAppSpine g gs vs) (GV g' v)
gAppSpine g SNil           SNil        = g
gAppSpine _ _              _           = error "gAppSpine: impossible"

gForce :: Glued -> Glued
gForce = \case
  GNe (HMeta x) gs vs | MESolved (GV g v) _ _ <- lookupMeta x -> gForce (gAppSpine g gs vs)
  g -> g

--------------------------------------------------------------------------------

vLocal :: VEnv -> Ix -> Box Val
vLocal = go where
  go (EDef vs v) 0 = Box v
  go (ESkip vs)  0 = let l = envLength vs in Box (VLocal l)
  go (EDef vs _) x = go vs (x - 1)
  go (ESkip vs)  x = go vs (x - 1)
  go ENil        x = error "vLocal: impossible"

-- | We use this to avoid allocating useless thunks for looking up variables
--   from environments.
vEvalBox :: VEnv -> Tm -> Box Val
vEvalBox vs = \case
  LocalVar x -> vLocal vs x
  TopVar x   -> Box (VTop x)
  MetaVar x  -> Box (VMeta x)
  t          -> Box (vEval vs t)
{-# inline vEvalBox #-}

vEval :: VEnv -> Tm -> Val
vEval vs = \case
  LocalVar x  -> let Box v = vLocal vs x in v
  TopVar x    -> VTop x
  MetaVar x   -> VMeta x
  AppI t u    -> let Box vu = vEvalBox vs u in vAppI (vEval vs t) vu
  AppE t u    -> let Box vu = vEvalBox vs u in vAppE (vEval vs t) vu
  Lam x t     -> VLam x (VCl vs t)
  Pi x a b    -> let Box va = vEvalBox vs a in VPi x va (VCl vs b)
  Fun t u     -> let Box vt = vEvalBox vs t; Box vu = vEvalBox vs u
                 in VFun vt vu
  U           -> VU
  Let _   t u -> vEval (EDef vs (vEval vs t)) u
  Irrelevant  -> VIrrelevant


vInst :: VCl -> Val -> Val
vInst (VCl vs t) ~u = vEval (EDef vs u) t
{-# inline vInst #-}

vAppI :: Val -> Val -> Val
vAppI (VLam _ t) ~u = vInst t u
vAppI (VNe h vs) ~u = VNe h (SAppI vs u)
vAppI _ ~_ = error "vAppI: impossible"
{-# inline vAppI #-}

vAppE :: Val -> Val -> Val
vAppE (VLam _ t) ~u = vInst t u
vAppE (VNe h vs) ~u = VNe h (SAppE vs u)
vAppE _ ~_ = error "vAppE: impossible"
{-# inline vAppE #-}

vApp :: Icit -> Val -> Val -> Val
vApp i (VLam _ t) ~u = vInst t u
vApp i (VNe h vs) ~u = case i of Impl -> VNe h (SAppI vs u)
                                 Expl -> VNe h (SAppE vs u)
vApp _ _ _ = error "vApp: impossible"
{-# inline vApp #-}

vAppSpine :: Val -> VSpine -> Val
vAppSpine v (SAppI vs v') = vAppI (vAppSpine v vs) v'
vAppSpine v (SAppE vs v') = vAppE (vAppSpine v vs) v'
vAppSpine v SNil          = v

--------------------------------------------------------------------------------

gvEval :: GEnv -> VEnv -> Tm -> GV
gvEval gs vs t = GV (gEval gs vs t) (vEval vs t)
{-# inline gvEval #-}

gvInst :: GCl -> GV -> GV
gvInst (GCl gs vs t) (GV g v) =
  let vs' = EDef vs v
      gs' = EDef gs g
  in GV (gEval gs' vs' t) (vEval vs' t)
{-# inline gvInst #-}

gvAppI :: Glued -> GV -> GV
gvAppI (GLam _ t)      gv       = gvInst t gv
gvAppI (GNe h gsp vsp) (GV g v) = let vsp' = SAppI vsp v
                                  in GV (GNe h (SAppI gsp g) vsp') (VNe h vsp')
gvAppI _ _ = error "gvAppI : impossible"
{-# inline gvAppI #-}

gvAppE :: Glued -> GV -> GV
gvAppE (GLam _ t)      gv       = gvInst t gv
gvAppE (GNe h gsp vsp) (GV g v) = let vsp' = SAppE vsp v
                                  in GV (GNe h (SAppE gsp g) vsp') (VNe h vsp')
gvAppE _ _ = error "gvAppE : impossible"
{-# inline gvAppE #-}

gvApp :: Icit -> Glued -> GV -> GV
gvApp Impl = gvAppI
gvApp Expl = gvAppE
{-# inline gvApp #-}

-- Quoting
--------------------------------------------------------------------------------

-- | Quote local value.
vQuote :: Lvl -> Val -> Tm
vQuote = go where
  go l = \case
    VNe h vsp   -> goSp vsp where
                     goSp SNil = case h of
                       HMeta x  -> MetaVar x
                       HLocal x -> LocalVar (l - x - 1)
                       HTop x   -> TopVar x
                     goSp (SAppI vsp t) = AppI (goSp vsp) (go l t)
                     goSp (SAppE vsp t) = AppE (goSp vsp) (go l t)
    VLam ni t   -> Lam ni (go (l + 1) (vInst t (VLocal l)))
    VPi ni a b  -> Pi ni (go l a) (go (l + 1) (vInst b (VLocal l)))
    VFun a b    -> Fun (go l a) (go l b)
    VU          -> U
    VIrrelevant -> Irrelevant

-- | Quote glued value to full normal form.
gQuote :: Lvl -> Glued -> Tm
gQuote = go where
  go l g = case gForce g of
    GNe h gsp vsp          -> goSp gsp where
                                goSp SNil = case h of
                                  HMeta x  -> MetaVar x
                                  HLocal x -> LocalVar (l - x - 1)
                                  HTop x   -> TopVar x
                                goSp (SAppI vsp t) = AppI (goSp vsp) (go l t)
                                goSp (SAppE vsp t) = AppE (goSp vsp) (go l t)
    GLam ni t              -> Lam ni (go (l + 1) (gInst t (gvLocal l)))
    GPi ni (GV a _) b      -> Pi ni (go l a) (go (l + 1) (gInst b (gvLocal l)))
    GFun (GV a _) (GV b _) -> Fun (go l a) (go l b)
    GU                     -> U
    GIrrelevant            -> Irrelevant

-- | Quote local value while unfolding all metas.
vQuoteMetaless :: Lvl -> Val -> Tm
vQuoteMetaless = go where
  go l = \case
    VNe h vsp   -> case h of
                     HMeta x | MESolved (GV _ vt) _ _ <- lookupMeta x
                       -> go l (vAppSpine vt vsp)
                     HMeta x  -> goSp l (MetaVar x) vsp
                     HLocal x -> goSp l (LocalVar x) vsp
                     HTop   x -> goSp l (TopVar x) vsp
    VLam ni t   -> Lam ni (go (l + 1) (vInst t (VLocal l)))
    VPi ni a b  -> Pi ni (go l a) (go (l + 1) (vInst b (VLocal l)))
    VFun a b    -> Fun (go l a) (go l b)
    VU          -> U
    VIrrelevant -> Irrelevant

  goSp l h SNil          = h
  goSp l h (SAppI vsp t) = AppI (goSp l h vsp) (go l t)
  goSp l h (SAppE vsp t) = AppE (goSp l h vsp) (go l t)
