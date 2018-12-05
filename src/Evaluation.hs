
module Evaluation where

{-|
TODO:
  - thunk allocation control with boxes
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

gLocal :: GEnv -> Ix -> Glued
gLocal = go where
  go (EDef gs g) 0 = g
  go (ESkip gs)  0 = GLocal (envLength gs)
  go (EDef gs _) x = go gs (x - 1)
  go (ESkip gs)  x = go gs (x - 1)
  go ENil        x = error "gLocal: impossible"

gTop :: Lvl -> Glued
gTop x = case _entryDef (lookupTop x) of
  EDPostulate             -> GTop x
  EDDefinition _ (GV g _) -> g
{-# inline gTop #-}

gEval :: GEnv -> VEnv -> Tm -> Glued
gEval gs vs = \case
  LocalVar x  -> gLocal gs x
  TopVar   x  -> gTop x
  MetaVar  x  -> case lookupMeta x of MESolved _  (GV g _) -> g; _ -> GMeta x
  AppI t u    -> gAppI (gEval gs vs t) (gvEval gs vs u)
  AppE t u    -> gAppE (gEval gs vs t) (gvEval gs vs u)
  Let _ t u   -> let GV gt vt = gvEval gs vs t in gEval (EDef gs gt) (EDef vs vt) u
  Lam x t     -> GLam x (GCl gs vs t)
  Pi x a b    -> GPi x (gvEval gs vs a) (GCl gs vs b)
  U           -> GU
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
  GNe (HMeta x) gs vs | MESolved _ (GV g v) <- lookupMeta x -> gForce (gAppSpine g gs vs)
  g -> g

--------------------------------------------------------------------------------

vLocal :: VEnv -> Ix -> Val
vLocal = go where
  go (EDef vs v) 0 = v
  go (ESkip vs)  0 = VLocal (envLength vs)
  go (EDef vs _) x = go vs (x - 1)
  go (ESkip vs)  x = go vs (x - 1)
  go ENil        x = error "vLocal: impossible"

vEval :: VEnv -> Tm -> Val
vEval vs = \case
  LocalVar x  -> vLocal vs x
  TopVar x    -> VTop x
  MetaVar x   -> VMeta x
  Let _   t u -> vEval (EDef vs (vEval vs t)) u
  AppI t u    -> vAppI (vEval vs t) (vEval vs u)
  AppE t u    -> vAppE (vEval vs t) (vEval vs u)
  Lam x t     -> VLam x (VCl vs t)
  Pi x a b    -> VPi x (vEval vs a) (VCl vs b)
  U           -> VU
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
    VU          -> U
    VIrrelevant -> Irrelevant

gQuote :: Lvl -> Glued -> Tm
gQuote = go where
  go l g = case gForce g of
    GNe h gsp vsp      -> goSp gsp where
                            goSp SNil = case h of
                              HMeta x  -> MetaVar x
                              HLocal x -> LocalVar (l - x - 1)
                              HTop x   -> TopVar x
                            goSp (SAppI vsp t) = AppI (goSp vsp) (go l t)
                            goSp (SAppE vsp t) = AppE (goSp vsp) (go l t)
    GLam ni t          -> Lam ni (go (l + 1) (gInst t (gvLocal l)))
    GPi ni (GV a _) b  -> Pi ni (go l a) (go (l + 1) (gInst b (gvLocal l)))
    GU                 -> U
    GIrrelevant        -> Irrelevant
