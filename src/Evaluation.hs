
module Evaluation where

import Data.Nullable
import Lens.Micro.Platform
import qualified Data.Array.Dynamic as A

import Common
import ElabState
import Syntax
import Values

--------------------------------------------------------------------------------

gLocal :: Int -> GEnv -> Ix -> Glued
gLocal d gs x = go x (d - x - 1) gs where
  go x _ ENil'         = error "gLocal: impossible: Ix out of scope"
  go x 0 (ESnoc' gs g) = maybe (GLocal x) id g
  go x y (ESnoc' gs _) = go x (y - 1) gs

gTop :: Ix -> Glued
gTop x = runIO $ do
  entry <- A.read topState x
  case entry^.entryDef of
    EDPostulate             -> pure (GTop x)
    EDDefinition _ (GV g _) -> pure g
{-# inline gTop #-}

gEval :: Int -> GEnv -> VEnv -> Tm -> Glued
gEval d gs vs = \case
  LocalVar x  -> gLocal d gs x
  TopVar   x  -> gTop x
  App t u i   -> gApp (gEval d gs vs t) (gvEval d gs vs u) i
  Let _ a t u -> let GV gt vt = gvEval d gs vs t
                 in gEval (d + 1) (ESnoc' gs (Just gt)) (ESnoc' vs (Just vt)) u
  Lam x t     -> GLam x (GCl d gs vs t)
  Pi x a b    -> GPi x (gvEval d gs vs a) (GCl d gs vs b)
  U           -> GU
  Irrelevant  -> GIrrelevant

gInst :: GCl -> GV -> Glued
gInst (GCl d gs vs t) (GV g v) =
  gEval (d + 1) (ESnoc' gs (Just g)) (ESnoc' vs (Just v)) t

gApp :: Glued -> GV -> Icit -> Glued
gApp (GLam _ t)    gv       i = gInst t gv
gApp (GNe h gs vs) (GV g v) i = GNe h (SApp gs g i) (SApp vs v i)
gApp _ _ _ = error "gApp: impossible"

gAppSpine :: Glued -> GSpine -> VSpine -> Glued
gAppSpine g (SApp gs g' i) (SApp vs v _) = gApp (gAppSpine g gs vs) (GV g' v) i
gAppSpine g SNil           SNil          = g
gAppSpine _ _ _ = error "gAppSpine: impossible"

gForce :: Glued -> Glued
gForce = \case
  GNe (HMeta x) gs vs | Some (GV g v) <- lookupMeta x -> gForce (gAppSpine g gs vs)
  g -> g

--------------------------------------------------------------------------------

vLocal :: Int -> VEnv -> Ix -> Val
vLocal d vs x = go x (d - x - 1) vs where
  go x _ ENil'         = error "vLocal: impossible: Ix out of scope"
  go x 0 (ESnoc' vs v) = maybe (VLocal x) id v
  go x y (ESnoc' vs _) = go x (y - 1) vs

vEval :: Int -> VEnv -> Tm -> Val
vEval d vs = \case
  LocalVar x  -> vLocal d vs x
  TopVar x    -> VTop x
  Let x a t u -> vEval (d + 1) (ESnoc' vs (Just (vEval d vs t))) u
  App t u i   -> vApp (vEval d vs t) (vEval d vs u) i
  Lam x t     -> VLam x (VCl d vs t)
  Pi x a b    -> VPi x (vEval d vs a) (VCl d vs b)
  U           -> VU
  Irrelevant  -> VIrrelevant

vInst :: VCl -> Val -> Val
vInst (VCl d vs t) ~u = vEval (d + 1) (ESnoc' vs (Just u)) t
{-# inline vInst #-}

vApp :: Val -> Val -> Icit -> Val
vApp (VLam _ t) ~u i = vInst t u
vApp (VNe h vs) ~u i = VNe h (SApp vs u i)
vApp _ ~_ _ = error "vApp : impossible"

--------------------------------------------------------------------------------

gvEval :: Int -> GEnv -> VEnv -> Tm -> GV
gvEval d gs vs t = GV (gEval d gs vs t) (vEval d vs t)
{-# inline gvEval #-}

--------------------------------------------------------------------------------
