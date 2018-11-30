
module Evaluation where

{-|

TODO:
  - thunk allocation control with boxes
  - known call optimization for syntax
  - environment trimming
  - meta solution lowering, inlining and arg trimming
    - (general optimization, after top-level group elaboration)
-}

import Data.Nullable
import qualified Data.Array.Dynamic as A

import Common
import ElabState
import Syntax
import Values

--------------------------------------------------------------------------------

gLocal :: Int -> GEnv -> Ix -> Glued
gLocal d gs x = go x (d - x - 1) gs where
  go x _ ENil'         = error "gLocal: impossible"
  go x 0 (ESnoc' gs g) = maybe (GLocal x) id g
  go x y (ESnoc' gs _) = go x (y - 1) gs

gTop :: Ix -> Glued
gTop x = runIO $ do
  entry <- A.read top x
  case _entryDef entry of
    EDPostulate             -> pure (GTop x)
    EDDefinition _ (GV g _) -> pure g
{-# inline gTop #-}

gEval :: Int -> GEnv -> VEnv -> Tm -> Glued
gEval d gs vs = \case
  LocalVar x  -> gLocal d gs x
  TopVar   x  -> gTop x
  MetaVar  x  -> nullable (GMeta x) (\(MEntry _ (GV g _)) -> g) (lookupMeta x)
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
{-# inline gInst #-}

gApp :: Glued -> GV -> Icit -> Glued
gApp (GLam _ t)    gv       i = gInst t gv
gApp (GNe h gs vs) (GV g v) i = GNe h (SApp gs g i) (SApp vs v i)
gApp _ _ _ = error "gApp: impossible"
{-# inline gApp #-}

gAppSpine :: Glued -> GSpine -> VSpine -> Glued
gAppSpine g (SApp gs g' i) (SApp vs v _) = gApp (gAppSpine g gs vs) (GV g' v) i
gAppSpine g SNil           SNil          = g
gAppSpine _ _ _ = error "gAppSpine: impossible"

gForce :: Glued -> Glued
gForce = \case
  GNe (HMeta x) gs vs | Some (MEntry _ (GV g v)) <- lookupMeta x -> gForce (gAppSpine g gs vs)
  g -> g

--------------------------------------------------------------------------------

vLocal :: Int -> VEnv -> Ix -> Val
vLocal d vs x = go x (d - x - 1) vs where
  go x _ ENil'         = error "vLocal: impossible"
  go x 0 (ESnoc' vs v) = maybe (VLocal x) id v
  go x y (ESnoc' vs _) = go x (y - 1) vs

vEval :: Int -> VEnv -> Tm -> Val
vEval d vs = \case
  LocalVar x  -> vLocal d vs x
  TopVar x    -> VTop x
  MetaVar x   -> VMeta x
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
vApp _ ~_ _ = error "vApp: impossible"
{-# inline vApp #-}

vAppSpine :: Val -> VSpine -> Val
vAppSpine v (SApp vs v' i) = vApp (vAppSpine v vs) v' i
vAppSpine v SNil           = v

--------------------------------------------------------------------------------

gvEval :: Int -> GEnv -> VEnv -> Tm -> GV
gvEval d gs vs t = GV (gEval d gs vs t) (vEval d vs t)
{-# inline gvEval #-}

gvInst :: GCl -> GV -> GV
gvInst (GCl d gs vs t) (GV g v) =
  let vs' = ESnoc' vs (Just v)
      gs' = ESnoc' gs (Just g)
      d'  = d + 1
  in GV (gEval d' gs' vs' t) (vEval d' vs' t)
{-# inline gvInst #-}

gvApp :: Glued -> GV -> Icit -> GV
gvApp (GLam _ t)      gv       i = gvInst t gv
gvApp (GNe x gsp vsp) (GV g v) i = let vsp' = SApp vsp v i
                                   in GV (GNe x (SApp gsp g i) vsp') (VNe x vsp')
gvApp _ _ _ = error "gvApp: impossible"


-- Quoting
--------------------------------------------------------------------------------

vQuote :: Int -> Val -> Tm
vQuote = go where
  go d = \case
    VNe h vsp   -> goSp vsp where
                     goSp SNil = case h of
                       HMeta x  -> MetaVar x
                       HLocal x -> LocalVar x
                       HTop x   -> TopVar x
                     goSp (SApp vsp t i) = App (goSp vsp) (go d t) i
    VLam ni t   -> Lam ni (go (d + 1) (vInst t (VLocal d)))
    VPi ni a b  -> Pi ni (go d a) (go (d + 1) (vInst b (VLocal d)))
    VU          -> U
    VIrrelevant -> Irrelevant

gQuote :: Int -> Glued -> Tm
gQuote = go where
  go d g = case gForce g of
    GNe h gsp vsp      -> goSp gsp where
                            goSp SNil = case h of
                              HMeta x  -> MetaVar x
                              HLocal x -> LocalVar x
                              HTop x   -> TopVar x
                            goSp (SApp vsp t i) = App (goSp vsp) (go d t) i
    GLam ni t          -> Lam ni (go (d + 1) (gInst t (gvLocal d)))
    GPi ni (GV a _) b  -> Pi ni (go d a) (go (d + 1) (gInst b (gvLocal d)))
    GU                 -> U
    GIrrelevant        -> Irrelevant
