{-# options_ghc -Wno-unused-imports #-}

module Evaluation where

import qualified Data.Array.Dynamic.L as ADL
import Data.Bits

import IO
import Common
import CoreTypes
import MetaCxt

import qualified EnvMask as EM

--------------------------------------------------------------------------------

-- localVar :: Env -> Ix -> Val
-- localVar (EDef _ v) 0 = v
-- localVar (EDef e _) x = localVar e (x - 1)
-- localVar _          _ = impossible

-- meta :: MetaCxt -> MetaVar -> Val
-- meta ms x = runIO do
--   ADL.read ms (coerce x) >>= \case
--     MEUnsolved -> pure (VMeta x SId)
--     MESolved v -> pure v
-- {-# inline meta #-}

-- appCl' :: MetaCxt -> Closure -> Val -> Val
-- appCl' ms (Closure e t) u = eval ms (EDef e u) t
-- {-# inline appCl' #-}

-- appCl :: MetaCxt -> Closure -> Val -> Val
-- appCl ms (Closure e t) ~u = eval ms (EDef e u) t
-- {-# inline appCl #-}

-- app :: MetaCxt -> Val -> Val -> Icit -> Val
-- app ms t u i = case t of
--   VLocalVar x sp   -> VLocalVar x (SApp sp u i)
--   VTopVar   x sp v -> VTopVar x (SApp sp u i) (app ms v u i)
--   VMeta     x sp   -> VMeta x (SApp sp u i)
--   VLam _ _ t       -> appCl' ms t u
--   _                -> impossible

-- inlApp :: MetaCxt -> Val -> Val -> Icit -> Val
-- inlApp ms t u i = case t of
--   VLocalVar x sp   -> VLocalVar x (SApp sp u i)
--   VTopVar   x sp v -> VTopVar x (SApp sp u i) (app ms v u i)
--   VMeta     x sp   -> VMeta x (SApp sp u i)
--   VLam _ _ t       -> appCl' ms t u
--   _                -> impossible
-- {-# inline inlApp #-}

-- appSp :: MetaCxt -> Val -> Spine -> Val
-- appSp ms t = \case
--   SId         -> t
--   SApp sp u i -> inlApp ms (appSp ms t sp) u i

-- data ValLvl = ValLvl Val Lvl

-- applyMask :: MetaCxt -> Env -> Val -> EM.EnvMask -> Val
-- applyMask ms e v mask = (case go ms e v mask of ValLvl v _ -> v) where
--   go :: MetaCxt -> Env -> Val -> EM.EnvMask -> ValLvl
--   go ms ENil        v m = ValLvl v 0
--   go ms (EDef e v') v m = case go ms e v m of
--     ValLvl v i -> EM.looked i m
--       (ValLvl v (i + 1))
--       (\icit -> ValLvl (inlApp ms v v' icit) (i + 1))

-- eval :: MetaCxt -> Env -> Tm -> Val
-- eval ms e = \case
--   LocalVar x          -> localVar e x
--   TopVar x v          -> VTopVar x SId v
--   Meta x              -> meta ms x
--   App t u i           -> inlApp ms (eval ms e t) (eval ms e u) i
--   Let _ t u           -> let ~vt = eval ms e t in eval ms (EDef e vt) u
--   InsertedMeta x mask -> applyMask ms e $$! meta ms x $$! mask
--   Lam x i t           -> VLam x i (Closure e t)
--   Pi x i a b          -> VPi x i (eval ms e a) (Closure e b)
--   Irrelevant          -> VIrrelevant
--   U                   -> VU


-- -- | Force metas only.
-- forceM :: MetaCxt -> Val -> Val
-- forceM ms = \case
--   VMeta x sp -> forceMMeta ms x sp
--   t -> t
-- {-# inline forceM #-}

-- forceMMeta :: MetaCxt -> MetaVar -> Spine -> Val
-- forceMMeta ms x sp = runIO do
--   ADL.read ms (coerce x) >>= \case
--     MEUnsolved -> pure $! VMeta x sp
--     MESolved v -> case appSp ms v sp of
--       VMeta x sp -> pure $! forceMMeta ms x sp
--       v          -> pure v

-- -- | Force both metas and top unfoldings.
-- forceMT :: MetaCxt -> Val -> Val
-- forceMT ms = \case
--   VMeta x sp     -> forceMTMeta ms x sp
--   VTopVar x sp v -> forceMT' ms v
--   t              -> t
-- {-# inline forceMT #-}

-- forceMT' :: MetaCxt -> Val -> Val
-- forceMT' ms = \case
--   VMeta x sp     -> forceMTMeta ms x sp
--   VTopVar x sp v -> forceMT' ms v
--   t              -> t

-- forceMTMeta :: MetaCxt -> MetaVar -> Spine -> Val
-- forceMTMeta ms x sp = runIO do
--   ADL.read ms (coerce x) >>= \case
--     MEUnsolved -> pure $ VMeta x sp
--     MESolved v -> pure $! forceMT' ms $! appSp ms v sp
-- {-# noinline forceMTMeta #-}
