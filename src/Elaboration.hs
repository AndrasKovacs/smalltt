{-# options_ghc -Wno-unused-imports #-}

{- |
Enhancement:
  - Put things in Reader monads when it makes sense, use combinators to dive into scopes.
  - Implement bounded unfolding in vUnify.

Things to later benchmark:
  - IO Exception vs error codes in unification
  - Arrays vs lists in renaming
  - Benefit of known call optimization.
  -     storing (in closure) and passing (to eval) local context length
    vs. passing local context length but not storing them in closures
    vs. not passing and not storing context length, instead recomputing it on each lookup.
  - Read monads vs param passing.
-}

module Elaboration where

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.Array.Dynamic (Array)
import qualified Data.Array.Dynamic as A
import Data.Nullable

import Lens.Micro.Platform
import Control.Exception
import Text.Megaparsec.Pos
import Data.IORef
import Data.Function

import Common
import Evaluation
import Syntax
import Values
import ElabState

-- Local elaboration context
--------------------------------------------------------------------------------

data NameEnv = NENil | NESnoc NameEnv {-# unpack #-} Name

-- | Local elaboration context.
data Cxt = Cxt {
  _depth    :: Int,
  _gVals    :: GEnv,
  _vVals    :: VEnv,
  _gTypes   :: Env GTy,
  _vTypes   :: Env VTy,
  _varNames :: NameEnv
  }
makeLenses ''Cxt


-- recordName :: Ix -> Posed Name -> NameOrigin -> NameVars -> NameVars
-- recordName d (T2 p x) origin ns =
--   HM.alter (Just . maybe [T3 origin p d] ((:) (T3 origin p d))) x ns
-- {-# inline recordName #-}

-- | Empty local context.
cnil :: Cxt
cnil = Cxt 0 ENil' ENil' ENil ENil NENil

-- | Add a bound variable to local context.
bind :: Posed Name -> NameOrigin -> GVTy -> Cxt -> Cxt
bind x origin (GV gty vty) (Cxt d gs vs gtys vtys ns) =
  Cxt (d + 1)
      (ESnoc' gs Nothing)
      (ESnoc' vs Nothing)
      (ESnoc gtys gty)
      (ESnoc vtys vty)
      (NESnoc ns (proj2 x))

-- | Add a new definition to local context.
define :: Posed Name -> GV -> GVTy -> Cxt -> Cxt
define x (GV g v) (GV gty vty) (Cxt d gs vs gtys vtys ns) =
  Cxt (d + 1)
      (ESnoc' gs (Just g))
      (ESnoc' vs (Just v))
      (ESnoc gtys gty)
      (ESnoc vtys vty)
      (NESnoc ns (proj2 x))

bindSrc, bindIns :: Posed Name -> GVTy -> Cxt -> Cxt
bindSrc x = bind x NOSource
bindIns x = bind x NOInserted


-- Unification
--------------------------------------------------------------------------------

{-
Currently, we don't track meta types, hence don't do pruning on metas at all.


Two basic operations: conversion, scope check.

Conversion:
  1. Check local conversion; track rigidity of conversion context, solve
     metas in rigid context but throw error when encountering metas
     in flex context. We throw rigidity of context as error.

  2. If local conversion throws flex, we do full conversion.

Scope check:
  1. Do scope check on local value. While doing this, build meta solution
     candidate as a Tm. If scope check succeeds, return this candidate.

     Illegal variable occurrences are possible in eventual meta solutions, but
     we replace all illegal occurrences with Irrelevant during scope checking,
     so evaluation will never encounter ill-scoped variables.

  2. We always use the local solution candidate. If local scope check fails
     flexibly we have to do full scope check.

-}

--------------------------------------------------------------------------------

data Renaming = RNil | RCons Ix Ix Renaming

lookupRen :: Renaming -> Ix -> Nullable Ix
lookupRen (RCons k v ren) x
  | x == k    = Some v
  | otherwise = lookupRen ren x
lookupRen RNil _ = Null

lookupNameEnv :: NameEnv -> Ix -> Name
lookupNameEnv = go where
  go NENil         _ = error "lookupNameEnv: impossible"
  go (NESnoc ns n) 0 = n
  go (NESnoc ns n) x = go ns (x - 1)

lams :: NameEnv -> Renaming -> Tm -> Tm
lams ns = go where
  go RNil            t = t
  go (RCons x y ren) t = go ren (Lam (NI (lookupNameEnv ns x) Expl) t)

registerSolution :: MetaIx -> Tm -> IO ()
registerSolution (MetaIx i j) t = do
  TEntry _ _ _ ms <- A.read top i
  A.write ms j (Some (MEntry t (gvEval 0 ENil' ENil' t)))

--------------------------------------------------------------------------------

data Rigidity = Rigid | Flex deriving Show
instance Exception Rigidity

-- | Scope
vRename :: Ix -> MetaIx -> T2 Int Renaming -> Val -> Tm
vRename d occurs (T2 renl ren) = go d Rigid ren where
  shift = d - renl

  go :: Ix -> Rigidity -> Renaming -> Val -> Tm
  go d r ren = \case
    VNe h vsp ->
      let h' = case h of
            HLocal x -> case lookupRen ren x of
              Null   -> throw r
              Some y -> LocalVar y
            HTop   x -> TopVar x
            HMeta  x | x == occurs -> throw r
                     | otherwise   -> MetaVar x
      in goSp d h' ren vsp
    VLam x t    -> Lam x (go (d + 1) r (RCons d (d - shift) ren) (vInst t (VLocal d)))
    VPi x a b   -> Pi x (go d r ren a) (go (d + 1) r (RCons d (d - shift) ren) (vInst b (VLocal d)))
    VU          -> U
    VIrrelevant -> Irrelevant

  goSp :: Ix -> Tm -> Renaming -> VSpine -> Tm
  goSp d t ren (SApp vsp v i) = App (goSp d t ren vsp) (go d Flex ren v) i
  goSp d t ren SNil           = t

-- | Try to unify local values. May succeed with () or throw Rigidity. A rigid
--   error is unrecoverable and will be reported, a flex error can be rectified
--   if full unification succeeds later. TODO: annotate rigid errors with
--   information.
vUnify :: Cxt -> Val -> Val -> IO ()
vUnify cxt v v' = go (cxt^.depth) (cxt^.varNames) Rigid v v' where

  go :: Ix -> NameEnv -> Rigidity -> Val -> Val -> IO ()
  go d ns r v v' = case (v, v') of
    (VIrrelevant, _) -> pure ()
    (_, VIrrelevant) -> pure ()

    (VU, VU) -> pure ()

    (VLam (NI n i) t, VLam _ t') ->
      go (d + 1) (NESnoc ns n) r (vInst t (VLocal d)) (vInst t' (VLocal d))
    (VLam (NI n i) t, t'       ) ->
      go (d + 1) (NESnoc ns n) r (vInst t (VLocal d)) (vApp t' (VLocal d) i)
    (t       , VLam (NI n' i') t') ->
      go (d + 1) (NESnoc ns n') r (vApp t (VLocal d) i') (vInst t' (VLocal d))

    (VPi (NI n i) a b, VPi x' a' b') -> do
      go d ns r a a'
      go (d + 1) (NESnoc ns n) r (vInst b (VLocal d)) (vInst b' (VLocal d))

    (VNe (HTop x) vsp, VNe (HTop x') vsp')    | x == x' -> goSp d ns vsp vsp'
    (VNe (HLocal x) vsp, VNe (HLocal x') vsp')| x == x' -> goSp d ns vsp vsp'
    (VNe (HMeta x) vsp, VNe (HMeta x') vsp') -> case compare x x' of
      LT -> solve d ns r x' vsp' (VNe (HMeta x) vsp)
      GT -> solve d ns r x vsp (VNe (HMeta x') vsp')
      EQ -> goSp d ns vsp vsp'

    (VNe (HMeta x) vsp, t') -> solve d ns r x vsp t'
    (t, VNe (HMeta x') vsp') -> solve d ns r x' vsp' t

    (t, t') -> throw r

  goSp :: Ix -> NameEnv -> VSpine -> VSpine -> IO ()
  goSp d ns (SApp vsp v _) (SApp vsp' v' _) = goSp d ns vsp vsp' >> go d ns Flex v v'
  goSp d ns SNil            SNil            = pure ()
  goSp _ _  _               _               = error "vUnify.goSp: impossible"

  checkSpine :: VSpine -> T2 Int Renaming
  checkSpine = go where
    go (SApp vsp v i) = case v of
      VLocal x -> case go vsp of
        T2 d ren -> T2 (d + 1) (RCons x d ren)
      _ -> throw Flex
    go SNil = T2 0 RNil

  solve :: Ix -> NameEnv -> Rigidity -> MetaIx -> VSpine -> Val -> IO ()
  solve d ns Flex  x vsp ~v = throw Flex
  solve d ns Rigid x vsp ~v = case lookupMeta x of
    Some{} -> throw Flex
    _      -> do
      let ren = checkSpine vsp
          rhs = lams ns (proj2 ren) (vRename d x ren v)
      registerSolution x rhs


gvUnify :: Cxt -> GV -> GV -> IO ()
gvUnify cxt gv@(GV g v) gv'@(GV g' v') =
  catch (vUnify cxt v v') $ \case
    Rigid -> error "gvUnify: can't unify"
    Flex  -> go (cxt^.depth) (cxt^.varNames) gv gv'
  where
    go :: Ix -> NameEnv -> GV -> GV -> IO ()
    go d ns (GV g v) (GV g' v') = case (gForce g, gForce g') of
      (GIrrelevant, _) -> pure ()
      (_, GIrrelevant) -> pure ()

      (GU, GU) -> pure ()

      (GLam (NI n i) t, GLam _ t') -> let d' = gvLocal d in
        go (d + 1) (NESnoc ns n) (gvInst t d') (gvInst t' d')

      (GLam (NI n i) t, t'       ) -> let d' = gvLocal d in
        go (d + 1) (NESnoc ns n) (gvInst t d') (gvApp t' d' i)

      (t       , GLam (NI n' i') t') -> let d' = gvLocal d in
        go (d + 1) (NESnoc ns n') (gvApp t d' i') (gvInst t' d')

      (GPi (NI n i) a b, GPi x' a' b') -> do
        let d' = gvLocal d
        go d ns a a'
        go (d + 1) (NESnoc ns n) (gvInst b d') (gvInst b' d')

      (GNe (HTop x)   gsp vsp, GNe (HTop x')   gsp' vsp') | x == x' -> goSp d ns gsp gsp' vsp vsp'
      (GNe (HLocal x) gsp vsp, GNe (HLocal x') gsp' vsp') | x == x' -> goSp d ns gsp gsp' vsp vsp'
      (g@(GNe (HMeta x) gsp vsp), g'@(GNe (HMeta x')  gsp' vsp')) -> case compare x x' of
        LT -> solve d ns x' gsp' (GV g v)
        GT -> solve d ns x gsp (GV g' v')
        EQ -> goSp d ns gsp gsp' vsp vsp'

      (GNe (HMeta x) gsp vsp, g') -> solve d ns x gsp (GV g' v')
      (g, GNe (HMeta x') gsp' vsp') -> solve d ns x' gsp' (GV g v)

      (g, g') -> error "gvUnify: can't unify"

    goSp :: Ix -> NameEnv -> GSpine -> GSpine -> VSpine -> VSpine -> IO ()
    goSp d ns (SApp gsp g _) (SApp gsp' g' _)
              (SApp vsp v _) (SApp vsp' v' _) =    goSp d ns gsp gsp' vsp vsp'
                                                >> go d ns (GV g v) (GV g' v')
    goSp d ns SNil SNil SNil SNil = pure ()
    goSp _ _  _    _    _    _    = error "gvUnify.goSp: impossible"

    checkSpine :: GSpine -> T2 Int Renaming
    checkSpine = go where
      go (SApp gsp g i) = case gForce g of
        GLocal x -> case go gsp of
          T2 d ren -> T2 (d + 1) (RCons x d ren)
        _ -> error "gvUnify: non-variable in meta spine"
      go SNil = T2 0 RNil

    solve :: Ix -> NameEnv -> MetaIx -> GSpine -> GV -> IO ()
    solve d ns x gsp gv = undefined

    rename :: Ix -> MetaIx -> T2 Int Renaming -> GV -> IO Tm
    rename d occurs (T2 renl ren) (GV g v) =
      catch (pure $! vRename d occurs (T2 renl ren) v) (\case
        Flex  -> pure (go d ren g)
        Rigid -> error "gvUnify.rename: ill-scoped solution candidate")
      where
        shift = d - renl

        go :: Ix -> Renaming -> Glued -> Tm
        go d ren = \case
          GNe h gsp vsp ->
            let h' = case h of
                  HLocal x -> case lookupRen ren x of
                    Null   -> error "gvUnify.rename: ill-scoped solution candidate"
                    Some y -> LocalVar y
                  HTop x  -> TopVar x
                  HMeta x | x == occurs -> error "occurs check"
                          | otherwise   -> MetaVar x
            in

      -- go d ren where
      -- shift = d - renl

      -- go :: Ix -> Renaming ->

  -- rename :: Ix -> MetaIx -> T2 Int Renaming -> Val -> Tm
  -- rename d occurs (T2 renl ren) = go d Rigid ren where

  --   shift = d - renl

  --   go :: Ix -> Rigidity -> Renaming -> Val -> Tm
  --   go d r ren = \case
  --     VNe h vsp ->
  --       let h' = case h of
  --             HLocal x -> case lookupRen ren x of
  --               Null   -> throw r
  --               Some y -> LocalVar y
  --             HTop   x -> TopVar x
  --             HMeta  x | x == occurs -> throw r
  --                      | otherwise   -> MetaVar x
  --       in goSp d h' ren vsp
  --     VLam x t    -> Lam x (go (d + 1) r (RCons d (d - shift) ren) (vInst t (VLocal d)))
  --     VPi x a b   -> Pi x (go d r ren a) (go (d + 1) r (RCons d (d - shift) ren) (vInst b (VLocal d)))
  --     VU          -> U
  --     VIrrelevant -> Irrelevant

  --   goSp :: Ix -> Tm -> Renaming -> VSpine -> Tm
  --   goSp d t ren (SApp vsp v i) = App (goSp d t ren vsp) (go d Flex ren v) i
  --   goSp d t ren SNil           = t

  -- solve :: Ix -> NameEnv -> Rigidity -> MetaIx -> VSpine -> Val -> IO ()
  -- solve d ns Flex  x vsp ~v = throw Flex
  -- solve d ns Rigid x vsp ~v = case lookupMeta x of
  --   Some{} -> throw Flex
  --   _      -> do
  --     let ren = checkSpine vsp
  --         rhs = lams ns (proj2 ren) (rename d x ren v)
  --     registerSolution x rhs


--------------------------------------------------------------------------------
