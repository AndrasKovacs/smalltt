{-# options_ghc -Wno-unused-imports #-}

{- |

Roadmap:
  1. not-so-pretty version with parameter passing and code duplication, which:
     - works
     - has test
     - has benchmarks
  2. prettify and benchmark various changes and improvements


n--------------------------------------------------------------------------------

Enhancement:
  - Put things in Reader monads when it makes sense, use combinators to dive into scopes.
  - Implement bounded unfolding in vUnify.
  - Have proper error messages
    - Throw informative Rigid errors from local operations
    - maybe even implement a simple error tracing, by adding more catch-es.

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
  _depth     :: Int,
  _gVals     :: GEnv,
  _vVals     :: VEnv,
  _gTypes    :: Env GTy,
  _vTypes    :: Env VTy,
  _nameTable :: NameTable,  -- ^ Structure for getting indices for names during elaboration.
  _nameEnv   :: NameEnv    -- ^ Structure for getting names for local indices during unification.
  }
makeLenses ''Cxt


recordName :: Ix -> Posed Name -> Scope -> NameOrigin -> NameTable -> NameTable
recordName d (T2 p x) sc origin ntbl =
  HM.alter (Just . maybe (ESnoc' ENil' (T4 sc p origin d))
                         (flip ESnoc' (T4 sc p origin d)))
           x ntbl
{-# inline recordName #-}

-- | Empty local context.
cnil :: Cxt
cnil = Cxt 0 ENil' ENil' ENil ENil mempty NENil

-- | Add a bound variable to local context.
localBind :: Posed Name -> NameOrigin -> GVTy -> Cxt -> Cxt
localBind x origin (GV gty vty) (Cxt d gs vs gtys vtys ninf ns) =
  Cxt (d + 1)
      (ESnoc' gs Nothing)
      (ESnoc' vs Nothing)
      (ESnoc gtys gty)
      (ESnoc vtys vty)
      (recordName d x Local NOSource ninf)
      (NESnoc ns (proj2 x))

-- | Add a new definition to local context.
localDefine :: Posed Name -> GV -> GVTy -> Cxt -> Cxt
localDefine x (GV g v) (GV gty vty) (Cxt d gs vs gtys vtys ninf ns) =
  Cxt (d + 1)
      (ESnoc' gs (Just g))
      (ESnoc' vs (Just v))
      (ESnoc gtys gty)
      (ESnoc vtys vty)
      (recordName d x Local NOInserted ninf)
      (NESnoc ns (proj2 x))

localBindSrc, localBindIns :: Posed Name -> GVTy -> Cxt -> Cxt
localBindSrc x = localBind x NOSource
localBindIns x = localBind x NOInserted


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


-- Unification
--------------------------------------------------------------------------------

data Rigidity = Rigid | Flex deriving Show
instance Exception Rigidity

-- we need a verrsion of vRename which throws and aborts, and a version which
-- always returns a Tm, possibly together with a flex or rigid error.
vRename :: (Rigidity -> IO ()) -> Ix -> MetaIx -> T2 Int Renaming -> Val -> Tm
vRename throwAction d occurs (T2 renl ren) = go d Rigid ren where
  shift = d - renl

  go :: Ix -> Rigidity -> Renaming -> Val -> Tm
  go d r ren = \case
    VNe h vsp ->
      let h' = case h of
            HLocal x -> case lookupRen ren x of
              Null   -> seq (runIO (throwAction r)) Irrelevant
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
{-# inline vRename #-}

vRenameShortCut :: Ix -> MetaIx -> T2 Int Renaming -> Val -> Tm
vRenameShortCut = vRename throw

vRenameRefError :: IORef (Nullable Rigidity) -> Ix -> MetaIx -> T2 Int Renaming -> Val -> Tm
vRenameRefError ref = vRename (writeIORef ref . Some)


-- | Try to unify local values. May succeed with () or throw Rigidity. A rigid
--   error is unrecoverable and will be reported, a flex error can be rectified
--   if full unification succeeds later. TODO: annotate rigid errors with
--   information.
vUnify :: Cxt -> Val -> Val -> IO ()
vUnify cxt v v' = go (cxt^.depth) (cxt^.nameEnv) Rigid v v' where

  go :: Ix -> NameEnv -> Rigidity -> Val -> Val -> IO ()
  go d ns r v v' = case (v, v') of
    (VIrrelevant, _) -> pure ()
    (_, VIrrelevant) -> pure ()

    (VU, VU) -> pure ()

    (VLam (NI n i) t, VLam _ t') -> let d' = VLocal d in
      go (d + 1) (NESnoc ns n) r (vInst t d') (vInst t' d')
    (VLam (NI n i) t, t'       ) -> let d' = VLocal d in
      go (d + 1) (NESnoc ns n) r (vInst t d') (vApp t' d' i)
    (t       , VLam (NI n' i') t') -> let d' = VLocal d in
      go (d + 1) (NESnoc ns n') r (vApp t d' i') (vInst t' d')

    (VPi (NI n i) a b, VPi x' a' b') -> do
      go d ns r a a'
      let d' = VLocal d
      go (d + 1) (NESnoc ns n) r (vInst b d') (vInst b' d')

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
      VLam x t -> error "TODO: eta-contraction in meta patterns"
      _        -> throw Flex
    go SNil = T2 0 RNil

  solve :: Ix -> NameEnv -> Rigidity -> MetaIx -> VSpine -> Val -> IO ()
  solve d ns Flex  x vsp ~v = throw Flex
  solve d ns Rigid x vsp ~v = case lookupMeta x of
    Some{} -> throw Flex
    _      -> do
      let ren = checkSpine vsp
          rhs = lams ns (proj2 ren) (vRenameShortCut d x ren v)
      registerSolution x rhs

gvRename :: Ix -> MetaIx -> T2 Int Renaming -> GV -> IO Tm
gvRename d occurs (T2 renl ren) (GV g v) = do
  err <- newIORef (Null @Rigidity)
  let rhs   = vRenameRefError err d occurs (T2 renl ren) v
      shift = d - renl
  readIORef err >>= \case
    Null       -> pure rhs
    Some Rigid -> error "gvRename: solution scope error"
    Some Flex  -> go d ren g >> pure rhs where

      go :: Ix -> Renaming -> Glued -> IO ()
      go d ren g = case gForce g of
        GNe h gsp _ -> do
          case h of
            HLocal x -> case lookupRen ren x of
              Null   -> error "gvUnify.rename: ill-scoped solution candidate"
              Some{} -> pure ()
            HTop{} -> pure ()
            HMeta x | x == occurs -> error "gvUnify.rename: occurs check"
                    | otherwise   -> pure ()
          goSp d ren gsp
        GLam x t -> go (d + 1) (RCons d (d - shift) ren) (gInst t (gvLocal d))
        GPi x (GV a _) b -> go d ren a >> go (d + 1) (RCons d (d - shift) ren) (gInst b (gvLocal d))
        GU -> pure ()
        GIrrelevant -> pure ()

      goSp :: Ix -> Renaming -> GSpine -> IO ()
      goSp d ren SNil           = pure ()
      goSp d ren (SApp gsp g _) = goSp d ren gsp >> go d ren g


gvUnify :: Cxt -> GV -> GV -> IO ()
gvUnify cxt gv@(GV g v) gv'@(GV g' v') =
  catch (vUnify cxt v v') $ \case
    Rigid -> error "gvUnify: can't unify"
    Flex  -> go (cxt^.depth) (cxt^.nameEnv) gv gv'
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
        GLam x t -> error "gvUnify: TODO: eta-contraction in meta patterns"
        _        -> error "gvUnify: non-variable in meta spine"
      go SNil = T2 0 RNil

    solve :: Ix -> NameEnv -> MetaIx -> GSpine -> GV -> IO ()
    solve d ns x gsp gv = do
      let ren = checkSpine gsp
      rhs <- lams ns (proj2 ren) <$> gvRename d x ren gv
      registerSolution x rhs


------------------------------------------------------------------------------------------
