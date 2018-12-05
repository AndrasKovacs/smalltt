{- |

Roadmap:
  1. not-so-pretty version with parameter passing and code duplication, which:
     - works
     - has test
     - has benchmarks
  2. prettify and benchmark various changes and improvements

--------------------------------------------------------------------------------

Enhancement:
  - Put things in Reader monads when it makes sense, use combinators to dive into scopes.
  - Fix buggy source location reporting, probably move source positions into elab reader monad.
  - Have proper error messages
    - Throw informative Rigid errors from local operations
    - maybe even implement a simple error tracing, by adding more catch-es.
  - make Ix and Lvl newtype, do safer API

Things to later benchmark:
  - IO Exception vs error codes in unification
  - Arrays vs lists in renaming
  - Benefit of known call optimization.
  -     storing (in closure) and passing (to eval) local context length
    vs. passing local context length but not storing them in closures
    vs. not passing and not storing context length, instead recomputing it on each lookup.
  - Reader monads vs param passing.
-}

module Elaboration where

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.Array.Dynamic as A
import qualified Data.Array.Dynamic.Unlifted as UA
import qualified Data.Text.Short as T
import Text.Megaparsec.Pos
import Text.Printf

import Control.Exception
import Control.Monad
import Data.IORef

import Common
import ElabState
import Evaluation
import Syntax
import Values
import qualified Presyntax as P
import Pretty

-- import Debug.Trace

-- Local elaboration context
--------------------------------------------------------------------------------

-- Naming state
--------------------------------------------------------------------------------

-- | Inserted names come from inserting implicit binders during elaboration.
--   Other names come from user input.
data NameOrigin = NOInserted | NOSource deriving Show
data NameInfo = NITop SourcePos Lvl | NILocal SourcePos NameOrigin Lvl

instance Show NameInfo where
  show (NITop _ i)     = "NITop " ++ show i
  show (NILocal _ o i) = printf "NILocal %s %d" (show o) i

-- | Reverse map from names to all de Bruijn levels with the keyed name.
--   Indices are sorted, the lowest in scope is the first element.  We also keep
--   track of source positions of binders. We only use this structure for name
--   lookup during elaboration.
type NameTable = HashMap Name [NameInfo]
data BoundIndices = BINil | BISnoc BoundIndices Lvl

-- | Local elaboration context.
data Cxt = Cxt {
  _size      :: Int, -- ^ Number of local entries.
  _gVals     :: GEnv, -- ^ Glued values of definitions.
  _vVals     :: VEnv, -- ^ Local values of definitions.
  _types     :: [GVTy], -- ^ Types of entries.

  -- | Structure for getting indices for names during elaboration.
  _nameTable :: NameTable,

  -- | Structure for getting names for local indices during unification. Only
  --   used for getting informative (source-originating) names for binders in
  --   meta solutions.
  _names        :: Names,
  -- | List of local bound indices. Used for making spines for fresh metas.
  _boundIndices :: BoundIndices
  }

addName :: Name -> NameInfo -> NameTable -> NameTable
addName n ni ntbl = if T.null n
  then ntbl
  else HM.alter (Just . maybe [ni] (ni:)) n ntbl
{-# inline addName #-}

-- | Initial local context.
initCxt :: NameTable -> Cxt
initCxt ntbl = Cxt 0 ENil ENil [] ntbl NNil BINil

-- | Add a bound variable to local context.
localBind :: Posed Name -> NameOrigin -> GVTy -> Cxt -> Cxt
localBind x origin gvty (Cxt l gs vs tys ninf ns bis) =
  Cxt (l + 1)
      (ESkip gs)
      (ESkip vs)
      (gvty:tys)
      (addName (unPosed x) (NILocal (posOf x) origin l) ninf)
      (NSnoc ns (unPosed x))
      (BISnoc bis l)

-- | Add a new definition to local context.
localDefine :: Posed Name -> GV -> GVTy -> Cxt -> Cxt
localDefine x (GV g v) gvty (Cxt l gs vs tys ninf ns bis) =
  Cxt (l + 1)
      (EDef gs g)
      (EDef vs v)
      (gvty:tys)
      (addName (unPosed x) (NILocal (posOf x) NOSource l) ninf)
      (NSnoc ns (unPosed x))
      bis

localBindSrc, localBindIns :: Posed Name -> GVTy -> Cxt -> Cxt
localBindSrc x = localBind x NOSource
localBindIns x = localBind x NOInserted

--------------------------------------------------------------------------------

lookupName :: Ix -> Names -> Name
lookupName = go where
  go 0 (NSnoc _ n) = n
  go n (NSnoc ns _) = go (n - 1) ns
  go _ _ = error "lookupName: impossible"

lams :: Lvl -> Names -> Renaming -> Tm -> Tm
lams l ns = go where
  go RNil            t = t
  go (RCons x y ren) t = go ren (Lam (Named (lookupName (l - x - 1) ns) Expl) t)

registerSolution :: Meta -> Tm -> IO ()
registerSolution (Meta i j) t = do
  arr <- UA.unsafeRead metas i
  A.unsafeWrite arr j (MESolved t (gvEval ENil ENil t))
{-# inline registerSolution #-}

vShowTm :: Cxt -> Val -> String
vShowTm cxt = showTm (_names cxt) . vQuote (_size cxt)

gShowTm :: Cxt -> Glued -> String
gShowTm cxt = showTm (_names cxt) . gQuote (_size cxt)

showTm' :: Cxt -> Tm -> String
showTm' cxt = showTm (_names cxt)


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

data ElabError = EEFlex String | EERigid String deriving Show
instance Exception ElabError

mkError :: Rigidity -> String -> ElabError
mkError Flex ~msg = let pos = runIO (readIORef currPos)
                    in EEFlex (sourcePosPretty pos ++ ":\n\n" ++ msg ++ "\n")
mkError _    ~msg = let pos = runIO (readIORef currPos)
                    in EERigid (sourcePosPretty pos ++ ":\n\n" ++ msg ++ "\n")
{-# inline mkError #-}

-- we need a version of vRename which throws and aborts, and a version which
-- always returns a Tm, possibly together with a flex or rigid error.
vQuoteSolution :: (ElabError -> IO ()) -> Lvl -> Meta -> T2 Lvl Renaming -> Val -> IO Tm
vQuoteSolution throwAction = \l occurs (T2 renl ren) ->
  let
    shift = l - renl

    go :: Lvl -> Rigidity -> Renaming -> Val -> IO Tm
    go l r ren = \case
      VNe h vsp -> do
        h' <- case h of
              HLocal x -> case applyRen ren x of
                (-1)   -> do
                            throwAction $ mkError r (printf "Out of scope variable: %d" x)
                            pure Irrelevant
                y      -> pure (LocalVar (l - shift - y - 1))
              HTop   x -> pure (TopVar x)
              HMeta  x | x == occurs -> do
                           throwAction $ mkError r "Occurs check"
                           pure Irrelevant
                       | otherwise   -> pure (MetaVar x)
        goSp l h' ren vsp
      VLam x t    -> Lam x <$> go (l + 1) r (RCons l (l - shift) ren) (vInst t (VLocal l))
      VPi x a b   -> Pi x <$> go l r ren a <*> go (l + 1) r (RCons l (l - shift) ren) (vInst b (VLocal l))
      VU          -> pure U
      VIrrelevant -> pure Irrelevant

    goSp :: Lvl -> Tm -> Renaming -> VSpine -> IO Tm
    goSp l t ren (SAppI vsp v) = AppI <$> goSp l t ren vsp <*> go l Flex ren v
    goSp l t ren (SAppE vsp v) = AppE <$> goSp l t ren vsp <*> go l Flex ren v
    goSp l t ren SNil          = pure t

  in go l Rigid ren
{-# inline vQuoteSolution #-}

vQuoteSolutionShortCut :: Lvl -> Meta -> T2 Lvl Renaming -> Val -> IO Tm
vQuoteSolutionShortCut = vQuoteSolution throw
{-# inline vQuoteSolutionShortCut #-}

vQuoteSolutionRefError :: IORef (Maybe ElabError) -> Lvl -> Meta -> T2 Lvl Renaming -> Val -> IO Tm
vQuoteSolutionRefError ref = vQuoteSolution (writeIORef ref . Just)
{-# inline vQuoteSolutionRefError #-}


type Unfolding = Int

-- | Try to unify local values. May succeed with () or throw Rigidity. A rigid
--   error is unrecoverable and will be reported, a flex error can be rectified
--   if full unification succeeds later. TODO: annotate rigid errors with
--   information.
unfoldLimit :: Unfolding
unfoldLimit = 2
{-# inline unfoldLimit #-}

vUnify :: Cxt -> Val -> Val -> IO ()
vUnify cxt v v' = go (_size cxt) unfoldLimit (_names cxt) Rigid v v' where

  go :: Lvl -> Unfolding -> Names -> Rigidity -> Val -> Val -> IO ()
  go l u ns r v v' = case (v, v') of
    -- irrelevance
    (VIrrelevant, _) -> pure ()
    (_, VIrrelevant) -> pure ()

    -- solve with same heads
    (VU, VU) -> pure ()

    (VLam (Named n i) t, VLam _ t') -> let var = VLocal l in
      go (l + 1) u (NSnoc ns n) r (vInst t var) (vInst t' var)
    (VLam (Named n i) t, t'       ) -> let var = VLocal l in
      go (l + 1) u (NSnoc ns n) r (vInst t var) (vApp i t' var)
    (t       , VLam (Named n' i') t') -> let var = VLocal l in
      go (l + 1) u (NSnoc ns n') r (vApp i' t var) (vInst t' var)

    (VPi (Named n i) a b, VPi (Named _ i') a' b') | i == i' -> do
      go l u ns r a a'
      let var = VLocal l
      go (l + 1) u (NSnoc ns n) r (vInst b var) (vInst b' var)

    (VNe (HTop x) vsp, VNe (HTop x') vsp') | x == x' ->
      goSp l u ns (r `meld` topRigidity x `meld` topRigidity x') vsp vsp'

    (VNe (HLocal x) vsp, VNe (HLocal x') vsp') | x == x' ->
      goSp l u ns r vsp vsp'

    (VNe (HMeta x) vsp, VNe (HMeta x') vsp') | x == x' ->
      goSp l u ns (r `meld` metaRigidity x `meld` metaRigidity x') vsp vsp'

    -- meta sides
    (v@(VNe (HMeta x) vsp), v')
      | MESolved _ (GV _ v) <- lookupMeta x ->
        if u > 0 then go l (u - 1) ns r (vAppSpine v vsp) v'
                 else cantUnify l ns Flex v v'
      | MEUnsolved <- lookupMeta x, Rigid <- r ->
        solve l ns x vsp v'

    (v, v'@(VNe (HMeta x') vsp'))
      | MESolved _ (GV _ v') <- lookupMeta x' ->
        if u > 0 then go l (u - 1) ns r v (vAppSpine v' vsp')
                 else cantUnify l ns Flex v v'
      | MEUnsolved <- lookupMeta x', Rigid <- r ->
        solve l ns  x' vsp' v

    -- top sides
    (v@(VNe (HTop x) vsp), v')
      | EDDefinition _ (GV _ v) <- _entryDef (lookupTop x) ->
        if u > 0 then go l (u - 1) ns r (vAppSpine v vsp) v'
                 else cantUnify l ns Flex v v'

    (v, v'@(VNe (HTop x') vsp'))
      | EDDefinition _ (GV _ v') <- _entryDef (lookupTop x') ->
        if u > 0 then go l (u - 1) ns r v (vAppSpine v' vsp')
                 else cantUnify l ns Flex v v'

    (v, v') -> cantUnify l ns r v v'

  cantUnify d ns r v v' =
    throw $ mkError r $
      printf "Can't (locally) unify\n\n%s\n\nwith\n\n%s"
        (showTm ns (vQuote d v)) (showTm ns (vQuote d v'))

  checkSpine :: VSpine -> T2 Lvl Renaming
  checkSpine = go where
    go SNil = T2 0 RNil
    go (SAppI vsp v) = case v of
      VLocal x -> case go vsp of
        T2 l ren -> T2 (l + 1) (RCons x l ren)
      _          -> throw $ mkError Flex "non-variable in meta spine"
    go (SAppE vsp v) = case v of
      VLocal x -> case go vsp of
        T2 l ren -> T2 (l + 1) (RCons x l ren)
      _          -> throw $ mkError Flex "non-variable in meta spine"

  solve :: Lvl -> Names -> Meta -> VSpine -> Val -> IO ()
  solve l ns x vsp ~v = do
    let ren = checkSpine vsp

    rhs <- lams l ns (proj2 ren) <$> vQuoteSolutionShortCut l x ren v

    -- let Meta i j = x
    -- traceM (printf "solution candidate: %s" (show (vQuote l v)))
    -- traceM (printf "solved meta %d.%d with %s" i j (show rhs))

    registerSolution x rhs

  goSp :: Lvl -> Unfolding -> Names -> Rigidity -> VSpine -> VSpine -> IO ()
  goSp l u ns r (SAppI vsp v) (SAppI vsp' v') = goSp l u ns r vsp vsp' >> go l u ns r v v'
  goSp l u ns r (SAppE vsp v) (SAppE vsp' v') = goSp l u ns r vsp vsp' >> go l u ns r v v'
  goSp l u ns r SNil            SNil          = pure ()
  goSp _ _ _  r _               _             = error "vUnify.goSp: impossible"


gvQuoteSolution :: Lvl -> Meta -> T2 Lvl Renaming -> GV -> IO Tm
gvQuoteSolution l occurs (T2 renl ren) (GV g v) = do
  err <- newIORef Nothing
  rhs <- vQuoteSolutionRefError err l occurs (T2 renl ren) v
  let shift = l - renl
  readIORef err >>= \case
    Nothing            -> pure rhs
    Just (EERigid msg) -> error msg
    Just (EEFlex msg)  -> go l ren g >> pure rhs where

      go :: Lvl -> Renaming -> Glued -> IO ()
      go l ren g = case gForce g of
        GNe h gsp _ -> do
          case h of
            HLocal x -> case applyRen ren x of
              (-1)   -> reportError "ill-scoped solution candidate"
              _      -> pure ()
            HTop{} -> pure ()
            HMeta x | x == occurs -> reportError "occurs check"
                    | otherwise   -> pure ()
          goSp l ren gsp
        GLam x t -> go (l + 1) (RCons l (l - shift) ren) (gInst t (gvLocal l))
        GPi x (GV a _) b -> go l ren a >> go (l + 1) (RCons l (l - shift) ren) (gInst b (gvLocal l))
        GU -> pure ()
        GIrrelevant -> pure ()

      goSp :: Lvl -> Renaming -> GSpine -> IO ()
      goSp l ren SNil          = pure ()
      goSp l ren (SAppI gsp g) = goSp l ren gsp >> go l ren g
      goSp l ren (SAppE gsp g) = goSp l ren gsp >> go l ren g

gvUnify :: Cxt -> GV -> GV -> IO ()
gvUnify cxt gv@(GV g v) gv'@(GV g' v') =
  catch (do
    -- let t1 = vShowTm cxt v
    --     t2 = vShowTm cxt v'
    vUnify cxt v v' -- <* traceM (printf "locally unified: %s   %s" t1 t2)
    )
  $ \case
    EERigid msg -> error msg
    EEFlex  msg -> do
      -- traceM (printf "failed local unify: %s\n%s\n%s\n%s"
      --          (show (vQuote (_size cxt) v)) (show (vQuote (_size cxt) v'))
      --         (vShowTm cxt v) (vShowTm cxt v'))
      -- traceM (printf "trying global unify: %s   %s" (gShowTm cxt g) (gShowTm cxt g'))
      go (_size cxt) (_names cxt) gv gv'
  where
    go :: Lvl -> Names -> GV -> GV -> IO ()
    go l ns (GV g v) (GV g' v') = case (gForce g, gForce g') of
      (GIrrelevant, _) -> pure ()
      (_, GIrrelevant) -> pure ()

      (GU, GU) -> pure ()

      (GLam (Named n i) t, GLam _ t') -> let var = gvLocal l in
        go (l + 1) (NSnoc ns n) (gvInst t var) (gvInst t' var)

      (GLam (Named n i) t, t'       ) -> let var = gvLocal l in
        go (l + 1) (NSnoc ns n) (gvInst t var) (gvApp i t' var)

      (t       , GLam (Named n' i') t') -> let var = gvLocal l in
        go (l + 1) (NSnoc ns n') (gvApp i' t var) (gvInst t' var)

      (GPi (Named n i) a b, GPi (Named _ i') a' b') | i == i' -> do
        let var = gvLocal l
        go l ns a a'
        go (l + 1) (NSnoc ns n) (gvInst b var) (gvInst b' var)

      (GNe (HTop x)   gsp vsp, GNe (HTop x')   gsp' vsp') | x == x' -> goSp l ns gsp gsp' vsp vsp'
      (GNe (HLocal x) gsp vsp, GNe (HLocal x') gsp' vsp') | x == x' -> goSp l ns gsp gsp' vsp vsp'
      (g@(GNe (HMeta x) gsp vsp), g'@(GNe (HMeta x')  gsp' vsp')) -> case compare x x' of
        LT -> solve l ns x' gsp' (GV g v)
        GT -> solve l ns x gsp (GV g' v')
        EQ -> goSp l ns gsp gsp' vsp vsp'

      (GNe (HMeta x) gsp vsp, g') -> solve l ns x gsp (GV g' v')
      (g, GNe (HMeta x') gsp' vsp') -> solve l ns x' gsp' (GV g v)

      (g, g') ->
        reportError $
          printf "Can't (globally) unify\n\n%s\n\nwith\n\n%s"
            (showTm ns (gQuote l g)) (showTm ns (gQuote l g'))

    goSp :: Lvl -> Names -> GSpine -> GSpine -> VSpine -> VSpine -> IO ()
    goSp l ns (SAppI gsp g) (SAppI gsp' g')
              (SAppI vsp v) (SAppI vsp' v') = goSp l ns gsp gsp' vsp vsp'
                                              >> go l ns (GV g v) (GV g' v')
    goSp l ns (SAppE gsp g) (SAppE gsp' g')
              (SAppE vsp v) (SAppE vsp' v') = goSp l ns gsp gsp' vsp vsp'
                                              >> go l ns (GV g v) (GV g' v')
    goSp d ns SNil SNil SNil SNil = pure ()
    goSp _ _  _    _    _    _    = error "gvUnify.goSp: impossible"

    checkSpine :: GSpine -> T2 Lvl Renaming
    checkSpine = go where
      go SNil = T2 0 RNil
      go (SAppI gsp g) = case gForce g of
        GLocal x -> case go gsp of
          T2 l ren -> T2 (l + 1) (RCons x l ren)
        GLam x t -> error "gvUnify: TODO: eta-contraction in meta patterns"
        _        -> error "gvUnify: non-variable in meta spine"
      go (SAppE gsp g) = case gForce g of
        GLocal x -> case go gsp of
          T2 l ren -> T2 (l + 1) (RCons x l ren)
        GLam x t -> error "gvUnify: TODO: eta-contraction in meta patterns"
        _        -> error "gvUnify: non-variable in meta spine"

    solve :: Lvl -> Names -> Meta -> GSpine -> GV -> IO ()
    solve l ns x gsp gv = do
      let ren = checkSpine gsp
      rhs <- lams l ns (proj2 ren) <$> gvQuoteSolution l x ren gv
      registerSolution x rhs

-- Elaboration
------------------------------------------------------------------------------------------

data MetaInsertion = MIYes | MINo | MIUntilName Name

gvEval' :: Cxt -> Tm -> GV
gvEval' cxt t = gvEval (_gVals cxt) (_vVals cxt) t
{-# inline gvEval' #-}

gEval' :: Cxt -> Tm -> Glued
gEval' cxt t = gEval (_gVals cxt) (_vVals cxt) t
{-# inline gEval' #-}

newMeta :: Cxt -> IO Tm
newMeta cxt = do
  i     <- subtract 1 <$> UA.size metas
  arr   <- UA.unsafeRead metas i
  j     <- A.size arr
  A.push arr MEUnsolved
  let l   = _size cxt
      bis = _boundIndices cxt
      go BINil          = MetaVar (Meta i j)
      go (BISnoc bis x) = AppE (go bis) (LocalVar (l - x - 1))
  pure (go bis)

check :: Cxt -> P.Tm -> GVTy -> IO Tm
check cxt (updPos -> Posed pos t) (GV gwant vwant) = case (t, gForce gwant) of
  (P.Lam x ni t, GPi (Named x' i') a b) | (case ni of NOName y -> y == x'
                                                      NOImpl   -> i' == Impl
                                                      NOExpl   -> i' == Expl) ->
    Lam (Named x i') <$> check (localBindSrc (Posed pos x) a cxt) t (gvInst b (gvLocal (_size cxt)))
  (t, GPi (Named x Impl) a b) ->
    Lam (Named x Impl) <$> check (localBindIns (Posed pos x) a cxt)
                                 (Posed pos t) (gvInst b (gvLocal (_size cxt)))
  (P.Let x a t u, gwant) -> do
    a <- check cxt a gvU
    let gva = gvEval' cxt a
    t <- check cxt t gva
    let gvt = gvEval' cxt t
    u <- check (localDefine (Posed pos x) gvt gva cxt) u (GV gwant vwant)
    pure (Let (Named x a) t u)
  (P.Hole, _) ->
    newMeta cxt
  (t, gwant) -> do
    T2 t gvhas <- infer MIYes cxt (Posed pos t)
    gvUnify cxt gvhas (GV gwant vwant)
    pure t

insertMetas :: MetaInsertion -> Cxt -> IO (T2 Tm GVTy) -> IO (T2 Tm GVTy)
insertMetas ins cxt inp = case ins of
  MINo  -> inp
  MIYes -> do
    T2 t (GV ga va) <- inp
    let go t (GV (GPi (Named x Impl) a b) va) = do
          m <- newMeta cxt
          go (AppI t m) (gvInst b (gvEval' cxt m))
        go t gva = pure (T2 t gva)
    go t (GV (gForce ga) va)
  MIUntilName x -> do
    T2 t (GV ga va) <- inp
    let go t gva@(GV (GPi (Named x' Impl) a b) va)
          | x  == x'  = pure (T2 t gva)
          | otherwise = do
              m <- newMeta cxt
              go (AppI t m) (gvInst b (gvEval' cxt m))
        go t a = reportError ("No named implicit argument with name " ++ show x)
    go t (GV (gForce ga) va)
{-# inline insertMetas #-}

inferVar :: Cxt -> Name -> IO (T2 Tm GVTy)
inferVar cxt n = do
  T2 t gvty@(GV ga va) <- case HM.lookup n (_nameTable cxt) of
    Nothing -> reportError (printf "Name not in scope: %s" n)
    Just es -> go es where
      go []               = reportError (printf "Name not in scope: %s" n)
      go (NITop pos x:es) = do
        EntryTy _ gvty <- _entryTy <$> A.unsafeRead top x
        pure (T2 (TopVar x) gvty)
      go (NILocal pos origin x:es) = case origin of
        NOInserted -> go es
        NOSource   ->
          pure (T2 (LocalVar (_size cxt - x - 1)) (_types cxt !! (_size cxt - x - 1)))

  -- putStrLn (T.unpack n)
  -- putStrLn (showTm' cxt t)
  -- putStrLn (gShowTm cxt ga)

  pure (T2 t gvty)
{-# inline inferVar #-}

infer :: MetaInsertion -> Cxt -> P.Tm -> IO (T2 Tm GVTy)
infer ins cxt (updPos -> Posed pos t) = case t of
  P.U -> pure (T2 U gvU)

  P.StopMetaIns t -> infer MINo cxt t

  P.Var x -> insertMetas ins cxt (inferVar cxt x)

  P.App t u ni -> insertMetas ins cxt $ do
    T2 t (GV ga va) <- infer
      (case ni of NOName x -> MIUntilName x
                  NOImpl   -> MINo
                  NOExpl   -> MIYes)
      cxt t
    case gForce ga of
      GPi (Named x i') a b -> do
        case ni of
          NOName x -> pure ()
          NOImpl   -> unless (i' == Impl) (reportError "icitness mismatch")
          NOExpl   -> unless (i' == Expl) (reportError "icitness mismatch")
        u <- check cxt u a
        pure (T2 (app i' t u) (gvInst b (gvEval' cxt u)))
      _ -> reportError $
        printf "Expected a function type for expression:\n\n%s\n\nInferred type:\n\n%s"
           (showTm' cxt t) (gShowTm cxt ga)

  P.Pi (Named x i) a b -> do
    a <- check cxt a gvU
    b <- check (localBindSrc (Posed pos x) (gvEval' cxt a) cxt) b gvU
    pure (T2 (Pi (Named x i) a b) gvU)

  P.Let x a t u -> do
    a <- check cxt a gvU
    let gva = gvEval' cxt a
    t <- check cxt t gva
    let gvt = gvEval' cxt t
    T2 u gvb <- infer ins (localDefine (Posed pos x) gvt gva cxt) u
    pure (T2 (Let (Named x a) t u) gvb)

  P.Lam x ni t -> insertMetas ins cxt $ do
    i <- case ni of
      NOName x -> reportError "Can't infer type for lambda with named arguments"
      NOImpl -> pure Impl
      NOExpl -> pure Expl
    gva@(GV ga va) <- gvEval' cxt <$> newMeta cxt
    T2 t gvb@(GV gb vb) <- infer MIYes (localBindSrc (Posed pos x) gva cxt) t
    let d = _size cxt
        b = vQuote (d + 1) vb
        ni' = Named x i
    pure (T2 (Lam ni' t)
             (GV (GPi ni' gva (GCl (_gVals cxt) (_vVals cxt) b))
                 (VPi ni' va  (VCl (_vVals cxt) b))))

  P.Hole -> do
    m1 <- newMeta cxt
    m2 <- newMeta cxt
    pure (T2 m1 (gvEval' cxt m2))

guardUnsolvedMetas :: IO ()
guardUnsolvedMetas = do
  arr <- UA.last metas
  i   <- subtract 1 <$> UA.size metas
  A.anyIx (\j -> \case MEUnsolved -> reportError (printf "Unsolved meta: ?%d.%d" i j)
                       _ -> False)
          arr
  pure ()

checkTopEntry :: NameTable -> P.TopEntry -> IO NameTable
checkTopEntry ntbl e = do
  UA.push metas =<< A.empty
  let cxt = initCxt ntbl
  x <- A.size top
  case e of
    P.TEPostulate (updPos -> Posed pos n) a -> do
      a <- check cxt a gvU
      guardUnsolvedMetas
      A.push top (TopEntry (Posed pos n) EDPostulate (EntryTy a (gvEval' cxt a)))
      pure (addName n (NITop pos x) ntbl)
    P.TEDefinition (updPos -> Posed pos n) a t -> do
      a <- check cxt a gvU
      let gva = gvEval' cxt a
      t <- check cxt t gva
      guardUnsolvedMetas
      let gvt = gvEval' cxt t
      A.push top (TopEntry (Posed pos n) (EDDefinition t gvt) (EntryTy a gva))
      pure (addName n (NITop pos x) ntbl)

checkProgram :: P.Program -> IO NameTable
checkProgram es = reset >> go mempty es where
  go ntbl = \case
    []   -> pure ntbl
    e:es -> do {ntbl <- checkTopEntry ntbl e; go ntbl es}

--------------------------------------------------------------------------------

-- | Render elaboration output. Just for demo purposes. Serialization proper is TODO,
--   but this should already contain all to-be-serialized information.
renderElabOutput :: IO String
renderElabOutput = do
  es <- A.foldr'  (:) [] top
  ms <- UA.foldr' (:) [] metas

  let go :: (Int, TopEntry) -> A.Array MetaEntry -> IO [String]
      go (i, TopEntry (Posed _ n)  def (EntryTy a _)) ms = do
        ms <- A.foldr' (:) [] ms
        let metaBlock = map
              (\case (j, (MESolved t _)) -> printf "  %d.%d = %s" i j (showTm0 t)
                     _                   -> error "renderElabOutput: impossible")
              (zip [(0 :: Int)..] ms)
            thisDef :: String
            thisDef = case def of
              EDPostulate      -> printf "assume %s : %s" n (showTm0 a)
              EDDefinition t _ -> printf "%s : %s\n = %s" n (showTm0 a) (showTm0 t)
        pure $ if not (null metaBlock) then "mutual":metaBlock ++ [thisDef]
                                       else [thisDef]

  unlines . map unlines <$> zipWithM go (zip [(0::Int)..] es) ms
