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
data NameInfo = NITop SourcePos Ix | NILocal SourcePos NameOrigin Ix

instance Show NameInfo where
  show (NITop _ i)     = "NITop " ++ show i
  show (NILocal _ o i) = printf "NILocal %s %d" (show o) i

-- | Reverse map from names to all de Bruijn levels with the keyed name.
--   Indices are sorted, the lowest in scope is the first element.  We also keep
--   track of source positions of binders. We only use this structure for name
--   lookup during elaboration.
type NameTable = HashMap Name (Env' NameInfo)


data BoundIndices = BINil | BISnoc BoundIndices Ix

-- | Local elaboration context.
data Cxt = Cxt {
  _size       :: Int, -- ^ Number of local entries.
  _gVals      :: GEnv, -- ^ Glued values of definitions.
  _vVals      :: VEnv, -- ^ Local values of definitions.
  _gTypes     :: Env GTy, -- ^ Glued types of entries.
  _vTypes     :: Env VTy, -- ^ Local types of entries.

  -- | Structure for getting indices for names during elaboration.
  _nameTable  :: NameTable,

  -- | Structure for getting names for local indices during unification. Only
  --   used for getting informative (source-originating) names for binders in
  --   meta solutions.
  _nameEnv    :: NameEnv,
  -- | List of local bound indices. Used for making spines for fresh metas.
  _boundIndices :: BoundIndices
  }

addName :: Name -> NameInfo -> NameTable -> NameTable
addName "" _ ntbl = ntbl
addName x ni ntbl = HM.alter (Just . maybe (ESnoc' ENil' ni) (flip ESnoc' ni)) x ntbl
{-# inline addName #-}

-- | Initial local context.
initCxt :: NameTable -> Cxt
initCxt ntbl = Cxt 0 ENil' ENil' ENil ENil ntbl NENil BINil

-- | Add a bound variable to local context.
localBind :: Posed Name -> NameOrigin -> GVTy -> Cxt -> Cxt
localBind x origin (GV gty vty) (Cxt d gs vs gtys vtys ninf ns bis) =
  Cxt (d + 1)
      (ESnoc' gs Nothing)
      (ESnoc' vs Nothing)
      (ESnoc gtys gty)
      (ESnoc vtys vty)
      (addName (proj2 x) (NILocal (proj1 x) origin d) ninf)
      (NESnoc ns (proj2 x))
      (BISnoc bis d)

-- | Add a new definition to local context.
localDefine :: Posed Name -> GV -> GVTy -> Cxt -> Cxt
localDefine x (GV g v) (GV gty vty) (Cxt d gs vs gtys vtys ninf ns bis) =
  Cxt (d + 1)
      (ESnoc' gs (Just g))
      (ESnoc' vs (Just v))
      (ESnoc gtys gty)
      (ESnoc vtys vty)
      (addName (proj2 x) (NILocal (proj1 x) NOSource d) ninf)
      (NESnoc ns (proj2 x))
      bis

localBindSrc, localBindIns :: Posed Name -> GVTy -> Cxt -> Cxt
localBindSrc x = localBind x NOSource
localBindIns x = localBind x NOInserted

--------------------------------------------------------------------------------

lams :: NameEnv -> Renaming -> Tm -> Tm
lams ns = go where
  go RNil            t = t
  go (RCons x y ren) t = go ren (Lam (NI (lookupNameEnv ns x) Expl) t)

registerSolution :: MetaIx -> Tm -> IO ()
registerSolution (MetaIx i j) t = do
  arr <- UA.read metas i
  A.write arr j (MESolved t (gvEval 0 ENil' ENil' t))

vShowTm :: Cxt -> Val -> String
vShowTm cxt v = showTm (_nameEnv cxt) (vQuote (_size cxt) v)

gShowTm :: Cxt -> Glued -> String
gShowTm cxt v = showTm (_nameEnv cxt) (gQuote (_size cxt) v)

showTm' :: Cxt -> Tm -> String
showTm' cxt t = showTm (_nameEnv cxt) t


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
vRename :: (ElabError -> IO ()) -> Ix -> MetaIx -> T2 Int Renaming -> Val -> IO Tm
vRename throwAction = \d occurs (T2 renl ren) ->
  let
    shift = d - renl

    go :: Ix -> Rigidity -> Renaming -> Val -> IO Tm
    go d r ren = \case
      VNe h vsp -> do
        h' <- case h of
              HLocal x -> case lookupRen ren x of
                (-1)   -> do
                            throwAction $ mkError r (printf "Out of scope variable: %d" x)
                            pure Irrelevant
                y      -> pure (LocalVar y)
              HTop   x -> pure (TopVar x)
              HMeta  x | x == occurs -> do
                           throwAction $ mkError r "Occurs check"
                           pure Irrelevant
                       | otherwise   -> pure (MetaVar x)
        goSp d h' ren vsp
      VLam x t    -> Lam x <$> go (d + 1) r (RCons d (d - shift) ren) (vInst t (VLocal d))
      VPi x a b   -> Pi x <$> go d r ren a <*> go (d + 1) r (RCons d (d - shift) ren) (vInst b (VLocal d))
      VU          -> pure U
      VIrrelevant -> pure Irrelevant

    goSp :: Ix -> Tm -> Renaming -> VSpine -> IO Tm
    goSp d t ren (SApp vsp v i) = App <$> goSp d t ren vsp <*> go d Flex ren v <*> pure i
    goSp d t ren SNil           = pure t

  in go d Rigid ren
{-# inline vRename #-}

vRenameShortCut :: Ix -> MetaIx -> T2 Int Renaming -> Val -> IO Tm
vRenameShortCut = vRename throw
{-# inline vRenameShortCut #-}

vRenameRefError :: IORef (Maybe ElabError) -> Ix -> MetaIx -> T2 Int Renaming -> Val -> IO Tm
vRenameRefError ref = vRename (writeIORef ref . Just)
{-# inline vRenameRefError #-}


-- | Try to unify local values. May succeed with () or throw Rigidity. A rigid
--   error is unrecoverable and will be reported, a flex error can be rectified
--   if full unification succeeds later. TODO: annotate rigid errors with
--   information.
unfoldLimit :: Int
unfoldLimit = 2
{-# inline unfoldLimit #-}

vUnify :: Cxt -> Val -> Val -> IO ()
vUnify cxt v v' = go (_size cxt) unfoldLimit (_nameEnv cxt) Rigid v v' where

  go :: Ix -> Int -> NameEnv -> Rigidity -> Val -> Val -> IO ()
  go d u ns r v v' = case (v, v') of
    -- irrelevance
    (VIrrelevant, _) -> pure ()
    (_, VIrrelevant) -> pure ()

    -- solve with same heads
    (VU, VU) -> pure ()

    (VLam (NI n i) t, VLam _ t') -> let d' = VLocal d in
      go (d + 1) u (NESnoc ns n) r (vInst t d') (vInst t' d')
    (VLam (NI n i) t, t'       ) -> let d' = VLocal d in
      go (d + 1) u (NESnoc ns n) r (vInst t d') (vApp t' d' i)
    (t       , VLam (NI n' i') t') -> let d' = VLocal d in
      go (d + 1) u (NESnoc ns n') r (vApp t d' i') (vInst t' d')

    (VPi (NI n i) a b, VPi (NI _ i') a' b') | i == i' -> do
      go d u ns r a a'
      let d' = VLocal d
      go (d + 1) u (NESnoc ns n) r (vInst b d') (vInst b' d')

    (VNe (HTop x) vsp, VNe (HTop x') vsp') | x == x' ->
      goSp d u ns (r `meld` topRigidity x `meld` topRigidity x') vsp vsp'

    (VNe (HLocal x) vsp, VNe (HLocal x') vsp') | x == x' ->
      goSp d u ns r vsp vsp'

    (VNe (HMeta x) vsp, VNe (HMeta x') vsp') | x == x' ->
      goSp d u ns (r `meld` metaRigidity x `meld` metaRigidity x') vsp vsp'

    -- meta sides
    (v@(VNe (HMeta x) vsp), v')
      | MESolved _ (GV _ v) <- lookupMeta x ->
        if u > 0 then go d (u - 1) ns r (vAppSpine v vsp) v'
                 else cantUnify d ns Flex v v'
      | MEUnsolved <- lookupMeta x, Rigid <- r ->
        solve d ns x vsp v'

    (v, v'@(VNe (HMeta x') vsp'))
      | MESolved _ (GV _ v') <- lookupMeta x' ->
        if u > 0 then go d (u - 1) ns r v (vAppSpine v' vsp')
                 else cantUnify d ns Flex v v'
      | MEUnsolved <- lookupMeta x', Rigid <- r ->
        solve d ns  x' vsp' v

    -- top sides
    (v@(VNe (HTop x) vsp), v')
      | EDDefinition _ (GV _ v) <- _entryDef (lookupTop x) ->
        if u > 0 then go d (u - 1) ns r (vAppSpine v vsp) v'
                 else cantUnify d ns Flex v v'

    (v, v'@(VNe (HTop x') vsp'))
      | EDDefinition _ (GV _ v') <- _entryDef (lookupTop x') ->
        if u > 0 then go d (u - 1) ns r v (vAppSpine v' vsp')
                 else cantUnify d ns Flex v v'

    (v, v') -> cantUnify d ns r v v'

  cantUnify d ns r v v' =
    throw $ mkError r $
      printf "Can't (locally) unify\n\n%s\n\nwith\n\n%s"
        (showTm ns (vQuote d v)) (showTm ns (vQuote d v'))

  checkSpine :: VSpine -> T2 Int Renaming
  checkSpine = go where
    go (SApp vsp v i) = case v of
      VLocal x -> case go vsp of
        T2 d ren -> T2 (d + 1) (RCons x d ren)
      _          -> throw $ mkError Flex "non-variable in meta spine"
    go SNil = T2 0 RNil

  solve :: Ix -> NameEnv -> MetaIx -> VSpine -> Val -> IO ()
  solve d ns x vsp ~v = do
    let ren = checkSpine vsp
    rhs <- lams ns (proj2 ren) <$> vRenameShortCut d x ren v
    registerSolution x rhs

  goSp :: Ix -> Int -> NameEnv -> Rigidity -> VSpine -> VSpine -> IO ()
  goSp d u ns r (SApp vsp v _) (SApp vsp' v' _) = goSp d u ns r vsp vsp' >> go d u ns r v v'
  goSp d u ns r SNil            SNil            = pure ()
  goSp _ _ _  r _               _               = error "vUnify.goSp: impossible"


gvRename :: Ix -> MetaIx -> T2 Int Renaming -> GV -> IO Tm
gvRename d occurs (T2 renl ren) (GV g v) = do
  err <- newIORef Nothing
  rhs <- vRenameRefError err d occurs (T2 renl ren) v
  let shift = d - renl
  readIORef err >>= \case
    Nothing            -> pure rhs
    Just (EERigid msg) -> error msg
    Just (EEFlex msg)  -> go d ren g >> pure rhs where

      go :: Ix -> Renaming -> Glued -> IO ()
      go d ren g = case gForce g of
        GNe h gsp _ -> do
          case h of
            HLocal x -> case lookupRen ren x of
              (-1)   -> reportError "ill-scoped solution candidate"
              _      -> pure ()
            HTop{} -> pure ()
            HMeta x | x == occurs -> reportError "occurs check"
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
  catch (do
    -- let t1 = vShowTm cxt v
    --     t2 = vShowTm cxt v'
    vUnify cxt v v' -- <* traceM (printf "locally unified: %s   %s" t1 t2)
    )
  $ \case
    EERigid msg -> error msg
    EEFlex  msg -> do
      -- traceM (printf "failed local unify: %s   %s" (vShowTm cxt v) (vShowTm cxt v'))
      -- traceM (printf "trying global unify: %s   %s" (gShowTm cxt g) (gShowTm cxt g'))
      go (_size cxt) (_nameEnv cxt) gv gv'
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

      (GPi (NI n i) a b, GPi (NI _ i') a' b') | i == i' -> do
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

      (g, g') ->
        reportError $
          printf "Can't (globally) unify\n\n%s\n\nwith\n\n%s"
            (showTm ns (gQuote d g)) (showTm ns (gQuote d g'))

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

-- Elaboration
------------------------------------------------------------------------------------------

data MetaInsertion = MIYes | MINo | MIUntilName Name

gvEval' :: Cxt -> Tm -> GV
gvEval' cxt t = gvEval (_size cxt) (_gVals cxt) (_vVals cxt) t
{-# inline gvEval' #-}

gEval' :: Cxt -> Tm -> Glued
gEval' cxt t = gEval (_size cxt) (_gVals cxt) (_vVals cxt) t
{-# inline gEval' #-}

newMeta :: Cxt -> IO Tm
newMeta (_boundIndices -> bis) = do
  i     <- subtract 1 <$> UA.size metas
  arr   <- UA.read metas i
  j     <- A.size arr
  A.push arr MEUnsolved
  let go BINil          = MetaVar (MetaIx i j)
      go (BISnoc bis x) = App (go bis) (LocalVar x) Expl
  pure (go bis)

check :: Cxt -> P.Tm -> GVTy -> IO Tm
check cxt (updPos -> T2 pos t) (GV gwant vwant) = case (t, gForce gwant) of
  (P.Lam x ni t, GPi (NI x' i') a b) | (case ni of Inl y -> y == x'; Inr i -> i == i') ->
    Lam (NI x i') <$> check (localBindSrc (T2 pos x) a cxt) t (gvInst b (gvLocal (_size cxt)))
  (t, GPi (NI x Impl) a b) ->
    Lam (NI x Impl) <$> check (localBindIns (T2 pos x) a cxt)
                              (T2 pos t) (gvInst b (gvLocal (_size cxt)))
  (P.Let x a t u, gwant) -> do
    a <- check cxt a gvU
    let gva = gvEval' cxt a
    t <- check cxt t gva
    let gvt = gvEval' cxt t
    u <- check (localDefine (T2 pos x) gvt gva cxt) u (GV gwant vwant)
    pure (Let x a t u)
  (P.Hole, _) ->
    newMeta cxt
  (t, gwant) -> do
    T2 t gvhas <- infer MIYes cxt (T2 pos t)
    gvUnify cxt gvhas (GV gwant vwant)
    pure t

insertMetas :: MetaInsertion -> Cxt -> IO (T2 Tm GVTy) -> IO (T2 Tm GVTy)
insertMetas ins cxt inp = case ins of
  MINo  -> inp
  MIYes -> do
    T2 t (GV ga va) <- inp
    let go t (GV (GPi (NI x Impl) a b) va) = do
          m <- newMeta cxt
          go (App t m Impl) (gvInst b (gvEval' cxt m))
        go t gva = pure (T2 t gva)
    go t (GV (gForce ga) va)
  MIUntilName x -> do
    T2 t (GV ga va) <- inp
    let go t gva@(GV (GPi (NI x' Impl) a b) va)
          | x  == x'  = pure (T2 t gva)
          | otherwise = do
              m <- newMeta cxt
              go (App t m Impl) (gvInst b (gvEval' cxt m))
        go t a = reportError ("No named implicit argument with name " ++ show x)
    go t (GV (gForce ga) va)
{-# inline insertMetas #-}

inferVar :: Cxt -> Name -> IO (T2 Tm GVTy)
inferVar cxt n = do
  case HM.lookup n (_nameTable cxt) of
    Nothing -> reportError (printf "Name not in scope: %s" n)
    Just es -> go es where
      go ENil'                              = reportError (printf "Name not in scope: %s" n)
      go (ESnoc' es (NITop pos x))          = do
        EntryTy _ gvty <- _entryTy <$> A.read top x
        pure (T2 (TopVar x) gvty)
      go (ESnoc' es (NILocal pos origin x)) = case origin of
        NOInserted -> go es
        NOSource   -> do
          let Box ga = lookupEnv (_size cxt) (_gTypes cxt) x
              Box va = lookupEnv (_size cxt) (_vTypes cxt) x
          pure (T2 (LocalVar x) (GV ga va))
{-# inline inferVar #-}

infer :: MetaInsertion -> Cxt -> P.Tm -> IO (T2 Tm GVTy)
infer ins cxt (updPos -> T2 pos t) = case t of
  P.U -> pure (T2 U gvU)

  P.StopMetaIns t -> infer MINo cxt t

  P.Var x -> insertMetas ins cxt (inferVar cxt x)

  P.App t u ni -> insertMetas ins cxt $ do
    T2 t (GV ga va) <- infer
      (case ni of Inl x    -> MIUntilName x
                  Inr Impl -> MINo
                  Inr Expl -> MIYes)
      cxt t
    case gForce ga of
      GPi (NI x i') a b -> do
        forM_ ni $ \i ->
          unless (i == i') $ reportError "implicitness mismatch"
        u <- check cxt u a
        pure (T2 (App t u i') (gvInst b (gvEval' cxt u)))
      _ -> reportError $
        printf "Expected a function type for expression:\n\n%s\n\nInferred type:\n\n%s"
           (showTm' cxt t) (gShowTm cxt ga)

  P.Pi (NI x i) a b -> do
    a <- check cxt a gvU
    b <- check (localBindSrc (T2 pos x) (gvEval' cxt a) cxt) b gvU
    pure (T2 (Pi (NI x i) a b) gvU)

  P.Let x a t u -> do
    a <- check cxt a gvU
    let gva = gvEval' cxt a
    t <- check cxt t gva
    let gvt = gvEval' cxt t
    T2 u gvb <- infer ins (localDefine (T2 pos x) gvt gva cxt) u
    pure (T2 (Let x a t u) gvb)

  P.Lam x ni t -> insertMetas ins cxt $ do
    i <- case ni of
      Inl x -> reportError "Can't infer type for lambda with named arguments"
      Inr i -> pure i
    gva@(GV ga va) <- gvEval' cxt <$> newMeta cxt
    T2 t gvb@(GV gb vb) <- infer MIYes (localBindSrc (T2 pos x) gva cxt) t
    let d = _size cxt
        b = vQuote (d + 1) vb
        ni' = NI x i
    pure (T2 (Lam ni' t)
             (GV (GPi ni' gva (GCl d (_gVals cxt) (_vVals cxt) b))
                 (VPi ni' va  (VCl d (_vVals cxt) b))))

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
    P.TEPostulate (updPos -> T2 pos n) a -> do
      a <- check cxt a gvU
      guardUnsolvedMetas
      A.push top (TopEntry (T2 pos n) EDPostulate (EntryTy a (gvEval' cxt a)))
      pure (addName n (NITop pos x) ntbl)
    P.TEDefinition (updPos -> T2 pos n) a t -> do
      a <- check cxt a gvU
      let gva = gvEval' cxt a
      t <- check cxt t gva
      guardUnsolvedMetas
      let gvt = gvEval' cxt t
      A.push top (TopEntry (T2 pos n) (EDDefinition t gvt) (EntryTy a gva))
      pure (addName n (NITop pos x) ntbl)

checkProgram :: P.Program -> IO NameTable
checkProgram es = reset >> go mempty es where
  go ntbl = \case
    []   -> pure ntbl
    e:es -> do {ntbl <- checkTopEntry ntbl e; go ntbl es}

--------------------------------------------------------------------------------

-- | Render elaboration output. Just for demo purposes. Serialization proper is TODO,
--   but this should already contain all to-be-seriaized information.
renderElabOutput :: IO String
renderElabOutput = do
  es <- A.foldr'  (:) [] top
  ms <- UA.foldr' (:) [] metas

  let go :: (Int, TopEntry) -> A.Array MetaEntry -> IO [String]
      go (i, TopEntry (T2 _ n)  def (EntryTy a _)) ms = do
        ms <- A.foldr' (:) [] ms
        let metaBlock = map
              (\case (j, (MESolved t _)) -> printf "%d.%d = %s" i j (showTm0 t)
                     _                   -> error "renderElabOutput: impossible")
              (zip [(0 :: Int)..] ms)
            thisDef :: String
            thisDef = case def of
              EDPostulate      -> printf "assume %s : %s" n (showTm0 a)
              EDDefinition t _ -> printf "%s : %s\n = %s" n (showTm0 a) (showTm0 t)
        pure $ metaBlock ++ [thisDef]

  unlines . map unlines <$> zipWithM go (zip [(0::Int)..] es) ms
