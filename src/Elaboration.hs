
module Elaboration where

import qualified Data.HashMap.Strict as HM
import qualified Data.Array.Dynamic as A
import qualified Data.Array.Dynamic.Unlifted as UA

import Control.Exception
import Control.Monad.State.Strict
import Data.IORef
import Text.Printf
import qualified GHC.Exts as Exts

import Common
import Cxt
import ElabState
import Errors
import Evaluation
import Pretty
import Simplify
import Syntax
import Values
import qualified LvlSet as LS
import qualified Presyntax as P


-- Unification
--------------------------------------------------------------------------------

{-
Currently, we don't track meta types, hence don't do pruning on metas at all.
Two basic operations: unification, meta solution quotation

Unification:
  1. Check local conversion; track rigidity of conversion context, solve
     metas in rigid context but throw error when encountering metas
     in flex context.

  2. If local unification throws flex error, do full glued unification.

Meta solution quotation:
  1. Quote solution candidate:
     - 1.1: attempt eta contraction of pattern, based on glued spines whenever available
            but local rhs. Only contract if rhs is locally neutral, abort
            contraction attempt at non-linear variables.
     - 1.2: check glued spine validity, throw rigid error on failure
     - 1.3: quote scope-checked solution candidate; may throw flex or
            rigid error.
  2. If 1. returns without error, solve.
     If 1. returns with rigid error, rethrow.
     If 1. returns with flex error, the solution candidate can be
        a) eta-convertible to lhs: return without solving
        b) ill-scoped: throw error
        c) fine: solve meta

-}


--------------------------------------------------------------------------------

registerSolution :: Meta -> Tm -> IO ()
registerSolution (Meta i j) t = do
  arr <- UA.read metas i
  pos <- getPos
  A.write arr j
    (MESolved (gvEval 0 ENil ENil t) (isInlinable t) t (MSSource pos))
{-# inline registerSolution #-}

disjointLvls :: LS.LvlSet -> Renaming -> Bool
disjointLvls xs RNil            = True
disjointLvls xs (RCons x _ ren) = not (LS.member x xs) && disjointLvls xs ren

-- | We only eta-contract if lhs spine exactly matches rhs spine.
contract :: (Lvl, Renaming, VSpine) -> Val -> ((Lvl, Renaming, VSpine), Val)
contract topRen topV@(VNe h vsp') = go (mempty @LS.LvlSet) topRen vsp' where
  go xs (!l, ren, vsp) SNil
    | disjointLvls xs ren = ((l, ren, vsp), VNe h SNil)
  go xs (!l, RCons x _ ren, SAppI vsp _) (SAppI vsp' (vForce -> VLocal x'))
    | x == x', not (LS.member x xs) = go (LS.insert x xs) (l - 1, ren, vsp) vsp'
  go xs (!l, RCons x _ ren, SAppE vsp _) (SAppE vsp' (vForce -> VLocal x'))
    | x == x', not (LS.member x xs) = go (LS.insert x xs) (l - 1, ren, vsp) vsp'
  go _ _ _ = (topRen, topV)
contract ren v = (ren, v)

lams :: Lvl -> Names -> Renaming -> VSpine -> Tm -> Tm
lams l ns = go where
  go RNil            _ t = t
  go (RCons x y ren) (SAppI vsp _) t =
    go ren vsp (Lam (Named (lookupName (l - x - 1) ns) Impl) t)
  go (RCons x y ren) (SAppE vsp _) t =
    go ren vsp (Lam (Named (lookupName (l - x - 1) ns) Expl) t)
  go _ _ _ = error "lams: impossible"

--  Generating meta solutions
--------------------------------------------------------------------------------

-- | Throws (FlexRigid LocalError).
--   Always throws flex because in a rigid case the glued check immediately throws
--   afterwards anyway, and error messages aren't worse in glued mode.
vQuoteSolution ::
  (FlexRigid LocalError -> IO ()) -> Lvl -> Names -> Meta -> (Lvl, Renaming, VSpine) -> Val -> IO Tm
vQuoteSolution throwAction = \l ns occurs (renl, ren, vsp) v ->
  let
    scopeCheck :: Lvl -> (Lvl, Renaming) -> Val -> IO Tm
    scopeCheck l (renl, ren) v = go l ren v  where
      shift = l - renl
      go :: Lvl -> Renaming -> Val -> IO Tm
      go l ren v = case vForce v of
        VNe h vsp -> case h of

          HLocal x -> case applyRen ren x of
            (-1)   -> Irrelevant <$ throwAction (FRFlex @LocalError)
            y      -> goSp l ren (LocalVar (l - shift - y - 1)) vsp

          HTopRigid (Int2 x _)         -> goSp l ren (TopVar x) vsp
          HTopBlockedOnMeta (Int2 x _) -> goSp l ren (TopVar x) vsp
          HTopUnderapplied (Int2 x _)  -> goSp l ren (TopVar x) vsp

          HMeta  x | x == occurs -> Irrelevant <$ throwAction (FRFlex @LocalError)
                   | otherwise   -> lookupMetaIO x >>= \case
                       MEUnsolved{} -> goSp l ren (MetaVar x) vsp
                       MESolved{}   -> do
                         when (metaTopLvl x == metaTopLvl occurs) $
                           throwAction (FRFlex @LocalError)
                         goSp l ren (MetaVar x) vsp

        VLam x t    -> Lam x <$> go (l + 1) (RCons l (l - shift) ren) (vInst t (VLocal l))
        VPi x a b   -> Pi x <$> go l ren a
                            <*> go (l + 1) (RCons l (l - shift) ren) (vInst b (VLocal l))
        VFun a b    -> Fun <$> go l ren a <*> go l ren b
        VU          -> pure U
        VIrrelevant -> pure Irrelevant

      goSp :: Lvl -> Renaming -> Tm -> VSpine -> IO Tm
      goSp l ren t (SAppI vsp v) = AppI <$> goSp l ren t vsp <*> go l ren v
      goSp l ren t (SAppE vsp v) = AppE <$> goSp l ren t vsp <*> go l ren v
      goSp l ren t SNil          = pure t

  in
    lams l ns ren vsp <$> scopeCheck l (renl, ren) v
{-# inline vQuoteSolution #-}

-- | Abort quoting on error.
vQuoteSolutionShortCut :: Lvl -> Names -> Meta -> (Lvl, Renaming, VSpine) -> Val -> IO Tm
vQuoteSolutionShortCut = vQuoteSolution throw
{-# inline vQuoteSolutionShortCut #-}

-- | On error, write error to IORef then continue quoting.
vQuoteSolutionRefError ::
     IORef (Maybe (FlexRigid LocalError))
  -> Lvl -> Names -> Meta -> (Lvl, Renaming, VSpine) -> Val -> IO Tm
vQuoteSolutionRefError ref = vQuoteSolution (\e -> writeIORef ref (Just e))
{-# inline vQuoteSolutionRefError #-}

type Unfolding = Int

-- | Try to unify local values. May succeed with () or throw ElabError. A rigid
--   error is unrecoverable and will be reported, a flex error can be rectified
--   if full unification succeeds later.
unfoldLimit :: Unfolding
unfoldLimit = 2
{-# inline unfoldLimit #-}

-- | Throws (FlexRigid LocalError).
vUnify :: Cxt -> Val -> Val -> IO ()
vUnify cxt v v' = go (_size cxt) unfoldLimit (_names cxt) Rigid v v' where

  go :: Lvl -> Unfolding -> Names -> Rigidity -> Val -> Val -> IO ()
  go l u ns r v v' = case (vForce v, vForce v') of

    (VIrrelevant, _) -> pure ()
    (_, VIrrelevant) -> pure ()

    -- same heads
    (VU, VU) -> pure ()

    (VLam (Named n i) t, VLam _ t') -> let var = VLocal l in
      go (l + 1) u (NSnoc ns n) r (vInst t var) (vInst t' var)
    (VLam (Named n i) t, t'       ) -> let var = VLocal l in
      go (l + 1) u (NSnoc ns n) r (vInst t var) (vApp i t' var)
    (t     , VLam (Named n' i') t') -> let var = VLocal l in
      go (l + 1) u (NSnoc ns n') r (vApp i' t var) (vInst t' var)

    (VPi (Named n i) a b, VPi (Named _ i') a' b') | i == i' -> do
      go l u ns r a a'
      let var = VLocal l
      go (l + 1) u (NSnoc ns n) r (vInst b var) (vInst b' var)

    (VPi (Named n i) a b, VFun a' b') -> do
      go l u ns r a a'
      go (l + 1) u (NSnoc ns n) r (vInst b (VLocal l)) b'

    (VFun a b, VPi (Named n' i') a' b') -> do
      go l u ns r a a'
      go (l + 1) u (NSnoc ns n') r b (vInst b' (VLocal l))

    (VFun a b, VFun a' b') -> go l u ns r a a' >> go l u ns r b b'

    (VNe h vsp, VNe h' vsp') | h == h' -> do
      -- printf "local neutral: %s   %s\n" (showValMetaless mempty ns (VNe h vsp))
      --                                   (showValMetaless mempty ns (VNe h' vsp'))
      -- printf "rigidity: %s, next rigidity: %s\n" (show r) (show (r `meld` headRigidity h))
      goSp l u ns (r `meld` headRigidity h) vsp vsp'

    -- meta sides
    (v@(VNe (HMeta x) vsp), v')
      | MESolved (GV _ v) _ _ _ <- lookupMeta x
       , u > 0 -> go l (u - 1) ns r (vAppSpine v vsp) v'
      | MEUnsolved _ <- lookupMeta x, Rigid <- r ->
        solve l ns x vsp v'

    (v, v'@(VNe (HMeta x') vsp'))
      | MESolved (GV _ v') _ _ _ <- lookupMeta x'
        , u > 0 -> go l (u - 1) ns r v (vAppSpine v' vsp')
      | MEUnsolved _ <- lookupMeta x', Rigid <- r ->
        solve l ns  x' vsp' v

    -- top definition sides
    (v@(VNe (HTopRigid (Int2 x _)) vsp), v')
      | TEDefinition (GV _ v) _ _ _ _ <- lookupTop x
        , u > 0 -> go l (u - 1) ns r (vAppSpine v vsp) v'

    (v, v'@(VNe (HTopRigid (Int2 x' _)) vsp'))
      | TEDefinition (GV _ v') _ _ _ _ <- lookupTop x'
        , u > 0 -> go l (u - 1) ns r v (vAppSpine v' vsp')

    (v@(VNe h vsp), v'@(VNe h' vsp')) ->
      cantUnify l ns (r `meld` headRigidity h `meld` headRigidity h') v v'
    (v@(VNe h vsp), v') ->
      cantUnify l ns (r `meld` headRigidity h) v v'
    (v, v'@(VNe h' vsp')) ->
      cantUnify l ns (r `meld` headRigidity h') v v'

    (v, v') ->
      cantUnify l ns r v v'

  cantUnify l ns r v v' = throw (makeFR r (LocalError ns (UELocalUnify v v')))
  {-# inline cantUnify #-}

  solve :: Lvl -> Names -> Meta -> VSpine -> Val -> IO ()
  solve l ns x vsp v = do
    let checkVSp :: VSpine -> (Lvl, Renaming)
        checkVSp = go where
          go SNil = (0, RNil)
          go (SAppI vsp v) =
              let h = case vForce v of
                        VLocal x -> x
                        _ -> throw (FRFlex @LocalError)
                  (l, ren) = go vsp
              in (l + 1, RCons h l ren)
          go (SAppE vsp v) =
              let h = case vForce v of
                        VLocal x -> x
                        _ -> throw (FRFlex @LocalError)
                  (l, ren) = go vsp
              in (l + 1, RCons h l ren)
    let (renl, ren) = checkVSp vsp
    case contract (renl, ren, vsp) v of
      (ren, v) -> do
        rhs <- vQuoteSolutionShortCut l ns x ren v
        registerSolution x rhs

  goSp :: Lvl -> Unfolding -> Names -> Rigidity -> VSpine -> VSpine -> IO ()
  goSp l u ns r (SAppI vsp v) (SAppI vsp' v') = goSp l u ns r vsp vsp' >> go l u ns r v v'
  goSp l u ns r (SAppE vsp v) (SAppE vsp' v') = goSp l u ns r vsp vsp' >> go l u ns r v v'
  goSp l u ns r SNil          SNil            = pure ()
  goSp _ _ _  r _             _               = error "vUnify.goSp: impossible"


-- | Throws SolutionError, returns True if rhs is eta-convertible to lhs.
gCheckSolution :: Lvl -> Meta -> (Lvl, Renaming) -> Glued -> IO Bool
gCheckSolution topLvl occurs (renl, ren) g = contr topLvl ren g where

  shift :: Int
  shift = topLvl - renl

  contr :: Lvl -> Renaming -> Glued -> IO Bool
  contr l ren g = case gForce l g of
    GLam _ t -> contr (l + 1) (RCons l (l - shift) ren) (gInst l t (gvLocal l))
    GNe (HMeta x) gsp _ | occurs == x, strip l gsp -> pure True where
       strip l SNil                   = l == topLvl
       strip l (SAppI gs (GLocal l')) = (l' == l - 1) && strip (l - 1) gs
       strip l (SAppE gs (GLocal l')) = (l' == l - 1) && strip (l - 1) gs
       strip _ _                      = False
    g -> False <$ scopeCheck l ren g

  scopeCheck :: Lvl -> Renaming -> Glued -> IO ()
  scopeCheck = go where
    go l ren g = case gForce l g of
      GNe h gsp _ -> do
        case h of
          HLocal x -> case applyRen ren x of
            (-1)   -> throw (SEScope x)
            _      -> pure ()
          HTopRigid{}         -> pure ()
          HTopBlockedOnMeta{} -> pure ()
          HTopUnderapplied{}  -> pure ()
          HMeta x | x == occurs -> throw SEOccurs
                  | otherwise   -> pure ()
        goSp l ren gsp
      GLam x t               -> go (l + 1) (RCons l (l - shift) ren) (gInst l t (gvLocal l))
      GPi x (GV a _) b       -> go l ren a
                                >> go (l + 1) (RCons l (l - shift) ren) (gInst l b (gvLocal l))
      GFun (GV a _) (GV b _) -> go l ren a >> go l ren b
      GU                     -> pure ()
      GIrrelevant            -> pure ()

    goSp :: Lvl -> Renaming -> GSpine -> IO ()
    goSp l ren SNil          = pure ()
    goSp l ren (SAppI gsp g) = goSp l ren gsp >> go l ren g
    goSp l ren (SAppE gsp g) = goSp l ren gsp >> go l ren g


-- | Throws LocalError.
gvUnify :: Cxt -> GV -> GV -> IO ()
gvUnify cxt gv@(GV g v) gv'@(GV g' v') =
  vUnify cxt v v'
  `catch`
  \case
    FRRigid e -> throw (e :: LocalError)
    FRFlex    -> go (_size cxt) (_names cxt) gv gv'
  where
    go :: Lvl -> Names -> GV -> GV -> IO ()
    go l ns (GV g v) (GV g' v') = case (gForce l g, gForce l g') of

      (GU, GU) -> pure ()

      (g@(GNe (HMeta x) gsp vsp), g'@(GNe (HMeta x')  gsp' vsp')) -> case compare x x' of
        LT -> solve l ns x' vsp' gsp' (GV g v)
        GT -> solve l ns x vsp gsp (GV g' v')
        EQ -> goSp l ns gsp gsp' vsp vsp'

      (GNe (HMeta x) gsp vsp, g') -> solve l ns x vsp gsp (GV g' v')
      (g, GNe (HMeta x') gsp' vsp') -> solve l ns x' vsp' gsp' (GV g v)

      (GLam (Named n i) t, GLam _ t') -> let var = gvLocal l in
        go (l + 1) (NSnoc ns n) (gvInst l t var) (gvInst l t' var)

      (GLam (Named n i) t, t'       ) -> let var = gvLocal l in
        go (l + 1) (NSnoc ns n) (gvInst l t var) (gvApp i l t' var)

      (t     , GLam (Named n' i') t') -> let var = gvLocal l in
        go (l + 1) (NSnoc ns n') (gvApp i' l t var) (gvInst l t' var)

      (g@(GNe h gsp vsp), g'@(GNe h' gsp' vsp'))
        | h == h' -> goSp l ns gsp gsp' vsp vsp'
        -- | otherwise -> do
        --     printf "head fail? %s %s\n" (show h) (show h')
        --     throw (LocalError ns (UEGluedUnify (GV g v) (GV g' v')))

      (GPi (Named n i) a b, GPi (Named _ i') a' b') | i == i' -> do
        let var = gvLocal l
        go l ns a a'
        go (l + 1) (NSnoc ns n) (gvInst l b var) (gvInst l b' var)

      (GPi (Named n i) a b, GFun a' b') -> do
        go l ns a a'
        go (l + 1) (NSnoc ns n) (gvInst l b (gvLocal l)) b'

      (GFun a b, GPi (Named n' i') a' b') -> do
        go l ns a a'
        go (l + 1) (NSnoc ns n') b (gvInst l b' (gvLocal l))

      (GFun a b, GFun a' b') -> go l ns a a' >> go l ns b b'

      (g, g') -> throw (LocalError ns (UEGluedUnify (GV g v) (GV g' v')))

    goSp :: Lvl -> Names -> GSpine -> GSpine -> VSpine -> VSpine -> IO ()
    goSp l ns (SAppI gsp g) (SAppI gsp' g')
              (SAppI vsp v) (SAppI vsp' v') = goSp l ns gsp gsp' vsp vsp'
                                              >> go l ns (GV g v) (GV g' v')
    goSp l ns (SAppE gsp g) (SAppE gsp' g')
              (SAppE vsp v) (SAppE vsp' v') = goSp l ns gsp gsp' vsp vsp'
                                              >> go l ns (GV g v) (GV g' v')
    goSp d ns SNil SNil SNil SNil = pure ()
    goSp _ _  _    _    _    _    = error "gvUnify.goSp: impossible"


    solve :: Lvl -> Names -> Meta -> VSpine -> GSpine -> GV -> IO ()
    solve l ns x vspTop gspTop gvTop@(GV g v) = do

      let checkGSp :: GSpine -> (Lvl, Renaming)
          checkGSp = go where
            go SNil = (0, RNil)
            go (SAppI gsp g) =
              let h = case gForce l g of
                        GLocal x -> x
                        _ -> throw (LocalError ns (UEGluedSpine x vspTop gspTop gvTop g))
                  (l, ren) = go gsp
              in (l + 1, RCons h l ren)
            go (SAppE gsp g) =
              let h = case gForce l g of
                        GLocal x -> x
                        _ -> throw (LocalError ns (UEGluedSpine x vspTop gspTop gvTop g))
                  (l, ren) = go gsp
              in (l + 1, RCons h l ren)
          (renl, ren) = checkGSp gspTop
          (ren', v') = contract (renl, ren, vspTop) v

      err <- newIORef Nothing
      rhs <- vQuoteSolutionRefError err l ns x ren' v'
      readIORef err >>= \case
        Nothing          -> registerSolution x rhs
        Just (FRRigid e) -> throw e
        Just FRFlex      -> do
          chk <- gCheckSolution l x (renl, ren) g
                 `catch`
                 (\e -> throw (LocalError ns (UEGluedSolution x vspTop gspTop gvTop e)))
          if chk then pure () else registerSolution x rhs

-- Elaboration
------------------------------------------------------------------------------------------

data MetaInsertion = MIYes | MINo | MIUntilName Name

gvEvalCxt :: Cxt -> Tm -> GV
gvEvalCxt Cxt{..} t = gvEval _size _gEnv _vEnv t
{-# inline gvEvalCxt #-}

gEvalCxt :: Cxt -> Tm -> Glued
gEvalCxt Cxt{..} t = gEval _size _gEnv _vEnv t
{-# inline gEvalCxt #-}

newMeta :: Cxt -> IO Tm
newMeta cxt@Cxt{..} = do
  i   <- subtract 1 <$> UA.size metas
  arr <- UA.read metas i
  j   <- A.size arr
  pos <- getPos
  A.push arr (MEUnsolved pos)
  let go BINil           = MetaVar (Meta i j)
      go (BILocal bis x) = AppE (go bis) (LocalVar (_size - x - 1))
  pure (go _boundIndices)

-- | Throws TopError.
check :: Cxt -> P.Tm -> GVTy -> IO Tm
check cxt@Cxt{..} (Posed pos t) (GV gwant vwant) = updPos pos >> case (t, gForce _size gwant) of
  (P.Lam x ni t, GPi (Named x' i') a b) | (case ni of NOName y -> y == x'
                                                      NOImpl   -> i' == Impl
                                                      NOExpl   -> i' == Expl) ->
    Lam (Named x i') <$> check (bindVar (Posed pos x) a cxt) t (gvInst _size b (gvLocal _size))

  (P.Lam x NOExpl t, GFun a b) ->
    Lam (Named x Expl) <$> check (bindVar (Posed pos x) a cxt) t b

  -- Special case for for checking implicit pi type for a variable
  (P.Var n, gwant@(GPi (Named x Impl) a b))
    | (t, gvty@(GV gty vty)) <- runIO (inferVar cxt n)
    , gty@(GNe (HMeta x) _ _) <- gForce _size gty -> do
        gvUnify cxt (GV gty vty) (GV gwant vwant)
          `catch`
          \e -> do
            updPos pos
            throw (TopError cxt (EECheck t (GV gwant vwant) (GV gty vty) e))
        pure t

  (t, GPi (Named x Impl) a b) ->
    Lam (Named x Impl) <$> check (localInsert (Posed pos x) a cxt)
                                 (Posed pos t) (gvInst _size b (gvLocal _size))

  (P.Let x a t u, gwant) -> do
    a <- check cxt a gvU
    let gva = gvEvalCxt cxt a
    t <- check cxt t gva
    let gvt = gvEvalCxt cxt t
    u <- check (localDefine (Posed pos x) gvt gva cxt) u (GV gwant vwant)
    pure (Let (Named x a) t u)

  (P.Hole, _) ->
    newMeta cxt

  (t, gwant) -> do
    (t, gvhas) <- infer MIYes cxt (Posed pos t)
    gvUnify cxt gvhas (GV gwant vwant)
      `catch`
      \e -> do
        updPos pos
        throw (TopError cxt (EECheck t (GV gwant vwant) gvhas e))
    pure t

insertMetas :: MetaInsertion -> Cxt -> IO (Tm, GVTy) -> IO (Tm, GVTy)
insertMetas ins cxt@Cxt{..} inp = case ins of
  MINo  -> inp
  MIYes -> do
    (t, gva) <- inp
    let go t (GV (gForce _size -> GPi (Named x Impl) a b) va) = do
          m <- newMeta cxt
          go (AppI t m) (gvInst _size b (gvEvalCxt cxt m))
        go t gva = pure (t, gva)
    go t gva
  MIUntilName x -> do
    (t, gva) <- inp
    let go t gva@(GV (gForce _size -> GPi (Named x' Impl) a b) va)
          | x  == x'  = pure (t, gva)
          | otherwise = do
              m <- newMeta cxt
              go (AppI t m) (gvInst _size b (gvEvalCxt cxt m))
        go t gva = throw (TopError cxt (EENoNamedArg t gva x))
    go t gva
{-# inline insertMetas #-}

inferVar :: Cxt -> Name -> IO (Tm, GVTy)
inferVar cxt@Cxt{..} n =
  case HM.lookup n _nameTable of
    Nothing -> throw (TopError cxt (EEScope n))
    Just (NTETop x)   -> case lookupTop x of
      TEPostulate _ _ _ _ _ gva -> pure (TopVar x, gva)
      TEDefinition _ _ _ _  gva -> pure (TopVar x, gva)
      TERewriteRule{}           -> error "inferVar: impossible"
    Just (NTELocal x) ->
      let x' = _size - x - 1 in pure (LocalVar x', _types !! x')
{-# inline inferVar #-}

-- throws TopError
infer :: MetaInsertion -> Cxt -> P.Tm -> IO (Tm, GVTy)
infer ins cxt@Cxt{..} (Posed pos t) = updPos pos >> case t of
  P.U -> pure (U, gvU)

  P.Var x -> insertMetas ins cxt (inferVar cxt x)

  P.App t u ni -> insertMetas ins cxt $ do
    let insertion = case ni of
          NOName x -> MIUntilName x
          NOImpl   -> MINo
          NOExpl   -> MIYes
        tpos = posOf t
    (t, GV gaTop vaTop) <- infer insertion cxt t
    case gForce _size gaTop of
      GPi (Named x i') a b -> do
        case ni of
          NOName x -> pure ()
          NOImpl   -> unless (i' == Impl) $ do
                        updPos (posOf u)
                        throw (TopError cxt (EEAppIcit t i' Impl))
          NOExpl   -> unless (i' == Expl) $ do
                        updPos (posOf u)
                        throw (TopError cxt (EEAppIcit t i' Expl))
        u <- check cxt u a
        pure (app i' t u, gvInst _size b (gvEvalCxt cxt u))
      GFun a b -> do
        case ni of NOExpl -> pure ()
                   _      -> updPos (posOf u) >> throw (TopError cxt (EEAppIcit t Expl Impl))
        u <- check cxt u a
        pure (AppE t u, b)
      gaTop@(GNe (HMeta _) _ _) -> do
        (u, gva@(GV ga va)) <- infer MIYes cxt u
        b <- newMeta (bindVar (Posed tpos "x") gva cxt)
        let i   = case ni of NOExpl -> Expl; _ -> Impl
            gPi = GPi (Named "x" i) gva (GCl _gEnv _vEnv b)
            vPi = VPi (Named "x" i) va  (VCl _vEnv b)
        gvUnify cxt (GV gaTop vaTop) (GV gPi vPi)
          `catch`
          \e -> do
            updPos tpos
            throw (TopError cxt (EECheck t (GV gPi vPi) (GV gaTop vaTop) e))
        pure (app i t u, gvInst _size (GCl _gEnv _vEnv b) (gvEvalCxt cxt u))
      ga -> throw (TopError cxt (EEFunctionExpected t (GV gaTop vaTop)))

  P.Pi (Named x i) a b -> do
    a <- check cxt a gvU
    b <- check (bindVar (Posed pos x) (gvEvalCxt cxt a) cxt) b gvU
    pure (Pi (Named x i) a b, gvU)

  P.Fun a b -> do
    a <- check cxt a gvU
    b <- check cxt b gvU
    pure (Fun a b, gvU)

  P.Lam x ni t -> insertMetas ins cxt $ do
    i <- case ni of
      NOName x -> throw (TopError cxt EENamedLambda)
      NOImpl   -> pure Impl
      NOExpl   -> pure Expl
    gva@(GV ga va) <- gvEvalCxt cxt <$> newMeta cxt
    (t, gvb@(GV gb vb)) <- infer MIYes (bindVar (Posed pos x) gva cxt) t
    let b   = vQuote (_size + 1) vb
        ni' = Named x i
    pure (Lam ni' t,
          GV (GPi ni' gva (GCl _gEnv _vEnv b))
             (VPi ni' va  (VCl _vEnv b)))

  P.Let x a t u -> do
    a <- check cxt a gvU
    let gva = gvEvalCxt cxt a
    t <- check cxt t gva
    let gvt = gvEvalCxt cxt t
    (u, gvb) <- infer ins (localDefine (Posed pos x) gvt gva cxt) u
    pure (Let (Named x a) t u, gvb)

  P.StopMetaIns t -> infer MINo cxt t

  P.Hole -> do
    m1 <- newMeta cxt
    m2 <- newMeta cxt
    pure (m1, gvEvalCxt cxt m2)

elabTopEntry :: P.TopEntry -> StateT NameTable IO ()
elabTopEntry e = do
  ntbl <- get
  lift (UA.push metas =<< A.empty)
  let cxt = initCxt ntbl
  x <- lift (A.size top)

  case e of
    P.TEPostulate (Posed pos n) a -> do
      lift $ do
        updPos pos
        a <- check cxt a gvU
        simplifyMetaBlock cxt
        let a'  = inline0 a
            gva = gvEvalCxt cxt a'
        A.push top (TEPostulate 0 [] 0 (Posed pos n) a' gva)
        pure gva
      put (addName n (NTETop x) ntbl)

    P.TEDefinition (Posed pos n) prof a t -> do
      lift $ do
        updPos pos
        ((GV gt _, gva), time) <- timed $ do
          a <- check cxt a gvU
          let gva = gvEvalCxt cxt a
          t <- check cxt t gva
          simplifyMetaBlock cxt
          let a'   = inline0 a
              t'   = inline0 t
              gva' = gvEvalCxt cxt a'
              gvt  = gvEvalCxt cxt t'
          A.push top (TEDefinition gvt t' (Posed pos n) a' gva')
          pure (gvt, gva')
        case prof of
          Nothing -> pure ()
          Just P.PElabTime ->
            printf "Definition \"%s\" elaborated in %s\n" n (show time)
          Just P.PNormalizeTime -> do
            (nt, time) <- timedPure (gQuote 0 gt)
            printf "Definition \"%s\" normalized in %s\n" n (show time)
        pure gva
      put (addName n (NTETop x) ntbl)

    P.TERewrite vars lhs rhs -> lift $ do

      -- Go under the rule variables.
      ($ vars) $ ($ []) $ ($ cxt) $ fix $ \dive cxt@Cxt{..} vars' -> \case
        Posed pos (Named n a):vars -> do
          updPos pos
          a <- check cxt a gvU
          let gva = gvEvalCxt cxt a
          dive (bindVar (Posed pos n) gva cxt) (Named n a:vars') vars
        [] -> do
          -- printf "size: %d\n" _size

          let vars   = reverse vars'
              lhsPos = posOf lhs

          -- elaborate lhs, rhs
          (lhs, gva@(GV ga _)) <- infer MIYes cxt lhs
          -- printf "inferred lhs type: %s\n" (showGluedCxt cxt ga)
          rhs <- check cxt rhs gva

          -- inline metas
          let inlineVars :: [Named Ty] -> [Named Ty]
              inlineVars = go 0 ENil where
                go l vs []               = []
                go l vs (Named n a:vars) =
                  (:) (Named n (inline l vs a)) $! go (l + 1) (ESkip vs) vars

          simplifyMetaBlock cxt
          vars <- pure (inlineVars vars)
          lhs  <- pure (inline _size _vEnv lhs)
          rhs  <- pure (inline _size _vEnv rhs)

          -- get lhs spine
          updPos lhsPos
          let (hd, sp) = go lhs [] where
                go (AppI t u) sp = go t (u:sp)
                go (AppE t u) sp = go t (u:sp)
                go t          sp = (t, sp)

          -- TODO: check whether lhs unifies with rhs

          -- check lhs head, arity, register rule
          case hd of
            TopVar x -> case lookupTop x of
              TEPostulate numRules rules arity name a gva -> do
                let spLen = length sp
                when (not (null rules) && (spLen /= arity)) $
                  throw (TopError cxt (EEWrongRuleArity arity spLen))
                when (spLen == 0) $
                  throw (TopError cxt EEIllegalRuleLHS)
                let lhsTms    = Exts.fromList sp
                    lhsOccurs = Exts.fromList (map (freeLocalVars _size) sp)
                    rule      = RewriteRule _size vars lhsTms lhsOccurs lhs rhs
                -- printf "%s %s\n" (show lhsTms) (show lhsOccurs)
                A.push top (TERewriteRule rule)
                A.write top x $
                  TEPostulate (numRules + 1) (rules ++ [rule]) spLen name a gva
              _ -> error "elabTopEntry: impossible"
            _ -> throw (TopError cxt EEIllegalRuleLHS)

checkProgram :: P.Program -> IO NameTable
checkProgram es = do
  reset
  execStateT (mapM_ elabTopEntry es) mempty

--------------------------------------------------------------------------------

-- | Render elaboration output. Just for demo purposes. Serialization proper is TODO,
--   but this should already contain all to-be-serialized information.
renderElabOutput :: NameTable -> IO String
renderElabOutput ntbl = do
  es <- A.foldr'  (:) [] top
  ms <- UA.foldr' (:) [] metas

  let go :: (Int, TopEntry) -> A.Array MetaEntry -> IO [String]
      go (i, e) ms = do
        ms <- A.foldr' (:) [] ms

        let metaBlock = filter (not . null) $ map
              (\case (j, (MESolved _ inl t _))
                         -> if inl then ""
                                   else printf "  %d.%d = %s" i j (showTm0 ntbl t)
                     _   -> error "renderElabOutput: impossible")
              (zip [(0 :: Int)..] ms)

            thisDef :: String
            thisDef = case e of
              TEDefinition _ t (Posed pos n) a _ ->
                printf "%s : %s\n = %s" n (showTm0 ntbl a) (showTm0 ntbl t)
              TEPostulate _ _ _ (Posed pos n) a _ ->
                printf "%s : %s" n (showTm0 ntbl a)
              TERewriteRule (RewriteRule _ vars _ _ lhs rhs) ->
                showRule ntbl vars lhs rhs

        pure $ if not (null metaBlock) then "mutual":metaBlock ++ [thisDef]
                                       else [thisDef]

  unlines . map unlines <$> zipWithM go (zip [(0::Int)..] es) ms
