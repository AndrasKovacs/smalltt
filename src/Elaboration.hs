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
  - make Ix and Lvl newtype, do safer API

Things to perhaps benchmark:
  - IO Exception vs error codes in unification
  - Arrays vs lists in renaming
  - Reader monads vs param passing.
-}

module Elaboration where

import qualified Data.HashMap.Strict as HM
import qualified Data.Array.Dynamic as A
import qualified Data.Array.Dynamic.Unlifted as UA
import Text.Printf

import Control.Exception
import Control.Monad
import Data.IORef

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

import Debug.Trace


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

isUnfoldable :: Tm -> Bool
isUnfoldable t = go t where
  go LocalVar{} = True
  go MetaVar{}  = True
  go TopVar{}   = True
  go (Lam _ t)  = go t
  go U          = True
  go _          = False

registerSolution :: Meta -> Tm -> IO ()
registerSolution (Meta i j) t = do
  arr <- UA.unsafeRead metas i
  pos <- getPos
  A.unsafeWrite arr j (MESolved (vEval ENil t) (isUnfoldable t) t pos)
{-# inline registerSolution #-}

disjointLvls :: LS.LvlSet -> Renaming -> Bool
disjointLvls xs RNil            = True
disjointLvls xs (RCons x _ ren) = not (LS.member x xs) && disjointLvls xs ren

contract :: (Lvl, Renaming) -> Val -> ((Lvl, Renaming), Val)
contract topRen topV@(VNe h topVsp) = go (mempty @LS.LvlSet) topRen topVsp where
  go xs (!l, ren) SNil
    | disjointLvls xs ren = ((l, ren), VNe h SNil)
  go xs (!l, RCons x _ ren) (SAppI vsp (VLocal x'))
    | x == x', not (LS.member x xs) = go (LS.insert x xs) (l - 1, ren) vsp
  go xs (!l, RCons x _ ren) (SAppE vsp (VLocal x'))
    | x == x', not (LS.member x xs) = go (LS.insert x xs) (l - 1, ren) vsp
  go _ _ _ = (topRen, topV)
contract ren v = (ren, v)

lams :: Lvl -> Names -> Renaming -> Tm -> Tm
lams l ns = go where
  go RNil            t = t
  go (RCons x y ren) t = go ren (Lam (Named (lookupName (l - x - 1) ns) Expl) t)


--  Generating meta solutions
--------------------------------------------------------------------------------

-- | Throws (FlexRigid LocalError).
--   Always throws flex because in a rigid case the glued check immediately throws
--   afterwards anyway, and error messages aren't worse in glued mode.
vQuoteSolution ::
  (FlexRigid LocalError -> IO ()) -> Lvl -> Names -> Meta -> (Lvl, Renaming) -> Val -> IO Tm
vQuoteSolution throwAction = \l ns occurs ren v ->
  let
    scopeCheck :: Lvl -> (Lvl, Renaming) -> Val -> IO Tm
    scopeCheck l (renl, ren) v = go l ren v  where
      shift = l - renl
      go :: Lvl -> Renaming -> Val -> IO Tm
      go l ren v = case v of
        VNe h vsp -> case h of
          HLocal x -> case applyRen ren x of
            (-1)   -> Irrelevant <$ throwAction (FRFlex @LocalError)
            y      -> goSp l ren (LocalVar (l - shift - y - 1)) vsp
          HTop   x -> goSp l ren (TopVar x) vsp
          HMeta  x | x == occurs -> Irrelevant <$ throwAction (FRFlex @LocalError)
                   | otherwise   -> lookupMetaIO x >>= \case
                       MEUnsolved{} -> goSp l ren (MetaVar x) vsp
                       MESolved{}   -> do
                         when (metaTopLvl x == metaTopLvl occurs) $
                           throwAction (FRFlex @LocalError)
                         goSp l ren (MetaVar x) vsp

        VLam x t     -> Lam x <$> go (l + 1) (RCons l (l - shift) ren) (vInst t (VLocal l))
        VPi x a b    -> Pi x <$> go l ren a
                             <*> go (l + 1) (RCons l (l - shift) ren) (vInst b (VLocal l))
        VFun a b     -> Fun <$> go l ren a <*> go l ren b
        VU           -> pure U
        VIrrelevant  -> pure Irrelevant
        VGlueTop x sp t -> goSp l ren (TopVar x) sp
        VGlueMeta x sp _ -> go l ren (VNe (HMeta x) sp)

      goSp :: Lvl -> Renaming -> Tm -> VSpine -> IO Tm
      goSp l ren t (SAppI vsp v) = AppI <$> goSp l ren t vsp <*> go l ren v
      goSp l ren t (SAppE vsp v) = AppE <$> goSp l ren t vsp <*> go l ren v
      goSp l ren t SNil          = pure t

  in lams l ns (snd ren) <$> scopeCheck l ren v
{-# inline vQuoteSolution #-}

-- | Abort quoting on error.
vQuoteSolutionShortCut :: Lvl -> Names -> Meta -> (Lvl, Renaming) -> Val -> IO Tm
vQuoteSolutionShortCut = vQuoteSolution throw
{-# inline vQuoteSolutionShortCut #-}

-- | On error, write error to IORef then continue quoting.
vQuoteSolutionRefError ::
     IORef (Maybe (FlexRigid LocalError))
  -> Lvl -> Names -> Meta -> (Lvl, Renaming) -> Val -> IO Tm
vQuoteSolutionRefError ref = vQuoteSolution (\e -> writeIORef ref (Just e))
{-# inline vQuoteSolutionRefError #-}

type Unfolding = Int

-- | Try to unify local values. May succeed with () or throw ElabError. A rigid
--   error is unrecoverable and will be reported, a flex error can be rectified
--   if full unification succeeds later.
-- unfoldLimit :: Unfolding
-- unfoldLimit = 2
-- {-# inline unfoldLimit #-}

-- -- | Throws (FlexRigid LocalError).
-- vUnify :: Cxt -> Val -> Val -> IO ()
-- vUnify cxt v v' = go (_size cxt) unfoldLimit (_names cxt) Rigid v v' where

--   go :: Lvl -> Unfolding -> Names -> Rigidity -> Val -> Val -> IO ()
--   go l u ns r v v' = case (v, v') of

--     (VIrrelevant, _) -> pure ()
--     (_, VIrrelevant) -> pure ()

--     -- same heads
--     (VU, VU) -> pure ()

--     (VLam (Named n i) t, VLam _ t') -> let var = VLocal l in
--       go (l + 1) u (NSnoc ns n) r (vInst t var) (vInst t' var)
--     (VLam (Named n i) t, t'       ) -> let var = VLocal l in
--       go (l + 1) u (NSnoc ns n) r (vInst t var) (vApp i t' var)
--     (t     , VLam (Named n' i') t') -> let var = VLocal l in
--       go (l + 1) u (NSnoc ns n') r (vApp i' t var) (vInst t' var)

--     (VPi (Named n i) a b, VPi (Named _ i') a' b') | i == i' -> do
--       go l u ns r a a'
--       let var = VLocal l
--       go (l + 1) u (NSnoc ns n) r (vInst b var) (vInst b' var)

--     (VPi (Named n i) a b, VFun a' b') -> do
--       go l u ns r a a'
--       go (l + 1) u (NSnoc ns n) r (vInst b (VLocal l)) b'

--     (VFun a b, VPi (Named n' i') a' b') -> do
--       go l u ns r a a'
--       go (l + 1) u (NSnoc ns n') r b (vInst b' (VLocal l))

--     (VFun a b, VFun a' b') -> go l u ns r a a' >> go l u ns r b b'

--     (v@(VNe (HTop x) vsp), v'@(VNe (HTop x') vsp')) | x == x' -> do
--       let r' = r `meld` topRigidity x `meld` topRigidity x'
--       goSp (cantUnify l ns r' v v') l u ns r' vsp vsp'

--     (v@(VNe (HLocal x) vsp), v'@(VNe (HLocal x') vsp')) | x == x' -> do
--       goSp (cantUnify l ns r v v') l u ns r vsp vsp'

--     (v@(VNe (HMeta x) vsp), v'@(VNe (HMeta x') vsp')) | x == x' -> do
--       let r'  = r `meld` metaRigidity x `meld` metaRigidity x'
--       let err = cantUnify l ns r' v v'
--       goSp err l u ns r' vsp vsp'

--     -- meta sides
--     (v@(VNe (HMeta x) vsp), v')
--       | MESolved v _ _ _ <- lookupMeta x ->
--         if u > 0 then go l (u - 1) ns r (vAppSpine v vsp) v'
--                  else cantUnify l ns Flex v v'
--       | MEUnsolved _ <- lookupMeta x, Rigid <- r ->
--         solve l ns x vsp v'

--     (v, v'@(VNe (HMeta x') vsp'))
--       | MESolved v' _ _ _ <- lookupMeta x' ->
--         if u > 0 then go l (u - 1) ns r v (vAppSpine v' vsp')
--                  else cantUnify l ns Flex v v'
--       | MEUnsolved _ <- lookupMeta x', Rigid <- r ->
--         solve l ns  x' vsp' v

--     -- top sides
--     (v@(VNe (HTop x) vsp), v')
--       | EDDefinition _ v <- _entryDef (lookupTop x) ->
--         if u > 0 then go l (u - 1) ns r (vAppSpine v vsp) v'
--                  else cantUnify l ns Flex v v'

--     (v, v'@(VNe (HTop x') vsp'))
--       | EDDefinition _ v' <- _entryDef (lookupTop x') ->
--         if u > 0 then go l (u - 1) ns r v (vAppSpine v' vsp')
--                  else cantUnify l ns Flex v v'

--     (v, v') -> cantUnify l ns r v v'

--   cantUnify l ns r v v' = throwIO (makeFR r (LocalError ns (UELocalUnify v v')))
--   {-# inline cantUnify #-}

--   solve :: Lvl -> Names -> Meta -> VSpine -> Val -> IO ()
--   solve l ns x vsp v = do
--     let checkVSp :: VSpine -> (Lvl, Renaming)
--         checkVSp = go where
--           go SNil = (0, RNil)
--           go (SAppI vsp v) = case vForce v of
--             VLocal x -> case go vsp of
--               (l, ren) -> (l + 1, RCons x l ren)
--             _        -> throw (FRFlex @LocalError)
--           go (SAppE vsp v) = case vForce v of
--             VLocal x -> case go vsp of
--               (l, ren) -> (l + 1, RCons x l ren)
--             _        -> throw (FRFlex @LocalError)

--     case contract (checkVSp vsp) v of
--       (ren, v) -> do
--         rhs <- vQuoteSolutionShortCut l ns x ren v
--         registerSolution x rhs

--   goSp :: IO () -> Lvl -> Unfolding -> Names -> Rigidity -> VSpine -> VSpine -> IO ()
--   goSp err l u ns r (SAppI vsp v) (SAppI vsp' v') = goSp err l u ns r vsp vsp' >> go l u ns r v v'
--   goSp err l u ns r (SAppE vsp v) (SAppE vsp' v') = goSp err l u ns r vsp vsp' >> go l u ns r v v'
--   goSp err l u ns r SNil            SNil          = pure ()
--   goSp err _ _ _  r _               _             = err


-- | Throws SolutionError, returns True if rhs is eta-convertible to lhs.
gCheckSolution :: Lvl -> Meta -> (Lvl, Renaming) -> Val -> IO Bool
gCheckSolution topLvl occurs (renl, ren) g = contr topLvl ren g where

  shift :: Int
  shift = topLvl - renl

  contr :: Lvl -> Renaming -> Val -> IO Bool
  contr l ren g = case vForce g of
    VLam _ t -> contr (l + 1) (RCons l (l - shift) ren) (vInst t (VLocal l))
    VNe (HMeta x) sp | occurs == x, strip l sp -> pure True where
       strip l SNil                   = l == topLvl
       strip l (SAppI gs (VLocal l')) = (l' == l - 1) && strip (l - 1) gs
       strip l (SAppE gs (VLocal l')) = (l' == l - 1) && strip (l - 1) gs
       strip _ _                      = False
    g -> False <$ scopeCheck l ren g

  scopeCheck :: Lvl -> Renaming -> Val -> IO ()
  scopeCheck = go where
    go l ren g = case vForce g of
      VNe h sp -> do
        case h of
          HLocal x -> case applyRen ren x of
            (-1)   -> throwIO (SEScope x)
            _      -> pure ()
          HTop{} -> pure ()
          HMeta x | x == occurs -> throwIO SEOccurs
                  | otherwise   -> pure ()
        goSp l ren sp
      VLam x t    -> go (l + 1) (RCons l (l - shift) ren) (vInst t (VLocal l))
      VPi x a b   -> go l ren a >> go (l + 1) (RCons l (l - shift) ren) (vInst b (VLocal l))
      VFun a b    -> go l ren a >> go l ren b
      VGlueTop _ _ t -> go l ren t
      VGlueMeta _ _ t -> go l ren t
      VU          -> pure ()
      VIrrelevant -> pure ()

    goSp :: Lvl -> Renaming -> VSpine -> IO ()
    goSp l ren SNil          = pure ()
    goSp l ren (SAppI gsp g) = goSp l ren gsp >> go l ren g
    goSp l ren (SAppE gsp g) = goSp l ren gsp >> go l ren g


-- | Throws LocalError.
gvUnify :: Cxt -> Val -> Val -> IO ()
gvUnify cxt v v' = go (_size cxt) (_names cxt) v v'
  -- vUnify cxt v v'
  -- `catch`
  -- \case
  --   FRRigid e -> throw (e :: LocalError)
  --   FRFlex    -> go (_size cxt) (_names cxt) v v'
  where
    go :: Lvl -> Names -> Val -> Val -> IO ()
    go l ns v v' = case (vForce v, vForce v') of
      (VIrrelevant, _) -> pure ()
      (_, VIrrelevant) -> pure ()

      (VU, VU) -> pure ()

      (v@(VNe (HMeta x) sp), v'@(VNe (HMeta x') sp')) -> case compare x x' of
        LT -> solve l ns x' sp' v
        GT -> solve l ns x sp v
        EQ -> goSp (err ns v v') l ns sp sp'

      (VNe (HMeta x) sp, g') -> solve l ns x sp v'
      (g, VNe (HMeta x') sp') -> solve l ns x' sp' v

      (VLam (Named n i) t, VLam _ t') -> let var = VLocal l in
        go (l + 1) (NSnoc ns n) (vInst t var) (vInst t' var)

      (VLam (Named n i) t, t'       ) -> let var = VLocal l in
        go (l + 1) (NSnoc ns n) (vInst t var) (vApp i t' var)

      (t     , VLam (Named n' i') t') -> let var = VLocal l in
        go (l + 1) (NSnoc ns n') (vApp i' t var) (vInst t' var)

      (VPi (Named n i) a b, VPi (Named _ i') a' b') | i == i' -> do
        let var = VLocal l
        go l ns a a'
        go (l + 1) (NSnoc ns n) (vInst b var) (vInst b' var)

      (VPi (Named n i) a b, VFun a' b') -> do
        go l ns a a'
        go (l + 1) (NSnoc ns n) (vInst b (VLocal l)) b'

      (VFun a b, VPi (Named n' i') a' b') -> do
        go l ns a a'
        go (l + 1) (NSnoc ns n') b (vInst b' (VLocal l))

      (VFun a b, VFun a' b') -> go l ns a a' >> go l ns b b'

      (g@(VNe (HTop x) sp), g'@(VNe (HTop x') sp')) | x == x' ->
        goSp (err ns v v') l ns sp sp'
      (g@(VNe (HLocal x) sp), g'@(VNe (HLocal x') sp')) | x == x' ->
        goSp (err ns v v') l ns sp sp'

      (g, g') -> err ns v v'

    err ns v v' = throwIO (LocalError ns (UEGluedUnify v v'))
    {-# inline err #-}

    goSp :: IO () -> Lvl -> Names -> VSpine -> VSpine -> IO ()
    goSp err l ns (SAppI vsp v) (SAppI vsp' v') = goSp err l ns vsp vsp'
                                                >> go l ns v v'
    goSp err l ns (SAppE vsp v) (SAppE vsp' v') = goSp err l ns vsp vsp'
                                                >> go l ns v v'
    goSp err l ns SNil SNil = pure ()
    goSp err _ _  _    _    = err


    solve :: Lvl -> Names -> Meta -> VSpine -> Val -> IO ()
    solve l ns x spTop vTop = do

      let checkSp :: VSpine -> (Lvl, Renaming)
          checkSp = go where
            go SNil = (0, RNil)
            go (SAppI gsp g) = case g of
              VLocal x -> case go gsp of
                (l, ren) -> (l + 1, RCons x l ren)
              _        -> throw (LocalError ns (UEGluedSpine x spTop vTop g))
            go (SAppE gsp v) = case v of
              VLocal x -> case go gsp of
                (l, ren) -> (l + 1, RCons x l ren)
              _        -> throw (LocalError ns (UEGluedSpine x spTop vTop v))

          ren        = checkSp spTop
          (ren', v') = contract ren v

      err <- newIORef Nothing
      rhs <- vQuoteSolutionRefError err l ns x ren' v'
      readIORef err >>= \case
        Nothing          -> registerSolution x rhs
        Just (FRRigid e) -> throwIO e
        Just FRFlex      -> do
          chk <- gCheckSolution l x ren vTop
                 `catch`
                 (\e -> throwIO (LocalError ns (UEGluedSolution x spTop vTop e)))
          if chk then pure () else registerSolution x rhs

-- Elaboration
------------------------------------------------------------------------------------------

data MetaInsertion = MIYes | MINo | MIUntilName Name

vEval' :: Cxt -> Tm -> Val
vEval' cxt t = vEval (_vVals cxt) t
{-# inline vEval' #-}

newMeta :: Cxt -> IO Tm
newMeta cxt = do
  i     <- subtract 1 <$> UA.size metas
  arr   <- UA.unsafeRead metas i
  j     <- A.size arr
  pos   <- getPos
  A.push arr (MEUnsolved pos)
  let l   = _size cxt
      bis = _boundIndices cxt
      go BINil          = MetaVar (Meta i j)
      go (BISnoc bis x) = AppE (go bis) (LocalVar (l - x - 1))
  pure (go bis)

-- | Throws TopError.
check :: Cxt -> P.Tm -> VTy -> IO Tm
check cxt (Posed pos t) want = updPos pos >> case (t, vForce want) of
  (P.Lam x ni t, VPi (Named x' i') a b) | (case ni of NOName y -> y == x'
                                                      NOImpl   -> i' == Impl
                                                      NOExpl   -> i' == Expl) ->
    Lam (Named x i') <$> check (localBindSrc (Posed pos x) a cxt) t (vInst b (VLocal (_size cxt)))

  (P.Lam x NOExpl t, VFun a b) ->
    Lam (Named x Expl) <$> check (localBindSrc (Posed pos x) a cxt) t b

  (t, VPi (Named x Impl) a b) ->
    Lam (Named x Impl) <$> check (localBindIns (Posed pos x) a cxt)
                                 (Posed pos t) (vInst b (VLocal (_size cxt)))

  (P.Let x a t u, want) -> do
    a <- check cxt a VU
    let ~va = vEval' cxt a
    t <- check cxt t va
    let ~vt = vEval' cxt t
    u <- check (localDefine (Posed pos x) vt va cxt) u want
    pure (Let (Named x a) t u)

  (P.Hole, _) ->
    newMeta cxt

  (t, want) -> do
    (t, has) <- infer MIYes cxt (Posed pos t)
    gvUnify cxt has want
      `catch`
      \e -> do
        updPos pos
        throwIO (TopError cxt (EECheck t want has e))
    pure t

insertMetas :: MetaInsertion -> Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insertMetas ins cxt inp = case ins of
  MINo  -> inp
  MIYes -> do
    (t, va) <- inp
    let go t (vForce -> VPi (Named x Impl) a b) = do
          m <- newMeta cxt
          go (AppI t m) (vInst b (vEval' cxt m))
        go t gva = pure (t, gva)
    go t va
  MIUntilName x -> do
    (t, va) <- inp
    let go t va@(vForce -> VPi (Named x' Impl) a b)
          | x  == x'  = pure (t, va)
          | otherwise = do
              m <- newMeta cxt
              go (AppI t m) (vInst b (vEval' cxt m))
        go t va = throwIO (TopError cxt (EENoNamedArg t va x))
    go t va
{-# inline insertMetas #-}

inferVar :: Cxt -> Name -> IO (Tm, VTy)
inferVar cxt n =
  case HM.lookup n (_nameTable cxt) of
    Nothing -> throwIO (TopError cxt (EEScope n))
    Just es -> go es where
      go []               = throwIO (TopError cxt (EEScope n))
      go (NITop pos x:es) = do
        EntryTy _ vty <- _entryTy <$> A.unsafeRead top x
        pure (TopVar x, vty)
      go (NILocal pos origin x:es) = case origin of
        NOInserted -> go es
        NOSource   ->
          pure (LocalVar (_size cxt - x - 1), (_types cxt !! (_size cxt - x - 1)))
{-# inline inferVar #-}

-- throws TopError
infer :: MetaInsertion -> Cxt -> P.Tm -> IO (Tm, VTy)
infer ins cxt (Posed pos t) = updPos pos >> case t of
  P.U -> pure (U, VU)

  P.Var x -> insertMetas ins cxt (inferVar cxt x)

  -- TODO: do the case where a meta is inferred for "t"
  P.App t u ni -> insertMetas ins cxt $ do
    let insertion = case ni of
          NOName x -> MIUntilName x
          NOImpl   -> MINo
          NOExpl   -> MIYes
    (t, va) <- infer insertion cxt t
    case vForce va of
      VPi (Named x i') a b -> do
        case ni of
          NOName x -> pure ()
          NOImpl   -> unless (i' == Impl)
                        (updPos (posOf u) >> throwIO (TopError cxt (EEAppIcit t i' Impl)))
          NOExpl   -> unless (i' == Expl)
                        (updPos (posOf u) >> throwIO (TopError cxt (EEAppIcit t i' Expl)))
        u <- check cxt u a
        pure (app i' t u, vInst b (vEval' cxt u))
      VFun a b -> do
        case ni of NOExpl -> pure ()
                   _      -> updPos (posOf u) >> throwIO (TopError cxt (EEAppIcit t Expl Impl))
        u <- check cxt u a
        pure (AppE t u, b)
      va -> do
        traceM (showValCxt cxt va)
        traceM (showValCxtMetaless cxt va)
        throwIO (TopError cxt (EEFunctionExpected t va))

  P.Pi (Named x i) a b -> do
    a <- check cxt a VU
    b <- check (localBindSrc (Posed pos x) (vEval' cxt a) cxt) b VU
    pure (Pi (Named x i) a b, VU)

  P.Fun a b -> do
    a <- check cxt a VU
    b <- check cxt b VU
    pure (Fun a b, VU)

  P.Lam x ni t -> insertMetas ins cxt $ do
    i <- case ni of
      NOName x -> throwIO (TopError cxt EENamedLambda)
      NOImpl   -> pure Impl
      NOExpl   -> pure Expl
    va <- vEval' cxt <$> newMeta cxt
    (t, vb) <- infer MIYes (localBindSrc (Posed pos x) va cxt) t
    let d = _size cxt
        b = lQuote (d + 1) vb
        ni' = Named x i
    pure (Lam ni' t, VPi ni' va  (Cl (_vVals cxt) b))

  P.Let x a t u -> do
    a <- check cxt a VU
    let va = vEval' cxt a
    t <- check cxt t va
    let vt = vEval' cxt t
    (u, vb) <- infer ins (localDefine (Posed pos x) vt va cxt) u
    pure (Let (Named x a) t u, vb)

  P.StopMetaIns t -> infer MINo cxt t

  P.Hole -> do
    m1 <- newMeta cxt
    m2 <- newMeta cxt
    pure (m1, vEval' cxt m2)

checkTopEntry :: NameTable -> P.TopEntry -> IO NameTable
checkTopEntry ntbl e = do
  UA.push metas =<< A.empty
  let cxt = initCxt ntbl
  x <- A.size top
  case e of
    P.TEPostulate (Posed pos n) a -> updPos pos >> do
      ((), time) <- timed $ do
        a <- check cxt a VU
        simplifyMetaBlock cxt
        let a' = inline0 a
        A.push top (TopEntry (Posed pos n) EDPostulate (EntryTy a' (vEval' cxt a')))
      pure (addName n (NITop pos x) ntbl)
    P.TEDefinition (Posed pos n) prof a t -> updPos pos >> do
      (vt, time) <- timed $ do
        a <- check cxt a VU
        let va = vEval' cxt a
        t <- check cxt t va
        simplifyMetaBlock cxt
        let a'   = inline0 a
            t'   = inline0 t
            gva' = vEval' cxt a'
            gvt  = vEval' cxt t'
        A.push top (TopEntry (Posed pos n) (EDDefinition t' gvt) (EntryTy a' gva'))
        pure gvt
      case prof of
        Nothing -> pure ()
        Just P.PElabTime ->
          printf "Definition \"%s\" elaborated in %s\n" n (show time)
        Just P.PNormalizeTime -> do
          (nt, time) <- timedPure (nfQuote 0 vt)
          printf "Definition \"%s\" normalized in %s\n" n (show time)
      pure (addName n (NITop pos x) ntbl)

checkProgram :: P.Program -> IO NameTable
checkProgram es = reset >> go mempty es where
  go ntbl = \case
    []   -> pure ntbl
    e:es -> do {ntbl <- checkTopEntry ntbl e; go ntbl es}

--------------------------------------------------------------------------------

-- | Render elaboration output. Just for demo purposes. Serialization proper is TODO,
--   but this should already contain all to-be-serialized information.
renderElabOutput :: NameTable -> IO String
renderElabOutput ntbl = do
  es <- A.foldr'  (:) [] top
  ms <- UA.foldr' (:) [] metas

  let go :: (Int, TopEntry) -> A.Array MetaEntry -> IO [String]
      go (i, TopEntry (Posed _ n)  def (EntryTy a _)) ms = do
        ms <- A.foldr' (:) [] ms
        let metaBlock = filter (not . null) $ map
              (\case (j, (MESolved _ uf t _))
                         -> if uf then ""
                                  else printf "  %d.%d = %s" i j (showTm0 ntbl t)
                     _   -> error "renderElabOutput: impossible")
              (zip [(0 :: Int)..] ms)
            thisDef :: String
            thisDef = case def of
              EDPostulate      -> printf "assume %s : %s" n (showTm0 ntbl a)
              EDDefinition t _ -> printf "%s : %s\n = %s" n (showTm0 ntbl a) (showTm0 ntbl t)
        pure $ if not (null metaBlock) then "mutual":metaBlock ++ [thisDef]
                                       else [thisDef]

  unlines . map unlines <$> zipWithM go (zip [(0::Int)..] es) ms
