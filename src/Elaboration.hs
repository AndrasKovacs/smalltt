
module Elaboration (elab) where

import GHC.Exts

import qualified LvlSet as LS
import qualified MetaCxt as MC
import qualified Presyntax as P
import qualified SymTable as ST
import qualified TopCxt as Top
import qualified Unification as Unif

import Common
import CoreTypes
import Cxt
import Exceptions
import InCxt

--------------------------------------------------------------------------------

unify :: Cxt -> P.Tm -> G -> G -> IO ()
unify cxt pt l r = do
  debug ["unify", showValOpt cxt (g1 l) UnfoldMetas, showValOpt cxt (g1 r) UnfoldMetas]
  let ecxt = ErrorCxt (mcxt cxt) (tbl cxt) (names cxt) (lvl cxt); {-# inline ecxt #-}
  Unif.unify (mcxt cxt) (lvl cxt) (frz cxt) Rigid l r `catch` \case
     UnifyEx e -> throw $ UnifyExInCxt ecxt pt (g1 l) (g1 r) e
     _         -> impossible

-- Fresh metas and meta insertions
--------------------------------------------------------------------------------

-- | Term, unforced type, forced type.
data Infer = Infer Tm {-# unpack #-} GTy

-- | Create fresh meta both as a term and a value.
freshMeta :: Cxt -> IO (Tm, Val)
freshMeta cxt = do

  let goSp x l mask acc
        | x == l    = acc
        | otherwise =
          let acc' | LS.member x mask = SApp acc (VLocalVar x SId) Expl
                   | otherwise        = acc
          in goSp (x + 1) l mask acc'

  mvar <- MC.fresh (mcxt cxt) (mask cxt)
  let mt = InsertedMeta (coerce mvar)
  let mv = VFlex (coerce mvar) (goSp 0 (lvl cxt) (mask cxt) SId)
  pure $! (mt // mv)
{-# inline freshMeta #-}

-- | Create fresh meta as a term, under an extra binder.
freshMetaUnderBinder :: Cxt -> Icit -> IO Tm
freshMetaUnderBinder cxt i = do
  mvar <- MC.fresh (mcxt cxt) (LS.insert (lvl cxt) (mask cxt))
  pure $! (InsertedMeta (coerce mvar))
{-# inline freshMetaUnderBinder #-}

goInsert' :: Cxt -> Infer -> IO Infer
goInsert' cxt (Infer t (G a fa)) = forceAll cxt fa >>= \case
  VPi (NI x Impl) a b -> do
    (m, mv) <- freshMeta cxt
    let b' = appCl' cxt b mv
    goInsert' cxt (Infer (App t m Impl) (gjoin b'))
  fa -> pure (Infer t (G a fa))

-- | Insert fresh implicit applications.
insertApps' :: Cxt -> IO Infer -> IO Infer
insertApps' cxt act = goInsert' cxt =<< act
{-# inline insertApps' #-}

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insertApps :: Cxt -> IO Infer -> IO Infer
insertApps cxt act = act >>= \case
  res@(Infer (Lam (NI _ Impl) _) _) -> pure res
  res                               -> insertApps' cxt (pure res)
{-# inline insertApps #-}

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertAppsUntilName :: P.Tm -> Cxt -> Span -> IO Infer -> IO Infer
insertAppsUntilName topT cxt name act = go cxt =<< act where
  go cxt (Infer t (G topa ftopa)) = forceAll cxt ftopa >>= \case
    fa@(VPi (NI x Impl) a b) -> do
      if eqName cxt x (NSpan name) then
        pure (Infer t (G topa fa))
      else do
        (m, mv) <- freshMeta cxt
        let b' = appCl' cxt b mv
        go cxt (Infer (App t m Impl) (gjoin b'))
    _ ->
      throw $ NoNamedArgument topT name
{-# inline insertAppsUntilName #-}

-- Elaboration
--------------------------------------------------------------------------------

infer :: Cxt -> P.Tm -> IO Infer
infer cxt topT = do
  debug ["infer", showPTm cxt topT]

  Infer t a <- case topT of

    P.Var px -> do
      ma <- ST.lookup px (tbl cxt)

      case ma of
        UNothing             -> throw $ NotInScope px
        UJust (ST.Local x a) -> do

          -- debugging do
          --   foo <- io $ ST.assocs (tbl cxt)
          --   debug ["local var", show foo, showSpan (src cxt) px, show x,
          --          show $ lvlToIx (lvl cxt) x, show $ lvl cxt]

          pure $! (Infer (LocalVar (lvlToIx (lvl cxt) x)) a)

        UJust (ST.Top _ ga _ t) -> do

          -- debugging do
          --   foo <- io $ ST.assocs (tbl cxt)
          --   let x = case t of TopVar x _ -> x; _ -> impossible
          --   debug ["top var", show foo, showSpan (src cxt) px, show x]

          pure (Infer t ga)

    P.Let _ x ma t u ->
      checkWithAnnot cxt ma t \ t a va -> do
        Infer u vb <- defining cxt x va (eval cxt t) \cxt -> infer cxt u
        pure $! Infer (Let x a t u) vb

    topT@(P.App t u inf) -> do

      (i, t, G tty ftty) <- case inf of
        P.Named x -> do
          Infer t tty <- insertAppsUntilName topT cxt x $ infer cxt t
          pure (Impl, t, tty)
        P.NoName Impl -> do
          Infer t tty <- infer cxt t
          pure (Impl, t, tty)
        P.NoName Expl -> do
          Infer t tty  <- insertApps' cxt $ infer cxt t
          pure (Expl, t, tty)

      (a, b) <- forceAll cxt tty >>= \case
        VPi (NI x i') a b | i == i'   -> pure (a, b)
                          | otherwise -> impossible
        ftty -> do
          a <- snd <$> freshMeta cxt
          b <- Closure (env cxt) <$> freshMetaUnderBinder cxt i
          let expected = VPi (NI NX i) a b
          unify cxt topT (G tty ftty) (gjoin expected)
          pure (a, b)

      u <- check cxt u (gjoin a)
      let b' = appCl cxt b (eval cxt u)
      pure $! Infer (App t u i) (gjoin b')

    P.Pi _ x i a b -> do
      a <- checkType cxt a
      let ~va = eval cxt a
      binding cxt x i (gjoin va) \cxt _ -> do
        b <- checkType cxt b
        pure $! (Infer (Pi (NI (P.bind x) i) a b) (gjoin VU))

    P.Lam _ x P.Named{} ma t ->
      throw InferNamedLam

    P.Lam _ x (P.NoName i) ma t -> do
      (a, va) <- case ma of
        UNothing -> freshMeta cxt
        UJust a  -> do a <- checkType cxt a
                       pure (a, eval cxt a)

      Infer t vb <- binding cxt x i (gjoin va) \cxt _ -> insertApps cxt (infer cxt t)
      let ty = VPi (NI (P.bind x) i) va (valToClosure cxt (g1 vb))
      pure $! Infer (Lam (NI (P.bind x) i) t) (gjoin ty)

    P.U _ ->
      pure $! (Infer U (gjoin VU))

    P.Hole _ -> do
      (_, va) <- freshMeta cxt
      (t, _ ) <- freshMeta cxt
      pure $! (Infer t (gjoin va))

  debug ["inferred", showTm cxt t, showValOpt cxt (g1 a) UnfoldNone]
  pure (Infer t a)

-- | Choose between checking and inferring depending on an optional type annotation.
checkWithAnnot :: Cxt -> UMaybe P.Tm -> P.Tm -> (Tm -> Ty -> GTy -> IO a) -> IO a
checkWithAnnot cxt ma t k = case ma of
  UNothing -> do
    Infer t va <- insertApps cxt $ infer cxt t
    let a = quote cxt UnfoldNone (g1 va)
    k t a va
  UJust a -> do
    a <- checkType cxt a
    let va = gjoin $! eval cxt a
    t <- check cxt t va
    k t a va
{-# inline checkWithAnnot #-}

-- | Check that a preterm is a type.
checkType :: Cxt -> P.Tm -> IO Tm
checkType cxt pt = check cxt pt (gjoin VU)
{-# inline checkType #-}

check :: Cxt -> P.Tm -> GTy -> IO Tm
check cxt topT (G topA ftopA) = do
  debug ["check", showPTm cxt topT, showValOpt cxt topA UnfoldNone]

  ftopA <- forceAll cxt ftopA
  case (topT, ftopA) of
    (P.Lam _ x inf ma t, VPi (NI x' i) a b)
      | (case inf of P.NoName i' -> i == i'
                     P.Named n   -> eqName cxt x' (NSpan n) && i == Impl) -> do

      -- We prefer the user-provided annotation for the unforced binder type
      a <- case ma of
        UNothing -> pure a
        UJust a' -> do
          a' <- checkType cxt a'
          let va' = eval cxt a'
          unify cxt topT (gjoin va') (gjoin a)
          pure va'

      binding cxt x i (gjoin a) \cxt v -> do
        Lam (NI (P.bind x) i) <$> (check cxt t $! (gjoin $! appCl' cxt b v))

    (t, VPi (NI x Impl) a b) ->
      inserting cxt x \cxt v -> do
        t <- check cxt t $! (gjoin $! appCl' cxt b v)
        pure (Lam (NI x Impl) t)

    (P.Let _ x ma t u, ftopA) ->
      checkWithAnnot cxt ma t \ ~t ~a va ->
        defining cxt x va (eval cxt t) \cxt ->
          Let x a t <$> check cxt u (G topA ftopA)

    (P.Hole _, _) ->
      fst <$> freshMeta cxt

    (topT, ftopA) -> do
      Infer t inferred <- insertApps cxt $ infer cxt topT
      unify cxt topT inferred (G topA ftopA)
      pure t


-- Top level elaboration
--------------------------------------------------------------------------------

printingElabTime :: Top.WithCxt (Span -> Bool -> IO a -> IO a)
printingElabTime x timing act
  | timing = do
    (a, time) <- timed act
    putStrLn (showTopSpan x ++ " elaborated in " ++ show time)
    pure a
  | otherwise = act
{-# inline printingElabTime #-}

printingNfTime :: Top.WithCxt (Span -> Bool -> Tm -> IO ())
printingNfTime x timing t
  | timing = do
    let cxt = empty Top.cxt
    time <- timedPure_ (quote cxt UnfoldAll (eval cxt t))
    putStrLn (showTopSpan x ++ " normalized in " ++ show time)
  | otherwise = pure ()
{-# inline printingNfTime #-}

showTopSpan :: Top.WithCxt (Span -> String)
showTopSpan x = showSpan (ST.src ?tbl) x
{-# noinline showTopSpan #-}

elabTopLevel :: Top.WithCxt (P.TopLevel -> IO Top.Cxt)
elabTopLevel = \case

  P.Nil ->
    pure $! Top.cxt

  P.Definition (P.TopInfo x elabt nft) ma t u -> do

    let cxt = empty $! Top.cxt
    (t, a, va) <- case ma of

      UNothing -> do
        Infer t va <- printingElabTime x elabt (insertApps cxt $ infer cxt t)
        let a = quote cxt UnfoldNone (g1 va)
        printingNfTime x nft t
        pure (t, a, va)

      UJust a -> do
        a <- checkType cxt a
        let va = gjoin $! eval cxt a
        t <- printingElabTime x elabt (check cxt t va)
        printingNfTime x nft t
        pure (t, a, va)

    Top.define x a va t $ elabTopLevel u

elab :: Src -> P.TopLevel -> IO (Either Exception Top.Cxt)
elab src top =
  Top.new src (P.topLen top) (try $! elabTopLevel top)
