{-# language UnboxedTuples #-}
{-# options_ghc -Wno-orphans #-}

module Elaboration (elab) where

import GHC.Exts

import qualified LvlSet as LS
import qualified MetaCxt as MC
import qualified Presyntax as P
import qualified SymTable as ST
import qualified TopCxt as Top
import qualified UIO
import qualified UIO as U
import qualified Unification as Unif

import Common
import CoreTypes
import Cxt
import Exceptions
import InCxt

#include "deriveCanIO.h"

--------------------------------------------------------------------------------

unify :: Cxt -> P.Tm -> G -> G -> U.IO ()
unify cxt pt l r = U.do
  debug ["unify", showValOpt cxt (g1 l) UnfoldMetas, showValOpt cxt (g1 r) UnfoldMetas]
  let ecxt = ErrorCxt (mcxt cxt) (tbl cxt) (names cxt) (lvl cxt); {-# inline ecxt #-}
  Unif.unify (mcxt cxt) (lvl cxt) (frz cxt) Rigid l r `catch` \case
     UnifyEx e -> throw $ UnifyExInCxt ecxt pt (g1 l) (g1 r) e
     _         -> impossible

-- Fresh metas and meta insertions
--------------------------------------------------------------------------------

-- | Term, unforced type, forced type.
data Infer = Infer Tm {-# unpack #-} GTy

CAN_IO3(Infer, LiftedRep, LiftedRep, LiftedRep, Tm, Val, Val, Infer x (G y z), CoeInfer)
CAN_IO2((Tm, Val), LiftedRep, LiftedRep, Tm, Val, (x, y), CoeTmVal)

-- CAN_IO(Infer, LiftedRep, Infer, x, CoeInfer)
-- CAN_IO((Tm, Val), LiftedRep, (Tm, Val), x, CoeTmVal)

-- | Create fresh meta both as a term and a value.
freshMeta :: Cxt -> U.IO (Tm, Val)
freshMeta cxt = U.do

  let goSp x l mask acc
        | x == l    = acc
        | otherwise =
          let acc' | LS.member x mask = SApp acc (VLocalVar x SId) Expl
                   | otherwise        = acc
          in goSp (x + 1) l mask acc'

  mvar <- MC.fresh (mcxt cxt) (mask cxt)
  let mt = InsertedMeta (coerce mvar)
  let mv = VFlex (coerce mvar) (goSp 0 (lvl cxt) (mask cxt) SId)
  U.pure (mt // mv)
{-# inline freshMeta #-}

-- | Create fresh meta as a term, under an extra binder.
freshMetaUnderBinder :: Cxt -> Icit -> U.IO Tm
freshMetaUnderBinder cxt i = U.do
  mvar <- MC.fresh (mcxt cxt) (LS.insert (lvl cxt) (mask cxt))
  U.pure (InsertedMeta (coerce mvar))
{-# inline freshMetaUnderBinder #-}

goInsert' :: Cxt -> Infer -> U.IO Infer
goInsert' cxt (Infer t (G a fa)) = forceAll cxt fa U.>>= \case
  VPi (NI x Impl) a b -> U.do
    (m, mv) <- freshMeta cxt
    let b' = appCl' cxt b mv
    goInsert' cxt (Infer (App t m Impl) (gjoin b'))
  fa -> U.pure (Infer t (G a fa))

-- | Insert fresh implicit applications.
insertApps' :: Cxt -> U.IO Infer -> U.IO Infer
insertApps' cxt act = goInsert' cxt U.=<< act
{-# inline insertApps' #-}

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insertApps :: Cxt -> U.IO Infer -> U.IO Infer
insertApps cxt act = act U.>>= \case
  res@(Infer (Lam (NI _ Impl) _) _) -> U.pure res
  res                               -> insertApps' cxt (U.pure res)
{-# inline insertApps #-}

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertAppsUntilName :: P.Tm -> Cxt -> Span -> U.IO Infer -> U.IO Infer
insertAppsUntilName topT cxt name act = go cxt U.=<< act where
  go cxt (Infer t (G topa ftopa)) = forceAll cxt ftopa U.>>= \case
    fa@(VPi (NI x Impl) a b) -> U.do
      if eqName cxt x (NSpan name) then
        U.pure (Infer t (G topa fa))
      else U.do
        (m, mv) <- freshMeta cxt
        let b' = appCl' cxt b mv
        go cxt (Infer (App t m Impl) (gjoin b'))
    _ ->
      throw $ NoNamedArgument topT name
{-# inline insertAppsUntilName #-}

-- Elaboration
--------------------------------------------------------------------------------

infer :: Cxt -> P.Tm -> U.IO Infer
infer cxt topT = U.do
  debug ["infer", showPTm cxt topT]

  Infer t a <- case topT of

    P.Var px -> U.do
      ma <- ST.lookup px (tbl cxt)

      case ma of
        UNothing             -> throw $ NotInScope px
        UJust (ST.Local x a) -> U.do

          -- debugging U.do
          --   foo <- U.io $ ST.assocs (tbl cxt)
          --   debug ["local var", show foo, showSpan (src cxt) px, show x,
          --          show $ lvlToIx (lvl cxt) x, show $ lvl cxt]

          U.pure (Infer (LocalVar (lvlToIx (lvl cxt) x)) a)

        UJust (ST.Top _ ga _ t) -> U.do

          -- debugging U.do
          --   foo <- U.io $ ST.assocs (tbl cxt)
          --   let x = case t of TopVar x _ -> x; _ -> impossible
          --   debug ["top var", show foo, showSpan (src cxt) px, show x]

          U.pure (Infer t ga)

    P.Let _ x ma t u ->
      checkWithAnnot cxt ma t \ ~t ~a va -> U.do
        Infer u vb <- defining cxt x va (eval cxt t) \cxt -> infer cxt u
        U.pure (Infer (Let x a t u) vb)

    topT@(P.App t u inf) ->

      U.bind3 (\pure -> case inf of
        P.Named x -> U.do
          Infer t tty <- insertAppsUntilName topT cxt x $ infer cxt t
          pure Impl t tty
        P.NoName Impl -> U.do
          Infer t tty <- infer cxt t
          pure Impl t tty
        P.NoName Expl -> U.do
          Infer t tty  <- insertApps' cxt $ infer cxt t
          pure Expl t tty)
      \i ~t (G tty ftty) ->

      U.bind2 (\pure -> forceAll cxt tty U.>>= \case
        VPi (NI x i') a b | i == i'   -> pure a b
                          | otherwise -> impossible
        ftty -> U.do
          a <- snd U.<$> freshMeta cxt
          b <- Closure (env cxt) U.<$> freshMetaUnderBinder cxt i
          let expected = VPi (NI NX i) a b
          unify cxt topT (G tty ftty) (gjoin expected)
          pure a b)
      \ ~a ~b -> U.do

      u <- check cxt u (gjoin a)
      let b' = appCl cxt b (eval cxt u)
      U.pure (Infer (App t u i) (gjoin b'))

    P.Pi _ x i a b -> U.do
      a <- checkType cxt a
      let ~va = eval cxt a
      binding cxt x i (gjoin va) \cxt _ -> U.do
        b <- checkType cxt b
        U.pure (Infer (Pi (NI (P.bind x) i) a b) (gjoin VU))

    P.Lam _ x P.Named{} ma t ->
      throw InferNamedLam

    P.Lam _ x (P.NoName i) ma t ->
      U.bind2 (\pure -> case ma of
        UNothing -> U.do (m, mv) <- freshMeta cxt
                         pure m mv
        UJust a  -> U.do a <- checkType cxt a
                         let ~va = eval cxt a
                         pure a va)
      \ ~a ~va -> U.do

      Infer t vb <- binding cxt x i (gjoin va) \cxt _ -> insertApps cxt (infer cxt t)
      let ty = VPi (NI (P.bind x) i) va (valToClosure cxt (g1 vb))
      U.pure (Infer (Lam (NI (P.bind x) i) t) (gjoin ty))

    P.U _ ->
      U.pure (Infer U (gjoin VU))

    P.Hole _ -> U.do
      (_, va) <- freshMeta cxt
      (t, _ ) <- freshMeta cxt
      U.pure (Infer t (gjoin va))

  debug ["inferred", showTm cxt t, showValOpt cxt (g1 a) UnfoldNone]
  U.pure (Infer t a)

-- | Choose between checking and inferring depending on an optional type annotation.
checkWithAnnot :: U.CanIO a => Cxt -> UMaybe P.Tm -> P.Tm
               -> (Tm -> Ty -> GTy -> U.IO a) -> U.IO a
checkWithAnnot cxt ma t k = case ma of
  UNothing -> U.do
    Infer t va <- insertApps cxt $ infer cxt t
    let a = quote cxt UnfoldNone (g1 va)
    k t a va
  UJust a -> U.do
    a <- checkType cxt a
    let va = gjoin $! eval cxt a
    t <- check cxt t va
    k t a va
{-# inline checkWithAnnot #-}

-- | Check that a preterm is a type.
checkType :: Cxt -> P.Tm -> U.IO Tm
checkType cxt pt = check cxt pt (gjoin VU)
{-# inline checkType #-}

check :: Cxt -> P.Tm -> GTy -> U.IO Tm
check cxt topT (G topA ftopA) = U.do
  debug ["check", showPTm cxt topT, showValOpt cxt topA UnfoldNone]

  ftopA <- forceAll cxt ftopA
  case (topT, ftopA) of
    (P.Lam _ x inf ma t, VPi (NI x' i) a b)
      | (case inf of P.NoName i' -> i == i'
                     P.Named n   -> eqName cxt x' (NSpan n) && i == Impl) ->

      -- We prefer the user-provided annotation for the unforced binder type
      U.bind1 (\pure -> case ma of
        UNothing -> pure a
        UJust a' -> U.do
          a' <- checkType cxt a'
          let va' = eval cxt a'
          unify cxt topT (gjoin va') (gjoin a)
          pure va')
      \a ->
      binding cxt x i (gjoin a) \cxt v -> U.do
        Lam (NI (P.bind x) i) U.<$> (check cxt t $! (gjoin $! appCl' cxt b v))

    (t, VPi (NI x Impl) a b) ->
      inserting cxt x \cxt v -> U.do
        t <- check cxt t $! (gjoin $! appCl' cxt b v)
        U.pure (Lam (NI x Impl) t)

    (P.Let _ x ma t u, ftopA) ->
      checkWithAnnot cxt ma t \ ~t ~a va ->
        defining cxt x va (eval cxt t) \cxt ->
          Let x a t U.<$> check cxt u (G topA ftopA)

    (P.Hole _, _) ->
      fst U.<$> freshMeta cxt

    (topT, ftopA) -> U.do
      Infer t inferred <- insertApps cxt $ infer cxt topT
      unify cxt topT inferred (G topA ftopA)
      U.pure t


-- Top level elaboration
--------------------------------------------------------------------------------

printingElabTime :: U.CanIO a => Top.Cxt -> Span -> Bool -> U.IO a -> U.IO a
printingElabTime topCxt x timing act
  | timing    = U.do
    (a, time) <- U.timed act
    U.io $ putStrLn (showTopSpan topCxt x ++ " elaborated in " ++ show time)
    U.pure a
  | otherwise = act
{-# inline printingElabTime #-}

printingNfTime :: Top.Cxt -> Span -> Bool -> Tm -> U.IO ()
printingNfTime topCxt x timing t
  | timing    = U.io do
    let cxt = empty topCxt
    time <- timedPure_ (quote cxt UnfoldAll (eval cxt t))
    putStrLn (showTopSpan topCxt x ++ " normalized in " ++ show time)
  | otherwise = U.pure ()
{-# inline printingNfTime #-}

showTopSpan :: Top.Cxt -> Span -> String
showTopSpan topCxt x = showSpan (ST.src (Top.tbl topCxt)) x
{-# noinline showTopSpan #-}

elabTopLevel :: Top.Cxt -> P.TopLevel -> U.IO Top.Cxt
elabTopLevel topCxt = \case

  P.Nil ->
    U.pure topCxt

  P.Definition (P.TopInfo x elabt nft) ma t u -> U.do

    let cxt = empty topCxt
    U.bind3 (\pure -> case ma of

      UNothing -> U.do
        Infer t va <- printingElabTime topCxt x elabt (insertApps cxt $ infer cxt t)
        let a = quote cxt UnfoldNone (g1 va)
        printingNfTime topCxt x nft t
        pure t a va

      UJust a -> U.do
        a <- checkType cxt a
        let va = gjoin $! eval cxt a
        t <- printingElabTime topCxt x elabt (check cxt t va)
        printingNfTime topCxt x nft t
        pure t a va)

      \ ~t ~a va -> U.do
        topCxt <- Top.define x a va t topCxt
        elabTopLevel topCxt u
{-# noinline elabTopLevel #-}


elab :: Src -> P.TopLevel -> IO (Either Exception Top.Cxt)
elab src top = U.toIO U.do
  topCxt <- Top.new src (P.topLen top)
  try (elabTopLevel topCxt top)
