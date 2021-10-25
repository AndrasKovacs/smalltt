{-# language UnboxedTuples #-}
{-# options_ghc -Wno-orphans #-}

module Elaboration (checkProg) where

import qualified Data.ByteString as B
import GHC.Exts

import qualified LvlSet as LS
import qualified Evaluation as E
import qualified MetaCxt as MC
import qualified Presyntax as P
import qualified SymTable as ST
import qualified UIO
import qualified UIO as U
import qualified Unification as Unif
import Common
import CoreTypes
import Cxt
import Exceptions
import InCxt
import MetaCxt (MetaCxt)
import SymTable (SymTable)

#include "deriveCanIO.h"


--------------------------------------------------------------------------------

unify :: Cxt -> P.Tm -> Val -> Val -> Val -> Val -> U.IO ()
unify cxt t l r fl fr = U.do
  debug ["unify", showVal cxt l, showVal cxt r]
  Unif.unify (mcxt cxt) (lvl cxt) CSRigid fl fr `catch` \case
    UnifyEx _ -> throw $ UnifyError cxt t l r
    _         -> impossible
{-# inline unify #-}

solve :: Cxt -> P.Tm -> ConvState -> MetaVar -> Spine -> Val -> U.IO ()
solve cxt pt cs x sp rhs = U.do
  Unif.solve (mcxt cxt) (lvl cxt) cs x sp rhs `catch` \case
    UnifyEx _ -> throw $ UnifyError cxt pt (VFlex x sp) rhs
    _         -> impossible
{-# inline solve #-}

-- Fresh metas and meta insertions
--------------------------------------------------------------------------------

-- | Term, unforced type, forced type.
data Infer = Infer Tm VTy VTy

CAN_IO3(Infer, TupleRep [LiftedRep COMMA LiftedRep COMMA LiftedRep],
        (# Tm, Val, Val #), Infer x y z, CoeInfer)

CAN_IO2((Tm, Val), TupleRep [LiftedRep COMMA LiftedRep], (# Tm, Val #), (x, y), CoeTmVal)

-- | Create fresh meta both as a term and a value.
freshMeta :: Cxt -> U.IO (Tm, Val)
freshMeta cxt = U.do

  let goSp x l mask acc
        | x == l    = acc
        | otherwise =
          let acc' | LS.member x mask = SApp acc (VLocalVar x SId) Expl
                   | otherwise        = acc
          in goSp (x + 1) l mask acc'

  mvar <- MC.fresh (mcxt cxt)
  let mt = InsertedMeta (coerce mvar) (mask cxt)
  let mv = VFlex (coerce mvar) (goSp 0 (lvl cxt) (mask cxt) SId)
  U.pure (mt, mv)
{-# inline freshMeta #-}

-- | Create fresh meta as a term, under an extra binder.
freshMetaUnder :: Cxt -> Icit -> U.IO Tm
freshMetaUnder cxt i = U.do
  mvar <- MC.fresh (mcxt cxt)
  U.pure (InsertedMeta (coerce mvar) (LS.insert (lvl cxt) (mask cxt)))
{-# inline freshMetaUnder #-}

goInsert' :: Cxt -> Infer -> U.IO Infer
goInsert' cxt (Infer t va fva) = forceFU cxt fva U.>>= \case
  VPi x Impl a b -> U.do
    (m, mv) <- freshMeta cxt
    let b' = appCl cxt b mv
    goInsert' cxt (Infer (App t m Impl) b' b')
  fva -> U.pure (Infer t va fva)

-- | Insert fresh implicit applications.
insertApps' :: Cxt -> U.IO Infer -> U.IO Infer
insertApps' cxt act = goInsert' cxt U.=<< act
{-# inline insertApps' #-}

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insertApps :: Cxt -> U.IO Infer -> U.IO Infer
insertApps cxt act = act U.>>= \case
  res@(Infer (Lam _ Impl _) _ _) -> U.pure res
  res                            -> insertApps' cxt (U.pure res)
{-# inline insertApps #-}

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertAppUntilName :: P.Tm -> Cxt -> Span -> U.IO Infer -> U.IO Infer
insertAppUntilName topT cxt name act = go cxt U.=<< act where
  go cxt (Infer t va fva) = forceFU cxt fva U.>>= \case
    fva@(VPi x Impl a b) -> U.do
      if eqName cxt x (NSpan name) then
        U.pure (Infer t va fva)
      else U.do
        (m, mv) <- freshMeta cxt
        let b' = appCl cxt b mv
        go cxt (Infer (App t m Impl) b' b')
    _ ->
      throw $ NoNamedArgument topT name
{-# inline insertAppUntilName #-}

-- Elaboration
--------------------------------------------------------------------------------

infer :: Cxt -> P.Tm -> U.IO Infer
infer cxt topT = U.do
  debug ["infer", showPTm cxt topT]

  Infer t a fa <- case topT of
    P.Var px -> U.do
      ma <- ST.lookup px (tbl cxt)
      case ma of
        UNothing                  -> throw $ NotInScope px
        UJust (ST.Local x va fva) -> U.do

          debugging U.do
            foo <- U.io $ ST.assocs (tbl cxt)
            debug ["local var", show foo, showSpan (src cxt) px, show x,
                   show $ lvlToIx (lvl cxt) x, show $ lvl cxt]

          U.pure (Infer (LocalVar (lvlToIx (lvl cxt) x)) va fva)

        UJust (ST.Top x _ va fva _ vt) -> U.do

          debugging U.do
            foo <- U.io $ ST.assocs (tbl cxt)
            debug ["top var", show foo, showSpan (src cxt) px, show x]

          U.pure (Infer (TopVar x vt) va fva)

    P.Let _ x ma t u ->
      checkWithAnnot cxt ma t \ ~t ~a ~va ~fva -> U.do
        Infer u vb fvb <- defining cxt x va fva (eval cxt t) \cxt -> infer cxt u
        U.pure (Infer (Let x a t u) vb fvb)

    topT@(P.App t u inf) ->

      U.bind4 (\pure -> case inf of
        P.Named x -> U.do
          Infer t tty ftty <- insertAppUntilName topT cxt x $ infer cxt t
          pure Impl t tty ftty
        P.NoName Impl -> U.do
          Infer t tty ftty <- infer cxt t
          pure Impl t tty ftty
        P.NoName Expl -> U.do
          Infer t tty ftty <- insertApps' cxt $ infer cxt t
          pure Expl t tty ftty)
      \i ~t ~tty ~ftty ->

      U.bind2 (\pure -> forceFU cxt tty U.>>= \case
        VPi x i' a b | i == i'   -> pure a b
                     | otherwise -> impossible
        ftty -> U.do
          a <- snd U.<$> freshMeta cxt
          b <- Closure (env cxt) U.<$> freshMetaUnder cxt i
          let expected = VPi NX i a b
          unify cxt topT tty expected ftty expected
          pure a b)
      \ ~a ~b -> U.do

      u <- check cxt u a
      let b' = appCl cxt b (eval cxt u)
      U.pure (Infer (App t u i) b' b')

    P.Pi _ x i a b -> U.do
      a <- checkType cxt a
      let ~va = eval cxt a
      binding cxt x i va va \cxt _ -> U.do
        b <- checkType cxt b
        U.pure (Infer (Pi (bind x) i a b) VU VU)

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
      Infer t vb _ <- binding cxt x i va va \cxt _ -> insertApps cxt (infer cxt t)
      let ty = VPi (bind x) i va (valToClosure cxt vb)
      U.pure (Infer (Lam (bind x) i t) ty ty)

    P.U _ ->
      U.pure (Infer U VU VU)

    P.Hole _ -> U.do
      (_, va) <- freshMeta cxt
      (t, _ ) <- freshMeta cxt
      U.pure (Infer t va va)

  debug ["inferred", showTm cxt t, showVal cxt a]
  U.pure (Infer t a fa)

-- | Choose between checking and inferring depending on an optional type annotation.
checkWithAnnot :: U.CanIO a => Cxt -> UMaybe P.Tm -> P.Tm
               -> (Tm -> Ty -> VTy -> VTy -> U.IO a) -> U.IO a
checkWithAnnot cxt ma t k = case ma of
  UNothing -> U.do
    Infer t va fva <- insertApps cxt $ infer cxt t
    let a = quote cxt UnfoldNone va
    k t a va fva
  UJust a -> U.do
    a <- checkType cxt a
    let va = eval cxt a
    t <- check cxt t va
    k t a va va
{-# inline checkWithAnnot #-}

-- | Check that a preterm is a type.
checkType :: Cxt -> P.Tm -> U.IO Tm
checkType cxt pt = U.do
  Infer t tty ftty <- infer cxt pt
  forceFU cxt ftty U.>>= \case
    VU         -> U.pure t
    VFlex x sp -> t U.<$ solve cxt pt CSRigid x sp VU
    ftty       -> throw $ UnifyError cxt pt tty VU

check :: Cxt -> P.Tm -> VTy -> U.IO Tm
check cxt topT topA = U.do
  debug ["check", showPTm cxt topT, showVal cxt topA]

  a <- forceFU cxt topA
  case (topT, a) of
    (P.Lam _ x inf ma t, VPi x' i a b)
      | (case inf of P.NoName i' -> i == i'
                     P.Named n   -> eqName cxt x' (NSpan n) && i == Impl) ->

      -- We prefer the user-provided annotation for the unforced binder type
      U.bind1 (\pure -> case ma of
        UNothing -> pure a
        UJust a' -> U.do
          a' <- checkType cxt a'
          let va' = eval cxt a'
          unify cxt topT a va' a va'
          pure va')
      \fa ->
      binding cxt x i a fa \cxt v ->
        Lam (bind x) i U.<$> check cxt t (appCl cxt b v)

    (t, VPi x Impl a b) ->
      inserting cxt x \cxt v -> U.do
        t <- check cxt t (appCl cxt b v)
        U.pure (Lam x Impl t)

    (P.Let _ x ma t u, a') ->
      checkWithAnnot cxt ma t \ ~t ~a ~va ~fva ->
        defining cxt x va fva (eval cxt t) \cxt ->
          Let x a t U.<$> check cxt u a'

    (P.Hole _, a) ->
      fst U.<$> freshMeta cxt

    (topT, fexpected) -> U.do
      Infer t inferred finferred <- insertApps cxt $ infer cxt topT
      unify cxt topT inferred topA finferred fexpected
      U.pure t

checkTopLevel :: SymTable -> MetaCxt -> TopLevel -> P.TopLevel -> U.IO TopLevel
checkTopLevel tbl ms top ptop = case ptop of
  P.Nil ->
    U.pure top
  P.Definition x ma t u -> U.do

    debug ["\nTOP DEF", showSpan (ST.byteString tbl) x]
    let cxt = empty tbl ms top
    checkWithAnnot cxt ma t \ ~t ~a ~va ~fva -> U.do

      let ~vt = E.eval ms ENil t
      ST.insert x (ST.Top (topLen top) a va fva t vt) tbl
      top <- topDefine x a t top
      checkTopLevel tbl ms top u

checkProg :: B.ByteString -> P.TopLevel -> IO (Either Exception (SymTable, TopLevel, MetaCxt))
checkProg src ptop = do
  tbl  <- U.toIO $ ST.new src
  top  <- U.toIO $ newTop (P.topLen ptop)
  ms   <- MC.new
  etop <- U.toIO $ try (checkTopLevel tbl ms top ptop)
  pure $! ((\top -> (tbl, top, ms)) <$> etop)
