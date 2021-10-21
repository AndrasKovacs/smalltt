{-# language UnboxedTuples #-}
{-# options_ghc -Wno-orphans #-}

module Elaboration (checkProg) where

import qualified Data.ByteString as B
import System.Exit
import GHC.Exts

import Common
import CoreTypes
import Cxt
import InCxt
import qualified Evaluation as E
import Exceptions
import Unification
import SymTable (SymTable)
import MetaCxt (MetaCxt)

import qualified EnvMask as EM
import qualified MetaCxt as MC
import qualified Presyntax as P
import qualified SymTable as ST
import qualified UIO
import qualified UIO as U

#include "deriveCanIO.h"

--------------------------------------------------------------------------------


data Infer = Infer Tm VTy

CAN_IO2(Infer, TupleRep [LiftedRep COMMA LiftedRep], (# Tm, VTy #), Infer x y, CoeInfer)


-- TODO: freshMetaVal, freshMetaVal1

-- | Create fresh meta.
freshMeta :: Cxt -> U.IO Tm
freshMeta cxt = U.do
  x <- MC.fresh (mcxt cxt)
  U.pure (InsertedMeta (coerce x) (mask cxt))

-- | Create fresh meta under extra binder.
freshMeta1 :: Cxt -> Icit -> U.IO Tm
freshMeta1 cxt i = U.do
  x <- MC.fresh (mcxt cxt)
  U.pure (InsertedMeta (coerce x) (EM.insert (lvl cxt) i (mask cxt)))

unifyCxt :: Cxt -> P.Tm -> Val -> Val -> U.IO ()
unifyCxt cxt t l r = U.do
  debug ["unify", showVal cxt l, showVal cxt r]
  unify (mcxt cxt) (lvl cxt) CSRigid l r `catch` \case
    UnifyEx _ -> throw $ UnifyError cxt t l r
    _         -> impossible
{-# inline unifyCxt #-}

goInsert' :: Cxt -> Infer -> U.IO Infer
goInsert' cxt (Infer t va) = case forceFU cxt va of
  VPi x Impl a b -> U.do
    m <- freshMeta cxt
    let mv = eval cxt m
    goInsert' cxt (Infer (App t m Impl) (appCl cxt b mv))
  va -> U.pure (Infer t va)

-- | Insert fresh implicit applications.
insert' :: Cxt -> U.IO Infer -> U.IO Infer
insert' cxt act = goInsert' cxt U.=<< act where
{-# inline insert' #-}

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Cxt -> U.IO Infer -> U.IO Infer
insert cxt act = act U.>>= \case
  res@(Infer (Lam _ Impl _) _) -> U.pure res
  res                          -> insert' cxt (U.pure res)
{-# inline insert #-}

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: P.Tm -> Cxt -> Span -> U.IO Infer -> U.IO Infer
insertUntilName topT cxt name act = go cxt U.=<< act where
  go cxt (Infer t va) = case forceFU cxt va of
    va@(VPi x Impl a b) -> U.do
      if eqName cxt x (NSpan name) then
        U.pure (Infer t va)
      else U.do
        m <- freshMeta cxt
        let mv = eval cxt m
        go cxt (Infer (App t m Impl) (appCl cxt b mv))
    _ ->
      throw $ NoNamedArgument topT name
{-# inline insertUntilName #-}

--------------------------------------------------------------------------------

infer :: Cxt -> P.Tm -> U.IO Infer
infer cxt topT = U.do
  debug ["infer", showPTm cxt topT, show (P.span topT)]

  Infer t a <- case topT of
    P.Var px -> U.do
      ma <- ST.lookup px (tbl cxt)
      case ma of
        UNothing                   -> throw $ NotInScope px
        UJust (ST.Local x va)      -> U.do
          foo <- U.io $ ST.assocs (tbl cxt)
          debug ["local var", show foo, showSpan (src cxt) px, show x,
                 show $ lvlToIx (lvl cxt) x, show $ lvl cxt]
          U.pure (Infer (LocalVar (lvlToIx (lvl cxt) x)) va)
        UJust (ST.Top x _ va _ vt) -> U.do
          foo <- U.io $ ST.assocs (tbl cxt)
          debug ["top var", show foo, showSpan (src cxt) px, show x]
          U.pure (Infer (TopVar x vt) va)

    P.Let _ x ma t u -> U.do
        a <- checkAnnot cxt ma
        let ~va = eval cxt a
        t <- check cxt t va
        let ~vt = eval cxt t
        Infer u vb <- defining cxt x va vt \cxt -> infer cxt u
        U.pure (Infer (Let x a t u) vb)

    topT@(P.App t u inf) ->

      U.bind3 (\pure -> case inf of
        P.Named x -> U.do
          Infer t tty <- insertUntilName topT cxt x $ infer cxt t
          pure Impl t tty
        P.NoName Impl -> U.do
          Infer t tty <- infer cxt t
          pure Impl t tty
        P.NoName Expl -> U.do
          Infer t tty <- insert' cxt $ infer cxt t
          pure Expl t tty)
      \i t tty ->

      U.bind2 (\pure -> case forceFU cxt tty of
        VPi x i' a b | i == i'   -> pure a b
                     | otherwise -> undefined
        tty -> U.do
          a <- eval cxt U.<$> freshMeta cxt
          b <- Closure (env cxt) U.<$> freshMeta1 cxt i
          unifyCxt cxt topT tty (VPi NEmpty i a b)
          pure a b)
      \a b -> U.do

      u <- check cxt u a
      U.pure (Infer (App t u i) (appCl cxt b (eval cxt u)))

    P.Pi _ x i a b -> U.do
      a <- check cxt a VU
      binding cxt x i (eval cxt a) \cxt _ -> U.do
        b <- check cxt b VU
        U.pure (Infer (Pi (bind x) i a b) VU)

    P.Lam _ x P.Named{} ma t ->
      throw InferNamedLam

    P.Lam _ x (P.NoName i) ma t -> U.do
      a <- checkAnnot cxt ma
      let ~va = eval cxt a
      Infer t vb <- binding cxt x i va \cxt _ -> insert cxt $ infer cxt t
      U.pure (Infer (Lam (bind x) i t) (VPi (bind x) i va (valToClosure cxt vb)))

    P.U _ ->
      U.pure $ Infer U VU

    P.Hole _ -> U.do
      va <- eval cxt U.<$> freshMeta cxt
      t  <- freshMeta cxt
      U.pure $ Infer t va

  debug ["inferred", showTm cxt t, showVal cxt a, show (P.span topT)]
  U.pure (Infer t a)

checkAnnot :: Cxt -> UMaybe P.Tm -> U.IO Tm
checkAnnot cxt = \case
  UNothing -> freshMeta cxt
  UJust a  -> check cxt a VU
{-# inline checkAnnot #-}

check :: Cxt -> P.Tm -> VTy -> U.IO Tm
check cxt topT a = U.do
  debug ["check", showPTm cxt topT, showVal cxt a]

  case (topT, forceFU cxt a) of
    (P.Lam _ x inf ma t, VPi x' i a b)
      | (case inf of P.NoName i' -> i == i'
                     P.Named n   -> eqName cxt x' (NSpan n) && i == Impl) -> U.do
      case ma of
        UNothing -> U.pure ()
        UJust a' -> U.do
          a' <- check cxt a' VU
          unifyCxt cxt topT a (eval cxt a')

      binding cxt x i a \cxt v ->
        Lam (bind x) i U.<$> check cxt t (appCl cxt b v)

    (t, VPi x Impl a b) ->
      inserting cxt a \cxt _ -> U.do
        t <- check cxt t a
        U.pure (Lam x Impl t)

    (P.Let _ x ma t u, a') -> U.do
      a <- checkAnnot cxt ma
      let ~va = eval cxt a
      t <- check cxt t va
      let ~vt = eval cxt t
      defining cxt x va vt \cxt ->
        Let x a t U.<$> check cxt u a'

    (P.Hole _, a) ->
      freshMeta cxt

    (topT, expected) -> U.do
      Infer t inferred <- insert cxt $ infer cxt topT
      unifyCxt cxt topT inferred expected
      U.pure t

checkTopLevel :: SymTable -> MetaCxt -> TopLevel -> P.TopLevel -> U.IO TopLevel
checkTopLevel tbl ms top ptop = case ptop of
  P.Nil ->
    U.pure top
  P.Definition x ma t u -> U.do
    debug ["TOP DEF", showSpan (ST.byteString tbl) x]
    let cxt = empty tbl ms top
    a <- checkAnnot cxt ma
    let ~va = E.eval ms ENil a
    t <- check cxt t va
    let ~vt = E.eval ms ENil t
    ST.insert x (ST.Top (topLen top) a va t vt) tbl
    top <- topDefine x a t top
    checkTopLevel tbl ms top u

checkProg :: B.ByteString -> P.TopLevel -> IO (MetaCxt, TopLevel)
checkProg src ptop = do
  tbl <- U.toIO $ ST.new src
  ms  <- MC.new
  top <- U.toIO $ newTop (P.topLen ptop)
  top <- U.toIO $ checkTopLevel tbl ms top ptop `catch` \e -> U.do
     U.io $ putStrLn (showException src e)
     U.io exitSuccess
  pure (ms, top)
