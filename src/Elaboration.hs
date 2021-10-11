{-# language UnboxedTuples #-}
{-# options_ghc -Wno-orphans #-}

module Elaboration (infer) where

-- import qualified Data.ByteString as B
import GHC.Exts
import Common
import CoreTypes
-- import EnvMask (EnvMask(..))
import qualified EnvMask as EM
-- import SymTable (SymTable(..))
import qualified MetaCxt as MC
import qualified SymTable as ST
import ElabCxt

import qualified Presyntax as P
import Exceptions
import Evaluation

import Unification

import qualified UIO as U
import qualified UIO

import IO

#include "deriveCanIO.h"

--------------------------------------------------------------------------------

-- TODO: separate Name & RawName, SymTable indexed by latter

--------------------------------------------------------------------------------

data Infer = Infer Tm VTy

CAN_IO2(Infer, TupleRep [LiftedRep COMMA LiftedRep], (# Tm, VTy #), Infer x y, CoeInfer)

eqName :: Cxt -> Name -> Name -> Bool
eqName cxt NEmpty    NEmpty     = True
eqName cxt (NSpan x) (NSpan x') = runIO do
  Ptr eob <- ST.eob (tbl cxt)
  pure $! isTrue# (eqSpan# eob x x')
eqName _   _         _          = False

evalCxt :: Cxt -> Tm -> Val
evalCxt cxt t = eval (mcxt cxt) (env cxt) t
{-# inline evalCxt #-}

forceMTCxt :: Cxt -> Val -> Val
forceMTCxt cxt t = forceFU (mcxt cxt) t
{-# inline forceMTCxt #-}

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

unifyCxt :: Cxt -> Val -> Val -> U.IO ()
unifyCxt cxt = unify (mcxt cxt) (lvl cxt) CSRigid
{-# inline unifyCxt #-}

goInsert' :: Cxt -> Infer -> U.IO Infer
goInsert' cxt (Infer t va) = case forceMTCxt cxt va of
  VPi x Impl a b -> U.do
    m <- freshMeta cxt
    let mv = evalCxt cxt m
    goInsert' cxt (Infer (App t m Impl) (appCl (mcxt cxt) b mv))
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
insertUntilName :: Cxt -> Span -> U.IO Infer -> U.IO Infer
insertUntilName cxt name act = go cxt U.=<< act where
  go cxt (Infer t va) = case forceMTCxt cxt va of
    va@(VPi x Impl a b) -> U.do
      if eqName cxt x (NSpan name) then
        U.pure (Infer t va)
      else U.do
        m <- freshMeta cxt
        let mv = evalCxt cxt m
        go cxt (Infer (App t m Impl) (appCl (mcxt cxt) b mv))
    _ ->
      throw Exception
{-# inline insertUntilName #-}

--------------------------------------------------------------------------------

infer :: Cxt -> P.Tm -> U.IO Infer
infer cxt = \case
  P.Var px -> U.do
    ma <- ST.lookup px (tbl cxt)
    case ma of
      UNothing                   -> throw Exception
      UJust (ST.Local x va)      -> U.pure (Infer (LocalVar (lvlToIx (lvl cxt) x)) va)
      UJust (ST.Top x _ va _ vt) -> U.pure (Infer (TopVar x vt) va)

  P.Let _ x ma t u -> U.do
      a <- checkAnnot cxt ma
      let ~va = evalCxt cxt a
      t <- check cxt t va
      let ~vt = evalCxt cxt t
      Infer u vb <- defining cxt (NSpan x) va vt \cxt -> infer cxt u
      U.pure (Infer (Let x a t u) vb)

  P.App t u inf ->

    U.bind3 (\pure -> case inf of
      P.Named x -> U.do
        Infer t tty <- insertUntilName cxt x $ infer cxt t
        pure Impl t tty
      P.NoName Impl -> U.do
        Infer t tty <- infer cxt t
        pure Impl t tty
      P.NoName Expl -> U.do
        Infer t tty <- insert' cxt $ infer cxt t
        pure Expl t tty)
    \i t tty ->

    U.bind2 (\pure -> case forceMTCxt cxt tty of
      VPi x i' a b | i == i'   -> pure a b
                   | otherwise -> undefined
      tty -> U.do
        a <- evalCxt cxt U.<$> freshMeta cxt
        b <- Closure (env cxt) U.<$> freshMeta1 cxt i
        unifyCxt cxt tty (VPi NEmpty i a b)
        pure a b)
    \a b -> U.do

    u <- check cxt u a
    U.pure (Infer (App t u i) (appCl (mcxt cxt) b (evalCxt cxt u)))

  P.Pi _ x i a b -> U.do
    a <- check cxt a VU
    let ~va = evalCxt cxt a
    b <- binding cxt x i va \cxt _ -> check cxt b VU
    U.pure (Infer (Pi x i a b) VU)

  P.Lam _ b inf ma t ->
    uf

  P.U _ ->
    U.pure $ Infer U VU

  P.Hole _ -> U.do
    va <- evalCxt cxt U.<$> freshMeta cxt
    t  <- freshMeta cxt
    U.pure $ Infer t va

checkAnnot :: Cxt -> UMaybe P.Tm -> U.IO Tm
checkAnnot cxt = \case
  UNothing -> freshMeta cxt
  UJust a  -> check cxt a VU
{-# inline checkAnnot #-}

check :: Cxt -> P.Tm -> VTy -> U.IO Tm
check cxt t a = case (,) $$! t $$! a of
  (P.Lam _ x inf ma t, VPi x' i a b)
    | (case inf of P.NoName i' -> i == i'
                   P.Named n   -> eqName cxt x' (NSpan n) && i == Impl) -> U.do
    case ma of
      UNothing -> U.pure ()
      UJust a' -> U.do
        a' <- check cxt a' VU
        unifyCxt cxt a (evalCxt cxt a')
    t <- binding cxt x i a \cxt v -> check cxt t (appCl (mcxt cxt) b v)
    U.pure (Lam x i t)

  (t, VPi x Impl a b) -> U.do
    t <- inserting cxt a \cxt _ -> check cxt t a
    U.pure (Lam x Impl t)

  (P.Let _ x ma t u, a') -> U.do
    a <- checkAnnot cxt ma
    let ~va = evalCxt cxt a
    t <- check cxt t va
    let ~vt = evalCxt cxt t
    u <- defining cxt (NSpan x) va vt \cxt -> check cxt u a'
    U.pure (Let x a t u)

  (P.Hole _, a) ->
    freshMeta cxt

  (t, expected) -> U.do
    Infer t inferred <- insert cxt $ infer cxt t
    unifyCxt cxt inferred expected
    U.pure t
