{-# language MagicHash, UnboxedTuples #-}

module Elaboration where

-- import qualified Data.ByteString as B
import GHC.Exts

import Common
import CoreTypes
-- import EnvMask (EnvMask(..))
-- import qualified EnvMask as EM
-- import SymTable (SymTable(..))
-- import MetaCxt (MetaCxt)
-- import qualified MetaCxt  as MC

import qualified SymTable as ST
import ElabCxt

import qualified Presyntax as P
import Exceptions
import Evaluation

{-
--------------------------------------------------------------------------------

data Infer = Infer# (# Tm, VTy #)

pattern Infer :: Tm -> VTy -> Infer
pattern Infer t a <- Infer# (# t, a #) where
  Infer t a = Infer# (# t, a #)

instance RunIO Infer where
  runIO (IO f) = Infer# (runRW# \s -> case f s of (# _, Infer# x #) -> x)
  {-# inline runIO #-}

--------------------------------------------------------------------------------

evalCxt :: Cxt -> Tm -> Val
evalCxt cxt t = eval (mcxt cxt) (env cxt) t
{-# inline evalCxt #-}

forceMTCxt :: Cxt -> Val -> Val
forceMTCxt cxt t = forceMT (mcxt cxt) t
{-# inline forceMTCxt #-}

freshMeta :: Cxt -> VTy -> Tm
freshMeta _ _ = LocalVar 0

infer :: Cxt -> P.Tm -> Infer
infer cxt = \case

  P.Var px -> ST.looked px (tbl cxt)
    (throw Exception)
    (\case
        ST.Top x a va t vt -> Infer (TopVar x vt) va
        ST.Local x va      -> Infer (LocalVar (lvlToIx (lvl cxt) x)) va
    )

  P.Let _ x pma pt pu -> let
    a   = case pma of UNothing -> freshMeta cxt VU
                      UJust pa -> check cxt pa VU
    va  = evalCxt cxt a
    t   = check cxt pt va
    ~vt = evalCxt cxt t
    in defining cxt x va vt \cxt -> infer cxt pu

  P.App pt pu inf -> let
    Infer t va = infer cxt pt
    in case forceMTCxt cxt va of
        VPi x i a b -> let
          u = check cxt pu a
          in Infer (App t u i) (appCl (mcxt cxt) b (evalCxt cxt u))
        _ -> throw Exception

  P.Pi _ P.DontBind i pa pb -> let
    a = check cxt pa VU
    b = check cxt pb VU
    in Infer (Pi (Span (Pos 0) (Pos 0)) i a b) VU

  P.Pi _ (P.Bind x) i pa pb -> let
    a   = check cxt pa VU
    ~va = evalCxt cxt a
    b   = binding cxt x i va \cxt -> check cxt pb VU
    in Infer (Pi x i a b) VU

  P.Lam _ b inf pma pt ->
    uf

  P.U _ ->
    Infer U VU

  P.Hole _ -> let
    va = evalCxt cxt $! freshMeta cxt VU
    t  = freshMeta cxt va
    in Infer t va

check :: Cxt -> P.Tm -> VTy -> Tm
check cxt t a = case (,) $$! t $$! a of
  (P.Lam _ bind inf pma pt, VPi x i a b) -> let
    t = binding cxt x i a \cxt' -> check cxt' pt (appCl (mcxt cxt) b (VLocalVar (lvl cxt) SId))
    in Lam x i t

  (t, a) ->
    uf
-}
