{-# language UnboxedTuples #-}

module Elaboration where

-- import qualified Data.ByteString as B
import GHC.Exts
import Common
import CoreTypes
-- import EnvMask (EnvMask(..))
-- import qualified EnvMask as EM
-- import SymTable (SymTable(..))

import qualified MetaCxt as MC

import qualified SymTable as ST
import ElabCxt

import qualified Presyntax as P
import Exceptions
import Evaluation

import Unification

import qualified UIO as U

import IO

--------------------------------------------------------------------------------
-- TODO:
--  - hammer out symtable operations
--    - general insert: takes UMaybe entry, deletes if UNothing, return UMaybe entry of the
--      entry which is already in table
--      (may also take hash, so that we don't recompute!)
--  - remorselessly add CanIO boilerplate everywhere! Otherwise we really don't get unboxing.

--------------------------------------------------------------------------------

data Infer = Infer Tm VTy

eqName :: Cxt -> Name -> Name -> Bool
eqName cxt NEmpty    NEmpty     = True
eqName cxt (NSpan x) (NSpan x') = runIO do
  Ptr eob <- ST.eob (tbl cxt)
  pure $! eqSpan# eob x x'
eqName _ _ _ = False

evalCxt :: Cxt -> Tm -> Val
evalCxt cxt t = eval (mcxt cxt) (env cxt) t
{-# inline evalCxt #-}

forceMTCxt :: Cxt -> Val -> Val
forceMTCxt cxt t = forceMT (mcxt cxt) t
{-# inline forceMTCxt #-}

freshMeta :: Cxt -> U.IO Tm
freshMeta cxt = U.do
  x <- MC.fresh (mcxt cxt)
  U.pure (InsertedMeta (coerce x) (mask cxt))

-- fresh meta under extra binder
freshMeta1 :: Cxt -> U.IO Tm
freshMeta1 = uf

unifyCxt :: Cxt -> Val -> Val -> U.IO ()
unifyCxt cxt = unify (mcxt cxt) (lvl cxt)
{-# inline unifyCxt #-}

insert' :: Cxt -> U.IO Infer -> U.IO Infer
insert' = uf

insert :: Cxt -> U.IO Infer -> U.IO Infer
insert cxt act = act U.>>= \case
  res@(Infer (Lam _ Impl _) _) -> U.pure res
  res                          -> insert' cxt (U.pure res)

insertUntilName :: Cxt -> Span -> U.IO Infer -> U.IO Infer
insertUntilName cxt x act = uf

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
    a <- case ma of UNothing -> freshMeta cxt
                    UJust a  -> check cxt a VU
    let ~va = evalCxt cxt a
    t <- check cxt t va
    let ~vt = evalCxt cxt t
    Infer u vb <- defining cxt (NSpan x) va vt \cxt -> infer cxt u
    U.pure (Infer (Let x a t u) vb)

  -- dodgy!
  P.App t u inf -> U.io do
    (!i, !t, !tty) <- case inf of
      P.Named x -> do
        Infer t tty <- U.toIO $ insertUntilName cxt x $ infer cxt t
        pure (Impl, t, tty)
      P.NoName Impl -> do
        Infer t tty <- U.toIO $ infer cxt t
        pure (Impl, t, tty)
      P.NoName Expl -> do
        Infer t tty <- U.toIO $ insert' cxt $ infer cxt t
        pure (Expl, t, tty)

    (a, b) <- case forceMTCxt cxt tty of
      VPi x i' a b | i == i'   -> pure (a, b)
                   | otherwise -> uf
      tty -> do
        a <- evalCxt cxt <$> U.toIO (freshMeta cxt)
        b <- Closure (env cxt) <$> U.toIO (freshMeta1 cxt)
        U.toIO $ unifyCxt cxt tty (VPi NEmpty i a b)
        pure (a, b)

    u <- U.toIO $ check cxt u a
    pure (Infer (App t u i) (appCl (mcxt cxt) b (evalCxt cxt u)))

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
    a <- case ma of UNothing -> freshMeta cxt
                    UJust a  -> check cxt a VU
    let ~va = evalCxt cxt a
    t <- check cxt t va
    let ~vt = evalCxt cxt t
    u <- defining cxt (NSpan x) va vt \cxt -> check cxt u a'
    U.pure (Let x a t u)

  (P.Hole _, a) ->
    freshMeta cxt

  (t, expected) -> U.do
    Infer t inferred <- insert cxt $ infer cxt t
    uf

-- boilerplate
--------------------------------------------------------------------------------

type instance U.RepRep Infer = TupleRep [ LiftedRep, LiftedRep ]
type family CoeInfer (x :: TYPE (TupleRep [ LiftedRep, LiftedRep ])) :: TYPE (U.RepRep Infer) where
  CoeInfer x = x
type instance U.Rep Infer = CoeInfer (# Tm, VTy #)

instance U.CanIO Infer where
  bind  :: forall r (b :: TYPE r). (U.RW -> (# U.RW, (# Tm, VTy #) #))
           -> (Infer -> U.RW -> (# U.RW, b #)) -> U.RW -> (# U.RW, b #)
  bind f g s = case f s of (# s, (# x, y #) #) -> g (Infer x y) s
  {-# inline bind #-}

  pure# :: Infer -> U.RW -> (# U.RW, (# Tm, VTy #) #)
  pure# (Infer x y) s = (# s, (# x, y #) #)
  {-# inline pure# #-}
