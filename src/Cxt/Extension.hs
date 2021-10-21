{-# language UnboxedTuples #-}

module Cxt.Extension where

import Cxt.Types
import qualified EnvMask as EM
import qualified SymTable as ST
import qualified UIO as U

import Common
import CoreTypes
import MetaCxt (MetaCxt)
import SymTable (SymTable(..))
import Exceptions

empty :: SymTable -> MetaCxt -> TopLevel -> Cxt
empty tbl ms top = Cxt 0 ENil EM.empty tbl ms (NNil top)
{-# inline empty #-}

binding :: U.CanIO a => Cxt -> Bind -> Icit -> VTy -> (Cxt -> Val -> U.IO a) -> U.IO a
binding (Cxt lvl env mask tbl mcxt ns) x i ~va k = let
  v     = VLocalVar lvl SId
  mask' = EM.insert lvl i mask
  env'  = EDef env v
  lvl'  = lvl + 1
  in case x of
    BEmpty  -> U.do
      k (Cxt lvl' env' mask' tbl mcxt (NCons ns NEmpty)) v
    BSpan x -> U.do
      U.when (lvl >= 64) $ throw TooManyLocals
      h   <- ST.hash tbl x
      old <- ST.insertWithHash x h (ST.Local lvl va) tbl
      res <- k (Cxt lvl' env' mask' tbl mcxt (NCons ns (NSpan x))) v
      ST.updateWithHash x h old tbl
      U.pure res
{-# inline binding #-}

defining :: U.CanIO a => Cxt -> Span -> VTy -> Val -> (Cxt -> U.IO a) -> U.IO a
defining (Cxt lvl env mask tbl mcxt ns) x ~va ~vt k = U.do
  U.when (lvl >= 64) $ throw $ TooManyLocals
  h   <- ST.hash tbl x
  old <- ST.insertWithHash x h (ST.Local lvl va) tbl
  res <- k (Cxt (lvl + 1) (EDef env vt) mask tbl mcxt (NCons ns (NSpan x)))
  ST.updateWithHash x h old tbl
  U.pure res
{-# inline defining #-}

inserting :: Cxt -> VTy -> (Cxt -> Val -> U.IO a) -> U.IO a
inserting (Cxt lvl env mask tbl mcxt ns) ~va k =
  let v = VLocalVar lvl SId
  in k (Cxt (lvl + 1) (EDef env v) (EM.insert lvl Impl mask) tbl mcxt (NCons ns NX)) v
{-# inline inserting #-}
