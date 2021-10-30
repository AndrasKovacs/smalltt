{-# language UnboxedTuples #-}

module Cxt.Extension where

import qualified LvlSet as LS
import qualified MetaCxt as MC
import qualified SymTable as ST
import qualified TopCxt as Top
import qualified UIO as U

import Common
import CoreTypes
import Cxt.Types
import Exceptions

empty :: Top.Cxt -> U.IO Cxt
empty (Top.Cxt lvl info vals tbl region ms) = U.do
  frozen <- MC.size ms
  U.pure $ Cxt 0 ENil mempty tbl ms vals (NNil info) (coerce frozen)
{-# inline empty #-}

binding :: U.CanIO a => Cxt -> Bind -> Icit -> GTy -> (Cxt -> Val -> U.IO a) -> U.IO a
binding (Cxt lvl env mask tbl mcxt vals ns frz) x i a k = let
  v     = VLocalVar lvl SId
  mask' = LS.insert lvl mask
  env'  = EDef env v
  lvl'  = lvl + 1
  in case x of
    BEmpty  -> U.do
      k (Cxt lvl' env' mask' tbl mcxt vals (NCons ns NEmpty) frz) v
    BSpan x -> U.do
      U.when (lvl >= 64) $ throw TooManyLocals
      h   <- ST.hash tbl x
      old <- ST.insertWithHash x h (ST.Local lvl a) tbl
      res <- k (Cxt lvl' env' mask' tbl mcxt vals (NCons ns (NSpan x)) frz) v
      ST.updateWithHash x h old tbl
      U.pure res
{-# inline binding #-}

defining :: U.CanIO a => Cxt -> Span -> GTy -> Val -> (Cxt -> U.IO a) -> U.IO a
defining (Cxt lvl env mask tbl mcxt vals ns frz) x a ~vt k = U.do
  U.when (lvl >= maxLocals) $ throw $ TooManyLocals
  h   <- ST.hash tbl x
  old <- ST.insertWithHash x h (ST.Local lvl a) tbl
  res <- k (Cxt (lvl + 1) (EDef env vt) mask tbl mcxt vals (NCons ns (NSpan x)) frz)
  ST.updateWithHash x h old tbl
  U.pure res
{-# inline defining #-}

inserting :: Cxt -> Name -> (Cxt -> Val -> U.IO a) -> U.IO a
inserting (Cxt lvl env mask tbl mcxt vals ns frz) x k =
  let v = VLocalVar lvl SId
  in k (Cxt (lvl + 1) (EDef env v) (LS.insert lvl mask) tbl mcxt vals (NCons ns x) frz) v
{-# inline inserting #-}
