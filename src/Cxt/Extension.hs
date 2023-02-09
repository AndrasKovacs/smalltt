
module Cxt.Extension where

import qualified LvlSet as LS
import qualified SymTable as ST
import qualified TopCxt as Top

import Common
import CoreTypes
import Cxt.Types
import Exceptions
import Presyntax (Bind(..), pattern BEmpty, pattern BSpan)

empty :: Top.Cxt -> Cxt
empty (Top.Cxt lvl info tbl ms frz) =
  Cxt 0 ENil mempty tbl ms (NNil info) frz
{-# inline empty #-}

-- | Add a new bound variable.
binding :: Cxt -> Bind -> Icit -> GTy -> (Cxt -> Val -> IO a) -> IO a
binding (Cxt lvl env mask tbl mcxt ns frz) x i a k = do
  let v     = VLocalVar lvl SId
      mask' = LS.insert lvl mask
      env'  = EDef env v
      lvl'  = lvl + 1
  when (lvl' > maxLocals) $ throw TooManyLocals
  case x of
    BEmpty  -> do
      k (Cxt lvl' env' mask' tbl mcxt (NCons ns NEmpty) frz) v
    BSpan x -> do
      h   <- ST.hash tbl x
      old <- ST.insertWithHash x h (ST.Local lvl a) tbl
      res <- k (Cxt lvl' env' mask' tbl mcxt (NCons ns (NSpan x)) frz) v
      ST.updateWithHash x h old tbl
      pure res
{-# inline binding #-}

-- | Add a new local definition.
defining :: Cxt -> Span -> GTy -> Val -> (Cxt -> IO a) -> IO a
defining (Cxt lvl env mask tbl mcxt ns frz) x a ~vt k = do
  when (lvl >= maxLocals) $ throw $ TooManyLocals
  h   <- ST.hash tbl x
  old <- ST.insertWithHash x h (ST.Local lvl a) tbl
  res <- k (Cxt (lvl + 1) (EDef env vt) mask tbl mcxt (NCons ns (NSpan x)) frz)
  ST.updateWithHash x h old tbl
  pure res
{-# inline defining #-}

-- | Insert a new binder. The binder does not exist in the source file.
inserting :: Cxt -> Name -> (Cxt -> Val -> IO a) -> IO a
inserting (Cxt lvl env mask tbl mcxt ns frz) x k = do
  when (lvl >= maxLocals) $ throw $ TooManyLocals
  let v = VLocalVar lvl SId
  k (Cxt (lvl + 1) (EDef env v) (LS.insert lvl mask) tbl mcxt (NCons ns x) frz) v
{-# inline inserting #-}
