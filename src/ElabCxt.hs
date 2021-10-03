
module ElabCxt where

import qualified Data.ByteString as B

import Common
import CoreTypes
import EnvMask (EnvMask(..))
import qualified EnvMask as EM
import SymTable (SymTable(..))
import qualified SymTable as ST
import MetaCxt (MetaCxt)
import qualified MetaCxt  as MC

data Cxt = Cxt {
    lvl     :: Lvl
  , env     :: Env
  , mask    :: {-# unpack #-} EnvMask
  , tbl     :: SymTable
  , mcxt    :: MetaCxt
  }

empty :: B.ByteString -> IO Cxt
empty src = Cxt 0 ENil EM.empty <$!> ST.new src <*!> MC.new

-- TODO: *very* dodgy runIO below!!!
-- check that it works, otherwise do some other workaround for IO result unboxing!
-- TODO: write symtable combined insert/delete which does not recompute hash!

binding :: Cxt -> Span -> Icit -> VTy -> (Cxt -> a) -> a
binding (Cxt lvl env mask tbl mcxt) x i ~va k = runIO do
  ST.insert x (ST.Local lvl va) tbl
  let res = k (Cxt (lvl + 1) (EDef env (VLocalVar lvl SId)) (EM.insert lvl i mask) tbl mcxt)
  ST.delete x tbl
  pure res
{-# inline binding #-}

defining :: Cxt -> Span -> VTy -> Val -> (Cxt -> a) -> a
defining (Cxt lvl env mask tbl mcxt) x ~va ~vt k = runIO do
  ST.insert x (ST.Local lvl va) tbl
  let res = k (Cxt (lvl + 1) (EDef env vt) mask tbl mcxt)
  ST.delete x tbl
  pure res
{-# inline defining #-}

inserting :: Cxt -> Span -> VTy -> (Cxt -> a) -> a
inserting (Cxt lvl env mask tbl mcxt) x ~va k =
  k (Cxt (lvl + 1) (EDef env (VLocalVar lvl SId)) (EM.insert lvl Impl mask) tbl mcxt)
{-# inline inserting #-}
