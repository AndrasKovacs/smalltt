
module ElabCxt where

import qualified Data.ByteString as B

import qualified EnvMask as EM
import qualified MetaCxt as MC
import qualified SymTable as ST
import qualified UIO as U

import Common
import CoreTypes
import EnvMask (EnvMask(..))
import MetaCxt (MetaCxt)
import SymTable (SymTable(..))

data Cxt = Cxt {
    lvl     :: Lvl
  , env     :: Env
  , mask    :: {-# unpack #-} EnvMask
  , tbl     :: SymTable
  , mcxt    :: MetaCxt
  }

empty :: B.ByteString -> IO Cxt
empty src = Cxt 0 ENil EM.empty <$> U.toIO (ST.new src) <*> MC.new

-- TODO: compute hashes only once!

binding :: U.CanIO a => Cxt -> Name -> Icit -> VTy -> (Cxt -> Val -> U.IO a) -> U.IO a
binding cxt NEmpty i ~va k = k cxt (VLocalVar (lvl cxt) SId)
binding (Cxt lvl env mask tbl mcxt) (NSpan x) i ~va k = U.do
  let v = VLocalVar lvl SId
  ST.insert x (ST.Local lvl va) tbl
  res <- k (Cxt (lvl + 1) (EDef env v) (EM.insert lvl i mask) tbl mcxt) v
  ST.delete x tbl
  U.pure res
{-# inline binding #-}

defining :: U.CanIO a => Cxt -> Name -> VTy -> Val -> (Cxt -> U.IO a) -> U.IO a
defining cxt NEmpty ~va ~vt k = k cxt
defining (Cxt lvl env mask tbl mcxt) (NSpan x) ~va ~vt k = U.do
  ST.insert x (ST.Local lvl va) tbl
  res <- k (Cxt (lvl + 1) (EDef env vt) mask tbl mcxt)
  ST.delete x tbl
  U.pure res
{-# inline defining #-}

inserting :: Cxt -> VTy -> (Cxt -> Val -> U.IO a) -> U.IO a
inserting (Cxt lvl env mask tbl mcxt) ~va k =
  let v = VLocalVar lvl SId
  in k (Cxt (lvl + 1) (EDef env v) (EM.insert lvl Impl mask) tbl mcxt) v
{-# inline inserting #-}
