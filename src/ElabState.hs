
module ElabState where

import qualified Data.Ref.F as RF
import qualified Data.Ref.U as RU
import IO

import qualified UIO as U
import Region
import Common

frozen :: RF.Ref MetaVar
frozen = runIO (RF.new 0)
{-# noinline frozen #-}

region :: RU.Ref Region
region = runIO (RU.new =<< U.toIO Region.new)
{-# noinline region #-}

getRegion :: IO Region
getRegion = RU.read region
{-# inline getRegion #-}

resetRegion :: IO ()
resetRegion = do
  r <- U.toIO Region.new
  RU.write region r

getFrozen :: IO MetaVar
getFrozen = RF.read frozen
{-# inline getFrozen #-}

setFrozen :: MetaVar -> IO ()
setFrozen = RF.write frozen
{-# inline setFrozen #-}

reset :: IO ()
reset = resetRegion >> setFrozen 0
