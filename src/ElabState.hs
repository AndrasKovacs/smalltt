
module ElabState where

import qualified Data.Ref.F as RF
import IO

import Common

frozen :: RF.Ref MetaVar
frozen = runIO (RF.new 0)
{-# noinline frozen #-}

getFrozen :: IO MetaVar
getFrozen = RF.read frozen
{-# inline getFrozen #-}

setFrozen :: MetaVar -> IO ()
setFrozen = RF.write frozen
{-# inline setFrozen #-}

reset :: IO ()
reset = setFrozen 0
