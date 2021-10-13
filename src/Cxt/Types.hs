
module Cxt.Types where

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
  , names   :: Names
  }
