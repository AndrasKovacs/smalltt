
module Cxt.Types where

import Common
import CoreTypes
import LvlSet (LvlSet(..))
import MetaCxt (MetaCxt)
import SymTable (SymTable(..))

data Cxt = Cxt {
    lvl     :: Lvl
  , env     :: Env
  , mask    :: LvlSet
  , tbl     :: SymTable
  , mcxt    :: MetaCxt
  , names   :: Names
  }

instance Show Cxt where
  show _ = "<cxt>"
