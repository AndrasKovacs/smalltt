
module Cxt.Types where

import Common
import CoreTypes
import LvlSet (LvlSet(..))
import SymTable (SymTable(..))

data Cxt = Cxt {
    lvl     :: Lvl       -- ^ Size of local context.
  , env     :: Env       -- ^ Local evaluation environment.
  , mask    :: LvlSet    -- ^ Masks bound vars in local context.
  , tbl     :: SymTable  -- ^ Symbol table for all names (top + local).
  , mcxt    :: MetaCxt   -- ^ Metacontext.
  , names   :: Names     -- ^ Compact list of local names, for error printing.
  , frz     :: MetaVar   -- ^ Every metavar smaller than frz is frozen.
  }

instance Show Cxt where
  show _ = "<cxt>"
