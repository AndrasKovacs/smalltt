
module Unification where

import Common
import CoreTypes
-- import Evaluation
import MetaCxt
import qualified UIO as U

import qualified Data.Array.FI as AFI

--------------------------------------------------------------------------------

data PartialRenaming = PRen {
    dom  :: Lvl
  , cod  :: Lvl
  , ren  :: AFI.Array Lvl
  }

lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) = PRen (dom + 1) (cod + 1) ren
{-# inline lift #-}

unify :: MetaCxt -> Lvl -> Val -> Val -> U.IO ()
unify ms l t t' = uf
