
module TopCxt where

import qualified Data.Array.LM        as ALM
import qualified Data.Array.Dynamic.L as ADL
import GHC.Exts

import qualified Evaluation as E
import qualified SymTable as ST
import qualified MetaCxt as MC
import Common
import CoreTypes

-- | Top-level elaboration context.
data Cxt = Cxt {
  lvl    :: Lvl,         -- ^ Size of context.
  info   :: TopInfo,     -- ^ Span, term, type for each definition.
  tbl    :: ST.SymTable, -- ^ Symbol table.
  mcxt   :: MetaCxt,     -- ^ Metacontext.
  frz    :: MetaVar      -- ^ All metavars smaller than frz are frozen.
  }

type WithCxt a =
  (?lvl :: Lvl)          =>
  (?info :: TopInfo)     =>
  (?tbl  :: ST.SymTable) =>
  (?mcxt :: MetaCxt)     =>
  (?frz  :: MetaVar)     =>
  a

-- | New top context from a source file and the number of top defs.
new :: Src -> Int -> WithCxt (IO a) -> IO a
new src len act = do
  info   <- ALM.new len (error "undefined top entry")
  tbl    <- ST.new src
  ms     <- ADL.empty
  let ?info = info
      ?tbl  = tbl
      ?mcxt = ms
      ?lvl  = 0
      ?frz  = 0
  act
{-# inline new #-}

cxt :: WithCxt Cxt
cxt = Cxt ?lvl ?info ?tbl ?mcxt ?frz
{-# inline cxt #-}

-- | Extend cxt with a top-level definition. Updates destructively. Freezes all
--   current metavariables.
define :: Span -> Ty -> GTy -> Tm -> WithCxt (IO a) -> WithCxt (IO a)
define x a ga t act = do
  let ~vt = E.eval ?mcxt ENil t
  frz <- coerce <$> MC.size ?mcxt
  ALM.write ?info (coerce ?lvl) (TopEntry x a t frz)
  ST.insert x (ST.Top a ga t (TopVar ?lvl (coerce vt))) ?tbl
  let lvl' = ?lvl + 1
  let ?lvl = lvl'
      ?frz = frz
  act
{-# inline define #-}
