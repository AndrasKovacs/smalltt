
module Cxt where

import Data.HashMap.Strict (HashMap)
import Text.Megaparsec.Pos
import Text.Printf
import Values
import qualified Data.HashMap.Strict as HM
import qualified Data.Text.Short as T

import Common

-- | Inserted names come from inserting implicit binders during elaboration.
--   Other names come from user input.
data NameOrigin = NOInserted | NOSource deriving Show
data NameInfo = NITop SourcePos Lvl | NILocal SourcePos NameOrigin Lvl

instance Show NameInfo where
  show (NITop _ i)     = "NITop " ++ show i
  show (NILocal _ o i) = printf "NILocal %s %d" (show o) i

-- | Reverse map from names to all de Bruijn levels with the keyed name.
--   Indices are sorted, the lowest in scope is the first element.  We also keep
--   track of source positions of binders. We only use this structure for name
--   lookup during elaboration.
type NameTable = HashMap Name [NameInfo]
data BoundIndices = BINil | BISnoc BoundIndices Lvl

-- | Local elaboration context.
data Cxt = Cxt {
  _size      :: Int,   -- ^ Number of local entries.
  _vVals     :: VEnv,  -- ^ Local values of definitions.
  _types     :: [VTy], -- ^ Types of entries.

  -- | Structure for getting indices for names during elaboration.
  _nameTable :: NameTable,

  -- | Structure for getting names for local indices during unification. Only
  --   used for getting informative (source-originating) names for binders in
  --   meta solutions.
  _names        :: Names,
  -- | List of local bound indices. Used for making spines for fresh metas.
  _boundIndices :: BoundIndices
  }

addName :: Name -> NameInfo -> NameTable -> NameTable
addName n ni ntbl = if T.null n
  then ntbl
  else HM.alter (Just . maybe [ni] (ni:)) n ntbl
{-# inline addName #-}

-- | Initial local context.
initCxt :: NameTable -> Cxt
initCxt ntbl = Cxt 0 ENil [] ntbl NNil BINil

-- | Add a bound variable to local context.
localBind :: Posed Name -> NameOrigin -> VTy -> Cxt -> Cxt
localBind x origin gvty (Cxt l vs tys ninf ns bis) =
  Cxt (l + 1)
      (ESkip vs)
      (gvty:tys)
      (addName (unPosed x) (NILocal (posOf x) origin l) ninf)
      (NSnoc ns (unPosed x))
      (BISnoc bis l)

-- | Add a new definition to local context.
localDefine :: Posed Name -> Val -> VTy -> Cxt -> Cxt
localDefine x v gvty (Cxt l vs tys ninf ns bis) =
  Cxt (l + 1)
      (EDef vs v)
      (gvty:tys)
      (addName (unPosed x) (NILocal (posOf x) NOSource l) ninf)
      (NSnoc ns (unPosed x))
      bis

localBindSrc, localBindIns :: Posed Name -> VTy -> Cxt -> Cxt
localBindSrc x = localBind x NOSource
localBindIns x = localBind x NOInserted
