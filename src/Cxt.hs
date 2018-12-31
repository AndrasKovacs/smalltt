

module Cxt where

import qualified Data.Text.Short as T
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Common
import Values

-- | Reverse map from names to all de Bruijn levels with the keyed name.
--   Indices are sorted, the lowest in scope is the first element.  We also keep
--   track of source positions of binders. We only use this structure for name
--   lookup during elaboration.
data NameTableEntry = NTETop Lvl | NTELocal Lvl
type NameTable = HashMap Name NameTableEntry

data BoundIndices
  = BINil
  | BILocal BoundIndices Lvl
  | BIRule BoundIndices Lvl

-- | Local elaboration context.
data Cxt = Cxt {
  _nameTable :: NameTable,
  _types     :: [GVTy],

  -- The fields below all exist basically for performance reasons.
  -- We need separate value environments, because otherwise we would need
  -- to unzip the values from _localEntries every time we want to evaluate
  -- something. Likewise for _names. _boundIndices lets us skip filtering out
  -- bound vars from _localEntries on every fresh meta creation.

  _size    :: Int,  -- ^ Number of local entries.
  _gEnv    :: GEnv, -- ^ Glued values of definitions.
  _vEnv    :: VEnv, -- ^ Local values of definitions.

  -- | Structure for getting names for local indices during unification. Only
  --   used for getting informative (source-originating) names for binders in
  --   meta solutions.
  _names   :: Names,

  -- | List of local bound indices. Used for making spines for fresh metas.
  _boundIndices :: BoundIndices
  }

addName :: Name -> NameTableEntry -> NameTable -> NameTable
addName n e ntbl = if T.null n
  then ntbl
  else HM.insert n e ntbl
{-# inline addName #-}

-- | Initial local context.
initCxt :: NameTable -> Cxt
initCxt ntbl = Cxt ntbl [] 0 ENil ENil NNil BINil

-- | Add local bound variable.
bindVar :: Posed Name -> GVTy -> Cxt -> Cxt
bindVar x gvty (Cxt ntbl tys l gs vs ns bis) =
  Cxt (addName (unPosed x) (NTELocal l) ntbl)
      (gvty:tys)
      (l + 1)
      (ESkip gs)
      (ESkip vs)
      (NSnoc ns (unPosed x))
      (BILocal bis l)
{-# inline bindVar #-}

-- | Add local definition.
localDefine :: Posed Name -> GV -> GVTy -> Cxt -> Cxt
localDefine x (GV g v) gvty (Cxt ntbl tys l gs vs ns bis) =
  Cxt (addName (unPosed x) (NTELocal l) ntbl)
      (gvty:tys)
      (l + 1)
      (EDef gs g)
      (EDef vs v)
      (NSnoc ns (unPosed x))
      bis
{-# inline localDefine #-}

-- | Insert a fresh local bound variable.
localInsert :: Posed Name -> GVTy -> Cxt -> Cxt
localInsert x gvty (Cxt ntbl tys l gs vs ns bis) =
  Cxt ntbl
      (gvty:tys)
      (l + 1)
      (ESkip gs)
      (ESkip vs)
      (NSnoc ns (unPosed x))
      (BILocal bis l)
{-# inline localInsert #-}
