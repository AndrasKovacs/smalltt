
module Elaboration where

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Lens.Micro.Platform
import Text.Megaparsec.Pos
import Data.IORef

import Common
import Evaluation
import Syntax
import Values


-- Local elaboration context
--------------------------------------------------------------------------------

-- | Inserted names come from inserting implicit binders during elaboration.
--   Other names come from user input.
data NameOrigin = NOInserted | NOSource

-- | Reverse map from names to all de Bruijn levels with the keyed name.
--   Indices are sorted, the lowest in scope is the first element.
--   We also keep track of source positions of binders.
type Naming = HashMap Name [T3 NameOrigin SourcePos Ix]

-- | Local elaboration context.
data Cxt = Cxt {
  _depth  :: Int,
  _gVals  :: GEnv,
  _vVals  :: VEnv,
  _gTypes :: Env GTy,
  _vTypes :: Env VTy,
  _naming :: Naming
  }
makeLenses ''Cxt


recordName :: Ix -> Posed Name -> NameOrigin -> Naming -> Naming
recordName d (T2 p x) origin ns =
  HM.alter (Just . maybe [T3 origin p d] ((:) (T3 origin p d))) x ns
{-# inline recordName #-}

-- | Empty local context.
cnil :: Cxt
cnil = Cxt 0 ENil' ENil' ENil ENil mempty

-- | Add a bound variable to local context.
bind :: Posed Name -> NameOrigin -> GVTy -> Cxt -> Cxt
bind x origin (GV gty vty) (Cxt d gs vs gtys vtys ns) =
  Cxt (d + 1)
      (ESnoc' gs Nothing)
      (ESnoc' vs Nothing)
      (ESnoc gtys gty)
      (ESnoc vtys vty)
      (recordName d x origin ns)

-- | Add a new definition to local context.
define :: Posed Name -> GV -> GVTy -> Cxt -> Cxt
define x (GV g v) (GV gty vty) (Cxt d gs vs gtys vtys ns) =
  Cxt (d + 1)
      (ESnoc' gs (Just g))
      (ESnoc' vs (Just v))
      (ESnoc gtys gty)
      (ESnoc vtys vty)
      (recordName d x NOSource ns)

bindSrc, bindIns :: Posed Name -> GVTy -> Cxt -> Cxt
bindSrc x = bind x NOSource
bindIns x = bind x NOInserted


-- Unification
--------------------------------------------------------------------------------

{-
Currently, we don't track meta types, hence don't do pruning on metas at all.


Two basic operations: conversion, scope check.

Conversion:
  1. Check local conversion; track rigidity of conversion context, solve
     metas in rigid context but return "dunno" when encountering meta
     equations in flex context. Local conversion could gather additional
     info, for example whether the sides are meta-ground.

  2. If local conversion returns "dunno", do full conversion. If
     local conversion says both sides are meta-ground, do fast non-glued
     full evaluation instead of glued evaluation.

Scope check:
  1. Do scope check on local value. While doing this, build meta solution
     candidate as a Tm. If scope check succeeds, return this candidate.

     Note that illegal variable occurrences are possible in the eventual
     solution, because we can have e.g. a top level constant function
     applied to illegal local var. Only local vars can occur illegally
     in solutions. In any case, we need to return dummy Irrelevant
     values when we hit illegal vars during evaluation.

     Note the shortcuts in scope check:
       - Top-level definitions never unfold to illegal occurrences, because
         they are in the scope of all active metas.
       - Solved metas from previous top-level groups likewise never unfold
         to illegal occurrences, because their solutions can't depend on any
         currently active meta, because of FREEZING.
       - (Of course any previous meta or definition can be applied to illegal
          vars and may or may not beta-reduce to illegal values.)

  2. If local scope check fails, keep the solution candidate, and do full
     scope check. If full check succeeds, still return the local solution
     candidate.

-}

type Ren = HashMap Int Ix

type Rigidity = Bool
pattern Flex, Rigid :: Rigidity
pattern Flex  = True
pattern Rigid = False
{-# complete Flex, Rigid #-}

data Perhaps = Yes | Dunno | No

invert = undefined
rename = undefined

-- TODO: see which one's faster: IO exception, or NullableT IO
-- vUnify :: Cxt -> Val -> Val -> IO ()
-- vUnify cxt v v' =

--   go :: Ix -> Rigidity -> Val -> Val -> IO ()
--   go d
