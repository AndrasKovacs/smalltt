
module Simplify where

import Control.Exception
import Control.Monad
import qualified Data.Array.Dynamic as AD
import qualified Data.Array.Dynamic.Unlifted as ADU
import qualified Data.Primitive.PrimArray as PA

import Common
import Cxt
import ElabState
import Errors
import Evaluation
import Syntax
import Values

inlineLocal :: VEnv -> Ix -> Either Val Tm
inlineLocal vs topx = go vs topx where
  go (EDef vs v) 0 = Left v
  go (ESkip vs)  0 = Right (LocalVar topx)
  go (EDef vs _) x = go vs (x - 1)
  go (ESkip vs)  x = go vs (x - 1)
  go ENil        x = error "inlineLocal: impossible"

inlineSp :: Lvl -> VEnv -> Tm -> Either Val Tm
inlineSp l vs = go where
  go (MetaVar x)  = case lookupMeta x of
    MESolved _ True t _ -> Left (vEval ENil t)
    _                   -> Right (MetaVar x)
  go (LocalVar x) = inlineLocal vs x
  go (AppI t u)   = either (\v -> Left (vAppI v (vEval vs u)))
                           (\t -> Right (AppI t (inline l vs u)))
                           (go t)
  go (AppE t u)   = either (\v -> Left (vAppE v (vEval vs u)))
                           (\t -> Right (AppE t (inline l vs u)))
                           (go t)
  go t            = Right (inline l vs t)

inline :: Lvl -> VEnv -> Tm -> Tm
inline l vs = \case
  LocalVar x -> either (vQuote l) id (inlineLocal vs x)
  TopVar x   -> TopVar x
  MetaVar x  -> case lookupMeta x of
    MESolved _ True t _ -> vQuote l (vEval ENil t)
    _                   -> MetaVar x
  Let (Named x a) t u -> Let (Named x (inline l vs a)) (inline l vs t) (inline (l + 1) (ESkip vs) u)
  AppI t u   -> either (\v -> vQuote l (vAppI v (vEval vs u)))
                       (\t -> AppI t (inline l vs u))
                       (inlineSp l vs t)
  AppE t u   -> either (\v -> vQuote l (vAppE v (vEval vs u)))
                       (\t -> AppE t (inline l vs u))
                       (inlineSp l vs t)
  Lam ni t   -> Lam ni (inline (l + 1) (ESkip vs) t)
  Fun a b    -> Fun (inline l vs a) (inline l vs b)
  Pi ni a b  -> Pi ni (inline l vs a) (inline (l + 1) (ESkip vs) b)
  U          -> U
  Irrelevant -> Irrelevant

inline0 :: Tm -> Tm
inline0 = inline 0 ENil

-- | Inline metas in the current meta block. We throw error on unsolved metas.
simplifyMetaBlock :: Cxt -> IO ()
simplifyMetaBlock cxt = do
  block     <- ADU.last metas
  blockSize <- AD.size block
  blockIx   <- subtract 1 <$> ADU.size metas

  -- 1. Inline already inlinable metas in block, check for unsolved metas

  -- first pass
  AD.forMIx_ block $ \j -> \case
    MESolved gv inl t pos -> do
      let t' = inline 0 ENil t
      AD.unsafeWrite block j
        -- (MESolved (gvEval 0 ENil ENil t') inl t' pos)
        (MESolved (gvEval 0 ENil ENil t') (isInlinable t') t' pos)
    MEUnsolved p -> do
      updPos p
      throw (TopError cxt (EEUnsolvedMeta (Meta blockIx j)))

  -- second pass (maybe unnecessary?)
  AD.forMIx_ block $ \j -> \case
    MESolved gv inl t pos -> do
      let t' = inline 0 ENil t
      AD.unsafeWrite block j (MESolved (gvEval 0 ENil ENil t') inl t' pos)
    MEUnsolved p -> do
      updPos p
      throw (TopError cxt (EEUnsolvedMeta (Meta blockIx j)))

  -- 2. Mark metas which don't occur in other metas as inlinable
  occurs <- PA.newPrimArray @_ @Int blockSize
  PA.setPrimArray occurs 0 blockSize 0

  let countOccurs :: Tm -> IO ()
      countOccurs = go where
        go = \case
          LocalVar{}          -> pure ()
          TopVar{}            -> pure ()
          MetaVar (Meta i j)  -> when (i == blockIx) $ do
                                   n <- PA.readPrimArray occurs j
                                   PA.writePrimArray occurs j (n + 1)
          Let (Named _ a) t u -> go a >> go t >> go u
          AppI t u            -> go t >> go u
          AppE t u            -> go t >> go u
          Lam _ t             -> go t
          Pi _ a b            -> go a >> go b
          Fun a b             -> go a >> go b
          Irrelevant          -> pure ()
          U                   -> pure ()

  AD.forM_ block $ \case
    MESolved _ _ t _ -> countOccurs t
    _                -> error "simplifyMetaBlock: impossible"

  AD.forMIx_ block $ \j -> \case
    MESolved gv inl t pos -> when (not inl) $ do
      occ <- PA.readPrimArray occurs j
      when (occ == 0) $ AD.write block j (MESolved gv True t pos)
    _ -> error "simplifyMetaBlock: impossible"
