
module ElabState where

import qualified Data.Array.Dynamic as A
import qualified Data.Array.Dynamic.Unlifted as UA
import qualified SmallArray as SA
import Text.Megaparsec.Pos
import Data.IORef

import Common
import Syntax
import Values


-- Top scope state
--------------------------------------------------------------------------------

data RewriteRule = RewriteRule
  Int            -- number of vars
  [Named Ty]     -- vars
  (SA.Array GV)  -- glued LHS spine
  Tm             -- LHS
  Tm             -- RHS

data TopEntry
  -- number of rewrite rules, rules, rule arity, name, type, gvtype
  = TEPostulate Int [RewriteRule] Int (Posed Name) Ty {-# unpack #-} GVTy
  -- value, definition, name, type, gvtype
  | TEDefinition {-# unpack #-} GV Tm (Posed Name) Ty {-# unpack #-} GVTy
  -- only stored here so that we can print rewrite rules in elab output in correct order
  | TERewriteRule {-# unpack #-} RewriteRule

top :: A.Array TopEntry
top = runIO A.empty
{-# noinline top #-}

lookupTopIO :: Lvl -> IO TopEntry
lookupTopIO x = A.read top x
{-# inline lookupTopIO #-}

lookupTop :: Lvl -> TopEntry
lookupTop x = runIO (lookupTopIO x)
{-# inline lookupTop #-}

topRigidity :: Lvl -> Rigidity
topRigidity x = case lookupTop x of
  TEPostulate 0 _ _ _ _ _ -> Rigid
  _                       -> Flex
{-# inline topRigidity #-}

topName :: Lvl -> Posed Name
topName x = case lookupTop x of
  TEDefinition _ _ n _ _  -> n
  TEPostulate _ _ _ n _ _ -> n
  _ -> error "topName: impossible"
{-# inline topName #-}

-- Rewrite LHS substitution
--------------------------------------------------------------------------------

data RewriteEntry = REUnsolved | RESolved {-# unpack #-} GV

emptyLHSArr :: SA.IOArray RewriteEntry
emptyLHSArr = runIO $ SA.new 0 REUnsolved
{-# noinline emptyLHSArr #-}

rewriteLHS :: IORef (SA.IOArray RewriteEntry)
rewriteLHS = runIO $ do
  ref <- newIORef emptyLHSArr
  pure ref
{-# noinline rewriteLHS #-}

lookupRuleVarIO :: Lvl -> IO RewriteEntry
lookupRuleVarIO x = do
  arr <- readIORef rewriteLHS
  SA.read arr x
{-# inline lookupRuleVarIO #-}

lookupRuleVar :: Lvl -> RewriteEntry
lookupRuleVar x = runIO (lookupRuleVarIO x)
{-# inline lookupRuleVar #-}

ruleVarRigidity :: Lvl -> Rigidity
ruleVarRigidity x = case lookupRuleVar x of RESolved{} -> Flex; _ -> Rigid
{-# inline ruleVarRigidity #-}


-- Meta state
--------------------------------------------------------------------------------

data MetaSource = MSSource SourcePos | MSRewrite

data MetaEntry
  = MEUnsolved SourcePos
  | MESolved {-# unpack #-} GV Unfoldable Tm MetaSource

metas :: UA.Array (A.Array MetaEntry)
metas = runIO UA.empty
{-# noinline metas #-}

lookupMetaIO :: Meta -> IO MetaEntry
lookupMetaIO (Meta i j) = do
  arr <- UA.read metas i
  res <- A.read arr j
  pure res
{-# inline lookupMetaIO #-}

lookupMeta :: Meta -> MetaEntry
lookupMeta x = runIO $ do
  lookupMetaIO x
{-# inline lookupMeta #-}

-- | Lookup meta in currently active block
lookupActiveMetaIO :: Lvl -> IO MetaEntry
lookupActiveMetaIO j = do
  block <- UA.last metas
  A.read block j
{-# inline lookupActiveMetaIO #-}

lookupActiveMeta :: Lvl -> MetaEntry
lookupActiveMeta j = runIO (lookupActiveMetaIO j)
{-# inline lookupActiveMeta #-}

metaRigidity :: Meta -> Rigidity
metaRigidity x = case lookupMeta x of MESolved{} -> Flex; _ -> Rigid
{-# inline metaRigidity #-}

writeMeta :: Meta -> MetaEntry -> IO ()
writeMeta (Meta i j) e = do
  arr <- UA.read metas i
  A.write arr j e
{-# inline writeMeta #-}

--------------------------------------------------------------------------------

headRigidity :: Head -> Rigidity
headRigidity = \case
  HMeta  x             -> metaRigidity x
  HTopRigid (Int2 x _) -> topRigidity x
  HRuleVar x           -> ruleVarRigidity x
  HLocal _             -> Rigid
  HTopBlockedOnMeta{}  -> Flex
  HTopUnderapplied{}   -> Flex

{-# inline headRigidity #-}

-- Source position state
--------------------------------------------------------------------------------

currPos :: IORef SourcePos
currPos = runIO (newIORef (initialPos ""))
{-# noinline currPos #-}

updPos :: SourcePos -> IO ()
updPos = writeIORef currPos
{-# inline updPos #-}

getPos :: IO SourcePos
getPos = readIORef currPos
{-# inline getPos #-}

withPos :: SourcePos -> IO a -> IO a
withPos pos ma = do
  p <- getPos
  updPos pos
  a <- ma
  updPos p
  pure a
{-# inline withPos #-}

--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  A.clear top
  UA.clear metas
  writeIORef rewriteLHS emptyLHSArr
  writeIORef currPos (initialPos "")
