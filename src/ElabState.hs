
module ElabState where

import qualified Data.Array.Dynamic as A
import qualified Data.Array.Dynamic.Unlifted as UA
import Text.Megaparsec.Pos
import Data.IORef

import Common
import Syntax
import Values


-- Top scope state
--------------------------------------------------------------------------------

data EntryDef
  = EDPostulate
  | EDDefinition Tm {-# unpack #-} GV

data EntryTy = EntryTy Tm {-# unpack #-} GV

data TopEntry = TopEntry {
  _entryName  :: {-# unpack #-} (Posed Name),
  _entryDef   :: EntryDef,
  _entryTy    :: {-# unpack #-} EntryTy
  }

top :: A.Array TopEntry
top = runIO A.empty
{-# noinline top #-}

lookupTop :: Lvl -> TopEntry
lookupTop x = runIO (A.unsafeRead top x)
{-# inline lookupTop #-}

topRigidity :: Lvl -> Rigidity
topRigidity x = case _entryDef (lookupTop x) of
  EDPostulate -> Rigid
  _           -> Flex
{-# inline topRigidity #-}

-- Meta state
--------------------------------------------------------------------------------

data MetaEntry = MEUnsolved SourcePos | MESolved SourcePos Tm {-# unpack #-} GV

metas :: UA.Array (A.Array MetaEntry)
metas = runIO UA.empty
{-# noinline metas #-}

lookupMeta :: Meta -> MetaEntry
lookupMeta (Meta i j) = runIO $ do
  arr <- UA.unsafeRead metas i
  res <- A.unsafeRead arr j
  pure res
{-# inline lookupMeta #-}

metaRigidity :: Meta -> Rigidity
metaRigidity x = case lookupMeta x of MESolved{} -> Flex; _ -> Rigid
{-# inline metaRigidity #-}

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

reportError :: String -> IO a
reportError msg = do
  pos <- getPos
  error (sourcePosPretty pos ++ ":\n\n" ++ msg ++ "\n")

--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  A.clear top
  UA.clear metas
  writeIORef currPos (initialPos "")
