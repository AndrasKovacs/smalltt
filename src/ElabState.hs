
module ElabState where

import           Data.HashMap.Strict (HashMap)
import qualified Data.Array.Dynamic as A
import qualified Data.Array.Dynamic.Unlifted as UA
import Data.Nullable
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

data TopEntry = TEntry {
  _entryName  :: {-# unpack #-} (Posed Name),
  _entryDef   :: EntryDef,
  _entryTy    :: {-# unpack #-} GV
  }

top :: A.Array TopEntry
top = runIO A.empty
{-# noinline top #-}

-- Meta state
--------------------------------------------------------------------------------

data MetaEntry = MEntry Tm {-# unpack #-} GV

metas :: UA.Array (A.Array (Nullable MetaEntry))
metas = runIO $ do
  ms <- UA.empty
  UA.push ms =<< A.empty
  pure ms
{-# noinline metas #-}

lookupMeta :: MetaIx -> Nullable MetaEntry
lookupMeta (MetaIx i j) = runIO $ do
  arr <- UA.read metas i
  A.read arr j
{-# inline lookupMeta #-}

-- Source position state
--------------------------------------------------------------------------------

currPos :: IORef SourcePos
currPos = runIO (newIORef (initialPos ""))
{-# noinline currPos #-}

reportError :: String -> a
reportError msg =
  let pos = runIO (readIORef currPos)
  in error (sourcePosPretty pos ++ ":\n\n" ++ msg ++ "\n")

updPos :: Posed a -> Posed a
updPos (T2 p a) = seq (runIO (writeIORef currPos p)) (T2 p a)
{-# inline updPos #-}

-- Naming state
--------------------------------------------------------------------------------

-- | Inserted names come from inserting implicit binders during elaboration.
--   Other names come from user input.
data NameOrigin = NOInserted | NOSource
data NameInfo = NITop SourcePos Ix | NILocal SourcePos NameOrigin Ix

-- | Reverse map from names to all de Bruijn levels with the keyed name.
--   Indices are sorted, the lowest in scope is the first element.  We also keep
--   track of source positions of binders. We only use this structure for name
--   lookup during elaboration.
type NameTable = HashMap Name (Env' NameInfo)

nameTable :: IORef NameTable
nameTable = runIO (newIORef mempty)
{-# noinline nameTable #-}

--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  A.clear top
  UA.clear metas
  UA.push metas =<< A.empty
  writeIORef currPos (initialPos "")
  writeIORef nameTable mempty
