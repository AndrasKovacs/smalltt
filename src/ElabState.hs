
module ElabState where

import           Data.HashMap.Strict (HashMap)
import           Data.Array.Dynamic (Array)
import qualified Data.Array.Dynamic as A
import Data.Nullable
import Lens.Micro.Platform
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

data MetaEntry = MEntry Tm {-# unpack #-} GV

data TopEntry = TEntry {
  _entryName  :: {-# unpack #-} (Posed Name),
  _entryDef   :: EntryDef,
  _entryTy    :: {-# unpack #-} GV,
  _entryMetas :: Array (Nullable MetaEntry)
  }
makeLenses ''TopEntry

top :: Array TopEntry
top = runIO A.empty
{-# noinline top #-}

lookupMeta :: MetaIx -> Nullable MetaEntry
lookupMeta (MetaIx i j) = runIO $ do
  entry <- A.read top i
  A.read (entry^.entryMetas) j
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


-- Naming state
--------------------------------------------------------------------------------

-- | Inserted names come from inserting implicit binders during elaboration.
--   Other names come from user input.
data NameOrigin = NOInserted | NOSource
data Scope = Top | Local
type NameInfo = T4 Scope SourcePos NameOrigin Ix


-- | Reverse map from names to all de Bruijn levels with the keyed name.
--   Indices are sorted, the lowest in scope is the first element.  We also keep
--   track of source positions of binders. We only use this structure for name
--   lookup during elaboration.
type NameTable = HashMap Name (Env' NameInfo)

nameVars :: IORef NameTable
nameVars = runIO (newIORef mempty)
{-# noinline nameVars #-}

--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  A.clear top
  writeIORef currPos (initialPos "")
  writeIORef nameVars mempty
