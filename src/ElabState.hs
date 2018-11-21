
module ElabState where

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

data TopEntry = TEntry {
  _entryName  :: {-# unpack #-} (Posed Name),
  _entryDef   :: EntryDef,
  _entryTy    :: {-# unpack #-} GV,
  _entryMetas :: Array (Nullable GV)
  }

makeLenses ''TopEntry
type TopState = Array TopEntry

topState :: TopState
topState = runIO A.empty
{-# noinline topState #-}

lookupMeta :: MetaIx -> Nullable GV
lookupMeta (MetaIx i j) = runIO $ do
  entry <- A.read topState i
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

--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  A.clear topState
  writeIORef currPos (initialPos "")
