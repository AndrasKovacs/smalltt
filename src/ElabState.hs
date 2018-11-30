
module ElabState where

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

data EntryTy = EntryTy Tm {-# unpack #-} GV

data TopEntry = TopEntry {
  _entryName  :: {-# unpack #-} (Posed Name),
  _entryDef   :: EntryDef,
  _entryTy    :: {-# unpack #-} EntryTy
  }

top :: A.Array TopEntry
top = runIO A.empty
{-# noinline top #-}

isPostulate :: Ix -> Bool
isPostulate x = let e = runIO (A.read top x)
                in case _entryDef e of EDPostulate -> True; _ -> False
{-# inline isPostulate #-}

-- Meta state
--------------------------------------------------------------------------------

data MetaEntry = MEntry Tm {-# unpack #-} GV

metas :: UA.Array (A.Array (Nullable MetaEntry))
metas = runIO UA.empty
{-# noinline metas #-}

lookupMeta :: MetaIx -> Nullable MetaEntry
lookupMeta (MetaIx i j) = runIO $ do
  arr <- UA.read metas i
  res <- A.read arr j
  pure res
{-# inline lookupMeta #-}

-- Source position state
--------------------------------------------------------------------------------

currPos :: IORef SourcePos
currPos = runIO (newIORef (initialPos ""))
{-# noinline currPos #-}

updPos :: Posed a -> Posed a
updPos (T2 p a) = seq (runIO (writeIORef currPos p)) (T2 p a)
{-# inline updPos #-}

reportError ∷ String → a
reportError msg =
  let pos = runIO (readIORef currPos)
  in error (sourcePosPretty pos ++ ":\n\n" ++ msg ++ "\n")

--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  A.clear top
  UA.clear metas
  writeIORef currPos (initialPos "")
