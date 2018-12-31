
module Main where

import Control.Exception
import Data.Char
import System.IO (hSetBuffering, stdout, BufferMode(..))
import System.Mem
import Text.Megaparsec (errorBundlePretty)
import Text.Megaparsec.Pos

import qualified Data.Text.Short as ST
import qualified Data.Text.IO as T
import qualified Data.Text as T

import Common
import Cxt
import Elaboration
import Evaluation
import ElabState
import Parser
import Pretty
import Values
import Errors

--------------------------------------------------------------------------------

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn "smalltt 0.2.0.0"
  putStrLn "enter :? for help"
  loop Nothing

load :: FilePath -> IO (T.Text, NameTable)
load path = do
  ((file, ntbl), ttotal) <- timed $
    try (T.readFile path) >>= \case
      Left (e :: SomeException) -> mempty <$ (putStrLn $ displayException e)
      Right file -> case parseFile path file of
        Left e     -> mempty <$ (putStrLn $ errorBundlePretty e)
        Right prog -> do
            (ntbl, telab) <- timed $ try (checkProgram prog) >>= \case
              Left (e :: TopError) -> do
                displayTopError file e
                pure mempty
              Right ntbl -> pure ntbl
            putStrLn ("file \"" ++ path ++ "\" elaborated in " ++ show telab)
            pure (file, ntbl)
  putStrLn ("total load time: " ++ show ttotal)
  pure (file, ntbl)


loop :: Maybe (T.Text, FilePath, NameTable) -> IO ()
loop state = do

  let whenLoaded state action =
        maybe (putStrLn "No file loaded" >> loop state) action state

  putStr "λ> "
  l <- getLine
  case l of
    ':':'l':rest -> do
      let path = dropWhile isSpace rest
      (file, ntbl) <- load path
      performGC
      loop (Just (file, path, ntbl))
    ':':'r':_ -> whenLoaded state $ \(file, path, ntbl) -> do
      (file, ntbl) <- load path
      performGC
      loop $ Just (file, path, ntbl)
    ':':'t':_:name -> whenLoaded state $ \(file, path, ntbl) -> do
      updPos (initialPos "interactive")
      try (inferVar (initCxt ntbl) (ST.pack name)) >>= \case
        Left e              -> displayTopError (T.pack name) e
        Right (_, GV ga va) -> putStrLn $ showValMetaless ntbl NNil va
      loop state
    ':':'n':'t':_:name -> whenLoaded state $ \(file, path, ntbl) -> do
      updPos (initialPos "interactive")
      try (inferVar (initCxt ntbl) (ST.pack name)) >>= \case
        Left e              -> displayTopError (T.pack name) e
        Right (_, GV ga va) -> putStrLn $ showGlued ntbl NNil ga
      loop state
    ':':'n':_:name -> whenLoaded state $ \(file, path, ntbl) -> do
      updPos (initialPos "interactive")
      try (inferVar (initCxt ntbl) (ST.pack name)) >>= \case
        Left e -> displayTopError (T.pack name) e
        Right (t, _) -> do
          (nt, time) <- timedPure (gQuote 0 (gEval 0 ENil ENil t))
          putStrLn (showTm0 ntbl nt)
          putStrLn ("evaluated in " ++ show time)
          performGC
      loop state
    ':':'e':_ -> whenLoaded state $ \(file, path, ntbl) -> do
      putStrLn =<< renderElabOutput ntbl
      loop state
    ':':'q':_ -> pure ()
    ':':'?':_ -> do
      putStrLn ":l <file>    load file"
      putStrLn ":r           reload file"
      putStrLn ":t <name>    show elaborated type of definition"
      putStrLn ":nt <name>   show normal elaborated type of definition"
      putStrLn ":n <name>    show normal form of definition"
      putStrLn ":e           show elaborated file"
      putStrLn ":q           quit"
      putStrLn ":?           show this message"
      loop state
    _ -> do
      putStrLn "Unknown command"
      putStrLn "use :? for help"
      loop state
