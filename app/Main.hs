
module Main where

import Control.Exception
import Data.Char
import Data.Nullable
import System.IO (hSetBuffering, stdout, BufferMode(..))
import Text.Megaparsec (errorBundlePretty)
import Data.Time.Clock

import qualified Data.Text.Short as ST
import qualified Data.Text.IO as T

import Values
import Common
import Elaboration
import Parser
import Pretty
import Evaluation

--------------------------------------------------------------------------------

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn "smalltt 0.1.0.0"
  putStrLn "enter :? for help"
  loop Null mempty

timed ∷ IO a → IO (a, NominalDiffTime)
timed a = do
  t1 ← getCurrentTime
  res ← a
  t2 ← getCurrentTime
  pure (res, diffUTCTime t2 t1)

load :: Nullable FilePath -> IO NameTable
load Null = do
  putStrLn "No filepath loaded" >> pure mempty
load (Some path) = do
  (ntbl, t) <- timed $
    try (T.readFile path) >>= \case
      Left (e :: SomeException) -> mempty <$ (putStrLn $ displayException e)
      Right file -> case parseFile path file of
        Left e     -> mempty <$ (putStrLn $ errorBundlePretty e)
        Right prog -> try (checkProgram prog) >>= \case
          Left (e :: SomeException) -> mempty <$ (putStrLn $ displayException e)
          Right ntbl -> pure ntbl
  putStrLn ("loaded in " ++ show t)
  pure ntbl

loop :: Nullable FilePath -> NameTable -> IO ()
loop p ntbl = do
  putStr "λ> "
  l <- getLine
  case l of
    ':':'l':rest -> do
      let path = dropWhile isSpace rest
      ntbl <- load (Some path)
      loop (Some path) ntbl
    ':':'r':_ -> do
      load p
      loop p ntbl
    ':':'t':_:name -> do
      try (inferVar (initCxt ntbl) (ST.pack name)) >>= \case
        Left (e :: SomeException) -> do
          putStrLn $ displayException e
        Right (T2 _ (GV ga va)) -> do
          putStrLn $ showTm0 (vQuote 0 va)
      loop p ntbl
    ':':'n':_:name -> do
      try (inferVar (initCxt ntbl) (ST.pack name)) >>= \case
        Left (e :: SomeException) -> do
          putStrLn $ displayException e
        Right (T2 t _) -> do
          (_, t) <- timed (putStrLn $ showTm0 (gQuote 0 $ gEval 0 ENil' ENil' t))
          putStrLn ("evaluated in " ++ show t)
      loop p ntbl
    ':':'e':_ -> do
      putStrLn =<< renderElabOutput
      loop p ntbl
    ':':'q':_ -> pure ()
    ':':'?':_ -> do
      putStrLn ":l <file>    load file"
      putStrLn ":r           reload file"
      putStrLn ":t <name>    show type of definition"
      putStrLn ":n <name>    show normal form of definition"
      putStrLn ":e           show elaborated file"
      putStrLn ":q           quit"
      putStrLn ":?           show this message"
      loop p ntbl
    _ -> do
      putStrLn "Unknown command"
      putStrLn "use :? for help"
      loop p ntbl
