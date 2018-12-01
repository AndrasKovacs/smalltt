
module Main where

import Control.Exception
import Data.Char
import Data.Time.Clock
import System.IO (hSetBuffering, stdout, BufferMode(..))
import System.Mem
import Text.Megaparsec (errorBundlePretty)

import qualified Data.Text.Short as ST
import qualified Data.Text.IO as T

import Common
import Elaboration
import Evaluation
import Parser
import Pretty
import Values

--------------------------------------------------------------------------------

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn "smalltt 0.1.0.0"
  putStrLn "enter :? for help"
  loop Nothing mempty

timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1 <- getCurrentTime
  res <- a
  t2 <- getCurrentTime
  pure (res, diffUTCTime t2 t1)

load :: Maybe FilePath -> IO NameTable
load Nothing = do
  putStrLn "No filepath loaded" >> pure mempty
load (Just path) = do
  (ntbl, ttotal) <- timed $
    try (T.readFile path) >>= \case
      Left (e :: SomeException) -> mempty <$ (putStrLn $ displayException e)
      Right file -> case parseFile path file of
        Left e     -> mempty <$ (putStrLn $ errorBundlePretty e)
        Right prog -> do
            (ntbl, telab) <- timed $ try (checkProgram prog) >>= \case
              Left (e :: SomeException) -> mempty <$ (putStrLn $ displayException e)
              Right ntbl -> pure ntbl
            putStrLn ("elaborated in " ++ show telab)
            pure ntbl

  putStrLn ("total load time: " ++ show ttotal)
  pure ntbl

loop :: Maybe FilePath -> NameTable -> IO ()
loop p ntbl = do
  putStr "λ> "
  l <- getLine
  case l of
    ':':'l':rest -> do
      let path = dropWhile isSpace rest
      ntbl <- load (Just path)
      performGC
      loop (Just path) ntbl
    ':':'r':_ -> do
      ntbl <- load p
      performGC
      loop p ntbl
    ':':'t':_:name -> do
      try (inferVar (initCxt ntbl) (ST.pack name)) >>= \case
        Left (e :: SomeException) -> do
          putStrLn $ displayException e
        Right (T2 _ (GV ga va)) -> do
          putStrLn $ showTm0 (vQuote 0 va)
      loop p ntbl
    ':':'n':'t':_:name -> do
      try (inferVar (initCxt ntbl) (ST.pack name)) >>= \case
        Left (e :: SomeException) -> do
          putStrLn $ displayException e
        Right (T2 _ (GV ga va)) -> do
          putStrLn $ showTm0 (gQuote 0 ga)
      loop p ntbl
    ':':'n':_:name -> do
      try (inferVar (initCxt ntbl) (ST.pack name)) >>= \case
        Left (e :: SomeException) -> do
          putStrLn $ displayException e
        Right (T2 t _) -> do
          (_, t) <- timed (putStrLn $ showTm0 (gQuote 0 $ gEval 0 ENil' ENil' t))
          putStrLn ("evaluated in " ++ show t)
      performGC
      loop p ntbl
    ':':'e':_ -> do
      putStrLn =<< renderElabOutput
      loop p ntbl
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
      loop p ntbl
    _ -> do
      putStrLn "Unknown command"
      putStrLn "use :? for help"
      loop p ntbl
