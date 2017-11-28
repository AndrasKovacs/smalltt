
module Main where

import Data.Char
import Control.Exception
import Text.Megaparsec (parseErrorPretty)
import System.IO

import Presyntax
import Syntax
import Elaboration

import Debug.Trace

load ∷ Maybe FilePath → IO (Maybe (Tm , Ty))
load Nothing = do
  putStrLn "No filepath loaded" >> pure Nothing
load (Just path) =
  try (readFile path) >>= \case
    Left (e ∷ SomeException) → Nothing <$ (putStrLn $ displayException e)
    Right file →
      case parseTmᴾ path file of
        Left e  → Nothing <$ (putStrLn $ parseErrorPretty e)
        Right t → try (reset *> infer MINo 0 [] [] t) >>= \case
          Left (e ∷ SomeException) → Nothing <$ (putStrLn $ displayException e)
          Right (t, a) → pure (Just (zonk 0 [] t, a))

loop ∷ Maybe FilePath → IO ()
loop p = do
  putStr "λ> "
  l ← getLine
  case l of
    ':':'l':rest → do
      let path = dropWhile isSpace rest
      _ ← load (Just path)
      loop (Just path)
    ':':'r':_ → load p >> loop p
    ':':'t':_ → load p >>= maybe (pure ()) (\(t, a) → print (quote 0 a)) >> loop p
    ':':'n':_ → load p >>= maybe (pure ()) (\(t, a) → print (quote 0 (eval [] t))) >> loop p
    ':':'e':_ → load p >>= maybe (pure ()) (\(t, a) → print t) >> loop p
    ':':'q':_ → pure ()
    ':':'?':_ → do
      putStrLn ":l <file>    load file"
      putStrLn ":r           reload file"
      putStrLn ":t           show type"
      putStrLn ":n           show normal form"
      putStrLn ":e           show elaborated file"
      putStrLn ":q           quit"
      putStrLn ":?           show this help"
      loop p
    _ → do
      putStrLn "Unknown command"
      putStrLn "use :? for help"
      loop p

main ∷ IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn "smalltt 0.1.0.0"
  putStrLn "enter :? for help"
  loop Nothing
