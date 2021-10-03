
module Main where

import System.Environment

import Common
import Presyntax
import Lexer
import Parser

main :: IO ()
main = do
  (file:_) <- getArgs
  (src, res) <- parseFile file
  case res of
    OK a _ _ -> putStrLn $ "Parse success, number of top defs: " ++ show (topLen a)
    Fail     -> putStrLn "parser failure"
    Err e    -> putStrLn $ prettyError src e
