{-# options_ghc -Wno-unused-imports #-}

module Test where

import qualified Data.Text as T
import Text.Megaparsec.Error

import Common
import Elaboration
import Evaluation
import Parser
import Syntax
import Values
import Pretty

t = T.unlines [
  "id : {A} -> A -> A",
  "id = \\x. x",

  "id2 : {A} -> A -> A",
  "id2 = id (id!)"
  ]

test :: IO ()
test = either (putStrLn . errorBundlePretty)
              (\t -> checkProgram t)
              (parseFile "" t)
