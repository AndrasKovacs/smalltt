
module Test where

import qualified UIO as U

foo :: Int -> U.IO Int
foo x = U.do
  if x == 0 then
    U.pure x
  else U.do
    y <- foo (x - 1)
    U.pure $! x * y

data Tree = Leaf Int | Node Tree Tree
  deriving Show

foo2 :: Tree -> U.IO Int
foo2 = \case
  Leaf n   -> U.pure n
  Node l r -> (+) U.<$> foo2 l U.<*> foo2 r
