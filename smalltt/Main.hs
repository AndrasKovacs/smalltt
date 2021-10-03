module Main where

main :: IO ()
main = putStrLn "hello"


-- import System.Directory
-- import Parser
-- import Common
-- import Presyntax
-- import Lexer

-- import qualified Data.ByteString as B

-- main :: IO ()
-- main = do
--   (src, res) <- parseFile "parsetest.stt"
--   case res of
--     OK a _ _ -> putStrLn $ "Success, number of top defs: " ++ show (topLen a)
--     Fail     -> putStrLn "parser failure"
--     Err e    -> putStrLn $ prettyError src e
