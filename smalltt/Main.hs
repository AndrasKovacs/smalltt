{-# language UnboxedTuples #-}

module Main where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Array.LM as ALM
import qualified Data.ByteString as B
import qualified Control.Exception as Ex
import FlatParse.Basic (packUTF8)
-- import System.Environment
-- import System.Exit
import System.IO
-- import System.Mem

import qualified SymTable as ST
import Common
import CoreTypes
import Elaboration
import Parser
import Lexer
import Exceptions
import SymTable (SymTable)
import MetaCxt
import Evaluation

--------------------------------------------------------------------------------

main :: IO ()
main = standardize do
  hSetBuffering stdout NoBuffering
  putStrLn "smalltt 2.0.0"
  putStrLn "enter :? for help"
  loop Nothing

data State = State {
    path :: FilePath
  , src  :: B.ByteString
  , tbl  :: SymTable
  , top  :: TopLevel
  , mcxt :: MetaCxt}

load :: FilePath -> IO (Maybe State)
load path = do
  (res, time) <- timed $
    Ex.try (B.readFile path) >>= \case
      Left (e :: Ex.SomeException) -> do
        putStrLn (Ex.displayException e)
        pure Nothing
      Right src -> do
        timedPure (parse src) >>= \case
          (Err e, _) -> do
            putStrLn (path ++ ":")
            putStrLn (prettyError src e)
            pure Nothing
          (Fail, _) -> do
            putStrLn "unknown parse error"
            pure Nothing
          (OK top _ _, time) -> do
            putStrLn ("parsed in " ++ show time)
            timed (checkProg src top) >>= \case
              (Left e, _) -> do
                putStrLn (showException src e)
                pure Nothing
              (Right (tbl, top, ms), time) -> do
                putStrLn ("elaborated in " ++ show time)
                pure (Just (State path src tbl top ms))
  putStrLn ("total load time: " ++ show time)
  pure res

loop :: Maybe State -> IO ()
loop st = do
  let whenLoaded action =
        maybe (putStrLn "no file loaded" >> loop st) action st

  let dropSp = dropWhile (==' ')

  let loadTopDef str act = whenLoaded \st -> do
        let x = packUTF8 str
        ST.lookupByteString x (tbl st) >>= \case
          UJust (ST.Top _ a va t vt) -> do
            act st a t
          _ -> do
            putStrLn "no such top-level name"
            loop (Just st)

  let showTm0 st = CoreTypes.showTm0 (src st) (top st)

  let renderElab st = do
        ADL.forIx (mcxt st) \i e -> case e of
          MEUnsolved ->
            putStrLn $ '?':show i ++ " unsolved"
          MESolved v ->
            putStrLn $ '?':show i ++ " = " ++ showTm0 st (quote0 (mcxt st) UnfoldNone v)
        ALM.for (topDefs (top st)) \(TopEntry x a t) -> do
          putStrLn ""
          putStrLn $ showSpan (src st) x ++ " : " ++ showTm0 st a
          putStrLn $ "  = " ++ showTm0 st t

  putStr (maybe "" path st ++ "> ")
  l <- getLine
  case l of
    ':':'l':' ':(dropSp -> rest) ->
      loop =<< load rest
    ':':'r':_ ->
      whenLoaded \st -> load (path st) >>= \case
        Nothing -> loop (Just st)
        Just st -> loop (Just st)
    ':':'t':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st a
        loop (Just st)
    ':':'n':'t':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st (nf0 (mcxt st) UnfoldAll a)
        loop (Just st)
    ':':'n':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st (nf0 (mcxt st) UnfoldAll t)
        loop (Just st)
    ':':'e':_ ->
      whenLoaded \st -> do
        renderElab st
        loop (Just st)
    ':':'?':_ -> do
      putStrLn ":l <file>    load file"
      putStrLn ":r           reload file"
      putStrLn ":t  <name>   show elaborated type of definition"
      putStrLn ":nt <name>   show normal elaborated type of top definition"
      putStrLn ":n  <name>   show normal form of top definition"
      putStrLn ":e           show elaborated file"
      putStrLn ":bro         show defined top names and types"
      putStrLn ":q           quit"
      putStrLn ":?           show this message"

      loop st
    ':':'q':_ -> do
      pure ()
    _ -> do
      putStrLn "unknown command"
      putStrLn "use :? for help"
      loop st
