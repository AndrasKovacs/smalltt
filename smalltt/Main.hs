
module Main where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Array.LM as ALM
import qualified Data.ByteString as B
import qualified Control.Exception as Ex
import System.IO
import Control.Monad

import qualified MetaCxt as MC
import qualified SymTable as ST
import qualified TopCxt as Top
import Common
import CoreTypes
import Elaboration
import Evaluation
import Exceptions
import Lexer
import Parser

--------------------------------------------------------------------------------
-- TODO:
-- - add parametrized flex unfolding depth, in unification and scopechecking

--------------------------------------------------------------------------------

main :: IO ()
main = standardize do
  hSetBuffering stdout NoBuffering
  putStrLn "smalltt 2.0.0"
  putStrLn "enter :? for help"
  loop Nothing

data State = State {
    path   :: FilePath
  , src    :: B.ByteString
  , topCxt :: Top.Cxt
  }

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
            putStrLn (path ++ " parsed in " ++ show time)
            timed (elab src top) >>= \case
              (Left e, _) -> do
                putStrLn (showException src e)
                pure Nothing
              (Right topCxt, time) -> do
                putStrLn (path ++ " elaborated in " ++ show time)
                metas <- MC.size (Top.mcxt topCxt)
                putStrLn ("created " ++ show metas ++ " metavariables")
                putStrLn ("loaded " ++ show (Top.lvl topCxt) ++ " definitions")
                pure (Just (State path src topCxt))
  putStrLn ("total load time: " ++ show time)
  pure res

loop :: Maybe State -> IO ()
loop st = do
  let whenLoaded action =
        maybe (putStrLn "no file loaded" >> loop st) action st
      {-# inline whenLoaded #-}

  let dropSp = dropWhile (==' ')

  let loadTopDef str act = whenLoaded \st -> do
        let x = strToUtf8 str
        ST.lookupByteString x (Top.tbl (topCxt st)) >>= \case
          UJust (ST.Top a ga t _) -> do
            act st a t
          _ -> do
            putStrLn "no such top-level name"
            loop (Just st)
      {-# inline loadTopDef #-}

  let showTm0 st =
        CoreTypes.showTm0 (Top.mcxt (topCxt st)) (src st) (Top.info (topCxt st))

  let nf0 (State _ _ cxt) = Evaluation.nf0 (Top.mcxt cxt)
      {-# inline nf0 #-}

  let zonk0 (State _ _ cxt) = Evaluation.zonk (Top.mcxt cxt) ENil 0
      {-# inline zonk0 #-}

  let renderElab st = do
       let size = Top.lvl (topCxt st)

       let go :: MetaVar -> Lvl -> IO ()
           go m i | i == size = pure ()
           go m i =
             ALM.read (Top.info (topCxt st)) (coerce i) >>= \case
               TopEntry x a t frz -> do
                 let go' m | m == frz = pure ()
                     go' m = do
                       ADL.read (Top.mcxt (topCxt st)) (coerce m) >>= \case
                         Unsolved _ ->
                           putStrLn $ show m ++ " unsolved"
                         Solved _ _ t _ ->
                           putStrLn $ show m ++ " = " ++ showTm0 st t
                       go' (m + 1)
                 go' m
                 when (m /= frz) (putStrLn "")
                 putStrLn $ showSpan (src st) x ++ " : " ++ showTm0 st a
                 putStrLn $ "  = " ++ showTm0 st t
                 putStrLn ""
                 go frz (i + 1)
       go 0 0

  let renderZonkedElab st = do
       let size = Top.lvl (topCxt st)

       let go :: MetaVar -> Lvl -> IO ()
           go m i | i == size = pure ()
           go m i =
             ALM.read (Top.info (topCxt st)) (coerce i) >>= \case
               TopEntry x a t frz -> do
                 putStrLn $ showSpan (src st) x ++ " : " ++ showTm0 st (zonk0 st a)
                 putStrLn $ "  = " ++ showTm0 st (zonk0 st t)
                 putStrLn ""
                 go frz (i + 1)
       go 0 0

  let renderBro st = do
        ALM.for (Top.info (topCxt st)) \(TopEntry x a t frz) ->
          putStrLn $ showSpan (src st) x ++ " : " ++ showTm0 st a

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
    ':':'z':'t':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st (zonk0 st a)
        loop (Just st)
    ':':'n':'t':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        (nf, t) <- timedPure (nf0 st UnfoldAll a)
        putStrLn $ showTm0 st nf
        putStrLn $ "normalized in " ++ show t
        loop (Just st)
    ':':'n':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        (nf, t) <- timedPure (nf0 st UnfoldAll t)
        putStrLn $ showTm0 st nf
        putStrLn $ "normalized in " ++ show t
        loop (Just st)
    ':':'z':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st (zonk0 st t)
        loop (Just st)
    ':':'e':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st t
        loop (Just st)
    ':':'o':'u':'t':_ ->
      whenLoaded \st -> do
        renderElab st
        loop (Just st)
    ':':'z':'o':'u':'t':_ ->
      whenLoaded \st -> do
        renderZonkedElab st
        loop (Just st)
    ':':'b':'r':'o':_ ->
      whenLoaded \st -> renderBro st >> loop (Just st)

    ':':'?':_ -> do
      putStrLn ":l <file>    load file"
      putStrLn ":r           reload file"
      putStrLn ":e  <name>   show elaborated version of top-level definition"
      putStrLn ":n  <name>   show normal form of top-level definition"
      putStrLn ":z  <name>   show zonked form of top-level definition"
      putStrLn ":t  <name>   show elaborated type of top-level definition"
      putStrLn ":nt <name>   show normal type of top-level definition"
      putStrLn ":zt <name>   show zonked type of top-level definition"
      putStrLn ":out         show whole elaboration output"
      putStrLn ":zout        show zonked whole elaboration output"
      putStrLn ":bro         show defined top-level names and their types"
      putStrLn ":q           quit"
      putStrLn ":?           show this message"
      loop st
    ':':'q':_ -> do
      pure ()
    _ -> do
      putStrLn "unknown command"
      putStrLn "use :? for help"
      loop st
