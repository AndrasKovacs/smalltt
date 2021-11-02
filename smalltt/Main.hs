{-# language UnboxedTuples #-}

module Main where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Array.LM as ALM
import qualified Data.ByteString as B
import qualified Control.Exception as Ex
import System.IO

import qualified MetaCxt as MC
import qualified SymTable as ST
import qualified UIO as U
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
--   main : add more cmd options, :bro, top-level name elabs, unfold opts
--   - known call optimization, solved meta eval optimization
--   - hpalloc reductions through shared vars, renamings & other data
--   - try putting terms in a compact region
--   - organize args in records (UnifyCxt, EvalCxt, SolveCxt etc)
--       overload fields with microlens
--   - add parametrized flex unfolding depth, in unification and scopechecking

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
            putStrLn ("parsed in " ++ show time)
            timed (elab src top) >>= \case
              (Left e, _) -> do
                putStrLn (showException src e)
                pure Nothing
              (Right topCxt, time) -> do
                putStrLn ("elaborated in " ++ show time)
                metas <- U.toIO $ MC.size (Top.mcxt topCxt)
                putStrLn ("created " ++ show metas ++ " metas")
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
        let x = packUTF8 str
        ST.lookupByteString x (Top.tbl (topCxt st)) >>= \case
          UJust (ST.Top a ga t _) -> do
            act st a t
          _ -> do
            putStrLn "no such top-level name"
            loop (Just st)
      {-# inline loadTopDef #-}

  let showTm0 st = CoreTypes.showTm0 (src st) (Top.info (topCxt st))

  let nf0 (State _ _ cxt) = Evaluation.nf0 (Top.mcxt cxt)
      {-# inline nf0 #-}

  let renderElab st = do
        ADL.forIx (Top.mcxt (topCxt st)) \i e -> case e of
          MC.MEUnsolved ->
            putStrLn $ '?':show i ++ " unsolved"
          MC.MESolved _ t _ ->
            putStrLn $ '?':show i ++ " = " ++ showTm0 st t
        ALM.for (Top.info (topCxt st)) \(TopEntry x a t) -> do
          putStrLn ""
          putStrLn $ showSpan (src st) x ++ " : " ++ showTm0 st a
          putStrLn $ "  = " ++ showTm0 st t

  let renderBro st = do
        ALM.for (Top.info (topCxt st)) \(TopEntry x a t) ->
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
    ':':'n':'t':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st (nf0 st UnfoldAll a)
        loop (Just st)
    ':':'n':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st (nf0 st UnfoldAll t)
        loop (Just st)
    ':':'e':' ':(dropSp -> rest) ->
      loadTopDef rest \st a t -> do
        putStrLn $ showTm0 st t
        loop (Just st)
    ':':'o':'u':'t':_ ->
      whenLoaded \st -> do
        renderElab st
        loop (Just st)
    ':':'b':'r':'o':_ ->
      whenLoaded \st -> renderBro st >> loop (Just st)

    ':':'?':_ -> do
      putStrLn ":l <file>    load file"
      putStrLn ":r           reload file"
      putStrLn ":t  <name>   show elaborated type of top-level definition"
      putStrLn ":nt <name>   show normal elaborated type of top-level definition"
      putStrLn ":e  <name>   show elaborated version of top-level definition"
      putStrLn ":n  <name>   show normal form of top-level definition"
      putStrLn ":out         show whole elaboration output"
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
