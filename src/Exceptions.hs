{-# language UnboxedTuples #-}

module Exceptions where

import GHC.Exts
import qualified Control.Exception as E
import qualified Data.ByteString as B
import qualified FlatParse.Basic as FP
import Text.Printf

import Common
import Cxt.Types
import IO
import qualified Presyntax as P
import qualified UIO as U
import CoreTypes

--------------------------------------------------------------------------------

data UnifyEx
  = Conversion
  | CSFlexSolution

data Exception
  = UnifyError Cxt P.Tm Val Val    -- checking, lhs, rhs
  | TooManyLocals Span             -- offending binder
  | UnifyEx UnifyEx
  | NoNamedArgument P.Tm Span  -- checking, name
  | NotInScope Span            -- offending name

--------------------------------------------------------------------------------

data Exception#
  = forall e. E.Exception e => SomeException e
  | Exception# Exception

catchIO :: forall a. IO a -> (Exception -> IO a) -> IO a
catchIO (IO f) k = IO (catch# f (\case e@(SomeException _) -> raiseIO# e
                                       Exception# e        -> unIO (k e)))
{-# inline catchIO #-}

catch :: forall a. U.CanIO a => U.IO a -> (Exception -> U.IO a) -> U.IO a
catch ma k = U.io $ catchIO (U.toIO ma) (\e -> U.toIO (k e))
{-# inline catch #-}

throw :: forall a. U.CanIO a => Exception -> U.IO a
throw e = U.IO \s -> case raiseIO# (Exception# e) s of (# s, a #) -> U.pure# @a a s
{-# inline throw #-}

-- | Converts all unhandled custom exceptions to standard exceptions.
standardize :: IO a -> IO a
standardize ma = catchIO ma (\e -> uf)
{-# inline standardize #-}

--------------------------------------------------------------------------------

render :: B.ByteString -> Span -> String -> String
render src (Span pos _) msg = let
  ls         = FP.lines src
  [(l, c)]   = FP.posLineCols src [pos]
  line       = if l < length ls then ls !! l else ""
  linum      = show l
  lpad       = map (const ' ') linum
  in show l ++ ":" ++ show c ++ ":\n" ++
     lpad   ++ "|\n" ++
     linum  ++ "| " ++ line ++ "\n" ++
     lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
     msg

showException :: B.ByteString -> Exception -> String
showException src = \case
  UnifyError cxt t l r -> render src (P.span t) $
    printf "Can't unify\n\n  %s\n\nwith\n\n  %s\n" (showTm  _
      -- (showVal0 cxt t) (showVal0 cxt u)

  -- = UnifyError P.Tm Val Val    -- checking, lhs, rhs
  -- | TooManyLocals Span         -- offending binder
  -- | UnifyEx UnifyEx
  -- | NoNamedArgument P.Tm Span  -- checking, name
  -- | NotInScope Span            -- offending name

-- showElabEx :: B.ByteString -> TopLevel -> Cxt -> ElabEx -> String
-- showElabEx src top cxt = \case
--   UnifyOuter t u -> uf
    -- printf "Can't unify\n\n  %s\n\nwith\n\n  %s\n"
    --   (showTm src top _) (showTm src top _)

-- showElabError :: B.ByteString -> TopLevel -> Cxt -> P.Tm -> ElabEx -> String
-- showElabError src top cxt t e = let
--   ls         = FP.lines src
--   Span pos _ = P.span t
--   [(l, c)]   = FP.posLineCols src [pos]
--   line       = if l < length ls then ls !! l else ""
--   linum      = show l
--   lpad       = map (const ' ') linum
--   in show l ++ ":" ++ show c ++ ":\n" ++
--      lpad   ++ "|\n" ++
--      linum  ++ "| " ++ line ++ "\n" ++
--      lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
--      showElabEx src top cxt e
