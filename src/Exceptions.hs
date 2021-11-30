{-# language UnboxedTuples #-}

module Exceptions where

import qualified Control.Exception as E
import qualified Data.ByteString as B
import qualified FlatParse.Basic as FP
import GHC.Exts
import Text.Printf

import qualified Presyntax as P
import qualified UIO as U
import qualified SymTable as ST
import Evaluation
import Common
import CoreTypes
import IO

--------------------------------------------------------------------------------

data UnifyEx
  = Conversion
  | CSFlexSolution
  | FrozenSolution MetaVar
  deriving Show

data ErrorCxt = ErrorCxt MetaCxt ST.SymTable Names Lvl

instance Show ErrorCxt where
  show _ = "<ErrorCxt>"

data Exception
  = UnifyError {-# unpack #-} ErrorCxt P.Tm Val Val UnifyEx  -- checking, lhs, rhs
  | TooManyLocals
  | UnifyEx UnifyEx
  | NoNamedArgument P.Tm {-# unpack #-} Span      -- checking, name
  | NotInScope {-# unpack #-} Span                -- offending name
  | Undefined
  | InferNamedLam
  deriving Show

--------------------------------------------------------------------------------

data Exception#
  = forall e. E.Exception e => SomeException e
  | Exception# Exception

catchIO :: forall a. IO a -> (Exception -> IO a) -> IO a
catchIO (IO f) k = IO (catch# f (\case e@(SomeException _) -> raiseIO# e
                                       Exception# e        -> unIO (k e)))
{-# inline catchIO #-}

catch :: forall a. U.CanIO a => U.IO a -> (Exception -> U.IO a) -> U.IO a
catch ma k = U.io (catchIO (U.toIO ma) (\e -> U.toIO (k e)))
{-# inline catch #-}

throw :: forall a. U.CanIO a => Exception -> U.IO a
throw e = U.IO \s -> case raiseIO# (Exception# e) s of (# s, a #) -> U.pure# @a a s
{-# inline throw #-}

-- | Converts all unhandled custom exceptions to standard exceptions.
standardize :: IO a -> IO a
standardize ma = catchIO ma (\e -> uf)
{-# inline standardize #-}

try :: forall a. U.CanIO a => U.IO a -> U.IO (Either Exception a)
try act = (Right U.<$> act) `catch` \e -> U.pure (Left e)
{-# inline try #-}

--------------------------------------------------------------------------------

render :: B.ByteString -> Span -> String -> String
render src (Span pos _) msg = let
  ls     = FP.lines src
  (l, c) = head $ FP.posLineCols src [pos]
  line   = if l < length ls then ls !! l else ""
  linum  = show (l + 1)
  lpad   = map (const ' ') linum
  in linum  ++ ":" ++ show c ++ ":\n" ++
     lpad   ++ "|\n" ++
     linum  ++ "| " ++ line ++ "\n" ++
     lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
     msg
{-# noinline render #-}

showVal :: ErrorCxt -> Val -> String
showVal (ErrorCxt ms tbl ns l) v =
  prettyTm ms 0 (ST.src tbl) ns (quote ms l UnfoldMetas v) []

showException :: B.ByteString -> Exception -> String
showException src = \case
  UnifyError cxt t l r (FrozenSolution x) -> render src (P.span t) $
    printf ("Can't solve frozen metavariable %s when trying to " ++
            "unify\n\n  %s\n\nwith\n\n  %s\n")
      (show x)
      (showVal cxt l) (showVal cxt r)
  UnifyError cxt t l r _ -> render src (P.span t) $
    printf "Can't unify\n\n  %s\n\nwith\n\n  %s\n"
      (showVal cxt l) (showVal cxt r)
  TooManyLocals ->
    "Too many local variables! You can't have more than 64."
  UnifyEx _ ->
    "Unhandled unification exception"
  NoNamedArgument t x -> render src (P.span t) $
    "No named implicit argument with name " ++ showSpan src x
  NotInScope x -> render src x $
    "Name not in scope: " ++ "\"" ++ showSpan src x ++ "\""
  Undefined ->
    "Undefined exception"
  InferNamedLam ->
    "Cannot infer type for lambda with named argument"
{-# noinline showException #-}
