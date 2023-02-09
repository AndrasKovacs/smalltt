
module Exceptions where

import qualified Control.Exception as E
import qualified FlatParse.Basic as FP
import GHC.Exts
import Text.Printf

import qualified Presyntax as P
import qualified SymTable as ST
import Evaluation
import Common
import CoreTypes
import IO

--------------------------------------------------------------------------------

-- | Exceptions throw during unification.
data UnifyEx
  = Conversion             -- ^ Generic conversion error, includes occurs/scoping checks, pattern
                           --   spine conditions and mismatched rigid heads.
  | FlexSolution           -- ^ Trying to solve a metavariable while in `Flex` mode.
  | FrozenSolution MetaVar -- ^ Trying to solve a frozen metavariable.
  deriving Show

data ErrorCxt = ErrorCxt MetaCxt ST.SymTable Names Lvl

instance Show ErrorCxt where
  show _ = "<ErrorCxt>"

data Exception
  -- ^ Context, preterm for error position, unification sides, exception.
  = UnifyExInCxt {-# unpack #-} ErrorCxt P.Tm Val Val UnifyEx
  -- ^ Exceeded `maxLocals` number of binders.
  | TooManyLocals
  | UnifyEx UnifyEx
  -- ^ Missing named implicit function argument.
  | NoNamedArgument P.Tm {-# unpack #-} Span      -- checking, name
  | NotInScope {-# unpack #-} Span                -- offending name
  -- ^ Trying to infer type for named implicit lambda.
  | InferNamedLam
  deriving Show

--------------------------------------------------------------------------------

-- | We elide usual `Control.Exception` type equality checks when
--   throwing/catching `Exception`, by adding the "runtime supertype"
--   `Exception#` for `E.Exception`. We rely on `SomeException` having the same
--   runtime representation in `E.Exception` and `Exception#`.
data Exception#
  = forall e. E.Exception e => SomeException e
  | Exception# Exception

catchIO :: forall a. IO a -> (Exception -> IO a) -> IO a
catchIO (IO f) k = IO (catch# f (\case e@(SomeException _) -> raiseIO# e
                                       Exception# e        -> unIO (k e)))
{-# inline catchIO #-}

catch :: IO a -> (Exception -> IO a) -> IO a
catch ma k = catchIO ma k
{-# inline catch #-}

throw :: forall a. Exception -> IO a
throw e = IO \s -> case raiseIO# (Exception# e) s of x -> unsafeCoerce# x
{-# inline throw #-}

-- | Converts all unhandled custom exceptions to standard exceptions. The main
--   function should be always wrapped in `standardize`.
standardize :: IO a -> IO a
standardize ma = catchIO ma (\e -> uf)
{-# inline standardize #-}

try :: IO a -> IO (Either Exception a)
try act = (Right <$> act) `catch` \e -> pure (Left e)
{-# inline try #-}

--------------------------------------------------------------------------------

-- | Display an error with source position. We only use of the first position in
--   the span.
render :: Src -> Span -> String -> String
render src (Span pos _) msg = let
  ls     = FP.linesUtf8 src
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

showException :: Src -> Exception -> String
showException src = \case
  UnifyExInCxt cxt t l r (FrozenSolution x) -> render src (P.span t) $
    printf ("Can't solve frozen metavariable %s when trying to " ++
            "unify\n\n  %s\n\nwith\n\n  %s\n")
      (show x)
      (showVal cxt l) (showVal cxt r)
  UnifyExInCxt cxt t l r _ -> render src (P.span t) $
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
  InferNamedLam ->
    "Cannot infer type for lambda with named argument"
{-# noinline showException #-}
