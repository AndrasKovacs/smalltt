
module Errors where

import Control.Exception
import qualified Data.Text as T
import Text.Megaparsec.Pos
import Text.Printf

import Common
import Syntax
import Values
import ElabState
import Pretty
import Evaluation

data SolutionError
  = SEScope Ix
  | SEOccurs

instance Show SolutionError where show _ = "SolutionError"
instance Exception SolutionError

data UnifyError
  = UELocalSolution Lvl Names Meta VSpine Val SolutionError
  | UELocalUnify Lvl Names Val Val
  | UEGluedSolution Lvl Names Meta GSpine GV SolutionError
  | UEGluedUnify Lvl Names GV GV
  | UELocalSpine Lvl Names Meta VSpine Val Val
  | UEGluedSpine Lvl Names Meta GSpine GV Glued

instance Show UnifyError where show _ = "UnifyError"
instance Exception UnifyError

data LocalError a
  = LEFlex
  | LERigid a

instance Show a => Show (LocalError a) where show a = "LocalError " ++ show a
instance Exception a => Exception (LocalError a)

data ElabError
  = EECheck Lvl Names Tm GVTy GVTy UnifyError
  | EENoNamedArg Lvl Names Tm GVTy Name
  | EEScope Name
  | EEAppIcit Tm Icit Icit
  | EEFunctionExpected Lvl Names Tm GVTy
  | EENamedLambda
  | EEUnsolvedMeta Meta

instance Show ElabError where show _ = "ElabError"
instance Exception ElabError

localError :: Rigidity -> a -> LocalError a
localError Flex  _  = LEFlex
localError Rigid x  = LERigid x
{-# inline localError #-}

reportWithLine :: T.Text -> SourcePos -> String -> IO ()
reportWithLine file (SourcePos path (unPos -> linum) (unPos -> colnum)) msg = do
  let line = T.unpack (T.lines file !! (linum - 1))
      caret = replicate (colnum - 1) ' ' ++ "^"
      careted = line ++ "\n" ++ caret
  printf "%s:%d:%d:\n\n" path linum colnum
  printf "%  s\n" careted
  printf msg

displayElabError :: T.Text -> ElabError -> IO ()
displayElabError file err = do
  report <- reportWithLine file <$> getPos
  case err of
    EECheck l ns t want@(GV gwant vwant) has@(GV ghas vhas) err -> do
      case err of
        UELocalUnify l ns v v' ->
          report $
            printf
              "Can't unify expected type:\n\n  %s\n\nwith inferred type:\n\n  %s\n\n"
              (showTm ns (vQuoteMetaless l vwant)) (showTm ns (vQuoteMetaless l vhas))

        UEGluedUnify l ns gv gv' ->
          report $
            printf
              "Can't unify expected type:\n\n  %s\n\nwith inferred type:\n\n  %s\n\n"
              (showTm ns (gQuote l gwant)) (showTm ns (gQuote l ghas))

        UELocalSolution l ns x vsp v err -> report "Illegal solution candidate"
        UEGluedSolution l ns x gsp gv err -> report "Illegal solution candidate"
        UELocalSpine l ns x vsp rhs v -> report "Non-variable in meta spine"
        UEGluedSpine l ns x gsp rhs g -> report "Non-variable in meta spine"


    EENoNamedArg l ns t gva x ->
      report $ printf "No implicit argument with name: %s\n\n" x

    EEScope x ->
      report $ printf "Name not found in scope: %s\n\n" x

    EEAppIcit t iwant ihas ->
      report $
        printf
          "Expected %s application\n\n"
          (case iwant of Expl -> "explicit"::String; _ -> "implicit")

    EEFunctionExpected l ns t (GV ga va) ->
      report $
        printf
          "Expected a function type for expression. Inferred type:\n\n  %s\n\n"
          (showTm ns (gQuote l ga))

    EENamedLambda ->
      report "Can't infer type for lambda with named implicit argument\n\n"

    EEUnsolvedMeta x@(Meta i j) ->
      case lookupMeta x of
        MESolved{}     -> error "displayElabError: impossible"
        MEUnsolved pos ->
          reportWithLine
            file pos (printf "Unsolved metavariable: %d.%d\n\n" i j)
