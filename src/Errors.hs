
module Errors where

import Control.Exception
import qualified Data.Text as T
import Text.Megaparsec.Pos
import Text.Printf

import Common
import Cxt
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

data FlexRigid a = FRFlex | FRRigid a
instance Show a => Show (FlexRigid a) where show x = "FlexRigid " ++ show x
instance Exception a => Exception (FlexRigid a)

data UnifyError
  = UELocalSolution Meta VSpine Val SolutionError
  | UELocalUnify Val Val
  | UEGluedSolution Meta GSpine GV SolutionError
  | UEGluedUnify GV GV
  | UELocalSpine Meta VSpine Val Val
  | UEGluedSpine Meta GSpine GV Glued

instance Show UnifyError where show _ = "UnifyError"
instance Exception UnifyError

data LocalError = LocalError Lvl Names UnifyError

instance Show LocalError where show _ = "LocalError"
instance Exception LocalError

data ElabError
  = EECheck Tm GVTy GVTy LocalError
  | EENoNamedArg Tm GVTy Name
  | EEScope Name
  | EEAppIcit Tm Icit Icit
  | EEFunctionExpected Tm GVTy
  | EENamedLambda
  | EEUnsolvedMeta Meta

instance Show ElabError where show _ = "ElabError"
instance Exception ElabError

data TopError = TopError Cxt ElabError
instance Show TopError where show _ = "TopError"
instance Exception TopError

makeFR :: Rigidity -> a -> FlexRigid a
makeFR Flex  _  = FRFlex
makeFR Rigid x  = FRRigid x
{-# inline makeFR #-}

reportWithLine :: T.Text -> SourcePos -> String -> IO ()
reportWithLine file (SourcePos path (unPos -> linum) (unPos -> colnum)) msg = do
  let line = T.unpack (T.lines file !! (linum - 1))
      caret = replicate (colnum - 1) ' ' ++ "^"
      careted = line ++ "\n" ++ caret
  printf "%s:%d:%d:\n\n" path linum colnum
  printf "%  s\n" careted
  printf msg

displayTopError :: T.Text -> TopError -> IO ()
displayTopError file (TopError cxt err) = do
  report <- reportWithLine file <$> getPos
  case err of
    EECheck t want@(GV gwant vwant) has@(GV ghas vhas)
              (LocalError l ns err) -> do
      case err of
        UELocalUnify v v' ->
          report $
            printf
              "Can't unify expected type:\n\n  %s\n\nwith inferred type:\n\n  %s\n\n"
              (showTm ns (gQuote l gwant)) (showTm ns (gQuote l ghas))

        UEGluedUnify gv gv' ->
          report $
            printf
              "Can't unify expected type:\n\n  %s\n\nwith inferred type:\n\n  %s\n\n"
              (showTm ns (gQuote l gwant)) (showTm ns (gQuote l ghas))

        UELocalSolution x vsp v err  -> report "Illegal solution candidate"
        UEGluedSolution x gsp gv err -> report "Illegal solution candidate"
        UELocalSpine    x vsp rhs v  -> report "Non-variable in meta spine"
        UEGluedSpine    x gsp rhs g  -> report "Non-variable in meta spine"


    EENoNamedArg t gva x ->
      report $ printf "No implicit argument with name: %s\n\n" x

    EEScope x ->
      report $ printf "Name not found in scope: %s\n\n" x

    EEAppIcit t iwant ihas ->
      report $
        printf
          "Expected %s application\n\n"
          (case iwant of Expl -> "explicit"::String; _ -> "implicit")

    EEFunctionExpected t (GV ga va) ->
      report $
        printf
          "Expected a function type for expression. Inferred type:\n\n  %s\n\n"
          (showTm (_names cxt) (gQuote (_size cxt) ga))

    EENamedLambda ->
      report "Can't infer type for lambda with named implicit argument\n\n"

    EEUnsolvedMeta x@(Meta i j) ->
      case lookupMeta x of
        MESolved{}     -> error "displayElabError: impossible"
        MEUnsolved pos ->
          reportWithLine
            file pos (printf "Unsolved metavariable: %d.%d\n\n" i j)
