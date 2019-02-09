{-# LANGUAGE RecordWildCards #-}

module Errors where

import Control.Exception
import Text.Megaparsec.Pos
import Text.Printf
import qualified Data.Text as T

import Common
import Cxt
import ElabState
import Syntax
import Values
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
  | UEGluedSolution Meta VSpine GSpine GV SolutionError
  | UEGluedUnify GV GV
  | UELocalSpine Meta VSpine Val Val
  | UEGluedSpine Meta VSpine GSpine GV Glued

instance Show UnifyError where show _ = "UnifyError"
instance Exception UnifyError

data LocalError = LocalError Names UnifyError

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
  | EEIllegalDefInPostulateBlock
  | EEIllegalRuleLHS
  | EEWrongRuleArity Int Int

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
displayTopError file (TopError cxt@(Cxt{..}) err) = do
  report <- reportWithLine file <$> getPos

  case err of
    EECheck t want@(GV gwant vwant) has@(GV ghas vhas)
              (LocalError ns err) -> do

      let reportUnify g g' v v' = report $ printf
           "Can't (glued) unify\n\n  %s\n\nwith\n\n  %s\n\n\
            \while unifying expected type:\n\n  %s\n\nwith inferred type:\n\n  %s\n\n"
            (showGlued _nameTable ns g') (showGlued _nameTable ns g)
            -- (showValMetaless _nameTable ns v') (showValMetaless _nameTable ns v)
            -- (showValCxtMetaless cxt vwant) (showValCxtMetaless cxt vhas)
            (showGlued _nameTable ns gwant) (showGlued _nameTable ns ghas)

      let reportLocalUnify v v' = report $ printf
           "Can't (locally) unify\n\n  %s\n\nwith\n\n  %s\n\n\
            \while unifying expected type:\n\n  %s\n\nwith inferred type:\n\n  %s\n\n"
            (showValMetaless _nameTable ns v') (showValMetaless _nameTable ns v)
            (showValCxtMetaless cxt vwant) (showValCxtMetaless cxt vhas)

          reportSolutionErr x vsp v err = report (
            printf
              "Illegal solution candidate when trying to solve\n\n\
               \  %s\n\nwith\n\n  %s\n\n"
              (showValMetaless _nameTable ns (VNe (HMeta x) vsp))
              (showValMetaless _nameTable ns v)
            ++
            case err of
              SEScope x' -> printf "Local variable \"%s\" is out of metavariable scope\n\n"
                                   (showValMetaless _nameTable ns (VLocal x'))
              SEOccurs   -> printf "To-be-solved metavariable occurs in solution candidate\n\n"
            )

      case err of
        UELocalUnify v v'                      -> reportLocalUnify v v'
        UEGluedUnify (GV g v) (GV g' v')       -> reportUnify g g' v v'
        UELocalSolution x vsp v err            -> reportSolutionErr x vsp v err
        UEGluedSolution x vsp gsp (GV _ v) err -> reportSolutionErr x vsp v err
        UELocalSpine x vsp rhs v               -> report "Non-variable in meta spine\n\n"
        UEGluedSpine x vsp gsp rhs g           -> report "Non-variable in meta spine\n\n"

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
          (showValCxtMetaless cxt va)

    EENamedLambda ->
      report "Can't infer type for lambda with named implicit argument\n\n"

    EEUnsolvedMeta x@(Meta i j) ->
      case lookupMeta x of
        MESolved{}     -> error "displayElabError: impossible"
        MEUnsolved pos ->
          reportWithLine
            file pos (printf "Unsolved metavariable: %d.%d\n\n" i j)

    EEIllegalDefInPostulateBlock ->
      report "Only lambda expressions are allowed as\
              \definitions in an \"assume\" block\n\n"

    EEIllegalRuleLHS ->
      report "Rewrite rule left hand side must be a postulated name applied to one or more arguments\n\n"

    EEWrongRuleArity want has ->
      report $ printf "Rewrite rule arity mismatch: expected arity %d, got %d\n\nAll \
                       \rewrite rules for the same name must have the same arity\n\n"
               want has
