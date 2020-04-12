{-# options_ghc -Wno-incomplete-patterns #-}

{- |
Preliminary pretty printing, to be replaced with more sophisticated solutions.
-}

module Pretty (
    showTm
  , showTm0
  , showTmCxt
  , showVal
  , showValMetaless
  , showValCxt
  , showValCxtMetaless
  , showLocal
  , showLocalCxt
  ) where

import qualified Data.Array.Dynamic as A
import qualified Data.Text.Short as T
import qualified Data.HashMap.Strict as HM

import Common
import ElabState
import Syntax
import Cxt
import Values
import Evaluation

showTm0 :: NameTable -> Tm -> String
showTm0 ntbl = showTm ntbl NNil

showTm :: NameTable -> Names -> Tm -> String
showTm ntbl ns t = prettyTm 0 ntbl ns t ""

showTmCxt :: Cxt -> Tm -> String
showTmCxt Cxt{..} = showTm _nameTable _names

showVal :: NameTable -> Names -> Val -> String
showVal ntbl ns = showTm ntbl ns . nfQuote (namesLength ns)

showValMetaless :: NameTable -> Names -> Val -> String
showValMetaless ntbl ns = showTm ntbl ns . lQuoteMetaless (namesLength ns)

showValCxt :: Cxt -> Val -> String
showValCxt Cxt{..} = showTm _nameTable _names . nfQuote _size

showValCxtMetaless :: Cxt -> Val -> String
showValCxtMetaless Cxt{..} = showValMetaless _nameTable _names

showLocal :: NameTable -> Names -> Val -> String
showLocal ntbl ns = showTm ntbl ns . lQuote (namesLength ns)

showLocalCxt :: Cxt -> Val -> String
showLocalCxt Cxt{..} = showLocal _nameTable _names

getApp :: Tm -> Maybe (Icit, Tm, Tm)
getApp (AppI t u) = Just (Impl, t, u)
getApp (AppE t u) = Just (Expl, t, u)
getApp _          = Nothing

-- | Unfortunately this trips ups pattern coverage checking.
pattern App :: Icit -> Tm -> Tm -> Tm
pattern App i t u <- (getApp -> Just (i, t, u)) where
  App Impl t u = AppI t u
  App Expl t u = AppE t u

prettyTm :: Int -> NameTable -> Names -> Tm -> ShowS
prettyTm prec ntbl = go (prec /= 0) where

  go :: Bool -> Names -> Tm -> ShowS
  go p ns = \case
    LocalVar x -> ((T.unpack $ lookupName ns x)++)
    TopVar x -> runIO $ do {Posed _ n <- _entryName <$> A.read top x; pure (T.unpack n++)}
    MetaVar (Meta i j) -> (("?"++).(show i++)).('.':).(show j++)
    Let (Named (disamb ns -> x) a) t u ->
      ("let "++) . (T.unpack x++) . (" : "++) . go False ns a . ("\n    = "++)
      . go False ns t  . ("\nin\n"++) . go False (NSnoc ns x) u
    App i' (App i t u) u' ->
      showParen p (go False ns t . (' ':) . goArg ns u i . (' ':) . goArg ns u' i')
    App i t u         -> showParen p (go True ns t . (' ':) . goArg ns u i)
    Lam (Named (disamb ns -> x) i) t ->
      showParen p (("λ "++) . goLamBind x i . goLam (NSnoc ns x) t)
    t@Pi{}            -> showParen p (goPi False ns t)
    Fun t u           -> showParen p (go (case t of App{} -> False; _ -> True) ns t
                                      . (" → "++) . go False ns u)
    U                 -> ("U"++)
    Irrelevant        -> ("Irr"++)

  goArg :: Names -> Tm -> Icit -> ShowS
  goArg ns t i = icit i (bracket (go False ns t)) (go True ns t)

  bracket :: ShowS -> ShowS
  bracket s = ('{':).s.('}':)

  goPiBind :: Name -> Icit -> Names -> Tm -> ShowS
  goPiBind x i ns a =
    icit i bracket (showParen True) ((T.unpack x++) . (" : "++) . go False ns a)

  goPi :: Bool -> Names -> Tm -> ShowS
  goPi p ns (Pi (Named (disamb ns -> x) i) a b) = goPiBind x i ns a . goPi True (NSnoc ns x) b
  goPi p ns t = (if p then (" → "++) else id) . go False ns t

  goLamBind :: Name -> Icit -> ShowS
  goLamBind x i = icit i bracket id (T.unpack (if T.null x then "_" else x) ++)

  goLam :: Names -> Tm -> ShowS
  goLam ns (Lam (Named (disamb ns -> x) i) t) = (' ':) . goLamBind x i . goLam (NSnoc ns x) t
  goLam ns t = (". "++) . go False ns t

  lookupName :: Names -> Ix -> Name
  lookupName = go where
    go NNil         _ = error "lookupNames: impossible"
    go (NSnoc ns n) 0 = if T.null n then "_" else n
    go (NSnoc ns n) x = go ns (x - 1)

  disamb :: Names -> Name -> Name
  disamb ns n | T.null n = n
  disamb ns n = go (0 :: Int) where
    go 0 | elem n ns || HM.member n ntbl = go 1
         | otherwise = n
    go i = let n' = n <> T.pack (show i)
           in if elem n' ns || HM.member n' ntbl then go (i + 1) else n'
    elem n NNil = False
    elem n (NSnoc ns n')
      | n == n'   = True
      | otherwise = elem n ns
