
module InCxt where

import qualified Data.ByteString as B
import GHC.Exts
import IO

import CoreTypes
import Cxt.Types
import Common
import qualified Evaluation as E
import qualified SymTable as ST
import qualified Presyntax as P
import qualified UIO as U

eval :: Cxt -> Tm -> Val
eval cxt t = E.eval (mcxt cxt) (env cxt) t
{-# inline eval #-}

quote :: Cxt -> QuoteOption -> Val -> Tm
quote cxt opt t = E.quote (mcxt cxt) (lvl cxt) opt t
{-# inline quote #-}

src :: Cxt -> B.ByteString
src cxt = ST.byteString (tbl cxt)
{-# inline src #-}

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (src cxt) (names cxt) t []
{-# inline showTm #-}

showVal :: Cxt -> Val -> String
showVal cxt t = showTm cxt (quote cxt UnfoldAll t)
{-# inline showVal #-}

showValOpt :: Cxt -> Val -> QuoteOption -> String
showValOpt cxt t opt = showTm cxt (quote cxt opt t)
{-# inline showValOpt #-}

forceFU :: Cxt -> Val -> Val
forceFU cxt t = E.forceFU (mcxt cxt) t
{-# inline forceFU #-}

forceF :: Cxt -> Val -> Val
forceF cxt t = E.forceF (mcxt cxt) t
{-# inline forceF #-}

forceFUM :: Cxt -> Val -> U.IO Val
forceFUM cxt t = E.forceFUM (mcxt cxt) t
{-# inline forceFUM #-}

forceFM :: Cxt -> Val -> U.IO Val
forceFM cxt t = E.forceFM (mcxt cxt) t
{-# inline forceFM #-}

app :: Cxt -> Val -> Val -> Icit -> Val
app cxt t u i = E.app (mcxt cxt) t u i
{-# inline app #-}

appCl :: Cxt -> Closure -> Val -> Val
appCl cxt t u = E.appCl (mcxt cxt) t u
{-# inline appCl #-}

showPTm :: Cxt -> P.Tm -> String
showPTm cxt t = showSpan (src cxt) (P.span t)
{-# inline showPTm #-}

eqName :: Cxt -> Name -> Name -> Bool
eqName cxt NEmpty    NEmpty     = True
eqName cxt NX        NX         = True
eqName cxt (NSpan x) (NSpan x') = runIO do
  Ptr eob <- ST.eob (tbl cxt)
  pure $! isTrue# (eqSpan# eob x x')
eqName _   _         _          = False

valToClosure :: Cxt -> Val -> Closure
valToClosure cxt t =
  Closure (env cxt) (E.quote (mcxt cxt) (lvl cxt + 1) UnfoldNone t)
{-# inline valToClosure #-}
