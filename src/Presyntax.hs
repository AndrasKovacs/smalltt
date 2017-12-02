
module Presyntax (
    Name
  , Tmᴾ(..)
  , Icit(..)
  , parseTmᴾ
  , icit
  ) where

{-| TODO: Add source position information to Tmᴾ -}

import Control.Applicative
import Control.Monad
import Data.List
import Data.Void
import Data.Char

import qualified Data.HashSet               as HS

import           Text.Megaparsec
import           Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

--------------------------------------------------------------------------------

type Name = String
data Icit = Expl | Impl deriving (Eq, Show)

data Tmᴾ
  = Varᴾ Name
  | Letᴾ Name Tmᴾ Tmᴾ Tmᴾ
  | Appᴾ Tmᴾ Tmᴾ (Either Name Icit)
  | Lamᴾ Name (Either Name Icit) Tmᴾ
  | Piᴾ Name Icit Tmᴾ Tmᴾ
  | Uᴾ
  | NoMIᴾ Tmᴾ
  | Holeᴾ

-- Parser
--------------------------------------------------------------------------------

type Parser = Parsec Void String

sc ∷ Parser ()
sc = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme     = L.lexeme sc
symbol     = L.symbol sc
char c     = lexeme (C.char c)
parens p   = lexeme (char '(' *> p <* char ')')
brackets p = lexeme (char '{' *> p <* char '}')
keywords   = HS.fromList ["let", "in"]

pIdent = try $ lexeme $ do
  w ← some C.alphaNumChar
  if HS.member w keywords
    then empty
    else pure w

pBind    = pIdent <|> symbol "_"
pVar     = Varᴾ <$> pIdent
pU       = Uᴾ <$ char '*'
pHole    = Holeᴾ <$ char '_'

pLamBinder ∷ Parser (Name, Either Name Icit)
pLamBinder =
      ((,Right Expl) <$> pBind)
  <|> try ((,Right Impl) <$> brackets pBind)
  <|> brackets ((\x y → (y, Left x)) <$> (pIdent <* char '=') <*> pBind)

pLam ∷ Parser Tmᴾ
pLam = do
  char 'λ'
  binders ← some pLamBinder
  char '.'
  t ← pTm
  pure (foldr (\(x, i) u → Lamᴾ x i u) t binders)

pArg ∷ Parser (Maybe (Tmᴾ, Either Name Icit))
pArg =
      (Just <$>
        (    try ((,Right Impl) <$> brackets pTm)
         <|> brackets ((\x t → (t, Left x)) <$> (pIdent <* char '=') <*> pTm)
         <|> ((,Right Expl) <$> pAtom)))
  <|> (Nothing <$ char '!')

pSpine ∷ Parser Tmᴾ
pSpine = do
  head  ← pAtom
  spine ← many pArg
  pure (foldl' (\t → maybe (NoMIᴾ t) (\(u, i) → Appᴾ t u i)) head spine)

pPiBinder ∷ Parser ([Name], Tmᴾ, Icit)
pPiBinder =
      brackets ((,,Impl) <$> some pBind <*> ((char ':' *> pTm) <|> pure Holeᴾ))
  <|> parens ((,,Expl) <$> some pBind <*> (char ':' *> pTm))

pPi ∷ Parser Tmᴾ
pPi = do
  dom ← try (Right <$> some pPiBinder) <|> (Left <$> pSpine)
  symbol "→"
  b ← pTm
  case dom of
    Right binders →
      pure (foldr (\(xs, a, i) b → foldr (\x → Piᴾ x i a) b xs) b binders)
    Left dom →
      pure (Piᴾ "_" Expl dom b)

pLet ∷ Parser Tmᴾ
pLet = Letᴾ
      <$> (symbol "let" *> pIdent)
      <*> (char ':' *> pTm)
      <*> (char '=' *> pTm)
      <*> (symbol "in" *> pTm)

pAtom ∷ Parser Tmᴾ
pAtom = pU <|> pVar <|> pHole <|> parens pTm

pTm ∷ Parser Tmᴾ
pTm = pLam <|> pLet <|> try pPi <|> pSpine

parseTmᴾ ∷ String → String → Either (ParseError Char Void) Tmᴾ
parseTmᴾ = parse (sc *> pTm <* eof)

--------------------------------------------------------------------------------

icit :: Icit → a → a → a
icit Impl i e = i
icit Expl i e = e

-- Printing
--------------------------------------------------------------------------------

prettyTmᴾ :: Int → Tmᴾ → ShowS
prettyTmᴾ prec = go (prec /= 0) where

  bracket :: ShowS → ShowS
  bracket s = ('{':).s.('}':)

  goArg ∷ Tmᴾ → Either Name Icit → ShowS
  goArg t (Left x)  = bracket ((x++) . (" = "++) . go False t)
  goArg t (Right i) = icit i (bracket (go False t)) (go True t)

  goPiBind ∷ Name → Icit → Tmᴾ → ShowS
  goPiBind x i a =
    icit i bracket (showParen True) ((x++) . (" : "++) . go False a)

  goLamBind ∷ Name → Either Name Icit  → ShowS
  goLamBind x (Left x') = bracket ((x'++) . (" = "++) . (x++))
  goLamBind x (Right i) = icit i bracket id (x++)

  goLam ∷ Tmᴾ → ShowS
  goLam (Lamᴾ x i t) = (' ':) . goLamBind x i . goLam t
  goLam t           = (". "++) . go False t

  goPi ∷ Bool → Tmᴾ → ShowS
  goPi p (Piᴾ x i a b)
    | i == Impl || x /= "_" = goPiBind x i a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of Appᴾ{} → False; _ → True) a .
       (" → "++) . go False b
  goPi p t = (if p then (" → "++) else id) . go False t

  go ∷ Bool → Tmᴾ → ShowS
  go p = \case
    Varᴾ x → (x++)
    Appᴾ (Appᴾ t u i) u' i' →
      showParen p (go False t . (' ':) . goArg u i . (' ':) . goArg u' i')
    Appᴾ (NoMIᴾ t) u i →
      showParen p (go False t . (" ! "++) . goArg u i)
    Appᴾ t u i  → showParen p (go True t . (' ':) . goArg u i)
    Lamᴾ x i t  → showParen p (("λ "++) . goLamBind x i . goLam t)
    Piᴾ x i a b → showParen p (goPi False (Piᴾ x i a b))
    Letᴾ x a t u →
      ("let "++) . (x++) . (" : "++) . go False a . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False  u
    Uᴾ      → ('*':)
    Holeᴾ   → ('?':)
    NoMIᴾ t → showParen p (go False t . (" !"++))

instance Show Tmᴾ where showsPrec = prettyTmᴾ
