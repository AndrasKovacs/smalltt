
module Presyntax (
    Name
  , Tmᴾ
  , Tmᴾ'(..)
  , Icit(..)
  , parseTmᴾ
  , icit
  , Posed
  ) where

import Control.Applicative hiding (many, some)
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
data Icit = Expl | Impl deriving (Eq)

instance Show Icit where
  show Expl = "explicit"
  show Impl = "implicit"

type Tmᴾ = (SourcePos, Tmᴾ')

data Tmᴾ'
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

type Posed a = (SourcePos, a)

withPos ∷ Parser a → Parser (Posed a)
withPos p = (,) <$> getPosition <*> p

pBind    = pIdent <|> symbol "_"
pVar     = withPos (Varᴾ <$> pIdent)
pU       = withPos (Uᴾ <$ char '*')
pHole    = withPos (Holeᴾ <$ char '_')

pLamBinder ∷ Parser (Posed (Name, Either Name Icit))
pLamBinder =
  withPos (
      ((,Right Expl) <$> pBind)
  <|> try ((,Right Impl) <$> brackets pBind)
  <|> brackets ((\x y → (y, Left x)) <$> (pIdent <* char '=') <*> pBind))

pLam ∷ Parser Tmᴾ
pLam = withPos $ do
  char 'λ' <|> char '\\'
  binders ← some pLamBinder
  char '.'
  t ← pTm
  pure $ snd $ foldr (\(p, (x, i)) u → (p, Lamᴾ x i u)) t binders

pArg ∷ Parser (Posed (Maybe (Tmᴾ, Either Name Icit)))
pArg = withPos (
      (Just <$>
        (    try ((,Right Impl) <$> brackets pTm)
         <|> brackets ((\x t → (t, Left x)) <$> (pIdent <* char '=') <*> pTm)
         <|> ((,Right Expl) <$> pAtom)))
  <|> (Nothing <$ char '!'))

pSpine ∷ Parser Tmᴾ
pSpine = withPos $ do
  head  ← pAtom
  spine ← many pArg
  pure $ snd $
    foldl' (\t (p, u) → (p, maybe (NoMIᴾ t) (\(u, i) → Appᴾ t u i) u)) head spine

pPiBinder ∷ Parser (Posed ([Posed Name], Tmᴾ, Icit))
pPiBinder = withPos (
      brackets ((,,Impl) <$> some (withPos pBind) <*> ((char ':' *> pTm) <|> withPos (pure Holeᴾ)))
  <|> parens ((,,Expl) <$> some (withPos pBind) <*> (char ':' *> pTm)))

pPi ∷ Parser Tmᴾ
pPi = withPos $ do
  dom ← try (Right <$> some pPiBinder) <|> (Left <$> pSpine)
  symbol "→" <|> symbol "->"
  b ← pTm
  case dom of
    Right binders → do
      pure $ snd $ foldr (\(p, (xs, a, i)) b → foldr (\(p, x) b → (p, Piᴾ x i a b)) b xs) b binders
    Left dom → do
      pure (Piᴾ "_" Expl dom b)

pLet ∷ Parser Tmᴾ
pLet = withPos (Letᴾ
  <$> (symbol "let" *> pIdent)
  <*> (char ':' *> pTm)
  <*> (char '=' *> pTm)
  <*> (symbol "in" *> pTm))

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

-- TODO: make Tmᴾ Cofree comonad or somemthing like that

prettyTmᴾ' :: Int → Tmᴾ' → ShowS
prettyTmᴾ' prec = go (prec /= 0) where

  bracket :: ShowS → ShowS
  bracket s = ('{':).s.('}':)

  goArg ∷ Tmᴾ' → Either Name Icit → ShowS
  goArg t (Left x)  = bracket ((x++) . (" = "++) . go False t)
  goArg t (Right i) = icit i (bracket (go False t)) (go True t)

  goPiBind ∷ Name → Icit → Tmᴾ' → ShowS
  goPiBind x i a =
    icit i bracket (showParen True) ((x++) . (" : "++) . go False a)

  goLamBind ∷ Name → Either Name Icit  → ShowS
  goLamBind x (Left x') = bracket ((x'++) . (" = "++) . (x++))
  goLamBind x (Right i) = icit i bracket id (x++)

  goLam ∷ Tmᴾ' → ShowS
  goLam (Lamᴾ x i (snd → t)) = (' ':) . goLamBind x i . goLam t
  goLam t                    = (". "++) . go False t

  goPi ∷ Bool → Tmᴾ' → ShowS
  goPi p (Piᴾ x i (snd → a) (snd → b))
    | i == Impl || x /= "_" = goPiBind x i a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of Appᴾ{} → False; _ → True) a .
       (" → "++) . go False b
  goPi p t = (if p then (" → "++) else id) . go False t

  go ∷ Bool → Tmᴾ' → ShowS
  go p = \case
    Varᴾ x → (x++)
    Appᴾ (snd → Appᴾ (snd → t) (snd → u) i) (snd → u') i' →
      showParen p (go False t . (' ':) . goArg u i . (' ':) . goArg u' i')
    Appᴾ (snd → NoMIᴾ (snd → t)) (snd → u) i →
      showParen p (go False t . (" ! "++) . goArg u i)
    Appᴾ (snd → t) (snd → u) i  → showParen p (go True t . (' ':) . goArg u i)
    Lamᴾ x i (snd → t)  → showParen p (("λ "++) . goLamBind x i . goLam t)
    Piᴾ x i a b → showParen p (goPi False (Piᴾ x i a b))
    Letᴾ x (snd → a) (snd → t) (snd → u) →
      ("let "++) . (x++) . (" : "++) . go False a . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False  u
    Uᴾ      → ('*':)
    Holeᴾ   → ('?':)
    NoMIᴾ (snd → t) → showParen p (go False t . (" !"++))

instance Show Tmᴾ' where showsPrec = prettyTmᴾ'
