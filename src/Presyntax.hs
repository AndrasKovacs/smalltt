
module Presyntax (
    Name
  , Tmᴾ(..)
  , Icit(..)
  , parseTmᴾ
  , icit
  , freeInTmᴾ
  ) where

{-| TODO: Add source position information to Tmᴾ -}

import Control.Applicative
import Control.Monad
import Data.List
import Data.Void

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

freeInTmᴾ :: Name → Tmᴾ → Bool
freeInTmᴾ x = \case
  Varᴾ x'         → x == x'
  Appᴾ f a i      → freeInTmᴾ x f || freeInTmᴾ x a
  Lamᴾ x' i t     → if x == x' then False else freeInTmᴾ x t
  Piᴾ x' i a b    → freeInTmᴾ x a || if x == x' then False else freeInTmᴾ x b
  Letᴾ x' a t u   → freeInTmᴾ x a || freeInTmᴾ x t ||
                     if x == x' then False else freeInTmᴾ x u
  NoMIᴾ t         → freeInTmᴾ x t
  Uᴾ              → False
  Holeᴾ           → False

-- Printing
--------------------------------------------------------------------------------

splitSpine ∷ Tmᴾ → (Tmᴾ, [(Tmᴾ, Either Name Icit)])
splitSpine = \case
  Appᴾ f a i → ((a,i):) <$> splitSpine f
  t          → (t, [])

prettyTmᴾ ∷ Int → Tmᴾ → ShowS
prettyTmᴾ prec = go (prec /= 0) where

  unwords' ∷ [ShowS] → ShowS
  unwords' = foldr1 (\x acc → x . (' ':) . acc)

  lams ∷ (Name, Either Name Icit) → Tmᴾ → ([(Name, Either Name Icit)], Tmᴾ)
  lams xi t = go [xi] t where
    go xs (Lamᴾ x i t) = go ((x,i):xs) t
    go xs t            = (xs, t)

  bracket ∷ ShowS → ShowS
  bracket s = ('{':).s.('}':)

  goArg ∷ (Tmᴾ, Either Name Icit) → ShowS
  goArg (t, Left x)  = bracket ((x++) . (" = "++) . go False t)
  goArg (t, Right i) = icit i (bracket (go False t)) (go True t)

  goBinder ∷ (Name, Either Name Icit) → ShowS
  goBinder (x, Left x') = bracket ((x'++) . (" = "++) . (x++))
  goBinder (x, Right i) = icit i bracket id (x++)

  -- TODO: printing is kinda slow (make tmSpine return in reverse, optimize App case)
  go ∷ Bool → Tmᴾ → ShowS
  go p = \case
    Varᴾ x → (x++)
    t@Appᴾ{} → showParen p $ unwords' $ go True h : reverse (map goArg sp)
      where (h, sp) = splitSpine t
    Lamᴾ x i t → case lams (x, i) t of
      (xis, t) → showParen p (("λ "++) . params . (". "++) . go False t)
        where params = unwords' $ reverse $ map goBinder xis
    Piᴾ x i a b → showParen p (arg . (" → "++) . go False b)
      where
        arg = if freeInTmᴾ x b
                then (icit i bracket (showParen True)) ((x++) . (" : "++) . go False a)
                else go True a
    Letᴾ x a t u →
      ("let "++) . (x++) . (" : "++) . go False a . ("\n"++) .
      ("   "++) . (" = "++) . go False t  . ("\nin\n"++) .
      go False u
    Uᴾ      → ('*':)
    Holeᴾ   → ('?':)
    NoMIᴾ t → go False t . (" !"++)

instance Show Tmᴾ where showsPrec = prettyTmᴾ
