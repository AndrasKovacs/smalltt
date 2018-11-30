
module Parser (parseFile, parseTm) where

import Control.Applicative hiding (many, some)
import Control.Monad.Reader
import Data.Char
import Data.Void
import Data.Nullable

import qualified Data.Set as Set

import           Data.Text (Text)
import qualified Data.Text       as T
import qualified Data.Text.Short as TS

import qualified Text.Megaparsec
import           Text.Megaparsec.Internal (ParsecT(..))
import           Text.Megaparsec hiding (satisfy)
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Text.Printf

import Common
import Presyntax

--------------------------------------------------------------------------------

-- | The `ReaderT` stores indentation level.
type Parser = ReaderT Pos (Parsec Void Text)


-- Extra combinators
--------------------------------------------------------------------------------

-- | Parse a starting value, then zero or more elements.
--   Combine the results with a function in a left-associated way.
chainl :: (Alternative m, Monad m) => (b -> a -> b) -> m a -> m b -> m b
chainl f elem start = start >>= go where
  go b = do {a <- elem; go (f b a)} <|> pure b
{-# inline chainl #-}

-- | Parse one or more elements, then parse an ending value.
--   Combine result with a function in a right-associated way.
chainr1 :: Alternative m => (a -> b -> b) -> m a -> m b -> m b
chainr1 f elem end = (\a rest -> f a rest) <$> elem <*> go where
  go = ((\a rest -> f a rest) <$> elem <*> go)
       <|> end
{-# inline chainr1 #-}

failWithOffset :: Int -> String -> Parser a
failWithOffset o msg = lift (ParsecT $ \s _ _ _ eerr ->
  eerr (FancyError o (Set.singleton (ErrorFail msg))) s)
{-# inline failWithOffset #-}

-- Indentation
--------------------------------------------------------------------------------

indentError :: Parser a
indentError = fail "incorrect indentation"
{-# noinline indentError #-}

indentedAt :: Pos -> Parser a -> Parser a
indentedAt level p = do
  actual <- L.indentLevel
  unless (actual == level) indentError
  p

nonIndented :: Parser a -> Parser a
nonIndented = indentedAt (mkPos 1)

-- | Parse a reference value, then parse something else which must be
--   more indented than the reference.
indent :: Parser a -> (a -> Parser b) -> Parser b
indent ref p = do
  lvl <- L.indentLevel
  a   <- ref
  local (const (lvl <> mkPos 1)) (p a)


-- Lexing
--------------------------------------------------------------------------------

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")
{-# inline ws #-}

-- | We check indentation before reading a token, and consume whitespace
--   after the token.
lexeme :: Parser a -> Parser a
lexeme p = do
  level  <- ask
  actual <- L.indentLevel
  if (actual < level)
    then indentError
    else p <* ws
{-# inline lexeme #-}

symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
satisfy f  = lexeme (Text.Megaparsec.satisfy f)
parens p   = char '(' *> p <* char ')'
brackets p = char '{' *> p <* char '}'

keyword :: Text -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U" || x == "assume"


-- Parsing
--------------------------------------------------------------------------------

pIdent :: Parser Name
pIdent = try $ lexeme $ do
  o   <- getOffset
  txt <- takeWhile1P Nothing isAlphaNum
  unless (isAlpha $ T.head txt) $
    failWithOffset o "identifier must start with an alphabetic character"
  when (keyword txt) $
    failWithOffset o $ printf "unexpected keyword \"%s\", expected an identifier" txt
  pure (TS.fromText txt)

withPos :: Parser a -> Parser (Posed a)
withPos p = T2 <$> getSourcePos <*> p

pBind    = pIdent <|> (mempty @Name <$ char '_')
pVar     = withPos (Var <$> pIdent)
pU       = withPos (U <$ char 'U')
pHole    = withPos (Hole <$ char '_')

pLamBinder :: Parser (Posed (T2 Name (Sum Name Icit)))
pLamBinder = withPos (
      (flip T2 (Inr Expl) <$> pBind)
  <|> try (flip T2 (Inr Impl) <$> brackets pBind)
  <|> brackets ((\x y → T2 y (Inl x)) <$> (pIdent <* char '=') <*> pBind))

pLam :: Parser Tm
pLam = withPos $ do
  satisfy (\c -> c == 'λ' || c == '\\')
  proj2 <$> chainr1 (\(T2 p (T2 x ni)) t -> T2 p (Lam x ni t))
                    pLamBinder
                    (char '.' *> pTm)

-- | Parse a spine argument or meta insertion stopping.
pArg :: Parser (Posed (Nullable (T2 Tm (Sum Name Icit))))
pArg = withPos (
      (Some <$> (
            try (flip T2 (Inr Impl) <$> brackets pTm)
        <|> brackets ((\x t -> T2 t (Inl x)) <$> (pIdent <* char '=') <*> pTm)
        <|> (flip T2 (Inr Expl) <$> pAtom)))
  <|> (Null <$ char '!'))

pSpine :: Parser Tm
pSpine = chainl
  (\t (T2 p u) -> T2 p (nullable (StopMetaIns t) (\(T2 u ni) -> App t u ni) u))
  pArg
  pAtom

pPiBinder :: Parser (Posed (T3 [Posed Name] Tm Icit))
pPiBinder = withPos (
      brackets ((\x y -> T3 x y Impl)
                <$> some (withPos pBind)
                <*> ((char ':' *> pTm) <|> withPos (pure Hole)))
  <|> parens ((\x y -> T3 x y Expl)
                <$> some (withPos pBind)
                <*> (char ':' *> pTm)))

pArrow :: Parser Text
pArrow = symbol "->" <|> symbol "→"

pPi :: Parser Tm
pPi = try (chainr1
             (\(T2 p (T3 xs a i)) b ->
                 T2 p (proj2 $ foldr (\(T2 p x) b -> T2 p (Pi (NI x i) a b)) b xs))
             pPiBinder
             (pArrow *> pTm))
  <|> (withPos (Pi (NI mempty Expl) <$> pSpine <*> (pArrow *> pTm)))

pLet :: Parser Tm
pLet = withPos $ do
  symbol "let"
  T3 x a t <- indent pIdent $ \x -> T3 x <$> (char ':' *> pTm) <*> (char '=' *> pTm)
  u <- symbol "in" *> pTm
  pure (Let x a t u)

pAtom :: Parser Tm
pAtom = pU <|> pVar <|> pHole <|> parens pTm

pTm :: Parser Tm
pTm = pLam <|> pLet <|> try pPi <|> pSpine

pPostulate :: Parser TopEntry
pPostulate = nonIndented $
  indent (symbol "assume") (\_ -> TEPostulate <$> withPos pIdent <*> (char ':' *> pTm))

pDefinition :: Parser TopEntry
pDefinition = nonIndented $ indent (withPos pIdent) $ \x -> do
  a <- optional (char ':' *> pTm)
  t <- char '=' *> pTm
  case a of
    Just a  -> pure (TEDefinition x a t)
    Nothing -> pure (TEDefinition x (T2 (proj1 x) Hole) t)

pProgram :: Parser Program
pProgram = many (pPostulate <|> pDefinition)

pFile :: Parser Program
pFile = ws *> pProgram <* eof

parseTm :: Text -> Either (ParseErrorBundle Text Void) Tm
parseTm = parse (runReaderT (ws *> pTm <* eof) (mkPos 1)) ""

parseFile :: String -> Text -> Either (ParseErrorBundle Text Void) Program
parseFile = parse (runReaderT pFile (mkPos 1))

--------------------------------------------------------------------------------

-- parseTest' :: Show a => Parser a -> Text -> IO ()
-- parseTest' p t = parseTest (runReaderT p (mkPos 1)) t

-- test = T.unlines [
--    "f : (x y z : U) -> U",
--    "f = \\ x y z. g !"
--    ]
