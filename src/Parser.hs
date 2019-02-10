
module Parser (parseFile, parseTm) where

import Control.Applicative hiding (many, some)
import Control.Monad.Reader
import Data.Char
import Data.Void

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
indentMore :: Parser a -> (a -> Parser b) -> Parser b
indentMore ref p = do
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
brackets p = char '[' *> p <* char ']'
braces p = char '{' *> p <* char '}'

keyword :: Text -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U"


-- Parsing
--------------------------------------------------------------------------------

pIdent :: Parser Name
pIdent = try $ lexeme $ do
  o   <- getOffset
  txt <- takeWhile1P Nothing (\c -> isAlphaNum c || c == '-' || c == '\'')
  unless (isAlpha $ T.head txt) $
    failWithOffset o "identifier must start with an alphabetic character"
  when (keyword txt) $
    failWithOffset o $ printf "unexpected keyword \"%s\", expected an identifier" txt
  pure (TS.fromText txt)

withPos :: Parser a -> Parser (Posed a)
withPos p = Posed <$> getSourcePos <*> p

pBind    = pIdent <|> (mempty @Name <$ char '_')
pVar     = withPos (Var <$> pIdent)
pU       = withPos (U <$ char 'U')
pHole    = withPos (Hole <$ char '_')

pLamBinder :: Parser (Posed (Named NameOrIcit))
pLamBinder = withPos (
      (flip Named NOExpl <$> pBind)
  <|> try (flip Named NOImpl <$> braces pBind)
  <|> braces ((\x y → Named y (NOName x)) <$> (pIdent <* char '=') <*> pBind))

pLam :: Parser Tm
pLam = withPos $ do
  satisfy (\c -> c == 'λ' || c == '\\')
  unPosed <$> chainr1 (\(Posed p (Named x ni)) t -> Posed p (Lam x ni t))
                    pLamBinder
                    (char '.' *> pTm)

-- | Parse a spine argument or meta insertion stopping.
pArg :: Parser (Maybe (T2 Tm (Posed NameOrIcit)))
pArg =
      (Just <$> (
            try (do {t <- braces pTm; pure (T2 t (Posed (posOf t) NOImpl))})
        <|> braces (do
              i <- withPos (NOName <$> (pIdent <* char '='))
              t <- pTm
              pure (T2 t i))
        <|> (do {t <- pAtom; pure (T2 t (Posed (posOf t) NOExpl))})))
  <|> (Nothing <$ char '!')

pSpine :: Parser Tm
pSpine = chainl
  (\t -> maybe (Posed (posOf t) (StopMetaIns t))
               (\(T2 u (Posed p ni)) -> Posed (posOf t) (App t u ni)))
  pArg
  pAtom

pInfer :: Parser Text
pInfer = lexeme (takeWhile1P Nothing (=='─'))

pColon :: Parser ()
pColon = char ':' *> void (optional pInfer)

pArrow :: Parser Text
pArrow =
      symbol "->"
  <|> symbol "→"
  <|> pInfer

pLet :: Parser Tm
pLet = withPos $ do
  symbol "let"
  T3 x a t <- indentMore (withPos pIdent) $ \(Posed pos x) -> do
    a <- optional (pColon *> pTm)
    t <- char '=' *> pTm
    case a of
      Just a  -> pure (T3 x a t)
      Nothing -> pure (T3 x (Posed pos Hole) t)
  u <- symbol "in" *> pTm
  pure (Let x a t u)

pBraceBinder =
      braces ((\x y -> T3 x y Impl)
  <$> some (withPos pBind)
  <*> ((pColon *> pTm) <|> withPos (pure Hole)))

pParenBinder =
      parens ((\x y -> T3 x y Expl)
  <$> some (withPos pBind)
  <*> (pColon *> pTm))

pPiBinder :: Parser (Posed (T3 [Posed Name] Tm Icit))
pPiBinder = withPos (pBraceBinder <|> pParenBinder)

pPi :: Parser Tm
pPi =
  chainr1
    (\(Posed p (T3 xs a i)) b ->
         Posed p (unPosed $ foldr (\(Posed p x) b -> Posed p (Pi (Named x i) a b)) b xs))
    pPiBinder
    (pArrow *> pTm)

pFunOrSpine :: Parser Tm
pFunOrSpine = do
  Posed pos sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure (Posed pos sp)
    Just{}  -> do
      b <- pTm
      pure (Posed pos (Fun (Posed pos sp) b))

pAtom :: Parser Tm
pAtom = pU <|> pVar <|> pHole <|> parens pTm

pTm :: Parser Tm
pTm = pLam <|> pLet <|> try pPi <|> pFunOrSpine

pRewrite :: Parser TopEntry
pRewrite = nonIndented $ do
  indentMore (([] <$ symbol "{}") <|> some (withPos pBraceBinder)) $ \bs -> do
    let bs' :: [Posed (Named Ty)]
        bs' = [Posed pos (Named n a) | Posed _ (T3 ns a _) <- bs, Posed pos n <- ns]
    pArrow
    lhs <- pTm
    char '='
    rhs <- pTm
    pure (TERewrite bs' lhs rhs)

pProfiling :: Parser (Maybe Profiling)
pProfiling = optional $ brackets $
  (PElabTime <$ symbol "elaborate") <|> (PNormalizeTime <$ symbol "normalize")

pPostulateOrDefinition :: Parser TopEntry
pPostulateOrDefinition = nonIndented $ indentMore (withPos pIdent) $ \x@(Posed pos _) -> do
  profiling <- pProfiling
  a <- optional (pColon *> pTm)
  t <- optional (char '=' *> pTm)
  case t of
    Just t  -> case a of
      Just a  -> pure (TEDefinition x profiling a t)
      Nothing -> pure (TEDefinition x profiling (Posed pos Hole) t)
    Nothing -> case a of
      Just a -> case  profiling of
        Nothing -> pure (TEPostulate x a)
        _       -> fail "No profiling options are available for postulates"
      _      -> fail "expected a postulate or a definition"

pProgram :: Parser Program
pProgram = many (pPostulateOrDefinition <|> pRewrite)

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
--   "{}  -> plus zero    = λ m. m"
--    ]
