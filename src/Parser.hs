{-# language UnboxedTuples, UnboxedSums, OverloadedStrings #-}

module Parser (src, parse, parseString, parseFile) where

import FlatParse.Stateful hiding (Parser, runParser, string, cut)
import qualified Data.ByteString as B

import Common
import Presyntax
import Lexer

-- keywords & identifiers
--------------------------------------------------------------------------------

colon   = $(symbol ":")
colon'  = $(symbol' ":")
semi    = $(symbol ";")
semi'   = $(symbol' ";")
braceL  = $(symbol "{")
braceR' = $(symbol' "}")
dot'    = $(symbol' ".")
eq      = $(symbol  "=")
eq'     = $(symbol' "=")
parR'   = $(symbol' ")")
arrow   = token $(switch [| case _ of "->" -> pure (); "→" -> pure () |])
arrow'  = token' $(switch [| case _ of "->" -> pure (); "→" -> pure () |])

isKeyword :: Span -> Parser ()
isKeyword span = inSpan span do
  $(switch [| case _ of
     "let"  -> pure ()
     "λ"    -> pure ()
     "U"    -> pure ()
     |])
  eof

scanIdent :: Parser ()
scanIdent = identStartChar >> manyIdentChars

identBased :: (Span -> Parser a) -> Parser a
identBased k = spanned scanIdent \_ x -> do
  fails (isKeyword x)
  ws
  k x
{-# inline identBased #-}

idented :: (Span -> Parser a) -> Parser a
idented k = lvl >> identBased k
{-# inline idented #-}

idented' :: (Span -> Parser a) -> Parser a
idented' k = lvl' >> identBased k `cut'` Msg "identifier"
{-# inline idented' #-}

skipToVar :: Pos -> (Pos -> Parser Tm) -> Parser Tm
skipToVar l k = branch identChar
  (do {manyIdentChars; r <- getPos; ws; pure $ Var (Span l r)})
  (do {r <- getPos; ws; k r})
{-# inline skipToVar #-}

-- atomic expressions
--------------------------------------------------------------------------------

atomBase :: Parser Tm
atomBase = do
  l <- getPos
  $(switch [| case _ of
    "("    -> ws *> tm' <* parR'
    "_"    -> ws >> pure (Hole l)
    "let"  -> skipToVar l \_ -> empty
    "λ"    -> skipToVar l \_ -> empty
    "U"    -> skipToVar l \_ -> pure $ U l
    _      -> do {identStartChar; manyIdentChars; r <- getPos; ws; pure (Var (Span l r))}
            |])

atom :: Parser Tm
atom = lvl >> atomBase

atom' :: Parser Tm
atom' = lvl' >> atomBase `cut` [Msg "atomic expression"]

-- application
--------------------------------------------------------------------------------

skipToApp :: Pos -> (Pos -> Parser Tm) -> Parser Tm
skipToApp l p = branch identChar
  (do {manyIdentChars; r <- getPos; ws; goApp (Var (Span l r))})
  (do {r <- getPos; ws; p r})
{-# inline skipToApp #-}

goApp :: Tm -> Parser Tm
goApp t = branch braceL
  ((idented \x -> do
     eq
     u <- tm'
     braceR'
     goApp (App t u (Named x)))
    <|>
   (do u <- tm'
       braceR'
       goApp (App t u (NoName Impl))))
  (optioned atom
     (\u -> goApp (App t u (NoName Expl)))
     (pure t))

app' :: Parser Tm
app' = goApp =<< atom'


-- Pi
--------------------------------------------------------------------------------

data Spans = SNil | SCons {-# unpack #-} Span Spans

manyIdents :: Parser Spans
manyIdents = go SNil where
  go acc = (idented \x -> go (SCons x acc)) <|> pure acc

spansToImplPi :: Pos -> Tm -> Tm -> Spans -> Tm
spansToImplPi l a acc = \case
  SNil       -> acc
  SCons x xs -> spansToImplPi l a (Pi l (BSpan x) Impl a acc) xs

spansToApps :: Span -> Spans -> Tm
spansToApps x = \case
  SNil        -> Var x
  SCons x' xs -> App (spansToApps x xs) (Var x') (NoName Expl)

piBrace :: Pos -> Parser Tm
piBrace pos = idented \x -> do
  holepos <- getPos
  $(switch [| case _ of
    ":" -> ws >> do
      a <- tm' <* braceR'
      optional_ arrow
      Pi pos (BSpan x) Impl a <$> pi'
    "}" -> ws >> do
      let a = Hole holepos
      optional_ arrow
      Pi pos (BSpan x) Impl (Hole holepos) <$> pi'
    _ -> do
      b <- piBrace pos
      case b of
        Pi _ _ _ a _ -> do
          pure $ Pi pos (BSpan x) Impl a b
        _ ->
          impossible
    |])

pi' :: Parser Tm
pi' = do
  l <- getPos
  lvl' >> $(switch [| case _ of

    "{" -> ws >>
      piBrace l

    "(" -> ws >>
      (idented \x -> do
        xs <- manyIdents
        $(switch [| case _ of

          ":" -> ws >> do
            a <- tm' <* parR'
            optional_ arrow
            b <- pi'
            pure $! (Pi l (BSpan x) Expl a $! spansToImplPi l a b xs)

          ")" -> ws >> do
            let t = spansToApps x xs
            branch arrow
              (goApp t)
              (Pi l BEmpty Expl t <$> pi')

          _ ->
            branch arrow
              (do a <- Pi l BEmpty Expl (spansToApps x xs) <$> (pi' <* parR')
                  branch arrow
                    (Pi l BEmpty Expl a <$> pi')
                    (pure a))
              (do a <- goApp (spansToApps x xs) <* parR'
                  branch arrow
                    (Pi l BEmpty Expl a <$> pi')
                    (pure a))
             |]))
       <|>
       (do t <- tm' <* parR'
           branch arrow
             (Pi l BEmpty Expl t <$> pi')
             (pure t))

    _   -> ws >> do
      t <- app'
      branch arrow
        (Pi l BEmpty Expl t <$> pi')
        (pure t)
    |])


-- Lambda
--------------------------------------------------------------------------------

goLamBraceL :: Pos -> Parser Tm
goLamBraceL pos = do
  ws
  branch $(symbol "_")
    (uoptioned (colon *> tm') \a -> do
        Lam pos BEmpty (NoName Impl) a <$> (braceR' *> goLam))
    (idented' \x -> do
        branch eq
          (idented' \y ->
             Lam pos (BSpan y) (Named x) UNothing <$> (braceR' *> goLam))
          (uoptioned (colon *> tm') \a ->
            Lam pos (BSpan x) (NoName Impl) a <$> (braceR' *> goLam)))

goLamParL :: Pos -> Parser Tm
goLamParL pos = do
  ws
  idented' \x -> do
    a <- colon' *> tm' <* parR'
    Lam pos (BSpan x) (NoName Expl) (UJust a) <$> goLam

goLam :: Parser Tm
goLam = do
  pos <- getPos
  lvl' >> $(switch [| case _ of
    "{" -> goLamBraceL pos
    "(" -> goLamParL pos
    "." -> ws >> tm'
    "_" -> ws >> Lam pos BEmpty (NoName Expl) UNothing <$> goLam
    _   -> ws >> idented' \x -> Lam pos (BSpan x) (NoName Expl) UNothing <$> goLam
      |])

lam' :: Pos -> Parser Tm
lam' pos = lvl' >> $(switch [| case _ of
  "{" -> goLamBraceL pos
  "(" -> goLamParL pos
  "_" -> ws >> Lam pos BEmpty (NoName Expl) UNothing <$> goLam
  _   -> ws >> idented' \x -> Lam pos (BSpan x) (NoName Expl) UNothing <$> goLam
    |])

-- terms
--------------------------------------------------------------------------------

pLet' :: Pos -> Parser Tm
pLet' l =
  idented' \x ->
  uoptioned (colon `notFollowedBy` eq *> tm') \a -> do
    eq'
    t <- tm'
    semi'
    u <- tm'
    pure $ Let l x a t u
{-# inline pLet' #-}

tm' :: Parser Tm
tm' = (do
  l <- getPos
  lvl' >> $(switch [| case _ of
    "λ"    -> skipToApp l \_ -> lam' l
    "\\"   -> ws >> lam' l
    "let"  -> skipToApp l \_ -> pLet' l
    _      -> ws >> pi' |]))
  `cut` [Msg "lambda expression", "let-definition"]

--------------------------------------------------------------------------------

topDef :: Span -> Parser TopLevel
topDef x = local (const 1) do
  uoptioned (colon `notFollowedBy` eq *> tm') \a -> do
    eq'
    rhs <- tm'
    local (const 0) (Definition x a rhs <$> top)

top :: Parser TopLevel
top =  (exactLvl 0 >> idented topDef)
   <|> (Nil <$ eof `cut` [Msg "end of file", Msg "top-level definition at column 1"])

--------------------------------------------------------------------------------

src :: Parser TopLevel
src = ws *> top

parse :: B.ByteString -> Result Error TopLevel
parse = runParser src

parseFile :: String -> IO (B.ByteString, Result Error TopLevel)
parseFile path = do
  src <- B.readFile path
  let res = parse src
  pure (src, res)

parseString :: String -> (B.ByteString, Result Error TopLevel)
parseString  (packUTF8 -> str) = (str, parse str)
