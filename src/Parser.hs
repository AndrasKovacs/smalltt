{-# language UnboxedTuples, UnboxedSums #-}

module Parser (src, parse, parseString, parseFile) where

import FlatParse.Stateful hiding (Parser, runParser, string, cut)
import qualified Data.ByteString as B

import Common
import Presyntax
import Lexer

--------------------------------------------------------------------------------

-- problems:
--  - reboxing in UMaybe and Span results
--  - random cruft

-- atoms
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

bind :: Parser Bind
bind = branch $(symbol "_") (pure DontBind) (Bind <$> identBased pure)

bind' :: Parser Bind
bind' = branch $(symbol' "_") (pure DontBind) (Bind <$> identBased pure)
        `cut'` Msg "binder"

data Spans = SNil | SCons {-# unpack #-} Span Spans

foldrSpans :: forall b. (Span -> b -> b) -> b -> Spans -> b
foldrSpans f b xs = go xs where
  go SNil         = b
  go (SCons x xs) = f x $! go xs
{-# inline foldrSpans #-}

manyIdents :: Parser Spans
manyIdents =
      (idented \x -> SCons x <$> manyIdents)
  <|> pure SNil

someIdented :: (Span -> Spans -> Parser a) -> Parser a
someIdented k = idented \x -> do {xs <- manyIdents; k x xs}
{-# inline someIdented #-}

pi' :: Parser Tm
pi' = do
  l <- getPos
  lvl' >> $(switch [| case _ of

    "{" -> ws >>
      someIdented \x xs -> do
        holepos <- getPos
        a <- optioned (colon *> tm') pure (pure (Hole holepos))
        braceR'
        optional_ arrow
        b <- pi'
        let !res = foldrSpans (\x@(Span x1 x2) -> Pi x1 (Bind x) Impl a) b xs
        pure $! Pi l (Bind x) Impl a res

    "(" -> ws >>
      (someIdented \x xs -> do
          colon
          a <- tm' <* parR'
          optional_ arrow
          b <- pi'
          let !res = foldrSpans (\x@(Span x1 x2) -> Pi x1 (Bind x) Expl a) b xs
          pure $! Pi l (Bind x) Expl a res)
      <|>
      (do t <- tm' <* parR'
          branch arrow
            (Pi l DontBind Expl t <$> pi')
            (pure t))

    _   -> ws >> do
      t <- app'
      branch arrow (Pi l DontBind Expl t <$> pi') (pure t)
    |])

goLamBraceL :: Pos -> Parser Tm
goLamBraceL pos = do
  ws
  branch $(symbol "_")
    (uoptioned (colon *> tm') \a -> do
        Lam pos DontBind (NoName Impl) a <$> (braceR' *> goLam))
    (idented' \x -> do
        branch eq
          (idented' \y ->
             Lam pos (Bind y) (Named x) UNothing <$> (braceR' *> goLam))
          (uoptioned (colon *> tm') \a ->
            Lam pos (Bind x) (NoName Impl) a <$> (braceR' *> goLam)))

goLamParL :: Pos -> Parser Tm
goLamParL pos = do
  ws
  idented' \x -> do
    a <- colon' *> tm' <* parR'
    Lam pos (Bind x) (NoName Expl) (UJust a) <$> goLam

goLam :: Parser Tm
goLam = do
  pos <- getPos
  lvl' >> $(switch [| case _ of
    "{" -> goLamBraceL pos
    "(" -> goLamParL pos
    "." -> ws >> tm'
    "_" -> ws >> Lam pos DontBind (NoName Expl) UNothing <$> goLam
    _   -> ws >> idented' \x -> Lam pos (Bind x) (NoName Expl) UNothing <$> goLam
      |])

lam' :: Pos -> Parser Tm
lam' pos = lvl' >> $(switch [| case _ of
  "{" -> goLamBraceL pos
  "(" -> goLamParL pos
  "_" -> ws >> Lam pos DontBind (NoName Expl) UNothing <$> goLam
  _   -> ws >> idented' \x -> Lam pos (Bind x) (NoName Expl) UNothing <$> goLam
    |])

pLet' :: Pos -> Parser Tm
pLet' l =
  idented' \x ->
  uoptioned (colon `notFollowedBy` eq *> tm') \a -> do
    eq'
    t <- tm'
    semi'
    u <- tm'
    pure $ Let l x a t u

tmBase :: Parser Tm
tmBase = do
  l <- getPos
  $(switch [| case _ of
    "λ"    -> skipToApp l \_ -> lam' l
    "\\"   -> ws >> lam' l
    "let"  -> skipToApp l \_ -> pLet' l
    _      -> ws >> pi' |])
{-# inline tmBase #-}

tm' :: Parser Tm
tm' = lvl' >> tmBase `cut` [Msg "lambda expression", "let-definition"]


--------------------------------------------------------------------------------

topDef :: Span -> Parser TopLevel
topDef x = local (const 1) do
  uoptioned (colon `notFollowedBy` eq *> tm') \a -> do
    eq'
    rhs <- tm'
    local (const 0) (Definition x a rhs <$> top)

top :: Parser TopLevel
top =  (exactLvl 0 >> (idented pure >>= topDef))
   <|> (Nil <$ eof `cut` [Msg "top-level definition at column 1"])

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
