{-# language UnboxedTuples, UnboxedSums #-}

module Parser where

import Data.Foldable
import FlatParse.Stateful hiding (Parser, runParser, string, cut)
import qualified Data.ByteString as B
-- import Data.Char (ord)

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

identBase :: Parser Span
identBase = spanned (identStartChar >> manyIdents) \_ x -> do
  fails (isKeyword x)
  ws
  pure x

ident :: Parser Span
ident = lvl >> identBase

ident' :: Parser Span
ident' = lvl' >> identBase `cut'` Msg "identifier"

skipToVar :: Pos -> (Pos -> Parser Tm) -> Parser Tm
skipToVar l k = branch identChar
  (do {manyIdents; r <- getPos; ws; pure $ Var (Span l r)})
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
    _      -> do {identStartChar; manyIdents; r <- getPos; ws; pure (Var (Span l r))}
            |])

atom :: Parser Tm
atom = lvl >> atomBase

atom' :: Parser Tm
atom' = lvl' >> atomBase `cut` [Msg "atomic expression"]

skipToApp :: Pos -> (Pos -> Parser Tm) -> Parser Tm
skipToApp l p = branch identChar
  (do {manyIdents; r <- getPos; ws; goApp (Var (Span l r))})
  (do {r <- getPos; ws; p r})
{-# inline skipToApp #-}

goApp :: Tm -> Parser Tm
goApp t = branch braceL
  (do optioned (ident <* eq)
        (\x -> do
          u <- tm'
          braceR'
          goApp (App t u (Named x)))
        (do
          u <- tm'
          braceR'
          goApp (App t u (NoName Impl))))
  (pure t)

app' :: Parser Tm
app' = goApp =<< atom'

bind :: Parser Bind
bind = branch $(symbol "_") (pure DontBind) (Bind <$> identBase)

bind' :: Parser Bind
bind' = branch $(symbol' "_") (pure DontBind) (Bind <$> identBase)
        `cut'` Msg "binder"

pi' :: Parser Tm
pi' = do
  l <- getPos
  lvl' >> $(switch [| case _ of

    "{" -> ws >>
      some ident >>= \(x:xs) -> do
      holepos <- getPos
      a <- optioned (colon *> tm') pure (pure (Hole holepos))
      braceR'
      optional_ arrow
      b <- pi'
      let !res = foldr' (\x@(Span x1 x2) -> Pi x1 (Bind x) Impl a) b xs
      pure $! Pi l (Bind x) Impl a res

    "(" -> ws >> do
      optioned (some ident <* colon)
        (\(x:xs) -> do
            a <- tm' <* parR'
            optional_ arrow
            b <- pi'
            let !res = foldr' (\x@(Span x1 x2) -> Pi x1 (Bind x) Expl a) b xs
            pure $! Pi l (Bind x) Expl a res)
        (do t <- tm' <* parR'
            branch arrow
              (Pi l DontBind Expl t <$> pi')
              (pure t))

    _   -> ws >> do
      t <- app'
      branch arrow (Pi l DontBind Expl t <$> pi') (pure t)
    |])

goLam :: Parser Tm
goLam = do
  pos <- getPos
  lvl' >> $(switch [| case _ of

    "{" -> ws >> do
      branch $(symbol "_")
        (Lam pos DontBind (NoName Impl) <$> uoptional (colon *> tm') <*> (braceR' *> goLam))
        (do x <- ident'
            branch eq
              (do y <- ident'
                  Lam pos (Bind y) (Named x) UNothing <$> (braceR' *> goLam))
              (Lam pos (Bind x) (NoName Impl) <$> uoptional (colon *> tm') <*> (braceR' *> goLam)))

    "(" -> ws >> do
      x <- ident'
      a <- colon' *> tm' <* parR'
      Lam pos (Bind x) (NoName Expl) (UJust a) <$> goLam

    "." -> ws >> tm'
    "_" -> ws >> Lam pos DontBind (NoName Expl) UNothing <$> goLam

    _ -> ws >> do
      x <- lvl' >> identBase `cut` [Msg "binder", "."]
      Lam pos (Bind x) (NoName Expl) UNothing <$> goLam
      |])

lam' :: Pos -> Parser Tm
lam' pos = lvl' >> $(switch [| case _ of

  "{" -> ws >>
    branch $(symbol "_")
      (Lam pos DontBind (NoName Impl) <$> uoptional (colon *> tm') <*> (braceR' *> goLam))
      (do x <- ident'
          branch eq
            (do y <- ident'
                Lam pos (Bind y) (Named x) UNothing <$> (braceR' *> goLam))
            (Lam pos (Bind x) (NoName Impl) <$> uoptional (colon *> tm') <*> (braceR' *> goLam)))

  "(" -> ws >> do
    x <- ident'
    a <- colon' *> tm' <* parR'
    Lam pos (Bind x) (NoName Expl) (UJust a) <$> goLam

  "_" -> ws >> Lam pos DontBind (NoName Expl) UNothing <$> goLam
  _ -> ws >> do
    x <- lvl' >> identBase `cut` [Msg "binder", "."]
    Lam pos (Bind x) (NoName Expl) UNothing <$> goLam
    |])

pLet' :: Pos -> Parser Tm
pLet' l = do
  x <- ident'
  a <- uoptional (colon `notFollowedBy` eq *> tm')
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
tm' = lvl' >> tmBase `cut` [Msg "lambda expression", "let"]


--------------------------------------------------------------------------------

topDef :: Span -> Parser TopLevel
topDef x = local (const 1) do
  a <- uoptional (colon `notFollowedBy` eq *> tm')
  eq'
  rhs <- tm'
  local (const 0) (Definition x a rhs <$> top)

top :: Parser TopLevel
top =  (exactLvl 0 >> (ident >>= topDef))
   <|> (Nil <$ eof `cut` [Msg "end of input", Msg "top-level declaration or definition"])

--------------------------------------------------------------------------------

src :: Parser TopLevel
src = ws *> top

parse :: B.ByteString -> Result Error TopLevel
parse = runParser src

parseString :: String -> (B.ByteString, Result Error TopLevel)
parseString  (packUTF8 -> str) = (str, parse str)
{-# inline parseString #-}

test :: String -> IO ()
test str = do
  let (src, res) = parseString str
  case res of
    OK a _ _ -> print a
    Fail     -> putStrLn "parser failure"
    Err e    -> putStrLn $ prettyError src e
