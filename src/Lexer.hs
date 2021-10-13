{-# language UnboxedTuples, UnboxedSums #-}

module Lexer where

import FlatParse.Stateful hiding (Parser, runParser, string, char, cut, err)

import qualified FlatParse.Stateful as FP
import qualified Data.ByteString as B
import Language.Haskell.TH
import Common

import qualified Data.Set as S
import Data.Char
import Data.String
import GHC.Exts

--------------------------------------------------------------------------------

data Expected
  = Lit String
  | Msg String
  deriving (Eq, Show, Ord)

instance IsString Expected where fromString = Lit

data Error'
  = Precise Expected
  | ExactIndent Int
  | IndentMore  Int
  | Imprecise [Expected]

  deriving Show

data Error = Error !Pos !Error' | DontUnboxError
  deriving Show

merge :: Error -> Error -> Error
merge ~err@(Error p e) ~err'@(Error p' e')
  | p < p'    = err'
  | p' < p    = err
  | otherwise = case (e, e') of
     (ExactIndent _ , _             ) -> err
     (_             , ExactIndent _ ) -> err'
     (IndentMore _  , _             ) -> err
     (_             , IndentMore _  ) -> err'
     (Precise _     , _             ) -> err
     (_             , Precise _     ) -> err'
     (Imprecise ss  , Imprecise ss' ) -> Error p (Imprecise (ss ++ ss'))
{-# noinline merge #-}

type Parser = FP.Parser Error

uoptioned :: FP.Parser e a -> (UMaybe a -> FP.Parser e b) -> FP.Parser e b
uoptioned (FP.Parser f) k = FP.Parser \ ~fp !r eob s n -> case f fp r eob s n of
  OK# a s n -> runParser# (k (UJust a)) fp r eob s n
  Fail#     -> runParser# (k UNothing)  fp r eob s n
  x         -> unsafeCoerce# x
{-# inline uoptioned #-}

uoptional :: FP.Parser e a -> FP.Parser e (UMaybe a)
uoptional p = (UJust <$> p) <|> pure UNothing
{-# inline uoptional #-}

prettyError :: B.ByteString -> Error -> String
prettyError _ DontUnboxError = impossible
prettyError b (Error pos e)  =

  let ls       = FP.lines b
      [(l, c)] = posLineCols b [pos]
      line     = if 0 <= l && l < length ls then ls !! l else ""
      linum    = show l
      lpad     = map (const ' ') linum

      expected (Lit s) = show s
      expected (Msg s) = s

      err (Precise exp)     = "expected " ++ expected exp
      err (Imprecise exps)  = "expected " ++ (imprec $ S.toList $ S.fromList exps)
      err (IndentMore col)  = "expected a token, indented to column " ++ show col ++ " or more"
      err (ExactIndent col) = "expected a token, indented to column " ++ show col

      imprec :: [Expected] -> String
      imprec []     = error "impossible"
      imprec [s]    = expected s
      imprec (s:ss) = expected s ++ go ss where
        go []     = ""
        go [s]    = " or " ++ expected s
        go (s:ss) = ", " ++ expected s ++ go ss

  in show l ++ ":" ++ show c ++ ":\n" ++
     lpad   ++ "|\n" ++
     linum  ++ "| " ++ line ++ "\n" ++
     lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
     "parse error: " ++
     err e

-- | Throw an error.
err :: Error' -> Parser a
err err = do
  p <- getPos
  FP.err $ Error p err

-- | Imprecise cut: we slap a list of expected things on inner errors.
cut :: Parser a -> [Expected] -> Parser a
cut p exps = do
  pos <- getPos
  FP.cutting p (Error pos (Imprecise exps)) merge

-- | Precise cut: we propagate at most a single expected thing.
cut' :: Parser a -> Expected -> Parser a
cut' p exp = do
  pos <- getPos
  FP.cutting p (Error pos (Precise exp)) merge

runParser :: Parser a -> B.ByteString -> Result Error a
runParser p = FP.runParser p 0 0

-- | Run parser, print pretty error on failure.
testParser :: Show a => Parser a -> String -> IO ()
testParser p str = case packUTF8 str of
  b -> case runParser p b of
    Err e    -> putStrLn $ prettyError b e
    OK a _ _ -> print a
    Fail     -> putStrLn "parse error"

-- | Consume whitespace. We track the number of whitespace characters read since the start of the
--   current line. We don't need to track column numbers precisely! Relevant indentation consists of
--   only whitespace at the start of a line. For simplicity, whitespace parsing counts characters
--   all the time, although it would be a possible optimization to only count characters after the
--   start of a newline.
ws :: Parser ()
ws = $(switch [| case _ of
  " "  -> modify (+1) >> ws
  "\n" -> put 0 >> ws
  "\t" -> modify (+1) >> ws
  "\r" -> modify (+1) >> ws
  "--" -> lineComment
  "{-" -> modify (+2) >> multilineComment
  _    -> pure () |])

-- | Parse a line comment.
lineComment :: Parser ()
lineComment =
  optioned anyWord8
    (\case 10 -> put 0 >> ws
           _  -> modify (+1) >> lineComment)
    (pure ())

-- | Parse a potentially nested multiline comment.
multilineComment :: Parser ()
multilineComment = go (1 :: Int) where
  go 0 = ws
  go n = $(switch [| case _ of
    "\n" -> put 0       >> go n
    "-}" -> modify (+2) >> go (n - 1)
    "{-" -> modify (+2) >> go (n + 1)
    _    -> branch anyChar (modify (+1) >> go n) (pure ()) |])

-- | Query the current indentation level, fail if it's smaller than the current expected level.
lvl :: Parser Int
lvl = do
  lvl <- ask
  currentLvl <- get
  if currentLvl < lvl
    then empty
    else pure currentLvl
{-# inline lvl #-}

-- | Same as `lvl` except we throw an error on mismatch.
lvl' :: Parser Int
lvl' = do
  lvl <- ask
  currentLvl <- get
  if currentLvl < lvl
    then err $ IndentMore lvl
    else pure currentLvl
{-# inline lvl' #-}

-- | Fail if the current level is not the expected one.
exactLvl :: Int -> Parser ()
exactLvl l = do
  l' <- get
  if l == l' then pure () else empty
{-# inline exactLvl #-}

-- | Throw error if the current level is not the expected one.
exactLvl' :: Int -> Parser ()
exactLvl' l = do
  l' <- get
  if l == l' then pure () else err (ExactIndent l)
{-# inline exactLvl' #-}

-- | We check indentation first, then read the token, then read trailing whitespace.
token :: Parser a -> Parser a
token p = lvl *> p <* ws
{-# inline token #-}

-- | `token`, but indentation failure is an error.
token' :: Parser a -> Parser a
token' p = lvl' *> p <* ws
{-# inline token' #-}

moreIndented :: Parser a -> (a -> Parser b) -> Parser b
moreIndented pa k = do
  lvl <- get
  a <- pa
  local (\_ -> lvl + 1) (k a)
{-# inline moreIndented #-}

-- | Read a starting character of an identifier.
identStartChar :: Parser Char
identStartChar = fusedSatisfy
  isLatinLetter
  (\c -> isGreekLetter c || isLetter c)
  isLetter
  isLetter

-- | Read a non-starting character of an identifier.
identChar :: Parser Char
identChar = fusedSatisfy
  (\c -> isLatinLetter c || FP.isDigit c)
  (\c -> isGreekLetter c || isLetter c)
  isLetter
  isLetter

inlineIdentChar :: Parser Char
inlineIdentChar = fusedSatisfy
  (\c -> isLatinLetter c || FP.isDigit c)
  (\c -> isGreekLetter c || isLetter c)
  isLetter
  isLetter
{-# inline inlineIdentChar #-}

manyIdentChars :: Parser ()
manyIdentChars = many_ inlineIdentChar

-- | Parse a non-keyword string.
symbol :: String -> Q Exp
symbol str = [| token $(FP.string str) |]

-- | Parser a non-keyword string, throw precise error on failure.
symbol' :: String -> Q Exp
symbol' str =
  [| token' ($(FP.string str) `cut'` Lit str) |]

-- | Parse a keyword string.
keyword :: String -> Q Exp
keyword str =
  [| token ($(FP.string str) `notFollowedBy` identChar) |]

-- | Parse a keyword string, throw precise error on failure.
keyword' :: String -> Q Exp
keyword' str =
  [| token' (($(FP.string str) `notFollowedBy` identChar) `cut'` Lit str) |]
