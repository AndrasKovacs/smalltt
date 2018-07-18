
module Elaboration (
    infer₀
  , zonk₀
  , nf₀
  , quote₀
  , eval₀) where

import Data.List hiding (lookup, insert)

import Control.Applicative
import Control.Monad
import Data.IORef
import Debug.Trace
import System.IO.Unsafe

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HS

import Text.Megaparsec.Pos

import Presyntax
import Syntax

lams ∷ [(Name, Icit)] → Tm → Tm
lams sp t = foldl' (\t (x, i) → Lam x i t) t sp

varᵛ ∷ Var → Val
varᵛ x = Neu (Varʰ x) []

metaᵛ ∷ Meta → Val
metaᵛ m = Neu (Metaʰ m) []

genᵛ' ∷ Int → Name → Val
genᵛ' g x = Neu (Varʰ (x, g)) []

genᵛ ∷ Con → Name → Val
genᵛ = genᵛ' . conSize

-- Global metacontext
--------------------------------------------------------------------------------

type Metas = IntMap Val

data MetaInsertion
  = MIYes
  | MINo
  | MIUntilName Name
  deriving (Show)

{-# noinline mcxt #-}
mcxt :: IORef Metas
mcxt = unsafeDupablePerformIO (newIORef mempty)

{-# noinline freshMeta #-}
freshMeta ∷ IORef Int
freshMeta = unsafeDupablePerformIO (newIORef 0)

reset ∷ IO ()
reset = do
  writeIORef currPos (initialPos "")
  writeIORef mcxt mempty
  writeIORef freshMeta 0

inst ∷ Meta -> Maybe Val
inst m = unsafeDupablePerformIO (IM.lookup m <$> readIORef mcxt)

-- Errors
--------------------------------------------------------------------------------

{-# noinline currPos #-}
currPos ∷ IORef SourcePos
currPos = unsafeDupablePerformIO (newIORef (initialPos ""))

reportError ∷ String → a
reportError msg =
  let pos = unsafeDupablePerformIO (readIORef currPos)
  in error (sourcePosPretty pos ++ ":\n\n" ++ msg ++ "\n")

updPos ∷ Posed a → Posed a
updPos (p, a) = seq (unsafeDupablePerformIO (writeIORef currPos p)) (p, a)

-- Elaboration context
--------------------------------------------------------------------------------

type Vals = [Maybe Val] -- Nothing: bound, Just: defined

-- First component:
--     Left: name from source
--     Right: inserted name
-- Second component:
--     Left: bound variable
--     Right: defined variables
type Tys  = [(Either Name Name, Either Ty Ty)]

-- TODO: custom (suggestively named) data types for context entries
data Con = Con {conSize ∷ Int, conTys ∷ Tys, conVals ∷ Vals}

nil ∷ Con
nil = Con 0 [] []

-- | Add a bound variable.
bind ∷ Con → Name → Ty → Con
bind (Con g tys vs) x ~a = Con (g + 1) ((Left x, Left a):tys) (Nothing:vs)

-- | Add a defined variable.
define ∷ Con → Name → Ty → Val → Con
define (Con  g tys vs) x ~a ~t = Con  (g + 1) ((Left x, Right a):tys) (Just t:vs)

-- | Insert a new bound variable.
insert ∷ Con → Name → Ty → Con
insert (Con  g tys vs) x ~a = Con  (g + 1) ((Right x, Left a):tys) (Nothing:vs)

-- Evaluation (modulo global metacontext)
--------------------------------------------------------------------------------

appᵛ ∷ Val → Val → Icit → Val
appᵛ t ~u i = case t of
  Lamᵛ _ _ t → t u
  Neu h sp   → Neu h ((u, i):sp)
  _          → reportError "appᵛ: IMPOSSIBLE"

eval ∷ Con → Tm → Val
eval (Con g _ vs) = eval' g vs

eval' ∷ Int → Vals → Tm → Val
eval' g vs = \case
  Var (xn, x)   → maybe (varᵛ (xn, x)) refresh (vs !! (g - x - 1))
  Let x a t u   → eval' (g + 1) (Just (eval' g vs t):vs) u
  App t u i     → appᵛ (eval' g vs t) (eval' g vs u) i
  Lam x i t     → Lamᵛ x i $ \a → eval' (g + 1) (Just a:vs) t
  Pi x i a b    → Piᵛ x i (eval' g vs a) $ \a → eval' (g + 1) (Just a:vs) b
  U             → Uᵛ
  Meta m        → maybe (metaᵛ m) refresh (inst m)

refresh ∷ Val → Val
refresh = \case
  Neu (Metaʰ i) sp
    | Just t ← inst i →
      refresh (foldr (\(u, i) t → appᵛ t u i) t sp)
  t → t

quote ∷ Int → Val → Tm
quote g = go g where
  goHead = \case
    Metaʰ m → Meta m
    Varʰ x  → Var x
  go g t = case refresh t of
    Neu h sp     → foldr (\(a, i) t → App t (go g a) i) (goHead h) sp
    Lamᵛ x i t   → Lam x i (go (g + 1) (t (genᵛ' g x)))
    Piᵛ  x i a b → Pi x i (go g a) (go (g + 1) (b (genᵛ' g x)))
    Uᵛ           → U

-- Unification
--------------------------------------------------------------------------------

type Ren = IntMap Var -- renaming

-- Possible additions to inversion:
--   - attempt eta contraction to variables
--   - non-unique solutions:
--     - ignore non-variables (dependency erasure)

invert ∷ Meta → Spine → (Int, [(Name, Icit)], Ren)
invert m = foldr go (0, [], IM.empty) where
  go (a, i) (!g, sp', r)  =
    let (xn, x) = case a of
          Neu (Varʰ xn) [] → xn
          _                →
            reportError ("Substitution for metavariable " ++ show m ++ " is not a renaming")

    -- note: nonlinearity ignored (we pick most recent var)
    in (g + 1, (xn, i):sp', IM.insert x (xn, g) r)

rename ∷ Int → Int → Meta → Ren → Tm → Tm
rename g spSize occur r t = go g r t where
  shift = g - spSize
  go g r = \case
    Var (xn, x) →
      maybe (reportError ("Solution scope error: variable " ++ show (xn, x)
                          ++ " is not in " ++ show r
                          ++ "\nwhen solving meta " ++ show  g ++ " for\n"
                          ++ show t))
            Var
            (IM.lookup x r)

    Let x a t u → Let x (go g r a) (go g r t) (go (g + 1) (IM.insert g (x, g - shift) r) u)
    App t u i   → App (go g r t) (go g r u) i
    Lam x i t   → Lam x i (go (g + 1) (IM.insert g (x, g - shift) r) t)
    Pi x i a b  → Pi x i (go g r a) (go (g + 1) (IM.insert g (x, g - shift) r) b)
    U           → U
    Meta i | i == occur →
             reportError ("Infinite solution error: meta " ++ show occur
                          ++ " occurs in solution candidate\n"
                          ++ show t)
           | otherwise  → Meta i

solve ∷ Int → Meta → Spine → Val → IO ()
solve g m sp t = do
  let (spSize, sp', r) = invert m sp
      t' = lams sp' (rename g spSize m r (quote g t))
  modifyIORef' mcxt $ IM.insert m (eval nil t')

matchIcit ∷ Icit → Icit → IO ()
matchIcit i i' = if i == i'
  then pure ()
  else reportError (
    "Can't match " ++ show i' ++ " binder with " ++ show i)

unify ∷ Con → Val → Val → IO ()
unify (Con  g₀ _ _) t₀ t₀' = go g₀ t₀ t₀' where

  go ∷ Int → Val → Val → IO ()
  go g t t' = case (refresh t, refresh t') of
    (Uᵛ, Uᵛ) → pure ()

    (Lamᵛ (genᵛ' g → x) i t, Lamᵛ (genᵛ' g → x') i' t') → go (g + 1) (t x) (t' x')
    (Lamᵛ (genᵛ' g → x) i t,   t') → go (g + 1) (t x) (appᵛ t' x i)
    (t, Lamᵛ (genᵛ' g → x') i' t') → go (g + 1) (appᵛ t x' i') (t' x')

    (Piᵛ (genᵛ' g → x) i a b, Piᵛ (genᵛ' g → x') i' a' b') → do
      matchIcit i i'
      go g a a'
      go (g + 1) (b x) (b' x')

    (Neu (Varʰ x)  sp, Neu (Varʰ x')  sp') | snd x == snd x' → goSpine g sp sp'
    (Neu (Metaʰ m) sp, Neu (Metaʰ m') sp') | m == m'         → goSpine g sp sp'
    (Neu (Metaʰ m) sp, t                 ) → solve g m sp t
    (t,                Neu (Metaʰ m) sp  ) → solve g m sp t

    (t, t') →
      reportError (
           "Can't unify\n\n" ++ show (quote g t)
        ++ "\n\nwith\n\n"        ++ show (quote g t'))

  goSpine ∷ Int → Spine → Spine → IO ()
  goSpine g sp sp' = case (sp, sp') of
    ((a, _):as, (b, _):bs) → goSpine g as bs >> go g a b
    ([]       , []       ) → pure ()
    _                      → reportError "unify.goSpine: IMPOSSIBLE"


-- Elaboration
--------------------------------------------------------------------------------

newMeta ∷ Con → IO Tm
newMeta (Con g tys _) = do
  m ← readIORef freshMeta
  writeIORef freshMeta (m + 1)
  let bvars = [(either id id x, g') | ((x, Left{}), g') ← zip tys [g-1,g-2 ..]]
  pure $ foldr (\x t → App t (Var x) Expl) (Meta m) bvars

check ∷ Con → Tmᴾ → Ty → IO Tm
check con (updPos → (pos, t)) want = case (t, refresh want) of
  (Lamᴾ x i t, Piᵛ x' i' a b) | either (==x') (==i') i →
    Lam x i' <$> check (bind con x a) t (b (genᵛ con x))
  (t, Piᵛ x Impl a b) →
    Lam x Impl <$> check (insert con x a) (pos, t) (b (genᵛ con x))

  (Letᴾ x a' t' u', _) → do
    a' ← check con a' Uᵛ
    let ~va' = eval con a'
    t' ← check con t' va'
    let ~vt' = eval con t'
    u' ← check (define con x va' vt') u' want
    pure (Let x a' t' u')

  (Holeᴾ, _) →
    newMeta con

  (t, _) → do
    (t, has) ← infer MIYes con (pos, t)
    t <$ unify con has want

insertMetas ∷ MetaInsertion → Con → IO (Tm, Ty) → IO (Tm, Ty)
insertMetas ins con inp = case ins of
  MINo  → inp
  MIYes → uncurry go =<< inp where
    go t (Piᵛ x Impl a b) = do
      m ← newMeta con
      go (App t m Impl) (b (eval con m))
    go t a = pure (t, a)
  MIUntilName x → uncurry go =<< inp where
    go t (Piᵛ x' Impl a b)
      | x == x'   = pure (t, Piᵛ x' Impl a b)
      | otherwise = do
          m ← newMeta con
          go (App t m Impl) (b (eval con m))
    go t a = reportError ("No named implicit argument with name " ++ show x)

inferVar ∷ Con → Name → (Tm, Ty)
inferVar (Con  g tys vs) x = go (g - 1) tys where
  go g ((name, a):tys)
    | Left x' ← name, x == x' = (Var (x, g), either id id a)
    | otherwise = go (g - 1) tys
  go g [] = reportError ("Name " ++ show x ++ " not in scope")

infer ∷ MetaInsertion → Con → Tmᴾ → IO (Tm, Ty)
infer ins con (updPos → (pos, t)) = case t of
  Uᴾ      → pure (U, Uᵛ)
  NoMIᴾ t → infer MINo con t
  Varᴾ x  → insertMetas ins con $ pure (inferVar con x)

  Appᴾ t u i → insertMetas ins con $ do
    (t, a) ← infer
        (case i of Left x     → MIUntilName x;
                   Right Impl → MINo;
                   Right Expl → MIYes)
        con t
    case refresh a of
      Piᵛ x i' a b → do
        traverse (matchIcit i') i
        u ← check con u a
        pure (App t u i', b (eval con u))
      a → reportError
           ("Expected a function type in application, got\n" ++ show (quote (conSize con) a))

  Piᴾ x i a b → do
    a ← check con a Uᵛ
    b ← check (bind con x (eval con a)) b Uᵛ
    pure (Pi x i a b, Uᵛ)

  Letᴾ x a t u → do
    a ← check con a Uᵛ
    let ~va = eval con a
    t ← check con t va
    let ~vt = eval con t
    (u, tu) ← infer ins (define con x va vt) u
    pure (Let x a t u, tu)

  Lamᴾ x i t → insertMetas ins con $ do
    i ← case i of
      Left x  → reportError ("Can't infer type for lambda with named arguments")
      Right i → pure i
    ~a ← eval con <$> newMeta con
    (t, ty) ← infer MIYes (bind con x a) t
    let g   = conSize con
    let ty' = quote (g + 1) ty
    pure (Lam x i t, Piᵛ x i a $ \v → eval' (g + 1) (Just v:conVals con) ty')

  Holeᴾ → do
    m₁ ← newMeta con
    m₂ ← newMeta con
    pure (m₁, eval con m₂)

-- Replace metas by their normal solutions
--------------------------------------------------------------------------------

zonkSp ∷ Int → Vals → Tm → Either Val Tm
zonkSp g vs = go where
  go (Meta m) | Just v ← inst m = Left v
  go (App t u i) =
    case go t of
      Left (Lamᵛ _ _ t) → Left (t (eval' g vs u))
      Left t            → Right (App (quote g t) (zonk g vs u) i)
      Right t           → Right (App t (zonk g vs u) i)
  go t = Right (zonk g vs t)

zonk ∷ Int → Vals → Tm → Tm
zonk g vs = \case
  Var x        → Var x
  Meta m       → maybe (Meta m) (quote g) (inst m)
  U            → U
  Pi x i a b   → Pi x i (zonk g vs a) (zonk (g + 1) (Nothing:vs) b)
  App t u i    → either (\t → quote g (appᵛ t (eval' g vs u) i))
                        (\t → App t (zonk g vs u) i)
                        (zonkSp g vs t)
  Lam x i t    → Lam x i (zonk (g + 1) (Nothing: vs) t)
  Let x a t u  → Let x (zonk g vs a) (zonk g vs t)
                       (zonk (g + 1) (Just (eval' g vs t) : vs) u)

--------------------------------------------------------------------------------

infer₀ ∷ Tmᴾ → IO (Tm, Ty)
infer₀ t = reset >> infer MINo nil t

zonk₀ ∷ Tm → Tm
zonk₀ = zonk 0 []

quote₀ ∷ Val → Tm
quote₀ = quote 0

eval₀ ∷ Tm → Val
eval₀ = eval nil

nf₀ ∷ Tm → Tm
nf₀ = quote 0 . eval₀
