
module Elaboration where

import Prelude hiding (lookup)
import Data.List hiding (lookup)

import Control.Applicative
import Control.Monad
import Data.IORef
import System.IO.Unsafe

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HS

import Presyntax
import Syntax

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
  writeIORef mcxt mempty
  writeIORef freshMeta 0

inst ∷ Meta -> Maybe Val
inst m = unsafeDupablePerformIO (IM.lookup m <$> readIORef mcxt)

-- Evaluation (modulo global metacontext)
--------------------------------------------------------------------------------

appᵛ ∷ Val → Val → Name → Icit → Val
appᵛ t ~u x i = case t of
  Lamᵛ _ _ t → t u
  Neu h sp   → Neu h ((x, (u, i)) : sp)
  _          → error "vapp: IMPOSSIBLE"

eval ∷ Vals → Tm → Val
eval vs = \case
  Var x         → maybe (varᵛ x) refresh (lookup "eval: IMPOSSIBLE" x vs)
  Let x a t u   → eval ((x, Just (eval vs t)):vs) u
  App t u x i   → appᵛ (eval vs t) (eval vs u) x i
  Lam x i t     → Lamᵛ x i $ \a → eval ((x, Just a):vs) t
  Pi x i a b    → Piᵛ x i (eval vs a) $ \a → eval ((x, Just a):vs) b
  U             → Uᵛ
  Meta m        → maybe (metaᵛ m) refresh (inst m)

refresh ∷ Val → Val
refresh = \case
  Neu (Metaʰ i) sp
    | Just t <- inst i →
      refresh (foldr (\(x, (u, i)) t → appᵛ t u x i) t sp)
  t → t

fresh ∷ Int → Name → Name
fresh g x = x ++ "_" ++ show g

quote ∷ Int → Val → Tm
quote = go where
  goHead = \case
    Metaʰ m → Meta m
    Varʰ x  → Var x
  go g t = case refresh t of
    Neu h sp                 → foldr (\(x, (a, i)) t → App t (go g a) x i) (goHead h) sp
    Lamᵛ (fresh g → x) i t   → Lam x i (go (g + 1) (t (varᵛ x)))
    Piᵛ  (fresh g → x) i a b → Pi x i (go g a) (go (g + 1) (b (varᵛ x)))
    Uᵛ                       → U

-- Unification
--------------------------------------------------------------------------------

invert ∷ Spine → Ren
invert = foldl' go HM.empty where
  go r (x, (a, _)) =
    let var = case a of
          Neu (Varʰ x') [] → x'
          _                → error "invert: meta substitution is not a renaming"
    in HM.alter (maybe (Just x) (\_ → Nothing)) var r

rename ∷ Meta → Ren → Tm → Tm
rename occur = go where
  go r = \case
    Var x       → maybe (error "rename: scope error") Var (HM.lookup x r)
    Let x a t u → Let x (go r a) (go r t) (go r u)
    App t u x i → App (go r t) (go r u) x i
    Lam x i t   → Lam x i (go (HM.insert x x r) t)
    Pi x i a b  → Pi x i (go r a) (go (HM.insert x x r) b)
    U           → U
    Meta i | i == occur → error "rename: occurs check"
           | otherwise  → Meta i

solve ∷ Int → Meta → Spine → Val → IO ()
solve g m sp t = do
  let t' = lams sp (rename m (invert sp) (quote g t))
  modifyIORef' mcxt $ IM.insert m (eval [] t')

matchIcit ∷ Icit → Icit → IO ()
matchIcit i i' = if i == i'
  then pure ()
  else error "can't match explicit binder with implicit"

unify ∷ Int → Val → Val → IO ()
unify = go where

  go ∷ Int → Val → Val → IO ()
  go g t t' = case (refresh t, refresh t') of
    (Uᵛ, Uᵛ) → pure ()

    (Lamᵛ ((varᵛ . fresh g) → x) i t, Lamᵛ _ i' t') → go (g + 1) (t x) (t' x)

    (Lamᵛ x i t, t') → go (g + 1) (t (varᵛ x')) (appᵛ t' (varᵛ x') x' i)
      where x' = fresh g x
    (t, Lamᵛ x' i' t') → go (g + 1) (appᵛ t (varᵛ x'') x'' i') (t' (varᵛ x''))
      where x'' = fresh g x'

    (Piᵛ ((varᵛ . fresh g) → x) i a b, Piᵛ _ i' a' b') → do
      matchIcit i i'
      go g a a'
      go (g + 1) (b x) (b' x)

    (Neu (Varʰ x ) sp, Neu (Varʰ x' ) sp') | x == x' → goSpine g sp sp'
    (Neu (Metaʰ m) sp, Neu (Metaʰ m') sp') | m == m' → goSpine g sp sp'
    (Neu (Metaʰ m) sp, t                 ) → solve g m sp t
    (t,                Neu (Metaʰ m) sp  ) → solve g m sp t

    (t, t') →
      error $ "Can't unify\n" ++ show (quote g t) ++ "\nwith\n" ++ show (quote g t')

  goSpine ∷ Int → Spine → Spine → IO ()
  goSpine g sp sp' = case (sp, sp') of
    ((_, (a, _)):as, (_, (b, _)):bs)  → goSpine g as bs >> go g a b
    ([]            , []            )  → pure ()
    _                                 → error "unify spine: IMPOSSIBLE"


-- Elaboration
--------------------------------------------------------------------------------

newMeta ∷ Tys → IO Tm
newMeta cxt = do
  m <- readIORef freshMeta
  writeIORef freshMeta (m + 1)
  let bvars = hashNub [x | (x, Left{}) <- cxt]
  pure $ foldr (\x t → App t (Var x) x Expl) (Meta m) bvars

check ∷ Int → Tys → Vals → Tmᴾ → Ty → IO Tm
check g tys vs t want = case (t, refresh want) of
  (Lamᴾ x i t, Piᵛ x' i' a b) | either (==x') (==i') i →
    Lam x i' <$> check (g + 1) ((x, Left a): tys) ((x, Nothing):vs) t (b (varᵛ x))

  (t, Piᵛ x Impl a b) → do
    let x' = x ++ "_" ++ show (length tys)
    t <- check (g + 1) ((x', Left a): tys) ((x', Nothing):vs) t (b (varᵛ x'))
    pure $ Lam x' Impl t

  (Letᴾ x a' t' u', _) → do
    a' <- check g tys vs a' Uᵛ
    let ~va' = eval vs a'
    t' <- check g tys vs t' va'
    let ~vt' = eval vs t'
    u' <- check (g + 1) ((x, Right va'): tys) ((x, Just vt'):vs) u' want
    pure (Let x a' t' u')

  (Holeᴾ, _) →
    newMeta tys

  (t, _) → do
    (t, has) <- infer MIYes g tys vs t
    t <$ unify g has want

insertMetas ∷ MetaInsertion → Tys → Vals → IO (Tm, Ty) → IO (Tm, Ty)
insertMetas ins tys vs inp = case ins of
  MINo  → inp
  MIYes → uncurry go =<< inp where
    go t (Piᵛ x Impl a b) = do
      m <- newMeta tys
      go (App t m x Impl) (b (eval vs m))
    go t a = pure (t, a)
  MIUntilName x → uncurry go =<< inp where
    go t (Piᵛ x' Impl a b)
      | x == x'   = pure (t, Piᵛ x' Impl a b)
      | otherwise = do
          m <- newMeta tys
          go (App t m x Impl) (b (eval vs m))
    go t a = error "inserMetas: expected named implicit argument"

infer ∷ MetaInsertion → Int → Tys → Vals → Tmᴾ → IO (Tm, Ty)
infer ins g tys vs = \case
  Uᴾ      → pure (U, Uᵛ)
  NoMIᴾ t → infer MINo g tys vs t
  Varᴾ x  → insertMetas ins tys vs $ do
    let a = either id id $ lookup "infer: variable not in scope" x tys
    pure (Var x, a)

  Appᴾ t u i → insertMetas ins tys vs $ do
    (t, a) <- infer
        (case i of Left x     → MIUntilName x;
                   Right Impl → MINo;
                   Right Expl → MIYes)
        g tys vs t
    case a of
      Piᵛ x i' a b → do
        traverse (matchIcit i') i
        u <- check g tys vs u a
        pure (App t u x i', b (eval vs u))
      _ → error "infer: expected a function in application"

  Piᴾ x i a b → do
    a <- check g tys vs a Uᵛ
    b <- check (g + 1) ((x, Left (eval vs a)):tys) ((x, Nothing):vs) b Uᵛ
    pure (Pi x i a b, Uᵛ)

  Letᴾ x a t u → do
    a <- check g tys vs a Uᵛ
    let ~va = eval vs a
    t <- check g tys vs t va
    let ~vt = eval vs t
    (u, tu) <- infer ins (g + 1) ((x, Right va): tys) ((x, Just vt):vs) u
    pure (Let x a t u, tu)

  Lamᴾ x i t → insertMetas ins tys vs $ do
    i <- case i of
      Left  x →
        error "infer: can't use named argument for lambda expression with inferred type"
      Right i → pure i
    a <- eval vs <$> newMeta tys
    let xa = x ++ "_" ++ show (length tys)
    b <- newMeta ((xa, Left a):tys)
    let ty = Piᵛ xa i a (\v → eval ((xa, Just v):vs) b)
    t <- check g tys vs (Lamᴾ x (Right i) t) ty
    pure (t, ty)

  Holeᴾ → do
    m1 <- newMeta tys
    m2 <- newMeta tys
    pure (m1, eval vs m2)

-- Replace metas by their solutions in normal forms.
--------------------------------------------------------------------------------

zonkSp ∷ Int → Vals → Val → Sub (Tm, Icit) → Tm
zonkSp g vs v sp = either id (quote g) $
  foldr
    (\(x, (a, i)) → either
      (\t → Left (App t a x i))
      (\case Lamᵛ _ _ t → Right (t (eval vs a))
             v          → Left (App (quote g v) a x i)))
    (Right v) sp

zonk ∷ Int → Vals → Tm → Tm
zonk g vs = \case
  Var x        → Var x
  Meta m       → maybe (Meta m) (quote g) (inst m)
  U            → U
  Pi x i a b   → Pi x i (zonk g vs a) (zonk (g + 1) ((x, Nothing):vs) b)
  App f a x i  → let (h, sp) = splitSpine (App f a x i)
                  in case h of
                       Meta m | Just v <- inst m →
                         zonkSp g vs v sp
                       _ → foldr (\(x, (t, i)) f → App f (zonk g vs t) x i) h sp
  Lam x i t    → Lam x i (zonk (g + 1) ((x, Nothing): vs) t)
  Let x a t u  → Let x (zonk g vs a) (zonk g vs t)
                       (zonk (g + 1) ((x, Just (eval vs t)) : vs) u)
