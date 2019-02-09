{-# OPTIONS --rewriting #-}

postulate _↦_ : {A : Set} → A → A → Set
infix 3 _↦_
{-# BUILTIN REWRITE _↦_ #-}

postulate
  Nat  : Set
  zero : Nat
  suc  : Nat → Nat

postulate
  plus  : Nat → Nat → Nat
  plus0 : ∀ {b} → plus zero b ↦ b
  pluss : ∀ {a b} → plus (suc a) b ↦ suc (plus a b)
{-# REWRITE plus0 pluss #-}

postulate
  mul  : Nat → Nat → Nat
  mul0 : ∀ {b} → mul zero b ↦ zero
  muls : ∀ {a b} → mul (suc a) b ↦ plus b (mul a b)
{-# REWRITE mul0 muls #-}

n5     = suc (suc (suc (suc (suc zero))))
n10    = plus n5 n5
n10b   = mul n5 (suc (suc zero))
n100   = mul n10 n10
n100b  = mul n10b n10b
n1k    = mul n100 n10
n1kb   = mul n100b n10
n5k    = mul n1k n5
n5kb   = mul n1kb n5
n10k   = mul n100 n100
n10kb  = mul n100b n100b
n100k  = mul n10k n10
n100kb = mul n10kb n10
n1M    = mul n100k n10
n1Mb   = mul n100kb n10

postulate
  Eq   : ∀{A : Set} → A → A → Set
  refl : ∀{A x} → Eq {A} x x

-- 840 MB, 2.27s

conv : Eq n5k n5kb
conv = refl

-- -- -- 840 MB, 0.86s
-- -- norm1M [normalize] = n1M
