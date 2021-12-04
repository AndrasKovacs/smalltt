{-# OPTIONS --type-in-type #-}

id : ∀ {A : Set} → A → A;id
 = λ x → x

Pair : Set → Set → Set;Pair
  = λ A B → (P : Set) → (A → B → P) → P

dup : ∀ {A : Set} → A → Pair A A;dup
  = λ a P p → p a a

Nat : Set;Nat
 = (n : Set) → (n → n) → n → n

zero : Nat;zero
 = λ n s z → z

suc : Nat → Nat;suc
 = λ a n s z → s (a n s z)

Vec : Set → Nat → Set;Vec
 = λ A n → (V : Nat → Set) → (∀{n} → A → V n → V (suc n)) → V zero → V n

nil : ∀ {A : Set} → Vec A zero;nil
 = λ V c n → n

cons : ∀ {A : Set}{n : Nat} → A → Vec A n → Vec A (suc n);cons
 = λ a as V c n → c a (as V c n)

--------------------------------------------------------------------------------

-- Fails
-- idTest : ∀ {A} → A → A;idTest
--   = id id id id id id id id id id id id id id id id id id id id
--     id id id id id id id id id id id id id id id id id id id id

-- Fails
-- pairTest =
--   let x0  = dup Set
--       x1  = dup x0
--       x2  = dup x1
--       x3  = dup x2
--       x4  = dup x3
--       x5  = dup x4
--       x6  = dup x5
--       x7  = dup x6
--       x8  = dup x7
--       x9  = dup x8
--       x10 = dup x9
--       x11 = dup x10
--       x12 = dup x11
--       x13 = dup x12
--       x14 = dup x13
--       x15 = dup x14
--       x16 = dup x15
--       x17 = dup x16
--       x18 = dup x17
--       x19 = dup x18
--       x20 = dup x19
--   in x20

vecTest
 =
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set
   (cons Set (cons Set (cons Set (cons Set (cons Set (cons Set

   nil

   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
