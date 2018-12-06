
Require Import Utf8.

Definition Nat : Set := ∀ (N : Set), (N → N) → N → N.
Definition n2  : Nat := λ N s z, s (s z).
Definition n5  : Nat := λ N s z, s (s (s (s (s z)))).
Definition mul : Nat → Nat → Nat := λ a b N s z, a N (b N s) z.
Definition n10   := mul n2 n5.
Definition n100  := mul n10 n10.
Definition n10k  := mul n100 n100.
Definition n10kb := mul n100 (mul n10 n10).
Definition n1M   := mul n10k n100.
Definition n1Mb  := mul n100 n10k.
Definition n10M  := mul n1M n10.
Definition n10Mb := mul n10 n1M.
Definition n100M := mul n10M n10.
Definition n200M := mul n2 n100M.

Definition forceNat : Nat → bool := λ n, n _ (λ x, x) true.

Eval vm_compute in forceNat n200M.
