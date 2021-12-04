Require Import Coq.Unicode.Utf8.

Definition id {A:Set} : A → A := λ x, x.
Definition Pair : Set → Set → Set := λ A B, ∀ (P : Set), (A → B → P) → P.
Definition dup {A:Set} : A → Pair A A := λ a P p, p a a.
Definition CNat : Set := ∀ (N : Set), (N → N) → N → N.
Definition czero : CNat := λ n s z, z.
Definition csuc : CNat → CNat := λ a n s z, s (a n s z).

Definition Vec : Set → CNat → Set
  := λ A n, ∀ (V : CNat → Set), (∀ n, A → V n → V (csuc n)) → V czero → V n.

Definition nil {A:Set} : Vec A czero
 := λ V c n, n.

Definition cons {A:Set} {n:CNat} : A → Vec A n → Vec A (csuc n)
  := λ x xs V c nil, c n x (xs V c nil).

--------------------------------------------------------------------------------

(* Fails *)
(* Definition idTest {A : Set} : A → A *)
(*   := id id id id id id id id id id id id id id id id id id id id *)
(*      id id id id id id id id id id id id id id id id id id id id. *)


(* Fails *)
(* Definition pairTest := *)
(*   let x0  := dup Set in *)
(*   let x1  := dup x0  in *)
(*   let x2  := dup x1  in *)
(*   let x3  := dup x2  in *)
(*   let x4  := dup x3  in *)
(*   let x5  := dup x4  in *)
(*   let x6  := dup x5  in *)
(*   let x7  := dup x6  in *)
(*   let x8  := dup x7  in *)
(*   let x9  := dup x8  in *)
(*   let x10 := dup x9  in *)
(*   let x11 := dup x10 in *)
(*   let x12 := dup x11 in *)
(*   let x13 := dup x12 in *)
(*   let x14 := dup x13 in *)
(*   let x15 := dup x14 in *)
(*   let x16 := dup x15 in *)
(*   let x17 := dup x16 in *)
(*   let x18 := dup x17 in *)
(*   let x19 := dup x18 in *)
(*   let x20 := dup x19 in *)
(*   x20. *)

(* 88 ms  *)
Definition vecTest :=
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

   .
