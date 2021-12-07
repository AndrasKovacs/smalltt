
Require Import Coq.Unicode.Utf8.

Definition the (A : Type)(x : A) := x.

Definition CBool := ∀ (B : Set), B → B → B.
Definition ctrue : CBool := λ B t f , t.
Definition cand  : CBool → CBool → CBool := λ a b B t f , a B (b B t f) f.

Definition CNat := ∀ (N : Set), (N → N) → N → N.
Definition add : CNat → CNat → CNat := λ a b n s z , a n s (b n s z).
Definition mul : CNat → CNat → CNat := λ a b N s z , a N (b N s) z.
Definition suc : CNat → CNat := λ a N s z , s (a N s z).
Definition n2  : CNat := λ N s z , s (s z).
Definition n3  : CNat := λ N s z , s (s (s z)).
Definition n4  : CNat := λ N s z , s (s (s (s z))).
Definition n5  : CNat := λ N s z , s (s (s (s (s z)))).
Definition n10    := mul n2 n5.
Definition n10b   := mul n5 n2.
Definition n15    := add n10  n5.
Definition n15b   := add n10b n5.
Definition n18    := add n15  n3.
Definition n18b   := add n15b n3.
Definition n19    := add n15  n4.
Definition n19b   := add n15b n4.
Definition n20    := mul n2 n10.
Definition n20b   := mul n2 n10b.
Definition n21    := suc n20.
Definition n21b   := suc n20b.
Definition n22    := suc n21.
Definition n22b   := suc n21b.
Definition n23    := suc n22.
Definition n23b   := suc n22b.
Definition n100   := mul n10   n10.
Definition n100b  := mul n10b  n10b.
Definition n10k   := mul n100  n100.
Definition n10kb  := mul n100b n100b.
Definition n100k  := mul n10k  n10.
Definition n100kb := mul n10kb n10b.
Definition n1M    := mul n10k  n100.
Definition n1Mb   := mul n10kb n100b.
Definition n5M    := mul n1M   n5.
Definition n5Mb   := mul n1Mb  n5.
Definition n10M   := mul n5M   n2.
Definition n10Mb  := mul n5Mb  n2.

Definition Tree := ∀ (T : Set), (T → T → T) → T → T.
Definition leaf : Tree := λ T n l , l.
Definition node (t1 t2 : Tree) : Tree := λ T n l , n (t1 T n l) (t2 T n l).
Definition fullTree (n : CNat) : Tree := n Tree (λ t , node t t) leaf.

Definition fullTree2 (n : CNat) : Tree := n Tree (λ t , node t (node t leaf)) leaf.

(* full tree with given trees at bottom level *)
Definition fullTreeWithLeaf : Tree → CNat → Tree
 := λ bottom n , n Tree (λ t , node t t) bottom.

Definition forceTree : Tree → CBool := λ t , t _ cand ctrue.


Definition t15  := fullTree n15.
Definition t15b := fullTree n15b.
Definition t18  := fullTree n18.
Definition t18b := fullTree n18b.
Definition t19  := fullTree n19.
Definition t19b := fullTree n19b.
Definition t20  := fullTree n20.
Definition t20b := fullTree n20b.
Definition t21  := fullTree n21.
Definition t21b := fullTree n21b.
Definition t22  := fullTree n22.
Definition t22b := fullTree n22b.
Definition t23  := fullTree n23.
Definition t23b := fullTree n23b.

(* -- Full tree conversion *)
(* -------------------------------------------------------------------------------- *)

(* Definition convt15  : t15 =  t15b  := eq_refl. *)
(* Definition convt18  : t18 =  t18b  := eq_refl. *)
(* Definition convt19  : t19 =  t19b  := eq_refl. *)
(* Definition convt20  : t20 =  t20b  := eq_refl. *)
(* Definition convt21  : t21 =  t21b  := eq_refl. *)
(* Definition convt22  : t22 =  t22b  := eq_refl. *)
(* Definition convt23  : t23 =  t23b  := eq_refl. *)

(* -- Full meta-containing tree conversion *)
(* -------------------------------------------------------------------------------- *)

(* Definition convmt15 : t15 = (fullTreeWithLeaf _ n15 ) := eq_refl. *)
(* Definition convmt18 : t18 = (fullTreeWithLeaf _ n18 ) := eq_refl. *)
(* Definition convmt19 : t19 = (fullTreeWithLeaf _ n19 ) := eq_refl. *)
(* Definition convmt20 : t20 = (fullTreeWithLeaf _ n20 ) := eq_refl. *)
(* Definition convmt21 : t21 = (fullTreeWithLeaf _ n21 ) := eq_refl. *)
(* Definition convmt22 : t22 = (fullTreeWithLeaf _ n22 ) := eq_refl. *)
(* Definition convmt23 : t23 = (fullTreeWithLeaf _ n23 ) := eq_refl. *)

(* -- Full tree forcing *)
(* -------------------------------------------------------------------------------- *)

Eval vm_compute in forceTree t15.
Eval vm_compute in forceTree t18.
Eval vm_compute in forceTree t19.
Eval vm_compute in forceTree t20.
Eval vm_compute in forceTree t21.
Eval vm_compute in forceTree t22.
Eval vm_compute in forceTree t23.


Goal True. let x := eval vm_compute in t15 in idtac. Abort.
Goal True. let x := eval vm_compute in t18 in idtac. Abort.
Goal True. let x := eval vm_compute in t19 in idtac. Abort.
Goal True. let x := eval vm_compute in t20 in idtac. Abort.
Goal True. let x := eval vm_compute in t21 in idtac. Abort.
Goal True. let x := eval vm_compute in t22 in idtac. Abort.
Goal True. let x := eval vm_compute in t23 in idtac. Abort.


(* Eval compute in forceTree t15. *)
(* Eval compute in forceTree t18. *)
(* Eval compute in forceTree t19. *)
(* Eval compute in forceTree t20. *)
(* Eval compute in forceTree t21. *)
(* Eval compute in forceTree t22. *)
(* Eval compute in forceTree t23. *)

(* Eval lazy in forceTree t15. *)
(* Eval lazy in forceTree t18. *)
(* Eval lazy in forceTree t19. *)
(* Eval lazy in forceTree t20. *)
(* Eval lazy in forceTree t21. *)
(* Eval lazy in forceTree t22. *)
(* Eval lazy in forceTree t23. *)
