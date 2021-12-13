
Require Import Coq.Unicode.Utf8.

Definition the (A : Set)(x : A) := x.

Definition Eq {A : Set}(x y : A) := ∀ (P : A → Set), P x → P y.
Definition refl {A}{x:A} : Eq x x := λ P px, px.

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

(* -- Nat conversion *)

(* Definition convnat1M  : Eq n1M   n1Mb  := refl. *)
(* Definition convnat5M  : Eq n5M   n5Mb  := refl. *)
(* Definition convnat10M : Eq n10M  n10Mb := refl. *)

(* -- Full tree conversion *)
(* -------------------------------------------------------------------------------- *)

(* Definition convt15  : Eq t15 t15b  := refl. *)
(* Definition convt18  : Eq t18 t18b  := refl. *)
(* Definition convt19  : Eq t19 t19b  := refl. *)
(* Definition convt20  : Eq t20 t20b  := refl. *)
(* Definition convt21  : Eq t21 t21b  := refl. *)
(* Definition convt22  : Eq t22 t22b  := refl. *)
(* Definition convt23  : Eq t23 t23b  := refl. *)

(* -- Full meta-containing tree conversion *)
(* -------------------------------------------------------------------------------- *)

(* Definition convmt15 : Eq t15b (fullTreeWithLeaf _ n15 ) := refl. *)
(* Definition convmt18 : Eq t18b (fullTreeWithLeaf _ n18 ) := refl. *)
(* Definition convmt19 : Eq t19b (fullTreeWithLeaf _ n19 ) := refl. *)
(* Definition convmt20 : Eq t20b (fullTreeWithLeaf _ n20 ) := refl. *)
(* Definition convmt21 : Eq t21b (fullTreeWithLeaf _ n21 ) := refl. *)
(* Definition convmt22 : Eq t22b (fullTreeWithLeaf _ n22 ) := refl. *)
(* Definition convmt23 : Eq t23b (fullTreeWithLeaf _ n23 ) := refl. *)

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


Eval compute in forceTree t15.
Eval compute in forceTree t18.
Eval compute in forceTree t19.
Eval compute in forceTree t20.
Eval compute in forceTree t21.
Eval compute in forceTree t22.
Eval compute in forceTree t23.
Goal True. let x := eval compute in t15 in idtac. Abort.
Goal True. let x := eval compute in t18 in idtac. Abort.
Goal True. let x := eval compute in t19 in idtac. Abort.
Goal True. let x := eval compute in t20 in idtac. Abort.
Goal True. let x := eval compute in t21 in idtac. Abort.
Goal True. let x := eval compute in t22 in idtac. Abort.
Goal True. let x := eval compute in t23 in idtac. Abort.

Eval lazy in forceTree t15.
Eval lazy in forceTree t18.
Eval lazy in forceTree t19.
Eval lazy in forceTree t20.
Eval lazy in forceTree t21.
Eval lazy in forceTree t22.
Eval lazy in forceTree t23.
Goal True. let x := eval lazy in t15 in idtac. Abort.
Goal True. let x := eval lazy in t18 in idtac. Abort.
Goal True. let x := eval lazy in t19 in idtac. Abort.
Goal True. let x := eval lazy in t20 in idtac. Abort.
Goal True. let x := eval lazy in t21 in idtac. Abort.
Goal True. let x := eval lazy in t22 in idtac. Abort.
Goal True. let x := eval lazy in t23 in idtac. Abort.


Chars 4225 - 4258 [Eval~vm_compute~in~forceTree~t15.] 0.002 secs (0.002u,0.s)
Chars 4259 - 4292 [Eval~vm_compute~in~forceTree~t18.] 0.019 secs (0.019u,0.s)
Chars 4293 - 4326 [Eval~vm_compute~in~forceTree~t19.] 0.041 secs (0.029u,0.011s)
Chars 4327 - 4360 [Eval~vm_compute~in~forceTree~t20.] 0.078 secs (0.07u,0.007s)
Chars 4361 - 4394 [Eval~vm_compute~in~forceTree~t21.] 0.152 secs (0.136u,0.016s)
Chars 4395 - 4428 [Eval~vm_compute~in~forceTree~t22.] 0.301 secs (0.289u,0.011s)
Chars 4429 - 4462 [Eval~vm_compute~in~forceTree~t23.] 0.747 secs (0.683u,0.064s)
Chars 4474 - 4515 [(let~x~:=~eval~vm_compute~in~t...] 0.028 secs (0.013u,0.004s)
Chars 4534 - 4575 [(let~x~:=~eval~vm_compute~in~t...] 0.192 secs (0.188u,0.003s)
Chars 4594 - 4635 [(let~x~:=~eval~vm_compute~in~t...] 0.525 secs (0.477u,0.048s)
Chars 4654 - 4695 [(let~x~:=~eval~vm_compute~in~t...] 0.718 secs (0.714u,0.003s)
Chars 4714 - 4755 [(let~x~:=~eval~vm_compute~in~t...] 1.573 secs (1.553u,0.02s)
Chars 4774 - 4815 [(let~x~:=~eval~vm_compute~in~t...] 2.962 secs (2.878u,0.083s)
Chars 4834 - 4875 [(let~x~:=~eval~vm_compute~in~t...] 5.975 secs (5.927u,0.047s)


Chars 4885 - 4915 [Eval~compute~in~forceTree~t15.]    0.023 secs (0.023u,0.s)
Chars 4916 - 4946 [Eval~compute~in~forceTree~t18.]    0.172 secs (0.156u,0.015s)
Chars 4947 - 4977 [Eval~compute~in~forceTree~t19.]    0.308 secs (0.296u,0.012s)
Chars 4978 - 5008 [Eval~compute~in~forceTree~t20.]    0.818 secs (0.782u,0.035s)
Chars 5009 - 5039 [Eval~compute~in~forceTree~t21.]    1.237 secs (1.217u,0.02s)
Chars 5040 - 5070 [Eval~compute~in~forceTree~t22.]    2.486 secs (2.426u,0.059s)
Chars 5071 - 5101 [Eval~compute~in~forceTree~t23.]    5.544 secs (5.5u,0.044s)
Chars 5113 - 5151 [(let~x~:=~eval~compute~in~t15~...] 0.013 secs (0.013u,0.s)
Chars 5170 - 5208 [(let~x~:=~eval~compute~in~t18~...] 0.128 secs (0.128u,0.s)
Chars 5227 - 5265 [(let~x~:=~eval~compute~in~t19~...] 0.293 secs (0.293u,0.s)
Chars 5284 - 5322 [(let~x~:=~eval~compute~in~t20~...] 0.635 secs (0.623u,0.011s)
Chars 5341 - 5379 [(let~x~:=~eval~compute~in~t21~...] 1.197 secs (1.145u,0.051s)
Chars 5398 - 5436 [(let~x~:=~eval~compute~in~t22~...] 2.952 secs (2.828u,0.124s)
Chars 5455 - 5493 [(let~x~:=~eval~compute~in~t23~...] 5.03  secs (4.934u,0.095s)


Chars 5502 - 5529 [Eval~lazy~in~forceTree~t15.]       0.053 secs (0.053u,0.s)
Chars 5530 - 5557 [Eval~lazy~in~forceTree~t18.]       0.295 secs (0.295u,0.s)
Chars 5558 - 5585 [Eval~lazy~in~forceTree~t19.]       0.74  secs (0.66u,0.079s)
Chars 5586 - 5613 [Eval~lazy~in~forceTree~t20.]       1.179 secs (1.151u,0.027s)
Chars 5614 - 5641 [Eval~lazy~in~forceTree~t21.]       2.293 secs (2.249u,0.044s)
Chars 5642 - 5669 [Eval~lazy~in~forceTree~t22.]       4.601 secs (4.501u,0.099s)
Chars 5670 - 5697 [Eval~lazy~in~forceTree~t23.]       9.658 secs (9.285u,0.372s)
Chars 5709 - 5744 [(let~x~:=~eval~lazy~in~t15~in~...] 0.01  secs (0.01u,0.s)
Chars 5763 - 5798 [(let~x~:=~eval~lazy~in~t18~in~...] 0.213 secs (0.209u,0.003s)
Chars 5817 - 5852 [(let~x~:=~eval~lazy~in~t19~in~...] 0.404 secs (0.4u,0.003s)
Chars 5871 - 5906 [(let~x~:=~eval~lazy~in~t20~in~...] 0.806 secs (0.794u,0.012s)
Chars 5925 - 5960 [(let~x~:=~eval~lazy~in~t21~in~...] 1.508 secs (1.424u,0.083s)
Chars 5979 - 6014 [(let~x~:=~eval~lazy~in~t22~in~...] 3.15  secs (3.046u,0.104s)
Chars 6033 - 6068 [(let~x~:=~eval~lazy~in~t23~in~...] 7.271 secs (7.114u,0.155s)
