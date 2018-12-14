

Require Import Utf8.

Definition U := Set.

Definition Nat : U
 := ∀(n : U), (n → n) → n → n.

Definition zero : Nat
 := λ n s z, z.

Definition suc : Nat → Nat
  := λ a n s z, s (a n s z).

Definition n2  : Nat := λ N s z, s (s z).
Definition n5  : Nat := λ N s z, s (s (s (s (s z)))).
Definition add : Nat → Nat → Nat := λ a b N s z, a N s (b N s z).
Definition mul : Nat → Nat → Nat := λ a b N s z, a N (b N s) z.

Definition n10    := mul n2    n5.
Definition n10b   := mul n5    n2.
Definition n100   := mul n10   n10.
Definition n100b  := mul n10b  n10b.
Definition n10k   := mul n100  n100.
Definition n10kb  := mul n100b n100b.
Definition n100k  := mul n10k  n10.
Definition n100kb := mul n10kb n10b.
Definition n1M    := mul n10k  n100.
Definition n1Mb   := mul n10kb n100b.
Definition n10M   := mul n1M   n10.
Definition n10Mb  := mul n1Mb  n10b.
Definition n100M  := mul n10M  n10.
Definition n200M  := mul n2    n100M.

Definition Vec : U → Nat → U
 := λ a n, ∀(V : Nat → U), V zero → (∀{n}, a → V n → V (suc n)) → V n.

Definition vnil : ∀{a}, Vec a zero
 := λ _ V n c, n.

Definition vcons {a n} : a → Vec a n → Vec a (suc n)
  := λ a xs V n c, c _ a (xs V n c).

Definition vec1 := vcons true (vcons true (vcons true vnil)).

Definition Eq : ∀{A}, A → A → U
 := λ A x y, ∀(P : A → U), P x → P y.

Definition refl : ∀{A}{x : A}, Eq x x
 := λ _ _ P px, px.

Definition Bool := ∀(B : U), B → B → B.
Definition true  : Bool := λ _ t f, t.
Definition false : Bool := λ _ t f, f.

Definition and : Bool → Bool → Bool
 := λ b1 b2, b1 Bool true b2.

Definition Pair : U → U → U
 := λ A B, ∀ (Pair : U)(pair : A → B → Pair), Pair.

Definition pair : ∀{A B}, A → B → Pair A B
 := λ _ _ a b Pair pair, pair a b.

Definition proj1 : ∀ {A B}, Pair A B → A
 := λ _ _ p, p _ (λ x y, x).

Definition proj2 : ∀ {A B}, Pair A B → B
 := λ _ _ p, p _ (λ x y, y).

Definition Top : U
 := ∀ (Top : U)(tt : Top), Top.

Definition tt : Top
 := λ Top tt, tt.

Definition Bot : U
 := ∀ (Bot : U), Bot.


Definition vecStress :=
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
   (vcons true (vcons true
   vnil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   ))))))))))))))))))).



Definition nfun : Nat → U
 := λ n, n U (λ A, U → A) U.

Definition synEqtest1 : nfun n10k → nfun n10k := λ x, x.


(* fails *)
(* Definition idStress {A} : A → A *)
(*  := id id id id id id id id id id id id id id id id id id id id *)
(*     id id id id id id id id id id id id id id id id id id id id. *)

(* fails *)
(* Definition pairStress : Top *)
(*  := let x0  := pair tt  tt  in *)
(*     let x1  := pair x0  x0  in *)
(*     let x2  := pair x1  x1  in *)
(*     let x3  := pair x2  x2  in *)
(*     let x4  := pair x3  x3  in *)
(*     let x5  := pair x4  x4  in *)
(*     let x6  := pair x5  x5  in *)
(*     let x7  := pair x6  x6  in *)
(*     let x8  := pair x7  x7  in *)
(*     let x9  := pair x8  x8  in *)
(*     let x10 := pair x9  x9  in *)
(*     let x11 := pair x10 x10 in *)
(*     let x12 := pair x11 x11 in *)
(*     let x13 := pair x12 x12 in *)
(*     let x14 := pair x13 x13 in *)
(*     let x15 := pair x14 x14 in *)
(*     let x16 := pair x15 x15 in *)
(*     let x17 := pair x16 x16 in *)
(*     let x18 := pair x17 x17 in *)
(*     let x19 := pair x18 x18 in *)
(*     let x20 := pair x19 x19 in *)
(*     tt. *)


Definition forceNat : Nat → Bool := λ n, n _ (λ x, x) true.

(* Eval vm_compute in forceNat n10M. *)
(* Eval cbv in forceNat n10M. *)
(* Eval lazy in forceNat n10M. *)
(* Eval native_compute in forceNat n10M. *)

(* Definition conv10k   : Eq n10k n10kb := refl. *)
(* Definition conv100k  : Eq n100k n100kb := refl. *)
(* Definition conv1M : Eq n1M n1Mb := refl. *)
(* Definition conv10M : Eq n10M n10Mb := refl. *)
(* Definition convNfun1M : Eq (nfun n1M) (nfun n1Mb) := refl. *)
(* Definition conv10kmeta : Eq n10k (add n10kb _) := refl. *)

(* Definition conv1Mmeta : Eq n1M (add n1Mb _) := refl. *)


(* -------------------------------------------------------------------------------- *)

Definition localCBN : Nat → Bool
 := λ n, let m := forceNat (mul n n100k) in
         n _ (λ b, and m b) true.

Definition cbnReference := forceNat (mul n10 n100k).
Definition localCBNtest := localCBN n10.

(* Eval lazy in localCBNtest. *)



(* Church-coded simply typed lambda calculus *)
(* -------------------------------------------------------------------------------- *)

Definition Ty : U
 := ∀ (Ty  : U)
      (ι   : Ty)
      (fn  : Ty → Ty → Ty)
    , Ty.

Definition ι : Ty
 := λ _ ι _, ι.

Definition fn : Ty → Ty → Ty
 := λ A B Ty ι fn, fn (A Ty ι fn) (B Ty ι fn).

Definition Con : U
 := ∀ (Con : U)
      (nil  : Con)
      (cons : Con → Ty → Con)
    , Con.

Definition nil : Con
 := λ Con nil cons, nil.

Definition cons : Con → Ty → Con
 := λ Γ A Con nil cons, cons (Γ Con nil cons) A.

Definition Var : Con → Ty → U
 := λ Γ A,
      ∀ (Var : Con → Ty → U)
        (vz  : ∀ {Γ A}, Var (cons Γ A) A)
        (vs  : ∀ {Γ B A}, Var Γ A → Var (cons Γ B) A)
      , Var Γ A.

Definition vz {Γ A} : Var (cons Γ A) A
 := λ V vz vs, vz _ _.

Definition vs : ∀ {Γ B A}, Var Γ A → Var (cons Γ B) A
 := λ _ _ _ x Var vz vs, vs _ _ _ (x Var vz vs).

Definition Tm : Con → Ty → U
 := λ Γ A,
     ∀ (Tm  : Con → Ty → U)
       (var : ∀{Γ A}, Var Γ A → Tm Γ A)
       (lam : ∀{Γ A B}, Tm (cons Γ A) B → Tm Γ (fn A B))
       (app : ∀{Γ A B}, Tm Γ (fn A B) → Tm Γ A → Tm Γ B)
     , Tm Γ A.

Definition var : ∀{Γ A}, Var Γ A → Tm Γ A
 := λ _ _ x Tm var lam app, var _ _ x.

Definition lam : ∀{Γ A B}, Tm (cons Γ A) B → Tm Γ (fn A B)
 := λ _ _ _ t Tm var lam app, lam _ _ _ (t Tm var lam app).

Definition  app : ∀ {Γ A B}, Tm Γ (fn A B) → Tm Γ A → Tm Γ B
  := λ _ _ _ t u Tm var lam app, app _ _ _ (t Tm var lam app) (u Tm var lam app).


(* Well-typed interpreter for Church-coded STLC *)
(* -------------------------------------------------------------------------------- *)

Definition EvalTy : Ty → U
 := λ A, A _ Bot (λ A B, A → B).

Definition EvalCon : Con → U
 := λ Γ, Γ _ Top (λ Δ A, Pair Δ (EvalTy A)).

Definition EvalVar : ∀ {Γ A}, Var Γ A → EvalCon Γ → EvalTy A
  := λ Γ A x, x (λ Γ A, EvalCon Γ → EvalTy A)
                (λ _ _ env, proj2 env)
                (λ _ _ _ hyp env, hyp (proj1 env)).

Definition EvalTm : ∀ {Γ A}, Tm Γ A → EvalCon Γ → EvalTy A
 := λ _ _ t, t (λ Γ A, EvalCon Γ → EvalTy A)
               (λ _ _, EvalVar)
	       (λ _ _ _ t env α, t (pair env α))
	       (λ _ _ _ t u env, t env (u env)).


(* Large embedded STLC term *)
(* -------------------------------------------------------------------------------- *)


Definition t1 : Tm nil (fn (fn ι ι) (fn ι ι))
 := lam (lam (
      app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
     (var vz))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     ))))))))))))))))))))))))))))))))))))))

        )).

Definition evalTest := EvalTm t1 tt.

Eval cbv in evalTest.
