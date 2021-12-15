Definition Ty : Set
 := forall (Ty : Set)
      (nat top bot  : Ty)
      (arr prod sum : Ty -> Ty -> Ty)
    , Ty.

Definition nat : Ty := fun _ nat _ _ _ _ _ => nat.
Definition top : Ty := fun _ _ top _ _ _ _ => top.
Definition bot : Ty := fun _ _ _ bot _ _ _ => bot.

Definition arr : Ty -> Ty -> Ty
 := fun A B Ty nat top bot arr prod sum =>
     arr (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum).

Definition prod : Ty -> Ty -> Ty
 := fun A B Ty nat top bot arr prod sum =>
     prod (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum).

Definition sum : Ty -> Ty -> Ty
 := fun A B Ty nat top bot arr prod sum =>
     sum (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum).

Definition Con : Set
 := forall (Con  : Set)
      (nil  : Con)
      (snoc : Con -> Ty -> Con)
    , Con.

Definition nil : Con
 := fun Con nil snoc => nil.

Definition snoc : Con -> Ty -> Con
 := fun Γ A Con nil snoc => snoc (Γ Con nil snoc) A.

Definition Var : Con -> Ty -> Set
 := fun Γ A =>
   forall (Var : Con -> Ty -> Set)
     (vz  : forall Γ A, Var (snoc Γ A) A)
     (vs  : forall Γ B A, Var Γ A -> Var (snoc Γ B) A)
   , Var Γ A.

Definition vz {Γ A} : Var (snoc Γ A) A
 := fun Var vz vs => vz _ _.

Definition vs {Γ B A} : Var Γ A -> Var (snoc Γ B) A
 := fun x Var vz vs => vs _ _ _ (x Var vz vs).

Definition Tm : Con -> Ty -> Set
 := fun Γ A =>
   forall (Tm  : Con -> Ty -> Set)
     (var   : forall Γ A     , Var Γ A -> Tm Γ A)
     (lam   : forall Γ A B   , Tm (snoc Γ A) B -> Tm Γ (arr A B))
     (app   : forall Γ A B   , Tm Γ (arr A B) -> Tm Γ A -> Tm Γ B)
     (tt    : forall Γ       , Tm Γ top)
     (pair  : forall Γ A B   , Tm Γ A -> Tm Γ B -> Tm Γ (prod A B))
     (fst   : forall Γ A B   , Tm Γ (prod A B) -> Tm Γ A)
     (snd   : forall Γ A B   , Tm Γ (prod A B) -> Tm Γ B)
     (left  : forall Γ A B   , Tm Γ A -> Tm Γ (sum A B))
     (right : forall Γ A B   , Tm Γ B -> Tm Γ (sum A B))
     (case  : forall Γ A B C , Tm Γ (sum A B) -> Tm Γ (arr A C) -> Tm Γ (arr B C) -> Tm Γ C)
     (zero  : forall Γ       , Tm Γ nat)
     (suc   : forall Γ       , Tm Γ nat -> Tm Γ nat)
     (rec   : forall Γ A     , Tm Γ nat -> Tm Γ (arr nat (arr A A)) -> Tm Γ A -> Tm Γ A)
   , Tm Γ A.

Definition var {Γ A} : Var Γ A -> Tm Γ A
 := fun x Tm var lam app tt pair fst snd left right case zero suc rec =>
     var _ _ x.

Definition lam {Γ A B} : Tm (snoc Γ A) B -> Tm Γ (arr A B)
 := fun t Tm var lam app tt pair fst snd left right case zero suc rec =>
     lam _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition app {Γ A B} : Tm Γ (arr A B) -> Tm Γ A -> Tm Γ B
 := fun t u Tm var lam app tt pair fst snd left right case zero suc rec =>
     app _ _ _
         (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec).

Definition tt {Γ} : Tm Γ top
 := fun Tm var lam app tt pair fst snd left right case zero suc rec => tt _.

Definition pair {Γ A B} : Tm Γ A -> Tm Γ B -> Tm Γ (prod A B)
 := fun t u Tm var lam app tt pair fst snd left right case zero suc rec =>
     pair _ _ _
          (t Tm var lam app tt pair fst snd left right case zero suc rec)
          (u Tm var lam app tt pair fst snd left right case zero suc rec).

Definition fst {Γ A B} : Tm Γ (prod A B) -> Tm Γ A
 := fun t Tm var lam app tt pair fst snd left right case zero suc rec =>
     fst _ _ _
         (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition snd {Γ A B} : Tm Γ (prod A B) -> Tm Γ B
 := fun t Tm var lam app tt pair fst snd left right case zero suc rec =>
     snd _ _ _
          (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition left {Γ A B} : Tm Γ A -> Tm Γ (sum A B)
 := fun t Tm var lam app tt pair fst snd left right case zero suc rec =>
     left _ _ _
          (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition right {Γ A B} : Tm Γ B -> Tm Γ (sum A B)
 := fun t Tm var lam app tt pair fst snd left right case zero suc rec =>
     right _ _ _
            (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition case {Γ A B C} : Tm Γ (sum A B) -> Tm Γ (arr A C) -> Tm Γ (arr B C) -> Tm Γ C
 := fun t u v Tm var lam app tt pair fst snd left right case zero suc rec =>
     case _ _ _ _
           (t Tm var lam app tt pair fst snd left right case zero suc rec)
           (u Tm var lam app tt pair fst snd left right case zero suc rec)
           (v Tm var lam app tt pair fst snd left right case zero suc rec).

Definition zero  {Γ} : Tm Γ nat
 := fun Tm var lam app tt pair fst snd left right case zero suc rec => zero _.

Definition suc {Γ} : Tm Γ nat -> Tm Γ nat
 := fun t Tm var lam app tt pair fst snd left right case zero suc rec =>
   suc _ (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition rec {Γ A} : Tm Γ nat -> Tm Γ (arr nat (arr A A)) -> Tm Γ A -> Tm Γ A
 := fun t u v Tm var lam app tt pair fst snd left right case zero suc rec =>
     rec _ _
         (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec)
         (v Tm var lam app tt pair fst snd left right case zero suc rec).

Definition v0 {Γ A} : Tm (snoc Γ A) A
 := var vz.

Definition v1 {Γ A B} : Tm (snoc (snoc Γ A) B) A
 := var (vs vz).

Definition v2 {Γ A B C} : Tm (snoc (snoc (snoc Γ A) B) C) A
 := var (vs (vs vz)).

Definition v3 {Γ A B C D} : Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A
 := var (vs (vs (vs vz))).

Definition tbool : Ty
 := sum top top.

Definition ttrue {Γ} : Tm Γ tbool
 := left tt.

Definition tfalse {Γ} : Tm Γ tbool
 := right tt.

Definition ifthenelse {Γ A} : Tm Γ (arr tbool (arr A (arr A A)))
 := lam (lam (lam (case v2 (lam v2) (lam v1)))).

Definition times4 {Γ A} : Tm Γ (arr (arr A A) (arr A A))
  := lam (lam (app v1 (app v1 (app v1 (app v1 v0))))).

Definition add {Γ} : Tm Γ (arr nat (arr nat nat))
 := lam (rec v0
      (lam (lam (lam (suc (app v1 v0)))))
      (lam v0)).

Definition mul {Γ} : Tm Γ (arr nat (arr nat nat))
 := lam (rec v0
     (lam (lam (lam (app (app add (app v1 v0)) v0))))
     (lam zero)).

Definition fact {Γ} : Tm Γ (arr nat nat)
 := lam (rec v0 (lam (lam (app (app mul (suc v1)) v0)))
        (suc zero)).
