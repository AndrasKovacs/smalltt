Definition Ty : Set
 := forall (Ty : Set)
      (base   : Ty)
      (arr : Ty -> Ty -> Ty)
    , Ty.

Definition base : Ty := fun _ base _ => base.

Definition arr : Ty -> Ty -> Ty
 := fun A B Ty base arr =>
     arr (A Ty base arr) (B Ty base arr).

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
   , Tm Γ A.

Definition var {Γ A} : Var Γ A -> Tm Γ A
 := fun x Tm var lam app =>
     var _ _ x.

Definition lam {Γ A B} : Tm (snoc Γ A) B -> Tm Γ (arr A B)
 := fun t Tm var lam app =>
     lam _ _ _ (t Tm var lam app).

Definition app {Γ A B} : Tm Γ (arr A B) -> Tm Γ A -> Tm Γ B
 := fun t u Tm var lam app =>
     app _ _ _
         (t Tm var lam app)
         (u Tm var lam app).

Definition v0 {Γ A} : Tm (snoc Γ A) A
 := var vz.

Definition v1 {Γ A B} : Tm (snoc (snoc Γ A) B) A
 := var (vs vz).

Definition v2 {Γ A B C} : Tm (snoc (snoc (snoc Γ A) B) C) A
 := var (vs (vs vz)).

Definition v3 {Γ A B C D} : Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A
 := var (vs (vs (vs vz))).

Definition v4 {Γ A B C D E} : Tm (snoc (snoc (snoc (snoc (snoc Γ A) B) C) D) E) A
 := var (vs (vs (vs (vs vz)))).

Definition test {Γ A} : Tm Γ (arr (arr A A) (arr A A))
 := lam (lam (app v1 (app v1 (app v1 (app v1 (app v1 (app v1 v0))))))).
