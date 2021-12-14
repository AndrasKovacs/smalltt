Require Import Coq.Unicode.Utf8.

Definition Ty : Set
 := ∀ (Ty : Set)
      (ι   : Ty)
      (arr : Ty → Ty → Ty)
    , Ty.

Definition ι : Ty := λ _ ι _, ι.

Definition arr : Ty → Ty → Ty
 := λ A B Ty ι arr,
     arr (A Ty ι arr) (B Ty ι arr).

Definition Con : Set
 := ∀ (Con  : Set)
      (nil  : Con)
      (snoc : Con → Ty → Con)
    , Con.

Definition nil : Con
 := λ Con nil snoc , nil.

Definition snoc : Con → Ty → Con
 := λ Γ A Con nil snoc , snoc (Γ Con nil snoc) A.

Definition Var : Con → Ty → Set
 := λ Γ A ,
   ∀ (Var : Con → Ty → Set)
     (vz  : ∀ Γ A, Var (snoc Γ A) A)
     (vs  : ∀ Γ B A, Var Γ A → Var (snoc Γ B) A)
   , Var Γ A.

Definition vz {Γ A} : Var (snoc Γ A) A
 := λ Var vz vs , vz _ _.

Definition vs {Γ B A} : Var Γ A → Var (snoc Γ B) A
 := λ x Var vz vs , vs _ _ _ (x Var vz vs).

Definition Tm : Con → Ty → Set
 := λ Γ A ,
   ∀ (Tm  : Con → Ty → Set)
     (var   : ∀ Γ A     , Var Γ A → Tm Γ A)
     (lam   : ∀ Γ A B   , Tm (snoc Γ A) B → Tm Γ (arr A B))
     (app   : ∀ Γ A B   , Tm Γ (arr A B) → Tm Γ A → Tm Γ B)
   , Tm Γ A.

Definition var {Γ A} : Var Γ A → Tm Γ A
 := λ x Tm var lam app,
     var _ _ x.

Definition lam {Γ A B} : Tm (snoc Γ A) B → Tm Γ (arr A B)
 := λ t Tm var lam app,
     lam _ _ _ (t Tm var lam app).

Definition app {Γ A B} : Tm Γ (arr A B) → Tm Γ A → Tm Γ B
 := λ t u Tm var lam app,
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
