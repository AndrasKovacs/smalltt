{-# OPTIONS --type-in-type #-}

Ty : Set; Ty
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι   : Ty; ι = λ _ ι _ → ι
arr : Ty → Ty → Ty; arr = λ A B Ty ι arr → arr (A Ty ι arr) (B Ty ι arr)

Con : Set;Con
 = (Con : Set)
   (nil  : Con)
   (snoc : Con → Ty → Con)
 → Con

nil : Con;nil
 = λ Con nil snoc → nil

snoc : Con → Ty → Con;snoc
 = λ Γ A Con nil snoc → snoc (Γ Con nil snoc) A

Var : Con → Ty → Set;Var
 = λ Γ A →
   (Var : Con → Ty → Set)
   (vz  : (Γ : _)(A : _) → Var (snoc Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var Γ A → Var (snoc Γ B) A)
 → Var Γ A

vz : ∀{Γ A} → Var (snoc Γ A) A;vz
 = λ Var vz vs → vz _ _

vs : ∀{Γ B A} → Var Γ A → Var (snoc Γ B) A;vs
 = λ x Var vz vs → vs _ _ _ (x Var vz vs)

Tm : Con → Ty → Set;Tm
 = λ Γ A →
   (Tm    : Con → Ty → Set)
   (var   : (Γ : _) (A : _) → Var Γ A → Tm Γ A)
   (lam   : (Γ : _) (A B : _) → Tm (snoc Γ A) B → Tm Γ (arr A B))
   (app   : (Γ : _) (A B : _) → Tm Γ (arr A B) → Tm Γ A → Tm Γ B)
 → Tm Γ A

var : ∀{Γ A} → Var Γ A → Tm Γ A;var
 = λ x Tm var lam app → var _ _ x

lam : ∀{Γ A B} → Tm (snoc Γ A) B → Tm Γ (arr A B);lam
 = λ t Tm var lam app → lam _ _ _ (t Tm var lam app)

app : ∀{Γ A B} → Tm Γ (arr A B) → Tm Γ A → Tm Γ B;app
 = λ t u Tm var lam app →
     app _ _ _ (t Tm var lam app) (u Tm var lam app)

v0 : ∀{Γ A} → Tm (snoc Γ A) A;v0
 = var vz

v1 : ∀{Γ A B} → Tm (snoc (snoc Γ A) B) A;v1
 = var (vs vz)

v2 : ∀{Γ A B C} → Tm (snoc (snoc (snoc Γ A) B) C) A;v2
 = var (vs (vs vz))

v3 : ∀{Γ A B C D} → Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A;v3
 = var (vs (vs (vs vz)))

v4 : ∀{Γ A B C D E} → Tm (snoc (snoc (snoc (snoc (snoc Γ A) B) C) D) E) A;v4
 = var (vs (vs (vs (vs vz))))

test1 : ∀{Γ A} → Tm Γ (arr (arr A A) (arr A A));test1
  = lam (lam (app v1 (app v1 (app v1 (app v1 (app v1 (app v1 v0)))))))
