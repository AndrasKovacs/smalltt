def Ty : Type 1
 := ∀ (Ty : Type)
      (ι   : Ty)
      (arr : Ty → Ty → Ty)
    , Ty

def ι : Ty := λ _ ι _ => ι

def arr : Ty → Ty → Ty
 := λ A B Ty ι arr =>
     arr (A Ty ι arr) (B Ty ι arr)

def Con : Type 1
 := ∀ (Con  : Type)
      (nil  : Con)
      (snoc : Con → Ty → Con)
    , Con

def nil : Con
 := λ Con nil snoc => nil

def snoc : Con → Ty → Con
 := λ Γ A Con nil snoc => snoc (Γ Con nil snoc) A

def Var : Con → Ty → Type 1
 := λ Γ A =>
   ∀ (Var : Con → Ty → Type)
     (vz  : ∀ Γ A, Var (snoc Γ A) A)
     (vs  : ∀ Γ B A, Var Γ A → Var (snoc Γ B) A)
   , Var Γ A

def vz {Γ A} : Var (snoc Γ A) A
 := λ Var vz vs => vz _ _

def vs {Γ B A} : Var Γ A → Var (snoc Γ B) A
 := λ x Var vz vs => vs _ _ _ (x Var vz vs)

def Tm : Con → Ty → Type 1
 := λ Γ A =>
   ∀ (Tm  : Con → Ty → Type)
     (var   : ∀ Γ A     , Var Γ A → Tm Γ A)
     (lam   : ∀ Γ A B   , Tm (snoc Γ A) B → Tm Γ (arr A B))
     (app   : ∀ Γ A B   , Tm Γ (arr A B) → Tm Γ A → Tm Γ B)
   , Tm Γ A

def var {Γ A} : Var Γ A → Tm Γ A
 := λ x Tm var lam app =>
     var _ _ x

def lam {Γ A B} : Tm (snoc Γ A) B → Tm Γ (arr A B)
 := λ t Tm var lam app =>
     lam _ _ _ (t Tm var lam app)

def app {Γ A B} : Tm Γ (arr A B) → Tm Γ A → Tm Γ B
 := λ t u Tm var lam app =>
     app _ _ _
         (t Tm var lam app)
         (u Tm var lam app)

def v0 {Γ A} : Tm (snoc Γ A) A
 := var vz

def v1 {Γ A B} : Tm (snoc (snoc Γ A) B) A
 := var (vs vz)

def v2 {Γ A B C} : Tm (snoc (snoc (snoc Γ A) B) C) A
 := var (vs (vs vz))

def v3 {Γ A B C D} : Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A
 := var (vs (vs (vs vz)))

def v4 {Γ A B C D E} : Tm (snoc (snoc (snoc (snoc (snoc Γ A) B) C) D) E) A
 := var (vs (vs (vs (vs vz))))

def test {Γ A} : Tm Γ (arr (arr A A) (arr A A))
 := lam (lam (app v1 (app v1 (app v1 (app v1 (app v1 (app v1 v0)))))))