
-- Church-coded STLC
--------------------------------------------------------------------------------

def Ty : Type 1
 := ∀ (Ty           : Type)
      (nat top bot  : Ty)
      (arr prod sum : Ty → Ty → Ty)
    , Ty

def nat : Ty := λ _ nat _ _ _ _ _ => nat
def top : Ty := λ _ _ top _ _ _ _ => top
def bot : Ty := λ _ _ _ bot _ _ _ => bot

def arr : Ty → Ty → Ty
 := λ A B Ty nat top bot arr prod sum =>
     arr (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)

def prod : Ty → Ty → Ty
 := λ A B Ty nat top bot arr prod sum =>
     prod (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)

def sum : Ty → Ty → Ty
 := λ A B Ty nat top bot arr prod sum =>
     sum (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)

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
     (vz  : ∀{Γ A}, Var (snoc Γ A) A)
     (vs  : ∀{Γ B A}, Var Γ A → Var (snoc Γ B) A)
   , Var Γ A

def vz : ∀ {Γ A}, Var (snoc Γ A) A
 := λ Var vz vs => vz

def vs : ∀ {Γ B A}, Var Γ A → Var (snoc Γ B) A
 := λ x Var vz vs => vs (x Var vz vs)

def Tm : Con → Ty → Type 1
 := λ Γ A =>
   ∀ (Tm  : Con → Ty → Type)
     (var : ∀ {Γ A}, Var Γ A → Tm Γ A)
     (lam : ∀ {Γ A B}, (Tm (snoc Γ A) B → Tm Γ (arr A B)))
     (app   : ∀ {Γ A B}   , Tm Γ (arr A B) → Tm Γ A → Tm Γ B)
     (tt    : ∀ {Γ}       , Tm Γ top)
     (pair  : ∀ {Γ A B}   , Tm Γ A → Tm Γ B → Tm Γ (prod A B))
     (fst   : ∀ {Γ A B}   , Tm Γ (prod A B) → Tm Γ A)
     (snd   : ∀ {Γ A B}   , Tm Γ (prod A B) → Tm Γ B)
     (left  : ∀ {Γ A B}   , Tm Γ A → Tm Γ (sum A B))
     (right : ∀ {Γ A B}   , Tm Γ B → Tm Γ (sum A B))
     (case  : ∀ {Γ A B C} , Tm Γ (sum A B) → Tm Γ (arr A C) → Tm Γ (arr B C) → Tm Γ C)
     (zero  : ∀ {Γ}       , Tm Γ nat)
     (suc   : ∀ {Γ}       , Tm Γ nat → Tm Γ nat)
     (rec   : ∀ {Γ A}     , Tm Γ nat → Tm Γ (arr nat (arr A A)) → Tm Γ A → Tm Γ A)
   , Tm Γ A

def var : ∀ {Γ A}, Var Γ A → Tm Γ A
 := λ x Tm var lam app tt pair fst snd left right case zero suc rec =>
     var x

def lam : ∀ {Γ A B} , Tm (snoc Γ A) B → Tm Γ (arr A B)
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec =>
     lam (t Tm var lam app tt pair fst snd left right case zero suc rec)

def app : ∀ {Γ A B} , Tm Γ (arr A B) → Tm Γ A → Tm Γ B
 := λ t u Tm var lam app tt pair fst snd left right case zero suc rec =>
     app (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec)

def tt : ∀ {Γ} , Tm Γ top
 := λ Tm var lam app tt pair fst snd left right case zero suc rec => tt

def pair : ∀ {Γ A B} , Tm Γ A → Tm Γ B → Tm Γ (prod A B)
 := λ t u Tm var lam app tt pair fst snd left right case zero suc rec =>
     pair (t Tm var lam app tt pair fst snd left right case zero suc rec)
          (u Tm var lam app tt pair fst snd left right case zero suc rec)

def fst : ∀ {Γ A B} , Tm Γ (prod A B) → Tm Γ A
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec =>
     fst (t Tm var lam app tt pair fst snd left right case zero suc rec)

def snd : ∀ {Γ A B} , Tm Γ (prod A B) → Tm Γ B
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec =>
     snd (t Tm var lam app tt pair fst snd left right case zero suc rec)

def left : ∀ {Γ A B} , Tm Γ A → Tm Γ (sum A B)
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec =>
     left (t Tm var lam app tt pair fst snd left right case zero suc rec)

def right : ∀ {Γ A B} , Tm Γ B → Tm Γ (sum A B)
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec =>
     right (t Tm var lam app tt pair fst snd left right case zero suc rec)

def case : ∀ {Γ A B C} , Tm Γ (sum A B) → Tm Γ (arr A C) → Tm Γ (arr B C) → Tm Γ C
 := λ t u v Tm var lam app tt pair fst snd left right case zero suc rec =>
     case (t Tm var lam app tt pair fst snd left right case zero suc rec)
          (u Tm var lam app tt pair fst snd left right case zero suc rec)
          (v Tm var lam app tt pair fst snd left right case zero suc rec)

def zero  : ∀ {Γ} , Tm Γ nat
 := λ Tm var lam app tt pair fst snd left right case zero suc rec => zero

def suc : ∀ {Γ} , Tm Γ nat → Tm Γ nat
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec =>
   suc (t Tm var lam app tt pair fst snd left right case zero suc rec)

def rec : ∀ {Γ A} , Tm Γ nat → Tm Γ (arr nat (arr A A)) → Tm Γ A → Tm Γ A
 := λ t u v Tm var lam app tt pair fst snd left right case zero suc rec =>
     rec (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec)
         (v Tm var lam app tt pair fst snd left right case zero suc rec)

--------------------------------------------------------------------------------

def v0 : ∀ {Γ A}, Tm (snoc Γ A) A
 := var vz

def v1 : ∀ {Γ A B}, Tm (snoc (snoc Γ A) B) A
 := var (vs vz)

def v2 : ∀ {Γ A B C}, Tm (snoc (snoc (snoc Γ A) B) C) A
 := var (vs (vs vz))

def v3 : ∀ {Γ A B C D}, Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A
 := var (vs (vs (vs vz)))

def tbool : Ty
 := sum top top

def true : ∀ {Γ}, Tm Γ tbool
 := left tt

def tfalse : ∀ {Γ}, Tm Γ tbool
 := right tt

def ifthenelse : ∀ {Γ A}, Tm Γ (arr tbool (arr A (arr A A)))
 := lam (lam (lam (case v2 (lam v2) (lam v1))))

def times4 : ∀ {Γ A}, Tm Γ (arr (arr A A) (arr A A))
  := lam (lam (app v1 (app v1 (app v1 (app v1 v0)))))

def add : ∀ {Γ}, Tm Γ (arr nat (arr nat nat))
 := lam (rec v0
      (lam (lam (lam (suc (app v1 v0)))))
      (lam v0))

def mul : ∀ {Γ}, Tm Γ (arr nat (arr nat nat))
 := lam (rec v0
     (lam (lam (lam (app (app add (app v1 v0)) v0))))
     (lam zero))

def fact : ∀ {Γ}, Tm Γ (arr nat nat)
 := lam (rec v0 (lam (lam (app (app mul (suc v1)) v0)))
                (suc zero))
