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

def ttrue : ∀ {Γ}, Tm Γ tbool
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
def Ty1 : Type 1
 := ∀ (Ty1           : Type)
      (nat top bot  : Ty1)
      (arr prod sum : Ty1 → Ty1 → Ty1)
    , Ty1

def nat1 : Ty1 := λ _ nat1 _ _ _ _ _ => nat1
def top1 : Ty1 := λ _ _ top1 _ _ _ _ => top1
def bot1 : Ty1 := λ _ _ _ bot1 _ _ _ => bot1

def arr1 : Ty1 → Ty1 → Ty1
 := λ A B Ty1 nat1 top1 bot1 arr1 prod sum =>
     arr1 (A Ty1 nat1 top1 bot1 arr1 prod sum) (B Ty1 nat1 top1 bot1 arr1 prod sum)

def prod1 : Ty1 → Ty1 → Ty1
 := λ A B Ty1 nat1 top1 bot1 arr1 prod1 sum =>
     prod1 (A Ty1 nat1 top1 bot1 arr1 prod1 sum) (B Ty1 nat1 top1 bot1 arr1 prod1 sum)

def sum1 : Ty1 → Ty1 → Ty1
 := λ A B Ty1 nat1 top1 bot1 arr1 prod1 sum1 =>
     sum1 (A Ty1 nat1 top1 bot1 arr1 prod1 sum1) (B Ty1 nat1 top1 bot1 arr1 prod1 sum1)

def Con1 : Type 1
 := ∀ (Con1  : Type)
      (nil  : Con1)
      (snoc : Con1 → Ty1 → Con1)
    , Con1

def nil1 : Con1
 := λ Con1 nil1 snoc => nil1

def snoc1 : Con1 → Ty1 → Con1
 := λ Γ A Con1 nil1 snoc1 => snoc1 (Γ Con1 nil1 snoc1) A

def Var1 : Con1 → Ty1 → Type 1
 := λ Γ A =>
   ∀ (Var1 : Con1 → Ty1 → Type)
     (vz  : ∀{Γ A}, Var1 (snoc1 Γ A) A)
     (vs  : ∀{Γ B A}, Var1 Γ A → Var1 (snoc1 Γ B) A)
   , Var1 Γ A

def vz1 : ∀ {Γ A}, Var1 (snoc1 Γ A) A
 := λ Var1 vz1 vs => vz1

def vs1 : ∀ {Γ B A}, Var1 Γ A → Var1 (snoc1 Γ B) A
 := λ x Var1 vz1 vs1 => vs1 (x Var1 vz1 vs1)

def Tm1 : Con1 → Ty1 → Type 1
 := λ Γ A =>
   ∀ (Tm1  : Con1 → Ty1 → Type)
     (var : ∀ {Γ A}, Var1 Γ A → Tm1 Γ A)
     (lam : ∀ {Γ A B}, (Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B)))
     (app   : ∀ {Γ A B}   , Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B)
     (tt    : ∀ {Γ}       , Tm1 Γ top1)
     (pair  : ∀ {Γ A B}   , Tm1 Γ A → Tm1 Γ B → Tm1 Γ (prod1 A B))
     (fst   : ∀ {Γ A B}   , Tm1 Γ (prod1 A B) → Tm1 Γ A)
     (snd   : ∀ {Γ A B}   , Tm1 Γ (prod1 A B) → Tm1 Γ B)
     (left  : ∀ {Γ A B}   , Tm1 Γ A → Tm1 Γ (sum1 A B))
     (right : ∀ {Γ A B}   , Tm1 Γ B → Tm1 Γ (sum1 A B))
     (case  : ∀ {Γ A B C} , Tm1 Γ (sum1 A B) → Tm1 Γ (arr1 A C) → Tm1 Γ (arr1 B C) → Tm1 Γ C)
     (zero  : ∀ {Γ}       , Tm1 Γ nat1)
     (suc   : ∀ {Γ}       , Tm1 Γ nat1 → Tm1 Γ nat1)
     (rec   : ∀ {Γ A}     , Tm1 Γ nat1 → Tm1 Γ (arr1 nat1 (arr1 A A)) → Tm1 Γ A → Tm1 Γ A)
   , Tm1 Γ A

def var1 : ∀ {Γ A}, Var1 Γ A → Tm1 Γ A
 := λ x Tm1 var1 lam app tt pair fst snd left right case zero suc rec =>
     var1 x

def lam1 : ∀ {Γ A B} , Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B)
 := λ t Tm1 var1 lam1 app tt pair fst snd left right case zero suc rec =>
     lam1 (t Tm1 var1 lam1 app tt pair fst snd left right case zero suc rec)

def app1 : ∀ {Γ A B} , Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B
 := λ t u Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec =>
     app1 (t Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec)
         (u Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec)

def tt1 : ∀ {Γ} , Tm1 Γ top1
 := λ Tm1 var1 lam1 app1 tt1 pair fst snd left right case zero suc rec => tt1

def pair1 : ∀ {Γ A B} , Tm1 Γ A → Tm1 Γ B → Tm1 Γ (prod1 A B)
 := λ t u Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec =>
     pair1 (t Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec)
          (u Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec)

def fst1 : ∀ {Γ A B} , Tm1 Γ (prod1 A B) → Tm1 Γ A
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd left right case zero suc rec =>
     fst1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd left right case zero suc rec)

def snd1 : ∀ {Γ A B} , Tm1 Γ (prod1 A B) → Tm1 Γ B
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left right case zero suc rec =>
     snd1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left right case zero suc rec)

def left1 : ∀ {Γ A B} , Tm1 Γ A → Tm1 Γ (sum1 A B)
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right case zero suc rec =>
     left1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right case zero suc rec)

def right1 : ∀ {Γ A B} , Tm1 Γ B → Tm1 Γ (sum1 A B)
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case zero suc rec =>
     right1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case zero suc rec)

def case1 : ∀ {Γ A B C} , Tm1 Γ (sum1 A B) → Tm1 Γ (arr1 A C) → Tm1 Γ (arr1 B C) → Tm1 Γ C
 := λ t u v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec =>
     case1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)
          (u Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)
          (v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)

def zero1  : ∀ {Γ} , Tm1 Γ nat1
 := λ Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc rec => zero1

def suc1 : ∀ {Γ} , Tm1 Γ nat1 → Tm1 Γ nat1
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec =>
   suc1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec)

def rec1 : ∀ {Γ A} , Tm1 Γ nat1 → Tm1 Γ (arr1 nat1 (arr1 A A)) → Tm1 Γ A → Tm1 Γ A
 := λ t u v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1 =>
     rec1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)
         (u Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)
         (v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)

def v01 : ∀ {Γ A}, Tm1 (snoc1 Γ A) A
 := var1 vz1

def v11 : ∀ {Γ A B}, Tm1 (snoc1 (snoc1 Γ A) B) A
 := var1 (vs1 vz1)

def v21 : ∀ {Γ A B C}, Tm1 (snoc1 (snoc1 (snoc1 Γ A) B) C) A
 := var1 (vs1 (vs1 vz1))

def v31 : ∀ {Γ A B C D}, Tm1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) A
 := var1 (vs1 (vs1 (vs1 vz1)))

def tbool1 : Ty1
 := sum1 top1 top1

def ttrue1 : ∀ {Γ}, Tm1 Γ tbool1
 := left1 tt1

def tfalse1 : ∀ {Γ}, Tm1 Γ tbool1
 := right1 tt1

def ifthenelse1 : ∀ {Γ A}, Tm1 Γ (arr1 tbool1 (arr1 A (arr1 A A)))
 := lam1 (lam1 (lam1 (case1 v21 (lam1 v21) (lam1 v11))))

def times41 : ∀ {Γ A}, Tm1 Γ (arr1 (arr1 A A) (arr1 A A))
  := lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01)))))

def add1 : ∀ {Γ}, Tm1 Γ (arr1 nat1 (arr1 nat1 nat1))
 := lam1 (rec1 v01
      (lam1 (lam1 (lam1 (suc1 (app1 v11 v01)))))
      (lam1 v01))

def mul1 : ∀ {Γ}, Tm1 Γ (arr1 nat1 (arr1 nat1 nat1))
 := lam1 (rec1 v01
     (lam1 (lam1 (lam1 (app1 (app1 add1 (app1 v11 v01)) v01))))
     (lam1 zero1))

def fact1 : ∀ {Γ}, Tm1 Γ (arr1 nat1 nat1)
 := lam1 (rec1 v01 (lam1 (lam1 (app1 (app1 mul1 (suc1 v11)) v01)))
        (suc1 zero1))
def Ty2 : Type 1
 := ∀ (Ty2           : Type)
      (nat top bot  : Ty2)
      (arr prod sum : Ty2 → Ty2 → Ty2)
    , Ty2

def nat2 : Ty2 := λ _ nat2 _ _ _ _ _ => nat2
def top2 : Ty2 := λ _ _ top2 _ _ _ _ => top2
def bot2 : Ty2 := λ _ _ _ bot2 _ _ _ => bot2

def arr2 : Ty2 → Ty2 → Ty2
 := λ A B Ty2 nat2 top2 bot2 arr2 prod sum =>
     arr2 (A Ty2 nat2 top2 bot2 arr2 prod sum) (B Ty2 nat2 top2 bot2 arr2 prod sum)

def prod2 : Ty2 → Ty2 → Ty2
 := λ A B Ty2 nat2 top2 bot2 arr2 prod2 sum =>
     prod2 (A Ty2 nat2 top2 bot2 arr2 prod2 sum) (B Ty2 nat2 top2 bot2 arr2 prod2 sum)

def sum2 : Ty2 → Ty2 → Ty2
 := λ A B Ty2 nat2 top2 bot2 arr2 prod2 sum2 =>
     sum2 (A Ty2 nat2 top2 bot2 arr2 prod2 sum2) (B Ty2 nat2 top2 bot2 arr2 prod2 sum2)

def Con2 : Type 1
 := ∀ (Con2  : Type)
      (nil  : Con2)
      (snoc : Con2 → Ty2 → Con2)
    , Con2

def nil2 : Con2
 := λ Con2 nil2 snoc => nil2

def snoc2 : Con2 → Ty2 → Con2
 := λ Γ A Con2 nil2 snoc2 => snoc2 (Γ Con2 nil2 snoc2) A

def Var2 : Con2 → Ty2 → Type 1
 := λ Γ A =>
   ∀ (Var2 : Con2 → Ty2 → Type)
     (vz  : ∀{Γ A}, Var2 (snoc2 Γ A) A)
     (vs  : ∀{Γ B A}, Var2 Γ A → Var2 (snoc2 Γ B) A)
   , Var2 Γ A

def vz2 : ∀ {Γ A}, Var2 (snoc2 Γ A) A
 := λ Var2 vz2 vs => vz2

def vs2 : ∀ {Γ B A}, Var2 Γ A → Var2 (snoc2 Γ B) A
 := λ x Var2 vz2 vs2 => vs2 (x Var2 vz2 vs2)

def Tm2 : Con2 → Ty2 → Type 1
 := λ Γ A =>
   ∀ (Tm2  : Con2 → Ty2 → Type)
     (var : ∀ {Γ A}, Var2 Γ A → Tm2 Γ A)
     (lam : ∀ {Γ A B}, (Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B)))
     (app   : ∀ {Γ A B}   , Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B)
     (tt    : ∀ {Γ}       , Tm2 Γ top2)
     (pair  : ∀ {Γ A B}   , Tm2 Γ A → Tm2 Γ B → Tm2 Γ (prod2 A B))
     (fst   : ∀ {Γ A B}   , Tm2 Γ (prod2 A B) → Tm2 Γ A)
     (snd   : ∀ {Γ A B}   , Tm2 Γ (prod2 A B) → Tm2 Γ B)
     (left  : ∀ {Γ A B}   , Tm2 Γ A → Tm2 Γ (sum2 A B))
     (right : ∀ {Γ A B}   , Tm2 Γ B → Tm2 Γ (sum2 A B))
     (case  : ∀ {Γ A B C} , Tm2 Γ (sum2 A B) → Tm2 Γ (arr2 A C) → Tm2 Γ (arr2 B C) → Tm2 Γ C)
     (zero  : ∀ {Γ}       , Tm2 Γ nat2)
     (suc   : ∀ {Γ}       , Tm2 Γ nat2 → Tm2 Γ nat2)
     (rec   : ∀ {Γ A}     , Tm2 Γ nat2 → Tm2 Γ (arr2 nat2 (arr2 A A)) → Tm2 Γ A → Tm2 Γ A)
   , Tm2 Γ A

def var2 : ∀ {Γ A}, Var2 Γ A → Tm2 Γ A
 := λ x Tm2 var2 lam app tt pair fst snd left right case zero suc rec =>
     var2 x

def lam2 : ∀ {Γ A B} , Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B)
 := λ t Tm2 var2 lam2 app tt pair fst snd left right case zero suc rec =>
     lam2 (t Tm2 var2 lam2 app tt pair fst snd left right case zero suc rec)

def app2 : ∀ {Γ A B} , Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B
 := λ t u Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec =>
     app2 (t Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec)
         (u Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec)

def tt2 : ∀ {Γ} , Tm2 Γ top2
 := λ Tm2 var2 lam2 app2 tt2 pair fst snd left right case zero suc rec => tt2

def pair2 : ∀ {Γ A B} , Tm2 Γ A → Tm2 Γ B → Tm2 Γ (prod2 A B)
 := λ t u Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec =>
     pair2 (t Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec)
          (u Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec)

def fst2 : ∀ {Γ A B} , Tm2 Γ (prod2 A B) → Tm2 Γ A
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd left right case zero suc rec =>
     fst2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd left right case zero suc rec)

def snd2 : ∀ {Γ A B} , Tm2 Γ (prod2 A B) → Tm2 Γ B
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left right case zero suc rec =>
     snd2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left right case zero suc rec)

def left2 : ∀ {Γ A B} , Tm2 Γ A → Tm2 Γ (sum2 A B)
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right case zero suc rec =>
     left2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right case zero suc rec)

def right2 : ∀ {Γ A B} , Tm2 Γ B → Tm2 Γ (sum2 A B)
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case zero suc rec =>
     right2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case zero suc rec)

def case2 : ∀ {Γ A B C} , Tm2 Γ (sum2 A B) → Tm2 Γ (arr2 A C) → Tm2 Γ (arr2 B C) → Tm2 Γ C
 := λ t u v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec =>
     case2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)
          (u Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)
          (v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)

def zero2  : ∀ {Γ} , Tm2 Γ nat2
 := λ Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc rec => zero2

def suc2 : ∀ {Γ} , Tm2 Γ nat2 → Tm2 Γ nat2
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec =>
   suc2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec)

def rec2 : ∀ {Γ A} , Tm2 Γ nat2 → Tm2 Γ (arr2 nat2 (arr2 A A)) → Tm2 Γ A → Tm2 Γ A
 := λ t u v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2 =>
     rec2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)
         (u Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)
         (v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)

def v02 : ∀ {Γ A}, Tm2 (snoc2 Γ A) A
 := var2 vz2

def v12 : ∀ {Γ A B}, Tm2 (snoc2 (snoc2 Γ A) B) A
 := var2 (vs2 vz2)

def v22 : ∀ {Γ A B C}, Tm2 (snoc2 (snoc2 (snoc2 Γ A) B) C) A
 := var2 (vs2 (vs2 vz2))

def v32 : ∀ {Γ A B C D}, Tm2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) A
 := var2 (vs2 (vs2 (vs2 vz2)))

def tbool2 : Ty2
 := sum2 top2 top2

def ttrue2 : ∀ {Γ}, Tm2 Γ tbool2
 := left2 tt2

def tfalse2 : ∀ {Γ}, Tm2 Γ tbool2
 := right2 tt2

def ifthenelse2 : ∀ {Γ A}, Tm2 Γ (arr2 tbool2 (arr2 A (arr2 A A)))
 := lam2 (lam2 (lam2 (case2 v22 (lam2 v22) (lam2 v12))))

def times42 : ∀ {Γ A}, Tm2 Γ (arr2 (arr2 A A) (arr2 A A))
  := lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02)))))

def add2 : ∀ {Γ}, Tm2 Γ (arr2 nat2 (arr2 nat2 nat2))
 := lam2 (rec2 v02
      (lam2 (lam2 (lam2 (suc2 (app2 v12 v02)))))
      (lam2 v02))

def mul2 : ∀ {Γ}, Tm2 Γ (arr2 nat2 (arr2 nat2 nat2))
 := lam2 (rec2 v02
     (lam2 (lam2 (lam2 (app2 (app2 add2 (app2 v12 v02)) v02))))
     (lam2 zero2))

def fact2 : ∀ {Γ}, Tm2 Γ (arr2 nat2 nat2)
 := lam2 (rec2 v02 (lam2 (lam2 (app2 (app2 mul2 (suc2 v12)) v02)))
        (suc2 zero2))
def Ty3 : Type 1
 := ∀ (Ty3           : Type)
      (nat top bot  : Ty3)
      (arr prod sum : Ty3 → Ty3 → Ty3)
    , Ty3

def nat3 : Ty3 := λ _ nat3 _ _ _ _ _ => nat3
def top3 : Ty3 := λ _ _ top3 _ _ _ _ => top3
def bot3 : Ty3 := λ _ _ _ bot3 _ _ _ => bot3

def arr3 : Ty3 → Ty3 → Ty3
 := λ A B Ty3 nat3 top3 bot3 arr3 prod sum =>
     arr3 (A Ty3 nat3 top3 bot3 arr3 prod sum) (B Ty3 nat3 top3 bot3 arr3 prod sum)

def prod3 : Ty3 → Ty3 → Ty3
 := λ A B Ty3 nat3 top3 bot3 arr3 prod3 sum =>
     prod3 (A Ty3 nat3 top3 bot3 arr3 prod3 sum) (B Ty3 nat3 top3 bot3 arr3 prod3 sum)

def sum3 : Ty3 → Ty3 → Ty3
 := λ A B Ty3 nat3 top3 bot3 arr3 prod3 sum3 =>
     sum3 (A Ty3 nat3 top3 bot3 arr3 prod3 sum3) (B Ty3 nat3 top3 bot3 arr3 prod3 sum3)

def Con3 : Type 1
 := ∀ (Con3  : Type)
      (nil  : Con3)
      (snoc : Con3 → Ty3 → Con3)
    , Con3

def nil3 : Con3
 := λ Con3 nil3 snoc => nil3

def snoc3 : Con3 → Ty3 → Con3
 := λ Γ A Con3 nil3 snoc3 => snoc3 (Γ Con3 nil3 snoc3) A

def Var3 : Con3 → Ty3 → Type 1
 := λ Γ A =>
   ∀ (Var3 : Con3 → Ty3 → Type)
     (vz  : ∀{Γ A}, Var3 (snoc3 Γ A) A)
     (vs  : ∀{Γ B A}, Var3 Γ A → Var3 (snoc3 Γ B) A)
   , Var3 Γ A

def vz3 : ∀ {Γ A}, Var3 (snoc3 Γ A) A
 := λ Var3 vz3 vs => vz3

def vs3 : ∀ {Γ B A}, Var3 Γ A → Var3 (snoc3 Γ B) A
 := λ x Var3 vz3 vs3 => vs3 (x Var3 vz3 vs3)

def Tm3 : Con3 → Ty3 → Type 1
 := λ Γ A =>
   ∀ (Tm3  : Con3 → Ty3 → Type)
     (var : ∀ {Γ A}, Var3 Γ A → Tm3 Γ A)
     (lam : ∀ {Γ A B}, (Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B)))
     (app   : ∀ {Γ A B}   , Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B)
     (tt    : ∀ {Γ}       , Tm3 Γ top3)
     (pair  : ∀ {Γ A B}   , Tm3 Γ A → Tm3 Γ B → Tm3 Γ (prod3 A B))
     (fst   : ∀ {Γ A B}   , Tm3 Γ (prod3 A B) → Tm3 Γ A)
     (snd   : ∀ {Γ A B}   , Tm3 Γ (prod3 A B) → Tm3 Γ B)
     (left  : ∀ {Γ A B}   , Tm3 Γ A → Tm3 Γ (sum3 A B))
     (right : ∀ {Γ A B}   , Tm3 Γ B → Tm3 Γ (sum3 A B))
     (case  : ∀ {Γ A B C} , Tm3 Γ (sum3 A B) → Tm3 Γ (arr3 A C) → Tm3 Γ (arr3 B C) → Tm3 Γ C)
     (zero  : ∀ {Γ}       , Tm3 Γ nat3)
     (suc   : ∀ {Γ}       , Tm3 Γ nat3 → Tm3 Γ nat3)
     (rec   : ∀ {Γ A}     , Tm3 Γ nat3 → Tm3 Γ (arr3 nat3 (arr3 A A)) → Tm3 Γ A → Tm3 Γ A)
   , Tm3 Γ A

def var3 : ∀ {Γ A}, Var3 Γ A → Tm3 Γ A
 := λ x Tm3 var3 lam app tt pair fst snd left right case zero suc rec =>
     var3 x

def lam3 : ∀ {Γ A B} , Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B)
 := λ t Tm3 var3 lam3 app tt pair fst snd left right case zero suc rec =>
     lam3 (t Tm3 var3 lam3 app tt pair fst snd left right case zero suc rec)

def app3 : ∀ {Γ A B} , Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B
 := λ t u Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec =>
     app3 (t Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec)
         (u Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec)

def tt3 : ∀ {Γ} , Tm3 Γ top3
 := λ Tm3 var3 lam3 app3 tt3 pair fst snd left right case zero suc rec => tt3

def pair3 : ∀ {Γ A B} , Tm3 Γ A → Tm3 Γ B → Tm3 Γ (prod3 A B)
 := λ t u Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec =>
     pair3 (t Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec)
          (u Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec)

def fst3 : ∀ {Γ A B} , Tm3 Γ (prod3 A B) → Tm3 Γ A
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd left right case zero suc rec =>
     fst3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd left right case zero suc rec)

def snd3 : ∀ {Γ A B} , Tm3 Γ (prod3 A B) → Tm3 Γ B
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left right case zero suc rec =>
     snd3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left right case zero suc rec)

def left3 : ∀ {Γ A B} , Tm3 Γ A → Tm3 Γ (sum3 A B)
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right case zero suc rec =>
     left3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right case zero suc rec)

def right3 : ∀ {Γ A B} , Tm3 Γ B → Tm3 Γ (sum3 A B)
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case zero suc rec =>
     right3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case zero suc rec)

def case3 : ∀ {Γ A B C} , Tm3 Γ (sum3 A B) → Tm3 Γ (arr3 A C) → Tm3 Γ (arr3 B C) → Tm3 Γ C
 := λ t u v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec =>
     case3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)
          (u Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)
          (v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)

def zero3  : ∀ {Γ} , Tm3 Γ nat3
 := λ Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc rec => zero3

def suc3 : ∀ {Γ} , Tm3 Γ nat3 → Tm3 Γ nat3
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec =>
   suc3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec)

def rec3 : ∀ {Γ A} , Tm3 Γ nat3 → Tm3 Γ (arr3 nat3 (arr3 A A)) → Tm3 Γ A → Tm3 Γ A
 := λ t u v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3 =>
     rec3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)
         (u Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)
         (v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)

def v03 : ∀ {Γ A}, Tm3 (snoc3 Γ A) A
 := var3 vz3

def v13 : ∀ {Γ A B}, Tm3 (snoc3 (snoc3 Γ A) B) A
 := var3 (vs3 vz3)

def v23 : ∀ {Γ A B C}, Tm3 (snoc3 (snoc3 (snoc3 Γ A) B) C) A
 := var3 (vs3 (vs3 vz3))

def v33 : ∀ {Γ A B C D}, Tm3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) A
 := var3 (vs3 (vs3 (vs3 vz3)))

def tbool3 : Ty3
 := sum3 top3 top3

def ttrue3 : ∀ {Γ}, Tm3 Γ tbool3
 := left3 tt3

def tfalse3 : ∀ {Γ}, Tm3 Γ tbool3
 := right3 tt3

def ifthenelse3 : ∀ {Γ A}, Tm3 Γ (arr3 tbool3 (arr3 A (arr3 A A)))
 := lam3 (lam3 (lam3 (case3 v23 (lam3 v23) (lam3 v13))))

def times43 : ∀ {Γ A}, Tm3 Γ (arr3 (arr3 A A) (arr3 A A))
  := lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03)))))

def add3 : ∀ {Γ}, Tm3 Γ (arr3 nat3 (arr3 nat3 nat3))
 := lam3 (rec3 v03
      (lam3 (lam3 (lam3 (suc3 (app3 v13 v03)))))
      (lam3 v03))

def mul3 : ∀ {Γ}, Tm3 Γ (arr3 nat3 (arr3 nat3 nat3))
 := lam3 (rec3 v03
     (lam3 (lam3 (lam3 (app3 (app3 add3 (app3 v13 v03)) v03))))
     (lam3 zero3))

def fact3 : ∀ {Γ}, Tm3 Γ (arr3 nat3 nat3)
 := lam3 (rec3 v03 (lam3 (lam3 (app3 (app3 mul3 (suc3 v13)) v03)))
        (suc3 zero3))
def Ty4 : Type 1
 := ∀ (Ty4           : Type)
      (nat top bot  : Ty4)
      (arr prod sum : Ty4 → Ty4 → Ty4)
    , Ty4

def nat4 : Ty4 := λ _ nat4 _ _ _ _ _ => nat4
def top4 : Ty4 := λ _ _ top4 _ _ _ _ => top4
def bot4 : Ty4 := λ _ _ _ bot4 _ _ _ => bot4

def arr4 : Ty4 → Ty4 → Ty4
 := λ A B Ty4 nat4 top4 bot4 arr4 prod sum =>
     arr4 (A Ty4 nat4 top4 bot4 arr4 prod sum) (B Ty4 nat4 top4 bot4 arr4 prod sum)

def prod4 : Ty4 → Ty4 → Ty4
 := λ A B Ty4 nat4 top4 bot4 arr4 prod4 sum =>
     prod4 (A Ty4 nat4 top4 bot4 arr4 prod4 sum) (B Ty4 nat4 top4 bot4 arr4 prod4 sum)

def sum4 : Ty4 → Ty4 → Ty4
 := λ A B Ty4 nat4 top4 bot4 arr4 prod4 sum4 =>
     sum4 (A Ty4 nat4 top4 bot4 arr4 prod4 sum4) (B Ty4 nat4 top4 bot4 arr4 prod4 sum4)

def Con4 : Type 1
 := ∀ (Con4  : Type)
      (nil  : Con4)
      (snoc : Con4 → Ty4 → Con4)
    , Con4

def nil4 : Con4
 := λ Con4 nil4 snoc => nil4

def snoc4 : Con4 → Ty4 → Con4
 := λ Γ A Con4 nil4 snoc4 => snoc4 (Γ Con4 nil4 snoc4) A

def Var4 : Con4 → Ty4 → Type 1
 := λ Γ A =>
   ∀ (Var4 : Con4 → Ty4 → Type)
     (vz  : ∀{Γ A}, Var4 (snoc4 Γ A) A)
     (vs  : ∀{Γ B A}, Var4 Γ A → Var4 (snoc4 Γ B) A)
   , Var4 Γ A

def vz4 : ∀ {Γ A}, Var4 (snoc4 Γ A) A
 := λ Var4 vz4 vs => vz4

def vs4 : ∀ {Γ B A}, Var4 Γ A → Var4 (snoc4 Γ B) A
 := λ x Var4 vz4 vs4 => vs4 (x Var4 vz4 vs4)

def Tm4 : Con4 → Ty4 → Type 1
 := λ Γ A =>
   ∀ (Tm4  : Con4 → Ty4 → Type)
     (var : ∀ {Γ A}, Var4 Γ A → Tm4 Γ A)
     (lam : ∀ {Γ A B}, (Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B)))
     (app   : ∀ {Γ A B}   , Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B)
     (tt    : ∀ {Γ}       , Tm4 Γ top4)
     (pair  : ∀ {Γ A B}   , Tm4 Γ A → Tm4 Γ B → Tm4 Γ (prod4 A B))
     (fst   : ∀ {Γ A B}   , Tm4 Γ (prod4 A B) → Tm4 Γ A)
     (snd   : ∀ {Γ A B}   , Tm4 Γ (prod4 A B) → Tm4 Γ B)
     (left  : ∀ {Γ A B}   , Tm4 Γ A → Tm4 Γ (sum4 A B))
     (right : ∀ {Γ A B}   , Tm4 Γ B → Tm4 Γ (sum4 A B))
     (case  : ∀ {Γ A B C} , Tm4 Γ (sum4 A B) → Tm4 Γ (arr4 A C) → Tm4 Γ (arr4 B C) → Tm4 Γ C)
     (zero  : ∀ {Γ}       , Tm4 Γ nat4)
     (suc   : ∀ {Γ}       , Tm4 Γ nat4 → Tm4 Γ nat4)
     (rec   : ∀ {Γ A}     , Tm4 Γ nat4 → Tm4 Γ (arr4 nat4 (arr4 A A)) → Tm4 Γ A → Tm4 Γ A)
   , Tm4 Γ A

def var4 : ∀ {Γ A}, Var4 Γ A → Tm4 Γ A
 := λ x Tm4 var4 lam app tt pair fst snd left right case zero suc rec =>
     var4 x

def lam4 : ∀ {Γ A B} , Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B)
 := λ t Tm4 var4 lam4 app tt pair fst snd left right case zero suc rec =>
     lam4 (t Tm4 var4 lam4 app tt pair fst snd left right case zero suc rec)

def app4 : ∀ {Γ A B} , Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B
 := λ t u Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec =>
     app4 (t Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec)
         (u Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec)

def tt4 : ∀ {Γ} , Tm4 Γ top4
 := λ Tm4 var4 lam4 app4 tt4 pair fst snd left right case zero suc rec => tt4

def pair4 : ∀ {Γ A B} , Tm4 Γ A → Tm4 Γ B → Tm4 Γ (prod4 A B)
 := λ t u Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec =>
     pair4 (t Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec)
          (u Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec)

def fst4 : ∀ {Γ A B} , Tm4 Γ (prod4 A B) → Tm4 Γ A
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd left right case zero suc rec =>
     fst4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd left right case zero suc rec)

def snd4 : ∀ {Γ A B} , Tm4 Γ (prod4 A B) → Tm4 Γ B
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left right case zero suc rec =>
     snd4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left right case zero suc rec)

def left4 : ∀ {Γ A B} , Tm4 Γ A → Tm4 Γ (sum4 A B)
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right case zero suc rec =>
     left4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right case zero suc rec)

def right4 : ∀ {Γ A B} , Tm4 Γ B → Tm4 Γ (sum4 A B)
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case zero suc rec =>
     right4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case zero suc rec)

def case4 : ∀ {Γ A B C} , Tm4 Γ (sum4 A B) → Tm4 Γ (arr4 A C) → Tm4 Γ (arr4 B C) → Tm4 Γ C
 := λ t u v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec =>
     case4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)
          (u Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)
          (v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)

def zero4  : ∀ {Γ} , Tm4 Γ nat4
 := λ Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc rec => zero4

def suc4 : ∀ {Γ} , Tm4 Γ nat4 → Tm4 Γ nat4
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec =>
   suc4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec)

def rec4 : ∀ {Γ A} , Tm4 Γ nat4 → Tm4 Γ (arr4 nat4 (arr4 A A)) → Tm4 Γ A → Tm4 Γ A
 := λ t u v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4 =>
     rec4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)
         (u Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)
         (v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)

def v04 : ∀ {Γ A}, Tm4 (snoc4 Γ A) A
 := var4 vz4

def v14 : ∀ {Γ A B}, Tm4 (snoc4 (snoc4 Γ A) B) A
 := var4 (vs4 vz4)

def v24 : ∀ {Γ A B C}, Tm4 (snoc4 (snoc4 (snoc4 Γ A) B) C) A
 := var4 (vs4 (vs4 vz4))

def v34 : ∀ {Γ A B C D}, Tm4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) A
 := var4 (vs4 (vs4 (vs4 vz4)))

def tbool4 : Ty4
 := sum4 top4 top4

def ttrue4 : ∀ {Γ}, Tm4 Γ tbool4
 := left4 tt4

def tfalse4 : ∀ {Γ}, Tm4 Γ tbool4
 := right4 tt4

def ifthenelse4 : ∀ {Γ A}, Tm4 Γ (arr4 tbool4 (arr4 A (arr4 A A)))
 := lam4 (lam4 (lam4 (case4 v24 (lam4 v24) (lam4 v14))))

def times44 : ∀ {Γ A}, Tm4 Γ (arr4 (arr4 A A) (arr4 A A))
  := lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04)))))

def add4 : ∀ {Γ}, Tm4 Γ (arr4 nat4 (arr4 nat4 nat4))
 := lam4 (rec4 v04
      (lam4 (lam4 (lam4 (suc4 (app4 v14 v04)))))
      (lam4 v04))

def mul4 : ∀ {Γ}, Tm4 Γ (arr4 nat4 (arr4 nat4 nat4))
 := lam4 (rec4 v04
     (lam4 (lam4 (lam4 (app4 (app4 add4 (app4 v14 v04)) v04))))
     (lam4 zero4))

def fact4 : ∀ {Γ}, Tm4 Γ (arr4 nat4 nat4)
 := lam4 (rec4 v04 (lam4 (lam4 (app4 (app4 mul4 (suc4 v14)) v04)))
        (suc4 zero4))
def Ty5 : Type 1
 := ∀ (Ty5           : Type)
      (nat top bot  : Ty5)
      (arr prod sum : Ty5 → Ty5 → Ty5)
    , Ty5

def nat5 : Ty5 := λ _ nat5 _ _ _ _ _ => nat5
def top5 : Ty5 := λ _ _ top5 _ _ _ _ => top5
def bot5 : Ty5 := λ _ _ _ bot5 _ _ _ => bot5

def arr5 : Ty5 → Ty5 → Ty5
 := λ A B Ty5 nat5 top5 bot5 arr5 prod sum =>
     arr5 (A Ty5 nat5 top5 bot5 arr5 prod sum) (B Ty5 nat5 top5 bot5 arr5 prod sum)

def prod5 : Ty5 → Ty5 → Ty5
 := λ A B Ty5 nat5 top5 bot5 arr5 prod5 sum =>
     prod5 (A Ty5 nat5 top5 bot5 arr5 prod5 sum) (B Ty5 nat5 top5 bot5 arr5 prod5 sum)

def sum5 : Ty5 → Ty5 → Ty5
 := λ A B Ty5 nat5 top5 bot5 arr5 prod5 sum5 =>
     sum5 (A Ty5 nat5 top5 bot5 arr5 prod5 sum5) (B Ty5 nat5 top5 bot5 arr5 prod5 sum5)

def Con5 : Type 1
 := ∀ (Con5  : Type)
      (nil  : Con5)
      (snoc : Con5 → Ty5 → Con5)
    , Con5

def nil5 : Con5
 := λ Con5 nil5 snoc => nil5

def snoc5 : Con5 → Ty5 → Con5
 := λ Γ A Con5 nil5 snoc5 => snoc5 (Γ Con5 nil5 snoc5) A

def Var5 : Con5 → Ty5 → Type 1
 := λ Γ A =>
   ∀ (Var5 : Con5 → Ty5 → Type)
     (vz  : ∀{Γ A}, Var5 (snoc5 Γ A) A)
     (vs  : ∀{Γ B A}, Var5 Γ A → Var5 (snoc5 Γ B) A)
   , Var5 Γ A

def vz5 : ∀ {Γ A}, Var5 (snoc5 Γ A) A
 := λ Var5 vz5 vs => vz5

def vs5 : ∀ {Γ B A}, Var5 Γ A → Var5 (snoc5 Γ B) A
 := λ x Var5 vz5 vs5 => vs5 (x Var5 vz5 vs5)

def Tm5 : Con5 → Ty5 → Type 1
 := λ Γ A =>
   ∀ (Tm5  : Con5 → Ty5 → Type)
     (var : ∀ {Γ A}, Var5 Γ A → Tm5 Γ A)
     (lam : ∀ {Γ A B}, (Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B)))
     (app   : ∀ {Γ A B}   , Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B)
     (tt    : ∀ {Γ}       , Tm5 Γ top5)
     (pair  : ∀ {Γ A B}   , Tm5 Γ A → Tm5 Γ B → Tm5 Γ (prod5 A B))
     (fst   : ∀ {Γ A B}   , Tm5 Γ (prod5 A B) → Tm5 Γ A)
     (snd   : ∀ {Γ A B}   , Tm5 Γ (prod5 A B) → Tm5 Γ B)
     (left  : ∀ {Γ A B}   , Tm5 Γ A → Tm5 Γ (sum5 A B))
     (right : ∀ {Γ A B}   , Tm5 Γ B → Tm5 Γ (sum5 A B))
     (case  : ∀ {Γ A B C} , Tm5 Γ (sum5 A B) → Tm5 Γ (arr5 A C) → Tm5 Γ (arr5 B C) → Tm5 Γ C)
     (zero  : ∀ {Γ}       , Tm5 Γ nat5)
     (suc   : ∀ {Γ}       , Tm5 Γ nat5 → Tm5 Γ nat5)
     (rec   : ∀ {Γ A}     , Tm5 Γ nat5 → Tm5 Γ (arr5 nat5 (arr5 A A)) → Tm5 Γ A → Tm5 Γ A)
   , Tm5 Γ A

def var5 : ∀ {Γ A}, Var5 Γ A → Tm5 Γ A
 := λ x Tm5 var5 lam app tt pair fst snd left right case zero suc rec =>
     var5 x

def lam5 : ∀ {Γ A B} , Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B)
 := λ t Tm5 var5 lam5 app tt pair fst snd left right case zero suc rec =>
     lam5 (t Tm5 var5 lam5 app tt pair fst snd left right case zero suc rec)

def app5 : ∀ {Γ A B} , Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B
 := λ t u Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec =>
     app5 (t Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec)
         (u Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec)

def tt5 : ∀ {Γ} , Tm5 Γ top5
 := λ Tm5 var5 lam5 app5 tt5 pair fst snd left right case zero suc rec => tt5

def pair5 : ∀ {Γ A B} , Tm5 Γ A → Tm5 Γ B → Tm5 Γ (prod5 A B)
 := λ t u Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec =>
     pair5 (t Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec)
          (u Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec)

def fst5 : ∀ {Γ A B} , Tm5 Γ (prod5 A B) → Tm5 Γ A
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd left right case zero suc rec =>
     fst5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd left right case zero suc rec)

def snd5 : ∀ {Γ A B} , Tm5 Γ (prod5 A B) → Tm5 Γ B
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left right case zero suc rec =>
     snd5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left right case zero suc rec)

def left5 : ∀ {Γ A B} , Tm5 Γ A → Tm5 Γ (sum5 A B)
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right case zero suc rec =>
     left5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right case zero suc rec)

def right5 : ∀ {Γ A B} , Tm5 Γ B → Tm5 Γ (sum5 A B)
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case zero suc rec =>
     right5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case zero suc rec)

def case5 : ∀ {Γ A B C} , Tm5 Γ (sum5 A B) → Tm5 Γ (arr5 A C) → Tm5 Γ (arr5 B C) → Tm5 Γ C
 := λ t u v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec =>
     case5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)
          (u Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)
          (v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)

def zero5  : ∀ {Γ} , Tm5 Γ nat5
 := λ Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc rec => zero5

def suc5 : ∀ {Γ} , Tm5 Γ nat5 → Tm5 Γ nat5
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec =>
   suc5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec)

def rec5 : ∀ {Γ A} , Tm5 Γ nat5 → Tm5 Γ (arr5 nat5 (arr5 A A)) → Tm5 Γ A → Tm5 Γ A
 := λ t u v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5 =>
     rec5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)
         (u Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)
         (v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)

def v05 : ∀ {Γ A}, Tm5 (snoc5 Γ A) A
 := var5 vz5

def v15 : ∀ {Γ A B}, Tm5 (snoc5 (snoc5 Γ A) B) A
 := var5 (vs5 vz5)

def v25 : ∀ {Γ A B C}, Tm5 (snoc5 (snoc5 (snoc5 Γ A) B) C) A
 := var5 (vs5 (vs5 vz5))

def v35 : ∀ {Γ A B C D}, Tm5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) A
 := var5 (vs5 (vs5 (vs5 vz5)))

def tbool5 : Ty5
 := sum5 top5 top5

def ttrue5 : ∀ {Γ}, Tm5 Γ tbool5
 := left5 tt5

def tfalse5 : ∀ {Γ}, Tm5 Γ tbool5
 := right5 tt5

def ifthenelse5 : ∀ {Γ A}, Tm5 Γ (arr5 tbool5 (arr5 A (arr5 A A)))
 := lam5 (lam5 (lam5 (case5 v25 (lam5 v25) (lam5 v15))))

def times45 : ∀ {Γ A}, Tm5 Γ (arr5 (arr5 A A) (arr5 A A))
  := lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05)))))

def add5 : ∀ {Γ}, Tm5 Γ (arr5 nat5 (arr5 nat5 nat5))
 := lam5 (rec5 v05
      (lam5 (lam5 (lam5 (suc5 (app5 v15 v05)))))
      (lam5 v05))

def mul5 : ∀ {Γ}, Tm5 Γ (arr5 nat5 (arr5 nat5 nat5))
 := lam5 (rec5 v05
     (lam5 (lam5 (lam5 (app5 (app5 add5 (app5 v15 v05)) v05))))
     (lam5 zero5))

def fact5 : ∀ {Γ}, Tm5 Γ (arr5 nat5 nat5)
 := lam5 (rec5 v05 (lam5 (lam5 (app5 (app5 mul5 (suc5 v15)) v05)))
        (suc5 zero5))
def Ty6 : Type 1
 := ∀ (Ty6           : Type)
      (nat top bot  : Ty6)
      (arr prod sum : Ty6 → Ty6 → Ty6)
    , Ty6

def nat6 : Ty6 := λ _ nat6 _ _ _ _ _ => nat6
def top6 : Ty6 := λ _ _ top6 _ _ _ _ => top6
def bot6 : Ty6 := λ _ _ _ bot6 _ _ _ => bot6

def arr6 : Ty6 → Ty6 → Ty6
 := λ A B Ty6 nat6 top6 bot6 arr6 prod sum =>
     arr6 (A Ty6 nat6 top6 bot6 arr6 prod sum) (B Ty6 nat6 top6 bot6 arr6 prod sum)

def prod6 : Ty6 → Ty6 → Ty6
 := λ A B Ty6 nat6 top6 bot6 arr6 prod6 sum =>
     prod6 (A Ty6 nat6 top6 bot6 arr6 prod6 sum) (B Ty6 nat6 top6 bot6 arr6 prod6 sum)

def sum6 : Ty6 → Ty6 → Ty6
 := λ A B Ty6 nat6 top6 bot6 arr6 prod6 sum6 =>
     sum6 (A Ty6 nat6 top6 bot6 arr6 prod6 sum6) (B Ty6 nat6 top6 bot6 arr6 prod6 sum6)

def Con6 : Type 1
 := ∀ (Con6  : Type)
      (nil  : Con6)
      (snoc : Con6 → Ty6 → Con6)
    , Con6

def nil6 : Con6
 := λ Con6 nil6 snoc => nil6

def snoc6 : Con6 → Ty6 → Con6
 := λ Γ A Con6 nil6 snoc6 => snoc6 (Γ Con6 nil6 snoc6) A

def Var6 : Con6 → Ty6 → Type 1
 := λ Γ A =>
   ∀ (Var6 : Con6 → Ty6 → Type)
     (vz  : ∀{Γ A}, Var6 (snoc6 Γ A) A)
     (vs  : ∀{Γ B A}, Var6 Γ A → Var6 (snoc6 Γ B) A)
   , Var6 Γ A

def vz6 : ∀ {Γ A}, Var6 (snoc6 Γ A) A
 := λ Var6 vz6 vs => vz6

def vs6 : ∀ {Γ B A}, Var6 Γ A → Var6 (snoc6 Γ B) A
 := λ x Var6 vz6 vs6 => vs6 (x Var6 vz6 vs6)

def Tm6 : Con6 → Ty6 → Type 1
 := λ Γ A =>
   ∀ (Tm6  : Con6 → Ty6 → Type)
     (var : ∀ {Γ A}, Var6 Γ A → Tm6 Γ A)
     (lam : ∀ {Γ A B}, (Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B)))
     (app   : ∀ {Γ A B}   , Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B)
     (tt    : ∀ {Γ}       , Tm6 Γ top6)
     (pair  : ∀ {Γ A B}   , Tm6 Γ A → Tm6 Γ B → Tm6 Γ (prod6 A B))
     (fst   : ∀ {Γ A B}   , Tm6 Γ (prod6 A B) → Tm6 Γ A)
     (snd   : ∀ {Γ A B}   , Tm6 Γ (prod6 A B) → Tm6 Γ B)
     (left  : ∀ {Γ A B}   , Tm6 Γ A → Tm6 Γ (sum6 A B))
     (right : ∀ {Γ A B}   , Tm6 Γ B → Tm6 Γ (sum6 A B))
     (case  : ∀ {Γ A B C} , Tm6 Γ (sum6 A B) → Tm6 Γ (arr6 A C) → Tm6 Γ (arr6 B C) → Tm6 Γ C)
     (zero  : ∀ {Γ}       , Tm6 Γ nat6)
     (suc   : ∀ {Γ}       , Tm6 Γ nat6 → Tm6 Γ nat6)
     (rec   : ∀ {Γ A}     , Tm6 Γ nat6 → Tm6 Γ (arr6 nat6 (arr6 A A)) → Tm6 Γ A → Tm6 Γ A)
   , Tm6 Γ A

def var6 : ∀ {Γ A}, Var6 Γ A → Tm6 Γ A
 := λ x Tm6 var6 lam app tt pair fst snd left right case zero suc rec =>
     var6 x

def lam6 : ∀ {Γ A B} , Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B)
 := λ t Tm6 var6 lam6 app tt pair fst snd left right case zero suc rec =>
     lam6 (t Tm6 var6 lam6 app tt pair fst snd left right case zero suc rec)

def app6 : ∀ {Γ A B} , Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B
 := λ t u Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec =>
     app6 (t Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec)
         (u Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec)

def tt6 : ∀ {Γ} , Tm6 Γ top6
 := λ Tm6 var6 lam6 app6 tt6 pair fst snd left right case zero suc rec => tt6

def pair6 : ∀ {Γ A B} , Tm6 Γ A → Tm6 Γ B → Tm6 Γ (prod6 A B)
 := λ t u Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec =>
     pair6 (t Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec)
          (u Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec)

def fst6 : ∀ {Γ A B} , Tm6 Γ (prod6 A B) → Tm6 Γ A
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd left right case zero suc rec =>
     fst6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd left right case zero suc rec)

def snd6 : ∀ {Γ A B} , Tm6 Γ (prod6 A B) → Tm6 Γ B
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left right case zero suc rec =>
     snd6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left right case zero suc rec)

def left6 : ∀ {Γ A B} , Tm6 Γ A → Tm6 Γ (sum6 A B)
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right case zero suc rec =>
     left6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right case zero suc rec)

def right6 : ∀ {Γ A B} , Tm6 Γ B → Tm6 Γ (sum6 A B)
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case zero suc rec =>
     right6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case zero suc rec)

def case6 : ∀ {Γ A B C} , Tm6 Γ (sum6 A B) → Tm6 Γ (arr6 A C) → Tm6 Γ (arr6 B C) → Tm6 Γ C
 := λ t u v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec =>
     case6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)
          (u Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)
          (v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)

def zero6  : ∀ {Γ} , Tm6 Γ nat6
 := λ Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc rec => zero6

def suc6 : ∀ {Γ} , Tm6 Γ nat6 → Tm6 Γ nat6
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec =>
   suc6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec)

def rec6 : ∀ {Γ A} , Tm6 Γ nat6 → Tm6 Γ (arr6 nat6 (arr6 A A)) → Tm6 Γ A → Tm6 Γ A
 := λ t u v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6 =>
     rec6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)
         (u Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)
         (v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)

def v06 : ∀ {Γ A}, Tm6 (snoc6 Γ A) A
 := var6 vz6

def v16 : ∀ {Γ A B}, Tm6 (snoc6 (snoc6 Γ A) B) A
 := var6 (vs6 vz6)

def v26 : ∀ {Γ A B C}, Tm6 (snoc6 (snoc6 (snoc6 Γ A) B) C) A
 := var6 (vs6 (vs6 vz6))

def v36 : ∀ {Γ A B C D}, Tm6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) A
 := var6 (vs6 (vs6 (vs6 vz6)))

def tbool6 : Ty6
 := sum6 top6 top6

def ttrue6 : ∀ {Γ}, Tm6 Γ tbool6
 := left6 tt6

def tfalse6 : ∀ {Γ}, Tm6 Γ tbool6
 := right6 tt6

def ifthenelse6 : ∀ {Γ A}, Tm6 Γ (arr6 tbool6 (arr6 A (arr6 A A)))
 := lam6 (lam6 (lam6 (case6 v26 (lam6 v26) (lam6 v16))))

def times46 : ∀ {Γ A}, Tm6 Γ (arr6 (arr6 A A) (arr6 A A))
  := lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06)))))

def add6 : ∀ {Γ}, Tm6 Γ (arr6 nat6 (arr6 nat6 nat6))
 := lam6 (rec6 v06
      (lam6 (lam6 (lam6 (suc6 (app6 v16 v06)))))
      (lam6 v06))

def mul6 : ∀ {Γ}, Tm6 Γ (arr6 nat6 (arr6 nat6 nat6))
 := lam6 (rec6 v06
     (lam6 (lam6 (lam6 (app6 (app6 add6 (app6 v16 v06)) v06))))
     (lam6 zero6))

def fact6 : ∀ {Γ}, Tm6 Γ (arr6 nat6 nat6)
 := lam6 (rec6 v06 (lam6 (lam6 (app6 (app6 mul6 (suc6 v16)) v06)))
        (suc6 zero6))
def Ty7 : Type 1
 := ∀ (Ty7           : Type)
      (nat top bot  : Ty7)
      (arr prod sum : Ty7 → Ty7 → Ty7)
    , Ty7

def nat7 : Ty7 := λ _ nat7 _ _ _ _ _ => nat7
def top7 : Ty7 := λ _ _ top7 _ _ _ _ => top7
def bot7 : Ty7 := λ _ _ _ bot7 _ _ _ => bot7

def arr7 : Ty7 → Ty7 → Ty7
 := λ A B Ty7 nat7 top7 bot7 arr7 prod sum =>
     arr7 (A Ty7 nat7 top7 bot7 arr7 prod sum) (B Ty7 nat7 top7 bot7 arr7 prod sum)

def prod7 : Ty7 → Ty7 → Ty7
 := λ A B Ty7 nat7 top7 bot7 arr7 prod7 sum =>
     prod7 (A Ty7 nat7 top7 bot7 arr7 prod7 sum) (B Ty7 nat7 top7 bot7 arr7 prod7 sum)

def sum7 : Ty7 → Ty7 → Ty7
 := λ A B Ty7 nat7 top7 bot7 arr7 prod7 sum7 =>
     sum7 (A Ty7 nat7 top7 bot7 arr7 prod7 sum7) (B Ty7 nat7 top7 bot7 arr7 prod7 sum7)

def Con7 : Type 1
 := ∀ (Con7  : Type)
      (nil  : Con7)
      (snoc : Con7 → Ty7 → Con7)
    , Con7

def nil7 : Con7
 := λ Con7 nil7 snoc => nil7

def snoc7 : Con7 → Ty7 → Con7
 := λ Γ A Con7 nil7 snoc7 => snoc7 (Γ Con7 nil7 snoc7) A

def Var7 : Con7 → Ty7 → Type 1
 := λ Γ A =>
   ∀ (Var7 : Con7 → Ty7 → Type)
     (vz  : ∀{Γ A}, Var7 (snoc7 Γ A) A)
     (vs  : ∀{Γ B A}, Var7 Γ A → Var7 (snoc7 Γ B) A)
   , Var7 Γ A

def vz7 : ∀ {Γ A}, Var7 (snoc7 Γ A) A
 := λ Var7 vz7 vs => vz7

def vs7 : ∀ {Γ B A}, Var7 Γ A → Var7 (snoc7 Γ B) A
 := λ x Var7 vz7 vs7 => vs7 (x Var7 vz7 vs7)

def Tm7 : Con7 → Ty7 → Type 1
 := λ Γ A =>
   ∀ (Tm7  : Con7 → Ty7 → Type)
     (var : ∀ {Γ A}, Var7 Γ A → Tm7 Γ A)
     (lam : ∀ {Γ A B}, (Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B)))
     (app   : ∀ {Γ A B}   , Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B)
     (tt    : ∀ {Γ}       , Tm7 Γ top7)
     (pair  : ∀ {Γ A B}   , Tm7 Γ A → Tm7 Γ B → Tm7 Γ (prod7 A B))
     (fst   : ∀ {Γ A B}   , Tm7 Γ (prod7 A B) → Tm7 Γ A)
     (snd   : ∀ {Γ A B}   , Tm7 Γ (prod7 A B) → Tm7 Γ B)
     (left  : ∀ {Γ A B}   , Tm7 Γ A → Tm7 Γ (sum7 A B))
     (right : ∀ {Γ A B}   , Tm7 Γ B → Tm7 Γ (sum7 A B))
     (case  : ∀ {Γ A B C} , Tm7 Γ (sum7 A B) → Tm7 Γ (arr7 A C) → Tm7 Γ (arr7 B C) → Tm7 Γ C)
     (zero  : ∀ {Γ}       , Tm7 Γ nat7)
     (suc   : ∀ {Γ}       , Tm7 Γ nat7 → Tm7 Γ nat7)
     (rec   : ∀ {Γ A}     , Tm7 Γ nat7 → Tm7 Γ (arr7 nat7 (arr7 A A)) → Tm7 Γ A → Tm7 Γ A)
   , Tm7 Γ A

def var7 : ∀ {Γ A}, Var7 Γ A → Tm7 Γ A
 := λ x Tm7 var7 lam app tt pair fst snd left right case zero suc rec =>
     var7 x

def lam7 : ∀ {Γ A B} , Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B)
 := λ t Tm7 var7 lam7 app tt pair fst snd left right case zero suc rec =>
     lam7 (t Tm7 var7 lam7 app tt pair fst snd left right case zero suc rec)

def app7 : ∀ {Γ A B} , Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B
 := λ t u Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec =>
     app7 (t Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec)
         (u Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec)

def tt7 : ∀ {Γ} , Tm7 Γ top7
 := λ Tm7 var7 lam7 app7 tt7 pair fst snd left right case zero suc rec => tt7

def pair7 : ∀ {Γ A B} , Tm7 Γ A → Tm7 Γ B → Tm7 Γ (prod7 A B)
 := λ t u Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec =>
     pair7 (t Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec)
          (u Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec)

def fst7 : ∀ {Γ A B} , Tm7 Γ (prod7 A B) → Tm7 Γ A
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd left right case zero suc rec =>
     fst7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd left right case zero suc rec)

def snd7 : ∀ {Γ A B} , Tm7 Γ (prod7 A B) → Tm7 Γ B
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left right case zero suc rec =>
     snd7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left right case zero suc rec)

def left7 : ∀ {Γ A B} , Tm7 Γ A → Tm7 Γ (sum7 A B)
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right case zero suc rec =>
     left7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right case zero suc rec)

def right7 : ∀ {Γ A B} , Tm7 Γ B → Tm7 Γ (sum7 A B)
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case zero suc rec =>
     right7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case zero suc rec)

def case7 : ∀ {Γ A B C} , Tm7 Γ (sum7 A B) → Tm7 Γ (arr7 A C) → Tm7 Γ (arr7 B C) → Tm7 Γ C
 := λ t u v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec =>
     case7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)
          (u Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)
          (v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)

def zero7  : ∀ {Γ} , Tm7 Γ nat7
 := λ Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc rec => zero7

def suc7 : ∀ {Γ} , Tm7 Γ nat7 → Tm7 Γ nat7
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec =>
   suc7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec)

def rec7 : ∀ {Γ A} , Tm7 Γ nat7 → Tm7 Γ (arr7 nat7 (arr7 A A)) → Tm7 Γ A → Tm7 Γ A
 := λ t u v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7 =>
     rec7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)
         (u Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)
         (v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)

def v07 : ∀ {Γ A}, Tm7 (snoc7 Γ A) A
 := var7 vz7

def v17 : ∀ {Γ A B}, Tm7 (snoc7 (snoc7 Γ A) B) A
 := var7 (vs7 vz7)

def v27 : ∀ {Γ A B C}, Tm7 (snoc7 (snoc7 (snoc7 Γ A) B) C) A
 := var7 (vs7 (vs7 vz7))

def v37 : ∀ {Γ A B C D}, Tm7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) A
 := var7 (vs7 (vs7 (vs7 vz7)))

def tbool7 : Ty7
 := sum7 top7 top7

def ttrue7 : ∀ {Γ}, Tm7 Γ tbool7
 := left7 tt7

def tfalse7 : ∀ {Γ}, Tm7 Γ tbool7
 := right7 tt7

def ifthenelse7 : ∀ {Γ A}, Tm7 Γ (arr7 tbool7 (arr7 A (arr7 A A)))
 := lam7 (lam7 (lam7 (case7 v27 (lam7 v27) (lam7 v17))))

def times47 : ∀ {Γ A}, Tm7 Γ (arr7 (arr7 A A) (arr7 A A))
  := lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07)))))

def add7 : ∀ {Γ}, Tm7 Γ (arr7 nat7 (arr7 nat7 nat7))
 := lam7 (rec7 v07
      (lam7 (lam7 (lam7 (suc7 (app7 v17 v07)))))
      (lam7 v07))

def mul7 : ∀ {Γ}, Tm7 Γ (arr7 nat7 (arr7 nat7 nat7))
 := lam7 (rec7 v07
     (lam7 (lam7 (lam7 (app7 (app7 add7 (app7 v17 v07)) v07))))
     (lam7 zero7))

def fact7 : ∀ {Γ}, Tm7 Γ (arr7 nat7 nat7)
 := lam7 (rec7 v07 (lam7 (lam7 (app7 (app7 mul7 (suc7 v17)) v07)))
        (suc7 zero7))
