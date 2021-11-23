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
def Ty8 : Type 1
 := ∀ (Ty8           : Type)
      (nat top bot  : Ty8)
      (arr prod sum : Ty8 → Ty8 → Ty8)
    , Ty8

def nat8 : Ty8 := λ _ nat8 _ _ _ _ _ => nat8
def top8 : Ty8 := λ _ _ top8 _ _ _ _ => top8
def bot8 : Ty8 := λ _ _ _ bot8 _ _ _ => bot8

def arr8 : Ty8 → Ty8 → Ty8
 := λ A B Ty8 nat8 top8 bot8 arr8 prod sum =>
     arr8 (A Ty8 nat8 top8 bot8 arr8 prod sum) (B Ty8 nat8 top8 bot8 arr8 prod sum)

def prod8 : Ty8 → Ty8 → Ty8
 := λ A B Ty8 nat8 top8 bot8 arr8 prod8 sum =>
     prod8 (A Ty8 nat8 top8 bot8 arr8 prod8 sum) (B Ty8 nat8 top8 bot8 arr8 prod8 sum)

def sum8 : Ty8 → Ty8 → Ty8
 := λ A B Ty8 nat8 top8 bot8 arr8 prod8 sum8 =>
     sum8 (A Ty8 nat8 top8 bot8 arr8 prod8 sum8) (B Ty8 nat8 top8 bot8 arr8 prod8 sum8)

def Con8 : Type 1
 := ∀ (Con8  : Type)
      (nil  : Con8)
      (snoc : Con8 → Ty8 → Con8)
    , Con8

def nil8 : Con8
 := λ Con8 nil8 snoc => nil8

def snoc8 : Con8 → Ty8 → Con8
 := λ Γ A Con8 nil8 snoc8 => snoc8 (Γ Con8 nil8 snoc8) A

def Var8 : Con8 → Ty8 → Type 1
 := λ Γ A =>
   ∀ (Var8 : Con8 → Ty8 → Type)
     (vz  : ∀{Γ A}, Var8 (snoc8 Γ A) A)
     (vs  : ∀{Γ B A}, Var8 Γ A → Var8 (snoc8 Γ B) A)
   , Var8 Γ A

def vz8 : ∀ {Γ A}, Var8 (snoc8 Γ A) A
 := λ Var8 vz8 vs => vz8

def vs8 : ∀ {Γ B A}, Var8 Γ A → Var8 (snoc8 Γ B) A
 := λ x Var8 vz8 vs8 => vs8 (x Var8 vz8 vs8)

def Tm8 : Con8 → Ty8 → Type 1
 := λ Γ A =>
   ∀ (Tm8  : Con8 → Ty8 → Type)
     (var : ∀ {Γ A}, Var8 Γ A → Tm8 Γ A)
     (lam : ∀ {Γ A B}, (Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B)))
     (app   : ∀ {Γ A B}   , Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B)
     (tt    : ∀ {Γ}       , Tm8 Γ top8)
     (pair  : ∀ {Γ A B}   , Tm8 Γ A → Tm8 Γ B → Tm8 Γ (prod8 A B))
     (fst   : ∀ {Γ A B}   , Tm8 Γ (prod8 A B) → Tm8 Γ A)
     (snd   : ∀ {Γ A B}   , Tm8 Γ (prod8 A B) → Tm8 Γ B)
     (left  : ∀ {Γ A B}   , Tm8 Γ A → Tm8 Γ (sum8 A B))
     (right : ∀ {Γ A B}   , Tm8 Γ B → Tm8 Γ (sum8 A B))
     (case  : ∀ {Γ A B C} , Tm8 Γ (sum8 A B) → Tm8 Γ (arr8 A C) → Tm8 Γ (arr8 B C) → Tm8 Γ C)
     (zero  : ∀ {Γ}       , Tm8 Γ nat8)
     (suc   : ∀ {Γ}       , Tm8 Γ nat8 → Tm8 Γ nat8)
     (rec   : ∀ {Γ A}     , Tm8 Γ nat8 → Tm8 Γ (arr8 nat8 (arr8 A A)) → Tm8 Γ A → Tm8 Γ A)
   , Tm8 Γ A

def var8 : ∀ {Γ A}, Var8 Γ A → Tm8 Γ A
 := λ x Tm8 var8 lam app tt pair fst snd left right case zero suc rec =>
     var8 x

def lam8 : ∀ {Γ A B} , Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B)
 := λ t Tm8 var8 lam8 app tt pair fst snd left right case zero suc rec =>
     lam8 (t Tm8 var8 lam8 app tt pair fst snd left right case zero suc rec)

def app8 : ∀ {Γ A B} , Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B
 := λ t u Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec =>
     app8 (t Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec)
         (u Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec)

def tt8 : ∀ {Γ} , Tm8 Γ top8
 := λ Tm8 var8 lam8 app8 tt8 pair fst snd left right case zero suc rec => tt8

def pair8 : ∀ {Γ A B} , Tm8 Γ A → Tm8 Γ B → Tm8 Γ (prod8 A B)
 := λ t u Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec =>
     pair8 (t Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec)
          (u Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec)

def fst8 : ∀ {Γ A B} , Tm8 Γ (prod8 A B) → Tm8 Γ A
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd left right case zero suc rec =>
     fst8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd left right case zero suc rec)

def snd8 : ∀ {Γ A B} , Tm8 Γ (prod8 A B) → Tm8 Γ B
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left right case zero suc rec =>
     snd8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left right case zero suc rec)

def left8 : ∀ {Γ A B} , Tm8 Γ A → Tm8 Γ (sum8 A B)
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right case zero suc rec =>
     left8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right case zero suc rec)

def right8 : ∀ {Γ A B} , Tm8 Γ B → Tm8 Γ (sum8 A B)
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case zero suc rec =>
     right8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case zero suc rec)

def case8 : ∀ {Γ A B C} , Tm8 Γ (sum8 A B) → Tm8 Γ (arr8 A C) → Tm8 Γ (arr8 B C) → Tm8 Γ C
 := λ t u v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec =>
     case8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)
          (u Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)
          (v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)

def zero8  : ∀ {Γ} , Tm8 Γ nat8
 := λ Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc rec => zero8

def suc8 : ∀ {Γ} , Tm8 Γ nat8 → Tm8 Γ nat8
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec =>
   suc8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec)

def rec8 : ∀ {Γ A} , Tm8 Γ nat8 → Tm8 Γ (arr8 nat8 (arr8 A A)) → Tm8 Γ A → Tm8 Γ A
 := λ t u v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8 =>
     rec8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)
         (u Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)
         (v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)

def v08 : ∀ {Γ A}, Tm8 (snoc8 Γ A) A
 := var8 vz8

def v18 : ∀ {Γ A B}, Tm8 (snoc8 (snoc8 Γ A) B) A
 := var8 (vs8 vz8)

def v28 : ∀ {Γ A B C}, Tm8 (snoc8 (snoc8 (snoc8 Γ A) B) C) A
 := var8 (vs8 (vs8 vz8))

def v38 : ∀ {Γ A B C D}, Tm8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) A
 := var8 (vs8 (vs8 (vs8 vz8)))

def tbool8 : Ty8
 := sum8 top8 top8

def ttrue8 : ∀ {Γ}, Tm8 Γ tbool8
 := left8 tt8

def tfalse8 : ∀ {Γ}, Tm8 Γ tbool8
 := right8 tt8

def ifthenelse8 : ∀ {Γ A}, Tm8 Γ (arr8 tbool8 (arr8 A (arr8 A A)))
 := lam8 (lam8 (lam8 (case8 v28 (lam8 v28) (lam8 v18))))

def times48 : ∀ {Γ A}, Tm8 Γ (arr8 (arr8 A A) (arr8 A A))
  := lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08)))))

def add8 : ∀ {Γ}, Tm8 Γ (arr8 nat8 (arr8 nat8 nat8))
 := lam8 (rec8 v08
      (lam8 (lam8 (lam8 (suc8 (app8 v18 v08)))))
      (lam8 v08))

def mul8 : ∀ {Γ}, Tm8 Γ (arr8 nat8 (arr8 nat8 nat8))
 := lam8 (rec8 v08
     (lam8 (lam8 (lam8 (app8 (app8 add8 (app8 v18 v08)) v08))))
     (lam8 zero8))

def fact8 : ∀ {Γ}, Tm8 Γ (arr8 nat8 nat8)
 := lam8 (rec8 v08 (lam8 (lam8 (app8 (app8 mul8 (suc8 v18)) v08)))
        (suc8 zero8))
def Ty9 : Type 1
 := ∀ (Ty9           : Type)
      (nat top bot  : Ty9)
      (arr prod sum : Ty9 → Ty9 → Ty9)
    , Ty9

def nat9 : Ty9 := λ _ nat9 _ _ _ _ _ => nat9
def top9 : Ty9 := λ _ _ top9 _ _ _ _ => top9
def bot9 : Ty9 := λ _ _ _ bot9 _ _ _ => bot9

def arr9 : Ty9 → Ty9 → Ty9
 := λ A B Ty9 nat9 top9 bot9 arr9 prod sum =>
     arr9 (A Ty9 nat9 top9 bot9 arr9 prod sum) (B Ty9 nat9 top9 bot9 arr9 prod sum)

def prod9 : Ty9 → Ty9 → Ty9
 := λ A B Ty9 nat9 top9 bot9 arr9 prod9 sum =>
     prod9 (A Ty9 nat9 top9 bot9 arr9 prod9 sum) (B Ty9 nat9 top9 bot9 arr9 prod9 sum)

def sum9 : Ty9 → Ty9 → Ty9
 := λ A B Ty9 nat9 top9 bot9 arr9 prod9 sum9 =>
     sum9 (A Ty9 nat9 top9 bot9 arr9 prod9 sum9) (B Ty9 nat9 top9 bot9 arr9 prod9 sum9)

def Con9 : Type 1
 := ∀ (Con9  : Type)
      (nil  : Con9)
      (snoc : Con9 → Ty9 → Con9)
    , Con9

def nil9 : Con9
 := λ Con9 nil9 snoc => nil9

def snoc9 : Con9 → Ty9 → Con9
 := λ Γ A Con9 nil9 snoc9 => snoc9 (Γ Con9 nil9 snoc9) A

def Var9 : Con9 → Ty9 → Type 1
 := λ Γ A =>
   ∀ (Var9 : Con9 → Ty9 → Type)
     (vz  : ∀{Γ A}, Var9 (snoc9 Γ A) A)
     (vs  : ∀{Γ B A}, Var9 Γ A → Var9 (snoc9 Γ B) A)
   , Var9 Γ A

def vz9 : ∀ {Γ A}, Var9 (snoc9 Γ A) A
 := λ Var9 vz9 vs => vz9

def vs9 : ∀ {Γ B A}, Var9 Γ A → Var9 (snoc9 Γ B) A
 := λ x Var9 vz9 vs9 => vs9 (x Var9 vz9 vs9)

def Tm9 : Con9 → Ty9 → Type 1
 := λ Γ A =>
   ∀ (Tm9  : Con9 → Ty9 → Type)
     (var : ∀ {Γ A}, Var9 Γ A → Tm9 Γ A)
     (lam : ∀ {Γ A B}, (Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B)))
     (app   : ∀ {Γ A B}   , Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B)
     (tt    : ∀ {Γ}       , Tm9 Γ top9)
     (pair  : ∀ {Γ A B}   , Tm9 Γ A → Tm9 Γ B → Tm9 Γ (prod9 A B))
     (fst   : ∀ {Γ A B}   , Tm9 Γ (prod9 A B) → Tm9 Γ A)
     (snd   : ∀ {Γ A B}   , Tm9 Γ (prod9 A B) → Tm9 Γ B)
     (left  : ∀ {Γ A B}   , Tm9 Γ A → Tm9 Γ (sum9 A B))
     (right : ∀ {Γ A B}   , Tm9 Γ B → Tm9 Γ (sum9 A B))
     (case  : ∀ {Γ A B C} , Tm9 Γ (sum9 A B) → Tm9 Γ (arr9 A C) → Tm9 Γ (arr9 B C) → Tm9 Γ C)
     (zero  : ∀ {Γ}       , Tm9 Γ nat9)
     (suc   : ∀ {Γ}       , Tm9 Γ nat9 → Tm9 Γ nat9)
     (rec   : ∀ {Γ A}     , Tm9 Γ nat9 → Tm9 Γ (arr9 nat9 (arr9 A A)) → Tm9 Γ A → Tm9 Γ A)
   , Tm9 Γ A

def var9 : ∀ {Γ A}, Var9 Γ A → Tm9 Γ A
 := λ x Tm9 var9 lam app tt pair fst snd left right case zero suc rec =>
     var9 x

def lam9 : ∀ {Γ A B} , Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B)
 := λ t Tm9 var9 lam9 app tt pair fst snd left right case zero suc rec =>
     lam9 (t Tm9 var9 lam9 app tt pair fst snd left right case zero suc rec)

def app9 : ∀ {Γ A B} , Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B
 := λ t u Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec =>
     app9 (t Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec)
         (u Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec)

def tt9 : ∀ {Γ} , Tm9 Γ top9
 := λ Tm9 var9 lam9 app9 tt9 pair fst snd left right case zero suc rec => tt9

def pair9 : ∀ {Γ A B} , Tm9 Γ A → Tm9 Γ B → Tm9 Γ (prod9 A B)
 := λ t u Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec =>
     pair9 (t Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec)
          (u Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec)

def fst9 : ∀ {Γ A B} , Tm9 Γ (prod9 A B) → Tm9 Γ A
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd left right case zero suc rec =>
     fst9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd left right case zero suc rec)

def snd9 : ∀ {Γ A B} , Tm9 Γ (prod9 A B) → Tm9 Γ B
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left right case zero suc rec =>
     snd9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left right case zero suc rec)

def left9 : ∀ {Γ A B} , Tm9 Γ A → Tm9 Γ (sum9 A B)
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right case zero suc rec =>
     left9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right case zero suc rec)

def right9 : ∀ {Γ A B} , Tm9 Γ B → Tm9 Γ (sum9 A B)
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case zero suc rec =>
     right9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case zero suc rec)

def case9 : ∀ {Γ A B C} , Tm9 Γ (sum9 A B) → Tm9 Γ (arr9 A C) → Tm9 Γ (arr9 B C) → Tm9 Γ C
 := λ t u v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec =>
     case9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)
          (u Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)
          (v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)

def zero9  : ∀ {Γ} , Tm9 Γ nat9
 := λ Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc rec => zero9

def suc9 : ∀ {Γ} , Tm9 Γ nat9 → Tm9 Γ nat9
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec =>
   suc9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec)

def rec9 : ∀ {Γ A} , Tm9 Γ nat9 → Tm9 Γ (arr9 nat9 (arr9 A A)) → Tm9 Γ A → Tm9 Γ A
 := λ t u v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9 =>
     rec9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)
         (u Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)
         (v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)

def v09 : ∀ {Γ A}, Tm9 (snoc9 Γ A) A
 := var9 vz9

def v19 : ∀ {Γ A B}, Tm9 (snoc9 (snoc9 Γ A) B) A
 := var9 (vs9 vz9)

def v29 : ∀ {Γ A B C}, Tm9 (snoc9 (snoc9 (snoc9 Γ A) B) C) A
 := var9 (vs9 (vs9 vz9))

def v39 : ∀ {Γ A B C D}, Tm9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) A
 := var9 (vs9 (vs9 (vs9 vz9)))

def tbool9 : Ty9
 := sum9 top9 top9

def ttrue9 : ∀ {Γ}, Tm9 Γ tbool9
 := left9 tt9

def tfalse9 : ∀ {Γ}, Tm9 Γ tbool9
 := right9 tt9

def ifthenelse9 : ∀ {Γ A}, Tm9 Γ (arr9 tbool9 (arr9 A (arr9 A A)))
 := lam9 (lam9 (lam9 (case9 v29 (lam9 v29) (lam9 v19))))

def times49 : ∀ {Γ A}, Tm9 Γ (arr9 (arr9 A A) (arr9 A A))
  := lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09)))))

def add9 : ∀ {Γ}, Tm9 Γ (arr9 nat9 (arr9 nat9 nat9))
 := lam9 (rec9 v09
      (lam9 (lam9 (lam9 (suc9 (app9 v19 v09)))))
      (lam9 v09))

def mul9 : ∀ {Γ}, Tm9 Γ (arr9 nat9 (arr9 nat9 nat9))
 := lam9 (rec9 v09
     (lam9 (lam9 (lam9 (app9 (app9 add9 (app9 v19 v09)) v09))))
     (lam9 zero9))

def fact9 : ∀ {Γ}, Tm9 Γ (arr9 nat9 nat9)
 := lam9 (rec9 v09 (lam9 (lam9 (app9 (app9 mul9 (suc9 v19)) v09)))
        (suc9 zero9))
def Ty10 : Type 1
 := ∀ (Ty10           : Type)
      (nat top bot  : Ty10)
      (arr prod sum : Ty10 → Ty10 → Ty10)
    , Ty10

def nat10 : Ty10 := λ _ nat10 _ _ _ _ _ => nat10
def top10 : Ty10 := λ _ _ top10 _ _ _ _ => top10
def bot10 : Ty10 := λ _ _ _ bot10 _ _ _ => bot10

def arr10 : Ty10 → Ty10 → Ty10
 := λ A B Ty10 nat10 top10 bot10 arr10 prod sum =>
     arr10 (A Ty10 nat10 top10 bot10 arr10 prod sum) (B Ty10 nat10 top10 bot10 arr10 prod sum)

def prod10 : Ty10 → Ty10 → Ty10
 := λ A B Ty10 nat10 top10 bot10 arr10 prod10 sum =>
     prod10 (A Ty10 nat10 top10 bot10 arr10 prod10 sum) (B Ty10 nat10 top10 bot10 arr10 prod10 sum)

def sum10 : Ty10 → Ty10 → Ty10
 := λ A B Ty10 nat10 top10 bot10 arr10 prod10 sum10 =>
     sum10 (A Ty10 nat10 top10 bot10 arr10 prod10 sum10) (B Ty10 nat10 top10 bot10 arr10 prod10 sum10)

def Con10 : Type 1
 := ∀ (Con10  : Type)
      (nil  : Con10)
      (snoc : Con10 → Ty10 → Con10)
    , Con10

def nil10 : Con10
 := λ Con10 nil10 snoc => nil10

def snoc10 : Con10 → Ty10 → Con10
 := λ Γ A Con10 nil10 snoc10 => snoc10 (Γ Con10 nil10 snoc10) A

def Var10 : Con10 → Ty10 → Type 1
 := λ Γ A =>
   ∀ (Var10 : Con10 → Ty10 → Type)
     (vz  : ∀{Γ A}, Var10 (snoc10 Γ A) A)
     (vs  : ∀{Γ B A}, Var10 Γ A → Var10 (snoc10 Γ B) A)
   , Var10 Γ A

def vz10 : ∀ {Γ A}, Var10 (snoc10 Γ A) A
 := λ Var10 vz10 vs => vz10

def vs10 : ∀ {Γ B A}, Var10 Γ A → Var10 (snoc10 Γ B) A
 := λ x Var10 vz10 vs10 => vs10 (x Var10 vz10 vs10)

def Tm10 : Con10 → Ty10 → Type 1
 := λ Γ A =>
   ∀ (Tm10  : Con10 → Ty10 → Type)
     (var : ∀ {Γ A}, Var10 Γ A → Tm10 Γ A)
     (lam : ∀ {Γ A B}, (Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B)))
     (app   : ∀ {Γ A B}   , Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B)
     (tt    : ∀ {Γ}       , Tm10 Γ top10)
     (pair  : ∀ {Γ A B}   , Tm10 Γ A → Tm10 Γ B → Tm10 Γ (prod10 A B))
     (fst   : ∀ {Γ A B}   , Tm10 Γ (prod10 A B) → Tm10 Γ A)
     (snd   : ∀ {Γ A B}   , Tm10 Γ (prod10 A B) → Tm10 Γ B)
     (left  : ∀ {Γ A B}   , Tm10 Γ A → Tm10 Γ (sum10 A B))
     (right : ∀ {Γ A B}   , Tm10 Γ B → Tm10 Γ (sum10 A B))
     (case  : ∀ {Γ A B C} , Tm10 Γ (sum10 A B) → Tm10 Γ (arr10 A C) → Tm10 Γ (arr10 B C) → Tm10 Γ C)
     (zero  : ∀ {Γ}       , Tm10 Γ nat10)
     (suc   : ∀ {Γ}       , Tm10 Γ nat10 → Tm10 Γ nat10)
     (rec   : ∀ {Γ A}     , Tm10 Γ nat10 → Tm10 Γ (arr10 nat10 (arr10 A A)) → Tm10 Γ A → Tm10 Γ A)
   , Tm10 Γ A

def var10 : ∀ {Γ A}, Var10 Γ A → Tm10 Γ A
 := λ x Tm10 var10 lam app tt pair fst snd left right case zero suc rec =>
     var10 x

def lam10 : ∀ {Γ A B} , Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B)
 := λ t Tm10 var10 lam10 app tt pair fst snd left right case zero suc rec =>
     lam10 (t Tm10 var10 lam10 app tt pair fst snd left right case zero suc rec)

def app10 : ∀ {Γ A B} , Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B
 := λ t u Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec =>
     app10 (t Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec)
         (u Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec)

def tt10 : ∀ {Γ} , Tm10 Γ top10
 := λ Tm10 var10 lam10 app10 tt10 pair fst snd left right case zero suc rec => tt10

def pair10 : ∀ {Γ A B} , Tm10 Γ A → Tm10 Γ B → Tm10 Γ (prod10 A B)
 := λ t u Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec =>
     pair10 (t Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec)
          (u Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec)

def fst10 : ∀ {Γ A B} , Tm10 Γ (prod10 A B) → Tm10 Γ A
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd left right case zero suc rec =>
     fst10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd left right case zero suc rec)

def snd10 : ∀ {Γ A B} , Tm10 Γ (prod10 A B) → Tm10 Γ B
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left right case zero suc rec =>
     snd10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left right case zero suc rec)

def left10 : ∀ {Γ A B} , Tm10 Γ A → Tm10 Γ (sum10 A B)
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right case zero suc rec =>
     left10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right case zero suc rec)

def right10 : ∀ {Γ A B} , Tm10 Γ B → Tm10 Γ (sum10 A B)
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case zero suc rec =>
     right10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case zero suc rec)

def case10 : ∀ {Γ A B C} , Tm10 Γ (sum10 A B) → Tm10 Γ (arr10 A C) → Tm10 Γ (arr10 B C) → Tm10 Γ C
 := λ t u v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec =>
     case10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)
          (u Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)
          (v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)

def zero10  : ∀ {Γ} , Tm10 Γ nat10
 := λ Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc rec => zero10

def suc10 : ∀ {Γ} , Tm10 Γ nat10 → Tm10 Γ nat10
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec =>
   suc10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec)

def rec10 : ∀ {Γ A} , Tm10 Γ nat10 → Tm10 Γ (arr10 nat10 (arr10 A A)) → Tm10 Γ A → Tm10 Γ A
 := λ t u v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10 =>
     rec10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)
         (u Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)
         (v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)

def v010 : ∀ {Γ A}, Tm10 (snoc10 Γ A) A
 := var10 vz10

def v110 : ∀ {Γ A B}, Tm10 (snoc10 (snoc10 Γ A) B) A
 := var10 (vs10 vz10)

def v210 : ∀ {Γ A B C}, Tm10 (snoc10 (snoc10 (snoc10 Γ A) B) C) A
 := var10 (vs10 (vs10 vz10))

def v310 : ∀ {Γ A B C D}, Tm10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) A
 := var10 (vs10 (vs10 (vs10 vz10)))

def tbool10 : Ty10
 := sum10 top10 top10

def ttrue10 : ∀ {Γ}, Tm10 Γ tbool10
 := left10 tt10

def tfalse10 : ∀ {Γ}, Tm10 Γ tbool10
 := right10 tt10

def ifthenelse10 : ∀ {Γ A}, Tm10 Γ (arr10 tbool10 (arr10 A (arr10 A A)))
 := lam10 (lam10 (lam10 (case10 v210 (lam10 v210) (lam10 v110))))

def times410 : ∀ {Γ A}, Tm10 Γ (arr10 (arr10 A A) (arr10 A A))
  := lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010)))))

def add10 : ∀ {Γ}, Tm10 Γ (arr10 nat10 (arr10 nat10 nat10))
 := lam10 (rec10 v010
      (lam10 (lam10 (lam10 (suc10 (app10 v110 v010)))))
      (lam10 v010))

def mul10 : ∀ {Γ}, Tm10 Γ (arr10 nat10 (arr10 nat10 nat10))
 := lam10 (rec10 v010
     (lam10 (lam10 (lam10 (app10 (app10 add10 (app10 v110 v010)) v010))))
     (lam10 zero10))

def fact10 : ∀ {Γ}, Tm10 Γ (arr10 nat10 nat10)
 := lam10 (rec10 v010 (lam10 (lam10 (app10 (app10 mul10 (suc10 v110)) v010)))
        (suc10 zero10))
def Ty11 : Type 1
 := ∀ (Ty11           : Type)
      (nat top bot  : Ty11)
      (arr prod sum : Ty11 → Ty11 → Ty11)
    , Ty11

def nat11 : Ty11 := λ _ nat11 _ _ _ _ _ => nat11
def top11 : Ty11 := λ _ _ top11 _ _ _ _ => top11
def bot11 : Ty11 := λ _ _ _ bot11 _ _ _ => bot11

def arr11 : Ty11 → Ty11 → Ty11
 := λ A B Ty11 nat11 top11 bot11 arr11 prod sum =>
     arr11 (A Ty11 nat11 top11 bot11 arr11 prod sum) (B Ty11 nat11 top11 bot11 arr11 prod sum)

def prod11 : Ty11 → Ty11 → Ty11
 := λ A B Ty11 nat11 top11 bot11 arr11 prod11 sum =>
     prod11 (A Ty11 nat11 top11 bot11 arr11 prod11 sum) (B Ty11 nat11 top11 bot11 arr11 prod11 sum)

def sum11 : Ty11 → Ty11 → Ty11
 := λ A B Ty11 nat11 top11 bot11 arr11 prod11 sum11 =>
     sum11 (A Ty11 nat11 top11 bot11 arr11 prod11 sum11) (B Ty11 nat11 top11 bot11 arr11 prod11 sum11)

def Con11 : Type 1
 := ∀ (Con11  : Type)
      (nil  : Con11)
      (snoc : Con11 → Ty11 → Con11)
    , Con11

def nil11 : Con11
 := λ Con11 nil11 snoc => nil11

def snoc11 : Con11 → Ty11 → Con11
 := λ Γ A Con11 nil11 snoc11 => snoc11 (Γ Con11 nil11 snoc11) A

def Var11 : Con11 → Ty11 → Type 1
 := λ Γ A =>
   ∀ (Var11 : Con11 → Ty11 → Type)
     (vz  : ∀{Γ A}, Var11 (snoc11 Γ A) A)
     (vs  : ∀{Γ B A}, Var11 Γ A → Var11 (snoc11 Γ B) A)
   , Var11 Γ A

def vz11 : ∀ {Γ A}, Var11 (snoc11 Γ A) A
 := λ Var11 vz11 vs => vz11

def vs11 : ∀ {Γ B A}, Var11 Γ A → Var11 (snoc11 Γ B) A
 := λ x Var11 vz11 vs11 => vs11 (x Var11 vz11 vs11)

def Tm11 : Con11 → Ty11 → Type 1
 := λ Γ A =>
   ∀ (Tm11  : Con11 → Ty11 → Type)
     (var : ∀ {Γ A}, Var11 Γ A → Tm11 Γ A)
     (lam : ∀ {Γ A B}, (Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B)))
     (app   : ∀ {Γ A B}   , Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B)
     (tt    : ∀ {Γ}       , Tm11 Γ top11)
     (pair  : ∀ {Γ A B}   , Tm11 Γ A → Tm11 Γ B → Tm11 Γ (prod11 A B))
     (fst   : ∀ {Γ A B}   , Tm11 Γ (prod11 A B) → Tm11 Γ A)
     (snd   : ∀ {Γ A B}   , Tm11 Γ (prod11 A B) → Tm11 Γ B)
     (left  : ∀ {Γ A B}   , Tm11 Γ A → Tm11 Γ (sum11 A B))
     (right : ∀ {Γ A B}   , Tm11 Γ B → Tm11 Γ (sum11 A B))
     (case  : ∀ {Γ A B C} , Tm11 Γ (sum11 A B) → Tm11 Γ (arr11 A C) → Tm11 Γ (arr11 B C) → Tm11 Γ C)
     (zero  : ∀ {Γ}       , Tm11 Γ nat11)
     (suc   : ∀ {Γ}       , Tm11 Γ nat11 → Tm11 Γ nat11)
     (rec   : ∀ {Γ A}     , Tm11 Γ nat11 → Tm11 Γ (arr11 nat11 (arr11 A A)) → Tm11 Γ A → Tm11 Γ A)
   , Tm11 Γ A

def var11 : ∀ {Γ A}, Var11 Γ A → Tm11 Γ A
 := λ x Tm11 var11 lam app tt pair fst snd left right case zero suc rec =>
     var11 x

def lam11 : ∀ {Γ A B} , Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B)
 := λ t Tm11 var11 lam11 app tt pair fst snd left right case zero suc rec =>
     lam11 (t Tm11 var11 lam11 app tt pair fst snd left right case zero suc rec)

def app11 : ∀ {Γ A B} , Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B
 := λ t u Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec =>
     app11 (t Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec)
         (u Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec)

def tt11 : ∀ {Γ} , Tm11 Γ top11
 := λ Tm11 var11 lam11 app11 tt11 pair fst snd left right case zero suc rec => tt11

def pair11 : ∀ {Γ A B} , Tm11 Γ A → Tm11 Γ B → Tm11 Γ (prod11 A B)
 := λ t u Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec =>
     pair11 (t Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec)
          (u Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec)

def fst11 : ∀ {Γ A B} , Tm11 Γ (prod11 A B) → Tm11 Γ A
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd left right case zero suc rec =>
     fst11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd left right case zero suc rec)

def snd11 : ∀ {Γ A B} , Tm11 Γ (prod11 A B) → Tm11 Γ B
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left right case zero suc rec =>
     snd11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left right case zero suc rec)

def left11 : ∀ {Γ A B} , Tm11 Γ A → Tm11 Γ (sum11 A B)
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right case zero suc rec =>
     left11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right case zero suc rec)

def right11 : ∀ {Γ A B} , Tm11 Γ B → Tm11 Γ (sum11 A B)
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case zero suc rec =>
     right11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case zero suc rec)

def case11 : ∀ {Γ A B C} , Tm11 Γ (sum11 A B) → Tm11 Γ (arr11 A C) → Tm11 Γ (arr11 B C) → Tm11 Γ C
 := λ t u v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec =>
     case11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)
          (u Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)
          (v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)

def zero11  : ∀ {Γ} , Tm11 Γ nat11
 := λ Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc rec => zero11

def suc11 : ∀ {Γ} , Tm11 Γ nat11 → Tm11 Γ nat11
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec =>
   suc11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec)

def rec11 : ∀ {Γ A} , Tm11 Γ nat11 → Tm11 Γ (arr11 nat11 (arr11 A A)) → Tm11 Γ A → Tm11 Γ A
 := λ t u v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11 =>
     rec11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)
         (u Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)
         (v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)

def v011 : ∀ {Γ A}, Tm11 (snoc11 Γ A) A
 := var11 vz11

def v111 : ∀ {Γ A B}, Tm11 (snoc11 (snoc11 Γ A) B) A
 := var11 (vs11 vz11)

def v211 : ∀ {Γ A B C}, Tm11 (snoc11 (snoc11 (snoc11 Γ A) B) C) A
 := var11 (vs11 (vs11 vz11))

def v311 : ∀ {Γ A B C D}, Tm11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) A
 := var11 (vs11 (vs11 (vs11 vz11)))

def tbool11 : Ty11
 := sum11 top11 top11

def ttrue11 : ∀ {Γ}, Tm11 Γ tbool11
 := left11 tt11

def tfalse11 : ∀ {Γ}, Tm11 Γ tbool11
 := right11 tt11

def ifthenelse11 : ∀ {Γ A}, Tm11 Γ (arr11 tbool11 (arr11 A (arr11 A A)))
 := lam11 (lam11 (lam11 (case11 v211 (lam11 v211) (lam11 v111))))

def times411 : ∀ {Γ A}, Tm11 Γ (arr11 (arr11 A A) (arr11 A A))
  := lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011)))))

def add11 : ∀ {Γ}, Tm11 Γ (arr11 nat11 (arr11 nat11 nat11))
 := lam11 (rec11 v011
      (lam11 (lam11 (lam11 (suc11 (app11 v111 v011)))))
      (lam11 v011))

def mul11 : ∀ {Γ}, Tm11 Γ (arr11 nat11 (arr11 nat11 nat11))
 := lam11 (rec11 v011
     (lam11 (lam11 (lam11 (app11 (app11 add11 (app11 v111 v011)) v011))))
     (lam11 zero11))

def fact11 : ∀ {Γ}, Tm11 Γ (arr11 nat11 nat11)
 := lam11 (rec11 v011 (lam11 (lam11 (app11 (app11 mul11 (suc11 v111)) v011)))
        (suc11 zero11))
def Ty12 : Type 1
 := ∀ (Ty12           : Type)
      (nat top bot  : Ty12)
      (arr prod sum : Ty12 → Ty12 → Ty12)
    , Ty12

def nat12 : Ty12 := λ _ nat12 _ _ _ _ _ => nat12
def top12 : Ty12 := λ _ _ top12 _ _ _ _ => top12
def bot12 : Ty12 := λ _ _ _ bot12 _ _ _ => bot12

def arr12 : Ty12 → Ty12 → Ty12
 := λ A B Ty12 nat12 top12 bot12 arr12 prod sum =>
     arr12 (A Ty12 nat12 top12 bot12 arr12 prod sum) (B Ty12 nat12 top12 bot12 arr12 prod sum)

def prod12 : Ty12 → Ty12 → Ty12
 := λ A B Ty12 nat12 top12 bot12 arr12 prod12 sum =>
     prod12 (A Ty12 nat12 top12 bot12 arr12 prod12 sum) (B Ty12 nat12 top12 bot12 arr12 prod12 sum)

def sum12 : Ty12 → Ty12 → Ty12
 := λ A B Ty12 nat12 top12 bot12 arr12 prod12 sum12 =>
     sum12 (A Ty12 nat12 top12 bot12 arr12 prod12 sum12) (B Ty12 nat12 top12 bot12 arr12 prod12 sum12)

def Con12 : Type 1
 := ∀ (Con12  : Type)
      (nil  : Con12)
      (snoc : Con12 → Ty12 → Con12)
    , Con12

def nil12 : Con12
 := λ Con12 nil12 snoc => nil12

def snoc12 : Con12 → Ty12 → Con12
 := λ Γ A Con12 nil12 snoc12 => snoc12 (Γ Con12 nil12 snoc12) A

def Var12 : Con12 → Ty12 → Type 1
 := λ Γ A =>
   ∀ (Var12 : Con12 → Ty12 → Type)
     (vz  : ∀{Γ A}, Var12 (snoc12 Γ A) A)
     (vs  : ∀{Γ B A}, Var12 Γ A → Var12 (snoc12 Γ B) A)
   , Var12 Γ A

def vz12 : ∀ {Γ A}, Var12 (snoc12 Γ A) A
 := λ Var12 vz12 vs => vz12

def vs12 : ∀ {Γ B A}, Var12 Γ A → Var12 (snoc12 Γ B) A
 := λ x Var12 vz12 vs12 => vs12 (x Var12 vz12 vs12)

def Tm12 : Con12 → Ty12 → Type 1
 := λ Γ A =>
   ∀ (Tm12  : Con12 → Ty12 → Type)
     (var : ∀ {Γ A}, Var12 Γ A → Tm12 Γ A)
     (lam : ∀ {Γ A B}, (Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B)))
     (app   : ∀ {Γ A B}   , Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B)
     (tt    : ∀ {Γ}       , Tm12 Γ top12)
     (pair  : ∀ {Γ A B}   , Tm12 Γ A → Tm12 Γ B → Tm12 Γ (prod12 A B))
     (fst   : ∀ {Γ A B}   , Tm12 Γ (prod12 A B) → Tm12 Γ A)
     (snd   : ∀ {Γ A B}   , Tm12 Γ (prod12 A B) → Tm12 Γ B)
     (left  : ∀ {Γ A B}   , Tm12 Γ A → Tm12 Γ (sum12 A B))
     (right : ∀ {Γ A B}   , Tm12 Γ B → Tm12 Γ (sum12 A B))
     (case  : ∀ {Γ A B C} , Tm12 Γ (sum12 A B) → Tm12 Γ (arr12 A C) → Tm12 Γ (arr12 B C) → Tm12 Γ C)
     (zero  : ∀ {Γ}       , Tm12 Γ nat12)
     (suc   : ∀ {Γ}       , Tm12 Γ nat12 → Tm12 Γ nat12)
     (rec   : ∀ {Γ A}     , Tm12 Γ nat12 → Tm12 Γ (arr12 nat12 (arr12 A A)) → Tm12 Γ A → Tm12 Γ A)
   , Tm12 Γ A

def var12 : ∀ {Γ A}, Var12 Γ A → Tm12 Γ A
 := λ x Tm12 var12 lam app tt pair fst snd left right case zero suc rec =>
     var12 x

def lam12 : ∀ {Γ A B} , Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B)
 := λ t Tm12 var12 lam12 app tt pair fst snd left right case zero suc rec =>
     lam12 (t Tm12 var12 lam12 app tt pair fst snd left right case zero suc rec)

def app12 : ∀ {Γ A B} , Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B
 := λ t u Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec =>
     app12 (t Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec)
         (u Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec)

def tt12 : ∀ {Γ} , Tm12 Γ top12
 := λ Tm12 var12 lam12 app12 tt12 pair fst snd left right case zero suc rec => tt12

def pair12 : ∀ {Γ A B} , Tm12 Γ A → Tm12 Γ B → Tm12 Γ (prod12 A B)
 := λ t u Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec =>
     pair12 (t Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec)
          (u Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec)

def fst12 : ∀ {Γ A B} , Tm12 Γ (prod12 A B) → Tm12 Γ A
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd left right case zero suc rec =>
     fst12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd left right case zero suc rec)

def snd12 : ∀ {Γ A B} , Tm12 Γ (prod12 A B) → Tm12 Γ B
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left right case zero suc rec =>
     snd12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left right case zero suc rec)

def left12 : ∀ {Γ A B} , Tm12 Γ A → Tm12 Γ (sum12 A B)
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right case zero suc rec =>
     left12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right case zero suc rec)

def right12 : ∀ {Γ A B} , Tm12 Γ B → Tm12 Γ (sum12 A B)
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case zero suc rec =>
     right12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case zero suc rec)

def case12 : ∀ {Γ A B C} , Tm12 Γ (sum12 A B) → Tm12 Γ (arr12 A C) → Tm12 Γ (arr12 B C) → Tm12 Γ C
 := λ t u v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec =>
     case12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)
          (u Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)
          (v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)

def zero12  : ∀ {Γ} , Tm12 Γ nat12
 := λ Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc rec => zero12

def suc12 : ∀ {Γ} , Tm12 Γ nat12 → Tm12 Γ nat12
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec =>
   suc12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec)

def rec12 : ∀ {Γ A} , Tm12 Γ nat12 → Tm12 Γ (arr12 nat12 (arr12 A A)) → Tm12 Γ A → Tm12 Γ A
 := λ t u v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12 =>
     rec12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)
         (u Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)
         (v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)

def v012 : ∀ {Γ A}, Tm12 (snoc12 Γ A) A
 := var12 vz12

def v112 : ∀ {Γ A B}, Tm12 (snoc12 (snoc12 Γ A) B) A
 := var12 (vs12 vz12)

def v212 : ∀ {Γ A B C}, Tm12 (snoc12 (snoc12 (snoc12 Γ A) B) C) A
 := var12 (vs12 (vs12 vz12))

def v312 : ∀ {Γ A B C D}, Tm12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) A
 := var12 (vs12 (vs12 (vs12 vz12)))

def tbool12 : Ty12
 := sum12 top12 top12

def ttrue12 : ∀ {Γ}, Tm12 Γ tbool12
 := left12 tt12

def tfalse12 : ∀ {Γ}, Tm12 Γ tbool12
 := right12 tt12

def ifthenelse12 : ∀ {Γ A}, Tm12 Γ (arr12 tbool12 (arr12 A (arr12 A A)))
 := lam12 (lam12 (lam12 (case12 v212 (lam12 v212) (lam12 v112))))

def times412 : ∀ {Γ A}, Tm12 Γ (arr12 (arr12 A A) (arr12 A A))
  := lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012)))))

def add12 : ∀ {Γ}, Tm12 Γ (arr12 nat12 (arr12 nat12 nat12))
 := lam12 (rec12 v012
      (lam12 (lam12 (lam12 (suc12 (app12 v112 v012)))))
      (lam12 v012))

def mul12 : ∀ {Γ}, Tm12 Γ (arr12 nat12 (arr12 nat12 nat12))
 := lam12 (rec12 v012
     (lam12 (lam12 (lam12 (app12 (app12 add12 (app12 v112 v012)) v012))))
     (lam12 zero12))

def fact12 : ∀ {Γ}, Tm12 Γ (arr12 nat12 nat12)
 := lam12 (rec12 v012 (lam12 (lam12 (app12 (app12 mul12 (suc12 v112)) v012)))
        (suc12 zero12))
def Ty13 : Type 1
 := ∀ (Ty13           : Type)
      (nat top bot  : Ty13)
      (arr prod sum : Ty13 → Ty13 → Ty13)
    , Ty13

def nat13 : Ty13 := λ _ nat13 _ _ _ _ _ => nat13
def top13 : Ty13 := λ _ _ top13 _ _ _ _ => top13
def bot13 : Ty13 := λ _ _ _ bot13 _ _ _ => bot13

def arr13 : Ty13 → Ty13 → Ty13
 := λ A B Ty13 nat13 top13 bot13 arr13 prod sum =>
     arr13 (A Ty13 nat13 top13 bot13 arr13 prod sum) (B Ty13 nat13 top13 bot13 arr13 prod sum)

def prod13 : Ty13 → Ty13 → Ty13
 := λ A B Ty13 nat13 top13 bot13 arr13 prod13 sum =>
     prod13 (A Ty13 nat13 top13 bot13 arr13 prod13 sum) (B Ty13 nat13 top13 bot13 arr13 prod13 sum)

def sum13 : Ty13 → Ty13 → Ty13
 := λ A B Ty13 nat13 top13 bot13 arr13 prod13 sum13 =>
     sum13 (A Ty13 nat13 top13 bot13 arr13 prod13 sum13) (B Ty13 nat13 top13 bot13 arr13 prod13 sum13)

def Con13 : Type 1
 := ∀ (Con13  : Type)
      (nil  : Con13)
      (snoc : Con13 → Ty13 → Con13)
    , Con13

def nil13 : Con13
 := λ Con13 nil13 snoc => nil13

def snoc13 : Con13 → Ty13 → Con13
 := λ Γ A Con13 nil13 snoc13 => snoc13 (Γ Con13 nil13 snoc13) A

def Var13 : Con13 → Ty13 → Type 1
 := λ Γ A =>
   ∀ (Var13 : Con13 → Ty13 → Type)
     (vz  : ∀{Γ A}, Var13 (snoc13 Γ A) A)
     (vs  : ∀{Γ B A}, Var13 Γ A → Var13 (snoc13 Γ B) A)
   , Var13 Γ A

def vz13 : ∀ {Γ A}, Var13 (snoc13 Γ A) A
 := λ Var13 vz13 vs => vz13

def vs13 : ∀ {Γ B A}, Var13 Γ A → Var13 (snoc13 Γ B) A
 := λ x Var13 vz13 vs13 => vs13 (x Var13 vz13 vs13)

def Tm13 : Con13 → Ty13 → Type 1
 := λ Γ A =>
   ∀ (Tm13  : Con13 → Ty13 → Type)
     (var : ∀ {Γ A}, Var13 Γ A → Tm13 Γ A)
     (lam : ∀ {Γ A B}, (Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B)))
     (app   : ∀ {Γ A B}   , Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B)
     (tt    : ∀ {Γ}       , Tm13 Γ top13)
     (pair  : ∀ {Γ A B}   , Tm13 Γ A → Tm13 Γ B → Tm13 Γ (prod13 A B))
     (fst   : ∀ {Γ A B}   , Tm13 Γ (prod13 A B) → Tm13 Γ A)
     (snd   : ∀ {Γ A B}   , Tm13 Γ (prod13 A B) → Tm13 Γ B)
     (left  : ∀ {Γ A B}   , Tm13 Γ A → Tm13 Γ (sum13 A B))
     (right : ∀ {Γ A B}   , Tm13 Γ B → Tm13 Γ (sum13 A B))
     (case  : ∀ {Γ A B C} , Tm13 Γ (sum13 A B) → Tm13 Γ (arr13 A C) → Tm13 Γ (arr13 B C) → Tm13 Γ C)
     (zero  : ∀ {Γ}       , Tm13 Γ nat13)
     (suc   : ∀ {Γ}       , Tm13 Γ nat13 → Tm13 Γ nat13)
     (rec   : ∀ {Γ A}     , Tm13 Γ nat13 → Tm13 Γ (arr13 nat13 (arr13 A A)) → Tm13 Γ A → Tm13 Γ A)
   , Tm13 Γ A

def var13 : ∀ {Γ A}, Var13 Γ A → Tm13 Γ A
 := λ x Tm13 var13 lam app tt pair fst snd left right case zero suc rec =>
     var13 x

def lam13 : ∀ {Γ A B} , Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B)
 := λ t Tm13 var13 lam13 app tt pair fst snd left right case zero suc rec =>
     lam13 (t Tm13 var13 lam13 app tt pair fst snd left right case zero suc rec)

def app13 : ∀ {Γ A B} , Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B
 := λ t u Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec =>
     app13 (t Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec)
         (u Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec)

def tt13 : ∀ {Γ} , Tm13 Γ top13
 := λ Tm13 var13 lam13 app13 tt13 pair fst snd left right case zero suc rec => tt13

def pair13 : ∀ {Γ A B} , Tm13 Γ A → Tm13 Γ B → Tm13 Γ (prod13 A B)
 := λ t u Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec =>
     pair13 (t Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec)
          (u Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec)

def fst13 : ∀ {Γ A B} , Tm13 Γ (prod13 A B) → Tm13 Γ A
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd left right case zero suc rec =>
     fst13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd left right case zero suc rec)

def snd13 : ∀ {Γ A B} , Tm13 Γ (prod13 A B) → Tm13 Γ B
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left right case zero suc rec =>
     snd13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left right case zero suc rec)

def left13 : ∀ {Γ A B} , Tm13 Γ A → Tm13 Γ (sum13 A B)
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right case zero suc rec =>
     left13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right case zero suc rec)

def right13 : ∀ {Γ A B} , Tm13 Γ B → Tm13 Γ (sum13 A B)
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case zero suc rec =>
     right13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case zero suc rec)

def case13 : ∀ {Γ A B C} , Tm13 Γ (sum13 A B) → Tm13 Γ (arr13 A C) → Tm13 Γ (arr13 B C) → Tm13 Γ C
 := λ t u v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec =>
     case13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)
          (u Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)
          (v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)

def zero13  : ∀ {Γ} , Tm13 Γ nat13
 := λ Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc rec => zero13

def suc13 : ∀ {Γ} , Tm13 Γ nat13 → Tm13 Γ nat13
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec =>
   suc13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec)

def rec13 : ∀ {Γ A} , Tm13 Γ nat13 → Tm13 Γ (arr13 nat13 (arr13 A A)) → Tm13 Γ A → Tm13 Γ A
 := λ t u v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13 =>
     rec13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)
         (u Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)
         (v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)

def v013 : ∀ {Γ A}, Tm13 (snoc13 Γ A) A
 := var13 vz13

def v113 : ∀ {Γ A B}, Tm13 (snoc13 (snoc13 Γ A) B) A
 := var13 (vs13 vz13)

def v213 : ∀ {Γ A B C}, Tm13 (snoc13 (snoc13 (snoc13 Γ A) B) C) A
 := var13 (vs13 (vs13 vz13))

def v313 : ∀ {Γ A B C D}, Tm13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) A
 := var13 (vs13 (vs13 (vs13 vz13)))

def tbool13 : Ty13
 := sum13 top13 top13

def ttrue13 : ∀ {Γ}, Tm13 Γ tbool13
 := left13 tt13

def tfalse13 : ∀ {Γ}, Tm13 Γ tbool13
 := right13 tt13

def ifthenelse13 : ∀ {Γ A}, Tm13 Γ (arr13 tbool13 (arr13 A (arr13 A A)))
 := lam13 (lam13 (lam13 (case13 v213 (lam13 v213) (lam13 v113))))

def times413 : ∀ {Γ A}, Tm13 Γ (arr13 (arr13 A A) (arr13 A A))
  := lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013)))))

def add13 : ∀ {Γ}, Tm13 Γ (arr13 nat13 (arr13 nat13 nat13))
 := lam13 (rec13 v013
      (lam13 (lam13 (lam13 (suc13 (app13 v113 v013)))))
      (lam13 v013))

def mul13 : ∀ {Γ}, Tm13 Γ (arr13 nat13 (arr13 nat13 nat13))
 := lam13 (rec13 v013
     (lam13 (lam13 (lam13 (app13 (app13 add13 (app13 v113 v013)) v013))))
     (lam13 zero13))

def fact13 : ∀ {Γ}, Tm13 Γ (arr13 nat13 nat13)
 := lam13 (rec13 v013 (lam13 (lam13 (app13 (app13 mul13 (suc13 v113)) v013)))
        (suc13 zero13))
def Ty14 : Type 1
 := ∀ (Ty14           : Type)
      (nat top bot  : Ty14)
      (arr prod sum : Ty14 → Ty14 → Ty14)
    , Ty14

def nat14 : Ty14 := λ _ nat14 _ _ _ _ _ => nat14
def top14 : Ty14 := λ _ _ top14 _ _ _ _ => top14
def bot14 : Ty14 := λ _ _ _ bot14 _ _ _ => bot14

def arr14 : Ty14 → Ty14 → Ty14
 := λ A B Ty14 nat14 top14 bot14 arr14 prod sum =>
     arr14 (A Ty14 nat14 top14 bot14 arr14 prod sum) (B Ty14 nat14 top14 bot14 arr14 prod sum)

def prod14 : Ty14 → Ty14 → Ty14
 := λ A B Ty14 nat14 top14 bot14 arr14 prod14 sum =>
     prod14 (A Ty14 nat14 top14 bot14 arr14 prod14 sum) (B Ty14 nat14 top14 bot14 arr14 prod14 sum)

def sum14 : Ty14 → Ty14 → Ty14
 := λ A B Ty14 nat14 top14 bot14 arr14 prod14 sum14 =>
     sum14 (A Ty14 nat14 top14 bot14 arr14 prod14 sum14) (B Ty14 nat14 top14 bot14 arr14 prod14 sum14)

def Con14 : Type 1
 := ∀ (Con14  : Type)
      (nil  : Con14)
      (snoc : Con14 → Ty14 → Con14)
    , Con14

def nil14 : Con14
 := λ Con14 nil14 snoc => nil14

def snoc14 : Con14 → Ty14 → Con14
 := λ Γ A Con14 nil14 snoc14 => snoc14 (Γ Con14 nil14 snoc14) A

def Var14 : Con14 → Ty14 → Type 1
 := λ Γ A =>
   ∀ (Var14 : Con14 → Ty14 → Type)
     (vz  : ∀{Γ A}, Var14 (snoc14 Γ A) A)
     (vs  : ∀{Γ B A}, Var14 Γ A → Var14 (snoc14 Γ B) A)
   , Var14 Γ A

def vz14 : ∀ {Γ A}, Var14 (snoc14 Γ A) A
 := λ Var14 vz14 vs => vz14

def vs14 : ∀ {Γ B A}, Var14 Γ A → Var14 (snoc14 Γ B) A
 := λ x Var14 vz14 vs14 => vs14 (x Var14 vz14 vs14)

def Tm14 : Con14 → Ty14 → Type 1
 := λ Γ A =>
   ∀ (Tm14  : Con14 → Ty14 → Type)
     (var : ∀ {Γ A}, Var14 Γ A → Tm14 Γ A)
     (lam : ∀ {Γ A B}, (Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B)))
     (app   : ∀ {Γ A B}   , Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B)
     (tt    : ∀ {Γ}       , Tm14 Γ top14)
     (pair  : ∀ {Γ A B}   , Tm14 Γ A → Tm14 Γ B → Tm14 Γ (prod14 A B))
     (fst   : ∀ {Γ A B}   , Tm14 Γ (prod14 A B) → Tm14 Γ A)
     (snd   : ∀ {Γ A B}   , Tm14 Γ (prod14 A B) → Tm14 Γ B)
     (left  : ∀ {Γ A B}   , Tm14 Γ A → Tm14 Γ (sum14 A B))
     (right : ∀ {Γ A B}   , Tm14 Γ B → Tm14 Γ (sum14 A B))
     (case  : ∀ {Γ A B C} , Tm14 Γ (sum14 A B) → Tm14 Γ (arr14 A C) → Tm14 Γ (arr14 B C) → Tm14 Γ C)
     (zero  : ∀ {Γ}       , Tm14 Γ nat14)
     (suc   : ∀ {Γ}       , Tm14 Γ nat14 → Tm14 Γ nat14)
     (rec   : ∀ {Γ A}     , Tm14 Γ nat14 → Tm14 Γ (arr14 nat14 (arr14 A A)) → Tm14 Γ A → Tm14 Γ A)
   , Tm14 Γ A

def var14 : ∀ {Γ A}, Var14 Γ A → Tm14 Γ A
 := λ x Tm14 var14 lam app tt pair fst snd left right case zero suc rec =>
     var14 x

def lam14 : ∀ {Γ A B} , Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B)
 := λ t Tm14 var14 lam14 app tt pair fst snd left right case zero suc rec =>
     lam14 (t Tm14 var14 lam14 app tt pair fst snd left right case zero suc rec)

def app14 : ∀ {Γ A B} , Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B
 := λ t u Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec =>
     app14 (t Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec)
         (u Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec)

def tt14 : ∀ {Γ} , Tm14 Γ top14
 := λ Tm14 var14 lam14 app14 tt14 pair fst snd left right case zero suc rec => tt14

def pair14 : ∀ {Γ A B} , Tm14 Γ A → Tm14 Γ B → Tm14 Γ (prod14 A B)
 := λ t u Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec =>
     pair14 (t Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec)
          (u Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec)

def fst14 : ∀ {Γ A B} , Tm14 Γ (prod14 A B) → Tm14 Γ A
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd left right case zero suc rec =>
     fst14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd left right case zero suc rec)

def snd14 : ∀ {Γ A B} , Tm14 Γ (prod14 A B) → Tm14 Γ B
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left right case zero suc rec =>
     snd14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left right case zero suc rec)

def left14 : ∀ {Γ A B} , Tm14 Γ A → Tm14 Γ (sum14 A B)
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right case zero suc rec =>
     left14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right case zero suc rec)

def right14 : ∀ {Γ A B} , Tm14 Γ B → Tm14 Γ (sum14 A B)
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case zero suc rec =>
     right14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case zero suc rec)

def case14 : ∀ {Γ A B C} , Tm14 Γ (sum14 A B) → Tm14 Γ (arr14 A C) → Tm14 Γ (arr14 B C) → Tm14 Γ C
 := λ t u v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec =>
     case14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)
          (u Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)
          (v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)

def zero14  : ∀ {Γ} , Tm14 Γ nat14
 := λ Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc rec => zero14

def suc14 : ∀ {Γ} , Tm14 Γ nat14 → Tm14 Γ nat14
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec =>
   suc14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec)

def rec14 : ∀ {Γ A} , Tm14 Γ nat14 → Tm14 Γ (arr14 nat14 (arr14 A A)) → Tm14 Γ A → Tm14 Γ A
 := λ t u v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14 =>
     rec14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)
         (u Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)
         (v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)

def v014 : ∀ {Γ A}, Tm14 (snoc14 Γ A) A
 := var14 vz14

def v114 : ∀ {Γ A B}, Tm14 (snoc14 (snoc14 Γ A) B) A
 := var14 (vs14 vz14)

def v214 : ∀ {Γ A B C}, Tm14 (snoc14 (snoc14 (snoc14 Γ A) B) C) A
 := var14 (vs14 (vs14 vz14))

def v314 : ∀ {Γ A B C D}, Tm14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) A
 := var14 (vs14 (vs14 (vs14 vz14)))

def tbool14 : Ty14
 := sum14 top14 top14

def ttrue14 : ∀ {Γ}, Tm14 Γ tbool14
 := left14 tt14

def tfalse14 : ∀ {Γ}, Tm14 Γ tbool14
 := right14 tt14

def ifthenelse14 : ∀ {Γ A}, Tm14 Γ (arr14 tbool14 (arr14 A (arr14 A A)))
 := lam14 (lam14 (lam14 (case14 v214 (lam14 v214) (lam14 v114))))

def times414 : ∀ {Γ A}, Tm14 Γ (arr14 (arr14 A A) (arr14 A A))
  := lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014)))))

def add14 : ∀ {Γ}, Tm14 Γ (arr14 nat14 (arr14 nat14 nat14))
 := lam14 (rec14 v014
      (lam14 (lam14 (lam14 (suc14 (app14 v114 v014)))))
      (lam14 v014))

def mul14 : ∀ {Γ}, Tm14 Γ (arr14 nat14 (arr14 nat14 nat14))
 := lam14 (rec14 v014
     (lam14 (lam14 (lam14 (app14 (app14 add14 (app14 v114 v014)) v014))))
     (lam14 zero14))

def fact14 : ∀ {Γ}, Tm14 Γ (arr14 nat14 nat14)
 := lam14 (rec14 v014 (lam14 (lam14 (app14 (app14 mul14 (suc14 v114)) v014)))
        (suc14 zero14))
def Ty15 : Type 1
 := ∀ (Ty15           : Type)
      (nat top bot  : Ty15)
      (arr prod sum : Ty15 → Ty15 → Ty15)
    , Ty15

def nat15 : Ty15 := λ _ nat15 _ _ _ _ _ => nat15
def top15 : Ty15 := λ _ _ top15 _ _ _ _ => top15
def bot15 : Ty15 := λ _ _ _ bot15 _ _ _ => bot15

def arr15 : Ty15 → Ty15 → Ty15
 := λ A B Ty15 nat15 top15 bot15 arr15 prod sum =>
     arr15 (A Ty15 nat15 top15 bot15 arr15 prod sum) (B Ty15 nat15 top15 bot15 arr15 prod sum)

def prod15 : Ty15 → Ty15 → Ty15
 := λ A B Ty15 nat15 top15 bot15 arr15 prod15 sum =>
     prod15 (A Ty15 nat15 top15 bot15 arr15 prod15 sum) (B Ty15 nat15 top15 bot15 arr15 prod15 sum)

def sum15 : Ty15 → Ty15 → Ty15
 := λ A B Ty15 nat15 top15 bot15 arr15 prod15 sum15 =>
     sum15 (A Ty15 nat15 top15 bot15 arr15 prod15 sum15) (B Ty15 nat15 top15 bot15 arr15 prod15 sum15)

def Con15 : Type 1
 := ∀ (Con15  : Type)
      (nil  : Con15)
      (snoc : Con15 → Ty15 → Con15)
    , Con15

def nil15 : Con15
 := λ Con15 nil15 snoc => nil15

def snoc15 : Con15 → Ty15 → Con15
 := λ Γ A Con15 nil15 snoc15 => snoc15 (Γ Con15 nil15 snoc15) A

def Var15 : Con15 → Ty15 → Type 1
 := λ Γ A =>
   ∀ (Var15 : Con15 → Ty15 → Type)
     (vz  : ∀{Γ A}, Var15 (snoc15 Γ A) A)
     (vs  : ∀{Γ B A}, Var15 Γ A → Var15 (snoc15 Γ B) A)
   , Var15 Γ A

def vz15 : ∀ {Γ A}, Var15 (snoc15 Γ A) A
 := λ Var15 vz15 vs => vz15

def vs15 : ∀ {Γ B A}, Var15 Γ A → Var15 (snoc15 Γ B) A
 := λ x Var15 vz15 vs15 => vs15 (x Var15 vz15 vs15)

def Tm15 : Con15 → Ty15 → Type 1
 := λ Γ A =>
   ∀ (Tm15  : Con15 → Ty15 → Type)
     (var : ∀ {Γ A}, Var15 Γ A → Tm15 Γ A)
     (lam : ∀ {Γ A B}, (Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B)))
     (app   : ∀ {Γ A B}   , Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B)
     (tt    : ∀ {Γ}       , Tm15 Γ top15)
     (pair  : ∀ {Γ A B}   , Tm15 Γ A → Tm15 Γ B → Tm15 Γ (prod15 A B))
     (fst   : ∀ {Γ A B}   , Tm15 Γ (prod15 A B) → Tm15 Γ A)
     (snd   : ∀ {Γ A B}   , Tm15 Γ (prod15 A B) → Tm15 Γ B)
     (left  : ∀ {Γ A B}   , Tm15 Γ A → Tm15 Γ (sum15 A B))
     (right : ∀ {Γ A B}   , Tm15 Γ B → Tm15 Γ (sum15 A B))
     (case  : ∀ {Γ A B C} , Tm15 Γ (sum15 A B) → Tm15 Γ (arr15 A C) → Tm15 Γ (arr15 B C) → Tm15 Γ C)
     (zero  : ∀ {Γ}       , Tm15 Γ nat15)
     (suc   : ∀ {Γ}       , Tm15 Γ nat15 → Tm15 Γ nat15)
     (rec   : ∀ {Γ A}     , Tm15 Γ nat15 → Tm15 Γ (arr15 nat15 (arr15 A A)) → Tm15 Γ A → Tm15 Γ A)
   , Tm15 Γ A

def var15 : ∀ {Γ A}, Var15 Γ A → Tm15 Γ A
 := λ x Tm15 var15 lam app tt pair fst snd left right case zero suc rec =>
     var15 x

def lam15 : ∀ {Γ A B} , Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B)
 := λ t Tm15 var15 lam15 app tt pair fst snd left right case zero suc rec =>
     lam15 (t Tm15 var15 lam15 app tt pair fst snd left right case zero suc rec)

def app15 : ∀ {Γ A B} , Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B
 := λ t u Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec =>
     app15 (t Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec)
         (u Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec)

def tt15 : ∀ {Γ} , Tm15 Γ top15
 := λ Tm15 var15 lam15 app15 tt15 pair fst snd left right case zero suc rec => tt15

def pair15 : ∀ {Γ A B} , Tm15 Γ A → Tm15 Γ B → Tm15 Γ (prod15 A B)
 := λ t u Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec =>
     pair15 (t Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec)
          (u Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec)

def fst15 : ∀ {Γ A B} , Tm15 Γ (prod15 A B) → Tm15 Γ A
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd left right case zero suc rec =>
     fst15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd left right case zero suc rec)

def snd15 : ∀ {Γ A B} , Tm15 Γ (prod15 A B) → Tm15 Γ B
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left right case zero suc rec =>
     snd15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left right case zero suc rec)

def left15 : ∀ {Γ A B} , Tm15 Γ A → Tm15 Γ (sum15 A B)
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right case zero suc rec =>
     left15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right case zero suc rec)

def right15 : ∀ {Γ A B} , Tm15 Γ B → Tm15 Γ (sum15 A B)
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case zero suc rec =>
     right15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case zero suc rec)

def case15 : ∀ {Γ A B C} , Tm15 Γ (sum15 A B) → Tm15 Γ (arr15 A C) → Tm15 Γ (arr15 B C) → Tm15 Γ C
 := λ t u v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec =>
     case15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)
          (u Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)
          (v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)

def zero15  : ∀ {Γ} , Tm15 Γ nat15
 := λ Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc rec => zero15

def suc15 : ∀ {Γ} , Tm15 Γ nat15 → Tm15 Γ nat15
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec =>
   suc15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec)

def rec15 : ∀ {Γ A} , Tm15 Γ nat15 → Tm15 Γ (arr15 nat15 (arr15 A A)) → Tm15 Γ A → Tm15 Γ A
 := λ t u v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15 =>
     rec15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)
         (u Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)
         (v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)

def v015 : ∀ {Γ A}, Tm15 (snoc15 Γ A) A
 := var15 vz15

def v115 : ∀ {Γ A B}, Tm15 (snoc15 (snoc15 Γ A) B) A
 := var15 (vs15 vz15)

def v215 : ∀ {Γ A B C}, Tm15 (snoc15 (snoc15 (snoc15 Γ A) B) C) A
 := var15 (vs15 (vs15 vz15))

def v315 : ∀ {Γ A B C D}, Tm15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) A
 := var15 (vs15 (vs15 (vs15 vz15)))

def tbool15 : Ty15
 := sum15 top15 top15

def ttrue15 : ∀ {Γ}, Tm15 Γ tbool15
 := left15 tt15

def tfalse15 : ∀ {Γ}, Tm15 Γ tbool15
 := right15 tt15

def ifthenelse15 : ∀ {Γ A}, Tm15 Γ (arr15 tbool15 (arr15 A (arr15 A A)))
 := lam15 (lam15 (lam15 (case15 v215 (lam15 v215) (lam15 v115))))

def times415 : ∀ {Γ A}, Tm15 Γ (arr15 (arr15 A A) (arr15 A A))
  := lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015)))))

def add15 : ∀ {Γ}, Tm15 Γ (arr15 nat15 (arr15 nat15 nat15))
 := lam15 (rec15 v015
      (lam15 (lam15 (lam15 (suc15 (app15 v115 v015)))))
      (lam15 v015))

def mul15 : ∀ {Γ}, Tm15 Γ (arr15 nat15 (arr15 nat15 nat15))
 := lam15 (rec15 v015
     (lam15 (lam15 (lam15 (app15 (app15 add15 (app15 v115 v015)) v015))))
     (lam15 zero15))

def fact15 : ∀ {Γ}, Tm15 Γ (arr15 nat15 nat15)
 := lam15 (rec15 v015 (lam15 (lam15 (app15 (app15 mul15 (suc15 v115)) v015)))
        (suc15 zero15))
def Ty16 : Type 1
 := ∀ (Ty16           : Type)
      (nat top bot  : Ty16)
      (arr prod sum : Ty16 → Ty16 → Ty16)
    , Ty16

def nat16 : Ty16 := λ _ nat16 _ _ _ _ _ => nat16
def top16 : Ty16 := λ _ _ top16 _ _ _ _ => top16
def bot16 : Ty16 := λ _ _ _ bot16 _ _ _ => bot16

def arr16 : Ty16 → Ty16 → Ty16
 := λ A B Ty16 nat16 top16 bot16 arr16 prod sum =>
     arr16 (A Ty16 nat16 top16 bot16 arr16 prod sum) (B Ty16 nat16 top16 bot16 arr16 prod sum)

def prod16 : Ty16 → Ty16 → Ty16
 := λ A B Ty16 nat16 top16 bot16 arr16 prod16 sum =>
     prod16 (A Ty16 nat16 top16 bot16 arr16 prod16 sum) (B Ty16 nat16 top16 bot16 arr16 prod16 sum)

def sum16 : Ty16 → Ty16 → Ty16
 := λ A B Ty16 nat16 top16 bot16 arr16 prod16 sum16 =>
     sum16 (A Ty16 nat16 top16 bot16 arr16 prod16 sum16) (B Ty16 nat16 top16 bot16 arr16 prod16 sum16)

def Con16 : Type 1
 := ∀ (Con16  : Type)
      (nil  : Con16)
      (snoc : Con16 → Ty16 → Con16)
    , Con16

def nil16 : Con16
 := λ Con16 nil16 snoc => nil16

def snoc16 : Con16 → Ty16 → Con16
 := λ Γ A Con16 nil16 snoc16 => snoc16 (Γ Con16 nil16 snoc16) A

def Var16 : Con16 → Ty16 → Type 1
 := λ Γ A =>
   ∀ (Var16 : Con16 → Ty16 → Type)
     (vz  : ∀{Γ A}, Var16 (snoc16 Γ A) A)
     (vs  : ∀{Γ B A}, Var16 Γ A → Var16 (snoc16 Γ B) A)
   , Var16 Γ A

def vz16 : ∀ {Γ A}, Var16 (snoc16 Γ A) A
 := λ Var16 vz16 vs => vz16

def vs16 : ∀ {Γ B A}, Var16 Γ A → Var16 (snoc16 Γ B) A
 := λ x Var16 vz16 vs16 => vs16 (x Var16 vz16 vs16)

def Tm16 : Con16 → Ty16 → Type 1
 := λ Γ A =>
   ∀ (Tm16  : Con16 → Ty16 → Type)
     (var : ∀ {Γ A}, Var16 Γ A → Tm16 Γ A)
     (lam : ∀ {Γ A B}, (Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B)))
     (app   : ∀ {Γ A B}   , Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B)
     (tt    : ∀ {Γ}       , Tm16 Γ top16)
     (pair  : ∀ {Γ A B}   , Tm16 Γ A → Tm16 Γ B → Tm16 Γ (prod16 A B))
     (fst   : ∀ {Γ A B}   , Tm16 Γ (prod16 A B) → Tm16 Γ A)
     (snd   : ∀ {Γ A B}   , Tm16 Γ (prod16 A B) → Tm16 Γ B)
     (left  : ∀ {Γ A B}   , Tm16 Γ A → Tm16 Γ (sum16 A B))
     (right : ∀ {Γ A B}   , Tm16 Γ B → Tm16 Γ (sum16 A B))
     (case  : ∀ {Γ A B C} , Tm16 Γ (sum16 A B) → Tm16 Γ (arr16 A C) → Tm16 Γ (arr16 B C) → Tm16 Γ C)
     (zero  : ∀ {Γ}       , Tm16 Γ nat16)
     (suc   : ∀ {Γ}       , Tm16 Γ nat16 → Tm16 Γ nat16)
     (rec   : ∀ {Γ A}     , Tm16 Γ nat16 → Tm16 Γ (arr16 nat16 (arr16 A A)) → Tm16 Γ A → Tm16 Γ A)
   , Tm16 Γ A

def var16 : ∀ {Γ A}, Var16 Γ A → Tm16 Γ A
 := λ x Tm16 var16 lam app tt pair fst snd left right case zero suc rec =>
     var16 x

def lam16 : ∀ {Γ A B} , Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B)
 := λ t Tm16 var16 lam16 app tt pair fst snd left right case zero suc rec =>
     lam16 (t Tm16 var16 lam16 app tt pair fst snd left right case zero suc rec)

def app16 : ∀ {Γ A B} , Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B
 := λ t u Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec =>
     app16 (t Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec)
         (u Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec)

def tt16 : ∀ {Γ} , Tm16 Γ top16
 := λ Tm16 var16 lam16 app16 tt16 pair fst snd left right case zero suc rec => tt16

def pair16 : ∀ {Γ A B} , Tm16 Γ A → Tm16 Γ B → Tm16 Γ (prod16 A B)
 := λ t u Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec =>
     pair16 (t Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec)
          (u Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec)

def fst16 : ∀ {Γ A B} , Tm16 Γ (prod16 A B) → Tm16 Γ A
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd left right case zero suc rec =>
     fst16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd left right case zero suc rec)

def snd16 : ∀ {Γ A B} , Tm16 Γ (prod16 A B) → Tm16 Γ B
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left right case zero suc rec =>
     snd16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left right case zero suc rec)

def left16 : ∀ {Γ A B} , Tm16 Γ A → Tm16 Γ (sum16 A B)
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right case zero suc rec =>
     left16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right case zero suc rec)

def right16 : ∀ {Γ A B} , Tm16 Γ B → Tm16 Γ (sum16 A B)
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case zero suc rec =>
     right16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case zero suc rec)

def case16 : ∀ {Γ A B C} , Tm16 Γ (sum16 A B) → Tm16 Γ (arr16 A C) → Tm16 Γ (arr16 B C) → Tm16 Γ C
 := λ t u v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec =>
     case16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)
          (u Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)
          (v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)

def zero16  : ∀ {Γ} , Tm16 Γ nat16
 := λ Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc rec => zero16

def suc16 : ∀ {Γ} , Tm16 Γ nat16 → Tm16 Γ nat16
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec =>
   suc16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec)

def rec16 : ∀ {Γ A} , Tm16 Γ nat16 → Tm16 Γ (arr16 nat16 (arr16 A A)) → Tm16 Γ A → Tm16 Γ A
 := λ t u v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16 =>
     rec16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)
         (u Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)
         (v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)

def v016 : ∀ {Γ A}, Tm16 (snoc16 Γ A) A
 := var16 vz16

def v116 : ∀ {Γ A B}, Tm16 (snoc16 (snoc16 Γ A) B) A
 := var16 (vs16 vz16)

def v216 : ∀ {Γ A B C}, Tm16 (snoc16 (snoc16 (snoc16 Γ A) B) C) A
 := var16 (vs16 (vs16 vz16))

def v316 : ∀ {Γ A B C D}, Tm16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) A
 := var16 (vs16 (vs16 (vs16 vz16)))

def tbool16 : Ty16
 := sum16 top16 top16

def ttrue16 : ∀ {Γ}, Tm16 Γ tbool16
 := left16 tt16

def tfalse16 : ∀ {Γ}, Tm16 Γ tbool16
 := right16 tt16

def ifthenelse16 : ∀ {Γ A}, Tm16 Γ (arr16 tbool16 (arr16 A (arr16 A A)))
 := lam16 (lam16 (lam16 (case16 v216 (lam16 v216) (lam16 v116))))

def times416 : ∀ {Γ A}, Tm16 Γ (arr16 (arr16 A A) (arr16 A A))
  := lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016)))))

def add16 : ∀ {Γ}, Tm16 Γ (arr16 nat16 (arr16 nat16 nat16))
 := lam16 (rec16 v016
      (lam16 (lam16 (lam16 (suc16 (app16 v116 v016)))))
      (lam16 v016))

def mul16 : ∀ {Γ}, Tm16 Γ (arr16 nat16 (arr16 nat16 nat16))
 := lam16 (rec16 v016
     (lam16 (lam16 (lam16 (app16 (app16 add16 (app16 v116 v016)) v016))))
     (lam16 zero16))

def fact16 : ∀ {Γ}, Tm16 Γ (arr16 nat16 nat16)
 := lam16 (rec16 v016 (lam16 (lam16 (app16 (app16 mul16 (suc16 v116)) v016)))
        (suc16 zero16))
def Ty17 : Type 1
 := ∀ (Ty17           : Type)
      (nat top bot  : Ty17)
      (arr prod sum : Ty17 → Ty17 → Ty17)
    , Ty17

def nat17 : Ty17 := λ _ nat17 _ _ _ _ _ => nat17
def top17 : Ty17 := λ _ _ top17 _ _ _ _ => top17
def bot17 : Ty17 := λ _ _ _ bot17 _ _ _ => bot17

def arr17 : Ty17 → Ty17 → Ty17
 := λ A B Ty17 nat17 top17 bot17 arr17 prod sum =>
     arr17 (A Ty17 nat17 top17 bot17 arr17 prod sum) (B Ty17 nat17 top17 bot17 arr17 prod sum)

def prod17 : Ty17 → Ty17 → Ty17
 := λ A B Ty17 nat17 top17 bot17 arr17 prod17 sum =>
     prod17 (A Ty17 nat17 top17 bot17 arr17 prod17 sum) (B Ty17 nat17 top17 bot17 arr17 prod17 sum)

def sum17 : Ty17 → Ty17 → Ty17
 := λ A B Ty17 nat17 top17 bot17 arr17 prod17 sum17 =>
     sum17 (A Ty17 nat17 top17 bot17 arr17 prod17 sum17) (B Ty17 nat17 top17 bot17 arr17 prod17 sum17)

def Con17 : Type 1
 := ∀ (Con17  : Type)
      (nil  : Con17)
      (snoc : Con17 → Ty17 → Con17)
    , Con17

def nil17 : Con17
 := λ Con17 nil17 snoc => nil17

def snoc17 : Con17 → Ty17 → Con17
 := λ Γ A Con17 nil17 snoc17 => snoc17 (Γ Con17 nil17 snoc17) A

def Var17 : Con17 → Ty17 → Type 1
 := λ Γ A =>
   ∀ (Var17 : Con17 → Ty17 → Type)
     (vz  : ∀{Γ A}, Var17 (snoc17 Γ A) A)
     (vs  : ∀{Γ B A}, Var17 Γ A → Var17 (snoc17 Γ B) A)
   , Var17 Γ A

def vz17 : ∀ {Γ A}, Var17 (snoc17 Γ A) A
 := λ Var17 vz17 vs => vz17

def vs17 : ∀ {Γ B A}, Var17 Γ A → Var17 (snoc17 Γ B) A
 := λ x Var17 vz17 vs17 => vs17 (x Var17 vz17 vs17)

def Tm17 : Con17 → Ty17 → Type 1
 := λ Γ A =>
   ∀ (Tm17  : Con17 → Ty17 → Type)
     (var : ∀ {Γ A}, Var17 Γ A → Tm17 Γ A)
     (lam : ∀ {Γ A B}, (Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B)))
     (app   : ∀ {Γ A B}   , Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B)
     (tt    : ∀ {Γ}       , Tm17 Γ top17)
     (pair  : ∀ {Γ A B}   , Tm17 Γ A → Tm17 Γ B → Tm17 Γ (prod17 A B))
     (fst   : ∀ {Γ A B}   , Tm17 Γ (prod17 A B) → Tm17 Γ A)
     (snd   : ∀ {Γ A B}   , Tm17 Γ (prod17 A B) → Tm17 Γ B)
     (left  : ∀ {Γ A B}   , Tm17 Γ A → Tm17 Γ (sum17 A B))
     (right : ∀ {Γ A B}   , Tm17 Γ B → Tm17 Γ (sum17 A B))
     (case  : ∀ {Γ A B C} , Tm17 Γ (sum17 A B) → Tm17 Γ (arr17 A C) → Tm17 Γ (arr17 B C) → Tm17 Γ C)
     (zero  : ∀ {Γ}       , Tm17 Γ nat17)
     (suc   : ∀ {Γ}       , Tm17 Γ nat17 → Tm17 Γ nat17)
     (rec   : ∀ {Γ A}     , Tm17 Γ nat17 → Tm17 Γ (arr17 nat17 (arr17 A A)) → Tm17 Γ A → Tm17 Γ A)
   , Tm17 Γ A

def var17 : ∀ {Γ A}, Var17 Γ A → Tm17 Γ A
 := λ x Tm17 var17 lam app tt pair fst snd left right case zero suc rec =>
     var17 x

def lam17 : ∀ {Γ A B} , Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B)
 := λ t Tm17 var17 lam17 app tt pair fst snd left right case zero suc rec =>
     lam17 (t Tm17 var17 lam17 app tt pair fst snd left right case zero suc rec)

def app17 : ∀ {Γ A B} , Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B
 := λ t u Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec =>
     app17 (t Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec)
         (u Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec)

def tt17 : ∀ {Γ} , Tm17 Γ top17
 := λ Tm17 var17 lam17 app17 tt17 pair fst snd left right case zero suc rec => tt17

def pair17 : ∀ {Γ A B} , Tm17 Γ A → Tm17 Γ B → Tm17 Γ (prod17 A B)
 := λ t u Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec =>
     pair17 (t Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec)
          (u Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec)

def fst17 : ∀ {Γ A B} , Tm17 Γ (prod17 A B) → Tm17 Γ A
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd left right case zero suc rec =>
     fst17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd left right case zero suc rec)

def snd17 : ∀ {Γ A B} , Tm17 Γ (prod17 A B) → Tm17 Γ B
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left right case zero suc rec =>
     snd17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left right case zero suc rec)

def left17 : ∀ {Γ A B} , Tm17 Γ A → Tm17 Γ (sum17 A B)
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right case zero suc rec =>
     left17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right case zero suc rec)

def right17 : ∀ {Γ A B} , Tm17 Γ B → Tm17 Γ (sum17 A B)
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case zero suc rec =>
     right17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case zero suc rec)

def case17 : ∀ {Γ A B C} , Tm17 Γ (sum17 A B) → Tm17 Γ (arr17 A C) → Tm17 Γ (arr17 B C) → Tm17 Γ C
 := λ t u v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec =>
     case17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)
          (u Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)
          (v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)

def zero17  : ∀ {Γ} , Tm17 Γ nat17
 := λ Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc rec => zero17

def suc17 : ∀ {Γ} , Tm17 Γ nat17 → Tm17 Γ nat17
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec =>
   suc17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec)

def rec17 : ∀ {Γ A} , Tm17 Γ nat17 → Tm17 Γ (arr17 nat17 (arr17 A A)) → Tm17 Γ A → Tm17 Γ A
 := λ t u v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17 =>
     rec17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)
         (u Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)
         (v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)

def v017 : ∀ {Γ A}, Tm17 (snoc17 Γ A) A
 := var17 vz17

def v117 : ∀ {Γ A B}, Tm17 (snoc17 (snoc17 Γ A) B) A
 := var17 (vs17 vz17)

def v217 : ∀ {Γ A B C}, Tm17 (snoc17 (snoc17 (snoc17 Γ A) B) C) A
 := var17 (vs17 (vs17 vz17))

def v317 : ∀ {Γ A B C D}, Tm17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) A
 := var17 (vs17 (vs17 (vs17 vz17)))

def tbool17 : Ty17
 := sum17 top17 top17

def ttrue17 : ∀ {Γ}, Tm17 Γ tbool17
 := left17 tt17

def tfalse17 : ∀ {Γ}, Tm17 Γ tbool17
 := right17 tt17

def ifthenelse17 : ∀ {Γ A}, Tm17 Γ (arr17 tbool17 (arr17 A (arr17 A A)))
 := lam17 (lam17 (lam17 (case17 v217 (lam17 v217) (lam17 v117))))

def times417 : ∀ {Γ A}, Tm17 Γ (arr17 (arr17 A A) (arr17 A A))
  := lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017)))))

def add17 : ∀ {Γ}, Tm17 Γ (arr17 nat17 (arr17 nat17 nat17))
 := lam17 (rec17 v017
      (lam17 (lam17 (lam17 (suc17 (app17 v117 v017)))))
      (lam17 v017))

def mul17 : ∀ {Γ}, Tm17 Γ (arr17 nat17 (arr17 nat17 nat17))
 := lam17 (rec17 v017
     (lam17 (lam17 (lam17 (app17 (app17 add17 (app17 v117 v017)) v017))))
     (lam17 zero17))

def fact17 : ∀ {Γ}, Tm17 Γ (arr17 nat17 nat17)
 := lam17 (rec17 v017 (lam17 (lam17 (app17 (app17 mul17 (suc17 v117)) v017)))
        (suc17 zero17))
def Ty18 : Type 1
 := ∀ (Ty18           : Type)
      (nat top bot  : Ty18)
      (arr prod sum : Ty18 → Ty18 → Ty18)
    , Ty18

def nat18 : Ty18 := λ _ nat18 _ _ _ _ _ => nat18
def top18 : Ty18 := λ _ _ top18 _ _ _ _ => top18
def bot18 : Ty18 := λ _ _ _ bot18 _ _ _ => bot18

def arr18 : Ty18 → Ty18 → Ty18
 := λ A B Ty18 nat18 top18 bot18 arr18 prod sum =>
     arr18 (A Ty18 nat18 top18 bot18 arr18 prod sum) (B Ty18 nat18 top18 bot18 arr18 prod sum)

def prod18 : Ty18 → Ty18 → Ty18
 := λ A B Ty18 nat18 top18 bot18 arr18 prod18 sum =>
     prod18 (A Ty18 nat18 top18 bot18 arr18 prod18 sum) (B Ty18 nat18 top18 bot18 arr18 prod18 sum)

def sum18 : Ty18 → Ty18 → Ty18
 := λ A B Ty18 nat18 top18 bot18 arr18 prod18 sum18 =>
     sum18 (A Ty18 nat18 top18 bot18 arr18 prod18 sum18) (B Ty18 nat18 top18 bot18 arr18 prod18 sum18)

def Con18 : Type 1
 := ∀ (Con18  : Type)
      (nil  : Con18)
      (snoc : Con18 → Ty18 → Con18)
    , Con18

def nil18 : Con18
 := λ Con18 nil18 snoc => nil18

def snoc18 : Con18 → Ty18 → Con18
 := λ Γ A Con18 nil18 snoc18 => snoc18 (Γ Con18 nil18 snoc18) A

def Var18 : Con18 → Ty18 → Type 1
 := λ Γ A =>
   ∀ (Var18 : Con18 → Ty18 → Type)
     (vz  : ∀{Γ A}, Var18 (snoc18 Γ A) A)
     (vs  : ∀{Γ B A}, Var18 Γ A → Var18 (snoc18 Γ B) A)
   , Var18 Γ A

def vz18 : ∀ {Γ A}, Var18 (snoc18 Γ A) A
 := λ Var18 vz18 vs => vz18

def vs18 : ∀ {Γ B A}, Var18 Γ A → Var18 (snoc18 Γ B) A
 := λ x Var18 vz18 vs18 => vs18 (x Var18 vz18 vs18)

def Tm18 : Con18 → Ty18 → Type 1
 := λ Γ A =>
   ∀ (Tm18  : Con18 → Ty18 → Type)
     (var : ∀ {Γ A}, Var18 Γ A → Tm18 Γ A)
     (lam : ∀ {Γ A B}, (Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B)))
     (app   : ∀ {Γ A B}   , Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B)
     (tt    : ∀ {Γ}       , Tm18 Γ top18)
     (pair  : ∀ {Γ A B}   , Tm18 Γ A → Tm18 Γ B → Tm18 Γ (prod18 A B))
     (fst   : ∀ {Γ A B}   , Tm18 Γ (prod18 A B) → Tm18 Γ A)
     (snd   : ∀ {Γ A B}   , Tm18 Γ (prod18 A B) → Tm18 Γ B)
     (left  : ∀ {Γ A B}   , Tm18 Γ A → Tm18 Γ (sum18 A B))
     (right : ∀ {Γ A B}   , Tm18 Γ B → Tm18 Γ (sum18 A B))
     (case  : ∀ {Γ A B C} , Tm18 Γ (sum18 A B) → Tm18 Γ (arr18 A C) → Tm18 Γ (arr18 B C) → Tm18 Γ C)
     (zero  : ∀ {Γ}       , Tm18 Γ nat18)
     (suc   : ∀ {Γ}       , Tm18 Γ nat18 → Tm18 Γ nat18)
     (rec   : ∀ {Γ A}     , Tm18 Γ nat18 → Tm18 Γ (arr18 nat18 (arr18 A A)) → Tm18 Γ A → Tm18 Γ A)
   , Tm18 Γ A

def var18 : ∀ {Γ A}, Var18 Γ A → Tm18 Γ A
 := λ x Tm18 var18 lam app tt pair fst snd left right case zero suc rec =>
     var18 x

def lam18 : ∀ {Γ A B} , Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B)
 := λ t Tm18 var18 lam18 app tt pair fst snd left right case zero suc rec =>
     lam18 (t Tm18 var18 lam18 app tt pair fst snd left right case zero suc rec)

def app18 : ∀ {Γ A B} , Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B
 := λ t u Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec =>
     app18 (t Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec)
         (u Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec)

def tt18 : ∀ {Γ} , Tm18 Γ top18
 := λ Tm18 var18 lam18 app18 tt18 pair fst snd left right case zero suc rec => tt18

def pair18 : ∀ {Γ A B} , Tm18 Γ A → Tm18 Γ B → Tm18 Γ (prod18 A B)
 := λ t u Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec =>
     pair18 (t Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec)
          (u Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec)

def fst18 : ∀ {Γ A B} , Tm18 Γ (prod18 A B) → Tm18 Γ A
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd left right case zero suc rec =>
     fst18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd left right case zero suc rec)

def snd18 : ∀ {Γ A B} , Tm18 Γ (prod18 A B) → Tm18 Γ B
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left right case zero suc rec =>
     snd18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left right case zero suc rec)

def left18 : ∀ {Γ A B} , Tm18 Γ A → Tm18 Γ (sum18 A B)
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right case zero suc rec =>
     left18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right case zero suc rec)

def right18 : ∀ {Γ A B} , Tm18 Γ B → Tm18 Γ (sum18 A B)
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case zero suc rec =>
     right18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case zero suc rec)

def case18 : ∀ {Γ A B C} , Tm18 Γ (sum18 A B) → Tm18 Γ (arr18 A C) → Tm18 Γ (arr18 B C) → Tm18 Γ C
 := λ t u v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec =>
     case18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)
          (u Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)
          (v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)

def zero18  : ∀ {Γ} , Tm18 Γ nat18
 := λ Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc rec => zero18

def suc18 : ∀ {Γ} , Tm18 Γ nat18 → Tm18 Γ nat18
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec =>
   suc18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec)

def rec18 : ∀ {Γ A} , Tm18 Γ nat18 → Tm18 Γ (arr18 nat18 (arr18 A A)) → Tm18 Γ A → Tm18 Γ A
 := λ t u v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18 =>
     rec18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)
         (u Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)
         (v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)

def v018 : ∀ {Γ A}, Tm18 (snoc18 Γ A) A
 := var18 vz18

def v118 : ∀ {Γ A B}, Tm18 (snoc18 (snoc18 Γ A) B) A
 := var18 (vs18 vz18)

def v218 : ∀ {Γ A B C}, Tm18 (snoc18 (snoc18 (snoc18 Γ A) B) C) A
 := var18 (vs18 (vs18 vz18))

def v318 : ∀ {Γ A B C D}, Tm18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) A
 := var18 (vs18 (vs18 (vs18 vz18)))

def tbool18 : Ty18
 := sum18 top18 top18

def ttrue18 : ∀ {Γ}, Tm18 Γ tbool18
 := left18 tt18

def tfalse18 : ∀ {Γ}, Tm18 Γ tbool18
 := right18 tt18

def ifthenelse18 : ∀ {Γ A}, Tm18 Γ (arr18 tbool18 (arr18 A (arr18 A A)))
 := lam18 (lam18 (lam18 (case18 v218 (lam18 v218) (lam18 v118))))

def times418 : ∀ {Γ A}, Tm18 Γ (arr18 (arr18 A A) (arr18 A A))
  := lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018)))))

def add18 : ∀ {Γ}, Tm18 Γ (arr18 nat18 (arr18 nat18 nat18))
 := lam18 (rec18 v018
      (lam18 (lam18 (lam18 (suc18 (app18 v118 v018)))))
      (lam18 v018))

def mul18 : ∀ {Γ}, Tm18 Γ (arr18 nat18 (arr18 nat18 nat18))
 := lam18 (rec18 v018
     (lam18 (lam18 (lam18 (app18 (app18 add18 (app18 v118 v018)) v018))))
     (lam18 zero18))

def fact18 : ∀ {Γ}, Tm18 Γ (arr18 nat18 nat18)
 := lam18 (rec18 v018 (lam18 (lam18 (app18 (app18 mul18 (suc18 v118)) v018)))
        (suc18 zero18))
def Ty19 : Type 1
 := ∀ (Ty19           : Type)
      (nat top bot  : Ty19)
      (arr prod sum : Ty19 → Ty19 → Ty19)
    , Ty19

def nat19 : Ty19 := λ _ nat19 _ _ _ _ _ => nat19
def top19 : Ty19 := λ _ _ top19 _ _ _ _ => top19
def bot19 : Ty19 := λ _ _ _ bot19 _ _ _ => bot19

def arr19 : Ty19 → Ty19 → Ty19
 := λ A B Ty19 nat19 top19 bot19 arr19 prod sum =>
     arr19 (A Ty19 nat19 top19 bot19 arr19 prod sum) (B Ty19 nat19 top19 bot19 arr19 prod sum)

def prod19 : Ty19 → Ty19 → Ty19
 := λ A B Ty19 nat19 top19 bot19 arr19 prod19 sum =>
     prod19 (A Ty19 nat19 top19 bot19 arr19 prod19 sum) (B Ty19 nat19 top19 bot19 arr19 prod19 sum)

def sum19 : Ty19 → Ty19 → Ty19
 := λ A B Ty19 nat19 top19 bot19 arr19 prod19 sum19 =>
     sum19 (A Ty19 nat19 top19 bot19 arr19 prod19 sum19) (B Ty19 nat19 top19 bot19 arr19 prod19 sum19)

def Con19 : Type 1
 := ∀ (Con19  : Type)
      (nil  : Con19)
      (snoc : Con19 → Ty19 → Con19)
    , Con19

def nil19 : Con19
 := λ Con19 nil19 snoc => nil19

def snoc19 : Con19 → Ty19 → Con19
 := λ Γ A Con19 nil19 snoc19 => snoc19 (Γ Con19 nil19 snoc19) A

def Var19 : Con19 → Ty19 → Type 1
 := λ Γ A =>
   ∀ (Var19 : Con19 → Ty19 → Type)
     (vz  : ∀{Γ A}, Var19 (snoc19 Γ A) A)
     (vs  : ∀{Γ B A}, Var19 Γ A → Var19 (snoc19 Γ B) A)
   , Var19 Γ A

def vz19 : ∀ {Γ A}, Var19 (snoc19 Γ A) A
 := λ Var19 vz19 vs => vz19

def vs19 : ∀ {Γ B A}, Var19 Γ A → Var19 (snoc19 Γ B) A
 := λ x Var19 vz19 vs19 => vs19 (x Var19 vz19 vs19)

def Tm19 : Con19 → Ty19 → Type 1
 := λ Γ A =>
   ∀ (Tm19  : Con19 → Ty19 → Type)
     (var : ∀ {Γ A}, Var19 Γ A → Tm19 Γ A)
     (lam : ∀ {Γ A B}, (Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B)))
     (app   : ∀ {Γ A B}   , Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B)
     (tt    : ∀ {Γ}       , Tm19 Γ top19)
     (pair  : ∀ {Γ A B}   , Tm19 Γ A → Tm19 Γ B → Tm19 Γ (prod19 A B))
     (fst   : ∀ {Γ A B}   , Tm19 Γ (prod19 A B) → Tm19 Γ A)
     (snd   : ∀ {Γ A B}   , Tm19 Γ (prod19 A B) → Tm19 Γ B)
     (left  : ∀ {Γ A B}   , Tm19 Γ A → Tm19 Γ (sum19 A B))
     (right : ∀ {Γ A B}   , Tm19 Γ B → Tm19 Γ (sum19 A B))
     (case  : ∀ {Γ A B C} , Tm19 Γ (sum19 A B) → Tm19 Γ (arr19 A C) → Tm19 Γ (arr19 B C) → Tm19 Γ C)
     (zero  : ∀ {Γ}       , Tm19 Γ nat19)
     (suc   : ∀ {Γ}       , Tm19 Γ nat19 → Tm19 Γ nat19)
     (rec   : ∀ {Γ A}     , Tm19 Γ nat19 → Tm19 Γ (arr19 nat19 (arr19 A A)) → Tm19 Γ A → Tm19 Γ A)
   , Tm19 Γ A

def var19 : ∀ {Γ A}, Var19 Γ A → Tm19 Γ A
 := λ x Tm19 var19 lam app tt pair fst snd left right case zero suc rec =>
     var19 x

def lam19 : ∀ {Γ A B} , Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B)
 := λ t Tm19 var19 lam19 app tt pair fst snd left right case zero suc rec =>
     lam19 (t Tm19 var19 lam19 app tt pair fst snd left right case zero suc rec)

def app19 : ∀ {Γ A B} , Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B
 := λ t u Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec =>
     app19 (t Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec)
         (u Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec)

def tt19 : ∀ {Γ} , Tm19 Γ top19
 := λ Tm19 var19 lam19 app19 tt19 pair fst snd left right case zero suc rec => tt19

def pair19 : ∀ {Γ A B} , Tm19 Γ A → Tm19 Γ B → Tm19 Γ (prod19 A B)
 := λ t u Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec =>
     pair19 (t Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec)
          (u Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec)

def fst19 : ∀ {Γ A B} , Tm19 Γ (prod19 A B) → Tm19 Γ A
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd left right case zero suc rec =>
     fst19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd left right case zero suc rec)

def snd19 : ∀ {Γ A B} , Tm19 Γ (prod19 A B) → Tm19 Γ B
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left right case zero suc rec =>
     snd19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left right case zero suc rec)

def left19 : ∀ {Γ A B} , Tm19 Γ A → Tm19 Γ (sum19 A B)
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right case zero suc rec =>
     left19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right case zero suc rec)

def right19 : ∀ {Γ A B} , Tm19 Γ B → Tm19 Γ (sum19 A B)
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case zero suc rec =>
     right19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case zero suc rec)

def case19 : ∀ {Γ A B C} , Tm19 Γ (sum19 A B) → Tm19 Γ (arr19 A C) → Tm19 Γ (arr19 B C) → Tm19 Γ C
 := λ t u v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec =>
     case19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)
          (u Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)
          (v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)

def zero19  : ∀ {Γ} , Tm19 Γ nat19
 := λ Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc rec => zero19

def suc19 : ∀ {Γ} , Tm19 Γ nat19 → Tm19 Γ nat19
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec =>
   suc19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec)

def rec19 : ∀ {Γ A} , Tm19 Γ nat19 → Tm19 Γ (arr19 nat19 (arr19 A A)) → Tm19 Γ A → Tm19 Γ A
 := λ t u v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19 =>
     rec19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)
         (u Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)
         (v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)

def v019 : ∀ {Γ A}, Tm19 (snoc19 Γ A) A
 := var19 vz19

def v119 : ∀ {Γ A B}, Tm19 (snoc19 (snoc19 Γ A) B) A
 := var19 (vs19 vz19)

def v219 : ∀ {Γ A B C}, Tm19 (snoc19 (snoc19 (snoc19 Γ A) B) C) A
 := var19 (vs19 (vs19 vz19))

def v319 : ∀ {Γ A B C D}, Tm19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) A
 := var19 (vs19 (vs19 (vs19 vz19)))

def tbool19 : Ty19
 := sum19 top19 top19

def ttrue19 : ∀ {Γ}, Tm19 Γ tbool19
 := left19 tt19

def tfalse19 : ∀ {Γ}, Tm19 Γ tbool19
 := right19 tt19

def ifthenelse19 : ∀ {Γ A}, Tm19 Γ (arr19 tbool19 (arr19 A (arr19 A A)))
 := lam19 (lam19 (lam19 (case19 v219 (lam19 v219) (lam19 v119))))

def times419 : ∀ {Γ A}, Tm19 Γ (arr19 (arr19 A A) (arr19 A A))
  := lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019)))))

def add19 : ∀ {Γ}, Tm19 Γ (arr19 nat19 (arr19 nat19 nat19))
 := lam19 (rec19 v019
      (lam19 (lam19 (lam19 (suc19 (app19 v119 v019)))))
      (lam19 v019))

def mul19 : ∀ {Γ}, Tm19 Γ (arr19 nat19 (arr19 nat19 nat19))
 := lam19 (rec19 v019
     (lam19 (lam19 (lam19 (app19 (app19 add19 (app19 v119 v019)) v019))))
     (lam19 zero19))

def fact19 : ∀ {Γ}, Tm19 Γ (arr19 nat19 nat19)
 := lam19 (rec19 v019 (lam19 (lam19 (app19 (app19 mul19 (suc19 v119)) v019)))
        (suc19 zero19))
def Ty20 : Type 1
 := ∀ (Ty20           : Type)
      (nat top bot  : Ty20)
      (arr prod sum : Ty20 → Ty20 → Ty20)
    , Ty20

def nat20 : Ty20 := λ _ nat20 _ _ _ _ _ => nat20
def top20 : Ty20 := λ _ _ top20 _ _ _ _ => top20
def bot20 : Ty20 := λ _ _ _ bot20 _ _ _ => bot20

def arr20 : Ty20 → Ty20 → Ty20
 := λ A B Ty20 nat20 top20 bot20 arr20 prod sum =>
     arr20 (A Ty20 nat20 top20 bot20 arr20 prod sum) (B Ty20 nat20 top20 bot20 arr20 prod sum)

def prod20 : Ty20 → Ty20 → Ty20
 := λ A B Ty20 nat20 top20 bot20 arr20 prod20 sum =>
     prod20 (A Ty20 nat20 top20 bot20 arr20 prod20 sum) (B Ty20 nat20 top20 bot20 arr20 prod20 sum)

def sum20 : Ty20 → Ty20 → Ty20
 := λ A B Ty20 nat20 top20 bot20 arr20 prod20 sum20 =>
     sum20 (A Ty20 nat20 top20 bot20 arr20 prod20 sum20) (B Ty20 nat20 top20 bot20 arr20 prod20 sum20)

def Con20 : Type 1
 := ∀ (Con20  : Type)
      (nil  : Con20)
      (snoc : Con20 → Ty20 → Con20)
    , Con20

def nil20 : Con20
 := λ Con20 nil20 snoc => nil20

def snoc20 : Con20 → Ty20 → Con20
 := λ Γ A Con20 nil20 snoc20 => snoc20 (Γ Con20 nil20 snoc20) A

def Var20 : Con20 → Ty20 → Type 1
 := λ Γ A =>
   ∀ (Var20 : Con20 → Ty20 → Type)
     (vz  : ∀{Γ A}, Var20 (snoc20 Γ A) A)
     (vs  : ∀{Γ B A}, Var20 Γ A → Var20 (snoc20 Γ B) A)
   , Var20 Γ A

def vz20 : ∀ {Γ A}, Var20 (snoc20 Γ A) A
 := λ Var20 vz20 vs => vz20

def vs20 : ∀ {Γ B A}, Var20 Γ A → Var20 (snoc20 Γ B) A
 := λ x Var20 vz20 vs20 => vs20 (x Var20 vz20 vs20)

def Tm20 : Con20 → Ty20 → Type 1
 := λ Γ A =>
   ∀ (Tm20  : Con20 → Ty20 → Type)
     (var : ∀ {Γ A}, Var20 Γ A → Tm20 Γ A)
     (lam : ∀ {Γ A B}, (Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B)))
     (app   : ∀ {Γ A B}   , Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B)
     (tt    : ∀ {Γ}       , Tm20 Γ top20)
     (pair  : ∀ {Γ A B}   , Tm20 Γ A → Tm20 Γ B → Tm20 Γ (prod20 A B))
     (fst   : ∀ {Γ A B}   , Tm20 Γ (prod20 A B) → Tm20 Γ A)
     (snd   : ∀ {Γ A B}   , Tm20 Γ (prod20 A B) → Tm20 Γ B)
     (left  : ∀ {Γ A B}   , Tm20 Γ A → Tm20 Γ (sum20 A B))
     (right : ∀ {Γ A B}   , Tm20 Γ B → Tm20 Γ (sum20 A B))
     (case  : ∀ {Γ A B C} , Tm20 Γ (sum20 A B) → Tm20 Γ (arr20 A C) → Tm20 Γ (arr20 B C) → Tm20 Γ C)
     (zero  : ∀ {Γ}       , Tm20 Γ nat20)
     (suc   : ∀ {Γ}       , Tm20 Γ nat20 → Tm20 Γ nat20)
     (rec   : ∀ {Γ A}     , Tm20 Γ nat20 → Tm20 Γ (arr20 nat20 (arr20 A A)) → Tm20 Γ A → Tm20 Γ A)
   , Tm20 Γ A

def var20 : ∀ {Γ A}, Var20 Γ A → Tm20 Γ A
 := λ x Tm20 var20 lam app tt pair fst snd left right case zero suc rec =>
     var20 x

def lam20 : ∀ {Γ A B} , Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B)
 := λ t Tm20 var20 lam20 app tt pair fst snd left right case zero suc rec =>
     lam20 (t Tm20 var20 lam20 app tt pair fst snd left right case zero suc rec)

def app20 : ∀ {Γ A B} , Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B
 := λ t u Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec =>
     app20 (t Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec)
         (u Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec)

def tt20 : ∀ {Γ} , Tm20 Γ top20
 := λ Tm20 var20 lam20 app20 tt20 pair fst snd left right case zero suc rec => tt20

def pair20 : ∀ {Γ A B} , Tm20 Γ A → Tm20 Γ B → Tm20 Γ (prod20 A B)
 := λ t u Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec =>
     pair20 (t Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec)
          (u Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec)

def fst20 : ∀ {Γ A B} , Tm20 Γ (prod20 A B) → Tm20 Γ A
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd left right case zero suc rec =>
     fst20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd left right case zero suc rec)

def snd20 : ∀ {Γ A B} , Tm20 Γ (prod20 A B) → Tm20 Γ B
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left right case zero suc rec =>
     snd20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left right case zero suc rec)

def left20 : ∀ {Γ A B} , Tm20 Γ A → Tm20 Γ (sum20 A B)
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right case zero suc rec =>
     left20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right case zero suc rec)

def right20 : ∀ {Γ A B} , Tm20 Γ B → Tm20 Γ (sum20 A B)
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case zero suc rec =>
     right20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case zero suc rec)

def case20 : ∀ {Γ A B C} , Tm20 Γ (sum20 A B) → Tm20 Γ (arr20 A C) → Tm20 Γ (arr20 B C) → Tm20 Γ C
 := λ t u v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec =>
     case20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)
          (u Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)
          (v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)

def zero20  : ∀ {Γ} , Tm20 Γ nat20
 := λ Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc rec => zero20

def suc20 : ∀ {Γ} , Tm20 Γ nat20 → Tm20 Γ nat20
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec =>
   suc20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec)

def rec20 : ∀ {Γ A} , Tm20 Γ nat20 → Tm20 Γ (arr20 nat20 (arr20 A A)) → Tm20 Γ A → Tm20 Γ A
 := λ t u v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20 =>
     rec20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)
         (u Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)
         (v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)

def v020 : ∀ {Γ A}, Tm20 (snoc20 Γ A) A
 := var20 vz20

def v120 : ∀ {Γ A B}, Tm20 (snoc20 (snoc20 Γ A) B) A
 := var20 (vs20 vz20)

def v220 : ∀ {Γ A B C}, Tm20 (snoc20 (snoc20 (snoc20 Γ A) B) C) A
 := var20 (vs20 (vs20 vz20))

def v320 : ∀ {Γ A B C D}, Tm20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) A
 := var20 (vs20 (vs20 (vs20 vz20)))

def tbool20 : Ty20
 := sum20 top20 top20

def ttrue20 : ∀ {Γ}, Tm20 Γ tbool20
 := left20 tt20

def tfalse20 : ∀ {Γ}, Tm20 Γ tbool20
 := right20 tt20

def ifthenelse20 : ∀ {Γ A}, Tm20 Γ (arr20 tbool20 (arr20 A (arr20 A A)))
 := lam20 (lam20 (lam20 (case20 v220 (lam20 v220) (lam20 v120))))

def times420 : ∀ {Γ A}, Tm20 Γ (arr20 (arr20 A A) (arr20 A A))
  := lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020)))))

def add20 : ∀ {Γ}, Tm20 Γ (arr20 nat20 (arr20 nat20 nat20))
 := lam20 (rec20 v020
      (lam20 (lam20 (lam20 (suc20 (app20 v120 v020)))))
      (lam20 v020))

def mul20 : ∀ {Γ}, Tm20 Γ (arr20 nat20 (arr20 nat20 nat20))
 := lam20 (rec20 v020
     (lam20 (lam20 (lam20 (app20 (app20 add20 (app20 v120 v020)) v020))))
     (lam20 zero20))

def fact20 : ∀ {Γ}, Tm20 Γ (arr20 nat20 nat20)
 := lam20 (rec20 v020 (lam20 (lam20 (app20 (app20 mul20 (suc20 v120)) v020)))
        (suc20 zero20))
def Ty21 : Type 1
 := ∀ (Ty21           : Type)
      (nat top bot  : Ty21)
      (arr prod sum : Ty21 → Ty21 → Ty21)
    , Ty21

def nat21 : Ty21 := λ _ nat21 _ _ _ _ _ => nat21
def top21 : Ty21 := λ _ _ top21 _ _ _ _ => top21
def bot21 : Ty21 := λ _ _ _ bot21 _ _ _ => bot21

def arr21 : Ty21 → Ty21 → Ty21
 := λ A B Ty21 nat21 top21 bot21 arr21 prod sum =>
     arr21 (A Ty21 nat21 top21 bot21 arr21 prod sum) (B Ty21 nat21 top21 bot21 arr21 prod sum)

def prod21 : Ty21 → Ty21 → Ty21
 := λ A B Ty21 nat21 top21 bot21 arr21 prod21 sum =>
     prod21 (A Ty21 nat21 top21 bot21 arr21 prod21 sum) (B Ty21 nat21 top21 bot21 arr21 prod21 sum)

def sum21 : Ty21 → Ty21 → Ty21
 := λ A B Ty21 nat21 top21 bot21 arr21 prod21 sum21 =>
     sum21 (A Ty21 nat21 top21 bot21 arr21 prod21 sum21) (B Ty21 nat21 top21 bot21 arr21 prod21 sum21)

def Con21 : Type 1
 := ∀ (Con21  : Type)
      (nil  : Con21)
      (snoc : Con21 → Ty21 → Con21)
    , Con21

def nil21 : Con21
 := λ Con21 nil21 snoc => nil21

def snoc21 : Con21 → Ty21 → Con21
 := λ Γ A Con21 nil21 snoc21 => snoc21 (Γ Con21 nil21 snoc21) A

def Var21 : Con21 → Ty21 → Type 1
 := λ Γ A =>
   ∀ (Var21 : Con21 → Ty21 → Type)
     (vz  : ∀{Γ A}, Var21 (snoc21 Γ A) A)
     (vs  : ∀{Γ B A}, Var21 Γ A → Var21 (snoc21 Γ B) A)
   , Var21 Γ A

def vz21 : ∀ {Γ A}, Var21 (snoc21 Γ A) A
 := λ Var21 vz21 vs => vz21

def vs21 : ∀ {Γ B A}, Var21 Γ A → Var21 (snoc21 Γ B) A
 := λ x Var21 vz21 vs21 => vs21 (x Var21 vz21 vs21)

def Tm21 : Con21 → Ty21 → Type 1
 := λ Γ A =>
   ∀ (Tm21  : Con21 → Ty21 → Type)
     (var : ∀ {Γ A}, Var21 Γ A → Tm21 Γ A)
     (lam : ∀ {Γ A B}, (Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B)))
     (app   : ∀ {Γ A B}   , Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B)
     (tt    : ∀ {Γ}       , Tm21 Γ top21)
     (pair  : ∀ {Γ A B}   , Tm21 Γ A → Tm21 Γ B → Tm21 Γ (prod21 A B))
     (fst   : ∀ {Γ A B}   , Tm21 Γ (prod21 A B) → Tm21 Γ A)
     (snd   : ∀ {Γ A B}   , Tm21 Γ (prod21 A B) → Tm21 Γ B)
     (left  : ∀ {Γ A B}   , Tm21 Γ A → Tm21 Γ (sum21 A B))
     (right : ∀ {Γ A B}   , Tm21 Γ B → Tm21 Γ (sum21 A B))
     (case  : ∀ {Γ A B C} , Tm21 Γ (sum21 A B) → Tm21 Γ (arr21 A C) → Tm21 Γ (arr21 B C) → Tm21 Γ C)
     (zero  : ∀ {Γ}       , Tm21 Γ nat21)
     (suc   : ∀ {Γ}       , Tm21 Γ nat21 → Tm21 Γ nat21)
     (rec   : ∀ {Γ A}     , Tm21 Γ nat21 → Tm21 Γ (arr21 nat21 (arr21 A A)) → Tm21 Γ A → Tm21 Γ A)
   , Tm21 Γ A

def var21 : ∀ {Γ A}, Var21 Γ A → Tm21 Γ A
 := λ x Tm21 var21 lam app tt pair fst snd left right case zero suc rec =>
     var21 x

def lam21 : ∀ {Γ A B} , Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B)
 := λ t Tm21 var21 lam21 app tt pair fst snd left right case zero suc rec =>
     lam21 (t Tm21 var21 lam21 app tt pair fst snd left right case zero suc rec)

def app21 : ∀ {Γ A B} , Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B
 := λ t u Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec =>
     app21 (t Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec)
         (u Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec)

def tt21 : ∀ {Γ} , Tm21 Γ top21
 := λ Tm21 var21 lam21 app21 tt21 pair fst snd left right case zero suc rec => tt21

def pair21 : ∀ {Γ A B} , Tm21 Γ A → Tm21 Γ B → Tm21 Γ (prod21 A B)
 := λ t u Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec =>
     pair21 (t Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec)
          (u Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec)

def fst21 : ∀ {Γ A B} , Tm21 Γ (prod21 A B) → Tm21 Γ A
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd left right case zero suc rec =>
     fst21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd left right case zero suc rec)

def snd21 : ∀ {Γ A B} , Tm21 Γ (prod21 A B) → Tm21 Γ B
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left right case zero suc rec =>
     snd21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left right case zero suc rec)

def left21 : ∀ {Γ A B} , Tm21 Γ A → Tm21 Γ (sum21 A B)
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right case zero suc rec =>
     left21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right case zero suc rec)

def right21 : ∀ {Γ A B} , Tm21 Γ B → Tm21 Γ (sum21 A B)
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case zero suc rec =>
     right21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case zero suc rec)

def case21 : ∀ {Γ A B C} , Tm21 Γ (sum21 A B) → Tm21 Γ (arr21 A C) → Tm21 Γ (arr21 B C) → Tm21 Γ C
 := λ t u v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec =>
     case21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)
          (u Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)
          (v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)

def zero21  : ∀ {Γ} , Tm21 Γ nat21
 := λ Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc rec => zero21

def suc21 : ∀ {Γ} , Tm21 Γ nat21 → Tm21 Γ nat21
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec =>
   suc21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec)

def rec21 : ∀ {Γ A} , Tm21 Γ nat21 → Tm21 Γ (arr21 nat21 (arr21 A A)) → Tm21 Γ A → Tm21 Γ A
 := λ t u v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21 =>
     rec21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)
         (u Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)
         (v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)

def v021 : ∀ {Γ A}, Tm21 (snoc21 Γ A) A
 := var21 vz21

def v121 : ∀ {Γ A B}, Tm21 (snoc21 (snoc21 Γ A) B) A
 := var21 (vs21 vz21)

def v221 : ∀ {Γ A B C}, Tm21 (snoc21 (snoc21 (snoc21 Γ A) B) C) A
 := var21 (vs21 (vs21 vz21))

def v321 : ∀ {Γ A B C D}, Tm21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) A
 := var21 (vs21 (vs21 (vs21 vz21)))

def tbool21 : Ty21
 := sum21 top21 top21

def ttrue21 : ∀ {Γ}, Tm21 Γ tbool21
 := left21 tt21

def tfalse21 : ∀ {Γ}, Tm21 Γ tbool21
 := right21 tt21

def ifthenelse21 : ∀ {Γ A}, Tm21 Γ (arr21 tbool21 (arr21 A (arr21 A A)))
 := lam21 (lam21 (lam21 (case21 v221 (lam21 v221) (lam21 v121))))

def times421 : ∀ {Γ A}, Tm21 Γ (arr21 (arr21 A A) (arr21 A A))
  := lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021)))))

def add21 : ∀ {Γ}, Tm21 Γ (arr21 nat21 (arr21 nat21 nat21))
 := lam21 (rec21 v021
      (lam21 (lam21 (lam21 (suc21 (app21 v121 v021)))))
      (lam21 v021))

def mul21 : ∀ {Γ}, Tm21 Γ (arr21 nat21 (arr21 nat21 nat21))
 := lam21 (rec21 v021
     (lam21 (lam21 (lam21 (app21 (app21 add21 (app21 v121 v021)) v021))))
     (lam21 zero21))

def fact21 : ∀ {Γ}, Tm21 Γ (arr21 nat21 nat21)
 := lam21 (rec21 v021 (lam21 (lam21 (app21 (app21 mul21 (suc21 v121)) v021)))
        (suc21 zero21))
def Ty22 : Type 1
 := ∀ (Ty22           : Type)
      (nat top bot  : Ty22)
      (arr prod sum : Ty22 → Ty22 → Ty22)
    , Ty22

def nat22 : Ty22 := λ _ nat22 _ _ _ _ _ => nat22
def top22 : Ty22 := λ _ _ top22 _ _ _ _ => top22
def bot22 : Ty22 := λ _ _ _ bot22 _ _ _ => bot22

def arr22 : Ty22 → Ty22 → Ty22
 := λ A B Ty22 nat22 top22 bot22 arr22 prod sum =>
     arr22 (A Ty22 nat22 top22 bot22 arr22 prod sum) (B Ty22 nat22 top22 bot22 arr22 prod sum)

def prod22 : Ty22 → Ty22 → Ty22
 := λ A B Ty22 nat22 top22 bot22 arr22 prod22 sum =>
     prod22 (A Ty22 nat22 top22 bot22 arr22 prod22 sum) (B Ty22 nat22 top22 bot22 arr22 prod22 sum)

def sum22 : Ty22 → Ty22 → Ty22
 := λ A B Ty22 nat22 top22 bot22 arr22 prod22 sum22 =>
     sum22 (A Ty22 nat22 top22 bot22 arr22 prod22 sum22) (B Ty22 nat22 top22 bot22 arr22 prod22 sum22)

def Con22 : Type 1
 := ∀ (Con22  : Type)
      (nil  : Con22)
      (snoc : Con22 → Ty22 → Con22)
    , Con22

def nil22 : Con22
 := λ Con22 nil22 snoc => nil22

def snoc22 : Con22 → Ty22 → Con22
 := λ Γ A Con22 nil22 snoc22 => snoc22 (Γ Con22 nil22 snoc22) A

def Var22 : Con22 → Ty22 → Type 1
 := λ Γ A =>
   ∀ (Var22 : Con22 → Ty22 → Type)
     (vz  : ∀{Γ A}, Var22 (snoc22 Γ A) A)
     (vs  : ∀{Γ B A}, Var22 Γ A → Var22 (snoc22 Γ B) A)
   , Var22 Γ A

def vz22 : ∀ {Γ A}, Var22 (snoc22 Γ A) A
 := λ Var22 vz22 vs => vz22

def vs22 : ∀ {Γ B A}, Var22 Γ A → Var22 (snoc22 Γ B) A
 := λ x Var22 vz22 vs22 => vs22 (x Var22 vz22 vs22)

def Tm22 : Con22 → Ty22 → Type 1
 := λ Γ A =>
   ∀ (Tm22  : Con22 → Ty22 → Type)
     (var : ∀ {Γ A}, Var22 Γ A → Tm22 Γ A)
     (lam : ∀ {Γ A B}, (Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B)))
     (app   : ∀ {Γ A B}   , Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B)
     (tt    : ∀ {Γ}       , Tm22 Γ top22)
     (pair  : ∀ {Γ A B}   , Tm22 Γ A → Tm22 Γ B → Tm22 Γ (prod22 A B))
     (fst   : ∀ {Γ A B}   , Tm22 Γ (prod22 A B) → Tm22 Γ A)
     (snd   : ∀ {Γ A B}   , Tm22 Γ (prod22 A B) → Tm22 Γ B)
     (left  : ∀ {Γ A B}   , Tm22 Γ A → Tm22 Γ (sum22 A B))
     (right : ∀ {Γ A B}   , Tm22 Γ B → Tm22 Γ (sum22 A B))
     (case  : ∀ {Γ A B C} , Tm22 Γ (sum22 A B) → Tm22 Γ (arr22 A C) → Tm22 Γ (arr22 B C) → Tm22 Γ C)
     (zero  : ∀ {Γ}       , Tm22 Γ nat22)
     (suc   : ∀ {Γ}       , Tm22 Γ nat22 → Tm22 Γ nat22)
     (rec   : ∀ {Γ A}     , Tm22 Γ nat22 → Tm22 Γ (arr22 nat22 (arr22 A A)) → Tm22 Γ A → Tm22 Γ A)
   , Tm22 Γ A

def var22 : ∀ {Γ A}, Var22 Γ A → Tm22 Γ A
 := λ x Tm22 var22 lam app tt pair fst snd left right case zero suc rec =>
     var22 x

def lam22 : ∀ {Γ A B} , Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B)
 := λ t Tm22 var22 lam22 app tt pair fst snd left right case zero suc rec =>
     lam22 (t Tm22 var22 lam22 app tt pair fst snd left right case zero suc rec)

def app22 : ∀ {Γ A B} , Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B
 := λ t u Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec =>
     app22 (t Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec)
         (u Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec)

def tt22 : ∀ {Γ} , Tm22 Γ top22
 := λ Tm22 var22 lam22 app22 tt22 pair fst snd left right case zero suc rec => tt22

def pair22 : ∀ {Γ A B} , Tm22 Γ A → Tm22 Γ B → Tm22 Γ (prod22 A B)
 := λ t u Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec =>
     pair22 (t Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec)
          (u Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec)

def fst22 : ∀ {Γ A B} , Tm22 Γ (prod22 A B) → Tm22 Γ A
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd left right case zero suc rec =>
     fst22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd left right case zero suc rec)

def snd22 : ∀ {Γ A B} , Tm22 Γ (prod22 A B) → Tm22 Γ B
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left right case zero suc rec =>
     snd22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left right case zero suc rec)

def left22 : ∀ {Γ A B} , Tm22 Γ A → Tm22 Γ (sum22 A B)
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right case zero suc rec =>
     left22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right case zero suc rec)

def right22 : ∀ {Γ A B} , Tm22 Γ B → Tm22 Γ (sum22 A B)
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case zero suc rec =>
     right22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case zero suc rec)

def case22 : ∀ {Γ A B C} , Tm22 Γ (sum22 A B) → Tm22 Γ (arr22 A C) → Tm22 Γ (arr22 B C) → Tm22 Γ C
 := λ t u v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec =>
     case22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)
          (u Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)
          (v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)

def zero22  : ∀ {Γ} , Tm22 Γ nat22
 := λ Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc rec => zero22

def suc22 : ∀ {Γ} , Tm22 Γ nat22 → Tm22 Γ nat22
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec =>
   suc22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec)

def rec22 : ∀ {Γ A} , Tm22 Γ nat22 → Tm22 Γ (arr22 nat22 (arr22 A A)) → Tm22 Γ A → Tm22 Γ A
 := λ t u v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22 =>
     rec22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)
         (u Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)
         (v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)

def v022 : ∀ {Γ A}, Tm22 (snoc22 Γ A) A
 := var22 vz22

def v122 : ∀ {Γ A B}, Tm22 (snoc22 (snoc22 Γ A) B) A
 := var22 (vs22 vz22)

def v222 : ∀ {Γ A B C}, Tm22 (snoc22 (snoc22 (snoc22 Γ A) B) C) A
 := var22 (vs22 (vs22 vz22))

def v322 : ∀ {Γ A B C D}, Tm22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) A
 := var22 (vs22 (vs22 (vs22 vz22)))

def tbool22 : Ty22
 := sum22 top22 top22

def ttrue22 : ∀ {Γ}, Tm22 Γ tbool22
 := left22 tt22

def tfalse22 : ∀ {Γ}, Tm22 Γ tbool22
 := right22 tt22

def ifthenelse22 : ∀ {Γ A}, Tm22 Γ (arr22 tbool22 (arr22 A (arr22 A A)))
 := lam22 (lam22 (lam22 (case22 v222 (lam22 v222) (lam22 v122))))

def times422 : ∀ {Γ A}, Tm22 Γ (arr22 (arr22 A A) (arr22 A A))
  := lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022)))))

def add22 : ∀ {Γ}, Tm22 Γ (arr22 nat22 (arr22 nat22 nat22))
 := lam22 (rec22 v022
      (lam22 (lam22 (lam22 (suc22 (app22 v122 v022)))))
      (lam22 v022))

def mul22 : ∀ {Γ}, Tm22 Γ (arr22 nat22 (arr22 nat22 nat22))
 := lam22 (rec22 v022
     (lam22 (lam22 (lam22 (app22 (app22 add22 (app22 v122 v022)) v022))))
     (lam22 zero22))

def fact22 : ∀ {Γ}, Tm22 Γ (arr22 nat22 nat22)
 := lam22 (rec22 v022 (lam22 (lam22 (app22 (app22 mul22 (suc22 v122)) v022)))
        (suc22 zero22))
def Ty23 : Type 1
 := ∀ (Ty23           : Type)
      (nat top bot  : Ty23)
      (arr prod sum : Ty23 → Ty23 → Ty23)
    , Ty23

def nat23 : Ty23 := λ _ nat23 _ _ _ _ _ => nat23
def top23 : Ty23 := λ _ _ top23 _ _ _ _ => top23
def bot23 : Ty23 := λ _ _ _ bot23 _ _ _ => bot23

def arr23 : Ty23 → Ty23 → Ty23
 := λ A B Ty23 nat23 top23 bot23 arr23 prod sum =>
     arr23 (A Ty23 nat23 top23 bot23 arr23 prod sum) (B Ty23 nat23 top23 bot23 arr23 prod sum)

def prod23 : Ty23 → Ty23 → Ty23
 := λ A B Ty23 nat23 top23 bot23 arr23 prod23 sum =>
     prod23 (A Ty23 nat23 top23 bot23 arr23 prod23 sum) (B Ty23 nat23 top23 bot23 arr23 prod23 sum)

def sum23 : Ty23 → Ty23 → Ty23
 := λ A B Ty23 nat23 top23 bot23 arr23 prod23 sum23 =>
     sum23 (A Ty23 nat23 top23 bot23 arr23 prod23 sum23) (B Ty23 nat23 top23 bot23 arr23 prod23 sum23)

def Con23 : Type 1
 := ∀ (Con23  : Type)
      (nil  : Con23)
      (snoc : Con23 → Ty23 → Con23)
    , Con23

def nil23 : Con23
 := λ Con23 nil23 snoc => nil23

def snoc23 : Con23 → Ty23 → Con23
 := λ Γ A Con23 nil23 snoc23 => snoc23 (Γ Con23 nil23 snoc23) A

def Var23 : Con23 → Ty23 → Type 1
 := λ Γ A =>
   ∀ (Var23 : Con23 → Ty23 → Type)
     (vz  : ∀{Γ A}, Var23 (snoc23 Γ A) A)
     (vs  : ∀{Γ B A}, Var23 Γ A → Var23 (snoc23 Γ B) A)
   , Var23 Γ A

def vz23 : ∀ {Γ A}, Var23 (snoc23 Γ A) A
 := λ Var23 vz23 vs => vz23

def vs23 : ∀ {Γ B A}, Var23 Γ A → Var23 (snoc23 Γ B) A
 := λ x Var23 vz23 vs23 => vs23 (x Var23 vz23 vs23)

def Tm23 : Con23 → Ty23 → Type 1
 := λ Γ A =>
   ∀ (Tm23  : Con23 → Ty23 → Type)
     (var : ∀ {Γ A}, Var23 Γ A → Tm23 Γ A)
     (lam : ∀ {Γ A B}, (Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B)))
     (app   : ∀ {Γ A B}   , Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B)
     (tt    : ∀ {Γ}       , Tm23 Γ top23)
     (pair  : ∀ {Γ A B}   , Tm23 Γ A → Tm23 Γ B → Tm23 Γ (prod23 A B))
     (fst   : ∀ {Γ A B}   , Tm23 Γ (prod23 A B) → Tm23 Γ A)
     (snd   : ∀ {Γ A B}   , Tm23 Γ (prod23 A B) → Tm23 Γ B)
     (left  : ∀ {Γ A B}   , Tm23 Γ A → Tm23 Γ (sum23 A B))
     (right : ∀ {Γ A B}   , Tm23 Γ B → Tm23 Γ (sum23 A B))
     (case  : ∀ {Γ A B C} , Tm23 Γ (sum23 A B) → Tm23 Γ (arr23 A C) → Tm23 Γ (arr23 B C) → Tm23 Γ C)
     (zero  : ∀ {Γ}       , Tm23 Γ nat23)
     (suc   : ∀ {Γ}       , Tm23 Γ nat23 → Tm23 Γ nat23)
     (rec   : ∀ {Γ A}     , Tm23 Γ nat23 → Tm23 Γ (arr23 nat23 (arr23 A A)) → Tm23 Γ A → Tm23 Γ A)
   , Tm23 Γ A

def var23 : ∀ {Γ A}, Var23 Γ A → Tm23 Γ A
 := λ x Tm23 var23 lam app tt pair fst snd left right case zero suc rec =>
     var23 x

def lam23 : ∀ {Γ A B} , Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B)
 := λ t Tm23 var23 lam23 app tt pair fst snd left right case zero suc rec =>
     lam23 (t Tm23 var23 lam23 app tt pair fst snd left right case zero suc rec)

def app23 : ∀ {Γ A B} , Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B
 := λ t u Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec =>
     app23 (t Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec)
         (u Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec)

def tt23 : ∀ {Γ} , Tm23 Γ top23
 := λ Tm23 var23 lam23 app23 tt23 pair fst snd left right case zero suc rec => tt23

def pair23 : ∀ {Γ A B} , Tm23 Γ A → Tm23 Γ B → Tm23 Γ (prod23 A B)
 := λ t u Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec =>
     pair23 (t Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec)
          (u Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec)

def fst23 : ∀ {Γ A B} , Tm23 Γ (prod23 A B) → Tm23 Γ A
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd left right case zero suc rec =>
     fst23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd left right case zero suc rec)

def snd23 : ∀ {Γ A B} , Tm23 Γ (prod23 A B) → Tm23 Γ B
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left right case zero suc rec =>
     snd23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left right case zero suc rec)

def left23 : ∀ {Γ A B} , Tm23 Γ A → Tm23 Γ (sum23 A B)
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right case zero suc rec =>
     left23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right case zero suc rec)

def right23 : ∀ {Γ A B} , Tm23 Γ B → Tm23 Γ (sum23 A B)
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case zero suc rec =>
     right23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case zero suc rec)

def case23 : ∀ {Γ A B C} , Tm23 Γ (sum23 A B) → Tm23 Γ (arr23 A C) → Tm23 Γ (arr23 B C) → Tm23 Γ C
 := λ t u v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec =>
     case23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)
          (u Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)
          (v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)

def zero23  : ∀ {Γ} , Tm23 Γ nat23
 := λ Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc rec => zero23

def suc23 : ∀ {Γ} , Tm23 Γ nat23 → Tm23 Γ nat23
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec =>
   suc23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec)

def rec23 : ∀ {Γ A} , Tm23 Γ nat23 → Tm23 Γ (arr23 nat23 (arr23 A A)) → Tm23 Γ A → Tm23 Γ A
 := λ t u v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23 =>
     rec23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)
         (u Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)
         (v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)

def v023 : ∀ {Γ A}, Tm23 (snoc23 Γ A) A
 := var23 vz23

def v123 : ∀ {Γ A B}, Tm23 (snoc23 (snoc23 Γ A) B) A
 := var23 (vs23 vz23)

def v223 : ∀ {Γ A B C}, Tm23 (snoc23 (snoc23 (snoc23 Γ A) B) C) A
 := var23 (vs23 (vs23 vz23))

def v323 : ∀ {Γ A B C D}, Tm23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) A
 := var23 (vs23 (vs23 (vs23 vz23)))

def tbool23 : Ty23
 := sum23 top23 top23

def ttrue23 : ∀ {Γ}, Tm23 Γ tbool23
 := left23 tt23

def tfalse23 : ∀ {Γ}, Tm23 Γ tbool23
 := right23 tt23

def ifthenelse23 : ∀ {Γ A}, Tm23 Γ (arr23 tbool23 (arr23 A (arr23 A A)))
 := lam23 (lam23 (lam23 (case23 v223 (lam23 v223) (lam23 v123))))

def times423 : ∀ {Γ A}, Tm23 Γ (arr23 (arr23 A A) (arr23 A A))
  := lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023)))))

def add23 : ∀ {Γ}, Tm23 Γ (arr23 nat23 (arr23 nat23 nat23))
 := lam23 (rec23 v023
      (lam23 (lam23 (lam23 (suc23 (app23 v123 v023)))))
      (lam23 v023))

def mul23 : ∀ {Γ}, Tm23 Γ (arr23 nat23 (arr23 nat23 nat23))
 := lam23 (rec23 v023
     (lam23 (lam23 (lam23 (app23 (app23 add23 (app23 v123 v023)) v023))))
     (lam23 zero23))

def fact23 : ∀ {Γ}, Tm23 Γ (arr23 nat23 nat23)
 := lam23 (rec23 v023 (lam23 (lam23 (app23 (app23 mul23 (suc23 v123)) v023)))
        (suc23 zero23))
def Ty24 : Type 1
 := ∀ (Ty24           : Type)
      (nat top bot  : Ty24)
      (arr prod sum : Ty24 → Ty24 → Ty24)
    , Ty24

def nat24 : Ty24 := λ _ nat24 _ _ _ _ _ => nat24
def top24 : Ty24 := λ _ _ top24 _ _ _ _ => top24
def bot24 : Ty24 := λ _ _ _ bot24 _ _ _ => bot24

def arr24 : Ty24 → Ty24 → Ty24
 := λ A B Ty24 nat24 top24 bot24 arr24 prod sum =>
     arr24 (A Ty24 nat24 top24 bot24 arr24 prod sum) (B Ty24 nat24 top24 bot24 arr24 prod sum)

def prod24 : Ty24 → Ty24 → Ty24
 := λ A B Ty24 nat24 top24 bot24 arr24 prod24 sum =>
     prod24 (A Ty24 nat24 top24 bot24 arr24 prod24 sum) (B Ty24 nat24 top24 bot24 arr24 prod24 sum)

def sum24 : Ty24 → Ty24 → Ty24
 := λ A B Ty24 nat24 top24 bot24 arr24 prod24 sum24 =>
     sum24 (A Ty24 nat24 top24 bot24 arr24 prod24 sum24) (B Ty24 nat24 top24 bot24 arr24 prod24 sum24)

def Con24 : Type 1
 := ∀ (Con24  : Type)
      (nil  : Con24)
      (snoc : Con24 → Ty24 → Con24)
    , Con24

def nil24 : Con24
 := λ Con24 nil24 snoc => nil24

def snoc24 : Con24 → Ty24 → Con24
 := λ Γ A Con24 nil24 snoc24 => snoc24 (Γ Con24 nil24 snoc24) A

def Var24 : Con24 → Ty24 → Type 1
 := λ Γ A =>
   ∀ (Var24 : Con24 → Ty24 → Type)
     (vz  : ∀{Γ A}, Var24 (snoc24 Γ A) A)
     (vs  : ∀{Γ B A}, Var24 Γ A → Var24 (snoc24 Γ B) A)
   , Var24 Γ A

def vz24 : ∀ {Γ A}, Var24 (snoc24 Γ A) A
 := λ Var24 vz24 vs => vz24

def vs24 : ∀ {Γ B A}, Var24 Γ A → Var24 (snoc24 Γ B) A
 := λ x Var24 vz24 vs24 => vs24 (x Var24 vz24 vs24)

def Tm24 : Con24 → Ty24 → Type 1
 := λ Γ A =>
   ∀ (Tm24  : Con24 → Ty24 → Type)
     (var : ∀ {Γ A}, Var24 Γ A → Tm24 Γ A)
     (lam : ∀ {Γ A B}, (Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B)))
     (app   : ∀ {Γ A B}   , Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B)
     (tt    : ∀ {Γ}       , Tm24 Γ top24)
     (pair  : ∀ {Γ A B}   , Tm24 Γ A → Tm24 Γ B → Tm24 Γ (prod24 A B))
     (fst   : ∀ {Γ A B}   , Tm24 Γ (prod24 A B) → Tm24 Γ A)
     (snd   : ∀ {Γ A B}   , Tm24 Γ (prod24 A B) → Tm24 Γ B)
     (left  : ∀ {Γ A B}   , Tm24 Γ A → Tm24 Γ (sum24 A B))
     (right : ∀ {Γ A B}   , Tm24 Γ B → Tm24 Γ (sum24 A B))
     (case  : ∀ {Γ A B C} , Tm24 Γ (sum24 A B) → Tm24 Γ (arr24 A C) → Tm24 Γ (arr24 B C) → Tm24 Γ C)
     (zero  : ∀ {Γ}       , Tm24 Γ nat24)
     (suc   : ∀ {Γ}       , Tm24 Γ nat24 → Tm24 Γ nat24)
     (rec   : ∀ {Γ A}     , Tm24 Γ nat24 → Tm24 Γ (arr24 nat24 (arr24 A A)) → Tm24 Γ A → Tm24 Γ A)
   , Tm24 Γ A

def var24 : ∀ {Γ A}, Var24 Γ A → Tm24 Γ A
 := λ x Tm24 var24 lam app tt pair fst snd left right case zero suc rec =>
     var24 x

def lam24 : ∀ {Γ A B} , Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B)
 := λ t Tm24 var24 lam24 app tt pair fst snd left right case zero suc rec =>
     lam24 (t Tm24 var24 lam24 app tt pair fst snd left right case zero suc rec)

def app24 : ∀ {Γ A B} , Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B
 := λ t u Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec =>
     app24 (t Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec)
         (u Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec)

def tt24 : ∀ {Γ} , Tm24 Γ top24
 := λ Tm24 var24 lam24 app24 tt24 pair fst snd left right case zero suc rec => tt24

def pair24 : ∀ {Γ A B} , Tm24 Γ A → Tm24 Γ B → Tm24 Γ (prod24 A B)
 := λ t u Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec =>
     pair24 (t Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec)
          (u Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec)

def fst24 : ∀ {Γ A B} , Tm24 Γ (prod24 A B) → Tm24 Γ A
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd left right case zero suc rec =>
     fst24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd left right case zero suc rec)

def snd24 : ∀ {Γ A B} , Tm24 Γ (prod24 A B) → Tm24 Γ B
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left right case zero suc rec =>
     snd24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left right case zero suc rec)

def left24 : ∀ {Γ A B} , Tm24 Γ A → Tm24 Γ (sum24 A B)
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right case zero suc rec =>
     left24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right case zero suc rec)

def right24 : ∀ {Γ A B} , Tm24 Γ B → Tm24 Γ (sum24 A B)
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case zero suc rec =>
     right24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case zero suc rec)

def case24 : ∀ {Γ A B C} , Tm24 Γ (sum24 A B) → Tm24 Γ (arr24 A C) → Tm24 Γ (arr24 B C) → Tm24 Γ C
 := λ t u v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec =>
     case24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)
          (u Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)
          (v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)

def zero24  : ∀ {Γ} , Tm24 Γ nat24
 := λ Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc rec => zero24

def suc24 : ∀ {Γ} , Tm24 Γ nat24 → Tm24 Γ nat24
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec =>
   suc24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec)

def rec24 : ∀ {Γ A} , Tm24 Γ nat24 → Tm24 Γ (arr24 nat24 (arr24 A A)) → Tm24 Γ A → Tm24 Γ A
 := λ t u v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24 =>
     rec24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)
         (u Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)
         (v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)

def v024 : ∀ {Γ A}, Tm24 (snoc24 Γ A) A
 := var24 vz24

def v124 : ∀ {Γ A B}, Tm24 (snoc24 (snoc24 Γ A) B) A
 := var24 (vs24 vz24)

def v224 : ∀ {Γ A B C}, Tm24 (snoc24 (snoc24 (snoc24 Γ A) B) C) A
 := var24 (vs24 (vs24 vz24))

def v324 : ∀ {Γ A B C D}, Tm24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) A
 := var24 (vs24 (vs24 (vs24 vz24)))

def tbool24 : Ty24
 := sum24 top24 top24

def ttrue24 : ∀ {Γ}, Tm24 Γ tbool24
 := left24 tt24

def tfalse24 : ∀ {Γ}, Tm24 Γ tbool24
 := right24 tt24

def ifthenelse24 : ∀ {Γ A}, Tm24 Γ (arr24 tbool24 (arr24 A (arr24 A A)))
 := lam24 (lam24 (lam24 (case24 v224 (lam24 v224) (lam24 v124))))

def times424 : ∀ {Γ A}, Tm24 Γ (arr24 (arr24 A A) (arr24 A A))
  := lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024)))))

def add24 : ∀ {Γ}, Tm24 Γ (arr24 nat24 (arr24 nat24 nat24))
 := lam24 (rec24 v024
      (lam24 (lam24 (lam24 (suc24 (app24 v124 v024)))))
      (lam24 v024))

def mul24 : ∀ {Γ}, Tm24 Γ (arr24 nat24 (arr24 nat24 nat24))
 := lam24 (rec24 v024
     (lam24 (lam24 (lam24 (app24 (app24 add24 (app24 v124 v024)) v024))))
     (lam24 zero24))

def fact24 : ∀ {Γ}, Tm24 Γ (arr24 nat24 nat24)
 := lam24 (rec24 v024 (lam24 (lam24 (app24 (app24 mul24 (suc24 v124)) v024)))
        (suc24 zero24))
def Ty25 : Type 1
 := ∀ (Ty25           : Type)
      (nat top bot  : Ty25)
      (arr prod sum : Ty25 → Ty25 → Ty25)
    , Ty25

def nat25 : Ty25 := λ _ nat25 _ _ _ _ _ => nat25
def top25 : Ty25 := λ _ _ top25 _ _ _ _ => top25
def bot25 : Ty25 := λ _ _ _ bot25 _ _ _ => bot25

def arr25 : Ty25 → Ty25 → Ty25
 := λ A B Ty25 nat25 top25 bot25 arr25 prod sum =>
     arr25 (A Ty25 nat25 top25 bot25 arr25 prod sum) (B Ty25 nat25 top25 bot25 arr25 prod sum)

def prod25 : Ty25 → Ty25 → Ty25
 := λ A B Ty25 nat25 top25 bot25 arr25 prod25 sum =>
     prod25 (A Ty25 nat25 top25 bot25 arr25 prod25 sum) (B Ty25 nat25 top25 bot25 arr25 prod25 sum)

def sum25 : Ty25 → Ty25 → Ty25
 := λ A B Ty25 nat25 top25 bot25 arr25 prod25 sum25 =>
     sum25 (A Ty25 nat25 top25 bot25 arr25 prod25 sum25) (B Ty25 nat25 top25 bot25 arr25 prod25 sum25)

def Con25 : Type 1
 := ∀ (Con25  : Type)
      (nil  : Con25)
      (snoc : Con25 → Ty25 → Con25)
    , Con25

def nil25 : Con25
 := λ Con25 nil25 snoc => nil25

def snoc25 : Con25 → Ty25 → Con25
 := λ Γ A Con25 nil25 snoc25 => snoc25 (Γ Con25 nil25 snoc25) A

def Var25 : Con25 → Ty25 → Type 1
 := λ Γ A =>
   ∀ (Var25 : Con25 → Ty25 → Type)
     (vz  : ∀{Γ A}, Var25 (snoc25 Γ A) A)
     (vs  : ∀{Γ B A}, Var25 Γ A → Var25 (snoc25 Γ B) A)
   , Var25 Γ A

def vz25 : ∀ {Γ A}, Var25 (snoc25 Γ A) A
 := λ Var25 vz25 vs => vz25

def vs25 : ∀ {Γ B A}, Var25 Γ A → Var25 (snoc25 Γ B) A
 := λ x Var25 vz25 vs25 => vs25 (x Var25 vz25 vs25)

def Tm25 : Con25 → Ty25 → Type 1
 := λ Γ A =>
   ∀ (Tm25  : Con25 → Ty25 → Type)
     (var : ∀ {Γ A}, Var25 Γ A → Tm25 Γ A)
     (lam : ∀ {Γ A B}, (Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B)))
     (app   : ∀ {Γ A B}   , Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B)
     (tt    : ∀ {Γ}       , Tm25 Γ top25)
     (pair  : ∀ {Γ A B}   , Tm25 Γ A → Tm25 Γ B → Tm25 Γ (prod25 A B))
     (fst   : ∀ {Γ A B}   , Tm25 Γ (prod25 A B) → Tm25 Γ A)
     (snd   : ∀ {Γ A B}   , Tm25 Γ (prod25 A B) → Tm25 Γ B)
     (left  : ∀ {Γ A B}   , Tm25 Γ A → Tm25 Γ (sum25 A B))
     (right : ∀ {Γ A B}   , Tm25 Γ B → Tm25 Γ (sum25 A B))
     (case  : ∀ {Γ A B C} , Tm25 Γ (sum25 A B) → Tm25 Γ (arr25 A C) → Tm25 Γ (arr25 B C) → Tm25 Γ C)
     (zero  : ∀ {Γ}       , Tm25 Γ nat25)
     (suc   : ∀ {Γ}       , Tm25 Γ nat25 → Tm25 Γ nat25)
     (rec   : ∀ {Γ A}     , Tm25 Γ nat25 → Tm25 Γ (arr25 nat25 (arr25 A A)) → Tm25 Γ A → Tm25 Γ A)
   , Tm25 Γ A

def var25 : ∀ {Γ A}, Var25 Γ A → Tm25 Γ A
 := λ x Tm25 var25 lam app tt pair fst snd left right case zero suc rec =>
     var25 x

def lam25 : ∀ {Γ A B} , Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B)
 := λ t Tm25 var25 lam25 app tt pair fst snd left right case zero suc rec =>
     lam25 (t Tm25 var25 lam25 app tt pair fst snd left right case zero suc rec)

def app25 : ∀ {Γ A B} , Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B
 := λ t u Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec =>
     app25 (t Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec)
         (u Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec)

def tt25 : ∀ {Γ} , Tm25 Γ top25
 := λ Tm25 var25 lam25 app25 tt25 pair fst snd left right case zero suc rec => tt25

def pair25 : ∀ {Γ A B} , Tm25 Γ A → Tm25 Γ B → Tm25 Γ (prod25 A B)
 := λ t u Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec =>
     pair25 (t Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec)
          (u Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec)

def fst25 : ∀ {Γ A B} , Tm25 Γ (prod25 A B) → Tm25 Γ A
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd left right case zero suc rec =>
     fst25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd left right case zero suc rec)

def snd25 : ∀ {Γ A B} , Tm25 Γ (prod25 A B) → Tm25 Γ B
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left right case zero suc rec =>
     snd25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left right case zero suc rec)

def left25 : ∀ {Γ A B} , Tm25 Γ A → Tm25 Γ (sum25 A B)
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right case zero suc rec =>
     left25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right case zero suc rec)

def right25 : ∀ {Γ A B} , Tm25 Γ B → Tm25 Γ (sum25 A B)
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case zero suc rec =>
     right25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case zero suc rec)

def case25 : ∀ {Γ A B C} , Tm25 Γ (sum25 A B) → Tm25 Γ (arr25 A C) → Tm25 Γ (arr25 B C) → Tm25 Γ C
 := λ t u v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec =>
     case25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)
          (u Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)
          (v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)

def zero25  : ∀ {Γ} , Tm25 Γ nat25
 := λ Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc rec => zero25

def suc25 : ∀ {Γ} , Tm25 Γ nat25 → Tm25 Γ nat25
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec =>
   suc25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec)

def rec25 : ∀ {Γ A} , Tm25 Γ nat25 → Tm25 Γ (arr25 nat25 (arr25 A A)) → Tm25 Γ A → Tm25 Γ A
 := λ t u v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25 =>
     rec25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)
         (u Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)
         (v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)

def v025 : ∀ {Γ A}, Tm25 (snoc25 Γ A) A
 := var25 vz25

def v125 : ∀ {Γ A B}, Tm25 (snoc25 (snoc25 Γ A) B) A
 := var25 (vs25 vz25)

def v225 : ∀ {Γ A B C}, Tm25 (snoc25 (snoc25 (snoc25 Γ A) B) C) A
 := var25 (vs25 (vs25 vz25))

def v325 : ∀ {Γ A B C D}, Tm25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) A
 := var25 (vs25 (vs25 (vs25 vz25)))

def tbool25 : Ty25
 := sum25 top25 top25

def ttrue25 : ∀ {Γ}, Tm25 Γ tbool25
 := left25 tt25

def tfalse25 : ∀ {Γ}, Tm25 Γ tbool25
 := right25 tt25

def ifthenelse25 : ∀ {Γ A}, Tm25 Γ (arr25 tbool25 (arr25 A (arr25 A A)))
 := lam25 (lam25 (lam25 (case25 v225 (lam25 v225) (lam25 v125))))

def times425 : ∀ {Γ A}, Tm25 Γ (arr25 (arr25 A A) (arr25 A A))
  := lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025)))))

def add25 : ∀ {Γ}, Tm25 Γ (arr25 nat25 (arr25 nat25 nat25))
 := lam25 (rec25 v025
      (lam25 (lam25 (lam25 (suc25 (app25 v125 v025)))))
      (lam25 v025))

def mul25 : ∀ {Γ}, Tm25 Γ (arr25 nat25 (arr25 nat25 nat25))
 := lam25 (rec25 v025
     (lam25 (lam25 (lam25 (app25 (app25 add25 (app25 v125 v025)) v025))))
     (lam25 zero25))

def fact25 : ∀ {Γ}, Tm25 Γ (arr25 nat25 nat25)
 := lam25 (rec25 v025 (lam25 (lam25 (app25 (app25 mul25 (suc25 v125)) v025)))
        (suc25 zero25))
def Ty26 : Type 1
 := ∀ (Ty26           : Type)
      (nat top bot  : Ty26)
      (arr prod sum : Ty26 → Ty26 → Ty26)
    , Ty26

def nat26 : Ty26 := λ _ nat26 _ _ _ _ _ => nat26
def top26 : Ty26 := λ _ _ top26 _ _ _ _ => top26
def bot26 : Ty26 := λ _ _ _ bot26 _ _ _ => bot26

def arr26 : Ty26 → Ty26 → Ty26
 := λ A B Ty26 nat26 top26 bot26 arr26 prod sum =>
     arr26 (A Ty26 nat26 top26 bot26 arr26 prod sum) (B Ty26 nat26 top26 bot26 arr26 prod sum)

def prod26 : Ty26 → Ty26 → Ty26
 := λ A B Ty26 nat26 top26 bot26 arr26 prod26 sum =>
     prod26 (A Ty26 nat26 top26 bot26 arr26 prod26 sum) (B Ty26 nat26 top26 bot26 arr26 prod26 sum)

def sum26 : Ty26 → Ty26 → Ty26
 := λ A B Ty26 nat26 top26 bot26 arr26 prod26 sum26 =>
     sum26 (A Ty26 nat26 top26 bot26 arr26 prod26 sum26) (B Ty26 nat26 top26 bot26 arr26 prod26 sum26)

def Con26 : Type 1
 := ∀ (Con26  : Type)
      (nil  : Con26)
      (snoc : Con26 → Ty26 → Con26)
    , Con26

def nil26 : Con26
 := λ Con26 nil26 snoc => nil26

def snoc26 : Con26 → Ty26 → Con26
 := λ Γ A Con26 nil26 snoc26 => snoc26 (Γ Con26 nil26 snoc26) A

def Var26 : Con26 → Ty26 → Type 1
 := λ Γ A =>
   ∀ (Var26 : Con26 → Ty26 → Type)
     (vz  : ∀{Γ A}, Var26 (snoc26 Γ A) A)
     (vs  : ∀{Γ B A}, Var26 Γ A → Var26 (snoc26 Γ B) A)
   , Var26 Γ A

def vz26 : ∀ {Γ A}, Var26 (snoc26 Γ A) A
 := λ Var26 vz26 vs => vz26

def vs26 : ∀ {Γ B A}, Var26 Γ A → Var26 (snoc26 Γ B) A
 := λ x Var26 vz26 vs26 => vs26 (x Var26 vz26 vs26)

def Tm26 : Con26 → Ty26 → Type 1
 := λ Γ A =>
   ∀ (Tm26  : Con26 → Ty26 → Type)
     (var : ∀ {Γ A}, Var26 Γ A → Tm26 Γ A)
     (lam : ∀ {Γ A B}, (Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B)))
     (app   : ∀ {Γ A B}   , Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B)
     (tt    : ∀ {Γ}       , Tm26 Γ top26)
     (pair  : ∀ {Γ A B}   , Tm26 Γ A → Tm26 Γ B → Tm26 Γ (prod26 A B))
     (fst   : ∀ {Γ A B}   , Tm26 Γ (prod26 A B) → Tm26 Γ A)
     (snd   : ∀ {Γ A B}   , Tm26 Γ (prod26 A B) → Tm26 Γ B)
     (left  : ∀ {Γ A B}   , Tm26 Γ A → Tm26 Γ (sum26 A B))
     (right : ∀ {Γ A B}   , Tm26 Γ B → Tm26 Γ (sum26 A B))
     (case  : ∀ {Γ A B C} , Tm26 Γ (sum26 A B) → Tm26 Γ (arr26 A C) → Tm26 Γ (arr26 B C) → Tm26 Γ C)
     (zero  : ∀ {Γ}       , Tm26 Γ nat26)
     (suc   : ∀ {Γ}       , Tm26 Γ nat26 → Tm26 Γ nat26)
     (rec   : ∀ {Γ A}     , Tm26 Γ nat26 → Tm26 Γ (arr26 nat26 (arr26 A A)) → Tm26 Γ A → Tm26 Γ A)
   , Tm26 Γ A

def var26 : ∀ {Γ A}, Var26 Γ A → Tm26 Γ A
 := λ x Tm26 var26 lam app tt pair fst snd left right case zero suc rec =>
     var26 x

def lam26 : ∀ {Γ A B} , Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B)
 := λ t Tm26 var26 lam26 app tt pair fst snd left right case zero suc rec =>
     lam26 (t Tm26 var26 lam26 app tt pair fst snd left right case zero suc rec)

def app26 : ∀ {Γ A B} , Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B
 := λ t u Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec =>
     app26 (t Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec)
         (u Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec)

def tt26 : ∀ {Γ} , Tm26 Γ top26
 := λ Tm26 var26 lam26 app26 tt26 pair fst snd left right case zero suc rec => tt26

def pair26 : ∀ {Γ A B} , Tm26 Γ A → Tm26 Γ B → Tm26 Γ (prod26 A B)
 := λ t u Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec =>
     pair26 (t Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec)
          (u Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec)

def fst26 : ∀ {Γ A B} , Tm26 Γ (prod26 A B) → Tm26 Γ A
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd left right case zero suc rec =>
     fst26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd left right case zero suc rec)

def snd26 : ∀ {Γ A B} , Tm26 Γ (prod26 A B) → Tm26 Γ B
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left right case zero suc rec =>
     snd26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left right case zero suc rec)

def left26 : ∀ {Γ A B} , Tm26 Γ A → Tm26 Γ (sum26 A B)
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right case zero suc rec =>
     left26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right case zero suc rec)

def right26 : ∀ {Γ A B} , Tm26 Γ B → Tm26 Γ (sum26 A B)
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case zero suc rec =>
     right26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case zero suc rec)

def case26 : ∀ {Γ A B C} , Tm26 Γ (sum26 A B) → Tm26 Γ (arr26 A C) → Tm26 Γ (arr26 B C) → Tm26 Γ C
 := λ t u v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec =>
     case26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)
          (u Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)
          (v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)

def zero26  : ∀ {Γ} , Tm26 Γ nat26
 := λ Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc rec => zero26

def suc26 : ∀ {Γ} , Tm26 Γ nat26 → Tm26 Γ nat26
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec =>
   suc26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec)

def rec26 : ∀ {Γ A} , Tm26 Γ nat26 → Tm26 Γ (arr26 nat26 (arr26 A A)) → Tm26 Γ A → Tm26 Γ A
 := λ t u v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26 =>
     rec26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)
         (u Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)
         (v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)

def v026 : ∀ {Γ A}, Tm26 (snoc26 Γ A) A
 := var26 vz26

def v126 : ∀ {Γ A B}, Tm26 (snoc26 (snoc26 Γ A) B) A
 := var26 (vs26 vz26)

def v226 : ∀ {Γ A B C}, Tm26 (snoc26 (snoc26 (snoc26 Γ A) B) C) A
 := var26 (vs26 (vs26 vz26))

def v326 : ∀ {Γ A B C D}, Tm26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) A
 := var26 (vs26 (vs26 (vs26 vz26)))

def tbool26 : Ty26
 := sum26 top26 top26

def ttrue26 : ∀ {Γ}, Tm26 Γ tbool26
 := left26 tt26

def tfalse26 : ∀ {Γ}, Tm26 Γ tbool26
 := right26 tt26

def ifthenelse26 : ∀ {Γ A}, Tm26 Γ (arr26 tbool26 (arr26 A (arr26 A A)))
 := lam26 (lam26 (lam26 (case26 v226 (lam26 v226) (lam26 v126))))

def times426 : ∀ {Γ A}, Tm26 Γ (arr26 (arr26 A A) (arr26 A A))
  := lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026)))))

def add26 : ∀ {Γ}, Tm26 Γ (arr26 nat26 (arr26 nat26 nat26))
 := lam26 (rec26 v026
      (lam26 (lam26 (lam26 (suc26 (app26 v126 v026)))))
      (lam26 v026))

def mul26 : ∀ {Γ}, Tm26 Γ (arr26 nat26 (arr26 nat26 nat26))
 := lam26 (rec26 v026
     (lam26 (lam26 (lam26 (app26 (app26 add26 (app26 v126 v026)) v026))))
     (lam26 zero26))

def fact26 : ∀ {Γ}, Tm26 Γ (arr26 nat26 nat26)
 := lam26 (rec26 v026 (lam26 (lam26 (app26 (app26 mul26 (suc26 v126)) v026)))
        (suc26 zero26))
def Ty27 : Type 1
 := ∀ (Ty27           : Type)
      (nat top bot  : Ty27)
      (arr prod sum : Ty27 → Ty27 → Ty27)
    , Ty27

def nat27 : Ty27 := λ _ nat27 _ _ _ _ _ => nat27
def top27 : Ty27 := λ _ _ top27 _ _ _ _ => top27
def bot27 : Ty27 := λ _ _ _ bot27 _ _ _ => bot27

def arr27 : Ty27 → Ty27 → Ty27
 := λ A B Ty27 nat27 top27 bot27 arr27 prod sum =>
     arr27 (A Ty27 nat27 top27 bot27 arr27 prod sum) (B Ty27 nat27 top27 bot27 arr27 prod sum)

def prod27 : Ty27 → Ty27 → Ty27
 := λ A B Ty27 nat27 top27 bot27 arr27 prod27 sum =>
     prod27 (A Ty27 nat27 top27 bot27 arr27 prod27 sum) (B Ty27 nat27 top27 bot27 arr27 prod27 sum)

def sum27 : Ty27 → Ty27 → Ty27
 := λ A B Ty27 nat27 top27 bot27 arr27 prod27 sum27 =>
     sum27 (A Ty27 nat27 top27 bot27 arr27 prod27 sum27) (B Ty27 nat27 top27 bot27 arr27 prod27 sum27)

def Con27 : Type 1
 := ∀ (Con27  : Type)
      (nil  : Con27)
      (snoc : Con27 → Ty27 → Con27)
    , Con27

def nil27 : Con27
 := λ Con27 nil27 snoc => nil27

def snoc27 : Con27 → Ty27 → Con27
 := λ Γ A Con27 nil27 snoc27 => snoc27 (Γ Con27 nil27 snoc27) A

def Var27 : Con27 → Ty27 → Type 1
 := λ Γ A =>
   ∀ (Var27 : Con27 → Ty27 → Type)
     (vz  : ∀{Γ A}, Var27 (snoc27 Γ A) A)
     (vs  : ∀{Γ B A}, Var27 Γ A → Var27 (snoc27 Γ B) A)
   , Var27 Γ A

def vz27 : ∀ {Γ A}, Var27 (snoc27 Γ A) A
 := λ Var27 vz27 vs => vz27

def vs27 : ∀ {Γ B A}, Var27 Γ A → Var27 (snoc27 Γ B) A
 := λ x Var27 vz27 vs27 => vs27 (x Var27 vz27 vs27)

def Tm27 : Con27 → Ty27 → Type 1
 := λ Γ A =>
   ∀ (Tm27  : Con27 → Ty27 → Type)
     (var : ∀ {Γ A}, Var27 Γ A → Tm27 Γ A)
     (lam : ∀ {Γ A B}, (Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B)))
     (app   : ∀ {Γ A B}   , Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B)
     (tt    : ∀ {Γ}       , Tm27 Γ top27)
     (pair  : ∀ {Γ A B}   , Tm27 Γ A → Tm27 Γ B → Tm27 Γ (prod27 A B))
     (fst   : ∀ {Γ A B}   , Tm27 Γ (prod27 A B) → Tm27 Γ A)
     (snd   : ∀ {Γ A B}   , Tm27 Γ (prod27 A B) → Tm27 Γ B)
     (left  : ∀ {Γ A B}   , Tm27 Γ A → Tm27 Γ (sum27 A B))
     (right : ∀ {Γ A B}   , Tm27 Γ B → Tm27 Γ (sum27 A B))
     (case  : ∀ {Γ A B C} , Tm27 Γ (sum27 A B) → Tm27 Γ (arr27 A C) → Tm27 Γ (arr27 B C) → Tm27 Γ C)
     (zero  : ∀ {Γ}       , Tm27 Γ nat27)
     (suc   : ∀ {Γ}       , Tm27 Γ nat27 → Tm27 Γ nat27)
     (rec   : ∀ {Γ A}     , Tm27 Γ nat27 → Tm27 Γ (arr27 nat27 (arr27 A A)) → Tm27 Γ A → Tm27 Γ A)
   , Tm27 Γ A

def var27 : ∀ {Γ A}, Var27 Γ A → Tm27 Γ A
 := λ x Tm27 var27 lam app tt pair fst snd left right case zero suc rec =>
     var27 x

def lam27 : ∀ {Γ A B} , Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B)
 := λ t Tm27 var27 lam27 app tt pair fst snd left right case zero suc rec =>
     lam27 (t Tm27 var27 lam27 app tt pair fst snd left right case zero suc rec)

def app27 : ∀ {Γ A B} , Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B
 := λ t u Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec =>
     app27 (t Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec)
         (u Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec)

def tt27 : ∀ {Γ} , Tm27 Γ top27
 := λ Tm27 var27 lam27 app27 tt27 pair fst snd left right case zero suc rec => tt27

def pair27 : ∀ {Γ A B} , Tm27 Γ A → Tm27 Γ B → Tm27 Γ (prod27 A B)
 := λ t u Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec =>
     pair27 (t Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec)
          (u Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec)

def fst27 : ∀ {Γ A B} , Tm27 Γ (prod27 A B) → Tm27 Γ A
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd left right case zero suc rec =>
     fst27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd left right case zero suc rec)

def snd27 : ∀ {Γ A B} , Tm27 Γ (prod27 A B) → Tm27 Γ B
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left right case zero suc rec =>
     snd27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left right case zero suc rec)

def left27 : ∀ {Γ A B} , Tm27 Γ A → Tm27 Γ (sum27 A B)
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right case zero suc rec =>
     left27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right case zero suc rec)

def right27 : ∀ {Γ A B} , Tm27 Γ B → Tm27 Γ (sum27 A B)
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case zero suc rec =>
     right27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case zero suc rec)

def case27 : ∀ {Γ A B C} , Tm27 Γ (sum27 A B) → Tm27 Γ (arr27 A C) → Tm27 Γ (arr27 B C) → Tm27 Γ C
 := λ t u v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec =>
     case27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)
          (u Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)
          (v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)

def zero27  : ∀ {Γ} , Tm27 Γ nat27
 := λ Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc rec => zero27

def suc27 : ∀ {Γ} , Tm27 Γ nat27 → Tm27 Γ nat27
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec =>
   suc27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec)

def rec27 : ∀ {Γ A} , Tm27 Γ nat27 → Tm27 Γ (arr27 nat27 (arr27 A A)) → Tm27 Γ A → Tm27 Γ A
 := λ t u v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27 =>
     rec27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)
         (u Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)
         (v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)

def v027 : ∀ {Γ A}, Tm27 (snoc27 Γ A) A
 := var27 vz27

def v127 : ∀ {Γ A B}, Tm27 (snoc27 (snoc27 Γ A) B) A
 := var27 (vs27 vz27)

def v227 : ∀ {Γ A B C}, Tm27 (snoc27 (snoc27 (snoc27 Γ A) B) C) A
 := var27 (vs27 (vs27 vz27))

def v327 : ∀ {Γ A B C D}, Tm27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) A
 := var27 (vs27 (vs27 (vs27 vz27)))

def tbool27 : Ty27
 := sum27 top27 top27

def ttrue27 : ∀ {Γ}, Tm27 Γ tbool27
 := left27 tt27

def tfalse27 : ∀ {Γ}, Tm27 Γ tbool27
 := right27 tt27

def ifthenelse27 : ∀ {Γ A}, Tm27 Γ (arr27 tbool27 (arr27 A (arr27 A A)))
 := lam27 (lam27 (lam27 (case27 v227 (lam27 v227) (lam27 v127))))

def times427 : ∀ {Γ A}, Tm27 Γ (arr27 (arr27 A A) (arr27 A A))
  := lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027)))))

def add27 : ∀ {Γ}, Tm27 Γ (arr27 nat27 (arr27 nat27 nat27))
 := lam27 (rec27 v027
      (lam27 (lam27 (lam27 (suc27 (app27 v127 v027)))))
      (lam27 v027))

def mul27 : ∀ {Γ}, Tm27 Γ (arr27 nat27 (arr27 nat27 nat27))
 := lam27 (rec27 v027
     (lam27 (lam27 (lam27 (app27 (app27 add27 (app27 v127 v027)) v027))))
     (lam27 zero27))

def fact27 : ∀ {Γ}, Tm27 Γ (arr27 nat27 nat27)
 := lam27 (rec27 v027 (lam27 (lam27 (app27 (app27 mul27 (suc27 v127)) v027)))
        (suc27 zero27))
def Ty28 : Type 1
 := ∀ (Ty28           : Type)
      (nat top bot  : Ty28)
      (arr prod sum : Ty28 → Ty28 → Ty28)
    , Ty28

def nat28 : Ty28 := λ _ nat28 _ _ _ _ _ => nat28
def top28 : Ty28 := λ _ _ top28 _ _ _ _ => top28
def bot28 : Ty28 := λ _ _ _ bot28 _ _ _ => bot28

def arr28 : Ty28 → Ty28 → Ty28
 := λ A B Ty28 nat28 top28 bot28 arr28 prod sum =>
     arr28 (A Ty28 nat28 top28 bot28 arr28 prod sum) (B Ty28 nat28 top28 bot28 arr28 prod sum)

def prod28 : Ty28 → Ty28 → Ty28
 := λ A B Ty28 nat28 top28 bot28 arr28 prod28 sum =>
     prod28 (A Ty28 nat28 top28 bot28 arr28 prod28 sum) (B Ty28 nat28 top28 bot28 arr28 prod28 sum)

def sum28 : Ty28 → Ty28 → Ty28
 := λ A B Ty28 nat28 top28 bot28 arr28 prod28 sum28 =>
     sum28 (A Ty28 nat28 top28 bot28 arr28 prod28 sum28) (B Ty28 nat28 top28 bot28 arr28 prod28 sum28)

def Con28 : Type 1
 := ∀ (Con28  : Type)
      (nil  : Con28)
      (snoc : Con28 → Ty28 → Con28)
    , Con28

def nil28 : Con28
 := λ Con28 nil28 snoc => nil28

def snoc28 : Con28 → Ty28 → Con28
 := λ Γ A Con28 nil28 snoc28 => snoc28 (Γ Con28 nil28 snoc28) A

def Var28 : Con28 → Ty28 → Type 1
 := λ Γ A =>
   ∀ (Var28 : Con28 → Ty28 → Type)
     (vz  : ∀{Γ A}, Var28 (snoc28 Γ A) A)
     (vs  : ∀{Γ B A}, Var28 Γ A → Var28 (snoc28 Γ B) A)
   , Var28 Γ A

def vz28 : ∀ {Γ A}, Var28 (snoc28 Γ A) A
 := λ Var28 vz28 vs => vz28

def vs28 : ∀ {Γ B A}, Var28 Γ A → Var28 (snoc28 Γ B) A
 := λ x Var28 vz28 vs28 => vs28 (x Var28 vz28 vs28)

def Tm28 : Con28 → Ty28 → Type 1
 := λ Γ A =>
   ∀ (Tm28  : Con28 → Ty28 → Type)
     (var : ∀ {Γ A}, Var28 Γ A → Tm28 Γ A)
     (lam : ∀ {Γ A B}, (Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B)))
     (app   : ∀ {Γ A B}   , Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B)
     (tt    : ∀ {Γ}       , Tm28 Γ top28)
     (pair  : ∀ {Γ A B}   , Tm28 Γ A → Tm28 Γ B → Tm28 Γ (prod28 A B))
     (fst   : ∀ {Γ A B}   , Tm28 Γ (prod28 A B) → Tm28 Γ A)
     (snd   : ∀ {Γ A B}   , Tm28 Γ (prod28 A B) → Tm28 Γ B)
     (left  : ∀ {Γ A B}   , Tm28 Γ A → Tm28 Γ (sum28 A B))
     (right : ∀ {Γ A B}   , Tm28 Γ B → Tm28 Γ (sum28 A B))
     (case  : ∀ {Γ A B C} , Tm28 Γ (sum28 A B) → Tm28 Γ (arr28 A C) → Tm28 Γ (arr28 B C) → Tm28 Γ C)
     (zero  : ∀ {Γ}       , Tm28 Γ nat28)
     (suc   : ∀ {Γ}       , Tm28 Γ nat28 → Tm28 Γ nat28)
     (rec   : ∀ {Γ A}     , Tm28 Γ nat28 → Tm28 Γ (arr28 nat28 (arr28 A A)) → Tm28 Γ A → Tm28 Γ A)
   , Tm28 Γ A

def var28 : ∀ {Γ A}, Var28 Γ A → Tm28 Γ A
 := λ x Tm28 var28 lam app tt pair fst snd left right case zero suc rec =>
     var28 x

def lam28 : ∀ {Γ A B} , Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B)
 := λ t Tm28 var28 lam28 app tt pair fst snd left right case zero suc rec =>
     lam28 (t Tm28 var28 lam28 app tt pair fst snd left right case zero suc rec)

def app28 : ∀ {Γ A B} , Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B
 := λ t u Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec =>
     app28 (t Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec)
         (u Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec)

def tt28 : ∀ {Γ} , Tm28 Γ top28
 := λ Tm28 var28 lam28 app28 tt28 pair fst snd left right case zero suc rec => tt28

def pair28 : ∀ {Γ A B} , Tm28 Γ A → Tm28 Γ B → Tm28 Γ (prod28 A B)
 := λ t u Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec =>
     pair28 (t Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec)
          (u Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec)

def fst28 : ∀ {Γ A B} , Tm28 Γ (prod28 A B) → Tm28 Γ A
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd left right case zero suc rec =>
     fst28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd left right case zero suc rec)

def snd28 : ∀ {Γ A B} , Tm28 Γ (prod28 A B) → Tm28 Γ B
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left right case zero suc rec =>
     snd28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left right case zero suc rec)

def left28 : ∀ {Γ A B} , Tm28 Γ A → Tm28 Γ (sum28 A B)
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right case zero suc rec =>
     left28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right case zero suc rec)

def right28 : ∀ {Γ A B} , Tm28 Γ B → Tm28 Γ (sum28 A B)
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case zero suc rec =>
     right28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case zero suc rec)

def case28 : ∀ {Γ A B C} , Tm28 Γ (sum28 A B) → Tm28 Γ (arr28 A C) → Tm28 Γ (arr28 B C) → Tm28 Γ C
 := λ t u v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec =>
     case28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)
          (u Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)
          (v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)

def zero28  : ∀ {Γ} , Tm28 Γ nat28
 := λ Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc rec => zero28

def suc28 : ∀ {Γ} , Tm28 Γ nat28 → Tm28 Γ nat28
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec =>
   suc28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec)

def rec28 : ∀ {Γ A} , Tm28 Γ nat28 → Tm28 Γ (arr28 nat28 (arr28 A A)) → Tm28 Γ A → Tm28 Γ A
 := λ t u v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28 =>
     rec28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)
         (u Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)
         (v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)

def v028 : ∀ {Γ A}, Tm28 (snoc28 Γ A) A
 := var28 vz28

def v128 : ∀ {Γ A B}, Tm28 (snoc28 (snoc28 Γ A) B) A
 := var28 (vs28 vz28)

def v228 : ∀ {Γ A B C}, Tm28 (snoc28 (snoc28 (snoc28 Γ A) B) C) A
 := var28 (vs28 (vs28 vz28))

def v328 : ∀ {Γ A B C D}, Tm28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) A
 := var28 (vs28 (vs28 (vs28 vz28)))

def tbool28 : Ty28
 := sum28 top28 top28

def ttrue28 : ∀ {Γ}, Tm28 Γ tbool28
 := left28 tt28

def tfalse28 : ∀ {Γ}, Tm28 Γ tbool28
 := right28 tt28

def ifthenelse28 : ∀ {Γ A}, Tm28 Γ (arr28 tbool28 (arr28 A (arr28 A A)))
 := lam28 (lam28 (lam28 (case28 v228 (lam28 v228) (lam28 v128))))

def times428 : ∀ {Γ A}, Tm28 Γ (arr28 (arr28 A A) (arr28 A A))
  := lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028)))))

def add28 : ∀ {Γ}, Tm28 Γ (arr28 nat28 (arr28 nat28 nat28))
 := lam28 (rec28 v028
      (lam28 (lam28 (lam28 (suc28 (app28 v128 v028)))))
      (lam28 v028))

def mul28 : ∀ {Γ}, Tm28 Γ (arr28 nat28 (arr28 nat28 nat28))
 := lam28 (rec28 v028
     (lam28 (lam28 (lam28 (app28 (app28 add28 (app28 v128 v028)) v028))))
     (lam28 zero28))

def fact28 : ∀ {Γ}, Tm28 Γ (arr28 nat28 nat28)
 := lam28 (rec28 v028 (lam28 (lam28 (app28 (app28 mul28 (suc28 v128)) v028)))
        (suc28 zero28))
def Ty29 : Type 1
 := ∀ (Ty29           : Type)
      (nat top bot  : Ty29)
      (arr prod sum : Ty29 → Ty29 → Ty29)
    , Ty29

def nat29 : Ty29 := λ _ nat29 _ _ _ _ _ => nat29
def top29 : Ty29 := λ _ _ top29 _ _ _ _ => top29
def bot29 : Ty29 := λ _ _ _ bot29 _ _ _ => bot29

def arr29 : Ty29 → Ty29 → Ty29
 := λ A B Ty29 nat29 top29 bot29 arr29 prod sum =>
     arr29 (A Ty29 nat29 top29 bot29 arr29 prod sum) (B Ty29 nat29 top29 bot29 arr29 prod sum)

def prod29 : Ty29 → Ty29 → Ty29
 := λ A B Ty29 nat29 top29 bot29 arr29 prod29 sum =>
     prod29 (A Ty29 nat29 top29 bot29 arr29 prod29 sum) (B Ty29 nat29 top29 bot29 arr29 prod29 sum)

def sum29 : Ty29 → Ty29 → Ty29
 := λ A B Ty29 nat29 top29 bot29 arr29 prod29 sum29 =>
     sum29 (A Ty29 nat29 top29 bot29 arr29 prod29 sum29) (B Ty29 nat29 top29 bot29 arr29 prod29 sum29)

def Con29 : Type 1
 := ∀ (Con29  : Type)
      (nil  : Con29)
      (snoc : Con29 → Ty29 → Con29)
    , Con29

def nil29 : Con29
 := λ Con29 nil29 snoc => nil29

def snoc29 : Con29 → Ty29 → Con29
 := λ Γ A Con29 nil29 snoc29 => snoc29 (Γ Con29 nil29 snoc29) A

def Var29 : Con29 → Ty29 → Type 1
 := λ Γ A =>
   ∀ (Var29 : Con29 → Ty29 → Type)
     (vz  : ∀{Γ A}, Var29 (snoc29 Γ A) A)
     (vs  : ∀{Γ B A}, Var29 Γ A → Var29 (snoc29 Γ B) A)
   , Var29 Γ A

def vz29 : ∀ {Γ A}, Var29 (snoc29 Γ A) A
 := λ Var29 vz29 vs => vz29

def vs29 : ∀ {Γ B A}, Var29 Γ A → Var29 (snoc29 Γ B) A
 := λ x Var29 vz29 vs29 => vs29 (x Var29 vz29 vs29)

def Tm29 : Con29 → Ty29 → Type 1
 := λ Γ A =>
   ∀ (Tm29  : Con29 → Ty29 → Type)
     (var : ∀ {Γ A}, Var29 Γ A → Tm29 Γ A)
     (lam : ∀ {Γ A B}, (Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B)))
     (app   : ∀ {Γ A B}   , Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B)
     (tt    : ∀ {Γ}       , Tm29 Γ top29)
     (pair  : ∀ {Γ A B}   , Tm29 Γ A → Tm29 Γ B → Tm29 Γ (prod29 A B))
     (fst   : ∀ {Γ A B}   , Tm29 Γ (prod29 A B) → Tm29 Γ A)
     (snd   : ∀ {Γ A B}   , Tm29 Γ (prod29 A B) → Tm29 Γ B)
     (left  : ∀ {Γ A B}   , Tm29 Γ A → Tm29 Γ (sum29 A B))
     (right : ∀ {Γ A B}   , Tm29 Γ B → Tm29 Γ (sum29 A B))
     (case  : ∀ {Γ A B C} , Tm29 Γ (sum29 A B) → Tm29 Γ (arr29 A C) → Tm29 Γ (arr29 B C) → Tm29 Γ C)
     (zero  : ∀ {Γ}       , Tm29 Γ nat29)
     (suc   : ∀ {Γ}       , Tm29 Γ nat29 → Tm29 Γ nat29)
     (rec   : ∀ {Γ A}     , Tm29 Γ nat29 → Tm29 Γ (arr29 nat29 (arr29 A A)) → Tm29 Γ A → Tm29 Γ A)
   , Tm29 Γ A

def var29 : ∀ {Γ A}, Var29 Γ A → Tm29 Γ A
 := λ x Tm29 var29 lam app tt pair fst snd left right case zero suc rec =>
     var29 x

def lam29 : ∀ {Γ A B} , Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B)
 := λ t Tm29 var29 lam29 app tt pair fst snd left right case zero suc rec =>
     lam29 (t Tm29 var29 lam29 app tt pair fst snd left right case zero suc rec)

def app29 : ∀ {Γ A B} , Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B
 := λ t u Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec =>
     app29 (t Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec)
         (u Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec)

def tt29 : ∀ {Γ} , Tm29 Γ top29
 := λ Tm29 var29 lam29 app29 tt29 pair fst snd left right case zero suc rec => tt29

def pair29 : ∀ {Γ A B} , Tm29 Γ A → Tm29 Γ B → Tm29 Γ (prod29 A B)
 := λ t u Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec =>
     pair29 (t Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec)
          (u Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec)

def fst29 : ∀ {Γ A B} , Tm29 Γ (prod29 A B) → Tm29 Γ A
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd left right case zero suc rec =>
     fst29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd left right case zero suc rec)

def snd29 : ∀ {Γ A B} , Tm29 Γ (prod29 A B) → Tm29 Γ B
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left right case zero suc rec =>
     snd29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left right case zero suc rec)

def left29 : ∀ {Γ A B} , Tm29 Γ A → Tm29 Γ (sum29 A B)
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right case zero suc rec =>
     left29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right case zero suc rec)

def right29 : ∀ {Γ A B} , Tm29 Γ B → Tm29 Γ (sum29 A B)
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case zero suc rec =>
     right29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case zero suc rec)

def case29 : ∀ {Γ A B C} , Tm29 Γ (sum29 A B) → Tm29 Γ (arr29 A C) → Tm29 Γ (arr29 B C) → Tm29 Γ C
 := λ t u v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec =>
     case29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)
          (u Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)
          (v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)

def zero29  : ∀ {Γ} , Tm29 Γ nat29
 := λ Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc rec => zero29

def suc29 : ∀ {Γ} , Tm29 Γ nat29 → Tm29 Γ nat29
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec =>
   suc29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec)

def rec29 : ∀ {Γ A} , Tm29 Γ nat29 → Tm29 Γ (arr29 nat29 (arr29 A A)) → Tm29 Γ A → Tm29 Γ A
 := λ t u v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29 =>
     rec29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)
         (u Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)
         (v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)

def v029 : ∀ {Γ A}, Tm29 (snoc29 Γ A) A
 := var29 vz29

def v129 : ∀ {Γ A B}, Tm29 (snoc29 (snoc29 Γ A) B) A
 := var29 (vs29 vz29)

def v229 : ∀ {Γ A B C}, Tm29 (snoc29 (snoc29 (snoc29 Γ A) B) C) A
 := var29 (vs29 (vs29 vz29))

def v329 : ∀ {Γ A B C D}, Tm29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) A
 := var29 (vs29 (vs29 (vs29 vz29)))

def tbool29 : Ty29
 := sum29 top29 top29

def ttrue29 : ∀ {Γ}, Tm29 Γ tbool29
 := left29 tt29

def tfalse29 : ∀ {Γ}, Tm29 Γ tbool29
 := right29 tt29

def ifthenelse29 : ∀ {Γ A}, Tm29 Γ (arr29 tbool29 (arr29 A (arr29 A A)))
 := lam29 (lam29 (lam29 (case29 v229 (lam29 v229) (lam29 v129))))

def times429 : ∀ {Γ A}, Tm29 Γ (arr29 (arr29 A A) (arr29 A A))
  := lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029)))))

def add29 : ∀ {Γ}, Tm29 Γ (arr29 nat29 (arr29 nat29 nat29))
 := lam29 (rec29 v029
      (lam29 (lam29 (lam29 (suc29 (app29 v129 v029)))))
      (lam29 v029))

def mul29 : ∀ {Γ}, Tm29 Γ (arr29 nat29 (arr29 nat29 nat29))
 := lam29 (rec29 v029
     (lam29 (lam29 (lam29 (app29 (app29 add29 (app29 v129 v029)) v029))))
     (lam29 zero29))

def fact29 : ∀ {Γ}, Tm29 Γ (arr29 nat29 nat29)
 := lam29 (rec29 v029 (lam29 (lam29 (app29 (app29 mul29 (suc29 v129)) v029)))
        (suc29 zero29))
def Ty30 : Type 1
 := ∀ (Ty30           : Type)
      (nat top bot  : Ty30)
      (arr prod sum : Ty30 → Ty30 → Ty30)
    , Ty30

def nat30 : Ty30 := λ _ nat30 _ _ _ _ _ => nat30
def top30 : Ty30 := λ _ _ top30 _ _ _ _ => top30
def bot30 : Ty30 := λ _ _ _ bot30 _ _ _ => bot30

def arr30 : Ty30 → Ty30 → Ty30
 := λ A B Ty30 nat30 top30 bot30 arr30 prod sum =>
     arr30 (A Ty30 nat30 top30 bot30 arr30 prod sum) (B Ty30 nat30 top30 bot30 arr30 prod sum)

def prod30 : Ty30 → Ty30 → Ty30
 := λ A B Ty30 nat30 top30 bot30 arr30 prod30 sum =>
     prod30 (A Ty30 nat30 top30 bot30 arr30 prod30 sum) (B Ty30 nat30 top30 bot30 arr30 prod30 sum)

def sum30 : Ty30 → Ty30 → Ty30
 := λ A B Ty30 nat30 top30 bot30 arr30 prod30 sum30 =>
     sum30 (A Ty30 nat30 top30 bot30 arr30 prod30 sum30) (B Ty30 nat30 top30 bot30 arr30 prod30 sum30)

def Con30 : Type 1
 := ∀ (Con30  : Type)
      (nil  : Con30)
      (snoc : Con30 → Ty30 → Con30)
    , Con30

def nil30 : Con30
 := λ Con30 nil30 snoc => nil30

def snoc30 : Con30 → Ty30 → Con30
 := λ Γ A Con30 nil30 snoc30 => snoc30 (Γ Con30 nil30 snoc30) A

def Var30 : Con30 → Ty30 → Type 1
 := λ Γ A =>
   ∀ (Var30 : Con30 → Ty30 → Type)
     (vz  : ∀{Γ A}, Var30 (snoc30 Γ A) A)
     (vs  : ∀{Γ B A}, Var30 Γ A → Var30 (snoc30 Γ B) A)
   , Var30 Γ A

def vz30 : ∀ {Γ A}, Var30 (snoc30 Γ A) A
 := λ Var30 vz30 vs => vz30

def vs30 : ∀ {Γ B A}, Var30 Γ A → Var30 (snoc30 Γ B) A
 := λ x Var30 vz30 vs30 => vs30 (x Var30 vz30 vs30)

def Tm30 : Con30 → Ty30 → Type 1
 := λ Γ A =>
   ∀ (Tm30  : Con30 → Ty30 → Type)
     (var : ∀ {Γ A}, Var30 Γ A → Tm30 Γ A)
     (lam : ∀ {Γ A B}, (Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B)))
     (app   : ∀ {Γ A B}   , Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B)
     (tt    : ∀ {Γ}       , Tm30 Γ top30)
     (pair  : ∀ {Γ A B}   , Tm30 Γ A → Tm30 Γ B → Tm30 Γ (prod30 A B))
     (fst   : ∀ {Γ A B}   , Tm30 Γ (prod30 A B) → Tm30 Γ A)
     (snd   : ∀ {Γ A B}   , Tm30 Γ (prod30 A B) → Tm30 Γ B)
     (left  : ∀ {Γ A B}   , Tm30 Γ A → Tm30 Γ (sum30 A B))
     (right : ∀ {Γ A B}   , Tm30 Γ B → Tm30 Γ (sum30 A B))
     (case  : ∀ {Γ A B C} , Tm30 Γ (sum30 A B) → Tm30 Γ (arr30 A C) → Tm30 Γ (arr30 B C) → Tm30 Γ C)
     (zero  : ∀ {Γ}       , Tm30 Γ nat30)
     (suc   : ∀ {Γ}       , Tm30 Γ nat30 → Tm30 Γ nat30)
     (rec   : ∀ {Γ A}     , Tm30 Γ nat30 → Tm30 Γ (arr30 nat30 (arr30 A A)) → Tm30 Γ A → Tm30 Γ A)
   , Tm30 Γ A

def var30 : ∀ {Γ A}, Var30 Γ A → Tm30 Γ A
 := λ x Tm30 var30 lam app tt pair fst snd left right case zero suc rec =>
     var30 x

def lam30 : ∀ {Γ A B} , Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B)
 := λ t Tm30 var30 lam30 app tt pair fst snd left right case zero suc rec =>
     lam30 (t Tm30 var30 lam30 app tt pair fst snd left right case zero suc rec)

def app30 : ∀ {Γ A B} , Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B
 := λ t u Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec =>
     app30 (t Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec)
         (u Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec)

def tt30 : ∀ {Γ} , Tm30 Γ top30
 := λ Tm30 var30 lam30 app30 tt30 pair fst snd left right case zero suc rec => tt30

def pair30 : ∀ {Γ A B} , Tm30 Γ A → Tm30 Γ B → Tm30 Γ (prod30 A B)
 := λ t u Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec =>
     pair30 (t Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec)
          (u Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec)

def fst30 : ∀ {Γ A B} , Tm30 Γ (prod30 A B) → Tm30 Γ A
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd left right case zero suc rec =>
     fst30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd left right case zero suc rec)

def snd30 : ∀ {Γ A B} , Tm30 Γ (prod30 A B) → Tm30 Γ B
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left right case zero suc rec =>
     snd30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left right case zero suc rec)

def left30 : ∀ {Γ A B} , Tm30 Γ A → Tm30 Γ (sum30 A B)
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right case zero suc rec =>
     left30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right case zero suc rec)

def right30 : ∀ {Γ A B} , Tm30 Γ B → Tm30 Γ (sum30 A B)
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case zero suc rec =>
     right30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case zero suc rec)

def case30 : ∀ {Γ A B C} , Tm30 Γ (sum30 A B) → Tm30 Γ (arr30 A C) → Tm30 Γ (arr30 B C) → Tm30 Γ C
 := λ t u v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec =>
     case30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)
          (u Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)
          (v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)

def zero30  : ∀ {Γ} , Tm30 Γ nat30
 := λ Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc rec => zero30

def suc30 : ∀ {Γ} , Tm30 Γ nat30 → Tm30 Γ nat30
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec =>
   suc30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec)

def rec30 : ∀ {Γ A} , Tm30 Γ nat30 → Tm30 Γ (arr30 nat30 (arr30 A A)) → Tm30 Γ A → Tm30 Γ A
 := λ t u v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30 =>
     rec30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)
         (u Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)
         (v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)

def v030 : ∀ {Γ A}, Tm30 (snoc30 Γ A) A
 := var30 vz30

def v130 : ∀ {Γ A B}, Tm30 (snoc30 (snoc30 Γ A) B) A
 := var30 (vs30 vz30)

def v230 : ∀ {Γ A B C}, Tm30 (snoc30 (snoc30 (snoc30 Γ A) B) C) A
 := var30 (vs30 (vs30 vz30))

def v330 : ∀ {Γ A B C D}, Tm30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) A
 := var30 (vs30 (vs30 (vs30 vz30)))

def tbool30 : Ty30
 := sum30 top30 top30

def ttrue30 : ∀ {Γ}, Tm30 Γ tbool30
 := left30 tt30

def tfalse30 : ∀ {Γ}, Tm30 Γ tbool30
 := right30 tt30

def ifthenelse30 : ∀ {Γ A}, Tm30 Γ (arr30 tbool30 (arr30 A (arr30 A A)))
 := lam30 (lam30 (lam30 (case30 v230 (lam30 v230) (lam30 v130))))

def times430 : ∀ {Γ A}, Tm30 Γ (arr30 (arr30 A A) (arr30 A A))
  := lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030)))))

def add30 : ∀ {Γ}, Tm30 Γ (arr30 nat30 (arr30 nat30 nat30))
 := lam30 (rec30 v030
      (lam30 (lam30 (lam30 (suc30 (app30 v130 v030)))))
      (lam30 v030))

def mul30 : ∀ {Γ}, Tm30 Γ (arr30 nat30 (arr30 nat30 nat30))
 := lam30 (rec30 v030
     (lam30 (lam30 (lam30 (app30 (app30 add30 (app30 v130 v030)) v030))))
     (lam30 zero30))

def fact30 : ∀ {Γ}, Tm30 Γ (arr30 nat30 nat30)
 := lam30 (rec30 v030 (lam30 (lam30 (app30 (app30 mul30 (suc30 v130)) v030)))
        (suc30 zero30))
def Ty31 : Type 1
 := ∀ (Ty31           : Type)
      (nat top bot  : Ty31)
      (arr prod sum : Ty31 → Ty31 → Ty31)
    , Ty31

def nat31 : Ty31 := λ _ nat31 _ _ _ _ _ => nat31
def top31 : Ty31 := λ _ _ top31 _ _ _ _ => top31
def bot31 : Ty31 := λ _ _ _ bot31 _ _ _ => bot31

def arr31 : Ty31 → Ty31 → Ty31
 := λ A B Ty31 nat31 top31 bot31 arr31 prod sum =>
     arr31 (A Ty31 nat31 top31 bot31 arr31 prod sum) (B Ty31 nat31 top31 bot31 arr31 prod sum)

def prod31 : Ty31 → Ty31 → Ty31
 := λ A B Ty31 nat31 top31 bot31 arr31 prod31 sum =>
     prod31 (A Ty31 nat31 top31 bot31 arr31 prod31 sum) (B Ty31 nat31 top31 bot31 arr31 prod31 sum)

def sum31 : Ty31 → Ty31 → Ty31
 := λ A B Ty31 nat31 top31 bot31 arr31 prod31 sum31 =>
     sum31 (A Ty31 nat31 top31 bot31 arr31 prod31 sum31) (B Ty31 nat31 top31 bot31 arr31 prod31 sum31)

def Con31 : Type 1
 := ∀ (Con31  : Type)
      (nil  : Con31)
      (snoc : Con31 → Ty31 → Con31)
    , Con31

def nil31 : Con31
 := λ Con31 nil31 snoc => nil31

def snoc31 : Con31 → Ty31 → Con31
 := λ Γ A Con31 nil31 snoc31 => snoc31 (Γ Con31 nil31 snoc31) A

def Var31 : Con31 → Ty31 → Type 1
 := λ Γ A =>
   ∀ (Var31 : Con31 → Ty31 → Type)
     (vz  : ∀{Γ A}, Var31 (snoc31 Γ A) A)
     (vs  : ∀{Γ B A}, Var31 Γ A → Var31 (snoc31 Γ B) A)
   , Var31 Γ A

def vz31 : ∀ {Γ A}, Var31 (snoc31 Γ A) A
 := λ Var31 vz31 vs => vz31

def vs31 : ∀ {Γ B A}, Var31 Γ A → Var31 (snoc31 Γ B) A
 := λ x Var31 vz31 vs31 => vs31 (x Var31 vz31 vs31)

def Tm31 : Con31 → Ty31 → Type 1
 := λ Γ A =>
   ∀ (Tm31  : Con31 → Ty31 → Type)
     (var : ∀ {Γ A}, Var31 Γ A → Tm31 Γ A)
     (lam : ∀ {Γ A B}, (Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B)))
     (app   : ∀ {Γ A B}   , Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B)
     (tt    : ∀ {Γ}       , Tm31 Γ top31)
     (pair  : ∀ {Γ A B}   , Tm31 Γ A → Tm31 Γ B → Tm31 Γ (prod31 A B))
     (fst   : ∀ {Γ A B}   , Tm31 Γ (prod31 A B) → Tm31 Γ A)
     (snd   : ∀ {Γ A B}   , Tm31 Γ (prod31 A B) → Tm31 Γ B)
     (left  : ∀ {Γ A B}   , Tm31 Γ A → Tm31 Γ (sum31 A B))
     (right : ∀ {Γ A B}   , Tm31 Γ B → Tm31 Γ (sum31 A B))
     (case  : ∀ {Γ A B C} , Tm31 Γ (sum31 A B) → Tm31 Γ (arr31 A C) → Tm31 Γ (arr31 B C) → Tm31 Γ C)
     (zero  : ∀ {Γ}       , Tm31 Γ nat31)
     (suc   : ∀ {Γ}       , Tm31 Γ nat31 → Tm31 Γ nat31)
     (rec   : ∀ {Γ A}     , Tm31 Γ nat31 → Tm31 Γ (arr31 nat31 (arr31 A A)) → Tm31 Γ A → Tm31 Γ A)
   , Tm31 Γ A

def var31 : ∀ {Γ A}, Var31 Γ A → Tm31 Γ A
 := λ x Tm31 var31 lam app tt pair fst snd left right case zero suc rec =>
     var31 x

def lam31 : ∀ {Γ A B} , Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B)
 := λ t Tm31 var31 lam31 app tt pair fst snd left right case zero suc rec =>
     lam31 (t Tm31 var31 lam31 app tt pair fst snd left right case zero suc rec)

def app31 : ∀ {Γ A B} , Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B
 := λ t u Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec =>
     app31 (t Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec)
         (u Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec)

def tt31 : ∀ {Γ} , Tm31 Γ top31
 := λ Tm31 var31 lam31 app31 tt31 pair fst snd left right case zero suc rec => tt31

def pair31 : ∀ {Γ A B} , Tm31 Γ A → Tm31 Γ B → Tm31 Γ (prod31 A B)
 := λ t u Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec =>
     pair31 (t Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec)
          (u Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec)

def fst31 : ∀ {Γ A B} , Tm31 Γ (prod31 A B) → Tm31 Γ A
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd left right case zero suc rec =>
     fst31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd left right case zero suc rec)

def snd31 : ∀ {Γ A B} , Tm31 Γ (prod31 A B) → Tm31 Γ B
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left right case zero suc rec =>
     snd31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left right case zero suc rec)

def left31 : ∀ {Γ A B} , Tm31 Γ A → Tm31 Γ (sum31 A B)
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right case zero suc rec =>
     left31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right case zero suc rec)

def right31 : ∀ {Γ A B} , Tm31 Γ B → Tm31 Γ (sum31 A B)
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case zero suc rec =>
     right31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case zero suc rec)

def case31 : ∀ {Γ A B C} , Tm31 Γ (sum31 A B) → Tm31 Γ (arr31 A C) → Tm31 Γ (arr31 B C) → Tm31 Γ C
 := λ t u v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec =>
     case31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)
          (u Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)
          (v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)

def zero31  : ∀ {Γ} , Tm31 Γ nat31
 := λ Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc rec => zero31

def suc31 : ∀ {Γ} , Tm31 Γ nat31 → Tm31 Γ nat31
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec =>
   suc31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec)

def rec31 : ∀ {Γ A} , Tm31 Γ nat31 → Tm31 Γ (arr31 nat31 (arr31 A A)) → Tm31 Γ A → Tm31 Γ A
 := λ t u v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31 =>
     rec31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)
         (u Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)
         (v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)

def v031 : ∀ {Γ A}, Tm31 (snoc31 Γ A) A
 := var31 vz31

def v131 : ∀ {Γ A B}, Tm31 (snoc31 (snoc31 Γ A) B) A
 := var31 (vs31 vz31)

def v231 : ∀ {Γ A B C}, Tm31 (snoc31 (snoc31 (snoc31 Γ A) B) C) A
 := var31 (vs31 (vs31 vz31))

def v331 : ∀ {Γ A B C D}, Tm31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) A
 := var31 (vs31 (vs31 (vs31 vz31)))

def tbool31 : Ty31
 := sum31 top31 top31

def ttrue31 : ∀ {Γ}, Tm31 Γ tbool31
 := left31 tt31

def tfalse31 : ∀ {Γ}, Tm31 Γ tbool31
 := right31 tt31

def ifthenelse31 : ∀ {Γ A}, Tm31 Γ (arr31 tbool31 (arr31 A (arr31 A A)))
 := lam31 (lam31 (lam31 (case31 v231 (lam31 v231) (lam31 v131))))

def times431 : ∀ {Γ A}, Tm31 Γ (arr31 (arr31 A A) (arr31 A A))
  := lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031)))))

def add31 : ∀ {Γ}, Tm31 Γ (arr31 nat31 (arr31 nat31 nat31))
 := lam31 (rec31 v031
      (lam31 (lam31 (lam31 (suc31 (app31 v131 v031)))))
      (lam31 v031))

def mul31 : ∀ {Γ}, Tm31 Γ (arr31 nat31 (arr31 nat31 nat31))
 := lam31 (rec31 v031
     (lam31 (lam31 (lam31 (app31 (app31 add31 (app31 v131 v031)) v031))))
     (lam31 zero31))

def fact31 : ∀ {Γ}, Tm31 Γ (arr31 nat31 nat31)
 := lam31 (rec31 v031 (lam31 (lam31 (app31 (app31 mul31 (suc31 v131)) v031)))
        (suc31 zero31))
def Ty32 : Type 1
 := ∀ (Ty32           : Type)
      (nat top bot  : Ty32)
      (arr prod sum : Ty32 → Ty32 → Ty32)
    , Ty32

def nat32 : Ty32 := λ _ nat32 _ _ _ _ _ => nat32
def top32 : Ty32 := λ _ _ top32 _ _ _ _ => top32
def bot32 : Ty32 := λ _ _ _ bot32 _ _ _ => bot32

def arr32 : Ty32 → Ty32 → Ty32
 := λ A B Ty32 nat32 top32 bot32 arr32 prod sum =>
     arr32 (A Ty32 nat32 top32 bot32 arr32 prod sum) (B Ty32 nat32 top32 bot32 arr32 prod sum)

def prod32 : Ty32 → Ty32 → Ty32
 := λ A B Ty32 nat32 top32 bot32 arr32 prod32 sum =>
     prod32 (A Ty32 nat32 top32 bot32 arr32 prod32 sum) (B Ty32 nat32 top32 bot32 arr32 prod32 sum)

def sum32 : Ty32 → Ty32 → Ty32
 := λ A B Ty32 nat32 top32 bot32 arr32 prod32 sum32 =>
     sum32 (A Ty32 nat32 top32 bot32 arr32 prod32 sum32) (B Ty32 nat32 top32 bot32 arr32 prod32 sum32)

def Con32 : Type 1
 := ∀ (Con32  : Type)
      (nil  : Con32)
      (snoc : Con32 → Ty32 → Con32)
    , Con32

def nil32 : Con32
 := λ Con32 nil32 snoc => nil32

def snoc32 : Con32 → Ty32 → Con32
 := λ Γ A Con32 nil32 snoc32 => snoc32 (Γ Con32 nil32 snoc32) A

def Var32 : Con32 → Ty32 → Type 1
 := λ Γ A =>
   ∀ (Var32 : Con32 → Ty32 → Type)
     (vz  : ∀{Γ A}, Var32 (snoc32 Γ A) A)
     (vs  : ∀{Γ B A}, Var32 Γ A → Var32 (snoc32 Γ B) A)
   , Var32 Γ A

def vz32 : ∀ {Γ A}, Var32 (snoc32 Γ A) A
 := λ Var32 vz32 vs => vz32

def vs32 : ∀ {Γ B A}, Var32 Γ A → Var32 (snoc32 Γ B) A
 := λ x Var32 vz32 vs32 => vs32 (x Var32 vz32 vs32)

def Tm32 : Con32 → Ty32 → Type 1
 := λ Γ A =>
   ∀ (Tm32  : Con32 → Ty32 → Type)
     (var : ∀ {Γ A}, Var32 Γ A → Tm32 Γ A)
     (lam : ∀ {Γ A B}, (Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B)))
     (app   : ∀ {Γ A B}   , Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B)
     (tt    : ∀ {Γ}       , Tm32 Γ top32)
     (pair  : ∀ {Γ A B}   , Tm32 Γ A → Tm32 Γ B → Tm32 Γ (prod32 A B))
     (fst   : ∀ {Γ A B}   , Tm32 Γ (prod32 A B) → Tm32 Γ A)
     (snd   : ∀ {Γ A B}   , Tm32 Γ (prod32 A B) → Tm32 Γ B)
     (left  : ∀ {Γ A B}   , Tm32 Γ A → Tm32 Γ (sum32 A B))
     (right : ∀ {Γ A B}   , Tm32 Γ B → Tm32 Γ (sum32 A B))
     (case  : ∀ {Γ A B C} , Tm32 Γ (sum32 A B) → Tm32 Γ (arr32 A C) → Tm32 Γ (arr32 B C) → Tm32 Γ C)
     (zero  : ∀ {Γ}       , Tm32 Γ nat32)
     (suc   : ∀ {Γ}       , Tm32 Γ nat32 → Tm32 Γ nat32)
     (rec   : ∀ {Γ A}     , Tm32 Γ nat32 → Tm32 Γ (arr32 nat32 (arr32 A A)) → Tm32 Γ A → Tm32 Γ A)
   , Tm32 Γ A

def var32 : ∀ {Γ A}, Var32 Γ A → Tm32 Γ A
 := λ x Tm32 var32 lam app tt pair fst snd left right case zero suc rec =>
     var32 x

def lam32 : ∀ {Γ A B} , Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B)
 := λ t Tm32 var32 lam32 app tt pair fst snd left right case zero suc rec =>
     lam32 (t Tm32 var32 lam32 app tt pair fst snd left right case zero suc rec)

def app32 : ∀ {Γ A B} , Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B
 := λ t u Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec =>
     app32 (t Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec)
         (u Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec)

def tt32 : ∀ {Γ} , Tm32 Γ top32
 := λ Tm32 var32 lam32 app32 tt32 pair fst snd left right case zero suc rec => tt32

def pair32 : ∀ {Γ A B} , Tm32 Γ A → Tm32 Γ B → Tm32 Γ (prod32 A B)
 := λ t u Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec =>
     pair32 (t Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec)
          (u Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec)

def fst32 : ∀ {Γ A B} , Tm32 Γ (prod32 A B) → Tm32 Γ A
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd left right case zero suc rec =>
     fst32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd left right case zero suc rec)

def snd32 : ∀ {Γ A B} , Tm32 Γ (prod32 A B) → Tm32 Γ B
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left right case zero suc rec =>
     snd32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left right case zero suc rec)

def left32 : ∀ {Γ A B} , Tm32 Γ A → Tm32 Γ (sum32 A B)
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right case zero suc rec =>
     left32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right case zero suc rec)

def right32 : ∀ {Γ A B} , Tm32 Γ B → Tm32 Γ (sum32 A B)
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case zero suc rec =>
     right32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case zero suc rec)

def case32 : ∀ {Γ A B C} , Tm32 Γ (sum32 A B) → Tm32 Γ (arr32 A C) → Tm32 Γ (arr32 B C) → Tm32 Γ C
 := λ t u v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec =>
     case32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)
          (u Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)
          (v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)

def zero32  : ∀ {Γ} , Tm32 Γ nat32
 := λ Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc rec => zero32

def suc32 : ∀ {Γ} , Tm32 Γ nat32 → Tm32 Γ nat32
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec =>
   suc32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec)

def rec32 : ∀ {Γ A} , Tm32 Γ nat32 → Tm32 Γ (arr32 nat32 (arr32 A A)) → Tm32 Γ A → Tm32 Γ A
 := λ t u v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32 =>
     rec32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)
         (u Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)
         (v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)

def v032 : ∀ {Γ A}, Tm32 (snoc32 Γ A) A
 := var32 vz32

def v132 : ∀ {Γ A B}, Tm32 (snoc32 (snoc32 Γ A) B) A
 := var32 (vs32 vz32)

def v232 : ∀ {Γ A B C}, Tm32 (snoc32 (snoc32 (snoc32 Γ A) B) C) A
 := var32 (vs32 (vs32 vz32))

def v332 : ∀ {Γ A B C D}, Tm32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) A
 := var32 (vs32 (vs32 (vs32 vz32)))

def tbool32 : Ty32
 := sum32 top32 top32

def ttrue32 : ∀ {Γ}, Tm32 Γ tbool32
 := left32 tt32

def tfalse32 : ∀ {Γ}, Tm32 Γ tbool32
 := right32 tt32

def ifthenelse32 : ∀ {Γ A}, Tm32 Γ (arr32 tbool32 (arr32 A (arr32 A A)))
 := lam32 (lam32 (lam32 (case32 v232 (lam32 v232) (lam32 v132))))

def times432 : ∀ {Γ A}, Tm32 Γ (arr32 (arr32 A A) (arr32 A A))
  := lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032)))))

def add32 : ∀ {Γ}, Tm32 Γ (arr32 nat32 (arr32 nat32 nat32))
 := lam32 (rec32 v032
      (lam32 (lam32 (lam32 (suc32 (app32 v132 v032)))))
      (lam32 v032))

def mul32 : ∀ {Γ}, Tm32 Γ (arr32 nat32 (arr32 nat32 nat32))
 := lam32 (rec32 v032
     (lam32 (lam32 (lam32 (app32 (app32 add32 (app32 v132 v032)) v032))))
     (lam32 zero32))

def fact32 : ∀ {Γ}, Tm32 Γ (arr32 nat32 nat32)
 := lam32 (rec32 v032 (lam32 (lam32 (app32 (app32 mul32 (suc32 v132)) v032)))
        (suc32 zero32))
def Ty33 : Type 1
 := ∀ (Ty33           : Type)
      (nat top bot  : Ty33)
      (arr prod sum : Ty33 → Ty33 → Ty33)
    , Ty33

def nat33 : Ty33 := λ _ nat33 _ _ _ _ _ => nat33
def top33 : Ty33 := λ _ _ top33 _ _ _ _ => top33
def bot33 : Ty33 := λ _ _ _ bot33 _ _ _ => bot33

def arr33 : Ty33 → Ty33 → Ty33
 := λ A B Ty33 nat33 top33 bot33 arr33 prod sum =>
     arr33 (A Ty33 nat33 top33 bot33 arr33 prod sum) (B Ty33 nat33 top33 bot33 arr33 prod sum)

def prod33 : Ty33 → Ty33 → Ty33
 := λ A B Ty33 nat33 top33 bot33 arr33 prod33 sum =>
     prod33 (A Ty33 nat33 top33 bot33 arr33 prod33 sum) (B Ty33 nat33 top33 bot33 arr33 prod33 sum)

def sum33 : Ty33 → Ty33 → Ty33
 := λ A B Ty33 nat33 top33 bot33 arr33 prod33 sum33 =>
     sum33 (A Ty33 nat33 top33 bot33 arr33 prod33 sum33) (B Ty33 nat33 top33 bot33 arr33 prod33 sum33)

def Con33 : Type 1
 := ∀ (Con33  : Type)
      (nil  : Con33)
      (snoc : Con33 → Ty33 → Con33)
    , Con33

def nil33 : Con33
 := λ Con33 nil33 snoc => nil33

def snoc33 : Con33 → Ty33 → Con33
 := λ Γ A Con33 nil33 snoc33 => snoc33 (Γ Con33 nil33 snoc33) A

def Var33 : Con33 → Ty33 → Type 1
 := λ Γ A =>
   ∀ (Var33 : Con33 → Ty33 → Type)
     (vz  : ∀{Γ A}, Var33 (snoc33 Γ A) A)
     (vs  : ∀{Γ B A}, Var33 Γ A → Var33 (snoc33 Γ B) A)
   , Var33 Γ A

def vz33 : ∀ {Γ A}, Var33 (snoc33 Γ A) A
 := λ Var33 vz33 vs => vz33

def vs33 : ∀ {Γ B A}, Var33 Γ A → Var33 (snoc33 Γ B) A
 := λ x Var33 vz33 vs33 => vs33 (x Var33 vz33 vs33)

def Tm33 : Con33 → Ty33 → Type 1
 := λ Γ A =>
   ∀ (Tm33  : Con33 → Ty33 → Type)
     (var : ∀ {Γ A}, Var33 Γ A → Tm33 Γ A)
     (lam : ∀ {Γ A B}, (Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B)))
     (app   : ∀ {Γ A B}   , Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B)
     (tt    : ∀ {Γ}       , Tm33 Γ top33)
     (pair  : ∀ {Γ A B}   , Tm33 Γ A → Tm33 Γ B → Tm33 Γ (prod33 A B))
     (fst   : ∀ {Γ A B}   , Tm33 Γ (prod33 A B) → Tm33 Γ A)
     (snd   : ∀ {Γ A B}   , Tm33 Γ (prod33 A B) → Tm33 Γ B)
     (left  : ∀ {Γ A B}   , Tm33 Γ A → Tm33 Γ (sum33 A B))
     (right : ∀ {Γ A B}   , Tm33 Γ B → Tm33 Γ (sum33 A B))
     (case  : ∀ {Γ A B C} , Tm33 Γ (sum33 A B) → Tm33 Γ (arr33 A C) → Tm33 Γ (arr33 B C) → Tm33 Γ C)
     (zero  : ∀ {Γ}       , Tm33 Γ nat33)
     (suc   : ∀ {Γ}       , Tm33 Γ nat33 → Tm33 Γ nat33)
     (rec   : ∀ {Γ A}     , Tm33 Γ nat33 → Tm33 Γ (arr33 nat33 (arr33 A A)) → Tm33 Γ A → Tm33 Γ A)
   , Tm33 Γ A

def var33 : ∀ {Γ A}, Var33 Γ A → Tm33 Γ A
 := λ x Tm33 var33 lam app tt pair fst snd left right case zero suc rec =>
     var33 x

def lam33 : ∀ {Γ A B} , Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B)
 := λ t Tm33 var33 lam33 app tt pair fst snd left right case zero suc rec =>
     lam33 (t Tm33 var33 lam33 app tt pair fst snd left right case zero suc rec)

def app33 : ∀ {Γ A B} , Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B
 := λ t u Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec =>
     app33 (t Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec)
         (u Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec)

def tt33 : ∀ {Γ} , Tm33 Γ top33
 := λ Tm33 var33 lam33 app33 tt33 pair fst snd left right case zero suc rec => tt33

def pair33 : ∀ {Γ A B} , Tm33 Γ A → Tm33 Γ B → Tm33 Γ (prod33 A B)
 := λ t u Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec =>
     pair33 (t Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec)
          (u Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec)

def fst33 : ∀ {Γ A B} , Tm33 Γ (prod33 A B) → Tm33 Γ A
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd left right case zero suc rec =>
     fst33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd left right case zero suc rec)

def snd33 : ∀ {Γ A B} , Tm33 Γ (prod33 A B) → Tm33 Γ B
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left right case zero suc rec =>
     snd33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left right case zero suc rec)

def left33 : ∀ {Γ A B} , Tm33 Γ A → Tm33 Γ (sum33 A B)
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right case zero suc rec =>
     left33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right case zero suc rec)

def right33 : ∀ {Γ A B} , Tm33 Γ B → Tm33 Γ (sum33 A B)
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case zero suc rec =>
     right33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case zero suc rec)

def case33 : ∀ {Γ A B C} , Tm33 Γ (sum33 A B) → Tm33 Γ (arr33 A C) → Tm33 Γ (arr33 B C) → Tm33 Γ C
 := λ t u v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec =>
     case33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)
          (u Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)
          (v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)

def zero33  : ∀ {Γ} , Tm33 Γ nat33
 := λ Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc rec => zero33

def suc33 : ∀ {Γ} , Tm33 Γ nat33 → Tm33 Γ nat33
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec =>
   suc33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec)

def rec33 : ∀ {Γ A} , Tm33 Γ nat33 → Tm33 Γ (arr33 nat33 (arr33 A A)) → Tm33 Γ A → Tm33 Γ A
 := λ t u v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33 =>
     rec33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)
         (u Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)
         (v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)

def v033 : ∀ {Γ A}, Tm33 (snoc33 Γ A) A
 := var33 vz33

def v133 : ∀ {Γ A B}, Tm33 (snoc33 (snoc33 Γ A) B) A
 := var33 (vs33 vz33)

def v233 : ∀ {Γ A B C}, Tm33 (snoc33 (snoc33 (snoc33 Γ A) B) C) A
 := var33 (vs33 (vs33 vz33))

def v333 : ∀ {Γ A B C D}, Tm33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) A
 := var33 (vs33 (vs33 (vs33 vz33)))

def tbool33 : Ty33
 := sum33 top33 top33

def ttrue33 : ∀ {Γ}, Tm33 Γ tbool33
 := left33 tt33

def tfalse33 : ∀ {Γ}, Tm33 Γ tbool33
 := right33 tt33

def ifthenelse33 : ∀ {Γ A}, Tm33 Γ (arr33 tbool33 (arr33 A (arr33 A A)))
 := lam33 (lam33 (lam33 (case33 v233 (lam33 v233) (lam33 v133))))

def times433 : ∀ {Γ A}, Tm33 Γ (arr33 (arr33 A A) (arr33 A A))
  := lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033)))))

def add33 : ∀ {Γ}, Tm33 Γ (arr33 nat33 (arr33 nat33 nat33))
 := lam33 (rec33 v033
      (lam33 (lam33 (lam33 (suc33 (app33 v133 v033)))))
      (lam33 v033))

def mul33 : ∀ {Γ}, Tm33 Γ (arr33 nat33 (arr33 nat33 nat33))
 := lam33 (rec33 v033
     (lam33 (lam33 (lam33 (app33 (app33 add33 (app33 v133 v033)) v033))))
     (lam33 zero33))

def fact33 : ∀ {Γ}, Tm33 Γ (arr33 nat33 nat33)
 := lam33 (rec33 v033 (lam33 (lam33 (app33 (app33 mul33 (suc33 v133)) v033)))
        (suc33 zero33))
def Ty34 : Type 1
 := ∀ (Ty34           : Type)
      (nat top bot  : Ty34)
      (arr prod sum : Ty34 → Ty34 → Ty34)
    , Ty34

def nat34 : Ty34 := λ _ nat34 _ _ _ _ _ => nat34
def top34 : Ty34 := λ _ _ top34 _ _ _ _ => top34
def bot34 : Ty34 := λ _ _ _ bot34 _ _ _ => bot34

def arr34 : Ty34 → Ty34 → Ty34
 := λ A B Ty34 nat34 top34 bot34 arr34 prod sum =>
     arr34 (A Ty34 nat34 top34 bot34 arr34 prod sum) (B Ty34 nat34 top34 bot34 arr34 prod sum)

def prod34 : Ty34 → Ty34 → Ty34
 := λ A B Ty34 nat34 top34 bot34 arr34 prod34 sum =>
     prod34 (A Ty34 nat34 top34 bot34 arr34 prod34 sum) (B Ty34 nat34 top34 bot34 arr34 prod34 sum)

def sum34 : Ty34 → Ty34 → Ty34
 := λ A B Ty34 nat34 top34 bot34 arr34 prod34 sum34 =>
     sum34 (A Ty34 nat34 top34 bot34 arr34 prod34 sum34) (B Ty34 nat34 top34 bot34 arr34 prod34 sum34)

def Con34 : Type 1
 := ∀ (Con34  : Type)
      (nil  : Con34)
      (snoc : Con34 → Ty34 → Con34)
    , Con34

def nil34 : Con34
 := λ Con34 nil34 snoc => nil34

def snoc34 : Con34 → Ty34 → Con34
 := λ Γ A Con34 nil34 snoc34 => snoc34 (Γ Con34 nil34 snoc34) A

def Var34 : Con34 → Ty34 → Type 1
 := λ Γ A =>
   ∀ (Var34 : Con34 → Ty34 → Type)
     (vz  : ∀{Γ A}, Var34 (snoc34 Γ A) A)
     (vs  : ∀{Γ B A}, Var34 Γ A → Var34 (snoc34 Γ B) A)
   , Var34 Γ A

def vz34 : ∀ {Γ A}, Var34 (snoc34 Γ A) A
 := λ Var34 vz34 vs => vz34

def vs34 : ∀ {Γ B A}, Var34 Γ A → Var34 (snoc34 Γ B) A
 := λ x Var34 vz34 vs34 => vs34 (x Var34 vz34 vs34)

def Tm34 : Con34 → Ty34 → Type 1
 := λ Γ A =>
   ∀ (Tm34  : Con34 → Ty34 → Type)
     (var : ∀ {Γ A}, Var34 Γ A → Tm34 Γ A)
     (lam : ∀ {Γ A B}, (Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B)))
     (app   : ∀ {Γ A B}   , Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B)
     (tt    : ∀ {Γ}       , Tm34 Γ top34)
     (pair  : ∀ {Γ A B}   , Tm34 Γ A → Tm34 Γ B → Tm34 Γ (prod34 A B))
     (fst   : ∀ {Γ A B}   , Tm34 Γ (prod34 A B) → Tm34 Γ A)
     (snd   : ∀ {Γ A B}   , Tm34 Γ (prod34 A B) → Tm34 Γ B)
     (left  : ∀ {Γ A B}   , Tm34 Γ A → Tm34 Γ (sum34 A B))
     (right : ∀ {Γ A B}   , Tm34 Γ B → Tm34 Γ (sum34 A B))
     (case  : ∀ {Γ A B C} , Tm34 Γ (sum34 A B) → Tm34 Γ (arr34 A C) → Tm34 Γ (arr34 B C) → Tm34 Γ C)
     (zero  : ∀ {Γ}       , Tm34 Γ nat34)
     (suc   : ∀ {Γ}       , Tm34 Γ nat34 → Tm34 Γ nat34)
     (rec   : ∀ {Γ A}     , Tm34 Γ nat34 → Tm34 Γ (arr34 nat34 (arr34 A A)) → Tm34 Γ A → Tm34 Γ A)
   , Tm34 Γ A

def var34 : ∀ {Γ A}, Var34 Γ A → Tm34 Γ A
 := λ x Tm34 var34 lam app tt pair fst snd left right case zero suc rec =>
     var34 x

def lam34 : ∀ {Γ A B} , Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B)
 := λ t Tm34 var34 lam34 app tt pair fst snd left right case zero suc rec =>
     lam34 (t Tm34 var34 lam34 app tt pair fst snd left right case zero suc rec)

def app34 : ∀ {Γ A B} , Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B
 := λ t u Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec =>
     app34 (t Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec)
         (u Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec)

def tt34 : ∀ {Γ} , Tm34 Γ top34
 := λ Tm34 var34 lam34 app34 tt34 pair fst snd left right case zero suc rec => tt34

def pair34 : ∀ {Γ A B} , Tm34 Γ A → Tm34 Γ B → Tm34 Γ (prod34 A B)
 := λ t u Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec =>
     pair34 (t Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec)
          (u Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec)

def fst34 : ∀ {Γ A B} , Tm34 Γ (prod34 A B) → Tm34 Γ A
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd left right case zero suc rec =>
     fst34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd left right case zero suc rec)

def snd34 : ∀ {Γ A B} , Tm34 Γ (prod34 A B) → Tm34 Γ B
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left right case zero suc rec =>
     snd34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left right case zero suc rec)

def left34 : ∀ {Γ A B} , Tm34 Γ A → Tm34 Γ (sum34 A B)
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right case zero suc rec =>
     left34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right case zero suc rec)

def right34 : ∀ {Γ A B} , Tm34 Γ B → Tm34 Γ (sum34 A B)
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case zero suc rec =>
     right34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case zero suc rec)

def case34 : ∀ {Γ A B C} , Tm34 Γ (sum34 A B) → Tm34 Γ (arr34 A C) → Tm34 Γ (arr34 B C) → Tm34 Γ C
 := λ t u v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec =>
     case34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)
          (u Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)
          (v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)

def zero34  : ∀ {Γ} , Tm34 Γ nat34
 := λ Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc rec => zero34

def suc34 : ∀ {Γ} , Tm34 Γ nat34 → Tm34 Γ nat34
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec =>
   suc34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec)

def rec34 : ∀ {Γ A} , Tm34 Γ nat34 → Tm34 Γ (arr34 nat34 (arr34 A A)) → Tm34 Γ A → Tm34 Γ A
 := λ t u v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34 =>
     rec34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)
         (u Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)
         (v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)

def v034 : ∀ {Γ A}, Tm34 (snoc34 Γ A) A
 := var34 vz34

def v134 : ∀ {Γ A B}, Tm34 (snoc34 (snoc34 Γ A) B) A
 := var34 (vs34 vz34)

def v234 : ∀ {Γ A B C}, Tm34 (snoc34 (snoc34 (snoc34 Γ A) B) C) A
 := var34 (vs34 (vs34 vz34))

def v334 : ∀ {Γ A B C D}, Tm34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) A
 := var34 (vs34 (vs34 (vs34 vz34)))

def tbool34 : Ty34
 := sum34 top34 top34

def ttrue34 : ∀ {Γ}, Tm34 Γ tbool34
 := left34 tt34

def tfalse34 : ∀ {Γ}, Tm34 Γ tbool34
 := right34 tt34

def ifthenelse34 : ∀ {Γ A}, Tm34 Γ (arr34 tbool34 (arr34 A (arr34 A A)))
 := lam34 (lam34 (lam34 (case34 v234 (lam34 v234) (lam34 v134))))

def times434 : ∀ {Γ A}, Tm34 Γ (arr34 (arr34 A A) (arr34 A A))
  := lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034)))))

def add34 : ∀ {Γ}, Tm34 Γ (arr34 nat34 (arr34 nat34 nat34))
 := lam34 (rec34 v034
      (lam34 (lam34 (lam34 (suc34 (app34 v134 v034)))))
      (lam34 v034))

def mul34 : ∀ {Γ}, Tm34 Γ (arr34 nat34 (arr34 nat34 nat34))
 := lam34 (rec34 v034
     (lam34 (lam34 (lam34 (app34 (app34 add34 (app34 v134 v034)) v034))))
     (lam34 zero34))

def fact34 : ∀ {Γ}, Tm34 Γ (arr34 nat34 nat34)
 := lam34 (rec34 v034 (lam34 (lam34 (app34 (app34 mul34 (suc34 v134)) v034)))
        (suc34 zero34))
def Ty35 : Type 1
 := ∀ (Ty35           : Type)
      (nat top bot  : Ty35)
      (arr prod sum : Ty35 → Ty35 → Ty35)
    , Ty35

def nat35 : Ty35 := λ _ nat35 _ _ _ _ _ => nat35
def top35 : Ty35 := λ _ _ top35 _ _ _ _ => top35
def bot35 : Ty35 := λ _ _ _ bot35 _ _ _ => bot35

def arr35 : Ty35 → Ty35 → Ty35
 := λ A B Ty35 nat35 top35 bot35 arr35 prod sum =>
     arr35 (A Ty35 nat35 top35 bot35 arr35 prod sum) (B Ty35 nat35 top35 bot35 arr35 prod sum)

def prod35 : Ty35 → Ty35 → Ty35
 := λ A B Ty35 nat35 top35 bot35 arr35 prod35 sum =>
     prod35 (A Ty35 nat35 top35 bot35 arr35 prod35 sum) (B Ty35 nat35 top35 bot35 arr35 prod35 sum)

def sum35 : Ty35 → Ty35 → Ty35
 := λ A B Ty35 nat35 top35 bot35 arr35 prod35 sum35 =>
     sum35 (A Ty35 nat35 top35 bot35 arr35 prod35 sum35) (B Ty35 nat35 top35 bot35 arr35 prod35 sum35)

def Con35 : Type 1
 := ∀ (Con35  : Type)
      (nil  : Con35)
      (snoc : Con35 → Ty35 → Con35)
    , Con35

def nil35 : Con35
 := λ Con35 nil35 snoc => nil35

def snoc35 : Con35 → Ty35 → Con35
 := λ Γ A Con35 nil35 snoc35 => snoc35 (Γ Con35 nil35 snoc35) A

def Var35 : Con35 → Ty35 → Type 1
 := λ Γ A =>
   ∀ (Var35 : Con35 → Ty35 → Type)
     (vz  : ∀{Γ A}, Var35 (snoc35 Γ A) A)
     (vs  : ∀{Γ B A}, Var35 Γ A → Var35 (snoc35 Γ B) A)
   , Var35 Γ A

def vz35 : ∀ {Γ A}, Var35 (snoc35 Γ A) A
 := λ Var35 vz35 vs => vz35

def vs35 : ∀ {Γ B A}, Var35 Γ A → Var35 (snoc35 Γ B) A
 := λ x Var35 vz35 vs35 => vs35 (x Var35 vz35 vs35)

def Tm35 : Con35 → Ty35 → Type 1
 := λ Γ A =>
   ∀ (Tm35  : Con35 → Ty35 → Type)
     (var : ∀ {Γ A}, Var35 Γ A → Tm35 Γ A)
     (lam : ∀ {Γ A B}, (Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B)))
     (app   : ∀ {Γ A B}   , Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B)
     (tt    : ∀ {Γ}       , Tm35 Γ top35)
     (pair  : ∀ {Γ A B}   , Tm35 Γ A → Tm35 Γ B → Tm35 Γ (prod35 A B))
     (fst   : ∀ {Γ A B}   , Tm35 Γ (prod35 A B) → Tm35 Γ A)
     (snd   : ∀ {Γ A B}   , Tm35 Γ (prod35 A B) → Tm35 Γ B)
     (left  : ∀ {Γ A B}   , Tm35 Γ A → Tm35 Γ (sum35 A B))
     (right : ∀ {Γ A B}   , Tm35 Γ B → Tm35 Γ (sum35 A B))
     (case  : ∀ {Γ A B C} , Tm35 Γ (sum35 A B) → Tm35 Γ (arr35 A C) → Tm35 Γ (arr35 B C) → Tm35 Γ C)
     (zero  : ∀ {Γ}       , Tm35 Γ nat35)
     (suc   : ∀ {Γ}       , Tm35 Γ nat35 → Tm35 Γ nat35)
     (rec   : ∀ {Γ A}     , Tm35 Γ nat35 → Tm35 Γ (arr35 nat35 (arr35 A A)) → Tm35 Γ A → Tm35 Γ A)
   , Tm35 Γ A

def var35 : ∀ {Γ A}, Var35 Γ A → Tm35 Γ A
 := λ x Tm35 var35 lam app tt pair fst snd left right case zero suc rec =>
     var35 x

def lam35 : ∀ {Γ A B} , Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B)
 := λ t Tm35 var35 lam35 app tt pair fst snd left right case zero suc rec =>
     lam35 (t Tm35 var35 lam35 app tt pair fst snd left right case zero suc rec)

def app35 : ∀ {Γ A B} , Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B
 := λ t u Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec =>
     app35 (t Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec)
         (u Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec)

def tt35 : ∀ {Γ} , Tm35 Γ top35
 := λ Tm35 var35 lam35 app35 tt35 pair fst snd left right case zero suc rec => tt35

def pair35 : ∀ {Γ A B} , Tm35 Γ A → Tm35 Γ B → Tm35 Γ (prod35 A B)
 := λ t u Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec =>
     pair35 (t Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec)
          (u Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec)

def fst35 : ∀ {Γ A B} , Tm35 Γ (prod35 A B) → Tm35 Γ A
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd left right case zero suc rec =>
     fst35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd left right case zero suc rec)

def snd35 : ∀ {Γ A B} , Tm35 Γ (prod35 A B) → Tm35 Γ B
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left right case zero suc rec =>
     snd35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left right case zero suc rec)

def left35 : ∀ {Γ A B} , Tm35 Γ A → Tm35 Γ (sum35 A B)
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right case zero suc rec =>
     left35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right case zero suc rec)

def right35 : ∀ {Γ A B} , Tm35 Γ B → Tm35 Γ (sum35 A B)
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case zero suc rec =>
     right35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case zero suc rec)

def case35 : ∀ {Γ A B C} , Tm35 Γ (sum35 A B) → Tm35 Γ (arr35 A C) → Tm35 Γ (arr35 B C) → Tm35 Γ C
 := λ t u v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec =>
     case35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)
          (u Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)
          (v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)

def zero35  : ∀ {Γ} , Tm35 Γ nat35
 := λ Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc rec => zero35

def suc35 : ∀ {Γ} , Tm35 Γ nat35 → Tm35 Γ nat35
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec =>
   suc35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec)

def rec35 : ∀ {Γ A} , Tm35 Γ nat35 → Tm35 Γ (arr35 nat35 (arr35 A A)) → Tm35 Γ A → Tm35 Γ A
 := λ t u v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35 =>
     rec35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)
         (u Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)
         (v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)

def v035 : ∀ {Γ A}, Tm35 (snoc35 Γ A) A
 := var35 vz35

def v135 : ∀ {Γ A B}, Tm35 (snoc35 (snoc35 Γ A) B) A
 := var35 (vs35 vz35)

def v235 : ∀ {Γ A B C}, Tm35 (snoc35 (snoc35 (snoc35 Γ A) B) C) A
 := var35 (vs35 (vs35 vz35))

def v335 : ∀ {Γ A B C D}, Tm35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) A
 := var35 (vs35 (vs35 (vs35 vz35)))

def tbool35 : Ty35
 := sum35 top35 top35

def ttrue35 : ∀ {Γ}, Tm35 Γ tbool35
 := left35 tt35

def tfalse35 : ∀ {Γ}, Tm35 Γ tbool35
 := right35 tt35

def ifthenelse35 : ∀ {Γ A}, Tm35 Γ (arr35 tbool35 (arr35 A (arr35 A A)))
 := lam35 (lam35 (lam35 (case35 v235 (lam35 v235) (lam35 v135))))

def times435 : ∀ {Γ A}, Tm35 Γ (arr35 (arr35 A A) (arr35 A A))
  := lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035)))))

def add35 : ∀ {Γ}, Tm35 Γ (arr35 nat35 (arr35 nat35 nat35))
 := lam35 (rec35 v035
      (lam35 (lam35 (lam35 (suc35 (app35 v135 v035)))))
      (lam35 v035))

def mul35 : ∀ {Γ}, Tm35 Γ (arr35 nat35 (arr35 nat35 nat35))
 := lam35 (rec35 v035
     (lam35 (lam35 (lam35 (app35 (app35 add35 (app35 v135 v035)) v035))))
     (lam35 zero35))

def fact35 : ∀ {Γ}, Tm35 Γ (arr35 nat35 nat35)
 := lam35 (rec35 v035 (lam35 (lam35 (app35 (app35 mul35 (suc35 v135)) v035)))
        (suc35 zero35))
def Ty36 : Type 1
 := ∀ (Ty36           : Type)
      (nat top bot  : Ty36)
      (arr prod sum : Ty36 → Ty36 → Ty36)
    , Ty36

def nat36 : Ty36 := λ _ nat36 _ _ _ _ _ => nat36
def top36 : Ty36 := λ _ _ top36 _ _ _ _ => top36
def bot36 : Ty36 := λ _ _ _ bot36 _ _ _ => bot36

def arr36 : Ty36 → Ty36 → Ty36
 := λ A B Ty36 nat36 top36 bot36 arr36 prod sum =>
     arr36 (A Ty36 nat36 top36 bot36 arr36 prod sum) (B Ty36 nat36 top36 bot36 arr36 prod sum)

def prod36 : Ty36 → Ty36 → Ty36
 := λ A B Ty36 nat36 top36 bot36 arr36 prod36 sum =>
     prod36 (A Ty36 nat36 top36 bot36 arr36 prod36 sum) (B Ty36 nat36 top36 bot36 arr36 prod36 sum)

def sum36 : Ty36 → Ty36 → Ty36
 := λ A B Ty36 nat36 top36 bot36 arr36 prod36 sum36 =>
     sum36 (A Ty36 nat36 top36 bot36 arr36 prod36 sum36) (B Ty36 nat36 top36 bot36 arr36 prod36 sum36)

def Con36 : Type 1
 := ∀ (Con36  : Type)
      (nil  : Con36)
      (snoc : Con36 → Ty36 → Con36)
    , Con36

def nil36 : Con36
 := λ Con36 nil36 snoc => nil36

def snoc36 : Con36 → Ty36 → Con36
 := λ Γ A Con36 nil36 snoc36 => snoc36 (Γ Con36 nil36 snoc36) A

def Var36 : Con36 → Ty36 → Type 1
 := λ Γ A =>
   ∀ (Var36 : Con36 → Ty36 → Type)
     (vz  : ∀{Γ A}, Var36 (snoc36 Γ A) A)
     (vs  : ∀{Γ B A}, Var36 Γ A → Var36 (snoc36 Γ B) A)
   , Var36 Γ A

def vz36 : ∀ {Γ A}, Var36 (snoc36 Γ A) A
 := λ Var36 vz36 vs => vz36

def vs36 : ∀ {Γ B A}, Var36 Γ A → Var36 (snoc36 Γ B) A
 := λ x Var36 vz36 vs36 => vs36 (x Var36 vz36 vs36)

def Tm36 : Con36 → Ty36 → Type 1
 := λ Γ A =>
   ∀ (Tm36  : Con36 → Ty36 → Type)
     (var : ∀ {Γ A}, Var36 Γ A → Tm36 Γ A)
     (lam : ∀ {Γ A B}, (Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B)))
     (app   : ∀ {Γ A B}   , Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B)
     (tt    : ∀ {Γ}       , Tm36 Γ top36)
     (pair  : ∀ {Γ A B}   , Tm36 Γ A → Tm36 Γ B → Tm36 Γ (prod36 A B))
     (fst   : ∀ {Γ A B}   , Tm36 Γ (prod36 A B) → Tm36 Γ A)
     (snd   : ∀ {Γ A B}   , Tm36 Γ (prod36 A B) → Tm36 Γ B)
     (left  : ∀ {Γ A B}   , Tm36 Γ A → Tm36 Γ (sum36 A B))
     (right : ∀ {Γ A B}   , Tm36 Γ B → Tm36 Γ (sum36 A B))
     (case  : ∀ {Γ A B C} , Tm36 Γ (sum36 A B) → Tm36 Γ (arr36 A C) → Tm36 Γ (arr36 B C) → Tm36 Γ C)
     (zero  : ∀ {Γ}       , Tm36 Γ nat36)
     (suc   : ∀ {Γ}       , Tm36 Γ nat36 → Tm36 Γ nat36)
     (rec   : ∀ {Γ A}     , Tm36 Γ nat36 → Tm36 Γ (arr36 nat36 (arr36 A A)) → Tm36 Γ A → Tm36 Γ A)
   , Tm36 Γ A

def var36 : ∀ {Γ A}, Var36 Γ A → Tm36 Γ A
 := λ x Tm36 var36 lam app tt pair fst snd left right case zero suc rec =>
     var36 x

def lam36 : ∀ {Γ A B} , Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B)
 := λ t Tm36 var36 lam36 app tt pair fst snd left right case zero suc rec =>
     lam36 (t Tm36 var36 lam36 app tt pair fst snd left right case zero suc rec)

def app36 : ∀ {Γ A B} , Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B
 := λ t u Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec =>
     app36 (t Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec)
         (u Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec)

def tt36 : ∀ {Γ} , Tm36 Γ top36
 := λ Tm36 var36 lam36 app36 tt36 pair fst snd left right case zero suc rec => tt36

def pair36 : ∀ {Γ A B} , Tm36 Γ A → Tm36 Γ B → Tm36 Γ (prod36 A B)
 := λ t u Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec =>
     pair36 (t Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec)
          (u Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec)

def fst36 : ∀ {Γ A B} , Tm36 Γ (prod36 A B) → Tm36 Γ A
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd left right case zero suc rec =>
     fst36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd left right case zero suc rec)

def snd36 : ∀ {Γ A B} , Tm36 Γ (prod36 A B) → Tm36 Γ B
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left right case zero suc rec =>
     snd36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left right case zero suc rec)

def left36 : ∀ {Γ A B} , Tm36 Γ A → Tm36 Γ (sum36 A B)
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right case zero suc rec =>
     left36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right case zero suc rec)

def right36 : ∀ {Γ A B} , Tm36 Γ B → Tm36 Γ (sum36 A B)
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case zero suc rec =>
     right36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case zero suc rec)

def case36 : ∀ {Γ A B C} , Tm36 Γ (sum36 A B) → Tm36 Γ (arr36 A C) → Tm36 Γ (arr36 B C) → Tm36 Γ C
 := λ t u v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec =>
     case36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)
          (u Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)
          (v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)

def zero36  : ∀ {Γ} , Tm36 Γ nat36
 := λ Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc rec => zero36

def suc36 : ∀ {Γ} , Tm36 Γ nat36 → Tm36 Γ nat36
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec =>
   suc36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec)

def rec36 : ∀ {Γ A} , Tm36 Γ nat36 → Tm36 Γ (arr36 nat36 (arr36 A A)) → Tm36 Γ A → Tm36 Γ A
 := λ t u v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36 =>
     rec36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)
         (u Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)
         (v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)

def v036 : ∀ {Γ A}, Tm36 (snoc36 Γ A) A
 := var36 vz36

def v136 : ∀ {Γ A B}, Tm36 (snoc36 (snoc36 Γ A) B) A
 := var36 (vs36 vz36)

def v236 : ∀ {Γ A B C}, Tm36 (snoc36 (snoc36 (snoc36 Γ A) B) C) A
 := var36 (vs36 (vs36 vz36))

def v336 : ∀ {Γ A B C D}, Tm36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) A
 := var36 (vs36 (vs36 (vs36 vz36)))

def tbool36 : Ty36
 := sum36 top36 top36

def ttrue36 : ∀ {Γ}, Tm36 Γ tbool36
 := left36 tt36

def tfalse36 : ∀ {Γ}, Tm36 Γ tbool36
 := right36 tt36

def ifthenelse36 : ∀ {Γ A}, Tm36 Γ (arr36 tbool36 (arr36 A (arr36 A A)))
 := lam36 (lam36 (lam36 (case36 v236 (lam36 v236) (lam36 v136))))

def times436 : ∀ {Γ A}, Tm36 Γ (arr36 (arr36 A A) (arr36 A A))
  := lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036)))))

def add36 : ∀ {Γ}, Tm36 Γ (arr36 nat36 (arr36 nat36 nat36))
 := lam36 (rec36 v036
      (lam36 (lam36 (lam36 (suc36 (app36 v136 v036)))))
      (lam36 v036))

def mul36 : ∀ {Γ}, Tm36 Γ (arr36 nat36 (arr36 nat36 nat36))
 := lam36 (rec36 v036
     (lam36 (lam36 (lam36 (app36 (app36 add36 (app36 v136 v036)) v036))))
     (lam36 zero36))

def fact36 : ∀ {Γ}, Tm36 Γ (arr36 nat36 nat36)
 := lam36 (rec36 v036 (lam36 (lam36 (app36 (app36 mul36 (suc36 v136)) v036)))
        (suc36 zero36))
def Ty37 : Type 1
 := ∀ (Ty37           : Type)
      (nat top bot  : Ty37)
      (arr prod sum : Ty37 → Ty37 → Ty37)
    , Ty37

def nat37 : Ty37 := λ _ nat37 _ _ _ _ _ => nat37
def top37 : Ty37 := λ _ _ top37 _ _ _ _ => top37
def bot37 : Ty37 := λ _ _ _ bot37 _ _ _ => bot37

def arr37 : Ty37 → Ty37 → Ty37
 := λ A B Ty37 nat37 top37 bot37 arr37 prod sum =>
     arr37 (A Ty37 nat37 top37 bot37 arr37 prod sum) (B Ty37 nat37 top37 bot37 arr37 prod sum)

def prod37 : Ty37 → Ty37 → Ty37
 := λ A B Ty37 nat37 top37 bot37 arr37 prod37 sum =>
     prod37 (A Ty37 nat37 top37 bot37 arr37 prod37 sum) (B Ty37 nat37 top37 bot37 arr37 prod37 sum)

def sum37 : Ty37 → Ty37 → Ty37
 := λ A B Ty37 nat37 top37 bot37 arr37 prod37 sum37 =>
     sum37 (A Ty37 nat37 top37 bot37 arr37 prod37 sum37) (B Ty37 nat37 top37 bot37 arr37 prod37 sum37)

def Con37 : Type 1
 := ∀ (Con37  : Type)
      (nil  : Con37)
      (snoc : Con37 → Ty37 → Con37)
    , Con37

def nil37 : Con37
 := λ Con37 nil37 snoc => nil37

def snoc37 : Con37 → Ty37 → Con37
 := λ Γ A Con37 nil37 snoc37 => snoc37 (Γ Con37 nil37 snoc37) A

def Var37 : Con37 → Ty37 → Type 1
 := λ Γ A =>
   ∀ (Var37 : Con37 → Ty37 → Type)
     (vz  : ∀{Γ A}, Var37 (snoc37 Γ A) A)
     (vs  : ∀{Γ B A}, Var37 Γ A → Var37 (snoc37 Γ B) A)
   , Var37 Γ A

def vz37 : ∀ {Γ A}, Var37 (snoc37 Γ A) A
 := λ Var37 vz37 vs => vz37

def vs37 : ∀ {Γ B A}, Var37 Γ A → Var37 (snoc37 Γ B) A
 := λ x Var37 vz37 vs37 => vs37 (x Var37 vz37 vs37)

def Tm37 : Con37 → Ty37 → Type 1
 := λ Γ A =>
   ∀ (Tm37  : Con37 → Ty37 → Type)
     (var : ∀ {Γ A}, Var37 Γ A → Tm37 Γ A)
     (lam : ∀ {Γ A B}, (Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B)))
     (app   : ∀ {Γ A B}   , Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B)
     (tt    : ∀ {Γ}       , Tm37 Γ top37)
     (pair  : ∀ {Γ A B}   , Tm37 Γ A → Tm37 Γ B → Tm37 Γ (prod37 A B))
     (fst   : ∀ {Γ A B}   , Tm37 Γ (prod37 A B) → Tm37 Γ A)
     (snd   : ∀ {Γ A B}   , Tm37 Γ (prod37 A B) → Tm37 Γ B)
     (left  : ∀ {Γ A B}   , Tm37 Γ A → Tm37 Γ (sum37 A B))
     (right : ∀ {Γ A B}   , Tm37 Γ B → Tm37 Γ (sum37 A B))
     (case  : ∀ {Γ A B C} , Tm37 Γ (sum37 A B) → Tm37 Γ (arr37 A C) → Tm37 Γ (arr37 B C) → Tm37 Γ C)
     (zero  : ∀ {Γ}       , Tm37 Γ nat37)
     (suc   : ∀ {Γ}       , Tm37 Γ nat37 → Tm37 Γ nat37)
     (rec   : ∀ {Γ A}     , Tm37 Γ nat37 → Tm37 Γ (arr37 nat37 (arr37 A A)) → Tm37 Γ A → Tm37 Γ A)
   , Tm37 Γ A

def var37 : ∀ {Γ A}, Var37 Γ A → Tm37 Γ A
 := λ x Tm37 var37 lam app tt pair fst snd left right case zero suc rec =>
     var37 x

def lam37 : ∀ {Γ A B} , Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B)
 := λ t Tm37 var37 lam37 app tt pair fst snd left right case zero suc rec =>
     lam37 (t Tm37 var37 lam37 app tt pair fst snd left right case zero suc rec)

def app37 : ∀ {Γ A B} , Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B
 := λ t u Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec =>
     app37 (t Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec)
         (u Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec)

def tt37 : ∀ {Γ} , Tm37 Γ top37
 := λ Tm37 var37 lam37 app37 tt37 pair fst snd left right case zero suc rec => tt37

def pair37 : ∀ {Γ A B} , Tm37 Γ A → Tm37 Γ B → Tm37 Γ (prod37 A B)
 := λ t u Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec =>
     pair37 (t Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec)
          (u Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec)

def fst37 : ∀ {Γ A B} , Tm37 Γ (prod37 A B) → Tm37 Γ A
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd left right case zero suc rec =>
     fst37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd left right case zero suc rec)

def snd37 : ∀ {Γ A B} , Tm37 Γ (prod37 A B) → Tm37 Γ B
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left right case zero suc rec =>
     snd37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left right case zero suc rec)

def left37 : ∀ {Γ A B} , Tm37 Γ A → Tm37 Γ (sum37 A B)
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right case zero suc rec =>
     left37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right case zero suc rec)

def right37 : ∀ {Γ A B} , Tm37 Γ B → Tm37 Γ (sum37 A B)
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case zero suc rec =>
     right37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case zero suc rec)

def case37 : ∀ {Γ A B C} , Tm37 Γ (sum37 A B) → Tm37 Γ (arr37 A C) → Tm37 Γ (arr37 B C) → Tm37 Γ C
 := λ t u v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec =>
     case37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)
          (u Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)
          (v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)

def zero37  : ∀ {Γ} , Tm37 Γ nat37
 := λ Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc rec => zero37

def suc37 : ∀ {Γ} , Tm37 Γ nat37 → Tm37 Γ nat37
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec =>
   suc37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec)

def rec37 : ∀ {Γ A} , Tm37 Γ nat37 → Tm37 Γ (arr37 nat37 (arr37 A A)) → Tm37 Γ A → Tm37 Γ A
 := λ t u v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37 =>
     rec37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)
         (u Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)
         (v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)

def v037 : ∀ {Γ A}, Tm37 (snoc37 Γ A) A
 := var37 vz37

def v137 : ∀ {Γ A B}, Tm37 (snoc37 (snoc37 Γ A) B) A
 := var37 (vs37 vz37)

def v237 : ∀ {Γ A B C}, Tm37 (snoc37 (snoc37 (snoc37 Γ A) B) C) A
 := var37 (vs37 (vs37 vz37))

def v337 : ∀ {Γ A B C D}, Tm37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) A
 := var37 (vs37 (vs37 (vs37 vz37)))

def tbool37 : Ty37
 := sum37 top37 top37

def ttrue37 : ∀ {Γ}, Tm37 Γ tbool37
 := left37 tt37

def tfalse37 : ∀ {Γ}, Tm37 Γ tbool37
 := right37 tt37

def ifthenelse37 : ∀ {Γ A}, Tm37 Γ (arr37 tbool37 (arr37 A (arr37 A A)))
 := lam37 (lam37 (lam37 (case37 v237 (lam37 v237) (lam37 v137))))

def times437 : ∀ {Γ A}, Tm37 Γ (arr37 (arr37 A A) (arr37 A A))
  := lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037)))))

def add37 : ∀ {Γ}, Tm37 Γ (arr37 nat37 (arr37 nat37 nat37))
 := lam37 (rec37 v037
      (lam37 (lam37 (lam37 (suc37 (app37 v137 v037)))))
      (lam37 v037))

def mul37 : ∀ {Γ}, Tm37 Γ (arr37 nat37 (arr37 nat37 nat37))
 := lam37 (rec37 v037
     (lam37 (lam37 (lam37 (app37 (app37 add37 (app37 v137 v037)) v037))))
     (lam37 zero37))

def fact37 : ∀ {Γ}, Tm37 Γ (arr37 nat37 nat37)
 := lam37 (rec37 v037 (lam37 (lam37 (app37 (app37 mul37 (suc37 v137)) v037)))
        (suc37 zero37))
def Ty38 : Type 1
 := ∀ (Ty38           : Type)
      (nat top bot  : Ty38)
      (arr prod sum : Ty38 → Ty38 → Ty38)
    , Ty38

def nat38 : Ty38 := λ _ nat38 _ _ _ _ _ => nat38
def top38 : Ty38 := λ _ _ top38 _ _ _ _ => top38
def bot38 : Ty38 := λ _ _ _ bot38 _ _ _ => bot38

def arr38 : Ty38 → Ty38 → Ty38
 := λ A B Ty38 nat38 top38 bot38 arr38 prod sum =>
     arr38 (A Ty38 nat38 top38 bot38 arr38 prod sum) (B Ty38 nat38 top38 bot38 arr38 prod sum)

def prod38 : Ty38 → Ty38 → Ty38
 := λ A B Ty38 nat38 top38 bot38 arr38 prod38 sum =>
     prod38 (A Ty38 nat38 top38 bot38 arr38 prod38 sum) (B Ty38 nat38 top38 bot38 arr38 prod38 sum)

def sum38 : Ty38 → Ty38 → Ty38
 := λ A B Ty38 nat38 top38 bot38 arr38 prod38 sum38 =>
     sum38 (A Ty38 nat38 top38 bot38 arr38 prod38 sum38) (B Ty38 nat38 top38 bot38 arr38 prod38 sum38)

def Con38 : Type 1
 := ∀ (Con38  : Type)
      (nil  : Con38)
      (snoc : Con38 → Ty38 → Con38)
    , Con38

def nil38 : Con38
 := λ Con38 nil38 snoc => nil38

def snoc38 : Con38 → Ty38 → Con38
 := λ Γ A Con38 nil38 snoc38 => snoc38 (Γ Con38 nil38 snoc38) A

def Var38 : Con38 → Ty38 → Type 1
 := λ Γ A =>
   ∀ (Var38 : Con38 → Ty38 → Type)
     (vz  : ∀{Γ A}, Var38 (snoc38 Γ A) A)
     (vs  : ∀{Γ B A}, Var38 Γ A → Var38 (snoc38 Γ B) A)
   , Var38 Γ A

def vz38 : ∀ {Γ A}, Var38 (snoc38 Γ A) A
 := λ Var38 vz38 vs => vz38

def vs38 : ∀ {Γ B A}, Var38 Γ A → Var38 (snoc38 Γ B) A
 := λ x Var38 vz38 vs38 => vs38 (x Var38 vz38 vs38)

def Tm38 : Con38 → Ty38 → Type 1
 := λ Γ A =>
   ∀ (Tm38  : Con38 → Ty38 → Type)
     (var : ∀ {Γ A}, Var38 Γ A → Tm38 Γ A)
     (lam : ∀ {Γ A B}, (Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B)))
     (app   : ∀ {Γ A B}   , Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B)
     (tt    : ∀ {Γ}       , Tm38 Γ top38)
     (pair  : ∀ {Γ A B}   , Tm38 Γ A → Tm38 Γ B → Tm38 Γ (prod38 A B))
     (fst   : ∀ {Γ A B}   , Tm38 Γ (prod38 A B) → Tm38 Γ A)
     (snd   : ∀ {Γ A B}   , Tm38 Γ (prod38 A B) → Tm38 Γ B)
     (left  : ∀ {Γ A B}   , Tm38 Γ A → Tm38 Γ (sum38 A B))
     (right : ∀ {Γ A B}   , Tm38 Γ B → Tm38 Γ (sum38 A B))
     (case  : ∀ {Γ A B C} , Tm38 Γ (sum38 A B) → Tm38 Γ (arr38 A C) → Tm38 Γ (arr38 B C) → Tm38 Γ C)
     (zero  : ∀ {Γ}       , Tm38 Γ nat38)
     (suc   : ∀ {Γ}       , Tm38 Γ nat38 → Tm38 Γ nat38)
     (rec   : ∀ {Γ A}     , Tm38 Γ nat38 → Tm38 Γ (arr38 nat38 (arr38 A A)) → Tm38 Γ A → Tm38 Γ A)
   , Tm38 Γ A

def var38 : ∀ {Γ A}, Var38 Γ A → Tm38 Γ A
 := λ x Tm38 var38 lam app tt pair fst snd left right case zero suc rec =>
     var38 x

def lam38 : ∀ {Γ A B} , Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B)
 := λ t Tm38 var38 lam38 app tt pair fst snd left right case zero suc rec =>
     lam38 (t Tm38 var38 lam38 app tt pair fst snd left right case zero suc rec)

def app38 : ∀ {Γ A B} , Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B
 := λ t u Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec =>
     app38 (t Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec)
         (u Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec)

def tt38 : ∀ {Γ} , Tm38 Γ top38
 := λ Tm38 var38 lam38 app38 tt38 pair fst snd left right case zero suc rec => tt38

def pair38 : ∀ {Γ A B} , Tm38 Γ A → Tm38 Γ B → Tm38 Γ (prod38 A B)
 := λ t u Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec =>
     pair38 (t Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec)
          (u Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec)

def fst38 : ∀ {Γ A B} , Tm38 Γ (prod38 A B) → Tm38 Γ A
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd left right case zero suc rec =>
     fst38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd left right case zero suc rec)

def snd38 : ∀ {Γ A B} , Tm38 Γ (prod38 A B) → Tm38 Γ B
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left right case zero suc rec =>
     snd38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left right case zero suc rec)

def left38 : ∀ {Γ A B} , Tm38 Γ A → Tm38 Γ (sum38 A B)
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right case zero suc rec =>
     left38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right case zero suc rec)

def right38 : ∀ {Γ A B} , Tm38 Γ B → Tm38 Γ (sum38 A B)
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case zero suc rec =>
     right38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case zero suc rec)

def case38 : ∀ {Γ A B C} , Tm38 Γ (sum38 A B) → Tm38 Γ (arr38 A C) → Tm38 Γ (arr38 B C) → Tm38 Γ C
 := λ t u v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec =>
     case38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)
          (u Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)
          (v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)

def zero38  : ∀ {Γ} , Tm38 Γ nat38
 := λ Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc rec => zero38

def suc38 : ∀ {Γ} , Tm38 Γ nat38 → Tm38 Γ nat38
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec =>
   suc38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec)

def rec38 : ∀ {Γ A} , Tm38 Γ nat38 → Tm38 Γ (arr38 nat38 (arr38 A A)) → Tm38 Γ A → Tm38 Γ A
 := λ t u v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38 =>
     rec38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)
         (u Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)
         (v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)

def v038 : ∀ {Γ A}, Tm38 (snoc38 Γ A) A
 := var38 vz38

def v138 : ∀ {Γ A B}, Tm38 (snoc38 (snoc38 Γ A) B) A
 := var38 (vs38 vz38)

def v238 : ∀ {Γ A B C}, Tm38 (snoc38 (snoc38 (snoc38 Γ A) B) C) A
 := var38 (vs38 (vs38 vz38))

def v338 : ∀ {Γ A B C D}, Tm38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) A
 := var38 (vs38 (vs38 (vs38 vz38)))

def tbool38 : Ty38
 := sum38 top38 top38

def ttrue38 : ∀ {Γ}, Tm38 Γ tbool38
 := left38 tt38

def tfalse38 : ∀ {Γ}, Tm38 Γ tbool38
 := right38 tt38

def ifthenelse38 : ∀ {Γ A}, Tm38 Γ (arr38 tbool38 (arr38 A (arr38 A A)))
 := lam38 (lam38 (lam38 (case38 v238 (lam38 v238) (lam38 v138))))

def times438 : ∀ {Γ A}, Tm38 Γ (arr38 (arr38 A A) (arr38 A A))
  := lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038)))))

def add38 : ∀ {Γ}, Tm38 Γ (arr38 nat38 (arr38 nat38 nat38))
 := lam38 (rec38 v038
      (lam38 (lam38 (lam38 (suc38 (app38 v138 v038)))))
      (lam38 v038))

def mul38 : ∀ {Γ}, Tm38 Γ (arr38 nat38 (arr38 nat38 nat38))
 := lam38 (rec38 v038
     (lam38 (lam38 (lam38 (app38 (app38 add38 (app38 v138 v038)) v038))))
     (lam38 zero38))

def fact38 : ∀ {Γ}, Tm38 Γ (arr38 nat38 nat38)
 := lam38 (rec38 v038 (lam38 (lam38 (app38 (app38 mul38 (suc38 v138)) v038)))
        (suc38 zero38))
def Ty39 : Type 1
 := ∀ (Ty39           : Type)
      (nat top bot  : Ty39)
      (arr prod sum : Ty39 → Ty39 → Ty39)
    , Ty39

def nat39 : Ty39 := λ _ nat39 _ _ _ _ _ => nat39
def top39 : Ty39 := λ _ _ top39 _ _ _ _ => top39
def bot39 : Ty39 := λ _ _ _ bot39 _ _ _ => bot39

def arr39 : Ty39 → Ty39 → Ty39
 := λ A B Ty39 nat39 top39 bot39 arr39 prod sum =>
     arr39 (A Ty39 nat39 top39 bot39 arr39 prod sum) (B Ty39 nat39 top39 bot39 arr39 prod sum)

def prod39 : Ty39 → Ty39 → Ty39
 := λ A B Ty39 nat39 top39 bot39 arr39 prod39 sum =>
     prod39 (A Ty39 nat39 top39 bot39 arr39 prod39 sum) (B Ty39 nat39 top39 bot39 arr39 prod39 sum)

def sum39 : Ty39 → Ty39 → Ty39
 := λ A B Ty39 nat39 top39 bot39 arr39 prod39 sum39 =>
     sum39 (A Ty39 nat39 top39 bot39 arr39 prod39 sum39) (B Ty39 nat39 top39 bot39 arr39 prod39 sum39)

def Con39 : Type 1
 := ∀ (Con39  : Type)
      (nil  : Con39)
      (snoc : Con39 → Ty39 → Con39)
    , Con39

def nil39 : Con39
 := λ Con39 nil39 snoc => nil39

def snoc39 : Con39 → Ty39 → Con39
 := λ Γ A Con39 nil39 snoc39 => snoc39 (Γ Con39 nil39 snoc39) A

def Var39 : Con39 → Ty39 → Type 1
 := λ Γ A =>
   ∀ (Var39 : Con39 → Ty39 → Type)
     (vz  : ∀{Γ A}, Var39 (snoc39 Γ A) A)
     (vs  : ∀{Γ B A}, Var39 Γ A → Var39 (snoc39 Γ B) A)
   , Var39 Γ A

def vz39 : ∀ {Γ A}, Var39 (snoc39 Γ A) A
 := λ Var39 vz39 vs => vz39

def vs39 : ∀ {Γ B A}, Var39 Γ A → Var39 (snoc39 Γ B) A
 := λ x Var39 vz39 vs39 => vs39 (x Var39 vz39 vs39)

def Tm39 : Con39 → Ty39 → Type 1
 := λ Γ A =>
   ∀ (Tm39  : Con39 → Ty39 → Type)
     (var : ∀ {Γ A}, Var39 Γ A → Tm39 Γ A)
     (lam : ∀ {Γ A B}, (Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B)))
     (app   : ∀ {Γ A B}   , Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B)
     (tt    : ∀ {Γ}       , Tm39 Γ top39)
     (pair  : ∀ {Γ A B}   , Tm39 Γ A → Tm39 Γ B → Tm39 Γ (prod39 A B))
     (fst   : ∀ {Γ A B}   , Tm39 Γ (prod39 A B) → Tm39 Γ A)
     (snd   : ∀ {Γ A B}   , Tm39 Γ (prod39 A B) → Tm39 Γ B)
     (left  : ∀ {Γ A B}   , Tm39 Γ A → Tm39 Γ (sum39 A B))
     (right : ∀ {Γ A B}   , Tm39 Γ B → Tm39 Γ (sum39 A B))
     (case  : ∀ {Γ A B C} , Tm39 Γ (sum39 A B) → Tm39 Γ (arr39 A C) → Tm39 Γ (arr39 B C) → Tm39 Γ C)
     (zero  : ∀ {Γ}       , Tm39 Γ nat39)
     (suc   : ∀ {Γ}       , Tm39 Γ nat39 → Tm39 Γ nat39)
     (rec   : ∀ {Γ A}     , Tm39 Γ nat39 → Tm39 Γ (arr39 nat39 (arr39 A A)) → Tm39 Γ A → Tm39 Γ A)
   , Tm39 Γ A

def var39 : ∀ {Γ A}, Var39 Γ A → Tm39 Γ A
 := λ x Tm39 var39 lam app tt pair fst snd left right case zero suc rec =>
     var39 x

def lam39 : ∀ {Γ A B} , Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B)
 := λ t Tm39 var39 lam39 app tt pair fst snd left right case zero suc rec =>
     lam39 (t Tm39 var39 lam39 app tt pair fst snd left right case zero suc rec)

def app39 : ∀ {Γ A B} , Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B
 := λ t u Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec =>
     app39 (t Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec)
         (u Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec)

def tt39 : ∀ {Γ} , Tm39 Γ top39
 := λ Tm39 var39 lam39 app39 tt39 pair fst snd left right case zero suc rec => tt39

def pair39 : ∀ {Γ A B} , Tm39 Γ A → Tm39 Γ B → Tm39 Γ (prod39 A B)
 := λ t u Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec =>
     pair39 (t Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec)
          (u Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec)

def fst39 : ∀ {Γ A B} , Tm39 Γ (prod39 A B) → Tm39 Γ A
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd left right case zero suc rec =>
     fst39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd left right case zero suc rec)

def snd39 : ∀ {Γ A B} , Tm39 Γ (prod39 A B) → Tm39 Γ B
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left right case zero suc rec =>
     snd39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left right case zero suc rec)

def left39 : ∀ {Γ A B} , Tm39 Γ A → Tm39 Γ (sum39 A B)
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right case zero suc rec =>
     left39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right case zero suc rec)

def right39 : ∀ {Γ A B} , Tm39 Γ B → Tm39 Γ (sum39 A B)
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case zero suc rec =>
     right39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case zero suc rec)

def case39 : ∀ {Γ A B C} , Tm39 Γ (sum39 A B) → Tm39 Γ (arr39 A C) → Tm39 Γ (arr39 B C) → Tm39 Γ C
 := λ t u v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec =>
     case39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)
          (u Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)
          (v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)

def zero39  : ∀ {Γ} , Tm39 Γ nat39
 := λ Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc rec => zero39

def suc39 : ∀ {Γ} , Tm39 Γ nat39 → Tm39 Γ nat39
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec =>
   suc39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec)

def rec39 : ∀ {Γ A} , Tm39 Γ nat39 → Tm39 Γ (arr39 nat39 (arr39 A A)) → Tm39 Γ A → Tm39 Γ A
 := λ t u v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39 =>
     rec39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)
         (u Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)
         (v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)

def v039 : ∀ {Γ A}, Tm39 (snoc39 Γ A) A
 := var39 vz39

def v139 : ∀ {Γ A B}, Tm39 (snoc39 (snoc39 Γ A) B) A
 := var39 (vs39 vz39)

def v239 : ∀ {Γ A B C}, Tm39 (snoc39 (snoc39 (snoc39 Γ A) B) C) A
 := var39 (vs39 (vs39 vz39))

def v339 : ∀ {Γ A B C D}, Tm39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) A
 := var39 (vs39 (vs39 (vs39 vz39)))

def tbool39 : Ty39
 := sum39 top39 top39

def ttrue39 : ∀ {Γ}, Tm39 Γ tbool39
 := left39 tt39

def tfalse39 : ∀ {Γ}, Tm39 Γ tbool39
 := right39 tt39

def ifthenelse39 : ∀ {Γ A}, Tm39 Γ (arr39 tbool39 (arr39 A (arr39 A A)))
 := lam39 (lam39 (lam39 (case39 v239 (lam39 v239) (lam39 v139))))

def times439 : ∀ {Γ A}, Tm39 Γ (arr39 (arr39 A A) (arr39 A A))
  := lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039)))))

def add39 : ∀ {Γ}, Tm39 Γ (arr39 nat39 (arr39 nat39 nat39))
 := lam39 (rec39 v039
      (lam39 (lam39 (lam39 (suc39 (app39 v139 v039)))))
      (lam39 v039))

def mul39 : ∀ {Γ}, Tm39 Γ (arr39 nat39 (arr39 nat39 nat39))
 := lam39 (rec39 v039
     (lam39 (lam39 (lam39 (app39 (app39 add39 (app39 v139 v039)) v039))))
     (lam39 zero39))

def fact39 : ∀ {Γ}, Tm39 Γ (arr39 nat39 nat39)
 := lam39 (rec39 v039 (lam39 (lam39 (app39 (app39 mul39 (suc39 v139)) v039)))
        (suc39 zero39))
