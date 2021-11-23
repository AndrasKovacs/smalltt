{-# OPTIONS --type-in-type #-}

Ty : Set
Ty =
   (Ty         : Set)
   (nat top bot  : Ty)
   (arr prod sum : Ty → Ty → Ty)
 → Ty

nat : Ty; nat = λ _ nat _ _ _ _ _ → nat
top : Ty; top = λ _ _ top _ _ _ _ → top
bot : Ty; bot = λ _ _ _ bot _ _ _ → bot

arr : Ty → Ty → Ty; arr
 = λ A B Ty nat top bot arr prod sum →
     arr (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)

prod : Ty → Ty → Ty; prod
 = λ A B Ty nat top bot arr prod sum →
     prod (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)

sum : Ty → Ty → Ty; sum
 = λ A B Ty nat top bot arr prod sum →
     sum (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)

Con : Set; Con
 = (Con : Set)
   (nil  : Con)
   (snoc : Con → Ty → Con)
 → Con

nil : Con; nil
 = λ Con nil snoc → nil

snoc : Con → Ty → Con; snoc
 = λ Γ A Con nil snoc → snoc (Γ Con nil snoc) A

Var : Con → Ty → Set; Var
 = λ Γ A →
   (Var : Con → Ty → Set)
   (vz  : ∀{Γ A} → Var (snoc Γ A) A)
   (vs  : ∀{Γ B A} → Var Γ A → Var (snoc Γ B) A)
 → Var Γ A

vz : ∀{Γ A} → Var (snoc Γ A) A; vz
 = λ Var vz vs → vz

vs : ∀{Γ B A} → Var Γ A → Var (snoc Γ B) A; vs
 = λ x Var vz vs → vs (x Var vz vs)

Tm : Con → Ty → Set; Tm
 = λ Γ A →
   (Tm  : Con → Ty → Set)
   (var   : ∀{Γ A} → Var Γ A → Tm Γ A)
   (lam   : ∀{Γ A B} → Tm (snoc Γ A) B → Tm Γ (arr A B))
   (app   : ∀{Γ A B} → Tm Γ (arr A B) → Tm Γ A → Tm Γ B)
   (tt    : ∀{Γ} → Tm Γ top)
   (pair  : ∀{Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (prod A B))
   (fst   : ∀{Γ A B} → Tm Γ (prod A B) → Tm Γ A)
   (snd   : ∀{Γ A B} → Tm Γ (prod A B) → Tm Γ B)
   (left  : ∀{Γ A B} → Tm Γ A → Tm Γ (sum A B))
   (right : ∀{Γ A B} → Tm Γ B → Tm Γ (sum A B))
   (case  : ∀{Γ A B C} → Tm Γ (sum A B) → Tm Γ (arr A C) → Tm Γ (arr B C) → Tm Γ C)
   (zero  : ∀{Γ} → Tm Γ nat)
   (suc   : ∀{Γ} → Tm Γ nat → Tm Γ nat)
   (rec   : ∀{Γ A} → Tm Γ nat → Tm Γ (arr nat (arr A A)) → Tm Γ A → Tm Γ A)
 → Tm Γ A

var : ∀{Γ A} → Var Γ A → Tm Γ A; var
 = λ x Tm var lam app tt pair fst snd left right case zero suc rec →
     var x

lam : ∀{Γ A B} → Tm (snoc Γ A) B → Tm Γ (arr A B); lam
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     lam (t Tm var lam app tt pair fst snd left right case zero suc rec)

app : ∀{Γ A B} → Tm Γ (arr A B) → Tm Γ A → Tm Γ B; app
 = λ t u Tm var lam app tt pair fst snd left right case zero suc rec →
     app (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec)

tt : ∀{Γ} → Tm Γ top; tt
 = λ Tm var lam app tt pair fst snd left right case zero suc rec → tt

pair : ∀{Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (prod A B); pair
 = λ t u Tm var lam app tt pair fst snd left right case zero suc rec →
     pair (t Tm var lam app tt pair fst snd left right case zero suc rec)
          (u Tm var lam app tt pair fst snd left right case zero suc rec)

fst : ∀{Γ A B} → Tm Γ (prod A B) → Tm Γ A; fst
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     fst (t Tm var lam app tt pair fst snd left right case zero suc rec)

snd : ∀{Γ A B} → Tm Γ (prod A B) → Tm Γ B; snd
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     snd (t Tm var lam app tt pair fst snd left right case zero suc rec)

left : ∀{Γ A B} → Tm Γ A → Tm Γ (sum A B); left
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     left (t Tm var lam app tt pair fst snd left right case zero suc rec)

right : ∀{Γ A B} → Tm Γ B → Tm Γ (sum A B); right
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     right (t Tm var lam app tt pair fst snd left right case zero suc rec)

case : ∀{Γ A B C} → Tm Γ (sum A B) → Tm Γ (arr A C) → Tm Γ (arr B C) → Tm Γ C; case
 = λ t u v Tm var lam app tt pair fst snd left right case zero suc rec →
     case (t Tm var lam app tt pair fst snd left right case zero suc rec)
           (u Tm var lam app tt pair fst snd left right case zero suc rec)
           (v Tm var lam app tt pair fst snd left right case zero suc rec)

zero  : ∀{Γ} → Tm Γ nat; zero
 = λ Tm var lam app tt pair fst snd left right case zero suc rec → zero

suc : ∀{Γ} → Tm Γ nat → Tm Γ nat; suc
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
   suc (t Tm var lam app tt pair fst snd left right case zero suc rec)

rec : ∀{Γ A} → Tm Γ nat → Tm Γ (arr nat (arr A A)) → Tm Γ A → Tm Γ A; rec
 = λ t u v Tm var lam app tt pair fst snd left right case zero suc rec →
     rec (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec)
         (v Tm var lam app tt pair fst snd left right case zero suc rec)

v0 : ∀{Γ A} → Tm (snoc Γ A) A; v0
 = var vz

v1 : ∀{Γ A B} → Tm (snoc (snoc Γ A) B) A; v1
 = var (vs vz)

v2 : ∀{Γ A B C} → Tm (snoc (snoc (snoc Γ A) B) C) A; v2
 = var (vs (vs vz))

v3 : ∀{Γ A B C D} → Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A; v3
 = var (vs (vs (vs vz)))

tbool : Ty; tbool
 = sum top top

true : ∀{Γ} → Tm Γ tbool; true
 = left tt

tfalse : ∀{Γ} → Tm Γ tbool; tfalse
 = right tt

ifthenelse : ∀{Γ A} → Tm Γ (arr tbool (arr A (arr A A))); ifthenelse
 = lam (lam (lam (case v2 (lam v2) (lam v1))))

times4 : ∀{Γ A} → Tm Γ (arr (arr A A) (arr A A)); times4
  = lam (lam (app v1 (app v1 (app v1 (app v1 v0)))))

add : ∀{Γ} → Tm Γ (arr nat (arr nat nat)); add
 = lam (rec v0
       (lam (lam (lam (suc (app v1 v0)))))
       (lam v0))

mul : ∀{Γ} → Tm Γ (arr nat (arr nat nat)); mul
 = lam (rec v0
       (lam (lam (lam (app (app add (app v1 v0)) v0))))
       (lam zero))

fact : ∀{Γ} → Tm Γ (arr nat nat); fact
 = lam (rec v0 (lam (lam (app (app mul (suc v1)) v0)))
        (suc zero))
{-# OPTIONS --type-in-type #-}

Ty1 : Set
Ty1 =
   (Ty1         : Set)
   (nat top bot  : Ty1)
   (arr prod sum : Ty1 → Ty1 → Ty1)
 → Ty1

nat1 : Ty1; nat1 = λ _ nat1 _ _ _ _ _ → nat1
top1 : Ty1; top1 = λ _ _ top1 _ _ _ _ → top1
bot1 : Ty1; bot1 = λ _ _ _ bot1 _ _ _ → bot1

arr1 : Ty1 → Ty1 → Ty1; arr1
 = λ A B Ty1 nat1 top1 bot1 arr1 prod sum →
     arr1 (A Ty1 nat1 top1 bot1 arr1 prod sum) (B Ty1 nat1 top1 bot1 arr1 prod sum)

prod1 : Ty1 → Ty1 → Ty1; prod1
 = λ A B Ty1 nat1 top1 bot1 arr1 prod1 sum →
     prod1 (A Ty1 nat1 top1 bot1 arr1 prod1 sum) (B Ty1 nat1 top1 bot1 arr1 prod1 sum)

sum1 : Ty1 → Ty1 → Ty1; sum1
 = λ A B Ty1 nat1 top1 bot1 arr1 prod1 sum1 →
     sum1 (A Ty1 nat1 top1 bot1 arr1 prod1 sum1) (B Ty1 nat1 top1 bot1 arr1 prod1 sum1)

Con1 : Set; Con1
 = (Con1 : Set)
   (nil  : Con1)
   (snoc : Con1 → Ty1 → Con1)
 → Con1

nil1 : Con1; nil1
 = λ Con1 nil1 snoc → nil1

snoc1 : Con1 → Ty1 → Con1; snoc1
 = λ Γ A Con1 nil1 snoc1 → snoc1 (Γ Con1 nil1 snoc1) A

Var1 : Con1 → Ty1 → Set; Var1
 = λ Γ A →
   (Var1 : Con1 → Ty1 → Set)
   (vz  : ∀{Γ A} → Var1 (snoc1 Γ A) A)
   (vs  : ∀{Γ B A} → Var1 Γ A → Var1 (snoc1 Γ B) A)
 → Var1 Γ A

vz1 : ∀{Γ A} → Var1 (snoc1 Γ A) A; vz1
 = λ Var1 vz1 vs → vz1

vs1 : ∀{Γ B A} → Var1 Γ A → Var1 (snoc1 Γ B) A; vs1
 = λ x Var1 vz1 vs1 → vs1 (x Var1 vz1 vs1)

Tm1 : Con1 → Ty1 → Set; Tm1
 = λ Γ A →
   (Tm1  : Con1 → Ty1 → Set)
   (var   : ∀{Γ A} → Var1 Γ A → Tm1 Γ A)
   (lam   : ∀{Γ A B} → Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B))
   (app   : ∀{Γ A B} → Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B)
   (tt    : ∀{Γ} → Tm1 Γ top1)
   (pair  : ∀{Γ A B} → Tm1 Γ A → Tm1 Γ B → Tm1 Γ (prod1 A B))
   (fst   : ∀{Γ A B} → Tm1 Γ (prod1 A B) → Tm1 Γ A)
   (snd   : ∀{Γ A B} → Tm1 Γ (prod1 A B) → Tm1 Γ B)
   (left  : ∀{Γ A B} → Tm1 Γ A → Tm1 Γ (sum1 A B))
   (right : ∀{Γ A B} → Tm1 Γ B → Tm1 Γ (sum1 A B))
   (case  : ∀{Γ A B C} → Tm1 Γ (sum1 A B) → Tm1 Γ (arr1 A C) → Tm1 Γ (arr1 B C) → Tm1 Γ C)
   (zero  : ∀{Γ} → Tm1 Γ nat1)
   (suc   : ∀{Γ} → Tm1 Γ nat1 → Tm1 Γ nat1)
   (rec   : ∀{Γ A} → Tm1 Γ nat1 → Tm1 Γ (arr1 nat1 (arr1 A A)) → Tm1 Γ A → Tm1 Γ A)
 → Tm1 Γ A

var1 : ∀{Γ A} → Var1 Γ A → Tm1 Γ A; var1
 = λ x Tm1 var1 lam app tt pair fst snd left right case zero suc rec →
     var1 x

lam1 : ∀{Γ A B} → Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B); lam1
 = λ t Tm1 var1 lam1 app tt pair fst snd left right case zero suc rec →
     lam1 (t Tm1 var1 lam1 app tt pair fst snd left right case zero suc rec)

app1 : ∀{Γ A B} → Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B; app1
 = λ t u Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec →
     app1 (t Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec)
         (u Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec)

tt1 : ∀{Γ} → Tm1 Γ top1; tt1
 = λ Tm1 var1 lam1 app1 tt1 pair fst snd left right case zero suc rec → tt1

pair1 : ∀{Γ A B} → Tm1 Γ A → Tm1 Γ B → Tm1 Γ (prod1 A B); pair1
 = λ t u Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec →
     pair1 (t Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec)
          (u Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec)

fst1 : ∀{Γ A B} → Tm1 Γ (prod1 A B) → Tm1 Γ A; fst1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd left right case zero suc rec →
     fst1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd left right case zero suc rec)

snd1 : ∀{Γ A B} → Tm1 Γ (prod1 A B) → Tm1 Γ B; snd1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left right case zero suc rec →
     snd1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left right case zero suc rec)

left1 : ∀{Γ A B} → Tm1 Γ A → Tm1 Γ (sum1 A B); left1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right case zero suc rec →
     left1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right case zero suc rec)

right1 : ∀{Γ A B} → Tm1 Γ B → Tm1 Γ (sum1 A B); right1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case zero suc rec →
     right1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case zero suc rec)

case1 : ∀{Γ A B C} → Tm1 Γ (sum1 A B) → Tm1 Γ (arr1 A C) → Tm1 Γ (arr1 B C) → Tm1 Γ C; case1
 = λ t u v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec →
     case1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)
           (u Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)
           (v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)

zero1  : ∀{Γ} → Tm1 Γ nat1; zero1
 = λ Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc rec → zero1

suc1 : ∀{Γ} → Tm1 Γ nat1 → Tm1 Γ nat1; suc1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec →
   suc1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec)

rec1 : ∀{Γ A} → Tm1 Γ nat1 → Tm1 Γ (arr1 nat1 (arr1 A A)) → Tm1 Γ A → Tm1 Γ A; rec1
 = λ t u v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1 →
     rec1 (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)
         (u Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)
         (v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)

v01 : ∀{Γ A} → Tm1 (snoc1 Γ A) A; v01
 = var1 vz1

v11 : ∀{Γ A B} → Tm1 (snoc1 (snoc1 Γ A) B) A; v11
 = var1 (vs1 vz1)

v21 : ∀{Γ A B C} → Tm1 (snoc1 (snoc1 (snoc1 Γ A) B) C) A; v21
 = var1 (vs1 (vs1 vz1))

v31 : ∀{Γ A B C D} → Tm1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) A; v31
 = var1 (vs1 (vs1 (vs1 vz1)))

tbool1 : Ty1; tbool1
 = sum1 top1 top1

true1 : ∀{Γ} → Tm1 Γ tbool1; true1
 = left1 tt1

tfalse1 : ∀{Γ} → Tm1 Γ tbool1; tfalse1
 = right1 tt1

ifthenelse1 : ∀{Γ A} → Tm1 Γ (arr1 tbool1 (arr1 A (arr1 A A))); ifthenelse1
 = lam1 (lam1 (lam1 (case1 v21 (lam1 v21) (lam1 v11))))

times41 : ∀{Γ A} → Tm1 Γ (arr1 (arr1 A A) (arr1 A A)); times41
  = lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01)))))

add1 : ∀{Γ} → Tm1 Γ (arr1 nat1 (arr1 nat1 nat1)); add1
 = lam1 (rec1 v01
       (lam1 (lam1 (lam1 (suc1 (app1 v11 v01)))))
       (lam1 v01))

mul1 : ∀{Γ} → Tm1 Γ (arr1 nat1 (arr1 nat1 nat1)); mul1
 = lam1 (rec1 v01
       (lam1 (lam1 (lam1 (app1 (app1 add1 (app1 v11 v01)) v01))))
       (lam1 zero1))

fact1 : ∀{Γ} → Tm1 Γ (arr1 nat1 nat1); fact1
 = lam1 (rec1 v01 (lam1 (lam1 (app1 (app1 mul1 (suc1 v11)) v01)))
        (suc1 zero1))
{-# OPTIONS --type-in-type #-}

Ty2 : Set
Ty2 =
   (Ty2         : Set)
   (nat top bot  : Ty2)
   (arr prod sum : Ty2 → Ty2 → Ty2)
 → Ty2

nat2 : Ty2; nat2 = λ _ nat2 _ _ _ _ _ → nat2
top2 : Ty2; top2 = λ _ _ top2 _ _ _ _ → top2
bot2 : Ty2; bot2 = λ _ _ _ bot2 _ _ _ → bot2

arr2 : Ty2 → Ty2 → Ty2; arr2
 = λ A B Ty2 nat2 top2 bot2 arr2 prod sum →
     arr2 (A Ty2 nat2 top2 bot2 arr2 prod sum) (B Ty2 nat2 top2 bot2 arr2 prod sum)

prod2 : Ty2 → Ty2 → Ty2; prod2
 = λ A B Ty2 nat2 top2 bot2 arr2 prod2 sum →
     prod2 (A Ty2 nat2 top2 bot2 arr2 prod2 sum) (B Ty2 nat2 top2 bot2 arr2 prod2 sum)

sum2 : Ty2 → Ty2 → Ty2; sum2
 = λ A B Ty2 nat2 top2 bot2 arr2 prod2 sum2 →
     sum2 (A Ty2 nat2 top2 bot2 arr2 prod2 sum2) (B Ty2 nat2 top2 bot2 arr2 prod2 sum2)

Con2 : Set; Con2
 = (Con2 : Set)
   (nil  : Con2)
   (snoc : Con2 → Ty2 → Con2)
 → Con2

nil2 : Con2; nil2
 = λ Con2 nil2 snoc → nil2

snoc2 : Con2 → Ty2 → Con2; snoc2
 = λ Γ A Con2 nil2 snoc2 → snoc2 (Γ Con2 nil2 snoc2) A

Var2 : Con2 → Ty2 → Set; Var2
 = λ Γ A →
   (Var2 : Con2 → Ty2 → Set)
   (vz  : ∀{Γ A} → Var2 (snoc2 Γ A) A)
   (vs  : ∀{Γ B A} → Var2 Γ A → Var2 (snoc2 Γ B) A)
 → Var2 Γ A

vz2 : ∀{Γ A} → Var2 (snoc2 Γ A) A; vz2
 = λ Var2 vz2 vs → vz2

vs2 : ∀{Γ B A} → Var2 Γ A → Var2 (snoc2 Γ B) A; vs2
 = λ x Var2 vz2 vs2 → vs2 (x Var2 vz2 vs2)

Tm2 : Con2 → Ty2 → Set; Tm2
 = λ Γ A →
   (Tm2  : Con2 → Ty2 → Set)
   (var   : ∀{Γ A} → Var2 Γ A → Tm2 Γ A)
   (lam   : ∀{Γ A B} → Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B))
   (app   : ∀{Γ A B} → Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B)
   (tt    : ∀{Γ} → Tm2 Γ top2)
   (pair  : ∀{Γ A B} → Tm2 Γ A → Tm2 Γ B → Tm2 Γ (prod2 A B))
   (fst   : ∀{Γ A B} → Tm2 Γ (prod2 A B) → Tm2 Γ A)
   (snd   : ∀{Γ A B} → Tm2 Γ (prod2 A B) → Tm2 Γ B)
   (left  : ∀{Γ A B} → Tm2 Γ A → Tm2 Γ (sum2 A B))
   (right : ∀{Γ A B} → Tm2 Γ B → Tm2 Γ (sum2 A B))
   (case  : ∀{Γ A B C} → Tm2 Γ (sum2 A B) → Tm2 Γ (arr2 A C) → Tm2 Γ (arr2 B C) → Tm2 Γ C)
   (zero  : ∀{Γ} → Tm2 Γ nat2)
   (suc   : ∀{Γ} → Tm2 Γ nat2 → Tm2 Γ nat2)
   (rec   : ∀{Γ A} → Tm2 Γ nat2 → Tm2 Γ (arr2 nat2 (arr2 A A)) → Tm2 Γ A → Tm2 Γ A)
 → Tm2 Γ A

var2 : ∀{Γ A} → Var2 Γ A → Tm2 Γ A; var2
 = λ x Tm2 var2 lam app tt pair fst snd left right case zero suc rec →
     var2 x

lam2 : ∀{Γ A B} → Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B); lam2
 = λ t Tm2 var2 lam2 app tt pair fst snd left right case zero suc rec →
     lam2 (t Tm2 var2 lam2 app tt pair fst snd left right case zero suc rec)

app2 : ∀{Γ A B} → Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B; app2
 = λ t u Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec →
     app2 (t Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec)
         (u Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec)

tt2 : ∀{Γ} → Tm2 Γ top2; tt2
 = λ Tm2 var2 lam2 app2 tt2 pair fst snd left right case zero suc rec → tt2

pair2 : ∀{Γ A B} → Tm2 Γ A → Tm2 Γ B → Tm2 Γ (prod2 A B); pair2
 = λ t u Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec →
     pair2 (t Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec)
          (u Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec)

fst2 : ∀{Γ A B} → Tm2 Γ (prod2 A B) → Tm2 Γ A; fst2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd left right case zero suc rec →
     fst2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd left right case zero suc rec)

snd2 : ∀{Γ A B} → Tm2 Γ (prod2 A B) → Tm2 Γ B; snd2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left right case zero suc rec →
     snd2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left right case zero suc rec)

left2 : ∀{Γ A B} → Tm2 Γ A → Tm2 Γ (sum2 A B); left2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right case zero suc rec →
     left2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right case zero suc rec)

right2 : ∀{Γ A B} → Tm2 Γ B → Tm2 Γ (sum2 A B); right2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case zero suc rec →
     right2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case zero suc rec)

case2 : ∀{Γ A B C} → Tm2 Γ (sum2 A B) → Tm2 Γ (arr2 A C) → Tm2 Γ (arr2 B C) → Tm2 Γ C; case2
 = λ t u v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec →
     case2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)
           (u Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)
           (v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)

zero2  : ∀{Γ} → Tm2 Γ nat2; zero2
 = λ Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc rec → zero2

suc2 : ∀{Γ} → Tm2 Γ nat2 → Tm2 Γ nat2; suc2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec →
   suc2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec)

rec2 : ∀{Γ A} → Tm2 Γ nat2 → Tm2 Γ (arr2 nat2 (arr2 A A)) → Tm2 Γ A → Tm2 Γ A; rec2
 = λ t u v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2 →
     rec2 (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)
         (u Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)
         (v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)

v02 : ∀{Γ A} → Tm2 (snoc2 Γ A) A; v02
 = var2 vz2

v12 : ∀{Γ A B} → Tm2 (snoc2 (snoc2 Γ A) B) A; v12
 = var2 (vs2 vz2)

v22 : ∀{Γ A B C} → Tm2 (snoc2 (snoc2 (snoc2 Γ A) B) C) A; v22
 = var2 (vs2 (vs2 vz2))

v32 : ∀{Γ A B C D} → Tm2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) A; v32
 = var2 (vs2 (vs2 (vs2 vz2)))

tbool2 : Ty2; tbool2
 = sum2 top2 top2

true2 : ∀{Γ} → Tm2 Γ tbool2; true2
 = left2 tt2

tfalse2 : ∀{Γ} → Tm2 Γ tbool2; tfalse2
 = right2 tt2

ifthenelse2 : ∀{Γ A} → Tm2 Γ (arr2 tbool2 (arr2 A (arr2 A A))); ifthenelse2
 = lam2 (lam2 (lam2 (case2 v22 (lam2 v22) (lam2 v12))))

times42 : ∀{Γ A} → Tm2 Γ (arr2 (arr2 A A) (arr2 A A)); times42
  = lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02)))))

add2 : ∀{Γ} → Tm2 Γ (arr2 nat2 (arr2 nat2 nat2)); add2
 = lam2 (rec2 v02
       (lam2 (lam2 (lam2 (suc2 (app2 v12 v02)))))
       (lam2 v02))

mul2 : ∀{Γ} → Tm2 Γ (arr2 nat2 (arr2 nat2 nat2)); mul2
 = lam2 (rec2 v02
       (lam2 (lam2 (lam2 (app2 (app2 add2 (app2 v12 v02)) v02))))
       (lam2 zero2))

fact2 : ∀{Γ} → Tm2 Γ (arr2 nat2 nat2); fact2
 = lam2 (rec2 v02 (lam2 (lam2 (app2 (app2 mul2 (suc2 v12)) v02)))
        (suc2 zero2))
{-# OPTIONS --type-in-type #-}

Ty3 : Set
Ty3 =
   (Ty3         : Set)
   (nat top bot  : Ty3)
   (arr prod sum : Ty3 → Ty3 → Ty3)
 → Ty3

nat3 : Ty3; nat3 = λ _ nat3 _ _ _ _ _ → nat3
top3 : Ty3; top3 = λ _ _ top3 _ _ _ _ → top3
bot3 : Ty3; bot3 = λ _ _ _ bot3 _ _ _ → bot3

arr3 : Ty3 → Ty3 → Ty3; arr3
 = λ A B Ty3 nat3 top3 bot3 arr3 prod sum →
     arr3 (A Ty3 nat3 top3 bot3 arr3 prod sum) (B Ty3 nat3 top3 bot3 arr3 prod sum)

prod3 : Ty3 → Ty3 → Ty3; prod3
 = λ A B Ty3 nat3 top3 bot3 arr3 prod3 sum →
     prod3 (A Ty3 nat3 top3 bot3 arr3 prod3 sum) (B Ty3 nat3 top3 bot3 arr3 prod3 sum)

sum3 : Ty3 → Ty3 → Ty3; sum3
 = λ A B Ty3 nat3 top3 bot3 arr3 prod3 sum3 →
     sum3 (A Ty3 nat3 top3 bot3 arr3 prod3 sum3) (B Ty3 nat3 top3 bot3 arr3 prod3 sum3)

Con3 : Set; Con3
 = (Con3 : Set)
   (nil  : Con3)
   (snoc : Con3 → Ty3 → Con3)
 → Con3

nil3 : Con3; nil3
 = λ Con3 nil3 snoc → nil3

snoc3 : Con3 → Ty3 → Con3; snoc3
 = λ Γ A Con3 nil3 snoc3 → snoc3 (Γ Con3 nil3 snoc3) A

Var3 : Con3 → Ty3 → Set; Var3
 = λ Γ A →
   (Var3 : Con3 → Ty3 → Set)
   (vz  : ∀{Γ A} → Var3 (snoc3 Γ A) A)
   (vs  : ∀{Γ B A} → Var3 Γ A → Var3 (snoc3 Γ B) A)
 → Var3 Γ A

vz3 : ∀{Γ A} → Var3 (snoc3 Γ A) A; vz3
 = λ Var3 vz3 vs → vz3

vs3 : ∀{Γ B A} → Var3 Γ A → Var3 (snoc3 Γ B) A; vs3
 = λ x Var3 vz3 vs3 → vs3 (x Var3 vz3 vs3)

Tm3 : Con3 → Ty3 → Set; Tm3
 = λ Γ A →
   (Tm3  : Con3 → Ty3 → Set)
   (var   : ∀{Γ A} → Var3 Γ A → Tm3 Γ A)
   (lam   : ∀{Γ A B} → Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B))
   (app   : ∀{Γ A B} → Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B)
   (tt    : ∀{Γ} → Tm3 Γ top3)
   (pair  : ∀{Γ A B} → Tm3 Γ A → Tm3 Γ B → Tm3 Γ (prod3 A B))
   (fst   : ∀{Γ A B} → Tm3 Γ (prod3 A B) → Tm3 Γ A)
   (snd   : ∀{Γ A B} → Tm3 Γ (prod3 A B) → Tm3 Γ B)
   (left  : ∀{Γ A B} → Tm3 Γ A → Tm3 Γ (sum3 A B))
   (right : ∀{Γ A B} → Tm3 Γ B → Tm3 Γ (sum3 A B))
   (case  : ∀{Γ A B C} → Tm3 Γ (sum3 A B) → Tm3 Γ (arr3 A C) → Tm3 Γ (arr3 B C) → Tm3 Γ C)
   (zero  : ∀{Γ} → Tm3 Γ nat3)
   (suc   : ∀{Γ} → Tm3 Γ nat3 → Tm3 Γ nat3)
   (rec   : ∀{Γ A} → Tm3 Γ nat3 → Tm3 Γ (arr3 nat3 (arr3 A A)) → Tm3 Γ A → Tm3 Γ A)
 → Tm3 Γ A

var3 : ∀{Γ A} → Var3 Γ A → Tm3 Γ A; var3
 = λ x Tm3 var3 lam app tt pair fst snd left right case zero suc rec →
     var3 x

lam3 : ∀{Γ A B} → Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B); lam3
 = λ t Tm3 var3 lam3 app tt pair fst snd left right case zero suc rec →
     lam3 (t Tm3 var3 lam3 app tt pair fst snd left right case zero suc rec)

app3 : ∀{Γ A B} → Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B; app3
 = λ t u Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec →
     app3 (t Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec)
         (u Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec)

tt3 : ∀{Γ} → Tm3 Γ top3; tt3
 = λ Tm3 var3 lam3 app3 tt3 pair fst snd left right case zero suc rec → tt3

pair3 : ∀{Γ A B} → Tm3 Γ A → Tm3 Γ B → Tm3 Γ (prod3 A B); pair3
 = λ t u Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec →
     pair3 (t Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec)
          (u Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec)

fst3 : ∀{Γ A B} → Tm3 Γ (prod3 A B) → Tm3 Γ A; fst3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd left right case zero suc rec →
     fst3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd left right case zero suc rec)

snd3 : ∀{Γ A B} → Tm3 Γ (prod3 A B) → Tm3 Γ B; snd3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left right case zero suc rec →
     snd3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left right case zero suc rec)

left3 : ∀{Γ A B} → Tm3 Γ A → Tm3 Γ (sum3 A B); left3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right case zero suc rec →
     left3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right case zero suc rec)

right3 : ∀{Γ A B} → Tm3 Γ B → Tm3 Γ (sum3 A B); right3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case zero suc rec →
     right3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case zero suc rec)

case3 : ∀{Γ A B C} → Tm3 Γ (sum3 A B) → Tm3 Γ (arr3 A C) → Tm3 Γ (arr3 B C) → Tm3 Γ C; case3
 = λ t u v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec →
     case3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)
           (u Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)
           (v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)

zero3  : ∀{Γ} → Tm3 Γ nat3; zero3
 = λ Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc rec → zero3

suc3 : ∀{Γ} → Tm3 Γ nat3 → Tm3 Γ nat3; suc3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec →
   suc3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec)

rec3 : ∀{Γ A} → Tm3 Γ nat3 → Tm3 Γ (arr3 nat3 (arr3 A A)) → Tm3 Γ A → Tm3 Γ A; rec3
 = λ t u v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3 →
     rec3 (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)
         (u Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)
         (v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)

v03 : ∀{Γ A} → Tm3 (snoc3 Γ A) A; v03
 = var3 vz3

v13 : ∀{Γ A B} → Tm3 (snoc3 (snoc3 Γ A) B) A; v13
 = var3 (vs3 vz3)

v23 : ∀{Γ A B C} → Tm3 (snoc3 (snoc3 (snoc3 Γ A) B) C) A; v23
 = var3 (vs3 (vs3 vz3))

v33 : ∀{Γ A B C D} → Tm3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) A; v33
 = var3 (vs3 (vs3 (vs3 vz3)))

tbool3 : Ty3; tbool3
 = sum3 top3 top3

true3 : ∀{Γ} → Tm3 Γ tbool3; true3
 = left3 tt3

tfalse3 : ∀{Γ} → Tm3 Γ tbool3; tfalse3
 = right3 tt3

ifthenelse3 : ∀{Γ A} → Tm3 Γ (arr3 tbool3 (arr3 A (arr3 A A))); ifthenelse3
 = lam3 (lam3 (lam3 (case3 v23 (lam3 v23) (lam3 v13))))

times43 : ∀{Γ A} → Tm3 Γ (arr3 (arr3 A A) (arr3 A A)); times43
  = lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03)))))

add3 : ∀{Γ} → Tm3 Γ (arr3 nat3 (arr3 nat3 nat3)); add3
 = lam3 (rec3 v03
       (lam3 (lam3 (lam3 (suc3 (app3 v13 v03)))))
       (lam3 v03))

mul3 : ∀{Γ} → Tm3 Γ (arr3 nat3 (arr3 nat3 nat3)); mul3
 = lam3 (rec3 v03
       (lam3 (lam3 (lam3 (app3 (app3 add3 (app3 v13 v03)) v03))))
       (lam3 zero3))

fact3 : ∀{Γ} → Tm3 Γ (arr3 nat3 nat3); fact3
 = lam3 (rec3 v03 (lam3 (lam3 (app3 (app3 mul3 (suc3 v13)) v03)))
        (suc3 zero3))
{-# OPTIONS --type-in-type #-}

Ty4 : Set
Ty4 =
   (Ty4         : Set)
   (nat top bot  : Ty4)
   (arr prod sum : Ty4 → Ty4 → Ty4)
 → Ty4

nat4 : Ty4; nat4 = λ _ nat4 _ _ _ _ _ → nat4
top4 : Ty4; top4 = λ _ _ top4 _ _ _ _ → top4
bot4 : Ty4; bot4 = λ _ _ _ bot4 _ _ _ → bot4

arr4 : Ty4 → Ty4 → Ty4; arr4
 = λ A B Ty4 nat4 top4 bot4 arr4 prod sum →
     arr4 (A Ty4 nat4 top4 bot4 arr4 prod sum) (B Ty4 nat4 top4 bot4 arr4 prod sum)

prod4 : Ty4 → Ty4 → Ty4; prod4
 = λ A B Ty4 nat4 top4 bot4 arr4 prod4 sum →
     prod4 (A Ty4 nat4 top4 bot4 arr4 prod4 sum) (B Ty4 nat4 top4 bot4 arr4 prod4 sum)

sum4 : Ty4 → Ty4 → Ty4; sum4
 = λ A B Ty4 nat4 top4 bot4 arr4 prod4 sum4 →
     sum4 (A Ty4 nat4 top4 bot4 arr4 prod4 sum4) (B Ty4 nat4 top4 bot4 arr4 prod4 sum4)

Con4 : Set; Con4
 = (Con4 : Set)
   (nil  : Con4)
   (snoc : Con4 → Ty4 → Con4)
 → Con4

nil4 : Con4; nil4
 = λ Con4 nil4 snoc → nil4

snoc4 : Con4 → Ty4 → Con4; snoc4
 = λ Γ A Con4 nil4 snoc4 → snoc4 (Γ Con4 nil4 snoc4) A

Var4 : Con4 → Ty4 → Set; Var4
 = λ Γ A →
   (Var4 : Con4 → Ty4 → Set)
   (vz  : ∀{Γ A} → Var4 (snoc4 Γ A) A)
   (vs  : ∀{Γ B A} → Var4 Γ A → Var4 (snoc4 Γ B) A)
 → Var4 Γ A

vz4 : ∀{Γ A} → Var4 (snoc4 Γ A) A; vz4
 = λ Var4 vz4 vs → vz4

vs4 : ∀{Γ B A} → Var4 Γ A → Var4 (snoc4 Γ B) A; vs4
 = λ x Var4 vz4 vs4 → vs4 (x Var4 vz4 vs4)

Tm4 : Con4 → Ty4 → Set; Tm4
 = λ Γ A →
   (Tm4  : Con4 → Ty4 → Set)
   (var   : ∀{Γ A} → Var4 Γ A → Tm4 Γ A)
   (lam   : ∀{Γ A B} → Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B))
   (app   : ∀{Γ A B} → Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B)
   (tt    : ∀{Γ} → Tm4 Γ top4)
   (pair  : ∀{Γ A B} → Tm4 Γ A → Tm4 Γ B → Tm4 Γ (prod4 A B))
   (fst   : ∀{Γ A B} → Tm4 Γ (prod4 A B) → Tm4 Γ A)
   (snd   : ∀{Γ A B} → Tm4 Γ (prod4 A B) → Tm4 Γ B)
   (left  : ∀{Γ A B} → Tm4 Γ A → Tm4 Γ (sum4 A B))
   (right : ∀{Γ A B} → Tm4 Γ B → Tm4 Γ (sum4 A B))
   (case  : ∀{Γ A B C} → Tm4 Γ (sum4 A B) → Tm4 Γ (arr4 A C) → Tm4 Γ (arr4 B C) → Tm4 Γ C)
   (zero  : ∀{Γ} → Tm4 Γ nat4)
   (suc   : ∀{Γ} → Tm4 Γ nat4 → Tm4 Γ nat4)
   (rec   : ∀{Γ A} → Tm4 Γ nat4 → Tm4 Γ (arr4 nat4 (arr4 A A)) → Tm4 Γ A → Tm4 Γ A)
 → Tm4 Γ A

var4 : ∀{Γ A} → Var4 Γ A → Tm4 Γ A; var4
 = λ x Tm4 var4 lam app tt pair fst snd left right case zero suc rec →
     var4 x

lam4 : ∀{Γ A B} → Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B); lam4
 = λ t Tm4 var4 lam4 app tt pair fst snd left right case zero suc rec →
     lam4 (t Tm4 var4 lam4 app tt pair fst snd left right case zero suc rec)

app4 : ∀{Γ A B} → Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B; app4
 = λ t u Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec →
     app4 (t Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec)
         (u Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec)

tt4 : ∀{Γ} → Tm4 Γ top4; tt4
 = λ Tm4 var4 lam4 app4 tt4 pair fst snd left right case zero suc rec → tt4

pair4 : ∀{Γ A B} → Tm4 Γ A → Tm4 Γ B → Tm4 Γ (prod4 A B); pair4
 = λ t u Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec →
     pair4 (t Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec)
          (u Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec)

fst4 : ∀{Γ A B} → Tm4 Γ (prod4 A B) → Tm4 Γ A; fst4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd left right case zero suc rec →
     fst4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd left right case zero suc rec)

snd4 : ∀{Γ A B} → Tm4 Γ (prod4 A B) → Tm4 Γ B; snd4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left right case zero suc rec →
     snd4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left right case zero suc rec)

left4 : ∀{Γ A B} → Tm4 Γ A → Tm4 Γ (sum4 A B); left4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right case zero suc rec →
     left4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right case zero suc rec)

right4 : ∀{Γ A B} → Tm4 Γ B → Tm4 Γ (sum4 A B); right4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case zero suc rec →
     right4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case zero suc rec)

case4 : ∀{Γ A B C} → Tm4 Γ (sum4 A B) → Tm4 Γ (arr4 A C) → Tm4 Γ (arr4 B C) → Tm4 Γ C; case4
 = λ t u v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec →
     case4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)
           (u Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)
           (v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)

zero4  : ∀{Γ} → Tm4 Γ nat4; zero4
 = λ Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc rec → zero4

suc4 : ∀{Γ} → Tm4 Γ nat4 → Tm4 Γ nat4; suc4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec →
   suc4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec)

rec4 : ∀{Γ A} → Tm4 Γ nat4 → Tm4 Γ (arr4 nat4 (arr4 A A)) → Tm4 Γ A → Tm4 Γ A; rec4
 = λ t u v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4 →
     rec4 (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)
         (u Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)
         (v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)

v04 : ∀{Γ A} → Tm4 (snoc4 Γ A) A; v04
 = var4 vz4

v14 : ∀{Γ A B} → Tm4 (snoc4 (snoc4 Γ A) B) A; v14
 = var4 (vs4 vz4)

v24 : ∀{Γ A B C} → Tm4 (snoc4 (snoc4 (snoc4 Γ A) B) C) A; v24
 = var4 (vs4 (vs4 vz4))

v34 : ∀{Γ A B C D} → Tm4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) A; v34
 = var4 (vs4 (vs4 (vs4 vz4)))

tbool4 : Ty4; tbool4
 = sum4 top4 top4

true4 : ∀{Γ} → Tm4 Γ tbool4; true4
 = left4 tt4

tfalse4 : ∀{Γ} → Tm4 Γ tbool4; tfalse4
 = right4 tt4

ifthenelse4 : ∀{Γ A} → Tm4 Γ (arr4 tbool4 (arr4 A (arr4 A A))); ifthenelse4
 = lam4 (lam4 (lam4 (case4 v24 (lam4 v24) (lam4 v14))))

times44 : ∀{Γ A} → Tm4 Γ (arr4 (arr4 A A) (arr4 A A)); times44
  = lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04)))))

add4 : ∀{Γ} → Tm4 Γ (arr4 nat4 (arr4 nat4 nat4)); add4
 = lam4 (rec4 v04
       (lam4 (lam4 (lam4 (suc4 (app4 v14 v04)))))
       (lam4 v04))

mul4 : ∀{Γ} → Tm4 Γ (arr4 nat4 (arr4 nat4 nat4)); mul4
 = lam4 (rec4 v04
       (lam4 (lam4 (lam4 (app4 (app4 add4 (app4 v14 v04)) v04))))
       (lam4 zero4))

fact4 : ∀{Γ} → Tm4 Γ (arr4 nat4 nat4); fact4
 = lam4 (rec4 v04 (lam4 (lam4 (app4 (app4 mul4 (suc4 v14)) v04)))
        (suc4 zero4))
{-# OPTIONS --type-in-type #-}

Ty5 : Set
Ty5 =
   (Ty5         : Set)
   (nat top bot  : Ty5)
   (arr prod sum : Ty5 → Ty5 → Ty5)
 → Ty5

nat5 : Ty5; nat5 = λ _ nat5 _ _ _ _ _ → nat5
top5 : Ty5; top5 = λ _ _ top5 _ _ _ _ → top5
bot5 : Ty5; bot5 = λ _ _ _ bot5 _ _ _ → bot5

arr5 : Ty5 → Ty5 → Ty5; arr5
 = λ A B Ty5 nat5 top5 bot5 arr5 prod sum →
     arr5 (A Ty5 nat5 top5 bot5 arr5 prod sum) (B Ty5 nat5 top5 bot5 arr5 prod sum)

prod5 : Ty5 → Ty5 → Ty5; prod5
 = λ A B Ty5 nat5 top5 bot5 arr5 prod5 sum →
     prod5 (A Ty5 nat5 top5 bot5 arr5 prod5 sum) (B Ty5 nat5 top5 bot5 arr5 prod5 sum)

sum5 : Ty5 → Ty5 → Ty5; sum5
 = λ A B Ty5 nat5 top5 bot5 arr5 prod5 sum5 →
     sum5 (A Ty5 nat5 top5 bot5 arr5 prod5 sum5) (B Ty5 nat5 top5 bot5 arr5 prod5 sum5)

Con5 : Set; Con5
 = (Con5 : Set)
   (nil  : Con5)
   (snoc : Con5 → Ty5 → Con5)
 → Con5

nil5 : Con5; nil5
 = λ Con5 nil5 snoc → nil5

snoc5 : Con5 → Ty5 → Con5; snoc5
 = λ Γ A Con5 nil5 snoc5 → snoc5 (Γ Con5 nil5 snoc5) A

Var5 : Con5 → Ty5 → Set; Var5
 = λ Γ A →
   (Var5 : Con5 → Ty5 → Set)
   (vz  : ∀{Γ A} → Var5 (snoc5 Γ A) A)
   (vs  : ∀{Γ B A} → Var5 Γ A → Var5 (snoc5 Γ B) A)
 → Var5 Γ A

vz5 : ∀{Γ A} → Var5 (snoc5 Γ A) A; vz5
 = λ Var5 vz5 vs → vz5

vs5 : ∀{Γ B A} → Var5 Γ A → Var5 (snoc5 Γ B) A; vs5
 = λ x Var5 vz5 vs5 → vs5 (x Var5 vz5 vs5)

Tm5 : Con5 → Ty5 → Set; Tm5
 = λ Γ A →
   (Tm5  : Con5 → Ty5 → Set)
   (var   : ∀{Γ A} → Var5 Γ A → Tm5 Γ A)
   (lam   : ∀{Γ A B} → Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B))
   (app   : ∀{Γ A B} → Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B)
   (tt    : ∀{Γ} → Tm5 Γ top5)
   (pair  : ∀{Γ A B} → Tm5 Γ A → Tm5 Γ B → Tm5 Γ (prod5 A B))
   (fst   : ∀{Γ A B} → Tm5 Γ (prod5 A B) → Tm5 Γ A)
   (snd   : ∀{Γ A B} → Tm5 Γ (prod5 A B) → Tm5 Γ B)
   (left  : ∀{Γ A B} → Tm5 Γ A → Tm5 Γ (sum5 A B))
   (right : ∀{Γ A B} → Tm5 Γ B → Tm5 Γ (sum5 A B))
   (case  : ∀{Γ A B C} → Tm5 Γ (sum5 A B) → Tm5 Γ (arr5 A C) → Tm5 Γ (arr5 B C) → Tm5 Γ C)
   (zero  : ∀{Γ} → Tm5 Γ nat5)
   (suc   : ∀{Γ} → Tm5 Γ nat5 → Tm5 Γ nat5)
   (rec   : ∀{Γ A} → Tm5 Γ nat5 → Tm5 Γ (arr5 nat5 (arr5 A A)) → Tm5 Γ A → Tm5 Γ A)
 → Tm5 Γ A

var5 : ∀{Γ A} → Var5 Γ A → Tm5 Γ A; var5
 = λ x Tm5 var5 lam app tt pair fst snd left right case zero suc rec →
     var5 x

lam5 : ∀{Γ A B} → Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B); lam5
 = λ t Tm5 var5 lam5 app tt pair fst snd left right case zero suc rec →
     lam5 (t Tm5 var5 lam5 app tt pair fst snd left right case zero suc rec)

app5 : ∀{Γ A B} → Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B; app5
 = λ t u Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec →
     app5 (t Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec)
         (u Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec)

tt5 : ∀{Γ} → Tm5 Γ top5; tt5
 = λ Tm5 var5 lam5 app5 tt5 pair fst snd left right case zero suc rec → tt5

pair5 : ∀{Γ A B} → Tm5 Γ A → Tm5 Γ B → Tm5 Γ (prod5 A B); pair5
 = λ t u Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec →
     pair5 (t Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec)
          (u Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec)

fst5 : ∀{Γ A B} → Tm5 Γ (prod5 A B) → Tm5 Γ A; fst5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd left right case zero suc rec →
     fst5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd left right case zero suc rec)

snd5 : ∀{Γ A B} → Tm5 Γ (prod5 A B) → Tm5 Γ B; snd5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left right case zero suc rec →
     snd5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left right case zero suc rec)

left5 : ∀{Γ A B} → Tm5 Γ A → Tm5 Γ (sum5 A B); left5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right case zero suc rec →
     left5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right case zero suc rec)

right5 : ∀{Γ A B} → Tm5 Γ B → Tm5 Γ (sum5 A B); right5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case zero suc rec →
     right5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case zero suc rec)

case5 : ∀{Γ A B C} → Tm5 Γ (sum5 A B) → Tm5 Γ (arr5 A C) → Tm5 Γ (arr5 B C) → Tm5 Γ C; case5
 = λ t u v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec →
     case5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)
           (u Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)
           (v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)

zero5  : ∀{Γ} → Tm5 Γ nat5; zero5
 = λ Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc rec → zero5

suc5 : ∀{Γ} → Tm5 Γ nat5 → Tm5 Γ nat5; suc5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec →
   suc5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec)

rec5 : ∀{Γ A} → Tm5 Γ nat5 → Tm5 Γ (arr5 nat5 (arr5 A A)) → Tm5 Γ A → Tm5 Γ A; rec5
 = λ t u v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5 →
     rec5 (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)
         (u Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)
         (v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)

v05 : ∀{Γ A} → Tm5 (snoc5 Γ A) A; v05
 = var5 vz5

v15 : ∀{Γ A B} → Tm5 (snoc5 (snoc5 Γ A) B) A; v15
 = var5 (vs5 vz5)

v25 : ∀{Γ A B C} → Tm5 (snoc5 (snoc5 (snoc5 Γ A) B) C) A; v25
 = var5 (vs5 (vs5 vz5))

v35 : ∀{Γ A B C D} → Tm5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) A; v35
 = var5 (vs5 (vs5 (vs5 vz5)))

tbool5 : Ty5; tbool5
 = sum5 top5 top5

true5 : ∀{Γ} → Tm5 Γ tbool5; true5
 = left5 tt5

tfalse5 : ∀{Γ} → Tm5 Γ tbool5; tfalse5
 = right5 tt5

ifthenelse5 : ∀{Γ A} → Tm5 Γ (arr5 tbool5 (arr5 A (arr5 A A))); ifthenelse5
 = lam5 (lam5 (lam5 (case5 v25 (lam5 v25) (lam5 v15))))

times45 : ∀{Γ A} → Tm5 Γ (arr5 (arr5 A A) (arr5 A A)); times45
  = lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05)))))

add5 : ∀{Γ} → Tm5 Γ (arr5 nat5 (arr5 nat5 nat5)); add5
 = lam5 (rec5 v05
       (lam5 (lam5 (lam5 (suc5 (app5 v15 v05)))))
       (lam5 v05))

mul5 : ∀{Γ} → Tm5 Γ (arr5 nat5 (arr5 nat5 nat5)); mul5
 = lam5 (rec5 v05
       (lam5 (lam5 (lam5 (app5 (app5 add5 (app5 v15 v05)) v05))))
       (lam5 zero5))

fact5 : ∀{Γ} → Tm5 Γ (arr5 nat5 nat5); fact5
 = lam5 (rec5 v05 (lam5 (lam5 (app5 (app5 mul5 (suc5 v15)) v05)))
        (suc5 zero5))
{-# OPTIONS --type-in-type #-}

Ty6 : Set
Ty6 =
   (Ty6         : Set)
   (nat top bot  : Ty6)
   (arr prod sum : Ty6 → Ty6 → Ty6)
 → Ty6

nat6 : Ty6; nat6 = λ _ nat6 _ _ _ _ _ → nat6
top6 : Ty6; top6 = λ _ _ top6 _ _ _ _ → top6
bot6 : Ty6; bot6 = λ _ _ _ bot6 _ _ _ → bot6

arr6 : Ty6 → Ty6 → Ty6; arr6
 = λ A B Ty6 nat6 top6 bot6 arr6 prod sum →
     arr6 (A Ty6 nat6 top6 bot6 arr6 prod sum) (B Ty6 nat6 top6 bot6 arr6 prod sum)

prod6 : Ty6 → Ty6 → Ty6; prod6
 = λ A B Ty6 nat6 top6 bot6 arr6 prod6 sum →
     prod6 (A Ty6 nat6 top6 bot6 arr6 prod6 sum) (B Ty6 nat6 top6 bot6 arr6 prod6 sum)

sum6 : Ty6 → Ty6 → Ty6; sum6
 = λ A B Ty6 nat6 top6 bot6 arr6 prod6 sum6 →
     sum6 (A Ty6 nat6 top6 bot6 arr6 prod6 sum6) (B Ty6 nat6 top6 bot6 arr6 prod6 sum6)

Con6 : Set; Con6
 = (Con6 : Set)
   (nil  : Con6)
   (snoc : Con6 → Ty6 → Con6)
 → Con6

nil6 : Con6; nil6
 = λ Con6 nil6 snoc → nil6

snoc6 : Con6 → Ty6 → Con6; snoc6
 = λ Γ A Con6 nil6 snoc6 → snoc6 (Γ Con6 nil6 snoc6) A

Var6 : Con6 → Ty6 → Set; Var6
 = λ Γ A →
   (Var6 : Con6 → Ty6 → Set)
   (vz  : ∀{Γ A} → Var6 (snoc6 Γ A) A)
   (vs  : ∀{Γ B A} → Var6 Γ A → Var6 (snoc6 Γ B) A)
 → Var6 Γ A

vz6 : ∀{Γ A} → Var6 (snoc6 Γ A) A; vz6
 = λ Var6 vz6 vs → vz6

vs6 : ∀{Γ B A} → Var6 Γ A → Var6 (snoc6 Γ B) A; vs6
 = λ x Var6 vz6 vs6 → vs6 (x Var6 vz6 vs6)

Tm6 : Con6 → Ty6 → Set; Tm6
 = λ Γ A →
   (Tm6  : Con6 → Ty6 → Set)
   (var   : ∀{Γ A} → Var6 Γ A → Tm6 Γ A)
   (lam   : ∀{Γ A B} → Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B))
   (app   : ∀{Γ A B} → Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B)
   (tt    : ∀{Γ} → Tm6 Γ top6)
   (pair  : ∀{Γ A B} → Tm6 Γ A → Tm6 Γ B → Tm6 Γ (prod6 A B))
   (fst   : ∀{Γ A B} → Tm6 Γ (prod6 A B) → Tm6 Γ A)
   (snd   : ∀{Γ A B} → Tm6 Γ (prod6 A B) → Tm6 Γ B)
   (left  : ∀{Γ A B} → Tm6 Γ A → Tm6 Γ (sum6 A B))
   (right : ∀{Γ A B} → Tm6 Γ B → Tm6 Γ (sum6 A B))
   (case  : ∀{Γ A B C} → Tm6 Γ (sum6 A B) → Tm6 Γ (arr6 A C) → Tm6 Γ (arr6 B C) → Tm6 Γ C)
   (zero  : ∀{Γ} → Tm6 Γ nat6)
   (suc   : ∀{Γ} → Tm6 Γ nat6 → Tm6 Γ nat6)
   (rec   : ∀{Γ A} → Tm6 Γ nat6 → Tm6 Γ (arr6 nat6 (arr6 A A)) → Tm6 Γ A → Tm6 Γ A)
 → Tm6 Γ A

var6 : ∀{Γ A} → Var6 Γ A → Tm6 Γ A; var6
 = λ x Tm6 var6 lam app tt pair fst snd left right case zero suc rec →
     var6 x

lam6 : ∀{Γ A B} → Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B); lam6
 = λ t Tm6 var6 lam6 app tt pair fst snd left right case zero suc rec →
     lam6 (t Tm6 var6 lam6 app tt pair fst snd left right case zero suc rec)

app6 : ∀{Γ A B} → Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B; app6
 = λ t u Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec →
     app6 (t Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec)
         (u Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec)

tt6 : ∀{Γ} → Tm6 Γ top6; tt6
 = λ Tm6 var6 lam6 app6 tt6 pair fst snd left right case zero suc rec → tt6

pair6 : ∀{Γ A B} → Tm6 Γ A → Tm6 Γ B → Tm6 Γ (prod6 A B); pair6
 = λ t u Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec →
     pair6 (t Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec)
          (u Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec)

fst6 : ∀{Γ A B} → Tm6 Γ (prod6 A B) → Tm6 Γ A; fst6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd left right case zero suc rec →
     fst6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd left right case zero suc rec)

snd6 : ∀{Γ A B} → Tm6 Γ (prod6 A B) → Tm6 Γ B; snd6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left right case zero suc rec →
     snd6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left right case zero suc rec)

left6 : ∀{Γ A B} → Tm6 Γ A → Tm6 Γ (sum6 A B); left6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right case zero suc rec →
     left6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right case zero suc rec)

right6 : ∀{Γ A B} → Tm6 Γ B → Tm6 Γ (sum6 A B); right6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case zero suc rec →
     right6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case zero suc rec)

case6 : ∀{Γ A B C} → Tm6 Γ (sum6 A B) → Tm6 Γ (arr6 A C) → Tm6 Γ (arr6 B C) → Tm6 Γ C; case6
 = λ t u v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec →
     case6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)
           (u Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)
           (v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)

zero6  : ∀{Γ} → Tm6 Γ nat6; zero6
 = λ Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc rec → zero6

suc6 : ∀{Γ} → Tm6 Γ nat6 → Tm6 Γ nat6; suc6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec →
   suc6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec)

rec6 : ∀{Γ A} → Tm6 Γ nat6 → Tm6 Γ (arr6 nat6 (arr6 A A)) → Tm6 Γ A → Tm6 Γ A; rec6
 = λ t u v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6 →
     rec6 (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)
         (u Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)
         (v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)

v06 : ∀{Γ A} → Tm6 (snoc6 Γ A) A; v06
 = var6 vz6

v16 : ∀{Γ A B} → Tm6 (snoc6 (snoc6 Γ A) B) A; v16
 = var6 (vs6 vz6)

v26 : ∀{Γ A B C} → Tm6 (snoc6 (snoc6 (snoc6 Γ A) B) C) A; v26
 = var6 (vs6 (vs6 vz6))

v36 : ∀{Γ A B C D} → Tm6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) A; v36
 = var6 (vs6 (vs6 (vs6 vz6)))

tbool6 : Ty6; tbool6
 = sum6 top6 top6

true6 : ∀{Γ} → Tm6 Γ tbool6; true6
 = left6 tt6

tfalse6 : ∀{Γ} → Tm6 Γ tbool6; tfalse6
 = right6 tt6

ifthenelse6 : ∀{Γ A} → Tm6 Γ (arr6 tbool6 (arr6 A (arr6 A A))); ifthenelse6
 = lam6 (lam6 (lam6 (case6 v26 (lam6 v26) (lam6 v16))))

times46 : ∀{Γ A} → Tm6 Γ (arr6 (arr6 A A) (arr6 A A)); times46
  = lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06)))))

add6 : ∀{Γ} → Tm6 Γ (arr6 nat6 (arr6 nat6 nat6)); add6
 = lam6 (rec6 v06
       (lam6 (lam6 (lam6 (suc6 (app6 v16 v06)))))
       (lam6 v06))

mul6 : ∀{Γ} → Tm6 Γ (arr6 nat6 (arr6 nat6 nat6)); mul6
 = lam6 (rec6 v06
       (lam6 (lam6 (lam6 (app6 (app6 add6 (app6 v16 v06)) v06))))
       (lam6 zero6))

fact6 : ∀{Γ} → Tm6 Γ (arr6 nat6 nat6); fact6
 = lam6 (rec6 v06 (lam6 (lam6 (app6 (app6 mul6 (suc6 v16)) v06)))
        (suc6 zero6))
{-# OPTIONS --type-in-type #-}

Ty7 : Set
Ty7 =
   (Ty7         : Set)
   (nat top bot  : Ty7)
   (arr prod sum : Ty7 → Ty7 → Ty7)
 → Ty7

nat7 : Ty7; nat7 = λ _ nat7 _ _ _ _ _ → nat7
top7 : Ty7; top7 = λ _ _ top7 _ _ _ _ → top7
bot7 : Ty7; bot7 = λ _ _ _ bot7 _ _ _ → bot7

arr7 : Ty7 → Ty7 → Ty7; arr7
 = λ A B Ty7 nat7 top7 bot7 arr7 prod sum →
     arr7 (A Ty7 nat7 top7 bot7 arr7 prod sum) (B Ty7 nat7 top7 bot7 arr7 prod sum)

prod7 : Ty7 → Ty7 → Ty7; prod7
 = λ A B Ty7 nat7 top7 bot7 arr7 prod7 sum →
     prod7 (A Ty7 nat7 top7 bot7 arr7 prod7 sum) (B Ty7 nat7 top7 bot7 arr7 prod7 sum)

sum7 : Ty7 → Ty7 → Ty7; sum7
 = λ A B Ty7 nat7 top7 bot7 arr7 prod7 sum7 →
     sum7 (A Ty7 nat7 top7 bot7 arr7 prod7 sum7) (B Ty7 nat7 top7 bot7 arr7 prod7 sum7)

Con7 : Set; Con7
 = (Con7 : Set)
   (nil  : Con7)
   (snoc : Con7 → Ty7 → Con7)
 → Con7

nil7 : Con7; nil7
 = λ Con7 nil7 snoc → nil7

snoc7 : Con7 → Ty7 → Con7; snoc7
 = λ Γ A Con7 nil7 snoc7 → snoc7 (Γ Con7 nil7 snoc7) A

Var7 : Con7 → Ty7 → Set; Var7
 = λ Γ A →
   (Var7 : Con7 → Ty7 → Set)
   (vz  : ∀{Γ A} → Var7 (snoc7 Γ A) A)
   (vs  : ∀{Γ B A} → Var7 Γ A → Var7 (snoc7 Γ B) A)
 → Var7 Γ A

vz7 : ∀{Γ A} → Var7 (snoc7 Γ A) A; vz7
 = λ Var7 vz7 vs → vz7

vs7 : ∀{Γ B A} → Var7 Γ A → Var7 (snoc7 Γ B) A; vs7
 = λ x Var7 vz7 vs7 → vs7 (x Var7 vz7 vs7)

Tm7 : Con7 → Ty7 → Set; Tm7
 = λ Γ A →
   (Tm7  : Con7 → Ty7 → Set)
   (var   : ∀{Γ A} → Var7 Γ A → Tm7 Γ A)
   (lam   : ∀{Γ A B} → Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B))
   (app   : ∀{Γ A B} → Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B)
   (tt    : ∀{Γ} → Tm7 Γ top7)
   (pair  : ∀{Γ A B} → Tm7 Γ A → Tm7 Γ B → Tm7 Γ (prod7 A B))
   (fst   : ∀{Γ A B} → Tm7 Γ (prod7 A B) → Tm7 Γ A)
   (snd   : ∀{Γ A B} → Tm7 Γ (prod7 A B) → Tm7 Γ B)
   (left  : ∀{Γ A B} → Tm7 Γ A → Tm7 Γ (sum7 A B))
   (right : ∀{Γ A B} → Tm7 Γ B → Tm7 Γ (sum7 A B))
   (case  : ∀{Γ A B C} → Tm7 Γ (sum7 A B) → Tm7 Γ (arr7 A C) → Tm7 Γ (arr7 B C) → Tm7 Γ C)
   (zero  : ∀{Γ} → Tm7 Γ nat7)
   (suc   : ∀{Γ} → Tm7 Γ nat7 → Tm7 Γ nat7)
   (rec   : ∀{Γ A} → Tm7 Γ nat7 → Tm7 Γ (arr7 nat7 (arr7 A A)) → Tm7 Γ A → Tm7 Γ A)
 → Tm7 Γ A

var7 : ∀{Γ A} → Var7 Γ A → Tm7 Γ A; var7
 = λ x Tm7 var7 lam app tt pair fst snd left right case zero suc rec →
     var7 x

lam7 : ∀{Γ A B} → Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B); lam7
 = λ t Tm7 var7 lam7 app tt pair fst snd left right case zero suc rec →
     lam7 (t Tm7 var7 lam7 app tt pair fst snd left right case zero suc rec)

app7 : ∀{Γ A B} → Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B; app7
 = λ t u Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec →
     app7 (t Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec)
         (u Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec)

tt7 : ∀{Γ} → Tm7 Γ top7; tt7
 = λ Tm7 var7 lam7 app7 tt7 pair fst snd left right case zero suc rec → tt7

pair7 : ∀{Γ A B} → Tm7 Γ A → Tm7 Γ B → Tm7 Γ (prod7 A B); pair7
 = λ t u Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec →
     pair7 (t Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec)
          (u Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec)

fst7 : ∀{Γ A B} → Tm7 Γ (prod7 A B) → Tm7 Γ A; fst7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd left right case zero suc rec →
     fst7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd left right case zero suc rec)

snd7 : ∀{Γ A B} → Tm7 Γ (prod7 A B) → Tm7 Γ B; snd7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left right case zero suc rec →
     snd7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left right case zero suc rec)

left7 : ∀{Γ A B} → Tm7 Γ A → Tm7 Γ (sum7 A B); left7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right case zero suc rec →
     left7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right case zero suc rec)

right7 : ∀{Γ A B} → Tm7 Γ B → Tm7 Γ (sum7 A B); right7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case zero suc rec →
     right7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case zero suc rec)

case7 : ∀{Γ A B C} → Tm7 Γ (sum7 A B) → Tm7 Γ (arr7 A C) → Tm7 Γ (arr7 B C) → Tm7 Γ C; case7
 = λ t u v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec →
     case7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)
           (u Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)
           (v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)

zero7  : ∀{Γ} → Tm7 Γ nat7; zero7
 = λ Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc rec → zero7

suc7 : ∀{Γ} → Tm7 Γ nat7 → Tm7 Γ nat7; suc7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec →
   suc7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec)

rec7 : ∀{Γ A} → Tm7 Γ nat7 → Tm7 Γ (arr7 nat7 (arr7 A A)) → Tm7 Γ A → Tm7 Γ A; rec7
 = λ t u v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7 →
     rec7 (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)
         (u Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)
         (v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)

v07 : ∀{Γ A} → Tm7 (snoc7 Γ A) A; v07
 = var7 vz7

v17 : ∀{Γ A B} → Tm7 (snoc7 (snoc7 Γ A) B) A; v17
 = var7 (vs7 vz7)

v27 : ∀{Γ A B C} → Tm7 (snoc7 (snoc7 (snoc7 Γ A) B) C) A; v27
 = var7 (vs7 (vs7 vz7))

v37 : ∀{Γ A B C D} → Tm7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) A; v37
 = var7 (vs7 (vs7 (vs7 vz7)))

tbool7 : Ty7; tbool7
 = sum7 top7 top7

true7 : ∀{Γ} → Tm7 Γ tbool7; true7
 = left7 tt7

tfalse7 : ∀{Γ} → Tm7 Γ tbool7; tfalse7
 = right7 tt7

ifthenelse7 : ∀{Γ A} → Tm7 Γ (arr7 tbool7 (arr7 A (arr7 A A))); ifthenelse7
 = lam7 (lam7 (lam7 (case7 v27 (lam7 v27) (lam7 v17))))

times47 : ∀{Γ A} → Tm7 Γ (arr7 (arr7 A A) (arr7 A A)); times47
  = lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07)))))

add7 : ∀{Γ} → Tm7 Γ (arr7 nat7 (arr7 nat7 nat7)); add7
 = lam7 (rec7 v07
       (lam7 (lam7 (lam7 (suc7 (app7 v17 v07)))))
       (lam7 v07))

mul7 : ∀{Γ} → Tm7 Γ (arr7 nat7 (arr7 nat7 nat7)); mul7
 = lam7 (rec7 v07
       (lam7 (lam7 (lam7 (app7 (app7 add7 (app7 v17 v07)) v07))))
       (lam7 zero7))

fact7 : ∀{Γ} → Tm7 Γ (arr7 nat7 nat7); fact7
 = lam7 (rec7 v07 (lam7 (lam7 (app7 (app7 mul7 (suc7 v17)) v07)))
        (suc7 zero7))
{-# OPTIONS --type-in-type #-}

Ty8 : Set
Ty8 =
   (Ty8         : Set)
   (nat top bot  : Ty8)
   (arr prod sum : Ty8 → Ty8 → Ty8)
 → Ty8

nat8 : Ty8; nat8 = λ _ nat8 _ _ _ _ _ → nat8
top8 : Ty8; top8 = λ _ _ top8 _ _ _ _ → top8
bot8 : Ty8; bot8 = λ _ _ _ bot8 _ _ _ → bot8

arr8 : Ty8 → Ty8 → Ty8; arr8
 = λ A B Ty8 nat8 top8 bot8 arr8 prod sum →
     arr8 (A Ty8 nat8 top8 bot8 arr8 prod sum) (B Ty8 nat8 top8 bot8 arr8 prod sum)

prod8 : Ty8 → Ty8 → Ty8; prod8
 = λ A B Ty8 nat8 top8 bot8 arr8 prod8 sum →
     prod8 (A Ty8 nat8 top8 bot8 arr8 prod8 sum) (B Ty8 nat8 top8 bot8 arr8 prod8 sum)

sum8 : Ty8 → Ty8 → Ty8; sum8
 = λ A B Ty8 nat8 top8 bot8 arr8 prod8 sum8 →
     sum8 (A Ty8 nat8 top8 bot8 arr8 prod8 sum8) (B Ty8 nat8 top8 bot8 arr8 prod8 sum8)

Con8 : Set; Con8
 = (Con8 : Set)
   (nil  : Con8)
   (snoc : Con8 → Ty8 → Con8)
 → Con8

nil8 : Con8; nil8
 = λ Con8 nil8 snoc → nil8

snoc8 : Con8 → Ty8 → Con8; snoc8
 = λ Γ A Con8 nil8 snoc8 → snoc8 (Γ Con8 nil8 snoc8) A

Var8 : Con8 → Ty8 → Set; Var8
 = λ Γ A →
   (Var8 : Con8 → Ty8 → Set)
   (vz  : ∀{Γ A} → Var8 (snoc8 Γ A) A)
   (vs  : ∀{Γ B A} → Var8 Γ A → Var8 (snoc8 Γ B) A)
 → Var8 Γ A

vz8 : ∀{Γ A} → Var8 (snoc8 Γ A) A; vz8
 = λ Var8 vz8 vs → vz8

vs8 : ∀{Γ B A} → Var8 Γ A → Var8 (snoc8 Γ B) A; vs8
 = λ x Var8 vz8 vs8 → vs8 (x Var8 vz8 vs8)

Tm8 : Con8 → Ty8 → Set; Tm8
 = λ Γ A →
   (Tm8  : Con8 → Ty8 → Set)
   (var   : ∀{Γ A} → Var8 Γ A → Tm8 Γ A)
   (lam   : ∀{Γ A B} → Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B))
   (app   : ∀{Γ A B} → Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B)
   (tt    : ∀{Γ} → Tm8 Γ top8)
   (pair  : ∀{Γ A B} → Tm8 Γ A → Tm8 Γ B → Tm8 Γ (prod8 A B))
   (fst   : ∀{Γ A B} → Tm8 Γ (prod8 A B) → Tm8 Γ A)
   (snd   : ∀{Γ A B} → Tm8 Γ (prod8 A B) → Tm8 Γ B)
   (left  : ∀{Γ A B} → Tm8 Γ A → Tm8 Γ (sum8 A B))
   (right : ∀{Γ A B} → Tm8 Γ B → Tm8 Γ (sum8 A B))
   (case  : ∀{Γ A B C} → Tm8 Γ (sum8 A B) → Tm8 Γ (arr8 A C) → Tm8 Γ (arr8 B C) → Tm8 Γ C)
   (zero  : ∀{Γ} → Tm8 Γ nat8)
   (suc   : ∀{Γ} → Tm8 Γ nat8 → Tm8 Γ nat8)
   (rec   : ∀{Γ A} → Tm8 Γ nat8 → Tm8 Γ (arr8 nat8 (arr8 A A)) → Tm8 Γ A → Tm8 Γ A)
 → Tm8 Γ A

var8 : ∀{Γ A} → Var8 Γ A → Tm8 Γ A; var8
 = λ x Tm8 var8 lam app tt pair fst snd left right case zero suc rec →
     var8 x

lam8 : ∀{Γ A B} → Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B); lam8
 = λ t Tm8 var8 lam8 app tt pair fst snd left right case zero suc rec →
     lam8 (t Tm8 var8 lam8 app tt pair fst snd left right case zero suc rec)

app8 : ∀{Γ A B} → Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B; app8
 = λ t u Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec →
     app8 (t Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec)
         (u Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec)

tt8 : ∀{Γ} → Tm8 Γ top8; tt8
 = λ Tm8 var8 lam8 app8 tt8 pair fst snd left right case zero suc rec → tt8

pair8 : ∀{Γ A B} → Tm8 Γ A → Tm8 Γ B → Tm8 Γ (prod8 A B); pair8
 = λ t u Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec →
     pair8 (t Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec)
          (u Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec)

fst8 : ∀{Γ A B} → Tm8 Γ (prod8 A B) → Tm8 Γ A; fst8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd left right case zero suc rec →
     fst8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd left right case zero suc rec)

snd8 : ∀{Γ A B} → Tm8 Γ (prod8 A B) → Tm8 Γ B; snd8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left right case zero suc rec →
     snd8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left right case zero suc rec)

left8 : ∀{Γ A B} → Tm8 Γ A → Tm8 Γ (sum8 A B); left8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right case zero suc rec →
     left8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right case zero suc rec)

right8 : ∀{Γ A B} → Tm8 Γ B → Tm8 Γ (sum8 A B); right8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case zero suc rec →
     right8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case zero suc rec)

case8 : ∀{Γ A B C} → Tm8 Γ (sum8 A B) → Tm8 Γ (arr8 A C) → Tm8 Γ (arr8 B C) → Tm8 Γ C; case8
 = λ t u v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec →
     case8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)
           (u Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)
           (v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)

zero8  : ∀{Γ} → Tm8 Γ nat8; zero8
 = λ Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc rec → zero8

suc8 : ∀{Γ} → Tm8 Γ nat8 → Tm8 Γ nat8; suc8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec →
   suc8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec)

rec8 : ∀{Γ A} → Tm8 Γ nat8 → Tm8 Γ (arr8 nat8 (arr8 A A)) → Tm8 Γ A → Tm8 Γ A; rec8
 = λ t u v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8 →
     rec8 (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)
         (u Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)
         (v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)

v08 : ∀{Γ A} → Tm8 (snoc8 Γ A) A; v08
 = var8 vz8

v18 : ∀{Γ A B} → Tm8 (snoc8 (snoc8 Γ A) B) A; v18
 = var8 (vs8 vz8)

v28 : ∀{Γ A B C} → Tm8 (snoc8 (snoc8 (snoc8 Γ A) B) C) A; v28
 = var8 (vs8 (vs8 vz8))

v38 : ∀{Γ A B C D} → Tm8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) A; v38
 = var8 (vs8 (vs8 (vs8 vz8)))

tbool8 : Ty8; tbool8
 = sum8 top8 top8

true8 : ∀{Γ} → Tm8 Γ tbool8; true8
 = left8 tt8

tfalse8 : ∀{Γ} → Tm8 Γ tbool8; tfalse8
 = right8 tt8

ifthenelse8 : ∀{Γ A} → Tm8 Γ (arr8 tbool8 (arr8 A (arr8 A A))); ifthenelse8
 = lam8 (lam8 (lam8 (case8 v28 (lam8 v28) (lam8 v18))))

times48 : ∀{Γ A} → Tm8 Γ (arr8 (arr8 A A) (arr8 A A)); times48
  = lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08)))))

add8 : ∀{Γ} → Tm8 Γ (arr8 nat8 (arr8 nat8 nat8)); add8
 = lam8 (rec8 v08
       (lam8 (lam8 (lam8 (suc8 (app8 v18 v08)))))
       (lam8 v08))

mul8 : ∀{Γ} → Tm8 Γ (arr8 nat8 (arr8 nat8 nat8)); mul8
 = lam8 (rec8 v08
       (lam8 (lam8 (lam8 (app8 (app8 add8 (app8 v18 v08)) v08))))
       (lam8 zero8))

fact8 : ∀{Γ} → Tm8 Γ (arr8 nat8 nat8); fact8
 = lam8 (rec8 v08 (lam8 (lam8 (app8 (app8 mul8 (suc8 v18)) v08)))
        (suc8 zero8))
{-# OPTIONS --type-in-type #-}

Ty9 : Set
Ty9 =
   (Ty9         : Set)
   (nat top bot  : Ty9)
   (arr prod sum : Ty9 → Ty9 → Ty9)
 → Ty9

nat9 : Ty9; nat9 = λ _ nat9 _ _ _ _ _ → nat9
top9 : Ty9; top9 = λ _ _ top9 _ _ _ _ → top9
bot9 : Ty9; bot9 = λ _ _ _ bot9 _ _ _ → bot9

arr9 : Ty9 → Ty9 → Ty9; arr9
 = λ A B Ty9 nat9 top9 bot9 arr9 prod sum →
     arr9 (A Ty9 nat9 top9 bot9 arr9 prod sum) (B Ty9 nat9 top9 bot9 arr9 prod sum)

prod9 : Ty9 → Ty9 → Ty9; prod9
 = λ A B Ty9 nat9 top9 bot9 arr9 prod9 sum →
     prod9 (A Ty9 nat9 top9 bot9 arr9 prod9 sum) (B Ty9 nat9 top9 bot9 arr9 prod9 sum)

sum9 : Ty9 → Ty9 → Ty9; sum9
 = λ A B Ty9 nat9 top9 bot9 arr9 prod9 sum9 →
     sum9 (A Ty9 nat9 top9 bot9 arr9 prod9 sum9) (B Ty9 nat9 top9 bot9 arr9 prod9 sum9)

Con9 : Set; Con9
 = (Con9 : Set)
   (nil  : Con9)
   (snoc : Con9 → Ty9 → Con9)
 → Con9

nil9 : Con9; nil9
 = λ Con9 nil9 snoc → nil9

snoc9 : Con9 → Ty9 → Con9; snoc9
 = λ Γ A Con9 nil9 snoc9 → snoc9 (Γ Con9 nil9 snoc9) A

Var9 : Con9 → Ty9 → Set; Var9
 = λ Γ A →
   (Var9 : Con9 → Ty9 → Set)
   (vz  : ∀{Γ A} → Var9 (snoc9 Γ A) A)
   (vs  : ∀{Γ B A} → Var9 Γ A → Var9 (snoc9 Γ B) A)
 → Var9 Γ A

vz9 : ∀{Γ A} → Var9 (snoc9 Γ A) A; vz9
 = λ Var9 vz9 vs → vz9

vs9 : ∀{Γ B A} → Var9 Γ A → Var9 (snoc9 Γ B) A; vs9
 = λ x Var9 vz9 vs9 → vs9 (x Var9 vz9 vs9)

Tm9 : Con9 → Ty9 → Set; Tm9
 = λ Γ A →
   (Tm9  : Con9 → Ty9 → Set)
   (var   : ∀{Γ A} → Var9 Γ A → Tm9 Γ A)
   (lam   : ∀{Γ A B} → Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B))
   (app   : ∀{Γ A B} → Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B)
   (tt    : ∀{Γ} → Tm9 Γ top9)
   (pair  : ∀{Γ A B} → Tm9 Γ A → Tm9 Γ B → Tm9 Γ (prod9 A B))
   (fst   : ∀{Γ A B} → Tm9 Γ (prod9 A B) → Tm9 Γ A)
   (snd   : ∀{Γ A B} → Tm9 Γ (prod9 A B) → Tm9 Γ B)
   (left  : ∀{Γ A B} → Tm9 Γ A → Tm9 Γ (sum9 A B))
   (right : ∀{Γ A B} → Tm9 Γ B → Tm9 Γ (sum9 A B))
   (case  : ∀{Γ A B C} → Tm9 Γ (sum9 A B) → Tm9 Γ (arr9 A C) → Tm9 Γ (arr9 B C) → Tm9 Γ C)
   (zero  : ∀{Γ} → Tm9 Γ nat9)
   (suc   : ∀{Γ} → Tm9 Γ nat9 → Tm9 Γ nat9)
   (rec   : ∀{Γ A} → Tm9 Γ nat9 → Tm9 Γ (arr9 nat9 (arr9 A A)) → Tm9 Γ A → Tm9 Γ A)
 → Tm9 Γ A

var9 : ∀{Γ A} → Var9 Γ A → Tm9 Γ A; var9
 = λ x Tm9 var9 lam app tt pair fst snd left right case zero suc rec →
     var9 x

lam9 : ∀{Γ A B} → Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B); lam9
 = λ t Tm9 var9 lam9 app tt pair fst snd left right case zero suc rec →
     lam9 (t Tm9 var9 lam9 app tt pair fst snd left right case zero suc rec)

app9 : ∀{Γ A B} → Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B; app9
 = λ t u Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec →
     app9 (t Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec)
         (u Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec)

tt9 : ∀{Γ} → Tm9 Γ top9; tt9
 = λ Tm9 var9 lam9 app9 tt9 pair fst snd left right case zero suc rec → tt9

pair9 : ∀{Γ A B} → Tm9 Γ A → Tm9 Γ B → Tm9 Γ (prod9 A B); pair9
 = λ t u Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec →
     pair9 (t Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec)
          (u Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec)

fst9 : ∀{Γ A B} → Tm9 Γ (prod9 A B) → Tm9 Γ A; fst9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd left right case zero suc rec →
     fst9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd left right case zero suc rec)

snd9 : ∀{Γ A B} → Tm9 Γ (prod9 A B) → Tm9 Γ B; snd9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left right case zero suc rec →
     snd9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left right case zero suc rec)

left9 : ∀{Γ A B} → Tm9 Γ A → Tm9 Γ (sum9 A B); left9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right case zero suc rec →
     left9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right case zero suc rec)

right9 : ∀{Γ A B} → Tm9 Γ B → Tm9 Γ (sum9 A B); right9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case zero suc rec →
     right9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case zero suc rec)

case9 : ∀{Γ A B C} → Tm9 Γ (sum9 A B) → Tm9 Γ (arr9 A C) → Tm9 Γ (arr9 B C) → Tm9 Γ C; case9
 = λ t u v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec →
     case9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)
           (u Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)
           (v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)

zero9  : ∀{Γ} → Tm9 Γ nat9; zero9
 = λ Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc rec → zero9

suc9 : ∀{Γ} → Tm9 Γ nat9 → Tm9 Γ nat9; suc9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec →
   suc9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec)

rec9 : ∀{Γ A} → Tm9 Γ nat9 → Tm9 Γ (arr9 nat9 (arr9 A A)) → Tm9 Γ A → Tm9 Γ A; rec9
 = λ t u v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9 →
     rec9 (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)
         (u Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)
         (v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)

v09 : ∀{Γ A} → Tm9 (snoc9 Γ A) A; v09
 = var9 vz9

v19 : ∀{Γ A B} → Tm9 (snoc9 (snoc9 Γ A) B) A; v19
 = var9 (vs9 vz9)

v29 : ∀{Γ A B C} → Tm9 (snoc9 (snoc9 (snoc9 Γ A) B) C) A; v29
 = var9 (vs9 (vs9 vz9))

v39 : ∀{Γ A B C D} → Tm9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) A; v39
 = var9 (vs9 (vs9 (vs9 vz9)))

tbool9 : Ty9; tbool9
 = sum9 top9 top9

true9 : ∀{Γ} → Tm9 Γ tbool9; true9
 = left9 tt9

tfalse9 : ∀{Γ} → Tm9 Γ tbool9; tfalse9
 = right9 tt9

ifthenelse9 : ∀{Γ A} → Tm9 Γ (arr9 tbool9 (arr9 A (arr9 A A))); ifthenelse9
 = lam9 (lam9 (lam9 (case9 v29 (lam9 v29) (lam9 v19))))

times49 : ∀{Γ A} → Tm9 Γ (arr9 (arr9 A A) (arr9 A A)); times49
  = lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09)))))

add9 : ∀{Γ} → Tm9 Γ (arr9 nat9 (arr9 nat9 nat9)); add9
 = lam9 (rec9 v09
       (lam9 (lam9 (lam9 (suc9 (app9 v19 v09)))))
       (lam9 v09))

mul9 : ∀{Γ} → Tm9 Γ (arr9 nat9 (arr9 nat9 nat9)); mul9
 = lam9 (rec9 v09
       (lam9 (lam9 (lam9 (app9 (app9 add9 (app9 v19 v09)) v09))))
       (lam9 zero9))

fact9 : ∀{Γ} → Tm9 Γ (arr9 nat9 nat9); fact9
 = lam9 (rec9 v09 (lam9 (lam9 (app9 (app9 mul9 (suc9 v19)) v09)))
        (suc9 zero9))
{-# OPTIONS --type-in-type #-}

Ty10 : Set
Ty10 =
   (Ty10         : Set)
   (nat top bot  : Ty10)
   (arr prod sum : Ty10 → Ty10 → Ty10)
 → Ty10

nat10 : Ty10; nat10 = λ _ nat10 _ _ _ _ _ → nat10
top10 : Ty10; top10 = λ _ _ top10 _ _ _ _ → top10
bot10 : Ty10; bot10 = λ _ _ _ bot10 _ _ _ → bot10

arr10 : Ty10 → Ty10 → Ty10; arr10
 = λ A B Ty10 nat10 top10 bot10 arr10 prod sum →
     arr10 (A Ty10 nat10 top10 bot10 arr10 prod sum) (B Ty10 nat10 top10 bot10 arr10 prod sum)

prod10 : Ty10 → Ty10 → Ty10; prod10
 = λ A B Ty10 nat10 top10 bot10 arr10 prod10 sum →
     prod10 (A Ty10 nat10 top10 bot10 arr10 prod10 sum) (B Ty10 nat10 top10 bot10 arr10 prod10 sum)

sum10 : Ty10 → Ty10 → Ty10; sum10
 = λ A B Ty10 nat10 top10 bot10 arr10 prod10 sum10 →
     sum10 (A Ty10 nat10 top10 bot10 arr10 prod10 sum10) (B Ty10 nat10 top10 bot10 arr10 prod10 sum10)

Con10 : Set; Con10
 = (Con10 : Set)
   (nil  : Con10)
   (snoc : Con10 → Ty10 → Con10)
 → Con10

nil10 : Con10; nil10
 = λ Con10 nil10 snoc → nil10

snoc10 : Con10 → Ty10 → Con10; snoc10
 = λ Γ A Con10 nil10 snoc10 → snoc10 (Γ Con10 nil10 snoc10) A

Var10 : Con10 → Ty10 → Set; Var10
 = λ Γ A →
   (Var10 : Con10 → Ty10 → Set)
   (vz  : ∀{Γ A} → Var10 (snoc10 Γ A) A)
   (vs  : ∀{Γ B A} → Var10 Γ A → Var10 (snoc10 Γ B) A)
 → Var10 Γ A

vz10 : ∀{Γ A} → Var10 (snoc10 Γ A) A; vz10
 = λ Var10 vz10 vs → vz10

vs10 : ∀{Γ B A} → Var10 Γ A → Var10 (snoc10 Γ B) A; vs10
 = λ x Var10 vz10 vs10 → vs10 (x Var10 vz10 vs10)

Tm10 : Con10 → Ty10 → Set; Tm10
 = λ Γ A →
   (Tm10  : Con10 → Ty10 → Set)
   (var   : ∀{Γ A} → Var10 Γ A → Tm10 Γ A)
   (lam   : ∀{Γ A B} → Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B))
   (app   : ∀{Γ A B} → Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B)
   (tt    : ∀{Γ} → Tm10 Γ top10)
   (pair  : ∀{Γ A B} → Tm10 Γ A → Tm10 Γ B → Tm10 Γ (prod10 A B))
   (fst   : ∀{Γ A B} → Tm10 Γ (prod10 A B) → Tm10 Γ A)
   (snd   : ∀{Γ A B} → Tm10 Γ (prod10 A B) → Tm10 Γ B)
   (left  : ∀{Γ A B} → Tm10 Γ A → Tm10 Γ (sum10 A B))
   (right : ∀{Γ A B} → Tm10 Γ B → Tm10 Γ (sum10 A B))
   (case  : ∀{Γ A B C} → Tm10 Γ (sum10 A B) → Tm10 Γ (arr10 A C) → Tm10 Γ (arr10 B C) → Tm10 Γ C)
   (zero  : ∀{Γ} → Tm10 Γ nat10)
   (suc   : ∀{Γ} → Tm10 Γ nat10 → Tm10 Γ nat10)
   (rec   : ∀{Γ A} → Tm10 Γ nat10 → Tm10 Γ (arr10 nat10 (arr10 A A)) → Tm10 Γ A → Tm10 Γ A)
 → Tm10 Γ A

var10 : ∀{Γ A} → Var10 Γ A → Tm10 Γ A; var10
 = λ x Tm10 var10 lam app tt pair fst snd left right case zero suc rec →
     var10 x

lam10 : ∀{Γ A B} → Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B); lam10
 = λ t Tm10 var10 lam10 app tt pair fst snd left right case zero suc rec →
     lam10 (t Tm10 var10 lam10 app tt pair fst snd left right case zero suc rec)

app10 : ∀{Γ A B} → Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B; app10
 = λ t u Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec →
     app10 (t Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec)
         (u Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec)

tt10 : ∀{Γ} → Tm10 Γ top10; tt10
 = λ Tm10 var10 lam10 app10 tt10 pair fst snd left right case zero suc rec → tt10

pair10 : ∀{Γ A B} → Tm10 Γ A → Tm10 Γ B → Tm10 Γ (prod10 A B); pair10
 = λ t u Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec →
     pair10 (t Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec)
          (u Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec)

fst10 : ∀{Γ A B} → Tm10 Γ (prod10 A B) → Tm10 Γ A; fst10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd left right case zero suc rec →
     fst10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd left right case zero suc rec)

snd10 : ∀{Γ A B} → Tm10 Γ (prod10 A B) → Tm10 Γ B; snd10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left right case zero suc rec →
     snd10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left right case zero suc rec)

left10 : ∀{Γ A B} → Tm10 Γ A → Tm10 Γ (sum10 A B); left10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right case zero suc rec →
     left10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right case zero suc rec)

right10 : ∀{Γ A B} → Tm10 Γ B → Tm10 Γ (sum10 A B); right10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case zero suc rec →
     right10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case zero suc rec)

case10 : ∀{Γ A B C} → Tm10 Γ (sum10 A B) → Tm10 Γ (arr10 A C) → Tm10 Γ (arr10 B C) → Tm10 Γ C; case10
 = λ t u v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec →
     case10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)
           (u Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)
           (v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)

zero10  : ∀{Γ} → Tm10 Γ nat10; zero10
 = λ Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc rec → zero10

suc10 : ∀{Γ} → Tm10 Γ nat10 → Tm10 Γ nat10; suc10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec →
   suc10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec)

rec10 : ∀{Γ A} → Tm10 Γ nat10 → Tm10 Γ (arr10 nat10 (arr10 A A)) → Tm10 Γ A → Tm10 Γ A; rec10
 = λ t u v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10 →
     rec10 (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)
         (u Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)
         (v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)

v010 : ∀{Γ A} → Tm10 (snoc10 Γ A) A; v010
 = var10 vz10

v110 : ∀{Γ A B} → Tm10 (snoc10 (snoc10 Γ A) B) A; v110
 = var10 (vs10 vz10)

v210 : ∀{Γ A B C} → Tm10 (snoc10 (snoc10 (snoc10 Γ A) B) C) A; v210
 = var10 (vs10 (vs10 vz10))

v310 : ∀{Γ A B C D} → Tm10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) A; v310
 = var10 (vs10 (vs10 (vs10 vz10)))

tbool10 : Ty10; tbool10
 = sum10 top10 top10

true10 : ∀{Γ} → Tm10 Γ tbool10; true10
 = left10 tt10

tfalse10 : ∀{Γ} → Tm10 Γ tbool10; tfalse10
 = right10 tt10

ifthenelse10 : ∀{Γ A} → Tm10 Γ (arr10 tbool10 (arr10 A (arr10 A A))); ifthenelse10
 = lam10 (lam10 (lam10 (case10 v210 (lam10 v210) (lam10 v110))))

times410 : ∀{Γ A} → Tm10 Γ (arr10 (arr10 A A) (arr10 A A)); times410
  = lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010)))))

add10 : ∀{Γ} → Tm10 Γ (arr10 nat10 (arr10 nat10 nat10)); add10
 = lam10 (rec10 v010
       (lam10 (lam10 (lam10 (suc10 (app10 v110 v010)))))
       (lam10 v010))

mul10 : ∀{Γ} → Tm10 Γ (arr10 nat10 (arr10 nat10 nat10)); mul10
 = lam10 (rec10 v010
       (lam10 (lam10 (lam10 (app10 (app10 add10 (app10 v110 v010)) v010))))
       (lam10 zero10))

fact10 : ∀{Γ} → Tm10 Γ (arr10 nat10 nat10); fact10
 = lam10 (rec10 v010 (lam10 (lam10 (app10 (app10 mul10 (suc10 v110)) v010)))
        (suc10 zero10))
{-# OPTIONS --type-in-type #-}

Ty11 : Set
Ty11 =
   (Ty11         : Set)
   (nat top bot  : Ty11)
   (arr prod sum : Ty11 → Ty11 → Ty11)
 → Ty11

nat11 : Ty11; nat11 = λ _ nat11 _ _ _ _ _ → nat11
top11 : Ty11; top11 = λ _ _ top11 _ _ _ _ → top11
bot11 : Ty11; bot11 = λ _ _ _ bot11 _ _ _ → bot11

arr11 : Ty11 → Ty11 → Ty11; arr11
 = λ A B Ty11 nat11 top11 bot11 arr11 prod sum →
     arr11 (A Ty11 nat11 top11 bot11 arr11 prod sum) (B Ty11 nat11 top11 bot11 arr11 prod sum)

prod11 : Ty11 → Ty11 → Ty11; prod11
 = λ A B Ty11 nat11 top11 bot11 arr11 prod11 sum →
     prod11 (A Ty11 nat11 top11 bot11 arr11 prod11 sum) (B Ty11 nat11 top11 bot11 arr11 prod11 sum)

sum11 : Ty11 → Ty11 → Ty11; sum11
 = λ A B Ty11 nat11 top11 bot11 arr11 prod11 sum11 →
     sum11 (A Ty11 nat11 top11 bot11 arr11 prod11 sum11) (B Ty11 nat11 top11 bot11 arr11 prod11 sum11)

Con11 : Set; Con11
 = (Con11 : Set)
   (nil  : Con11)
   (snoc : Con11 → Ty11 → Con11)
 → Con11

nil11 : Con11; nil11
 = λ Con11 nil11 snoc → nil11

snoc11 : Con11 → Ty11 → Con11; snoc11
 = λ Γ A Con11 nil11 snoc11 → snoc11 (Γ Con11 nil11 snoc11) A

Var11 : Con11 → Ty11 → Set; Var11
 = λ Γ A →
   (Var11 : Con11 → Ty11 → Set)
   (vz  : ∀{Γ A} → Var11 (snoc11 Γ A) A)
   (vs  : ∀{Γ B A} → Var11 Γ A → Var11 (snoc11 Γ B) A)
 → Var11 Γ A

vz11 : ∀{Γ A} → Var11 (snoc11 Γ A) A; vz11
 = λ Var11 vz11 vs → vz11

vs11 : ∀{Γ B A} → Var11 Γ A → Var11 (snoc11 Γ B) A; vs11
 = λ x Var11 vz11 vs11 → vs11 (x Var11 vz11 vs11)

Tm11 : Con11 → Ty11 → Set; Tm11
 = λ Γ A →
   (Tm11  : Con11 → Ty11 → Set)
   (var   : ∀{Γ A} → Var11 Γ A → Tm11 Γ A)
   (lam   : ∀{Γ A B} → Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B))
   (app   : ∀{Γ A B} → Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B)
   (tt    : ∀{Γ} → Tm11 Γ top11)
   (pair  : ∀{Γ A B} → Tm11 Γ A → Tm11 Γ B → Tm11 Γ (prod11 A B))
   (fst   : ∀{Γ A B} → Tm11 Γ (prod11 A B) → Tm11 Γ A)
   (snd   : ∀{Γ A B} → Tm11 Γ (prod11 A B) → Tm11 Γ B)
   (left  : ∀{Γ A B} → Tm11 Γ A → Tm11 Γ (sum11 A B))
   (right : ∀{Γ A B} → Tm11 Γ B → Tm11 Γ (sum11 A B))
   (case  : ∀{Γ A B C} → Tm11 Γ (sum11 A B) → Tm11 Γ (arr11 A C) → Tm11 Γ (arr11 B C) → Tm11 Γ C)
   (zero  : ∀{Γ} → Tm11 Γ nat11)
   (suc   : ∀{Γ} → Tm11 Γ nat11 → Tm11 Γ nat11)
   (rec   : ∀{Γ A} → Tm11 Γ nat11 → Tm11 Γ (arr11 nat11 (arr11 A A)) → Tm11 Γ A → Tm11 Γ A)
 → Tm11 Γ A

var11 : ∀{Γ A} → Var11 Γ A → Tm11 Γ A; var11
 = λ x Tm11 var11 lam app tt pair fst snd left right case zero suc rec →
     var11 x

lam11 : ∀{Γ A B} → Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B); lam11
 = λ t Tm11 var11 lam11 app tt pair fst snd left right case zero suc rec →
     lam11 (t Tm11 var11 lam11 app tt pair fst snd left right case zero suc rec)

app11 : ∀{Γ A B} → Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B; app11
 = λ t u Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec →
     app11 (t Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec)
         (u Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec)

tt11 : ∀{Γ} → Tm11 Γ top11; tt11
 = λ Tm11 var11 lam11 app11 tt11 pair fst snd left right case zero suc rec → tt11

pair11 : ∀{Γ A B} → Tm11 Γ A → Tm11 Γ B → Tm11 Γ (prod11 A B); pair11
 = λ t u Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec →
     pair11 (t Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec)
          (u Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec)

fst11 : ∀{Γ A B} → Tm11 Γ (prod11 A B) → Tm11 Γ A; fst11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd left right case zero suc rec →
     fst11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd left right case zero suc rec)

snd11 : ∀{Γ A B} → Tm11 Γ (prod11 A B) → Tm11 Γ B; snd11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left right case zero suc rec →
     snd11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left right case zero suc rec)

left11 : ∀{Γ A B} → Tm11 Γ A → Tm11 Γ (sum11 A B); left11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right case zero suc rec →
     left11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right case zero suc rec)

right11 : ∀{Γ A B} → Tm11 Γ B → Tm11 Γ (sum11 A B); right11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case zero suc rec →
     right11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case zero suc rec)

case11 : ∀{Γ A B C} → Tm11 Γ (sum11 A B) → Tm11 Γ (arr11 A C) → Tm11 Γ (arr11 B C) → Tm11 Γ C; case11
 = λ t u v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec →
     case11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)
           (u Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)
           (v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)

zero11  : ∀{Γ} → Tm11 Γ nat11; zero11
 = λ Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc rec → zero11

suc11 : ∀{Γ} → Tm11 Γ nat11 → Tm11 Γ nat11; suc11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec →
   suc11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec)

rec11 : ∀{Γ A} → Tm11 Γ nat11 → Tm11 Γ (arr11 nat11 (arr11 A A)) → Tm11 Γ A → Tm11 Γ A; rec11
 = λ t u v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11 →
     rec11 (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)
         (u Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)
         (v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)

v011 : ∀{Γ A} → Tm11 (snoc11 Γ A) A; v011
 = var11 vz11

v111 : ∀{Γ A B} → Tm11 (snoc11 (snoc11 Γ A) B) A; v111
 = var11 (vs11 vz11)

v211 : ∀{Γ A B C} → Tm11 (snoc11 (snoc11 (snoc11 Γ A) B) C) A; v211
 = var11 (vs11 (vs11 vz11))

v311 : ∀{Γ A B C D} → Tm11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) A; v311
 = var11 (vs11 (vs11 (vs11 vz11)))

tbool11 : Ty11; tbool11
 = sum11 top11 top11

true11 : ∀{Γ} → Tm11 Γ tbool11; true11
 = left11 tt11

tfalse11 : ∀{Γ} → Tm11 Γ tbool11; tfalse11
 = right11 tt11

ifthenelse11 : ∀{Γ A} → Tm11 Γ (arr11 tbool11 (arr11 A (arr11 A A))); ifthenelse11
 = lam11 (lam11 (lam11 (case11 v211 (lam11 v211) (lam11 v111))))

times411 : ∀{Γ A} → Tm11 Γ (arr11 (arr11 A A) (arr11 A A)); times411
  = lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011)))))

add11 : ∀{Γ} → Tm11 Γ (arr11 nat11 (arr11 nat11 nat11)); add11
 = lam11 (rec11 v011
       (lam11 (lam11 (lam11 (suc11 (app11 v111 v011)))))
       (lam11 v011))

mul11 : ∀{Γ} → Tm11 Γ (arr11 nat11 (arr11 nat11 nat11)); mul11
 = lam11 (rec11 v011
       (lam11 (lam11 (lam11 (app11 (app11 add11 (app11 v111 v011)) v011))))
       (lam11 zero11))

fact11 : ∀{Γ} → Tm11 Γ (arr11 nat11 nat11); fact11
 = lam11 (rec11 v011 (lam11 (lam11 (app11 (app11 mul11 (suc11 v111)) v011)))
        (suc11 zero11))
{-# OPTIONS --type-in-type #-}

Ty12 : Set
Ty12 =
   (Ty12         : Set)
   (nat top bot  : Ty12)
   (arr prod sum : Ty12 → Ty12 → Ty12)
 → Ty12

nat12 : Ty12; nat12 = λ _ nat12 _ _ _ _ _ → nat12
top12 : Ty12; top12 = λ _ _ top12 _ _ _ _ → top12
bot12 : Ty12; bot12 = λ _ _ _ bot12 _ _ _ → bot12

arr12 : Ty12 → Ty12 → Ty12; arr12
 = λ A B Ty12 nat12 top12 bot12 arr12 prod sum →
     arr12 (A Ty12 nat12 top12 bot12 arr12 prod sum) (B Ty12 nat12 top12 bot12 arr12 prod sum)

prod12 : Ty12 → Ty12 → Ty12; prod12
 = λ A B Ty12 nat12 top12 bot12 arr12 prod12 sum →
     prod12 (A Ty12 nat12 top12 bot12 arr12 prod12 sum) (B Ty12 nat12 top12 bot12 arr12 prod12 sum)

sum12 : Ty12 → Ty12 → Ty12; sum12
 = λ A B Ty12 nat12 top12 bot12 arr12 prod12 sum12 →
     sum12 (A Ty12 nat12 top12 bot12 arr12 prod12 sum12) (B Ty12 nat12 top12 bot12 arr12 prod12 sum12)

Con12 : Set; Con12
 = (Con12 : Set)
   (nil  : Con12)
   (snoc : Con12 → Ty12 → Con12)
 → Con12

nil12 : Con12; nil12
 = λ Con12 nil12 snoc → nil12

snoc12 : Con12 → Ty12 → Con12; snoc12
 = λ Γ A Con12 nil12 snoc12 → snoc12 (Γ Con12 nil12 snoc12) A

Var12 : Con12 → Ty12 → Set; Var12
 = λ Γ A →
   (Var12 : Con12 → Ty12 → Set)
   (vz  : ∀{Γ A} → Var12 (snoc12 Γ A) A)
   (vs  : ∀{Γ B A} → Var12 Γ A → Var12 (snoc12 Γ B) A)
 → Var12 Γ A

vz12 : ∀{Γ A} → Var12 (snoc12 Γ A) A; vz12
 = λ Var12 vz12 vs → vz12

vs12 : ∀{Γ B A} → Var12 Γ A → Var12 (snoc12 Γ B) A; vs12
 = λ x Var12 vz12 vs12 → vs12 (x Var12 vz12 vs12)

Tm12 : Con12 → Ty12 → Set; Tm12
 = λ Γ A →
   (Tm12  : Con12 → Ty12 → Set)
   (var   : ∀{Γ A} → Var12 Γ A → Tm12 Γ A)
   (lam   : ∀{Γ A B} → Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B))
   (app   : ∀{Γ A B} → Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B)
   (tt    : ∀{Γ} → Tm12 Γ top12)
   (pair  : ∀{Γ A B} → Tm12 Γ A → Tm12 Γ B → Tm12 Γ (prod12 A B))
   (fst   : ∀{Γ A B} → Tm12 Γ (prod12 A B) → Tm12 Γ A)
   (snd   : ∀{Γ A B} → Tm12 Γ (prod12 A B) → Tm12 Γ B)
   (left  : ∀{Γ A B} → Tm12 Γ A → Tm12 Γ (sum12 A B))
   (right : ∀{Γ A B} → Tm12 Γ B → Tm12 Γ (sum12 A B))
   (case  : ∀{Γ A B C} → Tm12 Γ (sum12 A B) → Tm12 Γ (arr12 A C) → Tm12 Γ (arr12 B C) → Tm12 Γ C)
   (zero  : ∀{Γ} → Tm12 Γ nat12)
   (suc   : ∀{Γ} → Tm12 Γ nat12 → Tm12 Γ nat12)
   (rec   : ∀{Γ A} → Tm12 Γ nat12 → Tm12 Γ (arr12 nat12 (arr12 A A)) → Tm12 Γ A → Tm12 Γ A)
 → Tm12 Γ A

var12 : ∀{Γ A} → Var12 Γ A → Tm12 Γ A; var12
 = λ x Tm12 var12 lam app tt pair fst snd left right case zero suc rec →
     var12 x

lam12 : ∀{Γ A B} → Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B); lam12
 = λ t Tm12 var12 lam12 app tt pair fst snd left right case zero suc rec →
     lam12 (t Tm12 var12 lam12 app tt pair fst snd left right case zero suc rec)

app12 : ∀{Γ A B} → Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B; app12
 = λ t u Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec →
     app12 (t Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec)
         (u Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec)

tt12 : ∀{Γ} → Tm12 Γ top12; tt12
 = λ Tm12 var12 lam12 app12 tt12 pair fst snd left right case zero suc rec → tt12

pair12 : ∀{Γ A B} → Tm12 Γ A → Tm12 Γ B → Tm12 Γ (prod12 A B); pair12
 = λ t u Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec →
     pair12 (t Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec)
          (u Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec)

fst12 : ∀{Γ A B} → Tm12 Γ (prod12 A B) → Tm12 Γ A; fst12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd left right case zero suc rec →
     fst12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd left right case zero suc rec)

snd12 : ∀{Γ A B} → Tm12 Γ (prod12 A B) → Tm12 Γ B; snd12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left right case zero suc rec →
     snd12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left right case zero suc rec)

left12 : ∀{Γ A B} → Tm12 Γ A → Tm12 Γ (sum12 A B); left12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right case zero suc rec →
     left12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right case zero suc rec)

right12 : ∀{Γ A B} → Tm12 Γ B → Tm12 Γ (sum12 A B); right12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case zero suc rec →
     right12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case zero suc rec)

case12 : ∀{Γ A B C} → Tm12 Γ (sum12 A B) → Tm12 Γ (arr12 A C) → Tm12 Γ (arr12 B C) → Tm12 Γ C; case12
 = λ t u v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec →
     case12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)
           (u Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)
           (v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)

zero12  : ∀{Γ} → Tm12 Γ nat12; zero12
 = λ Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc rec → zero12

suc12 : ∀{Γ} → Tm12 Γ nat12 → Tm12 Γ nat12; suc12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec →
   suc12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec)

rec12 : ∀{Γ A} → Tm12 Γ nat12 → Tm12 Γ (arr12 nat12 (arr12 A A)) → Tm12 Γ A → Tm12 Γ A; rec12
 = λ t u v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12 →
     rec12 (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)
         (u Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)
         (v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)

v012 : ∀{Γ A} → Tm12 (snoc12 Γ A) A; v012
 = var12 vz12

v112 : ∀{Γ A B} → Tm12 (snoc12 (snoc12 Γ A) B) A; v112
 = var12 (vs12 vz12)

v212 : ∀{Γ A B C} → Tm12 (snoc12 (snoc12 (snoc12 Γ A) B) C) A; v212
 = var12 (vs12 (vs12 vz12))

v312 : ∀{Γ A B C D} → Tm12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) A; v312
 = var12 (vs12 (vs12 (vs12 vz12)))

tbool12 : Ty12; tbool12
 = sum12 top12 top12

true12 : ∀{Γ} → Tm12 Γ tbool12; true12
 = left12 tt12

tfalse12 : ∀{Γ} → Tm12 Γ tbool12; tfalse12
 = right12 tt12

ifthenelse12 : ∀{Γ A} → Tm12 Γ (arr12 tbool12 (arr12 A (arr12 A A))); ifthenelse12
 = lam12 (lam12 (lam12 (case12 v212 (lam12 v212) (lam12 v112))))

times412 : ∀{Γ A} → Tm12 Γ (arr12 (arr12 A A) (arr12 A A)); times412
  = lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012)))))

add12 : ∀{Γ} → Tm12 Γ (arr12 nat12 (arr12 nat12 nat12)); add12
 = lam12 (rec12 v012
       (lam12 (lam12 (lam12 (suc12 (app12 v112 v012)))))
       (lam12 v012))

mul12 : ∀{Γ} → Tm12 Γ (arr12 nat12 (arr12 nat12 nat12)); mul12
 = lam12 (rec12 v012
       (lam12 (lam12 (lam12 (app12 (app12 add12 (app12 v112 v012)) v012))))
       (lam12 zero12))

fact12 : ∀{Γ} → Tm12 Γ (arr12 nat12 nat12); fact12
 = lam12 (rec12 v012 (lam12 (lam12 (app12 (app12 mul12 (suc12 v112)) v012)))
        (suc12 zero12))
{-# OPTIONS --type-in-type #-}

Ty13 : Set
Ty13 =
   (Ty13         : Set)
   (nat top bot  : Ty13)
   (arr prod sum : Ty13 → Ty13 → Ty13)
 → Ty13

nat13 : Ty13; nat13 = λ _ nat13 _ _ _ _ _ → nat13
top13 : Ty13; top13 = λ _ _ top13 _ _ _ _ → top13
bot13 : Ty13; bot13 = λ _ _ _ bot13 _ _ _ → bot13

arr13 : Ty13 → Ty13 → Ty13; arr13
 = λ A B Ty13 nat13 top13 bot13 arr13 prod sum →
     arr13 (A Ty13 nat13 top13 bot13 arr13 prod sum) (B Ty13 nat13 top13 bot13 arr13 prod sum)

prod13 : Ty13 → Ty13 → Ty13; prod13
 = λ A B Ty13 nat13 top13 bot13 arr13 prod13 sum →
     prod13 (A Ty13 nat13 top13 bot13 arr13 prod13 sum) (B Ty13 nat13 top13 bot13 arr13 prod13 sum)

sum13 : Ty13 → Ty13 → Ty13; sum13
 = λ A B Ty13 nat13 top13 bot13 arr13 prod13 sum13 →
     sum13 (A Ty13 nat13 top13 bot13 arr13 prod13 sum13) (B Ty13 nat13 top13 bot13 arr13 prod13 sum13)

Con13 : Set; Con13
 = (Con13 : Set)
   (nil  : Con13)
   (snoc : Con13 → Ty13 → Con13)
 → Con13

nil13 : Con13; nil13
 = λ Con13 nil13 snoc → nil13

snoc13 : Con13 → Ty13 → Con13; snoc13
 = λ Γ A Con13 nil13 snoc13 → snoc13 (Γ Con13 nil13 snoc13) A

Var13 : Con13 → Ty13 → Set; Var13
 = λ Γ A →
   (Var13 : Con13 → Ty13 → Set)
   (vz  : ∀{Γ A} → Var13 (snoc13 Γ A) A)
   (vs  : ∀{Γ B A} → Var13 Γ A → Var13 (snoc13 Γ B) A)
 → Var13 Γ A

vz13 : ∀{Γ A} → Var13 (snoc13 Γ A) A; vz13
 = λ Var13 vz13 vs → vz13

vs13 : ∀{Γ B A} → Var13 Γ A → Var13 (snoc13 Γ B) A; vs13
 = λ x Var13 vz13 vs13 → vs13 (x Var13 vz13 vs13)

Tm13 : Con13 → Ty13 → Set; Tm13
 = λ Γ A →
   (Tm13  : Con13 → Ty13 → Set)
   (var   : ∀{Γ A} → Var13 Γ A → Tm13 Γ A)
   (lam   : ∀{Γ A B} → Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B))
   (app   : ∀{Γ A B} → Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B)
   (tt    : ∀{Γ} → Tm13 Γ top13)
   (pair  : ∀{Γ A B} → Tm13 Γ A → Tm13 Γ B → Tm13 Γ (prod13 A B))
   (fst   : ∀{Γ A B} → Tm13 Γ (prod13 A B) → Tm13 Γ A)
   (snd   : ∀{Γ A B} → Tm13 Γ (prod13 A B) → Tm13 Γ B)
   (left  : ∀{Γ A B} → Tm13 Γ A → Tm13 Γ (sum13 A B))
   (right : ∀{Γ A B} → Tm13 Γ B → Tm13 Γ (sum13 A B))
   (case  : ∀{Γ A B C} → Tm13 Γ (sum13 A B) → Tm13 Γ (arr13 A C) → Tm13 Γ (arr13 B C) → Tm13 Γ C)
   (zero  : ∀{Γ} → Tm13 Γ nat13)
   (suc   : ∀{Γ} → Tm13 Γ nat13 → Tm13 Γ nat13)
   (rec   : ∀{Γ A} → Tm13 Γ nat13 → Tm13 Γ (arr13 nat13 (arr13 A A)) → Tm13 Γ A → Tm13 Γ A)
 → Tm13 Γ A

var13 : ∀{Γ A} → Var13 Γ A → Tm13 Γ A; var13
 = λ x Tm13 var13 lam app tt pair fst snd left right case zero suc rec →
     var13 x

lam13 : ∀{Γ A B} → Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B); lam13
 = λ t Tm13 var13 lam13 app tt pair fst snd left right case zero suc rec →
     lam13 (t Tm13 var13 lam13 app tt pair fst snd left right case zero suc rec)

app13 : ∀{Γ A B} → Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B; app13
 = λ t u Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec →
     app13 (t Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec)
         (u Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec)

tt13 : ∀{Γ} → Tm13 Γ top13; tt13
 = λ Tm13 var13 lam13 app13 tt13 pair fst snd left right case zero suc rec → tt13

pair13 : ∀{Γ A B} → Tm13 Γ A → Tm13 Γ B → Tm13 Γ (prod13 A B); pair13
 = λ t u Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec →
     pair13 (t Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec)
          (u Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec)

fst13 : ∀{Γ A B} → Tm13 Γ (prod13 A B) → Tm13 Γ A; fst13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd left right case zero suc rec →
     fst13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd left right case zero suc rec)

snd13 : ∀{Γ A B} → Tm13 Γ (prod13 A B) → Tm13 Γ B; snd13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left right case zero suc rec →
     snd13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left right case zero suc rec)

left13 : ∀{Γ A B} → Tm13 Γ A → Tm13 Γ (sum13 A B); left13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right case zero suc rec →
     left13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right case zero suc rec)

right13 : ∀{Γ A B} → Tm13 Γ B → Tm13 Γ (sum13 A B); right13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case zero suc rec →
     right13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case zero suc rec)

case13 : ∀{Γ A B C} → Tm13 Γ (sum13 A B) → Tm13 Γ (arr13 A C) → Tm13 Γ (arr13 B C) → Tm13 Γ C; case13
 = λ t u v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec →
     case13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)
           (u Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)
           (v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)

zero13  : ∀{Γ} → Tm13 Γ nat13; zero13
 = λ Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc rec → zero13

suc13 : ∀{Γ} → Tm13 Γ nat13 → Tm13 Γ nat13; suc13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec →
   suc13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec)

rec13 : ∀{Γ A} → Tm13 Γ nat13 → Tm13 Γ (arr13 nat13 (arr13 A A)) → Tm13 Γ A → Tm13 Γ A; rec13
 = λ t u v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13 →
     rec13 (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)
         (u Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)
         (v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)

v013 : ∀{Γ A} → Tm13 (snoc13 Γ A) A; v013
 = var13 vz13

v113 : ∀{Γ A B} → Tm13 (snoc13 (snoc13 Γ A) B) A; v113
 = var13 (vs13 vz13)

v213 : ∀{Γ A B C} → Tm13 (snoc13 (snoc13 (snoc13 Γ A) B) C) A; v213
 = var13 (vs13 (vs13 vz13))

v313 : ∀{Γ A B C D} → Tm13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) A; v313
 = var13 (vs13 (vs13 (vs13 vz13)))

tbool13 : Ty13; tbool13
 = sum13 top13 top13

true13 : ∀{Γ} → Tm13 Γ tbool13; true13
 = left13 tt13

tfalse13 : ∀{Γ} → Tm13 Γ tbool13; tfalse13
 = right13 tt13

ifthenelse13 : ∀{Γ A} → Tm13 Γ (arr13 tbool13 (arr13 A (arr13 A A))); ifthenelse13
 = lam13 (lam13 (lam13 (case13 v213 (lam13 v213) (lam13 v113))))

times413 : ∀{Γ A} → Tm13 Γ (arr13 (arr13 A A) (arr13 A A)); times413
  = lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013)))))

add13 : ∀{Γ} → Tm13 Γ (arr13 nat13 (arr13 nat13 nat13)); add13
 = lam13 (rec13 v013
       (lam13 (lam13 (lam13 (suc13 (app13 v113 v013)))))
       (lam13 v013))

mul13 : ∀{Γ} → Tm13 Γ (arr13 nat13 (arr13 nat13 nat13)); mul13
 = lam13 (rec13 v013
       (lam13 (lam13 (lam13 (app13 (app13 add13 (app13 v113 v013)) v013))))
       (lam13 zero13))

fact13 : ∀{Γ} → Tm13 Γ (arr13 nat13 nat13); fact13
 = lam13 (rec13 v013 (lam13 (lam13 (app13 (app13 mul13 (suc13 v113)) v013)))
        (suc13 zero13))
{-# OPTIONS --type-in-type #-}

Ty14 : Set
Ty14 =
   (Ty14         : Set)
   (nat top bot  : Ty14)
   (arr prod sum : Ty14 → Ty14 → Ty14)
 → Ty14

nat14 : Ty14; nat14 = λ _ nat14 _ _ _ _ _ → nat14
top14 : Ty14; top14 = λ _ _ top14 _ _ _ _ → top14
bot14 : Ty14; bot14 = λ _ _ _ bot14 _ _ _ → bot14

arr14 : Ty14 → Ty14 → Ty14; arr14
 = λ A B Ty14 nat14 top14 bot14 arr14 prod sum →
     arr14 (A Ty14 nat14 top14 bot14 arr14 prod sum) (B Ty14 nat14 top14 bot14 arr14 prod sum)

prod14 : Ty14 → Ty14 → Ty14; prod14
 = λ A B Ty14 nat14 top14 bot14 arr14 prod14 sum →
     prod14 (A Ty14 nat14 top14 bot14 arr14 prod14 sum) (B Ty14 nat14 top14 bot14 arr14 prod14 sum)

sum14 : Ty14 → Ty14 → Ty14; sum14
 = λ A B Ty14 nat14 top14 bot14 arr14 prod14 sum14 →
     sum14 (A Ty14 nat14 top14 bot14 arr14 prod14 sum14) (B Ty14 nat14 top14 bot14 arr14 prod14 sum14)

Con14 : Set; Con14
 = (Con14 : Set)
   (nil  : Con14)
   (snoc : Con14 → Ty14 → Con14)
 → Con14

nil14 : Con14; nil14
 = λ Con14 nil14 snoc → nil14

snoc14 : Con14 → Ty14 → Con14; snoc14
 = λ Γ A Con14 nil14 snoc14 → snoc14 (Γ Con14 nil14 snoc14) A

Var14 : Con14 → Ty14 → Set; Var14
 = λ Γ A →
   (Var14 : Con14 → Ty14 → Set)
   (vz  : ∀{Γ A} → Var14 (snoc14 Γ A) A)
   (vs  : ∀{Γ B A} → Var14 Γ A → Var14 (snoc14 Γ B) A)
 → Var14 Γ A

vz14 : ∀{Γ A} → Var14 (snoc14 Γ A) A; vz14
 = λ Var14 vz14 vs → vz14

vs14 : ∀{Γ B A} → Var14 Γ A → Var14 (snoc14 Γ B) A; vs14
 = λ x Var14 vz14 vs14 → vs14 (x Var14 vz14 vs14)

Tm14 : Con14 → Ty14 → Set; Tm14
 = λ Γ A →
   (Tm14  : Con14 → Ty14 → Set)
   (var   : ∀{Γ A} → Var14 Γ A → Tm14 Γ A)
   (lam   : ∀{Γ A B} → Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B))
   (app   : ∀{Γ A B} → Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B)
   (tt    : ∀{Γ} → Tm14 Γ top14)
   (pair  : ∀{Γ A B} → Tm14 Γ A → Tm14 Γ B → Tm14 Γ (prod14 A B))
   (fst   : ∀{Γ A B} → Tm14 Γ (prod14 A B) → Tm14 Γ A)
   (snd   : ∀{Γ A B} → Tm14 Γ (prod14 A B) → Tm14 Γ B)
   (left  : ∀{Γ A B} → Tm14 Γ A → Tm14 Γ (sum14 A B))
   (right : ∀{Γ A B} → Tm14 Γ B → Tm14 Γ (sum14 A B))
   (case  : ∀{Γ A B C} → Tm14 Γ (sum14 A B) → Tm14 Γ (arr14 A C) → Tm14 Γ (arr14 B C) → Tm14 Γ C)
   (zero  : ∀{Γ} → Tm14 Γ nat14)
   (suc   : ∀{Γ} → Tm14 Γ nat14 → Tm14 Γ nat14)
   (rec   : ∀{Γ A} → Tm14 Γ nat14 → Tm14 Γ (arr14 nat14 (arr14 A A)) → Tm14 Γ A → Tm14 Γ A)
 → Tm14 Γ A

var14 : ∀{Γ A} → Var14 Γ A → Tm14 Γ A; var14
 = λ x Tm14 var14 lam app tt pair fst snd left right case zero suc rec →
     var14 x

lam14 : ∀{Γ A B} → Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B); lam14
 = λ t Tm14 var14 lam14 app tt pair fst snd left right case zero suc rec →
     lam14 (t Tm14 var14 lam14 app tt pair fst snd left right case zero suc rec)

app14 : ∀{Γ A B} → Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B; app14
 = λ t u Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec →
     app14 (t Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec)
         (u Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec)

tt14 : ∀{Γ} → Tm14 Γ top14; tt14
 = λ Tm14 var14 lam14 app14 tt14 pair fst snd left right case zero suc rec → tt14

pair14 : ∀{Γ A B} → Tm14 Γ A → Tm14 Γ B → Tm14 Γ (prod14 A B); pair14
 = λ t u Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec →
     pair14 (t Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec)
          (u Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec)

fst14 : ∀{Γ A B} → Tm14 Γ (prod14 A B) → Tm14 Γ A; fst14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd left right case zero suc rec →
     fst14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd left right case zero suc rec)

snd14 : ∀{Γ A B} → Tm14 Γ (prod14 A B) → Tm14 Γ B; snd14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left right case zero suc rec →
     snd14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left right case zero suc rec)

left14 : ∀{Γ A B} → Tm14 Γ A → Tm14 Γ (sum14 A B); left14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right case zero suc rec →
     left14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right case zero suc rec)

right14 : ∀{Γ A B} → Tm14 Γ B → Tm14 Γ (sum14 A B); right14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case zero suc rec →
     right14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case zero suc rec)

case14 : ∀{Γ A B C} → Tm14 Γ (sum14 A B) → Tm14 Γ (arr14 A C) → Tm14 Γ (arr14 B C) → Tm14 Γ C; case14
 = λ t u v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec →
     case14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)
           (u Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)
           (v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)

zero14  : ∀{Γ} → Tm14 Γ nat14; zero14
 = λ Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc rec → zero14

suc14 : ∀{Γ} → Tm14 Γ nat14 → Tm14 Γ nat14; suc14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec →
   suc14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec)

rec14 : ∀{Γ A} → Tm14 Γ nat14 → Tm14 Γ (arr14 nat14 (arr14 A A)) → Tm14 Γ A → Tm14 Γ A; rec14
 = λ t u v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14 →
     rec14 (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)
         (u Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)
         (v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)

v014 : ∀{Γ A} → Tm14 (snoc14 Γ A) A; v014
 = var14 vz14

v114 : ∀{Γ A B} → Tm14 (snoc14 (snoc14 Γ A) B) A; v114
 = var14 (vs14 vz14)

v214 : ∀{Γ A B C} → Tm14 (snoc14 (snoc14 (snoc14 Γ A) B) C) A; v214
 = var14 (vs14 (vs14 vz14))

v314 : ∀{Γ A B C D} → Tm14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) A; v314
 = var14 (vs14 (vs14 (vs14 vz14)))

tbool14 : Ty14; tbool14
 = sum14 top14 top14

true14 : ∀{Γ} → Tm14 Γ tbool14; true14
 = left14 tt14

tfalse14 : ∀{Γ} → Tm14 Γ tbool14; tfalse14
 = right14 tt14

ifthenelse14 : ∀{Γ A} → Tm14 Γ (arr14 tbool14 (arr14 A (arr14 A A))); ifthenelse14
 = lam14 (lam14 (lam14 (case14 v214 (lam14 v214) (lam14 v114))))

times414 : ∀{Γ A} → Tm14 Γ (arr14 (arr14 A A) (arr14 A A)); times414
  = lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014)))))

add14 : ∀{Γ} → Tm14 Γ (arr14 nat14 (arr14 nat14 nat14)); add14
 = lam14 (rec14 v014
       (lam14 (lam14 (lam14 (suc14 (app14 v114 v014)))))
       (lam14 v014))

mul14 : ∀{Γ} → Tm14 Γ (arr14 nat14 (arr14 nat14 nat14)); mul14
 = lam14 (rec14 v014
       (lam14 (lam14 (lam14 (app14 (app14 add14 (app14 v114 v014)) v014))))
       (lam14 zero14))

fact14 : ∀{Γ} → Tm14 Γ (arr14 nat14 nat14); fact14
 = lam14 (rec14 v014 (lam14 (lam14 (app14 (app14 mul14 (suc14 v114)) v014)))
        (suc14 zero14))
{-# OPTIONS --type-in-type #-}

Ty15 : Set
Ty15 =
   (Ty15         : Set)
   (nat top bot  : Ty15)
   (arr prod sum : Ty15 → Ty15 → Ty15)
 → Ty15

nat15 : Ty15; nat15 = λ _ nat15 _ _ _ _ _ → nat15
top15 : Ty15; top15 = λ _ _ top15 _ _ _ _ → top15
bot15 : Ty15; bot15 = λ _ _ _ bot15 _ _ _ → bot15

arr15 : Ty15 → Ty15 → Ty15; arr15
 = λ A B Ty15 nat15 top15 bot15 arr15 prod sum →
     arr15 (A Ty15 nat15 top15 bot15 arr15 prod sum) (B Ty15 nat15 top15 bot15 arr15 prod sum)

prod15 : Ty15 → Ty15 → Ty15; prod15
 = λ A B Ty15 nat15 top15 bot15 arr15 prod15 sum →
     prod15 (A Ty15 nat15 top15 bot15 arr15 prod15 sum) (B Ty15 nat15 top15 bot15 arr15 prod15 sum)

sum15 : Ty15 → Ty15 → Ty15; sum15
 = λ A B Ty15 nat15 top15 bot15 arr15 prod15 sum15 →
     sum15 (A Ty15 nat15 top15 bot15 arr15 prod15 sum15) (B Ty15 nat15 top15 bot15 arr15 prod15 sum15)

Con15 : Set; Con15
 = (Con15 : Set)
   (nil  : Con15)
   (snoc : Con15 → Ty15 → Con15)
 → Con15

nil15 : Con15; nil15
 = λ Con15 nil15 snoc → nil15

snoc15 : Con15 → Ty15 → Con15; snoc15
 = λ Γ A Con15 nil15 snoc15 → snoc15 (Γ Con15 nil15 snoc15) A

Var15 : Con15 → Ty15 → Set; Var15
 = λ Γ A →
   (Var15 : Con15 → Ty15 → Set)
   (vz  : ∀{Γ A} → Var15 (snoc15 Γ A) A)
   (vs  : ∀{Γ B A} → Var15 Γ A → Var15 (snoc15 Γ B) A)
 → Var15 Γ A

vz15 : ∀{Γ A} → Var15 (snoc15 Γ A) A; vz15
 = λ Var15 vz15 vs → vz15

vs15 : ∀{Γ B A} → Var15 Γ A → Var15 (snoc15 Γ B) A; vs15
 = λ x Var15 vz15 vs15 → vs15 (x Var15 vz15 vs15)

Tm15 : Con15 → Ty15 → Set; Tm15
 = λ Γ A →
   (Tm15  : Con15 → Ty15 → Set)
   (var   : ∀{Γ A} → Var15 Γ A → Tm15 Γ A)
   (lam   : ∀{Γ A B} → Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B))
   (app   : ∀{Γ A B} → Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B)
   (tt    : ∀{Γ} → Tm15 Γ top15)
   (pair  : ∀{Γ A B} → Tm15 Γ A → Tm15 Γ B → Tm15 Γ (prod15 A B))
   (fst   : ∀{Γ A B} → Tm15 Γ (prod15 A B) → Tm15 Γ A)
   (snd   : ∀{Γ A B} → Tm15 Γ (prod15 A B) → Tm15 Γ B)
   (left  : ∀{Γ A B} → Tm15 Γ A → Tm15 Γ (sum15 A B))
   (right : ∀{Γ A B} → Tm15 Γ B → Tm15 Γ (sum15 A B))
   (case  : ∀{Γ A B C} → Tm15 Γ (sum15 A B) → Tm15 Γ (arr15 A C) → Tm15 Γ (arr15 B C) → Tm15 Γ C)
   (zero  : ∀{Γ} → Tm15 Γ nat15)
   (suc   : ∀{Γ} → Tm15 Γ nat15 → Tm15 Γ nat15)
   (rec   : ∀{Γ A} → Tm15 Γ nat15 → Tm15 Γ (arr15 nat15 (arr15 A A)) → Tm15 Γ A → Tm15 Γ A)
 → Tm15 Γ A

var15 : ∀{Γ A} → Var15 Γ A → Tm15 Γ A; var15
 = λ x Tm15 var15 lam app tt pair fst snd left right case zero suc rec →
     var15 x

lam15 : ∀{Γ A B} → Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B); lam15
 = λ t Tm15 var15 lam15 app tt pair fst snd left right case zero suc rec →
     lam15 (t Tm15 var15 lam15 app tt pair fst snd left right case zero suc rec)

app15 : ∀{Γ A B} → Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B; app15
 = λ t u Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec →
     app15 (t Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec)
         (u Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec)

tt15 : ∀{Γ} → Tm15 Γ top15; tt15
 = λ Tm15 var15 lam15 app15 tt15 pair fst snd left right case zero suc rec → tt15

pair15 : ∀{Γ A B} → Tm15 Γ A → Tm15 Γ B → Tm15 Γ (prod15 A B); pair15
 = λ t u Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec →
     pair15 (t Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec)
          (u Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec)

fst15 : ∀{Γ A B} → Tm15 Γ (prod15 A B) → Tm15 Γ A; fst15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd left right case zero suc rec →
     fst15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd left right case zero suc rec)

snd15 : ∀{Γ A B} → Tm15 Γ (prod15 A B) → Tm15 Γ B; snd15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left right case zero suc rec →
     snd15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left right case zero suc rec)

left15 : ∀{Γ A B} → Tm15 Γ A → Tm15 Γ (sum15 A B); left15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right case zero suc rec →
     left15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right case zero suc rec)

right15 : ∀{Γ A B} → Tm15 Γ B → Tm15 Γ (sum15 A B); right15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case zero suc rec →
     right15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case zero suc rec)

case15 : ∀{Γ A B C} → Tm15 Γ (sum15 A B) → Tm15 Γ (arr15 A C) → Tm15 Γ (arr15 B C) → Tm15 Γ C; case15
 = λ t u v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec →
     case15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)
           (u Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)
           (v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)

zero15  : ∀{Γ} → Tm15 Γ nat15; zero15
 = λ Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc rec → zero15

suc15 : ∀{Γ} → Tm15 Γ nat15 → Tm15 Γ nat15; suc15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec →
   suc15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec)

rec15 : ∀{Γ A} → Tm15 Γ nat15 → Tm15 Γ (arr15 nat15 (arr15 A A)) → Tm15 Γ A → Tm15 Γ A; rec15
 = λ t u v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15 →
     rec15 (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)
         (u Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)
         (v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)

v015 : ∀{Γ A} → Tm15 (snoc15 Γ A) A; v015
 = var15 vz15

v115 : ∀{Γ A B} → Tm15 (snoc15 (snoc15 Γ A) B) A; v115
 = var15 (vs15 vz15)

v215 : ∀{Γ A B C} → Tm15 (snoc15 (snoc15 (snoc15 Γ A) B) C) A; v215
 = var15 (vs15 (vs15 vz15))

v315 : ∀{Γ A B C D} → Tm15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) A; v315
 = var15 (vs15 (vs15 (vs15 vz15)))

tbool15 : Ty15; tbool15
 = sum15 top15 top15

true15 : ∀{Γ} → Tm15 Γ tbool15; true15
 = left15 tt15

tfalse15 : ∀{Γ} → Tm15 Γ tbool15; tfalse15
 = right15 tt15

ifthenelse15 : ∀{Γ A} → Tm15 Γ (arr15 tbool15 (arr15 A (arr15 A A))); ifthenelse15
 = lam15 (lam15 (lam15 (case15 v215 (lam15 v215) (lam15 v115))))

times415 : ∀{Γ A} → Tm15 Γ (arr15 (arr15 A A) (arr15 A A)); times415
  = lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015)))))

add15 : ∀{Γ} → Tm15 Γ (arr15 nat15 (arr15 nat15 nat15)); add15
 = lam15 (rec15 v015
       (lam15 (lam15 (lam15 (suc15 (app15 v115 v015)))))
       (lam15 v015))

mul15 : ∀{Γ} → Tm15 Γ (arr15 nat15 (arr15 nat15 nat15)); mul15
 = lam15 (rec15 v015
       (lam15 (lam15 (lam15 (app15 (app15 add15 (app15 v115 v015)) v015))))
       (lam15 zero15))

fact15 : ∀{Γ} → Tm15 Γ (arr15 nat15 nat15); fact15
 = lam15 (rec15 v015 (lam15 (lam15 (app15 (app15 mul15 (suc15 v115)) v015)))
        (suc15 zero15))
