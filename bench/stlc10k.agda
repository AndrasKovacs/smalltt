
{-# OPTIONS --type-in-type #-}

module stlc10k where

Ty0 : Set
Ty0 =
   (Ty0         : Set)
   (nat top bot  : Ty0)
   (arr prod sum : Ty0 → Ty0 → Ty0)
 → Ty0

nat0 : Ty0; nat0 = λ _ nat0 _ _ _ _ _ → nat0
top0 : Ty0; top0 = λ _ _ top0 _ _ _ _ → top0
bot0 : Ty0; bot0 = λ _ _ _ bot0 _ _ _ → bot0

arr0 : Ty0 → Ty0 → Ty0; arr0
 = λ A B Ty0 nat0 top0 bot0 arr0 prod sum →
     arr0 (A Ty0 nat0 top0 bot0 arr0 prod sum) (B Ty0 nat0 top0 bot0 arr0 prod sum)

prod0 : Ty0 → Ty0 → Ty0; prod0
 = λ A B Ty0 nat0 top0 bot0 arr0 prod0 sum →
     prod0 (A Ty0 nat0 top0 bot0 arr0 prod0 sum) (B Ty0 nat0 top0 bot0 arr0 prod0 sum)

sum0 : Ty0 → Ty0 → Ty0; sum0
 = λ A B Ty0 nat0 top0 bot0 arr0 prod0 sum0 →
     sum0 (A Ty0 nat0 top0 bot0 arr0 prod0 sum0) (B Ty0 nat0 top0 bot0 arr0 prod0 sum0)

Con0 : Set; Con0
 = (Con0 : Set)
   (nil  : Con0)
   (snoc : Con0 → Ty0 → Con0)
 → Con0

nil0 : Con0; nil0
 = λ Con0 nil0 snoc → nil0

snoc0 : Con0 → Ty0 → Con0; snoc0
 = λ Γ A Con0 nil0 snoc0 → snoc0 (Γ Con0 nil0 snoc0) A

Var0 : Con0 → Ty0 → Set; Var0
 = λ Γ A →
   (Var0 : Con0 → Ty0 → Set)
   (vz  : ∀{Γ A} → Var0 (snoc0 Γ A) A)
   (vs  : ∀{Γ B A} → Var0 Γ A → Var0 (snoc0 Γ B) A)
 → Var0 Γ A

vz0 : ∀{Γ A} → Var0 (snoc0 Γ A) A; vz0
 = λ Var0 vz0 vs → vz0

vs0 : ∀{Γ B A} → Var0 Γ A → Var0 (snoc0 Γ B) A; vs0
 = λ x Var0 vz0 vs0 → vs0 (x Var0 vz0 vs0)

Tm0 : Con0 → Ty0 → Set; Tm0
 = λ Γ A →
   (Tm0  : Con0 → Ty0 → Set)
   (var   : ∀{Γ A} → Var0 Γ A → Tm0 Γ A)
   (lam   : ∀{Γ A B} → Tm0 (snoc0 Γ A) B → Tm0 Γ (arr0 A B))
   (app   : ∀{Γ A B} → Tm0 Γ (arr0 A B) → Tm0 Γ A → Tm0 Γ B)
   (tt    : ∀{Γ} → Tm0 Γ top0)
   (pair  : ∀{Γ A B} → Tm0 Γ A → Tm0 Γ B → Tm0 Γ (prod0 A B))
   (fst   : ∀{Γ A B} → Tm0 Γ (prod0 A B) → Tm0 Γ A)
   (snd   : ∀{Γ A B} → Tm0 Γ (prod0 A B) → Tm0 Γ B)
   (left  : ∀{Γ A B} → Tm0 Γ A → Tm0 Γ (sum0 A B))
   (right : ∀{Γ A B} → Tm0 Γ B → Tm0 Γ (sum0 A B))
   (case  : ∀{Γ A B C} → Tm0 Γ (sum0 A B) → Tm0 Γ (arr0 A C) → Tm0 Γ (arr0 B C) → Tm0 Γ C)
   (zero  : ∀{Γ} → Tm0 Γ nat0)
   (suc   : ∀{Γ} → Tm0 Γ nat0 → Tm0 Γ nat0)
   (rec   : ∀{Γ A} → Tm0 Γ nat0 → Tm0 Γ (arr0 nat0 (arr0 A A)) → Tm0 Γ A → Tm0 Γ A)
 → Tm0 Γ A

var0 : ∀{Γ A} → Var0 Γ A → Tm0 Γ A; var0
 = λ x Tm0 var0 lam app tt pair fst snd left right case zero suc rec →
     var0 x

lam0 : ∀{Γ A B} → Tm0 (snoc0 Γ A) B → Tm0 Γ (arr0 A B); lam0
 = λ t Tm0 var0 lam0 app tt pair fst snd left right case zero suc rec →
     lam0 (t Tm0 var0 lam0 app tt pair fst snd left right case zero suc rec)

app0 : ∀{Γ A B} → Tm0 Γ (arr0 A B) → Tm0 Γ A → Tm0 Γ B; app0
 = λ t u Tm0 var0 lam0 app0 tt pair fst snd left right case zero suc rec →
     app0 (t Tm0 var0 lam0 app0 tt pair fst snd left right case zero suc rec)
         (u Tm0 var0 lam0 app0 tt pair fst snd left right case zero suc rec)

tt0 : ∀{Γ} → Tm0 Γ top0; tt0
 = λ Tm0 var0 lam0 app0 tt0 pair fst snd left right case zero suc rec → tt0

pair0 : ∀{Γ A B} → Tm0 Γ A → Tm0 Γ B → Tm0 Γ (prod0 A B); pair0
 = λ t u Tm0 var0 lam0 app0 tt0 pair0 fst snd left right case zero suc rec →
     pair0 (t Tm0 var0 lam0 app0 tt0 pair0 fst snd left right case zero suc rec)
          (u Tm0 var0 lam0 app0 tt0 pair0 fst snd left right case zero suc rec)

fst0 : ∀{Γ A B} → Tm0 Γ (prod0 A B) → Tm0 Γ A; fst0
 = λ t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd left right case zero suc rec →
     fst0 (t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd left right case zero suc rec)

snd0 : ∀{Γ A B} → Tm0 Γ (prod0 A B) → Tm0 Γ B; snd0
 = λ t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left right case zero suc rec →
     snd0 (t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left right case zero suc rec)

left0 : ∀{Γ A B} → Tm0 Γ A → Tm0 Γ (sum0 A B); left0
 = λ t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right case zero suc rec →
     left0 (t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right case zero suc rec)

right0 : ∀{Γ A B} → Tm0 Γ B → Tm0 Γ (sum0 A B); right0
 = λ t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case zero suc rec →
     right0 (t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case zero suc rec)

case0 : ∀{Γ A B C} → Tm0 Γ (sum0 A B) → Tm0 Γ (arr0 A C) → Tm0 Γ (arr0 B C) → Tm0 Γ C; case0
 = λ t u v Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero suc rec →
     case0 (t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero suc rec)
           (u Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero suc rec)
           (v Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero suc rec)

zero0  : ∀{Γ} → Tm0 Γ nat0; zero0
 = λ Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero0 suc rec → zero0

suc0 : ∀{Γ} → Tm0 Γ nat0 → Tm0 Γ nat0; suc0
 = λ t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero0 suc0 rec →
   suc0 (t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero0 suc0 rec)

rec0 : ∀{Γ A} → Tm0 Γ nat0 → Tm0 Γ (arr0 nat0 (arr0 A A)) → Tm0 Γ A → Tm0 Γ A; rec0
 = λ t u v Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero0 suc0 rec0 →
     rec0 (t Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero0 suc0 rec0)
         (u Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero0 suc0 rec0)
         (v Tm0 var0 lam0 app0 tt0 pair0 fst0 snd0 left0 right0 case0 zero0 suc0 rec0)

v00 : ∀{Γ A} → Tm0 (snoc0 Γ A) A; v00
 = var0 vz0

v10 : ∀{Γ A B} → Tm0 (snoc0 (snoc0 Γ A) B) A; v10
 = var0 (vs0 vz0)

v20 : ∀{Γ A B C} → Tm0 (snoc0 (snoc0 (snoc0 Γ A) B) C) A; v20
 = var0 (vs0 (vs0 vz0))

v30 : ∀{Γ A B C D} → Tm0 (snoc0 (snoc0 (snoc0 (snoc0 Γ A) B) C) D) A; v30
 = var0 (vs0 (vs0 (vs0 vz0)))

tbool0 : Ty0; tbool0
 = sum0 top0 top0

true0 : ∀{Γ} → Tm0 Γ tbool0; true0
 = left0 tt0

tfalse0 : ∀{Γ} → Tm0 Γ tbool0; tfalse0
 = right0 tt0

ifthenelse0 : ∀{Γ A} → Tm0 Γ (arr0 tbool0 (arr0 A (arr0 A A))); ifthenelse0
 = lam0 (lam0 (lam0 (case0 v20 (lam0 v20) (lam0 v10))))

times40 : ∀{Γ A} → Tm0 Γ (arr0 (arr0 A A) (arr0 A A)); times40
  = lam0 (lam0 (app0 v10 (app0 v10 (app0 v10 (app0 v10 v00)))))

add0 : ∀{Γ} → Tm0 Γ (arr0 nat0 (arr0 nat0 nat0)); add0
 = lam0 (rec0 v00
       (lam0 (lam0 (lam0 (suc0 (app0 v10 v00)))))
       (lam0 v00))

mul0 : ∀{Γ} → Tm0 Γ (arr0 nat0 (arr0 nat0 nat0)); mul0
 = lam0 (rec0 v00
       (lam0 (lam0 (lam0 (app0 (app0 add0 (app0 v10 v00)) v00))))
       (lam0 zero0))

fact0 : ∀{Γ} → Tm0 Γ (arr0 nat0 nat0); fact0
 = lam0 (rec0 v00 (lam0 (lam0 (app0 (app0 mul0 (suc0 v10)) v00)))
        (suc0 zero0))
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
{-# OPTIONS --type-in-type #-}

Ty16 : Set
Ty16 =
   (Ty16         : Set)
   (nat top bot  : Ty16)
   (arr prod sum : Ty16 → Ty16 → Ty16)
 → Ty16

nat16 : Ty16; nat16 = λ _ nat16 _ _ _ _ _ → nat16
top16 : Ty16; top16 = λ _ _ top16 _ _ _ _ → top16
bot16 : Ty16; bot16 = λ _ _ _ bot16 _ _ _ → bot16

arr16 : Ty16 → Ty16 → Ty16; arr16
 = λ A B Ty16 nat16 top16 bot16 arr16 prod sum →
     arr16 (A Ty16 nat16 top16 bot16 arr16 prod sum) (B Ty16 nat16 top16 bot16 arr16 prod sum)

prod16 : Ty16 → Ty16 → Ty16; prod16
 = λ A B Ty16 nat16 top16 bot16 arr16 prod16 sum →
     prod16 (A Ty16 nat16 top16 bot16 arr16 prod16 sum) (B Ty16 nat16 top16 bot16 arr16 prod16 sum)

sum16 : Ty16 → Ty16 → Ty16; sum16
 = λ A B Ty16 nat16 top16 bot16 arr16 prod16 sum16 →
     sum16 (A Ty16 nat16 top16 bot16 arr16 prod16 sum16) (B Ty16 nat16 top16 bot16 arr16 prod16 sum16)

Con16 : Set; Con16
 = (Con16 : Set)
   (nil  : Con16)
   (snoc : Con16 → Ty16 → Con16)
 → Con16

nil16 : Con16; nil16
 = λ Con16 nil16 snoc → nil16

snoc16 : Con16 → Ty16 → Con16; snoc16
 = λ Γ A Con16 nil16 snoc16 → snoc16 (Γ Con16 nil16 snoc16) A

Var16 : Con16 → Ty16 → Set; Var16
 = λ Γ A →
   (Var16 : Con16 → Ty16 → Set)
   (vz  : ∀{Γ A} → Var16 (snoc16 Γ A) A)
   (vs  : ∀{Γ B A} → Var16 Γ A → Var16 (snoc16 Γ B) A)
 → Var16 Γ A

vz16 : ∀{Γ A} → Var16 (snoc16 Γ A) A; vz16
 = λ Var16 vz16 vs → vz16

vs16 : ∀{Γ B A} → Var16 Γ A → Var16 (snoc16 Γ B) A; vs16
 = λ x Var16 vz16 vs16 → vs16 (x Var16 vz16 vs16)

Tm16 : Con16 → Ty16 → Set; Tm16
 = λ Γ A →
   (Tm16  : Con16 → Ty16 → Set)
   (var   : ∀{Γ A} → Var16 Γ A → Tm16 Γ A)
   (lam   : ∀{Γ A B} → Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B))
   (app   : ∀{Γ A B} → Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B)
   (tt    : ∀{Γ} → Tm16 Γ top16)
   (pair  : ∀{Γ A B} → Tm16 Γ A → Tm16 Γ B → Tm16 Γ (prod16 A B))
   (fst   : ∀{Γ A B} → Tm16 Γ (prod16 A B) → Tm16 Γ A)
   (snd   : ∀{Γ A B} → Tm16 Γ (prod16 A B) → Tm16 Γ B)
   (left  : ∀{Γ A B} → Tm16 Γ A → Tm16 Γ (sum16 A B))
   (right : ∀{Γ A B} → Tm16 Γ B → Tm16 Γ (sum16 A B))
   (case  : ∀{Γ A B C} → Tm16 Γ (sum16 A B) → Tm16 Γ (arr16 A C) → Tm16 Γ (arr16 B C) → Tm16 Γ C)
   (zero  : ∀{Γ} → Tm16 Γ nat16)
   (suc   : ∀{Γ} → Tm16 Γ nat16 → Tm16 Γ nat16)
   (rec   : ∀{Γ A} → Tm16 Γ nat16 → Tm16 Γ (arr16 nat16 (arr16 A A)) → Tm16 Γ A → Tm16 Γ A)
 → Tm16 Γ A

var16 : ∀{Γ A} → Var16 Γ A → Tm16 Γ A; var16
 = λ x Tm16 var16 lam app tt pair fst snd left right case zero suc rec →
     var16 x

lam16 : ∀{Γ A B} → Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B); lam16
 = λ t Tm16 var16 lam16 app tt pair fst snd left right case zero suc rec →
     lam16 (t Tm16 var16 lam16 app tt pair fst snd left right case zero suc rec)

app16 : ∀{Γ A B} → Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B; app16
 = λ t u Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec →
     app16 (t Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec)
         (u Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec)

tt16 : ∀{Γ} → Tm16 Γ top16; tt16
 = λ Tm16 var16 lam16 app16 tt16 pair fst snd left right case zero suc rec → tt16

pair16 : ∀{Γ A B} → Tm16 Γ A → Tm16 Γ B → Tm16 Γ (prod16 A B); pair16
 = λ t u Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec →
     pair16 (t Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec)
          (u Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec)

fst16 : ∀{Γ A B} → Tm16 Γ (prod16 A B) → Tm16 Γ A; fst16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd left right case zero suc rec →
     fst16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd left right case zero suc rec)

snd16 : ∀{Γ A B} → Tm16 Γ (prod16 A B) → Tm16 Γ B; snd16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left right case zero suc rec →
     snd16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left right case zero suc rec)

left16 : ∀{Γ A B} → Tm16 Γ A → Tm16 Γ (sum16 A B); left16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right case zero suc rec →
     left16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right case zero suc rec)

right16 : ∀{Γ A B} → Tm16 Γ B → Tm16 Γ (sum16 A B); right16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case zero suc rec →
     right16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case zero suc rec)

case16 : ∀{Γ A B C} → Tm16 Γ (sum16 A B) → Tm16 Γ (arr16 A C) → Tm16 Γ (arr16 B C) → Tm16 Γ C; case16
 = λ t u v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec →
     case16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)
           (u Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)
           (v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)

zero16  : ∀{Γ} → Tm16 Γ nat16; zero16
 = λ Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc rec → zero16

suc16 : ∀{Γ} → Tm16 Γ nat16 → Tm16 Γ nat16; suc16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec →
   suc16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec)

rec16 : ∀{Γ A} → Tm16 Γ nat16 → Tm16 Γ (arr16 nat16 (arr16 A A)) → Tm16 Γ A → Tm16 Γ A; rec16
 = λ t u v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16 →
     rec16 (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)
         (u Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)
         (v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)

v016 : ∀{Γ A} → Tm16 (snoc16 Γ A) A; v016
 = var16 vz16

v116 : ∀{Γ A B} → Tm16 (snoc16 (snoc16 Γ A) B) A; v116
 = var16 (vs16 vz16)

v216 : ∀{Γ A B C} → Tm16 (snoc16 (snoc16 (snoc16 Γ A) B) C) A; v216
 = var16 (vs16 (vs16 vz16))

v316 : ∀{Γ A B C D} → Tm16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) A; v316
 = var16 (vs16 (vs16 (vs16 vz16)))

tbool16 : Ty16; tbool16
 = sum16 top16 top16

true16 : ∀{Γ} → Tm16 Γ tbool16; true16
 = left16 tt16

tfalse16 : ∀{Γ} → Tm16 Γ tbool16; tfalse16
 = right16 tt16

ifthenelse16 : ∀{Γ A} → Tm16 Γ (arr16 tbool16 (arr16 A (arr16 A A))); ifthenelse16
 = lam16 (lam16 (lam16 (case16 v216 (lam16 v216) (lam16 v116))))

times416 : ∀{Γ A} → Tm16 Γ (arr16 (arr16 A A) (arr16 A A)); times416
  = lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016)))))

add16 : ∀{Γ} → Tm16 Γ (arr16 nat16 (arr16 nat16 nat16)); add16
 = lam16 (rec16 v016
       (lam16 (lam16 (lam16 (suc16 (app16 v116 v016)))))
       (lam16 v016))

mul16 : ∀{Γ} → Tm16 Γ (arr16 nat16 (arr16 nat16 nat16)); mul16
 = lam16 (rec16 v016
       (lam16 (lam16 (lam16 (app16 (app16 add16 (app16 v116 v016)) v016))))
       (lam16 zero16))

fact16 : ∀{Γ} → Tm16 Γ (arr16 nat16 nat16); fact16
 = lam16 (rec16 v016 (lam16 (lam16 (app16 (app16 mul16 (suc16 v116)) v016)))
        (suc16 zero16))
{-# OPTIONS --type-in-type #-}

Ty17 : Set
Ty17 =
   (Ty17         : Set)
   (nat top bot  : Ty17)
   (arr prod sum : Ty17 → Ty17 → Ty17)
 → Ty17

nat17 : Ty17; nat17 = λ _ nat17 _ _ _ _ _ → nat17
top17 : Ty17; top17 = λ _ _ top17 _ _ _ _ → top17
bot17 : Ty17; bot17 = λ _ _ _ bot17 _ _ _ → bot17

arr17 : Ty17 → Ty17 → Ty17; arr17
 = λ A B Ty17 nat17 top17 bot17 arr17 prod sum →
     arr17 (A Ty17 nat17 top17 bot17 arr17 prod sum) (B Ty17 nat17 top17 bot17 arr17 prod sum)

prod17 : Ty17 → Ty17 → Ty17; prod17
 = λ A B Ty17 nat17 top17 bot17 arr17 prod17 sum →
     prod17 (A Ty17 nat17 top17 bot17 arr17 prod17 sum) (B Ty17 nat17 top17 bot17 arr17 prod17 sum)

sum17 : Ty17 → Ty17 → Ty17; sum17
 = λ A B Ty17 nat17 top17 bot17 arr17 prod17 sum17 →
     sum17 (A Ty17 nat17 top17 bot17 arr17 prod17 sum17) (B Ty17 nat17 top17 bot17 arr17 prod17 sum17)

Con17 : Set; Con17
 = (Con17 : Set)
   (nil  : Con17)
   (snoc : Con17 → Ty17 → Con17)
 → Con17

nil17 : Con17; nil17
 = λ Con17 nil17 snoc → nil17

snoc17 : Con17 → Ty17 → Con17; snoc17
 = λ Γ A Con17 nil17 snoc17 → snoc17 (Γ Con17 nil17 snoc17) A

Var17 : Con17 → Ty17 → Set; Var17
 = λ Γ A →
   (Var17 : Con17 → Ty17 → Set)
   (vz  : ∀{Γ A} → Var17 (snoc17 Γ A) A)
   (vs  : ∀{Γ B A} → Var17 Γ A → Var17 (snoc17 Γ B) A)
 → Var17 Γ A

vz17 : ∀{Γ A} → Var17 (snoc17 Γ A) A; vz17
 = λ Var17 vz17 vs → vz17

vs17 : ∀{Γ B A} → Var17 Γ A → Var17 (snoc17 Γ B) A; vs17
 = λ x Var17 vz17 vs17 → vs17 (x Var17 vz17 vs17)

Tm17 : Con17 → Ty17 → Set; Tm17
 = λ Γ A →
   (Tm17  : Con17 → Ty17 → Set)
   (var   : ∀{Γ A} → Var17 Γ A → Tm17 Γ A)
   (lam   : ∀{Γ A B} → Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B))
   (app   : ∀{Γ A B} → Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B)
   (tt    : ∀{Γ} → Tm17 Γ top17)
   (pair  : ∀{Γ A B} → Tm17 Γ A → Tm17 Γ B → Tm17 Γ (prod17 A B))
   (fst   : ∀{Γ A B} → Tm17 Γ (prod17 A B) → Tm17 Γ A)
   (snd   : ∀{Γ A B} → Tm17 Γ (prod17 A B) → Tm17 Γ B)
   (left  : ∀{Γ A B} → Tm17 Γ A → Tm17 Γ (sum17 A B))
   (right : ∀{Γ A B} → Tm17 Γ B → Tm17 Γ (sum17 A B))
   (case  : ∀{Γ A B C} → Tm17 Γ (sum17 A B) → Tm17 Γ (arr17 A C) → Tm17 Γ (arr17 B C) → Tm17 Γ C)
   (zero  : ∀{Γ} → Tm17 Γ nat17)
   (suc   : ∀{Γ} → Tm17 Γ nat17 → Tm17 Γ nat17)
   (rec   : ∀{Γ A} → Tm17 Γ nat17 → Tm17 Γ (arr17 nat17 (arr17 A A)) → Tm17 Γ A → Tm17 Γ A)
 → Tm17 Γ A

var17 : ∀{Γ A} → Var17 Γ A → Tm17 Γ A; var17
 = λ x Tm17 var17 lam app tt pair fst snd left right case zero suc rec →
     var17 x

lam17 : ∀{Γ A B} → Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B); lam17
 = λ t Tm17 var17 lam17 app tt pair fst snd left right case zero suc rec →
     lam17 (t Tm17 var17 lam17 app tt pair fst snd left right case zero suc rec)

app17 : ∀{Γ A B} → Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B; app17
 = λ t u Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec →
     app17 (t Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec)
         (u Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec)

tt17 : ∀{Γ} → Tm17 Γ top17; tt17
 = λ Tm17 var17 lam17 app17 tt17 pair fst snd left right case zero suc rec → tt17

pair17 : ∀{Γ A B} → Tm17 Γ A → Tm17 Γ B → Tm17 Γ (prod17 A B); pair17
 = λ t u Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec →
     pair17 (t Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec)
          (u Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec)

fst17 : ∀{Γ A B} → Tm17 Γ (prod17 A B) → Tm17 Γ A; fst17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd left right case zero suc rec →
     fst17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd left right case zero suc rec)

snd17 : ∀{Γ A B} → Tm17 Γ (prod17 A B) → Tm17 Γ B; snd17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left right case zero suc rec →
     snd17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left right case zero suc rec)

left17 : ∀{Γ A B} → Tm17 Γ A → Tm17 Γ (sum17 A B); left17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right case zero suc rec →
     left17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right case zero suc rec)

right17 : ∀{Γ A B} → Tm17 Γ B → Tm17 Γ (sum17 A B); right17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case zero suc rec →
     right17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case zero suc rec)

case17 : ∀{Γ A B C} → Tm17 Γ (sum17 A B) → Tm17 Γ (arr17 A C) → Tm17 Γ (arr17 B C) → Tm17 Γ C; case17
 = λ t u v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec →
     case17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)
           (u Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)
           (v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)

zero17  : ∀{Γ} → Tm17 Γ nat17; zero17
 = λ Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc rec → zero17

suc17 : ∀{Γ} → Tm17 Γ nat17 → Tm17 Γ nat17; suc17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec →
   suc17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec)

rec17 : ∀{Γ A} → Tm17 Γ nat17 → Tm17 Γ (arr17 nat17 (arr17 A A)) → Tm17 Γ A → Tm17 Γ A; rec17
 = λ t u v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17 →
     rec17 (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)
         (u Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)
         (v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)

v017 : ∀{Γ A} → Tm17 (snoc17 Γ A) A; v017
 = var17 vz17

v117 : ∀{Γ A B} → Tm17 (snoc17 (snoc17 Γ A) B) A; v117
 = var17 (vs17 vz17)

v217 : ∀{Γ A B C} → Tm17 (snoc17 (snoc17 (snoc17 Γ A) B) C) A; v217
 = var17 (vs17 (vs17 vz17))

v317 : ∀{Γ A B C D} → Tm17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) A; v317
 = var17 (vs17 (vs17 (vs17 vz17)))

tbool17 : Ty17; tbool17
 = sum17 top17 top17

true17 : ∀{Γ} → Tm17 Γ tbool17; true17
 = left17 tt17

tfalse17 : ∀{Γ} → Tm17 Γ tbool17; tfalse17
 = right17 tt17

ifthenelse17 : ∀{Γ A} → Tm17 Γ (arr17 tbool17 (arr17 A (arr17 A A))); ifthenelse17
 = lam17 (lam17 (lam17 (case17 v217 (lam17 v217) (lam17 v117))))

times417 : ∀{Γ A} → Tm17 Γ (arr17 (arr17 A A) (arr17 A A)); times417
  = lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017)))))

add17 : ∀{Γ} → Tm17 Γ (arr17 nat17 (arr17 nat17 nat17)); add17
 = lam17 (rec17 v017
       (lam17 (lam17 (lam17 (suc17 (app17 v117 v017)))))
       (lam17 v017))

mul17 : ∀{Γ} → Tm17 Γ (arr17 nat17 (arr17 nat17 nat17)); mul17
 = lam17 (rec17 v017
       (lam17 (lam17 (lam17 (app17 (app17 add17 (app17 v117 v017)) v017))))
       (lam17 zero17))

fact17 : ∀{Γ} → Tm17 Γ (arr17 nat17 nat17); fact17
 = lam17 (rec17 v017 (lam17 (lam17 (app17 (app17 mul17 (suc17 v117)) v017)))
        (suc17 zero17))
{-# OPTIONS --type-in-type #-}

Ty18 : Set
Ty18 =
   (Ty18         : Set)
   (nat top bot  : Ty18)
   (arr prod sum : Ty18 → Ty18 → Ty18)
 → Ty18

nat18 : Ty18; nat18 = λ _ nat18 _ _ _ _ _ → nat18
top18 : Ty18; top18 = λ _ _ top18 _ _ _ _ → top18
bot18 : Ty18; bot18 = λ _ _ _ bot18 _ _ _ → bot18

arr18 : Ty18 → Ty18 → Ty18; arr18
 = λ A B Ty18 nat18 top18 bot18 arr18 prod sum →
     arr18 (A Ty18 nat18 top18 bot18 arr18 prod sum) (B Ty18 nat18 top18 bot18 arr18 prod sum)

prod18 : Ty18 → Ty18 → Ty18; prod18
 = λ A B Ty18 nat18 top18 bot18 arr18 prod18 sum →
     prod18 (A Ty18 nat18 top18 bot18 arr18 prod18 sum) (B Ty18 nat18 top18 bot18 arr18 prod18 sum)

sum18 : Ty18 → Ty18 → Ty18; sum18
 = λ A B Ty18 nat18 top18 bot18 arr18 prod18 sum18 →
     sum18 (A Ty18 nat18 top18 bot18 arr18 prod18 sum18) (B Ty18 nat18 top18 bot18 arr18 prod18 sum18)

Con18 : Set; Con18
 = (Con18 : Set)
   (nil  : Con18)
   (snoc : Con18 → Ty18 → Con18)
 → Con18

nil18 : Con18; nil18
 = λ Con18 nil18 snoc → nil18

snoc18 : Con18 → Ty18 → Con18; snoc18
 = λ Γ A Con18 nil18 snoc18 → snoc18 (Γ Con18 nil18 snoc18) A

Var18 : Con18 → Ty18 → Set; Var18
 = λ Γ A →
   (Var18 : Con18 → Ty18 → Set)
   (vz  : ∀{Γ A} → Var18 (snoc18 Γ A) A)
   (vs  : ∀{Γ B A} → Var18 Γ A → Var18 (snoc18 Γ B) A)
 → Var18 Γ A

vz18 : ∀{Γ A} → Var18 (snoc18 Γ A) A; vz18
 = λ Var18 vz18 vs → vz18

vs18 : ∀{Γ B A} → Var18 Γ A → Var18 (snoc18 Γ B) A; vs18
 = λ x Var18 vz18 vs18 → vs18 (x Var18 vz18 vs18)

Tm18 : Con18 → Ty18 → Set; Tm18
 = λ Γ A →
   (Tm18  : Con18 → Ty18 → Set)
   (var   : ∀{Γ A} → Var18 Γ A → Tm18 Γ A)
   (lam   : ∀{Γ A B} → Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B))
   (app   : ∀{Γ A B} → Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B)
   (tt    : ∀{Γ} → Tm18 Γ top18)
   (pair  : ∀{Γ A B} → Tm18 Γ A → Tm18 Γ B → Tm18 Γ (prod18 A B))
   (fst   : ∀{Γ A B} → Tm18 Γ (prod18 A B) → Tm18 Γ A)
   (snd   : ∀{Γ A B} → Tm18 Γ (prod18 A B) → Tm18 Γ B)
   (left  : ∀{Γ A B} → Tm18 Γ A → Tm18 Γ (sum18 A B))
   (right : ∀{Γ A B} → Tm18 Γ B → Tm18 Γ (sum18 A B))
   (case  : ∀{Γ A B C} → Tm18 Γ (sum18 A B) → Tm18 Γ (arr18 A C) → Tm18 Γ (arr18 B C) → Tm18 Γ C)
   (zero  : ∀{Γ} → Tm18 Γ nat18)
   (suc   : ∀{Γ} → Tm18 Γ nat18 → Tm18 Γ nat18)
   (rec   : ∀{Γ A} → Tm18 Γ nat18 → Tm18 Γ (arr18 nat18 (arr18 A A)) → Tm18 Γ A → Tm18 Γ A)
 → Tm18 Γ A

var18 : ∀{Γ A} → Var18 Γ A → Tm18 Γ A; var18
 = λ x Tm18 var18 lam app tt pair fst snd left right case zero suc rec →
     var18 x

lam18 : ∀{Γ A B} → Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B); lam18
 = λ t Tm18 var18 lam18 app tt pair fst snd left right case zero suc rec →
     lam18 (t Tm18 var18 lam18 app tt pair fst snd left right case zero suc rec)

app18 : ∀{Γ A B} → Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B; app18
 = λ t u Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec →
     app18 (t Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec)
         (u Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec)

tt18 : ∀{Γ} → Tm18 Γ top18; tt18
 = λ Tm18 var18 lam18 app18 tt18 pair fst snd left right case zero suc rec → tt18

pair18 : ∀{Γ A B} → Tm18 Γ A → Tm18 Γ B → Tm18 Γ (prod18 A B); pair18
 = λ t u Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec →
     pair18 (t Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec)
          (u Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec)

fst18 : ∀{Γ A B} → Tm18 Γ (prod18 A B) → Tm18 Γ A; fst18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd left right case zero suc rec →
     fst18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd left right case zero suc rec)

snd18 : ∀{Γ A B} → Tm18 Γ (prod18 A B) → Tm18 Γ B; snd18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left right case zero suc rec →
     snd18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left right case zero suc rec)

left18 : ∀{Γ A B} → Tm18 Γ A → Tm18 Γ (sum18 A B); left18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right case zero suc rec →
     left18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right case zero suc rec)

right18 : ∀{Γ A B} → Tm18 Γ B → Tm18 Γ (sum18 A B); right18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case zero suc rec →
     right18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case zero suc rec)

case18 : ∀{Γ A B C} → Tm18 Γ (sum18 A B) → Tm18 Γ (arr18 A C) → Tm18 Γ (arr18 B C) → Tm18 Γ C; case18
 = λ t u v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec →
     case18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)
           (u Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)
           (v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)

zero18  : ∀{Γ} → Tm18 Γ nat18; zero18
 = λ Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc rec → zero18

suc18 : ∀{Γ} → Tm18 Γ nat18 → Tm18 Γ nat18; suc18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec →
   suc18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec)

rec18 : ∀{Γ A} → Tm18 Γ nat18 → Tm18 Γ (arr18 nat18 (arr18 A A)) → Tm18 Γ A → Tm18 Γ A; rec18
 = λ t u v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18 →
     rec18 (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)
         (u Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)
         (v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)

v018 : ∀{Γ A} → Tm18 (snoc18 Γ A) A; v018
 = var18 vz18

v118 : ∀{Γ A B} → Tm18 (snoc18 (snoc18 Γ A) B) A; v118
 = var18 (vs18 vz18)

v218 : ∀{Γ A B C} → Tm18 (snoc18 (snoc18 (snoc18 Γ A) B) C) A; v218
 = var18 (vs18 (vs18 vz18))

v318 : ∀{Γ A B C D} → Tm18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) A; v318
 = var18 (vs18 (vs18 (vs18 vz18)))

tbool18 : Ty18; tbool18
 = sum18 top18 top18

true18 : ∀{Γ} → Tm18 Γ tbool18; true18
 = left18 tt18

tfalse18 : ∀{Γ} → Tm18 Γ tbool18; tfalse18
 = right18 tt18

ifthenelse18 : ∀{Γ A} → Tm18 Γ (arr18 tbool18 (arr18 A (arr18 A A))); ifthenelse18
 = lam18 (lam18 (lam18 (case18 v218 (lam18 v218) (lam18 v118))))

times418 : ∀{Γ A} → Tm18 Γ (arr18 (arr18 A A) (arr18 A A)); times418
  = lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018)))))

add18 : ∀{Γ} → Tm18 Γ (arr18 nat18 (arr18 nat18 nat18)); add18
 = lam18 (rec18 v018
       (lam18 (lam18 (lam18 (suc18 (app18 v118 v018)))))
       (lam18 v018))

mul18 : ∀{Γ} → Tm18 Γ (arr18 nat18 (arr18 nat18 nat18)); mul18
 = lam18 (rec18 v018
       (lam18 (lam18 (lam18 (app18 (app18 add18 (app18 v118 v018)) v018))))
       (lam18 zero18))

fact18 : ∀{Γ} → Tm18 Γ (arr18 nat18 nat18); fact18
 = lam18 (rec18 v018 (lam18 (lam18 (app18 (app18 mul18 (suc18 v118)) v018)))
        (suc18 zero18))
{-# OPTIONS --type-in-type #-}

Ty19 : Set
Ty19 =
   (Ty19         : Set)
   (nat top bot  : Ty19)
   (arr prod sum : Ty19 → Ty19 → Ty19)
 → Ty19

nat19 : Ty19; nat19 = λ _ nat19 _ _ _ _ _ → nat19
top19 : Ty19; top19 = λ _ _ top19 _ _ _ _ → top19
bot19 : Ty19; bot19 = λ _ _ _ bot19 _ _ _ → bot19

arr19 : Ty19 → Ty19 → Ty19; arr19
 = λ A B Ty19 nat19 top19 bot19 arr19 prod sum →
     arr19 (A Ty19 nat19 top19 bot19 arr19 prod sum) (B Ty19 nat19 top19 bot19 arr19 prod sum)

prod19 : Ty19 → Ty19 → Ty19; prod19
 = λ A B Ty19 nat19 top19 bot19 arr19 prod19 sum →
     prod19 (A Ty19 nat19 top19 bot19 arr19 prod19 sum) (B Ty19 nat19 top19 bot19 arr19 prod19 sum)

sum19 : Ty19 → Ty19 → Ty19; sum19
 = λ A B Ty19 nat19 top19 bot19 arr19 prod19 sum19 →
     sum19 (A Ty19 nat19 top19 bot19 arr19 prod19 sum19) (B Ty19 nat19 top19 bot19 arr19 prod19 sum19)

Con19 : Set; Con19
 = (Con19 : Set)
   (nil  : Con19)
   (snoc : Con19 → Ty19 → Con19)
 → Con19

nil19 : Con19; nil19
 = λ Con19 nil19 snoc → nil19

snoc19 : Con19 → Ty19 → Con19; snoc19
 = λ Γ A Con19 nil19 snoc19 → snoc19 (Γ Con19 nil19 snoc19) A

Var19 : Con19 → Ty19 → Set; Var19
 = λ Γ A →
   (Var19 : Con19 → Ty19 → Set)
   (vz  : ∀{Γ A} → Var19 (snoc19 Γ A) A)
   (vs  : ∀{Γ B A} → Var19 Γ A → Var19 (snoc19 Γ B) A)
 → Var19 Γ A

vz19 : ∀{Γ A} → Var19 (snoc19 Γ A) A; vz19
 = λ Var19 vz19 vs → vz19

vs19 : ∀{Γ B A} → Var19 Γ A → Var19 (snoc19 Γ B) A; vs19
 = λ x Var19 vz19 vs19 → vs19 (x Var19 vz19 vs19)

Tm19 : Con19 → Ty19 → Set; Tm19
 = λ Γ A →
   (Tm19  : Con19 → Ty19 → Set)
   (var   : ∀{Γ A} → Var19 Γ A → Tm19 Γ A)
   (lam   : ∀{Γ A B} → Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B))
   (app   : ∀{Γ A B} → Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B)
   (tt    : ∀{Γ} → Tm19 Γ top19)
   (pair  : ∀{Γ A B} → Tm19 Γ A → Tm19 Γ B → Tm19 Γ (prod19 A B))
   (fst   : ∀{Γ A B} → Tm19 Γ (prod19 A B) → Tm19 Γ A)
   (snd   : ∀{Γ A B} → Tm19 Γ (prod19 A B) → Tm19 Γ B)
   (left  : ∀{Γ A B} → Tm19 Γ A → Tm19 Γ (sum19 A B))
   (right : ∀{Γ A B} → Tm19 Γ B → Tm19 Γ (sum19 A B))
   (case  : ∀{Γ A B C} → Tm19 Γ (sum19 A B) → Tm19 Γ (arr19 A C) → Tm19 Γ (arr19 B C) → Tm19 Γ C)
   (zero  : ∀{Γ} → Tm19 Γ nat19)
   (suc   : ∀{Γ} → Tm19 Γ nat19 → Tm19 Γ nat19)
   (rec   : ∀{Γ A} → Tm19 Γ nat19 → Tm19 Γ (arr19 nat19 (arr19 A A)) → Tm19 Γ A → Tm19 Γ A)
 → Tm19 Γ A

var19 : ∀{Γ A} → Var19 Γ A → Tm19 Γ A; var19
 = λ x Tm19 var19 lam app tt pair fst snd left right case zero suc rec →
     var19 x

lam19 : ∀{Γ A B} → Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B); lam19
 = λ t Tm19 var19 lam19 app tt pair fst snd left right case zero suc rec →
     lam19 (t Tm19 var19 lam19 app tt pair fst snd left right case zero suc rec)

app19 : ∀{Γ A B} → Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B; app19
 = λ t u Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec →
     app19 (t Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec)
         (u Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec)

tt19 : ∀{Γ} → Tm19 Γ top19; tt19
 = λ Tm19 var19 lam19 app19 tt19 pair fst snd left right case zero suc rec → tt19

pair19 : ∀{Γ A B} → Tm19 Γ A → Tm19 Γ B → Tm19 Γ (prod19 A B); pair19
 = λ t u Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec →
     pair19 (t Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec)
          (u Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec)

fst19 : ∀{Γ A B} → Tm19 Γ (prod19 A B) → Tm19 Γ A; fst19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd left right case zero suc rec →
     fst19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd left right case zero suc rec)

snd19 : ∀{Γ A B} → Tm19 Γ (prod19 A B) → Tm19 Γ B; snd19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left right case zero suc rec →
     snd19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left right case zero suc rec)

left19 : ∀{Γ A B} → Tm19 Γ A → Tm19 Γ (sum19 A B); left19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right case zero suc rec →
     left19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right case zero suc rec)

right19 : ∀{Γ A B} → Tm19 Γ B → Tm19 Γ (sum19 A B); right19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case zero suc rec →
     right19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case zero suc rec)

case19 : ∀{Γ A B C} → Tm19 Γ (sum19 A B) → Tm19 Γ (arr19 A C) → Tm19 Γ (arr19 B C) → Tm19 Γ C; case19
 = λ t u v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec →
     case19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)
           (u Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)
           (v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)

zero19  : ∀{Γ} → Tm19 Γ nat19; zero19
 = λ Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc rec → zero19

suc19 : ∀{Γ} → Tm19 Γ nat19 → Tm19 Γ nat19; suc19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec →
   suc19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec)

rec19 : ∀{Γ A} → Tm19 Γ nat19 → Tm19 Γ (arr19 nat19 (arr19 A A)) → Tm19 Γ A → Tm19 Γ A; rec19
 = λ t u v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19 →
     rec19 (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)
         (u Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)
         (v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)

v019 : ∀{Γ A} → Tm19 (snoc19 Γ A) A; v019
 = var19 vz19

v119 : ∀{Γ A B} → Tm19 (snoc19 (snoc19 Γ A) B) A; v119
 = var19 (vs19 vz19)

v219 : ∀{Γ A B C} → Tm19 (snoc19 (snoc19 (snoc19 Γ A) B) C) A; v219
 = var19 (vs19 (vs19 vz19))

v319 : ∀{Γ A B C D} → Tm19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) A; v319
 = var19 (vs19 (vs19 (vs19 vz19)))

tbool19 : Ty19; tbool19
 = sum19 top19 top19

true19 : ∀{Γ} → Tm19 Γ tbool19; true19
 = left19 tt19

tfalse19 : ∀{Γ} → Tm19 Γ tbool19; tfalse19
 = right19 tt19

ifthenelse19 : ∀{Γ A} → Tm19 Γ (arr19 tbool19 (arr19 A (arr19 A A))); ifthenelse19
 = lam19 (lam19 (lam19 (case19 v219 (lam19 v219) (lam19 v119))))

times419 : ∀{Γ A} → Tm19 Γ (arr19 (arr19 A A) (arr19 A A)); times419
  = lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019)))))

add19 : ∀{Γ} → Tm19 Γ (arr19 nat19 (arr19 nat19 nat19)); add19
 = lam19 (rec19 v019
       (lam19 (lam19 (lam19 (suc19 (app19 v119 v019)))))
       (lam19 v019))

mul19 : ∀{Γ} → Tm19 Γ (arr19 nat19 (arr19 nat19 nat19)); mul19
 = lam19 (rec19 v019
       (lam19 (lam19 (lam19 (app19 (app19 add19 (app19 v119 v019)) v019))))
       (lam19 zero19))

fact19 : ∀{Γ} → Tm19 Γ (arr19 nat19 nat19); fact19
 = lam19 (rec19 v019 (lam19 (lam19 (app19 (app19 mul19 (suc19 v119)) v019)))
        (suc19 zero19))
{-# OPTIONS --type-in-type #-}

Ty20 : Set
Ty20 =
   (Ty20         : Set)
   (nat top bot  : Ty20)
   (arr prod sum : Ty20 → Ty20 → Ty20)
 → Ty20

nat20 : Ty20; nat20 = λ _ nat20 _ _ _ _ _ → nat20
top20 : Ty20; top20 = λ _ _ top20 _ _ _ _ → top20
bot20 : Ty20; bot20 = λ _ _ _ bot20 _ _ _ → bot20

arr20 : Ty20 → Ty20 → Ty20; arr20
 = λ A B Ty20 nat20 top20 bot20 arr20 prod sum →
     arr20 (A Ty20 nat20 top20 bot20 arr20 prod sum) (B Ty20 nat20 top20 bot20 arr20 prod sum)

prod20 : Ty20 → Ty20 → Ty20; prod20
 = λ A B Ty20 nat20 top20 bot20 arr20 prod20 sum →
     prod20 (A Ty20 nat20 top20 bot20 arr20 prod20 sum) (B Ty20 nat20 top20 bot20 arr20 prod20 sum)

sum20 : Ty20 → Ty20 → Ty20; sum20
 = λ A B Ty20 nat20 top20 bot20 arr20 prod20 sum20 →
     sum20 (A Ty20 nat20 top20 bot20 arr20 prod20 sum20) (B Ty20 nat20 top20 bot20 arr20 prod20 sum20)

Con20 : Set; Con20
 = (Con20 : Set)
   (nil  : Con20)
   (snoc : Con20 → Ty20 → Con20)
 → Con20

nil20 : Con20; nil20
 = λ Con20 nil20 snoc → nil20

snoc20 : Con20 → Ty20 → Con20; snoc20
 = λ Γ A Con20 nil20 snoc20 → snoc20 (Γ Con20 nil20 snoc20) A

Var20 : Con20 → Ty20 → Set; Var20
 = λ Γ A →
   (Var20 : Con20 → Ty20 → Set)
   (vz  : ∀{Γ A} → Var20 (snoc20 Γ A) A)
   (vs  : ∀{Γ B A} → Var20 Γ A → Var20 (snoc20 Γ B) A)
 → Var20 Γ A

vz20 : ∀{Γ A} → Var20 (snoc20 Γ A) A; vz20
 = λ Var20 vz20 vs → vz20

vs20 : ∀{Γ B A} → Var20 Γ A → Var20 (snoc20 Γ B) A; vs20
 = λ x Var20 vz20 vs20 → vs20 (x Var20 vz20 vs20)

Tm20 : Con20 → Ty20 → Set; Tm20
 = λ Γ A →
   (Tm20  : Con20 → Ty20 → Set)
   (var   : ∀{Γ A} → Var20 Γ A → Tm20 Γ A)
   (lam   : ∀{Γ A B} → Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B))
   (app   : ∀{Γ A B} → Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B)
   (tt    : ∀{Γ} → Tm20 Γ top20)
   (pair  : ∀{Γ A B} → Tm20 Γ A → Tm20 Γ B → Tm20 Γ (prod20 A B))
   (fst   : ∀{Γ A B} → Tm20 Γ (prod20 A B) → Tm20 Γ A)
   (snd   : ∀{Γ A B} → Tm20 Γ (prod20 A B) → Tm20 Γ B)
   (left  : ∀{Γ A B} → Tm20 Γ A → Tm20 Γ (sum20 A B))
   (right : ∀{Γ A B} → Tm20 Γ B → Tm20 Γ (sum20 A B))
   (case  : ∀{Γ A B C} → Tm20 Γ (sum20 A B) → Tm20 Γ (arr20 A C) → Tm20 Γ (arr20 B C) → Tm20 Γ C)
   (zero  : ∀{Γ} → Tm20 Γ nat20)
   (suc   : ∀{Γ} → Tm20 Γ nat20 → Tm20 Γ nat20)
   (rec   : ∀{Γ A} → Tm20 Γ nat20 → Tm20 Γ (arr20 nat20 (arr20 A A)) → Tm20 Γ A → Tm20 Γ A)
 → Tm20 Γ A

var20 : ∀{Γ A} → Var20 Γ A → Tm20 Γ A; var20
 = λ x Tm20 var20 lam app tt pair fst snd left right case zero suc rec →
     var20 x

lam20 : ∀{Γ A B} → Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B); lam20
 = λ t Tm20 var20 lam20 app tt pair fst snd left right case zero suc rec →
     lam20 (t Tm20 var20 lam20 app tt pair fst snd left right case zero suc rec)

app20 : ∀{Γ A B} → Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B; app20
 = λ t u Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec →
     app20 (t Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec)
         (u Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec)

tt20 : ∀{Γ} → Tm20 Γ top20; tt20
 = λ Tm20 var20 lam20 app20 tt20 pair fst snd left right case zero suc rec → tt20

pair20 : ∀{Γ A B} → Tm20 Γ A → Tm20 Γ B → Tm20 Γ (prod20 A B); pair20
 = λ t u Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec →
     pair20 (t Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec)
          (u Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec)

fst20 : ∀{Γ A B} → Tm20 Γ (prod20 A B) → Tm20 Γ A; fst20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd left right case zero suc rec →
     fst20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd left right case zero suc rec)

snd20 : ∀{Γ A B} → Tm20 Γ (prod20 A B) → Tm20 Γ B; snd20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left right case zero suc rec →
     snd20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left right case zero suc rec)

left20 : ∀{Γ A B} → Tm20 Γ A → Tm20 Γ (sum20 A B); left20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right case zero suc rec →
     left20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right case zero suc rec)

right20 : ∀{Γ A B} → Tm20 Γ B → Tm20 Γ (sum20 A B); right20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case zero suc rec →
     right20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case zero suc rec)

case20 : ∀{Γ A B C} → Tm20 Γ (sum20 A B) → Tm20 Γ (arr20 A C) → Tm20 Γ (arr20 B C) → Tm20 Γ C; case20
 = λ t u v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec →
     case20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)
           (u Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)
           (v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)

zero20  : ∀{Γ} → Tm20 Γ nat20; zero20
 = λ Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc rec → zero20

suc20 : ∀{Γ} → Tm20 Γ nat20 → Tm20 Γ nat20; suc20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec →
   suc20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec)

rec20 : ∀{Γ A} → Tm20 Γ nat20 → Tm20 Γ (arr20 nat20 (arr20 A A)) → Tm20 Γ A → Tm20 Γ A; rec20
 = λ t u v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20 →
     rec20 (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)
         (u Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)
         (v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)

v020 : ∀{Γ A} → Tm20 (snoc20 Γ A) A; v020
 = var20 vz20

v120 : ∀{Γ A B} → Tm20 (snoc20 (snoc20 Γ A) B) A; v120
 = var20 (vs20 vz20)

v220 : ∀{Γ A B C} → Tm20 (snoc20 (snoc20 (snoc20 Γ A) B) C) A; v220
 = var20 (vs20 (vs20 vz20))

v320 : ∀{Γ A B C D} → Tm20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) A; v320
 = var20 (vs20 (vs20 (vs20 vz20)))

tbool20 : Ty20; tbool20
 = sum20 top20 top20

true20 : ∀{Γ} → Tm20 Γ tbool20; true20
 = left20 tt20

tfalse20 : ∀{Γ} → Tm20 Γ tbool20; tfalse20
 = right20 tt20

ifthenelse20 : ∀{Γ A} → Tm20 Γ (arr20 tbool20 (arr20 A (arr20 A A))); ifthenelse20
 = lam20 (lam20 (lam20 (case20 v220 (lam20 v220) (lam20 v120))))

times420 : ∀{Γ A} → Tm20 Γ (arr20 (arr20 A A) (arr20 A A)); times420
  = lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020)))))

add20 : ∀{Γ} → Tm20 Γ (arr20 nat20 (arr20 nat20 nat20)); add20
 = lam20 (rec20 v020
       (lam20 (lam20 (lam20 (suc20 (app20 v120 v020)))))
       (lam20 v020))

mul20 : ∀{Γ} → Tm20 Γ (arr20 nat20 (arr20 nat20 nat20)); mul20
 = lam20 (rec20 v020
       (lam20 (lam20 (lam20 (app20 (app20 add20 (app20 v120 v020)) v020))))
       (lam20 zero20))

fact20 : ∀{Γ} → Tm20 Γ (arr20 nat20 nat20); fact20
 = lam20 (rec20 v020 (lam20 (lam20 (app20 (app20 mul20 (suc20 v120)) v020)))
        (suc20 zero20))
{-# OPTIONS --type-in-type #-}

Ty21 : Set
Ty21 =
   (Ty21         : Set)
   (nat top bot  : Ty21)
   (arr prod sum : Ty21 → Ty21 → Ty21)
 → Ty21

nat21 : Ty21; nat21 = λ _ nat21 _ _ _ _ _ → nat21
top21 : Ty21; top21 = λ _ _ top21 _ _ _ _ → top21
bot21 : Ty21; bot21 = λ _ _ _ bot21 _ _ _ → bot21

arr21 : Ty21 → Ty21 → Ty21; arr21
 = λ A B Ty21 nat21 top21 bot21 arr21 prod sum →
     arr21 (A Ty21 nat21 top21 bot21 arr21 prod sum) (B Ty21 nat21 top21 bot21 arr21 prod sum)

prod21 : Ty21 → Ty21 → Ty21; prod21
 = λ A B Ty21 nat21 top21 bot21 arr21 prod21 sum →
     prod21 (A Ty21 nat21 top21 bot21 arr21 prod21 sum) (B Ty21 nat21 top21 bot21 arr21 prod21 sum)

sum21 : Ty21 → Ty21 → Ty21; sum21
 = λ A B Ty21 nat21 top21 bot21 arr21 prod21 sum21 →
     sum21 (A Ty21 nat21 top21 bot21 arr21 prod21 sum21) (B Ty21 nat21 top21 bot21 arr21 prod21 sum21)

Con21 : Set; Con21
 = (Con21 : Set)
   (nil  : Con21)
   (snoc : Con21 → Ty21 → Con21)
 → Con21

nil21 : Con21; nil21
 = λ Con21 nil21 snoc → nil21

snoc21 : Con21 → Ty21 → Con21; snoc21
 = λ Γ A Con21 nil21 snoc21 → snoc21 (Γ Con21 nil21 snoc21) A

Var21 : Con21 → Ty21 → Set; Var21
 = λ Γ A →
   (Var21 : Con21 → Ty21 → Set)
   (vz  : ∀{Γ A} → Var21 (snoc21 Γ A) A)
   (vs  : ∀{Γ B A} → Var21 Γ A → Var21 (snoc21 Γ B) A)
 → Var21 Γ A

vz21 : ∀{Γ A} → Var21 (snoc21 Γ A) A; vz21
 = λ Var21 vz21 vs → vz21

vs21 : ∀{Γ B A} → Var21 Γ A → Var21 (snoc21 Γ B) A; vs21
 = λ x Var21 vz21 vs21 → vs21 (x Var21 vz21 vs21)

Tm21 : Con21 → Ty21 → Set; Tm21
 = λ Γ A →
   (Tm21  : Con21 → Ty21 → Set)
   (var   : ∀{Γ A} → Var21 Γ A → Tm21 Γ A)
   (lam   : ∀{Γ A B} → Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B))
   (app   : ∀{Γ A B} → Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B)
   (tt    : ∀{Γ} → Tm21 Γ top21)
   (pair  : ∀{Γ A B} → Tm21 Γ A → Tm21 Γ B → Tm21 Γ (prod21 A B))
   (fst   : ∀{Γ A B} → Tm21 Γ (prod21 A B) → Tm21 Γ A)
   (snd   : ∀{Γ A B} → Tm21 Γ (prod21 A B) → Tm21 Γ B)
   (left  : ∀{Γ A B} → Tm21 Γ A → Tm21 Γ (sum21 A B))
   (right : ∀{Γ A B} → Tm21 Γ B → Tm21 Γ (sum21 A B))
   (case  : ∀{Γ A B C} → Tm21 Γ (sum21 A B) → Tm21 Γ (arr21 A C) → Tm21 Γ (arr21 B C) → Tm21 Γ C)
   (zero  : ∀{Γ} → Tm21 Γ nat21)
   (suc   : ∀{Γ} → Tm21 Γ nat21 → Tm21 Γ nat21)
   (rec   : ∀{Γ A} → Tm21 Γ nat21 → Tm21 Γ (arr21 nat21 (arr21 A A)) → Tm21 Γ A → Tm21 Γ A)
 → Tm21 Γ A

var21 : ∀{Γ A} → Var21 Γ A → Tm21 Γ A; var21
 = λ x Tm21 var21 lam app tt pair fst snd left right case zero suc rec →
     var21 x

lam21 : ∀{Γ A B} → Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B); lam21
 = λ t Tm21 var21 lam21 app tt pair fst snd left right case zero suc rec →
     lam21 (t Tm21 var21 lam21 app tt pair fst snd left right case zero suc rec)

app21 : ∀{Γ A B} → Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B; app21
 = λ t u Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec →
     app21 (t Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec)
         (u Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec)

tt21 : ∀{Γ} → Tm21 Γ top21; tt21
 = λ Tm21 var21 lam21 app21 tt21 pair fst snd left right case zero suc rec → tt21

pair21 : ∀{Γ A B} → Tm21 Γ A → Tm21 Γ B → Tm21 Γ (prod21 A B); pair21
 = λ t u Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec →
     pair21 (t Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec)
          (u Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec)

fst21 : ∀{Γ A B} → Tm21 Γ (prod21 A B) → Tm21 Γ A; fst21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd left right case zero suc rec →
     fst21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd left right case zero suc rec)

snd21 : ∀{Γ A B} → Tm21 Γ (prod21 A B) → Tm21 Γ B; snd21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left right case zero suc rec →
     snd21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left right case zero suc rec)

left21 : ∀{Γ A B} → Tm21 Γ A → Tm21 Γ (sum21 A B); left21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right case zero suc rec →
     left21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right case zero suc rec)

right21 : ∀{Γ A B} → Tm21 Γ B → Tm21 Γ (sum21 A B); right21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case zero suc rec →
     right21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case zero suc rec)

case21 : ∀{Γ A B C} → Tm21 Γ (sum21 A B) → Tm21 Γ (arr21 A C) → Tm21 Γ (arr21 B C) → Tm21 Γ C; case21
 = λ t u v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec →
     case21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)
           (u Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)
           (v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)

zero21  : ∀{Γ} → Tm21 Γ nat21; zero21
 = λ Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc rec → zero21

suc21 : ∀{Γ} → Tm21 Γ nat21 → Tm21 Γ nat21; suc21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec →
   suc21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec)

rec21 : ∀{Γ A} → Tm21 Γ nat21 → Tm21 Γ (arr21 nat21 (arr21 A A)) → Tm21 Γ A → Tm21 Γ A; rec21
 = λ t u v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21 →
     rec21 (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)
         (u Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)
         (v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)

v021 : ∀{Γ A} → Tm21 (snoc21 Γ A) A; v021
 = var21 vz21

v121 : ∀{Γ A B} → Tm21 (snoc21 (snoc21 Γ A) B) A; v121
 = var21 (vs21 vz21)

v221 : ∀{Γ A B C} → Tm21 (snoc21 (snoc21 (snoc21 Γ A) B) C) A; v221
 = var21 (vs21 (vs21 vz21))

v321 : ∀{Γ A B C D} → Tm21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) A; v321
 = var21 (vs21 (vs21 (vs21 vz21)))

tbool21 : Ty21; tbool21
 = sum21 top21 top21

true21 : ∀{Γ} → Tm21 Γ tbool21; true21
 = left21 tt21

tfalse21 : ∀{Γ} → Tm21 Γ tbool21; tfalse21
 = right21 tt21

ifthenelse21 : ∀{Γ A} → Tm21 Γ (arr21 tbool21 (arr21 A (arr21 A A))); ifthenelse21
 = lam21 (lam21 (lam21 (case21 v221 (lam21 v221) (lam21 v121))))

times421 : ∀{Γ A} → Tm21 Γ (arr21 (arr21 A A) (arr21 A A)); times421
  = lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021)))))

add21 : ∀{Γ} → Tm21 Γ (arr21 nat21 (arr21 nat21 nat21)); add21
 = lam21 (rec21 v021
       (lam21 (lam21 (lam21 (suc21 (app21 v121 v021)))))
       (lam21 v021))

mul21 : ∀{Γ} → Tm21 Γ (arr21 nat21 (arr21 nat21 nat21)); mul21
 = lam21 (rec21 v021
       (lam21 (lam21 (lam21 (app21 (app21 add21 (app21 v121 v021)) v021))))
       (lam21 zero21))

fact21 : ∀{Γ} → Tm21 Γ (arr21 nat21 nat21); fact21
 = lam21 (rec21 v021 (lam21 (lam21 (app21 (app21 mul21 (suc21 v121)) v021)))
        (suc21 zero21))
{-# OPTIONS --type-in-type #-}

Ty22 : Set
Ty22 =
   (Ty22         : Set)
   (nat top bot  : Ty22)
   (arr prod sum : Ty22 → Ty22 → Ty22)
 → Ty22

nat22 : Ty22; nat22 = λ _ nat22 _ _ _ _ _ → nat22
top22 : Ty22; top22 = λ _ _ top22 _ _ _ _ → top22
bot22 : Ty22; bot22 = λ _ _ _ bot22 _ _ _ → bot22

arr22 : Ty22 → Ty22 → Ty22; arr22
 = λ A B Ty22 nat22 top22 bot22 arr22 prod sum →
     arr22 (A Ty22 nat22 top22 bot22 arr22 prod sum) (B Ty22 nat22 top22 bot22 arr22 prod sum)

prod22 : Ty22 → Ty22 → Ty22; prod22
 = λ A B Ty22 nat22 top22 bot22 arr22 prod22 sum →
     prod22 (A Ty22 nat22 top22 bot22 arr22 prod22 sum) (B Ty22 nat22 top22 bot22 arr22 prod22 sum)

sum22 : Ty22 → Ty22 → Ty22; sum22
 = λ A B Ty22 nat22 top22 bot22 arr22 prod22 sum22 →
     sum22 (A Ty22 nat22 top22 bot22 arr22 prod22 sum22) (B Ty22 nat22 top22 bot22 arr22 prod22 sum22)

Con22 : Set; Con22
 = (Con22 : Set)
   (nil  : Con22)
   (snoc : Con22 → Ty22 → Con22)
 → Con22

nil22 : Con22; nil22
 = λ Con22 nil22 snoc → nil22

snoc22 : Con22 → Ty22 → Con22; snoc22
 = λ Γ A Con22 nil22 snoc22 → snoc22 (Γ Con22 nil22 snoc22) A

Var22 : Con22 → Ty22 → Set; Var22
 = λ Γ A →
   (Var22 : Con22 → Ty22 → Set)
   (vz  : ∀{Γ A} → Var22 (snoc22 Γ A) A)
   (vs  : ∀{Γ B A} → Var22 Γ A → Var22 (snoc22 Γ B) A)
 → Var22 Γ A

vz22 : ∀{Γ A} → Var22 (snoc22 Γ A) A; vz22
 = λ Var22 vz22 vs → vz22

vs22 : ∀{Γ B A} → Var22 Γ A → Var22 (snoc22 Γ B) A; vs22
 = λ x Var22 vz22 vs22 → vs22 (x Var22 vz22 vs22)

Tm22 : Con22 → Ty22 → Set; Tm22
 = λ Γ A →
   (Tm22  : Con22 → Ty22 → Set)
   (var   : ∀{Γ A} → Var22 Γ A → Tm22 Γ A)
   (lam   : ∀{Γ A B} → Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B))
   (app   : ∀{Γ A B} → Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B)
   (tt    : ∀{Γ} → Tm22 Γ top22)
   (pair  : ∀{Γ A B} → Tm22 Γ A → Tm22 Γ B → Tm22 Γ (prod22 A B))
   (fst   : ∀{Γ A B} → Tm22 Γ (prod22 A B) → Tm22 Γ A)
   (snd   : ∀{Γ A B} → Tm22 Γ (prod22 A B) → Tm22 Γ B)
   (left  : ∀{Γ A B} → Tm22 Γ A → Tm22 Γ (sum22 A B))
   (right : ∀{Γ A B} → Tm22 Γ B → Tm22 Γ (sum22 A B))
   (case  : ∀{Γ A B C} → Tm22 Γ (sum22 A B) → Tm22 Γ (arr22 A C) → Tm22 Γ (arr22 B C) → Tm22 Γ C)
   (zero  : ∀{Γ} → Tm22 Γ nat22)
   (suc   : ∀{Γ} → Tm22 Γ nat22 → Tm22 Γ nat22)
   (rec   : ∀{Γ A} → Tm22 Γ nat22 → Tm22 Γ (arr22 nat22 (arr22 A A)) → Tm22 Γ A → Tm22 Γ A)
 → Tm22 Γ A

var22 : ∀{Γ A} → Var22 Γ A → Tm22 Γ A; var22
 = λ x Tm22 var22 lam app tt pair fst snd left right case zero suc rec →
     var22 x

lam22 : ∀{Γ A B} → Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B); lam22
 = λ t Tm22 var22 lam22 app tt pair fst snd left right case zero suc rec →
     lam22 (t Tm22 var22 lam22 app tt pair fst snd left right case zero suc rec)

app22 : ∀{Γ A B} → Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B; app22
 = λ t u Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec →
     app22 (t Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec)
         (u Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec)

tt22 : ∀{Γ} → Tm22 Γ top22; tt22
 = λ Tm22 var22 lam22 app22 tt22 pair fst snd left right case zero suc rec → tt22

pair22 : ∀{Γ A B} → Tm22 Γ A → Tm22 Γ B → Tm22 Γ (prod22 A B); pair22
 = λ t u Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec →
     pair22 (t Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec)
          (u Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec)

fst22 : ∀{Γ A B} → Tm22 Γ (prod22 A B) → Tm22 Γ A; fst22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd left right case zero suc rec →
     fst22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd left right case zero suc rec)

snd22 : ∀{Γ A B} → Tm22 Γ (prod22 A B) → Tm22 Γ B; snd22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left right case zero suc rec →
     snd22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left right case zero suc rec)

left22 : ∀{Γ A B} → Tm22 Γ A → Tm22 Γ (sum22 A B); left22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right case zero suc rec →
     left22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right case zero suc rec)

right22 : ∀{Γ A B} → Tm22 Γ B → Tm22 Γ (sum22 A B); right22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case zero suc rec →
     right22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case zero suc rec)

case22 : ∀{Γ A B C} → Tm22 Γ (sum22 A B) → Tm22 Γ (arr22 A C) → Tm22 Γ (arr22 B C) → Tm22 Γ C; case22
 = λ t u v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec →
     case22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)
           (u Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)
           (v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)

zero22  : ∀{Γ} → Tm22 Γ nat22; zero22
 = λ Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc rec → zero22

suc22 : ∀{Γ} → Tm22 Γ nat22 → Tm22 Γ nat22; suc22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec →
   suc22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec)

rec22 : ∀{Γ A} → Tm22 Γ nat22 → Tm22 Γ (arr22 nat22 (arr22 A A)) → Tm22 Γ A → Tm22 Γ A; rec22
 = λ t u v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22 →
     rec22 (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)
         (u Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)
         (v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)

v022 : ∀{Γ A} → Tm22 (snoc22 Γ A) A; v022
 = var22 vz22

v122 : ∀{Γ A B} → Tm22 (snoc22 (snoc22 Γ A) B) A; v122
 = var22 (vs22 vz22)

v222 : ∀{Γ A B C} → Tm22 (snoc22 (snoc22 (snoc22 Γ A) B) C) A; v222
 = var22 (vs22 (vs22 vz22))

v322 : ∀{Γ A B C D} → Tm22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) A; v322
 = var22 (vs22 (vs22 (vs22 vz22)))

tbool22 : Ty22; tbool22
 = sum22 top22 top22

true22 : ∀{Γ} → Tm22 Γ tbool22; true22
 = left22 tt22

tfalse22 : ∀{Γ} → Tm22 Γ tbool22; tfalse22
 = right22 tt22

ifthenelse22 : ∀{Γ A} → Tm22 Γ (arr22 tbool22 (arr22 A (arr22 A A))); ifthenelse22
 = lam22 (lam22 (lam22 (case22 v222 (lam22 v222) (lam22 v122))))

times422 : ∀{Γ A} → Tm22 Γ (arr22 (arr22 A A) (arr22 A A)); times422
  = lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022)))))

add22 : ∀{Γ} → Tm22 Γ (arr22 nat22 (arr22 nat22 nat22)); add22
 = lam22 (rec22 v022
       (lam22 (lam22 (lam22 (suc22 (app22 v122 v022)))))
       (lam22 v022))

mul22 : ∀{Γ} → Tm22 Γ (arr22 nat22 (arr22 nat22 nat22)); mul22
 = lam22 (rec22 v022
       (lam22 (lam22 (lam22 (app22 (app22 add22 (app22 v122 v022)) v022))))
       (lam22 zero22))

fact22 : ∀{Γ} → Tm22 Γ (arr22 nat22 nat22); fact22
 = lam22 (rec22 v022 (lam22 (lam22 (app22 (app22 mul22 (suc22 v122)) v022)))
        (suc22 zero22))
{-# OPTIONS --type-in-type #-}

Ty23 : Set
Ty23 =
   (Ty23         : Set)
   (nat top bot  : Ty23)
   (arr prod sum : Ty23 → Ty23 → Ty23)
 → Ty23

nat23 : Ty23; nat23 = λ _ nat23 _ _ _ _ _ → nat23
top23 : Ty23; top23 = λ _ _ top23 _ _ _ _ → top23
bot23 : Ty23; bot23 = λ _ _ _ bot23 _ _ _ → bot23

arr23 : Ty23 → Ty23 → Ty23; arr23
 = λ A B Ty23 nat23 top23 bot23 arr23 prod sum →
     arr23 (A Ty23 nat23 top23 bot23 arr23 prod sum) (B Ty23 nat23 top23 bot23 arr23 prod sum)

prod23 : Ty23 → Ty23 → Ty23; prod23
 = λ A B Ty23 nat23 top23 bot23 arr23 prod23 sum →
     prod23 (A Ty23 nat23 top23 bot23 arr23 prod23 sum) (B Ty23 nat23 top23 bot23 arr23 prod23 sum)

sum23 : Ty23 → Ty23 → Ty23; sum23
 = λ A B Ty23 nat23 top23 bot23 arr23 prod23 sum23 →
     sum23 (A Ty23 nat23 top23 bot23 arr23 prod23 sum23) (B Ty23 nat23 top23 bot23 arr23 prod23 sum23)

Con23 : Set; Con23
 = (Con23 : Set)
   (nil  : Con23)
   (snoc : Con23 → Ty23 → Con23)
 → Con23

nil23 : Con23; nil23
 = λ Con23 nil23 snoc → nil23

snoc23 : Con23 → Ty23 → Con23; snoc23
 = λ Γ A Con23 nil23 snoc23 → snoc23 (Γ Con23 nil23 snoc23) A

Var23 : Con23 → Ty23 → Set; Var23
 = λ Γ A →
   (Var23 : Con23 → Ty23 → Set)
   (vz  : ∀{Γ A} → Var23 (snoc23 Γ A) A)
   (vs  : ∀{Γ B A} → Var23 Γ A → Var23 (snoc23 Γ B) A)
 → Var23 Γ A

vz23 : ∀{Γ A} → Var23 (snoc23 Γ A) A; vz23
 = λ Var23 vz23 vs → vz23

vs23 : ∀{Γ B A} → Var23 Γ A → Var23 (snoc23 Γ B) A; vs23
 = λ x Var23 vz23 vs23 → vs23 (x Var23 vz23 vs23)

Tm23 : Con23 → Ty23 → Set; Tm23
 = λ Γ A →
   (Tm23  : Con23 → Ty23 → Set)
   (var   : ∀{Γ A} → Var23 Γ A → Tm23 Γ A)
   (lam   : ∀{Γ A B} → Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B))
   (app   : ∀{Γ A B} → Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B)
   (tt    : ∀{Γ} → Tm23 Γ top23)
   (pair  : ∀{Γ A B} → Tm23 Γ A → Tm23 Γ B → Tm23 Γ (prod23 A B))
   (fst   : ∀{Γ A B} → Tm23 Γ (prod23 A B) → Tm23 Γ A)
   (snd   : ∀{Γ A B} → Tm23 Γ (prod23 A B) → Tm23 Γ B)
   (left  : ∀{Γ A B} → Tm23 Γ A → Tm23 Γ (sum23 A B))
   (right : ∀{Γ A B} → Tm23 Γ B → Tm23 Γ (sum23 A B))
   (case  : ∀{Γ A B C} → Tm23 Γ (sum23 A B) → Tm23 Γ (arr23 A C) → Tm23 Γ (arr23 B C) → Tm23 Γ C)
   (zero  : ∀{Γ} → Tm23 Γ nat23)
   (suc   : ∀{Γ} → Tm23 Γ nat23 → Tm23 Γ nat23)
   (rec   : ∀{Γ A} → Tm23 Γ nat23 → Tm23 Γ (arr23 nat23 (arr23 A A)) → Tm23 Γ A → Tm23 Γ A)
 → Tm23 Γ A

var23 : ∀{Γ A} → Var23 Γ A → Tm23 Γ A; var23
 = λ x Tm23 var23 lam app tt pair fst snd left right case zero suc rec →
     var23 x

lam23 : ∀{Γ A B} → Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B); lam23
 = λ t Tm23 var23 lam23 app tt pair fst snd left right case zero suc rec →
     lam23 (t Tm23 var23 lam23 app tt pair fst snd left right case zero suc rec)

app23 : ∀{Γ A B} → Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B; app23
 = λ t u Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec →
     app23 (t Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec)
         (u Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec)

tt23 : ∀{Γ} → Tm23 Γ top23; tt23
 = λ Tm23 var23 lam23 app23 tt23 pair fst snd left right case zero suc rec → tt23

pair23 : ∀{Γ A B} → Tm23 Γ A → Tm23 Γ B → Tm23 Γ (prod23 A B); pair23
 = λ t u Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec →
     pair23 (t Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec)
          (u Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec)

fst23 : ∀{Γ A B} → Tm23 Γ (prod23 A B) → Tm23 Γ A; fst23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd left right case zero suc rec →
     fst23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd left right case zero suc rec)

snd23 : ∀{Γ A B} → Tm23 Γ (prod23 A B) → Tm23 Γ B; snd23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left right case zero suc rec →
     snd23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left right case zero suc rec)

left23 : ∀{Γ A B} → Tm23 Γ A → Tm23 Γ (sum23 A B); left23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right case zero suc rec →
     left23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right case zero suc rec)

right23 : ∀{Γ A B} → Tm23 Γ B → Tm23 Γ (sum23 A B); right23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case zero suc rec →
     right23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case zero suc rec)

case23 : ∀{Γ A B C} → Tm23 Γ (sum23 A B) → Tm23 Γ (arr23 A C) → Tm23 Γ (arr23 B C) → Tm23 Γ C; case23
 = λ t u v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec →
     case23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)
           (u Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)
           (v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)

zero23  : ∀{Γ} → Tm23 Γ nat23; zero23
 = λ Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc rec → zero23

suc23 : ∀{Γ} → Tm23 Γ nat23 → Tm23 Γ nat23; suc23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec →
   suc23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec)

rec23 : ∀{Γ A} → Tm23 Γ nat23 → Tm23 Γ (arr23 nat23 (arr23 A A)) → Tm23 Γ A → Tm23 Γ A; rec23
 = λ t u v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23 →
     rec23 (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)
         (u Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)
         (v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)

v023 : ∀{Γ A} → Tm23 (snoc23 Γ A) A; v023
 = var23 vz23

v123 : ∀{Γ A B} → Tm23 (snoc23 (snoc23 Γ A) B) A; v123
 = var23 (vs23 vz23)

v223 : ∀{Γ A B C} → Tm23 (snoc23 (snoc23 (snoc23 Γ A) B) C) A; v223
 = var23 (vs23 (vs23 vz23))

v323 : ∀{Γ A B C D} → Tm23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) A; v323
 = var23 (vs23 (vs23 (vs23 vz23)))

tbool23 : Ty23; tbool23
 = sum23 top23 top23

true23 : ∀{Γ} → Tm23 Γ tbool23; true23
 = left23 tt23

tfalse23 : ∀{Γ} → Tm23 Γ tbool23; tfalse23
 = right23 tt23

ifthenelse23 : ∀{Γ A} → Tm23 Γ (arr23 tbool23 (arr23 A (arr23 A A))); ifthenelse23
 = lam23 (lam23 (lam23 (case23 v223 (lam23 v223) (lam23 v123))))

times423 : ∀{Γ A} → Tm23 Γ (arr23 (arr23 A A) (arr23 A A)); times423
  = lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023)))))

add23 : ∀{Γ} → Tm23 Γ (arr23 nat23 (arr23 nat23 nat23)); add23
 = lam23 (rec23 v023
       (lam23 (lam23 (lam23 (suc23 (app23 v123 v023)))))
       (lam23 v023))

mul23 : ∀{Γ} → Tm23 Γ (arr23 nat23 (arr23 nat23 nat23)); mul23
 = lam23 (rec23 v023
       (lam23 (lam23 (lam23 (app23 (app23 add23 (app23 v123 v023)) v023))))
       (lam23 zero23))

fact23 : ∀{Γ} → Tm23 Γ (arr23 nat23 nat23); fact23
 = lam23 (rec23 v023 (lam23 (lam23 (app23 (app23 mul23 (suc23 v123)) v023)))
        (suc23 zero23))
{-# OPTIONS --type-in-type #-}

Ty24 : Set
Ty24 =
   (Ty24         : Set)
   (nat top bot  : Ty24)
   (arr prod sum : Ty24 → Ty24 → Ty24)
 → Ty24

nat24 : Ty24; nat24 = λ _ nat24 _ _ _ _ _ → nat24
top24 : Ty24; top24 = λ _ _ top24 _ _ _ _ → top24
bot24 : Ty24; bot24 = λ _ _ _ bot24 _ _ _ → bot24

arr24 : Ty24 → Ty24 → Ty24; arr24
 = λ A B Ty24 nat24 top24 bot24 arr24 prod sum →
     arr24 (A Ty24 nat24 top24 bot24 arr24 prod sum) (B Ty24 nat24 top24 bot24 arr24 prod sum)

prod24 : Ty24 → Ty24 → Ty24; prod24
 = λ A B Ty24 nat24 top24 bot24 arr24 prod24 sum →
     prod24 (A Ty24 nat24 top24 bot24 arr24 prod24 sum) (B Ty24 nat24 top24 bot24 arr24 prod24 sum)

sum24 : Ty24 → Ty24 → Ty24; sum24
 = λ A B Ty24 nat24 top24 bot24 arr24 prod24 sum24 →
     sum24 (A Ty24 nat24 top24 bot24 arr24 prod24 sum24) (B Ty24 nat24 top24 bot24 arr24 prod24 sum24)

Con24 : Set; Con24
 = (Con24 : Set)
   (nil  : Con24)
   (snoc : Con24 → Ty24 → Con24)
 → Con24

nil24 : Con24; nil24
 = λ Con24 nil24 snoc → nil24

snoc24 : Con24 → Ty24 → Con24; snoc24
 = λ Γ A Con24 nil24 snoc24 → snoc24 (Γ Con24 nil24 snoc24) A

Var24 : Con24 → Ty24 → Set; Var24
 = λ Γ A →
   (Var24 : Con24 → Ty24 → Set)
   (vz  : ∀{Γ A} → Var24 (snoc24 Γ A) A)
   (vs  : ∀{Γ B A} → Var24 Γ A → Var24 (snoc24 Γ B) A)
 → Var24 Γ A

vz24 : ∀{Γ A} → Var24 (snoc24 Γ A) A; vz24
 = λ Var24 vz24 vs → vz24

vs24 : ∀{Γ B A} → Var24 Γ A → Var24 (snoc24 Γ B) A; vs24
 = λ x Var24 vz24 vs24 → vs24 (x Var24 vz24 vs24)

Tm24 : Con24 → Ty24 → Set; Tm24
 = λ Γ A →
   (Tm24  : Con24 → Ty24 → Set)
   (var   : ∀{Γ A} → Var24 Γ A → Tm24 Γ A)
   (lam   : ∀{Γ A B} → Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B))
   (app   : ∀{Γ A B} → Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B)
   (tt    : ∀{Γ} → Tm24 Γ top24)
   (pair  : ∀{Γ A B} → Tm24 Γ A → Tm24 Γ B → Tm24 Γ (prod24 A B))
   (fst   : ∀{Γ A B} → Tm24 Γ (prod24 A B) → Tm24 Γ A)
   (snd   : ∀{Γ A B} → Tm24 Γ (prod24 A B) → Tm24 Γ B)
   (left  : ∀{Γ A B} → Tm24 Γ A → Tm24 Γ (sum24 A B))
   (right : ∀{Γ A B} → Tm24 Γ B → Tm24 Γ (sum24 A B))
   (case  : ∀{Γ A B C} → Tm24 Γ (sum24 A B) → Tm24 Γ (arr24 A C) → Tm24 Γ (arr24 B C) → Tm24 Γ C)
   (zero  : ∀{Γ} → Tm24 Γ nat24)
   (suc   : ∀{Γ} → Tm24 Γ nat24 → Tm24 Γ nat24)
   (rec   : ∀{Γ A} → Tm24 Γ nat24 → Tm24 Γ (arr24 nat24 (arr24 A A)) → Tm24 Γ A → Tm24 Γ A)
 → Tm24 Γ A

var24 : ∀{Γ A} → Var24 Γ A → Tm24 Γ A; var24
 = λ x Tm24 var24 lam app tt pair fst snd left right case zero suc rec →
     var24 x

lam24 : ∀{Γ A B} → Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B); lam24
 = λ t Tm24 var24 lam24 app tt pair fst snd left right case zero suc rec →
     lam24 (t Tm24 var24 lam24 app tt pair fst snd left right case zero suc rec)

app24 : ∀{Γ A B} → Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B; app24
 = λ t u Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec →
     app24 (t Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec)
         (u Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec)

tt24 : ∀{Γ} → Tm24 Γ top24; tt24
 = λ Tm24 var24 lam24 app24 tt24 pair fst snd left right case zero suc rec → tt24

pair24 : ∀{Γ A B} → Tm24 Γ A → Tm24 Γ B → Tm24 Γ (prod24 A B); pair24
 = λ t u Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec →
     pair24 (t Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec)
          (u Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec)

fst24 : ∀{Γ A B} → Tm24 Γ (prod24 A B) → Tm24 Γ A; fst24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd left right case zero suc rec →
     fst24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd left right case zero suc rec)

snd24 : ∀{Γ A B} → Tm24 Γ (prod24 A B) → Tm24 Γ B; snd24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left right case zero suc rec →
     snd24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left right case zero suc rec)

left24 : ∀{Γ A B} → Tm24 Γ A → Tm24 Γ (sum24 A B); left24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right case zero suc rec →
     left24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right case zero suc rec)

right24 : ∀{Γ A B} → Tm24 Γ B → Tm24 Γ (sum24 A B); right24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case zero suc rec →
     right24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case zero suc rec)

case24 : ∀{Γ A B C} → Tm24 Γ (sum24 A B) → Tm24 Γ (arr24 A C) → Tm24 Γ (arr24 B C) → Tm24 Γ C; case24
 = λ t u v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec →
     case24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)
           (u Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)
           (v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)

zero24  : ∀{Γ} → Tm24 Γ nat24; zero24
 = λ Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc rec → zero24

suc24 : ∀{Γ} → Tm24 Γ nat24 → Tm24 Γ nat24; suc24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec →
   suc24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec)

rec24 : ∀{Γ A} → Tm24 Γ nat24 → Tm24 Γ (arr24 nat24 (arr24 A A)) → Tm24 Γ A → Tm24 Γ A; rec24
 = λ t u v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24 →
     rec24 (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)
         (u Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)
         (v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)

v024 : ∀{Γ A} → Tm24 (snoc24 Γ A) A; v024
 = var24 vz24

v124 : ∀{Γ A B} → Tm24 (snoc24 (snoc24 Γ A) B) A; v124
 = var24 (vs24 vz24)

v224 : ∀{Γ A B C} → Tm24 (snoc24 (snoc24 (snoc24 Γ A) B) C) A; v224
 = var24 (vs24 (vs24 vz24))

v324 : ∀{Γ A B C D} → Tm24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) A; v324
 = var24 (vs24 (vs24 (vs24 vz24)))

tbool24 : Ty24; tbool24
 = sum24 top24 top24

true24 : ∀{Γ} → Tm24 Γ tbool24; true24
 = left24 tt24

tfalse24 : ∀{Γ} → Tm24 Γ tbool24; tfalse24
 = right24 tt24

ifthenelse24 : ∀{Γ A} → Tm24 Γ (arr24 tbool24 (arr24 A (arr24 A A))); ifthenelse24
 = lam24 (lam24 (lam24 (case24 v224 (lam24 v224) (lam24 v124))))

times424 : ∀{Γ A} → Tm24 Γ (arr24 (arr24 A A) (arr24 A A)); times424
  = lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024)))))

add24 : ∀{Γ} → Tm24 Γ (arr24 nat24 (arr24 nat24 nat24)); add24
 = lam24 (rec24 v024
       (lam24 (lam24 (lam24 (suc24 (app24 v124 v024)))))
       (lam24 v024))

mul24 : ∀{Γ} → Tm24 Γ (arr24 nat24 (arr24 nat24 nat24)); mul24
 = lam24 (rec24 v024
       (lam24 (lam24 (lam24 (app24 (app24 add24 (app24 v124 v024)) v024))))
       (lam24 zero24))

fact24 : ∀{Γ} → Tm24 Γ (arr24 nat24 nat24); fact24
 = lam24 (rec24 v024 (lam24 (lam24 (app24 (app24 mul24 (suc24 v124)) v024)))
        (suc24 zero24))
{-# OPTIONS --type-in-type #-}

Ty25 : Set
Ty25 =
   (Ty25         : Set)
   (nat top bot  : Ty25)
   (arr prod sum : Ty25 → Ty25 → Ty25)
 → Ty25

nat25 : Ty25; nat25 = λ _ nat25 _ _ _ _ _ → nat25
top25 : Ty25; top25 = λ _ _ top25 _ _ _ _ → top25
bot25 : Ty25; bot25 = λ _ _ _ bot25 _ _ _ → bot25

arr25 : Ty25 → Ty25 → Ty25; arr25
 = λ A B Ty25 nat25 top25 bot25 arr25 prod sum →
     arr25 (A Ty25 nat25 top25 bot25 arr25 prod sum) (B Ty25 nat25 top25 bot25 arr25 prod sum)

prod25 : Ty25 → Ty25 → Ty25; prod25
 = λ A B Ty25 nat25 top25 bot25 arr25 prod25 sum →
     prod25 (A Ty25 nat25 top25 bot25 arr25 prod25 sum) (B Ty25 nat25 top25 bot25 arr25 prod25 sum)

sum25 : Ty25 → Ty25 → Ty25; sum25
 = λ A B Ty25 nat25 top25 bot25 arr25 prod25 sum25 →
     sum25 (A Ty25 nat25 top25 bot25 arr25 prod25 sum25) (B Ty25 nat25 top25 bot25 arr25 prod25 sum25)

Con25 : Set; Con25
 = (Con25 : Set)
   (nil  : Con25)
   (snoc : Con25 → Ty25 → Con25)
 → Con25

nil25 : Con25; nil25
 = λ Con25 nil25 snoc → nil25

snoc25 : Con25 → Ty25 → Con25; snoc25
 = λ Γ A Con25 nil25 snoc25 → snoc25 (Γ Con25 nil25 snoc25) A

Var25 : Con25 → Ty25 → Set; Var25
 = λ Γ A →
   (Var25 : Con25 → Ty25 → Set)
   (vz  : ∀{Γ A} → Var25 (snoc25 Γ A) A)
   (vs  : ∀{Γ B A} → Var25 Γ A → Var25 (snoc25 Γ B) A)
 → Var25 Γ A

vz25 : ∀{Γ A} → Var25 (snoc25 Γ A) A; vz25
 = λ Var25 vz25 vs → vz25

vs25 : ∀{Γ B A} → Var25 Γ A → Var25 (snoc25 Γ B) A; vs25
 = λ x Var25 vz25 vs25 → vs25 (x Var25 vz25 vs25)

Tm25 : Con25 → Ty25 → Set; Tm25
 = λ Γ A →
   (Tm25  : Con25 → Ty25 → Set)
   (var   : ∀{Γ A} → Var25 Γ A → Tm25 Γ A)
   (lam   : ∀{Γ A B} → Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B))
   (app   : ∀{Γ A B} → Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B)
   (tt    : ∀{Γ} → Tm25 Γ top25)
   (pair  : ∀{Γ A B} → Tm25 Γ A → Tm25 Γ B → Tm25 Γ (prod25 A B))
   (fst   : ∀{Γ A B} → Tm25 Γ (prod25 A B) → Tm25 Γ A)
   (snd   : ∀{Γ A B} → Tm25 Γ (prod25 A B) → Tm25 Γ B)
   (left  : ∀{Γ A B} → Tm25 Γ A → Tm25 Γ (sum25 A B))
   (right : ∀{Γ A B} → Tm25 Γ B → Tm25 Γ (sum25 A B))
   (case  : ∀{Γ A B C} → Tm25 Γ (sum25 A B) → Tm25 Γ (arr25 A C) → Tm25 Γ (arr25 B C) → Tm25 Γ C)
   (zero  : ∀{Γ} → Tm25 Γ nat25)
   (suc   : ∀{Γ} → Tm25 Γ nat25 → Tm25 Γ nat25)
   (rec   : ∀{Γ A} → Tm25 Γ nat25 → Tm25 Γ (arr25 nat25 (arr25 A A)) → Tm25 Γ A → Tm25 Γ A)
 → Tm25 Γ A

var25 : ∀{Γ A} → Var25 Γ A → Tm25 Γ A; var25
 = λ x Tm25 var25 lam app tt pair fst snd left right case zero suc rec →
     var25 x

lam25 : ∀{Γ A B} → Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B); lam25
 = λ t Tm25 var25 lam25 app tt pair fst snd left right case zero suc rec →
     lam25 (t Tm25 var25 lam25 app tt pair fst snd left right case zero suc rec)

app25 : ∀{Γ A B} → Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B; app25
 = λ t u Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec →
     app25 (t Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec)
         (u Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec)

tt25 : ∀{Γ} → Tm25 Γ top25; tt25
 = λ Tm25 var25 lam25 app25 tt25 pair fst snd left right case zero suc rec → tt25

pair25 : ∀{Γ A B} → Tm25 Γ A → Tm25 Γ B → Tm25 Γ (prod25 A B); pair25
 = λ t u Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec →
     pair25 (t Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec)
          (u Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec)

fst25 : ∀{Γ A B} → Tm25 Γ (prod25 A B) → Tm25 Γ A; fst25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd left right case zero suc rec →
     fst25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd left right case zero suc rec)

snd25 : ∀{Γ A B} → Tm25 Γ (prod25 A B) → Tm25 Γ B; snd25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left right case zero suc rec →
     snd25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left right case zero suc rec)

left25 : ∀{Γ A B} → Tm25 Γ A → Tm25 Γ (sum25 A B); left25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right case zero suc rec →
     left25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right case zero suc rec)

right25 : ∀{Γ A B} → Tm25 Γ B → Tm25 Γ (sum25 A B); right25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case zero suc rec →
     right25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case zero suc rec)

case25 : ∀{Γ A B C} → Tm25 Γ (sum25 A B) → Tm25 Γ (arr25 A C) → Tm25 Γ (arr25 B C) → Tm25 Γ C; case25
 = λ t u v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec →
     case25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)
           (u Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)
           (v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)

zero25  : ∀{Γ} → Tm25 Γ nat25; zero25
 = λ Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc rec → zero25

suc25 : ∀{Γ} → Tm25 Γ nat25 → Tm25 Γ nat25; suc25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec →
   suc25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec)

rec25 : ∀{Γ A} → Tm25 Γ nat25 → Tm25 Γ (arr25 nat25 (arr25 A A)) → Tm25 Γ A → Tm25 Γ A; rec25
 = λ t u v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25 →
     rec25 (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)
         (u Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)
         (v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)

v025 : ∀{Γ A} → Tm25 (snoc25 Γ A) A; v025
 = var25 vz25

v125 : ∀{Γ A B} → Tm25 (snoc25 (snoc25 Γ A) B) A; v125
 = var25 (vs25 vz25)

v225 : ∀{Γ A B C} → Tm25 (snoc25 (snoc25 (snoc25 Γ A) B) C) A; v225
 = var25 (vs25 (vs25 vz25))

v325 : ∀{Γ A B C D} → Tm25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) A; v325
 = var25 (vs25 (vs25 (vs25 vz25)))

tbool25 : Ty25; tbool25
 = sum25 top25 top25

true25 : ∀{Γ} → Tm25 Γ tbool25; true25
 = left25 tt25

tfalse25 : ∀{Γ} → Tm25 Γ tbool25; tfalse25
 = right25 tt25

ifthenelse25 : ∀{Γ A} → Tm25 Γ (arr25 tbool25 (arr25 A (arr25 A A))); ifthenelse25
 = lam25 (lam25 (lam25 (case25 v225 (lam25 v225) (lam25 v125))))

times425 : ∀{Γ A} → Tm25 Γ (arr25 (arr25 A A) (arr25 A A)); times425
  = lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025)))))

add25 : ∀{Γ} → Tm25 Γ (arr25 nat25 (arr25 nat25 nat25)); add25
 = lam25 (rec25 v025
       (lam25 (lam25 (lam25 (suc25 (app25 v125 v025)))))
       (lam25 v025))

mul25 : ∀{Γ} → Tm25 Γ (arr25 nat25 (arr25 nat25 nat25)); mul25
 = lam25 (rec25 v025
       (lam25 (lam25 (lam25 (app25 (app25 add25 (app25 v125 v025)) v025))))
       (lam25 zero25))

fact25 : ∀{Γ} → Tm25 Γ (arr25 nat25 nat25); fact25
 = lam25 (rec25 v025 (lam25 (lam25 (app25 (app25 mul25 (suc25 v125)) v025)))
        (suc25 zero25))
{-# OPTIONS --type-in-type #-}

Ty26 : Set
Ty26 =
   (Ty26         : Set)
   (nat top bot  : Ty26)
   (arr prod sum : Ty26 → Ty26 → Ty26)
 → Ty26

nat26 : Ty26; nat26 = λ _ nat26 _ _ _ _ _ → nat26
top26 : Ty26; top26 = λ _ _ top26 _ _ _ _ → top26
bot26 : Ty26; bot26 = λ _ _ _ bot26 _ _ _ → bot26

arr26 : Ty26 → Ty26 → Ty26; arr26
 = λ A B Ty26 nat26 top26 bot26 arr26 prod sum →
     arr26 (A Ty26 nat26 top26 bot26 arr26 prod sum) (B Ty26 nat26 top26 bot26 arr26 prod sum)

prod26 : Ty26 → Ty26 → Ty26; prod26
 = λ A B Ty26 nat26 top26 bot26 arr26 prod26 sum →
     prod26 (A Ty26 nat26 top26 bot26 arr26 prod26 sum) (B Ty26 nat26 top26 bot26 arr26 prod26 sum)

sum26 : Ty26 → Ty26 → Ty26; sum26
 = λ A B Ty26 nat26 top26 bot26 arr26 prod26 sum26 →
     sum26 (A Ty26 nat26 top26 bot26 arr26 prod26 sum26) (B Ty26 nat26 top26 bot26 arr26 prod26 sum26)

Con26 : Set; Con26
 = (Con26 : Set)
   (nil  : Con26)
   (snoc : Con26 → Ty26 → Con26)
 → Con26

nil26 : Con26; nil26
 = λ Con26 nil26 snoc → nil26

snoc26 : Con26 → Ty26 → Con26; snoc26
 = λ Γ A Con26 nil26 snoc26 → snoc26 (Γ Con26 nil26 snoc26) A

Var26 : Con26 → Ty26 → Set; Var26
 = λ Γ A →
   (Var26 : Con26 → Ty26 → Set)
   (vz  : ∀{Γ A} → Var26 (snoc26 Γ A) A)
   (vs  : ∀{Γ B A} → Var26 Γ A → Var26 (snoc26 Γ B) A)
 → Var26 Γ A

vz26 : ∀{Γ A} → Var26 (snoc26 Γ A) A; vz26
 = λ Var26 vz26 vs → vz26

vs26 : ∀{Γ B A} → Var26 Γ A → Var26 (snoc26 Γ B) A; vs26
 = λ x Var26 vz26 vs26 → vs26 (x Var26 vz26 vs26)

Tm26 : Con26 → Ty26 → Set; Tm26
 = λ Γ A →
   (Tm26  : Con26 → Ty26 → Set)
   (var   : ∀{Γ A} → Var26 Γ A → Tm26 Γ A)
   (lam   : ∀{Γ A B} → Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B))
   (app   : ∀{Γ A B} → Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B)
   (tt    : ∀{Γ} → Tm26 Γ top26)
   (pair  : ∀{Γ A B} → Tm26 Γ A → Tm26 Γ B → Tm26 Γ (prod26 A B))
   (fst   : ∀{Γ A B} → Tm26 Γ (prod26 A B) → Tm26 Γ A)
   (snd   : ∀{Γ A B} → Tm26 Γ (prod26 A B) → Tm26 Γ B)
   (left  : ∀{Γ A B} → Tm26 Γ A → Tm26 Γ (sum26 A B))
   (right : ∀{Γ A B} → Tm26 Γ B → Tm26 Γ (sum26 A B))
   (case  : ∀{Γ A B C} → Tm26 Γ (sum26 A B) → Tm26 Γ (arr26 A C) → Tm26 Γ (arr26 B C) → Tm26 Γ C)
   (zero  : ∀{Γ} → Tm26 Γ nat26)
   (suc   : ∀{Γ} → Tm26 Γ nat26 → Tm26 Γ nat26)
   (rec   : ∀{Γ A} → Tm26 Γ nat26 → Tm26 Γ (arr26 nat26 (arr26 A A)) → Tm26 Γ A → Tm26 Γ A)
 → Tm26 Γ A

var26 : ∀{Γ A} → Var26 Γ A → Tm26 Γ A; var26
 = λ x Tm26 var26 lam app tt pair fst snd left right case zero suc rec →
     var26 x

lam26 : ∀{Γ A B} → Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B); lam26
 = λ t Tm26 var26 lam26 app tt pair fst snd left right case zero suc rec →
     lam26 (t Tm26 var26 lam26 app tt pair fst snd left right case zero suc rec)

app26 : ∀{Γ A B} → Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B; app26
 = λ t u Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec →
     app26 (t Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec)
         (u Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec)

tt26 : ∀{Γ} → Tm26 Γ top26; tt26
 = λ Tm26 var26 lam26 app26 tt26 pair fst snd left right case zero suc rec → tt26

pair26 : ∀{Γ A B} → Tm26 Γ A → Tm26 Γ B → Tm26 Γ (prod26 A B); pair26
 = λ t u Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec →
     pair26 (t Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec)
          (u Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec)

fst26 : ∀{Γ A B} → Tm26 Γ (prod26 A B) → Tm26 Γ A; fst26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd left right case zero suc rec →
     fst26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd left right case zero suc rec)

snd26 : ∀{Γ A B} → Tm26 Γ (prod26 A B) → Tm26 Γ B; snd26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left right case zero suc rec →
     snd26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left right case zero suc rec)

left26 : ∀{Γ A B} → Tm26 Γ A → Tm26 Γ (sum26 A B); left26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right case zero suc rec →
     left26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right case zero suc rec)

right26 : ∀{Γ A B} → Tm26 Γ B → Tm26 Γ (sum26 A B); right26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case zero suc rec →
     right26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case zero suc rec)

case26 : ∀{Γ A B C} → Tm26 Γ (sum26 A B) → Tm26 Γ (arr26 A C) → Tm26 Γ (arr26 B C) → Tm26 Γ C; case26
 = λ t u v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec →
     case26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)
           (u Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)
           (v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)

zero26  : ∀{Γ} → Tm26 Γ nat26; zero26
 = λ Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc rec → zero26

suc26 : ∀{Γ} → Tm26 Γ nat26 → Tm26 Γ nat26; suc26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec →
   suc26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec)

rec26 : ∀{Γ A} → Tm26 Γ nat26 → Tm26 Γ (arr26 nat26 (arr26 A A)) → Tm26 Γ A → Tm26 Γ A; rec26
 = λ t u v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26 →
     rec26 (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)
         (u Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)
         (v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)

v026 : ∀{Γ A} → Tm26 (snoc26 Γ A) A; v026
 = var26 vz26

v126 : ∀{Γ A B} → Tm26 (snoc26 (snoc26 Γ A) B) A; v126
 = var26 (vs26 vz26)

v226 : ∀{Γ A B C} → Tm26 (snoc26 (snoc26 (snoc26 Γ A) B) C) A; v226
 = var26 (vs26 (vs26 vz26))

v326 : ∀{Γ A B C D} → Tm26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) A; v326
 = var26 (vs26 (vs26 (vs26 vz26)))

tbool26 : Ty26; tbool26
 = sum26 top26 top26

true26 : ∀{Γ} → Tm26 Γ tbool26; true26
 = left26 tt26

tfalse26 : ∀{Γ} → Tm26 Γ tbool26; tfalse26
 = right26 tt26

ifthenelse26 : ∀{Γ A} → Tm26 Γ (arr26 tbool26 (arr26 A (arr26 A A))); ifthenelse26
 = lam26 (lam26 (lam26 (case26 v226 (lam26 v226) (lam26 v126))))

times426 : ∀{Γ A} → Tm26 Γ (arr26 (arr26 A A) (arr26 A A)); times426
  = lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026)))))

add26 : ∀{Γ} → Tm26 Γ (arr26 nat26 (arr26 nat26 nat26)); add26
 = lam26 (rec26 v026
       (lam26 (lam26 (lam26 (suc26 (app26 v126 v026)))))
       (lam26 v026))

mul26 : ∀{Γ} → Tm26 Γ (arr26 nat26 (arr26 nat26 nat26)); mul26
 = lam26 (rec26 v026
       (lam26 (lam26 (lam26 (app26 (app26 add26 (app26 v126 v026)) v026))))
       (lam26 zero26))

fact26 : ∀{Γ} → Tm26 Γ (arr26 nat26 nat26); fact26
 = lam26 (rec26 v026 (lam26 (lam26 (app26 (app26 mul26 (suc26 v126)) v026)))
        (suc26 zero26))
{-# OPTIONS --type-in-type #-}

Ty27 : Set
Ty27 =
   (Ty27         : Set)
   (nat top bot  : Ty27)
   (arr prod sum : Ty27 → Ty27 → Ty27)
 → Ty27

nat27 : Ty27; nat27 = λ _ nat27 _ _ _ _ _ → nat27
top27 : Ty27; top27 = λ _ _ top27 _ _ _ _ → top27
bot27 : Ty27; bot27 = λ _ _ _ bot27 _ _ _ → bot27

arr27 : Ty27 → Ty27 → Ty27; arr27
 = λ A B Ty27 nat27 top27 bot27 arr27 prod sum →
     arr27 (A Ty27 nat27 top27 bot27 arr27 prod sum) (B Ty27 nat27 top27 bot27 arr27 prod sum)

prod27 : Ty27 → Ty27 → Ty27; prod27
 = λ A B Ty27 nat27 top27 bot27 arr27 prod27 sum →
     prod27 (A Ty27 nat27 top27 bot27 arr27 prod27 sum) (B Ty27 nat27 top27 bot27 arr27 prod27 sum)

sum27 : Ty27 → Ty27 → Ty27; sum27
 = λ A B Ty27 nat27 top27 bot27 arr27 prod27 sum27 →
     sum27 (A Ty27 nat27 top27 bot27 arr27 prod27 sum27) (B Ty27 nat27 top27 bot27 arr27 prod27 sum27)

Con27 : Set; Con27
 = (Con27 : Set)
   (nil  : Con27)
   (snoc : Con27 → Ty27 → Con27)
 → Con27

nil27 : Con27; nil27
 = λ Con27 nil27 snoc → nil27

snoc27 : Con27 → Ty27 → Con27; snoc27
 = λ Γ A Con27 nil27 snoc27 → snoc27 (Γ Con27 nil27 snoc27) A

Var27 : Con27 → Ty27 → Set; Var27
 = λ Γ A →
   (Var27 : Con27 → Ty27 → Set)
   (vz  : ∀{Γ A} → Var27 (snoc27 Γ A) A)
   (vs  : ∀{Γ B A} → Var27 Γ A → Var27 (snoc27 Γ B) A)
 → Var27 Γ A

vz27 : ∀{Γ A} → Var27 (snoc27 Γ A) A; vz27
 = λ Var27 vz27 vs → vz27

vs27 : ∀{Γ B A} → Var27 Γ A → Var27 (snoc27 Γ B) A; vs27
 = λ x Var27 vz27 vs27 → vs27 (x Var27 vz27 vs27)

Tm27 : Con27 → Ty27 → Set; Tm27
 = λ Γ A →
   (Tm27  : Con27 → Ty27 → Set)
   (var   : ∀{Γ A} → Var27 Γ A → Tm27 Γ A)
   (lam   : ∀{Γ A B} → Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B))
   (app   : ∀{Γ A B} → Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B)
   (tt    : ∀{Γ} → Tm27 Γ top27)
   (pair  : ∀{Γ A B} → Tm27 Γ A → Tm27 Γ B → Tm27 Γ (prod27 A B))
   (fst   : ∀{Γ A B} → Tm27 Γ (prod27 A B) → Tm27 Γ A)
   (snd   : ∀{Γ A B} → Tm27 Γ (prod27 A B) → Tm27 Γ B)
   (left  : ∀{Γ A B} → Tm27 Γ A → Tm27 Γ (sum27 A B))
   (right : ∀{Γ A B} → Tm27 Γ B → Tm27 Γ (sum27 A B))
   (case  : ∀{Γ A B C} → Tm27 Γ (sum27 A B) → Tm27 Γ (arr27 A C) → Tm27 Γ (arr27 B C) → Tm27 Γ C)
   (zero  : ∀{Γ} → Tm27 Γ nat27)
   (suc   : ∀{Γ} → Tm27 Γ nat27 → Tm27 Γ nat27)
   (rec   : ∀{Γ A} → Tm27 Γ nat27 → Tm27 Γ (arr27 nat27 (arr27 A A)) → Tm27 Γ A → Tm27 Γ A)
 → Tm27 Γ A

var27 : ∀{Γ A} → Var27 Γ A → Tm27 Γ A; var27
 = λ x Tm27 var27 lam app tt pair fst snd left right case zero suc rec →
     var27 x

lam27 : ∀{Γ A B} → Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B); lam27
 = λ t Tm27 var27 lam27 app tt pair fst snd left right case zero suc rec →
     lam27 (t Tm27 var27 lam27 app tt pair fst snd left right case zero suc rec)

app27 : ∀{Γ A B} → Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B; app27
 = λ t u Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec →
     app27 (t Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec)
         (u Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec)

tt27 : ∀{Γ} → Tm27 Γ top27; tt27
 = λ Tm27 var27 lam27 app27 tt27 pair fst snd left right case zero suc rec → tt27

pair27 : ∀{Γ A B} → Tm27 Γ A → Tm27 Γ B → Tm27 Γ (prod27 A B); pair27
 = λ t u Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec →
     pair27 (t Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec)
          (u Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec)

fst27 : ∀{Γ A B} → Tm27 Γ (prod27 A B) → Tm27 Γ A; fst27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd left right case zero suc rec →
     fst27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd left right case zero suc rec)

snd27 : ∀{Γ A B} → Tm27 Γ (prod27 A B) → Tm27 Γ B; snd27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left right case zero suc rec →
     snd27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left right case zero suc rec)

left27 : ∀{Γ A B} → Tm27 Γ A → Tm27 Γ (sum27 A B); left27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right case zero suc rec →
     left27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right case zero suc rec)

right27 : ∀{Γ A B} → Tm27 Γ B → Tm27 Γ (sum27 A B); right27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case zero suc rec →
     right27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case zero suc rec)

case27 : ∀{Γ A B C} → Tm27 Γ (sum27 A B) → Tm27 Γ (arr27 A C) → Tm27 Γ (arr27 B C) → Tm27 Γ C; case27
 = λ t u v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec →
     case27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)
           (u Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)
           (v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)

zero27  : ∀{Γ} → Tm27 Γ nat27; zero27
 = λ Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc rec → zero27

suc27 : ∀{Γ} → Tm27 Γ nat27 → Tm27 Γ nat27; suc27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec →
   suc27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec)

rec27 : ∀{Γ A} → Tm27 Γ nat27 → Tm27 Γ (arr27 nat27 (arr27 A A)) → Tm27 Γ A → Tm27 Γ A; rec27
 = λ t u v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27 →
     rec27 (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)
         (u Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)
         (v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)

v027 : ∀{Γ A} → Tm27 (snoc27 Γ A) A; v027
 = var27 vz27

v127 : ∀{Γ A B} → Tm27 (snoc27 (snoc27 Γ A) B) A; v127
 = var27 (vs27 vz27)

v227 : ∀{Γ A B C} → Tm27 (snoc27 (snoc27 (snoc27 Γ A) B) C) A; v227
 = var27 (vs27 (vs27 vz27))

v327 : ∀{Γ A B C D} → Tm27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) A; v327
 = var27 (vs27 (vs27 (vs27 vz27)))

tbool27 : Ty27; tbool27
 = sum27 top27 top27

true27 : ∀{Γ} → Tm27 Γ tbool27; true27
 = left27 tt27

tfalse27 : ∀{Γ} → Tm27 Γ tbool27; tfalse27
 = right27 tt27

ifthenelse27 : ∀{Γ A} → Tm27 Γ (arr27 tbool27 (arr27 A (arr27 A A))); ifthenelse27
 = lam27 (lam27 (lam27 (case27 v227 (lam27 v227) (lam27 v127))))

times427 : ∀{Γ A} → Tm27 Γ (arr27 (arr27 A A) (arr27 A A)); times427
  = lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027)))))

add27 : ∀{Γ} → Tm27 Γ (arr27 nat27 (arr27 nat27 nat27)); add27
 = lam27 (rec27 v027
       (lam27 (lam27 (lam27 (suc27 (app27 v127 v027)))))
       (lam27 v027))

mul27 : ∀{Γ} → Tm27 Γ (arr27 nat27 (arr27 nat27 nat27)); mul27
 = lam27 (rec27 v027
       (lam27 (lam27 (lam27 (app27 (app27 add27 (app27 v127 v027)) v027))))
       (lam27 zero27))

fact27 : ∀{Γ} → Tm27 Γ (arr27 nat27 nat27); fact27
 = lam27 (rec27 v027 (lam27 (lam27 (app27 (app27 mul27 (suc27 v127)) v027)))
        (suc27 zero27))
{-# OPTIONS --type-in-type #-}

Ty28 : Set
Ty28 =
   (Ty28         : Set)
   (nat top bot  : Ty28)
   (arr prod sum : Ty28 → Ty28 → Ty28)
 → Ty28

nat28 : Ty28; nat28 = λ _ nat28 _ _ _ _ _ → nat28
top28 : Ty28; top28 = λ _ _ top28 _ _ _ _ → top28
bot28 : Ty28; bot28 = λ _ _ _ bot28 _ _ _ → bot28

arr28 : Ty28 → Ty28 → Ty28; arr28
 = λ A B Ty28 nat28 top28 bot28 arr28 prod sum →
     arr28 (A Ty28 nat28 top28 bot28 arr28 prod sum) (B Ty28 nat28 top28 bot28 arr28 prod sum)

prod28 : Ty28 → Ty28 → Ty28; prod28
 = λ A B Ty28 nat28 top28 bot28 arr28 prod28 sum →
     prod28 (A Ty28 nat28 top28 bot28 arr28 prod28 sum) (B Ty28 nat28 top28 bot28 arr28 prod28 sum)

sum28 : Ty28 → Ty28 → Ty28; sum28
 = λ A B Ty28 nat28 top28 bot28 arr28 prod28 sum28 →
     sum28 (A Ty28 nat28 top28 bot28 arr28 prod28 sum28) (B Ty28 nat28 top28 bot28 arr28 prod28 sum28)

Con28 : Set; Con28
 = (Con28 : Set)
   (nil  : Con28)
   (snoc : Con28 → Ty28 → Con28)
 → Con28

nil28 : Con28; nil28
 = λ Con28 nil28 snoc → nil28

snoc28 : Con28 → Ty28 → Con28; snoc28
 = λ Γ A Con28 nil28 snoc28 → snoc28 (Γ Con28 nil28 snoc28) A

Var28 : Con28 → Ty28 → Set; Var28
 = λ Γ A →
   (Var28 : Con28 → Ty28 → Set)
   (vz  : ∀{Γ A} → Var28 (snoc28 Γ A) A)
   (vs  : ∀{Γ B A} → Var28 Γ A → Var28 (snoc28 Γ B) A)
 → Var28 Γ A

vz28 : ∀{Γ A} → Var28 (snoc28 Γ A) A; vz28
 = λ Var28 vz28 vs → vz28

vs28 : ∀{Γ B A} → Var28 Γ A → Var28 (snoc28 Γ B) A; vs28
 = λ x Var28 vz28 vs28 → vs28 (x Var28 vz28 vs28)

Tm28 : Con28 → Ty28 → Set; Tm28
 = λ Γ A →
   (Tm28  : Con28 → Ty28 → Set)
   (var   : ∀{Γ A} → Var28 Γ A → Tm28 Γ A)
   (lam   : ∀{Γ A B} → Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B))
   (app   : ∀{Γ A B} → Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B)
   (tt    : ∀{Γ} → Tm28 Γ top28)
   (pair  : ∀{Γ A B} → Tm28 Γ A → Tm28 Γ B → Tm28 Γ (prod28 A B))
   (fst   : ∀{Γ A B} → Tm28 Γ (prod28 A B) → Tm28 Γ A)
   (snd   : ∀{Γ A B} → Tm28 Γ (prod28 A B) → Tm28 Γ B)
   (left  : ∀{Γ A B} → Tm28 Γ A → Tm28 Γ (sum28 A B))
   (right : ∀{Γ A B} → Tm28 Γ B → Tm28 Γ (sum28 A B))
   (case  : ∀{Γ A B C} → Tm28 Γ (sum28 A B) → Tm28 Γ (arr28 A C) → Tm28 Γ (arr28 B C) → Tm28 Γ C)
   (zero  : ∀{Γ} → Tm28 Γ nat28)
   (suc   : ∀{Γ} → Tm28 Γ nat28 → Tm28 Γ nat28)
   (rec   : ∀{Γ A} → Tm28 Γ nat28 → Tm28 Γ (arr28 nat28 (arr28 A A)) → Tm28 Γ A → Tm28 Γ A)
 → Tm28 Γ A

var28 : ∀{Γ A} → Var28 Γ A → Tm28 Γ A; var28
 = λ x Tm28 var28 lam app tt pair fst snd left right case zero suc rec →
     var28 x

lam28 : ∀{Γ A B} → Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B); lam28
 = λ t Tm28 var28 lam28 app tt pair fst snd left right case zero suc rec →
     lam28 (t Tm28 var28 lam28 app tt pair fst snd left right case zero suc rec)

app28 : ∀{Γ A B} → Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B; app28
 = λ t u Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec →
     app28 (t Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec)
         (u Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec)

tt28 : ∀{Γ} → Tm28 Γ top28; tt28
 = λ Tm28 var28 lam28 app28 tt28 pair fst snd left right case zero suc rec → tt28

pair28 : ∀{Γ A B} → Tm28 Γ A → Tm28 Γ B → Tm28 Γ (prod28 A B); pair28
 = λ t u Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec →
     pair28 (t Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec)
          (u Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec)

fst28 : ∀{Γ A B} → Tm28 Γ (prod28 A B) → Tm28 Γ A; fst28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd left right case zero suc rec →
     fst28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd left right case zero suc rec)

snd28 : ∀{Γ A B} → Tm28 Γ (prod28 A B) → Tm28 Γ B; snd28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left right case zero suc rec →
     snd28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left right case zero suc rec)

left28 : ∀{Γ A B} → Tm28 Γ A → Tm28 Γ (sum28 A B); left28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right case zero suc rec →
     left28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right case zero suc rec)

right28 : ∀{Γ A B} → Tm28 Γ B → Tm28 Γ (sum28 A B); right28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case zero suc rec →
     right28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case zero suc rec)

case28 : ∀{Γ A B C} → Tm28 Γ (sum28 A B) → Tm28 Γ (arr28 A C) → Tm28 Γ (arr28 B C) → Tm28 Γ C; case28
 = λ t u v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec →
     case28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)
           (u Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)
           (v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)

zero28  : ∀{Γ} → Tm28 Γ nat28; zero28
 = λ Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc rec → zero28

suc28 : ∀{Γ} → Tm28 Γ nat28 → Tm28 Γ nat28; suc28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec →
   suc28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec)

rec28 : ∀{Γ A} → Tm28 Γ nat28 → Tm28 Γ (arr28 nat28 (arr28 A A)) → Tm28 Γ A → Tm28 Γ A; rec28
 = λ t u v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28 →
     rec28 (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)
         (u Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)
         (v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)

v028 : ∀{Γ A} → Tm28 (snoc28 Γ A) A; v028
 = var28 vz28

v128 : ∀{Γ A B} → Tm28 (snoc28 (snoc28 Γ A) B) A; v128
 = var28 (vs28 vz28)

v228 : ∀{Γ A B C} → Tm28 (snoc28 (snoc28 (snoc28 Γ A) B) C) A; v228
 = var28 (vs28 (vs28 vz28))

v328 : ∀{Γ A B C D} → Tm28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) A; v328
 = var28 (vs28 (vs28 (vs28 vz28)))

tbool28 : Ty28; tbool28
 = sum28 top28 top28

true28 : ∀{Γ} → Tm28 Γ tbool28; true28
 = left28 tt28

tfalse28 : ∀{Γ} → Tm28 Γ tbool28; tfalse28
 = right28 tt28

ifthenelse28 : ∀{Γ A} → Tm28 Γ (arr28 tbool28 (arr28 A (arr28 A A))); ifthenelse28
 = lam28 (lam28 (lam28 (case28 v228 (lam28 v228) (lam28 v128))))

times428 : ∀{Γ A} → Tm28 Γ (arr28 (arr28 A A) (arr28 A A)); times428
  = lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028)))))

add28 : ∀{Γ} → Tm28 Γ (arr28 nat28 (arr28 nat28 nat28)); add28
 = lam28 (rec28 v028
       (lam28 (lam28 (lam28 (suc28 (app28 v128 v028)))))
       (lam28 v028))

mul28 : ∀{Γ} → Tm28 Γ (arr28 nat28 (arr28 nat28 nat28)); mul28
 = lam28 (rec28 v028
       (lam28 (lam28 (lam28 (app28 (app28 add28 (app28 v128 v028)) v028))))
       (lam28 zero28))

fact28 : ∀{Γ} → Tm28 Γ (arr28 nat28 nat28); fact28
 = lam28 (rec28 v028 (lam28 (lam28 (app28 (app28 mul28 (suc28 v128)) v028)))
        (suc28 zero28))
{-# OPTIONS --type-in-type #-}

Ty29 : Set
Ty29 =
   (Ty29         : Set)
   (nat top bot  : Ty29)
   (arr prod sum : Ty29 → Ty29 → Ty29)
 → Ty29

nat29 : Ty29; nat29 = λ _ nat29 _ _ _ _ _ → nat29
top29 : Ty29; top29 = λ _ _ top29 _ _ _ _ → top29
bot29 : Ty29; bot29 = λ _ _ _ bot29 _ _ _ → bot29

arr29 : Ty29 → Ty29 → Ty29; arr29
 = λ A B Ty29 nat29 top29 bot29 arr29 prod sum →
     arr29 (A Ty29 nat29 top29 bot29 arr29 prod sum) (B Ty29 nat29 top29 bot29 arr29 prod sum)

prod29 : Ty29 → Ty29 → Ty29; prod29
 = λ A B Ty29 nat29 top29 bot29 arr29 prod29 sum →
     prod29 (A Ty29 nat29 top29 bot29 arr29 prod29 sum) (B Ty29 nat29 top29 bot29 arr29 prod29 sum)

sum29 : Ty29 → Ty29 → Ty29; sum29
 = λ A B Ty29 nat29 top29 bot29 arr29 prod29 sum29 →
     sum29 (A Ty29 nat29 top29 bot29 arr29 prod29 sum29) (B Ty29 nat29 top29 bot29 arr29 prod29 sum29)

Con29 : Set; Con29
 = (Con29 : Set)
   (nil  : Con29)
   (snoc : Con29 → Ty29 → Con29)
 → Con29

nil29 : Con29; nil29
 = λ Con29 nil29 snoc → nil29

snoc29 : Con29 → Ty29 → Con29; snoc29
 = λ Γ A Con29 nil29 snoc29 → snoc29 (Γ Con29 nil29 snoc29) A

Var29 : Con29 → Ty29 → Set; Var29
 = λ Γ A →
   (Var29 : Con29 → Ty29 → Set)
   (vz  : ∀{Γ A} → Var29 (snoc29 Γ A) A)
   (vs  : ∀{Γ B A} → Var29 Γ A → Var29 (snoc29 Γ B) A)
 → Var29 Γ A

vz29 : ∀{Γ A} → Var29 (snoc29 Γ A) A; vz29
 = λ Var29 vz29 vs → vz29

vs29 : ∀{Γ B A} → Var29 Γ A → Var29 (snoc29 Γ B) A; vs29
 = λ x Var29 vz29 vs29 → vs29 (x Var29 vz29 vs29)

Tm29 : Con29 → Ty29 → Set; Tm29
 = λ Γ A →
   (Tm29  : Con29 → Ty29 → Set)
   (var   : ∀{Γ A} → Var29 Γ A → Tm29 Γ A)
   (lam   : ∀{Γ A B} → Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B))
   (app   : ∀{Γ A B} → Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B)
   (tt    : ∀{Γ} → Tm29 Γ top29)
   (pair  : ∀{Γ A B} → Tm29 Γ A → Tm29 Γ B → Tm29 Γ (prod29 A B))
   (fst   : ∀{Γ A B} → Tm29 Γ (prod29 A B) → Tm29 Γ A)
   (snd   : ∀{Γ A B} → Tm29 Γ (prod29 A B) → Tm29 Γ B)
   (left  : ∀{Γ A B} → Tm29 Γ A → Tm29 Γ (sum29 A B))
   (right : ∀{Γ A B} → Tm29 Γ B → Tm29 Γ (sum29 A B))
   (case  : ∀{Γ A B C} → Tm29 Γ (sum29 A B) → Tm29 Γ (arr29 A C) → Tm29 Γ (arr29 B C) → Tm29 Γ C)
   (zero  : ∀{Γ} → Tm29 Γ nat29)
   (suc   : ∀{Γ} → Tm29 Γ nat29 → Tm29 Γ nat29)
   (rec   : ∀{Γ A} → Tm29 Γ nat29 → Tm29 Γ (arr29 nat29 (arr29 A A)) → Tm29 Γ A → Tm29 Γ A)
 → Tm29 Γ A

var29 : ∀{Γ A} → Var29 Γ A → Tm29 Γ A; var29
 = λ x Tm29 var29 lam app tt pair fst snd left right case zero suc rec →
     var29 x

lam29 : ∀{Γ A B} → Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B); lam29
 = λ t Tm29 var29 lam29 app tt pair fst snd left right case zero suc rec →
     lam29 (t Tm29 var29 lam29 app tt pair fst snd left right case zero suc rec)

app29 : ∀{Γ A B} → Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B; app29
 = λ t u Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec →
     app29 (t Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec)
         (u Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec)

tt29 : ∀{Γ} → Tm29 Γ top29; tt29
 = λ Tm29 var29 lam29 app29 tt29 pair fst snd left right case zero suc rec → tt29

pair29 : ∀{Γ A B} → Tm29 Γ A → Tm29 Γ B → Tm29 Γ (prod29 A B); pair29
 = λ t u Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec →
     pair29 (t Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec)
          (u Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec)

fst29 : ∀{Γ A B} → Tm29 Γ (prod29 A B) → Tm29 Γ A; fst29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd left right case zero suc rec →
     fst29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd left right case zero suc rec)

snd29 : ∀{Γ A B} → Tm29 Γ (prod29 A B) → Tm29 Γ B; snd29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left right case zero suc rec →
     snd29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left right case zero suc rec)

left29 : ∀{Γ A B} → Tm29 Γ A → Tm29 Γ (sum29 A B); left29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right case zero suc rec →
     left29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right case zero suc rec)

right29 : ∀{Γ A B} → Tm29 Γ B → Tm29 Γ (sum29 A B); right29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case zero suc rec →
     right29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case zero suc rec)

case29 : ∀{Γ A B C} → Tm29 Γ (sum29 A B) → Tm29 Γ (arr29 A C) → Tm29 Γ (arr29 B C) → Tm29 Γ C; case29
 = λ t u v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec →
     case29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)
           (u Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)
           (v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)

zero29  : ∀{Γ} → Tm29 Γ nat29; zero29
 = λ Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc rec → zero29

suc29 : ∀{Γ} → Tm29 Γ nat29 → Tm29 Γ nat29; suc29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec →
   suc29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec)

rec29 : ∀{Γ A} → Tm29 Γ nat29 → Tm29 Γ (arr29 nat29 (arr29 A A)) → Tm29 Γ A → Tm29 Γ A; rec29
 = λ t u v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29 →
     rec29 (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)
         (u Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)
         (v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)

v029 : ∀{Γ A} → Tm29 (snoc29 Γ A) A; v029
 = var29 vz29

v129 : ∀{Γ A B} → Tm29 (snoc29 (snoc29 Γ A) B) A; v129
 = var29 (vs29 vz29)

v229 : ∀{Γ A B C} → Tm29 (snoc29 (snoc29 (snoc29 Γ A) B) C) A; v229
 = var29 (vs29 (vs29 vz29))

v329 : ∀{Γ A B C D} → Tm29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) A; v329
 = var29 (vs29 (vs29 (vs29 vz29)))

tbool29 : Ty29; tbool29
 = sum29 top29 top29

true29 : ∀{Γ} → Tm29 Γ tbool29; true29
 = left29 tt29

tfalse29 : ∀{Γ} → Tm29 Γ tbool29; tfalse29
 = right29 tt29

ifthenelse29 : ∀{Γ A} → Tm29 Γ (arr29 tbool29 (arr29 A (arr29 A A))); ifthenelse29
 = lam29 (lam29 (lam29 (case29 v229 (lam29 v229) (lam29 v129))))

times429 : ∀{Γ A} → Tm29 Γ (arr29 (arr29 A A) (arr29 A A)); times429
  = lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029)))))

add29 : ∀{Γ} → Tm29 Γ (arr29 nat29 (arr29 nat29 nat29)); add29
 = lam29 (rec29 v029
       (lam29 (lam29 (lam29 (suc29 (app29 v129 v029)))))
       (lam29 v029))

mul29 : ∀{Γ} → Tm29 Γ (arr29 nat29 (arr29 nat29 nat29)); mul29
 = lam29 (rec29 v029
       (lam29 (lam29 (lam29 (app29 (app29 add29 (app29 v129 v029)) v029))))
       (lam29 zero29))

fact29 : ∀{Γ} → Tm29 Γ (arr29 nat29 nat29); fact29
 = lam29 (rec29 v029 (lam29 (lam29 (app29 (app29 mul29 (suc29 v129)) v029)))
        (suc29 zero29))
{-# OPTIONS --type-in-type #-}

Ty30 : Set
Ty30 =
   (Ty30         : Set)
   (nat top bot  : Ty30)
   (arr prod sum : Ty30 → Ty30 → Ty30)
 → Ty30

nat30 : Ty30; nat30 = λ _ nat30 _ _ _ _ _ → nat30
top30 : Ty30; top30 = λ _ _ top30 _ _ _ _ → top30
bot30 : Ty30; bot30 = λ _ _ _ bot30 _ _ _ → bot30

arr30 : Ty30 → Ty30 → Ty30; arr30
 = λ A B Ty30 nat30 top30 bot30 arr30 prod sum →
     arr30 (A Ty30 nat30 top30 bot30 arr30 prod sum) (B Ty30 nat30 top30 bot30 arr30 prod sum)

prod30 : Ty30 → Ty30 → Ty30; prod30
 = λ A B Ty30 nat30 top30 bot30 arr30 prod30 sum →
     prod30 (A Ty30 nat30 top30 bot30 arr30 prod30 sum) (B Ty30 nat30 top30 bot30 arr30 prod30 sum)

sum30 : Ty30 → Ty30 → Ty30; sum30
 = λ A B Ty30 nat30 top30 bot30 arr30 prod30 sum30 →
     sum30 (A Ty30 nat30 top30 bot30 arr30 prod30 sum30) (B Ty30 nat30 top30 bot30 arr30 prod30 sum30)

Con30 : Set; Con30
 = (Con30 : Set)
   (nil  : Con30)
   (snoc : Con30 → Ty30 → Con30)
 → Con30

nil30 : Con30; nil30
 = λ Con30 nil30 snoc → nil30

snoc30 : Con30 → Ty30 → Con30; snoc30
 = λ Γ A Con30 nil30 snoc30 → snoc30 (Γ Con30 nil30 snoc30) A

Var30 : Con30 → Ty30 → Set; Var30
 = λ Γ A →
   (Var30 : Con30 → Ty30 → Set)
   (vz  : ∀{Γ A} → Var30 (snoc30 Γ A) A)
   (vs  : ∀{Γ B A} → Var30 Γ A → Var30 (snoc30 Γ B) A)
 → Var30 Γ A

vz30 : ∀{Γ A} → Var30 (snoc30 Γ A) A; vz30
 = λ Var30 vz30 vs → vz30

vs30 : ∀{Γ B A} → Var30 Γ A → Var30 (snoc30 Γ B) A; vs30
 = λ x Var30 vz30 vs30 → vs30 (x Var30 vz30 vs30)

Tm30 : Con30 → Ty30 → Set; Tm30
 = λ Γ A →
   (Tm30  : Con30 → Ty30 → Set)
   (var   : ∀{Γ A} → Var30 Γ A → Tm30 Γ A)
   (lam   : ∀{Γ A B} → Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B))
   (app   : ∀{Γ A B} → Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B)
   (tt    : ∀{Γ} → Tm30 Γ top30)
   (pair  : ∀{Γ A B} → Tm30 Γ A → Tm30 Γ B → Tm30 Γ (prod30 A B))
   (fst   : ∀{Γ A B} → Tm30 Γ (prod30 A B) → Tm30 Γ A)
   (snd   : ∀{Γ A B} → Tm30 Γ (prod30 A B) → Tm30 Γ B)
   (left  : ∀{Γ A B} → Tm30 Γ A → Tm30 Γ (sum30 A B))
   (right : ∀{Γ A B} → Tm30 Γ B → Tm30 Γ (sum30 A B))
   (case  : ∀{Γ A B C} → Tm30 Γ (sum30 A B) → Tm30 Γ (arr30 A C) → Tm30 Γ (arr30 B C) → Tm30 Γ C)
   (zero  : ∀{Γ} → Tm30 Γ nat30)
   (suc   : ∀{Γ} → Tm30 Γ nat30 → Tm30 Γ nat30)
   (rec   : ∀{Γ A} → Tm30 Γ nat30 → Tm30 Γ (arr30 nat30 (arr30 A A)) → Tm30 Γ A → Tm30 Γ A)
 → Tm30 Γ A

var30 : ∀{Γ A} → Var30 Γ A → Tm30 Γ A; var30
 = λ x Tm30 var30 lam app tt pair fst snd left right case zero suc rec →
     var30 x

lam30 : ∀{Γ A B} → Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B); lam30
 = λ t Tm30 var30 lam30 app tt pair fst snd left right case zero suc rec →
     lam30 (t Tm30 var30 lam30 app tt pair fst snd left right case zero suc rec)

app30 : ∀{Γ A B} → Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B; app30
 = λ t u Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec →
     app30 (t Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec)
         (u Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec)

tt30 : ∀{Γ} → Tm30 Γ top30; tt30
 = λ Tm30 var30 lam30 app30 tt30 pair fst snd left right case zero suc rec → tt30

pair30 : ∀{Γ A B} → Tm30 Γ A → Tm30 Γ B → Tm30 Γ (prod30 A B); pair30
 = λ t u Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec →
     pair30 (t Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec)
          (u Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec)

fst30 : ∀{Γ A B} → Tm30 Γ (prod30 A B) → Tm30 Γ A; fst30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd left right case zero suc rec →
     fst30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd left right case zero suc rec)

snd30 : ∀{Γ A B} → Tm30 Γ (prod30 A B) → Tm30 Γ B; snd30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left right case zero suc rec →
     snd30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left right case zero suc rec)

left30 : ∀{Γ A B} → Tm30 Γ A → Tm30 Γ (sum30 A B); left30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right case zero suc rec →
     left30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right case zero suc rec)

right30 : ∀{Γ A B} → Tm30 Γ B → Tm30 Γ (sum30 A B); right30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case zero suc rec →
     right30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case zero suc rec)

case30 : ∀{Γ A B C} → Tm30 Γ (sum30 A B) → Tm30 Γ (arr30 A C) → Tm30 Γ (arr30 B C) → Tm30 Γ C; case30
 = λ t u v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec →
     case30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)
           (u Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)
           (v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)

zero30  : ∀{Γ} → Tm30 Γ nat30; zero30
 = λ Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc rec → zero30

suc30 : ∀{Γ} → Tm30 Γ nat30 → Tm30 Γ nat30; suc30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec →
   suc30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec)

rec30 : ∀{Γ A} → Tm30 Γ nat30 → Tm30 Γ (arr30 nat30 (arr30 A A)) → Tm30 Γ A → Tm30 Γ A; rec30
 = λ t u v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30 →
     rec30 (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)
         (u Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)
         (v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)

v030 : ∀{Γ A} → Tm30 (snoc30 Γ A) A; v030
 = var30 vz30

v130 : ∀{Γ A B} → Tm30 (snoc30 (snoc30 Γ A) B) A; v130
 = var30 (vs30 vz30)

v230 : ∀{Γ A B C} → Tm30 (snoc30 (snoc30 (snoc30 Γ A) B) C) A; v230
 = var30 (vs30 (vs30 vz30))

v330 : ∀{Γ A B C D} → Tm30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) A; v330
 = var30 (vs30 (vs30 (vs30 vz30)))

tbool30 : Ty30; tbool30
 = sum30 top30 top30

true30 : ∀{Γ} → Tm30 Γ tbool30; true30
 = left30 tt30

tfalse30 : ∀{Γ} → Tm30 Γ tbool30; tfalse30
 = right30 tt30

ifthenelse30 : ∀{Γ A} → Tm30 Γ (arr30 tbool30 (arr30 A (arr30 A A))); ifthenelse30
 = lam30 (lam30 (lam30 (case30 v230 (lam30 v230) (lam30 v130))))

times430 : ∀{Γ A} → Tm30 Γ (arr30 (arr30 A A) (arr30 A A)); times430
  = lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030)))))

add30 : ∀{Γ} → Tm30 Γ (arr30 nat30 (arr30 nat30 nat30)); add30
 = lam30 (rec30 v030
       (lam30 (lam30 (lam30 (suc30 (app30 v130 v030)))))
       (lam30 v030))

mul30 : ∀{Γ} → Tm30 Γ (arr30 nat30 (arr30 nat30 nat30)); mul30
 = lam30 (rec30 v030
       (lam30 (lam30 (lam30 (app30 (app30 add30 (app30 v130 v030)) v030))))
       (lam30 zero30))

fact30 : ∀{Γ} → Tm30 Γ (arr30 nat30 nat30); fact30
 = lam30 (rec30 v030 (lam30 (lam30 (app30 (app30 mul30 (suc30 v130)) v030)))
        (suc30 zero30))
{-# OPTIONS --type-in-type #-}

Ty31 : Set
Ty31 =
   (Ty31         : Set)
   (nat top bot  : Ty31)
   (arr prod sum : Ty31 → Ty31 → Ty31)
 → Ty31

nat31 : Ty31; nat31 = λ _ nat31 _ _ _ _ _ → nat31
top31 : Ty31; top31 = λ _ _ top31 _ _ _ _ → top31
bot31 : Ty31; bot31 = λ _ _ _ bot31 _ _ _ → bot31

arr31 : Ty31 → Ty31 → Ty31; arr31
 = λ A B Ty31 nat31 top31 bot31 arr31 prod sum →
     arr31 (A Ty31 nat31 top31 bot31 arr31 prod sum) (B Ty31 nat31 top31 bot31 arr31 prod sum)

prod31 : Ty31 → Ty31 → Ty31; prod31
 = λ A B Ty31 nat31 top31 bot31 arr31 prod31 sum →
     prod31 (A Ty31 nat31 top31 bot31 arr31 prod31 sum) (B Ty31 nat31 top31 bot31 arr31 prod31 sum)

sum31 : Ty31 → Ty31 → Ty31; sum31
 = λ A B Ty31 nat31 top31 bot31 arr31 prod31 sum31 →
     sum31 (A Ty31 nat31 top31 bot31 arr31 prod31 sum31) (B Ty31 nat31 top31 bot31 arr31 prod31 sum31)

Con31 : Set; Con31
 = (Con31 : Set)
   (nil  : Con31)
   (snoc : Con31 → Ty31 → Con31)
 → Con31

nil31 : Con31; nil31
 = λ Con31 nil31 snoc → nil31

snoc31 : Con31 → Ty31 → Con31; snoc31
 = λ Γ A Con31 nil31 snoc31 → snoc31 (Γ Con31 nil31 snoc31) A

Var31 : Con31 → Ty31 → Set; Var31
 = λ Γ A →
   (Var31 : Con31 → Ty31 → Set)
   (vz  : ∀{Γ A} → Var31 (snoc31 Γ A) A)
   (vs  : ∀{Γ B A} → Var31 Γ A → Var31 (snoc31 Γ B) A)
 → Var31 Γ A

vz31 : ∀{Γ A} → Var31 (snoc31 Γ A) A; vz31
 = λ Var31 vz31 vs → vz31

vs31 : ∀{Γ B A} → Var31 Γ A → Var31 (snoc31 Γ B) A; vs31
 = λ x Var31 vz31 vs31 → vs31 (x Var31 vz31 vs31)

Tm31 : Con31 → Ty31 → Set; Tm31
 = λ Γ A →
   (Tm31  : Con31 → Ty31 → Set)
   (var   : ∀{Γ A} → Var31 Γ A → Tm31 Γ A)
   (lam   : ∀{Γ A B} → Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B))
   (app   : ∀{Γ A B} → Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B)
   (tt    : ∀{Γ} → Tm31 Γ top31)
   (pair  : ∀{Γ A B} → Tm31 Γ A → Tm31 Γ B → Tm31 Γ (prod31 A B))
   (fst   : ∀{Γ A B} → Tm31 Γ (prod31 A B) → Tm31 Γ A)
   (snd   : ∀{Γ A B} → Tm31 Γ (prod31 A B) → Tm31 Γ B)
   (left  : ∀{Γ A B} → Tm31 Γ A → Tm31 Γ (sum31 A B))
   (right : ∀{Γ A B} → Tm31 Γ B → Tm31 Γ (sum31 A B))
   (case  : ∀{Γ A B C} → Tm31 Γ (sum31 A B) → Tm31 Γ (arr31 A C) → Tm31 Γ (arr31 B C) → Tm31 Γ C)
   (zero  : ∀{Γ} → Tm31 Γ nat31)
   (suc   : ∀{Γ} → Tm31 Γ nat31 → Tm31 Γ nat31)
   (rec   : ∀{Γ A} → Tm31 Γ nat31 → Tm31 Γ (arr31 nat31 (arr31 A A)) → Tm31 Γ A → Tm31 Γ A)
 → Tm31 Γ A

var31 : ∀{Γ A} → Var31 Γ A → Tm31 Γ A; var31
 = λ x Tm31 var31 lam app tt pair fst snd left right case zero suc rec →
     var31 x

lam31 : ∀{Γ A B} → Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B); lam31
 = λ t Tm31 var31 lam31 app tt pair fst snd left right case zero suc rec →
     lam31 (t Tm31 var31 lam31 app tt pair fst snd left right case zero suc rec)

app31 : ∀{Γ A B} → Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B; app31
 = λ t u Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec →
     app31 (t Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec)
         (u Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec)

tt31 : ∀{Γ} → Tm31 Γ top31; tt31
 = λ Tm31 var31 lam31 app31 tt31 pair fst snd left right case zero suc rec → tt31

pair31 : ∀{Γ A B} → Tm31 Γ A → Tm31 Γ B → Tm31 Γ (prod31 A B); pair31
 = λ t u Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec →
     pair31 (t Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec)
          (u Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec)

fst31 : ∀{Γ A B} → Tm31 Γ (prod31 A B) → Tm31 Γ A; fst31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd left right case zero suc rec →
     fst31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd left right case zero suc rec)

snd31 : ∀{Γ A B} → Tm31 Γ (prod31 A B) → Tm31 Γ B; snd31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left right case zero suc rec →
     snd31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left right case zero suc rec)

left31 : ∀{Γ A B} → Tm31 Γ A → Tm31 Γ (sum31 A B); left31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right case zero suc rec →
     left31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right case zero suc rec)

right31 : ∀{Γ A B} → Tm31 Γ B → Tm31 Γ (sum31 A B); right31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case zero suc rec →
     right31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case zero suc rec)

case31 : ∀{Γ A B C} → Tm31 Γ (sum31 A B) → Tm31 Γ (arr31 A C) → Tm31 Γ (arr31 B C) → Tm31 Γ C; case31
 = λ t u v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec →
     case31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)
           (u Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)
           (v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)

zero31  : ∀{Γ} → Tm31 Γ nat31; zero31
 = λ Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc rec → zero31

suc31 : ∀{Γ} → Tm31 Γ nat31 → Tm31 Γ nat31; suc31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec →
   suc31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec)

rec31 : ∀{Γ A} → Tm31 Γ nat31 → Tm31 Γ (arr31 nat31 (arr31 A A)) → Tm31 Γ A → Tm31 Γ A; rec31
 = λ t u v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31 →
     rec31 (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)
         (u Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)
         (v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)

v031 : ∀{Γ A} → Tm31 (snoc31 Γ A) A; v031
 = var31 vz31

v131 : ∀{Γ A B} → Tm31 (snoc31 (snoc31 Γ A) B) A; v131
 = var31 (vs31 vz31)

v231 : ∀{Γ A B C} → Tm31 (snoc31 (snoc31 (snoc31 Γ A) B) C) A; v231
 = var31 (vs31 (vs31 vz31))

v331 : ∀{Γ A B C D} → Tm31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) A; v331
 = var31 (vs31 (vs31 (vs31 vz31)))

tbool31 : Ty31; tbool31
 = sum31 top31 top31

true31 : ∀{Γ} → Tm31 Γ tbool31; true31
 = left31 tt31

tfalse31 : ∀{Γ} → Tm31 Γ tbool31; tfalse31
 = right31 tt31

ifthenelse31 : ∀{Γ A} → Tm31 Γ (arr31 tbool31 (arr31 A (arr31 A A))); ifthenelse31
 = lam31 (lam31 (lam31 (case31 v231 (lam31 v231) (lam31 v131))))

times431 : ∀{Γ A} → Tm31 Γ (arr31 (arr31 A A) (arr31 A A)); times431
  = lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031)))))

add31 : ∀{Γ} → Tm31 Γ (arr31 nat31 (arr31 nat31 nat31)); add31
 = lam31 (rec31 v031
       (lam31 (lam31 (lam31 (suc31 (app31 v131 v031)))))
       (lam31 v031))

mul31 : ∀{Γ} → Tm31 Γ (arr31 nat31 (arr31 nat31 nat31)); mul31
 = lam31 (rec31 v031
       (lam31 (lam31 (lam31 (app31 (app31 add31 (app31 v131 v031)) v031))))
       (lam31 zero31))

fact31 : ∀{Γ} → Tm31 Γ (arr31 nat31 nat31); fact31
 = lam31 (rec31 v031 (lam31 (lam31 (app31 (app31 mul31 (suc31 v131)) v031)))
        (suc31 zero31))
{-# OPTIONS --type-in-type #-}

Ty32 : Set
Ty32 =
   (Ty32         : Set)
   (nat top bot  : Ty32)
   (arr prod sum : Ty32 → Ty32 → Ty32)
 → Ty32

nat32 : Ty32; nat32 = λ _ nat32 _ _ _ _ _ → nat32
top32 : Ty32; top32 = λ _ _ top32 _ _ _ _ → top32
bot32 : Ty32; bot32 = λ _ _ _ bot32 _ _ _ → bot32

arr32 : Ty32 → Ty32 → Ty32; arr32
 = λ A B Ty32 nat32 top32 bot32 arr32 prod sum →
     arr32 (A Ty32 nat32 top32 bot32 arr32 prod sum) (B Ty32 nat32 top32 bot32 arr32 prod sum)

prod32 : Ty32 → Ty32 → Ty32; prod32
 = λ A B Ty32 nat32 top32 bot32 arr32 prod32 sum →
     prod32 (A Ty32 nat32 top32 bot32 arr32 prod32 sum) (B Ty32 nat32 top32 bot32 arr32 prod32 sum)

sum32 : Ty32 → Ty32 → Ty32; sum32
 = λ A B Ty32 nat32 top32 bot32 arr32 prod32 sum32 →
     sum32 (A Ty32 nat32 top32 bot32 arr32 prod32 sum32) (B Ty32 nat32 top32 bot32 arr32 prod32 sum32)

Con32 : Set; Con32
 = (Con32 : Set)
   (nil  : Con32)
   (snoc : Con32 → Ty32 → Con32)
 → Con32

nil32 : Con32; nil32
 = λ Con32 nil32 snoc → nil32

snoc32 : Con32 → Ty32 → Con32; snoc32
 = λ Γ A Con32 nil32 snoc32 → snoc32 (Γ Con32 nil32 snoc32) A

Var32 : Con32 → Ty32 → Set; Var32
 = λ Γ A →
   (Var32 : Con32 → Ty32 → Set)
   (vz  : ∀{Γ A} → Var32 (snoc32 Γ A) A)
   (vs  : ∀{Γ B A} → Var32 Γ A → Var32 (snoc32 Γ B) A)
 → Var32 Γ A

vz32 : ∀{Γ A} → Var32 (snoc32 Γ A) A; vz32
 = λ Var32 vz32 vs → vz32

vs32 : ∀{Γ B A} → Var32 Γ A → Var32 (snoc32 Γ B) A; vs32
 = λ x Var32 vz32 vs32 → vs32 (x Var32 vz32 vs32)

Tm32 : Con32 → Ty32 → Set; Tm32
 = λ Γ A →
   (Tm32  : Con32 → Ty32 → Set)
   (var   : ∀{Γ A} → Var32 Γ A → Tm32 Γ A)
   (lam   : ∀{Γ A B} → Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B))
   (app   : ∀{Γ A B} → Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B)
   (tt    : ∀{Γ} → Tm32 Γ top32)
   (pair  : ∀{Γ A B} → Tm32 Γ A → Tm32 Γ B → Tm32 Γ (prod32 A B))
   (fst   : ∀{Γ A B} → Tm32 Γ (prod32 A B) → Tm32 Γ A)
   (snd   : ∀{Γ A B} → Tm32 Γ (prod32 A B) → Tm32 Γ B)
   (left  : ∀{Γ A B} → Tm32 Γ A → Tm32 Γ (sum32 A B))
   (right : ∀{Γ A B} → Tm32 Γ B → Tm32 Γ (sum32 A B))
   (case  : ∀{Γ A B C} → Tm32 Γ (sum32 A B) → Tm32 Γ (arr32 A C) → Tm32 Γ (arr32 B C) → Tm32 Γ C)
   (zero  : ∀{Γ} → Tm32 Γ nat32)
   (suc   : ∀{Γ} → Tm32 Γ nat32 → Tm32 Γ nat32)
   (rec   : ∀{Γ A} → Tm32 Γ nat32 → Tm32 Γ (arr32 nat32 (arr32 A A)) → Tm32 Γ A → Tm32 Γ A)
 → Tm32 Γ A

var32 : ∀{Γ A} → Var32 Γ A → Tm32 Γ A; var32
 = λ x Tm32 var32 lam app tt pair fst snd left right case zero suc rec →
     var32 x

lam32 : ∀{Γ A B} → Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B); lam32
 = λ t Tm32 var32 lam32 app tt pair fst snd left right case zero suc rec →
     lam32 (t Tm32 var32 lam32 app tt pair fst snd left right case zero suc rec)

app32 : ∀{Γ A B} → Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B; app32
 = λ t u Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec →
     app32 (t Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec)
         (u Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec)

tt32 : ∀{Γ} → Tm32 Γ top32; tt32
 = λ Tm32 var32 lam32 app32 tt32 pair fst snd left right case zero suc rec → tt32

pair32 : ∀{Γ A B} → Tm32 Γ A → Tm32 Γ B → Tm32 Γ (prod32 A B); pair32
 = λ t u Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec →
     pair32 (t Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec)
          (u Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec)

fst32 : ∀{Γ A B} → Tm32 Γ (prod32 A B) → Tm32 Γ A; fst32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd left right case zero suc rec →
     fst32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd left right case zero suc rec)

snd32 : ∀{Γ A B} → Tm32 Γ (prod32 A B) → Tm32 Γ B; snd32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left right case zero suc rec →
     snd32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left right case zero suc rec)

left32 : ∀{Γ A B} → Tm32 Γ A → Tm32 Γ (sum32 A B); left32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right case zero suc rec →
     left32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right case zero suc rec)

right32 : ∀{Γ A B} → Tm32 Γ B → Tm32 Γ (sum32 A B); right32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case zero suc rec →
     right32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case zero suc rec)

case32 : ∀{Γ A B C} → Tm32 Γ (sum32 A B) → Tm32 Γ (arr32 A C) → Tm32 Γ (arr32 B C) → Tm32 Γ C; case32
 = λ t u v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec →
     case32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)
           (u Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)
           (v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)

zero32  : ∀{Γ} → Tm32 Γ nat32; zero32
 = λ Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc rec → zero32

suc32 : ∀{Γ} → Tm32 Γ nat32 → Tm32 Γ nat32; suc32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec →
   suc32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec)

rec32 : ∀{Γ A} → Tm32 Γ nat32 → Tm32 Γ (arr32 nat32 (arr32 A A)) → Tm32 Γ A → Tm32 Γ A; rec32
 = λ t u v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32 →
     rec32 (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)
         (u Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)
         (v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)

v032 : ∀{Γ A} → Tm32 (snoc32 Γ A) A; v032
 = var32 vz32

v132 : ∀{Γ A B} → Tm32 (snoc32 (snoc32 Γ A) B) A; v132
 = var32 (vs32 vz32)

v232 : ∀{Γ A B C} → Tm32 (snoc32 (snoc32 (snoc32 Γ A) B) C) A; v232
 = var32 (vs32 (vs32 vz32))

v332 : ∀{Γ A B C D} → Tm32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) A; v332
 = var32 (vs32 (vs32 (vs32 vz32)))

tbool32 : Ty32; tbool32
 = sum32 top32 top32

true32 : ∀{Γ} → Tm32 Γ tbool32; true32
 = left32 tt32

tfalse32 : ∀{Γ} → Tm32 Γ tbool32; tfalse32
 = right32 tt32

ifthenelse32 : ∀{Γ A} → Tm32 Γ (arr32 tbool32 (arr32 A (arr32 A A))); ifthenelse32
 = lam32 (lam32 (lam32 (case32 v232 (lam32 v232) (lam32 v132))))

times432 : ∀{Γ A} → Tm32 Γ (arr32 (arr32 A A) (arr32 A A)); times432
  = lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032)))))

add32 : ∀{Γ} → Tm32 Γ (arr32 nat32 (arr32 nat32 nat32)); add32
 = lam32 (rec32 v032
       (lam32 (lam32 (lam32 (suc32 (app32 v132 v032)))))
       (lam32 v032))

mul32 : ∀{Γ} → Tm32 Γ (arr32 nat32 (arr32 nat32 nat32)); mul32
 = lam32 (rec32 v032
       (lam32 (lam32 (lam32 (app32 (app32 add32 (app32 v132 v032)) v032))))
       (lam32 zero32))

fact32 : ∀{Γ} → Tm32 Γ (arr32 nat32 nat32); fact32
 = lam32 (rec32 v032 (lam32 (lam32 (app32 (app32 mul32 (suc32 v132)) v032)))
        (suc32 zero32))
{-# OPTIONS --type-in-type #-}

Ty33 : Set
Ty33 =
   (Ty33         : Set)
   (nat top bot  : Ty33)
   (arr prod sum : Ty33 → Ty33 → Ty33)
 → Ty33

nat33 : Ty33; nat33 = λ _ nat33 _ _ _ _ _ → nat33
top33 : Ty33; top33 = λ _ _ top33 _ _ _ _ → top33
bot33 : Ty33; bot33 = λ _ _ _ bot33 _ _ _ → bot33

arr33 : Ty33 → Ty33 → Ty33; arr33
 = λ A B Ty33 nat33 top33 bot33 arr33 prod sum →
     arr33 (A Ty33 nat33 top33 bot33 arr33 prod sum) (B Ty33 nat33 top33 bot33 arr33 prod sum)

prod33 : Ty33 → Ty33 → Ty33; prod33
 = λ A B Ty33 nat33 top33 bot33 arr33 prod33 sum →
     prod33 (A Ty33 nat33 top33 bot33 arr33 prod33 sum) (B Ty33 nat33 top33 bot33 arr33 prod33 sum)

sum33 : Ty33 → Ty33 → Ty33; sum33
 = λ A B Ty33 nat33 top33 bot33 arr33 prod33 sum33 →
     sum33 (A Ty33 nat33 top33 bot33 arr33 prod33 sum33) (B Ty33 nat33 top33 bot33 arr33 prod33 sum33)

Con33 : Set; Con33
 = (Con33 : Set)
   (nil  : Con33)
   (snoc : Con33 → Ty33 → Con33)
 → Con33

nil33 : Con33; nil33
 = λ Con33 nil33 snoc → nil33

snoc33 : Con33 → Ty33 → Con33; snoc33
 = λ Γ A Con33 nil33 snoc33 → snoc33 (Γ Con33 nil33 snoc33) A

Var33 : Con33 → Ty33 → Set; Var33
 = λ Γ A →
   (Var33 : Con33 → Ty33 → Set)
   (vz  : ∀{Γ A} → Var33 (snoc33 Γ A) A)
   (vs  : ∀{Γ B A} → Var33 Γ A → Var33 (snoc33 Γ B) A)
 → Var33 Γ A

vz33 : ∀{Γ A} → Var33 (snoc33 Γ A) A; vz33
 = λ Var33 vz33 vs → vz33

vs33 : ∀{Γ B A} → Var33 Γ A → Var33 (snoc33 Γ B) A; vs33
 = λ x Var33 vz33 vs33 → vs33 (x Var33 vz33 vs33)

Tm33 : Con33 → Ty33 → Set; Tm33
 = λ Γ A →
   (Tm33  : Con33 → Ty33 → Set)
   (var   : ∀{Γ A} → Var33 Γ A → Tm33 Γ A)
   (lam   : ∀{Γ A B} → Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B))
   (app   : ∀{Γ A B} → Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B)
   (tt    : ∀{Γ} → Tm33 Γ top33)
   (pair  : ∀{Γ A B} → Tm33 Γ A → Tm33 Γ B → Tm33 Γ (prod33 A B))
   (fst   : ∀{Γ A B} → Tm33 Γ (prod33 A B) → Tm33 Γ A)
   (snd   : ∀{Γ A B} → Tm33 Γ (prod33 A B) → Tm33 Γ B)
   (left  : ∀{Γ A B} → Tm33 Γ A → Tm33 Γ (sum33 A B))
   (right : ∀{Γ A B} → Tm33 Γ B → Tm33 Γ (sum33 A B))
   (case  : ∀{Γ A B C} → Tm33 Γ (sum33 A B) → Tm33 Γ (arr33 A C) → Tm33 Γ (arr33 B C) → Tm33 Γ C)
   (zero  : ∀{Γ} → Tm33 Γ nat33)
   (suc   : ∀{Γ} → Tm33 Γ nat33 → Tm33 Γ nat33)
   (rec   : ∀{Γ A} → Tm33 Γ nat33 → Tm33 Γ (arr33 nat33 (arr33 A A)) → Tm33 Γ A → Tm33 Γ A)
 → Tm33 Γ A

var33 : ∀{Γ A} → Var33 Γ A → Tm33 Γ A; var33
 = λ x Tm33 var33 lam app tt pair fst snd left right case zero suc rec →
     var33 x

lam33 : ∀{Γ A B} → Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B); lam33
 = λ t Tm33 var33 lam33 app tt pair fst snd left right case zero suc rec →
     lam33 (t Tm33 var33 lam33 app tt pair fst snd left right case zero suc rec)

app33 : ∀{Γ A B} → Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B; app33
 = λ t u Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec →
     app33 (t Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec)
         (u Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec)

tt33 : ∀{Γ} → Tm33 Γ top33; tt33
 = λ Tm33 var33 lam33 app33 tt33 pair fst snd left right case zero suc rec → tt33

pair33 : ∀{Γ A B} → Tm33 Γ A → Tm33 Γ B → Tm33 Γ (prod33 A B); pair33
 = λ t u Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec →
     pair33 (t Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec)
          (u Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec)

fst33 : ∀{Γ A B} → Tm33 Γ (prod33 A B) → Tm33 Γ A; fst33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd left right case zero suc rec →
     fst33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd left right case zero suc rec)

snd33 : ∀{Γ A B} → Tm33 Γ (prod33 A B) → Tm33 Γ B; snd33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left right case zero suc rec →
     snd33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left right case zero suc rec)

left33 : ∀{Γ A B} → Tm33 Γ A → Tm33 Γ (sum33 A B); left33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right case zero suc rec →
     left33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right case zero suc rec)

right33 : ∀{Γ A B} → Tm33 Γ B → Tm33 Γ (sum33 A B); right33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case zero suc rec →
     right33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case zero suc rec)

case33 : ∀{Γ A B C} → Tm33 Γ (sum33 A B) → Tm33 Γ (arr33 A C) → Tm33 Γ (arr33 B C) → Tm33 Γ C; case33
 = λ t u v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec →
     case33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)
           (u Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)
           (v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)

zero33  : ∀{Γ} → Tm33 Γ nat33; zero33
 = λ Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc rec → zero33

suc33 : ∀{Γ} → Tm33 Γ nat33 → Tm33 Γ nat33; suc33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec →
   suc33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec)

rec33 : ∀{Γ A} → Tm33 Γ nat33 → Tm33 Γ (arr33 nat33 (arr33 A A)) → Tm33 Γ A → Tm33 Γ A; rec33
 = λ t u v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33 →
     rec33 (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)
         (u Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)
         (v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)

v033 : ∀{Γ A} → Tm33 (snoc33 Γ A) A; v033
 = var33 vz33

v133 : ∀{Γ A B} → Tm33 (snoc33 (snoc33 Γ A) B) A; v133
 = var33 (vs33 vz33)

v233 : ∀{Γ A B C} → Tm33 (snoc33 (snoc33 (snoc33 Γ A) B) C) A; v233
 = var33 (vs33 (vs33 vz33))

v333 : ∀{Γ A B C D} → Tm33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) A; v333
 = var33 (vs33 (vs33 (vs33 vz33)))

tbool33 : Ty33; tbool33
 = sum33 top33 top33

true33 : ∀{Γ} → Tm33 Γ tbool33; true33
 = left33 tt33

tfalse33 : ∀{Γ} → Tm33 Γ tbool33; tfalse33
 = right33 tt33

ifthenelse33 : ∀{Γ A} → Tm33 Γ (arr33 tbool33 (arr33 A (arr33 A A))); ifthenelse33
 = lam33 (lam33 (lam33 (case33 v233 (lam33 v233) (lam33 v133))))

times433 : ∀{Γ A} → Tm33 Γ (arr33 (arr33 A A) (arr33 A A)); times433
  = lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033)))))

add33 : ∀{Γ} → Tm33 Γ (arr33 nat33 (arr33 nat33 nat33)); add33
 = lam33 (rec33 v033
       (lam33 (lam33 (lam33 (suc33 (app33 v133 v033)))))
       (lam33 v033))

mul33 : ∀{Γ} → Tm33 Γ (arr33 nat33 (arr33 nat33 nat33)); mul33
 = lam33 (rec33 v033
       (lam33 (lam33 (lam33 (app33 (app33 add33 (app33 v133 v033)) v033))))
       (lam33 zero33))

fact33 : ∀{Γ} → Tm33 Γ (arr33 nat33 nat33); fact33
 = lam33 (rec33 v033 (lam33 (lam33 (app33 (app33 mul33 (suc33 v133)) v033)))
        (suc33 zero33))
{-# OPTIONS --type-in-type #-}

Ty34 : Set
Ty34 =
   (Ty34         : Set)
   (nat top bot  : Ty34)
   (arr prod sum : Ty34 → Ty34 → Ty34)
 → Ty34

nat34 : Ty34; nat34 = λ _ nat34 _ _ _ _ _ → nat34
top34 : Ty34; top34 = λ _ _ top34 _ _ _ _ → top34
bot34 : Ty34; bot34 = λ _ _ _ bot34 _ _ _ → bot34

arr34 : Ty34 → Ty34 → Ty34; arr34
 = λ A B Ty34 nat34 top34 bot34 arr34 prod sum →
     arr34 (A Ty34 nat34 top34 bot34 arr34 prod sum) (B Ty34 nat34 top34 bot34 arr34 prod sum)

prod34 : Ty34 → Ty34 → Ty34; prod34
 = λ A B Ty34 nat34 top34 bot34 arr34 prod34 sum →
     prod34 (A Ty34 nat34 top34 bot34 arr34 prod34 sum) (B Ty34 nat34 top34 bot34 arr34 prod34 sum)

sum34 : Ty34 → Ty34 → Ty34; sum34
 = λ A B Ty34 nat34 top34 bot34 arr34 prod34 sum34 →
     sum34 (A Ty34 nat34 top34 bot34 arr34 prod34 sum34) (B Ty34 nat34 top34 bot34 arr34 prod34 sum34)

Con34 : Set; Con34
 = (Con34 : Set)
   (nil  : Con34)
   (snoc : Con34 → Ty34 → Con34)
 → Con34

nil34 : Con34; nil34
 = λ Con34 nil34 snoc → nil34

snoc34 : Con34 → Ty34 → Con34; snoc34
 = λ Γ A Con34 nil34 snoc34 → snoc34 (Γ Con34 nil34 snoc34) A

Var34 : Con34 → Ty34 → Set; Var34
 = λ Γ A →
   (Var34 : Con34 → Ty34 → Set)
   (vz  : ∀{Γ A} → Var34 (snoc34 Γ A) A)
   (vs  : ∀{Γ B A} → Var34 Γ A → Var34 (snoc34 Γ B) A)
 → Var34 Γ A

vz34 : ∀{Γ A} → Var34 (snoc34 Γ A) A; vz34
 = λ Var34 vz34 vs → vz34

vs34 : ∀{Γ B A} → Var34 Γ A → Var34 (snoc34 Γ B) A; vs34
 = λ x Var34 vz34 vs34 → vs34 (x Var34 vz34 vs34)

Tm34 : Con34 → Ty34 → Set; Tm34
 = λ Γ A →
   (Tm34  : Con34 → Ty34 → Set)
   (var   : ∀{Γ A} → Var34 Γ A → Tm34 Γ A)
   (lam   : ∀{Γ A B} → Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B))
   (app   : ∀{Γ A B} → Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B)
   (tt    : ∀{Γ} → Tm34 Γ top34)
   (pair  : ∀{Γ A B} → Tm34 Γ A → Tm34 Γ B → Tm34 Γ (prod34 A B))
   (fst   : ∀{Γ A B} → Tm34 Γ (prod34 A B) → Tm34 Γ A)
   (snd   : ∀{Γ A B} → Tm34 Γ (prod34 A B) → Tm34 Γ B)
   (left  : ∀{Γ A B} → Tm34 Γ A → Tm34 Γ (sum34 A B))
   (right : ∀{Γ A B} → Tm34 Γ B → Tm34 Γ (sum34 A B))
   (case  : ∀{Γ A B C} → Tm34 Γ (sum34 A B) → Tm34 Γ (arr34 A C) → Tm34 Γ (arr34 B C) → Tm34 Γ C)
   (zero  : ∀{Γ} → Tm34 Γ nat34)
   (suc   : ∀{Γ} → Tm34 Γ nat34 → Tm34 Γ nat34)
   (rec   : ∀{Γ A} → Tm34 Γ nat34 → Tm34 Γ (arr34 nat34 (arr34 A A)) → Tm34 Γ A → Tm34 Γ A)
 → Tm34 Γ A

var34 : ∀{Γ A} → Var34 Γ A → Tm34 Γ A; var34
 = λ x Tm34 var34 lam app tt pair fst snd left right case zero suc rec →
     var34 x

lam34 : ∀{Γ A B} → Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B); lam34
 = λ t Tm34 var34 lam34 app tt pair fst snd left right case zero suc rec →
     lam34 (t Tm34 var34 lam34 app tt pair fst snd left right case zero suc rec)

app34 : ∀{Γ A B} → Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B; app34
 = λ t u Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec →
     app34 (t Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec)
         (u Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec)

tt34 : ∀{Γ} → Tm34 Γ top34; tt34
 = λ Tm34 var34 lam34 app34 tt34 pair fst snd left right case zero suc rec → tt34

pair34 : ∀{Γ A B} → Tm34 Γ A → Tm34 Γ B → Tm34 Γ (prod34 A B); pair34
 = λ t u Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec →
     pair34 (t Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec)
          (u Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec)

fst34 : ∀{Γ A B} → Tm34 Γ (prod34 A B) → Tm34 Γ A; fst34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd left right case zero suc rec →
     fst34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd left right case zero suc rec)

snd34 : ∀{Γ A B} → Tm34 Γ (prod34 A B) → Tm34 Γ B; snd34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left right case zero suc rec →
     snd34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left right case zero suc rec)

left34 : ∀{Γ A B} → Tm34 Γ A → Tm34 Γ (sum34 A B); left34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right case zero suc rec →
     left34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right case zero suc rec)

right34 : ∀{Γ A B} → Tm34 Γ B → Tm34 Γ (sum34 A B); right34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case zero suc rec →
     right34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case zero suc rec)

case34 : ∀{Γ A B C} → Tm34 Γ (sum34 A B) → Tm34 Γ (arr34 A C) → Tm34 Γ (arr34 B C) → Tm34 Γ C; case34
 = λ t u v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec →
     case34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)
           (u Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)
           (v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)

zero34  : ∀{Γ} → Tm34 Γ nat34; zero34
 = λ Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc rec → zero34

suc34 : ∀{Γ} → Tm34 Γ nat34 → Tm34 Γ nat34; suc34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec →
   suc34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec)

rec34 : ∀{Γ A} → Tm34 Γ nat34 → Tm34 Γ (arr34 nat34 (arr34 A A)) → Tm34 Γ A → Tm34 Γ A; rec34
 = λ t u v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34 →
     rec34 (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)
         (u Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)
         (v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)

v034 : ∀{Γ A} → Tm34 (snoc34 Γ A) A; v034
 = var34 vz34

v134 : ∀{Γ A B} → Tm34 (snoc34 (snoc34 Γ A) B) A; v134
 = var34 (vs34 vz34)

v234 : ∀{Γ A B C} → Tm34 (snoc34 (snoc34 (snoc34 Γ A) B) C) A; v234
 = var34 (vs34 (vs34 vz34))

v334 : ∀{Γ A B C D} → Tm34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) A; v334
 = var34 (vs34 (vs34 (vs34 vz34)))

tbool34 : Ty34; tbool34
 = sum34 top34 top34

true34 : ∀{Γ} → Tm34 Γ tbool34; true34
 = left34 tt34

tfalse34 : ∀{Γ} → Tm34 Γ tbool34; tfalse34
 = right34 tt34

ifthenelse34 : ∀{Γ A} → Tm34 Γ (arr34 tbool34 (arr34 A (arr34 A A))); ifthenelse34
 = lam34 (lam34 (lam34 (case34 v234 (lam34 v234) (lam34 v134))))

times434 : ∀{Γ A} → Tm34 Γ (arr34 (arr34 A A) (arr34 A A)); times434
  = lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034)))))

add34 : ∀{Γ} → Tm34 Γ (arr34 nat34 (arr34 nat34 nat34)); add34
 = lam34 (rec34 v034
       (lam34 (lam34 (lam34 (suc34 (app34 v134 v034)))))
       (lam34 v034))

mul34 : ∀{Γ} → Tm34 Γ (arr34 nat34 (arr34 nat34 nat34)); mul34
 = lam34 (rec34 v034
       (lam34 (lam34 (lam34 (app34 (app34 add34 (app34 v134 v034)) v034))))
       (lam34 zero34))

fact34 : ∀{Γ} → Tm34 Γ (arr34 nat34 nat34); fact34
 = lam34 (rec34 v034 (lam34 (lam34 (app34 (app34 mul34 (suc34 v134)) v034)))
        (suc34 zero34))
{-# OPTIONS --type-in-type #-}

Ty35 : Set
Ty35 =
   (Ty35         : Set)
   (nat top bot  : Ty35)
   (arr prod sum : Ty35 → Ty35 → Ty35)
 → Ty35

nat35 : Ty35; nat35 = λ _ nat35 _ _ _ _ _ → nat35
top35 : Ty35; top35 = λ _ _ top35 _ _ _ _ → top35
bot35 : Ty35; bot35 = λ _ _ _ bot35 _ _ _ → bot35

arr35 : Ty35 → Ty35 → Ty35; arr35
 = λ A B Ty35 nat35 top35 bot35 arr35 prod sum →
     arr35 (A Ty35 nat35 top35 bot35 arr35 prod sum) (B Ty35 nat35 top35 bot35 arr35 prod sum)

prod35 : Ty35 → Ty35 → Ty35; prod35
 = λ A B Ty35 nat35 top35 bot35 arr35 prod35 sum →
     prod35 (A Ty35 nat35 top35 bot35 arr35 prod35 sum) (B Ty35 nat35 top35 bot35 arr35 prod35 sum)

sum35 : Ty35 → Ty35 → Ty35; sum35
 = λ A B Ty35 nat35 top35 bot35 arr35 prod35 sum35 →
     sum35 (A Ty35 nat35 top35 bot35 arr35 prod35 sum35) (B Ty35 nat35 top35 bot35 arr35 prod35 sum35)

Con35 : Set; Con35
 = (Con35 : Set)
   (nil  : Con35)
   (snoc : Con35 → Ty35 → Con35)
 → Con35

nil35 : Con35; nil35
 = λ Con35 nil35 snoc → nil35

snoc35 : Con35 → Ty35 → Con35; snoc35
 = λ Γ A Con35 nil35 snoc35 → snoc35 (Γ Con35 nil35 snoc35) A

Var35 : Con35 → Ty35 → Set; Var35
 = λ Γ A →
   (Var35 : Con35 → Ty35 → Set)
   (vz  : ∀{Γ A} → Var35 (snoc35 Γ A) A)
   (vs  : ∀{Γ B A} → Var35 Γ A → Var35 (snoc35 Γ B) A)
 → Var35 Γ A

vz35 : ∀{Γ A} → Var35 (snoc35 Γ A) A; vz35
 = λ Var35 vz35 vs → vz35

vs35 : ∀{Γ B A} → Var35 Γ A → Var35 (snoc35 Γ B) A; vs35
 = λ x Var35 vz35 vs35 → vs35 (x Var35 vz35 vs35)

Tm35 : Con35 → Ty35 → Set; Tm35
 = λ Γ A →
   (Tm35  : Con35 → Ty35 → Set)
   (var   : ∀{Γ A} → Var35 Γ A → Tm35 Γ A)
   (lam   : ∀{Γ A B} → Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B))
   (app   : ∀{Γ A B} → Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B)
   (tt    : ∀{Γ} → Tm35 Γ top35)
   (pair  : ∀{Γ A B} → Tm35 Γ A → Tm35 Γ B → Tm35 Γ (prod35 A B))
   (fst   : ∀{Γ A B} → Tm35 Γ (prod35 A B) → Tm35 Γ A)
   (snd   : ∀{Γ A B} → Tm35 Γ (prod35 A B) → Tm35 Γ B)
   (left  : ∀{Γ A B} → Tm35 Γ A → Tm35 Γ (sum35 A B))
   (right : ∀{Γ A B} → Tm35 Γ B → Tm35 Γ (sum35 A B))
   (case  : ∀{Γ A B C} → Tm35 Γ (sum35 A B) → Tm35 Γ (arr35 A C) → Tm35 Γ (arr35 B C) → Tm35 Γ C)
   (zero  : ∀{Γ} → Tm35 Γ nat35)
   (suc   : ∀{Γ} → Tm35 Γ nat35 → Tm35 Γ nat35)
   (rec   : ∀{Γ A} → Tm35 Γ nat35 → Tm35 Γ (arr35 nat35 (arr35 A A)) → Tm35 Γ A → Tm35 Γ A)
 → Tm35 Γ A

var35 : ∀{Γ A} → Var35 Γ A → Tm35 Γ A; var35
 = λ x Tm35 var35 lam app tt pair fst snd left right case zero suc rec →
     var35 x

lam35 : ∀{Γ A B} → Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B); lam35
 = λ t Tm35 var35 lam35 app tt pair fst snd left right case zero suc rec →
     lam35 (t Tm35 var35 lam35 app tt pair fst snd left right case zero suc rec)

app35 : ∀{Γ A B} → Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B; app35
 = λ t u Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec →
     app35 (t Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec)
         (u Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec)

tt35 : ∀{Γ} → Tm35 Γ top35; tt35
 = λ Tm35 var35 lam35 app35 tt35 pair fst snd left right case zero suc rec → tt35

pair35 : ∀{Γ A B} → Tm35 Γ A → Tm35 Γ B → Tm35 Γ (prod35 A B); pair35
 = λ t u Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec →
     pair35 (t Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec)
          (u Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec)

fst35 : ∀{Γ A B} → Tm35 Γ (prod35 A B) → Tm35 Γ A; fst35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd left right case zero suc rec →
     fst35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd left right case zero suc rec)

snd35 : ∀{Γ A B} → Tm35 Γ (prod35 A B) → Tm35 Γ B; snd35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left right case zero suc rec →
     snd35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left right case zero suc rec)

left35 : ∀{Γ A B} → Tm35 Γ A → Tm35 Γ (sum35 A B); left35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right case zero suc rec →
     left35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right case zero suc rec)

right35 : ∀{Γ A B} → Tm35 Γ B → Tm35 Γ (sum35 A B); right35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case zero suc rec →
     right35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case zero suc rec)

case35 : ∀{Γ A B C} → Tm35 Γ (sum35 A B) → Tm35 Γ (arr35 A C) → Tm35 Γ (arr35 B C) → Tm35 Γ C; case35
 = λ t u v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec →
     case35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)
           (u Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)
           (v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)

zero35  : ∀{Γ} → Tm35 Γ nat35; zero35
 = λ Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc rec → zero35

suc35 : ∀{Γ} → Tm35 Γ nat35 → Tm35 Γ nat35; suc35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec →
   suc35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec)

rec35 : ∀{Γ A} → Tm35 Γ nat35 → Tm35 Γ (arr35 nat35 (arr35 A A)) → Tm35 Γ A → Tm35 Γ A; rec35
 = λ t u v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35 →
     rec35 (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)
         (u Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)
         (v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)

v035 : ∀{Γ A} → Tm35 (snoc35 Γ A) A; v035
 = var35 vz35

v135 : ∀{Γ A B} → Tm35 (snoc35 (snoc35 Γ A) B) A; v135
 = var35 (vs35 vz35)

v235 : ∀{Γ A B C} → Tm35 (snoc35 (snoc35 (snoc35 Γ A) B) C) A; v235
 = var35 (vs35 (vs35 vz35))

v335 : ∀{Γ A B C D} → Tm35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) A; v335
 = var35 (vs35 (vs35 (vs35 vz35)))

tbool35 : Ty35; tbool35
 = sum35 top35 top35

true35 : ∀{Γ} → Tm35 Γ tbool35; true35
 = left35 tt35

tfalse35 : ∀{Γ} → Tm35 Γ tbool35; tfalse35
 = right35 tt35

ifthenelse35 : ∀{Γ A} → Tm35 Γ (arr35 tbool35 (arr35 A (arr35 A A))); ifthenelse35
 = lam35 (lam35 (lam35 (case35 v235 (lam35 v235) (lam35 v135))))

times435 : ∀{Γ A} → Tm35 Γ (arr35 (arr35 A A) (arr35 A A)); times435
  = lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035)))))

add35 : ∀{Γ} → Tm35 Γ (arr35 nat35 (arr35 nat35 nat35)); add35
 = lam35 (rec35 v035
       (lam35 (lam35 (lam35 (suc35 (app35 v135 v035)))))
       (lam35 v035))

mul35 : ∀{Γ} → Tm35 Γ (arr35 nat35 (arr35 nat35 nat35)); mul35
 = lam35 (rec35 v035
       (lam35 (lam35 (lam35 (app35 (app35 add35 (app35 v135 v035)) v035))))
       (lam35 zero35))

fact35 : ∀{Γ} → Tm35 Γ (arr35 nat35 nat35); fact35
 = lam35 (rec35 v035 (lam35 (lam35 (app35 (app35 mul35 (suc35 v135)) v035)))
        (suc35 zero35))
{-# OPTIONS --type-in-type #-}

Ty36 : Set
Ty36 =
   (Ty36         : Set)
   (nat top bot  : Ty36)
   (arr prod sum : Ty36 → Ty36 → Ty36)
 → Ty36

nat36 : Ty36; nat36 = λ _ nat36 _ _ _ _ _ → nat36
top36 : Ty36; top36 = λ _ _ top36 _ _ _ _ → top36
bot36 : Ty36; bot36 = λ _ _ _ bot36 _ _ _ → bot36

arr36 : Ty36 → Ty36 → Ty36; arr36
 = λ A B Ty36 nat36 top36 bot36 arr36 prod sum →
     arr36 (A Ty36 nat36 top36 bot36 arr36 prod sum) (B Ty36 nat36 top36 bot36 arr36 prod sum)

prod36 : Ty36 → Ty36 → Ty36; prod36
 = λ A B Ty36 nat36 top36 bot36 arr36 prod36 sum →
     prod36 (A Ty36 nat36 top36 bot36 arr36 prod36 sum) (B Ty36 nat36 top36 bot36 arr36 prod36 sum)

sum36 : Ty36 → Ty36 → Ty36; sum36
 = λ A B Ty36 nat36 top36 bot36 arr36 prod36 sum36 →
     sum36 (A Ty36 nat36 top36 bot36 arr36 prod36 sum36) (B Ty36 nat36 top36 bot36 arr36 prod36 sum36)

Con36 : Set; Con36
 = (Con36 : Set)
   (nil  : Con36)
   (snoc : Con36 → Ty36 → Con36)
 → Con36

nil36 : Con36; nil36
 = λ Con36 nil36 snoc → nil36

snoc36 : Con36 → Ty36 → Con36; snoc36
 = λ Γ A Con36 nil36 snoc36 → snoc36 (Γ Con36 nil36 snoc36) A

Var36 : Con36 → Ty36 → Set; Var36
 = λ Γ A →
   (Var36 : Con36 → Ty36 → Set)
   (vz  : ∀{Γ A} → Var36 (snoc36 Γ A) A)
   (vs  : ∀{Γ B A} → Var36 Γ A → Var36 (snoc36 Γ B) A)
 → Var36 Γ A

vz36 : ∀{Γ A} → Var36 (snoc36 Γ A) A; vz36
 = λ Var36 vz36 vs → vz36

vs36 : ∀{Γ B A} → Var36 Γ A → Var36 (snoc36 Γ B) A; vs36
 = λ x Var36 vz36 vs36 → vs36 (x Var36 vz36 vs36)

Tm36 : Con36 → Ty36 → Set; Tm36
 = λ Γ A →
   (Tm36  : Con36 → Ty36 → Set)
   (var   : ∀{Γ A} → Var36 Γ A → Tm36 Γ A)
   (lam   : ∀{Γ A B} → Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B))
   (app   : ∀{Γ A B} → Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B)
   (tt    : ∀{Γ} → Tm36 Γ top36)
   (pair  : ∀{Γ A B} → Tm36 Γ A → Tm36 Γ B → Tm36 Γ (prod36 A B))
   (fst   : ∀{Γ A B} → Tm36 Γ (prod36 A B) → Tm36 Γ A)
   (snd   : ∀{Γ A B} → Tm36 Γ (prod36 A B) → Tm36 Γ B)
   (left  : ∀{Γ A B} → Tm36 Γ A → Tm36 Γ (sum36 A B))
   (right : ∀{Γ A B} → Tm36 Γ B → Tm36 Γ (sum36 A B))
   (case  : ∀{Γ A B C} → Tm36 Γ (sum36 A B) → Tm36 Γ (arr36 A C) → Tm36 Γ (arr36 B C) → Tm36 Γ C)
   (zero  : ∀{Γ} → Tm36 Γ nat36)
   (suc   : ∀{Γ} → Tm36 Γ nat36 → Tm36 Γ nat36)
   (rec   : ∀{Γ A} → Tm36 Γ nat36 → Tm36 Γ (arr36 nat36 (arr36 A A)) → Tm36 Γ A → Tm36 Γ A)
 → Tm36 Γ A

var36 : ∀{Γ A} → Var36 Γ A → Tm36 Γ A; var36
 = λ x Tm36 var36 lam app tt pair fst snd left right case zero suc rec →
     var36 x

lam36 : ∀{Γ A B} → Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B); lam36
 = λ t Tm36 var36 lam36 app tt pair fst snd left right case zero suc rec →
     lam36 (t Tm36 var36 lam36 app tt pair fst snd left right case zero suc rec)

app36 : ∀{Γ A B} → Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B; app36
 = λ t u Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec →
     app36 (t Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec)
         (u Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec)

tt36 : ∀{Γ} → Tm36 Γ top36; tt36
 = λ Tm36 var36 lam36 app36 tt36 pair fst snd left right case zero suc rec → tt36

pair36 : ∀{Γ A B} → Tm36 Γ A → Tm36 Γ B → Tm36 Γ (prod36 A B); pair36
 = λ t u Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec →
     pair36 (t Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec)
          (u Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec)

fst36 : ∀{Γ A B} → Tm36 Γ (prod36 A B) → Tm36 Γ A; fst36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd left right case zero suc rec →
     fst36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd left right case zero suc rec)

snd36 : ∀{Γ A B} → Tm36 Γ (prod36 A B) → Tm36 Γ B; snd36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left right case zero suc rec →
     snd36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left right case zero suc rec)

left36 : ∀{Γ A B} → Tm36 Γ A → Tm36 Γ (sum36 A B); left36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right case zero suc rec →
     left36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right case zero suc rec)

right36 : ∀{Γ A B} → Tm36 Γ B → Tm36 Γ (sum36 A B); right36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case zero suc rec →
     right36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case zero suc rec)

case36 : ∀{Γ A B C} → Tm36 Γ (sum36 A B) → Tm36 Γ (arr36 A C) → Tm36 Γ (arr36 B C) → Tm36 Γ C; case36
 = λ t u v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec →
     case36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)
           (u Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)
           (v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)

zero36  : ∀{Γ} → Tm36 Γ nat36; zero36
 = λ Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc rec → zero36

suc36 : ∀{Γ} → Tm36 Γ nat36 → Tm36 Γ nat36; suc36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec →
   suc36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec)

rec36 : ∀{Γ A} → Tm36 Γ nat36 → Tm36 Γ (arr36 nat36 (arr36 A A)) → Tm36 Γ A → Tm36 Γ A; rec36
 = λ t u v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36 →
     rec36 (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)
         (u Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)
         (v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)

v036 : ∀{Γ A} → Tm36 (snoc36 Γ A) A; v036
 = var36 vz36

v136 : ∀{Γ A B} → Tm36 (snoc36 (snoc36 Γ A) B) A; v136
 = var36 (vs36 vz36)

v236 : ∀{Γ A B C} → Tm36 (snoc36 (snoc36 (snoc36 Γ A) B) C) A; v236
 = var36 (vs36 (vs36 vz36))

v336 : ∀{Γ A B C D} → Tm36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) A; v336
 = var36 (vs36 (vs36 (vs36 vz36)))

tbool36 : Ty36; tbool36
 = sum36 top36 top36

true36 : ∀{Γ} → Tm36 Γ tbool36; true36
 = left36 tt36

tfalse36 : ∀{Γ} → Tm36 Γ tbool36; tfalse36
 = right36 tt36

ifthenelse36 : ∀{Γ A} → Tm36 Γ (arr36 tbool36 (arr36 A (arr36 A A))); ifthenelse36
 = lam36 (lam36 (lam36 (case36 v236 (lam36 v236) (lam36 v136))))

times436 : ∀{Γ A} → Tm36 Γ (arr36 (arr36 A A) (arr36 A A)); times436
  = lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036)))))

add36 : ∀{Γ} → Tm36 Γ (arr36 nat36 (arr36 nat36 nat36)); add36
 = lam36 (rec36 v036
       (lam36 (lam36 (lam36 (suc36 (app36 v136 v036)))))
       (lam36 v036))

mul36 : ∀{Γ} → Tm36 Γ (arr36 nat36 (arr36 nat36 nat36)); mul36
 = lam36 (rec36 v036
       (lam36 (lam36 (lam36 (app36 (app36 add36 (app36 v136 v036)) v036))))
       (lam36 zero36))

fact36 : ∀{Γ} → Tm36 Γ (arr36 nat36 nat36); fact36
 = lam36 (rec36 v036 (lam36 (lam36 (app36 (app36 mul36 (suc36 v136)) v036)))
        (suc36 zero36))
{-# OPTIONS --type-in-type #-}

Ty37 : Set
Ty37 =
   (Ty37         : Set)
   (nat top bot  : Ty37)
   (arr prod sum : Ty37 → Ty37 → Ty37)
 → Ty37

nat37 : Ty37; nat37 = λ _ nat37 _ _ _ _ _ → nat37
top37 : Ty37; top37 = λ _ _ top37 _ _ _ _ → top37
bot37 : Ty37; bot37 = λ _ _ _ bot37 _ _ _ → bot37

arr37 : Ty37 → Ty37 → Ty37; arr37
 = λ A B Ty37 nat37 top37 bot37 arr37 prod sum →
     arr37 (A Ty37 nat37 top37 bot37 arr37 prod sum) (B Ty37 nat37 top37 bot37 arr37 prod sum)

prod37 : Ty37 → Ty37 → Ty37; prod37
 = λ A B Ty37 nat37 top37 bot37 arr37 prod37 sum →
     prod37 (A Ty37 nat37 top37 bot37 arr37 prod37 sum) (B Ty37 nat37 top37 bot37 arr37 prod37 sum)

sum37 : Ty37 → Ty37 → Ty37; sum37
 = λ A B Ty37 nat37 top37 bot37 arr37 prod37 sum37 →
     sum37 (A Ty37 nat37 top37 bot37 arr37 prod37 sum37) (B Ty37 nat37 top37 bot37 arr37 prod37 sum37)

Con37 : Set; Con37
 = (Con37 : Set)
   (nil  : Con37)
   (snoc : Con37 → Ty37 → Con37)
 → Con37

nil37 : Con37; nil37
 = λ Con37 nil37 snoc → nil37

snoc37 : Con37 → Ty37 → Con37; snoc37
 = λ Γ A Con37 nil37 snoc37 → snoc37 (Γ Con37 nil37 snoc37) A

Var37 : Con37 → Ty37 → Set; Var37
 = λ Γ A →
   (Var37 : Con37 → Ty37 → Set)
   (vz  : ∀{Γ A} → Var37 (snoc37 Γ A) A)
   (vs  : ∀{Γ B A} → Var37 Γ A → Var37 (snoc37 Γ B) A)
 → Var37 Γ A

vz37 : ∀{Γ A} → Var37 (snoc37 Γ A) A; vz37
 = λ Var37 vz37 vs → vz37

vs37 : ∀{Γ B A} → Var37 Γ A → Var37 (snoc37 Γ B) A; vs37
 = λ x Var37 vz37 vs37 → vs37 (x Var37 vz37 vs37)

Tm37 : Con37 → Ty37 → Set; Tm37
 = λ Γ A →
   (Tm37  : Con37 → Ty37 → Set)
   (var   : ∀{Γ A} → Var37 Γ A → Tm37 Γ A)
   (lam   : ∀{Γ A B} → Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B))
   (app   : ∀{Γ A B} → Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B)
   (tt    : ∀{Γ} → Tm37 Γ top37)
   (pair  : ∀{Γ A B} → Tm37 Γ A → Tm37 Γ B → Tm37 Γ (prod37 A B))
   (fst   : ∀{Γ A B} → Tm37 Γ (prod37 A B) → Tm37 Γ A)
   (snd   : ∀{Γ A B} → Tm37 Γ (prod37 A B) → Tm37 Γ B)
   (left  : ∀{Γ A B} → Tm37 Γ A → Tm37 Γ (sum37 A B))
   (right : ∀{Γ A B} → Tm37 Γ B → Tm37 Γ (sum37 A B))
   (case  : ∀{Γ A B C} → Tm37 Γ (sum37 A B) → Tm37 Γ (arr37 A C) → Tm37 Γ (arr37 B C) → Tm37 Γ C)
   (zero  : ∀{Γ} → Tm37 Γ nat37)
   (suc   : ∀{Γ} → Tm37 Γ nat37 → Tm37 Γ nat37)
   (rec   : ∀{Γ A} → Tm37 Γ nat37 → Tm37 Γ (arr37 nat37 (arr37 A A)) → Tm37 Γ A → Tm37 Γ A)
 → Tm37 Γ A

var37 : ∀{Γ A} → Var37 Γ A → Tm37 Γ A; var37
 = λ x Tm37 var37 lam app tt pair fst snd left right case zero suc rec →
     var37 x

lam37 : ∀{Γ A B} → Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B); lam37
 = λ t Tm37 var37 lam37 app tt pair fst snd left right case zero suc rec →
     lam37 (t Tm37 var37 lam37 app tt pair fst snd left right case zero suc rec)

app37 : ∀{Γ A B} → Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B; app37
 = λ t u Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec →
     app37 (t Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec)
         (u Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec)

tt37 : ∀{Γ} → Tm37 Γ top37; tt37
 = λ Tm37 var37 lam37 app37 tt37 pair fst snd left right case zero suc rec → tt37

pair37 : ∀{Γ A B} → Tm37 Γ A → Tm37 Γ B → Tm37 Γ (prod37 A B); pair37
 = λ t u Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec →
     pair37 (t Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec)
          (u Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec)

fst37 : ∀{Γ A B} → Tm37 Γ (prod37 A B) → Tm37 Γ A; fst37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd left right case zero suc rec →
     fst37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd left right case zero suc rec)

snd37 : ∀{Γ A B} → Tm37 Γ (prod37 A B) → Tm37 Γ B; snd37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left right case zero suc rec →
     snd37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left right case zero suc rec)

left37 : ∀{Γ A B} → Tm37 Γ A → Tm37 Γ (sum37 A B); left37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right case zero suc rec →
     left37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right case zero suc rec)

right37 : ∀{Γ A B} → Tm37 Γ B → Tm37 Γ (sum37 A B); right37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case zero suc rec →
     right37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case zero suc rec)

case37 : ∀{Γ A B C} → Tm37 Γ (sum37 A B) → Tm37 Γ (arr37 A C) → Tm37 Γ (arr37 B C) → Tm37 Γ C; case37
 = λ t u v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec →
     case37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)
           (u Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)
           (v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)

zero37  : ∀{Γ} → Tm37 Γ nat37; zero37
 = λ Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc rec → zero37

suc37 : ∀{Γ} → Tm37 Γ nat37 → Tm37 Γ nat37; suc37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec →
   suc37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec)

rec37 : ∀{Γ A} → Tm37 Γ nat37 → Tm37 Γ (arr37 nat37 (arr37 A A)) → Tm37 Γ A → Tm37 Γ A; rec37
 = λ t u v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37 →
     rec37 (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)
         (u Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)
         (v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)

v037 : ∀{Γ A} → Tm37 (snoc37 Γ A) A; v037
 = var37 vz37

v137 : ∀{Γ A B} → Tm37 (snoc37 (snoc37 Γ A) B) A; v137
 = var37 (vs37 vz37)

v237 : ∀{Γ A B C} → Tm37 (snoc37 (snoc37 (snoc37 Γ A) B) C) A; v237
 = var37 (vs37 (vs37 vz37))

v337 : ∀{Γ A B C D} → Tm37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) A; v337
 = var37 (vs37 (vs37 (vs37 vz37)))

tbool37 : Ty37; tbool37
 = sum37 top37 top37

true37 : ∀{Γ} → Tm37 Γ tbool37; true37
 = left37 tt37

tfalse37 : ∀{Γ} → Tm37 Γ tbool37; tfalse37
 = right37 tt37

ifthenelse37 : ∀{Γ A} → Tm37 Γ (arr37 tbool37 (arr37 A (arr37 A A))); ifthenelse37
 = lam37 (lam37 (lam37 (case37 v237 (lam37 v237) (lam37 v137))))

times437 : ∀{Γ A} → Tm37 Γ (arr37 (arr37 A A) (arr37 A A)); times437
  = lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037)))))

add37 : ∀{Γ} → Tm37 Γ (arr37 nat37 (arr37 nat37 nat37)); add37
 = lam37 (rec37 v037
       (lam37 (lam37 (lam37 (suc37 (app37 v137 v037)))))
       (lam37 v037))

mul37 : ∀{Γ} → Tm37 Γ (arr37 nat37 (arr37 nat37 nat37)); mul37
 = lam37 (rec37 v037
       (lam37 (lam37 (lam37 (app37 (app37 add37 (app37 v137 v037)) v037))))
       (lam37 zero37))

fact37 : ∀{Γ} → Tm37 Γ (arr37 nat37 nat37); fact37
 = lam37 (rec37 v037 (lam37 (lam37 (app37 (app37 mul37 (suc37 v137)) v037)))
        (suc37 zero37))
{-# OPTIONS --type-in-type #-}

Ty38 : Set
Ty38 =
   (Ty38         : Set)
   (nat top bot  : Ty38)
   (arr prod sum : Ty38 → Ty38 → Ty38)
 → Ty38

nat38 : Ty38; nat38 = λ _ nat38 _ _ _ _ _ → nat38
top38 : Ty38; top38 = λ _ _ top38 _ _ _ _ → top38
bot38 : Ty38; bot38 = λ _ _ _ bot38 _ _ _ → bot38

arr38 : Ty38 → Ty38 → Ty38; arr38
 = λ A B Ty38 nat38 top38 bot38 arr38 prod sum →
     arr38 (A Ty38 nat38 top38 bot38 arr38 prod sum) (B Ty38 nat38 top38 bot38 arr38 prod sum)

prod38 : Ty38 → Ty38 → Ty38; prod38
 = λ A B Ty38 nat38 top38 bot38 arr38 prod38 sum →
     prod38 (A Ty38 nat38 top38 bot38 arr38 prod38 sum) (B Ty38 nat38 top38 bot38 arr38 prod38 sum)

sum38 : Ty38 → Ty38 → Ty38; sum38
 = λ A B Ty38 nat38 top38 bot38 arr38 prod38 sum38 →
     sum38 (A Ty38 nat38 top38 bot38 arr38 prod38 sum38) (B Ty38 nat38 top38 bot38 arr38 prod38 sum38)

Con38 : Set; Con38
 = (Con38 : Set)
   (nil  : Con38)
   (snoc : Con38 → Ty38 → Con38)
 → Con38

nil38 : Con38; nil38
 = λ Con38 nil38 snoc → nil38

snoc38 : Con38 → Ty38 → Con38; snoc38
 = λ Γ A Con38 nil38 snoc38 → snoc38 (Γ Con38 nil38 snoc38) A

Var38 : Con38 → Ty38 → Set; Var38
 = λ Γ A →
   (Var38 : Con38 → Ty38 → Set)
   (vz  : ∀{Γ A} → Var38 (snoc38 Γ A) A)
   (vs  : ∀{Γ B A} → Var38 Γ A → Var38 (snoc38 Γ B) A)
 → Var38 Γ A

vz38 : ∀{Γ A} → Var38 (snoc38 Γ A) A; vz38
 = λ Var38 vz38 vs → vz38

vs38 : ∀{Γ B A} → Var38 Γ A → Var38 (snoc38 Γ B) A; vs38
 = λ x Var38 vz38 vs38 → vs38 (x Var38 vz38 vs38)

Tm38 : Con38 → Ty38 → Set; Tm38
 = λ Γ A →
   (Tm38  : Con38 → Ty38 → Set)
   (var   : ∀{Γ A} → Var38 Γ A → Tm38 Γ A)
   (lam   : ∀{Γ A B} → Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B))
   (app   : ∀{Γ A B} → Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B)
   (tt    : ∀{Γ} → Tm38 Γ top38)
   (pair  : ∀{Γ A B} → Tm38 Γ A → Tm38 Γ B → Tm38 Γ (prod38 A B))
   (fst   : ∀{Γ A B} → Tm38 Γ (prod38 A B) → Tm38 Γ A)
   (snd   : ∀{Γ A B} → Tm38 Γ (prod38 A B) → Tm38 Γ B)
   (left  : ∀{Γ A B} → Tm38 Γ A → Tm38 Γ (sum38 A B))
   (right : ∀{Γ A B} → Tm38 Γ B → Tm38 Γ (sum38 A B))
   (case  : ∀{Γ A B C} → Tm38 Γ (sum38 A B) → Tm38 Γ (arr38 A C) → Tm38 Γ (arr38 B C) → Tm38 Γ C)
   (zero  : ∀{Γ} → Tm38 Γ nat38)
   (suc   : ∀{Γ} → Tm38 Γ nat38 → Tm38 Γ nat38)
   (rec   : ∀{Γ A} → Tm38 Γ nat38 → Tm38 Γ (arr38 nat38 (arr38 A A)) → Tm38 Γ A → Tm38 Γ A)
 → Tm38 Γ A

var38 : ∀{Γ A} → Var38 Γ A → Tm38 Γ A; var38
 = λ x Tm38 var38 lam app tt pair fst snd left right case zero suc rec →
     var38 x

lam38 : ∀{Γ A B} → Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B); lam38
 = λ t Tm38 var38 lam38 app tt pair fst snd left right case zero suc rec →
     lam38 (t Tm38 var38 lam38 app tt pair fst snd left right case zero suc rec)

app38 : ∀{Γ A B} → Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B; app38
 = λ t u Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec →
     app38 (t Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec)
         (u Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec)

tt38 : ∀{Γ} → Tm38 Γ top38; tt38
 = λ Tm38 var38 lam38 app38 tt38 pair fst snd left right case zero suc rec → tt38

pair38 : ∀{Γ A B} → Tm38 Γ A → Tm38 Γ B → Tm38 Γ (prod38 A B); pair38
 = λ t u Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec →
     pair38 (t Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec)
          (u Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec)

fst38 : ∀{Γ A B} → Tm38 Γ (prod38 A B) → Tm38 Γ A; fst38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd left right case zero suc rec →
     fst38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd left right case zero suc rec)

snd38 : ∀{Γ A B} → Tm38 Γ (prod38 A B) → Tm38 Γ B; snd38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left right case zero suc rec →
     snd38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left right case zero suc rec)

left38 : ∀{Γ A B} → Tm38 Γ A → Tm38 Γ (sum38 A B); left38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right case zero suc rec →
     left38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right case zero suc rec)

right38 : ∀{Γ A B} → Tm38 Γ B → Tm38 Γ (sum38 A B); right38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case zero suc rec →
     right38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case zero suc rec)

case38 : ∀{Γ A B C} → Tm38 Γ (sum38 A B) → Tm38 Γ (arr38 A C) → Tm38 Γ (arr38 B C) → Tm38 Γ C; case38
 = λ t u v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec →
     case38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)
           (u Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)
           (v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)

zero38  : ∀{Γ} → Tm38 Γ nat38; zero38
 = λ Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc rec → zero38

suc38 : ∀{Γ} → Tm38 Γ nat38 → Tm38 Γ nat38; suc38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec →
   suc38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec)

rec38 : ∀{Γ A} → Tm38 Γ nat38 → Tm38 Γ (arr38 nat38 (arr38 A A)) → Tm38 Γ A → Tm38 Γ A; rec38
 = λ t u v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38 →
     rec38 (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)
         (u Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)
         (v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)

v038 : ∀{Γ A} → Tm38 (snoc38 Γ A) A; v038
 = var38 vz38

v138 : ∀{Γ A B} → Tm38 (snoc38 (snoc38 Γ A) B) A; v138
 = var38 (vs38 vz38)

v238 : ∀{Γ A B C} → Tm38 (snoc38 (snoc38 (snoc38 Γ A) B) C) A; v238
 = var38 (vs38 (vs38 vz38))

v338 : ∀{Γ A B C D} → Tm38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) A; v338
 = var38 (vs38 (vs38 (vs38 vz38)))

tbool38 : Ty38; tbool38
 = sum38 top38 top38

true38 : ∀{Γ} → Tm38 Γ tbool38; true38
 = left38 tt38

tfalse38 : ∀{Γ} → Tm38 Γ tbool38; tfalse38
 = right38 tt38

ifthenelse38 : ∀{Γ A} → Tm38 Γ (arr38 tbool38 (arr38 A (arr38 A A))); ifthenelse38
 = lam38 (lam38 (lam38 (case38 v238 (lam38 v238) (lam38 v138))))

times438 : ∀{Γ A} → Tm38 Γ (arr38 (arr38 A A) (arr38 A A)); times438
  = lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038)))))

add38 : ∀{Γ} → Tm38 Γ (arr38 nat38 (arr38 nat38 nat38)); add38
 = lam38 (rec38 v038
       (lam38 (lam38 (lam38 (suc38 (app38 v138 v038)))))
       (lam38 v038))

mul38 : ∀{Γ} → Tm38 Γ (arr38 nat38 (arr38 nat38 nat38)); mul38
 = lam38 (rec38 v038
       (lam38 (lam38 (lam38 (app38 (app38 add38 (app38 v138 v038)) v038))))
       (lam38 zero38))

fact38 : ∀{Γ} → Tm38 Γ (arr38 nat38 nat38); fact38
 = lam38 (rec38 v038 (lam38 (lam38 (app38 (app38 mul38 (suc38 v138)) v038)))
        (suc38 zero38))
{-# OPTIONS --type-in-type #-}

Ty39 : Set
Ty39 =
   (Ty39         : Set)
   (nat top bot  : Ty39)
   (arr prod sum : Ty39 → Ty39 → Ty39)
 → Ty39

nat39 : Ty39; nat39 = λ _ nat39 _ _ _ _ _ → nat39
top39 : Ty39; top39 = λ _ _ top39 _ _ _ _ → top39
bot39 : Ty39; bot39 = λ _ _ _ bot39 _ _ _ → bot39

arr39 : Ty39 → Ty39 → Ty39; arr39
 = λ A B Ty39 nat39 top39 bot39 arr39 prod sum →
     arr39 (A Ty39 nat39 top39 bot39 arr39 prod sum) (B Ty39 nat39 top39 bot39 arr39 prod sum)

prod39 : Ty39 → Ty39 → Ty39; prod39
 = λ A B Ty39 nat39 top39 bot39 arr39 prod39 sum →
     prod39 (A Ty39 nat39 top39 bot39 arr39 prod39 sum) (B Ty39 nat39 top39 bot39 arr39 prod39 sum)

sum39 : Ty39 → Ty39 → Ty39; sum39
 = λ A B Ty39 nat39 top39 bot39 arr39 prod39 sum39 →
     sum39 (A Ty39 nat39 top39 bot39 arr39 prod39 sum39) (B Ty39 nat39 top39 bot39 arr39 prod39 sum39)

Con39 : Set; Con39
 = (Con39 : Set)
   (nil  : Con39)
   (snoc : Con39 → Ty39 → Con39)
 → Con39

nil39 : Con39; nil39
 = λ Con39 nil39 snoc → nil39

snoc39 : Con39 → Ty39 → Con39; snoc39
 = λ Γ A Con39 nil39 snoc39 → snoc39 (Γ Con39 nil39 snoc39) A

Var39 : Con39 → Ty39 → Set; Var39
 = λ Γ A →
   (Var39 : Con39 → Ty39 → Set)
   (vz  : ∀{Γ A} → Var39 (snoc39 Γ A) A)
   (vs  : ∀{Γ B A} → Var39 Γ A → Var39 (snoc39 Γ B) A)
 → Var39 Γ A

vz39 : ∀{Γ A} → Var39 (snoc39 Γ A) A; vz39
 = λ Var39 vz39 vs → vz39

vs39 : ∀{Γ B A} → Var39 Γ A → Var39 (snoc39 Γ B) A; vs39
 = λ x Var39 vz39 vs39 → vs39 (x Var39 vz39 vs39)

Tm39 : Con39 → Ty39 → Set; Tm39
 = λ Γ A →
   (Tm39  : Con39 → Ty39 → Set)
   (var   : ∀{Γ A} → Var39 Γ A → Tm39 Γ A)
   (lam   : ∀{Γ A B} → Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B))
   (app   : ∀{Γ A B} → Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B)
   (tt    : ∀{Γ} → Tm39 Γ top39)
   (pair  : ∀{Γ A B} → Tm39 Γ A → Tm39 Γ B → Tm39 Γ (prod39 A B))
   (fst   : ∀{Γ A B} → Tm39 Γ (prod39 A B) → Tm39 Γ A)
   (snd   : ∀{Γ A B} → Tm39 Γ (prod39 A B) → Tm39 Γ B)
   (left  : ∀{Γ A B} → Tm39 Γ A → Tm39 Γ (sum39 A B))
   (right : ∀{Γ A B} → Tm39 Γ B → Tm39 Γ (sum39 A B))
   (case  : ∀{Γ A B C} → Tm39 Γ (sum39 A B) → Tm39 Γ (arr39 A C) → Tm39 Γ (arr39 B C) → Tm39 Γ C)
   (zero  : ∀{Γ} → Tm39 Γ nat39)
   (suc   : ∀{Γ} → Tm39 Γ nat39 → Tm39 Γ nat39)
   (rec   : ∀{Γ A} → Tm39 Γ nat39 → Tm39 Γ (arr39 nat39 (arr39 A A)) → Tm39 Γ A → Tm39 Γ A)
 → Tm39 Γ A

var39 : ∀{Γ A} → Var39 Γ A → Tm39 Γ A; var39
 = λ x Tm39 var39 lam app tt pair fst snd left right case zero suc rec →
     var39 x

lam39 : ∀{Γ A B} → Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B); lam39
 = λ t Tm39 var39 lam39 app tt pair fst snd left right case zero suc rec →
     lam39 (t Tm39 var39 lam39 app tt pair fst snd left right case zero suc rec)

app39 : ∀{Γ A B} → Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B; app39
 = λ t u Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec →
     app39 (t Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec)
         (u Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec)

tt39 : ∀{Γ} → Tm39 Γ top39; tt39
 = λ Tm39 var39 lam39 app39 tt39 pair fst snd left right case zero suc rec → tt39

pair39 : ∀{Γ A B} → Tm39 Γ A → Tm39 Γ B → Tm39 Γ (prod39 A B); pair39
 = λ t u Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec →
     pair39 (t Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec)
          (u Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec)

fst39 : ∀{Γ A B} → Tm39 Γ (prod39 A B) → Tm39 Γ A; fst39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd left right case zero suc rec →
     fst39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd left right case zero suc rec)

snd39 : ∀{Γ A B} → Tm39 Γ (prod39 A B) → Tm39 Γ B; snd39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left right case zero suc rec →
     snd39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left right case zero suc rec)

left39 : ∀{Γ A B} → Tm39 Γ A → Tm39 Γ (sum39 A B); left39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right case zero suc rec →
     left39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right case zero suc rec)

right39 : ∀{Γ A B} → Tm39 Γ B → Tm39 Γ (sum39 A B); right39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case zero suc rec →
     right39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case zero suc rec)

case39 : ∀{Γ A B C} → Tm39 Γ (sum39 A B) → Tm39 Γ (arr39 A C) → Tm39 Γ (arr39 B C) → Tm39 Γ C; case39
 = λ t u v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec →
     case39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)
           (u Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)
           (v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)

zero39  : ∀{Γ} → Tm39 Γ nat39; zero39
 = λ Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc rec → zero39

suc39 : ∀{Γ} → Tm39 Γ nat39 → Tm39 Γ nat39; suc39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec →
   suc39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec)

rec39 : ∀{Γ A} → Tm39 Γ nat39 → Tm39 Γ (arr39 nat39 (arr39 A A)) → Tm39 Γ A → Tm39 Γ A; rec39
 = λ t u v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39 →
     rec39 (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)
         (u Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)
         (v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)

v039 : ∀{Γ A} → Tm39 (snoc39 Γ A) A; v039
 = var39 vz39

v139 : ∀{Γ A B} → Tm39 (snoc39 (snoc39 Γ A) B) A; v139
 = var39 (vs39 vz39)

v239 : ∀{Γ A B C} → Tm39 (snoc39 (snoc39 (snoc39 Γ A) B) C) A; v239
 = var39 (vs39 (vs39 vz39))

v339 : ∀{Γ A B C D} → Tm39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) A; v339
 = var39 (vs39 (vs39 (vs39 vz39)))

tbool39 : Ty39; tbool39
 = sum39 top39 top39

true39 : ∀{Γ} → Tm39 Γ tbool39; true39
 = left39 tt39

tfalse39 : ∀{Γ} → Tm39 Γ tbool39; tfalse39
 = right39 tt39

ifthenelse39 : ∀{Γ A} → Tm39 Γ (arr39 tbool39 (arr39 A (arr39 A A))); ifthenelse39
 = lam39 (lam39 (lam39 (case39 v239 (lam39 v239) (lam39 v139))))

times439 : ∀{Γ A} → Tm39 Γ (arr39 (arr39 A A) (arr39 A A)); times439
  = lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039)))))

add39 : ∀{Γ} → Tm39 Γ (arr39 nat39 (arr39 nat39 nat39)); add39
 = lam39 (rec39 v039
       (lam39 (lam39 (lam39 (suc39 (app39 v139 v039)))))
       (lam39 v039))

mul39 : ∀{Γ} → Tm39 Γ (arr39 nat39 (arr39 nat39 nat39)); mul39
 = lam39 (rec39 v039
       (lam39 (lam39 (lam39 (app39 (app39 add39 (app39 v139 v039)) v039))))
       (lam39 zero39))

fact39 : ∀{Γ} → Tm39 Γ (arr39 nat39 nat39); fact39
 = lam39 (rec39 v039 (lam39 (lam39 (app39 (app39 mul39 (suc39 v139)) v039)))
        (suc39 zero39))
{-# OPTIONS --type-in-type #-}

Ty40 : Set
Ty40 =
   (Ty40         : Set)
   (nat top bot  : Ty40)
   (arr prod sum : Ty40 → Ty40 → Ty40)
 → Ty40

nat40 : Ty40; nat40 = λ _ nat40 _ _ _ _ _ → nat40
top40 : Ty40; top40 = λ _ _ top40 _ _ _ _ → top40
bot40 : Ty40; bot40 = λ _ _ _ bot40 _ _ _ → bot40

arr40 : Ty40 → Ty40 → Ty40; arr40
 = λ A B Ty40 nat40 top40 bot40 arr40 prod sum →
     arr40 (A Ty40 nat40 top40 bot40 arr40 prod sum) (B Ty40 nat40 top40 bot40 arr40 prod sum)

prod40 : Ty40 → Ty40 → Ty40; prod40
 = λ A B Ty40 nat40 top40 bot40 arr40 prod40 sum →
     prod40 (A Ty40 nat40 top40 bot40 arr40 prod40 sum) (B Ty40 nat40 top40 bot40 arr40 prod40 sum)

sum40 : Ty40 → Ty40 → Ty40; sum40
 = λ A B Ty40 nat40 top40 bot40 arr40 prod40 sum40 →
     sum40 (A Ty40 nat40 top40 bot40 arr40 prod40 sum40) (B Ty40 nat40 top40 bot40 arr40 prod40 sum40)

Con40 : Set; Con40
 = (Con40 : Set)
   (nil  : Con40)
   (snoc : Con40 → Ty40 → Con40)
 → Con40

nil40 : Con40; nil40
 = λ Con40 nil40 snoc → nil40

snoc40 : Con40 → Ty40 → Con40; snoc40
 = λ Γ A Con40 nil40 snoc40 → snoc40 (Γ Con40 nil40 snoc40) A

Var40 : Con40 → Ty40 → Set; Var40
 = λ Γ A →
   (Var40 : Con40 → Ty40 → Set)
   (vz  : ∀{Γ A} → Var40 (snoc40 Γ A) A)
   (vs  : ∀{Γ B A} → Var40 Γ A → Var40 (snoc40 Γ B) A)
 → Var40 Γ A

vz40 : ∀{Γ A} → Var40 (snoc40 Γ A) A; vz40
 = λ Var40 vz40 vs → vz40

vs40 : ∀{Γ B A} → Var40 Γ A → Var40 (snoc40 Γ B) A; vs40
 = λ x Var40 vz40 vs40 → vs40 (x Var40 vz40 vs40)

Tm40 : Con40 → Ty40 → Set; Tm40
 = λ Γ A →
   (Tm40  : Con40 → Ty40 → Set)
   (var   : ∀{Γ A} → Var40 Γ A → Tm40 Γ A)
   (lam   : ∀{Γ A B} → Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B))
   (app   : ∀{Γ A B} → Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B)
   (tt    : ∀{Γ} → Tm40 Γ top40)
   (pair  : ∀{Γ A B} → Tm40 Γ A → Tm40 Γ B → Tm40 Γ (prod40 A B))
   (fst   : ∀{Γ A B} → Tm40 Γ (prod40 A B) → Tm40 Γ A)
   (snd   : ∀{Γ A B} → Tm40 Γ (prod40 A B) → Tm40 Γ B)
   (left  : ∀{Γ A B} → Tm40 Γ A → Tm40 Γ (sum40 A B))
   (right : ∀{Γ A B} → Tm40 Γ B → Tm40 Γ (sum40 A B))
   (case  : ∀{Γ A B C} → Tm40 Γ (sum40 A B) → Tm40 Γ (arr40 A C) → Tm40 Γ (arr40 B C) → Tm40 Γ C)
   (zero  : ∀{Γ} → Tm40 Γ nat40)
   (suc   : ∀{Γ} → Tm40 Γ nat40 → Tm40 Γ nat40)
   (rec   : ∀{Γ A} → Tm40 Γ nat40 → Tm40 Γ (arr40 nat40 (arr40 A A)) → Tm40 Γ A → Tm40 Γ A)
 → Tm40 Γ A

var40 : ∀{Γ A} → Var40 Γ A → Tm40 Γ A; var40
 = λ x Tm40 var40 lam app tt pair fst snd left right case zero suc rec →
     var40 x

lam40 : ∀{Γ A B} → Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B); lam40
 = λ t Tm40 var40 lam40 app tt pair fst snd left right case zero suc rec →
     lam40 (t Tm40 var40 lam40 app tt pair fst snd left right case zero suc rec)

app40 : ∀{Γ A B} → Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B; app40
 = λ t u Tm40 var40 lam40 app40 tt pair fst snd left right case zero suc rec →
     app40 (t Tm40 var40 lam40 app40 tt pair fst snd left right case zero suc rec)
         (u Tm40 var40 lam40 app40 tt pair fst snd left right case zero suc rec)

tt40 : ∀{Γ} → Tm40 Γ top40; tt40
 = λ Tm40 var40 lam40 app40 tt40 pair fst snd left right case zero suc rec → tt40

pair40 : ∀{Γ A B} → Tm40 Γ A → Tm40 Γ B → Tm40 Γ (prod40 A B); pair40
 = λ t u Tm40 var40 lam40 app40 tt40 pair40 fst snd left right case zero suc rec →
     pair40 (t Tm40 var40 lam40 app40 tt40 pair40 fst snd left right case zero suc rec)
          (u Tm40 var40 lam40 app40 tt40 pair40 fst snd left right case zero suc rec)

fst40 : ∀{Γ A B} → Tm40 Γ (prod40 A B) → Tm40 Γ A; fst40
 = λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd left right case zero suc rec →
     fst40 (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd left right case zero suc rec)

snd40 : ∀{Γ A B} → Tm40 Γ (prod40 A B) → Tm40 Γ B; snd40
 = λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left right case zero suc rec →
     snd40 (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left right case zero suc rec)

left40 : ∀{Γ A B} → Tm40 Γ A → Tm40 Γ (sum40 A B); left40
 = λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right case zero suc rec →
     left40 (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right case zero suc rec)

right40 : ∀{Γ A B} → Tm40 Γ B → Tm40 Γ (sum40 A B); right40
 = λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case zero suc rec →
     right40 (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case zero suc rec)

case40 : ∀{Γ A B C} → Tm40 Γ (sum40 A B) → Tm40 Γ (arr40 A C) → Tm40 Γ (arr40 B C) → Tm40 Γ C; case40
 = λ t u v Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero suc rec →
     case40 (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero suc rec)
           (u Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero suc rec)
           (v Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero suc rec)

zero40  : ∀{Γ} → Tm40 Γ nat40; zero40
 = λ Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc rec → zero40

suc40 : ∀{Γ} → Tm40 Γ nat40 → Tm40 Γ nat40; suc40
 = λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec →
   suc40 (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec)

rec40 : ∀{Γ A} → Tm40 Γ nat40 → Tm40 Γ (arr40 nat40 (arr40 A A)) → Tm40 Γ A → Tm40 Γ A; rec40
 = λ t u v Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec40 →
     rec40 (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec40)
         (u Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec40)
         (v Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec40)

v040 : ∀{Γ A} → Tm40 (snoc40 Γ A) A; v040
 = var40 vz40

v140 : ∀{Γ A B} → Tm40 (snoc40 (snoc40 Γ A) B) A; v140
 = var40 (vs40 vz40)

v240 : ∀{Γ A B C} → Tm40 (snoc40 (snoc40 (snoc40 Γ A) B) C) A; v240
 = var40 (vs40 (vs40 vz40))

v340 : ∀{Γ A B C D} → Tm40 (snoc40 (snoc40 (snoc40 (snoc40 Γ A) B) C) D) A; v340
 = var40 (vs40 (vs40 (vs40 vz40)))

tbool40 : Ty40; tbool40
 = sum40 top40 top40

true40 : ∀{Γ} → Tm40 Γ tbool40; true40
 = left40 tt40

tfalse40 : ∀{Γ} → Tm40 Γ tbool40; tfalse40
 = right40 tt40

ifthenelse40 : ∀{Γ A} → Tm40 Γ (arr40 tbool40 (arr40 A (arr40 A A))); ifthenelse40
 = lam40 (lam40 (lam40 (case40 v240 (lam40 v240) (lam40 v140))))

times440 : ∀{Γ A} → Tm40 Γ (arr40 (arr40 A A) (arr40 A A)); times440
  = lam40 (lam40 (app40 v140 (app40 v140 (app40 v140 (app40 v140 v040)))))

add40 : ∀{Γ} → Tm40 Γ (arr40 nat40 (arr40 nat40 nat40)); add40
 = lam40 (rec40 v040
       (lam40 (lam40 (lam40 (suc40 (app40 v140 v040)))))
       (lam40 v040))

mul40 : ∀{Γ} → Tm40 Γ (arr40 nat40 (arr40 nat40 nat40)); mul40
 = lam40 (rec40 v040
       (lam40 (lam40 (lam40 (app40 (app40 add40 (app40 v140 v040)) v040))))
       (lam40 zero40))

fact40 : ∀{Γ} → Tm40 Γ (arr40 nat40 nat40); fact40
 = lam40 (rec40 v040 (lam40 (lam40 (app40 (app40 mul40 (suc40 v140)) v040)))
        (suc40 zero40))
{-# OPTIONS --type-in-type #-}

Ty41 : Set
Ty41 =
   (Ty41         : Set)
   (nat top bot  : Ty41)
   (arr prod sum : Ty41 → Ty41 → Ty41)
 → Ty41

nat41 : Ty41; nat41 = λ _ nat41 _ _ _ _ _ → nat41
top41 : Ty41; top41 = λ _ _ top41 _ _ _ _ → top41
bot41 : Ty41; bot41 = λ _ _ _ bot41 _ _ _ → bot41

arr41 : Ty41 → Ty41 → Ty41; arr41
 = λ A B Ty41 nat41 top41 bot41 arr41 prod sum →
     arr41 (A Ty41 nat41 top41 bot41 arr41 prod sum) (B Ty41 nat41 top41 bot41 arr41 prod sum)

prod41 : Ty41 → Ty41 → Ty41; prod41
 = λ A B Ty41 nat41 top41 bot41 arr41 prod41 sum →
     prod41 (A Ty41 nat41 top41 bot41 arr41 prod41 sum) (B Ty41 nat41 top41 bot41 arr41 prod41 sum)

sum41 : Ty41 → Ty41 → Ty41; sum41
 = λ A B Ty41 nat41 top41 bot41 arr41 prod41 sum41 →
     sum41 (A Ty41 nat41 top41 bot41 arr41 prod41 sum41) (B Ty41 nat41 top41 bot41 arr41 prod41 sum41)

Con41 : Set; Con41
 = (Con41 : Set)
   (nil  : Con41)
   (snoc : Con41 → Ty41 → Con41)
 → Con41

nil41 : Con41; nil41
 = λ Con41 nil41 snoc → nil41

snoc41 : Con41 → Ty41 → Con41; snoc41
 = λ Γ A Con41 nil41 snoc41 → snoc41 (Γ Con41 nil41 snoc41) A

Var41 : Con41 → Ty41 → Set; Var41
 = λ Γ A →
   (Var41 : Con41 → Ty41 → Set)
   (vz  : ∀{Γ A} → Var41 (snoc41 Γ A) A)
   (vs  : ∀{Γ B A} → Var41 Γ A → Var41 (snoc41 Γ B) A)
 → Var41 Γ A

vz41 : ∀{Γ A} → Var41 (snoc41 Γ A) A; vz41
 = λ Var41 vz41 vs → vz41

vs41 : ∀{Γ B A} → Var41 Γ A → Var41 (snoc41 Γ B) A; vs41
 = λ x Var41 vz41 vs41 → vs41 (x Var41 vz41 vs41)

Tm41 : Con41 → Ty41 → Set; Tm41
 = λ Γ A →
   (Tm41  : Con41 → Ty41 → Set)
   (var   : ∀{Γ A} → Var41 Γ A → Tm41 Γ A)
   (lam   : ∀{Γ A B} → Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B))
   (app   : ∀{Γ A B} → Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B)
   (tt    : ∀{Γ} → Tm41 Γ top41)
   (pair  : ∀{Γ A B} → Tm41 Γ A → Tm41 Γ B → Tm41 Γ (prod41 A B))
   (fst   : ∀{Γ A B} → Tm41 Γ (prod41 A B) → Tm41 Γ A)
   (snd   : ∀{Γ A B} → Tm41 Γ (prod41 A B) → Tm41 Γ B)
   (left  : ∀{Γ A B} → Tm41 Γ A → Tm41 Γ (sum41 A B))
   (right : ∀{Γ A B} → Tm41 Γ B → Tm41 Γ (sum41 A B))
   (case  : ∀{Γ A B C} → Tm41 Γ (sum41 A B) → Tm41 Γ (arr41 A C) → Tm41 Γ (arr41 B C) → Tm41 Γ C)
   (zero  : ∀{Γ} → Tm41 Γ nat41)
   (suc   : ∀{Γ} → Tm41 Γ nat41 → Tm41 Γ nat41)
   (rec   : ∀{Γ A} → Tm41 Γ nat41 → Tm41 Γ (arr41 nat41 (arr41 A A)) → Tm41 Γ A → Tm41 Γ A)
 → Tm41 Γ A

var41 : ∀{Γ A} → Var41 Γ A → Tm41 Γ A; var41
 = λ x Tm41 var41 lam app tt pair fst snd left right case zero suc rec →
     var41 x

lam41 : ∀{Γ A B} → Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B); lam41
 = λ t Tm41 var41 lam41 app tt pair fst snd left right case zero suc rec →
     lam41 (t Tm41 var41 lam41 app tt pair fst snd left right case zero suc rec)

app41 : ∀{Γ A B} → Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B; app41
 = λ t u Tm41 var41 lam41 app41 tt pair fst snd left right case zero suc rec →
     app41 (t Tm41 var41 lam41 app41 tt pair fst snd left right case zero suc rec)
         (u Tm41 var41 lam41 app41 tt pair fst snd left right case zero suc rec)

tt41 : ∀{Γ} → Tm41 Γ top41; tt41
 = λ Tm41 var41 lam41 app41 tt41 pair fst snd left right case zero suc rec → tt41

pair41 : ∀{Γ A B} → Tm41 Γ A → Tm41 Γ B → Tm41 Γ (prod41 A B); pair41
 = λ t u Tm41 var41 lam41 app41 tt41 pair41 fst snd left right case zero suc rec →
     pair41 (t Tm41 var41 lam41 app41 tt41 pair41 fst snd left right case zero suc rec)
          (u Tm41 var41 lam41 app41 tt41 pair41 fst snd left right case zero suc rec)

fst41 : ∀{Γ A B} → Tm41 Γ (prod41 A B) → Tm41 Γ A; fst41
 = λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd left right case zero suc rec →
     fst41 (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd left right case zero suc rec)

snd41 : ∀{Γ A B} → Tm41 Γ (prod41 A B) → Tm41 Γ B; snd41
 = λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left right case zero suc rec →
     snd41 (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left right case zero suc rec)

left41 : ∀{Γ A B} → Tm41 Γ A → Tm41 Γ (sum41 A B); left41
 = λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right case zero suc rec →
     left41 (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right case zero suc rec)

right41 : ∀{Γ A B} → Tm41 Γ B → Tm41 Γ (sum41 A B); right41
 = λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case zero suc rec →
     right41 (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case zero suc rec)

case41 : ∀{Γ A B C} → Tm41 Γ (sum41 A B) → Tm41 Γ (arr41 A C) → Tm41 Γ (arr41 B C) → Tm41 Γ C; case41
 = λ t u v Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero suc rec →
     case41 (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero suc rec)
           (u Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero suc rec)
           (v Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero suc rec)

zero41  : ∀{Γ} → Tm41 Γ nat41; zero41
 = λ Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc rec → zero41

suc41 : ∀{Γ} → Tm41 Γ nat41 → Tm41 Γ nat41; suc41
 = λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec →
   suc41 (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec)

rec41 : ∀{Γ A} → Tm41 Γ nat41 → Tm41 Γ (arr41 nat41 (arr41 A A)) → Tm41 Γ A → Tm41 Γ A; rec41
 = λ t u v Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec41 →
     rec41 (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec41)
         (u Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec41)
         (v Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec41)

v041 : ∀{Γ A} → Tm41 (snoc41 Γ A) A; v041
 = var41 vz41

v141 : ∀{Γ A B} → Tm41 (snoc41 (snoc41 Γ A) B) A; v141
 = var41 (vs41 vz41)

v241 : ∀{Γ A B C} → Tm41 (snoc41 (snoc41 (snoc41 Γ A) B) C) A; v241
 = var41 (vs41 (vs41 vz41))

v341 : ∀{Γ A B C D} → Tm41 (snoc41 (snoc41 (snoc41 (snoc41 Γ A) B) C) D) A; v341
 = var41 (vs41 (vs41 (vs41 vz41)))

tbool41 : Ty41; tbool41
 = sum41 top41 top41

true41 : ∀{Γ} → Tm41 Γ tbool41; true41
 = left41 tt41

tfalse41 : ∀{Γ} → Tm41 Γ tbool41; tfalse41
 = right41 tt41

ifthenelse41 : ∀{Γ A} → Tm41 Γ (arr41 tbool41 (arr41 A (arr41 A A))); ifthenelse41
 = lam41 (lam41 (lam41 (case41 v241 (lam41 v241) (lam41 v141))))

times441 : ∀{Γ A} → Tm41 Γ (arr41 (arr41 A A) (arr41 A A)); times441
  = lam41 (lam41 (app41 v141 (app41 v141 (app41 v141 (app41 v141 v041)))))

add41 : ∀{Γ} → Tm41 Γ (arr41 nat41 (arr41 nat41 nat41)); add41
 = lam41 (rec41 v041
       (lam41 (lam41 (lam41 (suc41 (app41 v141 v041)))))
       (lam41 v041))

mul41 : ∀{Γ} → Tm41 Γ (arr41 nat41 (arr41 nat41 nat41)); mul41
 = lam41 (rec41 v041
       (lam41 (lam41 (lam41 (app41 (app41 add41 (app41 v141 v041)) v041))))
       (lam41 zero41))

fact41 : ∀{Γ} → Tm41 Γ (arr41 nat41 nat41); fact41
 = lam41 (rec41 v041 (lam41 (lam41 (app41 (app41 mul41 (suc41 v141)) v041)))
        (suc41 zero41))
{-# OPTIONS --type-in-type #-}

Ty42 : Set
Ty42 =
   (Ty42         : Set)
   (nat top bot  : Ty42)
   (arr prod sum : Ty42 → Ty42 → Ty42)
 → Ty42

nat42 : Ty42; nat42 = λ _ nat42 _ _ _ _ _ → nat42
top42 : Ty42; top42 = λ _ _ top42 _ _ _ _ → top42
bot42 : Ty42; bot42 = λ _ _ _ bot42 _ _ _ → bot42

arr42 : Ty42 → Ty42 → Ty42; arr42
 = λ A B Ty42 nat42 top42 bot42 arr42 prod sum →
     arr42 (A Ty42 nat42 top42 bot42 arr42 prod sum) (B Ty42 nat42 top42 bot42 arr42 prod sum)

prod42 : Ty42 → Ty42 → Ty42; prod42
 = λ A B Ty42 nat42 top42 bot42 arr42 prod42 sum →
     prod42 (A Ty42 nat42 top42 bot42 arr42 prod42 sum) (B Ty42 nat42 top42 bot42 arr42 prod42 sum)

sum42 : Ty42 → Ty42 → Ty42; sum42
 = λ A B Ty42 nat42 top42 bot42 arr42 prod42 sum42 →
     sum42 (A Ty42 nat42 top42 bot42 arr42 prod42 sum42) (B Ty42 nat42 top42 bot42 arr42 prod42 sum42)

Con42 : Set; Con42
 = (Con42 : Set)
   (nil  : Con42)
   (snoc : Con42 → Ty42 → Con42)
 → Con42

nil42 : Con42; nil42
 = λ Con42 nil42 snoc → nil42

snoc42 : Con42 → Ty42 → Con42; snoc42
 = λ Γ A Con42 nil42 snoc42 → snoc42 (Γ Con42 nil42 snoc42) A

Var42 : Con42 → Ty42 → Set; Var42
 = λ Γ A →
   (Var42 : Con42 → Ty42 → Set)
   (vz  : ∀{Γ A} → Var42 (snoc42 Γ A) A)
   (vs  : ∀{Γ B A} → Var42 Γ A → Var42 (snoc42 Γ B) A)
 → Var42 Γ A

vz42 : ∀{Γ A} → Var42 (snoc42 Γ A) A; vz42
 = λ Var42 vz42 vs → vz42

vs42 : ∀{Γ B A} → Var42 Γ A → Var42 (snoc42 Γ B) A; vs42
 = λ x Var42 vz42 vs42 → vs42 (x Var42 vz42 vs42)

Tm42 : Con42 → Ty42 → Set; Tm42
 = λ Γ A →
   (Tm42  : Con42 → Ty42 → Set)
   (var   : ∀{Γ A} → Var42 Γ A → Tm42 Γ A)
   (lam   : ∀{Γ A B} → Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B))
   (app   : ∀{Γ A B} → Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B)
   (tt    : ∀{Γ} → Tm42 Γ top42)
   (pair  : ∀{Γ A B} → Tm42 Γ A → Tm42 Γ B → Tm42 Γ (prod42 A B))
   (fst   : ∀{Γ A B} → Tm42 Γ (prod42 A B) → Tm42 Γ A)
   (snd   : ∀{Γ A B} → Tm42 Γ (prod42 A B) → Tm42 Γ B)
   (left  : ∀{Γ A B} → Tm42 Γ A → Tm42 Γ (sum42 A B))
   (right : ∀{Γ A B} → Tm42 Γ B → Tm42 Γ (sum42 A B))
   (case  : ∀{Γ A B C} → Tm42 Γ (sum42 A B) → Tm42 Γ (arr42 A C) → Tm42 Γ (arr42 B C) → Tm42 Γ C)
   (zero  : ∀{Γ} → Tm42 Γ nat42)
   (suc   : ∀{Γ} → Tm42 Γ nat42 → Tm42 Γ nat42)
   (rec   : ∀{Γ A} → Tm42 Γ nat42 → Tm42 Γ (arr42 nat42 (arr42 A A)) → Tm42 Γ A → Tm42 Γ A)
 → Tm42 Γ A

var42 : ∀{Γ A} → Var42 Γ A → Tm42 Γ A; var42
 = λ x Tm42 var42 lam app tt pair fst snd left right case zero suc rec →
     var42 x

lam42 : ∀{Γ A B} → Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B); lam42
 = λ t Tm42 var42 lam42 app tt pair fst snd left right case zero suc rec →
     lam42 (t Tm42 var42 lam42 app tt pair fst snd left right case zero suc rec)

app42 : ∀{Γ A B} → Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B; app42
 = λ t u Tm42 var42 lam42 app42 tt pair fst snd left right case zero suc rec →
     app42 (t Tm42 var42 lam42 app42 tt pair fst snd left right case zero suc rec)
         (u Tm42 var42 lam42 app42 tt pair fst snd left right case zero suc rec)

tt42 : ∀{Γ} → Tm42 Γ top42; tt42
 = λ Tm42 var42 lam42 app42 tt42 pair fst snd left right case zero suc rec → tt42

pair42 : ∀{Γ A B} → Tm42 Γ A → Tm42 Γ B → Tm42 Γ (prod42 A B); pair42
 = λ t u Tm42 var42 lam42 app42 tt42 pair42 fst snd left right case zero suc rec →
     pair42 (t Tm42 var42 lam42 app42 tt42 pair42 fst snd left right case zero suc rec)
          (u Tm42 var42 lam42 app42 tt42 pair42 fst snd left right case zero suc rec)

fst42 : ∀{Γ A B} → Tm42 Γ (prod42 A B) → Tm42 Γ A; fst42
 = λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd left right case zero suc rec →
     fst42 (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd left right case zero suc rec)

snd42 : ∀{Γ A B} → Tm42 Γ (prod42 A B) → Tm42 Γ B; snd42
 = λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left right case zero suc rec →
     snd42 (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left right case zero suc rec)

left42 : ∀{Γ A B} → Tm42 Γ A → Tm42 Γ (sum42 A B); left42
 = λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right case zero suc rec →
     left42 (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right case zero suc rec)

right42 : ∀{Γ A B} → Tm42 Γ B → Tm42 Γ (sum42 A B); right42
 = λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case zero suc rec →
     right42 (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case zero suc rec)

case42 : ∀{Γ A B C} → Tm42 Γ (sum42 A B) → Tm42 Γ (arr42 A C) → Tm42 Γ (arr42 B C) → Tm42 Γ C; case42
 = λ t u v Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero suc rec →
     case42 (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero suc rec)
           (u Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero suc rec)
           (v Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero suc rec)

zero42  : ∀{Γ} → Tm42 Γ nat42; zero42
 = λ Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc rec → zero42

suc42 : ∀{Γ} → Tm42 Γ nat42 → Tm42 Γ nat42; suc42
 = λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec →
   suc42 (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec)

rec42 : ∀{Γ A} → Tm42 Γ nat42 → Tm42 Γ (arr42 nat42 (arr42 A A)) → Tm42 Γ A → Tm42 Γ A; rec42
 = λ t u v Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec42 →
     rec42 (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec42)
         (u Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec42)
         (v Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec42)

v042 : ∀{Γ A} → Tm42 (snoc42 Γ A) A; v042
 = var42 vz42

v142 : ∀{Γ A B} → Tm42 (snoc42 (snoc42 Γ A) B) A; v142
 = var42 (vs42 vz42)

v242 : ∀{Γ A B C} → Tm42 (snoc42 (snoc42 (snoc42 Γ A) B) C) A; v242
 = var42 (vs42 (vs42 vz42))

v342 : ∀{Γ A B C D} → Tm42 (snoc42 (snoc42 (snoc42 (snoc42 Γ A) B) C) D) A; v342
 = var42 (vs42 (vs42 (vs42 vz42)))

tbool42 : Ty42; tbool42
 = sum42 top42 top42

true42 : ∀{Γ} → Tm42 Γ tbool42; true42
 = left42 tt42

tfalse42 : ∀{Γ} → Tm42 Γ tbool42; tfalse42
 = right42 tt42

ifthenelse42 : ∀{Γ A} → Tm42 Γ (arr42 tbool42 (arr42 A (arr42 A A))); ifthenelse42
 = lam42 (lam42 (lam42 (case42 v242 (lam42 v242) (lam42 v142))))

times442 : ∀{Γ A} → Tm42 Γ (arr42 (arr42 A A) (arr42 A A)); times442
  = lam42 (lam42 (app42 v142 (app42 v142 (app42 v142 (app42 v142 v042)))))

add42 : ∀{Γ} → Tm42 Γ (arr42 nat42 (arr42 nat42 nat42)); add42
 = lam42 (rec42 v042
       (lam42 (lam42 (lam42 (suc42 (app42 v142 v042)))))
       (lam42 v042))

mul42 : ∀{Γ} → Tm42 Γ (arr42 nat42 (arr42 nat42 nat42)); mul42
 = lam42 (rec42 v042
       (lam42 (lam42 (lam42 (app42 (app42 add42 (app42 v142 v042)) v042))))
       (lam42 zero42))

fact42 : ∀{Γ} → Tm42 Γ (arr42 nat42 nat42); fact42
 = lam42 (rec42 v042 (lam42 (lam42 (app42 (app42 mul42 (suc42 v142)) v042)))
        (suc42 zero42))
{-# OPTIONS --type-in-type #-}

Ty43 : Set
Ty43 =
   (Ty43         : Set)
   (nat top bot  : Ty43)
   (arr prod sum : Ty43 → Ty43 → Ty43)
 → Ty43

nat43 : Ty43; nat43 = λ _ nat43 _ _ _ _ _ → nat43
top43 : Ty43; top43 = λ _ _ top43 _ _ _ _ → top43
bot43 : Ty43; bot43 = λ _ _ _ bot43 _ _ _ → bot43

arr43 : Ty43 → Ty43 → Ty43; arr43
 = λ A B Ty43 nat43 top43 bot43 arr43 prod sum →
     arr43 (A Ty43 nat43 top43 bot43 arr43 prod sum) (B Ty43 nat43 top43 bot43 arr43 prod sum)

prod43 : Ty43 → Ty43 → Ty43; prod43
 = λ A B Ty43 nat43 top43 bot43 arr43 prod43 sum →
     prod43 (A Ty43 nat43 top43 bot43 arr43 prod43 sum) (B Ty43 nat43 top43 bot43 arr43 prod43 sum)

sum43 : Ty43 → Ty43 → Ty43; sum43
 = λ A B Ty43 nat43 top43 bot43 arr43 prod43 sum43 →
     sum43 (A Ty43 nat43 top43 bot43 arr43 prod43 sum43) (B Ty43 nat43 top43 bot43 arr43 prod43 sum43)

Con43 : Set; Con43
 = (Con43 : Set)
   (nil  : Con43)
   (snoc : Con43 → Ty43 → Con43)
 → Con43

nil43 : Con43; nil43
 = λ Con43 nil43 snoc → nil43

snoc43 : Con43 → Ty43 → Con43; snoc43
 = λ Γ A Con43 nil43 snoc43 → snoc43 (Γ Con43 nil43 snoc43) A

Var43 : Con43 → Ty43 → Set; Var43
 = λ Γ A →
   (Var43 : Con43 → Ty43 → Set)
   (vz  : ∀{Γ A} → Var43 (snoc43 Γ A) A)
   (vs  : ∀{Γ B A} → Var43 Γ A → Var43 (snoc43 Γ B) A)
 → Var43 Γ A

vz43 : ∀{Γ A} → Var43 (snoc43 Γ A) A; vz43
 = λ Var43 vz43 vs → vz43

vs43 : ∀{Γ B A} → Var43 Γ A → Var43 (snoc43 Γ B) A; vs43
 = λ x Var43 vz43 vs43 → vs43 (x Var43 vz43 vs43)

Tm43 : Con43 → Ty43 → Set; Tm43
 = λ Γ A →
   (Tm43  : Con43 → Ty43 → Set)
   (var   : ∀{Γ A} → Var43 Γ A → Tm43 Γ A)
   (lam   : ∀{Γ A B} → Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B))
   (app   : ∀{Γ A B} → Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B)
   (tt    : ∀{Γ} → Tm43 Γ top43)
   (pair  : ∀{Γ A B} → Tm43 Γ A → Tm43 Γ B → Tm43 Γ (prod43 A B))
   (fst   : ∀{Γ A B} → Tm43 Γ (prod43 A B) → Tm43 Γ A)
   (snd   : ∀{Γ A B} → Tm43 Γ (prod43 A B) → Tm43 Γ B)
   (left  : ∀{Γ A B} → Tm43 Γ A → Tm43 Γ (sum43 A B))
   (right : ∀{Γ A B} → Tm43 Γ B → Tm43 Γ (sum43 A B))
   (case  : ∀{Γ A B C} → Tm43 Γ (sum43 A B) → Tm43 Γ (arr43 A C) → Tm43 Γ (arr43 B C) → Tm43 Γ C)
   (zero  : ∀{Γ} → Tm43 Γ nat43)
   (suc   : ∀{Γ} → Tm43 Γ nat43 → Tm43 Γ nat43)
   (rec   : ∀{Γ A} → Tm43 Γ nat43 → Tm43 Γ (arr43 nat43 (arr43 A A)) → Tm43 Γ A → Tm43 Γ A)
 → Tm43 Γ A

var43 : ∀{Γ A} → Var43 Γ A → Tm43 Γ A; var43
 = λ x Tm43 var43 lam app tt pair fst snd left right case zero suc rec →
     var43 x

lam43 : ∀{Γ A B} → Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B); lam43
 = λ t Tm43 var43 lam43 app tt pair fst snd left right case zero suc rec →
     lam43 (t Tm43 var43 lam43 app tt pair fst snd left right case zero suc rec)

app43 : ∀{Γ A B} → Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B; app43
 = λ t u Tm43 var43 lam43 app43 tt pair fst snd left right case zero suc rec →
     app43 (t Tm43 var43 lam43 app43 tt pair fst snd left right case zero suc rec)
         (u Tm43 var43 lam43 app43 tt pair fst snd left right case zero suc rec)

tt43 : ∀{Γ} → Tm43 Γ top43; tt43
 = λ Tm43 var43 lam43 app43 tt43 pair fst snd left right case zero suc rec → tt43

pair43 : ∀{Γ A B} → Tm43 Γ A → Tm43 Γ B → Tm43 Γ (prod43 A B); pair43
 = λ t u Tm43 var43 lam43 app43 tt43 pair43 fst snd left right case zero suc rec →
     pair43 (t Tm43 var43 lam43 app43 tt43 pair43 fst snd left right case zero suc rec)
          (u Tm43 var43 lam43 app43 tt43 pair43 fst snd left right case zero suc rec)

fst43 : ∀{Γ A B} → Tm43 Γ (prod43 A B) → Tm43 Γ A; fst43
 = λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd left right case zero suc rec →
     fst43 (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd left right case zero suc rec)

snd43 : ∀{Γ A B} → Tm43 Γ (prod43 A B) → Tm43 Γ B; snd43
 = λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left right case zero suc rec →
     snd43 (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left right case zero suc rec)

left43 : ∀{Γ A B} → Tm43 Γ A → Tm43 Γ (sum43 A B); left43
 = λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right case zero suc rec →
     left43 (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right case zero suc rec)

right43 : ∀{Γ A B} → Tm43 Γ B → Tm43 Γ (sum43 A B); right43
 = λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case zero suc rec →
     right43 (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case zero suc rec)

case43 : ∀{Γ A B C} → Tm43 Γ (sum43 A B) → Tm43 Γ (arr43 A C) → Tm43 Γ (arr43 B C) → Tm43 Γ C; case43
 = λ t u v Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero suc rec →
     case43 (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero suc rec)
           (u Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero suc rec)
           (v Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero suc rec)

zero43  : ∀{Γ} → Tm43 Γ nat43; zero43
 = λ Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc rec → zero43

suc43 : ∀{Γ} → Tm43 Γ nat43 → Tm43 Γ nat43; suc43
 = λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec →
   suc43 (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec)

rec43 : ∀{Γ A} → Tm43 Γ nat43 → Tm43 Γ (arr43 nat43 (arr43 A A)) → Tm43 Γ A → Tm43 Γ A; rec43
 = λ t u v Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec43 →
     rec43 (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec43)
         (u Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec43)
         (v Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec43)

v043 : ∀{Γ A} → Tm43 (snoc43 Γ A) A; v043
 = var43 vz43

v143 : ∀{Γ A B} → Tm43 (snoc43 (snoc43 Γ A) B) A; v143
 = var43 (vs43 vz43)

v243 : ∀{Γ A B C} → Tm43 (snoc43 (snoc43 (snoc43 Γ A) B) C) A; v243
 = var43 (vs43 (vs43 vz43))

v343 : ∀{Γ A B C D} → Tm43 (snoc43 (snoc43 (snoc43 (snoc43 Γ A) B) C) D) A; v343
 = var43 (vs43 (vs43 (vs43 vz43)))

tbool43 : Ty43; tbool43
 = sum43 top43 top43

true43 : ∀{Γ} → Tm43 Γ tbool43; true43
 = left43 tt43

tfalse43 : ∀{Γ} → Tm43 Γ tbool43; tfalse43
 = right43 tt43

ifthenelse43 : ∀{Γ A} → Tm43 Γ (arr43 tbool43 (arr43 A (arr43 A A))); ifthenelse43
 = lam43 (lam43 (lam43 (case43 v243 (lam43 v243) (lam43 v143))))

times443 : ∀{Γ A} → Tm43 Γ (arr43 (arr43 A A) (arr43 A A)); times443
  = lam43 (lam43 (app43 v143 (app43 v143 (app43 v143 (app43 v143 v043)))))

add43 : ∀{Γ} → Tm43 Γ (arr43 nat43 (arr43 nat43 nat43)); add43
 = lam43 (rec43 v043
       (lam43 (lam43 (lam43 (suc43 (app43 v143 v043)))))
       (lam43 v043))

mul43 : ∀{Γ} → Tm43 Γ (arr43 nat43 (arr43 nat43 nat43)); mul43
 = lam43 (rec43 v043
       (lam43 (lam43 (lam43 (app43 (app43 add43 (app43 v143 v043)) v043))))
       (lam43 zero43))

fact43 : ∀{Γ} → Tm43 Γ (arr43 nat43 nat43); fact43
 = lam43 (rec43 v043 (lam43 (lam43 (app43 (app43 mul43 (suc43 v143)) v043)))
        (suc43 zero43))
{-# OPTIONS --type-in-type #-}

Ty44 : Set
Ty44 =
   (Ty44         : Set)
   (nat top bot  : Ty44)
   (arr prod sum : Ty44 → Ty44 → Ty44)
 → Ty44

nat44 : Ty44; nat44 = λ _ nat44 _ _ _ _ _ → nat44
top44 : Ty44; top44 = λ _ _ top44 _ _ _ _ → top44
bot44 : Ty44; bot44 = λ _ _ _ bot44 _ _ _ → bot44

arr44 : Ty44 → Ty44 → Ty44; arr44
 = λ A B Ty44 nat44 top44 bot44 arr44 prod sum →
     arr44 (A Ty44 nat44 top44 bot44 arr44 prod sum) (B Ty44 nat44 top44 bot44 arr44 prod sum)

prod44 : Ty44 → Ty44 → Ty44; prod44
 = λ A B Ty44 nat44 top44 bot44 arr44 prod44 sum →
     prod44 (A Ty44 nat44 top44 bot44 arr44 prod44 sum) (B Ty44 nat44 top44 bot44 arr44 prod44 sum)

sum44 : Ty44 → Ty44 → Ty44; sum44
 = λ A B Ty44 nat44 top44 bot44 arr44 prod44 sum44 →
     sum44 (A Ty44 nat44 top44 bot44 arr44 prod44 sum44) (B Ty44 nat44 top44 bot44 arr44 prod44 sum44)

Con44 : Set; Con44
 = (Con44 : Set)
   (nil  : Con44)
   (snoc : Con44 → Ty44 → Con44)
 → Con44

nil44 : Con44; nil44
 = λ Con44 nil44 snoc → nil44

snoc44 : Con44 → Ty44 → Con44; snoc44
 = λ Γ A Con44 nil44 snoc44 → snoc44 (Γ Con44 nil44 snoc44) A

Var44 : Con44 → Ty44 → Set; Var44
 = λ Γ A →
   (Var44 : Con44 → Ty44 → Set)
   (vz  : ∀{Γ A} → Var44 (snoc44 Γ A) A)
   (vs  : ∀{Γ B A} → Var44 Γ A → Var44 (snoc44 Γ B) A)
 → Var44 Γ A

vz44 : ∀{Γ A} → Var44 (snoc44 Γ A) A; vz44
 = λ Var44 vz44 vs → vz44

vs44 : ∀{Γ B A} → Var44 Γ A → Var44 (snoc44 Γ B) A; vs44
 = λ x Var44 vz44 vs44 → vs44 (x Var44 vz44 vs44)

Tm44 : Con44 → Ty44 → Set; Tm44
 = λ Γ A →
   (Tm44  : Con44 → Ty44 → Set)
   (var   : ∀{Γ A} → Var44 Γ A → Tm44 Γ A)
   (lam   : ∀{Γ A B} → Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B))
   (app   : ∀{Γ A B} → Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B)
   (tt    : ∀{Γ} → Tm44 Γ top44)
   (pair  : ∀{Γ A B} → Tm44 Γ A → Tm44 Γ B → Tm44 Γ (prod44 A B))
   (fst   : ∀{Γ A B} → Tm44 Γ (prod44 A B) → Tm44 Γ A)
   (snd   : ∀{Γ A B} → Tm44 Γ (prod44 A B) → Tm44 Γ B)
   (left  : ∀{Γ A B} → Tm44 Γ A → Tm44 Γ (sum44 A B))
   (right : ∀{Γ A B} → Tm44 Γ B → Tm44 Γ (sum44 A B))
   (case  : ∀{Γ A B C} → Tm44 Γ (sum44 A B) → Tm44 Γ (arr44 A C) → Tm44 Γ (arr44 B C) → Tm44 Γ C)
   (zero  : ∀{Γ} → Tm44 Γ nat44)
   (suc   : ∀{Γ} → Tm44 Γ nat44 → Tm44 Γ nat44)
   (rec   : ∀{Γ A} → Tm44 Γ nat44 → Tm44 Γ (arr44 nat44 (arr44 A A)) → Tm44 Γ A → Tm44 Γ A)
 → Tm44 Γ A

var44 : ∀{Γ A} → Var44 Γ A → Tm44 Γ A; var44
 = λ x Tm44 var44 lam app tt pair fst snd left right case zero suc rec →
     var44 x

lam44 : ∀{Γ A B} → Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B); lam44
 = λ t Tm44 var44 lam44 app tt pair fst snd left right case zero suc rec →
     lam44 (t Tm44 var44 lam44 app tt pair fst snd left right case zero suc rec)

app44 : ∀{Γ A B} → Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B; app44
 = λ t u Tm44 var44 lam44 app44 tt pair fst snd left right case zero suc rec →
     app44 (t Tm44 var44 lam44 app44 tt pair fst snd left right case zero suc rec)
         (u Tm44 var44 lam44 app44 tt pair fst snd left right case zero suc rec)

tt44 : ∀{Γ} → Tm44 Γ top44; tt44
 = λ Tm44 var44 lam44 app44 tt44 pair fst snd left right case zero suc rec → tt44

pair44 : ∀{Γ A B} → Tm44 Γ A → Tm44 Γ B → Tm44 Γ (prod44 A B); pair44
 = λ t u Tm44 var44 lam44 app44 tt44 pair44 fst snd left right case zero suc rec →
     pair44 (t Tm44 var44 lam44 app44 tt44 pair44 fst snd left right case zero suc rec)
          (u Tm44 var44 lam44 app44 tt44 pair44 fst snd left right case zero suc rec)

fst44 : ∀{Γ A B} → Tm44 Γ (prod44 A B) → Tm44 Γ A; fst44
 = λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd left right case zero suc rec →
     fst44 (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd left right case zero suc rec)

snd44 : ∀{Γ A B} → Tm44 Γ (prod44 A B) → Tm44 Γ B; snd44
 = λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left right case zero suc rec →
     snd44 (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left right case zero suc rec)

left44 : ∀{Γ A B} → Tm44 Γ A → Tm44 Γ (sum44 A B); left44
 = λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right case zero suc rec →
     left44 (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right case zero suc rec)

right44 : ∀{Γ A B} → Tm44 Γ B → Tm44 Γ (sum44 A B); right44
 = λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case zero suc rec →
     right44 (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case zero suc rec)

case44 : ∀{Γ A B C} → Tm44 Γ (sum44 A B) → Tm44 Γ (arr44 A C) → Tm44 Γ (arr44 B C) → Tm44 Γ C; case44
 = λ t u v Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero suc rec →
     case44 (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero suc rec)
           (u Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero suc rec)
           (v Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero suc rec)

zero44  : ∀{Γ} → Tm44 Γ nat44; zero44
 = λ Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc rec → zero44

suc44 : ∀{Γ} → Tm44 Γ nat44 → Tm44 Γ nat44; suc44
 = λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec →
   suc44 (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec)

rec44 : ∀{Γ A} → Tm44 Γ nat44 → Tm44 Γ (arr44 nat44 (arr44 A A)) → Tm44 Γ A → Tm44 Γ A; rec44
 = λ t u v Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec44 →
     rec44 (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec44)
         (u Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec44)
         (v Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec44)

v044 : ∀{Γ A} → Tm44 (snoc44 Γ A) A; v044
 = var44 vz44

v144 : ∀{Γ A B} → Tm44 (snoc44 (snoc44 Γ A) B) A; v144
 = var44 (vs44 vz44)

v244 : ∀{Γ A B C} → Tm44 (snoc44 (snoc44 (snoc44 Γ A) B) C) A; v244
 = var44 (vs44 (vs44 vz44))

v344 : ∀{Γ A B C D} → Tm44 (snoc44 (snoc44 (snoc44 (snoc44 Γ A) B) C) D) A; v344
 = var44 (vs44 (vs44 (vs44 vz44)))

tbool44 : Ty44; tbool44
 = sum44 top44 top44

true44 : ∀{Γ} → Tm44 Γ tbool44; true44
 = left44 tt44

tfalse44 : ∀{Γ} → Tm44 Γ tbool44; tfalse44
 = right44 tt44

ifthenelse44 : ∀{Γ A} → Tm44 Γ (arr44 tbool44 (arr44 A (arr44 A A))); ifthenelse44
 = lam44 (lam44 (lam44 (case44 v244 (lam44 v244) (lam44 v144))))

times444 : ∀{Γ A} → Tm44 Γ (arr44 (arr44 A A) (arr44 A A)); times444
  = lam44 (lam44 (app44 v144 (app44 v144 (app44 v144 (app44 v144 v044)))))

add44 : ∀{Γ} → Tm44 Γ (arr44 nat44 (arr44 nat44 nat44)); add44
 = lam44 (rec44 v044
       (lam44 (lam44 (lam44 (suc44 (app44 v144 v044)))))
       (lam44 v044))

mul44 : ∀{Γ} → Tm44 Γ (arr44 nat44 (arr44 nat44 nat44)); mul44
 = lam44 (rec44 v044
       (lam44 (lam44 (lam44 (app44 (app44 add44 (app44 v144 v044)) v044))))
       (lam44 zero44))

fact44 : ∀{Γ} → Tm44 Γ (arr44 nat44 nat44); fact44
 = lam44 (rec44 v044 (lam44 (lam44 (app44 (app44 mul44 (suc44 v144)) v044)))
        (suc44 zero44))
{-# OPTIONS --type-in-type #-}

Ty45 : Set
Ty45 =
   (Ty45         : Set)
   (nat top bot  : Ty45)
   (arr prod sum : Ty45 → Ty45 → Ty45)
 → Ty45

nat45 : Ty45; nat45 = λ _ nat45 _ _ _ _ _ → nat45
top45 : Ty45; top45 = λ _ _ top45 _ _ _ _ → top45
bot45 : Ty45; bot45 = λ _ _ _ bot45 _ _ _ → bot45

arr45 : Ty45 → Ty45 → Ty45; arr45
 = λ A B Ty45 nat45 top45 bot45 arr45 prod sum →
     arr45 (A Ty45 nat45 top45 bot45 arr45 prod sum) (B Ty45 nat45 top45 bot45 arr45 prod sum)

prod45 : Ty45 → Ty45 → Ty45; prod45
 = λ A B Ty45 nat45 top45 bot45 arr45 prod45 sum →
     prod45 (A Ty45 nat45 top45 bot45 arr45 prod45 sum) (B Ty45 nat45 top45 bot45 arr45 prod45 sum)

sum45 : Ty45 → Ty45 → Ty45; sum45
 = λ A B Ty45 nat45 top45 bot45 arr45 prod45 sum45 →
     sum45 (A Ty45 nat45 top45 bot45 arr45 prod45 sum45) (B Ty45 nat45 top45 bot45 arr45 prod45 sum45)

Con45 : Set; Con45
 = (Con45 : Set)
   (nil  : Con45)
   (snoc : Con45 → Ty45 → Con45)
 → Con45

nil45 : Con45; nil45
 = λ Con45 nil45 snoc → nil45

snoc45 : Con45 → Ty45 → Con45; snoc45
 = λ Γ A Con45 nil45 snoc45 → snoc45 (Γ Con45 nil45 snoc45) A

Var45 : Con45 → Ty45 → Set; Var45
 = λ Γ A →
   (Var45 : Con45 → Ty45 → Set)
   (vz  : ∀{Γ A} → Var45 (snoc45 Γ A) A)
   (vs  : ∀{Γ B A} → Var45 Γ A → Var45 (snoc45 Γ B) A)
 → Var45 Γ A

vz45 : ∀{Γ A} → Var45 (snoc45 Γ A) A; vz45
 = λ Var45 vz45 vs → vz45

vs45 : ∀{Γ B A} → Var45 Γ A → Var45 (snoc45 Γ B) A; vs45
 = λ x Var45 vz45 vs45 → vs45 (x Var45 vz45 vs45)

Tm45 : Con45 → Ty45 → Set; Tm45
 = λ Γ A →
   (Tm45  : Con45 → Ty45 → Set)
   (var   : ∀{Γ A} → Var45 Γ A → Tm45 Γ A)
   (lam   : ∀{Γ A B} → Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B))
   (app   : ∀{Γ A B} → Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B)
   (tt    : ∀{Γ} → Tm45 Γ top45)
   (pair  : ∀{Γ A B} → Tm45 Γ A → Tm45 Γ B → Tm45 Γ (prod45 A B))
   (fst   : ∀{Γ A B} → Tm45 Γ (prod45 A B) → Tm45 Γ A)
   (snd   : ∀{Γ A B} → Tm45 Γ (prod45 A B) → Tm45 Γ B)
   (left  : ∀{Γ A B} → Tm45 Γ A → Tm45 Γ (sum45 A B))
   (right : ∀{Γ A B} → Tm45 Γ B → Tm45 Γ (sum45 A B))
   (case  : ∀{Γ A B C} → Tm45 Γ (sum45 A B) → Tm45 Γ (arr45 A C) → Tm45 Γ (arr45 B C) → Tm45 Γ C)
   (zero  : ∀{Γ} → Tm45 Γ nat45)
   (suc   : ∀{Γ} → Tm45 Γ nat45 → Tm45 Γ nat45)
   (rec   : ∀{Γ A} → Tm45 Γ nat45 → Tm45 Γ (arr45 nat45 (arr45 A A)) → Tm45 Γ A → Tm45 Γ A)
 → Tm45 Γ A

var45 : ∀{Γ A} → Var45 Γ A → Tm45 Γ A; var45
 = λ x Tm45 var45 lam app tt pair fst snd left right case zero suc rec →
     var45 x

lam45 : ∀{Γ A B} → Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B); lam45
 = λ t Tm45 var45 lam45 app tt pair fst snd left right case zero suc rec →
     lam45 (t Tm45 var45 lam45 app tt pair fst snd left right case zero suc rec)

app45 : ∀{Γ A B} → Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B; app45
 = λ t u Tm45 var45 lam45 app45 tt pair fst snd left right case zero suc rec →
     app45 (t Tm45 var45 lam45 app45 tt pair fst snd left right case zero suc rec)
         (u Tm45 var45 lam45 app45 tt pair fst snd left right case zero suc rec)

tt45 : ∀{Γ} → Tm45 Γ top45; tt45
 = λ Tm45 var45 lam45 app45 tt45 pair fst snd left right case zero suc rec → tt45

pair45 : ∀{Γ A B} → Tm45 Γ A → Tm45 Γ B → Tm45 Γ (prod45 A B); pair45
 = λ t u Tm45 var45 lam45 app45 tt45 pair45 fst snd left right case zero suc rec →
     pair45 (t Tm45 var45 lam45 app45 tt45 pair45 fst snd left right case zero suc rec)
          (u Tm45 var45 lam45 app45 tt45 pair45 fst snd left right case zero suc rec)

fst45 : ∀{Γ A B} → Tm45 Γ (prod45 A B) → Tm45 Γ A; fst45
 = λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd left right case zero suc rec →
     fst45 (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd left right case zero suc rec)

snd45 : ∀{Γ A B} → Tm45 Γ (prod45 A B) → Tm45 Γ B; snd45
 = λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left right case zero suc rec →
     snd45 (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left right case zero suc rec)

left45 : ∀{Γ A B} → Tm45 Γ A → Tm45 Γ (sum45 A B); left45
 = λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right case zero suc rec →
     left45 (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right case zero suc rec)

right45 : ∀{Γ A B} → Tm45 Γ B → Tm45 Γ (sum45 A B); right45
 = λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case zero suc rec →
     right45 (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case zero suc rec)

case45 : ∀{Γ A B C} → Tm45 Γ (sum45 A B) → Tm45 Γ (arr45 A C) → Tm45 Γ (arr45 B C) → Tm45 Γ C; case45
 = λ t u v Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero suc rec →
     case45 (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero suc rec)
           (u Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero suc rec)
           (v Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero suc rec)

zero45  : ∀{Γ} → Tm45 Γ nat45; zero45
 = λ Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc rec → zero45

suc45 : ∀{Γ} → Tm45 Γ nat45 → Tm45 Γ nat45; suc45
 = λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec →
   suc45 (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec)

rec45 : ∀{Γ A} → Tm45 Γ nat45 → Tm45 Γ (arr45 nat45 (arr45 A A)) → Tm45 Γ A → Tm45 Γ A; rec45
 = λ t u v Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec45 →
     rec45 (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec45)
         (u Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec45)
         (v Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec45)

v045 : ∀{Γ A} → Tm45 (snoc45 Γ A) A; v045
 = var45 vz45

v145 : ∀{Γ A B} → Tm45 (snoc45 (snoc45 Γ A) B) A; v145
 = var45 (vs45 vz45)

v245 : ∀{Γ A B C} → Tm45 (snoc45 (snoc45 (snoc45 Γ A) B) C) A; v245
 = var45 (vs45 (vs45 vz45))

v345 : ∀{Γ A B C D} → Tm45 (snoc45 (snoc45 (snoc45 (snoc45 Γ A) B) C) D) A; v345
 = var45 (vs45 (vs45 (vs45 vz45)))

tbool45 : Ty45; tbool45
 = sum45 top45 top45

true45 : ∀{Γ} → Tm45 Γ tbool45; true45
 = left45 tt45

tfalse45 : ∀{Γ} → Tm45 Γ tbool45; tfalse45
 = right45 tt45

ifthenelse45 : ∀{Γ A} → Tm45 Γ (arr45 tbool45 (arr45 A (arr45 A A))); ifthenelse45
 = lam45 (lam45 (lam45 (case45 v245 (lam45 v245) (lam45 v145))))

times445 : ∀{Γ A} → Tm45 Γ (arr45 (arr45 A A) (arr45 A A)); times445
  = lam45 (lam45 (app45 v145 (app45 v145 (app45 v145 (app45 v145 v045)))))

add45 : ∀{Γ} → Tm45 Γ (arr45 nat45 (arr45 nat45 nat45)); add45
 = lam45 (rec45 v045
       (lam45 (lam45 (lam45 (suc45 (app45 v145 v045)))))
       (lam45 v045))

mul45 : ∀{Γ} → Tm45 Γ (arr45 nat45 (arr45 nat45 nat45)); mul45
 = lam45 (rec45 v045
       (lam45 (lam45 (lam45 (app45 (app45 add45 (app45 v145 v045)) v045))))
       (lam45 zero45))

fact45 : ∀{Γ} → Tm45 Γ (arr45 nat45 nat45); fact45
 = lam45 (rec45 v045 (lam45 (lam45 (app45 (app45 mul45 (suc45 v145)) v045)))
        (suc45 zero45))
{-# OPTIONS --type-in-type #-}

Ty46 : Set
Ty46 =
   (Ty46         : Set)
   (nat top bot  : Ty46)
   (arr prod sum : Ty46 → Ty46 → Ty46)
 → Ty46

nat46 : Ty46; nat46 = λ _ nat46 _ _ _ _ _ → nat46
top46 : Ty46; top46 = λ _ _ top46 _ _ _ _ → top46
bot46 : Ty46; bot46 = λ _ _ _ bot46 _ _ _ → bot46

arr46 : Ty46 → Ty46 → Ty46; arr46
 = λ A B Ty46 nat46 top46 bot46 arr46 prod sum →
     arr46 (A Ty46 nat46 top46 bot46 arr46 prod sum) (B Ty46 nat46 top46 bot46 arr46 prod sum)

prod46 : Ty46 → Ty46 → Ty46; prod46
 = λ A B Ty46 nat46 top46 bot46 arr46 prod46 sum →
     prod46 (A Ty46 nat46 top46 bot46 arr46 prod46 sum) (B Ty46 nat46 top46 bot46 arr46 prod46 sum)

sum46 : Ty46 → Ty46 → Ty46; sum46
 = λ A B Ty46 nat46 top46 bot46 arr46 prod46 sum46 →
     sum46 (A Ty46 nat46 top46 bot46 arr46 prod46 sum46) (B Ty46 nat46 top46 bot46 arr46 prod46 sum46)

Con46 : Set; Con46
 = (Con46 : Set)
   (nil  : Con46)
   (snoc : Con46 → Ty46 → Con46)
 → Con46

nil46 : Con46; nil46
 = λ Con46 nil46 snoc → nil46

snoc46 : Con46 → Ty46 → Con46; snoc46
 = λ Γ A Con46 nil46 snoc46 → snoc46 (Γ Con46 nil46 snoc46) A

Var46 : Con46 → Ty46 → Set; Var46
 = λ Γ A →
   (Var46 : Con46 → Ty46 → Set)
   (vz  : ∀{Γ A} → Var46 (snoc46 Γ A) A)
   (vs  : ∀{Γ B A} → Var46 Γ A → Var46 (snoc46 Γ B) A)
 → Var46 Γ A

vz46 : ∀{Γ A} → Var46 (snoc46 Γ A) A; vz46
 = λ Var46 vz46 vs → vz46

vs46 : ∀{Γ B A} → Var46 Γ A → Var46 (snoc46 Γ B) A; vs46
 = λ x Var46 vz46 vs46 → vs46 (x Var46 vz46 vs46)

Tm46 : Con46 → Ty46 → Set; Tm46
 = λ Γ A →
   (Tm46  : Con46 → Ty46 → Set)
   (var   : ∀{Γ A} → Var46 Γ A → Tm46 Γ A)
   (lam   : ∀{Γ A B} → Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B))
   (app   : ∀{Γ A B} → Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B)
   (tt    : ∀{Γ} → Tm46 Γ top46)
   (pair  : ∀{Γ A B} → Tm46 Γ A → Tm46 Γ B → Tm46 Γ (prod46 A B))
   (fst   : ∀{Γ A B} → Tm46 Γ (prod46 A B) → Tm46 Γ A)
   (snd   : ∀{Γ A B} → Tm46 Γ (prod46 A B) → Tm46 Γ B)
   (left  : ∀{Γ A B} → Tm46 Γ A → Tm46 Γ (sum46 A B))
   (right : ∀{Γ A B} → Tm46 Γ B → Tm46 Γ (sum46 A B))
   (case  : ∀{Γ A B C} → Tm46 Γ (sum46 A B) → Tm46 Γ (arr46 A C) → Tm46 Γ (arr46 B C) → Tm46 Γ C)
   (zero  : ∀{Γ} → Tm46 Γ nat46)
   (suc   : ∀{Γ} → Tm46 Γ nat46 → Tm46 Γ nat46)
   (rec   : ∀{Γ A} → Tm46 Γ nat46 → Tm46 Γ (arr46 nat46 (arr46 A A)) → Tm46 Γ A → Tm46 Γ A)
 → Tm46 Γ A

var46 : ∀{Γ A} → Var46 Γ A → Tm46 Γ A; var46
 = λ x Tm46 var46 lam app tt pair fst snd left right case zero suc rec →
     var46 x

lam46 : ∀{Γ A B} → Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B); lam46
 = λ t Tm46 var46 lam46 app tt pair fst snd left right case zero suc rec →
     lam46 (t Tm46 var46 lam46 app tt pair fst snd left right case zero suc rec)

app46 : ∀{Γ A B} → Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B; app46
 = λ t u Tm46 var46 lam46 app46 tt pair fst snd left right case zero suc rec →
     app46 (t Tm46 var46 lam46 app46 tt pair fst snd left right case zero suc rec)
         (u Tm46 var46 lam46 app46 tt pair fst snd left right case zero suc rec)

tt46 : ∀{Γ} → Tm46 Γ top46; tt46
 = λ Tm46 var46 lam46 app46 tt46 pair fst snd left right case zero suc rec → tt46

pair46 : ∀{Γ A B} → Tm46 Γ A → Tm46 Γ B → Tm46 Γ (prod46 A B); pair46
 = λ t u Tm46 var46 lam46 app46 tt46 pair46 fst snd left right case zero suc rec →
     pair46 (t Tm46 var46 lam46 app46 tt46 pair46 fst snd left right case zero suc rec)
          (u Tm46 var46 lam46 app46 tt46 pair46 fst snd left right case zero suc rec)

fst46 : ∀{Γ A B} → Tm46 Γ (prod46 A B) → Tm46 Γ A; fst46
 = λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd left right case zero suc rec →
     fst46 (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd left right case zero suc rec)

snd46 : ∀{Γ A B} → Tm46 Γ (prod46 A B) → Tm46 Γ B; snd46
 = λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left right case zero suc rec →
     snd46 (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left right case zero suc rec)

left46 : ∀{Γ A B} → Tm46 Γ A → Tm46 Γ (sum46 A B); left46
 = λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right case zero suc rec →
     left46 (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right case zero suc rec)

right46 : ∀{Γ A B} → Tm46 Γ B → Tm46 Γ (sum46 A B); right46
 = λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case zero suc rec →
     right46 (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case zero suc rec)

case46 : ∀{Γ A B C} → Tm46 Γ (sum46 A B) → Tm46 Γ (arr46 A C) → Tm46 Γ (arr46 B C) → Tm46 Γ C; case46
 = λ t u v Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero suc rec →
     case46 (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero suc rec)
           (u Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero suc rec)
           (v Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero suc rec)

zero46  : ∀{Γ} → Tm46 Γ nat46; zero46
 = λ Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc rec → zero46

suc46 : ∀{Γ} → Tm46 Γ nat46 → Tm46 Γ nat46; suc46
 = λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec →
   suc46 (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec)

rec46 : ∀{Γ A} → Tm46 Γ nat46 → Tm46 Γ (arr46 nat46 (arr46 A A)) → Tm46 Γ A → Tm46 Γ A; rec46
 = λ t u v Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec46 →
     rec46 (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec46)
         (u Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec46)
         (v Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec46)

v046 : ∀{Γ A} → Tm46 (snoc46 Γ A) A; v046
 = var46 vz46

v146 : ∀{Γ A B} → Tm46 (snoc46 (snoc46 Γ A) B) A; v146
 = var46 (vs46 vz46)

v246 : ∀{Γ A B C} → Tm46 (snoc46 (snoc46 (snoc46 Γ A) B) C) A; v246
 = var46 (vs46 (vs46 vz46))

v346 : ∀{Γ A B C D} → Tm46 (snoc46 (snoc46 (snoc46 (snoc46 Γ A) B) C) D) A; v346
 = var46 (vs46 (vs46 (vs46 vz46)))

tbool46 : Ty46; tbool46
 = sum46 top46 top46

true46 : ∀{Γ} → Tm46 Γ tbool46; true46
 = left46 tt46

tfalse46 : ∀{Γ} → Tm46 Γ tbool46; tfalse46
 = right46 tt46

ifthenelse46 : ∀{Γ A} → Tm46 Γ (arr46 tbool46 (arr46 A (arr46 A A))); ifthenelse46
 = lam46 (lam46 (lam46 (case46 v246 (lam46 v246) (lam46 v146))))

times446 : ∀{Γ A} → Tm46 Γ (arr46 (arr46 A A) (arr46 A A)); times446
  = lam46 (lam46 (app46 v146 (app46 v146 (app46 v146 (app46 v146 v046)))))

add46 : ∀{Γ} → Tm46 Γ (arr46 nat46 (arr46 nat46 nat46)); add46
 = lam46 (rec46 v046
       (lam46 (lam46 (lam46 (suc46 (app46 v146 v046)))))
       (lam46 v046))

mul46 : ∀{Γ} → Tm46 Γ (arr46 nat46 (arr46 nat46 nat46)); mul46
 = lam46 (rec46 v046
       (lam46 (lam46 (lam46 (app46 (app46 add46 (app46 v146 v046)) v046))))
       (lam46 zero46))

fact46 : ∀{Γ} → Tm46 Γ (arr46 nat46 nat46); fact46
 = lam46 (rec46 v046 (lam46 (lam46 (app46 (app46 mul46 (suc46 v146)) v046)))
        (suc46 zero46))
{-# OPTIONS --type-in-type #-}

Ty47 : Set
Ty47 =
   (Ty47         : Set)
   (nat top bot  : Ty47)
   (arr prod sum : Ty47 → Ty47 → Ty47)
 → Ty47

nat47 : Ty47; nat47 = λ _ nat47 _ _ _ _ _ → nat47
top47 : Ty47; top47 = λ _ _ top47 _ _ _ _ → top47
bot47 : Ty47; bot47 = λ _ _ _ bot47 _ _ _ → bot47

arr47 : Ty47 → Ty47 → Ty47; arr47
 = λ A B Ty47 nat47 top47 bot47 arr47 prod sum →
     arr47 (A Ty47 nat47 top47 bot47 arr47 prod sum) (B Ty47 nat47 top47 bot47 arr47 prod sum)

prod47 : Ty47 → Ty47 → Ty47; prod47
 = λ A B Ty47 nat47 top47 bot47 arr47 prod47 sum →
     prod47 (A Ty47 nat47 top47 bot47 arr47 prod47 sum) (B Ty47 nat47 top47 bot47 arr47 prod47 sum)

sum47 : Ty47 → Ty47 → Ty47; sum47
 = λ A B Ty47 nat47 top47 bot47 arr47 prod47 sum47 →
     sum47 (A Ty47 nat47 top47 bot47 arr47 prod47 sum47) (B Ty47 nat47 top47 bot47 arr47 prod47 sum47)

Con47 : Set; Con47
 = (Con47 : Set)
   (nil  : Con47)
   (snoc : Con47 → Ty47 → Con47)
 → Con47

nil47 : Con47; nil47
 = λ Con47 nil47 snoc → nil47

snoc47 : Con47 → Ty47 → Con47; snoc47
 = λ Γ A Con47 nil47 snoc47 → snoc47 (Γ Con47 nil47 snoc47) A

Var47 : Con47 → Ty47 → Set; Var47
 = λ Γ A →
   (Var47 : Con47 → Ty47 → Set)
   (vz  : ∀{Γ A} → Var47 (snoc47 Γ A) A)
   (vs  : ∀{Γ B A} → Var47 Γ A → Var47 (snoc47 Γ B) A)
 → Var47 Γ A

vz47 : ∀{Γ A} → Var47 (snoc47 Γ A) A; vz47
 = λ Var47 vz47 vs → vz47

vs47 : ∀{Γ B A} → Var47 Γ A → Var47 (snoc47 Γ B) A; vs47
 = λ x Var47 vz47 vs47 → vs47 (x Var47 vz47 vs47)

Tm47 : Con47 → Ty47 → Set; Tm47
 = λ Γ A →
   (Tm47  : Con47 → Ty47 → Set)
   (var   : ∀{Γ A} → Var47 Γ A → Tm47 Γ A)
   (lam   : ∀{Γ A B} → Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B))
   (app   : ∀{Γ A B} → Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B)
   (tt    : ∀{Γ} → Tm47 Γ top47)
   (pair  : ∀{Γ A B} → Tm47 Γ A → Tm47 Γ B → Tm47 Γ (prod47 A B))
   (fst   : ∀{Γ A B} → Tm47 Γ (prod47 A B) → Tm47 Γ A)
   (snd   : ∀{Γ A B} → Tm47 Γ (prod47 A B) → Tm47 Γ B)
   (left  : ∀{Γ A B} → Tm47 Γ A → Tm47 Γ (sum47 A B))
   (right : ∀{Γ A B} → Tm47 Γ B → Tm47 Γ (sum47 A B))
   (case  : ∀{Γ A B C} → Tm47 Γ (sum47 A B) → Tm47 Γ (arr47 A C) → Tm47 Γ (arr47 B C) → Tm47 Γ C)
   (zero  : ∀{Γ} → Tm47 Γ nat47)
   (suc   : ∀{Γ} → Tm47 Γ nat47 → Tm47 Γ nat47)
   (rec   : ∀{Γ A} → Tm47 Γ nat47 → Tm47 Γ (arr47 nat47 (arr47 A A)) → Tm47 Γ A → Tm47 Γ A)
 → Tm47 Γ A

var47 : ∀{Γ A} → Var47 Γ A → Tm47 Γ A; var47
 = λ x Tm47 var47 lam app tt pair fst snd left right case zero suc rec →
     var47 x

lam47 : ∀{Γ A B} → Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B); lam47
 = λ t Tm47 var47 lam47 app tt pair fst snd left right case zero suc rec →
     lam47 (t Tm47 var47 lam47 app tt pair fst snd left right case zero suc rec)

app47 : ∀{Γ A B} → Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B; app47
 = λ t u Tm47 var47 lam47 app47 tt pair fst snd left right case zero suc rec →
     app47 (t Tm47 var47 lam47 app47 tt pair fst snd left right case zero suc rec)
         (u Tm47 var47 lam47 app47 tt pair fst snd left right case zero suc rec)

tt47 : ∀{Γ} → Tm47 Γ top47; tt47
 = λ Tm47 var47 lam47 app47 tt47 pair fst snd left right case zero suc rec → tt47

pair47 : ∀{Γ A B} → Tm47 Γ A → Tm47 Γ B → Tm47 Γ (prod47 A B); pair47
 = λ t u Tm47 var47 lam47 app47 tt47 pair47 fst snd left right case zero suc rec →
     pair47 (t Tm47 var47 lam47 app47 tt47 pair47 fst snd left right case zero suc rec)
          (u Tm47 var47 lam47 app47 tt47 pair47 fst snd left right case zero suc rec)

fst47 : ∀{Γ A B} → Tm47 Γ (prod47 A B) → Tm47 Γ A; fst47
 = λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd left right case zero suc rec →
     fst47 (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd left right case zero suc rec)

snd47 : ∀{Γ A B} → Tm47 Γ (prod47 A B) → Tm47 Γ B; snd47
 = λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left right case zero suc rec →
     snd47 (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left right case zero suc rec)

left47 : ∀{Γ A B} → Tm47 Γ A → Tm47 Γ (sum47 A B); left47
 = λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right case zero suc rec →
     left47 (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right case zero suc rec)

right47 : ∀{Γ A B} → Tm47 Γ B → Tm47 Γ (sum47 A B); right47
 = λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case zero suc rec →
     right47 (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case zero suc rec)

case47 : ∀{Γ A B C} → Tm47 Γ (sum47 A B) → Tm47 Γ (arr47 A C) → Tm47 Γ (arr47 B C) → Tm47 Γ C; case47
 = λ t u v Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero suc rec →
     case47 (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero suc rec)
           (u Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero suc rec)
           (v Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero suc rec)

zero47  : ∀{Γ} → Tm47 Γ nat47; zero47
 = λ Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc rec → zero47

suc47 : ∀{Γ} → Tm47 Γ nat47 → Tm47 Γ nat47; suc47
 = λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec →
   suc47 (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec)

rec47 : ∀{Γ A} → Tm47 Γ nat47 → Tm47 Γ (arr47 nat47 (arr47 A A)) → Tm47 Γ A → Tm47 Γ A; rec47
 = λ t u v Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec47 →
     rec47 (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec47)
         (u Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec47)
         (v Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec47)

v047 : ∀{Γ A} → Tm47 (snoc47 Γ A) A; v047
 = var47 vz47

v147 : ∀{Γ A B} → Tm47 (snoc47 (snoc47 Γ A) B) A; v147
 = var47 (vs47 vz47)

v247 : ∀{Γ A B C} → Tm47 (snoc47 (snoc47 (snoc47 Γ A) B) C) A; v247
 = var47 (vs47 (vs47 vz47))

v347 : ∀{Γ A B C D} → Tm47 (snoc47 (snoc47 (snoc47 (snoc47 Γ A) B) C) D) A; v347
 = var47 (vs47 (vs47 (vs47 vz47)))

tbool47 : Ty47; tbool47
 = sum47 top47 top47

true47 : ∀{Γ} → Tm47 Γ tbool47; true47
 = left47 tt47

tfalse47 : ∀{Γ} → Tm47 Γ tbool47; tfalse47
 = right47 tt47

ifthenelse47 : ∀{Γ A} → Tm47 Γ (arr47 tbool47 (arr47 A (arr47 A A))); ifthenelse47
 = lam47 (lam47 (lam47 (case47 v247 (lam47 v247) (lam47 v147))))

times447 : ∀{Γ A} → Tm47 Γ (arr47 (arr47 A A) (arr47 A A)); times447
  = lam47 (lam47 (app47 v147 (app47 v147 (app47 v147 (app47 v147 v047)))))

add47 : ∀{Γ} → Tm47 Γ (arr47 nat47 (arr47 nat47 nat47)); add47
 = lam47 (rec47 v047
       (lam47 (lam47 (lam47 (suc47 (app47 v147 v047)))))
       (lam47 v047))

mul47 : ∀{Γ} → Tm47 Γ (arr47 nat47 (arr47 nat47 nat47)); mul47
 = lam47 (rec47 v047
       (lam47 (lam47 (lam47 (app47 (app47 add47 (app47 v147 v047)) v047))))
       (lam47 zero47))

fact47 : ∀{Γ} → Tm47 Γ (arr47 nat47 nat47); fact47
 = lam47 (rec47 v047 (lam47 (lam47 (app47 (app47 mul47 (suc47 v147)) v047)))
        (suc47 zero47))
{-# OPTIONS --type-in-type #-}

Ty48 : Set
Ty48 =
   (Ty48         : Set)
   (nat top bot  : Ty48)
   (arr prod sum : Ty48 → Ty48 → Ty48)
 → Ty48

nat48 : Ty48; nat48 = λ _ nat48 _ _ _ _ _ → nat48
top48 : Ty48; top48 = λ _ _ top48 _ _ _ _ → top48
bot48 : Ty48; bot48 = λ _ _ _ bot48 _ _ _ → bot48

arr48 : Ty48 → Ty48 → Ty48; arr48
 = λ A B Ty48 nat48 top48 bot48 arr48 prod sum →
     arr48 (A Ty48 nat48 top48 bot48 arr48 prod sum) (B Ty48 nat48 top48 bot48 arr48 prod sum)

prod48 : Ty48 → Ty48 → Ty48; prod48
 = λ A B Ty48 nat48 top48 bot48 arr48 prod48 sum →
     prod48 (A Ty48 nat48 top48 bot48 arr48 prod48 sum) (B Ty48 nat48 top48 bot48 arr48 prod48 sum)

sum48 : Ty48 → Ty48 → Ty48; sum48
 = λ A B Ty48 nat48 top48 bot48 arr48 prod48 sum48 →
     sum48 (A Ty48 nat48 top48 bot48 arr48 prod48 sum48) (B Ty48 nat48 top48 bot48 arr48 prod48 sum48)

Con48 : Set; Con48
 = (Con48 : Set)
   (nil  : Con48)
   (snoc : Con48 → Ty48 → Con48)
 → Con48

nil48 : Con48; nil48
 = λ Con48 nil48 snoc → nil48

snoc48 : Con48 → Ty48 → Con48; snoc48
 = λ Γ A Con48 nil48 snoc48 → snoc48 (Γ Con48 nil48 snoc48) A

Var48 : Con48 → Ty48 → Set; Var48
 = λ Γ A →
   (Var48 : Con48 → Ty48 → Set)
   (vz  : ∀{Γ A} → Var48 (snoc48 Γ A) A)
   (vs  : ∀{Γ B A} → Var48 Γ A → Var48 (snoc48 Γ B) A)
 → Var48 Γ A

vz48 : ∀{Γ A} → Var48 (snoc48 Γ A) A; vz48
 = λ Var48 vz48 vs → vz48

vs48 : ∀{Γ B A} → Var48 Γ A → Var48 (snoc48 Γ B) A; vs48
 = λ x Var48 vz48 vs48 → vs48 (x Var48 vz48 vs48)

Tm48 : Con48 → Ty48 → Set; Tm48
 = λ Γ A →
   (Tm48  : Con48 → Ty48 → Set)
   (var   : ∀{Γ A} → Var48 Γ A → Tm48 Γ A)
   (lam   : ∀{Γ A B} → Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B))
   (app   : ∀{Γ A B} → Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B)
   (tt    : ∀{Γ} → Tm48 Γ top48)
   (pair  : ∀{Γ A B} → Tm48 Γ A → Tm48 Γ B → Tm48 Γ (prod48 A B))
   (fst   : ∀{Γ A B} → Tm48 Γ (prod48 A B) → Tm48 Γ A)
   (snd   : ∀{Γ A B} → Tm48 Γ (prod48 A B) → Tm48 Γ B)
   (left  : ∀{Γ A B} → Tm48 Γ A → Tm48 Γ (sum48 A B))
   (right : ∀{Γ A B} → Tm48 Γ B → Tm48 Γ (sum48 A B))
   (case  : ∀{Γ A B C} → Tm48 Γ (sum48 A B) → Tm48 Γ (arr48 A C) → Tm48 Γ (arr48 B C) → Tm48 Γ C)
   (zero  : ∀{Γ} → Tm48 Γ nat48)
   (suc   : ∀{Γ} → Tm48 Γ nat48 → Tm48 Γ nat48)
   (rec   : ∀{Γ A} → Tm48 Γ nat48 → Tm48 Γ (arr48 nat48 (arr48 A A)) → Tm48 Γ A → Tm48 Γ A)
 → Tm48 Γ A

var48 : ∀{Γ A} → Var48 Γ A → Tm48 Γ A; var48
 = λ x Tm48 var48 lam app tt pair fst snd left right case zero suc rec →
     var48 x

lam48 : ∀{Γ A B} → Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B); lam48
 = λ t Tm48 var48 lam48 app tt pair fst snd left right case zero suc rec →
     lam48 (t Tm48 var48 lam48 app tt pair fst snd left right case zero suc rec)

app48 : ∀{Γ A B} → Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B; app48
 = λ t u Tm48 var48 lam48 app48 tt pair fst snd left right case zero suc rec →
     app48 (t Tm48 var48 lam48 app48 tt pair fst snd left right case zero suc rec)
         (u Tm48 var48 lam48 app48 tt pair fst snd left right case zero suc rec)

tt48 : ∀{Γ} → Tm48 Γ top48; tt48
 = λ Tm48 var48 lam48 app48 tt48 pair fst snd left right case zero suc rec → tt48

pair48 : ∀{Γ A B} → Tm48 Γ A → Tm48 Γ B → Tm48 Γ (prod48 A B); pair48
 = λ t u Tm48 var48 lam48 app48 tt48 pair48 fst snd left right case zero suc rec →
     pair48 (t Tm48 var48 lam48 app48 tt48 pair48 fst snd left right case zero suc rec)
          (u Tm48 var48 lam48 app48 tt48 pair48 fst snd left right case zero suc rec)

fst48 : ∀{Γ A B} → Tm48 Γ (prod48 A B) → Tm48 Γ A; fst48
 = λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd left right case zero suc rec →
     fst48 (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd left right case zero suc rec)

snd48 : ∀{Γ A B} → Tm48 Γ (prod48 A B) → Tm48 Γ B; snd48
 = λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left right case zero suc rec →
     snd48 (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left right case zero suc rec)

left48 : ∀{Γ A B} → Tm48 Γ A → Tm48 Γ (sum48 A B); left48
 = λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right case zero suc rec →
     left48 (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right case zero suc rec)

right48 : ∀{Γ A B} → Tm48 Γ B → Tm48 Γ (sum48 A B); right48
 = λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case zero suc rec →
     right48 (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case zero suc rec)

case48 : ∀{Γ A B C} → Tm48 Γ (sum48 A B) → Tm48 Γ (arr48 A C) → Tm48 Γ (arr48 B C) → Tm48 Γ C; case48
 = λ t u v Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero suc rec →
     case48 (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero suc rec)
           (u Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero suc rec)
           (v Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero suc rec)

zero48  : ∀{Γ} → Tm48 Γ nat48; zero48
 = λ Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc rec → zero48

suc48 : ∀{Γ} → Tm48 Γ nat48 → Tm48 Γ nat48; suc48
 = λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec →
   suc48 (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec)

rec48 : ∀{Γ A} → Tm48 Γ nat48 → Tm48 Γ (arr48 nat48 (arr48 A A)) → Tm48 Γ A → Tm48 Γ A; rec48
 = λ t u v Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec48 →
     rec48 (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec48)
         (u Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec48)
         (v Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec48)

v048 : ∀{Γ A} → Tm48 (snoc48 Γ A) A; v048
 = var48 vz48

v148 : ∀{Γ A B} → Tm48 (snoc48 (snoc48 Γ A) B) A; v148
 = var48 (vs48 vz48)

v248 : ∀{Γ A B C} → Tm48 (snoc48 (snoc48 (snoc48 Γ A) B) C) A; v248
 = var48 (vs48 (vs48 vz48))

v348 : ∀{Γ A B C D} → Tm48 (snoc48 (snoc48 (snoc48 (snoc48 Γ A) B) C) D) A; v348
 = var48 (vs48 (vs48 (vs48 vz48)))

tbool48 : Ty48; tbool48
 = sum48 top48 top48

true48 : ∀{Γ} → Tm48 Γ tbool48; true48
 = left48 tt48

tfalse48 : ∀{Γ} → Tm48 Γ tbool48; tfalse48
 = right48 tt48

ifthenelse48 : ∀{Γ A} → Tm48 Γ (arr48 tbool48 (arr48 A (arr48 A A))); ifthenelse48
 = lam48 (lam48 (lam48 (case48 v248 (lam48 v248) (lam48 v148))))

times448 : ∀{Γ A} → Tm48 Γ (arr48 (arr48 A A) (arr48 A A)); times448
  = lam48 (lam48 (app48 v148 (app48 v148 (app48 v148 (app48 v148 v048)))))

add48 : ∀{Γ} → Tm48 Γ (arr48 nat48 (arr48 nat48 nat48)); add48
 = lam48 (rec48 v048
       (lam48 (lam48 (lam48 (suc48 (app48 v148 v048)))))
       (lam48 v048))

mul48 : ∀{Γ} → Tm48 Γ (arr48 nat48 (arr48 nat48 nat48)); mul48
 = lam48 (rec48 v048
       (lam48 (lam48 (lam48 (app48 (app48 add48 (app48 v148 v048)) v048))))
       (lam48 zero48))

fact48 : ∀{Γ} → Tm48 Γ (arr48 nat48 nat48); fact48
 = lam48 (rec48 v048 (lam48 (lam48 (app48 (app48 mul48 (suc48 v148)) v048)))
        (suc48 zero48))
{-# OPTIONS --type-in-type #-}

Ty49 : Set
Ty49 =
   (Ty49         : Set)
   (nat top bot  : Ty49)
   (arr prod sum : Ty49 → Ty49 → Ty49)
 → Ty49

nat49 : Ty49; nat49 = λ _ nat49 _ _ _ _ _ → nat49
top49 : Ty49; top49 = λ _ _ top49 _ _ _ _ → top49
bot49 : Ty49; bot49 = λ _ _ _ bot49 _ _ _ → bot49

arr49 : Ty49 → Ty49 → Ty49; arr49
 = λ A B Ty49 nat49 top49 bot49 arr49 prod sum →
     arr49 (A Ty49 nat49 top49 bot49 arr49 prod sum) (B Ty49 nat49 top49 bot49 arr49 prod sum)

prod49 : Ty49 → Ty49 → Ty49; prod49
 = λ A B Ty49 nat49 top49 bot49 arr49 prod49 sum →
     prod49 (A Ty49 nat49 top49 bot49 arr49 prod49 sum) (B Ty49 nat49 top49 bot49 arr49 prod49 sum)

sum49 : Ty49 → Ty49 → Ty49; sum49
 = λ A B Ty49 nat49 top49 bot49 arr49 prod49 sum49 →
     sum49 (A Ty49 nat49 top49 bot49 arr49 prod49 sum49) (B Ty49 nat49 top49 bot49 arr49 prod49 sum49)

Con49 : Set; Con49
 = (Con49 : Set)
   (nil  : Con49)
   (snoc : Con49 → Ty49 → Con49)
 → Con49

nil49 : Con49; nil49
 = λ Con49 nil49 snoc → nil49

snoc49 : Con49 → Ty49 → Con49; snoc49
 = λ Γ A Con49 nil49 snoc49 → snoc49 (Γ Con49 nil49 snoc49) A

Var49 : Con49 → Ty49 → Set; Var49
 = λ Γ A →
   (Var49 : Con49 → Ty49 → Set)
   (vz  : ∀{Γ A} → Var49 (snoc49 Γ A) A)
   (vs  : ∀{Γ B A} → Var49 Γ A → Var49 (snoc49 Γ B) A)
 → Var49 Γ A

vz49 : ∀{Γ A} → Var49 (snoc49 Γ A) A; vz49
 = λ Var49 vz49 vs → vz49

vs49 : ∀{Γ B A} → Var49 Γ A → Var49 (snoc49 Γ B) A; vs49
 = λ x Var49 vz49 vs49 → vs49 (x Var49 vz49 vs49)

Tm49 : Con49 → Ty49 → Set; Tm49
 = λ Γ A →
   (Tm49  : Con49 → Ty49 → Set)
   (var   : ∀{Γ A} → Var49 Γ A → Tm49 Γ A)
   (lam   : ∀{Γ A B} → Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B))
   (app   : ∀{Γ A B} → Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B)
   (tt    : ∀{Γ} → Tm49 Γ top49)
   (pair  : ∀{Γ A B} → Tm49 Γ A → Tm49 Γ B → Tm49 Γ (prod49 A B))
   (fst   : ∀{Γ A B} → Tm49 Γ (prod49 A B) → Tm49 Γ A)
   (snd   : ∀{Γ A B} → Tm49 Γ (prod49 A B) → Tm49 Γ B)
   (left  : ∀{Γ A B} → Tm49 Γ A → Tm49 Γ (sum49 A B))
   (right : ∀{Γ A B} → Tm49 Γ B → Tm49 Γ (sum49 A B))
   (case  : ∀{Γ A B C} → Tm49 Γ (sum49 A B) → Tm49 Γ (arr49 A C) → Tm49 Γ (arr49 B C) → Tm49 Γ C)
   (zero  : ∀{Γ} → Tm49 Γ nat49)
   (suc   : ∀{Γ} → Tm49 Γ nat49 → Tm49 Γ nat49)
   (rec   : ∀{Γ A} → Tm49 Γ nat49 → Tm49 Γ (arr49 nat49 (arr49 A A)) → Tm49 Γ A → Tm49 Γ A)
 → Tm49 Γ A

var49 : ∀{Γ A} → Var49 Γ A → Tm49 Γ A; var49
 = λ x Tm49 var49 lam app tt pair fst snd left right case zero suc rec →
     var49 x

lam49 : ∀{Γ A B} → Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B); lam49
 = λ t Tm49 var49 lam49 app tt pair fst snd left right case zero suc rec →
     lam49 (t Tm49 var49 lam49 app tt pair fst snd left right case zero suc rec)

app49 : ∀{Γ A B} → Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B; app49
 = λ t u Tm49 var49 lam49 app49 tt pair fst snd left right case zero suc rec →
     app49 (t Tm49 var49 lam49 app49 tt pair fst snd left right case zero suc rec)
         (u Tm49 var49 lam49 app49 tt pair fst snd left right case zero suc rec)

tt49 : ∀{Γ} → Tm49 Γ top49; tt49
 = λ Tm49 var49 lam49 app49 tt49 pair fst snd left right case zero suc rec → tt49

pair49 : ∀{Γ A B} → Tm49 Γ A → Tm49 Γ B → Tm49 Γ (prod49 A B); pair49
 = λ t u Tm49 var49 lam49 app49 tt49 pair49 fst snd left right case zero suc rec →
     pair49 (t Tm49 var49 lam49 app49 tt49 pair49 fst snd left right case zero suc rec)
          (u Tm49 var49 lam49 app49 tt49 pair49 fst snd left right case zero suc rec)

fst49 : ∀{Γ A B} → Tm49 Γ (prod49 A B) → Tm49 Γ A; fst49
 = λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd left right case zero suc rec →
     fst49 (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd left right case zero suc rec)

snd49 : ∀{Γ A B} → Tm49 Γ (prod49 A B) → Tm49 Γ B; snd49
 = λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left right case zero suc rec →
     snd49 (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left right case zero suc rec)

left49 : ∀{Γ A B} → Tm49 Γ A → Tm49 Γ (sum49 A B); left49
 = λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right case zero suc rec →
     left49 (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right case zero suc rec)

right49 : ∀{Γ A B} → Tm49 Γ B → Tm49 Γ (sum49 A B); right49
 = λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case zero suc rec →
     right49 (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case zero suc rec)

case49 : ∀{Γ A B C} → Tm49 Γ (sum49 A B) → Tm49 Γ (arr49 A C) → Tm49 Γ (arr49 B C) → Tm49 Γ C; case49
 = λ t u v Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero suc rec →
     case49 (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero suc rec)
           (u Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero suc rec)
           (v Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero suc rec)

zero49  : ∀{Γ} → Tm49 Γ nat49; zero49
 = λ Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc rec → zero49

suc49 : ∀{Γ} → Tm49 Γ nat49 → Tm49 Γ nat49; suc49
 = λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec →
   suc49 (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec)

rec49 : ∀{Γ A} → Tm49 Γ nat49 → Tm49 Γ (arr49 nat49 (arr49 A A)) → Tm49 Γ A → Tm49 Γ A; rec49
 = λ t u v Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec49 →
     rec49 (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec49)
         (u Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec49)
         (v Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec49)

v049 : ∀{Γ A} → Tm49 (snoc49 Γ A) A; v049
 = var49 vz49

v149 : ∀{Γ A B} → Tm49 (snoc49 (snoc49 Γ A) B) A; v149
 = var49 (vs49 vz49)

v249 : ∀{Γ A B C} → Tm49 (snoc49 (snoc49 (snoc49 Γ A) B) C) A; v249
 = var49 (vs49 (vs49 vz49))

v349 : ∀{Γ A B C D} → Tm49 (snoc49 (snoc49 (snoc49 (snoc49 Γ A) B) C) D) A; v349
 = var49 (vs49 (vs49 (vs49 vz49)))

tbool49 : Ty49; tbool49
 = sum49 top49 top49

true49 : ∀{Γ} → Tm49 Γ tbool49; true49
 = left49 tt49

tfalse49 : ∀{Γ} → Tm49 Γ tbool49; tfalse49
 = right49 tt49

ifthenelse49 : ∀{Γ A} → Tm49 Γ (arr49 tbool49 (arr49 A (arr49 A A))); ifthenelse49
 = lam49 (lam49 (lam49 (case49 v249 (lam49 v249) (lam49 v149))))

times449 : ∀{Γ A} → Tm49 Γ (arr49 (arr49 A A) (arr49 A A)); times449
  = lam49 (lam49 (app49 v149 (app49 v149 (app49 v149 (app49 v149 v049)))))

add49 : ∀{Γ} → Tm49 Γ (arr49 nat49 (arr49 nat49 nat49)); add49
 = lam49 (rec49 v049
       (lam49 (lam49 (lam49 (suc49 (app49 v149 v049)))))
       (lam49 v049))

mul49 : ∀{Γ} → Tm49 Γ (arr49 nat49 (arr49 nat49 nat49)); mul49
 = lam49 (rec49 v049
       (lam49 (lam49 (lam49 (app49 (app49 add49 (app49 v149 v049)) v049))))
       (lam49 zero49))

fact49 : ∀{Γ} → Tm49 Γ (arr49 nat49 nat49); fact49
 = lam49 (rec49 v049 (lam49 (lam49 (app49 (app49 mul49 (suc49 v149)) v049)))
        (suc49 zero49))
{-# OPTIONS --type-in-type #-}

Ty50 : Set
Ty50 =
   (Ty50         : Set)
   (nat top bot  : Ty50)
   (arr prod sum : Ty50 → Ty50 → Ty50)
 → Ty50

nat50 : Ty50; nat50 = λ _ nat50 _ _ _ _ _ → nat50
top50 : Ty50; top50 = λ _ _ top50 _ _ _ _ → top50
bot50 : Ty50; bot50 = λ _ _ _ bot50 _ _ _ → bot50

arr50 : Ty50 → Ty50 → Ty50; arr50
 = λ A B Ty50 nat50 top50 bot50 arr50 prod sum →
     arr50 (A Ty50 nat50 top50 bot50 arr50 prod sum) (B Ty50 nat50 top50 bot50 arr50 prod sum)

prod50 : Ty50 → Ty50 → Ty50; prod50
 = λ A B Ty50 nat50 top50 bot50 arr50 prod50 sum →
     prod50 (A Ty50 nat50 top50 bot50 arr50 prod50 sum) (B Ty50 nat50 top50 bot50 arr50 prod50 sum)

sum50 : Ty50 → Ty50 → Ty50; sum50
 = λ A B Ty50 nat50 top50 bot50 arr50 prod50 sum50 →
     sum50 (A Ty50 nat50 top50 bot50 arr50 prod50 sum50) (B Ty50 nat50 top50 bot50 arr50 prod50 sum50)

Con50 : Set; Con50
 = (Con50 : Set)
   (nil  : Con50)
   (snoc : Con50 → Ty50 → Con50)
 → Con50

nil50 : Con50; nil50
 = λ Con50 nil50 snoc → nil50

snoc50 : Con50 → Ty50 → Con50; snoc50
 = λ Γ A Con50 nil50 snoc50 → snoc50 (Γ Con50 nil50 snoc50) A

Var50 : Con50 → Ty50 → Set; Var50
 = λ Γ A →
   (Var50 : Con50 → Ty50 → Set)
   (vz  : ∀{Γ A} → Var50 (snoc50 Γ A) A)
   (vs  : ∀{Γ B A} → Var50 Γ A → Var50 (snoc50 Γ B) A)
 → Var50 Γ A

vz50 : ∀{Γ A} → Var50 (snoc50 Γ A) A; vz50
 = λ Var50 vz50 vs → vz50

vs50 : ∀{Γ B A} → Var50 Γ A → Var50 (snoc50 Γ B) A; vs50
 = λ x Var50 vz50 vs50 → vs50 (x Var50 vz50 vs50)

Tm50 : Con50 → Ty50 → Set; Tm50
 = λ Γ A →
   (Tm50  : Con50 → Ty50 → Set)
   (var   : ∀{Γ A} → Var50 Γ A → Tm50 Γ A)
   (lam   : ∀{Γ A B} → Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B))
   (app   : ∀{Γ A B} → Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B)
   (tt    : ∀{Γ} → Tm50 Γ top50)
   (pair  : ∀{Γ A B} → Tm50 Γ A → Tm50 Γ B → Tm50 Γ (prod50 A B))
   (fst   : ∀{Γ A B} → Tm50 Γ (prod50 A B) → Tm50 Γ A)
   (snd   : ∀{Γ A B} → Tm50 Γ (prod50 A B) → Tm50 Γ B)
   (left  : ∀{Γ A B} → Tm50 Γ A → Tm50 Γ (sum50 A B))
   (right : ∀{Γ A B} → Tm50 Γ B → Tm50 Γ (sum50 A B))
   (case  : ∀{Γ A B C} → Tm50 Γ (sum50 A B) → Tm50 Γ (arr50 A C) → Tm50 Γ (arr50 B C) → Tm50 Γ C)
   (zero  : ∀{Γ} → Tm50 Γ nat50)
   (suc   : ∀{Γ} → Tm50 Γ nat50 → Tm50 Γ nat50)
   (rec   : ∀{Γ A} → Tm50 Γ nat50 → Tm50 Γ (arr50 nat50 (arr50 A A)) → Tm50 Γ A → Tm50 Γ A)
 → Tm50 Γ A

var50 : ∀{Γ A} → Var50 Γ A → Tm50 Γ A; var50
 = λ x Tm50 var50 lam app tt pair fst snd left right case zero suc rec →
     var50 x

lam50 : ∀{Γ A B} → Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B); lam50
 = λ t Tm50 var50 lam50 app tt pair fst snd left right case zero suc rec →
     lam50 (t Tm50 var50 lam50 app tt pair fst snd left right case zero suc rec)

app50 : ∀{Γ A B} → Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B; app50
 = λ t u Tm50 var50 lam50 app50 tt pair fst snd left right case zero suc rec →
     app50 (t Tm50 var50 lam50 app50 tt pair fst snd left right case zero suc rec)
         (u Tm50 var50 lam50 app50 tt pair fst snd left right case zero suc rec)

tt50 : ∀{Γ} → Tm50 Γ top50; tt50
 = λ Tm50 var50 lam50 app50 tt50 pair fst snd left right case zero suc rec → tt50

pair50 : ∀{Γ A B} → Tm50 Γ A → Tm50 Γ B → Tm50 Γ (prod50 A B); pair50
 = λ t u Tm50 var50 lam50 app50 tt50 pair50 fst snd left right case zero suc rec →
     pair50 (t Tm50 var50 lam50 app50 tt50 pair50 fst snd left right case zero suc rec)
          (u Tm50 var50 lam50 app50 tt50 pair50 fst snd left right case zero suc rec)

fst50 : ∀{Γ A B} → Tm50 Γ (prod50 A B) → Tm50 Γ A; fst50
 = λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd left right case zero suc rec →
     fst50 (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd left right case zero suc rec)

snd50 : ∀{Γ A B} → Tm50 Γ (prod50 A B) → Tm50 Γ B; snd50
 = λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left right case zero suc rec →
     snd50 (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left right case zero suc rec)

left50 : ∀{Γ A B} → Tm50 Γ A → Tm50 Γ (sum50 A B); left50
 = λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right case zero suc rec →
     left50 (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right case zero suc rec)

right50 : ∀{Γ A B} → Tm50 Γ B → Tm50 Γ (sum50 A B); right50
 = λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case zero suc rec →
     right50 (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case zero suc rec)

case50 : ∀{Γ A B C} → Tm50 Γ (sum50 A B) → Tm50 Γ (arr50 A C) → Tm50 Γ (arr50 B C) → Tm50 Γ C; case50
 = λ t u v Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero suc rec →
     case50 (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero suc rec)
           (u Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero suc rec)
           (v Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero suc rec)

zero50  : ∀{Γ} → Tm50 Γ nat50; zero50
 = λ Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc rec → zero50

suc50 : ∀{Γ} → Tm50 Γ nat50 → Tm50 Γ nat50; suc50
 = λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec →
   suc50 (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec)

rec50 : ∀{Γ A} → Tm50 Γ nat50 → Tm50 Γ (arr50 nat50 (arr50 A A)) → Tm50 Γ A → Tm50 Γ A; rec50
 = λ t u v Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec50 →
     rec50 (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec50)
         (u Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec50)
         (v Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec50)

v050 : ∀{Γ A} → Tm50 (snoc50 Γ A) A; v050
 = var50 vz50

v150 : ∀{Γ A B} → Tm50 (snoc50 (snoc50 Γ A) B) A; v150
 = var50 (vs50 vz50)

v250 : ∀{Γ A B C} → Tm50 (snoc50 (snoc50 (snoc50 Γ A) B) C) A; v250
 = var50 (vs50 (vs50 vz50))

v350 : ∀{Γ A B C D} → Tm50 (snoc50 (snoc50 (snoc50 (snoc50 Γ A) B) C) D) A; v350
 = var50 (vs50 (vs50 (vs50 vz50)))

tbool50 : Ty50; tbool50
 = sum50 top50 top50

true50 : ∀{Γ} → Tm50 Γ tbool50; true50
 = left50 tt50

tfalse50 : ∀{Γ} → Tm50 Γ tbool50; tfalse50
 = right50 tt50

ifthenelse50 : ∀{Γ A} → Tm50 Γ (arr50 tbool50 (arr50 A (arr50 A A))); ifthenelse50
 = lam50 (lam50 (lam50 (case50 v250 (lam50 v250) (lam50 v150))))

times450 : ∀{Γ A} → Tm50 Γ (arr50 (arr50 A A) (arr50 A A)); times450
  = lam50 (lam50 (app50 v150 (app50 v150 (app50 v150 (app50 v150 v050)))))

add50 : ∀{Γ} → Tm50 Γ (arr50 nat50 (arr50 nat50 nat50)); add50
 = lam50 (rec50 v050
       (lam50 (lam50 (lam50 (suc50 (app50 v150 v050)))))
       (lam50 v050))

mul50 : ∀{Γ} → Tm50 Γ (arr50 nat50 (arr50 nat50 nat50)); mul50
 = lam50 (rec50 v050
       (lam50 (lam50 (lam50 (app50 (app50 add50 (app50 v150 v050)) v050))))
       (lam50 zero50))

fact50 : ∀{Γ} → Tm50 Γ (arr50 nat50 nat50); fact50
 = lam50 (rec50 v050 (lam50 (lam50 (app50 (app50 mul50 (suc50 v150)) v050)))
        (suc50 zero50))
{-# OPTIONS --type-in-type #-}

Ty51 : Set
Ty51 =
   (Ty51         : Set)
   (nat top bot  : Ty51)
   (arr prod sum : Ty51 → Ty51 → Ty51)
 → Ty51

nat51 : Ty51; nat51 = λ _ nat51 _ _ _ _ _ → nat51
top51 : Ty51; top51 = λ _ _ top51 _ _ _ _ → top51
bot51 : Ty51; bot51 = λ _ _ _ bot51 _ _ _ → bot51

arr51 : Ty51 → Ty51 → Ty51; arr51
 = λ A B Ty51 nat51 top51 bot51 arr51 prod sum →
     arr51 (A Ty51 nat51 top51 bot51 arr51 prod sum) (B Ty51 nat51 top51 bot51 arr51 prod sum)

prod51 : Ty51 → Ty51 → Ty51; prod51
 = λ A B Ty51 nat51 top51 bot51 arr51 prod51 sum →
     prod51 (A Ty51 nat51 top51 bot51 arr51 prod51 sum) (B Ty51 nat51 top51 bot51 arr51 prod51 sum)

sum51 : Ty51 → Ty51 → Ty51; sum51
 = λ A B Ty51 nat51 top51 bot51 arr51 prod51 sum51 →
     sum51 (A Ty51 nat51 top51 bot51 arr51 prod51 sum51) (B Ty51 nat51 top51 bot51 arr51 prod51 sum51)

Con51 : Set; Con51
 = (Con51 : Set)
   (nil  : Con51)
   (snoc : Con51 → Ty51 → Con51)
 → Con51

nil51 : Con51; nil51
 = λ Con51 nil51 snoc → nil51

snoc51 : Con51 → Ty51 → Con51; snoc51
 = λ Γ A Con51 nil51 snoc51 → snoc51 (Γ Con51 nil51 snoc51) A

Var51 : Con51 → Ty51 → Set; Var51
 = λ Γ A →
   (Var51 : Con51 → Ty51 → Set)
   (vz  : ∀{Γ A} → Var51 (snoc51 Γ A) A)
   (vs  : ∀{Γ B A} → Var51 Γ A → Var51 (snoc51 Γ B) A)
 → Var51 Γ A

vz51 : ∀{Γ A} → Var51 (snoc51 Γ A) A; vz51
 = λ Var51 vz51 vs → vz51

vs51 : ∀{Γ B A} → Var51 Γ A → Var51 (snoc51 Γ B) A; vs51
 = λ x Var51 vz51 vs51 → vs51 (x Var51 vz51 vs51)

Tm51 : Con51 → Ty51 → Set; Tm51
 = λ Γ A →
   (Tm51  : Con51 → Ty51 → Set)
   (var   : ∀{Γ A} → Var51 Γ A → Tm51 Γ A)
   (lam   : ∀{Γ A B} → Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B))
   (app   : ∀{Γ A B} → Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B)
   (tt    : ∀{Γ} → Tm51 Γ top51)
   (pair  : ∀{Γ A B} → Tm51 Γ A → Tm51 Γ B → Tm51 Γ (prod51 A B))
   (fst   : ∀{Γ A B} → Tm51 Γ (prod51 A B) → Tm51 Γ A)
   (snd   : ∀{Γ A B} → Tm51 Γ (prod51 A B) → Tm51 Γ B)
   (left  : ∀{Γ A B} → Tm51 Γ A → Tm51 Γ (sum51 A B))
   (right : ∀{Γ A B} → Tm51 Γ B → Tm51 Γ (sum51 A B))
   (case  : ∀{Γ A B C} → Tm51 Γ (sum51 A B) → Tm51 Γ (arr51 A C) → Tm51 Γ (arr51 B C) → Tm51 Γ C)
   (zero  : ∀{Γ} → Tm51 Γ nat51)
   (suc   : ∀{Γ} → Tm51 Γ nat51 → Tm51 Γ nat51)
   (rec   : ∀{Γ A} → Tm51 Γ nat51 → Tm51 Γ (arr51 nat51 (arr51 A A)) → Tm51 Γ A → Tm51 Γ A)
 → Tm51 Γ A

var51 : ∀{Γ A} → Var51 Γ A → Tm51 Γ A; var51
 = λ x Tm51 var51 lam app tt pair fst snd left right case zero suc rec →
     var51 x

lam51 : ∀{Γ A B} → Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B); lam51
 = λ t Tm51 var51 lam51 app tt pair fst snd left right case zero suc rec →
     lam51 (t Tm51 var51 lam51 app tt pair fst snd left right case zero suc rec)

app51 : ∀{Γ A B} → Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B; app51
 = λ t u Tm51 var51 lam51 app51 tt pair fst snd left right case zero suc rec →
     app51 (t Tm51 var51 lam51 app51 tt pair fst snd left right case zero suc rec)
         (u Tm51 var51 lam51 app51 tt pair fst snd left right case zero suc rec)

tt51 : ∀{Γ} → Tm51 Γ top51; tt51
 = λ Tm51 var51 lam51 app51 tt51 pair fst snd left right case zero suc rec → tt51

pair51 : ∀{Γ A B} → Tm51 Γ A → Tm51 Γ B → Tm51 Γ (prod51 A B); pair51
 = λ t u Tm51 var51 lam51 app51 tt51 pair51 fst snd left right case zero suc rec →
     pair51 (t Tm51 var51 lam51 app51 tt51 pair51 fst snd left right case zero suc rec)
          (u Tm51 var51 lam51 app51 tt51 pair51 fst snd left right case zero suc rec)

fst51 : ∀{Γ A B} → Tm51 Γ (prod51 A B) → Tm51 Γ A; fst51
 = λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd left right case zero suc rec →
     fst51 (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd left right case zero suc rec)

snd51 : ∀{Γ A B} → Tm51 Γ (prod51 A B) → Tm51 Γ B; snd51
 = λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left right case zero suc rec →
     snd51 (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left right case zero suc rec)

left51 : ∀{Γ A B} → Tm51 Γ A → Tm51 Γ (sum51 A B); left51
 = λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right case zero suc rec →
     left51 (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right case zero suc rec)

right51 : ∀{Γ A B} → Tm51 Γ B → Tm51 Γ (sum51 A B); right51
 = λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case zero suc rec →
     right51 (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case zero suc rec)

case51 : ∀{Γ A B C} → Tm51 Γ (sum51 A B) → Tm51 Γ (arr51 A C) → Tm51 Γ (arr51 B C) → Tm51 Γ C; case51
 = λ t u v Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero suc rec →
     case51 (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero suc rec)
           (u Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero suc rec)
           (v Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero suc rec)

zero51  : ∀{Γ} → Tm51 Γ nat51; zero51
 = λ Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc rec → zero51

suc51 : ∀{Γ} → Tm51 Γ nat51 → Tm51 Γ nat51; suc51
 = λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec →
   suc51 (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec)

rec51 : ∀{Γ A} → Tm51 Γ nat51 → Tm51 Γ (arr51 nat51 (arr51 A A)) → Tm51 Γ A → Tm51 Γ A; rec51
 = λ t u v Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec51 →
     rec51 (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec51)
         (u Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec51)
         (v Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec51)

v051 : ∀{Γ A} → Tm51 (snoc51 Γ A) A; v051
 = var51 vz51

v151 : ∀{Γ A B} → Tm51 (snoc51 (snoc51 Γ A) B) A; v151
 = var51 (vs51 vz51)

v251 : ∀{Γ A B C} → Tm51 (snoc51 (snoc51 (snoc51 Γ A) B) C) A; v251
 = var51 (vs51 (vs51 vz51))

v351 : ∀{Γ A B C D} → Tm51 (snoc51 (snoc51 (snoc51 (snoc51 Γ A) B) C) D) A; v351
 = var51 (vs51 (vs51 (vs51 vz51)))

tbool51 : Ty51; tbool51
 = sum51 top51 top51

true51 : ∀{Γ} → Tm51 Γ tbool51; true51
 = left51 tt51

tfalse51 : ∀{Γ} → Tm51 Γ tbool51; tfalse51
 = right51 tt51

ifthenelse51 : ∀{Γ A} → Tm51 Γ (arr51 tbool51 (arr51 A (arr51 A A))); ifthenelse51
 = lam51 (lam51 (lam51 (case51 v251 (lam51 v251) (lam51 v151))))

times451 : ∀{Γ A} → Tm51 Γ (arr51 (arr51 A A) (arr51 A A)); times451
  = lam51 (lam51 (app51 v151 (app51 v151 (app51 v151 (app51 v151 v051)))))

add51 : ∀{Γ} → Tm51 Γ (arr51 nat51 (arr51 nat51 nat51)); add51
 = lam51 (rec51 v051
       (lam51 (lam51 (lam51 (suc51 (app51 v151 v051)))))
       (lam51 v051))

mul51 : ∀{Γ} → Tm51 Γ (arr51 nat51 (arr51 nat51 nat51)); mul51
 = lam51 (rec51 v051
       (lam51 (lam51 (lam51 (app51 (app51 add51 (app51 v151 v051)) v051))))
       (lam51 zero51))

fact51 : ∀{Γ} → Tm51 Γ (arr51 nat51 nat51); fact51
 = lam51 (rec51 v051 (lam51 (lam51 (app51 (app51 mul51 (suc51 v151)) v051)))
        (suc51 zero51))
{-# OPTIONS --type-in-type #-}

Ty52 : Set
Ty52 =
   (Ty52         : Set)
   (nat top bot  : Ty52)
   (arr prod sum : Ty52 → Ty52 → Ty52)
 → Ty52

nat52 : Ty52; nat52 = λ _ nat52 _ _ _ _ _ → nat52
top52 : Ty52; top52 = λ _ _ top52 _ _ _ _ → top52
bot52 : Ty52; bot52 = λ _ _ _ bot52 _ _ _ → bot52

arr52 : Ty52 → Ty52 → Ty52; arr52
 = λ A B Ty52 nat52 top52 bot52 arr52 prod sum →
     arr52 (A Ty52 nat52 top52 bot52 arr52 prod sum) (B Ty52 nat52 top52 bot52 arr52 prod sum)

prod52 : Ty52 → Ty52 → Ty52; prod52
 = λ A B Ty52 nat52 top52 bot52 arr52 prod52 sum →
     prod52 (A Ty52 nat52 top52 bot52 arr52 prod52 sum) (B Ty52 nat52 top52 bot52 arr52 prod52 sum)

sum52 : Ty52 → Ty52 → Ty52; sum52
 = λ A B Ty52 nat52 top52 bot52 arr52 prod52 sum52 →
     sum52 (A Ty52 nat52 top52 bot52 arr52 prod52 sum52) (B Ty52 nat52 top52 bot52 arr52 prod52 sum52)

Con52 : Set; Con52
 = (Con52 : Set)
   (nil  : Con52)
   (snoc : Con52 → Ty52 → Con52)
 → Con52

nil52 : Con52; nil52
 = λ Con52 nil52 snoc → nil52

snoc52 : Con52 → Ty52 → Con52; snoc52
 = λ Γ A Con52 nil52 snoc52 → snoc52 (Γ Con52 nil52 snoc52) A

Var52 : Con52 → Ty52 → Set; Var52
 = λ Γ A →
   (Var52 : Con52 → Ty52 → Set)
   (vz  : ∀{Γ A} → Var52 (snoc52 Γ A) A)
   (vs  : ∀{Γ B A} → Var52 Γ A → Var52 (snoc52 Γ B) A)
 → Var52 Γ A

vz52 : ∀{Γ A} → Var52 (snoc52 Γ A) A; vz52
 = λ Var52 vz52 vs → vz52

vs52 : ∀{Γ B A} → Var52 Γ A → Var52 (snoc52 Γ B) A; vs52
 = λ x Var52 vz52 vs52 → vs52 (x Var52 vz52 vs52)

Tm52 : Con52 → Ty52 → Set; Tm52
 = λ Γ A →
   (Tm52  : Con52 → Ty52 → Set)
   (var   : ∀{Γ A} → Var52 Γ A → Tm52 Γ A)
   (lam   : ∀{Γ A B} → Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B))
   (app   : ∀{Γ A B} → Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B)
   (tt    : ∀{Γ} → Tm52 Γ top52)
   (pair  : ∀{Γ A B} → Tm52 Γ A → Tm52 Γ B → Tm52 Γ (prod52 A B))
   (fst   : ∀{Γ A B} → Tm52 Γ (prod52 A B) → Tm52 Γ A)
   (snd   : ∀{Γ A B} → Tm52 Γ (prod52 A B) → Tm52 Γ B)
   (left  : ∀{Γ A B} → Tm52 Γ A → Tm52 Γ (sum52 A B))
   (right : ∀{Γ A B} → Tm52 Γ B → Tm52 Γ (sum52 A B))
   (case  : ∀{Γ A B C} → Tm52 Γ (sum52 A B) → Tm52 Γ (arr52 A C) → Tm52 Γ (arr52 B C) → Tm52 Γ C)
   (zero  : ∀{Γ} → Tm52 Γ nat52)
   (suc   : ∀{Γ} → Tm52 Γ nat52 → Tm52 Γ nat52)
   (rec   : ∀{Γ A} → Tm52 Γ nat52 → Tm52 Γ (arr52 nat52 (arr52 A A)) → Tm52 Γ A → Tm52 Γ A)
 → Tm52 Γ A

var52 : ∀{Γ A} → Var52 Γ A → Tm52 Γ A; var52
 = λ x Tm52 var52 lam app tt pair fst snd left right case zero suc rec →
     var52 x

lam52 : ∀{Γ A B} → Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B); lam52
 = λ t Tm52 var52 lam52 app tt pair fst snd left right case zero suc rec →
     lam52 (t Tm52 var52 lam52 app tt pair fst snd left right case zero suc rec)

app52 : ∀{Γ A B} → Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B; app52
 = λ t u Tm52 var52 lam52 app52 tt pair fst snd left right case zero suc rec →
     app52 (t Tm52 var52 lam52 app52 tt pair fst snd left right case zero suc rec)
         (u Tm52 var52 lam52 app52 tt pair fst snd left right case zero suc rec)

tt52 : ∀{Γ} → Tm52 Γ top52; tt52
 = λ Tm52 var52 lam52 app52 tt52 pair fst snd left right case zero suc rec → tt52

pair52 : ∀{Γ A B} → Tm52 Γ A → Tm52 Γ B → Tm52 Γ (prod52 A B); pair52
 = λ t u Tm52 var52 lam52 app52 tt52 pair52 fst snd left right case zero suc rec →
     pair52 (t Tm52 var52 lam52 app52 tt52 pair52 fst snd left right case zero suc rec)
          (u Tm52 var52 lam52 app52 tt52 pair52 fst snd left right case zero suc rec)

fst52 : ∀{Γ A B} → Tm52 Γ (prod52 A B) → Tm52 Γ A; fst52
 = λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd left right case zero suc rec →
     fst52 (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd left right case zero suc rec)

snd52 : ∀{Γ A B} → Tm52 Γ (prod52 A B) → Tm52 Γ B; snd52
 = λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left right case zero suc rec →
     snd52 (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left right case zero suc rec)

left52 : ∀{Γ A B} → Tm52 Γ A → Tm52 Γ (sum52 A B); left52
 = λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right case zero suc rec →
     left52 (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right case zero suc rec)

right52 : ∀{Γ A B} → Tm52 Γ B → Tm52 Γ (sum52 A B); right52
 = λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case zero suc rec →
     right52 (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case zero suc rec)

case52 : ∀{Γ A B C} → Tm52 Γ (sum52 A B) → Tm52 Γ (arr52 A C) → Tm52 Γ (arr52 B C) → Tm52 Γ C; case52
 = λ t u v Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero suc rec →
     case52 (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero suc rec)
           (u Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero suc rec)
           (v Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero suc rec)

zero52  : ∀{Γ} → Tm52 Γ nat52; zero52
 = λ Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc rec → zero52

suc52 : ∀{Γ} → Tm52 Γ nat52 → Tm52 Γ nat52; suc52
 = λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec →
   suc52 (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec)

rec52 : ∀{Γ A} → Tm52 Γ nat52 → Tm52 Γ (arr52 nat52 (arr52 A A)) → Tm52 Γ A → Tm52 Γ A; rec52
 = λ t u v Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec52 →
     rec52 (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec52)
         (u Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec52)
         (v Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec52)

v052 : ∀{Γ A} → Tm52 (snoc52 Γ A) A; v052
 = var52 vz52

v152 : ∀{Γ A B} → Tm52 (snoc52 (snoc52 Γ A) B) A; v152
 = var52 (vs52 vz52)

v252 : ∀{Γ A B C} → Tm52 (snoc52 (snoc52 (snoc52 Γ A) B) C) A; v252
 = var52 (vs52 (vs52 vz52))

v352 : ∀{Γ A B C D} → Tm52 (snoc52 (snoc52 (snoc52 (snoc52 Γ A) B) C) D) A; v352
 = var52 (vs52 (vs52 (vs52 vz52)))

tbool52 : Ty52; tbool52
 = sum52 top52 top52

true52 : ∀{Γ} → Tm52 Γ tbool52; true52
 = left52 tt52

tfalse52 : ∀{Γ} → Tm52 Γ tbool52; tfalse52
 = right52 tt52

ifthenelse52 : ∀{Γ A} → Tm52 Γ (arr52 tbool52 (arr52 A (arr52 A A))); ifthenelse52
 = lam52 (lam52 (lam52 (case52 v252 (lam52 v252) (lam52 v152))))

times452 : ∀{Γ A} → Tm52 Γ (arr52 (arr52 A A) (arr52 A A)); times452
  = lam52 (lam52 (app52 v152 (app52 v152 (app52 v152 (app52 v152 v052)))))

add52 : ∀{Γ} → Tm52 Γ (arr52 nat52 (arr52 nat52 nat52)); add52
 = lam52 (rec52 v052
       (lam52 (lam52 (lam52 (suc52 (app52 v152 v052)))))
       (lam52 v052))

mul52 : ∀{Γ} → Tm52 Γ (arr52 nat52 (arr52 nat52 nat52)); mul52
 = lam52 (rec52 v052
       (lam52 (lam52 (lam52 (app52 (app52 add52 (app52 v152 v052)) v052))))
       (lam52 zero52))

fact52 : ∀{Γ} → Tm52 Γ (arr52 nat52 nat52); fact52
 = lam52 (rec52 v052 (lam52 (lam52 (app52 (app52 mul52 (suc52 v152)) v052)))
        (suc52 zero52))
{-# OPTIONS --type-in-type #-}

Ty53 : Set
Ty53 =
   (Ty53         : Set)
   (nat top bot  : Ty53)
   (arr prod sum : Ty53 → Ty53 → Ty53)
 → Ty53

nat53 : Ty53; nat53 = λ _ nat53 _ _ _ _ _ → nat53
top53 : Ty53; top53 = λ _ _ top53 _ _ _ _ → top53
bot53 : Ty53; bot53 = λ _ _ _ bot53 _ _ _ → bot53

arr53 : Ty53 → Ty53 → Ty53; arr53
 = λ A B Ty53 nat53 top53 bot53 arr53 prod sum →
     arr53 (A Ty53 nat53 top53 bot53 arr53 prod sum) (B Ty53 nat53 top53 bot53 arr53 prod sum)

prod53 : Ty53 → Ty53 → Ty53; prod53
 = λ A B Ty53 nat53 top53 bot53 arr53 prod53 sum →
     prod53 (A Ty53 nat53 top53 bot53 arr53 prod53 sum) (B Ty53 nat53 top53 bot53 arr53 prod53 sum)

sum53 : Ty53 → Ty53 → Ty53; sum53
 = λ A B Ty53 nat53 top53 bot53 arr53 prod53 sum53 →
     sum53 (A Ty53 nat53 top53 bot53 arr53 prod53 sum53) (B Ty53 nat53 top53 bot53 arr53 prod53 sum53)

Con53 : Set; Con53
 = (Con53 : Set)
   (nil  : Con53)
   (snoc : Con53 → Ty53 → Con53)
 → Con53

nil53 : Con53; nil53
 = λ Con53 nil53 snoc → nil53

snoc53 : Con53 → Ty53 → Con53; snoc53
 = λ Γ A Con53 nil53 snoc53 → snoc53 (Γ Con53 nil53 snoc53) A

Var53 : Con53 → Ty53 → Set; Var53
 = λ Γ A →
   (Var53 : Con53 → Ty53 → Set)
   (vz  : ∀{Γ A} → Var53 (snoc53 Γ A) A)
   (vs  : ∀{Γ B A} → Var53 Γ A → Var53 (snoc53 Γ B) A)
 → Var53 Γ A

vz53 : ∀{Γ A} → Var53 (snoc53 Γ A) A; vz53
 = λ Var53 vz53 vs → vz53

vs53 : ∀{Γ B A} → Var53 Γ A → Var53 (snoc53 Γ B) A; vs53
 = λ x Var53 vz53 vs53 → vs53 (x Var53 vz53 vs53)

Tm53 : Con53 → Ty53 → Set; Tm53
 = λ Γ A →
   (Tm53  : Con53 → Ty53 → Set)
   (var   : ∀{Γ A} → Var53 Γ A → Tm53 Γ A)
   (lam   : ∀{Γ A B} → Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B))
   (app   : ∀{Γ A B} → Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B)
   (tt    : ∀{Γ} → Tm53 Γ top53)
   (pair  : ∀{Γ A B} → Tm53 Γ A → Tm53 Γ B → Tm53 Γ (prod53 A B))
   (fst   : ∀{Γ A B} → Tm53 Γ (prod53 A B) → Tm53 Γ A)
   (snd   : ∀{Γ A B} → Tm53 Γ (prod53 A B) → Tm53 Γ B)
   (left  : ∀{Γ A B} → Tm53 Γ A → Tm53 Γ (sum53 A B))
   (right : ∀{Γ A B} → Tm53 Γ B → Tm53 Γ (sum53 A B))
   (case  : ∀{Γ A B C} → Tm53 Γ (sum53 A B) → Tm53 Γ (arr53 A C) → Tm53 Γ (arr53 B C) → Tm53 Γ C)
   (zero  : ∀{Γ} → Tm53 Γ nat53)
   (suc   : ∀{Γ} → Tm53 Γ nat53 → Tm53 Γ nat53)
   (rec   : ∀{Γ A} → Tm53 Γ nat53 → Tm53 Γ (arr53 nat53 (arr53 A A)) → Tm53 Γ A → Tm53 Γ A)
 → Tm53 Γ A

var53 : ∀{Γ A} → Var53 Γ A → Tm53 Γ A; var53
 = λ x Tm53 var53 lam app tt pair fst snd left right case zero suc rec →
     var53 x

lam53 : ∀{Γ A B} → Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B); lam53
 = λ t Tm53 var53 lam53 app tt pair fst snd left right case zero suc rec →
     lam53 (t Tm53 var53 lam53 app tt pair fst snd left right case zero suc rec)

app53 : ∀{Γ A B} → Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B; app53
 = λ t u Tm53 var53 lam53 app53 tt pair fst snd left right case zero suc rec →
     app53 (t Tm53 var53 lam53 app53 tt pair fst snd left right case zero suc rec)
         (u Tm53 var53 lam53 app53 tt pair fst snd left right case zero suc rec)

tt53 : ∀{Γ} → Tm53 Γ top53; tt53
 = λ Tm53 var53 lam53 app53 tt53 pair fst snd left right case zero suc rec → tt53

pair53 : ∀{Γ A B} → Tm53 Γ A → Tm53 Γ B → Tm53 Γ (prod53 A B); pair53
 = λ t u Tm53 var53 lam53 app53 tt53 pair53 fst snd left right case zero suc rec →
     pair53 (t Tm53 var53 lam53 app53 tt53 pair53 fst snd left right case zero suc rec)
          (u Tm53 var53 lam53 app53 tt53 pair53 fst snd left right case zero suc rec)

fst53 : ∀{Γ A B} → Tm53 Γ (prod53 A B) → Tm53 Γ A; fst53
 = λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd left right case zero suc rec →
     fst53 (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd left right case zero suc rec)

snd53 : ∀{Γ A B} → Tm53 Γ (prod53 A B) → Tm53 Γ B; snd53
 = λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left right case zero suc rec →
     snd53 (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left right case zero suc rec)

left53 : ∀{Γ A B} → Tm53 Γ A → Tm53 Γ (sum53 A B); left53
 = λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right case zero suc rec →
     left53 (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right case zero suc rec)

right53 : ∀{Γ A B} → Tm53 Γ B → Tm53 Γ (sum53 A B); right53
 = λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case zero suc rec →
     right53 (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case zero suc rec)

case53 : ∀{Γ A B C} → Tm53 Γ (sum53 A B) → Tm53 Γ (arr53 A C) → Tm53 Γ (arr53 B C) → Tm53 Γ C; case53
 = λ t u v Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero suc rec →
     case53 (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero suc rec)
           (u Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero suc rec)
           (v Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero suc rec)

zero53  : ∀{Γ} → Tm53 Γ nat53; zero53
 = λ Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc rec → zero53

suc53 : ∀{Γ} → Tm53 Γ nat53 → Tm53 Γ nat53; suc53
 = λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec →
   suc53 (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec)

rec53 : ∀{Γ A} → Tm53 Γ nat53 → Tm53 Γ (arr53 nat53 (arr53 A A)) → Tm53 Γ A → Tm53 Γ A; rec53
 = λ t u v Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec53 →
     rec53 (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec53)
         (u Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec53)
         (v Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec53)

v053 : ∀{Γ A} → Tm53 (snoc53 Γ A) A; v053
 = var53 vz53

v153 : ∀{Γ A B} → Tm53 (snoc53 (snoc53 Γ A) B) A; v153
 = var53 (vs53 vz53)

v253 : ∀{Γ A B C} → Tm53 (snoc53 (snoc53 (snoc53 Γ A) B) C) A; v253
 = var53 (vs53 (vs53 vz53))

v353 : ∀{Γ A B C D} → Tm53 (snoc53 (snoc53 (snoc53 (snoc53 Γ A) B) C) D) A; v353
 = var53 (vs53 (vs53 (vs53 vz53)))

tbool53 : Ty53; tbool53
 = sum53 top53 top53

true53 : ∀{Γ} → Tm53 Γ tbool53; true53
 = left53 tt53

tfalse53 : ∀{Γ} → Tm53 Γ tbool53; tfalse53
 = right53 tt53

ifthenelse53 : ∀{Γ A} → Tm53 Γ (arr53 tbool53 (arr53 A (arr53 A A))); ifthenelse53
 = lam53 (lam53 (lam53 (case53 v253 (lam53 v253) (lam53 v153))))

times453 : ∀{Γ A} → Tm53 Γ (arr53 (arr53 A A) (arr53 A A)); times453
  = lam53 (lam53 (app53 v153 (app53 v153 (app53 v153 (app53 v153 v053)))))

add53 : ∀{Γ} → Tm53 Γ (arr53 nat53 (arr53 nat53 nat53)); add53
 = lam53 (rec53 v053
       (lam53 (lam53 (lam53 (suc53 (app53 v153 v053)))))
       (lam53 v053))

mul53 : ∀{Γ} → Tm53 Γ (arr53 nat53 (arr53 nat53 nat53)); mul53
 = lam53 (rec53 v053
       (lam53 (lam53 (lam53 (app53 (app53 add53 (app53 v153 v053)) v053))))
       (lam53 zero53))

fact53 : ∀{Γ} → Tm53 Γ (arr53 nat53 nat53); fact53
 = lam53 (rec53 v053 (lam53 (lam53 (app53 (app53 mul53 (suc53 v153)) v053)))
        (suc53 zero53))
{-# OPTIONS --type-in-type #-}

Ty54 : Set
Ty54 =
   (Ty54         : Set)
   (nat top bot  : Ty54)
   (arr prod sum : Ty54 → Ty54 → Ty54)
 → Ty54

nat54 : Ty54; nat54 = λ _ nat54 _ _ _ _ _ → nat54
top54 : Ty54; top54 = λ _ _ top54 _ _ _ _ → top54
bot54 : Ty54; bot54 = λ _ _ _ bot54 _ _ _ → bot54

arr54 : Ty54 → Ty54 → Ty54; arr54
 = λ A B Ty54 nat54 top54 bot54 arr54 prod sum →
     arr54 (A Ty54 nat54 top54 bot54 arr54 prod sum) (B Ty54 nat54 top54 bot54 arr54 prod sum)

prod54 : Ty54 → Ty54 → Ty54; prod54
 = λ A B Ty54 nat54 top54 bot54 arr54 prod54 sum →
     prod54 (A Ty54 nat54 top54 bot54 arr54 prod54 sum) (B Ty54 nat54 top54 bot54 arr54 prod54 sum)

sum54 : Ty54 → Ty54 → Ty54; sum54
 = λ A B Ty54 nat54 top54 bot54 arr54 prod54 sum54 →
     sum54 (A Ty54 nat54 top54 bot54 arr54 prod54 sum54) (B Ty54 nat54 top54 bot54 arr54 prod54 sum54)

Con54 : Set; Con54
 = (Con54 : Set)
   (nil  : Con54)
   (snoc : Con54 → Ty54 → Con54)
 → Con54

nil54 : Con54; nil54
 = λ Con54 nil54 snoc → nil54

snoc54 : Con54 → Ty54 → Con54; snoc54
 = λ Γ A Con54 nil54 snoc54 → snoc54 (Γ Con54 nil54 snoc54) A

Var54 : Con54 → Ty54 → Set; Var54
 = λ Γ A →
   (Var54 : Con54 → Ty54 → Set)
   (vz  : ∀{Γ A} → Var54 (snoc54 Γ A) A)
   (vs  : ∀{Γ B A} → Var54 Γ A → Var54 (snoc54 Γ B) A)
 → Var54 Γ A

vz54 : ∀{Γ A} → Var54 (snoc54 Γ A) A; vz54
 = λ Var54 vz54 vs → vz54

vs54 : ∀{Γ B A} → Var54 Γ A → Var54 (snoc54 Γ B) A; vs54
 = λ x Var54 vz54 vs54 → vs54 (x Var54 vz54 vs54)

Tm54 : Con54 → Ty54 → Set; Tm54
 = λ Γ A →
   (Tm54  : Con54 → Ty54 → Set)
   (var   : ∀{Γ A} → Var54 Γ A → Tm54 Γ A)
   (lam   : ∀{Γ A B} → Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B))
   (app   : ∀{Γ A B} → Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B)
   (tt    : ∀{Γ} → Tm54 Γ top54)
   (pair  : ∀{Γ A B} → Tm54 Γ A → Tm54 Γ B → Tm54 Γ (prod54 A B))
   (fst   : ∀{Γ A B} → Tm54 Γ (prod54 A B) → Tm54 Γ A)
   (snd   : ∀{Γ A B} → Tm54 Γ (prod54 A B) → Tm54 Γ B)
   (left  : ∀{Γ A B} → Tm54 Γ A → Tm54 Γ (sum54 A B))
   (right : ∀{Γ A B} → Tm54 Γ B → Tm54 Γ (sum54 A B))
   (case  : ∀{Γ A B C} → Tm54 Γ (sum54 A B) → Tm54 Γ (arr54 A C) → Tm54 Γ (arr54 B C) → Tm54 Γ C)
   (zero  : ∀{Γ} → Tm54 Γ nat54)
   (suc   : ∀{Γ} → Tm54 Γ nat54 → Tm54 Γ nat54)
   (rec   : ∀{Γ A} → Tm54 Γ nat54 → Tm54 Γ (arr54 nat54 (arr54 A A)) → Tm54 Γ A → Tm54 Γ A)
 → Tm54 Γ A

var54 : ∀{Γ A} → Var54 Γ A → Tm54 Γ A; var54
 = λ x Tm54 var54 lam app tt pair fst snd left right case zero suc rec →
     var54 x

lam54 : ∀{Γ A B} → Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B); lam54
 = λ t Tm54 var54 lam54 app tt pair fst snd left right case zero suc rec →
     lam54 (t Tm54 var54 lam54 app tt pair fst snd left right case zero suc rec)

app54 : ∀{Γ A B} → Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B; app54
 = λ t u Tm54 var54 lam54 app54 tt pair fst snd left right case zero suc rec →
     app54 (t Tm54 var54 lam54 app54 tt pair fst snd left right case zero suc rec)
         (u Tm54 var54 lam54 app54 tt pair fst snd left right case zero suc rec)

tt54 : ∀{Γ} → Tm54 Γ top54; tt54
 = λ Tm54 var54 lam54 app54 tt54 pair fst snd left right case zero suc rec → tt54

pair54 : ∀{Γ A B} → Tm54 Γ A → Tm54 Γ B → Tm54 Γ (prod54 A B); pair54
 = λ t u Tm54 var54 lam54 app54 tt54 pair54 fst snd left right case zero suc rec →
     pair54 (t Tm54 var54 lam54 app54 tt54 pair54 fst snd left right case zero suc rec)
          (u Tm54 var54 lam54 app54 tt54 pair54 fst snd left right case zero suc rec)

fst54 : ∀{Γ A B} → Tm54 Γ (prod54 A B) → Tm54 Γ A; fst54
 = λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd left right case zero suc rec →
     fst54 (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd left right case zero suc rec)

snd54 : ∀{Γ A B} → Tm54 Γ (prod54 A B) → Tm54 Γ B; snd54
 = λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left right case zero suc rec →
     snd54 (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left right case zero suc rec)

left54 : ∀{Γ A B} → Tm54 Γ A → Tm54 Γ (sum54 A B); left54
 = λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right case zero suc rec →
     left54 (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right case zero suc rec)

right54 : ∀{Γ A B} → Tm54 Γ B → Tm54 Γ (sum54 A B); right54
 = λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case zero suc rec →
     right54 (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case zero suc rec)

case54 : ∀{Γ A B C} → Tm54 Γ (sum54 A B) → Tm54 Γ (arr54 A C) → Tm54 Γ (arr54 B C) → Tm54 Γ C; case54
 = λ t u v Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero suc rec →
     case54 (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero suc rec)
           (u Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero suc rec)
           (v Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero suc rec)

zero54  : ∀{Γ} → Tm54 Γ nat54; zero54
 = λ Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc rec → zero54

suc54 : ∀{Γ} → Tm54 Γ nat54 → Tm54 Γ nat54; suc54
 = λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec →
   suc54 (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec)

rec54 : ∀{Γ A} → Tm54 Γ nat54 → Tm54 Γ (arr54 nat54 (arr54 A A)) → Tm54 Γ A → Tm54 Γ A; rec54
 = λ t u v Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec54 →
     rec54 (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec54)
         (u Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec54)
         (v Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec54)

v054 : ∀{Γ A} → Tm54 (snoc54 Γ A) A; v054
 = var54 vz54

v154 : ∀{Γ A B} → Tm54 (snoc54 (snoc54 Γ A) B) A; v154
 = var54 (vs54 vz54)

v254 : ∀{Γ A B C} → Tm54 (snoc54 (snoc54 (snoc54 Γ A) B) C) A; v254
 = var54 (vs54 (vs54 vz54))

v354 : ∀{Γ A B C D} → Tm54 (snoc54 (snoc54 (snoc54 (snoc54 Γ A) B) C) D) A; v354
 = var54 (vs54 (vs54 (vs54 vz54)))

tbool54 : Ty54; tbool54
 = sum54 top54 top54

true54 : ∀{Γ} → Tm54 Γ tbool54; true54
 = left54 tt54

tfalse54 : ∀{Γ} → Tm54 Γ tbool54; tfalse54
 = right54 tt54

ifthenelse54 : ∀{Γ A} → Tm54 Γ (arr54 tbool54 (arr54 A (arr54 A A))); ifthenelse54
 = lam54 (lam54 (lam54 (case54 v254 (lam54 v254) (lam54 v154))))

times454 : ∀{Γ A} → Tm54 Γ (arr54 (arr54 A A) (arr54 A A)); times454
  = lam54 (lam54 (app54 v154 (app54 v154 (app54 v154 (app54 v154 v054)))))

add54 : ∀{Γ} → Tm54 Γ (arr54 nat54 (arr54 nat54 nat54)); add54
 = lam54 (rec54 v054
       (lam54 (lam54 (lam54 (suc54 (app54 v154 v054)))))
       (lam54 v054))

mul54 : ∀{Γ} → Tm54 Γ (arr54 nat54 (arr54 nat54 nat54)); mul54
 = lam54 (rec54 v054
       (lam54 (lam54 (lam54 (app54 (app54 add54 (app54 v154 v054)) v054))))
       (lam54 zero54))

fact54 : ∀{Γ} → Tm54 Γ (arr54 nat54 nat54); fact54
 = lam54 (rec54 v054 (lam54 (lam54 (app54 (app54 mul54 (suc54 v154)) v054)))
        (suc54 zero54))
{-# OPTIONS --type-in-type #-}

Ty55 : Set
Ty55 =
   (Ty55         : Set)
   (nat top bot  : Ty55)
   (arr prod sum : Ty55 → Ty55 → Ty55)
 → Ty55

nat55 : Ty55; nat55 = λ _ nat55 _ _ _ _ _ → nat55
top55 : Ty55; top55 = λ _ _ top55 _ _ _ _ → top55
bot55 : Ty55; bot55 = λ _ _ _ bot55 _ _ _ → bot55

arr55 : Ty55 → Ty55 → Ty55; arr55
 = λ A B Ty55 nat55 top55 bot55 arr55 prod sum →
     arr55 (A Ty55 nat55 top55 bot55 arr55 prod sum) (B Ty55 nat55 top55 bot55 arr55 prod sum)

prod55 : Ty55 → Ty55 → Ty55; prod55
 = λ A B Ty55 nat55 top55 bot55 arr55 prod55 sum →
     prod55 (A Ty55 nat55 top55 bot55 arr55 prod55 sum) (B Ty55 nat55 top55 bot55 arr55 prod55 sum)

sum55 : Ty55 → Ty55 → Ty55; sum55
 = λ A B Ty55 nat55 top55 bot55 arr55 prod55 sum55 →
     sum55 (A Ty55 nat55 top55 bot55 arr55 prod55 sum55) (B Ty55 nat55 top55 bot55 arr55 prod55 sum55)

Con55 : Set; Con55
 = (Con55 : Set)
   (nil  : Con55)
   (snoc : Con55 → Ty55 → Con55)
 → Con55

nil55 : Con55; nil55
 = λ Con55 nil55 snoc → nil55

snoc55 : Con55 → Ty55 → Con55; snoc55
 = λ Γ A Con55 nil55 snoc55 → snoc55 (Γ Con55 nil55 snoc55) A

Var55 : Con55 → Ty55 → Set; Var55
 = λ Γ A →
   (Var55 : Con55 → Ty55 → Set)
   (vz  : ∀{Γ A} → Var55 (snoc55 Γ A) A)
   (vs  : ∀{Γ B A} → Var55 Γ A → Var55 (snoc55 Γ B) A)
 → Var55 Γ A

vz55 : ∀{Γ A} → Var55 (snoc55 Γ A) A; vz55
 = λ Var55 vz55 vs → vz55

vs55 : ∀{Γ B A} → Var55 Γ A → Var55 (snoc55 Γ B) A; vs55
 = λ x Var55 vz55 vs55 → vs55 (x Var55 vz55 vs55)

Tm55 : Con55 → Ty55 → Set; Tm55
 = λ Γ A →
   (Tm55  : Con55 → Ty55 → Set)
   (var   : ∀{Γ A} → Var55 Γ A → Tm55 Γ A)
   (lam   : ∀{Γ A B} → Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B))
   (app   : ∀{Γ A B} → Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B)
   (tt    : ∀{Γ} → Tm55 Γ top55)
   (pair  : ∀{Γ A B} → Tm55 Γ A → Tm55 Γ B → Tm55 Γ (prod55 A B))
   (fst   : ∀{Γ A B} → Tm55 Γ (prod55 A B) → Tm55 Γ A)
   (snd   : ∀{Γ A B} → Tm55 Γ (prod55 A B) → Tm55 Γ B)
   (left  : ∀{Γ A B} → Tm55 Γ A → Tm55 Γ (sum55 A B))
   (right : ∀{Γ A B} → Tm55 Γ B → Tm55 Γ (sum55 A B))
   (case  : ∀{Γ A B C} → Tm55 Γ (sum55 A B) → Tm55 Γ (arr55 A C) → Tm55 Γ (arr55 B C) → Tm55 Γ C)
   (zero  : ∀{Γ} → Tm55 Γ nat55)
   (suc   : ∀{Γ} → Tm55 Γ nat55 → Tm55 Γ nat55)
   (rec   : ∀{Γ A} → Tm55 Γ nat55 → Tm55 Γ (arr55 nat55 (arr55 A A)) → Tm55 Γ A → Tm55 Γ A)
 → Tm55 Γ A

var55 : ∀{Γ A} → Var55 Γ A → Tm55 Γ A; var55
 = λ x Tm55 var55 lam app tt pair fst snd left right case zero suc rec →
     var55 x

lam55 : ∀{Γ A B} → Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B); lam55
 = λ t Tm55 var55 lam55 app tt pair fst snd left right case zero suc rec →
     lam55 (t Tm55 var55 lam55 app tt pair fst snd left right case zero suc rec)

app55 : ∀{Γ A B} → Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B; app55
 = λ t u Tm55 var55 lam55 app55 tt pair fst snd left right case zero suc rec →
     app55 (t Tm55 var55 lam55 app55 tt pair fst snd left right case zero suc rec)
         (u Tm55 var55 lam55 app55 tt pair fst snd left right case zero suc rec)

tt55 : ∀{Γ} → Tm55 Γ top55; tt55
 = λ Tm55 var55 lam55 app55 tt55 pair fst snd left right case zero suc rec → tt55

pair55 : ∀{Γ A B} → Tm55 Γ A → Tm55 Γ B → Tm55 Γ (prod55 A B); pair55
 = λ t u Tm55 var55 lam55 app55 tt55 pair55 fst snd left right case zero suc rec →
     pair55 (t Tm55 var55 lam55 app55 tt55 pair55 fst snd left right case zero suc rec)
          (u Tm55 var55 lam55 app55 tt55 pair55 fst snd left right case zero suc rec)

fst55 : ∀{Γ A B} → Tm55 Γ (prod55 A B) → Tm55 Γ A; fst55
 = λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd left right case zero suc rec →
     fst55 (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd left right case zero suc rec)

snd55 : ∀{Γ A B} → Tm55 Γ (prod55 A B) → Tm55 Γ B; snd55
 = λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left right case zero suc rec →
     snd55 (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left right case zero suc rec)

left55 : ∀{Γ A B} → Tm55 Γ A → Tm55 Γ (sum55 A B); left55
 = λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right case zero suc rec →
     left55 (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right case zero suc rec)

right55 : ∀{Γ A B} → Tm55 Γ B → Tm55 Γ (sum55 A B); right55
 = λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case zero suc rec →
     right55 (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case zero suc rec)

case55 : ∀{Γ A B C} → Tm55 Γ (sum55 A B) → Tm55 Γ (arr55 A C) → Tm55 Γ (arr55 B C) → Tm55 Γ C; case55
 = λ t u v Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero suc rec →
     case55 (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero suc rec)
           (u Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero suc rec)
           (v Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero suc rec)

zero55  : ∀{Γ} → Tm55 Γ nat55; zero55
 = λ Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc rec → zero55

suc55 : ∀{Γ} → Tm55 Γ nat55 → Tm55 Γ nat55; suc55
 = λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec →
   suc55 (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec)

rec55 : ∀{Γ A} → Tm55 Γ nat55 → Tm55 Γ (arr55 nat55 (arr55 A A)) → Tm55 Γ A → Tm55 Γ A; rec55
 = λ t u v Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec55 →
     rec55 (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec55)
         (u Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec55)
         (v Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec55)

v055 : ∀{Γ A} → Tm55 (snoc55 Γ A) A; v055
 = var55 vz55

v155 : ∀{Γ A B} → Tm55 (snoc55 (snoc55 Γ A) B) A; v155
 = var55 (vs55 vz55)

v255 : ∀{Γ A B C} → Tm55 (snoc55 (snoc55 (snoc55 Γ A) B) C) A; v255
 = var55 (vs55 (vs55 vz55))

v355 : ∀{Γ A B C D} → Tm55 (snoc55 (snoc55 (snoc55 (snoc55 Γ A) B) C) D) A; v355
 = var55 (vs55 (vs55 (vs55 vz55)))

tbool55 : Ty55; tbool55
 = sum55 top55 top55

true55 : ∀{Γ} → Tm55 Γ tbool55; true55
 = left55 tt55

tfalse55 : ∀{Γ} → Tm55 Γ tbool55; tfalse55
 = right55 tt55

ifthenelse55 : ∀{Γ A} → Tm55 Γ (arr55 tbool55 (arr55 A (arr55 A A))); ifthenelse55
 = lam55 (lam55 (lam55 (case55 v255 (lam55 v255) (lam55 v155))))

times455 : ∀{Γ A} → Tm55 Γ (arr55 (arr55 A A) (arr55 A A)); times455
  = lam55 (lam55 (app55 v155 (app55 v155 (app55 v155 (app55 v155 v055)))))

add55 : ∀{Γ} → Tm55 Γ (arr55 nat55 (arr55 nat55 nat55)); add55
 = lam55 (rec55 v055
       (lam55 (lam55 (lam55 (suc55 (app55 v155 v055)))))
       (lam55 v055))

mul55 : ∀{Γ} → Tm55 Γ (arr55 nat55 (arr55 nat55 nat55)); mul55
 = lam55 (rec55 v055
       (lam55 (lam55 (lam55 (app55 (app55 add55 (app55 v155 v055)) v055))))
       (lam55 zero55))

fact55 : ∀{Γ} → Tm55 Γ (arr55 nat55 nat55); fact55
 = lam55 (rec55 v055 (lam55 (lam55 (app55 (app55 mul55 (suc55 v155)) v055)))
        (suc55 zero55))
{-# OPTIONS --type-in-type #-}

Ty56 : Set
Ty56 =
   (Ty56         : Set)
   (nat top bot  : Ty56)
   (arr prod sum : Ty56 → Ty56 → Ty56)
 → Ty56

nat56 : Ty56; nat56 = λ _ nat56 _ _ _ _ _ → nat56
top56 : Ty56; top56 = λ _ _ top56 _ _ _ _ → top56
bot56 : Ty56; bot56 = λ _ _ _ bot56 _ _ _ → bot56

arr56 : Ty56 → Ty56 → Ty56; arr56
 = λ A B Ty56 nat56 top56 bot56 arr56 prod sum →
     arr56 (A Ty56 nat56 top56 bot56 arr56 prod sum) (B Ty56 nat56 top56 bot56 arr56 prod sum)

prod56 : Ty56 → Ty56 → Ty56; prod56
 = λ A B Ty56 nat56 top56 bot56 arr56 prod56 sum →
     prod56 (A Ty56 nat56 top56 bot56 arr56 prod56 sum) (B Ty56 nat56 top56 bot56 arr56 prod56 sum)

sum56 : Ty56 → Ty56 → Ty56; sum56
 = λ A B Ty56 nat56 top56 bot56 arr56 prod56 sum56 →
     sum56 (A Ty56 nat56 top56 bot56 arr56 prod56 sum56) (B Ty56 nat56 top56 bot56 arr56 prod56 sum56)

Con56 : Set; Con56
 = (Con56 : Set)
   (nil  : Con56)
   (snoc : Con56 → Ty56 → Con56)
 → Con56

nil56 : Con56; nil56
 = λ Con56 nil56 snoc → nil56

snoc56 : Con56 → Ty56 → Con56; snoc56
 = λ Γ A Con56 nil56 snoc56 → snoc56 (Γ Con56 nil56 snoc56) A

Var56 : Con56 → Ty56 → Set; Var56
 = λ Γ A →
   (Var56 : Con56 → Ty56 → Set)
   (vz  : ∀{Γ A} → Var56 (snoc56 Γ A) A)
   (vs  : ∀{Γ B A} → Var56 Γ A → Var56 (snoc56 Γ B) A)
 → Var56 Γ A

vz56 : ∀{Γ A} → Var56 (snoc56 Γ A) A; vz56
 = λ Var56 vz56 vs → vz56

vs56 : ∀{Γ B A} → Var56 Γ A → Var56 (snoc56 Γ B) A; vs56
 = λ x Var56 vz56 vs56 → vs56 (x Var56 vz56 vs56)

Tm56 : Con56 → Ty56 → Set; Tm56
 = λ Γ A →
   (Tm56  : Con56 → Ty56 → Set)
   (var   : ∀{Γ A} → Var56 Γ A → Tm56 Γ A)
   (lam   : ∀{Γ A B} → Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B))
   (app   : ∀{Γ A B} → Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B)
   (tt    : ∀{Γ} → Tm56 Γ top56)
   (pair  : ∀{Γ A B} → Tm56 Γ A → Tm56 Γ B → Tm56 Γ (prod56 A B))
   (fst   : ∀{Γ A B} → Tm56 Γ (prod56 A B) → Tm56 Γ A)
   (snd   : ∀{Γ A B} → Tm56 Γ (prod56 A B) → Tm56 Γ B)
   (left  : ∀{Γ A B} → Tm56 Γ A → Tm56 Γ (sum56 A B))
   (right : ∀{Γ A B} → Tm56 Γ B → Tm56 Γ (sum56 A B))
   (case  : ∀{Γ A B C} → Tm56 Γ (sum56 A B) → Tm56 Γ (arr56 A C) → Tm56 Γ (arr56 B C) → Tm56 Γ C)
   (zero  : ∀{Γ} → Tm56 Γ nat56)
   (suc   : ∀{Γ} → Tm56 Γ nat56 → Tm56 Γ nat56)
   (rec   : ∀{Γ A} → Tm56 Γ nat56 → Tm56 Γ (arr56 nat56 (arr56 A A)) → Tm56 Γ A → Tm56 Γ A)
 → Tm56 Γ A

var56 : ∀{Γ A} → Var56 Γ A → Tm56 Γ A; var56
 = λ x Tm56 var56 lam app tt pair fst snd left right case zero suc rec →
     var56 x

lam56 : ∀{Γ A B} → Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B); lam56
 = λ t Tm56 var56 lam56 app tt pair fst snd left right case zero suc rec →
     lam56 (t Tm56 var56 lam56 app tt pair fst snd left right case zero suc rec)

app56 : ∀{Γ A B} → Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B; app56
 = λ t u Tm56 var56 lam56 app56 tt pair fst snd left right case zero suc rec →
     app56 (t Tm56 var56 lam56 app56 tt pair fst snd left right case zero suc rec)
         (u Tm56 var56 lam56 app56 tt pair fst snd left right case zero suc rec)

tt56 : ∀{Γ} → Tm56 Γ top56; tt56
 = λ Tm56 var56 lam56 app56 tt56 pair fst snd left right case zero suc rec → tt56

pair56 : ∀{Γ A B} → Tm56 Γ A → Tm56 Γ B → Tm56 Γ (prod56 A B); pair56
 = λ t u Tm56 var56 lam56 app56 tt56 pair56 fst snd left right case zero suc rec →
     pair56 (t Tm56 var56 lam56 app56 tt56 pair56 fst snd left right case zero suc rec)
          (u Tm56 var56 lam56 app56 tt56 pair56 fst snd left right case zero suc rec)

fst56 : ∀{Γ A B} → Tm56 Γ (prod56 A B) → Tm56 Γ A; fst56
 = λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd left right case zero suc rec →
     fst56 (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd left right case zero suc rec)

snd56 : ∀{Γ A B} → Tm56 Γ (prod56 A B) → Tm56 Γ B; snd56
 = λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left right case zero suc rec →
     snd56 (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left right case zero suc rec)

left56 : ∀{Γ A B} → Tm56 Γ A → Tm56 Γ (sum56 A B); left56
 = λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right case zero suc rec →
     left56 (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right case zero suc rec)

right56 : ∀{Γ A B} → Tm56 Γ B → Tm56 Γ (sum56 A B); right56
 = λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case zero suc rec →
     right56 (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case zero suc rec)

case56 : ∀{Γ A B C} → Tm56 Γ (sum56 A B) → Tm56 Γ (arr56 A C) → Tm56 Γ (arr56 B C) → Tm56 Γ C; case56
 = λ t u v Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero suc rec →
     case56 (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero suc rec)
           (u Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero suc rec)
           (v Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero suc rec)

zero56  : ∀{Γ} → Tm56 Γ nat56; zero56
 = λ Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc rec → zero56

suc56 : ∀{Γ} → Tm56 Γ nat56 → Tm56 Γ nat56; suc56
 = λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec →
   suc56 (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec)

rec56 : ∀{Γ A} → Tm56 Γ nat56 → Tm56 Γ (arr56 nat56 (arr56 A A)) → Tm56 Γ A → Tm56 Γ A; rec56
 = λ t u v Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec56 →
     rec56 (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec56)
         (u Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec56)
         (v Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec56)

v056 : ∀{Γ A} → Tm56 (snoc56 Γ A) A; v056
 = var56 vz56

v156 : ∀{Γ A B} → Tm56 (snoc56 (snoc56 Γ A) B) A; v156
 = var56 (vs56 vz56)

v256 : ∀{Γ A B C} → Tm56 (snoc56 (snoc56 (snoc56 Γ A) B) C) A; v256
 = var56 (vs56 (vs56 vz56))

v356 : ∀{Γ A B C D} → Tm56 (snoc56 (snoc56 (snoc56 (snoc56 Γ A) B) C) D) A; v356
 = var56 (vs56 (vs56 (vs56 vz56)))

tbool56 : Ty56; tbool56
 = sum56 top56 top56

true56 : ∀{Γ} → Tm56 Γ tbool56; true56
 = left56 tt56

tfalse56 : ∀{Γ} → Tm56 Γ tbool56; tfalse56
 = right56 tt56

ifthenelse56 : ∀{Γ A} → Tm56 Γ (arr56 tbool56 (arr56 A (arr56 A A))); ifthenelse56
 = lam56 (lam56 (lam56 (case56 v256 (lam56 v256) (lam56 v156))))

times456 : ∀{Γ A} → Tm56 Γ (arr56 (arr56 A A) (arr56 A A)); times456
  = lam56 (lam56 (app56 v156 (app56 v156 (app56 v156 (app56 v156 v056)))))

add56 : ∀{Γ} → Tm56 Γ (arr56 nat56 (arr56 nat56 nat56)); add56
 = lam56 (rec56 v056
       (lam56 (lam56 (lam56 (suc56 (app56 v156 v056)))))
       (lam56 v056))

mul56 : ∀{Γ} → Tm56 Γ (arr56 nat56 (arr56 nat56 nat56)); mul56
 = lam56 (rec56 v056
       (lam56 (lam56 (lam56 (app56 (app56 add56 (app56 v156 v056)) v056))))
       (lam56 zero56))

fact56 : ∀{Γ} → Tm56 Γ (arr56 nat56 nat56); fact56
 = lam56 (rec56 v056 (lam56 (lam56 (app56 (app56 mul56 (suc56 v156)) v056)))
        (suc56 zero56))
{-# OPTIONS --type-in-type #-}

Ty57 : Set
Ty57 =
   (Ty57         : Set)
   (nat top bot  : Ty57)
   (arr prod sum : Ty57 → Ty57 → Ty57)
 → Ty57

nat57 : Ty57; nat57 = λ _ nat57 _ _ _ _ _ → nat57
top57 : Ty57; top57 = λ _ _ top57 _ _ _ _ → top57
bot57 : Ty57; bot57 = λ _ _ _ bot57 _ _ _ → bot57

arr57 : Ty57 → Ty57 → Ty57; arr57
 = λ A B Ty57 nat57 top57 bot57 arr57 prod sum →
     arr57 (A Ty57 nat57 top57 bot57 arr57 prod sum) (B Ty57 nat57 top57 bot57 arr57 prod sum)

prod57 : Ty57 → Ty57 → Ty57; prod57
 = λ A B Ty57 nat57 top57 bot57 arr57 prod57 sum →
     prod57 (A Ty57 nat57 top57 bot57 arr57 prod57 sum) (B Ty57 nat57 top57 bot57 arr57 prod57 sum)

sum57 : Ty57 → Ty57 → Ty57; sum57
 = λ A B Ty57 nat57 top57 bot57 arr57 prod57 sum57 →
     sum57 (A Ty57 nat57 top57 bot57 arr57 prod57 sum57) (B Ty57 nat57 top57 bot57 arr57 prod57 sum57)

Con57 : Set; Con57
 = (Con57 : Set)
   (nil  : Con57)
   (snoc : Con57 → Ty57 → Con57)
 → Con57

nil57 : Con57; nil57
 = λ Con57 nil57 snoc → nil57

snoc57 : Con57 → Ty57 → Con57; snoc57
 = λ Γ A Con57 nil57 snoc57 → snoc57 (Γ Con57 nil57 snoc57) A

Var57 : Con57 → Ty57 → Set; Var57
 = λ Γ A →
   (Var57 : Con57 → Ty57 → Set)
   (vz  : ∀{Γ A} → Var57 (snoc57 Γ A) A)
   (vs  : ∀{Γ B A} → Var57 Γ A → Var57 (snoc57 Γ B) A)
 → Var57 Γ A

vz57 : ∀{Γ A} → Var57 (snoc57 Γ A) A; vz57
 = λ Var57 vz57 vs → vz57

vs57 : ∀{Γ B A} → Var57 Γ A → Var57 (snoc57 Γ B) A; vs57
 = λ x Var57 vz57 vs57 → vs57 (x Var57 vz57 vs57)

Tm57 : Con57 → Ty57 → Set; Tm57
 = λ Γ A →
   (Tm57  : Con57 → Ty57 → Set)
   (var   : ∀{Γ A} → Var57 Γ A → Tm57 Γ A)
   (lam   : ∀{Γ A B} → Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B))
   (app   : ∀{Γ A B} → Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B)
   (tt    : ∀{Γ} → Tm57 Γ top57)
   (pair  : ∀{Γ A B} → Tm57 Γ A → Tm57 Γ B → Tm57 Γ (prod57 A B))
   (fst   : ∀{Γ A B} → Tm57 Γ (prod57 A B) → Tm57 Γ A)
   (snd   : ∀{Γ A B} → Tm57 Γ (prod57 A B) → Tm57 Γ B)
   (left  : ∀{Γ A B} → Tm57 Γ A → Tm57 Γ (sum57 A B))
   (right : ∀{Γ A B} → Tm57 Γ B → Tm57 Γ (sum57 A B))
   (case  : ∀{Γ A B C} → Tm57 Γ (sum57 A B) → Tm57 Γ (arr57 A C) → Tm57 Γ (arr57 B C) → Tm57 Γ C)
   (zero  : ∀{Γ} → Tm57 Γ nat57)
   (suc   : ∀{Γ} → Tm57 Γ nat57 → Tm57 Γ nat57)
   (rec   : ∀{Γ A} → Tm57 Γ nat57 → Tm57 Γ (arr57 nat57 (arr57 A A)) → Tm57 Γ A → Tm57 Γ A)
 → Tm57 Γ A

var57 : ∀{Γ A} → Var57 Γ A → Tm57 Γ A; var57
 = λ x Tm57 var57 lam app tt pair fst snd left right case zero suc rec →
     var57 x

lam57 : ∀{Γ A B} → Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B); lam57
 = λ t Tm57 var57 lam57 app tt pair fst snd left right case zero suc rec →
     lam57 (t Tm57 var57 lam57 app tt pair fst snd left right case zero suc rec)

app57 : ∀{Γ A B} → Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B; app57
 = λ t u Tm57 var57 lam57 app57 tt pair fst snd left right case zero suc rec →
     app57 (t Tm57 var57 lam57 app57 tt pair fst snd left right case zero suc rec)
         (u Tm57 var57 lam57 app57 tt pair fst snd left right case zero suc rec)

tt57 : ∀{Γ} → Tm57 Γ top57; tt57
 = λ Tm57 var57 lam57 app57 tt57 pair fst snd left right case zero suc rec → tt57

pair57 : ∀{Γ A B} → Tm57 Γ A → Tm57 Γ B → Tm57 Γ (prod57 A B); pair57
 = λ t u Tm57 var57 lam57 app57 tt57 pair57 fst snd left right case zero suc rec →
     pair57 (t Tm57 var57 lam57 app57 tt57 pair57 fst snd left right case zero suc rec)
          (u Tm57 var57 lam57 app57 tt57 pair57 fst snd left right case zero suc rec)

fst57 : ∀{Γ A B} → Tm57 Γ (prod57 A B) → Tm57 Γ A; fst57
 = λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd left right case zero suc rec →
     fst57 (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd left right case zero suc rec)

snd57 : ∀{Γ A B} → Tm57 Γ (prod57 A B) → Tm57 Γ B; snd57
 = λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left right case zero suc rec →
     snd57 (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left right case zero suc rec)

left57 : ∀{Γ A B} → Tm57 Γ A → Tm57 Γ (sum57 A B); left57
 = λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right case zero suc rec →
     left57 (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right case zero suc rec)

right57 : ∀{Γ A B} → Tm57 Γ B → Tm57 Γ (sum57 A B); right57
 = λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case zero suc rec →
     right57 (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case zero suc rec)

case57 : ∀{Γ A B C} → Tm57 Γ (sum57 A B) → Tm57 Γ (arr57 A C) → Tm57 Γ (arr57 B C) → Tm57 Γ C; case57
 = λ t u v Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero suc rec →
     case57 (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero suc rec)
           (u Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero suc rec)
           (v Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero suc rec)

zero57  : ∀{Γ} → Tm57 Γ nat57; zero57
 = λ Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc rec → zero57

suc57 : ∀{Γ} → Tm57 Γ nat57 → Tm57 Γ nat57; suc57
 = λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec →
   suc57 (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec)

rec57 : ∀{Γ A} → Tm57 Γ nat57 → Tm57 Γ (arr57 nat57 (arr57 A A)) → Tm57 Γ A → Tm57 Γ A; rec57
 = λ t u v Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec57 →
     rec57 (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec57)
         (u Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec57)
         (v Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec57)

v057 : ∀{Γ A} → Tm57 (snoc57 Γ A) A; v057
 = var57 vz57

v157 : ∀{Γ A B} → Tm57 (snoc57 (snoc57 Γ A) B) A; v157
 = var57 (vs57 vz57)

v257 : ∀{Γ A B C} → Tm57 (snoc57 (snoc57 (snoc57 Γ A) B) C) A; v257
 = var57 (vs57 (vs57 vz57))

v357 : ∀{Γ A B C D} → Tm57 (snoc57 (snoc57 (snoc57 (snoc57 Γ A) B) C) D) A; v357
 = var57 (vs57 (vs57 (vs57 vz57)))

tbool57 : Ty57; tbool57
 = sum57 top57 top57

true57 : ∀{Γ} → Tm57 Γ tbool57; true57
 = left57 tt57

tfalse57 : ∀{Γ} → Tm57 Γ tbool57; tfalse57
 = right57 tt57

ifthenelse57 : ∀{Γ A} → Tm57 Γ (arr57 tbool57 (arr57 A (arr57 A A))); ifthenelse57
 = lam57 (lam57 (lam57 (case57 v257 (lam57 v257) (lam57 v157))))

times457 : ∀{Γ A} → Tm57 Γ (arr57 (arr57 A A) (arr57 A A)); times457
  = lam57 (lam57 (app57 v157 (app57 v157 (app57 v157 (app57 v157 v057)))))

add57 : ∀{Γ} → Tm57 Γ (arr57 nat57 (arr57 nat57 nat57)); add57
 = lam57 (rec57 v057
       (lam57 (lam57 (lam57 (suc57 (app57 v157 v057)))))
       (lam57 v057))

mul57 : ∀{Γ} → Tm57 Γ (arr57 nat57 (arr57 nat57 nat57)); mul57
 = lam57 (rec57 v057
       (lam57 (lam57 (lam57 (app57 (app57 add57 (app57 v157 v057)) v057))))
       (lam57 zero57))

fact57 : ∀{Γ} → Tm57 Γ (arr57 nat57 nat57); fact57
 = lam57 (rec57 v057 (lam57 (lam57 (app57 (app57 mul57 (suc57 v157)) v057)))
        (suc57 zero57))
{-# OPTIONS --type-in-type #-}

Ty58 : Set
Ty58 =
   (Ty58         : Set)
   (nat top bot  : Ty58)
   (arr prod sum : Ty58 → Ty58 → Ty58)
 → Ty58

nat58 : Ty58; nat58 = λ _ nat58 _ _ _ _ _ → nat58
top58 : Ty58; top58 = λ _ _ top58 _ _ _ _ → top58
bot58 : Ty58; bot58 = λ _ _ _ bot58 _ _ _ → bot58

arr58 : Ty58 → Ty58 → Ty58; arr58
 = λ A B Ty58 nat58 top58 bot58 arr58 prod sum →
     arr58 (A Ty58 nat58 top58 bot58 arr58 prod sum) (B Ty58 nat58 top58 bot58 arr58 prod sum)

prod58 : Ty58 → Ty58 → Ty58; prod58
 = λ A B Ty58 nat58 top58 bot58 arr58 prod58 sum →
     prod58 (A Ty58 nat58 top58 bot58 arr58 prod58 sum) (B Ty58 nat58 top58 bot58 arr58 prod58 sum)

sum58 : Ty58 → Ty58 → Ty58; sum58
 = λ A B Ty58 nat58 top58 bot58 arr58 prod58 sum58 →
     sum58 (A Ty58 nat58 top58 bot58 arr58 prod58 sum58) (B Ty58 nat58 top58 bot58 arr58 prod58 sum58)

Con58 : Set; Con58
 = (Con58 : Set)
   (nil  : Con58)
   (snoc : Con58 → Ty58 → Con58)
 → Con58

nil58 : Con58; nil58
 = λ Con58 nil58 snoc → nil58

snoc58 : Con58 → Ty58 → Con58; snoc58
 = λ Γ A Con58 nil58 snoc58 → snoc58 (Γ Con58 nil58 snoc58) A

Var58 : Con58 → Ty58 → Set; Var58
 = λ Γ A →
   (Var58 : Con58 → Ty58 → Set)
   (vz  : ∀{Γ A} → Var58 (snoc58 Γ A) A)
   (vs  : ∀{Γ B A} → Var58 Γ A → Var58 (snoc58 Γ B) A)
 → Var58 Γ A

vz58 : ∀{Γ A} → Var58 (snoc58 Γ A) A; vz58
 = λ Var58 vz58 vs → vz58

vs58 : ∀{Γ B A} → Var58 Γ A → Var58 (snoc58 Γ B) A; vs58
 = λ x Var58 vz58 vs58 → vs58 (x Var58 vz58 vs58)

Tm58 : Con58 → Ty58 → Set; Tm58
 = λ Γ A →
   (Tm58  : Con58 → Ty58 → Set)
   (var   : ∀{Γ A} → Var58 Γ A → Tm58 Γ A)
   (lam   : ∀{Γ A B} → Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B))
   (app   : ∀{Γ A B} → Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B)
   (tt    : ∀{Γ} → Tm58 Γ top58)
   (pair  : ∀{Γ A B} → Tm58 Γ A → Tm58 Γ B → Tm58 Γ (prod58 A B))
   (fst   : ∀{Γ A B} → Tm58 Γ (prod58 A B) → Tm58 Γ A)
   (snd   : ∀{Γ A B} → Tm58 Γ (prod58 A B) → Tm58 Γ B)
   (left  : ∀{Γ A B} → Tm58 Γ A → Tm58 Γ (sum58 A B))
   (right : ∀{Γ A B} → Tm58 Γ B → Tm58 Γ (sum58 A B))
   (case  : ∀{Γ A B C} → Tm58 Γ (sum58 A B) → Tm58 Γ (arr58 A C) → Tm58 Γ (arr58 B C) → Tm58 Γ C)
   (zero  : ∀{Γ} → Tm58 Γ nat58)
   (suc   : ∀{Γ} → Tm58 Γ nat58 → Tm58 Γ nat58)
   (rec   : ∀{Γ A} → Tm58 Γ nat58 → Tm58 Γ (arr58 nat58 (arr58 A A)) → Tm58 Γ A → Tm58 Γ A)
 → Tm58 Γ A

var58 : ∀{Γ A} → Var58 Γ A → Tm58 Γ A; var58
 = λ x Tm58 var58 lam app tt pair fst snd left right case zero suc rec →
     var58 x

lam58 : ∀{Γ A B} → Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B); lam58
 = λ t Tm58 var58 lam58 app tt pair fst snd left right case zero suc rec →
     lam58 (t Tm58 var58 lam58 app tt pair fst snd left right case zero suc rec)

app58 : ∀{Γ A B} → Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B; app58
 = λ t u Tm58 var58 lam58 app58 tt pair fst snd left right case zero suc rec →
     app58 (t Tm58 var58 lam58 app58 tt pair fst snd left right case zero suc rec)
         (u Tm58 var58 lam58 app58 tt pair fst snd left right case zero suc rec)

tt58 : ∀{Γ} → Tm58 Γ top58; tt58
 = λ Tm58 var58 lam58 app58 tt58 pair fst snd left right case zero suc rec → tt58

pair58 : ∀{Γ A B} → Tm58 Γ A → Tm58 Γ B → Tm58 Γ (prod58 A B); pair58
 = λ t u Tm58 var58 lam58 app58 tt58 pair58 fst snd left right case zero suc rec →
     pair58 (t Tm58 var58 lam58 app58 tt58 pair58 fst snd left right case zero suc rec)
          (u Tm58 var58 lam58 app58 tt58 pair58 fst snd left right case zero suc rec)

fst58 : ∀{Γ A B} → Tm58 Γ (prod58 A B) → Tm58 Γ A; fst58
 = λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd left right case zero suc rec →
     fst58 (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd left right case zero suc rec)

snd58 : ∀{Γ A B} → Tm58 Γ (prod58 A B) → Tm58 Γ B; snd58
 = λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left right case zero suc rec →
     snd58 (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left right case zero suc rec)

left58 : ∀{Γ A B} → Tm58 Γ A → Tm58 Γ (sum58 A B); left58
 = λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right case zero suc rec →
     left58 (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right case zero suc rec)

right58 : ∀{Γ A B} → Tm58 Γ B → Tm58 Γ (sum58 A B); right58
 = λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case zero suc rec →
     right58 (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case zero suc rec)

case58 : ∀{Γ A B C} → Tm58 Γ (sum58 A B) → Tm58 Γ (arr58 A C) → Tm58 Γ (arr58 B C) → Tm58 Γ C; case58
 = λ t u v Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero suc rec →
     case58 (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero suc rec)
           (u Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero suc rec)
           (v Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero suc rec)

zero58  : ∀{Γ} → Tm58 Γ nat58; zero58
 = λ Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc rec → zero58

suc58 : ∀{Γ} → Tm58 Γ nat58 → Tm58 Γ nat58; suc58
 = λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec →
   suc58 (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec)

rec58 : ∀{Γ A} → Tm58 Γ nat58 → Tm58 Γ (arr58 nat58 (arr58 A A)) → Tm58 Γ A → Tm58 Γ A; rec58
 = λ t u v Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec58 →
     rec58 (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec58)
         (u Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec58)
         (v Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec58)

v058 : ∀{Γ A} → Tm58 (snoc58 Γ A) A; v058
 = var58 vz58

v158 : ∀{Γ A B} → Tm58 (snoc58 (snoc58 Γ A) B) A; v158
 = var58 (vs58 vz58)

v258 : ∀{Γ A B C} → Tm58 (snoc58 (snoc58 (snoc58 Γ A) B) C) A; v258
 = var58 (vs58 (vs58 vz58))

v358 : ∀{Γ A B C D} → Tm58 (snoc58 (snoc58 (snoc58 (snoc58 Γ A) B) C) D) A; v358
 = var58 (vs58 (vs58 (vs58 vz58)))

tbool58 : Ty58; tbool58
 = sum58 top58 top58

true58 : ∀{Γ} → Tm58 Γ tbool58; true58
 = left58 tt58

tfalse58 : ∀{Γ} → Tm58 Γ tbool58; tfalse58
 = right58 tt58

ifthenelse58 : ∀{Γ A} → Tm58 Γ (arr58 tbool58 (arr58 A (arr58 A A))); ifthenelse58
 = lam58 (lam58 (lam58 (case58 v258 (lam58 v258) (lam58 v158))))

times458 : ∀{Γ A} → Tm58 Γ (arr58 (arr58 A A) (arr58 A A)); times458
  = lam58 (lam58 (app58 v158 (app58 v158 (app58 v158 (app58 v158 v058)))))

add58 : ∀{Γ} → Tm58 Γ (arr58 nat58 (arr58 nat58 nat58)); add58
 = lam58 (rec58 v058
       (lam58 (lam58 (lam58 (suc58 (app58 v158 v058)))))
       (lam58 v058))

mul58 : ∀{Γ} → Tm58 Γ (arr58 nat58 (arr58 nat58 nat58)); mul58
 = lam58 (rec58 v058
       (lam58 (lam58 (lam58 (app58 (app58 add58 (app58 v158 v058)) v058))))
       (lam58 zero58))

fact58 : ∀{Γ} → Tm58 Γ (arr58 nat58 nat58); fact58
 = lam58 (rec58 v058 (lam58 (lam58 (app58 (app58 mul58 (suc58 v158)) v058)))
        (suc58 zero58))
{-# OPTIONS --type-in-type #-}

Ty59 : Set
Ty59 =
   (Ty59         : Set)
   (nat top bot  : Ty59)
   (arr prod sum : Ty59 → Ty59 → Ty59)
 → Ty59

nat59 : Ty59; nat59 = λ _ nat59 _ _ _ _ _ → nat59
top59 : Ty59; top59 = λ _ _ top59 _ _ _ _ → top59
bot59 : Ty59; bot59 = λ _ _ _ bot59 _ _ _ → bot59

arr59 : Ty59 → Ty59 → Ty59; arr59
 = λ A B Ty59 nat59 top59 bot59 arr59 prod sum →
     arr59 (A Ty59 nat59 top59 bot59 arr59 prod sum) (B Ty59 nat59 top59 bot59 arr59 prod sum)

prod59 : Ty59 → Ty59 → Ty59; prod59
 = λ A B Ty59 nat59 top59 bot59 arr59 prod59 sum →
     prod59 (A Ty59 nat59 top59 bot59 arr59 prod59 sum) (B Ty59 nat59 top59 bot59 arr59 prod59 sum)

sum59 : Ty59 → Ty59 → Ty59; sum59
 = λ A B Ty59 nat59 top59 bot59 arr59 prod59 sum59 →
     sum59 (A Ty59 nat59 top59 bot59 arr59 prod59 sum59) (B Ty59 nat59 top59 bot59 arr59 prod59 sum59)

Con59 : Set; Con59
 = (Con59 : Set)
   (nil  : Con59)
   (snoc : Con59 → Ty59 → Con59)
 → Con59

nil59 : Con59; nil59
 = λ Con59 nil59 snoc → nil59

snoc59 : Con59 → Ty59 → Con59; snoc59
 = λ Γ A Con59 nil59 snoc59 → snoc59 (Γ Con59 nil59 snoc59) A

Var59 : Con59 → Ty59 → Set; Var59
 = λ Γ A →
   (Var59 : Con59 → Ty59 → Set)
   (vz  : ∀{Γ A} → Var59 (snoc59 Γ A) A)
   (vs  : ∀{Γ B A} → Var59 Γ A → Var59 (snoc59 Γ B) A)
 → Var59 Γ A

vz59 : ∀{Γ A} → Var59 (snoc59 Γ A) A; vz59
 = λ Var59 vz59 vs → vz59

vs59 : ∀{Γ B A} → Var59 Γ A → Var59 (snoc59 Γ B) A; vs59
 = λ x Var59 vz59 vs59 → vs59 (x Var59 vz59 vs59)

Tm59 : Con59 → Ty59 → Set; Tm59
 = λ Γ A →
   (Tm59  : Con59 → Ty59 → Set)
   (var   : ∀{Γ A} → Var59 Γ A → Tm59 Γ A)
   (lam   : ∀{Γ A B} → Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B))
   (app   : ∀{Γ A B} → Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B)
   (tt    : ∀{Γ} → Tm59 Γ top59)
   (pair  : ∀{Γ A B} → Tm59 Γ A → Tm59 Γ B → Tm59 Γ (prod59 A B))
   (fst   : ∀{Γ A B} → Tm59 Γ (prod59 A B) → Tm59 Γ A)
   (snd   : ∀{Γ A B} → Tm59 Γ (prod59 A B) → Tm59 Γ B)
   (left  : ∀{Γ A B} → Tm59 Γ A → Tm59 Γ (sum59 A B))
   (right : ∀{Γ A B} → Tm59 Γ B → Tm59 Γ (sum59 A B))
   (case  : ∀{Γ A B C} → Tm59 Γ (sum59 A B) → Tm59 Γ (arr59 A C) → Tm59 Γ (arr59 B C) → Tm59 Γ C)
   (zero  : ∀{Γ} → Tm59 Γ nat59)
   (suc   : ∀{Γ} → Tm59 Γ nat59 → Tm59 Γ nat59)
   (rec   : ∀{Γ A} → Tm59 Γ nat59 → Tm59 Γ (arr59 nat59 (arr59 A A)) → Tm59 Γ A → Tm59 Γ A)
 → Tm59 Γ A

var59 : ∀{Γ A} → Var59 Γ A → Tm59 Γ A; var59
 = λ x Tm59 var59 lam app tt pair fst snd left right case zero suc rec →
     var59 x

lam59 : ∀{Γ A B} → Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B); lam59
 = λ t Tm59 var59 lam59 app tt pair fst snd left right case zero suc rec →
     lam59 (t Tm59 var59 lam59 app tt pair fst snd left right case zero suc rec)

app59 : ∀{Γ A B} → Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B; app59
 = λ t u Tm59 var59 lam59 app59 tt pair fst snd left right case zero suc rec →
     app59 (t Tm59 var59 lam59 app59 tt pair fst snd left right case zero suc rec)
         (u Tm59 var59 lam59 app59 tt pair fst snd left right case zero suc rec)

tt59 : ∀{Γ} → Tm59 Γ top59; tt59
 = λ Tm59 var59 lam59 app59 tt59 pair fst snd left right case zero suc rec → tt59

pair59 : ∀{Γ A B} → Tm59 Γ A → Tm59 Γ B → Tm59 Γ (prod59 A B); pair59
 = λ t u Tm59 var59 lam59 app59 tt59 pair59 fst snd left right case zero suc rec →
     pair59 (t Tm59 var59 lam59 app59 tt59 pair59 fst snd left right case zero suc rec)
          (u Tm59 var59 lam59 app59 tt59 pair59 fst snd left right case zero suc rec)

fst59 : ∀{Γ A B} → Tm59 Γ (prod59 A B) → Tm59 Γ A; fst59
 = λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd left right case zero suc rec →
     fst59 (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd left right case zero suc rec)

snd59 : ∀{Γ A B} → Tm59 Γ (prod59 A B) → Tm59 Γ B; snd59
 = λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left right case zero suc rec →
     snd59 (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left right case zero suc rec)

left59 : ∀{Γ A B} → Tm59 Γ A → Tm59 Γ (sum59 A B); left59
 = λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right case zero suc rec →
     left59 (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right case zero suc rec)

right59 : ∀{Γ A B} → Tm59 Γ B → Tm59 Γ (sum59 A B); right59
 = λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case zero suc rec →
     right59 (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case zero suc rec)

case59 : ∀{Γ A B C} → Tm59 Γ (sum59 A B) → Tm59 Γ (arr59 A C) → Tm59 Γ (arr59 B C) → Tm59 Γ C; case59
 = λ t u v Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero suc rec →
     case59 (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero suc rec)
           (u Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero suc rec)
           (v Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero suc rec)

zero59  : ∀{Γ} → Tm59 Γ nat59; zero59
 = λ Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc rec → zero59

suc59 : ∀{Γ} → Tm59 Γ nat59 → Tm59 Γ nat59; suc59
 = λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec →
   suc59 (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec)

rec59 : ∀{Γ A} → Tm59 Γ nat59 → Tm59 Γ (arr59 nat59 (arr59 A A)) → Tm59 Γ A → Tm59 Γ A; rec59
 = λ t u v Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec59 →
     rec59 (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec59)
         (u Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec59)
         (v Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec59)

v059 : ∀{Γ A} → Tm59 (snoc59 Γ A) A; v059
 = var59 vz59

v159 : ∀{Γ A B} → Tm59 (snoc59 (snoc59 Γ A) B) A; v159
 = var59 (vs59 vz59)

v259 : ∀{Γ A B C} → Tm59 (snoc59 (snoc59 (snoc59 Γ A) B) C) A; v259
 = var59 (vs59 (vs59 vz59))

v359 : ∀{Γ A B C D} → Tm59 (snoc59 (snoc59 (snoc59 (snoc59 Γ A) B) C) D) A; v359
 = var59 (vs59 (vs59 (vs59 vz59)))

tbool59 : Ty59; tbool59
 = sum59 top59 top59

true59 : ∀{Γ} → Tm59 Γ tbool59; true59
 = left59 tt59

tfalse59 : ∀{Γ} → Tm59 Γ tbool59; tfalse59
 = right59 tt59

ifthenelse59 : ∀{Γ A} → Tm59 Γ (arr59 tbool59 (arr59 A (arr59 A A))); ifthenelse59
 = lam59 (lam59 (lam59 (case59 v259 (lam59 v259) (lam59 v159))))

times459 : ∀{Γ A} → Tm59 Γ (arr59 (arr59 A A) (arr59 A A)); times459
  = lam59 (lam59 (app59 v159 (app59 v159 (app59 v159 (app59 v159 v059)))))

add59 : ∀{Γ} → Tm59 Γ (arr59 nat59 (arr59 nat59 nat59)); add59
 = lam59 (rec59 v059
       (lam59 (lam59 (lam59 (suc59 (app59 v159 v059)))))
       (lam59 v059))

mul59 : ∀{Γ} → Tm59 Γ (arr59 nat59 (arr59 nat59 nat59)); mul59
 = lam59 (rec59 v059
       (lam59 (lam59 (lam59 (app59 (app59 add59 (app59 v159 v059)) v059))))
       (lam59 zero59))

fact59 : ∀{Γ} → Tm59 Γ (arr59 nat59 nat59); fact59
 = lam59 (rec59 v059 (lam59 (lam59 (app59 (app59 mul59 (suc59 v159)) v059)))
        (suc59 zero59))
{-# OPTIONS --type-in-type #-}

Ty60 : Set
Ty60 =
   (Ty60         : Set)
   (nat top bot  : Ty60)
   (arr prod sum : Ty60 → Ty60 → Ty60)
 → Ty60

nat60 : Ty60; nat60 = λ _ nat60 _ _ _ _ _ → nat60
top60 : Ty60; top60 = λ _ _ top60 _ _ _ _ → top60
bot60 : Ty60; bot60 = λ _ _ _ bot60 _ _ _ → bot60

arr60 : Ty60 → Ty60 → Ty60; arr60
 = λ A B Ty60 nat60 top60 bot60 arr60 prod sum →
     arr60 (A Ty60 nat60 top60 bot60 arr60 prod sum) (B Ty60 nat60 top60 bot60 arr60 prod sum)

prod60 : Ty60 → Ty60 → Ty60; prod60
 = λ A B Ty60 nat60 top60 bot60 arr60 prod60 sum →
     prod60 (A Ty60 nat60 top60 bot60 arr60 prod60 sum) (B Ty60 nat60 top60 bot60 arr60 prod60 sum)

sum60 : Ty60 → Ty60 → Ty60; sum60
 = λ A B Ty60 nat60 top60 bot60 arr60 prod60 sum60 →
     sum60 (A Ty60 nat60 top60 bot60 arr60 prod60 sum60) (B Ty60 nat60 top60 bot60 arr60 prod60 sum60)

Con60 : Set; Con60
 = (Con60 : Set)
   (nil  : Con60)
   (snoc : Con60 → Ty60 → Con60)
 → Con60

nil60 : Con60; nil60
 = λ Con60 nil60 snoc → nil60

snoc60 : Con60 → Ty60 → Con60; snoc60
 = λ Γ A Con60 nil60 snoc60 → snoc60 (Γ Con60 nil60 snoc60) A

Var60 : Con60 → Ty60 → Set; Var60
 = λ Γ A →
   (Var60 : Con60 → Ty60 → Set)
   (vz  : ∀{Γ A} → Var60 (snoc60 Γ A) A)
   (vs  : ∀{Γ B A} → Var60 Γ A → Var60 (snoc60 Γ B) A)
 → Var60 Γ A

vz60 : ∀{Γ A} → Var60 (snoc60 Γ A) A; vz60
 = λ Var60 vz60 vs → vz60

vs60 : ∀{Γ B A} → Var60 Γ A → Var60 (snoc60 Γ B) A; vs60
 = λ x Var60 vz60 vs60 → vs60 (x Var60 vz60 vs60)

Tm60 : Con60 → Ty60 → Set; Tm60
 = λ Γ A →
   (Tm60  : Con60 → Ty60 → Set)
   (var   : ∀{Γ A} → Var60 Γ A → Tm60 Γ A)
   (lam   : ∀{Γ A B} → Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B))
   (app   : ∀{Γ A B} → Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B)
   (tt    : ∀{Γ} → Tm60 Γ top60)
   (pair  : ∀{Γ A B} → Tm60 Γ A → Tm60 Γ B → Tm60 Γ (prod60 A B))
   (fst   : ∀{Γ A B} → Tm60 Γ (prod60 A B) → Tm60 Γ A)
   (snd   : ∀{Γ A B} → Tm60 Γ (prod60 A B) → Tm60 Γ B)
   (left  : ∀{Γ A B} → Tm60 Γ A → Tm60 Γ (sum60 A B))
   (right : ∀{Γ A B} → Tm60 Γ B → Tm60 Γ (sum60 A B))
   (case  : ∀{Γ A B C} → Tm60 Γ (sum60 A B) → Tm60 Γ (arr60 A C) → Tm60 Γ (arr60 B C) → Tm60 Γ C)
   (zero  : ∀{Γ} → Tm60 Γ nat60)
   (suc   : ∀{Γ} → Tm60 Γ nat60 → Tm60 Γ nat60)
   (rec   : ∀{Γ A} → Tm60 Γ nat60 → Tm60 Γ (arr60 nat60 (arr60 A A)) → Tm60 Γ A → Tm60 Γ A)
 → Tm60 Γ A

var60 : ∀{Γ A} → Var60 Γ A → Tm60 Γ A; var60
 = λ x Tm60 var60 lam app tt pair fst snd left right case zero suc rec →
     var60 x

lam60 : ∀{Γ A B} → Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B); lam60
 = λ t Tm60 var60 lam60 app tt pair fst snd left right case zero suc rec →
     lam60 (t Tm60 var60 lam60 app tt pair fst snd left right case zero suc rec)

app60 : ∀{Γ A B} → Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B; app60
 = λ t u Tm60 var60 lam60 app60 tt pair fst snd left right case zero suc rec →
     app60 (t Tm60 var60 lam60 app60 tt pair fst snd left right case zero suc rec)
         (u Tm60 var60 lam60 app60 tt pair fst snd left right case zero suc rec)

tt60 : ∀{Γ} → Tm60 Γ top60; tt60
 = λ Tm60 var60 lam60 app60 tt60 pair fst snd left right case zero suc rec → tt60

pair60 : ∀{Γ A B} → Tm60 Γ A → Tm60 Γ B → Tm60 Γ (prod60 A B); pair60
 = λ t u Tm60 var60 lam60 app60 tt60 pair60 fst snd left right case zero suc rec →
     pair60 (t Tm60 var60 lam60 app60 tt60 pair60 fst snd left right case zero suc rec)
          (u Tm60 var60 lam60 app60 tt60 pair60 fst snd left right case zero suc rec)

fst60 : ∀{Γ A B} → Tm60 Γ (prod60 A B) → Tm60 Γ A; fst60
 = λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd left right case zero suc rec →
     fst60 (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd left right case zero suc rec)

snd60 : ∀{Γ A B} → Tm60 Γ (prod60 A B) → Tm60 Γ B; snd60
 = λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left right case zero suc rec →
     snd60 (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left right case zero suc rec)

left60 : ∀{Γ A B} → Tm60 Γ A → Tm60 Γ (sum60 A B); left60
 = λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right case zero suc rec →
     left60 (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right case zero suc rec)

right60 : ∀{Γ A B} → Tm60 Γ B → Tm60 Γ (sum60 A B); right60
 = λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case zero suc rec →
     right60 (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case zero suc rec)

case60 : ∀{Γ A B C} → Tm60 Γ (sum60 A B) → Tm60 Γ (arr60 A C) → Tm60 Γ (arr60 B C) → Tm60 Γ C; case60
 = λ t u v Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero suc rec →
     case60 (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero suc rec)
           (u Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero suc rec)
           (v Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero suc rec)

zero60  : ∀{Γ} → Tm60 Γ nat60; zero60
 = λ Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc rec → zero60

suc60 : ∀{Γ} → Tm60 Γ nat60 → Tm60 Γ nat60; suc60
 = λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec →
   suc60 (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec)

rec60 : ∀{Γ A} → Tm60 Γ nat60 → Tm60 Γ (arr60 nat60 (arr60 A A)) → Tm60 Γ A → Tm60 Γ A; rec60
 = λ t u v Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec60 →
     rec60 (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec60)
         (u Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec60)
         (v Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec60)

v060 : ∀{Γ A} → Tm60 (snoc60 Γ A) A; v060
 = var60 vz60

v160 : ∀{Γ A B} → Tm60 (snoc60 (snoc60 Γ A) B) A; v160
 = var60 (vs60 vz60)

v260 : ∀{Γ A B C} → Tm60 (snoc60 (snoc60 (snoc60 Γ A) B) C) A; v260
 = var60 (vs60 (vs60 vz60))

v360 : ∀{Γ A B C D} → Tm60 (snoc60 (snoc60 (snoc60 (snoc60 Γ A) B) C) D) A; v360
 = var60 (vs60 (vs60 (vs60 vz60)))

tbool60 : Ty60; tbool60
 = sum60 top60 top60

true60 : ∀{Γ} → Tm60 Γ tbool60; true60
 = left60 tt60

tfalse60 : ∀{Γ} → Tm60 Γ tbool60; tfalse60
 = right60 tt60

ifthenelse60 : ∀{Γ A} → Tm60 Γ (arr60 tbool60 (arr60 A (arr60 A A))); ifthenelse60
 = lam60 (lam60 (lam60 (case60 v260 (lam60 v260) (lam60 v160))))

times460 : ∀{Γ A} → Tm60 Γ (arr60 (arr60 A A) (arr60 A A)); times460
  = lam60 (lam60 (app60 v160 (app60 v160 (app60 v160 (app60 v160 v060)))))

add60 : ∀{Γ} → Tm60 Γ (arr60 nat60 (arr60 nat60 nat60)); add60
 = lam60 (rec60 v060
       (lam60 (lam60 (lam60 (suc60 (app60 v160 v060)))))
       (lam60 v060))

mul60 : ∀{Γ} → Tm60 Γ (arr60 nat60 (arr60 nat60 nat60)); mul60
 = lam60 (rec60 v060
       (lam60 (lam60 (lam60 (app60 (app60 add60 (app60 v160 v060)) v060))))
       (lam60 zero60))

fact60 : ∀{Γ} → Tm60 Γ (arr60 nat60 nat60); fact60
 = lam60 (rec60 v060 (lam60 (lam60 (app60 (app60 mul60 (suc60 v160)) v060)))
        (suc60 zero60))
{-# OPTIONS --type-in-type #-}

Ty61 : Set
Ty61 =
   (Ty61         : Set)
   (nat top bot  : Ty61)
   (arr prod sum : Ty61 → Ty61 → Ty61)
 → Ty61

nat61 : Ty61; nat61 = λ _ nat61 _ _ _ _ _ → nat61
top61 : Ty61; top61 = λ _ _ top61 _ _ _ _ → top61
bot61 : Ty61; bot61 = λ _ _ _ bot61 _ _ _ → bot61

arr61 : Ty61 → Ty61 → Ty61; arr61
 = λ A B Ty61 nat61 top61 bot61 arr61 prod sum →
     arr61 (A Ty61 nat61 top61 bot61 arr61 prod sum) (B Ty61 nat61 top61 bot61 arr61 prod sum)

prod61 : Ty61 → Ty61 → Ty61; prod61
 = λ A B Ty61 nat61 top61 bot61 arr61 prod61 sum →
     prod61 (A Ty61 nat61 top61 bot61 arr61 prod61 sum) (B Ty61 nat61 top61 bot61 arr61 prod61 sum)

sum61 : Ty61 → Ty61 → Ty61; sum61
 = λ A B Ty61 nat61 top61 bot61 arr61 prod61 sum61 →
     sum61 (A Ty61 nat61 top61 bot61 arr61 prod61 sum61) (B Ty61 nat61 top61 bot61 arr61 prod61 sum61)

Con61 : Set; Con61
 = (Con61 : Set)
   (nil  : Con61)
   (snoc : Con61 → Ty61 → Con61)
 → Con61

nil61 : Con61; nil61
 = λ Con61 nil61 snoc → nil61

snoc61 : Con61 → Ty61 → Con61; snoc61
 = λ Γ A Con61 nil61 snoc61 → snoc61 (Γ Con61 nil61 snoc61) A

Var61 : Con61 → Ty61 → Set; Var61
 = λ Γ A →
   (Var61 : Con61 → Ty61 → Set)
   (vz  : ∀{Γ A} → Var61 (snoc61 Γ A) A)
   (vs  : ∀{Γ B A} → Var61 Γ A → Var61 (snoc61 Γ B) A)
 → Var61 Γ A

vz61 : ∀{Γ A} → Var61 (snoc61 Γ A) A; vz61
 = λ Var61 vz61 vs → vz61

vs61 : ∀{Γ B A} → Var61 Γ A → Var61 (snoc61 Γ B) A; vs61
 = λ x Var61 vz61 vs61 → vs61 (x Var61 vz61 vs61)

Tm61 : Con61 → Ty61 → Set; Tm61
 = λ Γ A →
   (Tm61  : Con61 → Ty61 → Set)
   (var   : ∀{Γ A} → Var61 Γ A → Tm61 Γ A)
   (lam   : ∀{Γ A B} → Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B))
   (app   : ∀{Γ A B} → Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B)
   (tt    : ∀{Γ} → Tm61 Γ top61)
   (pair  : ∀{Γ A B} → Tm61 Γ A → Tm61 Γ B → Tm61 Γ (prod61 A B))
   (fst   : ∀{Γ A B} → Tm61 Γ (prod61 A B) → Tm61 Γ A)
   (snd   : ∀{Γ A B} → Tm61 Γ (prod61 A B) → Tm61 Γ B)
   (left  : ∀{Γ A B} → Tm61 Γ A → Tm61 Γ (sum61 A B))
   (right : ∀{Γ A B} → Tm61 Γ B → Tm61 Γ (sum61 A B))
   (case  : ∀{Γ A B C} → Tm61 Γ (sum61 A B) → Tm61 Γ (arr61 A C) → Tm61 Γ (arr61 B C) → Tm61 Γ C)
   (zero  : ∀{Γ} → Tm61 Γ nat61)
   (suc   : ∀{Γ} → Tm61 Γ nat61 → Tm61 Γ nat61)
   (rec   : ∀{Γ A} → Tm61 Γ nat61 → Tm61 Γ (arr61 nat61 (arr61 A A)) → Tm61 Γ A → Tm61 Γ A)
 → Tm61 Γ A

var61 : ∀{Γ A} → Var61 Γ A → Tm61 Γ A; var61
 = λ x Tm61 var61 lam app tt pair fst snd left right case zero suc rec →
     var61 x

lam61 : ∀{Γ A B} → Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B); lam61
 = λ t Tm61 var61 lam61 app tt pair fst snd left right case zero suc rec →
     lam61 (t Tm61 var61 lam61 app tt pair fst snd left right case zero suc rec)

app61 : ∀{Γ A B} → Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B; app61
 = λ t u Tm61 var61 lam61 app61 tt pair fst snd left right case zero suc rec →
     app61 (t Tm61 var61 lam61 app61 tt pair fst snd left right case zero suc rec)
         (u Tm61 var61 lam61 app61 tt pair fst snd left right case zero suc rec)

tt61 : ∀{Γ} → Tm61 Γ top61; tt61
 = λ Tm61 var61 lam61 app61 tt61 pair fst snd left right case zero suc rec → tt61

pair61 : ∀{Γ A B} → Tm61 Γ A → Tm61 Γ B → Tm61 Γ (prod61 A B); pair61
 = λ t u Tm61 var61 lam61 app61 tt61 pair61 fst snd left right case zero suc rec →
     pair61 (t Tm61 var61 lam61 app61 tt61 pair61 fst snd left right case zero suc rec)
          (u Tm61 var61 lam61 app61 tt61 pair61 fst snd left right case zero suc rec)

fst61 : ∀{Γ A B} → Tm61 Γ (prod61 A B) → Tm61 Γ A; fst61
 = λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd left right case zero suc rec →
     fst61 (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd left right case zero suc rec)

snd61 : ∀{Γ A B} → Tm61 Γ (prod61 A B) → Tm61 Γ B; snd61
 = λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left right case zero suc rec →
     snd61 (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left right case zero suc rec)

left61 : ∀{Γ A B} → Tm61 Γ A → Tm61 Γ (sum61 A B); left61
 = λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right case zero suc rec →
     left61 (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right case zero suc rec)

right61 : ∀{Γ A B} → Tm61 Γ B → Tm61 Γ (sum61 A B); right61
 = λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case zero suc rec →
     right61 (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case zero suc rec)

case61 : ∀{Γ A B C} → Tm61 Γ (sum61 A B) → Tm61 Γ (arr61 A C) → Tm61 Γ (arr61 B C) → Tm61 Γ C; case61
 = λ t u v Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero suc rec →
     case61 (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero suc rec)
           (u Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero suc rec)
           (v Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero suc rec)

zero61  : ∀{Γ} → Tm61 Γ nat61; zero61
 = λ Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc rec → zero61

suc61 : ∀{Γ} → Tm61 Γ nat61 → Tm61 Γ nat61; suc61
 = λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec →
   suc61 (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec)

rec61 : ∀{Γ A} → Tm61 Γ nat61 → Tm61 Γ (arr61 nat61 (arr61 A A)) → Tm61 Γ A → Tm61 Γ A; rec61
 = λ t u v Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec61 →
     rec61 (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec61)
         (u Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec61)
         (v Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec61)

v061 : ∀{Γ A} → Tm61 (snoc61 Γ A) A; v061
 = var61 vz61

v161 : ∀{Γ A B} → Tm61 (snoc61 (snoc61 Γ A) B) A; v161
 = var61 (vs61 vz61)

v261 : ∀{Γ A B C} → Tm61 (snoc61 (snoc61 (snoc61 Γ A) B) C) A; v261
 = var61 (vs61 (vs61 vz61))

v361 : ∀{Γ A B C D} → Tm61 (snoc61 (snoc61 (snoc61 (snoc61 Γ A) B) C) D) A; v361
 = var61 (vs61 (vs61 (vs61 vz61)))

tbool61 : Ty61; tbool61
 = sum61 top61 top61

true61 : ∀{Γ} → Tm61 Γ tbool61; true61
 = left61 tt61

tfalse61 : ∀{Γ} → Tm61 Γ tbool61; tfalse61
 = right61 tt61

ifthenelse61 : ∀{Γ A} → Tm61 Γ (arr61 tbool61 (arr61 A (arr61 A A))); ifthenelse61
 = lam61 (lam61 (lam61 (case61 v261 (lam61 v261) (lam61 v161))))

times461 : ∀{Γ A} → Tm61 Γ (arr61 (arr61 A A) (arr61 A A)); times461
  = lam61 (lam61 (app61 v161 (app61 v161 (app61 v161 (app61 v161 v061)))))

add61 : ∀{Γ} → Tm61 Γ (arr61 nat61 (arr61 nat61 nat61)); add61
 = lam61 (rec61 v061
       (lam61 (lam61 (lam61 (suc61 (app61 v161 v061)))))
       (lam61 v061))

mul61 : ∀{Γ} → Tm61 Γ (arr61 nat61 (arr61 nat61 nat61)); mul61
 = lam61 (rec61 v061
       (lam61 (lam61 (lam61 (app61 (app61 add61 (app61 v161 v061)) v061))))
       (lam61 zero61))

fact61 : ∀{Γ} → Tm61 Γ (arr61 nat61 nat61); fact61
 = lam61 (rec61 v061 (lam61 (lam61 (app61 (app61 mul61 (suc61 v161)) v061)))
        (suc61 zero61))
{-# OPTIONS --type-in-type #-}

Ty62 : Set
Ty62 =
   (Ty62         : Set)
   (nat top bot  : Ty62)
   (arr prod sum : Ty62 → Ty62 → Ty62)
 → Ty62

nat62 : Ty62; nat62 = λ _ nat62 _ _ _ _ _ → nat62
top62 : Ty62; top62 = λ _ _ top62 _ _ _ _ → top62
bot62 : Ty62; bot62 = λ _ _ _ bot62 _ _ _ → bot62

arr62 : Ty62 → Ty62 → Ty62; arr62
 = λ A B Ty62 nat62 top62 bot62 arr62 prod sum →
     arr62 (A Ty62 nat62 top62 bot62 arr62 prod sum) (B Ty62 nat62 top62 bot62 arr62 prod sum)

prod62 : Ty62 → Ty62 → Ty62; prod62
 = λ A B Ty62 nat62 top62 bot62 arr62 prod62 sum →
     prod62 (A Ty62 nat62 top62 bot62 arr62 prod62 sum) (B Ty62 nat62 top62 bot62 arr62 prod62 sum)

sum62 : Ty62 → Ty62 → Ty62; sum62
 = λ A B Ty62 nat62 top62 bot62 arr62 prod62 sum62 →
     sum62 (A Ty62 nat62 top62 bot62 arr62 prod62 sum62) (B Ty62 nat62 top62 bot62 arr62 prod62 sum62)

Con62 : Set; Con62
 = (Con62 : Set)
   (nil  : Con62)
   (snoc : Con62 → Ty62 → Con62)
 → Con62

nil62 : Con62; nil62
 = λ Con62 nil62 snoc → nil62

snoc62 : Con62 → Ty62 → Con62; snoc62
 = λ Γ A Con62 nil62 snoc62 → snoc62 (Γ Con62 nil62 snoc62) A

Var62 : Con62 → Ty62 → Set; Var62
 = λ Γ A →
   (Var62 : Con62 → Ty62 → Set)
   (vz  : ∀{Γ A} → Var62 (snoc62 Γ A) A)
   (vs  : ∀{Γ B A} → Var62 Γ A → Var62 (snoc62 Γ B) A)
 → Var62 Γ A

vz62 : ∀{Γ A} → Var62 (snoc62 Γ A) A; vz62
 = λ Var62 vz62 vs → vz62

vs62 : ∀{Γ B A} → Var62 Γ A → Var62 (snoc62 Γ B) A; vs62
 = λ x Var62 vz62 vs62 → vs62 (x Var62 vz62 vs62)

Tm62 : Con62 → Ty62 → Set; Tm62
 = λ Γ A →
   (Tm62  : Con62 → Ty62 → Set)
   (var   : ∀{Γ A} → Var62 Γ A → Tm62 Γ A)
   (lam   : ∀{Γ A B} → Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B))
   (app   : ∀{Γ A B} → Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B)
   (tt    : ∀{Γ} → Tm62 Γ top62)
   (pair  : ∀{Γ A B} → Tm62 Γ A → Tm62 Γ B → Tm62 Γ (prod62 A B))
   (fst   : ∀{Γ A B} → Tm62 Γ (prod62 A B) → Tm62 Γ A)
   (snd   : ∀{Γ A B} → Tm62 Γ (prod62 A B) → Tm62 Γ B)
   (left  : ∀{Γ A B} → Tm62 Γ A → Tm62 Γ (sum62 A B))
   (right : ∀{Γ A B} → Tm62 Γ B → Tm62 Γ (sum62 A B))
   (case  : ∀{Γ A B C} → Tm62 Γ (sum62 A B) → Tm62 Γ (arr62 A C) → Tm62 Γ (arr62 B C) → Tm62 Γ C)
   (zero  : ∀{Γ} → Tm62 Γ nat62)
   (suc   : ∀{Γ} → Tm62 Γ nat62 → Tm62 Γ nat62)
   (rec   : ∀{Γ A} → Tm62 Γ nat62 → Tm62 Γ (arr62 nat62 (arr62 A A)) → Tm62 Γ A → Tm62 Γ A)
 → Tm62 Γ A

var62 : ∀{Γ A} → Var62 Γ A → Tm62 Γ A; var62
 = λ x Tm62 var62 lam app tt pair fst snd left right case zero suc rec →
     var62 x

lam62 : ∀{Γ A B} → Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B); lam62
 = λ t Tm62 var62 lam62 app tt pair fst snd left right case zero suc rec →
     lam62 (t Tm62 var62 lam62 app tt pair fst snd left right case zero suc rec)

app62 : ∀{Γ A B} → Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B; app62
 = λ t u Tm62 var62 lam62 app62 tt pair fst snd left right case zero suc rec →
     app62 (t Tm62 var62 lam62 app62 tt pair fst snd left right case zero suc rec)
         (u Tm62 var62 lam62 app62 tt pair fst snd left right case zero suc rec)

tt62 : ∀{Γ} → Tm62 Γ top62; tt62
 = λ Tm62 var62 lam62 app62 tt62 pair fst snd left right case zero suc rec → tt62

pair62 : ∀{Γ A B} → Tm62 Γ A → Tm62 Γ B → Tm62 Γ (prod62 A B); pair62
 = λ t u Tm62 var62 lam62 app62 tt62 pair62 fst snd left right case zero suc rec →
     pair62 (t Tm62 var62 lam62 app62 tt62 pair62 fst snd left right case zero suc rec)
          (u Tm62 var62 lam62 app62 tt62 pair62 fst snd left right case zero suc rec)

fst62 : ∀{Γ A B} → Tm62 Γ (prod62 A B) → Tm62 Γ A; fst62
 = λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd left right case zero suc rec →
     fst62 (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd left right case zero suc rec)

snd62 : ∀{Γ A B} → Tm62 Γ (prod62 A B) → Tm62 Γ B; snd62
 = λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left right case zero suc rec →
     snd62 (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left right case zero suc rec)

left62 : ∀{Γ A B} → Tm62 Γ A → Tm62 Γ (sum62 A B); left62
 = λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right case zero suc rec →
     left62 (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right case zero suc rec)

right62 : ∀{Γ A B} → Tm62 Γ B → Tm62 Γ (sum62 A B); right62
 = λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case zero suc rec →
     right62 (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case zero suc rec)

case62 : ∀{Γ A B C} → Tm62 Γ (sum62 A B) → Tm62 Γ (arr62 A C) → Tm62 Γ (arr62 B C) → Tm62 Γ C; case62
 = λ t u v Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero suc rec →
     case62 (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero suc rec)
           (u Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero suc rec)
           (v Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero suc rec)

zero62  : ∀{Γ} → Tm62 Γ nat62; zero62
 = λ Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc rec → zero62

suc62 : ∀{Γ} → Tm62 Γ nat62 → Tm62 Γ nat62; suc62
 = λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec →
   suc62 (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec)

rec62 : ∀{Γ A} → Tm62 Γ nat62 → Tm62 Γ (arr62 nat62 (arr62 A A)) → Tm62 Γ A → Tm62 Γ A; rec62
 = λ t u v Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec62 →
     rec62 (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec62)
         (u Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec62)
         (v Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec62)

v062 : ∀{Γ A} → Tm62 (snoc62 Γ A) A; v062
 = var62 vz62

v162 : ∀{Γ A B} → Tm62 (snoc62 (snoc62 Γ A) B) A; v162
 = var62 (vs62 vz62)

v262 : ∀{Γ A B C} → Tm62 (snoc62 (snoc62 (snoc62 Γ A) B) C) A; v262
 = var62 (vs62 (vs62 vz62))

v362 : ∀{Γ A B C D} → Tm62 (snoc62 (snoc62 (snoc62 (snoc62 Γ A) B) C) D) A; v362
 = var62 (vs62 (vs62 (vs62 vz62)))

tbool62 : Ty62; tbool62
 = sum62 top62 top62

true62 : ∀{Γ} → Tm62 Γ tbool62; true62
 = left62 tt62

tfalse62 : ∀{Γ} → Tm62 Γ tbool62; tfalse62
 = right62 tt62

ifthenelse62 : ∀{Γ A} → Tm62 Γ (arr62 tbool62 (arr62 A (arr62 A A))); ifthenelse62
 = lam62 (lam62 (lam62 (case62 v262 (lam62 v262) (lam62 v162))))

times462 : ∀{Γ A} → Tm62 Γ (arr62 (arr62 A A) (arr62 A A)); times462
  = lam62 (lam62 (app62 v162 (app62 v162 (app62 v162 (app62 v162 v062)))))

add62 : ∀{Γ} → Tm62 Γ (arr62 nat62 (arr62 nat62 nat62)); add62
 = lam62 (rec62 v062
       (lam62 (lam62 (lam62 (suc62 (app62 v162 v062)))))
       (lam62 v062))

mul62 : ∀{Γ} → Tm62 Γ (arr62 nat62 (arr62 nat62 nat62)); mul62
 = lam62 (rec62 v062
       (lam62 (lam62 (lam62 (app62 (app62 add62 (app62 v162 v062)) v062))))
       (lam62 zero62))

fact62 : ∀{Γ} → Tm62 Γ (arr62 nat62 nat62); fact62
 = lam62 (rec62 v062 (lam62 (lam62 (app62 (app62 mul62 (suc62 v162)) v062)))
        (suc62 zero62))
{-# OPTIONS --type-in-type #-}

Ty63 : Set
Ty63 =
   (Ty63         : Set)
   (nat top bot  : Ty63)
   (arr prod sum : Ty63 → Ty63 → Ty63)
 → Ty63

nat63 : Ty63; nat63 = λ _ nat63 _ _ _ _ _ → nat63
top63 : Ty63; top63 = λ _ _ top63 _ _ _ _ → top63
bot63 : Ty63; bot63 = λ _ _ _ bot63 _ _ _ → bot63

arr63 : Ty63 → Ty63 → Ty63; arr63
 = λ A B Ty63 nat63 top63 bot63 arr63 prod sum →
     arr63 (A Ty63 nat63 top63 bot63 arr63 prod sum) (B Ty63 nat63 top63 bot63 arr63 prod sum)

prod63 : Ty63 → Ty63 → Ty63; prod63
 = λ A B Ty63 nat63 top63 bot63 arr63 prod63 sum →
     prod63 (A Ty63 nat63 top63 bot63 arr63 prod63 sum) (B Ty63 nat63 top63 bot63 arr63 prod63 sum)

sum63 : Ty63 → Ty63 → Ty63; sum63
 = λ A B Ty63 nat63 top63 bot63 arr63 prod63 sum63 →
     sum63 (A Ty63 nat63 top63 bot63 arr63 prod63 sum63) (B Ty63 nat63 top63 bot63 arr63 prod63 sum63)

Con63 : Set; Con63
 = (Con63 : Set)
   (nil  : Con63)
   (snoc : Con63 → Ty63 → Con63)
 → Con63

nil63 : Con63; nil63
 = λ Con63 nil63 snoc → nil63

snoc63 : Con63 → Ty63 → Con63; snoc63
 = λ Γ A Con63 nil63 snoc63 → snoc63 (Γ Con63 nil63 snoc63) A

Var63 : Con63 → Ty63 → Set; Var63
 = λ Γ A →
   (Var63 : Con63 → Ty63 → Set)
   (vz  : ∀{Γ A} → Var63 (snoc63 Γ A) A)
   (vs  : ∀{Γ B A} → Var63 Γ A → Var63 (snoc63 Γ B) A)
 → Var63 Γ A

vz63 : ∀{Γ A} → Var63 (snoc63 Γ A) A; vz63
 = λ Var63 vz63 vs → vz63

vs63 : ∀{Γ B A} → Var63 Γ A → Var63 (snoc63 Γ B) A; vs63
 = λ x Var63 vz63 vs63 → vs63 (x Var63 vz63 vs63)

Tm63 : Con63 → Ty63 → Set; Tm63
 = λ Γ A →
   (Tm63  : Con63 → Ty63 → Set)
   (var   : ∀{Γ A} → Var63 Γ A → Tm63 Γ A)
   (lam   : ∀{Γ A B} → Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B))
   (app   : ∀{Γ A B} → Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B)
   (tt    : ∀{Γ} → Tm63 Γ top63)
   (pair  : ∀{Γ A B} → Tm63 Γ A → Tm63 Γ B → Tm63 Γ (prod63 A B))
   (fst   : ∀{Γ A B} → Tm63 Γ (prod63 A B) → Tm63 Γ A)
   (snd   : ∀{Γ A B} → Tm63 Γ (prod63 A B) → Tm63 Γ B)
   (left  : ∀{Γ A B} → Tm63 Γ A → Tm63 Γ (sum63 A B))
   (right : ∀{Γ A B} → Tm63 Γ B → Tm63 Γ (sum63 A B))
   (case  : ∀{Γ A B C} → Tm63 Γ (sum63 A B) → Tm63 Γ (arr63 A C) → Tm63 Γ (arr63 B C) → Tm63 Γ C)
   (zero  : ∀{Γ} → Tm63 Γ nat63)
   (suc   : ∀{Γ} → Tm63 Γ nat63 → Tm63 Γ nat63)
   (rec   : ∀{Γ A} → Tm63 Γ nat63 → Tm63 Γ (arr63 nat63 (arr63 A A)) → Tm63 Γ A → Tm63 Γ A)
 → Tm63 Γ A

var63 : ∀{Γ A} → Var63 Γ A → Tm63 Γ A; var63
 = λ x Tm63 var63 lam app tt pair fst snd left right case zero suc rec →
     var63 x

lam63 : ∀{Γ A B} → Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B); lam63
 = λ t Tm63 var63 lam63 app tt pair fst snd left right case zero suc rec →
     lam63 (t Tm63 var63 lam63 app tt pair fst snd left right case zero suc rec)

app63 : ∀{Γ A B} → Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B; app63
 = λ t u Tm63 var63 lam63 app63 tt pair fst snd left right case zero suc rec →
     app63 (t Tm63 var63 lam63 app63 tt pair fst snd left right case zero suc rec)
         (u Tm63 var63 lam63 app63 tt pair fst snd left right case zero suc rec)

tt63 : ∀{Γ} → Tm63 Γ top63; tt63
 = λ Tm63 var63 lam63 app63 tt63 pair fst snd left right case zero suc rec → tt63

pair63 : ∀{Γ A B} → Tm63 Γ A → Tm63 Γ B → Tm63 Γ (prod63 A B); pair63
 = λ t u Tm63 var63 lam63 app63 tt63 pair63 fst snd left right case zero suc rec →
     pair63 (t Tm63 var63 lam63 app63 tt63 pair63 fst snd left right case zero suc rec)
          (u Tm63 var63 lam63 app63 tt63 pair63 fst snd left right case zero suc rec)

fst63 : ∀{Γ A B} → Tm63 Γ (prod63 A B) → Tm63 Γ A; fst63
 = λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd left right case zero suc rec →
     fst63 (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd left right case zero suc rec)

snd63 : ∀{Γ A B} → Tm63 Γ (prod63 A B) → Tm63 Γ B; snd63
 = λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left right case zero suc rec →
     snd63 (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left right case zero suc rec)

left63 : ∀{Γ A B} → Tm63 Γ A → Tm63 Γ (sum63 A B); left63
 = λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right case zero suc rec →
     left63 (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right case zero suc rec)

right63 : ∀{Γ A B} → Tm63 Γ B → Tm63 Γ (sum63 A B); right63
 = λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case zero suc rec →
     right63 (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case zero suc rec)

case63 : ∀{Γ A B C} → Tm63 Γ (sum63 A B) → Tm63 Γ (arr63 A C) → Tm63 Γ (arr63 B C) → Tm63 Γ C; case63
 = λ t u v Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero suc rec →
     case63 (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero suc rec)
           (u Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero suc rec)
           (v Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero suc rec)

zero63  : ∀{Γ} → Tm63 Γ nat63; zero63
 = λ Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc rec → zero63

suc63 : ∀{Γ} → Tm63 Γ nat63 → Tm63 Γ nat63; suc63
 = λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec →
   suc63 (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec)

rec63 : ∀{Γ A} → Tm63 Γ nat63 → Tm63 Γ (arr63 nat63 (arr63 A A)) → Tm63 Γ A → Tm63 Γ A; rec63
 = λ t u v Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec63 →
     rec63 (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec63)
         (u Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec63)
         (v Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec63)

v063 : ∀{Γ A} → Tm63 (snoc63 Γ A) A; v063
 = var63 vz63

v163 : ∀{Γ A B} → Tm63 (snoc63 (snoc63 Γ A) B) A; v163
 = var63 (vs63 vz63)

v263 : ∀{Γ A B C} → Tm63 (snoc63 (snoc63 (snoc63 Γ A) B) C) A; v263
 = var63 (vs63 (vs63 vz63))

v363 : ∀{Γ A B C D} → Tm63 (snoc63 (snoc63 (snoc63 (snoc63 Γ A) B) C) D) A; v363
 = var63 (vs63 (vs63 (vs63 vz63)))

tbool63 : Ty63; tbool63
 = sum63 top63 top63

true63 : ∀{Γ} → Tm63 Γ tbool63; true63
 = left63 tt63

tfalse63 : ∀{Γ} → Tm63 Γ tbool63; tfalse63
 = right63 tt63

ifthenelse63 : ∀{Γ A} → Tm63 Γ (arr63 tbool63 (arr63 A (arr63 A A))); ifthenelse63
 = lam63 (lam63 (lam63 (case63 v263 (lam63 v263) (lam63 v163))))

times463 : ∀{Γ A} → Tm63 Γ (arr63 (arr63 A A) (arr63 A A)); times463
  = lam63 (lam63 (app63 v163 (app63 v163 (app63 v163 (app63 v163 v063)))))

add63 : ∀{Γ} → Tm63 Γ (arr63 nat63 (arr63 nat63 nat63)); add63
 = lam63 (rec63 v063
       (lam63 (lam63 (lam63 (suc63 (app63 v163 v063)))))
       (lam63 v063))

mul63 : ∀{Γ} → Tm63 Γ (arr63 nat63 (arr63 nat63 nat63)); mul63
 = lam63 (rec63 v063
       (lam63 (lam63 (lam63 (app63 (app63 add63 (app63 v163 v063)) v063))))
       (lam63 zero63))

fact63 : ∀{Γ} → Tm63 Γ (arr63 nat63 nat63); fact63
 = lam63 (rec63 v063 (lam63 (lam63 (app63 (app63 mul63 (suc63 v163)) v063)))
        (suc63 zero63))
{-# OPTIONS --type-in-type #-}

Ty64 : Set
Ty64 =
   (Ty64         : Set)
   (nat top bot  : Ty64)
   (arr prod sum : Ty64 → Ty64 → Ty64)
 → Ty64

nat64 : Ty64; nat64 = λ _ nat64 _ _ _ _ _ → nat64
top64 : Ty64; top64 = λ _ _ top64 _ _ _ _ → top64
bot64 : Ty64; bot64 = λ _ _ _ bot64 _ _ _ → bot64

arr64 : Ty64 → Ty64 → Ty64; arr64
 = λ A B Ty64 nat64 top64 bot64 arr64 prod sum →
     arr64 (A Ty64 nat64 top64 bot64 arr64 prod sum) (B Ty64 nat64 top64 bot64 arr64 prod sum)

prod64 : Ty64 → Ty64 → Ty64; prod64
 = λ A B Ty64 nat64 top64 bot64 arr64 prod64 sum →
     prod64 (A Ty64 nat64 top64 bot64 arr64 prod64 sum) (B Ty64 nat64 top64 bot64 arr64 prod64 sum)

sum64 : Ty64 → Ty64 → Ty64; sum64
 = λ A B Ty64 nat64 top64 bot64 arr64 prod64 sum64 →
     sum64 (A Ty64 nat64 top64 bot64 arr64 prod64 sum64) (B Ty64 nat64 top64 bot64 arr64 prod64 sum64)

Con64 : Set; Con64
 = (Con64 : Set)
   (nil  : Con64)
   (snoc : Con64 → Ty64 → Con64)
 → Con64

nil64 : Con64; nil64
 = λ Con64 nil64 snoc → nil64

snoc64 : Con64 → Ty64 → Con64; snoc64
 = λ Γ A Con64 nil64 snoc64 → snoc64 (Γ Con64 nil64 snoc64) A

Var64 : Con64 → Ty64 → Set; Var64
 = λ Γ A →
   (Var64 : Con64 → Ty64 → Set)
   (vz  : ∀{Γ A} → Var64 (snoc64 Γ A) A)
   (vs  : ∀{Γ B A} → Var64 Γ A → Var64 (snoc64 Γ B) A)
 → Var64 Γ A

vz64 : ∀{Γ A} → Var64 (snoc64 Γ A) A; vz64
 = λ Var64 vz64 vs → vz64

vs64 : ∀{Γ B A} → Var64 Γ A → Var64 (snoc64 Γ B) A; vs64
 = λ x Var64 vz64 vs64 → vs64 (x Var64 vz64 vs64)

Tm64 : Con64 → Ty64 → Set; Tm64
 = λ Γ A →
   (Tm64  : Con64 → Ty64 → Set)
   (var   : ∀{Γ A} → Var64 Γ A → Tm64 Γ A)
   (lam   : ∀{Γ A B} → Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B))
   (app   : ∀{Γ A B} → Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B)
   (tt    : ∀{Γ} → Tm64 Γ top64)
   (pair  : ∀{Γ A B} → Tm64 Γ A → Tm64 Γ B → Tm64 Γ (prod64 A B))
   (fst   : ∀{Γ A B} → Tm64 Γ (prod64 A B) → Tm64 Γ A)
   (snd   : ∀{Γ A B} → Tm64 Γ (prod64 A B) → Tm64 Γ B)
   (left  : ∀{Γ A B} → Tm64 Γ A → Tm64 Γ (sum64 A B))
   (right : ∀{Γ A B} → Tm64 Γ B → Tm64 Γ (sum64 A B))
   (case  : ∀{Γ A B C} → Tm64 Γ (sum64 A B) → Tm64 Γ (arr64 A C) → Tm64 Γ (arr64 B C) → Tm64 Γ C)
   (zero  : ∀{Γ} → Tm64 Γ nat64)
   (suc   : ∀{Γ} → Tm64 Γ nat64 → Tm64 Γ nat64)
   (rec   : ∀{Γ A} → Tm64 Γ nat64 → Tm64 Γ (arr64 nat64 (arr64 A A)) → Tm64 Γ A → Tm64 Γ A)
 → Tm64 Γ A

var64 : ∀{Γ A} → Var64 Γ A → Tm64 Γ A; var64
 = λ x Tm64 var64 lam app tt pair fst snd left right case zero suc rec →
     var64 x

lam64 : ∀{Γ A B} → Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B); lam64
 = λ t Tm64 var64 lam64 app tt pair fst snd left right case zero suc rec →
     lam64 (t Tm64 var64 lam64 app tt pair fst snd left right case zero suc rec)

app64 : ∀{Γ A B} → Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B; app64
 = λ t u Tm64 var64 lam64 app64 tt pair fst snd left right case zero suc rec →
     app64 (t Tm64 var64 lam64 app64 tt pair fst snd left right case zero suc rec)
         (u Tm64 var64 lam64 app64 tt pair fst snd left right case zero suc rec)

tt64 : ∀{Γ} → Tm64 Γ top64; tt64
 = λ Tm64 var64 lam64 app64 tt64 pair fst snd left right case zero suc rec → tt64

pair64 : ∀{Γ A B} → Tm64 Γ A → Tm64 Γ B → Tm64 Γ (prod64 A B); pair64
 = λ t u Tm64 var64 lam64 app64 tt64 pair64 fst snd left right case zero suc rec →
     pair64 (t Tm64 var64 lam64 app64 tt64 pair64 fst snd left right case zero suc rec)
          (u Tm64 var64 lam64 app64 tt64 pair64 fst snd left right case zero suc rec)

fst64 : ∀{Γ A B} → Tm64 Γ (prod64 A B) → Tm64 Γ A; fst64
 = λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd left right case zero suc rec →
     fst64 (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd left right case zero suc rec)

snd64 : ∀{Γ A B} → Tm64 Γ (prod64 A B) → Tm64 Γ B; snd64
 = λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left right case zero suc rec →
     snd64 (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left right case zero suc rec)

left64 : ∀{Γ A B} → Tm64 Γ A → Tm64 Γ (sum64 A B); left64
 = λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right case zero suc rec →
     left64 (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right case zero suc rec)

right64 : ∀{Γ A B} → Tm64 Γ B → Tm64 Γ (sum64 A B); right64
 = λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case zero suc rec →
     right64 (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case zero suc rec)

case64 : ∀{Γ A B C} → Tm64 Γ (sum64 A B) → Tm64 Γ (arr64 A C) → Tm64 Γ (arr64 B C) → Tm64 Γ C; case64
 = λ t u v Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero suc rec →
     case64 (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero suc rec)
           (u Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero suc rec)
           (v Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero suc rec)

zero64  : ∀{Γ} → Tm64 Γ nat64; zero64
 = λ Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc rec → zero64

suc64 : ∀{Γ} → Tm64 Γ nat64 → Tm64 Γ nat64; suc64
 = λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec →
   suc64 (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec)

rec64 : ∀{Γ A} → Tm64 Γ nat64 → Tm64 Γ (arr64 nat64 (arr64 A A)) → Tm64 Γ A → Tm64 Γ A; rec64
 = λ t u v Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec64 →
     rec64 (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec64)
         (u Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec64)
         (v Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec64)

v064 : ∀{Γ A} → Tm64 (snoc64 Γ A) A; v064
 = var64 vz64

v164 : ∀{Γ A B} → Tm64 (snoc64 (snoc64 Γ A) B) A; v164
 = var64 (vs64 vz64)

v264 : ∀{Γ A B C} → Tm64 (snoc64 (snoc64 (snoc64 Γ A) B) C) A; v264
 = var64 (vs64 (vs64 vz64))

v364 : ∀{Γ A B C D} → Tm64 (snoc64 (snoc64 (snoc64 (snoc64 Γ A) B) C) D) A; v364
 = var64 (vs64 (vs64 (vs64 vz64)))

tbool64 : Ty64; tbool64
 = sum64 top64 top64

true64 : ∀{Γ} → Tm64 Γ tbool64; true64
 = left64 tt64

tfalse64 : ∀{Γ} → Tm64 Γ tbool64; tfalse64
 = right64 tt64

ifthenelse64 : ∀{Γ A} → Tm64 Γ (arr64 tbool64 (arr64 A (arr64 A A))); ifthenelse64
 = lam64 (lam64 (lam64 (case64 v264 (lam64 v264) (lam64 v164))))

times464 : ∀{Γ A} → Tm64 Γ (arr64 (arr64 A A) (arr64 A A)); times464
  = lam64 (lam64 (app64 v164 (app64 v164 (app64 v164 (app64 v164 v064)))))

add64 : ∀{Γ} → Tm64 Γ (arr64 nat64 (arr64 nat64 nat64)); add64
 = lam64 (rec64 v064
       (lam64 (lam64 (lam64 (suc64 (app64 v164 v064)))))
       (lam64 v064))

mul64 : ∀{Γ} → Tm64 Γ (arr64 nat64 (arr64 nat64 nat64)); mul64
 = lam64 (rec64 v064
       (lam64 (lam64 (lam64 (app64 (app64 add64 (app64 v164 v064)) v064))))
       (lam64 zero64))

fact64 : ∀{Γ} → Tm64 Γ (arr64 nat64 nat64); fact64
 = lam64 (rec64 v064 (lam64 (lam64 (app64 (app64 mul64 (suc64 v164)) v064)))
        (suc64 zero64))
{-# OPTIONS --type-in-type #-}

Ty65 : Set
Ty65 =
   (Ty65         : Set)
   (nat top bot  : Ty65)
   (arr prod sum : Ty65 → Ty65 → Ty65)
 → Ty65

nat65 : Ty65; nat65 = λ _ nat65 _ _ _ _ _ → nat65
top65 : Ty65; top65 = λ _ _ top65 _ _ _ _ → top65
bot65 : Ty65; bot65 = λ _ _ _ bot65 _ _ _ → bot65

arr65 : Ty65 → Ty65 → Ty65; arr65
 = λ A B Ty65 nat65 top65 bot65 arr65 prod sum →
     arr65 (A Ty65 nat65 top65 bot65 arr65 prod sum) (B Ty65 nat65 top65 bot65 arr65 prod sum)

prod65 : Ty65 → Ty65 → Ty65; prod65
 = λ A B Ty65 nat65 top65 bot65 arr65 prod65 sum →
     prod65 (A Ty65 nat65 top65 bot65 arr65 prod65 sum) (B Ty65 nat65 top65 bot65 arr65 prod65 sum)

sum65 : Ty65 → Ty65 → Ty65; sum65
 = λ A B Ty65 nat65 top65 bot65 arr65 prod65 sum65 →
     sum65 (A Ty65 nat65 top65 bot65 arr65 prod65 sum65) (B Ty65 nat65 top65 bot65 arr65 prod65 sum65)

Con65 : Set; Con65
 = (Con65 : Set)
   (nil  : Con65)
   (snoc : Con65 → Ty65 → Con65)
 → Con65

nil65 : Con65; nil65
 = λ Con65 nil65 snoc → nil65

snoc65 : Con65 → Ty65 → Con65; snoc65
 = λ Γ A Con65 nil65 snoc65 → snoc65 (Γ Con65 nil65 snoc65) A

Var65 : Con65 → Ty65 → Set; Var65
 = λ Γ A →
   (Var65 : Con65 → Ty65 → Set)
   (vz  : ∀{Γ A} → Var65 (snoc65 Γ A) A)
   (vs  : ∀{Γ B A} → Var65 Γ A → Var65 (snoc65 Γ B) A)
 → Var65 Γ A

vz65 : ∀{Γ A} → Var65 (snoc65 Γ A) A; vz65
 = λ Var65 vz65 vs → vz65

vs65 : ∀{Γ B A} → Var65 Γ A → Var65 (snoc65 Γ B) A; vs65
 = λ x Var65 vz65 vs65 → vs65 (x Var65 vz65 vs65)

Tm65 : Con65 → Ty65 → Set; Tm65
 = λ Γ A →
   (Tm65  : Con65 → Ty65 → Set)
   (var   : ∀{Γ A} → Var65 Γ A → Tm65 Γ A)
   (lam   : ∀{Γ A B} → Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B))
   (app   : ∀{Γ A B} → Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B)
   (tt    : ∀{Γ} → Tm65 Γ top65)
   (pair  : ∀{Γ A B} → Tm65 Γ A → Tm65 Γ B → Tm65 Γ (prod65 A B))
   (fst   : ∀{Γ A B} → Tm65 Γ (prod65 A B) → Tm65 Γ A)
   (snd   : ∀{Γ A B} → Tm65 Γ (prod65 A B) → Tm65 Γ B)
   (left  : ∀{Γ A B} → Tm65 Γ A → Tm65 Γ (sum65 A B))
   (right : ∀{Γ A B} → Tm65 Γ B → Tm65 Γ (sum65 A B))
   (case  : ∀{Γ A B C} → Tm65 Γ (sum65 A B) → Tm65 Γ (arr65 A C) → Tm65 Γ (arr65 B C) → Tm65 Γ C)
   (zero  : ∀{Γ} → Tm65 Γ nat65)
   (suc   : ∀{Γ} → Tm65 Γ nat65 → Tm65 Γ nat65)
   (rec   : ∀{Γ A} → Tm65 Γ nat65 → Tm65 Γ (arr65 nat65 (arr65 A A)) → Tm65 Γ A → Tm65 Γ A)
 → Tm65 Γ A

var65 : ∀{Γ A} → Var65 Γ A → Tm65 Γ A; var65
 = λ x Tm65 var65 lam app tt pair fst snd left right case zero suc rec →
     var65 x

lam65 : ∀{Γ A B} → Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B); lam65
 = λ t Tm65 var65 lam65 app tt pair fst snd left right case zero suc rec →
     lam65 (t Tm65 var65 lam65 app tt pair fst snd left right case zero suc rec)

app65 : ∀{Γ A B} → Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B; app65
 = λ t u Tm65 var65 lam65 app65 tt pair fst snd left right case zero suc rec →
     app65 (t Tm65 var65 lam65 app65 tt pair fst snd left right case zero suc rec)
         (u Tm65 var65 lam65 app65 tt pair fst snd left right case zero suc rec)

tt65 : ∀{Γ} → Tm65 Γ top65; tt65
 = λ Tm65 var65 lam65 app65 tt65 pair fst snd left right case zero suc rec → tt65

pair65 : ∀{Γ A B} → Tm65 Γ A → Tm65 Γ B → Tm65 Γ (prod65 A B); pair65
 = λ t u Tm65 var65 lam65 app65 tt65 pair65 fst snd left right case zero suc rec →
     pair65 (t Tm65 var65 lam65 app65 tt65 pair65 fst snd left right case zero suc rec)
          (u Tm65 var65 lam65 app65 tt65 pair65 fst snd left right case zero suc rec)

fst65 : ∀{Γ A B} → Tm65 Γ (prod65 A B) → Tm65 Γ A; fst65
 = λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd left right case zero suc rec →
     fst65 (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd left right case zero suc rec)

snd65 : ∀{Γ A B} → Tm65 Γ (prod65 A B) → Tm65 Γ B; snd65
 = λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left right case zero suc rec →
     snd65 (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left right case zero suc rec)

left65 : ∀{Γ A B} → Tm65 Γ A → Tm65 Γ (sum65 A B); left65
 = λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right case zero suc rec →
     left65 (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right case zero suc rec)

right65 : ∀{Γ A B} → Tm65 Γ B → Tm65 Γ (sum65 A B); right65
 = λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case zero suc rec →
     right65 (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case zero suc rec)

case65 : ∀{Γ A B C} → Tm65 Γ (sum65 A B) → Tm65 Γ (arr65 A C) → Tm65 Γ (arr65 B C) → Tm65 Γ C; case65
 = λ t u v Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero suc rec →
     case65 (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero suc rec)
           (u Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero suc rec)
           (v Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero suc rec)

zero65  : ∀{Γ} → Tm65 Γ nat65; zero65
 = λ Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc rec → zero65

suc65 : ∀{Γ} → Tm65 Γ nat65 → Tm65 Γ nat65; suc65
 = λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec →
   suc65 (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec)

rec65 : ∀{Γ A} → Tm65 Γ nat65 → Tm65 Γ (arr65 nat65 (arr65 A A)) → Tm65 Γ A → Tm65 Γ A; rec65
 = λ t u v Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec65 →
     rec65 (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec65)
         (u Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec65)
         (v Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec65)

v065 : ∀{Γ A} → Tm65 (snoc65 Γ A) A; v065
 = var65 vz65

v165 : ∀{Γ A B} → Tm65 (snoc65 (snoc65 Γ A) B) A; v165
 = var65 (vs65 vz65)

v265 : ∀{Γ A B C} → Tm65 (snoc65 (snoc65 (snoc65 Γ A) B) C) A; v265
 = var65 (vs65 (vs65 vz65))

v365 : ∀{Γ A B C D} → Tm65 (snoc65 (snoc65 (snoc65 (snoc65 Γ A) B) C) D) A; v365
 = var65 (vs65 (vs65 (vs65 vz65)))

tbool65 : Ty65; tbool65
 = sum65 top65 top65

true65 : ∀{Γ} → Tm65 Γ tbool65; true65
 = left65 tt65

tfalse65 : ∀{Γ} → Tm65 Γ tbool65; tfalse65
 = right65 tt65

ifthenelse65 : ∀{Γ A} → Tm65 Γ (arr65 tbool65 (arr65 A (arr65 A A))); ifthenelse65
 = lam65 (lam65 (lam65 (case65 v265 (lam65 v265) (lam65 v165))))

times465 : ∀{Γ A} → Tm65 Γ (arr65 (arr65 A A) (arr65 A A)); times465
  = lam65 (lam65 (app65 v165 (app65 v165 (app65 v165 (app65 v165 v065)))))

add65 : ∀{Γ} → Tm65 Γ (arr65 nat65 (arr65 nat65 nat65)); add65
 = lam65 (rec65 v065
       (lam65 (lam65 (lam65 (suc65 (app65 v165 v065)))))
       (lam65 v065))

mul65 : ∀{Γ} → Tm65 Γ (arr65 nat65 (arr65 nat65 nat65)); mul65
 = lam65 (rec65 v065
       (lam65 (lam65 (lam65 (app65 (app65 add65 (app65 v165 v065)) v065))))
       (lam65 zero65))

fact65 : ∀{Γ} → Tm65 Γ (arr65 nat65 nat65); fact65
 = lam65 (rec65 v065 (lam65 (lam65 (app65 (app65 mul65 (suc65 v165)) v065)))
        (suc65 zero65))
{-# OPTIONS --type-in-type #-}

Ty66 : Set
Ty66 =
   (Ty66         : Set)
   (nat top bot  : Ty66)
   (arr prod sum : Ty66 → Ty66 → Ty66)
 → Ty66

nat66 : Ty66; nat66 = λ _ nat66 _ _ _ _ _ → nat66
top66 : Ty66; top66 = λ _ _ top66 _ _ _ _ → top66
bot66 : Ty66; bot66 = λ _ _ _ bot66 _ _ _ → bot66

arr66 : Ty66 → Ty66 → Ty66; arr66
 = λ A B Ty66 nat66 top66 bot66 arr66 prod sum →
     arr66 (A Ty66 nat66 top66 bot66 arr66 prod sum) (B Ty66 nat66 top66 bot66 arr66 prod sum)

prod66 : Ty66 → Ty66 → Ty66; prod66
 = λ A B Ty66 nat66 top66 bot66 arr66 prod66 sum →
     prod66 (A Ty66 nat66 top66 bot66 arr66 prod66 sum) (B Ty66 nat66 top66 bot66 arr66 prod66 sum)

sum66 : Ty66 → Ty66 → Ty66; sum66
 = λ A B Ty66 nat66 top66 bot66 arr66 prod66 sum66 →
     sum66 (A Ty66 nat66 top66 bot66 arr66 prod66 sum66) (B Ty66 nat66 top66 bot66 arr66 prod66 sum66)

Con66 : Set; Con66
 = (Con66 : Set)
   (nil  : Con66)
   (snoc : Con66 → Ty66 → Con66)
 → Con66

nil66 : Con66; nil66
 = λ Con66 nil66 snoc → nil66

snoc66 : Con66 → Ty66 → Con66; snoc66
 = λ Γ A Con66 nil66 snoc66 → snoc66 (Γ Con66 nil66 snoc66) A

Var66 : Con66 → Ty66 → Set; Var66
 = λ Γ A →
   (Var66 : Con66 → Ty66 → Set)
   (vz  : ∀{Γ A} → Var66 (snoc66 Γ A) A)
   (vs  : ∀{Γ B A} → Var66 Γ A → Var66 (snoc66 Γ B) A)
 → Var66 Γ A

vz66 : ∀{Γ A} → Var66 (snoc66 Γ A) A; vz66
 = λ Var66 vz66 vs → vz66

vs66 : ∀{Γ B A} → Var66 Γ A → Var66 (snoc66 Γ B) A; vs66
 = λ x Var66 vz66 vs66 → vs66 (x Var66 vz66 vs66)

Tm66 : Con66 → Ty66 → Set; Tm66
 = λ Γ A →
   (Tm66  : Con66 → Ty66 → Set)
   (var   : ∀{Γ A} → Var66 Γ A → Tm66 Γ A)
   (lam   : ∀{Γ A B} → Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B))
   (app   : ∀{Γ A B} → Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B)
   (tt    : ∀{Γ} → Tm66 Γ top66)
   (pair  : ∀{Γ A B} → Tm66 Γ A → Tm66 Γ B → Tm66 Γ (prod66 A B))
   (fst   : ∀{Γ A B} → Tm66 Γ (prod66 A B) → Tm66 Γ A)
   (snd   : ∀{Γ A B} → Tm66 Γ (prod66 A B) → Tm66 Γ B)
   (left  : ∀{Γ A B} → Tm66 Γ A → Tm66 Γ (sum66 A B))
   (right : ∀{Γ A B} → Tm66 Γ B → Tm66 Γ (sum66 A B))
   (case  : ∀{Γ A B C} → Tm66 Γ (sum66 A B) → Tm66 Γ (arr66 A C) → Tm66 Γ (arr66 B C) → Tm66 Γ C)
   (zero  : ∀{Γ} → Tm66 Γ nat66)
   (suc   : ∀{Γ} → Tm66 Γ nat66 → Tm66 Γ nat66)
   (rec   : ∀{Γ A} → Tm66 Γ nat66 → Tm66 Γ (arr66 nat66 (arr66 A A)) → Tm66 Γ A → Tm66 Γ A)
 → Tm66 Γ A

var66 : ∀{Γ A} → Var66 Γ A → Tm66 Γ A; var66
 = λ x Tm66 var66 lam app tt pair fst snd left right case zero suc rec →
     var66 x

lam66 : ∀{Γ A B} → Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B); lam66
 = λ t Tm66 var66 lam66 app tt pair fst snd left right case zero suc rec →
     lam66 (t Tm66 var66 lam66 app tt pair fst snd left right case zero suc rec)

app66 : ∀{Γ A B} → Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B; app66
 = λ t u Tm66 var66 lam66 app66 tt pair fst snd left right case zero suc rec →
     app66 (t Tm66 var66 lam66 app66 tt pair fst snd left right case zero suc rec)
         (u Tm66 var66 lam66 app66 tt pair fst snd left right case zero suc rec)

tt66 : ∀{Γ} → Tm66 Γ top66; tt66
 = λ Tm66 var66 lam66 app66 tt66 pair fst snd left right case zero suc rec → tt66

pair66 : ∀{Γ A B} → Tm66 Γ A → Tm66 Γ B → Tm66 Γ (prod66 A B); pair66
 = λ t u Tm66 var66 lam66 app66 tt66 pair66 fst snd left right case zero suc rec →
     pair66 (t Tm66 var66 lam66 app66 tt66 pair66 fst snd left right case zero suc rec)
          (u Tm66 var66 lam66 app66 tt66 pair66 fst snd left right case zero suc rec)

fst66 : ∀{Γ A B} → Tm66 Γ (prod66 A B) → Tm66 Γ A; fst66
 = λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd left right case zero suc rec →
     fst66 (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd left right case zero suc rec)

snd66 : ∀{Γ A B} → Tm66 Γ (prod66 A B) → Tm66 Γ B; snd66
 = λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left right case zero suc rec →
     snd66 (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left right case zero suc rec)

left66 : ∀{Γ A B} → Tm66 Γ A → Tm66 Γ (sum66 A B); left66
 = λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right case zero suc rec →
     left66 (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right case zero suc rec)

right66 : ∀{Γ A B} → Tm66 Γ B → Tm66 Γ (sum66 A B); right66
 = λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case zero suc rec →
     right66 (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case zero suc rec)

case66 : ∀{Γ A B C} → Tm66 Γ (sum66 A B) → Tm66 Γ (arr66 A C) → Tm66 Γ (arr66 B C) → Tm66 Γ C; case66
 = λ t u v Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero suc rec →
     case66 (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero suc rec)
           (u Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero suc rec)
           (v Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero suc rec)

zero66  : ∀{Γ} → Tm66 Γ nat66; zero66
 = λ Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc rec → zero66

suc66 : ∀{Γ} → Tm66 Γ nat66 → Tm66 Γ nat66; suc66
 = λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec →
   suc66 (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec)

rec66 : ∀{Γ A} → Tm66 Γ nat66 → Tm66 Γ (arr66 nat66 (arr66 A A)) → Tm66 Γ A → Tm66 Γ A; rec66
 = λ t u v Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec66 →
     rec66 (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec66)
         (u Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec66)
         (v Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec66)

v066 : ∀{Γ A} → Tm66 (snoc66 Γ A) A; v066
 = var66 vz66

v166 : ∀{Γ A B} → Tm66 (snoc66 (snoc66 Γ A) B) A; v166
 = var66 (vs66 vz66)

v266 : ∀{Γ A B C} → Tm66 (snoc66 (snoc66 (snoc66 Γ A) B) C) A; v266
 = var66 (vs66 (vs66 vz66))

v366 : ∀{Γ A B C D} → Tm66 (snoc66 (snoc66 (snoc66 (snoc66 Γ A) B) C) D) A; v366
 = var66 (vs66 (vs66 (vs66 vz66)))

tbool66 : Ty66; tbool66
 = sum66 top66 top66

true66 : ∀{Γ} → Tm66 Γ tbool66; true66
 = left66 tt66

tfalse66 : ∀{Γ} → Tm66 Γ tbool66; tfalse66
 = right66 tt66

ifthenelse66 : ∀{Γ A} → Tm66 Γ (arr66 tbool66 (arr66 A (arr66 A A))); ifthenelse66
 = lam66 (lam66 (lam66 (case66 v266 (lam66 v266) (lam66 v166))))

times466 : ∀{Γ A} → Tm66 Γ (arr66 (arr66 A A) (arr66 A A)); times466
  = lam66 (lam66 (app66 v166 (app66 v166 (app66 v166 (app66 v166 v066)))))

add66 : ∀{Γ} → Tm66 Γ (arr66 nat66 (arr66 nat66 nat66)); add66
 = lam66 (rec66 v066
       (lam66 (lam66 (lam66 (suc66 (app66 v166 v066)))))
       (lam66 v066))

mul66 : ∀{Γ} → Tm66 Γ (arr66 nat66 (arr66 nat66 nat66)); mul66
 = lam66 (rec66 v066
       (lam66 (lam66 (lam66 (app66 (app66 add66 (app66 v166 v066)) v066))))
       (lam66 zero66))

fact66 : ∀{Γ} → Tm66 Γ (arr66 nat66 nat66); fact66
 = lam66 (rec66 v066 (lam66 (lam66 (app66 (app66 mul66 (suc66 v166)) v066)))
        (suc66 zero66))
{-# OPTIONS --type-in-type #-}

Ty67 : Set
Ty67 =
   (Ty67         : Set)
   (nat top bot  : Ty67)
   (arr prod sum : Ty67 → Ty67 → Ty67)
 → Ty67

nat67 : Ty67; nat67 = λ _ nat67 _ _ _ _ _ → nat67
top67 : Ty67; top67 = λ _ _ top67 _ _ _ _ → top67
bot67 : Ty67; bot67 = λ _ _ _ bot67 _ _ _ → bot67

arr67 : Ty67 → Ty67 → Ty67; arr67
 = λ A B Ty67 nat67 top67 bot67 arr67 prod sum →
     arr67 (A Ty67 nat67 top67 bot67 arr67 prod sum) (B Ty67 nat67 top67 bot67 arr67 prod sum)

prod67 : Ty67 → Ty67 → Ty67; prod67
 = λ A B Ty67 nat67 top67 bot67 arr67 prod67 sum →
     prod67 (A Ty67 nat67 top67 bot67 arr67 prod67 sum) (B Ty67 nat67 top67 bot67 arr67 prod67 sum)

sum67 : Ty67 → Ty67 → Ty67; sum67
 = λ A B Ty67 nat67 top67 bot67 arr67 prod67 sum67 →
     sum67 (A Ty67 nat67 top67 bot67 arr67 prod67 sum67) (B Ty67 nat67 top67 bot67 arr67 prod67 sum67)

Con67 : Set; Con67
 = (Con67 : Set)
   (nil  : Con67)
   (snoc : Con67 → Ty67 → Con67)
 → Con67

nil67 : Con67; nil67
 = λ Con67 nil67 snoc → nil67

snoc67 : Con67 → Ty67 → Con67; snoc67
 = λ Γ A Con67 nil67 snoc67 → snoc67 (Γ Con67 nil67 snoc67) A

Var67 : Con67 → Ty67 → Set; Var67
 = λ Γ A →
   (Var67 : Con67 → Ty67 → Set)
   (vz  : ∀{Γ A} → Var67 (snoc67 Γ A) A)
   (vs  : ∀{Γ B A} → Var67 Γ A → Var67 (snoc67 Γ B) A)
 → Var67 Γ A

vz67 : ∀{Γ A} → Var67 (snoc67 Γ A) A; vz67
 = λ Var67 vz67 vs → vz67

vs67 : ∀{Γ B A} → Var67 Γ A → Var67 (snoc67 Γ B) A; vs67
 = λ x Var67 vz67 vs67 → vs67 (x Var67 vz67 vs67)

Tm67 : Con67 → Ty67 → Set; Tm67
 = λ Γ A →
   (Tm67  : Con67 → Ty67 → Set)
   (var   : ∀{Γ A} → Var67 Γ A → Tm67 Γ A)
   (lam   : ∀{Γ A B} → Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B))
   (app   : ∀{Γ A B} → Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B)
   (tt    : ∀{Γ} → Tm67 Γ top67)
   (pair  : ∀{Γ A B} → Tm67 Γ A → Tm67 Γ B → Tm67 Γ (prod67 A B))
   (fst   : ∀{Γ A B} → Tm67 Γ (prod67 A B) → Tm67 Γ A)
   (snd   : ∀{Γ A B} → Tm67 Γ (prod67 A B) → Tm67 Γ B)
   (left  : ∀{Γ A B} → Tm67 Γ A → Tm67 Γ (sum67 A B))
   (right : ∀{Γ A B} → Tm67 Γ B → Tm67 Γ (sum67 A B))
   (case  : ∀{Γ A B C} → Tm67 Γ (sum67 A B) → Tm67 Γ (arr67 A C) → Tm67 Γ (arr67 B C) → Tm67 Γ C)
   (zero  : ∀{Γ} → Tm67 Γ nat67)
   (suc   : ∀{Γ} → Tm67 Γ nat67 → Tm67 Γ nat67)
   (rec   : ∀{Γ A} → Tm67 Γ nat67 → Tm67 Γ (arr67 nat67 (arr67 A A)) → Tm67 Γ A → Tm67 Γ A)
 → Tm67 Γ A

var67 : ∀{Γ A} → Var67 Γ A → Tm67 Γ A; var67
 = λ x Tm67 var67 lam app tt pair fst snd left right case zero suc rec →
     var67 x

lam67 : ∀{Γ A B} → Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B); lam67
 = λ t Tm67 var67 lam67 app tt pair fst snd left right case zero suc rec →
     lam67 (t Tm67 var67 lam67 app tt pair fst snd left right case zero suc rec)

app67 : ∀{Γ A B} → Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B; app67
 = λ t u Tm67 var67 lam67 app67 tt pair fst snd left right case zero suc rec →
     app67 (t Tm67 var67 lam67 app67 tt pair fst snd left right case zero suc rec)
         (u Tm67 var67 lam67 app67 tt pair fst snd left right case zero suc rec)

tt67 : ∀{Γ} → Tm67 Γ top67; tt67
 = λ Tm67 var67 lam67 app67 tt67 pair fst snd left right case zero suc rec → tt67

pair67 : ∀{Γ A B} → Tm67 Γ A → Tm67 Γ B → Tm67 Γ (prod67 A B); pair67
 = λ t u Tm67 var67 lam67 app67 tt67 pair67 fst snd left right case zero suc rec →
     pair67 (t Tm67 var67 lam67 app67 tt67 pair67 fst snd left right case zero suc rec)
          (u Tm67 var67 lam67 app67 tt67 pair67 fst snd left right case zero suc rec)

fst67 : ∀{Γ A B} → Tm67 Γ (prod67 A B) → Tm67 Γ A; fst67
 = λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd left right case zero suc rec →
     fst67 (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd left right case zero suc rec)

snd67 : ∀{Γ A B} → Tm67 Γ (prod67 A B) → Tm67 Γ B; snd67
 = λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left right case zero suc rec →
     snd67 (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left right case zero suc rec)

left67 : ∀{Γ A B} → Tm67 Γ A → Tm67 Γ (sum67 A B); left67
 = λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right case zero suc rec →
     left67 (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right case zero suc rec)

right67 : ∀{Γ A B} → Tm67 Γ B → Tm67 Γ (sum67 A B); right67
 = λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case zero suc rec →
     right67 (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case zero suc rec)

case67 : ∀{Γ A B C} → Tm67 Γ (sum67 A B) → Tm67 Γ (arr67 A C) → Tm67 Γ (arr67 B C) → Tm67 Γ C; case67
 = λ t u v Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero suc rec →
     case67 (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero suc rec)
           (u Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero suc rec)
           (v Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero suc rec)

zero67  : ∀{Γ} → Tm67 Γ nat67; zero67
 = λ Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc rec → zero67

suc67 : ∀{Γ} → Tm67 Γ nat67 → Tm67 Γ nat67; suc67
 = λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec →
   suc67 (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec)

rec67 : ∀{Γ A} → Tm67 Γ nat67 → Tm67 Γ (arr67 nat67 (arr67 A A)) → Tm67 Γ A → Tm67 Γ A; rec67
 = λ t u v Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec67 →
     rec67 (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec67)
         (u Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec67)
         (v Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec67)

v067 : ∀{Γ A} → Tm67 (snoc67 Γ A) A; v067
 = var67 vz67

v167 : ∀{Γ A B} → Tm67 (snoc67 (snoc67 Γ A) B) A; v167
 = var67 (vs67 vz67)

v267 : ∀{Γ A B C} → Tm67 (snoc67 (snoc67 (snoc67 Γ A) B) C) A; v267
 = var67 (vs67 (vs67 vz67))

v367 : ∀{Γ A B C D} → Tm67 (snoc67 (snoc67 (snoc67 (snoc67 Γ A) B) C) D) A; v367
 = var67 (vs67 (vs67 (vs67 vz67)))

tbool67 : Ty67; tbool67
 = sum67 top67 top67

true67 : ∀{Γ} → Tm67 Γ tbool67; true67
 = left67 tt67

tfalse67 : ∀{Γ} → Tm67 Γ tbool67; tfalse67
 = right67 tt67

ifthenelse67 : ∀{Γ A} → Tm67 Γ (arr67 tbool67 (arr67 A (arr67 A A))); ifthenelse67
 = lam67 (lam67 (lam67 (case67 v267 (lam67 v267) (lam67 v167))))

times467 : ∀{Γ A} → Tm67 Γ (arr67 (arr67 A A) (arr67 A A)); times467
  = lam67 (lam67 (app67 v167 (app67 v167 (app67 v167 (app67 v167 v067)))))

add67 : ∀{Γ} → Tm67 Γ (arr67 nat67 (arr67 nat67 nat67)); add67
 = lam67 (rec67 v067
       (lam67 (lam67 (lam67 (suc67 (app67 v167 v067)))))
       (lam67 v067))

mul67 : ∀{Γ} → Tm67 Γ (arr67 nat67 (arr67 nat67 nat67)); mul67
 = lam67 (rec67 v067
       (lam67 (lam67 (lam67 (app67 (app67 add67 (app67 v167 v067)) v067))))
       (lam67 zero67))

fact67 : ∀{Γ} → Tm67 Γ (arr67 nat67 nat67); fact67
 = lam67 (rec67 v067 (lam67 (lam67 (app67 (app67 mul67 (suc67 v167)) v067)))
        (suc67 zero67))
{-# OPTIONS --type-in-type #-}

Ty68 : Set
Ty68 =
   (Ty68         : Set)
   (nat top bot  : Ty68)
   (arr prod sum : Ty68 → Ty68 → Ty68)
 → Ty68

nat68 : Ty68; nat68 = λ _ nat68 _ _ _ _ _ → nat68
top68 : Ty68; top68 = λ _ _ top68 _ _ _ _ → top68
bot68 : Ty68; bot68 = λ _ _ _ bot68 _ _ _ → bot68

arr68 : Ty68 → Ty68 → Ty68; arr68
 = λ A B Ty68 nat68 top68 bot68 arr68 prod sum →
     arr68 (A Ty68 nat68 top68 bot68 arr68 prod sum) (B Ty68 nat68 top68 bot68 arr68 prod sum)

prod68 : Ty68 → Ty68 → Ty68; prod68
 = λ A B Ty68 nat68 top68 bot68 arr68 prod68 sum →
     prod68 (A Ty68 nat68 top68 bot68 arr68 prod68 sum) (B Ty68 nat68 top68 bot68 arr68 prod68 sum)

sum68 : Ty68 → Ty68 → Ty68; sum68
 = λ A B Ty68 nat68 top68 bot68 arr68 prod68 sum68 →
     sum68 (A Ty68 nat68 top68 bot68 arr68 prod68 sum68) (B Ty68 nat68 top68 bot68 arr68 prod68 sum68)

Con68 : Set; Con68
 = (Con68 : Set)
   (nil  : Con68)
   (snoc : Con68 → Ty68 → Con68)
 → Con68

nil68 : Con68; nil68
 = λ Con68 nil68 snoc → nil68

snoc68 : Con68 → Ty68 → Con68; snoc68
 = λ Γ A Con68 nil68 snoc68 → snoc68 (Γ Con68 nil68 snoc68) A

Var68 : Con68 → Ty68 → Set; Var68
 = λ Γ A →
   (Var68 : Con68 → Ty68 → Set)
   (vz  : ∀{Γ A} → Var68 (snoc68 Γ A) A)
   (vs  : ∀{Γ B A} → Var68 Γ A → Var68 (snoc68 Γ B) A)
 → Var68 Γ A

vz68 : ∀{Γ A} → Var68 (snoc68 Γ A) A; vz68
 = λ Var68 vz68 vs → vz68

vs68 : ∀{Γ B A} → Var68 Γ A → Var68 (snoc68 Γ B) A; vs68
 = λ x Var68 vz68 vs68 → vs68 (x Var68 vz68 vs68)

Tm68 : Con68 → Ty68 → Set; Tm68
 = λ Γ A →
   (Tm68  : Con68 → Ty68 → Set)
   (var   : ∀{Γ A} → Var68 Γ A → Tm68 Γ A)
   (lam   : ∀{Γ A B} → Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B))
   (app   : ∀{Γ A B} → Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B)
   (tt    : ∀{Γ} → Tm68 Γ top68)
   (pair  : ∀{Γ A B} → Tm68 Γ A → Tm68 Γ B → Tm68 Γ (prod68 A B))
   (fst   : ∀{Γ A B} → Tm68 Γ (prod68 A B) → Tm68 Γ A)
   (snd   : ∀{Γ A B} → Tm68 Γ (prod68 A B) → Tm68 Γ B)
   (left  : ∀{Γ A B} → Tm68 Γ A → Tm68 Γ (sum68 A B))
   (right : ∀{Γ A B} → Tm68 Γ B → Tm68 Γ (sum68 A B))
   (case  : ∀{Γ A B C} → Tm68 Γ (sum68 A B) → Tm68 Γ (arr68 A C) → Tm68 Γ (arr68 B C) → Tm68 Γ C)
   (zero  : ∀{Γ} → Tm68 Γ nat68)
   (suc   : ∀{Γ} → Tm68 Γ nat68 → Tm68 Γ nat68)
   (rec   : ∀{Γ A} → Tm68 Γ nat68 → Tm68 Γ (arr68 nat68 (arr68 A A)) → Tm68 Γ A → Tm68 Γ A)
 → Tm68 Γ A

var68 : ∀{Γ A} → Var68 Γ A → Tm68 Γ A; var68
 = λ x Tm68 var68 lam app tt pair fst snd left right case zero suc rec →
     var68 x

lam68 : ∀{Γ A B} → Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B); lam68
 = λ t Tm68 var68 lam68 app tt pair fst snd left right case zero suc rec →
     lam68 (t Tm68 var68 lam68 app tt pair fst snd left right case zero suc rec)

app68 : ∀{Γ A B} → Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B; app68
 = λ t u Tm68 var68 lam68 app68 tt pair fst snd left right case zero suc rec →
     app68 (t Tm68 var68 lam68 app68 tt pair fst snd left right case zero suc rec)
         (u Tm68 var68 lam68 app68 tt pair fst snd left right case zero suc rec)

tt68 : ∀{Γ} → Tm68 Γ top68; tt68
 = λ Tm68 var68 lam68 app68 tt68 pair fst snd left right case zero suc rec → tt68

pair68 : ∀{Γ A B} → Tm68 Γ A → Tm68 Γ B → Tm68 Γ (prod68 A B); pair68
 = λ t u Tm68 var68 lam68 app68 tt68 pair68 fst snd left right case zero suc rec →
     pair68 (t Tm68 var68 lam68 app68 tt68 pair68 fst snd left right case zero suc rec)
          (u Tm68 var68 lam68 app68 tt68 pair68 fst snd left right case zero suc rec)

fst68 : ∀{Γ A B} → Tm68 Γ (prod68 A B) → Tm68 Γ A; fst68
 = λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd left right case zero suc rec →
     fst68 (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd left right case zero suc rec)

snd68 : ∀{Γ A B} → Tm68 Γ (prod68 A B) → Tm68 Γ B; snd68
 = λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left right case zero suc rec →
     snd68 (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left right case zero suc rec)

left68 : ∀{Γ A B} → Tm68 Γ A → Tm68 Γ (sum68 A B); left68
 = λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right case zero suc rec →
     left68 (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right case zero suc rec)

right68 : ∀{Γ A B} → Tm68 Γ B → Tm68 Γ (sum68 A B); right68
 = λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case zero suc rec →
     right68 (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case zero suc rec)

case68 : ∀{Γ A B C} → Tm68 Γ (sum68 A B) → Tm68 Γ (arr68 A C) → Tm68 Γ (arr68 B C) → Tm68 Γ C; case68
 = λ t u v Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero suc rec →
     case68 (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero suc rec)
           (u Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero suc rec)
           (v Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero suc rec)

zero68  : ∀{Γ} → Tm68 Γ nat68; zero68
 = λ Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc rec → zero68

suc68 : ∀{Γ} → Tm68 Γ nat68 → Tm68 Γ nat68; suc68
 = λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec →
   suc68 (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec)

rec68 : ∀{Γ A} → Tm68 Γ nat68 → Tm68 Γ (arr68 nat68 (arr68 A A)) → Tm68 Γ A → Tm68 Γ A; rec68
 = λ t u v Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec68 →
     rec68 (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec68)
         (u Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec68)
         (v Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec68)

v068 : ∀{Γ A} → Tm68 (snoc68 Γ A) A; v068
 = var68 vz68

v168 : ∀{Γ A B} → Tm68 (snoc68 (snoc68 Γ A) B) A; v168
 = var68 (vs68 vz68)

v268 : ∀{Γ A B C} → Tm68 (snoc68 (snoc68 (snoc68 Γ A) B) C) A; v268
 = var68 (vs68 (vs68 vz68))

v368 : ∀{Γ A B C D} → Tm68 (snoc68 (snoc68 (snoc68 (snoc68 Γ A) B) C) D) A; v368
 = var68 (vs68 (vs68 (vs68 vz68)))

tbool68 : Ty68; tbool68
 = sum68 top68 top68

true68 : ∀{Γ} → Tm68 Γ tbool68; true68
 = left68 tt68

tfalse68 : ∀{Γ} → Tm68 Γ tbool68; tfalse68
 = right68 tt68

ifthenelse68 : ∀{Γ A} → Tm68 Γ (arr68 tbool68 (arr68 A (arr68 A A))); ifthenelse68
 = lam68 (lam68 (lam68 (case68 v268 (lam68 v268) (lam68 v168))))

times468 : ∀{Γ A} → Tm68 Γ (arr68 (arr68 A A) (arr68 A A)); times468
  = lam68 (lam68 (app68 v168 (app68 v168 (app68 v168 (app68 v168 v068)))))

add68 : ∀{Γ} → Tm68 Γ (arr68 nat68 (arr68 nat68 nat68)); add68
 = lam68 (rec68 v068
       (lam68 (lam68 (lam68 (suc68 (app68 v168 v068)))))
       (lam68 v068))

mul68 : ∀{Γ} → Tm68 Γ (arr68 nat68 (arr68 nat68 nat68)); mul68
 = lam68 (rec68 v068
       (lam68 (lam68 (lam68 (app68 (app68 add68 (app68 v168 v068)) v068))))
       (lam68 zero68))

fact68 : ∀{Γ} → Tm68 Γ (arr68 nat68 nat68); fact68
 = lam68 (rec68 v068 (lam68 (lam68 (app68 (app68 mul68 (suc68 v168)) v068)))
        (suc68 zero68))
{-# OPTIONS --type-in-type #-}

Ty69 : Set
Ty69 =
   (Ty69         : Set)
   (nat top bot  : Ty69)
   (arr prod sum : Ty69 → Ty69 → Ty69)
 → Ty69

nat69 : Ty69; nat69 = λ _ nat69 _ _ _ _ _ → nat69
top69 : Ty69; top69 = λ _ _ top69 _ _ _ _ → top69
bot69 : Ty69; bot69 = λ _ _ _ bot69 _ _ _ → bot69

arr69 : Ty69 → Ty69 → Ty69; arr69
 = λ A B Ty69 nat69 top69 bot69 arr69 prod sum →
     arr69 (A Ty69 nat69 top69 bot69 arr69 prod sum) (B Ty69 nat69 top69 bot69 arr69 prod sum)

prod69 : Ty69 → Ty69 → Ty69; prod69
 = λ A B Ty69 nat69 top69 bot69 arr69 prod69 sum →
     prod69 (A Ty69 nat69 top69 bot69 arr69 prod69 sum) (B Ty69 nat69 top69 bot69 arr69 prod69 sum)

sum69 : Ty69 → Ty69 → Ty69; sum69
 = λ A B Ty69 nat69 top69 bot69 arr69 prod69 sum69 →
     sum69 (A Ty69 nat69 top69 bot69 arr69 prod69 sum69) (B Ty69 nat69 top69 bot69 arr69 prod69 sum69)

Con69 : Set; Con69
 = (Con69 : Set)
   (nil  : Con69)
   (snoc : Con69 → Ty69 → Con69)
 → Con69

nil69 : Con69; nil69
 = λ Con69 nil69 snoc → nil69

snoc69 : Con69 → Ty69 → Con69; snoc69
 = λ Γ A Con69 nil69 snoc69 → snoc69 (Γ Con69 nil69 snoc69) A

Var69 : Con69 → Ty69 → Set; Var69
 = λ Γ A →
   (Var69 : Con69 → Ty69 → Set)
   (vz  : ∀{Γ A} → Var69 (snoc69 Γ A) A)
   (vs  : ∀{Γ B A} → Var69 Γ A → Var69 (snoc69 Γ B) A)
 → Var69 Γ A

vz69 : ∀{Γ A} → Var69 (snoc69 Γ A) A; vz69
 = λ Var69 vz69 vs → vz69

vs69 : ∀{Γ B A} → Var69 Γ A → Var69 (snoc69 Γ B) A; vs69
 = λ x Var69 vz69 vs69 → vs69 (x Var69 vz69 vs69)

Tm69 : Con69 → Ty69 → Set; Tm69
 = λ Γ A →
   (Tm69  : Con69 → Ty69 → Set)
   (var   : ∀{Γ A} → Var69 Γ A → Tm69 Γ A)
   (lam   : ∀{Γ A B} → Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B))
   (app   : ∀{Γ A B} → Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B)
   (tt    : ∀{Γ} → Tm69 Γ top69)
   (pair  : ∀{Γ A B} → Tm69 Γ A → Tm69 Γ B → Tm69 Γ (prod69 A B))
   (fst   : ∀{Γ A B} → Tm69 Γ (prod69 A B) → Tm69 Γ A)
   (snd   : ∀{Γ A B} → Tm69 Γ (prod69 A B) → Tm69 Γ B)
   (left  : ∀{Γ A B} → Tm69 Γ A → Tm69 Γ (sum69 A B))
   (right : ∀{Γ A B} → Tm69 Γ B → Tm69 Γ (sum69 A B))
   (case  : ∀{Γ A B C} → Tm69 Γ (sum69 A B) → Tm69 Γ (arr69 A C) → Tm69 Γ (arr69 B C) → Tm69 Γ C)
   (zero  : ∀{Γ} → Tm69 Γ nat69)
   (suc   : ∀{Γ} → Tm69 Γ nat69 → Tm69 Γ nat69)
   (rec   : ∀{Γ A} → Tm69 Γ nat69 → Tm69 Γ (arr69 nat69 (arr69 A A)) → Tm69 Γ A → Tm69 Γ A)
 → Tm69 Γ A

var69 : ∀{Γ A} → Var69 Γ A → Tm69 Γ A; var69
 = λ x Tm69 var69 lam app tt pair fst snd left right case zero suc rec →
     var69 x

lam69 : ∀{Γ A B} → Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B); lam69
 = λ t Tm69 var69 lam69 app tt pair fst snd left right case zero suc rec →
     lam69 (t Tm69 var69 lam69 app tt pair fst snd left right case zero suc rec)

app69 : ∀{Γ A B} → Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B; app69
 = λ t u Tm69 var69 lam69 app69 tt pair fst snd left right case zero suc rec →
     app69 (t Tm69 var69 lam69 app69 tt pair fst snd left right case zero suc rec)
         (u Tm69 var69 lam69 app69 tt pair fst snd left right case zero suc rec)

tt69 : ∀{Γ} → Tm69 Γ top69; tt69
 = λ Tm69 var69 lam69 app69 tt69 pair fst snd left right case zero suc rec → tt69

pair69 : ∀{Γ A B} → Tm69 Γ A → Tm69 Γ B → Tm69 Γ (prod69 A B); pair69
 = λ t u Tm69 var69 lam69 app69 tt69 pair69 fst snd left right case zero suc rec →
     pair69 (t Tm69 var69 lam69 app69 tt69 pair69 fst snd left right case zero suc rec)
          (u Tm69 var69 lam69 app69 tt69 pair69 fst snd left right case zero suc rec)

fst69 : ∀{Γ A B} → Tm69 Γ (prod69 A B) → Tm69 Γ A; fst69
 = λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd left right case zero suc rec →
     fst69 (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd left right case zero suc rec)

snd69 : ∀{Γ A B} → Tm69 Γ (prod69 A B) → Tm69 Γ B; snd69
 = λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left right case zero suc rec →
     snd69 (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left right case zero suc rec)

left69 : ∀{Γ A B} → Tm69 Γ A → Tm69 Γ (sum69 A B); left69
 = λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right case zero suc rec →
     left69 (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right case zero suc rec)

right69 : ∀{Γ A B} → Tm69 Γ B → Tm69 Γ (sum69 A B); right69
 = λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case zero suc rec →
     right69 (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case zero suc rec)

case69 : ∀{Γ A B C} → Tm69 Γ (sum69 A B) → Tm69 Γ (arr69 A C) → Tm69 Γ (arr69 B C) → Tm69 Γ C; case69
 = λ t u v Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero suc rec →
     case69 (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero suc rec)
           (u Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero suc rec)
           (v Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero suc rec)

zero69  : ∀{Γ} → Tm69 Γ nat69; zero69
 = λ Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc rec → zero69

suc69 : ∀{Γ} → Tm69 Γ nat69 → Tm69 Γ nat69; suc69
 = λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec →
   suc69 (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec)

rec69 : ∀{Γ A} → Tm69 Γ nat69 → Tm69 Γ (arr69 nat69 (arr69 A A)) → Tm69 Γ A → Tm69 Γ A; rec69
 = λ t u v Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec69 →
     rec69 (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec69)
         (u Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec69)
         (v Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec69)

v069 : ∀{Γ A} → Tm69 (snoc69 Γ A) A; v069
 = var69 vz69

v169 : ∀{Γ A B} → Tm69 (snoc69 (snoc69 Γ A) B) A; v169
 = var69 (vs69 vz69)

v269 : ∀{Γ A B C} → Tm69 (snoc69 (snoc69 (snoc69 Γ A) B) C) A; v269
 = var69 (vs69 (vs69 vz69))

v369 : ∀{Γ A B C D} → Tm69 (snoc69 (snoc69 (snoc69 (snoc69 Γ A) B) C) D) A; v369
 = var69 (vs69 (vs69 (vs69 vz69)))

tbool69 : Ty69; tbool69
 = sum69 top69 top69

true69 : ∀{Γ} → Tm69 Γ tbool69; true69
 = left69 tt69

tfalse69 : ∀{Γ} → Tm69 Γ tbool69; tfalse69
 = right69 tt69

ifthenelse69 : ∀{Γ A} → Tm69 Γ (arr69 tbool69 (arr69 A (arr69 A A))); ifthenelse69
 = lam69 (lam69 (lam69 (case69 v269 (lam69 v269) (lam69 v169))))

times469 : ∀{Γ A} → Tm69 Γ (arr69 (arr69 A A) (arr69 A A)); times469
  = lam69 (lam69 (app69 v169 (app69 v169 (app69 v169 (app69 v169 v069)))))

add69 : ∀{Γ} → Tm69 Γ (arr69 nat69 (arr69 nat69 nat69)); add69
 = lam69 (rec69 v069
       (lam69 (lam69 (lam69 (suc69 (app69 v169 v069)))))
       (lam69 v069))

mul69 : ∀{Γ} → Tm69 Γ (arr69 nat69 (arr69 nat69 nat69)); mul69
 = lam69 (rec69 v069
       (lam69 (lam69 (lam69 (app69 (app69 add69 (app69 v169 v069)) v069))))
       (lam69 zero69))

fact69 : ∀{Γ} → Tm69 Γ (arr69 nat69 nat69); fact69
 = lam69 (rec69 v069 (lam69 (lam69 (app69 (app69 mul69 (suc69 v169)) v069)))
        (suc69 zero69))
{-# OPTIONS --type-in-type #-}

Ty70 : Set
Ty70 =
   (Ty70         : Set)
   (nat top bot  : Ty70)
   (arr prod sum : Ty70 → Ty70 → Ty70)
 → Ty70

nat70 : Ty70; nat70 = λ _ nat70 _ _ _ _ _ → nat70
top70 : Ty70; top70 = λ _ _ top70 _ _ _ _ → top70
bot70 : Ty70; bot70 = λ _ _ _ bot70 _ _ _ → bot70

arr70 : Ty70 → Ty70 → Ty70; arr70
 = λ A B Ty70 nat70 top70 bot70 arr70 prod sum →
     arr70 (A Ty70 nat70 top70 bot70 arr70 prod sum) (B Ty70 nat70 top70 bot70 arr70 prod sum)

prod70 : Ty70 → Ty70 → Ty70; prod70
 = λ A B Ty70 nat70 top70 bot70 arr70 prod70 sum →
     prod70 (A Ty70 nat70 top70 bot70 arr70 prod70 sum) (B Ty70 nat70 top70 bot70 arr70 prod70 sum)

sum70 : Ty70 → Ty70 → Ty70; sum70
 = λ A B Ty70 nat70 top70 bot70 arr70 prod70 sum70 →
     sum70 (A Ty70 nat70 top70 bot70 arr70 prod70 sum70) (B Ty70 nat70 top70 bot70 arr70 prod70 sum70)

Con70 : Set; Con70
 = (Con70 : Set)
   (nil  : Con70)
   (snoc : Con70 → Ty70 → Con70)
 → Con70

nil70 : Con70; nil70
 = λ Con70 nil70 snoc → nil70

snoc70 : Con70 → Ty70 → Con70; snoc70
 = λ Γ A Con70 nil70 snoc70 → snoc70 (Γ Con70 nil70 snoc70) A

Var70 : Con70 → Ty70 → Set; Var70
 = λ Γ A →
   (Var70 : Con70 → Ty70 → Set)
   (vz  : ∀{Γ A} → Var70 (snoc70 Γ A) A)
   (vs  : ∀{Γ B A} → Var70 Γ A → Var70 (snoc70 Γ B) A)
 → Var70 Γ A

vz70 : ∀{Γ A} → Var70 (snoc70 Γ A) A; vz70
 = λ Var70 vz70 vs → vz70

vs70 : ∀{Γ B A} → Var70 Γ A → Var70 (snoc70 Γ B) A; vs70
 = λ x Var70 vz70 vs70 → vs70 (x Var70 vz70 vs70)

Tm70 : Con70 → Ty70 → Set; Tm70
 = λ Γ A →
   (Tm70  : Con70 → Ty70 → Set)
   (var   : ∀{Γ A} → Var70 Γ A → Tm70 Γ A)
   (lam   : ∀{Γ A B} → Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B))
   (app   : ∀{Γ A B} → Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B)
   (tt    : ∀{Γ} → Tm70 Γ top70)
   (pair  : ∀{Γ A B} → Tm70 Γ A → Tm70 Γ B → Tm70 Γ (prod70 A B))
   (fst   : ∀{Γ A B} → Tm70 Γ (prod70 A B) → Tm70 Γ A)
   (snd   : ∀{Γ A B} → Tm70 Γ (prod70 A B) → Tm70 Γ B)
   (left  : ∀{Γ A B} → Tm70 Γ A → Tm70 Γ (sum70 A B))
   (right : ∀{Γ A B} → Tm70 Γ B → Tm70 Γ (sum70 A B))
   (case  : ∀{Γ A B C} → Tm70 Γ (sum70 A B) → Tm70 Γ (arr70 A C) → Tm70 Γ (arr70 B C) → Tm70 Γ C)
   (zero  : ∀{Γ} → Tm70 Γ nat70)
   (suc   : ∀{Γ} → Tm70 Γ nat70 → Tm70 Γ nat70)
   (rec   : ∀{Γ A} → Tm70 Γ nat70 → Tm70 Γ (arr70 nat70 (arr70 A A)) → Tm70 Γ A → Tm70 Γ A)
 → Tm70 Γ A

var70 : ∀{Γ A} → Var70 Γ A → Tm70 Γ A; var70
 = λ x Tm70 var70 lam app tt pair fst snd left right case zero suc rec →
     var70 x

lam70 : ∀{Γ A B} → Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B); lam70
 = λ t Tm70 var70 lam70 app tt pair fst snd left right case zero suc rec →
     lam70 (t Tm70 var70 lam70 app tt pair fst snd left right case zero suc rec)

app70 : ∀{Γ A B} → Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B; app70
 = λ t u Tm70 var70 lam70 app70 tt pair fst snd left right case zero suc rec →
     app70 (t Tm70 var70 lam70 app70 tt pair fst snd left right case zero suc rec)
         (u Tm70 var70 lam70 app70 tt pair fst snd left right case zero suc rec)

tt70 : ∀{Γ} → Tm70 Γ top70; tt70
 = λ Tm70 var70 lam70 app70 tt70 pair fst snd left right case zero suc rec → tt70

pair70 : ∀{Γ A B} → Tm70 Γ A → Tm70 Γ B → Tm70 Γ (prod70 A B); pair70
 = λ t u Tm70 var70 lam70 app70 tt70 pair70 fst snd left right case zero suc rec →
     pair70 (t Tm70 var70 lam70 app70 tt70 pair70 fst snd left right case zero suc rec)
          (u Tm70 var70 lam70 app70 tt70 pair70 fst snd left right case zero suc rec)

fst70 : ∀{Γ A B} → Tm70 Γ (prod70 A B) → Tm70 Γ A; fst70
 = λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd left right case zero suc rec →
     fst70 (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd left right case zero suc rec)

snd70 : ∀{Γ A B} → Tm70 Γ (prod70 A B) → Tm70 Γ B; snd70
 = λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left right case zero suc rec →
     snd70 (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left right case zero suc rec)

left70 : ∀{Γ A B} → Tm70 Γ A → Tm70 Γ (sum70 A B); left70
 = λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right case zero suc rec →
     left70 (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right case zero suc rec)

right70 : ∀{Γ A B} → Tm70 Γ B → Tm70 Γ (sum70 A B); right70
 = λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case zero suc rec →
     right70 (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case zero suc rec)

case70 : ∀{Γ A B C} → Tm70 Γ (sum70 A B) → Tm70 Γ (arr70 A C) → Tm70 Γ (arr70 B C) → Tm70 Γ C; case70
 = λ t u v Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero suc rec →
     case70 (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero suc rec)
           (u Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero suc rec)
           (v Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero suc rec)

zero70  : ∀{Γ} → Tm70 Γ nat70; zero70
 = λ Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc rec → zero70

suc70 : ∀{Γ} → Tm70 Γ nat70 → Tm70 Γ nat70; suc70
 = λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec →
   suc70 (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec)

rec70 : ∀{Γ A} → Tm70 Γ nat70 → Tm70 Γ (arr70 nat70 (arr70 A A)) → Tm70 Γ A → Tm70 Γ A; rec70
 = λ t u v Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec70 →
     rec70 (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec70)
         (u Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec70)
         (v Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec70)

v070 : ∀{Γ A} → Tm70 (snoc70 Γ A) A; v070
 = var70 vz70

v170 : ∀{Γ A B} → Tm70 (snoc70 (snoc70 Γ A) B) A; v170
 = var70 (vs70 vz70)

v270 : ∀{Γ A B C} → Tm70 (snoc70 (snoc70 (snoc70 Γ A) B) C) A; v270
 = var70 (vs70 (vs70 vz70))

v370 : ∀{Γ A B C D} → Tm70 (snoc70 (snoc70 (snoc70 (snoc70 Γ A) B) C) D) A; v370
 = var70 (vs70 (vs70 (vs70 vz70)))

tbool70 : Ty70; tbool70
 = sum70 top70 top70

true70 : ∀{Γ} → Tm70 Γ tbool70; true70
 = left70 tt70

tfalse70 : ∀{Γ} → Tm70 Γ tbool70; tfalse70
 = right70 tt70

ifthenelse70 : ∀{Γ A} → Tm70 Γ (arr70 tbool70 (arr70 A (arr70 A A))); ifthenelse70
 = lam70 (lam70 (lam70 (case70 v270 (lam70 v270) (lam70 v170))))

times470 : ∀{Γ A} → Tm70 Γ (arr70 (arr70 A A) (arr70 A A)); times470
  = lam70 (lam70 (app70 v170 (app70 v170 (app70 v170 (app70 v170 v070)))))

add70 : ∀{Γ} → Tm70 Γ (arr70 nat70 (arr70 nat70 nat70)); add70
 = lam70 (rec70 v070
       (lam70 (lam70 (lam70 (suc70 (app70 v170 v070)))))
       (lam70 v070))

mul70 : ∀{Γ} → Tm70 Γ (arr70 nat70 (arr70 nat70 nat70)); mul70
 = lam70 (rec70 v070
       (lam70 (lam70 (lam70 (app70 (app70 add70 (app70 v170 v070)) v070))))
       (lam70 zero70))

fact70 : ∀{Γ} → Tm70 Γ (arr70 nat70 nat70); fact70
 = lam70 (rec70 v070 (lam70 (lam70 (app70 (app70 mul70 (suc70 v170)) v070)))
        (suc70 zero70))
{-# OPTIONS --type-in-type #-}

Ty71 : Set
Ty71 =
   (Ty71         : Set)
   (nat top bot  : Ty71)
   (arr prod sum : Ty71 → Ty71 → Ty71)
 → Ty71

nat71 : Ty71; nat71 = λ _ nat71 _ _ _ _ _ → nat71
top71 : Ty71; top71 = λ _ _ top71 _ _ _ _ → top71
bot71 : Ty71; bot71 = λ _ _ _ bot71 _ _ _ → bot71

arr71 : Ty71 → Ty71 → Ty71; arr71
 = λ A B Ty71 nat71 top71 bot71 arr71 prod sum →
     arr71 (A Ty71 nat71 top71 bot71 arr71 prod sum) (B Ty71 nat71 top71 bot71 arr71 prod sum)

prod71 : Ty71 → Ty71 → Ty71; prod71
 = λ A B Ty71 nat71 top71 bot71 arr71 prod71 sum →
     prod71 (A Ty71 nat71 top71 bot71 arr71 prod71 sum) (B Ty71 nat71 top71 bot71 arr71 prod71 sum)

sum71 : Ty71 → Ty71 → Ty71; sum71
 = λ A B Ty71 nat71 top71 bot71 arr71 prod71 sum71 →
     sum71 (A Ty71 nat71 top71 bot71 arr71 prod71 sum71) (B Ty71 nat71 top71 bot71 arr71 prod71 sum71)

Con71 : Set; Con71
 = (Con71 : Set)
   (nil  : Con71)
   (snoc : Con71 → Ty71 → Con71)
 → Con71

nil71 : Con71; nil71
 = λ Con71 nil71 snoc → nil71

snoc71 : Con71 → Ty71 → Con71; snoc71
 = λ Γ A Con71 nil71 snoc71 → snoc71 (Γ Con71 nil71 snoc71) A

Var71 : Con71 → Ty71 → Set; Var71
 = λ Γ A →
   (Var71 : Con71 → Ty71 → Set)
   (vz  : ∀{Γ A} → Var71 (snoc71 Γ A) A)
   (vs  : ∀{Γ B A} → Var71 Γ A → Var71 (snoc71 Γ B) A)
 → Var71 Γ A

vz71 : ∀{Γ A} → Var71 (snoc71 Γ A) A; vz71
 = λ Var71 vz71 vs → vz71

vs71 : ∀{Γ B A} → Var71 Γ A → Var71 (snoc71 Γ B) A; vs71
 = λ x Var71 vz71 vs71 → vs71 (x Var71 vz71 vs71)

Tm71 : Con71 → Ty71 → Set; Tm71
 = λ Γ A →
   (Tm71  : Con71 → Ty71 → Set)
   (var   : ∀{Γ A} → Var71 Γ A → Tm71 Γ A)
   (lam   : ∀{Γ A B} → Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B))
   (app   : ∀{Γ A B} → Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B)
   (tt    : ∀{Γ} → Tm71 Γ top71)
   (pair  : ∀{Γ A B} → Tm71 Γ A → Tm71 Γ B → Tm71 Γ (prod71 A B))
   (fst   : ∀{Γ A B} → Tm71 Γ (prod71 A B) → Tm71 Γ A)
   (snd   : ∀{Γ A B} → Tm71 Γ (prod71 A B) → Tm71 Γ B)
   (left  : ∀{Γ A B} → Tm71 Γ A → Tm71 Γ (sum71 A B))
   (right : ∀{Γ A B} → Tm71 Γ B → Tm71 Γ (sum71 A B))
   (case  : ∀{Γ A B C} → Tm71 Γ (sum71 A B) → Tm71 Γ (arr71 A C) → Tm71 Γ (arr71 B C) → Tm71 Γ C)
   (zero  : ∀{Γ} → Tm71 Γ nat71)
   (suc   : ∀{Γ} → Tm71 Γ nat71 → Tm71 Γ nat71)
   (rec   : ∀{Γ A} → Tm71 Γ nat71 → Tm71 Γ (arr71 nat71 (arr71 A A)) → Tm71 Γ A → Tm71 Γ A)
 → Tm71 Γ A

var71 : ∀{Γ A} → Var71 Γ A → Tm71 Γ A; var71
 = λ x Tm71 var71 lam app tt pair fst snd left right case zero suc rec →
     var71 x

lam71 : ∀{Γ A B} → Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B); lam71
 = λ t Tm71 var71 lam71 app tt pair fst snd left right case zero suc rec →
     lam71 (t Tm71 var71 lam71 app tt pair fst snd left right case zero suc rec)

app71 : ∀{Γ A B} → Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B; app71
 = λ t u Tm71 var71 lam71 app71 tt pair fst snd left right case zero suc rec →
     app71 (t Tm71 var71 lam71 app71 tt pair fst snd left right case zero suc rec)
         (u Tm71 var71 lam71 app71 tt pair fst snd left right case zero suc rec)

tt71 : ∀{Γ} → Tm71 Γ top71; tt71
 = λ Tm71 var71 lam71 app71 tt71 pair fst snd left right case zero suc rec → tt71

pair71 : ∀{Γ A B} → Tm71 Γ A → Tm71 Γ B → Tm71 Γ (prod71 A B); pair71
 = λ t u Tm71 var71 lam71 app71 tt71 pair71 fst snd left right case zero suc rec →
     pair71 (t Tm71 var71 lam71 app71 tt71 pair71 fst snd left right case zero suc rec)
          (u Tm71 var71 lam71 app71 tt71 pair71 fst snd left right case zero suc rec)

fst71 : ∀{Γ A B} → Tm71 Γ (prod71 A B) → Tm71 Γ A; fst71
 = λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd left right case zero suc rec →
     fst71 (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd left right case zero suc rec)

snd71 : ∀{Γ A B} → Tm71 Γ (prod71 A B) → Tm71 Γ B; snd71
 = λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left right case zero suc rec →
     snd71 (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left right case zero suc rec)

left71 : ∀{Γ A B} → Tm71 Γ A → Tm71 Γ (sum71 A B); left71
 = λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right case zero suc rec →
     left71 (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right case zero suc rec)

right71 : ∀{Γ A B} → Tm71 Γ B → Tm71 Γ (sum71 A B); right71
 = λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case zero suc rec →
     right71 (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case zero suc rec)

case71 : ∀{Γ A B C} → Tm71 Γ (sum71 A B) → Tm71 Γ (arr71 A C) → Tm71 Γ (arr71 B C) → Tm71 Γ C; case71
 = λ t u v Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero suc rec →
     case71 (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero suc rec)
           (u Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero suc rec)
           (v Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero suc rec)

zero71  : ∀{Γ} → Tm71 Γ nat71; zero71
 = λ Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc rec → zero71

suc71 : ∀{Γ} → Tm71 Γ nat71 → Tm71 Γ nat71; suc71
 = λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec →
   suc71 (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec)

rec71 : ∀{Γ A} → Tm71 Γ nat71 → Tm71 Γ (arr71 nat71 (arr71 A A)) → Tm71 Γ A → Tm71 Γ A; rec71
 = λ t u v Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec71 →
     rec71 (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec71)
         (u Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec71)
         (v Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec71)

v071 : ∀{Γ A} → Tm71 (snoc71 Γ A) A; v071
 = var71 vz71

v171 : ∀{Γ A B} → Tm71 (snoc71 (snoc71 Γ A) B) A; v171
 = var71 (vs71 vz71)

v271 : ∀{Γ A B C} → Tm71 (snoc71 (snoc71 (snoc71 Γ A) B) C) A; v271
 = var71 (vs71 (vs71 vz71))

v371 : ∀{Γ A B C D} → Tm71 (snoc71 (snoc71 (snoc71 (snoc71 Γ A) B) C) D) A; v371
 = var71 (vs71 (vs71 (vs71 vz71)))

tbool71 : Ty71; tbool71
 = sum71 top71 top71

true71 : ∀{Γ} → Tm71 Γ tbool71; true71
 = left71 tt71

tfalse71 : ∀{Γ} → Tm71 Γ tbool71; tfalse71
 = right71 tt71

ifthenelse71 : ∀{Γ A} → Tm71 Γ (arr71 tbool71 (arr71 A (arr71 A A))); ifthenelse71
 = lam71 (lam71 (lam71 (case71 v271 (lam71 v271) (lam71 v171))))

times471 : ∀{Γ A} → Tm71 Γ (arr71 (arr71 A A) (arr71 A A)); times471
  = lam71 (lam71 (app71 v171 (app71 v171 (app71 v171 (app71 v171 v071)))))

add71 : ∀{Γ} → Tm71 Γ (arr71 nat71 (arr71 nat71 nat71)); add71
 = lam71 (rec71 v071
       (lam71 (lam71 (lam71 (suc71 (app71 v171 v071)))))
       (lam71 v071))

mul71 : ∀{Γ} → Tm71 Γ (arr71 nat71 (arr71 nat71 nat71)); mul71
 = lam71 (rec71 v071
       (lam71 (lam71 (lam71 (app71 (app71 add71 (app71 v171 v071)) v071))))
       (lam71 zero71))

fact71 : ∀{Γ} → Tm71 Γ (arr71 nat71 nat71); fact71
 = lam71 (rec71 v071 (lam71 (lam71 (app71 (app71 mul71 (suc71 v171)) v071)))
        (suc71 zero71))
{-# OPTIONS --type-in-type #-}

Ty72 : Set
Ty72 =
   (Ty72         : Set)
   (nat top bot  : Ty72)
   (arr prod sum : Ty72 → Ty72 → Ty72)
 → Ty72

nat72 : Ty72; nat72 = λ _ nat72 _ _ _ _ _ → nat72
top72 : Ty72; top72 = λ _ _ top72 _ _ _ _ → top72
bot72 : Ty72; bot72 = λ _ _ _ bot72 _ _ _ → bot72

arr72 : Ty72 → Ty72 → Ty72; arr72
 = λ A B Ty72 nat72 top72 bot72 arr72 prod sum →
     arr72 (A Ty72 nat72 top72 bot72 arr72 prod sum) (B Ty72 nat72 top72 bot72 arr72 prod sum)

prod72 : Ty72 → Ty72 → Ty72; prod72
 = λ A B Ty72 nat72 top72 bot72 arr72 prod72 sum →
     prod72 (A Ty72 nat72 top72 bot72 arr72 prod72 sum) (B Ty72 nat72 top72 bot72 arr72 prod72 sum)

sum72 : Ty72 → Ty72 → Ty72; sum72
 = λ A B Ty72 nat72 top72 bot72 arr72 prod72 sum72 →
     sum72 (A Ty72 nat72 top72 bot72 arr72 prod72 sum72) (B Ty72 nat72 top72 bot72 arr72 prod72 sum72)

Con72 : Set; Con72
 = (Con72 : Set)
   (nil  : Con72)
   (snoc : Con72 → Ty72 → Con72)
 → Con72

nil72 : Con72; nil72
 = λ Con72 nil72 snoc → nil72

snoc72 : Con72 → Ty72 → Con72; snoc72
 = λ Γ A Con72 nil72 snoc72 → snoc72 (Γ Con72 nil72 snoc72) A

Var72 : Con72 → Ty72 → Set; Var72
 = λ Γ A →
   (Var72 : Con72 → Ty72 → Set)
   (vz  : ∀{Γ A} → Var72 (snoc72 Γ A) A)
   (vs  : ∀{Γ B A} → Var72 Γ A → Var72 (snoc72 Γ B) A)
 → Var72 Γ A

vz72 : ∀{Γ A} → Var72 (snoc72 Γ A) A; vz72
 = λ Var72 vz72 vs → vz72

vs72 : ∀{Γ B A} → Var72 Γ A → Var72 (snoc72 Γ B) A; vs72
 = λ x Var72 vz72 vs72 → vs72 (x Var72 vz72 vs72)

Tm72 : Con72 → Ty72 → Set; Tm72
 = λ Γ A →
   (Tm72  : Con72 → Ty72 → Set)
   (var   : ∀{Γ A} → Var72 Γ A → Tm72 Γ A)
   (lam   : ∀{Γ A B} → Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B))
   (app   : ∀{Γ A B} → Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B)
   (tt    : ∀{Γ} → Tm72 Γ top72)
   (pair  : ∀{Γ A B} → Tm72 Γ A → Tm72 Γ B → Tm72 Γ (prod72 A B))
   (fst   : ∀{Γ A B} → Tm72 Γ (prod72 A B) → Tm72 Γ A)
   (snd   : ∀{Γ A B} → Tm72 Γ (prod72 A B) → Tm72 Γ B)
   (left  : ∀{Γ A B} → Tm72 Γ A → Tm72 Γ (sum72 A B))
   (right : ∀{Γ A B} → Tm72 Γ B → Tm72 Γ (sum72 A B))
   (case  : ∀{Γ A B C} → Tm72 Γ (sum72 A B) → Tm72 Γ (arr72 A C) → Tm72 Γ (arr72 B C) → Tm72 Γ C)
   (zero  : ∀{Γ} → Tm72 Γ nat72)
   (suc   : ∀{Γ} → Tm72 Γ nat72 → Tm72 Γ nat72)
   (rec   : ∀{Γ A} → Tm72 Γ nat72 → Tm72 Γ (arr72 nat72 (arr72 A A)) → Tm72 Γ A → Tm72 Γ A)
 → Tm72 Γ A

var72 : ∀{Γ A} → Var72 Γ A → Tm72 Γ A; var72
 = λ x Tm72 var72 lam app tt pair fst snd left right case zero suc rec →
     var72 x

lam72 : ∀{Γ A B} → Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B); lam72
 = λ t Tm72 var72 lam72 app tt pair fst snd left right case zero suc rec →
     lam72 (t Tm72 var72 lam72 app tt pair fst snd left right case zero suc rec)

app72 : ∀{Γ A B} → Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B; app72
 = λ t u Tm72 var72 lam72 app72 tt pair fst snd left right case zero suc rec →
     app72 (t Tm72 var72 lam72 app72 tt pair fst snd left right case zero suc rec)
         (u Tm72 var72 lam72 app72 tt pair fst snd left right case zero suc rec)

tt72 : ∀{Γ} → Tm72 Γ top72; tt72
 = λ Tm72 var72 lam72 app72 tt72 pair fst snd left right case zero suc rec → tt72

pair72 : ∀{Γ A B} → Tm72 Γ A → Tm72 Γ B → Tm72 Γ (prod72 A B); pair72
 = λ t u Tm72 var72 lam72 app72 tt72 pair72 fst snd left right case zero suc rec →
     pair72 (t Tm72 var72 lam72 app72 tt72 pair72 fst snd left right case zero suc rec)
          (u Tm72 var72 lam72 app72 tt72 pair72 fst snd left right case zero suc rec)

fst72 : ∀{Γ A B} → Tm72 Γ (prod72 A B) → Tm72 Γ A; fst72
 = λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd left right case zero suc rec →
     fst72 (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd left right case zero suc rec)

snd72 : ∀{Γ A B} → Tm72 Γ (prod72 A B) → Tm72 Γ B; snd72
 = λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left right case zero suc rec →
     snd72 (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left right case zero suc rec)

left72 : ∀{Γ A B} → Tm72 Γ A → Tm72 Γ (sum72 A B); left72
 = λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right case zero suc rec →
     left72 (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right case zero suc rec)

right72 : ∀{Γ A B} → Tm72 Γ B → Tm72 Γ (sum72 A B); right72
 = λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case zero suc rec →
     right72 (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case zero suc rec)

case72 : ∀{Γ A B C} → Tm72 Γ (sum72 A B) → Tm72 Γ (arr72 A C) → Tm72 Γ (arr72 B C) → Tm72 Γ C; case72
 = λ t u v Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero suc rec →
     case72 (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero suc rec)
           (u Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero suc rec)
           (v Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero suc rec)

zero72  : ∀{Γ} → Tm72 Γ nat72; zero72
 = λ Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc rec → zero72

suc72 : ∀{Γ} → Tm72 Γ nat72 → Tm72 Γ nat72; suc72
 = λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec →
   suc72 (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec)

rec72 : ∀{Γ A} → Tm72 Γ nat72 → Tm72 Γ (arr72 nat72 (arr72 A A)) → Tm72 Γ A → Tm72 Γ A; rec72
 = λ t u v Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec72 →
     rec72 (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec72)
         (u Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec72)
         (v Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec72)

v072 : ∀{Γ A} → Tm72 (snoc72 Γ A) A; v072
 = var72 vz72

v172 : ∀{Γ A B} → Tm72 (snoc72 (snoc72 Γ A) B) A; v172
 = var72 (vs72 vz72)

v272 : ∀{Γ A B C} → Tm72 (snoc72 (snoc72 (snoc72 Γ A) B) C) A; v272
 = var72 (vs72 (vs72 vz72))

v372 : ∀{Γ A B C D} → Tm72 (snoc72 (snoc72 (snoc72 (snoc72 Γ A) B) C) D) A; v372
 = var72 (vs72 (vs72 (vs72 vz72)))

tbool72 : Ty72; tbool72
 = sum72 top72 top72

true72 : ∀{Γ} → Tm72 Γ tbool72; true72
 = left72 tt72

tfalse72 : ∀{Γ} → Tm72 Γ tbool72; tfalse72
 = right72 tt72

ifthenelse72 : ∀{Γ A} → Tm72 Γ (arr72 tbool72 (arr72 A (arr72 A A))); ifthenelse72
 = lam72 (lam72 (lam72 (case72 v272 (lam72 v272) (lam72 v172))))

times472 : ∀{Γ A} → Tm72 Γ (arr72 (arr72 A A) (arr72 A A)); times472
  = lam72 (lam72 (app72 v172 (app72 v172 (app72 v172 (app72 v172 v072)))))

add72 : ∀{Γ} → Tm72 Γ (arr72 nat72 (arr72 nat72 nat72)); add72
 = lam72 (rec72 v072
       (lam72 (lam72 (lam72 (suc72 (app72 v172 v072)))))
       (lam72 v072))

mul72 : ∀{Γ} → Tm72 Γ (arr72 nat72 (arr72 nat72 nat72)); mul72
 = lam72 (rec72 v072
       (lam72 (lam72 (lam72 (app72 (app72 add72 (app72 v172 v072)) v072))))
       (lam72 zero72))

fact72 : ∀{Γ} → Tm72 Γ (arr72 nat72 nat72); fact72
 = lam72 (rec72 v072 (lam72 (lam72 (app72 (app72 mul72 (suc72 v172)) v072)))
        (suc72 zero72))
{-# OPTIONS --type-in-type #-}

Ty73 : Set
Ty73 =
   (Ty73         : Set)
   (nat top bot  : Ty73)
   (arr prod sum : Ty73 → Ty73 → Ty73)
 → Ty73

nat73 : Ty73; nat73 = λ _ nat73 _ _ _ _ _ → nat73
top73 : Ty73; top73 = λ _ _ top73 _ _ _ _ → top73
bot73 : Ty73; bot73 = λ _ _ _ bot73 _ _ _ → bot73

arr73 : Ty73 → Ty73 → Ty73; arr73
 = λ A B Ty73 nat73 top73 bot73 arr73 prod sum →
     arr73 (A Ty73 nat73 top73 bot73 arr73 prod sum) (B Ty73 nat73 top73 bot73 arr73 prod sum)

prod73 : Ty73 → Ty73 → Ty73; prod73
 = λ A B Ty73 nat73 top73 bot73 arr73 prod73 sum →
     prod73 (A Ty73 nat73 top73 bot73 arr73 prod73 sum) (B Ty73 nat73 top73 bot73 arr73 prod73 sum)

sum73 : Ty73 → Ty73 → Ty73; sum73
 = λ A B Ty73 nat73 top73 bot73 arr73 prod73 sum73 →
     sum73 (A Ty73 nat73 top73 bot73 arr73 prod73 sum73) (B Ty73 nat73 top73 bot73 arr73 prod73 sum73)

Con73 : Set; Con73
 = (Con73 : Set)
   (nil  : Con73)
   (snoc : Con73 → Ty73 → Con73)
 → Con73

nil73 : Con73; nil73
 = λ Con73 nil73 snoc → nil73

snoc73 : Con73 → Ty73 → Con73; snoc73
 = λ Γ A Con73 nil73 snoc73 → snoc73 (Γ Con73 nil73 snoc73) A

Var73 : Con73 → Ty73 → Set; Var73
 = λ Γ A →
   (Var73 : Con73 → Ty73 → Set)
   (vz  : ∀{Γ A} → Var73 (snoc73 Γ A) A)
   (vs  : ∀{Γ B A} → Var73 Γ A → Var73 (snoc73 Γ B) A)
 → Var73 Γ A

vz73 : ∀{Γ A} → Var73 (snoc73 Γ A) A; vz73
 = λ Var73 vz73 vs → vz73

vs73 : ∀{Γ B A} → Var73 Γ A → Var73 (snoc73 Γ B) A; vs73
 = λ x Var73 vz73 vs73 → vs73 (x Var73 vz73 vs73)

Tm73 : Con73 → Ty73 → Set; Tm73
 = λ Γ A →
   (Tm73  : Con73 → Ty73 → Set)
   (var   : ∀{Γ A} → Var73 Γ A → Tm73 Γ A)
   (lam   : ∀{Γ A B} → Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B))
   (app   : ∀{Γ A B} → Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B)
   (tt    : ∀{Γ} → Tm73 Γ top73)
   (pair  : ∀{Γ A B} → Tm73 Γ A → Tm73 Γ B → Tm73 Γ (prod73 A B))
   (fst   : ∀{Γ A B} → Tm73 Γ (prod73 A B) → Tm73 Γ A)
   (snd   : ∀{Γ A B} → Tm73 Γ (prod73 A B) → Tm73 Γ B)
   (left  : ∀{Γ A B} → Tm73 Γ A → Tm73 Γ (sum73 A B))
   (right : ∀{Γ A B} → Tm73 Γ B → Tm73 Γ (sum73 A B))
   (case  : ∀{Γ A B C} → Tm73 Γ (sum73 A B) → Tm73 Γ (arr73 A C) → Tm73 Γ (arr73 B C) → Tm73 Γ C)
   (zero  : ∀{Γ} → Tm73 Γ nat73)
   (suc   : ∀{Γ} → Tm73 Γ nat73 → Tm73 Γ nat73)
   (rec   : ∀{Γ A} → Tm73 Γ nat73 → Tm73 Γ (arr73 nat73 (arr73 A A)) → Tm73 Γ A → Tm73 Γ A)
 → Tm73 Γ A

var73 : ∀{Γ A} → Var73 Γ A → Tm73 Γ A; var73
 = λ x Tm73 var73 lam app tt pair fst snd left right case zero suc rec →
     var73 x

lam73 : ∀{Γ A B} → Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B); lam73
 = λ t Tm73 var73 lam73 app tt pair fst snd left right case zero suc rec →
     lam73 (t Tm73 var73 lam73 app tt pair fst snd left right case zero suc rec)

app73 : ∀{Γ A B} → Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B; app73
 = λ t u Tm73 var73 lam73 app73 tt pair fst snd left right case zero suc rec →
     app73 (t Tm73 var73 lam73 app73 tt pair fst snd left right case zero suc rec)
         (u Tm73 var73 lam73 app73 tt pair fst snd left right case zero suc rec)

tt73 : ∀{Γ} → Tm73 Γ top73; tt73
 = λ Tm73 var73 lam73 app73 tt73 pair fst snd left right case zero suc rec → tt73

pair73 : ∀{Γ A B} → Tm73 Γ A → Tm73 Γ B → Tm73 Γ (prod73 A B); pair73
 = λ t u Tm73 var73 lam73 app73 tt73 pair73 fst snd left right case zero suc rec →
     pair73 (t Tm73 var73 lam73 app73 tt73 pair73 fst snd left right case zero suc rec)
          (u Tm73 var73 lam73 app73 tt73 pair73 fst snd left right case zero suc rec)

fst73 : ∀{Γ A B} → Tm73 Γ (prod73 A B) → Tm73 Γ A; fst73
 = λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd left right case zero suc rec →
     fst73 (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd left right case zero suc rec)

snd73 : ∀{Γ A B} → Tm73 Γ (prod73 A B) → Tm73 Γ B; snd73
 = λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left right case zero suc rec →
     snd73 (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left right case zero suc rec)

left73 : ∀{Γ A B} → Tm73 Γ A → Tm73 Γ (sum73 A B); left73
 = λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right case zero suc rec →
     left73 (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right case zero suc rec)

right73 : ∀{Γ A B} → Tm73 Γ B → Tm73 Γ (sum73 A B); right73
 = λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case zero suc rec →
     right73 (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case zero suc rec)

case73 : ∀{Γ A B C} → Tm73 Γ (sum73 A B) → Tm73 Γ (arr73 A C) → Tm73 Γ (arr73 B C) → Tm73 Γ C; case73
 = λ t u v Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero suc rec →
     case73 (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero suc rec)
           (u Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero suc rec)
           (v Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero suc rec)

zero73  : ∀{Γ} → Tm73 Γ nat73; zero73
 = λ Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc rec → zero73

suc73 : ∀{Γ} → Tm73 Γ nat73 → Tm73 Γ nat73; suc73
 = λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec →
   suc73 (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec)

rec73 : ∀{Γ A} → Tm73 Γ nat73 → Tm73 Γ (arr73 nat73 (arr73 A A)) → Tm73 Γ A → Tm73 Γ A; rec73
 = λ t u v Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec73 →
     rec73 (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec73)
         (u Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec73)
         (v Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec73)

v073 : ∀{Γ A} → Tm73 (snoc73 Γ A) A; v073
 = var73 vz73

v173 : ∀{Γ A B} → Tm73 (snoc73 (snoc73 Γ A) B) A; v173
 = var73 (vs73 vz73)

v273 : ∀{Γ A B C} → Tm73 (snoc73 (snoc73 (snoc73 Γ A) B) C) A; v273
 = var73 (vs73 (vs73 vz73))

v373 : ∀{Γ A B C D} → Tm73 (snoc73 (snoc73 (snoc73 (snoc73 Γ A) B) C) D) A; v373
 = var73 (vs73 (vs73 (vs73 vz73)))

tbool73 : Ty73; tbool73
 = sum73 top73 top73

true73 : ∀{Γ} → Tm73 Γ tbool73; true73
 = left73 tt73

tfalse73 : ∀{Γ} → Tm73 Γ tbool73; tfalse73
 = right73 tt73

ifthenelse73 : ∀{Γ A} → Tm73 Γ (arr73 tbool73 (arr73 A (arr73 A A))); ifthenelse73
 = lam73 (lam73 (lam73 (case73 v273 (lam73 v273) (lam73 v173))))

times473 : ∀{Γ A} → Tm73 Γ (arr73 (arr73 A A) (arr73 A A)); times473
  = lam73 (lam73 (app73 v173 (app73 v173 (app73 v173 (app73 v173 v073)))))

add73 : ∀{Γ} → Tm73 Γ (arr73 nat73 (arr73 nat73 nat73)); add73
 = lam73 (rec73 v073
       (lam73 (lam73 (lam73 (suc73 (app73 v173 v073)))))
       (lam73 v073))

mul73 : ∀{Γ} → Tm73 Γ (arr73 nat73 (arr73 nat73 nat73)); mul73
 = lam73 (rec73 v073
       (lam73 (lam73 (lam73 (app73 (app73 add73 (app73 v173 v073)) v073))))
       (lam73 zero73))

fact73 : ∀{Γ} → Tm73 Γ (arr73 nat73 nat73); fact73
 = lam73 (rec73 v073 (lam73 (lam73 (app73 (app73 mul73 (suc73 v173)) v073)))
        (suc73 zero73))
{-# OPTIONS --type-in-type #-}

Ty74 : Set
Ty74 =
   (Ty74         : Set)
   (nat top bot  : Ty74)
   (arr prod sum : Ty74 → Ty74 → Ty74)
 → Ty74

nat74 : Ty74; nat74 = λ _ nat74 _ _ _ _ _ → nat74
top74 : Ty74; top74 = λ _ _ top74 _ _ _ _ → top74
bot74 : Ty74; bot74 = λ _ _ _ bot74 _ _ _ → bot74

arr74 : Ty74 → Ty74 → Ty74; arr74
 = λ A B Ty74 nat74 top74 bot74 arr74 prod sum →
     arr74 (A Ty74 nat74 top74 bot74 arr74 prod sum) (B Ty74 nat74 top74 bot74 arr74 prod sum)

prod74 : Ty74 → Ty74 → Ty74; prod74
 = λ A B Ty74 nat74 top74 bot74 arr74 prod74 sum →
     prod74 (A Ty74 nat74 top74 bot74 arr74 prod74 sum) (B Ty74 nat74 top74 bot74 arr74 prod74 sum)

sum74 : Ty74 → Ty74 → Ty74; sum74
 = λ A B Ty74 nat74 top74 bot74 arr74 prod74 sum74 →
     sum74 (A Ty74 nat74 top74 bot74 arr74 prod74 sum74) (B Ty74 nat74 top74 bot74 arr74 prod74 sum74)

Con74 : Set; Con74
 = (Con74 : Set)
   (nil  : Con74)
   (snoc : Con74 → Ty74 → Con74)
 → Con74

nil74 : Con74; nil74
 = λ Con74 nil74 snoc → nil74

snoc74 : Con74 → Ty74 → Con74; snoc74
 = λ Γ A Con74 nil74 snoc74 → snoc74 (Γ Con74 nil74 snoc74) A

Var74 : Con74 → Ty74 → Set; Var74
 = λ Γ A →
   (Var74 : Con74 → Ty74 → Set)
   (vz  : ∀{Γ A} → Var74 (snoc74 Γ A) A)
   (vs  : ∀{Γ B A} → Var74 Γ A → Var74 (snoc74 Γ B) A)
 → Var74 Γ A

vz74 : ∀{Γ A} → Var74 (snoc74 Γ A) A; vz74
 = λ Var74 vz74 vs → vz74

vs74 : ∀{Γ B A} → Var74 Γ A → Var74 (snoc74 Γ B) A; vs74
 = λ x Var74 vz74 vs74 → vs74 (x Var74 vz74 vs74)

Tm74 : Con74 → Ty74 → Set; Tm74
 = λ Γ A →
   (Tm74  : Con74 → Ty74 → Set)
   (var   : ∀{Γ A} → Var74 Γ A → Tm74 Γ A)
   (lam   : ∀{Γ A B} → Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B))
   (app   : ∀{Γ A B} → Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B)
   (tt    : ∀{Γ} → Tm74 Γ top74)
   (pair  : ∀{Γ A B} → Tm74 Γ A → Tm74 Γ B → Tm74 Γ (prod74 A B))
   (fst   : ∀{Γ A B} → Tm74 Γ (prod74 A B) → Tm74 Γ A)
   (snd   : ∀{Γ A B} → Tm74 Γ (prod74 A B) → Tm74 Γ B)
   (left  : ∀{Γ A B} → Tm74 Γ A → Tm74 Γ (sum74 A B))
   (right : ∀{Γ A B} → Tm74 Γ B → Tm74 Γ (sum74 A B))
   (case  : ∀{Γ A B C} → Tm74 Γ (sum74 A B) → Tm74 Γ (arr74 A C) → Tm74 Γ (arr74 B C) → Tm74 Γ C)
   (zero  : ∀{Γ} → Tm74 Γ nat74)
   (suc   : ∀{Γ} → Tm74 Γ nat74 → Tm74 Γ nat74)
   (rec   : ∀{Γ A} → Tm74 Γ nat74 → Tm74 Γ (arr74 nat74 (arr74 A A)) → Tm74 Γ A → Tm74 Γ A)
 → Tm74 Γ A

var74 : ∀{Γ A} → Var74 Γ A → Tm74 Γ A; var74
 = λ x Tm74 var74 lam app tt pair fst snd left right case zero suc rec →
     var74 x

lam74 : ∀{Γ A B} → Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B); lam74
 = λ t Tm74 var74 lam74 app tt pair fst snd left right case zero suc rec →
     lam74 (t Tm74 var74 lam74 app tt pair fst snd left right case zero suc rec)

app74 : ∀{Γ A B} → Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B; app74
 = λ t u Tm74 var74 lam74 app74 tt pair fst snd left right case zero suc rec →
     app74 (t Tm74 var74 lam74 app74 tt pair fst snd left right case zero suc rec)
         (u Tm74 var74 lam74 app74 tt pair fst snd left right case zero suc rec)

tt74 : ∀{Γ} → Tm74 Γ top74; tt74
 = λ Tm74 var74 lam74 app74 tt74 pair fst snd left right case zero suc rec → tt74

pair74 : ∀{Γ A B} → Tm74 Γ A → Tm74 Γ B → Tm74 Γ (prod74 A B); pair74
 = λ t u Tm74 var74 lam74 app74 tt74 pair74 fst snd left right case zero suc rec →
     pair74 (t Tm74 var74 lam74 app74 tt74 pair74 fst snd left right case zero suc rec)
          (u Tm74 var74 lam74 app74 tt74 pair74 fst snd left right case zero suc rec)

fst74 : ∀{Γ A B} → Tm74 Γ (prod74 A B) → Tm74 Γ A; fst74
 = λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd left right case zero suc rec →
     fst74 (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd left right case zero suc rec)

snd74 : ∀{Γ A B} → Tm74 Γ (prod74 A B) → Tm74 Γ B; snd74
 = λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left right case zero suc rec →
     snd74 (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left right case zero suc rec)

left74 : ∀{Γ A B} → Tm74 Γ A → Tm74 Γ (sum74 A B); left74
 = λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right case zero suc rec →
     left74 (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right case zero suc rec)

right74 : ∀{Γ A B} → Tm74 Γ B → Tm74 Γ (sum74 A B); right74
 = λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case zero suc rec →
     right74 (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case zero suc rec)

case74 : ∀{Γ A B C} → Tm74 Γ (sum74 A B) → Tm74 Γ (arr74 A C) → Tm74 Γ (arr74 B C) → Tm74 Γ C; case74
 = λ t u v Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero suc rec →
     case74 (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero suc rec)
           (u Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero suc rec)
           (v Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero suc rec)

zero74  : ∀{Γ} → Tm74 Γ nat74; zero74
 = λ Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc rec → zero74

suc74 : ∀{Γ} → Tm74 Γ nat74 → Tm74 Γ nat74; suc74
 = λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec →
   suc74 (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec)

rec74 : ∀{Γ A} → Tm74 Γ nat74 → Tm74 Γ (arr74 nat74 (arr74 A A)) → Tm74 Γ A → Tm74 Γ A; rec74
 = λ t u v Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec74 →
     rec74 (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec74)
         (u Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec74)
         (v Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec74)

v074 : ∀{Γ A} → Tm74 (snoc74 Γ A) A; v074
 = var74 vz74

v174 : ∀{Γ A B} → Tm74 (snoc74 (snoc74 Γ A) B) A; v174
 = var74 (vs74 vz74)

v274 : ∀{Γ A B C} → Tm74 (snoc74 (snoc74 (snoc74 Γ A) B) C) A; v274
 = var74 (vs74 (vs74 vz74))

v374 : ∀{Γ A B C D} → Tm74 (snoc74 (snoc74 (snoc74 (snoc74 Γ A) B) C) D) A; v374
 = var74 (vs74 (vs74 (vs74 vz74)))

tbool74 : Ty74; tbool74
 = sum74 top74 top74

true74 : ∀{Γ} → Tm74 Γ tbool74; true74
 = left74 tt74

tfalse74 : ∀{Γ} → Tm74 Γ tbool74; tfalse74
 = right74 tt74

ifthenelse74 : ∀{Γ A} → Tm74 Γ (arr74 tbool74 (arr74 A (arr74 A A))); ifthenelse74
 = lam74 (lam74 (lam74 (case74 v274 (lam74 v274) (lam74 v174))))

times474 : ∀{Γ A} → Tm74 Γ (arr74 (arr74 A A) (arr74 A A)); times474
  = lam74 (lam74 (app74 v174 (app74 v174 (app74 v174 (app74 v174 v074)))))

add74 : ∀{Γ} → Tm74 Γ (arr74 nat74 (arr74 nat74 nat74)); add74
 = lam74 (rec74 v074
       (lam74 (lam74 (lam74 (suc74 (app74 v174 v074)))))
       (lam74 v074))

mul74 : ∀{Γ} → Tm74 Γ (arr74 nat74 (arr74 nat74 nat74)); mul74
 = lam74 (rec74 v074
       (lam74 (lam74 (lam74 (app74 (app74 add74 (app74 v174 v074)) v074))))
       (lam74 zero74))

fact74 : ∀{Γ} → Tm74 Γ (arr74 nat74 nat74); fact74
 = lam74 (rec74 v074 (lam74 (lam74 (app74 (app74 mul74 (suc74 v174)) v074)))
        (suc74 zero74))
{-# OPTIONS --type-in-type #-}

Ty75 : Set
Ty75 =
   (Ty75         : Set)
   (nat top bot  : Ty75)
   (arr prod sum : Ty75 → Ty75 → Ty75)
 → Ty75

nat75 : Ty75; nat75 = λ _ nat75 _ _ _ _ _ → nat75
top75 : Ty75; top75 = λ _ _ top75 _ _ _ _ → top75
bot75 : Ty75; bot75 = λ _ _ _ bot75 _ _ _ → bot75

arr75 : Ty75 → Ty75 → Ty75; arr75
 = λ A B Ty75 nat75 top75 bot75 arr75 prod sum →
     arr75 (A Ty75 nat75 top75 bot75 arr75 prod sum) (B Ty75 nat75 top75 bot75 arr75 prod sum)

prod75 : Ty75 → Ty75 → Ty75; prod75
 = λ A B Ty75 nat75 top75 bot75 arr75 prod75 sum →
     prod75 (A Ty75 nat75 top75 bot75 arr75 prod75 sum) (B Ty75 nat75 top75 bot75 arr75 prod75 sum)

sum75 : Ty75 → Ty75 → Ty75; sum75
 = λ A B Ty75 nat75 top75 bot75 arr75 prod75 sum75 →
     sum75 (A Ty75 nat75 top75 bot75 arr75 prod75 sum75) (B Ty75 nat75 top75 bot75 arr75 prod75 sum75)

Con75 : Set; Con75
 = (Con75 : Set)
   (nil  : Con75)
   (snoc : Con75 → Ty75 → Con75)
 → Con75

nil75 : Con75; nil75
 = λ Con75 nil75 snoc → nil75

snoc75 : Con75 → Ty75 → Con75; snoc75
 = λ Γ A Con75 nil75 snoc75 → snoc75 (Γ Con75 nil75 snoc75) A

Var75 : Con75 → Ty75 → Set; Var75
 = λ Γ A →
   (Var75 : Con75 → Ty75 → Set)
   (vz  : ∀{Γ A} → Var75 (snoc75 Γ A) A)
   (vs  : ∀{Γ B A} → Var75 Γ A → Var75 (snoc75 Γ B) A)
 → Var75 Γ A

vz75 : ∀{Γ A} → Var75 (snoc75 Γ A) A; vz75
 = λ Var75 vz75 vs → vz75

vs75 : ∀{Γ B A} → Var75 Γ A → Var75 (snoc75 Γ B) A; vs75
 = λ x Var75 vz75 vs75 → vs75 (x Var75 vz75 vs75)

Tm75 : Con75 → Ty75 → Set; Tm75
 = λ Γ A →
   (Tm75  : Con75 → Ty75 → Set)
   (var   : ∀{Γ A} → Var75 Γ A → Tm75 Γ A)
   (lam   : ∀{Γ A B} → Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B))
   (app   : ∀{Γ A B} → Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B)
   (tt    : ∀{Γ} → Tm75 Γ top75)
   (pair  : ∀{Γ A B} → Tm75 Γ A → Tm75 Γ B → Tm75 Γ (prod75 A B))
   (fst   : ∀{Γ A B} → Tm75 Γ (prod75 A B) → Tm75 Γ A)
   (snd   : ∀{Γ A B} → Tm75 Γ (prod75 A B) → Tm75 Γ B)
   (left  : ∀{Γ A B} → Tm75 Γ A → Tm75 Γ (sum75 A B))
   (right : ∀{Γ A B} → Tm75 Γ B → Tm75 Γ (sum75 A B))
   (case  : ∀{Γ A B C} → Tm75 Γ (sum75 A B) → Tm75 Γ (arr75 A C) → Tm75 Γ (arr75 B C) → Tm75 Γ C)
   (zero  : ∀{Γ} → Tm75 Γ nat75)
   (suc   : ∀{Γ} → Tm75 Γ nat75 → Tm75 Γ nat75)
   (rec   : ∀{Γ A} → Tm75 Γ nat75 → Tm75 Γ (arr75 nat75 (arr75 A A)) → Tm75 Γ A → Tm75 Γ A)
 → Tm75 Γ A

var75 : ∀{Γ A} → Var75 Γ A → Tm75 Γ A; var75
 = λ x Tm75 var75 lam app tt pair fst snd left right case zero suc rec →
     var75 x

lam75 : ∀{Γ A B} → Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B); lam75
 = λ t Tm75 var75 lam75 app tt pair fst snd left right case zero suc rec →
     lam75 (t Tm75 var75 lam75 app tt pair fst snd left right case zero suc rec)

app75 : ∀{Γ A B} → Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B; app75
 = λ t u Tm75 var75 lam75 app75 tt pair fst snd left right case zero suc rec →
     app75 (t Tm75 var75 lam75 app75 tt pair fst snd left right case zero suc rec)
         (u Tm75 var75 lam75 app75 tt pair fst snd left right case zero suc rec)

tt75 : ∀{Γ} → Tm75 Γ top75; tt75
 = λ Tm75 var75 lam75 app75 tt75 pair fst snd left right case zero suc rec → tt75

pair75 : ∀{Γ A B} → Tm75 Γ A → Tm75 Γ B → Tm75 Γ (prod75 A B); pair75
 = λ t u Tm75 var75 lam75 app75 tt75 pair75 fst snd left right case zero suc rec →
     pair75 (t Tm75 var75 lam75 app75 tt75 pair75 fst snd left right case zero suc rec)
          (u Tm75 var75 lam75 app75 tt75 pair75 fst snd left right case zero suc rec)

fst75 : ∀{Γ A B} → Tm75 Γ (prod75 A B) → Tm75 Γ A; fst75
 = λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd left right case zero suc rec →
     fst75 (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd left right case zero suc rec)

snd75 : ∀{Γ A B} → Tm75 Γ (prod75 A B) → Tm75 Γ B; snd75
 = λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left right case zero suc rec →
     snd75 (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left right case zero suc rec)

left75 : ∀{Γ A B} → Tm75 Γ A → Tm75 Γ (sum75 A B); left75
 = λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right case zero suc rec →
     left75 (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right case zero suc rec)

right75 : ∀{Γ A B} → Tm75 Γ B → Tm75 Γ (sum75 A B); right75
 = λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case zero suc rec →
     right75 (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case zero suc rec)

case75 : ∀{Γ A B C} → Tm75 Γ (sum75 A B) → Tm75 Γ (arr75 A C) → Tm75 Γ (arr75 B C) → Tm75 Γ C; case75
 = λ t u v Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero suc rec →
     case75 (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero suc rec)
           (u Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero suc rec)
           (v Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero suc rec)

zero75  : ∀{Γ} → Tm75 Γ nat75; zero75
 = λ Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc rec → zero75

suc75 : ∀{Γ} → Tm75 Γ nat75 → Tm75 Γ nat75; suc75
 = λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec →
   suc75 (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec)

rec75 : ∀{Γ A} → Tm75 Γ nat75 → Tm75 Γ (arr75 nat75 (arr75 A A)) → Tm75 Γ A → Tm75 Γ A; rec75
 = λ t u v Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec75 →
     rec75 (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec75)
         (u Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec75)
         (v Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec75)

v075 : ∀{Γ A} → Tm75 (snoc75 Γ A) A; v075
 = var75 vz75

v175 : ∀{Γ A B} → Tm75 (snoc75 (snoc75 Γ A) B) A; v175
 = var75 (vs75 vz75)

v275 : ∀{Γ A B C} → Tm75 (snoc75 (snoc75 (snoc75 Γ A) B) C) A; v275
 = var75 (vs75 (vs75 vz75))

v375 : ∀{Γ A B C D} → Tm75 (snoc75 (snoc75 (snoc75 (snoc75 Γ A) B) C) D) A; v375
 = var75 (vs75 (vs75 (vs75 vz75)))

tbool75 : Ty75; tbool75
 = sum75 top75 top75

true75 : ∀{Γ} → Tm75 Γ tbool75; true75
 = left75 tt75

tfalse75 : ∀{Γ} → Tm75 Γ tbool75; tfalse75
 = right75 tt75

ifthenelse75 : ∀{Γ A} → Tm75 Γ (arr75 tbool75 (arr75 A (arr75 A A))); ifthenelse75
 = lam75 (lam75 (lam75 (case75 v275 (lam75 v275) (lam75 v175))))

times475 : ∀{Γ A} → Tm75 Γ (arr75 (arr75 A A) (arr75 A A)); times475
  = lam75 (lam75 (app75 v175 (app75 v175 (app75 v175 (app75 v175 v075)))))

add75 : ∀{Γ} → Tm75 Γ (arr75 nat75 (arr75 nat75 nat75)); add75
 = lam75 (rec75 v075
       (lam75 (lam75 (lam75 (suc75 (app75 v175 v075)))))
       (lam75 v075))

mul75 : ∀{Γ} → Tm75 Γ (arr75 nat75 (arr75 nat75 nat75)); mul75
 = lam75 (rec75 v075
       (lam75 (lam75 (lam75 (app75 (app75 add75 (app75 v175 v075)) v075))))
       (lam75 zero75))

fact75 : ∀{Γ} → Tm75 Γ (arr75 nat75 nat75); fact75
 = lam75 (rec75 v075 (lam75 (lam75 (app75 (app75 mul75 (suc75 v175)) v075)))
        (suc75 zero75))
{-# OPTIONS --type-in-type #-}

Ty76 : Set
Ty76 =
   (Ty76         : Set)
   (nat top bot  : Ty76)
   (arr prod sum : Ty76 → Ty76 → Ty76)
 → Ty76

nat76 : Ty76; nat76 = λ _ nat76 _ _ _ _ _ → nat76
top76 : Ty76; top76 = λ _ _ top76 _ _ _ _ → top76
bot76 : Ty76; bot76 = λ _ _ _ bot76 _ _ _ → bot76

arr76 : Ty76 → Ty76 → Ty76; arr76
 = λ A B Ty76 nat76 top76 bot76 arr76 prod sum →
     arr76 (A Ty76 nat76 top76 bot76 arr76 prod sum) (B Ty76 nat76 top76 bot76 arr76 prod sum)

prod76 : Ty76 → Ty76 → Ty76; prod76
 = λ A B Ty76 nat76 top76 bot76 arr76 prod76 sum →
     prod76 (A Ty76 nat76 top76 bot76 arr76 prod76 sum) (B Ty76 nat76 top76 bot76 arr76 prod76 sum)

sum76 : Ty76 → Ty76 → Ty76; sum76
 = λ A B Ty76 nat76 top76 bot76 arr76 prod76 sum76 →
     sum76 (A Ty76 nat76 top76 bot76 arr76 prod76 sum76) (B Ty76 nat76 top76 bot76 arr76 prod76 sum76)

Con76 : Set; Con76
 = (Con76 : Set)
   (nil  : Con76)
   (snoc : Con76 → Ty76 → Con76)
 → Con76

nil76 : Con76; nil76
 = λ Con76 nil76 snoc → nil76

snoc76 : Con76 → Ty76 → Con76; snoc76
 = λ Γ A Con76 nil76 snoc76 → snoc76 (Γ Con76 nil76 snoc76) A

Var76 : Con76 → Ty76 → Set; Var76
 = λ Γ A →
   (Var76 : Con76 → Ty76 → Set)
   (vz  : ∀{Γ A} → Var76 (snoc76 Γ A) A)
   (vs  : ∀{Γ B A} → Var76 Γ A → Var76 (snoc76 Γ B) A)
 → Var76 Γ A

vz76 : ∀{Γ A} → Var76 (snoc76 Γ A) A; vz76
 = λ Var76 vz76 vs → vz76

vs76 : ∀{Γ B A} → Var76 Γ A → Var76 (snoc76 Γ B) A; vs76
 = λ x Var76 vz76 vs76 → vs76 (x Var76 vz76 vs76)

Tm76 : Con76 → Ty76 → Set; Tm76
 = λ Γ A →
   (Tm76  : Con76 → Ty76 → Set)
   (var   : ∀{Γ A} → Var76 Γ A → Tm76 Γ A)
   (lam   : ∀{Γ A B} → Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B))
   (app   : ∀{Γ A B} → Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B)
   (tt    : ∀{Γ} → Tm76 Γ top76)
   (pair  : ∀{Γ A B} → Tm76 Γ A → Tm76 Γ B → Tm76 Γ (prod76 A B))
   (fst   : ∀{Γ A B} → Tm76 Γ (prod76 A B) → Tm76 Γ A)
   (snd   : ∀{Γ A B} → Tm76 Γ (prod76 A B) → Tm76 Γ B)
   (left  : ∀{Γ A B} → Tm76 Γ A → Tm76 Γ (sum76 A B))
   (right : ∀{Γ A B} → Tm76 Γ B → Tm76 Γ (sum76 A B))
   (case  : ∀{Γ A B C} → Tm76 Γ (sum76 A B) → Tm76 Γ (arr76 A C) → Tm76 Γ (arr76 B C) → Tm76 Γ C)
   (zero  : ∀{Γ} → Tm76 Γ nat76)
   (suc   : ∀{Γ} → Tm76 Γ nat76 → Tm76 Γ nat76)
   (rec   : ∀{Γ A} → Tm76 Γ nat76 → Tm76 Γ (arr76 nat76 (arr76 A A)) → Tm76 Γ A → Tm76 Γ A)
 → Tm76 Γ A

var76 : ∀{Γ A} → Var76 Γ A → Tm76 Γ A; var76
 = λ x Tm76 var76 lam app tt pair fst snd left right case zero suc rec →
     var76 x

lam76 : ∀{Γ A B} → Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B); lam76
 = λ t Tm76 var76 lam76 app tt pair fst snd left right case zero suc rec →
     lam76 (t Tm76 var76 lam76 app tt pair fst snd left right case zero suc rec)

app76 : ∀{Γ A B} → Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B; app76
 = λ t u Tm76 var76 lam76 app76 tt pair fst snd left right case zero suc rec →
     app76 (t Tm76 var76 lam76 app76 tt pair fst snd left right case zero suc rec)
         (u Tm76 var76 lam76 app76 tt pair fst snd left right case zero suc rec)

tt76 : ∀{Γ} → Tm76 Γ top76; tt76
 = λ Tm76 var76 lam76 app76 tt76 pair fst snd left right case zero suc rec → tt76

pair76 : ∀{Γ A B} → Tm76 Γ A → Tm76 Γ B → Tm76 Γ (prod76 A B); pair76
 = λ t u Tm76 var76 lam76 app76 tt76 pair76 fst snd left right case zero suc rec →
     pair76 (t Tm76 var76 lam76 app76 tt76 pair76 fst snd left right case zero suc rec)
          (u Tm76 var76 lam76 app76 tt76 pair76 fst snd left right case zero suc rec)

fst76 : ∀{Γ A B} → Tm76 Γ (prod76 A B) → Tm76 Γ A; fst76
 = λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd left right case zero suc rec →
     fst76 (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd left right case zero suc rec)

snd76 : ∀{Γ A B} → Tm76 Γ (prod76 A B) → Tm76 Γ B; snd76
 = λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left right case zero suc rec →
     snd76 (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left right case zero suc rec)

left76 : ∀{Γ A B} → Tm76 Γ A → Tm76 Γ (sum76 A B); left76
 = λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right case zero suc rec →
     left76 (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right case zero suc rec)

right76 : ∀{Γ A B} → Tm76 Γ B → Tm76 Γ (sum76 A B); right76
 = λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case zero suc rec →
     right76 (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case zero suc rec)

case76 : ∀{Γ A B C} → Tm76 Γ (sum76 A B) → Tm76 Γ (arr76 A C) → Tm76 Γ (arr76 B C) → Tm76 Γ C; case76
 = λ t u v Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero suc rec →
     case76 (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero suc rec)
           (u Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero suc rec)
           (v Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero suc rec)

zero76  : ∀{Γ} → Tm76 Γ nat76; zero76
 = λ Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc rec → zero76

suc76 : ∀{Γ} → Tm76 Γ nat76 → Tm76 Γ nat76; suc76
 = λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec →
   suc76 (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec)

rec76 : ∀{Γ A} → Tm76 Γ nat76 → Tm76 Γ (arr76 nat76 (arr76 A A)) → Tm76 Γ A → Tm76 Γ A; rec76
 = λ t u v Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec76 →
     rec76 (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec76)
         (u Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec76)
         (v Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec76)

v076 : ∀{Γ A} → Tm76 (snoc76 Γ A) A; v076
 = var76 vz76

v176 : ∀{Γ A B} → Tm76 (snoc76 (snoc76 Γ A) B) A; v176
 = var76 (vs76 vz76)

v276 : ∀{Γ A B C} → Tm76 (snoc76 (snoc76 (snoc76 Γ A) B) C) A; v276
 = var76 (vs76 (vs76 vz76))

v376 : ∀{Γ A B C D} → Tm76 (snoc76 (snoc76 (snoc76 (snoc76 Γ A) B) C) D) A; v376
 = var76 (vs76 (vs76 (vs76 vz76)))

tbool76 : Ty76; tbool76
 = sum76 top76 top76

true76 : ∀{Γ} → Tm76 Γ tbool76; true76
 = left76 tt76

tfalse76 : ∀{Γ} → Tm76 Γ tbool76; tfalse76
 = right76 tt76

ifthenelse76 : ∀{Γ A} → Tm76 Γ (arr76 tbool76 (arr76 A (arr76 A A))); ifthenelse76
 = lam76 (lam76 (lam76 (case76 v276 (lam76 v276) (lam76 v176))))

times476 : ∀{Γ A} → Tm76 Γ (arr76 (arr76 A A) (arr76 A A)); times476
  = lam76 (lam76 (app76 v176 (app76 v176 (app76 v176 (app76 v176 v076)))))

add76 : ∀{Γ} → Tm76 Γ (arr76 nat76 (arr76 nat76 nat76)); add76
 = lam76 (rec76 v076
       (lam76 (lam76 (lam76 (suc76 (app76 v176 v076)))))
       (lam76 v076))

mul76 : ∀{Γ} → Tm76 Γ (arr76 nat76 (arr76 nat76 nat76)); mul76
 = lam76 (rec76 v076
       (lam76 (lam76 (lam76 (app76 (app76 add76 (app76 v176 v076)) v076))))
       (lam76 zero76))

fact76 : ∀{Γ} → Tm76 Γ (arr76 nat76 nat76); fact76
 = lam76 (rec76 v076 (lam76 (lam76 (app76 (app76 mul76 (suc76 v176)) v076)))
        (suc76 zero76))
{-# OPTIONS --type-in-type #-}

Ty77 : Set
Ty77 =
   (Ty77         : Set)
   (nat top bot  : Ty77)
   (arr prod sum : Ty77 → Ty77 → Ty77)
 → Ty77

nat77 : Ty77; nat77 = λ _ nat77 _ _ _ _ _ → nat77
top77 : Ty77; top77 = λ _ _ top77 _ _ _ _ → top77
bot77 : Ty77; bot77 = λ _ _ _ bot77 _ _ _ → bot77

arr77 : Ty77 → Ty77 → Ty77; arr77
 = λ A B Ty77 nat77 top77 bot77 arr77 prod sum →
     arr77 (A Ty77 nat77 top77 bot77 arr77 prod sum) (B Ty77 nat77 top77 bot77 arr77 prod sum)

prod77 : Ty77 → Ty77 → Ty77; prod77
 = λ A B Ty77 nat77 top77 bot77 arr77 prod77 sum →
     prod77 (A Ty77 nat77 top77 bot77 arr77 prod77 sum) (B Ty77 nat77 top77 bot77 arr77 prod77 sum)

sum77 : Ty77 → Ty77 → Ty77; sum77
 = λ A B Ty77 nat77 top77 bot77 arr77 prod77 sum77 →
     sum77 (A Ty77 nat77 top77 bot77 arr77 prod77 sum77) (B Ty77 nat77 top77 bot77 arr77 prod77 sum77)

Con77 : Set; Con77
 = (Con77 : Set)
   (nil  : Con77)
   (snoc : Con77 → Ty77 → Con77)
 → Con77

nil77 : Con77; nil77
 = λ Con77 nil77 snoc → nil77

snoc77 : Con77 → Ty77 → Con77; snoc77
 = λ Γ A Con77 nil77 snoc77 → snoc77 (Γ Con77 nil77 snoc77) A

Var77 : Con77 → Ty77 → Set; Var77
 = λ Γ A →
   (Var77 : Con77 → Ty77 → Set)
   (vz  : ∀{Γ A} → Var77 (snoc77 Γ A) A)
   (vs  : ∀{Γ B A} → Var77 Γ A → Var77 (snoc77 Γ B) A)
 → Var77 Γ A

vz77 : ∀{Γ A} → Var77 (snoc77 Γ A) A; vz77
 = λ Var77 vz77 vs → vz77

vs77 : ∀{Γ B A} → Var77 Γ A → Var77 (snoc77 Γ B) A; vs77
 = λ x Var77 vz77 vs77 → vs77 (x Var77 vz77 vs77)

Tm77 : Con77 → Ty77 → Set; Tm77
 = λ Γ A →
   (Tm77  : Con77 → Ty77 → Set)
   (var   : ∀{Γ A} → Var77 Γ A → Tm77 Γ A)
   (lam   : ∀{Γ A B} → Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B))
   (app   : ∀{Γ A B} → Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B)
   (tt    : ∀{Γ} → Tm77 Γ top77)
   (pair  : ∀{Γ A B} → Tm77 Γ A → Tm77 Γ B → Tm77 Γ (prod77 A B))
   (fst   : ∀{Γ A B} → Tm77 Γ (prod77 A B) → Tm77 Γ A)
   (snd   : ∀{Γ A B} → Tm77 Γ (prod77 A B) → Tm77 Γ B)
   (left  : ∀{Γ A B} → Tm77 Γ A → Tm77 Γ (sum77 A B))
   (right : ∀{Γ A B} → Tm77 Γ B → Tm77 Γ (sum77 A B))
   (case  : ∀{Γ A B C} → Tm77 Γ (sum77 A B) → Tm77 Γ (arr77 A C) → Tm77 Γ (arr77 B C) → Tm77 Γ C)
   (zero  : ∀{Γ} → Tm77 Γ nat77)
   (suc   : ∀{Γ} → Tm77 Γ nat77 → Tm77 Γ nat77)
   (rec   : ∀{Γ A} → Tm77 Γ nat77 → Tm77 Γ (arr77 nat77 (arr77 A A)) → Tm77 Γ A → Tm77 Γ A)
 → Tm77 Γ A

var77 : ∀{Γ A} → Var77 Γ A → Tm77 Γ A; var77
 = λ x Tm77 var77 lam app tt pair fst snd left right case zero suc rec →
     var77 x

lam77 : ∀{Γ A B} → Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B); lam77
 = λ t Tm77 var77 lam77 app tt pair fst snd left right case zero suc rec →
     lam77 (t Tm77 var77 lam77 app tt pair fst snd left right case zero suc rec)

app77 : ∀{Γ A B} → Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B; app77
 = λ t u Tm77 var77 lam77 app77 tt pair fst snd left right case zero suc rec →
     app77 (t Tm77 var77 lam77 app77 tt pair fst snd left right case zero suc rec)
         (u Tm77 var77 lam77 app77 tt pair fst snd left right case zero suc rec)

tt77 : ∀{Γ} → Tm77 Γ top77; tt77
 = λ Tm77 var77 lam77 app77 tt77 pair fst snd left right case zero suc rec → tt77

pair77 : ∀{Γ A B} → Tm77 Γ A → Tm77 Γ B → Tm77 Γ (prod77 A B); pair77
 = λ t u Tm77 var77 lam77 app77 tt77 pair77 fst snd left right case zero suc rec →
     pair77 (t Tm77 var77 lam77 app77 tt77 pair77 fst snd left right case zero suc rec)
          (u Tm77 var77 lam77 app77 tt77 pair77 fst snd left right case zero suc rec)

fst77 : ∀{Γ A B} → Tm77 Γ (prod77 A B) → Tm77 Γ A; fst77
 = λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd left right case zero suc rec →
     fst77 (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd left right case zero suc rec)

snd77 : ∀{Γ A B} → Tm77 Γ (prod77 A B) → Tm77 Γ B; snd77
 = λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left right case zero suc rec →
     snd77 (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left right case zero suc rec)

left77 : ∀{Γ A B} → Tm77 Γ A → Tm77 Γ (sum77 A B); left77
 = λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right case zero suc rec →
     left77 (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right case zero suc rec)

right77 : ∀{Γ A B} → Tm77 Γ B → Tm77 Γ (sum77 A B); right77
 = λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case zero suc rec →
     right77 (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case zero suc rec)

case77 : ∀{Γ A B C} → Tm77 Γ (sum77 A B) → Tm77 Γ (arr77 A C) → Tm77 Γ (arr77 B C) → Tm77 Γ C; case77
 = λ t u v Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero suc rec →
     case77 (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero suc rec)
           (u Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero suc rec)
           (v Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero suc rec)

zero77  : ∀{Γ} → Tm77 Γ nat77; zero77
 = λ Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc rec → zero77

suc77 : ∀{Γ} → Tm77 Γ nat77 → Tm77 Γ nat77; suc77
 = λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec →
   suc77 (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec)

rec77 : ∀{Γ A} → Tm77 Γ nat77 → Tm77 Γ (arr77 nat77 (arr77 A A)) → Tm77 Γ A → Tm77 Γ A; rec77
 = λ t u v Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec77 →
     rec77 (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec77)
         (u Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec77)
         (v Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec77)

v077 : ∀{Γ A} → Tm77 (snoc77 Γ A) A; v077
 = var77 vz77

v177 : ∀{Γ A B} → Tm77 (snoc77 (snoc77 Γ A) B) A; v177
 = var77 (vs77 vz77)

v277 : ∀{Γ A B C} → Tm77 (snoc77 (snoc77 (snoc77 Γ A) B) C) A; v277
 = var77 (vs77 (vs77 vz77))

v377 : ∀{Γ A B C D} → Tm77 (snoc77 (snoc77 (snoc77 (snoc77 Γ A) B) C) D) A; v377
 = var77 (vs77 (vs77 (vs77 vz77)))

tbool77 : Ty77; tbool77
 = sum77 top77 top77

true77 : ∀{Γ} → Tm77 Γ tbool77; true77
 = left77 tt77

tfalse77 : ∀{Γ} → Tm77 Γ tbool77; tfalse77
 = right77 tt77

ifthenelse77 : ∀{Γ A} → Tm77 Γ (arr77 tbool77 (arr77 A (arr77 A A))); ifthenelse77
 = lam77 (lam77 (lam77 (case77 v277 (lam77 v277) (lam77 v177))))

times477 : ∀{Γ A} → Tm77 Γ (arr77 (arr77 A A) (arr77 A A)); times477
  = lam77 (lam77 (app77 v177 (app77 v177 (app77 v177 (app77 v177 v077)))))

add77 : ∀{Γ} → Tm77 Γ (arr77 nat77 (arr77 nat77 nat77)); add77
 = lam77 (rec77 v077
       (lam77 (lam77 (lam77 (suc77 (app77 v177 v077)))))
       (lam77 v077))

mul77 : ∀{Γ} → Tm77 Γ (arr77 nat77 (arr77 nat77 nat77)); mul77
 = lam77 (rec77 v077
       (lam77 (lam77 (lam77 (app77 (app77 add77 (app77 v177 v077)) v077))))
       (lam77 zero77))

fact77 : ∀{Γ} → Tm77 Γ (arr77 nat77 nat77); fact77
 = lam77 (rec77 v077 (lam77 (lam77 (app77 (app77 mul77 (suc77 v177)) v077)))
        (suc77 zero77))
{-# OPTIONS --type-in-type #-}

Ty78 : Set
Ty78 =
   (Ty78         : Set)
   (nat top bot  : Ty78)
   (arr prod sum : Ty78 → Ty78 → Ty78)
 → Ty78

nat78 : Ty78; nat78 = λ _ nat78 _ _ _ _ _ → nat78
top78 : Ty78; top78 = λ _ _ top78 _ _ _ _ → top78
bot78 : Ty78; bot78 = λ _ _ _ bot78 _ _ _ → bot78

arr78 : Ty78 → Ty78 → Ty78; arr78
 = λ A B Ty78 nat78 top78 bot78 arr78 prod sum →
     arr78 (A Ty78 nat78 top78 bot78 arr78 prod sum) (B Ty78 nat78 top78 bot78 arr78 prod sum)

prod78 : Ty78 → Ty78 → Ty78; prod78
 = λ A B Ty78 nat78 top78 bot78 arr78 prod78 sum →
     prod78 (A Ty78 nat78 top78 bot78 arr78 prod78 sum) (B Ty78 nat78 top78 bot78 arr78 prod78 sum)

sum78 : Ty78 → Ty78 → Ty78; sum78
 = λ A B Ty78 nat78 top78 bot78 arr78 prod78 sum78 →
     sum78 (A Ty78 nat78 top78 bot78 arr78 prod78 sum78) (B Ty78 nat78 top78 bot78 arr78 prod78 sum78)

Con78 : Set; Con78
 = (Con78 : Set)
   (nil  : Con78)
   (snoc : Con78 → Ty78 → Con78)
 → Con78

nil78 : Con78; nil78
 = λ Con78 nil78 snoc → nil78

snoc78 : Con78 → Ty78 → Con78; snoc78
 = λ Γ A Con78 nil78 snoc78 → snoc78 (Γ Con78 nil78 snoc78) A

Var78 : Con78 → Ty78 → Set; Var78
 = λ Γ A →
   (Var78 : Con78 → Ty78 → Set)
   (vz  : ∀{Γ A} → Var78 (snoc78 Γ A) A)
   (vs  : ∀{Γ B A} → Var78 Γ A → Var78 (snoc78 Γ B) A)
 → Var78 Γ A

vz78 : ∀{Γ A} → Var78 (snoc78 Γ A) A; vz78
 = λ Var78 vz78 vs → vz78

vs78 : ∀{Γ B A} → Var78 Γ A → Var78 (snoc78 Γ B) A; vs78
 = λ x Var78 vz78 vs78 → vs78 (x Var78 vz78 vs78)

Tm78 : Con78 → Ty78 → Set; Tm78
 = λ Γ A →
   (Tm78  : Con78 → Ty78 → Set)
   (var   : ∀{Γ A} → Var78 Γ A → Tm78 Γ A)
   (lam   : ∀{Γ A B} → Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B))
   (app   : ∀{Γ A B} → Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B)
   (tt    : ∀{Γ} → Tm78 Γ top78)
   (pair  : ∀{Γ A B} → Tm78 Γ A → Tm78 Γ B → Tm78 Γ (prod78 A B))
   (fst   : ∀{Γ A B} → Tm78 Γ (prod78 A B) → Tm78 Γ A)
   (snd   : ∀{Γ A B} → Tm78 Γ (prod78 A B) → Tm78 Γ B)
   (left  : ∀{Γ A B} → Tm78 Γ A → Tm78 Γ (sum78 A B))
   (right : ∀{Γ A B} → Tm78 Γ B → Tm78 Γ (sum78 A B))
   (case  : ∀{Γ A B C} → Tm78 Γ (sum78 A B) → Tm78 Γ (arr78 A C) → Tm78 Γ (arr78 B C) → Tm78 Γ C)
   (zero  : ∀{Γ} → Tm78 Γ nat78)
   (suc   : ∀{Γ} → Tm78 Γ nat78 → Tm78 Γ nat78)
   (rec   : ∀{Γ A} → Tm78 Γ nat78 → Tm78 Γ (arr78 nat78 (arr78 A A)) → Tm78 Γ A → Tm78 Γ A)
 → Tm78 Γ A

var78 : ∀{Γ A} → Var78 Γ A → Tm78 Γ A; var78
 = λ x Tm78 var78 lam app tt pair fst snd left right case zero suc rec →
     var78 x

lam78 : ∀{Γ A B} → Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B); lam78
 = λ t Tm78 var78 lam78 app tt pair fst snd left right case zero suc rec →
     lam78 (t Tm78 var78 lam78 app tt pair fst snd left right case zero suc rec)

app78 : ∀{Γ A B} → Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B; app78
 = λ t u Tm78 var78 lam78 app78 tt pair fst snd left right case zero suc rec →
     app78 (t Tm78 var78 lam78 app78 tt pair fst snd left right case zero suc rec)
         (u Tm78 var78 lam78 app78 tt pair fst snd left right case zero suc rec)

tt78 : ∀{Γ} → Tm78 Γ top78; tt78
 = λ Tm78 var78 lam78 app78 tt78 pair fst snd left right case zero suc rec → tt78

pair78 : ∀{Γ A B} → Tm78 Γ A → Tm78 Γ B → Tm78 Γ (prod78 A B); pair78
 = λ t u Tm78 var78 lam78 app78 tt78 pair78 fst snd left right case zero suc rec →
     pair78 (t Tm78 var78 lam78 app78 tt78 pair78 fst snd left right case zero suc rec)
          (u Tm78 var78 lam78 app78 tt78 pair78 fst snd left right case zero suc rec)

fst78 : ∀{Γ A B} → Tm78 Γ (prod78 A B) → Tm78 Γ A; fst78
 = λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd left right case zero suc rec →
     fst78 (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd left right case zero suc rec)

snd78 : ∀{Γ A B} → Tm78 Γ (prod78 A B) → Tm78 Γ B; snd78
 = λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left right case zero suc rec →
     snd78 (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left right case zero suc rec)

left78 : ∀{Γ A B} → Tm78 Γ A → Tm78 Γ (sum78 A B); left78
 = λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right case zero suc rec →
     left78 (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right case zero suc rec)

right78 : ∀{Γ A B} → Tm78 Γ B → Tm78 Γ (sum78 A B); right78
 = λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case zero suc rec →
     right78 (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case zero suc rec)

case78 : ∀{Γ A B C} → Tm78 Γ (sum78 A B) → Tm78 Γ (arr78 A C) → Tm78 Γ (arr78 B C) → Tm78 Γ C; case78
 = λ t u v Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero suc rec →
     case78 (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero suc rec)
           (u Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero suc rec)
           (v Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero suc rec)

zero78  : ∀{Γ} → Tm78 Γ nat78; zero78
 = λ Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc rec → zero78

suc78 : ∀{Γ} → Tm78 Γ nat78 → Tm78 Γ nat78; suc78
 = λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec →
   suc78 (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec)

rec78 : ∀{Γ A} → Tm78 Γ nat78 → Tm78 Γ (arr78 nat78 (arr78 A A)) → Tm78 Γ A → Tm78 Γ A; rec78
 = λ t u v Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec78 →
     rec78 (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec78)
         (u Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec78)
         (v Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec78)

v078 : ∀{Γ A} → Tm78 (snoc78 Γ A) A; v078
 = var78 vz78

v178 : ∀{Γ A B} → Tm78 (snoc78 (snoc78 Γ A) B) A; v178
 = var78 (vs78 vz78)

v278 : ∀{Γ A B C} → Tm78 (snoc78 (snoc78 (snoc78 Γ A) B) C) A; v278
 = var78 (vs78 (vs78 vz78))

v378 : ∀{Γ A B C D} → Tm78 (snoc78 (snoc78 (snoc78 (snoc78 Γ A) B) C) D) A; v378
 = var78 (vs78 (vs78 (vs78 vz78)))

tbool78 : Ty78; tbool78
 = sum78 top78 top78

true78 : ∀{Γ} → Tm78 Γ tbool78; true78
 = left78 tt78

tfalse78 : ∀{Γ} → Tm78 Γ tbool78; tfalse78
 = right78 tt78

ifthenelse78 : ∀{Γ A} → Tm78 Γ (arr78 tbool78 (arr78 A (arr78 A A))); ifthenelse78
 = lam78 (lam78 (lam78 (case78 v278 (lam78 v278) (lam78 v178))))

times478 : ∀{Γ A} → Tm78 Γ (arr78 (arr78 A A) (arr78 A A)); times478
  = lam78 (lam78 (app78 v178 (app78 v178 (app78 v178 (app78 v178 v078)))))

add78 : ∀{Γ} → Tm78 Γ (arr78 nat78 (arr78 nat78 nat78)); add78
 = lam78 (rec78 v078
       (lam78 (lam78 (lam78 (suc78 (app78 v178 v078)))))
       (lam78 v078))

mul78 : ∀{Γ} → Tm78 Γ (arr78 nat78 (arr78 nat78 nat78)); mul78
 = lam78 (rec78 v078
       (lam78 (lam78 (lam78 (app78 (app78 add78 (app78 v178 v078)) v078))))
       (lam78 zero78))

fact78 : ∀{Γ} → Tm78 Γ (arr78 nat78 nat78); fact78
 = lam78 (rec78 v078 (lam78 (lam78 (app78 (app78 mul78 (suc78 v178)) v078)))
        (suc78 zero78))
{-# OPTIONS --type-in-type #-}

Ty79 : Set
Ty79 =
   (Ty79         : Set)
   (nat top bot  : Ty79)
   (arr prod sum : Ty79 → Ty79 → Ty79)
 → Ty79

nat79 : Ty79; nat79 = λ _ nat79 _ _ _ _ _ → nat79
top79 : Ty79; top79 = λ _ _ top79 _ _ _ _ → top79
bot79 : Ty79; bot79 = λ _ _ _ bot79 _ _ _ → bot79

arr79 : Ty79 → Ty79 → Ty79; arr79
 = λ A B Ty79 nat79 top79 bot79 arr79 prod sum →
     arr79 (A Ty79 nat79 top79 bot79 arr79 prod sum) (B Ty79 nat79 top79 bot79 arr79 prod sum)

prod79 : Ty79 → Ty79 → Ty79; prod79
 = λ A B Ty79 nat79 top79 bot79 arr79 prod79 sum →
     prod79 (A Ty79 nat79 top79 bot79 arr79 prod79 sum) (B Ty79 nat79 top79 bot79 arr79 prod79 sum)

sum79 : Ty79 → Ty79 → Ty79; sum79
 = λ A B Ty79 nat79 top79 bot79 arr79 prod79 sum79 →
     sum79 (A Ty79 nat79 top79 bot79 arr79 prod79 sum79) (B Ty79 nat79 top79 bot79 arr79 prod79 sum79)

Con79 : Set; Con79
 = (Con79 : Set)
   (nil  : Con79)
   (snoc : Con79 → Ty79 → Con79)
 → Con79

nil79 : Con79; nil79
 = λ Con79 nil79 snoc → nil79

snoc79 : Con79 → Ty79 → Con79; snoc79
 = λ Γ A Con79 nil79 snoc79 → snoc79 (Γ Con79 nil79 snoc79) A

Var79 : Con79 → Ty79 → Set; Var79
 = λ Γ A →
   (Var79 : Con79 → Ty79 → Set)
   (vz  : ∀{Γ A} → Var79 (snoc79 Γ A) A)
   (vs  : ∀{Γ B A} → Var79 Γ A → Var79 (snoc79 Γ B) A)
 → Var79 Γ A

vz79 : ∀{Γ A} → Var79 (snoc79 Γ A) A; vz79
 = λ Var79 vz79 vs → vz79

vs79 : ∀{Γ B A} → Var79 Γ A → Var79 (snoc79 Γ B) A; vs79
 = λ x Var79 vz79 vs79 → vs79 (x Var79 vz79 vs79)

Tm79 : Con79 → Ty79 → Set; Tm79
 = λ Γ A →
   (Tm79  : Con79 → Ty79 → Set)
   (var   : ∀{Γ A} → Var79 Γ A → Tm79 Γ A)
   (lam   : ∀{Γ A B} → Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B))
   (app   : ∀{Γ A B} → Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B)
   (tt    : ∀{Γ} → Tm79 Γ top79)
   (pair  : ∀{Γ A B} → Tm79 Γ A → Tm79 Γ B → Tm79 Γ (prod79 A B))
   (fst   : ∀{Γ A B} → Tm79 Γ (prod79 A B) → Tm79 Γ A)
   (snd   : ∀{Γ A B} → Tm79 Γ (prod79 A B) → Tm79 Γ B)
   (left  : ∀{Γ A B} → Tm79 Γ A → Tm79 Γ (sum79 A B))
   (right : ∀{Γ A B} → Tm79 Γ B → Tm79 Γ (sum79 A B))
   (case  : ∀{Γ A B C} → Tm79 Γ (sum79 A B) → Tm79 Γ (arr79 A C) → Tm79 Γ (arr79 B C) → Tm79 Γ C)
   (zero  : ∀{Γ} → Tm79 Γ nat79)
   (suc   : ∀{Γ} → Tm79 Γ nat79 → Tm79 Γ nat79)
   (rec   : ∀{Γ A} → Tm79 Γ nat79 → Tm79 Γ (arr79 nat79 (arr79 A A)) → Tm79 Γ A → Tm79 Γ A)
 → Tm79 Γ A

var79 : ∀{Γ A} → Var79 Γ A → Tm79 Γ A; var79
 = λ x Tm79 var79 lam app tt pair fst snd left right case zero suc rec →
     var79 x

lam79 : ∀{Γ A B} → Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B); lam79
 = λ t Tm79 var79 lam79 app tt pair fst snd left right case zero suc rec →
     lam79 (t Tm79 var79 lam79 app tt pair fst snd left right case zero suc rec)

app79 : ∀{Γ A B} → Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B; app79
 = λ t u Tm79 var79 lam79 app79 tt pair fst snd left right case zero suc rec →
     app79 (t Tm79 var79 lam79 app79 tt pair fst snd left right case zero suc rec)
         (u Tm79 var79 lam79 app79 tt pair fst snd left right case zero suc rec)

tt79 : ∀{Γ} → Tm79 Γ top79; tt79
 = λ Tm79 var79 lam79 app79 tt79 pair fst snd left right case zero suc rec → tt79

pair79 : ∀{Γ A B} → Tm79 Γ A → Tm79 Γ B → Tm79 Γ (prod79 A B); pair79
 = λ t u Tm79 var79 lam79 app79 tt79 pair79 fst snd left right case zero suc rec →
     pair79 (t Tm79 var79 lam79 app79 tt79 pair79 fst snd left right case zero suc rec)
          (u Tm79 var79 lam79 app79 tt79 pair79 fst snd left right case zero suc rec)

fst79 : ∀{Γ A B} → Tm79 Γ (prod79 A B) → Tm79 Γ A; fst79
 = λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd left right case zero suc rec →
     fst79 (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd left right case zero suc rec)

snd79 : ∀{Γ A B} → Tm79 Γ (prod79 A B) → Tm79 Γ B; snd79
 = λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left right case zero suc rec →
     snd79 (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left right case zero suc rec)

left79 : ∀{Γ A B} → Tm79 Γ A → Tm79 Γ (sum79 A B); left79
 = λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right case zero suc rec →
     left79 (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right case zero suc rec)

right79 : ∀{Γ A B} → Tm79 Γ B → Tm79 Γ (sum79 A B); right79
 = λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case zero suc rec →
     right79 (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case zero suc rec)

case79 : ∀{Γ A B C} → Tm79 Γ (sum79 A B) → Tm79 Γ (arr79 A C) → Tm79 Γ (arr79 B C) → Tm79 Γ C; case79
 = λ t u v Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero suc rec →
     case79 (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero suc rec)
           (u Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero suc rec)
           (v Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero suc rec)

zero79  : ∀{Γ} → Tm79 Γ nat79; zero79
 = λ Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc rec → zero79

suc79 : ∀{Γ} → Tm79 Γ nat79 → Tm79 Γ nat79; suc79
 = λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec →
   suc79 (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec)

rec79 : ∀{Γ A} → Tm79 Γ nat79 → Tm79 Γ (arr79 nat79 (arr79 A A)) → Tm79 Γ A → Tm79 Γ A; rec79
 = λ t u v Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec79 →
     rec79 (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec79)
         (u Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec79)
         (v Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec79)

v079 : ∀{Γ A} → Tm79 (snoc79 Γ A) A; v079
 = var79 vz79

v179 : ∀{Γ A B} → Tm79 (snoc79 (snoc79 Γ A) B) A; v179
 = var79 (vs79 vz79)

v279 : ∀{Γ A B C} → Tm79 (snoc79 (snoc79 (snoc79 Γ A) B) C) A; v279
 = var79 (vs79 (vs79 vz79))

v379 : ∀{Γ A B C D} → Tm79 (snoc79 (snoc79 (snoc79 (snoc79 Γ A) B) C) D) A; v379
 = var79 (vs79 (vs79 (vs79 vz79)))

tbool79 : Ty79; tbool79
 = sum79 top79 top79

true79 : ∀{Γ} → Tm79 Γ tbool79; true79
 = left79 tt79

tfalse79 : ∀{Γ} → Tm79 Γ tbool79; tfalse79
 = right79 tt79

ifthenelse79 : ∀{Γ A} → Tm79 Γ (arr79 tbool79 (arr79 A (arr79 A A))); ifthenelse79
 = lam79 (lam79 (lam79 (case79 v279 (lam79 v279) (lam79 v179))))

times479 : ∀{Γ A} → Tm79 Γ (arr79 (arr79 A A) (arr79 A A)); times479
  = lam79 (lam79 (app79 v179 (app79 v179 (app79 v179 (app79 v179 v079)))))

add79 : ∀{Γ} → Tm79 Γ (arr79 nat79 (arr79 nat79 nat79)); add79
 = lam79 (rec79 v079
       (lam79 (lam79 (lam79 (suc79 (app79 v179 v079)))))
       (lam79 v079))

mul79 : ∀{Γ} → Tm79 Γ (arr79 nat79 (arr79 nat79 nat79)); mul79
 = lam79 (rec79 v079
       (lam79 (lam79 (lam79 (app79 (app79 add79 (app79 v179 v079)) v079))))
       (lam79 zero79))

fact79 : ∀{Γ} → Tm79 Γ (arr79 nat79 nat79); fact79
 = lam79 (rec79 v079 (lam79 (lam79 (app79 (app79 mul79 (suc79 v179)) v079)))
        (suc79 zero79))
