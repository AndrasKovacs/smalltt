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
   (vz  : ∀ Γ A → Var (snoc Γ A) A)
   (vs  : ∀ Γ B A → Var Γ A → Var (snoc Γ B) A)
 → Var Γ A

vz : ∀{Γ A} → Var (snoc Γ A) A; vz
 = λ Var vz vs → vz _ _

vs : ∀{Γ B A} → Var Γ A → Var (snoc Γ B) A; vs
 = λ x Var vz vs → vs _ _ _ (x Var vz vs)

Tm : Con → Ty → Set; Tm
 = λ Γ A →
   (Tm  : Con → Ty → Set)
   (var   : ∀ Γ A      → Var Γ A → Tm Γ A)
   (lam   : ∀ Γ A B    → Tm (snoc Γ A) B → Tm Γ (arr A B))
   (app   : ∀ Γ A B    → Tm Γ (arr A B) → Tm Γ A → Tm Γ B)
   (tt    : ∀ Γ        → Tm Γ top)
   (pair  : ∀ Γ A B    → Tm Γ A → Tm Γ B → Tm Γ (prod A B))
   (fst   : ∀ Γ A B    → Tm Γ (prod A B) → Tm Γ A)
   (snd   : ∀ Γ A B    → Tm Γ (prod A B) → Tm Γ B)
   (left  : ∀ Γ A B    → Tm Γ A → Tm Γ (sum A B))
   (right : ∀ Γ A B    → Tm Γ B → Tm Γ (sum A B))
   (case  : ∀ Γ A B C  → Tm Γ (sum A B) → Tm Γ (arr A C) → Tm Γ (arr B C) → Tm Γ C)
   (zero  : ∀ Γ        → Tm Γ nat)
   (suc   : ∀ Γ        → Tm Γ nat → Tm Γ nat)
   (rec   : ∀ Γ A      → Tm Γ nat → Tm Γ (arr nat (arr A A)) → Tm Γ A → Tm Γ A)
 → Tm Γ A

var : ∀{Γ A} → Var Γ A → Tm Γ A; var
 = λ x Tm var lam app tt pair fst snd left right case zero suc rec →
     var _ _ x

lam : ∀{Γ A B} → Tm (snoc Γ A) B → Tm Γ (arr A B); lam
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     lam _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec)

app : ∀{Γ A B} → Tm Γ (arr A B) → Tm Γ A → Tm Γ B; app
 = λ t u Tm var lam app tt pair fst snd left right case zero suc rec →
     app _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec)

tt : ∀{Γ} → Tm Γ top; tt
 = λ Tm var lam app tt pair fst snd left right case zero suc rec → tt _

pair : ∀{Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (prod A B); pair
 = λ t u Tm var lam app tt pair fst snd left right case zero suc rec →
     pair _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec)
          (u Tm var lam app tt pair fst snd left right case zero suc rec)

fst : ∀{Γ A B} → Tm Γ (prod A B) → Tm Γ A; fst
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     fst _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec)

snd : ∀{Γ A B} → Tm Γ (prod A B) → Tm Γ B; snd
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     snd _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec)

left : ∀{Γ A B} → Tm Γ A → Tm Γ (sum A B); left
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     left _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec)

right : ∀{Γ A B} → Tm Γ B → Tm Γ (sum A B); right
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
     right _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec)

case : ∀{Γ A B C} → Tm Γ (sum A B) → Tm Γ (arr A C) → Tm Γ (arr B C) → Tm Γ C; case
 = λ t u v Tm var lam app tt pair fst snd left right case zero suc rec →
     case _ _ _ _
           (t Tm var lam app tt pair fst snd left right case zero suc rec)
           (u Tm var lam app tt pair fst snd left right case zero suc rec)
           (v Tm var lam app tt pair fst snd left right case zero suc rec)

zero  : ∀{Γ} → Tm Γ nat; zero
 = λ Tm var lam app tt pair fst snd left right case zero suc rec → zero _

suc : ∀{Γ} → Tm Γ nat → Tm Γ nat; suc
 = λ t Tm var lam app tt pair fst snd left right case zero suc rec →
   suc _ (t Tm var lam app tt pair fst snd left right case zero suc rec)

rec : ∀{Γ A} → Tm Γ nat → Tm Γ (arr nat (arr A A)) → Tm Γ A → Tm Γ A; rec
 = λ t u v Tm var lam app tt pair fst snd left right case zero suc rec →
     rec _ _
          (t Tm var lam app tt pair fst snd left right case zero suc rec)
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
   (vz  : ∀ Γ A → Var1 (snoc1 Γ A) A)
   (vs  : ∀ Γ B A → Var1 Γ A → Var1 (snoc1 Γ B) A)
 → Var1 Γ A

vz1 : ∀{Γ A} → Var1 (snoc1 Γ A) A; vz1
 = λ Var1 vz1 vs → vz1 _ _

vs1 : ∀{Γ B A} → Var1 Γ A → Var1 (snoc1 Γ B) A; vs1
 = λ x Var1 vz1 vs1 → vs1 _ _ _ (x Var1 vz1 vs1)

Tm1 : Con1 → Ty1 → Set; Tm1
 = λ Γ A →
   (Tm1  : Con1 → Ty1 → Set)
   (var   : ∀ Γ A      → Var1 Γ A → Tm1 Γ A)
   (lam   : ∀ Γ A B    → Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B))
   (app   : ∀ Γ A B    → Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B)
   (tt    : ∀ Γ        → Tm1 Γ top1)
   (pair  : ∀ Γ A B    → Tm1 Γ A → Tm1 Γ B → Tm1 Γ (prod1 A B))
   (fst   : ∀ Γ A B    → Tm1 Γ (prod1 A B) → Tm1 Γ A)
   (snd   : ∀ Γ A B    → Tm1 Γ (prod1 A B) → Tm1 Γ B)
   (left  : ∀ Γ A B    → Tm1 Γ A → Tm1 Γ (sum1 A B))
   (right : ∀ Γ A B    → Tm1 Γ B → Tm1 Γ (sum1 A B))
   (case  : ∀ Γ A B C  → Tm1 Γ (sum1 A B) → Tm1 Γ (arr1 A C) → Tm1 Γ (arr1 B C) → Tm1 Γ C)
   (zero  : ∀ Γ        → Tm1 Γ nat1)
   (suc   : ∀ Γ        → Tm1 Γ nat1 → Tm1 Γ nat1)
   (rec   : ∀ Γ A      → Tm1 Γ nat1 → Tm1 Γ (arr1 nat1 (arr1 A A)) → Tm1 Γ A → Tm1 Γ A)
 → Tm1 Γ A

var1 : ∀{Γ A} → Var1 Γ A → Tm1 Γ A; var1
 = λ x Tm1 var1 lam app tt pair fst snd left right case zero suc rec →
     var1 _ _ x

lam1 : ∀{Γ A B} → Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B); lam1
 = λ t Tm1 var1 lam1 app tt pair fst snd left right case zero suc rec →
     lam1 _ _ _ (t Tm1 var1 lam1 app tt pair fst snd left right case zero suc rec)

app1 : ∀{Γ A B} → Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B; app1
 = λ t u Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec →
     app1 _ _ _ (t Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec)
         (u Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec)

tt1 : ∀{Γ} → Tm1 Γ top1; tt1
 = λ Tm1 var1 lam1 app1 tt1 pair fst snd left right case zero suc rec → tt1 _

pair1 : ∀{Γ A B} → Tm1 Γ A → Tm1 Γ B → Tm1 Γ (prod1 A B); pair1
 = λ t u Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec →
     pair1 _ _ _ (t Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec)
          (u Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec)

fst1 : ∀{Γ A B} → Tm1 Γ (prod1 A B) → Tm1 Γ A; fst1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd left right case zero suc rec →
     fst1 _ _ _ (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd left right case zero suc rec)

snd1 : ∀{Γ A B} → Tm1 Γ (prod1 A B) → Tm1 Γ B; snd1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left right case zero suc rec →
     snd1 _ _ _ (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left right case zero suc rec)

left1 : ∀{Γ A B} → Tm1 Γ A → Tm1 Γ (sum1 A B); left1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right case zero suc rec →
     left1 _ _ _ (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right case zero suc rec)

right1 : ∀{Γ A B} → Tm1 Γ B → Tm1 Γ (sum1 A B); right1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case zero suc rec →
     right1 _ _ _ (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case zero suc rec)

case1 : ∀{Γ A B C} → Tm1 Γ (sum1 A B) → Tm1 Γ (arr1 A C) → Tm1 Γ (arr1 B C) → Tm1 Γ C; case1
 = λ t u v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec →
     case1 _ _ _ _
           (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)
           (u Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)
           (v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)

zero1  : ∀{Γ} → Tm1 Γ nat1; zero1
 = λ Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc rec → zero1 _

suc1 : ∀{Γ} → Tm1 Γ nat1 → Tm1 Γ nat1; suc1
 = λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec →
   suc1 _ (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec)

rec1 : ∀{Γ A} → Tm1 Γ nat1 → Tm1 Γ (arr1 nat1 (arr1 A A)) → Tm1 Γ A → Tm1 Γ A; rec1
 = λ t u v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1 →
     rec1 _ _
          (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)
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
   (vz  : ∀ Γ A → Var2 (snoc2 Γ A) A)
   (vs  : ∀ Γ B A → Var2 Γ A → Var2 (snoc2 Γ B) A)
 → Var2 Γ A

vz2 : ∀{Γ A} → Var2 (snoc2 Γ A) A; vz2
 = λ Var2 vz2 vs → vz2 _ _

vs2 : ∀{Γ B A} → Var2 Γ A → Var2 (snoc2 Γ B) A; vs2
 = λ x Var2 vz2 vs2 → vs2 _ _ _ (x Var2 vz2 vs2)

Tm2 : Con2 → Ty2 → Set; Tm2
 = λ Γ A →
   (Tm2  : Con2 → Ty2 → Set)
   (var   : ∀ Γ A      → Var2 Γ A → Tm2 Γ A)
   (lam   : ∀ Γ A B    → Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B))
   (app   : ∀ Γ A B    → Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B)
   (tt    : ∀ Γ        → Tm2 Γ top2)
   (pair  : ∀ Γ A B    → Tm2 Γ A → Tm2 Γ B → Tm2 Γ (prod2 A B))
   (fst   : ∀ Γ A B    → Tm2 Γ (prod2 A B) → Tm2 Γ A)
   (snd   : ∀ Γ A B    → Tm2 Γ (prod2 A B) → Tm2 Γ B)
   (left  : ∀ Γ A B    → Tm2 Γ A → Tm2 Γ (sum2 A B))
   (right : ∀ Γ A B    → Tm2 Γ B → Tm2 Γ (sum2 A B))
   (case  : ∀ Γ A B C  → Tm2 Γ (sum2 A B) → Tm2 Γ (arr2 A C) → Tm2 Γ (arr2 B C) → Tm2 Γ C)
   (zero  : ∀ Γ        → Tm2 Γ nat2)
   (suc   : ∀ Γ        → Tm2 Γ nat2 → Tm2 Γ nat2)
   (rec   : ∀ Γ A      → Tm2 Γ nat2 → Tm2 Γ (arr2 nat2 (arr2 A A)) → Tm2 Γ A → Tm2 Γ A)
 → Tm2 Γ A

var2 : ∀{Γ A} → Var2 Γ A → Tm2 Γ A; var2
 = λ x Tm2 var2 lam app tt pair fst snd left right case zero suc rec →
     var2 _ _ x

lam2 : ∀{Γ A B} → Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B); lam2
 = λ t Tm2 var2 lam2 app tt pair fst snd left right case zero suc rec →
     lam2 _ _ _ (t Tm2 var2 lam2 app tt pair fst snd left right case zero suc rec)

app2 : ∀{Γ A B} → Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B; app2
 = λ t u Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec →
     app2 _ _ _ (t Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec)
         (u Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec)

tt2 : ∀{Γ} → Tm2 Γ top2; tt2
 = λ Tm2 var2 lam2 app2 tt2 pair fst snd left right case zero suc rec → tt2 _

pair2 : ∀{Γ A B} → Tm2 Γ A → Tm2 Γ B → Tm2 Γ (prod2 A B); pair2
 = λ t u Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec →
     pair2 _ _ _ (t Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec)
          (u Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec)

fst2 : ∀{Γ A B} → Tm2 Γ (prod2 A B) → Tm2 Γ A; fst2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd left right case zero suc rec →
     fst2 _ _ _ (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd left right case zero suc rec)

snd2 : ∀{Γ A B} → Tm2 Γ (prod2 A B) → Tm2 Γ B; snd2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left right case zero suc rec →
     snd2 _ _ _ (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left right case zero suc rec)

left2 : ∀{Γ A B} → Tm2 Γ A → Tm2 Γ (sum2 A B); left2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right case zero suc rec →
     left2 _ _ _ (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right case zero suc rec)

right2 : ∀{Γ A B} → Tm2 Γ B → Tm2 Γ (sum2 A B); right2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case zero suc rec →
     right2 _ _ _ (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case zero suc rec)

case2 : ∀{Γ A B C} → Tm2 Γ (sum2 A B) → Tm2 Γ (arr2 A C) → Tm2 Γ (arr2 B C) → Tm2 Γ C; case2
 = λ t u v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec →
     case2 _ _ _ _
           (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)
           (u Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)
           (v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)

zero2  : ∀{Γ} → Tm2 Γ nat2; zero2
 = λ Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc rec → zero2 _

suc2 : ∀{Γ} → Tm2 Γ nat2 → Tm2 Γ nat2; suc2
 = λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec →
   suc2 _ (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec)

rec2 : ∀{Γ A} → Tm2 Γ nat2 → Tm2 Γ (arr2 nat2 (arr2 A A)) → Tm2 Γ A → Tm2 Γ A; rec2
 = λ t u v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2 →
     rec2 _ _
          (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)
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
   (vz  : ∀ Γ A → Var3 (snoc3 Γ A) A)
   (vs  : ∀ Γ B A → Var3 Γ A → Var3 (snoc3 Γ B) A)
 → Var3 Γ A

vz3 : ∀{Γ A} → Var3 (snoc3 Γ A) A; vz3
 = λ Var3 vz3 vs → vz3 _ _

vs3 : ∀{Γ B A} → Var3 Γ A → Var3 (snoc3 Γ B) A; vs3
 = λ x Var3 vz3 vs3 → vs3 _ _ _ (x Var3 vz3 vs3)

Tm3 : Con3 → Ty3 → Set; Tm3
 = λ Γ A →
   (Tm3  : Con3 → Ty3 → Set)
   (var   : ∀ Γ A      → Var3 Γ A → Tm3 Γ A)
   (lam   : ∀ Γ A B    → Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B))
   (app   : ∀ Γ A B    → Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B)
   (tt    : ∀ Γ        → Tm3 Γ top3)
   (pair  : ∀ Γ A B    → Tm3 Γ A → Tm3 Γ B → Tm3 Γ (prod3 A B))
   (fst   : ∀ Γ A B    → Tm3 Γ (prod3 A B) → Tm3 Γ A)
   (snd   : ∀ Γ A B    → Tm3 Γ (prod3 A B) → Tm3 Γ B)
   (left  : ∀ Γ A B    → Tm3 Γ A → Tm3 Γ (sum3 A B))
   (right : ∀ Γ A B    → Tm3 Γ B → Tm3 Γ (sum3 A B))
   (case  : ∀ Γ A B C  → Tm3 Γ (sum3 A B) → Tm3 Γ (arr3 A C) → Tm3 Γ (arr3 B C) → Tm3 Γ C)
   (zero  : ∀ Γ        → Tm3 Γ nat3)
   (suc   : ∀ Γ        → Tm3 Γ nat3 → Tm3 Γ nat3)
   (rec   : ∀ Γ A      → Tm3 Γ nat3 → Tm3 Γ (arr3 nat3 (arr3 A A)) → Tm3 Γ A → Tm3 Γ A)
 → Tm3 Γ A

var3 : ∀{Γ A} → Var3 Γ A → Tm3 Γ A; var3
 = λ x Tm3 var3 lam app tt pair fst snd left right case zero suc rec →
     var3 _ _ x

lam3 : ∀{Γ A B} → Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B); lam3
 = λ t Tm3 var3 lam3 app tt pair fst snd left right case zero suc rec →
     lam3 _ _ _ (t Tm3 var3 lam3 app tt pair fst snd left right case zero suc rec)

app3 : ∀{Γ A B} → Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B; app3
 = λ t u Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec →
     app3 _ _ _ (t Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec)
         (u Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec)

tt3 : ∀{Γ} → Tm3 Γ top3; tt3
 = λ Tm3 var3 lam3 app3 tt3 pair fst snd left right case zero suc rec → tt3 _

pair3 : ∀{Γ A B} → Tm3 Γ A → Tm3 Γ B → Tm3 Γ (prod3 A B); pair3
 = λ t u Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec →
     pair3 _ _ _ (t Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec)
          (u Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec)

fst3 : ∀{Γ A B} → Tm3 Γ (prod3 A B) → Tm3 Γ A; fst3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd left right case zero suc rec →
     fst3 _ _ _ (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd left right case zero suc rec)

snd3 : ∀{Γ A B} → Tm3 Γ (prod3 A B) → Tm3 Γ B; snd3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left right case zero suc rec →
     snd3 _ _ _ (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left right case zero suc rec)

left3 : ∀{Γ A B} → Tm3 Γ A → Tm3 Γ (sum3 A B); left3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right case zero suc rec →
     left3 _ _ _ (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right case zero suc rec)

right3 : ∀{Γ A B} → Tm3 Γ B → Tm3 Γ (sum3 A B); right3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case zero suc rec →
     right3 _ _ _ (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case zero suc rec)

case3 : ∀{Γ A B C} → Tm3 Γ (sum3 A B) → Tm3 Γ (arr3 A C) → Tm3 Γ (arr3 B C) → Tm3 Γ C; case3
 = λ t u v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec →
     case3 _ _ _ _
           (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)
           (u Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)
           (v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)

zero3  : ∀{Γ} → Tm3 Γ nat3; zero3
 = λ Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc rec → zero3 _

suc3 : ∀{Γ} → Tm3 Γ nat3 → Tm3 Γ nat3; suc3
 = λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec →
   suc3 _ (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec)

rec3 : ∀{Γ A} → Tm3 Γ nat3 → Tm3 Γ (arr3 nat3 (arr3 A A)) → Tm3 Γ A → Tm3 Γ A; rec3
 = λ t u v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3 →
     rec3 _ _
          (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)
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
   (vz  : ∀ Γ A → Var4 (snoc4 Γ A) A)
   (vs  : ∀ Γ B A → Var4 Γ A → Var4 (snoc4 Γ B) A)
 → Var4 Γ A

vz4 : ∀{Γ A} → Var4 (snoc4 Γ A) A; vz4
 = λ Var4 vz4 vs → vz4 _ _

vs4 : ∀{Γ B A} → Var4 Γ A → Var4 (snoc4 Γ B) A; vs4
 = λ x Var4 vz4 vs4 → vs4 _ _ _ (x Var4 vz4 vs4)

Tm4 : Con4 → Ty4 → Set; Tm4
 = λ Γ A →
   (Tm4  : Con4 → Ty4 → Set)
   (var   : ∀ Γ A      → Var4 Γ A → Tm4 Γ A)
   (lam   : ∀ Γ A B    → Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B))
   (app   : ∀ Γ A B    → Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B)
   (tt    : ∀ Γ        → Tm4 Γ top4)
   (pair  : ∀ Γ A B    → Tm4 Γ A → Tm4 Γ B → Tm4 Γ (prod4 A B))
   (fst   : ∀ Γ A B    → Tm4 Γ (prod4 A B) → Tm4 Γ A)
   (snd   : ∀ Γ A B    → Tm4 Γ (prod4 A B) → Tm4 Γ B)
   (left  : ∀ Γ A B    → Tm4 Γ A → Tm4 Γ (sum4 A B))
   (right : ∀ Γ A B    → Tm4 Γ B → Tm4 Γ (sum4 A B))
   (case  : ∀ Γ A B C  → Tm4 Γ (sum4 A B) → Tm4 Γ (arr4 A C) → Tm4 Γ (arr4 B C) → Tm4 Γ C)
   (zero  : ∀ Γ        → Tm4 Γ nat4)
   (suc   : ∀ Γ        → Tm4 Γ nat4 → Tm4 Γ nat4)
   (rec   : ∀ Γ A      → Tm4 Γ nat4 → Tm4 Γ (arr4 nat4 (arr4 A A)) → Tm4 Γ A → Tm4 Γ A)
 → Tm4 Γ A

var4 : ∀{Γ A} → Var4 Γ A → Tm4 Γ A; var4
 = λ x Tm4 var4 lam app tt pair fst snd left right case zero suc rec →
     var4 _ _ x

lam4 : ∀{Γ A B} → Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B); lam4
 = λ t Tm4 var4 lam4 app tt pair fst snd left right case zero suc rec →
     lam4 _ _ _ (t Tm4 var4 lam4 app tt pair fst snd left right case zero suc rec)

app4 : ∀{Γ A B} → Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B; app4
 = λ t u Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec →
     app4 _ _ _ (t Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec)
         (u Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec)

tt4 : ∀{Γ} → Tm4 Γ top4; tt4
 = λ Tm4 var4 lam4 app4 tt4 pair fst snd left right case zero suc rec → tt4 _

pair4 : ∀{Γ A B} → Tm4 Γ A → Tm4 Γ B → Tm4 Γ (prod4 A B); pair4
 = λ t u Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec →
     pair4 _ _ _ (t Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec)
          (u Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec)

fst4 : ∀{Γ A B} → Tm4 Γ (prod4 A B) → Tm4 Γ A; fst4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd left right case zero suc rec →
     fst4 _ _ _ (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd left right case zero suc rec)

snd4 : ∀{Γ A B} → Tm4 Γ (prod4 A B) → Tm4 Γ B; snd4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left right case zero suc rec →
     snd4 _ _ _ (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left right case zero suc rec)

left4 : ∀{Γ A B} → Tm4 Γ A → Tm4 Γ (sum4 A B); left4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right case zero suc rec →
     left4 _ _ _ (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right case zero suc rec)

right4 : ∀{Γ A B} → Tm4 Γ B → Tm4 Γ (sum4 A B); right4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case zero suc rec →
     right4 _ _ _ (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case zero suc rec)

case4 : ∀{Γ A B C} → Tm4 Γ (sum4 A B) → Tm4 Γ (arr4 A C) → Tm4 Γ (arr4 B C) → Tm4 Γ C; case4
 = λ t u v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec →
     case4 _ _ _ _
           (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)
           (u Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)
           (v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)

zero4  : ∀{Γ} → Tm4 Γ nat4; zero4
 = λ Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc rec → zero4 _

suc4 : ∀{Γ} → Tm4 Γ nat4 → Tm4 Γ nat4; suc4
 = λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec →
   suc4 _ (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec)

rec4 : ∀{Γ A} → Tm4 Γ nat4 → Tm4 Γ (arr4 nat4 (arr4 A A)) → Tm4 Γ A → Tm4 Γ A; rec4
 = λ t u v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4 →
     rec4 _ _
          (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)
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
   (vz  : ∀ Γ A → Var5 (snoc5 Γ A) A)
   (vs  : ∀ Γ B A → Var5 Γ A → Var5 (snoc5 Γ B) A)
 → Var5 Γ A

vz5 : ∀{Γ A} → Var5 (snoc5 Γ A) A; vz5
 = λ Var5 vz5 vs → vz5 _ _

vs5 : ∀{Γ B A} → Var5 Γ A → Var5 (snoc5 Γ B) A; vs5
 = λ x Var5 vz5 vs5 → vs5 _ _ _ (x Var5 vz5 vs5)

Tm5 : Con5 → Ty5 → Set; Tm5
 = λ Γ A →
   (Tm5  : Con5 → Ty5 → Set)
   (var   : ∀ Γ A      → Var5 Γ A → Tm5 Γ A)
   (lam   : ∀ Γ A B    → Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B))
   (app   : ∀ Γ A B    → Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B)
   (tt    : ∀ Γ        → Tm5 Γ top5)
   (pair  : ∀ Γ A B    → Tm5 Γ A → Tm5 Γ B → Tm5 Γ (prod5 A B))
   (fst   : ∀ Γ A B    → Tm5 Γ (prod5 A B) → Tm5 Γ A)
   (snd   : ∀ Γ A B    → Tm5 Γ (prod5 A B) → Tm5 Γ B)
   (left  : ∀ Γ A B    → Tm5 Γ A → Tm5 Γ (sum5 A B))
   (right : ∀ Γ A B    → Tm5 Γ B → Tm5 Γ (sum5 A B))
   (case  : ∀ Γ A B C  → Tm5 Γ (sum5 A B) → Tm5 Γ (arr5 A C) → Tm5 Γ (arr5 B C) → Tm5 Γ C)
   (zero  : ∀ Γ        → Tm5 Γ nat5)
   (suc   : ∀ Γ        → Tm5 Γ nat5 → Tm5 Γ nat5)
   (rec   : ∀ Γ A      → Tm5 Γ nat5 → Tm5 Γ (arr5 nat5 (arr5 A A)) → Tm5 Γ A → Tm5 Γ A)
 → Tm5 Γ A

var5 : ∀{Γ A} → Var5 Γ A → Tm5 Γ A; var5
 = λ x Tm5 var5 lam app tt pair fst snd left right case zero suc rec →
     var5 _ _ x

lam5 : ∀{Γ A B} → Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B); lam5
 = λ t Tm5 var5 lam5 app tt pair fst snd left right case zero suc rec →
     lam5 _ _ _ (t Tm5 var5 lam5 app tt pair fst snd left right case zero suc rec)

app5 : ∀{Γ A B} → Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B; app5
 = λ t u Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec →
     app5 _ _ _ (t Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec)
         (u Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec)

tt5 : ∀{Γ} → Tm5 Γ top5; tt5
 = λ Tm5 var5 lam5 app5 tt5 pair fst snd left right case zero suc rec → tt5 _

pair5 : ∀{Γ A B} → Tm5 Γ A → Tm5 Γ B → Tm5 Γ (prod5 A B); pair5
 = λ t u Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec →
     pair5 _ _ _ (t Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec)
          (u Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec)

fst5 : ∀{Γ A B} → Tm5 Γ (prod5 A B) → Tm5 Γ A; fst5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd left right case zero suc rec →
     fst5 _ _ _ (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd left right case zero suc rec)

snd5 : ∀{Γ A B} → Tm5 Γ (prod5 A B) → Tm5 Γ B; snd5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left right case zero suc rec →
     snd5 _ _ _ (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left right case zero suc rec)

left5 : ∀{Γ A B} → Tm5 Γ A → Tm5 Γ (sum5 A B); left5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right case zero suc rec →
     left5 _ _ _ (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right case zero suc rec)

right5 : ∀{Γ A B} → Tm5 Γ B → Tm5 Γ (sum5 A B); right5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case zero suc rec →
     right5 _ _ _ (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case zero suc rec)

case5 : ∀{Γ A B C} → Tm5 Γ (sum5 A B) → Tm5 Γ (arr5 A C) → Tm5 Γ (arr5 B C) → Tm5 Γ C; case5
 = λ t u v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec →
     case5 _ _ _ _
           (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)
           (u Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)
           (v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)

zero5  : ∀{Γ} → Tm5 Γ nat5; zero5
 = λ Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc rec → zero5 _

suc5 : ∀{Γ} → Tm5 Γ nat5 → Tm5 Γ nat5; suc5
 = λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec →
   suc5 _ (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec)

rec5 : ∀{Γ A} → Tm5 Γ nat5 → Tm5 Γ (arr5 nat5 (arr5 A A)) → Tm5 Γ A → Tm5 Γ A; rec5
 = λ t u v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5 →
     rec5 _ _
          (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)
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
   (vz  : ∀ Γ A → Var6 (snoc6 Γ A) A)
   (vs  : ∀ Γ B A → Var6 Γ A → Var6 (snoc6 Γ B) A)
 → Var6 Γ A

vz6 : ∀{Γ A} → Var6 (snoc6 Γ A) A; vz6
 = λ Var6 vz6 vs → vz6 _ _

vs6 : ∀{Γ B A} → Var6 Γ A → Var6 (snoc6 Γ B) A; vs6
 = λ x Var6 vz6 vs6 → vs6 _ _ _ (x Var6 vz6 vs6)

Tm6 : Con6 → Ty6 → Set; Tm6
 = λ Γ A →
   (Tm6  : Con6 → Ty6 → Set)
   (var   : ∀ Γ A      → Var6 Γ A → Tm6 Γ A)
   (lam   : ∀ Γ A B    → Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B))
   (app   : ∀ Γ A B    → Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B)
   (tt    : ∀ Γ        → Tm6 Γ top6)
   (pair  : ∀ Γ A B    → Tm6 Γ A → Tm6 Γ B → Tm6 Γ (prod6 A B))
   (fst   : ∀ Γ A B    → Tm6 Γ (prod6 A B) → Tm6 Γ A)
   (snd   : ∀ Γ A B    → Tm6 Γ (prod6 A B) → Tm6 Γ B)
   (left  : ∀ Γ A B    → Tm6 Γ A → Tm6 Γ (sum6 A B))
   (right : ∀ Γ A B    → Tm6 Γ B → Tm6 Γ (sum6 A B))
   (case  : ∀ Γ A B C  → Tm6 Γ (sum6 A B) → Tm6 Γ (arr6 A C) → Tm6 Γ (arr6 B C) → Tm6 Γ C)
   (zero  : ∀ Γ        → Tm6 Γ nat6)
   (suc   : ∀ Γ        → Tm6 Γ nat6 → Tm6 Γ nat6)
   (rec   : ∀ Γ A      → Tm6 Γ nat6 → Tm6 Γ (arr6 nat6 (arr6 A A)) → Tm6 Γ A → Tm6 Γ A)
 → Tm6 Γ A

var6 : ∀{Γ A} → Var6 Γ A → Tm6 Γ A; var6
 = λ x Tm6 var6 lam app tt pair fst snd left right case zero suc rec →
     var6 _ _ x

lam6 : ∀{Γ A B} → Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B); lam6
 = λ t Tm6 var6 lam6 app tt pair fst snd left right case zero suc rec →
     lam6 _ _ _ (t Tm6 var6 lam6 app tt pair fst snd left right case zero suc rec)

app6 : ∀{Γ A B} → Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B; app6
 = λ t u Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec →
     app6 _ _ _ (t Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec)
         (u Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec)

tt6 : ∀{Γ} → Tm6 Γ top6; tt6
 = λ Tm6 var6 lam6 app6 tt6 pair fst snd left right case zero suc rec → tt6 _

pair6 : ∀{Γ A B} → Tm6 Γ A → Tm6 Γ B → Tm6 Γ (prod6 A B); pair6
 = λ t u Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec →
     pair6 _ _ _ (t Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec)
          (u Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec)

fst6 : ∀{Γ A B} → Tm6 Γ (prod6 A B) → Tm6 Γ A; fst6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd left right case zero suc rec →
     fst6 _ _ _ (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd left right case zero suc rec)

snd6 : ∀{Γ A B} → Tm6 Γ (prod6 A B) → Tm6 Γ B; snd6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left right case zero suc rec →
     snd6 _ _ _ (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left right case zero suc rec)

left6 : ∀{Γ A B} → Tm6 Γ A → Tm6 Γ (sum6 A B); left6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right case zero suc rec →
     left6 _ _ _ (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right case zero suc rec)

right6 : ∀{Γ A B} → Tm6 Γ B → Tm6 Γ (sum6 A B); right6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case zero suc rec →
     right6 _ _ _ (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case zero suc rec)

case6 : ∀{Γ A B C} → Tm6 Γ (sum6 A B) → Tm6 Γ (arr6 A C) → Tm6 Γ (arr6 B C) → Tm6 Γ C; case6
 = λ t u v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec →
     case6 _ _ _ _
           (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)
           (u Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)
           (v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)

zero6  : ∀{Γ} → Tm6 Γ nat6; zero6
 = λ Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc rec → zero6 _

suc6 : ∀{Γ} → Tm6 Γ nat6 → Tm6 Γ nat6; suc6
 = λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec →
   suc6 _ (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec)

rec6 : ∀{Γ A} → Tm6 Γ nat6 → Tm6 Γ (arr6 nat6 (arr6 A A)) → Tm6 Γ A → Tm6 Γ A; rec6
 = λ t u v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6 →
     rec6 _ _
          (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)
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
   (vz  : ∀ Γ A → Var7 (snoc7 Γ A) A)
   (vs  : ∀ Γ B A → Var7 Γ A → Var7 (snoc7 Γ B) A)
 → Var7 Γ A

vz7 : ∀{Γ A} → Var7 (snoc7 Γ A) A; vz7
 = λ Var7 vz7 vs → vz7 _ _

vs7 : ∀{Γ B A} → Var7 Γ A → Var7 (snoc7 Γ B) A; vs7
 = λ x Var7 vz7 vs7 → vs7 _ _ _ (x Var7 vz7 vs7)

Tm7 : Con7 → Ty7 → Set; Tm7
 = λ Γ A →
   (Tm7  : Con7 → Ty7 → Set)
   (var   : ∀ Γ A      → Var7 Γ A → Tm7 Γ A)
   (lam   : ∀ Γ A B    → Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B))
   (app   : ∀ Γ A B    → Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B)
   (tt    : ∀ Γ        → Tm7 Γ top7)
   (pair  : ∀ Γ A B    → Tm7 Γ A → Tm7 Γ B → Tm7 Γ (prod7 A B))
   (fst   : ∀ Γ A B    → Tm7 Γ (prod7 A B) → Tm7 Γ A)
   (snd   : ∀ Γ A B    → Tm7 Γ (prod7 A B) → Tm7 Γ B)
   (left  : ∀ Γ A B    → Tm7 Γ A → Tm7 Γ (sum7 A B))
   (right : ∀ Γ A B    → Tm7 Γ B → Tm7 Γ (sum7 A B))
   (case  : ∀ Γ A B C  → Tm7 Γ (sum7 A B) → Tm7 Γ (arr7 A C) → Tm7 Γ (arr7 B C) → Tm7 Γ C)
   (zero  : ∀ Γ        → Tm7 Γ nat7)
   (suc   : ∀ Γ        → Tm7 Γ nat7 → Tm7 Γ nat7)
   (rec   : ∀ Γ A      → Tm7 Γ nat7 → Tm7 Γ (arr7 nat7 (arr7 A A)) → Tm7 Γ A → Tm7 Γ A)
 → Tm7 Γ A

var7 : ∀{Γ A} → Var7 Γ A → Tm7 Γ A; var7
 = λ x Tm7 var7 lam app tt pair fst snd left right case zero suc rec →
     var7 _ _ x

lam7 : ∀{Γ A B} → Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B); lam7
 = λ t Tm7 var7 lam7 app tt pair fst snd left right case zero suc rec →
     lam7 _ _ _ (t Tm7 var7 lam7 app tt pair fst snd left right case zero suc rec)

app7 : ∀{Γ A B} → Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B; app7
 = λ t u Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec →
     app7 _ _ _ (t Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec)
         (u Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec)

tt7 : ∀{Γ} → Tm7 Γ top7; tt7
 = λ Tm7 var7 lam7 app7 tt7 pair fst snd left right case zero suc rec → tt7 _

pair7 : ∀{Γ A B} → Tm7 Γ A → Tm7 Γ B → Tm7 Γ (prod7 A B); pair7
 = λ t u Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec →
     pair7 _ _ _ (t Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec)
          (u Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec)

fst7 : ∀{Γ A B} → Tm7 Γ (prod7 A B) → Tm7 Γ A; fst7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd left right case zero suc rec →
     fst7 _ _ _ (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd left right case zero suc rec)

snd7 : ∀{Γ A B} → Tm7 Γ (prod7 A B) → Tm7 Γ B; snd7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left right case zero suc rec →
     snd7 _ _ _ (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left right case zero suc rec)

left7 : ∀{Γ A B} → Tm7 Γ A → Tm7 Γ (sum7 A B); left7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right case zero suc rec →
     left7 _ _ _ (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right case zero suc rec)

right7 : ∀{Γ A B} → Tm7 Γ B → Tm7 Γ (sum7 A B); right7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case zero suc rec →
     right7 _ _ _ (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case zero suc rec)

case7 : ∀{Γ A B C} → Tm7 Γ (sum7 A B) → Tm7 Γ (arr7 A C) → Tm7 Γ (arr7 B C) → Tm7 Γ C; case7
 = λ t u v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec →
     case7 _ _ _ _
           (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)
           (u Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)
           (v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)

zero7  : ∀{Γ} → Tm7 Γ nat7; zero7
 = λ Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc rec → zero7 _

suc7 : ∀{Γ} → Tm7 Γ nat7 → Tm7 Γ nat7; suc7
 = λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec →
   suc7 _ (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec)

rec7 : ∀{Γ A} → Tm7 Γ nat7 → Tm7 Γ (arr7 nat7 (arr7 A A)) → Tm7 Γ A → Tm7 Γ A; rec7
 = λ t u v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7 →
     rec7 _ _
          (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)
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
   (vz  : ∀ Γ A → Var8 (snoc8 Γ A) A)
   (vs  : ∀ Γ B A → Var8 Γ A → Var8 (snoc8 Γ B) A)
 → Var8 Γ A

vz8 : ∀{Γ A} → Var8 (snoc8 Γ A) A; vz8
 = λ Var8 vz8 vs → vz8 _ _

vs8 : ∀{Γ B A} → Var8 Γ A → Var8 (snoc8 Γ B) A; vs8
 = λ x Var8 vz8 vs8 → vs8 _ _ _ (x Var8 vz8 vs8)

Tm8 : Con8 → Ty8 → Set; Tm8
 = λ Γ A →
   (Tm8  : Con8 → Ty8 → Set)
   (var   : ∀ Γ A      → Var8 Γ A → Tm8 Γ A)
   (lam   : ∀ Γ A B    → Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B))
   (app   : ∀ Γ A B    → Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B)
   (tt    : ∀ Γ        → Tm8 Γ top8)
   (pair  : ∀ Γ A B    → Tm8 Γ A → Tm8 Γ B → Tm8 Γ (prod8 A B))
   (fst   : ∀ Γ A B    → Tm8 Γ (prod8 A B) → Tm8 Γ A)
   (snd   : ∀ Γ A B    → Tm8 Γ (prod8 A B) → Tm8 Γ B)
   (left  : ∀ Γ A B    → Tm8 Γ A → Tm8 Γ (sum8 A B))
   (right : ∀ Γ A B    → Tm8 Γ B → Tm8 Γ (sum8 A B))
   (case  : ∀ Γ A B C  → Tm8 Γ (sum8 A B) → Tm8 Γ (arr8 A C) → Tm8 Γ (arr8 B C) → Tm8 Γ C)
   (zero  : ∀ Γ        → Tm8 Γ nat8)
   (suc   : ∀ Γ        → Tm8 Γ nat8 → Tm8 Γ nat8)
   (rec   : ∀ Γ A      → Tm8 Γ nat8 → Tm8 Γ (arr8 nat8 (arr8 A A)) → Tm8 Γ A → Tm8 Γ A)
 → Tm8 Γ A

var8 : ∀{Γ A} → Var8 Γ A → Tm8 Γ A; var8
 = λ x Tm8 var8 lam app tt pair fst snd left right case zero suc rec →
     var8 _ _ x

lam8 : ∀{Γ A B} → Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B); lam8
 = λ t Tm8 var8 lam8 app tt pair fst snd left right case zero suc rec →
     lam8 _ _ _ (t Tm8 var8 lam8 app tt pair fst snd left right case zero suc rec)

app8 : ∀{Γ A B} → Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B; app8
 = λ t u Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec →
     app8 _ _ _ (t Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec)
         (u Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec)

tt8 : ∀{Γ} → Tm8 Γ top8; tt8
 = λ Tm8 var8 lam8 app8 tt8 pair fst snd left right case zero suc rec → tt8 _

pair8 : ∀{Γ A B} → Tm8 Γ A → Tm8 Γ B → Tm8 Γ (prod8 A B); pair8
 = λ t u Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec →
     pair8 _ _ _ (t Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec)
          (u Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec)

fst8 : ∀{Γ A B} → Tm8 Γ (prod8 A B) → Tm8 Γ A; fst8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd left right case zero suc rec →
     fst8 _ _ _ (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd left right case zero suc rec)

snd8 : ∀{Γ A B} → Tm8 Γ (prod8 A B) → Tm8 Γ B; snd8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left right case zero suc rec →
     snd8 _ _ _ (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left right case zero suc rec)

left8 : ∀{Γ A B} → Tm8 Γ A → Tm8 Γ (sum8 A B); left8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right case zero suc rec →
     left8 _ _ _ (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right case zero suc rec)

right8 : ∀{Γ A B} → Tm8 Γ B → Tm8 Γ (sum8 A B); right8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case zero suc rec →
     right8 _ _ _ (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case zero suc rec)

case8 : ∀{Γ A B C} → Tm8 Γ (sum8 A B) → Tm8 Γ (arr8 A C) → Tm8 Γ (arr8 B C) → Tm8 Γ C; case8
 = λ t u v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec →
     case8 _ _ _ _
           (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)
           (u Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)
           (v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)

zero8  : ∀{Γ} → Tm8 Γ nat8; zero8
 = λ Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc rec → zero8 _

suc8 : ∀{Γ} → Tm8 Γ nat8 → Tm8 Γ nat8; suc8
 = λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec →
   suc8 _ (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec)

rec8 : ∀{Γ A} → Tm8 Γ nat8 → Tm8 Γ (arr8 nat8 (arr8 A A)) → Tm8 Γ A → Tm8 Γ A; rec8
 = λ t u v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8 →
     rec8 _ _
          (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)
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
   (vz  : ∀ Γ A → Var9 (snoc9 Γ A) A)
   (vs  : ∀ Γ B A → Var9 Γ A → Var9 (snoc9 Γ B) A)
 → Var9 Γ A

vz9 : ∀{Γ A} → Var9 (snoc9 Γ A) A; vz9
 = λ Var9 vz9 vs → vz9 _ _

vs9 : ∀{Γ B A} → Var9 Γ A → Var9 (snoc9 Γ B) A; vs9
 = λ x Var9 vz9 vs9 → vs9 _ _ _ (x Var9 vz9 vs9)

Tm9 : Con9 → Ty9 → Set; Tm9
 = λ Γ A →
   (Tm9  : Con9 → Ty9 → Set)
   (var   : ∀ Γ A      → Var9 Γ A → Tm9 Γ A)
   (lam   : ∀ Γ A B    → Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B))
   (app   : ∀ Γ A B    → Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B)
   (tt    : ∀ Γ        → Tm9 Γ top9)
   (pair  : ∀ Γ A B    → Tm9 Γ A → Tm9 Γ B → Tm9 Γ (prod9 A B))
   (fst   : ∀ Γ A B    → Tm9 Γ (prod9 A B) → Tm9 Γ A)
   (snd   : ∀ Γ A B    → Tm9 Γ (prod9 A B) → Tm9 Γ B)
   (left  : ∀ Γ A B    → Tm9 Γ A → Tm9 Γ (sum9 A B))
   (right : ∀ Γ A B    → Tm9 Γ B → Tm9 Γ (sum9 A B))
   (case  : ∀ Γ A B C  → Tm9 Γ (sum9 A B) → Tm9 Γ (arr9 A C) → Tm9 Γ (arr9 B C) → Tm9 Γ C)
   (zero  : ∀ Γ        → Tm9 Γ nat9)
   (suc   : ∀ Γ        → Tm9 Γ nat9 → Tm9 Γ nat9)
   (rec   : ∀ Γ A      → Tm9 Γ nat9 → Tm9 Γ (arr9 nat9 (arr9 A A)) → Tm9 Γ A → Tm9 Γ A)
 → Tm9 Γ A

var9 : ∀{Γ A} → Var9 Γ A → Tm9 Γ A; var9
 = λ x Tm9 var9 lam app tt pair fst snd left right case zero suc rec →
     var9 _ _ x

lam9 : ∀{Γ A B} → Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B); lam9
 = λ t Tm9 var9 lam9 app tt pair fst snd left right case zero suc rec →
     lam9 _ _ _ (t Tm9 var9 lam9 app tt pair fst snd left right case zero suc rec)

app9 : ∀{Γ A B} → Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B; app9
 = λ t u Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec →
     app9 _ _ _ (t Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec)
         (u Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec)

tt9 : ∀{Γ} → Tm9 Γ top9; tt9
 = λ Tm9 var9 lam9 app9 tt9 pair fst snd left right case zero suc rec → tt9 _

pair9 : ∀{Γ A B} → Tm9 Γ A → Tm9 Γ B → Tm9 Γ (prod9 A B); pair9
 = λ t u Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec →
     pair9 _ _ _ (t Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec)
          (u Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec)

fst9 : ∀{Γ A B} → Tm9 Γ (prod9 A B) → Tm9 Γ A; fst9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd left right case zero suc rec →
     fst9 _ _ _ (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd left right case zero suc rec)

snd9 : ∀{Γ A B} → Tm9 Γ (prod9 A B) → Tm9 Γ B; snd9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left right case zero suc rec →
     snd9 _ _ _ (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left right case zero suc rec)

left9 : ∀{Γ A B} → Tm9 Γ A → Tm9 Γ (sum9 A B); left9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right case zero suc rec →
     left9 _ _ _ (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right case zero suc rec)

right9 : ∀{Γ A B} → Tm9 Γ B → Tm9 Γ (sum9 A B); right9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case zero suc rec →
     right9 _ _ _ (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case zero suc rec)

case9 : ∀{Γ A B C} → Tm9 Γ (sum9 A B) → Tm9 Γ (arr9 A C) → Tm9 Γ (arr9 B C) → Tm9 Γ C; case9
 = λ t u v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec →
     case9 _ _ _ _
           (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)
           (u Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)
           (v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)

zero9  : ∀{Γ} → Tm9 Γ nat9; zero9
 = λ Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc rec → zero9 _

suc9 : ∀{Γ} → Tm9 Γ nat9 → Tm9 Γ nat9; suc9
 = λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec →
   suc9 _ (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec)

rec9 : ∀{Γ A} → Tm9 Γ nat9 → Tm9 Γ (arr9 nat9 (arr9 A A)) → Tm9 Γ A → Tm9 Γ A; rec9
 = λ t u v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9 →
     rec9 _ _
          (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)
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
   (vz  : ∀ Γ A → Var10 (snoc10 Γ A) A)
   (vs  : ∀ Γ B A → Var10 Γ A → Var10 (snoc10 Γ B) A)
 → Var10 Γ A

vz10 : ∀{Γ A} → Var10 (snoc10 Γ A) A; vz10
 = λ Var10 vz10 vs → vz10 _ _

vs10 : ∀{Γ B A} → Var10 Γ A → Var10 (snoc10 Γ B) A; vs10
 = λ x Var10 vz10 vs10 → vs10 _ _ _ (x Var10 vz10 vs10)

Tm10 : Con10 → Ty10 → Set; Tm10
 = λ Γ A →
   (Tm10  : Con10 → Ty10 → Set)
   (var   : ∀ Γ A      → Var10 Γ A → Tm10 Γ A)
   (lam   : ∀ Γ A B    → Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B))
   (app   : ∀ Γ A B    → Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B)
   (tt    : ∀ Γ        → Tm10 Γ top10)
   (pair  : ∀ Γ A B    → Tm10 Γ A → Tm10 Γ B → Tm10 Γ (prod10 A B))
   (fst   : ∀ Γ A B    → Tm10 Γ (prod10 A B) → Tm10 Γ A)
   (snd   : ∀ Γ A B    → Tm10 Γ (prod10 A B) → Tm10 Γ B)
   (left  : ∀ Γ A B    → Tm10 Γ A → Tm10 Γ (sum10 A B))
   (right : ∀ Γ A B    → Tm10 Γ B → Tm10 Γ (sum10 A B))
   (case  : ∀ Γ A B C  → Tm10 Γ (sum10 A B) → Tm10 Γ (arr10 A C) → Tm10 Γ (arr10 B C) → Tm10 Γ C)
   (zero  : ∀ Γ        → Tm10 Γ nat10)
   (suc   : ∀ Γ        → Tm10 Γ nat10 → Tm10 Γ nat10)
   (rec   : ∀ Γ A      → Tm10 Γ nat10 → Tm10 Γ (arr10 nat10 (arr10 A A)) → Tm10 Γ A → Tm10 Γ A)
 → Tm10 Γ A

var10 : ∀{Γ A} → Var10 Γ A → Tm10 Γ A; var10
 = λ x Tm10 var10 lam app tt pair fst snd left right case zero suc rec →
     var10 _ _ x

lam10 : ∀{Γ A B} → Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B); lam10
 = λ t Tm10 var10 lam10 app tt pair fst snd left right case zero suc rec →
     lam10 _ _ _ (t Tm10 var10 lam10 app tt pair fst snd left right case zero suc rec)

app10 : ∀{Γ A B} → Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B; app10
 = λ t u Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec →
     app10 _ _ _ (t Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec)
         (u Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec)

tt10 : ∀{Γ} → Tm10 Γ top10; tt10
 = λ Tm10 var10 lam10 app10 tt10 pair fst snd left right case zero suc rec → tt10 _

pair10 : ∀{Γ A B} → Tm10 Γ A → Tm10 Γ B → Tm10 Γ (prod10 A B); pair10
 = λ t u Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec →
     pair10 _ _ _ (t Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec)
          (u Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec)

fst10 : ∀{Γ A B} → Tm10 Γ (prod10 A B) → Tm10 Γ A; fst10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd left right case zero suc rec →
     fst10 _ _ _ (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd left right case zero suc rec)

snd10 : ∀{Γ A B} → Tm10 Γ (prod10 A B) → Tm10 Γ B; snd10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left right case zero suc rec →
     snd10 _ _ _ (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left right case zero suc rec)

left10 : ∀{Γ A B} → Tm10 Γ A → Tm10 Γ (sum10 A B); left10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right case zero suc rec →
     left10 _ _ _ (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right case zero suc rec)

right10 : ∀{Γ A B} → Tm10 Γ B → Tm10 Γ (sum10 A B); right10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case zero suc rec →
     right10 _ _ _ (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case zero suc rec)

case10 : ∀{Γ A B C} → Tm10 Γ (sum10 A B) → Tm10 Γ (arr10 A C) → Tm10 Γ (arr10 B C) → Tm10 Γ C; case10
 = λ t u v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec →
     case10 _ _ _ _
           (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)
           (u Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)
           (v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)

zero10  : ∀{Γ} → Tm10 Γ nat10; zero10
 = λ Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc rec → zero10 _

suc10 : ∀{Γ} → Tm10 Γ nat10 → Tm10 Γ nat10; suc10
 = λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec →
   suc10 _ (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec)

rec10 : ∀{Γ A} → Tm10 Γ nat10 → Tm10 Γ (arr10 nat10 (arr10 A A)) → Tm10 Γ A → Tm10 Γ A; rec10
 = λ t u v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10 →
     rec10 _ _
          (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)
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
   (vz  : ∀ Γ A → Var11 (snoc11 Γ A) A)
   (vs  : ∀ Γ B A → Var11 Γ A → Var11 (snoc11 Γ B) A)
 → Var11 Γ A

vz11 : ∀{Γ A} → Var11 (snoc11 Γ A) A; vz11
 = λ Var11 vz11 vs → vz11 _ _

vs11 : ∀{Γ B A} → Var11 Γ A → Var11 (snoc11 Γ B) A; vs11
 = λ x Var11 vz11 vs11 → vs11 _ _ _ (x Var11 vz11 vs11)

Tm11 : Con11 → Ty11 → Set; Tm11
 = λ Γ A →
   (Tm11  : Con11 → Ty11 → Set)
   (var   : ∀ Γ A      → Var11 Γ A → Tm11 Γ A)
   (lam   : ∀ Γ A B    → Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B))
   (app   : ∀ Γ A B    → Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B)
   (tt    : ∀ Γ        → Tm11 Γ top11)
   (pair  : ∀ Γ A B    → Tm11 Γ A → Tm11 Γ B → Tm11 Γ (prod11 A B))
   (fst   : ∀ Γ A B    → Tm11 Γ (prod11 A B) → Tm11 Γ A)
   (snd   : ∀ Γ A B    → Tm11 Γ (prod11 A B) → Tm11 Γ B)
   (left  : ∀ Γ A B    → Tm11 Γ A → Tm11 Γ (sum11 A B))
   (right : ∀ Γ A B    → Tm11 Γ B → Tm11 Γ (sum11 A B))
   (case  : ∀ Γ A B C  → Tm11 Γ (sum11 A B) → Tm11 Γ (arr11 A C) → Tm11 Γ (arr11 B C) → Tm11 Γ C)
   (zero  : ∀ Γ        → Tm11 Γ nat11)
   (suc   : ∀ Γ        → Tm11 Γ nat11 → Tm11 Γ nat11)
   (rec   : ∀ Γ A      → Tm11 Γ nat11 → Tm11 Γ (arr11 nat11 (arr11 A A)) → Tm11 Γ A → Tm11 Γ A)
 → Tm11 Γ A

var11 : ∀{Γ A} → Var11 Γ A → Tm11 Γ A; var11
 = λ x Tm11 var11 lam app tt pair fst snd left right case zero suc rec →
     var11 _ _ x

lam11 : ∀{Γ A B} → Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B); lam11
 = λ t Tm11 var11 lam11 app tt pair fst snd left right case zero suc rec →
     lam11 _ _ _ (t Tm11 var11 lam11 app tt pair fst snd left right case zero suc rec)

app11 : ∀{Γ A B} → Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B; app11
 = λ t u Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec →
     app11 _ _ _ (t Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec)
         (u Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec)

tt11 : ∀{Γ} → Tm11 Γ top11; tt11
 = λ Tm11 var11 lam11 app11 tt11 pair fst snd left right case zero suc rec → tt11 _

pair11 : ∀{Γ A B} → Tm11 Γ A → Tm11 Γ B → Tm11 Γ (prod11 A B); pair11
 = λ t u Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec →
     pair11 _ _ _ (t Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec)
          (u Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec)

fst11 : ∀{Γ A B} → Tm11 Γ (prod11 A B) → Tm11 Γ A; fst11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd left right case zero suc rec →
     fst11 _ _ _ (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd left right case zero suc rec)

snd11 : ∀{Γ A B} → Tm11 Γ (prod11 A B) → Tm11 Γ B; snd11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left right case zero suc rec →
     snd11 _ _ _ (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left right case zero suc rec)

left11 : ∀{Γ A B} → Tm11 Γ A → Tm11 Γ (sum11 A B); left11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right case zero suc rec →
     left11 _ _ _ (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right case zero suc rec)

right11 : ∀{Γ A B} → Tm11 Γ B → Tm11 Γ (sum11 A B); right11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case zero suc rec →
     right11 _ _ _ (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case zero suc rec)

case11 : ∀{Γ A B C} → Tm11 Γ (sum11 A B) → Tm11 Γ (arr11 A C) → Tm11 Γ (arr11 B C) → Tm11 Γ C; case11
 = λ t u v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec →
     case11 _ _ _ _
           (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)
           (u Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)
           (v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)

zero11  : ∀{Γ} → Tm11 Γ nat11; zero11
 = λ Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc rec → zero11 _

suc11 : ∀{Γ} → Tm11 Γ nat11 → Tm11 Γ nat11; suc11
 = λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec →
   suc11 _ (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec)

rec11 : ∀{Γ A} → Tm11 Γ nat11 → Tm11 Γ (arr11 nat11 (arr11 A A)) → Tm11 Γ A → Tm11 Γ A; rec11
 = λ t u v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11 →
     rec11 _ _
          (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)
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
   (vz  : ∀ Γ A → Var12 (snoc12 Γ A) A)
   (vs  : ∀ Γ B A → Var12 Γ A → Var12 (snoc12 Γ B) A)
 → Var12 Γ A

vz12 : ∀{Γ A} → Var12 (snoc12 Γ A) A; vz12
 = λ Var12 vz12 vs → vz12 _ _

vs12 : ∀{Γ B A} → Var12 Γ A → Var12 (snoc12 Γ B) A; vs12
 = λ x Var12 vz12 vs12 → vs12 _ _ _ (x Var12 vz12 vs12)

Tm12 : Con12 → Ty12 → Set; Tm12
 = λ Γ A →
   (Tm12  : Con12 → Ty12 → Set)
   (var   : ∀ Γ A      → Var12 Γ A → Tm12 Γ A)
   (lam   : ∀ Γ A B    → Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B))
   (app   : ∀ Γ A B    → Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B)
   (tt    : ∀ Γ        → Tm12 Γ top12)
   (pair  : ∀ Γ A B    → Tm12 Γ A → Tm12 Γ B → Tm12 Γ (prod12 A B))
   (fst   : ∀ Γ A B    → Tm12 Γ (prod12 A B) → Tm12 Γ A)
   (snd   : ∀ Γ A B    → Tm12 Γ (prod12 A B) → Tm12 Γ B)
   (left  : ∀ Γ A B    → Tm12 Γ A → Tm12 Γ (sum12 A B))
   (right : ∀ Γ A B    → Tm12 Γ B → Tm12 Γ (sum12 A B))
   (case  : ∀ Γ A B C  → Tm12 Γ (sum12 A B) → Tm12 Γ (arr12 A C) → Tm12 Γ (arr12 B C) → Tm12 Γ C)
   (zero  : ∀ Γ        → Tm12 Γ nat12)
   (suc   : ∀ Γ        → Tm12 Γ nat12 → Tm12 Γ nat12)
   (rec   : ∀ Γ A      → Tm12 Γ nat12 → Tm12 Γ (arr12 nat12 (arr12 A A)) → Tm12 Γ A → Tm12 Γ A)
 → Tm12 Γ A

var12 : ∀{Γ A} → Var12 Γ A → Tm12 Γ A; var12
 = λ x Tm12 var12 lam app tt pair fst snd left right case zero suc rec →
     var12 _ _ x

lam12 : ∀{Γ A B} → Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B); lam12
 = λ t Tm12 var12 lam12 app tt pair fst snd left right case zero suc rec →
     lam12 _ _ _ (t Tm12 var12 lam12 app tt pair fst snd left right case zero suc rec)

app12 : ∀{Γ A B} → Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B; app12
 = λ t u Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec →
     app12 _ _ _ (t Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec)
         (u Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec)

tt12 : ∀{Γ} → Tm12 Γ top12; tt12
 = λ Tm12 var12 lam12 app12 tt12 pair fst snd left right case zero suc rec → tt12 _

pair12 : ∀{Γ A B} → Tm12 Γ A → Tm12 Γ B → Tm12 Γ (prod12 A B); pair12
 = λ t u Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec →
     pair12 _ _ _ (t Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec)
          (u Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec)

fst12 : ∀{Γ A B} → Tm12 Γ (prod12 A B) → Tm12 Γ A; fst12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd left right case zero suc rec →
     fst12 _ _ _ (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd left right case zero suc rec)

snd12 : ∀{Γ A B} → Tm12 Γ (prod12 A B) → Tm12 Γ B; snd12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left right case zero suc rec →
     snd12 _ _ _ (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left right case zero suc rec)

left12 : ∀{Γ A B} → Tm12 Γ A → Tm12 Γ (sum12 A B); left12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right case zero suc rec →
     left12 _ _ _ (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right case zero suc rec)

right12 : ∀{Γ A B} → Tm12 Γ B → Tm12 Γ (sum12 A B); right12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case zero suc rec →
     right12 _ _ _ (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case zero suc rec)

case12 : ∀{Γ A B C} → Tm12 Γ (sum12 A B) → Tm12 Γ (arr12 A C) → Tm12 Γ (arr12 B C) → Tm12 Γ C; case12
 = λ t u v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec →
     case12 _ _ _ _
           (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)
           (u Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)
           (v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)

zero12  : ∀{Γ} → Tm12 Γ nat12; zero12
 = λ Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc rec → zero12 _

suc12 : ∀{Γ} → Tm12 Γ nat12 → Tm12 Γ nat12; suc12
 = λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec →
   suc12 _ (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec)

rec12 : ∀{Γ A} → Tm12 Γ nat12 → Tm12 Γ (arr12 nat12 (arr12 A A)) → Tm12 Γ A → Tm12 Γ A; rec12
 = λ t u v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12 →
     rec12 _ _
          (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)
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
   (vz  : ∀ Γ A → Var13 (snoc13 Γ A) A)
   (vs  : ∀ Γ B A → Var13 Γ A → Var13 (snoc13 Γ B) A)
 → Var13 Γ A

vz13 : ∀{Γ A} → Var13 (snoc13 Γ A) A; vz13
 = λ Var13 vz13 vs → vz13 _ _

vs13 : ∀{Γ B A} → Var13 Γ A → Var13 (snoc13 Γ B) A; vs13
 = λ x Var13 vz13 vs13 → vs13 _ _ _ (x Var13 vz13 vs13)

Tm13 : Con13 → Ty13 → Set; Tm13
 = λ Γ A →
   (Tm13  : Con13 → Ty13 → Set)
   (var   : ∀ Γ A      → Var13 Γ A → Tm13 Γ A)
   (lam   : ∀ Γ A B    → Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B))
   (app   : ∀ Γ A B    → Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B)
   (tt    : ∀ Γ        → Tm13 Γ top13)
   (pair  : ∀ Γ A B    → Tm13 Γ A → Tm13 Γ B → Tm13 Γ (prod13 A B))
   (fst   : ∀ Γ A B    → Tm13 Γ (prod13 A B) → Tm13 Γ A)
   (snd   : ∀ Γ A B    → Tm13 Γ (prod13 A B) → Tm13 Γ B)
   (left  : ∀ Γ A B    → Tm13 Γ A → Tm13 Γ (sum13 A B))
   (right : ∀ Γ A B    → Tm13 Γ B → Tm13 Γ (sum13 A B))
   (case  : ∀ Γ A B C  → Tm13 Γ (sum13 A B) → Tm13 Γ (arr13 A C) → Tm13 Γ (arr13 B C) → Tm13 Γ C)
   (zero  : ∀ Γ        → Tm13 Γ nat13)
   (suc   : ∀ Γ        → Tm13 Γ nat13 → Tm13 Γ nat13)
   (rec   : ∀ Γ A      → Tm13 Γ nat13 → Tm13 Γ (arr13 nat13 (arr13 A A)) → Tm13 Γ A → Tm13 Γ A)
 → Tm13 Γ A

var13 : ∀{Γ A} → Var13 Γ A → Tm13 Γ A; var13
 = λ x Tm13 var13 lam app tt pair fst snd left right case zero suc rec →
     var13 _ _ x

lam13 : ∀{Γ A B} → Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B); lam13
 = λ t Tm13 var13 lam13 app tt pair fst snd left right case zero suc rec →
     lam13 _ _ _ (t Tm13 var13 lam13 app tt pair fst snd left right case zero suc rec)

app13 : ∀{Γ A B} → Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B; app13
 = λ t u Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec →
     app13 _ _ _ (t Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec)
         (u Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec)

tt13 : ∀{Γ} → Tm13 Γ top13; tt13
 = λ Tm13 var13 lam13 app13 tt13 pair fst snd left right case zero suc rec → tt13 _

pair13 : ∀{Γ A B} → Tm13 Γ A → Tm13 Γ B → Tm13 Γ (prod13 A B); pair13
 = λ t u Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec →
     pair13 _ _ _ (t Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec)
          (u Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec)

fst13 : ∀{Γ A B} → Tm13 Γ (prod13 A B) → Tm13 Γ A; fst13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd left right case zero suc rec →
     fst13 _ _ _ (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd left right case zero suc rec)

snd13 : ∀{Γ A B} → Tm13 Γ (prod13 A B) → Tm13 Γ B; snd13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left right case zero suc rec →
     snd13 _ _ _ (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left right case zero suc rec)

left13 : ∀{Γ A B} → Tm13 Γ A → Tm13 Γ (sum13 A B); left13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right case zero suc rec →
     left13 _ _ _ (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right case zero suc rec)

right13 : ∀{Γ A B} → Tm13 Γ B → Tm13 Γ (sum13 A B); right13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case zero suc rec →
     right13 _ _ _ (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case zero suc rec)

case13 : ∀{Γ A B C} → Tm13 Γ (sum13 A B) → Tm13 Γ (arr13 A C) → Tm13 Γ (arr13 B C) → Tm13 Γ C; case13
 = λ t u v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec →
     case13 _ _ _ _
           (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)
           (u Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)
           (v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)

zero13  : ∀{Γ} → Tm13 Γ nat13; zero13
 = λ Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc rec → zero13 _

suc13 : ∀{Γ} → Tm13 Γ nat13 → Tm13 Γ nat13; suc13
 = λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec →
   suc13 _ (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec)

rec13 : ∀{Γ A} → Tm13 Γ nat13 → Tm13 Γ (arr13 nat13 (arr13 A A)) → Tm13 Γ A → Tm13 Γ A; rec13
 = λ t u v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13 →
     rec13 _ _
          (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)
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
   (vz  : ∀ Γ A → Var14 (snoc14 Γ A) A)
   (vs  : ∀ Γ B A → Var14 Γ A → Var14 (snoc14 Γ B) A)
 → Var14 Γ A

vz14 : ∀{Γ A} → Var14 (snoc14 Γ A) A; vz14
 = λ Var14 vz14 vs → vz14 _ _

vs14 : ∀{Γ B A} → Var14 Γ A → Var14 (snoc14 Γ B) A; vs14
 = λ x Var14 vz14 vs14 → vs14 _ _ _ (x Var14 vz14 vs14)

Tm14 : Con14 → Ty14 → Set; Tm14
 = λ Γ A →
   (Tm14  : Con14 → Ty14 → Set)
   (var   : ∀ Γ A      → Var14 Γ A → Tm14 Γ A)
   (lam   : ∀ Γ A B    → Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B))
   (app   : ∀ Γ A B    → Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B)
   (tt    : ∀ Γ        → Tm14 Γ top14)
   (pair  : ∀ Γ A B    → Tm14 Γ A → Tm14 Γ B → Tm14 Γ (prod14 A B))
   (fst   : ∀ Γ A B    → Tm14 Γ (prod14 A B) → Tm14 Γ A)
   (snd   : ∀ Γ A B    → Tm14 Γ (prod14 A B) → Tm14 Γ B)
   (left  : ∀ Γ A B    → Tm14 Γ A → Tm14 Γ (sum14 A B))
   (right : ∀ Γ A B    → Tm14 Γ B → Tm14 Γ (sum14 A B))
   (case  : ∀ Γ A B C  → Tm14 Γ (sum14 A B) → Tm14 Γ (arr14 A C) → Tm14 Γ (arr14 B C) → Tm14 Γ C)
   (zero  : ∀ Γ        → Tm14 Γ nat14)
   (suc   : ∀ Γ        → Tm14 Γ nat14 → Tm14 Γ nat14)
   (rec   : ∀ Γ A      → Tm14 Γ nat14 → Tm14 Γ (arr14 nat14 (arr14 A A)) → Tm14 Γ A → Tm14 Γ A)
 → Tm14 Γ A

var14 : ∀{Γ A} → Var14 Γ A → Tm14 Γ A; var14
 = λ x Tm14 var14 lam app tt pair fst snd left right case zero suc rec →
     var14 _ _ x

lam14 : ∀{Γ A B} → Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B); lam14
 = λ t Tm14 var14 lam14 app tt pair fst snd left right case zero suc rec →
     lam14 _ _ _ (t Tm14 var14 lam14 app tt pair fst snd left right case zero suc rec)

app14 : ∀{Γ A B} → Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B; app14
 = λ t u Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec →
     app14 _ _ _ (t Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec)
         (u Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec)

tt14 : ∀{Γ} → Tm14 Γ top14; tt14
 = λ Tm14 var14 lam14 app14 tt14 pair fst snd left right case zero suc rec → tt14 _

pair14 : ∀{Γ A B} → Tm14 Γ A → Tm14 Γ B → Tm14 Γ (prod14 A B); pair14
 = λ t u Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec →
     pair14 _ _ _ (t Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec)
          (u Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec)

fst14 : ∀{Γ A B} → Tm14 Γ (prod14 A B) → Tm14 Γ A; fst14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd left right case zero suc rec →
     fst14 _ _ _ (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd left right case zero suc rec)

snd14 : ∀{Γ A B} → Tm14 Γ (prod14 A B) → Tm14 Γ B; snd14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left right case zero suc rec →
     snd14 _ _ _ (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left right case zero suc rec)

left14 : ∀{Γ A B} → Tm14 Γ A → Tm14 Γ (sum14 A B); left14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right case zero suc rec →
     left14 _ _ _ (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right case zero suc rec)

right14 : ∀{Γ A B} → Tm14 Γ B → Tm14 Γ (sum14 A B); right14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case zero suc rec →
     right14 _ _ _ (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case zero suc rec)

case14 : ∀{Γ A B C} → Tm14 Γ (sum14 A B) → Tm14 Γ (arr14 A C) → Tm14 Γ (arr14 B C) → Tm14 Γ C; case14
 = λ t u v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec →
     case14 _ _ _ _
           (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)
           (u Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)
           (v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)

zero14  : ∀{Γ} → Tm14 Γ nat14; zero14
 = λ Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc rec → zero14 _

suc14 : ∀{Γ} → Tm14 Γ nat14 → Tm14 Γ nat14; suc14
 = λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec →
   suc14 _ (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec)

rec14 : ∀{Γ A} → Tm14 Γ nat14 → Tm14 Γ (arr14 nat14 (arr14 A A)) → Tm14 Γ A → Tm14 Γ A; rec14
 = λ t u v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14 →
     rec14 _ _
          (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)
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
   (vz  : ∀ Γ A → Var15 (snoc15 Γ A) A)
   (vs  : ∀ Γ B A → Var15 Γ A → Var15 (snoc15 Γ B) A)
 → Var15 Γ A

vz15 : ∀{Γ A} → Var15 (snoc15 Γ A) A; vz15
 = λ Var15 vz15 vs → vz15 _ _

vs15 : ∀{Γ B A} → Var15 Γ A → Var15 (snoc15 Γ B) A; vs15
 = λ x Var15 vz15 vs15 → vs15 _ _ _ (x Var15 vz15 vs15)

Tm15 : Con15 → Ty15 → Set; Tm15
 = λ Γ A →
   (Tm15  : Con15 → Ty15 → Set)
   (var   : ∀ Γ A      → Var15 Γ A → Tm15 Γ A)
   (lam   : ∀ Γ A B    → Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B))
   (app   : ∀ Γ A B    → Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B)
   (tt    : ∀ Γ        → Tm15 Γ top15)
   (pair  : ∀ Γ A B    → Tm15 Γ A → Tm15 Γ B → Tm15 Γ (prod15 A B))
   (fst   : ∀ Γ A B    → Tm15 Γ (prod15 A B) → Tm15 Γ A)
   (snd   : ∀ Γ A B    → Tm15 Γ (prod15 A B) → Tm15 Γ B)
   (left  : ∀ Γ A B    → Tm15 Γ A → Tm15 Γ (sum15 A B))
   (right : ∀ Γ A B    → Tm15 Γ B → Tm15 Γ (sum15 A B))
   (case  : ∀ Γ A B C  → Tm15 Γ (sum15 A B) → Tm15 Γ (arr15 A C) → Tm15 Γ (arr15 B C) → Tm15 Γ C)
   (zero  : ∀ Γ        → Tm15 Γ nat15)
   (suc   : ∀ Γ        → Tm15 Γ nat15 → Tm15 Γ nat15)
   (rec   : ∀ Γ A      → Tm15 Γ nat15 → Tm15 Γ (arr15 nat15 (arr15 A A)) → Tm15 Γ A → Tm15 Γ A)
 → Tm15 Γ A

var15 : ∀{Γ A} → Var15 Γ A → Tm15 Γ A; var15
 = λ x Tm15 var15 lam app tt pair fst snd left right case zero suc rec →
     var15 _ _ x

lam15 : ∀{Γ A B} → Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B); lam15
 = λ t Tm15 var15 lam15 app tt pair fst snd left right case zero suc rec →
     lam15 _ _ _ (t Tm15 var15 lam15 app tt pair fst snd left right case zero suc rec)

app15 : ∀{Γ A B} → Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B; app15
 = λ t u Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec →
     app15 _ _ _ (t Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec)
         (u Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec)

tt15 : ∀{Γ} → Tm15 Γ top15; tt15
 = λ Tm15 var15 lam15 app15 tt15 pair fst snd left right case zero suc rec → tt15 _

pair15 : ∀{Γ A B} → Tm15 Γ A → Tm15 Γ B → Tm15 Γ (prod15 A B); pair15
 = λ t u Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec →
     pair15 _ _ _ (t Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec)
          (u Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec)

fst15 : ∀{Γ A B} → Tm15 Γ (prod15 A B) → Tm15 Γ A; fst15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd left right case zero suc rec →
     fst15 _ _ _ (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd left right case zero suc rec)

snd15 : ∀{Γ A B} → Tm15 Γ (prod15 A B) → Tm15 Γ B; snd15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left right case zero suc rec →
     snd15 _ _ _ (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left right case zero suc rec)

left15 : ∀{Γ A B} → Tm15 Γ A → Tm15 Γ (sum15 A B); left15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right case zero suc rec →
     left15 _ _ _ (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right case zero suc rec)

right15 : ∀{Γ A B} → Tm15 Γ B → Tm15 Γ (sum15 A B); right15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case zero suc rec →
     right15 _ _ _ (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case zero suc rec)

case15 : ∀{Γ A B C} → Tm15 Γ (sum15 A B) → Tm15 Γ (arr15 A C) → Tm15 Γ (arr15 B C) → Tm15 Γ C; case15
 = λ t u v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec →
     case15 _ _ _ _
           (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)
           (u Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)
           (v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)

zero15  : ∀{Γ} → Tm15 Γ nat15; zero15
 = λ Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc rec → zero15 _

suc15 : ∀{Γ} → Tm15 Γ nat15 → Tm15 Γ nat15; suc15
 = λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec →
   suc15 _ (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec)

rec15 : ∀{Γ A} → Tm15 Γ nat15 → Tm15 Γ (arr15 nat15 (arr15 A A)) → Tm15 Γ A → Tm15 Γ A; rec15
 = λ t u v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15 →
     rec15 _ _
          (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)
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
   (vz  : ∀ Γ A → Var16 (snoc16 Γ A) A)
   (vs  : ∀ Γ B A → Var16 Γ A → Var16 (snoc16 Γ B) A)
 → Var16 Γ A

vz16 : ∀{Γ A} → Var16 (snoc16 Γ A) A; vz16
 = λ Var16 vz16 vs → vz16 _ _

vs16 : ∀{Γ B A} → Var16 Γ A → Var16 (snoc16 Γ B) A; vs16
 = λ x Var16 vz16 vs16 → vs16 _ _ _ (x Var16 vz16 vs16)

Tm16 : Con16 → Ty16 → Set; Tm16
 = λ Γ A →
   (Tm16  : Con16 → Ty16 → Set)
   (var   : ∀ Γ A      → Var16 Γ A → Tm16 Γ A)
   (lam   : ∀ Γ A B    → Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B))
   (app   : ∀ Γ A B    → Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B)
   (tt    : ∀ Γ        → Tm16 Γ top16)
   (pair  : ∀ Γ A B    → Tm16 Γ A → Tm16 Γ B → Tm16 Γ (prod16 A B))
   (fst   : ∀ Γ A B    → Tm16 Γ (prod16 A B) → Tm16 Γ A)
   (snd   : ∀ Γ A B    → Tm16 Γ (prod16 A B) → Tm16 Γ B)
   (left  : ∀ Γ A B    → Tm16 Γ A → Tm16 Γ (sum16 A B))
   (right : ∀ Γ A B    → Tm16 Γ B → Tm16 Γ (sum16 A B))
   (case  : ∀ Γ A B C  → Tm16 Γ (sum16 A B) → Tm16 Γ (arr16 A C) → Tm16 Γ (arr16 B C) → Tm16 Γ C)
   (zero  : ∀ Γ        → Tm16 Γ nat16)
   (suc   : ∀ Γ        → Tm16 Γ nat16 → Tm16 Γ nat16)
   (rec   : ∀ Γ A      → Tm16 Γ nat16 → Tm16 Γ (arr16 nat16 (arr16 A A)) → Tm16 Γ A → Tm16 Γ A)
 → Tm16 Γ A

var16 : ∀{Γ A} → Var16 Γ A → Tm16 Γ A; var16
 = λ x Tm16 var16 lam app tt pair fst snd left right case zero suc rec →
     var16 _ _ x

lam16 : ∀{Γ A B} → Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B); lam16
 = λ t Tm16 var16 lam16 app tt pair fst snd left right case zero suc rec →
     lam16 _ _ _ (t Tm16 var16 lam16 app tt pair fst snd left right case zero suc rec)

app16 : ∀{Γ A B} → Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B; app16
 = λ t u Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec →
     app16 _ _ _ (t Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec)
         (u Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec)

tt16 : ∀{Γ} → Tm16 Γ top16; tt16
 = λ Tm16 var16 lam16 app16 tt16 pair fst snd left right case zero suc rec → tt16 _

pair16 : ∀{Γ A B} → Tm16 Γ A → Tm16 Γ B → Tm16 Γ (prod16 A B); pair16
 = λ t u Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec →
     pair16 _ _ _ (t Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec)
          (u Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec)

fst16 : ∀{Γ A B} → Tm16 Γ (prod16 A B) → Tm16 Γ A; fst16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd left right case zero suc rec →
     fst16 _ _ _ (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd left right case zero suc rec)

snd16 : ∀{Γ A B} → Tm16 Γ (prod16 A B) → Tm16 Γ B; snd16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left right case zero suc rec →
     snd16 _ _ _ (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left right case zero suc rec)

left16 : ∀{Γ A B} → Tm16 Γ A → Tm16 Γ (sum16 A B); left16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right case zero suc rec →
     left16 _ _ _ (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right case zero suc rec)

right16 : ∀{Γ A B} → Tm16 Γ B → Tm16 Γ (sum16 A B); right16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case zero suc rec →
     right16 _ _ _ (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case zero suc rec)

case16 : ∀{Γ A B C} → Tm16 Γ (sum16 A B) → Tm16 Γ (arr16 A C) → Tm16 Γ (arr16 B C) → Tm16 Γ C; case16
 = λ t u v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec →
     case16 _ _ _ _
           (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)
           (u Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)
           (v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)

zero16  : ∀{Γ} → Tm16 Γ nat16; zero16
 = λ Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc rec → zero16 _

suc16 : ∀{Γ} → Tm16 Γ nat16 → Tm16 Γ nat16; suc16
 = λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec →
   suc16 _ (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec)

rec16 : ∀{Γ A} → Tm16 Γ nat16 → Tm16 Γ (arr16 nat16 (arr16 A A)) → Tm16 Γ A → Tm16 Γ A; rec16
 = λ t u v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16 →
     rec16 _ _
          (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)
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
   (vz  : ∀ Γ A → Var17 (snoc17 Γ A) A)
   (vs  : ∀ Γ B A → Var17 Γ A → Var17 (snoc17 Γ B) A)
 → Var17 Γ A

vz17 : ∀{Γ A} → Var17 (snoc17 Γ A) A; vz17
 = λ Var17 vz17 vs → vz17 _ _

vs17 : ∀{Γ B A} → Var17 Γ A → Var17 (snoc17 Γ B) A; vs17
 = λ x Var17 vz17 vs17 → vs17 _ _ _ (x Var17 vz17 vs17)

Tm17 : Con17 → Ty17 → Set; Tm17
 = λ Γ A →
   (Tm17  : Con17 → Ty17 → Set)
   (var   : ∀ Γ A      → Var17 Γ A → Tm17 Γ A)
   (lam   : ∀ Γ A B    → Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B))
   (app   : ∀ Γ A B    → Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B)
   (tt    : ∀ Γ        → Tm17 Γ top17)
   (pair  : ∀ Γ A B    → Tm17 Γ A → Tm17 Γ B → Tm17 Γ (prod17 A B))
   (fst   : ∀ Γ A B    → Tm17 Γ (prod17 A B) → Tm17 Γ A)
   (snd   : ∀ Γ A B    → Tm17 Γ (prod17 A B) → Tm17 Γ B)
   (left  : ∀ Γ A B    → Tm17 Γ A → Tm17 Γ (sum17 A B))
   (right : ∀ Γ A B    → Tm17 Γ B → Tm17 Γ (sum17 A B))
   (case  : ∀ Γ A B C  → Tm17 Γ (sum17 A B) → Tm17 Γ (arr17 A C) → Tm17 Γ (arr17 B C) → Tm17 Γ C)
   (zero  : ∀ Γ        → Tm17 Γ nat17)
   (suc   : ∀ Γ        → Tm17 Γ nat17 → Tm17 Γ nat17)
   (rec   : ∀ Γ A      → Tm17 Γ nat17 → Tm17 Γ (arr17 nat17 (arr17 A A)) → Tm17 Γ A → Tm17 Γ A)
 → Tm17 Γ A

var17 : ∀{Γ A} → Var17 Γ A → Tm17 Γ A; var17
 = λ x Tm17 var17 lam app tt pair fst snd left right case zero suc rec →
     var17 _ _ x

lam17 : ∀{Γ A B} → Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B); lam17
 = λ t Tm17 var17 lam17 app tt pair fst snd left right case zero suc rec →
     lam17 _ _ _ (t Tm17 var17 lam17 app tt pair fst snd left right case zero suc rec)

app17 : ∀{Γ A B} → Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B; app17
 = λ t u Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec →
     app17 _ _ _ (t Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec)
         (u Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec)

tt17 : ∀{Γ} → Tm17 Γ top17; tt17
 = λ Tm17 var17 lam17 app17 tt17 pair fst snd left right case zero suc rec → tt17 _

pair17 : ∀{Γ A B} → Tm17 Γ A → Tm17 Γ B → Tm17 Γ (prod17 A B); pair17
 = λ t u Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec →
     pair17 _ _ _ (t Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec)
          (u Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec)

fst17 : ∀{Γ A B} → Tm17 Γ (prod17 A B) → Tm17 Γ A; fst17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd left right case zero suc rec →
     fst17 _ _ _ (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd left right case zero suc rec)

snd17 : ∀{Γ A B} → Tm17 Γ (prod17 A B) → Tm17 Γ B; snd17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left right case zero suc rec →
     snd17 _ _ _ (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left right case zero suc rec)

left17 : ∀{Γ A B} → Tm17 Γ A → Tm17 Γ (sum17 A B); left17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right case zero suc rec →
     left17 _ _ _ (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right case zero suc rec)

right17 : ∀{Γ A B} → Tm17 Γ B → Tm17 Γ (sum17 A B); right17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case zero suc rec →
     right17 _ _ _ (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case zero suc rec)

case17 : ∀{Γ A B C} → Tm17 Γ (sum17 A B) → Tm17 Γ (arr17 A C) → Tm17 Γ (arr17 B C) → Tm17 Γ C; case17
 = λ t u v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec →
     case17 _ _ _ _
           (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)
           (u Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)
           (v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)

zero17  : ∀{Γ} → Tm17 Γ nat17; zero17
 = λ Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc rec → zero17 _

suc17 : ∀{Γ} → Tm17 Γ nat17 → Tm17 Γ nat17; suc17
 = λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec →
   suc17 _ (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec)

rec17 : ∀{Γ A} → Tm17 Γ nat17 → Tm17 Γ (arr17 nat17 (arr17 A A)) → Tm17 Γ A → Tm17 Γ A; rec17
 = λ t u v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17 →
     rec17 _ _
          (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)
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
   (vz  : ∀ Γ A → Var18 (snoc18 Γ A) A)
   (vs  : ∀ Γ B A → Var18 Γ A → Var18 (snoc18 Γ B) A)
 → Var18 Γ A

vz18 : ∀{Γ A} → Var18 (snoc18 Γ A) A; vz18
 = λ Var18 vz18 vs → vz18 _ _

vs18 : ∀{Γ B A} → Var18 Γ A → Var18 (snoc18 Γ B) A; vs18
 = λ x Var18 vz18 vs18 → vs18 _ _ _ (x Var18 vz18 vs18)

Tm18 : Con18 → Ty18 → Set; Tm18
 = λ Γ A →
   (Tm18  : Con18 → Ty18 → Set)
   (var   : ∀ Γ A      → Var18 Γ A → Tm18 Γ A)
   (lam   : ∀ Γ A B    → Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B))
   (app   : ∀ Γ A B    → Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B)
   (tt    : ∀ Γ        → Tm18 Γ top18)
   (pair  : ∀ Γ A B    → Tm18 Γ A → Tm18 Γ B → Tm18 Γ (prod18 A B))
   (fst   : ∀ Γ A B    → Tm18 Γ (prod18 A B) → Tm18 Γ A)
   (snd   : ∀ Γ A B    → Tm18 Γ (prod18 A B) → Tm18 Γ B)
   (left  : ∀ Γ A B    → Tm18 Γ A → Tm18 Γ (sum18 A B))
   (right : ∀ Γ A B    → Tm18 Γ B → Tm18 Γ (sum18 A B))
   (case  : ∀ Γ A B C  → Tm18 Γ (sum18 A B) → Tm18 Γ (arr18 A C) → Tm18 Γ (arr18 B C) → Tm18 Γ C)
   (zero  : ∀ Γ        → Tm18 Γ nat18)
   (suc   : ∀ Γ        → Tm18 Γ nat18 → Tm18 Γ nat18)
   (rec   : ∀ Γ A      → Tm18 Γ nat18 → Tm18 Γ (arr18 nat18 (arr18 A A)) → Tm18 Γ A → Tm18 Γ A)
 → Tm18 Γ A

var18 : ∀{Γ A} → Var18 Γ A → Tm18 Γ A; var18
 = λ x Tm18 var18 lam app tt pair fst snd left right case zero suc rec →
     var18 _ _ x

lam18 : ∀{Γ A B} → Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B); lam18
 = λ t Tm18 var18 lam18 app tt pair fst snd left right case zero suc rec →
     lam18 _ _ _ (t Tm18 var18 lam18 app tt pair fst snd left right case zero suc rec)

app18 : ∀{Γ A B} → Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B; app18
 = λ t u Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec →
     app18 _ _ _ (t Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec)
         (u Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec)

tt18 : ∀{Γ} → Tm18 Γ top18; tt18
 = λ Tm18 var18 lam18 app18 tt18 pair fst snd left right case zero suc rec → tt18 _

pair18 : ∀{Γ A B} → Tm18 Γ A → Tm18 Γ B → Tm18 Γ (prod18 A B); pair18
 = λ t u Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec →
     pair18 _ _ _ (t Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec)
          (u Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec)

fst18 : ∀{Γ A B} → Tm18 Γ (prod18 A B) → Tm18 Γ A; fst18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd left right case zero suc rec →
     fst18 _ _ _ (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd left right case zero suc rec)

snd18 : ∀{Γ A B} → Tm18 Γ (prod18 A B) → Tm18 Γ B; snd18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left right case zero suc rec →
     snd18 _ _ _ (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left right case zero suc rec)

left18 : ∀{Γ A B} → Tm18 Γ A → Tm18 Γ (sum18 A B); left18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right case zero suc rec →
     left18 _ _ _ (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right case zero suc rec)

right18 : ∀{Γ A B} → Tm18 Γ B → Tm18 Γ (sum18 A B); right18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case zero suc rec →
     right18 _ _ _ (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case zero suc rec)

case18 : ∀{Γ A B C} → Tm18 Γ (sum18 A B) → Tm18 Γ (arr18 A C) → Tm18 Γ (arr18 B C) → Tm18 Γ C; case18
 = λ t u v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec →
     case18 _ _ _ _
           (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)
           (u Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)
           (v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)

zero18  : ∀{Γ} → Tm18 Γ nat18; zero18
 = λ Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc rec → zero18 _

suc18 : ∀{Γ} → Tm18 Γ nat18 → Tm18 Γ nat18; suc18
 = λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec →
   suc18 _ (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec)

rec18 : ∀{Γ A} → Tm18 Γ nat18 → Tm18 Γ (arr18 nat18 (arr18 A A)) → Tm18 Γ A → Tm18 Γ A; rec18
 = λ t u v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18 →
     rec18 _ _
          (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)
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
   (vz  : ∀ Γ A → Var19 (snoc19 Γ A) A)
   (vs  : ∀ Γ B A → Var19 Γ A → Var19 (snoc19 Γ B) A)
 → Var19 Γ A

vz19 : ∀{Γ A} → Var19 (snoc19 Γ A) A; vz19
 = λ Var19 vz19 vs → vz19 _ _

vs19 : ∀{Γ B A} → Var19 Γ A → Var19 (snoc19 Γ B) A; vs19
 = λ x Var19 vz19 vs19 → vs19 _ _ _ (x Var19 vz19 vs19)

Tm19 : Con19 → Ty19 → Set; Tm19
 = λ Γ A →
   (Tm19  : Con19 → Ty19 → Set)
   (var   : ∀ Γ A      → Var19 Γ A → Tm19 Γ A)
   (lam   : ∀ Γ A B    → Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B))
   (app   : ∀ Γ A B    → Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B)
   (tt    : ∀ Γ        → Tm19 Γ top19)
   (pair  : ∀ Γ A B    → Tm19 Γ A → Tm19 Γ B → Tm19 Γ (prod19 A B))
   (fst   : ∀ Γ A B    → Tm19 Γ (prod19 A B) → Tm19 Γ A)
   (snd   : ∀ Γ A B    → Tm19 Γ (prod19 A B) → Tm19 Γ B)
   (left  : ∀ Γ A B    → Tm19 Γ A → Tm19 Γ (sum19 A B))
   (right : ∀ Γ A B    → Tm19 Γ B → Tm19 Γ (sum19 A B))
   (case  : ∀ Γ A B C  → Tm19 Γ (sum19 A B) → Tm19 Γ (arr19 A C) → Tm19 Γ (arr19 B C) → Tm19 Γ C)
   (zero  : ∀ Γ        → Tm19 Γ nat19)
   (suc   : ∀ Γ        → Tm19 Γ nat19 → Tm19 Γ nat19)
   (rec   : ∀ Γ A      → Tm19 Γ nat19 → Tm19 Γ (arr19 nat19 (arr19 A A)) → Tm19 Γ A → Tm19 Γ A)
 → Tm19 Γ A

var19 : ∀{Γ A} → Var19 Γ A → Tm19 Γ A; var19
 = λ x Tm19 var19 lam app tt pair fst snd left right case zero suc rec →
     var19 _ _ x

lam19 : ∀{Γ A B} → Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B); lam19
 = λ t Tm19 var19 lam19 app tt pair fst snd left right case zero suc rec →
     lam19 _ _ _ (t Tm19 var19 lam19 app tt pair fst snd left right case zero suc rec)

app19 : ∀{Γ A B} → Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B; app19
 = λ t u Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec →
     app19 _ _ _ (t Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec)
         (u Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec)

tt19 : ∀{Γ} → Tm19 Γ top19; tt19
 = λ Tm19 var19 lam19 app19 tt19 pair fst snd left right case zero suc rec → tt19 _

pair19 : ∀{Γ A B} → Tm19 Γ A → Tm19 Γ B → Tm19 Γ (prod19 A B); pair19
 = λ t u Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec →
     pair19 _ _ _ (t Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec)
          (u Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec)

fst19 : ∀{Γ A B} → Tm19 Γ (prod19 A B) → Tm19 Γ A; fst19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd left right case zero suc rec →
     fst19 _ _ _ (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd left right case zero suc rec)

snd19 : ∀{Γ A B} → Tm19 Γ (prod19 A B) → Tm19 Γ B; snd19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left right case zero suc rec →
     snd19 _ _ _ (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left right case zero suc rec)

left19 : ∀{Γ A B} → Tm19 Γ A → Tm19 Γ (sum19 A B); left19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right case zero suc rec →
     left19 _ _ _ (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right case zero suc rec)

right19 : ∀{Γ A B} → Tm19 Γ B → Tm19 Γ (sum19 A B); right19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case zero suc rec →
     right19 _ _ _ (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case zero suc rec)

case19 : ∀{Γ A B C} → Tm19 Γ (sum19 A B) → Tm19 Γ (arr19 A C) → Tm19 Γ (arr19 B C) → Tm19 Γ C; case19
 = λ t u v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec →
     case19 _ _ _ _
           (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)
           (u Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)
           (v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)

zero19  : ∀{Γ} → Tm19 Γ nat19; zero19
 = λ Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc rec → zero19 _

suc19 : ∀{Γ} → Tm19 Γ nat19 → Tm19 Γ nat19; suc19
 = λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec →
   suc19 _ (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec)

rec19 : ∀{Γ A} → Tm19 Γ nat19 → Tm19 Γ (arr19 nat19 (arr19 A A)) → Tm19 Γ A → Tm19 Γ A; rec19
 = λ t u v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19 →
     rec19 _ _
          (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)
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
   (vz  : ∀ Γ A → Var20 (snoc20 Γ A) A)
   (vs  : ∀ Γ B A → Var20 Γ A → Var20 (snoc20 Γ B) A)
 → Var20 Γ A

vz20 : ∀{Γ A} → Var20 (snoc20 Γ A) A; vz20
 = λ Var20 vz20 vs → vz20 _ _

vs20 : ∀{Γ B A} → Var20 Γ A → Var20 (snoc20 Γ B) A; vs20
 = λ x Var20 vz20 vs20 → vs20 _ _ _ (x Var20 vz20 vs20)

Tm20 : Con20 → Ty20 → Set; Tm20
 = λ Γ A →
   (Tm20  : Con20 → Ty20 → Set)
   (var   : ∀ Γ A      → Var20 Γ A → Tm20 Γ A)
   (lam   : ∀ Γ A B    → Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B))
   (app   : ∀ Γ A B    → Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B)
   (tt    : ∀ Γ        → Tm20 Γ top20)
   (pair  : ∀ Γ A B    → Tm20 Γ A → Tm20 Γ B → Tm20 Γ (prod20 A B))
   (fst   : ∀ Γ A B    → Tm20 Γ (prod20 A B) → Tm20 Γ A)
   (snd   : ∀ Γ A B    → Tm20 Γ (prod20 A B) → Tm20 Γ B)
   (left  : ∀ Γ A B    → Tm20 Γ A → Tm20 Γ (sum20 A B))
   (right : ∀ Γ A B    → Tm20 Γ B → Tm20 Γ (sum20 A B))
   (case  : ∀ Γ A B C  → Tm20 Γ (sum20 A B) → Tm20 Γ (arr20 A C) → Tm20 Γ (arr20 B C) → Tm20 Γ C)
   (zero  : ∀ Γ        → Tm20 Γ nat20)
   (suc   : ∀ Γ        → Tm20 Γ nat20 → Tm20 Γ nat20)
   (rec   : ∀ Γ A      → Tm20 Γ nat20 → Tm20 Γ (arr20 nat20 (arr20 A A)) → Tm20 Γ A → Tm20 Γ A)
 → Tm20 Γ A

var20 : ∀{Γ A} → Var20 Γ A → Tm20 Γ A; var20
 = λ x Tm20 var20 lam app tt pair fst snd left right case zero suc rec →
     var20 _ _ x

lam20 : ∀{Γ A B} → Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B); lam20
 = λ t Tm20 var20 lam20 app tt pair fst snd left right case zero suc rec →
     lam20 _ _ _ (t Tm20 var20 lam20 app tt pair fst snd left right case zero suc rec)

app20 : ∀{Γ A B} → Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B; app20
 = λ t u Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec →
     app20 _ _ _ (t Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec)
         (u Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec)

tt20 : ∀{Γ} → Tm20 Γ top20; tt20
 = λ Tm20 var20 lam20 app20 tt20 pair fst snd left right case zero suc rec → tt20 _

pair20 : ∀{Γ A B} → Tm20 Γ A → Tm20 Γ B → Tm20 Γ (prod20 A B); pair20
 = λ t u Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec →
     pair20 _ _ _ (t Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec)
          (u Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec)

fst20 : ∀{Γ A B} → Tm20 Γ (prod20 A B) → Tm20 Γ A; fst20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd left right case zero suc rec →
     fst20 _ _ _ (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd left right case zero suc rec)

snd20 : ∀{Γ A B} → Tm20 Γ (prod20 A B) → Tm20 Γ B; snd20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left right case zero suc rec →
     snd20 _ _ _ (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left right case zero suc rec)

left20 : ∀{Γ A B} → Tm20 Γ A → Tm20 Γ (sum20 A B); left20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right case zero suc rec →
     left20 _ _ _ (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right case zero suc rec)

right20 : ∀{Γ A B} → Tm20 Γ B → Tm20 Γ (sum20 A B); right20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case zero suc rec →
     right20 _ _ _ (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case zero suc rec)

case20 : ∀{Γ A B C} → Tm20 Γ (sum20 A B) → Tm20 Γ (arr20 A C) → Tm20 Γ (arr20 B C) → Tm20 Γ C; case20
 = λ t u v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec →
     case20 _ _ _ _
           (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)
           (u Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)
           (v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)

zero20  : ∀{Γ} → Tm20 Γ nat20; zero20
 = λ Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc rec → zero20 _

suc20 : ∀{Γ} → Tm20 Γ nat20 → Tm20 Γ nat20; suc20
 = λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec →
   suc20 _ (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec)

rec20 : ∀{Γ A} → Tm20 Γ nat20 → Tm20 Γ (arr20 nat20 (arr20 A A)) → Tm20 Γ A → Tm20 Γ A; rec20
 = λ t u v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20 →
     rec20 _ _
          (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)
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
   (vz  : ∀ Γ A → Var21 (snoc21 Γ A) A)
   (vs  : ∀ Γ B A → Var21 Γ A → Var21 (snoc21 Γ B) A)
 → Var21 Γ A

vz21 : ∀{Γ A} → Var21 (snoc21 Γ A) A; vz21
 = λ Var21 vz21 vs → vz21 _ _

vs21 : ∀{Γ B A} → Var21 Γ A → Var21 (snoc21 Γ B) A; vs21
 = λ x Var21 vz21 vs21 → vs21 _ _ _ (x Var21 vz21 vs21)

Tm21 : Con21 → Ty21 → Set; Tm21
 = λ Γ A →
   (Tm21  : Con21 → Ty21 → Set)
   (var   : ∀ Γ A      → Var21 Γ A → Tm21 Γ A)
   (lam   : ∀ Γ A B    → Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B))
   (app   : ∀ Γ A B    → Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B)
   (tt    : ∀ Γ        → Tm21 Γ top21)
   (pair  : ∀ Γ A B    → Tm21 Γ A → Tm21 Γ B → Tm21 Γ (prod21 A B))
   (fst   : ∀ Γ A B    → Tm21 Γ (prod21 A B) → Tm21 Γ A)
   (snd   : ∀ Γ A B    → Tm21 Γ (prod21 A B) → Tm21 Γ B)
   (left  : ∀ Γ A B    → Tm21 Γ A → Tm21 Γ (sum21 A B))
   (right : ∀ Γ A B    → Tm21 Γ B → Tm21 Γ (sum21 A B))
   (case  : ∀ Γ A B C  → Tm21 Γ (sum21 A B) → Tm21 Γ (arr21 A C) → Tm21 Γ (arr21 B C) → Tm21 Γ C)
   (zero  : ∀ Γ        → Tm21 Γ nat21)
   (suc   : ∀ Γ        → Tm21 Γ nat21 → Tm21 Γ nat21)
   (rec   : ∀ Γ A      → Tm21 Γ nat21 → Tm21 Γ (arr21 nat21 (arr21 A A)) → Tm21 Γ A → Tm21 Γ A)
 → Tm21 Γ A

var21 : ∀{Γ A} → Var21 Γ A → Tm21 Γ A; var21
 = λ x Tm21 var21 lam app tt pair fst snd left right case zero suc rec →
     var21 _ _ x

lam21 : ∀{Γ A B} → Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B); lam21
 = λ t Tm21 var21 lam21 app tt pair fst snd left right case zero suc rec →
     lam21 _ _ _ (t Tm21 var21 lam21 app tt pair fst snd left right case zero suc rec)

app21 : ∀{Γ A B} → Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B; app21
 = λ t u Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec →
     app21 _ _ _ (t Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec)
         (u Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec)

tt21 : ∀{Γ} → Tm21 Γ top21; tt21
 = λ Tm21 var21 lam21 app21 tt21 pair fst snd left right case zero suc rec → tt21 _

pair21 : ∀{Γ A B} → Tm21 Γ A → Tm21 Γ B → Tm21 Γ (prod21 A B); pair21
 = λ t u Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec →
     pair21 _ _ _ (t Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec)
          (u Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec)

fst21 : ∀{Γ A B} → Tm21 Γ (prod21 A B) → Tm21 Γ A; fst21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd left right case zero suc rec →
     fst21 _ _ _ (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd left right case zero suc rec)

snd21 : ∀{Γ A B} → Tm21 Γ (prod21 A B) → Tm21 Γ B; snd21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left right case zero suc rec →
     snd21 _ _ _ (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left right case zero suc rec)

left21 : ∀{Γ A B} → Tm21 Γ A → Tm21 Γ (sum21 A B); left21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right case zero suc rec →
     left21 _ _ _ (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right case zero suc rec)

right21 : ∀{Γ A B} → Tm21 Γ B → Tm21 Γ (sum21 A B); right21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case zero suc rec →
     right21 _ _ _ (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case zero suc rec)

case21 : ∀{Γ A B C} → Tm21 Γ (sum21 A B) → Tm21 Γ (arr21 A C) → Tm21 Γ (arr21 B C) → Tm21 Γ C; case21
 = λ t u v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec →
     case21 _ _ _ _
           (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)
           (u Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)
           (v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)

zero21  : ∀{Γ} → Tm21 Γ nat21; zero21
 = λ Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc rec → zero21 _

suc21 : ∀{Γ} → Tm21 Γ nat21 → Tm21 Γ nat21; suc21
 = λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec →
   suc21 _ (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec)

rec21 : ∀{Γ A} → Tm21 Γ nat21 → Tm21 Γ (arr21 nat21 (arr21 A A)) → Tm21 Γ A → Tm21 Γ A; rec21
 = λ t u v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21 →
     rec21 _ _
          (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)
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
   (vz  : ∀ Γ A → Var22 (snoc22 Γ A) A)
   (vs  : ∀ Γ B A → Var22 Γ A → Var22 (snoc22 Γ B) A)
 → Var22 Γ A

vz22 : ∀{Γ A} → Var22 (snoc22 Γ A) A; vz22
 = λ Var22 vz22 vs → vz22 _ _

vs22 : ∀{Γ B A} → Var22 Γ A → Var22 (snoc22 Γ B) A; vs22
 = λ x Var22 vz22 vs22 → vs22 _ _ _ (x Var22 vz22 vs22)

Tm22 : Con22 → Ty22 → Set; Tm22
 = λ Γ A →
   (Tm22  : Con22 → Ty22 → Set)
   (var   : ∀ Γ A      → Var22 Γ A → Tm22 Γ A)
   (lam   : ∀ Γ A B    → Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B))
   (app   : ∀ Γ A B    → Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B)
   (tt    : ∀ Γ        → Tm22 Γ top22)
   (pair  : ∀ Γ A B    → Tm22 Γ A → Tm22 Γ B → Tm22 Γ (prod22 A B))
   (fst   : ∀ Γ A B    → Tm22 Γ (prod22 A B) → Tm22 Γ A)
   (snd   : ∀ Γ A B    → Tm22 Γ (prod22 A B) → Tm22 Γ B)
   (left  : ∀ Γ A B    → Tm22 Γ A → Tm22 Γ (sum22 A B))
   (right : ∀ Γ A B    → Tm22 Γ B → Tm22 Γ (sum22 A B))
   (case  : ∀ Γ A B C  → Tm22 Γ (sum22 A B) → Tm22 Γ (arr22 A C) → Tm22 Γ (arr22 B C) → Tm22 Γ C)
   (zero  : ∀ Γ        → Tm22 Γ nat22)
   (suc   : ∀ Γ        → Tm22 Γ nat22 → Tm22 Γ nat22)
   (rec   : ∀ Γ A      → Tm22 Γ nat22 → Tm22 Γ (arr22 nat22 (arr22 A A)) → Tm22 Γ A → Tm22 Γ A)
 → Tm22 Γ A

var22 : ∀{Γ A} → Var22 Γ A → Tm22 Γ A; var22
 = λ x Tm22 var22 lam app tt pair fst snd left right case zero suc rec →
     var22 _ _ x

lam22 : ∀{Γ A B} → Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B); lam22
 = λ t Tm22 var22 lam22 app tt pair fst snd left right case zero suc rec →
     lam22 _ _ _ (t Tm22 var22 lam22 app tt pair fst snd left right case zero suc rec)

app22 : ∀{Γ A B} → Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B; app22
 = λ t u Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec →
     app22 _ _ _ (t Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec)
         (u Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec)

tt22 : ∀{Γ} → Tm22 Γ top22; tt22
 = λ Tm22 var22 lam22 app22 tt22 pair fst snd left right case zero suc rec → tt22 _

pair22 : ∀{Γ A B} → Tm22 Γ A → Tm22 Γ B → Tm22 Γ (prod22 A B); pair22
 = λ t u Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec →
     pair22 _ _ _ (t Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec)
          (u Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec)

fst22 : ∀{Γ A B} → Tm22 Γ (prod22 A B) → Tm22 Γ A; fst22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd left right case zero suc rec →
     fst22 _ _ _ (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd left right case zero suc rec)

snd22 : ∀{Γ A B} → Tm22 Γ (prod22 A B) → Tm22 Γ B; snd22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left right case zero suc rec →
     snd22 _ _ _ (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left right case zero suc rec)

left22 : ∀{Γ A B} → Tm22 Γ A → Tm22 Γ (sum22 A B); left22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right case zero suc rec →
     left22 _ _ _ (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right case zero suc rec)

right22 : ∀{Γ A B} → Tm22 Γ B → Tm22 Γ (sum22 A B); right22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case zero suc rec →
     right22 _ _ _ (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case zero suc rec)

case22 : ∀{Γ A B C} → Tm22 Γ (sum22 A B) → Tm22 Γ (arr22 A C) → Tm22 Γ (arr22 B C) → Tm22 Γ C; case22
 = λ t u v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec →
     case22 _ _ _ _
           (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)
           (u Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)
           (v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)

zero22  : ∀{Γ} → Tm22 Γ nat22; zero22
 = λ Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc rec → zero22 _

suc22 : ∀{Γ} → Tm22 Γ nat22 → Tm22 Γ nat22; suc22
 = λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec →
   suc22 _ (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec)

rec22 : ∀{Γ A} → Tm22 Γ nat22 → Tm22 Γ (arr22 nat22 (arr22 A A)) → Tm22 Γ A → Tm22 Γ A; rec22
 = λ t u v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22 →
     rec22 _ _
          (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)
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
   (vz  : ∀ Γ A → Var23 (snoc23 Γ A) A)
   (vs  : ∀ Γ B A → Var23 Γ A → Var23 (snoc23 Γ B) A)
 → Var23 Γ A

vz23 : ∀{Γ A} → Var23 (snoc23 Γ A) A; vz23
 = λ Var23 vz23 vs → vz23 _ _

vs23 : ∀{Γ B A} → Var23 Γ A → Var23 (snoc23 Γ B) A; vs23
 = λ x Var23 vz23 vs23 → vs23 _ _ _ (x Var23 vz23 vs23)

Tm23 : Con23 → Ty23 → Set; Tm23
 = λ Γ A →
   (Tm23  : Con23 → Ty23 → Set)
   (var   : ∀ Γ A      → Var23 Γ A → Tm23 Γ A)
   (lam   : ∀ Γ A B    → Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B))
   (app   : ∀ Γ A B    → Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B)
   (tt    : ∀ Γ        → Tm23 Γ top23)
   (pair  : ∀ Γ A B    → Tm23 Γ A → Tm23 Γ B → Tm23 Γ (prod23 A B))
   (fst   : ∀ Γ A B    → Tm23 Γ (prod23 A B) → Tm23 Γ A)
   (snd   : ∀ Γ A B    → Tm23 Γ (prod23 A B) → Tm23 Γ B)
   (left  : ∀ Γ A B    → Tm23 Γ A → Tm23 Γ (sum23 A B))
   (right : ∀ Γ A B    → Tm23 Γ B → Tm23 Γ (sum23 A B))
   (case  : ∀ Γ A B C  → Tm23 Γ (sum23 A B) → Tm23 Γ (arr23 A C) → Tm23 Γ (arr23 B C) → Tm23 Γ C)
   (zero  : ∀ Γ        → Tm23 Γ nat23)
   (suc   : ∀ Γ        → Tm23 Γ nat23 → Tm23 Γ nat23)
   (rec   : ∀ Γ A      → Tm23 Γ nat23 → Tm23 Γ (arr23 nat23 (arr23 A A)) → Tm23 Γ A → Tm23 Γ A)
 → Tm23 Γ A

var23 : ∀{Γ A} → Var23 Γ A → Tm23 Γ A; var23
 = λ x Tm23 var23 lam app tt pair fst snd left right case zero suc rec →
     var23 _ _ x

lam23 : ∀{Γ A B} → Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B); lam23
 = λ t Tm23 var23 lam23 app tt pair fst snd left right case zero suc rec →
     lam23 _ _ _ (t Tm23 var23 lam23 app tt pair fst snd left right case zero suc rec)

app23 : ∀{Γ A B} → Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B; app23
 = λ t u Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec →
     app23 _ _ _ (t Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec)
         (u Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec)

tt23 : ∀{Γ} → Tm23 Γ top23; tt23
 = λ Tm23 var23 lam23 app23 tt23 pair fst snd left right case zero suc rec → tt23 _

pair23 : ∀{Γ A B} → Tm23 Γ A → Tm23 Γ B → Tm23 Γ (prod23 A B); pair23
 = λ t u Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec →
     pair23 _ _ _ (t Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec)
          (u Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec)

fst23 : ∀{Γ A B} → Tm23 Γ (prod23 A B) → Tm23 Γ A; fst23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd left right case zero suc rec →
     fst23 _ _ _ (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd left right case zero suc rec)

snd23 : ∀{Γ A B} → Tm23 Γ (prod23 A B) → Tm23 Γ B; snd23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left right case zero suc rec →
     snd23 _ _ _ (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left right case zero suc rec)

left23 : ∀{Γ A B} → Tm23 Γ A → Tm23 Γ (sum23 A B); left23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right case zero suc rec →
     left23 _ _ _ (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right case zero suc rec)

right23 : ∀{Γ A B} → Tm23 Γ B → Tm23 Γ (sum23 A B); right23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case zero suc rec →
     right23 _ _ _ (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case zero suc rec)

case23 : ∀{Γ A B C} → Tm23 Γ (sum23 A B) → Tm23 Γ (arr23 A C) → Tm23 Γ (arr23 B C) → Tm23 Γ C; case23
 = λ t u v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec →
     case23 _ _ _ _
           (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)
           (u Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)
           (v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)

zero23  : ∀{Γ} → Tm23 Γ nat23; zero23
 = λ Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc rec → zero23 _

suc23 : ∀{Γ} → Tm23 Γ nat23 → Tm23 Γ nat23; suc23
 = λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec →
   suc23 _ (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec)

rec23 : ∀{Γ A} → Tm23 Γ nat23 → Tm23 Γ (arr23 nat23 (arr23 A A)) → Tm23 Γ A → Tm23 Γ A; rec23
 = λ t u v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23 →
     rec23 _ _
          (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)
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
   (vz  : ∀ Γ A → Var24 (snoc24 Γ A) A)
   (vs  : ∀ Γ B A → Var24 Γ A → Var24 (snoc24 Γ B) A)
 → Var24 Γ A

vz24 : ∀{Γ A} → Var24 (snoc24 Γ A) A; vz24
 = λ Var24 vz24 vs → vz24 _ _

vs24 : ∀{Γ B A} → Var24 Γ A → Var24 (snoc24 Γ B) A; vs24
 = λ x Var24 vz24 vs24 → vs24 _ _ _ (x Var24 vz24 vs24)

Tm24 : Con24 → Ty24 → Set; Tm24
 = λ Γ A →
   (Tm24  : Con24 → Ty24 → Set)
   (var   : ∀ Γ A      → Var24 Γ A → Tm24 Γ A)
   (lam   : ∀ Γ A B    → Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B))
   (app   : ∀ Γ A B    → Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B)
   (tt    : ∀ Γ        → Tm24 Γ top24)
   (pair  : ∀ Γ A B    → Tm24 Γ A → Tm24 Γ B → Tm24 Γ (prod24 A B))
   (fst   : ∀ Γ A B    → Tm24 Γ (prod24 A B) → Tm24 Γ A)
   (snd   : ∀ Γ A B    → Tm24 Γ (prod24 A B) → Tm24 Γ B)
   (left  : ∀ Γ A B    → Tm24 Γ A → Tm24 Γ (sum24 A B))
   (right : ∀ Γ A B    → Tm24 Γ B → Tm24 Γ (sum24 A B))
   (case  : ∀ Γ A B C  → Tm24 Γ (sum24 A B) → Tm24 Γ (arr24 A C) → Tm24 Γ (arr24 B C) → Tm24 Γ C)
   (zero  : ∀ Γ        → Tm24 Γ nat24)
   (suc   : ∀ Γ        → Tm24 Γ nat24 → Tm24 Γ nat24)
   (rec   : ∀ Γ A      → Tm24 Γ nat24 → Tm24 Γ (arr24 nat24 (arr24 A A)) → Tm24 Γ A → Tm24 Γ A)
 → Tm24 Γ A

var24 : ∀{Γ A} → Var24 Γ A → Tm24 Γ A; var24
 = λ x Tm24 var24 lam app tt pair fst snd left right case zero suc rec →
     var24 _ _ x

lam24 : ∀{Γ A B} → Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B); lam24
 = λ t Tm24 var24 lam24 app tt pair fst snd left right case zero suc rec →
     lam24 _ _ _ (t Tm24 var24 lam24 app tt pair fst snd left right case zero suc rec)

app24 : ∀{Γ A B} → Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B; app24
 = λ t u Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec →
     app24 _ _ _ (t Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec)
         (u Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec)

tt24 : ∀{Γ} → Tm24 Γ top24; tt24
 = λ Tm24 var24 lam24 app24 tt24 pair fst snd left right case zero suc rec → tt24 _

pair24 : ∀{Γ A B} → Tm24 Γ A → Tm24 Γ B → Tm24 Γ (prod24 A B); pair24
 = λ t u Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec →
     pair24 _ _ _ (t Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec)
          (u Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec)

fst24 : ∀{Γ A B} → Tm24 Γ (prod24 A B) → Tm24 Γ A; fst24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd left right case zero suc rec →
     fst24 _ _ _ (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd left right case zero suc rec)

snd24 : ∀{Γ A B} → Tm24 Γ (prod24 A B) → Tm24 Γ B; snd24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left right case zero suc rec →
     snd24 _ _ _ (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left right case zero suc rec)

left24 : ∀{Γ A B} → Tm24 Γ A → Tm24 Γ (sum24 A B); left24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right case zero suc rec →
     left24 _ _ _ (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right case zero suc rec)

right24 : ∀{Γ A B} → Tm24 Γ B → Tm24 Γ (sum24 A B); right24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case zero suc rec →
     right24 _ _ _ (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case zero suc rec)

case24 : ∀{Γ A B C} → Tm24 Γ (sum24 A B) → Tm24 Γ (arr24 A C) → Tm24 Γ (arr24 B C) → Tm24 Γ C; case24
 = λ t u v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec →
     case24 _ _ _ _
           (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)
           (u Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)
           (v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)

zero24  : ∀{Γ} → Tm24 Γ nat24; zero24
 = λ Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc rec → zero24 _

suc24 : ∀{Γ} → Tm24 Γ nat24 → Tm24 Γ nat24; suc24
 = λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec →
   suc24 _ (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec)

rec24 : ∀{Γ A} → Tm24 Γ nat24 → Tm24 Γ (arr24 nat24 (arr24 A A)) → Tm24 Γ A → Tm24 Γ A; rec24
 = λ t u v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24 →
     rec24 _ _
          (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)
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
   (vz  : ∀ Γ A → Var25 (snoc25 Γ A) A)
   (vs  : ∀ Γ B A → Var25 Γ A → Var25 (snoc25 Γ B) A)
 → Var25 Γ A

vz25 : ∀{Γ A} → Var25 (snoc25 Γ A) A; vz25
 = λ Var25 vz25 vs → vz25 _ _

vs25 : ∀{Γ B A} → Var25 Γ A → Var25 (snoc25 Γ B) A; vs25
 = λ x Var25 vz25 vs25 → vs25 _ _ _ (x Var25 vz25 vs25)

Tm25 : Con25 → Ty25 → Set; Tm25
 = λ Γ A →
   (Tm25  : Con25 → Ty25 → Set)
   (var   : ∀ Γ A      → Var25 Γ A → Tm25 Γ A)
   (lam   : ∀ Γ A B    → Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B))
   (app   : ∀ Γ A B    → Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B)
   (tt    : ∀ Γ        → Tm25 Γ top25)
   (pair  : ∀ Γ A B    → Tm25 Γ A → Tm25 Γ B → Tm25 Γ (prod25 A B))
   (fst   : ∀ Γ A B    → Tm25 Γ (prod25 A B) → Tm25 Γ A)
   (snd   : ∀ Γ A B    → Tm25 Γ (prod25 A B) → Tm25 Γ B)
   (left  : ∀ Γ A B    → Tm25 Γ A → Tm25 Γ (sum25 A B))
   (right : ∀ Γ A B    → Tm25 Γ B → Tm25 Γ (sum25 A B))
   (case  : ∀ Γ A B C  → Tm25 Γ (sum25 A B) → Tm25 Γ (arr25 A C) → Tm25 Γ (arr25 B C) → Tm25 Γ C)
   (zero  : ∀ Γ        → Tm25 Γ nat25)
   (suc   : ∀ Γ        → Tm25 Γ nat25 → Tm25 Γ nat25)
   (rec   : ∀ Γ A      → Tm25 Γ nat25 → Tm25 Γ (arr25 nat25 (arr25 A A)) → Tm25 Γ A → Tm25 Γ A)
 → Tm25 Γ A

var25 : ∀{Γ A} → Var25 Γ A → Tm25 Γ A; var25
 = λ x Tm25 var25 lam app tt pair fst snd left right case zero suc rec →
     var25 _ _ x

lam25 : ∀{Γ A B} → Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B); lam25
 = λ t Tm25 var25 lam25 app tt pair fst snd left right case zero suc rec →
     lam25 _ _ _ (t Tm25 var25 lam25 app tt pair fst snd left right case zero suc rec)

app25 : ∀{Γ A B} → Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B; app25
 = λ t u Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec →
     app25 _ _ _ (t Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec)
         (u Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec)

tt25 : ∀{Γ} → Tm25 Γ top25; tt25
 = λ Tm25 var25 lam25 app25 tt25 pair fst snd left right case zero suc rec → tt25 _

pair25 : ∀{Γ A B} → Tm25 Γ A → Tm25 Γ B → Tm25 Γ (prod25 A B); pair25
 = λ t u Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec →
     pair25 _ _ _ (t Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec)
          (u Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec)

fst25 : ∀{Γ A B} → Tm25 Γ (prod25 A B) → Tm25 Γ A; fst25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd left right case zero suc rec →
     fst25 _ _ _ (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd left right case zero suc rec)

snd25 : ∀{Γ A B} → Tm25 Γ (prod25 A B) → Tm25 Γ B; snd25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left right case zero suc rec →
     snd25 _ _ _ (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left right case zero suc rec)

left25 : ∀{Γ A B} → Tm25 Γ A → Tm25 Γ (sum25 A B); left25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right case zero suc rec →
     left25 _ _ _ (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right case zero suc rec)

right25 : ∀{Γ A B} → Tm25 Γ B → Tm25 Γ (sum25 A B); right25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case zero suc rec →
     right25 _ _ _ (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case zero suc rec)

case25 : ∀{Γ A B C} → Tm25 Γ (sum25 A B) → Tm25 Γ (arr25 A C) → Tm25 Γ (arr25 B C) → Tm25 Γ C; case25
 = λ t u v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec →
     case25 _ _ _ _
           (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)
           (u Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)
           (v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)

zero25  : ∀{Γ} → Tm25 Γ nat25; zero25
 = λ Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc rec → zero25 _

suc25 : ∀{Γ} → Tm25 Γ nat25 → Tm25 Γ nat25; suc25
 = λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec →
   suc25 _ (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec)

rec25 : ∀{Γ A} → Tm25 Γ nat25 → Tm25 Γ (arr25 nat25 (arr25 A A)) → Tm25 Γ A → Tm25 Γ A; rec25
 = λ t u v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25 →
     rec25 _ _
          (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)
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
   (vz  : ∀ Γ A → Var26 (snoc26 Γ A) A)
   (vs  : ∀ Γ B A → Var26 Γ A → Var26 (snoc26 Γ B) A)
 → Var26 Γ A

vz26 : ∀{Γ A} → Var26 (snoc26 Γ A) A; vz26
 = λ Var26 vz26 vs → vz26 _ _

vs26 : ∀{Γ B A} → Var26 Γ A → Var26 (snoc26 Γ B) A; vs26
 = λ x Var26 vz26 vs26 → vs26 _ _ _ (x Var26 vz26 vs26)

Tm26 : Con26 → Ty26 → Set; Tm26
 = λ Γ A →
   (Tm26  : Con26 → Ty26 → Set)
   (var   : ∀ Γ A      → Var26 Γ A → Tm26 Γ A)
   (lam   : ∀ Γ A B    → Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B))
   (app   : ∀ Γ A B    → Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B)
   (tt    : ∀ Γ        → Tm26 Γ top26)
   (pair  : ∀ Γ A B    → Tm26 Γ A → Tm26 Γ B → Tm26 Γ (prod26 A B))
   (fst   : ∀ Γ A B    → Tm26 Γ (prod26 A B) → Tm26 Γ A)
   (snd   : ∀ Γ A B    → Tm26 Γ (prod26 A B) → Tm26 Γ B)
   (left  : ∀ Γ A B    → Tm26 Γ A → Tm26 Γ (sum26 A B))
   (right : ∀ Γ A B    → Tm26 Γ B → Tm26 Γ (sum26 A B))
   (case  : ∀ Γ A B C  → Tm26 Γ (sum26 A B) → Tm26 Γ (arr26 A C) → Tm26 Γ (arr26 B C) → Tm26 Γ C)
   (zero  : ∀ Γ        → Tm26 Γ nat26)
   (suc   : ∀ Γ        → Tm26 Γ nat26 → Tm26 Γ nat26)
   (rec   : ∀ Γ A      → Tm26 Γ nat26 → Tm26 Γ (arr26 nat26 (arr26 A A)) → Tm26 Γ A → Tm26 Γ A)
 → Tm26 Γ A

var26 : ∀{Γ A} → Var26 Γ A → Tm26 Γ A; var26
 = λ x Tm26 var26 lam app tt pair fst snd left right case zero suc rec →
     var26 _ _ x

lam26 : ∀{Γ A B} → Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B); lam26
 = λ t Tm26 var26 lam26 app tt pair fst snd left right case zero suc rec →
     lam26 _ _ _ (t Tm26 var26 lam26 app tt pair fst snd left right case zero suc rec)

app26 : ∀{Γ A B} → Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B; app26
 = λ t u Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec →
     app26 _ _ _ (t Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec)
         (u Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec)

tt26 : ∀{Γ} → Tm26 Γ top26; tt26
 = λ Tm26 var26 lam26 app26 tt26 pair fst snd left right case zero suc rec → tt26 _

pair26 : ∀{Γ A B} → Tm26 Γ A → Tm26 Γ B → Tm26 Γ (prod26 A B); pair26
 = λ t u Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec →
     pair26 _ _ _ (t Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec)
          (u Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec)

fst26 : ∀{Γ A B} → Tm26 Γ (prod26 A B) → Tm26 Γ A; fst26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd left right case zero suc rec →
     fst26 _ _ _ (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd left right case zero suc rec)

snd26 : ∀{Γ A B} → Tm26 Γ (prod26 A B) → Tm26 Γ B; snd26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left right case zero suc rec →
     snd26 _ _ _ (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left right case zero suc rec)

left26 : ∀{Γ A B} → Tm26 Γ A → Tm26 Γ (sum26 A B); left26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right case zero suc rec →
     left26 _ _ _ (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right case zero suc rec)

right26 : ∀{Γ A B} → Tm26 Γ B → Tm26 Γ (sum26 A B); right26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case zero suc rec →
     right26 _ _ _ (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case zero suc rec)

case26 : ∀{Γ A B C} → Tm26 Γ (sum26 A B) → Tm26 Γ (arr26 A C) → Tm26 Γ (arr26 B C) → Tm26 Γ C; case26
 = λ t u v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec →
     case26 _ _ _ _
           (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)
           (u Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)
           (v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)

zero26  : ∀{Γ} → Tm26 Γ nat26; zero26
 = λ Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc rec → zero26 _

suc26 : ∀{Γ} → Tm26 Γ nat26 → Tm26 Γ nat26; suc26
 = λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec →
   suc26 _ (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec)

rec26 : ∀{Γ A} → Tm26 Γ nat26 → Tm26 Γ (arr26 nat26 (arr26 A A)) → Tm26 Γ A → Tm26 Γ A; rec26
 = λ t u v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26 →
     rec26 _ _
          (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)
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
   (vz  : ∀ Γ A → Var27 (snoc27 Γ A) A)
   (vs  : ∀ Γ B A → Var27 Γ A → Var27 (snoc27 Γ B) A)
 → Var27 Γ A

vz27 : ∀{Γ A} → Var27 (snoc27 Γ A) A; vz27
 = λ Var27 vz27 vs → vz27 _ _

vs27 : ∀{Γ B A} → Var27 Γ A → Var27 (snoc27 Γ B) A; vs27
 = λ x Var27 vz27 vs27 → vs27 _ _ _ (x Var27 vz27 vs27)

Tm27 : Con27 → Ty27 → Set; Tm27
 = λ Γ A →
   (Tm27  : Con27 → Ty27 → Set)
   (var   : ∀ Γ A      → Var27 Γ A → Tm27 Γ A)
   (lam   : ∀ Γ A B    → Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B))
   (app   : ∀ Γ A B    → Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B)
   (tt    : ∀ Γ        → Tm27 Γ top27)
   (pair  : ∀ Γ A B    → Tm27 Γ A → Tm27 Γ B → Tm27 Γ (prod27 A B))
   (fst   : ∀ Γ A B    → Tm27 Γ (prod27 A B) → Tm27 Γ A)
   (snd   : ∀ Γ A B    → Tm27 Γ (prod27 A B) → Tm27 Γ B)
   (left  : ∀ Γ A B    → Tm27 Γ A → Tm27 Γ (sum27 A B))
   (right : ∀ Γ A B    → Tm27 Γ B → Tm27 Γ (sum27 A B))
   (case  : ∀ Γ A B C  → Tm27 Γ (sum27 A B) → Tm27 Γ (arr27 A C) → Tm27 Γ (arr27 B C) → Tm27 Γ C)
   (zero  : ∀ Γ        → Tm27 Γ nat27)
   (suc   : ∀ Γ        → Tm27 Γ nat27 → Tm27 Γ nat27)
   (rec   : ∀ Γ A      → Tm27 Γ nat27 → Tm27 Γ (arr27 nat27 (arr27 A A)) → Tm27 Γ A → Tm27 Γ A)
 → Tm27 Γ A

var27 : ∀{Γ A} → Var27 Γ A → Tm27 Γ A; var27
 = λ x Tm27 var27 lam app tt pair fst snd left right case zero suc rec →
     var27 _ _ x

lam27 : ∀{Γ A B} → Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B); lam27
 = λ t Tm27 var27 lam27 app tt pair fst snd left right case zero suc rec →
     lam27 _ _ _ (t Tm27 var27 lam27 app tt pair fst snd left right case zero suc rec)

app27 : ∀{Γ A B} → Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B; app27
 = λ t u Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec →
     app27 _ _ _ (t Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec)
         (u Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec)

tt27 : ∀{Γ} → Tm27 Γ top27; tt27
 = λ Tm27 var27 lam27 app27 tt27 pair fst snd left right case zero suc rec → tt27 _

pair27 : ∀{Γ A B} → Tm27 Γ A → Tm27 Γ B → Tm27 Γ (prod27 A B); pair27
 = λ t u Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec →
     pair27 _ _ _ (t Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec)
          (u Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec)

fst27 : ∀{Γ A B} → Tm27 Γ (prod27 A B) → Tm27 Γ A; fst27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd left right case zero suc rec →
     fst27 _ _ _ (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd left right case zero suc rec)

snd27 : ∀{Γ A B} → Tm27 Γ (prod27 A B) → Tm27 Γ B; snd27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left right case zero suc rec →
     snd27 _ _ _ (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left right case zero suc rec)

left27 : ∀{Γ A B} → Tm27 Γ A → Tm27 Γ (sum27 A B); left27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right case zero suc rec →
     left27 _ _ _ (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right case zero suc rec)

right27 : ∀{Γ A B} → Tm27 Γ B → Tm27 Γ (sum27 A B); right27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case zero suc rec →
     right27 _ _ _ (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case zero suc rec)

case27 : ∀{Γ A B C} → Tm27 Γ (sum27 A B) → Tm27 Γ (arr27 A C) → Tm27 Γ (arr27 B C) → Tm27 Γ C; case27
 = λ t u v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec →
     case27 _ _ _ _
           (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)
           (u Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)
           (v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)

zero27  : ∀{Γ} → Tm27 Γ nat27; zero27
 = λ Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc rec → zero27 _

suc27 : ∀{Γ} → Tm27 Γ nat27 → Tm27 Γ nat27; suc27
 = λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec →
   suc27 _ (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec)

rec27 : ∀{Γ A} → Tm27 Γ nat27 → Tm27 Γ (arr27 nat27 (arr27 A A)) → Tm27 Γ A → Tm27 Γ A; rec27
 = λ t u v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27 →
     rec27 _ _
          (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)
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
   (vz  : ∀ Γ A → Var28 (snoc28 Γ A) A)
   (vs  : ∀ Γ B A → Var28 Γ A → Var28 (snoc28 Γ B) A)
 → Var28 Γ A

vz28 : ∀{Γ A} → Var28 (snoc28 Γ A) A; vz28
 = λ Var28 vz28 vs → vz28 _ _

vs28 : ∀{Γ B A} → Var28 Γ A → Var28 (snoc28 Γ B) A; vs28
 = λ x Var28 vz28 vs28 → vs28 _ _ _ (x Var28 vz28 vs28)

Tm28 : Con28 → Ty28 → Set; Tm28
 = λ Γ A →
   (Tm28  : Con28 → Ty28 → Set)
   (var   : ∀ Γ A      → Var28 Γ A → Tm28 Γ A)
   (lam   : ∀ Γ A B    → Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B))
   (app   : ∀ Γ A B    → Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B)
   (tt    : ∀ Γ        → Tm28 Γ top28)
   (pair  : ∀ Γ A B    → Tm28 Γ A → Tm28 Γ B → Tm28 Γ (prod28 A B))
   (fst   : ∀ Γ A B    → Tm28 Γ (prod28 A B) → Tm28 Γ A)
   (snd   : ∀ Γ A B    → Tm28 Γ (prod28 A B) → Tm28 Γ B)
   (left  : ∀ Γ A B    → Tm28 Γ A → Tm28 Γ (sum28 A B))
   (right : ∀ Γ A B    → Tm28 Γ B → Tm28 Γ (sum28 A B))
   (case  : ∀ Γ A B C  → Tm28 Γ (sum28 A B) → Tm28 Γ (arr28 A C) → Tm28 Γ (arr28 B C) → Tm28 Γ C)
   (zero  : ∀ Γ        → Tm28 Γ nat28)
   (suc   : ∀ Γ        → Tm28 Γ nat28 → Tm28 Γ nat28)
   (rec   : ∀ Γ A      → Tm28 Γ nat28 → Tm28 Γ (arr28 nat28 (arr28 A A)) → Tm28 Γ A → Tm28 Γ A)
 → Tm28 Γ A

var28 : ∀{Γ A} → Var28 Γ A → Tm28 Γ A; var28
 = λ x Tm28 var28 lam app tt pair fst snd left right case zero suc rec →
     var28 _ _ x

lam28 : ∀{Γ A B} → Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B); lam28
 = λ t Tm28 var28 lam28 app tt pair fst snd left right case zero suc rec →
     lam28 _ _ _ (t Tm28 var28 lam28 app tt pair fst snd left right case zero suc rec)

app28 : ∀{Γ A B} → Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B; app28
 = λ t u Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec →
     app28 _ _ _ (t Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec)
         (u Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec)

tt28 : ∀{Γ} → Tm28 Γ top28; tt28
 = λ Tm28 var28 lam28 app28 tt28 pair fst snd left right case zero suc rec → tt28 _

pair28 : ∀{Γ A B} → Tm28 Γ A → Tm28 Γ B → Tm28 Γ (prod28 A B); pair28
 = λ t u Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec →
     pair28 _ _ _ (t Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec)
          (u Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec)

fst28 : ∀{Γ A B} → Tm28 Γ (prod28 A B) → Tm28 Γ A; fst28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd left right case zero suc rec →
     fst28 _ _ _ (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd left right case zero suc rec)

snd28 : ∀{Γ A B} → Tm28 Γ (prod28 A B) → Tm28 Γ B; snd28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left right case zero suc rec →
     snd28 _ _ _ (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left right case zero suc rec)

left28 : ∀{Γ A B} → Tm28 Γ A → Tm28 Γ (sum28 A B); left28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right case zero suc rec →
     left28 _ _ _ (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right case zero suc rec)

right28 : ∀{Γ A B} → Tm28 Γ B → Tm28 Γ (sum28 A B); right28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case zero suc rec →
     right28 _ _ _ (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case zero suc rec)

case28 : ∀{Γ A B C} → Tm28 Γ (sum28 A B) → Tm28 Γ (arr28 A C) → Tm28 Γ (arr28 B C) → Tm28 Γ C; case28
 = λ t u v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec →
     case28 _ _ _ _
           (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)
           (u Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)
           (v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)

zero28  : ∀{Γ} → Tm28 Γ nat28; zero28
 = λ Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc rec → zero28 _

suc28 : ∀{Γ} → Tm28 Γ nat28 → Tm28 Γ nat28; suc28
 = λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec →
   suc28 _ (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec)

rec28 : ∀{Γ A} → Tm28 Γ nat28 → Tm28 Γ (arr28 nat28 (arr28 A A)) → Tm28 Γ A → Tm28 Γ A; rec28
 = λ t u v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28 →
     rec28 _ _
          (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)
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
   (vz  : ∀ Γ A → Var29 (snoc29 Γ A) A)
   (vs  : ∀ Γ B A → Var29 Γ A → Var29 (snoc29 Γ B) A)
 → Var29 Γ A

vz29 : ∀{Γ A} → Var29 (snoc29 Γ A) A; vz29
 = λ Var29 vz29 vs → vz29 _ _

vs29 : ∀{Γ B A} → Var29 Γ A → Var29 (snoc29 Γ B) A; vs29
 = λ x Var29 vz29 vs29 → vs29 _ _ _ (x Var29 vz29 vs29)

Tm29 : Con29 → Ty29 → Set; Tm29
 = λ Γ A →
   (Tm29  : Con29 → Ty29 → Set)
   (var   : ∀ Γ A      → Var29 Γ A → Tm29 Γ A)
   (lam   : ∀ Γ A B    → Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B))
   (app   : ∀ Γ A B    → Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B)
   (tt    : ∀ Γ        → Tm29 Γ top29)
   (pair  : ∀ Γ A B    → Tm29 Γ A → Tm29 Γ B → Tm29 Γ (prod29 A B))
   (fst   : ∀ Γ A B    → Tm29 Γ (prod29 A B) → Tm29 Γ A)
   (snd   : ∀ Γ A B    → Tm29 Γ (prod29 A B) → Tm29 Γ B)
   (left  : ∀ Γ A B    → Tm29 Γ A → Tm29 Γ (sum29 A B))
   (right : ∀ Γ A B    → Tm29 Γ B → Tm29 Γ (sum29 A B))
   (case  : ∀ Γ A B C  → Tm29 Γ (sum29 A B) → Tm29 Γ (arr29 A C) → Tm29 Γ (arr29 B C) → Tm29 Γ C)
   (zero  : ∀ Γ        → Tm29 Γ nat29)
   (suc   : ∀ Γ        → Tm29 Γ nat29 → Tm29 Γ nat29)
   (rec   : ∀ Γ A      → Tm29 Γ nat29 → Tm29 Γ (arr29 nat29 (arr29 A A)) → Tm29 Γ A → Tm29 Γ A)
 → Tm29 Γ A

var29 : ∀{Γ A} → Var29 Γ A → Tm29 Γ A; var29
 = λ x Tm29 var29 lam app tt pair fst snd left right case zero suc rec →
     var29 _ _ x

lam29 : ∀{Γ A B} → Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B); lam29
 = λ t Tm29 var29 lam29 app tt pair fst snd left right case zero suc rec →
     lam29 _ _ _ (t Tm29 var29 lam29 app tt pair fst snd left right case zero suc rec)

app29 : ∀{Γ A B} → Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B; app29
 = λ t u Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec →
     app29 _ _ _ (t Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec)
         (u Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec)

tt29 : ∀{Γ} → Tm29 Γ top29; tt29
 = λ Tm29 var29 lam29 app29 tt29 pair fst snd left right case zero suc rec → tt29 _

pair29 : ∀{Γ A B} → Tm29 Γ A → Tm29 Γ B → Tm29 Γ (prod29 A B); pair29
 = λ t u Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec →
     pair29 _ _ _ (t Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec)
          (u Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec)

fst29 : ∀{Γ A B} → Tm29 Γ (prod29 A B) → Tm29 Γ A; fst29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd left right case zero suc rec →
     fst29 _ _ _ (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd left right case zero suc rec)

snd29 : ∀{Γ A B} → Tm29 Γ (prod29 A B) → Tm29 Γ B; snd29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left right case zero suc rec →
     snd29 _ _ _ (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left right case zero suc rec)

left29 : ∀{Γ A B} → Tm29 Γ A → Tm29 Γ (sum29 A B); left29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right case zero suc rec →
     left29 _ _ _ (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right case zero suc rec)

right29 : ∀{Γ A B} → Tm29 Γ B → Tm29 Γ (sum29 A B); right29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case zero suc rec →
     right29 _ _ _ (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case zero suc rec)

case29 : ∀{Γ A B C} → Tm29 Γ (sum29 A B) → Tm29 Γ (arr29 A C) → Tm29 Γ (arr29 B C) → Tm29 Γ C; case29
 = λ t u v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec →
     case29 _ _ _ _
           (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)
           (u Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)
           (v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)

zero29  : ∀{Γ} → Tm29 Γ nat29; zero29
 = λ Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc rec → zero29 _

suc29 : ∀{Γ} → Tm29 Γ nat29 → Tm29 Γ nat29; suc29
 = λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec →
   suc29 _ (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec)

rec29 : ∀{Γ A} → Tm29 Γ nat29 → Tm29 Γ (arr29 nat29 (arr29 A A)) → Tm29 Γ A → Tm29 Γ A; rec29
 = λ t u v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29 →
     rec29 _ _
          (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)
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
   (vz  : ∀ Γ A → Var30 (snoc30 Γ A) A)
   (vs  : ∀ Γ B A → Var30 Γ A → Var30 (snoc30 Γ B) A)
 → Var30 Γ A

vz30 : ∀{Γ A} → Var30 (snoc30 Γ A) A; vz30
 = λ Var30 vz30 vs → vz30 _ _

vs30 : ∀{Γ B A} → Var30 Γ A → Var30 (snoc30 Γ B) A; vs30
 = λ x Var30 vz30 vs30 → vs30 _ _ _ (x Var30 vz30 vs30)

Tm30 : Con30 → Ty30 → Set; Tm30
 = λ Γ A →
   (Tm30  : Con30 → Ty30 → Set)
   (var   : ∀ Γ A      → Var30 Γ A → Tm30 Γ A)
   (lam   : ∀ Γ A B    → Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B))
   (app   : ∀ Γ A B    → Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B)
   (tt    : ∀ Γ        → Tm30 Γ top30)
   (pair  : ∀ Γ A B    → Tm30 Γ A → Tm30 Γ B → Tm30 Γ (prod30 A B))
   (fst   : ∀ Γ A B    → Tm30 Γ (prod30 A B) → Tm30 Γ A)
   (snd   : ∀ Γ A B    → Tm30 Γ (prod30 A B) → Tm30 Γ B)
   (left  : ∀ Γ A B    → Tm30 Γ A → Tm30 Γ (sum30 A B))
   (right : ∀ Γ A B    → Tm30 Γ B → Tm30 Γ (sum30 A B))
   (case  : ∀ Γ A B C  → Tm30 Γ (sum30 A B) → Tm30 Γ (arr30 A C) → Tm30 Γ (arr30 B C) → Tm30 Γ C)
   (zero  : ∀ Γ        → Tm30 Γ nat30)
   (suc   : ∀ Γ        → Tm30 Γ nat30 → Tm30 Γ nat30)
   (rec   : ∀ Γ A      → Tm30 Γ nat30 → Tm30 Γ (arr30 nat30 (arr30 A A)) → Tm30 Γ A → Tm30 Γ A)
 → Tm30 Γ A

var30 : ∀{Γ A} → Var30 Γ A → Tm30 Γ A; var30
 = λ x Tm30 var30 lam app tt pair fst snd left right case zero suc rec →
     var30 _ _ x

lam30 : ∀{Γ A B} → Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B); lam30
 = λ t Tm30 var30 lam30 app tt pair fst snd left right case zero suc rec →
     lam30 _ _ _ (t Tm30 var30 lam30 app tt pair fst snd left right case zero suc rec)

app30 : ∀{Γ A B} → Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B; app30
 = λ t u Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec →
     app30 _ _ _ (t Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec)
         (u Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec)

tt30 : ∀{Γ} → Tm30 Γ top30; tt30
 = λ Tm30 var30 lam30 app30 tt30 pair fst snd left right case zero suc rec → tt30 _

pair30 : ∀{Γ A B} → Tm30 Γ A → Tm30 Γ B → Tm30 Γ (prod30 A B); pair30
 = λ t u Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec →
     pair30 _ _ _ (t Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec)
          (u Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec)

fst30 : ∀{Γ A B} → Tm30 Γ (prod30 A B) → Tm30 Γ A; fst30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd left right case zero suc rec →
     fst30 _ _ _ (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd left right case zero suc rec)

snd30 : ∀{Γ A B} → Tm30 Γ (prod30 A B) → Tm30 Γ B; snd30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left right case zero suc rec →
     snd30 _ _ _ (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left right case zero suc rec)

left30 : ∀{Γ A B} → Tm30 Γ A → Tm30 Γ (sum30 A B); left30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right case zero suc rec →
     left30 _ _ _ (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right case zero suc rec)

right30 : ∀{Γ A B} → Tm30 Γ B → Tm30 Γ (sum30 A B); right30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case zero suc rec →
     right30 _ _ _ (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case zero suc rec)

case30 : ∀{Γ A B C} → Tm30 Γ (sum30 A B) → Tm30 Γ (arr30 A C) → Tm30 Γ (arr30 B C) → Tm30 Γ C; case30
 = λ t u v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec →
     case30 _ _ _ _
           (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)
           (u Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)
           (v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)

zero30  : ∀{Γ} → Tm30 Γ nat30; zero30
 = λ Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc rec → zero30 _

suc30 : ∀{Γ} → Tm30 Γ nat30 → Tm30 Γ nat30; suc30
 = λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec →
   suc30 _ (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec)

rec30 : ∀{Γ A} → Tm30 Γ nat30 → Tm30 Γ (arr30 nat30 (arr30 A A)) → Tm30 Γ A → Tm30 Γ A; rec30
 = λ t u v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30 →
     rec30 _ _
          (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)
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
   (vz  : ∀ Γ A → Var31 (snoc31 Γ A) A)
   (vs  : ∀ Γ B A → Var31 Γ A → Var31 (snoc31 Γ B) A)
 → Var31 Γ A

vz31 : ∀{Γ A} → Var31 (snoc31 Γ A) A; vz31
 = λ Var31 vz31 vs → vz31 _ _

vs31 : ∀{Γ B A} → Var31 Γ A → Var31 (snoc31 Γ B) A; vs31
 = λ x Var31 vz31 vs31 → vs31 _ _ _ (x Var31 vz31 vs31)

Tm31 : Con31 → Ty31 → Set; Tm31
 = λ Γ A →
   (Tm31  : Con31 → Ty31 → Set)
   (var   : ∀ Γ A      → Var31 Γ A → Tm31 Γ A)
   (lam   : ∀ Γ A B    → Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B))
   (app   : ∀ Γ A B    → Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B)
   (tt    : ∀ Γ        → Tm31 Γ top31)
   (pair  : ∀ Γ A B    → Tm31 Γ A → Tm31 Γ B → Tm31 Γ (prod31 A B))
   (fst   : ∀ Γ A B    → Tm31 Γ (prod31 A B) → Tm31 Γ A)
   (snd   : ∀ Γ A B    → Tm31 Γ (prod31 A B) → Tm31 Γ B)
   (left  : ∀ Γ A B    → Tm31 Γ A → Tm31 Γ (sum31 A B))
   (right : ∀ Γ A B    → Tm31 Γ B → Tm31 Γ (sum31 A B))
   (case  : ∀ Γ A B C  → Tm31 Γ (sum31 A B) → Tm31 Γ (arr31 A C) → Tm31 Γ (arr31 B C) → Tm31 Γ C)
   (zero  : ∀ Γ        → Tm31 Γ nat31)
   (suc   : ∀ Γ        → Tm31 Γ nat31 → Tm31 Γ nat31)
   (rec   : ∀ Γ A      → Tm31 Γ nat31 → Tm31 Γ (arr31 nat31 (arr31 A A)) → Tm31 Γ A → Tm31 Γ A)
 → Tm31 Γ A

var31 : ∀{Γ A} → Var31 Γ A → Tm31 Γ A; var31
 = λ x Tm31 var31 lam app tt pair fst snd left right case zero suc rec →
     var31 _ _ x

lam31 : ∀{Γ A B} → Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B); lam31
 = λ t Tm31 var31 lam31 app tt pair fst snd left right case zero suc rec →
     lam31 _ _ _ (t Tm31 var31 lam31 app tt pair fst snd left right case zero suc rec)

app31 : ∀{Γ A B} → Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B; app31
 = λ t u Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec →
     app31 _ _ _ (t Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec)
         (u Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec)

tt31 : ∀{Γ} → Tm31 Γ top31; tt31
 = λ Tm31 var31 lam31 app31 tt31 pair fst snd left right case zero suc rec → tt31 _

pair31 : ∀{Γ A B} → Tm31 Γ A → Tm31 Γ B → Tm31 Γ (prod31 A B); pair31
 = λ t u Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec →
     pair31 _ _ _ (t Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec)
          (u Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec)

fst31 : ∀{Γ A B} → Tm31 Γ (prod31 A B) → Tm31 Γ A; fst31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd left right case zero suc rec →
     fst31 _ _ _ (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd left right case zero suc rec)

snd31 : ∀{Γ A B} → Tm31 Γ (prod31 A B) → Tm31 Γ B; snd31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left right case zero suc rec →
     snd31 _ _ _ (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left right case zero suc rec)

left31 : ∀{Γ A B} → Tm31 Γ A → Tm31 Γ (sum31 A B); left31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right case zero suc rec →
     left31 _ _ _ (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right case zero suc rec)

right31 : ∀{Γ A B} → Tm31 Γ B → Tm31 Γ (sum31 A B); right31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case zero suc rec →
     right31 _ _ _ (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case zero suc rec)

case31 : ∀{Γ A B C} → Tm31 Γ (sum31 A B) → Tm31 Γ (arr31 A C) → Tm31 Γ (arr31 B C) → Tm31 Γ C; case31
 = λ t u v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec →
     case31 _ _ _ _
           (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)
           (u Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)
           (v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)

zero31  : ∀{Γ} → Tm31 Γ nat31; zero31
 = λ Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc rec → zero31 _

suc31 : ∀{Γ} → Tm31 Γ nat31 → Tm31 Γ nat31; suc31
 = λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec →
   suc31 _ (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec)

rec31 : ∀{Γ A} → Tm31 Γ nat31 → Tm31 Γ (arr31 nat31 (arr31 A A)) → Tm31 Γ A → Tm31 Γ A; rec31
 = λ t u v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31 →
     rec31 _ _
          (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)
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
   (vz  : ∀ Γ A → Var32 (snoc32 Γ A) A)
   (vs  : ∀ Γ B A → Var32 Γ A → Var32 (snoc32 Γ B) A)
 → Var32 Γ A

vz32 : ∀{Γ A} → Var32 (snoc32 Γ A) A; vz32
 = λ Var32 vz32 vs → vz32 _ _

vs32 : ∀{Γ B A} → Var32 Γ A → Var32 (snoc32 Γ B) A; vs32
 = λ x Var32 vz32 vs32 → vs32 _ _ _ (x Var32 vz32 vs32)

Tm32 : Con32 → Ty32 → Set; Tm32
 = λ Γ A →
   (Tm32  : Con32 → Ty32 → Set)
   (var   : ∀ Γ A      → Var32 Γ A → Tm32 Γ A)
   (lam   : ∀ Γ A B    → Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B))
   (app   : ∀ Γ A B    → Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B)
   (tt    : ∀ Γ        → Tm32 Γ top32)
   (pair  : ∀ Γ A B    → Tm32 Γ A → Tm32 Γ B → Tm32 Γ (prod32 A B))
   (fst   : ∀ Γ A B    → Tm32 Γ (prod32 A B) → Tm32 Γ A)
   (snd   : ∀ Γ A B    → Tm32 Γ (prod32 A B) → Tm32 Γ B)
   (left  : ∀ Γ A B    → Tm32 Γ A → Tm32 Γ (sum32 A B))
   (right : ∀ Γ A B    → Tm32 Γ B → Tm32 Γ (sum32 A B))
   (case  : ∀ Γ A B C  → Tm32 Γ (sum32 A B) → Tm32 Γ (arr32 A C) → Tm32 Γ (arr32 B C) → Tm32 Γ C)
   (zero  : ∀ Γ        → Tm32 Γ nat32)
   (suc   : ∀ Γ        → Tm32 Γ nat32 → Tm32 Γ nat32)
   (rec   : ∀ Γ A      → Tm32 Γ nat32 → Tm32 Γ (arr32 nat32 (arr32 A A)) → Tm32 Γ A → Tm32 Γ A)
 → Tm32 Γ A

var32 : ∀{Γ A} → Var32 Γ A → Tm32 Γ A; var32
 = λ x Tm32 var32 lam app tt pair fst snd left right case zero suc rec →
     var32 _ _ x

lam32 : ∀{Γ A B} → Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B); lam32
 = λ t Tm32 var32 lam32 app tt pair fst snd left right case zero suc rec →
     lam32 _ _ _ (t Tm32 var32 lam32 app tt pair fst snd left right case zero suc rec)

app32 : ∀{Γ A B} → Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B; app32
 = λ t u Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec →
     app32 _ _ _ (t Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec)
         (u Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec)

tt32 : ∀{Γ} → Tm32 Γ top32; tt32
 = λ Tm32 var32 lam32 app32 tt32 pair fst snd left right case zero suc rec → tt32 _

pair32 : ∀{Γ A B} → Tm32 Γ A → Tm32 Γ B → Tm32 Γ (prod32 A B); pair32
 = λ t u Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec →
     pair32 _ _ _ (t Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec)
          (u Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec)

fst32 : ∀{Γ A B} → Tm32 Γ (prod32 A B) → Tm32 Γ A; fst32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd left right case zero suc rec →
     fst32 _ _ _ (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd left right case zero suc rec)

snd32 : ∀{Γ A B} → Tm32 Γ (prod32 A B) → Tm32 Γ B; snd32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left right case zero suc rec →
     snd32 _ _ _ (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left right case zero suc rec)

left32 : ∀{Γ A B} → Tm32 Γ A → Tm32 Γ (sum32 A B); left32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right case zero suc rec →
     left32 _ _ _ (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right case zero suc rec)

right32 : ∀{Γ A B} → Tm32 Γ B → Tm32 Γ (sum32 A B); right32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case zero suc rec →
     right32 _ _ _ (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case zero suc rec)

case32 : ∀{Γ A B C} → Tm32 Γ (sum32 A B) → Tm32 Γ (arr32 A C) → Tm32 Γ (arr32 B C) → Tm32 Γ C; case32
 = λ t u v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec →
     case32 _ _ _ _
           (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)
           (u Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)
           (v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)

zero32  : ∀{Γ} → Tm32 Γ nat32; zero32
 = λ Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc rec → zero32 _

suc32 : ∀{Γ} → Tm32 Γ nat32 → Tm32 Γ nat32; suc32
 = λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec →
   suc32 _ (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec)

rec32 : ∀{Γ A} → Tm32 Γ nat32 → Tm32 Γ (arr32 nat32 (arr32 A A)) → Tm32 Γ A → Tm32 Γ A; rec32
 = λ t u v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32 →
     rec32 _ _
          (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)
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
   (vz  : ∀ Γ A → Var33 (snoc33 Γ A) A)
   (vs  : ∀ Γ B A → Var33 Γ A → Var33 (snoc33 Γ B) A)
 → Var33 Γ A

vz33 : ∀{Γ A} → Var33 (snoc33 Γ A) A; vz33
 = λ Var33 vz33 vs → vz33 _ _

vs33 : ∀{Γ B A} → Var33 Γ A → Var33 (snoc33 Γ B) A; vs33
 = λ x Var33 vz33 vs33 → vs33 _ _ _ (x Var33 vz33 vs33)

Tm33 : Con33 → Ty33 → Set; Tm33
 = λ Γ A →
   (Tm33  : Con33 → Ty33 → Set)
   (var   : ∀ Γ A      → Var33 Γ A → Tm33 Γ A)
   (lam   : ∀ Γ A B    → Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B))
   (app   : ∀ Γ A B    → Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B)
   (tt    : ∀ Γ        → Tm33 Γ top33)
   (pair  : ∀ Γ A B    → Tm33 Γ A → Tm33 Γ B → Tm33 Γ (prod33 A B))
   (fst   : ∀ Γ A B    → Tm33 Γ (prod33 A B) → Tm33 Γ A)
   (snd   : ∀ Γ A B    → Tm33 Γ (prod33 A B) → Tm33 Γ B)
   (left  : ∀ Γ A B    → Tm33 Γ A → Tm33 Γ (sum33 A B))
   (right : ∀ Γ A B    → Tm33 Γ B → Tm33 Γ (sum33 A B))
   (case  : ∀ Γ A B C  → Tm33 Γ (sum33 A B) → Tm33 Γ (arr33 A C) → Tm33 Γ (arr33 B C) → Tm33 Γ C)
   (zero  : ∀ Γ        → Tm33 Γ nat33)
   (suc   : ∀ Γ        → Tm33 Γ nat33 → Tm33 Γ nat33)
   (rec   : ∀ Γ A      → Tm33 Γ nat33 → Tm33 Γ (arr33 nat33 (arr33 A A)) → Tm33 Γ A → Tm33 Γ A)
 → Tm33 Γ A

var33 : ∀{Γ A} → Var33 Γ A → Tm33 Γ A; var33
 = λ x Tm33 var33 lam app tt pair fst snd left right case zero suc rec →
     var33 _ _ x

lam33 : ∀{Γ A B} → Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B); lam33
 = λ t Tm33 var33 lam33 app tt pair fst snd left right case zero suc rec →
     lam33 _ _ _ (t Tm33 var33 lam33 app tt pair fst snd left right case zero suc rec)

app33 : ∀{Γ A B} → Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B; app33
 = λ t u Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec →
     app33 _ _ _ (t Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec)
         (u Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec)

tt33 : ∀{Γ} → Tm33 Γ top33; tt33
 = λ Tm33 var33 lam33 app33 tt33 pair fst snd left right case zero suc rec → tt33 _

pair33 : ∀{Γ A B} → Tm33 Γ A → Tm33 Γ B → Tm33 Γ (prod33 A B); pair33
 = λ t u Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec →
     pair33 _ _ _ (t Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec)
          (u Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec)

fst33 : ∀{Γ A B} → Tm33 Γ (prod33 A B) → Tm33 Γ A; fst33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd left right case zero suc rec →
     fst33 _ _ _ (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd left right case zero suc rec)

snd33 : ∀{Γ A B} → Tm33 Γ (prod33 A B) → Tm33 Γ B; snd33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left right case zero suc rec →
     snd33 _ _ _ (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left right case zero suc rec)

left33 : ∀{Γ A B} → Tm33 Γ A → Tm33 Γ (sum33 A B); left33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right case zero suc rec →
     left33 _ _ _ (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right case zero suc rec)

right33 : ∀{Γ A B} → Tm33 Γ B → Tm33 Γ (sum33 A B); right33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case zero suc rec →
     right33 _ _ _ (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case zero suc rec)

case33 : ∀{Γ A B C} → Tm33 Γ (sum33 A B) → Tm33 Γ (arr33 A C) → Tm33 Γ (arr33 B C) → Tm33 Γ C; case33
 = λ t u v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec →
     case33 _ _ _ _
           (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)
           (u Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)
           (v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)

zero33  : ∀{Γ} → Tm33 Γ nat33; zero33
 = λ Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc rec → zero33 _

suc33 : ∀{Γ} → Tm33 Γ nat33 → Tm33 Γ nat33; suc33
 = λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec →
   suc33 _ (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec)

rec33 : ∀{Γ A} → Tm33 Γ nat33 → Tm33 Γ (arr33 nat33 (arr33 A A)) → Tm33 Γ A → Tm33 Γ A; rec33
 = λ t u v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33 →
     rec33 _ _
          (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)
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
   (vz  : ∀ Γ A → Var34 (snoc34 Γ A) A)
   (vs  : ∀ Γ B A → Var34 Γ A → Var34 (snoc34 Γ B) A)
 → Var34 Γ A

vz34 : ∀{Γ A} → Var34 (snoc34 Γ A) A; vz34
 = λ Var34 vz34 vs → vz34 _ _

vs34 : ∀{Γ B A} → Var34 Γ A → Var34 (snoc34 Γ B) A; vs34
 = λ x Var34 vz34 vs34 → vs34 _ _ _ (x Var34 vz34 vs34)

Tm34 : Con34 → Ty34 → Set; Tm34
 = λ Γ A →
   (Tm34  : Con34 → Ty34 → Set)
   (var   : ∀ Γ A      → Var34 Γ A → Tm34 Γ A)
   (lam   : ∀ Γ A B    → Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B))
   (app   : ∀ Γ A B    → Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B)
   (tt    : ∀ Γ        → Tm34 Γ top34)
   (pair  : ∀ Γ A B    → Tm34 Γ A → Tm34 Γ B → Tm34 Γ (prod34 A B))
   (fst   : ∀ Γ A B    → Tm34 Γ (prod34 A B) → Tm34 Γ A)
   (snd   : ∀ Γ A B    → Tm34 Γ (prod34 A B) → Tm34 Γ B)
   (left  : ∀ Γ A B    → Tm34 Γ A → Tm34 Γ (sum34 A B))
   (right : ∀ Γ A B    → Tm34 Γ B → Tm34 Γ (sum34 A B))
   (case  : ∀ Γ A B C  → Tm34 Γ (sum34 A B) → Tm34 Γ (arr34 A C) → Tm34 Γ (arr34 B C) → Tm34 Γ C)
   (zero  : ∀ Γ        → Tm34 Γ nat34)
   (suc   : ∀ Γ        → Tm34 Γ nat34 → Tm34 Γ nat34)
   (rec   : ∀ Γ A      → Tm34 Γ nat34 → Tm34 Γ (arr34 nat34 (arr34 A A)) → Tm34 Γ A → Tm34 Γ A)
 → Tm34 Γ A

var34 : ∀{Γ A} → Var34 Γ A → Tm34 Γ A; var34
 = λ x Tm34 var34 lam app tt pair fst snd left right case zero suc rec →
     var34 _ _ x

lam34 : ∀{Γ A B} → Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B); lam34
 = λ t Tm34 var34 lam34 app tt pair fst snd left right case zero suc rec →
     lam34 _ _ _ (t Tm34 var34 lam34 app tt pair fst snd left right case zero suc rec)

app34 : ∀{Γ A B} → Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B; app34
 = λ t u Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec →
     app34 _ _ _ (t Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec)
         (u Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec)

tt34 : ∀{Γ} → Tm34 Γ top34; tt34
 = λ Tm34 var34 lam34 app34 tt34 pair fst snd left right case zero suc rec → tt34 _

pair34 : ∀{Γ A B} → Tm34 Γ A → Tm34 Γ B → Tm34 Γ (prod34 A B); pair34
 = λ t u Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec →
     pair34 _ _ _ (t Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec)
          (u Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec)

fst34 : ∀{Γ A B} → Tm34 Γ (prod34 A B) → Tm34 Γ A; fst34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd left right case zero suc rec →
     fst34 _ _ _ (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd left right case zero suc rec)

snd34 : ∀{Γ A B} → Tm34 Γ (prod34 A B) → Tm34 Γ B; snd34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left right case zero suc rec →
     snd34 _ _ _ (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left right case zero suc rec)

left34 : ∀{Γ A B} → Tm34 Γ A → Tm34 Γ (sum34 A B); left34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right case zero suc rec →
     left34 _ _ _ (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right case zero suc rec)

right34 : ∀{Γ A B} → Tm34 Γ B → Tm34 Γ (sum34 A B); right34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case zero suc rec →
     right34 _ _ _ (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case zero suc rec)

case34 : ∀{Γ A B C} → Tm34 Γ (sum34 A B) → Tm34 Γ (arr34 A C) → Tm34 Γ (arr34 B C) → Tm34 Γ C; case34
 = λ t u v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec →
     case34 _ _ _ _
           (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)
           (u Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)
           (v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)

zero34  : ∀{Γ} → Tm34 Γ nat34; zero34
 = λ Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc rec → zero34 _

suc34 : ∀{Γ} → Tm34 Γ nat34 → Tm34 Γ nat34; suc34
 = λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec →
   suc34 _ (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec)

rec34 : ∀{Γ A} → Tm34 Γ nat34 → Tm34 Γ (arr34 nat34 (arr34 A A)) → Tm34 Γ A → Tm34 Γ A; rec34
 = λ t u v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34 →
     rec34 _ _
          (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)
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
   (vz  : ∀ Γ A → Var35 (snoc35 Γ A) A)
   (vs  : ∀ Γ B A → Var35 Γ A → Var35 (snoc35 Γ B) A)
 → Var35 Γ A

vz35 : ∀{Γ A} → Var35 (snoc35 Γ A) A; vz35
 = λ Var35 vz35 vs → vz35 _ _

vs35 : ∀{Γ B A} → Var35 Γ A → Var35 (snoc35 Γ B) A; vs35
 = λ x Var35 vz35 vs35 → vs35 _ _ _ (x Var35 vz35 vs35)

Tm35 : Con35 → Ty35 → Set; Tm35
 = λ Γ A →
   (Tm35  : Con35 → Ty35 → Set)
   (var   : ∀ Γ A      → Var35 Γ A → Tm35 Γ A)
   (lam   : ∀ Γ A B    → Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B))
   (app   : ∀ Γ A B    → Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B)
   (tt    : ∀ Γ        → Tm35 Γ top35)
   (pair  : ∀ Γ A B    → Tm35 Γ A → Tm35 Γ B → Tm35 Γ (prod35 A B))
   (fst   : ∀ Γ A B    → Tm35 Γ (prod35 A B) → Tm35 Γ A)
   (snd   : ∀ Γ A B    → Tm35 Γ (prod35 A B) → Tm35 Γ B)
   (left  : ∀ Γ A B    → Tm35 Γ A → Tm35 Γ (sum35 A B))
   (right : ∀ Γ A B    → Tm35 Γ B → Tm35 Γ (sum35 A B))
   (case  : ∀ Γ A B C  → Tm35 Γ (sum35 A B) → Tm35 Γ (arr35 A C) → Tm35 Γ (arr35 B C) → Tm35 Γ C)
   (zero  : ∀ Γ        → Tm35 Γ nat35)
   (suc   : ∀ Γ        → Tm35 Γ nat35 → Tm35 Γ nat35)
   (rec   : ∀ Γ A      → Tm35 Γ nat35 → Tm35 Γ (arr35 nat35 (arr35 A A)) → Tm35 Γ A → Tm35 Γ A)
 → Tm35 Γ A

var35 : ∀{Γ A} → Var35 Γ A → Tm35 Γ A; var35
 = λ x Tm35 var35 lam app tt pair fst snd left right case zero suc rec →
     var35 _ _ x

lam35 : ∀{Γ A B} → Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B); lam35
 = λ t Tm35 var35 lam35 app tt pair fst snd left right case zero suc rec →
     lam35 _ _ _ (t Tm35 var35 lam35 app tt pair fst snd left right case zero suc rec)

app35 : ∀{Γ A B} → Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B; app35
 = λ t u Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec →
     app35 _ _ _ (t Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec)
         (u Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec)

tt35 : ∀{Γ} → Tm35 Γ top35; tt35
 = λ Tm35 var35 lam35 app35 tt35 pair fst snd left right case zero suc rec → tt35 _

pair35 : ∀{Γ A B} → Tm35 Γ A → Tm35 Γ B → Tm35 Γ (prod35 A B); pair35
 = λ t u Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec →
     pair35 _ _ _ (t Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec)
          (u Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec)

fst35 : ∀{Γ A B} → Tm35 Γ (prod35 A B) → Tm35 Γ A; fst35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd left right case zero suc rec →
     fst35 _ _ _ (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd left right case zero suc rec)

snd35 : ∀{Γ A B} → Tm35 Γ (prod35 A B) → Tm35 Γ B; snd35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left right case zero suc rec →
     snd35 _ _ _ (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left right case zero suc rec)

left35 : ∀{Γ A B} → Tm35 Γ A → Tm35 Γ (sum35 A B); left35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right case zero suc rec →
     left35 _ _ _ (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right case zero suc rec)

right35 : ∀{Γ A B} → Tm35 Γ B → Tm35 Γ (sum35 A B); right35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case zero suc rec →
     right35 _ _ _ (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case zero suc rec)

case35 : ∀{Γ A B C} → Tm35 Γ (sum35 A B) → Tm35 Γ (arr35 A C) → Tm35 Γ (arr35 B C) → Tm35 Γ C; case35
 = λ t u v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec →
     case35 _ _ _ _
           (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)
           (u Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)
           (v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)

zero35  : ∀{Γ} → Tm35 Γ nat35; zero35
 = λ Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc rec → zero35 _

suc35 : ∀{Γ} → Tm35 Γ nat35 → Tm35 Γ nat35; suc35
 = λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec →
   suc35 _ (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec)

rec35 : ∀{Γ A} → Tm35 Γ nat35 → Tm35 Γ (arr35 nat35 (arr35 A A)) → Tm35 Γ A → Tm35 Γ A; rec35
 = λ t u v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35 →
     rec35 _ _
          (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)
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
   (vz  : ∀ Γ A → Var36 (snoc36 Γ A) A)
   (vs  : ∀ Γ B A → Var36 Γ A → Var36 (snoc36 Γ B) A)
 → Var36 Γ A

vz36 : ∀{Γ A} → Var36 (snoc36 Γ A) A; vz36
 = λ Var36 vz36 vs → vz36 _ _

vs36 : ∀{Γ B A} → Var36 Γ A → Var36 (snoc36 Γ B) A; vs36
 = λ x Var36 vz36 vs36 → vs36 _ _ _ (x Var36 vz36 vs36)

Tm36 : Con36 → Ty36 → Set; Tm36
 = λ Γ A →
   (Tm36  : Con36 → Ty36 → Set)
   (var   : ∀ Γ A      → Var36 Γ A → Tm36 Γ A)
   (lam   : ∀ Γ A B    → Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B))
   (app   : ∀ Γ A B    → Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B)
   (tt    : ∀ Γ        → Tm36 Γ top36)
   (pair  : ∀ Γ A B    → Tm36 Γ A → Tm36 Γ B → Tm36 Γ (prod36 A B))
   (fst   : ∀ Γ A B    → Tm36 Γ (prod36 A B) → Tm36 Γ A)
   (snd   : ∀ Γ A B    → Tm36 Γ (prod36 A B) → Tm36 Γ B)
   (left  : ∀ Γ A B    → Tm36 Γ A → Tm36 Γ (sum36 A B))
   (right : ∀ Γ A B    → Tm36 Γ B → Tm36 Γ (sum36 A B))
   (case  : ∀ Γ A B C  → Tm36 Γ (sum36 A B) → Tm36 Γ (arr36 A C) → Tm36 Γ (arr36 B C) → Tm36 Γ C)
   (zero  : ∀ Γ        → Tm36 Γ nat36)
   (suc   : ∀ Γ        → Tm36 Γ nat36 → Tm36 Γ nat36)
   (rec   : ∀ Γ A      → Tm36 Γ nat36 → Tm36 Γ (arr36 nat36 (arr36 A A)) → Tm36 Γ A → Tm36 Γ A)
 → Tm36 Γ A

var36 : ∀{Γ A} → Var36 Γ A → Tm36 Γ A; var36
 = λ x Tm36 var36 lam app tt pair fst snd left right case zero suc rec →
     var36 _ _ x

lam36 : ∀{Γ A B} → Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B); lam36
 = λ t Tm36 var36 lam36 app tt pair fst snd left right case zero suc rec →
     lam36 _ _ _ (t Tm36 var36 lam36 app tt pair fst snd left right case zero suc rec)

app36 : ∀{Γ A B} → Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B; app36
 = λ t u Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec →
     app36 _ _ _ (t Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec)
         (u Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec)

tt36 : ∀{Γ} → Tm36 Γ top36; tt36
 = λ Tm36 var36 lam36 app36 tt36 pair fst snd left right case zero suc rec → tt36 _

pair36 : ∀{Γ A B} → Tm36 Γ A → Tm36 Γ B → Tm36 Γ (prod36 A B); pair36
 = λ t u Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec →
     pair36 _ _ _ (t Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec)
          (u Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec)

fst36 : ∀{Γ A B} → Tm36 Γ (prod36 A B) → Tm36 Γ A; fst36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd left right case zero suc rec →
     fst36 _ _ _ (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd left right case zero suc rec)

snd36 : ∀{Γ A B} → Tm36 Γ (prod36 A B) → Tm36 Γ B; snd36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left right case zero suc rec →
     snd36 _ _ _ (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left right case zero suc rec)

left36 : ∀{Γ A B} → Tm36 Γ A → Tm36 Γ (sum36 A B); left36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right case zero suc rec →
     left36 _ _ _ (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right case zero suc rec)

right36 : ∀{Γ A B} → Tm36 Γ B → Tm36 Γ (sum36 A B); right36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case zero suc rec →
     right36 _ _ _ (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case zero suc rec)

case36 : ∀{Γ A B C} → Tm36 Γ (sum36 A B) → Tm36 Γ (arr36 A C) → Tm36 Γ (arr36 B C) → Tm36 Γ C; case36
 = λ t u v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec →
     case36 _ _ _ _
           (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)
           (u Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)
           (v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)

zero36  : ∀{Γ} → Tm36 Γ nat36; zero36
 = λ Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc rec → zero36 _

suc36 : ∀{Γ} → Tm36 Γ nat36 → Tm36 Γ nat36; suc36
 = λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec →
   suc36 _ (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec)

rec36 : ∀{Γ A} → Tm36 Γ nat36 → Tm36 Γ (arr36 nat36 (arr36 A A)) → Tm36 Γ A → Tm36 Γ A; rec36
 = λ t u v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36 →
     rec36 _ _
          (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)
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
   (vz  : ∀ Γ A → Var37 (snoc37 Γ A) A)
   (vs  : ∀ Γ B A → Var37 Γ A → Var37 (snoc37 Γ B) A)
 → Var37 Γ A

vz37 : ∀{Γ A} → Var37 (snoc37 Γ A) A; vz37
 = λ Var37 vz37 vs → vz37 _ _

vs37 : ∀{Γ B A} → Var37 Γ A → Var37 (snoc37 Γ B) A; vs37
 = λ x Var37 vz37 vs37 → vs37 _ _ _ (x Var37 vz37 vs37)

Tm37 : Con37 → Ty37 → Set; Tm37
 = λ Γ A →
   (Tm37  : Con37 → Ty37 → Set)
   (var   : ∀ Γ A      → Var37 Γ A → Tm37 Γ A)
   (lam   : ∀ Γ A B    → Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B))
   (app   : ∀ Γ A B    → Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B)
   (tt    : ∀ Γ        → Tm37 Γ top37)
   (pair  : ∀ Γ A B    → Tm37 Γ A → Tm37 Γ B → Tm37 Γ (prod37 A B))
   (fst   : ∀ Γ A B    → Tm37 Γ (prod37 A B) → Tm37 Γ A)
   (snd   : ∀ Γ A B    → Tm37 Γ (prod37 A B) → Tm37 Γ B)
   (left  : ∀ Γ A B    → Tm37 Γ A → Tm37 Γ (sum37 A B))
   (right : ∀ Γ A B    → Tm37 Γ B → Tm37 Γ (sum37 A B))
   (case  : ∀ Γ A B C  → Tm37 Γ (sum37 A B) → Tm37 Γ (arr37 A C) → Tm37 Γ (arr37 B C) → Tm37 Γ C)
   (zero  : ∀ Γ        → Tm37 Γ nat37)
   (suc   : ∀ Γ        → Tm37 Γ nat37 → Tm37 Γ nat37)
   (rec   : ∀ Γ A      → Tm37 Γ nat37 → Tm37 Γ (arr37 nat37 (arr37 A A)) → Tm37 Γ A → Tm37 Γ A)
 → Tm37 Γ A

var37 : ∀{Γ A} → Var37 Γ A → Tm37 Γ A; var37
 = λ x Tm37 var37 lam app tt pair fst snd left right case zero suc rec →
     var37 _ _ x

lam37 : ∀{Γ A B} → Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B); lam37
 = λ t Tm37 var37 lam37 app tt pair fst snd left right case zero suc rec →
     lam37 _ _ _ (t Tm37 var37 lam37 app tt pair fst snd left right case zero suc rec)

app37 : ∀{Γ A B} → Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B; app37
 = λ t u Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec →
     app37 _ _ _ (t Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec)
         (u Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec)

tt37 : ∀{Γ} → Tm37 Γ top37; tt37
 = λ Tm37 var37 lam37 app37 tt37 pair fst snd left right case zero suc rec → tt37 _

pair37 : ∀{Γ A B} → Tm37 Γ A → Tm37 Γ B → Tm37 Γ (prod37 A B); pair37
 = λ t u Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec →
     pair37 _ _ _ (t Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec)
          (u Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec)

fst37 : ∀{Γ A B} → Tm37 Γ (prod37 A B) → Tm37 Γ A; fst37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd left right case zero suc rec →
     fst37 _ _ _ (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd left right case zero suc rec)

snd37 : ∀{Γ A B} → Tm37 Γ (prod37 A B) → Tm37 Γ B; snd37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left right case zero suc rec →
     snd37 _ _ _ (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left right case zero suc rec)

left37 : ∀{Γ A B} → Tm37 Γ A → Tm37 Γ (sum37 A B); left37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right case zero suc rec →
     left37 _ _ _ (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right case zero suc rec)

right37 : ∀{Γ A B} → Tm37 Γ B → Tm37 Γ (sum37 A B); right37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case zero suc rec →
     right37 _ _ _ (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case zero suc rec)

case37 : ∀{Γ A B C} → Tm37 Γ (sum37 A B) → Tm37 Γ (arr37 A C) → Tm37 Γ (arr37 B C) → Tm37 Γ C; case37
 = λ t u v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec →
     case37 _ _ _ _
           (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)
           (u Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)
           (v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)

zero37  : ∀{Γ} → Tm37 Γ nat37; zero37
 = λ Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc rec → zero37 _

suc37 : ∀{Γ} → Tm37 Γ nat37 → Tm37 Γ nat37; suc37
 = λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec →
   suc37 _ (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec)

rec37 : ∀{Γ A} → Tm37 Γ nat37 → Tm37 Γ (arr37 nat37 (arr37 A A)) → Tm37 Γ A → Tm37 Γ A; rec37
 = λ t u v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37 →
     rec37 _ _
          (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)
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
   (vz  : ∀ Γ A → Var38 (snoc38 Γ A) A)
   (vs  : ∀ Γ B A → Var38 Γ A → Var38 (snoc38 Γ B) A)
 → Var38 Γ A

vz38 : ∀{Γ A} → Var38 (snoc38 Γ A) A; vz38
 = λ Var38 vz38 vs → vz38 _ _

vs38 : ∀{Γ B A} → Var38 Γ A → Var38 (snoc38 Γ B) A; vs38
 = λ x Var38 vz38 vs38 → vs38 _ _ _ (x Var38 vz38 vs38)

Tm38 : Con38 → Ty38 → Set; Tm38
 = λ Γ A →
   (Tm38  : Con38 → Ty38 → Set)
   (var   : ∀ Γ A      → Var38 Γ A → Tm38 Γ A)
   (lam   : ∀ Γ A B    → Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B))
   (app   : ∀ Γ A B    → Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B)
   (tt    : ∀ Γ        → Tm38 Γ top38)
   (pair  : ∀ Γ A B    → Tm38 Γ A → Tm38 Γ B → Tm38 Γ (prod38 A B))
   (fst   : ∀ Γ A B    → Tm38 Γ (prod38 A B) → Tm38 Γ A)
   (snd   : ∀ Γ A B    → Tm38 Γ (prod38 A B) → Tm38 Γ B)
   (left  : ∀ Γ A B    → Tm38 Γ A → Tm38 Γ (sum38 A B))
   (right : ∀ Γ A B    → Tm38 Γ B → Tm38 Γ (sum38 A B))
   (case  : ∀ Γ A B C  → Tm38 Γ (sum38 A B) → Tm38 Γ (arr38 A C) → Tm38 Γ (arr38 B C) → Tm38 Γ C)
   (zero  : ∀ Γ        → Tm38 Γ nat38)
   (suc   : ∀ Γ        → Tm38 Γ nat38 → Tm38 Γ nat38)
   (rec   : ∀ Γ A      → Tm38 Γ nat38 → Tm38 Γ (arr38 nat38 (arr38 A A)) → Tm38 Γ A → Tm38 Γ A)
 → Tm38 Γ A

var38 : ∀{Γ A} → Var38 Γ A → Tm38 Γ A; var38
 = λ x Tm38 var38 lam app tt pair fst snd left right case zero suc rec →
     var38 _ _ x

lam38 : ∀{Γ A B} → Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B); lam38
 = λ t Tm38 var38 lam38 app tt pair fst snd left right case zero suc rec →
     lam38 _ _ _ (t Tm38 var38 lam38 app tt pair fst snd left right case zero suc rec)

app38 : ∀{Γ A B} → Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B; app38
 = λ t u Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec →
     app38 _ _ _ (t Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec)
         (u Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec)

tt38 : ∀{Γ} → Tm38 Γ top38; tt38
 = λ Tm38 var38 lam38 app38 tt38 pair fst snd left right case zero suc rec → tt38 _

pair38 : ∀{Γ A B} → Tm38 Γ A → Tm38 Γ B → Tm38 Γ (prod38 A B); pair38
 = λ t u Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec →
     pair38 _ _ _ (t Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec)
          (u Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec)

fst38 : ∀{Γ A B} → Tm38 Γ (prod38 A B) → Tm38 Γ A; fst38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd left right case zero suc rec →
     fst38 _ _ _ (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd left right case zero suc rec)

snd38 : ∀{Γ A B} → Tm38 Γ (prod38 A B) → Tm38 Γ B; snd38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left right case zero suc rec →
     snd38 _ _ _ (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left right case zero suc rec)

left38 : ∀{Γ A B} → Tm38 Γ A → Tm38 Γ (sum38 A B); left38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right case zero suc rec →
     left38 _ _ _ (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right case zero suc rec)

right38 : ∀{Γ A B} → Tm38 Γ B → Tm38 Γ (sum38 A B); right38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case zero suc rec →
     right38 _ _ _ (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case zero suc rec)

case38 : ∀{Γ A B C} → Tm38 Γ (sum38 A B) → Tm38 Γ (arr38 A C) → Tm38 Γ (arr38 B C) → Tm38 Γ C; case38
 = λ t u v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec →
     case38 _ _ _ _
           (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)
           (u Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)
           (v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)

zero38  : ∀{Γ} → Tm38 Γ nat38; zero38
 = λ Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc rec → zero38 _

suc38 : ∀{Γ} → Tm38 Γ nat38 → Tm38 Γ nat38; suc38
 = λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec →
   suc38 _ (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec)

rec38 : ∀{Γ A} → Tm38 Γ nat38 → Tm38 Γ (arr38 nat38 (arr38 A A)) → Tm38 Γ A → Tm38 Γ A; rec38
 = λ t u v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38 →
     rec38 _ _
          (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)
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
   (vz  : ∀ Γ A → Var39 (snoc39 Γ A) A)
   (vs  : ∀ Γ B A → Var39 Γ A → Var39 (snoc39 Γ B) A)
 → Var39 Γ A

vz39 : ∀{Γ A} → Var39 (snoc39 Γ A) A; vz39
 = λ Var39 vz39 vs → vz39 _ _

vs39 : ∀{Γ B A} → Var39 Γ A → Var39 (snoc39 Γ B) A; vs39
 = λ x Var39 vz39 vs39 → vs39 _ _ _ (x Var39 vz39 vs39)

Tm39 : Con39 → Ty39 → Set; Tm39
 = λ Γ A →
   (Tm39  : Con39 → Ty39 → Set)
   (var   : ∀ Γ A      → Var39 Γ A → Tm39 Γ A)
   (lam   : ∀ Γ A B    → Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B))
   (app   : ∀ Γ A B    → Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B)
   (tt    : ∀ Γ        → Tm39 Γ top39)
   (pair  : ∀ Γ A B    → Tm39 Γ A → Tm39 Γ B → Tm39 Γ (prod39 A B))
   (fst   : ∀ Γ A B    → Tm39 Γ (prod39 A B) → Tm39 Γ A)
   (snd   : ∀ Γ A B    → Tm39 Γ (prod39 A B) → Tm39 Γ B)
   (left  : ∀ Γ A B    → Tm39 Γ A → Tm39 Γ (sum39 A B))
   (right : ∀ Γ A B    → Tm39 Γ B → Tm39 Γ (sum39 A B))
   (case  : ∀ Γ A B C  → Tm39 Γ (sum39 A B) → Tm39 Γ (arr39 A C) → Tm39 Γ (arr39 B C) → Tm39 Γ C)
   (zero  : ∀ Γ        → Tm39 Γ nat39)
   (suc   : ∀ Γ        → Tm39 Γ nat39 → Tm39 Γ nat39)
   (rec   : ∀ Γ A      → Tm39 Γ nat39 → Tm39 Γ (arr39 nat39 (arr39 A A)) → Tm39 Γ A → Tm39 Γ A)
 → Tm39 Γ A

var39 : ∀{Γ A} → Var39 Γ A → Tm39 Γ A; var39
 = λ x Tm39 var39 lam app tt pair fst snd left right case zero suc rec →
     var39 _ _ x

lam39 : ∀{Γ A B} → Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B); lam39
 = λ t Tm39 var39 lam39 app tt pair fst snd left right case zero suc rec →
     lam39 _ _ _ (t Tm39 var39 lam39 app tt pair fst snd left right case zero suc rec)

app39 : ∀{Γ A B} → Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B; app39
 = λ t u Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec →
     app39 _ _ _ (t Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec)
         (u Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec)

tt39 : ∀{Γ} → Tm39 Γ top39; tt39
 = λ Tm39 var39 lam39 app39 tt39 pair fst snd left right case zero suc rec → tt39 _

pair39 : ∀{Γ A B} → Tm39 Γ A → Tm39 Γ B → Tm39 Γ (prod39 A B); pair39
 = λ t u Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec →
     pair39 _ _ _ (t Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec)
          (u Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec)

fst39 : ∀{Γ A B} → Tm39 Γ (prod39 A B) → Tm39 Γ A; fst39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd left right case zero suc rec →
     fst39 _ _ _ (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd left right case zero suc rec)

snd39 : ∀{Γ A B} → Tm39 Γ (prod39 A B) → Tm39 Γ B; snd39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left right case zero suc rec →
     snd39 _ _ _ (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left right case zero suc rec)

left39 : ∀{Γ A B} → Tm39 Γ A → Tm39 Γ (sum39 A B); left39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right case zero suc rec →
     left39 _ _ _ (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right case zero suc rec)

right39 : ∀{Γ A B} → Tm39 Γ B → Tm39 Γ (sum39 A B); right39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case zero suc rec →
     right39 _ _ _ (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case zero suc rec)

case39 : ∀{Γ A B C} → Tm39 Γ (sum39 A B) → Tm39 Γ (arr39 A C) → Tm39 Γ (arr39 B C) → Tm39 Γ C; case39
 = λ t u v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec →
     case39 _ _ _ _
           (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)
           (u Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)
           (v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)

zero39  : ∀{Γ} → Tm39 Γ nat39; zero39
 = λ Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc rec → zero39 _

suc39 : ∀{Γ} → Tm39 Γ nat39 → Tm39 Γ nat39; suc39
 = λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec →
   suc39 _ (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec)

rec39 : ∀{Γ A} → Tm39 Γ nat39 → Tm39 Γ (arr39 nat39 (arr39 A A)) → Tm39 Γ A → Tm39 Γ A; rec39
 = λ t u v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39 →
     rec39 _ _
          (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)
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
