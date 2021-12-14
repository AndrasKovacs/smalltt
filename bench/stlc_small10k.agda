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

test : ∀{Γ A} → Tm Γ (arr (arr A A) (arr A A));test
  = lam (lam (app v1 (app v1 (app v1 (app v1 (app v1 (app v1 v0)))))))
{-# OPTIONS --type-in-type #-}

Ty1 : Set; Ty1
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι1   : Ty1; ι1 = λ _ ι1 _ → ι1
arr1 : Ty1 → Ty1 → Ty1; arr1 = λ A B Ty1 ι1 arr1 → arr1 (A Ty1 ι1 arr1) (B Ty1 ι1 arr1)

Con1 : Set;Con1
 = (Con1 : Set)
   (nil  : Con1)
   (snoc : Con1 → Ty1 → Con1)
 → Con1

nil1 : Con1;nil1
 = λ Con1 nil1 snoc → nil1

snoc1 : Con1 → Ty1 → Con1;snoc1
 = λ Γ A Con1 nil1 snoc1 → snoc1 (Γ Con1 nil1 snoc1) A

Var1 : Con1 → Ty1 → Set;Var1
 = λ Γ A →
   (Var1 : Con1 → Ty1 → Set)
   (vz  : (Γ : _)(A : _) → Var1 (snoc1 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var1 Γ A → Var1 (snoc1 Γ B) A)
 → Var1 Γ A

vz1 : ∀{Γ A} → Var1 (snoc1 Γ A) A;vz1
 = λ Var1 vz1 vs → vz1 _ _

vs1 : ∀{Γ B A} → Var1 Γ A → Var1 (snoc1 Γ B) A;vs1
 = λ x Var1 vz1 vs1 → vs1 _ _ _ (x Var1 vz1 vs1)

Tm1 : Con1 → Ty1 → Set;Tm1
 = λ Γ A →
   (Tm1    : Con1 → Ty1 → Set)
   (var   : (Γ : _) (A : _) → Var1 Γ A → Tm1 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B))
   (app   : (Γ : _) (A B : _) → Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B)
 → Tm1 Γ A

var1 : ∀{Γ A} → Var1 Γ A → Tm1 Γ A;var1
 = λ x Tm1 var1 lam app → var1 _ _ x

lam1 : ∀{Γ A B} → Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B);lam1
 = λ t Tm1 var1 lam1 app → lam1 _ _ _ (t Tm1 var1 lam1 app)

app1 : ∀{Γ A B} → Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B;app1
 = λ t u Tm1 var1 lam1 app1 →
     app1 _ _ _ (t Tm1 var1 lam1 app1) (u Tm1 var1 lam1 app1)

v01 : ∀{Γ A} → Tm1 (snoc1 Γ A) A;v01
 = var1 vz1

v11 : ∀{Γ A B} → Tm1 (snoc1 (snoc1 Γ A) B) A;v11
 = var1 (vs1 vz1)

v21 : ∀{Γ A B C} → Tm1 (snoc1 (snoc1 (snoc1 Γ A) B) C) A;v21
 = var1 (vs1 (vs1 vz1))

v31 : ∀{Γ A B C D} → Tm1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) A;v31
 = var1 (vs1 (vs1 (vs1 vz1)))

v41 : ∀{Γ A B C D E} → Tm1 (snoc1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) E) A;v41
 = var1 (vs1 (vs1 (vs1 (vs1 vz1))))

test1 : ∀{Γ A} → Tm1 Γ (arr1 (arr1 A A) (arr1 A A));test1
  = lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01)))))))
{-# OPTIONS --type-in-type #-}

Ty2 : Set; Ty2
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι2   : Ty2; ι2 = λ _ ι2 _ → ι2
arr2 : Ty2 → Ty2 → Ty2; arr2 = λ A B Ty2 ι2 arr2 → arr2 (A Ty2 ι2 arr2) (B Ty2 ι2 arr2)

Con2 : Set;Con2
 = (Con2 : Set)
   (nil  : Con2)
   (snoc : Con2 → Ty2 → Con2)
 → Con2

nil2 : Con2;nil2
 = λ Con2 nil2 snoc → nil2

snoc2 : Con2 → Ty2 → Con2;snoc2
 = λ Γ A Con2 nil2 snoc2 → snoc2 (Γ Con2 nil2 snoc2) A

Var2 : Con2 → Ty2 → Set;Var2
 = λ Γ A →
   (Var2 : Con2 → Ty2 → Set)
   (vz  : (Γ : _)(A : _) → Var2 (snoc2 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var2 Γ A → Var2 (snoc2 Γ B) A)
 → Var2 Γ A

vz2 : ∀{Γ A} → Var2 (snoc2 Γ A) A;vz2
 = λ Var2 vz2 vs → vz2 _ _

vs2 : ∀{Γ B A} → Var2 Γ A → Var2 (snoc2 Γ B) A;vs2
 = λ x Var2 vz2 vs2 → vs2 _ _ _ (x Var2 vz2 vs2)

Tm2 : Con2 → Ty2 → Set;Tm2
 = λ Γ A →
   (Tm2    : Con2 → Ty2 → Set)
   (var   : (Γ : _) (A : _) → Var2 Γ A → Tm2 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B))
   (app   : (Γ : _) (A B : _) → Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B)
 → Tm2 Γ A

var2 : ∀{Γ A} → Var2 Γ A → Tm2 Γ A;var2
 = λ x Tm2 var2 lam app → var2 _ _ x

lam2 : ∀{Γ A B} → Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B);lam2
 = λ t Tm2 var2 lam2 app → lam2 _ _ _ (t Tm2 var2 lam2 app)

app2 : ∀{Γ A B} → Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B;app2
 = λ t u Tm2 var2 lam2 app2 →
     app2 _ _ _ (t Tm2 var2 lam2 app2) (u Tm2 var2 lam2 app2)

v02 : ∀{Γ A} → Tm2 (snoc2 Γ A) A;v02
 = var2 vz2

v12 : ∀{Γ A B} → Tm2 (snoc2 (snoc2 Γ A) B) A;v12
 = var2 (vs2 vz2)

v22 : ∀{Γ A B C} → Tm2 (snoc2 (snoc2 (snoc2 Γ A) B) C) A;v22
 = var2 (vs2 (vs2 vz2))

v32 : ∀{Γ A B C D} → Tm2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) A;v32
 = var2 (vs2 (vs2 (vs2 vz2)))

v42 : ∀{Γ A B C D E} → Tm2 (snoc2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) E) A;v42
 = var2 (vs2 (vs2 (vs2 (vs2 vz2))))

test2 : ∀{Γ A} → Tm2 Γ (arr2 (arr2 A A) (arr2 A A));test2
  = lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02)))))))
{-# OPTIONS --type-in-type #-}

Ty3 : Set; Ty3
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι3   : Ty3; ι3 = λ _ ι3 _ → ι3
arr3 : Ty3 → Ty3 → Ty3; arr3 = λ A B Ty3 ι3 arr3 → arr3 (A Ty3 ι3 arr3) (B Ty3 ι3 arr3)

Con3 : Set;Con3
 = (Con3 : Set)
   (nil  : Con3)
   (snoc : Con3 → Ty3 → Con3)
 → Con3

nil3 : Con3;nil3
 = λ Con3 nil3 snoc → nil3

snoc3 : Con3 → Ty3 → Con3;snoc3
 = λ Γ A Con3 nil3 snoc3 → snoc3 (Γ Con3 nil3 snoc3) A

Var3 : Con3 → Ty3 → Set;Var3
 = λ Γ A →
   (Var3 : Con3 → Ty3 → Set)
   (vz  : (Γ : _)(A : _) → Var3 (snoc3 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var3 Γ A → Var3 (snoc3 Γ B) A)
 → Var3 Γ A

vz3 : ∀{Γ A} → Var3 (snoc3 Γ A) A;vz3
 = λ Var3 vz3 vs → vz3 _ _

vs3 : ∀{Γ B A} → Var3 Γ A → Var3 (snoc3 Γ B) A;vs3
 = λ x Var3 vz3 vs3 → vs3 _ _ _ (x Var3 vz3 vs3)

Tm3 : Con3 → Ty3 → Set;Tm3
 = λ Γ A →
   (Tm3    : Con3 → Ty3 → Set)
   (var   : (Γ : _) (A : _) → Var3 Γ A → Tm3 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B))
   (app   : (Γ : _) (A B : _) → Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B)
 → Tm3 Γ A

var3 : ∀{Γ A} → Var3 Γ A → Tm3 Γ A;var3
 = λ x Tm3 var3 lam app → var3 _ _ x

lam3 : ∀{Γ A B} → Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B);lam3
 = λ t Tm3 var3 lam3 app → lam3 _ _ _ (t Tm3 var3 lam3 app)

app3 : ∀{Γ A B} → Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B;app3
 = λ t u Tm3 var3 lam3 app3 →
     app3 _ _ _ (t Tm3 var3 lam3 app3) (u Tm3 var3 lam3 app3)

v03 : ∀{Γ A} → Tm3 (snoc3 Γ A) A;v03
 = var3 vz3

v13 : ∀{Γ A B} → Tm3 (snoc3 (snoc3 Γ A) B) A;v13
 = var3 (vs3 vz3)

v23 : ∀{Γ A B C} → Tm3 (snoc3 (snoc3 (snoc3 Γ A) B) C) A;v23
 = var3 (vs3 (vs3 vz3))

v33 : ∀{Γ A B C D} → Tm3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) A;v33
 = var3 (vs3 (vs3 (vs3 vz3)))

v43 : ∀{Γ A B C D E} → Tm3 (snoc3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) E) A;v43
 = var3 (vs3 (vs3 (vs3 (vs3 vz3))))

test3 : ∀{Γ A} → Tm3 Γ (arr3 (arr3 A A) (arr3 A A));test3
  = lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03)))))))
{-# OPTIONS --type-in-type #-}

Ty4 : Set; Ty4
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι4   : Ty4; ι4 = λ _ ι4 _ → ι4
arr4 : Ty4 → Ty4 → Ty4; arr4 = λ A B Ty4 ι4 arr4 → arr4 (A Ty4 ι4 arr4) (B Ty4 ι4 arr4)

Con4 : Set;Con4
 = (Con4 : Set)
   (nil  : Con4)
   (snoc : Con4 → Ty4 → Con4)
 → Con4

nil4 : Con4;nil4
 = λ Con4 nil4 snoc → nil4

snoc4 : Con4 → Ty4 → Con4;snoc4
 = λ Γ A Con4 nil4 snoc4 → snoc4 (Γ Con4 nil4 snoc4) A

Var4 : Con4 → Ty4 → Set;Var4
 = λ Γ A →
   (Var4 : Con4 → Ty4 → Set)
   (vz  : (Γ : _)(A : _) → Var4 (snoc4 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var4 Γ A → Var4 (snoc4 Γ B) A)
 → Var4 Γ A

vz4 : ∀{Γ A} → Var4 (snoc4 Γ A) A;vz4
 = λ Var4 vz4 vs → vz4 _ _

vs4 : ∀{Γ B A} → Var4 Γ A → Var4 (snoc4 Γ B) A;vs4
 = λ x Var4 vz4 vs4 → vs4 _ _ _ (x Var4 vz4 vs4)

Tm4 : Con4 → Ty4 → Set;Tm4
 = λ Γ A →
   (Tm4    : Con4 → Ty4 → Set)
   (var   : (Γ : _) (A : _) → Var4 Γ A → Tm4 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B))
   (app   : (Γ : _) (A B : _) → Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B)
 → Tm4 Γ A

var4 : ∀{Γ A} → Var4 Γ A → Tm4 Γ A;var4
 = λ x Tm4 var4 lam app → var4 _ _ x

lam4 : ∀{Γ A B} → Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B);lam4
 = λ t Tm4 var4 lam4 app → lam4 _ _ _ (t Tm4 var4 lam4 app)

app4 : ∀{Γ A B} → Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B;app4
 = λ t u Tm4 var4 lam4 app4 →
     app4 _ _ _ (t Tm4 var4 lam4 app4) (u Tm4 var4 lam4 app4)

v04 : ∀{Γ A} → Tm4 (snoc4 Γ A) A;v04
 = var4 vz4

v14 : ∀{Γ A B} → Tm4 (snoc4 (snoc4 Γ A) B) A;v14
 = var4 (vs4 vz4)

v24 : ∀{Γ A B C} → Tm4 (snoc4 (snoc4 (snoc4 Γ A) B) C) A;v24
 = var4 (vs4 (vs4 vz4))

v34 : ∀{Γ A B C D} → Tm4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) A;v34
 = var4 (vs4 (vs4 (vs4 vz4)))

v44 : ∀{Γ A B C D E} → Tm4 (snoc4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) E) A;v44
 = var4 (vs4 (vs4 (vs4 (vs4 vz4))))

test4 : ∀{Γ A} → Tm4 Γ (arr4 (arr4 A A) (arr4 A A));test4
  = lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04)))))))
{-# OPTIONS --type-in-type #-}

Ty5 : Set; Ty5
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι5   : Ty5; ι5 = λ _ ι5 _ → ι5
arr5 : Ty5 → Ty5 → Ty5; arr5 = λ A B Ty5 ι5 arr5 → arr5 (A Ty5 ι5 arr5) (B Ty5 ι5 arr5)

Con5 : Set;Con5
 = (Con5 : Set)
   (nil  : Con5)
   (snoc : Con5 → Ty5 → Con5)
 → Con5

nil5 : Con5;nil5
 = λ Con5 nil5 snoc → nil5

snoc5 : Con5 → Ty5 → Con5;snoc5
 = λ Γ A Con5 nil5 snoc5 → snoc5 (Γ Con5 nil5 snoc5) A

Var5 : Con5 → Ty5 → Set;Var5
 = λ Γ A →
   (Var5 : Con5 → Ty5 → Set)
   (vz  : (Γ : _)(A : _) → Var5 (snoc5 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var5 Γ A → Var5 (snoc5 Γ B) A)
 → Var5 Γ A

vz5 : ∀{Γ A} → Var5 (snoc5 Γ A) A;vz5
 = λ Var5 vz5 vs → vz5 _ _

vs5 : ∀{Γ B A} → Var5 Γ A → Var5 (snoc5 Γ B) A;vs5
 = λ x Var5 vz5 vs5 → vs5 _ _ _ (x Var5 vz5 vs5)

Tm5 : Con5 → Ty5 → Set;Tm5
 = λ Γ A →
   (Tm5    : Con5 → Ty5 → Set)
   (var   : (Γ : _) (A : _) → Var5 Γ A → Tm5 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B))
   (app   : (Γ : _) (A B : _) → Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B)
 → Tm5 Γ A

var5 : ∀{Γ A} → Var5 Γ A → Tm5 Γ A;var5
 = λ x Tm5 var5 lam app → var5 _ _ x

lam5 : ∀{Γ A B} → Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B);lam5
 = λ t Tm5 var5 lam5 app → lam5 _ _ _ (t Tm5 var5 lam5 app)

app5 : ∀{Γ A B} → Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B;app5
 = λ t u Tm5 var5 lam5 app5 →
     app5 _ _ _ (t Tm5 var5 lam5 app5) (u Tm5 var5 lam5 app5)

v05 : ∀{Γ A} → Tm5 (snoc5 Γ A) A;v05
 = var5 vz5

v15 : ∀{Γ A B} → Tm5 (snoc5 (snoc5 Γ A) B) A;v15
 = var5 (vs5 vz5)

v25 : ∀{Γ A B C} → Tm5 (snoc5 (snoc5 (snoc5 Γ A) B) C) A;v25
 = var5 (vs5 (vs5 vz5))

v35 : ∀{Γ A B C D} → Tm5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) A;v35
 = var5 (vs5 (vs5 (vs5 vz5)))

v45 : ∀{Γ A B C D E} → Tm5 (snoc5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) E) A;v45
 = var5 (vs5 (vs5 (vs5 (vs5 vz5))))

test5 : ∀{Γ A} → Tm5 Γ (arr5 (arr5 A A) (arr5 A A));test5
  = lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05)))))))
{-# OPTIONS --type-in-type #-}

Ty6 : Set; Ty6
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι6   : Ty6; ι6 = λ _ ι6 _ → ι6
arr6 : Ty6 → Ty6 → Ty6; arr6 = λ A B Ty6 ι6 arr6 → arr6 (A Ty6 ι6 arr6) (B Ty6 ι6 arr6)

Con6 : Set;Con6
 = (Con6 : Set)
   (nil  : Con6)
   (snoc : Con6 → Ty6 → Con6)
 → Con6

nil6 : Con6;nil6
 = λ Con6 nil6 snoc → nil6

snoc6 : Con6 → Ty6 → Con6;snoc6
 = λ Γ A Con6 nil6 snoc6 → snoc6 (Γ Con6 nil6 snoc6) A

Var6 : Con6 → Ty6 → Set;Var6
 = λ Γ A →
   (Var6 : Con6 → Ty6 → Set)
   (vz  : (Γ : _)(A : _) → Var6 (snoc6 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var6 Γ A → Var6 (snoc6 Γ B) A)
 → Var6 Γ A

vz6 : ∀{Γ A} → Var6 (snoc6 Γ A) A;vz6
 = λ Var6 vz6 vs → vz6 _ _

vs6 : ∀{Γ B A} → Var6 Γ A → Var6 (snoc6 Γ B) A;vs6
 = λ x Var6 vz6 vs6 → vs6 _ _ _ (x Var6 vz6 vs6)

Tm6 : Con6 → Ty6 → Set;Tm6
 = λ Γ A →
   (Tm6    : Con6 → Ty6 → Set)
   (var   : (Γ : _) (A : _) → Var6 Γ A → Tm6 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B))
   (app   : (Γ : _) (A B : _) → Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B)
 → Tm6 Γ A

var6 : ∀{Γ A} → Var6 Γ A → Tm6 Γ A;var6
 = λ x Tm6 var6 lam app → var6 _ _ x

lam6 : ∀{Γ A B} → Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B);lam6
 = λ t Tm6 var6 lam6 app → lam6 _ _ _ (t Tm6 var6 lam6 app)

app6 : ∀{Γ A B} → Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B;app6
 = λ t u Tm6 var6 lam6 app6 →
     app6 _ _ _ (t Tm6 var6 lam6 app6) (u Tm6 var6 lam6 app6)

v06 : ∀{Γ A} → Tm6 (snoc6 Γ A) A;v06
 = var6 vz6

v16 : ∀{Γ A B} → Tm6 (snoc6 (snoc6 Γ A) B) A;v16
 = var6 (vs6 vz6)

v26 : ∀{Γ A B C} → Tm6 (snoc6 (snoc6 (snoc6 Γ A) B) C) A;v26
 = var6 (vs6 (vs6 vz6))

v36 : ∀{Γ A B C D} → Tm6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) A;v36
 = var6 (vs6 (vs6 (vs6 vz6)))

v46 : ∀{Γ A B C D E} → Tm6 (snoc6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) E) A;v46
 = var6 (vs6 (vs6 (vs6 (vs6 vz6))))

test6 : ∀{Γ A} → Tm6 Γ (arr6 (arr6 A A) (arr6 A A));test6
  = lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06)))))))
{-# OPTIONS --type-in-type #-}

Ty7 : Set; Ty7
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι7   : Ty7; ι7 = λ _ ι7 _ → ι7
arr7 : Ty7 → Ty7 → Ty7; arr7 = λ A B Ty7 ι7 arr7 → arr7 (A Ty7 ι7 arr7) (B Ty7 ι7 arr7)

Con7 : Set;Con7
 = (Con7 : Set)
   (nil  : Con7)
   (snoc : Con7 → Ty7 → Con7)
 → Con7

nil7 : Con7;nil7
 = λ Con7 nil7 snoc → nil7

snoc7 : Con7 → Ty7 → Con7;snoc7
 = λ Γ A Con7 nil7 snoc7 → snoc7 (Γ Con7 nil7 snoc7) A

Var7 : Con7 → Ty7 → Set;Var7
 = λ Γ A →
   (Var7 : Con7 → Ty7 → Set)
   (vz  : (Γ : _)(A : _) → Var7 (snoc7 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var7 Γ A → Var7 (snoc7 Γ B) A)
 → Var7 Γ A

vz7 : ∀{Γ A} → Var7 (snoc7 Γ A) A;vz7
 = λ Var7 vz7 vs → vz7 _ _

vs7 : ∀{Γ B A} → Var7 Γ A → Var7 (snoc7 Γ B) A;vs7
 = λ x Var7 vz7 vs7 → vs7 _ _ _ (x Var7 vz7 vs7)

Tm7 : Con7 → Ty7 → Set;Tm7
 = λ Γ A →
   (Tm7    : Con7 → Ty7 → Set)
   (var   : (Γ : _) (A : _) → Var7 Γ A → Tm7 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B))
   (app   : (Γ : _) (A B : _) → Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B)
 → Tm7 Γ A

var7 : ∀{Γ A} → Var7 Γ A → Tm7 Γ A;var7
 = λ x Tm7 var7 lam app → var7 _ _ x

lam7 : ∀{Γ A B} → Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B);lam7
 = λ t Tm7 var7 lam7 app → lam7 _ _ _ (t Tm7 var7 lam7 app)

app7 : ∀{Γ A B} → Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B;app7
 = λ t u Tm7 var7 lam7 app7 →
     app7 _ _ _ (t Tm7 var7 lam7 app7) (u Tm7 var7 lam7 app7)

v07 : ∀{Γ A} → Tm7 (snoc7 Γ A) A;v07
 = var7 vz7

v17 : ∀{Γ A B} → Tm7 (snoc7 (snoc7 Γ A) B) A;v17
 = var7 (vs7 vz7)

v27 : ∀{Γ A B C} → Tm7 (snoc7 (snoc7 (snoc7 Γ A) B) C) A;v27
 = var7 (vs7 (vs7 vz7))

v37 : ∀{Γ A B C D} → Tm7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) A;v37
 = var7 (vs7 (vs7 (vs7 vz7)))

v47 : ∀{Γ A B C D E} → Tm7 (snoc7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) E) A;v47
 = var7 (vs7 (vs7 (vs7 (vs7 vz7))))

test7 : ∀{Γ A} → Tm7 Γ (arr7 (arr7 A A) (arr7 A A));test7
  = lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07)))))))
{-# OPTIONS --type-in-type #-}

Ty8 : Set; Ty8
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι8   : Ty8; ι8 = λ _ ι8 _ → ι8
arr8 : Ty8 → Ty8 → Ty8; arr8 = λ A B Ty8 ι8 arr8 → arr8 (A Ty8 ι8 arr8) (B Ty8 ι8 arr8)

Con8 : Set;Con8
 = (Con8 : Set)
   (nil  : Con8)
   (snoc : Con8 → Ty8 → Con8)
 → Con8

nil8 : Con8;nil8
 = λ Con8 nil8 snoc → nil8

snoc8 : Con8 → Ty8 → Con8;snoc8
 = λ Γ A Con8 nil8 snoc8 → snoc8 (Γ Con8 nil8 snoc8) A

Var8 : Con8 → Ty8 → Set;Var8
 = λ Γ A →
   (Var8 : Con8 → Ty8 → Set)
   (vz  : (Γ : _)(A : _) → Var8 (snoc8 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var8 Γ A → Var8 (snoc8 Γ B) A)
 → Var8 Γ A

vz8 : ∀{Γ A} → Var8 (snoc8 Γ A) A;vz8
 = λ Var8 vz8 vs → vz8 _ _

vs8 : ∀{Γ B A} → Var8 Γ A → Var8 (snoc8 Γ B) A;vs8
 = λ x Var8 vz8 vs8 → vs8 _ _ _ (x Var8 vz8 vs8)

Tm8 : Con8 → Ty8 → Set;Tm8
 = λ Γ A →
   (Tm8    : Con8 → Ty8 → Set)
   (var   : (Γ : _) (A : _) → Var8 Γ A → Tm8 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B))
   (app   : (Γ : _) (A B : _) → Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B)
 → Tm8 Γ A

var8 : ∀{Γ A} → Var8 Γ A → Tm8 Γ A;var8
 = λ x Tm8 var8 lam app → var8 _ _ x

lam8 : ∀{Γ A B} → Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B);lam8
 = λ t Tm8 var8 lam8 app → lam8 _ _ _ (t Tm8 var8 lam8 app)

app8 : ∀{Γ A B} → Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B;app8
 = λ t u Tm8 var8 lam8 app8 →
     app8 _ _ _ (t Tm8 var8 lam8 app8) (u Tm8 var8 lam8 app8)

v08 : ∀{Γ A} → Tm8 (snoc8 Γ A) A;v08
 = var8 vz8

v18 : ∀{Γ A B} → Tm8 (snoc8 (snoc8 Γ A) B) A;v18
 = var8 (vs8 vz8)

v28 : ∀{Γ A B C} → Tm8 (snoc8 (snoc8 (snoc8 Γ A) B) C) A;v28
 = var8 (vs8 (vs8 vz8))

v38 : ∀{Γ A B C D} → Tm8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) A;v38
 = var8 (vs8 (vs8 (vs8 vz8)))

v48 : ∀{Γ A B C D E} → Tm8 (snoc8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) E) A;v48
 = var8 (vs8 (vs8 (vs8 (vs8 vz8))))

test8 : ∀{Γ A} → Tm8 Γ (arr8 (arr8 A A) (arr8 A A));test8
  = lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08)))))))
{-# OPTIONS --type-in-type #-}

Ty9 : Set; Ty9
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι9   : Ty9; ι9 = λ _ ι9 _ → ι9
arr9 : Ty9 → Ty9 → Ty9; arr9 = λ A B Ty9 ι9 arr9 → arr9 (A Ty9 ι9 arr9) (B Ty9 ι9 arr9)

Con9 : Set;Con9
 = (Con9 : Set)
   (nil  : Con9)
   (snoc : Con9 → Ty9 → Con9)
 → Con9

nil9 : Con9;nil9
 = λ Con9 nil9 snoc → nil9

snoc9 : Con9 → Ty9 → Con9;snoc9
 = λ Γ A Con9 nil9 snoc9 → snoc9 (Γ Con9 nil9 snoc9) A

Var9 : Con9 → Ty9 → Set;Var9
 = λ Γ A →
   (Var9 : Con9 → Ty9 → Set)
   (vz  : (Γ : _)(A : _) → Var9 (snoc9 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var9 Γ A → Var9 (snoc9 Γ B) A)
 → Var9 Γ A

vz9 : ∀{Γ A} → Var9 (snoc9 Γ A) A;vz9
 = λ Var9 vz9 vs → vz9 _ _

vs9 : ∀{Γ B A} → Var9 Γ A → Var9 (snoc9 Γ B) A;vs9
 = λ x Var9 vz9 vs9 → vs9 _ _ _ (x Var9 vz9 vs9)

Tm9 : Con9 → Ty9 → Set;Tm9
 = λ Γ A →
   (Tm9    : Con9 → Ty9 → Set)
   (var   : (Γ : _) (A : _) → Var9 Γ A → Tm9 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B))
   (app   : (Γ : _) (A B : _) → Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B)
 → Tm9 Γ A

var9 : ∀{Γ A} → Var9 Γ A → Tm9 Γ A;var9
 = λ x Tm9 var9 lam app → var9 _ _ x

lam9 : ∀{Γ A B} → Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B);lam9
 = λ t Tm9 var9 lam9 app → lam9 _ _ _ (t Tm9 var9 lam9 app)

app9 : ∀{Γ A B} → Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B;app9
 = λ t u Tm9 var9 lam9 app9 →
     app9 _ _ _ (t Tm9 var9 lam9 app9) (u Tm9 var9 lam9 app9)

v09 : ∀{Γ A} → Tm9 (snoc9 Γ A) A;v09
 = var9 vz9

v19 : ∀{Γ A B} → Tm9 (snoc9 (snoc9 Γ A) B) A;v19
 = var9 (vs9 vz9)

v29 : ∀{Γ A B C} → Tm9 (snoc9 (snoc9 (snoc9 Γ A) B) C) A;v29
 = var9 (vs9 (vs9 vz9))

v39 : ∀{Γ A B C D} → Tm9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) A;v39
 = var9 (vs9 (vs9 (vs9 vz9)))

v49 : ∀{Γ A B C D E} → Tm9 (snoc9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) E) A;v49
 = var9 (vs9 (vs9 (vs9 (vs9 vz9))))

test9 : ∀{Γ A} → Tm9 Γ (arr9 (arr9 A A) (arr9 A A));test9
  = lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09)))))))
{-# OPTIONS --type-in-type #-}

Ty10 : Set; Ty10
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι10   : Ty10; ι10 = λ _ ι10 _ → ι10
arr10 : Ty10 → Ty10 → Ty10; arr10 = λ A B Ty10 ι10 arr10 → arr10 (A Ty10 ι10 arr10) (B Ty10 ι10 arr10)

Con10 : Set;Con10
 = (Con10 : Set)
   (nil  : Con10)
   (snoc : Con10 → Ty10 → Con10)
 → Con10

nil10 : Con10;nil10
 = λ Con10 nil10 snoc → nil10

snoc10 : Con10 → Ty10 → Con10;snoc10
 = λ Γ A Con10 nil10 snoc10 → snoc10 (Γ Con10 nil10 snoc10) A

Var10 : Con10 → Ty10 → Set;Var10
 = λ Γ A →
   (Var10 : Con10 → Ty10 → Set)
   (vz  : (Γ : _)(A : _) → Var10 (snoc10 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var10 Γ A → Var10 (snoc10 Γ B) A)
 → Var10 Γ A

vz10 : ∀{Γ A} → Var10 (snoc10 Γ A) A;vz10
 = λ Var10 vz10 vs → vz10 _ _

vs10 : ∀{Γ B A} → Var10 Γ A → Var10 (snoc10 Γ B) A;vs10
 = λ x Var10 vz10 vs10 → vs10 _ _ _ (x Var10 vz10 vs10)

Tm10 : Con10 → Ty10 → Set;Tm10
 = λ Γ A →
   (Tm10    : Con10 → Ty10 → Set)
   (var   : (Γ : _) (A : _) → Var10 Γ A → Tm10 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B))
   (app   : (Γ : _) (A B : _) → Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B)
 → Tm10 Γ A

var10 : ∀{Γ A} → Var10 Γ A → Tm10 Γ A;var10
 = λ x Tm10 var10 lam app → var10 _ _ x

lam10 : ∀{Γ A B} → Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B);lam10
 = λ t Tm10 var10 lam10 app → lam10 _ _ _ (t Tm10 var10 lam10 app)

app10 : ∀{Γ A B} → Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B;app10
 = λ t u Tm10 var10 lam10 app10 →
     app10 _ _ _ (t Tm10 var10 lam10 app10) (u Tm10 var10 lam10 app10)

v010 : ∀{Γ A} → Tm10 (snoc10 Γ A) A;v010
 = var10 vz10

v110 : ∀{Γ A B} → Tm10 (snoc10 (snoc10 Γ A) B) A;v110
 = var10 (vs10 vz10)

v210 : ∀{Γ A B C} → Tm10 (snoc10 (snoc10 (snoc10 Γ A) B) C) A;v210
 = var10 (vs10 (vs10 vz10))

v310 : ∀{Γ A B C D} → Tm10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) A;v310
 = var10 (vs10 (vs10 (vs10 vz10)))

v410 : ∀{Γ A B C D E} → Tm10 (snoc10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) E) A;v410
 = var10 (vs10 (vs10 (vs10 (vs10 vz10))))

test10 : ∀{Γ A} → Tm10 Γ (arr10 (arr10 A A) (arr10 A A));test10
  = lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010)))))))
{-# OPTIONS --type-in-type #-}

Ty11 : Set; Ty11
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι11   : Ty11; ι11 = λ _ ι11 _ → ι11
arr11 : Ty11 → Ty11 → Ty11; arr11 = λ A B Ty11 ι11 arr11 → arr11 (A Ty11 ι11 arr11) (B Ty11 ι11 arr11)

Con11 : Set;Con11
 = (Con11 : Set)
   (nil  : Con11)
   (snoc : Con11 → Ty11 → Con11)
 → Con11

nil11 : Con11;nil11
 = λ Con11 nil11 snoc → nil11

snoc11 : Con11 → Ty11 → Con11;snoc11
 = λ Γ A Con11 nil11 snoc11 → snoc11 (Γ Con11 nil11 snoc11) A

Var11 : Con11 → Ty11 → Set;Var11
 = λ Γ A →
   (Var11 : Con11 → Ty11 → Set)
   (vz  : (Γ : _)(A : _) → Var11 (snoc11 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var11 Γ A → Var11 (snoc11 Γ B) A)
 → Var11 Γ A

vz11 : ∀{Γ A} → Var11 (snoc11 Γ A) A;vz11
 = λ Var11 vz11 vs → vz11 _ _

vs11 : ∀{Γ B A} → Var11 Γ A → Var11 (snoc11 Γ B) A;vs11
 = λ x Var11 vz11 vs11 → vs11 _ _ _ (x Var11 vz11 vs11)

Tm11 : Con11 → Ty11 → Set;Tm11
 = λ Γ A →
   (Tm11    : Con11 → Ty11 → Set)
   (var   : (Γ : _) (A : _) → Var11 Γ A → Tm11 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B))
   (app   : (Γ : _) (A B : _) → Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B)
 → Tm11 Γ A

var11 : ∀{Γ A} → Var11 Γ A → Tm11 Γ A;var11
 = λ x Tm11 var11 lam app → var11 _ _ x

lam11 : ∀{Γ A B} → Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B);lam11
 = λ t Tm11 var11 lam11 app → lam11 _ _ _ (t Tm11 var11 lam11 app)

app11 : ∀{Γ A B} → Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B;app11
 = λ t u Tm11 var11 lam11 app11 →
     app11 _ _ _ (t Tm11 var11 lam11 app11) (u Tm11 var11 lam11 app11)

v011 : ∀{Γ A} → Tm11 (snoc11 Γ A) A;v011
 = var11 vz11

v111 : ∀{Γ A B} → Tm11 (snoc11 (snoc11 Γ A) B) A;v111
 = var11 (vs11 vz11)

v211 : ∀{Γ A B C} → Tm11 (snoc11 (snoc11 (snoc11 Γ A) B) C) A;v211
 = var11 (vs11 (vs11 vz11))

v311 : ∀{Γ A B C D} → Tm11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) A;v311
 = var11 (vs11 (vs11 (vs11 vz11)))

v411 : ∀{Γ A B C D E} → Tm11 (snoc11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) E) A;v411
 = var11 (vs11 (vs11 (vs11 (vs11 vz11))))

test11 : ∀{Γ A} → Tm11 Γ (arr11 (arr11 A A) (arr11 A A));test11
  = lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011)))))))
{-# OPTIONS --type-in-type #-}

Ty12 : Set; Ty12
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι12   : Ty12; ι12 = λ _ ι12 _ → ι12
arr12 : Ty12 → Ty12 → Ty12; arr12 = λ A B Ty12 ι12 arr12 → arr12 (A Ty12 ι12 arr12) (B Ty12 ι12 arr12)

Con12 : Set;Con12
 = (Con12 : Set)
   (nil  : Con12)
   (snoc : Con12 → Ty12 → Con12)
 → Con12

nil12 : Con12;nil12
 = λ Con12 nil12 snoc → nil12

snoc12 : Con12 → Ty12 → Con12;snoc12
 = λ Γ A Con12 nil12 snoc12 → snoc12 (Γ Con12 nil12 snoc12) A

Var12 : Con12 → Ty12 → Set;Var12
 = λ Γ A →
   (Var12 : Con12 → Ty12 → Set)
   (vz  : (Γ : _)(A : _) → Var12 (snoc12 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var12 Γ A → Var12 (snoc12 Γ B) A)
 → Var12 Γ A

vz12 : ∀{Γ A} → Var12 (snoc12 Γ A) A;vz12
 = λ Var12 vz12 vs → vz12 _ _

vs12 : ∀{Γ B A} → Var12 Γ A → Var12 (snoc12 Γ B) A;vs12
 = λ x Var12 vz12 vs12 → vs12 _ _ _ (x Var12 vz12 vs12)

Tm12 : Con12 → Ty12 → Set;Tm12
 = λ Γ A →
   (Tm12    : Con12 → Ty12 → Set)
   (var   : (Γ : _) (A : _) → Var12 Γ A → Tm12 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B))
   (app   : (Γ : _) (A B : _) → Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B)
 → Tm12 Γ A

var12 : ∀{Γ A} → Var12 Γ A → Tm12 Γ A;var12
 = λ x Tm12 var12 lam app → var12 _ _ x

lam12 : ∀{Γ A B} → Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B);lam12
 = λ t Tm12 var12 lam12 app → lam12 _ _ _ (t Tm12 var12 lam12 app)

app12 : ∀{Γ A B} → Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B;app12
 = λ t u Tm12 var12 lam12 app12 →
     app12 _ _ _ (t Tm12 var12 lam12 app12) (u Tm12 var12 lam12 app12)

v012 : ∀{Γ A} → Tm12 (snoc12 Γ A) A;v012
 = var12 vz12

v112 : ∀{Γ A B} → Tm12 (snoc12 (snoc12 Γ A) B) A;v112
 = var12 (vs12 vz12)

v212 : ∀{Γ A B C} → Tm12 (snoc12 (snoc12 (snoc12 Γ A) B) C) A;v212
 = var12 (vs12 (vs12 vz12))

v312 : ∀{Γ A B C D} → Tm12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) A;v312
 = var12 (vs12 (vs12 (vs12 vz12)))

v412 : ∀{Γ A B C D E} → Tm12 (snoc12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) E) A;v412
 = var12 (vs12 (vs12 (vs12 (vs12 vz12))))

test12 : ∀{Γ A} → Tm12 Γ (arr12 (arr12 A A) (arr12 A A));test12
  = lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012)))))))
{-# OPTIONS --type-in-type #-}

Ty13 : Set; Ty13
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι13   : Ty13; ι13 = λ _ ι13 _ → ι13
arr13 : Ty13 → Ty13 → Ty13; arr13 = λ A B Ty13 ι13 arr13 → arr13 (A Ty13 ι13 arr13) (B Ty13 ι13 arr13)

Con13 : Set;Con13
 = (Con13 : Set)
   (nil  : Con13)
   (snoc : Con13 → Ty13 → Con13)
 → Con13

nil13 : Con13;nil13
 = λ Con13 nil13 snoc → nil13

snoc13 : Con13 → Ty13 → Con13;snoc13
 = λ Γ A Con13 nil13 snoc13 → snoc13 (Γ Con13 nil13 snoc13) A

Var13 : Con13 → Ty13 → Set;Var13
 = λ Γ A →
   (Var13 : Con13 → Ty13 → Set)
   (vz  : (Γ : _)(A : _) → Var13 (snoc13 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var13 Γ A → Var13 (snoc13 Γ B) A)
 → Var13 Γ A

vz13 : ∀{Γ A} → Var13 (snoc13 Γ A) A;vz13
 = λ Var13 vz13 vs → vz13 _ _

vs13 : ∀{Γ B A} → Var13 Γ A → Var13 (snoc13 Γ B) A;vs13
 = λ x Var13 vz13 vs13 → vs13 _ _ _ (x Var13 vz13 vs13)

Tm13 : Con13 → Ty13 → Set;Tm13
 = λ Γ A →
   (Tm13    : Con13 → Ty13 → Set)
   (var   : (Γ : _) (A : _) → Var13 Γ A → Tm13 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B))
   (app   : (Γ : _) (A B : _) → Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B)
 → Tm13 Γ A

var13 : ∀{Γ A} → Var13 Γ A → Tm13 Γ A;var13
 = λ x Tm13 var13 lam app → var13 _ _ x

lam13 : ∀{Γ A B} → Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B);lam13
 = λ t Tm13 var13 lam13 app → lam13 _ _ _ (t Tm13 var13 lam13 app)

app13 : ∀{Γ A B} → Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B;app13
 = λ t u Tm13 var13 lam13 app13 →
     app13 _ _ _ (t Tm13 var13 lam13 app13) (u Tm13 var13 lam13 app13)

v013 : ∀{Γ A} → Tm13 (snoc13 Γ A) A;v013
 = var13 vz13

v113 : ∀{Γ A B} → Tm13 (snoc13 (snoc13 Γ A) B) A;v113
 = var13 (vs13 vz13)

v213 : ∀{Γ A B C} → Tm13 (snoc13 (snoc13 (snoc13 Γ A) B) C) A;v213
 = var13 (vs13 (vs13 vz13))

v313 : ∀{Γ A B C D} → Tm13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) A;v313
 = var13 (vs13 (vs13 (vs13 vz13)))

v413 : ∀{Γ A B C D E} → Tm13 (snoc13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) E) A;v413
 = var13 (vs13 (vs13 (vs13 (vs13 vz13))))

test13 : ∀{Γ A} → Tm13 Γ (arr13 (arr13 A A) (arr13 A A));test13
  = lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013)))))))
{-# OPTIONS --type-in-type #-}

Ty14 : Set; Ty14
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι14   : Ty14; ι14 = λ _ ι14 _ → ι14
arr14 : Ty14 → Ty14 → Ty14; arr14 = λ A B Ty14 ι14 arr14 → arr14 (A Ty14 ι14 arr14) (B Ty14 ι14 arr14)

Con14 : Set;Con14
 = (Con14 : Set)
   (nil  : Con14)
   (snoc : Con14 → Ty14 → Con14)
 → Con14

nil14 : Con14;nil14
 = λ Con14 nil14 snoc → nil14

snoc14 : Con14 → Ty14 → Con14;snoc14
 = λ Γ A Con14 nil14 snoc14 → snoc14 (Γ Con14 nil14 snoc14) A

Var14 : Con14 → Ty14 → Set;Var14
 = λ Γ A →
   (Var14 : Con14 → Ty14 → Set)
   (vz  : (Γ : _)(A : _) → Var14 (snoc14 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var14 Γ A → Var14 (snoc14 Γ B) A)
 → Var14 Γ A

vz14 : ∀{Γ A} → Var14 (snoc14 Γ A) A;vz14
 = λ Var14 vz14 vs → vz14 _ _

vs14 : ∀{Γ B A} → Var14 Γ A → Var14 (snoc14 Γ B) A;vs14
 = λ x Var14 vz14 vs14 → vs14 _ _ _ (x Var14 vz14 vs14)

Tm14 : Con14 → Ty14 → Set;Tm14
 = λ Γ A →
   (Tm14    : Con14 → Ty14 → Set)
   (var   : (Γ : _) (A : _) → Var14 Γ A → Tm14 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B))
   (app   : (Γ : _) (A B : _) → Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B)
 → Tm14 Γ A

var14 : ∀{Γ A} → Var14 Γ A → Tm14 Γ A;var14
 = λ x Tm14 var14 lam app → var14 _ _ x

lam14 : ∀{Γ A B} → Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B);lam14
 = λ t Tm14 var14 lam14 app → lam14 _ _ _ (t Tm14 var14 lam14 app)

app14 : ∀{Γ A B} → Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B;app14
 = λ t u Tm14 var14 lam14 app14 →
     app14 _ _ _ (t Tm14 var14 lam14 app14) (u Tm14 var14 lam14 app14)

v014 : ∀{Γ A} → Tm14 (snoc14 Γ A) A;v014
 = var14 vz14

v114 : ∀{Γ A B} → Tm14 (snoc14 (snoc14 Γ A) B) A;v114
 = var14 (vs14 vz14)

v214 : ∀{Γ A B C} → Tm14 (snoc14 (snoc14 (snoc14 Γ A) B) C) A;v214
 = var14 (vs14 (vs14 vz14))

v314 : ∀{Γ A B C D} → Tm14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) A;v314
 = var14 (vs14 (vs14 (vs14 vz14)))

v414 : ∀{Γ A B C D E} → Tm14 (snoc14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) E) A;v414
 = var14 (vs14 (vs14 (vs14 (vs14 vz14))))

test14 : ∀{Γ A} → Tm14 Γ (arr14 (arr14 A A) (arr14 A A));test14
  = lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014)))))))
{-# OPTIONS --type-in-type #-}

Ty15 : Set; Ty15
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι15   : Ty15; ι15 = λ _ ι15 _ → ι15
arr15 : Ty15 → Ty15 → Ty15; arr15 = λ A B Ty15 ι15 arr15 → arr15 (A Ty15 ι15 arr15) (B Ty15 ι15 arr15)

Con15 : Set;Con15
 = (Con15 : Set)
   (nil  : Con15)
   (snoc : Con15 → Ty15 → Con15)
 → Con15

nil15 : Con15;nil15
 = λ Con15 nil15 snoc → nil15

snoc15 : Con15 → Ty15 → Con15;snoc15
 = λ Γ A Con15 nil15 snoc15 → snoc15 (Γ Con15 nil15 snoc15) A

Var15 : Con15 → Ty15 → Set;Var15
 = λ Γ A →
   (Var15 : Con15 → Ty15 → Set)
   (vz  : (Γ : _)(A : _) → Var15 (snoc15 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var15 Γ A → Var15 (snoc15 Γ B) A)
 → Var15 Γ A

vz15 : ∀{Γ A} → Var15 (snoc15 Γ A) A;vz15
 = λ Var15 vz15 vs → vz15 _ _

vs15 : ∀{Γ B A} → Var15 Γ A → Var15 (snoc15 Γ B) A;vs15
 = λ x Var15 vz15 vs15 → vs15 _ _ _ (x Var15 vz15 vs15)

Tm15 : Con15 → Ty15 → Set;Tm15
 = λ Γ A →
   (Tm15    : Con15 → Ty15 → Set)
   (var   : (Γ : _) (A : _) → Var15 Γ A → Tm15 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B))
   (app   : (Γ : _) (A B : _) → Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B)
 → Tm15 Γ A

var15 : ∀{Γ A} → Var15 Γ A → Tm15 Γ A;var15
 = λ x Tm15 var15 lam app → var15 _ _ x

lam15 : ∀{Γ A B} → Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B);lam15
 = λ t Tm15 var15 lam15 app → lam15 _ _ _ (t Tm15 var15 lam15 app)

app15 : ∀{Γ A B} → Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B;app15
 = λ t u Tm15 var15 lam15 app15 →
     app15 _ _ _ (t Tm15 var15 lam15 app15) (u Tm15 var15 lam15 app15)

v015 : ∀{Γ A} → Tm15 (snoc15 Γ A) A;v015
 = var15 vz15

v115 : ∀{Γ A B} → Tm15 (snoc15 (snoc15 Γ A) B) A;v115
 = var15 (vs15 vz15)

v215 : ∀{Γ A B C} → Tm15 (snoc15 (snoc15 (snoc15 Γ A) B) C) A;v215
 = var15 (vs15 (vs15 vz15))

v315 : ∀{Γ A B C D} → Tm15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) A;v315
 = var15 (vs15 (vs15 (vs15 vz15)))

v415 : ∀{Γ A B C D E} → Tm15 (snoc15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) E) A;v415
 = var15 (vs15 (vs15 (vs15 (vs15 vz15))))

test15 : ∀{Γ A} → Tm15 Γ (arr15 (arr15 A A) (arr15 A A));test15
  = lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015)))))))
{-# OPTIONS --type-in-type #-}

Ty16 : Set; Ty16
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι16   : Ty16; ι16 = λ _ ι16 _ → ι16
arr16 : Ty16 → Ty16 → Ty16; arr16 = λ A B Ty16 ι16 arr16 → arr16 (A Ty16 ι16 arr16) (B Ty16 ι16 arr16)

Con16 : Set;Con16
 = (Con16 : Set)
   (nil  : Con16)
   (snoc : Con16 → Ty16 → Con16)
 → Con16

nil16 : Con16;nil16
 = λ Con16 nil16 snoc → nil16

snoc16 : Con16 → Ty16 → Con16;snoc16
 = λ Γ A Con16 nil16 snoc16 → snoc16 (Γ Con16 nil16 snoc16) A

Var16 : Con16 → Ty16 → Set;Var16
 = λ Γ A →
   (Var16 : Con16 → Ty16 → Set)
   (vz  : (Γ : _)(A : _) → Var16 (snoc16 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var16 Γ A → Var16 (snoc16 Γ B) A)
 → Var16 Γ A

vz16 : ∀{Γ A} → Var16 (snoc16 Γ A) A;vz16
 = λ Var16 vz16 vs → vz16 _ _

vs16 : ∀{Γ B A} → Var16 Γ A → Var16 (snoc16 Γ B) A;vs16
 = λ x Var16 vz16 vs16 → vs16 _ _ _ (x Var16 vz16 vs16)

Tm16 : Con16 → Ty16 → Set;Tm16
 = λ Γ A →
   (Tm16    : Con16 → Ty16 → Set)
   (var   : (Γ : _) (A : _) → Var16 Γ A → Tm16 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B))
   (app   : (Γ : _) (A B : _) → Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B)
 → Tm16 Γ A

var16 : ∀{Γ A} → Var16 Γ A → Tm16 Γ A;var16
 = λ x Tm16 var16 lam app → var16 _ _ x

lam16 : ∀{Γ A B} → Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B);lam16
 = λ t Tm16 var16 lam16 app → lam16 _ _ _ (t Tm16 var16 lam16 app)

app16 : ∀{Γ A B} → Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B;app16
 = λ t u Tm16 var16 lam16 app16 →
     app16 _ _ _ (t Tm16 var16 lam16 app16) (u Tm16 var16 lam16 app16)

v016 : ∀{Γ A} → Tm16 (snoc16 Γ A) A;v016
 = var16 vz16

v116 : ∀{Γ A B} → Tm16 (snoc16 (snoc16 Γ A) B) A;v116
 = var16 (vs16 vz16)

v216 : ∀{Γ A B C} → Tm16 (snoc16 (snoc16 (snoc16 Γ A) B) C) A;v216
 = var16 (vs16 (vs16 vz16))

v316 : ∀{Γ A B C D} → Tm16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) A;v316
 = var16 (vs16 (vs16 (vs16 vz16)))

v416 : ∀{Γ A B C D E} → Tm16 (snoc16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) E) A;v416
 = var16 (vs16 (vs16 (vs16 (vs16 vz16))))

test16 : ∀{Γ A} → Tm16 Γ (arr16 (arr16 A A) (arr16 A A));test16
  = lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016)))))))
{-# OPTIONS --type-in-type #-}

Ty17 : Set; Ty17
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι17   : Ty17; ι17 = λ _ ι17 _ → ι17
arr17 : Ty17 → Ty17 → Ty17; arr17 = λ A B Ty17 ι17 arr17 → arr17 (A Ty17 ι17 arr17) (B Ty17 ι17 arr17)

Con17 : Set;Con17
 = (Con17 : Set)
   (nil  : Con17)
   (snoc : Con17 → Ty17 → Con17)
 → Con17

nil17 : Con17;nil17
 = λ Con17 nil17 snoc → nil17

snoc17 : Con17 → Ty17 → Con17;snoc17
 = λ Γ A Con17 nil17 snoc17 → snoc17 (Γ Con17 nil17 snoc17) A

Var17 : Con17 → Ty17 → Set;Var17
 = λ Γ A →
   (Var17 : Con17 → Ty17 → Set)
   (vz  : (Γ : _)(A : _) → Var17 (snoc17 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var17 Γ A → Var17 (snoc17 Γ B) A)
 → Var17 Γ A

vz17 : ∀{Γ A} → Var17 (snoc17 Γ A) A;vz17
 = λ Var17 vz17 vs → vz17 _ _

vs17 : ∀{Γ B A} → Var17 Γ A → Var17 (snoc17 Γ B) A;vs17
 = λ x Var17 vz17 vs17 → vs17 _ _ _ (x Var17 vz17 vs17)

Tm17 : Con17 → Ty17 → Set;Tm17
 = λ Γ A →
   (Tm17    : Con17 → Ty17 → Set)
   (var   : (Γ : _) (A : _) → Var17 Γ A → Tm17 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B))
   (app   : (Γ : _) (A B : _) → Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B)
 → Tm17 Γ A

var17 : ∀{Γ A} → Var17 Γ A → Tm17 Γ A;var17
 = λ x Tm17 var17 lam app → var17 _ _ x

lam17 : ∀{Γ A B} → Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B);lam17
 = λ t Tm17 var17 lam17 app → lam17 _ _ _ (t Tm17 var17 lam17 app)

app17 : ∀{Γ A B} → Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B;app17
 = λ t u Tm17 var17 lam17 app17 →
     app17 _ _ _ (t Tm17 var17 lam17 app17) (u Tm17 var17 lam17 app17)

v017 : ∀{Γ A} → Tm17 (snoc17 Γ A) A;v017
 = var17 vz17

v117 : ∀{Γ A B} → Tm17 (snoc17 (snoc17 Γ A) B) A;v117
 = var17 (vs17 vz17)

v217 : ∀{Γ A B C} → Tm17 (snoc17 (snoc17 (snoc17 Γ A) B) C) A;v217
 = var17 (vs17 (vs17 vz17))

v317 : ∀{Γ A B C D} → Tm17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) A;v317
 = var17 (vs17 (vs17 (vs17 vz17)))

v417 : ∀{Γ A B C D E} → Tm17 (snoc17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) E) A;v417
 = var17 (vs17 (vs17 (vs17 (vs17 vz17))))

test17 : ∀{Γ A} → Tm17 Γ (arr17 (arr17 A A) (arr17 A A));test17
  = lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017)))))))
{-# OPTIONS --type-in-type #-}

Ty18 : Set; Ty18
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι18   : Ty18; ι18 = λ _ ι18 _ → ι18
arr18 : Ty18 → Ty18 → Ty18; arr18 = λ A B Ty18 ι18 arr18 → arr18 (A Ty18 ι18 arr18) (B Ty18 ι18 arr18)

Con18 : Set;Con18
 = (Con18 : Set)
   (nil  : Con18)
   (snoc : Con18 → Ty18 → Con18)
 → Con18

nil18 : Con18;nil18
 = λ Con18 nil18 snoc → nil18

snoc18 : Con18 → Ty18 → Con18;snoc18
 = λ Γ A Con18 nil18 snoc18 → snoc18 (Γ Con18 nil18 snoc18) A

Var18 : Con18 → Ty18 → Set;Var18
 = λ Γ A →
   (Var18 : Con18 → Ty18 → Set)
   (vz  : (Γ : _)(A : _) → Var18 (snoc18 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var18 Γ A → Var18 (snoc18 Γ B) A)
 → Var18 Γ A

vz18 : ∀{Γ A} → Var18 (snoc18 Γ A) A;vz18
 = λ Var18 vz18 vs → vz18 _ _

vs18 : ∀{Γ B A} → Var18 Γ A → Var18 (snoc18 Γ B) A;vs18
 = λ x Var18 vz18 vs18 → vs18 _ _ _ (x Var18 vz18 vs18)

Tm18 : Con18 → Ty18 → Set;Tm18
 = λ Γ A →
   (Tm18    : Con18 → Ty18 → Set)
   (var   : (Γ : _) (A : _) → Var18 Γ A → Tm18 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B))
   (app   : (Γ : _) (A B : _) → Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B)
 → Tm18 Γ A

var18 : ∀{Γ A} → Var18 Γ A → Tm18 Γ A;var18
 = λ x Tm18 var18 lam app → var18 _ _ x

lam18 : ∀{Γ A B} → Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B);lam18
 = λ t Tm18 var18 lam18 app → lam18 _ _ _ (t Tm18 var18 lam18 app)

app18 : ∀{Γ A B} → Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B;app18
 = λ t u Tm18 var18 lam18 app18 →
     app18 _ _ _ (t Tm18 var18 lam18 app18) (u Tm18 var18 lam18 app18)

v018 : ∀{Γ A} → Tm18 (snoc18 Γ A) A;v018
 = var18 vz18

v118 : ∀{Γ A B} → Tm18 (snoc18 (snoc18 Γ A) B) A;v118
 = var18 (vs18 vz18)

v218 : ∀{Γ A B C} → Tm18 (snoc18 (snoc18 (snoc18 Γ A) B) C) A;v218
 = var18 (vs18 (vs18 vz18))

v318 : ∀{Γ A B C D} → Tm18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) A;v318
 = var18 (vs18 (vs18 (vs18 vz18)))

v418 : ∀{Γ A B C D E} → Tm18 (snoc18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) E) A;v418
 = var18 (vs18 (vs18 (vs18 (vs18 vz18))))

test18 : ∀{Γ A} → Tm18 Γ (arr18 (arr18 A A) (arr18 A A));test18
  = lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018)))))))
{-# OPTIONS --type-in-type #-}

Ty19 : Set; Ty19
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι19   : Ty19; ι19 = λ _ ι19 _ → ι19
arr19 : Ty19 → Ty19 → Ty19; arr19 = λ A B Ty19 ι19 arr19 → arr19 (A Ty19 ι19 arr19) (B Ty19 ι19 arr19)

Con19 : Set;Con19
 = (Con19 : Set)
   (nil  : Con19)
   (snoc : Con19 → Ty19 → Con19)
 → Con19

nil19 : Con19;nil19
 = λ Con19 nil19 snoc → nil19

snoc19 : Con19 → Ty19 → Con19;snoc19
 = λ Γ A Con19 nil19 snoc19 → snoc19 (Γ Con19 nil19 snoc19) A

Var19 : Con19 → Ty19 → Set;Var19
 = λ Γ A →
   (Var19 : Con19 → Ty19 → Set)
   (vz  : (Γ : _)(A : _) → Var19 (snoc19 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var19 Γ A → Var19 (snoc19 Γ B) A)
 → Var19 Γ A

vz19 : ∀{Γ A} → Var19 (snoc19 Γ A) A;vz19
 = λ Var19 vz19 vs → vz19 _ _

vs19 : ∀{Γ B A} → Var19 Γ A → Var19 (snoc19 Γ B) A;vs19
 = λ x Var19 vz19 vs19 → vs19 _ _ _ (x Var19 vz19 vs19)

Tm19 : Con19 → Ty19 → Set;Tm19
 = λ Γ A →
   (Tm19    : Con19 → Ty19 → Set)
   (var   : (Γ : _) (A : _) → Var19 Γ A → Tm19 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B))
   (app   : (Γ : _) (A B : _) → Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B)
 → Tm19 Γ A

var19 : ∀{Γ A} → Var19 Γ A → Tm19 Γ A;var19
 = λ x Tm19 var19 lam app → var19 _ _ x

lam19 : ∀{Γ A B} → Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B);lam19
 = λ t Tm19 var19 lam19 app → lam19 _ _ _ (t Tm19 var19 lam19 app)

app19 : ∀{Γ A B} → Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B;app19
 = λ t u Tm19 var19 lam19 app19 →
     app19 _ _ _ (t Tm19 var19 lam19 app19) (u Tm19 var19 lam19 app19)

v019 : ∀{Γ A} → Tm19 (snoc19 Γ A) A;v019
 = var19 vz19

v119 : ∀{Γ A B} → Tm19 (snoc19 (snoc19 Γ A) B) A;v119
 = var19 (vs19 vz19)

v219 : ∀{Γ A B C} → Tm19 (snoc19 (snoc19 (snoc19 Γ A) B) C) A;v219
 = var19 (vs19 (vs19 vz19))

v319 : ∀{Γ A B C D} → Tm19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) A;v319
 = var19 (vs19 (vs19 (vs19 vz19)))

v419 : ∀{Γ A B C D E} → Tm19 (snoc19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) E) A;v419
 = var19 (vs19 (vs19 (vs19 (vs19 vz19))))

test19 : ∀{Γ A} → Tm19 Γ (arr19 (arr19 A A) (arr19 A A));test19
  = lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019)))))))
{-# OPTIONS --type-in-type #-}

Ty20 : Set; Ty20
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι20   : Ty20; ι20 = λ _ ι20 _ → ι20
arr20 : Ty20 → Ty20 → Ty20; arr20 = λ A B Ty20 ι20 arr20 → arr20 (A Ty20 ι20 arr20) (B Ty20 ι20 arr20)

Con20 : Set;Con20
 = (Con20 : Set)
   (nil  : Con20)
   (snoc : Con20 → Ty20 → Con20)
 → Con20

nil20 : Con20;nil20
 = λ Con20 nil20 snoc → nil20

snoc20 : Con20 → Ty20 → Con20;snoc20
 = λ Γ A Con20 nil20 snoc20 → snoc20 (Γ Con20 nil20 snoc20) A

Var20 : Con20 → Ty20 → Set;Var20
 = λ Γ A →
   (Var20 : Con20 → Ty20 → Set)
   (vz  : (Γ : _)(A : _) → Var20 (snoc20 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var20 Γ A → Var20 (snoc20 Γ B) A)
 → Var20 Γ A

vz20 : ∀{Γ A} → Var20 (snoc20 Γ A) A;vz20
 = λ Var20 vz20 vs → vz20 _ _

vs20 : ∀{Γ B A} → Var20 Γ A → Var20 (snoc20 Γ B) A;vs20
 = λ x Var20 vz20 vs20 → vs20 _ _ _ (x Var20 vz20 vs20)

Tm20 : Con20 → Ty20 → Set;Tm20
 = λ Γ A →
   (Tm20    : Con20 → Ty20 → Set)
   (var   : (Γ : _) (A : _) → Var20 Γ A → Tm20 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B))
   (app   : (Γ : _) (A B : _) → Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B)
 → Tm20 Γ A

var20 : ∀{Γ A} → Var20 Γ A → Tm20 Γ A;var20
 = λ x Tm20 var20 lam app → var20 _ _ x

lam20 : ∀{Γ A B} → Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B);lam20
 = λ t Tm20 var20 lam20 app → lam20 _ _ _ (t Tm20 var20 lam20 app)

app20 : ∀{Γ A B} → Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B;app20
 = λ t u Tm20 var20 lam20 app20 →
     app20 _ _ _ (t Tm20 var20 lam20 app20) (u Tm20 var20 lam20 app20)

v020 : ∀{Γ A} → Tm20 (snoc20 Γ A) A;v020
 = var20 vz20

v120 : ∀{Γ A B} → Tm20 (snoc20 (snoc20 Γ A) B) A;v120
 = var20 (vs20 vz20)

v220 : ∀{Γ A B C} → Tm20 (snoc20 (snoc20 (snoc20 Γ A) B) C) A;v220
 = var20 (vs20 (vs20 vz20))

v320 : ∀{Γ A B C D} → Tm20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) A;v320
 = var20 (vs20 (vs20 (vs20 vz20)))

v420 : ∀{Γ A B C D E} → Tm20 (snoc20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) E) A;v420
 = var20 (vs20 (vs20 (vs20 (vs20 vz20))))

test20 : ∀{Γ A} → Tm20 Γ (arr20 (arr20 A A) (arr20 A A));test20
  = lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020)))))))
{-# OPTIONS --type-in-type #-}

Ty21 : Set; Ty21
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι21   : Ty21; ι21 = λ _ ι21 _ → ι21
arr21 : Ty21 → Ty21 → Ty21; arr21 = λ A B Ty21 ι21 arr21 → arr21 (A Ty21 ι21 arr21) (B Ty21 ι21 arr21)

Con21 : Set;Con21
 = (Con21 : Set)
   (nil  : Con21)
   (snoc : Con21 → Ty21 → Con21)
 → Con21

nil21 : Con21;nil21
 = λ Con21 nil21 snoc → nil21

snoc21 : Con21 → Ty21 → Con21;snoc21
 = λ Γ A Con21 nil21 snoc21 → snoc21 (Γ Con21 nil21 snoc21) A

Var21 : Con21 → Ty21 → Set;Var21
 = λ Γ A →
   (Var21 : Con21 → Ty21 → Set)
   (vz  : (Γ : _)(A : _) → Var21 (snoc21 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var21 Γ A → Var21 (snoc21 Γ B) A)
 → Var21 Γ A

vz21 : ∀{Γ A} → Var21 (snoc21 Γ A) A;vz21
 = λ Var21 vz21 vs → vz21 _ _

vs21 : ∀{Γ B A} → Var21 Γ A → Var21 (snoc21 Γ B) A;vs21
 = λ x Var21 vz21 vs21 → vs21 _ _ _ (x Var21 vz21 vs21)

Tm21 : Con21 → Ty21 → Set;Tm21
 = λ Γ A →
   (Tm21    : Con21 → Ty21 → Set)
   (var   : (Γ : _) (A : _) → Var21 Γ A → Tm21 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B))
   (app   : (Γ : _) (A B : _) → Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B)
 → Tm21 Γ A

var21 : ∀{Γ A} → Var21 Γ A → Tm21 Γ A;var21
 = λ x Tm21 var21 lam app → var21 _ _ x

lam21 : ∀{Γ A B} → Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B);lam21
 = λ t Tm21 var21 lam21 app → lam21 _ _ _ (t Tm21 var21 lam21 app)

app21 : ∀{Γ A B} → Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B;app21
 = λ t u Tm21 var21 lam21 app21 →
     app21 _ _ _ (t Tm21 var21 lam21 app21) (u Tm21 var21 lam21 app21)

v021 : ∀{Γ A} → Tm21 (snoc21 Γ A) A;v021
 = var21 vz21

v121 : ∀{Γ A B} → Tm21 (snoc21 (snoc21 Γ A) B) A;v121
 = var21 (vs21 vz21)

v221 : ∀{Γ A B C} → Tm21 (snoc21 (snoc21 (snoc21 Γ A) B) C) A;v221
 = var21 (vs21 (vs21 vz21))

v321 : ∀{Γ A B C D} → Tm21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) A;v321
 = var21 (vs21 (vs21 (vs21 vz21)))

v421 : ∀{Γ A B C D E} → Tm21 (snoc21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) E) A;v421
 = var21 (vs21 (vs21 (vs21 (vs21 vz21))))

test21 : ∀{Γ A} → Tm21 Γ (arr21 (arr21 A A) (arr21 A A));test21
  = lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021)))))))
{-# OPTIONS --type-in-type #-}

Ty22 : Set; Ty22
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι22   : Ty22; ι22 = λ _ ι22 _ → ι22
arr22 : Ty22 → Ty22 → Ty22; arr22 = λ A B Ty22 ι22 arr22 → arr22 (A Ty22 ι22 arr22) (B Ty22 ι22 arr22)

Con22 : Set;Con22
 = (Con22 : Set)
   (nil  : Con22)
   (snoc : Con22 → Ty22 → Con22)
 → Con22

nil22 : Con22;nil22
 = λ Con22 nil22 snoc → nil22

snoc22 : Con22 → Ty22 → Con22;snoc22
 = λ Γ A Con22 nil22 snoc22 → snoc22 (Γ Con22 nil22 snoc22) A

Var22 : Con22 → Ty22 → Set;Var22
 = λ Γ A →
   (Var22 : Con22 → Ty22 → Set)
   (vz  : (Γ : _)(A : _) → Var22 (snoc22 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var22 Γ A → Var22 (snoc22 Γ B) A)
 → Var22 Γ A

vz22 : ∀{Γ A} → Var22 (snoc22 Γ A) A;vz22
 = λ Var22 vz22 vs → vz22 _ _

vs22 : ∀{Γ B A} → Var22 Γ A → Var22 (snoc22 Γ B) A;vs22
 = λ x Var22 vz22 vs22 → vs22 _ _ _ (x Var22 vz22 vs22)

Tm22 : Con22 → Ty22 → Set;Tm22
 = λ Γ A →
   (Tm22    : Con22 → Ty22 → Set)
   (var   : (Γ : _) (A : _) → Var22 Γ A → Tm22 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B))
   (app   : (Γ : _) (A B : _) → Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B)
 → Tm22 Γ A

var22 : ∀{Γ A} → Var22 Γ A → Tm22 Γ A;var22
 = λ x Tm22 var22 lam app → var22 _ _ x

lam22 : ∀{Γ A B} → Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B);lam22
 = λ t Tm22 var22 lam22 app → lam22 _ _ _ (t Tm22 var22 lam22 app)

app22 : ∀{Γ A B} → Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B;app22
 = λ t u Tm22 var22 lam22 app22 →
     app22 _ _ _ (t Tm22 var22 lam22 app22) (u Tm22 var22 lam22 app22)

v022 : ∀{Γ A} → Tm22 (snoc22 Γ A) A;v022
 = var22 vz22

v122 : ∀{Γ A B} → Tm22 (snoc22 (snoc22 Γ A) B) A;v122
 = var22 (vs22 vz22)

v222 : ∀{Γ A B C} → Tm22 (snoc22 (snoc22 (snoc22 Γ A) B) C) A;v222
 = var22 (vs22 (vs22 vz22))

v322 : ∀{Γ A B C D} → Tm22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) A;v322
 = var22 (vs22 (vs22 (vs22 vz22)))

v422 : ∀{Γ A B C D E} → Tm22 (snoc22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) E) A;v422
 = var22 (vs22 (vs22 (vs22 (vs22 vz22))))

test22 : ∀{Γ A} → Tm22 Γ (arr22 (arr22 A A) (arr22 A A));test22
  = lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022)))))))
{-# OPTIONS --type-in-type #-}

Ty23 : Set; Ty23
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι23   : Ty23; ι23 = λ _ ι23 _ → ι23
arr23 : Ty23 → Ty23 → Ty23; arr23 = λ A B Ty23 ι23 arr23 → arr23 (A Ty23 ι23 arr23) (B Ty23 ι23 arr23)

Con23 : Set;Con23
 = (Con23 : Set)
   (nil  : Con23)
   (snoc : Con23 → Ty23 → Con23)
 → Con23

nil23 : Con23;nil23
 = λ Con23 nil23 snoc → nil23

snoc23 : Con23 → Ty23 → Con23;snoc23
 = λ Γ A Con23 nil23 snoc23 → snoc23 (Γ Con23 nil23 snoc23) A

Var23 : Con23 → Ty23 → Set;Var23
 = λ Γ A →
   (Var23 : Con23 → Ty23 → Set)
   (vz  : (Γ : _)(A : _) → Var23 (snoc23 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var23 Γ A → Var23 (snoc23 Γ B) A)
 → Var23 Γ A

vz23 : ∀{Γ A} → Var23 (snoc23 Γ A) A;vz23
 = λ Var23 vz23 vs → vz23 _ _

vs23 : ∀{Γ B A} → Var23 Γ A → Var23 (snoc23 Γ B) A;vs23
 = λ x Var23 vz23 vs23 → vs23 _ _ _ (x Var23 vz23 vs23)

Tm23 : Con23 → Ty23 → Set;Tm23
 = λ Γ A →
   (Tm23    : Con23 → Ty23 → Set)
   (var   : (Γ : _) (A : _) → Var23 Γ A → Tm23 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B))
   (app   : (Γ : _) (A B : _) → Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B)
 → Tm23 Γ A

var23 : ∀{Γ A} → Var23 Γ A → Tm23 Γ A;var23
 = λ x Tm23 var23 lam app → var23 _ _ x

lam23 : ∀{Γ A B} → Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B);lam23
 = λ t Tm23 var23 lam23 app → lam23 _ _ _ (t Tm23 var23 lam23 app)

app23 : ∀{Γ A B} → Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B;app23
 = λ t u Tm23 var23 lam23 app23 →
     app23 _ _ _ (t Tm23 var23 lam23 app23) (u Tm23 var23 lam23 app23)

v023 : ∀{Γ A} → Tm23 (snoc23 Γ A) A;v023
 = var23 vz23

v123 : ∀{Γ A B} → Tm23 (snoc23 (snoc23 Γ A) B) A;v123
 = var23 (vs23 vz23)

v223 : ∀{Γ A B C} → Tm23 (snoc23 (snoc23 (snoc23 Γ A) B) C) A;v223
 = var23 (vs23 (vs23 vz23))

v323 : ∀{Γ A B C D} → Tm23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) A;v323
 = var23 (vs23 (vs23 (vs23 vz23)))

v423 : ∀{Γ A B C D E} → Tm23 (snoc23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) E) A;v423
 = var23 (vs23 (vs23 (vs23 (vs23 vz23))))

test23 : ∀{Γ A} → Tm23 Γ (arr23 (arr23 A A) (arr23 A A));test23
  = lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023)))))))
{-# OPTIONS --type-in-type #-}

Ty24 : Set; Ty24
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι24   : Ty24; ι24 = λ _ ι24 _ → ι24
arr24 : Ty24 → Ty24 → Ty24; arr24 = λ A B Ty24 ι24 arr24 → arr24 (A Ty24 ι24 arr24) (B Ty24 ι24 arr24)

Con24 : Set;Con24
 = (Con24 : Set)
   (nil  : Con24)
   (snoc : Con24 → Ty24 → Con24)
 → Con24

nil24 : Con24;nil24
 = λ Con24 nil24 snoc → nil24

snoc24 : Con24 → Ty24 → Con24;snoc24
 = λ Γ A Con24 nil24 snoc24 → snoc24 (Γ Con24 nil24 snoc24) A

Var24 : Con24 → Ty24 → Set;Var24
 = λ Γ A →
   (Var24 : Con24 → Ty24 → Set)
   (vz  : (Γ : _)(A : _) → Var24 (snoc24 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var24 Γ A → Var24 (snoc24 Γ B) A)
 → Var24 Γ A

vz24 : ∀{Γ A} → Var24 (snoc24 Γ A) A;vz24
 = λ Var24 vz24 vs → vz24 _ _

vs24 : ∀{Γ B A} → Var24 Γ A → Var24 (snoc24 Γ B) A;vs24
 = λ x Var24 vz24 vs24 → vs24 _ _ _ (x Var24 vz24 vs24)

Tm24 : Con24 → Ty24 → Set;Tm24
 = λ Γ A →
   (Tm24    : Con24 → Ty24 → Set)
   (var   : (Γ : _) (A : _) → Var24 Γ A → Tm24 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B))
   (app   : (Γ : _) (A B : _) → Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B)
 → Tm24 Γ A

var24 : ∀{Γ A} → Var24 Γ A → Tm24 Γ A;var24
 = λ x Tm24 var24 lam app → var24 _ _ x

lam24 : ∀{Γ A B} → Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B);lam24
 = λ t Tm24 var24 lam24 app → lam24 _ _ _ (t Tm24 var24 lam24 app)

app24 : ∀{Γ A B} → Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B;app24
 = λ t u Tm24 var24 lam24 app24 →
     app24 _ _ _ (t Tm24 var24 lam24 app24) (u Tm24 var24 lam24 app24)

v024 : ∀{Γ A} → Tm24 (snoc24 Γ A) A;v024
 = var24 vz24

v124 : ∀{Γ A B} → Tm24 (snoc24 (snoc24 Γ A) B) A;v124
 = var24 (vs24 vz24)

v224 : ∀{Γ A B C} → Tm24 (snoc24 (snoc24 (snoc24 Γ A) B) C) A;v224
 = var24 (vs24 (vs24 vz24))

v324 : ∀{Γ A B C D} → Tm24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) A;v324
 = var24 (vs24 (vs24 (vs24 vz24)))

v424 : ∀{Γ A B C D E} → Tm24 (snoc24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) E) A;v424
 = var24 (vs24 (vs24 (vs24 (vs24 vz24))))

test24 : ∀{Γ A} → Tm24 Γ (arr24 (arr24 A A) (arr24 A A));test24
  = lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024)))))))
{-# OPTIONS --type-in-type #-}

Ty25 : Set; Ty25
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι25   : Ty25; ι25 = λ _ ι25 _ → ι25
arr25 : Ty25 → Ty25 → Ty25; arr25 = λ A B Ty25 ι25 arr25 → arr25 (A Ty25 ι25 arr25) (B Ty25 ι25 arr25)

Con25 : Set;Con25
 = (Con25 : Set)
   (nil  : Con25)
   (snoc : Con25 → Ty25 → Con25)
 → Con25

nil25 : Con25;nil25
 = λ Con25 nil25 snoc → nil25

snoc25 : Con25 → Ty25 → Con25;snoc25
 = λ Γ A Con25 nil25 snoc25 → snoc25 (Γ Con25 nil25 snoc25) A

Var25 : Con25 → Ty25 → Set;Var25
 = λ Γ A →
   (Var25 : Con25 → Ty25 → Set)
   (vz  : (Γ : _)(A : _) → Var25 (snoc25 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var25 Γ A → Var25 (snoc25 Γ B) A)
 → Var25 Γ A

vz25 : ∀{Γ A} → Var25 (snoc25 Γ A) A;vz25
 = λ Var25 vz25 vs → vz25 _ _

vs25 : ∀{Γ B A} → Var25 Γ A → Var25 (snoc25 Γ B) A;vs25
 = λ x Var25 vz25 vs25 → vs25 _ _ _ (x Var25 vz25 vs25)

Tm25 : Con25 → Ty25 → Set;Tm25
 = λ Γ A →
   (Tm25    : Con25 → Ty25 → Set)
   (var   : (Γ : _) (A : _) → Var25 Γ A → Tm25 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B))
   (app   : (Γ : _) (A B : _) → Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B)
 → Tm25 Γ A

var25 : ∀{Γ A} → Var25 Γ A → Tm25 Γ A;var25
 = λ x Tm25 var25 lam app → var25 _ _ x

lam25 : ∀{Γ A B} → Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B);lam25
 = λ t Tm25 var25 lam25 app → lam25 _ _ _ (t Tm25 var25 lam25 app)

app25 : ∀{Γ A B} → Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B;app25
 = λ t u Tm25 var25 lam25 app25 →
     app25 _ _ _ (t Tm25 var25 lam25 app25) (u Tm25 var25 lam25 app25)

v025 : ∀{Γ A} → Tm25 (snoc25 Γ A) A;v025
 = var25 vz25

v125 : ∀{Γ A B} → Tm25 (snoc25 (snoc25 Γ A) B) A;v125
 = var25 (vs25 vz25)

v225 : ∀{Γ A B C} → Tm25 (snoc25 (snoc25 (snoc25 Γ A) B) C) A;v225
 = var25 (vs25 (vs25 vz25))

v325 : ∀{Γ A B C D} → Tm25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) A;v325
 = var25 (vs25 (vs25 (vs25 vz25)))

v425 : ∀{Γ A B C D E} → Tm25 (snoc25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) E) A;v425
 = var25 (vs25 (vs25 (vs25 (vs25 vz25))))

test25 : ∀{Γ A} → Tm25 Γ (arr25 (arr25 A A) (arr25 A A));test25
  = lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025)))))))
{-# OPTIONS --type-in-type #-}

Ty26 : Set; Ty26
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι26   : Ty26; ι26 = λ _ ι26 _ → ι26
arr26 : Ty26 → Ty26 → Ty26; arr26 = λ A B Ty26 ι26 arr26 → arr26 (A Ty26 ι26 arr26) (B Ty26 ι26 arr26)

Con26 : Set;Con26
 = (Con26 : Set)
   (nil  : Con26)
   (snoc : Con26 → Ty26 → Con26)
 → Con26

nil26 : Con26;nil26
 = λ Con26 nil26 snoc → nil26

snoc26 : Con26 → Ty26 → Con26;snoc26
 = λ Γ A Con26 nil26 snoc26 → snoc26 (Γ Con26 nil26 snoc26) A

Var26 : Con26 → Ty26 → Set;Var26
 = λ Γ A →
   (Var26 : Con26 → Ty26 → Set)
   (vz  : (Γ : _)(A : _) → Var26 (snoc26 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var26 Γ A → Var26 (snoc26 Γ B) A)
 → Var26 Γ A

vz26 : ∀{Γ A} → Var26 (snoc26 Γ A) A;vz26
 = λ Var26 vz26 vs → vz26 _ _

vs26 : ∀{Γ B A} → Var26 Γ A → Var26 (snoc26 Γ B) A;vs26
 = λ x Var26 vz26 vs26 → vs26 _ _ _ (x Var26 vz26 vs26)

Tm26 : Con26 → Ty26 → Set;Tm26
 = λ Γ A →
   (Tm26    : Con26 → Ty26 → Set)
   (var   : (Γ : _) (A : _) → Var26 Γ A → Tm26 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B))
   (app   : (Γ : _) (A B : _) → Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B)
 → Tm26 Γ A

var26 : ∀{Γ A} → Var26 Γ A → Tm26 Γ A;var26
 = λ x Tm26 var26 lam app → var26 _ _ x

lam26 : ∀{Γ A B} → Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B);lam26
 = λ t Tm26 var26 lam26 app → lam26 _ _ _ (t Tm26 var26 lam26 app)

app26 : ∀{Γ A B} → Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B;app26
 = λ t u Tm26 var26 lam26 app26 →
     app26 _ _ _ (t Tm26 var26 lam26 app26) (u Tm26 var26 lam26 app26)

v026 : ∀{Γ A} → Tm26 (snoc26 Γ A) A;v026
 = var26 vz26

v126 : ∀{Γ A B} → Tm26 (snoc26 (snoc26 Γ A) B) A;v126
 = var26 (vs26 vz26)

v226 : ∀{Γ A B C} → Tm26 (snoc26 (snoc26 (snoc26 Γ A) B) C) A;v226
 = var26 (vs26 (vs26 vz26))

v326 : ∀{Γ A B C D} → Tm26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) A;v326
 = var26 (vs26 (vs26 (vs26 vz26)))

v426 : ∀{Γ A B C D E} → Tm26 (snoc26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) E) A;v426
 = var26 (vs26 (vs26 (vs26 (vs26 vz26))))

test26 : ∀{Γ A} → Tm26 Γ (arr26 (arr26 A A) (arr26 A A));test26
  = lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026)))))))
{-# OPTIONS --type-in-type #-}

Ty27 : Set; Ty27
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι27   : Ty27; ι27 = λ _ ι27 _ → ι27
arr27 : Ty27 → Ty27 → Ty27; arr27 = λ A B Ty27 ι27 arr27 → arr27 (A Ty27 ι27 arr27) (B Ty27 ι27 arr27)

Con27 : Set;Con27
 = (Con27 : Set)
   (nil  : Con27)
   (snoc : Con27 → Ty27 → Con27)
 → Con27

nil27 : Con27;nil27
 = λ Con27 nil27 snoc → nil27

snoc27 : Con27 → Ty27 → Con27;snoc27
 = λ Γ A Con27 nil27 snoc27 → snoc27 (Γ Con27 nil27 snoc27) A

Var27 : Con27 → Ty27 → Set;Var27
 = λ Γ A →
   (Var27 : Con27 → Ty27 → Set)
   (vz  : (Γ : _)(A : _) → Var27 (snoc27 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var27 Γ A → Var27 (snoc27 Γ B) A)
 → Var27 Γ A

vz27 : ∀{Γ A} → Var27 (snoc27 Γ A) A;vz27
 = λ Var27 vz27 vs → vz27 _ _

vs27 : ∀{Γ B A} → Var27 Γ A → Var27 (snoc27 Γ B) A;vs27
 = λ x Var27 vz27 vs27 → vs27 _ _ _ (x Var27 vz27 vs27)

Tm27 : Con27 → Ty27 → Set;Tm27
 = λ Γ A →
   (Tm27    : Con27 → Ty27 → Set)
   (var   : (Γ : _) (A : _) → Var27 Γ A → Tm27 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B))
   (app   : (Γ : _) (A B : _) → Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B)
 → Tm27 Γ A

var27 : ∀{Γ A} → Var27 Γ A → Tm27 Γ A;var27
 = λ x Tm27 var27 lam app → var27 _ _ x

lam27 : ∀{Γ A B} → Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B);lam27
 = λ t Tm27 var27 lam27 app → lam27 _ _ _ (t Tm27 var27 lam27 app)

app27 : ∀{Γ A B} → Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B;app27
 = λ t u Tm27 var27 lam27 app27 →
     app27 _ _ _ (t Tm27 var27 lam27 app27) (u Tm27 var27 lam27 app27)

v027 : ∀{Γ A} → Tm27 (snoc27 Γ A) A;v027
 = var27 vz27

v127 : ∀{Γ A B} → Tm27 (snoc27 (snoc27 Γ A) B) A;v127
 = var27 (vs27 vz27)

v227 : ∀{Γ A B C} → Tm27 (snoc27 (snoc27 (snoc27 Γ A) B) C) A;v227
 = var27 (vs27 (vs27 vz27))

v327 : ∀{Γ A B C D} → Tm27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) A;v327
 = var27 (vs27 (vs27 (vs27 vz27)))

v427 : ∀{Γ A B C D E} → Tm27 (snoc27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) E) A;v427
 = var27 (vs27 (vs27 (vs27 (vs27 vz27))))

test27 : ∀{Γ A} → Tm27 Γ (arr27 (arr27 A A) (arr27 A A));test27
  = lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027)))))))
{-# OPTIONS --type-in-type #-}

Ty28 : Set; Ty28
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι28   : Ty28; ι28 = λ _ ι28 _ → ι28
arr28 : Ty28 → Ty28 → Ty28; arr28 = λ A B Ty28 ι28 arr28 → arr28 (A Ty28 ι28 arr28) (B Ty28 ι28 arr28)

Con28 : Set;Con28
 = (Con28 : Set)
   (nil  : Con28)
   (snoc : Con28 → Ty28 → Con28)
 → Con28

nil28 : Con28;nil28
 = λ Con28 nil28 snoc → nil28

snoc28 : Con28 → Ty28 → Con28;snoc28
 = λ Γ A Con28 nil28 snoc28 → snoc28 (Γ Con28 nil28 snoc28) A

Var28 : Con28 → Ty28 → Set;Var28
 = λ Γ A →
   (Var28 : Con28 → Ty28 → Set)
   (vz  : (Γ : _)(A : _) → Var28 (snoc28 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var28 Γ A → Var28 (snoc28 Γ B) A)
 → Var28 Γ A

vz28 : ∀{Γ A} → Var28 (snoc28 Γ A) A;vz28
 = λ Var28 vz28 vs → vz28 _ _

vs28 : ∀{Γ B A} → Var28 Γ A → Var28 (snoc28 Γ B) A;vs28
 = λ x Var28 vz28 vs28 → vs28 _ _ _ (x Var28 vz28 vs28)

Tm28 : Con28 → Ty28 → Set;Tm28
 = λ Γ A →
   (Tm28    : Con28 → Ty28 → Set)
   (var   : (Γ : _) (A : _) → Var28 Γ A → Tm28 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B))
   (app   : (Γ : _) (A B : _) → Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B)
 → Tm28 Γ A

var28 : ∀{Γ A} → Var28 Γ A → Tm28 Γ A;var28
 = λ x Tm28 var28 lam app → var28 _ _ x

lam28 : ∀{Γ A B} → Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B);lam28
 = λ t Tm28 var28 lam28 app → lam28 _ _ _ (t Tm28 var28 lam28 app)

app28 : ∀{Γ A B} → Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B;app28
 = λ t u Tm28 var28 lam28 app28 →
     app28 _ _ _ (t Tm28 var28 lam28 app28) (u Tm28 var28 lam28 app28)

v028 : ∀{Γ A} → Tm28 (snoc28 Γ A) A;v028
 = var28 vz28

v128 : ∀{Γ A B} → Tm28 (snoc28 (snoc28 Γ A) B) A;v128
 = var28 (vs28 vz28)

v228 : ∀{Γ A B C} → Tm28 (snoc28 (snoc28 (snoc28 Γ A) B) C) A;v228
 = var28 (vs28 (vs28 vz28))

v328 : ∀{Γ A B C D} → Tm28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) A;v328
 = var28 (vs28 (vs28 (vs28 vz28)))

v428 : ∀{Γ A B C D E} → Tm28 (snoc28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) E) A;v428
 = var28 (vs28 (vs28 (vs28 (vs28 vz28))))

test28 : ∀{Γ A} → Tm28 Γ (arr28 (arr28 A A) (arr28 A A));test28
  = lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028)))))))
{-# OPTIONS --type-in-type #-}

Ty29 : Set; Ty29
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι29   : Ty29; ι29 = λ _ ι29 _ → ι29
arr29 : Ty29 → Ty29 → Ty29; arr29 = λ A B Ty29 ι29 arr29 → arr29 (A Ty29 ι29 arr29) (B Ty29 ι29 arr29)

Con29 : Set;Con29
 = (Con29 : Set)
   (nil  : Con29)
   (snoc : Con29 → Ty29 → Con29)
 → Con29

nil29 : Con29;nil29
 = λ Con29 nil29 snoc → nil29

snoc29 : Con29 → Ty29 → Con29;snoc29
 = λ Γ A Con29 nil29 snoc29 → snoc29 (Γ Con29 nil29 snoc29) A

Var29 : Con29 → Ty29 → Set;Var29
 = λ Γ A →
   (Var29 : Con29 → Ty29 → Set)
   (vz  : (Γ : _)(A : _) → Var29 (snoc29 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var29 Γ A → Var29 (snoc29 Γ B) A)
 → Var29 Γ A

vz29 : ∀{Γ A} → Var29 (snoc29 Γ A) A;vz29
 = λ Var29 vz29 vs → vz29 _ _

vs29 : ∀{Γ B A} → Var29 Γ A → Var29 (snoc29 Γ B) A;vs29
 = λ x Var29 vz29 vs29 → vs29 _ _ _ (x Var29 vz29 vs29)

Tm29 : Con29 → Ty29 → Set;Tm29
 = λ Γ A →
   (Tm29    : Con29 → Ty29 → Set)
   (var   : (Γ : _) (A : _) → Var29 Γ A → Tm29 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B))
   (app   : (Γ : _) (A B : _) → Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B)
 → Tm29 Γ A

var29 : ∀{Γ A} → Var29 Γ A → Tm29 Γ A;var29
 = λ x Tm29 var29 lam app → var29 _ _ x

lam29 : ∀{Γ A B} → Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B);lam29
 = λ t Tm29 var29 lam29 app → lam29 _ _ _ (t Tm29 var29 lam29 app)

app29 : ∀{Γ A B} → Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B;app29
 = λ t u Tm29 var29 lam29 app29 →
     app29 _ _ _ (t Tm29 var29 lam29 app29) (u Tm29 var29 lam29 app29)

v029 : ∀{Γ A} → Tm29 (snoc29 Γ A) A;v029
 = var29 vz29

v129 : ∀{Γ A B} → Tm29 (snoc29 (snoc29 Γ A) B) A;v129
 = var29 (vs29 vz29)

v229 : ∀{Γ A B C} → Tm29 (snoc29 (snoc29 (snoc29 Γ A) B) C) A;v229
 = var29 (vs29 (vs29 vz29))

v329 : ∀{Γ A B C D} → Tm29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) A;v329
 = var29 (vs29 (vs29 (vs29 vz29)))

v429 : ∀{Γ A B C D E} → Tm29 (snoc29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) E) A;v429
 = var29 (vs29 (vs29 (vs29 (vs29 vz29))))

test29 : ∀{Γ A} → Tm29 Γ (arr29 (arr29 A A) (arr29 A A));test29
  = lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029)))))))
{-# OPTIONS --type-in-type #-}

Ty30 : Set; Ty30
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι30   : Ty30; ι30 = λ _ ι30 _ → ι30
arr30 : Ty30 → Ty30 → Ty30; arr30 = λ A B Ty30 ι30 arr30 → arr30 (A Ty30 ι30 arr30) (B Ty30 ι30 arr30)

Con30 : Set;Con30
 = (Con30 : Set)
   (nil  : Con30)
   (snoc : Con30 → Ty30 → Con30)
 → Con30

nil30 : Con30;nil30
 = λ Con30 nil30 snoc → nil30

snoc30 : Con30 → Ty30 → Con30;snoc30
 = λ Γ A Con30 nil30 snoc30 → snoc30 (Γ Con30 nil30 snoc30) A

Var30 : Con30 → Ty30 → Set;Var30
 = λ Γ A →
   (Var30 : Con30 → Ty30 → Set)
   (vz  : (Γ : _)(A : _) → Var30 (snoc30 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var30 Γ A → Var30 (snoc30 Γ B) A)
 → Var30 Γ A

vz30 : ∀{Γ A} → Var30 (snoc30 Γ A) A;vz30
 = λ Var30 vz30 vs → vz30 _ _

vs30 : ∀{Γ B A} → Var30 Γ A → Var30 (snoc30 Γ B) A;vs30
 = λ x Var30 vz30 vs30 → vs30 _ _ _ (x Var30 vz30 vs30)

Tm30 : Con30 → Ty30 → Set;Tm30
 = λ Γ A →
   (Tm30    : Con30 → Ty30 → Set)
   (var   : (Γ : _) (A : _) → Var30 Γ A → Tm30 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B))
   (app   : (Γ : _) (A B : _) → Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B)
 → Tm30 Γ A

var30 : ∀{Γ A} → Var30 Γ A → Tm30 Γ A;var30
 = λ x Tm30 var30 lam app → var30 _ _ x

lam30 : ∀{Γ A B} → Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B);lam30
 = λ t Tm30 var30 lam30 app → lam30 _ _ _ (t Tm30 var30 lam30 app)

app30 : ∀{Γ A B} → Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B;app30
 = λ t u Tm30 var30 lam30 app30 →
     app30 _ _ _ (t Tm30 var30 lam30 app30) (u Tm30 var30 lam30 app30)

v030 : ∀{Γ A} → Tm30 (snoc30 Γ A) A;v030
 = var30 vz30

v130 : ∀{Γ A B} → Tm30 (snoc30 (snoc30 Γ A) B) A;v130
 = var30 (vs30 vz30)

v230 : ∀{Γ A B C} → Tm30 (snoc30 (snoc30 (snoc30 Γ A) B) C) A;v230
 = var30 (vs30 (vs30 vz30))

v330 : ∀{Γ A B C D} → Tm30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) A;v330
 = var30 (vs30 (vs30 (vs30 vz30)))

v430 : ∀{Γ A B C D E} → Tm30 (snoc30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) E) A;v430
 = var30 (vs30 (vs30 (vs30 (vs30 vz30))))

test30 : ∀{Γ A} → Tm30 Γ (arr30 (arr30 A A) (arr30 A A));test30
  = lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030)))))))
{-# OPTIONS --type-in-type #-}

Ty31 : Set; Ty31
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι31   : Ty31; ι31 = λ _ ι31 _ → ι31
arr31 : Ty31 → Ty31 → Ty31; arr31 = λ A B Ty31 ι31 arr31 → arr31 (A Ty31 ι31 arr31) (B Ty31 ι31 arr31)

Con31 : Set;Con31
 = (Con31 : Set)
   (nil  : Con31)
   (snoc : Con31 → Ty31 → Con31)
 → Con31

nil31 : Con31;nil31
 = λ Con31 nil31 snoc → nil31

snoc31 : Con31 → Ty31 → Con31;snoc31
 = λ Γ A Con31 nil31 snoc31 → snoc31 (Γ Con31 nil31 snoc31) A

Var31 : Con31 → Ty31 → Set;Var31
 = λ Γ A →
   (Var31 : Con31 → Ty31 → Set)
   (vz  : (Γ : _)(A : _) → Var31 (snoc31 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var31 Γ A → Var31 (snoc31 Γ B) A)
 → Var31 Γ A

vz31 : ∀{Γ A} → Var31 (snoc31 Γ A) A;vz31
 = λ Var31 vz31 vs → vz31 _ _

vs31 : ∀{Γ B A} → Var31 Γ A → Var31 (snoc31 Γ B) A;vs31
 = λ x Var31 vz31 vs31 → vs31 _ _ _ (x Var31 vz31 vs31)

Tm31 : Con31 → Ty31 → Set;Tm31
 = λ Γ A →
   (Tm31    : Con31 → Ty31 → Set)
   (var   : (Γ : _) (A : _) → Var31 Γ A → Tm31 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B))
   (app   : (Γ : _) (A B : _) → Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B)
 → Tm31 Γ A

var31 : ∀{Γ A} → Var31 Γ A → Tm31 Γ A;var31
 = λ x Tm31 var31 lam app → var31 _ _ x

lam31 : ∀{Γ A B} → Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B);lam31
 = λ t Tm31 var31 lam31 app → lam31 _ _ _ (t Tm31 var31 lam31 app)

app31 : ∀{Γ A B} → Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B;app31
 = λ t u Tm31 var31 lam31 app31 →
     app31 _ _ _ (t Tm31 var31 lam31 app31) (u Tm31 var31 lam31 app31)

v031 : ∀{Γ A} → Tm31 (snoc31 Γ A) A;v031
 = var31 vz31

v131 : ∀{Γ A B} → Tm31 (snoc31 (snoc31 Γ A) B) A;v131
 = var31 (vs31 vz31)

v231 : ∀{Γ A B C} → Tm31 (snoc31 (snoc31 (snoc31 Γ A) B) C) A;v231
 = var31 (vs31 (vs31 vz31))

v331 : ∀{Γ A B C D} → Tm31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) A;v331
 = var31 (vs31 (vs31 (vs31 vz31)))

v431 : ∀{Γ A B C D E} → Tm31 (snoc31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) E) A;v431
 = var31 (vs31 (vs31 (vs31 (vs31 vz31))))

test31 : ∀{Γ A} → Tm31 Γ (arr31 (arr31 A A) (arr31 A A));test31
  = lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031)))))))
{-# OPTIONS --type-in-type #-}

Ty32 : Set; Ty32
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι32   : Ty32; ι32 = λ _ ι32 _ → ι32
arr32 : Ty32 → Ty32 → Ty32; arr32 = λ A B Ty32 ι32 arr32 → arr32 (A Ty32 ι32 arr32) (B Ty32 ι32 arr32)

Con32 : Set;Con32
 = (Con32 : Set)
   (nil  : Con32)
   (snoc : Con32 → Ty32 → Con32)
 → Con32

nil32 : Con32;nil32
 = λ Con32 nil32 snoc → nil32

snoc32 : Con32 → Ty32 → Con32;snoc32
 = λ Γ A Con32 nil32 snoc32 → snoc32 (Γ Con32 nil32 snoc32) A

Var32 : Con32 → Ty32 → Set;Var32
 = λ Γ A →
   (Var32 : Con32 → Ty32 → Set)
   (vz  : (Γ : _)(A : _) → Var32 (snoc32 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var32 Γ A → Var32 (snoc32 Γ B) A)
 → Var32 Γ A

vz32 : ∀{Γ A} → Var32 (snoc32 Γ A) A;vz32
 = λ Var32 vz32 vs → vz32 _ _

vs32 : ∀{Γ B A} → Var32 Γ A → Var32 (snoc32 Γ B) A;vs32
 = λ x Var32 vz32 vs32 → vs32 _ _ _ (x Var32 vz32 vs32)

Tm32 : Con32 → Ty32 → Set;Tm32
 = λ Γ A →
   (Tm32    : Con32 → Ty32 → Set)
   (var   : (Γ : _) (A : _) → Var32 Γ A → Tm32 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B))
   (app   : (Γ : _) (A B : _) → Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B)
 → Tm32 Γ A

var32 : ∀{Γ A} → Var32 Γ A → Tm32 Γ A;var32
 = λ x Tm32 var32 lam app → var32 _ _ x

lam32 : ∀{Γ A B} → Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B);lam32
 = λ t Tm32 var32 lam32 app → lam32 _ _ _ (t Tm32 var32 lam32 app)

app32 : ∀{Γ A B} → Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B;app32
 = λ t u Tm32 var32 lam32 app32 →
     app32 _ _ _ (t Tm32 var32 lam32 app32) (u Tm32 var32 lam32 app32)

v032 : ∀{Γ A} → Tm32 (snoc32 Γ A) A;v032
 = var32 vz32

v132 : ∀{Γ A B} → Tm32 (snoc32 (snoc32 Γ A) B) A;v132
 = var32 (vs32 vz32)

v232 : ∀{Γ A B C} → Tm32 (snoc32 (snoc32 (snoc32 Γ A) B) C) A;v232
 = var32 (vs32 (vs32 vz32))

v332 : ∀{Γ A B C D} → Tm32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) A;v332
 = var32 (vs32 (vs32 (vs32 vz32)))

v432 : ∀{Γ A B C D E} → Tm32 (snoc32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) E) A;v432
 = var32 (vs32 (vs32 (vs32 (vs32 vz32))))

test32 : ∀{Γ A} → Tm32 Γ (arr32 (arr32 A A) (arr32 A A));test32
  = lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032)))))))
{-# OPTIONS --type-in-type #-}

Ty33 : Set; Ty33
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι33   : Ty33; ι33 = λ _ ι33 _ → ι33
arr33 : Ty33 → Ty33 → Ty33; arr33 = λ A B Ty33 ι33 arr33 → arr33 (A Ty33 ι33 arr33) (B Ty33 ι33 arr33)

Con33 : Set;Con33
 = (Con33 : Set)
   (nil  : Con33)
   (snoc : Con33 → Ty33 → Con33)
 → Con33

nil33 : Con33;nil33
 = λ Con33 nil33 snoc → nil33

snoc33 : Con33 → Ty33 → Con33;snoc33
 = λ Γ A Con33 nil33 snoc33 → snoc33 (Γ Con33 nil33 snoc33) A

Var33 : Con33 → Ty33 → Set;Var33
 = λ Γ A →
   (Var33 : Con33 → Ty33 → Set)
   (vz  : (Γ : _)(A : _) → Var33 (snoc33 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var33 Γ A → Var33 (snoc33 Γ B) A)
 → Var33 Γ A

vz33 : ∀{Γ A} → Var33 (snoc33 Γ A) A;vz33
 = λ Var33 vz33 vs → vz33 _ _

vs33 : ∀{Γ B A} → Var33 Γ A → Var33 (snoc33 Γ B) A;vs33
 = λ x Var33 vz33 vs33 → vs33 _ _ _ (x Var33 vz33 vs33)

Tm33 : Con33 → Ty33 → Set;Tm33
 = λ Γ A →
   (Tm33    : Con33 → Ty33 → Set)
   (var   : (Γ : _) (A : _) → Var33 Γ A → Tm33 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B))
   (app   : (Γ : _) (A B : _) → Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B)
 → Tm33 Γ A

var33 : ∀{Γ A} → Var33 Γ A → Tm33 Γ A;var33
 = λ x Tm33 var33 lam app → var33 _ _ x

lam33 : ∀{Γ A B} → Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B);lam33
 = λ t Tm33 var33 lam33 app → lam33 _ _ _ (t Tm33 var33 lam33 app)

app33 : ∀{Γ A B} → Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B;app33
 = λ t u Tm33 var33 lam33 app33 →
     app33 _ _ _ (t Tm33 var33 lam33 app33) (u Tm33 var33 lam33 app33)

v033 : ∀{Γ A} → Tm33 (snoc33 Γ A) A;v033
 = var33 vz33

v133 : ∀{Γ A B} → Tm33 (snoc33 (snoc33 Γ A) B) A;v133
 = var33 (vs33 vz33)

v233 : ∀{Γ A B C} → Tm33 (snoc33 (snoc33 (snoc33 Γ A) B) C) A;v233
 = var33 (vs33 (vs33 vz33))

v333 : ∀{Γ A B C D} → Tm33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) A;v333
 = var33 (vs33 (vs33 (vs33 vz33)))

v433 : ∀{Γ A B C D E} → Tm33 (snoc33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) E) A;v433
 = var33 (vs33 (vs33 (vs33 (vs33 vz33))))

test33 : ∀{Γ A} → Tm33 Γ (arr33 (arr33 A A) (arr33 A A));test33
  = lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033)))))))
{-# OPTIONS --type-in-type #-}

Ty34 : Set; Ty34
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι34   : Ty34; ι34 = λ _ ι34 _ → ι34
arr34 : Ty34 → Ty34 → Ty34; arr34 = λ A B Ty34 ι34 arr34 → arr34 (A Ty34 ι34 arr34) (B Ty34 ι34 arr34)

Con34 : Set;Con34
 = (Con34 : Set)
   (nil  : Con34)
   (snoc : Con34 → Ty34 → Con34)
 → Con34

nil34 : Con34;nil34
 = λ Con34 nil34 snoc → nil34

snoc34 : Con34 → Ty34 → Con34;snoc34
 = λ Γ A Con34 nil34 snoc34 → snoc34 (Γ Con34 nil34 snoc34) A

Var34 : Con34 → Ty34 → Set;Var34
 = λ Γ A →
   (Var34 : Con34 → Ty34 → Set)
   (vz  : (Γ : _)(A : _) → Var34 (snoc34 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var34 Γ A → Var34 (snoc34 Γ B) A)
 → Var34 Γ A

vz34 : ∀{Γ A} → Var34 (snoc34 Γ A) A;vz34
 = λ Var34 vz34 vs → vz34 _ _

vs34 : ∀{Γ B A} → Var34 Γ A → Var34 (snoc34 Γ B) A;vs34
 = λ x Var34 vz34 vs34 → vs34 _ _ _ (x Var34 vz34 vs34)

Tm34 : Con34 → Ty34 → Set;Tm34
 = λ Γ A →
   (Tm34    : Con34 → Ty34 → Set)
   (var   : (Γ : _) (A : _) → Var34 Γ A → Tm34 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B))
   (app   : (Γ : _) (A B : _) → Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B)
 → Tm34 Γ A

var34 : ∀{Γ A} → Var34 Γ A → Tm34 Γ A;var34
 = λ x Tm34 var34 lam app → var34 _ _ x

lam34 : ∀{Γ A B} → Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B);lam34
 = λ t Tm34 var34 lam34 app → lam34 _ _ _ (t Tm34 var34 lam34 app)

app34 : ∀{Γ A B} → Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B;app34
 = λ t u Tm34 var34 lam34 app34 →
     app34 _ _ _ (t Tm34 var34 lam34 app34) (u Tm34 var34 lam34 app34)

v034 : ∀{Γ A} → Tm34 (snoc34 Γ A) A;v034
 = var34 vz34

v134 : ∀{Γ A B} → Tm34 (snoc34 (snoc34 Γ A) B) A;v134
 = var34 (vs34 vz34)

v234 : ∀{Γ A B C} → Tm34 (snoc34 (snoc34 (snoc34 Γ A) B) C) A;v234
 = var34 (vs34 (vs34 vz34))

v334 : ∀{Γ A B C D} → Tm34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) A;v334
 = var34 (vs34 (vs34 (vs34 vz34)))

v434 : ∀{Γ A B C D E} → Tm34 (snoc34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) E) A;v434
 = var34 (vs34 (vs34 (vs34 (vs34 vz34))))

test34 : ∀{Γ A} → Tm34 Γ (arr34 (arr34 A A) (arr34 A A));test34
  = lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034)))))))
{-# OPTIONS --type-in-type #-}

Ty35 : Set; Ty35
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι35   : Ty35; ι35 = λ _ ι35 _ → ι35
arr35 : Ty35 → Ty35 → Ty35; arr35 = λ A B Ty35 ι35 arr35 → arr35 (A Ty35 ι35 arr35) (B Ty35 ι35 arr35)

Con35 : Set;Con35
 = (Con35 : Set)
   (nil  : Con35)
   (snoc : Con35 → Ty35 → Con35)
 → Con35

nil35 : Con35;nil35
 = λ Con35 nil35 snoc → nil35

snoc35 : Con35 → Ty35 → Con35;snoc35
 = λ Γ A Con35 nil35 snoc35 → snoc35 (Γ Con35 nil35 snoc35) A

Var35 : Con35 → Ty35 → Set;Var35
 = λ Γ A →
   (Var35 : Con35 → Ty35 → Set)
   (vz  : (Γ : _)(A : _) → Var35 (snoc35 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var35 Γ A → Var35 (snoc35 Γ B) A)
 → Var35 Γ A

vz35 : ∀{Γ A} → Var35 (snoc35 Γ A) A;vz35
 = λ Var35 vz35 vs → vz35 _ _

vs35 : ∀{Γ B A} → Var35 Γ A → Var35 (snoc35 Γ B) A;vs35
 = λ x Var35 vz35 vs35 → vs35 _ _ _ (x Var35 vz35 vs35)

Tm35 : Con35 → Ty35 → Set;Tm35
 = λ Γ A →
   (Tm35    : Con35 → Ty35 → Set)
   (var   : (Γ : _) (A : _) → Var35 Γ A → Tm35 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B))
   (app   : (Γ : _) (A B : _) → Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B)
 → Tm35 Γ A

var35 : ∀{Γ A} → Var35 Γ A → Tm35 Γ A;var35
 = λ x Tm35 var35 lam app → var35 _ _ x

lam35 : ∀{Γ A B} → Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B);lam35
 = λ t Tm35 var35 lam35 app → lam35 _ _ _ (t Tm35 var35 lam35 app)

app35 : ∀{Γ A B} → Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B;app35
 = λ t u Tm35 var35 lam35 app35 →
     app35 _ _ _ (t Tm35 var35 lam35 app35) (u Tm35 var35 lam35 app35)

v035 : ∀{Γ A} → Tm35 (snoc35 Γ A) A;v035
 = var35 vz35

v135 : ∀{Γ A B} → Tm35 (snoc35 (snoc35 Γ A) B) A;v135
 = var35 (vs35 vz35)

v235 : ∀{Γ A B C} → Tm35 (snoc35 (snoc35 (snoc35 Γ A) B) C) A;v235
 = var35 (vs35 (vs35 vz35))

v335 : ∀{Γ A B C D} → Tm35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) A;v335
 = var35 (vs35 (vs35 (vs35 vz35)))

v435 : ∀{Γ A B C D E} → Tm35 (snoc35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) E) A;v435
 = var35 (vs35 (vs35 (vs35 (vs35 vz35))))

test35 : ∀{Γ A} → Tm35 Γ (arr35 (arr35 A A) (arr35 A A));test35
  = lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035)))))))
{-# OPTIONS --type-in-type #-}

Ty36 : Set; Ty36
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι36   : Ty36; ι36 = λ _ ι36 _ → ι36
arr36 : Ty36 → Ty36 → Ty36; arr36 = λ A B Ty36 ι36 arr36 → arr36 (A Ty36 ι36 arr36) (B Ty36 ι36 arr36)

Con36 : Set;Con36
 = (Con36 : Set)
   (nil  : Con36)
   (snoc : Con36 → Ty36 → Con36)
 → Con36

nil36 : Con36;nil36
 = λ Con36 nil36 snoc → nil36

snoc36 : Con36 → Ty36 → Con36;snoc36
 = λ Γ A Con36 nil36 snoc36 → snoc36 (Γ Con36 nil36 snoc36) A

Var36 : Con36 → Ty36 → Set;Var36
 = λ Γ A →
   (Var36 : Con36 → Ty36 → Set)
   (vz  : (Γ : _)(A : _) → Var36 (snoc36 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var36 Γ A → Var36 (snoc36 Γ B) A)
 → Var36 Γ A

vz36 : ∀{Γ A} → Var36 (snoc36 Γ A) A;vz36
 = λ Var36 vz36 vs → vz36 _ _

vs36 : ∀{Γ B A} → Var36 Γ A → Var36 (snoc36 Γ B) A;vs36
 = λ x Var36 vz36 vs36 → vs36 _ _ _ (x Var36 vz36 vs36)

Tm36 : Con36 → Ty36 → Set;Tm36
 = λ Γ A →
   (Tm36    : Con36 → Ty36 → Set)
   (var   : (Γ : _) (A : _) → Var36 Γ A → Tm36 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B))
   (app   : (Γ : _) (A B : _) → Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B)
 → Tm36 Γ A

var36 : ∀{Γ A} → Var36 Γ A → Tm36 Γ A;var36
 = λ x Tm36 var36 lam app → var36 _ _ x

lam36 : ∀{Γ A B} → Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B);lam36
 = λ t Tm36 var36 lam36 app → lam36 _ _ _ (t Tm36 var36 lam36 app)

app36 : ∀{Γ A B} → Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B;app36
 = λ t u Tm36 var36 lam36 app36 →
     app36 _ _ _ (t Tm36 var36 lam36 app36) (u Tm36 var36 lam36 app36)

v036 : ∀{Γ A} → Tm36 (snoc36 Γ A) A;v036
 = var36 vz36

v136 : ∀{Γ A B} → Tm36 (snoc36 (snoc36 Γ A) B) A;v136
 = var36 (vs36 vz36)

v236 : ∀{Γ A B C} → Tm36 (snoc36 (snoc36 (snoc36 Γ A) B) C) A;v236
 = var36 (vs36 (vs36 vz36))

v336 : ∀{Γ A B C D} → Tm36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) A;v336
 = var36 (vs36 (vs36 (vs36 vz36)))

v436 : ∀{Γ A B C D E} → Tm36 (snoc36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) E) A;v436
 = var36 (vs36 (vs36 (vs36 (vs36 vz36))))

test36 : ∀{Γ A} → Tm36 Γ (arr36 (arr36 A A) (arr36 A A));test36
  = lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036)))))))
{-# OPTIONS --type-in-type #-}

Ty37 : Set; Ty37
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι37   : Ty37; ι37 = λ _ ι37 _ → ι37
arr37 : Ty37 → Ty37 → Ty37; arr37 = λ A B Ty37 ι37 arr37 → arr37 (A Ty37 ι37 arr37) (B Ty37 ι37 arr37)

Con37 : Set;Con37
 = (Con37 : Set)
   (nil  : Con37)
   (snoc : Con37 → Ty37 → Con37)
 → Con37

nil37 : Con37;nil37
 = λ Con37 nil37 snoc → nil37

snoc37 : Con37 → Ty37 → Con37;snoc37
 = λ Γ A Con37 nil37 snoc37 → snoc37 (Γ Con37 nil37 snoc37) A

Var37 : Con37 → Ty37 → Set;Var37
 = λ Γ A →
   (Var37 : Con37 → Ty37 → Set)
   (vz  : (Γ : _)(A : _) → Var37 (snoc37 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var37 Γ A → Var37 (snoc37 Γ B) A)
 → Var37 Γ A

vz37 : ∀{Γ A} → Var37 (snoc37 Γ A) A;vz37
 = λ Var37 vz37 vs → vz37 _ _

vs37 : ∀{Γ B A} → Var37 Γ A → Var37 (snoc37 Γ B) A;vs37
 = λ x Var37 vz37 vs37 → vs37 _ _ _ (x Var37 vz37 vs37)

Tm37 : Con37 → Ty37 → Set;Tm37
 = λ Γ A →
   (Tm37    : Con37 → Ty37 → Set)
   (var   : (Γ : _) (A : _) → Var37 Γ A → Tm37 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B))
   (app   : (Γ : _) (A B : _) → Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B)
 → Tm37 Γ A

var37 : ∀{Γ A} → Var37 Γ A → Tm37 Γ A;var37
 = λ x Tm37 var37 lam app → var37 _ _ x

lam37 : ∀{Γ A B} → Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B);lam37
 = λ t Tm37 var37 lam37 app → lam37 _ _ _ (t Tm37 var37 lam37 app)

app37 : ∀{Γ A B} → Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B;app37
 = λ t u Tm37 var37 lam37 app37 →
     app37 _ _ _ (t Tm37 var37 lam37 app37) (u Tm37 var37 lam37 app37)

v037 : ∀{Γ A} → Tm37 (snoc37 Γ A) A;v037
 = var37 vz37

v137 : ∀{Γ A B} → Tm37 (snoc37 (snoc37 Γ A) B) A;v137
 = var37 (vs37 vz37)

v237 : ∀{Γ A B C} → Tm37 (snoc37 (snoc37 (snoc37 Γ A) B) C) A;v237
 = var37 (vs37 (vs37 vz37))

v337 : ∀{Γ A B C D} → Tm37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) A;v337
 = var37 (vs37 (vs37 (vs37 vz37)))

v437 : ∀{Γ A B C D E} → Tm37 (snoc37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) E) A;v437
 = var37 (vs37 (vs37 (vs37 (vs37 vz37))))

test37 : ∀{Γ A} → Tm37 Γ (arr37 (arr37 A A) (arr37 A A));test37
  = lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037)))))))
{-# OPTIONS --type-in-type #-}

Ty38 : Set; Ty38
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι38   : Ty38; ι38 = λ _ ι38 _ → ι38
arr38 : Ty38 → Ty38 → Ty38; arr38 = λ A B Ty38 ι38 arr38 → arr38 (A Ty38 ι38 arr38) (B Ty38 ι38 arr38)

Con38 : Set;Con38
 = (Con38 : Set)
   (nil  : Con38)
   (snoc : Con38 → Ty38 → Con38)
 → Con38

nil38 : Con38;nil38
 = λ Con38 nil38 snoc → nil38

snoc38 : Con38 → Ty38 → Con38;snoc38
 = λ Γ A Con38 nil38 snoc38 → snoc38 (Γ Con38 nil38 snoc38) A

Var38 : Con38 → Ty38 → Set;Var38
 = λ Γ A →
   (Var38 : Con38 → Ty38 → Set)
   (vz  : (Γ : _)(A : _) → Var38 (snoc38 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var38 Γ A → Var38 (snoc38 Γ B) A)
 → Var38 Γ A

vz38 : ∀{Γ A} → Var38 (snoc38 Γ A) A;vz38
 = λ Var38 vz38 vs → vz38 _ _

vs38 : ∀{Γ B A} → Var38 Γ A → Var38 (snoc38 Γ B) A;vs38
 = λ x Var38 vz38 vs38 → vs38 _ _ _ (x Var38 vz38 vs38)

Tm38 : Con38 → Ty38 → Set;Tm38
 = λ Γ A →
   (Tm38    : Con38 → Ty38 → Set)
   (var   : (Γ : _) (A : _) → Var38 Γ A → Tm38 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B))
   (app   : (Γ : _) (A B : _) → Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B)
 → Tm38 Γ A

var38 : ∀{Γ A} → Var38 Γ A → Tm38 Γ A;var38
 = λ x Tm38 var38 lam app → var38 _ _ x

lam38 : ∀{Γ A B} → Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B);lam38
 = λ t Tm38 var38 lam38 app → lam38 _ _ _ (t Tm38 var38 lam38 app)

app38 : ∀{Γ A B} → Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B;app38
 = λ t u Tm38 var38 lam38 app38 →
     app38 _ _ _ (t Tm38 var38 lam38 app38) (u Tm38 var38 lam38 app38)

v038 : ∀{Γ A} → Tm38 (snoc38 Γ A) A;v038
 = var38 vz38

v138 : ∀{Γ A B} → Tm38 (snoc38 (snoc38 Γ A) B) A;v138
 = var38 (vs38 vz38)

v238 : ∀{Γ A B C} → Tm38 (snoc38 (snoc38 (snoc38 Γ A) B) C) A;v238
 = var38 (vs38 (vs38 vz38))

v338 : ∀{Γ A B C D} → Tm38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) A;v338
 = var38 (vs38 (vs38 (vs38 vz38)))

v438 : ∀{Γ A B C D E} → Tm38 (snoc38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) E) A;v438
 = var38 (vs38 (vs38 (vs38 (vs38 vz38))))

test38 : ∀{Γ A} → Tm38 Γ (arr38 (arr38 A A) (arr38 A A));test38
  = lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038)))))))
{-# OPTIONS --type-in-type #-}

Ty39 : Set; Ty39
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι39   : Ty39; ι39 = λ _ ι39 _ → ι39
arr39 : Ty39 → Ty39 → Ty39; arr39 = λ A B Ty39 ι39 arr39 → arr39 (A Ty39 ι39 arr39) (B Ty39 ι39 arr39)

Con39 : Set;Con39
 = (Con39 : Set)
   (nil  : Con39)
   (snoc : Con39 → Ty39 → Con39)
 → Con39

nil39 : Con39;nil39
 = λ Con39 nil39 snoc → nil39

snoc39 : Con39 → Ty39 → Con39;snoc39
 = λ Γ A Con39 nil39 snoc39 → snoc39 (Γ Con39 nil39 snoc39) A

Var39 : Con39 → Ty39 → Set;Var39
 = λ Γ A →
   (Var39 : Con39 → Ty39 → Set)
   (vz  : (Γ : _)(A : _) → Var39 (snoc39 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var39 Γ A → Var39 (snoc39 Γ B) A)
 → Var39 Γ A

vz39 : ∀{Γ A} → Var39 (snoc39 Γ A) A;vz39
 = λ Var39 vz39 vs → vz39 _ _

vs39 : ∀{Γ B A} → Var39 Γ A → Var39 (snoc39 Γ B) A;vs39
 = λ x Var39 vz39 vs39 → vs39 _ _ _ (x Var39 vz39 vs39)

Tm39 : Con39 → Ty39 → Set;Tm39
 = λ Γ A →
   (Tm39    : Con39 → Ty39 → Set)
   (var   : (Γ : _) (A : _) → Var39 Γ A → Tm39 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B))
   (app   : (Γ : _) (A B : _) → Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B)
 → Tm39 Γ A

var39 : ∀{Γ A} → Var39 Γ A → Tm39 Γ A;var39
 = λ x Tm39 var39 lam app → var39 _ _ x

lam39 : ∀{Γ A B} → Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B);lam39
 = λ t Tm39 var39 lam39 app → lam39 _ _ _ (t Tm39 var39 lam39 app)

app39 : ∀{Γ A B} → Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B;app39
 = λ t u Tm39 var39 lam39 app39 →
     app39 _ _ _ (t Tm39 var39 lam39 app39) (u Tm39 var39 lam39 app39)

v039 : ∀{Γ A} → Tm39 (snoc39 Γ A) A;v039
 = var39 vz39

v139 : ∀{Γ A B} → Tm39 (snoc39 (snoc39 Γ A) B) A;v139
 = var39 (vs39 vz39)

v239 : ∀{Γ A B C} → Tm39 (snoc39 (snoc39 (snoc39 Γ A) B) C) A;v239
 = var39 (vs39 (vs39 vz39))

v339 : ∀{Γ A B C D} → Tm39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) A;v339
 = var39 (vs39 (vs39 (vs39 vz39)))

v439 : ∀{Γ A B C D E} → Tm39 (snoc39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) E) A;v439
 = var39 (vs39 (vs39 (vs39 (vs39 vz39))))

test39 : ∀{Γ A} → Tm39 Γ (arr39 (arr39 A A) (arr39 A A));test39
  = lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039)))))))
{-# OPTIONS --type-in-type #-}

Ty40 : Set; Ty40
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι40   : Ty40; ι40 = λ _ ι40 _ → ι40
arr40 : Ty40 → Ty40 → Ty40; arr40 = λ A B Ty40 ι40 arr40 → arr40 (A Ty40 ι40 arr40) (B Ty40 ι40 arr40)

Con40 : Set;Con40
 = (Con40 : Set)
   (nil  : Con40)
   (snoc : Con40 → Ty40 → Con40)
 → Con40

nil40 : Con40;nil40
 = λ Con40 nil40 snoc → nil40

snoc40 : Con40 → Ty40 → Con40;snoc40
 = λ Γ A Con40 nil40 snoc40 → snoc40 (Γ Con40 nil40 snoc40) A

Var40 : Con40 → Ty40 → Set;Var40
 = λ Γ A →
   (Var40 : Con40 → Ty40 → Set)
   (vz  : (Γ : _)(A : _) → Var40 (snoc40 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var40 Γ A → Var40 (snoc40 Γ B) A)
 → Var40 Γ A

vz40 : ∀{Γ A} → Var40 (snoc40 Γ A) A;vz40
 = λ Var40 vz40 vs → vz40 _ _

vs40 : ∀{Γ B A} → Var40 Γ A → Var40 (snoc40 Γ B) A;vs40
 = λ x Var40 vz40 vs40 → vs40 _ _ _ (x Var40 vz40 vs40)

Tm40 : Con40 → Ty40 → Set;Tm40
 = λ Γ A →
   (Tm40    : Con40 → Ty40 → Set)
   (var   : (Γ : _) (A : _) → Var40 Γ A → Tm40 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B))
   (app   : (Γ : _) (A B : _) → Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B)
 → Tm40 Γ A

var40 : ∀{Γ A} → Var40 Γ A → Tm40 Γ A;var40
 = λ x Tm40 var40 lam app → var40 _ _ x

lam40 : ∀{Γ A B} → Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B);lam40
 = λ t Tm40 var40 lam40 app → lam40 _ _ _ (t Tm40 var40 lam40 app)

app40 : ∀{Γ A B} → Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B;app40
 = λ t u Tm40 var40 lam40 app40 →
     app40 _ _ _ (t Tm40 var40 lam40 app40) (u Tm40 var40 lam40 app40)

v040 : ∀{Γ A} → Tm40 (snoc40 Γ A) A;v040
 = var40 vz40

v140 : ∀{Γ A B} → Tm40 (snoc40 (snoc40 Γ A) B) A;v140
 = var40 (vs40 vz40)

v240 : ∀{Γ A B C} → Tm40 (snoc40 (snoc40 (snoc40 Γ A) B) C) A;v240
 = var40 (vs40 (vs40 vz40))

v340 : ∀{Γ A B C D} → Tm40 (snoc40 (snoc40 (snoc40 (snoc40 Γ A) B) C) D) A;v340
 = var40 (vs40 (vs40 (vs40 vz40)))

v440 : ∀{Γ A B C D E} → Tm40 (snoc40 (snoc40 (snoc40 (snoc40 (snoc40 Γ A) B) C) D) E) A;v440
 = var40 (vs40 (vs40 (vs40 (vs40 vz40))))

test40 : ∀{Γ A} → Tm40 Γ (arr40 (arr40 A A) (arr40 A A));test40
  = lam40 (lam40 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 v040)))))))
{-# OPTIONS --type-in-type #-}

Ty41 : Set; Ty41
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι41   : Ty41; ι41 = λ _ ι41 _ → ι41
arr41 : Ty41 → Ty41 → Ty41; arr41 = λ A B Ty41 ι41 arr41 → arr41 (A Ty41 ι41 arr41) (B Ty41 ι41 arr41)

Con41 : Set;Con41
 = (Con41 : Set)
   (nil  : Con41)
   (snoc : Con41 → Ty41 → Con41)
 → Con41

nil41 : Con41;nil41
 = λ Con41 nil41 snoc → nil41

snoc41 : Con41 → Ty41 → Con41;snoc41
 = λ Γ A Con41 nil41 snoc41 → snoc41 (Γ Con41 nil41 snoc41) A

Var41 : Con41 → Ty41 → Set;Var41
 = λ Γ A →
   (Var41 : Con41 → Ty41 → Set)
   (vz  : (Γ : _)(A : _) → Var41 (snoc41 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var41 Γ A → Var41 (snoc41 Γ B) A)
 → Var41 Γ A

vz41 : ∀{Γ A} → Var41 (snoc41 Γ A) A;vz41
 = λ Var41 vz41 vs → vz41 _ _

vs41 : ∀{Γ B A} → Var41 Γ A → Var41 (snoc41 Γ B) A;vs41
 = λ x Var41 vz41 vs41 → vs41 _ _ _ (x Var41 vz41 vs41)

Tm41 : Con41 → Ty41 → Set;Tm41
 = λ Γ A →
   (Tm41    : Con41 → Ty41 → Set)
   (var   : (Γ : _) (A : _) → Var41 Γ A → Tm41 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B))
   (app   : (Γ : _) (A B : _) → Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B)
 → Tm41 Γ A

var41 : ∀{Γ A} → Var41 Γ A → Tm41 Γ A;var41
 = λ x Tm41 var41 lam app → var41 _ _ x

lam41 : ∀{Γ A B} → Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B);lam41
 = λ t Tm41 var41 lam41 app → lam41 _ _ _ (t Tm41 var41 lam41 app)

app41 : ∀{Γ A B} → Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B;app41
 = λ t u Tm41 var41 lam41 app41 →
     app41 _ _ _ (t Tm41 var41 lam41 app41) (u Tm41 var41 lam41 app41)

v041 : ∀{Γ A} → Tm41 (snoc41 Γ A) A;v041
 = var41 vz41

v141 : ∀{Γ A B} → Tm41 (snoc41 (snoc41 Γ A) B) A;v141
 = var41 (vs41 vz41)

v241 : ∀{Γ A B C} → Tm41 (snoc41 (snoc41 (snoc41 Γ A) B) C) A;v241
 = var41 (vs41 (vs41 vz41))

v341 : ∀{Γ A B C D} → Tm41 (snoc41 (snoc41 (snoc41 (snoc41 Γ A) B) C) D) A;v341
 = var41 (vs41 (vs41 (vs41 vz41)))

v441 : ∀{Γ A B C D E} → Tm41 (snoc41 (snoc41 (snoc41 (snoc41 (snoc41 Γ A) B) C) D) E) A;v441
 = var41 (vs41 (vs41 (vs41 (vs41 vz41))))

test41 : ∀{Γ A} → Tm41 Γ (arr41 (arr41 A A) (arr41 A A));test41
  = lam41 (lam41 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 v041)))))))
{-# OPTIONS --type-in-type #-}

Ty42 : Set; Ty42
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι42   : Ty42; ι42 = λ _ ι42 _ → ι42
arr42 : Ty42 → Ty42 → Ty42; arr42 = λ A B Ty42 ι42 arr42 → arr42 (A Ty42 ι42 arr42) (B Ty42 ι42 arr42)

Con42 : Set;Con42
 = (Con42 : Set)
   (nil  : Con42)
   (snoc : Con42 → Ty42 → Con42)
 → Con42

nil42 : Con42;nil42
 = λ Con42 nil42 snoc → nil42

snoc42 : Con42 → Ty42 → Con42;snoc42
 = λ Γ A Con42 nil42 snoc42 → snoc42 (Γ Con42 nil42 snoc42) A

Var42 : Con42 → Ty42 → Set;Var42
 = λ Γ A →
   (Var42 : Con42 → Ty42 → Set)
   (vz  : (Γ : _)(A : _) → Var42 (snoc42 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var42 Γ A → Var42 (snoc42 Γ B) A)
 → Var42 Γ A

vz42 : ∀{Γ A} → Var42 (snoc42 Γ A) A;vz42
 = λ Var42 vz42 vs → vz42 _ _

vs42 : ∀{Γ B A} → Var42 Γ A → Var42 (snoc42 Γ B) A;vs42
 = λ x Var42 vz42 vs42 → vs42 _ _ _ (x Var42 vz42 vs42)

Tm42 : Con42 → Ty42 → Set;Tm42
 = λ Γ A →
   (Tm42    : Con42 → Ty42 → Set)
   (var   : (Γ : _) (A : _) → Var42 Γ A → Tm42 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B))
   (app   : (Γ : _) (A B : _) → Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B)
 → Tm42 Γ A

var42 : ∀{Γ A} → Var42 Γ A → Tm42 Γ A;var42
 = λ x Tm42 var42 lam app → var42 _ _ x

lam42 : ∀{Γ A B} → Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B);lam42
 = λ t Tm42 var42 lam42 app → lam42 _ _ _ (t Tm42 var42 lam42 app)

app42 : ∀{Γ A B} → Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B;app42
 = λ t u Tm42 var42 lam42 app42 →
     app42 _ _ _ (t Tm42 var42 lam42 app42) (u Tm42 var42 lam42 app42)

v042 : ∀{Γ A} → Tm42 (snoc42 Γ A) A;v042
 = var42 vz42

v142 : ∀{Γ A B} → Tm42 (snoc42 (snoc42 Γ A) B) A;v142
 = var42 (vs42 vz42)

v242 : ∀{Γ A B C} → Tm42 (snoc42 (snoc42 (snoc42 Γ A) B) C) A;v242
 = var42 (vs42 (vs42 vz42))

v342 : ∀{Γ A B C D} → Tm42 (snoc42 (snoc42 (snoc42 (snoc42 Γ A) B) C) D) A;v342
 = var42 (vs42 (vs42 (vs42 vz42)))

v442 : ∀{Γ A B C D E} → Tm42 (snoc42 (snoc42 (snoc42 (snoc42 (snoc42 Γ A) B) C) D) E) A;v442
 = var42 (vs42 (vs42 (vs42 (vs42 vz42))))

test42 : ∀{Γ A} → Tm42 Γ (arr42 (arr42 A A) (arr42 A A));test42
  = lam42 (lam42 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 v042)))))))
{-# OPTIONS --type-in-type #-}

Ty43 : Set; Ty43
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι43   : Ty43; ι43 = λ _ ι43 _ → ι43
arr43 : Ty43 → Ty43 → Ty43; arr43 = λ A B Ty43 ι43 arr43 → arr43 (A Ty43 ι43 arr43) (B Ty43 ι43 arr43)

Con43 : Set;Con43
 = (Con43 : Set)
   (nil  : Con43)
   (snoc : Con43 → Ty43 → Con43)
 → Con43

nil43 : Con43;nil43
 = λ Con43 nil43 snoc → nil43

snoc43 : Con43 → Ty43 → Con43;snoc43
 = λ Γ A Con43 nil43 snoc43 → snoc43 (Γ Con43 nil43 snoc43) A

Var43 : Con43 → Ty43 → Set;Var43
 = λ Γ A →
   (Var43 : Con43 → Ty43 → Set)
   (vz  : (Γ : _)(A : _) → Var43 (snoc43 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var43 Γ A → Var43 (snoc43 Γ B) A)
 → Var43 Γ A

vz43 : ∀{Γ A} → Var43 (snoc43 Γ A) A;vz43
 = λ Var43 vz43 vs → vz43 _ _

vs43 : ∀{Γ B A} → Var43 Γ A → Var43 (snoc43 Γ B) A;vs43
 = λ x Var43 vz43 vs43 → vs43 _ _ _ (x Var43 vz43 vs43)

Tm43 : Con43 → Ty43 → Set;Tm43
 = λ Γ A →
   (Tm43    : Con43 → Ty43 → Set)
   (var   : (Γ : _) (A : _) → Var43 Γ A → Tm43 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B))
   (app   : (Γ : _) (A B : _) → Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B)
 → Tm43 Γ A

var43 : ∀{Γ A} → Var43 Γ A → Tm43 Γ A;var43
 = λ x Tm43 var43 lam app → var43 _ _ x

lam43 : ∀{Γ A B} → Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B);lam43
 = λ t Tm43 var43 lam43 app → lam43 _ _ _ (t Tm43 var43 lam43 app)

app43 : ∀{Γ A B} → Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B;app43
 = λ t u Tm43 var43 lam43 app43 →
     app43 _ _ _ (t Tm43 var43 lam43 app43) (u Tm43 var43 lam43 app43)

v043 : ∀{Γ A} → Tm43 (snoc43 Γ A) A;v043
 = var43 vz43

v143 : ∀{Γ A B} → Tm43 (snoc43 (snoc43 Γ A) B) A;v143
 = var43 (vs43 vz43)

v243 : ∀{Γ A B C} → Tm43 (snoc43 (snoc43 (snoc43 Γ A) B) C) A;v243
 = var43 (vs43 (vs43 vz43))

v343 : ∀{Γ A B C D} → Tm43 (snoc43 (snoc43 (snoc43 (snoc43 Γ A) B) C) D) A;v343
 = var43 (vs43 (vs43 (vs43 vz43)))

v443 : ∀{Γ A B C D E} → Tm43 (snoc43 (snoc43 (snoc43 (snoc43 (snoc43 Γ A) B) C) D) E) A;v443
 = var43 (vs43 (vs43 (vs43 (vs43 vz43))))

test43 : ∀{Γ A} → Tm43 Γ (arr43 (arr43 A A) (arr43 A A));test43
  = lam43 (lam43 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 v043)))))))
{-# OPTIONS --type-in-type #-}

Ty44 : Set; Ty44
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι44   : Ty44; ι44 = λ _ ι44 _ → ι44
arr44 : Ty44 → Ty44 → Ty44; arr44 = λ A B Ty44 ι44 arr44 → arr44 (A Ty44 ι44 arr44) (B Ty44 ι44 arr44)

Con44 : Set;Con44
 = (Con44 : Set)
   (nil  : Con44)
   (snoc : Con44 → Ty44 → Con44)
 → Con44

nil44 : Con44;nil44
 = λ Con44 nil44 snoc → nil44

snoc44 : Con44 → Ty44 → Con44;snoc44
 = λ Γ A Con44 nil44 snoc44 → snoc44 (Γ Con44 nil44 snoc44) A

Var44 : Con44 → Ty44 → Set;Var44
 = λ Γ A →
   (Var44 : Con44 → Ty44 → Set)
   (vz  : (Γ : _)(A : _) → Var44 (snoc44 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var44 Γ A → Var44 (snoc44 Γ B) A)
 → Var44 Γ A

vz44 : ∀{Γ A} → Var44 (snoc44 Γ A) A;vz44
 = λ Var44 vz44 vs → vz44 _ _

vs44 : ∀{Γ B A} → Var44 Γ A → Var44 (snoc44 Γ B) A;vs44
 = λ x Var44 vz44 vs44 → vs44 _ _ _ (x Var44 vz44 vs44)

Tm44 : Con44 → Ty44 → Set;Tm44
 = λ Γ A →
   (Tm44    : Con44 → Ty44 → Set)
   (var   : (Γ : _) (A : _) → Var44 Γ A → Tm44 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B))
   (app   : (Γ : _) (A B : _) → Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B)
 → Tm44 Γ A

var44 : ∀{Γ A} → Var44 Γ A → Tm44 Γ A;var44
 = λ x Tm44 var44 lam app → var44 _ _ x

lam44 : ∀{Γ A B} → Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B);lam44
 = λ t Tm44 var44 lam44 app → lam44 _ _ _ (t Tm44 var44 lam44 app)

app44 : ∀{Γ A B} → Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B;app44
 = λ t u Tm44 var44 lam44 app44 →
     app44 _ _ _ (t Tm44 var44 lam44 app44) (u Tm44 var44 lam44 app44)

v044 : ∀{Γ A} → Tm44 (snoc44 Γ A) A;v044
 = var44 vz44

v144 : ∀{Γ A B} → Tm44 (snoc44 (snoc44 Γ A) B) A;v144
 = var44 (vs44 vz44)

v244 : ∀{Γ A B C} → Tm44 (snoc44 (snoc44 (snoc44 Γ A) B) C) A;v244
 = var44 (vs44 (vs44 vz44))

v344 : ∀{Γ A B C D} → Tm44 (snoc44 (snoc44 (snoc44 (snoc44 Γ A) B) C) D) A;v344
 = var44 (vs44 (vs44 (vs44 vz44)))

v444 : ∀{Γ A B C D E} → Tm44 (snoc44 (snoc44 (snoc44 (snoc44 (snoc44 Γ A) B) C) D) E) A;v444
 = var44 (vs44 (vs44 (vs44 (vs44 vz44))))

test44 : ∀{Γ A} → Tm44 Γ (arr44 (arr44 A A) (arr44 A A));test44
  = lam44 (lam44 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 v044)))))))
{-# OPTIONS --type-in-type #-}

Ty45 : Set; Ty45
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι45   : Ty45; ι45 = λ _ ι45 _ → ι45
arr45 : Ty45 → Ty45 → Ty45; arr45 = λ A B Ty45 ι45 arr45 → arr45 (A Ty45 ι45 arr45) (B Ty45 ι45 arr45)

Con45 : Set;Con45
 = (Con45 : Set)
   (nil  : Con45)
   (snoc : Con45 → Ty45 → Con45)
 → Con45

nil45 : Con45;nil45
 = λ Con45 nil45 snoc → nil45

snoc45 : Con45 → Ty45 → Con45;snoc45
 = λ Γ A Con45 nil45 snoc45 → snoc45 (Γ Con45 nil45 snoc45) A

Var45 : Con45 → Ty45 → Set;Var45
 = λ Γ A →
   (Var45 : Con45 → Ty45 → Set)
   (vz  : (Γ : _)(A : _) → Var45 (snoc45 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var45 Γ A → Var45 (snoc45 Γ B) A)
 → Var45 Γ A

vz45 : ∀{Γ A} → Var45 (snoc45 Γ A) A;vz45
 = λ Var45 vz45 vs → vz45 _ _

vs45 : ∀{Γ B A} → Var45 Γ A → Var45 (snoc45 Γ B) A;vs45
 = λ x Var45 vz45 vs45 → vs45 _ _ _ (x Var45 vz45 vs45)

Tm45 : Con45 → Ty45 → Set;Tm45
 = λ Γ A →
   (Tm45    : Con45 → Ty45 → Set)
   (var   : (Γ : _) (A : _) → Var45 Γ A → Tm45 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B))
   (app   : (Γ : _) (A B : _) → Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B)
 → Tm45 Γ A

var45 : ∀{Γ A} → Var45 Γ A → Tm45 Γ A;var45
 = λ x Tm45 var45 lam app → var45 _ _ x

lam45 : ∀{Γ A B} → Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B);lam45
 = λ t Tm45 var45 lam45 app → lam45 _ _ _ (t Tm45 var45 lam45 app)

app45 : ∀{Γ A B} → Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B;app45
 = λ t u Tm45 var45 lam45 app45 →
     app45 _ _ _ (t Tm45 var45 lam45 app45) (u Tm45 var45 lam45 app45)

v045 : ∀{Γ A} → Tm45 (snoc45 Γ A) A;v045
 = var45 vz45

v145 : ∀{Γ A B} → Tm45 (snoc45 (snoc45 Γ A) B) A;v145
 = var45 (vs45 vz45)

v245 : ∀{Γ A B C} → Tm45 (snoc45 (snoc45 (snoc45 Γ A) B) C) A;v245
 = var45 (vs45 (vs45 vz45))

v345 : ∀{Γ A B C D} → Tm45 (snoc45 (snoc45 (snoc45 (snoc45 Γ A) B) C) D) A;v345
 = var45 (vs45 (vs45 (vs45 vz45)))

v445 : ∀{Γ A B C D E} → Tm45 (snoc45 (snoc45 (snoc45 (snoc45 (snoc45 Γ A) B) C) D) E) A;v445
 = var45 (vs45 (vs45 (vs45 (vs45 vz45))))

test45 : ∀{Γ A} → Tm45 Γ (arr45 (arr45 A A) (arr45 A A));test45
  = lam45 (lam45 (app45 v145 (app45 v145 (app45 v145 (app45 v145 (app45 v145 (app45 v145 v045)))))))
{-# OPTIONS --type-in-type #-}

Ty46 : Set; Ty46
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι46   : Ty46; ι46 = λ _ ι46 _ → ι46
arr46 : Ty46 → Ty46 → Ty46; arr46 = λ A B Ty46 ι46 arr46 → arr46 (A Ty46 ι46 arr46) (B Ty46 ι46 arr46)

Con46 : Set;Con46
 = (Con46 : Set)
   (nil  : Con46)
   (snoc : Con46 → Ty46 → Con46)
 → Con46

nil46 : Con46;nil46
 = λ Con46 nil46 snoc → nil46

snoc46 : Con46 → Ty46 → Con46;snoc46
 = λ Γ A Con46 nil46 snoc46 → snoc46 (Γ Con46 nil46 snoc46) A

Var46 : Con46 → Ty46 → Set;Var46
 = λ Γ A →
   (Var46 : Con46 → Ty46 → Set)
   (vz  : (Γ : _)(A : _) → Var46 (snoc46 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var46 Γ A → Var46 (snoc46 Γ B) A)
 → Var46 Γ A

vz46 : ∀{Γ A} → Var46 (snoc46 Γ A) A;vz46
 = λ Var46 vz46 vs → vz46 _ _

vs46 : ∀{Γ B A} → Var46 Γ A → Var46 (snoc46 Γ B) A;vs46
 = λ x Var46 vz46 vs46 → vs46 _ _ _ (x Var46 vz46 vs46)

Tm46 : Con46 → Ty46 → Set;Tm46
 = λ Γ A →
   (Tm46    : Con46 → Ty46 → Set)
   (var   : (Γ : _) (A : _) → Var46 Γ A → Tm46 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B))
   (app   : (Γ : _) (A B : _) → Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B)
 → Tm46 Γ A

var46 : ∀{Γ A} → Var46 Γ A → Tm46 Γ A;var46
 = λ x Tm46 var46 lam app → var46 _ _ x

lam46 : ∀{Γ A B} → Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B);lam46
 = λ t Tm46 var46 lam46 app → lam46 _ _ _ (t Tm46 var46 lam46 app)

app46 : ∀{Γ A B} → Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B;app46
 = λ t u Tm46 var46 lam46 app46 →
     app46 _ _ _ (t Tm46 var46 lam46 app46) (u Tm46 var46 lam46 app46)

v046 : ∀{Γ A} → Tm46 (snoc46 Γ A) A;v046
 = var46 vz46

v146 : ∀{Γ A B} → Tm46 (snoc46 (snoc46 Γ A) B) A;v146
 = var46 (vs46 vz46)

v246 : ∀{Γ A B C} → Tm46 (snoc46 (snoc46 (snoc46 Γ A) B) C) A;v246
 = var46 (vs46 (vs46 vz46))

v346 : ∀{Γ A B C D} → Tm46 (snoc46 (snoc46 (snoc46 (snoc46 Γ A) B) C) D) A;v346
 = var46 (vs46 (vs46 (vs46 vz46)))

v446 : ∀{Γ A B C D E} → Tm46 (snoc46 (snoc46 (snoc46 (snoc46 (snoc46 Γ A) B) C) D) E) A;v446
 = var46 (vs46 (vs46 (vs46 (vs46 vz46))))

test46 : ∀{Γ A} → Tm46 Γ (arr46 (arr46 A A) (arr46 A A));test46
  = lam46 (lam46 (app46 v146 (app46 v146 (app46 v146 (app46 v146 (app46 v146 (app46 v146 v046)))))))
{-# OPTIONS --type-in-type #-}

Ty47 : Set; Ty47
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι47   : Ty47; ι47 = λ _ ι47 _ → ι47
arr47 : Ty47 → Ty47 → Ty47; arr47 = λ A B Ty47 ι47 arr47 → arr47 (A Ty47 ι47 arr47) (B Ty47 ι47 arr47)

Con47 : Set;Con47
 = (Con47 : Set)
   (nil  : Con47)
   (snoc : Con47 → Ty47 → Con47)
 → Con47

nil47 : Con47;nil47
 = λ Con47 nil47 snoc → nil47

snoc47 : Con47 → Ty47 → Con47;snoc47
 = λ Γ A Con47 nil47 snoc47 → snoc47 (Γ Con47 nil47 snoc47) A

Var47 : Con47 → Ty47 → Set;Var47
 = λ Γ A →
   (Var47 : Con47 → Ty47 → Set)
   (vz  : (Γ : _)(A : _) → Var47 (snoc47 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var47 Γ A → Var47 (snoc47 Γ B) A)
 → Var47 Γ A

vz47 : ∀{Γ A} → Var47 (snoc47 Γ A) A;vz47
 = λ Var47 vz47 vs → vz47 _ _

vs47 : ∀{Γ B A} → Var47 Γ A → Var47 (snoc47 Γ B) A;vs47
 = λ x Var47 vz47 vs47 → vs47 _ _ _ (x Var47 vz47 vs47)

Tm47 : Con47 → Ty47 → Set;Tm47
 = λ Γ A →
   (Tm47    : Con47 → Ty47 → Set)
   (var   : (Γ : _) (A : _) → Var47 Γ A → Tm47 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B))
   (app   : (Γ : _) (A B : _) → Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B)
 → Tm47 Γ A

var47 : ∀{Γ A} → Var47 Γ A → Tm47 Γ A;var47
 = λ x Tm47 var47 lam app → var47 _ _ x

lam47 : ∀{Γ A B} → Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B);lam47
 = λ t Tm47 var47 lam47 app → lam47 _ _ _ (t Tm47 var47 lam47 app)

app47 : ∀{Γ A B} → Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B;app47
 = λ t u Tm47 var47 lam47 app47 →
     app47 _ _ _ (t Tm47 var47 lam47 app47) (u Tm47 var47 lam47 app47)

v047 : ∀{Γ A} → Tm47 (snoc47 Γ A) A;v047
 = var47 vz47

v147 : ∀{Γ A B} → Tm47 (snoc47 (snoc47 Γ A) B) A;v147
 = var47 (vs47 vz47)

v247 : ∀{Γ A B C} → Tm47 (snoc47 (snoc47 (snoc47 Γ A) B) C) A;v247
 = var47 (vs47 (vs47 vz47))

v347 : ∀{Γ A B C D} → Tm47 (snoc47 (snoc47 (snoc47 (snoc47 Γ A) B) C) D) A;v347
 = var47 (vs47 (vs47 (vs47 vz47)))

v447 : ∀{Γ A B C D E} → Tm47 (snoc47 (snoc47 (snoc47 (snoc47 (snoc47 Γ A) B) C) D) E) A;v447
 = var47 (vs47 (vs47 (vs47 (vs47 vz47))))

test47 : ∀{Γ A} → Tm47 Γ (arr47 (arr47 A A) (arr47 A A));test47
  = lam47 (lam47 (app47 v147 (app47 v147 (app47 v147 (app47 v147 (app47 v147 (app47 v147 v047)))))))
{-# OPTIONS --type-in-type #-}

Ty48 : Set; Ty48
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι48   : Ty48; ι48 = λ _ ι48 _ → ι48
arr48 : Ty48 → Ty48 → Ty48; arr48 = λ A B Ty48 ι48 arr48 → arr48 (A Ty48 ι48 arr48) (B Ty48 ι48 arr48)

Con48 : Set;Con48
 = (Con48 : Set)
   (nil  : Con48)
   (snoc : Con48 → Ty48 → Con48)
 → Con48

nil48 : Con48;nil48
 = λ Con48 nil48 snoc → nil48

snoc48 : Con48 → Ty48 → Con48;snoc48
 = λ Γ A Con48 nil48 snoc48 → snoc48 (Γ Con48 nil48 snoc48) A

Var48 : Con48 → Ty48 → Set;Var48
 = λ Γ A →
   (Var48 : Con48 → Ty48 → Set)
   (vz  : (Γ : _)(A : _) → Var48 (snoc48 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var48 Γ A → Var48 (snoc48 Γ B) A)
 → Var48 Γ A

vz48 : ∀{Γ A} → Var48 (snoc48 Γ A) A;vz48
 = λ Var48 vz48 vs → vz48 _ _

vs48 : ∀{Γ B A} → Var48 Γ A → Var48 (snoc48 Γ B) A;vs48
 = λ x Var48 vz48 vs48 → vs48 _ _ _ (x Var48 vz48 vs48)

Tm48 : Con48 → Ty48 → Set;Tm48
 = λ Γ A →
   (Tm48    : Con48 → Ty48 → Set)
   (var   : (Γ : _) (A : _) → Var48 Γ A → Tm48 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B))
   (app   : (Γ : _) (A B : _) → Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B)
 → Tm48 Γ A

var48 : ∀{Γ A} → Var48 Γ A → Tm48 Γ A;var48
 = λ x Tm48 var48 lam app → var48 _ _ x

lam48 : ∀{Γ A B} → Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B);lam48
 = λ t Tm48 var48 lam48 app → lam48 _ _ _ (t Tm48 var48 lam48 app)

app48 : ∀{Γ A B} → Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B;app48
 = λ t u Tm48 var48 lam48 app48 →
     app48 _ _ _ (t Tm48 var48 lam48 app48) (u Tm48 var48 lam48 app48)

v048 : ∀{Γ A} → Tm48 (snoc48 Γ A) A;v048
 = var48 vz48

v148 : ∀{Γ A B} → Tm48 (snoc48 (snoc48 Γ A) B) A;v148
 = var48 (vs48 vz48)

v248 : ∀{Γ A B C} → Tm48 (snoc48 (snoc48 (snoc48 Γ A) B) C) A;v248
 = var48 (vs48 (vs48 vz48))

v348 : ∀{Γ A B C D} → Tm48 (snoc48 (snoc48 (snoc48 (snoc48 Γ A) B) C) D) A;v348
 = var48 (vs48 (vs48 (vs48 vz48)))

v448 : ∀{Γ A B C D E} → Tm48 (snoc48 (snoc48 (snoc48 (snoc48 (snoc48 Γ A) B) C) D) E) A;v448
 = var48 (vs48 (vs48 (vs48 (vs48 vz48))))

test48 : ∀{Γ A} → Tm48 Γ (arr48 (arr48 A A) (arr48 A A));test48
  = lam48 (lam48 (app48 v148 (app48 v148 (app48 v148 (app48 v148 (app48 v148 (app48 v148 v048)))))))
{-# OPTIONS --type-in-type #-}

Ty49 : Set; Ty49
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι49   : Ty49; ι49 = λ _ ι49 _ → ι49
arr49 : Ty49 → Ty49 → Ty49; arr49 = λ A B Ty49 ι49 arr49 → arr49 (A Ty49 ι49 arr49) (B Ty49 ι49 arr49)

Con49 : Set;Con49
 = (Con49 : Set)
   (nil  : Con49)
   (snoc : Con49 → Ty49 → Con49)
 → Con49

nil49 : Con49;nil49
 = λ Con49 nil49 snoc → nil49

snoc49 : Con49 → Ty49 → Con49;snoc49
 = λ Γ A Con49 nil49 snoc49 → snoc49 (Γ Con49 nil49 snoc49) A

Var49 : Con49 → Ty49 → Set;Var49
 = λ Γ A →
   (Var49 : Con49 → Ty49 → Set)
   (vz  : (Γ : _)(A : _) → Var49 (snoc49 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var49 Γ A → Var49 (snoc49 Γ B) A)
 → Var49 Γ A

vz49 : ∀{Γ A} → Var49 (snoc49 Γ A) A;vz49
 = λ Var49 vz49 vs → vz49 _ _

vs49 : ∀{Γ B A} → Var49 Γ A → Var49 (snoc49 Γ B) A;vs49
 = λ x Var49 vz49 vs49 → vs49 _ _ _ (x Var49 vz49 vs49)

Tm49 : Con49 → Ty49 → Set;Tm49
 = λ Γ A →
   (Tm49    : Con49 → Ty49 → Set)
   (var   : (Γ : _) (A : _) → Var49 Γ A → Tm49 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B))
   (app   : (Γ : _) (A B : _) → Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B)
 → Tm49 Γ A

var49 : ∀{Γ A} → Var49 Γ A → Tm49 Γ A;var49
 = λ x Tm49 var49 lam app → var49 _ _ x

lam49 : ∀{Γ A B} → Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B);lam49
 = λ t Tm49 var49 lam49 app → lam49 _ _ _ (t Tm49 var49 lam49 app)

app49 : ∀{Γ A B} → Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B;app49
 = λ t u Tm49 var49 lam49 app49 →
     app49 _ _ _ (t Tm49 var49 lam49 app49) (u Tm49 var49 lam49 app49)

v049 : ∀{Γ A} → Tm49 (snoc49 Γ A) A;v049
 = var49 vz49

v149 : ∀{Γ A B} → Tm49 (snoc49 (snoc49 Γ A) B) A;v149
 = var49 (vs49 vz49)

v249 : ∀{Γ A B C} → Tm49 (snoc49 (snoc49 (snoc49 Γ A) B) C) A;v249
 = var49 (vs49 (vs49 vz49))

v349 : ∀{Γ A B C D} → Tm49 (snoc49 (snoc49 (snoc49 (snoc49 Γ A) B) C) D) A;v349
 = var49 (vs49 (vs49 (vs49 vz49)))

v449 : ∀{Γ A B C D E} → Tm49 (snoc49 (snoc49 (snoc49 (snoc49 (snoc49 Γ A) B) C) D) E) A;v449
 = var49 (vs49 (vs49 (vs49 (vs49 vz49))))

test49 : ∀{Γ A} → Tm49 Γ (arr49 (arr49 A A) (arr49 A A));test49
  = lam49 (lam49 (app49 v149 (app49 v149 (app49 v149 (app49 v149 (app49 v149 (app49 v149 v049)))))))
{-# OPTIONS --type-in-type #-}

Ty50 : Set; Ty50
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι50   : Ty50; ι50 = λ _ ι50 _ → ι50
arr50 : Ty50 → Ty50 → Ty50; arr50 = λ A B Ty50 ι50 arr50 → arr50 (A Ty50 ι50 arr50) (B Ty50 ι50 arr50)

Con50 : Set;Con50
 = (Con50 : Set)
   (nil  : Con50)
   (snoc : Con50 → Ty50 → Con50)
 → Con50

nil50 : Con50;nil50
 = λ Con50 nil50 snoc → nil50

snoc50 : Con50 → Ty50 → Con50;snoc50
 = λ Γ A Con50 nil50 snoc50 → snoc50 (Γ Con50 nil50 snoc50) A

Var50 : Con50 → Ty50 → Set;Var50
 = λ Γ A →
   (Var50 : Con50 → Ty50 → Set)
   (vz  : (Γ : _)(A : _) → Var50 (snoc50 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var50 Γ A → Var50 (snoc50 Γ B) A)
 → Var50 Γ A

vz50 : ∀{Γ A} → Var50 (snoc50 Γ A) A;vz50
 = λ Var50 vz50 vs → vz50 _ _

vs50 : ∀{Γ B A} → Var50 Γ A → Var50 (snoc50 Γ B) A;vs50
 = λ x Var50 vz50 vs50 → vs50 _ _ _ (x Var50 vz50 vs50)

Tm50 : Con50 → Ty50 → Set;Tm50
 = λ Γ A →
   (Tm50    : Con50 → Ty50 → Set)
   (var   : (Γ : _) (A : _) → Var50 Γ A → Tm50 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B))
   (app   : (Γ : _) (A B : _) → Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B)
 → Tm50 Γ A

var50 : ∀{Γ A} → Var50 Γ A → Tm50 Γ A;var50
 = λ x Tm50 var50 lam app → var50 _ _ x

lam50 : ∀{Γ A B} → Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B);lam50
 = λ t Tm50 var50 lam50 app → lam50 _ _ _ (t Tm50 var50 lam50 app)

app50 : ∀{Γ A B} → Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B;app50
 = λ t u Tm50 var50 lam50 app50 →
     app50 _ _ _ (t Tm50 var50 lam50 app50) (u Tm50 var50 lam50 app50)

v050 : ∀{Γ A} → Tm50 (snoc50 Γ A) A;v050
 = var50 vz50

v150 : ∀{Γ A B} → Tm50 (snoc50 (snoc50 Γ A) B) A;v150
 = var50 (vs50 vz50)

v250 : ∀{Γ A B C} → Tm50 (snoc50 (snoc50 (snoc50 Γ A) B) C) A;v250
 = var50 (vs50 (vs50 vz50))

v350 : ∀{Γ A B C D} → Tm50 (snoc50 (snoc50 (snoc50 (snoc50 Γ A) B) C) D) A;v350
 = var50 (vs50 (vs50 (vs50 vz50)))

v450 : ∀{Γ A B C D E} → Tm50 (snoc50 (snoc50 (snoc50 (snoc50 (snoc50 Γ A) B) C) D) E) A;v450
 = var50 (vs50 (vs50 (vs50 (vs50 vz50))))

test50 : ∀{Γ A} → Tm50 Γ (arr50 (arr50 A A) (arr50 A A));test50
  = lam50 (lam50 (app50 v150 (app50 v150 (app50 v150 (app50 v150 (app50 v150 (app50 v150 v050)))))))
{-# OPTIONS --type-in-type #-}

Ty51 : Set; Ty51
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι51   : Ty51; ι51 = λ _ ι51 _ → ι51
arr51 : Ty51 → Ty51 → Ty51; arr51 = λ A B Ty51 ι51 arr51 → arr51 (A Ty51 ι51 arr51) (B Ty51 ι51 arr51)

Con51 : Set;Con51
 = (Con51 : Set)
   (nil  : Con51)
   (snoc : Con51 → Ty51 → Con51)
 → Con51

nil51 : Con51;nil51
 = λ Con51 nil51 snoc → nil51

snoc51 : Con51 → Ty51 → Con51;snoc51
 = λ Γ A Con51 nil51 snoc51 → snoc51 (Γ Con51 nil51 snoc51) A

Var51 : Con51 → Ty51 → Set;Var51
 = λ Γ A →
   (Var51 : Con51 → Ty51 → Set)
   (vz  : (Γ : _)(A : _) → Var51 (snoc51 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var51 Γ A → Var51 (snoc51 Γ B) A)
 → Var51 Γ A

vz51 : ∀{Γ A} → Var51 (snoc51 Γ A) A;vz51
 = λ Var51 vz51 vs → vz51 _ _

vs51 : ∀{Γ B A} → Var51 Γ A → Var51 (snoc51 Γ B) A;vs51
 = λ x Var51 vz51 vs51 → vs51 _ _ _ (x Var51 vz51 vs51)

Tm51 : Con51 → Ty51 → Set;Tm51
 = λ Γ A →
   (Tm51    : Con51 → Ty51 → Set)
   (var   : (Γ : _) (A : _) → Var51 Γ A → Tm51 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B))
   (app   : (Γ : _) (A B : _) → Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B)
 → Tm51 Γ A

var51 : ∀{Γ A} → Var51 Γ A → Tm51 Γ A;var51
 = λ x Tm51 var51 lam app → var51 _ _ x

lam51 : ∀{Γ A B} → Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B);lam51
 = λ t Tm51 var51 lam51 app → lam51 _ _ _ (t Tm51 var51 lam51 app)

app51 : ∀{Γ A B} → Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B;app51
 = λ t u Tm51 var51 lam51 app51 →
     app51 _ _ _ (t Tm51 var51 lam51 app51) (u Tm51 var51 lam51 app51)

v051 : ∀{Γ A} → Tm51 (snoc51 Γ A) A;v051
 = var51 vz51

v151 : ∀{Γ A B} → Tm51 (snoc51 (snoc51 Γ A) B) A;v151
 = var51 (vs51 vz51)

v251 : ∀{Γ A B C} → Tm51 (snoc51 (snoc51 (snoc51 Γ A) B) C) A;v251
 = var51 (vs51 (vs51 vz51))

v351 : ∀{Γ A B C D} → Tm51 (snoc51 (snoc51 (snoc51 (snoc51 Γ A) B) C) D) A;v351
 = var51 (vs51 (vs51 (vs51 vz51)))

v451 : ∀{Γ A B C D E} → Tm51 (snoc51 (snoc51 (snoc51 (snoc51 (snoc51 Γ A) B) C) D) E) A;v451
 = var51 (vs51 (vs51 (vs51 (vs51 vz51))))

test51 : ∀{Γ A} → Tm51 Γ (arr51 (arr51 A A) (arr51 A A));test51
  = lam51 (lam51 (app51 v151 (app51 v151 (app51 v151 (app51 v151 (app51 v151 (app51 v151 v051)))))))
{-# OPTIONS --type-in-type #-}

Ty52 : Set; Ty52
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι52   : Ty52; ι52 = λ _ ι52 _ → ι52
arr52 : Ty52 → Ty52 → Ty52; arr52 = λ A B Ty52 ι52 arr52 → arr52 (A Ty52 ι52 arr52) (B Ty52 ι52 arr52)

Con52 : Set;Con52
 = (Con52 : Set)
   (nil  : Con52)
   (snoc : Con52 → Ty52 → Con52)
 → Con52

nil52 : Con52;nil52
 = λ Con52 nil52 snoc → nil52

snoc52 : Con52 → Ty52 → Con52;snoc52
 = λ Γ A Con52 nil52 snoc52 → snoc52 (Γ Con52 nil52 snoc52) A

Var52 : Con52 → Ty52 → Set;Var52
 = λ Γ A →
   (Var52 : Con52 → Ty52 → Set)
   (vz  : (Γ : _)(A : _) → Var52 (snoc52 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var52 Γ A → Var52 (snoc52 Γ B) A)
 → Var52 Γ A

vz52 : ∀{Γ A} → Var52 (snoc52 Γ A) A;vz52
 = λ Var52 vz52 vs → vz52 _ _

vs52 : ∀{Γ B A} → Var52 Γ A → Var52 (snoc52 Γ B) A;vs52
 = λ x Var52 vz52 vs52 → vs52 _ _ _ (x Var52 vz52 vs52)

Tm52 : Con52 → Ty52 → Set;Tm52
 = λ Γ A →
   (Tm52    : Con52 → Ty52 → Set)
   (var   : (Γ : _) (A : _) → Var52 Γ A → Tm52 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B))
   (app   : (Γ : _) (A B : _) → Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B)
 → Tm52 Γ A

var52 : ∀{Γ A} → Var52 Γ A → Tm52 Γ A;var52
 = λ x Tm52 var52 lam app → var52 _ _ x

lam52 : ∀{Γ A B} → Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B);lam52
 = λ t Tm52 var52 lam52 app → lam52 _ _ _ (t Tm52 var52 lam52 app)

app52 : ∀{Γ A B} → Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B;app52
 = λ t u Tm52 var52 lam52 app52 →
     app52 _ _ _ (t Tm52 var52 lam52 app52) (u Tm52 var52 lam52 app52)

v052 : ∀{Γ A} → Tm52 (snoc52 Γ A) A;v052
 = var52 vz52

v152 : ∀{Γ A B} → Tm52 (snoc52 (snoc52 Γ A) B) A;v152
 = var52 (vs52 vz52)

v252 : ∀{Γ A B C} → Tm52 (snoc52 (snoc52 (snoc52 Γ A) B) C) A;v252
 = var52 (vs52 (vs52 vz52))

v352 : ∀{Γ A B C D} → Tm52 (snoc52 (snoc52 (snoc52 (snoc52 Γ A) B) C) D) A;v352
 = var52 (vs52 (vs52 (vs52 vz52)))

v452 : ∀{Γ A B C D E} → Tm52 (snoc52 (snoc52 (snoc52 (snoc52 (snoc52 Γ A) B) C) D) E) A;v452
 = var52 (vs52 (vs52 (vs52 (vs52 vz52))))

test52 : ∀{Γ A} → Tm52 Γ (arr52 (arr52 A A) (arr52 A A));test52
  = lam52 (lam52 (app52 v152 (app52 v152 (app52 v152 (app52 v152 (app52 v152 (app52 v152 v052)))))))
{-# OPTIONS --type-in-type #-}

Ty53 : Set; Ty53
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι53   : Ty53; ι53 = λ _ ι53 _ → ι53
arr53 : Ty53 → Ty53 → Ty53; arr53 = λ A B Ty53 ι53 arr53 → arr53 (A Ty53 ι53 arr53) (B Ty53 ι53 arr53)

Con53 : Set;Con53
 = (Con53 : Set)
   (nil  : Con53)
   (snoc : Con53 → Ty53 → Con53)
 → Con53

nil53 : Con53;nil53
 = λ Con53 nil53 snoc → nil53

snoc53 : Con53 → Ty53 → Con53;snoc53
 = λ Γ A Con53 nil53 snoc53 → snoc53 (Γ Con53 nil53 snoc53) A

Var53 : Con53 → Ty53 → Set;Var53
 = λ Γ A →
   (Var53 : Con53 → Ty53 → Set)
   (vz  : (Γ : _)(A : _) → Var53 (snoc53 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var53 Γ A → Var53 (snoc53 Γ B) A)
 → Var53 Γ A

vz53 : ∀{Γ A} → Var53 (snoc53 Γ A) A;vz53
 = λ Var53 vz53 vs → vz53 _ _

vs53 : ∀{Γ B A} → Var53 Γ A → Var53 (snoc53 Γ B) A;vs53
 = λ x Var53 vz53 vs53 → vs53 _ _ _ (x Var53 vz53 vs53)

Tm53 : Con53 → Ty53 → Set;Tm53
 = λ Γ A →
   (Tm53    : Con53 → Ty53 → Set)
   (var   : (Γ : _) (A : _) → Var53 Γ A → Tm53 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B))
   (app   : (Γ : _) (A B : _) → Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B)
 → Tm53 Γ A

var53 : ∀{Γ A} → Var53 Γ A → Tm53 Γ A;var53
 = λ x Tm53 var53 lam app → var53 _ _ x

lam53 : ∀{Γ A B} → Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B);lam53
 = λ t Tm53 var53 lam53 app → lam53 _ _ _ (t Tm53 var53 lam53 app)

app53 : ∀{Γ A B} → Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B;app53
 = λ t u Tm53 var53 lam53 app53 →
     app53 _ _ _ (t Tm53 var53 lam53 app53) (u Tm53 var53 lam53 app53)

v053 : ∀{Γ A} → Tm53 (snoc53 Γ A) A;v053
 = var53 vz53

v153 : ∀{Γ A B} → Tm53 (snoc53 (snoc53 Γ A) B) A;v153
 = var53 (vs53 vz53)

v253 : ∀{Γ A B C} → Tm53 (snoc53 (snoc53 (snoc53 Γ A) B) C) A;v253
 = var53 (vs53 (vs53 vz53))

v353 : ∀{Γ A B C D} → Tm53 (snoc53 (snoc53 (snoc53 (snoc53 Γ A) B) C) D) A;v353
 = var53 (vs53 (vs53 (vs53 vz53)))

v453 : ∀{Γ A B C D E} → Tm53 (snoc53 (snoc53 (snoc53 (snoc53 (snoc53 Γ A) B) C) D) E) A;v453
 = var53 (vs53 (vs53 (vs53 (vs53 vz53))))

test53 : ∀{Γ A} → Tm53 Γ (arr53 (arr53 A A) (arr53 A A));test53
  = lam53 (lam53 (app53 v153 (app53 v153 (app53 v153 (app53 v153 (app53 v153 (app53 v153 v053)))))))
{-# OPTIONS --type-in-type #-}

Ty54 : Set; Ty54
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι54   : Ty54; ι54 = λ _ ι54 _ → ι54
arr54 : Ty54 → Ty54 → Ty54; arr54 = λ A B Ty54 ι54 arr54 → arr54 (A Ty54 ι54 arr54) (B Ty54 ι54 arr54)

Con54 : Set;Con54
 = (Con54 : Set)
   (nil  : Con54)
   (snoc : Con54 → Ty54 → Con54)
 → Con54

nil54 : Con54;nil54
 = λ Con54 nil54 snoc → nil54

snoc54 : Con54 → Ty54 → Con54;snoc54
 = λ Γ A Con54 nil54 snoc54 → snoc54 (Γ Con54 nil54 snoc54) A

Var54 : Con54 → Ty54 → Set;Var54
 = λ Γ A →
   (Var54 : Con54 → Ty54 → Set)
   (vz  : (Γ : _)(A : _) → Var54 (snoc54 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var54 Γ A → Var54 (snoc54 Γ B) A)
 → Var54 Γ A

vz54 : ∀{Γ A} → Var54 (snoc54 Γ A) A;vz54
 = λ Var54 vz54 vs → vz54 _ _

vs54 : ∀{Γ B A} → Var54 Γ A → Var54 (snoc54 Γ B) A;vs54
 = λ x Var54 vz54 vs54 → vs54 _ _ _ (x Var54 vz54 vs54)

Tm54 : Con54 → Ty54 → Set;Tm54
 = λ Γ A →
   (Tm54    : Con54 → Ty54 → Set)
   (var   : (Γ : _) (A : _) → Var54 Γ A → Tm54 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B))
   (app   : (Γ : _) (A B : _) → Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B)
 → Tm54 Γ A

var54 : ∀{Γ A} → Var54 Γ A → Tm54 Γ A;var54
 = λ x Tm54 var54 lam app → var54 _ _ x

lam54 : ∀{Γ A B} → Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B);lam54
 = λ t Tm54 var54 lam54 app → lam54 _ _ _ (t Tm54 var54 lam54 app)

app54 : ∀{Γ A B} → Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B;app54
 = λ t u Tm54 var54 lam54 app54 →
     app54 _ _ _ (t Tm54 var54 lam54 app54) (u Tm54 var54 lam54 app54)

v054 : ∀{Γ A} → Tm54 (snoc54 Γ A) A;v054
 = var54 vz54

v154 : ∀{Γ A B} → Tm54 (snoc54 (snoc54 Γ A) B) A;v154
 = var54 (vs54 vz54)

v254 : ∀{Γ A B C} → Tm54 (snoc54 (snoc54 (snoc54 Γ A) B) C) A;v254
 = var54 (vs54 (vs54 vz54))

v354 : ∀{Γ A B C D} → Tm54 (snoc54 (snoc54 (snoc54 (snoc54 Γ A) B) C) D) A;v354
 = var54 (vs54 (vs54 (vs54 vz54)))

v454 : ∀{Γ A B C D E} → Tm54 (snoc54 (snoc54 (snoc54 (snoc54 (snoc54 Γ A) B) C) D) E) A;v454
 = var54 (vs54 (vs54 (vs54 (vs54 vz54))))

test54 : ∀{Γ A} → Tm54 Γ (arr54 (arr54 A A) (arr54 A A));test54
  = lam54 (lam54 (app54 v154 (app54 v154 (app54 v154 (app54 v154 (app54 v154 (app54 v154 v054)))))))
{-# OPTIONS --type-in-type #-}

Ty55 : Set; Ty55
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι55   : Ty55; ι55 = λ _ ι55 _ → ι55
arr55 : Ty55 → Ty55 → Ty55; arr55 = λ A B Ty55 ι55 arr55 → arr55 (A Ty55 ι55 arr55) (B Ty55 ι55 arr55)

Con55 : Set;Con55
 = (Con55 : Set)
   (nil  : Con55)
   (snoc : Con55 → Ty55 → Con55)
 → Con55

nil55 : Con55;nil55
 = λ Con55 nil55 snoc → nil55

snoc55 : Con55 → Ty55 → Con55;snoc55
 = λ Γ A Con55 nil55 snoc55 → snoc55 (Γ Con55 nil55 snoc55) A

Var55 : Con55 → Ty55 → Set;Var55
 = λ Γ A →
   (Var55 : Con55 → Ty55 → Set)
   (vz  : (Γ : _)(A : _) → Var55 (snoc55 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var55 Γ A → Var55 (snoc55 Γ B) A)
 → Var55 Γ A

vz55 : ∀{Γ A} → Var55 (snoc55 Γ A) A;vz55
 = λ Var55 vz55 vs → vz55 _ _

vs55 : ∀{Γ B A} → Var55 Γ A → Var55 (snoc55 Γ B) A;vs55
 = λ x Var55 vz55 vs55 → vs55 _ _ _ (x Var55 vz55 vs55)

Tm55 : Con55 → Ty55 → Set;Tm55
 = λ Γ A →
   (Tm55    : Con55 → Ty55 → Set)
   (var   : (Γ : _) (A : _) → Var55 Γ A → Tm55 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B))
   (app   : (Γ : _) (A B : _) → Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B)
 → Tm55 Γ A

var55 : ∀{Γ A} → Var55 Γ A → Tm55 Γ A;var55
 = λ x Tm55 var55 lam app → var55 _ _ x

lam55 : ∀{Γ A B} → Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B);lam55
 = λ t Tm55 var55 lam55 app → lam55 _ _ _ (t Tm55 var55 lam55 app)

app55 : ∀{Γ A B} → Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B;app55
 = λ t u Tm55 var55 lam55 app55 →
     app55 _ _ _ (t Tm55 var55 lam55 app55) (u Tm55 var55 lam55 app55)

v055 : ∀{Γ A} → Tm55 (snoc55 Γ A) A;v055
 = var55 vz55

v155 : ∀{Γ A B} → Tm55 (snoc55 (snoc55 Γ A) B) A;v155
 = var55 (vs55 vz55)

v255 : ∀{Γ A B C} → Tm55 (snoc55 (snoc55 (snoc55 Γ A) B) C) A;v255
 = var55 (vs55 (vs55 vz55))

v355 : ∀{Γ A B C D} → Tm55 (snoc55 (snoc55 (snoc55 (snoc55 Γ A) B) C) D) A;v355
 = var55 (vs55 (vs55 (vs55 vz55)))

v455 : ∀{Γ A B C D E} → Tm55 (snoc55 (snoc55 (snoc55 (snoc55 (snoc55 Γ A) B) C) D) E) A;v455
 = var55 (vs55 (vs55 (vs55 (vs55 vz55))))

test55 : ∀{Γ A} → Tm55 Γ (arr55 (arr55 A A) (arr55 A A));test55
  = lam55 (lam55 (app55 v155 (app55 v155 (app55 v155 (app55 v155 (app55 v155 (app55 v155 v055)))))))
{-# OPTIONS --type-in-type #-}

Ty56 : Set; Ty56
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι56   : Ty56; ι56 = λ _ ι56 _ → ι56
arr56 : Ty56 → Ty56 → Ty56; arr56 = λ A B Ty56 ι56 arr56 → arr56 (A Ty56 ι56 arr56) (B Ty56 ι56 arr56)

Con56 : Set;Con56
 = (Con56 : Set)
   (nil  : Con56)
   (snoc : Con56 → Ty56 → Con56)
 → Con56

nil56 : Con56;nil56
 = λ Con56 nil56 snoc → nil56

snoc56 : Con56 → Ty56 → Con56;snoc56
 = λ Γ A Con56 nil56 snoc56 → snoc56 (Γ Con56 nil56 snoc56) A

Var56 : Con56 → Ty56 → Set;Var56
 = λ Γ A →
   (Var56 : Con56 → Ty56 → Set)
   (vz  : (Γ : _)(A : _) → Var56 (snoc56 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var56 Γ A → Var56 (snoc56 Γ B) A)
 → Var56 Γ A

vz56 : ∀{Γ A} → Var56 (snoc56 Γ A) A;vz56
 = λ Var56 vz56 vs → vz56 _ _

vs56 : ∀{Γ B A} → Var56 Γ A → Var56 (snoc56 Γ B) A;vs56
 = λ x Var56 vz56 vs56 → vs56 _ _ _ (x Var56 vz56 vs56)

Tm56 : Con56 → Ty56 → Set;Tm56
 = λ Γ A →
   (Tm56    : Con56 → Ty56 → Set)
   (var   : (Γ : _) (A : _) → Var56 Γ A → Tm56 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B))
   (app   : (Γ : _) (A B : _) → Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B)
 → Tm56 Γ A

var56 : ∀{Γ A} → Var56 Γ A → Tm56 Γ A;var56
 = λ x Tm56 var56 lam app → var56 _ _ x

lam56 : ∀{Γ A B} → Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B);lam56
 = λ t Tm56 var56 lam56 app → lam56 _ _ _ (t Tm56 var56 lam56 app)

app56 : ∀{Γ A B} → Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B;app56
 = λ t u Tm56 var56 lam56 app56 →
     app56 _ _ _ (t Tm56 var56 lam56 app56) (u Tm56 var56 lam56 app56)

v056 : ∀{Γ A} → Tm56 (snoc56 Γ A) A;v056
 = var56 vz56

v156 : ∀{Γ A B} → Tm56 (snoc56 (snoc56 Γ A) B) A;v156
 = var56 (vs56 vz56)

v256 : ∀{Γ A B C} → Tm56 (snoc56 (snoc56 (snoc56 Γ A) B) C) A;v256
 = var56 (vs56 (vs56 vz56))

v356 : ∀{Γ A B C D} → Tm56 (snoc56 (snoc56 (snoc56 (snoc56 Γ A) B) C) D) A;v356
 = var56 (vs56 (vs56 (vs56 vz56)))

v456 : ∀{Γ A B C D E} → Tm56 (snoc56 (snoc56 (snoc56 (snoc56 (snoc56 Γ A) B) C) D) E) A;v456
 = var56 (vs56 (vs56 (vs56 (vs56 vz56))))

test56 : ∀{Γ A} → Tm56 Γ (arr56 (arr56 A A) (arr56 A A));test56
  = lam56 (lam56 (app56 v156 (app56 v156 (app56 v156 (app56 v156 (app56 v156 (app56 v156 v056)))))))
{-# OPTIONS --type-in-type #-}

Ty57 : Set; Ty57
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι57   : Ty57; ι57 = λ _ ι57 _ → ι57
arr57 : Ty57 → Ty57 → Ty57; arr57 = λ A B Ty57 ι57 arr57 → arr57 (A Ty57 ι57 arr57) (B Ty57 ι57 arr57)

Con57 : Set;Con57
 = (Con57 : Set)
   (nil  : Con57)
   (snoc : Con57 → Ty57 → Con57)
 → Con57

nil57 : Con57;nil57
 = λ Con57 nil57 snoc → nil57

snoc57 : Con57 → Ty57 → Con57;snoc57
 = λ Γ A Con57 nil57 snoc57 → snoc57 (Γ Con57 nil57 snoc57) A

Var57 : Con57 → Ty57 → Set;Var57
 = λ Γ A →
   (Var57 : Con57 → Ty57 → Set)
   (vz  : (Γ : _)(A : _) → Var57 (snoc57 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var57 Γ A → Var57 (snoc57 Γ B) A)
 → Var57 Γ A

vz57 : ∀{Γ A} → Var57 (snoc57 Γ A) A;vz57
 = λ Var57 vz57 vs → vz57 _ _

vs57 : ∀{Γ B A} → Var57 Γ A → Var57 (snoc57 Γ B) A;vs57
 = λ x Var57 vz57 vs57 → vs57 _ _ _ (x Var57 vz57 vs57)

Tm57 : Con57 → Ty57 → Set;Tm57
 = λ Γ A →
   (Tm57    : Con57 → Ty57 → Set)
   (var   : (Γ : _) (A : _) → Var57 Γ A → Tm57 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B))
   (app   : (Γ : _) (A B : _) → Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B)
 → Tm57 Γ A

var57 : ∀{Γ A} → Var57 Γ A → Tm57 Γ A;var57
 = λ x Tm57 var57 lam app → var57 _ _ x

lam57 : ∀{Γ A B} → Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B);lam57
 = λ t Tm57 var57 lam57 app → lam57 _ _ _ (t Tm57 var57 lam57 app)

app57 : ∀{Γ A B} → Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B;app57
 = λ t u Tm57 var57 lam57 app57 →
     app57 _ _ _ (t Tm57 var57 lam57 app57) (u Tm57 var57 lam57 app57)

v057 : ∀{Γ A} → Tm57 (snoc57 Γ A) A;v057
 = var57 vz57

v157 : ∀{Γ A B} → Tm57 (snoc57 (snoc57 Γ A) B) A;v157
 = var57 (vs57 vz57)

v257 : ∀{Γ A B C} → Tm57 (snoc57 (snoc57 (snoc57 Γ A) B) C) A;v257
 = var57 (vs57 (vs57 vz57))

v357 : ∀{Γ A B C D} → Tm57 (snoc57 (snoc57 (snoc57 (snoc57 Γ A) B) C) D) A;v357
 = var57 (vs57 (vs57 (vs57 vz57)))

v457 : ∀{Γ A B C D E} → Tm57 (snoc57 (snoc57 (snoc57 (snoc57 (snoc57 Γ A) B) C) D) E) A;v457
 = var57 (vs57 (vs57 (vs57 (vs57 vz57))))

test57 : ∀{Γ A} → Tm57 Γ (arr57 (arr57 A A) (arr57 A A));test57
  = lam57 (lam57 (app57 v157 (app57 v157 (app57 v157 (app57 v157 (app57 v157 (app57 v157 v057)))))))
{-# OPTIONS --type-in-type #-}

Ty58 : Set; Ty58
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι58   : Ty58; ι58 = λ _ ι58 _ → ι58
arr58 : Ty58 → Ty58 → Ty58; arr58 = λ A B Ty58 ι58 arr58 → arr58 (A Ty58 ι58 arr58) (B Ty58 ι58 arr58)

Con58 : Set;Con58
 = (Con58 : Set)
   (nil  : Con58)
   (snoc : Con58 → Ty58 → Con58)
 → Con58

nil58 : Con58;nil58
 = λ Con58 nil58 snoc → nil58

snoc58 : Con58 → Ty58 → Con58;snoc58
 = λ Γ A Con58 nil58 snoc58 → snoc58 (Γ Con58 nil58 snoc58) A

Var58 : Con58 → Ty58 → Set;Var58
 = λ Γ A →
   (Var58 : Con58 → Ty58 → Set)
   (vz  : (Γ : _)(A : _) → Var58 (snoc58 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var58 Γ A → Var58 (snoc58 Γ B) A)
 → Var58 Γ A

vz58 : ∀{Γ A} → Var58 (snoc58 Γ A) A;vz58
 = λ Var58 vz58 vs → vz58 _ _

vs58 : ∀{Γ B A} → Var58 Γ A → Var58 (snoc58 Γ B) A;vs58
 = λ x Var58 vz58 vs58 → vs58 _ _ _ (x Var58 vz58 vs58)

Tm58 : Con58 → Ty58 → Set;Tm58
 = λ Γ A →
   (Tm58    : Con58 → Ty58 → Set)
   (var   : (Γ : _) (A : _) → Var58 Γ A → Tm58 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B))
   (app   : (Γ : _) (A B : _) → Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B)
 → Tm58 Γ A

var58 : ∀{Γ A} → Var58 Γ A → Tm58 Γ A;var58
 = λ x Tm58 var58 lam app → var58 _ _ x

lam58 : ∀{Γ A B} → Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B);lam58
 = λ t Tm58 var58 lam58 app → lam58 _ _ _ (t Tm58 var58 lam58 app)

app58 : ∀{Γ A B} → Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B;app58
 = λ t u Tm58 var58 lam58 app58 →
     app58 _ _ _ (t Tm58 var58 lam58 app58) (u Tm58 var58 lam58 app58)

v058 : ∀{Γ A} → Tm58 (snoc58 Γ A) A;v058
 = var58 vz58

v158 : ∀{Γ A B} → Tm58 (snoc58 (snoc58 Γ A) B) A;v158
 = var58 (vs58 vz58)

v258 : ∀{Γ A B C} → Tm58 (snoc58 (snoc58 (snoc58 Γ A) B) C) A;v258
 = var58 (vs58 (vs58 vz58))

v358 : ∀{Γ A B C D} → Tm58 (snoc58 (snoc58 (snoc58 (snoc58 Γ A) B) C) D) A;v358
 = var58 (vs58 (vs58 (vs58 vz58)))

v458 : ∀{Γ A B C D E} → Tm58 (snoc58 (snoc58 (snoc58 (snoc58 (snoc58 Γ A) B) C) D) E) A;v458
 = var58 (vs58 (vs58 (vs58 (vs58 vz58))))

test58 : ∀{Γ A} → Tm58 Γ (arr58 (arr58 A A) (arr58 A A));test58
  = lam58 (lam58 (app58 v158 (app58 v158 (app58 v158 (app58 v158 (app58 v158 (app58 v158 v058)))))))
{-# OPTIONS --type-in-type #-}

Ty59 : Set; Ty59
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι59   : Ty59; ι59 = λ _ ι59 _ → ι59
arr59 : Ty59 → Ty59 → Ty59; arr59 = λ A B Ty59 ι59 arr59 → arr59 (A Ty59 ι59 arr59) (B Ty59 ι59 arr59)

Con59 : Set;Con59
 = (Con59 : Set)
   (nil  : Con59)
   (snoc : Con59 → Ty59 → Con59)
 → Con59

nil59 : Con59;nil59
 = λ Con59 nil59 snoc → nil59

snoc59 : Con59 → Ty59 → Con59;snoc59
 = λ Γ A Con59 nil59 snoc59 → snoc59 (Γ Con59 nil59 snoc59) A

Var59 : Con59 → Ty59 → Set;Var59
 = λ Γ A →
   (Var59 : Con59 → Ty59 → Set)
   (vz  : (Γ : _)(A : _) → Var59 (snoc59 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var59 Γ A → Var59 (snoc59 Γ B) A)
 → Var59 Γ A

vz59 : ∀{Γ A} → Var59 (snoc59 Γ A) A;vz59
 = λ Var59 vz59 vs → vz59 _ _

vs59 : ∀{Γ B A} → Var59 Γ A → Var59 (snoc59 Γ B) A;vs59
 = λ x Var59 vz59 vs59 → vs59 _ _ _ (x Var59 vz59 vs59)

Tm59 : Con59 → Ty59 → Set;Tm59
 = λ Γ A →
   (Tm59    : Con59 → Ty59 → Set)
   (var   : (Γ : _) (A : _) → Var59 Γ A → Tm59 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B))
   (app   : (Γ : _) (A B : _) → Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B)
 → Tm59 Γ A

var59 : ∀{Γ A} → Var59 Γ A → Tm59 Γ A;var59
 = λ x Tm59 var59 lam app → var59 _ _ x

lam59 : ∀{Γ A B} → Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B);lam59
 = λ t Tm59 var59 lam59 app → lam59 _ _ _ (t Tm59 var59 lam59 app)

app59 : ∀{Γ A B} → Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B;app59
 = λ t u Tm59 var59 lam59 app59 →
     app59 _ _ _ (t Tm59 var59 lam59 app59) (u Tm59 var59 lam59 app59)

v059 : ∀{Γ A} → Tm59 (snoc59 Γ A) A;v059
 = var59 vz59

v159 : ∀{Γ A B} → Tm59 (snoc59 (snoc59 Γ A) B) A;v159
 = var59 (vs59 vz59)

v259 : ∀{Γ A B C} → Tm59 (snoc59 (snoc59 (snoc59 Γ A) B) C) A;v259
 = var59 (vs59 (vs59 vz59))

v359 : ∀{Γ A B C D} → Tm59 (snoc59 (snoc59 (snoc59 (snoc59 Γ A) B) C) D) A;v359
 = var59 (vs59 (vs59 (vs59 vz59)))

v459 : ∀{Γ A B C D E} → Tm59 (snoc59 (snoc59 (snoc59 (snoc59 (snoc59 Γ A) B) C) D) E) A;v459
 = var59 (vs59 (vs59 (vs59 (vs59 vz59))))

test59 : ∀{Γ A} → Tm59 Γ (arr59 (arr59 A A) (arr59 A A));test59
  = lam59 (lam59 (app59 v159 (app59 v159 (app59 v159 (app59 v159 (app59 v159 (app59 v159 v059)))))))
{-# OPTIONS --type-in-type #-}

Ty60 : Set; Ty60
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι60   : Ty60; ι60 = λ _ ι60 _ → ι60
arr60 : Ty60 → Ty60 → Ty60; arr60 = λ A B Ty60 ι60 arr60 → arr60 (A Ty60 ι60 arr60) (B Ty60 ι60 arr60)

Con60 : Set;Con60
 = (Con60 : Set)
   (nil  : Con60)
   (snoc : Con60 → Ty60 → Con60)
 → Con60

nil60 : Con60;nil60
 = λ Con60 nil60 snoc → nil60

snoc60 : Con60 → Ty60 → Con60;snoc60
 = λ Γ A Con60 nil60 snoc60 → snoc60 (Γ Con60 nil60 snoc60) A

Var60 : Con60 → Ty60 → Set;Var60
 = λ Γ A →
   (Var60 : Con60 → Ty60 → Set)
   (vz  : (Γ : _)(A : _) → Var60 (snoc60 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var60 Γ A → Var60 (snoc60 Γ B) A)
 → Var60 Γ A

vz60 : ∀{Γ A} → Var60 (snoc60 Γ A) A;vz60
 = λ Var60 vz60 vs → vz60 _ _

vs60 : ∀{Γ B A} → Var60 Γ A → Var60 (snoc60 Γ B) A;vs60
 = λ x Var60 vz60 vs60 → vs60 _ _ _ (x Var60 vz60 vs60)

Tm60 : Con60 → Ty60 → Set;Tm60
 = λ Γ A →
   (Tm60    : Con60 → Ty60 → Set)
   (var   : (Γ : _) (A : _) → Var60 Γ A → Tm60 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B))
   (app   : (Γ : _) (A B : _) → Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B)
 → Tm60 Γ A

var60 : ∀{Γ A} → Var60 Γ A → Tm60 Γ A;var60
 = λ x Tm60 var60 lam app → var60 _ _ x

lam60 : ∀{Γ A B} → Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B);lam60
 = λ t Tm60 var60 lam60 app → lam60 _ _ _ (t Tm60 var60 lam60 app)

app60 : ∀{Γ A B} → Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B;app60
 = λ t u Tm60 var60 lam60 app60 →
     app60 _ _ _ (t Tm60 var60 lam60 app60) (u Tm60 var60 lam60 app60)

v060 : ∀{Γ A} → Tm60 (snoc60 Γ A) A;v060
 = var60 vz60

v160 : ∀{Γ A B} → Tm60 (snoc60 (snoc60 Γ A) B) A;v160
 = var60 (vs60 vz60)

v260 : ∀{Γ A B C} → Tm60 (snoc60 (snoc60 (snoc60 Γ A) B) C) A;v260
 = var60 (vs60 (vs60 vz60))

v360 : ∀{Γ A B C D} → Tm60 (snoc60 (snoc60 (snoc60 (snoc60 Γ A) B) C) D) A;v360
 = var60 (vs60 (vs60 (vs60 vz60)))

v460 : ∀{Γ A B C D E} → Tm60 (snoc60 (snoc60 (snoc60 (snoc60 (snoc60 Γ A) B) C) D) E) A;v460
 = var60 (vs60 (vs60 (vs60 (vs60 vz60))))

test60 : ∀{Γ A} → Tm60 Γ (arr60 (arr60 A A) (arr60 A A));test60
  = lam60 (lam60 (app60 v160 (app60 v160 (app60 v160 (app60 v160 (app60 v160 (app60 v160 v060)))))))
{-# OPTIONS --type-in-type #-}

Ty61 : Set; Ty61
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι61   : Ty61; ι61 = λ _ ι61 _ → ι61
arr61 : Ty61 → Ty61 → Ty61; arr61 = λ A B Ty61 ι61 arr61 → arr61 (A Ty61 ι61 arr61) (B Ty61 ι61 arr61)

Con61 : Set;Con61
 = (Con61 : Set)
   (nil  : Con61)
   (snoc : Con61 → Ty61 → Con61)
 → Con61

nil61 : Con61;nil61
 = λ Con61 nil61 snoc → nil61

snoc61 : Con61 → Ty61 → Con61;snoc61
 = λ Γ A Con61 nil61 snoc61 → snoc61 (Γ Con61 nil61 snoc61) A

Var61 : Con61 → Ty61 → Set;Var61
 = λ Γ A →
   (Var61 : Con61 → Ty61 → Set)
   (vz  : (Γ : _)(A : _) → Var61 (snoc61 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var61 Γ A → Var61 (snoc61 Γ B) A)
 → Var61 Γ A

vz61 : ∀{Γ A} → Var61 (snoc61 Γ A) A;vz61
 = λ Var61 vz61 vs → vz61 _ _

vs61 : ∀{Γ B A} → Var61 Γ A → Var61 (snoc61 Γ B) A;vs61
 = λ x Var61 vz61 vs61 → vs61 _ _ _ (x Var61 vz61 vs61)

Tm61 : Con61 → Ty61 → Set;Tm61
 = λ Γ A →
   (Tm61    : Con61 → Ty61 → Set)
   (var   : (Γ : _) (A : _) → Var61 Γ A → Tm61 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B))
   (app   : (Γ : _) (A B : _) → Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B)
 → Tm61 Γ A

var61 : ∀{Γ A} → Var61 Γ A → Tm61 Γ A;var61
 = λ x Tm61 var61 lam app → var61 _ _ x

lam61 : ∀{Γ A B} → Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B);lam61
 = λ t Tm61 var61 lam61 app → lam61 _ _ _ (t Tm61 var61 lam61 app)

app61 : ∀{Γ A B} → Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B;app61
 = λ t u Tm61 var61 lam61 app61 →
     app61 _ _ _ (t Tm61 var61 lam61 app61) (u Tm61 var61 lam61 app61)

v061 : ∀{Γ A} → Tm61 (snoc61 Γ A) A;v061
 = var61 vz61

v161 : ∀{Γ A B} → Tm61 (snoc61 (snoc61 Γ A) B) A;v161
 = var61 (vs61 vz61)

v261 : ∀{Γ A B C} → Tm61 (snoc61 (snoc61 (snoc61 Γ A) B) C) A;v261
 = var61 (vs61 (vs61 vz61))

v361 : ∀{Γ A B C D} → Tm61 (snoc61 (snoc61 (snoc61 (snoc61 Γ A) B) C) D) A;v361
 = var61 (vs61 (vs61 (vs61 vz61)))

v461 : ∀{Γ A B C D E} → Tm61 (snoc61 (snoc61 (snoc61 (snoc61 (snoc61 Γ A) B) C) D) E) A;v461
 = var61 (vs61 (vs61 (vs61 (vs61 vz61))))

test61 : ∀{Γ A} → Tm61 Γ (arr61 (arr61 A A) (arr61 A A));test61
  = lam61 (lam61 (app61 v161 (app61 v161 (app61 v161 (app61 v161 (app61 v161 (app61 v161 v061)))))))
{-# OPTIONS --type-in-type #-}

Ty62 : Set; Ty62
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι62   : Ty62; ι62 = λ _ ι62 _ → ι62
arr62 : Ty62 → Ty62 → Ty62; arr62 = λ A B Ty62 ι62 arr62 → arr62 (A Ty62 ι62 arr62) (B Ty62 ι62 arr62)

Con62 : Set;Con62
 = (Con62 : Set)
   (nil  : Con62)
   (snoc : Con62 → Ty62 → Con62)
 → Con62

nil62 : Con62;nil62
 = λ Con62 nil62 snoc → nil62

snoc62 : Con62 → Ty62 → Con62;snoc62
 = λ Γ A Con62 nil62 snoc62 → snoc62 (Γ Con62 nil62 snoc62) A

Var62 : Con62 → Ty62 → Set;Var62
 = λ Γ A →
   (Var62 : Con62 → Ty62 → Set)
   (vz  : (Γ : _)(A : _) → Var62 (snoc62 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var62 Γ A → Var62 (snoc62 Γ B) A)
 → Var62 Γ A

vz62 : ∀{Γ A} → Var62 (snoc62 Γ A) A;vz62
 = λ Var62 vz62 vs → vz62 _ _

vs62 : ∀{Γ B A} → Var62 Γ A → Var62 (snoc62 Γ B) A;vs62
 = λ x Var62 vz62 vs62 → vs62 _ _ _ (x Var62 vz62 vs62)

Tm62 : Con62 → Ty62 → Set;Tm62
 = λ Γ A →
   (Tm62    : Con62 → Ty62 → Set)
   (var   : (Γ : _) (A : _) → Var62 Γ A → Tm62 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B))
   (app   : (Γ : _) (A B : _) → Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B)
 → Tm62 Γ A

var62 : ∀{Γ A} → Var62 Γ A → Tm62 Γ A;var62
 = λ x Tm62 var62 lam app → var62 _ _ x

lam62 : ∀{Γ A B} → Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B);lam62
 = λ t Tm62 var62 lam62 app → lam62 _ _ _ (t Tm62 var62 lam62 app)

app62 : ∀{Γ A B} → Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B;app62
 = λ t u Tm62 var62 lam62 app62 →
     app62 _ _ _ (t Tm62 var62 lam62 app62) (u Tm62 var62 lam62 app62)

v062 : ∀{Γ A} → Tm62 (snoc62 Γ A) A;v062
 = var62 vz62

v162 : ∀{Γ A B} → Tm62 (snoc62 (snoc62 Γ A) B) A;v162
 = var62 (vs62 vz62)

v262 : ∀{Γ A B C} → Tm62 (snoc62 (snoc62 (snoc62 Γ A) B) C) A;v262
 = var62 (vs62 (vs62 vz62))

v362 : ∀{Γ A B C D} → Tm62 (snoc62 (snoc62 (snoc62 (snoc62 Γ A) B) C) D) A;v362
 = var62 (vs62 (vs62 (vs62 vz62)))

v462 : ∀{Γ A B C D E} → Tm62 (snoc62 (snoc62 (snoc62 (snoc62 (snoc62 Γ A) B) C) D) E) A;v462
 = var62 (vs62 (vs62 (vs62 (vs62 vz62))))

test62 : ∀{Γ A} → Tm62 Γ (arr62 (arr62 A A) (arr62 A A));test62
  = lam62 (lam62 (app62 v162 (app62 v162 (app62 v162 (app62 v162 (app62 v162 (app62 v162 v062)))))))
{-# OPTIONS --type-in-type #-}

Ty63 : Set; Ty63
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι63   : Ty63; ι63 = λ _ ι63 _ → ι63
arr63 : Ty63 → Ty63 → Ty63; arr63 = λ A B Ty63 ι63 arr63 → arr63 (A Ty63 ι63 arr63) (B Ty63 ι63 arr63)

Con63 : Set;Con63
 = (Con63 : Set)
   (nil  : Con63)
   (snoc : Con63 → Ty63 → Con63)
 → Con63

nil63 : Con63;nil63
 = λ Con63 nil63 snoc → nil63

snoc63 : Con63 → Ty63 → Con63;snoc63
 = λ Γ A Con63 nil63 snoc63 → snoc63 (Γ Con63 nil63 snoc63) A

Var63 : Con63 → Ty63 → Set;Var63
 = λ Γ A →
   (Var63 : Con63 → Ty63 → Set)
   (vz  : (Γ : _)(A : _) → Var63 (snoc63 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var63 Γ A → Var63 (snoc63 Γ B) A)
 → Var63 Γ A

vz63 : ∀{Γ A} → Var63 (snoc63 Γ A) A;vz63
 = λ Var63 vz63 vs → vz63 _ _

vs63 : ∀{Γ B A} → Var63 Γ A → Var63 (snoc63 Γ B) A;vs63
 = λ x Var63 vz63 vs63 → vs63 _ _ _ (x Var63 vz63 vs63)

Tm63 : Con63 → Ty63 → Set;Tm63
 = λ Γ A →
   (Tm63    : Con63 → Ty63 → Set)
   (var   : (Γ : _) (A : _) → Var63 Γ A → Tm63 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B))
   (app   : (Γ : _) (A B : _) → Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B)
 → Tm63 Γ A

var63 : ∀{Γ A} → Var63 Γ A → Tm63 Γ A;var63
 = λ x Tm63 var63 lam app → var63 _ _ x

lam63 : ∀{Γ A B} → Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B);lam63
 = λ t Tm63 var63 lam63 app → lam63 _ _ _ (t Tm63 var63 lam63 app)

app63 : ∀{Γ A B} → Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B;app63
 = λ t u Tm63 var63 lam63 app63 →
     app63 _ _ _ (t Tm63 var63 lam63 app63) (u Tm63 var63 lam63 app63)

v063 : ∀{Γ A} → Tm63 (snoc63 Γ A) A;v063
 = var63 vz63

v163 : ∀{Γ A B} → Tm63 (snoc63 (snoc63 Γ A) B) A;v163
 = var63 (vs63 vz63)

v263 : ∀{Γ A B C} → Tm63 (snoc63 (snoc63 (snoc63 Γ A) B) C) A;v263
 = var63 (vs63 (vs63 vz63))

v363 : ∀{Γ A B C D} → Tm63 (snoc63 (snoc63 (snoc63 (snoc63 Γ A) B) C) D) A;v363
 = var63 (vs63 (vs63 (vs63 vz63)))

v463 : ∀{Γ A B C D E} → Tm63 (snoc63 (snoc63 (snoc63 (snoc63 (snoc63 Γ A) B) C) D) E) A;v463
 = var63 (vs63 (vs63 (vs63 (vs63 vz63))))

test63 : ∀{Γ A} → Tm63 Γ (arr63 (arr63 A A) (arr63 A A));test63
  = lam63 (lam63 (app63 v163 (app63 v163 (app63 v163 (app63 v163 (app63 v163 (app63 v163 v063)))))))
{-# OPTIONS --type-in-type #-}

Ty64 : Set; Ty64
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι64   : Ty64; ι64 = λ _ ι64 _ → ι64
arr64 : Ty64 → Ty64 → Ty64; arr64 = λ A B Ty64 ι64 arr64 → arr64 (A Ty64 ι64 arr64) (B Ty64 ι64 arr64)

Con64 : Set;Con64
 = (Con64 : Set)
   (nil  : Con64)
   (snoc : Con64 → Ty64 → Con64)
 → Con64

nil64 : Con64;nil64
 = λ Con64 nil64 snoc → nil64

snoc64 : Con64 → Ty64 → Con64;snoc64
 = λ Γ A Con64 nil64 snoc64 → snoc64 (Γ Con64 nil64 snoc64) A

Var64 : Con64 → Ty64 → Set;Var64
 = λ Γ A →
   (Var64 : Con64 → Ty64 → Set)
   (vz  : (Γ : _)(A : _) → Var64 (snoc64 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var64 Γ A → Var64 (snoc64 Γ B) A)
 → Var64 Γ A

vz64 : ∀{Γ A} → Var64 (snoc64 Γ A) A;vz64
 = λ Var64 vz64 vs → vz64 _ _

vs64 : ∀{Γ B A} → Var64 Γ A → Var64 (snoc64 Γ B) A;vs64
 = λ x Var64 vz64 vs64 → vs64 _ _ _ (x Var64 vz64 vs64)

Tm64 : Con64 → Ty64 → Set;Tm64
 = λ Γ A →
   (Tm64    : Con64 → Ty64 → Set)
   (var   : (Γ : _) (A : _) → Var64 Γ A → Tm64 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B))
   (app   : (Γ : _) (A B : _) → Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B)
 → Tm64 Γ A

var64 : ∀{Γ A} → Var64 Γ A → Tm64 Γ A;var64
 = λ x Tm64 var64 lam app → var64 _ _ x

lam64 : ∀{Γ A B} → Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B);lam64
 = λ t Tm64 var64 lam64 app → lam64 _ _ _ (t Tm64 var64 lam64 app)

app64 : ∀{Γ A B} → Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B;app64
 = λ t u Tm64 var64 lam64 app64 →
     app64 _ _ _ (t Tm64 var64 lam64 app64) (u Tm64 var64 lam64 app64)

v064 : ∀{Γ A} → Tm64 (snoc64 Γ A) A;v064
 = var64 vz64

v164 : ∀{Γ A B} → Tm64 (snoc64 (snoc64 Γ A) B) A;v164
 = var64 (vs64 vz64)

v264 : ∀{Γ A B C} → Tm64 (snoc64 (snoc64 (snoc64 Γ A) B) C) A;v264
 = var64 (vs64 (vs64 vz64))

v364 : ∀{Γ A B C D} → Tm64 (snoc64 (snoc64 (snoc64 (snoc64 Γ A) B) C) D) A;v364
 = var64 (vs64 (vs64 (vs64 vz64)))

v464 : ∀{Γ A B C D E} → Tm64 (snoc64 (snoc64 (snoc64 (snoc64 (snoc64 Γ A) B) C) D) E) A;v464
 = var64 (vs64 (vs64 (vs64 (vs64 vz64))))

test64 : ∀{Γ A} → Tm64 Γ (arr64 (arr64 A A) (arr64 A A));test64
  = lam64 (lam64 (app64 v164 (app64 v164 (app64 v164 (app64 v164 (app64 v164 (app64 v164 v064)))))))
{-# OPTIONS --type-in-type #-}

Ty65 : Set; Ty65
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι65   : Ty65; ι65 = λ _ ι65 _ → ι65
arr65 : Ty65 → Ty65 → Ty65; arr65 = λ A B Ty65 ι65 arr65 → arr65 (A Ty65 ι65 arr65) (B Ty65 ι65 arr65)

Con65 : Set;Con65
 = (Con65 : Set)
   (nil  : Con65)
   (snoc : Con65 → Ty65 → Con65)
 → Con65

nil65 : Con65;nil65
 = λ Con65 nil65 snoc → nil65

snoc65 : Con65 → Ty65 → Con65;snoc65
 = λ Γ A Con65 nil65 snoc65 → snoc65 (Γ Con65 nil65 snoc65) A

Var65 : Con65 → Ty65 → Set;Var65
 = λ Γ A →
   (Var65 : Con65 → Ty65 → Set)
   (vz  : (Γ : _)(A : _) → Var65 (snoc65 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var65 Γ A → Var65 (snoc65 Γ B) A)
 → Var65 Γ A

vz65 : ∀{Γ A} → Var65 (snoc65 Γ A) A;vz65
 = λ Var65 vz65 vs → vz65 _ _

vs65 : ∀{Γ B A} → Var65 Γ A → Var65 (snoc65 Γ B) A;vs65
 = λ x Var65 vz65 vs65 → vs65 _ _ _ (x Var65 vz65 vs65)

Tm65 : Con65 → Ty65 → Set;Tm65
 = λ Γ A →
   (Tm65    : Con65 → Ty65 → Set)
   (var   : (Γ : _) (A : _) → Var65 Γ A → Tm65 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B))
   (app   : (Γ : _) (A B : _) → Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B)
 → Tm65 Γ A

var65 : ∀{Γ A} → Var65 Γ A → Tm65 Γ A;var65
 = λ x Tm65 var65 lam app → var65 _ _ x

lam65 : ∀{Γ A B} → Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B);lam65
 = λ t Tm65 var65 lam65 app → lam65 _ _ _ (t Tm65 var65 lam65 app)

app65 : ∀{Γ A B} → Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B;app65
 = λ t u Tm65 var65 lam65 app65 →
     app65 _ _ _ (t Tm65 var65 lam65 app65) (u Tm65 var65 lam65 app65)

v065 : ∀{Γ A} → Tm65 (snoc65 Γ A) A;v065
 = var65 vz65

v165 : ∀{Γ A B} → Tm65 (snoc65 (snoc65 Γ A) B) A;v165
 = var65 (vs65 vz65)

v265 : ∀{Γ A B C} → Tm65 (snoc65 (snoc65 (snoc65 Γ A) B) C) A;v265
 = var65 (vs65 (vs65 vz65))

v365 : ∀{Γ A B C D} → Tm65 (snoc65 (snoc65 (snoc65 (snoc65 Γ A) B) C) D) A;v365
 = var65 (vs65 (vs65 (vs65 vz65)))

v465 : ∀{Γ A B C D E} → Tm65 (snoc65 (snoc65 (snoc65 (snoc65 (snoc65 Γ A) B) C) D) E) A;v465
 = var65 (vs65 (vs65 (vs65 (vs65 vz65))))

test65 : ∀{Γ A} → Tm65 Γ (arr65 (arr65 A A) (arr65 A A));test65
  = lam65 (lam65 (app65 v165 (app65 v165 (app65 v165 (app65 v165 (app65 v165 (app65 v165 v065)))))))
{-# OPTIONS --type-in-type #-}

Ty66 : Set; Ty66
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι66   : Ty66; ι66 = λ _ ι66 _ → ι66
arr66 : Ty66 → Ty66 → Ty66; arr66 = λ A B Ty66 ι66 arr66 → arr66 (A Ty66 ι66 arr66) (B Ty66 ι66 arr66)

Con66 : Set;Con66
 = (Con66 : Set)
   (nil  : Con66)
   (snoc : Con66 → Ty66 → Con66)
 → Con66

nil66 : Con66;nil66
 = λ Con66 nil66 snoc → nil66

snoc66 : Con66 → Ty66 → Con66;snoc66
 = λ Γ A Con66 nil66 snoc66 → snoc66 (Γ Con66 nil66 snoc66) A

Var66 : Con66 → Ty66 → Set;Var66
 = λ Γ A →
   (Var66 : Con66 → Ty66 → Set)
   (vz  : (Γ : _)(A : _) → Var66 (snoc66 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var66 Γ A → Var66 (snoc66 Γ B) A)
 → Var66 Γ A

vz66 : ∀{Γ A} → Var66 (snoc66 Γ A) A;vz66
 = λ Var66 vz66 vs → vz66 _ _

vs66 : ∀{Γ B A} → Var66 Γ A → Var66 (snoc66 Γ B) A;vs66
 = λ x Var66 vz66 vs66 → vs66 _ _ _ (x Var66 vz66 vs66)

Tm66 : Con66 → Ty66 → Set;Tm66
 = λ Γ A →
   (Tm66    : Con66 → Ty66 → Set)
   (var   : (Γ : _) (A : _) → Var66 Γ A → Tm66 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B))
   (app   : (Γ : _) (A B : _) → Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B)
 → Tm66 Γ A

var66 : ∀{Γ A} → Var66 Γ A → Tm66 Γ A;var66
 = λ x Tm66 var66 lam app → var66 _ _ x

lam66 : ∀{Γ A B} → Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B);lam66
 = λ t Tm66 var66 lam66 app → lam66 _ _ _ (t Tm66 var66 lam66 app)

app66 : ∀{Γ A B} → Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B;app66
 = λ t u Tm66 var66 lam66 app66 →
     app66 _ _ _ (t Tm66 var66 lam66 app66) (u Tm66 var66 lam66 app66)

v066 : ∀{Γ A} → Tm66 (snoc66 Γ A) A;v066
 = var66 vz66

v166 : ∀{Γ A B} → Tm66 (snoc66 (snoc66 Γ A) B) A;v166
 = var66 (vs66 vz66)

v266 : ∀{Γ A B C} → Tm66 (snoc66 (snoc66 (snoc66 Γ A) B) C) A;v266
 = var66 (vs66 (vs66 vz66))

v366 : ∀{Γ A B C D} → Tm66 (snoc66 (snoc66 (snoc66 (snoc66 Γ A) B) C) D) A;v366
 = var66 (vs66 (vs66 (vs66 vz66)))

v466 : ∀{Γ A B C D E} → Tm66 (snoc66 (snoc66 (snoc66 (snoc66 (snoc66 Γ A) B) C) D) E) A;v466
 = var66 (vs66 (vs66 (vs66 (vs66 vz66))))

test66 : ∀{Γ A} → Tm66 Γ (arr66 (arr66 A A) (arr66 A A));test66
  = lam66 (lam66 (app66 v166 (app66 v166 (app66 v166 (app66 v166 (app66 v166 (app66 v166 v066)))))))
{-# OPTIONS --type-in-type #-}

Ty67 : Set; Ty67
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι67   : Ty67; ι67 = λ _ ι67 _ → ι67
arr67 : Ty67 → Ty67 → Ty67; arr67 = λ A B Ty67 ι67 arr67 → arr67 (A Ty67 ι67 arr67) (B Ty67 ι67 arr67)

Con67 : Set;Con67
 = (Con67 : Set)
   (nil  : Con67)
   (snoc : Con67 → Ty67 → Con67)
 → Con67

nil67 : Con67;nil67
 = λ Con67 nil67 snoc → nil67

snoc67 : Con67 → Ty67 → Con67;snoc67
 = λ Γ A Con67 nil67 snoc67 → snoc67 (Γ Con67 nil67 snoc67) A

Var67 : Con67 → Ty67 → Set;Var67
 = λ Γ A →
   (Var67 : Con67 → Ty67 → Set)
   (vz  : (Γ : _)(A : _) → Var67 (snoc67 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var67 Γ A → Var67 (snoc67 Γ B) A)
 → Var67 Γ A

vz67 : ∀{Γ A} → Var67 (snoc67 Γ A) A;vz67
 = λ Var67 vz67 vs → vz67 _ _

vs67 : ∀{Γ B A} → Var67 Γ A → Var67 (snoc67 Γ B) A;vs67
 = λ x Var67 vz67 vs67 → vs67 _ _ _ (x Var67 vz67 vs67)

Tm67 : Con67 → Ty67 → Set;Tm67
 = λ Γ A →
   (Tm67    : Con67 → Ty67 → Set)
   (var   : (Γ : _) (A : _) → Var67 Γ A → Tm67 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B))
   (app   : (Γ : _) (A B : _) → Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B)
 → Tm67 Γ A

var67 : ∀{Γ A} → Var67 Γ A → Tm67 Γ A;var67
 = λ x Tm67 var67 lam app → var67 _ _ x

lam67 : ∀{Γ A B} → Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B);lam67
 = λ t Tm67 var67 lam67 app → lam67 _ _ _ (t Tm67 var67 lam67 app)

app67 : ∀{Γ A B} → Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B;app67
 = λ t u Tm67 var67 lam67 app67 →
     app67 _ _ _ (t Tm67 var67 lam67 app67) (u Tm67 var67 lam67 app67)

v067 : ∀{Γ A} → Tm67 (snoc67 Γ A) A;v067
 = var67 vz67

v167 : ∀{Γ A B} → Tm67 (snoc67 (snoc67 Γ A) B) A;v167
 = var67 (vs67 vz67)

v267 : ∀{Γ A B C} → Tm67 (snoc67 (snoc67 (snoc67 Γ A) B) C) A;v267
 = var67 (vs67 (vs67 vz67))

v367 : ∀{Γ A B C D} → Tm67 (snoc67 (snoc67 (snoc67 (snoc67 Γ A) B) C) D) A;v367
 = var67 (vs67 (vs67 (vs67 vz67)))

v467 : ∀{Γ A B C D E} → Tm67 (snoc67 (snoc67 (snoc67 (snoc67 (snoc67 Γ A) B) C) D) E) A;v467
 = var67 (vs67 (vs67 (vs67 (vs67 vz67))))

test67 : ∀{Γ A} → Tm67 Γ (arr67 (arr67 A A) (arr67 A A));test67
  = lam67 (lam67 (app67 v167 (app67 v167 (app67 v167 (app67 v167 (app67 v167 (app67 v167 v067)))))))
{-# OPTIONS --type-in-type #-}

Ty68 : Set; Ty68
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι68   : Ty68; ι68 = λ _ ι68 _ → ι68
arr68 : Ty68 → Ty68 → Ty68; arr68 = λ A B Ty68 ι68 arr68 → arr68 (A Ty68 ι68 arr68) (B Ty68 ι68 arr68)

Con68 : Set;Con68
 = (Con68 : Set)
   (nil  : Con68)
   (snoc : Con68 → Ty68 → Con68)
 → Con68

nil68 : Con68;nil68
 = λ Con68 nil68 snoc → nil68

snoc68 : Con68 → Ty68 → Con68;snoc68
 = λ Γ A Con68 nil68 snoc68 → snoc68 (Γ Con68 nil68 snoc68) A

Var68 : Con68 → Ty68 → Set;Var68
 = λ Γ A →
   (Var68 : Con68 → Ty68 → Set)
   (vz  : (Γ : _)(A : _) → Var68 (snoc68 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var68 Γ A → Var68 (snoc68 Γ B) A)
 → Var68 Γ A

vz68 : ∀{Γ A} → Var68 (snoc68 Γ A) A;vz68
 = λ Var68 vz68 vs → vz68 _ _

vs68 : ∀{Γ B A} → Var68 Γ A → Var68 (snoc68 Γ B) A;vs68
 = λ x Var68 vz68 vs68 → vs68 _ _ _ (x Var68 vz68 vs68)

Tm68 : Con68 → Ty68 → Set;Tm68
 = λ Γ A →
   (Tm68    : Con68 → Ty68 → Set)
   (var   : (Γ : _) (A : _) → Var68 Γ A → Tm68 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B))
   (app   : (Γ : _) (A B : _) → Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B)
 → Tm68 Γ A

var68 : ∀{Γ A} → Var68 Γ A → Tm68 Γ A;var68
 = λ x Tm68 var68 lam app → var68 _ _ x

lam68 : ∀{Γ A B} → Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B);lam68
 = λ t Tm68 var68 lam68 app → lam68 _ _ _ (t Tm68 var68 lam68 app)

app68 : ∀{Γ A B} → Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B;app68
 = λ t u Tm68 var68 lam68 app68 →
     app68 _ _ _ (t Tm68 var68 lam68 app68) (u Tm68 var68 lam68 app68)

v068 : ∀{Γ A} → Tm68 (snoc68 Γ A) A;v068
 = var68 vz68

v168 : ∀{Γ A B} → Tm68 (snoc68 (snoc68 Γ A) B) A;v168
 = var68 (vs68 vz68)

v268 : ∀{Γ A B C} → Tm68 (snoc68 (snoc68 (snoc68 Γ A) B) C) A;v268
 = var68 (vs68 (vs68 vz68))

v368 : ∀{Γ A B C D} → Tm68 (snoc68 (snoc68 (snoc68 (snoc68 Γ A) B) C) D) A;v368
 = var68 (vs68 (vs68 (vs68 vz68)))

v468 : ∀{Γ A B C D E} → Tm68 (snoc68 (snoc68 (snoc68 (snoc68 (snoc68 Γ A) B) C) D) E) A;v468
 = var68 (vs68 (vs68 (vs68 (vs68 vz68))))

test68 : ∀{Γ A} → Tm68 Γ (arr68 (arr68 A A) (arr68 A A));test68
  = lam68 (lam68 (app68 v168 (app68 v168 (app68 v168 (app68 v168 (app68 v168 (app68 v168 v068)))))))
{-# OPTIONS --type-in-type #-}

Ty69 : Set; Ty69
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι69   : Ty69; ι69 = λ _ ι69 _ → ι69
arr69 : Ty69 → Ty69 → Ty69; arr69 = λ A B Ty69 ι69 arr69 → arr69 (A Ty69 ι69 arr69) (B Ty69 ι69 arr69)

Con69 : Set;Con69
 = (Con69 : Set)
   (nil  : Con69)
   (snoc : Con69 → Ty69 → Con69)
 → Con69

nil69 : Con69;nil69
 = λ Con69 nil69 snoc → nil69

snoc69 : Con69 → Ty69 → Con69;snoc69
 = λ Γ A Con69 nil69 snoc69 → snoc69 (Γ Con69 nil69 snoc69) A

Var69 : Con69 → Ty69 → Set;Var69
 = λ Γ A →
   (Var69 : Con69 → Ty69 → Set)
   (vz  : (Γ : _)(A : _) → Var69 (snoc69 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var69 Γ A → Var69 (snoc69 Γ B) A)
 → Var69 Γ A

vz69 : ∀{Γ A} → Var69 (snoc69 Γ A) A;vz69
 = λ Var69 vz69 vs → vz69 _ _

vs69 : ∀{Γ B A} → Var69 Γ A → Var69 (snoc69 Γ B) A;vs69
 = λ x Var69 vz69 vs69 → vs69 _ _ _ (x Var69 vz69 vs69)

Tm69 : Con69 → Ty69 → Set;Tm69
 = λ Γ A →
   (Tm69    : Con69 → Ty69 → Set)
   (var   : (Γ : _) (A : _) → Var69 Γ A → Tm69 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B))
   (app   : (Γ : _) (A B : _) → Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B)
 → Tm69 Γ A

var69 : ∀{Γ A} → Var69 Γ A → Tm69 Γ A;var69
 = λ x Tm69 var69 lam app → var69 _ _ x

lam69 : ∀{Γ A B} → Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B);lam69
 = λ t Tm69 var69 lam69 app → lam69 _ _ _ (t Tm69 var69 lam69 app)

app69 : ∀{Γ A B} → Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B;app69
 = λ t u Tm69 var69 lam69 app69 →
     app69 _ _ _ (t Tm69 var69 lam69 app69) (u Tm69 var69 lam69 app69)

v069 : ∀{Γ A} → Tm69 (snoc69 Γ A) A;v069
 = var69 vz69

v169 : ∀{Γ A B} → Tm69 (snoc69 (snoc69 Γ A) B) A;v169
 = var69 (vs69 vz69)

v269 : ∀{Γ A B C} → Tm69 (snoc69 (snoc69 (snoc69 Γ A) B) C) A;v269
 = var69 (vs69 (vs69 vz69))

v369 : ∀{Γ A B C D} → Tm69 (snoc69 (snoc69 (snoc69 (snoc69 Γ A) B) C) D) A;v369
 = var69 (vs69 (vs69 (vs69 vz69)))

v469 : ∀{Γ A B C D E} → Tm69 (snoc69 (snoc69 (snoc69 (snoc69 (snoc69 Γ A) B) C) D) E) A;v469
 = var69 (vs69 (vs69 (vs69 (vs69 vz69))))

test69 : ∀{Γ A} → Tm69 Γ (arr69 (arr69 A A) (arr69 A A));test69
  = lam69 (lam69 (app69 v169 (app69 v169 (app69 v169 (app69 v169 (app69 v169 (app69 v169 v069)))))))
{-# OPTIONS --type-in-type #-}

Ty70 : Set; Ty70
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι70   : Ty70; ι70 = λ _ ι70 _ → ι70
arr70 : Ty70 → Ty70 → Ty70; arr70 = λ A B Ty70 ι70 arr70 → arr70 (A Ty70 ι70 arr70) (B Ty70 ι70 arr70)

Con70 : Set;Con70
 = (Con70 : Set)
   (nil  : Con70)
   (snoc : Con70 → Ty70 → Con70)
 → Con70

nil70 : Con70;nil70
 = λ Con70 nil70 snoc → nil70

snoc70 : Con70 → Ty70 → Con70;snoc70
 = λ Γ A Con70 nil70 snoc70 → snoc70 (Γ Con70 nil70 snoc70) A

Var70 : Con70 → Ty70 → Set;Var70
 = λ Γ A →
   (Var70 : Con70 → Ty70 → Set)
   (vz  : (Γ : _)(A : _) → Var70 (snoc70 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var70 Γ A → Var70 (snoc70 Γ B) A)
 → Var70 Γ A

vz70 : ∀{Γ A} → Var70 (snoc70 Γ A) A;vz70
 = λ Var70 vz70 vs → vz70 _ _

vs70 : ∀{Γ B A} → Var70 Γ A → Var70 (snoc70 Γ B) A;vs70
 = λ x Var70 vz70 vs70 → vs70 _ _ _ (x Var70 vz70 vs70)

Tm70 : Con70 → Ty70 → Set;Tm70
 = λ Γ A →
   (Tm70    : Con70 → Ty70 → Set)
   (var   : (Γ : _) (A : _) → Var70 Γ A → Tm70 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B))
   (app   : (Γ : _) (A B : _) → Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B)
 → Tm70 Γ A

var70 : ∀{Γ A} → Var70 Γ A → Tm70 Γ A;var70
 = λ x Tm70 var70 lam app → var70 _ _ x

lam70 : ∀{Γ A B} → Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B);lam70
 = λ t Tm70 var70 lam70 app → lam70 _ _ _ (t Tm70 var70 lam70 app)

app70 : ∀{Γ A B} → Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B;app70
 = λ t u Tm70 var70 lam70 app70 →
     app70 _ _ _ (t Tm70 var70 lam70 app70) (u Tm70 var70 lam70 app70)

v070 : ∀{Γ A} → Tm70 (snoc70 Γ A) A;v070
 = var70 vz70

v170 : ∀{Γ A B} → Tm70 (snoc70 (snoc70 Γ A) B) A;v170
 = var70 (vs70 vz70)

v270 : ∀{Γ A B C} → Tm70 (snoc70 (snoc70 (snoc70 Γ A) B) C) A;v270
 = var70 (vs70 (vs70 vz70))

v370 : ∀{Γ A B C D} → Tm70 (snoc70 (snoc70 (snoc70 (snoc70 Γ A) B) C) D) A;v370
 = var70 (vs70 (vs70 (vs70 vz70)))

v470 : ∀{Γ A B C D E} → Tm70 (snoc70 (snoc70 (snoc70 (snoc70 (snoc70 Γ A) B) C) D) E) A;v470
 = var70 (vs70 (vs70 (vs70 (vs70 vz70))))

test70 : ∀{Γ A} → Tm70 Γ (arr70 (arr70 A A) (arr70 A A));test70
  = lam70 (lam70 (app70 v170 (app70 v170 (app70 v170 (app70 v170 (app70 v170 (app70 v170 v070)))))))
{-# OPTIONS --type-in-type #-}

Ty71 : Set; Ty71
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι71   : Ty71; ι71 = λ _ ι71 _ → ι71
arr71 : Ty71 → Ty71 → Ty71; arr71 = λ A B Ty71 ι71 arr71 → arr71 (A Ty71 ι71 arr71) (B Ty71 ι71 arr71)

Con71 : Set;Con71
 = (Con71 : Set)
   (nil  : Con71)
   (snoc : Con71 → Ty71 → Con71)
 → Con71

nil71 : Con71;nil71
 = λ Con71 nil71 snoc → nil71

snoc71 : Con71 → Ty71 → Con71;snoc71
 = λ Γ A Con71 nil71 snoc71 → snoc71 (Γ Con71 nil71 snoc71) A

Var71 : Con71 → Ty71 → Set;Var71
 = λ Γ A →
   (Var71 : Con71 → Ty71 → Set)
   (vz  : (Γ : _)(A : _) → Var71 (snoc71 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var71 Γ A → Var71 (snoc71 Γ B) A)
 → Var71 Γ A

vz71 : ∀{Γ A} → Var71 (snoc71 Γ A) A;vz71
 = λ Var71 vz71 vs → vz71 _ _

vs71 : ∀{Γ B A} → Var71 Γ A → Var71 (snoc71 Γ B) A;vs71
 = λ x Var71 vz71 vs71 → vs71 _ _ _ (x Var71 vz71 vs71)

Tm71 : Con71 → Ty71 → Set;Tm71
 = λ Γ A →
   (Tm71    : Con71 → Ty71 → Set)
   (var   : (Γ : _) (A : _) → Var71 Γ A → Tm71 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B))
   (app   : (Γ : _) (A B : _) → Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B)
 → Tm71 Γ A

var71 : ∀{Γ A} → Var71 Γ A → Tm71 Γ A;var71
 = λ x Tm71 var71 lam app → var71 _ _ x

lam71 : ∀{Γ A B} → Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B);lam71
 = λ t Tm71 var71 lam71 app → lam71 _ _ _ (t Tm71 var71 lam71 app)

app71 : ∀{Γ A B} → Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B;app71
 = λ t u Tm71 var71 lam71 app71 →
     app71 _ _ _ (t Tm71 var71 lam71 app71) (u Tm71 var71 lam71 app71)

v071 : ∀{Γ A} → Tm71 (snoc71 Γ A) A;v071
 = var71 vz71

v171 : ∀{Γ A B} → Tm71 (snoc71 (snoc71 Γ A) B) A;v171
 = var71 (vs71 vz71)

v271 : ∀{Γ A B C} → Tm71 (snoc71 (snoc71 (snoc71 Γ A) B) C) A;v271
 = var71 (vs71 (vs71 vz71))

v371 : ∀{Γ A B C D} → Tm71 (snoc71 (snoc71 (snoc71 (snoc71 Γ A) B) C) D) A;v371
 = var71 (vs71 (vs71 (vs71 vz71)))

v471 : ∀{Γ A B C D E} → Tm71 (snoc71 (snoc71 (snoc71 (snoc71 (snoc71 Γ A) B) C) D) E) A;v471
 = var71 (vs71 (vs71 (vs71 (vs71 vz71))))

test71 : ∀{Γ A} → Tm71 Γ (arr71 (arr71 A A) (arr71 A A));test71
  = lam71 (lam71 (app71 v171 (app71 v171 (app71 v171 (app71 v171 (app71 v171 (app71 v171 v071)))))))
{-# OPTIONS --type-in-type #-}

Ty72 : Set; Ty72
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι72   : Ty72; ι72 = λ _ ι72 _ → ι72
arr72 : Ty72 → Ty72 → Ty72; arr72 = λ A B Ty72 ι72 arr72 → arr72 (A Ty72 ι72 arr72) (B Ty72 ι72 arr72)

Con72 : Set;Con72
 = (Con72 : Set)
   (nil  : Con72)
   (snoc : Con72 → Ty72 → Con72)
 → Con72

nil72 : Con72;nil72
 = λ Con72 nil72 snoc → nil72

snoc72 : Con72 → Ty72 → Con72;snoc72
 = λ Γ A Con72 nil72 snoc72 → snoc72 (Γ Con72 nil72 snoc72) A

Var72 : Con72 → Ty72 → Set;Var72
 = λ Γ A →
   (Var72 : Con72 → Ty72 → Set)
   (vz  : (Γ : _)(A : _) → Var72 (snoc72 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var72 Γ A → Var72 (snoc72 Γ B) A)
 → Var72 Γ A

vz72 : ∀{Γ A} → Var72 (snoc72 Γ A) A;vz72
 = λ Var72 vz72 vs → vz72 _ _

vs72 : ∀{Γ B A} → Var72 Γ A → Var72 (snoc72 Γ B) A;vs72
 = λ x Var72 vz72 vs72 → vs72 _ _ _ (x Var72 vz72 vs72)

Tm72 : Con72 → Ty72 → Set;Tm72
 = λ Γ A →
   (Tm72    : Con72 → Ty72 → Set)
   (var   : (Γ : _) (A : _) → Var72 Γ A → Tm72 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B))
   (app   : (Γ : _) (A B : _) → Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B)
 → Tm72 Γ A

var72 : ∀{Γ A} → Var72 Γ A → Tm72 Γ A;var72
 = λ x Tm72 var72 lam app → var72 _ _ x

lam72 : ∀{Γ A B} → Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B);lam72
 = λ t Tm72 var72 lam72 app → lam72 _ _ _ (t Tm72 var72 lam72 app)

app72 : ∀{Γ A B} → Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B;app72
 = λ t u Tm72 var72 lam72 app72 →
     app72 _ _ _ (t Tm72 var72 lam72 app72) (u Tm72 var72 lam72 app72)

v072 : ∀{Γ A} → Tm72 (snoc72 Γ A) A;v072
 = var72 vz72

v172 : ∀{Γ A B} → Tm72 (snoc72 (snoc72 Γ A) B) A;v172
 = var72 (vs72 vz72)

v272 : ∀{Γ A B C} → Tm72 (snoc72 (snoc72 (snoc72 Γ A) B) C) A;v272
 = var72 (vs72 (vs72 vz72))

v372 : ∀{Γ A B C D} → Tm72 (snoc72 (snoc72 (snoc72 (snoc72 Γ A) B) C) D) A;v372
 = var72 (vs72 (vs72 (vs72 vz72)))

v472 : ∀{Γ A B C D E} → Tm72 (snoc72 (snoc72 (snoc72 (snoc72 (snoc72 Γ A) B) C) D) E) A;v472
 = var72 (vs72 (vs72 (vs72 (vs72 vz72))))

test72 : ∀{Γ A} → Tm72 Γ (arr72 (arr72 A A) (arr72 A A));test72
  = lam72 (lam72 (app72 v172 (app72 v172 (app72 v172 (app72 v172 (app72 v172 (app72 v172 v072)))))))
{-# OPTIONS --type-in-type #-}

Ty73 : Set; Ty73
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι73   : Ty73; ι73 = λ _ ι73 _ → ι73
arr73 : Ty73 → Ty73 → Ty73; arr73 = λ A B Ty73 ι73 arr73 → arr73 (A Ty73 ι73 arr73) (B Ty73 ι73 arr73)

Con73 : Set;Con73
 = (Con73 : Set)
   (nil  : Con73)
   (snoc : Con73 → Ty73 → Con73)
 → Con73

nil73 : Con73;nil73
 = λ Con73 nil73 snoc → nil73

snoc73 : Con73 → Ty73 → Con73;snoc73
 = λ Γ A Con73 nil73 snoc73 → snoc73 (Γ Con73 nil73 snoc73) A

Var73 : Con73 → Ty73 → Set;Var73
 = λ Γ A →
   (Var73 : Con73 → Ty73 → Set)
   (vz  : (Γ : _)(A : _) → Var73 (snoc73 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var73 Γ A → Var73 (snoc73 Γ B) A)
 → Var73 Γ A

vz73 : ∀{Γ A} → Var73 (snoc73 Γ A) A;vz73
 = λ Var73 vz73 vs → vz73 _ _

vs73 : ∀{Γ B A} → Var73 Γ A → Var73 (snoc73 Γ B) A;vs73
 = λ x Var73 vz73 vs73 → vs73 _ _ _ (x Var73 vz73 vs73)

Tm73 : Con73 → Ty73 → Set;Tm73
 = λ Γ A →
   (Tm73    : Con73 → Ty73 → Set)
   (var   : (Γ : _) (A : _) → Var73 Γ A → Tm73 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B))
   (app   : (Γ : _) (A B : _) → Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B)
 → Tm73 Γ A

var73 : ∀{Γ A} → Var73 Γ A → Tm73 Γ A;var73
 = λ x Tm73 var73 lam app → var73 _ _ x

lam73 : ∀{Γ A B} → Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B);lam73
 = λ t Tm73 var73 lam73 app → lam73 _ _ _ (t Tm73 var73 lam73 app)

app73 : ∀{Γ A B} → Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B;app73
 = λ t u Tm73 var73 lam73 app73 →
     app73 _ _ _ (t Tm73 var73 lam73 app73) (u Tm73 var73 lam73 app73)

v073 : ∀{Γ A} → Tm73 (snoc73 Γ A) A;v073
 = var73 vz73

v173 : ∀{Γ A B} → Tm73 (snoc73 (snoc73 Γ A) B) A;v173
 = var73 (vs73 vz73)

v273 : ∀{Γ A B C} → Tm73 (snoc73 (snoc73 (snoc73 Γ A) B) C) A;v273
 = var73 (vs73 (vs73 vz73))

v373 : ∀{Γ A B C D} → Tm73 (snoc73 (snoc73 (snoc73 (snoc73 Γ A) B) C) D) A;v373
 = var73 (vs73 (vs73 (vs73 vz73)))

v473 : ∀{Γ A B C D E} → Tm73 (snoc73 (snoc73 (snoc73 (snoc73 (snoc73 Γ A) B) C) D) E) A;v473
 = var73 (vs73 (vs73 (vs73 (vs73 vz73))))

test73 : ∀{Γ A} → Tm73 Γ (arr73 (arr73 A A) (arr73 A A));test73
  = lam73 (lam73 (app73 v173 (app73 v173 (app73 v173 (app73 v173 (app73 v173 (app73 v173 v073)))))))
{-# OPTIONS --type-in-type #-}

Ty74 : Set; Ty74
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι74   : Ty74; ι74 = λ _ ι74 _ → ι74
arr74 : Ty74 → Ty74 → Ty74; arr74 = λ A B Ty74 ι74 arr74 → arr74 (A Ty74 ι74 arr74) (B Ty74 ι74 arr74)

Con74 : Set;Con74
 = (Con74 : Set)
   (nil  : Con74)
   (snoc : Con74 → Ty74 → Con74)
 → Con74

nil74 : Con74;nil74
 = λ Con74 nil74 snoc → nil74

snoc74 : Con74 → Ty74 → Con74;snoc74
 = λ Γ A Con74 nil74 snoc74 → snoc74 (Γ Con74 nil74 snoc74) A

Var74 : Con74 → Ty74 → Set;Var74
 = λ Γ A →
   (Var74 : Con74 → Ty74 → Set)
   (vz  : (Γ : _)(A : _) → Var74 (snoc74 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var74 Γ A → Var74 (snoc74 Γ B) A)
 → Var74 Γ A

vz74 : ∀{Γ A} → Var74 (snoc74 Γ A) A;vz74
 = λ Var74 vz74 vs → vz74 _ _

vs74 : ∀{Γ B A} → Var74 Γ A → Var74 (snoc74 Γ B) A;vs74
 = λ x Var74 vz74 vs74 → vs74 _ _ _ (x Var74 vz74 vs74)

Tm74 : Con74 → Ty74 → Set;Tm74
 = λ Γ A →
   (Tm74    : Con74 → Ty74 → Set)
   (var   : (Γ : _) (A : _) → Var74 Γ A → Tm74 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B))
   (app   : (Γ : _) (A B : _) → Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B)
 → Tm74 Γ A

var74 : ∀{Γ A} → Var74 Γ A → Tm74 Γ A;var74
 = λ x Tm74 var74 lam app → var74 _ _ x

lam74 : ∀{Γ A B} → Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B);lam74
 = λ t Tm74 var74 lam74 app → lam74 _ _ _ (t Tm74 var74 lam74 app)

app74 : ∀{Γ A B} → Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B;app74
 = λ t u Tm74 var74 lam74 app74 →
     app74 _ _ _ (t Tm74 var74 lam74 app74) (u Tm74 var74 lam74 app74)

v074 : ∀{Γ A} → Tm74 (snoc74 Γ A) A;v074
 = var74 vz74

v174 : ∀{Γ A B} → Tm74 (snoc74 (snoc74 Γ A) B) A;v174
 = var74 (vs74 vz74)

v274 : ∀{Γ A B C} → Tm74 (snoc74 (snoc74 (snoc74 Γ A) B) C) A;v274
 = var74 (vs74 (vs74 vz74))

v374 : ∀{Γ A B C D} → Tm74 (snoc74 (snoc74 (snoc74 (snoc74 Γ A) B) C) D) A;v374
 = var74 (vs74 (vs74 (vs74 vz74)))

v474 : ∀{Γ A B C D E} → Tm74 (snoc74 (snoc74 (snoc74 (snoc74 (snoc74 Γ A) B) C) D) E) A;v474
 = var74 (vs74 (vs74 (vs74 (vs74 vz74))))

test74 : ∀{Γ A} → Tm74 Γ (arr74 (arr74 A A) (arr74 A A));test74
  = lam74 (lam74 (app74 v174 (app74 v174 (app74 v174 (app74 v174 (app74 v174 (app74 v174 v074)))))))
{-# OPTIONS --type-in-type #-}

Ty75 : Set; Ty75
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι75   : Ty75; ι75 = λ _ ι75 _ → ι75
arr75 : Ty75 → Ty75 → Ty75; arr75 = λ A B Ty75 ι75 arr75 → arr75 (A Ty75 ι75 arr75) (B Ty75 ι75 arr75)

Con75 : Set;Con75
 = (Con75 : Set)
   (nil  : Con75)
   (snoc : Con75 → Ty75 → Con75)
 → Con75

nil75 : Con75;nil75
 = λ Con75 nil75 snoc → nil75

snoc75 : Con75 → Ty75 → Con75;snoc75
 = λ Γ A Con75 nil75 snoc75 → snoc75 (Γ Con75 nil75 snoc75) A

Var75 : Con75 → Ty75 → Set;Var75
 = λ Γ A →
   (Var75 : Con75 → Ty75 → Set)
   (vz  : (Γ : _)(A : _) → Var75 (snoc75 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var75 Γ A → Var75 (snoc75 Γ B) A)
 → Var75 Γ A

vz75 : ∀{Γ A} → Var75 (snoc75 Γ A) A;vz75
 = λ Var75 vz75 vs → vz75 _ _

vs75 : ∀{Γ B A} → Var75 Γ A → Var75 (snoc75 Γ B) A;vs75
 = λ x Var75 vz75 vs75 → vs75 _ _ _ (x Var75 vz75 vs75)

Tm75 : Con75 → Ty75 → Set;Tm75
 = λ Γ A →
   (Tm75    : Con75 → Ty75 → Set)
   (var   : (Γ : _) (A : _) → Var75 Γ A → Tm75 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B))
   (app   : (Γ : _) (A B : _) → Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B)
 → Tm75 Γ A

var75 : ∀{Γ A} → Var75 Γ A → Tm75 Γ A;var75
 = λ x Tm75 var75 lam app → var75 _ _ x

lam75 : ∀{Γ A B} → Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B);lam75
 = λ t Tm75 var75 lam75 app → lam75 _ _ _ (t Tm75 var75 lam75 app)

app75 : ∀{Γ A B} → Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B;app75
 = λ t u Tm75 var75 lam75 app75 →
     app75 _ _ _ (t Tm75 var75 lam75 app75) (u Tm75 var75 lam75 app75)

v075 : ∀{Γ A} → Tm75 (snoc75 Γ A) A;v075
 = var75 vz75

v175 : ∀{Γ A B} → Tm75 (snoc75 (snoc75 Γ A) B) A;v175
 = var75 (vs75 vz75)

v275 : ∀{Γ A B C} → Tm75 (snoc75 (snoc75 (snoc75 Γ A) B) C) A;v275
 = var75 (vs75 (vs75 vz75))

v375 : ∀{Γ A B C D} → Tm75 (snoc75 (snoc75 (snoc75 (snoc75 Γ A) B) C) D) A;v375
 = var75 (vs75 (vs75 (vs75 vz75)))

v475 : ∀{Γ A B C D E} → Tm75 (snoc75 (snoc75 (snoc75 (snoc75 (snoc75 Γ A) B) C) D) E) A;v475
 = var75 (vs75 (vs75 (vs75 (vs75 vz75))))

test75 : ∀{Γ A} → Tm75 Γ (arr75 (arr75 A A) (arr75 A A));test75
  = lam75 (lam75 (app75 v175 (app75 v175 (app75 v175 (app75 v175 (app75 v175 (app75 v175 v075)))))))
{-# OPTIONS --type-in-type #-}

Ty76 : Set; Ty76
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι76   : Ty76; ι76 = λ _ ι76 _ → ι76
arr76 : Ty76 → Ty76 → Ty76; arr76 = λ A B Ty76 ι76 arr76 → arr76 (A Ty76 ι76 arr76) (B Ty76 ι76 arr76)

Con76 : Set;Con76
 = (Con76 : Set)
   (nil  : Con76)
   (snoc : Con76 → Ty76 → Con76)
 → Con76

nil76 : Con76;nil76
 = λ Con76 nil76 snoc → nil76

snoc76 : Con76 → Ty76 → Con76;snoc76
 = λ Γ A Con76 nil76 snoc76 → snoc76 (Γ Con76 nil76 snoc76) A

Var76 : Con76 → Ty76 → Set;Var76
 = λ Γ A →
   (Var76 : Con76 → Ty76 → Set)
   (vz  : (Γ : _)(A : _) → Var76 (snoc76 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var76 Γ A → Var76 (snoc76 Γ B) A)
 → Var76 Γ A

vz76 : ∀{Γ A} → Var76 (snoc76 Γ A) A;vz76
 = λ Var76 vz76 vs → vz76 _ _

vs76 : ∀{Γ B A} → Var76 Γ A → Var76 (snoc76 Γ B) A;vs76
 = λ x Var76 vz76 vs76 → vs76 _ _ _ (x Var76 vz76 vs76)

Tm76 : Con76 → Ty76 → Set;Tm76
 = λ Γ A →
   (Tm76    : Con76 → Ty76 → Set)
   (var   : (Γ : _) (A : _) → Var76 Γ A → Tm76 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B))
   (app   : (Γ : _) (A B : _) → Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B)
 → Tm76 Γ A

var76 : ∀{Γ A} → Var76 Γ A → Tm76 Γ A;var76
 = λ x Tm76 var76 lam app → var76 _ _ x

lam76 : ∀{Γ A B} → Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B);lam76
 = λ t Tm76 var76 lam76 app → lam76 _ _ _ (t Tm76 var76 lam76 app)

app76 : ∀{Γ A B} → Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B;app76
 = λ t u Tm76 var76 lam76 app76 →
     app76 _ _ _ (t Tm76 var76 lam76 app76) (u Tm76 var76 lam76 app76)

v076 : ∀{Γ A} → Tm76 (snoc76 Γ A) A;v076
 = var76 vz76

v176 : ∀{Γ A B} → Tm76 (snoc76 (snoc76 Γ A) B) A;v176
 = var76 (vs76 vz76)

v276 : ∀{Γ A B C} → Tm76 (snoc76 (snoc76 (snoc76 Γ A) B) C) A;v276
 = var76 (vs76 (vs76 vz76))

v376 : ∀{Γ A B C D} → Tm76 (snoc76 (snoc76 (snoc76 (snoc76 Γ A) B) C) D) A;v376
 = var76 (vs76 (vs76 (vs76 vz76)))

v476 : ∀{Γ A B C D E} → Tm76 (snoc76 (snoc76 (snoc76 (snoc76 (snoc76 Γ A) B) C) D) E) A;v476
 = var76 (vs76 (vs76 (vs76 (vs76 vz76))))

test76 : ∀{Γ A} → Tm76 Γ (arr76 (arr76 A A) (arr76 A A));test76
  = lam76 (lam76 (app76 v176 (app76 v176 (app76 v176 (app76 v176 (app76 v176 (app76 v176 v076)))))))
{-# OPTIONS --type-in-type #-}

Ty77 : Set; Ty77
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι77   : Ty77; ι77 = λ _ ι77 _ → ι77
arr77 : Ty77 → Ty77 → Ty77; arr77 = λ A B Ty77 ι77 arr77 → arr77 (A Ty77 ι77 arr77) (B Ty77 ι77 arr77)

Con77 : Set;Con77
 = (Con77 : Set)
   (nil  : Con77)
   (snoc : Con77 → Ty77 → Con77)
 → Con77

nil77 : Con77;nil77
 = λ Con77 nil77 snoc → nil77

snoc77 : Con77 → Ty77 → Con77;snoc77
 = λ Γ A Con77 nil77 snoc77 → snoc77 (Γ Con77 nil77 snoc77) A

Var77 : Con77 → Ty77 → Set;Var77
 = λ Γ A →
   (Var77 : Con77 → Ty77 → Set)
   (vz  : (Γ : _)(A : _) → Var77 (snoc77 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var77 Γ A → Var77 (snoc77 Γ B) A)
 → Var77 Γ A

vz77 : ∀{Γ A} → Var77 (snoc77 Γ A) A;vz77
 = λ Var77 vz77 vs → vz77 _ _

vs77 : ∀{Γ B A} → Var77 Γ A → Var77 (snoc77 Γ B) A;vs77
 = λ x Var77 vz77 vs77 → vs77 _ _ _ (x Var77 vz77 vs77)

Tm77 : Con77 → Ty77 → Set;Tm77
 = λ Γ A →
   (Tm77    : Con77 → Ty77 → Set)
   (var   : (Γ : _) (A : _) → Var77 Γ A → Tm77 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B))
   (app   : (Γ : _) (A B : _) → Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B)
 → Tm77 Γ A

var77 : ∀{Γ A} → Var77 Γ A → Tm77 Γ A;var77
 = λ x Tm77 var77 lam app → var77 _ _ x

lam77 : ∀{Γ A B} → Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B);lam77
 = λ t Tm77 var77 lam77 app → lam77 _ _ _ (t Tm77 var77 lam77 app)

app77 : ∀{Γ A B} → Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B;app77
 = λ t u Tm77 var77 lam77 app77 →
     app77 _ _ _ (t Tm77 var77 lam77 app77) (u Tm77 var77 lam77 app77)

v077 : ∀{Γ A} → Tm77 (snoc77 Γ A) A;v077
 = var77 vz77

v177 : ∀{Γ A B} → Tm77 (snoc77 (snoc77 Γ A) B) A;v177
 = var77 (vs77 vz77)

v277 : ∀{Γ A B C} → Tm77 (snoc77 (snoc77 (snoc77 Γ A) B) C) A;v277
 = var77 (vs77 (vs77 vz77))

v377 : ∀{Γ A B C D} → Tm77 (snoc77 (snoc77 (snoc77 (snoc77 Γ A) B) C) D) A;v377
 = var77 (vs77 (vs77 (vs77 vz77)))

v477 : ∀{Γ A B C D E} → Tm77 (snoc77 (snoc77 (snoc77 (snoc77 (snoc77 Γ A) B) C) D) E) A;v477
 = var77 (vs77 (vs77 (vs77 (vs77 vz77))))

test77 : ∀{Γ A} → Tm77 Γ (arr77 (arr77 A A) (arr77 A A));test77
  = lam77 (lam77 (app77 v177 (app77 v177 (app77 v177 (app77 v177 (app77 v177 (app77 v177 v077)))))))
{-# OPTIONS --type-in-type #-}

Ty78 : Set; Ty78
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι78   : Ty78; ι78 = λ _ ι78 _ → ι78
arr78 : Ty78 → Ty78 → Ty78; arr78 = λ A B Ty78 ι78 arr78 → arr78 (A Ty78 ι78 arr78) (B Ty78 ι78 arr78)

Con78 : Set;Con78
 = (Con78 : Set)
   (nil  : Con78)
   (snoc : Con78 → Ty78 → Con78)
 → Con78

nil78 : Con78;nil78
 = λ Con78 nil78 snoc → nil78

snoc78 : Con78 → Ty78 → Con78;snoc78
 = λ Γ A Con78 nil78 snoc78 → snoc78 (Γ Con78 nil78 snoc78) A

Var78 : Con78 → Ty78 → Set;Var78
 = λ Γ A →
   (Var78 : Con78 → Ty78 → Set)
   (vz  : (Γ : _)(A : _) → Var78 (snoc78 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var78 Γ A → Var78 (snoc78 Γ B) A)
 → Var78 Γ A

vz78 : ∀{Γ A} → Var78 (snoc78 Γ A) A;vz78
 = λ Var78 vz78 vs → vz78 _ _

vs78 : ∀{Γ B A} → Var78 Γ A → Var78 (snoc78 Γ B) A;vs78
 = λ x Var78 vz78 vs78 → vs78 _ _ _ (x Var78 vz78 vs78)

Tm78 : Con78 → Ty78 → Set;Tm78
 = λ Γ A →
   (Tm78    : Con78 → Ty78 → Set)
   (var   : (Γ : _) (A : _) → Var78 Γ A → Tm78 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B))
   (app   : (Γ : _) (A B : _) → Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B)
 → Tm78 Γ A

var78 : ∀{Γ A} → Var78 Γ A → Tm78 Γ A;var78
 = λ x Tm78 var78 lam app → var78 _ _ x

lam78 : ∀{Γ A B} → Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B);lam78
 = λ t Tm78 var78 lam78 app → lam78 _ _ _ (t Tm78 var78 lam78 app)

app78 : ∀{Γ A B} → Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B;app78
 = λ t u Tm78 var78 lam78 app78 →
     app78 _ _ _ (t Tm78 var78 lam78 app78) (u Tm78 var78 lam78 app78)

v078 : ∀{Γ A} → Tm78 (snoc78 Γ A) A;v078
 = var78 vz78

v178 : ∀{Γ A B} → Tm78 (snoc78 (snoc78 Γ A) B) A;v178
 = var78 (vs78 vz78)

v278 : ∀{Γ A B C} → Tm78 (snoc78 (snoc78 (snoc78 Γ A) B) C) A;v278
 = var78 (vs78 (vs78 vz78))

v378 : ∀{Γ A B C D} → Tm78 (snoc78 (snoc78 (snoc78 (snoc78 Γ A) B) C) D) A;v378
 = var78 (vs78 (vs78 (vs78 vz78)))

v478 : ∀{Γ A B C D E} → Tm78 (snoc78 (snoc78 (snoc78 (snoc78 (snoc78 Γ A) B) C) D) E) A;v478
 = var78 (vs78 (vs78 (vs78 (vs78 vz78))))

test78 : ∀{Γ A} → Tm78 Γ (arr78 (arr78 A A) (arr78 A A));test78
  = lam78 (lam78 (app78 v178 (app78 v178 (app78 v178 (app78 v178 (app78 v178 (app78 v178 v078)))))))
{-# OPTIONS --type-in-type #-}

Ty79 : Set; Ty79
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι79   : Ty79; ι79 = λ _ ι79 _ → ι79
arr79 : Ty79 → Ty79 → Ty79; arr79 = λ A B Ty79 ι79 arr79 → arr79 (A Ty79 ι79 arr79) (B Ty79 ι79 arr79)

Con79 : Set;Con79
 = (Con79 : Set)
   (nil  : Con79)
   (snoc : Con79 → Ty79 → Con79)
 → Con79

nil79 : Con79;nil79
 = λ Con79 nil79 snoc → nil79

snoc79 : Con79 → Ty79 → Con79;snoc79
 = λ Γ A Con79 nil79 snoc79 → snoc79 (Γ Con79 nil79 snoc79) A

Var79 : Con79 → Ty79 → Set;Var79
 = λ Γ A →
   (Var79 : Con79 → Ty79 → Set)
   (vz  : (Γ : _)(A : _) → Var79 (snoc79 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var79 Γ A → Var79 (snoc79 Γ B) A)
 → Var79 Γ A

vz79 : ∀{Γ A} → Var79 (snoc79 Γ A) A;vz79
 = λ Var79 vz79 vs → vz79 _ _

vs79 : ∀{Γ B A} → Var79 Γ A → Var79 (snoc79 Γ B) A;vs79
 = λ x Var79 vz79 vs79 → vs79 _ _ _ (x Var79 vz79 vs79)

Tm79 : Con79 → Ty79 → Set;Tm79
 = λ Γ A →
   (Tm79    : Con79 → Ty79 → Set)
   (var   : (Γ : _) (A : _) → Var79 Γ A → Tm79 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B))
   (app   : (Γ : _) (A B : _) → Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B)
 → Tm79 Γ A

var79 : ∀{Γ A} → Var79 Γ A → Tm79 Γ A;var79
 = λ x Tm79 var79 lam app → var79 _ _ x

lam79 : ∀{Γ A B} → Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B);lam79
 = λ t Tm79 var79 lam79 app → lam79 _ _ _ (t Tm79 var79 lam79 app)

app79 : ∀{Γ A B} → Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B;app79
 = λ t u Tm79 var79 lam79 app79 →
     app79 _ _ _ (t Tm79 var79 lam79 app79) (u Tm79 var79 lam79 app79)

v079 : ∀{Γ A} → Tm79 (snoc79 Γ A) A;v079
 = var79 vz79

v179 : ∀{Γ A B} → Tm79 (snoc79 (snoc79 Γ A) B) A;v179
 = var79 (vs79 vz79)

v279 : ∀{Γ A B C} → Tm79 (snoc79 (snoc79 (snoc79 Γ A) B) C) A;v279
 = var79 (vs79 (vs79 vz79))

v379 : ∀{Γ A B C D} → Tm79 (snoc79 (snoc79 (snoc79 (snoc79 Γ A) B) C) D) A;v379
 = var79 (vs79 (vs79 (vs79 vz79)))

v479 : ∀{Γ A B C D E} → Tm79 (snoc79 (snoc79 (snoc79 (snoc79 (snoc79 Γ A) B) C) D) E) A;v479
 = var79 (vs79 (vs79 (vs79 (vs79 vz79))))

test79 : ∀{Γ A} → Tm79 Γ (arr79 (arr79 A A) (arr79 A A));test79
  = lam79 (lam79 (app79 v179 (app79 v179 (app79 v179 (app79 v179 (app79 v179 (app79 v179 v079)))))))
{-# OPTIONS --type-in-type #-}

Ty80 : Set; Ty80
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι80   : Ty80; ι80 = λ _ ι80 _ → ι80
arr80 : Ty80 → Ty80 → Ty80; arr80 = λ A B Ty80 ι80 arr80 → arr80 (A Ty80 ι80 arr80) (B Ty80 ι80 arr80)

Con80 : Set;Con80
 = (Con80 : Set)
   (nil  : Con80)
   (snoc : Con80 → Ty80 → Con80)
 → Con80

nil80 : Con80;nil80
 = λ Con80 nil80 snoc → nil80

snoc80 : Con80 → Ty80 → Con80;snoc80
 = λ Γ A Con80 nil80 snoc80 → snoc80 (Γ Con80 nil80 snoc80) A

Var80 : Con80 → Ty80 → Set;Var80
 = λ Γ A →
   (Var80 : Con80 → Ty80 → Set)
   (vz  : (Γ : _)(A : _) → Var80 (snoc80 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var80 Γ A → Var80 (snoc80 Γ B) A)
 → Var80 Γ A

vz80 : ∀{Γ A} → Var80 (snoc80 Γ A) A;vz80
 = λ Var80 vz80 vs → vz80 _ _

vs80 : ∀{Γ B A} → Var80 Γ A → Var80 (snoc80 Γ B) A;vs80
 = λ x Var80 vz80 vs80 → vs80 _ _ _ (x Var80 vz80 vs80)

Tm80 : Con80 → Ty80 → Set;Tm80
 = λ Γ A →
   (Tm80    : Con80 → Ty80 → Set)
   (var   : (Γ : _) (A : _) → Var80 Γ A → Tm80 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm80 (snoc80 Γ A) B → Tm80 Γ (arr80 A B))
   (app   : (Γ : _) (A B : _) → Tm80 Γ (arr80 A B) → Tm80 Γ A → Tm80 Γ B)
 → Tm80 Γ A

var80 : ∀{Γ A} → Var80 Γ A → Tm80 Γ A;var80
 = λ x Tm80 var80 lam app → var80 _ _ x

lam80 : ∀{Γ A B} → Tm80 (snoc80 Γ A) B → Tm80 Γ (arr80 A B);lam80
 = λ t Tm80 var80 lam80 app → lam80 _ _ _ (t Tm80 var80 lam80 app)

app80 : ∀{Γ A B} → Tm80 Γ (arr80 A B) → Tm80 Γ A → Tm80 Γ B;app80
 = λ t u Tm80 var80 lam80 app80 →
     app80 _ _ _ (t Tm80 var80 lam80 app80) (u Tm80 var80 lam80 app80)

v080 : ∀{Γ A} → Tm80 (snoc80 Γ A) A;v080
 = var80 vz80

v180 : ∀{Γ A B} → Tm80 (snoc80 (snoc80 Γ A) B) A;v180
 = var80 (vs80 vz80)

v280 : ∀{Γ A B C} → Tm80 (snoc80 (snoc80 (snoc80 Γ A) B) C) A;v280
 = var80 (vs80 (vs80 vz80))

v380 : ∀{Γ A B C D} → Tm80 (snoc80 (snoc80 (snoc80 (snoc80 Γ A) B) C) D) A;v380
 = var80 (vs80 (vs80 (vs80 vz80)))

v480 : ∀{Γ A B C D E} → Tm80 (snoc80 (snoc80 (snoc80 (snoc80 (snoc80 Γ A) B) C) D) E) A;v480
 = var80 (vs80 (vs80 (vs80 (vs80 vz80))))

test80 : ∀{Γ A} → Tm80 Γ (arr80 (arr80 A A) (arr80 A A));test80
  = lam80 (lam80 (app80 v180 (app80 v180 (app80 v180 (app80 v180 (app80 v180 (app80 v180 v080)))))))
{-# OPTIONS --type-in-type #-}

Ty81 : Set; Ty81
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι81   : Ty81; ι81 = λ _ ι81 _ → ι81
arr81 : Ty81 → Ty81 → Ty81; arr81 = λ A B Ty81 ι81 arr81 → arr81 (A Ty81 ι81 arr81) (B Ty81 ι81 arr81)

Con81 : Set;Con81
 = (Con81 : Set)
   (nil  : Con81)
   (snoc : Con81 → Ty81 → Con81)
 → Con81

nil81 : Con81;nil81
 = λ Con81 nil81 snoc → nil81

snoc81 : Con81 → Ty81 → Con81;snoc81
 = λ Γ A Con81 nil81 snoc81 → snoc81 (Γ Con81 nil81 snoc81) A

Var81 : Con81 → Ty81 → Set;Var81
 = λ Γ A →
   (Var81 : Con81 → Ty81 → Set)
   (vz  : (Γ : _)(A : _) → Var81 (snoc81 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var81 Γ A → Var81 (snoc81 Γ B) A)
 → Var81 Γ A

vz81 : ∀{Γ A} → Var81 (snoc81 Γ A) A;vz81
 = λ Var81 vz81 vs → vz81 _ _

vs81 : ∀{Γ B A} → Var81 Γ A → Var81 (snoc81 Γ B) A;vs81
 = λ x Var81 vz81 vs81 → vs81 _ _ _ (x Var81 vz81 vs81)

Tm81 : Con81 → Ty81 → Set;Tm81
 = λ Γ A →
   (Tm81    : Con81 → Ty81 → Set)
   (var   : (Γ : _) (A : _) → Var81 Γ A → Tm81 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm81 (snoc81 Γ A) B → Tm81 Γ (arr81 A B))
   (app   : (Γ : _) (A B : _) → Tm81 Γ (arr81 A B) → Tm81 Γ A → Tm81 Γ B)
 → Tm81 Γ A

var81 : ∀{Γ A} → Var81 Γ A → Tm81 Γ A;var81
 = λ x Tm81 var81 lam app → var81 _ _ x

lam81 : ∀{Γ A B} → Tm81 (snoc81 Γ A) B → Tm81 Γ (arr81 A B);lam81
 = λ t Tm81 var81 lam81 app → lam81 _ _ _ (t Tm81 var81 lam81 app)

app81 : ∀{Γ A B} → Tm81 Γ (arr81 A B) → Tm81 Γ A → Tm81 Γ B;app81
 = λ t u Tm81 var81 lam81 app81 →
     app81 _ _ _ (t Tm81 var81 lam81 app81) (u Tm81 var81 lam81 app81)

v081 : ∀{Γ A} → Tm81 (snoc81 Γ A) A;v081
 = var81 vz81

v181 : ∀{Γ A B} → Tm81 (snoc81 (snoc81 Γ A) B) A;v181
 = var81 (vs81 vz81)

v281 : ∀{Γ A B C} → Tm81 (snoc81 (snoc81 (snoc81 Γ A) B) C) A;v281
 = var81 (vs81 (vs81 vz81))

v381 : ∀{Γ A B C D} → Tm81 (snoc81 (snoc81 (snoc81 (snoc81 Γ A) B) C) D) A;v381
 = var81 (vs81 (vs81 (vs81 vz81)))

v481 : ∀{Γ A B C D E} → Tm81 (snoc81 (snoc81 (snoc81 (snoc81 (snoc81 Γ A) B) C) D) E) A;v481
 = var81 (vs81 (vs81 (vs81 (vs81 vz81))))

test81 : ∀{Γ A} → Tm81 Γ (arr81 (arr81 A A) (arr81 A A));test81
  = lam81 (lam81 (app81 v181 (app81 v181 (app81 v181 (app81 v181 (app81 v181 (app81 v181 v081)))))))
{-# OPTIONS --type-in-type #-}

Ty82 : Set; Ty82
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι82   : Ty82; ι82 = λ _ ι82 _ → ι82
arr82 : Ty82 → Ty82 → Ty82; arr82 = λ A B Ty82 ι82 arr82 → arr82 (A Ty82 ι82 arr82) (B Ty82 ι82 arr82)

Con82 : Set;Con82
 = (Con82 : Set)
   (nil  : Con82)
   (snoc : Con82 → Ty82 → Con82)
 → Con82

nil82 : Con82;nil82
 = λ Con82 nil82 snoc → nil82

snoc82 : Con82 → Ty82 → Con82;snoc82
 = λ Γ A Con82 nil82 snoc82 → snoc82 (Γ Con82 nil82 snoc82) A

Var82 : Con82 → Ty82 → Set;Var82
 = λ Γ A →
   (Var82 : Con82 → Ty82 → Set)
   (vz  : (Γ : _)(A : _) → Var82 (snoc82 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var82 Γ A → Var82 (snoc82 Γ B) A)
 → Var82 Γ A

vz82 : ∀{Γ A} → Var82 (snoc82 Γ A) A;vz82
 = λ Var82 vz82 vs → vz82 _ _

vs82 : ∀{Γ B A} → Var82 Γ A → Var82 (snoc82 Γ B) A;vs82
 = λ x Var82 vz82 vs82 → vs82 _ _ _ (x Var82 vz82 vs82)

Tm82 : Con82 → Ty82 → Set;Tm82
 = λ Γ A →
   (Tm82    : Con82 → Ty82 → Set)
   (var   : (Γ : _) (A : _) → Var82 Γ A → Tm82 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm82 (snoc82 Γ A) B → Tm82 Γ (arr82 A B))
   (app   : (Γ : _) (A B : _) → Tm82 Γ (arr82 A B) → Tm82 Γ A → Tm82 Γ B)
 → Tm82 Γ A

var82 : ∀{Γ A} → Var82 Γ A → Tm82 Γ A;var82
 = λ x Tm82 var82 lam app → var82 _ _ x

lam82 : ∀{Γ A B} → Tm82 (snoc82 Γ A) B → Tm82 Γ (arr82 A B);lam82
 = λ t Tm82 var82 lam82 app → lam82 _ _ _ (t Tm82 var82 lam82 app)

app82 : ∀{Γ A B} → Tm82 Γ (arr82 A B) → Tm82 Γ A → Tm82 Γ B;app82
 = λ t u Tm82 var82 lam82 app82 →
     app82 _ _ _ (t Tm82 var82 lam82 app82) (u Tm82 var82 lam82 app82)

v082 : ∀{Γ A} → Tm82 (snoc82 Γ A) A;v082
 = var82 vz82

v182 : ∀{Γ A B} → Tm82 (snoc82 (snoc82 Γ A) B) A;v182
 = var82 (vs82 vz82)

v282 : ∀{Γ A B C} → Tm82 (snoc82 (snoc82 (snoc82 Γ A) B) C) A;v282
 = var82 (vs82 (vs82 vz82))

v382 : ∀{Γ A B C D} → Tm82 (snoc82 (snoc82 (snoc82 (snoc82 Γ A) B) C) D) A;v382
 = var82 (vs82 (vs82 (vs82 vz82)))

v482 : ∀{Γ A B C D E} → Tm82 (snoc82 (snoc82 (snoc82 (snoc82 (snoc82 Γ A) B) C) D) E) A;v482
 = var82 (vs82 (vs82 (vs82 (vs82 vz82))))

test82 : ∀{Γ A} → Tm82 Γ (arr82 (arr82 A A) (arr82 A A));test82
  = lam82 (lam82 (app82 v182 (app82 v182 (app82 v182 (app82 v182 (app82 v182 (app82 v182 v082)))))))
{-# OPTIONS --type-in-type #-}

Ty83 : Set; Ty83
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι83   : Ty83; ι83 = λ _ ι83 _ → ι83
arr83 : Ty83 → Ty83 → Ty83; arr83 = λ A B Ty83 ι83 arr83 → arr83 (A Ty83 ι83 arr83) (B Ty83 ι83 arr83)

Con83 : Set;Con83
 = (Con83 : Set)
   (nil  : Con83)
   (snoc : Con83 → Ty83 → Con83)
 → Con83

nil83 : Con83;nil83
 = λ Con83 nil83 snoc → nil83

snoc83 : Con83 → Ty83 → Con83;snoc83
 = λ Γ A Con83 nil83 snoc83 → snoc83 (Γ Con83 nil83 snoc83) A

Var83 : Con83 → Ty83 → Set;Var83
 = λ Γ A →
   (Var83 : Con83 → Ty83 → Set)
   (vz  : (Γ : _)(A : _) → Var83 (snoc83 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var83 Γ A → Var83 (snoc83 Γ B) A)
 → Var83 Γ A

vz83 : ∀{Γ A} → Var83 (snoc83 Γ A) A;vz83
 = λ Var83 vz83 vs → vz83 _ _

vs83 : ∀{Γ B A} → Var83 Γ A → Var83 (snoc83 Γ B) A;vs83
 = λ x Var83 vz83 vs83 → vs83 _ _ _ (x Var83 vz83 vs83)

Tm83 : Con83 → Ty83 → Set;Tm83
 = λ Γ A →
   (Tm83    : Con83 → Ty83 → Set)
   (var   : (Γ : _) (A : _) → Var83 Γ A → Tm83 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm83 (snoc83 Γ A) B → Tm83 Γ (arr83 A B))
   (app   : (Γ : _) (A B : _) → Tm83 Γ (arr83 A B) → Tm83 Γ A → Tm83 Γ B)
 → Tm83 Γ A

var83 : ∀{Γ A} → Var83 Γ A → Tm83 Γ A;var83
 = λ x Tm83 var83 lam app → var83 _ _ x

lam83 : ∀{Γ A B} → Tm83 (snoc83 Γ A) B → Tm83 Γ (arr83 A B);lam83
 = λ t Tm83 var83 lam83 app → lam83 _ _ _ (t Tm83 var83 lam83 app)

app83 : ∀{Γ A B} → Tm83 Γ (arr83 A B) → Tm83 Γ A → Tm83 Γ B;app83
 = λ t u Tm83 var83 lam83 app83 →
     app83 _ _ _ (t Tm83 var83 lam83 app83) (u Tm83 var83 lam83 app83)

v083 : ∀{Γ A} → Tm83 (snoc83 Γ A) A;v083
 = var83 vz83

v183 : ∀{Γ A B} → Tm83 (snoc83 (snoc83 Γ A) B) A;v183
 = var83 (vs83 vz83)

v283 : ∀{Γ A B C} → Tm83 (snoc83 (snoc83 (snoc83 Γ A) B) C) A;v283
 = var83 (vs83 (vs83 vz83))

v383 : ∀{Γ A B C D} → Tm83 (snoc83 (snoc83 (snoc83 (snoc83 Γ A) B) C) D) A;v383
 = var83 (vs83 (vs83 (vs83 vz83)))

v483 : ∀{Γ A B C D E} → Tm83 (snoc83 (snoc83 (snoc83 (snoc83 (snoc83 Γ A) B) C) D) E) A;v483
 = var83 (vs83 (vs83 (vs83 (vs83 vz83))))

test83 : ∀{Γ A} → Tm83 Γ (arr83 (arr83 A A) (arr83 A A));test83
  = lam83 (lam83 (app83 v183 (app83 v183 (app83 v183 (app83 v183 (app83 v183 (app83 v183 v083)))))))
{-# OPTIONS --type-in-type #-}

Ty84 : Set; Ty84
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι84   : Ty84; ι84 = λ _ ι84 _ → ι84
arr84 : Ty84 → Ty84 → Ty84; arr84 = λ A B Ty84 ι84 arr84 → arr84 (A Ty84 ι84 arr84) (B Ty84 ι84 arr84)

Con84 : Set;Con84
 = (Con84 : Set)
   (nil  : Con84)
   (snoc : Con84 → Ty84 → Con84)
 → Con84

nil84 : Con84;nil84
 = λ Con84 nil84 snoc → nil84

snoc84 : Con84 → Ty84 → Con84;snoc84
 = λ Γ A Con84 nil84 snoc84 → snoc84 (Γ Con84 nil84 snoc84) A

Var84 : Con84 → Ty84 → Set;Var84
 = λ Γ A →
   (Var84 : Con84 → Ty84 → Set)
   (vz  : (Γ : _)(A : _) → Var84 (snoc84 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var84 Γ A → Var84 (snoc84 Γ B) A)
 → Var84 Γ A

vz84 : ∀{Γ A} → Var84 (snoc84 Γ A) A;vz84
 = λ Var84 vz84 vs → vz84 _ _

vs84 : ∀{Γ B A} → Var84 Γ A → Var84 (snoc84 Γ B) A;vs84
 = λ x Var84 vz84 vs84 → vs84 _ _ _ (x Var84 vz84 vs84)

Tm84 : Con84 → Ty84 → Set;Tm84
 = λ Γ A →
   (Tm84    : Con84 → Ty84 → Set)
   (var   : (Γ : _) (A : _) → Var84 Γ A → Tm84 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm84 (snoc84 Γ A) B → Tm84 Γ (arr84 A B))
   (app   : (Γ : _) (A B : _) → Tm84 Γ (arr84 A B) → Tm84 Γ A → Tm84 Γ B)
 → Tm84 Γ A

var84 : ∀{Γ A} → Var84 Γ A → Tm84 Γ A;var84
 = λ x Tm84 var84 lam app → var84 _ _ x

lam84 : ∀{Γ A B} → Tm84 (snoc84 Γ A) B → Tm84 Γ (arr84 A B);lam84
 = λ t Tm84 var84 lam84 app → lam84 _ _ _ (t Tm84 var84 lam84 app)

app84 : ∀{Γ A B} → Tm84 Γ (arr84 A B) → Tm84 Γ A → Tm84 Γ B;app84
 = λ t u Tm84 var84 lam84 app84 →
     app84 _ _ _ (t Tm84 var84 lam84 app84) (u Tm84 var84 lam84 app84)

v084 : ∀{Γ A} → Tm84 (snoc84 Γ A) A;v084
 = var84 vz84

v184 : ∀{Γ A B} → Tm84 (snoc84 (snoc84 Γ A) B) A;v184
 = var84 (vs84 vz84)

v284 : ∀{Γ A B C} → Tm84 (snoc84 (snoc84 (snoc84 Γ A) B) C) A;v284
 = var84 (vs84 (vs84 vz84))

v384 : ∀{Γ A B C D} → Tm84 (snoc84 (snoc84 (snoc84 (snoc84 Γ A) B) C) D) A;v384
 = var84 (vs84 (vs84 (vs84 vz84)))

v484 : ∀{Γ A B C D E} → Tm84 (snoc84 (snoc84 (snoc84 (snoc84 (snoc84 Γ A) B) C) D) E) A;v484
 = var84 (vs84 (vs84 (vs84 (vs84 vz84))))

test84 : ∀{Γ A} → Tm84 Γ (arr84 (arr84 A A) (arr84 A A));test84
  = lam84 (lam84 (app84 v184 (app84 v184 (app84 v184 (app84 v184 (app84 v184 (app84 v184 v084)))))))
{-# OPTIONS --type-in-type #-}

Ty85 : Set; Ty85
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι85   : Ty85; ι85 = λ _ ι85 _ → ι85
arr85 : Ty85 → Ty85 → Ty85; arr85 = λ A B Ty85 ι85 arr85 → arr85 (A Ty85 ι85 arr85) (B Ty85 ι85 arr85)

Con85 : Set;Con85
 = (Con85 : Set)
   (nil  : Con85)
   (snoc : Con85 → Ty85 → Con85)
 → Con85

nil85 : Con85;nil85
 = λ Con85 nil85 snoc → nil85

snoc85 : Con85 → Ty85 → Con85;snoc85
 = λ Γ A Con85 nil85 snoc85 → snoc85 (Γ Con85 nil85 snoc85) A

Var85 : Con85 → Ty85 → Set;Var85
 = λ Γ A →
   (Var85 : Con85 → Ty85 → Set)
   (vz  : (Γ : _)(A : _) → Var85 (snoc85 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var85 Γ A → Var85 (snoc85 Γ B) A)
 → Var85 Γ A

vz85 : ∀{Γ A} → Var85 (snoc85 Γ A) A;vz85
 = λ Var85 vz85 vs → vz85 _ _

vs85 : ∀{Γ B A} → Var85 Γ A → Var85 (snoc85 Γ B) A;vs85
 = λ x Var85 vz85 vs85 → vs85 _ _ _ (x Var85 vz85 vs85)

Tm85 : Con85 → Ty85 → Set;Tm85
 = λ Γ A →
   (Tm85    : Con85 → Ty85 → Set)
   (var   : (Γ : _) (A : _) → Var85 Γ A → Tm85 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm85 (snoc85 Γ A) B → Tm85 Γ (arr85 A B))
   (app   : (Γ : _) (A B : _) → Tm85 Γ (arr85 A B) → Tm85 Γ A → Tm85 Γ B)
 → Tm85 Γ A

var85 : ∀{Γ A} → Var85 Γ A → Tm85 Γ A;var85
 = λ x Tm85 var85 lam app → var85 _ _ x

lam85 : ∀{Γ A B} → Tm85 (snoc85 Γ A) B → Tm85 Γ (arr85 A B);lam85
 = λ t Tm85 var85 lam85 app → lam85 _ _ _ (t Tm85 var85 lam85 app)

app85 : ∀{Γ A B} → Tm85 Γ (arr85 A B) → Tm85 Γ A → Tm85 Γ B;app85
 = λ t u Tm85 var85 lam85 app85 →
     app85 _ _ _ (t Tm85 var85 lam85 app85) (u Tm85 var85 lam85 app85)

v085 : ∀{Γ A} → Tm85 (snoc85 Γ A) A;v085
 = var85 vz85

v185 : ∀{Γ A B} → Tm85 (snoc85 (snoc85 Γ A) B) A;v185
 = var85 (vs85 vz85)

v285 : ∀{Γ A B C} → Tm85 (snoc85 (snoc85 (snoc85 Γ A) B) C) A;v285
 = var85 (vs85 (vs85 vz85))

v385 : ∀{Γ A B C D} → Tm85 (snoc85 (snoc85 (snoc85 (snoc85 Γ A) B) C) D) A;v385
 = var85 (vs85 (vs85 (vs85 vz85)))

v485 : ∀{Γ A B C D E} → Tm85 (snoc85 (snoc85 (snoc85 (snoc85 (snoc85 Γ A) B) C) D) E) A;v485
 = var85 (vs85 (vs85 (vs85 (vs85 vz85))))

test85 : ∀{Γ A} → Tm85 Γ (arr85 (arr85 A A) (arr85 A A));test85
  = lam85 (lam85 (app85 v185 (app85 v185 (app85 v185 (app85 v185 (app85 v185 (app85 v185 v085)))))))
{-# OPTIONS --type-in-type #-}

Ty86 : Set; Ty86
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι86   : Ty86; ι86 = λ _ ι86 _ → ι86
arr86 : Ty86 → Ty86 → Ty86; arr86 = λ A B Ty86 ι86 arr86 → arr86 (A Ty86 ι86 arr86) (B Ty86 ι86 arr86)

Con86 : Set;Con86
 = (Con86 : Set)
   (nil  : Con86)
   (snoc : Con86 → Ty86 → Con86)
 → Con86

nil86 : Con86;nil86
 = λ Con86 nil86 snoc → nil86

snoc86 : Con86 → Ty86 → Con86;snoc86
 = λ Γ A Con86 nil86 snoc86 → snoc86 (Γ Con86 nil86 snoc86) A

Var86 : Con86 → Ty86 → Set;Var86
 = λ Γ A →
   (Var86 : Con86 → Ty86 → Set)
   (vz  : (Γ : _)(A : _) → Var86 (snoc86 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var86 Γ A → Var86 (snoc86 Γ B) A)
 → Var86 Γ A

vz86 : ∀{Γ A} → Var86 (snoc86 Γ A) A;vz86
 = λ Var86 vz86 vs → vz86 _ _

vs86 : ∀{Γ B A} → Var86 Γ A → Var86 (snoc86 Γ B) A;vs86
 = λ x Var86 vz86 vs86 → vs86 _ _ _ (x Var86 vz86 vs86)

Tm86 : Con86 → Ty86 → Set;Tm86
 = λ Γ A →
   (Tm86    : Con86 → Ty86 → Set)
   (var   : (Γ : _) (A : _) → Var86 Γ A → Tm86 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm86 (snoc86 Γ A) B → Tm86 Γ (arr86 A B))
   (app   : (Γ : _) (A B : _) → Tm86 Γ (arr86 A B) → Tm86 Γ A → Tm86 Γ B)
 → Tm86 Γ A

var86 : ∀{Γ A} → Var86 Γ A → Tm86 Γ A;var86
 = λ x Tm86 var86 lam app → var86 _ _ x

lam86 : ∀{Γ A B} → Tm86 (snoc86 Γ A) B → Tm86 Γ (arr86 A B);lam86
 = λ t Tm86 var86 lam86 app → lam86 _ _ _ (t Tm86 var86 lam86 app)

app86 : ∀{Γ A B} → Tm86 Γ (arr86 A B) → Tm86 Γ A → Tm86 Γ B;app86
 = λ t u Tm86 var86 lam86 app86 →
     app86 _ _ _ (t Tm86 var86 lam86 app86) (u Tm86 var86 lam86 app86)

v086 : ∀{Γ A} → Tm86 (snoc86 Γ A) A;v086
 = var86 vz86

v186 : ∀{Γ A B} → Tm86 (snoc86 (snoc86 Γ A) B) A;v186
 = var86 (vs86 vz86)

v286 : ∀{Γ A B C} → Tm86 (snoc86 (snoc86 (snoc86 Γ A) B) C) A;v286
 = var86 (vs86 (vs86 vz86))

v386 : ∀{Γ A B C D} → Tm86 (snoc86 (snoc86 (snoc86 (snoc86 Γ A) B) C) D) A;v386
 = var86 (vs86 (vs86 (vs86 vz86)))

v486 : ∀{Γ A B C D E} → Tm86 (snoc86 (snoc86 (snoc86 (snoc86 (snoc86 Γ A) B) C) D) E) A;v486
 = var86 (vs86 (vs86 (vs86 (vs86 vz86))))

test86 : ∀{Γ A} → Tm86 Γ (arr86 (arr86 A A) (arr86 A A));test86
  = lam86 (lam86 (app86 v186 (app86 v186 (app86 v186 (app86 v186 (app86 v186 (app86 v186 v086)))))))
{-# OPTIONS --type-in-type #-}

Ty87 : Set; Ty87
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι87   : Ty87; ι87 = λ _ ι87 _ → ι87
arr87 : Ty87 → Ty87 → Ty87; arr87 = λ A B Ty87 ι87 arr87 → arr87 (A Ty87 ι87 arr87) (B Ty87 ι87 arr87)

Con87 : Set;Con87
 = (Con87 : Set)
   (nil  : Con87)
   (snoc : Con87 → Ty87 → Con87)
 → Con87

nil87 : Con87;nil87
 = λ Con87 nil87 snoc → nil87

snoc87 : Con87 → Ty87 → Con87;snoc87
 = λ Γ A Con87 nil87 snoc87 → snoc87 (Γ Con87 nil87 snoc87) A

Var87 : Con87 → Ty87 → Set;Var87
 = λ Γ A →
   (Var87 : Con87 → Ty87 → Set)
   (vz  : (Γ : _)(A : _) → Var87 (snoc87 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var87 Γ A → Var87 (snoc87 Γ B) A)
 → Var87 Γ A

vz87 : ∀{Γ A} → Var87 (snoc87 Γ A) A;vz87
 = λ Var87 vz87 vs → vz87 _ _

vs87 : ∀{Γ B A} → Var87 Γ A → Var87 (snoc87 Γ B) A;vs87
 = λ x Var87 vz87 vs87 → vs87 _ _ _ (x Var87 vz87 vs87)

Tm87 : Con87 → Ty87 → Set;Tm87
 = λ Γ A →
   (Tm87    : Con87 → Ty87 → Set)
   (var   : (Γ : _) (A : _) → Var87 Γ A → Tm87 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm87 (snoc87 Γ A) B → Tm87 Γ (arr87 A B))
   (app   : (Γ : _) (A B : _) → Tm87 Γ (arr87 A B) → Tm87 Γ A → Tm87 Γ B)
 → Tm87 Γ A

var87 : ∀{Γ A} → Var87 Γ A → Tm87 Γ A;var87
 = λ x Tm87 var87 lam app → var87 _ _ x

lam87 : ∀{Γ A B} → Tm87 (snoc87 Γ A) B → Tm87 Γ (arr87 A B);lam87
 = λ t Tm87 var87 lam87 app → lam87 _ _ _ (t Tm87 var87 lam87 app)

app87 : ∀{Γ A B} → Tm87 Γ (arr87 A B) → Tm87 Γ A → Tm87 Γ B;app87
 = λ t u Tm87 var87 lam87 app87 →
     app87 _ _ _ (t Tm87 var87 lam87 app87) (u Tm87 var87 lam87 app87)

v087 : ∀{Γ A} → Tm87 (snoc87 Γ A) A;v087
 = var87 vz87

v187 : ∀{Γ A B} → Tm87 (snoc87 (snoc87 Γ A) B) A;v187
 = var87 (vs87 vz87)

v287 : ∀{Γ A B C} → Tm87 (snoc87 (snoc87 (snoc87 Γ A) B) C) A;v287
 = var87 (vs87 (vs87 vz87))

v387 : ∀{Γ A B C D} → Tm87 (snoc87 (snoc87 (snoc87 (snoc87 Γ A) B) C) D) A;v387
 = var87 (vs87 (vs87 (vs87 vz87)))

v487 : ∀{Γ A B C D E} → Tm87 (snoc87 (snoc87 (snoc87 (snoc87 (snoc87 Γ A) B) C) D) E) A;v487
 = var87 (vs87 (vs87 (vs87 (vs87 vz87))))

test87 : ∀{Γ A} → Tm87 Γ (arr87 (arr87 A A) (arr87 A A));test87
  = lam87 (lam87 (app87 v187 (app87 v187 (app87 v187 (app87 v187 (app87 v187 (app87 v187 v087)))))))
{-# OPTIONS --type-in-type #-}

Ty88 : Set; Ty88
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι88   : Ty88; ι88 = λ _ ι88 _ → ι88
arr88 : Ty88 → Ty88 → Ty88; arr88 = λ A B Ty88 ι88 arr88 → arr88 (A Ty88 ι88 arr88) (B Ty88 ι88 arr88)

Con88 : Set;Con88
 = (Con88 : Set)
   (nil  : Con88)
   (snoc : Con88 → Ty88 → Con88)
 → Con88

nil88 : Con88;nil88
 = λ Con88 nil88 snoc → nil88

snoc88 : Con88 → Ty88 → Con88;snoc88
 = λ Γ A Con88 nil88 snoc88 → snoc88 (Γ Con88 nil88 snoc88) A

Var88 : Con88 → Ty88 → Set;Var88
 = λ Γ A →
   (Var88 : Con88 → Ty88 → Set)
   (vz  : (Γ : _)(A : _) → Var88 (snoc88 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var88 Γ A → Var88 (snoc88 Γ B) A)
 → Var88 Γ A

vz88 : ∀{Γ A} → Var88 (snoc88 Γ A) A;vz88
 = λ Var88 vz88 vs → vz88 _ _

vs88 : ∀{Γ B A} → Var88 Γ A → Var88 (snoc88 Γ B) A;vs88
 = λ x Var88 vz88 vs88 → vs88 _ _ _ (x Var88 vz88 vs88)

Tm88 : Con88 → Ty88 → Set;Tm88
 = λ Γ A →
   (Tm88    : Con88 → Ty88 → Set)
   (var   : (Γ : _) (A : _) → Var88 Γ A → Tm88 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm88 (snoc88 Γ A) B → Tm88 Γ (arr88 A B))
   (app   : (Γ : _) (A B : _) → Tm88 Γ (arr88 A B) → Tm88 Γ A → Tm88 Γ B)
 → Tm88 Γ A

var88 : ∀{Γ A} → Var88 Γ A → Tm88 Γ A;var88
 = λ x Tm88 var88 lam app → var88 _ _ x

lam88 : ∀{Γ A B} → Tm88 (snoc88 Γ A) B → Tm88 Γ (arr88 A B);lam88
 = λ t Tm88 var88 lam88 app → lam88 _ _ _ (t Tm88 var88 lam88 app)

app88 : ∀{Γ A B} → Tm88 Γ (arr88 A B) → Tm88 Γ A → Tm88 Γ B;app88
 = λ t u Tm88 var88 lam88 app88 →
     app88 _ _ _ (t Tm88 var88 lam88 app88) (u Tm88 var88 lam88 app88)

v088 : ∀{Γ A} → Tm88 (snoc88 Γ A) A;v088
 = var88 vz88

v188 : ∀{Γ A B} → Tm88 (snoc88 (snoc88 Γ A) B) A;v188
 = var88 (vs88 vz88)

v288 : ∀{Γ A B C} → Tm88 (snoc88 (snoc88 (snoc88 Γ A) B) C) A;v288
 = var88 (vs88 (vs88 vz88))

v388 : ∀{Γ A B C D} → Tm88 (snoc88 (snoc88 (snoc88 (snoc88 Γ A) B) C) D) A;v388
 = var88 (vs88 (vs88 (vs88 vz88)))

v488 : ∀{Γ A B C D E} → Tm88 (snoc88 (snoc88 (snoc88 (snoc88 (snoc88 Γ A) B) C) D) E) A;v488
 = var88 (vs88 (vs88 (vs88 (vs88 vz88))))

test88 : ∀{Γ A} → Tm88 Γ (arr88 (arr88 A A) (arr88 A A));test88
  = lam88 (lam88 (app88 v188 (app88 v188 (app88 v188 (app88 v188 (app88 v188 (app88 v188 v088)))))))
{-# OPTIONS --type-in-type #-}

Ty89 : Set; Ty89
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι89   : Ty89; ι89 = λ _ ι89 _ → ι89
arr89 : Ty89 → Ty89 → Ty89; arr89 = λ A B Ty89 ι89 arr89 → arr89 (A Ty89 ι89 arr89) (B Ty89 ι89 arr89)

Con89 : Set;Con89
 = (Con89 : Set)
   (nil  : Con89)
   (snoc : Con89 → Ty89 → Con89)
 → Con89

nil89 : Con89;nil89
 = λ Con89 nil89 snoc → nil89

snoc89 : Con89 → Ty89 → Con89;snoc89
 = λ Γ A Con89 nil89 snoc89 → snoc89 (Γ Con89 nil89 snoc89) A

Var89 : Con89 → Ty89 → Set;Var89
 = λ Γ A →
   (Var89 : Con89 → Ty89 → Set)
   (vz  : (Γ : _)(A : _) → Var89 (snoc89 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var89 Γ A → Var89 (snoc89 Γ B) A)
 → Var89 Γ A

vz89 : ∀{Γ A} → Var89 (snoc89 Γ A) A;vz89
 = λ Var89 vz89 vs → vz89 _ _

vs89 : ∀{Γ B A} → Var89 Γ A → Var89 (snoc89 Γ B) A;vs89
 = λ x Var89 vz89 vs89 → vs89 _ _ _ (x Var89 vz89 vs89)

Tm89 : Con89 → Ty89 → Set;Tm89
 = λ Γ A →
   (Tm89    : Con89 → Ty89 → Set)
   (var   : (Γ : _) (A : _) → Var89 Γ A → Tm89 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm89 (snoc89 Γ A) B → Tm89 Γ (arr89 A B))
   (app   : (Γ : _) (A B : _) → Tm89 Γ (arr89 A B) → Tm89 Γ A → Tm89 Γ B)
 → Tm89 Γ A

var89 : ∀{Γ A} → Var89 Γ A → Tm89 Γ A;var89
 = λ x Tm89 var89 lam app → var89 _ _ x

lam89 : ∀{Γ A B} → Tm89 (snoc89 Γ A) B → Tm89 Γ (arr89 A B);lam89
 = λ t Tm89 var89 lam89 app → lam89 _ _ _ (t Tm89 var89 lam89 app)

app89 : ∀{Γ A B} → Tm89 Γ (arr89 A B) → Tm89 Γ A → Tm89 Γ B;app89
 = λ t u Tm89 var89 lam89 app89 →
     app89 _ _ _ (t Tm89 var89 lam89 app89) (u Tm89 var89 lam89 app89)

v089 : ∀{Γ A} → Tm89 (snoc89 Γ A) A;v089
 = var89 vz89

v189 : ∀{Γ A B} → Tm89 (snoc89 (snoc89 Γ A) B) A;v189
 = var89 (vs89 vz89)

v289 : ∀{Γ A B C} → Tm89 (snoc89 (snoc89 (snoc89 Γ A) B) C) A;v289
 = var89 (vs89 (vs89 vz89))

v389 : ∀{Γ A B C D} → Tm89 (snoc89 (snoc89 (snoc89 (snoc89 Γ A) B) C) D) A;v389
 = var89 (vs89 (vs89 (vs89 vz89)))

v489 : ∀{Γ A B C D E} → Tm89 (snoc89 (snoc89 (snoc89 (snoc89 (snoc89 Γ A) B) C) D) E) A;v489
 = var89 (vs89 (vs89 (vs89 (vs89 vz89))))

test89 : ∀{Γ A} → Tm89 Γ (arr89 (arr89 A A) (arr89 A A));test89
  = lam89 (lam89 (app89 v189 (app89 v189 (app89 v189 (app89 v189 (app89 v189 (app89 v189 v089)))))))
{-# OPTIONS --type-in-type #-}

Ty90 : Set; Ty90
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι90   : Ty90; ι90 = λ _ ι90 _ → ι90
arr90 : Ty90 → Ty90 → Ty90; arr90 = λ A B Ty90 ι90 arr90 → arr90 (A Ty90 ι90 arr90) (B Ty90 ι90 arr90)

Con90 : Set;Con90
 = (Con90 : Set)
   (nil  : Con90)
   (snoc : Con90 → Ty90 → Con90)
 → Con90

nil90 : Con90;nil90
 = λ Con90 nil90 snoc → nil90

snoc90 : Con90 → Ty90 → Con90;snoc90
 = λ Γ A Con90 nil90 snoc90 → snoc90 (Γ Con90 nil90 snoc90) A

Var90 : Con90 → Ty90 → Set;Var90
 = λ Γ A →
   (Var90 : Con90 → Ty90 → Set)
   (vz  : (Γ : _)(A : _) → Var90 (snoc90 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var90 Γ A → Var90 (snoc90 Γ B) A)
 → Var90 Γ A

vz90 : ∀{Γ A} → Var90 (snoc90 Γ A) A;vz90
 = λ Var90 vz90 vs → vz90 _ _

vs90 : ∀{Γ B A} → Var90 Γ A → Var90 (snoc90 Γ B) A;vs90
 = λ x Var90 vz90 vs90 → vs90 _ _ _ (x Var90 vz90 vs90)

Tm90 : Con90 → Ty90 → Set;Tm90
 = λ Γ A →
   (Tm90    : Con90 → Ty90 → Set)
   (var   : (Γ : _) (A : _) → Var90 Γ A → Tm90 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm90 (snoc90 Γ A) B → Tm90 Γ (arr90 A B))
   (app   : (Γ : _) (A B : _) → Tm90 Γ (arr90 A B) → Tm90 Γ A → Tm90 Γ B)
 → Tm90 Γ A

var90 : ∀{Γ A} → Var90 Γ A → Tm90 Γ A;var90
 = λ x Tm90 var90 lam app → var90 _ _ x

lam90 : ∀{Γ A B} → Tm90 (snoc90 Γ A) B → Tm90 Γ (arr90 A B);lam90
 = λ t Tm90 var90 lam90 app → lam90 _ _ _ (t Tm90 var90 lam90 app)

app90 : ∀{Γ A B} → Tm90 Γ (arr90 A B) → Tm90 Γ A → Tm90 Γ B;app90
 = λ t u Tm90 var90 lam90 app90 →
     app90 _ _ _ (t Tm90 var90 lam90 app90) (u Tm90 var90 lam90 app90)

v090 : ∀{Γ A} → Tm90 (snoc90 Γ A) A;v090
 = var90 vz90

v190 : ∀{Γ A B} → Tm90 (snoc90 (snoc90 Γ A) B) A;v190
 = var90 (vs90 vz90)

v290 : ∀{Γ A B C} → Tm90 (snoc90 (snoc90 (snoc90 Γ A) B) C) A;v290
 = var90 (vs90 (vs90 vz90))

v390 : ∀{Γ A B C D} → Tm90 (snoc90 (snoc90 (snoc90 (snoc90 Γ A) B) C) D) A;v390
 = var90 (vs90 (vs90 (vs90 vz90)))

v490 : ∀{Γ A B C D E} → Tm90 (snoc90 (snoc90 (snoc90 (snoc90 (snoc90 Γ A) B) C) D) E) A;v490
 = var90 (vs90 (vs90 (vs90 (vs90 vz90))))

test90 : ∀{Γ A} → Tm90 Γ (arr90 (arr90 A A) (arr90 A A));test90
  = lam90 (lam90 (app90 v190 (app90 v190 (app90 v190 (app90 v190 (app90 v190 (app90 v190 v090)))))))
{-# OPTIONS --type-in-type #-}

Ty91 : Set; Ty91
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι91   : Ty91; ι91 = λ _ ι91 _ → ι91
arr91 : Ty91 → Ty91 → Ty91; arr91 = λ A B Ty91 ι91 arr91 → arr91 (A Ty91 ι91 arr91) (B Ty91 ι91 arr91)

Con91 : Set;Con91
 = (Con91 : Set)
   (nil  : Con91)
   (snoc : Con91 → Ty91 → Con91)
 → Con91

nil91 : Con91;nil91
 = λ Con91 nil91 snoc → nil91

snoc91 : Con91 → Ty91 → Con91;snoc91
 = λ Γ A Con91 nil91 snoc91 → snoc91 (Γ Con91 nil91 snoc91) A

Var91 : Con91 → Ty91 → Set;Var91
 = λ Γ A →
   (Var91 : Con91 → Ty91 → Set)
   (vz  : (Γ : _)(A : _) → Var91 (snoc91 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var91 Γ A → Var91 (snoc91 Γ B) A)
 → Var91 Γ A

vz91 : ∀{Γ A} → Var91 (snoc91 Γ A) A;vz91
 = λ Var91 vz91 vs → vz91 _ _

vs91 : ∀{Γ B A} → Var91 Γ A → Var91 (snoc91 Γ B) A;vs91
 = λ x Var91 vz91 vs91 → vs91 _ _ _ (x Var91 vz91 vs91)

Tm91 : Con91 → Ty91 → Set;Tm91
 = λ Γ A →
   (Tm91    : Con91 → Ty91 → Set)
   (var   : (Γ : _) (A : _) → Var91 Γ A → Tm91 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm91 (snoc91 Γ A) B → Tm91 Γ (arr91 A B))
   (app   : (Γ : _) (A B : _) → Tm91 Γ (arr91 A B) → Tm91 Γ A → Tm91 Γ B)
 → Tm91 Γ A

var91 : ∀{Γ A} → Var91 Γ A → Tm91 Γ A;var91
 = λ x Tm91 var91 lam app → var91 _ _ x

lam91 : ∀{Γ A B} → Tm91 (snoc91 Γ A) B → Tm91 Γ (arr91 A B);lam91
 = λ t Tm91 var91 lam91 app → lam91 _ _ _ (t Tm91 var91 lam91 app)

app91 : ∀{Γ A B} → Tm91 Γ (arr91 A B) → Tm91 Γ A → Tm91 Γ B;app91
 = λ t u Tm91 var91 lam91 app91 →
     app91 _ _ _ (t Tm91 var91 lam91 app91) (u Tm91 var91 lam91 app91)

v091 : ∀{Γ A} → Tm91 (snoc91 Γ A) A;v091
 = var91 vz91

v191 : ∀{Γ A B} → Tm91 (snoc91 (snoc91 Γ A) B) A;v191
 = var91 (vs91 vz91)

v291 : ∀{Γ A B C} → Tm91 (snoc91 (snoc91 (snoc91 Γ A) B) C) A;v291
 = var91 (vs91 (vs91 vz91))

v391 : ∀{Γ A B C D} → Tm91 (snoc91 (snoc91 (snoc91 (snoc91 Γ A) B) C) D) A;v391
 = var91 (vs91 (vs91 (vs91 vz91)))

v491 : ∀{Γ A B C D E} → Tm91 (snoc91 (snoc91 (snoc91 (snoc91 (snoc91 Γ A) B) C) D) E) A;v491
 = var91 (vs91 (vs91 (vs91 (vs91 vz91))))

test91 : ∀{Γ A} → Tm91 Γ (arr91 (arr91 A A) (arr91 A A));test91
  = lam91 (lam91 (app91 v191 (app91 v191 (app91 v191 (app91 v191 (app91 v191 (app91 v191 v091)))))))
{-# OPTIONS --type-in-type #-}

Ty92 : Set; Ty92
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι92   : Ty92; ι92 = λ _ ι92 _ → ι92
arr92 : Ty92 → Ty92 → Ty92; arr92 = λ A B Ty92 ι92 arr92 → arr92 (A Ty92 ι92 arr92) (B Ty92 ι92 arr92)

Con92 : Set;Con92
 = (Con92 : Set)
   (nil  : Con92)
   (snoc : Con92 → Ty92 → Con92)
 → Con92

nil92 : Con92;nil92
 = λ Con92 nil92 snoc → nil92

snoc92 : Con92 → Ty92 → Con92;snoc92
 = λ Γ A Con92 nil92 snoc92 → snoc92 (Γ Con92 nil92 snoc92) A

Var92 : Con92 → Ty92 → Set;Var92
 = λ Γ A →
   (Var92 : Con92 → Ty92 → Set)
   (vz  : (Γ : _)(A : _) → Var92 (snoc92 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var92 Γ A → Var92 (snoc92 Γ B) A)
 → Var92 Γ A

vz92 : ∀{Γ A} → Var92 (snoc92 Γ A) A;vz92
 = λ Var92 vz92 vs → vz92 _ _

vs92 : ∀{Γ B A} → Var92 Γ A → Var92 (snoc92 Γ B) A;vs92
 = λ x Var92 vz92 vs92 → vs92 _ _ _ (x Var92 vz92 vs92)

Tm92 : Con92 → Ty92 → Set;Tm92
 = λ Γ A →
   (Tm92    : Con92 → Ty92 → Set)
   (var   : (Γ : _) (A : _) → Var92 Γ A → Tm92 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm92 (snoc92 Γ A) B → Tm92 Γ (arr92 A B))
   (app   : (Γ : _) (A B : _) → Tm92 Γ (arr92 A B) → Tm92 Γ A → Tm92 Γ B)
 → Tm92 Γ A

var92 : ∀{Γ A} → Var92 Γ A → Tm92 Γ A;var92
 = λ x Tm92 var92 lam app → var92 _ _ x

lam92 : ∀{Γ A B} → Tm92 (snoc92 Γ A) B → Tm92 Γ (arr92 A B);lam92
 = λ t Tm92 var92 lam92 app → lam92 _ _ _ (t Tm92 var92 lam92 app)

app92 : ∀{Γ A B} → Tm92 Γ (arr92 A B) → Tm92 Γ A → Tm92 Γ B;app92
 = λ t u Tm92 var92 lam92 app92 →
     app92 _ _ _ (t Tm92 var92 lam92 app92) (u Tm92 var92 lam92 app92)

v092 : ∀{Γ A} → Tm92 (snoc92 Γ A) A;v092
 = var92 vz92

v192 : ∀{Γ A B} → Tm92 (snoc92 (snoc92 Γ A) B) A;v192
 = var92 (vs92 vz92)

v292 : ∀{Γ A B C} → Tm92 (snoc92 (snoc92 (snoc92 Γ A) B) C) A;v292
 = var92 (vs92 (vs92 vz92))

v392 : ∀{Γ A B C D} → Tm92 (snoc92 (snoc92 (snoc92 (snoc92 Γ A) B) C) D) A;v392
 = var92 (vs92 (vs92 (vs92 vz92)))

v492 : ∀{Γ A B C D E} → Tm92 (snoc92 (snoc92 (snoc92 (snoc92 (snoc92 Γ A) B) C) D) E) A;v492
 = var92 (vs92 (vs92 (vs92 (vs92 vz92))))

test92 : ∀{Γ A} → Tm92 Γ (arr92 (arr92 A A) (arr92 A A));test92
  = lam92 (lam92 (app92 v192 (app92 v192 (app92 v192 (app92 v192 (app92 v192 (app92 v192 v092)))))))
{-# OPTIONS --type-in-type #-}

Ty93 : Set; Ty93
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι93   : Ty93; ι93 = λ _ ι93 _ → ι93
arr93 : Ty93 → Ty93 → Ty93; arr93 = λ A B Ty93 ι93 arr93 → arr93 (A Ty93 ι93 arr93) (B Ty93 ι93 arr93)

Con93 : Set;Con93
 = (Con93 : Set)
   (nil  : Con93)
   (snoc : Con93 → Ty93 → Con93)
 → Con93

nil93 : Con93;nil93
 = λ Con93 nil93 snoc → nil93

snoc93 : Con93 → Ty93 → Con93;snoc93
 = λ Γ A Con93 nil93 snoc93 → snoc93 (Γ Con93 nil93 snoc93) A

Var93 : Con93 → Ty93 → Set;Var93
 = λ Γ A →
   (Var93 : Con93 → Ty93 → Set)
   (vz  : (Γ : _)(A : _) → Var93 (snoc93 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var93 Γ A → Var93 (snoc93 Γ B) A)
 → Var93 Γ A

vz93 : ∀{Γ A} → Var93 (snoc93 Γ A) A;vz93
 = λ Var93 vz93 vs → vz93 _ _

vs93 : ∀{Γ B A} → Var93 Γ A → Var93 (snoc93 Γ B) A;vs93
 = λ x Var93 vz93 vs93 → vs93 _ _ _ (x Var93 vz93 vs93)

Tm93 : Con93 → Ty93 → Set;Tm93
 = λ Γ A →
   (Tm93    : Con93 → Ty93 → Set)
   (var   : (Γ : _) (A : _) → Var93 Γ A → Tm93 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm93 (snoc93 Γ A) B → Tm93 Γ (arr93 A B))
   (app   : (Γ : _) (A B : _) → Tm93 Γ (arr93 A B) → Tm93 Γ A → Tm93 Γ B)
 → Tm93 Γ A

var93 : ∀{Γ A} → Var93 Γ A → Tm93 Γ A;var93
 = λ x Tm93 var93 lam app → var93 _ _ x

lam93 : ∀{Γ A B} → Tm93 (snoc93 Γ A) B → Tm93 Γ (arr93 A B);lam93
 = λ t Tm93 var93 lam93 app → lam93 _ _ _ (t Tm93 var93 lam93 app)

app93 : ∀{Γ A B} → Tm93 Γ (arr93 A B) → Tm93 Γ A → Tm93 Γ B;app93
 = λ t u Tm93 var93 lam93 app93 →
     app93 _ _ _ (t Tm93 var93 lam93 app93) (u Tm93 var93 lam93 app93)

v093 : ∀{Γ A} → Tm93 (snoc93 Γ A) A;v093
 = var93 vz93

v193 : ∀{Γ A B} → Tm93 (snoc93 (snoc93 Γ A) B) A;v193
 = var93 (vs93 vz93)

v293 : ∀{Γ A B C} → Tm93 (snoc93 (snoc93 (snoc93 Γ A) B) C) A;v293
 = var93 (vs93 (vs93 vz93))

v393 : ∀{Γ A B C D} → Tm93 (snoc93 (snoc93 (snoc93 (snoc93 Γ A) B) C) D) A;v393
 = var93 (vs93 (vs93 (vs93 vz93)))

v493 : ∀{Γ A B C D E} → Tm93 (snoc93 (snoc93 (snoc93 (snoc93 (snoc93 Γ A) B) C) D) E) A;v493
 = var93 (vs93 (vs93 (vs93 (vs93 vz93))))

test93 : ∀{Γ A} → Tm93 Γ (arr93 (arr93 A A) (arr93 A A));test93
  = lam93 (lam93 (app93 v193 (app93 v193 (app93 v193 (app93 v193 (app93 v193 (app93 v193 v093)))))))
{-# OPTIONS --type-in-type #-}

Ty94 : Set; Ty94
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι94   : Ty94; ι94 = λ _ ι94 _ → ι94
arr94 : Ty94 → Ty94 → Ty94; arr94 = λ A B Ty94 ι94 arr94 → arr94 (A Ty94 ι94 arr94) (B Ty94 ι94 arr94)

Con94 : Set;Con94
 = (Con94 : Set)
   (nil  : Con94)
   (snoc : Con94 → Ty94 → Con94)
 → Con94

nil94 : Con94;nil94
 = λ Con94 nil94 snoc → nil94

snoc94 : Con94 → Ty94 → Con94;snoc94
 = λ Γ A Con94 nil94 snoc94 → snoc94 (Γ Con94 nil94 snoc94) A

Var94 : Con94 → Ty94 → Set;Var94
 = λ Γ A →
   (Var94 : Con94 → Ty94 → Set)
   (vz  : (Γ : _)(A : _) → Var94 (snoc94 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var94 Γ A → Var94 (snoc94 Γ B) A)
 → Var94 Γ A

vz94 : ∀{Γ A} → Var94 (snoc94 Γ A) A;vz94
 = λ Var94 vz94 vs → vz94 _ _

vs94 : ∀{Γ B A} → Var94 Γ A → Var94 (snoc94 Γ B) A;vs94
 = λ x Var94 vz94 vs94 → vs94 _ _ _ (x Var94 vz94 vs94)

Tm94 : Con94 → Ty94 → Set;Tm94
 = λ Γ A →
   (Tm94    : Con94 → Ty94 → Set)
   (var   : (Γ : _) (A : _) → Var94 Γ A → Tm94 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm94 (snoc94 Γ A) B → Tm94 Γ (arr94 A B))
   (app   : (Γ : _) (A B : _) → Tm94 Γ (arr94 A B) → Tm94 Γ A → Tm94 Γ B)
 → Tm94 Γ A

var94 : ∀{Γ A} → Var94 Γ A → Tm94 Γ A;var94
 = λ x Tm94 var94 lam app → var94 _ _ x

lam94 : ∀{Γ A B} → Tm94 (snoc94 Γ A) B → Tm94 Γ (arr94 A B);lam94
 = λ t Tm94 var94 lam94 app → lam94 _ _ _ (t Tm94 var94 lam94 app)

app94 : ∀{Γ A B} → Tm94 Γ (arr94 A B) → Tm94 Γ A → Tm94 Γ B;app94
 = λ t u Tm94 var94 lam94 app94 →
     app94 _ _ _ (t Tm94 var94 lam94 app94) (u Tm94 var94 lam94 app94)

v094 : ∀{Γ A} → Tm94 (snoc94 Γ A) A;v094
 = var94 vz94

v194 : ∀{Γ A B} → Tm94 (snoc94 (snoc94 Γ A) B) A;v194
 = var94 (vs94 vz94)

v294 : ∀{Γ A B C} → Tm94 (snoc94 (snoc94 (snoc94 Γ A) B) C) A;v294
 = var94 (vs94 (vs94 vz94))

v394 : ∀{Γ A B C D} → Tm94 (snoc94 (snoc94 (snoc94 (snoc94 Γ A) B) C) D) A;v394
 = var94 (vs94 (vs94 (vs94 vz94)))

v494 : ∀{Γ A B C D E} → Tm94 (snoc94 (snoc94 (snoc94 (snoc94 (snoc94 Γ A) B) C) D) E) A;v494
 = var94 (vs94 (vs94 (vs94 (vs94 vz94))))

test94 : ∀{Γ A} → Tm94 Γ (arr94 (arr94 A A) (arr94 A A));test94
  = lam94 (lam94 (app94 v194 (app94 v194 (app94 v194 (app94 v194 (app94 v194 (app94 v194 v094)))))))
{-# OPTIONS --type-in-type #-}

Ty95 : Set; Ty95
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι95   : Ty95; ι95 = λ _ ι95 _ → ι95
arr95 : Ty95 → Ty95 → Ty95; arr95 = λ A B Ty95 ι95 arr95 → arr95 (A Ty95 ι95 arr95) (B Ty95 ι95 arr95)

Con95 : Set;Con95
 = (Con95 : Set)
   (nil  : Con95)
   (snoc : Con95 → Ty95 → Con95)
 → Con95

nil95 : Con95;nil95
 = λ Con95 nil95 snoc → nil95

snoc95 : Con95 → Ty95 → Con95;snoc95
 = λ Γ A Con95 nil95 snoc95 → snoc95 (Γ Con95 nil95 snoc95) A

Var95 : Con95 → Ty95 → Set;Var95
 = λ Γ A →
   (Var95 : Con95 → Ty95 → Set)
   (vz  : (Γ : _)(A : _) → Var95 (snoc95 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var95 Γ A → Var95 (snoc95 Γ B) A)
 → Var95 Γ A

vz95 : ∀{Γ A} → Var95 (snoc95 Γ A) A;vz95
 = λ Var95 vz95 vs → vz95 _ _

vs95 : ∀{Γ B A} → Var95 Γ A → Var95 (snoc95 Γ B) A;vs95
 = λ x Var95 vz95 vs95 → vs95 _ _ _ (x Var95 vz95 vs95)

Tm95 : Con95 → Ty95 → Set;Tm95
 = λ Γ A →
   (Tm95    : Con95 → Ty95 → Set)
   (var   : (Γ : _) (A : _) → Var95 Γ A → Tm95 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm95 (snoc95 Γ A) B → Tm95 Γ (arr95 A B))
   (app   : (Γ : _) (A B : _) → Tm95 Γ (arr95 A B) → Tm95 Γ A → Tm95 Γ B)
 → Tm95 Γ A

var95 : ∀{Γ A} → Var95 Γ A → Tm95 Γ A;var95
 = λ x Tm95 var95 lam app → var95 _ _ x

lam95 : ∀{Γ A B} → Tm95 (snoc95 Γ A) B → Tm95 Γ (arr95 A B);lam95
 = λ t Tm95 var95 lam95 app → lam95 _ _ _ (t Tm95 var95 lam95 app)

app95 : ∀{Γ A B} → Tm95 Γ (arr95 A B) → Tm95 Γ A → Tm95 Γ B;app95
 = λ t u Tm95 var95 lam95 app95 →
     app95 _ _ _ (t Tm95 var95 lam95 app95) (u Tm95 var95 lam95 app95)

v095 : ∀{Γ A} → Tm95 (snoc95 Γ A) A;v095
 = var95 vz95

v195 : ∀{Γ A B} → Tm95 (snoc95 (snoc95 Γ A) B) A;v195
 = var95 (vs95 vz95)

v295 : ∀{Γ A B C} → Tm95 (snoc95 (snoc95 (snoc95 Γ A) B) C) A;v295
 = var95 (vs95 (vs95 vz95))

v395 : ∀{Γ A B C D} → Tm95 (snoc95 (snoc95 (snoc95 (snoc95 Γ A) B) C) D) A;v395
 = var95 (vs95 (vs95 (vs95 vz95)))

v495 : ∀{Γ A B C D E} → Tm95 (snoc95 (snoc95 (snoc95 (snoc95 (snoc95 Γ A) B) C) D) E) A;v495
 = var95 (vs95 (vs95 (vs95 (vs95 vz95))))

test95 : ∀{Γ A} → Tm95 Γ (arr95 (arr95 A A) (arr95 A A));test95
  = lam95 (lam95 (app95 v195 (app95 v195 (app95 v195 (app95 v195 (app95 v195 (app95 v195 v095)))))))
{-# OPTIONS --type-in-type #-}

Ty96 : Set; Ty96
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι96   : Ty96; ι96 = λ _ ι96 _ → ι96
arr96 : Ty96 → Ty96 → Ty96; arr96 = λ A B Ty96 ι96 arr96 → arr96 (A Ty96 ι96 arr96) (B Ty96 ι96 arr96)

Con96 : Set;Con96
 = (Con96 : Set)
   (nil  : Con96)
   (snoc : Con96 → Ty96 → Con96)
 → Con96

nil96 : Con96;nil96
 = λ Con96 nil96 snoc → nil96

snoc96 : Con96 → Ty96 → Con96;snoc96
 = λ Γ A Con96 nil96 snoc96 → snoc96 (Γ Con96 nil96 snoc96) A

Var96 : Con96 → Ty96 → Set;Var96
 = λ Γ A →
   (Var96 : Con96 → Ty96 → Set)
   (vz  : (Γ : _)(A : _) → Var96 (snoc96 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var96 Γ A → Var96 (snoc96 Γ B) A)
 → Var96 Γ A

vz96 : ∀{Γ A} → Var96 (snoc96 Γ A) A;vz96
 = λ Var96 vz96 vs → vz96 _ _

vs96 : ∀{Γ B A} → Var96 Γ A → Var96 (snoc96 Γ B) A;vs96
 = λ x Var96 vz96 vs96 → vs96 _ _ _ (x Var96 vz96 vs96)

Tm96 : Con96 → Ty96 → Set;Tm96
 = λ Γ A →
   (Tm96    : Con96 → Ty96 → Set)
   (var   : (Γ : _) (A : _) → Var96 Γ A → Tm96 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm96 (snoc96 Γ A) B → Tm96 Γ (arr96 A B))
   (app   : (Γ : _) (A B : _) → Tm96 Γ (arr96 A B) → Tm96 Γ A → Tm96 Γ B)
 → Tm96 Γ A

var96 : ∀{Γ A} → Var96 Γ A → Tm96 Γ A;var96
 = λ x Tm96 var96 lam app → var96 _ _ x

lam96 : ∀{Γ A B} → Tm96 (snoc96 Γ A) B → Tm96 Γ (arr96 A B);lam96
 = λ t Tm96 var96 lam96 app → lam96 _ _ _ (t Tm96 var96 lam96 app)

app96 : ∀{Γ A B} → Tm96 Γ (arr96 A B) → Tm96 Γ A → Tm96 Γ B;app96
 = λ t u Tm96 var96 lam96 app96 →
     app96 _ _ _ (t Tm96 var96 lam96 app96) (u Tm96 var96 lam96 app96)

v096 : ∀{Γ A} → Tm96 (snoc96 Γ A) A;v096
 = var96 vz96

v196 : ∀{Γ A B} → Tm96 (snoc96 (snoc96 Γ A) B) A;v196
 = var96 (vs96 vz96)

v296 : ∀{Γ A B C} → Tm96 (snoc96 (snoc96 (snoc96 Γ A) B) C) A;v296
 = var96 (vs96 (vs96 vz96))

v396 : ∀{Γ A B C D} → Tm96 (snoc96 (snoc96 (snoc96 (snoc96 Γ A) B) C) D) A;v396
 = var96 (vs96 (vs96 (vs96 vz96)))

v496 : ∀{Γ A B C D E} → Tm96 (snoc96 (snoc96 (snoc96 (snoc96 (snoc96 Γ A) B) C) D) E) A;v496
 = var96 (vs96 (vs96 (vs96 (vs96 vz96))))

test96 : ∀{Γ A} → Tm96 Γ (arr96 (arr96 A A) (arr96 A A));test96
  = lam96 (lam96 (app96 v196 (app96 v196 (app96 v196 (app96 v196 (app96 v196 (app96 v196 v096)))))))
{-# OPTIONS --type-in-type #-}

Ty97 : Set; Ty97
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι97   : Ty97; ι97 = λ _ ι97 _ → ι97
arr97 : Ty97 → Ty97 → Ty97; arr97 = λ A B Ty97 ι97 arr97 → arr97 (A Ty97 ι97 arr97) (B Ty97 ι97 arr97)

Con97 : Set;Con97
 = (Con97 : Set)
   (nil  : Con97)
   (snoc : Con97 → Ty97 → Con97)
 → Con97

nil97 : Con97;nil97
 = λ Con97 nil97 snoc → nil97

snoc97 : Con97 → Ty97 → Con97;snoc97
 = λ Γ A Con97 nil97 snoc97 → snoc97 (Γ Con97 nil97 snoc97) A

Var97 : Con97 → Ty97 → Set;Var97
 = λ Γ A →
   (Var97 : Con97 → Ty97 → Set)
   (vz  : (Γ : _)(A : _) → Var97 (snoc97 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var97 Γ A → Var97 (snoc97 Γ B) A)
 → Var97 Γ A

vz97 : ∀{Γ A} → Var97 (snoc97 Γ A) A;vz97
 = λ Var97 vz97 vs → vz97 _ _

vs97 : ∀{Γ B A} → Var97 Γ A → Var97 (snoc97 Γ B) A;vs97
 = λ x Var97 vz97 vs97 → vs97 _ _ _ (x Var97 vz97 vs97)

Tm97 : Con97 → Ty97 → Set;Tm97
 = λ Γ A →
   (Tm97    : Con97 → Ty97 → Set)
   (var   : (Γ : _) (A : _) → Var97 Γ A → Tm97 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm97 (snoc97 Γ A) B → Tm97 Γ (arr97 A B))
   (app   : (Γ : _) (A B : _) → Tm97 Γ (arr97 A B) → Tm97 Γ A → Tm97 Γ B)
 → Tm97 Γ A

var97 : ∀{Γ A} → Var97 Γ A → Tm97 Γ A;var97
 = λ x Tm97 var97 lam app → var97 _ _ x

lam97 : ∀{Γ A B} → Tm97 (snoc97 Γ A) B → Tm97 Γ (arr97 A B);lam97
 = λ t Tm97 var97 lam97 app → lam97 _ _ _ (t Tm97 var97 lam97 app)

app97 : ∀{Γ A B} → Tm97 Γ (arr97 A B) → Tm97 Γ A → Tm97 Γ B;app97
 = λ t u Tm97 var97 lam97 app97 →
     app97 _ _ _ (t Tm97 var97 lam97 app97) (u Tm97 var97 lam97 app97)

v097 : ∀{Γ A} → Tm97 (snoc97 Γ A) A;v097
 = var97 vz97

v197 : ∀{Γ A B} → Tm97 (snoc97 (snoc97 Γ A) B) A;v197
 = var97 (vs97 vz97)

v297 : ∀{Γ A B C} → Tm97 (snoc97 (snoc97 (snoc97 Γ A) B) C) A;v297
 = var97 (vs97 (vs97 vz97))

v397 : ∀{Γ A B C D} → Tm97 (snoc97 (snoc97 (snoc97 (snoc97 Γ A) B) C) D) A;v397
 = var97 (vs97 (vs97 (vs97 vz97)))

v497 : ∀{Γ A B C D E} → Tm97 (snoc97 (snoc97 (snoc97 (snoc97 (snoc97 Γ A) B) C) D) E) A;v497
 = var97 (vs97 (vs97 (vs97 (vs97 vz97))))

test97 : ∀{Γ A} → Tm97 Γ (arr97 (arr97 A A) (arr97 A A));test97
  = lam97 (lam97 (app97 v197 (app97 v197 (app97 v197 (app97 v197 (app97 v197 (app97 v197 v097)))))))
{-# OPTIONS --type-in-type #-}

Ty98 : Set; Ty98
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι98   : Ty98; ι98 = λ _ ι98 _ → ι98
arr98 : Ty98 → Ty98 → Ty98; arr98 = λ A B Ty98 ι98 arr98 → arr98 (A Ty98 ι98 arr98) (B Ty98 ι98 arr98)

Con98 : Set;Con98
 = (Con98 : Set)
   (nil  : Con98)
   (snoc : Con98 → Ty98 → Con98)
 → Con98

nil98 : Con98;nil98
 = λ Con98 nil98 snoc → nil98

snoc98 : Con98 → Ty98 → Con98;snoc98
 = λ Γ A Con98 nil98 snoc98 → snoc98 (Γ Con98 nil98 snoc98) A

Var98 : Con98 → Ty98 → Set;Var98
 = λ Γ A →
   (Var98 : Con98 → Ty98 → Set)
   (vz  : (Γ : _)(A : _) → Var98 (snoc98 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var98 Γ A → Var98 (snoc98 Γ B) A)
 → Var98 Γ A

vz98 : ∀{Γ A} → Var98 (snoc98 Γ A) A;vz98
 = λ Var98 vz98 vs → vz98 _ _

vs98 : ∀{Γ B A} → Var98 Γ A → Var98 (snoc98 Γ B) A;vs98
 = λ x Var98 vz98 vs98 → vs98 _ _ _ (x Var98 vz98 vs98)

Tm98 : Con98 → Ty98 → Set;Tm98
 = λ Γ A →
   (Tm98    : Con98 → Ty98 → Set)
   (var   : (Γ : _) (A : _) → Var98 Γ A → Tm98 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm98 (snoc98 Γ A) B → Tm98 Γ (arr98 A B))
   (app   : (Γ : _) (A B : _) → Tm98 Γ (arr98 A B) → Tm98 Γ A → Tm98 Γ B)
 → Tm98 Γ A

var98 : ∀{Γ A} → Var98 Γ A → Tm98 Γ A;var98
 = λ x Tm98 var98 lam app → var98 _ _ x

lam98 : ∀{Γ A B} → Tm98 (snoc98 Γ A) B → Tm98 Γ (arr98 A B);lam98
 = λ t Tm98 var98 lam98 app → lam98 _ _ _ (t Tm98 var98 lam98 app)

app98 : ∀{Γ A B} → Tm98 Γ (arr98 A B) → Tm98 Γ A → Tm98 Γ B;app98
 = λ t u Tm98 var98 lam98 app98 →
     app98 _ _ _ (t Tm98 var98 lam98 app98) (u Tm98 var98 lam98 app98)

v098 : ∀{Γ A} → Tm98 (snoc98 Γ A) A;v098
 = var98 vz98

v198 : ∀{Γ A B} → Tm98 (snoc98 (snoc98 Γ A) B) A;v198
 = var98 (vs98 vz98)

v298 : ∀{Γ A B C} → Tm98 (snoc98 (snoc98 (snoc98 Γ A) B) C) A;v298
 = var98 (vs98 (vs98 vz98))

v398 : ∀{Γ A B C D} → Tm98 (snoc98 (snoc98 (snoc98 (snoc98 Γ A) B) C) D) A;v398
 = var98 (vs98 (vs98 (vs98 vz98)))

v498 : ∀{Γ A B C D E} → Tm98 (snoc98 (snoc98 (snoc98 (snoc98 (snoc98 Γ A) B) C) D) E) A;v498
 = var98 (vs98 (vs98 (vs98 (vs98 vz98))))

test98 : ∀{Γ A} → Tm98 Γ (arr98 (arr98 A A) (arr98 A A));test98
  = lam98 (lam98 (app98 v198 (app98 v198 (app98 v198 (app98 v198 (app98 v198 (app98 v198 v098)))))))
{-# OPTIONS --type-in-type #-}

Ty99 : Set; Ty99
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι99   : Ty99; ι99 = λ _ ι99 _ → ι99
arr99 : Ty99 → Ty99 → Ty99; arr99 = λ A B Ty99 ι99 arr99 → arr99 (A Ty99 ι99 arr99) (B Ty99 ι99 arr99)

Con99 : Set;Con99
 = (Con99 : Set)
   (nil  : Con99)
   (snoc : Con99 → Ty99 → Con99)
 → Con99

nil99 : Con99;nil99
 = λ Con99 nil99 snoc → nil99

snoc99 : Con99 → Ty99 → Con99;snoc99
 = λ Γ A Con99 nil99 snoc99 → snoc99 (Γ Con99 nil99 snoc99) A

Var99 : Con99 → Ty99 → Set;Var99
 = λ Γ A →
   (Var99 : Con99 → Ty99 → Set)
   (vz  : (Γ : _)(A : _) → Var99 (snoc99 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var99 Γ A → Var99 (snoc99 Γ B) A)
 → Var99 Γ A

vz99 : ∀{Γ A} → Var99 (snoc99 Γ A) A;vz99
 = λ Var99 vz99 vs → vz99 _ _

vs99 : ∀{Γ B A} → Var99 Γ A → Var99 (snoc99 Γ B) A;vs99
 = λ x Var99 vz99 vs99 → vs99 _ _ _ (x Var99 vz99 vs99)

Tm99 : Con99 → Ty99 → Set;Tm99
 = λ Γ A →
   (Tm99    : Con99 → Ty99 → Set)
   (var   : (Γ : _) (A : _) → Var99 Γ A → Tm99 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm99 (snoc99 Γ A) B → Tm99 Γ (arr99 A B))
   (app   : (Γ : _) (A B : _) → Tm99 Γ (arr99 A B) → Tm99 Γ A → Tm99 Γ B)
 → Tm99 Γ A

var99 : ∀{Γ A} → Var99 Γ A → Tm99 Γ A;var99
 = λ x Tm99 var99 lam app → var99 _ _ x

lam99 : ∀{Γ A B} → Tm99 (snoc99 Γ A) B → Tm99 Γ (arr99 A B);lam99
 = λ t Tm99 var99 lam99 app → lam99 _ _ _ (t Tm99 var99 lam99 app)

app99 : ∀{Γ A B} → Tm99 Γ (arr99 A B) → Tm99 Γ A → Tm99 Γ B;app99
 = λ t u Tm99 var99 lam99 app99 →
     app99 _ _ _ (t Tm99 var99 lam99 app99) (u Tm99 var99 lam99 app99)

v099 : ∀{Γ A} → Tm99 (snoc99 Γ A) A;v099
 = var99 vz99

v199 : ∀{Γ A B} → Tm99 (snoc99 (snoc99 Γ A) B) A;v199
 = var99 (vs99 vz99)

v299 : ∀{Γ A B C} → Tm99 (snoc99 (snoc99 (snoc99 Γ A) B) C) A;v299
 = var99 (vs99 (vs99 vz99))

v399 : ∀{Γ A B C D} → Tm99 (snoc99 (snoc99 (snoc99 (snoc99 Γ A) B) C) D) A;v399
 = var99 (vs99 (vs99 (vs99 vz99)))

v499 : ∀{Γ A B C D E} → Tm99 (snoc99 (snoc99 (snoc99 (snoc99 (snoc99 Γ A) B) C) D) E) A;v499
 = var99 (vs99 (vs99 (vs99 (vs99 vz99))))

test99 : ∀{Γ A} → Tm99 Γ (arr99 (arr99 A A) (arr99 A A));test99
  = lam99 (lam99 (app99 v199 (app99 v199 (app99 v199 (app99 v199 (app99 v199 (app99 v199 v099)))))))
{-# OPTIONS --type-in-type #-}

Ty100 : Set; Ty100
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι100   : Ty100; ι100 = λ _ ι100 _ → ι100
arr100 : Ty100 → Ty100 → Ty100; arr100 = λ A B Ty100 ι100 arr100 → arr100 (A Ty100 ι100 arr100) (B Ty100 ι100 arr100)

Con100 : Set;Con100
 = (Con100 : Set)
   (nil  : Con100)
   (snoc : Con100 → Ty100 → Con100)
 → Con100

nil100 : Con100;nil100
 = λ Con100 nil100 snoc → nil100

snoc100 : Con100 → Ty100 → Con100;snoc100
 = λ Γ A Con100 nil100 snoc100 → snoc100 (Γ Con100 nil100 snoc100) A

Var100 : Con100 → Ty100 → Set;Var100
 = λ Γ A →
   (Var100 : Con100 → Ty100 → Set)
   (vz  : (Γ : _)(A : _) → Var100 (snoc100 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var100 Γ A → Var100 (snoc100 Γ B) A)
 → Var100 Γ A

vz100 : ∀{Γ A} → Var100 (snoc100 Γ A) A;vz100
 = λ Var100 vz100 vs → vz100 _ _

vs100 : ∀{Γ B A} → Var100 Γ A → Var100 (snoc100 Γ B) A;vs100
 = λ x Var100 vz100 vs100 → vs100 _ _ _ (x Var100 vz100 vs100)

Tm100 : Con100 → Ty100 → Set;Tm100
 = λ Γ A →
   (Tm100    : Con100 → Ty100 → Set)
   (var   : (Γ : _) (A : _) → Var100 Γ A → Tm100 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm100 (snoc100 Γ A) B → Tm100 Γ (arr100 A B))
   (app   : (Γ : _) (A B : _) → Tm100 Γ (arr100 A B) → Tm100 Γ A → Tm100 Γ B)
 → Tm100 Γ A

var100 : ∀{Γ A} → Var100 Γ A → Tm100 Γ A;var100
 = λ x Tm100 var100 lam app → var100 _ _ x

lam100 : ∀{Γ A B} → Tm100 (snoc100 Γ A) B → Tm100 Γ (arr100 A B);lam100
 = λ t Tm100 var100 lam100 app → lam100 _ _ _ (t Tm100 var100 lam100 app)

app100 : ∀{Γ A B} → Tm100 Γ (arr100 A B) → Tm100 Γ A → Tm100 Γ B;app100
 = λ t u Tm100 var100 lam100 app100 →
     app100 _ _ _ (t Tm100 var100 lam100 app100) (u Tm100 var100 lam100 app100)

v0100 : ∀{Γ A} → Tm100 (snoc100 Γ A) A;v0100
 = var100 vz100

v1100 : ∀{Γ A B} → Tm100 (snoc100 (snoc100 Γ A) B) A;v1100
 = var100 (vs100 vz100)

v2100 : ∀{Γ A B C} → Tm100 (snoc100 (snoc100 (snoc100 Γ A) B) C) A;v2100
 = var100 (vs100 (vs100 vz100))

v3100 : ∀{Γ A B C D} → Tm100 (snoc100 (snoc100 (snoc100 (snoc100 Γ A) B) C) D) A;v3100
 = var100 (vs100 (vs100 (vs100 vz100)))

v4100 : ∀{Γ A B C D E} → Tm100 (snoc100 (snoc100 (snoc100 (snoc100 (snoc100 Γ A) B) C) D) E) A;v4100
 = var100 (vs100 (vs100 (vs100 (vs100 vz100))))

test100 : ∀{Γ A} → Tm100 Γ (arr100 (arr100 A A) (arr100 A A));test100
  = lam100 (lam100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 v0100)))))))
{-# OPTIONS --type-in-type #-}

Ty101 : Set; Ty101
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι101   : Ty101; ι101 = λ _ ι101 _ → ι101
arr101 : Ty101 → Ty101 → Ty101; arr101 = λ A B Ty101 ι101 arr101 → arr101 (A Ty101 ι101 arr101) (B Ty101 ι101 arr101)

Con101 : Set;Con101
 = (Con101 : Set)
   (nil  : Con101)
   (snoc : Con101 → Ty101 → Con101)
 → Con101

nil101 : Con101;nil101
 = λ Con101 nil101 snoc → nil101

snoc101 : Con101 → Ty101 → Con101;snoc101
 = λ Γ A Con101 nil101 snoc101 → snoc101 (Γ Con101 nil101 snoc101) A

Var101 : Con101 → Ty101 → Set;Var101
 = λ Γ A →
   (Var101 : Con101 → Ty101 → Set)
   (vz  : (Γ : _)(A : _) → Var101 (snoc101 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var101 Γ A → Var101 (snoc101 Γ B) A)
 → Var101 Γ A

vz101 : ∀{Γ A} → Var101 (snoc101 Γ A) A;vz101
 = λ Var101 vz101 vs → vz101 _ _

vs101 : ∀{Γ B A} → Var101 Γ A → Var101 (snoc101 Γ B) A;vs101
 = λ x Var101 vz101 vs101 → vs101 _ _ _ (x Var101 vz101 vs101)

Tm101 : Con101 → Ty101 → Set;Tm101
 = λ Γ A →
   (Tm101    : Con101 → Ty101 → Set)
   (var   : (Γ : _) (A : _) → Var101 Γ A → Tm101 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm101 (snoc101 Γ A) B → Tm101 Γ (arr101 A B))
   (app   : (Γ : _) (A B : _) → Tm101 Γ (arr101 A B) → Tm101 Γ A → Tm101 Γ B)
 → Tm101 Γ A

var101 : ∀{Γ A} → Var101 Γ A → Tm101 Γ A;var101
 = λ x Tm101 var101 lam app → var101 _ _ x

lam101 : ∀{Γ A B} → Tm101 (snoc101 Γ A) B → Tm101 Γ (arr101 A B);lam101
 = λ t Tm101 var101 lam101 app → lam101 _ _ _ (t Tm101 var101 lam101 app)

app101 : ∀{Γ A B} → Tm101 Γ (arr101 A B) → Tm101 Γ A → Tm101 Γ B;app101
 = λ t u Tm101 var101 lam101 app101 →
     app101 _ _ _ (t Tm101 var101 lam101 app101) (u Tm101 var101 lam101 app101)

v0101 : ∀{Γ A} → Tm101 (snoc101 Γ A) A;v0101
 = var101 vz101

v1101 : ∀{Γ A B} → Tm101 (snoc101 (snoc101 Γ A) B) A;v1101
 = var101 (vs101 vz101)

v2101 : ∀{Γ A B C} → Tm101 (snoc101 (snoc101 (snoc101 Γ A) B) C) A;v2101
 = var101 (vs101 (vs101 vz101))

v3101 : ∀{Γ A B C D} → Tm101 (snoc101 (snoc101 (snoc101 (snoc101 Γ A) B) C) D) A;v3101
 = var101 (vs101 (vs101 (vs101 vz101)))

v4101 : ∀{Γ A B C D E} → Tm101 (snoc101 (snoc101 (snoc101 (snoc101 (snoc101 Γ A) B) C) D) E) A;v4101
 = var101 (vs101 (vs101 (vs101 (vs101 vz101))))

test101 : ∀{Γ A} → Tm101 Γ (arr101 (arr101 A A) (arr101 A A));test101
  = lam101 (lam101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 v0101)))))))
{-# OPTIONS --type-in-type #-}

Ty102 : Set; Ty102
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι102   : Ty102; ι102 = λ _ ι102 _ → ι102
arr102 : Ty102 → Ty102 → Ty102; arr102 = λ A B Ty102 ι102 arr102 → arr102 (A Ty102 ι102 arr102) (B Ty102 ι102 arr102)

Con102 : Set;Con102
 = (Con102 : Set)
   (nil  : Con102)
   (snoc : Con102 → Ty102 → Con102)
 → Con102

nil102 : Con102;nil102
 = λ Con102 nil102 snoc → nil102

snoc102 : Con102 → Ty102 → Con102;snoc102
 = λ Γ A Con102 nil102 snoc102 → snoc102 (Γ Con102 nil102 snoc102) A

Var102 : Con102 → Ty102 → Set;Var102
 = λ Γ A →
   (Var102 : Con102 → Ty102 → Set)
   (vz  : (Γ : _)(A : _) → Var102 (snoc102 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var102 Γ A → Var102 (snoc102 Γ B) A)
 → Var102 Γ A

vz102 : ∀{Γ A} → Var102 (snoc102 Γ A) A;vz102
 = λ Var102 vz102 vs → vz102 _ _

vs102 : ∀{Γ B A} → Var102 Γ A → Var102 (snoc102 Γ B) A;vs102
 = λ x Var102 vz102 vs102 → vs102 _ _ _ (x Var102 vz102 vs102)

Tm102 : Con102 → Ty102 → Set;Tm102
 = λ Γ A →
   (Tm102    : Con102 → Ty102 → Set)
   (var   : (Γ : _) (A : _) → Var102 Γ A → Tm102 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm102 (snoc102 Γ A) B → Tm102 Γ (arr102 A B))
   (app   : (Γ : _) (A B : _) → Tm102 Γ (arr102 A B) → Tm102 Γ A → Tm102 Γ B)
 → Tm102 Γ A

var102 : ∀{Γ A} → Var102 Γ A → Tm102 Γ A;var102
 = λ x Tm102 var102 lam app → var102 _ _ x

lam102 : ∀{Γ A B} → Tm102 (snoc102 Γ A) B → Tm102 Γ (arr102 A B);lam102
 = λ t Tm102 var102 lam102 app → lam102 _ _ _ (t Tm102 var102 lam102 app)

app102 : ∀{Γ A B} → Tm102 Γ (arr102 A B) → Tm102 Γ A → Tm102 Γ B;app102
 = λ t u Tm102 var102 lam102 app102 →
     app102 _ _ _ (t Tm102 var102 lam102 app102) (u Tm102 var102 lam102 app102)

v0102 : ∀{Γ A} → Tm102 (snoc102 Γ A) A;v0102
 = var102 vz102

v1102 : ∀{Γ A B} → Tm102 (snoc102 (snoc102 Γ A) B) A;v1102
 = var102 (vs102 vz102)

v2102 : ∀{Γ A B C} → Tm102 (snoc102 (snoc102 (snoc102 Γ A) B) C) A;v2102
 = var102 (vs102 (vs102 vz102))

v3102 : ∀{Γ A B C D} → Tm102 (snoc102 (snoc102 (snoc102 (snoc102 Γ A) B) C) D) A;v3102
 = var102 (vs102 (vs102 (vs102 vz102)))

v4102 : ∀{Γ A B C D E} → Tm102 (snoc102 (snoc102 (snoc102 (snoc102 (snoc102 Γ A) B) C) D) E) A;v4102
 = var102 (vs102 (vs102 (vs102 (vs102 vz102))))

test102 : ∀{Γ A} → Tm102 Γ (arr102 (arr102 A A) (arr102 A A));test102
  = lam102 (lam102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 v0102)))))))
{-# OPTIONS --type-in-type #-}

Ty103 : Set; Ty103
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι103   : Ty103; ι103 = λ _ ι103 _ → ι103
arr103 : Ty103 → Ty103 → Ty103; arr103 = λ A B Ty103 ι103 arr103 → arr103 (A Ty103 ι103 arr103) (B Ty103 ι103 arr103)

Con103 : Set;Con103
 = (Con103 : Set)
   (nil  : Con103)
   (snoc : Con103 → Ty103 → Con103)
 → Con103

nil103 : Con103;nil103
 = λ Con103 nil103 snoc → nil103

snoc103 : Con103 → Ty103 → Con103;snoc103
 = λ Γ A Con103 nil103 snoc103 → snoc103 (Γ Con103 nil103 snoc103) A

Var103 : Con103 → Ty103 → Set;Var103
 = λ Γ A →
   (Var103 : Con103 → Ty103 → Set)
   (vz  : (Γ : _)(A : _) → Var103 (snoc103 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var103 Γ A → Var103 (snoc103 Γ B) A)
 → Var103 Γ A

vz103 : ∀{Γ A} → Var103 (snoc103 Γ A) A;vz103
 = λ Var103 vz103 vs → vz103 _ _

vs103 : ∀{Γ B A} → Var103 Γ A → Var103 (snoc103 Γ B) A;vs103
 = λ x Var103 vz103 vs103 → vs103 _ _ _ (x Var103 vz103 vs103)

Tm103 : Con103 → Ty103 → Set;Tm103
 = λ Γ A →
   (Tm103    : Con103 → Ty103 → Set)
   (var   : (Γ : _) (A : _) → Var103 Γ A → Tm103 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm103 (snoc103 Γ A) B → Tm103 Γ (arr103 A B))
   (app   : (Γ : _) (A B : _) → Tm103 Γ (arr103 A B) → Tm103 Γ A → Tm103 Γ B)
 → Tm103 Γ A

var103 : ∀{Γ A} → Var103 Γ A → Tm103 Γ A;var103
 = λ x Tm103 var103 lam app → var103 _ _ x

lam103 : ∀{Γ A B} → Tm103 (snoc103 Γ A) B → Tm103 Γ (arr103 A B);lam103
 = λ t Tm103 var103 lam103 app → lam103 _ _ _ (t Tm103 var103 lam103 app)

app103 : ∀{Γ A B} → Tm103 Γ (arr103 A B) → Tm103 Γ A → Tm103 Γ B;app103
 = λ t u Tm103 var103 lam103 app103 →
     app103 _ _ _ (t Tm103 var103 lam103 app103) (u Tm103 var103 lam103 app103)

v0103 : ∀{Γ A} → Tm103 (snoc103 Γ A) A;v0103
 = var103 vz103

v1103 : ∀{Γ A B} → Tm103 (snoc103 (snoc103 Γ A) B) A;v1103
 = var103 (vs103 vz103)

v2103 : ∀{Γ A B C} → Tm103 (snoc103 (snoc103 (snoc103 Γ A) B) C) A;v2103
 = var103 (vs103 (vs103 vz103))

v3103 : ∀{Γ A B C D} → Tm103 (snoc103 (snoc103 (snoc103 (snoc103 Γ A) B) C) D) A;v3103
 = var103 (vs103 (vs103 (vs103 vz103)))

v4103 : ∀{Γ A B C D E} → Tm103 (snoc103 (snoc103 (snoc103 (snoc103 (snoc103 Γ A) B) C) D) E) A;v4103
 = var103 (vs103 (vs103 (vs103 (vs103 vz103))))

test103 : ∀{Γ A} → Tm103 Γ (arr103 (arr103 A A) (arr103 A A));test103
  = lam103 (lam103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 v0103)))))))
{-# OPTIONS --type-in-type #-}

Ty104 : Set; Ty104
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι104   : Ty104; ι104 = λ _ ι104 _ → ι104
arr104 : Ty104 → Ty104 → Ty104; arr104 = λ A B Ty104 ι104 arr104 → arr104 (A Ty104 ι104 arr104) (B Ty104 ι104 arr104)

Con104 : Set;Con104
 = (Con104 : Set)
   (nil  : Con104)
   (snoc : Con104 → Ty104 → Con104)
 → Con104

nil104 : Con104;nil104
 = λ Con104 nil104 snoc → nil104

snoc104 : Con104 → Ty104 → Con104;snoc104
 = λ Γ A Con104 nil104 snoc104 → snoc104 (Γ Con104 nil104 snoc104) A

Var104 : Con104 → Ty104 → Set;Var104
 = λ Γ A →
   (Var104 : Con104 → Ty104 → Set)
   (vz  : (Γ : _)(A : _) → Var104 (snoc104 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var104 Γ A → Var104 (snoc104 Γ B) A)
 → Var104 Γ A

vz104 : ∀{Γ A} → Var104 (snoc104 Γ A) A;vz104
 = λ Var104 vz104 vs → vz104 _ _

vs104 : ∀{Γ B A} → Var104 Γ A → Var104 (snoc104 Γ B) A;vs104
 = λ x Var104 vz104 vs104 → vs104 _ _ _ (x Var104 vz104 vs104)

Tm104 : Con104 → Ty104 → Set;Tm104
 = λ Γ A →
   (Tm104    : Con104 → Ty104 → Set)
   (var   : (Γ : _) (A : _) → Var104 Γ A → Tm104 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm104 (snoc104 Γ A) B → Tm104 Γ (arr104 A B))
   (app   : (Γ : _) (A B : _) → Tm104 Γ (arr104 A B) → Tm104 Γ A → Tm104 Γ B)
 → Tm104 Γ A

var104 : ∀{Γ A} → Var104 Γ A → Tm104 Γ A;var104
 = λ x Tm104 var104 lam app → var104 _ _ x

lam104 : ∀{Γ A B} → Tm104 (snoc104 Γ A) B → Tm104 Γ (arr104 A B);lam104
 = λ t Tm104 var104 lam104 app → lam104 _ _ _ (t Tm104 var104 lam104 app)

app104 : ∀{Γ A B} → Tm104 Γ (arr104 A B) → Tm104 Γ A → Tm104 Γ B;app104
 = λ t u Tm104 var104 lam104 app104 →
     app104 _ _ _ (t Tm104 var104 lam104 app104) (u Tm104 var104 lam104 app104)

v0104 : ∀{Γ A} → Tm104 (snoc104 Γ A) A;v0104
 = var104 vz104

v1104 : ∀{Γ A B} → Tm104 (snoc104 (snoc104 Γ A) B) A;v1104
 = var104 (vs104 vz104)

v2104 : ∀{Γ A B C} → Tm104 (snoc104 (snoc104 (snoc104 Γ A) B) C) A;v2104
 = var104 (vs104 (vs104 vz104))

v3104 : ∀{Γ A B C D} → Tm104 (snoc104 (snoc104 (snoc104 (snoc104 Γ A) B) C) D) A;v3104
 = var104 (vs104 (vs104 (vs104 vz104)))

v4104 : ∀{Γ A B C D E} → Tm104 (snoc104 (snoc104 (snoc104 (snoc104 (snoc104 Γ A) B) C) D) E) A;v4104
 = var104 (vs104 (vs104 (vs104 (vs104 vz104))))

test104 : ∀{Γ A} → Tm104 Γ (arr104 (arr104 A A) (arr104 A A));test104
  = lam104 (lam104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 v0104)))))))
{-# OPTIONS --type-in-type #-}

Ty105 : Set; Ty105
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι105   : Ty105; ι105 = λ _ ι105 _ → ι105
arr105 : Ty105 → Ty105 → Ty105; arr105 = λ A B Ty105 ι105 arr105 → arr105 (A Ty105 ι105 arr105) (B Ty105 ι105 arr105)

Con105 : Set;Con105
 = (Con105 : Set)
   (nil  : Con105)
   (snoc : Con105 → Ty105 → Con105)
 → Con105

nil105 : Con105;nil105
 = λ Con105 nil105 snoc → nil105

snoc105 : Con105 → Ty105 → Con105;snoc105
 = λ Γ A Con105 nil105 snoc105 → snoc105 (Γ Con105 nil105 snoc105) A

Var105 : Con105 → Ty105 → Set;Var105
 = λ Γ A →
   (Var105 : Con105 → Ty105 → Set)
   (vz  : (Γ : _)(A : _) → Var105 (snoc105 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var105 Γ A → Var105 (snoc105 Γ B) A)
 → Var105 Γ A

vz105 : ∀{Γ A} → Var105 (snoc105 Γ A) A;vz105
 = λ Var105 vz105 vs → vz105 _ _

vs105 : ∀{Γ B A} → Var105 Γ A → Var105 (snoc105 Γ B) A;vs105
 = λ x Var105 vz105 vs105 → vs105 _ _ _ (x Var105 vz105 vs105)

Tm105 : Con105 → Ty105 → Set;Tm105
 = λ Γ A →
   (Tm105    : Con105 → Ty105 → Set)
   (var   : (Γ : _) (A : _) → Var105 Γ A → Tm105 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm105 (snoc105 Γ A) B → Tm105 Γ (arr105 A B))
   (app   : (Γ : _) (A B : _) → Tm105 Γ (arr105 A B) → Tm105 Γ A → Tm105 Γ B)
 → Tm105 Γ A

var105 : ∀{Γ A} → Var105 Γ A → Tm105 Γ A;var105
 = λ x Tm105 var105 lam app → var105 _ _ x

lam105 : ∀{Γ A B} → Tm105 (snoc105 Γ A) B → Tm105 Γ (arr105 A B);lam105
 = λ t Tm105 var105 lam105 app → lam105 _ _ _ (t Tm105 var105 lam105 app)

app105 : ∀{Γ A B} → Tm105 Γ (arr105 A B) → Tm105 Γ A → Tm105 Γ B;app105
 = λ t u Tm105 var105 lam105 app105 →
     app105 _ _ _ (t Tm105 var105 lam105 app105) (u Tm105 var105 lam105 app105)

v0105 : ∀{Γ A} → Tm105 (snoc105 Γ A) A;v0105
 = var105 vz105

v1105 : ∀{Γ A B} → Tm105 (snoc105 (snoc105 Γ A) B) A;v1105
 = var105 (vs105 vz105)

v2105 : ∀{Γ A B C} → Tm105 (snoc105 (snoc105 (snoc105 Γ A) B) C) A;v2105
 = var105 (vs105 (vs105 vz105))

v3105 : ∀{Γ A B C D} → Tm105 (snoc105 (snoc105 (snoc105 (snoc105 Γ A) B) C) D) A;v3105
 = var105 (vs105 (vs105 (vs105 vz105)))

v4105 : ∀{Γ A B C D E} → Tm105 (snoc105 (snoc105 (snoc105 (snoc105 (snoc105 Γ A) B) C) D) E) A;v4105
 = var105 (vs105 (vs105 (vs105 (vs105 vz105))))

test105 : ∀{Γ A} → Tm105 Γ (arr105 (arr105 A A) (arr105 A A));test105
  = lam105 (lam105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 v0105)))))))
{-# OPTIONS --type-in-type #-}

Ty106 : Set; Ty106
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι106   : Ty106; ι106 = λ _ ι106 _ → ι106
arr106 : Ty106 → Ty106 → Ty106; arr106 = λ A B Ty106 ι106 arr106 → arr106 (A Ty106 ι106 arr106) (B Ty106 ι106 arr106)

Con106 : Set;Con106
 = (Con106 : Set)
   (nil  : Con106)
   (snoc : Con106 → Ty106 → Con106)
 → Con106

nil106 : Con106;nil106
 = λ Con106 nil106 snoc → nil106

snoc106 : Con106 → Ty106 → Con106;snoc106
 = λ Γ A Con106 nil106 snoc106 → snoc106 (Γ Con106 nil106 snoc106) A

Var106 : Con106 → Ty106 → Set;Var106
 = λ Γ A →
   (Var106 : Con106 → Ty106 → Set)
   (vz  : (Γ : _)(A : _) → Var106 (snoc106 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var106 Γ A → Var106 (snoc106 Γ B) A)
 → Var106 Γ A

vz106 : ∀{Γ A} → Var106 (snoc106 Γ A) A;vz106
 = λ Var106 vz106 vs → vz106 _ _

vs106 : ∀{Γ B A} → Var106 Γ A → Var106 (snoc106 Γ B) A;vs106
 = λ x Var106 vz106 vs106 → vs106 _ _ _ (x Var106 vz106 vs106)

Tm106 : Con106 → Ty106 → Set;Tm106
 = λ Γ A →
   (Tm106    : Con106 → Ty106 → Set)
   (var   : (Γ : _) (A : _) → Var106 Γ A → Tm106 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm106 (snoc106 Γ A) B → Tm106 Γ (arr106 A B))
   (app   : (Γ : _) (A B : _) → Tm106 Γ (arr106 A B) → Tm106 Γ A → Tm106 Γ B)
 → Tm106 Γ A

var106 : ∀{Γ A} → Var106 Γ A → Tm106 Γ A;var106
 = λ x Tm106 var106 lam app → var106 _ _ x

lam106 : ∀{Γ A B} → Tm106 (snoc106 Γ A) B → Tm106 Γ (arr106 A B);lam106
 = λ t Tm106 var106 lam106 app → lam106 _ _ _ (t Tm106 var106 lam106 app)

app106 : ∀{Γ A B} → Tm106 Γ (arr106 A B) → Tm106 Γ A → Tm106 Γ B;app106
 = λ t u Tm106 var106 lam106 app106 →
     app106 _ _ _ (t Tm106 var106 lam106 app106) (u Tm106 var106 lam106 app106)

v0106 : ∀{Γ A} → Tm106 (snoc106 Γ A) A;v0106
 = var106 vz106

v1106 : ∀{Γ A B} → Tm106 (snoc106 (snoc106 Γ A) B) A;v1106
 = var106 (vs106 vz106)

v2106 : ∀{Γ A B C} → Tm106 (snoc106 (snoc106 (snoc106 Γ A) B) C) A;v2106
 = var106 (vs106 (vs106 vz106))

v3106 : ∀{Γ A B C D} → Tm106 (snoc106 (snoc106 (snoc106 (snoc106 Γ A) B) C) D) A;v3106
 = var106 (vs106 (vs106 (vs106 vz106)))

v4106 : ∀{Γ A B C D E} → Tm106 (snoc106 (snoc106 (snoc106 (snoc106 (snoc106 Γ A) B) C) D) E) A;v4106
 = var106 (vs106 (vs106 (vs106 (vs106 vz106))))

test106 : ∀{Γ A} → Tm106 Γ (arr106 (arr106 A A) (arr106 A A));test106
  = lam106 (lam106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 v0106)))))))
{-# OPTIONS --type-in-type #-}

Ty107 : Set; Ty107
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι107   : Ty107; ι107 = λ _ ι107 _ → ι107
arr107 : Ty107 → Ty107 → Ty107; arr107 = λ A B Ty107 ι107 arr107 → arr107 (A Ty107 ι107 arr107) (B Ty107 ι107 arr107)

Con107 : Set;Con107
 = (Con107 : Set)
   (nil  : Con107)
   (snoc : Con107 → Ty107 → Con107)
 → Con107

nil107 : Con107;nil107
 = λ Con107 nil107 snoc → nil107

snoc107 : Con107 → Ty107 → Con107;snoc107
 = λ Γ A Con107 nil107 snoc107 → snoc107 (Γ Con107 nil107 snoc107) A

Var107 : Con107 → Ty107 → Set;Var107
 = λ Γ A →
   (Var107 : Con107 → Ty107 → Set)
   (vz  : (Γ : _)(A : _) → Var107 (snoc107 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var107 Γ A → Var107 (snoc107 Γ B) A)
 → Var107 Γ A

vz107 : ∀{Γ A} → Var107 (snoc107 Γ A) A;vz107
 = λ Var107 vz107 vs → vz107 _ _

vs107 : ∀{Γ B A} → Var107 Γ A → Var107 (snoc107 Γ B) A;vs107
 = λ x Var107 vz107 vs107 → vs107 _ _ _ (x Var107 vz107 vs107)

Tm107 : Con107 → Ty107 → Set;Tm107
 = λ Γ A →
   (Tm107    : Con107 → Ty107 → Set)
   (var   : (Γ : _) (A : _) → Var107 Γ A → Tm107 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm107 (snoc107 Γ A) B → Tm107 Γ (arr107 A B))
   (app   : (Γ : _) (A B : _) → Tm107 Γ (arr107 A B) → Tm107 Γ A → Tm107 Γ B)
 → Tm107 Γ A

var107 : ∀{Γ A} → Var107 Γ A → Tm107 Γ A;var107
 = λ x Tm107 var107 lam app → var107 _ _ x

lam107 : ∀{Γ A B} → Tm107 (snoc107 Γ A) B → Tm107 Γ (arr107 A B);lam107
 = λ t Tm107 var107 lam107 app → lam107 _ _ _ (t Tm107 var107 lam107 app)

app107 : ∀{Γ A B} → Tm107 Γ (arr107 A B) → Tm107 Γ A → Tm107 Γ B;app107
 = λ t u Tm107 var107 lam107 app107 →
     app107 _ _ _ (t Tm107 var107 lam107 app107) (u Tm107 var107 lam107 app107)

v0107 : ∀{Γ A} → Tm107 (snoc107 Γ A) A;v0107
 = var107 vz107

v1107 : ∀{Γ A B} → Tm107 (snoc107 (snoc107 Γ A) B) A;v1107
 = var107 (vs107 vz107)

v2107 : ∀{Γ A B C} → Tm107 (snoc107 (snoc107 (snoc107 Γ A) B) C) A;v2107
 = var107 (vs107 (vs107 vz107))

v3107 : ∀{Γ A B C D} → Tm107 (snoc107 (snoc107 (snoc107 (snoc107 Γ A) B) C) D) A;v3107
 = var107 (vs107 (vs107 (vs107 vz107)))

v4107 : ∀{Γ A B C D E} → Tm107 (snoc107 (snoc107 (snoc107 (snoc107 (snoc107 Γ A) B) C) D) E) A;v4107
 = var107 (vs107 (vs107 (vs107 (vs107 vz107))))

test107 : ∀{Γ A} → Tm107 Γ (arr107 (arr107 A A) (arr107 A A));test107
  = lam107 (lam107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 v0107)))))))
{-# OPTIONS --type-in-type #-}

Ty108 : Set; Ty108
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι108   : Ty108; ι108 = λ _ ι108 _ → ι108
arr108 : Ty108 → Ty108 → Ty108; arr108 = λ A B Ty108 ι108 arr108 → arr108 (A Ty108 ι108 arr108) (B Ty108 ι108 arr108)

Con108 : Set;Con108
 = (Con108 : Set)
   (nil  : Con108)
   (snoc : Con108 → Ty108 → Con108)
 → Con108

nil108 : Con108;nil108
 = λ Con108 nil108 snoc → nil108

snoc108 : Con108 → Ty108 → Con108;snoc108
 = λ Γ A Con108 nil108 snoc108 → snoc108 (Γ Con108 nil108 snoc108) A

Var108 : Con108 → Ty108 → Set;Var108
 = λ Γ A →
   (Var108 : Con108 → Ty108 → Set)
   (vz  : (Γ : _)(A : _) → Var108 (snoc108 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var108 Γ A → Var108 (snoc108 Γ B) A)
 → Var108 Γ A

vz108 : ∀{Γ A} → Var108 (snoc108 Γ A) A;vz108
 = λ Var108 vz108 vs → vz108 _ _

vs108 : ∀{Γ B A} → Var108 Γ A → Var108 (snoc108 Γ B) A;vs108
 = λ x Var108 vz108 vs108 → vs108 _ _ _ (x Var108 vz108 vs108)

Tm108 : Con108 → Ty108 → Set;Tm108
 = λ Γ A →
   (Tm108    : Con108 → Ty108 → Set)
   (var   : (Γ : _) (A : _) → Var108 Γ A → Tm108 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm108 (snoc108 Γ A) B → Tm108 Γ (arr108 A B))
   (app   : (Γ : _) (A B : _) → Tm108 Γ (arr108 A B) → Tm108 Γ A → Tm108 Γ B)
 → Tm108 Γ A

var108 : ∀{Γ A} → Var108 Γ A → Tm108 Γ A;var108
 = λ x Tm108 var108 lam app → var108 _ _ x

lam108 : ∀{Γ A B} → Tm108 (snoc108 Γ A) B → Tm108 Γ (arr108 A B);lam108
 = λ t Tm108 var108 lam108 app → lam108 _ _ _ (t Tm108 var108 lam108 app)

app108 : ∀{Γ A B} → Tm108 Γ (arr108 A B) → Tm108 Γ A → Tm108 Γ B;app108
 = λ t u Tm108 var108 lam108 app108 →
     app108 _ _ _ (t Tm108 var108 lam108 app108) (u Tm108 var108 lam108 app108)

v0108 : ∀{Γ A} → Tm108 (snoc108 Γ A) A;v0108
 = var108 vz108

v1108 : ∀{Γ A B} → Tm108 (snoc108 (snoc108 Γ A) B) A;v1108
 = var108 (vs108 vz108)

v2108 : ∀{Γ A B C} → Tm108 (snoc108 (snoc108 (snoc108 Γ A) B) C) A;v2108
 = var108 (vs108 (vs108 vz108))

v3108 : ∀{Γ A B C D} → Tm108 (snoc108 (snoc108 (snoc108 (snoc108 Γ A) B) C) D) A;v3108
 = var108 (vs108 (vs108 (vs108 vz108)))

v4108 : ∀{Γ A B C D E} → Tm108 (snoc108 (snoc108 (snoc108 (snoc108 (snoc108 Γ A) B) C) D) E) A;v4108
 = var108 (vs108 (vs108 (vs108 (vs108 vz108))))

test108 : ∀{Γ A} → Tm108 Γ (arr108 (arr108 A A) (arr108 A A));test108
  = lam108 (lam108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 v0108)))))))
{-# OPTIONS --type-in-type #-}

Ty109 : Set; Ty109
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι109   : Ty109; ι109 = λ _ ι109 _ → ι109
arr109 : Ty109 → Ty109 → Ty109; arr109 = λ A B Ty109 ι109 arr109 → arr109 (A Ty109 ι109 arr109) (B Ty109 ι109 arr109)

Con109 : Set;Con109
 = (Con109 : Set)
   (nil  : Con109)
   (snoc : Con109 → Ty109 → Con109)
 → Con109

nil109 : Con109;nil109
 = λ Con109 nil109 snoc → nil109

snoc109 : Con109 → Ty109 → Con109;snoc109
 = λ Γ A Con109 nil109 snoc109 → snoc109 (Γ Con109 nil109 snoc109) A

Var109 : Con109 → Ty109 → Set;Var109
 = λ Γ A →
   (Var109 : Con109 → Ty109 → Set)
   (vz  : (Γ : _)(A : _) → Var109 (snoc109 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var109 Γ A → Var109 (snoc109 Γ B) A)
 → Var109 Γ A

vz109 : ∀{Γ A} → Var109 (snoc109 Γ A) A;vz109
 = λ Var109 vz109 vs → vz109 _ _

vs109 : ∀{Γ B A} → Var109 Γ A → Var109 (snoc109 Γ B) A;vs109
 = λ x Var109 vz109 vs109 → vs109 _ _ _ (x Var109 vz109 vs109)

Tm109 : Con109 → Ty109 → Set;Tm109
 = λ Γ A →
   (Tm109    : Con109 → Ty109 → Set)
   (var   : (Γ : _) (A : _) → Var109 Γ A → Tm109 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm109 (snoc109 Γ A) B → Tm109 Γ (arr109 A B))
   (app   : (Γ : _) (A B : _) → Tm109 Γ (arr109 A B) → Tm109 Γ A → Tm109 Γ B)
 → Tm109 Γ A

var109 : ∀{Γ A} → Var109 Γ A → Tm109 Γ A;var109
 = λ x Tm109 var109 lam app → var109 _ _ x

lam109 : ∀{Γ A B} → Tm109 (snoc109 Γ A) B → Tm109 Γ (arr109 A B);lam109
 = λ t Tm109 var109 lam109 app → lam109 _ _ _ (t Tm109 var109 lam109 app)

app109 : ∀{Γ A B} → Tm109 Γ (arr109 A B) → Tm109 Γ A → Tm109 Γ B;app109
 = λ t u Tm109 var109 lam109 app109 →
     app109 _ _ _ (t Tm109 var109 lam109 app109) (u Tm109 var109 lam109 app109)

v0109 : ∀{Γ A} → Tm109 (snoc109 Γ A) A;v0109
 = var109 vz109

v1109 : ∀{Γ A B} → Tm109 (snoc109 (snoc109 Γ A) B) A;v1109
 = var109 (vs109 vz109)

v2109 : ∀{Γ A B C} → Tm109 (snoc109 (snoc109 (snoc109 Γ A) B) C) A;v2109
 = var109 (vs109 (vs109 vz109))

v3109 : ∀{Γ A B C D} → Tm109 (snoc109 (snoc109 (snoc109 (snoc109 Γ A) B) C) D) A;v3109
 = var109 (vs109 (vs109 (vs109 vz109)))

v4109 : ∀{Γ A B C D E} → Tm109 (snoc109 (snoc109 (snoc109 (snoc109 (snoc109 Γ A) B) C) D) E) A;v4109
 = var109 (vs109 (vs109 (vs109 (vs109 vz109))))

test109 : ∀{Γ A} → Tm109 Γ (arr109 (arr109 A A) (arr109 A A));test109
  = lam109 (lam109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 v0109)))))))
{-# OPTIONS --type-in-type #-}

Ty110 : Set; Ty110
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι110   : Ty110; ι110 = λ _ ι110 _ → ι110
arr110 : Ty110 → Ty110 → Ty110; arr110 = λ A B Ty110 ι110 arr110 → arr110 (A Ty110 ι110 arr110) (B Ty110 ι110 arr110)

Con110 : Set;Con110
 = (Con110 : Set)
   (nil  : Con110)
   (snoc : Con110 → Ty110 → Con110)
 → Con110

nil110 : Con110;nil110
 = λ Con110 nil110 snoc → nil110

snoc110 : Con110 → Ty110 → Con110;snoc110
 = λ Γ A Con110 nil110 snoc110 → snoc110 (Γ Con110 nil110 snoc110) A

Var110 : Con110 → Ty110 → Set;Var110
 = λ Γ A →
   (Var110 : Con110 → Ty110 → Set)
   (vz  : (Γ : _)(A : _) → Var110 (snoc110 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var110 Γ A → Var110 (snoc110 Γ B) A)
 → Var110 Γ A

vz110 : ∀{Γ A} → Var110 (snoc110 Γ A) A;vz110
 = λ Var110 vz110 vs → vz110 _ _

vs110 : ∀{Γ B A} → Var110 Γ A → Var110 (snoc110 Γ B) A;vs110
 = λ x Var110 vz110 vs110 → vs110 _ _ _ (x Var110 vz110 vs110)

Tm110 : Con110 → Ty110 → Set;Tm110
 = λ Γ A →
   (Tm110    : Con110 → Ty110 → Set)
   (var   : (Γ : _) (A : _) → Var110 Γ A → Tm110 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm110 (snoc110 Γ A) B → Tm110 Γ (arr110 A B))
   (app   : (Γ : _) (A B : _) → Tm110 Γ (arr110 A B) → Tm110 Γ A → Tm110 Γ B)
 → Tm110 Γ A

var110 : ∀{Γ A} → Var110 Γ A → Tm110 Γ A;var110
 = λ x Tm110 var110 lam app → var110 _ _ x

lam110 : ∀{Γ A B} → Tm110 (snoc110 Γ A) B → Tm110 Γ (arr110 A B);lam110
 = λ t Tm110 var110 lam110 app → lam110 _ _ _ (t Tm110 var110 lam110 app)

app110 : ∀{Γ A B} → Tm110 Γ (arr110 A B) → Tm110 Γ A → Tm110 Γ B;app110
 = λ t u Tm110 var110 lam110 app110 →
     app110 _ _ _ (t Tm110 var110 lam110 app110) (u Tm110 var110 lam110 app110)

v0110 : ∀{Γ A} → Tm110 (snoc110 Γ A) A;v0110
 = var110 vz110

v1110 : ∀{Γ A B} → Tm110 (snoc110 (snoc110 Γ A) B) A;v1110
 = var110 (vs110 vz110)

v2110 : ∀{Γ A B C} → Tm110 (snoc110 (snoc110 (snoc110 Γ A) B) C) A;v2110
 = var110 (vs110 (vs110 vz110))

v3110 : ∀{Γ A B C D} → Tm110 (snoc110 (snoc110 (snoc110 (snoc110 Γ A) B) C) D) A;v3110
 = var110 (vs110 (vs110 (vs110 vz110)))

v4110 : ∀{Γ A B C D E} → Tm110 (snoc110 (snoc110 (snoc110 (snoc110 (snoc110 Γ A) B) C) D) E) A;v4110
 = var110 (vs110 (vs110 (vs110 (vs110 vz110))))

test110 : ∀{Γ A} → Tm110 Γ (arr110 (arr110 A A) (arr110 A A));test110
  = lam110 (lam110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 v0110)))))))
{-# OPTIONS --type-in-type #-}

Ty111 : Set; Ty111
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι111   : Ty111; ι111 = λ _ ι111 _ → ι111
arr111 : Ty111 → Ty111 → Ty111; arr111 = λ A B Ty111 ι111 arr111 → arr111 (A Ty111 ι111 arr111) (B Ty111 ι111 arr111)

Con111 : Set;Con111
 = (Con111 : Set)
   (nil  : Con111)
   (snoc : Con111 → Ty111 → Con111)
 → Con111

nil111 : Con111;nil111
 = λ Con111 nil111 snoc → nil111

snoc111 : Con111 → Ty111 → Con111;snoc111
 = λ Γ A Con111 nil111 snoc111 → snoc111 (Γ Con111 nil111 snoc111) A

Var111 : Con111 → Ty111 → Set;Var111
 = λ Γ A →
   (Var111 : Con111 → Ty111 → Set)
   (vz  : (Γ : _)(A : _) → Var111 (snoc111 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var111 Γ A → Var111 (snoc111 Γ B) A)
 → Var111 Γ A

vz111 : ∀{Γ A} → Var111 (snoc111 Γ A) A;vz111
 = λ Var111 vz111 vs → vz111 _ _

vs111 : ∀{Γ B A} → Var111 Γ A → Var111 (snoc111 Γ B) A;vs111
 = λ x Var111 vz111 vs111 → vs111 _ _ _ (x Var111 vz111 vs111)

Tm111 : Con111 → Ty111 → Set;Tm111
 = λ Γ A →
   (Tm111    : Con111 → Ty111 → Set)
   (var   : (Γ : _) (A : _) → Var111 Γ A → Tm111 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm111 (snoc111 Γ A) B → Tm111 Γ (arr111 A B))
   (app   : (Γ : _) (A B : _) → Tm111 Γ (arr111 A B) → Tm111 Γ A → Tm111 Γ B)
 → Tm111 Γ A

var111 : ∀{Γ A} → Var111 Γ A → Tm111 Γ A;var111
 = λ x Tm111 var111 lam app → var111 _ _ x

lam111 : ∀{Γ A B} → Tm111 (snoc111 Γ A) B → Tm111 Γ (arr111 A B);lam111
 = λ t Tm111 var111 lam111 app → lam111 _ _ _ (t Tm111 var111 lam111 app)

app111 : ∀{Γ A B} → Tm111 Γ (arr111 A B) → Tm111 Γ A → Tm111 Γ B;app111
 = λ t u Tm111 var111 lam111 app111 →
     app111 _ _ _ (t Tm111 var111 lam111 app111) (u Tm111 var111 lam111 app111)

v0111 : ∀{Γ A} → Tm111 (snoc111 Γ A) A;v0111
 = var111 vz111

v1111 : ∀{Γ A B} → Tm111 (snoc111 (snoc111 Γ A) B) A;v1111
 = var111 (vs111 vz111)

v2111 : ∀{Γ A B C} → Tm111 (snoc111 (snoc111 (snoc111 Γ A) B) C) A;v2111
 = var111 (vs111 (vs111 vz111))

v3111 : ∀{Γ A B C D} → Tm111 (snoc111 (snoc111 (snoc111 (snoc111 Γ A) B) C) D) A;v3111
 = var111 (vs111 (vs111 (vs111 vz111)))

v4111 : ∀{Γ A B C D E} → Tm111 (snoc111 (snoc111 (snoc111 (snoc111 (snoc111 Γ A) B) C) D) E) A;v4111
 = var111 (vs111 (vs111 (vs111 (vs111 vz111))))

test111 : ∀{Γ A} → Tm111 Γ (arr111 (arr111 A A) (arr111 A A));test111
  = lam111 (lam111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 v0111)))))))
{-# OPTIONS --type-in-type #-}

Ty112 : Set; Ty112
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι112   : Ty112; ι112 = λ _ ι112 _ → ι112
arr112 : Ty112 → Ty112 → Ty112; arr112 = λ A B Ty112 ι112 arr112 → arr112 (A Ty112 ι112 arr112) (B Ty112 ι112 arr112)

Con112 : Set;Con112
 = (Con112 : Set)
   (nil  : Con112)
   (snoc : Con112 → Ty112 → Con112)
 → Con112

nil112 : Con112;nil112
 = λ Con112 nil112 snoc → nil112

snoc112 : Con112 → Ty112 → Con112;snoc112
 = λ Γ A Con112 nil112 snoc112 → snoc112 (Γ Con112 nil112 snoc112) A

Var112 : Con112 → Ty112 → Set;Var112
 = λ Γ A →
   (Var112 : Con112 → Ty112 → Set)
   (vz  : (Γ : _)(A : _) → Var112 (snoc112 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var112 Γ A → Var112 (snoc112 Γ B) A)
 → Var112 Γ A

vz112 : ∀{Γ A} → Var112 (snoc112 Γ A) A;vz112
 = λ Var112 vz112 vs → vz112 _ _

vs112 : ∀{Γ B A} → Var112 Γ A → Var112 (snoc112 Γ B) A;vs112
 = λ x Var112 vz112 vs112 → vs112 _ _ _ (x Var112 vz112 vs112)

Tm112 : Con112 → Ty112 → Set;Tm112
 = λ Γ A →
   (Tm112    : Con112 → Ty112 → Set)
   (var   : (Γ : _) (A : _) → Var112 Γ A → Tm112 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm112 (snoc112 Γ A) B → Tm112 Γ (arr112 A B))
   (app   : (Γ : _) (A B : _) → Tm112 Γ (arr112 A B) → Tm112 Γ A → Tm112 Γ B)
 → Tm112 Γ A

var112 : ∀{Γ A} → Var112 Γ A → Tm112 Γ A;var112
 = λ x Tm112 var112 lam app → var112 _ _ x

lam112 : ∀{Γ A B} → Tm112 (snoc112 Γ A) B → Tm112 Γ (arr112 A B);lam112
 = λ t Tm112 var112 lam112 app → lam112 _ _ _ (t Tm112 var112 lam112 app)

app112 : ∀{Γ A B} → Tm112 Γ (arr112 A B) → Tm112 Γ A → Tm112 Γ B;app112
 = λ t u Tm112 var112 lam112 app112 →
     app112 _ _ _ (t Tm112 var112 lam112 app112) (u Tm112 var112 lam112 app112)

v0112 : ∀{Γ A} → Tm112 (snoc112 Γ A) A;v0112
 = var112 vz112

v1112 : ∀{Γ A B} → Tm112 (snoc112 (snoc112 Γ A) B) A;v1112
 = var112 (vs112 vz112)

v2112 : ∀{Γ A B C} → Tm112 (snoc112 (snoc112 (snoc112 Γ A) B) C) A;v2112
 = var112 (vs112 (vs112 vz112))

v3112 : ∀{Γ A B C D} → Tm112 (snoc112 (snoc112 (snoc112 (snoc112 Γ A) B) C) D) A;v3112
 = var112 (vs112 (vs112 (vs112 vz112)))

v4112 : ∀{Γ A B C D E} → Tm112 (snoc112 (snoc112 (snoc112 (snoc112 (snoc112 Γ A) B) C) D) E) A;v4112
 = var112 (vs112 (vs112 (vs112 (vs112 vz112))))

test112 : ∀{Γ A} → Tm112 Γ (arr112 (arr112 A A) (arr112 A A));test112
  = lam112 (lam112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 v0112)))))))
{-# OPTIONS --type-in-type #-}

Ty113 : Set; Ty113
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι113   : Ty113; ι113 = λ _ ι113 _ → ι113
arr113 : Ty113 → Ty113 → Ty113; arr113 = λ A B Ty113 ι113 arr113 → arr113 (A Ty113 ι113 arr113) (B Ty113 ι113 arr113)

Con113 : Set;Con113
 = (Con113 : Set)
   (nil  : Con113)
   (snoc : Con113 → Ty113 → Con113)
 → Con113

nil113 : Con113;nil113
 = λ Con113 nil113 snoc → nil113

snoc113 : Con113 → Ty113 → Con113;snoc113
 = λ Γ A Con113 nil113 snoc113 → snoc113 (Γ Con113 nil113 snoc113) A

Var113 : Con113 → Ty113 → Set;Var113
 = λ Γ A →
   (Var113 : Con113 → Ty113 → Set)
   (vz  : (Γ : _)(A : _) → Var113 (snoc113 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var113 Γ A → Var113 (snoc113 Γ B) A)
 → Var113 Γ A

vz113 : ∀{Γ A} → Var113 (snoc113 Γ A) A;vz113
 = λ Var113 vz113 vs → vz113 _ _

vs113 : ∀{Γ B A} → Var113 Γ A → Var113 (snoc113 Γ B) A;vs113
 = λ x Var113 vz113 vs113 → vs113 _ _ _ (x Var113 vz113 vs113)

Tm113 : Con113 → Ty113 → Set;Tm113
 = λ Γ A →
   (Tm113    : Con113 → Ty113 → Set)
   (var   : (Γ : _) (A : _) → Var113 Γ A → Tm113 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm113 (snoc113 Γ A) B → Tm113 Γ (arr113 A B))
   (app   : (Γ : _) (A B : _) → Tm113 Γ (arr113 A B) → Tm113 Γ A → Tm113 Γ B)
 → Tm113 Γ A

var113 : ∀{Γ A} → Var113 Γ A → Tm113 Γ A;var113
 = λ x Tm113 var113 lam app → var113 _ _ x

lam113 : ∀{Γ A B} → Tm113 (snoc113 Γ A) B → Tm113 Γ (arr113 A B);lam113
 = λ t Tm113 var113 lam113 app → lam113 _ _ _ (t Tm113 var113 lam113 app)

app113 : ∀{Γ A B} → Tm113 Γ (arr113 A B) → Tm113 Γ A → Tm113 Γ B;app113
 = λ t u Tm113 var113 lam113 app113 →
     app113 _ _ _ (t Tm113 var113 lam113 app113) (u Tm113 var113 lam113 app113)

v0113 : ∀{Γ A} → Tm113 (snoc113 Γ A) A;v0113
 = var113 vz113

v1113 : ∀{Γ A B} → Tm113 (snoc113 (snoc113 Γ A) B) A;v1113
 = var113 (vs113 vz113)

v2113 : ∀{Γ A B C} → Tm113 (snoc113 (snoc113 (snoc113 Γ A) B) C) A;v2113
 = var113 (vs113 (vs113 vz113))

v3113 : ∀{Γ A B C D} → Tm113 (snoc113 (snoc113 (snoc113 (snoc113 Γ A) B) C) D) A;v3113
 = var113 (vs113 (vs113 (vs113 vz113)))

v4113 : ∀{Γ A B C D E} → Tm113 (snoc113 (snoc113 (snoc113 (snoc113 (snoc113 Γ A) B) C) D) E) A;v4113
 = var113 (vs113 (vs113 (vs113 (vs113 vz113))))

test113 : ∀{Γ A} → Tm113 Γ (arr113 (arr113 A A) (arr113 A A));test113
  = lam113 (lam113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 v0113)))))))
{-# OPTIONS --type-in-type #-}

Ty114 : Set; Ty114
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι114   : Ty114; ι114 = λ _ ι114 _ → ι114
arr114 : Ty114 → Ty114 → Ty114; arr114 = λ A B Ty114 ι114 arr114 → arr114 (A Ty114 ι114 arr114) (B Ty114 ι114 arr114)

Con114 : Set;Con114
 = (Con114 : Set)
   (nil  : Con114)
   (snoc : Con114 → Ty114 → Con114)
 → Con114

nil114 : Con114;nil114
 = λ Con114 nil114 snoc → nil114

snoc114 : Con114 → Ty114 → Con114;snoc114
 = λ Γ A Con114 nil114 snoc114 → snoc114 (Γ Con114 nil114 snoc114) A

Var114 : Con114 → Ty114 → Set;Var114
 = λ Γ A →
   (Var114 : Con114 → Ty114 → Set)
   (vz  : (Γ : _)(A : _) → Var114 (snoc114 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var114 Γ A → Var114 (snoc114 Γ B) A)
 → Var114 Γ A

vz114 : ∀{Γ A} → Var114 (snoc114 Γ A) A;vz114
 = λ Var114 vz114 vs → vz114 _ _

vs114 : ∀{Γ B A} → Var114 Γ A → Var114 (snoc114 Γ B) A;vs114
 = λ x Var114 vz114 vs114 → vs114 _ _ _ (x Var114 vz114 vs114)

Tm114 : Con114 → Ty114 → Set;Tm114
 = λ Γ A →
   (Tm114    : Con114 → Ty114 → Set)
   (var   : (Γ : _) (A : _) → Var114 Γ A → Tm114 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm114 (snoc114 Γ A) B → Tm114 Γ (arr114 A B))
   (app   : (Γ : _) (A B : _) → Tm114 Γ (arr114 A B) → Tm114 Γ A → Tm114 Γ B)
 → Tm114 Γ A

var114 : ∀{Γ A} → Var114 Γ A → Tm114 Γ A;var114
 = λ x Tm114 var114 lam app → var114 _ _ x

lam114 : ∀{Γ A B} → Tm114 (snoc114 Γ A) B → Tm114 Γ (arr114 A B);lam114
 = λ t Tm114 var114 lam114 app → lam114 _ _ _ (t Tm114 var114 lam114 app)

app114 : ∀{Γ A B} → Tm114 Γ (arr114 A B) → Tm114 Γ A → Tm114 Γ B;app114
 = λ t u Tm114 var114 lam114 app114 →
     app114 _ _ _ (t Tm114 var114 lam114 app114) (u Tm114 var114 lam114 app114)

v0114 : ∀{Γ A} → Tm114 (snoc114 Γ A) A;v0114
 = var114 vz114

v1114 : ∀{Γ A B} → Tm114 (snoc114 (snoc114 Γ A) B) A;v1114
 = var114 (vs114 vz114)

v2114 : ∀{Γ A B C} → Tm114 (snoc114 (snoc114 (snoc114 Γ A) B) C) A;v2114
 = var114 (vs114 (vs114 vz114))

v3114 : ∀{Γ A B C D} → Tm114 (snoc114 (snoc114 (snoc114 (snoc114 Γ A) B) C) D) A;v3114
 = var114 (vs114 (vs114 (vs114 vz114)))

v4114 : ∀{Γ A B C D E} → Tm114 (snoc114 (snoc114 (snoc114 (snoc114 (snoc114 Γ A) B) C) D) E) A;v4114
 = var114 (vs114 (vs114 (vs114 (vs114 vz114))))

test114 : ∀{Γ A} → Tm114 Γ (arr114 (arr114 A A) (arr114 A A));test114
  = lam114 (lam114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 v0114)))))))
{-# OPTIONS --type-in-type #-}

Ty115 : Set; Ty115
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι115   : Ty115; ι115 = λ _ ι115 _ → ι115
arr115 : Ty115 → Ty115 → Ty115; arr115 = λ A B Ty115 ι115 arr115 → arr115 (A Ty115 ι115 arr115) (B Ty115 ι115 arr115)

Con115 : Set;Con115
 = (Con115 : Set)
   (nil  : Con115)
   (snoc : Con115 → Ty115 → Con115)
 → Con115

nil115 : Con115;nil115
 = λ Con115 nil115 snoc → nil115

snoc115 : Con115 → Ty115 → Con115;snoc115
 = λ Γ A Con115 nil115 snoc115 → snoc115 (Γ Con115 nil115 snoc115) A

Var115 : Con115 → Ty115 → Set;Var115
 = λ Γ A →
   (Var115 : Con115 → Ty115 → Set)
   (vz  : (Γ : _)(A : _) → Var115 (snoc115 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var115 Γ A → Var115 (snoc115 Γ B) A)
 → Var115 Γ A

vz115 : ∀{Γ A} → Var115 (snoc115 Γ A) A;vz115
 = λ Var115 vz115 vs → vz115 _ _

vs115 : ∀{Γ B A} → Var115 Γ A → Var115 (snoc115 Γ B) A;vs115
 = λ x Var115 vz115 vs115 → vs115 _ _ _ (x Var115 vz115 vs115)

Tm115 : Con115 → Ty115 → Set;Tm115
 = λ Γ A →
   (Tm115    : Con115 → Ty115 → Set)
   (var   : (Γ : _) (A : _) → Var115 Γ A → Tm115 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm115 (snoc115 Γ A) B → Tm115 Γ (arr115 A B))
   (app   : (Γ : _) (A B : _) → Tm115 Γ (arr115 A B) → Tm115 Γ A → Tm115 Γ B)
 → Tm115 Γ A

var115 : ∀{Γ A} → Var115 Γ A → Tm115 Γ A;var115
 = λ x Tm115 var115 lam app → var115 _ _ x

lam115 : ∀{Γ A B} → Tm115 (snoc115 Γ A) B → Tm115 Γ (arr115 A B);lam115
 = λ t Tm115 var115 lam115 app → lam115 _ _ _ (t Tm115 var115 lam115 app)

app115 : ∀{Γ A B} → Tm115 Γ (arr115 A B) → Tm115 Γ A → Tm115 Γ B;app115
 = λ t u Tm115 var115 lam115 app115 →
     app115 _ _ _ (t Tm115 var115 lam115 app115) (u Tm115 var115 lam115 app115)

v0115 : ∀{Γ A} → Tm115 (snoc115 Γ A) A;v0115
 = var115 vz115

v1115 : ∀{Γ A B} → Tm115 (snoc115 (snoc115 Γ A) B) A;v1115
 = var115 (vs115 vz115)

v2115 : ∀{Γ A B C} → Tm115 (snoc115 (snoc115 (snoc115 Γ A) B) C) A;v2115
 = var115 (vs115 (vs115 vz115))

v3115 : ∀{Γ A B C D} → Tm115 (snoc115 (snoc115 (snoc115 (snoc115 Γ A) B) C) D) A;v3115
 = var115 (vs115 (vs115 (vs115 vz115)))

v4115 : ∀{Γ A B C D E} → Tm115 (snoc115 (snoc115 (snoc115 (snoc115 (snoc115 Γ A) B) C) D) E) A;v4115
 = var115 (vs115 (vs115 (vs115 (vs115 vz115))))

test115 : ∀{Γ A} → Tm115 Γ (arr115 (arr115 A A) (arr115 A A));test115
  = lam115 (lam115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 v0115)))))))
{-# OPTIONS --type-in-type #-}

Ty116 : Set; Ty116
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι116   : Ty116; ι116 = λ _ ι116 _ → ι116
arr116 : Ty116 → Ty116 → Ty116; arr116 = λ A B Ty116 ι116 arr116 → arr116 (A Ty116 ι116 arr116) (B Ty116 ι116 arr116)

Con116 : Set;Con116
 = (Con116 : Set)
   (nil  : Con116)
   (snoc : Con116 → Ty116 → Con116)
 → Con116

nil116 : Con116;nil116
 = λ Con116 nil116 snoc → nil116

snoc116 : Con116 → Ty116 → Con116;snoc116
 = λ Γ A Con116 nil116 snoc116 → snoc116 (Γ Con116 nil116 snoc116) A

Var116 : Con116 → Ty116 → Set;Var116
 = λ Γ A →
   (Var116 : Con116 → Ty116 → Set)
   (vz  : (Γ : _)(A : _) → Var116 (snoc116 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var116 Γ A → Var116 (snoc116 Γ B) A)
 → Var116 Γ A

vz116 : ∀{Γ A} → Var116 (snoc116 Γ A) A;vz116
 = λ Var116 vz116 vs → vz116 _ _

vs116 : ∀{Γ B A} → Var116 Γ A → Var116 (snoc116 Γ B) A;vs116
 = λ x Var116 vz116 vs116 → vs116 _ _ _ (x Var116 vz116 vs116)

Tm116 : Con116 → Ty116 → Set;Tm116
 = λ Γ A →
   (Tm116    : Con116 → Ty116 → Set)
   (var   : (Γ : _) (A : _) → Var116 Γ A → Tm116 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm116 (snoc116 Γ A) B → Tm116 Γ (arr116 A B))
   (app   : (Γ : _) (A B : _) → Tm116 Γ (arr116 A B) → Tm116 Γ A → Tm116 Γ B)
 → Tm116 Γ A

var116 : ∀{Γ A} → Var116 Γ A → Tm116 Γ A;var116
 = λ x Tm116 var116 lam app → var116 _ _ x

lam116 : ∀{Γ A B} → Tm116 (snoc116 Γ A) B → Tm116 Γ (arr116 A B);lam116
 = λ t Tm116 var116 lam116 app → lam116 _ _ _ (t Tm116 var116 lam116 app)

app116 : ∀{Γ A B} → Tm116 Γ (arr116 A B) → Tm116 Γ A → Tm116 Γ B;app116
 = λ t u Tm116 var116 lam116 app116 →
     app116 _ _ _ (t Tm116 var116 lam116 app116) (u Tm116 var116 lam116 app116)

v0116 : ∀{Γ A} → Tm116 (snoc116 Γ A) A;v0116
 = var116 vz116

v1116 : ∀{Γ A B} → Tm116 (snoc116 (snoc116 Γ A) B) A;v1116
 = var116 (vs116 vz116)

v2116 : ∀{Γ A B C} → Tm116 (snoc116 (snoc116 (snoc116 Γ A) B) C) A;v2116
 = var116 (vs116 (vs116 vz116))

v3116 : ∀{Γ A B C D} → Tm116 (snoc116 (snoc116 (snoc116 (snoc116 Γ A) B) C) D) A;v3116
 = var116 (vs116 (vs116 (vs116 vz116)))

v4116 : ∀{Γ A B C D E} → Tm116 (snoc116 (snoc116 (snoc116 (snoc116 (snoc116 Γ A) B) C) D) E) A;v4116
 = var116 (vs116 (vs116 (vs116 (vs116 vz116))))

test116 : ∀{Γ A} → Tm116 Γ (arr116 (arr116 A A) (arr116 A A));test116
  = lam116 (lam116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 v0116)))))))
{-# OPTIONS --type-in-type #-}

Ty117 : Set; Ty117
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι117   : Ty117; ι117 = λ _ ι117 _ → ι117
arr117 : Ty117 → Ty117 → Ty117; arr117 = λ A B Ty117 ι117 arr117 → arr117 (A Ty117 ι117 arr117) (B Ty117 ι117 arr117)

Con117 : Set;Con117
 = (Con117 : Set)
   (nil  : Con117)
   (snoc : Con117 → Ty117 → Con117)
 → Con117

nil117 : Con117;nil117
 = λ Con117 nil117 snoc → nil117

snoc117 : Con117 → Ty117 → Con117;snoc117
 = λ Γ A Con117 nil117 snoc117 → snoc117 (Γ Con117 nil117 snoc117) A

Var117 : Con117 → Ty117 → Set;Var117
 = λ Γ A →
   (Var117 : Con117 → Ty117 → Set)
   (vz  : (Γ : _)(A : _) → Var117 (snoc117 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var117 Γ A → Var117 (snoc117 Γ B) A)
 → Var117 Γ A

vz117 : ∀{Γ A} → Var117 (snoc117 Γ A) A;vz117
 = λ Var117 vz117 vs → vz117 _ _

vs117 : ∀{Γ B A} → Var117 Γ A → Var117 (snoc117 Γ B) A;vs117
 = λ x Var117 vz117 vs117 → vs117 _ _ _ (x Var117 vz117 vs117)

Tm117 : Con117 → Ty117 → Set;Tm117
 = λ Γ A →
   (Tm117    : Con117 → Ty117 → Set)
   (var   : (Γ : _) (A : _) → Var117 Γ A → Tm117 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm117 (snoc117 Γ A) B → Tm117 Γ (arr117 A B))
   (app   : (Γ : _) (A B : _) → Tm117 Γ (arr117 A B) → Tm117 Γ A → Tm117 Γ B)
 → Tm117 Γ A

var117 : ∀{Γ A} → Var117 Γ A → Tm117 Γ A;var117
 = λ x Tm117 var117 lam app → var117 _ _ x

lam117 : ∀{Γ A B} → Tm117 (snoc117 Γ A) B → Tm117 Γ (arr117 A B);lam117
 = λ t Tm117 var117 lam117 app → lam117 _ _ _ (t Tm117 var117 lam117 app)

app117 : ∀{Γ A B} → Tm117 Γ (arr117 A B) → Tm117 Γ A → Tm117 Γ B;app117
 = λ t u Tm117 var117 lam117 app117 →
     app117 _ _ _ (t Tm117 var117 lam117 app117) (u Tm117 var117 lam117 app117)

v0117 : ∀{Γ A} → Tm117 (snoc117 Γ A) A;v0117
 = var117 vz117

v1117 : ∀{Γ A B} → Tm117 (snoc117 (snoc117 Γ A) B) A;v1117
 = var117 (vs117 vz117)

v2117 : ∀{Γ A B C} → Tm117 (snoc117 (snoc117 (snoc117 Γ A) B) C) A;v2117
 = var117 (vs117 (vs117 vz117))

v3117 : ∀{Γ A B C D} → Tm117 (snoc117 (snoc117 (snoc117 (snoc117 Γ A) B) C) D) A;v3117
 = var117 (vs117 (vs117 (vs117 vz117)))

v4117 : ∀{Γ A B C D E} → Tm117 (snoc117 (snoc117 (snoc117 (snoc117 (snoc117 Γ A) B) C) D) E) A;v4117
 = var117 (vs117 (vs117 (vs117 (vs117 vz117))))

test117 : ∀{Γ A} → Tm117 Γ (arr117 (arr117 A A) (arr117 A A));test117
  = lam117 (lam117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 v0117)))))))
{-# OPTIONS --type-in-type #-}

Ty118 : Set; Ty118
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι118   : Ty118; ι118 = λ _ ι118 _ → ι118
arr118 : Ty118 → Ty118 → Ty118; arr118 = λ A B Ty118 ι118 arr118 → arr118 (A Ty118 ι118 arr118) (B Ty118 ι118 arr118)

Con118 : Set;Con118
 = (Con118 : Set)
   (nil  : Con118)
   (snoc : Con118 → Ty118 → Con118)
 → Con118

nil118 : Con118;nil118
 = λ Con118 nil118 snoc → nil118

snoc118 : Con118 → Ty118 → Con118;snoc118
 = λ Γ A Con118 nil118 snoc118 → snoc118 (Γ Con118 nil118 snoc118) A

Var118 : Con118 → Ty118 → Set;Var118
 = λ Γ A →
   (Var118 : Con118 → Ty118 → Set)
   (vz  : (Γ : _)(A : _) → Var118 (snoc118 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var118 Γ A → Var118 (snoc118 Γ B) A)
 → Var118 Γ A

vz118 : ∀{Γ A} → Var118 (snoc118 Γ A) A;vz118
 = λ Var118 vz118 vs → vz118 _ _

vs118 : ∀{Γ B A} → Var118 Γ A → Var118 (snoc118 Γ B) A;vs118
 = λ x Var118 vz118 vs118 → vs118 _ _ _ (x Var118 vz118 vs118)

Tm118 : Con118 → Ty118 → Set;Tm118
 = λ Γ A →
   (Tm118    : Con118 → Ty118 → Set)
   (var   : (Γ : _) (A : _) → Var118 Γ A → Tm118 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm118 (snoc118 Γ A) B → Tm118 Γ (arr118 A B))
   (app   : (Γ : _) (A B : _) → Tm118 Γ (arr118 A B) → Tm118 Γ A → Tm118 Γ B)
 → Tm118 Γ A

var118 : ∀{Γ A} → Var118 Γ A → Tm118 Γ A;var118
 = λ x Tm118 var118 lam app → var118 _ _ x

lam118 : ∀{Γ A B} → Tm118 (snoc118 Γ A) B → Tm118 Γ (arr118 A B);lam118
 = λ t Tm118 var118 lam118 app → lam118 _ _ _ (t Tm118 var118 lam118 app)

app118 : ∀{Γ A B} → Tm118 Γ (arr118 A B) → Tm118 Γ A → Tm118 Γ B;app118
 = λ t u Tm118 var118 lam118 app118 →
     app118 _ _ _ (t Tm118 var118 lam118 app118) (u Tm118 var118 lam118 app118)

v0118 : ∀{Γ A} → Tm118 (snoc118 Γ A) A;v0118
 = var118 vz118

v1118 : ∀{Γ A B} → Tm118 (snoc118 (snoc118 Γ A) B) A;v1118
 = var118 (vs118 vz118)

v2118 : ∀{Γ A B C} → Tm118 (snoc118 (snoc118 (snoc118 Γ A) B) C) A;v2118
 = var118 (vs118 (vs118 vz118))

v3118 : ∀{Γ A B C D} → Tm118 (snoc118 (snoc118 (snoc118 (snoc118 Γ A) B) C) D) A;v3118
 = var118 (vs118 (vs118 (vs118 vz118)))

v4118 : ∀{Γ A B C D E} → Tm118 (snoc118 (snoc118 (snoc118 (snoc118 (snoc118 Γ A) B) C) D) E) A;v4118
 = var118 (vs118 (vs118 (vs118 (vs118 vz118))))

test118 : ∀{Γ A} → Tm118 Γ (arr118 (arr118 A A) (arr118 A A));test118
  = lam118 (lam118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 v0118)))))))
{-# OPTIONS --type-in-type #-}

Ty119 : Set; Ty119
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι119   : Ty119; ι119 = λ _ ι119 _ → ι119
arr119 : Ty119 → Ty119 → Ty119; arr119 = λ A B Ty119 ι119 arr119 → arr119 (A Ty119 ι119 arr119) (B Ty119 ι119 arr119)

Con119 : Set;Con119
 = (Con119 : Set)
   (nil  : Con119)
   (snoc : Con119 → Ty119 → Con119)
 → Con119

nil119 : Con119;nil119
 = λ Con119 nil119 snoc → nil119

snoc119 : Con119 → Ty119 → Con119;snoc119
 = λ Γ A Con119 nil119 snoc119 → snoc119 (Γ Con119 nil119 snoc119) A

Var119 : Con119 → Ty119 → Set;Var119
 = λ Γ A →
   (Var119 : Con119 → Ty119 → Set)
   (vz  : (Γ : _)(A : _) → Var119 (snoc119 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var119 Γ A → Var119 (snoc119 Γ B) A)
 → Var119 Γ A

vz119 : ∀{Γ A} → Var119 (snoc119 Γ A) A;vz119
 = λ Var119 vz119 vs → vz119 _ _

vs119 : ∀{Γ B A} → Var119 Γ A → Var119 (snoc119 Γ B) A;vs119
 = λ x Var119 vz119 vs119 → vs119 _ _ _ (x Var119 vz119 vs119)

Tm119 : Con119 → Ty119 → Set;Tm119
 = λ Γ A →
   (Tm119    : Con119 → Ty119 → Set)
   (var   : (Γ : _) (A : _) → Var119 Γ A → Tm119 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm119 (snoc119 Γ A) B → Tm119 Γ (arr119 A B))
   (app   : (Γ : _) (A B : _) → Tm119 Γ (arr119 A B) → Tm119 Γ A → Tm119 Γ B)
 → Tm119 Γ A

var119 : ∀{Γ A} → Var119 Γ A → Tm119 Γ A;var119
 = λ x Tm119 var119 lam app → var119 _ _ x

lam119 : ∀{Γ A B} → Tm119 (snoc119 Γ A) B → Tm119 Γ (arr119 A B);lam119
 = λ t Tm119 var119 lam119 app → lam119 _ _ _ (t Tm119 var119 lam119 app)

app119 : ∀{Γ A B} → Tm119 Γ (arr119 A B) → Tm119 Γ A → Tm119 Γ B;app119
 = λ t u Tm119 var119 lam119 app119 →
     app119 _ _ _ (t Tm119 var119 lam119 app119) (u Tm119 var119 lam119 app119)

v0119 : ∀{Γ A} → Tm119 (snoc119 Γ A) A;v0119
 = var119 vz119

v1119 : ∀{Γ A B} → Tm119 (snoc119 (snoc119 Γ A) B) A;v1119
 = var119 (vs119 vz119)

v2119 : ∀{Γ A B C} → Tm119 (snoc119 (snoc119 (snoc119 Γ A) B) C) A;v2119
 = var119 (vs119 (vs119 vz119))

v3119 : ∀{Γ A B C D} → Tm119 (snoc119 (snoc119 (snoc119 (snoc119 Γ A) B) C) D) A;v3119
 = var119 (vs119 (vs119 (vs119 vz119)))

v4119 : ∀{Γ A B C D E} → Tm119 (snoc119 (snoc119 (snoc119 (snoc119 (snoc119 Γ A) B) C) D) E) A;v4119
 = var119 (vs119 (vs119 (vs119 (vs119 vz119))))

test119 : ∀{Γ A} → Tm119 Γ (arr119 (arr119 A A) (arr119 A A));test119
  = lam119 (lam119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 v0119)))))))
{-# OPTIONS --type-in-type #-}

Ty120 : Set; Ty120
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι120   : Ty120; ι120 = λ _ ι120 _ → ι120
arr120 : Ty120 → Ty120 → Ty120; arr120 = λ A B Ty120 ι120 arr120 → arr120 (A Ty120 ι120 arr120) (B Ty120 ι120 arr120)

Con120 : Set;Con120
 = (Con120 : Set)
   (nil  : Con120)
   (snoc : Con120 → Ty120 → Con120)
 → Con120

nil120 : Con120;nil120
 = λ Con120 nil120 snoc → nil120

snoc120 : Con120 → Ty120 → Con120;snoc120
 = λ Γ A Con120 nil120 snoc120 → snoc120 (Γ Con120 nil120 snoc120) A

Var120 : Con120 → Ty120 → Set;Var120
 = λ Γ A →
   (Var120 : Con120 → Ty120 → Set)
   (vz  : (Γ : _)(A : _) → Var120 (snoc120 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var120 Γ A → Var120 (snoc120 Γ B) A)
 → Var120 Γ A

vz120 : ∀{Γ A} → Var120 (snoc120 Γ A) A;vz120
 = λ Var120 vz120 vs → vz120 _ _

vs120 : ∀{Γ B A} → Var120 Γ A → Var120 (snoc120 Γ B) A;vs120
 = λ x Var120 vz120 vs120 → vs120 _ _ _ (x Var120 vz120 vs120)

Tm120 : Con120 → Ty120 → Set;Tm120
 = λ Γ A →
   (Tm120    : Con120 → Ty120 → Set)
   (var   : (Γ : _) (A : _) → Var120 Γ A → Tm120 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm120 (snoc120 Γ A) B → Tm120 Γ (arr120 A B))
   (app   : (Γ : _) (A B : _) → Tm120 Γ (arr120 A B) → Tm120 Γ A → Tm120 Γ B)
 → Tm120 Γ A

var120 : ∀{Γ A} → Var120 Γ A → Tm120 Γ A;var120
 = λ x Tm120 var120 lam app → var120 _ _ x

lam120 : ∀{Γ A B} → Tm120 (snoc120 Γ A) B → Tm120 Γ (arr120 A B);lam120
 = λ t Tm120 var120 lam120 app → lam120 _ _ _ (t Tm120 var120 lam120 app)

app120 : ∀{Γ A B} → Tm120 Γ (arr120 A B) → Tm120 Γ A → Tm120 Γ B;app120
 = λ t u Tm120 var120 lam120 app120 →
     app120 _ _ _ (t Tm120 var120 lam120 app120) (u Tm120 var120 lam120 app120)

v0120 : ∀{Γ A} → Tm120 (snoc120 Γ A) A;v0120
 = var120 vz120

v1120 : ∀{Γ A B} → Tm120 (snoc120 (snoc120 Γ A) B) A;v1120
 = var120 (vs120 vz120)

v2120 : ∀{Γ A B C} → Tm120 (snoc120 (snoc120 (snoc120 Γ A) B) C) A;v2120
 = var120 (vs120 (vs120 vz120))

v3120 : ∀{Γ A B C D} → Tm120 (snoc120 (snoc120 (snoc120 (snoc120 Γ A) B) C) D) A;v3120
 = var120 (vs120 (vs120 (vs120 vz120)))

v4120 : ∀{Γ A B C D E} → Tm120 (snoc120 (snoc120 (snoc120 (snoc120 (snoc120 Γ A) B) C) D) E) A;v4120
 = var120 (vs120 (vs120 (vs120 (vs120 vz120))))

test120 : ∀{Γ A} → Tm120 Γ (arr120 (arr120 A A) (arr120 A A));test120
  = lam120 (lam120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 v0120)))))))
{-# OPTIONS --type-in-type #-}

Ty121 : Set; Ty121
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι121   : Ty121; ι121 = λ _ ι121 _ → ι121
arr121 : Ty121 → Ty121 → Ty121; arr121 = λ A B Ty121 ι121 arr121 → arr121 (A Ty121 ι121 arr121) (B Ty121 ι121 arr121)

Con121 : Set;Con121
 = (Con121 : Set)
   (nil  : Con121)
   (snoc : Con121 → Ty121 → Con121)
 → Con121

nil121 : Con121;nil121
 = λ Con121 nil121 snoc → nil121

snoc121 : Con121 → Ty121 → Con121;snoc121
 = λ Γ A Con121 nil121 snoc121 → snoc121 (Γ Con121 nil121 snoc121) A

Var121 : Con121 → Ty121 → Set;Var121
 = λ Γ A →
   (Var121 : Con121 → Ty121 → Set)
   (vz  : (Γ : _)(A : _) → Var121 (snoc121 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var121 Γ A → Var121 (snoc121 Γ B) A)
 → Var121 Γ A

vz121 : ∀{Γ A} → Var121 (snoc121 Γ A) A;vz121
 = λ Var121 vz121 vs → vz121 _ _

vs121 : ∀{Γ B A} → Var121 Γ A → Var121 (snoc121 Γ B) A;vs121
 = λ x Var121 vz121 vs121 → vs121 _ _ _ (x Var121 vz121 vs121)

Tm121 : Con121 → Ty121 → Set;Tm121
 = λ Γ A →
   (Tm121    : Con121 → Ty121 → Set)
   (var   : (Γ : _) (A : _) → Var121 Γ A → Tm121 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm121 (snoc121 Γ A) B → Tm121 Γ (arr121 A B))
   (app   : (Γ : _) (A B : _) → Tm121 Γ (arr121 A B) → Tm121 Γ A → Tm121 Γ B)
 → Tm121 Γ A

var121 : ∀{Γ A} → Var121 Γ A → Tm121 Γ A;var121
 = λ x Tm121 var121 lam app → var121 _ _ x

lam121 : ∀{Γ A B} → Tm121 (snoc121 Γ A) B → Tm121 Γ (arr121 A B);lam121
 = λ t Tm121 var121 lam121 app → lam121 _ _ _ (t Tm121 var121 lam121 app)

app121 : ∀{Γ A B} → Tm121 Γ (arr121 A B) → Tm121 Γ A → Tm121 Γ B;app121
 = λ t u Tm121 var121 lam121 app121 →
     app121 _ _ _ (t Tm121 var121 lam121 app121) (u Tm121 var121 lam121 app121)

v0121 : ∀{Γ A} → Tm121 (snoc121 Γ A) A;v0121
 = var121 vz121

v1121 : ∀{Γ A B} → Tm121 (snoc121 (snoc121 Γ A) B) A;v1121
 = var121 (vs121 vz121)

v2121 : ∀{Γ A B C} → Tm121 (snoc121 (snoc121 (snoc121 Γ A) B) C) A;v2121
 = var121 (vs121 (vs121 vz121))

v3121 : ∀{Γ A B C D} → Tm121 (snoc121 (snoc121 (snoc121 (snoc121 Γ A) B) C) D) A;v3121
 = var121 (vs121 (vs121 (vs121 vz121)))

v4121 : ∀{Γ A B C D E} → Tm121 (snoc121 (snoc121 (snoc121 (snoc121 (snoc121 Γ A) B) C) D) E) A;v4121
 = var121 (vs121 (vs121 (vs121 (vs121 vz121))))

test121 : ∀{Γ A} → Tm121 Γ (arr121 (arr121 A A) (arr121 A A));test121
  = lam121 (lam121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 v0121)))))))
{-# OPTIONS --type-in-type #-}

Ty122 : Set; Ty122
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι122   : Ty122; ι122 = λ _ ι122 _ → ι122
arr122 : Ty122 → Ty122 → Ty122; arr122 = λ A B Ty122 ι122 arr122 → arr122 (A Ty122 ι122 arr122) (B Ty122 ι122 arr122)

Con122 : Set;Con122
 = (Con122 : Set)
   (nil  : Con122)
   (snoc : Con122 → Ty122 → Con122)
 → Con122

nil122 : Con122;nil122
 = λ Con122 nil122 snoc → nil122

snoc122 : Con122 → Ty122 → Con122;snoc122
 = λ Γ A Con122 nil122 snoc122 → snoc122 (Γ Con122 nil122 snoc122) A

Var122 : Con122 → Ty122 → Set;Var122
 = λ Γ A →
   (Var122 : Con122 → Ty122 → Set)
   (vz  : (Γ : _)(A : _) → Var122 (snoc122 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var122 Γ A → Var122 (snoc122 Γ B) A)
 → Var122 Γ A

vz122 : ∀{Γ A} → Var122 (snoc122 Γ A) A;vz122
 = λ Var122 vz122 vs → vz122 _ _

vs122 : ∀{Γ B A} → Var122 Γ A → Var122 (snoc122 Γ B) A;vs122
 = λ x Var122 vz122 vs122 → vs122 _ _ _ (x Var122 vz122 vs122)

Tm122 : Con122 → Ty122 → Set;Tm122
 = λ Γ A →
   (Tm122    : Con122 → Ty122 → Set)
   (var   : (Γ : _) (A : _) → Var122 Γ A → Tm122 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm122 (snoc122 Γ A) B → Tm122 Γ (arr122 A B))
   (app   : (Γ : _) (A B : _) → Tm122 Γ (arr122 A B) → Tm122 Γ A → Tm122 Γ B)
 → Tm122 Γ A

var122 : ∀{Γ A} → Var122 Γ A → Tm122 Γ A;var122
 = λ x Tm122 var122 lam app → var122 _ _ x

lam122 : ∀{Γ A B} → Tm122 (snoc122 Γ A) B → Tm122 Γ (arr122 A B);lam122
 = λ t Tm122 var122 lam122 app → lam122 _ _ _ (t Tm122 var122 lam122 app)

app122 : ∀{Γ A B} → Tm122 Γ (arr122 A B) → Tm122 Γ A → Tm122 Γ B;app122
 = λ t u Tm122 var122 lam122 app122 →
     app122 _ _ _ (t Tm122 var122 lam122 app122) (u Tm122 var122 lam122 app122)

v0122 : ∀{Γ A} → Tm122 (snoc122 Γ A) A;v0122
 = var122 vz122

v1122 : ∀{Γ A B} → Tm122 (snoc122 (snoc122 Γ A) B) A;v1122
 = var122 (vs122 vz122)

v2122 : ∀{Γ A B C} → Tm122 (snoc122 (snoc122 (snoc122 Γ A) B) C) A;v2122
 = var122 (vs122 (vs122 vz122))

v3122 : ∀{Γ A B C D} → Tm122 (snoc122 (snoc122 (snoc122 (snoc122 Γ A) B) C) D) A;v3122
 = var122 (vs122 (vs122 (vs122 vz122)))

v4122 : ∀{Γ A B C D E} → Tm122 (snoc122 (snoc122 (snoc122 (snoc122 (snoc122 Γ A) B) C) D) E) A;v4122
 = var122 (vs122 (vs122 (vs122 (vs122 vz122))))

test122 : ∀{Γ A} → Tm122 Γ (arr122 (arr122 A A) (arr122 A A));test122
  = lam122 (lam122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 v0122)))))))
{-# OPTIONS --type-in-type #-}

Ty123 : Set; Ty123
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι123   : Ty123; ι123 = λ _ ι123 _ → ι123
arr123 : Ty123 → Ty123 → Ty123; arr123 = λ A B Ty123 ι123 arr123 → arr123 (A Ty123 ι123 arr123) (B Ty123 ι123 arr123)

Con123 : Set;Con123
 = (Con123 : Set)
   (nil  : Con123)
   (snoc : Con123 → Ty123 → Con123)
 → Con123

nil123 : Con123;nil123
 = λ Con123 nil123 snoc → nil123

snoc123 : Con123 → Ty123 → Con123;snoc123
 = λ Γ A Con123 nil123 snoc123 → snoc123 (Γ Con123 nil123 snoc123) A

Var123 : Con123 → Ty123 → Set;Var123
 = λ Γ A →
   (Var123 : Con123 → Ty123 → Set)
   (vz  : (Γ : _)(A : _) → Var123 (snoc123 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var123 Γ A → Var123 (snoc123 Γ B) A)
 → Var123 Γ A

vz123 : ∀{Γ A} → Var123 (snoc123 Γ A) A;vz123
 = λ Var123 vz123 vs → vz123 _ _

vs123 : ∀{Γ B A} → Var123 Γ A → Var123 (snoc123 Γ B) A;vs123
 = λ x Var123 vz123 vs123 → vs123 _ _ _ (x Var123 vz123 vs123)

Tm123 : Con123 → Ty123 → Set;Tm123
 = λ Γ A →
   (Tm123    : Con123 → Ty123 → Set)
   (var   : (Γ : _) (A : _) → Var123 Γ A → Tm123 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm123 (snoc123 Γ A) B → Tm123 Γ (arr123 A B))
   (app   : (Γ : _) (A B : _) → Tm123 Γ (arr123 A B) → Tm123 Γ A → Tm123 Γ B)
 → Tm123 Γ A

var123 : ∀{Γ A} → Var123 Γ A → Tm123 Γ A;var123
 = λ x Tm123 var123 lam app → var123 _ _ x

lam123 : ∀{Γ A B} → Tm123 (snoc123 Γ A) B → Tm123 Γ (arr123 A B);lam123
 = λ t Tm123 var123 lam123 app → lam123 _ _ _ (t Tm123 var123 lam123 app)

app123 : ∀{Γ A B} → Tm123 Γ (arr123 A B) → Tm123 Γ A → Tm123 Γ B;app123
 = λ t u Tm123 var123 lam123 app123 →
     app123 _ _ _ (t Tm123 var123 lam123 app123) (u Tm123 var123 lam123 app123)

v0123 : ∀{Γ A} → Tm123 (snoc123 Γ A) A;v0123
 = var123 vz123

v1123 : ∀{Γ A B} → Tm123 (snoc123 (snoc123 Γ A) B) A;v1123
 = var123 (vs123 vz123)

v2123 : ∀{Γ A B C} → Tm123 (snoc123 (snoc123 (snoc123 Γ A) B) C) A;v2123
 = var123 (vs123 (vs123 vz123))

v3123 : ∀{Γ A B C D} → Tm123 (snoc123 (snoc123 (snoc123 (snoc123 Γ A) B) C) D) A;v3123
 = var123 (vs123 (vs123 (vs123 vz123)))

v4123 : ∀{Γ A B C D E} → Tm123 (snoc123 (snoc123 (snoc123 (snoc123 (snoc123 Γ A) B) C) D) E) A;v4123
 = var123 (vs123 (vs123 (vs123 (vs123 vz123))))

test123 : ∀{Γ A} → Tm123 Γ (arr123 (arr123 A A) (arr123 A A));test123
  = lam123 (lam123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 v0123)))))))
{-# OPTIONS --type-in-type #-}

Ty124 : Set; Ty124
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι124   : Ty124; ι124 = λ _ ι124 _ → ι124
arr124 : Ty124 → Ty124 → Ty124; arr124 = λ A B Ty124 ι124 arr124 → arr124 (A Ty124 ι124 arr124) (B Ty124 ι124 arr124)

Con124 : Set;Con124
 = (Con124 : Set)
   (nil  : Con124)
   (snoc : Con124 → Ty124 → Con124)
 → Con124

nil124 : Con124;nil124
 = λ Con124 nil124 snoc → nil124

snoc124 : Con124 → Ty124 → Con124;snoc124
 = λ Γ A Con124 nil124 snoc124 → snoc124 (Γ Con124 nil124 snoc124) A

Var124 : Con124 → Ty124 → Set;Var124
 = λ Γ A →
   (Var124 : Con124 → Ty124 → Set)
   (vz  : (Γ : _)(A : _) → Var124 (snoc124 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var124 Γ A → Var124 (snoc124 Γ B) A)
 → Var124 Γ A

vz124 : ∀{Γ A} → Var124 (snoc124 Γ A) A;vz124
 = λ Var124 vz124 vs → vz124 _ _

vs124 : ∀{Γ B A} → Var124 Γ A → Var124 (snoc124 Γ B) A;vs124
 = λ x Var124 vz124 vs124 → vs124 _ _ _ (x Var124 vz124 vs124)

Tm124 : Con124 → Ty124 → Set;Tm124
 = λ Γ A →
   (Tm124    : Con124 → Ty124 → Set)
   (var   : (Γ : _) (A : _) → Var124 Γ A → Tm124 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm124 (snoc124 Γ A) B → Tm124 Γ (arr124 A B))
   (app   : (Γ : _) (A B : _) → Tm124 Γ (arr124 A B) → Tm124 Γ A → Tm124 Γ B)
 → Tm124 Γ A

var124 : ∀{Γ A} → Var124 Γ A → Tm124 Γ A;var124
 = λ x Tm124 var124 lam app → var124 _ _ x

lam124 : ∀{Γ A B} → Tm124 (snoc124 Γ A) B → Tm124 Γ (arr124 A B);lam124
 = λ t Tm124 var124 lam124 app → lam124 _ _ _ (t Tm124 var124 lam124 app)

app124 : ∀{Γ A B} → Tm124 Γ (arr124 A B) → Tm124 Γ A → Tm124 Γ B;app124
 = λ t u Tm124 var124 lam124 app124 →
     app124 _ _ _ (t Tm124 var124 lam124 app124) (u Tm124 var124 lam124 app124)

v0124 : ∀{Γ A} → Tm124 (snoc124 Γ A) A;v0124
 = var124 vz124

v1124 : ∀{Γ A B} → Tm124 (snoc124 (snoc124 Γ A) B) A;v1124
 = var124 (vs124 vz124)

v2124 : ∀{Γ A B C} → Tm124 (snoc124 (snoc124 (snoc124 Γ A) B) C) A;v2124
 = var124 (vs124 (vs124 vz124))

v3124 : ∀{Γ A B C D} → Tm124 (snoc124 (snoc124 (snoc124 (snoc124 Γ A) B) C) D) A;v3124
 = var124 (vs124 (vs124 (vs124 vz124)))

v4124 : ∀{Γ A B C D E} → Tm124 (snoc124 (snoc124 (snoc124 (snoc124 (snoc124 Γ A) B) C) D) E) A;v4124
 = var124 (vs124 (vs124 (vs124 (vs124 vz124))))

test124 : ∀{Γ A} → Tm124 Γ (arr124 (arr124 A A) (arr124 A A));test124
  = lam124 (lam124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 v0124)))))))
{-# OPTIONS --type-in-type #-}

Ty125 : Set; Ty125
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι125   : Ty125; ι125 = λ _ ι125 _ → ι125
arr125 : Ty125 → Ty125 → Ty125; arr125 = λ A B Ty125 ι125 arr125 → arr125 (A Ty125 ι125 arr125) (B Ty125 ι125 arr125)

Con125 : Set;Con125
 = (Con125 : Set)
   (nil  : Con125)
   (snoc : Con125 → Ty125 → Con125)
 → Con125

nil125 : Con125;nil125
 = λ Con125 nil125 snoc → nil125

snoc125 : Con125 → Ty125 → Con125;snoc125
 = λ Γ A Con125 nil125 snoc125 → snoc125 (Γ Con125 nil125 snoc125) A

Var125 : Con125 → Ty125 → Set;Var125
 = λ Γ A →
   (Var125 : Con125 → Ty125 → Set)
   (vz  : (Γ : _)(A : _) → Var125 (snoc125 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var125 Γ A → Var125 (snoc125 Γ B) A)
 → Var125 Γ A

vz125 : ∀{Γ A} → Var125 (snoc125 Γ A) A;vz125
 = λ Var125 vz125 vs → vz125 _ _

vs125 : ∀{Γ B A} → Var125 Γ A → Var125 (snoc125 Γ B) A;vs125
 = λ x Var125 vz125 vs125 → vs125 _ _ _ (x Var125 vz125 vs125)

Tm125 : Con125 → Ty125 → Set;Tm125
 = λ Γ A →
   (Tm125    : Con125 → Ty125 → Set)
   (var   : (Γ : _) (A : _) → Var125 Γ A → Tm125 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm125 (snoc125 Γ A) B → Tm125 Γ (arr125 A B))
   (app   : (Γ : _) (A B : _) → Tm125 Γ (arr125 A B) → Tm125 Γ A → Tm125 Γ B)
 → Tm125 Γ A

var125 : ∀{Γ A} → Var125 Γ A → Tm125 Γ A;var125
 = λ x Tm125 var125 lam app → var125 _ _ x

lam125 : ∀{Γ A B} → Tm125 (snoc125 Γ A) B → Tm125 Γ (arr125 A B);lam125
 = λ t Tm125 var125 lam125 app → lam125 _ _ _ (t Tm125 var125 lam125 app)

app125 : ∀{Γ A B} → Tm125 Γ (arr125 A B) → Tm125 Γ A → Tm125 Γ B;app125
 = λ t u Tm125 var125 lam125 app125 →
     app125 _ _ _ (t Tm125 var125 lam125 app125) (u Tm125 var125 lam125 app125)

v0125 : ∀{Γ A} → Tm125 (snoc125 Γ A) A;v0125
 = var125 vz125

v1125 : ∀{Γ A B} → Tm125 (snoc125 (snoc125 Γ A) B) A;v1125
 = var125 (vs125 vz125)

v2125 : ∀{Γ A B C} → Tm125 (snoc125 (snoc125 (snoc125 Γ A) B) C) A;v2125
 = var125 (vs125 (vs125 vz125))

v3125 : ∀{Γ A B C D} → Tm125 (snoc125 (snoc125 (snoc125 (snoc125 Γ A) B) C) D) A;v3125
 = var125 (vs125 (vs125 (vs125 vz125)))

v4125 : ∀{Γ A B C D E} → Tm125 (snoc125 (snoc125 (snoc125 (snoc125 (snoc125 Γ A) B) C) D) E) A;v4125
 = var125 (vs125 (vs125 (vs125 (vs125 vz125))))

test125 : ∀{Γ A} → Tm125 Γ (arr125 (arr125 A A) (arr125 A A));test125
  = lam125 (lam125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 v0125)))))))
{-# OPTIONS --type-in-type #-}

Ty126 : Set; Ty126
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι126   : Ty126; ι126 = λ _ ι126 _ → ι126
arr126 : Ty126 → Ty126 → Ty126; arr126 = λ A B Ty126 ι126 arr126 → arr126 (A Ty126 ι126 arr126) (B Ty126 ι126 arr126)

Con126 : Set;Con126
 = (Con126 : Set)
   (nil  : Con126)
   (snoc : Con126 → Ty126 → Con126)
 → Con126

nil126 : Con126;nil126
 = λ Con126 nil126 snoc → nil126

snoc126 : Con126 → Ty126 → Con126;snoc126
 = λ Γ A Con126 nil126 snoc126 → snoc126 (Γ Con126 nil126 snoc126) A

Var126 : Con126 → Ty126 → Set;Var126
 = λ Γ A →
   (Var126 : Con126 → Ty126 → Set)
   (vz  : (Γ : _)(A : _) → Var126 (snoc126 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var126 Γ A → Var126 (snoc126 Γ B) A)
 → Var126 Γ A

vz126 : ∀{Γ A} → Var126 (snoc126 Γ A) A;vz126
 = λ Var126 vz126 vs → vz126 _ _

vs126 : ∀{Γ B A} → Var126 Γ A → Var126 (snoc126 Γ B) A;vs126
 = λ x Var126 vz126 vs126 → vs126 _ _ _ (x Var126 vz126 vs126)

Tm126 : Con126 → Ty126 → Set;Tm126
 = λ Γ A →
   (Tm126    : Con126 → Ty126 → Set)
   (var   : (Γ : _) (A : _) → Var126 Γ A → Tm126 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm126 (snoc126 Γ A) B → Tm126 Γ (arr126 A B))
   (app   : (Γ : _) (A B : _) → Tm126 Γ (arr126 A B) → Tm126 Γ A → Tm126 Γ B)
 → Tm126 Γ A

var126 : ∀{Γ A} → Var126 Γ A → Tm126 Γ A;var126
 = λ x Tm126 var126 lam app → var126 _ _ x

lam126 : ∀{Γ A B} → Tm126 (snoc126 Γ A) B → Tm126 Γ (arr126 A B);lam126
 = λ t Tm126 var126 lam126 app → lam126 _ _ _ (t Tm126 var126 lam126 app)

app126 : ∀{Γ A B} → Tm126 Γ (arr126 A B) → Tm126 Γ A → Tm126 Γ B;app126
 = λ t u Tm126 var126 lam126 app126 →
     app126 _ _ _ (t Tm126 var126 lam126 app126) (u Tm126 var126 lam126 app126)

v0126 : ∀{Γ A} → Tm126 (snoc126 Γ A) A;v0126
 = var126 vz126

v1126 : ∀{Γ A B} → Tm126 (snoc126 (snoc126 Γ A) B) A;v1126
 = var126 (vs126 vz126)

v2126 : ∀{Γ A B C} → Tm126 (snoc126 (snoc126 (snoc126 Γ A) B) C) A;v2126
 = var126 (vs126 (vs126 vz126))

v3126 : ∀{Γ A B C D} → Tm126 (snoc126 (snoc126 (snoc126 (snoc126 Γ A) B) C) D) A;v3126
 = var126 (vs126 (vs126 (vs126 vz126)))

v4126 : ∀{Γ A B C D E} → Tm126 (snoc126 (snoc126 (snoc126 (snoc126 (snoc126 Γ A) B) C) D) E) A;v4126
 = var126 (vs126 (vs126 (vs126 (vs126 vz126))))

test126 : ∀{Γ A} → Tm126 Γ (arr126 (arr126 A A) (arr126 A A));test126
  = lam126 (lam126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 v0126)))))))
{-# OPTIONS --type-in-type #-}

Ty127 : Set; Ty127
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι127   : Ty127; ι127 = λ _ ι127 _ → ι127
arr127 : Ty127 → Ty127 → Ty127; arr127 = λ A B Ty127 ι127 arr127 → arr127 (A Ty127 ι127 arr127) (B Ty127 ι127 arr127)

Con127 : Set;Con127
 = (Con127 : Set)
   (nil  : Con127)
   (snoc : Con127 → Ty127 → Con127)
 → Con127

nil127 : Con127;nil127
 = λ Con127 nil127 snoc → nil127

snoc127 : Con127 → Ty127 → Con127;snoc127
 = λ Γ A Con127 nil127 snoc127 → snoc127 (Γ Con127 nil127 snoc127) A

Var127 : Con127 → Ty127 → Set;Var127
 = λ Γ A →
   (Var127 : Con127 → Ty127 → Set)
   (vz  : (Γ : _)(A : _) → Var127 (snoc127 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var127 Γ A → Var127 (snoc127 Γ B) A)
 → Var127 Γ A

vz127 : ∀{Γ A} → Var127 (snoc127 Γ A) A;vz127
 = λ Var127 vz127 vs → vz127 _ _

vs127 : ∀{Γ B A} → Var127 Γ A → Var127 (snoc127 Γ B) A;vs127
 = λ x Var127 vz127 vs127 → vs127 _ _ _ (x Var127 vz127 vs127)

Tm127 : Con127 → Ty127 → Set;Tm127
 = λ Γ A →
   (Tm127    : Con127 → Ty127 → Set)
   (var   : (Γ : _) (A : _) → Var127 Γ A → Tm127 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm127 (snoc127 Γ A) B → Tm127 Γ (arr127 A B))
   (app   : (Γ : _) (A B : _) → Tm127 Γ (arr127 A B) → Tm127 Γ A → Tm127 Γ B)
 → Tm127 Γ A

var127 : ∀{Γ A} → Var127 Γ A → Tm127 Γ A;var127
 = λ x Tm127 var127 lam app → var127 _ _ x

lam127 : ∀{Γ A B} → Tm127 (snoc127 Γ A) B → Tm127 Γ (arr127 A B);lam127
 = λ t Tm127 var127 lam127 app → lam127 _ _ _ (t Tm127 var127 lam127 app)

app127 : ∀{Γ A B} → Tm127 Γ (arr127 A B) → Tm127 Γ A → Tm127 Γ B;app127
 = λ t u Tm127 var127 lam127 app127 →
     app127 _ _ _ (t Tm127 var127 lam127 app127) (u Tm127 var127 lam127 app127)

v0127 : ∀{Γ A} → Tm127 (snoc127 Γ A) A;v0127
 = var127 vz127

v1127 : ∀{Γ A B} → Tm127 (snoc127 (snoc127 Γ A) B) A;v1127
 = var127 (vs127 vz127)

v2127 : ∀{Γ A B C} → Tm127 (snoc127 (snoc127 (snoc127 Γ A) B) C) A;v2127
 = var127 (vs127 (vs127 vz127))

v3127 : ∀{Γ A B C D} → Tm127 (snoc127 (snoc127 (snoc127 (snoc127 Γ A) B) C) D) A;v3127
 = var127 (vs127 (vs127 (vs127 vz127)))

v4127 : ∀{Γ A B C D E} → Tm127 (snoc127 (snoc127 (snoc127 (snoc127 (snoc127 Γ A) B) C) D) E) A;v4127
 = var127 (vs127 (vs127 (vs127 (vs127 vz127))))

test127 : ∀{Γ A} → Tm127 Γ (arr127 (arr127 A A) (arr127 A A));test127
  = lam127 (lam127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 v0127)))))))
{-# OPTIONS --type-in-type #-}

Ty128 : Set; Ty128
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι128   : Ty128; ι128 = λ _ ι128 _ → ι128
arr128 : Ty128 → Ty128 → Ty128; arr128 = λ A B Ty128 ι128 arr128 → arr128 (A Ty128 ι128 arr128) (B Ty128 ι128 arr128)

Con128 : Set;Con128
 = (Con128 : Set)
   (nil  : Con128)
   (snoc : Con128 → Ty128 → Con128)
 → Con128

nil128 : Con128;nil128
 = λ Con128 nil128 snoc → nil128

snoc128 : Con128 → Ty128 → Con128;snoc128
 = λ Γ A Con128 nil128 snoc128 → snoc128 (Γ Con128 nil128 snoc128) A

Var128 : Con128 → Ty128 → Set;Var128
 = λ Γ A →
   (Var128 : Con128 → Ty128 → Set)
   (vz  : (Γ : _)(A : _) → Var128 (snoc128 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var128 Γ A → Var128 (snoc128 Γ B) A)
 → Var128 Γ A

vz128 : ∀{Γ A} → Var128 (snoc128 Γ A) A;vz128
 = λ Var128 vz128 vs → vz128 _ _

vs128 : ∀{Γ B A} → Var128 Γ A → Var128 (snoc128 Γ B) A;vs128
 = λ x Var128 vz128 vs128 → vs128 _ _ _ (x Var128 vz128 vs128)

Tm128 : Con128 → Ty128 → Set;Tm128
 = λ Γ A →
   (Tm128    : Con128 → Ty128 → Set)
   (var   : (Γ : _) (A : _) → Var128 Γ A → Tm128 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm128 (snoc128 Γ A) B → Tm128 Γ (arr128 A B))
   (app   : (Γ : _) (A B : _) → Tm128 Γ (arr128 A B) → Tm128 Γ A → Tm128 Γ B)
 → Tm128 Γ A

var128 : ∀{Γ A} → Var128 Γ A → Tm128 Γ A;var128
 = λ x Tm128 var128 lam app → var128 _ _ x

lam128 : ∀{Γ A B} → Tm128 (snoc128 Γ A) B → Tm128 Γ (arr128 A B);lam128
 = λ t Tm128 var128 lam128 app → lam128 _ _ _ (t Tm128 var128 lam128 app)

app128 : ∀{Γ A B} → Tm128 Γ (arr128 A B) → Tm128 Γ A → Tm128 Γ B;app128
 = λ t u Tm128 var128 lam128 app128 →
     app128 _ _ _ (t Tm128 var128 lam128 app128) (u Tm128 var128 lam128 app128)

v0128 : ∀{Γ A} → Tm128 (snoc128 Γ A) A;v0128
 = var128 vz128

v1128 : ∀{Γ A B} → Tm128 (snoc128 (snoc128 Γ A) B) A;v1128
 = var128 (vs128 vz128)

v2128 : ∀{Γ A B C} → Tm128 (snoc128 (snoc128 (snoc128 Γ A) B) C) A;v2128
 = var128 (vs128 (vs128 vz128))

v3128 : ∀{Γ A B C D} → Tm128 (snoc128 (snoc128 (snoc128 (snoc128 Γ A) B) C) D) A;v3128
 = var128 (vs128 (vs128 (vs128 vz128)))

v4128 : ∀{Γ A B C D E} → Tm128 (snoc128 (snoc128 (snoc128 (snoc128 (snoc128 Γ A) B) C) D) E) A;v4128
 = var128 (vs128 (vs128 (vs128 (vs128 vz128))))

test128 : ∀{Γ A} → Tm128 Γ (arr128 (arr128 A A) (arr128 A A));test128
  = lam128 (lam128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 v0128)))))))
{-# OPTIONS --type-in-type #-}

Ty129 : Set; Ty129
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι129   : Ty129; ι129 = λ _ ι129 _ → ι129
arr129 : Ty129 → Ty129 → Ty129; arr129 = λ A B Ty129 ι129 arr129 → arr129 (A Ty129 ι129 arr129) (B Ty129 ι129 arr129)

Con129 : Set;Con129
 = (Con129 : Set)
   (nil  : Con129)
   (snoc : Con129 → Ty129 → Con129)
 → Con129

nil129 : Con129;nil129
 = λ Con129 nil129 snoc → nil129

snoc129 : Con129 → Ty129 → Con129;snoc129
 = λ Γ A Con129 nil129 snoc129 → snoc129 (Γ Con129 nil129 snoc129) A

Var129 : Con129 → Ty129 → Set;Var129
 = λ Γ A →
   (Var129 : Con129 → Ty129 → Set)
   (vz  : (Γ : _)(A : _) → Var129 (snoc129 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var129 Γ A → Var129 (snoc129 Γ B) A)
 → Var129 Γ A

vz129 : ∀{Γ A} → Var129 (snoc129 Γ A) A;vz129
 = λ Var129 vz129 vs → vz129 _ _

vs129 : ∀{Γ B A} → Var129 Γ A → Var129 (snoc129 Γ B) A;vs129
 = λ x Var129 vz129 vs129 → vs129 _ _ _ (x Var129 vz129 vs129)

Tm129 : Con129 → Ty129 → Set;Tm129
 = λ Γ A →
   (Tm129    : Con129 → Ty129 → Set)
   (var   : (Γ : _) (A : _) → Var129 Γ A → Tm129 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm129 (snoc129 Γ A) B → Tm129 Γ (arr129 A B))
   (app   : (Γ : _) (A B : _) → Tm129 Γ (arr129 A B) → Tm129 Γ A → Tm129 Γ B)
 → Tm129 Γ A

var129 : ∀{Γ A} → Var129 Γ A → Tm129 Γ A;var129
 = λ x Tm129 var129 lam app → var129 _ _ x

lam129 : ∀{Γ A B} → Tm129 (snoc129 Γ A) B → Tm129 Γ (arr129 A B);lam129
 = λ t Tm129 var129 lam129 app → lam129 _ _ _ (t Tm129 var129 lam129 app)

app129 : ∀{Γ A B} → Tm129 Γ (arr129 A B) → Tm129 Γ A → Tm129 Γ B;app129
 = λ t u Tm129 var129 lam129 app129 →
     app129 _ _ _ (t Tm129 var129 lam129 app129) (u Tm129 var129 lam129 app129)

v0129 : ∀{Γ A} → Tm129 (snoc129 Γ A) A;v0129
 = var129 vz129

v1129 : ∀{Γ A B} → Tm129 (snoc129 (snoc129 Γ A) B) A;v1129
 = var129 (vs129 vz129)

v2129 : ∀{Γ A B C} → Tm129 (snoc129 (snoc129 (snoc129 Γ A) B) C) A;v2129
 = var129 (vs129 (vs129 vz129))

v3129 : ∀{Γ A B C D} → Tm129 (snoc129 (snoc129 (snoc129 (snoc129 Γ A) B) C) D) A;v3129
 = var129 (vs129 (vs129 (vs129 vz129)))

v4129 : ∀{Γ A B C D E} → Tm129 (snoc129 (snoc129 (snoc129 (snoc129 (snoc129 Γ A) B) C) D) E) A;v4129
 = var129 (vs129 (vs129 (vs129 (vs129 vz129))))

test129 : ∀{Γ A} → Tm129 Γ (arr129 (arr129 A A) (arr129 A A));test129
  = lam129 (lam129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 v0129)))))))
{-# OPTIONS --type-in-type #-}

Ty130 : Set; Ty130
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι130   : Ty130; ι130 = λ _ ι130 _ → ι130
arr130 : Ty130 → Ty130 → Ty130; arr130 = λ A B Ty130 ι130 arr130 → arr130 (A Ty130 ι130 arr130) (B Ty130 ι130 arr130)

Con130 : Set;Con130
 = (Con130 : Set)
   (nil  : Con130)
   (snoc : Con130 → Ty130 → Con130)
 → Con130

nil130 : Con130;nil130
 = λ Con130 nil130 snoc → nil130

snoc130 : Con130 → Ty130 → Con130;snoc130
 = λ Γ A Con130 nil130 snoc130 → snoc130 (Γ Con130 nil130 snoc130) A

Var130 : Con130 → Ty130 → Set;Var130
 = λ Γ A →
   (Var130 : Con130 → Ty130 → Set)
   (vz  : (Γ : _)(A : _) → Var130 (snoc130 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var130 Γ A → Var130 (snoc130 Γ B) A)
 → Var130 Γ A

vz130 : ∀{Γ A} → Var130 (snoc130 Γ A) A;vz130
 = λ Var130 vz130 vs → vz130 _ _

vs130 : ∀{Γ B A} → Var130 Γ A → Var130 (snoc130 Γ B) A;vs130
 = λ x Var130 vz130 vs130 → vs130 _ _ _ (x Var130 vz130 vs130)

Tm130 : Con130 → Ty130 → Set;Tm130
 = λ Γ A →
   (Tm130    : Con130 → Ty130 → Set)
   (var   : (Γ : _) (A : _) → Var130 Γ A → Tm130 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm130 (snoc130 Γ A) B → Tm130 Γ (arr130 A B))
   (app   : (Γ : _) (A B : _) → Tm130 Γ (arr130 A B) → Tm130 Γ A → Tm130 Γ B)
 → Tm130 Γ A

var130 : ∀{Γ A} → Var130 Γ A → Tm130 Γ A;var130
 = λ x Tm130 var130 lam app → var130 _ _ x

lam130 : ∀{Γ A B} → Tm130 (snoc130 Γ A) B → Tm130 Γ (arr130 A B);lam130
 = λ t Tm130 var130 lam130 app → lam130 _ _ _ (t Tm130 var130 lam130 app)

app130 : ∀{Γ A B} → Tm130 Γ (arr130 A B) → Tm130 Γ A → Tm130 Γ B;app130
 = λ t u Tm130 var130 lam130 app130 →
     app130 _ _ _ (t Tm130 var130 lam130 app130) (u Tm130 var130 lam130 app130)

v0130 : ∀{Γ A} → Tm130 (snoc130 Γ A) A;v0130
 = var130 vz130

v1130 : ∀{Γ A B} → Tm130 (snoc130 (snoc130 Γ A) B) A;v1130
 = var130 (vs130 vz130)

v2130 : ∀{Γ A B C} → Tm130 (snoc130 (snoc130 (snoc130 Γ A) B) C) A;v2130
 = var130 (vs130 (vs130 vz130))

v3130 : ∀{Γ A B C D} → Tm130 (snoc130 (snoc130 (snoc130 (snoc130 Γ A) B) C) D) A;v3130
 = var130 (vs130 (vs130 (vs130 vz130)))

v4130 : ∀{Γ A B C D E} → Tm130 (snoc130 (snoc130 (snoc130 (snoc130 (snoc130 Γ A) B) C) D) E) A;v4130
 = var130 (vs130 (vs130 (vs130 (vs130 vz130))))

test130 : ∀{Γ A} → Tm130 Γ (arr130 (arr130 A A) (arr130 A A));test130
  = lam130 (lam130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 v0130)))))))
{-# OPTIONS --type-in-type #-}

Ty131 : Set; Ty131
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι131   : Ty131; ι131 = λ _ ι131 _ → ι131
arr131 : Ty131 → Ty131 → Ty131; arr131 = λ A B Ty131 ι131 arr131 → arr131 (A Ty131 ι131 arr131) (B Ty131 ι131 arr131)

Con131 : Set;Con131
 = (Con131 : Set)
   (nil  : Con131)
   (snoc : Con131 → Ty131 → Con131)
 → Con131

nil131 : Con131;nil131
 = λ Con131 nil131 snoc → nil131

snoc131 : Con131 → Ty131 → Con131;snoc131
 = λ Γ A Con131 nil131 snoc131 → snoc131 (Γ Con131 nil131 snoc131) A

Var131 : Con131 → Ty131 → Set;Var131
 = λ Γ A →
   (Var131 : Con131 → Ty131 → Set)
   (vz  : (Γ : _)(A : _) → Var131 (snoc131 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var131 Γ A → Var131 (snoc131 Γ B) A)
 → Var131 Γ A

vz131 : ∀{Γ A} → Var131 (snoc131 Γ A) A;vz131
 = λ Var131 vz131 vs → vz131 _ _

vs131 : ∀{Γ B A} → Var131 Γ A → Var131 (snoc131 Γ B) A;vs131
 = λ x Var131 vz131 vs131 → vs131 _ _ _ (x Var131 vz131 vs131)

Tm131 : Con131 → Ty131 → Set;Tm131
 = λ Γ A →
   (Tm131    : Con131 → Ty131 → Set)
   (var   : (Γ : _) (A : _) → Var131 Γ A → Tm131 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm131 (snoc131 Γ A) B → Tm131 Γ (arr131 A B))
   (app   : (Γ : _) (A B : _) → Tm131 Γ (arr131 A B) → Tm131 Γ A → Tm131 Γ B)
 → Tm131 Γ A

var131 : ∀{Γ A} → Var131 Γ A → Tm131 Γ A;var131
 = λ x Tm131 var131 lam app → var131 _ _ x

lam131 : ∀{Γ A B} → Tm131 (snoc131 Γ A) B → Tm131 Γ (arr131 A B);lam131
 = λ t Tm131 var131 lam131 app → lam131 _ _ _ (t Tm131 var131 lam131 app)

app131 : ∀{Γ A B} → Tm131 Γ (arr131 A B) → Tm131 Γ A → Tm131 Γ B;app131
 = λ t u Tm131 var131 lam131 app131 →
     app131 _ _ _ (t Tm131 var131 lam131 app131) (u Tm131 var131 lam131 app131)

v0131 : ∀{Γ A} → Tm131 (snoc131 Γ A) A;v0131
 = var131 vz131

v1131 : ∀{Γ A B} → Tm131 (snoc131 (snoc131 Γ A) B) A;v1131
 = var131 (vs131 vz131)

v2131 : ∀{Γ A B C} → Tm131 (snoc131 (snoc131 (snoc131 Γ A) B) C) A;v2131
 = var131 (vs131 (vs131 vz131))

v3131 : ∀{Γ A B C D} → Tm131 (snoc131 (snoc131 (snoc131 (snoc131 Γ A) B) C) D) A;v3131
 = var131 (vs131 (vs131 (vs131 vz131)))

v4131 : ∀{Γ A B C D E} → Tm131 (snoc131 (snoc131 (snoc131 (snoc131 (snoc131 Γ A) B) C) D) E) A;v4131
 = var131 (vs131 (vs131 (vs131 (vs131 vz131))))

test131 : ∀{Γ A} → Tm131 Γ (arr131 (arr131 A A) (arr131 A A));test131
  = lam131 (lam131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 v0131)))))))
{-# OPTIONS --type-in-type #-}

Ty132 : Set; Ty132
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι132   : Ty132; ι132 = λ _ ι132 _ → ι132
arr132 : Ty132 → Ty132 → Ty132; arr132 = λ A B Ty132 ι132 arr132 → arr132 (A Ty132 ι132 arr132) (B Ty132 ι132 arr132)

Con132 : Set;Con132
 = (Con132 : Set)
   (nil  : Con132)
   (snoc : Con132 → Ty132 → Con132)
 → Con132

nil132 : Con132;nil132
 = λ Con132 nil132 snoc → nil132

snoc132 : Con132 → Ty132 → Con132;snoc132
 = λ Γ A Con132 nil132 snoc132 → snoc132 (Γ Con132 nil132 snoc132) A

Var132 : Con132 → Ty132 → Set;Var132
 = λ Γ A →
   (Var132 : Con132 → Ty132 → Set)
   (vz  : (Γ : _)(A : _) → Var132 (snoc132 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var132 Γ A → Var132 (snoc132 Γ B) A)
 → Var132 Γ A

vz132 : ∀{Γ A} → Var132 (snoc132 Γ A) A;vz132
 = λ Var132 vz132 vs → vz132 _ _

vs132 : ∀{Γ B A} → Var132 Γ A → Var132 (snoc132 Γ B) A;vs132
 = λ x Var132 vz132 vs132 → vs132 _ _ _ (x Var132 vz132 vs132)

Tm132 : Con132 → Ty132 → Set;Tm132
 = λ Γ A →
   (Tm132    : Con132 → Ty132 → Set)
   (var   : (Γ : _) (A : _) → Var132 Γ A → Tm132 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm132 (snoc132 Γ A) B → Tm132 Γ (arr132 A B))
   (app   : (Γ : _) (A B : _) → Tm132 Γ (arr132 A B) → Tm132 Γ A → Tm132 Γ B)
 → Tm132 Γ A

var132 : ∀{Γ A} → Var132 Γ A → Tm132 Γ A;var132
 = λ x Tm132 var132 lam app → var132 _ _ x

lam132 : ∀{Γ A B} → Tm132 (snoc132 Γ A) B → Tm132 Γ (arr132 A B);lam132
 = λ t Tm132 var132 lam132 app → lam132 _ _ _ (t Tm132 var132 lam132 app)

app132 : ∀{Γ A B} → Tm132 Γ (arr132 A B) → Tm132 Γ A → Tm132 Γ B;app132
 = λ t u Tm132 var132 lam132 app132 →
     app132 _ _ _ (t Tm132 var132 lam132 app132) (u Tm132 var132 lam132 app132)

v0132 : ∀{Γ A} → Tm132 (snoc132 Γ A) A;v0132
 = var132 vz132

v1132 : ∀{Γ A B} → Tm132 (snoc132 (snoc132 Γ A) B) A;v1132
 = var132 (vs132 vz132)

v2132 : ∀{Γ A B C} → Tm132 (snoc132 (snoc132 (snoc132 Γ A) B) C) A;v2132
 = var132 (vs132 (vs132 vz132))

v3132 : ∀{Γ A B C D} → Tm132 (snoc132 (snoc132 (snoc132 (snoc132 Γ A) B) C) D) A;v3132
 = var132 (vs132 (vs132 (vs132 vz132)))

v4132 : ∀{Γ A B C D E} → Tm132 (snoc132 (snoc132 (snoc132 (snoc132 (snoc132 Γ A) B) C) D) E) A;v4132
 = var132 (vs132 (vs132 (vs132 (vs132 vz132))))

test132 : ∀{Γ A} → Tm132 Γ (arr132 (arr132 A A) (arr132 A A));test132
  = lam132 (lam132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 v0132)))))))
{-# OPTIONS --type-in-type #-}

Ty133 : Set; Ty133
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι133   : Ty133; ι133 = λ _ ι133 _ → ι133
arr133 : Ty133 → Ty133 → Ty133; arr133 = λ A B Ty133 ι133 arr133 → arr133 (A Ty133 ι133 arr133) (B Ty133 ι133 arr133)

Con133 : Set;Con133
 = (Con133 : Set)
   (nil  : Con133)
   (snoc : Con133 → Ty133 → Con133)
 → Con133

nil133 : Con133;nil133
 = λ Con133 nil133 snoc → nil133

snoc133 : Con133 → Ty133 → Con133;snoc133
 = λ Γ A Con133 nil133 snoc133 → snoc133 (Γ Con133 nil133 snoc133) A

Var133 : Con133 → Ty133 → Set;Var133
 = λ Γ A →
   (Var133 : Con133 → Ty133 → Set)
   (vz  : (Γ : _)(A : _) → Var133 (snoc133 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var133 Γ A → Var133 (snoc133 Γ B) A)
 → Var133 Γ A

vz133 : ∀{Γ A} → Var133 (snoc133 Γ A) A;vz133
 = λ Var133 vz133 vs → vz133 _ _

vs133 : ∀{Γ B A} → Var133 Γ A → Var133 (snoc133 Γ B) A;vs133
 = λ x Var133 vz133 vs133 → vs133 _ _ _ (x Var133 vz133 vs133)

Tm133 : Con133 → Ty133 → Set;Tm133
 = λ Γ A →
   (Tm133    : Con133 → Ty133 → Set)
   (var   : (Γ : _) (A : _) → Var133 Γ A → Tm133 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm133 (snoc133 Γ A) B → Tm133 Γ (arr133 A B))
   (app   : (Γ : _) (A B : _) → Tm133 Γ (arr133 A B) → Tm133 Γ A → Tm133 Γ B)
 → Tm133 Γ A

var133 : ∀{Γ A} → Var133 Γ A → Tm133 Γ A;var133
 = λ x Tm133 var133 lam app → var133 _ _ x

lam133 : ∀{Γ A B} → Tm133 (snoc133 Γ A) B → Tm133 Γ (arr133 A B);lam133
 = λ t Tm133 var133 lam133 app → lam133 _ _ _ (t Tm133 var133 lam133 app)

app133 : ∀{Γ A B} → Tm133 Γ (arr133 A B) → Tm133 Γ A → Tm133 Γ B;app133
 = λ t u Tm133 var133 lam133 app133 →
     app133 _ _ _ (t Tm133 var133 lam133 app133) (u Tm133 var133 lam133 app133)

v0133 : ∀{Γ A} → Tm133 (snoc133 Γ A) A;v0133
 = var133 vz133

v1133 : ∀{Γ A B} → Tm133 (snoc133 (snoc133 Γ A) B) A;v1133
 = var133 (vs133 vz133)

v2133 : ∀{Γ A B C} → Tm133 (snoc133 (snoc133 (snoc133 Γ A) B) C) A;v2133
 = var133 (vs133 (vs133 vz133))

v3133 : ∀{Γ A B C D} → Tm133 (snoc133 (snoc133 (snoc133 (snoc133 Γ A) B) C) D) A;v3133
 = var133 (vs133 (vs133 (vs133 vz133)))

v4133 : ∀{Γ A B C D E} → Tm133 (snoc133 (snoc133 (snoc133 (snoc133 (snoc133 Γ A) B) C) D) E) A;v4133
 = var133 (vs133 (vs133 (vs133 (vs133 vz133))))

test133 : ∀{Γ A} → Tm133 Γ (arr133 (arr133 A A) (arr133 A A));test133
  = lam133 (lam133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 v0133)))))))
{-# OPTIONS --type-in-type #-}

Ty134 : Set; Ty134
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι134   : Ty134; ι134 = λ _ ι134 _ → ι134
arr134 : Ty134 → Ty134 → Ty134; arr134 = λ A B Ty134 ι134 arr134 → arr134 (A Ty134 ι134 arr134) (B Ty134 ι134 arr134)

Con134 : Set;Con134
 = (Con134 : Set)
   (nil  : Con134)
   (snoc : Con134 → Ty134 → Con134)
 → Con134

nil134 : Con134;nil134
 = λ Con134 nil134 snoc → nil134

snoc134 : Con134 → Ty134 → Con134;snoc134
 = λ Γ A Con134 nil134 snoc134 → snoc134 (Γ Con134 nil134 snoc134) A

Var134 : Con134 → Ty134 → Set;Var134
 = λ Γ A →
   (Var134 : Con134 → Ty134 → Set)
   (vz  : (Γ : _)(A : _) → Var134 (snoc134 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var134 Γ A → Var134 (snoc134 Γ B) A)
 → Var134 Γ A

vz134 : ∀{Γ A} → Var134 (snoc134 Γ A) A;vz134
 = λ Var134 vz134 vs → vz134 _ _

vs134 : ∀{Γ B A} → Var134 Γ A → Var134 (snoc134 Γ B) A;vs134
 = λ x Var134 vz134 vs134 → vs134 _ _ _ (x Var134 vz134 vs134)

Tm134 : Con134 → Ty134 → Set;Tm134
 = λ Γ A →
   (Tm134    : Con134 → Ty134 → Set)
   (var   : (Γ : _) (A : _) → Var134 Γ A → Tm134 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm134 (snoc134 Γ A) B → Tm134 Γ (arr134 A B))
   (app   : (Γ : _) (A B : _) → Tm134 Γ (arr134 A B) → Tm134 Γ A → Tm134 Γ B)
 → Tm134 Γ A

var134 : ∀{Γ A} → Var134 Γ A → Tm134 Γ A;var134
 = λ x Tm134 var134 lam app → var134 _ _ x

lam134 : ∀{Γ A B} → Tm134 (snoc134 Γ A) B → Tm134 Γ (arr134 A B);lam134
 = λ t Tm134 var134 lam134 app → lam134 _ _ _ (t Tm134 var134 lam134 app)

app134 : ∀{Γ A B} → Tm134 Γ (arr134 A B) → Tm134 Γ A → Tm134 Γ B;app134
 = λ t u Tm134 var134 lam134 app134 →
     app134 _ _ _ (t Tm134 var134 lam134 app134) (u Tm134 var134 lam134 app134)

v0134 : ∀{Γ A} → Tm134 (snoc134 Γ A) A;v0134
 = var134 vz134

v1134 : ∀{Γ A B} → Tm134 (snoc134 (snoc134 Γ A) B) A;v1134
 = var134 (vs134 vz134)

v2134 : ∀{Γ A B C} → Tm134 (snoc134 (snoc134 (snoc134 Γ A) B) C) A;v2134
 = var134 (vs134 (vs134 vz134))

v3134 : ∀{Γ A B C D} → Tm134 (snoc134 (snoc134 (snoc134 (snoc134 Γ A) B) C) D) A;v3134
 = var134 (vs134 (vs134 (vs134 vz134)))

v4134 : ∀{Γ A B C D E} → Tm134 (snoc134 (snoc134 (snoc134 (snoc134 (snoc134 Γ A) B) C) D) E) A;v4134
 = var134 (vs134 (vs134 (vs134 (vs134 vz134))))

test134 : ∀{Γ A} → Tm134 Γ (arr134 (arr134 A A) (arr134 A A));test134
  = lam134 (lam134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 v0134)))))))
{-# OPTIONS --type-in-type #-}

Ty135 : Set; Ty135
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι135   : Ty135; ι135 = λ _ ι135 _ → ι135
arr135 : Ty135 → Ty135 → Ty135; arr135 = λ A B Ty135 ι135 arr135 → arr135 (A Ty135 ι135 arr135) (B Ty135 ι135 arr135)

Con135 : Set;Con135
 = (Con135 : Set)
   (nil  : Con135)
   (snoc : Con135 → Ty135 → Con135)
 → Con135

nil135 : Con135;nil135
 = λ Con135 nil135 snoc → nil135

snoc135 : Con135 → Ty135 → Con135;snoc135
 = λ Γ A Con135 nil135 snoc135 → snoc135 (Γ Con135 nil135 snoc135) A

Var135 : Con135 → Ty135 → Set;Var135
 = λ Γ A →
   (Var135 : Con135 → Ty135 → Set)
   (vz  : (Γ : _)(A : _) → Var135 (snoc135 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var135 Γ A → Var135 (snoc135 Γ B) A)
 → Var135 Γ A

vz135 : ∀{Γ A} → Var135 (snoc135 Γ A) A;vz135
 = λ Var135 vz135 vs → vz135 _ _

vs135 : ∀{Γ B A} → Var135 Γ A → Var135 (snoc135 Γ B) A;vs135
 = λ x Var135 vz135 vs135 → vs135 _ _ _ (x Var135 vz135 vs135)

Tm135 : Con135 → Ty135 → Set;Tm135
 = λ Γ A →
   (Tm135    : Con135 → Ty135 → Set)
   (var   : (Γ : _) (A : _) → Var135 Γ A → Tm135 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm135 (snoc135 Γ A) B → Tm135 Γ (arr135 A B))
   (app   : (Γ : _) (A B : _) → Tm135 Γ (arr135 A B) → Tm135 Γ A → Tm135 Γ B)
 → Tm135 Γ A

var135 : ∀{Γ A} → Var135 Γ A → Tm135 Γ A;var135
 = λ x Tm135 var135 lam app → var135 _ _ x

lam135 : ∀{Γ A B} → Tm135 (snoc135 Γ A) B → Tm135 Γ (arr135 A B);lam135
 = λ t Tm135 var135 lam135 app → lam135 _ _ _ (t Tm135 var135 lam135 app)

app135 : ∀{Γ A B} → Tm135 Γ (arr135 A B) → Tm135 Γ A → Tm135 Γ B;app135
 = λ t u Tm135 var135 lam135 app135 →
     app135 _ _ _ (t Tm135 var135 lam135 app135) (u Tm135 var135 lam135 app135)

v0135 : ∀{Γ A} → Tm135 (snoc135 Γ A) A;v0135
 = var135 vz135

v1135 : ∀{Γ A B} → Tm135 (snoc135 (snoc135 Γ A) B) A;v1135
 = var135 (vs135 vz135)

v2135 : ∀{Γ A B C} → Tm135 (snoc135 (snoc135 (snoc135 Γ A) B) C) A;v2135
 = var135 (vs135 (vs135 vz135))

v3135 : ∀{Γ A B C D} → Tm135 (snoc135 (snoc135 (snoc135 (snoc135 Γ A) B) C) D) A;v3135
 = var135 (vs135 (vs135 (vs135 vz135)))

v4135 : ∀{Γ A B C D E} → Tm135 (snoc135 (snoc135 (snoc135 (snoc135 (snoc135 Γ A) B) C) D) E) A;v4135
 = var135 (vs135 (vs135 (vs135 (vs135 vz135))))

test135 : ∀{Γ A} → Tm135 Γ (arr135 (arr135 A A) (arr135 A A));test135
  = lam135 (lam135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 v0135)))))))
{-# OPTIONS --type-in-type #-}

Ty136 : Set; Ty136
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι136   : Ty136; ι136 = λ _ ι136 _ → ι136
arr136 : Ty136 → Ty136 → Ty136; arr136 = λ A B Ty136 ι136 arr136 → arr136 (A Ty136 ι136 arr136) (B Ty136 ι136 arr136)

Con136 : Set;Con136
 = (Con136 : Set)
   (nil  : Con136)
   (snoc : Con136 → Ty136 → Con136)
 → Con136

nil136 : Con136;nil136
 = λ Con136 nil136 snoc → nil136

snoc136 : Con136 → Ty136 → Con136;snoc136
 = λ Γ A Con136 nil136 snoc136 → snoc136 (Γ Con136 nil136 snoc136) A

Var136 : Con136 → Ty136 → Set;Var136
 = λ Γ A →
   (Var136 : Con136 → Ty136 → Set)
   (vz  : (Γ : _)(A : _) → Var136 (snoc136 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var136 Γ A → Var136 (snoc136 Γ B) A)
 → Var136 Γ A

vz136 : ∀{Γ A} → Var136 (snoc136 Γ A) A;vz136
 = λ Var136 vz136 vs → vz136 _ _

vs136 : ∀{Γ B A} → Var136 Γ A → Var136 (snoc136 Γ B) A;vs136
 = λ x Var136 vz136 vs136 → vs136 _ _ _ (x Var136 vz136 vs136)

Tm136 : Con136 → Ty136 → Set;Tm136
 = λ Γ A →
   (Tm136    : Con136 → Ty136 → Set)
   (var   : (Γ : _) (A : _) → Var136 Γ A → Tm136 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm136 (snoc136 Γ A) B → Tm136 Γ (arr136 A B))
   (app   : (Γ : _) (A B : _) → Tm136 Γ (arr136 A B) → Tm136 Γ A → Tm136 Γ B)
 → Tm136 Γ A

var136 : ∀{Γ A} → Var136 Γ A → Tm136 Γ A;var136
 = λ x Tm136 var136 lam app → var136 _ _ x

lam136 : ∀{Γ A B} → Tm136 (snoc136 Γ A) B → Tm136 Γ (arr136 A B);lam136
 = λ t Tm136 var136 lam136 app → lam136 _ _ _ (t Tm136 var136 lam136 app)

app136 : ∀{Γ A B} → Tm136 Γ (arr136 A B) → Tm136 Γ A → Tm136 Γ B;app136
 = λ t u Tm136 var136 lam136 app136 →
     app136 _ _ _ (t Tm136 var136 lam136 app136) (u Tm136 var136 lam136 app136)

v0136 : ∀{Γ A} → Tm136 (snoc136 Γ A) A;v0136
 = var136 vz136

v1136 : ∀{Γ A B} → Tm136 (snoc136 (snoc136 Γ A) B) A;v1136
 = var136 (vs136 vz136)

v2136 : ∀{Γ A B C} → Tm136 (snoc136 (snoc136 (snoc136 Γ A) B) C) A;v2136
 = var136 (vs136 (vs136 vz136))

v3136 : ∀{Γ A B C D} → Tm136 (snoc136 (snoc136 (snoc136 (snoc136 Γ A) B) C) D) A;v3136
 = var136 (vs136 (vs136 (vs136 vz136)))

v4136 : ∀{Γ A B C D E} → Tm136 (snoc136 (snoc136 (snoc136 (snoc136 (snoc136 Γ A) B) C) D) E) A;v4136
 = var136 (vs136 (vs136 (vs136 (vs136 vz136))))

test136 : ∀{Γ A} → Tm136 Γ (arr136 (arr136 A A) (arr136 A A));test136
  = lam136 (lam136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 v0136)))))))
{-# OPTIONS --type-in-type #-}

Ty137 : Set; Ty137
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι137   : Ty137; ι137 = λ _ ι137 _ → ι137
arr137 : Ty137 → Ty137 → Ty137; arr137 = λ A B Ty137 ι137 arr137 → arr137 (A Ty137 ι137 arr137) (B Ty137 ι137 arr137)

Con137 : Set;Con137
 = (Con137 : Set)
   (nil  : Con137)
   (snoc : Con137 → Ty137 → Con137)
 → Con137

nil137 : Con137;nil137
 = λ Con137 nil137 snoc → nil137

snoc137 : Con137 → Ty137 → Con137;snoc137
 = λ Γ A Con137 nil137 snoc137 → snoc137 (Γ Con137 nil137 snoc137) A

Var137 : Con137 → Ty137 → Set;Var137
 = λ Γ A →
   (Var137 : Con137 → Ty137 → Set)
   (vz  : (Γ : _)(A : _) → Var137 (snoc137 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var137 Γ A → Var137 (snoc137 Γ B) A)
 → Var137 Γ A

vz137 : ∀{Γ A} → Var137 (snoc137 Γ A) A;vz137
 = λ Var137 vz137 vs → vz137 _ _

vs137 : ∀{Γ B A} → Var137 Γ A → Var137 (snoc137 Γ B) A;vs137
 = λ x Var137 vz137 vs137 → vs137 _ _ _ (x Var137 vz137 vs137)

Tm137 : Con137 → Ty137 → Set;Tm137
 = λ Γ A →
   (Tm137    : Con137 → Ty137 → Set)
   (var   : (Γ : _) (A : _) → Var137 Γ A → Tm137 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm137 (snoc137 Γ A) B → Tm137 Γ (arr137 A B))
   (app   : (Γ : _) (A B : _) → Tm137 Γ (arr137 A B) → Tm137 Γ A → Tm137 Γ B)
 → Tm137 Γ A

var137 : ∀{Γ A} → Var137 Γ A → Tm137 Γ A;var137
 = λ x Tm137 var137 lam app → var137 _ _ x

lam137 : ∀{Γ A B} → Tm137 (snoc137 Γ A) B → Tm137 Γ (arr137 A B);lam137
 = λ t Tm137 var137 lam137 app → lam137 _ _ _ (t Tm137 var137 lam137 app)

app137 : ∀{Γ A B} → Tm137 Γ (arr137 A B) → Tm137 Γ A → Tm137 Γ B;app137
 = λ t u Tm137 var137 lam137 app137 →
     app137 _ _ _ (t Tm137 var137 lam137 app137) (u Tm137 var137 lam137 app137)

v0137 : ∀{Γ A} → Tm137 (snoc137 Γ A) A;v0137
 = var137 vz137

v1137 : ∀{Γ A B} → Tm137 (snoc137 (snoc137 Γ A) B) A;v1137
 = var137 (vs137 vz137)

v2137 : ∀{Γ A B C} → Tm137 (snoc137 (snoc137 (snoc137 Γ A) B) C) A;v2137
 = var137 (vs137 (vs137 vz137))

v3137 : ∀{Γ A B C D} → Tm137 (snoc137 (snoc137 (snoc137 (snoc137 Γ A) B) C) D) A;v3137
 = var137 (vs137 (vs137 (vs137 vz137)))

v4137 : ∀{Γ A B C D E} → Tm137 (snoc137 (snoc137 (snoc137 (snoc137 (snoc137 Γ A) B) C) D) E) A;v4137
 = var137 (vs137 (vs137 (vs137 (vs137 vz137))))

test137 : ∀{Γ A} → Tm137 Γ (arr137 (arr137 A A) (arr137 A A));test137
  = lam137 (lam137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 v0137)))))))
{-# OPTIONS --type-in-type #-}

Ty138 : Set; Ty138
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι138   : Ty138; ι138 = λ _ ι138 _ → ι138
arr138 : Ty138 → Ty138 → Ty138; arr138 = λ A B Ty138 ι138 arr138 → arr138 (A Ty138 ι138 arr138) (B Ty138 ι138 arr138)

Con138 : Set;Con138
 = (Con138 : Set)
   (nil  : Con138)
   (snoc : Con138 → Ty138 → Con138)
 → Con138

nil138 : Con138;nil138
 = λ Con138 nil138 snoc → nil138

snoc138 : Con138 → Ty138 → Con138;snoc138
 = λ Γ A Con138 nil138 snoc138 → snoc138 (Γ Con138 nil138 snoc138) A

Var138 : Con138 → Ty138 → Set;Var138
 = λ Γ A →
   (Var138 : Con138 → Ty138 → Set)
   (vz  : (Γ : _)(A : _) → Var138 (snoc138 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var138 Γ A → Var138 (snoc138 Γ B) A)
 → Var138 Γ A

vz138 : ∀{Γ A} → Var138 (snoc138 Γ A) A;vz138
 = λ Var138 vz138 vs → vz138 _ _

vs138 : ∀{Γ B A} → Var138 Γ A → Var138 (snoc138 Γ B) A;vs138
 = λ x Var138 vz138 vs138 → vs138 _ _ _ (x Var138 vz138 vs138)

Tm138 : Con138 → Ty138 → Set;Tm138
 = λ Γ A →
   (Tm138    : Con138 → Ty138 → Set)
   (var   : (Γ : _) (A : _) → Var138 Γ A → Tm138 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm138 (snoc138 Γ A) B → Tm138 Γ (arr138 A B))
   (app   : (Γ : _) (A B : _) → Tm138 Γ (arr138 A B) → Tm138 Γ A → Tm138 Γ B)
 → Tm138 Γ A

var138 : ∀{Γ A} → Var138 Γ A → Tm138 Γ A;var138
 = λ x Tm138 var138 lam app → var138 _ _ x

lam138 : ∀{Γ A B} → Tm138 (snoc138 Γ A) B → Tm138 Γ (arr138 A B);lam138
 = λ t Tm138 var138 lam138 app → lam138 _ _ _ (t Tm138 var138 lam138 app)

app138 : ∀{Γ A B} → Tm138 Γ (arr138 A B) → Tm138 Γ A → Tm138 Γ B;app138
 = λ t u Tm138 var138 lam138 app138 →
     app138 _ _ _ (t Tm138 var138 lam138 app138) (u Tm138 var138 lam138 app138)

v0138 : ∀{Γ A} → Tm138 (snoc138 Γ A) A;v0138
 = var138 vz138

v1138 : ∀{Γ A B} → Tm138 (snoc138 (snoc138 Γ A) B) A;v1138
 = var138 (vs138 vz138)

v2138 : ∀{Γ A B C} → Tm138 (snoc138 (snoc138 (snoc138 Γ A) B) C) A;v2138
 = var138 (vs138 (vs138 vz138))

v3138 : ∀{Γ A B C D} → Tm138 (snoc138 (snoc138 (snoc138 (snoc138 Γ A) B) C) D) A;v3138
 = var138 (vs138 (vs138 (vs138 vz138)))

v4138 : ∀{Γ A B C D E} → Tm138 (snoc138 (snoc138 (snoc138 (snoc138 (snoc138 Γ A) B) C) D) E) A;v4138
 = var138 (vs138 (vs138 (vs138 (vs138 vz138))))

test138 : ∀{Γ A} → Tm138 Γ (arr138 (arr138 A A) (arr138 A A));test138
  = lam138 (lam138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 v0138)))))))
{-# OPTIONS --type-in-type #-}

Ty139 : Set; Ty139
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι139   : Ty139; ι139 = λ _ ι139 _ → ι139
arr139 : Ty139 → Ty139 → Ty139; arr139 = λ A B Ty139 ι139 arr139 → arr139 (A Ty139 ι139 arr139) (B Ty139 ι139 arr139)

Con139 : Set;Con139
 = (Con139 : Set)
   (nil  : Con139)
   (snoc : Con139 → Ty139 → Con139)
 → Con139

nil139 : Con139;nil139
 = λ Con139 nil139 snoc → nil139

snoc139 : Con139 → Ty139 → Con139;snoc139
 = λ Γ A Con139 nil139 snoc139 → snoc139 (Γ Con139 nil139 snoc139) A

Var139 : Con139 → Ty139 → Set;Var139
 = λ Γ A →
   (Var139 : Con139 → Ty139 → Set)
   (vz  : (Γ : _)(A : _) → Var139 (snoc139 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var139 Γ A → Var139 (snoc139 Γ B) A)
 → Var139 Γ A

vz139 : ∀{Γ A} → Var139 (snoc139 Γ A) A;vz139
 = λ Var139 vz139 vs → vz139 _ _

vs139 : ∀{Γ B A} → Var139 Γ A → Var139 (snoc139 Γ B) A;vs139
 = λ x Var139 vz139 vs139 → vs139 _ _ _ (x Var139 vz139 vs139)

Tm139 : Con139 → Ty139 → Set;Tm139
 = λ Γ A →
   (Tm139    : Con139 → Ty139 → Set)
   (var   : (Γ : _) (A : _) → Var139 Γ A → Tm139 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm139 (snoc139 Γ A) B → Tm139 Γ (arr139 A B))
   (app   : (Γ : _) (A B : _) → Tm139 Γ (arr139 A B) → Tm139 Γ A → Tm139 Γ B)
 → Tm139 Γ A

var139 : ∀{Γ A} → Var139 Γ A → Tm139 Γ A;var139
 = λ x Tm139 var139 lam app → var139 _ _ x

lam139 : ∀{Γ A B} → Tm139 (snoc139 Γ A) B → Tm139 Γ (arr139 A B);lam139
 = λ t Tm139 var139 lam139 app → lam139 _ _ _ (t Tm139 var139 lam139 app)

app139 : ∀{Γ A B} → Tm139 Γ (arr139 A B) → Tm139 Γ A → Tm139 Γ B;app139
 = λ t u Tm139 var139 lam139 app139 →
     app139 _ _ _ (t Tm139 var139 lam139 app139) (u Tm139 var139 lam139 app139)

v0139 : ∀{Γ A} → Tm139 (snoc139 Γ A) A;v0139
 = var139 vz139

v1139 : ∀{Γ A B} → Tm139 (snoc139 (snoc139 Γ A) B) A;v1139
 = var139 (vs139 vz139)

v2139 : ∀{Γ A B C} → Tm139 (snoc139 (snoc139 (snoc139 Γ A) B) C) A;v2139
 = var139 (vs139 (vs139 vz139))

v3139 : ∀{Γ A B C D} → Tm139 (snoc139 (snoc139 (snoc139 (snoc139 Γ A) B) C) D) A;v3139
 = var139 (vs139 (vs139 (vs139 vz139)))

v4139 : ∀{Γ A B C D E} → Tm139 (snoc139 (snoc139 (snoc139 (snoc139 (snoc139 Γ A) B) C) D) E) A;v4139
 = var139 (vs139 (vs139 (vs139 (vs139 vz139))))

test139 : ∀{Γ A} → Tm139 Γ (arr139 (arr139 A A) (arr139 A A));test139
  = lam139 (lam139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 v0139)))))))
{-# OPTIONS --type-in-type #-}

Ty140 : Set; Ty140
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι140   : Ty140; ι140 = λ _ ι140 _ → ι140
arr140 : Ty140 → Ty140 → Ty140; arr140 = λ A B Ty140 ι140 arr140 → arr140 (A Ty140 ι140 arr140) (B Ty140 ι140 arr140)

Con140 : Set;Con140
 = (Con140 : Set)
   (nil  : Con140)
   (snoc : Con140 → Ty140 → Con140)
 → Con140

nil140 : Con140;nil140
 = λ Con140 nil140 snoc → nil140

snoc140 : Con140 → Ty140 → Con140;snoc140
 = λ Γ A Con140 nil140 snoc140 → snoc140 (Γ Con140 nil140 snoc140) A

Var140 : Con140 → Ty140 → Set;Var140
 = λ Γ A →
   (Var140 : Con140 → Ty140 → Set)
   (vz  : (Γ : _)(A : _) → Var140 (snoc140 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var140 Γ A → Var140 (snoc140 Γ B) A)
 → Var140 Γ A

vz140 : ∀{Γ A} → Var140 (snoc140 Γ A) A;vz140
 = λ Var140 vz140 vs → vz140 _ _

vs140 : ∀{Γ B A} → Var140 Γ A → Var140 (snoc140 Γ B) A;vs140
 = λ x Var140 vz140 vs140 → vs140 _ _ _ (x Var140 vz140 vs140)

Tm140 : Con140 → Ty140 → Set;Tm140
 = λ Γ A →
   (Tm140    : Con140 → Ty140 → Set)
   (var   : (Γ : _) (A : _) → Var140 Γ A → Tm140 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm140 (snoc140 Γ A) B → Tm140 Γ (arr140 A B))
   (app   : (Γ : _) (A B : _) → Tm140 Γ (arr140 A B) → Tm140 Γ A → Tm140 Γ B)
 → Tm140 Γ A

var140 : ∀{Γ A} → Var140 Γ A → Tm140 Γ A;var140
 = λ x Tm140 var140 lam app → var140 _ _ x

lam140 : ∀{Γ A B} → Tm140 (snoc140 Γ A) B → Tm140 Γ (arr140 A B);lam140
 = λ t Tm140 var140 lam140 app → lam140 _ _ _ (t Tm140 var140 lam140 app)

app140 : ∀{Γ A B} → Tm140 Γ (arr140 A B) → Tm140 Γ A → Tm140 Γ B;app140
 = λ t u Tm140 var140 lam140 app140 →
     app140 _ _ _ (t Tm140 var140 lam140 app140) (u Tm140 var140 lam140 app140)

v0140 : ∀{Γ A} → Tm140 (snoc140 Γ A) A;v0140
 = var140 vz140

v1140 : ∀{Γ A B} → Tm140 (snoc140 (snoc140 Γ A) B) A;v1140
 = var140 (vs140 vz140)

v2140 : ∀{Γ A B C} → Tm140 (snoc140 (snoc140 (snoc140 Γ A) B) C) A;v2140
 = var140 (vs140 (vs140 vz140))

v3140 : ∀{Γ A B C D} → Tm140 (snoc140 (snoc140 (snoc140 (snoc140 Γ A) B) C) D) A;v3140
 = var140 (vs140 (vs140 (vs140 vz140)))

v4140 : ∀{Γ A B C D E} → Tm140 (snoc140 (snoc140 (snoc140 (snoc140 (snoc140 Γ A) B) C) D) E) A;v4140
 = var140 (vs140 (vs140 (vs140 (vs140 vz140))))

test140 : ∀{Γ A} → Tm140 Γ (arr140 (arr140 A A) (arr140 A A));test140
  = lam140 (lam140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 v0140)))))))
{-# OPTIONS --type-in-type #-}

Ty141 : Set; Ty141
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι141   : Ty141; ι141 = λ _ ι141 _ → ι141
arr141 : Ty141 → Ty141 → Ty141; arr141 = λ A B Ty141 ι141 arr141 → arr141 (A Ty141 ι141 arr141) (B Ty141 ι141 arr141)

Con141 : Set;Con141
 = (Con141 : Set)
   (nil  : Con141)
   (snoc : Con141 → Ty141 → Con141)
 → Con141

nil141 : Con141;nil141
 = λ Con141 nil141 snoc → nil141

snoc141 : Con141 → Ty141 → Con141;snoc141
 = λ Γ A Con141 nil141 snoc141 → snoc141 (Γ Con141 nil141 snoc141) A

Var141 : Con141 → Ty141 → Set;Var141
 = λ Γ A →
   (Var141 : Con141 → Ty141 → Set)
   (vz  : (Γ : _)(A : _) → Var141 (snoc141 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var141 Γ A → Var141 (snoc141 Γ B) A)
 → Var141 Γ A

vz141 : ∀{Γ A} → Var141 (snoc141 Γ A) A;vz141
 = λ Var141 vz141 vs → vz141 _ _

vs141 : ∀{Γ B A} → Var141 Γ A → Var141 (snoc141 Γ B) A;vs141
 = λ x Var141 vz141 vs141 → vs141 _ _ _ (x Var141 vz141 vs141)

Tm141 : Con141 → Ty141 → Set;Tm141
 = λ Γ A →
   (Tm141    : Con141 → Ty141 → Set)
   (var   : (Γ : _) (A : _) → Var141 Γ A → Tm141 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm141 (snoc141 Γ A) B → Tm141 Γ (arr141 A B))
   (app   : (Γ : _) (A B : _) → Tm141 Γ (arr141 A B) → Tm141 Γ A → Tm141 Γ B)
 → Tm141 Γ A

var141 : ∀{Γ A} → Var141 Γ A → Tm141 Γ A;var141
 = λ x Tm141 var141 lam app → var141 _ _ x

lam141 : ∀{Γ A B} → Tm141 (snoc141 Γ A) B → Tm141 Γ (arr141 A B);lam141
 = λ t Tm141 var141 lam141 app → lam141 _ _ _ (t Tm141 var141 lam141 app)

app141 : ∀{Γ A B} → Tm141 Γ (arr141 A B) → Tm141 Γ A → Tm141 Γ B;app141
 = λ t u Tm141 var141 lam141 app141 →
     app141 _ _ _ (t Tm141 var141 lam141 app141) (u Tm141 var141 lam141 app141)

v0141 : ∀{Γ A} → Tm141 (snoc141 Γ A) A;v0141
 = var141 vz141

v1141 : ∀{Γ A B} → Tm141 (snoc141 (snoc141 Γ A) B) A;v1141
 = var141 (vs141 vz141)

v2141 : ∀{Γ A B C} → Tm141 (snoc141 (snoc141 (snoc141 Γ A) B) C) A;v2141
 = var141 (vs141 (vs141 vz141))

v3141 : ∀{Γ A B C D} → Tm141 (snoc141 (snoc141 (snoc141 (snoc141 Γ A) B) C) D) A;v3141
 = var141 (vs141 (vs141 (vs141 vz141)))

v4141 : ∀{Γ A B C D E} → Tm141 (snoc141 (snoc141 (snoc141 (snoc141 (snoc141 Γ A) B) C) D) E) A;v4141
 = var141 (vs141 (vs141 (vs141 (vs141 vz141))))

test141 : ∀{Γ A} → Tm141 Γ (arr141 (arr141 A A) (arr141 A A));test141
  = lam141 (lam141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 v0141)))))))
{-# OPTIONS --type-in-type #-}

Ty142 : Set; Ty142
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι142   : Ty142; ι142 = λ _ ι142 _ → ι142
arr142 : Ty142 → Ty142 → Ty142; arr142 = λ A B Ty142 ι142 arr142 → arr142 (A Ty142 ι142 arr142) (B Ty142 ι142 arr142)

Con142 : Set;Con142
 = (Con142 : Set)
   (nil  : Con142)
   (snoc : Con142 → Ty142 → Con142)
 → Con142

nil142 : Con142;nil142
 = λ Con142 nil142 snoc → nil142

snoc142 : Con142 → Ty142 → Con142;snoc142
 = λ Γ A Con142 nil142 snoc142 → snoc142 (Γ Con142 nil142 snoc142) A

Var142 : Con142 → Ty142 → Set;Var142
 = λ Γ A →
   (Var142 : Con142 → Ty142 → Set)
   (vz  : (Γ : _)(A : _) → Var142 (snoc142 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var142 Γ A → Var142 (snoc142 Γ B) A)
 → Var142 Γ A

vz142 : ∀{Γ A} → Var142 (snoc142 Γ A) A;vz142
 = λ Var142 vz142 vs → vz142 _ _

vs142 : ∀{Γ B A} → Var142 Γ A → Var142 (snoc142 Γ B) A;vs142
 = λ x Var142 vz142 vs142 → vs142 _ _ _ (x Var142 vz142 vs142)

Tm142 : Con142 → Ty142 → Set;Tm142
 = λ Γ A →
   (Tm142    : Con142 → Ty142 → Set)
   (var   : (Γ : _) (A : _) → Var142 Γ A → Tm142 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm142 (snoc142 Γ A) B → Tm142 Γ (arr142 A B))
   (app   : (Γ : _) (A B : _) → Tm142 Γ (arr142 A B) → Tm142 Γ A → Tm142 Γ B)
 → Tm142 Γ A

var142 : ∀{Γ A} → Var142 Γ A → Tm142 Γ A;var142
 = λ x Tm142 var142 lam app → var142 _ _ x

lam142 : ∀{Γ A B} → Tm142 (snoc142 Γ A) B → Tm142 Γ (arr142 A B);lam142
 = λ t Tm142 var142 lam142 app → lam142 _ _ _ (t Tm142 var142 lam142 app)

app142 : ∀{Γ A B} → Tm142 Γ (arr142 A B) → Tm142 Γ A → Tm142 Γ B;app142
 = λ t u Tm142 var142 lam142 app142 →
     app142 _ _ _ (t Tm142 var142 lam142 app142) (u Tm142 var142 lam142 app142)

v0142 : ∀{Γ A} → Tm142 (snoc142 Γ A) A;v0142
 = var142 vz142

v1142 : ∀{Γ A B} → Tm142 (snoc142 (snoc142 Γ A) B) A;v1142
 = var142 (vs142 vz142)

v2142 : ∀{Γ A B C} → Tm142 (snoc142 (snoc142 (snoc142 Γ A) B) C) A;v2142
 = var142 (vs142 (vs142 vz142))

v3142 : ∀{Γ A B C D} → Tm142 (snoc142 (snoc142 (snoc142 (snoc142 Γ A) B) C) D) A;v3142
 = var142 (vs142 (vs142 (vs142 vz142)))

v4142 : ∀{Γ A B C D E} → Tm142 (snoc142 (snoc142 (snoc142 (snoc142 (snoc142 Γ A) B) C) D) E) A;v4142
 = var142 (vs142 (vs142 (vs142 (vs142 vz142))))

test142 : ∀{Γ A} → Tm142 Γ (arr142 (arr142 A A) (arr142 A A));test142
  = lam142 (lam142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 v0142)))))))
{-# OPTIONS --type-in-type #-}

Ty143 : Set; Ty143
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι143   : Ty143; ι143 = λ _ ι143 _ → ι143
arr143 : Ty143 → Ty143 → Ty143; arr143 = λ A B Ty143 ι143 arr143 → arr143 (A Ty143 ι143 arr143) (B Ty143 ι143 arr143)

Con143 : Set;Con143
 = (Con143 : Set)
   (nil  : Con143)
   (snoc : Con143 → Ty143 → Con143)
 → Con143

nil143 : Con143;nil143
 = λ Con143 nil143 snoc → nil143

snoc143 : Con143 → Ty143 → Con143;snoc143
 = λ Γ A Con143 nil143 snoc143 → snoc143 (Γ Con143 nil143 snoc143) A

Var143 : Con143 → Ty143 → Set;Var143
 = λ Γ A →
   (Var143 : Con143 → Ty143 → Set)
   (vz  : (Γ : _)(A : _) → Var143 (snoc143 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var143 Γ A → Var143 (snoc143 Γ B) A)
 → Var143 Γ A

vz143 : ∀{Γ A} → Var143 (snoc143 Γ A) A;vz143
 = λ Var143 vz143 vs → vz143 _ _

vs143 : ∀{Γ B A} → Var143 Γ A → Var143 (snoc143 Γ B) A;vs143
 = λ x Var143 vz143 vs143 → vs143 _ _ _ (x Var143 vz143 vs143)

Tm143 : Con143 → Ty143 → Set;Tm143
 = λ Γ A →
   (Tm143    : Con143 → Ty143 → Set)
   (var   : (Γ : _) (A : _) → Var143 Γ A → Tm143 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm143 (snoc143 Γ A) B → Tm143 Γ (arr143 A B))
   (app   : (Γ : _) (A B : _) → Tm143 Γ (arr143 A B) → Tm143 Γ A → Tm143 Γ B)
 → Tm143 Γ A

var143 : ∀{Γ A} → Var143 Γ A → Tm143 Γ A;var143
 = λ x Tm143 var143 lam app → var143 _ _ x

lam143 : ∀{Γ A B} → Tm143 (snoc143 Γ A) B → Tm143 Γ (arr143 A B);lam143
 = λ t Tm143 var143 lam143 app → lam143 _ _ _ (t Tm143 var143 lam143 app)

app143 : ∀{Γ A B} → Tm143 Γ (arr143 A B) → Tm143 Γ A → Tm143 Γ B;app143
 = λ t u Tm143 var143 lam143 app143 →
     app143 _ _ _ (t Tm143 var143 lam143 app143) (u Tm143 var143 lam143 app143)

v0143 : ∀{Γ A} → Tm143 (snoc143 Γ A) A;v0143
 = var143 vz143

v1143 : ∀{Γ A B} → Tm143 (snoc143 (snoc143 Γ A) B) A;v1143
 = var143 (vs143 vz143)

v2143 : ∀{Γ A B C} → Tm143 (snoc143 (snoc143 (snoc143 Γ A) B) C) A;v2143
 = var143 (vs143 (vs143 vz143))

v3143 : ∀{Γ A B C D} → Tm143 (snoc143 (snoc143 (snoc143 (snoc143 Γ A) B) C) D) A;v3143
 = var143 (vs143 (vs143 (vs143 vz143)))

v4143 : ∀{Γ A B C D E} → Tm143 (snoc143 (snoc143 (snoc143 (snoc143 (snoc143 Γ A) B) C) D) E) A;v4143
 = var143 (vs143 (vs143 (vs143 (vs143 vz143))))

test143 : ∀{Γ A} → Tm143 Γ (arr143 (arr143 A A) (arr143 A A));test143
  = lam143 (lam143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 v0143)))))))
{-# OPTIONS --type-in-type #-}

Ty144 : Set; Ty144
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι144   : Ty144; ι144 = λ _ ι144 _ → ι144
arr144 : Ty144 → Ty144 → Ty144; arr144 = λ A B Ty144 ι144 arr144 → arr144 (A Ty144 ι144 arr144) (B Ty144 ι144 arr144)

Con144 : Set;Con144
 = (Con144 : Set)
   (nil  : Con144)
   (snoc : Con144 → Ty144 → Con144)
 → Con144

nil144 : Con144;nil144
 = λ Con144 nil144 snoc → nil144

snoc144 : Con144 → Ty144 → Con144;snoc144
 = λ Γ A Con144 nil144 snoc144 → snoc144 (Γ Con144 nil144 snoc144) A

Var144 : Con144 → Ty144 → Set;Var144
 = λ Γ A →
   (Var144 : Con144 → Ty144 → Set)
   (vz  : (Γ : _)(A : _) → Var144 (snoc144 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var144 Γ A → Var144 (snoc144 Γ B) A)
 → Var144 Γ A

vz144 : ∀{Γ A} → Var144 (snoc144 Γ A) A;vz144
 = λ Var144 vz144 vs → vz144 _ _

vs144 : ∀{Γ B A} → Var144 Γ A → Var144 (snoc144 Γ B) A;vs144
 = λ x Var144 vz144 vs144 → vs144 _ _ _ (x Var144 vz144 vs144)

Tm144 : Con144 → Ty144 → Set;Tm144
 = λ Γ A →
   (Tm144    : Con144 → Ty144 → Set)
   (var   : (Γ : _) (A : _) → Var144 Γ A → Tm144 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm144 (snoc144 Γ A) B → Tm144 Γ (arr144 A B))
   (app   : (Γ : _) (A B : _) → Tm144 Γ (arr144 A B) → Tm144 Γ A → Tm144 Γ B)
 → Tm144 Γ A

var144 : ∀{Γ A} → Var144 Γ A → Tm144 Γ A;var144
 = λ x Tm144 var144 lam app → var144 _ _ x

lam144 : ∀{Γ A B} → Tm144 (snoc144 Γ A) B → Tm144 Γ (arr144 A B);lam144
 = λ t Tm144 var144 lam144 app → lam144 _ _ _ (t Tm144 var144 lam144 app)

app144 : ∀{Γ A B} → Tm144 Γ (arr144 A B) → Tm144 Γ A → Tm144 Γ B;app144
 = λ t u Tm144 var144 lam144 app144 →
     app144 _ _ _ (t Tm144 var144 lam144 app144) (u Tm144 var144 lam144 app144)

v0144 : ∀{Γ A} → Tm144 (snoc144 Γ A) A;v0144
 = var144 vz144

v1144 : ∀{Γ A B} → Tm144 (snoc144 (snoc144 Γ A) B) A;v1144
 = var144 (vs144 vz144)

v2144 : ∀{Γ A B C} → Tm144 (snoc144 (snoc144 (snoc144 Γ A) B) C) A;v2144
 = var144 (vs144 (vs144 vz144))

v3144 : ∀{Γ A B C D} → Tm144 (snoc144 (snoc144 (snoc144 (snoc144 Γ A) B) C) D) A;v3144
 = var144 (vs144 (vs144 (vs144 vz144)))

v4144 : ∀{Γ A B C D E} → Tm144 (snoc144 (snoc144 (snoc144 (snoc144 (snoc144 Γ A) B) C) D) E) A;v4144
 = var144 (vs144 (vs144 (vs144 (vs144 vz144))))

test144 : ∀{Γ A} → Tm144 Γ (arr144 (arr144 A A) (arr144 A A));test144
  = lam144 (lam144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 v0144)))))))
{-# OPTIONS --type-in-type #-}

Ty145 : Set; Ty145
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι145   : Ty145; ι145 = λ _ ι145 _ → ι145
arr145 : Ty145 → Ty145 → Ty145; arr145 = λ A B Ty145 ι145 arr145 → arr145 (A Ty145 ι145 arr145) (B Ty145 ι145 arr145)

Con145 : Set;Con145
 = (Con145 : Set)
   (nil  : Con145)
   (snoc : Con145 → Ty145 → Con145)
 → Con145

nil145 : Con145;nil145
 = λ Con145 nil145 snoc → nil145

snoc145 : Con145 → Ty145 → Con145;snoc145
 = λ Γ A Con145 nil145 snoc145 → snoc145 (Γ Con145 nil145 snoc145) A

Var145 : Con145 → Ty145 → Set;Var145
 = λ Γ A →
   (Var145 : Con145 → Ty145 → Set)
   (vz  : (Γ : _)(A : _) → Var145 (snoc145 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var145 Γ A → Var145 (snoc145 Γ B) A)
 → Var145 Γ A

vz145 : ∀{Γ A} → Var145 (snoc145 Γ A) A;vz145
 = λ Var145 vz145 vs → vz145 _ _

vs145 : ∀{Γ B A} → Var145 Γ A → Var145 (snoc145 Γ B) A;vs145
 = λ x Var145 vz145 vs145 → vs145 _ _ _ (x Var145 vz145 vs145)

Tm145 : Con145 → Ty145 → Set;Tm145
 = λ Γ A →
   (Tm145    : Con145 → Ty145 → Set)
   (var   : (Γ : _) (A : _) → Var145 Γ A → Tm145 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm145 (snoc145 Γ A) B → Tm145 Γ (arr145 A B))
   (app   : (Γ : _) (A B : _) → Tm145 Γ (arr145 A B) → Tm145 Γ A → Tm145 Γ B)
 → Tm145 Γ A

var145 : ∀{Γ A} → Var145 Γ A → Tm145 Γ A;var145
 = λ x Tm145 var145 lam app → var145 _ _ x

lam145 : ∀{Γ A B} → Tm145 (snoc145 Γ A) B → Tm145 Γ (arr145 A B);lam145
 = λ t Tm145 var145 lam145 app → lam145 _ _ _ (t Tm145 var145 lam145 app)

app145 : ∀{Γ A B} → Tm145 Γ (arr145 A B) → Tm145 Γ A → Tm145 Γ B;app145
 = λ t u Tm145 var145 lam145 app145 →
     app145 _ _ _ (t Tm145 var145 lam145 app145) (u Tm145 var145 lam145 app145)

v0145 : ∀{Γ A} → Tm145 (snoc145 Γ A) A;v0145
 = var145 vz145

v1145 : ∀{Γ A B} → Tm145 (snoc145 (snoc145 Γ A) B) A;v1145
 = var145 (vs145 vz145)

v2145 : ∀{Γ A B C} → Tm145 (snoc145 (snoc145 (snoc145 Γ A) B) C) A;v2145
 = var145 (vs145 (vs145 vz145))

v3145 : ∀{Γ A B C D} → Tm145 (snoc145 (snoc145 (snoc145 (snoc145 Γ A) B) C) D) A;v3145
 = var145 (vs145 (vs145 (vs145 vz145)))

v4145 : ∀{Γ A B C D E} → Tm145 (snoc145 (snoc145 (snoc145 (snoc145 (snoc145 Γ A) B) C) D) E) A;v4145
 = var145 (vs145 (vs145 (vs145 (vs145 vz145))))

test145 : ∀{Γ A} → Tm145 Γ (arr145 (arr145 A A) (arr145 A A));test145
  = lam145 (lam145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 v0145)))))))
{-# OPTIONS --type-in-type #-}

Ty146 : Set; Ty146
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι146   : Ty146; ι146 = λ _ ι146 _ → ι146
arr146 : Ty146 → Ty146 → Ty146; arr146 = λ A B Ty146 ι146 arr146 → arr146 (A Ty146 ι146 arr146) (B Ty146 ι146 arr146)

Con146 : Set;Con146
 = (Con146 : Set)
   (nil  : Con146)
   (snoc : Con146 → Ty146 → Con146)
 → Con146

nil146 : Con146;nil146
 = λ Con146 nil146 snoc → nil146

snoc146 : Con146 → Ty146 → Con146;snoc146
 = λ Γ A Con146 nil146 snoc146 → snoc146 (Γ Con146 nil146 snoc146) A

Var146 : Con146 → Ty146 → Set;Var146
 = λ Γ A →
   (Var146 : Con146 → Ty146 → Set)
   (vz  : (Γ : _)(A : _) → Var146 (snoc146 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var146 Γ A → Var146 (snoc146 Γ B) A)
 → Var146 Γ A

vz146 : ∀{Γ A} → Var146 (snoc146 Γ A) A;vz146
 = λ Var146 vz146 vs → vz146 _ _

vs146 : ∀{Γ B A} → Var146 Γ A → Var146 (snoc146 Γ B) A;vs146
 = λ x Var146 vz146 vs146 → vs146 _ _ _ (x Var146 vz146 vs146)

Tm146 : Con146 → Ty146 → Set;Tm146
 = λ Γ A →
   (Tm146    : Con146 → Ty146 → Set)
   (var   : (Γ : _) (A : _) → Var146 Γ A → Tm146 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm146 (snoc146 Γ A) B → Tm146 Γ (arr146 A B))
   (app   : (Γ : _) (A B : _) → Tm146 Γ (arr146 A B) → Tm146 Γ A → Tm146 Γ B)
 → Tm146 Γ A

var146 : ∀{Γ A} → Var146 Γ A → Tm146 Γ A;var146
 = λ x Tm146 var146 lam app → var146 _ _ x

lam146 : ∀{Γ A B} → Tm146 (snoc146 Γ A) B → Tm146 Γ (arr146 A B);lam146
 = λ t Tm146 var146 lam146 app → lam146 _ _ _ (t Tm146 var146 lam146 app)

app146 : ∀{Γ A B} → Tm146 Γ (arr146 A B) → Tm146 Γ A → Tm146 Γ B;app146
 = λ t u Tm146 var146 lam146 app146 →
     app146 _ _ _ (t Tm146 var146 lam146 app146) (u Tm146 var146 lam146 app146)

v0146 : ∀{Γ A} → Tm146 (snoc146 Γ A) A;v0146
 = var146 vz146

v1146 : ∀{Γ A B} → Tm146 (snoc146 (snoc146 Γ A) B) A;v1146
 = var146 (vs146 vz146)

v2146 : ∀{Γ A B C} → Tm146 (snoc146 (snoc146 (snoc146 Γ A) B) C) A;v2146
 = var146 (vs146 (vs146 vz146))

v3146 : ∀{Γ A B C D} → Tm146 (snoc146 (snoc146 (snoc146 (snoc146 Γ A) B) C) D) A;v3146
 = var146 (vs146 (vs146 (vs146 vz146)))

v4146 : ∀{Γ A B C D E} → Tm146 (snoc146 (snoc146 (snoc146 (snoc146 (snoc146 Γ A) B) C) D) E) A;v4146
 = var146 (vs146 (vs146 (vs146 (vs146 vz146))))

test146 : ∀{Γ A} → Tm146 Γ (arr146 (arr146 A A) (arr146 A A));test146
  = lam146 (lam146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 v0146)))))))
{-# OPTIONS --type-in-type #-}

Ty147 : Set; Ty147
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι147   : Ty147; ι147 = λ _ ι147 _ → ι147
arr147 : Ty147 → Ty147 → Ty147; arr147 = λ A B Ty147 ι147 arr147 → arr147 (A Ty147 ι147 arr147) (B Ty147 ι147 arr147)

Con147 : Set;Con147
 = (Con147 : Set)
   (nil  : Con147)
   (snoc : Con147 → Ty147 → Con147)
 → Con147

nil147 : Con147;nil147
 = λ Con147 nil147 snoc → nil147

snoc147 : Con147 → Ty147 → Con147;snoc147
 = λ Γ A Con147 nil147 snoc147 → snoc147 (Γ Con147 nil147 snoc147) A

Var147 : Con147 → Ty147 → Set;Var147
 = λ Γ A →
   (Var147 : Con147 → Ty147 → Set)
   (vz  : (Γ : _)(A : _) → Var147 (snoc147 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var147 Γ A → Var147 (snoc147 Γ B) A)
 → Var147 Γ A

vz147 : ∀{Γ A} → Var147 (snoc147 Γ A) A;vz147
 = λ Var147 vz147 vs → vz147 _ _

vs147 : ∀{Γ B A} → Var147 Γ A → Var147 (snoc147 Γ B) A;vs147
 = λ x Var147 vz147 vs147 → vs147 _ _ _ (x Var147 vz147 vs147)

Tm147 : Con147 → Ty147 → Set;Tm147
 = λ Γ A →
   (Tm147    : Con147 → Ty147 → Set)
   (var   : (Γ : _) (A : _) → Var147 Γ A → Tm147 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm147 (snoc147 Γ A) B → Tm147 Γ (arr147 A B))
   (app   : (Γ : _) (A B : _) → Tm147 Γ (arr147 A B) → Tm147 Γ A → Tm147 Γ B)
 → Tm147 Γ A

var147 : ∀{Γ A} → Var147 Γ A → Tm147 Γ A;var147
 = λ x Tm147 var147 lam app → var147 _ _ x

lam147 : ∀{Γ A B} → Tm147 (snoc147 Γ A) B → Tm147 Γ (arr147 A B);lam147
 = λ t Tm147 var147 lam147 app → lam147 _ _ _ (t Tm147 var147 lam147 app)

app147 : ∀{Γ A B} → Tm147 Γ (arr147 A B) → Tm147 Γ A → Tm147 Γ B;app147
 = λ t u Tm147 var147 lam147 app147 →
     app147 _ _ _ (t Tm147 var147 lam147 app147) (u Tm147 var147 lam147 app147)

v0147 : ∀{Γ A} → Tm147 (snoc147 Γ A) A;v0147
 = var147 vz147

v1147 : ∀{Γ A B} → Tm147 (snoc147 (snoc147 Γ A) B) A;v1147
 = var147 (vs147 vz147)

v2147 : ∀{Γ A B C} → Tm147 (snoc147 (snoc147 (snoc147 Γ A) B) C) A;v2147
 = var147 (vs147 (vs147 vz147))

v3147 : ∀{Γ A B C D} → Tm147 (snoc147 (snoc147 (snoc147 (snoc147 Γ A) B) C) D) A;v3147
 = var147 (vs147 (vs147 (vs147 vz147)))

v4147 : ∀{Γ A B C D E} → Tm147 (snoc147 (snoc147 (snoc147 (snoc147 (snoc147 Γ A) B) C) D) E) A;v4147
 = var147 (vs147 (vs147 (vs147 (vs147 vz147))))

test147 : ∀{Γ A} → Tm147 Γ (arr147 (arr147 A A) (arr147 A A));test147
  = lam147 (lam147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 v0147)))))))
{-# OPTIONS --type-in-type #-}

Ty148 : Set; Ty148
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι148   : Ty148; ι148 = λ _ ι148 _ → ι148
arr148 : Ty148 → Ty148 → Ty148; arr148 = λ A B Ty148 ι148 arr148 → arr148 (A Ty148 ι148 arr148) (B Ty148 ι148 arr148)

Con148 : Set;Con148
 = (Con148 : Set)
   (nil  : Con148)
   (snoc : Con148 → Ty148 → Con148)
 → Con148

nil148 : Con148;nil148
 = λ Con148 nil148 snoc → nil148

snoc148 : Con148 → Ty148 → Con148;snoc148
 = λ Γ A Con148 nil148 snoc148 → snoc148 (Γ Con148 nil148 snoc148) A

Var148 : Con148 → Ty148 → Set;Var148
 = λ Γ A →
   (Var148 : Con148 → Ty148 → Set)
   (vz  : (Γ : _)(A : _) → Var148 (snoc148 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var148 Γ A → Var148 (snoc148 Γ B) A)
 → Var148 Γ A

vz148 : ∀{Γ A} → Var148 (snoc148 Γ A) A;vz148
 = λ Var148 vz148 vs → vz148 _ _

vs148 : ∀{Γ B A} → Var148 Γ A → Var148 (snoc148 Γ B) A;vs148
 = λ x Var148 vz148 vs148 → vs148 _ _ _ (x Var148 vz148 vs148)

Tm148 : Con148 → Ty148 → Set;Tm148
 = λ Γ A →
   (Tm148    : Con148 → Ty148 → Set)
   (var   : (Γ : _) (A : _) → Var148 Γ A → Tm148 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm148 (snoc148 Γ A) B → Tm148 Γ (arr148 A B))
   (app   : (Γ : _) (A B : _) → Tm148 Γ (arr148 A B) → Tm148 Γ A → Tm148 Γ B)
 → Tm148 Γ A

var148 : ∀{Γ A} → Var148 Γ A → Tm148 Γ A;var148
 = λ x Tm148 var148 lam app → var148 _ _ x

lam148 : ∀{Γ A B} → Tm148 (snoc148 Γ A) B → Tm148 Γ (arr148 A B);lam148
 = λ t Tm148 var148 lam148 app → lam148 _ _ _ (t Tm148 var148 lam148 app)

app148 : ∀{Γ A B} → Tm148 Γ (arr148 A B) → Tm148 Γ A → Tm148 Γ B;app148
 = λ t u Tm148 var148 lam148 app148 →
     app148 _ _ _ (t Tm148 var148 lam148 app148) (u Tm148 var148 lam148 app148)

v0148 : ∀{Γ A} → Tm148 (snoc148 Γ A) A;v0148
 = var148 vz148

v1148 : ∀{Γ A B} → Tm148 (snoc148 (snoc148 Γ A) B) A;v1148
 = var148 (vs148 vz148)

v2148 : ∀{Γ A B C} → Tm148 (snoc148 (snoc148 (snoc148 Γ A) B) C) A;v2148
 = var148 (vs148 (vs148 vz148))

v3148 : ∀{Γ A B C D} → Tm148 (snoc148 (snoc148 (snoc148 (snoc148 Γ A) B) C) D) A;v3148
 = var148 (vs148 (vs148 (vs148 vz148)))

v4148 : ∀{Γ A B C D E} → Tm148 (snoc148 (snoc148 (snoc148 (snoc148 (snoc148 Γ A) B) C) D) E) A;v4148
 = var148 (vs148 (vs148 (vs148 (vs148 vz148))))

test148 : ∀{Γ A} → Tm148 Γ (arr148 (arr148 A A) (arr148 A A));test148
  = lam148 (lam148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 v0148)))))))
{-# OPTIONS --type-in-type #-}

Ty149 : Set; Ty149
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι149   : Ty149; ι149 = λ _ ι149 _ → ι149
arr149 : Ty149 → Ty149 → Ty149; arr149 = λ A B Ty149 ι149 arr149 → arr149 (A Ty149 ι149 arr149) (B Ty149 ι149 arr149)

Con149 : Set;Con149
 = (Con149 : Set)
   (nil  : Con149)
   (snoc : Con149 → Ty149 → Con149)
 → Con149

nil149 : Con149;nil149
 = λ Con149 nil149 snoc → nil149

snoc149 : Con149 → Ty149 → Con149;snoc149
 = λ Γ A Con149 nil149 snoc149 → snoc149 (Γ Con149 nil149 snoc149) A

Var149 : Con149 → Ty149 → Set;Var149
 = λ Γ A →
   (Var149 : Con149 → Ty149 → Set)
   (vz  : (Γ : _)(A : _) → Var149 (snoc149 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var149 Γ A → Var149 (snoc149 Γ B) A)
 → Var149 Γ A

vz149 : ∀{Γ A} → Var149 (snoc149 Γ A) A;vz149
 = λ Var149 vz149 vs → vz149 _ _

vs149 : ∀{Γ B A} → Var149 Γ A → Var149 (snoc149 Γ B) A;vs149
 = λ x Var149 vz149 vs149 → vs149 _ _ _ (x Var149 vz149 vs149)

Tm149 : Con149 → Ty149 → Set;Tm149
 = λ Γ A →
   (Tm149    : Con149 → Ty149 → Set)
   (var   : (Γ : _) (A : _) → Var149 Γ A → Tm149 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm149 (snoc149 Γ A) B → Tm149 Γ (arr149 A B))
   (app   : (Γ : _) (A B : _) → Tm149 Γ (arr149 A B) → Tm149 Γ A → Tm149 Γ B)
 → Tm149 Γ A

var149 : ∀{Γ A} → Var149 Γ A → Tm149 Γ A;var149
 = λ x Tm149 var149 lam app → var149 _ _ x

lam149 : ∀{Γ A B} → Tm149 (snoc149 Γ A) B → Tm149 Γ (arr149 A B);lam149
 = λ t Tm149 var149 lam149 app → lam149 _ _ _ (t Tm149 var149 lam149 app)

app149 : ∀{Γ A B} → Tm149 Γ (arr149 A B) → Tm149 Γ A → Tm149 Γ B;app149
 = λ t u Tm149 var149 lam149 app149 →
     app149 _ _ _ (t Tm149 var149 lam149 app149) (u Tm149 var149 lam149 app149)

v0149 : ∀{Γ A} → Tm149 (snoc149 Γ A) A;v0149
 = var149 vz149

v1149 : ∀{Γ A B} → Tm149 (snoc149 (snoc149 Γ A) B) A;v1149
 = var149 (vs149 vz149)

v2149 : ∀{Γ A B C} → Tm149 (snoc149 (snoc149 (snoc149 Γ A) B) C) A;v2149
 = var149 (vs149 (vs149 vz149))

v3149 : ∀{Γ A B C D} → Tm149 (snoc149 (snoc149 (snoc149 (snoc149 Γ A) B) C) D) A;v3149
 = var149 (vs149 (vs149 (vs149 vz149)))

v4149 : ∀{Γ A B C D E} → Tm149 (snoc149 (snoc149 (snoc149 (snoc149 (snoc149 Γ A) B) C) D) E) A;v4149
 = var149 (vs149 (vs149 (vs149 (vs149 vz149))))

test149 : ∀{Γ A} → Tm149 Γ (arr149 (arr149 A A) (arr149 A A));test149
  = lam149 (lam149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 v0149)))))))
{-# OPTIONS --type-in-type #-}

Ty150 : Set; Ty150
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι150   : Ty150; ι150 = λ _ ι150 _ → ι150
arr150 : Ty150 → Ty150 → Ty150; arr150 = λ A B Ty150 ι150 arr150 → arr150 (A Ty150 ι150 arr150) (B Ty150 ι150 arr150)

Con150 : Set;Con150
 = (Con150 : Set)
   (nil  : Con150)
   (snoc : Con150 → Ty150 → Con150)
 → Con150

nil150 : Con150;nil150
 = λ Con150 nil150 snoc → nil150

snoc150 : Con150 → Ty150 → Con150;snoc150
 = λ Γ A Con150 nil150 snoc150 → snoc150 (Γ Con150 nil150 snoc150) A

Var150 : Con150 → Ty150 → Set;Var150
 = λ Γ A →
   (Var150 : Con150 → Ty150 → Set)
   (vz  : (Γ : _)(A : _) → Var150 (snoc150 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var150 Γ A → Var150 (snoc150 Γ B) A)
 → Var150 Γ A

vz150 : ∀{Γ A} → Var150 (snoc150 Γ A) A;vz150
 = λ Var150 vz150 vs → vz150 _ _

vs150 : ∀{Γ B A} → Var150 Γ A → Var150 (snoc150 Γ B) A;vs150
 = λ x Var150 vz150 vs150 → vs150 _ _ _ (x Var150 vz150 vs150)

Tm150 : Con150 → Ty150 → Set;Tm150
 = λ Γ A →
   (Tm150    : Con150 → Ty150 → Set)
   (var   : (Γ : _) (A : _) → Var150 Γ A → Tm150 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm150 (snoc150 Γ A) B → Tm150 Γ (arr150 A B))
   (app   : (Γ : _) (A B : _) → Tm150 Γ (arr150 A B) → Tm150 Γ A → Tm150 Γ B)
 → Tm150 Γ A

var150 : ∀{Γ A} → Var150 Γ A → Tm150 Γ A;var150
 = λ x Tm150 var150 lam app → var150 _ _ x

lam150 : ∀{Γ A B} → Tm150 (snoc150 Γ A) B → Tm150 Γ (arr150 A B);lam150
 = λ t Tm150 var150 lam150 app → lam150 _ _ _ (t Tm150 var150 lam150 app)

app150 : ∀{Γ A B} → Tm150 Γ (arr150 A B) → Tm150 Γ A → Tm150 Γ B;app150
 = λ t u Tm150 var150 lam150 app150 →
     app150 _ _ _ (t Tm150 var150 lam150 app150) (u Tm150 var150 lam150 app150)

v0150 : ∀{Γ A} → Tm150 (snoc150 Γ A) A;v0150
 = var150 vz150

v1150 : ∀{Γ A B} → Tm150 (snoc150 (snoc150 Γ A) B) A;v1150
 = var150 (vs150 vz150)

v2150 : ∀{Γ A B C} → Tm150 (snoc150 (snoc150 (snoc150 Γ A) B) C) A;v2150
 = var150 (vs150 (vs150 vz150))

v3150 : ∀{Γ A B C D} → Tm150 (snoc150 (snoc150 (snoc150 (snoc150 Γ A) B) C) D) A;v3150
 = var150 (vs150 (vs150 (vs150 vz150)))

v4150 : ∀{Γ A B C D E} → Tm150 (snoc150 (snoc150 (snoc150 (snoc150 (snoc150 Γ A) B) C) D) E) A;v4150
 = var150 (vs150 (vs150 (vs150 (vs150 vz150))))

test150 : ∀{Γ A} → Tm150 Γ (arr150 (arr150 A A) (arr150 A A));test150
  = lam150 (lam150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 v0150)))))))
{-# OPTIONS --type-in-type #-}

Ty151 : Set; Ty151
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι151   : Ty151; ι151 = λ _ ι151 _ → ι151
arr151 : Ty151 → Ty151 → Ty151; arr151 = λ A B Ty151 ι151 arr151 → arr151 (A Ty151 ι151 arr151) (B Ty151 ι151 arr151)

Con151 : Set;Con151
 = (Con151 : Set)
   (nil  : Con151)
   (snoc : Con151 → Ty151 → Con151)
 → Con151

nil151 : Con151;nil151
 = λ Con151 nil151 snoc → nil151

snoc151 : Con151 → Ty151 → Con151;snoc151
 = λ Γ A Con151 nil151 snoc151 → snoc151 (Γ Con151 nil151 snoc151) A

Var151 : Con151 → Ty151 → Set;Var151
 = λ Γ A →
   (Var151 : Con151 → Ty151 → Set)
   (vz  : (Γ : _)(A : _) → Var151 (snoc151 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var151 Γ A → Var151 (snoc151 Γ B) A)
 → Var151 Γ A

vz151 : ∀{Γ A} → Var151 (snoc151 Γ A) A;vz151
 = λ Var151 vz151 vs → vz151 _ _

vs151 : ∀{Γ B A} → Var151 Γ A → Var151 (snoc151 Γ B) A;vs151
 = λ x Var151 vz151 vs151 → vs151 _ _ _ (x Var151 vz151 vs151)

Tm151 : Con151 → Ty151 → Set;Tm151
 = λ Γ A →
   (Tm151    : Con151 → Ty151 → Set)
   (var   : (Γ : _) (A : _) → Var151 Γ A → Tm151 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm151 (snoc151 Γ A) B → Tm151 Γ (arr151 A B))
   (app   : (Γ : _) (A B : _) → Tm151 Γ (arr151 A B) → Tm151 Γ A → Tm151 Γ B)
 → Tm151 Γ A

var151 : ∀{Γ A} → Var151 Γ A → Tm151 Γ A;var151
 = λ x Tm151 var151 lam app → var151 _ _ x

lam151 : ∀{Γ A B} → Tm151 (snoc151 Γ A) B → Tm151 Γ (arr151 A B);lam151
 = λ t Tm151 var151 lam151 app → lam151 _ _ _ (t Tm151 var151 lam151 app)

app151 : ∀{Γ A B} → Tm151 Γ (arr151 A B) → Tm151 Γ A → Tm151 Γ B;app151
 = λ t u Tm151 var151 lam151 app151 →
     app151 _ _ _ (t Tm151 var151 lam151 app151) (u Tm151 var151 lam151 app151)

v0151 : ∀{Γ A} → Tm151 (snoc151 Γ A) A;v0151
 = var151 vz151

v1151 : ∀{Γ A B} → Tm151 (snoc151 (snoc151 Γ A) B) A;v1151
 = var151 (vs151 vz151)

v2151 : ∀{Γ A B C} → Tm151 (snoc151 (snoc151 (snoc151 Γ A) B) C) A;v2151
 = var151 (vs151 (vs151 vz151))

v3151 : ∀{Γ A B C D} → Tm151 (snoc151 (snoc151 (snoc151 (snoc151 Γ A) B) C) D) A;v3151
 = var151 (vs151 (vs151 (vs151 vz151)))

v4151 : ∀{Γ A B C D E} → Tm151 (snoc151 (snoc151 (snoc151 (snoc151 (snoc151 Γ A) B) C) D) E) A;v4151
 = var151 (vs151 (vs151 (vs151 (vs151 vz151))))

test151 : ∀{Γ A} → Tm151 Γ (arr151 (arr151 A A) (arr151 A A));test151
  = lam151 (lam151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 v0151)))))))
{-# OPTIONS --type-in-type #-}

Ty152 : Set; Ty152
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι152   : Ty152; ι152 = λ _ ι152 _ → ι152
arr152 : Ty152 → Ty152 → Ty152; arr152 = λ A B Ty152 ι152 arr152 → arr152 (A Ty152 ι152 arr152) (B Ty152 ι152 arr152)

Con152 : Set;Con152
 = (Con152 : Set)
   (nil  : Con152)
   (snoc : Con152 → Ty152 → Con152)
 → Con152

nil152 : Con152;nil152
 = λ Con152 nil152 snoc → nil152

snoc152 : Con152 → Ty152 → Con152;snoc152
 = λ Γ A Con152 nil152 snoc152 → snoc152 (Γ Con152 nil152 snoc152) A

Var152 : Con152 → Ty152 → Set;Var152
 = λ Γ A →
   (Var152 : Con152 → Ty152 → Set)
   (vz  : (Γ : _)(A : _) → Var152 (snoc152 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var152 Γ A → Var152 (snoc152 Γ B) A)
 → Var152 Γ A

vz152 : ∀{Γ A} → Var152 (snoc152 Γ A) A;vz152
 = λ Var152 vz152 vs → vz152 _ _

vs152 : ∀{Γ B A} → Var152 Γ A → Var152 (snoc152 Γ B) A;vs152
 = λ x Var152 vz152 vs152 → vs152 _ _ _ (x Var152 vz152 vs152)

Tm152 : Con152 → Ty152 → Set;Tm152
 = λ Γ A →
   (Tm152    : Con152 → Ty152 → Set)
   (var   : (Γ : _) (A : _) → Var152 Γ A → Tm152 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm152 (snoc152 Γ A) B → Tm152 Γ (arr152 A B))
   (app   : (Γ : _) (A B : _) → Tm152 Γ (arr152 A B) → Tm152 Γ A → Tm152 Γ B)
 → Tm152 Γ A

var152 : ∀{Γ A} → Var152 Γ A → Tm152 Γ A;var152
 = λ x Tm152 var152 lam app → var152 _ _ x

lam152 : ∀{Γ A B} → Tm152 (snoc152 Γ A) B → Tm152 Γ (arr152 A B);lam152
 = λ t Tm152 var152 lam152 app → lam152 _ _ _ (t Tm152 var152 lam152 app)

app152 : ∀{Γ A B} → Tm152 Γ (arr152 A B) → Tm152 Γ A → Tm152 Γ B;app152
 = λ t u Tm152 var152 lam152 app152 →
     app152 _ _ _ (t Tm152 var152 lam152 app152) (u Tm152 var152 lam152 app152)

v0152 : ∀{Γ A} → Tm152 (snoc152 Γ A) A;v0152
 = var152 vz152

v1152 : ∀{Γ A B} → Tm152 (snoc152 (snoc152 Γ A) B) A;v1152
 = var152 (vs152 vz152)

v2152 : ∀{Γ A B C} → Tm152 (snoc152 (snoc152 (snoc152 Γ A) B) C) A;v2152
 = var152 (vs152 (vs152 vz152))

v3152 : ∀{Γ A B C D} → Tm152 (snoc152 (snoc152 (snoc152 (snoc152 Γ A) B) C) D) A;v3152
 = var152 (vs152 (vs152 (vs152 vz152)))

v4152 : ∀{Γ A B C D E} → Tm152 (snoc152 (snoc152 (snoc152 (snoc152 (snoc152 Γ A) B) C) D) E) A;v4152
 = var152 (vs152 (vs152 (vs152 (vs152 vz152))))

test152 : ∀{Γ A} → Tm152 Γ (arr152 (arr152 A A) (arr152 A A));test152
  = lam152 (lam152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 v0152)))))))
{-# OPTIONS --type-in-type #-}

Ty153 : Set; Ty153
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι153   : Ty153; ι153 = λ _ ι153 _ → ι153
arr153 : Ty153 → Ty153 → Ty153; arr153 = λ A B Ty153 ι153 arr153 → arr153 (A Ty153 ι153 arr153) (B Ty153 ι153 arr153)

Con153 : Set;Con153
 = (Con153 : Set)
   (nil  : Con153)
   (snoc : Con153 → Ty153 → Con153)
 → Con153

nil153 : Con153;nil153
 = λ Con153 nil153 snoc → nil153

snoc153 : Con153 → Ty153 → Con153;snoc153
 = λ Γ A Con153 nil153 snoc153 → snoc153 (Γ Con153 nil153 snoc153) A

Var153 : Con153 → Ty153 → Set;Var153
 = λ Γ A →
   (Var153 : Con153 → Ty153 → Set)
   (vz  : (Γ : _)(A : _) → Var153 (snoc153 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var153 Γ A → Var153 (snoc153 Γ B) A)
 → Var153 Γ A

vz153 : ∀{Γ A} → Var153 (snoc153 Γ A) A;vz153
 = λ Var153 vz153 vs → vz153 _ _

vs153 : ∀{Γ B A} → Var153 Γ A → Var153 (snoc153 Γ B) A;vs153
 = λ x Var153 vz153 vs153 → vs153 _ _ _ (x Var153 vz153 vs153)

Tm153 : Con153 → Ty153 → Set;Tm153
 = λ Γ A →
   (Tm153    : Con153 → Ty153 → Set)
   (var   : (Γ : _) (A : _) → Var153 Γ A → Tm153 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm153 (snoc153 Γ A) B → Tm153 Γ (arr153 A B))
   (app   : (Γ : _) (A B : _) → Tm153 Γ (arr153 A B) → Tm153 Γ A → Tm153 Γ B)
 → Tm153 Γ A

var153 : ∀{Γ A} → Var153 Γ A → Tm153 Γ A;var153
 = λ x Tm153 var153 lam app → var153 _ _ x

lam153 : ∀{Γ A B} → Tm153 (snoc153 Γ A) B → Tm153 Γ (arr153 A B);lam153
 = λ t Tm153 var153 lam153 app → lam153 _ _ _ (t Tm153 var153 lam153 app)

app153 : ∀{Γ A B} → Tm153 Γ (arr153 A B) → Tm153 Γ A → Tm153 Γ B;app153
 = λ t u Tm153 var153 lam153 app153 →
     app153 _ _ _ (t Tm153 var153 lam153 app153) (u Tm153 var153 lam153 app153)

v0153 : ∀{Γ A} → Tm153 (snoc153 Γ A) A;v0153
 = var153 vz153

v1153 : ∀{Γ A B} → Tm153 (snoc153 (snoc153 Γ A) B) A;v1153
 = var153 (vs153 vz153)

v2153 : ∀{Γ A B C} → Tm153 (snoc153 (snoc153 (snoc153 Γ A) B) C) A;v2153
 = var153 (vs153 (vs153 vz153))

v3153 : ∀{Γ A B C D} → Tm153 (snoc153 (snoc153 (snoc153 (snoc153 Γ A) B) C) D) A;v3153
 = var153 (vs153 (vs153 (vs153 vz153)))

v4153 : ∀{Γ A B C D E} → Tm153 (snoc153 (snoc153 (snoc153 (snoc153 (snoc153 Γ A) B) C) D) E) A;v4153
 = var153 (vs153 (vs153 (vs153 (vs153 vz153))))

test153 : ∀{Γ A} → Tm153 Γ (arr153 (arr153 A A) (arr153 A A));test153
  = lam153 (lam153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 v0153)))))))
{-# OPTIONS --type-in-type #-}

Ty154 : Set; Ty154
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι154   : Ty154; ι154 = λ _ ι154 _ → ι154
arr154 : Ty154 → Ty154 → Ty154; arr154 = λ A B Ty154 ι154 arr154 → arr154 (A Ty154 ι154 arr154) (B Ty154 ι154 arr154)

Con154 : Set;Con154
 = (Con154 : Set)
   (nil  : Con154)
   (snoc : Con154 → Ty154 → Con154)
 → Con154

nil154 : Con154;nil154
 = λ Con154 nil154 snoc → nil154

snoc154 : Con154 → Ty154 → Con154;snoc154
 = λ Γ A Con154 nil154 snoc154 → snoc154 (Γ Con154 nil154 snoc154) A

Var154 : Con154 → Ty154 → Set;Var154
 = λ Γ A →
   (Var154 : Con154 → Ty154 → Set)
   (vz  : (Γ : _)(A : _) → Var154 (snoc154 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var154 Γ A → Var154 (snoc154 Γ B) A)
 → Var154 Γ A

vz154 : ∀{Γ A} → Var154 (snoc154 Γ A) A;vz154
 = λ Var154 vz154 vs → vz154 _ _

vs154 : ∀{Γ B A} → Var154 Γ A → Var154 (snoc154 Γ B) A;vs154
 = λ x Var154 vz154 vs154 → vs154 _ _ _ (x Var154 vz154 vs154)

Tm154 : Con154 → Ty154 → Set;Tm154
 = λ Γ A →
   (Tm154    : Con154 → Ty154 → Set)
   (var   : (Γ : _) (A : _) → Var154 Γ A → Tm154 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm154 (snoc154 Γ A) B → Tm154 Γ (arr154 A B))
   (app   : (Γ : _) (A B : _) → Tm154 Γ (arr154 A B) → Tm154 Γ A → Tm154 Γ B)
 → Tm154 Γ A

var154 : ∀{Γ A} → Var154 Γ A → Tm154 Γ A;var154
 = λ x Tm154 var154 lam app → var154 _ _ x

lam154 : ∀{Γ A B} → Tm154 (snoc154 Γ A) B → Tm154 Γ (arr154 A B);lam154
 = λ t Tm154 var154 lam154 app → lam154 _ _ _ (t Tm154 var154 lam154 app)

app154 : ∀{Γ A B} → Tm154 Γ (arr154 A B) → Tm154 Γ A → Tm154 Γ B;app154
 = λ t u Tm154 var154 lam154 app154 →
     app154 _ _ _ (t Tm154 var154 lam154 app154) (u Tm154 var154 lam154 app154)

v0154 : ∀{Γ A} → Tm154 (snoc154 Γ A) A;v0154
 = var154 vz154

v1154 : ∀{Γ A B} → Tm154 (snoc154 (snoc154 Γ A) B) A;v1154
 = var154 (vs154 vz154)

v2154 : ∀{Γ A B C} → Tm154 (snoc154 (snoc154 (snoc154 Γ A) B) C) A;v2154
 = var154 (vs154 (vs154 vz154))

v3154 : ∀{Γ A B C D} → Tm154 (snoc154 (snoc154 (snoc154 (snoc154 Γ A) B) C) D) A;v3154
 = var154 (vs154 (vs154 (vs154 vz154)))

v4154 : ∀{Γ A B C D E} → Tm154 (snoc154 (snoc154 (snoc154 (snoc154 (snoc154 Γ A) B) C) D) E) A;v4154
 = var154 (vs154 (vs154 (vs154 (vs154 vz154))))

test154 : ∀{Γ A} → Tm154 Γ (arr154 (arr154 A A) (arr154 A A));test154
  = lam154 (lam154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 v0154)))))))
{-# OPTIONS --type-in-type #-}

Ty155 : Set; Ty155
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι155   : Ty155; ι155 = λ _ ι155 _ → ι155
arr155 : Ty155 → Ty155 → Ty155; arr155 = λ A B Ty155 ι155 arr155 → arr155 (A Ty155 ι155 arr155) (B Ty155 ι155 arr155)

Con155 : Set;Con155
 = (Con155 : Set)
   (nil  : Con155)
   (snoc : Con155 → Ty155 → Con155)
 → Con155

nil155 : Con155;nil155
 = λ Con155 nil155 snoc → nil155

snoc155 : Con155 → Ty155 → Con155;snoc155
 = λ Γ A Con155 nil155 snoc155 → snoc155 (Γ Con155 nil155 snoc155) A

Var155 : Con155 → Ty155 → Set;Var155
 = λ Γ A →
   (Var155 : Con155 → Ty155 → Set)
   (vz  : (Γ : _)(A : _) → Var155 (snoc155 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var155 Γ A → Var155 (snoc155 Γ B) A)
 → Var155 Γ A

vz155 : ∀{Γ A} → Var155 (snoc155 Γ A) A;vz155
 = λ Var155 vz155 vs → vz155 _ _

vs155 : ∀{Γ B A} → Var155 Γ A → Var155 (snoc155 Γ B) A;vs155
 = λ x Var155 vz155 vs155 → vs155 _ _ _ (x Var155 vz155 vs155)

Tm155 : Con155 → Ty155 → Set;Tm155
 = λ Γ A →
   (Tm155    : Con155 → Ty155 → Set)
   (var   : (Γ : _) (A : _) → Var155 Γ A → Tm155 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm155 (snoc155 Γ A) B → Tm155 Γ (arr155 A B))
   (app   : (Γ : _) (A B : _) → Tm155 Γ (arr155 A B) → Tm155 Γ A → Tm155 Γ B)
 → Tm155 Γ A

var155 : ∀{Γ A} → Var155 Γ A → Tm155 Γ A;var155
 = λ x Tm155 var155 lam app → var155 _ _ x

lam155 : ∀{Γ A B} → Tm155 (snoc155 Γ A) B → Tm155 Γ (arr155 A B);lam155
 = λ t Tm155 var155 lam155 app → lam155 _ _ _ (t Tm155 var155 lam155 app)

app155 : ∀{Γ A B} → Tm155 Γ (arr155 A B) → Tm155 Γ A → Tm155 Γ B;app155
 = λ t u Tm155 var155 lam155 app155 →
     app155 _ _ _ (t Tm155 var155 lam155 app155) (u Tm155 var155 lam155 app155)

v0155 : ∀{Γ A} → Tm155 (snoc155 Γ A) A;v0155
 = var155 vz155

v1155 : ∀{Γ A B} → Tm155 (snoc155 (snoc155 Γ A) B) A;v1155
 = var155 (vs155 vz155)

v2155 : ∀{Γ A B C} → Tm155 (snoc155 (snoc155 (snoc155 Γ A) B) C) A;v2155
 = var155 (vs155 (vs155 vz155))

v3155 : ∀{Γ A B C D} → Tm155 (snoc155 (snoc155 (snoc155 (snoc155 Γ A) B) C) D) A;v3155
 = var155 (vs155 (vs155 (vs155 vz155)))

v4155 : ∀{Γ A B C D E} → Tm155 (snoc155 (snoc155 (snoc155 (snoc155 (snoc155 Γ A) B) C) D) E) A;v4155
 = var155 (vs155 (vs155 (vs155 (vs155 vz155))))

test155 : ∀{Γ A} → Tm155 Γ (arr155 (arr155 A A) (arr155 A A));test155
  = lam155 (lam155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 v0155)))))))
{-# OPTIONS --type-in-type #-}

Ty156 : Set; Ty156
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι156   : Ty156; ι156 = λ _ ι156 _ → ι156
arr156 : Ty156 → Ty156 → Ty156; arr156 = λ A B Ty156 ι156 arr156 → arr156 (A Ty156 ι156 arr156) (B Ty156 ι156 arr156)

Con156 : Set;Con156
 = (Con156 : Set)
   (nil  : Con156)
   (snoc : Con156 → Ty156 → Con156)
 → Con156

nil156 : Con156;nil156
 = λ Con156 nil156 snoc → nil156

snoc156 : Con156 → Ty156 → Con156;snoc156
 = λ Γ A Con156 nil156 snoc156 → snoc156 (Γ Con156 nil156 snoc156) A

Var156 : Con156 → Ty156 → Set;Var156
 = λ Γ A →
   (Var156 : Con156 → Ty156 → Set)
   (vz  : (Γ : _)(A : _) → Var156 (snoc156 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var156 Γ A → Var156 (snoc156 Γ B) A)
 → Var156 Γ A

vz156 : ∀{Γ A} → Var156 (snoc156 Γ A) A;vz156
 = λ Var156 vz156 vs → vz156 _ _

vs156 : ∀{Γ B A} → Var156 Γ A → Var156 (snoc156 Γ B) A;vs156
 = λ x Var156 vz156 vs156 → vs156 _ _ _ (x Var156 vz156 vs156)

Tm156 : Con156 → Ty156 → Set;Tm156
 = λ Γ A →
   (Tm156    : Con156 → Ty156 → Set)
   (var   : (Γ : _) (A : _) → Var156 Γ A → Tm156 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm156 (snoc156 Γ A) B → Tm156 Γ (arr156 A B))
   (app   : (Γ : _) (A B : _) → Tm156 Γ (arr156 A B) → Tm156 Γ A → Tm156 Γ B)
 → Tm156 Γ A

var156 : ∀{Γ A} → Var156 Γ A → Tm156 Γ A;var156
 = λ x Tm156 var156 lam app → var156 _ _ x

lam156 : ∀{Γ A B} → Tm156 (snoc156 Γ A) B → Tm156 Γ (arr156 A B);lam156
 = λ t Tm156 var156 lam156 app → lam156 _ _ _ (t Tm156 var156 lam156 app)

app156 : ∀{Γ A B} → Tm156 Γ (arr156 A B) → Tm156 Γ A → Tm156 Γ B;app156
 = λ t u Tm156 var156 lam156 app156 →
     app156 _ _ _ (t Tm156 var156 lam156 app156) (u Tm156 var156 lam156 app156)

v0156 : ∀{Γ A} → Tm156 (snoc156 Γ A) A;v0156
 = var156 vz156

v1156 : ∀{Γ A B} → Tm156 (snoc156 (snoc156 Γ A) B) A;v1156
 = var156 (vs156 vz156)

v2156 : ∀{Γ A B C} → Tm156 (snoc156 (snoc156 (snoc156 Γ A) B) C) A;v2156
 = var156 (vs156 (vs156 vz156))

v3156 : ∀{Γ A B C D} → Tm156 (snoc156 (snoc156 (snoc156 (snoc156 Γ A) B) C) D) A;v3156
 = var156 (vs156 (vs156 (vs156 vz156)))

v4156 : ∀{Γ A B C D E} → Tm156 (snoc156 (snoc156 (snoc156 (snoc156 (snoc156 Γ A) B) C) D) E) A;v4156
 = var156 (vs156 (vs156 (vs156 (vs156 vz156))))

test156 : ∀{Γ A} → Tm156 Γ (arr156 (arr156 A A) (arr156 A A));test156
  = lam156 (lam156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 v0156)))))))
{-# OPTIONS --type-in-type #-}

Ty157 : Set; Ty157
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι157   : Ty157; ι157 = λ _ ι157 _ → ι157
arr157 : Ty157 → Ty157 → Ty157; arr157 = λ A B Ty157 ι157 arr157 → arr157 (A Ty157 ι157 arr157) (B Ty157 ι157 arr157)

Con157 : Set;Con157
 = (Con157 : Set)
   (nil  : Con157)
   (snoc : Con157 → Ty157 → Con157)
 → Con157

nil157 : Con157;nil157
 = λ Con157 nil157 snoc → nil157

snoc157 : Con157 → Ty157 → Con157;snoc157
 = λ Γ A Con157 nil157 snoc157 → snoc157 (Γ Con157 nil157 snoc157) A

Var157 : Con157 → Ty157 → Set;Var157
 = λ Γ A →
   (Var157 : Con157 → Ty157 → Set)
   (vz  : (Γ : _)(A : _) → Var157 (snoc157 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var157 Γ A → Var157 (snoc157 Γ B) A)
 → Var157 Γ A

vz157 : ∀{Γ A} → Var157 (snoc157 Γ A) A;vz157
 = λ Var157 vz157 vs → vz157 _ _

vs157 : ∀{Γ B A} → Var157 Γ A → Var157 (snoc157 Γ B) A;vs157
 = λ x Var157 vz157 vs157 → vs157 _ _ _ (x Var157 vz157 vs157)

Tm157 : Con157 → Ty157 → Set;Tm157
 = λ Γ A →
   (Tm157    : Con157 → Ty157 → Set)
   (var   : (Γ : _) (A : _) → Var157 Γ A → Tm157 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm157 (snoc157 Γ A) B → Tm157 Γ (arr157 A B))
   (app   : (Γ : _) (A B : _) → Tm157 Γ (arr157 A B) → Tm157 Γ A → Tm157 Γ B)
 → Tm157 Γ A

var157 : ∀{Γ A} → Var157 Γ A → Tm157 Γ A;var157
 = λ x Tm157 var157 lam app → var157 _ _ x

lam157 : ∀{Γ A B} → Tm157 (snoc157 Γ A) B → Tm157 Γ (arr157 A B);lam157
 = λ t Tm157 var157 lam157 app → lam157 _ _ _ (t Tm157 var157 lam157 app)

app157 : ∀{Γ A B} → Tm157 Γ (arr157 A B) → Tm157 Γ A → Tm157 Γ B;app157
 = λ t u Tm157 var157 lam157 app157 →
     app157 _ _ _ (t Tm157 var157 lam157 app157) (u Tm157 var157 lam157 app157)

v0157 : ∀{Γ A} → Tm157 (snoc157 Γ A) A;v0157
 = var157 vz157

v1157 : ∀{Γ A B} → Tm157 (snoc157 (snoc157 Γ A) B) A;v1157
 = var157 (vs157 vz157)

v2157 : ∀{Γ A B C} → Tm157 (snoc157 (snoc157 (snoc157 Γ A) B) C) A;v2157
 = var157 (vs157 (vs157 vz157))

v3157 : ∀{Γ A B C D} → Tm157 (snoc157 (snoc157 (snoc157 (snoc157 Γ A) B) C) D) A;v3157
 = var157 (vs157 (vs157 (vs157 vz157)))

v4157 : ∀{Γ A B C D E} → Tm157 (snoc157 (snoc157 (snoc157 (snoc157 (snoc157 Γ A) B) C) D) E) A;v4157
 = var157 (vs157 (vs157 (vs157 (vs157 vz157))))

test157 : ∀{Γ A} → Tm157 Γ (arr157 (arr157 A A) (arr157 A A));test157
  = lam157 (lam157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 v0157)))))))
{-# OPTIONS --type-in-type #-}

Ty158 : Set; Ty158
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι158   : Ty158; ι158 = λ _ ι158 _ → ι158
arr158 : Ty158 → Ty158 → Ty158; arr158 = λ A B Ty158 ι158 arr158 → arr158 (A Ty158 ι158 arr158) (B Ty158 ι158 arr158)

Con158 : Set;Con158
 = (Con158 : Set)
   (nil  : Con158)
   (snoc : Con158 → Ty158 → Con158)
 → Con158

nil158 : Con158;nil158
 = λ Con158 nil158 snoc → nil158

snoc158 : Con158 → Ty158 → Con158;snoc158
 = λ Γ A Con158 nil158 snoc158 → snoc158 (Γ Con158 nil158 snoc158) A

Var158 : Con158 → Ty158 → Set;Var158
 = λ Γ A →
   (Var158 : Con158 → Ty158 → Set)
   (vz  : (Γ : _)(A : _) → Var158 (snoc158 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var158 Γ A → Var158 (snoc158 Γ B) A)
 → Var158 Γ A

vz158 : ∀{Γ A} → Var158 (snoc158 Γ A) A;vz158
 = λ Var158 vz158 vs → vz158 _ _

vs158 : ∀{Γ B A} → Var158 Γ A → Var158 (snoc158 Γ B) A;vs158
 = λ x Var158 vz158 vs158 → vs158 _ _ _ (x Var158 vz158 vs158)

Tm158 : Con158 → Ty158 → Set;Tm158
 = λ Γ A →
   (Tm158    : Con158 → Ty158 → Set)
   (var   : (Γ : _) (A : _) → Var158 Γ A → Tm158 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm158 (snoc158 Γ A) B → Tm158 Γ (arr158 A B))
   (app   : (Γ : _) (A B : _) → Tm158 Γ (arr158 A B) → Tm158 Γ A → Tm158 Γ B)
 → Tm158 Γ A

var158 : ∀{Γ A} → Var158 Γ A → Tm158 Γ A;var158
 = λ x Tm158 var158 lam app → var158 _ _ x

lam158 : ∀{Γ A B} → Tm158 (snoc158 Γ A) B → Tm158 Γ (arr158 A B);lam158
 = λ t Tm158 var158 lam158 app → lam158 _ _ _ (t Tm158 var158 lam158 app)

app158 : ∀{Γ A B} → Tm158 Γ (arr158 A B) → Tm158 Γ A → Tm158 Γ B;app158
 = λ t u Tm158 var158 lam158 app158 →
     app158 _ _ _ (t Tm158 var158 lam158 app158) (u Tm158 var158 lam158 app158)

v0158 : ∀{Γ A} → Tm158 (snoc158 Γ A) A;v0158
 = var158 vz158

v1158 : ∀{Γ A B} → Tm158 (snoc158 (snoc158 Γ A) B) A;v1158
 = var158 (vs158 vz158)

v2158 : ∀{Γ A B C} → Tm158 (snoc158 (snoc158 (snoc158 Γ A) B) C) A;v2158
 = var158 (vs158 (vs158 vz158))

v3158 : ∀{Γ A B C D} → Tm158 (snoc158 (snoc158 (snoc158 (snoc158 Γ A) B) C) D) A;v3158
 = var158 (vs158 (vs158 (vs158 vz158)))

v4158 : ∀{Γ A B C D E} → Tm158 (snoc158 (snoc158 (snoc158 (snoc158 (snoc158 Γ A) B) C) D) E) A;v4158
 = var158 (vs158 (vs158 (vs158 (vs158 vz158))))

test158 : ∀{Γ A} → Tm158 Γ (arr158 (arr158 A A) (arr158 A A));test158
  = lam158 (lam158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 v0158)))))))
{-# OPTIONS --type-in-type #-}

Ty159 : Set; Ty159
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι159   : Ty159; ι159 = λ _ ι159 _ → ι159
arr159 : Ty159 → Ty159 → Ty159; arr159 = λ A B Ty159 ι159 arr159 → arr159 (A Ty159 ι159 arr159) (B Ty159 ι159 arr159)

Con159 : Set;Con159
 = (Con159 : Set)
   (nil  : Con159)
   (snoc : Con159 → Ty159 → Con159)
 → Con159

nil159 : Con159;nil159
 = λ Con159 nil159 snoc → nil159

snoc159 : Con159 → Ty159 → Con159;snoc159
 = λ Γ A Con159 nil159 snoc159 → snoc159 (Γ Con159 nil159 snoc159) A

Var159 : Con159 → Ty159 → Set;Var159
 = λ Γ A →
   (Var159 : Con159 → Ty159 → Set)
   (vz  : (Γ : _)(A : _) → Var159 (snoc159 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var159 Γ A → Var159 (snoc159 Γ B) A)
 → Var159 Γ A

vz159 : ∀{Γ A} → Var159 (snoc159 Γ A) A;vz159
 = λ Var159 vz159 vs → vz159 _ _

vs159 : ∀{Γ B A} → Var159 Γ A → Var159 (snoc159 Γ B) A;vs159
 = λ x Var159 vz159 vs159 → vs159 _ _ _ (x Var159 vz159 vs159)

Tm159 : Con159 → Ty159 → Set;Tm159
 = λ Γ A →
   (Tm159    : Con159 → Ty159 → Set)
   (var   : (Γ : _) (A : _) → Var159 Γ A → Tm159 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm159 (snoc159 Γ A) B → Tm159 Γ (arr159 A B))
   (app   : (Γ : _) (A B : _) → Tm159 Γ (arr159 A B) → Tm159 Γ A → Tm159 Γ B)
 → Tm159 Γ A

var159 : ∀{Γ A} → Var159 Γ A → Tm159 Γ A;var159
 = λ x Tm159 var159 lam app → var159 _ _ x

lam159 : ∀{Γ A B} → Tm159 (snoc159 Γ A) B → Tm159 Γ (arr159 A B);lam159
 = λ t Tm159 var159 lam159 app → lam159 _ _ _ (t Tm159 var159 lam159 app)

app159 : ∀{Γ A B} → Tm159 Γ (arr159 A B) → Tm159 Γ A → Tm159 Γ B;app159
 = λ t u Tm159 var159 lam159 app159 →
     app159 _ _ _ (t Tm159 var159 lam159 app159) (u Tm159 var159 lam159 app159)

v0159 : ∀{Γ A} → Tm159 (snoc159 Γ A) A;v0159
 = var159 vz159

v1159 : ∀{Γ A B} → Tm159 (snoc159 (snoc159 Γ A) B) A;v1159
 = var159 (vs159 vz159)

v2159 : ∀{Γ A B C} → Tm159 (snoc159 (snoc159 (snoc159 Γ A) B) C) A;v2159
 = var159 (vs159 (vs159 vz159))

v3159 : ∀{Γ A B C D} → Tm159 (snoc159 (snoc159 (snoc159 (snoc159 Γ A) B) C) D) A;v3159
 = var159 (vs159 (vs159 (vs159 vz159)))

v4159 : ∀{Γ A B C D E} → Tm159 (snoc159 (snoc159 (snoc159 (snoc159 (snoc159 Γ A) B) C) D) E) A;v4159
 = var159 (vs159 (vs159 (vs159 (vs159 vz159))))

test159 : ∀{Γ A} → Tm159 Γ (arr159 (arr159 A A) (arr159 A A));test159
  = lam159 (lam159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 v0159)))))))
{-# OPTIONS --type-in-type #-}

Ty160 : Set; Ty160
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι160   : Ty160; ι160 = λ _ ι160 _ → ι160
arr160 : Ty160 → Ty160 → Ty160; arr160 = λ A B Ty160 ι160 arr160 → arr160 (A Ty160 ι160 arr160) (B Ty160 ι160 arr160)

Con160 : Set;Con160
 = (Con160 : Set)
   (nil  : Con160)
   (snoc : Con160 → Ty160 → Con160)
 → Con160

nil160 : Con160;nil160
 = λ Con160 nil160 snoc → nil160

snoc160 : Con160 → Ty160 → Con160;snoc160
 = λ Γ A Con160 nil160 snoc160 → snoc160 (Γ Con160 nil160 snoc160) A

Var160 : Con160 → Ty160 → Set;Var160
 = λ Γ A →
   (Var160 : Con160 → Ty160 → Set)
   (vz  : (Γ : _)(A : _) → Var160 (snoc160 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var160 Γ A → Var160 (snoc160 Γ B) A)
 → Var160 Γ A

vz160 : ∀{Γ A} → Var160 (snoc160 Γ A) A;vz160
 = λ Var160 vz160 vs → vz160 _ _

vs160 : ∀{Γ B A} → Var160 Γ A → Var160 (snoc160 Γ B) A;vs160
 = λ x Var160 vz160 vs160 → vs160 _ _ _ (x Var160 vz160 vs160)

Tm160 : Con160 → Ty160 → Set;Tm160
 = λ Γ A →
   (Tm160    : Con160 → Ty160 → Set)
   (var   : (Γ : _) (A : _) → Var160 Γ A → Tm160 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm160 (snoc160 Γ A) B → Tm160 Γ (arr160 A B))
   (app   : (Γ : _) (A B : _) → Tm160 Γ (arr160 A B) → Tm160 Γ A → Tm160 Γ B)
 → Tm160 Γ A

var160 : ∀{Γ A} → Var160 Γ A → Tm160 Γ A;var160
 = λ x Tm160 var160 lam app → var160 _ _ x

lam160 : ∀{Γ A B} → Tm160 (snoc160 Γ A) B → Tm160 Γ (arr160 A B);lam160
 = λ t Tm160 var160 lam160 app → lam160 _ _ _ (t Tm160 var160 lam160 app)

app160 : ∀{Γ A B} → Tm160 Γ (arr160 A B) → Tm160 Γ A → Tm160 Γ B;app160
 = λ t u Tm160 var160 lam160 app160 →
     app160 _ _ _ (t Tm160 var160 lam160 app160) (u Tm160 var160 lam160 app160)

v0160 : ∀{Γ A} → Tm160 (snoc160 Γ A) A;v0160
 = var160 vz160

v1160 : ∀{Γ A B} → Tm160 (snoc160 (snoc160 Γ A) B) A;v1160
 = var160 (vs160 vz160)

v2160 : ∀{Γ A B C} → Tm160 (snoc160 (snoc160 (snoc160 Γ A) B) C) A;v2160
 = var160 (vs160 (vs160 vz160))

v3160 : ∀{Γ A B C D} → Tm160 (snoc160 (snoc160 (snoc160 (snoc160 Γ A) B) C) D) A;v3160
 = var160 (vs160 (vs160 (vs160 vz160)))

v4160 : ∀{Γ A B C D E} → Tm160 (snoc160 (snoc160 (snoc160 (snoc160 (snoc160 Γ A) B) C) D) E) A;v4160
 = var160 (vs160 (vs160 (vs160 (vs160 vz160))))

test160 : ∀{Γ A} → Tm160 Γ (arr160 (arr160 A A) (arr160 A A));test160
  = lam160 (lam160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 v0160)))))))
{-# OPTIONS --type-in-type #-}

Ty161 : Set; Ty161
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι161   : Ty161; ι161 = λ _ ι161 _ → ι161
arr161 : Ty161 → Ty161 → Ty161; arr161 = λ A B Ty161 ι161 arr161 → arr161 (A Ty161 ι161 arr161) (B Ty161 ι161 arr161)

Con161 : Set;Con161
 = (Con161 : Set)
   (nil  : Con161)
   (snoc : Con161 → Ty161 → Con161)
 → Con161

nil161 : Con161;nil161
 = λ Con161 nil161 snoc → nil161

snoc161 : Con161 → Ty161 → Con161;snoc161
 = λ Γ A Con161 nil161 snoc161 → snoc161 (Γ Con161 nil161 snoc161) A

Var161 : Con161 → Ty161 → Set;Var161
 = λ Γ A →
   (Var161 : Con161 → Ty161 → Set)
   (vz  : (Γ : _)(A : _) → Var161 (snoc161 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var161 Γ A → Var161 (snoc161 Γ B) A)
 → Var161 Γ A

vz161 : ∀{Γ A} → Var161 (snoc161 Γ A) A;vz161
 = λ Var161 vz161 vs → vz161 _ _

vs161 : ∀{Γ B A} → Var161 Γ A → Var161 (snoc161 Γ B) A;vs161
 = λ x Var161 vz161 vs161 → vs161 _ _ _ (x Var161 vz161 vs161)

Tm161 : Con161 → Ty161 → Set;Tm161
 = λ Γ A →
   (Tm161    : Con161 → Ty161 → Set)
   (var   : (Γ : _) (A : _) → Var161 Γ A → Tm161 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm161 (snoc161 Γ A) B → Tm161 Γ (arr161 A B))
   (app   : (Γ : _) (A B : _) → Tm161 Γ (arr161 A B) → Tm161 Γ A → Tm161 Γ B)
 → Tm161 Γ A

var161 : ∀{Γ A} → Var161 Γ A → Tm161 Γ A;var161
 = λ x Tm161 var161 lam app → var161 _ _ x

lam161 : ∀{Γ A B} → Tm161 (snoc161 Γ A) B → Tm161 Γ (arr161 A B);lam161
 = λ t Tm161 var161 lam161 app → lam161 _ _ _ (t Tm161 var161 lam161 app)

app161 : ∀{Γ A B} → Tm161 Γ (arr161 A B) → Tm161 Γ A → Tm161 Γ B;app161
 = λ t u Tm161 var161 lam161 app161 →
     app161 _ _ _ (t Tm161 var161 lam161 app161) (u Tm161 var161 lam161 app161)

v0161 : ∀{Γ A} → Tm161 (snoc161 Γ A) A;v0161
 = var161 vz161

v1161 : ∀{Γ A B} → Tm161 (snoc161 (snoc161 Γ A) B) A;v1161
 = var161 (vs161 vz161)

v2161 : ∀{Γ A B C} → Tm161 (snoc161 (snoc161 (snoc161 Γ A) B) C) A;v2161
 = var161 (vs161 (vs161 vz161))

v3161 : ∀{Γ A B C D} → Tm161 (snoc161 (snoc161 (snoc161 (snoc161 Γ A) B) C) D) A;v3161
 = var161 (vs161 (vs161 (vs161 vz161)))

v4161 : ∀{Γ A B C D E} → Tm161 (snoc161 (snoc161 (snoc161 (snoc161 (snoc161 Γ A) B) C) D) E) A;v4161
 = var161 (vs161 (vs161 (vs161 (vs161 vz161))))

test161 : ∀{Γ A} → Tm161 Γ (arr161 (arr161 A A) (arr161 A A));test161
  = lam161 (lam161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 v0161)))))))
{-# OPTIONS --type-in-type #-}

Ty162 : Set; Ty162
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι162   : Ty162; ι162 = λ _ ι162 _ → ι162
arr162 : Ty162 → Ty162 → Ty162; arr162 = λ A B Ty162 ι162 arr162 → arr162 (A Ty162 ι162 arr162) (B Ty162 ι162 arr162)

Con162 : Set;Con162
 = (Con162 : Set)
   (nil  : Con162)
   (snoc : Con162 → Ty162 → Con162)
 → Con162

nil162 : Con162;nil162
 = λ Con162 nil162 snoc → nil162

snoc162 : Con162 → Ty162 → Con162;snoc162
 = λ Γ A Con162 nil162 snoc162 → snoc162 (Γ Con162 nil162 snoc162) A

Var162 : Con162 → Ty162 → Set;Var162
 = λ Γ A →
   (Var162 : Con162 → Ty162 → Set)
   (vz  : (Γ : _)(A : _) → Var162 (snoc162 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var162 Γ A → Var162 (snoc162 Γ B) A)
 → Var162 Γ A

vz162 : ∀{Γ A} → Var162 (snoc162 Γ A) A;vz162
 = λ Var162 vz162 vs → vz162 _ _

vs162 : ∀{Γ B A} → Var162 Γ A → Var162 (snoc162 Γ B) A;vs162
 = λ x Var162 vz162 vs162 → vs162 _ _ _ (x Var162 vz162 vs162)

Tm162 : Con162 → Ty162 → Set;Tm162
 = λ Γ A →
   (Tm162    : Con162 → Ty162 → Set)
   (var   : (Γ : _) (A : _) → Var162 Γ A → Tm162 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm162 (snoc162 Γ A) B → Tm162 Γ (arr162 A B))
   (app   : (Γ : _) (A B : _) → Tm162 Γ (arr162 A B) → Tm162 Γ A → Tm162 Γ B)
 → Tm162 Γ A

var162 : ∀{Γ A} → Var162 Γ A → Tm162 Γ A;var162
 = λ x Tm162 var162 lam app → var162 _ _ x

lam162 : ∀{Γ A B} → Tm162 (snoc162 Γ A) B → Tm162 Γ (arr162 A B);lam162
 = λ t Tm162 var162 lam162 app → lam162 _ _ _ (t Tm162 var162 lam162 app)

app162 : ∀{Γ A B} → Tm162 Γ (arr162 A B) → Tm162 Γ A → Tm162 Γ B;app162
 = λ t u Tm162 var162 lam162 app162 →
     app162 _ _ _ (t Tm162 var162 lam162 app162) (u Tm162 var162 lam162 app162)

v0162 : ∀{Γ A} → Tm162 (snoc162 Γ A) A;v0162
 = var162 vz162

v1162 : ∀{Γ A B} → Tm162 (snoc162 (snoc162 Γ A) B) A;v1162
 = var162 (vs162 vz162)

v2162 : ∀{Γ A B C} → Tm162 (snoc162 (snoc162 (snoc162 Γ A) B) C) A;v2162
 = var162 (vs162 (vs162 vz162))

v3162 : ∀{Γ A B C D} → Tm162 (snoc162 (snoc162 (snoc162 (snoc162 Γ A) B) C) D) A;v3162
 = var162 (vs162 (vs162 (vs162 vz162)))

v4162 : ∀{Γ A B C D E} → Tm162 (snoc162 (snoc162 (snoc162 (snoc162 (snoc162 Γ A) B) C) D) E) A;v4162
 = var162 (vs162 (vs162 (vs162 (vs162 vz162))))

test162 : ∀{Γ A} → Tm162 Γ (arr162 (arr162 A A) (arr162 A A));test162
  = lam162 (lam162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 v0162)))))))
{-# OPTIONS --type-in-type #-}

Ty163 : Set; Ty163
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι163   : Ty163; ι163 = λ _ ι163 _ → ι163
arr163 : Ty163 → Ty163 → Ty163; arr163 = λ A B Ty163 ι163 arr163 → arr163 (A Ty163 ι163 arr163) (B Ty163 ι163 arr163)

Con163 : Set;Con163
 = (Con163 : Set)
   (nil  : Con163)
   (snoc : Con163 → Ty163 → Con163)
 → Con163

nil163 : Con163;nil163
 = λ Con163 nil163 snoc → nil163

snoc163 : Con163 → Ty163 → Con163;snoc163
 = λ Γ A Con163 nil163 snoc163 → snoc163 (Γ Con163 nil163 snoc163) A

Var163 : Con163 → Ty163 → Set;Var163
 = λ Γ A →
   (Var163 : Con163 → Ty163 → Set)
   (vz  : (Γ : _)(A : _) → Var163 (snoc163 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var163 Γ A → Var163 (snoc163 Γ B) A)
 → Var163 Γ A

vz163 : ∀{Γ A} → Var163 (snoc163 Γ A) A;vz163
 = λ Var163 vz163 vs → vz163 _ _

vs163 : ∀{Γ B A} → Var163 Γ A → Var163 (snoc163 Γ B) A;vs163
 = λ x Var163 vz163 vs163 → vs163 _ _ _ (x Var163 vz163 vs163)

Tm163 : Con163 → Ty163 → Set;Tm163
 = λ Γ A →
   (Tm163    : Con163 → Ty163 → Set)
   (var   : (Γ : _) (A : _) → Var163 Γ A → Tm163 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm163 (snoc163 Γ A) B → Tm163 Γ (arr163 A B))
   (app   : (Γ : _) (A B : _) → Tm163 Γ (arr163 A B) → Tm163 Γ A → Tm163 Γ B)
 → Tm163 Γ A

var163 : ∀{Γ A} → Var163 Γ A → Tm163 Γ A;var163
 = λ x Tm163 var163 lam app → var163 _ _ x

lam163 : ∀{Γ A B} → Tm163 (snoc163 Γ A) B → Tm163 Γ (arr163 A B);lam163
 = λ t Tm163 var163 lam163 app → lam163 _ _ _ (t Tm163 var163 lam163 app)

app163 : ∀{Γ A B} → Tm163 Γ (arr163 A B) → Tm163 Γ A → Tm163 Γ B;app163
 = λ t u Tm163 var163 lam163 app163 →
     app163 _ _ _ (t Tm163 var163 lam163 app163) (u Tm163 var163 lam163 app163)

v0163 : ∀{Γ A} → Tm163 (snoc163 Γ A) A;v0163
 = var163 vz163

v1163 : ∀{Γ A B} → Tm163 (snoc163 (snoc163 Γ A) B) A;v1163
 = var163 (vs163 vz163)

v2163 : ∀{Γ A B C} → Tm163 (snoc163 (snoc163 (snoc163 Γ A) B) C) A;v2163
 = var163 (vs163 (vs163 vz163))

v3163 : ∀{Γ A B C D} → Tm163 (snoc163 (snoc163 (snoc163 (snoc163 Γ A) B) C) D) A;v3163
 = var163 (vs163 (vs163 (vs163 vz163)))

v4163 : ∀{Γ A B C D E} → Tm163 (snoc163 (snoc163 (snoc163 (snoc163 (snoc163 Γ A) B) C) D) E) A;v4163
 = var163 (vs163 (vs163 (vs163 (vs163 vz163))))

test163 : ∀{Γ A} → Tm163 Γ (arr163 (arr163 A A) (arr163 A A));test163
  = lam163 (lam163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 v0163)))))))
{-# OPTIONS --type-in-type #-}

Ty164 : Set; Ty164
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι164   : Ty164; ι164 = λ _ ι164 _ → ι164
arr164 : Ty164 → Ty164 → Ty164; arr164 = λ A B Ty164 ι164 arr164 → arr164 (A Ty164 ι164 arr164) (B Ty164 ι164 arr164)

Con164 : Set;Con164
 = (Con164 : Set)
   (nil  : Con164)
   (snoc : Con164 → Ty164 → Con164)
 → Con164

nil164 : Con164;nil164
 = λ Con164 nil164 snoc → nil164

snoc164 : Con164 → Ty164 → Con164;snoc164
 = λ Γ A Con164 nil164 snoc164 → snoc164 (Γ Con164 nil164 snoc164) A

Var164 : Con164 → Ty164 → Set;Var164
 = λ Γ A →
   (Var164 : Con164 → Ty164 → Set)
   (vz  : (Γ : _)(A : _) → Var164 (snoc164 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var164 Γ A → Var164 (snoc164 Γ B) A)
 → Var164 Γ A

vz164 : ∀{Γ A} → Var164 (snoc164 Γ A) A;vz164
 = λ Var164 vz164 vs → vz164 _ _

vs164 : ∀{Γ B A} → Var164 Γ A → Var164 (snoc164 Γ B) A;vs164
 = λ x Var164 vz164 vs164 → vs164 _ _ _ (x Var164 vz164 vs164)

Tm164 : Con164 → Ty164 → Set;Tm164
 = λ Γ A →
   (Tm164    : Con164 → Ty164 → Set)
   (var   : (Γ : _) (A : _) → Var164 Γ A → Tm164 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm164 (snoc164 Γ A) B → Tm164 Γ (arr164 A B))
   (app   : (Γ : _) (A B : _) → Tm164 Γ (arr164 A B) → Tm164 Γ A → Tm164 Γ B)
 → Tm164 Γ A

var164 : ∀{Γ A} → Var164 Γ A → Tm164 Γ A;var164
 = λ x Tm164 var164 lam app → var164 _ _ x

lam164 : ∀{Γ A B} → Tm164 (snoc164 Γ A) B → Tm164 Γ (arr164 A B);lam164
 = λ t Tm164 var164 lam164 app → lam164 _ _ _ (t Tm164 var164 lam164 app)

app164 : ∀{Γ A B} → Tm164 Γ (arr164 A B) → Tm164 Γ A → Tm164 Γ B;app164
 = λ t u Tm164 var164 lam164 app164 →
     app164 _ _ _ (t Tm164 var164 lam164 app164) (u Tm164 var164 lam164 app164)

v0164 : ∀{Γ A} → Tm164 (snoc164 Γ A) A;v0164
 = var164 vz164

v1164 : ∀{Γ A B} → Tm164 (snoc164 (snoc164 Γ A) B) A;v1164
 = var164 (vs164 vz164)

v2164 : ∀{Γ A B C} → Tm164 (snoc164 (snoc164 (snoc164 Γ A) B) C) A;v2164
 = var164 (vs164 (vs164 vz164))

v3164 : ∀{Γ A B C D} → Tm164 (snoc164 (snoc164 (snoc164 (snoc164 Γ A) B) C) D) A;v3164
 = var164 (vs164 (vs164 (vs164 vz164)))

v4164 : ∀{Γ A B C D E} → Tm164 (snoc164 (snoc164 (snoc164 (snoc164 (snoc164 Γ A) B) C) D) E) A;v4164
 = var164 (vs164 (vs164 (vs164 (vs164 vz164))))

test164 : ∀{Γ A} → Tm164 Γ (arr164 (arr164 A A) (arr164 A A));test164
  = lam164 (lam164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 v0164)))))))
{-# OPTIONS --type-in-type #-}

Ty165 : Set; Ty165
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι165   : Ty165; ι165 = λ _ ι165 _ → ι165
arr165 : Ty165 → Ty165 → Ty165; arr165 = λ A B Ty165 ι165 arr165 → arr165 (A Ty165 ι165 arr165) (B Ty165 ι165 arr165)

Con165 : Set;Con165
 = (Con165 : Set)
   (nil  : Con165)
   (snoc : Con165 → Ty165 → Con165)
 → Con165

nil165 : Con165;nil165
 = λ Con165 nil165 snoc → nil165

snoc165 : Con165 → Ty165 → Con165;snoc165
 = λ Γ A Con165 nil165 snoc165 → snoc165 (Γ Con165 nil165 snoc165) A

Var165 : Con165 → Ty165 → Set;Var165
 = λ Γ A →
   (Var165 : Con165 → Ty165 → Set)
   (vz  : (Γ : _)(A : _) → Var165 (snoc165 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var165 Γ A → Var165 (snoc165 Γ B) A)
 → Var165 Γ A

vz165 : ∀{Γ A} → Var165 (snoc165 Γ A) A;vz165
 = λ Var165 vz165 vs → vz165 _ _

vs165 : ∀{Γ B A} → Var165 Γ A → Var165 (snoc165 Γ B) A;vs165
 = λ x Var165 vz165 vs165 → vs165 _ _ _ (x Var165 vz165 vs165)

Tm165 : Con165 → Ty165 → Set;Tm165
 = λ Γ A →
   (Tm165    : Con165 → Ty165 → Set)
   (var   : (Γ : _) (A : _) → Var165 Γ A → Tm165 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm165 (snoc165 Γ A) B → Tm165 Γ (arr165 A B))
   (app   : (Γ : _) (A B : _) → Tm165 Γ (arr165 A B) → Tm165 Γ A → Tm165 Γ B)
 → Tm165 Γ A

var165 : ∀{Γ A} → Var165 Γ A → Tm165 Γ A;var165
 = λ x Tm165 var165 lam app → var165 _ _ x

lam165 : ∀{Γ A B} → Tm165 (snoc165 Γ A) B → Tm165 Γ (arr165 A B);lam165
 = λ t Tm165 var165 lam165 app → lam165 _ _ _ (t Tm165 var165 lam165 app)

app165 : ∀{Γ A B} → Tm165 Γ (arr165 A B) → Tm165 Γ A → Tm165 Γ B;app165
 = λ t u Tm165 var165 lam165 app165 →
     app165 _ _ _ (t Tm165 var165 lam165 app165) (u Tm165 var165 lam165 app165)

v0165 : ∀{Γ A} → Tm165 (snoc165 Γ A) A;v0165
 = var165 vz165

v1165 : ∀{Γ A B} → Tm165 (snoc165 (snoc165 Γ A) B) A;v1165
 = var165 (vs165 vz165)

v2165 : ∀{Γ A B C} → Tm165 (snoc165 (snoc165 (snoc165 Γ A) B) C) A;v2165
 = var165 (vs165 (vs165 vz165))

v3165 : ∀{Γ A B C D} → Tm165 (snoc165 (snoc165 (snoc165 (snoc165 Γ A) B) C) D) A;v3165
 = var165 (vs165 (vs165 (vs165 vz165)))

v4165 : ∀{Γ A B C D E} → Tm165 (snoc165 (snoc165 (snoc165 (snoc165 (snoc165 Γ A) B) C) D) E) A;v4165
 = var165 (vs165 (vs165 (vs165 (vs165 vz165))))

test165 : ∀{Γ A} → Tm165 Γ (arr165 (arr165 A A) (arr165 A A));test165
  = lam165 (lam165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 v0165)))))))
{-# OPTIONS --type-in-type #-}

Ty166 : Set; Ty166
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι166   : Ty166; ι166 = λ _ ι166 _ → ι166
arr166 : Ty166 → Ty166 → Ty166; arr166 = λ A B Ty166 ι166 arr166 → arr166 (A Ty166 ι166 arr166) (B Ty166 ι166 arr166)

Con166 : Set;Con166
 = (Con166 : Set)
   (nil  : Con166)
   (snoc : Con166 → Ty166 → Con166)
 → Con166

nil166 : Con166;nil166
 = λ Con166 nil166 snoc → nil166

snoc166 : Con166 → Ty166 → Con166;snoc166
 = λ Γ A Con166 nil166 snoc166 → snoc166 (Γ Con166 nil166 snoc166) A

Var166 : Con166 → Ty166 → Set;Var166
 = λ Γ A →
   (Var166 : Con166 → Ty166 → Set)
   (vz  : (Γ : _)(A : _) → Var166 (snoc166 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var166 Γ A → Var166 (snoc166 Γ B) A)
 → Var166 Γ A

vz166 : ∀{Γ A} → Var166 (snoc166 Γ A) A;vz166
 = λ Var166 vz166 vs → vz166 _ _

vs166 : ∀{Γ B A} → Var166 Γ A → Var166 (snoc166 Γ B) A;vs166
 = λ x Var166 vz166 vs166 → vs166 _ _ _ (x Var166 vz166 vs166)

Tm166 : Con166 → Ty166 → Set;Tm166
 = λ Γ A →
   (Tm166    : Con166 → Ty166 → Set)
   (var   : (Γ : _) (A : _) → Var166 Γ A → Tm166 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm166 (snoc166 Γ A) B → Tm166 Γ (arr166 A B))
   (app   : (Γ : _) (A B : _) → Tm166 Γ (arr166 A B) → Tm166 Γ A → Tm166 Γ B)
 → Tm166 Γ A

var166 : ∀{Γ A} → Var166 Γ A → Tm166 Γ A;var166
 = λ x Tm166 var166 lam app → var166 _ _ x

lam166 : ∀{Γ A B} → Tm166 (snoc166 Γ A) B → Tm166 Γ (arr166 A B);lam166
 = λ t Tm166 var166 lam166 app → lam166 _ _ _ (t Tm166 var166 lam166 app)

app166 : ∀{Γ A B} → Tm166 Γ (arr166 A B) → Tm166 Γ A → Tm166 Γ B;app166
 = λ t u Tm166 var166 lam166 app166 →
     app166 _ _ _ (t Tm166 var166 lam166 app166) (u Tm166 var166 lam166 app166)

v0166 : ∀{Γ A} → Tm166 (snoc166 Γ A) A;v0166
 = var166 vz166

v1166 : ∀{Γ A B} → Tm166 (snoc166 (snoc166 Γ A) B) A;v1166
 = var166 (vs166 vz166)

v2166 : ∀{Γ A B C} → Tm166 (snoc166 (snoc166 (snoc166 Γ A) B) C) A;v2166
 = var166 (vs166 (vs166 vz166))

v3166 : ∀{Γ A B C D} → Tm166 (snoc166 (snoc166 (snoc166 (snoc166 Γ A) B) C) D) A;v3166
 = var166 (vs166 (vs166 (vs166 vz166)))

v4166 : ∀{Γ A B C D E} → Tm166 (snoc166 (snoc166 (snoc166 (snoc166 (snoc166 Γ A) B) C) D) E) A;v4166
 = var166 (vs166 (vs166 (vs166 (vs166 vz166))))

test166 : ∀{Γ A} → Tm166 Γ (arr166 (arr166 A A) (arr166 A A));test166
  = lam166 (lam166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 v0166)))))))
{-# OPTIONS --type-in-type #-}

Ty167 : Set; Ty167
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι167   : Ty167; ι167 = λ _ ι167 _ → ι167
arr167 : Ty167 → Ty167 → Ty167; arr167 = λ A B Ty167 ι167 arr167 → arr167 (A Ty167 ι167 arr167) (B Ty167 ι167 arr167)

Con167 : Set;Con167
 = (Con167 : Set)
   (nil  : Con167)
   (snoc : Con167 → Ty167 → Con167)
 → Con167

nil167 : Con167;nil167
 = λ Con167 nil167 snoc → nil167

snoc167 : Con167 → Ty167 → Con167;snoc167
 = λ Γ A Con167 nil167 snoc167 → snoc167 (Γ Con167 nil167 snoc167) A

Var167 : Con167 → Ty167 → Set;Var167
 = λ Γ A →
   (Var167 : Con167 → Ty167 → Set)
   (vz  : (Γ : _)(A : _) → Var167 (snoc167 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var167 Γ A → Var167 (snoc167 Γ B) A)
 → Var167 Γ A

vz167 : ∀{Γ A} → Var167 (snoc167 Γ A) A;vz167
 = λ Var167 vz167 vs → vz167 _ _

vs167 : ∀{Γ B A} → Var167 Γ A → Var167 (snoc167 Γ B) A;vs167
 = λ x Var167 vz167 vs167 → vs167 _ _ _ (x Var167 vz167 vs167)

Tm167 : Con167 → Ty167 → Set;Tm167
 = λ Γ A →
   (Tm167    : Con167 → Ty167 → Set)
   (var   : (Γ : _) (A : _) → Var167 Γ A → Tm167 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm167 (snoc167 Γ A) B → Tm167 Γ (arr167 A B))
   (app   : (Γ : _) (A B : _) → Tm167 Γ (arr167 A B) → Tm167 Γ A → Tm167 Γ B)
 → Tm167 Γ A

var167 : ∀{Γ A} → Var167 Γ A → Tm167 Γ A;var167
 = λ x Tm167 var167 lam app → var167 _ _ x

lam167 : ∀{Γ A B} → Tm167 (snoc167 Γ A) B → Tm167 Γ (arr167 A B);lam167
 = λ t Tm167 var167 lam167 app → lam167 _ _ _ (t Tm167 var167 lam167 app)

app167 : ∀{Γ A B} → Tm167 Γ (arr167 A B) → Tm167 Γ A → Tm167 Γ B;app167
 = λ t u Tm167 var167 lam167 app167 →
     app167 _ _ _ (t Tm167 var167 lam167 app167) (u Tm167 var167 lam167 app167)

v0167 : ∀{Γ A} → Tm167 (snoc167 Γ A) A;v0167
 = var167 vz167

v1167 : ∀{Γ A B} → Tm167 (snoc167 (snoc167 Γ A) B) A;v1167
 = var167 (vs167 vz167)

v2167 : ∀{Γ A B C} → Tm167 (snoc167 (snoc167 (snoc167 Γ A) B) C) A;v2167
 = var167 (vs167 (vs167 vz167))

v3167 : ∀{Γ A B C D} → Tm167 (snoc167 (snoc167 (snoc167 (snoc167 Γ A) B) C) D) A;v3167
 = var167 (vs167 (vs167 (vs167 vz167)))

v4167 : ∀{Γ A B C D E} → Tm167 (snoc167 (snoc167 (snoc167 (snoc167 (snoc167 Γ A) B) C) D) E) A;v4167
 = var167 (vs167 (vs167 (vs167 (vs167 vz167))))

test167 : ∀{Γ A} → Tm167 Γ (arr167 (arr167 A A) (arr167 A A));test167
  = lam167 (lam167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 v0167)))))))
{-# OPTIONS --type-in-type #-}

Ty168 : Set; Ty168
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι168   : Ty168; ι168 = λ _ ι168 _ → ι168
arr168 : Ty168 → Ty168 → Ty168; arr168 = λ A B Ty168 ι168 arr168 → arr168 (A Ty168 ι168 arr168) (B Ty168 ι168 arr168)

Con168 : Set;Con168
 = (Con168 : Set)
   (nil  : Con168)
   (snoc : Con168 → Ty168 → Con168)
 → Con168

nil168 : Con168;nil168
 = λ Con168 nil168 snoc → nil168

snoc168 : Con168 → Ty168 → Con168;snoc168
 = λ Γ A Con168 nil168 snoc168 → snoc168 (Γ Con168 nil168 snoc168) A

Var168 : Con168 → Ty168 → Set;Var168
 = λ Γ A →
   (Var168 : Con168 → Ty168 → Set)
   (vz  : (Γ : _)(A : _) → Var168 (snoc168 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var168 Γ A → Var168 (snoc168 Γ B) A)
 → Var168 Γ A

vz168 : ∀{Γ A} → Var168 (snoc168 Γ A) A;vz168
 = λ Var168 vz168 vs → vz168 _ _

vs168 : ∀{Γ B A} → Var168 Γ A → Var168 (snoc168 Γ B) A;vs168
 = λ x Var168 vz168 vs168 → vs168 _ _ _ (x Var168 vz168 vs168)

Tm168 : Con168 → Ty168 → Set;Tm168
 = λ Γ A →
   (Tm168    : Con168 → Ty168 → Set)
   (var   : (Γ : _) (A : _) → Var168 Γ A → Tm168 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm168 (snoc168 Γ A) B → Tm168 Γ (arr168 A B))
   (app   : (Γ : _) (A B : _) → Tm168 Γ (arr168 A B) → Tm168 Γ A → Tm168 Γ B)
 → Tm168 Γ A

var168 : ∀{Γ A} → Var168 Γ A → Tm168 Γ A;var168
 = λ x Tm168 var168 lam app → var168 _ _ x

lam168 : ∀{Γ A B} → Tm168 (snoc168 Γ A) B → Tm168 Γ (arr168 A B);lam168
 = λ t Tm168 var168 lam168 app → lam168 _ _ _ (t Tm168 var168 lam168 app)

app168 : ∀{Γ A B} → Tm168 Γ (arr168 A B) → Tm168 Γ A → Tm168 Γ B;app168
 = λ t u Tm168 var168 lam168 app168 →
     app168 _ _ _ (t Tm168 var168 lam168 app168) (u Tm168 var168 lam168 app168)

v0168 : ∀{Γ A} → Tm168 (snoc168 Γ A) A;v0168
 = var168 vz168

v1168 : ∀{Γ A B} → Tm168 (snoc168 (snoc168 Γ A) B) A;v1168
 = var168 (vs168 vz168)

v2168 : ∀{Γ A B C} → Tm168 (snoc168 (snoc168 (snoc168 Γ A) B) C) A;v2168
 = var168 (vs168 (vs168 vz168))

v3168 : ∀{Γ A B C D} → Tm168 (snoc168 (snoc168 (snoc168 (snoc168 Γ A) B) C) D) A;v3168
 = var168 (vs168 (vs168 (vs168 vz168)))

v4168 : ∀{Γ A B C D E} → Tm168 (snoc168 (snoc168 (snoc168 (snoc168 (snoc168 Γ A) B) C) D) E) A;v4168
 = var168 (vs168 (vs168 (vs168 (vs168 vz168))))

test168 : ∀{Γ A} → Tm168 Γ (arr168 (arr168 A A) (arr168 A A));test168
  = lam168 (lam168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 v0168)))))))
{-# OPTIONS --type-in-type #-}

Ty169 : Set; Ty169
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι169   : Ty169; ι169 = λ _ ι169 _ → ι169
arr169 : Ty169 → Ty169 → Ty169; arr169 = λ A B Ty169 ι169 arr169 → arr169 (A Ty169 ι169 arr169) (B Ty169 ι169 arr169)

Con169 : Set;Con169
 = (Con169 : Set)
   (nil  : Con169)
   (snoc : Con169 → Ty169 → Con169)
 → Con169

nil169 : Con169;nil169
 = λ Con169 nil169 snoc → nil169

snoc169 : Con169 → Ty169 → Con169;snoc169
 = λ Γ A Con169 nil169 snoc169 → snoc169 (Γ Con169 nil169 snoc169) A

Var169 : Con169 → Ty169 → Set;Var169
 = λ Γ A →
   (Var169 : Con169 → Ty169 → Set)
   (vz  : (Γ : _)(A : _) → Var169 (snoc169 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var169 Γ A → Var169 (snoc169 Γ B) A)
 → Var169 Γ A

vz169 : ∀{Γ A} → Var169 (snoc169 Γ A) A;vz169
 = λ Var169 vz169 vs → vz169 _ _

vs169 : ∀{Γ B A} → Var169 Γ A → Var169 (snoc169 Γ B) A;vs169
 = λ x Var169 vz169 vs169 → vs169 _ _ _ (x Var169 vz169 vs169)

Tm169 : Con169 → Ty169 → Set;Tm169
 = λ Γ A →
   (Tm169    : Con169 → Ty169 → Set)
   (var   : (Γ : _) (A : _) → Var169 Γ A → Tm169 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm169 (snoc169 Γ A) B → Tm169 Γ (arr169 A B))
   (app   : (Γ : _) (A B : _) → Tm169 Γ (arr169 A B) → Tm169 Γ A → Tm169 Γ B)
 → Tm169 Γ A

var169 : ∀{Γ A} → Var169 Γ A → Tm169 Γ A;var169
 = λ x Tm169 var169 lam app → var169 _ _ x

lam169 : ∀{Γ A B} → Tm169 (snoc169 Γ A) B → Tm169 Γ (arr169 A B);lam169
 = λ t Tm169 var169 lam169 app → lam169 _ _ _ (t Tm169 var169 lam169 app)

app169 : ∀{Γ A B} → Tm169 Γ (arr169 A B) → Tm169 Γ A → Tm169 Γ B;app169
 = λ t u Tm169 var169 lam169 app169 →
     app169 _ _ _ (t Tm169 var169 lam169 app169) (u Tm169 var169 lam169 app169)

v0169 : ∀{Γ A} → Tm169 (snoc169 Γ A) A;v0169
 = var169 vz169

v1169 : ∀{Γ A B} → Tm169 (snoc169 (snoc169 Γ A) B) A;v1169
 = var169 (vs169 vz169)

v2169 : ∀{Γ A B C} → Tm169 (snoc169 (snoc169 (snoc169 Γ A) B) C) A;v2169
 = var169 (vs169 (vs169 vz169))

v3169 : ∀{Γ A B C D} → Tm169 (snoc169 (snoc169 (snoc169 (snoc169 Γ A) B) C) D) A;v3169
 = var169 (vs169 (vs169 (vs169 vz169)))

v4169 : ∀{Γ A B C D E} → Tm169 (snoc169 (snoc169 (snoc169 (snoc169 (snoc169 Γ A) B) C) D) E) A;v4169
 = var169 (vs169 (vs169 (vs169 (vs169 vz169))))

test169 : ∀{Γ A} → Tm169 Γ (arr169 (arr169 A A) (arr169 A A));test169
  = lam169 (lam169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 v0169)))))))
{-# OPTIONS --type-in-type #-}

Ty170 : Set; Ty170
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι170   : Ty170; ι170 = λ _ ι170 _ → ι170
arr170 : Ty170 → Ty170 → Ty170; arr170 = λ A B Ty170 ι170 arr170 → arr170 (A Ty170 ι170 arr170) (B Ty170 ι170 arr170)

Con170 : Set;Con170
 = (Con170 : Set)
   (nil  : Con170)
   (snoc : Con170 → Ty170 → Con170)
 → Con170

nil170 : Con170;nil170
 = λ Con170 nil170 snoc → nil170

snoc170 : Con170 → Ty170 → Con170;snoc170
 = λ Γ A Con170 nil170 snoc170 → snoc170 (Γ Con170 nil170 snoc170) A

Var170 : Con170 → Ty170 → Set;Var170
 = λ Γ A →
   (Var170 : Con170 → Ty170 → Set)
   (vz  : (Γ : _)(A : _) → Var170 (snoc170 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var170 Γ A → Var170 (snoc170 Γ B) A)
 → Var170 Γ A

vz170 : ∀{Γ A} → Var170 (snoc170 Γ A) A;vz170
 = λ Var170 vz170 vs → vz170 _ _

vs170 : ∀{Γ B A} → Var170 Γ A → Var170 (snoc170 Γ B) A;vs170
 = λ x Var170 vz170 vs170 → vs170 _ _ _ (x Var170 vz170 vs170)

Tm170 : Con170 → Ty170 → Set;Tm170
 = λ Γ A →
   (Tm170    : Con170 → Ty170 → Set)
   (var   : (Γ : _) (A : _) → Var170 Γ A → Tm170 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm170 (snoc170 Γ A) B → Tm170 Γ (arr170 A B))
   (app   : (Γ : _) (A B : _) → Tm170 Γ (arr170 A B) → Tm170 Γ A → Tm170 Γ B)
 → Tm170 Γ A

var170 : ∀{Γ A} → Var170 Γ A → Tm170 Γ A;var170
 = λ x Tm170 var170 lam app → var170 _ _ x

lam170 : ∀{Γ A B} → Tm170 (snoc170 Γ A) B → Tm170 Γ (arr170 A B);lam170
 = λ t Tm170 var170 lam170 app → lam170 _ _ _ (t Tm170 var170 lam170 app)

app170 : ∀{Γ A B} → Tm170 Γ (arr170 A B) → Tm170 Γ A → Tm170 Γ B;app170
 = λ t u Tm170 var170 lam170 app170 →
     app170 _ _ _ (t Tm170 var170 lam170 app170) (u Tm170 var170 lam170 app170)

v0170 : ∀{Γ A} → Tm170 (snoc170 Γ A) A;v0170
 = var170 vz170

v1170 : ∀{Γ A B} → Tm170 (snoc170 (snoc170 Γ A) B) A;v1170
 = var170 (vs170 vz170)

v2170 : ∀{Γ A B C} → Tm170 (snoc170 (snoc170 (snoc170 Γ A) B) C) A;v2170
 = var170 (vs170 (vs170 vz170))

v3170 : ∀{Γ A B C D} → Tm170 (snoc170 (snoc170 (snoc170 (snoc170 Γ A) B) C) D) A;v3170
 = var170 (vs170 (vs170 (vs170 vz170)))

v4170 : ∀{Γ A B C D E} → Tm170 (snoc170 (snoc170 (snoc170 (snoc170 (snoc170 Γ A) B) C) D) E) A;v4170
 = var170 (vs170 (vs170 (vs170 (vs170 vz170))))

test170 : ∀{Γ A} → Tm170 Γ (arr170 (arr170 A A) (arr170 A A));test170
  = lam170 (lam170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 v0170)))))))
{-# OPTIONS --type-in-type #-}

Ty171 : Set; Ty171
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι171   : Ty171; ι171 = λ _ ι171 _ → ι171
arr171 : Ty171 → Ty171 → Ty171; arr171 = λ A B Ty171 ι171 arr171 → arr171 (A Ty171 ι171 arr171) (B Ty171 ι171 arr171)

Con171 : Set;Con171
 = (Con171 : Set)
   (nil  : Con171)
   (snoc : Con171 → Ty171 → Con171)
 → Con171

nil171 : Con171;nil171
 = λ Con171 nil171 snoc → nil171

snoc171 : Con171 → Ty171 → Con171;snoc171
 = λ Γ A Con171 nil171 snoc171 → snoc171 (Γ Con171 nil171 snoc171) A

Var171 : Con171 → Ty171 → Set;Var171
 = λ Γ A →
   (Var171 : Con171 → Ty171 → Set)
   (vz  : (Γ : _)(A : _) → Var171 (snoc171 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var171 Γ A → Var171 (snoc171 Γ B) A)
 → Var171 Γ A

vz171 : ∀{Γ A} → Var171 (snoc171 Γ A) A;vz171
 = λ Var171 vz171 vs → vz171 _ _

vs171 : ∀{Γ B A} → Var171 Γ A → Var171 (snoc171 Γ B) A;vs171
 = λ x Var171 vz171 vs171 → vs171 _ _ _ (x Var171 vz171 vs171)

Tm171 : Con171 → Ty171 → Set;Tm171
 = λ Γ A →
   (Tm171    : Con171 → Ty171 → Set)
   (var   : (Γ : _) (A : _) → Var171 Γ A → Tm171 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm171 (snoc171 Γ A) B → Tm171 Γ (arr171 A B))
   (app   : (Γ : _) (A B : _) → Tm171 Γ (arr171 A B) → Tm171 Γ A → Tm171 Γ B)
 → Tm171 Γ A

var171 : ∀{Γ A} → Var171 Γ A → Tm171 Γ A;var171
 = λ x Tm171 var171 lam app → var171 _ _ x

lam171 : ∀{Γ A B} → Tm171 (snoc171 Γ A) B → Tm171 Γ (arr171 A B);lam171
 = λ t Tm171 var171 lam171 app → lam171 _ _ _ (t Tm171 var171 lam171 app)

app171 : ∀{Γ A B} → Tm171 Γ (arr171 A B) → Tm171 Γ A → Tm171 Γ B;app171
 = λ t u Tm171 var171 lam171 app171 →
     app171 _ _ _ (t Tm171 var171 lam171 app171) (u Tm171 var171 lam171 app171)

v0171 : ∀{Γ A} → Tm171 (snoc171 Γ A) A;v0171
 = var171 vz171

v1171 : ∀{Γ A B} → Tm171 (snoc171 (snoc171 Γ A) B) A;v1171
 = var171 (vs171 vz171)

v2171 : ∀{Γ A B C} → Tm171 (snoc171 (snoc171 (snoc171 Γ A) B) C) A;v2171
 = var171 (vs171 (vs171 vz171))

v3171 : ∀{Γ A B C D} → Tm171 (snoc171 (snoc171 (snoc171 (snoc171 Γ A) B) C) D) A;v3171
 = var171 (vs171 (vs171 (vs171 vz171)))

v4171 : ∀{Γ A B C D E} → Tm171 (snoc171 (snoc171 (snoc171 (snoc171 (snoc171 Γ A) B) C) D) E) A;v4171
 = var171 (vs171 (vs171 (vs171 (vs171 vz171))))

test171 : ∀{Γ A} → Tm171 Γ (arr171 (arr171 A A) (arr171 A A));test171
  = lam171 (lam171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 v0171)))))))
{-# OPTIONS --type-in-type #-}

Ty172 : Set; Ty172
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι172   : Ty172; ι172 = λ _ ι172 _ → ι172
arr172 : Ty172 → Ty172 → Ty172; arr172 = λ A B Ty172 ι172 arr172 → arr172 (A Ty172 ι172 arr172) (B Ty172 ι172 arr172)

Con172 : Set;Con172
 = (Con172 : Set)
   (nil  : Con172)
   (snoc : Con172 → Ty172 → Con172)
 → Con172

nil172 : Con172;nil172
 = λ Con172 nil172 snoc → nil172

snoc172 : Con172 → Ty172 → Con172;snoc172
 = λ Γ A Con172 nil172 snoc172 → snoc172 (Γ Con172 nil172 snoc172) A

Var172 : Con172 → Ty172 → Set;Var172
 = λ Γ A →
   (Var172 : Con172 → Ty172 → Set)
   (vz  : (Γ : _)(A : _) → Var172 (snoc172 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var172 Γ A → Var172 (snoc172 Γ B) A)
 → Var172 Γ A

vz172 : ∀{Γ A} → Var172 (snoc172 Γ A) A;vz172
 = λ Var172 vz172 vs → vz172 _ _

vs172 : ∀{Γ B A} → Var172 Γ A → Var172 (snoc172 Γ B) A;vs172
 = λ x Var172 vz172 vs172 → vs172 _ _ _ (x Var172 vz172 vs172)

Tm172 : Con172 → Ty172 → Set;Tm172
 = λ Γ A →
   (Tm172    : Con172 → Ty172 → Set)
   (var   : (Γ : _) (A : _) → Var172 Γ A → Tm172 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm172 (snoc172 Γ A) B → Tm172 Γ (arr172 A B))
   (app   : (Γ : _) (A B : _) → Tm172 Γ (arr172 A B) → Tm172 Γ A → Tm172 Γ B)
 → Tm172 Γ A

var172 : ∀{Γ A} → Var172 Γ A → Tm172 Γ A;var172
 = λ x Tm172 var172 lam app → var172 _ _ x

lam172 : ∀{Γ A B} → Tm172 (snoc172 Γ A) B → Tm172 Γ (arr172 A B);lam172
 = λ t Tm172 var172 lam172 app → lam172 _ _ _ (t Tm172 var172 lam172 app)

app172 : ∀{Γ A B} → Tm172 Γ (arr172 A B) → Tm172 Γ A → Tm172 Γ B;app172
 = λ t u Tm172 var172 lam172 app172 →
     app172 _ _ _ (t Tm172 var172 lam172 app172) (u Tm172 var172 lam172 app172)

v0172 : ∀{Γ A} → Tm172 (snoc172 Γ A) A;v0172
 = var172 vz172

v1172 : ∀{Γ A B} → Tm172 (snoc172 (snoc172 Γ A) B) A;v1172
 = var172 (vs172 vz172)

v2172 : ∀{Γ A B C} → Tm172 (snoc172 (snoc172 (snoc172 Γ A) B) C) A;v2172
 = var172 (vs172 (vs172 vz172))

v3172 : ∀{Γ A B C D} → Tm172 (snoc172 (snoc172 (snoc172 (snoc172 Γ A) B) C) D) A;v3172
 = var172 (vs172 (vs172 (vs172 vz172)))

v4172 : ∀{Γ A B C D E} → Tm172 (snoc172 (snoc172 (snoc172 (snoc172 (snoc172 Γ A) B) C) D) E) A;v4172
 = var172 (vs172 (vs172 (vs172 (vs172 vz172))))

test172 : ∀{Γ A} → Tm172 Γ (arr172 (arr172 A A) (arr172 A A));test172
  = lam172 (lam172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 v0172)))))))
{-# OPTIONS --type-in-type #-}

Ty173 : Set; Ty173
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι173   : Ty173; ι173 = λ _ ι173 _ → ι173
arr173 : Ty173 → Ty173 → Ty173; arr173 = λ A B Ty173 ι173 arr173 → arr173 (A Ty173 ι173 arr173) (B Ty173 ι173 arr173)

Con173 : Set;Con173
 = (Con173 : Set)
   (nil  : Con173)
   (snoc : Con173 → Ty173 → Con173)
 → Con173

nil173 : Con173;nil173
 = λ Con173 nil173 snoc → nil173

snoc173 : Con173 → Ty173 → Con173;snoc173
 = λ Γ A Con173 nil173 snoc173 → snoc173 (Γ Con173 nil173 snoc173) A

Var173 : Con173 → Ty173 → Set;Var173
 = λ Γ A →
   (Var173 : Con173 → Ty173 → Set)
   (vz  : (Γ : _)(A : _) → Var173 (snoc173 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var173 Γ A → Var173 (snoc173 Γ B) A)
 → Var173 Γ A

vz173 : ∀{Γ A} → Var173 (snoc173 Γ A) A;vz173
 = λ Var173 vz173 vs → vz173 _ _

vs173 : ∀{Γ B A} → Var173 Γ A → Var173 (snoc173 Γ B) A;vs173
 = λ x Var173 vz173 vs173 → vs173 _ _ _ (x Var173 vz173 vs173)

Tm173 : Con173 → Ty173 → Set;Tm173
 = λ Γ A →
   (Tm173    : Con173 → Ty173 → Set)
   (var   : (Γ : _) (A : _) → Var173 Γ A → Tm173 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm173 (snoc173 Γ A) B → Tm173 Γ (arr173 A B))
   (app   : (Γ : _) (A B : _) → Tm173 Γ (arr173 A B) → Tm173 Γ A → Tm173 Γ B)
 → Tm173 Γ A

var173 : ∀{Γ A} → Var173 Γ A → Tm173 Γ A;var173
 = λ x Tm173 var173 lam app → var173 _ _ x

lam173 : ∀{Γ A B} → Tm173 (snoc173 Γ A) B → Tm173 Γ (arr173 A B);lam173
 = λ t Tm173 var173 lam173 app → lam173 _ _ _ (t Tm173 var173 lam173 app)

app173 : ∀{Γ A B} → Tm173 Γ (arr173 A B) → Tm173 Γ A → Tm173 Γ B;app173
 = λ t u Tm173 var173 lam173 app173 →
     app173 _ _ _ (t Tm173 var173 lam173 app173) (u Tm173 var173 lam173 app173)

v0173 : ∀{Γ A} → Tm173 (snoc173 Γ A) A;v0173
 = var173 vz173

v1173 : ∀{Γ A B} → Tm173 (snoc173 (snoc173 Γ A) B) A;v1173
 = var173 (vs173 vz173)

v2173 : ∀{Γ A B C} → Tm173 (snoc173 (snoc173 (snoc173 Γ A) B) C) A;v2173
 = var173 (vs173 (vs173 vz173))

v3173 : ∀{Γ A B C D} → Tm173 (snoc173 (snoc173 (snoc173 (snoc173 Γ A) B) C) D) A;v3173
 = var173 (vs173 (vs173 (vs173 vz173)))

v4173 : ∀{Γ A B C D E} → Tm173 (snoc173 (snoc173 (snoc173 (snoc173 (snoc173 Γ A) B) C) D) E) A;v4173
 = var173 (vs173 (vs173 (vs173 (vs173 vz173))))

test173 : ∀{Γ A} → Tm173 Γ (arr173 (arr173 A A) (arr173 A A));test173
  = lam173 (lam173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 v0173)))))))
{-# OPTIONS --type-in-type #-}

Ty174 : Set; Ty174
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι174   : Ty174; ι174 = λ _ ι174 _ → ι174
arr174 : Ty174 → Ty174 → Ty174; arr174 = λ A B Ty174 ι174 arr174 → arr174 (A Ty174 ι174 arr174) (B Ty174 ι174 arr174)

Con174 : Set;Con174
 = (Con174 : Set)
   (nil  : Con174)
   (snoc : Con174 → Ty174 → Con174)
 → Con174

nil174 : Con174;nil174
 = λ Con174 nil174 snoc → nil174

snoc174 : Con174 → Ty174 → Con174;snoc174
 = λ Γ A Con174 nil174 snoc174 → snoc174 (Γ Con174 nil174 snoc174) A

Var174 : Con174 → Ty174 → Set;Var174
 = λ Γ A →
   (Var174 : Con174 → Ty174 → Set)
   (vz  : (Γ : _)(A : _) → Var174 (snoc174 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var174 Γ A → Var174 (snoc174 Γ B) A)
 → Var174 Γ A

vz174 : ∀{Γ A} → Var174 (snoc174 Γ A) A;vz174
 = λ Var174 vz174 vs → vz174 _ _

vs174 : ∀{Γ B A} → Var174 Γ A → Var174 (snoc174 Γ B) A;vs174
 = λ x Var174 vz174 vs174 → vs174 _ _ _ (x Var174 vz174 vs174)

Tm174 : Con174 → Ty174 → Set;Tm174
 = λ Γ A →
   (Tm174    : Con174 → Ty174 → Set)
   (var   : (Γ : _) (A : _) → Var174 Γ A → Tm174 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm174 (snoc174 Γ A) B → Tm174 Γ (arr174 A B))
   (app   : (Γ : _) (A B : _) → Tm174 Γ (arr174 A B) → Tm174 Γ A → Tm174 Γ B)
 → Tm174 Γ A

var174 : ∀{Γ A} → Var174 Γ A → Tm174 Γ A;var174
 = λ x Tm174 var174 lam app → var174 _ _ x

lam174 : ∀{Γ A B} → Tm174 (snoc174 Γ A) B → Tm174 Γ (arr174 A B);lam174
 = λ t Tm174 var174 lam174 app → lam174 _ _ _ (t Tm174 var174 lam174 app)

app174 : ∀{Γ A B} → Tm174 Γ (arr174 A B) → Tm174 Γ A → Tm174 Γ B;app174
 = λ t u Tm174 var174 lam174 app174 →
     app174 _ _ _ (t Tm174 var174 lam174 app174) (u Tm174 var174 lam174 app174)

v0174 : ∀{Γ A} → Tm174 (snoc174 Γ A) A;v0174
 = var174 vz174

v1174 : ∀{Γ A B} → Tm174 (snoc174 (snoc174 Γ A) B) A;v1174
 = var174 (vs174 vz174)

v2174 : ∀{Γ A B C} → Tm174 (snoc174 (snoc174 (snoc174 Γ A) B) C) A;v2174
 = var174 (vs174 (vs174 vz174))

v3174 : ∀{Γ A B C D} → Tm174 (snoc174 (snoc174 (snoc174 (snoc174 Γ A) B) C) D) A;v3174
 = var174 (vs174 (vs174 (vs174 vz174)))

v4174 : ∀{Γ A B C D E} → Tm174 (snoc174 (snoc174 (snoc174 (snoc174 (snoc174 Γ A) B) C) D) E) A;v4174
 = var174 (vs174 (vs174 (vs174 (vs174 vz174))))

test174 : ∀{Γ A} → Tm174 Γ (arr174 (arr174 A A) (arr174 A A));test174
  = lam174 (lam174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 v0174)))))))
{-# OPTIONS --type-in-type #-}

Ty175 : Set; Ty175
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι175   : Ty175; ι175 = λ _ ι175 _ → ι175
arr175 : Ty175 → Ty175 → Ty175; arr175 = λ A B Ty175 ι175 arr175 → arr175 (A Ty175 ι175 arr175) (B Ty175 ι175 arr175)

Con175 : Set;Con175
 = (Con175 : Set)
   (nil  : Con175)
   (snoc : Con175 → Ty175 → Con175)
 → Con175

nil175 : Con175;nil175
 = λ Con175 nil175 snoc → nil175

snoc175 : Con175 → Ty175 → Con175;snoc175
 = λ Γ A Con175 nil175 snoc175 → snoc175 (Γ Con175 nil175 snoc175) A

Var175 : Con175 → Ty175 → Set;Var175
 = λ Γ A →
   (Var175 : Con175 → Ty175 → Set)
   (vz  : (Γ : _)(A : _) → Var175 (snoc175 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var175 Γ A → Var175 (snoc175 Γ B) A)
 → Var175 Γ A

vz175 : ∀{Γ A} → Var175 (snoc175 Γ A) A;vz175
 = λ Var175 vz175 vs → vz175 _ _

vs175 : ∀{Γ B A} → Var175 Γ A → Var175 (snoc175 Γ B) A;vs175
 = λ x Var175 vz175 vs175 → vs175 _ _ _ (x Var175 vz175 vs175)

Tm175 : Con175 → Ty175 → Set;Tm175
 = λ Γ A →
   (Tm175    : Con175 → Ty175 → Set)
   (var   : (Γ : _) (A : _) → Var175 Γ A → Tm175 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm175 (snoc175 Γ A) B → Tm175 Γ (arr175 A B))
   (app   : (Γ : _) (A B : _) → Tm175 Γ (arr175 A B) → Tm175 Γ A → Tm175 Γ B)
 → Tm175 Γ A

var175 : ∀{Γ A} → Var175 Γ A → Tm175 Γ A;var175
 = λ x Tm175 var175 lam app → var175 _ _ x

lam175 : ∀{Γ A B} → Tm175 (snoc175 Γ A) B → Tm175 Γ (arr175 A B);lam175
 = λ t Tm175 var175 lam175 app → lam175 _ _ _ (t Tm175 var175 lam175 app)

app175 : ∀{Γ A B} → Tm175 Γ (arr175 A B) → Tm175 Γ A → Tm175 Γ B;app175
 = λ t u Tm175 var175 lam175 app175 →
     app175 _ _ _ (t Tm175 var175 lam175 app175) (u Tm175 var175 lam175 app175)

v0175 : ∀{Γ A} → Tm175 (snoc175 Γ A) A;v0175
 = var175 vz175

v1175 : ∀{Γ A B} → Tm175 (snoc175 (snoc175 Γ A) B) A;v1175
 = var175 (vs175 vz175)

v2175 : ∀{Γ A B C} → Tm175 (snoc175 (snoc175 (snoc175 Γ A) B) C) A;v2175
 = var175 (vs175 (vs175 vz175))

v3175 : ∀{Γ A B C D} → Tm175 (snoc175 (snoc175 (snoc175 (snoc175 Γ A) B) C) D) A;v3175
 = var175 (vs175 (vs175 (vs175 vz175)))

v4175 : ∀{Γ A B C D E} → Tm175 (snoc175 (snoc175 (snoc175 (snoc175 (snoc175 Γ A) B) C) D) E) A;v4175
 = var175 (vs175 (vs175 (vs175 (vs175 vz175))))

test175 : ∀{Γ A} → Tm175 Γ (arr175 (arr175 A A) (arr175 A A));test175
  = lam175 (lam175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 v0175)))))))
{-# OPTIONS --type-in-type #-}

Ty176 : Set; Ty176
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι176   : Ty176; ι176 = λ _ ι176 _ → ι176
arr176 : Ty176 → Ty176 → Ty176; arr176 = λ A B Ty176 ι176 arr176 → arr176 (A Ty176 ι176 arr176) (B Ty176 ι176 arr176)

Con176 : Set;Con176
 = (Con176 : Set)
   (nil  : Con176)
   (snoc : Con176 → Ty176 → Con176)
 → Con176

nil176 : Con176;nil176
 = λ Con176 nil176 snoc → nil176

snoc176 : Con176 → Ty176 → Con176;snoc176
 = λ Γ A Con176 nil176 snoc176 → snoc176 (Γ Con176 nil176 snoc176) A

Var176 : Con176 → Ty176 → Set;Var176
 = λ Γ A →
   (Var176 : Con176 → Ty176 → Set)
   (vz  : (Γ : _)(A : _) → Var176 (snoc176 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var176 Γ A → Var176 (snoc176 Γ B) A)
 → Var176 Γ A

vz176 : ∀{Γ A} → Var176 (snoc176 Γ A) A;vz176
 = λ Var176 vz176 vs → vz176 _ _

vs176 : ∀{Γ B A} → Var176 Γ A → Var176 (snoc176 Γ B) A;vs176
 = λ x Var176 vz176 vs176 → vs176 _ _ _ (x Var176 vz176 vs176)

Tm176 : Con176 → Ty176 → Set;Tm176
 = λ Γ A →
   (Tm176    : Con176 → Ty176 → Set)
   (var   : (Γ : _) (A : _) → Var176 Γ A → Tm176 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm176 (snoc176 Γ A) B → Tm176 Γ (arr176 A B))
   (app   : (Γ : _) (A B : _) → Tm176 Γ (arr176 A B) → Tm176 Γ A → Tm176 Γ B)
 → Tm176 Γ A

var176 : ∀{Γ A} → Var176 Γ A → Tm176 Γ A;var176
 = λ x Tm176 var176 lam app → var176 _ _ x

lam176 : ∀{Γ A B} → Tm176 (snoc176 Γ A) B → Tm176 Γ (arr176 A B);lam176
 = λ t Tm176 var176 lam176 app → lam176 _ _ _ (t Tm176 var176 lam176 app)

app176 : ∀{Γ A B} → Tm176 Γ (arr176 A B) → Tm176 Γ A → Tm176 Γ B;app176
 = λ t u Tm176 var176 lam176 app176 →
     app176 _ _ _ (t Tm176 var176 lam176 app176) (u Tm176 var176 lam176 app176)

v0176 : ∀{Γ A} → Tm176 (snoc176 Γ A) A;v0176
 = var176 vz176

v1176 : ∀{Γ A B} → Tm176 (snoc176 (snoc176 Γ A) B) A;v1176
 = var176 (vs176 vz176)

v2176 : ∀{Γ A B C} → Tm176 (snoc176 (snoc176 (snoc176 Γ A) B) C) A;v2176
 = var176 (vs176 (vs176 vz176))

v3176 : ∀{Γ A B C D} → Tm176 (snoc176 (snoc176 (snoc176 (snoc176 Γ A) B) C) D) A;v3176
 = var176 (vs176 (vs176 (vs176 vz176)))

v4176 : ∀{Γ A B C D E} → Tm176 (snoc176 (snoc176 (snoc176 (snoc176 (snoc176 Γ A) B) C) D) E) A;v4176
 = var176 (vs176 (vs176 (vs176 (vs176 vz176))))

test176 : ∀{Γ A} → Tm176 Γ (arr176 (arr176 A A) (arr176 A A));test176
  = lam176 (lam176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 v0176)))))))
{-# OPTIONS --type-in-type #-}

Ty177 : Set; Ty177
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι177   : Ty177; ι177 = λ _ ι177 _ → ι177
arr177 : Ty177 → Ty177 → Ty177; arr177 = λ A B Ty177 ι177 arr177 → arr177 (A Ty177 ι177 arr177) (B Ty177 ι177 arr177)

Con177 : Set;Con177
 = (Con177 : Set)
   (nil  : Con177)
   (snoc : Con177 → Ty177 → Con177)
 → Con177

nil177 : Con177;nil177
 = λ Con177 nil177 snoc → nil177

snoc177 : Con177 → Ty177 → Con177;snoc177
 = λ Γ A Con177 nil177 snoc177 → snoc177 (Γ Con177 nil177 snoc177) A

Var177 : Con177 → Ty177 → Set;Var177
 = λ Γ A →
   (Var177 : Con177 → Ty177 → Set)
   (vz  : (Γ : _)(A : _) → Var177 (snoc177 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var177 Γ A → Var177 (snoc177 Γ B) A)
 → Var177 Γ A

vz177 : ∀{Γ A} → Var177 (snoc177 Γ A) A;vz177
 = λ Var177 vz177 vs → vz177 _ _

vs177 : ∀{Γ B A} → Var177 Γ A → Var177 (snoc177 Γ B) A;vs177
 = λ x Var177 vz177 vs177 → vs177 _ _ _ (x Var177 vz177 vs177)

Tm177 : Con177 → Ty177 → Set;Tm177
 = λ Γ A →
   (Tm177    : Con177 → Ty177 → Set)
   (var   : (Γ : _) (A : _) → Var177 Γ A → Tm177 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm177 (snoc177 Γ A) B → Tm177 Γ (arr177 A B))
   (app   : (Γ : _) (A B : _) → Tm177 Γ (arr177 A B) → Tm177 Γ A → Tm177 Γ B)
 → Tm177 Γ A

var177 : ∀{Γ A} → Var177 Γ A → Tm177 Γ A;var177
 = λ x Tm177 var177 lam app → var177 _ _ x

lam177 : ∀{Γ A B} → Tm177 (snoc177 Γ A) B → Tm177 Γ (arr177 A B);lam177
 = λ t Tm177 var177 lam177 app → lam177 _ _ _ (t Tm177 var177 lam177 app)

app177 : ∀{Γ A B} → Tm177 Γ (arr177 A B) → Tm177 Γ A → Tm177 Γ B;app177
 = λ t u Tm177 var177 lam177 app177 →
     app177 _ _ _ (t Tm177 var177 lam177 app177) (u Tm177 var177 lam177 app177)

v0177 : ∀{Γ A} → Tm177 (snoc177 Γ A) A;v0177
 = var177 vz177

v1177 : ∀{Γ A B} → Tm177 (snoc177 (snoc177 Γ A) B) A;v1177
 = var177 (vs177 vz177)

v2177 : ∀{Γ A B C} → Tm177 (snoc177 (snoc177 (snoc177 Γ A) B) C) A;v2177
 = var177 (vs177 (vs177 vz177))

v3177 : ∀{Γ A B C D} → Tm177 (snoc177 (snoc177 (snoc177 (snoc177 Γ A) B) C) D) A;v3177
 = var177 (vs177 (vs177 (vs177 vz177)))

v4177 : ∀{Γ A B C D E} → Tm177 (snoc177 (snoc177 (snoc177 (snoc177 (snoc177 Γ A) B) C) D) E) A;v4177
 = var177 (vs177 (vs177 (vs177 (vs177 vz177))))

test177 : ∀{Γ A} → Tm177 Γ (arr177 (arr177 A A) (arr177 A A));test177
  = lam177 (lam177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 v0177)))))))
{-# OPTIONS --type-in-type #-}

Ty178 : Set; Ty178
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι178   : Ty178; ι178 = λ _ ι178 _ → ι178
arr178 : Ty178 → Ty178 → Ty178; arr178 = λ A B Ty178 ι178 arr178 → arr178 (A Ty178 ι178 arr178) (B Ty178 ι178 arr178)

Con178 : Set;Con178
 = (Con178 : Set)
   (nil  : Con178)
   (snoc : Con178 → Ty178 → Con178)
 → Con178

nil178 : Con178;nil178
 = λ Con178 nil178 snoc → nil178

snoc178 : Con178 → Ty178 → Con178;snoc178
 = λ Γ A Con178 nil178 snoc178 → snoc178 (Γ Con178 nil178 snoc178) A

Var178 : Con178 → Ty178 → Set;Var178
 = λ Γ A →
   (Var178 : Con178 → Ty178 → Set)
   (vz  : (Γ : _)(A : _) → Var178 (snoc178 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var178 Γ A → Var178 (snoc178 Γ B) A)
 → Var178 Γ A

vz178 : ∀{Γ A} → Var178 (snoc178 Γ A) A;vz178
 = λ Var178 vz178 vs → vz178 _ _

vs178 : ∀{Γ B A} → Var178 Γ A → Var178 (snoc178 Γ B) A;vs178
 = λ x Var178 vz178 vs178 → vs178 _ _ _ (x Var178 vz178 vs178)

Tm178 : Con178 → Ty178 → Set;Tm178
 = λ Γ A →
   (Tm178    : Con178 → Ty178 → Set)
   (var   : (Γ : _) (A : _) → Var178 Γ A → Tm178 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm178 (snoc178 Γ A) B → Tm178 Γ (arr178 A B))
   (app   : (Γ : _) (A B : _) → Tm178 Γ (arr178 A B) → Tm178 Γ A → Tm178 Γ B)
 → Tm178 Γ A

var178 : ∀{Γ A} → Var178 Γ A → Tm178 Γ A;var178
 = λ x Tm178 var178 lam app → var178 _ _ x

lam178 : ∀{Γ A B} → Tm178 (snoc178 Γ A) B → Tm178 Γ (arr178 A B);lam178
 = λ t Tm178 var178 lam178 app → lam178 _ _ _ (t Tm178 var178 lam178 app)

app178 : ∀{Γ A B} → Tm178 Γ (arr178 A B) → Tm178 Γ A → Tm178 Γ B;app178
 = λ t u Tm178 var178 lam178 app178 →
     app178 _ _ _ (t Tm178 var178 lam178 app178) (u Tm178 var178 lam178 app178)

v0178 : ∀{Γ A} → Tm178 (snoc178 Γ A) A;v0178
 = var178 vz178

v1178 : ∀{Γ A B} → Tm178 (snoc178 (snoc178 Γ A) B) A;v1178
 = var178 (vs178 vz178)

v2178 : ∀{Γ A B C} → Tm178 (snoc178 (snoc178 (snoc178 Γ A) B) C) A;v2178
 = var178 (vs178 (vs178 vz178))

v3178 : ∀{Γ A B C D} → Tm178 (snoc178 (snoc178 (snoc178 (snoc178 Γ A) B) C) D) A;v3178
 = var178 (vs178 (vs178 (vs178 vz178)))

v4178 : ∀{Γ A B C D E} → Tm178 (snoc178 (snoc178 (snoc178 (snoc178 (snoc178 Γ A) B) C) D) E) A;v4178
 = var178 (vs178 (vs178 (vs178 (vs178 vz178))))

test178 : ∀{Γ A} → Tm178 Γ (arr178 (arr178 A A) (arr178 A A));test178
  = lam178 (lam178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 v0178)))))))
{-# OPTIONS --type-in-type #-}

Ty179 : Set; Ty179
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι179   : Ty179; ι179 = λ _ ι179 _ → ι179
arr179 : Ty179 → Ty179 → Ty179; arr179 = λ A B Ty179 ι179 arr179 → arr179 (A Ty179 ι179 arr179) (B Ty179 ι179 arr179)

Con179 : Set;Con179
 = (Con179 : Set)
   (nil  : Con179)
   (snoc : Con179 → Ty179 → Con179)
 → Con179

nil179 : Con179;nil179
 = λ Con179 nil179 snoc → nil179

snoc179 : Con179 → Ty179 → Con179;snoc179
 = λ Γ A Con179 nil179 snoc179 → snoc179 (Γ Con179 nil179 snoc179) A

Var179 : Con179 → Ty179 → Set;Var179
 = λ Γ A →
   (Var179 : Con179 → Ty179 → Set)
   (vz  : (Γ : _)(A : _) → Var179 (snoc179 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var179 Γ A → Var179 (snoc179 Γ B) A)
 → Var179 Γ A

vz179 : ∀{Γ A} → Var179 (snoc179 Γ A) A;vz179
 = λ Var179 vz179 vs → vz179 _ _

vs179 : ∀{Γ B A} → Var179 Γ A → Var179 (snoc179 Γ B) A;vs179
 = λ x Var179 vz179 vs179 → vs179 _ _ _ (x Var179 vz179 vs179)

Tm179 : Con179 → Ty179 → Set;Tm179
 = λ Γ A →
   (Tm179    : Con179 → Ty179 → Set)
   (var   : (Γ : _) (A : _) → Var179 Γ A → Tm179 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm179 (snoc179 Γ A) B → Tm179 Γ (arr179 A B))
   (app   : (Γ : _) (A B : _) → Tm179 Γ (arr179 A B) → Tm179 Γ A → Tm179 Γ B)
 → Tm179 Γ A

var179 : ∀{Γ A} → Var179 Γ A → Tm179 Γ A;var179
 = λ x Tm179 var179 lam app → var179 _ _ x

lam179 : ∀{Γ A B} → Tm179 (snoc179 Γ A) B → Tm179 Γ (arr179 A B);lam179
 = λ t Tm179 var179 lam179 app → lam179 _ _ _ (t Tm179 var179 lam179 app)

app179 : ∀{Γ A B} → Tm179 Γ (arr179 A B) → Tm179 Γ A → Tm179 Γ B;app179
 = λ t u Tm179 var179 lam179 app179 →
     app179 _ _ _ (t Tm179 var179 lam179 app179) (u Tm179 var179 lam179 app179)

v0179 : ∀{Γ A} → Tm179 (snoc179 Γ A) A;v0179
 = var179 vz179

v1179 : ∀{Γ A B} → Tm179 (snoc179 (snoc179 Γ A) B) A;v1179
 = var179 (vs179 vz179)

v2179 : ∀{Γ A B C} → Tm179 (snoc179 (snoc179 (snoc179 Γ A) B) C) A;v2179
 = var179 (vs179 (vs179 vz179))

v3179 : ∀{Γ A B C D} → Tm179 (snoc179 (snoc179 (snoc179 (snoc179 Γ A) B) C) D) A;v3179
 = var179 (vs179 (vs179 (vs179 vz179)))

v4179 : ∀{Γ A B C D E} → Tm179 (snoc179 (snoc179 (snoc179 (snoc179 (snoc179 Γ A) B) C) D) E) A;v4179
 = var179 (vs179 (vs179 (vs179 (vs179 vz179))))

test179 : ∀{Γ A} → Tm179 Γ (arr179 (arr179 A A) (arr179 A A));test179
  = lam179 (lam179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 v0179)))))))
{-# OPTIONS --type-in-type #-}

Ty180 : Set; Ty180
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι180   : Ty180; ι180 = λ _ ι180 _ → ι180
arr180 : Ty180 → Ty180 → Ty180; arr180 = λ A B Ty180 ι180 arr180 → arr180 (A Ty180 ι180 arr180) (B Ty180 ι180 arr180)

Con180 : Set;Con180
 = (Con180 : Set)
   (nil  : Con180)
   (snoc : Con180 → Ty180 → Con180)
 → Con180

nil180 : Con180;nil180
 = λ Con180 nil180 snoc → nil180

snoc180 : Con180 → Ty180 → Con180;snoc180
 = λ Γ A Con180 nil180 snoc180 → snoc180 (Γ Con180 nil180 snoc180) A

Var180 : Con180 → Ty180 → Set;Var180
 = λ Γ A →
   (Var180 : Con180 → Ty180 → Set)
   (vz  : (Γ : _)(A : _) → Var180 (snoc180 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var180 Γ A → Var180 (snoc180 Γ B) A)
 → Var180 Γ A

vz180 : ∀{Γ A} → Var180 (snoc180 Γ A) A;vz180
 = λ Var180 vz180 vs → vz180 _ _

vs180 : ∀{Γ B A} → Var180 Γ A → Var180 (snoc180 Γ B) A;vs180
 = λ x Var180 vz180 vs180 → vs180 _ _ _ (x Var180 vz180 vs180)

Tm180 : Con180 → Ty180 → Set;Tm180
 = λ Γ A →
   (Tm180    : Con180 → Ty180 → Set)
   (var   : (Γ : _) (A : _) → Var180 Γ A → Tm180 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm180 (snoc180 Γ A) B → Tm180 Γ (arr180 A B))
   (app   : (Γ : _) (A B : _) → Tm180 Γ (arr180 A B) → Tm180 Γ A → Tm180 Γ B)
 → Tm180 Γ A

var180 : ∀{Γ A} → Var180 Γ A → Tm180 Γ A;var180
 = λ x Tm180 var180 lam app → var180 _ _ x

lam180 : ∀{Γ A B} → Tm180 (snoc180 Γ A) B → Tm180 Γ (arr180 A B);lam180
 = λ t Tm180 var180 lam180 app → lam180 _ _ _ (t Tm180 var180 lam180 app)

app180 : ∀{Γ A B} → Tm180 Γ (arr180 A B) → Tm180 Γ A → Tm180 Γ B;app180
 = λ t u Tm180 var180 lam180 app180 →
     app180 _ _ _ (t Tm180 var180 lam180 app180) (u Tm180 var180 lam180 app180)

v0180 : ∀{Γ A} → Tm180 (snoc180 Γ A) A;v0180
 = var180 vz180

v1180 : ∀{Γ A B} → Tm180 (snoc180 (snoc180 Γ A) B) A;v1180
 = var180 (vs180 vz180)

v2180 : ∀{Γ A B C} → Tm180 (snoc180 (snoc180 (snoc180 Γ A) B) C) A;v2180
 = var180 (vs180 (vs180 vz180))

v3180 : ∀{Γ A B C D} → Tm180 (snoc180 (snoc180 (snoc180 (snoc180 Γ A) B) C) D) A;v3180
 = var180 (vs180 (vs180 (vs180 vz180)))

v4180 : ∀{Γ A B C D E} → Tm180 (snoc180 (snoc180 (snoc180 (snoc180 (snoc180 Γ A) B) C) D) E) A;v4180
 = var180 (vs180 (vs180 (vs180 (vs180 vz180))))

test180 : ∀{Γ A} → Tm180 Γ (arr180 (arr180 A A) (arr180 A A));test180
  = lam180 (lam180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 v0180)))))))
{-# OPTIONS --type-in-type #-}

Ty181 : Set; Ty181
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι181   : Ty181; ι181 = λ _ ι181 _ → ι181
arr181 : Ty181 → Ty181 → Ty181; arr181 = λ A B Ty181 ι181 arr181 → arr181 (A Ty181 ι181 arr181) (B Ty181 ι181 arr181)

Con181 : Set;Con181
 = (Con181 : Set)
   (nil  : Con181)
   (snoc : Con181 → Ty181 → Con181)
 → Con181

nil181 : Con181;nil181
 = λ Con181 nil181 snoc → nil181

snoc181 : Con181 → Ty181 → Con181;snoc181
 = λ Γ A Con181 nil181 snoc181 → snoc181 (Γ Con181 nil181 snoc181) A

Var181 : Con181 → Ty181 → Set;Var181
 = λ Γ A →
   (Var181 : Con181 → Ty181 → Set)
   (vz  : (Γ : _)(A : _) → Var181 (snoc181 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var181 Γ A → Var181 (snoc181 Γ B) A)
 → Var181 Γ A

vz181 : ∀{Γ A} → Var181 (snoc181 Γ A) A;vz181
 = λ Var181 vz181 vs → vz181 _ _

vs181 : ∀{Γ B A} → Var181 Γ A → Var181 (snoc181 Γ B) A;vs181
 = λ x Var181 vz181 vs181 → vs181 _ _ _ (x Var181 vz181 vs181)

Tm181 : Con181 → Ty181 → Set;Tm181
 = λ Γ A →
   (Tm181    : Con181 → Ty181 → Set)
   (var   : (Γ : _) (A : _) → Var181 Γ A → Tm181 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm181 (snoc181 Γ A) B → Tm181 Γ (arr181 A B))
   (app   : (Γ : _) (A B : _) → Tm181 Γ (arr181 A B) → Tm181 Γ A → Tm181 Γ B)
 → Tm181 Γ A

var181 : ∀{Γ A} → Var181 Γ A → Tm181 Γ A;var181
 = λ x Tm181 var181 lam app → var181 _ _ x

lam181 : ∀{Γ A B} → Tm181 (snoc181 Γ A) B → Tm181 Γ (arr181 A B);lam181
 = λ t Tm181 var181 lam181 app → lam181 _ _ _ (t Tm181 var181 lam181 app)

app181 : ∀{Γ A B} → Tm181 Γ (arr181 A B) → Tm181 Γ A → Tm181 Γ B;app181
 = λ t u Tm181 var181 lam181 app181 →
     app181 _ _ _ (t Tm181 var181 lam181 app181) (u Tm181 var181 lam181 app181)

v0181 : ∀{Γ A} → Tm181 (snoc181 Γ A) A;v0181
 = var181 vz181

v1181 : ∀{Γ A B} → Tm181 (snoc181 (snoc181 Γ A) B) A;v1181
 = var181 (vs181 vz181)

v2181 : ∀{Γ A B C} → Tm181 (snoc181 (snoc181 (snoc181 Γ A) B) C) A;v2181
 = var181 (vs181 (vs181 vz181))

v3181 : ∀{Γ A B C D} → Tm181 (snoc181 (snoc181 (snoc181 (snoc181 Γ A) B) C) D) A;v3181
 = var181 (vs181 (vs181 (vs181 vz181)))

v4181 : ∀{Γ A B C D E} → Tm181 (snoc181 (snoc181 (snoc181 (snoc181 (snoc181 Γ A) B) C) D) E) A;v4181
 = var181 (vs181 (vs181 (vs181 (vs181 vz181))))

test181 : ∀{Γ A} → Tm181 Γ (arr181 (arr181 A A) (arr181 A A));test181
  = lam181 (lam181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 v0181)))))))
{-# OPTIONS --type-in-type #-}

Ty182 : Set; Ty182
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι182   : Ty182; ι182 = λ _ ι182 _ → ι182
arr182 : Ty182 → Ty182 → Ty182; arr182 = λ A B Ty182 ι182 arr182 → arr182 (A Ty182 ι182 arr182) (B Ty182 ι182 arr182)

Con182 : Set;Con182
 = (Con182 : Set)
   (nil  : Con182)
   (snoc : Con182 → Ty182 → Con182)
 → Con182

nil182 : Con182;nil182
 = λ Con182 nil182 snoc → nil182

snoc182 : Con182 → Ty182 → Con182;snoc182
 = λ Γ A Con182 nil182 snoc182 → snoc182 (Γ Con182 nil182 snoc182) A

Var182 : Con182 → Ty182 → Set;Var182
 = λ Γ A →
   (Var182 : Con182 → Ty182 → Set)
   (vz  : (Γ : _)(A : _) → Var182 (snoc182 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var182 Γ A → Var182 (snoc182 Γ B) A)
 → Var182 Γ A

vz182 : ∀{Γ A} → Var182 (snoc182 Γ A) A;vz182
 = λ Var182 vz182 vs → vz182 _ _

vs182 : ∀{Γ B A} → Var182 Γ A → Var182 (snoc182 Γ B) A;vs182
 = λ x Var182 vz182 vs182 → vs182 _ _ _ (x Var182 vz182 vs182)

Tm182 : Con182 → Ty182 → Set;Tm182
 = λ Γ A →
   (Tm182    : Con182 → Ty182 → Set)
   (var   : (Γ : _) (A : _) → Var182 Γ A → Tm182 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm182 (snoc182 Γ A) B → Tm182 Γ (arr182 A B))
   (app   : (Γ : _) (A B : _) → Tm182 Γ (arr182 A B) → Tm182 Γ A → Tm182 Γ B)
 → Tm182 Γ A

var182 : ∀{Γ A} → Var182 Γ A → Tm182 Γ A;var182
 = λ x Tm182 var182 lam app → var182 _ _ x

lam182 : ∀{Γ A B} → Tm182 (snoc182 Γ A) B → Tm182 Γ (arr182 A B);lam182
 = λ t Tm182 var182 lam182 app → lam182 _ _ _ (t Tm182 var182 lam182 app)

app182 : ∀{Γ A B} → Tm182 Γ (arr182 A B) → Tm182 Γ A → Tm182 Γ B;app182
 = λ t u Tm182 var182 lam182 app182 →
     app182 _ _ _ (t Tm182 var182 lam182 app182) (u Tm182 var182 lam182 app182)

v0182 : ∀{Γ A} → Tm182 (snoc182 Γ A) A;v0182
 = var182 vz182

v1182 : ∀{Γ A B} → Tm182 (snoc182 (snoc182 Γ A) B) A;v1182
 = var182 (vs182 vz182)

v2182 : ∀{Γ A B C} → Tm182 (snoc182 (snoc182 (snoc182 Γ A) B) C) A;v2182
 = var182 (vs182 (vs182 vz182))

v3182 : ∀{Γ A B C D} → Tm182 (snoc182 (snoc182 (snoc182 (snoc182 Γ A) B) C) D) A;v3182
 = var182 (vs182 (vs182 (vs182 vz182)))

v4182 : ∀{Γ A B C D E} → Tm182 (snoc182 (snoc182 (snoc182 (snoc182 (snoc182 Γ A) B) C) D) E) A;v4182
 = var182 (vs182 (vs182 (vs182 (vs182 vz182))))

test182 : ∀{Γ A} → Tm182 Γ (arr182 (arr182 A A) (arr182 A A));test182
  = lam182 (lam182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 v0182)))))))
{-# OPTIONS --type-in-type #-}

Ty183 : Set; Ty183
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι183   : Ty183; ι183 = λ _ ι183 _ → ι183
arr183 : Ty183 → Ty183 → Ty183; arr183 = λ A B Ty183 ι183 arr183 → arr183 (A Ty183 ι183 arr183) (B Ty183 ι183 arr183)

Con183 : Set;Con183
 = (Con183 : Set)
   (nil  : Con183)
   (snoc : Con183 → Ty183 → Con183)
 → Con183

nil183 : Con183;nil183
 = λ Con183 nil183 snoc → nil183

snoc183 : Con183 → Ty183 → Con183;snoc183
 = λ Γ A Con183 nil183 snoc183 → snoc183 (Γ Con183 nil183 snoc183) A

Var183 : Con183 → Ty183 → Set;Var183
 = λ Γ A →
   (Var183 : Con183 → Ty183 → Set)
   (vz  : (Γ : _)(A : _) → Var183 (snoc183 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var183 Γ A → Var183 (snoc183 Γ B) A)
 → Var183 Γ A

vz183 : ∀{Γ A} → Var183 (snoc183 Γ A) A;vz183
 = λ Var183 vz183 vs → vz183 _ _

vs183 : ∀{Γ B A} → Var183 Γ A → Var183 (snoc183 Γ B) A;vs183
 = λ x Var183 vz183 vs183 → vs183 _ _ _ (x Var183 vz183 vs183)

Tm183 : Con183 → Ty183 → Set;Tm183
 = λ Γ A →
   (Tm183    : Con183 → Ty183 → Set)
   (var   : (Γ : _) (A : _) → Var183 Γ A → Tm183 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm183 (snoc183 Γ A) B → Tm183 Γ (arr183 A B))
   (app   : (Γ : _) (A B : _) → Tm183 Γ (arr183 A B) → Tm183 Γ A → Tm183 Γ B)
 → Tm183 Γ A

var183 : ∀{Γ A} → Var183 Γ A → Tm183 Γ A;var183
 = λ x Tm183 var183 lam app → var183 _ _ x

lam183 : ∀{Γ A B} → Tm183 (snoc183 Γ A) B → Tm183 Γ (arr183 A B);lam183
 = λ t Tm183 var183 lam183 app → lam183 _ _ _ (t Tm183 var183 lam183 app)

app183 : ∀{Γ A B} → Tm183 Γ (arr183 A B) → Tm183 Γ A → Tm183 Γ B;app183
 = λ t u Tm183 var183 lam183 app183 →
     app183 _ _ _ (t Tm183 var183 lam183 app183) (u Tm183 var183 lam183 app183)

v0183 : ∀{Γ A} → Tm183 (snoc183 Γ A) A;v0183
 = var183 vz183

v1183 : ∀{Γ A B} → Tm183 (snoc183 (snoc183 Γ A) B) A;v1183
 = var183 (vs183 vz183)

v2183 : ∀{Γ A B C} → Tm183 (snoc183 (snoc183 (snoc183 Γ A) B) C) A;v2183
 = var183 (vs183 (vs183 vz183))

v3183 : ∀{Γ A B C D} → Tm183 (snoc183 (snoc183 (snoc183 (snoc183 Γ A) B) C) D) A;v3183
 = var183 (vs183 (vs183 (vs183 vz183)))

v4183 : ∀{Γ A B C D E} → Tm183 (snoc183 (snoc183 (snoc183 (snoc183 (snoc183 Γ A) B) C) D) E) A;v4183
 = var183 (vs183 (vs183 (vs183 (vs183 vz183))))

test183 : ∀{Γ A} → Tm183 Γ (arr183 (arr183 A A) (arr183 A A));test183
  = lam183 (lam183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 v0183)))))))
{-# OPTIONS --type-in-type #-}

Ty184 : Set; Ty184
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι184   : Ty184; ι184 = λ _ ι184 _ → ι184
arr184 : Ty184 → Ty184 → Ty184; arr184 = λ A B Ty184 ι184 arr184 → arr184 (A Ty184 ι184 arr184) (B Ty184 ι184 arr184)

Con184 : Set;Con184
 = (Con184 : Set)
   (nil  : Con184)
   (snoc : Con184 → Ty184 → Con184)
 → Con184

nil184 : Con184;nil184
 = λ Con184 nil184 snoc → nil184

snoc184 : Con184 → Ty184 → Con184;snoc184
 = λ Γ A Con184 nil184 snoc184 → snoc184 (Γ Con184 nil184 snoc184) A

Var184 : Con184 → Ty184 → Set;Var184
 = λ Γ A →
   (Var184 : Con184 → Ty184 → Set)
   (vz  : (Γ : _)(A : _) → Var184 (snoc184 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var184 Γ A → Var184 (snoc184 Γ B) A)
 → Var184 Γ A

vz184 : ∀{Γ A} → Var184 (snoc184 Γ A) A;vz184
 = λ Var184 vz184 vs → vz184 _ _

vs184 : ∀{Γ B A} → Var184 Γ A → Var184 (snoc184 Γ B) A;vs184
 = λ x Var184 vz184 vs184 → vs184 _ _ _ (x Var184 vz184 vs184)

Tm184 : Con184 → Ty184 → Set;Tm184
 = λ Γ A →
   (Tm184    : Con184 → Ty184 → Set)
   (var   : (Γ : _) (A : _) → Var184 Γ A → Tm184 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm184 (snoc184 Γ A) B → Tm184 Γ (arr184 A B))
   (app   : (Γ : _) (A B : _) → Tm184 Γ (arr184 A B) → Tm184 Γ A → Tm184 Γ B)
 → Tm184 Γ A

var184 : ∀{Γ A} → Var184 Γ A → Tm184 Γ A;var184
 = λ x Tm184 var184 lam app → var184 _ _ x

lam184 : ∀{Γ A B} → Tm184 (snoc184 Γ A) B → Tm184 Γ (arr184 A B);lam184
 = λ t Tm184 var184 lam184 app → lam184 _ _ _ (t Tm184 var184 lam184 app)

app184 : ∀{Γ A B} → Tm184 Γ (arr184 A B) → Tm184 Γ A → Tm184 Γ B;app184
 = λ t u Tm184 var184 lam184 app184 →
     app184 _ _ _ (t Tm184 var184 lam184 app184) (u Tm184 var184 lam184 app184)

v0184 : ∀{Γ A} → Tm184 (snoc184 Γ A) A;v0184
 = var184 vz184

v1184 : ∀{Γ A B} → Tm184 (snoc184 (snoc184 Γ A) B) A;v1184
 = var184 (vs184 vz184)

v2184 : ∀{Γ A B C} → Tm184 (snoc184 (snoc184 (snoc184 Γ A) B) C) A;v2184
 = var184 (vs184 (vs184 vz184))

v3184 : ∀{Γ A B C D} → Tm184 (snoc184 (snoc184 (snoc184 (snoc184 Γ A) B) C) D) A;v3184
 = var184 (vs184 (vs184 (vs184 vz184)))

v4184 : ∀{Γ A B C D E} → Tm184 (snoc184 (snoc184 (snoc184 (snoc184 (snoc184 Γ A) B) C) D) E) A;v4184
 = var184 (vs184 (vs184 (vs184 (vs184 vz184))))

test184 : ∀{Γ A} → Tm184 Γ (arr184 (arr184 A A) (arr184 A A));test184
  = lam184 (lam184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 v0184)))))))
{-# OPTIONS --type-in-type #-}

Ty185 : Set; Ty185
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι185   : Ty185; ι185 = λ _ ι185 _ → ι185
arr185 : Ty185 → Ty185 → Ty185; arr185 = λ A B Ty185 ι185 arr185 → arr185 (A Ty185 ι185 arr185) (B Ty185 ι185 arr185)

Con185 : Set;Con185
 = (Con185 : Set)
   (nil  : Con185)
   (snoc : Con185 → Ty185 → Con185)
 → Con185

nil185 : Con185;nil185
 = λ Con185 nil185 snoc → nil185

snoc185 : Con185 → Ty185 → Con185;snoc185
 = λ Γ A Con185 nil185 snoc185 → snoc185 (Γ Con185 nil185 snoc185) A

Var185 : Con185 → Ty185 → Set;Var185
 = λ Γ A →
   (Var185 : Con185 → Ty185 → Set)
   (vz  : (Γ : _)(A : _) → Var185 (snoc185 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var185 Γ A → Var185 (snoc185 Γ B) A)
 → Var185 Γ A

vz185 : ∀{Γ A} → Var185 (snoc185 Γ A) A;vz185
 = λ Var185 vz185 vs → vz185 _ _

vs185 : ∀{Γ B A} → Var185 Γ A → Var185 (snoc185 Γ B) A;vs185
 = λ x Var185 vz185 vs185 → vs185 _ _ _ (x Var185 vz185 vs185)

Tm185 : Con185 → Ty185 → Set;Tm185
 = λ Γ A →
   (Tm185    : Con185 → Ty185 → Set)
   (var   : (Γ : _) (A : _) → Var185 Γ A → Tm185 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm185 (snoc185 Γ A) B → Tm185 Γ (arr185 A B))
   (app   : (Γ : _) (A B : _) → Tm185 Γ (arr185 A B) → Tm185 Γ A → Tm185 Γ B)
 → Tm185 Γ A

var185 : ∀{Γ A} → Var185 Γ A → Tm185 Γ A;var185
 = λ x Tm185 var185 lam app → var185 _ _ x

lam185 : ∀{Γ A B} → Tm185 (snoc185 Γ A) B → Tm185 Γ (arr185 A B);lam185
 = λ t Tm185 var185 lam185 app → lam185 _ _ _ (t Tm185 var185 lam185 app)

app185 : ∀{Γ A B} → Tm185 Γ (arr185 A B) → Tm185 Γ A → Tm185 Γ B;app185
 = λ t u Tm185 var185 lam185 app185 →
     app185 _ _ _ (t Tm185 var185 lam185 app185) (u Tm185 var185 lam185 app185)

v0185 : ∀{Γ A} → Tm185 (snoc185 Γ A) A;v0185
 = var185 vz185

v1185 : ∀{Γ A B} → Tm185 (snoc185 (snoc185 Γ A) B) A;v1185
 = var185 (vs185 vz185)

v2185 : ∀{Γ A B C} → Tm185 (snoc185 (snoc185 (snoc185 Γ A) B) C) A;v2185
 = var185 (vs185 (vs185 vz185))

v3185 : ∀{Γ A B C D} → Tm185 (snoc185 (snoc185 (snoc185 (snoc185 Γ A) B) C) D) A;v3185
 = var185 (vs185 (vs185 (vs185 vz185)))

v4185 : ∀{Γ A B C D E} → Tm185 (snoc185 (snoc185 (snoc185 (snoc185 (snoc185 Γ A) B) C) D) E) A;v4185
 = var185 (vs185 (vs185 (vs185 (vs185 vz185))))

test185 : ∀{Γ A} → Tm185 Γ (arr185 (arr185 A A) (arr185 A A));test185
  = lam185 (lam185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 v0185)))))))
{-# OPTIONS --type-in-type #-}

Ty186 : Set; Ty186
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι186   : Ty186; ι186 = λ _ ι186 _ → ι186
arr186 : Ty186 → Ty186 → Ty186; arr186 = λ A B Ty186 ι186 arr186 → arr186 (A Ty186 ι186 arr186) (B Ty186 ι186 arr186)

Con186 : Set;Con186
 = (Con186 : Set)
   (nil  : Con186)
   (snoc : Con186 → Ty186 → Con186)
 → Con186

nil186 : Con186;nil186
 = λ Con186 nil186 snoc → nil186

snoc186 : Con186 → Ty186 → Con186;snoc186
 = λ Γ A Con186 nil186 snoc186 → snoc186 (Γ Con186 nil186 snoc186) A

Var186 : Con186 → Ty186 → Set;Var186
 = λ Γ A →
   (Var186 : Con186 → Ty186 → Set)
   (vz  : (Γ : _)(A : _) → Var186 (snoc186 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var186 Γ A → Var186 (snoc186 Γ B) A)
 → Var186 Γ A

vz186 : ∀{Γ A} → Var186 (snoc186 Γ A) A;vz186
 = λ Var186 vz186 vs → vz186 _ _

vs186 : ∀{Γ B A} → Var186 Γ A → Var186 (snoc186 Γ B) A;vs186
 = λ x Var186 vz186 vs186 → vs186 _ _ _ (x Var186 vz186 vs186)

Tm186 : Con186 → Ty186 → Set;Tm186
 = λ Γ A →
   (Tm186    : Con186 → Ty186 → Set)
   (var   : (Γ : _) (A : _) → Var186 Γ A → Tm186 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm186 (snoc186 Γ A) B → Tm186 Γ (arr186 A B))
   (app   : (Γ : _) (A B : _) → Tm186 Γ (arr186 A B) → Tm186 Γ A → Tm186 Γ B)
 → Tm186 Γ A

var186 : ∀{Γ A} → Var186 Γ A → Tm186 Γ A;var186
 = λ x Tm186 var186 lam app → var186 _ _ x

lam186 : ∀{Γ A B} → Tm186 (snoc186 Γ A) B → Tm186 Γ (arr186 A B);lam186
 = λ t Tm186 var186 lam186 app → lam186 _ _ _ (t Tm186 var186 lam186 app)

app186 : ∀{Γ A B} → Tm186 Γ (arr186 A B) → Tm186 Γ A → Tm186 Γ B;app186
 = λ t u Tm186 var186 lam186 app186 →
     app186 _ _ _ (t Tm186 var186 lam186 app186) (u Tm186 var186 lam186 app186)

v0186 : ∀{Γ A} → Tm186 (snoc186 Γ A) A;v0186
 = var186 vz186

v1186 : ∀{Γ A B} → Tm186 (snoc186 (snoc186 Γ A) B) A;v1186
 = var186 (vs186 vz186)

v2186 : ∀{Γ A B C} → Tm186 (snoc186 (snoc186 (snoc186 Γ A) B) C) A;v2186
 = var186 (vs186 (vs186 vz186))

v3186 : ∀{Γ A B C D} → Tm186 (snoc186 (snoc186 (snoc186 (snoc186 Γ A) B) C) D) A;v3186
 = var186 (vs186 (vs186 (vs186 vz186)))

v4186 : ∀{Γ A B C D E} → Tm186 (snoc186 (snoc186 (snoc186 (snoc186 (snoc186 Γ A) B) C) D) E) A;v4186
 = var186 (vs186 (vs186 (vs186 (vs186 vz186))))

test186 : ∀{Γ A} → Tm186 Γ (arr186 (arr186 A A) (arr186 A A));test186
  = lam186 (lam186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 v0186)))))))
{-# OPTIONS --type-in-type #-}

Ty187 : Set; Ty187
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι187   : Ty187; ι187 = λ _ ι187 _ → ι187
arr187 : Ty187 → Ty187 → Ty187; arr187 = λ A B Ty187 ι187 arr187 → arr187 (A Ty187 ι187 arr187) (B Ty187 ι187 arr187)

Con187 : Set;Con187
 = (Con187 : Set)
   (nil  : Con187)
   (snoc : Con187 → Ty187 → Con187)
 → Con187

nil187 : Con187;nil187
 = λ Con187 nil187 snoc → nil187

snoc187 : Con187 → Ty187 → Con187;snoc187
 = λ Γ A Con187 nil187 snoc187 → snoc187 (Γ Con187 nil187 snoc187) A

Var187 : Con187 → Ty187 → Set;Var187
 = λ Γ A →
   (Var187 : Con187 → Ty187 → Set)
   (vz  : (Γ : _)(A : _) → Var187 (snoc187 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var187 Γ A → Var187 (snoc187 Γ B) A)
 → Var187 Γ A

vz187 : ∀{Γ A} → Var187 (snoc187 Γ A) A;vz187
 = λ Var187 vz187 vs → vz187 _ _

vs187 : ∀{Γ B A} → Var187 Γ A → Var187 (snoc187 Γ B) A;vs187
 = λ x Var187 vz187 vs187 → vs187 _ _ _ (x Var187 vz187 vs187)

Tm187 : Con187 → Ty187 → Set;Tm187
 = λ Γ A →
   (Tm187    : Con187 → Ty187 → Set)
   (var   : (Γ : _) (A : _) → Var187 Γ A → Tm187 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm187 (snoc187 Γ A) B → Tm187 Γ (arr187 A B))
   (app   : (Γ : _) (A B : _) → Tm187 Γ (arr187 A B) → Tm187 Γ A → Tm187 Γ B)
 → Tm187 Γ A

var187 : ∀{Γ A} → Var187 Γ A → Tm187 Γ A;var187
 = λ x Tm187 var187 lam app → var187 _ _ x

lam187 : ∀{Γ A B} → Tm187 (snoc187 Γ A) B → Tm187 Γ (arr187 A B);lam187
 = λ t Tm187 var187 lam187 app → lam187 _ _ _ (t Tm187 var187 lam187 app)

app187 : ∀{Γ A B} → Tm187 Γ (arr187 A B) → Tm187 Γ A → Tm187 Γ B;app187
 = λ t u Tm187 var187 lam187 app187 →
     app187 _ _ _ (t Tm187 var187 lam187 app187) (u Tm187 var187 lam187 app187)

v0187 : ∀{Γ A} → Tm187 (snoc187 Γ A) A;v0187
 = var187 vz187

v1187 : ∀{Γ A B} → Tm187 (snoc187 (snoc187 Γ A) B) A;v1187
 = var187 (vs187 vz187)

v2187 : ∀{Γ A B C} → Tm187 (snoc187 (snoc187 (snoc187 Γ A) B) C) A;v2187
 = var187 (vs187 (vs187 vz187))

v3187 : ∀{Γ A B C D} → Tm187 (snoc187 (snoc187 (snoc187 (snoc187 Γ A) B) C) D) A;v3187
 = var187 (vs187 (vs187 (vs187 vz187)))

v4187 : ∀{Γ A B C D E} → Tm187 (snoc187 (snoc187 (snoc187 (snoc187 (snoc187 Γ A) B) C) D) E) A;v4187
 = var187 (vs187 (vs187 (vs187 (vs187 vz187))))

test187 : ∀{Γ A} → Tm187 Γ (arr187 (arr187 A A) (arr187 A A));test187
  = lam187 (lam187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 v0187)))))))
{-# OPTIONS --type-in-type #-}

Ty188 : Set; Ty188
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι188   : Ty188; ι188 = λ _ ι188 _ → ι188
arr188 : Ty188 → Ty188 → Ty188; arr188 = λ A B Ty188 ι188 arr188 → arr188 (A Ty188 ι188 arr188) (B Ty188 ι188 arr188)

Con188 : Set;Con188
 = (Con188 : Set)
   (nil  : Con188)
   (snoc : Con188 → Ty188 → Con188)
 → Con188

nil188 : Con188;nil188
 = λ Con188 nil188 snoc → nil188

snoc188 : Con188 → Ty188 → Con188;snoc188
 = λ Γ A Con188 nil188 snoc188 → snoc188 (Γ Con188 nil188 snoc188) A

Var188 : Con188 → Ty188 → Set;Var188
 = λ Γ A →
   (Var188 : Con188 → Ty188 → Set)
   (vz  : (Γ : _)(A : _) → Var188 (snoc188 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var188 Γ A → Var188 (snoc188 Γ B) A)
 → Var188 Γ A

vz188 : ∀{Γ A} → Var188 (snoc188 Γ A) A;vz188
 = λ Var188 vz188 vs → vz188 _ _

vs188 : ∀{Γ B A} → Var188 Γ A → Var188 (snoc188 Γ B) A;vs188
 = λ x Var188 vz188 vs188 → vs188 _ _ _ (x Var188 vz188 vs188)

Tm188 : Con188 → Ty188 → Set;Tm188
 = λ Γ A →
   (Tm188    : Con188 → Ty188 → Set)
   (var   : (Γ : _) (A : _) → Var188 Γ A → Tm188 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm188 (snoc188 Γ A) B → Tm188 Γ (arr188 A B))
   (app   : (Γ : _) (A B : _) → Tm188 Γ (arr188 A B) → Tm188 Γ A → Tm188 Γ B)
 → Tm188 Γ A

var188 : ∀{Γ A} → Var188 Γ A → Tm188 Γ A;var188
 = λ x Tm188 var188 lam app → var188 _ _ x

lam188 : ∀{Γ A B} → Tm188 (snoc188 Γ A) B → Tm188 Γ (arr188 A B);lam188
 = λ t Tm188 var188 lam188 app → lam188 _ _ _ (t Tm188 var188 lam188 app)

app188 : ∀{Γ A B} → Tm188 Γ (arr188 A B) → Tm188 Γ A → Tm188 Γ B;app188
 = λ t u Tm188 var188 lam188 app188 →
     app188 _ _ _ (t Tm188 var188 lam188 app188) (u Tm188 var188 lam188 app188)

v0188 : ∀{Γ A} → Tm188 (snoc188 Γ A) A;v0188
 = var188 vz188

v1188 : ∀{Γ A B} → Tm188 (snoc188 (snoc188 Γ A) B) A;v1188
 = var188 (vs188 vz188)

v2188 : ∀{Γ A B C} → Tm188 (snoc188 (snoc188 (snoc188 Γ A) B) C) A;v2188
 = var188 (vs188 (vs188 vz188))

v3188 : ∀{Γ A B C D} → Tm188 (snoc188 (snoc188 (snoc188 (snoc188 Γ A) B) C) D) A;v3188
 = var188 (vs188 (vs188 (vs188 vz188)))

v4188 : ∀{Γ A B C D E} → Tm188 (snoc188 (snoc188 (snoc188 (snoc188 (snoc188 Γ A) B) C) D) E) A;v4188
 = var188 (vs188 (vs188 (vs188 (vs188 vz188))))

test188 : ∀{Γ A} → Tm188 Γ (arr188 (arr188 A A) (arr188 A A));test188
  = lam188 (lam188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 v0188)))))))
{-# OPTIONS --type-in-type #-}

Ty189 : Set; Ty189
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι189   : Ty189; ι189 = λ _ ι189 _ → ι189
arr189 : Ty189 → Ty189 → Ty189; arr189 = λ A B Ty189 ι189 arr189 → arr189 (A Ty189 ι189 arr189) (B Ty189 ι189 arr189)

Con189 : Set;Con189
 = (Con189 : Set)
   (nil  : Con189)
   (snoc : Con189 → Ty189 → Con189)
 → Con189

nil189 : Con189;nil189
 = λ Con189 nil189 snoc → nil189

snoc189 : Con189 → Ty189 → Con189;snoc189
 = λ Γ A Con189 nil189 snoc189 → snoc189 (Γ Con189 nil189 snoc189) A

Var189 : Con189 → Ty189 → Set;Var189
 = λ Γ A →
   (Var189 : Con189 → Ty189 → Set)
   (vz  : (Γ : _)(A : _) → Var189 (snoc189 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var189 Γ A → Var189 (snoc189 Γ B) A)
 → Var189 Γ A

vz189 : ∀{Γ A} → Var189 (snoc189 Γ A) A;vz189
 = λ Var189 vz189 vs → vz189 _ _

vs189 : ∀{Γ B A} → Var189 Γ A → Var189 (snoc189 Γ B) A;vs189
 = λ x Var189 vz189 vs189 → vs189 _ _ _ (x Var189 vz189 vs189)

Tm189 : Con189 → Ty189 → Set;Tm189
 = λ Γ A →
   (Tm189    : Con189 → Ty189 → Set)
   (var   : (Γ : _) (A : _) → Var189 Γ A → Tm189 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm189 (snoc189 Γ A) B → Tm189 Γ (arr189 A B))
   (app   : (Γ : _) (A B : _) → Tm189 Γ (arr189 A B) → Tm189 Γ A → Tm189 Γ B)
 → Tm189 Γ A

var189 : ∀{Γ A} → Var189 Γ A → Tm189 Γ A;var189
 = λ x Tm189 var189 lam app → var189 _ _ x

lam189 : ∀{Γ A B} → Tm189 (snoc189 Γ A) B → Tm189 Γ (arr189 A B);lam189
 = λ t Tm189 var189 lam189 app → lam189 _ _ _ (t Tm189 var189 lam189 app)

app189 : ∀{Γ A B} → Tm189 Γ (arr189 A B) → Tm189 Γ A → Tm189 Γ B;app189
 = λ t u Tm189 var189 lam189 app189 →
     app189 _ _ _ (t Tm189 var189 lam189 app189) (u Tm189 var189 lam189 app189)

v0189 : ∀{Γ A} → Tm189 (snoc189 Γ A) A;v0189
 = var189 vz189

v1189 : ∀{Γ A B} → Tm189 (snoc189 (snoc189 Γ A) B) A;v1189
 = var189 (vs189 vz189)

v2189 : ∀{Γ A B C} → Tm189 (snoc189 (snoc189 (snoc189 Γ A) B) C) A;v2189
 = var189 (vs189 (vs189 vz189))

v3189 : ∀{Γ A B C D} → Tm189 (snoc189 (snoc189 (snoc189 (snoc189 Γ A) B) C) D) A;v3189
 = var189 (vs189 (vs189 (vs189 vz189)))

v4189 : ∀{Γ A B C D E} → Tm189 (snoc189 (snoc189 (snoc189 (snoc189 (snoc189 Γ A) B) C) D) E) A;v4189
 = var189 (vs189 (vs189 (vs189 (vs189 vz189))))

test189 : ∀{Γ A} → Tm189 Γ (arr189 (arr189 A A) (arr189 A A));test189
  = lam189 (lam189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 v0189)))))))
{-# OPTIONS --type-in-type #-}

Ty190 : Set; Ty190
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι190   : Ty190; ι190 = λ _ ι190 _ → ι190
arr190 : Ty190 → Ty190 → Ty190; arr190 = λ A B Ty190 ι190 arr190 → arr190 (A Ty190 ι190 arr190) (B Ty190 ι190 arr190)

Con190 : Set;Con190
 = (Con190 : Set)
   (nil  : Con190)
   (snoc : Con190 → Ty190 → Con190)
 → Con190

nil190 : Con190;nil190
 = λ Con190 nil190 snoc → nil190

snoc190 : Con190 → Ty190 → Con190;snoc190
 = λ Γ A Con190 nil190 snoc190 → snoc190 (Γ Con190 nil190 snoc190) A

Var190 : Con190 → Ty190 → Set;Var190
 = λ Γ A →
   (Var190 : Con190 → Ty190 → Set)
   (vz  : (Γ : _)(A : _) → Var190 (snoc190 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var190 Γ A → Var190 (snoc190 Γ B) A)
 → Var190 Γ A

vz190 : ∀{Γ A} → Var190 (snoc190 Γ A) A;vz190
 = λ Var190 vz190 vs → vz190 _ _

vs190 : ∀{Γ B A} → Var190 Γ A → Var190 (snoc190 Γ B) A;vs190
 = λ x Var190 vz190 vs190 → vs190 _ _ _ (x Var190 vz190 vs190)

Tm190 : Con190 → Ty190 → Set;Tm190
 = λ Γ A →
   (Tm190    : Con190 → Ty190 → Set)
   (var   : (Γ : _) (A : _) → Var190 Γ A → Tm190 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm190 (snoc190 Γ A) B → Tm190 Γ (arr190 A B))
   (app   : (Γ : _) (A B : _) → Tm190 Γ (arr190 A B) → Tm190 Γ A → Tm190 Γ B)
 → Tm190 Γ A

var190 : ∀{Γ A} → Var190 Γ A → Tm190 Γ A;var190
 = λ x Tm190 var190 lam app → var190 _ _ x

lam190 : ∀{Γ A B} → Tm190 (snoc190 Γ A) B → Tm190 Γ (arr190 A B);lam190
 = λ t Tm190 var190 lam190 app → lam190 _ _ _ (t Tm190 var190 lam190 app)

app190 : ∀{Γ A B} → Tm190 Γ (arr190 A B) → Tm190 Γ A → Tm190 Γ B;app190
 = λ t u Tm190 var190 lam190 app190 →
     app190 _ _ _ (t Tm190 var190 lam190 app190) (u Tm190 var190 lam190 app190)

v0190 : ∀{Γ A} → Tm190 (snoc190 Γ A) A;v0190
 = var190 vz190

v1190 : ∀{Γ A B} → Tm190 (snoc190 (snoc190 Γ A) B) A;v1190
 = var190 (vs190 vz190)

v2190 : ∀{Γ A B C} → Tm190 (snoc190 (snoc190 (snoc190 Γ A) B) C) A;v2190
 = var190 (vs190 (vs190 vz190))

v3190 : ∀{Γ A B C D} → Tm190 (snoc190 (snoc190 (snoc190 (snoc190 Γ A) B) C) D) A;v3190
 = var190 (vs190 (vs190 (vs190 vz190)))

v4190 : ∀{Γ A B C D E} → Tm190 (snoc190 (snoc190 (snoc190 (snoc190 (snoc190 Γ A) B) C) D) E) A;v4190
 = var190 (vs190 (vs190 (vs190 (vs190 vz190))))

test190 : ∀{Γ A} → Tm190 Γ (arr190 (arr190 A A) (arr190 A A));test190
  = lam190 (lam190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 v0190)))))))
{-# OPTIONS --type-in-type #-}

Ty191 : Set; Ty191
 = (Ty  : Set)
   (ι   : Ty)
   (arr : Ty → Ty → Ty)
 → Ty

ι191   : Ty191; ι191 = λ _ ι191 _ → ι191
arr191 : Ty191 → Ty191 → Ty191; arr191 = λ A B Ty191 ι191 arr191 → arr191 (A Ty191 ι191 arr191) (B Ty191 ι191 arr191)

Con191 : Set;Con191
 = (Con191 : Set)
   (nil  : Con191)
   (snoc : Con191 → Ty191 → Con191)
 → Con191

nil191 : Con191;nil191
 = λ Con191 nil191 snoc → nil191

snoc191 : Con191 → Ty191 → Con191;snoc191
 = λ Γ A Con191 nil191 snoc191 → snoc191 (Γ Con191 nil191 snoc191) A

Var191 : Con191 → Ty191 → Set;Var191
 = λ Γ A →
   (Var191 : Con191 → Ty191 → Set)
   (vz  : (Γ : _)(A : _) → Var191 (snoc191 Γ A) A)
   (vs  : (Γ : _)(B A : _) → Var191 Γ A → Var191 (snoc191 Γ B) A)
 → Var191 Γ A

vz191 : ∀{Γ A} → Var191 (snoc191 Γ A) A;vz191
 = λ Var191 vz191 vs → vz191 _ _

vs191 : ∀{Γ B A} → Var191 Γ A → Var191 (snoc191 Γ B) A;vs191
 = λ x Var191 vz191 vs191 → vs191 _ _ _ (x Var191 vz191 vs191)

Tm191 : Con191 → Ty191 → Set;Tm191
 = λ Γ A →
   (Tm191    : Con191 → Ty191 → Set)
   (var   : (Γ : _) (A : _) → Var191 Γ A → Tm191 Γ A)
   (lam   : (Γ : _) (A B : _) → Tm191 (snoc191 Γ A) B → Tm191 Γ (arr191 A B))
   (app   : (Γ : _) (A B : _) → Tm191 Γ (arr191 A B) → Tm191 Γ A → Tm191 Γ B)
 → Tm191 Γ A

var191 : ∀{Γ A} → Var191 Γ A → Tm191 Γ A;var191
 = λ x Tm191 var191 lam app → var191 _ _ x

lam191 : ∀{Γ A B} → Tm191 (snoc191 Γ A) B → Tm191 Γ (arr191 A B);lam191
 = λ t Tm191 var191 lam191 app → lam191 _ _ _ (t Tm191 var191 lam191 app)

app191 : ∀{Γ A B} → Tm191 Γ (arr191 A B) → Tm191 Γ A → Tm191 Γ B;app191
 = λ t u Tm191 var191 lam191 app191 →
     app191 _ _ _ (t Tm191 var191 lam191 app191) (u Tm191 var191 lam191 app191)

v0191 : ∀{Γ A} → Tm191 (snoc191 Γ A) A;v0191
 = var191 vz191

v1191 : ∀{Γ A B} → Tm191 (snoc191 (snoc191 Γ A) B) A;v1191
 = var191 (vs191 vz191)

v2191 : ∀{Γ A B C} → Tm191 (snoc191 (snoc191 (snoc191 Γ A) B) C) A;v2191
 = var191 (vs191 (vs191 vz191))

v3191 : ∀{Γ A B C D} → Tm191 (snoc191 (snoc191 (snoc191 (snoc191 Γ A) B) C) D) A;v3191
 = var191 (vs191 (vs191 (vs191 vz191)))

v4191 : ∀{Γ A B C D E} → Tm191 (snoc191 (snoc191 (snoc191 (snoc191 (snoc191 Γ A) B) C) D) E) A;v4191
 = var191 (vs191 (vs191 (vs191 (vs191 vz191))))

test191 : ∀{Γ A} → Tm191 Γ (arr191 (arr191 A A) (arr191 A A));test191
  = lam191 (lam191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 v0191)))))))
