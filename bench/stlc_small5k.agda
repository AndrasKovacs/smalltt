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
