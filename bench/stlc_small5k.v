Require Import Coq.Unicode.Utf8.

Definition Ty : Set
 := ∀ (Ty : Set)
      (ι   : Ty)
      (arr : Ty → Ty → Ty)
    , Ty.

Definition ι : Ty := λ _ ι _, ι.

Definition arr : Ty → Ty → Ty
 := λ A B Ty ι arr,
     arr (A Ty ι arr) (B Ty ι arr).

Definition Con : Set
 := ∀ (Con  : Set)
      (nil  : Con)
      (snoc : Con → Ty → Con)
    , Con.

Definition nil : Con
 := λ Con nil snoc , nil.

Definition snoc : Con → Ty → Con
 := λ Γ A Con nil snoc , snoc (Γ Con nil snoc) A.

Definition Var : Con → Ty → Set
 := λ Γ A ,
   ∀ (Var : Con → Ty → Set)
     (vz  : ∀ Γ A, Var (snoc Γ A) A)
     (vs  : ∀ Γ B A, Var Γ A → Var (snoc Γ B) A)
   , Var Γ A.

Definition vz {Γ A} : Var (snoc Γ A) A
 := λ Var vz vs , vz _ _.

Definition vs {Γ B A} : Var Γ A → Var (snoc Γ B) A
 := λ x Var vz vs , vs _ _ _ (x Var vz vs).

Definition Tm : Con → Ty → Set
 := λ Γ A ,
   ∀ (Tm  : Con → Ty → Set)
     (var   : ∀ Γ A     , Var Γ A → Tm Γ A)
     (lam   : ∀ Γ A B   , Tm (snoc Γ A) B → Tm Γ (arr A B))
     (app   : ∀ Γ A B   , Tm Γ (arr A B) → Tm Γ A → Tm Γ B)
   , Tm Γ A.

Definition var {Γ A} : Var Γ A → Tm Γ A
 := λ x Tm var lam app,
     var _ _ x.

Definition lam {Γ A B} : Tm (snoc Γ A) B → Tm Γ (arr A B)
 := λ t Tm var lam app,
     lam _ _ _ (t Tm var lam app).

Definition app {Γ A B} : Tm Γ (arr A B) → Tm Γ A → Tm Γ B
 := λ t u Tm var lam app,
     app _ _ _
         (t Tm var lam app)
         (u Tm var lam app).

Definition v0 {Γ A} : Tm (snoc Γ A) A
 := var vz.

Definition v1 {Γ A B} : Tm (snoc (snoc Γ A) B) A
 := var (vs vz).

Definition v2 {Γ A B C} : Tm (snoc (snoc (snoc Γ A) B) C) A
 := var (vs (vs vz)).

Definition v3 {Γ A B C D} : Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A
 := var (vs (vs (vs vz))).

Definition v4 {Γ A B C D E} : Tm (snoc (snoc (snoc (snoc (snoc Γ A) B) C) D) E) A
 := var (vs (vs (vs (vs vz)))).

Definition test {Γ A} : Tm Γ (arr (arr A A) (arr A A))
 := lam (lam (app v1 (app v1 (app v1 (app v1 (app v1 (app v1 v0))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty1 : Set
 := ∀ (Ty1 : Set)
      (ι   : Ty1)
      (arr : Ty1 → Ty1 → Ty1)
    , Ty1.

Definition ι1 : Ty1 := λ _ ι1 _, ι1.

Definition arr1 : Ty1 → Ty1 → Ty1
 := λ A B Ty1 ι1 arr1,
     arr1 (A Ty1 ι1 arr1) (B Ty1 ι1 arr1).

Definition Con1 : Set
 := ∀ (Con1  : Set)
      (nil  : Con1)
      (snoc : Con1 → Ty1 → Con1)
    , Con1.

Definition nil1 : Con1
 := λ Con1 nil1 snoc , nil1.

Definition snoc1 : Con1 → Ty1 → Con1
 := λ Γ A Con1 nil1 snoc1 , snoc1 (Γ Con1 nil1 snoc1) A.

Definition Var1 : Con1 → Ty1 → Set
 := λ Γ A ,
   ∀ (Var1 : Con1 → Ty1 → Set)
     (vz  : ∀ Γ A, Var1 (snoc1 Γ A) A)
     (vs  : ∀ Γ B A, Var1 Γ A → Var1 (snoc1 Γ B) A)
   , Var1 Γ A.

Definition vz1 {Γ A} : Var1 (snoc1 Γ A) A
 := λ Var1 vz1 vs , vz1 _ _.

Definition vs1 {Γ B A} : Var1 Γ A → Var1 (snoc1 Γ B) A
 := λ x Var1 vz1 vs1 , vs1 _ _ _ (x Var1 vz1 vs1).

Definition Tm1 : Con1 → Ty1 → Set
 := λ Γ A ,
   ∀ (Tm1  : Con1 → Ty1 → Set)
     (var   : ∀ Γ A     , Var1 Γ A → Tm1 Γ A)
     (lam   : ∀ Γ A B   , Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B))
     (app   : ∀ Γ A B   , Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B)
   , Tm1 Γ A.

Definition var1 {Γ A} : Var1 Γ A → Tm1 Γ A
 := λ x Tm1 var1 lam app,
     var1 _ _ x.

Definition lam1 {Γ A B} : Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B)
 := λ t Tm1 var1 lam1 app,
     lam1 _ _ _ (t Tm1 var1 lam1 app).

Definition app1 {Γ A B} : Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B
 := λ t u Tm1 var1 lam1 app1,
     app1 _ _ _
         (t Tm1 var1 lam1 app1)
         (u Tm1 var1 lam1 app1).

Definition v01 {Γ A} : Tm1 (snoc1 Γ A) A
 := var1 vz1.

Definition v11 {Γ A B} : Tm1 (snoc1 (snoc1 Γ A) B) A
 := var1 (vs1 vz1).

Definition v21 {Γ A B C} : Tm1 (snoc1 (snoc1 (snoc1 Γ A) B) C) A
 := var1 (vs1 (vs1 vz1)).

Definition v31 {Γ A B C D} : Tm1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) A
 := var1 (vs1 (vs1 (vs1 vz1))).

Definition v41 {Γ A B C D E} : Tm1 (snoc1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) E) A
 := var1 (vs1 (vs1 (vs1 (vs1 vz1)))).

Definition test1 {Γ A} : Tm1 Γ (arr1 (arr1 A A) (arr1 A A))
 := lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty2 : Set
 := ∀ (Ty2 : Set)
      (ι   : Ty2)
      (arr : Ty2 → Ty2 → Ty2)
    , Ty2.

Definition ι2 : Ty2 := λ _ ι2 _, ι2.

Definition arr2 : Ty2 → Ty2 → Ty2
 := λ A B Ty2 ι2 arr2,
     arr2 (A Ty2 ι2 arr2) (B Ty2 ι2 arr2).

Definition Con2 : Set
 := ∀ (Con2  : Set)
      (nil  : Con2)
      (snoc : Con2 → Ty2 → Con2)
    , Con2.

Definition nil2 : Con2
 := λ Con2 nil2 snoc , nil2.

Definition snoc2 : Con2 → Ty2 → Con2
 := λ Γ A Con2 nil2 snoc2 , snoc2 (Γ Con2 nil2 snoc2) A.

Definition Var2 : Con2 → Ty2 → Set
 := λ Γ A ,
   ∀ (Var2 : Con2 → Ty2 → Set)
     (vz  : ∀ Γ A, Var2 (snoc2 Γ A) A)
     (vs  : ∀ Γ B A, Var2 Γ A → Var2 (snoc2 Γ B) A)
   , Var2 Γ A.

Definition vz2 {Γ A} : Var2 (snoc2 Γ A) A
 := λ Var2 vz2 vs , vz2 _ _.

Definition vs2 {Γ B A} : Var2 Γ A → Var2 (snoc2 Γ B) A
 := λ x Var2 vz2 vs2 , vs2 _ _ _ (x Var2 vz2 vs2).

Definition Tm2 : Con2 → Ty2 → Set
 := λ Γ A ,
   ∀ (Tm2  : Con2 → Ty2 → Set)
     (var   : ∀ Γ A     , Var2 Γ A → Tm2 Γ A)
     (lam   : ∀ Γ A B   , Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B))
     (app   : ∀ Γ A B   , Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B)
   , Tm2 Γ A.

Definition var2 {Γ A} : Var2 Γ A → Tm2 Γ A
 := λ x Tm2 var2 lam app,
     var2 _ _ x.

Definition lam2 {Γ A B} : Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B)
 := λ t Tm2 var2 lam2 app,
     lam2 _ _ _ (t Tm2 var2 lam2 app).

Definition app2 {Γ A B} : Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B
 := λ t u Tm2 var2 lam2 app2,
     app2 _ _ _
         (t Tm2 var2 lam2 app2)
         (u Tm2 var2 lam2 app2).

Definition v02 {Γ A} : Tm2 (snoc2 Γ A) A
 := var2 vz2.

Definition v12 {Γ A B} : Tm2 (snoc2 (snoc2 Γ A) B) A
 := var2 (vs2 vz2).

Definition v22 {Γ A B C} : Tm2 (snoc2 (snoc2 (snoc2 Γ A) B) C) A
 := var2 (vs2 (vs2 vz2)).

Definition v32 {Γ A B C D} : Tm2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) A
 := var2 (vs2 (vs2 (vs2 vz2))).

Definition v42 {Γ A B C D E} : Tm2 (snoc2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) E) A
 := var2 (vs2 (vs2 (vs2 (vs2 vz2)))).

Definition test2 {Γ A} : Tm2 Γ (arr2 (arr2 A A) (arr2 A A))
 := lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty3 : Set
 := ∀ (Ty3 : Set)
      (ι   : Ty3)
      (arr : Ty3 → Ty3 → Ty3)
    , Ty3.

Definition ι3 : Ty3 := λ _ ι3 _, ι3.

Definition arr3 : Ty3 → Ty3 → Ty3
 := λ A B Ty3 ι3 arr3,
     arr3 (A Ty3 ι3 arr3) (B Ty3 ι3 arr3).

Definition Con3 : Set
 := ∀ (Con3  : Set)
      (nil  : Con3)
      (snoc : Con3 → Ty3 → Con3)
    , Con3.

Definition nil3 : Con3
 := λ Con3 nil3 snoc , nil3.

Definition snoc3 : Con3 → Ty3 → Con3
 := λ Γ A Con3 nil3 snoc3 , snoc3 (Γ Con3 nil3 snoc3) A.

Definition Var3 : Con3 → Ty3 → Set
 := λ Γ A ,
   ∀ (Var3 : Con3 → Ty3 → Set)
     (vz  : ∀ Γ A, Var3 (snoc3 Γ A) A)
     (vs  : ∀ Γ B A, Var3 Γ A → Var3 (snoc3 Γ B) A)
   , Var3 Γ A.

Definition vz3 {Γ A} : Var3 (snoc3 Γ A) A
 := λ Var3 vz3 vs , vz3 _ _.

Definition vs3 {Γ B A} : Var3 Γ A → Var3 (snoc3 Γ B) A
 := λ x Var3 vz3 vs3 , vs3 _ _ _ (x Var3 vz3 vs3).

Definition Tm3 : Con3 → Ty3 → Set
 := λ Γ A ,
   ∀ (Tm3  : Con3 → Ty3 → Set)
     (var   : ∀ Γ A     , Var3 Γ A → Tm3 Γ A)
     (lam   : ∀ Γ A B   , Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B))
     (app   : ∀ Γ A B   , Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B)
   , Tm3 Γ A.

Definition var3 {Γ A} : Var3 Γ A → Tm3 Γ A
 := λ x Tm3 var3 lam app,
     var3 _ _ x.

Definition lam3 {Γ A B} : Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B)
 := λ t Tm3 var3 lam3 app,
     lam3 _ _ _ (t Tm3 var3 lam3 app).

Definition app3 {Γ A B} : Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B
 := λ t u Tm3 var3 lam3 app3,
     app3 _ _ _
         (t Tm3 var3 lam3 app3)
         (u Tm3 var3 lam3 app3).

Definition v03 {Γ A} : Tm3 (snoc3 Γ A) A
 := var3 vz3.

Definition v13 {Γ A B} : Tm3 (snoc3 (snoc3 Γ A) B) A
 := var3 (vs3 vz3).

Definition v23 {Γ A B C} : Tm3 (snoc3 (snoc3 (snoc3 Γ A) B) C) A
 := var3 (vs3 (vs3 vz3)).

Definition v33 {Γ A B C D} : Tm3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) A
 := var3 (vs3 (vs3 (vs3 vz3))).

Definition v43 {Γ A B C D E} : Tm3 (snoc3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) E) A
 := var3 (vs3 (vs3 (vs3 (vs3 vz3)))).

Definition test3 {Γ A} : Tm3 Γ (arr3 (arr3 A A) (arr3 A A))
 := lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty4 : Set
 := ∀ (Ty4 : Set)
      (ι   : Ty4)
      (arr : Ty4 → Ty4 → Ty4)
    , Ty4.

Definition ι4 : Ty4 := λ _ ι4 _, ι4.

Definition arr4 : Ty4 → Ty4 → Ty4
 := λ A B Ty4 ι4 arr4,
     arr4 (A Ty4 ι4 arr4) (B Ty4 ι4 arr4).

Definition Con4 : Set
 := ∀ (Con4  : Set)
      (nil  : Con4)
      (snoc : Con4 → Ty4 → Con4)
    , Con4.

Definition nil4 : Con4
 := λ Con4 nil4 snoc , nil4.

Definition snoc4 : Con4 → Ty4 → Con4
 := λ Γ A Con4 nil4 snoc4 , snoc4 (Γ Con4 nil4 snoc4) A.

Definition Var4 : Con4 → Ty4 → Set
 := λ Γ A ,
   ∀ (Var4 : Con4 → Ty4 → Set)
     (vz  : ∀ Γ A, Var4 (snoc4 Γ A) A)
     (vs  : ∀ Γ B A, Var4 Γ A → Var4 (snoc4 Γ B) A)
   , Var4 Γ A.

Definition vz4 {Γ A} : Var4 (snoc4 Γ A) A
 := λ Var4 vz4 vs , vz4 _ _.

Definition vs4 {Γ B A} : Var4 Γ A → Var4 (snoc4 Γ B) A
 := λ x Var4 vz4 vs4 , vs4 _ _ _ (x Var4 vz4 vs4).

Definition Tm4 : Con4 → Ty4 → Set
 := λ Γ A ,
   ∀ (Tm4  : Con4 → Ty4 → Set)
     (var   : ∀ Γ A     , Var4 Γ A → Tm4 Γ A)
     (lam   : ∀ Γ A B   , Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B))
     (app   : ∀ Γ A B   , Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B)
   , Tm4 Γ A.

Definition var4 {Γ A} : Var4 Γ A → Tm4 Γ A
 := λ x Tm4 var4 lam app,
     var4 _ _ x.

Definition lam4 {Γ A B} : Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B)
 := λ t Tm4 var4 lam4 app,
     lam4 _ _ _ (t Tm4 var4 lam4 app).

Definition app4 {Γ A B} : Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B
 := λ t u Tm4 var4 lam4 app4,
     app4 _ _ _
         (t Tm4 var4 lam4 app4)
         (u Tm4 var4 lam4 app4).

Definition v04 {Γ A} : Tm4 (snoc4 Γ A) A
 := var4 vz4.

Definition v14 {Γ A B} : Tm4 (snoc4 (snoc4 Γ A) B) A
 := var4 (vs4 vz4).

Definition v24 {Γ A B C} : Tm4 (snoc4 (snoc4 (snoc4 Γ A) B) C) A
 := var4 (vs4 (vs4 vz4)).

Definition v34 {Γ A B C D} : Tm4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) A
 := var4 (vs4 (vs4 (vs4 vz4))).

Definition v44 {Γ A B C D E} : Tm4 (snoc4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) E) A
 := var4 (vs4 (vs4 (vs4 (vs4 vz4)))).

Definition test4 {Γ A} : Tm4 Γ (arr4 (arr4 A A) (arr4 A A))
 := lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty5 : Set
 := ∀ (Ty5 : Set)
      (ι   : Ty5)
      (arr : Ty5 → Ty5 → Ty5)
    , Ty5.

Definition ι5 : Ty5 := λ _ ι5 _, ι5.

Definition arr5 : Ty5 → Ty5 → Ty5
 := λ A B Ty5 ι5 arr5,
     arr5 (A Ty5 ι5 arr5) (B Ty5 ι5 arr5).

Definition Con5 : Set
 := ∀ (Con5  : Set)
      (nil  : Con5)
      (snoc : Con5 → Ty5 → Con5)
    , Con5.

Definition nil5 : Con5
 := λ Con5 nil5 snoc , nil5.

Definition snoc5 : Con5 → Ty5 → Con5
 := λ Γ A Con5 nil5 snoc5 , snoc5 (Γ Con5 nil5 snoc5) A.

Definition Var5 : Con5 → Ty5 → Set
 := λ Γ A ,
   ∀ (Var5 : Con5 → Ty5 → Set)
     (vz  : ∀ Γ A, Var5 (snoc5 Γ A) A)
     (vs  : ∀ Γ B A, Var5 Γ A → Var5 (snoc5 Γ B) A)
   , Var5 Γ A.

Definition vz5 {Γ A} : Var5 (snoc5 Γ A) A
 := λ Var5 vz5 vs , vz5 _ _.

Definition vs5 {Γ B A} : Var5 Γ A → Var5 (snoc5 Γ B) A
 := λ x Var5 vz5 vs5 , vs5 _ _ _ (x Var5 vz5 vs5).

Definition Tm5 : Con5 → Ty5 → Set
 := λ Γ A ,
   ∀ (Tm5  : Con5 → Ty5 → Set)
     (var   : ∀ Γ A     , Var5 Γ A → Tm5 Γ A)
     (lam   : ∀ Γ A B   , Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B))
     (app   : ∀ Γ A B   , Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B)
   , Tm5 Γ A.

Definition var5 {Γ A} : Var5 Γ A → Tm5 Γ A
 := λ x Tm5 var5 lam app,
     var5 _ _ x.

Definition lam5 {Γ A B} : Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B)
 := λ t Tm5 var5 lam5 app,
     lam5 _ _ _ (t Tm5 var5 lam5 app).

Definition app5 {Γ A B} : Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B
 := λ t u Tm5 var5 lam5 app5,
     app5 _ _ _
         (t Tm5 var5 lam5 app5)
         (u Tm5 var5 lam5 app5).

Definition v05 {Γ A} : Tm5 (snoc5 Γ A) A
 := var5 vz5.

Definition v15 {Γ A B} : Tm5 (snoc5 (snoc5 Γ A) B) A
 := var5 (vs5 vz5).

Definition v25 {Γ A B C} : Tm5 (snoc5 (snoc5 (snoc5 Γ A) B) C) A
 := var5 (vs5 (vs5 vz5)).

Definition v35 {Γ A B C D} : Tm5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) A
 := var5 (vs5 (vs5 (vs5 vz5))).

Definition v45 {Γ A B C D E} : Tm5 (snoc5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) E) A
 := var5 (vs5 (vs5 (vs5 (vs5 vz5)))).

Definition test5 {Γ A} : Tm5 Γ (arr5 (arr5 A A) (arr5 A A))
 := lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty6 : Set
 := ∀ (Ty6 : Set)
      (ι   : Ty6)
      (arr : Ty6 → Ty6 → Ty6)
    , Ty6.

Definition ι6 : Ty6 := λ _ ι6 _, ι6.

Definition arr6 : Ty6 → Ty6 → Ty6
 := λ A B Ty6 ι6 arr6,
     arr6 (A Ty6 ι6 arr6) (B Ty6 ι6 arr6).

Definition Con6 : Set
 := ∀ (Con6  : Set)
      (nil  : Con6)
      (snoc : Con6 → Ty6 → Con6)
    , Con6.

Definition nil6 : Con6
 := λ Con6 nil6 snoc , nil6.

Definition snoc6 : Con6 → Ty6 → Con6
 := λ Γ A Con6 nil6 snoc6 , snoc6 (Γ Con6 nil6 snoc6) A.

Definition Var6 : Con6 → Ty6 → Set
 := λ Γ A ,
   ∀ (Var6 : Con6 → Ty6 → Set)
     (vz  : ∀ Γ A, Var6 (snoc6 Γ A) A)
     (vs  : ∀ Γ B A, Var6 Γ A → Var6 (snoc6 Γ B) A)
   , Var6 Γ A.

Definition vz6 {Γ A} : Var6 (snoc6 Γ A) A
 := λ Var6 vz6 vs , vz6 _ _.

Definition vs6 {Γ B A} : Var6 Γ A → Var6 (snoc6 Γ B) A
 := λ x Var6 vz6 vs6 , vs6 _ _ _ (x Var6 vz6 vs6).

Definition Tm6 : Con6 → Ty6 → Set
 := λ Γ A ,
   ∀ (Tm6  : Con6 → Ty6 → Set)
     (var   : ∀ Γ A     , Var6 Γ A → Tm6 Γ A)
     (lam   : ∀ Γ A B   , Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B))
     (app   : ∀ Γ A B   , Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B)
   , Tm6 Γ A.

Definition var6 {Γ A} : Var6 Γ A → Tm6 Γ A
 := λ x Tm6 var6 lam app,
     var6 _ _ x.

Definition lam6 {Γ A B} : Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B)
 := λ t Tm6 var6 lam6 app,
     lam6 _ _ _ (t Tm6 var6 lam6 app).

Definition app6 {Γ A B} : Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B
 := λ t u Tm6 var6 lam6 app6,
     app6 _ _ _
         (t Tm6 var6 lam6 app6)
         (u Tm6 var6 lam6 app6).

Definition v06 {Γ A} : Tm6 (snoc6 Γ A) A
 := var6 vz6.

Definition v16 {Γ A B} : Tm6 (snoc6 (snoc6 Γ A) B) A
 := var6 (vs6 vz6).

Definition v26 {Γ A B C} : Tm6 (snoc6 (snoc6 (snoc6 Γ A) B) C) A
 := var6 (vs6 (vs6 vz6)).

Definition v36 {Γ A B C D} : Tm6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) A
 := var6 (vs6 (vs6 (vs6 vz6))).

Definition v46 {Γ A B C D E} : Tm6 (snoc6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) E) A
 := var6 (vs6 (vs6 (vs6 (vs6 vz6)))).

Definition test6 {Γ A} : Tm6 Γ (arr6 (arr6 A A) (arr6 A A))
 := lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty7 : Set
 := ∀ (Ty7 : Set)
      (ι   : Ty7)
      (arr : Ty7 → Ty7 → Ty7)
    , Ty7.

Definition ι7 : Ty7 := λ _ ι7 _, ι7.

Definition arr7 : Ty7 → Ty7 → Ty7
 := λ A B Ty7 ι7 arr7,
     arr7 (A Ty7 ι7 arr7) (B Ty7 ι7 arr7).

Definition Con7 : Set
 := ∀ (Con7  : Set)
      (nil  : Con7)
      (snoc : Con7 → Ty7 → Con7)
    , Con7.

Definition nil7 : Con7
 := λ Con7 nil7 snoc , nil7.

Definition snoc7 : Con7 → Ty7 → Con7
 := λ Γ A Con7 nil7 snoc7 , snoc7 (Γ Con7 nil7 snoc7) A.

Definition Var7 : Con7 → Ty7 → Set
 := λ Γ A ,
   ∀ (Var7 : Con7 → Ty7 → Set)
     (vz  : ∀ Γ A, Var7 (snoc7 Γ A) A)
     (vs  : ∀ Γ B A, Var7 Γ A → Var7 (snoc7 Γ B) A)
   , Var7 Γ A.

Definition vz7 {Γ A} : Var7 (snoc7 Γ A) A
 := λ Var7 vz7 vs , vz7 _ _.

Definition vs7 {Γ B A} : Var7 Γ A → Var7 (snoc7 Γ B) A
 := λ x Var7 vz7 vs7 , vs7 _ _ _ (x Var7 vz7 vs7).

Definition Tm7 : Con7 → Ty7 → Set
 := λ Γ A ,
   ∀ (Tm7  : Con7 → Ty7 → Set)
     (var   : ∀ Γ A     , Var7 Γ A → Tm7 Γ A)
     (lam   : ∀ Γ A B   , Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B))
     (app   : ∀ Γ A B   , Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B)
   , Tm7 Γ A.

Definition var7 {Γ A} : Var7 Γ A → Tm7 Γ A
 := λ x Tm7 var7 lam app,
     var7 _ _ x.

Definition lam7 {Γ A B} : Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B)
 := λ t Tm7 var7 lam7 app,
     lam7 _ _ _ (t Tm7 var7 lam7 app).

Definition app7 {Γ A B} : Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B
 := λ t u Tm7 var7 lam7 app7,
     app7 _ _ _
         (t Tm7 var7 lam7 app7)
         (u Tm7 var7 lam7 app7).

Definition v07 {Γ A} : Tm7 (snoc7 Γ A) A
 := var7 vz7.

Definition v17 {Γ A B} : Tm7 (snoc7 (snoc7 Γ A) B) A
 := var7 (vs7 vz7).

Definition v27 {Γ A B C} : Tm7 (snoc7 (snoc7 (snoc7 Γ A) B) C) A
 := var7 (vs7 (vs7 vz7)).

Definition v37 {Γ A B C D} : Tm7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) A
 := var7 (vs7 (vs7 (vs7 vz7))).

Definition v47 {Γ A B C D E} : Tm7 (snoc7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) E) A
 := var7 (vs7 (vs7 (vs7 (vs7 vz7)))).

Definition test7 {Γ A} : Tm7 Γ (arr7 (arr7 A A) (arr7 A A))
 := lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty8 : Set
 := ∀ (Ty8 : Set)
      (ι   : Ty8)
      (arr : Ty8 → Ty8 → Ty8)
    , Ty8.

Definition ι8 : Ty8 := λ _ ι8 _, ι8.

Definition arr8 : Ty8 → Ty8 → Ty8
 := λ A B Ty8 ι8 arr8,
     arr8 (A Ty8 ι8 arr8) (B Ty8 ι8 arr8).

Definition Con8 : Set
 := ∀ (Con8  : Set)
      (nil  : Con8)
      (snoc : Con8 → Ty8 → Con8)
    , Con8.

Definition nil8 : Con8
 := λ Con8 nil8 snoc , nil8.

Definition snoc8 : Con8 → Ty8 → Con8
 := λ Γ A Con8 nil8 snoc8 , snoc8 (Γ Con8 nil8 snoc8) A.

Definition Var8 : Con8 → Ty8 → Set
 := λ Γ A ,
   ∀ (Var8 : Con8 → Ty8 → Set)
     (vz  : ∀ Γ A, Var8 (snoc8 Γ A) A)
     (vs  : ∀ Γ B A, Var8 Γ A → Var8 (snoc8 Γ B) A)
   , Var8 Γ A.

Definition vz8 {Γ A} : Var8 (snoc8 Γ A) A
 := λ Var8 vz8 vs , vz8 _ _.

Definition vs8 {Γ B A} : Var8 Γ A → Var8 (snoc8 Γ B) A
 := λ x Var8 vz8 vs8 , vs8 _ _ _ (x Var8 vz8 vs8).

Definition Tm8 : Con8 → Ty8 → Set
 := λ Γ A ,
   ∀ (Tm8  : Con8 → Ty8 → Set)
     (var   : ∀ Γ A     , Var8 Γ A → Tm8 Γ A)
     (lam   : ∀ Γ A B   , Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B))
     (app   : ∀ Γ A B   , Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B)
   , Tm8 Γ A.

Definition var8 {Γ A} : Var8 Γ A → Tm8 Γ A
 := λ x Tm8 var8 lam app,
     var8 _ _ x.

Definition lam8 {Γ A B} : Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B)
 := λ t Tm8 var8 lam8 app,
     lam8 _ _ _ (t Tm8 var8 lam8 app).

Definition app8 {Γ A B} : Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B
 := λ t u Tm8 var8 lam8 app8,
     app8 _ _ _
         (t Tm8 var8 lam8 app8)
         (u Tm8 var8 lam8 app8).

Definition v08 {Γ A} : Tm8 (snoc8 Γ A) A
 := var8 vz8.

Definition v18 {Γ A B} : Tm8 (snoc8 (snoc8 Γ A) B) A
 := var8 (vs8 vz8).

Definition v28 {Γ A B C} : Tm8 (snoc8 (snoc8 (snoc8 Γ A) B) C) A
 := var8 (vs8 (vs8 vz8)).

Definition v38 {Γ A B C D} : Tm8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) A
 := var8 (vs8 (vs8 (vs8 vz8))).

Definition v48 {Γ A B C D E} : Tm8 (snoc8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) E) A
 := var8 (vs8 (vs8 (vs8 (vs8 vz8)))).

Definition test8 {Γ A} : Tm8 Γ (arr8 (arr8 A A) (arr8 A A))
 := lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty9 : Set
 := ∀ (Ty9 : Set)
      (ι   : Ty9)
      (arr : Ty9 → Ty9 → Ty9)
    , Ty9.

Definition ι9 : Ty9 := λ _ ι9 _, ι9.

Definition arr9 : Ty9 → Ty9 → Ty9
 := λ A B Ty9 ι9 arr9,
     arr9 (A Ty9 ι9 arr9) (B Ty9 ι9 arr9).

Definition Con9 : Set
 := ∀ (Con9  : Set)
      (nil  : Con9)
      (snoc : Con9 → Ty9 → Con9)
    , Con9.

Definition nil9 : Con9
 := λ Con9 nil9 snoc , nil9.

Definition snoc9 : Con9 → Ty9 → Con9
 := λ Γ A Con9 nil9 snoc9 , snoc9 (Γ Con9 nil9 snoc9) A.

Definition Var9 : Con9 → Ty9 → Set
 := λ Γ A ,
   ∀ (Var9 : Con9 → Ty9 → Set)
     (vz  : ∀ Γ A, Var9 (snoc9 Γ A) A)
     (vs  : ∀ Γ B A, Var9 Γ A → Var9 (snoc9 Γ B) A)
   , Var9 Γ A.

Definition vz9 {Γ A} : Var9 (snoc9 Γ A) A
 := λ Var9 vz9 vs , vz9 _ _.

Definition vs9 {Γ B A} : Var9 Γ A → Var9 (snoc9 Γ B) A
 := λ x Var9 vz9 vs9 , vs9 _ _ _ (x Var9 vz9 vs9).

Definition Tm9 : Con9 → Ty9 → Set
 := λ Γ A ,
   ∀ (Tm9  : Con9 → Ty9 → Set)
     (var   : ∀ Γ A     , Var9 Γ A → Tm9 Γ A)
     (lam   : ∀ Γ A B   , Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B))
     (app   : ∀ Γ A B   , Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B)
   , Tm9 Γ A.

Definition var9 {Γ A} : Var9 Γ A → Tm9 Γ A
 := λ x Tm9 var9 lam app,
     var9 _ _ x.

Definition lam9 {Γ A B} : Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B)
 := λ t Tm9 var9 lam9 app,
     lam9 _ _ _ (t Tm9 var9 lam9 app).

Definition app9 {Γ A B} : Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B
 := λ t u Tm9 var9 lam9 app9,
     app9 _ _ _
         (t Tm9 var9 lam9 app9)
         (u Tm9 var9 lam9 app9).

Definition v09 {Γ A} : Tm9 (snoc9 Γ A) A
 := var9 vz9.

Definition v19 {Γ A B} : Tm9 (snoc9 (snoc9 Γ A) B) A
 := var9 (vs9 vz9).

Definition v29 {Γ A B C} : Tm9 (snoc9 (snoc9 (snoc9 Γ A) B) C) A
 := var9 (vs9 (vs9 vz9)).

Definition v39 {Γ A B C D} : Tm9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) A
 := var9 (vs9 (vs9 (vs9 vz9))).

Definition v49 {Γ A B C D E} : Tm9 (snoc9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) E) A
 := var9 (vs9 (vs9 (vs9 (vs9 vz9)))).

Definition test9 {Γ A} : Tm9 Γ (arr9 (arr9 A A) (arr9 A A))
 := lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty10 : Set
 := ∀ (Ty10 : Set)
      (ι   : Ty10)
      (arr : Ty10 → Ty10 → Ty10)
    , Ty10.

Definition ι10 : Ty10 := λ _ ι10 _, ι10.

Definition arr10 : Ty10 → Ty10 → Ty10
 := λ A B Ty10 ι10 arr10,
     arr10 (A Ty10 ι10 arr10) (B Ty10 ι10 arr10).

Definition Con10 : Set
 := ∀ (Con10  : Set)
      (nil  : Con10)
      (snoc : Con10 → Ty10 → Con10)
    , Con10.

Definition nil10 : Con10
 := λ Con10 nil10 snoc , nil10.

Definition snoc10 : Con10 → Ty10 → Con10
 := λ Γ A Con10 nil10 snoc10 , snoc10 (Γ Con10 nil10 snoc10) A.

Definition Var10 : Con10 → Ty10 → Set
 := λ Γ A ,
   ∀ (Var10 : Con10 → Ty10 → Set)
     (vz  : ∀ Γ A, Var10 (snoc10 Γ A) A)
     (vs  : ∀ Γ B A, Var10 Γ A → Var10 (snoc10 Γ B) A)
   , Var10 Γ A.

Definition vz10 {Γ A} : Var10 (snoc10 Γ A) A
 := λ Var10 vz10 vs , vz10 _ _.

Definition vs10 {Γ B A} : Var10 Γ A → Var10 (snoc10 Γ B) A
 := λ x Var10 vz10 vs10 , vs10 _ _ _ (x Var10 vz10 vs10).

Definition Tm10 : Con10 → Ty10 → Set
 := λ Γ A ,
   ∀ (Tm10  : Con10 → Ty10 → Set)
     (var   : ∀ Γ A     , Var10 Γ A → Tm10 Γ A)
     (lam   : ∀ Γ A B   , Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B))
     (app   : ∀ Γ A B   , Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B)
   , Tm10 Γ A.

Definition var10 {Γ A} : Var10 Γ A → Tm10 Γ A
 := λ x Tm10 var10 lam app,
     var10 _ _ x.

Definition lam10 {Γ A B} : Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B)
 := λ t Tm10 var10 lam10 app,
     lam10 _ _ _ (t Tm10 var10 lam10 app).

Definition app10 {Γ A B} : Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B
 := λ t u Tm10 var10 lam10 app10,
     app10 _ _ _
         (t Tm10 var10 lam10 app10)
         (u Tm10 var10 lam10 app10).

Definition v010 {Γ A} : Tm10 (snoc10 Γ A) A
 := var10 vz10.

Definition v110 {Γ A B} : Tm10 (snoc10 (snoc10 Γ A) B) A
 := var10 (vs10 vz10).

Definition v210 {Γ A B C} : Tm10 (snoc10 (snoc10 (snoc10 Γ A) B) C) A
 := var10 (vs10 (vs10 vz10)).

Definition v310 {Γ A B C D} : Tm10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) A
 := var10 (vs10 (vs10 (vs10 vz10))).

Definition v410 {Γ A B C D E} : Tm10 (snoc10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) E) A
 := var10 (vs10 (vs10 (vs10 (vs10 vz10)))).

Definition test10 {Γ A} : Tm10 Γ (arr10 (arr10 A A) (arr10 A A))
 := lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty11 : Set
 := ∀ (Ty11 : Set)
      (ι   : Ty11)
      (arr : Ty11 → Ty11 → Ty11)
    , Ty11.

Definition ι11 : Ty11 := λ _ ι11 _, ι11.

Definition arr11 : Ty11 → Ty11 → Ty11
 := λ A B Ty11 ι11 arr11,
     arr11 (A Ty11 ι11 arr11) (B Ty11 ι11 arr11).

Definition Con11 : Set
 := ∀ (Con11  : Set)
      (nil  : Con11)
      (snoc : Con11 → Ty11 → Con11)
    , Con11.

Definition nil11 : Con11
 := λ Con11 nil11 snoc , nil11.

Definition snoc11 : Con11 → Ty11 → Con11
 := λ Γ A Con11 nil11 snoc11 , snoc11 (Γ Con11 nil11 snoc11) A.

Definition Var11 : Con11 → Ty11 → Set
 := λ Γ A ,
   ∀ (Var11 : Con11 → Ty11 → Set)
     (vz  : ∀ Γ A, Var11 (snoc11 Γ A) A)
     (vs  : ∀ Γ B A, Var11 Γ A → Var11 (snoc11 Γ B) A)
   , Var11 Γ A.

Definition vz11 {Γ A} : Var11 (snoc11 Γ A) A
 := λ Var11 vz11 vs , vz11 _ _.

Definition vs11 {Γ B A} : Var11 Γ A → Var11 (snoc11 Γ B) A
 := λ x Var11 vz11 vs11 , vs11 _ _ _ (x Var11 vz11 vs11).

Definition Tm11 : Con11 → Ty11 → Set
 := λ Γ A ,
   ∀ (Tm11  : Con11 → Ty11 → Set)
     (var   : ∀ Γ A     , Var11 Γ A → Tm11 Γ A)
     (lam   : ∀ Γ A B   , Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B))
     (app   : ∀ Γ A B   , Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B)
   , Tm11 Γ A.

Definition var11 {Γ A} : Var11 Γ A → Tm11 Γ A
 := λ x Tm11 var11 lam app,
     var11 _ _ x.

Definition lam11 {Γ A B} : Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B)
 := λ t Tm11 var11 lam11 app,
     lam11 _ _ _ (t Tm11 var11 lam11 app).

Definition app11 {Γ A B} : Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B
 := λ t u Tm11 var11 lam11 app11,
     app11 _ _ _
         (t Tm11 var11 lam11 app11)
         (u Tm11 var11 lam11 app11).

Definition v011 {Γ A} : Tm11 (snoc11 Γ A) A
 := var11 vz11.

Definition v111 {Γ A B} : Tm11 (snoc11 (snoc11 Γ A) B) A
 := var11 (vs11 vz11).

Definition v211 {Γ A B C} : Tm11 (snoc11 (snoc11 (snoc11 Γ A) B) C) A
 := var11 (vs11 (vs11 vz11)).

Definition v311 {Γ A B C D} : Tm11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) A
 := var11 (vs11 (vs11 (vs11 vz11))).

Definition v411 {Γ A B C D E} : Tm11 (snoc11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) E) A
 := var11 (vs11 (vs11 (vs11 (vs11 vz11)))).

Definition test11 {Γ A} : Tm11 Γ (arr11 (arr11 A A) (arr11 A A))
 := lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty12 : Set
 := ∀ (Ty12 : Set)
      (ι   : Ty12)
      (arr : Ty12 → Ty12 → Ty12)
    , Ty12.

Definition ι12 : Ty12 := λ _ ι12 _, ι12.

Definition arr12 : Ty12 → Ty12 → Ty12
 := λ A B Ty12 ι12 arr12,
     arr12 (A Ty12 ι12 arr12) (B Ty12 ι12 arr12).

Definition Con12 : Set
 := ∀ (Con12  : Set)
      (nil  : Con12)
      (snoc : Con12 → Ty12 → Con12)
    , Con12.

Definition nil12 : Con12
 := λ Con12 nil12 snoc , nil12.

Definition snoc12 : Con12 → Ty12 → Con12
 := λ Γ A Con12 nil12 snoc12 , snoc12 (Γ Con12 nil12 snoc12) A.

Definition Var12 : Con12 → Ty12 → Set
 := λ Γ A ,
   ∀ (Var12 : Con12 → Ty12 → Set)
     (vz  : ∀ Γ A, Var12 (snoc12 Γ A) A)
     (vs  : ∀ Γ B A, Var12 Γ A → Var12 (snoc12 Γ B) A)
   , Var12 Γ A.

Definition vz12 {Γ A} : Var12 (snoc12 Γ A) A
 := λ Var12 vz12 vs , vz12 _ _.

Definition vs12 {Γ B A} : Var12 Γ A → Var12 (snoc12 Γ B) A
 := λ x Var12 vz12 vs12 , vs12 _ _ _ (x Var12 vz12 vs12).

Definition Tm12 : Con12 → Ty12 → Set
 := λ Γ A ,
   ∀ (Tm12  : Con12 → Ty12 → Set)
     (var   : ∀ Γ A     , Var12 Γ A → Tm12 Γ A)
     (lam   : ∀ Γ A B   , Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B))
     (app   : ∀ Γ A B   , Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B)
   , Tm12 Γ A.

Definition var12 {Γ A} : Var12 Γ A → Tm12 Γ A
 := λ x Tm12 var12 lam app,
     var12 _ _ x.

Definition lam12 {Γ A B} : Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B)
 := λ t Tm12 var12 lam12 app,
     lam12 _ _ _ (t Tm12 var12 lam12 app).

Definition app12 {Γ A B} : Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B
 := λ t u Tm12 var12 lam12 app12,
     app12 _ _ _
         (t Tm12 var12 lam12 app12)
         (u Tm12 var12 lam12 app12).

Definition v012 {Γ A} : Tm12 (snoc12 Γ A) A
 := var12 vz12.

Definition v112 {Γ A B} : Tm12 (snoc12 (snoc12 Γ A) B) A
 := var12 (vs12 vz12).

Definition v212 {Γ A B C} : Tm12 (snoc12 (snoc12 (snoc12 Γ A) B) C) A
 := var12 (vs12 (vs12 vz12)).

Definition v312 {Γ A B C D} : Tm12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) A
 := var12 (vs12 (vs12 (vs12 vz12))).

Definition v412 {Γ A B C D E} : Tm12 (snoc12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) E) A
 := var12 (vs12 (vs12 (vs12 (vs12 vz12)))).

Definition test12 {Γ A} : Tm12 Γ (arr12 (arr12 A A) (arr12 A A))
 := lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty13 : Set
 := ∀ (Ty13 : Set)
      (ι   : Ty13)
      (arr : Ty13 → Ty13 → Ty13)
    , Ty13.

Definition ι13 : Ty13 := λ _ ι13 _, ι13.

Definition arr13 : Ty13 → Ty13 → Ty13
 := λ A B Ty13 ι13 arr13,
     arr13 (A Ty13 ι13 arr13) (B Ty13 ι13 arr13).

Definition Con13 : Set
 := ∀ (Con13  : Set)
      (nil  : Con13)
      (snoc : Con13 → Ty13 → Con13)
    , Con13.

Definition nil13 : Con13
 := λ Con13 nil13 snoc , nil13.

Definition snoc13 : Con13 → Ty13 → Con13
 := λ Γ A Con13 nil13 snoc13 , snoc13 (Γ Con13 nil13 snoc13) A.

Definition Var13 : Con13 → Ty13 → Set
 := λ Γ A ,
   ∀ (Var13 : Con13 → Ty13 → Set)
     (vz  : ∀ Γ A, Var13 (snoc13 Γ A) A)
     (vs  : ∀ Γ B A, Var13 Γ A → Var13 (snoc13 Γ B) A)
   , Var13 Γ A.

Definition vz13 {Γ A} : Var13 (snoc13 Γ A) A
 := λ Var13 vz13 vs , vz13 _ _.

Definition vs13 {Γ B A} : Var13 Γ A → Var13 (snoc13 Γ B) A
 := λ x Var13 vz13 vs13 , vs13 _ _ _ (x Var13 vz13 vs13).

Definition Tm13 : Con13 → Ty13 → Set
 := λ Γ A ,
   ∀ (Tm13  : Con13 → Ty13 → Set)
     (var   : ∀ Γ A     , Var13 Γ A → Tm13 Γ A)
     (lam   : ∀ Γ A B   , Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B))
     (app   : ∀ Γ A B   , Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B)
   , Tm13 Γ A.

Definition var13 {Γ A} : Var13 Γ A → Tm13 Γ A
 := λ x Tm13 var13 lam app,
     var13 _ _ x.

Definition lam13 {Γ A B} : Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B)
 := λ t Tm13 var13 lam13 app,
     lam13 _ _ _ (t Tm13 var13 lam13 app).

Definition app13 {Γ A B} : Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B
 := λ t u Tm13 var13 lam13 app13,
     app13 _ _ _
         (t Tm13 var13 lam13 app13)
         (u Tm13 var13 lam13 app13).

Definition v013 {Γ A} : Tm13 (snoc13 Γ A) A
 := var13 vz13.

Definition v113 {Γ A B} : Tm13 (snoc13 (snoc13 Γ A) B) A
 := var13 (vs13 vz13).

Definition v213 {Γ A B C} : Tm13 (snoc13 (snoc13 (snoc13 Γ A) B) C) A
 := var13 (vs13 (vs13 vz13)).

Definition v313 {Γ A B C D} : Tm13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) A
 := var13 (vs13 (vs13 (vs13 vz13))).

Definition v413 {Γ A B C D E} : Tm13 (snoc13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) E) A
 := var13 (vs13 (vs13 (vs13 (vs13 vz13)))).

Definition test13 {Γ A} : Tm13 Γ (arr13 (arr13 A A) (arr13 A A))
 := lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty14 : Set
 := ∀ (Ty14 : Set)
      (ι   : Ty14)
      (arr : Ty14 → Ty14 → Ty14)
    , Ty14.

Definition ι14 : Ty14 := λ _ ι14 _, ι14.

Definition arr14 : Ty14 → Ty14 → Ty14
 := λ A B Ty14 ι14 arr14,
     arr14 (A Ty14 ι14 arr14) (B Ty14 ι14 arr14).

Definition Con14 : Set
 := ∀ (Con14  : Set)
      (nil  : Con14)
      (snoc : Con14 → Ty14 → Con14)
    , Con14.

Definition nil14 : Con14
 := λ Con14 nil14 snoc , nil14.

Definition snoc14 : Con14 → Ty14 → Con14
 := λ Γ A Con14 nil14 snoc14 , snoc14 (Γ Con14 nil14 snoc14) A.

Definition Var14 : Con14 → Ty14 → Set
 := λ Γ A ,
   ∀ (Var14 : Con14 → Ty14 → Set)
     (vz  : ∀ Γ A, Var14 (snoc14 Γ A) A)
     (vs  : ∀ Γ B A, Var14 Γ A → Var14 (snoc14 Γ B) A)
   , Var14 Γ A.

Definition vz14 {Γ A} : Var14 (snoc14 Γ A) A
 := λ Var14 vz14 vs , vz14 _ _.

Definition vs14 {Γ B A} : Var14 Γ A → Var14 (snoc14 Γ B) A
 := λ x Var14 vz14 vs14 , vs14 _ _ _ (x Var14 vz14 vs14).

Definition Tm14 : Con14 → Ty14 → Set
 := λ Γ A ,
   ∀ (Tm14  : Con14 → Ty14 → Set)
     (var   : ∀ Γ A     , Var14 Γ A → Tm14 Γ A)
     (lam   : ∀ Γ A B   , Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B))
     (app   : ∀ Γ A B   , Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B)
   , Tm14 Γ A.

Definition var14 {Γ A} : Var14 Γ A → Tm14 Γ A
 := λ x Tm14 var14 lam app,
     var14 _ _ x.

Definition lam14 {Γ A B} : Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B)
 := λ t Tm14 var14 lam14 app,
     lam14 _ _ _ (t Tm14 var14 lam14 app).

Definition app14 {Γ A B} : Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B
 := λ t u Tm14 var14 lam14 app14,
     app14 _ _ _
         (t Tm14 var14 lam14 app14)
         (u Tm14 var14 lam14 app14).

Definition v014 {Γ A} : Tm14 (snoc14 Γ A) A
 := var14 vz14.

Definition v114 {Γ A B} : Tm14 (snoc14 (snoc14 Γ A) B) A
 := var14 (vs14 vz14).

Definition v214 {Γ A B C} : Tm14 (snoc14 (snoc14 (snoc14 Γ A) B) C) A
 := var14 (vs14 (vs14 vz14)).

Definition v314 {Γ A B C D} : Tm14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) A
 := var14 (vs14 (vs14 (vs14 vz14))).

Definition v414 {Γ A B C D E} : Tm14 (snoc14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) E) A
 := var14 (vs14 (vs14 (vs14 (vs14 vz14)))).

Definition test14 {Γ A} : Tm14 Γ (arr14 (arr14 A A) (arr14 A A))
 := lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty15 : Set
 := ∀ (Ty15 : Set)
      (ι   : Ty15)
      (arr : Ty15 → Ty15 → Ty15)
    , Ty15.

Definition ι15 : Ty15 := λ _ ι15 _, ι15.

Definition arr15 : Ty15 → Ty15 → Ty15
 := λ A B Ty15 ι15 arr15,
     arr15 (A Ty15 ι15 arr15) (B Ty15 ι15 arr15).

Definition Con15 : Set
 := ∀ (Con15  : Set)
      (nil  : Con15)
      (snoc : Con15 → Ty15 → Con15)
    , Con15.

Definition nil15 : Con15
 := λ Con15 nil15 snoc , nil15.

Definition snoc15 : Con15 → Ty15 → Con15
 := λ Γ A Con15 nil15 snoc15 , snoc15 (Γ Con15 nil15 snoc15) A.

Definition Var15 : Con15 → Ty15 → Set
 := λ Γ A ,
   ∀ (Var15 : Con15 → Ty15 → Set)
     (vz  : ∀ Γ A, Var15 (snoc15 Γ A) A)
     (vs  : ∀ Γ B A, Var15 Γ A → Var15 (snoc15 Γ B) A)
   , Var15 Γ A.

Definition vz15 {Γ A} : Var15 (snoc15 Γ A) A
 := λ Var15 vz15 vs , vz15 _ _.

Definition vs15 {Γ B A} : Var15 Γ A → Var15 (snoc15 Γ B) A
 := λ x Var15 vz15 vs15 , vs15 _ _ _ (x Var15 vz15 vs15).

Definition Tm15 : Con15 → Ty15 → Set
 := λ Γ A ,
   ∀ (Tm15  : Con15 → Ty15 → Set)
     (var   : ∀ Γ A     , Var15 Γ A → Tm15 Γ A)
     (lam   : ∀ Γ A B   , Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B))
     (app   : ∀ Γ A B   , Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B)
   , Tm15 Γ A.

Definition var15 {Γ A} : Var15 Γ A → Tm15 Γ A
 := λ x Tm15 var15 lam app,
     var15 _ _ x.

Definition lam15 {Γ A B} : Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B)
 := λ t Tm15 var15 lam15 app,
     lam15 _ _ _ (t Tm15 var15 lam15 app).

Definition app15 {Γ A B} : Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B
 := λ t u Tm15 var15 lam15 app15,
     app15 _ _ _
         (t Tm15 var15 lam15 app15)
         (u Tm15 var15 lam15 app15).

Definition v015 {Γ A} : Tm15 (snoc15 Γ A) A
 := var15 vz15.

Definition v115 {Γ A B} : Tm15 (snoc15 (snoc15 Γ A) B) A
 := var15 (vs15 vz15).

Definition v215 {Γ A B C} : Tm15 (snoc15 (snoc15 (snoc15 Γ A) B) C) A
 := var15 (vs15 (vs15 vz15)).

Definition v315 {Γ A B C D} : Tm15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) A
 := var15 (vs15 (vs15 (vs15 vz15))).

Definition v415 {Γ A B C D E} : Tm15 (snoc15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) E) A
 := var15 (vs15 (vs15 (vs15 (vs15 vz15)))).

Definition test15 {Γ A} : Tm15 Γ (arr15 (arr15 A A) (arr15 A A))
 := lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty16 : Set
 := ∀ (Ty16 : Set)
      (ι   : Ty16)
      (arr : Ty16 → Ty16 → Ty16)
    , Ty16.

Definition ι16 : Ty16 := λ _ ι16 _, ι16.

Definition arr16 : Ty16 → Ty16 → Ty16
 := λ A B Ty16 ι16 arr16,
     arr16 (A Ty16 ι16 arr16) (B Ty16 ι16 arr16).

Definition Con16 : Set
 := ∀ (Con16  : Set)
      (nil  : Con16)
      (snoc : Con16 → Ty16 → Con16)
    , Con16.

Definition nil16 : Con16
 := λ Con16 nil16 snoc , nil16.

Definition snoc16 : Con16 → Ty16 → Con16
 := λ Γ A Con16 nil16 snoc16 , snoc16 (Γ Con16 nil16 snoc16) A.

Definition Var16 : Con16 → Ty16 → Set
 := λ Γ A ,
   ∀ (Var16 : Con16 → Ty16 → Set)
     (vz  : ∀ Γ A, Var16 (snoc16 Γ A) A)
     (vs  : ∀ Γ B A, Var16 Γ A → Var16 (snoc16 Γ B) A)
   , Var16 Γ A.

Definition vz16 {Γ A} : Var16 (snoc16 Γ A) A
 := λ Var16 vz16 vs , vz16 _ _.

Definition vs16 {Γ B A} : Var16 Γ A → Var16 (snoc16 Γ B) A
 := λ x Var16 vz16 vs16 , vs16 _ _ _ (x Var16 vz16 vs16).

Definition Tm16 : Con16 → Ty16 → Set
 := λ Γ A ,
   ∀ (Tm16  : Con16 → Ty16 → Set)
     (var   : ∀ Γ A     , Var16 Γ A → Tm16 Γ A)
     (lam   : ∀ Γ A B   , Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B))
     (app   : ∀ Γ A B   , Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B)
   , Tm16 Γ A.

Definition var16 {Γ A} : Var16 Γ A → Tm16 Γ A
 := λ x Tm16 var16 lam app,
     var16 _ _ x.

Definition lam16 {Γ A B} : Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B)
 := λ t Tm16 var16 lam16 app,
     lam16 _ _ _ (t Tm16 var16 lam16 app).

Definition app16 {Γ A B} : Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B
 := λ t u Tm16 var16 lam16 app16,
     app16 _ _ _
         (t Tm16 var16 lam16 app16)
         (u Tm16 var16 lam16 app16).

Definition v016 {Γ A} : Tm16 (snoc16 Γ A) A
 := var16 vz16.

Definition v116 {Γ A B} : Tm16 (snoc16 (snoc16 Γ A) B) A
 := var16 (vs16 vz16).

Definition v216 {Γ A B C} : Tm16 (snoc16 (snoc16 (snoc16 Γ A) B) C) A
 := var16 (vs16 (vs16 vz16)).

Definition v316 {Γ A B C D} : Tm16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) A
 := var16 (vs16 (vs16 (vs16 vz16))).

Definition v416 {Γ A B C D E} : Tm16 (snoc16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) E) A
 := var16 (vs16 (vs16 (vs16 (vs16 vz16)))).

Definition test16 {Γ A} : Tm16 Γ (arr16 (arr16 A A) (arr16 A A))
 := lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty17 : Set
 := ∀ (Ty17 : Set)
      (ι   : Ty17)
      (arr : Ty17 → Ty17 → Ty17)
    , Ty17.

Definition ι17 : Ty17 := λ _ ι17 _, ι17.

Definition arr17 : Ty17 → Ty17 → Ty17
 := λ A B Ty17 ι17 arr17,
     arr17 (A Ty17 ι17 arr17) (B Ty17 ι17 arr17).

Definition Con17 : Set
 := ∀ (Con17  : Set)
      (nil  : Con17)
      (snoc : Con17 → Ty17 → Con17)
    , Con17.

Definition nil17 : Con17
 := λ Con17 nil17 snoc , nil17.

Definition snoc17 : Con17 → Ty17 → Con17
 := λ Γ A Con17 nil17 snoc17 , snoc17 (Γ Con17 nil17 snoc17) A.

Definition Var17 : Con17 → Ty17 → Set
 := λ Γ A ,
   ∀ (Var17 : Con17 → Ty17 → Set)
     (vz  : ∀ Γ A, Var17 (snoc17 Γ A) A)
     (vs  : ∀ Γ B A, Var17 Γ A → Var17 (snoc17 Γ B) A)
   , Var17 Γ A.

Definition vz17 {Γ A} : Var17 (snoc17 Γ A) A
 := λ Var17 vz17 vs , vz17 _ _.

Definition vs17 {Γ B A} : Var17 Γ A → Var17 (snoc17 Γ B) A
 := λ x Var17 vz17 vs17 , vs17 _ _ _ (x Var17 vz17 vs17).

Definition Tm17 : Con17 → Ty17 → Set
 := λ Γ A ,
   ∀ (Tm17  : Con17 → Ty17 → Set)
     (var   : ∀ Γ A     , Var17 Γ A → Tm17 Γ A)
     (lam   : ∀ Γ A B   , Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B))
     (app   : ∀ Γ A B   , Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B)
   , Tm17 Γ A.

Definition var17 {Γ A} : Var17 Γ A → Tm17 Γ A
 := λ x Tm17 var17 lam app,
     var17 _ _ x.

Definition lam17 {Γ A B} : Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B)
 := λ t Tm17 var17 lam17 app,
     lam17 _ _ _ (t Tm17 var17 lam17 app).

Definition app17 {Γ A B} : Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B
 := λ t u Tm17 var17 lam17 app17,
     app17 _ _ _
         (t Tm17 var17 lam17 app17)
         (u Tm17 var17 lam17 app17).

Definition v017 {Γ A} : Tm17 (snoc17 Γ A) A
 := var17 vz17.

Definition v117 {Γ A B} : Tm17 (snoc17 (snoc17 Γ A) B) A
 := var17 (vs17 vz17).

Definition v217 {Γ A B C} : Tm17 (snoc17 (snoc17 (snoc17 Γ A) B) C) A
 := var17 (vs17 (vs17 vz17)).

Definition v317 {Γ A B C D} : Tm17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) A
 := var17 (vs17 (vs17 (vs17 vz17))).

Definition v417 {Γ A B C D E} : Tm17 (snoc17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) E) A
 := var17 (vs17 (vs17 (vs17 (vs17 vz17)))).

Definition test17 {Γ A} : Tm17 Γ (arr17 (arr17 A A) (arr17 A A))
 := lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty18 : Set
 := ∀ (Ty18 : Set)
      (ι   : Ty18)
      (arr : Ty18 → Ty18 → Ty18)
    , Ty18.

Definition ι18 : Ty18 := λ _ ι18 _, ι18.

Definition arr18 : Ty18 → Ty18 → Ty18
 := λ A B Ty18 ι18 arr18,
     arr18 (A Ty18 ι18 arr18) (B Ty18 ι18 arr18).

Definition Con18 : Set
 := ∀ (Con18  : Set)
      (nil  : Con18)
      (snoc : Con18 → Ty18 → Con18)
    , Con18.

Definition nil18 : Con18
 := λ Con18 nil18 snoc , nil18.

Definition snoc18 : Con18 → Ty18 → Con18
 := λ Γ A Con18 nil18 snoc18 , snoc18 (Γ Con18 nil18 snoc18) A.

Definition Var18 : Con18 → Ty18 → Set
 := λ Γ A ,
   ∀ (Var18 : Con18 → Ty18 → Set)
     (vz  : ∀ Γ A, Var18 (snoc18 Γ A) A)
     (vs  : ∀ Γ B A, Var18 Γ A → Var18 (snoc18 Γ B) A)
   , Var18 Γ A.

Definition vz18 {Γ A} : Var18 (snoc18 Γ A) A
 := λ Var18 vz18 vs , vz18 _ _.

Definition vs18 {Γ B A} : Var18 Γ A → Var18 (snoc18 Γ B) A
 := λ x Var18 vz18 vs18 , vs18 _ _ _ (x Var18 vz18 vs18).

Definition Tm18 : Con18 → Ty18 → Set
 := λ Γ A ,
   ∀ (Tm18  : Con18 → Ty18 → Set)
     (var   : ∀ Γ A     , Var18 Γ A → Tm18 Γ A)
     (lam   : ∀ Γ A B   , Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B))
     (app   : ∀ Γ A B   , Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B)
   , Tm18 Γ A.

Definition var18 {Γ A} : Var18 Γ A → Tm18 Γ A
 := λ x Tm18 var18 lam app,
     var18 _ _ x.

Definition lam18 {Γ A B} : Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B)
 := λ t Tm18 var18 lam18 app,
     lam18 _ _ _ (t Tm18 var18 lam18 app).

Definition app18 {Γ A B} : Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B
 := λ t u Tm18 var18 lam18 app18,
     app18 _ _ _
         (t Tm18 var18 lam18 app18)
         (u Tm18 var18 lam18 app18).

Definition v018 {Γ A} : Tm18 (snoc18 Γ A) A
 := var18 vz18.

Definition v118 {Γ A B} : Tm18 (snoc18 (snoc18 Γ A) B) A
 := var18 (vs18 vz18).

Definition v218 {Γ A B C} : Tm18 (snoc18 (snoc18 (snoc18 Γ A) B) C) A
 := var18 (vs18 (vs18 vz18)).

Definition v318 {Γ A B C D} : Tm18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) A
 := var18 (vs18 (vs18 (vs18 vz18))).

Definition v418 {Γ A B C D E} : Tm18 (snoc18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) E) A
 := var18 (vs18 (vs18 (vs18 (vs18 vz18)))).

Definition test18 {Γ A} : Tm18 Γ (arr18 (arr18 A A) (arr18 A A))
 := lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty19 : Set
 := ∀ (Ty19 : Set)
      (ι   : Ty19)
      (arr : Ty19 → Ty19 → Ty19)
    , Ty19.

Definition ι19 : Ty19 := λ _ ι19 _, ι19.

Definition arr19 : Ty19 → Ty19 → Ty19
 := λ A B Ty19 ι19 arr19,
     arr19 (A Ty19 ι19 arr19) (B Ty19 ι19 arr19).

Definition Con19 : Set
 := ∀ (Con19  : Set)
      (nil  : Con19)
      (snoc : Con19 → Ty19 → Con19)
    , Con19.

Definition nil19 : Con19
 := λ Con19 nil19 snoc , nil19.

Definition snoc19 : Con19 → Ty19 → Con19
 := λ Γ A Con19 nil19 snoc19 , snoc19 (Γ Con19 nil19 snoc19) A.

Definition Var19 : Con19 → Ty19 → Set
 := λ Γ A ,
   ∀ (Var19 : Con19 → Ty19 → Set)
     (vz  : ∀ Γ A, Var19 (snoc19 Γ A) A)
     (vs  : ∀ Γ B A, Var19 Γ A → Var19 (snoc19 Γ B) A)
   , Var19 Γ A.

Definition vz19 {Γ A} : Var19 (snoc19 Γ A) A
 := λ Var19 vz19 vs , vz19 _ _.

Definition vs19 {Γ B A} : Var19 Γ A → Var19 (snoc19 Γ B) A
 := λ x Var19 vz19 vs19 , vs19 _ _ _ (x Var19 vz19 vs19).

Definition Tm19 : Con19 → Ty19 → Set
 := λ Γ A ,
   ∀ (Tm19  : Con19 → Ty19 → Set)
     (var   : ∀ Γ A     , Var19 Γ A → Tm19 Γ A)
     (lam   : ∀ Γ A B   , Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B))
     (app   : ∀ Γ A B   , Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B)
   , Tm19 Γ A.

Definition var19 {Γ A} : Var19 Γ A → Tm19 Γ A
 := λ x Tm19 var19 lam app,
     var19 _ _ x.

Definition lam19 {Γ A B} : Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B)
 := λ t Tm19 var19 lam19 app,
     lam19 _ _ _ (t Tm19 var19 lam19 app).

Definition app19 {Γ A B} : Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B
 := λ t u Tm19 var19 lam19 app19,
     app19 _ _ _
         (t Tm19 var19 lam19 app19)
         (u Tm19 var19 lam19 app19).

Definition v019 {Γ A} : Tm19 (snoc19 Γ A) A
 := var19 vz19.

Definition v119 {Γ A B} : Tm19 (snoc19 (snoc19 Γ A) B) A
 := var19 (vs19 vz19).

Definition v219 {Γ A B C} : Tm19 (snoc19 (snoc19 (snoc19 Γ A) B) C) A
 := var19 (vs19 (vs19 vz19)).

Definition v319 {Γ A B C D} : Tm19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) A
 := var19 (vs19 (vs19 (vs19 vz19))).

Definition v419 {Γ A B C D E} : Tm19 (snoc19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) E) A
 := var19 (vs19 (vs19 (vs19 (vs19 vz19)))).

Definition test19 {Γ A} : Tm19 Γ (arr19 (arr19 A A) (arr19 A A))
 := lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty20 : Set
 := ∀ (Ty20 : Set)
      (ι   : Ty20)
      (arr : Ty20 → Ty20 → Ty20)
    , Ty20.

Definition ι20 : Ty20 := λ _ ι20 _, ι20.

Definition arr20 : Ty20 → Ty20 → Ty20
 := λ A B Ty20 ι20 arr20,
     arr20 (A Ty20 ι20 arr20) (B Ty20 ι20 arr20).

Definition Con20 : Set
 := ∀ (Con20  : Set)
      (nil  : Con20)
      (snoc : Con20 → Ty20 → Con20)
    , Con20.

Definition nil20 : Con20
 := λ Con20 nil20 snoc , nil20.

Definition snoc20 : Con20 → Ty20 → Con20
 := λ Γ A Con20 nil20 snoc20 , snoc20 (Γ Con20 nil20 snoc20) A.

Definition Var20 : Con20 → Ty20 → Set
 := λ Γ A ,
   ∀ (Var20 : Con20 → Ty20 → Set)
     (vz  : ∀ Γ A, Var20 (snoc20 Γ A) A)
     (vs  : ∀ Γ B A, Var20 Γ A → Var20 (snoc20 Γ B) A)
   , Var20 Γ A.

Definition vz20 {Γ A} : Var20 (snoc20 Γ A) A
 := λ Var20 vz20 vs , vz20 _ _.

Definition vs20 {Γ B A} : Var20 Γ A → Var20 (snoc20 Γ B) A
 := λ x Var20 vz20 vs20 , vs20 _ _ _ (x Var20 vz20 vs20).

Definition Tm20 : Con20 → Ty20 → Set
 := λ Γ A ,
   ∀ (Tm20  : Con20 → Ty20 → Set)
     (var   : ∀ Γ A     , Var20 Γ A → Tm20 Γ A)
     (lam   : ∀ Γ A B   , Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B))
     (app   : ∀ Γ A B   , Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B)
   , Tm20 Γ A.

Definition var20 {Γ A} : Var20 Γ A → Tm20 Γ A
 := λ x Tm20 var20 lam app,
     var20 _ _ x.

Definition lam20 {Γ A B} : Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B)
 := λ t Tm20 var20 lam20 app,
     lam20 _ _ _ (t Tm20 var20 lam20 app).

Definition app20 {Γ A B} : Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B
 := λ t u Tm20 var20 lam20 app20,
     app20 _ _ _
         (t Tm20 var20 lam20 app20)
         (u Tm20 var20 lam20 app20).

Definition v020 {Γ A} : Tm20 (snoc20 Γ A) A
 := var20 vz20.

Definition v120 {Γ A B} : Tm20 (snoc20 (snoc20 Γ A) B) A
 := var20 (vs20 vz20).

Definition v220 {Γ A B C} : Tm20 (snoc20 (snoc20 (snoc20 Γ A) B) C) A
 := var20 (vs20 (vs20 vz20)).

Definition v320 {Γ A B C D} : Tm20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) A
 := var20 (vs20 (vs20 (vs20 vz20))).

Definition v420 {Γ A B C D E} : Tm20 (snoc20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) E) A
 := var20 (vs20 (vs20 (vs20 (vs20 vz20)))).

Definition test20 {Γ A} : Tm20 Γ (arr20 (arr20 A A) (arr20 A A))
 := lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty21 : Set
 := ∀ (Ty21 : Set)
      (ι   : Ty21)
      (arr : Ty21 → Ty21 → Ty21)
    , Ty21.

Definition ι21 : Ty21 := λ _ ι21 _, ι21.

Definition arr21 : Ty21 → Ty21 → Ty21
 := λ A B Ty21 ι21 arr21,
     arr21 (A Ty21 ι21 arr21) (B Ty21 ι21 arr21).

Definition Con21 : Set
 := ∀ (Con21  : Set)
      (nil  : Con21)
      (snoc : Con21 → Ty21 → Con21)
    , Con21.

Definition nil21 : Con21
 := λ Con21 nil21 snoc , nil21.

Definition snoc21 : Con21 → Ty21 → Con21
 := λ Γ A Con21 nil21 snoc21 , snoc21 (Γ Con21 nil21 snoc21) A.

Definition Var21 : Con21 → Ty21 → Set
 := λ Γ A ,
   ∀ (Var21 : Con21 → Ty21 → Set)
     (vz  : ∀ Γ A, Var21 (snoc21 Γ A) A)
     (vs  : ∀ Γ B A, Var21 Γ A → Var21 (snoc21 Γ B) A)
   , Var21 Γ A.

Definition vz21 {Γ A} : Var21 (snoc21 Γ A) A
 := λ Var21 vz21 vs , vz21 _ _.

Definition vs21 {Γ B A} : Var21 Γ A → Var21 (snoc21 Γ B) A
 := λ x Var21 vz21 vs21 , vs21 _ _ _ (x Var21 vz21 vs21).

Definition Tm21 : Con21 → Ty21 → Set
 := λ Γ A ,
   ∀ (Tm21  : Con21 → Ty21 → Set)
     (var   : ∀ Γ A     , Var21 Γ A → Tm21 Γ A)
     (lam   : ∀ Γ A B   , Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B))
     (app   : ∀ Γ A B   , Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B)
   , Tm21 Γ A.

Definition var21 {Γ A} : Var21 Γ A → Tm21 Γ A
 := λ x Tm21 var21 lam app,
     var21 _ _ x.

Definition lam21 {Γ A B} : Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B)
 := λ t Tm21 var21 lam21 app,
     lam21 _ _ _ (t Tm21 var21 lam21 app).

Definition app21 {Γ A B} : Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B
 := λ t u Tm21 var21 lam21 app21,
     app21 _ _ _
         (t Tm21 var21 lam21 app21)
         (u Tm21 var21 lam21 app21).

Definition v021 {Γ A} : Tm21 (snoc21 Γ A) A
 := var21 vz21.

Definition v121 {Γ A B} : Tm21 (snoc21 (snoc21 Γ A) B) A
 := var21 (vs21 vz21).

Definition v221 {Γ A B C} : Tm21 (snoc21 (snoc21 (snoc21 Γ A) B) C) A
 := var21 (vs21 (vs21 vz21)).

Definition v321 {Γ A B C D} : Tm21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) A
 := var21 (vs21 (vs21 (vs21 vz21))).

Definition v421 {Γ A B C D E} : Tm21 (snoc21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) E) A
 := var21 (vs21 (vs21 (vs21 (vs21 vz21)))).

Definition test21 {Γ A} : Tm21 Γ (arr21 (arr21 A A) (arr21 A A))
 := lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty22 : Set
 := ∀ (Ty22 : Set)
      (ι   : Ty22)
      (arr : Ty22 → Ty22 → Ty22)
    , Ty22.

Definition ι22 : Ty22 := λ _ ι22 _, ι22.

Definition arr22 : Ty22 → Ty22 → Ty22
 := λ A B Ty22 ι22 arr22,
     arr22 (A Ty22 ι22 arr22) (B Ty22 ι22 arr22).

Definition Con22 : Set
 := ∀ (Con22  : Set)
      (nil  : Con22)
      (snoc : Con22 → Ty22 → Con22)
    , Con22.

Definition nil22 : Con22
 := λ Con22 nil22 snoc , nil22.

Definition snoc22 : Con22 → Ty22 → Con22
 := λ Γ A Con22 nil22 snoc22 , snoc22 (Γ Con22 nil22 snoc22) A.

Definition Var22 : Con22 → Ty22 → Set
 := λ Γ A ,
   ∀ (Var22 : Con22 → Ty22 → Set)
     (vz  : ∀ Γ A, Var22 (snoc22 Γ A) A)
     (vs  : ∀ Γ B A, Var22 Γ A → Var22 (snoc22 Γ B) A)
   , Var22 Γ A.

Definition vz22 {Γ A} : Var22 (snoc22 Γ A) A
 := λ Var22 vz22 vs , vz22 _ _.

Definition vs22 {Γ B A} : Var22 Γ A → Var22 (snoc22 Γ B) A
 := λ x Var22 vz22 vs22 , vs22 _ _ _ (x Var22 vz22 vs22).

Definition Tm22 : Con22 → Ty22 → Set
 := λ Γ A ,
   ∀ (Tm22  : Con22 → Ty22 → Set)
     (var   : ∀ Γ A     , Var22 Γ A → Tm22 Γ A)
     (lam   : ∀ Γ A B   , Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B))
     (app   : ∀ Γ A B   , Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B)
   , Tm22 Γ A.

Definition var22 {Γ A} : Var22 Γ A → Tm22 Γ A
 := λ x Tm22 var22 lam app,
     var22 _ _ x.

Definition lam22 {Γ A B} : Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B)
 := λ t Tm22 var22 lam22 app,
     lam22 _ _ _ (t Tm22 var22 lam22 app).

Definition app22 {Γ A B} : Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B
 := λ t u Tm22 var22 lam22 app22,
     app22 _ _ _
         (t Tm22 var22 lam22 app22)
         (u Tm22 var22 lam22 app22).

Definition v022 {Γ A} : Tm22 (snoc22 Γ A) A
 := var22 vz22.

Definition v122 {Γ A B} : Tm22 (snoc22 (snoc22 Γ A) B) A
 := var22 (vs22 vz22).

Definition v222 {Γ A B C} : Tm22 (snoc22 (snoc22 (snoc22 Γ A) B) C) A
 := var22 (vs22 (vs22 vz22)).

Definition v322 {Γ A B C D} : Tm22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) A
 := var22 (vs22 (vs22 (vs22 vz22))).

Definition v422 {Γ A B C D E} : Tm22 (snoc22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) E) A
 := var22 (vs22 (vs22 (vs22 (vs22 vz22)))).

Definition test22 {Γ A} : Tm22 Γ (arr22 (arr22 A A) (arr22 A A))
 := lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty23 : Set
 := ∀ (Ty23 : Set)
      (ι   : Ty23)
      (arr : Ty23 → Ty23 → Ty23)
    , Ty23.

Definition ι23 : Ty23 := λ _ ι23 _, ι23.

Definition arr23 : Ty23 → Ty23 → Ty23
 := λ A B Ty23 ι23 arr23,
     arr23 (A Ty23 ι23 arr23) (B Ty23 ι23 arr23).

Definition Con23 : Set
 := ∀ (Con23  : Set)
      (nil  : Con23)
      (snoc : Con23 → Ty23 → Con23)
    , Con23.

Definition nil23 : Con23
 := λ Con23 nil23 snoc , nil23.

Definition snoc23 : Con23 → Ty23 → Con23
 := λ Γ A Con23 nil23 snoc23 , snoc23 (Γ Con23 nil23 snoc23) A.

Definition Var23 : Con23 → Ty23 → Set
 := λ Γ A ,
   ∀ (Var23 : Con23 → Ty23 → Set)
     (vz  : ∀ Γ A, Var23 (snoc23 Γ A) A)
     (vs  : ∀ Γ B A, Var23 Γ A → Var23 (snoc23 Γ B) A)
   , Var23 Γ A.

Definition vz23 {Γ A} : Var23 (snoc23 Γ A) A
 := λ Var23 vz23 vs , vz23 _ _.

Definition vs23 {Γ B A} : Var23 Γ A → Var23 (snoc23 Γ B) A
 := λ x Var23 vz23 vs23 , vs23 _ _ _ (x Var23 vz23 vs23).

Definition Tm23 : Con23 → Ty23 → Set
 := λ Γ A ,
   ∀ (Tm23  : Con23 → Ty23 → Set)
     (var   : ∀ Γ A     , Var23 Γ A → Tm23 Γ A)
     (lam   : ∀ Γ A B   , Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B))
     (app   : ∀ Γ A B   , Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B)
   , Tm23 Γ A.

Definition var23 {Γ A} : Var23 Γ A → Tm23 Γ A
 := λ x Tm23 var23 lam app,
     var23 _ _ x.

Definition lam23 {Γ A B} : Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B)
 := λ t Tm23 var23 lam23 app,
     lam23 _ _ _ (t Tm23 var23 lam23 app).

Definition app23 {Γ A B} : Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B
 := λ t u Tm23 var23 lam23 app23,
     app23 _ _ _
         (t Tm23 var23 lam23 app23)
         (u Tm23 var23 lam23 app23).

Definition v023 {Γ A} : Tm23 (snoc23 Γ A) A
 := var23 vz23.

Definition v123 {Γ A B} : Tm23 (snoc23 (snoc23 Γ A) B) A
 := var23 (vs23 vz23).

Definition v223 {Γ A B C} : Tm23 (snoc23 (snoc23 (snoc23 Γ A) B) C) A
 := var23 (vs23 (vs23 vz23)).

Definition v323 {Γ A B C D} : Tm23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) A
 := var23 (vs23 (vs23 (vs23 vz23))).

Definition v423 {Γ A B C D E} : Tm23 (snoc23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) E) A
 := var23 (vs23 (vs23 (vs23 (vs23 vz23)))).

Definition test23 {Γ A} : Tm23 Γ (arr23 (arr23 A A) (arr23 A A))
 := lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty24 : Set
 := ∀ (Ty24 : Set)
      (ι   : Ty24)
      (arr : Ty24 → Ty24 → Ty24)
    , Ty24.

Definition ι24 : Ty24 := λ _ ι24 _, ι24.

Definition arr24 : Ty24 → Ty24 → Ty24
 := λ A B Ty24 ι24 arr24,
     arr24 (A Ty24 ι24 arr24) (B Ty24 ι24 arr24).

Definition Con24 : Set
 := ∀ (Con24  : Set)
      (nil  : Con24)
      (snoc : Con24 → Ty24 → Con24)
    , Con24.

Definition nil24 : Con24
 := λ Con24 nil24 snoc , nil24.

Definition snoc24 : Con24 → Ty24 → Con24
 := λ Γ A Con24 nil24 snoc24 , snoc24 (Γ Con24 nil24 snoc24) A.

Definition Var24 : Con24 → Ty24 → Set
 := λ Γ A ,
   ∀ (Var24 : Con24 → Ty24 → Set)
     (vz  : ∀ Γ A, Var24 (snoc24 Γ A) A)
     (vs  : ∀ Γ B A, Var24 Γ A → Var24 (snoc24 Γ B) A)
   , Var24 Γ A.

Definition vz24 {Γ A} : Var24 (snoc24 Γ A) A
 := λ Var24 vz24 vs , vz24 _ _.

Definition vs24 {Γ B A} : Var24 Γ A → Var24 (snoc24 Γ B) A
 := λ x Var24 vz24 vs24 , vs24 _ _ _ (x Var24 vz24 vs24).

Definition Tm24 : Con24 → Ty24 → Set
 := λ Γ A ,
   ∀ (Tm24  : Con24 → Ty24 → Set)
     (var   : ∀ Γ A     , Var24 Γ A → Tm24 Γ A)
     (lam   : ∀ Γ A B   , Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B))
     (app   : ∀ Γ A B   , Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B)
   , Tm24 Γ A.

Definition var24 {Γ A} : Var24 Γ A → Tm24 Γ A
 := λ x Tm24 var24 lam app,
     var24 _ _ x.

Definition lam24 {Γ A B} : Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B)
 := λ t Tm24 var24 lam24 app,
     lam24 _ _ _ (t Tm24 var24 lam24 app).

Definition app24 {Γ A B} : Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B
 := λ t u Tm24 var24 lam24 app24,
     app24 _ _ _
         (t Tm24 var24 lam24 app24)
         (u Tm24 var24 lam24 app24).

Definition v024 {Γ A} : Tm24 (snoc24 Γ A) A
 := var24 vz24.

Definition v124 {Γ A B} : Tm24 (snoc24 (snoc24 Γ A) B) A
 := var24 (vs24 vz24).

Definition v224 {Γ A B C} : Tm24 (snoc24 (snoc24 (snoc24 Γ A) B) C) A
 := var24 (vs24 (vs24 vz24)).

Definition v324 {Γ A B C D} : Tm24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) A
 := var24 (vs24 (vs24 (vs24 vz24))).

Definition v424 {Γ A B C D E} : Tm24 (snoc24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) E) A
 := var24 (vs24 (vs24 (vs24 (vs24 vz24)))).

Definition test24 {Γ A} : Tm24 Γ (arr24 (arr24 A A) (arr24 A A))
 := lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty25 : Set
 := ∀ (Ty25 : Set)
      (ι   : Ty25)
      (arr : Ty25 → Ty25 → Ty25)
    , Ty25.

Definition ι25 : Ty25 := λ _ ι25 _, ι25.

Definition arr25 : Ty25 → Ty25 → Ty25
 := λ A B Ty25 ι25 arr25,
     arr25 (A Ty25 ι25 arr25) (B Ty25 ι25 arr25).

Definition Con25 : Set
 := ∀ (Con25  : Set)
      (nil  : Con25)
      (snoc : Con25 → Ty25 → Con25)
    , Con25.

Definition nil25 : Con25
 := λ Con25 nil25 snoc , nil25.

Definition snoc25 : Con25 → Ty25 → Con25
 := λ Γ A Con25 nil25 snoc25 , snoc25 (Γ Con25 nil25 snoc25) A.

Definition Var25 : Con25 → Ty25 → Set
 := λ Γ A ,
   ∀ (Var25 : Con25 → Ty25 → Set)
     (vz  : ∀ Γ A, Var25 (snoc25 Γ A) A)
     (vs  : ∀ Γ B A, Var25 Γ A → Var25 (snoc25 Γ B) A)
   , Var25 Γ A.

Definition vz25 {Γ A} : Var25 (snoc25 Γ A) A
 := λ Var25 vz25 vs , vz25 _ _.

Definition vs25 {Γ B A} : Var25 Γ A → Var25 (snoc25 Γ B) A
 := λ x Var25 vz25 vs25 , vs25 _ _ _ (x Var25 vz25 vs25).

Definition Tm25 : Con25 → Ty25 → Set
 := λ Γ A ,
   ∀ (Tm25  : Con25 → Ty25 → Set)
     (var   : ∀ Γ A     , Var25 Γ A → Tm25 Γ A)
     (lam   : ∀ Γ A B   , Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B))
     (app   : ∀ Γ A B   , Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B)
   , Tm25 Γ A.

Definition var25 {Γ A} : Var25 Γ A → Tm25 Γ A
 := λ x Tm25 var25 lam app,
     var25 _ _ x.

Definition lam25 {Γ A B} : Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B)
 := λ t Tm25 var25 lam25 app,
     lam25 _ _ _ (t Tm25 var25 lam25 app).

Definition app25 {Γ A B} : Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B
 := λ t u Tm25 var25 lam25 app25,
     app25 _ _ _
         (t Tm25 var25 lam25 app25)
         (u Tm25 var25 lam25 app25).

Definition v025 {Γ A} : Tm25 (snoc25 Γ A) A
 := var25 vz25.

Definition v125 {Γ A B} : Tm25 (snoc25 (snoc25 Γ A) B) A
 := var25 (vs25 vz25).

Definition v225 {Γ A B C} : Tm25 (snoc25 (snoc25 (snoc25 Γ A) B) C) A
 := var25 (vs25 (vs25 vz25)).

Definition v325 {Γ A B C D} : Tm25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) A
 := var25 (vs25 (vs25 (vs25 vz25))).

Definition v425 {Γ A B C D E} : Tm25 (snoc25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) E) A
 := var25 (vs25 (vs25 (vs25 (vs25 vz25)))).

Definition test25 {Γ A} : Tm25 Γ (arr25 (arr25 A A) (arr25 A A))
 := lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty26 : Set
 := ∀ (Ty26 : Set)
      (ι   : Ty26)
      (arr : Ty26 → Ty26 → Ty26)
    , Ty26.

Definition ι26 : Ty26 := λ _ ι26 _, ι26.

Definition arr26 : Ty26 → Ty26 → Ty26
 := λ A B Ty26 ι26 arr26,
     arr26 (A Ty26 ι26 arr26) (B Ty26 ι26 arr26).

Definition Con26 : Set
 := ∀ (Con26  : Set)
      (nil  : Con26)
      (snoc : Con26 → Ty26 → Con26)
    , Con26.

Definition nil26 : Con26
 := λ Con26 nil26 snoc , nil26.

Definition snoc26 : Con26 → Ty26 → Con26
 := λ Γ A Con26 nil26 snoc26 , snoc26 (Γ Con26 nil26 snoc26) A.

Definition Var26 : Con26 → Ty26 → Set
 := λ Γ A ,
   ∀ (Var26 : Con26 → Ty26 → Set)
     (vz  : ∀ Γ A, Var26 (snoc26 Γ A) A)
     (vs  : ∀ Γ B A, Var26 Γ A → Var26 (snoc26 Γ B) A)
   , Var26 Γ A.

Definition vz26 {Γ A} : Var26 (snoc26 Γ A) A
 := λ Var26 vz26 vs , vz26 _ _.

Definition vs26 {Γ B A} : Var26 Γ A → Var26 (snoc26 Γ B) A
 := λ x Var26 vz26 vs26 , vs26 _ _ _ (x Var26 vz26 vs26).

Definition Tm26 : Con26 → Ty26 → Set
 := λ Γ A ,
   ∀ (Tm26  : Con26 → Ty26 → Set)
     (var   : ∀ Γ A     , Var26 Γ A → Tm26 Γ A)
     (lam   : ∀ Γ A B   , Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B))
     (app   : ∀ Γ A B   , Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B)
   , Tm26 Γ A.

Definition var26 {Γ A} : Var26 Γ A → Tm26 Γ A
 := λ x Tm26 var26 lam app,
     var26 _ _ x.

Definition lam26 {Γ A B} : Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B)
 := λ t Tm26 var26 lam26 app,
     lam26 _ _ _ (t Tm26 var26 lam26 app).

Definition app26 {Γ A B} : Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B
 := λ t u Tm26 var26 lam26 app26,
     app26 _ _ _
         (t Tm26 var26 lam26 app26)
         (u Tm26 var26 lam26 app26).

Definition v026 {Γ A} : Tm26 (snoc26 Γ A) A
 := var26 vz26.

Definition v126 {Γ A B} : Tm26 (snoc26 (snoc26 Γ A) B) A
 := var26 (vs26 vz26).

Definition v226 {Γ A B C} : Tm26 (snoc26 (snoc26 (snoc26 Γ A) B) C) A
 := var26 (vs26 (vs26 vz26)).

Definition v326 {Γ A B C D} : Tm26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) A
 := var26 (vs26 (vs26 (vs26 vz26))).

Definition v426 {Γ A B C D E} : Tm26 (snoc26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) E) A
 := var26 (vs26 (vs26 (vs26 (vs26 vz26)))).

Definition test26 {Γ A} : Tm26 Γ (arr26 (arr26 A A) (arr26 A A))
 := lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty27 : Set
 := ∀ (Ty27 : Set)
      (ι   : Ty27)
      (arr : Ty27 → Ty27 → Ty27)
    , Ty27.

Definition ι27 : Ty27 := λ _ ι27 _, ι27.

Definition arr27 : Ty27 → Ty27 → Ty27
 := λ A B Ty27 ι27 arr27,
     arr27 (A Ty27 ι27 arr27) (B Ty27 ι27 arr27).

Definition Con27 : Set
 := ∀ (Con27  : Set)
      (nil  : Con27)
      (snoc : Con27 → Ty27 → Con27)
    , Con27.

Definition nil27 : Con27
 := λ Con27 nil27 snoc , nil27.

Definition snoc27 : Con27 → Ty27 → Con27
 := λ Γ A Con27 nil27 snoc27 , snoc27 (Γ Con27 nil27 snoc27) A.

Definition Var27 : Con27 → Ty27 → Set
 := λ Γ A ,
   ∀ (Var27 : Con27 → Ty27 → Set)
     (vz  : ∀ Γ A, Var27 (snoc27 Γ A) A)
     (vs  : ∀ Γ B A, Var27 Γ A → Var27 (snoc27 Γ B) A)
   , Var27 Γ A.

Definition vz27 {Γ A} : Var27 (snoc27 Γ A) A
 := λ Var27 vz27 vs , vz27 _ _.

Definition vs27 {Γ B A} : Var27 Γ A → Var27 (snoc27 Γ B) A
 := λ x Var27 vz27 vs27 , vs27 _ _ _ (x Var27 vz27 vs27).

Definition Tm27 : Con27 → Ty27 → Set
 := λ Γ A ,
   ∀ (Tm27  : Con27 → Ty27 → Set)
     (var   : ∀ Γ A     , Var27 Γ A → Tm27 Γ A)
     (lam   : ∀ Γ A B   , Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B))
     (app   : ∀ Γ A B   , Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B)
   , Tm27 Γ A.

Definition var27 {Γ A} : Var27 Γ A → Tm27 Γ A
 := λ x Tm27 var27 lam app,
     var27 _ _ x.

Definition lam27 {Γ A B} : Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B)
 := λ t Tm27 var27 lam27 app,
     lam27 _ _ _ (t Tm27 var27 lam27 app).

Definition app27 {Γ A B} : Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B
 := λ t u Tm27 var27 lam27 app27,
     app27 _ _ _
         (t Tm27 var27 lam27 app27)
         (u Tm27 var27 lam27 app27).

Definition v027 {Γ A} : Tm27 (snoc27 Γ A) A
 := var27 vz27.

Definition v127 {Γ A B} : Tm27 (snoc27 (snoc27 Γ A) B) A
 := var27 (vs27 vz27).

Definition v227 {Γ A B C} : Tm27 (snoc27 (snoc27 (snoc27 Γ A) B) C) A
 := var27 (vs27 (vs27 vz27)).

Definition v327 {Γ A B C D} : Tm27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) A
 := var27 (vs27 (vs27 (vs27 vz27))).

Definition v427 {Γ A B C D E} : Tm27 (snoc27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) E) A
 := var27 (vs27 (vs27 (vs27 (vs27 vz27)))).

Definition test27 {Γ A} : Tm27 Γ (arr27 (arr27 A A) (arr27 A A))
 := lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty28 : Set
 := ∀ (Ty28 : Set)
      (ι   : Ty28)
      (arr : Ty28 → Ty28 → Ty28)
    , Ty28.

Definition ι28 : Ty28 := λ _ ι28 _, ι28.

Definition arr28 : Ty28 → Ty28 → Ty28
 := λ A B Ty28 ι28 arr28,
     arr28 (A Ty28 ι28 arr28) (B Ty28 ι28 arr28).

Definition Con28 : Set
 := ∀ (Con28  : Set)
      (nil  : Con28)
      (snoc : Con28 → Ty28 → Con28)
    , Con28.

Definition nil28 : Con28
 := λ Con28 nil28 snoc , nil28.

Definition snoc28 : Con28 → Ty28 → Con28
 := λ Γ A Con28 nil28 snoc28 , snoc28 (Γ Con28 nil28 snoc28) A.

Definition Var28 : Con28 → Ty28 → Set
 := λ Γ A ,
   ∀ (Var28 : Con28 → Ty28 → Set)
     (vz  : ∀ Γ A, Var28 (snoc28 Γ A) A)
     (vs  : ∀ Γ B A, Var28 Γ A → Var28 (snoc28 Γ B) A)
   , Var28 Γ A.

Definition vz28 {Γ A} : Var28 (snoc28 Γ A) A
 := λ Var28 vz28 vs , vz28 _ _.

Definition vs28 {Γ B A} : Var28 Γ A → Var28 (snoc28 Γ B) A
 := λ x Var28 vz28 vs28 , vs28 _ _ _ (x Var28 vz28 vs28).

Definition Tm28 : Con28 → Ty28 → Set
 := λ Γ A ,
   ∀ (Tm28  : Con28 → Ty28 → Set)
     (var   : ∀ Γ A     , Var28 Γ A → Tm28 Γ A)
     (lam   : ∀ Γ A B   , Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B))
     (app   : ∀ Γ A B   , Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B)
   , Tm28 Γ A.

Definition var28 {Γ A} : Var28 Γ A → Tm28 Γ A
 := λ x Tm28 var28 lam app,
     var28 _ _ x.

Definition lam28 {Γ A B} : Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B)
 := λ t Tm28 var28 lam28 app,
     lam28 _ _ _ (t Tm28 var28 lam28 app).

Definition app28 {Γ A B} : Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B
 := λ t u Tm28 var28 lam28 app28,
     app28 _ _ _
         (t Tm28 var28 lam28 app28)
         (u Tm28 var28 lam28 app28).

Definition v028 {Γ A} : Tm28 (snoc28 Γ A) A
 := var28 vz28.

Definition v128 {Γ A B} : Tm28 (snoc28 (snoc28 Γ A) B) A
 := var28 (vs28 vz28).

Definition v228 {Γ A B C} : Tm28 (snoc28 (snoc28 (snoc28 Γ A) B) C) A
 := var28 (vs28 (vs28 vz28)).

Definition v328 {Γ A B C D} : Tm28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) A
 := var28 (vs28 (vs28 (vs28 vz28))).

Definition v428 {Γ A B C D E} : Tm28 (snoc28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) E) A
 := var28 (vs28 (vs28 (vs28 (vs28 vz28)))).

Definition test28 {Γ A} : Tm28 Γ (arr28 (arr28 A A) (arr28 A A))
 := lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty29 : Set
 := ∀ (Ty29 : Set)
      (ι   : Ty29)
      (arr : Ty29 → Ty29 → Ty29)
    , Ty29.

Definition ι29 : Ty29 := λ _ ι29 _, ι29.

Definition arr29 : Ty29 → Ty29 → Ty29
 := λ A B Ty29 ι29 arr29,
     arr29 (A Ty29 ι29 arr29) (B Ty29 ι29 arr29).

Definition Con29 : Set
 := ∀ (Con29  : Set)
      (nil  : Con29)
      (snoc : Con29 → Ty29 → Con29)
    , Con29.

Definition nil29 : Con29
 := λ Con29 nil29 snoc , nil29.

Definition snoc29 : Con29 → Ty29 → Con29
 := λ Γ A Con29 nil29 snoc29 , snoc29 (Γ Con29 nil29 snoc29) A.

Definition Var29 : Con29 → Ty29 → Set
 := λ Γ A ,
   ∀ (Var29 : Con29 → Ty29 → Set)
     (vz  : ∀ Γ A, Var29 (snoc29 Γ A) A)
     (vs  : ∀ Γ B A, Var29 Γ A → Var29 (snoc29 Γ B) A)
   , Var29 Γ A.

Definition vz29 {Γ A} : Var29 (snoc29 Γ A) A
 := λ Var29 vz29 vs , vz29 _ _.

Definition vs29 {Γ B A} : Var29 Γ A → Var29 (snoc29 Γ B) A
 := λ x Var29 vz29 vs29 , vs29 _ _ _ (x Var29 vz29 vs29).

Definition Tm29 : Con29 → Ty29 → Set
 := λ Γ A ,
   ∀ (Tm29  : Con29 → Ty29 → Set)
     (var   : ∀ Γ A     , Var29 Γ A → Tm29 Γ A)
     (lam   : ∀ Γ A B   , Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B))
     (app   : ∀ Γ A B   , Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B)
   , Tm29 Γ A.

Definition var29 {Γ A} : Var29 Γ A → Tm29 Γ A
 := λ x Tm29 var29 lam app,
     var29 _ _ x.

Definition lam29 {Γ A B} : Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B)
 := λ t Tm29 var29 lam29 app,
     lam29 _ _ _ (t Tm29 var29 lam29 app).

Definition app29 {Γ A B} : Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B
 := λ t u Tm29 var29 lam29 app29,
     app29 _ _ _
         (t Tm29 var29 lam29 app29)
         (u Tm29 var29 lam29 app29).

Definition v029 {Γ A} : Tm29 (snoc29 Γ A) A
 := var29 vz29.

Definition v129 {Γ A B} : Tm29 (snoc29 (snoc29 Γ A) B) A
 := var29 (vs29 vz29).

Definition v229 {Γ A B C} : Tm29 (snoc29 (snoc29 (snoc29 Γ A) B) C) A
 := var29 (vs29 (vs29 vz29)).

Definition v329 {Γ A B C D} : Tm29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) A
 := var29 (vs29 (vs29 (vs29 vz29))).

Definition v429 {Γ A B C D E} : Tm29 (snoc29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) E) A
 := var29 (vs29 (vs29 (vs29 (vs29 vz29)))).

Definition test29 {Γ A} : Tm29 Γ (arr29 (arr29 A A) (arr29 A A))
 := lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty30 : Set
 := ∀ (Ty30 : Set)
      (ι   : Ty30)
      (arr : Ty30 → Ty30 → Ty30)
    , Ty30.

Definition ι30 : Ty30 := λ _ ι30 _, ι30.

Definition arr30 : Ty30 → Ty30 → Ty30
 := λ A B Ty30 ι30 arr30,
     arr30 (A Ty30 ι30 arr30) (B Ty30 ι30 arr30).

Definition Con30 : Set
 := ∀ (Con30  : Set)
      (nil  : Con30)
      (snoc : Con30 → Ty30 → Con30)
    , Con30.

Definition nil30 : Con30
 := λ Con30 nil30 snoc , nil30.

Definition snoc30 : Con30 → Ty30 → Con30
 := λ Γ A Con30 nil30 snoc30 , snoc30 (Γ Con30 nil30 snoc30) A.

Definition Var30 : Con30 → Ty30 → Set
 := λ Γ A ,
   ∀ (Var30 : Con30 → Ty30 → Set)
     (vz  : ∀ Γ A, Var30 (snoc30 Γ A) A)
     (vs  : ∀ Γ B A, Var30 Γ A → Var30 (snoc30 Γ B) A)
   , Var30 Γ A.

Definition vz30 {Γ A} : Var30 (snoc30 Γ A) A
 := λ Var30 vz30 vs , vz30 _ _.

Definition vs30 {Γ B A} : Var30 Γ A → Var30 (snoc30 Γ B) A
 := λ x Var30 vz30 vs30 , vs30 _ _ _ (x Var30 vz30 vs30).

Definition Tm30 : Con30 → Ty30 → Set
 := λ Γ A ,
   ∀ (Tm30  : Con30 → Ty30 → Set)
     (var   : ∀ Γ A     , Var30 Γ A → Tm30 Γ A)
     (lam   : ∀ Γ A B   , Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B))
     (app   : ∀ Γ A B   , Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B)
   , Tm30 Γ A.

Definition var30 {Γ A} : Var30 Γ A → Tm30 Γ A
 := λ x Tm30 var30 lam app,
     var30 _ _ x.

Definition lam30 {Γ A B} : Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B)
 := λ t Tm30 var30 lam30 app,
     lam30 _ _ _ (t Tm30 var30 lam30 app).

Definition app30 {Γ A B} : Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B
 := λ t u Tm30 var30 lam30 app30,
     app30 _ _ _
         (t Tm30 var30 lam30 app30)
         (u Tm30 var30 lam30 app30).

Definition v030 {Γ A} : Tm30 (snoc30 Γ A) A
 := var30 vz30.

Definition v130 {Γ A B} : Tm30 (snoc30 (snoc30 Γ A) B) A
 := var30 (vs30 vz30).

Definition v230 {Γ A B C} : Tm30 (snoc30 (snoc30 (snoc30 Γ A) B) C) A
 := var30 (vs30 (vs30 vz30)).

Definition v330 {Γ A B C D} : Tm30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) A
 := var30 (vs30 (vs30 (vs30 vz30))).

Definition v430 {Γ A B C D E} : Tm30 (snoc30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) E) A
 := var30 (vs30 (vs30 (vs30 (vs30 vz30)))).

Definition test30 {Γ A} : Tm30 Γ (arr30 (arr30 A A) (arr30 A A))
 := lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty31 : Set
 := ∀ (Ty31 : Set)
      (ι   : Ty31)
      (arr : Ty31 → Ty31 → Ty31)
    , Ty31.

Definition ι31 : Ty31 := λ _ ι31 _, ι31.

Definition arr31 : Ty31 → Ty31 → Ty31
 := λ A B Ty31 ι31 arr31,
     arr31 (A Ty31 ι31 arr31) (B Ty31 ι31 arr31).

Definition Con31 : Set
 := ∀ (Con31  : Set)
      (nil  : Con31)
      (snoc : Con31 → Ty31 → Con31)
    , Con31.

Definition nil31 : Con31
 := λ Con31 nil31 snoc , nil31.

Definition snoc31 : Con31 → Ty31 → Con31
 := λ Γ A Con31 nil31 snoc31 , snoc31 (Γ Con31 nil31 snoc31) A.

Definition Var31 : Con31 → Ty31 → Set
 := λ Γ A ,
   ∀ (Var31 : Con31 → Ty31 → Set)
     (vz  : ∀ Γ A, Var31 (snoc31 Γ A) A)
     (vs  : ∀ Γ B A, Var31 Γ A → Var31 (snoc31 Γ B) A)
   , Var31 Γ A.

Definition vz31 {Γ A} : Var31 (snoc31 Γ A) A
 := λ Var31 vz31 vs , vz31 _ _.

Definition vs31 {Γ B A} : Var31 Γ A → Var31 (snoc31 Γ B) A
 := λ x Var31 vz31 vs31 , vs31 _ _ _ (x Var31 vz31 vs31).

Definition Tm31 : Con31 → Ty31 → Set
 := λ Γ A ,
   ∀ (Tm31  : Con31 → Ty31 → Set)
     (var   : ∀ Γ A     , Var31 Γ A → Tm31 Γ A)
     (lam   : ∀ Γ A B   , Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B))
     (app   : ∀ Γ A B   , Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B)
   , Tm31 Γ A.

Definition var31 {Γ A} : Var31 Γ A → Tm31 Γ A
 := λ x Tm31 var31 lam app,
     var31 _ _ x.

Definition lam31 {Γ A B} : Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B)
 := λ t Tm31 var31 lam31 app,
     lam31 _ _ _ (t Tm31 var31 lam31 app).

Definition app31 {Γ A B} : Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B
 := λ t u Tm31 var31 lam31 app31,
     app31 _ _ _
         (t Tm31 var31 lam31 app31)
         (u Tm31 var31 lam31 app31).

Definition v031 {Γ A} : Tm31 (snoc31 Γ A) A
 := var31 vz31.

Definition v131 {Γ A B} : Tm31 (snoc31 (snoc31 Γ A) B) A
 := var31 (vs31 vz31).

Definition v231 {Γ A B C} : Tm31 (snoc31 (snoc31 (snoc31 Γ A) B) C) A
 := var31 (vs31 (vs31 vz31)).

Definition v331 {Γ A B C D} : Tm31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) A
 := var31 (vs31 (vs31 (vs31 vz31))).

Definition v431 {Γ A B C D E} : Tm31 (snoc31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) E) A
 := var31 (vs31 (vs31 (vs31 (vs31 vz31)))).

Definition test31 {Γ A} : Tm31 Γ (arr31 (arr31 A A) (arr31 A A))
 := lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty32 : Set
 := ∀ (Ty32 : Set)
      (ι   : Ty32)
      (arr : Ty32 → Ty32 → Ty32)
    , Ty32.

Definition ι32 : Ty32 := λ _ ι32 _, ι32.

Definition arr32 : Ty32 → Ty32 → Ty32
 := λ A B Ty32 ι32 arr32,
     arr32 (A Ty32 ι32 arr32) (B Ty32 ι32 arr32).

Definition Con32 : Set
 := ∀ (Con32  : Set)
      (nil  : Con32)
      (snoc : Con32 → Ty32 → Con32)
    , Con32.

Definition nil32 : Con32
 := λ Con32 nil32 snoc , nil32.

Definition snoc32 : Con32 → Ty32 → Con32
 := λ Γ A Con32 nil32 snoc32 , snoc32 (Γ Con32 nil32 snoc32) A.

Definition Var32 : Con32 → Ty32 → Set
 := λ Γ A ,
   ∀ (Var32 : Con32 → Ty32 → Set)
     (vz  : ∀ Γ A, Var32 (snoc32 Γ A) A)
     (vs  : ∀ Γ B A, Var32 Γ A → Var32 (snoc32 Γ B) A)
   , Var32 Γ A.

Definition vz32 {Γ A} : Var32 (snoc32 Γ A) A
 := λ Var32 vz32 vs , vz32 _ _.

Definition vs32 {Γ B A} : Var32 Γ A → Var32 (snoc32 Γ B) A
 := λ x Var32 vz32 vs32 , vs32 _ _ _ (x Var32 vz32 vs32).

Definition Tm32 : Con32 → Ty32 → Set
 := λ Γ A ,
   ∀ (Tm32  : Con32 → Ty32 → Set)
     (var   : ∀ Γ A     , Var32 Γ A → Tm32 Γ A)
     (lam   : ∀ Γ A B   , Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B))
     (app   : ∀ Γ A B   , Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B)
   , Tm32 Γ A.

Definition var32 {Γ A} : Var32 Γ A → Tm32 Γ A
 := λ x Tm32 var32 lam app,
     var32 _ _ x.

Definition lam32 {Γ A B} : Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B)
 := λ t Tm32 var32 lam32 app,
     lam32 _ _ _ (t Tm32 var32 lam32 app).

Definition app32 {Γ A B} : Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B
 := λ t u Tm32 var32 lam32 app32,
     app32 _ _ _
         (t Tm32 var32 lam32 app32)
         (u Tm32 var32 lam32 app32).

Definition v032 {Γ A} : Tm32 (snoc32 Γ A) A
 := var32 vz32.

Definition v132 {Γ A B} : Tm32 (snoc32 (snoc32 Γ A) B) A
 := var32 (vs32 vz32).

Definition v232 {Γ A B C} : Tm32 (snoc32 (snoc32 (snoc32 Γ A) B) C) A
 := var32 (vs32 (vs32 vz32)).

Definition v332 {Γ A B C D} : Tm32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) A
 := var32 (vs32 (vs32 (vs32 vz32))).

Definition v432 {Γ A B C D E} : Tm32 (snoc32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) E) A
 := var32 (vs32 (vs32 (vs32 (vs32 vz32)))).

Definition test32 {Γ A} : Tm32 Γ (arr32 (arr32 A A) (arr32 A A))
 := lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty33 : Set
 := ∀ (Ty33 : Set)
      (ι   : Ty33)
      (arr : Ty33 → Ty33 → Ty33)
    , Ty33.

Definition ι33 : Ty33 := λ _ ι33 _, ι33.

Definition arr33 : Ty33 → Ty33 → Ty33
 := λ A B Ty33 ι33 arr33,
     arr33 (A Ty33 ι33 arr33) (B Ty33 ι33 arr33).

Definition Con33 : Set
 := ∀ (Con33  : Set)
      (nil  : Con33)
      (snoc : Con33 → Ty33 → Con33)
    , Con33.

Definition nil33 : Con33
 := λ Con33 nil33 snoc , nil33.

Definition snoc33 : Con33 → Ty33 → Con33
 := λ Γ A Con33 nil33 snoc33 , snoc33 (Γ Con33 nil33 snoc33) A.

Definition Var33 : Con33 → Ty33 → Set
 := λ Γ A ,
   ∀ (Var33 : Con33 → Ty33 → Set)
     (vz  : ∀ Γ A, Var33 (snoc33 Γ A) A)
     (vs  : ∀ Γ B A, Var33 Γ A → Var33 (snoc33 Γ B) A)
   , Var33 Γ A.

Definition vz33 {Γ A} : Var33 (snoc33 Γ A) A
 := λ Var33 vz33 vs , vz33 _ _.

Definition vs33 {Γ B A} : Var33 Γ A → Var33 (snoc33 Γ B) A
 := λ x Var33 vz33 vs33 , vs33 _ _ _ (x Var33 vz33 vs33).

Definition Tm33 : Con33 → Ty33 → Set
 := λ Γ A ,
   ∀ (Tm33  : Con33 → Ty33 → Set)
     (var   : ∀ Γ A     , Var33 Γ A → Tm33 Γ A)
     (lam   : ∀ Γ A B   , Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B))
     (app   : ∀ Γ A B   , Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B)
   , Tm33 Γ A.

Definition var33 {Γ A} : Var33 Γ A → Tm33 Γ A
 := λ x Tm33 var33 lam app,
     var33 _ _ x.

Definition lam33 {Γ A B} : Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B)
 := λ t Tm33 var33 lam33 app,
     lam33 _ _ _ (t Tm33 var33 lam33 app).

Definition app33 {Γ A B} : Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B
 := λ t u Tm33 var33 lam33 app33,
     app33 _ _ _
         (t Tm33 var33 lam33 app33)
         (u Tm33 var33 lam33 app33).

Definition v033 {Γ A} : Tm33 (snoc33 Γ A) A
 := var33 vz33.

Definition v133 {Γ A B} : Tm33 (snoc33 (snoc33 Γ A) B) A
 := var33 (vs33 vz33).

Definition v233 {Γ A B C} : Tm33 (snoc33 (snoc33 (snoc33 Γ A) B) C) A
 := var33 (vs33 (vs33 vz33)).

Definition v333 {Γ A B C D} : Tm33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) A
 := var33 (vs33 (vs33 (vs33 vz33))).

Definition v433 {Γ A B C D E} : Tm33 (snoc33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) E) A
 := var33 (vs33 (vs33 (vs33 (vs33 vz33)))).

Definition test33 {Γ A} : Tm33 Γ (arr33 (arr33 A A) (arr33 A A))
 := lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty34 : Set
 := ∀ (Ty34 : Set)
      (ι   : Ty34)
      (arr : Ty34 → Ty34 → Ty34)
    , Ty34.

Definition ι34 : Ty34 := λ _ ι34 _, ι34.

Definition arr34 : Ty34 → Ty34 → Ty34
 := λ A B Ty34 ι34 arr34,
     arr34 (A Ty34 ι34 arr34) (B Ty34 ι34 arr34).

Definition Con34 : Set
 := ∀ (Con34  : Set)
      (nil  : Con34)
      (snoc : Con34 → Ty34 → Con34)
    , Con34.

Definition nil34 : Con34
 := λ Con34 nil34 snoc , nil34.

Definition snoc34 : Con34 → Ty34 → Con34
 := λ Γ A Con34 nil34 snoc34 , snoc34 (Γ Con34 nil34 snoc34) A.

Definition Var34 : Con34 → Ty34 → Set
 := λ Γ A ,
   ∀ (Var34 : Con34 → Ty34 → Set)
     (vz  : ∀ Γ A, Var34 (snoc34 Γ A) A)
     (vs  : ∀ Γ B A, Var34 Γ A → Var34 (snoc34 Γ B) A)
   , Var34 Γ A.

Definition vz34 {Γ A} : Var34 (snoc34 Γ A) A
 := λ Var34 vz34 vs , vz34 _ _.

Definition vs34 {Γ B A} : Var34 Γ A → Var34 (snoc34 Γ B) A
 := λ x Var34 vz34 vs34 , vs34 _ _ _ (x Var34 vz34 vs34).

Definition Tm34 : Con34 → Ty34 → Set
 := λ Γ A ,
   ∀ (Tm34  : Con34 → Ty34 → Set)
     (var   : ∀ Γ A     , Var34 Γ A → Tm34 Γ A)
     (lam   : ∀ Γ A B   , Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B))
     (app   : ∀ Γ A B   , Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B)
   , Tm34 Γ A.

Definition var34 {Γ A} : Var34 Γ A → Tm34 Γ A
 := λ x Tm34 var34 lam app,
     var34 _ _ x.

Definition lam34 {Γ A B} : Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B)
 := λ t Tm34 var34 lam34 app,
     lam34 _ _ _ (t Tm34 var34 lam34 app).

Definition app34 {Γ A B} : Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B
 := λ t u Tm34 var34 lam34 app34,
     app34 _ _ _
         (t Tm34 var34 lam34 app34)
         (u Tm34 var34 lam34 app34).

Definition v034 {Γ A} : Tm34 (snoc34 Γ A) A
 := var34 vz34.

Definition v134 {Γ A B} : Tm34 (snoc34 (snoc34 Γ A) B) A
 := var34 (vs34 vz34).

Definition v234 {Γ A B C} : Tm34 (snoc34 (snoc34 (snoc34 Γ A) B) C) A
 := var34 (vs34 (vs34 vz34)).

Definition v334 {Γ A B C D} : Tm34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) A
 := var34 (vs34 (vs34 (vs34 vz34))).

Definition v434 {Γ A B C D E} : Tm34 (snoc34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) E) A
 := var34 (vs34 (vs34 (vs34 (vs34 vz34)))).

Definition test34 {Γ A} : Tm34 Γ (arr34 (arr34 A A) (arr34 A A))
 := lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty35 : Set
 := ∀ (Ty35 : Set)
      (ι   : Ty35)
      (arr : Ty35 → Ty35 → Ty35)
    , Ty35.

Definition ι35 : Ty35 := λ _ ι35 _, ι35.

Definition arr35 : Ty35 → Ty35 → Ty35
 := λ A B Ty35 ι35 arr35,
     arr35 (A Ty35 ι35 arr35) (B Ty35 ι35 arr35).

Definition Con35 : Set
 := ∀ (Con35  : Set)
      (nil  : Con35)
      (snoc : Con35 → Ty35 → Con35)
    , Con35.

Definition nil35 : Con35
 := λ Con35 nil35 snoc , nil35.

Definition snoc35 : Con35 → Ty35 → Con35
 := λ Γ A Con35 nil35 snoc35 , snoc35 (Γ Con35 nil35 snoc35) A.

Definition Var35 : Con35 → Ty35 → Set
 := λ Γ A ,
   ∀ (Var35 : Con35 → Ty35 → Set)
     (vz  : ∀ Γ A, Var35 (snoc35 Γ A) A)
     (vs  : ∀ Γ B A, Var35 Γ A → Var35 (snoc35 Γ B) A)
   , Var35 Γ A.

Definition vz35 {Γ A} : Var35 (snoc35 Γ A) A
 := λ Var35 vz35 vs , vz35 _ _.

Definition vs35 {Γ B A} : Var35 Γ A → Var35 (snoc35 Γ B) A
 := λ x Var35 vz35 vs35 , vs35 _ _ _ (x Var35 vz35 vs35).

Definition Tm35 : Con35 → Ty35 → Set
 := λ Γ A ,
   ∀ (Tm35  : Con35 → Ty35 → Set)
     (var   : ∀ Γ A     , Var35 Γ A → Tm35 Γ A)
     (lam   : ∀ Γ A B   , Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B))
     (app   : ∀ Γ A B   , Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B)
   , Tm35 Γ A.

Definition var35 {Γ A} : Var35 Γ A → Tm35 Γ A
 := λ x Tm35 var35 lam app,
     var35 _ _ x.

Definition lam35 {Γ A B} : Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B)
 := λ t Tm35 var35 lam35 app,
     lam35 _ _ _ (t Tm35 var35 lam35 app).

Definition app35 {Γ A B} : Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B
 := λ t u Tm35 var35 lam35 app35,
     app35 _ _ _
         (t Tm35 var35 lam35 app35)
         (u Tm35 var35 lam35 app35).

Definition v035 {Γ A} : Tm35 (snoc35 Γ A) A
 := var35 vz35.

Definition v135 {Γ A B} : Tm35 (snoc35 (snoc35 Γ A) B) A
 := var35 (vs35 vz35).

Definition v235 {Γ A B C} : Tm35 (snoc35 (snoc35 (snoc35 Γ A) B) C) A
 := var35 (vs35 (vs35 vz35)).

Definition v335 {Γ A B C D} : Tm35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) A
 := var35 (vs35 (vs35 (vs35 vz35))).

Definition v435 {Γ A B C D E} : Tm35 (snoc35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) E) A
 := var35 (vs35 (vs35 (vs35 (vs35 vz35)))).

Definition test35 {Γ A} : Tm35 Γ (arr35 (arr35 A A) (arr35 A A))
 := lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty36 : Set
 := ∀ (Ty36 : Set)
      (ι   : Ty36)
      (arr : Ty36 → Ty36 → Ty36)
    , Ty36.

Definition ι36 : Ty36 := λ _ ι36 _, ι36.

Definition arr36 : Ty36 → Ty36 → Ty36
 := λ A B Ty36 ι36 arr36,
     arr36 (A Ty36 ι36 arr36) (B Ty36 ι36 arr36).

Definition Con36 : Set
 := ∀ (Con36  : Set)
      (nil  : Con36)
      (snoc : Con36 → Ty36 → Con36)
    , Con36.

Definition nil36 : Con36
 := λ Con36 nil36 snoc , nil36.

Definition snoc36 : Con36 → Ty36 → Con36
 := λ Γ A Con36 nil36 snoc36 , snoc36 (Γ Con36 nil36 snoc36) A.

Definition Var36 : Con36 → Ty36 → Set
 := λ Γ A ,
   ∀ (Var36 : Con36 → Ty36 → Set)
     (vz  : ∀ Γ A, Var36 (snoc36 Γ A) A)
     (vs  : ∀ Γ B A, Var36 Γ A → Var36 (snoc36 Γ B) A)
   , Var36 Γ A.

Definition vz36 {Γ A} : Var36 (snoc36 Γ A) A
 := λ Var36 vz36 vs , vz36 _ _.

Definition vs36 {Γ B A} : Var36 Γ A → Var36 (snoc36 Γ B) A
 := λ x Var36 vz36 vs36 , vs36 _ _ _ (x Var36 vz36 vs36).

Definition Tm36 : Con36 → Ty36 → Set
 := λ Γ A ,
   ∀ (Tm36  : Con36 → Ty36 → Set)
     (var   : ∀ Γ A     , Var36 Γ A → Tm36 Γ A)
     (lam   : ∀ Γ A B   , Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B))
     (app   : ∀ Γ A B   , Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B)
   , Tm36 Γ A.

Definition var36 {Γ A} : Var36 Γ A → Tm36 Γ A
 := λ x Tm36 var36 lam app,
     var36 _ _ x.

Definition lam36 {Γ A B} : Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B)
 := λ t Tm36 var36 lam36 app,
     lam36 _ _ _ (t Tm36 var36 lam36 app).

Definition app36 {Γ A B} : Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B
 := λ t u Tm36 var36 lam36 app36,
     app36 _ _ _
         (t Tm36 var36 lam36 app36)
         (u Tm36 var36 lam36 app36).

Definition v036 {Γ A} : Tm36 (snoc36 Γ A) A
 := var36 vz36.

Definition v136 {Γ A B} : Tm36 (snoc36 (snoc36 Γ A) B) A
 := var36 (vs36 vz36).

Definition v236 {Γ A B C} : Tm36 (snoc36 (snoc36 (snoc36 Γ A) B) C) A
 := var36 (vs36 (vs36 vz36)).

Definition v336 {Γ A B C D} : Tm36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) A
 := var36 (vs36 (vs36 (vs36 vz36))).

Definition v436 {Γ A B C D E} : Tm36 (snoc36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) E) A
 := var36 (vs36 (vs36 (vs36 (vs36 vz36)))).

Definition test36 {Γ A} : Tm36 Γ (arr36 (arr36 A A) (arr36 A A))
 := lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty37 : Set
 := ∀ (Ty37 : Set)
      (ι   : Ty37)
      (arr : Ty37 → Ty37 → Ty37)
    , Ty37.

Definition ι37 : Ty37 := λ _ ι37 _, ι37.

Definition arr37 : Ty37 → Ty37 → Ty37
 := λ A B Ty37 ι37 arr37,
     arr37 (A Ty37 ι37 arr37) (B Ty37 ι37 arr37).

Definition Con37 : Set
 := ∀ (Con37  : Set)
      (nil  : Con37)
      (snoc : Con37 → Ty37 → Con37)
    , Con37.

Definition nil37 : Con37
 := λ Con37 nil37 snoc , nil37.

Definition snoc37 : Con37 → Ty37 → Con37
 := λ Γ A Con37 nil37 snoc37 , snoc37 (Γ Con37 nil37 snoc37) A.

Definition Var37 : Con37 → Ty37 → Set
 := λ Γ A ,
   ∀ (Var37 : Con37 → Ty37 → Set)
     (vz  : ∀ Γ A, Var37 (snoc37 Γ A) A)
     (vs  : ∀ Γ B A, Var37 Γ A → Var37 (snoc37 Γ B) A)
   , Var37 Γ A.

Definition vz37 {Γ A} : Var37 (snoc37 Γ A) A
 := λ Var37 vz37 vs , vz37 _ _.

Definition vs37 {Γ B A} : Var37 Γ A → Var37 (snoc37 Γ B) A
 := λ x Var37 vz37 vs37 , vs37 _ _ _ (x Var37 vz37 vs37).

Definition Tm37 : Con37 → Ty37 → Set
 := λ Γ A ,
   ∀ (Tm37  : Con37 → Ty37 → Set)
     (var   : ∀ Γ A     , Var37 Γ A → Tm37 Γ A)
     (lam   : ∀ Γ A B   , Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B))
     (app   : ∀ Γ A B   , Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B)
   , Tm37 Γ A.

Definition var37 {Γ A} : Var37 Γ A → Tm37 Γ A
 := λ x Tm37 var37 lam app,
     var37 _ _ x.

Definition lam37 {Γ A B} : Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B)
 := λ t Tm37 var37 lam37 app,
     lam37 _ _ _ (t Tm37 var37 lam37 app).

Definition app37 {Γ A B} : Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B
 := λ t u Tm37 var37 lam37 app37,
     app37 _ _ _
         (t Tm37 var37 lam37 app37)
         (u Tm37 var37 lam37 app37).

Definition v037 {Γ A} : Tm37 (snoc37 Γ A) A
 := var37 vz37.

Definition v137 {Γ A B} : Tm37 (snoc37 (snoc37 Γ A) B) A
 := var37 (vs37 vz37).

Definition v237 {Γ A B C} : Tm37 (snoc37 (snoc37 (snoc37 Γ A) B) C) A
 := var37 (vs37 (vs37 vz37)).

Definition v337 {Γ A B C D} : Tm37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) A
 := var37 (vs37 (vs37 (vs37 vz37))).

Definition v437 {Γ A B C D E} : Tm37 (snoc37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) E) A
 := var37 (vs37 (vs37 (vs37 (vs37 vz37)))).

Definition test37 {Γ A} : Tm37 Γ (arr37 (arr37 A A) (arr37 A A))
 := lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty38 : Set
 := ∀ (Ty38 : Set)
      (ι   : Ty38)
      (arr : Ty38 → Ty38 → Ty38)
    , Ty38.

Definition ι38 : Ty38 := λ _ ι38 _, ι38.

Definition arr38 : Ty38 → Ty38 → Ty38
 := λ A B Ty38 ι38 arr38,
     arr38 (A Ty38 ι38 arr38) (B Ty38 ι38 arr38).

Definition Con38 : Set
 := ∀ (Con38  : Set)
      (nil  : Con38)
      (snoc : Con38 → Ty38 → Con38)
    , Con38.

Definition nil38 : Con38
 := λ Con38 nil38 snoc , nil38.

Definition snoc38 : Con38 → Ty38 → Con38
 := λ Γ A Con38 nil38 snoc38 , snoc38 (Γ Con38 nil38 snoc38) A.

Definition Var38 : Con38 → Ty38 → Set
 := λ Γ A ,
   ∀ (Var38 : Con38 → Ty38 → Set)
     (vz  : ∀ Γ A, Var38 (snoc38 Γ A) A)
     (vs  : ∀ Γ B A, Var38 Γ A → Var38 (snoc38 Γ B) A)
   , Var38 Γ A.

Definition vz38 {Γ A} : Var38 (snoc38 Γ A) A
 := λ Var38 vz38 vs , vz38 _ _.

Definition vs38 {Γ B A} : Var38 Γ A → Var38 (snoc38 Γ B) A
 := λ x Var38 vz38 vs38 , vs38 _ _ _ (x Var38 vz38 vs38).

Definition Tm38 : Con38 → Ty38 → Set
 := λ Γ A ,
   ∀ (Tm38  : Con38 → Ty38 → Set)
     (var   : ∀ Γ A     , Var38 Γ A → Tm38 Γ A)
     (lam   : ∀ Γ A B   , Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B))
     (app   : ∀ Γ A B   , Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B)
   , Tm38 Γ A.

Definition var38 {Γ A} : Var38 Γ A → Tm38 Γ A
 := λ x Tm38 var38 lam app,
     var38 _ _ x.

Definition lam38 {Γ A B} : Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B)
 := λ t Tm38 var38 lam38 app,
     lam38 _ _ _ (t Tm38 var38 lam38 app).

Definition app38 {Γ A B} : Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B
 := λ t u Tm38 var38 lam38 app38,
     app38 _ _ _
         (t Tm38 var38 lam38 app38)
         (u Tm38 var38 lam38 app38).

Definition v038 {Γ A} : Tm38 (snoc38 Γ A) A
 := var38 vz38.

Definition v138 {Γ A B} : Tm38 (snoc38 (snoc38 Γ A) B) A
 := var38 (vs38 vz38).

Definition v238 {Γ A B C} : Tm38 (snoc38 (snoc38 (snoc38 Γ A) B) C) A
 := var38 (vs38 (vs38 vz38)).

Definition v338 {Γ A B C D} : Tm38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) A
 := var38 (vs38 (vs38 (vs38 vz38))).

Definition v438 {Γ A B C D E} : Tm38 (snoc38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) E) A
 := var38 (vs38 (vs38 (vs38 (vs38 vz38)))).

Definition test38 {Γ A} : Tm38 Γ (arr38 (arr38 A A) (arr38 A A))
 := lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty39 : Set
 := ∀ (Ty39 : Set)
      (ι   : Ty39)
      (arr : Ty39 → Ty39 → Ty39)
    , Ty39.

Definition ι39 : Ty39 := λ _ ι39 _, ι39.

Definition arr39 : Ty39 → Ty39 → Ty39
 := λ A B Ty39 ι39 arr39,
     arr39 (A Ty39 ι39 arr39) (B Ty39 ι39 arr39).

Definition Con39 : Set
 := ∀ (Con39  : Set)
      (nil  : Con39)
      (snoc : Con39 → Ty39 → Con39)
    , Con39.

Definition nil39 : Con39
 := λ Con39 nil39 snoc , nil39.

Definition snoc39 : Con39 → Ty39 → Con39
 := λ Γ A Con39 nil39 snoc39 , snoc39 (Γ Con39 nil39 snoc39) A.

Definition Var39 : Con39 → Ty39 → Set
 := λ Γ A ,
   ∀ (Var39 : Con39 → Ty39 → Set)
     (vz  : ∀ Γ A, Var39 (snoc39 Γ A) A)
     (vs  : ∀ Γ B A, Var39 Γ A → Var39 (snoc39 Γ B) A)
   , Var39 Γ A.

Definition vz39 {Γ A} : Var39 (snoc39 Γ A) A
 := λ Var39 vz39 vs , vz39 _ _.

Definition vs39 {Γ B A} : Var39 Γ A → Var39 (snoc39 Γ B) A
 := λ x Var39 vz39 vs39 , vs39 _ _ _ (x Var39 vz39 vs39).

Definition Tm39 : Con39 → Ty39 → Set
 := λ Γ A ,
   ∀ (Tm39  : Con39 → Ty39 → Set)
     (var   : ∀ Γ A     , Var39 Γ A → Tm39 Γ A)
     (lam   : ∀ Γ A B   , Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B))
     (app   : ∀ Γ A B   , Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B)
   , Tm39 Γ A.

Definition var39 {Γ A} : Var39 Γ A → Tm39 Γ A
 := λ x Tm39 var39 lam app,
     var39 _ _ x.

Definition lam39 {Γ A B} : Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B)
 := λ t Tm39 var39 lam39 app,
     lam39 _ _ _ (t Tm39 var39 lam39 app).

Definition app39 {Γ A B} : Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B
 := λ t u Tm39 var39 lam39 app39,
     app39 _ _ _
         (t Tm39 var39 lam39 app39)
         (u Tm39 var39 lam39 app39).

Definition v039 {Γ A} : Tm39 (snoc39 Γ A) A
 := var39 vz39.

Definition v139 {Γ A B} : Tm39 (snoc39 (snoc39 Γ A) B) A
 := var39 (vs39 vz39).

Definition v239 {Γ A B C} : Tm39 (snoc39 (snoc39 (snoc39 Γ A) B) C) A
 := var39 (vs39 (vs39 vz39)).

Definition v339 {Γ A B C D} : Tm39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) A
 := var39 (vs39 (vs39 (vs39 vz39))).

Definition v439 {Γ A B C D E} : Tm39 (snoc39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) E) A
 := var39 (vs39 (vs39 (vs39 (vs39 vz39)))).

Definition test39 {Γ A} : Tm39 Γ (arr39 (arr39 A A) (arr39 A A))
 := lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty40 : Set
 := ∀ (Ty40 : Set)
      (ι   : Ty40)
      (arr : Ty40 → Ty40 → Ty40)
    , Ty40.

Definition ι40 : Ty40 := λ _ ι40 _, ι40.

Definition arr40 : Ty40 → Ty40 → Ty40
 := λ A B Ty40 ι40 arr40,
     arr40 (A Ty40 ι40 arr40) (B Ty40 ι40 arr40).

Definition Con40 : Set
 := ∀ (Con40  : Set)
      (nil  : Con40)
      (snoc : Con40 → Ty40 → Con40)
    , Con40.

Definition nil40 : Con40
 := λ Con40 nil40 snoc , nil40.

Definition snoc40 : Con40 → Ty40 → Con40
 := λ Γ A Con40 nil40 snoc40 , snoc40 (Γ Con40 nil40 snoc40) A.

Definition Var40 : Con40 → Ty40 → Set
 := λ Γ A ,
   ∀ (Var40 : Con40 → Ty40 → Set)
     (vz  : ∀ Γ A, Var40 (snoc40 Γ A) A)
     (vs  : ∀ Γ B A, Var40 Γ A → Var40 (snoc40 Γ B) A)
   , Var40 Γ A.

Definition vz40 {Γ A} : Var40 (snoc40 Γ A) A
 := λ Var40 vz40 vs , vz40 _ _.

Definition vs40 {Γ B A} : Var40 Γ A → Var40 (snoc40 Γ B) A
 := λ x Var40 vz40 vs40 , vs40 _ _ _ (x Var40 vz40 vs40).

Definition Tm40 : Con40 → Ty40 → Set
 := λ Γ A ,
   ∀ (Tm40  : Con40 → Ty40 → Set)
     (var   : ∀ Γ A     , Var40 Γ A → Tm40 Γ A)
     (lam   : ∀ Γ A B   , Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B))
     (app   : ∀ Γ A B   , Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B)
   , Tm40 Γ A.

Definition var40 {Γ A} : Var40 Γ A → Tm40 Γ A
 := λ x Tm40 var40 lam app,
     var40 _ _ x.

Definition lam40 {Γ A B} : Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B)
 := λ t Tm40 var40 lam40 app,
     lam40 _ _ _ (t Tm40 var40 lam40 app).

Definition app40 {Γ A B} : Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B
 := λ t u Tm40 var40 lam40 app40,
     app40 _ _ _
         (t Tm40 var40 lam40 app40)
         (u Tm40 var40 lam40 app40).

Definition v040 {Γ A} : Tm40 (snoc40 Γ A) A
 := var40 vz40.

Definition v140 {Γ A B} : Tm40 (snoc40 (snoc40 Γ A) B) A
 := var40 (vs40 vz40).

Definition v240 {Γ A B C} : Tm40 (snoc40 (snoc40 (snoc40 Γ A) B) C) A
 := var40 (vs40 (vs40 vz40)).

Definition v340 {Γ A B C D} : Tm40 (snoc40 (snoc40 (snoc40 (snoc40 Γ A) B) C) D) A
 := var40 (vs40 (vs40 (vs40 vz40))).

Definition v440 {Γ A B C D E} : Tm40 (snoc40 (snoc40 (snoc40 (snoc40 (snoc40 Γ A) B) C) D) E) A
 := var40 (vs40 (vs40 (vs40 (vs40 vz40)))).

Definition test40 {Γ A} : Tm40 Γ (arr40 (arr40 A A) (arr40 A A))
 := lam40 (lam40 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 v040))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty41 : Set
 := ∀ (Ty41 : Set)
      (ι   : Ty41)
      (arr : Ty41 → Ty41 → Ty41)
    , Ty41.

Definition ι41 : Ty41 := λ _ ι41 _, ι41.

Definition arr41 : Ty41 → Ty41 → Ty41
 := λ A B Ty41 ι41 arr41,
     arr41 (A Ty41 ι41 arr41) (B Ty41 ι41 arr41).

Definition Con41 : Set
 := ∀ (Con41  : Set)
      (nil  : Con41)
      (snoc : Con41 → Ty41 → Con41)
    , Con41.

Definition nil41 : Con41
 := λ Con41 nil41 snoc , nil41.

Definition snoc41 : Con41 → Ty41 → Con41
 := λ Γ A Con41 nil41 snoc41 , snoc41 (Γ Con41 nil41 snoc41) A.

Definition Var41 : Con41 → Ty41 → Set
 := λ Γ A ,
   ∀ (Var41 : Con41 → Ty41 → Set)
     (vz  : ∀ Γ A, Var41 (snoc41 Γ A) A)
     (vs  : ∀ Γ B A, Var41 Γ A → Var41 (snoc41 Γ B) A)
   , Var41 Γ A.

Definition vz41 {Γ A} : Var41 (snoc41 Γ A) A
 := λ Var41 vz41 vs , vz41 _ _.

Definition vs41 {Γ B A} : Var41 Γ A → Var41 (snoc41 Γ B) A
 := λ x Var41 vz41 vs41 , vs41 _ _ _ (x Var41 vz41 vs41).

Definition Tm41 : Con41 → Ty41 → Set
 := λ Γ A ,
   ∀ (Tm41  : Con41 → Ty41 → Set)
     (var   : ∀ Γ A     , Var41 Γ A → Tm41 Γ A)
     (lam   : ∀ Γ A B   , Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B))
     (app   : ∀ Γ A B   , Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B)
   , Tm41 Γ A.

Definition var41 {Γ A} : Var41 Γ A → Tm41 Γ A
 := λ x Tm41 var41 lam app,
     var41 _ _ x.

Definition lam41 {Γ A B} : Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B)
 := λ t Tm41 var41 lam41 app,
     lam41 _ _ _ (t Tm41 var41 lam41 app).

Definition app41 {Γ A B} : Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B
 := λ t u Tm41 var41 lam41 app41,
     app41 _ _ _
         (t Tm41 var41 lam41 app41)
         (u Tm41 var41 lam41 app41).

Definition v041 {Γ A} : Tm41 (snoc41 Γ A) A
 := var41 vz41.

Definition v141 {Γ A B} : Tm41 (snoc41 (snoc41 Γ A) B) A
 := var41 (vs41 vz41).

Definition v241 {Γ A B C} : Tm41 (snoc41 (snoc41 (snoc41 Γ A) B) C) A
 := var41 (vs41 (vs41 vz41)).

Definition v341 {Γ A B C D} : Tm41 (snoc41 (snoc41 (snoc41 (snoc41 Γ A) B) C) D) A
 := var41 (vs41 (vs41 (vs41 vz41))).

Definition v441 {Γ A B C D E} : Tm41 (snoc41 (snoc41 (snoc41 (snoc41 (snoc41 Γ A) B) C) D) E) A
 := var41 (vs41 (vs41 (vs41 (vs41 vz41)))).

Definition test41 {Γ A} : Tm41 Γ (arr41 (arr41 A A) (arr41 A A))
 := lam41 (lam41 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 v041))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty42 : Set
 := ∀ (Ty42 : Set)
      (ι   : Ty42)
      (arr : Ty42 → Ty42 → Ty42)
    , Ty42.

Definition ι42 : Ty42 := λ _ ι42 _, ι42.

Definition arr42 : Ty42 → Ty42 → Ty42
 := λ A B Ty42 ι42 arr42,
     arr42 (A Ty42 ι42 arr42) (B Ty42 ι42 arr42).

Definition Con42 : Set
 := ∀ (Con42  : Set)
      (nil  : Con42)
      (snoc : Con42 → Ty42 → Con42)
    , Con42.

Definition nil42 : Con42
 := λ Con42 nil42 snoc , nil42.

Definition snoc42 : Con42 → Ty42 → Con42
 := λ Γ A Con42 nil42 snoc42 , snoc42 (Γ Con42 nil42 snoc42) A.

Definition Var42 : Con42 → Ty42 → Set
 := λ Γ A ,
   ∀ (Var42 : Con42 → Ty42 → Set)
     (vz  : ∀ Γ A, Var42 (snoc42 Γ A) A)
     (vs  : ∀ Γ B A, Var42 Γ A → Var42 (snoc42 Γ B) A)
   , Var42 Γ A.

Definition vz42 {Γ A} : Var42 (snoc42 Γ A) A
 := λ Var42 vz42 vs , vz42 _ _.

Definition vs42 {Γ B A} : Var42 Γ A → Var42 (snoc42 Γ B) A
 := λ x Var42 vz42 vs42 , vs42 _ _ _ (x Var42 vz42 vs42).

Definition Tm42 : Con42 → Ty42 → Set
 := λ Γ A ,
   ∀ (Tm42  : Con42 → Ty42 → Set)
     (var   : ∀ Γ A     , Var42 Γ A → Tm42 Γ A)
     (lam   : ∀ Γ A B   , Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B))
     (app   : ∀ Γ A B   , Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B)
   , Tm42 Γ A.

Definition var42 {Γ A} : Var42 Γ A → Tm42 Γ A
 := λ x Tm42 var42 lam app,
     var42 _ _ x.

Definition lam42 {Γ A B} : Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B)
 := λ t Tm42 var42 lam42 app,
     lam42 _ _ _ (t Tm42 var42 lam42 app).

Definition app42 {Γ A B} : Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B
 := λ t u Tm42 var42 lam42 app42,
     app42 _ _ _
         (t Tm42 var42 lam42 app42)
         (u Tm42 var42 lam42 app42).

Definition v042 {Γ A} : Tm42 (snoc42 Γ A) A
 := var42 vz42.

Definition v142 {Γ A B} : Tm42 (snoc42 (snoc42 Γ A) B) A
 := var42 (vs42 vz42).

Definition v242 {Γ A B C} : Tm42 (snoc42 (snoc42 (snoc42 Γ A) B) C) A
 := var42 (vs42 (vs42 vz42)).

Definition v342 {Γ A B C D} : Tm42 (snoc42 (snoc42 (snoc42 (snoc42 Γ A) B) C) D) A
 := var42 (vs42 (vs42 (vs42 vz42))).

Definition v442 {Γ A B C D E} : Tm42 (snoc42 (snoc42 (snoc42 (snoc42 (snoc42 Γ A) B) C) D) E) A
 := var42 (vs42 (vs42 (vs42 (vs42 vz42)))).

Definition test42 {Γ A} : Tm42 Γ (arr42 (arr42 A A) (arr42 A A))
 := lam42 (lam42 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 v042))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty43 : Set
 := ∀ (Ty43 : Set)
      (ι   : Ty43)
      (arr : Ty43 → Ty43 → Ty43)
    , Ty43.

Definition ι43 : Ty43 := λ _ ι43 _, ι43.

Definition arr43 : Ty43 → Ty43 → Ty43
 := λ A B Ty43 ι43 arr43,
     arr43 (A Ty43 ι43 arr43) (B Ty43 ι43 arr43).

Definition Con43 : Set
 := ∀ (Con43  : Set)
      (nil  : Con43)
      (snoc : Con43 → Ty43 → Con43)
    , Con43.

Definition nil43 : Con43
 := λ Con43 nil43 snoc , nil43.

Definition snoc43 : Con43 → Ty43 → Con43
 := λ Γ A Con43 nil43 snoc43 , snoc43 (Γ Con43 nil43 snoc43) A.

Definition Var43 : Con43 → Ty43 → Set
 := λ Γ A ,
   ∀ (Var43 : Con43 → Ty43 → Set)
     (vz  : ∀ Γ A, Var43 (snoc43 Γ A) A)
     (vs  : ∀ Γ B A, Var43 Γ A → Var43 (snoc43 Γ B) A)
   , Var43 Γ A.

Definition vz43 {Γ A} : Var43 (snoc43 Γ A) A
 := λ Var43 vz43 vs , vz43 _ _.

Definition vs43 {Γ B A} : Var43 Γ A → Var43 (snoc43 Γ B) A
 := λ x Var43 vz43 vs43 , vs43 _ _ _ (x Var43 vz43 vs43).

Definition Tm43 : Con43 → Ty43 → Set
 := λ Γ A ,
   ∀ (Tm43  : Con43 → Ty43 → Set)
     (var   : ∀ Γ A     , Var43 Γ A → Tm43 Γ A)
     (lam   : ∀ Γ A B   , Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B))
     (app   : ∀ Γ A B   , Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B)
   , Tm43 Γ A.

Definition var43 {Γ A} : Var43 Γ A → Tm43 Γ A
 := λ x Tm43 var43 lam app,
     var43 _ _ x.

Definition lam43 {Γ A B} : Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B)
 := λ t Tm43 var43 lam43 app,
     lam43 _ _ _ (t Tm43 var43 lam43 app).

Definition app43 {Γ A B} : Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B
 := λ t u Tm43 var43 lam43 app43,
     app43 _ _ _
         (t Tm43 var43 lam43 app43)
         (u Tm43 var43 lam43 app43).

Definition v043 {Γ A} : Tm43 (snoc43 Γ A) A
 := var43 vz43.

Definition v143 {Γ A B} : Tm43 (snoc43 (snoc43 Γ A) B) A
 := var43 (vs43 vz43).

Definition v243 {Γ A B C} : Tm43 (snoc43 (snoc43 (snoc43 Γ A) B) C) A
 := var43 (vs43 (vs43 vz43)).

Definition v343 {Γ A B C D} : Tm43 (snoc43 (snoc43 (snoc43 (snoc43 Γ A) B) C) D) A
 := var43 (vs43 (vs43 (vs43 vz43))).

Definition v443 {Γ A B C D E} : Tm43 (snoc43 (snoc43 (snoc43 (snoc43 (snoc43 Γ A) B) C) D) E) A
 := var43 (vs43 (vs43 (vs43 (vs43 vz43)))).

Definition test43 {Γ A} : Tm43 Γ (arr43 (arr43 A A) (arr43 A A))
 := lam43 (lam43 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 v043))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty44 : Set
 := ∀ (Ty44 : Set)
      (ι   : Ty44)
      (arr : Ty44 → Ty44 → Ty44)
    , Ty44.

Definition ι44 : Ty44 := λ _ ι44 _, ι44.

Definition arr44 : Ty44 → Ty44 → Ty44
 := λ A B Ty44 ι44 arr44,
     arr44 (A Ty44 ι44 arr44) (B Ty44 ι44 arr44).

Definition Con44 : Set
 := ∀ (Con44  : Set)
      (nil  : Con44)
      (snoc : Con44 → Ty44 → Con44)
    , Con44.

Definition nil44 : Con44
 := λ Con44 nil44 snoc , nil44.

Definition snoc44 : Con44 → Ty44 → Con44
 := λ Γ A Con44 nil44 snoc44 , snoc44 (Γ Con44 nil44 snoc44) A.

Definition Var44 : Con44 → Ty44 → Set
 := λ Γ A ,
   ∀ (Var44 : Con44 → Ty44 → Set)
     (vz  : ∀ Γ A, Var44 (snoc44 Γ A) A)
     (vs  : ∀ Γ B A, Var44 Γ A → Var44 (snoc44 Γ B) A)
   , Var44 Γ A.

Definition vz44 {Γ A} : Var44 (snoc44 Γ A) A
 := λ Var44 vz44 vs , vz44 _ _.

Definition vs44 {Γ B A} : Var44 Γ A → Var44 (snoc44 Γ B) A
 := λ x Var44 vz44 vs44 , vs44 _ _ _ (x Var44 vz44 vs44).

Definition Tm44 : Con44 → Ty44 → Set
 := λ Γ A ,
   ∀ (Tm44  : Con44 → Ty44 → Set)
     (var   : ∀ Γ A     , Var44 Γ A → Tm44 Γ A)
     (lam   : ∀ Γ A B   , Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B))
     (app   : ∀ Γ A B   , Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B)
   , Tm44 Γ A.

Definition var44 {Γ A} : Var44 Γ A → Tm44 Γ A
 := λ x Tm44 var44 lam app,
     var44 _ _ x.

Definition lam44 {Γ A B} : Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B)
 := λ t Tm44 var44 lam44 app,
     lam44 _ _ _ (t Tm44 var44 lam44 app).

Definition app44 {Γ A B} : Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B
 := λ t u Tm44 var44 lam44 app44,
     app44 _ _ _
         (t Tm44 var44 lam44 app44)
         (u Tm44 var44 lam44 app44).

Definition v044 {Γ A} : Tm44 (snoc44 Γ A) A
 := var44 vz44.

Definition v144 {Γ A B} : Tm44 (snoc44 (snoc44 Γ A) B) A
 := var44 (vs44 vz44).

Definition v244 {Γ A B C} : Tm44 (snoc44 (snoc44 (snoc44 Γ A) B) C) A
 := var44 (vs44 (vs44 vz44)).

Definition v344 {Γ A B C D} : Tm44 (snoc44 (snoc44 (snoc44 (snoc44 Γ A) B) C) D) A
 := var44 (vs44 (vs44 (vs44 vz44))).

Definition v444 {Γ A B C D E} : Tm44 (snoc44 (snoc44 (snoc44 (snoc44 (snoc44 Γ A) B) C) D) E) A
 := var44 (vs44 (vs44 (vs44 (vs44 vz44)))).

Definition test44 {Γ A} : Tm44 Γ (arr44 (arr44 A A) (arr44 A A))
 := lam44 (lam44 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 v044))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty45 : Set
 := ∀ (Ty45 : Set)
      (ι   : Ty45)
      (arr : Ty45 → Ty45 → Ty45)
    , Ty45.

Definition ι45 : Ty45 := λ _ ι45 _, ι45.

Definition arr45 : Ty45 → Ty45 → Ty45
 := λ A B Ty45 ι45 arr45,
     arr45 (A Ty45 ι45 arr45) (B Ty45 ι45 arr45).

Definition Con45 : Set
 := ∀ (Con45  : Set)
      (nil  : Con45)
      (snoc : Con45 → Ty45 → Con45)
    , Con45.

Definition nil45 : Con45
 := λ Con45 nil45 snoc , nil45.

Definition snoc45 : Con45 → Ty45 → Con45
 := λ Γ A Con45 nil45 snoc45 , snoc45 (Γ Con45 nil45 snoc45) A.

Definition Var45 : Con45 → Ty45 → Set
 := λ Γ A ,
   ∀ (Var45 : Con45 → Ty45 → Set)
     (vz  : ∀ Γ A, Var45 (snoc45 Γ A) A)
     (vs  : ∀ Γ B A, Var45 Γ A → Var45 (snoc45 Γ B) A)
   , Var45 Γ A.

Definition vz45 {Γ A} : Var45 (snoc45 Γ A) A
 := λ Var45 vz45 vs , vz45 _ _.

Definition vs45 {Γ B A} : Var45 Γ A → Var45 (snoc45 Γ B) A
 := λ x Var45 vz45 vs45 , vs45 _ _ _ (x Var45 vz45 vs45).

Definition Tm45 : Con45 → Ty45 → Set
 := λ Γ A ,
   ∀ (Tm45  : Con45 → Ty45 → Set)
     (var   : ∀ Γ A     , Var45 Γ A → Tm45 Γ A)
     (lam   : ∀ Γ A B   , Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B))
     (app   : ∀ Γ A B   , Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B)
   , Tm45 Γ A.

Definition var45 {Γ A} : Var45 Γ A → Tm45 Γ A
 := λ x Tm45 var45 lam app,
     var45 _ _ x.

Definition lam45 {Γ A B} : Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B)
 := λ t Tm45 var45 lam45 app,
     lam45 _ _ _ (t Tm45 var45 lam45 app).

Definition app45 {Γ A B} : Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B
 := λ t u Tm45 var45 lam45 app45,
     app45 _ _ _
         (t Tm45 var45 lam45 app45)
         (u Tm45 var45 lam45 app45).

Definition v045 {Γ A} : Tm45 (snoc45 Γ A) A
 := var45 vz45.

Definition v145 {Γ A B} : Tm45 (snoc45 (snoc45 Γ A) B) A
 := var45 (vs45 vz45).

Definition v245 {Γ A B C} : Tm45 (snoc45 (snoc45 (snoc45 Γ A) B) C) A
 := var45 (vs45 (vs45 vz45)).

Definition v345 {Γ A B C D} : Tm45 (snoc45 (snoc45 (snoc45 (snoc45 Γ A) B) C) D) A
 := var45 (vs45 (vs45 (vs45 vz45))).

Definition v445 {Γ A B C D E} : Tm45 (snoc45 (snoc45 (snoc45 (snoc45 (snoc45 Γ A) B) C) D) E) A
 := var45 (vs45 (vs45 (vs45 (vs45 vz45)))).

Definition test45 {Γ A} : Tm45 Γ (arr45 (arr45 A A) (arr45 A A))
 := lam45 (lam45 (app45 v145 (app45 v145 (app45 v145 (app45 v145 (app45 v145 (app45 v145 v045))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty46 : Set
 := ∀ (Ty46 : Set)
      (ι   : Ty46)
      (arr : Ty46 → Ty46 → Ty46)
    , Ty46.

Definition ι46 : Ty46 := λ _ ι46 _, ι46.

Definition arr46 : Ty46 → Ty46 → Ty46
 := λ A B Ty46 ι46 arr46,
     arr46 (A Ty46 ι46 arr46) (B Ty46 ι46 arr46).

Definition Con46 : Set
 := ∀ (Con46  : Set)
      (nil  : Con46)
      (snoc : Con46 → Ty46 → Con46)
    , Con46.

Definition nil46 : Con46
 := λ Con46 nil46 snoc , nil46.

Definition snoc46 : Con46 → Ty46 → Con46
 := λ Γ A Con46 nil46 snoc46 , snoc46 (Γ Con46 nil46 snoc46) A.

Definition Var46 : Con46 → Ty46 → Set
 := λ Γ A ,
   ∀ (Var46 : Con46 → Ty46 → Set)
     (vz  : ∀ Γ A, Var46 (snoc46 Γ A) A)
     (vs  : ∀ Γ B A, Var46 Γ A → Var46 (snoc46 Γ B) A)
   , Var46 Γ A.

Definition vz46 {Γ A} : Var46 (snoc46 Γ A) A
 := λ Var46 vz46 vs , vz46 _ _.

Definition vs46 {Γ B A} : Var46 Γ A → Var46 (snoc46 Γ B) A
 := λ x Var46 vz46 vs46 , vs46 _ _ _ (x Var46 vz46 vs46).

Definition Tm46 : Con46 → Ty46 → Set
 := λ Γ A ,
   ∀ (Tm46  : Con46 → Ty46 → Set)
     (var   : ∀ Γ A     , Var46 Γ A → Tm46 Γ A)
     (lam   : ∀ Γ A B   , Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B))
     (app   : ∀ Γ A B   , Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B)
   , Tm46 Γ A.

Definition var46 {Γ A} : Var46 Γ A → Tm46 Γ A
 := λ x Tm46 var46 lam app,
     var46 _ _ x.

Definition lam46 {Γ A B} : Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B)
 := λ t Tm46 var46 lam46 app,
     lam46 _ _ _ (t Tm46 var46 lam46 app).

Definition app46 {Γ A B} : Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B
 := λ t u Tm46 var46 lam46 app46,
     app46 _ _ _
         (t Tm46 var46 lam46 app46)
         (u Tm46 var46 lam46 app46).

Definition v046 {Γ A} : Tm46 (snoc46 Γ A) A
 := var46 vz46.

Definition v146 {Γ A B} : Tm46 (snoc46 (snoc46 Γ A) B) A
 := var46 (vs46 vz46).

Definition v246 {Γ A B C} : Tm46 (snoc46 (snoc46 (snoc46 Γ A) B) C) A
 := var46 (vs46 (vs46 vz46)).

Definition v346 {Γ A B C D} : Tm46 (snoc46 (snoc46 (snoc46 (snoc46 Γ A) B) C) D) A
 := var46 (vs46 (vs46 (vs46 vz46))).

Definition v446 {Γ A B C D E} : Tm46 (snoc46 (snoc46 (snoc46 (snoc46 (snoc46 Γ A) B) C) D) E) A
 := var46 (vs46 (vs46 (vs46 (vs46 vz46)))).

Definition test46 {Γ A} : Tm46 Γ (arr46 (arr46 A A) (arr46 A A))
 := lam46 (lam46 (app46 v146 (app46 v146 (app46 v146 (app46 v146 (app46 v146 (app46 v146 v046))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty47 : Set
 := ∀ (Ty47 : Set)
      (ι   : Ty47)
      (arr : Ty47 → Ty47 → Ty47)
    , Ty47.

Definition ι47 : Ty47 := λ _ ι47 _, ι47.

Definition arr47 : Ty47 → Ty47 → Ty47
 := λ A B Ty47 ι47 arr47,
     arr47 (A Ty47 ι47 arr47) (B Ty47 ι47 arr47).

Definition Con47 : Set
 := ∀ (Con47  : Set)
      (nil  : Con47)
      (snoc : Con47 → Ty47 → Con47)
    , Con47.

Definition nil47 : Con47
 := λ Con47 nil47 snoc , nil47.

Definition snoc47 : Con47 → Ty47 → Con47
 := λ Γ A Con47 nil47 snoc47 , snoc47 (Γ Con47 nil47 snoc47) A.

Definition Var47 : Con47 → Ty47 → Set
 := λ Γ A ,
   ∀ (Var47 : Con47 → Ty47 → Set)
     (vz  : ∀ Γ A, Var47 (snoc47 Γ A) A)
     (vs  : ∀ Γ B A, Var47 Γ A → Var47 (snoc47 Γ B) A)
   , Var47 Γ A.

Definition vz47 {Γ A} : Var47 (snoc47 Γ A) A
 := λ Var47 vz47 vs , vz47 _ _.

Definition vs47 {Γ B A} : Var47 Γ A → Var47 (snoc47 Γ B) A
 := λ x Var47 vz47 vs47 , vs47 _ _ _ (x Var47 vz47 vs47).

Definition Tm47 : Con47 → Ty47 → Set
 := λ Γ A ,
   ∀ (Tm47  : Con47 → Ty47 → Set)
     (var   : ∀ Γ A     , Var47 Γ A → Tm47 Γ A)
     (lam   : ∀ Γ A B   , Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B))
     (app   : ∀ Γ A B   , Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B)
   , Tm47 Γ A.

Definition var47 {Γ A} : Var47 Γ A → Tm47 Γ A
 := λ x Tm47 var47 lam app,
     var47 _ _ x.

Definition lam47 {Γ A B} : Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B)
 := λ t Tm47 var47 lam47 app,
     lam47 _ _ _ (t Tm47 var47 lam47 app).

Definition app47 {Γ A B} : Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B
 := λ t u Tm47 var47 lam47 app47,
     app47 _ _ _
         (t Tm47 var47 lam47 app47)
         (u Tm47 var47 lam47 app47).

Definition v047 {Γ A} : Tm47 (snoc47 Γ A) A
 := var47 vz47.

Definition v147 {Γ A B} : Tm47 (snoc47 (snoc47 Γ A) B) A
 := var47 (vs47 vz47).

Definition v247 {Γ A B C} : Tm47 (snoc47 (snoc47 (snoc47 Γ A) B) C) A
 := var47 (vs47 (vs47 vz47)).

Definition v347 {Γ A B C D} : Tm47 (snoc47 (snoc47 (snoc47 (snoc47 Γ A) B) C) D) A
 := var47 (vs47 (vs47 (vs47 vz47))).

Definition v447 {Γ A B C D E} : Tm47 (snoc47 (snoc47 (snoc47 (snoc47 (snoc47 Γ A) B) C) D) E) A
 := var47 (vs47 (vs47 (vs47 (vs47 vz47)))).

Definition test47 {Γ A} : Tm47 Γ (arr47 (arr47 A A) (arr47 A A))
 := lam47 (lam47 (app47 v147 (app47 v147 (app47 v147 (app47 v147 (app47 v147 (app47 v147 v047))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty48 : Set
 := ∀ (Ty48 : Set)
      (ι   : Ty48)
      (arr : Ty48 → Ty48 → Ty48)
    , Ty48.

Definition ι48 : Ty48 := λ _ ι48 _, ι48.

Definition arr48 : Ty48 → Ty48 → Ty48
 := λ A B Ty48 ι48 arr48,
     arr48 (A Ty48 ι48 arr48) (B Ty48 ι48 arr48).

Definition Con48 : Set
 := ∀ (Con48  : Set)
      (nil  : Con48)
      (snoc : Con48 → Ty48 → Con48)
    , Con48.

Definition nil48 : Con48
 := λ Con48 nil48 snoc , nil48.

Definition snoc48 : Con48 → Ty48 → Con48
 := λ Γ A Con48 nil48 snoc48 , snoc48 (Γ Con48 nil48 snoc48) A.

Definition Var48 : Con48 → Ty48 → Set
 := λ Γ A ,
   ∀ (Var48 : Con48 → Ty48 → Set)
     (vz  : ∀ Γ A, Var48 (snoc48 Γ A) A)
     (vs  : ∀ Γ B A, Var48 Γ A → Var48 (snoc48 Γ B) A)
   , Var48 Γ A.

Definition vz48 {Γ A} : Var48 (snoc48 Γ A) A
 := λ Var48 vz48 vs , vz48 _ _.

Definition vs48 {Γ B A} : Var48 Γ A → Var48 (snoc48 Γ B) A
 := λ x Var48 vz48 vs48 , vs48 _ _ _ (x Var48 vz48 vs48).

Definition Tm48 : Con48 → Ty48 → Set
 := λ Γ A ,
   ∀ (Tm48  : Con48 → Ty48 → Set)
     (var   : ∀ Γ A     , Var48 Γ A → Tm48 Γ A)
     (lam   : ∀ Γ A B   , Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B))
     (app   : ∀ Γ A B   , Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B)
   , Tm48 Γ A.

Definition var48 {Γ A} : Var48 Γ A → Tm48 Γ A
 := λ x Tm48 var48 lam app,
     var48 _ _ x.

Definition lam48 {Γ A B} : Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B)
 := λ t Tm48 var48 lam48 app,
     lam48 _ _ _ (t Tm48 var48 lam48 app).

Definition app48 {Γ A B} : Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B
 := λ t u Tm48 var48 lam48 app48,
     app48 _ _ _
         (t Tm48 var48 lam48 app48)
         (u Tm48 var48 lam48 app48).

Definition v048 {Γ A} : Tm48 (snoc48 Γ A) A
 := var48 vz48.

Definition v148 {Γ A B} : Tm48 (snoc48 (snoc48 Γ A) B) A
 := var48 (vs48 vz48).

Definition v248 {Γ A B C} : Tm48 (snoc48 (snoc48 (snoc48 Γ A) B) C) A
 := var48 (vs48 (vs48 vz48)).

Definition v348 {Γ A B C D} : Tm48 (snoc48 (snoc48 (snoc48 (snoc48 Γ A) B) C) D) A
 := var48 (vs48 (vs48 (vs48 vz48))).

Definition v448 {Γ A B C D E} : Tm48 (snoc48 (snoc48 (snoc48 (snoc48 (snoc48 Γ A) B) C) D) E) A
 := var48 (vs48 (vs48 (vs48 (vs48 vz48)))).

Definition test48 {Γ A} : Tm48 Γ (arr48 (arr48 A A) (arr48 A A))
 := lam48 (lam48 (app48 v148 (app48 v148 (app48 v148 (app48 v148 (app48 v148 (app48 v148 v048))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty49 : Set
 := ∀ (Ty49 : Set)
      (ι   : Ty49)
      (arr : Ty49 → Ty49 → Ty49)
    , Ty49.

Definition ι49 : Ty49 := λ _ ι49 _, ι49.

Definition arr49 : Ty49 → Ty49 → Ty49
 := λ A B Ty49 ι49 arr49,
     arr49 (A Ty49 ι49 arr49) (B Ty49 ι49 arr49).

Definition Con49 : Set
 := ∀ (Con49  : Set)
      (nil  : Con49)
      (snoc : Con49 → Ty49 → Con49)
    , Con49.

Definition nil49 : Con49
 := λ Con49 nil49 snoc , nil49.

Definition snoc49 : Con49 → Ty49 → Con49
 := λ Γ A Con49 nil49 snoc49 , snoc49 (Γ Con49 nil49 snoc49) A.

Definition Var49 : Con49 → Ty49 → Set
 := λ Γ A ,
   ∀ (Var49 : Con49 → Ty49 → Set)
     (vz  : ∀ Γ A, Var49 (snoc49 Γ A) A)
     (vs  : ∀ Γ B A, Var49 Γ A → Var49 (snoc49 Γ B) A)
   , Var49 Γ A.

Definition vz49 {Γ A} : Var49 (snoc49 Γ A) A
 := λ Var49 vz49 vs , vz49 _ _.

Definition vs49 {Γ B A} : Var49 Γ A → Var49 (snoc49 Γ B) A
 := λ x Var49 vz49 vs49 , vs49 _ _ _ (x Var49 vz49 vs49).

Definition Tm49 : Con49 → Ty49 → Set
 := λ Γ A ,
   ∀ (Tm49  : Con49 → Ty49 → Set)
     (var   : ∀ Γ A     , Var49 Γ A → Tm49 Γ A)
     (lam   : ∀ Γ A B   , Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B))
     (app   : ∀ Γ A B   , Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B)
   , Tm49 Γ A.

Definition var49 {Γ A} : Var49 Γ A → Tm49 Γ A
 := λ x Tm49 var49 lam app,
     var49 _ _ x.

Definition lam49 {Γ A B} : Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B)
 := λ t Tm49 var49 lam49 app,
     lam49 _ _ _ (t Tm49 var49 lam49 app).

Definition app49 {Γ A B} : Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B
 := λ t u Tm49 var49 lam49 app49,
     app49 _ _ _
         (t Tm49 var49 lam49 app49)
         (u Tm49 var49 lam49 app49).

Definition v049 {Γ A} : Tm49 (snoc49 Γ A) A
 := var49 vz49.

Definition v149 {Γ A B} : Tm49 (snoc49 (snoc49 Γ A) B) A
 := var49 (vs49 vz49).

Definition v249 {Γ A B C} : Tm49 (snoc49 (snoc49 (snoc49 Γ A) B) C) A
 := var49 (vs49 (vs49 vz49)).

Definition v349 {Γ A B C D} : Tm49 (snoc49 (snoc49 (snoc49 (snoc49 Γ A) B) C) D) A
 := var49 (vs49 (vs49 (vs49 vz49))).

Definition v449 {Γ A B C D E} : Tm49 (snoc49 (snoc49 (snoc49 (snoc49 (snoc49 Γ A) B) C) D) E) A
 := var49 (vs49 (vs49 (vs49 (vs49 vz49)))).

Definition test49 {Γ A} : Tm49 Γ (arr49 (arr49 A A) (arr49 A A))
 := lam49 (lam49 (app49 v149 (app49 v149 (app49 v149 (app49 v149 (app49 v149 (app49 v149 v049))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty50 : Set
 := ∀ (Ty50 : Set)
      (ι   : Ty50)
      (arr : Ty50 → Ty50 → Ty50)
    , Ty50.

Definition ι50 : Ty50 := λ _ ι50 _, ι50.

Definition arr50 : Ty50 → Ty50 → Ty50
 := λ A B Ty50 ι50 arr50,
     arr50 (A Ty50 ι50 arr50) (B Ty50 ι50 arr50).

Definition Con50 : Set
 := ∀ (Con50  : Set)
      (nil  : Con50)
      (snoc : Con50 → Ty50 → Con50)
    , Con50.

Definition nil50 : Con50
 := λ Con50 nil50 snoc , nil50.

Definition snoc50 : Con50 → Ty50 → Con50
 := λ Γ A Con50 nil50 snoc50 , snoc50 (Γ Con50 nil50 snoc50) A.

Definition Var50 : Con50 → Ty50 → Set
 := λ Γ A ,
   ∀ (Var50 : Con50 → Ty50 → Set)
     (vz  : ∀ Γ A, Var50 (snoc50 Γ A) A)
     (vs  : ∀ Γ B A, Var50 Γ A → Var50 (snoc50 Γ B) A)
   , Var50 Γ A.

Definition vz50 {Γ A} : Var50 (snoc50 Γ A) A
 := λ Var50 vz50 vs , vz50 _ _.

Definition vs50 {Γ B A} : Var50 Γ A → Var50 (snoc50 Γ B) A
 := λ x Var50 vz50 vs50 , vs50 _ _ _ (x Var50 vz50 vs50).

Definition Tm50 : Con50 → Ty50 → Set
 := λ Γ A ,
   ∀ (Tm50  : Con50 → Ty50 → Set)
     (var   : ∀ Γ A     , Var50 Γ A → Tm50 Γ A)
     (lam   : ∀ Γ A B   , Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B))
     (app   : ∀ Γ A B   , Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B)
   , Tm50 Γ A.

Definition var50 {Γ A} : Var50 Γ A → Tm50 Γ A
 := λ x Tm50 var50 lam app,
     var50 _ _ x.

Definition lam50 {Γ A B} : Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B)
 := λ t Tm50 var50 lam50 app,
     lam50 _ _ _ (t Tm50 var50 lam50 app).

Definition app50 {Γ A B} : Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B
 := λ t u Tm50 var50 lam50 app50,
     app50 _ _ _
         (t Tm50 var50 lam50 app50)
         (u Tm50 var50 lam50 app50).

Definition v050 {Γ A} : Tm50 (snoc50 Γ A) A
 := var50 vz50.

Definition v150 {Γ A B} : Tm50 (snoc50 (snoc50 Γ A) B) A
 := var50 (vs50 vz50).

Definition v250 {Γ A B C} : Tm50 (snoc50 (snoc50 (snoc50 Γ A) B) C) A
 := var50 (vs50 (vs50 vz50)).

Definition v350 {Γ A B C D} : Tm50 (snoc50 (snoc50 (snoc50 (snoc50 Γ A) B) C) D) A
 := var50 (vs50 (vs50 (vs50 vz50))).

Definition v450 {Γ A B C D E} : Tm50 (snoc50 (snoc50 (snoc50 (snoc50 (snoc50 Γ A) B) C) D) E) A
 := var50 (vs50 (vs50 (vs50 (vs50 vz50)))).

Definition test50 {Γ A} : Tm50 Γ (arr50 (arr50 A A) (arr50 A A))
 := lam50 (lam50 (app50 v150 (app50 v150 (app50 v150 (app50 v150 (app50 v150 (app50 v150 v050))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty51 : Set
 := ∀ (Ty51 : Set)
      (ι   : Ty51)
      (arr : Ty51 → Ty51 → Ty51)
    , Ty51.

Definition ι51 : Ty51 := λ _ ι51 _, ι51.

Definition arr51 : Ty51 → Ty51 → Ty51
 := λ A B Ty51 ι51 arr51,
     arr51 (A Ty51 ι51 arr51) (B Ty51 ι51 arr51).

Definition Con51 : Set
 := ∀ (Con51  : Set)
      (nil  : Con51)
      (snoc : Con51 → Ty51 → Con51)
    , Con51.

Definition nil51 : Con51
 := λ Con51 nil51 snoc , nil51.

Definition snoc51 : Con51 → Ty51 → Con51
 := λ Γ A Con51 nil51 snoc51 , snoc51 (Γ Con51 nil51 snoc51) A.

Definition Var51 : Con51 → Ty51 → Set
 := λ Γ A ,
   ∀ (Var51 : Con51 → Ty51 → Set)
     (vz  : ∀ Γ A, Var51 (snoc51 Γ A) A)
     (vs  : ∀ Γ B A, Var51 Γ A → Var51 (snoc51 Γ B) A)
   , Var51 Γ A.

Definition vz51 {Γ A} : Var51 (snoc51 Γ A) A
 := λ Var51 vz51 vs , vz51 _ _.

Definition vs51 {Γ B A} : Var51 Γ A → Var51 (snoc51 Γ B) A
 := λ x Var51 vz51 vs51 , vs51 _ _ _ (x Var51 vz51 vs51).

Definition Tm51 : Con51 → Ty51 → Set
 := λ Γ A ,
   ∀ (Tm51  : Con51 → Ty51 → Set)
     (var   : ∀ Γ A     , Var51 Γ A → Tm51 Γ A)
     (lam   : ∀ Γ A B   , Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B))
     (app   : ∀ Γ A B   , Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B)
   , Tm51 Γ A.

Definition var51 {Γ A} : Var51 Γ A → Tm51 Γ A
 := λ x Tm51 var51 lam app,
     var51 _ _ x.

Definition lam51 {Γ A B} : Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B)
 := λ t Tm51 var51 lam51 app,
     lam51 _ _ _ (t Tm51 var51 lam51 app).

Definition app51 {Γ A B} : Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B
 := λ t u Tm51 var51 lam51 app51,
     app51 _ _ _
         (t Tm51 var51 lam51 app51)
         (u Tm51 var51 lam51 app51).

Definition v051 {Γ A} : Tm51 (snoc51 Γ A) A
 := var51 vz51.

Definition v151 {Γ A B} : Tm51 (snoc51 (snoc51 Γ A) B) A
 := var51 (vs51 vz51).

Definition v251 {Γ A B C} : Tm51 (snoc51 (snoc51 (snoc51 Γ A) B) C) A
 := var51 (vs51 (vs51 vz51)).

Definition v351 {Γ A B C D} : Tm51 (snoc51 (snoc51 (snoc51 (snoc51 Γ A) B) C) D) A
 := var51 (vs51 (vs51 (vs51 vz51))).

Definition v451 {Γ A B C D E} : Tm51 (snoc51 (snoc51 (snoc51 (snoc51 (snoc51 Γ A) B) C) D) E) A
 := var51 (vs51 (vs51 (vs51 (vs51 vz51)))).

Definition test51 {Γ A} : Tm51 Γ (arr51 (arr51 A A) (arr51 A A))
 := lam51 (lam51 (app51 v151 (app51 v151 (app51 v151 (app51 v151 (app51 v151 (app51 v151 v051))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty52 : Set
 := ∀ (Ty52 : Set)
      (ι   : Ty52)
      (arr : Ty52 → Ty52 → Ty52)
    , Ty52.

Definition ι52 : Ty52 := λ _ ι52 _, ι52.

Definition arr52 : Ty52 → Ty52 → Ty52
 := λ A B Ty52 ι52 arr52,
     arr52 (A Ty52 ι52 arr52) (B Ty52 ι52 arr52).

Definition Con52 : Set
 := ∀ (Con52  : Set)
      (nil  : Con52)
      (snoc : Con52 → Ty52 → Con52)
    , Con52.

Definition nil52 : Con52
 := λ Con52 nil52 snoc , nil52.

Definition snoc52 : Con52 → Ty52 → Con52
 := λ Γ A Con52 nil52 snoc52 , snoc52 (Γ Con52 nil52 snoc52) A.

Definition Var52 : Con52 → Ty52 → Set
 := λ Γ A ,
   ∀ (Var52 : Con52 → Ty52 → Set)
     (vz  : ∀ Γ A, Var52 (snoc52 Γ A) A)
     (vs  : ∀ Γ B A, Var52 Γ A → Var52 (snoc52 Γ B) A)
   , Var52 Γ A.

Definition vz52 {Γ A} : Var52 (snoc52 Γ A) A
 := λ Var52 vz52 vs , vz52 _ _.

Definition vs52 {Γ B A} : Var52 Γ A → Var52 (snoc52 Γ B) A
 := λ x Var52 vz52 vs52 , vs52 _ _ _ (x Var52 vz52 vs52).

Definition Tm52 : Con52 → Ty52 → Set
 := λ Γ A ,
   ∀ (Tm52  : Con52 → Ty52 → Set)
     (var   : ∀ Γ A     , Var52 Γ A → Tm52 Γ A)
     (lam   : ∀ Γ A B   , Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B))
     (app   : ∀ Γ A B   , Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B)
   , Tm52 Γ A.

Definition var52 {Γ A} : Var52 Γ A → Tm52 Γ A
 := λ x Tm52 var52 lam app,
     var52 _ _ x.

Definition lam52 {Γ A B} : Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B)
 := λ t Tm52 var52 lam52 app,
     lam52 _ _ _ (t Tm52 var52 lam52 app).

Definition app52 {Γ A B} : Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B
 := λ t u Tm52 var52 lam52 app52,
     app52 _ _ _
         (t Tm52 var52 lam52 app52)
         (u Tm52 var52 lam52 app52).

Definition v052 {Γ A} : Tm52 (snoc52 Γ A) A
 := var52 vz52.

Definition v152 {Γ A B} : Tm52 (snoc52 (snoc52 Γ A) B) A
 := var52 (vs52 vz52).

Definition v252 {Γ A B C} : Tm52 (snoc52 (snoc52 (snoc52 Γ A) B) C) A
 := var52 (vs52 (vs52 vz52)).

Definition v352 {Γ A B C D} : Tm52 (snoc52 (snoc52 (snoc52 (snoc52 Γ A) B) C) D) A
 := var52 (vs52 (vs52 (vs52 vz52))).

Definition v452 {Γ A B C D E} : Tm52 (snoc52 (snoc52 (snoc52 (snoc52 (snoc52 Γ A) B) C) D) E) A
 := var52 (vs52 (vs52 (vs52 (vs52 vz52)))).

Definition test52 {Γ A} : Tm52 Γ (arr52 (arr52 A A) (arr52 A A))
 := lam52 (lam52 (app52 v152 (app52 v152 (app52 v152 (app52 v152 (app52 v152 (app52 v152 v052))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty53 : Set
 := ∀ (Ty53 : Set)
      (ι   : Ty53)
      (arr : Ty53 → Ty53 → Ty53)
    , Ty53.

Definition ι53 : Ty53 := λ _ ι53 _, ι53.

Definition arr53 : Ty53 → Ty53 → Ty53
 := λ A B Ty53 ι53 arr53,
     arr53 (A Ty53 ι53 arr53) (B Ty53 ι53 arr53).

Definition Con53 : Set
 := ∀ (Con53  : Set)
      (nil  : Con53)
      (snoc : Con53 → Ty53 → Con53)
    , Con53.

Definition nil53 : Con53
 := λ Con53 nil53 snoc , nil53.

Definition snoc53 : Con53 → Ty53 → Con53
 := λ Γ A Con53 nil53 snoc53 , snoc53 (Γ Con53 nil53 snoc53) A.

Definition Var53 : Con53 → Ty53 → Set
 := λ Γ A ,
   ∀ (Var53 : Con53 → Ty53 → Set)
     (vz  : ∀ Γ A, Var53 (snoc53 Γ A) A)
     (vs  : ∀ Γ B A, Var53 Γ A → Var53 (snoc53 Γ B) A)
   , Var53 Γ A.

Definition vz53 {Γ A} : Var53 (snoc53 Γ A) A
 := λ Var53 vz53 vs , vz53 _ _.

Definition vs53 {Γ B A} : Var53 Γ A → Var53 (snoc53 Γ B) A
 := λ x Var53 vz53 vs53 , vs53 _ _ _ (x Var53 vz53 vs53).

Definition Tm53 : Con53 → Ty53 → Set
 := λ Γ A ,
   ∀ (Tm53  : Con53 → Ty53 → Set)
     (var   : ∀ Γ A     , Var53 Γ A → Tm53 Γ A)
     (lam   : ∀ Γ A B   , Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B))
     (app   : ∀ Γ A B   , Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B)
   , Tm53 Γ A.

Definition var53 {Γ A} : Var53 Γ A → Tm53 Γ A
 := λ x Tm53 var53 lam app,
     var53 _ _ x.

Definition lam53 {Γ A B} : Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B)
 := λ t Tm53 var53 lam53 app,
     lam53 _ _ _ (t Tm53 var53 lam53 app).

Definition app53 {Γ A B} : Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B
 := λ t u Tm53 var53 lam53 app53,
     app53 _ _ _
         (t Tm53 var53 lam53 app53)
         (u Tm53 var53 lam53 app53).

Definition v053 {Γ A} : Tm53 (snoc53 Γ A) A
 := var53 vz53.

Definition v153 {Γ A B} : Tm53 (snoc53 (snoc53 Γ A) B) A
 := var53 (vs53 vz53).

Definition v253 {Γ A B C} : Tm53 (snoc53 (snoc53 (snoc53 Γ A) B) C) A
 := var53 (vs53 (vs53 vz53)).

Definition v353 {Γ A B C D} : Tm53 (snoc53 (snoc53 (snoc53 (snoc53 Γ A) B) C) D) A
 := var53 (vs53 (vs53 (vs53 vz53))).

Definition v453 {Γ A B C D E} : Tm53 (snoc53 (snoc53 (snoc53 (snoc53 (snoc53 Γ A) B) C) D) E) A
 := var53 (vs53 (vs53 (vs53 (vs53 vz53)))).

Definition test53 {Γ A} : Tm53 Γ (arr53 (arr53 A A) (arr53 A A))
 := lam53 (lam53 (app53 v153 (app53 v153 (app53 v153 (app53 v153 (app53 v153 (app53 v153 v053))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty54 : Set
 := ∀ (Ty54 : Set)
      (ι   : Ty54)
      (arr : Ty54 → Ty54 → Ty54)
    , Ty54.

Definition ι54 : Ty54 := λ _ ι54 _, ι54.

Definition arr54 : Ty54 → Ty54 → Ty54
 := λ A B Ty54 ι54 arr54,
     arr54 (A Ty54 ι54 arr54) (B Ty54 ι54 arr54).

Definition Con54 : Set
 := ∀ (Con54  : Set)
      (nil  : Con54)
      (snoc : Con54 → Ty54 → Con54)
    , Con54.

Definition nil54 : Con54
 := λ Con54 nil54 snoc , nil54.

Definition snoc54 : Con54 → Ty54 → Con54
 := λ Γ A Con54 nil54 snoc54 , snoc54 (Γ Con54 nil54 snoc54) A.

Definition Var54 : Con54 → Ty54 → Set
 := λ Γ A ,
   ∀ (Var54 : Con54 → Ty54 → Set)
     (vz  : ∀ Γ A, Var54 (snoc54 Γ A) A)
     (vs  : ∀ Γ B A, Var54 Γ A → Var54 (snoc54 Γ B) A)
   , Var54 Γ A.

Definition vz54 {Γ A} : Var54 (snoc54 Γ A) A
 := λ Var54 vz54 vs , vz54 _ _.

Definition vs54 {Γ B A} : Var54 Γ A → Var54 (snoc54 Γ B) A
 := λ x Var54 vz54 vs54 , vs54 _ _ _ (x Var54 vz54 vs54).

Definition Tm54 : Con54 → Ty54 → Set
 := λ Γ A ,
   ∀ (Tm54  : Con54 → Ty54 → Set)
     (var   : ∀ Γ A     , Var54 Γ A → Tm54 Γ A)
     (lam   : ∀ Γ A B   , Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B))
     (app   : ∀ Γ A B   , Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B)
   , Tm54 Γ A.

Definition var54 {Γ A} : Var54 Γ A → Tm54 Γ A
 := λ x Tm54 var54 lam app,
     var54 _ _ x.

Definition lam54 {Γ A B} : Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B)
 := λ t Tm54 var54 lam54 app,
     lam54 _ _ _ (t Tm54 var54 lam54 app).

Definition app54 {Γ A B} : Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B
 := λ t u Tm54 var54 lam54 app54,
     app54 _ _ _
         (t Tm54 var54 lam54 app54)
         (u Tm54 var54 lam54 app54).

Definition v054 {Γ A} : Tm54 (snoc54 Γ A) A
 := var54 vz54.

Definition v154 {Γ A B} : Tm54 (snoc54 (snoc54 Γ A) B) A
 := var54 (vs54 vz54).

Definition v254 {Γ A B C} : Tm54 (snoc54 (snoc54 (snoc54 Γ A) B) C) A
 := var54 (vs54 (vs54 vz54)).

Definition v354 {Γ A B C D} : Tm54 (snoc54 (snoc54 (snoc54 (snoc54 Γ A) B) C) D) A
 := var54 (vs54 (vs54 (vs54 vz54))).

Definition v454 {Γ A B C D E} : Tm54 (snoc54 (snoc54 (snoc54 (snoc54 (snoc54 Γ A) B) C) D) E) A
 := var54 (vs54 (vs54 (vs54 (vs54 vz54)))).

Definition test54 {Γ A} : Tm54 Γ (arr54 (arr54 A A) (arr54 A A))
 := lam54 (lam54 (app54 v154 (app54 v154 (app54 v154 (app54 v154 (app54 v154 (app54 v154 v054))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty55 : Set
 := ∀ (Ty55 : Set)
      (ι   : Ty55)
      (arr : Ty55 → Ty55 → Ty55)
    , Ty55.

Definition ι55 : Ty55 := λ _ ι55 _, ι55.

Definition arr55 : Ty55 → Ty55 → Ty55
 := λ A B Ty55 ι55 arr55,
     arr55 (A Ty55 ι55 arr55) (B Ty55 ι55 arr55).

Definition Con55 : Set
 := ∀ (Con55  : Set)
      (nil  : Con55)
      (snoc : Con55 → Ty55 → Con55)
    , Con55.

Definition nil55 : Con55
 := λ Con55 nil55 snoc , nil55.

Definition snoc55 : Con55 → Ty55 → Con55
 := λ Γ A Con55 nil55 snoc55 , snoc55 (Γ Con55 nil55 snoc55) A.

Definition Var55 : Con55 → Ty55 → Set
 := λ Γ A ,
   ∀ (Var55 : Con55 → Ty55 → Set)
     (vz  : ∀ Γ A, Var55 (snoc55 Γ A) A)
     (vs  : ∀ Γ B A, Var55 Γ A → Var55 (snoc55 Γ B) A)
   , Var55 Γ A.

Definition vz55 {Γ A} : Var55 (snoc55 Γ A) A
 := λ Var55 vz55 vs , vz55 _ _.

Definition vs55 {Γ B A} : Var55 Γ A → Var55 (snoc55 Γ B) A
 := λ x Var55 vz55 vs55 , vs55 _ _ _ (x Var55 vz55 vs55).

Definition Tm55 : Con55 → Ty55 → Set
 := λ Γ A ,
   ∀ (Tm55  : Con55 → Ty55 → Set)
     (var   : ∀ Γ A     , Var55 Γ A → Tm55 Γ A)
     (lam   : ∀ Γ A B   , Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B))
     (app   : ∀ Γ A B   , Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B)
   , Tm55 Γ A.

Definition var55 {Γ A} : Var55 Γ A → Tm55 Γ A
 := λ x Tm55 var55 lam app,
     var55 _ _ x.

Definition lam55 {Γ A B} : Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B)
 := λ t Tm55 var55 lam55 app,
     lam55 _ _ _ (t Tm55 var55 lam55 app).

Definition app55 {Γ A B} : Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B
 := λ t u Tm55 var55 lam55 app55,
     app55 _ _ _
         (t Tm55 var55 lam55 app55)
         (u Tm55 var55 lam55 app55).

Definition v055 {Γ A} : Tm55 (snoc55 Γ A) A
 := var55 vz55.

Definition v155 {Γ A B} : Tm55 (snoc55 (snoc55 Γ A) B) A
 := var55 (vs55 vz55).

Definition v255 {Γ A B C} : Tm55 (snoc55 (snoc55 (snoc55 Γ A) B) C) A
 := var55 (vs55 (vs55 vz55)).

Definition v355 {Γ A B C D} : Tm55 (snoc55 (snoc55 (snoc55 (snoc55 Γ A) B) C) D) A
 := var55 (vs55 (vs55 (vs55 vz55))).

Definition v455 {Γ A B C D E} : Tm55 (snoc55 (snoc55 (snoc55 (snoc55 (snoc55 Γ A) B) C) D) E) A
 := var55 (vs55 (vs55 (vs55 (vs55 vz55)))).

Definition test55 {Γ A} : Tm55 Γ (arr55 (arr55 A A) (arr55 A A))
 := lam55 (lam55 (app55 v155 (app55 v155 (app55 v155 (app55 v155 (app55 v155 (app55 v155 v055))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty56 : Set
 := ∀ (Ty56 : Set)
      (ι   : Ty56)
      (arr : Ty56 → Ty56 → Ty56)
    , Ty56.

Definition ι56 : Ty56 := λ _ ι56 _, ι56.

Definition arr56 : Ty56 → Ty56 → Ty56
 := λ A B Ty56 ι56 arr56,
     arr56 (A Ty56 ι56 arr56) (B Ty56 ι56 arr56).

Definition Con56 : Set
 := ∀ (Con56  : Set)
      (nil  : Con56)
      (snoc : Con56 → Ty56 → Con56)
    , Con56.

Definition nil56 : Con56
 := λ Con56 nil56 snoc , nil56.

Definition snoc56 : Con56 → Ty56 → Con56
 := λ Γ A Con56 nil56 snoc56 , snoc56 (Γ Con56 nil56 snoc56) A.

Definition Var56 : Con56 → Ty56 → Set
 := λ Γ A ,
   ∀ (Var56 : Con56 → Ty56 → Set)
     (vz  : ∀ Γ A, Var56 (snoc56 Γ A) A)
     (vs  : ∀ Γ B A, Var56 Γ A → Var56 (snoc56 Γ B) A)
   , Var56 Γ A.

Definition vz56 {Γ A} : Var56 (snoc56 Γ A) A
 := λ Var56 vz56 vs , vz56 _ _.

Definition vs56 {Γ B A} : Var56 Γ A → Var56 (snoc56 Γ B) A
 := λ x Var56 vz56 vs56 , vs56 _ _ _ (x Var56 vz56 vs56).

Definition Tm56 : Con56 → Ty56 → Set
 := λ Γ A ,
   ∀ (Tm56  : Con56 → Ty56 → Set)
     (var   : ∀ Γ A     , Var56 Γ A → Tm56 Γ A)
     (lam   : ∀ Γ A B   , Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B))
     (app   : ∀ Γ A B   , Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B)
   , Tm56 Γ A.

Definition var56 {Γ A} : Var56 Γ A → Tm56 Γ A
 := λ x Tm56 var56 lam app,
     var56 _ _ x.

Definition lam56 {Γ A B} : Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B)
 := λ t Tm56 var56 lam56 app,
     lam56 _ _ _ (t Tm56 var56 lam56 app).

Definition app56 {Γ A B} : Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B
 := λ t u Tm56 var56 lam56 app56,
     app56 _ _ _
         (t Tm56 var56 lam56 app56)
         (u Tm56 var56 lam56 app56).

Definition v056 {Γ A} : Tm56 (snoc56 Γ A) A
 := var56 vz56.

Definition v156 {Γ A B} : Tm56 (snoc56 (snoc56 Γ A) B) A
 := var56 (vs56 vz56).

Definition v256 {Γ A B C} : Tm56 (snoc56 (snoc56 (snoc56 Γ A) B) C) A
 := var56 (vs56 (vs56 vz56)).

Definition v356 {Γ A B C D} : Tm56 (snoc56 (snoc56 (snoc56 (snoc56 Γ A) B) C) D) A
 := var56 (vs56 (vs56 (vs56 vz56))).

Definition v456 {Γ A B C D E} : Tm56 (snoc56 (snoc56 (snoc56 (snoc56 (snoc56 Γ A) B) C) D) E) A
 := var56 (vs56 (vs56 (vs56 (vs56 vz56)))).

Definition test56 {Γ A} : Tm56 Γ (arr56 (arr56 A A) (arr56 A A))
 := lam56 (lam56 (app56 v156 (app56 v156 (app56 v156 (app56 v156 (app56 v156 (app56 v156 v056))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty57 : Set
 := ∀ (Ty57 : Set)
      (ι   : Ty57)
      (arr : Ty57 → Ty57 → Ty57)
    , Ty57.

Definition ι57 : Ty57 := λ _ ι57 _, ι57.

Definition arr57 : Ty57 → Ty57 → Ty57
 := λ A B Ty57 ι57 arr57,
     arr57 (A Ty57 ι57 arr57) (B Ty57 ι57 arr57).

Definition Con57 : Set
 := ∀ (Con57  : Set)
      (nil  : Con57)
      (snoc : Con57 → Ty57 → Con57)
    , Con57.

Definition nil57 : Con57
 := λ Con57 nil57 snoc , nil57.

Definition snoc57 : Con57 → Ty57 → Con57
 := λ Γ A Con57 nil57 snoc57 , snoc57 (Γ Con57 nil57 snoc57) A.

Definition Var57 : Con57 → Ty57 → Set
 := λ Γ A ,
   ∀ (Var57 : Con57 → Ty57 → Set)
     (vz  : ∀ Γ A, Var57 (snoc57 Γ A) A)
     (vs  : ∀ Γ B A, Var57 Γ A → Var57 (snoc57 Γ B) A)
   , Var57 Γ A.

Definition vz57 {Γ A} : Var57 (snoc57 Γ A) A
 := λ Var57 vz57 vs , vz57 _ _.

Definition vs57 {Γ B A} : Var57 Γ A → Var57 (snoc57 Γ B) A
 := λ x Var57 vz57 vs57 , vs57 _ _ _ (x Var57 vz57 vs57).

Definition Tm57 : Con57 → Ty57 → Set
 := λ Γ A ,
   ∀ (Tm57  : Con57 → Ty57 → Set)
     (var   : ∀ Γ A     , Var57 Γ A → Tm57 Γ A)
     (lam   : ∀ Γ A B   , Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B))
     (app   : ∀ Γ A B   , Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B)
   , Tm57 Γ A.

Definition var57 {Γ A} : Var57 Γ A → Tm57 Γ A
 := λ x Tm57 var57 lam app,
     var57 _ _ x.

Definition lam57 {Γ A B} : Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B)
 := λ t Tm57 var57 lam57 app,
     lam57 _ _ _ (t Tm57 var57 lam57 app).

Definition app57 {Γ A B} : Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B
 := λ t u Tm57 var57 lam57 app57,
     app57 _ _ _
         (t Tm57 var57 lam57 app57)
         (u Tm57 var57 lam57 app57).

Definition v057 {Γ A} : Tm57 (snoc57 Γ A) A
 := var57 vz57.

Definition v157 {Γ A B} : Tm57 (snoc57 (snoc57 Γ A) B) A
 := var57 (vs57 vz57).

Definition v257 {Γ A B C} : Tm57 (snoc57 (snoc57 (snoc57 Γ A) B) C) A
 := var57 (vs57 (vs57 vz57)).

Definition v357 {Γ A B C D} : Tm57 (snoc57 (snoc57 (snoc57 (snoc57 Γ A) B) C) D) A
 := var57 (vs57 (vs57 (vs57 vz57))).

Definition v457 {Γ A B C D E} : Tm57 (snoc57 (snoc57 (snoc57 (snoc57 (snoc57 Γ A) B) C) D) E) A
 := var57 (vs57 (vs57 (vs57 (vs57 vz57)))).

Definition test57 {Γ A} : Tm57 Γ (arr57 (arr57 A A) (arr57 A A))
 := lam57 (lam57 (app57 v157 (app57 v157 (app57 v157 (app57 v157 (app57 v157 (app57 v157 v057))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty58 : Set
 := ∀ (Ty58 : Set)
      (ι   : Ty58)
      (arr : Ty58 → Ty58 → Ty58)
    , Ty58.

Definition ι58 : Ty58 := λ _ ι58 _, ι58.

Definition arr58 : Ty58 → Ty58 → Ty58
 := λ A B Ty58 ι58 arr58,
     arr58 (A Ty58 ι58 arr58) (B Ty58 ι58 arr58).

Definition Con58 : Set
 := ∀ (Con58  : Set)
      (nil  : Con58)
      (snoc : Con58 → Ty58 → Con58)
    , Con58.

Definition nil58 : Con58
 := λ Con58 nil58 snoc , nil58.

Definition snoc58 : Con58 → Ty58 → Con58
 := λ Γ A Con58 nil58 snoc58 , snoc58 (Γ Con58 nil58 snoc58) A.

Definition Var58 : Con58 → Ty58 → Set
 := λ Γ A ,
   ∀ (Var58 : Con58 → Ty58 → Set)
     (vz  : ∀ Γ A, Var58 (snoc58 Γ A) A)
     (vs  : ∀ Γ B A, Var58 Γ A → Var58 (snoc58 Γ B) A)
   , Var58 Γ A.

Definition vz58 {Γ A} : Var58 (snoc58 Γ A) A
 := λ Var58 vz58 vs , vz58 _ _.

Definition vs58 {Γ B A} : Var58 Γ A → Var58 (snoc58 Γ B) A
 := λ x Var58 vz58 vs58 , vs58 _ _ _ (x Var58 vz58 vs58).

Definition Tm58 : Con58 → Ty58 → Set
 := λ Γ A ,
   ∀ (Tm58  : Con58 → Ty58 → Set)
     (var   : ∀ Γ A     , Var58 Γ A → Tm58 Γ A)
     (lam   : ∀ Γ A B   , Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B))
     (app   : ∀ Γ A B   , Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B)
   , Tm58 Γ A.

Definition var58 {Γ A} : Var58 Γ A → Tm58 Γ A
 := λ x Tm58 var58 lam app,
     var58 _ _ x.

Definition lam58 {Γ A B} : Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B)
 := λ t Tm58 var58 lam58 app,
     lam58 _ _ _ (t Tm58 var58 lam58 app).

Definition app58 {Γ A B} : Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B
 := λ t u Tm58 var58 lam58 app58,
     app58 _ _ _
         (t Tm58 var58 lam58 app58)
         (u Tm58 var58 lam58 app58).

Definition v058 {Γ A} : Tm58 (snoc58 Γ A) A
 := var58 vz58.

Definition v158 {Γ A B} : Tm58 (snoc58 (snoc58 Γ A) B) A
 := var58 (vs58 vz58).

Definition v258 {Γ A B C} : Tm58 (snoc58 (snoc58 (snoc58 Γ A) B) C) A
 := var58 (vs58 (vs58 vz58)).

Definition v358 {Γ A B C D} : Tm58 (snoc58 (snoc58 (snoc58 (snoc58 Γ A) B) C) D) A
 := var58 (vs58 (vs58 (vs58 vz58))).

Definition v458 {Γ A B C D E} : Tm58 (snoc58 (snoc58 (snoc58 (snoc58 (snoc58 Γ A) B) C) D) E) A
 := var58 (vs58 (vs58 (vs58 (vs58 vz58)))).

Definition test58 {Γ A} : Tm58 Γ (arr58 (arr58 A A) (arr58 A A))
 := lam58 (lam58 (app58 v158 (app58 v158 (app58 v158 (app58 v158 (app58 v158 (app58 v158 v058))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty59 : Set
 := ∀ (Ty59 : Set)
      (ι   : Ty59)
      (arr : Ty59 → Ty59 → Ty59)
    , Ty59.

Definition ι59 : Ty59 := λ _ ι59 _, ι59.

Definition arr59 : Ty59 → Ty59 → Ty59
 := λ A B Ty59 ι59 arr59,
     arr59 (A Ty59 ι59 arr59) (B Ty59 ι59 arr59).

Definition Con59 : Set
 := ∀ (Con59  : Set)
      (nil  : Con59)
      (snoc : Con59 → Ty59 → Con59)
    , Con59.

Definition nil59 : Con59
 := λ Con59 nil59 snoc , nil59.

Definition snoc59 : Con59 → Ty59 → Con59
 := λ Γ A Con59 nil59 snoc59 , snoc59 (Γ Con59 nil59 snoc59) A.

Definition Var59 : Con59 → Ty59 → Set
 := λ Γ A ,
   ∀ (Var59 : Con59 → Ty59 → Set)
     (vz  : ∀ Γ A, Var59 (snoc59 Γ A) A)
     (vs  : ∀ Γ B A, Var59 Γ A → Var59 (snoc59 Γ B) A)
   , Var59 Γ A.

Definition vz59 {Γ A} : Var59 (snoc59 Γ A) A
 := λ Var59 vz59 vs , vz59 _ _.

Definition vs59 {Γ B A} : Var59 Γ A → Var59 (snoc59 Γ B) A
 := λ x Var59 vz59 vs59 , vs59 _ _ _ (x Var59 vz59 vs59).

Definition Tm59 : Con59 → Ty59 → Set
 := λ Γ A ,
   ∀ (Tm59  : Con59 → Ty59 → Set)
     (var   : ∀ Γ A     , Var59 Γ A → Tm59 Γ A)
     (lam   : ∀ Γ A B   , Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B))
     (app   : ∀ Γ A B   , Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B)
   , Tm59 Γ A.

Definition var59 {Γ A} : Var59 Γ A → Tm59 Γ A
 := λ x Tm59 var59 lam app,
     var59 _ _ x.

Definition lam59 {Γ A B} : Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B)
 := λ t Tm59 var59 lam59 app,
     lam59 _ _ _ (t Tm59 var59 lam59 app).

Definition app59 {Γ A B} : Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B
 := λ t u Tm59 var59 lam59 app59,
     app59 _ _ _
         (t Tm59 var59 lam59 app59)
         (u Tm59 var59 lam59 app59).

Definition v059 {Γ A} : Tm59 (snoc59 Γ A) A
 := var59 vz59.

Definition v159 {Γ A B} : Tm59 (snoc59 (snoc59 Γ A) B) A
 := var59 (vs59 vz59).

Definition v259 {Γ A B C} : Tm59 (snoc59 (snoc59 (snoc59 Γ A) B) C) A
 := var59 (vs59 (vs59 vz59)).

Definition v359 {Γ A B C D} : Tm59 (snoc59 (snoc59 (snoc59 (snoc59 Γ A) B) C) D) A
 := var59 (vs59 (vs59 (vs59 vz59))).

Definition v459 {Γ A B C D E} : Tm59 (snoc59 (snoc59 (snoc59 (snoc59 (snoc59 Γ A) B) C) D) E) A
 := var59 (vs59 (vs59 (vs59 (vs59 vz59)))).

Definition test59 {Γ A} : Tm59 Γ (arr59 (arr59 A A) (arr59 A A))
 := lam59 (lam59 (app59 v159 (app59 v159 (app59 v159 (app59 v159 (app59 v159 (app59 v159 v059))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty60 : Set
 := ∀ (Ty60 : Set)
      (ι   : Ty60)
      (arr : Ty60 → Ty60 → Ty60)
    , Ty60.

Definition ι60 : Ty60 := λ _ ι60 _, ι60.

Definition arr60 : Ty60 → Ty60 → Ty60
 := λ A B Ty60 ι60 arr60,
     arr60 (A Ty60 ι60 arr60) (B Ty60 ι60 arr60).

Definition Con60 : Set
 := ∀ (Con60  : Set)
      (nil  : Con60)
      (snoc : Con60 → Ty60 → Con60)
    , Con60.

Definition nil60 : Con60
 := λ Con60 nil60 snoc , nil60.

Definition snoc60 : Con60 → Ty60 → Con60
 := λ Γ A Con60 nil60 snoc60 , snoc60 (Γ Con60 nil60 snoc60) A.

Definition Var60 : Con60 → Ty60 → Set
 := λ Γ A ,
   ∀ (Var60 : Con60 → Ty60 → Set)
     (vz  : ∀ Γ A, Var60 (snoc60 Γ A) A)
     (vs  : ∀ Γ B A, Var60 Γ A → Var60 (snoc60 Γ B) A)
   , Var60 Γ A.

Definition vz60 {Γ A} : Var60 (snoc60 Γ A) A
 := λ Var60 vz60 vs , vz60 _ _.

Definition vs60 {Γ B A} : Var60 Γ A → Var60 (snoc60 Γ B) A
 := λ x Var60 vz60 vs60 , vs60 _ _ _ (x Var60 vz60 vs60).

Definition Tm60 : Con60 → Ty60 → Set
 := λ Γ A ,
   ∀ (Tm60  : Con60 → Ty60 → Set)
     (var   : ∀ Γ A     , Var60 Γ A → Tm60 Γ A)
     (lam   : ∀ Γ A B   , Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B))
     (app   : ∀ Γ A B   , Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B)
   , Tm60 Γ A.

Definition var60 {Γ A} : Var60 Γ A → Tm60 Γ A
 := λ x Tm60 var60 lam app,
     var60 _ _ x.

Definition lam60 {Γ A B} : Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B)
 := λ t Tm60 var60 lam60 app,
     lam60 _ _ _ (t Tm60 var60 lam60 app).

Definition app60 {Γ A B} : Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B
 := λ t u Tm60 var60 lam60 app60,
     app60 _ _ _
         (t Tm60 var60 lam60 app60)
         (u Tm60 var60 lam60 app60).

Definition v060 {Γ A} : Tm60 (snoc60 Γ A) A
 := var60 vz60.

Definition v160 {Γ A B} : Tm60 (snoc60 (snoc60 Γ A) B) A
 := var60 (vs60 vz60).

Definition v260 {Γ A B C} : Tm60 (snoc60 (snoc60 (snoc60 Γ A) B) C) A
 := var60 (vs60 (vs60 vz60)).

Definition v360 {Γ A B C D} : Tm60 (snoc60 (snoc60 (snoc60 (snoc60 Γ A) B) C) D) A
 := var60 (vs60 (vs60 (vs60 vz60))).

Definition v460 {Γ A B C D E} : Tm60 (snoc60 (snoc60 (snoc60 (snoc60 (snoc60 Γ A) B) C) D) E) A
 := var60 (vs60 (vs60 (vs60 (vs60 vz60)))).

Definition test60 {Γ A} : Tm60 Γ (arr60 (arr60 A A) (arr60 A A))
 := lam60 (lam60 (app60 v160 (app60 v160 (app60 v160 (app60 v160 (app60 v160 (app60 v160 v060))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty61 : Set
 := ∀ (Ty61 : Set)
      (ι   : Ty61)
      (arr : Ty61 → Ty61 → Ty61)
    , Ty61.

Definition ι61 : Ty61 := λ _ ι61 _, ι61.

Definition arr61 : Ty61 → Ty61 → Ty61
 := λ A B Ty61 ι61 arr61,
     arr61 (A Ty61 ι61 arr61) (B Ty61 ι61 arr61).

Definition Con61 : Set
 := ∀ (Con61  : Set)
      (nil  : Con61)
      (snoc : Con61 → Ty61 → Con61)
    , Con61.

Definition nil61 : Con61
 := λ Con61 nil61 snoc , nil61.

Definition snoc61 : Con61 → Ty61 → Con61
 := λ Γ A Con61 nil61 snoc61 , snoc61 (Γ Con61 nil61 snoc61) A.

Definition Var61 : Con61 → Ty61 → Set
 := λ Γ A ,
   ∀ (Var61 : Con61 → Ty61 → Set)
     (vz  : ∀ Γ A, Var61 (snoc61 Γ A) A)
     (vs  : ∀ Γ B A, Var61 Γ A → Var61 (snoc61 Γ B) A)
   , Var61 Γ A.

Definition vz61 {Γ A} : Var61 (snoc61 Γ A) A
 := λ Var61 vz61 vs , vz61 _ _.

Definition vs61 {Γ B A} : Var61 Γ A → Var61 (snoc61 Γ B) A
 := λ x Var61 vz61 vs61 , vs61 _ _ _ (x Var61 vz61 vs61).

Definition Tm61 : Con61 → Ty61 → Set
 := λ Γ A ,
   ∀ (Tm61  : Con61 → Ty61 → Set)
     (var   : ∀ Γ A     , Var61 Γ A → Tm61 Γ A)
     (lam   : ∀ Γ A B   , Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B))
     (app   : ∀ Γ A B   , Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B)
   , Tm61 Γ A.

Definition var61 {Γ A} : Var61 Γ A → Tm61 Γ A
 := λ x Tm61 var61 lam app,
     var61 _ _ x.

Definition lam61 {Γ A B} : Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B)
 := λ t Tm61 var61 lam61 app,
     lam61 _ _ _ (t Tm61 var61 lam61 app).

Definition app61 {Γ A B} : Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B
 := λ t u Tm61 var61 lam61 app61,
     app61 _ _ _
         (t Tm61 var61 lam61 app61)
         (u Tm61 var61 lam61 app61).

Definition v061 {Γ A} : Tm61 (snoc61 Γ A) A
 := var61 vz61.

Definition v161 {Γ A B} : Tm61 (snoc61 (snoc61 Γ A) B) A
 := var61 (vs61 vz61).

Definition v261 {Γ A B C} : Tm61 (snoc61 (snoc61 (snoc61 Γ A) B) C) A
 := var61 (vs61 (vs61 vz61)).

Definition v361 {Γ A B C D} : Tm61 (snoc61 (snoc61 (snoc61 (snoc61 Γ A) B) C) D) A
 := var61 (vs61 (vs61 (vs61 vz61))).

Definition v461 {Γ A B C D E} : Tm61 (snoc61 (snoc61 (snoc61 (snoc61 (snoc61 Γ A) B) C) D) E) A
 := var61 (vs61 (vs61 (vs61 (vs61 vz61)))).

Definition test61 {Γ A} : Tm61 Γ (arr61 (arr61 A A) (arr61 A A))
 := lam61 (lam61 (app61 v161 (app61 v161 (app61 v161 (app61 v161 (app61 v161 (app61 v161 v061))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty62 : Set
 := ∀ (Ty62 : Set)
      (ι   : Ty62)
      (arr : Ty62 → Ty62 → Ty62)
    , Ty62.

Definition ι62 : Ty62 := λ _ ι62 _, ι62.

Definition arr62 : Ty62 → Ty62 → Ty62
 := λ A B Ty62 ι62 arr62,
     arr62 (A Ty62 ι62 arr62) (B Ty62 ι62 arr62).

Definition Con62 : Set
 := ∀ (Con62  : Set)
      (nil  : Con62)
      (snoc : Con62 → Ty62 → Con62)
    , Con62.

Definition nil62 : Con62
 := λ Con62 nil62 snoc , nil62.

Definition snoc62 : Con62 → Ty62 → Con62
 := λ Γ A Con62 nil62 snoc62 , snoc62 (Γ Con62 nil62 snoc62) A.

Definition Var62 : Con62 → Ty62 → Set
 := λ Γ A ,
   ∀ (Var62 : Con62 → Ty62 → Set)
     (vz  : ∀ Γ A, Var62 (snoc62 Γ A) A)
     (vs  : ∀ Γ B A, Var62 Γ A → Var62 (snoc62 Γ B) A)
   , Var62 Γ A.

Definition vz62 {Γ A} : Var62 (snoc62 Γ A) A
 := λ Var62 vz62 vs , vz62 _ _.

Definition vs62 {Γ B A} : Var62 Γ A → Var62 (snoc62 Γ B) A
 := λ x Var62 vz62 vs62 , vs62 _ _ _ (x Var62 vz62 vs62).

Definition Tm62 : Con62 → Ty62 → Set
 := λ Γ A ,
   ∀ (Tm62  : Con62 → Ty62 → Set)
     (var   : ∀ Γ A     , Var62 Γ A → Tm62 Γ A)
     (lam   : ∀ Γ A B   , Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B))
     (app   : ∀ Γ A B   , Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B)
   , Tm62 Γ A.

Definition var62 {Γ A} : Var62 Γ A → Tm62 Γ A
 := λ x Tm62 var62 lam app,
     var62 _ _ x.

Definition lam62 {Γ A B} : Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B)
 := λ t Tm62 var62 lam62 app,
     lam62 _ _ _ (t Tm62 var62 lam62 app).

Definition app62 {Γ A B} : Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B
 := λ t u Tm62 var62 lam62 app62,
     app62 _ _ _
         (t Tm62 var62 lam62 app62)
         (u Tm62 var62 lam62 app62).

Definition v062 {Γ A} : Tm62 (snoc62 Γ A) A
 := var62 vz62.

Definition v162 {Γ A B} : Tm62 (snoc62 (snoc62 Γ A) B) A
 := var62 (vs62 vz62).

Definition v262 {Γ A B C} : Tm62 (snoc62 (snoc62 (snoc62 Γ A) B) C) A
 := var62 (vs62 (vs62 vz62)).

Definition v362 {Γ A B C D} : Tm62 (snoc62 (snoc62 (snoc62 (snoc62 Γ A) B) C) D) A
 := var62 (vs62 (vs62 (vs62 vz62))).

Definition v462 {Γ A B C D E} : Tm62 (snoc62 (snoc62 (snoc62 (snoc62 (snoc62 Γ A) B) C) D) E) A
 := var62 (vs62 (vs62 (vs62 (vs62 vz62)))).

Definition test62 {Γ A} : Tm62 Γ (arr62 (arr62 A A) (arr62 A A))
 := lam62 (lam62 (app62 v162 (app62 v162 (app62 v162 (app62 v162 (app62 v162 (app62 v162 v062))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty63 : Set
 := ∀ (Ty63 : Set)
      (ι   : Ty63)
      (arr : Ty63 → Ty63 → Ty63)
    , Ty63.

Definition ι63 : Ty63 := λ _ ι63 _, ι63.

Definition arr63 : Ty63 → Ty63 → Ty63
 := λ A B Ty63 ι63 arr63,
     arr63 (A Ty63 ι63 arr63) (B Ty63 ι63 arr63).

Definition Con63 : Set
 := ∀ (Con63  : Set)
      (nil  : Con63)
      (snoc : Con63 → Ty63 → Con63)
    , Con63.

Definition nil63 : Con63
 := λ Con63 nil63 snoc , nil63.

Definition snoc63 : Con63 → Ty63 → Con63
 := λ Γ A Con63 nil63 snoc63 , snoc63 (Γ Con63 nil63 snoc63) A.

Definition Var63 : Con63 → Ty63 → Set
 := λ Γ A ,
   ∀ (Var63 : Con63 → Ty63 → Set)
     (vz  : ∀ Γ A, Var63 (snoc63 Γ A) A)
     (vs  : ∀ Γ B A, Var63 Γ A → Var63 (snoc63 Γ B) A)
   , Var63 Γ A.

Definition vz63 {Γ A} : Var63 (snoc63 Γ A) A
 := λ Var63 vz63 vs , vz63 _ _.

Definition vs63 {Γ B A} : Var63 Γ A → Var63 (snoc63 Γ B) A
 := λ x Var63 vz63 vs63 , vs63 _ _ _ (x Var63 vz63 vs63).

Definition Tm63 : Con63 → Ty63 → Set
 := λ Γ A ,
   ∀ (Tm63  : Con63 → Ty63 → Set)
     (var   : ∀ Γ A     , Var63 Γ A → Tm63 Γ A)
     (lam   : ∀ Γ A B   , Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B))
     (app   : ∀ Γ A B   , Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B)
   , Tm63 Γ A.

Definition var63 {Γ A} : Var63 Γ A → Tm63 Γ A
 := λ x Tm63 var63 lam app,
     var63 _ _ x.

Definition lam63 {Γ A B} : Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B)
 := λ t Tm63 var63 lam63 app,
     lam63 _ _ _ (t Tm63 var63 lam63 app).

Definition app63 {Γ A B} : Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B
 := λ t u Tm63 var63 lam63 app63,
     app63 _ _ _
         (t Tm63 var63 lam63 app63)
         (u Tm63 var63 lam63 app63).

Definition v063 {Γ A} : Tm63 (snoc63 Γ A) A
 := var63 vz63.

Definition v163 {Γ A B} : Tm63 (snoc63 (snoc63 Γ A) B) A
 := var63 (vs63 vz63).

Definition v263 {Γ A B C} : Tm63 (snoc63 (snoc63 (snoc63 Γ A) B) C) A
 := var63 (vs63 (vs63 vz63)).

Definition v363 {Γ A B C D} : Tm63 (snoc63 (snoc63 (snoc63 (snoc63 Γ A) B) C) D) A
 := var63 (vs63 (vs63 (vs63 vz63))).

Definition v463 {Γ A B C D E} : Tm63 (snoc63 (snoc63 (snoc63 (snoc63 (snoc63 Γ A) B) C) D) E) A
 := var63 (vs63 (vs63 (vs63 (vs63 vz63)))).

Definition test63 {Γ A} : Tm63 Γ (arr63 (arr63 A A) (arr63 A A))
 := lam63 (lam63 (app63 v163 (app63 v163 (app63 v163 (app63 v163 (app63 v163 (app63 v163 v063))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty64 : Set
 := ∀ (Ty64 : Set)
      (ι   : Ty64)
      (arr : Ty64 → Ty64 → Ty64)
    , Ty64.

Definition ι64 : Ty64 := λ _ ι64 _, ι64.

Definition arr64 : Ty64 → Ty64 → Ty64
 := λ A B Ty64 ι64 arr64,
     arr64 (A Ty64 ι64 arr64) (B Ty64 ι64 arr64).

Definition Con64 : Set
 := ∀ (Con64  : Set)
      (nil  : Con64)
      (snoc : Con64 → Ty64 → Con64)
    , Con64.

Definition nil64 : Con64
 := λ Con64 nil64 snoc , nil64.

Definition snoc64 : Con64 → Ty64 → Con64
 := λ Γ A Con64 nil64 snoc64 , snoc64 (Γ Con64 nil64 snoc64) A.

Definition Var64 : Con64 → Ty64 → Set
 := λ Γ A ,
   ∀ (Var64 : Con64 → Ty64 → Set)
     (vz  : ∀ Γ A, Var64 (snoc64 Γ A) A)
     (vs  : ∀ Γ B A, Var64 Γ A → Var64 (snoc64 Γ B) A)
   , Var64 Γ A.

Definition vz64 {Γ A} : Var64 (snoc64 Γ A) A
 := λ Var64 vz64 vs , vz64 _ _.

Definition vs64 {Γ B A} : Var64 Γ A → Var64 (snoc64 Γ B) A
 := λ x Var64 vz64 vs64 , vs64 _ _ _ (x Var64 vz64 vs64).

Definition Tm64 : Con64 → Ty64 → Set
 := λ Γ A ,
   ∀ (Tm64  : Con64 → Ty64 → Set)
     (var   : ∀ Γ A     , Var64 Γ A → Tm64 Γ A)
     (lam   : ∀ Γ A B   , Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B))
     (app   : ∀ Γ A B   , Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B)
   , Tm64 Γ A.

Definition var64 {Γ A} : Var64 Γ A → Tm64 Γ A
 := λ x Tm64 var64 lam app,
     var64 _ _ x.

Definition lam64 {Γ A B} : Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B)
 := λ t Tm64 var64 lam64 app,
     lam64 _ _ _ (t Tm64 var64 lam64 app).

Definition app64 {Γ A B} : Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B
 := λ t u Tm64 var64 lam64 app64,
     app64 _ _ _
         (t Tm64 var64 lam64 app64)
         (u Tm64 var64 lam64 app64).

Definition v064 {Γ A} : Tm64 (snoc64 Γ A) A
 := var64 vz64.

Definition v164 {Γ A B} : Tm64 (snoc64 (snoc64 Γ A) B) A
 := var64 (vs64 vz64).

Definition v264 {Γ A B C} : Tm64 (snoc64 (snoc64 (snoc64 Γ A) B) C) A
 := var64 (vs64 (vs64 vz64)).

Definition v364 {Γ A B C D} : Tm64 (snoc64 (snoc64 (snoc64 (snoc64 Γ A) B) C) D) A
 := var64 (vs64 (vs64 (vs64 vz64))).

Definition v464 {Γ A B C D E} : Tm64 (snoc64 (snoc64 (snoc64 (snoc64 (snoc64 Γ A) B) C) D) E) A
 := var64 (vs64 (vs64 (vs64 (vs64 vz64)))).

Definition test64 {Γ A} : Tm64 Γ (arr64 (arr64 A A) (arr64 A A))
 := lam64 (lam64 (app64 v164 (app64 v164 (app64 v164 (app64 v164 (app64 v164 (app64 v164 v064))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty65 : Set
 := ∀ (Ty65 : Set)
      (ι   : Ty65)
      (arr : Ty65 → Ty65 → Ty65)
    , Ty65.

Definition ι65 : Ty65 := λ _ ι65 _, ι65.

Definition arr65 : Ty65 → Ty65 → Ty65
 := λ A B Ty65 ι65 arr65,
     arr65 (A Ty65 ι65 arr65) (B Ty65 ι65 arr65).

Definition Con65 : Set
 := ∀ (Con65  : Set)
      (nil  : Con65)
      (snoc : Con65 → Ty65 → Con65)
    , Con65.

Definition nil65 : Con65
 := λ Con65 nil65 snoc , nil65.

Definition snoc65 : Con65 → Ty65 → Con65
 := λ Γ A Con65 nil65 snoc65 , snoc65 (Γ Con65 nil65 snoc65) A.

Definition Var65 : Con65 → Ty65 → Set
 := λ Γ A ,
   ∀ (Var65 : Con65 → Ty65 → Set)
     (vz  : ∀ Γ A, Var65 (snoc65 Γ A) A)
     (vs  : ∀ Γ B A, Var65 Γ A → Var65 (snoc65 Γ B) A)
   , Var65 Γ A.

Definition vz65 {Γ A} : Var65 (snoc65 Γ A) A
 := λ Var65 vz65 vs , vz65 _ _.

Definition vs65 {Γ B A} : Var65 Γ A → Var65 (snoc65 Γ B) A
 := λ x Var65 vz65 vs65 , vs65 _ _ _ (x Var65 vz65 vs65).

Definition Tm65 : Con65 → Ty65 → Set
 := λ Γ A ,
   ∀ (Tm65  : Con65 → Ty65 → Set)
     (var   : ∀ Γ A     , Var65 Γ A → Tm65 Γ A)
     (lam   : ∀ Γ A B   , Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B))
     (app   : ∀ Γ A B   , Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B)
   , Tm65 Γ A.

Definition var65 {Γ A} : Var65 Γ A → Tm65 Γ A
 := λ x Tm65 var65 lam app,
     var65 _ _ x.

Definition lam65 {Γ A B} : Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B)
 := λ t Tm65 var65 lam65 app,
     lam65 _ _ _ (t Tm65 var65 lam65 app).

Definition app65 {Γ A B} : Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B
 := λ t u Tm65 var65 lam65 app65,
     app65 _ _ _
         (t Tm65 var65 lam65 app65)
         (u Tm65 var65 lam65 app65).

Definition v065 {Γ A} : Tm65 (snoc65 Γ A) A
 := var65 vz65.

Definition v165 {Γ A B} : Tm65 (snoc65 (snoc65 Γ A) B) A
 := var65 (vs65 vz65).

Definition v265 {Γ A B C} : Tm65 (snoc65 (snoc65 (snoc65 Γ A) B) C) A
 := var65 (vs65 (vs65 vz65)).

Definition v365 {Γ A B C D} : Tm65 (snoc65 (snoc65 (snoc65 (snoc65 Γ A) B) C) D) A
 := var65 (vs65 (vs65 (vs65 vz65))).

Definition v465 {Γ A B C D E} : Tm65 (snoc65 (snoc65 (snoc65 (snoc65 (snoc65 Γ A) B) C) D) E) A
 := var65 (vs65 (vs65 (vs65 (vs65 vz65)))).

Definition test65 {Γ A} : Tm65 Γ (arr65 (arr65 A A) (arr65 A A))
 := lam65 (lam65 (app65 v165 (app65 v165 (app65 v165 (app65 v165 (app65 v165 (app65 v165 v065))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty66 : Set
 := ∀ (Ty66 : Set)
      (ι   : Ty66)
      (arr : Ty66 → Ty66 → Ty66)
    , Ty66.

Definition ι66 : Ty66 := λ _ ι66 _, ι66.

Definition arr66 : Ty66 → Ty66 → Ty66
 := λ A B Ty66 ι66 arr66,
     arr66 (A Ty66 ι66 arr66) (B Ty66 ι66 arr66).

Definition Con66 : Set
 := ∀ (Con66  : Set)
      (nil  : Con66)
      (snoc : Con66 → Ty66 → Con66)
    , Con66.

Definition nil66 : Con66
 := λ Con66 nil66 snoc , nil66.

Definition snoc66 : Con66 → Ty66 → Con66
 := λ Γ A Con66 nil66 snoc66 , snoc66 (Γ Con66 nil66 snoc66) A.

Definition Var66 : Con66 → Ty66 → Set
 := λ Γ A ,
   ∀ (Var66 : Con66 → Ty66 → Set)
     (vz  : ∀ Γ A, Var66 (snoc66 Γ A) A)
     (vs  : ∀ Γ B A, Var66 Γ A → Var66 (snoc66 Γ B) A)
   , Var66 Γ A.

Definition vz66 {Γ A} : Var66 (snoc66 Γ A) A
 := λ Var66 vz66 vs , vz66 _ _.

Definition vs66 {Γ B A} : Var66 Γ A → Var66 (snoc66 Γ B) A
 := λ x Var66 vz66 vs66 , vs66 _ _ _ (x Var66 vz66 vs66).

Definition Tm66 : Con66 → Ty66 → Set
 := λ Γ A ,
   ∀ (Tm66  : Con66 → Ty66 → Set)
     (var   : ∀ Γ A     , Var66 Γ A → Tm66 Γ A)
     (lam   : ∀ Γ A B   , Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B))
     (app   : ∀ Γ A B   , Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B)
   , Tm66 Γ A.

Definition var66 {Γ A} : Var66 Γ A → Tm66 Γ A
 := λ x Tm66 var66 lam app,
     var66 _ _ x.

Definition lam66 {Γ A B} : Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B)
 := λ t Tm66 var66 lam66 app,
     lam66 _ _ _ (t Tm66 var66 lam66 app).

Definition app66 {Γ A B} : Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B
 := λ t u Tm66 var66 lam66 app66,
     app66 _ _ _
         (t Tm66 var66 lam66 app66)
         (u Tm66 var66 lam66 app66).

Definition v066 {Γ A} : Tm66 (snoc66 Γ A) A
 := var66 vz66.

Definition v166 {Γ A B} : Tm66 (snoc66 (snoc66 Γ A) B) A
 := var66 (vs66 vz66).

Definition v266 {Γ A B C} : Tm66 (snoc66 (snoc66 (snoc66 Γ A) B) C) A
 := var66 (vs66 (vs66 vz66)).

Definition v366 {Γ A B C D} : Tm66 (snoc66 (snoc66 (snoc66 (snoc66 Γ A) B) C) D) A
 := var66 (vs66 (vs66 (vs66 vz66))).

Definition v466 {Γ A B C D E} : Tm66 (snoc66 (snoc66 (snoc66 (snoc66 (snoc66 Γ A) B) C) D) E) A
 := var66 (vs66 (vs66 (vs66 (vs66 vz66)))).

Definition test66 {Γ A} : Tm66 Γ (arr66 (arr66 A A) (arr66 A A))
 := lam66 (lam66 (app66 v166 (app66 v166 (app66 v166 (app66 v166 (app66 v166 (app66 v166 v066))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty67 : Set
 := ∀ (Ty67 : Set)
      (ι   : Ty67)
      (arr : Ty67 → Ty67 → Ty67)
    , Ty67.

Definition ι67 : Ty67 := λ _ ι67 _, ι67.

Definition arr67 : Ty67 → Ty67 → Ty67
 := λ A B Ty67 ι67 arr67,
     arr67 (A Ty67 ι67 arr67) (B Ty67 ι67 arr67).

Definition Con67 : Set
 := ∀ (Con67  : Set)
      (nil  : Con67)
      (snoc : Con67 → Ty67 → Con67)
    , Con67.

Definition nil67 : Con67
 := λ Con67 nil67 snoc , nil67.

Definition snoc67 : Con67 → Ty67 → Con67
 := λ Γ A Con67 nil67 snoc67 , snoc67 (Γ Con67 nil67 snoc67) A.

Definition Var67 : Con67 → Ty67 → Set
 := λ Γ A ,
   ∀ (Var67 : Con67 → Ty67 → Set)
     (vz  : ∀ Γ A, Var67 (snoc67 Γ A) A)
     (vs  : ∀ Γ B A, Var67 Γ A → Var67 (snoc67 Γ B) A)
   , Var67 Γ A.

Definition vz67 {Γ A} : Var67 (snoc67 Γ A) A
 := λ Var67 vz67 vs , vz67 _ _.

Definition vs67 {Γ B A} : Var67 Γ A → Var67 (snoc67 Γ B) A
 := λ x Var67 vz67 vs67 , vs67 _ _ _ (x Var67 vz67 vs67).

Definition Tm67 : Con67 → Ty67 → Set
 := λ Γ A ,
   ∀ (Tm67  : Con67 → Ty67 → Set)
     (var   : ∀ Γ A     , Var67 Γ A → Tm67 Γ A)
     (lam   : ∀ Γ A B   , Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B))
     (app   : ∀ Γ A B   , Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B)
   , Tm67 Γ A.

Definition var67 {Γ A} : Var67 Γ A → Tm67 Γ A
 := λ x Tm67 var67 lam app,
     var67 _ _ x.

Definition lam67 {Γ A B} : Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B)
 := λ t Tm67 var67 lam67 app,
     lam67 _ _ _ (t Tm67 var67 lam67 app).

Definition app67 {Γ A B} : Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B
 := λ t u Tm67 var67 lam67 app67,
     app67 _ _ _
         (t Tm67 var67 lam67 app67)
         (u Tm67 var67 lam67 app67).

Definition v067 {Γ A} : Tm67 (snoc67 Γ A) A
 := var67 vz67.

Definition v167 {Γ A B} : Tm67 (snoc67 (snoc67 Γ A) B) A
 := var67 (vs67 vz67).

Definition v267 {Γ A B C} : Tm67 (snoc67 (snoc67 (snoc67 Γ A) B) C) A
 := var67 (vs67 (vs67 vz67)).

Definition v367 {Γ A B C D} : Tm67 (snoc67 (snoc67 (snoc67 (snoc67 Γ A) B) C) D) A
 := var67 (vs67 (vs67 (vs67 vz67))).

Definition v467 {Γ A B C D E} : Tm67 (snoc67 (snoc67 (snoc67 (snoc67 (snoc67 Γ A) B) C) D) E) A
 := var67 (vs67 (vs67 (vs67 (vs67 vz67)))).

Definition test67 {Γ A} : Tm67 Γ (arr67 (arr67 A A) (arr67 A A))
 := lam67 (lam67 (app67 v167 (app67 v167 (app67 v167 (app67 v167 (app67 v167 (app67 v167 v067))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty68 : Set
 := ∀ (Ty68 : Set)
      (ι   : Ty68)
      (arr : Ty68 → Ty68 → Ty68)
    , Ty68.

Definition ι68 : Ty68 := λ _ ι68 _, ι68.

Definition arr68 : Ty68 → Ty68 → Ty68
 := λ A B Ty68 ι68 arr68,
     arr68 (A Ty68 ι68 arr68) (B Ty68 ι68 arr68).

Definition Con68 : Set
 := ∀ (Con68  : Set)
      (nil  : Con68)
      (snoc : Con68 → Ty68 → Con68)
    , Con68.

Definition nil68 : Con68
 := λ Con68 nil68 snoc , nil68.

Definition snoc68 : Con68 → Ty68 → Con68
 := λ Γ A Con68 nil68 snoc68 , snoc68 (Γ Con68 nil68 snoc68) A.

Definition Var68 : Con68 → Ty68 → Set
 := λ Γ A ,
   ∀ (Var68 : Con68 → Ty68 → Set)
     (vz  : ∀ Γ A, Var68 (snoc68 Γ A) A)
     (vs  : ∀ Γ B A, Var68 Γ A → Var68 (snoc68 Γ B) A)
   , Var68 Γ A.

Definition vz68 {Γ A} : Var68 (snoc68 Γ A) A
 := λ Var68 vz68 vs , vz68 _ _.

Definition vs68 {Γ B A} : Var68 Γ A → Var68 (snoc68 Γ B) A
 := λ x Var68 vz68 vs68 , vs68 _ _ _ (x Var68 vz68 vs68).

Definition Tm68 : Con68 → Ty68 → Set
 := λ Γ A ,
   ∀ (Tm68  : Con68 → Ty68 → Set)
     (var   : ∀ Γ A     , Var68 Γ A → Tm68 Γ A)
     (lam   : ∀ Γ A B   , Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B))
     (app   : ∀ Γ A B   , Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B)
   , Tm68 Γ A.

Definition var68 {Γ A} : Var68 Γ A → Tm68 Γ A
 := λ x Tm68 var68 lam app,
     var68 _ _ x.

Definition lam68 {Γ A B} : Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B)
 := λ t Tm68 var68 lam68 app,
     lam68 _ _ _ (t Tm68 var68 lam68 app).

Definition app68 {Γ A B} : Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B
 := λ t u Tm68 var68 lam68 app68,
     app68 _ _ _
         (t Tm68 var68 lam68 app68)
         (u Tm68 var68 lam68 app68).

Definition v068 {Γ A} : Tm68 (snoc68 Γ A) A
 := var68 vz68.

Definition v168 {Γ A B} : Tm68 (snoc68 (snoc68 Γ A) B) A
 := var68 (vs68 vz68).

Definition v268 {Γ A B C} : Tm68 (snoc68 (snoc68 (snoc68 Γ A) B) C) A
 := var68 (vs68 (vs68 vz68)).

Definition v368 {Γ A B C D} : Tm68 (snoc68 (snoc68 (snoc68 (snoc68 Γ A) B) C) D) A
 := var68 (vs68 (vs68 (vs68 vz68))).

Definition v468 {Γ A B C D E} : Tm68 (snoc68 (snoc68 (snoc68 (snoc68 (snoc68 Γ A) B) C) D) E) A
 := var68 (vs68 (vs68 (vs68 (vs68 vz68)))).

Definition test68 {Γ A} : Tm68 Γ (arr68 (arr68 A A) (arr68 A A))
 := lam68 (lam68 (app68 v168 (app68 v168 (app68 v168 (app68 v168 (app68 v168 (app68 v168 v068))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty69 : Set
 := ∀ (Ty69 : Set)
      (ι   : Ty69)
      (arr : Ty69 → Ty69 → Ty69)
    , Ty69.

Definition ι69 : Ty69 := λ _ ι69 _, ι69.

Definition arr69 : Ty69 → Ty69 → Ty69
 := λ A B Ty69 ι69 arr69,
     arr69 (A Ty69 ι69 arr69) (B Ty69 ι69 arr69).

Definition Con69 : Set
 := ∀ (Con69  : Set)
      (nil  : Con69)
      (snoc : Con69 → Ty69 → Con69)
    , Con69.

Definition nil69 : Con69
 := λ Con69 nil69 snoc , nil69.

Definition snoc69 : Con69 → Ty69 → Con69
 := λ Γ A Con69 nil69 snoc69 , snoc69 (Γ Con69 nil69 snoc69) A.

Definition Var69 : Con69 → Ty69 → Set
 := λ Γ A ,
   ∀ (Var69 : Con69 → Ty69 → Set)
     (vz  : ∀ Γ A, Var69 (snoc69 Γ A) A)
     (vs  : ∀ Γ B A, Var69 Γ A → Var69 (snoc69 Γ B) A)
   , Var69 Γ A.

Definition vz69 {Γ A} : Var69 (snoc69 Γ A) A
 := λ Var69 vz69 vs , vz69 _ _.

Definition vs69 {Γ B A} : Var69 Γ A → Var69 (snoc69 Γ B) A
 := λ x Var69 vz69 vs69 , vs69 _ _ _ (x Var69 vz69 vs69).

Definition Tm69 : Con69 → Ty69 → Set
 := λ Γ A ,
   ∀ (Tm69  : Con69 → Ty69 → Set)
     (var   : ∀ Γ A     , Var69 Γ A → Tm69 Γ A)
     (lam   : ∀ Γ A B   , Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B))
     (app   : ∀ Γ A B   , Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B)
   , Tm69 Γ A.

Definition var69 {Γ A} : Var69 Γ A → Tm69 Γ A
 := λ x Tm69 var69 lam app,
     var69 _ _ x.

Definition lam69 {Γ A B} : Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B)
 := λ t Tm69 var69 lam69 app,
     lam69 _ _ _ (t Tm69 var69 lam69 app).

Definition app69 {Γ A B} : Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B
 := λ t u Tm69 var69 lam69 app69,
     app69 _ _ _
         (t Tm69 var69 lam69 app69)
         (u Tm69 var69 lam69 app69).

Definition v069 {Γ A} : Tm69 (snoc69 Γ A) A
 := var69 vz69.

Definition v169 {Γ A B} : Tm69 (snoc69 (snoc69 Γ A) B) A
 := var69 (vs69 vz69).

Definition v269 {Γ A B C} : Tm69 (snoc69 (snoc69 (snoc69 Γ A) B) C) A
 := var69 (vs69 (vs69 vz69)).

Definition v369 {Γ A B C D} : Tm69 (snoc69 (snoc69 (snoc69 (snoc69 Γ A) B) C) D) A
 := var69 (vs69 (vs69 (vs69 vz69))).

Definition v469 {Γ A B C D E} : Tm69 (snoc69 (snoc69 (snoc69 (snoc69 (snoc69 Γ A) B) C) D) E) A
 := var69 (vs69 (vs69 (vs69 (vs69 vz69)))).

Definition test69 {Γ A} : Tm69 Γ (arr69 (arr69 A A) (arr69 A A))
 := lam69 (lam69 (app69 v169 (app69 v169 (app69 v169 (app69 v169 (app69 v169 (app69 v169 v069))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty70 : Set
 := ∀ (Ty70 : Set)
      (ι   : Ty70)
      (arr : Ty70 → Ty70 → Ty70)
    , Ty70.

Definition ι70 : Ty70 := λ _ ι70 _, ι70.

Definition arr70 : Ty70 → Ty70 → Ty70
 := λ A B Ty70 ι70 arr70,
     arr70 (A Ty70 ι70 arr70) (B Ty70 ι70 arr70).

Definition Con70 : Set
 := ∀ (Con70  : Set)
      (nil  : Con70)
      (snoc : Con70 → Ty70 → Con70)
    , Con70.

Definition nil70 : Con70
 := λ Con70 nil70 snoc , nil70.

Definition snoc70 : Con70 → Ty70 → Con70
 := λ Γ A Con70 nil70 snoc70 , snoc70 (Γ Con70 nil70 snoc70) A.

Definition Var70 : Con70 → Ty70 → Set
 := λ Γ A ,
   ∀ (Var70 : Con70 → Ty70 → Set)
     (vz  : ∀ Γ A, Var70 (snoc70 Γ A) A)
     (vs  : ∀ Γ B A, Var70 Γ A → Var70 (snoc70 Γ B) A)
   , Var70 Γ A.

Definition vz70 {Γ A} : Var70 (snoc70 Γ A) A
 := λ Var70 vz70 vs , vz70 _ _.

Definition vs70 {Γ B A} : Var70 Γ A → Var70 (snoc70 Γ B) A
 := λ x Var70 vz70 vs70 , vs70 _ _ _ (x Var70 vz70 vs70).

Definition Tm70 : Con70 → Ty70 → Set
 := λ Γ A ,
   ∀ (Tm70  : Con70 → Ty70 → Set)
     (var   : ∀ Γ A     , Var70 Γ A → Tm70 Γ A)
     (lam   : ∀ Γ A B   , Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B))
     (app   : ∀ Γ A B   , Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B)
   , Tm70 Γ A.

Definition var70 {Γ A} : Var70 Γ A → Tm70 Γ A
 := λ x Tm70 var70 lam app,
     var70 _ _ x.

Definition lam70 {Γ A B} : Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B)
 := λ t Tm70 var70 lam70 app,
     lam70 _ _ _ (t Tm70 var70 lam70 app).

Definition app70 {Γ A B} : Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B
 := λ t u Tm70 var70 lam70 app70,
     app70 _ _ _
         (t Tm70 var70 lam70 app70)
         (u Tm70 var70 lam70 app70).

Definition v070 {Γ A} : Tm70 (snoc70 Γ A) A
 := var70 vz70.

Definition v170 {Γ A B} : Tm70 (snoc70 (snoc70 Γ A) B) A
 := var70 (vs70 vz70).

Definition v270 {Γ A B C} : Tm70 (snoc70 (snoc70 (snoc70 Γ A) B) C) A
 := var70 (vs70 (vs70 vz70)).

Definition v370 {Γ A B C D} : Tm70 (snoc70 (snoc70 (snoc70 (snoc70 Γ A) B) C) D) A
 := var70 (vs70 (vs70 (vs70 vz70))).

Definition v470 {Γ A B C D E} : Tm70 (snoc70 (snoc70 (snoc70 (snoc70 (snoc70 Γ A) B) C) D) E) A
 := var70 (vs70 (vs70 (vs70 (vs70 vz70)))).

Definition test70 {Γ A} : Tm70 Γ (arr70 (arr70 A A) (arr70 A A))
 := lam70 (lam70 (app70 v170 (app70 v170 (app70 v170 (app70 v170 (app70 v170 (app70 v170 v070))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty71 : Set
 := ∀ (Ty71 : Set)
      (ι   : Ty71)
      (arr : Ty71 → Ty71 → Ty71)
    , Ty71.

Definition ι71 : Ty71 := λ _ ι71 _, ι71.

Definition arr71 : Ty71 → Ty71 → Ty71
 := λ A B Ty71 ι71 arr71,
     arr71 (A Ty71 ι71 arr71) (B Ty71 ι71 arr71).

Definition Con71 : Set
 := ∀ (Con71  : Set)
      (nil  : Con71)
      (snoc : Con71 → Ty71 → Con71)
    , Con71.

Definition nil71 : Con71
 := λ Con71 nil71 snoc , nil71.

Definition snoc71 : Con71 → Ty71 → Con71
 := λ Γ A Con71 nil71 snoc71 , snoc71 (Γ Con71 nil71 snoc71) A.

Definition Var71 : Con71 → Ty71 → Set
 := λ Γ A ,
   ∀ (Var71 : Con71 → Ty71 → Set)
     (vz  : ∀ Γ A, Var71 (snoc71 Γ A) A)
     (vs  : ∀ Γ B A, Var71 Γ A → Var71 (snoc71 Γ B) A)
   , Var71 Γ A.

Definition vz71 {Γ A} : Var71 (snoc71 Γ A) A
 := λ Var71 vz71 vs , vz71 _ _.

Definition vs71 {Γ B A} : Var71 Γ A → Var71 (snoc71 Γ B) A
 := λ x Var71 vz71 vs71 , vs71 _ _ _ (x Var71 vz71 vs71).

Definition Tm71 : Con71 → Ty71 → Set
 := λ Γ A ,
   ∀ (Tm71  : Con71 → Ty71 → Set)
     (var   : ∀ Γ A     , Var71 Γ A → Tm71 Γ A)
     (lam   : ∀ Γ A B   , Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B))
     (app   : ∀ Γ A B   , Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B)
   , Tm71 Γ A.

Definition var71 {Γ A} : Var71 Γ A → Tm71 Γ A
 := λ x Tm71 var71 lam app,
     var71 _ _ x.

Definition lam71 {Γ A B} : Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B)
 := λ t Tm71 var71 lam71 app,
     lam71 _ _ _ (t Tm71 var71 lam71 app).

Definition app71 {Γ A B} : Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B
 := λ t u Tm71 var71 lam71 app71,
     app71 _ _ _
         (t Tm71 var71 lam71 app71)
         (u Tm71 var71 lam71 app71).

Definition v071 {Γ A} : Tm71 (snoc71 Γ A) A
 := var71 vz71.

Definition v171 {Γ A B} : Tm71 (snoc71 (snoc71 Γ A) B) A
 := var71 (vs71 vz71).

Definition v271 {Γ A B C} : Tm71 (snoc71 (snoc71 (snoc71 Γ A) B) C) A
 := var71 (vs71 (vs71 vz71)).

Definition v371 {Γ A B C D} : Tm71 (snoc71 (snoc71 (snoc71 (snoc71 Γ A) B) C) D) A
 := var71 (vs71 (vs71 (vs71 vz71))).

Definition v471 {Γ A B C D E} : Tm71 (snoc71 (snoc71 (snoc71 (snoc71 (snoc71 Γ A) B) C) D) E) A
 := var71 (vs71 (vs71 (vs71 (vs71 vz71)))).

Definition test71 {Γ A} : Tm71 Γ (arr71 (arr71 A A) (arr71 A A))
 := lam71 (lam71 (app71 v171 (app71 v171 (app71 v171 (app71 v171 (app71 v171 (app71 v171 v071))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty72 : Set
 := ∀ (Ty72 : Set)
      (ι   : Ty72)
      (arr : Ty72 → Ty72 → Ty72)
    , Ty72.

Definition ι72 : Ty72 := λ _ ι72 _, ι72.

Definition arr72 : Ty72 → Ty72 → Ty72
 := λ A B Ty72 ι72 arr72,
     arr72 (A Ty72 ι72 arr72) (B Ty72 ι72 arr72).

Definition Con72 : Set
 := ∀ (Con72  : Set)
      (nil  : Con72)
      (snoc : Con72 → Ty72 → Con72)
    , Con72.

Definition nil72 : Con72
 := λ Con72 nil72 snoc , nil72.

Definition snoc72 : Con72 → Ty72 → Con72
 := λ Γ A Con72 nil72 snoc72 , snoc72 (Γ Con72 nil72 snoc72) A.

Definition Var72 : Con72 → Ty72 → Set
 := λ Γ A ,
   ∀ (Var72 : Con72 → Ty72 → Set)
     (vz  : ∀ Γ A, Var72 (snoc72 Γ A) A)
     (vs  : ∀ Γ B A, Var72 Γ A → Var72 (snoc72 Γ B) A)
   , Var72 Γ A.

Definition vz72 {Γ A} : Var72 (snoc72 Γ A) A
 := λ Var72 vz72 vs , vz72 _ _.

Definition vs72 {Γ B A} : Var72 Γ A → Var72 (snoc72 Γ B) A
 := λ x Var72 vz72 vs72 , vs72 _ _ _ (x Var72 vz72 vs72).

Definition Tm72 : Con72 → Ty72 → Set
 := λ Γ A ,
   ∀ (Tm72  : Con72 → Ty72 → Set)
     (var   : ∀ Γ A     , Var72 Γ A → Tm72 Γ A)
     (lam   : ∀ Γ A B   , Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B))
     (app   : ∀ Γ A B   , Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B)
   , Tm72 Γ A.

Definition var72 {Γ A} : Var72 Γ A → Tm72 Γ A
 := λ x Tm72 var72 lam app,
     var72 _ _ x.

Definition lam72 {Γ A B} : Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B)
 := λ t Tm72 var72 lam72 app,
     lam72 _ _ _ (t Tm72 var72 lam72 app).

Definition app72 {Γ A B} : Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B
 := λ t u Tm72 var72 lam72 app72,
     app72 _ _ _
         (t Tm72 var72 lam72 app72)
         (u Tm72 var72 lam72 app72).

Definition v072 {Γ A} : Tm72 (snoc72 Γ A) A
 := var72 vz72.

Definition v172 {Γ A B} : Tm72 (snoc72 (snoc72 Γ A) B) A
 := var72 (vs72 vz72).

Definition v272 {Γ A B C} : Tm72 (snoc72 (snoc72 (snoc72 Γ A) B) C) A
 := var72 (vs72 (vs72 vz72)).

Definition v372 {Γ A B C D} : Tm72 (snoc72 (snoc72 (snoc72 (snoc72 Γ A) B) C) D) A
 := var72 (vs72 (vs72 (vs72 vz72))).

Definition v472 {Γ A B C D E} : Tm72 (snoc72 (snoc72 (snoc72 (snoc72 (snoc72 Γ A) B) C) D) E) A
 := var72 (vs72 (vs72 (vs72 (vs72 vz72)))).

Definition test72 {Γ A} : Tm72 Γ (arr72 (arr72 A A) (arr72 A A))
 := lam72 (lam72 (app72 v172 (app72 v172 (app72 v172 (app72 v172 (app72 v172 (app72 v172 v072))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty73 : Set
 := ∀ (Ty73 : Set)
      (ι   : Ty73)
      (arr : Ty73 → Ty73 → Ty73)
    , Ty73.

Definition ι73 : Ty73 := λ _ ι73 _, ι73.

Definition arr73 : Ty73 → Ty73 → Ty73
 := λ A B Ty73 ι73 arr73,
     arr73 (A Ty73 ι73 arr73) (B Ty73 ι73 arr73).

Definition Con73 : Set
 := ∀ (Con73  : Set)
      (nil  : Con73)
      (snoc : Con73 → Ty73 → Con73)
    , Con73.

Definition nil73 : Con73
 := λ Con73 nil73 snoc , nil73.

Definition snoc73 : Con73 → Ty73 → Con73
 := λ Γ A Con73 nil73 snoc73 , snoc73 (Γ Con73 nil73 snoc73) A.

Definition Var73 : Con73 → Ty73 → Set
 := λ Γ A ,
   ∀ (Var73 : Con73 → Ty73 → Set)
     (vz  : ∀ Γ A, Var73 (snoc73 Γ A) A)
     (vs  : ∀ Γ B A, Var73 Γ A → Var73 (snoc73 Γ B) A)
   , Var73 Γ A.

Definition vz73 {Γ A} : Var73 (snoc73 Γ A) A
 := λ Var73 vz73 vs , vz73 _ _.

Definition vs73 {Γ B A} : Var73 Γ A → Var73 (snoc73 Γ B) A
 := λ x Var73 vz73 vs73 , vs73 _ _ _ (x Var73 vz73 vs73).

Definition Tm73 : Con73 → Ty73 → Set
 := λ Γ A ,
   ∀ (Tm73  : Con73 → Ty73 → Set)
     (var   : ∀ Γ A     , Var73 Γ A → Tm73 Γ A)
     (lam   : ∀ Γ A B   , Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B))
     (app   : ∀ Γ A B   , Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B)
   , Tm73 Γ A.

Definition var73 {Γ A} : Var73 Γ A → Tm73 Γ A
 := λ x Tm73 var73 lam app,
     var73 _ _ x.

Definition lam73 {Γ A B} : Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B)
 := λ t Tm73 var73 lam73 app,
     lam73 _ _ _ (t Tm73 var73 lam73 app).

Definition app73 {Γ A B} : Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B
 := λ t u Tm73 var73 lam73 app73,
     app73 _ _ _
         (t Tm73 var73 lam73 app73)
         (u Tm73 var73 lam73 app73).

Definition v073 {Γ A} : Tm73 (snoc73 Γ A) A
 := var73 vz73.

Definition v173 {Γ A B} : Tm73 (snoc73 (snoc73 Γ A) B) A
 := var73 (vs73 vz73).

Definition v273 {Γ A B C} : Tm73 (snoc73 (snoc73 (snoc73 Γ A) B) C) A
 := var73 (vs73 (vs73 vz73)).

Definition v373 {Γ A B C D} : Tm73 (snoc73 (snoc73 (snoc73 (snoc73 Γ A) B) C) D) A
 := var73 (vs73 (vs73 (vs73 vz73))).

Definition v473 {Γ A B C D E} : Tm73 (snoc73 (snoc73 (snoc73 (snoc73 (snoc73 Γ A) B) C) D) E) A
 := var73 (vs73 (vs73 (vs73 (vs73 vz73)))).

Definition test73 {Γ A} : Tm73 Γ (arr73 (arr73 A A) (arr73 A A))
 := lam73 (lam73 (app73 v173 (app73 v173 (app73 v173 (app73 v173 (app73 v173 (app73 v173 v073))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty74 : Set
 := ∀ (Ty74 : Set)
      (ι   : Ty74)
      (arr : Ty74 → Ty74 → Ty74)
    , Ty74.

Definition ι74 : Ty74 := λ _ ι74 _, ι74.

Definition arr74 : Ty74 → Ty74 → Ty74
 := λ A B Ty74 ι74 arr74,
     arr74 (A Ty74 ι74 arr74) (B Ty74 ι74 arr74).

Definition Con74 : Set
 := ∀ (Con74  : Set)
      (nil  : Con74)
      (snoc : Con74 → Ty74 → Con74)
    , Con74.

Definition nil74 : Con74
 := λ Con74 nil74 snoc , nil74.

Definition snoc74 : Con74 → Ty74 → Con74
 := λ Γ A Con74 nil74 snoc74 , snoc74 (Γ Con74 nil74 snoc74) A.

Definition Var74 : Con74 → Ty74 → Set
 := λ Γ A ,
   ∀ (Var74 : Con74 → Ty74 → Set)
     (vz  : ∀ Γ A, Var74 (snoc74 Γ A) A)
     (vs  : ∀ Γ B A, Var74 Γ A → Var74 (snoc74 Γ B) A)
   , Var74 Γ A.

Definition vz74 {Γ A} : Var74 (snoc74 Γ A) A
 := λ Var74 vz74 vs , vz74 _ _.

Definition vs74 {Γ B A} : Var74 Γ A → Var74 (snoc74 Γ B) A
 := λ x Var74 vz74 vs74 , vs74 _ _ _ (x Var74 vz74 vs74).

Definition Tm74 : Con74 → Ty74 → Set
 := λ Γ A ,
   ∀ (Tm74  : Con74 → Ty74 → Set)
     (var   : ∀ Γ A     , Var74 Γ A → Tm74 Γ A)
     (lam   : ∀ Γ A B   , Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B))
     (app   : ∀ Γ A B   , Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B)
   , Tm74 Γ A.

Definition var74 {Γ A} : Var74 Γ A → Tm74 Γ A
 := λ x Tm74 var74 lam app,
     var74 _ _ x.

Definition lam74 {Γ A B} : Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B)
 := λ t Tm74 var74 lam74 app,
     lam74 _ _ _ (t Tm74 var74 lam74 app).

Definition app74 {Γ A B} : Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B
 := λ t u Tm74 var74 lam74 app74,
     app74 _ _ _
         (t Tm74 var74 lam74 app74)
         (u Tm74 var74 lam74 app74).

Definition v074 {Γ A} : Tm74 (snoc74 Γ A) A
 := var74 vz74.

Definition v174 {Γ A B} : Tm74 (snoc74 (snoc74 Γ A) B) A
 := var74 (vs74 vz74).

Definition v274 {Γ A B C} : Tm74 (snoc74 (snoc74 (snoc74 Γ A) B) C) A
 := var74 (vs74 (vs74 vz74)).

Definition v374 {Γ A B C D} : Tm74 (snoc74 (snoc74 (snoc74 (snoc74 Γ A) B) C) D) A
 := var74 (vs74 (vs74 (vs74 vz74))).

Definition v474 {Γ A B C D E} : Tm74 (snoc74 (snoc74 (snoc74 (snoc74 (snoc74 Γ A) B) C) D) E) A
 := var74 (vs74 (vs74 (vs74 (vs74 vz74)))).

Definition test74 {Γ A} : Tm74 Γ (arr74 (arr74 A A) (arr74 A A))
 := lam74 (lam74 (app74 v174 (app74 v174 (app74 v174 (app74 v174 (app74 v174 (app74 v174 v074))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty75 : Set
 := ∀ (Ty75 : Set)
      (ι   : Ty75)
      (arr : Ty75 → Ty75 → Ty75)
    , Ty75.

Definition ι75 : Ty75 := λ _ ι75 _, ι75.

Definition arr75 : Ty75 → Ty75 → Ty75
 := λ A B Ty75 ι75 arr75,
     arr75 (A Ty75 ι75 arr75) (B Ty75 ι75 arr75).

Definition Con75 : Set
 := ∀ (Con75  : Set)
      (nil  : Con75)
      (snoc : Con75 → Ty75 → Con75)
    , Con75.

Definition nil75 : Con75
 := λ Con75 nil75 snoc , nil75.

Definition snoc75 : Con75 → Ty75 → Con75
 := λ Γ A Con75 nil75 snoc75 , snoc75 (Γ Con75 nil75 snoc75) A.

Definition Var75 : Con75 → Ty75 → Set
 := λ Γ A ,
   ∀ (Var75 : Con75 → Ty75 → Set)
     (vz  : ∀ Γ A, Var75 (snoc75 Γ A) A)
     (vs  : ∀ Γ B A, Var75 Γ A → Var75 (snoc75 Γ B) A)
   , Var75 Γ A.

Definition vz75 {Γ A} : Var75 (snoc75 Γ A) A
 := λ Var75 vz75 vs , vz75 _ _.

Definition vs75 {Γ B A} : Var75 Γ A → Var75 (snoc75 Γ B) A
 := λ x Var75 vz75 vs75 , vs75 _ _ _ (x Var75 vz75 vs75).

Definition Tm75 : Con75 → Ty75 → Set
 := λ Γ A ,
   ∀ (Tm75  : Con75 → Ty75 → Set)
     (var   : ∀ Γ A     , Var75 Γ A → Tm75 Γ A)
     (lam   : ∀ Γ A B   , Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B))
     (app   : ∀ Γ A B   , Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B)
   , Tm75 Γ A.

Definition var75 {Γ A} : Var75 Γ A → Tm75 Γ A
 := λ x Tm75 var75 lam app,
     var75 _ _ x.

Definition lam75 {Γ A B} : Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B)
 := λ t Tm75 var75 lam75 app,
     lam75 _ _ _ (t Tm75 var75 lam75 app).

Definition app75 {Γ A B} : Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B
 := λ t u Tm75 var75 lam75 app75,
     app75 _ _ _
         (t Tm75 var75 lam75 app75)
         (u Tm75 var75 lam75 app75).

Definition v075 {Γ A} : Tm75 (snoc75 Γ A) A
 := var75 vz75.

Definition v175 {Γ A B} : Tm75 (snoc75 (snoc75 Γ A) B) A
 := var75 (vs75 vz75).

Definition v275 {Γ A B C} : Tm75 (snoc75 (snoc75 (snoc75 Γ A) B) C) A
 := var75 (vs75 (vs75 vz75)).

Definition v375 {Γ A B C D} : Tm75 (snoc75 (snoc75 (snoc75 (snoc75 Γ A) B) C) D) A
 := var75 (vs75 (vs75 (vs75 vz75))).

Definition v475 {Γ A B C D E} : Tm75 (snoc75 (snoc75 (snoc75 (snoc75 (snoc75 Γ A) B) C) D) E) A
 := var75 (vs75 (vs75 (vs75 (vs75 vz75)))).

Definition test75 {Γ A} : Tm75 Γ (arr75 (arr75 A A) (arr75 A A))
 := lam75 (lam75 (app75 v175 (app75 v175 (app75 v175 (app75 v175 (app75 v175 (app75 v175 v075))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty76 : Set
 := ∀ (Ty76 : Set)
      (ι   : Ty76)
      (arr : Ty76 → Ty76 → Ty76)
    , Ty76.

Definition ι76 : Ty76 := λ _ ι76 _, ι76.

Definition arr76 : Ty76 → Ty76 → Ty76
 := λ A B Ty76 ι76 arr76,
     arr76 (A Ty76 ι76 arr76) (B Ty76 ι76 arr76).

Definition Con76 : Set
 := ∀ (Con76  : Set)
      (nil  : Con76)
      (snoc : Con76 → Ty76 → Con76)
    , Con76.

Definition nil76 : Con76
 := λ Con76 nil76 snoc , nil76.

Definition snoc76 : Con76 → Ty76 → Con76
 := λ Γ A Con76 nil76 snoc76 , snoc76 (Γ Con76 nil76 snoc76) A.

Definition Var76 : Con76 → Ty76 → Set
 := λ Γ A ,
   ∀ (Var76 : Con76 → Ty76 → Set)
     (vz  : ∀ Γ A, Var76 (snoc76 Γ A) A)
     (vs  : ∀ Γ B A, Var76 Γ A → Var76 (snoc76 Γ B) A)
   , Var76 Γ A.

Definition vz76 {Γ A} : Var76 (snoc76 Γ A) A
 := λ Var76 vz76 vs , vz76 _ _.

Definition vs76 {Γ B A} : Var76 Γ A → Var76 (snoc76 Γ B) A
 := λ x Var76 vz76 vs76 , vs76 _ _ _ (x Var76 vz76 vs76).

Definition Tm76 : Con76 → Ty76 → Set
 := λ Γ A ,
   ∀ (Tm76  : Con76 → Ty76 → Set)
     (var   : ∀ Γ A     , Var76 Γ A → Tm76 Γ A)
     (lam   : ∀ Γ A B   , Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B))
     (app   : ∀ Γ A B   , Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B)
   , Tm76 Γ A.

Definition var76 {Γ A} : Var76 Γ A → Tm76 Γ A
 := λ x Tm76 var76 lam app,
     var76 _ _ x.

Definition lam76 {Γ A B} : Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B)
 := λ t Tm76 var76 lam76 app,
     lam76 _ _ _ (t Tm76 var76 lam76 app).

Definition app76 {Γ A B} : Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B
 := λ t u Tm76 var76 lam76 app76,
     app76 _ _ _
         (t Tm76 var76 lam76 app76)
         (u Tm76 var76 lam76 app76).

Definition v076 {Γ A} : Tm76 (snoc76 Γ A) A
 := var76 vz76.

Definition v176 {Γ A B} : Tm76 (snoc76 (snoc76 Γ A) B) A
 := var76 (vs76 vz76).

Definition v276 {Γ A B C} : Tm76 (snoc76 (snoc76 (snoc76 Γ A) B) C) A
 := var76 (vs76 (vs76 vz76)).

Definition v376 {Γ A B C D} : Tm76 (snoc76 (snoc76 (snoc76 (snoc76 Γ A) B) C) D) A
 := var76 (vs76 (vs76 (vs76 vz76))).

Definition v476 {Γ A B C D E} : Tm76 (snoc76 (snoc76 (snoc76 (snoc76 (snoc76 Γ A) B) C) D) E) A
 := var76 (vs76 (vs76 (vs76 (vs76 vz76)))).

Definition test76 {Γ A} : Tm76 Γ (arr76 (arr76 A A) (arr76 A A))
 := lam76 (lam76 (app76 v176 (app76 v176 (app76 v176 (app76 v176 (app76 v176 (app76 v176 v076))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty77 : Set
 := ∀ (Ty77 : Set)
      (ι   : Ty77)
      (arr : Ty77 → Ty77 → Ty77)
    , Ty77.

Definition ι77 : Ty77 := λ _ ι77 _, ι77.

Definition arr77 : Ty77 → Ty77 → Ty77
 := λ A B Ty77 ι77 arr77,
     arr77 (A Ty77 ι77 arr77) (B Ty77 ι77 arr77).

Definition Con77 : Set
 := ∀ (Con77  : Set)
      (nil  : Con77)
      (snoc : Con77 → Ty77 → Con77)
    , Con77.

Definition nil77 : Con77
 := λ Con77 nil77 snoc , nil77.

Definition snoc77 : Con77 → Ty77 → Con77
 := λ Γ A Con77 nil77 snoc77 , snoc77 (Γ Con77 nil77 snoc77) A.

Definition Var77 : Con77 → Ty77 → Set
 := λ Γ A ,
   ∀ (Var77 : Con77 → Ty77 → Set)
     (vz  : ∀ Γ A, Var77 (snoc77 Γ A) A)
     (vs  : ∀ Γ B A, Var77 Γ A → Var77 (snoc77 Γ B) A)
   , Var77 Γ A.

Definition vz77 {Γ A} : Var77 (snoc77 Γ A) A
 := λ Var77 vz77 vs , vz77 _ _.

Definition vs77 {Γ B A} : Var77 Γ A → Var77 (snoc77 Γ B) A
 := λ x Var77 vz77 vs77 , vs77 _ _ _ (x Var77 vz77 vs77).

Definition Tm77 : Con77 → Ty77 → Set
 := λ Γ A ,
   ∀ (Tm77  : Con77 → Ty77 → Set)
     (var   : ∀ Γ A     , Var77 Γ A → Tm77 Γ A)
     (lam   : ∀ Γ A B   , Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B))
     (app   : ∀ Γ A B   , Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B)
   , Tm77 Γ A.

Definition var77 {Γ A} : Var77 Γ A → Tm77 Γ A
 := λ x Tm77 var77 lam app,
     var77 _ _ x.

Definition lam77 {Γ A B} : Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B)
 := λ t Tm77 var77 lam77 app,
     lam77 _ _ _ (t Tm77 var77 lam77 app).

Definition app77 {Γ A B} : Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B
 := λ t u Tm77 var77 lam77 app77,
     app77 _ _ _
         (t Tm77 var77 lam77 app77)
         (u Tm77 var77 lam77 app77).

Definition v077 {Γ A} : Tm77 (snoc77 Γ A) A
 := var77 vz77.

Definition v177 {Γ A B} : Tm77 (snoc77 (snoc77 Γ A) B) A
 := var77 (vs77 vz77).

Definition v277 {Γ A B C} : Tm77 (snoc77 (snoc77 (snoc77 Γ A) B) C) A
 := var77 (vs77 (vs77 vz77)).

Definition v377 {Γ A B C D} : Tm77 (snoc77 (snoc77 (snoc77 (snoc77 Γ A) B) C) D) A
 := var77 (vs77 (vs77 (vs77 vz77))).

Definition v477 {Γ A B C D E} : Tm77 (snoc77 (snoc77 (snoc77 (snoc77 (snoc77 Γ A) B) C) D) E) A
 := var77 (vs77 (vs77 (vs77 (vs77 vz77)))).

Definition test77 {Γ A} : Tm77 Γ (arr77 (arr77 A A) (arr77 A A))
 := lam77 (lam77 (app77 v177 (app77 v177 (app77 v177 (app77 v177 (app77 v177 (app77 v177 v077))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty78 : Set
 := ∀ (Ty78 : Set)
      (ι   : Ty78)
      (arr : Ty78 → Ty78 → Ty78)
    , Ty78.

Definition ι78 : Ty78 := λ _ ι78 _, ι78.

Definition arr78 : Ty78 → Ty78 → Ty78
 := λ A B Ty78 ι78 arr78,
     arr78 (A Ty78 ι78 arr78) (B Ty78 ι78 arr78).

Definition Con78 : Set
 := ∀ (Con78  : Set)
      (nil  : Con78)
      (snoc : Con78 → Ty78 → Con78)
    , Con78.

Definition nil78 : Con78
 := λ Con78 nil78 snoc , nil78.

Definition snoc78 : Con78 → Ty78 → Con78
 := λ Γ A Con78 nil78 snoc78 , snoc78 (Γ Con78 nil78 snoc78) A.

Definition Var78 : Con78 → Ty78 → Set
 := λ Γ A ,
   ∀ (Var78 : Con78 → Ty78 → Set)
     (vz  : ∀ Γ A, Var78 (snoc78 Γ A) A)
     (vs  : ∀ Γ B A, Var78 Γ A → Var78 (snoc78 Γ B) A)
   , Var78 Γ A.

Definition vz78 {Γ A} : Var78 (snoc78 Γ A) A
 := λ Var78 vz78 vs , vz78 _ _.

Definition vs78 {Γ B A} : Var78 Γ A → Var78 (snoc78 Γ B) A
 := λ x Var78 vz78 vs78 , vs78 _ _ _ (x Var78 vz78 vs78).

Definition Tm78 : Con78 → Ty78 → Set
 := λ Γ A ,
   ∀ (Tm78  : Con78 → Ty78 → Set)
     (var   : ∀ Γ A     , Var78 Γ A → Tm78 Γ A)
     (lam   : ∀ Γ A B   , Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B))
     (app   : ∀ Γ A B   , Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B)
   , Tm78 Γ A.

Definition var78 {Γ A} : Var78 Γ A → Tm78 Γ A
 := λ x Tm78 var78 lam app,
     var78 _ _ x.

Definition lam78 {Γ A B} : Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B)
 := λ t Tm78 var78 lam78 app,
     lam78 _ _ _ (t Tm78 var78 lam78 app).

Definition app78 {Γ A B} : Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B
 := λ t u Tm78 var78 lam78 app78,
     app78 _ _ _
         (t Tm78 var78 lam78 app78)
         (u Tm78 var78 lam78 app78).

Definition v078 {Γ A} : Tm78 (snoc78 Γ A) A
 := var78 vz78.

Definition v178 {Γ A B} : Tm78 (snoc78 (snoc78 Γ A) B) A
 := var78 (vs78 vz78).

Definition v278 {Γ A B C} : Tm78 (snoc78 (snoc78 (snoc78 Γ A) B) C) A
 := var78 (vs78 (vs78 vz78)).

Definition v378 {Γ A B C D} : Tm78 (snoc78 (snoc78 (snoc78 (snoc78 Γ A) B) C) D) A
 := var78 (vs78 (vs78 (vs78 vz78))).

Definition v478 {Γ A B C D E} : Tm78 (snoc78 (snoc78 (snoc78 (snoc78 (snoc78 Γ A) B) C) D) E) A
 := var78 (vs78 (vs78 (vs78 (vs78 vz78)))).

Definition test78 {Γ A} : Tm78 Γ (arr78 (arr78 A A) (arr78 A A))
 := lam78 (lam78 (app78 v178 (app78 v178 (app78 v178 (app78 v178 (app78 v178 (app78 v178 v078))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty79 : Set
 := ∀ (Ty79 : Set)
      (ι   : Ty79)
      (arr : Ty79 → Ty79 → Ty79)
    , Ty79.

Definition ι79 : Ty79 := λ _ ι79 _, ι79.

Definition arr79 : Ty79 → Ty79 → Ty79
 := λ A B Ty79 ι79 arr79,
     arr79 (A Ty79 ι79 arr79) (B Ty79 ι79 arr79).

Definition Con79 : Set
 := ∀ (Con79  : Set)
      (nil  : Con79)
      (snoc : Con79 → Ty79 → Con79)
    , Con79.

Definition nil79 : Con79
 := λ Con79 nil79 snoc , nil79.

Definition snoc79 : Con79 → Ty79 → Con79
 := λ Γ A Con79 nil79 snoc79 , snoc79 (Γ Con79 nil79 snoc79) A.

Definition Var79 : Con79 → Ty79 → Set
 := λ Γ A ,
   ∀ (Var79 : Con79 → Ty79 → Set)
     (vz  : ∀ Γ A, Var79 (snoc79 Γ A) A)
     (vs  : ∀ Γ B A, Var79 Γ A → Var79 (snoc79 Γ B) A)
   , Var79 Γ A.

Definition vz79 {Γ A} : Var79 (snoc79 Γ A) A
 := λ Var79 vz79 vs , vz79 _ _.

Definition vs79 {Γ B A} : Var79 Γ A → Var79 (snoc79 Γ B) A
 := λ x Var79 vz79 vs79 , vs79 _ _ _ (x Var79 vz79 vs79).

Definition Tm79 : Con79 → Ty79 → Set
 := λ Γ A ,
   ∀ (Tm79  : Con79 → Ty79 → Set)
     (var   : ∀ Γ A     , Var79 Γ A → Tm79 Γ A)
     (lam   : ∀ Γ A B   , Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B))
     (app   : ∀ Γ A B   , Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B)
   , Tm79 Γ A.

Definition var79 {Γ A} : Var79 Γ A → Tm79 Γ A
 := λ x Tm79 var79 lam app,
     var79 _ _ x.

Definition lam79 {Γ A B} : Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B)
 := λ t Tm79 var79 lam79 app,
     lam79 _ _ _ (t Tm79 var79 lam79 app).

Definition app79 {Γ A B} : Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B
 := λ t u Tm79 var79 lam79 app79,
     app79 _ _ _
         (t Tm79 var79 lam79 app79)
         (u Tm79 var79 lam79 app79).

Definition v079 {Γ A} : Tm79 (snoc79 Γ A) A
 := var79 vz79.

Definition v179 {Γ A B} : Tm79 (snoc79 (snoc79 Γ A) B) A
 := var79 (vs79 vz79).

Definition v279 {Γ A B C} : Tm79 (snoc79 (snoc79 (snoc79 Γ A) B) C) A
 := var79 (vs79 (vs79 vz79)).

Definition v379 {Γ A B C D} : Tm79 (snoc79 (snoc79 (snoc79 (snoc79 Γ A) B) C) D) A
 := var79 (vs79 (vs79 (vs79 vz79))).

Definition v479 {Γ A B C D E} : Tm79 (snoc79 (snoc79 (snoc79 (snoc79 (snoc79 Γ A) B) C) D) E) A
 := var79 (vs79 (vs79 (vs79 (vs79 vz79)))).

Definition test79 {Γ A} : Tm79 Γ (arr79 (arr79 A A) (arr79 A A))
 := lam79 (lam79 (app79 v179 (app79 v179 (app79 v179 (app79 v179 (app79 v179 (app79 v179 v079))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty80 : Set
 := ∀ (Ty80 : Set)
      (ι   : Ty80)
      (arr : Ty80 → Ty80 → Ty80)
    , Ty80.

Definition ι80 : Ty80 := λ _ ι80 _, ι80.

Definition arr80 : Ty80 → Ty80 → Ty80
 := λ A B Ty80 ι80 arr80,
     arr80 (A Ty80 ι80 arr80) (B Ty80 ι80 arr80).

Definition Con80 : Set
 := ∀ (Con80  : Set)
      (nil  : Con80)
      (snoc : Con80 → Ty80 → Con80)
    , Con80.

Definition nil80 : Con80
 := λ Con80 nil80 snoc , nil80.

Definition snoc80 : Con80 → Ty80 → Con80
 := λ Γ A Con80 nil80 snoc80 , snoc80 (Γ Con80 nil80 snoc80) A.

Definition Var80 : Con80 → Ty80 → Set
 := λ Γ A ,
   ∀ (Var80 : Con80 → Ty80 → Set)
     (vz  : ∀ Γ A, Var80 (snoc80 Γ A) A)
     (vs  : ∀ Γ B A, Var80 Γ A → Var80 (snoc80 Γ B) A)
   , Var80 Γ A.

Definition vz80 {Γ A} : Var80 (snoc80 Γ A) A
 := λ Var80 vz80 vs , vz80 _ _.

Definition vs80 {Γ B A} : Var80 Γ A → Var80 (snoc80 Γ B) A
 := λ x Var80 vz80 vs80 , vs80 _ _ _ (x Var80 vz80 vs80).

Definition Tm80 : Con80 → Ty80 → Set
 := λ Γ A ,
   ∀ (Tm80  : Con80 → Ty80 → Set)
     (var   : ∀ Γ A     , Var80 Γ A → Tm80 Γ A)
     (lam   : ∀ Γ A B   , Tm80 (snoc80 Γ A) B → Tm80 Γ (arr80 A B))
     (app   : ∀ Γ A B   , Tm80 Γ (arr80 A B) → Tm80 Γ A → Tm80 Γ B)
   , Tm80 Γ A.

Definition var80 {Γ A} : Var80 Γ A → Tm80 Γ A
 := λ x Tm80 var80 lam app,
     var80 _ _ x.

Definition lam80 {Γ A B} : Tm80 (snoc80 Γ A) B → Tm80 Γ (arr80 A B)
 := λ t Tm80 var80 lam80 app,
     lam80 _ _ _ (t Tm80 var80 lam80 app).

Definition app80 {Γ A B} : Tm80 Γ (arr80 A B) → Tm80 Γ A → Tm80 Γ B
 := λ t u Tm80 var80 lam80 app80,
     app80 _ _ _
         (t Tm80 var80 lam80 app80)
         (u Tm80 var80 lam80 app80).

Definition v080 {Γ A} : Tm80 (snoc80 Γ A) A
 := var80 vz80.

Definition v180 {Γ A B} : Tm80 (snoc80 (snoc80 Γ A) B) A
 := var80 (vs80 vz80).

Definition v280 {Γ A B C} : Tm80 (snoc80 (snoc80 (snoc80 Γ A) B) C) A
 := var80 (vs80 (vs80 vz80)).

Definition v380 {Γ A B C D} : Tm80 (snoc80 (snoc80 (snoc80 (snoc80 Γ A) B) C) D) A
 := var80 (vs80 (vs80 (vs80 vz80))).

Definition v480 {Γ A B C D E} : Tm80 (snoc80 (snoc80 (snoc80 (snoc80 (snoc80 Γ A) B) C) D) E) A
 := var80 (vs80 (vs80 (vs80 (vs80 vz80)))).

Definition test80 {Γ A} : Tm80 Γ (arr80 (arr80 A A) (arr80 A A))
 := lam80 (lam80 (app80 v180 (app80 v180 (app80 v180 (app80 v180 (app80 v180 (app80 v180 v080))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty81 : Set
 := ∀ (Ty81 : Set)
      (ι   : Ty81)
      (arr : Ty81 → Ty81 → Ty81)
    , Ty81.

Definition ι81 : Ty81 := λ _ ι81 _, ι81.

Definition arr81 : Ty81 → Ty81 → Ty81
 := λ A B Ty81 ι81 arr81,
     arr81 (A Ty81 ι81 arr81) (B Ty81 ι81 arr81).

Definition Con81 : Set
 := ∀ (Con81  : Set)
      (nil  : Con81)
      (snoc : Con81 → Ty81 → Con81)
    , Con81.

Definition nil81 : Con81
 := λ Con81 nil81 snoc , nil81.

Definition snoc81 : Con81 → Ty81 → Con81
 := λ Γ A Con81 nil81 snoc81 , snoc81 (Γ Con81 nil81 snoc81) A.

Definition Var81 : Con81 → Ty81 → Set
 := λ Γ A ,
   ∀ (Var81 : Con81 → Ty81 → Set)
     (vz  : ∀ Γ A, Var81 (snoc81 Γ A) A)
     (vs  : ∀ Γ B A, Var81 Γ A → Var81 (snoc81 Γ B) A)
   , Var81 Γ A.

Definition vz81 {Γ A} : Var81 (snoc81 Γ A) A
 := λ Var81 vz81 vs , vz81 _ _.

Definition vs81 {Γ B A} : Var81 Γ A → Var81 (snoc81 Γ B) A
 := λ x Var81 vz81 vs81 , vs81 _ _ _ (x Var81 vz81 vs81).

Definition Tm81 : Con81 → Ty81 → Set
 := λ Γ A ,
   ∀ (Tm81  : Con81 → Ty81 → Set)
     (var   : ∀ Γ A     , Var81 Γ A → Tm81 Γ A)
     (lam   : ∀ Γ A B   , Tm81 (snoc81 Γ A) B → Tm81 Γ (arr81 A B))
     (app   : ∀ Γ A B   , Tm81 Γ (arr81 A B) → Tm81 Γ A → Tm81 Γ B)
   , Tm81 Γ A.

Definition var81 {Γ A} : Var81 Γ A → Tm81 Γ A
 := λ x Tm81 var81 lam app,
     var81 _ _ x.

Definition lam81 {Γ A B} : Tm81 (snoc81 Γ A) B → Tm81 Γ (arr81 A B)
 := λ t Tm81 var81 lam81 app,
     lam81 _ _ _ (t Tm81 var81 lam81 app).

Definition app81 {Γ A B} : Tm81 Γ (arr81 A B) → Tm81 Γ A → Tm81 Γ B
 := λ t u Tm81 var81 lam81 app81,
     app81 _ _ _
         (t Tm81 var81 lam81 app81)
         (u Tm81 var81 lam81 app81).

Definition v081 {Γ A} : Tm81 (snoc81 Γ A) A
 := var81 vz81.

Definition v181 {Γ A B} : Tm81 (snoc81 (snoc81 Γ A) B) A
 := var81 (vs81 vz81).

Definition v281 {Γ A B C} : Tm81 (snoc81 (snoc81 (snoc81 Γ A) B) C) A
 := var81 (vs81 (vs81 vz81)).

Definition v381 {Γ A B C D} : Tm81 (snoc81 (snoc81 (snoc81 (snoc81 Γ A) B) C) D) A
 := var81 (vs81 (vs81 (vs81 vz81))).

Definition v481 {Γ A B C D E} : Tm81 (snoc81 (snoc81 (snoc81 (snoc81 (snoc81 Γ A) B) C) D) E) A
 := var81 (vs81 (vs81 (vs81 (vs81 vz81)))).

Definition test81 {Γ A} : Tm81 Γ (arr81 (arr81 A A) (arr81 A A))
 := lam81 (lam81 (app81 v181 (app81 v181 (app81 v181 (app81 v181 (app81 v181 (app81 v181 v081))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty82 : Set
 := ∀ (Ty82 : Set)
      (ι   : Ty82)
      (arr : Ty82 → Ty82 → Ty82)
    , Ty82.

Definition ι82 : Ty82 := λ _ ι82 _, ι82.

Definition arr82 : Ty82 → Ty82 → Ty82
 := λ A B Ty82 ι82 arr82,
     arr82 (A Ty82 ι82 arr82) (B Ty82 ι82 arr82).

Definition Con82 : Set
 := ∀ (Con82  : Set)
      (nil  : Con82)
      (snoc : Con82 → Ty82 → Con82)
    , Con82.

Definition nil82 : Con82
 := λ Con82 nil82 snoc , nil82.

Definition snoc82 : Con82 → Ty82 → Con82
 := λ Γ A Con82 nil82 snoc82 , snoc82 (Γ Con82 nil82 snoc82) A.

Definition Var82 : Con82 → Ty82 → Set
 := λ Γ A ,
   ∀ (Var82 : Con82 → Ty82 → Set)
     (vz  : ∀ Γ A, Var82 (snoc82 Γ A) A)
     (vs  : ∀ Γ B A, Var82 Γ A → Var82 (snoc82 Γ B) A)
   , Var82 Γ A.

Definition vz82 {Γ A} : Var82 (snoc82 Γ A) A
 := λ Var82 vz82 vs , vz82 _ _.

Definition vs82 {Γ B A} : Var82 Γ A → Var82 (snoc82 Γ B) A
 := λ x Var82 vz82 vs82 , vs82 _ _ _ (x Var82 vz82 vs82).

Definition Tm82 : Con82 → Ty82 → Set
 := λ Γ A ,
   ∀ (Tm82  : Con82 → Ty82 → Set)
     (var   : ∀ Γ A     , Var82 Γ A → Tm82 Γ A)
     (lam   : ∀ Γ A B   , Tm82 (snoc82 Γ A) B → Tm82 Γ (arr82 A B))
     (app   : ∀ Γ A B   , Tm82 Γ (arr82 A B) → Tm82 Γ A → Tm82 Γ B)
   , Tm82 Γ A.

Definition var82 {Γ A} : Var82 Γ A → Tm82 Γ A
 := λ x Tm82 var82 lam app,
     var82 _ _ x.

Definition lam82 {Γ A B} : Tm82 (snoc82 Γ A) B → Tm82 Γ (arr82 A B)
 := λ t Tm82 var82 lam82 app,
     lam82 _ _ _ (t Tm82 var82 lam82 app).

Definition app82 {Γ A B} : Tm82 Γ (arr82 A B) → Tm82 Γ A → Tm82 Γ B
 := λ t u Tm82 var82 lam82 app82,
     app82 _ _ _
         (t Tm82 var82 lam82 app82)
         (u Tm82 var82 lam82 app82).

Definition v082 {Γ A} : Tm82 (snoc82 Γ A) A
 := var82 vz82.

Definition v182 {Γ A B} : Tm82 (snoc82 (snoc82 Γ A) B) A
 := var82 (vs82 vz82).

Definition v282 {Γ A B C} : Tm82 (snoc82 (snoc82 (snoc82 Γ A) B) C) A
 := var82 (vs82 (vs82 vz82)).

Definition v382 {Γ A B C D} : Tm82 (snoc82 (snoc82 (snoc82 (snoc82 Γ A) B) C) D) A
 := var82 (vs82 (vs82 (vs82 vz82))).

Definition v482 {Γ A B C D E} : Tm82 (snoc82 (snoc82 (snoc82 (snoc82 (snoc82 Γ A) B) C) D) E) A
 := var82 (vs82 (vs82 (vs82 (vs82 vz82)))).

Definition test82 {Γ A} : Tm82 Γ (arr82 (arr82 A A) (arr82 A A))
 := lam82 (lam82 (app82 v182 (app82 v182 (app82 v182 (app82 v182 (app82 v182 (app82 v182 v082))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty83 : Set
 := ∀ (Ty83 : Set)
      (ι   : Ty83)
      (arr : Ty83 → Ty83 → Ty83)
    , Ty83.

Definition ι83 : Ty83 := λ _ ι83 _, ι83.

Definition arr83 : Ty83 → Ty83 → Ty83
 := λ A B Ty83 ι83 arr83,
     arr83 (A Ty83 ι83 arr83) (B Ty83 ι83 arr83).

Definition Con83 : Set
 := ∀ (Con83  : Set)
      (nil  : Con83)
      (snoc : Con83 → Ty83 → Con83)
    , Con83.

Definition nil83 : Con83
 := λ Con83 nil83 snoc , nil83.

Definition snoc83 : Con83 → Ty83 → Con83
 := λ Γ A Con83 nil83 snoc83 , snoc83 (Γ Con83 nil83 snoc83) A.

Definition Var83 : Con83 → Ty83 → Set
 := λ Γ A ,
   ∀ (Var83 : Con83 → Ty83 → Set)
     (vz  : ∀ Γ A, Var83 (snoc83 Γ A) A)
     (vs  : ∀ Γ B A, Var83 Γ A → Var83 (snoc83 Γ B) A)
   , Var83 Γ A.

Definition vz83 {Γ A} : Var83 (snoc83 Γ A) A
 := λ Var83 vz83 vs , vz83 _ _.

Definition vs83 {Γ B A} : Var83 Γ A → Var83 (snoc83 Γ B) A
 := λ x Var83 vz83 vs83 , vs83 _ _ _ (x Var83 vz83 vs83).

Definition Tm83 : Con83 → Ty83 → Set
 := λ Γ A ,
   ∀ (Tm83  : Con83 → Ty83 → Set)
     (var   : ∀ Γ A     , Var83 Γ A → Tm83 Γ A)
     (lam   : ∀ Γ A B   , Tm83 (snoc83 Γ A) B → Tm83 Γ (arr83 A B))
     (app   : ∀ Γ A B   , Tm83 Γ (arr83 A B) → Tm83 Γ A → Tm83 Γ B)
   , Tm83 Γ A.

Definition var83 {Γ A} : Var83 Γ A → Tm83 Γ A
 := λ x Tm83 var83 lam app,
     var83 _ _ x.

Definition lam83 {Γ A B} : Tm83 (snoc83 Γ A) B → Tm83 Γ (arr83 A B)
 := λ t Tm83 var83 lam83 app,
     lam83 _ _ _ (t Tm83 var83 lam83 app).

Definition app83 {Γ A B} : Tm83 Γ (arr83 A B) → Tm83 Γ A → Tm83 Γ B
 := λ t u Tm83 var83 lam83 app83,
     app83 _ _ _
         (t Tm83 var83 lam83 app83)
         (u Tm83 var83 lam83 app83).

Definition v083 {Γ A} : Tm83 (snoc83 Γ A) A
 := var83 vz83.

Definition v183 {Γ A B} : Tm83 (snoc83 (snoc83 Γ A) B) A
 := var83 (vs83 vz83).

Definition v283 {Γ A B C} : Tm83 (snoc83 (snoc83 (snoc83 Γ A) B) C) A
 := var83 (vs83 (vs83 vz83)).

Definition v383 {Γ A B C D} : Tm83 (snoc83 (snoc83 (snoc83 (snoc83 Γ A) B) C) D) A
 := var83 (vs83 (vs83 (vs83 vz83))).

Definition v483 {Γ A B C D E} : Tm83 (snoc83 (snoc83 (snoc83 (snoc83 (snoc83 Γ A) B) C) D) E) A
 := var83 (vs83 (vs83 (vs83 (vs83 vz83)))).

Definition test83 {Γ A} : Tm83 Γ (arr83 (arr83 A A) (arr83 A A))
 := lam83 (lam83 (app83 v183 (app83 v183 (app83 v183 (app83 v183 (app83 v183 (app83 v183 v083))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty84 : Set
 := ∀ (Ty84 : Set)
      (ι   : Ty84)
      (arr : Ty84 → Ty84 → Ty84)
    , Ty84.

Definition ι84 : Ty84 := λ _ ι84 _, ι84.

Definition arr84 : Ty84 → Ty84 → Ty84
 := λ A B Ty84 ι84 arr84,
     arr84 (A Ty84 ι84 arr84) (B Ty84 ι84 arr84).

Definition Con84 : Set
 := ∀ (Con84  : Set)
      (nil  : Con84)
      (snoc : Con84 → Ty84 → Con84)
    , Con84.

Definition nil84 : Con84
 := λ Con84 nil84 snoc , nil84.

Definition snoc84 : Con84 → Ty84 → Con84
 := λ Γ A Con84 nil84 snoc84 , snoc84 (Γ Con84 nil84 snoc84) A.

Definition Var84 : Con84 → Ty84 → Set
 := λ Γ A ,
   ∀ (Var84 : Con84 → Ty84 → Set)
     (vz  : ∀ Γ A, Var84 (snoc84 Γ A) A)
     (vs  : ∀ Γ B A, Var84 Γ A → Var84 (snoc84 Γ B) A)
   , Var84 Γ A.

Definition vz84 {Γ A} : Var84 (snoc84 Γ A) A
 := λ Var84 vz84 vs , vz84 _ _.

Definition vs84 {Γ B A} : Var84 Γ A → Var84 (snoc84 Γ B) A
 := λ x Var84 vz84 vs84 , vs84 _ _ _ (x Var84 vz84 vs84).

Definition Tm84 : Con84 → Ty84 → Set
 := λ Γ A ,
   ∀ (Tm84  : Con84 → Ty84 → Set)
     (var   : ∀ Γ A     , Var84 Γ A → Tm84 Γ A)
     (lam   : ∀ Γ A B   , Tm84 (snoc84 Γ A) B → Tm84 Γ (arr84 A B))
     (app   : ∀ Γ A B   , Tm84 Γ (arr84 A B) → Tm84 Γ A → Tm84 Γ B)
   , Tm84 Γ A.

Definition var84 {Γ A} : Var84 Γ A → Tm84 Γ A
 := λ x Tm84 var84 lam app,
     var84 _ _ x.

Definition lam84 {Γ A B} : Tm84 (snoc84 Γ A) B → Tm84 Γ (arr84 A B)
 := λ t Tm84 var84 lam84 app,
     lam84 _ _ _ (t Tm84 var84 lam84 app).

Definition app84 {Γ A B} : Tm84 Γ (arr84 A B) → Tm84 Γ A → Tm84 Γ B
 := λ t u Tm84 var84 lam84 app84,
     app84 _ _ _
         (t Tm84 var84 lam84 app84)
         (u Tm84 var84 lam84 app84).

Definition v084 {Γ A} : Tm84 (snoc84 Γ A) A
 := var84 vz84.

Definition v184 {Γ A B} : Tm84 (snoc84 (snoc84 Γ A) B) A
 := var84 (vs84 vz84).

Definition v284 {Γ A B C} : Tm84 (snoc84 (snoc84 (snoc84 Γ A) B) C) A
 := var84 (vs84 (vs84 vz84)).

Definition v384 {Γ A B C D} : Tm84 (snoc84 (snoc84 (snoc84 (snoc84 Γ A) B) C) D) A
 := var84 (vs84 (vs84 (vs84 vz84))).

Definition v484 {Γ A B C D E} : Tm84 (snoc84 (snoc84 (snoc84 (snoc84 (snoc84 Γ A) B) C) D) E) A
 := var84 (vs84 (vs84 (vs84 (vs84 vz84)))).

Definition test84 {Γ A} : Tm84 Γ (arr84 (arr84 A A) (arr84 A A))
 := lam84 (lam84 (app84 v184 (app84 v184 (app84 v184 (app84 v184 (app84 v184 (app84 v184 v084))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty85 : Set
 := ∀ (Ty85 : Set)
      (ι   : Ty85)
      (arr : Ty85 → Ty85 → Ty85)
    , Ty85.

Definition ι85 : Ty85 := λ _ ι85 _, ι85.

Definition arr85 : Ty85 → Ty85 → Ty85
 := λ A B Ty85 ι85 arr85,
     arr85 (A Ty85 ι85 arr85) (B Ty85 ι85 arr85).

Definition Con85 : Set
 := ∀ (Con85  : Set)
      (nil  : Con85)
      (snoc : Con85 → Ty85 → Con85)
    , Con85.

Definition nil85 : Con85
 := λ Con85 nil85 snoc , nil85.

Definition snoc85 : Con85 → Ty85 → Con85
 := λ Γ A Con85 nil85 snoc85 , snoc85 (Γ Con85 nil85 snoc85) A.

Definition Var85 : Con85 → Ty85 → Set
 := λ Γ A ,
   ∀ (Var85 : Con85 → Ty85 → Set)
     (vz  : ∀ Γ A, Var85 (snoc85 Γ A) A)
     (vs  : ∀ Γ B A, Var85 Γ A → Var85 (snoc85 Γ B) A)
   , Var85 Γ A.

Definition vz85 {Γ A} : Var85 (snoc85 Γ A) A
 := λ Var85 vz85 vs , vz85 _ _.

Definition vs85 {Γ B A} : Var85 Γ A → Var85 (snoc85 Γ B) A
 := λ x Var85 vz85 vs85 , vs85 _ _ _ (x Var85 vz85 vs85).

Definition Tm85 : Con85 → Ty85 → Set
 := λ Γ A ,
   ∀ (Tm85  : Con85 → Ty85 → Set)
     (var   : ∀ Γ A     , Var85 Γ A → Tm85 Γ A)
     (lam   : ∀ Γ A B   , Tm85 (snoc85 Γ A) B → Tm85 Γ (arr85 A B))
     (app   : ∀ Γ A B   , Tm85 Γ (arr85 A B) → Tm85 Γ A → Tm85 Γ B)
   , Tm85 Γ A.

Definition var85 {Γ A} : Var85 Γ A → Tm85 Γ A
 := λ x Tm85 var85 lam app,
     var85 _ _ x.

Definition lam85 {Γ A B} : Tm85 (snoc85 Γ A) B → Tm85 Γ (arr85 A B)
 := λ t Tm85 var85 lam85 app,
     lam85 _ _ _ (t Tm85 var85 lam85 app).

Definition app85 {Γ A B} : Tm85 Γ (arr85 A B) → Tm85 Γ A → Tm85 Γ B
 := λ t u Tm85 var85 lam85 app85,
     app85 _ _ _
         (t Tm85 var85 lam85 app85)
         (u Tm85 var85 lam85 app85).

Definition v085 {Γ A} : Tm85 (snoc85 Γ A) A
 := var85 vz85.

Definition v185 {Γ A B} : Tm85 (snoc85 (snoc85 Γ A) B) A
 := var85 (vs85 vz85).

Definition v285 {Γ A B C} : Tm85 (snoc85 (snoc85 (snoc85 Γ A) B) C) A
 := var85 (vs85 (vs85 vz85)).

Definition v385 {Γ A B C D} : Tm85 (snoc85 (snoc85 (snoc85 (snoc85 Γ A) B) C) D) A
 := var85 (vs85 (vs85 (vs85 vz85))).

Definition v485 {Γ A B C D E} : Tm85 (snoc85 (snoc85 (snoc85 (snoc85 (snoc85 Γ A) B) C) D) E) A
 := var85 (vs85 (vs85 (vs85 (vs85 vz85)))).

Definition test85 {Γ A} : Tm85 Γ (arr85 (arr85 A A) (arr85 A A))
 := lam85 (lam85 (app85 v185 (app85 v185 (app85 v185 (app85 v185 (app85 v185 (app85 v185 v085))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty86 : Set
 := ∀ (Ty86 : Set)
      (ι   : Ty86)
      (arr : Ty86 → Ty86 → Ty86)
    , Ty86.

Definition ι86 : Ty86 := λ _ ι86 _, ι86.

Definition arr86 : Ty86 → Ty86 → Ty86
 := λ A B Ty86 ι86 arr86,
     arr86 (A Ty86 ι86 arr86) (B Ty86 ι86 arr86).

Definition Con86 : Set
 := ∀ (Con86  : Set)
      (nil  : Con86)
      (snoc : Con86 → Ty86 → Con86)
    , Con86.

Definition nil86 : Con86
 := λ Con86 nil86 snoc , nil86.

Definition snoc86 : Con86 → Ty86 → Con86
 := λ Γ A Con86 nil86 snoc86 , snoc86 (Γ Con86 nil86 snoc86) A.

Definition Var86 : Con86 → Ty86 → Set
 := λ Γ A ,
   ∀ (Var86 : Con86 → Ty86 → Set)
     (vz  : ∀ Γ A, Var86 (snoc86 Γ A) A)
     (vs  : ∀ Γ B A, Var86 Γ A → Var86 (snoc86 Γ B) A)
   , Var86 Γ A.

Definition vz86 {Γ A} : Var86 (snoc86 Γ A) A
 := λ Var86 vz86 vs , vz86 _ _.

Definition vs86 {Γ B A} : Var86 Γ A → Var86 (snoc86 Γ B) A
 := λ x Var86 vz86 vs86 , vs86 _ _ _ (x Var86 vz86 vs86).

Definition Tm86 : Con86 → Ty86 → Set
 := λ Γ A ,
   ∀ (Tm86  : Con86 → Ty86 → Set)
     (var   : ∀ Γ A     , Var86 Γ A → Tm86 Γ A)
     (lam   : ∀ Γ A B   , Tm86 (snoc86 Γ A) B → Tm86 Γ (arr86 A B))
     (app   : ∀ Γ A B   , Tm86 Γ (arr86 A B) → Tm86 Γ A → Tm86 Γ B)
   , Tm86 Γ A.

Definition var86 {Γ A} : Var86 Γ A → Tm86 Γ A
 := λ x Tm86 var86 lam app,
     var86 _ _ x.

Definition lam86 {Γ A B} : Tm86 (snoc86 Γ A) B → Tm86 Γ (arr86 A B)
 := λ t Tm86 var86 lam86 app,
     lam86 _ _ _ (t Tm86 var86 lam86 app).

Definition app86 {Γ A B} : Tm86 Γ (arr86 A B) → Tm86 Γ A → Tm86 Γ B
 := λ t u Tm86 var86 lam86 app86,
     app86 _ _ _
         (t Tm86 var86 lam86 app86)
         (u Tm86 var86 lam86 app86).

Definition v086 {Γ A} : Tm86 (snoc86 Γ A) A
 := var86 vz86.

Definition v186 {Γ A B} : Tm86 (snoc86 (snoc86 Γ A) B) A
 := var86 (vs86 vz86).

Definition v286 {Γ A B C} : Tm86 (snoc86 (snoc86 (snoc86 Γ A) B) C) A
 := var86 (vs86 (vs86 vz86)).

Definition v386 {Γ A B C D} : Tm86 (snoc86 (snoc86 (snoc86 (snoc86 Γ A) B) C) D) A
 := var86 (vs86 (vs86 (vs86 vz86))).

Definition v486 {Γ A B C D E} : Tm86 (snoc86 (snoc86 (snoc86 (snoc86 (snoc86 Γ A) B) C) D) E) A
 := var86 (vs86 (vs86 (vs86 (vs86 vz86)))).

Definition test86 {Γ A} : Tm86 Γ (arr86 (arr86 A A) (arr86 A A))
 := lam86 (lam86 (app86 v186 (app86 v186 (app86 v186 (app86 v186 (app86 v186 (app86 v186 v086))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty87 : Set
 := ∀ (Ty87 : Set)
      (ι   : Ty87)
      (arr : Ty87 → Ty87 → Ty87)
    , Ty87.

Definition ι87 : Ty87 := λ _ ι87 _, ι87.

Definition arr87 : Ty87 → Ty87 → Ty87
 := λ A B Ty87 ι87 arr87,
     arr87 (A Ty87 ι87 arr87) (B Ty87 ι87 arr87).

Definition Con87 : Set
 := ∀ (Con87  : Set)
      (nil  : Con87)
      (snoc : Con87 → Ty87 → Con87)
    , Con87.

Definition nil87 : Con87
 := λ Con87 nil87 snoc , nil87.

Definition snoc87 : Con87 → Ty87 → Con87
 := λ Γ A Con87 nil87 snoc87 , snoc87 (Γ Con87 nil87 snoc87) A.

Definition Var87 : Con87 → Ty87 → Set
 := λ Γ A ,
   ∀ (Var87 : Con87 → Ty87 → Set)
     (vz  : ∀ Γ A, Var87 (snoc87 Γ A) A)
     (vs  : ∀ Γ B A, Var87 Γ A → Var87 (snoc87 Γ B) A)
   , Var87 Γ A.

Definition vz87 {Γ A} : Var87 (snoc87 Γ A) A
 := λ Var87 vz87 vs , vz87 _ _.

Definition vs87 {Γ B A} : Var87 Γ A → Var87 (snoc87 Γ B) A
 := λ x Var87 vz87 vs87 , vs87 _ _ _ (x Var87 vz87 vs87).

Definition Tm87 : Con87 → Ty87 → Set
 := λ Γ A ,
   ∀ (Tm87  : Con87 → Ty87 → Set)
     (var   : ∀ Γ A     , Var87 Γ A → Tm87 Γ A)
     (lam   : ∀ Γ A B   , Tm87 (snoc87 Γ A) B → Tm87 Γ (arr87 A B))
     (app   : ∀ Γ A B   , Tm87 Γ (arr87 A B) → Tm87 Γ A → Tm87 Γ B)
   , Tm87 Γ A.

Definition var87 {Γ A} : Var87 Γ A → Tm87 Γ A
 := λ x Tm87 var87 lam app,
     var87 _ _ x.

Definition lam87 {Γ A B} : Tm87 (snoc87 Γ A) B → Tm87 Γ (arr87 A B)
 := λ t Tm87 var87 lam87 app,
     lam87 _ _ _ (t Tm87 var87 lam87 app).

Definition app87 {Γ A B} : Tm87 Γ (arr87 A B) → Tm87 Γ A → Tm87 Γ B
 := λ t u Tm87 var87 lam87 app87,
     app87 _ _ _
         (t Tm87 var87 lam87 app87)
         (u Tm87 var87 lam87 app87).

Definition v087 {Γ A} : Tm87 (snoc87 Γ A) A
 := var87 vz87.

Definition v187 {Γ A B} : Tm87 (snoc87 (snoc87 Γ A) B) A
 := var87 (vs87 vz87).

Definition v287 {Γ A B C} : Tm87 (snoc87 (snoc87 (snoc87 Γ A) B) C) A
 := var87 (vs87 (vs87 vz87)).

Definition v387 {Γ A B C D} : Tm87 (snoc87 (snoc87 (snoc87 (snoc87 Γ A) B) C) D) A
 := var87 (vs87 (vs87 (vs87 vz87))).

Definition v487 {Γ A B C D E} : Tm87 (snoc87 (snoc87 (snoc87 (snoc87 (snoc87 Γ A) B) C) D) E) A
 := var87 (vs87 (vs87 (vs87 (vs87 vz87)))).

Definition test87 {Γ A} : Tm87 Γ (arr87 (arr87 A A) (arr87 A A))
 := lam87 (lam87 (app87 v187 (app87 v187 (app87 v187 (app87 v187 (app87 v187 (app87 v187 v087))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty88 : Set
 := ∀ (Ty88 : Set)
      (ι   : Ty88)
      (arr : Ty88 → Ty88 → Ty88)
    , Ty88.

Definition ι88 : Ty88 := λ _ ι88 _, ι88.

Definition arr88 : Ty88 → Ty88 → Ty88
 := λ A B Ty88 ι88 arr88,
     arr88 (A Ty88 ι88 arr88) (B Ty88 ι88 arr88).

Definition Con88 : Set
 := ∀ (Con88  : Set)
      (nil  : Con88)
      (snoc : Con88 → Ty88 → Con88)
    , Con88.

Definition nil88 : Con88
 := λ Con88 nil88 snoc , nil88.

Definition snoc88 : Con88 → Ty88 → Con88
 := λ Γ A Con88 nil88 snoc88 , snoc88 (Γ Con88 nil88 snoc88) A.

Definition Var88 : Con88 → Ty88 → Set
 := λ Γ A ,
   ∀ (Var88 : Con88 → Ty88 → Set)
     (vz  : ∀ Γ A, Var88 (snoc88 Γ A) A)
     (vs  : ∀ Γ B A, Var88 Γ A → Var88 (snoc88 Γ B) A)
   , Var88 Γ A.

Definition vz88 {Γ A} : Var88 (snoc88 Γ A) A
 := λ Var88 vz88 vs , vz88 _ _.

Definition vs88 {Γ B A} : Var88 Γ A → Var88 (snoc88 Γ B) A
 := λ x Var88 vz88 vs88 , vs88 _ _ _ (x Var88 vz88 vs88).

Definition Tm88 : Con88 → Ty88 → Set
 := λ Γ A ,
   ∀ (Tm88  : Con88 → Ty88 → Set)
     (var   : ∀ Γ A     , Var88 Γ A → Tm88 Γ A)
     (lam   : ∀ Γ A B   , Tm88 (snoc88 Γ A) B → Tm88 Γ (arr88 A B))
     (app   : ∀ Γ A B   , Tm88 Γ (arr88 A B) → Tm88 Γ A → Tm88 Γ B)
   , Tm88 Γ A.

Definition var88 {Γ A} : Var88 Γ A → Tm88 Γ A
 := λ x Tm88 var88 lam app,
     var88 _ _ x.

Definition lam88 {Γ A B} : Tm88 (snoc88 Γ A) B → Tm88 Γ (arr88 A B)
 := λ t Tm88 var88 lam88 app,
     lam88 _ _ _ (t Tm88 var88 lam88 app).

Definition app88 {Γ A B} : Tm88 Γ (arr88 A B) → Tm88 Γ A → Tm88 Γ B
 := λ t u Tm88 var88 lam88 app88,
     app88 _ _ _
         (t Tm88 var88 lam88 app88)
         (u Tm88 var88 lam88 app88).

Definition v088 {Γ A} : Tm88 (snoc88 Γ A) A
 := var88 vz88.

Definition v188 {Γ A B} : Tm88 (snoc88 (snoc88 Γ A) B) A
 := var88 (vs88 vz88).

Definition v288 {Γ A B C} : Tm88 (snoc88 (snoc88 (snoc88 Γ A) B) C) A
 := var88 (vs88 (vs88 vz88)).

Definition v388 {Γ A B C D} : Tm88 (snoc88 (snoc88 (snoc88 (snoc88 Γ A) B) C) D) A
 := var88 (vs88 (vs88 (vs88 vz88))).

Definition v488 {Γ A B C D E} : Tm88 (snoc88 (snoc88 (snoc88 (snoc88 (snoc88 Γ A) B) C) D) E) A
 := var88 (vs88 (vs88 (vs88 (vs88 vz88)))).

Definition test88 {Γ A} : Tm88 Γ (arr88 (arr88 A A) (arr88 A A))
 := lam88 (lam88 (app88 v188 (app88 v188 (app88 v188 (app88 v188 (app88 v188 (app88 v188 v088))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty89 : Set
 := ∀ (Ty89 : Set)
      (ι   : Ty89)
      (arr : Ty89 → Ty89 → Ty89)
    , Ty89.

Definition ι89 : Ty89 := λ _ ι89 _, ι89.

Definition arr89 : Ty89 → Ty89 → Ty89
 := λ A B Ty89 ι89 arr89,
     arr89 (A Ty89 ι89 arr89) (B Ty89 ι89 arr89).

Definition Con89 : Set
 := ∀ (Con89  : Set)
      (nil  : Con89)
      (snoc : Con89 → Ty89 → Con89)
    , Con89.

Definition nil89 : Con89
 := λ Con89 nil89 snoc , nil89.

Definition snoc89 : Con89 → Ty89 → Con89
 := λ Γ A Con89 nil89 snoc89 , snoc89 (Γ Con89 nil89 snoc89) A.

Definition Var89 : Con89 → Ty89 → Set
 := λ Γ A ,
   ∀ (Var89 : Con89 → Ty89 → Set)
     (vz  : ∀ Γ A, Var89 (snoc89 Γ A) A)
     (vs  : ∀ Γ B A, Var89 Γ A → Var89 (snoc89 Γ B) A)
   , Var89 Γ A.

Definition vz89 {Γ A} : Var89 (snoc89 Γ A) A
 := λ Var89 vz89 vs , vz89 _ _.

Definition vs89 {Γ B A} : Var89 Γ A → Var89 (snoc89 Γ B) A
 := λ x Var89 vz89 vs89 , vs89 _ _ _ (x Var89 vz89 vs89).

Definition Tm89 : Con89 → Ty89 → Set
 := λ Γ A ,
   ∀ (Tm89  : Con89 → Ty89 → Set)
     (var   : ∀ Γ A     , Var89 Γ A → Tm89 Γ A)
     (lam   : ∀ Γ A B   , Tm89 (snoc89 Γ A) B → Tm89 Γ (arr89 A B))
     (app   : ∀ Γ A B   , Tm89 Γ (arr89 A B) → Tm89 Γ A → Tm89 Γ B)
   , Tm89 Γ A.

Definition var89 {Γ A} : Var89 Γ A → Tm89 Γ A
 := λ x Tm89 var89 lam app,
     var89 _ _ x.

Definition lam89 {Γ A B} : Tm89 (snoc89 Γ A) B → Tm89 Γ (arr89 A B)
 := λ t Tm89 var89 lam89 app,
     lam89 _ _ _ (t Tm89 var89 lam89 app).

Definition app89 {Γ A B} : Tm89 Γ (arr89 A B) → Tm89 Γ A → Tm89 Γ B
 := λ t u Tm89 var89 lam89 app89,
     app89 _ _ _
         (t Tm89 var89 lam89 app89)
         (u Tm89 var89 lam89 app89).

Definition v089 {Γ A} : Tm89 (snoc89 Γ A) A
 := var89 vz89.

Definition v189 {Γ A B} : Tm89 (snoc89 (snoc89 Γ A) B) A
 := var89 (vs89 vz89).

Definition v289 {Γ A B C} : Tm89 (snoc89 (snoc89 (snoc89 Γ A) B) C) A
 := var89 (vs89 (vs89 vz89)).

Definition v389 {Γ A B C D} : Tm89 (snoc89 (snoc89 (snoc89 (snoc89 Γ A) B) C) D) A
 := var89 (vs89 (vs89 (vs89 vz89))).

Definition v489 {Γ A B C D E} : Tm89 (snoc89 (snoc89 (snoc89 (snoc89 (snoc89 Γ A) B) C) D) E) A
 := var89 (vs89 (vs89 (vs89 (vs89 vz89)))).

Definition test89 {Γ A} : Tm89 Γ (arr89 (arr89 A A) (arr89 A A))
 := lam89 (lam89 (app89 v189 (app89 v189 (app89 v189 (app89 v189 (app89 v189 (app89 v189 v089))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty90 : Set
 := ∀ (Ty90 : Set)
      (ι   : Ty90)
      (arr : Ty90 → Ty90 → Ty90)
    , Ty90.

Definition ι90 : Ty90 := λ _ ι90 _, ι90.

Definition arr90 : Ty90 → Ty90 → Ty90
 := λ A B Ty90 ι90 arr90,
     arr90 (A Ty90 ι90 arr90) (B Ty90 ι90 arr90).

Definition Con90 : Set
 := ∀ (Con90  : Set)
      (nil  : Con90)
      (snoc : Con90 → Ty90 → Con90)
    , Con90.

Definition nil90 : Con90
 := λ Con90 nil90 snoc , nil90.

Definition snoc90 : Con90 → Ty90 → Con90
 := λ Γ A Con90 nil90 snoc90 , snoc90 (Γ Con90 nil90 snoc90) A.

Definition Var90 : Con90 → Ty90 → Set
 := λ Γ A ,
   ∀ (Var90 : Con90 → Ty90 → Set)
     (vz  : ∀ Γ A, Var90 (snoc90 Γ A) A)
     (vs  : ∀ Γ B A, Var90 Γ A → Var90 (snoc90 Γ B) A)
   , Var90 Γ A.

Definition vz90 {Γ A} : Var90 (snoc90 Γ A) A
 := λ Var90 vz90 vs , vz90 _ _.

Definition vs90 {Γ B A} : Var90 Γ A → Var90 (snoc90 Γ B) A
 := λ x Var90 vz90 vs90 , vs90 _ _ _ (x Var90 vz90 vs90).

Definition Tm90 : Con90 → Ty90 → Set
 := λ Γ A ,
   ∀ (Tm90  : Con90 → Ty90 → Set)
     (var   : ∀ Γ A     , Var90 Γ A → Tm90 Γ A)
     (lam   : ∀ Γ A B   , Tm90 (snoc90 Γ A) B → Tm90 Γ (arr90 A B))
     (app   : ∀ Γ A B   , Tm90 Γ (arr90 A B) → Tm90 Γ A → Tm90 Γ B)
   , Tm90 Γ A.

Definition var90 {Γ A} : Var90 Γ A → Tm90 Γ A
 := λ x Tm90 var90 lam app,
     var90 _ _ x.

Definition lam90 {Γ A B} : Tm90 (snoc90 Γ A) B → Tm90 Γ (arr90 A B)
 := λ t Tm90 var90 lam90 app,
     lam90 _ _ _ (t Tm90 var90 lam90 app).

Definition app90 {Γ A B} : Tm90 Γ (arr90 A B) → Tm90 Γ A → Tm90 Γ B
 := λ t u Tm90 var90 lam90 app90,
     app90 _ _ _
         (t Tm90 var90 lam90 app90)
         (u Tm90 var90 lam90 app90).

Definition v090 {Γ A} : Tm90 (snoc90 Γ A) A
 := var90 vz90.

Definition v190 {Γ A B} : Tm90 (snoc90 (snoc90 Γ A) B) A
 := var90 (vs90 vz90).

Definition v290 {Γ A B C} : Tm90 (snoc90 (snoc90 (snoc90 Γ A) B) C) A
 := var90 (vs90 (vs90 vz90)).

Definition v390 {Γ A B C D} : Tm90 (snoc90 (snoc90 (snoc90 (snoc90 Γ A) B) C) D) A
 := var90 (vs90 (vs90 (vs90 vz90))).

Definition v490 {Γ A B C D E} : Tm90 (snoc90 (snoc90 (snoc90 (snoc90 (snoc90 Γ A) B) C) D) E) A
 := var90 (vs90 (vs90 (vs90 (vs90 vz90)))).

Definition test90 {Γ A} : Tm90 Γ (arr90 (arr90 A A) (arr90 A A))
 := lam90 (lam90 (app90 v190 (app90 v190 (app90 v190 (app90 v190 (app90 v190 (app90 v190 v090))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty91 : Set
 := ∀ (Ty91 : Set)
      (ι   : Ty91)
      (arr : Ty91 → Ty91 → Ty91)
    , Ty91.

Definition ι91 : Ty91 := λ _ ι91 _, ι91.

Definition arr91 : Ty91 → Ty91 → Ty91
 := λ A B Ty91 ι91 arr91,
     arr91 (A Ty91 ι91 arr91) (B Ty91 ι91 arr91).

Definition Con91 : Set
 := ∀ (Con91  : Set)
      (nil  : Con91)
      (snoc : Con91 → Ty91 → Con91)
    , Con91.

Definition nil91 : Con91
 := λ Con91 nil91 snoc , nil91.

Definition snoc91 : Con91 → Ty91 → Con91
 := λ Γ A Con91 nil91 snoc91 , snoc91 (Γ Con91 nil91 snoc91) A.

Definition Var91 : Con91 → Ty91 → Set
 := λ Γ A ,
   ∀ (Var91 : Con91 → Ty91 → Set)
     (vz  : ∀ Γ A, Var91 (snoc91 Γ A) A)
     (vs  : ∀ Γ B A, Var91 Γ A → Var91 (snoc91 Γ B) A)
   , Var91 Γ A.

Definition vz91 {Γ A} : Var91 (snoc91 Γ A) A
 := λ Var91 vz91 vs , vz91 _ _.

Definition vs91 {Γ B A} : Var91 Γ A → Var91 (snoc91 Γ B) A
 := λ x Var91 vz91 vs91 , vs91 _ _ _ (x Var91 vz91 vs91).

Definition Tm91 : Con91 → Ty91 → Set
 := λ Γ A ,
   ∀ (Tm91  : Con91 → Ty91 → Set)
     (var   : ∀ Γ A     , Var91 Γ A → Tm91 Γ A)
     (lam   : ∀ Γ A B   , Tm91 (snoc91 Γ A) B → Tm91 Γ (arr91 A B))
     (app   : ∀ Γ A B   , Tm91 Γ (arr91 A B) → Tm91 Γ A → Tm91 Γ B)
   , Tm91 Γ A.

Definition var91 {Γ A} : Var91 Γ A → Tm91 Γ A
 := λ x Tm91 var91 lam app,
     var91 _ _ x.

Definition lam91 {Γ A B} : Tm91 (snoc91 Γ A) B → Tm91 Γ (arr91 A B)
 := λ t Tm91 var91 lam91 app,
     lam91 _ _ _ (t Tm91 var91 lam91 app).

Definition app91 {Γ A B} : Tm91 Γ (arr91 A B) → Tm91 Γ A → Tm91 Γ B
 := λ t u Tm91 var91 lam91 app91,
     app91 _ _ _
         (t Tm91 var91 lam91 app91)
         (u Tm91 var91 lam91 app91).

Definition v091 {Γ A} : Tm91 (snoc91 Γ A) A
 := var91 vz91.

Definition v191 {Γ A B} : Tm91 (snoc91 (snoc91 Γ A) B) A
 := var91 (vs91 vz91).

Definition v291 {Γ A B C} : Tm91 (snoc91 (snoc91 (snoc91 Γ A) B) C) A
 := var91 (vs91 (vs91 vz91)).

Definition v391 {Γ A B C D} : Tm91 (snoc91 (snoc91 (snoc91 (snoc91 Γ A) B) C) D) A
 := var91 (vs91 (vs91 (vs91 vz91))).

Definition v491 {Γ A B C D E} : Tm91 (snoc91 (snoc91 (snoc91 (snoc91 (snoc91 Γ A) B) C) D) E) A
 := var91 (vs91 (vs91 (vs91 (vs91 vz91)))).

Definition test91 {Γ A} : Tm91 Γ (arr91 (arr91 A A) (arr91 A A))
 := lam91 (lam91 (app91 v191 (app91 v191 (app91 v191 (app91 v191 (app91 v191 (app91 v191 v091))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty92 : Set
 := ∀ (Ty92 : Set)
      (ι   : Ty92)
      (arr : Ty92 → Ty92 → Ty92)
    , Ty92.

Definition ι92 : Ty92 := λ _ ι92 _, ι92.

Definition arr92 : Ty92 → Ty92 → Ty92
 := λ A B Ty92 ι92 arr92,
     arr92 (A Ty92 ι92 arr92) (B Ty92 ι92 arr92).

Definition Con92 : Set
 := ∀ (Con92  : Set)
      (nil  : Con92)
      (snoc : Con92 → Ty92 → Con92)
    , Con92.

Definition nil92 : Con92
 := λ Con92 nil92 snoc , nil92.

Definition snoc92 : Con92 → Ty92 → Con92
 := λ Γ A Con92 nil92 snoc92 , snoc92 (Γ Con92 nil92 snoc92) A.

Definition Var92 : Con92 → Ty92 → Set
 := λ Γ A ,
   ∀ (Var92 : Con92 → Ty92 → Set)
     (vz  : ∀ Γ A, Var92 (snoc92 Γ A) A)
     (vs  : ∀ Γ B A, Var92 Γ A → Var92 (snoc92 Γ B) A)
   , Var92 Γ A.

Definition vz92 {Γ A} : Var92 (snoc92 Γ A) A
 := λ Var92 vz92 vs , vz92 _ _.

Definition vs92 {Γ B A} : Var92 Γ A → Var92 (snoc92 Γ B) A
 := λ x Var92 vz92 vs92 , vs92 _ _ _ (x Var92 vz92 vs92).

Definition Tm92 : Con92 → Ty92 → Set
 := λ Γ A ,
   ∀ (Tm92  : Con92 → Ty92 → Set)
     (var   : ∀ Γ A     , Var92 Γ A → Tm92 Γ A)
     (lam   : ∀ Γ A B   , Tm92 (snoc92 Γ A) B → Tm92 Γ (arr92 A B))
     (app   : ∀ Γ A B   , Tm92 Γ (arr92 A B) → Tm92 Γ A → Tm92 Γ B)
   , Tm92 Γ A.

Definition var92 {Γ A} : Var92 Γ A → Tm92 Γ A
 := λ x Tm92 var92 lam app,
     var92 _ _ x.

Definition lam92 {Γ A B} : Tm92 (snoc92 Γ A) B → Tm92 Γ (arr92 A B)
 := λ t Tm92 var92 lam92 app,
     lam92 _ _ _ (t Tm92 var92 lam92 app).

Definition app92 {Γ A B} : Tm92 Γ (arr92 A B) → Tm92 Γ A → Tm92 Γ B
 := λ t u Tm92 var92 lam92 app92,
     app92 _ _ _
         (t Tm92 var92 lam92 app92)
         (u Tm92 var92 lam92 app92).

Definition v092 {Γ A} : Tm92 (snoc92 Γ A) A
 := var92 vz92.

Definition v192 {Γ A B} : Tm92 (snoc92 (snoc92 Γ A) B) A
 := var92 (vs92 vz92).

Definition v292 {Γ A B C} : Tm92 (snoc92 (snoc92 (snoc92 Γ A) B) C) A
 := var92 (vs92 (vs92 vz92)).

Definition v392 {Γ A B C D} : Tm92 (snoc92 (snoc92 (snoc92 (snoc92 Γ A) B) C) D) A
 := var92 (vs92 (vs92 (vs92 vz92))).

Definition v492 {Γ A B C D E} : Tm92 (snoc92 (snoc92 (snoc92 (snoc92 (snoc92 Γ A) B) C) D) E) A
 := var92 (vs92 (vs92 (vs92 (vs92 vz92)))).

Definition test92 {Γ A} : Tm92 Γ (arr92 (arr92 A A) (arr92 A A))
 := lam92 (lam92 (app92 v192 (app92 v192 (app92 v192 (app92 v192 (app92 v192 (app92 v192 v092))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty93 : Set
 := ∀ (Ty93 : Set)
      (ι   : Ty93)
      (arr : Ty93 → Ty93 → Ty93)
    , Ty93.

Definition ι93 : Ty93 := λ _ ι93 _, ι93.

Definition arr93 : Ty93 → Ty93 → Ty93
 := λ A B Ty93 ι93 arr93,
     arr93 (A Ty93 ι93 arr93) (B Ty93 ι93 arr93).

Definition Con93 : Set
 := ∀ (Con93  : Set)
      (nil  : Con93)
      (snoc : Con93 → Ty93 → Con93)
    , Con93.

Definition nil93 : Con93
 := λ Con93 nil93 snoc , nil93.

Definition snoc93 : Con93 → Ty93 → Con93
 := λ Γ A Con93 nil93 snoc93 , snoc93 (Γ Con93 nil93 snoc93) A.

Definition Var93 : Con93 → Ty93 → Set
 := λ Γ A ,
   ∀ (Var93 : Con93 → Ty93 → Set)
     (vz  : ∀ Γ A, Var93 (snoc93 Γ A) A)
     (vs  : ∀ Γ B A, Var93 Γ A → Var93 (snoc93 Γ B) A)
   , Var93 Γ A.

Definition vz93 {Γ A} : Var93 (snoc93 Γ A) A
 := λ Var93 vz93 vs , vz93 _ _.

Definition vs93 {Γ B A} : Var93 Γ A → Var93 (snoc93 Γ B) A
 := λ x Var93 vz93 vs93 , vs93 _ _ _ (x Var93 vz93 vs93).

Definition Tm93 : Con93 → Ty93 → Set
 := λ Γ A ,
   ∀ (Tm93  : Con93 → Ty93 → Set)
     (var   : ∀ Γ A     , Var93 Γ A → Tm93 Γ A)
     (lam   : ∀ Γ A B   , Tm93 (snoc93 Γ A) B → Tm93 Γ (arr93 A B))
     (app   : ∀ Γ A B   , Tm93 Γ (arr93 A B) → Tm93 Γ A → Tm93 Γ B)
   , Tm93 Γ A.

Definition var93 {Γ A} : Var93 Γ A → Tm93 Γ A
 := λ x Tm93 var93 lam app,
     var93 _ _ x.

Definition lam93 {Γ A B} : Tm93 (snoc93 Γ A) B → Tm93 Γ (arr93 A B)
 := λ t Tm93 var93 lam93 app,
     lam93 _ _ _ (t Tm93 var93 lam93 app).

Definition app93 {Γ A B} : Tm93 Γ (arr93 A B) → Tm93 Γ A → Tm93 Γ B
 := λ t u Tm93 var93 lam93 app93,
     app93 _ _ _
         (t Tm93 var93 lam93 app93)
         (u Tm93 var93 lam93 app93).

Definition v093 {Γ A} : Tm93 (snoc93 Γ A) A
 := var93 vz93.

Definition v193 {Γ A B} : Tm93 (snoc93 (snoc93 Γ A) B) A
 := var93 (vs93 vz93).

Definition v293 {Γ A B C} : Tm93 (snoc93 (snoc93 (snoc93 Γ A) B) C) A
 := var93 (vs93 (vs93 vz93)).

Definition v393 {Γ A B C D} : Tm93 (snoc93 (snoc93 (snoc93 (snoc93 Γ A) B) C) D) A
 := var93 (vs93 (vs93 (vs93 vz93))).

Definition v493 {Γ A B C D E} : Tm93 (snoc93 (snoc93 (snoc93 (snoc93 (snoc93 Γ A) B) C) D) E) A
 := var93 (vs93 (vs93 (vs93 (vs93 vz93)))).

Definition test93 {Γ A} : Tm93 Γ (arr93 (arr93 A A) (arr93 A A))
 := lam93 (lam93 (app93 v193 (app93 v193 (app93 v193 (app93 v193 (app93 v193 (app93 v193 v093))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty94 : Set
 := ∀ (Ty94 : Set)
      (ι   : Ty94)
      (arr : Ty94 → Ty94 → Ty94)
    , Ty94.

Definition ι94 : Ty94 := λ _ ι94 _, ι94.

Definition arr94 : Ty94 → Ty94 → Ty94
 := λ A B Ty94 ι94 arr94,
     arr94 (A Ty94 ι94 arr94) (B Ty94 ι94 arr94).

Definition Con94 : Set
 := ∀ (Con94  : Set)
      (nil  : Con94)
      (snoc : Con94 → Ty94 → Con94)
    , Con94.

Definition nil94 : Con94
 := λ Con94 nil94 snoc , nil94.

Definition snoc94 : Con94 → Ty94 → Con94
 := λ Γ A Con94 nil94 snoc94 , snoc94 (Γ Con94 nil94 snoc94) A.

Definition Var94 : Con94 → Ty94 → Set
 := λ Γ A ,
   ∀ (Var94 : Con94 → Ty94 → Set)
     (vz  : ∀ Γ A, Var94 (snoc94 Γ A) A)
     (vs  : ∀ Γ B A, Var94 Γ A → Var94 (snoc94 Γ B) A)
   , Var94 Γ A.

Definition vz94 {Γ A} : Var94 (snoc94 Γ A) A
 := λ Var94 vz94 vs , vz94 _ _.

Definition vs94 {Γ B A} : Var94 Γ A → Var94 (snoc94 Γ B) A
 := λ x Var94 vz94 vs94 , vs94 _ _ _ (x Var94 vz94 vs94).

Definition Tm94 : Con94 → Ty94 → Set
 := λ Γ A ,
   ∀ (Tm94  : Con94 → Ty94 → Set)
     (var   : ∀ Γ A     , Var94 Γ A → Tm94 Γ A)
     (lam   : ∀ Γ A B   , Tm94 (snoc94 Γ A) B → Tm94 Γ (arr94 A B))
     (app   : ∀ Γ A B   , Tm94 Γ (arr94 A B) → Tm94 Γ A → Tm94 Γ B)
   , Tm94 Γ A.

Definition var94 {Γ A} : Var94 Γ A → Tm94 Γ A
 := λ x Tm94 var94 lam app,
     var94 _ _ x.

Definition lam94 {Γ A B} : Tm94 (snoc94 Γ A) B → Tm94 Γ (arr94 A B)
 := λ t Tm94 var94 lam94 app,
     lam94 _ _ _ (t Tm94 var94 lam94 app).

Definition app94 {Γ A B} : Tm94 Γ (arr94 A B) → Tm94 Γ A → Tm94 Γ B
 := λ t u Tm94 var94 lam94 app94,
     app94 _ _ _
         (t Tm94 var94 lam94 app94)
         (u Tm94 var94 lam94 app94).

Definition v094 {Γ A} : Tm94 (snoc94 Γ A) A
 := var94 vz94.

Definition v194 {Γ A B} : Tm94 (snoc94 (snoc94 Γ A) B) A
 := var94 (vs94 vz94).

Definition v294 {Γ A B C} : Tm94 (snoc94 (snoc94 (snoc94 Γ A) B) C) A
 := var94 (vs94 (vs94 vz94)).

Definition v394 {Γ A B C D} : Tm94 (snoc94 (snoc94 (snoc94 (snoc94 Γ A) B) C) D) A
 := var94 (vs94 (vs94 (vs94 vz94))).

Definition v494 {Γ A B C D E} : Tm94 (snoc94 (snoc94 (snoc94 (snoc94 (snoc94 Γ A) B) C) D) E) A
 := var94 (vs94 (vs94 (vs94 (vs94 vz94)))).

Definition test94 {Γ A} : Tm94 Γ (arr94 (arr94 A A) (arr94 A A))
 := lam94 (lam94 (app94 v194 (app94 v194 (app94 v194 (app94 v194 (app94 v194 (app94 v194 v094))))))).

Require Import Coq.Unicode.Utf8.

Definition Ty95 : Set
 := ∀ (Ty95 : Set)
      (ι   : Ty95)
      (arr : Ty95 → Ty95 → Ty95)
    , Ty95.

Definition ι95 : Ty95 := λ _ ι95 _, ι95.

Definition arr95 : Ty95 → Ty95 → Ty95
 := λ A B Ty95 ι95 arr95,
     arr95 (A Ty95 ι95 arr95) (B Ty95 ι95 arr95).

Definition Con95 : Set
 := ∀ (Con95  : Set)
      (nil  : Con95)
      (snoc : Con95 → Ty95 → Con95)
    , Con95.

Definition nil95 : Con95
 := λ Con95 nil95 snoc , nil95.

Definition snoc95 : Con95 → Ty95 → Con95
 := λ Γ A Con95 nil95 snoc95 , snoc95 (Γ Con95 nil95 snoc95) A.

Definition Var95 : Con95 → Ty95 → Set
 := λ Γ A ,
   ∀ (Var95 : Con95 → Ty95 → Set)
     (vz  : ∀ Γ A, Var95 (snoc95 Γ A) A)
     (vs  : ∀ Γ B A, Var95 Γ A → Var95 (snoc95 Γ B) A)
   , Var95 Γ A.

Definition vz95 {Γ A} : Var95 (snoc95 Γ A) A
 := λ Var95 vz95 vs , vz95 _ _.

Definition vs95 {Γ B A} : Var95 Γ A → Var95 (snoc95 Γ B) A
 := λ x Var95 vz95 vs95 , vs95 _ _ _ (x Var95 vz95 vs95).

Definition Tm95 : Con95 → Ty95 → Set
 := λ Γ A ,
   ∀ (Tm95  : Con95 → Ty95 → Set)
     (var   : ∀ Γ A     , Var95 Γ A → Tm95 Γ A)
     (lam   : ∀ Γ A B   , Tm95 (snoc95 Γ A) B → Tm95 Γ (arr95 A B))
     (app   : ∀ Γ A B   , Tm95 Γ (arr95 A B) → Tm95 Γ A → Tm95 Γ B)
   , Tm95 Γ A.

Definition var95 {Γ A} : Var95 Γ A → Tm95 Γ A
 := λ x Tm95 var95 lam app,
     var95 _ _ x.

Definition lam95 {Γ A B} : Tm95 (snoc95 Γ A) B → Tm95 Γ (arr95 A B)
 := λ t Tm95 var95 lam95 app,
     lam95 _ _ _ (t Tm95 var95 lam95 app).

Definition app95 {Γ A B} : Tm95 Γ (arr95 A B) → Tm95 Γ A → Tm95 Γ B
 := λ t u Tm95 var95 lam95 app95,
     app95 _ _ _
         (t Tm95 var95 lam95 app95)
         (u Tm95 var95 lam95 app95).

Definition v095 {Γ A} : Tm95 (snoc95 Γ A) A
 := var95 vz95.

Definition v195 {Γ A B} : Tm95 (snoc95 (snoc95 Γ A) B) A
 := var95 (vs95 vz95).

Definition v295 {Γ A B C} : Tm95 (snoc95 (snoc95 (snoc95 Γ A) B) C) A
 := var95 (vs95 (vs95 vz95)).

Definition v395 {Γ A B C D} : Tm95 (snoc95 (snoc95 (snoc95 (snoc95 Γ A) B) C) D) A
 := var95 (vs95 (vs95 (vs95 vz95))).

Definition v495 {Γ A B C D E} : Tm95 (snoc95 (snoc95 (snoc95 (snoc95 (snoc95 Γ A) B) C) D) E) A
 := var95 (vs95 (vs95 (vs95 (vs95 vz95)))).

Definition test95 {Γ A} : Tm95 Γ (arr95 (arr95 A A) (arr95 A A))
 := lam95 (lam95 (app95 v195 (app95 v195 (app95 v195 (app95 v195 (app95 v195 (app95 v195 v095))))))).

