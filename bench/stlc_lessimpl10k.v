Require Import Coq.Unicode.Utf8.

Definition Ty : Set
 := ∀ (Ty           : Set)
      (nat top bot  : Ty)
      (arr prod sum : Ty → Ty → Ty)
    , Ty.

Definition nat : Ty := λ _ nat _ _ _ _ _ , nat.
Definition top : Ty := λ _ _ top _ _ _ _ , top.
Definition bot : Ty := λ _ _ _ bot _ _ _ , bot.

Definition arr : Ty → Ty → Ty
 := λ A B Ty nat top bot arr prod sum ,
     arr (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum).

Definition prod : Ty → Ty → Ty
 := λ A B Ty nat top bot arr prod sum ,
     prod (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum).

Definition sum : Ty → Ty → Ty
 := λ A B Ty nat top bot arr prod sum ,
     sum (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum).

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
     (tt    : ∀ Γ       , Tm Γ top)
     (pair  : ∀ Γ A B   , Tm Γ A → Tm Γ B → Tm Γ (prod A B))
     (fst   : ∀ Γ A B   , Tm Γ (prod A B) → Tm Γ A)
     (snd   : ∀ Γ A B   , Tm Γ (prod A B) → Tm Γ B)
     (left  : ∀ Γ A B   , Tm Γ A → Tm Γ (sum A B))
     (right : ∀ Γ A B   , Tm Γ B → Tm Γ (sum A B))
     (case  : ∀ Γ A B C , Tm Γ (sum A B) → Tm Γ (arr A C) → Tm Γ (arr B C) → Tm Γ C)
     (zero  : ∀ Γ       , Tm Γ nat)
     (suc   : ∀ Γ       , Tm Γ nat → Tm Γ nat)
     (rec   : ∀ Γ A     , Tm Γ nat → Tm Γ (arr nat (arr A A)) → Tm Γ A → Tm Γ A)
   , Tm Γ A.

Definition var {Γ A} : Var Γ A → Tm Γ A
 := λ x Tm var lam app tt pair fst snd left right case zero suc rec ,
     var _ _ x.

Definition lam {Γ A B} : Tm (snoc Γ A) B → Tm Γ (arr A B)
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec ,
     lam _ _ _ (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition app {Γ A B} : Tm Γ (arr A B) → Tm Γ A → Tm Γ B
 := λ t u Tm var lam app tt pair fst snd left right case zero suc rec ,
     app _ _ _
         (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec).

Definition tt {Γ} : Tm Γ top
 := λ Tm var lam app tt pair fst snd left right case zero suc rec , tt _.

Definition pair {Γ A B} : Tm Γ A → Tm Γ B → Tm Γ (prod A B)
 := λ t u Tm var lam app tt pair fst snd left right case zero suc rec ,
     pair _ _ _
          (t Tm var lam app tt pair fst snd left right case zero suc rec)
          (u Tm var lam app tt pair fst snd left right case zero suc rec).

Definition fst {Γ A B} : Tm Γ (prod A B) → Tm Γ A
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec ,
     fst _ _ _
         (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition snd {Γ A B} : Tm Γ (prod A B) → Tm Γ B
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec ,
     snd _ _ _
          (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition left {Γ A B} : Tm Γ A → Tm Γ (sum A B)
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec ,
     left _ _ _
          (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition right {Γ A B} : Tm Γ B → Tm Γ (sum A B)
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec ,
     right _ _ _
            (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition case {Γ A B C} : Tm Γ (sum A B) → Tm Γ (arr A C) → Tm Γ (arr B C) → Tm Γ C
 := λ t u v Tm var lam app tt pair fst snd left right case zero suc rec ,
     case _ _ _ _
           (t Tm var lam app tt pair fst snd left right case zero suc rec)
           (u Tm var lam app tt pair fst snd left right case zero suc rec)
           (v Tm var lam app tt pair fst snd left right case zero suc rec).

Definition zero  {Γ} : Tm Γ nat
 := λ Tm var lam app tt pair fst snd left right case zero suc rec , zero _.

Definition suc {Γ} : Tm Γ nat → Tm Γ nat
 := λ t Tm var lam app tt pair fst snd left right case zero suc rec ,
   suc _ (t Tm var lam app tt pair fst snd left right case zero suc rec).

Definition rec {Γ A} : Tm Γ nat → Tm Γ (arr nat (arr A A)) → Tm Γ A → Tm Γ A
 := λ t u v Tm var lam app tt pair fst snd left right case zero suc rec ,
     rec _ _
         (t Tm var lam app tt pair fst snd left right case zero suc rec)
         (u Tm var lam app tt pair fst snd left right case zero suc rec)
         (v Tm var lam app tt pair fst snd left right case zero suc rec).

Definition v0 {Γ A} : Tm (snoc Γ A) A
 := var vz.

Definition v1 {Γ A B} : Tm (snoc (snoc Γ A) B) A
 := var (vs vz).

Definition v2 {Γ A B C} : Tm (snoc (snoc (snoc Γ A) B) C) A
 := var (vs (vs vz)).

Definition v3 {Γ A B C D} : Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A
 := var (vs (vs (vs vz))).

Definition tbool : Ty
 := sum top top.

Definition ttrue {Γ} : Tm Γ tbool
 := left tt.

Definition tfalse {Γ} : Tm Γ tbool
 := right tt.

Definition ifthenelse {Γ A} : Tm Γ (arr tbool (arr A (arr A A)))
 := lam (lam (lam (case v2 (lam v2) (lam v1)))).

Definition times4 {Γ A} : Tm Γ (arr (arr A A) (arr A A))
  := lam (lam (app v1 (app v1 (app v1 (app v1 v0))))).

Definition add {Γ} : Tm Γ (arr nat (arr nat nat))
 := lam (rec v0
      (lam (lam (lam (suc (app v1 v0)))))
      (lam v0)).

Definition mul {Γ} : Tm Γ (arr nat (arr nat nat))
 := lam (rec v0
     (lam (lam (lam (app (app add (app v1 v0)) v0))))
     (lam zero)).

Definition fact {Γ} : Tm Γ (arr nat nat)
 := lam (rec v0 (lam (lam (app (app mul (suc v1)) v0)))
        (suc zero)).

Require Import Coq.Unicode.Utf8.

Definition Ty1 : Set
 := ∀ (Ty1           : Set)
      (nat top bot  : Ty1)
      (arr prod sum : Ty1 → Ty1 → Ty1)
    , Ty1.

Definition nat1 : Ty1 := λ _ nat1 _ _ _ _ _ , nat1.
Definition top1 : Ty1 := λ _ _ top1 _ _ _ _ , top1.
Definition bot1 : Ty1 := λ _ _ _ bot1 _ _ _ , bot1.

Definition arr1 : Ty1 → Ty1 → Ty1
 := λ A B Ty1 nat1 top1 bot1 arr1 prod sum ,
     arr1 (A Ty1 nat1 top1 bot1 arr1 prod sum) (B Ty1 nat1 top1 bot1 arr1 prod sum).

Definition prod1 : Ty1 → Ty1 → Ty1
 := λ A B Ty1 nat1 top1 bot1 arr1 prod1 sum ,
     prod1 (A Ty1 nat1 top1 bot1 arr1 prod1 sum) (B Ty1 nat1 top1 bot1 arr1 prod1 sum).

Definition sum1 : Ty1 → Ty1 → Ty1
 := λ A B Ty1 nat1 top1 bot1 arr1 prod1 sum1 ,
     sum1 (A Ty1 nat1 top1 bot1 arr1 prod1 sum1) (B Ty1 nat1 top1 bot1 arr1 prod1 sum1).

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
     (tt    : ∀ Γ       , Tm1 Γ top1)
     (pair  : ∀ Γ A B   , Tm1 Γ A → Tm1 Γ B → Tm1 Γ (prod1 A B))
     (fst   : ∀ Γ A B   , Tm1 Γ (prod1 A B) → Tm1 Γ A)
     (snd   : ∀ Γ A B   , Tm1 Γ (prod1 A B) → Tm1 Γ B)
     (left  : ∀ Γ A B   , Tm1 Γ A → Tm1 Γ (sum1 A B))
     (right : ∀ Γ A B   , Tm1 Γ B → Tm1 Γ (sum1 A B))
     (case  : ∀ Γ A B C , Tm1 Γ (sum1 A B) → Tm1 Γ (arr1 A C) → Tm1 Γ (arr1 B C) → Tm1 Γ C)
     (zero  : ∀ Γ       , Tm1 Γ nat1)
     (suc   : ∀ Γ       , Tm1 Γ nat1 → Tm1 Γ nat1)
     (rec   : ∀ Γ A     , Tm1 Γ nat1 → Tm1 Γ (arr1 nat1 (arr1 A A)) → Tm1 Γ A → Tm1 Γ A)
   , Tm1 Γ A.

Definition var1 {Γ A} : Var1 Γ A → Tm1 Γ A
 := λ x Tm1 var1 lam app tt pair fst snd left right case zero suc rec ,
     var1 _ _ x.

Definition lam1 {Γ A B} : Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B)
 := λ t Tm1 var1 lam1 app tt pair fst snd left right case zero suc rec ,
     lam1 _ _ _ (t Tm1 var1 lam1 app tt pair fst snd left right case zero suc rec).

Definition app1 {Γ A B} : Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B
 := λ t u Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec ,
     app1 _ _ _
         (t Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec)
         (u Tm1 var1 lam1 app1 tt pair fst snd left right case zero suc rec).

Definition tt1 {Γ} : Tm1 Γ top1
 := λ Tm1 var1 lam1 app1 tt1 pair fst snd left right case zero suc rec , tt1 _.

Definition pair1 {Γ A B} : Tm1 Γ A → Tm1 Γ B → Tm1 Γ (prod1 A B)
 := λ t u Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec ,
     pair1 _ _ _
          (t Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec)
          (u Tm1 var1 lam1 app1 tt1 pair1 fst snd left right case zero suc rec).

Definition fst1 {Γ A B} : Tm1 Γ (prod1 A B) → Tm1 Γ A
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd left right case zero suc rec ,
     fst1 _ _ _
         (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd left right case zero suc rec).

Definition snd1 {Γ A B} : Tm1 Γ (prod1 A B) → Tm1 Γ B
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left right case zero suc rec ,
     snd1 _ _ _
          (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left right case zero suc rec).

Definition left1 {Γ A B} : Tm1 Γ A → Tm1 Γ (sum1 A B)
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right case zero suc rec ,
     left1 _ _ _
          (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right case zero suc rec).

Definition right1 {Γ A B} : Tm1 Γ B → Tm1 Γ (sum1 A B)
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case zero suc rec ,
     right1 _ _ _
            (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case zero suc rec).

Definition case1 {Γ A B C} : Tm1 Γ (sum1 A B) → Tm1 Γ (arr1 A C) → Tm1 Γ (arr1 B C) → Tm1 Γ C
 := λ t u v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec ,
     case1 _ _ _ _
           (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)
           (u Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec)
           (v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero suc rec).

Definition zero1  {Γ} : Tm1 Γ nat1
 := λ Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc rec , zero1 _.

Definition suc1 {Γ} : Tm1 Γ nat1 → Tm1 Γ nat1
 := λ t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec ,
   suc1 _ (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec).

Definition rec1 {Γ A} : Tm1 Γ nat1 → Tm1 Γ (arr1 nat1 (arr1 A A)) → Tm1 Γ A → Tm1 Γ A
 := λ t u v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1 ,
     rec1 _ _
         (t Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)
         (u Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1)
         (v Tm1 var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 case1 zero1 suc1 rec1).

Definition v01 {Γ A} : Tm1 (snoc1 Γ A) A
 := var1 vz1.

Definition v11 {Γ A B} : Tm1 (snoc1 (snoc1 Γ A) B) A
 := var1 (vs1 vz1).

Definition v21 {Γ A B C} : Tm1 (snoc1 (snoc1 (snoc1 Γ A) B) C) A
 := var1 (vs1 (vs1 vz1)).

Definition v31 {Γ A B C D} : Tm1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) A
 := var1 (vs1 (vs1 (vs1 vz1))).

Definition tbool1 : Ty1
 := sum1 top1 top1.

Definition ttrue1 {Γ} : Tm1 Γ tbool1
 := left1 tt1.

Definition tfalse1 {Γ} : Tm1 Γ tbool1
 := right1 tt1.

Definition ifthenelse1 {Γ A} : Tm1 Γ (arr1 tbool1 (arr1 A (arr1 A A)))
 := lam1 (lam1 (lam1 (case1 v21 (lam1 v21) (lam1 v11)))).

Definition times41 {Γ A} : Tm1 Γ (arr1 (arr1 A A) (arr1 A A))
  := lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01))))).

Definition add1 {Γ} : Tm1 Γ (arr1 nat1 (arr1 nat1 nat1))
 := lam1 (rec1 v01
      (lam1 (lam1 (lam1 (suc1 (app1 v11 v01)))))
      (lam1 v01)).

Definition mul1 {Γ} : Tm1 Γ (arr1 nat1 (arr1 nat1 nat1))
 := lam1 (rec1 v01
     (lam1 (lam1 (lam1 (app1 (app1 add1 (app1 v11 v01)) v01))))
     (lam1 zero1)).

Definition fact1 {Γ} : Tm1 Γ (arr1 nat1 nat1)
 := lam1 (rec1 v01 (lam1 (lam1 (app1 (app1 mul1 (suc1 v11)) v01)))
        (suc1 zero1)).

Require Import Coq.Unicode.Utf8.

Definition Ty2 : Set
 := ∀ (Ty2           : Set)
      (nat top bot  : Ty2)
      (arr prod sum : Ty2 → Ty2 → Ty2)
    , Ty2.

Definition nat2 : Ty2 := λ _ nat2 _ _ _ _ _ , nat2.
Definition top2 : Ty2 := λ _ _ top2 _ _ _ _ , top2.
Definition bot2 : Ty2 := λ _ _ _ bot2 _ _ _ , bot2.

Definition arr2 : Ty2 → Ty2 → Ty2
 := λ A B Ty2 nat2 top2 bot2 arr2 prod sum ,
     arr2 (A Ty2 nat2 top2 bot2 arr2 prod sum) (B Ty2 nat2 top2 bot2 arr2 prod sum).

Definition prod2 : Ty2 → Ty2 → Ty2
 := λ A B Ty2 nat2 top2 bot2 arr2 prod2 sum ,
     prod2 (A Ty2 nat2 top2 bot2 arr2 prod2 sum) (B Ty2 nat2 top2 bot2 arr2 prod2 sum).

Definition sum2 : Ty2 → Ty2 → Ty2
 := λ A B Ty2 nat2 top2 bot2 arr2 prod2 sum2 ,
     sum2 (A Ty2 nat2 top2 bot2 arr2 prod2 sum2) (B Ty2 nat2 top2 bot2 arr2 prod2 sum2).

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
     (tt    : ∀ Γ       , Tm2 Γ top2)
     (pair  : ∀ Γ A B   , Tm2 Γ A → Tm2 Γ B → Tm2 Γ (prod2 A B))
     (fst   : ∀ Γ A B   , Tm2 Γ (prod2 A B) → Tm2 Γ A)
     (snd   : ∀ Γ A B   , Tm2 Γ (prod2 A B) → Tm2 Γ B)
     (left  : ∀ Γ A B   , Tm2 Γ A → Tm2 Γ (sum2 A B))
     (right : ∀ Γ A B   , Tm2 Γ B → Tm2 Γ (sum2 A B))
     (case  : ∀ Γ A B C , Tm2 Γ (sum2 A B) → Tm2 Γ (arr2 A C) → Tm2 Γ (arr2 B C) → Tm2 Γ C)
     (zero  : ∀ Γ       , Tm2 Γ nat2)
     (suc   : ∀ Γ       , Tm2 Γ nat2 → Tm2 Γ nat2)
     (rec   : ∀ Γ A     , Tm2 Γ nat2 → Tm2 Γ (arr2 nat2 (arr2 A A)) → Tm2 Γ A → Tm2 Γ A)
   , Tm2 Γ A.

Definition var2 {Γ A} : Var2 Γ A → Tm2 Γ A
 := λ x Tm2 var2 lam app tt pair fst snd left right case zero suc rec ,
     var2 _ _ x.

Definition lam2 {Γ A B} : Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B)
 := λ t Tm2 var2 lam2 app tt pair fst snd left right case zero suc rec ,
     lam2 _ _ _ (t Tm2 var2 lam2 app tt pair fst snd left right case zero suc rec).

Definition app2 {Γ A B} : Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B
 := λ t u Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec ,
     app2 _ _ _
         (t Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec)
         (u Tm2 var2 lam2 app2 tt pair fst snd left right case zero suc rec).

Definition tt2 {Γ} : Tm2 Γ top2
 := λ Tm2 var2 lam2 app2 tt2 pair fst snd left right case zero suc rec , tt2 _.

Definition pair2 {Γ A B} : Tm2 Γ A → Tm2 Γ B → Tm2 Γ (prod2 A B)
 := λ t u Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec ,
     pair2 _ _ _
          (t Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec)
          (u Tm2 var2 lam2 app2 tt2 pair2 fst snd left right case zero suc rec).

Definition fst2 {Γ A B} : Tm2 Γ (prod2 A B) → Tm2 Γ A
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd left right case zero suc rec ,
     fst2 _ _ _
         (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd left right case zero suc rec).

Definition snd2 {Γ A B} : Tm2 Γ (prod2 A B) → Tm2 Γ B
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left right case zero suc rec ,
     snd2 _ _ _
          (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left right case zero suc rec).

Definition left2 {Γ A B} : Tm2 Γ A → Tm2 Γ (sum2 A B)
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right case zero suc rec ,
     left2 _ _ _
          (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right case zero suc rec).

Definition right2 {Γ A B} : Tm2 Γ B → Tm2 Γ (sum2 A B)
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case zero suc rec ,
     right2 _ _ _
            (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case zero suc rec).

Definition case2 {Γ A B C} : Tm2 Γ (sum2 A B) → Tm2 Γ (arr2 A C) → Tm2 Γ (arr2 B C) → Tm2 Γ C
 := λ t u v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec ,
     case2 _ _ _ _
           (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)
           (u Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec)
           (v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero suc rec).

Definition zero2  {Γ} : Tm2 Γ nat2
 := λ Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc rec , zero2 _.

Definition suc2 {Γ} : Tm2 Γ nat2 → Tm2 Γ nat2
 := λ t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec ,
   suc2 _ (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec).

Definition rec2 {Γ A} : Tm2 Γ nat2 → Tm2 Γ (arr2 nat2 (arr2 A A)) → Tm2 Γ A → Tm2 Γ A
 := λ t u v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2 ,
     rec2 _ _
         (t Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)
         (u Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2)
         (v Tm2 var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 case2 zero2 suc2 rec2).

Definition v02 {Γ A} : Tm2 (snoc2 Γ A) A
 := var2 vz2.

Definition v12 {Γ A B} : Tm2 (snoc2 (snoc2 Γ A) B) A
 := var2 (vs2 vz2).

Definition v22 {Γ A B C} : Tm2 (snoc2 (snoc2 (snoc2 Γ A) B) C) A
 := var2 (vs2 (vs2 vz2)).

Definition v32 {Γ A B C D} : Tm2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) A
 := var2 (vs2 (vs2 (vs2 vz2))).

Definition tbool2 : Ty2
 := sum2 top2 top2.

Definition ttrue2 {Γ} : Tm2 Γ tbool2
 := left2 tt2.

Definition tfalse2 {Γ} : Tm2 Γ tbool2
 := right2 tt2.

Definition ifthenelse2 {Γ A} : Tm2 Γ (arr2 tbool2 (arr2 A (arr2 A A)))
 := lam2 (lam2 (lam2 (case2 v22 (lam2 v22) (lam2 v12)))).

Definition times42 {Γ A} : Tm2 Γ (arr2 (arr2 A A) (arr2 A A))
  := lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02))))).

Definition add2 {Γ} : Tm2 Γ (arr2 nat2 (arr2 nat2 nat2))
 := lam2 (rec2 v02
      (lam2 (lam2 (lam2 (suc2 (app2 v12 v02)))))
      (lam2 v02)).

Definition mul2 {Γ} : Tm2 Γ (arr2 nat2 (arr2 nat2 nat2))
 := lam2 (rec2 v02
     (lam2 (lam2 (lam2 (app2 (app2 add2 (app2 v12 v02)) v02))))
     (lam2 zero2)).

Definition fact2 {Γ} : Tm2 Γ (arr2 nat2 nat2)
 := lam2 (rec2 v02 (lam2 (lam2 (app2 (app2 mul2 (suc2 v12)) v02)))
        (suc2 zero2)).

Require Import Coq.Unicode.Utf8.

Definition Ty3 : Set
 := ∀ (Ty3           : Set)
      (nat top bot  : Ty3)
      (arr prod sum : Ty3 → Ty3 → Ty3)
    , Ty3.

Definition nat3 : Ty3 := λ _ nat3 _ _ _ _ _ , nat3.
Definition top3 : Ty3 := λ _ _ top3 _ _ _ _ , top3.
Definition bot3 : Ty3 := λ _ _ _ bot3 _ _ _ , bot3.

Definition arr3 : Ty3 → Ty3 → Ty3
 := λ A B Ty3 nat3 top3 bot3 arr3 prod sum ,
     arr3 (A Ty3 nat3 top3 bot3 arr3 prod sum) (B Ty3 nat3 top3 bot3 arr3 prod sum).

Definition prod3 : Ty3 → Ty3 → Ty3
 := λ A B Ty3 nat3 top3 bot3 arr3 prod3 sum ,
     prod3 (A Ty3 nat3 top3 bot3 arr3 prod3 sum) (B Ty3 nat3 top3 bot3 arr3 prod3 sum).

Definition sum3 : Ty3 → Ty3 → Ty3
 := λ A B Ty3 nat3 top3 bot3 arr3 prod3 sum3 ,
     sum3 (A Ty3 nat3 top3 bot3 arr3 prod3 sum3) (B Ty3 nat3 top3 bot3 arr3 prod3 sum3).

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
     (tt    : ∀ Γ       , Tm3 Γ top3)
     (pair  : ∀ Γ A B   , Tm3 Γ A → Tm3 Γ B → Tm3 Γ (prod3 A B))
     (fst   : ∀ Γ A B   , Tm3 Γ (prod3 A B) → Tm3 Γ A)
     (snd   : ∀ Γ A B   , Tm3 Γ (prod3 A B) → Tm3 Γ B)
     (left  : ∀ Γ A B   , Tm3 Γ A → Tm3 Γ (sum3 A B))
     (right : ∀ Γ A B   , Tm3 Γ B → Tm3 Γ (sum3 A B))
     (case  : ∀ Γ A B C , Tm3 Γ (sum3 A B) → Tm3 Γ (arr3 A C) → Tm3 Γ (arr3 B C) → Tm3 Γ C)
     (zero  : ∀ Γ       , Tm3 Γ nat3)
     (suc   : ∀ Γ       , Tm3 Γ nat3 → Tm3 Γ nat3)
     (rec   : ∀ Γ A     , Tm3 Γ nat3 → Tm3 Γ (arr3 nat3 (arr3 A A)) → Tm3 Γ A → Tm3 Γ A)
   , Tm3 Γ A.

Definition var3 {Γ A} : Var3 Γ A → Tm3 Γ A
 := λ x Tm3 var3 lam app tt pair fst snd left right case zero suc rec ,
     var3 _ _ x.

Definition lam3 {Γ A B} : Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B)
 := λ t Tm3 var3 lam3 app tt pair fst snd left right case zero suc rec ,
     lam3 _ _ _ (t Tm3 var3 lam3 app tt pair fst snd left right case zero suc rec).

Definition app3 {Γ A B} : Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B
 := λ t u Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec ,
     app3 _ _ _
         (t Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec)
         (u Tm3 var3 lam3 app3 tt pair fst snd left right case zero suc rec).

Definition tt3 {Γ} : Tm3 Γ top3
 := λ Tm3 var3 lam3 app3 tt3 pair fst snd left right case zero suc rec , tt3 _.

Definition pair3 {Γ A B} : Tm3 Γ A → Tm3 Γ B → Tm3 Γ (prod3 A B)
 := λ t u Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec ,
     pair3 _ _ _
          (t Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec)
          (u Tm3 var3 lam3 app3 tt3 pair3 fst snd left right case zero suc rec).

Definition fst3 {Γ A B} : Tm3 Γ (prod3 A B) → Tm3 Γ A
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd left right case zero suc rec ,
     fst3 _ _ _
         (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd left right case zero suc rec).

Definition snd3 {Γ A B} : Tm3 Γ (prod3 A B) → Tm3 Γ B
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left right case zero suc rec ,
     snd3 _ _ _
          (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left right case zero suc rec).

Definition left3 {Γ A B} : Tm3 Γ A → Tm3 Γ (sum3 A B)
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right case zero suc rec ,
     left3 _ _ _
          (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right case zero suc rec).

Definition right3 {Γ A B} : Tm3 Γ B → Tm3 Γ (sum3 A B)
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case zero suc rec ,
     right3 _ _ _
            (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case zero suc rec).

Definition case3 {Γ A B C} : Tm3 Γ (sum3 A B) → Tm3 Γ (arr3 A C) → Tm3 Γ (arr3 B C) → Tm3 Γ C
 := λ t u v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec ,
     case3 _ _ _ _
           (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)
           (u Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec)
           (v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero suc rec).

Definition zero3  {Γ} : Tm3 Γ nat3
 := λ Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc rec , zero3 _.

Definition suc3 {Γ} : Tm3 Γ nat3 → Tm3 Γ nat3
 := λ t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec ,
   suc3 _ (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec).

Definition rec3 {Γ A} : Tm3 Γ nat3 → Tm3 Γ (arr3 nat3 (arr3 A A)) → Tm3 Γ A → Tm3 Γ A
 := λ t u v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3 ,
     rec3 _ _
         (t Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)
         (u Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3)
         (v Tm3 var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 case3 zero3 suc3 rec3).

Definition v03 {Γ A} : Tm3 (snoc3 Γ A) A
 := var3 vz3.

Definition v13 {Γ A B} : Tm3 (snoc3 (snoc3 Γ A) B) A
 := var3 (vs3 vz3).

Definition v23 {Γ A B C} : Tm3 (snoc3 (snoc3 (snoc3 Γ A) B) C) A
 := var3 (vs3 (vs3 vz3)).

Definition v33 {Γ A B C D} : Tm3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) A
 := var3 (vs3 (vs3 (vs3 vz3))).

Definition tbool3 : Ty3
 := sum3 top3 top3.

Definition ttrue3 {Γ} : Tm3 Γ tbool3
 := left3 tt3.

Definition tfalse3 {Γ} : Tm3 Γ tbool3
 := right3 tt3.

Definition ifthenelse3 {Γ A} : Tm3 Γ (arr3 tbool3 (arr3 A (arr3 A A)))
 := lam3 (lam3 (lam3 (case3 v23 (lam3 v23) (lam3 v13)))).

Definition times43 {Γ A} : Tm3 Γ (arr3 (arr3 A A) (arr3 A A))
  := lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03))))).

Definition add3 {Γ} : Tm3 Γ (arr3 nat3 (arr3 nat3 nat3))
 := lam3 (rec3 v03
      (lam3 (lam3 (lam3 (suc3 (app3 v13 v03)))))
      (lam3 v03)).

Definition mul3 {Γ} : Tm3 Γ (arr3 nat3 (arr3 nat3 nat3))
 := lam3 (rec3 v03
     (lam3 (lam3 (lam3 (app3 (app3 add3 (app3 v13 v03)) v03))))
     (lam3 zero3)).

Definition fact3 {Γ} : Tm3 Γ (arr3 nat3 nat3)
 := lam3 (rec3 v03 (lam3 (lam3 (app3 (app3 mul3 (suc3 v13)) v03)))
        (suc3 zero3)).

Require Import Coq.Unicode.Utf8.

Definition Ty4 : Set
 := ∀ (Ty4           : Set)
      (nat top bot  : Ty4)
      (arr prod sum : Ty4 → Ty4 → Ty4)
    , Ty4.

Definition nat4 : Ty4 := λ _ nat4 _ _ _ _ _ , nat4.
Definition top4 : Ty4 := λ _ _ top4 _ _ _ _ , top4.
Definition bot4 : Ty4 := λ _ _ _ bot4 _ _ _ , bot4.

Definition arr4 : Ty4 → Ty4 → Ty4
 := λ A B Ty4 nat4 top4 bot4 arr4 prod sum ,
     arr4 (A Ty4 nat4 top4 bot4 arr4 prod sum) (B Ty4 nat4 top4 bot4 arr4 prod sum).

Definition prod4 : Ty4 → Ty4 → Ty4
 := λ A B Ty4 nat4 top4 bot4 arr4 prod4 sum ,
     prod4 (A Ty4 nat4 top4 bot4 arr4 prod4 sum) (B Ty4 nat4 top4 bot4 arr4 prod4 sum).

Definition sum4 : Ty4 → Ty4 → Ty4
 := λ A B Ty4 nat4 top4 bot4 arr4 prod4 sum4 ,
     sum4 (A Ty4 nat4 top4 bot4 arr4 prod4 sum4) (B Ty4 nat4 top4 bot4 arr4 prod4 sum4).

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
     (tt    : ∀ Γ       , Tm4 Γ top4)
     (pair  : ∀ Γ A B   , Tm4 Γ A → Tm4 Γ B → Tm4 Γ (prod4 A B))
     (fst   : ∀ Γ A B   , Tm4 Γ (prod4 A B) → Tm4 Γ A)
     (snd   : ∀ Γ A B   , Tm4 Γ (prod4 A B) → Tm4 Γ B)
     (left  : ∀ Γ A B   , Tm4 Γ A → Tm4 Γ (sum4 A B))
     (right : ∀ Γ A B   , Tm4 Γ B → Tm4 Γ (sum4 A B))
     (case  : ∀ Γ A B C , Tm4 Γ (sum4 A B) → Tm4 Γ (arr4 A C) → Tm4 Γ (arr4 B C) → Tm4 Γ C)
     (zero  : ∀ Γ       , Tm4 Γ nat4)
     (suc   : ∀ Γ       , Tm4 Γ nat4 → Tm4 Γ nat4)
     (rec   : ∀ Γ A     , Tm4 Γ nat4 → Tm4 Γ (arr4 nat4 (arr4 A A)) → Tm4 Γ A → Tm4 Γ A)
   , Tm4 Γ A.

Definition var4 {Γ A} : Var4 Γ A → Tm4 Γ A
 := λ x Tm4 var4 lam app tt pair fst snd left right case zero suc rec ,
     var4 _ _ x.

Definition lam4 {Γ A B} : Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B)
 := λ t Tm4 var4 lam4 app tt pair fst snd left right case zero suc rec ,
     lam4 _ _ _ (t Tm4 var4 lam4 app tt pair fst snd left right case zero suc rec).

Definition app4 {Γ A B} : Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B
 := λ t u Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec ,
     app4 _ _ _
         (t Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec)
         (u Tm4 var4 lam4 app4 tt pair fst snd left right case zero suc rec).

Definition tt4 {Γ} : Tm4 Γ top4
 := λ Tm4 var4 lam4 app4 tt4 pair fst snd left right case zero suc rec , tt4 _.

Definition pair4 {Γ A B} : Tm4 Γ A → Tm4 Γ B → Tm4 Γ (prod4 A B)
 := λ t u Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec ,
     pair4 _ _ _
          (t Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec)
          (u Tm4 var4 lam4 app4 tt4 pair4 fst snd left right case zero suc rec).

Definition fst4 {Γ A B} : Tm4 Γ (prod4 A B) → Tm4 Γ A
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd left right case zero suc rec ,
     fst4 _ _ _
         (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd left right case zero suc rec).

Definition snd4 {Γ A B} : Tm4 Γ (prod4 A B) → Tm4 Γ B
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left right case zero suc rec ,
     snd4 _ _ _
          (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left right case zero suc rec).

Definition left4 {Γ A B} : Tm4 Γ A → Tm4 Γ (sum4 A B)
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right case zero suc rec ,
     left4 _ _ _
          (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right case zero suc rec).

Definition right4 {Γ A B} : Tm4 Γ B → Tm4 Γ (sum4 A B)
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case zero suc rec ,
     right4 _ _ _
            (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case zero suc rec).

Definition case4 {Γ A B C} : Tm4 Γ (sum4 A B) → Tm4 Γ (arr4 A C) → Tm4 Γ (arr4 B C) → Tm4 Γ C
 := λ t u v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec ,
     case4 _ _ _ _
           (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)
           (u Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec)
           (v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero suc rec).

Definition zero4  {Γ} : Tm4 Γ nat4
 := λ Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc rec , zero4 _.

Definition suc4 {Γ} : Tm4 Γ nat4 → Tm4 Γ nat4
 := λ t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec ,
   suc4 _ (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec).

Definition rec4 {Γ A} : Tm4 Γ nat4 → Tm4 Γ (arr4 nat4 (arr4 A A)) → Tm4 Γ A → Tm4 Γ A
 := λ t u v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4 ,
     rec4 _ _
         (t Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)
         (u Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4)
         (v Tm4 var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 case4 zero4 suc4 rec4).

Definition v04 {Γ A} : Tm4 (snoc4 Γ A) A
 := var4 vz4.

Definition v14 {Γ A B} : Tm4 (snoc4 (snoc4 Γ A) B) A
 := var4 (vs4 vz4).

Definition v24 {Γ A B C} : Tm4 (snoc4 (snoc4 (snoc4 Γ A) B) C) A
 := var4 (vs4 (vs4 vz4)).

Definition v34 {Γ A B C D} : Tm4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) A
 := var4 (vs4 (vs4 (vs4 vz4))).

Definition tbool4 : Ty4
 := sum4 top4 top4.

Definition ttrue4 {Γ} : Tm4 Γ tbool4
 := left4 tt4.

Definition tfalse4 {Γ} : Tm4 Γ tbool4
 := right4 tt4.

Definition ifthenelse4 {Γ A} : Tm4 Γ (arr4 tbool4 (arr4 A (arr4 A A)))
 := lam4 (lam4 (lam4 (case4 v24 (lam4 v24) (lam4 v14)))).

Definition times44 {Γ A} : Tm4 Γ (arr4 (arr4 A A) (arr4 A A))
  := lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04))))).

Definition add4 {Γ} : Tm4 Γ (arr4 nat4 (arr4 nat4 nat4))
 := lam4 (rec4 v04
      (lam4 (lam4 (lam4 (suc4 (app4 v14 v04)))))
      (lam4 v04)).

Definition mul4 {Γ} : Tm4 Γ (arr4 nat4 (arr4 nat4 nat4))
 := lam4 (rec4 v04
     (lam4 (lam4 (lam4 (app4 (app4 add4 (app4 v14 v04)) v04))))
     (lam4 zero4)).

Definition fact4 {Γ} : Tm4 Γ (arr4 nat4 nat4)
 := lam4 (rec4 v04 (lam4 (lam4 (app4 (app4 mul4 (suc4 v14)) v04)))
        (suc4 zero4)).

Require Import Coq.Unicode.Utf8.

Definition Ty5 : Set
 := ∀ (Ty5           : Set)
      (nat top bot  : Ty5)
      (arr prod sum : Ty5 → Ty5 → Ty5)
    , Ty5.

Definition nat5 : Ty5 := λ _ nat5 _ _ _ _ _ , nat5.
Definition top5 : Ty5 := λ _ _ top5 _ _ _ _ , top5.
Definition bot5 : Ty5 := λ _ _ _ bot5 _ _ _ , bot5.

Definition arr5 : Ty5 → Ty5 → Ty5
 := λ A B Ty5 nat5 top5 bot5 arr5 prod sum ,
     arr5 (A Ty5 nat5 top5 bot5 arr5 prod sum) (B Ty5 nat5 top5 bot5 arr5 prod sum).

Definition prod5 : Ty5 → Ty5 → Ty5
 := λ A B Ty5 nat5 top5 bot5 arr5 prod5 sum ,
     prod5 (A Ty5 nat5 top5 bot5 arr5 prod5 sum) (B Ty5 nat5 top5 bot5 arr5 prod5 sum).

Definition sum5 : Ty5 → Ty5 → Ty5
 := λ A B Ty5 nat5 top5 bot5 arr5 prod5 sum5 ,
     sum5 (A Ty5 nat5 top5 bot5 arr5 prod5 sum5) (B Ty5 nat5 top5 bot5 arr5 prod5 sum5).

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
     (tt    : ∀ Γ       , Tm5 Γ top5)
     (pair  : ∀ Γ A B   , Tm5 Γ A → Tm5 Γ B → Tm5 Γ (prod5 A B))
     (fst   : ∀ Γ A B   , Tm5 Γ (prod5 A B) → Tm5 Γ A)
     (snd   : ∀ Γ A B   , Tm5 Γ (prod5 A B) → Tm5 Γ B)
     (left  : ∀ Γ A B   , Tm5 Γ A → Tm5 Γ (sum5 A B))
     (right : ∀ Γ A B   , Tm5 Γ B → Tm5 Γ (sum5 A B))
     (case  : ∀ Γ A B C , Tm5 Γ (sum5 A B) → Tm5 Γ (arr5 A C) → Tm5 Γ (arr5 B C) → Tm5 Γ C)
     (zero  : ∀ Γ       , Tm5 Γ nat5)
     (suc   : ∀ Γ       , Tm5 Γ nat5 → Tm5 Γ nat5)
     (rec   : ∀ Γ A     , Tm5 Γ nat5 → Tm5 Γ (arr5 nat5 (arr5 A A)) → Tm5 Γ A → Tm5 Γ A)
   , Tm5 Γ A.

Definition var5 {Γ A} : Var5 Γ A → Tm5 Γ A
 := λ x Tm5 var5 lam app tt pair fst snd left right case zero suc rec ,
     var5 _ _ x.

Definition lam5 {Γ A B} : Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B)
 := λ t Tm5 var5 lam5 app tt pair fst snd left right case zero suc rec ,
     lam5 _ _ _ (t Tm5 var5 lam5 app tt pair fst snd left right case zero suc rec).

Definition app5 {Γ A B} : Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B
 := λ t u Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec ,
     app5 _ _ _
         (t Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec)
         (u Tm5 var5 lam5 app5 tt pair fst snd left right case zero suc rec).

Definition tt5 {Γ} : Tm5 Γ top5
 := λ Tm5 var5 lam5 app5 tt5 pair fst snd left right case zero suc rec , tt5 _.

Definition pair5 {Γ A B} : Tm5 Γ A → Tm5 Γ B → Tm5 Γ (prod5 A B)
 := λ t u Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec ,
     pair5 _ _ _
          (t Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec)
          (u Tm5 var5 lam5 app5 tt5 pair5 fst snd left right case zero suc rec).

Definition fst5 {Γ A B} : Tm5 Γ (prod5 A B) → Tm5 Γ A
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd left right case zero suc rec ,
     fst5 _ _ _
         (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd left right case zero suc rec).

Definition snd5 {Γ A B} : Tm5 Γ (prod5 A B) → Tm5 Γ B
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left right case zero suc rec ,
     snd5 _ _ _
          (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left right case zero suc rec).

Definition left5 {Γ A B} : Tm5 Γ A → Tm5 Γ (sum5 A B)
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right case zero suc rec ,
     left5 _ _ _
          (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right case zero suc rec).

Definition right5 {Γ A B} : Tm5 Γ B → Tm5 Γ (sum5 A B)
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case zero suc rec ,
     right5 _ _ _
            (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case zero suc rec).

Definition case5 {Γ A B C} : Tm5 Γ (sum5 A B) → Tm5 Γ (arr5 A C) → Tm5 Γ (arr5 B C) → Tm5 Γ C
 := λ t u v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec ,
     case5 _ _ _ _
           (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)
           (u Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec)
           (v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero suc rec).

Definition zero5  {Γ} : Tm5 Γ nat5
 := λ Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc rec , zero5 _.

Definition suc5 {Γ} : Tm5 Γ nat5 → Tm5 Γ nat5
 := λ t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec ,
   suc5 _ (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec).

Definition rec5 {Γ A} : Tm5 Γ nat5 → Tm5 Γ (arr5 nat5 (arr5 A A)) → Tm5 Γ A → Tm5 Γ A
 := λ t u v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5 ,
     rec5 _ _
         (t Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)
         (u Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5)
         (v Tm5 var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 case5 zero5 suc5 rec5).

Definition v05 {Γ A} : Tm5 (snoc5 Γ A) A
 := var5 vz5.

Definition v15 {Γ A B} : Tm5 (snoc5 (snoc5 Γ A) B) A
 := var5 (vs5 vz5).

Definition v25 {Γ A B C} : Tm5 (snoc5 (snoc5 (snoc5 Γ A) B) C) A
 := var5 (vs5 (vs5 vz5)).

Definition v35 {Γ A B C D} : Tm5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) A
 := var5 (vs5 (vs5 (vs5 vz5))).

Definition tbool5 : Ty5
 := sum5 top5 top5.

Definition ttrue5 {Γ} : Tm5 Γ tbool5
 := left5 tt5.

Definition tfalse5 {Γ} : Tm5 Γ tbool5
 := right5 tt5.

Definition ifthenelse5 {Γ A} : Tm5 Γ (arr5 tbool5 (arr5 A (arr5 A A)))
 := lam5 (lam5 (lam5 (case5 v25 (lam5 v25) (lam5 v15)))).

Definition times45 {Γ A} : Tm5 Γ (arr5 (arr5 A A) (arr5 A A))
  := lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05))))).

Definition add5 {Γ} : Tm5 Γ (arr5 nat5 (arr5 nat5 nat5))
 := lam5 (rec5 v05
      (lam5 (lam5 (lam5 (suc5 (app5 v15 v05)))))
      (lam5 v05)).

Definition mul5 {Γ} : Tm5 Γ (arr5 nat5 (arr5 nat5 nat5))
 := lam5 (rec5 v05
     (lam5 (lam5 (lam5 (app5 (app5 add5 (app5 v15 v05)) v05))))
     (lam5 zero5)).

Definition fact5 {Γ} : Tm5 Γ (arr5 nat5 nat5)
 := lam5 (rec5 v05 (lam5 (lam5 (app5 (app5 mul5 (suc5 v15)) v05)))
        (suc5 zero5)).

Require Import Coq.Unicode.Utf8.

Definition Ty6 : Set
 := ∀ (Ty6           : Set)
      (nat top bot  : Ty6)
      (arr prod sum : Ty6 → Ty6 → Ty6)
    , Ty6.

Definition nat6 : Ty6 := λ _ nat6 _ _ _ _ _ , nat6.
Definition top6 : Ty6 := λ _ _ top6 _ _ _ _ , top6.
Definition bot6 : Ty6 := λ _ _ _ bot6 _ _ _ , bot6.

Definition arr6 : Ty6 → Ty6 → Ty6
 := λ A B Ty6 nat6 top6 bot6 arr6 prod sum ,
     arr6 (A Ty6 nat6 top6 bot6 arr6 prod sum) (B Ty6 nat6 top6 bot6 arr6 prod sum).

Definition prod6 : Ty6 → Ty6 → Ty6
 := λ A B Ty6 nat6 top6 bot6 arr6 prod6 sum ,
     prod6 (A Ty6 nat6 top6 bot6 arr6 prod6 sum) (B Ty6 nat6 top6 bot6 arr6 prod6 sum).

Definition sum6 : Ty6 → Ty6 → Ty6
 := λ A B Ty6 nat6 top6 bot6 arr6 prod6 sum6 ,
     sum6 (A Ty6 nat6 top6 bot6 arr6 prod6 sum6) (B Ty6 nat6 top6 bot6 arr6 prod6 sum6).

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
     (tt    : ∀ Γ       , Tm6 Γ top6)
     (pair  : ∀ Γ A B   , Tm6 Γ A → Tm6 Γ B → Tm6 Γ (prod6 A B))
     (fst   : ∀ Γ A B   , Tm6 Γ (prod6 A B) → Tm6 Γ A)
     (snd   : ∀ Γ A B   , Tm6 Γ (prod6 A B) → Tm6 Γ B)
     (left  : ∀ Γ A B   , Tm6 Γ A → Tm6 Γ (sum6 A B))
     (right : ∀ Γ A B   , Tm6 Γ B → Tm6 Γ (sum6 A B))
     (case  : ∀ Γ A B C , Tm6 Γ (sum6 A B) → Tm6 Γ (arr6 A C) → Tm6 Γ (arr6 B C) → Tm6 Γ C)
     (zero  : ∀ Γ       , Tm6 Γ nat6)
     (suc   : ∀ Γ       , Tm6 Γ nat6 → Tm6 Γ nat6)
     (rec   : ∀ Γ A     , Tm6 Γ nat6 → Tm6 Γ (arr6 nat6 (arr6 A A)) → Tm6 Γ A → Tm6 Γ A)
   , Tm6 Γ A.

Definition var6 {Γ A} : Var6 Γ A → Tm6 Γ A
 := λ x Tm6 var6 lam app tt pair fst snd left right case zero suc rec ,
     var6 _ _ x.

Definition lam6 {Γ A B} : Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B)
 := λ t Tm6 var6 lam6 app tt pair fst snd left right case zero suc rec ,
     lam6 _ _ _ (t Tm6 var6 lam6 app tt pair fst snd left right case zero suc rec).

Definition app6 {Γ A B} : Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B
 := λ t u Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec ,
     app6 _ _ _
         (t Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec)
         (u Tm6 var6 lam6 app6 tt pair fst snd left right case zero suc rec).

Definition tt6 {Γ} : Tm6 Γ top6
 := λ Tm6 var6 lam6 app6 tt6 pair fst snd left right case zero suc rec , tt6 _.

Definition pair6 {Γ A B} : Tm6 Γ A → Tm6 Γ B → Tm6 Γ (prod6 A B)
 := λ t u Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec ,
     pair6 _ _ _
          (t Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec)
          (u Tm6 var6 lam6 app6 tt6 pair6 fst snd left right case zero suc rec).

Definition fst6 {Γ A B} : Tm6 Γ (prod6 A B) → Tm6 Γ A
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd left right case zero suc rec ,
     fst6 _ _ _
         (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd left right case zero suc rec).

Definition snd6 {Γ A B} : Tm6 Γ (prod6 A B) → Tm6 Γ B
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left right case zero suc rec ,
     snd6 _ _ _
          (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left right case zero suc rec).

Definition left6 {Γ A B} : Tm6 Γ A → Tm6 Γ (sum6 A B)
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right case zero suc rec ,
     left6 _ _ _
          (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right case zero suc rec).

Definition right6 {Γ A B} : Tm6 Γ B → Tm6 Γ (sum6 A B)
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case zero suc rec ,
     right6 _ _ _
            (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case zero suc rec).

Definition case6 {Γ A B C} : Tm6 Γ (sum6 A B) → Tm6 Γ (arr6 A C) → Tm6 Γ (arr6 B C) → Tm6 Γ C
 := λ t u v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec ,
     case6 _ _ _ _
           (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)
           (u Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec)
           (v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero suc rec).

Definition zero6  {Γ} : Tm6 Γ nat6
 := λ Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc rec , zero6 _.

Definition suc6 {Γ} : Tm6 Γ nat6 → Tm6 Γ nat6
 := λ t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec ,
   suc6 _ (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec).

Definition rec6 {Γ A} : Tm6 Γ nat6 → Tm6 Γ (arr6 nat6 (arr6 A A)) → Tm6 Γ A → Tm6 Γ A
 := λ t u v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6 ,
     rec6 _ _
         (t Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)
         (u Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6)
         (v Tm6 var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 case6 zero6 suc6 rec6).

Definition v06 {Γ A} : Tm6 (snoc6 Γ A) A
 := var6 vz6.

Definition v16 {Γ A B} : Tm6 (snoc6 (snoc6 Γ A) B) A
 := var6 (vs6 vz6).

Definition v26 {Γ A B C} : Tm6 (snoc6 (snoc6 (snoc6 Γ A) B) C) A
 := var6 (vs6 (vs6 vz6)).

Definition v36 {Γ A B C D} : Tm6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) A
 := var6 (vs6 (vs6 (vs6 vz6))).

Definition tbool6 : Ty6
 := sum6 top6 top6.

Definition ttrue6 {Γ} : Tm6 Γ tbool6
 := left6 tt6.

Definition tfalse6 {Γ} : Tm6 Γ tbool6
 := right6 tt6.

Definition ifthenelse6 {Γ A} : Tm6 Γ (arr6 tbool6 (arr6 A (arr6 A A)))
 := lam6 (lam6 (lam6 (case6 v26 (lam6 v26) (lam6 v16)))).

Definition times46 {Γ A} : Tm6 Γ (arr6 (arr6 A A) (arr6 A A))
  := lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06))))).

Definition add6 {Γ} : Tm6 Γ (arr6 nat6 (arr6 nat6 nat6))
 := lam6 (rec6 v06
      (lam6 (lam6 (lam6 (suc6 (app6 v16 v06)))))
      (lam6 v06)).

Definition mul6 {Γ} : Tm6 Γ (arr6 nat6 (arr6 nat6 nat6))
 := lam6 (rec6 v06
     (lam6 (lam6 (lam6 (app6 (app6 add6 (app6 v16 v06)) v06))))
     (lam6 zero6)).

Definition fact6 {Γ} : Tm6 Γ (arr6 nat6 nat6)
 := lam6 (rec6 v06 (lam6 (lam6 (app6 (app6 mul6 (suc6 v16)) v06)))
        (suc6 zero6)).

Require Import Coq.Unicode.Utf8.

Definition Ty7 : Set
 := ∀ (Ty7           : Set)
      (nat top bot  : Ty7)
      (arr prod sum : Ty7 → Ty7 → Ty7)
    , Ty7.

Definition nat7 : Ty7 := λ _ nat7 _ _ _ _ _ , nat7.
Definition top7 : Ty7 := λ _ _ top7 _ _ _ _ , top7.
Definition bot7 : Ty7 := λ _ _ _ bot7 _ _ _ , bot7.

Definition arr7 : Ty7 → Ty7 → Ty7
 := λ A B Ty7 nat7 top7 bot7 arr7 prod sum ,
     arr7 (A Ty7 nat7 top7 bot7 arr7 prod sum) (B Ty7 nat7 top7 bot7 arr7 prod sum).

Definition prod7 : Ty7 → Ty7 → Ty7
 := λ A B Ty7 nat7 top7 bot7 arr7 prod7 sum ,
     prod7 (A Ty7 nat7 top7 bot7 arr7 prod7 sum) (B Ty7 nat7 top7 bot7 arr7 prod7 sum).

Definition sum7 : Ty7 → Ty7 → Ty7
 := λ A B Ty7 nat7 top7 bot7 arr7 prod7 sum7 ,
     sum7 (A Ty7 nat7 top7 bot7 arr7 prod7 sum7) (B Ty7 nat7 top7 bot7 arr7 prod7 sum7).

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
     (tt    : ∀ Γ       , Tm7 Γ top7)
     (pair  : ∀ Γ A B   , Tm7 Γ A → Tm7 Γ B → Tm7 Γ (prod7 A B))
     (fst   : ∀ Γ A B   , Tm7 Γ (prod7 A B) → Tm7 Γ A)
     (snd   : ∀ Γ A B   , Tm7 Γ (prod7 A B) → Tm7 Γ B)
     (left  : ∀ Γ A B   , Tm7 Γ A → Tm7 Γ (sum7 A B))
     (right : ∀ Γ A B   , Tm7 Γ B → Tm7 Γ (sum7 A B))
     (case  : ∀ Γ A B C , Tm7 Γ (sum7 A B) → Tm7 Γ (arr7 A C) → Tm7 Γ (arr7 B C) → Tm7 Γ C)
     (zero  : ∀ Γ       , Tm7 Γ nat7)
     (suc   : ∀ Γ       , Tm7 Γ nat7 → Tm7 Γ nat7)
     (rec   : ∀ Γ A     , Tm7 Γ nat7 → Tm7 Γ (arr7 nat7 (arr7 A A)) → Tm7 Γ A → Tm7 Γ A)
   , Tm7 Γ A.

Definition var7 {Γ A} : Var7 Γ A → Tm7 Γ A
 := λ x Tm7 var7 lam app tt pair fst snd left right case zero suc rec ,
     var7 _ _ x.

Definition lam7 {Γ A B} : Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B)
 := λ t Tm7 var7 lam7 app tt pair fst snd left right case zero suc rec ,
     lam7 _ _ _ (t Tm7 var7 lam7 app tt pair fst snd left right case zero suc rec).

Definition app7 {Γ A B} : Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B
 := λ t u Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec ,
     app7 _ _ _
         (t Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec)
         (u Tm7 var7 lam7 app7 tt pair fst snd left right case zero suc rec).

Definition tt7 {Γ} : Tm7 Γ top7
 := λ Tm7 var7 lam7 app7 tt7 pair fst snd left right case zero suc rec , tt7 _.

Definition pair7 {Γ A B} : Tm7 Γ A → Tm7 Γ B → Tm7 Γ (prod7 A B)
 := λ t u Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec ,
     pair7 _ _ _
          (t Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec)
          (u Tm7 var7 lam7 app7 tt7 pair7 fst snd left right case zero suc rec).

Definition fst7 {Γ A B} : Tm7 Γ (prod7 A B) → Tm7 Γ A
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd left right case zero suc rec ,
     fst7 _ _ _
         (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd left right case zero suc rec).

Definition snd7 {Γ A B} : Tm7 Γ (prod7 A B) → Tm7 Γ B
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left right case zero suc rec ,
     snd7 _ _ _
          (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left right case zero suc rec).

Definition left7 {Γ A B} : Tm7 Γ A → Tm7 Γ (sum7 A B)
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right case zero suc rec ,
     left7 _ _ _
          (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right case zero suc rec).

Definition right7 {Γ A B} : Tm7 Γ B → Tm7 Γ (sum7 A B)
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case zero suc rec ,
     right7 _ _ _
            (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case zero suc rec).

Definition case7 {Γ A B C} : Tm7 Γ (sum7 A B) → Tm7 Γ (arr7 A C) → Tm7 Γ (arr7 B C) → Tm7 Γ C
 := λ t u v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec ,
     case7 _ _ _ _
           (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)
           (u Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec)
           (v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero suc rec).

Definition zero7  {Γ} : Tm7 Γ nat7
 := λ Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc rec , zero7 _.

Definition suc7 {Γ} : Tm7 Γ nat7 → Tm7 Γ nat7
 := λ t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec ,
   suc7 _ (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec).

Definition rec7 {Γ A} : Tm7 Γ nat7 → Tm7 Γ (arr7 nat7 (arr7 A A)) → Tm7 Γ A → Tm7 Γ A
 := λ t u v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7 ,
     rec7 _ _
         (t Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)
         (u Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7)
         (v Tm7 var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 case7 zero7 suc7 rec7).

Definition v07 {Γ A} : Tm7 (snoc7 Γ A) A
 := var7 vz7.

Definition v17 {Γ A B} : Tm7 (snoc7 (snoc7 Γ A) B) A
 := var7 (vs7 vz7).

Definition v27 {Γ A B C} : Tm7 (snoc7 (snoc7 (snoc7 Γ A) B) C) A
 := var7 (vs7 (vs7 vz7)).

Definition v37 {Γ A B C D} : Tm7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) A
 := var7 (vs7 (vs7 (vs7 vz7))).

Definition tbool7 : Ty7
 := sum7 top7 top7.

Definition ttrue7 {Γ} : Tm7 Γ tbool7
 := left7 tt7.

Definition tfalse7 {Γ} : Tm7 Γ tbool7
 := right7 tt7.

Definition ifthenelse7 {Γ A} : Tm7 Γ (arr7 tbool7 (arr7 A (arr7 A A)))
 := lam7 (lam7 (lam7 (case7 v27 (lam7 v27) (lam7 v17)))).

Definition times47 {Γ A} : Tm7 Γ (arr7 (arr7 A A) (arr7 A A))
  := lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07))))).

Definition add7 {Γ} : Tm7 Γ (arr7 nat7 (arr7 nat7 nat7))
 := lam7 (rec7 v07
      (lam7 (lam7 (lam7 (suc7 (app7 v17 v07)))))
      (lam7 v07)).

Definition mul7 {Γ} : Tm7 Γ (arr7 nat7 (arr7 nat7 nat7))
 := lam7 (rec7 v07
     (lam7 (lam7 (lam7 (app7 (app7 add7 (app7 v17 v07)) v07))))
     (lam7 zero7)).

Definition fact7 {Γ} : Tm7 Γ (arr7 nat7 nat7)
 := lam7 (rec7 v07 (lam7 (lam7 (app7 (app7 mul7 (suc7 v17)) v07)))
        (suc7 zero7)).

Require Import Coq.Unicode.Utf8.

Definition Ty8 : Set
 := ∀ (Ty8           : Set)
      (nat top bot  : Ty8)
      (arr prod sum : Ty8 → Ty8 → Ty8)
    , Ty8.

Definition nat8 : Ty8 := λ _ nat8 _ _ _ _ _ , nat8.
Definition top8 : Ty8 := λ _ _ top8 _ _ _ _ , top8.
Definition bot8 : Ty8 := λ _ _ _ bot8 _ _ _ , bot8.

Definition arr8 : Ty8 → Ty8 → Ty8
 := λ A B Ty8 nat8 top8 bot8 arr8 prod sum ,
     arr8 (A Ty8 nat8 top8 bot8 arr8 prod sum) (B Ty8 nat8 top8 bot8 arr8 prod sum).

Definition prod8 : Ty8 → Ty8 → Ty8
 := λ A B Ty8 nat8 top8 bot8 arr8 prod8 sum ,
     prod8 (A Ty8 nat8 top8 bot8 arr8 prod8 sum) (B Ty8 nat8 top8 bot8 arr8 prod8 sum).

Definition sum8 : Ty8 → Ty8 → Ty8
 := λ A B Ty8 nat8 top8 bot8 arr8 prod8 sum8 ,
     sum8 (A Ty8 nat8 top8 bot8 arr8 prod8 sum8) (B Ty8 nat8 top8 bot8 arr8 prod8 sum8).

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
     (tt    : ∀ Γ       , Tm8 Γ top8)
     (pair  : ∀ Γ A B   , Tm8 Γ A → Tm8 Γ B → Tm8 Γ (prod8 A B))
     (fst   : ∀ Γ A B   , Tm8 Γ (prod8 A B) → Tm8 Γ A)
     (snd   : ∀ Γ A B   , Tm8 Γ (prod8 A B) → Tm8 Γ B)
     (left  : ∀ Γ A B   , Tm8 Γ A → Tm8 Γ (sum8 A B))
     (right : ∀ Γ A B   , Tm8 Γ B → Tm8 Γ (sum8 A B))
     (case  : ∀ Γ A B C , Tm8 Γ (sum8 A B) → Tm8 Γ (arr8 A C) → Tm8 Γ (arr8 B C) → Tm8 Γ C)
     (zero  : ∀ Γ       , Tm8 Γ nat8)
     (suc   : ∀ Γ       , Tm8 Γ nat8 → Tm8 Γ nat8)
     (rec   : ∀ Γ A     , Tm8 Γ nat8 → Tm8 Γ (arr8 nat8 (arr8 A A)) → Tm8 Γ A → Tm8 Γ A)
   , Tm8 Γ A.

Definition var8 {Γ A} : Var8 Γ A → Tm8 Γ A
 := λ x Tm8 var8 lam app tt pair fst snd left right case zero suc rec ,
     var8 _ _ x.

Definition lam8 {Γ A B} : Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B)
 := λ t Tm8 var8 lam8 app tt pair fst snd left right case zero suc rec ,
     lam8 _ _ _ (t Tm8 var8 lam8 app tt pair fst snd left right case zero suc rec).

Definition app8 {Γ A B} : Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B
 := λ t u Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec ,
     app8 _ _ _
         (t Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec)
         (u Tm8 var8 lam8 app8 tt pair fst snd left right case zero suc rec).

Definition tt8 {Γ} : Tm8 Γ top8
 := λ Tm8 var8 lam8 app8 tt8 pair fst snd left right case zero suc rec , tt8 _.

Definition pair8 {Γ A B} : Tm8 Γ A → Tm8 Γ B → Tm8 Γ (prod8 A B)
 := λ t u Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec ,
     pair8 _ _ _
          (t Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec)
          (u Tm8 var8 lam8 app8 tt8 pair8 fst snd left right case zero suc rec).

Definition fst8 {Γ A B} : Tm8 Γ (prod8 A B) → Tm8 Γ A
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd left right case zero suc rec ,
     fst8 _ _ _
         (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd left right case zero suc rec).

Definition snd8 {Γ A B} : Tm8 Γ (prod8 A B) → Tm8 Γ B
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left right case zero suc rec ,
     snd8 _ _ _
          (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left right case zero suc rec).

Definition left8 {Γ A B} : Tm8 Γ A → Tm8 Γ (sum8 A B)
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right case zero suc rec ,
     left8 _ _ _
          (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right case zero suc rec).

Definition right8 {Γ A B} : Tm8 Γ B → Tm8 Γ (sum8 A B)
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case zero suc rec ,
     right8 _ _ _
            (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case zero suc rec).

Definition case8 {Γ A B C} : Tm8 Γ (sum8 A B) → Tm8 Γ (arr8 A C) → Tm8 Γ (arr8 B C) → Tm8 Γ C
 := λ t u v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec ,
     case8 _ _ _ _
           (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)
           (u Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec)
           (v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero suc rec).

Definition zero8  {Γ} : Tm8 Γ nat8
 := λ Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc rec , zero8 _.

Definition suc8 {Γ} : Tm8 Γ nat8 → Tm8 Γ nat8
 := λ t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec ,
   suc8 _ (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec).

Definition rec8 {Γ A} : Tm8 Γ nat8 → Tm8 Γ (arr8 nat8 (arr8 A A)) → Tm8 Γ A → Tm8 Γ A
 := λ t u v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8 ,
     rec8 _ _
         (t Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)
         (u Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8)
         (v Tm8 var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 case8 zero8 suc8 rec8).

Definition v08 {Γ A} : Tm8 (snoc8 Γ A) A
 := var8 vz8.

Definition v18 {Γ A B} : Tm8 (snoc8 (snoc8 Γ A) B) A
 := var8 (vs8 vz8).

Definition v28 {Γ A B C} : Tm8 (snoc8 (snoc8 (snoc8 Γ A) B) C) A
 := var8 (vs8 (vs8 vz8)).

Definition v38 {Γ A B C D} : Tm8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) A
 := var8 (vs8 (vs8 (vs8 vz8))).

Definition tbool8 : Ty8
 := sum8 top8 top8.

Definition ttrue8 {Γ} : Tm8 Γ tbool8
 := left8 tt8.

Definition tfalse8 {Γ} : Tm8 Γ tbool8
 := right8 tt8.

Definition ifthenelse8 {Γ A} : Tm8 Γ (arr8 tbool8 (arr8 A (arr8 A A)))
 := lam8 (lam8 (lam8 (case8 v28 (lam8 v28) (lam8 v18)))).

Definition times48 {Γ A} : Tm8 Γ (arr8 (arr8 A A) (arr8 A A))
  := lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08))))).

Definition add8 {Γ} : Tm8 Γ (arr8 nat8 (arr8 nat8 nat8))
 := lam8 (rec8 v08
      (lam8 (lam8 (lam8 (suc8 (app8 v18 v08)))))
      (lam8 v08)).

Definition mul8 {Γ} : Tm8 Γ (arr8 nat8 (arr8 nat8 nat8))
 := lam8 (rec8 v08
     (lam8 (lam8 (lam8 (app8 (app8 add8 (app8 v18 v08)) v08))))
     (lam8 zero8)).

Definition fact8 {Γ} : Tm8 Γ (arr8 nat8 nat8)
 := lam8 (rec8 v08 (lam8 (lam8 (app8 (app8 mul8 (suc8 v18)) v08)))
        (suc8 zero8)).

Require Import Coq.Unicode.Utf8.

Definition Ty9 : Set
 := ∀ (Ty9           : Set)
      (nat top bot  : Ty9)
      (arr prod sum : Ty9 → Ty9 → Ty9)
    , Ty9.

Definition nat9 : Ty9 := λ _ nat9 _ _ _ _ _ , nat9.
Definition top9 : Ty9 := λ _ _ top9 _ _ _ _ , top9.
Definition bot9 : Ty9 := λ _ _ _ bot9 _ _ _ , bot9.

Definition arr9 : Ty9 → Ty9 → Ty9
 := λ A B Ty9 nat9 top9 bot9 arr9 prod sum ,
     arr9 (A Ty9 nat9 top9 bot9 arr9 prod sum) (B Ty9 nat9 top9 bot9 arr9 prod sum).

Definition prod9 : Ty9 → Ty9 → Ty9
 := λ A B Ty9 nat9 top9 bot9 arr9 prod9 sum ,
     prod9 (A Ty9 nat9 top9 bot9 arr9 prod9 sum) (B Ty9 nat9 top9 bot9 arr9 prod9 sum).

Definition sum9 : Ty9 → Ty9 → Ty9
 := λ A B Ty9 nat9 top9 bot9 arr9 prod9 sum9 ,
     sum9 (A Ty9 nat9 top9 bot9 arr9 prod9 sum9) (B Ty9 nat9 top9 bot9 arr9 prod9 sum9).

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
     (tt    : ∀ Γ       , Tm9 Γ top9)
     (pair  : ∀ Γ A B   , Tm9 Γ A → Tm9 Γ B → Tm9 Γ (prod9 A B))
     (fst   : ∀ Γ A B   , Tm9 Γ (prod9 A B) → Tm9 Γ A)
     (snd   : ∀ Γ A B   , Tm9 Γ (prod9 A B) → Tm9 Γ B)
     (left  : ∀ Γ A B   , Tm9 Γ A → Tm9 Γ (sum9 A B))
     (right : ∀ Γ A B   , Tm9 Γ B → Tm9 Γ (sum9 A B))
     (case  : ∀ Γ A B C , Tm9 Γ (sum9 A B) → Tm9 Γ (arr9 A C) → Tm9 Γ (arr9 B C) → Tm9 Γ C)
     (zero  : ∀ Γ       , Tm9 Γ nat9)
     (suc   : ∀ Γ       , Tm9 Γ nat9 → Tm9 Γ nat9)
     (rec   : ∀ Γ A     , Tm9 Γ nat9 → Tm9 Γ (arr9 nat9 (arr9 A A)) → Tm9 Γ A → Tm9 Γ A)
   , Tm9 Γ A.

Definition var9 {Γ A} : Var9 Γ A → Tm9 Γ A
 := λ x Tm9 var9 lam app tt pair fst snd left right case zero suc rec ,
     var9 _ _ x.

Definition lam9 {Γ A B} : Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B)
 := λ t Tm9 var9 lam9 app tt pair fst snd left right case zero suc rec ,
     lam9 _ _ _ (t Tm9 var9 lam9 app tt pair fst snd left right case zero suc rec).

Definition app9 {Γ A B} : Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B
 := λ t u Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec ,
     app9 _ _ _
         (t Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec)
         (u Tm9 var9 lam9 app9 tt pair fst snd left right case zero suc rec).

Definition tt9 {Γ} : Tm9 Γ top9
 := λ Tm9 var9 lam9 app9 tt9 pair fst snd left right case zero suc rec , tt9 _.

Definition pair9 {Γ A B} : Tm9 Γ A → Tm9 Γ B → Tm9 Γ (prod9 A B)
 := λ t u Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec ,
     pair9 _ _ _
          (t Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec)
          (u Tm9 var9 lam9 app9 tt9 pair9 fst snd left right case zero suc rec).

Definition fst9 {Γ A B} : Tm9 Γ (prod9 A B) → Tm9 Γ A
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd left right case zero suc rec ,
     fst9 _ _ _
         (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd left right case zero suc rec).

Definition snd9 {Γ A B} : Tm9 Γ (prod9 A B) → Tm9 Γ B
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left right case zero suc rec ,
     snd9 _ _ _
          (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left right case zero suc rec).

Definition left9 {Γ A B} : Tm9 Γ A → Tm9 Γ (sum9 A B)
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right case zero suc rec ,
     left9 _ _ _
          (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right case zero suc rec).

Definition right9 {Γ A B} : Tm9 Γ B → Tm9 Γ (sum9 A B)
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case zero suc rec ,
     right9 _ _ _
            (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case zero suc rec).

Definition case9 {Γ A B C} : Tm9 Γ (sum9 A B) → Tm9 Γ (arr9 A C) → Tm9 Γ (arr9 B C) → Tm9 Γ C
 := λ t u v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec ,
     case9 _ _ _ _
           (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)
           (u Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec)
           (v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero suc rec).

Definition zero9  {Γ} : Tm9 Γ nat9
 := λ Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc rec , zero9 _.

Definition suc9 {Γ} : Tm9 Γ nat9 → Tm9 Γ nat9
 := λ t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec ,
   suc9 _ (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec).

Definition rec9 {Γ A} : Tm9 Γ nat9 → Tm9 Γ (arr9 nat9 (arr9 A A)) → Tm9 Γ A → Tm9 Γ A
 := λ t u v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9 ,
     rec9 _ _
         (t Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)
         (u Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9)
         (v Tm9 var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 case9 zero9 suc9 rec9).

Definition v09 {Γ A} : Tm9 (snoc9 Γ A) A
 := var9 vz9.

Definition v19 {Γ A B} : Tm9 (snoc9 (snoc9 Γ A) B) A
 := var9 (vs9 vz9).

Definition v29 {Γ A B C} : Tm9 (snoc9 (snoc9 (snoc9 Γ A) B) C) A
 := var9 (vs9 (vs9 vz9)).

Definition v39 {Γ A B C D} : Tm9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) A
 := var9 (vs9 (vs9 (vs9 vz9))).

Definition tbool9 : Ty9
 := sum9 top9 top9.

Definition ttrue9 {Γ} : Tm9 Γ tbool9
 := left9 tt9.

Definition tfalse9 {Γ} : Tm9 Γ tbool9
 := right9 tt9.

Definition ifthenelse9 {Γ A} : Tm9 Γ (arr9 tbool9 (arr9 A (arr9 A A)))
 := lam9 (lam9 (lam9 (case9 v29 (lam9 v29) (lam9 v19)))).

Definition times49 {Γ A} : Tm9 Γ (arr9 (arr9 A A) (arr9 A A))
  := lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09))))).

Definition add9 {Γ} : Tm9 Γ (arr9 nat9 (arr9 nat9 nat9))
 := lam9 (rec9 v09
      (lam9 (lam9 (lam9 (suc9 (app9 v19 v09)))))
      (lam9 v09)).

Definition mul9 {Γ} : Tm9 Γ (arr9 nat9 (arr9 nat9 nat9))
 := lam9 (rec9 v09
     (lam9 (lam9 (lam9 (app9 (app9 add9 (app9 v19 v09)) v09))))
     (lam9 zero9)).

Definition fact9 {Γ} : Tm9 Γ (arr9 nat9 nat9)
 := lam9 (rec9 v09 (lam9 (lam9 (app9 (app9 mul9 (suc9 v19)) v09)))
        (suc9 zero9)).

Require Import Coq.Unicode.Utf8.

Definition Ty10 : Set
 := ∀ (Ty10           : Set)
      (nat top bot  : Ty10)
      (arr prod sum : Ty10 → Ty10 → Ty10)
    , Ty10.

Definition nat10 : Ty10 := λ _ nat10 _ _ _ _ _ , nat10.
Definition top10 : Ty10 := λ _ _ top10 _ _ _ _ , top10.
Definition bot10 : Ty10 := λ _ _ _ bot10 _ _ _ , bot10.

Definition arr10 : Ty10 → Ty10 → Ty10
 := λ A B Ty10 nat10 top10 bot10 arr10 prod sum ,
     arr10 (A Ty10 nat10 top10 bot10 arr10 prod sum) (B Ty10 nat10 top10 bot10 arr10 prod sum).

Definition prod10 : Ty10 → Ty10 → Ty10
 := λ A B Ty10 nat10 top10 bot10 arr10 prod10 sum ,
     prod10 (A Ty10 nat10 top10 bot10 arr10 prod10 sum) (B Ty10 nat10 top10 bot10 arr10 prod10 sum).

Definition sum10 : Ty10 → Ty10 → Ty10
 := λ A B Ty10 nat10 top10 bot10 arr10 prod10 sum10 ,
     sum10 (A Ty10 nat10 top10 bot10 arr10 prod10 sum10) (B Ty10 nat10 top10 bot10 arr10 prod10 sum10).

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
     (tt    : ∀ Γ       , Tm10 Γ top10)
     (pair  : ∀ Γ A B   , Tm10 Γ A → Tm10 Γ B → Tm10 Γ (prod10 A B))
     (fst   : ∀ Γ A B   , Tm10 Γ (prod10 A B) → Tm10 Γ A)
     (snd   : ∀ Γ A B   , Tm10 Γ (prod10 A B) → Tm10 Γ B)
     (left  : ∀ Γ A B   , Tm10 Γ A → Tm10 Γ (sum10 A B))
     (right : ∀ Γ A B   , Tm10 Γ B → Tm10 Γ (sum10 A B))
     (case  : ∀ Γ A B C , Tm10 Γ (sum10 A B) → Tm10 Γ (arr10 A C) → Tm10 Γ (arr10 B C) → Tm10 Γ C)
     (zero  : ∀ Γ       , Tm10 Γ nat10)
     (suc   : ∀ Γ       , Tm10 Γ nat10 → Tm10 Γ nat10)
     (rec   : ∀ Γ A     , Tm10 Γ nat10 → Tm10 Γ (arr10 nat10 (arr10 A A)) → Tm10 Γ A → Tm10 Γ A)
   , Tm10 Γ A.

Definition var10 {Γ A} : Var10 Γ A → Tm10 Γ A
 := λ x Tm10 var10 lam app tt pair fst snd left right case zero suc rec ,
     var10 _ _ x.

Definition lam10 {Γ A B} : Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B)
 := λ t Tm10 var10 lam10 app tt pair fst snd left right case zero suc rec ,
     lam10 _ _ _ (t Tm10 var10 lam10 app tt pair fst snd left right case zero suc rec).

Definition app10 {Γ A B} : Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B
 := λ t u Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec ,
     app10 _ _ _
         (t Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec)
         (u Tm10 var10 lam10 app10 tt pair fst snd left right case zero suc rec).

Definition tt10 {Γ} : Tm10 Γ top10
 := λ Tm10 var10 lam10 app10 tt10 pair fst snd left right case zero suc rec , tt10 _.

Definition pair10 {Γ A B} : Tm10 Γ A → Tm10 Γ B → Tm10 Γ (prod10 A B)
 := λ t u Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec ,
     pair10 _ _ _
          (t Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec)
          (u Tm10 var10 lam10 app10 tt10 pair10 fst snd left right case zero suc rec).

Definition fst10 {Γ A B} : Tm10 Γ (prod10 A B) → Tm10 Γ A
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd left right case zero suc rec ,
     fst10 _ _ _
         (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd left right case zero suc rec).

Definition snd10 {Γ A B} : Tm10 Γ (prod10 A B) → Tm10 Γ B
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left right case zero suc rec ,
     snd10 _ _ _
          (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left right case zero suc rec).

Definition left10 {Γ A B} : Tm10 Γ A → Tm10 Γ (sum10 A B)
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right case zero suc rec ,
     left10 _ _ _
          (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right case zero suc rec).

Definition right10 {Γ A B} : Tm10 Γ B → Tm10 Γ (sum10 A B)
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case zero suc rec ,
     right10 _ _ _
            (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case zero suc rec).

Definition case10 {Γ A B C} : Tm10 Γ (sum10 A B) → Tm10 Γ (arr10 A C) → Tm10 Γ (arr10 B C) → Tm10 Γ C
 := λ t u v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec ,
     case10 _ _ _ _
           (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)
           (u Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec)
           (v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero suc rec).

Definition zero10  {Γ} : Tm10 Γ nat10
 := λ Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc rec , zero10 _.

Definition suc10 {Γ} : Tm10 Γ nat10 → Tm10 Γ nat10
 := λ t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec ,
   suc10 _ (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec).

Definition rec10 {Γ A} : Tm10 Γ nat10 → Tm10 Γ (arr10 nat10 (arr10 A A)) → Tm10 Γ A → Tm10 Γ A
 := λ t u v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10 ,
     rec10 _ _
         (t Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)
         (u Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10)
         (v Tm10 var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 case10 zero10 suc10 rec10).

Definition v010 {Γ A} : Tm10 (snoc10 Γ A) A
 := var10 vz10.

Definition v110 {Γ A B} : Tm10 (snoc10 (snoc10 Γ A) B) A
 := var10 (vs10 vz10).

Definition v210 {Γ A B C} : Tm10 (snoc10 (snoc10 (snoc10 Γ A) B) C) A
 := var10 (vs10 (vs10 vz10)).

Definition v310 {Γ A B C D} : Tm10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) A
 := var10 (vs10 (vs10 (vs10 vz10))).

Definition tbool10 : Ty10
 := sum10 top10 top10.

Definition ttrue10 {Γ} : Tm10 Γ tbool10
 := left10 tt10.

Definition tfalse10 {Γ} : Tm10 Γ tbool10
 := right10 tt10.

Definition ifthenelse10 {Γ A} : Tm10 Γ (arr10 tbool10 (arr10 A (arr10 A A)))
 := lam10 (lam10 (lam10 (case10 v210 (lam10 v210) (lam10 v110)))).

Definition times410 {Γ A} : Tm10 Γ (arr10 (arr10 A A) (arr10 A A))
  := lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010))))).

Definition add10 {Γ} : Tm10 Γ (arr10 nat10 (arr10 nat10 nat10))
 := lam10 (rec10 v010
      (lam10 (lam10 (lam10 (suc10 (app10 v110 v010)))))
      (lam10 v010)).

Definition mul10 {Γ} : Tm10 Γ (arr10 nat10 (arr10 nat10 nat10))
 := lam10 (rec10 v010
     (lam10 (lam10 (lam10 (app10 (app10 add10 (app10 v110 v010)) v010))))
     (lam10 zero10)).

Definition fact10 {Γ} : Tm10 Γ (arr10 nat10 nat10)
 := lam10 (rec10 v010 (lam10 (lam10 (app10 (app10 mul10 (suc10 v110)) v010)))
        (suc10 zero10)).

Require Import Coq.Unicode.Utf8.

Definition Ty11 : Set
 := ∀ (Ty11           : Set)
      (nat top bot  : Ty11)
      (arr prod sum : Ty11 → Ty11 → Ty11)
    , Ty11.

Definition nat11 : Ty11 := λ _ nat11 _ _ _ _ _ , nat11.
Definition top11 : Ty11 := λ _ _ top11 _ _ _ _ , top11.
Definition bot11 : Ty11 := λ _ _ _ bot11 _ _ _ , bot11.

Definition arr11 : Ty11 → Ty11 → Ty11
 := λ A B Ty11 nat11 top11 bot11 arr11 prod sum ,
     arr11 (A Ty11 nat11 top11 bot11 arr11 prod sum) (B Ty11 nat11 top11 bot11 arr11 prod sum).

Definition prod11 : Ty11 → Ty11 → Ty11
 := λ A B Ty11 nat11 top11 bot11 arr11 prod11 sum ,
     prod11 (A Ty11 nat11 top11 bot11 arr11 prod11 sum) (B Ty11 nat11 top11 bot11 arr11 prod11 sum).

Definition sum11 : Ty11 → Ty11 → Ty11
 := λ A B Ty11 nat11 top11 bot11 arr11 prod11 sum11 ,
     sum11 (A Ty11 nat11 top11 bot11 arr11 prod11 sum11) (B Ty11 nat11 top11 bot11 arr11 prod11 sum11).

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
     (tt    : ∀ Γ       , Tm11 Γ top11)
     (pair  : ∀ Γ A B   , Tm11 Γ A → Tm11 Γ B → Tm11 Γ (prod11 A B))
     (fst   : ∀ Γ A B   , Tm11 Γ (prod11 A B) → Tm11 Γ A)
     (snd   : ∀ Γ A B   , Tm11 Γ (prod11 A B) → Tm11 Γ B)
     (left  : ∀ Γ A B   , Tm11 Γ A → Tm11 Γ (sum11 A B))
     (right : ∀ Γ A B   , Tm11 Γ B → Tm11 Γ (sum11 A B))
     (case  : ∀ Γ A B C , Tm11 Γ (sum11 A B) → Tm11 Γ (arr11 A C) → Tm11 Γ (arr11 B C) → Tm11 Γ C)
     (zero  : ∀ Γ       , Tm11 Γ nat11)
     (suc   : ∀ Γ       , Tm11 Γ nat11 → Tm11 Γ nat11)
     (rec   : ∀ Γ A     , Tm11 Γ nat11 → Tm11 Γ (arr11 nat11 (arr11 A A)) → Tm11 Γ A → Tm11 Γ A)
   , Tm11 Γ A.

Definition var11 {Γ A} : Var11 Γ A → Tm11 Γ A
 := λ x Tm11 var11 lam app tt pair fst snd left right case zero suc rec ,
     var11 _ _ x.

Definition lam11 {Γ A B} : Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B)
 := λ t Tm11 var11 lam11 app tt pair fst snd left right case zero suc rec ,
     lam11 _ _ _ (t Tm11 var11 lam11 app tt pair fst snd left right case zero suc rec).

Definition app11 {Γ A B} : Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B
 := λ t u Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec ,
     app11 _ _ _
         (t Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec)
         (u Tm11 var11 lam11 app11 tt pair fst snd left right case zero suc rec).

Definition tt11 {Γ} : Tm11 Γ top11
 := λ Tm11 var11 lam11 app11 tt11 pair fst snd left right case zero suc rec , tt11 _.

Definition pair11 {Γ A B} : Tm11 Γ A → Tm11 Γ B → Tm11 Γ (prod11 A B)
 := λ t u Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec ,
     pair11 _ _ _
          (t Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec)
          (u Tm11 var11 lam11 app11 tt11 pair11 fst snd left right case zero suc rec).

Definition fst11 {Γ A B} : Tm11 Γ (prod11 A B) → Tm11 Γ A
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd left right case zero suc rec ,
     fst11 _ _ _
         (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd left right case zero suc rec).

Definition snd11 {Γ A B} : Tm11 Γ (prod11 A B) → Tm11 Γ B
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left right case zero suc rec ,
     snd11 _ _ _
          (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left right case zero suc rec).

Definition left11 {Γ A B} : Tm11 Γ A → Tm11 Γ (sum11 A B)
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right case zero suc rec ,
     left11 _ _ _
          (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right case zero suc rec).

Definition right11 {Γ A B} : Tm11 Γ B → Tm11 Γ (sum11 A B)
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case zero suc rec ,
     right11 _ _ _
            (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case zero suc rec).

Definition case11 {Γ A B C} : Tm11 Γ (sum11 A B) → Tm11 Γ (arr11 A C) → Tm11 Γ (arr11 B C) → Tm11 Γ C
 := λ t u v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec ,
     case11 _ _ _ _
           (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)
           (u Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec)
           (v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero suc rec).

Definition zero11  {Γ} : Tm11 Γ nat11
 := λ Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc rec , zero11 _.

Definition suc11 {Γ} : Tm11 Γ nat11 → Tm11 Γ nat11
 := λ t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec ,
   suc11 _ (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec).

Definition rec11 {Γ A} : Tm11 Γ nat11 → Tm11 Γ (arr11 nat11 (arr11 A A)) → Tm11 Γ A → Tm11 Γ A
 := λ t u v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11 ,
     rec11 _ _
         (t Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)
         (u Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11)
         (v Tm11 var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 case11 zero11 suc11 rec11).

Definition v011 {Γ A} : Tm11 (snoc11 Γ A) A
 := var11 vz11.

Definition v111 {Γ A B} : Tm11 (snoc11 (snoc11 Γ A) B) A
 := var11 (vs11 vz11).

Definition v211 {Γ A B C} : Tm11 (snoc11 (snoc11 (snoc11 Γ A) B) C) A
 := var11 (vs11 (vs11 vz11)).

Definition v311 {Γ A B C D} : Tm11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) A
 := var11 (vs11 (vs11 (vs11 vz11))).

Definition tbool11 : Ty11
 := sum11 top11 top11.

Definition ttrue11 {Γ} : Tm11 Γ tbool11
 := left11 tt11.

Definition tfalse11 {Γ} : Tm11 Γ tbool11
 := right11 tt11.

Definition ifthenelse11 {Γ A} : Tm11 Γ (arr11 tbool11 (arr11 A (arr11 A A)))
 := lam11 (lam11 (lam11 (case11 v211 (lam11 v211) (lam11 v111)))).

Definition times411 {Γ A} : Tm11 Γ (arr11 (arr11 A A) (arr11 A A))
  := lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011))))).

Definition add11 {Γ} : Tm11 Γ (arr11 nat11 (arr11 nat11 nat11))
 := lam11 (rec11 v011
      (lam11 (lam11 (lam11 (suc11 (app11 v111 v011)))))
      (lam11 v011)).

Definition mul11 {Γ} : Tm11 Γ (arr11 nat11 (arr11 nat11 nat11))
 := lam11 (rec11 v011
     (lam11 (lam11 (lam11 (app11 (app11 add11 (app11 v111 v011)) v011))))
     (lam11 zero11)).

Definition fact11 {Γ} : Tm11 Γ (arr11 nat11 nat11)
 := lam11 (rec11 v011 (lam11 (lam11 (app11 (app11 mul11 (suc11 v111)) v011)))
        (suc11 zero11)).

Require Import Coq.Unicode.Utf8.

Definition Ty12 : Set
 := ∀ (Ty12           : Set)
      (nat top bot  : Ty12)
      (arr prod sum : Ty12 → Ty12 → Ty12)
    , Ty12.

Definition nat12 : Ty12 := λ _ nat12 _ _ _ _ _ , nat12.
Definition top12 : Ty12 := λ _ _ top12 _ _ _ _ , top12.
Definition bot12 : Ty12 := λ _ _ _ bot12 _ _ _ , bot12.

Definition arr12 : Ty12 → Ty12 → Ty12
 := λ A B Ty12 nat12 top12 bot12 arr12 prod sum ,
     arr12 (A Ty12 nat12 top12 bot12 arr12 prod sum) (B Ty12 nat12 top12 bot12 arr12 prod sum).

Definition prod12 : Ty12 → Ty12 → Ty12
 := λ A B Ty12 nat12 top12 bot12 arr12 prod12 sum ,
     prod12 (A Ty12 nat12 top12 bot12 arr12 prod12 sum) (B Ty12 nat12 top12 bot12 arr12 prod12 sum).

Definition sum12 : Ty12 → Ty12 → Ty12
 := λ A B Ty12 nat12 top12 bot12 arr12 prod12 sum12 ,
     sum12 (A Ty12 nat12 top12 bot12 arr12 prod12 sum12) (B Ty12 nat12 top12 bot12 arr12 prod12 sum12).

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
     (tt    : ∀ Γ       , Tm12 Γ top12)
     (pair  : ∀ Γ A B   , Tm12 Γ A → Tm12 Γ B → Tm12 Γ (prod12 A B))
     (fst   : ∀ Γ A B   , Tm12 Γ (prod12 A B) → Tm12 Γ A)
     (snd   : ∀ Γ A B   , Tm12 Γ (prod12 A B) → Tm12 Γ B)
     (left  : ∀ Γ A B   , Tm12 Γ A → Tm12 Γ (sum12 A B))
     (right : ∀ Γ A B   , Tm12 Γ B → Tm12 Γ (sum12 A B))
     (case  : ∀ Γ A B C , Tm12 Γ (sum12 A B) → Tm12 Γ (arr12 A C) → Tm12 Γ (arr12 B C) → Tm12 Γ C)
     (zero  : ∀ Γ       , Tm12 Γ nat12)
     (suc   : ∀ Γ       , Tm12 Γ nat12 → Tm12 Γ nat12)
     (rec   : ∀ Γ A     , Tm12 Γ nat12 → Tm12 Γ (arr12 nat12 (arr12 A A)) → Tm12 Γ A → Tm12 Γ A)
   , Tm12 Γ A.

Definition var12 {Γ A} : Var12 Γ A → Tm12 Γ A
 := λ x Tm12 var12 lam app tt pair fst snd left right case zero suc rec ,
     var12 _ _ x.

Definition lam12 {Γ A B} : Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B)
 := λ t Tm12 var12 lam12 app tt pair fst snd left right case zero suc rec ,
     lam12 _ _ _ (t Tm12 var12 lam12 app tt pair fst snd left right case zero suc rec).

Definition app12 {Γ A B} : Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B
 := λ t u Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec ,
     app12 _ _ _
         (t Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec)
         (u Tm12 var12 lam12 app12 tt pair fst snd left right case zero suc rec).

Definition tt12 {Γ} : Tm12 Γ top12
 := λ Tm12 var12 lam12 app12 tt12 pair fst snd left right case zero suc rec , tt12 _.

Definition pair12 {Γ A B} : Tm12 Γ A → Tm12 Γ B → Tm12 Γ (prod12 A B)
 := λ t u Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec ,
     pair12 _ _ _
          (t Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec)
          (u Tm12 var12 lam12 app12 tt12 pair12 fst snd left right case zero suc rec).

Definition fst12 {Γ A B} : Tm12 Γ (prod12 A B) → Tm12 Γ A
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd left right case zero suc rec ,
     fst12 _ _ _
         (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd left right case zero suc rec).

Definition snd12 {Γ A B} : Tm12 Γ (prod12 A B) → Tm12 Γ B
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left right case zero suc rec ,
     snd12 _ _ _
          (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left right case zero suc rec).

Definition left12 {Γ A B} : Tm12 Γ A → Tm12 Γ (sum12 A B)
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right case zero suc rec ,
     left12 _ _ _
          (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right case zero suc rec).

Definition right12 {Γ A B} : Tm12 Γ B → Tm12 Γ (sum12 A B)
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case zero suc rec ,
     right12 _ _ _
            (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case zero suc rec).

Definition case12 {Γ A B C} : Tm12 Γ (sum12 A B) → Tm12 Γ (arr12 A C) → Tm12 Γ (arr12 B C) → Tm12 Γ C
 := λ t u v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec ,
     case12 _ _ _ _
           (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)
           (u Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec)
           (v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero suc rec).

Definition zero12  {Γ} : Tm12 Γ nat12
 := λ Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc rec , zero12 _.

Definition suc12 {Γ} : Tm12 Γ nat12 → Tm12 Γ nat12
 := λ t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec ,
   suc12 _ (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec).

Definition rec12 {Γ A} : Tm12 Γ nat12 → Tm12 Γ (arr12 nat12 (arr12 A A)) → Tm12 Γ A → Tm12 Γ A
 := λ t u v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12 ,
     rec12 _ _
         (t Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)
         (u Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12)
         (v Tm12 var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 case12 zero12 suc12 rec12).

Definition v012 {Γ A} : Tm12 (snoc12 Γ A) A
 := var12 vz12.

Definition v112 {Γ A B} : Tm12 (snoc12 (snoc12 Γ A) B) A
 := var12 (vs12 vz12).

Definition v212 {Γ A B C} : Tm12 (snoc12 (snoc12 (snoc12 Γ A) B) C) A
 := var12 (vs12 (vs12 vz12)).

Definition v312 {Γ A B C D} : Tm12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) A
 := var12 (vs12 (vs12 (vs12 vz12))).

Definition tbool12 : Ty12
 := sum12 top12 top12.

Definition ttrue12 {Γ} : Tm12 Γ tbool12
 := left12 tt12.

Definition tfalse12 {Γ} : Tm12 Γ tbool12
 := right12 tt12.

Definition ifthenelse12 {Γ A} : Tm12 Γ (arr12 tbool12 (arr12 A (arr12 A A)))
 := lam12 (lam12 (lam12 (case12 v212 (lam12 v212) (lam12 v112)))).

Definition times412 {Γ A} : Tm12 Γ (arr12 (arr12 A A) (arr12 A A))
  := lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012))))).

Definition add12 {Γ} : Tm12 Γ (arr12 nat12 (arr12 nat12 nat12))
 := lam12 (rec12 v012
      (lam12 (lam12 (lam12 (suc12 (app12 v112 v012)))))
      (lam12 v012)).

Definition mul12 {Γ} : Tm12 Γ (arr12 nat12 (arr12 nat12 nat12))
 := lam12 (rec12 v012
     (lam12 (lam12 (lam12 (app12 (app12 add12 (app12 v112 v012)) v012))))
     (lam12 zero12)).

Definition fact12 {Γ} : Tm12 Γ (arr12 nat12 nat12)
 := lam12 (rec12 v012 (lam12 (lam12 (app12 (app12 mul12 (suc12 v112)) v012)))
        (suc12 zero12)).

Require Import Coq.Unicode.Utf8.

Definition Ty13 : Set
 := ∀ (Ty13           : Set)
      (nat top bot  : Ty13)
      (arr prod sum : Ty13 → Ty13 → Ty13)
    , Ty13.

Definition nat13 : Ty13 := λ _ nat13 _ _ _ _ _ , nat13.
Definition top13 : Ty13 := λ _ _ top13 _ _ _ _ , top13.
Definition bot13 : Ty13 := λ _ _ _ bot13 _ _ _ , bot13.

Definition arr13 : Ty13 → Ty13 → Ty13
 := λ A B Ty13 nat13 top13 bot13 arr13 prod sum ,
     arr13 (A Ty13 nat13 top13 bot13 arr13 prod sum) (B Ty13 nat13 top13 bot13 arr13 prod sum).

Definition prod13 : Ty13 → Ty13 → Ty13
 := λ A B Ty13 nat13 top13 bot13 arr13 prod13 sum ,
     prod13 (A Ty13 nat13 top13 bot13 arr13 prod13 sum) (B Ty13 nat13 top13 bot13 arr13 prod13 sum).

Definition sum13 : Ty13 → Ty13 → Ty13
 := λ A B Ty13 nat13 top13 bot13 arr13 prod13 sum13 ,
     sum13 (A Ty13 nat13 top13 bot13 arr13 prod13 sum13) (B Ty13 nat13 top13 bot13 arr13 prod13 sum13).

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
     (tt    : ∀ Γ       , Tm13 Γ top13)
     (pair  : ∀ Γ A B   , Tm13 Γ A → Tm13 Γ B → Tm13 Γ (prod13 A B))
     (fst   : ∀ Γ A B   , Tm13 Γ (prod13 A B) → Tm13 Γ A)
     (snd   : ∀ Γ A B   , Tm13 Γ (prod13 A B) → Tm13 Γ B)
     (left  : ∀ Γ A B   , Tm13 Γ A → Tm13 Γ (sum13 A B))
     (right : ∀ Γ A B   , Tm13 Γ B → Tm13 Γ (sum13 A B))
     (case  : ∀ Γ A B C , Tm13 Γ (sum13 A B) → Tm13 Γ (arr13 A C) → Tm13 Γ (arr13 B C) → Tm13 Γ C)
     (zero  : ∀ Γ       , Tm13 Γ nat13)
     (suc   : ∀ Γ       , Tm13 Γ nat13 → Tm13 Γ nat13)
     (rec   : ∀ Γ A     , Tm13 Γ nat13 → Tm13 Γ (arr13 nat13 (arr13 A A)) → Tm13 Γ A → Tm13 Γ A)
   , Tm13 Γ A.

Definition var13 {Γ A} : Var13 Γ A → Tm13 Γ A
 := λ x Tm13 var13 lam app tt pair fst snd left right case zero suc rec ,
     var13 _ _ x.

Definition lam13 {Γ A B} : Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B)
 := λ t Tm13 var13 lam13 app tt pair fst snd left right case zero suc rec ,
     lam13 _ _ _ (t Tm13 var13 lam13 app tt pair fst snd left right case zero suc rec).

Definition app13 {Γ A B} : Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B
 := λ t u Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec ,
     app13 _ _ _
         (t Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec)
         (u Tm13 var13 lam13 app13 tt pair fst snd left right case zero suc rec).

Definition tt13 {Γ} : Tm13 Γ top13
 := λ Tm13 var13 lam13 app13 tt13 pair fst snd left right case zero suc rec , tt13 _.

Definition pair13 {Γ A B} : Tm13 Γ A → Tm13 Γ B → Tm13 Γ (prod13 A B)
 := λ t u Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec ,
     pair13 _ _ _
          (t Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec)
          (u Tm13 var13 lam13 app13 tt13 pair13 fst snd left right case zero suc rec).

Definition fst13 {Γ A B} : Tm13 Γ (prod13 A B) → Tm13 Γ A
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd left right case zero suc rec ,
     fst13 _ _ _
         (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd left right case zero suc rec).

Definition snd13 {Γ A B} : Tm13 Γ (prod13 A B) → Tm13 Γ B
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left right case zero suc rec ,
     snd13 _ _ _
          (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left right case zero suc rec).

Definition left13 {Γ A B} : Tm13 Γ A → Tm13 Γ (sum13 A B)
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right case zero suc rec ,
     left13 _ _ _
          (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right case zero suc rec).

Definition right13 {Γ A B} : Tm13 Γ B → Tm13 Γ (sum13 A B)
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case zero suc rec ,
     right13 _ _ _
            (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case zero suc rec).

Definition case13 {Γ A B C} : Tm13 Γ (sum13 A B) → Tm13 Γ (arr13 A C) → Tm13 Γ (arr13 B C) → Tm13 Γ C
 := λ t u v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec ,
     case13 _ _ _ _
           (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)
           (u Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec)
           (v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero suc rec).

Definition zero13  {Γ} : Tm13 Γ nat13
 := λ Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc rec , zero13 _.

Definition suc13 {Γ} : Tm13 Γ nat13 → Tm13 Γ nat13
 := λ t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec ,
   suc13 _ (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec).

Definition rec13 {Γ A} : Tm13 Γ nat13 → Tm13 Γ (arr13 nat13 (arr13 A A)) → Tm13 Γ A → Tm13 Γ A
 := λ t u v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13 ,
     rec13 _ _
         (t Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)
         (u Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13)
         (v Tm13 var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 case13 zero13 suc13 rec13).

Definition v013 {Γ A} : Tm13 (snoc13 Γ A) A
 := var13 vz13.

Definition v113 {Γ A B} : Tm13 (snoc13 (snoc13 Γ A) B) A
 := var13 (vs13 vz13).

Definition v213 {Γ A B C} : Tm13 (snoc13 (snoc13 (snoc13 Γ A) B) C) A
 := var13 (vs13 (vs13 vz13)).

Definition v313 {Γ A B C D} : Tm13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) A
 := var13 (vs13 (vs13 (vs13 vz13))).

Definition tbool13 : Ty13
 := sum13 top13 top13.

Definition ttrue13 {Γ} : Tm13 Γ tbool13
 := left13 tt13.

Definition tfalse13 {Γ} : Tm13 Γ tbool13
 := right13 tt13.

Definition ifthenelse13 {Γ A} : Tm13 Γ (arr13 tbool13 (arr13 A (arr13 A A)))
 := lam13 (lam13 (lam13 (case13 v213 (lam13 v213) (lam13 v113)))).

Definition times413 {Γ A} : Tm13 Γ (arr13 (arr13 A A) (arr13 A A))
  := lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013))))).

Definition add13 {Γ} : Tm13 Γ (arr13 nat13 (arr13 nat13 nat13))
 := lam13 (rec13 v013
      (lam13 (lam13 (lam13 (suc13 (app13 v113 v013)))))
      (lam13 v013)).

Definition mul13 {Γ} : Tm13 Γ (arr13 nat13 (arr13 nat13 nat13))
 := lam13 (rec13 v013
     (lam13 (lam13 (lam13 (app13 (app13 add13 (app13 v113 v013)) v013))))
     (lam13 zero13)).

Definition fact13 {Γ} : Tm13 Γ (arr13 nat13 nat13)
 := lam13 (rec13 v013 (lam13 (lam13 (app13 (app13 mul13 (suc13 v113)) v013)))
        (suc13 zero13)).

Require Import Coq.Unicode.Utf8.

Definition Ty14 : Set
 := ∀ (Ty14           : Set)
      (nat top bot  : Ty14)
      (arr prod sum : Ty14 → Ty14 → Ty14)
    , Ty14.

Definition nat14 : Ty14 := λ _ nat14 _ _ _ _ _ , nat14.
Definition top14 : Ty14 := λ _ _ top14 _ _ _ _ , top14.
Definition bot14 : Ty14 := λ _ _ _ bot14 _ _ _ , bot14.

Definition arr14 : Ty14 → Ty14 → Ty14
 := λ A B Ty14 nat14 top14 bot14 arr14 prod sum ,
     arr14 (A Ty14 nat14 top14 bot14 arr14 prod sum) (B Ty14 nat14 top14 bot14 arr14 prod sum).

Definition prod14 : Ty14 → Ty14 → Ty14
 := λ A B Ty14 nat14 top14 bot14 arr14 prod14 sum ,
     prod14 (A Ty14 nat14 top14 bot14 arr14 prod14 sum) (B Ty14 nat14 top14 bot14 arr14 prod14 sum).

Definition sum14 : Ty14 → Ty14 → Ty14
 := λ A B Ty14 nat14 top14 bot14 arr14 prod14 sum14 ,
     sum14 (A Ty14 nat14 top14 bot14 arr14 prod14 sum14) (B Ty14 nat14 top14 bot14 arr14 prod14 sum14).

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
     (tt    : ∀ Γ       , Tm14 Γ top14)
     (pair  : ∀ Γ A B   , Tm14 Γ A → Tm14 Γ B → Tm14 Γ (prod14 A B))
     (fst   : ∀ Γ A B   , Tm14 Γ (prod14 A B) → Tm14 Γ A)
     (snd   : ∀ Γ A B   , Tm14 Γ (prod14 A B) → Tm14 Γ B)
     (left  : ∀ Γ A B   , Tm14 Γ A → Tm14 Γ (sum14 A B))
     (right : ∀ Γ A B   , Tm14 Γ B → Tm14 Γ (sum14 A B))
     (case  : ∀ Γ A B C , Tm14 Γ (sum14 A B) → Tm14 Γ (arr14 A C) → Tm14 Γ (arr14 B C) → Tm14 Γ C)
     (zero  : ∀ Γ       , Tm14 Γ nat14)
     (suc   : ∀ Γ       , Tm14 Γ nat14 → Tm14 Γ nat14)
     (rec   : ∀ Γ A     , Tm14 Γ nat14 → Tm14 Γ (arr14 nat14 (arr14 A A)) → Tm14 Γ A → Tm14 Γ A)
   , Tm14 Γ A.

Definition var14 {Γ A} : Var14 Γ A → Tm14 Γ A
 := λ x Tm14 var14 lam app tt pair fst snd left right case zero suc rec ,
     var14 _ _ x.

Definition lam14 {Γ A B} : Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B)
 := λ t Tm14 var14 lam14 app tt pair fst snd left right case zero suc rec ,
     lam14 _ _ _ (t Tm14 var14 lam14 app tt pair fst snd left right case zero suc rec).

Definition app14 {Γ A B} : Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B
 := λ t u Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec ,
     app14 _ _ _
         (t Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec)
         (u Tm14 var14 lam14 app14 tt pair fst snd left right case zero suc rec).

Definition tt14 {Γ} : Tm14 Γ top14
 := λ Tm14 var14 lam14 app14 tt14 pair fst snd left right case zero suc rec , tt14 _.

Definition pair14 {Γ A B} : Tm14 Γ A → Tm14 Γ B → Tm14 Γ (prod14 A B)
 := λ t u Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec ,
     pair14 _ _ _
          (t Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec)
          (u Tm14 var14 lam14 app14 tt14 pair14 fst snd left right case zero suc rec).

Definition fst14 {Γ A B} : Tm14 Γ (prod14 A B) → Tm14 Γ A
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd left right case zero suc rec ,
     fst14 _ _ _
         (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd left right case zero suc rec).

Definition snd14 {Γ A B} : Tm14 Γ (prod14 A B) → Tm14 Γ B
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left right case zero suc rec ,
     snd14 _ _ _
          (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left right case zero suc rec).

Definition left14 {Γ A B} : Tm14 Γ A → Tm14 Γ (sum14 A B)
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right case zero suc rec ,
     left14 _ _ _
          (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right case zero suc rec).

Definition right14 {Γ A B} : Tm14 Γ B → Tm14 Γ (sum14 A B)
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case zero suc rec ,
     right14 _ _ _
            (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case zero suc rec).

Definition case14 {Γ A B C} : Tm14 Γ (sum14 A B) → Tm14 Γ (arr14 A C) → Tm14 Γ (arr14 B C) → Tm14 Γ C
 := λ t u v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec ,
     case14 _ _ _ _
           (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)
           (u Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec)
           (v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero suc rec).

Definition zero14  {Γ} : Tm14 Γ nat14
 := λ Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc rec , zero14 _.

Definition suc14 {Γ} : Tm14 Γ nat14 → Tm14 Γ nat14
 := λ t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec ,
   suc14 _ (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec).

Definition rec14 {Γ A} : Tm14 Γ nat14 → Tm14 Γ (arr14 nat14 (arr14 A A)) → Tm14 Γ A → Tm14 Γ A
 := λ t u v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14 ,
     rec14 _ _
         (t Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)
         (u Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14)
         (v Tm14 var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 case14 zero14 suc14 rec14).

Definition v014 {Γ A} : Tm14 (snoc14 Γ A) A
 := var14 vz14.

Definition v114 {Γ A B} : Tm14 (snoc14 (snoc14 Γ A) B) A
 := var14 (vs14 vz14).

Definition v214 {Γ A B C} : Tm14 (snoc14 (snoc14 (snoc14 Γ A) B) C) A
 := var14 (vs14 (vs14 vz14)).

Definition v314 {Γ A B C D} : Tm14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) A
 := var14 (vs14 (vs14 (vs14 vz14))).

Definition tbool14 : Ty14
 := sum14 top14 top14.

Definition ttrue14 {Γ} : Tm14 Γ tbool14
 := left14 tt14.

Definition tfalse14 {Γ} : Tm14 Γ tbool14
 := right14 tt14.

Definition ifthenelse14 {Γ A} : Tm14 Γ (arr14 tbool14 (arr14 A (arr14 A A)))
 := lam14 (lam14 (lam14 (case14 v214 (lam14 v214) (lam14 v114)))).

Definition times414 {Γ A} : Tm14 Γ (arr14 (arr14 A A) (arr14 A A))
  := lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014))))).

Definition add14 {Γ} : Tm14 Γ (arr14 nat14 (arr14 nat14 nat14))
 := lam14 (rec14 v014
      (lam14 (lam14 (lam14 (suc14 (app14 v114 v014)))))
      (lam14 v014)).

Definition mul14 {Γ} : Tm14 Γ (arr14 nat14 (arr14 nat14 nat14))
 := lam14 (rec14 v014
     (lam14 (lam14 (lam14 (app14 (app14 add14 (app14 v114 v014)) v014))))
     (lam14 zero14)).

Definition fact14 {Γ} : Tm14 Γ (arr14 nat14 nat14)
 := lam14 (rec14 v014 (lam14 (lam14 (app14 (app14 mul14 (suc14 v114)) v014)))
        (suc14 zero14)).

Require Import Coq.Unicode.Utf8.

Definition Ty15 : Set
 := ∀ (Ty15           : Set)
      (nat top bot  : Ty15)
      (arr prod sum : Ty15 → Ty15 → Ty15)
    , Ty15.

Definition nat15 : Ty15 := λ _ nat15 _ _ _ _ _ , nat15.
Definition top15 : Ty15 := λ _ _ top15 _ _ _ _ , top15.
Definition bot15 : Ty15 := λ _ _ _ bot15 _ _ _ , bot15.

Definition arr15 : Ty15 → Ty15 → Ty15
 := λ A B Ty15 nat15 top15 bot15 arr15 prod sum ,
     arr15 (A Ty15 nat15 top15 bot15 arr15 prod sum) (B Ty15 nat15 top15 bot15 arr15 prod sum).

Definition prod15 : Ty15 → Ty15 → Ty15
 := λ A B Ty15 nat15 top15 bot15 arr15 prod15 sum ,
     prod15 (A Ty15 nat15 top15 bot15 arr15 prod15 sum) (B Ty15 nat15 top15 bot15 arr15 prod15 sum).

Definition sum15 : Ty15 → Ty15 → Ty15
 := λ A B Ty15 nat15 top15 bot15 arr15 prod15 sum15 ,
     sum15 (A Ty15 nat15 top15 bot15 arr15 prod15 sum15) (B Ty15 nat15 top15 bot15 arr15 prod15 sum15).

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
     (tt    : ∀ Γ       , Tm15 Γ top15)
     (pair  : ∀ Γ A B   , Tm15 Γ A → Tm15 Γ B → Tm15 Γ (prod15 A B))
     (fst   : ∀ Γ A B   , Tm15 Γ (prod15 A B) → Tm15 Γ A)
     (snd   : ∀ Γ A B   , Tm15 Γ (prod15 A B) → Tm15 Γ B)
     (left  : ∀ Γ A B   , Tm15 Γ A → Tm15 Γ (sum15 A B))
     (right : ∀ Γ A B   , Tm15 Γ B → Tm15 Γ (sum15 A B))
     (case  : ∀ Γ A B C , Tm15 Γ (sum15 A B) → Tm15 Γ (arr15 A C) → Tm15 Γ (arr15 B C) → Tm15 Γ C)
     (zero  : ∀ Γ       , Tm15 Γ nat15)
     (suc   : ∀ Γ       , Tm15 Γ nat15 → Tm15 Γ nat15)
     (rec   : ∀ Γ A     , Tm15 Γ nat15 → Tm15 Γ (arr15 nat15 (arr15 A A)) → Tm15 Γ A → Tm15 Γ A)
   , Tm15 Γ A.

Definition var15 {Γ A} : Var15 Γ A → Tm15 Γ A
 := λ x Tm15 var15 lam app tt pair fst snd left right case zero suc rec ,
     var15 _ _ x.

Definition lam15 {Γ A B} : Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B)
 := λ t Tm15 var15 lam15 app tt pair fst snd left right case zero suc rec ,
     lam15 _ _ _ (t Tm15 var15 lam15 app tt pair fst snd left right case zero suc rec).

Definition app15 {Γ A B} : Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B
 := λ t u Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec ,
     app15 _ _ _
         (t Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec)
         (u Tm15 var15 lam15 app15 tt pair fst snd left right case zero suc rec).

Definition tt15 {Γ} : Tm15 Γ top15
 := λ Tm15 var15 lam15 app15 tt15 pair fst snd left right case zero suc rec , tt15 _.

Definition pair15 {Γ A B} : Tm15 Γ A → Tm15 Γ B → Tm15 Γ (prod15 A B)
 := λ t u Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec ,
     pair15 _ _ _
          (t Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec)
          (u Tm15 var15 lam15 app15 tt15 pair15 fst snd left right case zero suc rec).

Definition fst15 {Γ A B} : Tm15 Γ (prod15 A B) → Tm15 Γ A
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd left right case zero suc rec ,
     fst15 _ _ _
         (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd left right case zero suc rec).

Definition snd15 {Γ A B} : Tm15 Γ (prod15 A B) → Tm15 Γ B
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left right case zero suc rec ,
     snd15 _ _ _
          (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left right case zero suc rec).

Definition left15 {Γ A B} : Tm15 Γ A → Tm15 Γ (sum15 A B)
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right case zero suc rec ,
     left15 _ _ _
          (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right case zero suc rec).

Definition right15 {Γ A B} : Tm15 Γ B → Tm15 Γ (sum15 A B)
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case zero suc rec ,
     right15 _ _ _
            (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case zero suc rec).

Definition case15 {Γ A B C} : Tm15 Γ (sum15 A B) → Tm15 Γ (arr15 A C) → Tm15 Γ (arr15 B C) → Tm15 Γ C
 := λ t u v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec ,
     case15 _ _ _ _
           (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)
           (u Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec)
           (v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero suc rec).

Definition zero15  {Γ} : Tm15 Γ nat15
 := λ Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc rec , zero15 _.

Definition suc15 {Γ} : Tm15 Γ nat15 → Tm15 Γ nat15
 := λ t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec ,
   suc15 _ (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec).

Definition rec15 {Γ A} : Tm15 Γ nat15 → Tm15 Γ (arr15 nat15 (arr15 A A)) → Tm15 Γ A → Tm15 Γ A
 := λ t u v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15 ,
     rec15 _ _
         (t Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)
         (u Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15)
         (v Tm15 var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 case15 zero15 suc15 rec15).

Definition v015 {Γ A} : Tm15 (snoc15 Γ A) A
 := var15 vz15.

Definition v115 {Γ A B} : Tm15 (snoc15 (snoc15 Γ A) B) A
 := var15 (vs15 vz15).

Definition v215 {Γ A B C} : Tm15 (snoc15 (snoc15 (snoc15 Γ A) B) C) A
 := var15 (vs15 (vs15 vz15)).

Definition v315 {Γ A B C D} : Tm15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) A
 := var15 (vs15 (vs15 (vs15 vz15))).

Definition tbool15 : Ty15
 := sum15 top15 top15.

Definition ttrue15 {Γ} : Tm15 Γ tbool15
 := left15 tt15.

Definition tfalse15 {Γ} : Tm15 Γ tbool15
 := right15 tt15.

Definition ifthenelse15 {Γ A} : Tm15 Γ (arr15 tbool15 (arr15 A (arr15 A A)))
 := lam15 (lam15 (lam15 (case15 v215 (lam15 v215) (lam15 v115)))).

Definition times415 {Γ A} : Tm15 Γ (arr15 (arr15 A A) (arr15 A A))
  := lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015))))).

Definition add15 {Γ} : Tm15 Γ (arr15 nat15 (arr15 nat15 nat15))
 := lam15 (rec15 v015
      (lam15 (lam15 (lam15 (suc15 (app15 v115 v015)))))
      (lam15 v015)).

Definition mul15 {Γ} : Tm15 Γ (arr15 nat15 (arr15 nat15 nat15))
 := lam15 (rec15 v015
     (lam15 (lam15 (lam15 (app15 (app15 add15 (app15 v115 v015)) v015))))
     (lam15 zero15)).

Definition fact15 {Γ} : Tm15 Γ (arr15 nat15 nat15)
 := lam15 (rec15 v015 (lam15 (lam15 (app15 (app15 mul15 (suc15 v115)) v015)))
        (suc15 zero15)).

Require Import Coq.Unicode.Utf8.

Definition Ty16 : Set
 := ∀ (Ty16           : Set)
      (nat top bot  : Ty16)
      (arr prod sum : Ty16 → Ty16 → Ty16)
    , Ty16.

Definition nat16 : Ty16 := λ _ nat16 _ _ _ _ _ , nat16.
Definition top16 : Ty16 := λ _ _ top16 _ _ _ _ , top16.
Definition bot16 : Ty16 := λ _ _ _ bot16 _ _ _ , bot16.

Definition arr16 : Ty16 → Ty16 → Ty16
 := λ A B Ty16 nat16 top16 bot16 arr16 prod sum ,
     arr16 (A Ty16 nat16 top16 bot16 arr16 prod sum) (B Ty16 nat16 top16 bot16 arr16 prod sum).

Definition prod16 : Ty16 → Ty16 → Ty16
 := λ A B Ty16 nat16 top16 bot16 arr16 prod16 sum ,
     prod16 (A Ty16 nat16 top16 bot16 arr16 prod16 sum) (B Ty16 nat16 top16 bot16 arr16 prod16 sum).

Definition sum16 : Ty16 → Ty16 → Ty16
 := λ A B Ty16 nat16 top16 bot16 arr16 prod16 sum16 ,
     sum16 (A Ty16 nat16 top16 bot16 arr16 prod16 sum16) (B Ty16 nat16 top16 bot16 arr16 prod16 sum16).

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
     (tt    : ∀ Γ       , Tm16 Γ top16)
     (pair  : ∀ Γ A B   , Tm16 Γ A → Tm16 Γ B → Tm16 Γ (prod16 A B))
     (fst   : ∀ Γ A B   , Tm16 Γ (prod16 A B) → Tm16 Γ A)
     (snd   : ∀ Γ A B   , Tm16 Γ (prod16 A B) → Tm16 Γ B)
     (left  : ∀ Γ A B   , Tm16 Γ A → Tm16 Γ (sum16 A B))
     (right : ∀ Γ A B   , Tm16 Γ B → Tm16 Γ (sum16 A B))
     (case  : ∀ Γ A B C , Tm16 Γ (sum16 A B) → Tm16 Γ (arr16 A C) → Tm16 Γ (arr16 B C) → Tm16 Γ C)
     (zero  : ∀ Γ       , Tm16 Γ nat16)
     (suc   : ∀ Γ       , Tm16 Γ nat16 → Tm16 Γ nat16)
     (rec   : ∀ Γ A     , Tm16 Γ nat16 → Tm16 Γ (arr16 nat16 (arr16 A A)) → Tm16 Γ A → Tm16 Γ A)
   , Tm16 Γ A.

Definition var16 {Γ A} : Var16 Γ A → Tm16 Γ A
 := λ x Tm16 var16 lam app tt pair fst snd left right case zero suc rec ,
     var16 _ _ x.

Definition lam16 {Γ A B} : Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B)
 := λ t Tm16 var16 lam16 app tt pair fst snd left right case zero suc rec ,
     lam16 _ _ _ (t Tm16 var16 lam16 app tt pair fst snd left right case zero suc rec).

Definition app16 {Γ A B} : Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B
 := λ t u Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec ,
     app16 _ _ _
         (t Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec)
         (u Tm16 var16 lam16 app16 tt pair fst snd left right case zero suc rec).

Definition tt16 {Γ} : Tm16 Γ top16
 := λ Tm16 var16 lam16 app16 tt16 pair fst snd left right case zero suc rec , tt16 _.

Definition pair16 {Γ A B} : Tm16 Γ A → Tm16 Γ B → Tm16 Γ (prod16 A B)
 := λ t u Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec ,
     pair16 _ _ _
          (t Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec)
          (u Tm16 var16 lam16 app16 tt16 pair16 fst snd left right case zero suc rec).

Definition fst16 {Γ A B} : Tm16 Γ (prod16 A B) → Tm16 Γ A
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd left right case zero suc rec ,
     fst16 _ _ _
         (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd left right case zero suc rec).

Definition snd16 {Γ A B} : Tm16 Γ (prod16 A B) → Tm16 Γ B
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left right case zero suc rec ,
     snd16 _ _ _
          (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left right case zero suc rec).

Definition left16 {Γ A B} : Tm16 Γ A → Tm16 Γ (sum16 A B)
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right case zero suc rec ,
     left16 _ _ _
          (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right case zero suc rec).

Definition right16 {Γ A B} : Tm16 Γ B → Tm16 Γ (sum16 A B)
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case zero suc rec ,
     right16 _ _ _
            (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case zero suc rec).

Definition case16 {Γ A B C} : Tm16 Γ (sum16 A B) → Tm16 Γ (arr16 A C) → Tm16 Γ (arr16 B C) → Tm16 Γ C
 := λ t u v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec ,
     case16 _ _ _ _
           (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)
           (u Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec)
           (v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero suc rec).

Definition zero16  {Γ} : Tm16 Γ nat16
 := λ Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc rec , zero16 _.

Definition suc16 {Γ} : Tm16 Γ nat16 → Tm16 Γ nat16
 := λ t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec ,
   suc16 _ (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec).

Definition rec16 {Γ A} : Tm16 Γ nat16 → Tm16 Γ (arr16 nat16 (arr16 A A)) → Tm16 Γ A → Tm16 Γ A
 := λ t u v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16 ,
     rec16 _ _
         (t Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)
         (u Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16)
         (v Tm16 var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 case16 zero16 suc16 rec16).

Definition v016 {Γ A} : Tm16 (snoc16 Γ A) A
 := var16 vz16.

Definition v116 {Γ A B} : Tm16 (snoc16 (snoc16 Γ A) B) A
 := var16 (vs16 vz16).

Definition v216 {Γ A B C} : Tm16 (snoc16 (snoc16 (snoc16 Γ A) B) C) A
 := var16 (vs16 (vs16 vz16)).

Definition v316 {Γ A B C D} : Tm16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) A
 := var16 (vs16 (vs16 (vs16 vz16))).

Definition tbool16 : Ty16
 := sum16 top16 top16.

Definition ttrue16 {Γ} : Tm16 Γ tbool16
 := left16 tt16.

Definition tfalse16 {Γ} : Tm16 Γ tbool16
 := right16 tt16.

Definition ifthenelse16 {Γ A} : Tm16 Γ (arr16 tbool16 (arr16 A (arr16 A A)))
 := lam16 (lam16 (lam16 (case16 v216 (lam16 v216) (lam16 v116)))).

Definition times416 {Γ A} : Tm16 Γ (arr16 (arr16 A A) (arr16 A A))
  := lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016))))).

Definition add16 {Γ} : Tm16 Γ (arr16 nat16 (arr16 nat16 nat16))
 := lam16 (rec16 v016
      (lam16 (lam16 (lam16 (suc16 (app16 v116 v016)))))
      (lam16 v016)).

Definition mul16 {Γ} : Tm16 Γ (arr16 nat16 (arr16 nat16 nat16))
 := lam16 (rec16 v016
     (lam16 (lam16 (lam16 (app16 (app16 add16 (app16 v116 v016)) v016))))
     (lam16 zero16)).

Definition fact16 {Γ} : Tm16 Γ (arr16 nat16 nat16)
 := lam16 (rec16 v016 (lam16 (lam16 (app16 (app16 mul16 (suc16 v116)) v016)))
        (suc16 zero16)).

Require Import Coq.Unicode.Utf8.

Definition Ty17 : Set
 := ∀ (Ty17           : Set)
      (nat top bot  : Ty17)
      (arr prod sum : Ty17 → Ty17 → Ty17)
    , Ty17.

Definition nat17 : Ty17 := λ _ nat17 _ _ _ _ _ , nat17.
Definition top17 : Ty17 := λ _ _ top17 _ _ _ _ , top17.
Definition bot17 : Ty17 := λ _ _ _ bot17 _ _ _ , bot17.

Definition arr17 : Ty17 → Ty17 → Ty17
 := λ A B Ty17 nat17 top17 bot17 arr17 prod sum ,
     arr17 (A Ty17 nat17 top17 bot17 arr17 prod sum) (B Ty17 nat17 top17 bot17 arr17 prod sum).

Definition prod17 : Ty17 → Ty17 → Ty17
 := λ A B Ty17 nat17 top17 bot17 arr17 prod17 sum ,
     prod17 (A Ty17 nat17 top17 bot17 arr17 prod17 sum) (B Ty17 nat17 top17 bot17 arr17 prod17 sum).

Definition sum17 : Ty17 → Ty17 → Ty17
 := λ A B Ty17 nat17 top17 bot17 arr17 prod17 sum17 ,
     sum17 (A Ty17 nat17 top17 bot17 arr17 prod17 sum17) (B Ty17 nat17 top17 bot17 arr17 prod17 sum17).

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
     (tt    : ∀ Γ       , Tm17 Γ top17)
     (pair  : ∀ Γ A B   , Tm17 Γ A → Tm17 Γ B → Tm17 Γ (prod17 A B))
     (fst   : ∀ Γ A B   , Tm17 Γ (prod17 A B) → Tm17 Γ A)
     (snd   : ∀ Γ A B   , Tm17 Γ (prod17 A B) → Tm17 Γ B)
     (left  : ∀ Γ A B   , Tm17 Γ A → Tm17 Γ (sum17 A B))
     (right : ∀ Γ A B   , Tm17 Γ B → Tm17 Γ (sum17 A B))
     (case  : ∀ Γ A B C , Tm17 Γ (sum17 A B) → Tm17 Γ (arr17 A C) → Tm17 Γ (arr17 B C) → Tm17 Γ C)
     (zero  : ∀ Γ       , Tm17 Γ nat17)
     (suc   : ∀ Γ       , Tm17 Γ nat17 → Tm17 Γ nat17)
     (rec   : ∀ Γ A     , Tm17 Γ nat17 → Tm17 Γ (arr17 nat17 (arr17 A A)) → Tm17 Γ A → Tm17 Γ A)
   , Tm17 Γ A.

Definition var17 {Γ A} : Var17 Γ A → Tm17 Γ A
 := λ x Tm17 var17 lam app tt pair fst snd left right case zero suc rec ,
     var17 _ _ x.

Definition lam17 {Γ A B} : Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B)
 := λ t Tm17 var17 lam17 app tt pair fst snd left right case zero suc rec ,
     lam17 _ _ _ (t Tm17 var17 lam17 app tt pair fst snd left right case zero suc rec).

Definition app17 {Γ A B} : Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B
 := λ t u Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec ,
     app17 _ _ _
         (t Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec)
         (u Tm17 var17 lam17 app17 tt pair fst snd left right case zero suc rec).

Definition tt17 {Γ} : Tm17 Γ top17
 := λ Tm17 var17 lam17 app17 tt17 pair fst snd left right case zero suc rec , tt17 _.

Definition pair17 {Γ A B} : Tm17 Γ A → Tm17 Γ B → Tm17 Γ (prod17 A B)
 := λ t u Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec ,
     pair17 _ _ _
          (t Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec)
          (u Tm17 var17 lam17 app17 tt17 pair17 fst snd left right case zero suc rec).

Definition fst17 {Γ A B} : Tm17 Γ (prod17 A B) → Tm17 Γ A
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd left right case zero suc rec ,
     fst17 _ _ _
         (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd left right case zero suc rec).

Definition snd17 {Γ A B} : Tm17 Γ (prod17 A B) → Tm17 Γ B
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left right case zero suc rec ,
     snd17 _ _ _
          (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left right case zero suc rec).

Definition left17 {Γ A B} : Tm17 Γ A → Tm17 Γ (sum17 A B)
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right case zero suc rec ,
     left17 _ _ _
          (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right case zero suc rec).

Definition right17 {Γ A B} : Tm17 Γ B → Tm17 Γ (sum17 A B)
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case zero suc rec ,
     right17 _ _ _
            (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case zero suc rec).

Definition case17 {Γ A B C} : Tm17 Γ (sum17 A B) → Tm17 Γ (arr17 A C) → Tm17 Γ (arr17 B C) → Tm17 Γ C
 := λ t u v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec ,
     case17 _ _ _ _
           (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)
           (u Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec)
           (v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero suc rec).

Definition zero17  {Γ} : Tm17 Γ nat17
 := λ Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc rec , zero17 _.

Definition suc17 {Γ} : Tm17 Γ nat17 → Tm17 Γ nat17
 := λ t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec ,
   suc17 _ (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec).

Definition rec17 {Γ A} : Tm17 Γ nat17 → Tm17 Γ (arr17 nat17 (arr17 A A)) → Tm17 Γ A → Tm17 Γ A
 := λ t u v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17 ,
     rec17 _ _
         (t Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)
         (u Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17)
         (v Tm17 var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 case17 zero17 suc17 rec17).

Definition v017 {Γ A} : Tm17 (snoc17 Γ A) A
 := var17 vz17.

Definition v117 {Γ A B} : Tm17 (snoc17 (snoc17 Γ A) B) A
 := var17 (vs17 vz17).

Definition v217 {Γ A B C} : Tm17 (snoc17 (snoc17 (snoc17 Γ A) B) C) A
 := var17 (vs17 (vs17 vz17)).

Definition v317 {Γ A B C D} : Tm17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) A
 := var17 (vs17 (vs17 (vs17 vz17))).

Definition tbool17 : Ty17
 := sum17 top17 top17.

Definition ttrue17 {Γ} : Tm17 Γ tbool17
 := left17 tt17.

Definition tfalse17 {Γ} : Tm17 Γ tbool17
 := right17 tt17.

Definition ifthenelse17 {Γ A} : Tm17 Γ (arr17 tbool17 (arr17 A (arr17 A A)))
 := lam17 (lam17 (lam17 (case17 v217 (lam17 v217) (lam17 v117)))).

Definition times417 {Γ A} : Tm17 Γ (arr17 (arr17 A A) (arr17 A A))
  := lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017))))).

Definition add17 {Γ} : Tm17 Γ (arr17 nat17 (arr17 nat17 nat17))
 := lam17 (rec17 v017
      (lam17 (lam17 (lam17 (suc17 (app17 v117 v017)))))
      (lam17 v017)).

Definition mul17 {Γ} : Tm17 Γ (arr17 nat17 (arr17 nat17 nat17))
 := lam17 (rec17 v017
     (lam17 (lam17 (lam17 (app17 (app17 add17 (app17 v117 v017)) v017))))
     (lam17 zero17)).

Definition fact17 {Γ} : Tm17 Γ (arr17 nat17 nat17)
 := lam17 (rec17 v017 (lam17 (lam17 (app17 (app17 mul17 (suc17 v117)) v017)))
        (suc17 zero17)).

Require Import Coq.Unicode.Utf8.

Definition Ty18 : Set
 := ∀ (Ty18           : Set)
      (nat top bot  : Ty18)
      (arr prod sum : Ty18 → Ty18 → Ty18)
    , Ty18.

Definition nat18 : Ty18 := λ _ nat18 _ _ _ _ _ , nat18.
Definition top18 : Ty18 := λ _ _ top18 _ _ _ _ , top18.
Definition bot18 : Ty18 := λ _ _ _ bot18 _ _ _ , bot18.

Definition arr18 : Ty18 → Ty18 → Ty18
 := λ A B Ty18 nat18 top18 bot18 arr18 prod sum ,
     arr18 (A Ty18 nat18 top18 bot18 arr18 prod sum) (B Ty18 nat18 top18 bot18 arr18 prod sum).

Definition prod18 : Ty18 → Ty18 → Ty18
 := λ A B Ty18 nat18 top18 bot18 arr18 prod18 sum ,
     prod18 (A Ty18 nat18 top18 bot18 arr18 prod18 sum) (B Ty18 nat18 top18 bot18 arr18 prod18 sum).

Definition sum18 : Ty18 → Ty18 → Ty18
 := λ A B Ty18 nat18 top18 bot18 arr18 prod18 sum18 ,
     sum18 (A Ty18 nat18 top18 bot18 arr18 prod18 sum18) (B Ty18 nat18 top18 bot18 arr18 prod18 sum18).

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
     (tt    : ∀ Γ       , Tm18 Γ top18)
     (pair  : ∀ Γ A B   , Tm18 Γ A → Tm18 Γ B → Tm18 Γ (prod18 A B))
     (fst   : ∀ Γ A B   , Tm18 Γ (prod18 A B) → Tm18 Γ A)
     (snd   : ∀ Γ A B   , Tm18 Γ (prod18 A B) → Tm18 Γ B)
     (left  : ∀ Γ A B   , Tm18 Γ A → Tm18 Γ (sum18 A B))
     (right : ∀ Γ A B   , Tm18 Γ B → Tm18 Γ (sum18 A B))
     (case  : ∀ Γ A B C , Tm18 Γ (sum18 A B) → Tm18 Γ (arr18 A C) → Tm18 Γ (arr18 B C) → Tm18 Γ C)
     (zero  : ∀ Γ       , Tm18 Γ nat18)
     (suc   : ∀ Γ       , Tm18 Γ nat18 → Tm18 Γ nat18)
     (rec   : ∀ Γ A     , Tm18 Γ nat18 → Tm18 Γ (arr18 nat18 (arr18 A A)) → Tm18 Γ A → Tm18 Γ A)
   , Tm18 Γ A.

Definition var18 {Γ A} : Var18 Γ A → Tm18 Γ A
 := λ x Tm18 var18 lam app tt pair fst snd left right case zero suc rec ,
     var18 _ _ x.

Definition lam18 {Γ A B} : Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B)
 := λ t Tm18 var18 lam18 app tt pair fst snd left right case zero suc rec ,
     lam18 _ _ _ (t Tm18 var18 lam18 app tt pair fst snd left right case zero suc rec).

Definition app18 {Γ A B} : Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B
 := λ t u Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec ,
     app18 _ _ _
         (t Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec)
         (u Tm18 var18 lam18 app18 tt pair fst snd left right case zero suc rec).

Definition tt18 {Γ} : Tm18 Γ top18
 := λ Tm18 var18 lam18 app18 tt18 pair fst snd left right case zero suc rec , tt18 _.

Definition pair18 {Γ A B} : Tm18 Γ A → Tm18 Γ B → Tm18 Γ (prod18 A B)
 := λ t u Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec ,
     pair18 _ _ _
          (t Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec)
          (u Tm18 var18 lam18 app18 tt18 pair18 fst snd left right case zero suc rec).

Definition fst18 {Γ A B} : Tm18 Γ (prod18 A B) → Tm18 Γ A
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd left right case zero suc rec ,
     fst18 _ _ _
         (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd left right case zero suc rec).

Definition snd18 {Γ A B} : Tm18 Γ (prod18 A B) → Tm18 Γ B
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left right case zero suc rec ,
     snd18 _ _ _
          (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left right case zero suc rec).

Definition left18 {Γ A B} : Tm18 Γ A → Tm18 Γ (sum18 A B)
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right case zero suc rec ,
     left18 _ _ _
          (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right case zero suc rec).

Definition right18 {Γ A B} : Tm18 Γ B → Tm18 Γ (sum18 A B)
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case zero suc rec ,
     right18 _ _ _
            (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case zero suc rec).

Definition case18 {Γ A B C} : Tm18 Γ (sum18 A B) → Tm18 Γ (arr18 A C) → Tm18 Γ (arr18 B C) → Tm18 Γ C
 := λ t u v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec ,
     case18 _ _ _ _
           (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)
           (u Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec)
           (v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero suc rec).

Definition zero18  {Γ} : Tm18 Γ nat18
 := λ Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc rec , zero18 _.

Definition suc18 {Γ} : Tm18 Γ nat18 → Tm18 Γ nat18
 := λ t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec ,
   suc18 _ (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec).

Definition rec18 {Γ A} : Tm18 Γ nat18 → Tm18 Γ (arr18 nat18 (arr18 A A)) → Tm18 Γ A → Tm18 Γ A
 := λ t u v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18 ,
     rec18 _ _
         (t Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)
         (u Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18)
         (v Tm18 var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 case18 zero18 suc18 rec18).

Definition v018 {Γ A} : Tm18 (snoc18 Γ A) A
 := var18 vz18.

Definition v118 {Γ A B} : Tm18 (snoc18 (snoc18 Γ A) B) A
 := var18 (vs18 vz18).

Definition v218 {Γ A B C} : Tm18 (snoc18 (snoc18 (snoc18 Γ A) B) C) A
 := var18 (vs18 (vs18 vz18)).

Definition v318 {Γ A B C D} : Tm18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) A
 := var18 (vs18 (vs18 (vs18 vz18))).

Definition tbool18 : Ty18
 := sum18 top18 top18.

Definition ttrue18 {Γ} : Tm18 Γ tbool18
 := left18 tt18.

Definition tfalse18 {Γ} : Tm18 Γ tbool18
 := right18 tt18.

Definition ifthenelse18 {Γ A} : Tm18 Γ (arr18 tbool18 (arr18 A (arr18 A A)))
 := lam18 (lam18 (lam18 (case18 v218 (lam18 v218) (lam18 v118)))).

Definition times418 {Γ A} : Tm18 Γ (arr18 (arr18 A A) (arr18 A A))
  := lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018))))).

Definition add18 {Γ} : Tm18 Γ (arr18 nat18 (arr18 nat18 nat18))
 := lam18 (rec18 v018
      (lam18 (lam18 (lam18 (suc18 (app18 v118 v018)))))
      (lam18 v018)).

Definition mul18 {Γ} : Tm18 Γ (arr18 nat18 (arr18 nat18 nat18))
 := lam18 (rec18 v018
     (lam18 (lam18 (lam18 (app18 (app18 add18 (app18 v118 v018)) v018))))
     (lam18 zero18)).

Definition fact18 {Γ} : Tm18 Γ (arr18 nat18 nat18)
 := lam18 (rec18 v018 (lam18 (lam18 (app18 (app18 mul18 (suc18 v118)) v018)))
        (suc18 zero18)).

Require Import Coq.Unicode.Utf8.

Definition Ty19 : Set
 := ∀ (Ty19           : Set)
      (nat top bot  : Ty19)
      (arr prod sum : Ty19 → Ty19 → Ty19)
    , Ty19.

Definition nat19 : Ty19 := λ _ nat19 _ _ _ _ _ , nat19.
Definition top19 : Ty19 := λ _ _ top19 _ _ _ _ , top19.
Definition bot19 : Ty19 := λ _ _ _ bot19 _ _ _ , bot19.

Definition arr19 : Ty19 → Ty19 → Ty19
 := λ A B Ty19 nat19 top19 bot19 arr19 prod sum ,
     arr19 (A Ty19 nat19 top19 bot19 arr19 prod sum) (B Ty19 nat19 top19 bot19 arr19 prod sum).

Definition prod19 : Ty19 → Ty19 → Ty19
 := λ A B Ty19 nat19 top19 bot19 arr19 prod19 sum ,
     prod19 (A Ty19 nat19 top19 bot19 arr19 prod19 sum) (B Ty19 nat19 top19 bot19 arr19 prod19 sum).

Definition sum19 : Ty19 → Ty19 → Ty19
 := λ A B Ty19 nat19 top19 bot19 arr19 prod19 sum19 ,
     sum19 (A Ty19 nat19 top19 bot19 arr19 prod19 sum19) (B Ty19 nat19 top19 bot19 arr19 prod19 sum19).

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
     (tt    : ∀ Γ       , Tm19 Γ top19)
     (pair  : ∀ Γ A B   , Tm19 Γ A → Tm19 Γ B → Tm19 Γ (prod19 A B))
     (fst   : ∀ Γ A B   , Tm19 Γ (prod19 A B) → Tm19 Γ A)
     (snd   : ∀ Γ A B   , Tm19 Γ (prod19 A B) → Tm19 Γ B)
     (left  : ∀ Γ A B   , Tm19 Γ A → Tm19 Γ (sum19 A B))
     (right : ∀ Γ A B   , Tm19 Γ B → Tm19 Γ (sum19 A B))
     (case  : ∀ Γ A B C , Tm19 Γ (sum19 A B) → Tm19 Γ (arr19 A C) → Tm19 Γ (arr19 B C) → Tm19 Γ C)
     (zero  : ∀ Γ       , Tm19 Γ nat19)
     (suc   : ∀ Γ       , Tm19 Γ nat19 → Tm19 Γ nat19)
     (rec   : ∀ Γ A     , Tm19 Γ nat19 → Tm19 Γ (arr19 nat19 (arr19 A A)) → Tm19 Γ A → Tm19 Γ A)
   , Tm19 Γ A.

Definition var19 {Γ A} : Var19 Γ A → Tm19 Γ A
 := λ x Tm19 var19 lam app tt pair fst snd left right case zero suc rec ,
     var19 _ _ x.

Definition lam19 {Γ A B} : Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B)
 := λ t Tm19 var19 lam19 app tt pair fst snd left right case zero suc rec ,
     lam19 _ _ _ (t Tm19 var19 lam19 app tt pair fst snd left right case zero suc rec).

Definition app19 {Γ A B} : Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B
 := λ t u Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec ,
     app19 _ _ _
         (t Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec)
         (u Tm19 var19 lam19 app19 tt pair fst snd left right case zero suc rec).

Definition tt19 {Γ} : Tm19 Γ top19
 := λ Tm19 var19 lam19 app19 tt19 pair fst snd left right case zero suc rec , tt19 _.

Definition pair19 {Γ A B} : Tm19 Γ A → Tm19 Γ B → Tm19 Γ (prod19 A B)
 := λ t u Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec ,
     pair19 _ _ _
          (t Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec)
          (u Tm19 var19 lam19 app19 tt19 pair19 fst snd left right case zero suc rec).

Definition fst19 {Γ A B} : Tm19 Γ (prod19 A B) → Tm19 Γ A
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd left right case zero suc rec ,
     fst19 _ _ _
         (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd left right case zero suc rec).

Definition snd19 {Γ A B} : Tm19 Γ (prod19 A B) → Tm19 Γ B
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left right case zero suc rec ,
     snd19 _ _ _
          (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left right case zero suc rec).

Definition left19 {Γ A B} : Tm19 Γ A → Tm19 Γ (sum19 A B)
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right case zero suc rec ,
     left19 _ _ _
          (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right case zero suc rec).

Definition right19 {Γ A B} : Tm19 Γ B → Tm19 Γ (sum19 A B)
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case zero suc rec ,
     right19 _ _ _
            (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case zero suc rec).

Definition case19 {Γ A B C} : Tm19 Γ (sum19 A B) → Tm19 Γ (arr19 A C) → Tm19 Γ (arr19 B C) → Tm19 Γ C
 := λ t u v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec ,
     case19 _ _ _ _
           (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)
           (u Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec)
           (v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero suc rec).

Definition zero19  {Γ} : Tm19 Γ nat19
 := λ Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc rec , zero19 _.

Definition suc19 {Γ} : Tm19 Γ nat19 → Tm19 Γ nat19
 := λ t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec ,
   suc19 _ (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec).

Definition rec19 {Γ A} : Tm19 Γ nat19 → Tm19 Γ (arr19 nat19 (arr19 A A)) → Tm19 Γ A → Tm19 Γ A
 := λ t u v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19 ,
     rec19 _ _
         (t Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)
         (u Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19)
         (v Tm19 var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 case19 zero19 suc19 rec19).

Definition v019 {Γ A} : Tm19 (snoc19 Γ A) A
 := var19 vz19.

Definition v119 {Γ A B} : Tm19 (snoc19 (snoc19 Γ A) B) A
 := var19 (vs19 vz19).

Definition v219 {Γ A B C} : Tm19 (snoc19 (snoc19 (snoc19 Γ A) B) C) A
 := var19 (vs19 (vs19 vz19)).

Definition v319 {Γ A B C D} : Tm19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) A
 := var19 (vs19 (vs19 (vs19 vz19))).

Definition tbool19 : Ty19
 := sum19 top19 top19.

Definition ttrue19 {Γ} : Tm19 Γ tbool19
 := left19 tt19.

Definition tfalse19 {Γ} : Tm19 Γ tbool19
 := right19 tt19.

Definition ifthenelse19 {Γ A} : Tm19 Γ (arr19 tbool19 (arr19 A (arr19 A A)))
 := lam19 (lam19 (lam19 (case19 v219 (lam19 v219) (lam19 v119)))).

Definition times419 {Γ A} : Tm19 Γ (arr19 (arr19 A A) (arr19 A A))
  := lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019))))).

Definition add19 {Γ} : Tm19 Γ (arr19 nat19 (arr19 nat19 nat19))
 := lam19 (rec19 v019
      (lam19 (lam19 (lam19 (suc19 (app19 v119 v019)))))
      (lam19 v019)).

Definition mul19 {Γ} : Tm19 Γ (arr19 nat19 (arr19 nat19 nat19))
 := lam19 (rec19 v019
     (lam19 (lam19 (lam19 (app19 (app19 add19 (app19 v119 v019)) v019))))
     (lam19 zero19)).

Definition fact19 {Γ} : Tm19 Γ (arr19 nat19 nat19)
 := lam19 (rec19 v019 (lam19 (lam19 (app19 (app19 mul19 (suc19 v119)) v019)))
        (suc19 zero19)).

Require Import Coq.Unicode.Utf8.

Definition Ty20 : Set
 := ∀ (Ty20           : Set)
      (nat top bot  : Ty20)
      (arr prod sum : Ty20 → Ty20 → Ty20)
    , Ty20.

Definition nat20 : Ty20 := λ _ nat20 _ _ _ _ _ , nat20.
Definition top20 : Ty20 := λ _ _ top20 _ _ _ _ , top20.
Definition bot20 : Ty20 := λ _ _ _ bot20 _ _ _ , bot20.

Definition arr20 : Ty20 → Ty20 → Ty20
 := λ A B Ty20 nat20 top20 bot20 arr20 prod sum ,
     arr20 (A Ty20 nat20 top20 bot20 arr20 prod sum) (B Ty20 nat20 top20 bot20 arr20 prod sum).

Definition prod20 : Ty20 → Ty20 → Ty20
 := λ A B Ty20 nat20 top20 bot20 arr20 prod20 sum ,
     prod20 (A Ty20 nat20 top20 bot20 arr20 prod20 sum) (B Ty20 nat20 top20 bot20 arr20 prod20 sum).

Definition sum20 : Ty20 → Ty20 → Ty20
 := λ A B Ty20 nat20 top20 bot20 arr20 prod20 sum20 ,
     sum20 (A Ty20 nat20 top20 bot20 arr20 prod20 sum20) (B Ty20 nat20 top20 bot20 arr20 prod20 sum20).

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
     (tt    : ∀ Γ       , Tm20 Γ top20)
     (pair  : ∀ Γ A B   , Tm20 Γ A → Tm20 Γ B → Tm20 Γ (prod20 A B))
     (fst   : ∀ Γ A B   , Tm20 Γ (prod20 A B) → Tm20 Γ A)
     (snd   : ∀ Γ A B   , Tm20 Γ (prod20 A B) → Tm20 Γ B)
     (left  : ∀ Γ A B   , Tm20 Γ A → Tm20 Γ (sum20 A B))
     (right : ∀ Γ A B   , Tm20 Γ B → Tm20 Γ (sum20 A B))
     (case  : ∀ Γ A B C , Tm20 Γ (sum20 A B) → Tm20 Γ (arr20 A C) → Tm20 Γ (arr20 B C) → Tm20 Γ C)
     (zero  : ∀ Γ       , Tm20 Γ nat20)
     (suc   : ∀ Γ       , Tm20 Γ nat20 → Tm20 Γ nat20)
     (rec   : ∀ Γ A     , Tm20 Γ nat20 → Tm20 Γ (arr20 nat20 (arr20 A A)) → Tm20 Γ A → Tm20 Γ A)
   , Tm20 Γ A.

Definition var20 {Γ A} : Var20 Γ A → Tm20 Γ A
 := λ x Tm20 var20 lam app tt pair fst snd left right case zero suc rec ,
     var20 _ _ x.

Definition lam20 {Γ A B} : Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B)
 := λ t Tm20 var20 lam20 app tt pair fst snd left right case zero suc rec ,
     lam20 _ _ _ (t Tm20 var20 lam20 app tt pair fst snd left right case zero suc rec).

Definition app20 {Γ A B} : Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B
 := λ t u Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec ,
     app20 _ _ _
         (t Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec)
         (u Tm20 var20 lam20 app20 tt pair fst snd left right case zero suc rec).

Definition tt20 {Γ} : Tm20 Γ top20
 := λ Tm20 var20 lam20 app20 tt20 pair fst snd left right case zero suc rec , tt20 _.

Definition pair20 {Γ A B} : Tm20 Γ A → Tm20 Γ B → Tm20 Γ (prod20 A B)
 := λ t u Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec ,
     pair20 _ _ _
          (t Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec)
          (u Tm20 var20 lam20 app20 tt20 pair20 fst snd left right case zero suc rec).

Definition fst20 {Γ A B} : Tm20 Γ (prod20 A B) → Tm20 Γ A
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd left right case zero suc rec ,
     fst20 _ _ _
         (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd left right case zero suc rec).

Definition snd20 {Γ A B} : Tm20 Γ (prod20 A B) → Tm20 Γ B
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left right case zero suc rec ,
     snd20 _ _ _
          (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left right case zero suc rec).

Definition left20 {Γ A B} : Tm20 Γ A → Tm20 Γ (sum20 A B)
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right case zero suc rec ,
     left20 _ _ _
          (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right case zero suc rec).

Definition right20 {Γ A B} : Tm20 Γ B → Tm20 Γ (sum20 A B)
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case zero suc rec ,
     right20 _ _ _
            (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case zero suc rec).

Definition case20 {Γ A B C} : Tm20 Γ (sum20 A B) → Tm20 Γ (arr20 A C) → Tm20 Γ (arr20 B C) → Tm20 Γ C
 := λ t u v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec ,
     case20 _ _ _ _
           (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)
           (u Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec)
           (v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero suc rec).

Definition zero20  {Γ} : Tm20 Γ nat20
 := λ Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc rec , zero20 _.

Definition suc20 {Γ} : Tm20 Γ nat20 → Tm20 Γ nat20
 := λ t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec ,
   suc20 _ (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec).

Definition rec20 {Γ A} : Tm20 Γ nat20 → Tm20 Γ (arr20 nat20 (arr20 A A)) → Tm20 Γ A → Tm20 Γ A
 := λ t u v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20 ,
     rec20 _ _
         (t Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)
         (u Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20)
         (v Tm20 var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 case20 zero20 suc20 rec20).

Definition v020 {Γ A} : Tm20 (snoc20 Γ A) A
 := var20 vz20.

Definition v120 {Γ A B} : Tm20 (snoc20 (snoc20 Γ A) B) A
 := var20 (vs20 vz20).

Definition v220 {Γ A B C} : Tm20 (snoc20 (snoc20 (snoc20 Γ A) B) C) A
 := var20 (vs20 (vs20 vz20)).

Definition v320 {Γ A B C D} : Tm20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) A
 := var20 (vs20 (vs20 (vs20 vz20))).

Definition tbool20 : Ty20
 := sum20 top20 top20.

Definition ttrue20 {Γ} : Tm20 Γ tbool20
 := left20 tt20.

Definition tfalse20 {Γ} : Tm20 Γ tbool20
 := right20 tt20.

Definition ifthenelse20 {Γ A} : Tm20 Γ (arr20 tbool20 (arr20 A (arr20 A A)))
 := lam20 (lam20 (lam20 (case20 v220 (lam20 v220) (lam20 v120)))).

Definition times420 {Γ A} : Tm20 Γ (arr20 (arr20 A A) (arr20 A A))
  := lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020))))).

Definition add20 {Γ} : Tm20 Γ (arr20 nat20 (arr20 nat20 nat20))
 := lam20 (rec20 v020
      (lam20 (lam20 (lam20 (suc20 (app20 v120 v020)))))
      (lam20 v020)).

Definition mul20 {Γ} : Tm20 Γ (arr20 nat20 (arr20 nat20 nat20))
 := lam20 (rec20 v020
     (lam20 (lam20 (lam20 (app20 (app20 add20 (app20 v120 v020)) v020))))
     (lam20 zero20)).

Definition fact20 {Γ} : Tm20 Γ (arr20 nat20 nat20)
 := lam20 (rec20 v020 (lam20 (lam20 (app20 (app20 mul20 (suc20 v120)) v020)))
        (suc20 zero20)).

Require Import Coq.Unicode.Utf8.

Definition Ty21 : Set
 := ∀ (Ty21           : Set)
      (nat top bot  : Ty21)
      (arr prod sum : Ty21 → Ty21 → Ty21)
    , Ty21.

Definition nat21 : Ty21 := λ _ nat21 _ _ _ _ _ , nat21.
Definition top21 : Ty21 := λ _ _ top21 _ _ _ _ , top21.
Definition bot21 : Ty21 := λ _ _ _ bot21 _ _ _ , bot21.

Definition arr21 : Ty21 → Ty21 → Ty21
 := λ A B Ty21 nat21 top21 bot21 arr21 prod sum ,
     arr21 (A Ty21 nat21 top21 bot21 arr21 prod sum) (B Ty21 nat21 top21 bot21 arr21 prod sum).

Definition prod21 : Ty21 → Ty21 → Ty21
 := λ A B Ty21 nat21 top21 bot21 arr21 prod21 sum ,
     prod21 (A Ty21 nat21 top21 bot21 arr21 prod21 sum) (B Ty21 nat21 top21 bot21 arr21 prod21 sum).

Definition sum21 : Ty21 → Ty21 → Ty21
 := λ A B Ty21 nat21 top21 bot21 arr21 prod21 sum21 ,
     sum21 (A Ty21 nat21 top21 bot21 arr21 prod21 sum21) (B Ty21 nat21 top21 bot21 arr21 prod21 sum21).

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
     (tt    : ∀ Γ       , Tm21 Γ top21)
     (pair  : ∀ Γ A B   , Tm21 Γ A → Tm21 Γ B → Tm21 Γ (prod21 A B))
     (fst   : ∀ Γ A B   , Tm21 Γ (prod21 A B) → Tm21 Γ A)
     (snd   : ∀ Γ A B   , Tm21 Γ (prod21 A B) → Tm21 Γ B)
     (left  : ∀ Γ A B   , Tm21 Γ A → Tm21 Γ (sum21 A B))
     (right : ∀ Γ A B   , Tm21 Γ B → Tm21 Γ (sum21 A B))
     (case  : ∀ Γ A B C , Tm21 Γ (sum21 A B) → Tm21 Γ (arr21 A C) → Tm21 Γ (arr21 B C) → Tm21 Γ C)
     (zero  : ∀ Γ       , Tm21 Γ nat21)
     (suc   : ∀ Γ       , Tm21 Γ nat21 → Tm21 Γ nat21)
     (rec   : ∀ Γ A     , Tm21 Γ nat21 → Tm21 Γ (arr21 nat21 (arr21 A A)) → Tm21 Γ A → Tm21 Γ A)
   , Tm21 Γ A.

Definition var21 {Γ A} : Var21 Γ A → Tm21 Γ A
 := λ x Tm21 var21 lam app tt pair fst snd left right case zero suc rec ,
     var21 _ _ x.

Definition lam21 {Γ A B} : Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B)
 := λ t Tm21 var21 lam21 app tt pair fst snd left right case zero suc rec ,
     lam21 _ _ _ (t Tm21 var21 lam21 app tt pair fst snd left right case zero suc rec).

Definition app21 {Γ A B} : Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B
 := λ t u Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec ,
     app21 _ _ _
         (t Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec)
         (u Tm21 var21 lam21 app21 tt pair fst snd left right case zero suc rec).

Definition tt21 {Γ} : Tm21 Γ top21
 := λ Tm21 var21 lam21 app21 tt21 pair fst snd left right case zero suc rec , tt21 _.

Definition pair21 {Γ A B} : Tm21 Γ A → Tm21 Γ B → Tm21 Γ (prod21 A B)
 := λ t u Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec ,
     pair21 _ _ _
          (t Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec)
          (u Tm21 var21 lam21 app21 tt21 pair21 fst snd left right case zero suc rec).

Definition fst21 {Γ A B} : Tm21 Γ (prod21 A B) → Tm21 Γ A
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd left right case zero suc rec ,
     fst21 _ _ _
         (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd left right case zero suc rec).

Definition snd21 {Γ A B} : Tm21 Γ (prod21 A B) → Tm21 Γ B
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left right case zero suc rec ,
     snd21 _ _ _
          (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left right case zero suc rec).

Definition left21 {Γ A B} : Tm21 Γ A → Tm21 Γ (sum21 A B)
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right case zero suc rec ,
     left21 _ _ _
          (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right case zero suc rec).

Definition right21 {Γ A B} : Tm21 Γ B → Tm21 Γ (sum21 A B)
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case zero suc rec ,
     right21 _ _ _
            (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case zero suc rec).

Definition case21 {Γ A B C} : Tm21 Γ (sum21 A B) → Tm21 Γ (arr21 A C) → Tm21 Γ (arr21 B C) → Tm21 Γ C
 := λ t u v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec ,
     case21 _ _ _ _
           (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)
           (u Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec)
           (v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero suc rec).

Definition zero21  {Γ} : Tm21 Γ nat21
 := λ Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc rec , zero21 _.

Definition suc21 {Γ} : Tm21 Γ nat21 → Tm21 Γ nat21
 := λ t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec ,
   suc21 _ (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec).

Definition rec21 {Γ A} : Tm21 Γ nat21 → Tm21 Γ (arr21 nat21 (arr21 A A)) → Tm21 Γ A → Tm21 Γ A
 := λ t u v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21 ,
     rec21 _ _
         (t Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)
         (u Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21)
         (v Tm21 var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 case21 zero21 suc21 rec21).

Definition v021 {Γ A} : Tm21 (snoc21 Γ A) A
 := var21 vz21.

Definition v121 {Γ A B} : Tm21 (snoc21 (snoc21 Γ A) B) A
 := var21 (vs21 vz21).

Definition v221 {Γ A B C} : Tm21 (snoc21 (snoc21 (snoc21 Γ A) B) C) A
 := var21 (vs21 (vs21 vz21)).

Definition v321 {Γ A B C D} : Tm21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) A
 := var21 (vs21 (vs21 (vs21 vz21))).

Definition tbool21 : Ty21
 := sum21 top21 top21.

Definition ttrue21 {Γ} : Tm21 Γ tbool21
 := left21 tt21.

Definition tfalse21 {Γ} : Tm21 Γ tbool21
 := right21 tt21.

Definition ifthenelse21 {Γ A} : Tm21 Γ (arr21 tbool21 (arr21 A (arr21 A A)))
 := lam21 (lam21 (lam21 (case21 v221 (lam21 v221) (lam21 v121)))).

Definition times421 {Γ A} : Tm21 Γ (arr21 (arr21 A A) (arr21 A A))
  := lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021))))).

Definition add21 {Γ} : Tm21 Γ (arr21 nat21 (arr21 nat21 nat21))
 := lam21 (rec21 v021
      (lam21 (lam21 (lam21 (suc21 (app21 v121 v021)))))
      (lam21 v021)).

Definition mul21 {Γ} : Tm21 Γ (arr21 nat21 (arr21 nat21 nat21))
 := lam21 (rec21 v021
     (lam21 (lam21 (lam21 (app21 (app21 add21 (app21 v121 v021)) v021))))
     (lam21 zero21)).

Definition fact21 {Γ} : Tm21 Γ (arr21 nat21 nat21)
 := lam21 (rec21 v021 (lam21 (lam21 (app21 (app21 mul21 (suc21 v121)) v021)))
        (suc21 zero21)).

Require Import Coq.Unicode.Utf8.

Definition Ty22 : Set
 := ∀ (Ty22           : Set)
      (nat top bot  : Ty22)
      (arr prod sum : Ty22 → Ty22 → Ty22)
    , Ty22.

Definition nat22 : Ty22 := λ _ nat22 _ _ _ _ _ , nat22.
Definition top22 : Ty22 := λ _ _ top22 _ _ _ _ , top22.
Definition bot22 : Ty22 := λ _ _ _ bot22 _ _ _ , bot22.

Definition arr22 : Ty22 → Ty22 → Ty22
 := λ A B Ty22 nat22 top22 bot22 arr22 prod sum ,
     arr22 (A Ty22 nat22 top22 bot22 arr22 prod sum) (B Ty22 nat22 top22 bot22 arr22 prod sum).

Definition prod22 : Ty22 → Ty22 → Ty22
 := λ A B Ty22 nat22 top22 bot22 arr22 prod22 sum ,
     prod22 (A Ty22 nat22 top22 bot22 arr22 prod22 sum) (B Ty22 nat22 top22 bot22 arr22 prod22 sum).

Definition sum22 : Ty22 → Ty22 → Ty22
 := λ A B Ty22 nat22 top22 bot22 arr22 prod22 sum22 ,
     sum22 (A Ty22 nat22 top22 bot22 arr22 prod22 sum22) (B Ty22 nat22 top22 bot22 arr22 prod22 sum22).

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
     (tt    : ∀ Γ       , Tm22 Γ top22)
     (pair  : ∀ Γ A B   , Tm22 Γ A → Tm22 Γ B → Tm22 Γ (prod22 A B))
     (fst   : ∀ Γ A B   , Tm22 Γ (prod22 A B) → Tm22 Γ A)
     (snd   : ∀ Γ A B   , Tm22 Γ (prod22 A B) → Tm22 Γ B)
     (left  : ∀ Γ A B   , Tm22 Γ A → Tm22 Γ (sum22 A B))
     (right : ∀ Γ A B   , Tm22 Γ B → Tm22 Γ (sum22 A B))
     (case  : ∀ Γ A B C , Tm22 Γ (sum22 A B) → Tm22 Γ (arr22 A C) → Tm22 Γ (arr22 B C) → Tm22 Γ C)
     (zero  : ∀ Γ       , Tm22 Γ nat22)
     (suc   : ∀ Γ       , Tm22 Γ nat22 → Tm22 Γ nat22)
     (rec   : ∀ Γ A     , Tm22 Γ nat22 → Tm22 Γ (arr22 nat22 (arr22 A A)) → Tm22 Γ A → Tm22 Γ A)
   , Tm22 Γ A.

Definition var22 {Γ A} : Var22 Γ A → Tm22 Γ A
 := λ x Tm22 var22 lam app tt pair fst snd left right case zero suc rec ,
     var22 _ _ x.

Definition lam22 {Γ A B} : Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B)
 := λ t Tm22 var22 lam22 app tt pair fst snd left right case zero suc rec ,
     lam22 _ _ _ (t Tm22 var22 lam22 app tt pair fst snd left right case zero suc rec).

Definition app22 {Γ A B} : Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B
 := λ t u Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec ,
     app22 _ _ _
         (t Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec)
         (u Tm22 var22 lam22 app22 tt pair fst snd left right case zero suc rec).

Definition tt22 {Γ} : Tm22 Γ top22
 := λ Tm22 var22 lam22 app22 tt22 pair fst snd left right case zero suc rec , tt22 _.

Definition pair22 {Γ A B} : Tm22 Γ A → Tm22 Γ B → Tm22 Γ (prod22 A B)
 := λ t u Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec ,
     pair22 _ _ _
          (t Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec)
          (u Tm22 var22 lam22 app22 tt22 pair22 fst snd left right case zero suc rec).

Definition fst22 {Γ A B} : Tm22 Γ (prod22 A B) → Tm22 Γ A
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd left right case zero suc rec ,
     fst22 _ _ _
         (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd left right case zero suc rec).

Definition snd22 {Γ A B} : Tm22 Γ (prod22 A B) → Tm22 Γ B
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left right case zero suc rec ,
     snd22 _ _ _
          (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left right case zero suc rec).

Definition left22 {Γ A B} : Tm22 Γ A → Tm22 Γ (sum22 A B)
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right case zero suc rec ,
     left22 _ _ _
          (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right case zero suc rec).

Definition right22 {Γ A B} : Tm22 Γ B → Tm22 Γ (sum22 A B)
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case zero suc rec ,
     right22 _ _ _
            (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case zero suc rec).

Definition case22 {Γ A B C} : Tm22 Γ (sum22 A B) → Tm22 Γ (arr22 A C) → Tm22 Γ (arr22 B C) → Tm22 Γ C
 := λ t u v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec ,
     case22 _ _ _ _
           (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)
           (u Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec)
           (v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero suc rec).

Definition zero22  {Γ} : Tm22 Γ nat22
 := λ Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc rec , zero22 _.

Definition suc22 {Γ} : Tm22 Γ nat22 → Tm22 Γ nat22
 := λ t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec ,
   suc22 _ (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec).

Definition rec22 {Γ A} : Tm22 Γ nat22 → Tm22 Γ (arr22 nat22 (arr22 A A)) → Tm22 Γ A → Tm22 Γ A
 := λ t u v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22 ,
     rec22 _ _
         (t Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)
         (u Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22)
         (v Tm22 var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 case22 zero22 suc22 rec22).

Definition v022 {Γ A} : Tm22 (snoc22 Γ A) A
 := var22 vz22.

Definition v122 {Γ A B} : Tm22 (snoc22 (snoc22 Γ A) B) A
 := var22 (vs22 vz22).

Definition v222 {Γ A B C} : Tm22 (snoc22 (snoc22 (snoc22 Γ A) B) C) A
 := var22 (vs22 (vs22 vz22)).

Definition v322 {Γ A B C D} : Tm22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) A
 := var22 (vs22 (vs22 (vs22 vz22))).

Definition tbool22 : Ty22
 := sum22 top22 top22.

Definition ttrue22 {Γ} : Tm22 Γ tbool22
 := left22 tt22.

Definition tfalse22 {Γ} : Tm22 Γ tbool22
 := right22 tt22.

Definition ifthenelse22 {Γ A} : Tm22 Γ (arr22 tbool22 (arr22 A (arr22 A A)))
 := lam22 (lam22 (lam22 (case22 v222 (lam22 v222) (lam22 v122)))).

Definition times422 {Γ A} : Tm22 Γ (arr22 (arr22 A A) (arr22 A A))
  := lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022))))).

Definition add22 {Γ} : Tm22 Γ (arr22 nat22 (arr22 nat22 nat22))
 := lam22 (rec22 v022
      (lam22 (lam22 (lam22 (suc22 (app22 v122 v022)))))
      (lam22 v022)).

Definition mul22 {Γ} : Tm22 Γ (arr22 nat22 (arr22 nat22 nat22))
 := lam22 (rec22 v022
     (lam22 (lam22 (lam22 (app22 (app22 add22 (app22 v122 v022)) v022))))
     (lam22 zero22)).

Definition fact22 {Γ} : Tm22 Γ (arr22 nat22 nat22)
 := lam22 (rec22 v022 (lam22 (lam22 (app22 (app22 mul22 (suc22 v122)) v022)))
        (suc22 zero22)).

Require Import Coq.Unicode.Utf8.

Definition Ty23 : Set
 := ∀ (Ty23           : Set)
      (nat top bot  : Ty23)
      (arr prod sum : Ty23 → Ty23 → Ty23)
    , Ty23.

Definition nat23 : Ty23 := λ _ nat23 _ _ _ _ _ , nat23.
Definition top23 : Ty23 := λ _ _ top23 _ _ _ _ , top23.
Definition bot23 : Ty23 := λ _ _ _ bot23 _ _ _ , bot23.

Definition arr23 : Ty23 → Ty23 → Ty23
 := λ A B Ty23 nat23 top23 bot23 arr23 prod sum ,
     arr23 (A Ty23 nat23 top23 bot23 arr23 prod sum) (B Ty23 nat23 top23 bot23 arr23 prod sum).

Definition prod23 : Ty23 → Ty23 → Ty23
 := λ A B Ty23 nat23 top23 bot23 arr23 prod23 sum ,
     prod23 (A Ty23 nat23 top23 bot23 arr23 prod23 sum) (B Ty23 nat23 top23 bot23 arr23 prod23 sum).

Definition sum23 : Ty23 → Ty23 → Ty23
 := λ A B Ty23 nat23 top23 bot23 arr23 prod23 sum23 ,
     sum23 (A Ty23 nat23 top23 bot23 arr23 prod23 sum23) (B Ty23 nat23 top23 bot23 arr23 prod23 sum23).

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
     (tt    : ∀ Γ       , Tm23 Γ top23)
     (pair  : ∀ Γ A B   , Tm23 Γ A → Tm23 Γ B → Tm23 Γ (prod23 A B))
     (fst   : ∀ Γ A B   , Tm23 Γ (prod23 A B) → Tm23 Γ A)
     (snd   : ∀ Γ A B   , Tm23 Γ (prod23 A B) → Tm23 Γ B)
     (left  : ∀ Γ A B   , Tm23 Γ A → Tm23 Γ (sum23 A B))
     (right : ∀ Γ A B   , Tm23 Γ B → Tm23 Γ (sum23 A B))
     (case  : ∀ Γ A B C , Tm23 Γ (sum23 A B) → Tm23 Γ (arr23 A C) → Tm23 Γ (arr23 B C) → Tm23 Γ C)
     (zero  : ∀ Γ       , Tm23 Γ nat23)
     (suc   : ∀ Γ       , Tm23 Γ nat23 → Tm23 Γ nat23)
     (rec   : ∀ Γ A     , Tm23 Γ nat23 → Tm23 Γ (arr23 nat23 (arr23 A A)) → Tm23 Γ A → Tm23 Γ A)
   , Tm23 Γ A.

Definition var23 {Γ A} : Var23 Γ A → Tm23 Γ A
 := λ x Tm23 var23 lam app tt pair fst snd left right case zero suc rec ,
     var23 _ _ x.

Definition lam23 {Γ A B} : Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B)
 := λ t Tm23 var23 lam23 app tt pair fst snd left right case zero suc rec ,
     lam23 _ _ _ (t Tm23 var23 lam23 app tt pair fst snd left right case zero suc rec).

Definition app23 {Γ A B} : Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B
 := λ t u Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec ,
     app23 _ _ _
         (t Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec)
         (u Tm23 var23 lam23 app23 tt pair fst snd left right case zero suc rec).

Definition tt23 {Γ} : Tm23 Γ top23
 := λ Tm23 var23 lam23 app23 tt23 pair fst snd left right case zero suc rec , tt23 _.

Definition pair23 {Γ A B} : Tm23 Γ A → Tm23 Γ B → Tm23 Γ (prod23 A B)
 := λ t u Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec ,
     pair23 _ _ _
          (t Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec)
          (u Tm23 var23 lam23 app23 tt23 pair23 fst snd left right case zero suc rec).

Definition fst23 {Γ A B} : Tm23 Γ (prod23 A B) → Tm23 Γ A
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd left right case zero suc rec ,
     fst23 _ _ _
         (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd left right case zero suc rec).

Definition snd23 {Γ A B} : Tm23 Γ (prod23 A B) → Tm23 Γ B
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left right case zero suc rec ,
     snd23 _ _ _
          (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left right case zero suc rec).

Definition left23 {Γ A B} : Tm23 Γ A → Tm23 Γ (sum23 A B)
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right case zero suc rec ,
     left23 _ _ _
          (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right case zero suc rec).

Definition right23 {Γ A B} : Tm23 Γ B → Tm23 Γ (sum23 A B)
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case zero suc rec ,
     right23 _ _ _
            (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case zero suc rec).

Definition case23 {Γ A B C} : Tm23 Γ (sum23 A B) → Tm23 Γ (arr23 A C) → Tm23 Γ (arr23 B C) → Tm23 Γ C
 := λ t u v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec ,
     case23 _ _ _ _
           (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)
           (u Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec)
           (v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero suc rec).

Definition zero23  {Γ} : Tm23 Γ nat23
 := λ Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc rec , zero23 _.

Definition suc23 {Γ} : Tm23 Γ nat23 → Tm23 Γ nat23
 := λ t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec ,
   suc23 _ (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec).

Definition rec23 {Γ A} : Tm23 Γ nat23 → Tm23 Γ (arr23 nat23 (arr23 A A)) → Tm23 Γ A → Tm23 Γ A
 := λ t u v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23 ,
     rec23 _ _
         (t Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)
         (u Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23)
         (v Tm23 var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 case23 zero23 suc23 rec23).

Definition v023 {Γ A} : Tm23 (snoc23 Γ A) A
 := var23 vz23.

Definition v123 {Γ A B} : Tm23 (snoc23 (snoc23 Γ A) B) A
 := var23 (vs23 vz23).

Definition v223 {Γ A B C} : Tm23 (snoc23 (snoc23 (snoc23 Γ A) B) C) A
 := var23 (vs23 (vs23 vz23)).

Definition v323 {Γ A B C D} : Tm23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) A
 := var23 (vs23 (vs23 (vs23 vz23))).

Definition tbool23 : Ty23
 := sum23 top23 top23.

Definition ttrue23 {Γ} : Tm23 Γ tbool23
 := left23 tt23.

Definition tfalse23 {Γ} : Tm23 Γ tbool23
 := right23 tt23.

Definition ifthenelse23 {Γ A} : Tm23 Γ (arr23 tbool23 (arr23 A (arr23 A A)))
 := lam23 (lam23 (lam23 (case23 v223 (lam23 v223) (lam23 v123)))).

Definition times423 {Γ A} : Tm23 Γ (arr23 (arr23 A A) (arr23 A A))
  := lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023))))).

Definition add23 {Γ} : Tm23 Γ (arr23 nat23 (arr23 nat23 nat23))
 := lam23 (rec23 v023
      (lam23 (lam23 (lam23 (suc23 (app23 v123 v023)))))
      (lam23 v023)).

Definition mul23 {Γ} : Tm23 Γ (arr23 nat23 (arr23 nat23 nat23))
 := lam23 (rec23 v023
     (lam23 (lam23 (lam23 (app23 (app23 add23 (app23 v123 v023)) v023))))
     (lam23 zero23)).

Definition fact23 {Γ} : Tm23 Γ (arr23 nat23 nat23)
 := lam23 (rec23 v023 (lam23 (lam23 (app23 (app23 mul23 (suc23 v123)) v023)))
        (suc23 zero23)).

Require Import Coq.Unicode.Utf8.

Definition Ty24 : Set
 := ∀ (Ty24           : Set)
      (nat top bot  : Ty24)
      (arr prod sum : Ty24 → Ty24 → Ty24)
    , Ty24.

Definition nat24 : Ty24 := λ _ nat24 _ _ _ _ _ , nat24.
Definition top24 : Ty24 := λ _ _ top24 _ _ _ _ , top24.
Definition bot24 : Ty24 := λ _ _ _ bot24 _ _ _ , bot24.

Definition arr24 : Ty24 → Ty24 → Ty24
 := λ A B Ty24 nat24 top24 bot24 arr24 prod sum ,
     arr24 (A Ty24 nat24 top24 bot24 arr24 prod sum) (B Ty24 nat24 top24 bot24 arr24 prod sum).

Definition prod24 : Ty24 → Ty24 → Ty24
 := λ A B Ty24 nat24 top24 bot24 arr24 prod24 sum ,
     prod24 (A Ty24 nat24 top24 bot24 arr24 prod24 sum) (B Ty24 nat24 top24 bot24 arr24 prod24 sum).

Definition sum24 : Ty24 → Ty24 → Ty24
 := λ A B Ty24 nat24 top24 bot24 arr24 prod24 sum24 ,
     sum24 (A Ty24 nat24 top24 bot24 arr24 prod24 sum24) (B Ty24 nat24 top24 bot24 arr24 prod24 sum24).

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
     (tt    : ∀ Γ       , Tm24 Γ top24)
     (pair  : ∀ Γ A B   , Tm24 Γ A → Tm24 Γ B → Tm24 Γ (prod24 A B))
     (fst   : ∀ Γ A B   , Tm24 Γ (prod24 A B) → Tm24 Γ A)
     (snd   : ∀ Γ A B   , Tm24 Γ (prod24 A B) → Tm24 Γ B)
     (left  : ∀ Γ A B   , Tm24 Γ A → Tm24 Γ (sum24 A B))
     (right : ∀ Γ A B   , Tm24 Γ B → Tm24 Γ (sum24 A B))
     (case  : ∀ Γ A B C , Tm24 Γ (sum24 A B) → Tm24 Γ (arr24 A C) → Tm24 Γ (arr24 B C) → Tm24 Γ C)
     (zero  : ∀ Γ       , Tm24 Γ nat24)
     (suc   : ∀ Γ       , Tm24 Γ nat24 → Tm24 Γ nat24)
     (rec   : ∀ Γ A     , Tm24 Γ nat24 → Tm24 Γ (arr24 nat24 (arr24 A A)) → Tm24 Γ A → Tm24 Γ A)
   , Tm24 Γ A.

Definition var24 {Γ A} : Var24 Γ A → Tm24 Γ A
 := λ x Tm24 var24 lam app tt pair fst snd left right case zero suc rec ,
     var24 _ _ x.

Definition lam24 {Γ A B} : Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B)
 := λ t Tm24 var24 lam24 app tt pair fst snd left right case zero suc rec ,
     lam24 _ _ _ (t Tm24 var24 lam24 app tt pair fst snd left right case zero suc rec).

Definition app24 {Γ A B} : Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B
 := λ t u Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec ,
     app24 _ _ _
         (t Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec)
         (u Tm24 var24 lam24 app24 tt pair fst snd left right case zero suc rec).

Definition tt24 {Γ} : Tm24 Γ top24
 := λ Tm24 var24 lam24 app24 tt24 pair fst snd left right case zero suc rec , tt24 _.

Definition pair24 {Γ A B} : Tm24 Γ A → Tm24 Γ B → Tm24 Γ (prod24 A B)
 := λ t u Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec ,
     pair24 _ _ _
          (t Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec)
          (u Tm24 var24 lam24 app24 tt24 pair24 fst snd left right case zero suc rec).

Definition fst24 {Γ A B} : Tm24 Γ (prod24 A B) → Tm24 Γ A
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd left right case zero suc rec ,
     fst24 _ _ _
         (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd left right case zero suc rec).

Definition snd24 {Γ A B} : Tm24 Γ (prod24 A B) → Tm24 Γ B
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left right case zero suc rec ,
     snd24 _ _ _
          (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left right case zero suc rec).

Definition left24 {Γ A B} : Tm24 Γ A → Tm24 Γ (sum24 A B)
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right case zero suc rec ,
     left24 _ _ _
          (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right case zero suc rec).

Definition right24 {Γ A B} : Tm24 Γ B → Tm24 Γ (sum24 A B)
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case zero suc rec ,
     right24 _ _ _
            (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case zero suc rec).

Definition case24 {Γ A B C} : Tm24 Γ (sum24 A B) → Tm24 Γ (arr24 A C) → Tm24 Γ (arr24 B C) → Tm24 Γ C
 := λ t u v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec ,
     case24 _ _ _ _
           (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)
           (u Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec)
           (v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero suc rec).

Definition zero24  {Γ} : Tm24 Γ nat24
 := λ Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc rec , zero24 _.

Definition suc24 {Γ} : Tm24 Γ nat24 → Tm24 Γ nat24
 := λ t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec ,
   suc24 _ (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec).

Definition rec24 {Γ A} : Tm24 Γ nat24 → Tm24 Γ (arr24 nat24 (arr24 A A)) → Tm24 Γ A → Tm24 Γ A
 := λ t u v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24 ,
     rec24 _ _
         (t Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)
         (u Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24)
         (v Tm24 var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 case24 zero24 suc24 rec24).

Definition v024 {Γ A} : Tm24 (snoc24 Γ A) A
 := var24 vz24.

Definition v124 {Γ A B} : Tm24 (snoc24 (snoc24 Γ A) B) A
 := var24 (vs24 vz24).

Definition v224 {Γ A B C} : Tm24 (snoc24 (snoc24 (snoc24 Γ A) B) C) A
 := var24 (vs24 (vs24 vz24)).

Definition v324 {Γ A B C D} : Tm24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) A
 := var24 (vs24 (vs24 (vs24 vz24))).

Definition tbool24 : Ty24
 := sum24 top24 top24.

Definition ttrue24 {Γ} : Tm24 Γ tbool24
 := left24 tt24.

Definition tfalse24 {Γ} : Tm24 Γ tbool24
 := right24 tt24.

Definition ifthenelse24 {Γ A} : Tm24 Γ (arr24 tbool24 (arr24 A (arr24 A A)))
 := lam24 (lam24 (lam24 (case24 v224 (lam24 v224) (lam24 v124)))).

Definition times424 {Γ A} : Tm24 Γ (arr24 (arr24 A A) (arr24 A A))
  := lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024))))).

Definition add24 {Γ} : Tm24 Γ (arr24 nat24 (arr24 nat24 nat24))
 := lam24 (rec24 v024
      (lam24 (lam24 (lam24 (suc24 (app24 v124 v024)))))
      (lam24 v024)).

Definition mul24 {Γ} : Tm24 Γ (arr24 nat24 (arr24 nat24 nat24))
 := lam24 (rec24 v024
     (lam24 (lam24 (lam24 (app24 (app24 add24 (app24 v124 v024)) v024))))
     (lam24 zero24)).

Definition fact24 {Γ} : Tm24 Γ (arr24 nat24 nat24)
 := lam24 (rec24 v024 (lam24 (lam24 (app24 (app24 mul24 (suc24 v124)) v024)))
        (suc24 zero24)).

Require Import Coq.Unicode.Utf8.

Definition Ty25 : Set
 := ∀ (Ty25           : Set)
      (nat top bot  : Ty25)
      (arr prod sum : Ty25 → Ty25 → Ty25)
    , Ty25.

Definition nat25 : Ty25 := λ _ nat25 _ _ _ _ _ , nat25.
Definition top25 : Ty25 := λ _ _ top25 _ _ _ _ , top25.
Definition bot25 : Ty25 := λ _ _ _ bot25 _ _ _ , bot25.

Definition arr25 : Ty25 → Ty25 → Ty25
 := λ A B Ty25 nat25 top25 bot25 arr25 prod sum ,
     arr25 (A Ty25 nat25 top25 bot25 arr25 prod sum) (B Ty25 nat25 top25 bot25 arr25 prod sum).

Definition prod25 : Ty25 → Ty25 → Ty25
 := λ A B Ty25 nat25 top25 bot25 arr25 prod25 sum ,
     prod25 (A Ty25 nat25 top25 bot25 arr25 prod25 sum) (B Ty25 nat25 top25 bot25 arr25 prod25 sum).

Definition sum25 : Ty25 → Ty25 → Ty25
 := λ A B Ty25 nat25 top25 bot25 arr25 prod25 sum25 ,
     sum25 (A Ty25 nat25 top25 bot25 arr25 prod25 sum25) (B Ty25 nat25 top25 bot25 arr25 prod25 sum25).

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
     (tt    : ∀ Γ       , Tm25 Γ top25)
     (pair  : ∀ Γ A B   , Tm25 Γ A → Tm25 Γ B → Tm25 Γ (prod25 A B))
     (fst   : ∀ Γ A B   , Tm25 Γ (prod25 A B) → Tm25 Γ A)
     (snd   : ∀ Γ A B   , Tm25 Γ (prod25 A B) → Tm25 Γ B)
     (left  : ∀ Γ A B   , Tm25 Γ A → Tm25 Γ (sum25 A B))
     (right : ∀ Γ A B   , Tm25 Γ B → Tm25 Γ (sum25 A B))
     (case  : ∀ Γ A B C , Tm25 Γ (sum25 A B) → Tm25 Γ (arr25 A C) → Tm25 Γ (arr25 B C) → Tm25 Γ C)
     (zero  : ∀ Γ       , Tm25 Γ nat25)
     (suc   : ∀ Γ       , Tm25 Γ nat25 → Tm25 Γ nat25)
     (rec   : ∀ Γ A     , Tm25 Γ nat25 → Tm25 Γ (arr25 nat25 (arr25 A A)) → Tm25 Γ A → Tm25 Γ A)
   , Tm25 Γ A.

Definition var25 {Γ A} : Var25 Γ A → Tm25 Γ A
 := λ x Tm25 var25 lam app tt pair fst snd left right case zero suc rec ,
     var25 _ _ x.

Definition lam25 {Γ A B} : Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B)
 := λ t Tm25 var25 lam25 app tt pair fst snd left right case zero suc rec ,
     lam25 _ _ _ (t Tm25 var25 lam25 app tt pair fst snd left right case zero suc rec).

Definition app25 {Γ A B} : Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B
 := λ t u Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec ,
     app25 _ _ _
         (t Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec)
         (u Tm25 var25 lam25 app25 tt pair fst snd left right case zero suc rec).

Definition tt25 {Γ} : Tm25 Γ top25
 := λ Tm25 var25 lam25 app25 tt25 pair fst snd left right case zero suc rec , tt25 _.

Definition pair25 {Γ A B} : Tm25 Γ A → Tm25 Γ B → Tm25 Γ (prod25 A B)
 := λ t u Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec ,
     pair25 _ _ _
          (t Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec)
          (u Tm25 var25 lam25 app25 tt25 pair25 fst snd left right case zero suc rec).

Definition fst25 {Γ A B} : Tm25 Γ (prod25 A B) → Tm25 Γ A
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd left right case zero suc rec ,
     fst25 _ _ _
         (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd left right case zero suc rec).

Definition snd25 {Γ A B} : Tm25 Γ (prod25 A B) → Tm25 Γ B
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left right case zero suc rec ,
     snd25 _ _ _
          (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left right case zero suc rec).

Definition left25 {Γ A B} : Tm25 Γ A → Tm25 Γ (sum25 A B)
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right case zero suc rec ,
     left25 _ _ _
          (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right case zero suc rec).

Definition right25 {Γ A B} : Tm25 Γ B → Tm25 Γ (sum25 A B)
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case zero suc rec ,
     right25 _ _ _
            (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case zero suc rec).

Definition case25 {Γ A B C} : Tm25 Γ (sum25 A B) → Tm25 Γ (arr25 A C) → Tm25 Γ (arr25 B C) → Tm25 Γ C
 := λ t u v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec ,
     case25 _ _ _ _
           (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)
           (u Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec)
           (v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero suc rec).

Definition zero25  {Γ} : Tm25 Γ nat25
 := λ Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc rec , zero25 _.

Definition suc25 {Γ} : Tm25 Γ nat25 → Tm25 Γ nat25
 := λ t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec ,
   suc25 _ (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec).

Definition rec25 {Γ A} : Tm25 Γ nat25 → Tm25 Γ (arr25 nat25 (arr25 A A)) → Tm25 Γ A → Tm25 Γ A
 := λ t u v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25 ,
     rec25 _ _
         (t Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)
         (u Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25)
         (v Tm25 var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 case25 zero25 suc25 rec25).

Definition v025 {Γ A} : Tm25 (snoc25 Γ A) A
 := var25 vz25.

Definition v125 {Γ A B} : Tm25 (snoc25 (snoc25 Γ A) B) A
 := var25 (vs25 vz25).

Definition v225 {Γ A B C} : Tm25 (snoc25 (snoc25 (snoc25 Γ A) B) C) A
 := var25 (vs25 (vs25 vz25)).

Definition v325 {Γ A B C D} : Tm25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) A
 := var25 (vs25 (vs25 (vs25 vz25))).

Definition tbool25 : Ty25
 := sum25 top25 top25.

Definition ttrue25 {Γ} : Tm25 Γ tbool25
 := left25 tt25.

Definition tfalse25 {Γ} : Tm25 Γ tbool25
 := right25 tt25.

Definition ifthenelse25 {Γ A} : Tm25 Γ (arr25 tbool25 (arr25 A (arr25 A A)))
 := lam25 (lam25 (lam25 (case25 v225 (lam25 v225) (lam25 v125)))).

Definition times425 {Γ A} : Tm25 Γ (arr25 (arr25 A A) (arr25 A A))
  := lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025))))).

Definition add25 {Γ} : Tm25 Γ (arr25 nat25 (arr25 nat25 nat25))
 := lam25 (rec25 v025
      (lam25 (lam25 (lam25 (suc25 (app25 v125 v025)))))
      (lam25 v025)).

Definition mul25 {Γ} : Tm25 Γ (arr25 nat25 (arr25 nat25 nat25))
 := lam25 (rec25 v025
     (lam25 (lam25 (lam25 (app25 (app25 add25 (app25 v125 v025)) v025))))
     (lam25 zero25)).

Definition fact25 {Γ} : Tm25 Γ (arr25 nat25 nat25)
 := lam25 (rec25 v025 (lam25 (lam25 (app25 (app25 mul25 (suc25 v125)) v025)))
        (suc25 zero25)).

Require Import Coq.Unicode.Utf8.

Definition Ty26 : Set
 := ∀ (Ty26           : Set)
      (nat top bot  : Ty26)
      (arr prod sum : Ty26 → Ty26 → Ty26)
    , Ty26.

Definition nat26 : Ty26 := λ _ nat26 _ _ _ _ _ , nat26.
Definition top26 : Ty26 := λ _ _ top26 _ _ _ _ , top26.
Definition bot26 : Ty26 := λ _ _ _ bot26 _ _ _ , bot26.

Definition arr26 : Ty26 → Ty26 → Ty26
 := λ A B Ty26 nat26 top26 bot26 arr26 prod sum ,
     arr26 (A Ty26 nat26 top26 bot26 arr26 prod sum) (B Ty26 nat26 top26 bot26 arr26 prod sum).

Definition prod26 : Ty26 → Ty26 → Ty26
 := λ A B Ty26 nat26 top26 bot26 arr26 prod26 sum ,
     prod26 (A Ty26 nat26 top26 bot26 arr26 prod26 sum) (B Ty26 nat26 top26 bot26 arr26 prod26 sum).

Definition sum26 : Ty26 → Ty26 → Ty26
 := λ A B Ty26 nat26 top26 bot26 arr26 prod26 sum26 ,
     sum26 (A Ty26 nat26 top26 bot26 arr26 prod26 sum26) (B Ty26 nat26 top26 bot26 arr26 prod26 sum26).

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
     (tt    : ∀ Γ       , Tm26 Γ top26)
     (pair  : ∀ Γ A B   , Tm26 Γ A → Tm26 Γ B → Tm26 Γ (prod26 A B))
     (fst   : ∀ Γ A B   , Tm26 Γ (prod26 A B) → Tm26 Γ A)
     (snd   : ∀ Γ A B   , Tm26 Γ (prod26 A B) → Tm26 Γ B)
     (left  : ∀ Γ A B   , Tm26 Γ A → Tm26 Γ (sum26 A B))
     (right : ∀ Γ A B   , Tm26 Γ B → Tm26 Γ (sum26 A B))
     (case  : ∀ Γ A B C , Tm26 Γ (sum26 A B) → Tm26 Γ (arr26 A C) → Tm26 Γ (arr26 B C) → Tm26 Γ C)
     (zero  : ∀ Γ       , Tm26 Γ nat26)
     (suc   : ∀ Γ       , Tm26 Γ nat26 → Tm26 Γ nat26)
     (rec   : ∀ Γ A     , Tm26 Γ nat26 → Tm26 Γ (arr26 nat26 (arr26 A A)) → Tm26 Γ A → Tm26 Γ A)
   , Tm26 Γ A.

Definition var26 {Γ A} : Var26 Γ A → Tm26 Γ A
 := λ x Tm26 var26 lam app tt pair fst snd left right case zero suc rec ,
     var26 _ _ x.

Definition lam26 {Γ A B} : Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B)
 := λ t Tm26 var26 lam26 app tt pair fst snd left right case zero suc rec ,
     lam26 _ _ _ (t Tm26 var26 lam26 app tt pair fst snd left right case zero suc rec).

Definition app26 {Γ A B} : Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B
 := λ t u Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec ,
     app26 _ _ _
         (t Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec)
         (u Tm26 var26 lam26 app26 tt pair fst snd left right case zero suc rec).

Definition tt26 {Γ} : Tm26 Γ top26
 := λ Tm26 var26 lam26 app26 tt26 pair fst snd left right case zero suc rec , tt26 _.

Definition pair26 {Γ A B} : Tm26 Γ A → Tm26 Γ B → Tm26 Γ (prod26 A B)
 := λ t u Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec ,
     pair26 _ _ _
          (t Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec)
          (u Tm26 var26 lam26 app26 tt26 pair26 fst snd left right case zero suc rec).

Definition fst26 {Γ A B} : Tm26 Γ (prod26 A B) → Tm26 Γ A
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd left right case zero suc rec ,
     fst26 _ _ _
         (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd left right case zero suc rec).

Definition snd26 {Γ A B} : Tm26 Γ (prod26 A B) → Tm26 Γ B
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left right case zero suc rec ,
     snd26 _ _ _
          (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left right case zero suc rec).

Definition left26 {Γ A B} : Tm26 Γ A → Tm26 Γ (sum26 A B)
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right case zero suc rec ,
     left26 _ _ _
          (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right case zero suc rec).

Definition right26 {Γ A B} : Tm26 Γ B → Tm26 Γ (sum26 A B)
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case zero suc rec ,
     right26 _ _ _
            (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case zero suc rec).

Definition case26 {Γ A B C} : Tm26 Γ (sum26 A B) → Tm26 Γ (arr26 A C) → Tm26 Γ (arr26 B C) → Tm26 Γ C
 := λ t u v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec ,
     case26 _ _ _ _
           (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)
           (u Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec)
           (v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero suc rec).

Definition zero26  {Γ} : Tm26 Γ nat26
 := λ Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc rec , zero26 _.

Definition suc26 {Γ} : Tm26 Γ nat26 → Tm26 Γ nat26
 := λ t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec ,
   suc26 _ (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec).

Definition rec26 {Γ A} : Tm26 Γ nat26 → Tm26 Γ (arr26 nat26 (arr26 A A)) → Tm26 Γ A → Tm26 Γ A
 := λ t u v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26 ,
     rec26 _ _
         (t Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)
         (u Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26)
         (v Tm26 var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 case26 zero26 suc26 rec26).

Definition v026 {Γ A} : Tm26 (snoc26 Γ A) A
 := var26 vz26.

Definition v126 {Γ A B} : Tm26 (snoc26 (snoc26 Γ A) B) A
 := var26 (vs26 vz26).

Definition v226 {Γ A B C} : Tm26 (snoc26 (snoc26 (snoc26 Γ A) B) C) A
 := var26 (vs26 (vs26 vz26)).

Definition v326 {Γ A B C D} : Tm26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) A
 := var26 (vs26 (vs26 (vs26 vz26))).

Definition tbool26 : Ty26
 := sum26 top26 top26.

Definition ttrue26 {Γ} : Tm26 Γ tbool26
 := left26 tt26.

Definition tfalse26 {Γ} : Tm26 Γ tbool26
 := right26 tt26.

Definition ifthenelse26 {Γ A} : Tm26 Γ (arr26 tbool26 (arr26 A (arr26 A A)))
 := lam26 (lam26 (lam26 (case26 v226 (lam26 v226) (lam26 v126)))).

Definition times426 {Γ A} : Tm26 Γ (arr26 (arr26 A A) (arr26 A A))
  := lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026))))).

Definition add26 {Γ} : Tm26 Γ (arr26 nat26 (arr26 nat26 nat26))
 := lam26 (rec26 v026
      (lam26 (lam26 (lam26 (suc26 (app26 v126 v026)))))
      (lam26 v026)).

Definition mul26 {Γ} : Tm26 Γ (arr26 nat26 (arr26 nat26 nat26))
 := lam26 (rec26 v026
     (lam26 (lam26 (lam26 (app26 (app26 add26 (app26 v126 v026)) v026))))
     (lam26 zero26)).

Definition fact26 {Γ} : Tm26 Γ (arr26 nat26 nat26)
 := lam26 (rec26 v026 (lam26 (lam26 (app26 (app26 mul26 (suc26 v126)) v026)))
        (suc26 zero26)).

Require Import Coq.Unicode.Utf8.

Definition Ty27 : Set
 := ∀ (Ty27           : Set)
      (nat top bot  : Ty27)
      (arr prod sum : Ty27 → Ty27 → Ty27)
    , Ty27.

Definition nat27 : Ty27 := λ _ nat27 _ _ _ _ _ , nat27.
Definition top27 : Ty27 := λ _ _ top27 _ _ _ _ , top27.
Definition bot27 : Ty27 := λ _ _ _ bot27 _ _ _ , bot27.

Definition arr27 : Ty27 → Ty27 → Ty27
 := λ A B Ty27 nat27 top27 bot27 arr27 prod sum ,
     arr27 (A Ty27 nat27 top27 bot27 arr27 prod sum) (B Ty27 nat27 top27 bot27 arr27 prod sum).

Definition prod27 : Ty27 → Ty27 → Ty27
 := λ A B Ty27 nat27 top27 bot27 arr27 prod27 sum ,
     prod27 (A Ty27 nat27 top27 bot27 arr27 prod27 sum) (B Ty27 nat27 top27 bot27 arr27 prod27 sum).

Definition sum27 : Ty27 → Ty27 → Ty27
 := λ A B Ty27 nat27 top27 bot27 arr27 prod27 sum27 ,
     sum27 (A Ty27 nat27 top27 bot27 arr27 prod27 sum27) (B Ty27 nat27 top27 bot27 arr27 prod27 sum27).

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
     (tt    : ∀ Γ       , Tm27 Γ top27)
     (pair  : ∀ Γ A B   , Tm27 Γ A → Tm27 Γ B → Tm27 Γ (prod27 A B))
     (fst   : ∀ Γ A B   , Tm27 Γ (prod27 A B) → Tm27 Γ A)
     (snd   : ∀ Γ A B   , Tm27 Γ (prod27 A B) → Tm27 Γ B)
     (left  : ∀ Γ A B   , Tm27 Γ A → Tm27 Γ (sum27 A B))
     (right : ∀ Γ A B   , Tm27 Γ B → Tm27 Γ (sum27 A B))
     (case  : ∀ Γ A B C , Tm27 Γ (sum27 A B) → Tm27 Γ (arr27 A C) → Tm27 Γ (arr27 B C) → Tm27 Γ C)
     (zero  : ∀ Γ       , Tm27 Γ nat27)
     (suc   : ∀ Γ       , Tm27 Γ nat27 → Tm27 Γ nat27)
     (rec   : ∀ Γ A     , Tm27 Γ nat27 → Tm27 Γ (arr27 nat27 (arr27 A A)) → Tm27 Γ A → Tm27 Γ A)
   , Tm27 Γ A.

Definition var27 {Γ A} : Var27 Γ A → Tm27 Γ A
 := λ x Tm27 var27 lam app tt pair fst snd left right case zero suc rec ,
     var27 _ _ x.

Definition lam27 {Γ A B} : Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B)
 := λ t Tm27 var27 lam27 app tt pair fst snd left right case zero suc rec ,
     lam27 _ _ _ (t Tm27 var27 lam27 app tt pair fst snd left right case zero suc rec).

Definition app27 {Γ A B} : Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B
 := λ t u Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec ,
     app27 _ _ _
         (t Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec)
         (u Tm27 var27 lam27 app27 tt pair fst snd left right case zero suc rec).

Definition tt27 {Γ} : Tm27 Γ top27
 := λ Tm27 var27 lam27 app27 tt27 pair fst snd left right case zero suc rec , tt27 _.

Definition pair27 {Γ A B} : Tm27 Γ A → Tm27 Γ B → Tm27 Γ (prod27 A B)
 := λ t u Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec ,
     pair27 _ _ _
          (t Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec)
          (u Tm27 var27 lam27 app27 tt27 pair27 fst snd left right case zero suc rec).

Definition fst27 {Γ A B} : Tm27 Γ (prod27 A B) → Tm27 Γ A
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd left right case zero suc rec ,
     fst27 _ _ _
         (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd left right case zero suc rec).

Definition snd27 {Γ A B} : Tm27 Γ (prod27 A B) → Tm27 Γ B
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left right case zero suc rec ,
     snd27 _ _ _
          (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left right case zero suc rec).

Definition left27 {Γ A B} : Tm27 Γ A → Tm27 Γ (sum27 A B)
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right case zero suc rec ,
     left27 _ _ _
          (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right case zero suc rec).

Definition right27 {Γ A B} : Tm27 Γ B → Tm27 Γ (sum27 A B)
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case zero suc rec ,
     right27 _ _ _
            (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case zero suc rec).

Definition case27 {Γ A B C} : Tm27 Γ (sum27 A B) → Tm27 Γ (arr27 A C) → Tm27 Γ (arr27 B C) → Tm27 Γ C
 := λ t u v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec ,
     case27 _ _ _ _
           (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)
           (u Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec)
           (v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero suc rec).

Definition zero27  {Γ} : Tm27 Γ nat27
 := λ Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc rec , zero27 _.

Definition suc27 {Γ} : Tm27 Γ nat27 → Tm27 Γ nat27
 := λ t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec ,
   suc27 _ (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec).

Definition rec27 {Γ A} : Tm27 Γ nat27 → Tm27 Γ (arr27 nat27 (arr27 A A)) → Tm27 Γ A → Tm27 Γ A
 := λ t u v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27 ,
     rec27 _ _
         (t Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)
         (u Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27)
         (v Tm27 var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 case27 zero27 suc27 rec27).

Definition v027 {Γ A} : Tm27 (snoc27 Γ A) A
 := var27 vz27.

Definition v127 {Γ A B} : Tm27 (snoc27 (snoc27 Γ A) B) A
 := var27 (vs27 vz27).

Definition v227 {Γ A B C} : Tm27 (snoc27 (snoc27 (snoc27 Γ A) B) C) A
 := var27 (vs27 (vs27 vz27)).

Definition v327 {Γ A B C D} : Tm27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) A
 := var27 (vs27 (vs27 (vs27 vz27))).

Definition tbool27 : Ty27
 := sum27 top27 top27.

Definition ttrue27 {Γ} : Tm27 Γ tbool27
 := left27 tt27.

Definition tfalse27 {Γ} : Tm27 Γ tbool27
 := right27 tt27.

Definition ifthenelse27 {Γ A} : Tm27 Γ (arr27 tbool27 (arr27 A (arr27 A A)))
 := lam27 (lam27 (lam27 (case27 v227 (lam27 v227) (lam27 v127)))).

Definition times427 {Γ A} : Tm27 Γ (arr27 (arr27 A A) (arr27 A A))
  := lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027))))).

Definition add27 {Γ} : Tm27 Γ (arr27 nat27 (arr27 nat27 nat27))
 := lam27 (rec27 v027
      (lam27 (lam27 (lam27 (suc27 (app27 v127 v027)))))
      (lam27 v027)).

Definition mul27 {Γ} : Tm27 Γ (arr27 nat27 (arr27 nat27 nat27))
 := lam27 (rec27 v027
     (lam27 (lam27 (lam27 (app27 (app27 add27 (app27 v127 v027)) v027))))
     (lam27 zero27)).

Definition fact27 {Γ} : Tm27 Γ (arr27 nat27 nat27)
 := lam27 (rec27 v027 (lam27 (lam27 (app27 (app27 mul27 (suc27 v127)) v027)))
        (suc27 zero27)).

Require Import Coq.Unicode.Utf8.

Definition Ty28 : Set
 := ∀ (Ty28           : Set)
      (nat top bot  : Ty28)
      (arr prod sum : Ty28 → Ty28 → Ty28)
    , Ty28.

Definition nat28 : Ty28 := λ _ nat28 _ _ _ _ _ , nat28.
Definition top28 : Ty28 := λ _ _ top28 _ _ _ _ , top28.
Definition bot28 : Ty28 := λ _ _ _ bot28 _ _ _ , bot28.

Definition arr28 : Ty28 → Ty28 → Ty28
 := λ A B Ty28 nat28 top28 bot28 arr28 prod sum ,
     arr28 (A Ty28 nat28 top28 bot28 arr28 prod sum) (B Ty28 nat28 top28 bot28 arr28 prod sum).

Definition prod28 : Ty28 → Ty28 → Ty28
 := λ A B Ty28 nat28 top28 bot28 arr28 prod28 sum ,
     prod28 (A Ty28 nat28 top28 bot28 arr28 prod28 sum) (B Ty28 nat28 top28 bot28 arr28 prod28 sum).

Definition sum28 : Ty28 → Ty28 → Ty28
 := λ A B Ty28 nat28 top28 bot28 arr28 prod28 sum28 ,
     sum28 (A Ty28 nat28 top28 bot28 arr28 prod28 sum28) (B Ty28 nat28 top28 bot28 arr28 prod28 sum28).

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
     (tt    : ∀ Γ       , Tm28 Γ top28)
     (pair  : ∀ Γ A B   , Tm28 Γ A → Tm28 Γ B → Tm28 Γ (prod28 A B))
     (fst   : ∀ Γ A B   , Tm28 Γ (prod28 A B) → Tm28 Γ A)
     (snd   : ∀ Γ A B   , Tm28 Γ (prod28 A B) → Tm28 Γ B)
     (left  : ∀ Γ A B   , Tm28 Γ A → Tm28 Γ (sum28 A B))
     (right : ∀ Γ A B   , Tm28 Γ B → Tm28 Γ (sum28 A B))
     (case  : ∀ Γ A B C , Tm28 Γ (sum28 A B) → Tm28 Γ (arr28 A C) → Tm28 Γ (arr28 B C) → Tm28 Γ C)
     (zero  : ∀ Γ       , Tm28 Γ nat28)
     (suc   : ∀ Γ       , Tm28 Γ nat28 → Tm28 Γ nat28)
     (rec   : ∀ Γ A     , Tm28 Γ nat28 → Tm28 Γ (arr28 nat28 (arr28 A A)) → Tm28 Γ A → Tm28 Γ A)
   , Tm28 Γ A.

Definition var28 {Γ A} : Var28 Γ A → Tm28 Γ A
 := λ x Tm28 var28 lam app tt pair fst snd left right case zero suc rec ,
     var28 _ _ x.

Definition lam28 {Γ A B} : Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B)
 := λ t Tm28 var28 lam28 app tt pair fst snd left right case zero suc rec ,
     lam28 _ _ _ (t Tm28 var28 lam28 app tt pair fst snd left right case zero suc rec).

Definition app28 {Γ A B} : Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B
 := λ t u Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec ,
     app28 _ _ _
         (t Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec)
         (u Tm28 var28 lam28 app28 tt pair fst snd left right case zero suc rec).

Definition tt28 {Γ} : Tm28 Γ top28
 := λ Tm28 var28 lam28 app28 tt28 pair fst snd left right case zero suc rec , tt28 _.

Definition pair28 {Γ A B} : Tm28 Γ A → Tm28 Γ B → Tm28 Γ (prod28 A B)
 := λ t u Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec ,
     pair28 _ _ _
          (t Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec)
          (u Tm28 var28 lam28 app28 tt28 pair28 fst snd left right case zero suc rec).

Definition fst28 {Γ A B} : Tm28 Γ (prod28 A B) → Tm28 Γ A
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd left right case zero suc rec ,
     fst28 _ _ _
         (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd left right case zero suc rec).

Definition snd28 {Γ A B} : Tm28 Γ (prod28 A B) → Tm28 Γ B
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left right case zero suc rec ,
     snd28 _ _ _
          (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left right case zero suc rec).

Definition left28 {Γ A B} : Tm28 Γ A → Tm28 Γ (sum28 A B)
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right case zero suc rec ,
     left28 _ _ _
          (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right case zero suc rec).

Definition right28 {Γ A B} : Tm28 Γ B → Tm28 Γ (sum28 A B)
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case zero suc rec ,
     right28 _ _ _
            (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case zero suc rec).

Definition case28 {Γ A B C} : Tm28 Γ (sum28 A B) → Tm28 Γ (arr28 A C) → Tm28 Γ (arr28 B C) → Tm28 Γ C
 := λ t u v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec ,
     case28 _ _ _ _
           (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)
           (u Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec)
           (v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero suc rec).

Definition zero28  {Γ} : Tm28 Γ nat28
 := λ Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc rec , zero28 _.

Definition suc28 {Γ} : Tm28 Γ nat28 → Tm28 Γ nat28
 := λ t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec ,
   suc28 _ (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec).

Definition rec28 {Γ A} : Tm28 Γ nat28 → Tm28 Γ (arr28 nat28 (arr28 A A)) → Tm28 Γ A → Tm28 Γ A
 := λ t u v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28 ,
     rec28 _ _
         (t Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)
         (u Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28)
         (v Tm28 var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 case28 zero28 suc28 rec28).

Definition v028 {Γ A} : Tm28 (snoc28 Γ A) A
 := var28 vz28.

Definition v128 {Γ A B} : Tm28 (snoc28 (snoc28 Γ A) B) A
 := var28 (vs28 vz28).

Definition v228 {Γ A B C} : Tm28 (snoc28 (snoc28 (snoc28 Γ A) B) C) A
 := var28 (vs28 (vs28 vz28)).

Definition v328 {Γ A B C D} : Tm28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) A
 := var28 (vs28 (vs28 (vs28 vz28))).

Definition tbool28 : Ty28
 := sum28 top28 top28.

Definition ttrue28 {Γ} : Tm28 Γ tbool28
 := left28 tt28.

Definition tfalse28 {Γ} : Tm28 Γ tbool28
 := right28 tt28.

Definition ifthenelse28 {Γ A} : Tm28 Γ (arr28 tbool28 (arr28 A (arr28 A A)))
 := lam28 (lam28 (lam28 (case28 v228 (lam28 v228) (lam28 v128)))).

Definition times428 {Γ A} : Tm28 Γ (arr28 (arr28 A A) (arr28 A A))
  := lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028))))).

Definition add28 {Γ} : Tm28 Γ (arr28 nat28 (arr28 nat28 nat28))
 := lam28 (rec28 v028
      (lam28 (lam28 (lam28 (suc28 (app28 v128 v028)))))
      (lam28 v028)).

Definition mul28 {Γ} : Tm28 Γ (arr28 nat28 (arr28 nat28 nat28))
 := lam28 (rec28 v028
     (lam28 (lam28 (lam28 (app28 (app28 add28 (app28 v128 v028)) v028))))
     (lam28 zero28)).

Definition fact28 {Γ} : Tm28 Γ (arr28 nat28 nat28)
 := lam28 (rec28 v028 (lam28 (lam28 (app28 (app28 mul28 (suc28 v128)) v028)))
        (suc28 zero28)).

Require Import Coq.Unicode.Utf8.

Definition Ty29 : Set
 := ∀ (Ty29           : Set)
      (nat top bot  : Ty29)
      (arr prod sum : Ty29 → Ty29 → Ty29)
    , Ty29.

Definition nat29 : Ty29 := λ _ nat29 _ _ _ _ _ , nat29.
Definition top29 : Ty29 := λ _ _ top29 _ _ _ _ , top29.
Definition bot29 : Ty29 := λ _ _ _ bot29 _ _ _ , bot29.

Definition arr29 : Ty29 → Ty29 → Ty29
 := λ A B Ty29 nat29 top29 bot29 arr29 prod sum ,
     arr29 (A Ty29 nat29 top29 bot29 arr29 prod sum) (B Ty29 nat29 top29 bot29 arr29 prod sum).

Definition prod29 : Ty29 → Ty29 → Ty29
 := λ A B Ty29 nat29 top29 bot29 arr29 prod29 sum ,
     prod29 (A Ty29 nat29 top29 bot29 arr29 prod29 sum) (B Ty29 nat29 top29 bot29 arr29 prod29 sum).

Definition sum29 : Ty29 → Ty29 → Ty29
 := λ A B Ty29 nat29 top29 bot29 arr29 prod29 sum29 ,
     sum29 (A Ty29 nat29 top29 bot29 arr29 prod29 sum29) (B Ty29 nat29 top29 bot29 arr29 prod29 sum29).

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
     (tt    : ∀ Γ       , Tm29 Γ top29)
     (pair  : ∀ Γ A B   , Tm29 Γ A → Tm29 Γ B → Tm29 Γ (prod29 A B))
     (fst   : ∀ Γ A B   , Tm29 Γ (prod29 A B) → Tm29 Γ A)
     (snd   : ∀ Γ A B   , Tm29 Γ (prod29 A B) → Tm29 Γ B)
     (left  : ∀ Γ A B   , Tm29 Γ A → Tm29 Γ (sum29 A B))
     (right : ∀ Γ A B   , Tm29 Γ B → Tm29 Γ (sum29 A B))
     (case  : ∀ Γ A B C , Tm29 Γ (sum29 A B) → Tm29 Γ (arr29 A C) → Tm29 Γ (arr29 B C) → Tm29 Γ C)
     (zero  : ∀ Γ       , Tm29 Γ nat29)
     (suc   : ∀ Γ       , Tm29 Γ nat29 → Tm29 Γ nat29)
     (rec   : ∀ Γ A     , Tm29 Γ nat29 → Tm29 Γ (arr29 nat29 (arr29 A A)) → Tm29 Γ A → Tm29 Γ A)
   , Tm29 Γ A.

Definition var29 {Γ A} : Var29 Γ A → Tm29 Γ A
 := λ x Tm29 var29 lam app tt pair fst snd left right case zero suc rec ,
     var29 _ _ x.

Definition lam29 {Γ A B} : Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B)
 := λ t Tm29 var29 lam29 app tt pair fst snd left right case zero suc rec ,
     lam29 _ _ _ (t Tm29 var29 lam29 app tt pair fst snd left right case zero suc rec).

Definition app29 {Γ A B} : Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B
 := λ t u Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec ,
     app29 _ _ _
         (t Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec)
         (u Tm29 var29 lam29 app29 tt pair fst snd left right case zero suc rec).

Definition tt29 {Γ} : Tm29 Γ top29
 := λ Tm29 var29 lam29 app29 tt29 pair fst snd left right case zero suc rec , tt29 _.

Definition pair29 {Γ A B} : Tm29 Γ A → Tm29 Γ B → Tm29 Γ (prod29 A B)
 := λ t u Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec ,
     pair29 _ _ _
          (t Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec)
          (u Tm29 var29 lam29 app29 tt29 pair29 fst snd left right case zero suc rec).

Definition fst29 {Γ A B} : Tm29 Γ (prod29 A B) → Tm29 Γ A
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd left right case zero suc rec ,
     fst29 _ _ _
         (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd left right case zero suc rec).

Definition snd29 {Γ A B} : Tm29 Γ (prod29 A B) → Tm29 Γ B
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left right case zero suc rec ,
     snd29 _ _ _
          (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left right case zero suc rec).

Definition left29 {Γ A B} : Tm29 Γ A → Tm29 Γ (sum29 A B)
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right case zero suc rec ,
     left29 _ _ _
          (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right case zero suc rec).

Definition right29 {Γ A B} : Tm29 Γ B → Tm29 Γ (sum29 A B)
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case zero suc rec ,
     right29 _ _ _
            (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case zero suc rec).

Definition case29 {Γ A B C} : Tm29 Γ (sum29 A B) → Tm29 Γ (arr29 A C) → Tm29 Γ (arr29 B C) → Tm29 Γ C
 := λ t u v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec ,
     case29 _ _ _ _
           (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)
           (u Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec)
           (v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero suc rec).

Definition zero29  {Γ} : Tm29 Γ nat29
 := λ Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc rec , zero29 _.

Definition suc29 {Γ} : Tm29 Γ nat29 → Tm29 Γ nat29
 := λ t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec ,
   suc29 _ (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec).

Definition rec29 {Γ A} : Tm29 Γ nat29 → Tm29 Γ (arr29 nat29 (arr29 A A)) → Tm29 Γ A → Tm29 Γ A
 := λ t u v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29 ,
     rec29 _ _
         (t Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)
         (u Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29)
         (v Tm29 var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 case29 zero29 suc29 rec29).

Definition v029 {Γ A} : Tm29 (snoc29 Γ A) A
 := var29 vz29.

Definition v129 {Γ A B} : Tm29 (snoc29 (snoc29 Γ A) B) A
 := var29 (vs29 vz29).

Definition v229 {Γ A B C} : Tm29 (snoc29 (snoc29 (snoc29 Γ A) B) C) A
 := var29 (vs29 (vs29 vz29)).

Definition v329 {Γ A B C D} : Tm29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) A
 := var29 (vs29 (vs29 (vs29 vz29))).

Definition tbool29 : Ty29
 := sum29 top29 top29.

Definition ttrue29 {Γ} : Tm29 Γ tbool29
 := left29 tt29.

Definition tfalse29 {Γ} : Tm29 Γ tbool29
 := right29 tt29.

Definition ifthenelse29 {Γ A} : Tm29 Γ (arr29 tbool29 (arr29 A (arr29 A A)))
 := lam29 (lam29 (lam29 (case29 v229 (lam29 v229) (lam29 v129)))).

Definition times429 {Γ A} : Tm29 Γ (arr29 (arr29 A A) (arr29 A A))
  := lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029))))).

Definition add29 {Γ} : Tm29 Γ (arr29 nat29 (arr29 nat29 nat29))
 := lam29 (rec29 v029
      (lam29 (lam29 (lam29 (suc29 (app29 v129 v029)))))
      (lam29 v029)).

Definition mul29 {Γ} : Tm29 Γ (arr29 nat29 (arr29 nat29 nat29))
 := lam29 (rec29 v029
     (lam29 (lam29 (lam29 (app29 (app29 add29 (app29 v129 v029)) v029))))
     (lam29 zero29)).

Definition fact29 {Γ} : Tm29 Γ (arr29 nat29 nat29)
 := lam29 (rec29 v029 (lam29 (lam29 (app29 (app29 mul29 (suc29 v129)) v029)))
        (suc29 zero29)).

Require Import Coq.Unicode.Utf8.

Definition Ty30 : Set
 := ∀ (Ty30           : Set)
      (nat top bot  : Ty30)
      (arr prod sum : Ty30 → Ty30 → Ty30)
    , Ty30.

Definition nat30 : Ty30 := λ _ nat30 _ _ _ _ _ , nat30.
Definition top30 : Ty30 := λ _ _ top30 _ _ _ _ , top30.
Definition bot30 : Ty30 := λ _ _ _ bot30 _ _ _ , bot30.

Definition arr30 : Ty30 → Ty30 → Ty30
 := λ A B Ty30 nat30 top30 bot30 arr30 prod sum ,
     arr30 (A Ty30 nat30 top30 bot30 arr30 prod sum) (B Ty30 nat30 top30 bot30 arr30 prod sum).

Definition prod30 : Ty30 → Ty30 → Ty30
 := λ A B Ty30 nat30 top30 bot30 arr30 prod30 sum ,
     prod30 (A Ty30 nat30 top30 bot30 arr30 prod30 sum) (B Ty30 nat30 top30 bot30 arr30 prod30 sum).

Definition sum30 : Ty30 → Ty30 → Ty30
 := λ A B Ty30 nat30 top30 bot30 arr30 prod30 sum30 ,
     sum30 (A Ty30 nat30 top30 bot30 arr30 prod30 sum30) (B Ty30 nat30 top30 bot30 arr30 prod30 sum30).

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
     (tt    : ∀ Γ       , Tm30 Γ top30)
     (pair  : ∀ Γ A B   , Tm30 Γ A → Tm30 Γ B → Tm30 Γ (prod30 A B))
     (fst   : ∀ Γ A B   , Tm30 Γ (prod30 A B) → Tm30 Γ A)
     (snd   : ∀ Γ A B   , Tm30 Γ (prod30 A B) → Tm30 Γ B)
     (left  : ∀ Γ A B   , Tm30 Γ A → Tm30 Γ (sum30 A B))
     (right : ∀ Γ A B   , Tm30 Γ B → Tm30 Γ (sum30 A B))
     (case  : ∀ Γ A B C , Tm30 Γ (sum30 A B) → Tm30 Γ (arr30 A C) → Tm30 Γ (arr30 B C) → Tm30 Γ C)
     (zero  : ∀ Γ       , Tm30 Γ nat30)
     (suc   : ∀ Γ       , Tm30 Γ nat30 → Tm30 Γ nat30)
     (rec   : ∀ Γ A     , Tm30 Γ nat30 → Tm30 Γ (arr30 nat30 (arr30 A A)) → Tm30 Γ A → Tm30 Γ A)
   , Tm30 Γ A.

Definition var30 {Γ A} : Var30 Γ A → Tm30 Γ A
 := λ x Tm30 var30 lam app tt pair fst snd left right case zero suc rec ,
     var30 _ _ x.

Definition lam30 {Γ A B} : Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B)
 := λ t Tm30 var30 lam30 app tt pair fst snd left right case zero suc rec ,
     lam30 _ _ _ (t Tm30 var30 lam30 app tt pair fst snd left right case zero suc rec).

Definition app30 {Γ A B} : Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B
 := λ t u Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec ,
     app30 _ _ _
         (t Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec)
         (u Tm30 var30 lam30 app30 tt pair fst snd left right case zero suc rec).

Definition tt30 {Γ} : Tm30 Γ top30
 := λ Tm30 var30 lam30 app30 tt30 pair fst snd left right case zero suc rec , tt30 _.

Definition pair30 {Γ A B} : Tm30 Γ A → Tm30 Γ B → Tm30 Γ (prod30 A B)
 := λ t u Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec ,
     pair30 _ _ _
          (t Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec)
          (u Tm30 var30 lam30 app30 tt30 pair30 fst snd left right case zero suc rec).

Definition fst30 {Γ A B} : Tm30 Γ (prod30 A B) → Tm30 Γ A
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd left right case zero suc rec ,
     fst30 _ _ _
         (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd left right case zero suc rec).

Definition snd30 {Γ A B} : Tm30 Γ (prod30 A B) → Tm30 Γ B
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left right case zero suc rec ,
     snd30 _ _ _
          (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left right case zero suc rec).

Definition left30 {Γ A B} : Tm30 Γ A → Tm30 Γ (sum30 A B)
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right case zero suc rec ,
     left30 _ _ _
          (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right case zero suc rec).

Definition right30 {Γ A B} : Tm30 Γ B → Tm30 Γ (sum30 A B)
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case zero suc rec ,
     right30 _ _ _
            (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case zero suc rec).

Definition case30 {Γ A B C} : Tm30 Γ (sum30 A B) → Tm30 Γ (arr30 A C) → Tm30 Γ (arr30 B C) → Tm30 Γ C
 := λ t u v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec ,
     case30 _ _ _ _
           (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)
           (u Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec)
           (v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero suc rec).

Definition zero30  {Γ} : Tm30 Γ nat30
 := λ Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc rec , zero30 _.

Definition suc30 {Γ} : Tm30 Γ nat30 → Tm30 Γ nat30
 := λ t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec ,
   suc30 _ (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec).

Definition rec30 {Γ A} : Tm30 Γ nat30 → Tm30 Γ (arr30 nat30 (arr30 A A)) → Tm30 Γ A → Tm30 Γ A
 := λ t u v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30 ,
     rec30 _ _
         (t Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)
         (u Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30)
         (v Tm30 var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 case30 zero30 suc30 rec30).

Definition v030 {Γ A} : Tm30 (snoc30 Γ A) A
 := var30 vz30.

Definition v130 {Γ A B} : Tm30 (snoc30 (snoc30 Γ A) B) A
 := var30 (vs30 vz30).

Definition v230 {Γ A B C} : Tm30 (snoc30 (snoc30 (snoc30 Γ A) B) C) A
 := var30 (vs30 (vs30 vz30)).

Definition v330 {Γ A B C D} : Tm30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) A
 := var30 (vs30 (vs30 (vs30 vz30))).

Definition tbool30 : Ty30
 := sum30 top30 top30.

Definition ttrue30 {Γ} : Tm30 Γ tbool30
 := left30 tt30.

Definition tfalse30 {Γ} : Tm30 Γ tbool30
 := right30 tt30.

Definition ifthenelse30 {Γ A} : Tm30 Γ (arr30 tbool30 (arr30 A (arr30 A A)))
 := lam30 (lam30 (lam30 (case30 v230 (lam30 v230) (lam30 v130)))).

Definition times430 {Γ A} : Tm30 Γ (arr30 (arr30 A A) (arr30 A A))
  := lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030))))).

Definition add30 {Γ} : Tm30 Γ (arr30 nat30 (arr30 nat30 nat30))
 := lam30 (rec30 v030
      (lam30 (lam30 (lam30 (suc30 (app30 v130 v030)))))
      (lam30 v030)).

Definition mul30 {Γ} : Tm30 Γ (arr30 nat30 (arr30 nat30 nat30))
 := lam30 (rec30 v030
     (lam30 (lam30 (lam30 (app30 (app30 add30 (app30 v130 v030)) v030))))
     (lam30 zero30)).

Definition fact30 {Γ} : Tm30 Γ (arr30 nat30 nat30)
 := lam30 (rec30 v030 (lam30 (lam30 (app30 (app30 mul30 (suc30 v130)) v030)))
        (suc30 zero30)).

Require Import Coq.Unicode.Utf8.

Definition Ty31 : Set
 := ∀ (Ty31           : Set)
      (nat top bot  : Ty31)
      (arr prod sum : Ty31 → Ty31 → Ty31)
    , Ty31.

Definition nat31 : Ty31 := λ _ nat31 _ _ _ _ _ , nat31.
Definition top31 : Ty31 := λ _ _ top31 _ _ _ _ , top31.
Definition bot31 : Ty31 := λ _ _ _ bot31 _ _ _ , bot31.

Definition arr31 : Ty31 → Ty31 → Ty31
 := λ A B Ty31 nat31 top31 bot31 arr31 prod sum ,
     arr31 (A Ty31 nat31 top31 bot31 arr31 prod sum) (B Ty31 nat31 top31 bot31 arr31 prod sum).

Definition prod31 : Ty31 → Ty31 → Ty31
 := λ A B Ty31 nat31 top31 bot31 arr31 prod31 sum ,
     prod31 (A Ty31 nat31 top31 bot31 arr31 prod31 sum) (B Ty31 nat31 top31 bot31 arr31 prod31 sum).

Definition sum31 : Ty31 → Ty31 → Ty31
 := λ A B Ty31 nat31 top31 bot31 arr31 prod31 sum31 ,
     sum31 (A Ty31 nat31 top31 bot31 arr31 prod31 sum31) (B Ty31 nat31 top31 bot31 arr31 prod31 sum31).

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
     (tt    : ∀ Γ       , Tm31 Γ top31)
     (pair  : ∀ Γ A B   , Tm31 Γ A → Tm31 Γ B → Tm31 Γ (prod31 A B))
     (fst   : ∀ Γ A B   , Tm31 Γ (prod31 A B) → Tm31 Γ A)
     (snd   : ∀ Γ A B   , Tm31 Γ (prod31 A B) → Tm31 Γ B)
     (left  : ∀ Γ A B   , Tm31 Γ A → Tm31 Γ (sum31 A B))
     (right : ∀ Γ A B   , Tm31 Γ B → Tm31 Γ (sum31 A B))
     (case  : ∀ Γ A B C , Tm31 Γ (sum31 A B) → Tm31 Γ (arr31 A C) → Tm31 Γ (arr31 B C) → Tm31 Γ C)
     (zero  : ∀ Γ       , Tm31 Γ nat31)
     (suc   : ∀ Γ       , Tm31 Γ nat31 → Tm31 Γ nat31)
     (rec   : ∀ Γ A     , Tm31 Γ nat31 → Tm31 Γ (arr31 nat31 (arr31 A A)) → Tm31 Γ A → Tm31 Γ A)
   , Tm31 Γ A.

Definition var31 {Γ A} : Var31 Γ A → Tm31 Γ A
 := λ x Tm31 var31 lam app tt pair fst snd left right case zero suc rec ,
     var31 _ _ x.

Definition lam31 {Γ A B} : Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B)
 := λ t Tm31 var31 lam31 app tt pair fst snd left right case zero suc rec ,
     lam31 _ _ _ (t Tm31 var31 lam31 app tt pair fst snd left right case zero suc rec).

Definition app31 {Γ A B} : Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B
 := λ t u Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec ,
     app31 _ _ _
         (t Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec)
         (u Tm31 var31 lam31 app31 tt pair fst snd left right case zero suc rec).

Definition tt31 {Γ} : Tm31 Γ top31
 := λ Tm31 var31 lam31 app31 tt31 pair fst snd left right case zero suc rec , tt31 _.

Definition pair31 {Γ A B} : Tm31 Γ A → Tm31 Γ B → Tm31 Γ (prod31 A B)
 := λ t u Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec ,
     pair31 _ _ _
          (t Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec)
          (u Tm31 var31 lam31 app31 tt31 pair31 fst snd left right case zero suc rec).

Definition fst31 {Γ A B} : Tm31 Γ (prod31 A B) → Tm31 Γ A
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd left right case zero suc rec ,
     fst31 _ _ _
         (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd left right case zero suc rec).

Definition snd31 {Γ A B} : Tm31 Γ (prod31 A B) → Tm31 Γ B
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left right case zero suc rec ,
     snd31 _ _ _
          (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left right case zero suc rec).

Definition left31 {Γ A B} : Tm31 Γ A → Tm31 Γ (sum31 A B)
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right case zero suc rec ,
     left31 _ _ _
          (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right case zero suc rec).

Definition right31 {Γ A B} : Tm31 Γ B → Tm31 Γ (sum31 A B)
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case zero suc rec ,
     right31 _ _ _
            (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case zero suc rec).

Definition case31 {Γ A B C} : Tm31 Γ (sum31 A B) → Tm31 Γ (arr31 A C) → Tm31 Γ (arr31 B C) → Tm31 Γ C
 := λ t u v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec ,
     case31 _ _ _ _
           (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)
           (u Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec)
           (v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero suc rec).

Definition zero31  {Γ} : Tm31 Γ nat31
 := λ Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc rec , zero31 _.

Definition suc31 {Γ} : Tm31 Γ nat31 → Tm31 Γ nat31
 := λ t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec ,
   suc31 _ (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec).

Definition rec31 {Γ A} : Tm31 Γ nat31 → Tm31 Γ (arr31 nat31 (arr31 A A)) → Tm31 Γ A → Tm31 Γ A
 := λ t u v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31 ,
     rec31 _ _
         (t Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)
         (u Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31)
         (v Tm31 var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 case31 zero31 suc31 rec31).

Definition v031 {Γ A} : Tm31 (snoc31 Γ A) A
 := var31 vz31.

Definition v131 {Γ A B} : Tm31 (snoc31 (snoc31 Γ A) B) A
 := var31 (vs31 vz31).

Definition v231 {Γ A B C} : Tm31 (snoc31 (snoc31 (snoc31 Γ A) B) C) A
 := var31 (vs31 (vs31 vz31)).

Definition v331 {Γ A B C D} : Tm31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) A
 := var31 (vs31 (vs31 (vs31 vz31))).

Definition tbool31 : Ty31
 := sum31 top31 top31.

Definition ttrue31 {Γ} : Tm31 Γ tbool31
 := left31 tt31.

Definition tfalse31 {Γ} : Tm31 Γ tbool31
 := right31 tt31.

Definition ifthenelse31 {Γ A} : Tm31 Γ (arr31 tbool31 (arr31 A (arr31 A A)))
 := lam31 (lam31 (lam31 (case31 v231 (lam31 v231) (lam31 v131)))).

Definition times431 {Γ A} : Tm31 Γ (arr31 (arr31 A A) (arr31 A A))
  := lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031))))).

Definition add31 {Γ} : Tm31 Γ (arr31 nat31 (arr31 nat31 nat31))
 := lam31 (rec31 v031
      (lam31 (lam31 (lam31 (suc31 (app31 v131 v031)))))
      (lam31 v031)).

Definition mul31 {Γ} : Tm31 Γ (arr31 nat31 (arr31 nat31 nat31))
 := lam31 (rec31 v031
     (lam31 (lam31 (lam31 (app31 (app31 add31 (app31 v131 v031)) v031))))
     (lam31 zero31)).

Definition fact31 {Γ} : Tm31 Γ (arr31 nat31 nat31)
 := lam31 (rec31 v031 (lam31 (lam31 (app31 (app31 mul31 (suc31 v131)) v031)))
        (suc31 zero31)).

Require Import Coq.Unicode.Utf8.

Definition Ty32 : Set
 := ∀ (Ty32           : Set)
      (nat top bot  : Ty32)
      (arr prod sum : Ty32 → Ty32 → Ty32)
    , Ty32.

Definition nat32 : Ty32 := λ _ nat32 _ _ _ _ _ , nat32.
Definition top32 : Ty32 := λ _ _ top32 _ _ _ _ , top32.
Definition bot32 : Ty32 := λ _ _ _ bot32 _ _ _ , bot32.

Definition arr32 : Ty32 → Ty32 → Ty32
 := λ A B Ty32 nat32 top32 bot32 arr32 prod sum ,
     arr32 (A Ty32 nat32 top32 bot32 arr32 prod sum) (B Ty32 nat32 top32 bot32 arr32 prod sum).

Definition prod32 : Ty32 → Ty32 → Ty32
 := λ A B Ty32 nat32 top32 bot32 arr32 prod32 sum ,
     prod32 (A Ty32 nat32 top32 bot32 arr32 prod32 sum) (B Ty32 nat32 top32 bot32 arr32 prod32 sum).

Definition sum32 : Ty32 → Ty32 → Ty32
 := λ A B Ty32 nat32 top32 bot32 arr32 prod32 sum32 ,
     sum32 (A Ty32 nat32 top32 bot32 arr32 prod32 sum32) (B Ty32 nat32 top32 bot32 arr32 prod32 sum32).

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
     (tt    : ∀ Γ       , Tm32 Γ top32)
     (pair  : ∀ Γ A B   , Tm32 Γ A → Tm32 Γ B → Tm32 Γ (prod32 A B))
     (fst   : ∀ Γ A B   , Tm32 Γ (prod32 A B) → Tm32 Γ A)
     (snd   : ∀ Γ A B   , Tm32 Γ (prod32 A B) → Tm32 Γ B)
     (left  : ∀ Γ A B   , Tm32 Γ A → Tm32 Γ (sum32 A B))
     (right : ∀ Γ A B   , Tm32 Γ B → Tm32 Γ (sum32 A B))
     (case  : ∀ Γ A B C , Tm32 Γ (sum32 A B) → Tm32 Γ (arr32 A C) → Tm32 Γ (arr32 B C) → Tm32 Γ C)
     (zero  : ∀ Γ       , Tm32 Γ nat32)
     (suc   : ∀ Γ       , Tm32 Γ nat32 → Tm32 Γ nat32)
     (rec   : ∀ Γ A     , Tm32 Γ nat32 → Tm32 Γ (arr32 nat32 (arr32 A A)) → Tm32 Γ A → Tm32 Γ A)
   , Tm32 Γ A.

Definition var32 {Γ A} : Var32 Γ A → Tm32 Γ A
 := λ x Tm32 var32 lam app tt pair fst snd left right case zero suc rec ,
     var32 _ _ x.

Definition lam32 {Γ A B} : Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B)
 := λ t Tm32 var32 lam32 app tt pair fst snd left right case zero suc rec ,
     lam32 _ _ _ (t Tm32 var32 lam32 app tt pair fst snd left right case zero suc rec).

Definition app32 {Γ A B} : Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B
 := λ t u Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec ,
     app32 _ _ _
         (t Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec)
         (u Tm32 var32 lam32 app32 tt pair fst snd left right case zero suc rec).

Definition tt32 {Γ} : Tm32 Γ top32
 := λ Tm32 var32 lam32 app32 tt32 pair fst snd left right case zero suc rec , tt32 _.

Definition pair32 {Γ A B} : Tm32 Γ A → Tm32 Γ B → Tm32 Γ (prod32 A B)
 := λ t u Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec ,
     pair32 _ _ _
          (t Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec)
          (u Tm32 var32 lam32 app32 tt32 pair32 fst snd left right case zero suc rec).

Definition fst32 {Γ A B} : Tm32 Γ (prod32 A B) → Tm32 Γ A
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd left right case zero suc rec ,
     fst32 _ _ _
         (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd left right case zero suc rec).

Definition snd32 {Γ A B} : Tm32 Γ (prod32 A B) → Tm32 Γ B
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left right case zero suc rec ,
     snd32 _ _ _
          (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left right case zero suc rec).

Definition left32 {Γ A B} : Tm32 Γ A → Tm32 Γ (sum32 A B)
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right case zero suc rec ,
     left32 _ _ _
          (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right case zero suc rec).

Definition right32 {Γ A B} : Tm32 Γ B → Tm32 Γ (sum32 A B)
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case zero suc rec ,
     right32 _ _ _
            (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case zero suc rec).

Definition case32 {Γ A B C} : Tm32 Γ (sum32 A B) → Tm32 Γ (arr32 A C) → Tm32 Γ (arr32 B C) → Tm32 Γ C
 := λ t u v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec ,
     case32 _ _ _ _
           (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)
           (u Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec)
           (v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero suc rec).

Definition zero32  {Γ} : Tm32 Γ nat32
 := λ Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc rec , zero32 _.

Definition suc32 {Γ} : Tm32 Γ nat32 → Tm32 Γ nat32
 := λ t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec ,
   suc32 _ (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec).

Definition rec32 {Γ A} : Tm32 Γ nat32 → Tm32 Γ (arr32 nat32 (arr32 A A)) → Tm32 Γ A → Tm32 Γ A
 := λ t u v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32 ,
     rec32 _ _
         (t Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)
         (u Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32)
         (v Tm32 var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 case32 zero32 suc32 rec32).

Definition v032 {Γ A} : Tm32 (snoc32 Γ A) A
 := var32 vz32.

Definition v132 {Γ A B} : Tm32 (snoc32 (snoc32 Γ A) B) A
 := var32 (vs32 vz32).

Definition v232 {Γ A B C} : Tm32 (snoc32 (snoc32 (snoc32 Γ A) B) C) A
 := var32 (vs32 (vs32 vz32)).

Definition v332 {Γ A B C D} : Tm32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) A
 := var32 (vs32 (vs32 (vs32 vz32))).

Definition tbool32 : Ty32
 := sum32 top32 top32.

Definition ttrue32 {Γ} : Tm32 Γ tbool32
 := left32 tt32.

Definition tfalse32 {Γ} : Tm32 Γ tbool32
 := right32 tt32.

Definition ifthenelse32 {Γ A} : Tm32 Γ (arr32 tbool32 (arr32 A (arr32 A A)))
 := lam32 (lam32 (lam32 (case32 v232 (lam32 v232) (lam32 v132)))).

Definition times432 {Γ A} : Tm32 Γ (arr32 (arr32 A A) (arr32 A A))
  := lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032))))).

Definition add32 {Γ} : Tm32 Γ (arr32 nat32 (arr32 nat32 nat32))
 := lam32 (rec32 v032
      (lam32 (lam32 (lam32 (suc32 (app32 v132 v032)))))
      (lam32 v032)).

Definition mul32 {Γ} : Tm32 Γ (arr32 nat32 (arr32 nat32 nat32))
 := lam32 (rec32 v032
     (lam32 (lam32 (lam32 (app32 (app32 add32 (app32 v132 v032)) v032))))
     (lam32 zero32)).

Definition fact32 {Γ} : Tm32 Γ (arr32 nat32 nat32)
 := lam32 (rec32 v032 (lam32 (lam32 (app32 (app32 mul32 (suc32 v132)) v032)))
        (suc32 zero32)).

Require Import Coq.Unicode.Utf8.

Definition Ty33 : Set
 := ∀ (Ty33           : Set)
      (nat top bot  : Ty33)
      (arr prod sum : Ty33 → Ty33 → Ty33)
    , Ty33.

Definition nat33 : Ty33 := λ _ nat33 _ _ _ _ _ , nat33.
Definition top33 : Ty33 := λ _ _ top33 _ _ _ _ , top33.
Definition bot33 : Ty33 := λ _ _ _ bot33 _ _ _ , bot33.

Definition arr33 : Ty33 → Ty33 → Ty33
 := λ A B Ty33 nat33 top33 bot33 arr33 prod sum ,
     arr33 (A Ty33 nat33 top33 bot33 arr33 prod sum) (B Ty33 nat33 top33 bot33 arr33 prod sum).

Definition prod33 : Ty33 → Ty33 → Ty33
 := λ A B Ty33 nat33 top33 bot33 arr33 prod33 sum ,
     prod33 (A Ty33 nat33 top33 bot33 arr33 prod33 sum) (B Ty33 nat33 top33 bot33 arr33 prod33 sum).

Definition sum33 : Ty33 → Ty33 → Ty33
 := λ A B Ty33 nat33 top33 bot33 arr33 prod33 sum33 ,
     sum33 (A Ty33 nat33 top33 bot33 arr33 prod33 sum33) (B Ty33 nat33 top33 bot33 arr33 prod33 sum33).

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
     (tt    : ∀ Γ       , Tm33 Γ top33)
     (pair  : ∀ Γ A B   , Tm33 Γ A → Tm33 Γ B → Tm33 Γ (prod33 A B))
     (fst   : ∀ Γ A B   , Tm33 Γ (prod33 A B) → Tm33 Γ A)
     (snd   : ∀ Γ A B   , Tm33 Γ (prod33 A B) → Tm33 Γ B)
     (left  : ∀ Γ A B   , Tm33 Γ A → Tm33 Γ (sum33 A B))
     (right : ∀ Γ A B   , Tm33 Γ B → Tm33 Γ (sum33 A B))
     (case  : ∀ Γ A B C , Tm33 Γ (sum33 A B) → Tm33 Γ (arr33 A C) → Tm33 Γ (arr33 B C) → Tm33 Γ C)
     (zero  : ∀ Γ       , Tm33 Γ nat33)
     (suc   : ∀ Γ       , Tm33 Γ nat33 → Tm33 Γ nat33)
     (rec   : ∀ Γ A     , Tm33 Γ nat33 → Tm33 Γ (arr33 nat33 (arr33 A A)) → Tm33 Γ A → Tm33 Γ A)
   , Tm33 Γ A.

Definition var33 {Γ A} : Var33 Γ A → Tm33 Γ A
 := λ x Tm33 var33 lam app tt pair fst snd left right case zero suc rec ,
     var33 _ _ x.

Definition lam33 {Γ A B} : Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B)
 := λ t Tm33 var33 lam33 app tt pair fst snd left right case zero suc rec ,
     lam33 _ _ _ (t Tm33 var33 lam33 app tt pair fst snd left right case zero suc rec).

Definition app33 {Γ A B} : Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B
 := λ t u Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec ,
     app33 _ _ _
         (t Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec)
         (u Tm33 var33 lam33 app33 tt pair fst snd left right case zero suc rec).

Definition tt33 {Γ} : Tm33 Γ top33
 := λ Tm33 var33 lam33 app33 tt33 pair fst snd left right case zero suc rec , tt33 _.

Definition pair33 {Γ A B} : Tm33 Γ A → Tm33 Γ B → Tm33 Γ (prod33 A B)
 := λ t u Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec ,
     pair33 _ _ _
          (t Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec)
          (u Tm33 var33 lam33 app33 tt33 pair33 fst snd left right case zero suc rec).

Definition fst33 {Γ A B} : Tm33 Γ (prod33 A B) → Tm33 Γ A
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd left right case zero suc rec ,
     fst33 _ _ _
         (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd left right case zero suc rec).

Definition snd33 {Γ A B} : Tm33 Γ (prod33 A B) → Tm33 Γ B
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left right case zero suc rec ,
     snd33 _ _ _
          (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left right case zero suc rec).

Definition left33 {Γ A B} : Tm33 Γ A → Tm33 Γ (sum33 A B)
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right case zero suc rec ,
     left33 _ _ _
          (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right case zero suc rec).

Definition right33 {Γ A B} : Tm33 Γ B → Tm33 Γ (sum33 A B)
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case zero suc rec ,
     right33 _ _ _
            (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case zero suc rec).

Definition case33 {Γ A B C} : Tm33 Γ (sum33 A B) → Tm33 Γ (arr33 A C) → Tm33 Γ (arr33 B C) → Tm33 Γ C
 := λ t u v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec ,
     case33 _ _ _ _
           (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)
           (u Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec)
           (v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero suc rec).

Definition zero33  {Γ} : Tm33 Γ nat33
 := λ Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc rec , zero33 _.

Definition suc33 {Γ} : Tm33 Γ nat33 → Tm33 Γ nat33
 := λ t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec ,
   suc33 _ (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec).

Definition rec33 {Γ A} : Tm33 Γ nat33 → Tm33 Γ (arr33 nat33 (arr33 A A)) → Tm33 Γ A → Tm33 Γ A
 := λ t u v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33 ,
     rec33 _ _
         (t Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)
         (u Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33)
         (v Tm33 var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 case33 zero33 suc33 rec33).

Definition v033 {Γ A} : Tm33 (snoc33 Γ A) A
 := var33 vz33.

Definition v133 {Γ A B} : Tm33 (snoc33 (snoc33 Γ A) B) A
 := var33 (vs33 vz33).

Definition v233 {Γ A B C} : Tm33 (snoc33 (snoc33 (snoc33 Γ A) B) C) A
 := var33 (vs33 (vs33 vz33)).

Definition v333 {Γ A B C D} : Tm33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) A
 := var33 (vs33 (vs33 (vs33 vz33))).

Definition tbool33 : Ty33
 := sum33 top33 top33.

Definition ttrue33 {Γ} : Tm33 Γ tbool33
 := left33 tt33.

Definition tfalse33 {Γ} : Tm33 Γ tbool33
 := right33 tt33.

Definition ifthenelse33 {Γ A} : Tm33 Γ (arr33 tbool33 (arr33 A (arr33 A A)))
 := lam33 (lam33 (lam33 (case33 v233 (lam33 v233) (lam33 v133)))).

Definition times433 {Γ A} : Tm33 Γ (arr33 (arr33 A A) (arr33 A A))
  := lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033))))).

Definition add33 {Γ} : Tm33 Γ (arr33 nat33 (arr33 nat33 nat33))
 := lam33 (rec33 v033
      (lam33 (lam33 (lam33 (suc33 (app33 v133 v033)))))
      (lam33 v033)).

Definition mul33 {Γ} : Tm33 Γ (arr33 nat33 (arr33 nat33 nat33))
 := lam33 (rec33 v033
     (lam33 (lam33 (lam33 (app33 (app33 add33 (app33 v133 v033)) v033))))
     (lam33 zero33)).

Definition fact33 {Γ} : Tm33 Γ (arr33 nat33 nat33)
 := lam33 (rec33 v033 (lam33 (lam33 (app33 (app33 mul33 (suc33 v133)) v033)))
        (suc33 zero33)).

Require Import Coq.Unicode.Utf8.

Definition Ty34 : Set
 := ∀ (Ty34           : Set)
      (nat top bot  : Ty34)
      (arr prod sum : Ty34 → Ty34 → Ty34)
    , Ty34.

Definition nat34 : Ty34 := λ _ nat34 _ _ _ _ _ , nat34.
Definition top34 : Ty34 := λ _ _ top34 _ _ _ _ , top34.
Definition bot34 : Ty34 := λ _ _ _ bot34 _ _ _ , bot34.

Definition arr34 : Ty34 → Ty34 → Ty34
 := λ A B Ty34 nat34 top34 bot34 arr34 prod sum ,
     arr34 (A Ty34 nat34 top34 bot34 arr34 prod sum) (B Ty34 nat34 top34 bot34 arr34 prod sum).

Definition prod34 : Ty34 → Ty34 → Ty34
 := λ A B Ty34 nat34 top34 bot34 arr34 prod34 sum ,
     prod34 (A Ty34 nat34 top34 bot34 arr34 prod34 sum) (B Ty34 nat34 top34 bot34 arr34 prod34 sum).

Definition sum34 : Ty34 → Ty34 → Ty34
 := λ A B Ty34 nat34 top34 bot34 arr34 prod34 sum34 ,
     sum34 (A Ty34 nat34 top34 bot34 arr34 prod34 sum34) (B Ty34 nat34 top34 bot34 arr34 prod34 sum34).

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
     (tt    : ∀ Γ       , Tm34 Γ top34)
     (pair  : ∀ Γ A B   , Tm34 Γ A → Tm34 Γ B → Tm34 Γ (prod34 A B))
     (fst   : ∀ Γ A B   , Tm34 Γ (prod34 A B) → Tm34 Γ A)
     (snd   : ∀ Γ A B   , Tm34 Γ (prod34 A B) → Tm34 Γ B)
     (left  : ∀ Γ A B   , Tm34 Γ A → Tm34 Γ (sum34 A B))
     (right : ∀ Γ A B   , Tm34 Γ B → Tm34 Γ (sum34 A B))
     (case  : ∀ Γ A B C , Tm34 Γ (sum34 A B) → Tm34 Γ (arr34 A C) → Tm34 Γ (arr34 B C) → Tm34 Γ C)
     (zero  : ∀ Γ       , Tm34 Γ nat34)
     (suc   : ∀ Γ       , Tm34 Γ nat34 → Tm34 Γ nat34)
     (rec   : ∀ Γ A     , Tm34 Γ nat34 → Tm34 Γ (arr34 nat34 (arr34 A A)) → Tm34 Γ A → Tm34 Γ A)
   , Tm34 Γ A.

Definition var34 {Γ A} : Var34 Γ A → Tm34 Γ A
 := λ x Tm34 var34 lam app tt pair fst snd left right case zero suc rec ,
     var34 _ _ x.

Definition lam34 {Γ A B} : Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B)
 := λ t Tm34 var34 lam34 app tt pair fst snd left right case zero suc rec ,
     lam34 _ _ _ (t Tm34 var34 lam34 app tt pair fst snd left right case zero suc rec).

Definition app34 {Γ A B} : Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B
 := λ t u Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec ,
     app34 _ _ _
         (t Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec)
         (u Tm34 var34 lam34 app34 tt pair fst snd left right case zero suc rec).

Definition tt34 {Γ} : Tm34 Γ top34
 := λ Tm34 var34 lam34 app34 tt34 pair fst snd left right case zero suc rec , tt34 _.

Definition pair34 {Γ A B} : Tm34 Γ A → Tm34 Γ B → Tm34 Γ (prod34 A B)
 := λ t u Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec ,
     pair34 _ _ _
          (t Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec)
          (u Tm34 var34 lam34 app34 tt34 pair34 fst snd left right case zero suc rec).

Definition fst34 {Γ A B} : Tm34 Γ (prod34 A B) → Tm34 Γ A
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd left right case zero suc rec ,
     fst34 _ _ _
         (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd left right case zero suc rec).

Definition snd34 {Γ A B} : Tm34 Γ (prod34 A B) → Tm34 Γ B
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left right case zero suc rec ,
     snd34 _ _ _
          (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left right case zero suc rec).

Definition left34 {Γ A B} : Tm34 Γ A → Tm34 Γ (sum34 A B)
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right case zero suc rec ,
     left34 _ _ _
          (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right case zero suc rec).

Definition right34 {Γ A B} : Tm34 Γ B → Tm34 Γ (sum34 A B)
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case zero suc rec ,
     right34 _ _ _
            (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case zero suc rec).

Definition case34 {Γ A B C} : Tm34 Γ (sum34 A B) → Tm34 Γ (arr34 A C) → Tm34 Γ (arr34 B C) → Tm34 Γ C
 := λ t u v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec ,
     case34 _ _ _ _
           (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)
           (u Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec)
           (v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero suc rec).

Definition zero34  {Γ} : Tm34 Γ nat34
 := λ Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc rec , zero34 _.

Definition suc34 {Γ} : Tm34 Γ nat34 → Tm34 Γ nat34
 := λ t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec ,
   suc34 _ (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec).

Definition rec34 {Γ A} : Tm34 Γ nat34 → Tm34 Γ (arr34 nat34 (arr34 A A)) → Tm34 Γ A → Tm34 Γ A
 := λ t u v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34 ,
     rec34 _ _
         (t Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)
         (u Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34)
         (v Tm34 var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 case34 zero34 suc34 rec34).

Definition v034 {Γ A} : Tm34 (snoc34 Γ A) A
 := var34 vz34.

Definition v134 {Γ A B} : Tm34 (snoc34 (snoc34 Γ A) B) A
 := var34 (vs34 vz34).

Definition v234 {Γ A B C} : Tm34 (snoc34 (snoc34 (snoc34 Γ A) B) C) A
 := var34 (vs34 (vs34 vz34)).

Definition v334 {Γ A B C D} : Tm34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) A
 := var34 (vs34 (vs34 (vs34 vz34))).

Definition tbool34 : Ty34
 := sum34 top34 top34.

Definition ttrue34 {Γ} : Tm34 Γ tbool34
 := left34 tt34.

Definition tfalse34 {Γ} : Tm34 Γ tbool34
 := right34 tt34.

Definition ifthenelse34 {Γ A} : Tm34 Γ (arr34 tbool34 (arr34 A (arr34 A A)))
 := lam34 (lam34 (lam34 (case34 v234 (lam34 v234) (lam34 v134)))).

Definition times434 {Γ A} : Tm34 Γ (arr34 (arr34 A A) (arr34 A A))
  := lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034))))).

Definition add34 {Γ} : Tm34 Γ (arr34 nat34 (arr34 nat34 nat34))
 := lam34 (rec34 v034
      (lam34 (lam34 (lam34 (suc34 (app34 v134 v034)))))
      (lam34 v034)).

Definition mul34 {Γ} : Tm34 Γ (arr34 nat34 (arr34 nat34 nat34))
 := lam34 (rec34 v034
     (lam34 (lam34 (lam34 (app34 (app34 add34 (app34 v134 v034)) v034))))
     (lam34 zero34)).

Definition fact34 {Γ} : Tm34 Γ (arr34 nat34 nat34)
 := lam34 (rec34 v034 (lam34 (lam34 (app34 (app34 mul34 (suc34 v134)) v034)))
        (suc34 zero34)).

Require Import Coq.Unicode.Utf8.

Definition Ty35 : Set
 := ∀ (Ty35           : Set)
      (nat top bot  : Ty35)
      (arr prod sum : Ty35 → Ty35 → Ty35)
    , Ty35.

Definition nat35 : Ty35 := λ _ nat35 _ _ _ _ _ , nat35.
Definition top35 : Ty35 := λ _ _ top35 _ _ _ _ , top35.
Definition bot35 : Ty35 := λ _ _ _ bot35 _ _ _ , bot35.

Definition arr35 : Ty35 → Ty35 → Ty35
 := λ A B Ty35 nat35 top35 bot35 arr35 prod sum ,
     arr35 (A Ty35 nat35 top35 bot35 arr35 prod sum) (B Ty35 nat35 top35 bot35 arr35 prod sum).

Definition prod35 : Ty35 → Ty35 → Ty35
 := λ A B Ty35 nat35 top35 bot35 arr35 prod35 sum ,
     prod35 (A Ty35 nat35 top35 bot35 arr35 prod35 sum) (B Ty35 nat35 top35 bot35 arr35 prod35 sum).

Definition sum35 : Ty35 → Ty35 → Ty35
 := λ A B Ty35 nat35 top35 bot35 arr35 prod35 sum35 ,
     sum35 (A Ty35 nat35 top35 bot35 arr35 prod35 sum35) (B Ty35 nat35 top35 bot35 arr35 prod35 sum35).

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
     (tt    : ∀ Γ       , Tm35 Γ top35)
     (pair  : ∀ Γ A B   , Tm35 Γ A → Tm35 Γ B → Tm35 Γ (prod35 A B))
     (fst   : ∀ Γ A B   , Tm35 Γ (prod35 A B) → Tm35 Γ A)
     (snd   : ∀ Γ A B   , Tm35 Γ (prod35 A B) → Tm35 Γ B)
     (left  : ∀ Γ A B   , Tm35 Γ A → Tm35 Γ (sum35 A B))
     (right : ∀ Γ A B   , Tm35 Γ B → Tm35 Γ (sum35 A B))
     (case  : ∀ Γ A B C , Tm35 Γ (sum35 A B) → Tm35 Γ (arr35 A C) → Tm35 Γ (arr35 B C) → Tm35 Γ C)
     (zero  : ∀ Γ       , Tm35 Γ nat35)
     (suc   : ∀ Γ       , Tm35 Γ nat35 → Tm35 Γ nat35)
     (rec   : ∀ Γ A     , Tm35 Γ nat35 → Tm35 Γ (arr35 nat35 (arr35 A A)) → Tm35 Γ A → Tm35 Γ A)
   , Tm35 Γ A.

Definition var35 {Γ A} : Var35 Γ A → Tm35 Γ A
 := λ x Tm35 var35 lam app tt pair fst snd left right case zero suc rec ,
     var35 _ _ x.

Definition lam35 {Γ A B} : Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B)
 := λ t Tm35 var35 lam35 app tt pair fst snd left right case zero suc rec ,
     lam35 _ _ _ (t Tm35 var35 lam35 app tt pair fst snd left right case zero suc rec).

Definition app35 {Γ A B} : Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B
 := λ t u Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec ,
     app35 _ _ _
         (t Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec)
         (u Tm35 var35 lam35 app35 tt pair fst snd left right case zero suc rec).

Definition tt35 {Γ} : Tm35 Γ top35
 := λ Tm35 var35 lam35 app35 tt35 pair fst snd left right case zero suc rec , tt35 _.

Definition pair35 {Γ A B} : Tm35 Γ A → Tm35 Γ B → Tm35 Γ (prod35 A B)
 := λ t u Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec ,
     pair35 _ _ _
          (t Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec)
          (u Tm35 var35 lam35 app35 tt35 pair35 fst snd left right case zero suc rec).

Definition fst35 {Γ A B} : Tm35 Γ (prod35 A B) → Tm35 Γ A
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd left right case zero suc rec ,
     fst35 _ _ _
         (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd left right case zero suc rec).

Definition snd35 {Γ A B} : Tm35 Γ (prod35 A B) → Tm35 Γ B
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left right case zero suc rec ,
     snd35 _ _ _
          (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left right case zero suc rec).

Definition left35 {Γ A B} : Tm35 Γ A → Tm35 Γ (sum35 A B)
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right case zero suc rec ,
     left35 _ _ _
          (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right case zero suc rec).

Definition right35 {Γ A B} : Tm35 Γ B → Tm35 Γ (sum35 A B)
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case zero suc rec ,
     right35 _ _ _
            (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case zero suc rec).

Definition case35 {Γ A B C} : Tm35 Γ (sum35 A B) → Tm35 Γ (arr35 A C) → Tm35 Γ (arr35 B C) → Tm35 Γ C
 := λ t u v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec ,
     case35 _ _ _ _
           (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)
           (u Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec)
           (v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero suc rec).

Definition zero35  {Γ} : Tm35 Γ nat35
 := λ Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc rec , zero35 _.

Definition suc35 {Γ} : Tm35 Γ nat35 → Tm35 Γ nat35
 := λ t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec ,
   suc35 _ (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec).

Definition rec35 {Γ A} : Tm35 Γ nat35 → Tm35 Γ (arr35 nat35 (arr35 A A)) → Tm35 Γ A → Tm35 Γ A
 := λ t u v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35 ,
     rec35 _ _
         (t Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)
         (u Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35)
         (v Tm35 var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 case35 zero35 suc35 rec35).

Definition v035 {Γ A} : Tm35 (snoc35 Γ A) A
 := var35 vz35.

Definition v135 {Γ A B} : Tm35 (snoc35 (snoc35 Γ A) B) A
 := var35 (vs35 vz35).

Definition v235 {Γ A B C} : Tm35 (snoc35 (snoc35 (snoc35 Γ A) B) C) A
 := var35 (vs35 (vs35 vz35)).

Definition v335 {Γ A B C D} : Tm35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) A
 := var35 (vs35 (vs35 (vs35 vz35))).

Definition tbool35 : Ty35
 := sum35 top35 top35.

Definition ttrue35 {Γ} : Tm35 Γ tbool35
 := left35 tt35.

Definition tfalse35 {Γ} : Tm35 Γ tbool35
 := right35 tt35.

Definition ifthenelse35 {Γ A} : Tm35 Γ (arr35 tbool35 (arr35 A (arr35 A A)))
 := lam35 (lam35 (lam35 (case35 v235 (lam35 v235) (lam35 v135)))).

Definition times435 {Γ A} : Tm35 Γ (arr35 (arr35 A A) (arr35 A A))
  := lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035))))).

Definition add35 {Γ} : Tm35 Γ (arr35 nat35 (arr35 nat35 nat35))
 := lam35 (rec35 v035
      (lam35 (lam35 (lam35 (suc35 (app35 v135 v035)))))
      (lam35 v035)).

Definition mul35 {Γ} : Tm35 Γ (arr35 nat35 (arr35 nat35 nat35))
 := lam35 (rec35 v035
     (lam35 (lam35 (lam35 (app35 (app35 add35 (app35 v135 v035)) v035))))
     (lam35 zero35)).

Definition fact35 {Γ} : Tm35 Γ (arr35 nat35 nat35)
 := lam35 (rec35 v035 (lam35 (lam35 (app35 (app35 mul35 (suc35 v135)) v035)))
        (suc35 zero35)).

Require Import Coq.Unicode.Utf8.

Definition Ty36 : Set
 := ∀ (Ty36           : Set)
      (nat top bot  : Ty36)
      (arr prod sum : Ty36 → Ty36 → Ty36)
    , Ty36.

Definition nat36 : Ty36 := λ _ nat36 _ _ _ _ _ , nat36.
Definition top36 : Ty36 := λ _ _ top36 _ _ _ _ , top36.
Definition bot36 : Ty36 := λ _ _ _ bot36 _ _ _ , bot36.

Definition arr36 : Ty36 → Ty36 → Ty36
 := λ A B Ty36 nat36 top36 bot36 arr36 prod sum ,
     arr36 (A Ty36 nat36 top36 bot36 arr36 prod sum) (B Ty36 nat36 top36 bot36 arr36 prod sum).

Definition prod36 : Ty36 → Ty36 → Ty36
 := λ A B Ty36 nat36 top36 bot36 arr36 prod36 sum ,
     prod36 (A Ty36 nat36 top36 bot36 arr36 prod36 sum) (B Ty36 nat36 top36 bot36 arr36 prod36 sum).

Definition sum36 : Ty36 → Ty36 → Ty36
 := λ A B Ty36 nat36 top36 bot36 arr36 prod36 sum36 ,
     sum36 (A Ty36 nat36 top36 bot36 arr36 prod36 sum36) (B Ty36 nat36 top36 bot36 arr36 prod36 sum36).

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
     (tt    : ∀ Γ       , Tm36 Γ top36)
     (pair  : ∀ Γ A B   , Tm36 Γ A → Tm36 Γ B → Tm36 Γ (prod36 A B))
     (fst   : ∀ Γ A B   , Tm36 Γ (prod36 A B) → Tm36 Γ A)
     (snd   : ∀ Γ A B   , Tm36 Γ (prod36 A B) → Tm36 Γ B)
     (left  : ∀ Γ A B   , Tm36 Γ A → Tm36 Γ (sum36 A B))
     (right : ∀ Γ A B   , Tm36 Γ B → Tm36 Γ (sum36 A B))
     (case  : ∀ Γ A B C , Tm36 Γ (sum36 A B) → Tm36 Γ (arr36 A C) → Tm36 Γ (arr36 B C) → Tm36 Γ C)
     (zero  : ∀ Γ       , Tm36 Γ nat36)
     (suc   : ∀ Γ       , Tm36 Γ nat36 → Tm36 Γ nat36)
     (rec   : ∀ Γ A     , Tm36 Γ nat36 → Tm36 Γ (arr36 nat36 (arr36 A A)) → Tm36 Γ A → Tm36 Γ A)
   , Tm36 Γ A.

Definition var36 {Γ A} : Var36 Γ A → Tm36 Γ A
 := λ x Tm36 var36 lam app tt pair fst snd left right case zero suc rec ,
     var36 _ _ x.

Definition lam36 {Γ A B} : Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B)
 := λ t Tm36 var36 lam36 app tt pair fst snd left right case zero suc rec ,
     lam36 _ _ _ (t Tm36 var36 lam36 app tt pair fst snd left right case zero suc rec).

Definition app36 {Γ A B} : Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B
 := λ t u Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec ,
     app36 _ _ _
         (t Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec)
         (u Tm36 var36 lam36 app36 tt pair fst snd left right case zero suc rec).

Definition tt36 {Γ} : Tm36 Γ top36
 := λ Tm36 var36 lam36 app36 tt36 pair fst snd left right case zero suc rec , tt36 _.

Definition pair36 {Γ A B} : Tm36 Γ A → Tm36 Γ B → Tm36 Γ (prod36 A B)
 := λ t u Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec ,
     pair36 _ _ _
          (t Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec)
          (u Tm36 var36 lam36 app36 tt36 pair36 fst snd left right case zero suc rec).

Definition fst36 {Γ A B} : Tm36 Γ (prod36 A B) → Tm36 Γ A
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd left right case zero suc rec ,
     fst36 _ _ _
         (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd left right case zero suc rec).

Definition snd36 {Γ A B} : Tm36 Γ (prod36 A B) → Tm36 Γ B
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left right case zero suc rec ,
     snd36 _ _ _
          (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left right case zero suc rec).

Definition left36 {Γ A B} : Tm36 Γ A → Tm36 Γ (sum36 A B)
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right case zero suc rec ,
     left36 _ _ _
          (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right case zero suc rec).

Definition right36 {Γ A B} : Tm36 Γ B → Tm36 Γ (sum36 A B)
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case zero suc rec ,
     right36 _ _ _
            (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case zero suc rec).

Definition case36 {Γ A B C} : Tm36 Γ (sum36 A B) → Tm36 Γ (arr36 A C) → Tm36 Γ (arr36 B C) → Tm36 Γ C
 := λ t u v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec ,
     case36 _ _ _ _
           (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)
           (u Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec)
           (v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero suc rec).

Definition zero36  {Γ} : Tm36 Γ nat36
 := λ Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc rec , zero36 _.

Definition suc36 {Γ} : Tm36 Γ nat36 → Tm36 Γ nat36
 := λ t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec ,
   suc36 _ (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec).

Definition rec36 {Γ A} : Tm36 Γ nat36 → Tm36 Γ (arr36 nat36 (arr36 A A)) → Tm36 Γ A → Tm36 Γ A
 := λ t u v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36 ,
     rec36 _ _
         (t Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)
         (u Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36)
         (v Tm36 var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 case36 zero36 suc36 rec36).

Definition v036 {Γ A} : Tm36 (snoc36 Γ A) A
 := var36 vz36.

Definition v136 {Γ A B} : Tm36 (snoc36 (snoc36 Γ A) B) A
 := var36 (vs36 vz36).

Definition v236 {Γ A B C} : Tm36 (snoc36 (snoc36 (snoc36 Γ A) B) C) A
 := var36 (vs36 (vs36 vz36)).

Definition v336 {Γ A B C D} : Tm36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) A
 := var36 (vs36 (vs36 (vs36 vz36))).

Definition tbool36 : Ty36
 := sum36 top36 top36.

Definition ttrue36 {Γ} : Tm36 Γ tbool36
 := left36 tt36.

Definition tfalse36 {Γ} : Tm36 Γ tbool36
 := right36 tt36.

Definition ifthenelse36 {Γ A} : Tm36 Γ (arr36 tbool36 (arr36 A (arr36 A A)))
 := lam36 (lam36 (lam36 (case36 v236 (lam36 v236) (lam36 v136)))).

Definition times436 {Γ A} : Tm36 Γ (arr36 (arr36 A A) (arr36 A A))
  := lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036))))).

Definition add36 {Γ} : Tm36 Γ (arr36 nat36 (arr36 nat36 nat36))
 := lam36 (rec36 v036
      (lam36 (lam36 (lam36 (suc36 (app36 v136 v036)))))
      (lam36 v036)).

Definition mul36 {Γ} : Tm36 Γ (arr36 nat36 (arr36 nat36 nat36))
 := lam36 (rec36 v036
     (lam36 (lam36 (lam36 (app36 (app36 add36 (app36 v136 v036)) v036))))
     (lam36 zero36)).

Definition fact36 {Γ} : Tm36 Γ (arr36 nat36 nat36)
 := lam36 (rec36 v036 (lam36 (lam36 (app36 (app36 mul36 (suc36 v136)) v036)))
        (suc36 zero36)).

Require Import Coq.Unicode.Utf8.

Definition Ty37 : Set
 := ∀ (Ty37           : Set)
      (nat top bot  : Ty37)
      (arr prod sum : Ty37 → Ty37 → Ty37)
    , Ty37.

Definition nat37 : Ty37 := λ _ nat37 _ _ _ _ _ , nat37.
Definition top37 : Ty37 := λ _ _ top37 _ _ _ _ , top37.
Definition bot37 : Ty37 := λ _ _ _ bot37 _ _ _ , bot37.

Definition arr37 : Ty37 → Ty37 → Ty37
 := λ A B Ty37 nat37 top37 bot37 arr37 prod sum ,
     arr37 (A Ty37 nat37 top37 bot37 arr37 prod sum) (B Ty37 nat37 top37 bot37 arr37 prod sum).

Definition prod37 : Ty37 → Ty37 → Ty37
 := λ A B Ty37 nat37 top37 bot37 arr37 prod37 sum ,
     prod37 (A Ty37 nat37 top37 bot37 arr37 prod37 sum) (B Ty37 nat37 top37 bot37 arr37 prod37 sum).

Definition sum37 : Ty37 → Ty37 → Ty37
 := λ A B Ty37 nat37 top37 bot37 arr37 prod37 sum37 ,
     sum37 (A Ty37 nat37 top37 bot37 arr37 prod37 sum37) (B Ty37 nat37 top37 bot37 arr37 prod37 sum37).

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
     (tt    : ∀ Γ       , Tm37 Γ top37)
     (pair  : ∀ Γ A B   , Tm37 Γ A → Tm37 Γ B → Tm37 Γ (prod37 A B))
     (fst   : ∀ Γ A B   , Tm37 Γ (prod37 A B) → Tm37 Γ A)
     (snd   : ∀ Γ A B   , Tm37 Γ (prod37 A B) → Tm37 Γ B)
     (left  : ∀ Γ A B   , Tm37 Γ A → Tm37 Γ (sum37 A B))
     (right : ∀ Γ A B   , Tm37 Γ B → Tm37 Γ (sum37 A B))
     (case  : ∀ Γ A B C , Tm37 Γ (sum37 A B) → Tm37 Γ (arr37 A C) → Tm37 Γ (arr37 B C) → Tm37 Γ C)
     (zero  : ∀ Γ       , Tm37 Γ nat37)
     (suc   : ∀ Γ       , Tm37 Γ nat37 → Tm37 Γ nat37)
     (rec   : ∀ Γ A     , Tm37 Γ nat37 → Tm37 Γ (arr37 nat37 (arr37 A A)) → Tm37 Γ A → Tm37 Γ A)
   , Tm37 Γ A.

Definition var37 {Γ A} : Var37 Γ A → Tm37 Γ A
 := λ x Tm37 var37 lam app tt pair fst snd left right case zero suc rec ,
     var37 _ _ x.

Definition lam37 {Γ A B} : Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B)
 := λ t Tm37 var37 lam37 app tt pair fst snd left right case zero suc rec ,
     lam37 _ _ _ (t Tm37 var37 lam37 app tt pair fst snd left right case zero suc rec).

Definition app37 {Γ A B} : Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B
 := λ t u Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec ,
     app37 _ _ _
         (t Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec)
         (u Tm37 var37 lam37 app37 tt pair fst snd left right case zero suc rec).

Definition tt37 {Γ} : Tm37 Γ top37
 := λ Tm37 var37 lam37 app37 tt37 pair fst snd left right case zero suc rec , tt37 _.

Definition pair37 {Γ A B} : Tm37 Γ A → Tm37 Γ B → Tm37 Γ (prod37 A B)
 := λ t u Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec ,
     pair37 _ _ _
          (t Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec)
          (u Tm37 var37 lam37 app37 tt37 pair37 fst snd left right case zero suc rec).

Definition fst37 {Γ A B} : Tm37 Γ (prod37 A B) → Tm37 Γ A
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd left right case zero suc rec ,
     fst37 _ _ _
         (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd left right case zero suc rec).

Definition snd37 {Γ A B} : Tm37 Γ (prod37 A B) → Tm37 Γ B
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left right case zero suc rec ,
     snd37 _ _ _
          (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left right case zero suc rec).

Definition left37 {Γ A B} : Tm37 Γ A → Tm37 Γ (sum37 A B)
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right case zero suc rec ,
     left37 _ _ _
          (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right case zero suc rec).

Definition right37 {Γ A B} : Tm37 Γ B → Tm37 Γ (sum37 A B)
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case zero suc rec ,
     right37 _ _ _
            (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case zero suc rec).

Definition case37 {Γ A B C} : Tm37 Γ (sum37 A B) → Tm37 Γ (arr37 A C) → Tm37 Γ (arr37 B C) → Tm37 Γ C
 := λ t u v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec ,
     case37 _ _ _ _
           (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)
           (u Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec)
           (v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero suc rec).

Definition zero37  {Γ} : Tm37 Γ nat37
 := λ Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc rec , zero37 _.

Definition suc37 {Γ} : Tm37 Γ nat37 → Tm37 Γ nat37
 := λ t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec ,
   suc37 _ (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec).

Definition rec37 {Γ A} : Tm37 Γ nat37 → Tm37 Γ (arr37 nat37 (arr37 A A)) → Tm37 Γ A → Tm37 Γ A
 := λ t u v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37 ,
     rec37 _ _
         (t Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)
         (u Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37)
         (v Tm37 var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 case37 zero37 suc37 rec37).

Definition v037 {Γ A} : Tm37 (snoc37 Γ A) A
 := var37 vz37.

Definition v137 {Γ A B} : Tm37 (snoc37 (snoc37 Γ A) B) A
 := var37 (vs37 vz37).

Definition v237 {Γ A B C} : Tm37 (snoc37 (snoc37 (snoc37 Γ A) B) C) A
 := var37 (vs37 (vs37 vz37)).

Definition v337 {Γ A B C D} : Tm37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) A
 := var37 (vs37 (vs37 (vs37 vz37))).

Definition tbool37 : Ty37
 := sum37 top37 top37.

Definition ttrue37 {Γ} : Tm37 Γ tbool37
 := left37 tt37.

Definition tfalse37 {Γ} : Tm37 Γ tbool37
 := right37 tt37.

Definition ifthenelse37 {Γ A} : Tm37 Γ (arr37 tbool37 (arr37 A (arr37 A A)))
 := lam37 (lam37 (lam37 (case37 v237 (lam37 v237) (lam37 v137)))).

Definition times437 {Γ A} : Tm37 Γ (arr37 (arr37 A A) (arr37 A A))
  := lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037))))).

Definition add37 {Γ} : Tm37 Γ (arr37 nat37 (arr37 nat37 nat37))
 := lam37 (rec37 v037
      (lam37 (lam37 (lam37 (suc37 (app37 v137 v037)))))
      (lam37 v037)).

Definition mul37 {Γ} : Tm37 Γ (arr37 nat37 (arr37 nat37 nat37))
 := lam37 (rec37 v037
     (lam37 (lam37 (lam37 (app37 (app37 add37 (app37 v137 v037)) v037))))
     (lam37 zero37)).

Definition fact37 {Γ} : Tm37 Γ (arr37 nat37 nat37)
 := lam37 (rec37 v037 (lam37 (lam37 (app37 (app37 mul37 (suc37 v137)) v037)))
        (suc37 zero37)).

Require Import Coq.Unicode.Utf8.

Definition Ty38 : Set
 := ∀ (Ty38           : Set)
      (nat top bot  : Ty38)
      (arr prod sum : Ty38 → Ty38 → Ty38)
    , Ty38.

Definition nat38 : Ty38 := λ _ nat38 _ _ _ _ _ , nat38.
Definition top38 : Ty38 := λ _ _ top38 _ _ _ _ , top38.
Definition bot38 : Ty38 := λ _ _ _ bot38 _ _ _ , bot38.

Definition arr38 : Ty38 → Ty38 → Ty38
 := λ A B Ty38 nat38 top38 bot38 arr38 prod sum ,
     arr38 (A Ty38 nat38 top38 bot38 arr38 prod sum) (B Ty38 nat38 top38 bot38 arr38 prod sum).

Definition prod38 : Ty38 → Ty38 → Ty38
 := λ A B Ty38 nat38 top38 bot38 arr38 prod38 sum ,
     prod38 (A Ty38 nat38 top38 bot38 arr38 prod38 sum) (B Ty38 nat38 top38 bot38 arr38 prod38 sum).

Definition sum38 : Ty38 → Ty38 → Ty38
 := λ A B Ty38 nat38 top38 bot38 arr38 prod38 sum38 ,
     sum38 (A Ty38 nat38 top38 bot38 arr38 prod38 sum38) (B Ty38 nat38 top38 bot38 arr38 prod38 sum38).

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
     (tt    : ∀ Γ       , Tm38 Γ top38)
     (pair  : ∀ Γ A B   , Tm38 Γ A → Tm38 Γ B → Tm38 Γ (prod38 A B))
     (fst   : ∀ Γ A B   , Tm38 Γ (prod38 A B) → Tm38 Γ A)
     (snd   : ∀ Γ A B   , Tm38 Γ (prod38 A B) → Tm38 Γ B)
     (left  : ∀ Γ A B   , Tm38 Γ A → Tm38 Γ (sum38 A B))
     (right : ∀ Γ A B   , Tm38 Γ B → Tm38 Γ (sum38 A B))
     (case  : ∀ Γ A B C , Tm38 Γ (sum38 A B) → Tm38 Γ (arr38 A C) → Tm38 Γ (arr38 B C) → Tm38 Γ C)
     (zero  : ∀ Γ       , Tm38 Γ nat38)
     (suc   : ∀ Γ       , Tm38 Γ nat38 → Tm38 Γ nat38)
     (rec   : ∀ Γ A     , Tm38 Γ nat38 → Tm38 Γ (arr38 nat38 (arr38 A A)) → Tm38 Γ A → Tm38 Γ A)
   , Tm38 Γ A.

Definition var38 {Γ A} : Var38 Γ A → Tm38 Γ A
 := λ x Tm38 var38 lam app tt pair fst snd left right case zero suc rec ,
     var38 _ _ x.

Definition lam38 {Γ A B} : Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B)
 := λ t Tm38 var38 lam38 app tt pair fst snd left right case zero suc rec ,
     lam38 _ _ _ (t Tm38 var38 lam38 app tt pair fst snd left right case zero suc rec).

Definition app38 {Γ A B} : Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B
 := λ t u Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec ,
     app38 _ _ _
         (t Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec)
         (u Tm38 var38 lam38 app38 tt pair fst snd left right case zero suc rec).

Definition tt38 {Γ} : Tm38 Γ top38
 := λ Tm38 var38 lam38 app38 tt38 pair fst snd left right case zero suc rec , tt38 _.

Definition pair38 {Γ A B} : Tm38 Γ A → Tm38 Γ B → Tm38 Γ (prod38 A B)
 := λ t u Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec ,
     pair38 _ _ _
          (t Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec)
          (u Tm38 var38 lam38 app38 tt38 pair38 fst snd left right case zero suc rec).

Definition fst38 {Γ A B} : Tm38 Γ (prod38 A B) → Tm38 Γ A
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd left right case zero suc rec ,
     fst38 _ _ _
         (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd left right case zero suc rec).

Definition snd38 {Γ A B} : Tm38 Γ (prod38 A B) → Tm38 Γ B
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left right case zero suc rec ,
     snd38 _ _ _
          (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left right case zero suc rec).

Definition left38 {Γ A B} : Tm38 Γ A → Tm38 Γ (sum38 A B)
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right case zero suc rec ,
     left38 _ _ _
          (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right case zero suc rec).

Definition right38 {Γ A B} : Tm38 Γ B → Tm38 Γ (sum38 A B)
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case zero suc rec ,
     right38 _ _ _
            (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case zero suc rec).

Definition case38 {Γ A B C} : Tm38 Γ (sum38 A B) → Tm38 Γ (arr38 A C) → Tm38 Γ (arr38 B C) → Tm38 Γ C
 := λ t u v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec ,
     case38 _ _ _ _
           (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)
           (u Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec)
           (v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero suc rec).

Definition zero38  {Γ} : Tm38 Γ nat38
 := λ Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc rec , zero38 _.

Definition suc38 {Γ} : Tm38 Γ nat38 → Tm38 Γ nat38
 := λ t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec ,
   suc38 _ (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec).

Definition rec38 {Γ A} : Tm38 Γ nat38 → Tm38 Γ (arr38 nat38 (arr38 A A)) → Tm38 Γ A → Tm38 Γ A
 := λ t u v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38 ,
     rec38 _ _
         (t Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)
         (u Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38)
         (v Tm38 var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 case38 zero38 suc38 rec38).

Definition v038 {Γ A} : Tm38 (snoc38 Γ A) A
 := var38 vz38.

Definition v138 {Γ A B} : Tm38 (snoc38 (snoc38 Γ A) B) A
 := var38 (vs38 vz38).

Definition v238 {Γ A B C} : Tm38 (snoc38 (snoc38 (snoc38 Γ A) B) C) A
 := var38 (vs38 (vs38 vz38)).

Definition v338 {Γ A B C D} : Tm38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) A
 := var38 (vs38 (vs38 (vs38 vz38))).

Definition tbool38 : Ty38
 := sum38 top38 top38.

Definition ttrue38 {Γ} : Tm38 Γ tbool38
 := left38 tt38.

Definition tfalse38 {Γ} : Tm38 Γ tbool38
 := right38 tt38.

Definition ifthenelse38 {Γ A} : Tm38 Γ (arr38 tbool38 (arr38 A (arr38 A A)))
 := lam38 (lam38 (lam38 (case38 v238 (lam38 v238) (lam38 v138)))).

Definition times438 {Γ A} : Tm38 Γ (arr38 (arr38 A A) (arr38 A A))
  := lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038))))).

Definition add38 {Γ} : Tm38 Γ (arr38 nat38 (arr38 nat38 nat38))
 := lam38 (rec38 v038
      (lam38 (lam38 (lam38 (suc38 (app38 v138 v038)))))
      (lam38 v038)).

Definition mul38 {Γ} : Tm38 Γ (arr38 nat38 (arr38 nat38 nat38))
 := lam38 (rec38 v038
     (lam38 (lam38 (lam38 (app38 (app38 add38 (app38 v138 v038)) v038))))
     (lam38 zero38)).

Definition fact38 {Γ} : Tm38 Γ (arr38 nat38 nat38)
 := lam38 (rec38 v038 (lam38 (lam38 (app38 (app38 mul38 (suc38 v138)) v038)))
        (suc38 zero38)).

Require Import Coq.Unicode.Utf8.

Definition Ty39 : Set
 := ∀ (Ty39           : Set)
      (nat top bot  : Ty39)
      (arr prod sum : Ty39 → Ty39 → Ty39)
    , Ty39.

Definition nat39 : Ty39 := λ _ nat39 _ _ _ _ _ , nat39.
Definition top39 : Ty39 := λ _ _ top39 _ _ _ _ , top39.
Definition bot39 : Ty39 := λ _ _ _ bot39 _ _ _ , bot39.

Definition arr39 : Ty39 → Ty39 → Ty39
 := λ A B Ty39 nat39 top39 bot39 arr39 prod sum ,
     arr39 (A Ty39 nat39 top39 bot39 arr39 prod sum) (B Ty39 nat39 top39 bot39 arr39 prod sum).

Definition prod39 : Ty39 → Ty39 → Ty39
 := λ A B Ty39 nat39 top39 bot39 arr39 prod39 sum ,
     prod39 (A Ty39 nat39 top39 bot39 arr39 prod39 sum) (B Ty39 nat39 top39 bot39 arr39 prod39 sum).

Definition sum39 : Ty39 → Ty39 → Ty39
 := λ A B Ty39 nat39 top39 bot39 arr39 prod39 sum39 ,
     sum39 (A Ty39 nat39 top39 bot39 arr39 prod39 sum39) (B Ty39 nat39 top39 bot39 arr39 prod39 sum39).

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
     (tt    : ∀ Γ       , Tm39 Γ top39)
     (pair  : ∀ Γ A B   , Tm39 Γ A → Tm39 Γ B → Tm39 Γ (prod39 A B))
     (fst   : ∀ Γ A B   , Tm39 Γ (prod39 A B) → Tm39 Γ A)
     (snd   : ∀ Γ A B   , Tm39 Γ (prod39 A B) → Tm39 Γ B)
     (left  : ∀ Γ A B   , Tm39 Γ A → Tm39 Γ (sum39 A B))
     (right : ∀ Γ A B   , Tm39 Γ B → Tm39 Γ (sum39 A B))
     (case  : ∀ Γ A B C , Tm39 Γ (sum39 A B) → Tm39 Γ (arr39 A C) → Tm39 Γ (arr39 B C) → Tm39 Γ C)
     (zero  : ∀ Γ       , Tm39 Γ nat39)
     (suc   : ∀ Γ       , Tm39 Γ nat39 → Tm39 Γ nat39)
     (rec   : ∀ Γ A     , Tm39 Γ nat39 → Tm39 Γ (arr39 nat39 (arr39 A A)) → Tm39 Γ A → Tm39 Γ A)
   , Tm39 Γ A.

Definition var39 {Γ A} : Var39 Γ A → Tm39 Γ A
 := λ x Tm39 var39 lam app tt pair fst snd left right case zero suc rec ,
     var39 _ _ x.

Definition lam39 {Γ A B} : Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B)
 := λ t Tm39 var39 lam39 app tt pair fst snd left right case zero suc rec ,
     lam39 _ _ _ (t Tm39 var39 lam39 app tt pair fst snd left right case zero suc rec).

Definition app39 {Γ A B} : Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B
 := λ t u Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec ,
     app39 _ _ _
         (t Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec)
         (u Tm39 var39 lam39 app39 tt pair fst snd left right case zero suc rec).

Definition tt39 {Γ} : Tm39 Γ top39
 := λ Tm39 var39 lam39 app39 tt39 pair fst snd left right case zero suc rec , tt39 _.

Definition pair39 {Γ A B} : Tm39 Γ A → Tm39 Γ B → Tm39 Γ (prod39 A B)
 := λ t u Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec ,
     pair39 _ _ _
          (t Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec)
          (u Tm39 var39 lam39 app39 tt39 pair39 fst snd left right case zero suc rec).

Definition fst39 {Γ A B} : Tm39 Γ (prod39 A B) → Tm39 Γ A
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd left right case zero suc rec ,
     fst39 _ _ _
         (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd left right case zero suc rec).

Definition snd39 {Γ A B} : Tm39 Γ (prod39 A B) → Tm39 Γ B
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left right case zero suc rec ,
     snd39 _ _ _
          (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left right case zero suc rec).

Definition left39 {Γ A B} : Tm39 Γ A → Tm39 Γ (sum39 A B)
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right case zero suc rec ,
     left39 _ _ _
          (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right case zero suc rec).

Definition right39 {Γ A B} : Tm39 Γ B → Tm39 Γ (sum39 A B)
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case zero suc rec ,
     right39 _ _ _
            (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case zero suc rec).

Definition case39 {Γ A B C} : Tm39 Γ (sum39 A B) → Tm39 Γ (arr39 A C) → Tm39 Γ (arr39 B C) → Tm39 Γ C
 := λ t u v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec ,
     case39 _ _ _ _
           (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)
           (u Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec)
           (v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero suc rec).

Definition zero39  {Γ} : Tm39 Γ nat39
 := λ Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc rec , zero39 _.

Definition suc39 {Γ} : Tm39 Γ nat39 → Tm39 Γ nat39
 := λ t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec ,
   suc39 _ (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec).

Definition rec39 {Γ A} : Tm39 Γ nat39 → Tm39 Γ (arr39 nat39 (arr39 A A)) → Tm39 Γ A → Tm39 Γ A
 := λ t u v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39 ,
     rec39 _ _
         (t Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)
         (u Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39)
         (v Tm39 var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 case39 zero39 suc39 rec39).

Definition v039 {Γ A} : Tm39 (snoc39 Γ A) A
 := var39 vz39.

Definition v139 {Γ A B} : Tm39 (snoc39 (snoc39 Γ A) B) A
 := var39 (vs39 vz39).

Definition v239 {Γ A B C} : Tm39 (snoc39 (snoc39 (snoc39 Γ A) B) C) A
 := var39 (vs39 (vs39 vz39)).

Definition v339 {Γ A B C D} : Tm39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) A
 := var39 (vs39 (vs39 (vs39 vz39))).

Definition tbool39 : Ty39
 := sum39 top39 top39.

Definition ttrue39 {Γ} : Tm39 Γ tbool39
 := left39 tt39.

Definition tfalse39 {Γ} : Tm39 Γ tbool39
 := right39 tt39.

Definition ifthenelse39 {Γ A} : Tm39 Γ (arr39 tbool39 (arr39 A (arr39 A A)))
 := lam39 (lam39 (lam39 (case39 v239 (lam39 v239) (lam39 v139)))).

Definition times439 {Γ A} : Tm39 Γ (arr39 (arr39 A A) (arr39 A A))
  := lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039))))).

Definition add39 {Γ} : Tm39 Γ (arr39 nat39 (arr39 nat39 nat39))
 := lam39 (rec39 v039
      (lam39 (lam39 (lam39 (suc39 (app39 v139 v039)))))
      (lam39 v039)).

Definition mul39 {Γ} : Tm39 Γ (arr39 nat39 (arr39 nat39 nat39))
 := lam39 (rec39 v039
     (lam39 (lam39 (lam39 (app39 (app39 add39 (app39 v139 v039)) v039))))
     (lam39 zero39)).

Definition fact39 {Γ} : Tm39 Γ (arr39 nat39 nat39)
 := lam39 (rec39 v039 (lam39 (lam39 (app39 (app39 mul39 (suc39 v139)) v039)))
        (suc39 zero39)).

Require Import Coq.Unicode.Utf8.

Definition Ty40 : Set
 := ∀ (Ty40           : Set)
      (nat top bot  : Ty40)
      (arr prod sum : Ty40 → Ty40 → Ty40)
    , Ty40.

Definition nat40 : Ty40 := λ _ nat40 _ _ _ _ _ , nat40.
Definition top40 : Ty40 := λ _ _ top40 _ _ _ _ , top40.
Definition bot40 : Ty40 := λ _ _ _ bot40 _ _ _ , bot40.

Definition arr40 : Ty40 → Ty40 → Ty40
 := λ A B Ty40 nat40 top40 bot40 arr40 prod sum ,
     arr40 (A Ty40 nat40 top40 bot40 arr40 prod sum) (B Ty40 nat40 top40 bot40 arr40 prod sum).

Definition prod40 : Ty40 → Ty40 → Ty40
 := λ A B Ty40 nat40 top40 bot40 arr40 prod40 sum ,
     prod40 (A Ty40 nat40 top40 bot40 arr40 prod40 sum) (B Ty40 nat40 top40 bot40 arr40 prod40 sum).

Definition sum40 : Ty40 → Ty40 → Ty40
 := λ A B Ty40 nat40 top40 bot40 arr40 prod40 sum40 ,
     sum40 (A Ty40 nat40 top40 bot40 arr40 prod40 sum40) (B Ty40 nat40 top40 bot40 arr40 prod40 sum40).

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
     (tt    : ∀ Γ       , Tm40 Γ top40)
     (pair  : ∀ Γ A B   , Tm40 Γ A → Tm40 Γ B → Tm40 Γ (prod40 A B))
     (fst   : ∀ Γ A B   , Tm40 Γ (prod40 A B) → Tm40 Γ A)
     (snd   : ∀ Γ A B   , Tm40 Γ (prod40 A B) → Tm40 Γ B)
     (left  : ∀ Γ A B   , Tm40 Γ A → Tm40 Γ (sum40 A B))
     (right : ∀ Γ A B   , Tm40 Γ B → Tm40 Γ (sum40 A B))
     (case  : ∀ Γ A B C , Tm40 Γ (sum40 A B) → Tm40 Γ (arr40 A C) → Tm40 Γ (arr40 B C) → Tm40 Γ C)
     (zero  : ∀ Γ       , Tm40 Γ nat40)
     (suc   : ∀ Γ       , Tm40 Γ nat40 → Tm40 Γ nat40)
     (rec   : ∀ Γ A     , Tm40 Γ nat40 → Tm40 Γ (arr40 nat40 (arr40 A A)) → Tm40 Γ A → Tm40 Γ A)
   , Tm40 Γ A.

Definition var40 {Γ A} : Var40 Γ A → Tm40 Γ A
 := λ x Tm40 var40 lam app tt pair fst snd left right case zero suc rec ,
     var40 _ _ x.

Definition lam40 {Γ A B} : Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B)
 := λ t Tm40 var40 lam40 app tt pair fst snd left right case zero suc rec ,
     lam40 _ _ _ (t Tm40 var40 lam40 app tt pair fst snd left right case zero suc rec).

Definition app40 {Γ A B} : Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B
 := λ t u Tm40 var40 lam40 app40 tt pair fst snd left right case zero suc rec ,
     app40 _ _ _
         (t Tm40 var40 lam40 app40 tt pair fst snd left right case zero suc rec)
         (u Tm40 var40 lam40 app40 tt pair fst snd left right case zero suc rec).

Definition tt40 {Γ} : Tm40 Γ top40
 := λ Tm40 var40 lam40 app40 tt40 pair fst snd left right case zero suc rec , tt40 _.

Definition pair40 {Γ A B} : Tm40 Γ A → Tm40 Γ B → Tm40 Γ (prod40 A B)
 := λ t u Tm40 var40 lam40 app40 tt40 pair40 fst snd left right case zero suc rec ,
     pair40 _ _ _
          (t Tm40 var40 lam40 app40 tt40 pair40 fst snd left right case zero suc rec)
          (u Tm40 var40 lam40 app40 tt40 pair40 fst snd left right case zero suc rec).

Definition fst40 {Γ A B} : Tm40 Γ (prod40 A B) → Tm40 Γ A
 := λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd left right case zero suc rec ,
     fst40 _ _ _
         (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd left right case zero suc rec).

Definition snd40 {Γ A B} : Tm40 Γ (prod40 A B) → Tm40 Γ B
 := λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left right case zero suc rec ,
     snd40 _ _ _
          (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left right case zero suc rec).

Definition left40 {Γ A B} : Tm40 Γ A → Tm40 Γ (sum40 A B)
 := λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right case zero suc rec ,
     left40 _ _ _
          (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right case zero suc rec).

Definition right40 {Γ A B} : Tm40 Γ B → Tm40 Γ (sum40 A B)
 := λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case zero suc rec ,
     right40 _ _ _
            (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case zero suc rec).

Definition case40 {Γ A B C} : Tm40 Γ (sum40 A B) → Tm40 Γ (arr40 A C) → Tm40 Γ (arr40 B C) → Tm40 Γ C
 := λ t u v Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero suc rec ,
     case40 _ _ _ _
           (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero suc rec)
           (u Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero suc rec)
           (v Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero suc rec).

Definition zero40  {Γ} : Tm40 Γ nat40
 := λ Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc rec , zero40 _.

Definition suc40 {Γ} : Tm40 Γ nat40 → Tm40 Γ nat40
 := λ t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec ,
   suc40 _ (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec).

Definition rec40 {Γ A} : Tm40 Γ nat40 → Tm40 Γ (arr40 nat40 (arr40 A A)) → Tm40 Γ A → Tm40 Γ A
 := λ t u v Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec40 ,
     rec40 _ _
         (t Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec40)
         (u Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec40)
         (v Tm40 var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 case40 zero40 suc40 rec40).

Definition v040 {Γ A} : Tm40 (snoc40 Γ A) A
 := var40 vz40.

Definition v140 {Γ A B} : Tm40 (snoc40 (snoc40 Γ A) B) A
 := var40 (vs40 vz40).

Definition v240 {Γ A B C} : Tm40 (snoc40 (snoc40 (snoc40 Γ A) B) C) A
 := var40 (vs40 (vs40 vz40)).

Definition v340 {Γ A B C D} : Tm40 (snoc40 (snoc40 (snoc40 (snoc40 Γ A) B) C) D) A
 := var40 (vs40 (vs40 (vs40 vz40))).

Definition tbool40 : Ty40
 := sum40 top40 top40.

Definition ttrue40 {Γ} : Tm40 Γ tbool40
 := left40 tt40.

Definition tfalse40 {Γ} : Tm40 Γ tbool40
 := right40 tt40.

Definition ifthenelse40 {Γ A} : Tm40 Γ (arr40 tbool40 (arr40 A (arr40 A A)))
 := lam40 (lam40 (lam40 (case40 v240 (lam40 v240) (lam40 v140)))).

Definition times440 {Γ A} : Tm40 Γ (arr40 (arr40 A A) (arr40 A A))
  := lam40 (lam40 (app40 v140 (app40 v140 (app40 v140 (app40 v140 v040))))).

Definition add40 {Γ} : Tm40 Γ (arr40 nat40 (arr40 nat40 nat40))
 := lam40 (rec40 v040
      (lam40 (lam40 (lam40 (suc40 (app40 v140 v040)))))
      (lam40 v040)).

Definition mul40 {Γ} : Tm40 Γ (arr40 nat40 (arr40 nat40 nat40))
 := lam40 (rec40 v040
     (lam40 (lam40 (lam40 (app40 (app40 add40 (app40 v140 v040)) v040))))
     (lam40 zero40)).

Definition fact40 {Γ} : Tm40 Γ (arr40 nat40 nat40)
 := lam40 (rec40 v040 (lam40 (lam40 (app40 (app40 mul40 (suc40 v140)) v040)))
        (suc40 zero40)).

Require Import Coq.Unicode.Utf8.

Definition Ty41 : Set
 := ∀ (Ty41           : Set)
      (nat top bot  : Ty41)
      (arr prod sum : Ty41 → Ty41 → Ty41)
    , Ty41.

Definition nat41 : Ty41 := λ _ nat41 _ _ _ _ _ , nat41.
Definition top41 : Ty41 := λ _ _ top41 _ _ _ _ , top41.
Definition bot41 : Ty41 := λ _ _ _ bot41 _ _ _ , bot41.

Definition arr41 : Ty41 → Ty41 → Ty41
 := λ A B Ty41 nat41 top41 bot41 arr41 prod sum ,
     arr41 (A Ty41 nat41 top41 bot41 arr41 prod sum) (B Ty41 nat41 top41 bot41 arr41 prod sum).

Definition prod41 : Ty41 → Ty41 → Ty41
 := λ A B Ty41 nat41 top41 bot41 arr41 prod41 sum ,
     prod41 (A Ty41 nat41 top41 bot41 arr41 prod41 sum) (B Ty41 nat41 top41 bot41 arr41 prod41 sum).

Definition sum41 : Ty41 → Ty41 → Ty41
 := λ A B Ty41 nat41 top41 bot41 arr41 prod41 sum41 ,
     sum41 (A Ty41 nat41 top41 bot41 arr41 prod41 sum41) (B Ty41 nat41 top41 bot41 arr41 prod41 sum41).

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
     (tt    : ∀ Γ       , Tm41 Γ top41)
     (pair  : ∀ Γ A B   , Tm41 Γ A → Tm41 Γ B → Tm41 Γ (prod41 A B))
     (fst   : ∀ Γ A B   , Tm41 Γ (prod41 A B) → Tm41 Γ A)
     (snd   : ∀ Γ A B   , Tm41 Γ (prod41 A B) → Tm41 Γ B)
     (left  : ∀ Γ A B   , Tm41 Γ A → Tm41 Γ (sum41 A B))
     (right : ∀ Γ A B   , Tm41 Γ B → Tm41 Γ (sum41 A B))
     (case  : ∀ Γ A B C , Tm41 Γ (sum41 A B) → Tm41 Γ (arr41 A C) → Tm41 Γ (arr41 B C) → Tm41 Γ C)
     (zero  : ∀ Γ       , Tm41 Γ nat41)
     (suc   : ∀ Γ       , Tm41 Γ nat41 → Tm41 Γ nat41)
     (rec   : ∀ Γ A     , Tm41 Γ nat41 → Tm41 Γ (arr41 nat41 (arr41 A A)) → Tm41 Γ A → Tm41 Γ A)
   , Tm41 Γ A.

Definition var41 {Γ A} : Var41 Γ A → Tm41 Γ A
 := λ x Tm41 var41 lam app tt pair fst snd left right case zero suc rec ,
     var41 _ _ x.

Definition lam41 {Γ A B} : Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B)
 := λ t Tm41 var41 lam41 app tt pair fst snd left right case zero suc rec ,
     lam41 _ _ _ (t Tm41 var41 lam41 app tt pair fst snd left right case zero suc rec).

Definition app41 {Γ A B} : Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B
 := λ t u Tm41 var41 lam41 app41 tt pair fst snd left right case zero suc rec ,
     app41 _ _ _
         (t Tm41 var41 lam41 app41 tt pair fst snd left right case zero suc rec)
         (u Tm41 var41 lam41 app41 tt pair fst snd left right case zero suc rec).

Definition tt41 {Γ} : Tm41 Γ top41
 := λ Tm41 var41 lam41 app41 tt41 pair fst snd left right case zero suc rec , tt41 _.

Definition pair41 {Γ A B} : Tm41 Γ A → Tm41 Γ B → Tm41 Γ (prod41 A B)
 := λ t u Tm41 var41 lam41 app41 tt41 pair41 fst snd left right case zero suc rec ,
     pair41 _ _ _
          (t Tm41 var41 lam41 app41 tt41 pair41 fst snd left right case zero suc rec)
          (u Tm41 var41 lam41 app41 tt41 pair41 fst snd left right case zero suc rec).

Definition fst41 {Γ A B} : Tm41 Γ (prod41 A B) → Tm41 Γ A
 := λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd left right case zero suc rec ,
     fst41 _ _ _
         (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd left right case zero suc rec).

Definition snd41 {Γ A B} : Tm41 Γ (prod41 A B) → Tm41 Γ B
 := λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left right case zero suc rec ,
     snd41 _ _ _
          (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left right case zero suc rec).

Definition left41 {Γ A B} : Tm41 Γ A → Tm41 Γ (sum41 A B)
 := λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right case zero suc rec ,
     left41 _ _ _
          (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right case zero suc rec).

Definition right41 {Γ A B} : Tm41 Γ B → Tm41 Γ (sum41 A B)
 := λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case zero suc rec ,
     right41 _ _ _
            (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case zero suc rec).

Definition case41 {Γ A B C} : Tm41 Γ (sum41 A B) → Tm41 Γ (arr41 A C) → Tm41 Γ (arr41 B C) → Tm41 Γ C
 := λ t u v Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero suc rec ,
     case41 _ _ _ _
           (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero suc rec)
           (u Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero suc rec)
           (v Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero suc rec).

Definition zero41  {Γ} : Tm41 Γ nat41
 := λ Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc rec , zero41 _.

Definition suc41 {Γ} : Tm41 Γ nat41 → Tm41 Γ nat41
 := λ t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec ,
   suc41 _ (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec).

Definition rec41 {Γ A} : Tm41 Γ nat41 → Tm41 Γ (arr41 nat41 (arr41 A A)) → Tm41 Γ A → Tm41 Γ A
 := λ t u v Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec41 ,
     rec41 _ _
         (t Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec41)
         (u Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec41)
         (v Tm41 var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 case41 zero41 suc41 rec41).

Definition v041 {Γ A} : Tm41 (snoc41 Γ A) A
 := var41 vz41.

Definition v141 {Γ A B} : Tm41 (snoc41 (snoc41 Γ A) B) A
 := var41 (vs41 vz41).

Definition v241 {Γ A B C} : Tm41 (snoc41 (snoc41 (snoc41 Γ A) B) C) A
 := var41 (vs41 (vs41 vz41)).

Definition v341 {Γ A B C D} : Tm41 (snoc41 (snoc41 (snoc41 (snoc41 Γ A) B) C) D) A
 := var41 (vs41 (vs41 (vs41 vz41))).

Definition tbool41 : Ty41
 := sum41 top41 top41.

Definition ttrue41 {Γ} : Tm41 Γ tbool41
 := left41 tt41.

Definition tfalse41 {Γ} : Tm41 Γ tbool41
 := right41 tt41.

Definition ifthenelse41 {Γ A} : Tm41 Γ (arr41 tbool41 (arr41 A (arr41 A A)))
 := lam41 (lam41 (lam41 (case41 v241 (lam41 v241) (lam41 v141)))).

Definition times441 {Γ A} : Tm41 Γ (arr41 (arr41 A A) (arr41 A A))
  := lam41 (lam41 (app41 v141 (app41 v141 (app41 v141 (app41 v141 v041))))).

Definition add41 {Γ} : Tm41 Γ (arr41 nat41 (arr41 nat41 nat41))
 := lam41 (rec41 v041
      (lam41 (lam41 (lam41 (suc41 (app41 v141 v041)))))
      (lam41 v041)).

Definition mul41 {Γ} : Tm41 Γ (arr41 nat41 (arr41 nat41 nat41))
 := lam41 (rec41 v041
     (lam41 (lam41 (lam41 (app41 (app41 add41 (app41 v141 v041)) v041))))
     (lam41 zero41)).

Definition fact41 {Γ} : Tm41 Γ (arr41 nat41 nat41)
 := lam41 (rec41 v041 (lam41 (lam41 (app41 (app41 mul41 (suc41 v141)) v041)))
        (suc41 zero41)).

Require Import Coq.Unicode.Utf8.

Definition Ty42 : Set
 := ∀ (Ty42           : Set)
      (nat top bot  : Ty42)
      (arr prod sum : Ty42 → Ty42 → Ty42)
    , Ty42.

Definition nat42 : Ty42 := λ _ nat42 _ _ _ _ _ , nat42.
Definition top42 : Ty42 := λ _ _ top42 _ _ _ _ , top42.
Definition bot42 : Ty42 := λ _ _ _ bot42 _ _ _ , bot42.

Definition arr42 : Ty42 → Ty42 → Ty42
 := λ A B Ty42 nat42 top42 bot42 arr42 prod sum ,
     arr42 (A Ty42 nat42 top42 bot42 arr42 prod sum) (B Ty42 nat42 top42 bot42 arr42 prod sum).

Definition prod42 : Ty42 → Ty42 → Ty42
 := λ A B Ty42 nat42 top42 bot42 arr42 prod42 sum ,
     prod42 (A Ty42 nat42 top42 bot42 arr42 prod42 sum) (B Ty42 nat42 top42 bot42 arr42 prod42 sum).

Definition sum42 : Ty42 → Ty42 → Ty42
 := λ A B Ty42 nat42 top42 bot42 arr42 prod42 sum42 ,
     sum42 (A Ty42 nat42 top42 bot42 arr42 prod42 sum42) (B Ty42 nat42 top42 bot42 arr42 prod42 sum42).

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
     (tt    : ∀ Γ       , Tm42 Γ top42)
     (pair  : ∀ Γ A B   , Tm42 Γ A → Tm42 Γ B → Tm42 Γ (prod42 A B))
     (fst   : ∀ Γ A B   , Tm42 Γ (prod42 A B) → Tm42 Γ A)
     (snd   : ∀ Γ A B   , Tm42 Γ (prod42 A B) → Tm42 Γ B)
     (left  : ∀ Γ A B   , Tm42 Γ A → Tm42 Γ (sum42 A B))
     (right : ∀ Γ A B   , Tm42 Γ B → Tm42 Γ (sum42 A B))
     (case  : ∀ Γ A B C , Tm42 Γ (sum42 A B) → Tm42 Γ (arr42 A C) → Tm42 Γ (arr42 B C) → Tm42 Γ C)
     (zero  : ∀ Γ       , Tm42 Γ nat42)
     (suc   : ∀ Γ       , Tm42 Γ nat42 → Tm42 Γ nat42)
     (rec   : ∀ Γ A     , Tm42 Γ nat42 → Tm42 Γ (arr42 nat42 (arr42 A A)) → Tm42 Γ A → Tm42 Γ A)
   , Tm42 Γ A.

Definition var42 {Γ A} : Var42 Γ A → Tm42 Γ A
 := λ x Tm42 var42 lam app tt pair fst snd left right case zero suc rec ,
     var42 _ _ x.

Definition lam42 {Γ A B} : Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B)
 := λ t Tm42 var42 lam42 app tt pair fst snd left right case zero suc rec ,
     lam42 _ _ _ (t Tm42 var42 lam42 app tt pair fst snd left right case zero suc rec).

Definition app42 {Γ A B} : Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B
 := λ t u Tm42 var42 lam42 app42 tt pair fst snd left right case zero suc rec ,
     app42 _ _ _
         (t Tm42 var42 lam42 app42 tt pair fst snd left right case zero suc rec)
         (u Tm42 var42 lam42 app42 tt pair fst snd left right case zero suc rec).

Definition tt42 {Γ} : Tm42 Γ top42
 := λ Tm42 var42 lam42 app42 tt42 pair fst snd left right case zero suc rec , tt42 _.

Definition pair42 {Γ A B} : Tm42 Γ A → Tm42 Γ B → Tm42 Γ (prod42 A B)
 := λ t u Tm42 var42 lam42 app42 tt42 pair42 fst snd left right case zero suc rec ,
     pair42 _ _ _
          (t Tm42 var42 lam42 app42 tt42 pair42 fst snd left right case zero suc rec)
          (u Tm42 var42 lam42 app42 tt42 pair42 fst snd left right case zero suc rec).

Definition fst42 {Γ A B} : Tm42 Γ (prod42 A B) → Tm42 Γ A
 := λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd left right case zero suc rec ,
     fst42 _ _ _
         (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd left right case zero suc rec).

Definition snd42 {Γ A B} : Tm42 Γ (prod42 A B) → Tm42 Γ B
 := λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left right case zero suc rec ,
     snd42 _ _ _
          (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left right case zero suc rec).

Definition left42 {Γ A B} : Tm42 Γ A → Tm42 Γ (sum42 A B)
 := λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right case zero suc rec ,
     left42 _ _ _
          (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right case zero suc rec).

Definition right42 {Γ A B} : Tm42 Γ B → Tm42 Γ (sum42 A B)
 := λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case zero suc rec ,
     right42 _ _ _
            (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case zero suc rec).

Definition case42 {Γ A B C} : Tm42 Γ (sum42 A B) → Tm42 Γ (arr42 A C) → Tm42 Γ (arr42 B C) → Tm42 Γ C
 := λ t u v Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero suc rec ,
     case42 _ _ _ _
           (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero suc rec)
           (u Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero suc rec)
           (v Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero suc rec).

Definition zero42  {Γ} : Tm42 Γ nat42
 := λ Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc rec , zero42 _.

Definition suc42 {Γ} : Tm42 Γ nat42 → Tm42 Γ nat42
 := λ t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec ,
   suc42 _ (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec).

Definition rec42 {Γ A} : Tm42 Γ nat42 → Tm42 Γ (arr42 nat42 (arr42 A A)) → Tm42 Γ A → Tm42 Γ A
 := λ t u v Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec42 ,
     rec42 _ _
         (t Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec42)
         (u Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec42)
         (v Tm42 var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 case42 zero42 suc42 rec42).

Definition v042 {Γ A} : Tm42 (snoc42 Γ A) A
 := var42 vz42.

Definition v142 {Γ A B} : Tm42 (snoc42 (snoc42 Γ A) B) A
 := var42 (vs42 vz42).

Definition v242 {Γ A B C} : Tm42 (snoc42 (snoc42 (snoc42 Γ A) B) C) A
 := var42 (vs42 (vs42 vz42)).

Definition v342 {Γ A B C D} : Tm42 (snoc42 (snoc42 (snoc42 (snoc42 Γ A) B) C) D) A
 := var42 (vs42 (vs42 (vs42 vz42))).

Definition tbool42 : Ty42
 := sum42 top42 top42.

Definition ttrue42 {Γ} : Tm42 Γ tbool42
 := left42 tt42.

Definition tfalse42 {Γ} : Tm42 Γ tbool42
 := right42 tt42.

Definition ifthenelse42 {Γ A} : Tm42 Γ (arr42 tbool42 (arr42 A (arr42 A A)))
 := lam42 (lam42 (lam42 (case42 v242 (lam42 v242) (lam42 v142)))).

Definition times442 {Γ A} : Tm42 Γ (arr42 (arr42 A A) (arr42 A A))
  := lam42 (lam42 (app42 v142 (app42 v142 (app42 v142 (app42 v142 v042))))).

Definition add42 {Γ} : Tm42 Γ (arr42 nat42 (arr42 nat42 nat42))
 := lam42 (rec42 v042
      (lam42 (lam42 (lam42 (suc42 (app42 v142 v042)))))
      (lam42 v042)).

Definition mul42 {Γ} : Tm42 Γ (arr42 nat42 (arr42 nat42 nat42))
 := lam42 (rec42 v042
     (lam42 (lam42 (lam42 (app42 (app42 add42 (app42 v142 v042)) v042))))
     (lam42 zero42)).

Definition fact42 {Γ} : Tm42 Γ (arr42 nat42 nat42)
 := lam42 (rec42 v042 (lam42 (lam42 (app42 (app42 mul42 (suc42 v142)) v042)))
        (suc42 zero42)).

Require Import Coq.Unicode.Utf8.

Definition Ty43 : Set
 := ∀ (Ty43           : Set)
      (nat top bot  : Ty43)
      (arr prod sum : Ty43 → Ty43 → Ty43)
    , Ty43.

Definition nat43 : Ty43 := λ _ nat43 _ _ _ _ _ , nat43.
Definition top43 : Ty43 := λ _ _ top43 _ _ _ _ , top43.
Definition bot43 : Ty43 := λ _ _ _ bot43 _ _ _ , bot43.

Definition arr43 : Ty43 → Ty43 → Ty43
 := λ A B Ty43 nat43 top43 bot43 arr43 prod sum ,
     arr43 (A Ty43 nat43 top43 bot43 arr43 prod sum) (B Ty43 nat43 top43 bot43 arr43 prod sum).

Definition prod43 : Ty43 → Ty43 → Ty43
 := λ A B Ty43 nat43 top43 bot43 arr43 prod43 sum ,
     prod43 (A Ty43 nat43 top43 bot43 arr43 prod43 sum) (B Ty43 nat43 top43 bot43 arr43 prod43 sum).

Definition sum43 : Ty43 → Ty43 → Ty43
 := λ A B Ty43 nat43 top43 bot43 arr43 prod43 sum43 ,
     sum43 (A Ty43 nat43 top43 bot43 arr43 prod43 sum43) (B Ty43 nat43 top43 bot43 arr43 prod43 sum43).

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
     (tt    : ∀ Γ       , Tm43 Γ top43)
     (pair  : ∀ Γ A B   , Tm43 Γ A → Tm43 Γ B → Tm43 Γ (prod43 A B))
     (fst   : ∀ Γ A B   , Tm43 Γ (prod43 A B) → Tm43 Γ A)
     (snd   : ∀ Γ A B   , Tm43 Γ (prod43 A B) → Tm43 Γ B)
     (left  : ∀ Γ A B   , Tm43 Γ A → Tm43 Γ (sum43 A B))
     (right : ∀ Γ A B   , Tm43 Γ B → Tm43 Γ (sum43 A B))
     (case  : ∀ Γ A B C , Tm43 Γ (sum43 A B) → Tm43 Γ (arr43 A C) → Tm43 Γ (arr43 B C) → Tm43 Γ C)
     (zero  : ∀ Γ       , Tm43 Γ nat43)
     (suc   : ∀ Γ       , Tm43 Γ nat43 → Tm43 Γ nat43)
     (rec   : ∀ Γ A     , Tm43 Γ nat43 → Tm43 Γ (arr43 nat43 (arr43 A A)) → Tm43 Γ A → Tm43 Γ A)
   , Tm43 Γ A.

Definition var43 {Γ A} : Var43 Γ A → Tm43 Γ A
 := λ x Tm43 var43 lam app tt pair fst snd left right case zero suc rec ,
     var43 _ _ x.

Definition lam43 {Γ A B} : Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B)
 := λ t Tm43 var43 lam43 app tt pair fst snd left right case zero suc rec ,
     lam43 _ _ _ (t Tm43 var43 lam43 app tt pair fst snd left right case zero suc rec).

Definition app43 {Γ A B} : Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B
 := λ t u Tm43 var43 lam43 app43 tt pair fst snd left right case zero suc rec ,
     app43 _ _ _
         (t Tm43 var43 lam43 app43 tt pair fst snd left right case zero suc rec)
         (u Tm43 var43 lam43 app43 tt pair fst snd left right case zero suc rec).

Definition tt43 {Γ} : Tm43 Γ top43
 := λ Tm43 var43 lam43 app43 tt43 pair fst snd left right case zero suc rec , tt43 _.

Definition pair43 {Γ A B} : Tm43 Γ A → Tm43 Γ B → Tm43 Γ (prod43 A B)
 := λ t u Tm43 var43 lam43 app43 tt43 pair43 fst snd left right case zero suc rec ,
     pair43 _ _ _
          (t Tm43 var43 lam43 app43 tt43 pair43 fst snd left right case zero suc rec)
          (u Tm43 var43 lam43 app43 tt43 pair43 fst snd left right case zero suc rec).

Definition fst43 {Γ A B} : Tm43 Γ (prod43 A B) → Tm43 Γ A
 := λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd left right case zero suc rec ,
     fst43 _ _ _
         (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd left right case zero suc rec).

Definition snd43 {Γ A B} : Tm43 Γ (prod43 A B) → Tm43 Γ B
 := λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left right case zero suc rec ,
     snd43 _ _ _
          (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left right case zero suc rec).

Definition left43 {Γ A B} : Tm43 Γ A → Tm43 Γ (sum43 A B)
 := λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right case zero suc rec ,
     left43 _ _ _
          (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right case zero suc rec).

Definition right43 {Γ A B} : Tm43 Γ B → Tm43 Γ (sum43 A B)
 := λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case zero suc rec ,
     right43 _ _ _
            (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case zero suc rec).

Definition case43 {Γ A B C} : Tm43 Γ (sum43 A B) → Tm43 Γ (arr43 A C) → Tm43 Γ (arr43 B C) → Tm43 Γ C
 := λ t u v Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero suc rec ,
     case43 _ _ _ _
           (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero suc rec)
           (u Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero suc rec)
           (v Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero suc rec).

Definition zero43  {Γ} : Tm43 Γ nat43
 := λ Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc rec , zero43 _.

Definition suc43 {Γ} : Tm43 Γ nat43 → Tm43 Γ nat43
 := λ t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec ,
   suc43 _ (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec).

Definition rec43 {Γ A} : Tm43 Γ nat43 → Tm43 Γ (arr43 nat43 (arr43 A A)) → Tm43 Γ A → Tm43 Γ A
 := λ t u v Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec43 ,
     rec43 _ _
         (t Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec43)
         (u Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec43)
         (v Tm43 var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 case43 zero43 suc43 rec43).

Definition v043 {Γ A} : Tm43 (snoc43 Γ A) A
 := var43 vz43.

Definition v143 {Γ A B} : Tm43 (snoc43 (snoc43 Γ A) B) A
 := var43 (vs43 vz43).

Definition v243 {Γ A B C} : Tm43 (snoc43 (snoc43 (snoc43 Γ A) B) C) A
 := var43 (vs43 (vs43 vz43)).

Definition v343 {Γ A B C D} : Tm43 (snoc43 (snoc43 (snoc43 (snoc43 Γ A) B) C) D) A
 := var43 (vs43 (vs43 (vs43 vz43))).

Definition tbool43 : Ty43
 := sum43 top43 top43.

Definition ttrue43 {Γ} : Tm43 Γ tbool43
 := left43 tt43.

Definition tfalse43 {Γ} : Tm43 Γ tbool43
 := right43 tt43.

Definition ifthenelse43 {Γ A} : Tm43 Γ (arr43 tbool43 (arr43 A (arr43 A A)))
 := lam43 (lam43 (lam43 (case43 v243 (lam43 v243) (lam43 v143)))).

Definition times443 {Γ A} : Tm43 Γ (arr43 (arr43 A A) (arr43 A A))
  := lam43 (lam43 (app43 v143 (app43 v143 (app43 v143 (app43 v143 v043))))).

Definition add43 {Γ} : Tm43 Γ (arr43 nat43 (arr43 nat43 nat43))
 := lam43 (rec43 v043
      (lam43 (lam43 (lam43 (suc43 (app43 v143 v043)))))
      (lam43 v043)).

Definition mul43 {Γ} : Tm43 Γ (arr43 nat43 (arr43 nat43 nat43))
 := lam43 (rec43 v043
     (lam43 (lam43 (lam43 (app43 (app43 add43 (app43 v143 v043)) v043))))
     (lam43 zero43)).

Definition fact43 {Γ} : Tm43 Γ (arr43 nat43 nat43)
 := lam43 (rec43 v043 (lam43 (lam43 (app43 (app43 mul43 (suc43 v143)) v043)))
        (suc43 zero43)).

Require Import Coq.Unicode.Utf8.

Definition Ty44 : Set
 := ∀ (Ty44           : Set)
      (nat top bot  : Ty44)
      (arr prod sum : Ty44 → Ty44 → Ty44)
    , Ty44.

Definition nat44 : Ty44 := λ _ nat44 _ _ _ _ _ , nat44.
Definition top44 : Ty44 := λ _ _ top44 _ _ _ _ , top44.
Definition bot44 : Ty44 := λ _ _ _ bot44 _ _ _ , bot44.

Definition arr44 : Ty44 → Ty44 → Ty44
 := λ A B Ty44 nat44 top44 bot44 arr44 prod sum ,
     arr44 (A Ty44 nat44 top44 bot44 arr44 prod sum) (B Ty44 nat44 top44 bot44 arr44 prod sum).

Definition prod44 : Ty44 → Ty44 → Ty44
 := λ A B Ty44 nat44 top44 bot44 arr44 prod44 sum ,
     prod44 (A Ty44 nat44 top44 bot44 arr44 prod44 sum) (B Ty44 nat44 top44 bot44 arr44 prod44 sum).

Definition sum44 : Ty44 → Ty44 → Ty44
 := λ A B Ty44 nat44 top44 bot44 arr44 prod44 sum44 ,
     sum44 (A Ty44 nat44 top44 bot44 arr44 prod44 sum44) (B Ty44 nat44 top44 bot44 arr44 prod44 sum44).

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
     (tt    : ∀ Γ       , Tm44 Γ top44)
     (pair  : ∀ Γ A B   , Tm44 Γ A → Tm44 Γ B → Tm44 Γ (prod44 A B))
     (fst   : ∀ Γ A B   , Tm44 Γ (prod44 A B) → Tm44 Γ A)
     (snd   : ∀ Γ A B   , Tm44 Γ (prod44 A B) → Tm44 Γ B)
     (left  : ∀ Γ A B   , Tm44 Γ A → Tm44 Γ (sum44 A B))
     (right : ∀ Γ A B   , Tm44 Γ B → Tm44 Γ (sum44 A B))
     (case  : ∀ Γ A B C , Tm44 Γ (sum44 A B) → Tm44 Γ (arr44 A C) → Tm44 Γ (arr44 B C) → Tm44 Γ C)
     (zero  : ∀ Γ       , Tm44 Γ nat44)
     (suc   : ∀ Γ       , Tm44 Γ nat44 → Tm44 Γ nat44)
     (rec   : ∀ Γ A     , Tm44 Γ nat44 → Tm44 Γ (arr44 nat44 (arr44 A A)) → Tm44 Γ A → Tm44 Γ A)
   , Tm44 Γ A.

Definition var44 {Γ A} : Var44 Γ A → Tm44 Γ A
 := λ x Tm44 var44 lam app tt pair fst snd left right case zero suc rec ,
     var44 _ _ x.

Definition lam44 {Γ A B} : Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B)
 := λ t Tm44 var44 lam44 app tt pair fst snd left right case zero suc rec ,
     lam44 _ _ _ (t Tm44 var44 lam44 app tt pair fst snd left right case zero suc rec).

Definition app44 {Γ A B} : Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B
 := λ t u Tm44 var44 lam44 app44 tt pair fst snd left right case zero suc rec ,
     app44 _ _ _
         (t Tm44 var44 lam44 app44 tt pair fst snd left right case zero suc rec)
         (u Tm44 var44 lam44 app44 tt pair fst snd left right case zero suc rec).

Definition tt44 {Γ} : Tm44 Γ top44
 := λ Tm44 var44 lam44 app44 tt44 pair fst snd left right case zero suc rec , tt44 _.

Definition pair44 {Γ A B} : Tm44 Γ A → Tm44 Γ B → Tm44 Γ (prod44 A B)
 := λ t u Tm44 var44 lam44 app44 tt44 pair44 fst snd left right case zero suc rec ,
     pair44 _ _ _
          (t Tm44 var44 lam44 app44 tt44 pair44 fst snd left right case zero suc rec)
          (u Tm44 var44 lam44 app44 tt44 pair44 fst snd left right case zero suc rec).

Definition fst44 {Γ A B} : Tm44 Γ (prod44 A B) → Tm44 Γ A
 := λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd left right case zero suc rec ,
     fst44 _ _ _
         (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd left right case zero suc rec).

Definition snd44 {Γ A B} : Tm44 Γ (prod44 A B) → Tm44 Γ B
 := λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left right case zero suc rec ,
     snd44 _ _ _
          (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left right case zero suc rec).

Definition left44 {Γ A B} : Tm44 Γ A → Tm44 Γ (sum44 A B)
 := λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right case zero suc rec ,
     left44 _ _ _
          (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right case zero suc rec).

Definition right44 {Γ A B} : Tm44 Γ B → Tm44 Γ (sum44 A B)
 := λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case zero suc rec ,
     right44 _ _ _
            (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case zero suc rec).

Definition case44 {Γ A B C} : Tm44 Γ (sum44 A B) → Tm44 Γ (arr44 A C) → Tm44 Γ (arr44 B C) → Tm44 Γ C
 := λ t u v Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero suc rec ,
     case44 _ _ _ _
           (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero suc rec)
           (u Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero suc rec)
           (v Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero suc rec).

Definition zero44  {Γ} : Tm44 Γ nat44
 := λ Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc rec , zero44 _.

Definition suc44 {Γ} : Tm44 Γ nat44 → Tm44 Γ nat44
 := λ t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec ,
   suc44 _ (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec).

Definition rec44 {Γ A} : Tm44 Γ nat44 → Tm44 Γ (arr44 nat44 (arr44 A A)) → Tm44 Γ A → Tm44 Γ A
 := λ t u v Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec44 ,
     rec44 _ _
         (t Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec44)
         (u Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec44)
         (v Tm44 var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 case44 zero44 suc44 rec44).

Definition v044 {Γ A} : Tm44 (snoc44 Γ A) A
 := var44 vz44.

Definition v144 {Γ A B} : Tm44 (snoc44 (snoc44 Γ A) B) A
 := var44 (vs44 vz44).

Definition v244 {Γ A B C} : Tm44 (snoc44 (snoc44 (snoc44 Γ A) B) C) A
 := var44 (vs44 (vs44 vz44)).

Definition v344 {Γ A B C D} : Tm44 (snoc44 (snoc44 (snoc44 (snoc44 Γ A) B) C) D) A
 := var44 (vs44 (vs44 (vs44 vz44))).

Definition tbool44 : Ty44
 := sum44 top44 top44.

Definition ttrue44 {Γ} : Tm44 Γ tbool44
 := left44 tt44.

Definition tfalse44 {Γ} : Tm44 Γ tbool44
 := right44 tt44.

Definition ifthenelse44 {Γ A} : Tm44 Γ (arr44 tbool44 (arr44 A (arr44 A A)))
 := lam44 (lam44 (lam44 (case44 v244 (lam44 v244) (lam44 v144)))).

Definition times444 {Γ A} : Tm44 Γ (arr44 (arr44 A A) (arr44 A A))
  := lam44 (lam44 (app44 v144 (app44 v144 (app44 v144 (app44 v144 v044))))).

Definition add44 {Γ} : Tm44 Γ (arr44 nat44 (arr44 nat44 nat44))
 := lam44 (rec44 v044
      (lam44 (lam44 (lam44 (suc44 (app44 v144 v044)))))
      (lam44 v044)).

Definition mul44 {Γ} : Tm44 Γ (arr44 nat44 (arr44 nat44 nat44))
 := lam44 (rec44 v044
     (lam44 (lam44 (lam44 (app44 (app44 add44 (app44 v144 v044)) v044))))
     (lam44 zero44)).

Definition fact44 {Γ} : Tm44 Γ (arr44 nat44 nat44)
 := lam44 (rec44 v044 (lam44 (lam44 (app44 (app44 mul44 (suc44 v144)) v044)))
        (suc44 zero44)).

Require Import Coq.Unicode.Utf8.

Definition Ty45 : Set
 := ∀ (Ty45           : Set)
      (nat top bot  : Ty45)
      (arr prod sum : Ty45 → Ty45 → Ty45)
    , Ty45.

Definition nat45 : Ty45 := λ _ nat45 _ _ _ _ _ , nat45.
Definition top45 : Ty45 := λ _ _ top45 _ _ _ _ , top45.
Definition bot45 : Ty45 := λ _ _ _ bot45 _ _ _ , bot45.

Definition arr45 : Ty45 → Ty45 → Ty45
 := λ A B Ty45 nat45 top45 bot45 arr45 prod sum ,
     arr45 (A Ty45 nat45 top45 bot45 arr45 prod sum) (B Ty45 nat45 top45 bot45 arr45 prod sum).

Definition prod45 : Ty45 → Ty45 → Ty45
 := λ A B Ty45 nat45 top45 bot45 arr45 prod45 sum ,
     prod45 (A Ty45 nat45 top45 bot45 arr45 prod45 sum) (B Ty45 nat45 top45 bot45 arr45 prod45 sum).

Definition sum45 : Ty45 → Ty45 → Ty45
 := λ A B Ty45 nat45 top45 bot45 arr45 prod45 sum45 ,
     sum45 (A Ty45 nat45 top45 bot45 arr45 prod45 sum45) (B Ty45 nat45 top45 bot45 arr45 prod45 sum45).

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
     (tt    : ∀ Γ       , Tm45 Γ top45)
     (pair  : ∀ Γ A B   , Tm45 Γ A → Tm45 Γ B → Tm45 Γ (prod45 A B))
     (fst   : ∀ Γ A B   , Tm45 Γ (prod45 A B) → Tm45 Γ A)
     (snd   : ∀ Γ A B   , Tm45 Γ (prod45 A B) → Tm45 Γ B)
     (left  : ∀ Γ A B   , Tm45 Γ A → Tm45 Γ (sum45 A B))
     (right : ∀ Γ A B   , Tm45 Γ B → Tm45 Γ (sum45 A B))
     (case  : ∀ Γ A B C , Tm45 Γ (sum45 A B) → Tm45 Γ (arr45 A C) → Tm45 Γ (arr45 B C) → Tm45 Γ C)
     (zero  : ∀ Γ       , Tm45 Γ nat45)
     (suc   : ∀ Γ       , Tm45 Γ nat45 → Tm45 Γ nat45)
     (rec   : ∀ Γ A     , Tm45 Γ nat45 → Tm45 Γ (arr45 nat45 (arr45 A A)) → Tm45 Γ A → Tm45 Γ A)
   , Tm45 Γ A.

Definition var45 {Γ A} : Var45 Γ A → Tm45 Γ A
 := λ x Tm45 var45 lam app tt pair fst snd left right case zero suc rec ,
     var45 _ _ x.

Definition lam45 {Γ A B} : Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B)
 := λ t Tm45 var45 lam45 app tt pair fst snd left right case zero suc rec ,
     lam45 _ _ _ (t Tm45 var45 lam45 app tt pair fst snd left right case zero suc rec).

Definition app45 {Γ A B} : Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B
 := λ t u Tm45 var45 lam45 app45 tt pair fst snd left right case zero suc rec ,
     app45 _ _ _
         (t Tm45 var45 lam45 app45 tt pair fst snd left right case zero suc rec)
         (u Tm45 var45 lam45 app45 tt pair fst snd left right case zero suc rec).

Definition tt45 {Γ} : Tm45 Γ top45
 := λ Tm45 var45 lam45 app45 tt45 pair fst snd left right case zero suc rec , tt45 _.

Definition pair45 {Γ A B} : Tm45 Γ A → Tm45 Γ B → Tm45 Γ (prod45 A B)
 := λ t u Tm45 var45 lam45 app45 tt45 pair45 fst snd left right case zero suc rec ,
     pair45 _ _ _
          (t Tm45 var45 lam45 app45 tt45 pair45 fst snd left right case zero suc rec)
          (u Tm45 var45 lam45 app45 tt45 pair45 fst snd left right case zero suc rec).

Definition fst45 {Γ A B} : Tm45 Γ (prod45 A B) → Tm45 Γ A
 := λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd left right case zero suc rec ,
     fst45 _ _ _
         (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd left right case zero suc rec).

Definition snd45 {Γ A B} : Tm45 Γ (prod45 A B) → Tm45 Γ B
 := λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left right case zero suc rec ,
     snd45 _ _ _
          (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left right case zero suc rec).

Definition left45 {Γ A B} : Tm45 Γ A → Tm45 Γ (sum45 A B)
 := λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right case zero suc rec ,
     left45 _ _ _
          (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right case zero suc rec).

Definition right45 {Γ A B} : Tm45 Γ B → Tm45 Γ (sum45 A B)
 := λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case zero suc rec ,
     right45 _ _ _
            (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case zero suc rec).

Definition case45 {Γ A B C} : Tm45 Γ (sum45 A B) → Tm45 Γ (arr45 A C) → Tm45 Γ (arr45 B C) → Tm45 Γ C
 := λ t u v Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero suc rec ,
     case45 _ _ _ _
           (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero suc rec)
           (u Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero suc rec)
           (v Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero suc rec).

Definition zero45  {Γ} : Tm45 Γ nat45
 := λ Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc rec , zero45 _.

Definition suc45 {Γ} : Tm45 Γ nat45 → Tm45 Γ nat45
 := λ t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec ,
   suc45 _ (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec).

Definition rec45 {Γ A} : Tm45 Γ nat45 → Tm45 Γ (arr45 nat45 (arr45 A A)) → Tm45 Γ A → Tm45 Γ A
 := λ t u v Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec45 ,
     rec45 _ _
         (t Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec45)
         (u Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec45)
         (v Tm45 var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 case45 zero45 suc45 rec45).

Definition v045 {Γ A} : Tm45 (snoc45 Γ A) A
 := var45 vz45.

Definition v145 {Γ A B} : Tm45 (snoc45 (snoc45 Γ A) B) A
 := var45 (vs45 vz45).

Definition v245 {Γ A B C} : Tm45 (snoc45 (snoc45 (snoc45 Γ A) B) C) A
 := var45 (vs45 (vs45 vz45)).

Definition v345 {Γ A B C D} : Tm45 (snoc45 (snoc45 (snoc45 (snoc45 Γ A) B) C) D) A
 := var45 (vs45 (vs45 (vs45 vz45))).

Definition tbool45 : Ty45
 := sum45 top45 top45.

Definition ttrue45 {Γ} : Tm45 Γ tbool45
 := left45 tt45.

Definition tfalse45 {Γ} : Tm45 Γ tbool45
 := right45 tt45.

Definition ifthenelse45 {Γ A} : Tm45 Γ (arr45 tbool45 (arr45 A (arr45 A A)))
 := lam45 (lam45 (lam45 (case45 v245 (lam45 v245) (lam45 v145)))).

Definition times445 {Γ A} : Tm45 Γ (arr45 (arr45 A A) (arr45 A A))
  := lam45 (lam45 (app45 v145 (app45 v145 (app45 v145 (app45 v145 v045))))).

Definition add45 {Γ} : Tm45 Γ (arr45 nat45 (arr45 nat45 nat45))
 := lam45 (rec45 v045
      (lam45 (lam45 (lam45 (suc45 (app45 v145 v045)))))
      (lam45 v045)).

Definition mul45 {Γ} : Tm45 Γ (arr45 nat45 (arr45 nat45 nat45))
 := lam45 (rec45 v045
     (lam45 (lam45 (lam45 (app45 (app45 add45 (app45 v145 v045)) v045))))
     (lam45 zero45)).

Definition fact45 {Γ} : Tm45 Γ (arr45 nat45 nat45)
 := lam45 (rec45 v045 (lam45 (lam45 (app45 (app45 mul45 (suc45 v145)) v045)))
        (suc45 zero45)).

Require Import Coq.Unicode.Utf8.

Definition Ty46 : Set
 := ∀ (Ty46           : Set)
      (nat top bot  : Ty46)
      (arr prod sum : Ty46 → Ty46 → Ty46)
    , Ty46.

Definition nat46 : Ty46 := λ _ nat46 _ _ _ _ _ , nat46.
Definition top46 : Ty46 := λ _ _ top46 _ _ _ _ , top46.
Definition bot46 : Ty46 := λ _ _ _ bot46 _ _ _ , bot46.

Definition arr46 : Ty46 → Ty46 → Ty46
 := λ A B Ty46 nat46 top46 bot46 arr46 prod sum ,
     arr46 (A Ty46 nat46 top46 bot46 arr46 prod sum) (B Ty46 nat46 top46 bot46 arr46 prod sum).

Definition prod46 : Ty46 → Ty46 → Ty46
 := λ A B Ty46 nat46 top46 bot46 arr46 prod46 sum ,
     prod46 (A Ty46 nat46 top46 bot46 arr46 prod46 sum) (B Ty46 nat46 top46 bot46 arr46 prod46 sum).

Definition sum46 : Ty46 → Ty46 → Ty46
 := λ A B Ty46 nat46 top46 bot46 arr46 prod46 sum46 ,
     sum46 (A Ty46 nat46 top46 bot46 arr46 prod46 sum46) (B Ty46 nat46 top46 bot46 arr46 prod46 sum46).

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
     (tt    : ∀ Γ       , Tm46 Γ top46)
     (pair  : ∀ Γ A B   , Tm46 Γ A → Tm46 Γ B → Tm46 Γ (prod46 A B))
     (fst   : ∀ Γ A B   , Tm46 Γ (prod46 A B) → Tm46 Γ A)
     (snd   : ∀ Γ A B   , Tm46 Γ (prod46 A B) → Tm46 Γ B)
     (left  : ∀ Γ A B   , Tm46 Γ A → Tm46 Γ (sum46 A B))
     (right : ∀ Γ A B   , Tm46 Γ B → Tm46 Γ (sum46 A B))
     (case  : ∀ Γ A B C , Tm46 Γ (sum46 A B) → Tm46 Γ (arr46 A C) → Tm46 Γ (arr46 B C) → Tm46 Γ C)
     (zero  : ∀ Γ       , Tm46 Γ nat46)
     (suc   : ∀ Γ       , Tm46 Γ nat46 → Tm46 Γ nat46)
     (rec   : ∀ Γ A     , Tm46 Γ nat46 → Tm46 Γ (arr46 nat46 (arr46 A A)) → Tm46 Γ A → Tm46 Γ A)
   , Tm46 Γ A.

Definition var46 {Γ A} : Var46 Γ A → Tm46 Γ A
 := λ x Tm46 var46 lam app tt pair fst snd left right case zero suc rec ,
     var46 _ _ x.

Definition lam46 {Γ A B} : Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B)
 := λ t Tm46 var46 lam46 app tt pair fst snd left right case zero suc rec ,
     lam46 _ _ _ (t Tm46 var46 lam46 app tt pair fst snd left right case zero suc rec).

Definition app46 {Γ A B} : Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B
 := λ t u Tm46 var46 lam46 app46 tt pair fst snd left right case zero suc rec ,
     app46 _ _ _
         (t Tm46 var46 lam46 app46 tt pair fst snd left right case zero suc rec)
         (u Tm46 var46 lam46 app46 tt pair fst snd left right case zero suc rec).

Definition tt46 {Γ} : Tm46 Γ top46
 := λ Tm46 var46 lam46 app46 tt46 pair fst snd left right case zero suc rec , tt46 _.

Definition pair46 {Γ A B} : Tm46 Γ A → Tm46 Γ B → Tm46 Γ (prod46 A B)
 := λ t u Tm46 var46 lam46 app46 tt46 pair46 fst snd left right case zero suc rec ,
     pair46 _ _ _
          (t Tm46 var46 lam46 app46 tt46 pair46 fst snd left right case zero suc rec)
          (u Tm46 var46 lam46 app46 tt46 pair46 fst snd left right case zero suc rec).

Definition fst46 {Γ A B} : Tm46 Γ (prod46 A B) → Tm46 Γ A
 := λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd left right case zero suc rec ,
     fst46 _ _ _
         (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd left right case zero suc rec).

Definition snd46 {Γ A B} : Tm46 Γ (prod46 A B) → Tm46 Γ B
 := λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left right case zero suc rec ,
     snd46 _ _ _
          (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left right case zero suc rec).

Definition left46 {Γ A B} : Tm46 Γ A → Tm46 Γ (sum46 A B)
 := λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right case zero suc rec ,
     left46 _ _ _
          (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right case zero suc rec).

Definition right46 {Γ A B} : Tm46 Γ B → Tm46 Γ (sum46 A B)
 := λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case zero suc rec ,
     right46 _ _ _
            (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case zero suc rec).

Definition case46 {Γ A B C} : Tm46 Γ (sum46 A B) → Tm46 Γ (arr46 A C) → Tm46 Γ (arr46 B C) → Tm46 Γ C
 := λ t u v Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero suc rec ,
     case46 _ _ _ _
           (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero suc rec)
           (u Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero suc rec)
           (v Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero suc rec).

Definition zero46  {Γ} : Tm46 Γ nat46
 := λ Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc rec , zero46 _.

Definition suc46 {Γ} : Tm46 Γ nat46 → Tm46 Γ nat46
 := λ t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec ,
   suc46 _ (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec).

Definition rec46 {Γ A} : Tm46 Γ nat46 → Tm46 Γ (arr46 nat46 (arr46 A A)) → Tm46 Γ A → Tm46 Γ A
 := λ t u v Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec46 ,
     rec46 _ _
         (t Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec46)
         (u Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec46)
         (v Tm46 var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 case46 zero46 suc46 rec46).

Definition v046 {Γ A} : Tm46 (snoc46 Γ A) A
 := var46 vz46.

Definition v146 {Γ A B} : Tm46 (snoc46 (snoc46 Γ A) B) A
 := var46 (vs46 vz46).

Definition v246 {Γ A B C} : Tm46 (snoc46 (snoc46 (snoc46 Γ A) B) C) A
 := var46 (vs46 (vs46 vz46)).

Definition v346 {Γ A B C D} : Tm46 (snoc46 (snoc46 (snoc46 (snoc46 Γ A) B) C) D) A
 := var46 (vs46 (vs46 (vs46 vz46))).

Definition tbool46 : Ty46
 := sum46 top46 top46.

Definition ttrue46 {Γ} : Tm46 Γ tbool46
 := left46 tt46.

Definition tfalse46 {Γ} : Tm46 Γ tbool46
 := right46 tt46.

Definition ifthenelse46 {Γ A} : Tm46 Γ (arr46 tbool46 (arr46 A (arr46 A A)))
 := lam46 (lam46 (lam46 (case46 v246 (lam46 v246) (lam46 v146)))).

Definition times446 {Γ A} : Tm46 Γ (arr46 (arr46 A A) (arr46 A A))
  := lam46 (lam46 (app46 v146 (app46 v146 (app46 v146 (app46 v146 v046))))).

Definition add46 {Γ} : Tm46 Γ (arr46 nat46 (arr46 nat46 nat46))
 := lam46 (rec46 v046
      (lam46 (lam46 (lam46 (suc46 (app46 v146 v046)))))
      (lam46 v046)).

Definition mul46 {Γ} : Tm46 Γ (arr46 nat46 (arr46 nat46 nat46))
 := lam46 (rec46 v046
     (lam46 (lam46 (lam46 (app46 (app46 add46 (app46 v146 v046)) v046))))
     (lam46 zero46)).

Definition fact46 {Γ} : Tm46 Γ (arr46 nat46 nat46)
 := lam46 (rec46 v046 (lam46 (lam46 (app46 (app46 mul46 (suc46 v146)) v046)))
        (suc46 zero46)).

Require Import Coq.Unicode.Utf8.

Definition Ty47 : Set
 := ∀ (Ty47           : Set)
      (nat top bot  : Ty47)
      (arr prod sum : Ty47 → Ty47 → Ty47)
    , Ty47.

Definition nat47 : Ty47 := λ _ nat47 _ _ _ _ _ , nat47.
Definition top47 : Ty47 := λ _ _ top47 _ _ _ _ , top47.
Definition bot47 : Ty47 := λ _ _ _ bot47 _ _ _ , bot47.

Definition arr47 : Ty47 → Ty47 → Ty47
 := λ A B Ty47 nat47 top47 bot47 arr47 prod sum ,
     arr47 (A Ty47 nat47 top47 bot47 arr47 prod sum) (B Ty47 nat47 top47 bot47 arr47 prod sum).

Definition prod47 : Ty47 → Ty47 → Ty47
 := λ A B Ty47 nat47 top47 bot47 arr47 prod47 sum ,
     prod47 (A Ty47 nat47 top47 bot47 arr47 prod47 sum) (B Ty47 nat47 top47 bot47 arr47 prod47 sum).

Definition sum47 : Ty47 → Ty47 → Ty47
 := λ A B Ty47 nat47 top47 bot47 arr47 prod47 sum47 ,
     sum47 (A Ty47 nat47 top47 bot47 arr47 prod47 sum47) (B Ty47 nat47 top47 bot47 arr47 prod47 sum47).

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
     (tt    : ∀ Γ       , Tm47 Γ top47)
     (pair  : ∀ Γ A B   , Tm47 Γ A → Tm47 Γ B → Tm47 Γ (prod47 A B))
     (fst   : ∀ Γ A B   , Tm47 Γ (prod47 A B) → Tm47 Γ A)
     (snd   : ∀ Γ A B   , Tm47 Γ (prod47 A B) → Tm47 Γ B)
     (left  : ∀ Γ A B   , Tm47 Γ A → Tm47 Γ (sum47 A B))
     (right : ∀ Γ A B   , Tm47 Γ B → Tm47 Γ (sum47 A B))
     (case  : ∀ Γ A B C , Tm47 Γ (sum47 A B) → Tm47 Γ (arr47 A C) → Tm47 Γ (arr47 B C) → Tm47 Γ C)
     (zero  : ∀ Γ       , Tm47 Γ nat47)
     (suc   : ∀ Γ       , Tm47 Γ nat47 → Tm47 Γ nat47)
     (rec   : ∀ Γ A     , Tm47 Γ nat47 → Tm47 Γ (arr47 nat47 (arr47 A A)) → Tm47 Γ A → Tm47 Γ A)
   , Tm47 Γ A.

Definition var47 {Γ A} : Var47 Γ A → Tm47 Γ A
 := λ x Tm47 var47 lam app tt pair fst snd left right case zero suc rec ,
     var47 _ _ x.

Definition lam47 {Γ A B} : Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B)
 := λ t Tm47 var47 lam47 app tt pair fst snd left right case zero suc rec ,
     lam47 _ _ _ (t Tm47 var47 lam47 app tt pair fst snd left right case zero suc rec).

Definition app47 {Γ A B} : Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B
 := λ t u Tm47 var47 lam47 app47 tt pair fst snd left right case zero suc rec ,
     app47 _ _ _
         (t Tm47 var47 lam47 app47 tt pair fst snd left right case zero suc rec)
         (u Tm47 var47 lam47 app47 tt pair fst snd left right case zero suc rec).

Definition tt47 {Γ} : Tm47 Γ top47
 := λ Tm47 var47 lam47 app47 tt47 pair fst snd left right case zero suc rec , tt47 _.

Definition pair47 {Γ A B} : Tm47 Γ A → Tm47 Γ B → Tm47 Γ (prod47 A B)
 := λ t u Tm47 var47 lam47 app47 tt47 pair47 fst snd left right case zero suc rec ,
     pair47 _ _ _
          (t Tm47 var47 lam47 app47 tt47 pair47 fst snd left right case zero suc rec)
          (u Tm47 var47 lam47 app47 tt47 pair47 fst snd left right case zero suc rec).

Definition fst47 {Γ A B} : Tm47 Γ (prod47 A B) → Tm47 Γ A
 := λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd left right case zero suc rec ,
     fst47 _ _ _
         (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd left right case zero suc rec).

Definition snd47 {Γ A B} : Tm47 Γ (prod47 A B) → Tm47 Γ B
 := λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left right case zero suc rec ,
     snd47 _ _ _
          (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left right case zero suc rec).

Definition left47 {Γ A B} : Tm47 Γ A → Tm47 Γ (sum47 A B)
 := λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right case zero suc rec ,
     left47 _ _ _
          (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right case zero suc rec).

Definition right47 {Γ A B} : Tm47 Γ B → Tm47 Γ (sum47 A B)
 := λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case zero suc rec ,
     right47 _ _ _
            (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case zero suc rec).

Definition case47 {Γ A B C} : Tm47 Γ (sum47 A B) → Tm47 Γ (arr47 A C) → Tm47 Γ (arr47 B C) → Tm47 Γ C
 := λ t u v Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero suc rec ,
     case47 _ _ _ _
           (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero suc rec)
           (u Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero suc rec)
           (v Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero suc rec).

Definition zero47  {Γ} : Tm47 Γ nat47
 := λ Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc rec , zero47 _.

Definition suc47 {Γ} : Tm47 Γ nat47 → Tm47 Γ nat47
 := λ t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec ,
   suc47 _ (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec).

Definition rec47 {Γ A} : Tm47 Γ nat47 → Tm47 Γ (arr47 nat47 (arr47 A A)) → Tm47 Γ A → Tm47 Γ A
 := λ t u v Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec47 ,
     rec47 _ _
         (t Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec47)
         (u Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec47)
         (v Tm47 var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 case47 zero47 suc47 rec47).

Definition v047 {Γ A} : Tm47 (snoc47 Γ A) A
 := var47 vz47.

Definition v147 {Γ A B} : Tm47 (snoc47 (snoc47 Γ A) B) A
 := var47 (vs47 vz47).

Definition v247 {Γ A B C} : Tm47 (snoc47 (snoc47 (snoc47 Γ A) B) C) A
 := var47 (vs47 (vs47 vz47)).

Definition v347 {Γ A B C D} : Tm47 (snoc47 (snoc47 (snoc47 (snoc47 Γ A) B) C) D) A
 := var47 (vs47 (vs47 (vs47 vz47))).

Definition tbool47 : Ty47
 := sum47 top47 top47.

Definition ttrue47 {Γ} : Tm47 Γ tbool47
 := left47 tt47.

Definition tfalse47 {Γ} : Tm47 Γ tbool47
 := right47 tt47.

Definition ifthenelse47 {Γ A} : Tm47 Γ (arr47 tbool47 (arr47 A (arr47 A A)))
 := lam47 (lam47 (lam47 (case47 v247 (lam47 v247) (lam47 v147)))).

Definition times447 {Γ A} : Tm47 Γ (arr47 (arr47 A A) (arr47 A A))
  := lam47 (lam47 (app47 v147 (app47 v147 (app47 v147 (app47 v147 v047))))).

Definition add47 {Γ} : Tm47 Γ (arr47 nat47 (arr47 nat47 nat47))
 := lam47 (rec47 v047
      (lam47 (lam47 (lam47 (suc47 (app47 v147 v047)))))
      (lam47 v047)).

Definition mul47 {Γ} : Tm47 Γ (arr47 nat47 (arr47 nat47 nat47))
 := lam47 (rec47 v047
     (lam47 (lam47 (lam47 (app47 (app47 add47 (app47 v147 v047)) v047))))
     (lam47 zero47)).

Definition fact47 {Γ} : Tm47 Γ (arr47 nat47 nat47)
 := lam47 (rec47 v047 (lam47 (lam47 (app47 (app47 mul47 (suc47 v147)) v047)))
        (suc47 zero47)).

Require Import Coq.Unicode.Utf8.

Definition Ty48 : Set
 := ∀ (Ty48           : Set)
      (nat top bot  : Ty48)
      (arr prod sum : Ty48 → Ty48 → Ty48)
    , Ty48.

Definition nat48 : Ty48 := λ _ nat48 _ _ _ _ _ , nat48.
Definition top48 : Ty48 := λ _ _ top48 _ _ _ _ , top48.
Definition bot48 : Ty48 := λ _ _ _ bot48 _ _ _ , bot48.

Definition arr48 : Ty48 → Ty48 → Ty48
 := λ A B Ty48 nat48 top48 bot48 arr48 prod sum ,
     arr48 (A Ty48 nat48 top48 bot48 arr48 prod sum) (B Ty48 nat48 top48 bot48 arr48 prod sum).

Definition prod48 : Ty48 → Ty48 → Ty48
 := λ A B Ty48 nat48 top48 bot48 arr48 prod48 sum ,
     prod48 (A Ty48 nat48 top48 bot48 arr48 prod48 sum) (B Ty48 nat48 top48 bot48 arr48 prod48 sum).

Definition sum48 : Ty48 → Ty48 → Ty48
 := λ A B Ty48 nat48 top48 bot48 arr48 prod48 sum48 ,
     sum48 (A Ty48 nat48 top48 bot48 arr48 prod48 sum48) (B Ty48 nat48 top48 bot48 arr48 prod48 sum48).

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
     (tt    : ∀ Γ       , Tm48 Γ top48)
     (pair  : ∀ Γ A B   , Tm48 Γ A → Tm48 Γ B → Tm48 Γ (prod48 A B))
     (fst   : ∀ Γ A B   , Tm48 Γ (prod48 A B) → Tm48 Γ A)
     (snd   : ∀ Γ A B   , Tm48 Γ (prod48 A B) → Tm48 Γ B)
     (left  : ∀ Γ A B   , Tm48 Γ A → Tm48 Γ (sum48 A B))
     (right : ∀ Γ A B   , Tm48 Γ B → Tm48 Γ (sum48 A B))
     (case  : ∀ Γ A B C , Tm48 Γ (sum48 A B) → Tm48 Γ (arr48 A C) → Tm48 Γ (arr48 B C) → Tm48 Γ C)
     (zero  : ∀ Γ       , Tm48 Γ nat48)
     (suc   : ∀ Γ       , Tm48 Γ nat48 → Tm48 Γ nat48)
     (rec   : ∀ Γ A     , Tm48 Γ nat48 → Tm48 Γ (arr48 nat48 (arr48 A A)) → Tm48 Γ A → Tm48 Γ A)
   , Tm48 Γ A.

Definition var48 {Γ A} : Var48 Γ A → Tm48 Γ A
 := λ x Tm48 var48 lam app tt pair fst snd left right case zero suc rec ,
     var48 _ _ x.

Definition lam48 {Γ A B} : Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B)
 := λ t Tm48 var48 lam48 app tt pair fst snd left right case zero suc rec ,
     lam48 _ _ _ (t Tm48 var48 lam48 app tt pair fst snd left right case zero suc rec).

Definition app48 {Γ A B} : Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B
 := λ t u Tm48 var48 lam48 app48 tt pair fst snd left right case zero suc rec ,
     app48 _ _ _
         (t Tm48 var48 lam48 app48 tt pair fst snd left right case zero suc rec)
         (u Tm48 var48 lam48 app48 tt pair fst snd left right case zero suc rec).

Definition tt48 {Γ} : Tm48 Γ top48
 := λ Tm48 var48 lam48 app48 tt48 pair fst snd left right case zero suc rec , tt48 _.

Definition pair48 {Γ A B} : Tm48 Γ A → Tm48 Γ B → Tm48 Γ (prod48 A B)
 := λ t u Tm48 var48 lam48 app48 tt48 pair48 fst snd left right case zero suc rec ,
     pair48 _ _ _
          (t Tm48 var48 lam48 app48 tt48 pair48 fst snd left right case zero suc rec)
          (u Tm48 var48 lam48 app48 tt48 pair48 fst snd left right case zero suc rec).

Definition fst48 {Γ A B} : Tm48 Γ (prod48 A B) → Tm48 Γ A
 := λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd left right case zero suc rec ,
     fst48 _ _ _
         (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd left right case zero suc rec).

Definition snd48 {Γ A B} : Tm48 Γ (prod48 A B) → Tm48 Γ B
 := λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left right case zero suc rec ,
     snd48 _ _ _
          (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left right case zero suc rec).

Definition left48 {Γ A B} : Tm48 Γ A → Tm48 Γ (sum48 A B)
 := λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right case zero suc rec ,
     left48 _ _ _
          (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right case zero suc rec).

Definition right48 {Γ A B} : Tm48 Γ B → Tm48 Γ (sum48 A B)
 := λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case zero suc rec ,
     right48 _ _ _
            (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case zero suc rec).

Definition case48 {Γ A B C} : Tm48 Γ (sum48 A B) → Tm48 Γ (arr48 A C) → Tm48 Γ (arr48 B C) → Tm48 Γ C
 := λ t u v Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero suc rec ,
     case48 _ _ _ _
           (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero suc rec)
           (u Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero suc rec)
           (v Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero suc rec).

Definition zero48  {Γ} : Tm48 Γ nat48
 := λ Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc rec , zero48 _.

Definition suc48 {Γ} : Tm48 Γ nat48 → Tm48 Γ nat48
 := λ t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec ,
   suc48 _ (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec).

Definition rec48 {Γ A} : Tm48 Γ nat48 → Tm48 Γ (arr48 nat48 (arr48 A A)) → Tm48 Γ A → Tm48 Γ A
 := λ t u v Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec48 ,
     rec48 _ _
         (t Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec48)
         (u Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec48)
         (v Tm48 var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 case48 zero48 suc48 rec48).

Definition v048 {Γ A} : Tm48 (snoc48 Γ A) A
 := var48 vz48.

Definition v148 {Γ A B} : Tm48 (snoc48 (snoc48 Γ A) B) A
 := var48 (vs48 vz48).

Definition v248 {Γ A B C} : Tm48 (snoc48 (snoc48 (snoc48 Γ A) B) C) A
 := var48 (vs48 (vs48 vz48)).

Definition v348 {Γ A B C D} : Tm48 (snoc48 (snoc48 (snoc48 (snoc48 Γ A) B) C) D) A
 := var48 (vs48 (vs48 (vs48 vz48))).

Definition tbool48 : Ty48
 := sum48 top48 top48.

Definition ttrue48 {Γ} : Tm48 Γ tbool48
 := left48 tt48.

Definition tfalse48 {Γ} : Tm48 Γ tbool48
 := right48 tt48.

Definition ifthenelse48 {Γ A} : Tm48 Γ (arr48 tbool48 (arr48 A (arr48 A A)))
 := lam48 (lam48 (lam48 (case48 v248 (lam48 v248) (lam48 v148)))).

Definition times448 {Γ A} : Tm48 Γ (arr48 (arr48 A A) (arr48 A A))
  := lam48 (lam48 (app48 v148 (app48 v148 (app48 v148 (app48 v148 v048))))).

Definition add48 {Γ} : Tm48 Γ (arr48 nat48 (arr48 nat48 nat48))
 := lam48 (rec48 v048
      (lam48 (lam48 (lam48 (suc48 (app48 v148 v048)))))
      (lam48 v048)).

Definition mul48 {Γ} : Tm48 Γ (arr48 nat48 (arr48 nat48 nat48))
 := lam48 (rec48 v048
     (lam48 (lam48 (lam48 (app48 (app48 add48 (app48 v148 v048)) v048))))
     (lam48 zero48)).

Definition fact48 {Γ} : Tm48 Γ (arr48 nat48 nat48)
 := lam48 (rec48 v048 (lam48 (lam48 (app48 (app48 mul48 (suc48 v148)) v048)))
        (suc48 zero48)).

Require Import Coq.Unicode.Utf8.

Definition Ty49 : Set
 := ∀ (Ty49           : Set)
      (nat top bot  : Ty49)
      (arr prod sum : Ty49 → Ty49 → Ty49)
    , Ty49.

Definition nat49 : Ty49 := λ _ nat49 _ _ _ _ _ , nat49.
Definition top49 : Ty49 := λ _ _ top49 _ _ _ _ , top49.
Definition bot49 : Ty49 := λ _ _ _ bot49 _ _ _ , bot49.

Definition arr49 : Ty49 → Ty49 → Ty49
 := λ A B Ty49 nat49 top49 bot49 arr49 prod sum ,
     arr49 (A Ty49 nat49 top49 bot49 arr49 prod sum) (B Ty49 nat49 top49 bot49 arr49 prod sum).

Definition prod49 : Ty49 → Ty49 → Ty49
 := λ A B Ty49 nat49 top49 bot49 arr49 prod49 sum ,
     prod49 (A Ty49 nat49 top49 bot49 arr49 prod49 sum) (B Ty49 nat49 top49 bot49 arr49 prod49 sum).

Definition sum49 : Ty49 → Ty49 → Ty49
 := λ A B Ty49 nat49 top49 bot49 arr49 prod49 sum49 ,
     sum49 (A Ty49 nat49 top49 bot49 arr49 prod49 sum49) (B Ty49 nat49 top49 bot49 arr49 prod49 sum49).

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
     (tt    : ∀ Γ       , Tm49 Γ top49)
     (pair  : ∀ Γ A B   , Tm49 Γ A → Tm49 Γ B → Tm49 Γ (prod49 A B))
     (fst   : ∀ Γ A B   , Tm49 Γ (prod49 A B) → Tm49 Γ A)
     (snd   : ∀ Γ A B   , Tm49 Γ (prod49 A B) → Tm49 Γ B)
     (left  : ∀ Γ A B   , Tm49 Γ A → Tm49 Γ (sum49 A B))
     (right : ∀ Γ A B   , Tm49 Γ B → Tm49 Γ (sum49 A B))
     (case  : ∀ Γ A B C , Tm49 Γ (sum49 A B) → Tm49 Γ (arr49 A C) → Tm49 Γ (arr49 B C) → Tm49 Γ C)
     (zero  : ∀ Γ       , Tm49 Γ nat49)
     (suc   : ∀ Γ       , Tm49 Γ nat49 → Tm49 Γ nat49)
     (rec   : ∀ Γ A     , Tm49 Γ nat49 → Tm49 Γ (arr49 nat49 (arr49 A A)) → Tm49 Γ A → Tm49 Γ A)
   , Tm49 Γ A.

Definition var49 {Γ A} : Var49 Γ A → Tm49 Γ A
 := λ x Tm49 var49 lam app tt pair fst snd left right case zero suc rec ,
     var49 _ _ x.

Definition lam49 {Γ A B} : Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B)
 := λ t Tm49 var49 lam49 app tt pair fst snd left right case zero suc rec ,
     lam49 _ _ _ (t Tm49 var49 lam49 app tt pair fst snd left right case zero suc rec).

Definition app49 {Γ A B} : Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B
 := λ t u Tm49 var49 lam49 app49 tt pair fst snd left right case zero suc rec ,
     app49 _ _ _
         (t Tm49 var49 lam49 app49 tt pair fst snd left right case zero suc rec)
         (u Tm49 var49 lam49 app49 tt pair fst snd left right case zero suc rec).

Definition tt49 {Γ} : Tm49 Γ top49
 := λ Tm49 var49 lam49 app49 tt49 pair fst snd left right case zero suc rec , tt49 _.

Definition pair49 {Γ A B} : Tm49 Γ A → Tm49 Γ B → Tm49 Γ (prod49 A B)
 := λ t u Tm49 var49 lam49 app49 tt49 pair49 fst snd left right case zero suc rec ,
     pair49 _ _ _
          (t Tm49 var49 lam49 app49 tt49 pair49 fst snd left right case zero suc rec)
          (u Tm49 var49 lam49 app49 tt49 pair49 fst snd left right case zero suc rec).

Definition fst49 {Γ A B} : Tm49 Γ (prod49 A B) → Tm49 Γ A
 := λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd left right case zero suc rec ,
     fst49 _ _ _
         (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd left right case zero suc rec).

Definition snd49 {Γ A B} : Tm49 Γ (prod49 A B) → Tm49 Γ B
 := λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left right case zero suc rec ,
     snd49 _ _ _
          (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left right case zero suc rec).

Definition left49 {Γ A B} : Tm49 Γ A → Tm49 Γ (sum49 A B)
 := λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right case zero suc rec ,
     left49 _ _ _
          (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right case zero suc rec).

Definition right49 {Γ A B} : Tm49 Γ B → Tm49 Γ (sum49 A B)
 := λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case zero suc rec ,
     right49 _ _ _
            (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case zero suc rec).

Definition case49 {Γ A B C} : Tm49 Γ (sum49 A B) → Tm49 Γ (arr49 A C) → Tm49 Γ (arr49 B C) → Tm49 Γ C
 := λ t u v Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero suc rec ,
     case49 _ _ _ _
           (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero suc rec)
           (u Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero suc rec)
           (v Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero suc rec).

Definition zero49  {Γ} : Tm49 Γ nat49
 := λ Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc rec , zero49 _.

Definition suc49 {Γ} : Tm49 Γ nat49 → Tm49 Γ nat49
 := λ t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec ,
   suc49 _ (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec).

Definition rec49 {Γ A} : Tm49 Γ nat49 → Tm49 Γ (arr49 nat49 (arr49 A A)) → Tm49 Γ A → Tm49 Γ A
 := λ t u v Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec49 ,
     rec49 _ _
         (t Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec49)
         (u Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec49)
         (v Tm49 var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 case49 zero49 suc49 rec49).

Definition v049 {Γ A} : Tm49 (snoc49 Γ A) A
 := var49 vz49.

Definition v149 {Γ A B} : Tm49 (snoc49 (snoc49 Γ A) B) A
 := var49 (vs49 vz49).

Definition v249 {Γ A B C} : Tm49 (snoc49 (snoc49 (snoc49 Γ A) B) C) A
 := var49 (vs49 (vs49 vz49)).

Definition v349 {Γ A B C D} : Tm49 (snoc49 (snoc49 (snoc49 (snoc49 Γ A) B) C) D) A
 := var49 (vs49 (vs49 (vs49 vz49))).

Definition tbool49 : Ty49
 := sum49 top49 top49.

Definition ttrue49 {Γ} : Tm49 Γ tbool49
 := left49 tt49.

Definition tfalse49 {Γ} : Tm49 Γ tbool49
 := right49 tt49.

Definition ifthenelse49 {Γ A} : Tm49 Γ (arr49 tbool49 (arr49 A (arr49 A A)))
 := lam49 (lam49 (lam49 (case49 v249 (lam49 v249) (lam49 v149)))).

Definition times449 {Γ A} : Tm49 Γ (arr49 (arr49 A A) (arr49 A A))
  := lam49 (lam49 (app49 v149 (app49 v149 (app49 v149 (app49 v149 v049))))).

Definition add49 {Γ} : Tm49 Γ (arr49 nat49 (arr49 nat49 nat49))
 := lam49 (rec49 v049
      (lam49 (lam49 (lam49 (suc49 (app49 v149 v049)))))
      (lam49 v049)).

Definition mul49 {Γ} : Tm49 Γ (arr49 nat49 (arr49 nat49 nat49))
 := lam49 (rec49 v049
     (lam49 (lam49 (lam49 (app49 (app49 add49 (app49 v149 v049)) v049))))
     (lam49 zero49)).

Definition fact49 {Γ} : Tm49 Γ (arr49 nat49 nat49)
 := lam49 (rec49 v049 (lam49 (lam49 (app49 (app49 mul49 (suc49 v149)) v049)))
        (suc49 zero49)).

Require Import Coq.Unicode.Utf8.

Definition Ty50 : Set
 := ∀ (Ty50           : Set)
      (nat top bot  : Ty50)
      (arr prod sum : Ty50 → Ty50 → Ty50)
    , Ty50.

Definition nat50 : Ty50 := λ _ nat50 _ _ _ _ _ , nat50.
Definition top50 : Ty50 := λ _ _ top50 _ _ _ _ , top50.
Definition bot50 : Ty50 := λ _ _ _ bot50 _ _ _ , bot50.

Definition arr50 : Ty50 → Ty50 → Ty50
 := λ A B Ty50 nat50 top50 bot50 arr50 prod sum ,
     arr50 (A Ty50 nat50 top50 bot50 arr50 prod sum) (B Ty50 nat50 top50 bot50 arr50 prod sum).

Definition prod50 : Ty50 → Ty50 → Ty50
 := λ A B Ty50 nat50 top50 bot50 arr50 prod50 sum ,
     prod50 (A Ty50 nat50 top50 bot50 arr50 prod50 sum) (B Ty50 nat50 top50 bot50 arr50 prod50 sum).

Definition sum50 : Ty50 → Ty50 → Ty50
 := λ A B Ty50 nat50 top50 bot50 arr50 prod50 sum50 ,
     sum50 (A Ty50 nat50 top50 bot50 arr50 prod50 sum50) (B Ty50 nat50 top50 bot50 arr50 prod50 sum50).

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
     (tt    : ∀ Γ       , Tm50 Γ top50)
     (pair  : ∀ Γ A B   , Tm50 Γ A → Tm50 Γ B → Tm50 Γ (prod50 A B))
     (fst   : ∀ Γ A B   , Tm50 Γ (prod50 A B) → Tm50 Γ A)
     (snd   : ∀ Γ A B   , Tm50 Γ (prod50 A B) → Tm50 Γ B)
     (left  : ∀ Γ A B   , Tm50 Γ A → Tm50 Γ (sum50 A B))
     (right : ∀ Γ A B   , Tm50 Γ B → Tm50 Γ (sum50 A B))
     (case  : ∀ Γ A B C , Tm50 Γ (sum50 A B) → Tm50 Γ (arr50 A C) → Tm50 Γ (arr50 B C) → Tm50 Γ C)
     (zero  : ∀ Γ       , Tm50 Γ nat50)
     (suc   : ∀ Γ       , Tm50 Γ nat50 → Tm50 Γ nat50)
     (rec   : ∀ Γ A     , Tm50 Γ nat50 → Tm50 Γ (arr50 nat50 (arr50 A A)) → Tm50 Γ A → Tm50 Γ A)
   , Tm50 Γ A.

Definition var50 {Γ A} : Var50 Γ A → Tm50 Γ A
 := λ x Tm50 var50 lam app tt pair fst snd left right case zero suc rec ,
     var50 _ _ x.

Definition lam50 {Γ A B} : Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B)
 := λ t Tm50 var50 lam50 app tt pair fst snd left right case zero suc rec ,
     lam50 _ _ _ (t Tm50 var50 lam50 app tt pair fst snd left right case zero suc rec).

Definition app50 {Γ A B} : Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B
 := λ t u Tm50 var50 lam50 app50 tt pair fst snd left right case zero suc rec ,
     app50 _ _ _
         (t Tm50 var50 lam50 app50 tt pair fst snd left right case zero suc rec)
         (u Tm50 var50 lam50 app50 tt pair fst snd left right case zero suc rec).

Definition tt50 {Γ} : Tm50 Γ top50
 := λ Tm50 var50 lam50 app50 tt50 pair fst snd left right case zero suc rec , tt50 _.

Definition pair50 {Γ A B} : Tm50 Γ A → Tm50 Γ B → Tm50 Γ (prod50 A B)
 := λ t u Tm50 var50 lam50 app50 tt50 pair50 fst snd left right case zero suc rec ,
     pair50 _ _ _
          (t Tm50 var50 lam50 app50 tt50 pair50 fst snd left right case zero suc rec)
          (u Tm50 var50 lam50 app50 tt50 pair50 fst snd left right case zero suc rec).

Definition fst50 {Γ A B} : Tm50 Γ (prod50 A B) → Tm50 Γ A
 := λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd left right case zero suc rec ,
     fst50 _ _ _
         (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd left right case zero suc rec).

Definition snd50 {Γ A B} : Tm50 Γ (prod50 A B) → Tm50 Γ B
 := λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left right case zero suc rec ,
     snd50 _ _ _
          (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left right case zero suc rec).

Definition left50 {Γ A B} : Tm50 Γ A → Tm50 Γ (sum50 A B)
 := λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right case zero suc rec ,
     left50 _ _ _
          (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right case zero suc rec).

Definition right50 {Γ A B} : Tm50 Γ B → Tm50 Γ (sum50 A B)
 := λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case zero suc rec ,
     right50 _ _ _
            (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case zero suc rec).

Definition case50 {Γ A B C} : Tm50 Γ (sum50 A B) → Tm50 Γ (arr50 A C) → Tm50 Γ (arr50 B C) → Tm50 Γ C
 := λ t u v Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero suc rec ,
     case50 _ _ _ _
           (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero suc rec)
           (u Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero suc rec)
           (v Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero suc rec).

Definition zero50  {Γ} : Tm50 Γ nat50
 := λ Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc rec , zero50 _.

Definition suc50 {Γ} : Tm50 Γ nat50 → Tm50 Γ nat50
 := λ t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec ,
   suc50 _ (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec).

Definition rec50 {Γ A} : Tm50 Γ nat50 → Tm50 Γ (arr50 nat50 (arr50 A A)) → Tm50 Γ A → Tm50 Γ A
 := λ t u v Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec50 ,
     rec50 _ _
         (t Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec50)
         (u Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec50)
         (v Tm50 var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 case50 zero50 suc50 rec50).

Definition v050 {Γ A} : Tm50 (snoc50 Γ A) A
 := var50 vz50.

Definition v150 {Γ A B} : Tm50 (snoc50 (snoc50 Γ A) B) A
 := var50 (vs50 vz50).

Definition v250 {Γ A B C} : Tm50 (snoc50 (snoc50 (snoc50 Γ A) B) C) A
 := var50 (vs50 (vs50 vz50)).

Definition v350 {Γ A B C D} : Tm50 (snoc50 (snoc50 (snoc50 (snoc50 Γ A) B) C) D) A
 := var50 (vs50 (vs50 (vs50 vz50))).

Definition tbool50 : Ty50
 := sum50 top50 top50.

Definition ttrue50 {Γ} : Tm50 Γ tbool50
 := left50 tt50.

Definition tfalse50 {Γ} : Tm50 Γ tbool50
 := right50 tt50.

Definition ifthenelse50 {Γ A} : Tm50 Γ (arr50 tbool50 (arr50 A (arr50 A A)))
 := lam50 (lam50 (lam50 (case50 v250 (lam50 v250) (lam50 v150)))).

Definition times450 {Γ A} : Tm50 Γ (arr50 (arr50 A A) (arr50 A A))
  := lam50 (lam50 (app50 v150 (app50 v150 (app50 v150 (app50 v150 v050))))).

Definition add50 {Γ} : Tm50 Γ (arr50 nat50 (arr50 nat50 nat50))
 := lam50 (rec50 v050
      (lam50 (lam50 (lam50 (suc50 (app50 v150 v050)))))
      (lam50 v050)).

Definition mul50 {Γ} : Tm50 Γ (arr50 nat50 (arr50 nat50 nat50))
 := lam50 (rec50 v050
     (lam50 (lam50 (lam50 (app50 (app50 add50 (app50 v150 v050)) v050))))
     (lam50 zero50)).

Definition fact50 {Γ} : Tm50 Γ (arr50 nat50 nat50)
 := lam50 (rec50 v050 (lam50 (lam50 (app50 (app50 mul50 (suc50 v150)) v050)))
        (suc50 zero50)).

Require Import Coq.Unicode.Utf8.

Definition Ty51 : Set
 := ∀ (Ty51           : Set)
      (nat top bot  : Ty51)
      (arr prod sum : Ty51 → Ty51 → Ty51)
    , Ty51.

Definition nat51 : Ty51 := λ _ nat51 _ _ _ _ _ , nat51.
Definition top51 : Ty51 := λ _ _ top51 _ _ _ _ , top51.
Definition bot51 : Ty51 := λ _ _ _ bot51 _ _ _ , bot51.

Definition arr51 : Ty51 → Ty51 → Ty51
 := λ A B Ty51 nat51 top51 bot51 arr51 prod sum ,
     arr51 (A Ty51 nat51 top51 bot51 arr51 prod sum) (B Ty51 nat51 top51 bot51 arr51 prod sum).

Definition prod51 : Ty51 → Ty51 → Ty51
 := λ A B Ty51 nat51 top51 bot51 arr51 prod51 sum ,
     prod51 (A Ty51 nat51 top51 bot51 arr51 prod51 sum) (B Ty51 nat51 top51 bot51 arr51 prod51 sum).

Definition sum51 : Ty51 → Ty51 → Ty51
 := λ A B Ty51 nat51 top51 bot51 arr51 prod51 sum51 ,
     sum51 (A Ty51 nat51 top51 bot51 arr51 prod51 sum51) (B Ty51 nat51 top51 bot51 arr51 prod51 sum51).

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
     (tt    : ∀ Γ       , Tm51 Γ top51)
     (pair  : ∀ Γ A B   , Tm51 Γ A → Tm51 Γ B → Tm51 Γ (prod51 A B))
     (fst   : ∀ Γ A B   , Tm51 Γ (prod51 A B) → Tm51 Γ A)
     (snd   : ∀ Γ A B   , Tm51 Γ (prod51 A B) → Tm51 Γ B)
     (left  : ∀ Γ A B   , Tm51 Γ A → Tm51 Γ (sum51 A B))
     (right : ∀ Γ A B   , Tm51 Γ B → Tm51 Γ (sum51 A B))
     (case  : ∀ Γ A B C , Tm51 Γ (sum51 A B) → Tm51 Γ (arr51 A C) → Tm51 Γ (arr51 B C) → Tm51 Γ C)
     (zero  : ∀ Γ       , Tm51 Γ nat51)
     (suc   : ∀ Γ       , Tm51 Γ nat51 → Tm51 Γ nat51)
     (rec   : ∀ Γ A     , Tm51 Γ nat51 → Tm51 Γ (arr51 nat51 (arr51 A A)) → Tm51 Γ A → Tm51 Γ A)
   , Tm51 Γ A.

Definition var51 {Γ A} : Var51 Γ A → Tm51 Γ A
 := λ x Tm51 var51 lam app tt pair fst snd left right case zero suc rec ,
     var51 _ _ x.

Definition lam51 {Γ A B} : Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B)
 := λ t Tm51 var51 lam51 app tt pair fst snd left right case zero suc rec ,
     lam51 _ _ _ (t Tm51 var51 lam51 app tt pair fst snd left right case zero suc rec).

Definition app51 {Γ A B} : Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B
 := λ t u Tm51 var51 lam51 app51 tt pair fst snd left right case zero suc rec ,
     app51 _ _ _
         (t Tm51 var51 lam51 app51 tt pair fst snd left right case zero suc rec)
         (u Tm51 var51 lam51 app51 tt pair fst snd left right case zero suc rec).

Definition tt51 {Γ} : Tm51 Γ top51
 := λ Tm51 var51 lam51 app51 tt51 pair fst snd left right case zero suc rec , tt51 _.

Definition pair51 {Γ A B} : Tm51 Γ A → Tm51 Γ B → Tm51 Γ (prod51 A B)
 := λ t u Tm51 var51 lam51 app51 tt51 pair51 fst snd left right case zero suc rec ,
     pair51 _ _ _
          (t Tm51 var51 lam51 app51 tt51 pair51 fst snd left right case zero suc rec)
          (u Tm51 var51 lam51 app51 tt51 pair51 fst snd left right case zero suc rec).

Definition fst51 {Γ A B} : Tm51 Γ (prod51 A B) → Tm51 Γ A
 := λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd left right case zero suc rec ,
     fst51 _ _ _
         (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd left right case zero suc rec).

Definition snd51 {Γ A B} : Tm51 Γ (prod51 A B) → Tm51 Γ B
 := λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left right case zero suc rec ,
     snd51 _ _ _
          (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left right case zero suc rec).

Definition left51 {Γ A B} : Tm51 Γ A → Tm51 Γ (sum51 A B)
 := λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right case zero suc rec ,
     left51 _ _ _
          (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right case zero suc rec).

Definition right51 {Γ A B} : Tm51 Γ B → Tm51 Γ (sum51 A B)
 := λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case zero suc rec ,
     right51 _ _ _
            (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case zero suc rec).

Definition case51 {Γ A B C} : Tm51 Γ (sum51 A B) → Tm51 Γ (arr51 A C) → Tm51 Γ (arr51 B C) → Tm51 Γ C
 := λ t u v Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero suc rec ,
     case51 _ _ _ _
           (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero suc rec)
           (u Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero suc rec)
           (v Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero suc rec).

Definition zero51  {Γ} : Tm51 Γ nat51
 := λ Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc rec , zero51 _.

Definition suc51 {Γ} : Tm51 Γ nat51 → Tm51 Γ nat51
 := λ t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec ,
   suc51 _ (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec).

Definition rec51 {Γ A} : Tm51 Γ nat51 → Tm51 Γ (arr51 nat51 (arr51 A A)) → Tm51 Γ A → Tm51 Γ A
 := λ t u v Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec51 ,
     rec51 _ _
         (t Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec51)
         (u Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec51)
         (v Tm51 var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 case51 zero51 suc51 rec51).

Definition v051 {Γ A} : Tm51 (snoc51 Γ A) A
 := var51 vz51.

Definition v151 {Γ A B} : Tm51 (snoc51 (snoc51 Γ A) B) A
 := var51 (vs51 vz51).

Definition v251 {Γ A B C} : Tm51 (snoc51 (snoc51 (snoc51 Γ A) B) C) A
 := var51 (vs51 (vs51 vz51)).

Definition v351 {Γ A B C D} : Tm51 (snoc51 (snoc51 (snoc51 (snoc51 Γ A) B) C) D) A
 := var51 (vs51 (vs51 (vs51 vz51))).

Definition tbool51 : Ty51
 := sum51 top51 top51.

Definition ttrue51 {Γ} : Tm51 Γ tbool51
 := left51 tt51.

Definition tfalse51 {Γ} : Tm51 Γ tbool51
 := right51 tt51.

Definition ifthenelse51 {Γ A} : Tm51 Γ (arr51 tbool51 (arr51 A (arr51 A A)))
 := lam51 (lam51 (lam51 (case51 v251 (lam51 v251) (lam51 v151)))).

Definition times451 {Γ A} : Tm51 Γ (arr51 (arr51 A A) (arr51 A A))
  := lam51 (lam51 (app51 v151 (app51 v151 (app51 v151 (app51 v151 v051))))).

Definition add51 {Γ} : Tm51 Γ (arr51 nat51 (arr51 nat51 nat51))
 := lam51 (rec51 v051
      (lam51 (lam51 (lam51 (suc51 (app51 v151 v051)))))
      (lam51 v051)).

Definition mul51 {Γ} : Tm51 Γ (arr51 nat51 (arr51 nat51 nat51))
 := lam51 (rec51 v051
     (lam51 (lam51 (lam51 (app51 (app51 add51 (app51 v151 v051)) v051))))
     (lam51 zero51)).

Definition fact51 {Γ} : Tm51 Γ (arr51 nat51 nat51)
 := lam51 (rec51 v051 (lam51 (lam51 (app51 (app51 mul51 (suc51 v151)) v051)))
        (suc51 zero51)).

Require Import Coq.Unicode.Utf8.

Definition Ty52 : Set
 := ∀ (Ty52           : Set)
      (nat top bot  : Ty52)
      (arr prod sum : Ty52 → Ty52 → Ty52)
    , Ty52.

Definition nat52 : Ty52 := λ _ nat52 _ _ _ _ _ , nat52.
Definition top52 : Ty52 := λ _ _ top52 _ _ _ _ , top52.
Definition bot52 : Ty52 := λ _ _ _ bot52 _ _ _ , bot52.

Definition arr52 : Ty52 → Ty52 → Ty52
 := λ A B Ty52 nat52 top52 bot52 arr52 prod sum ,
     arr52 (A Ty52 nat52 top52 bot52 arr52 prod sum) (B Ty52 nat52 top52 bot52 arr52 prod sum).

Definition prod52 : Ty52 → Ty52 → Ty52
 := λ A B Ty52 nat52 top52 bot52 arr52 prod52 sum ,
     prod52 (A Ty52 nat52 top52 bot52 arr52 prod52 sum) (B Ty52 nat52 top52 bot52 arr52 prod52 sum).

Definition sum52 : Ty52 → Ty52 → Ty52
 := λ A B Ty52 nat52 top52 bot52 arr52 prod52 sum52 ,
     sum52 (A Ty52 nat52 top52 bot52 arr52 prod52 sum52) (B Ty52 nat52 top52 bot52 arr52 prod52 sum52).

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
     (tt    : ∀ Γ       , Tm52 Γ top52)
     (pair  : ∀ Γ A B   , Tm52 Γ A → Tm52 Γ B → Tm52 Γ (prod52 A B))
     (fst   : ∀ Γ A B   , Tm52 Γ (prod52 A B) → Tm52 Γ A)
     (snd   : ∀ Γ A B   , Tm52 Γ (prod52 A B) → Tm52 Γ B)
     (left  : ∀ Γ A B   , Tm52 Γ A → Tm52 Γ (sum52 A B))
     (right : ∀ Γ A B   , Tm52 Γ B → Tm52 Γ (sum52 A B))
     (case  : ∀ Γ A B C , Tm52 Γ (sum52 A B) → Tm52 Γ (arr52 A C) → Tm52 Γ (arr52 B C) → Tm52 Γ C)
     (zero  : ∀ Γ       , Tm52 Γ nat52)
     (suc   : ∀ Γ       , Tm52 Γ nat52 → Tm52 Γ nat52)
     (rec   : ∀ Γ A     , Tm52 Γ nat52 → Tm52 Γ (arr52 nat52 (arr52 A A)) → Tm52 Γ A → Tm52 Γ A)
   , Tm52 Γ A.

Definition var52 {Γ A} : Var52 Γ A → Tm52 Γ A
 := λ x Tm52 var52 lam app tt pair fst snd left right case zero suc rec ,
     var52 _ _ x.

Definition lam52 {Γ A B} : Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B)
 := λ t Tm52 var52 lam52 app tt pair fst snd left right case zero suc rec ,
     lam52 _ _ _ (t Tm52 var52 lam52 app tt pair fst snd left right case zero suc rec).

Definition app52 {Γ A B} : Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B
 := λ t u Tm52 var52 lam52 app52 tt pair fst snd left right case zero suc rec ,
     app52 _ _ _
         (t Tm52 var52 lam52 app52 tt pair fst snd left right case zero suc rec)
         (u Tm52 var52 lam52 app52 tt pair fst snd left right case zero suc rec).

Definition tt52 {Γ} : Tm52 Γ top52
 := λ Tm52 var52 lam52 app52 tt52 pair fst snd left right case zero suc rec , tt52 _.

Definition pair52 {Γ A B} : Tm52 Γ A → Tm52 Γ B → Tm52 Γ (prod52 A B)
 := λ t u Tm52 var52 lam52 app52 tt52 pair52 fst snd left right case zero suc rec ,
     pair52 _ _ _
          (t Tm52 var52 lam52 app52 tt52 pair52 fst snd left right case zero suc rec)
          (u Tm52 var52 lam52 app52 tt52 pair52 fst snd left right case zero suc rec).

Definition fst52 {Γ A B} : Tm52 Γ (prod52 A B) → Tm52 Γ A
 := λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd left right case zero suc rec ,
     fst52 _ _ _
         (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd left right case zero suc rec).

Definition snd52 {Γ A B} : Tm52 Γ (prod52 A B) → Tm52 Γ B
 := λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left right case zero suc rec ,
     snd52 _ _ _
          (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left right case zero suc rec).

Definition left52 {Γ A B} : Tm52 Γ A → Tm52 Γ (sum52 A B)
 := λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right case zero suc rec ,
     left52 _ _ _
          (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right case zero suc rec).

Definition right52 {Γ A B} : Tm52 Γ B → Tm52 Γ (sum52 A B)
 := λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case zero suc rec ,
     right52 _ _ _
            (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case zero suc rec).

Definition case52 {Γ A B C} : Tm52 Γ (sum52 A B) → Tm52 Γ (arr52 A C) → Tm52 Γ (arr52 B C) → Tm52 Γ C
 := λ t u v Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero suc rec ,
     case52 _ _ _ _
           (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero suc rec)
           (u Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero suc rec)
           (v Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero suc rec).

Definition zero52  {Γ} : Tm52 Γ nat52
 := λ Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc rec , zero52 _.

Definition suc52 {Γ} : Tm52 Γ nat52 → Tm52 Γ nat52
 := λ t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec ,
   suc52 _ (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec).

Definition rec52 {Γ A} : Tm52 Γ nat52 → Tm52 Γ (arr52 nat52 (arr52 A A)) → Tm52 Γ A → Tm52 Γ A
 := λ t u v Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec52 ,
     rec52 _ _
         (t Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec52)
         (u Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec52)
         (v Tm52 var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 case52 zero52 suc52 rec52).

Definition v052 {Γ A} : Tm52 (snoc52 Γ A) A
 := var52 vz52.

Definition v152 {Γ A B} : Tm52 (snoc52 (snoc52 Γ A) B) A
 := var52 (vs52 vz52).

Definition v252 {Γ A B C} : Tm52 (snoc52 (snoc52 (snoc52 Γ A) B) C) A
 := var52 (vs52 (vs52 vz52)).

Definition v352 {Γ A B C D} : Tm52 (snoc52 (snoc52 (snoc52 (snoc52 Γ A) B) C) D) A
 := var52 (vs52 (vs52 (vs52 vz52))).

Definition tbool52 : Ty52
 := sum52 top52 top52.

Definition ttrue52 {Γ} : Tm52 Γ tbool52
 := left52 tt52.

Definition tfalse52 {Γ} : Tm52 Γ tbool52
 := right52 tt52.

Definition ifthenelse52 {Γ A} : Tm52 Γ (arr52 tbool52 (arr52 A (arr52 A A)))
 := lam52 (lam52 (lam52 (case52 v252 (lam52 v252) (lam52 v152)))).

Definition times452 {Γ A} : Tm52 Γ (arr52 (arr52 A A) (arr52 A A))
  := lam52 (lam52 (app52 v152 (app52 v152 (app52 v152 (app52 v152 v052))))).

Definition add52 {Γ} : Tm52 Γ (arr52 nat52 (arr52 nat52 nat52))
 := lam52 (rec52 v052
      (lam52 (lam52 (lam52 (suc52 (app52 v152 v052)))))
      (lam52 v052)).

Definition mul52 {Γ} : Tm52 Γ (arr52 nat52 (arr52 nat52 nat52))
 := lam52 (rec52 v052
     (lam52 (lam52 (lam52 (app52 (app52 add52 (app52 v152 v052)) v052))))
     (lam52 zero52)).

Definition fact52 {Γ} : Tm52 Γ (arr52 nat52 nat52)
 := lam52 (rec52 v052 (lam52 (lam52 (app52 (app52 mul52 (suc52 v152)) v052)))
        (suc52 zero52)).

Require Import Coq.Unicode.Utf8.

Definition Ty53 : Set
 := ∀ (Ty53           : Set)
      (nat top bot  : Ty53)
      (arr prod sum : Ty53 → Ty53 → Ty53)
    , Ty53.

Definition nat53 : Ty53 := λ _ nat53 _ _ _ _ _ , nat53.
Definition top53 : Ty53 := λ _ _ top53 _ _ _ _ , top53.
Definition bot53 : Ty53 := λ _ _ _ bot53 _ _ _ , bot53.

Definition arr53 : Ty53 → Ty53 → Ty53
 := λ A B Ty53 nat53 top53 bot53 arr53 prod sum ,
     arr53 (A Ty53 nat53 top53 bot53 arr53 prod sum) (B Ty53 nat53 top53 bot53 arr53 prod sum).

Definition prod53 : Ty53 → Ty53 → Ty53
 := λ A B Ty53 nat53 top53 bot53 arr53 prod53 sum ,
     prod53 (A Ty53 nat53 top53 bot53 arr53 prod53 sum) (B Ty53 nat53 top53 bot53 arr53 prod53 sum).

Definition sum53 : Ty53 → Ty53 → Ty53
 := λ A B Ty53 nat53 top53 bot53 arr53 prod53 sum53 ,
     sum53 (A Ty53 nat53 top53 bot53 arr53 prod53 sum53) (B Ty53 nat53 top53 bot53 arr53 prod53 sum53).

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
     (tt    : ∀ Γ       , Tm53 Γ top53)
     (pair  : ∀ Γ A B   , Tm53 Γ A → Tm53 Γ B → Tm53 Γ (prod53 A B))
     (fst   : ∀ Γ A B   , Tm53 Γ (prod53 A B) → Tm53 Γ A)
     (snd   : ∀ Γ A B   , Tm53 Γ (prod53 A B) → Tm53 Γ B)
     (left  : ∀ Γ A B   , Tm53 Γ A → Tm53 Γ (sum53 A B))
     (right : ∀ Γ A B   , Tm53 Γ B → Tm53 Γ (sum53 A B))
     (case  : ∀ Γ A B C , Tm53 Γ (sum53 A B) → Tm53 Γ (arr53 A C) → Tm53 Γ (arr53 B C) → Tm53 Γ C)
     (zero  : ∀ Γ       , Tm53 Γ nat53)
     (suc   : ∀ Γ       , Tm53 Γ nat53 → Tm53 Γ nat53)
     (rec   : ∀ Γ A     , Tm53 Γ nat53 → Tm53 Γ (arr53 nat53 (arr53 A A)) → Tm53 Γ A → Tm53 Γ A)
   , Tm53 Γ A.

Definition var53 {Γ A} : Var53 Γ A → Tm53 Γ A
 := λ x Tm53 var53 lam app tt pair fst snd left right case zero suc rec ,
     var53 _ _ x.

Definition lam53 {Γ A B} : Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B)
 := λ t Tm53 var53 lam53 app tt pair fst snd left right case zero suc rec ,
     lam53 _ _ _ (t Tm53 var53 lam53 app tt pair fst snd left right case zero suc rec).

Definition app53 {Γ A B} : Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B
 := λ t u Tm53 var53 lam53 app53 tt pair fst snd left right case zero suc rec ,
     app53 _ _ _
         (t Tm53 var53 lam53 app53 tt pair fst snd left right case zero suc rec)
         (u Tm53 var53 lam53 app53 tt pair fst snd left right case zero suc rec).

Definition tt53 {Γ} : Tm53 Γ top53
 := λ Tm53 var53 lam53 app53 tt53 pair fst snd left right case zero suc rec , tt53 _.

Definition pair53 {Γ A B} : Tm53 Γ A → Tm53 Γ B → Tm53 Γ (prod53 A B)
 := λ t u Tm53 var53 lam53 app53 tt53 pair53 fst snd left right case zero suc rec ,
     pair53 _ _ _
          (t Tm53 var53 lam53 app53 tt53 pair53 fst snd left right case zero suc rec)
          (u Tm53 var53 lam53 app53 tt53 pair53 fst snd left right case zero suc rec).

Definition fst53 {Γ A B} : Tm53 Γ (prod53 A B) → Tm53 Γ A
 := λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd left right case zero suc rec ,
     fst53 _ _ _
         (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd left right case zero suc rec).

Definition snd53 {Γ A B} : Tm53 Γ (prod53 A B) → Tm53 Γ B
 := λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left right case zero suc rec ,
     snd53 _ _ _
          (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left right case zero suc rec).

Definition left53 {Γ A B} : Tm53 Γ A → Tm53 Γ (sum53 A B)
 := λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right case zero suc rec ,
     left53 _ _ _
          (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right case zero suc rec).

Definition right53 {Γ A B} : Tm53 Γ B → Tm53 Γ (sum53 A B)
 := λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case zero suc rec ,
     right53 _ _ _
            (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case zero suc rec).

Definition case53 {Γ A B C} : Tm53 Γ (sum53 A B) → Tm53 Γ (arr53 A C) → Tm53 Γ (arr53 B C) → Tm53 Γ C
 := λ t u v Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero suc rec ,
     case53 _ _ _ _
           (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero suc rec)
           (u Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero suc rec)
           (v Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero suc rec).

Definition zero53  {Γ} : Tm53 Γ nat53
 := λ Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc rec , zero53 _.

Definition suc53 {Γ} : Tm53 Γ nat53 → Tm53 Γ nat53
 := λ t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec ,
   suc53 _ (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec).

Definition rec53 {Γ A} : Tm53 Γ nat53 → Tm53 Γ (arr53 nat53 (arr53 A A)) → Tm53 Γ A → Tm53 Γ A
 := λ t u v Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec53 ,
     rec53 _ _
         (t Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec53)
         (u Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec53)
         (v Tm53 var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 case53 zero53 suc53 rec53).

Definition v053 {Γ A} : Tm53 (snoc53 Γ A) A
 := var53 vz53.

Definition v153 {Γ A B} : Tm53 (snoc53 (snoc53 Γ A) B) A
 := var53 (vs53 vz53).

Definition v253 {Γ A B C} : Tm53 (snoc53 (snoc53 (snoc53 Γ A) B) C) A
 := var53 (vs53 (vs53 vz53)).

Definition v353 {Γ A B C D} : Tm53 (snoc53 (snoc53 (snoc53 (snoc53 Γ A) B) C) D) A
 := var53 (vs53 (vs53 (vs53 vz53))).

Definition tbool53 : Ty53
 := sum53 top53 top53.

Definition ttrue53 {Γ} : Tm53 Γ tbool53
 := left53 tt53.

Definition tfalse53 {Γ} : Tm53 Γ tbool53
 := right53 tt53.

Definition ifthenelse53 {Γ A} : Tm53 Γ (arr53 tbool53 (arr53 A (arr53 A A)))
 := lam53 (lam53 (lam53 (case53 v253 (lam53 v253) (lam53 v153)))).

Definition times453 {Γ A} : Tm53 Γ (arr53 (arr53 A A) (arr53 A A))
  := lam53 (lam53 (app53 v153 (app53 v153 (app53 v153 (app53 v153 v053))))).

Definition add53 {Γ} : Tm53 Γ (arr53 nat53 (arr53 nat53 nat53))
 := lam53 (rec53 v053
      (lam53 (lam53 (lam53 (suc53 (app53 v153 v053)))))
      (lam53 v053)).

Definition mul53 {Γ} : Tm53 Γ (arr53 nat53 (arr53 nat53 nat53))
 := lam53 (rec53 v053
     (lam53 (lam53 (lam53 (app53 (app53 add53 (app53 v153 v053)) v053))))
     (lam53 zero53)).

Definition fact53 {Γ} : Tm53 Γ (arr53 nat53 nat53)
 := lam53 (rec53 v053 (lam53 (lam53 (app53 (app53 mul53 (suc53 v153)) v053)))
        (suc53 zero53)).

Require Import Coq.Unicode.Utf8.

Definition Ty54 : Set
 := ∀ (Ty54           : Set)
      (nat top bot  : Ty54)
      (arr prod sum : Ty54 → Ty54 → Ty54)
    , Ty54.

Definition nat54 : Ty54 := λ _ nat54 _ _ _ _ _ , nat54.
Definition top54 : Ty54 := λ _ _ top54 _ _ _ _ , top54.
Definition bot54 : Ty54 := λ _ _ _ bot54 _ _ _ , bot54.

Definition arr54 : Ty54 → Ty54 → Ty54
 := λ A B Ty54 nat54 top54 bot54 arr54 prod sum ,
     arr54 (A Ty54 nat54 top54 bot54 arr54 prod sum) (B Ty54 nat54 top54 bot54 arr54 prod sum).

Definition prod54 : Ty54 → Ty54 → Ty54
 := λ A B Ty54 nat54 top54 bot54 arr54 prod54 sum ,
     prod54 (A Ty54 nat54 top54 bot54 arr54 prod54 sum) (B Ty54 nat54 top54 bot54 arr54 prod54 sum).

Definition sum54 : Ty54 → Ty54 → Ty54
 := λ A B Ty54 nat54 top54 bot54 arr54 prod54 sum54 ,
     sum54 (A Ty54 nat54 top54 bot54 arr54 prod54 sum54) (B Ty54 nat54 top54 bot54 arr54 prod54 sum54).

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
     (tt    : ∀ Γ       , Tm54 Γ top54)
     (pair  : ∀ Γ A B   , Tm54 Γ A → Tm54 Γ B → Tm54 Γ (prod54 A B))
     (fst   : ∀ Γ A B   , Tm54 Γ (prod54 A B) → Tm54 Γ A)
     (snd   : ∀ Γ A B   , Tm54 Γ (prod54 A B) → Tm54 Γ B)
     (left  : ∀ Γ A B   , Tm54 Γ A → Tm54 Γ (sum54 A B))
     (right : ∀ Γ A B   , Tm54 Γ B → Tm54 Γ (sum54 A B))
     (case  : ∀ Γ A B C , Tm54 Γ (sum54 A B) → Tm54 Γ (arr54 A C) → Tm54 Γ (arr54 B C) → Tm54 Γ C)
     (zero  : ∀ Γ       , Tm54 Γ nat54)
     (suc   : ∀ Γ       , Tm54 Γ nat54 → Tm54 Γ nat54)
     (rec   : ∀ Γ A     , Tm54 Γ nat54 → Tm54 Γ (arr54 nat54 (arr54 A A)) → Tm54 Γ A → Tm54 Γ A)
   , Tm54 Γ A.

Definition var54 {Γ A} : Var54 Γ A → Tm54 Γ A
 := λ x Tm54 var54 lam app tt pair fst snd left right case zero suc rec ,
     var54 _ _ x.

Definition lam54 {Γ A B} : Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B)
 := λ t Tm54 var54 lam54 app tt pair fst snd left right case zero suc rec ,
     lam54 _ _ _ (t Tm54 var54 lam54 app tt pair fst snd left right case zero suc rec).

Definition app54 {Γ A B} : Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B
 := λ t u Tm54 var54 lam54 app54 tt pair fst snd left right case zero suc rec ,
     app54 _ _ _
         (t Tm54 var54 lam54 app54 tt pair fst snd left right case zero suc rec)
         (u Tm54 var54 lam54 app54 tt pair fst snd left right case zero suc rec).

Definition tt54 {Γ} : Tm54 Γ top54
 := λ Tm54 var54 lam54 app54 tt54 pair fst snd left right case zero suc rec , tt54 _.

Definition pair54 {Γ A B} : Tm54 Γ A → Tm54 Γ B → Tm54 Γ (prod54 A B)
 := λ t u Tm54 var54 lam54 app54 tt54 pair54 fst snd left right case zero suc rec ,
     pair54 _ _ _
          (t Tm54 var54 lam54 app54 tt54 pair54 fst snd left right case zero suc rec)
          (u Tm54 var54 lam54 app54 tt54 pair54 fst snd left right case zero suc rec).

Definition fst54 {Γ A B} : Tm54 Γ (prod54 A B) → Tm54 Γ A
 := λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd left right case zero suc rec ,
     fst54 _ _ _
         (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd left right case zero suc rec).

Definition snd54 {Γ A B} : Tm54 Γ (prod54 A B) → Tm54 Γ B
 := λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left right case zero suc rec ,
     snd54 _ _ _
          (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left right case zero suc rec).

Definition left54 {Γ A B} : Tm54 Γ A → Tm54 Γ (sum54 A B)
 := λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right case zero suc rec ,
     left54 _ _ _
          (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right case zero suc rec).

Definition right54 {Γ A B} : Tm54 Γ B → Tm54 Γ (sum54 A B)
 := λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case zero suc rec ,
     right54 _ _ _
            (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case zero suc rec).

Definition case54 {Γ A B C} : Tm54 Γ (sum54 A B) → Tm54 Γ (arr54 A C) → Tm54 Γ (arr54 B C) → Tm54 Γ C
 := λ t u v Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero suc rec ,
     case54 _ _ _ _
           (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero suc rec)
           (u Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero suc rec)
           (v Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero suc rec).

Definition zero54  {Γ} : Tm54 Γ nat54
 := λ Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc rec , zero54 _.

Definition suc54 {Γ} : Tm54 Γ nat54 → Tm54 Γ nat54
 := λ t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec ,
   suc54 _ (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec).

Definition rec54 {Γ A} : Tm54 Γ nat54 → Tm54 Γ (arr54 nat54 (arr54 A A)) → Tm54 Γ A → Tm54 Γ A
 := λ t u v Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec54 ,
     rec54 _ _
         (t Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec54)
         (u Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec54)
         (v Tm54 var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 case54 zero54 suc54 rec54).

Definition v054 {Γ A} : Tm54 (snoc54 Γ A) A
 := var54 vz54.

Definition v154 {Γ A B} : Tm54 (snoc54 (snoc54 Γ A) B) A
 := var54 (vs54 vz54).

Definition v254 {Γ A B C} : Tm54 (snoc54 (snoc54 (snoc54 Γ A) B) C) A
 := var54 (vs54 (vs54 vz54)).

Definition v354 {Γ A B C D} : Tm54 (snoc54 (snoc54 (snoc54 (snoc54 Γ A) B) C) D) A
 := var54 (vs54 (vs54 (vs54 vz54))).

Definition tbool54 : Ty54
 := sum54 top54 top54.

Definition ttrue54 {Γ} : Tm54 Γ tbool54
 := left54 tt54.

Definition tfalse54 {Γ} : Tm54 Γ tbool54
 := right54 tt54.

Definition ifthenelse54 {Γ A} : Tm54 Γ (arr54 tbool54 (arr54 A (arr54 A A)))
 := lam54 (lam54 (lam54 (case54 v254 (lam54 v254) (lam54 v154)))).

Definition times454 {Γ A} : Tm54 Γ (arr54 (arr54 A A) (arr54 A A))
  := lam54 (lam54 (app54 v154 (app54 v154 (app54 v154 (app54 v154 v054))))).

Definition add54 {Γ} : Tm54 Γ (arr54 nat54 (arr54 nat54 nat54))
 := lam54 (rec54 v054
      (lam54 (lam54 (lam54 (suc54 (app54 v154 v054)))))
      (lam54 v054)).

Definition mul54 {Γ} : Tm54 Γ (arr54 nat54 (arr54 nat54 nat54))
 := lam54 (rec54 v054
     (lam54 (lam54 (lam54 (app54 (app54 add54 (app54 v154 v054)) v054))))
     (lam54 zero54)).

Definition fact54 {Γ} : Tm54 Γ (arr54 nat54 nat54)
 := lam54 (rec54 v054 (lam54 (lam54 (app54 (app54 mul54 (suc54 v154)) v054)))
        (suc54 zero54)).

Require Import Coq.Unicode.Utf8.

Definition Ty55 : Set
 := ∀ (Ty55           : Set)
      (nat top bot  : Ty55)
      (arr prod sum : Ty55 → Ty55 → Ty55)
    , Ty55.

Definition nat55 : Ty55 := λ _ nat55 _ _ _ _ _ , nat55.
Definition top55 : Ty55 := λ _ _ top55 _ _ _ _ , top55.
Definition bot55 : Ty55 := λ _ _ _ bot55 _ _ _ , bot55.

Definition arr55 : Ty55 → Ty55 → Ty55
 := λ A B Ty55 nat55 top55 bot55 arr55 prod sum ,
     arr55 (A Ty55 nat55 top55 bot55 arr55 prod sum) (B Ty55 nat55 top55 bot55 arr55 prod sum).

Definition prod55 : Ty55 → Ty55 → Ty55
 := λ A B Ty55 nat55 top55 bot55 arr55 prod55 sum ,
     prod55 (A Ty55 nat55 top55 bot55 arr55 prod55 sum) (B Ty55 nat55 top55 bot55 arr55 prod55 sum).

Definition sum55 : Ty55 → Ty55 → Ty55
 := λ A B Ty55 nat55 top55 bot55 arr55 prod55 sum55 ,
     sum55 (A Ty55 nat55 top55 bot55 arr55 prod55 sum55) (B Ty55 nat55 top55 bot55 arr55 prod55 sum55).

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
     (tt    : ∀ Γ       , Tm55 Γ top55)
     (pair  : ∀ Γ A B   , Tm55 Γ A → Tm55 Γ B → Tm55 Γ (prod55 A B))
     (fst   : ∀ Γ A B   , Tm55 Γ (prod55 A B) → Tm55 Γ A)
     (snd   : ∀ Γ A B   , Tm55 Γ (prod55 A B) → Tm55 Γ B)
     (left  : ∀ Γ A B   , Tm55 Γ A → Tm55 Γ (sum55 A B))
     (right : ∀ Γ A B   , Tm55 Γ B → Tm55 Γ (sum55 A B))
     (case  : ∀ Γ A B C , Tm55 Γ (sum55 A B) → Tm55 Γ (arr55 A C) → Tm55 Γ (arr55 B C) → Tm55 Γ C)
     (zero  : ∀ Γ       , Tm55 Γ nat55)
     (suc   : ∀ Γ       , Tm55 Γ nat55 → Tm55 Γ nat55)
     (rec   : ∀ Γ A     , Tm55 Γ nat55 → Tm55 Γ (arr55 nat55 (arr55 A A)) → Tm55 Γ A → Tm55 Γ A)
   , Tm55 Γ A.

Definition var55 {Γ A} : Var55 Γ A → Tm55 Γ A
 := λ x Tm55 var55 lam app tt pair fst snd left right case zero suc rec ,
     var55 _ _ x.

Definition lam55 {Γ A B} : Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B)
 := λ t Tm55 var55 lam55 app tt pair fst snd left right case zero suc rec ,
     lam55 _ _ _ (t Tm55 var55 lam55 app tt pair fst snd left right case zero suc rec).

Definition app55 {Γ A B} : Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B
 := λ t u Tm55 var55 lam55 app55 tt pair fst snd left right case zero suc rec ,
     app55 _ _ _
         (t Tm55 var55 lam55 app55 tt pair fst snd left right case zero suc rec)
         (u Tm55 var55 lam55 app55 tt pair fst snd left right case zero suc rec).

Definition tt55 {Γ} : Tm55 Γ top55
 := λ Tm55 var55 lam55 app55 tt55 pair fst snd left right case zero suc rec , tt55 _.

Definition pair55 {Γ A B} : Tm55 Γ A → Tm55 Γ B → Tm55 Γ (prod55 A B)
 := λ t u Tm55 var55 lam55 app55 tt55 pair55 fst snd left right case zero suc rec ,
     pair55 _ _ _
          (t Tm55 var55 lam55 app55 tt55 pair55 fst snd left right case zero suc rec)
          (u Tm55 var55 lam55 app55 tt55 pair55 fst snd left right case zero suc rec).

Definition fst55 {Γ A B} : Tm55 Γ (prod55 A B) → Tm55 Γ A
 := λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd left right case zero suc rec ,
     fst55 _ _ _
         (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd left right case zero suc rec).

Definition snd55 {Γ A B} : Tm55 Γ (prod55 A B) → Tm55 Γ B
 := λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left right case zero suc rec ,
     snd55 _ _ _
          (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left right case zero suc rec).

Definition left55 {Γ A B} : Tm55 Γ A → Tm55 Γ (sum55 A B)
 := λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right case zero suc rec ,
     left55 _ _ _
          (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right case zero suc rec).

Definition right55 {Γ A B} : Tm55 Γ B → Tm55 Γ (sum55 A B)
 := λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case zero suc rec ,
     right55 _ _ _
            (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case zero suc rec).

Definition case55 {Γ A B C} : Tm55 Γ (sum55 A B) → Tm55 Γ (arr55 A C) → Tm55 Γ (arr55 B C) → Tm55 Γ C
 := λ t u v Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero suc rec ,
     case55 _ _ _ _
           (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero suc rec)
           (u Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero suc rec)
           (v Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero suc rec).

Definition zero55  {Γ} : Tm55 Γ nat55
 := λ Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc rec , zero55 _.

Definition suc55 {Γ} : Tm55 Γ nat55 → Tm55 Γ nat55
 := λ t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec ,
   suc55 _ (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec).

Definition rec55 {Γ A} : Tm55 Γ nat55 → Tm55 Γ (arr55 nat55 (arr55 A A)) → Tm55 Γ A → Tm55 Γ A
 := λ t u v Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec55 ,
     rec55 _ _
         (t Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec55)
         (u Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec55)
         (v Tm55 var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 case55 zero55 suc55 rec55).

Definition v055 {Γ A} : Tm55 (snoc55 Γ A) A
 := var55 vz55.

Definition v155 {Γ A B} : Tm55 (snoc55 (snoc55 Γ A) B) A
 := var55 (vs55 vz55).

Definition v255 {Γ A B C} : Tm55 (snoc55 (snoc55 (snoc55 Γ A) B) C) A
 := var55 (vs55 (vs55 vz55)).

Definition v355 {Γ A B C D} : Tm55 (snoc55 (snoc55 (snoc55 (snoc55 Γ A) B) C) D) A
 := var55 (vs55 (vs55 (vs55 vz55))).

Definition tbool55 : Ty55
 := sum55 top55 top55.

Definition ttrue55 {Γ} : Tm55 Γ tbool55
 := left55 tt55.

Definition tfalse55 {Γ} : Tm55 Γ tbool55
 := right55 tt55.

Definition ifthenelse55 {Γ A} : Tm55 Γ (arr55 tbool55 (arr55 A (arr55 A A)))
 := lam55 (lam55 (lam55 (case55 v255 (lam55 v255) (lam55 v155)))).

Definition times455 {Γ A} : Tm55 Γ (arr55 (arr55 A A) (arr55 A A))
  := lam55 (lam55 (app55 v155 (app55 v155 (app55 v155 (app55 v155 v055))))).

Definition add55 {Γ} : Tm55 Γ (arr55 nat55 (arr55 nat55 nat55))
 := lam55 (rec55 v055
      (lam55 (lam55 (lam55 (suc55 (app55 v155 v055)))))
      (lam55 v055)).

Definition mul55 {Γ} : Tm55 Γ (arr55 nat55 (arr55 nat55 nat55))
 := lam55 (rec55 v055
     (lam55 (lam55 (lam55 (app55 (app55 add55 (app55 v155 v055)) v055))))
     (lam55 zero55)).

Definition fact55 {Γ} : Tm55 Γ (arr55 nat55 nat55)
 := lam55 (rec55 v055 (lam55 (lam55 (app55 (app55 mul55 (suc55 v155)) v055)))
        (suc55 zero55)).

Require Import Coq.Unicode.Utf8.

Definition Ty56 : Set
 := ∀ (Ty56           : Set)
      (nat top bot  : Ty56)
      (arr prod sum : Ty56 → Ty56 → Ty56)
    , Ty56.

Definition nat56 : Ty56 := λ _ nat56 _ _ _ _ _ , nat56.
Definition top56 : Ty56 := λ _ _ top56 _ _ _ _ , top56.
Definition bot56 : Ty56 := λ _ _ _ bot56 _ _ _ , bot56.

Definition arr56 : Ty56 → Ty56 → Ty56
 := λ A B Ty56 nat56 top56 bot56 arr56 prod sum ,
     arr56 (A Ty56 nat56 top56 bot56 arr56 prod sum) (B Ty56 nat56 top56 bot56 arr56 prod sum).

Definition prod56 : Ty56 → Ty56 → Ty56
 := λ A B Ty56 nat56 top56 bot56 arr56 prod56 sum ,
     prod56 (A Ty56 nat56 top56 bot56 arr56 prod56 sum) (B Ty56 nat56 top56 bot56 arr56 prod56 sum).

Definition sum56 : Ty56 → Ty56 → Ty56
 := λ A B Ty56 nat56 top56 bot56 arr56 prod56 sum56 ,
     sum56 (A Ty56 nat56 top56 bot56 arr56 prod56 sum56) (B Ty56 nat56 top56 bot56 arr56 prod56 sum56).

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
     (tt    : ∀ Γ       , Tm56 Γ top56)
     (pair  : ∀ Γ A B   , Tm56 Γ A → Tm56 Γ B → Tm56 Γ (prod56 A B))
     (fst   : ∀ Γ A B   , Tm56 Γ (prod56 A B) → Tm56 Γ A)
     (snd   : ∀ Γ A B   , Tm56 Γ (prod56 A B) → Tm56 Γ B)
     (left  : ∀ Γ A B   , Tm56 Γ A → Tm56 Γ (sum56 A B))
     (right : ∀ Γ A B   , Tm56 Γ B → Tm56 Γ (sum56 A B))
     (case  : ∀ Γ A B C , Tm56 Γ (sum56 A B) → Tm56 Γ (arr56 A C) → Tm56 Γ (arr56 B C) → Tm56 Γ C)
     (zero  : ∀ Γ       , Tm56 Γ nat56)
     (suc   : ∀ Γ       , Tm56 Γ nat56 → Tm56 Γ nat56)
     (rec   : ∀ Γ A     , Tm56 Γ nat56 → Tm56 Γ (arr56 nat56 (arr56 A A)) → Tm56 Γ A → Tm56 Γ A)
   , Tm56 Γ A.

Definition var56 {Γ A} : Var56 Γ A → Tm56 Γ A
 := λ x Tm56 var56 lam app tt pair fst snd left right case zero suc rec ,
     var56 _ _ x.

Definition lam56 {Γ A B} : Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B)
 := λ t Tm56 var56 lam56 app tt pair fst snd left right case zero suc rec ,
     lam56 _ _ _ (t Tm56 var56 lam56 app tt pair fst snd left right case zero suc rec).

Definition app56 {Γ A B} : Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B
 := λ t u Tm56 var56 lam56 app56 tt pair fst snd left right case zero suc rec ,
     app56 _ _ _
         (t Tm56 var56 lam56 app56 tt pair fst snd left right case zero suc rec)
         (u Tm56 var56 lam56 app56 tt pair fst snd left right case zero suc rec).

Definition tt56 {Γ} : Tm56 Γ top56
 := λ Tm56 var56 lam56 app56 tt56 pair fst snd left right case zero suc rec , tt56 _.

Definition pair56 {Γ A B} : Tm56 Γ A → Tm56 Γ B → Tm56 Γ (prod56 A B)
 := λ t u Tm56 var56 lam56 app56 tt56 pair56 fst snd left right case zero suc rec ,
     pair56 _ _ _
          (t Tm56 var56 lam56 app56 tt56 pair56 fst snd left right case zero suc rec)
          (u Tm56 var56 lam56 app56 tt56 pair56 fst snd left right case zero suc rec).

Definition fst56 {Γ A B} : Tm56 Γ (prod56 A B) → Tm56 Γ A
 := λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd left right case zero suc rec ,
     fst56 _ _ _
         (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd left right case zero suc rec).

Definition snd56 {Γ A B} : Tm56 Γ (prod56 A B) → Tm56 Γ B
 := λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left right case zero suc rec ,
     snd56 _ _ _
          (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left right case zero suc rec).

Definition left56 {Γ A B} : Tm56 Γ A → Tm56 Γ (sum56 A B)
 := λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right case zero suc rec ,
     left56 _ _ _
          (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right case zero suc rec).

Definition right56 {Γ A B} : Tm56 Γ B → Tm56 Γ (sum56 A B)
 := λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case zero suc rec ,
     right56 _ _ _
            (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case zero suc rec).

Definition case56 {Γ A B C} : Tm56 Γ (sum56 A B) → Tm56 Γ (arr56 A C) → Tm56 Γ (arr56 B C) → Tm56 Γ C
 := λ t u v Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero suc rec ,
     case56 _ _ _ _
           (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero suc rec)
           (u Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero suc rec)
           (v Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero suc rec).

Definition zero56  {Γ} : Tm56 Γ nat56
 := λ Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc rec , zero56 _.

Definition suc56 {Γ} : Tm56 Γ nat56 → Tm56 Γ nat56
 := λ t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec ,
   suc56 _ (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec).

Definition rec56 {Γ A} : Tm56 Γ nat56 → Tm56 Γ (arr56 nat56 (arr56 A A)) → Tm56 Γ A → Tm56 Γ A
 := λ t u v Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec56 ,
     rec56 _ _
         (t Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec56)
         (u Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec56)
         (v Tm56 var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 case56 zero56 suc56 rec56).

Definition v056 {Γ A} : Tm56 (snoc56 Γ A) A
 := var56 vz56.

Definition v156 {Γ A B} : Tm56 (snoc56 (snoc56 Γ A) B) A
 := var56 (vs56 vz56).

Definition v256 {Γ A B C} : Tm56 (snoc56 (snoc56 (snoc56 Γ A) B) C) A
 := var56 (vs56 (vs56 vz56)).

Definition v356 {Γ A B C D} : Tm56 (snoc56 (snoc56 (snoc56 (snoc56 Γ A) B) C) D) A
 := var56 (vs56 (vs56 (vs56 vz56))).

Definition tbool56 : Ty56
 := sum56 top56 top56.

Definition ttrue56 {Γ} : Tm56 Γ tbool56
 := left56 tt56.

Definition tfalse56 {Γ} : Tm56 Γ tbool56
 := right56 tt56.

Definition ifthenelse56 {Γ A} : Tm56 Γ (arr56 tbool56 (arr56 A (arr56 A A)))
 := lam56 (lam56 (lam56 (case56 v256 (lam56 v256) (lam56 v156)))).

Definition times456 {Γ A} : Tm56 Γ (arr56 (arr56 A A) (arr56 A A))
  := lam56 (lam56 (app56 v156 (app56 v156 (app56 v156 (app56 v156 v056))))).

Definition add56 {Γ} : Tm56 Γ (arr56 nat56 (arr56 nat56 nat56))
 := lam56 (rec56 v056
      (lam56 (lam56 (lam56 (suc56 (app56 v156 v056)))))
      (lam56 v056)).

Definition mul56 {Γ} : Tm56 Γ (arr56 nat56 (arr56 nat56 nat56))
 := lam56 (rec56 v056
     (lam56 (lam56 (lam56 (app56 (app56 add56 (app56 v156 v056)) v056))))
     (lam56 zero56)).

Definition fact56 {Γ} : Tm56 Γ (arr56 nat56 nat56)
 := lam56 (rec56 v056 (lam56 (lam56 (app56 (app56 mul56 (suc56 v156)) v056)))
        (suc56 zero56)).

Require Import Coq.Unicode.Utf8.

Definition Ty57 : Set
 := ∀ (Ty57           : Set)
      (nat top bot  : Ty57)
      (arr prod sum : Ty57 → Ty57 → Ty57)
    , Ty57.

Definition nat57 : Ty57 := λ _ nat57 _ _ _ _ _ , nat57.
Definition top57 : Ty57 := λ _ _ top57 _ _ _ _ , top57.
Definition bot57 : Ty57 := λ _ _ _ bot57 _ _ _ , bot57.

Definition arr57 : Ty57 → Ty57 → Ty57
 := λ A B Ty57 nat57 top57 bot57 arr57 prod sum ,
     arr57 (A Ty57 nat57 top57 bot57 arr57 prod sum) (B Ty57 nat57 top57 bot57 arr57 prod sum).

Definition prod57 : Ty57 → Ty57 → Ty57
 := λ A B Ty57 nat57 top57 bot57 arr57 prod57 sum ,
     prod57 (A Ty57 nat57 top57 bot57 arr57 prod57 sum) (B Ty57 nat57 top57 bot57 arr57 prod57 sum).

Definition sum57 : Ty57 → Ty57 → Ty57
 := λ A B Ty57 nat57 top57 bot57 arr57 prod57 sum57 ,
     sum57 (A Ty57 nat57 top57 bot57 arr57 prod57 sum57) (B Ty57 nat57 top57 bot57 arr57 prod57 sum57).

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
     (tt    : ∀ Γ       , Tm57 Γ top57)
     (pair  : ∀ Γ A B   , Tm57 Γ A → Tm57 Γ B → Tm57 Γ (prod57 A B))
     (fst   : ∀ Γ A B   , Tm57 Γ (prod57 A B) → Tm57 Γ A)
     (snd   : ∀ Γ A B   , Tm57 Γ (prod57 A B) → Tm57 Γ B)
     (left  : ∀ Γ A B   , Tm57 Γ A → Tm57 Γ (sum57 A B))
     (right : ∀ Γ A B   , Tm57 Γ B → Tm57 Γ (sum57 A B))
     (case  : ∀ Γ A B C , Tm57 Γ (sum57 A B) → Tm57 Γ (arr57 A C) → Tm57 Γ (arr57 B C) → Tm57 Γ C)
     (zero  : ∀ Γ       , Tm57 Γ nat57)
     (suc   : ∀ Γ       , Tm57 Γ nat57 → Tm57 Γ nat57)
     (rec   : ∀ Γ A     , Tm57 Γ nat57 → Tm57 Γ (arr57 nat57 (arr57 A A)) → Tm57 Γ A → Tm57 Γ A)
   , Tm57 Γ A.

Definition var57 {Γ A} : Var57 Γ A → Tm57 Γ A
 := λ x Tm57 var57 lam app tt pair fst snd left right case zero suc rec ,
     var57 _ _ x.

Definition lam57 {Γ A B} : Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B)
 := λ t Tm57 var57 lam57 app tt pair fst snd left right case zero suc rec ,
     lam57 _ _ _ (t Tm57 var57 lam57 app tt pair fst snd left right case zero suc rec).

Definition app57 {Γ A B} : Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B
 := λ t u Tm57 var57 lam57 app57 tt pair fst snd left right case zero suc rec ,
     app57 _ _ _
         (t Tm57 var57 lam57 app57 tt pair fst snd left right case zero suc rec)
         (u Tm57 var57 lam57 app57 tt pair fst snd left right case zero suc rec).

Definition tt57 {Γ} : Tm57 Γ top57
 := λ Tm57 var57 lam57 app57 tt57 pair fst snd left right case zero suc rec , tt57 _.

Definition pair57 {Γ A B} : Tm57 Γ A → Tm57 Γ B → Tm57 Γ (prod57 A B)
 := λ t u Tm57 var57 lam57 app57 tt57 pair57 fst snd left right case zero suc rec ,
     pair57 _ _ _
          (t Tm57 var57 lam57 app57 tt57 pair57 fst snd left right case zero suc rec)
          (u Tm57 var57 lam57 app57 tt57 pair57 fst snd left right case zero suc rec).

Definition fst57 {Γ A B} : Tm57 Γ (prod57 A B) → Tm57 Γ A
 := λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd left right case zero suc rec ,
     fst57 _ _ _
         (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd left right case zero suc rec).

Definition snd57 {Γ A B} : Tm57 Γ (prod57 A B) → Tm57 Γ B
 := λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left right case zero suc rec ,
     snd57 _ _ _
          (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left right case zero suc rec).

Definition left57 {Γ A B} : Tm57 Γ A → Tm57 Γ (sum57 A B)
 := λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right case zero suc rec ,
     left57 _ _ _
          (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right case zero suc rec).

Definition right57 {Γ A B} : Tm57 Γ B → Tm57 Γ (sum57 A B)
 := λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case zero suc rec ,
     right57 _ _ _
            (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case zero suc rec).

Definition case57 {Γ A B C} : Tm57 Γ (sum57 A B) → Tm57 Γ (arr57 A C) → Tm57 Γ (arr57 B C) → Tm57 Γ C
 := λ t u v Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero suc rec ,
     case57 _ _ _ _
           (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero suc rec)
           (u Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero suc rec)
           (v Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero suc rec).

Definition zero57  {Γ} : Tm57 Γ nat57
 := λ Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc rec , zero57 _.

Definition suc57 {Γ} : Tm57 Γ nat57 → Tm57 Γ nat57
 := λ t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec ,
   suc57 _ (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec).

Definition rec57 {Γ A} : Tm57 Γ nat57 → Tm57 Γ (arr57 nat57 (arr57 A A)) → Tm57 Γ A → Tm57 Γ A
 := λ t u v Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec57 ,
     rec57 _ _
         (t Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec57)
         (u Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec57)
         (v Tm57 var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 case57 zero57 suc57 rec57).

Definition v057 {Γ A} : Tm57 (snoc57 Γ A) A
 := var57 vz57.

Definition v157 {Γ A B} : Tm57 (snoc57 (snoc57 Γ A) B) A
 := var57 (vs57 vz57).

Definition v257 {Γ A B C} : Tm57 (snoc57 (snoc57 (snoc57 Γ A) B) C) A
 := var57 (vs57 (vs57 vz57)).

Definition v357 {Γ A B C D} : Tm57 (snoc57 (snoc57 (snoc57 (snoc57 Γ A) B) C) D) A
 := var57 (vs57 (vs57 (vs57 vz57))).

Definition tbool57 : Ty57
 := sum57 top57 top57.

Definition ttrue57 {Γ} : Tm57 Γ tbool57
 := left57 tt57.

Definition tfalse57 {Γ} : Tm57 Γ tbool57
 := right57 tt57.

Definition ifthenelse57 {Γ A} : Tm57 Γ (arr57 tbool57 (arr57 A (arr57 A A)))
 := lam57 (lam57 (lam57 (case57 v257 (lam57 v257) (lam57 v157)))).

Definition times457 {Γ A} : Tm57 Γ (arr57 (arr57 A A) (arr57 A A))
  := lam57 (lam57 (app57 v157 (app57 v157 (app57 v157 (app57 v157 v057))))).

Definition add57 {Γ} : Tm57 Γ (arr57 nat57 (arr57 nat57 nat57))
 := lam57 (rec57 v057
      (lam57 (lam57 (lam57 (suc57 (app57 v157 v057)))))
      (lam57 v057)).

Definition mul57 {Γ} : Tm57 Γ (arr57 nat57 (arr57 nat57 nat57))
 := lam57 (rec57 v057
     (lam57 (lam57 (lam57 (app57 (app57 add57 (app57 v157 v057)) v057))))
     (lam57 zero57)).

Definition fact57 {Γ} : Tm57 Γ (arr57 nat57 nat57)
 := lam57 (rec57 v057 (lam57 (lam57 (app57 (app57 mul57 (suc57 v157)) v057)))
        (suc57 zero57)).

Require Import Coq.Unicode.Utf8.

Definition Ty58 : Set
 := ∀ (Ty58           : Set)
      (nat top bot  : Ty58)
      (arr prod sum : Ty58 → Ty58 → Ty58)
    , Ty58.

Definition nat58 : Ty58 := λ _ nat58 _ _ _ _ _ , nat58.
Definition top58 : Ty58 := λ _ _ top58 _ _ _ _ , top58.
Definition bot58 : Ty58 := λ _ _ _ bot58 _ _ _ , bot58.

Definition arr58 : Ty58 → Ty58 → Ty58
 := λ A B Ty58 nat58 top58 bot58 arr58 prod sum ,
     arr58 (A Ty58 nat58 top58 bot58 arr58 prod sum) (B Ty58 nat58 top58 bot58 arr58 prod sum).

Definition prod58 : Ty58 → Ty58 → Ty58
 := λ A B Ty58 nat58 top58 bot58 arr58 prod58 sum ,
     prod58 (A Ty58 nat58 top58 bot58 arr58 prod58 sum) (B Ty58 nat58 top58 bot58 arr58 prod58 sum).

Definition sum58 : Ty58 → Ty58 → Ty58
 := λ A B Ty58 nat58 top58 bot58 arr58 prod58 sum58 ,
     sum58 (A Ty58 nat58 top58 bot58 arr58 prod58 sum58) (B Ty58 nat58 top58 bot58 arr58 prod58 sum58).

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
     (tt    : ∀ Γ       , Tm58 Γ top58)
     (pair  : ∀ Γ A B   , Tm58 Γ A → Tm58 Γ B → Tm58 Γ (prod58 A B))
     (fst   : ∀ Γ A B   , Tm58 Γ (prod58 A B) → Tm58 Γ A)
     (snd   : ∀ Γ A B   , Tm58 Γ (prod58 A B) → Tm58 Γ B)
     (left  : ∀ Γ A B   , Tm58 Γ A → Tm58 Γ (sum58 A B))
     (right : ∀ Γ A B   , Tm58 Γ B → Tm58 Γ (sum58 A B))
     (case  : ∀ Γ A B C , Tm58 Γ (sum58 A B) → Tm58 Γ (arr58 A C) → Tm58 Γ (arr58 B C) → Tm58 Γ C)
     (zero  : ∀ Γ       , Tm58 Γ nat58)
     (suc   : ∀ Γ       , Tm58 Γ nat58 → Tm58 Γ nat58)
     (rec   : ∀ Γ A     , Tm58 Γ nat58 → Tm58 Γ (arr58 nat58 (arr58 A A)) → Tm58 Γ A → Tm58 Γ A)
   , Tm58 Γ A.

Definition var58 {Γ A} : Var58 Γ A → Tm58 Γ A
 := λ x Tm58 var58 lam app tt pair fst snd left right case zero suc rec ,
     var58 _ _ x.

Definition lam58 {Γ A B} : Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B)
 := λ t Tm58 var58 lam58 app tt pair fst snd left right case zero suc rec ,
     lam58 _ _ _ (t Tm58 var58 lam58 app tt pair fst snd left right case zero suc rec).

Definition app58 {Γ A B} : Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B
 := λ t u Tm58 var58 lam58 app58 tt pair fst snd left right case zero suc rec ,
     app58 _ _ _
         (t Tm58 var58 lam58 app58 tt pair fst snd left right case zero suc rec)
         (u Tm58 var58 lam58 app58 tt pair fst snd left right case zero suc rec).

Definition tt58 {Γ} : Tm58 Γ top58
 := λ Tm58 var58 lam58 app58 tt58 pair fst snd left right case zero suc rec , tt58 _.

Definition pair58 {Γ A B} : Tm58 Γ A → Tm58 Γ B → Tm58 Γ (prod58 A B)
 := λ t u Tm58 var58 lam58 app58 tt58 pair58 fst snd left right case zero suc rec ,
     pair58 _ _ _
          (t Tm58 var58 lam58 app58 tt58 pair58 fst snd left right case zero suc rec)
          (u Tm58 var58 lam58 app58 tt58 pair58 fst snd left right case zero suc rec).

Definition fst58 {Γ A B} : Tm58 Γ (prod58 A B) → Tm58 Γ A
 := λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd left right case zero suc rec ,
     fst58 _ _ _
         (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd left right case zero suc rec).

Definition snd58 {Γ A B} : Tm58 Γ (prod58 A B) → Tm58 Γ B
 := λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left right case zero suc rec ,
     snd58 _ _ _
          (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left right case zero suc rec).

Definition left58 {Γ A B} : Tm58 Γ A → Tm58 Γ (sum58 A B)
 := λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right case zero suc rec ,
     left58 _ _ _
          (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right case zero suc rec).

Definition right58 {Γ A B} : Tm58 Γ B → Tm58 Γ (sum58 A B)
 := λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case zero suc rec ,
     right58 _ _ _
            (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case zero suc rec).

Definition case58 {Γ A B C} : Tm58 Γ (sum58 A B) → Tm58 Γ (arr58 A C) → Tm58 Γ (arr58 B C) → Tm58 Γ C
 := λ t u v Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero suc rec ,
     case58 _ _ _ _
           (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero suc rec)
           (u Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero suc rec)
           (v Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero suc rec).

Definition zero58  {Γ} : Tm58 Γ nat58
 := λ Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc rec , zero58 _.

Definition suc58 {Γ} : Tm58 Γ nat58 → Tm58 Γ nat58
 := λ t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec ,
   suc58 _ (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec).

Definition rec58 {Γ A} : Tm58 Γ nat58 → Tm58 Γ (arr58 nat58 (arr58 A A)) → Tm58 Γ A → Tm58 Γ A
 := λ t u v Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec58 ,
     rec58 _ _
         (t Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec58)
         (u Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec58)
         (v Tm58 var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 case58 zero58 suc58 rec58).

Definition v058 {Γ A} : Tm58 (snoc58 Γ A) A
 := var58 vz58.

Definition v158 {Γ A B} : Tm58 (snoc58 (snoc58 Γ A) B) A
 := var58 (vs58 vz58).

Definition v258 {Γ A B C} : Tm58 (snoc58 (snoc58 (snoc58 Γ A) B) C) A
 := var58 (vs58 (vs58 vz58)).

Definition v358 {Γ A B C D} : Tm58 (snoc58 (snoc58 (snoc58 (snoc58 Γ A) B) C) D) A
 := var58 (vs58 (vs58 (vs58 vz58))).

Definition tbool58 : Ty58
 := sum58 top58 top58.

Definition ttrue58 {Γ} : Tm58 Γ tbool58
 := left58 tt58.

Definition tfalse58 {Γ} : Tm58 Γ tbool58
 := right58 tt58.

Definition ifthenelse58 {Γ A} : Tm58 Γ (arr58 tbool58 (arr58 A (arr58 A A)))
 := lam58 (lam58 (lam58 (case58 v258 (lam58 v258) (lam58 v158)))).

Definition times458 {Γ A} : Tm58 Γ (arr58 (arr58 A A) (arr58 A A))
  := lam58 (lam58 (app58 v158 (app58 v158 (app58 v158 (app58 v158 v058))))).

Definition add58 {Γ} : Tm58 Γ (arr58 nat58 (arr58 nat58 nat58))
 := lam58 (rec58 v058
      (lam58 (lam58 (lam58 (suc58 (app58 v158 v058)))))
      (lam58 v058)).

Definition mul58 {Γ} : Tm58 Γ (arr58 nat58 (arr58 nat58 nat58))
 := lam58 (rec58 v058
     (lam58 (lam58 (lam58 (app58 (app58 add58 (app58 v158 v058)) v058))))
     (lam58 zero58)).

Definition fact58 {Γ} : Tm58 Γ (arr58 nat58 nat58)
 := lam58 (rec58 v058 (lam58 (lam58 (app58 (app58 mul58 (suc58 v158)) v058)))
        (suc58 zero58)).

Require Import Coq.Unicode.Utf8.

Definition Ty59 : Set
 := ∀ (Ty59           : Set)
      (nat top bot  : Ty59)
      (arr prod sum : Ty59 → Ty59 → Ty59)
    , Ty59.

Definition nat59 : Ty59 := λ _ nat59 _ _ _ _ _ , nat59.
Definition top59 : Ty59 := λ _ _ top59 _ _ _ _ , top59.
Definition bot59 : Ty59 := λ _ _ _ bot59 _ _ _ , bot59.

Definition arr59 : Ty59 → Ty59 → Ty59
 := λ A B Ty59 nat59 top59 bot59 arr59 prod sum ,
     arr59 (A Ty59 nat59 top59 bot59 arr59 prod sum) (B Ty59 nat59 top59 bot59 arr59 prod sum).

Definition prod59 : Ty59 → Ty59 → Ty59
 := λ A B Ty59 nat59 top59 bot59 arr59 prod59 sum ,
     prod59 (A Ty59 nat59 top59 bot59 arr59 prod59 sum) (B Ty59 nat59 top59 bot59 arr59 prod59 sum).

Definition sum59 : Ty59 → Ty59 → Ty59
 := λ A B Ty59 nat59 top59 bot59 arr59 prod59 sum59 ,
     sum59 (A Ty59 nat59 top59 bot59 arr59 prod59 sum59) (B Ty59 nat59 top59 bot59 arr59 prod59 sum59).

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
     (tt    : ∀ Γ       , Tm59 Γ top59)
     (pair  : ∀ Γ A B   , Tm59 Γ A → Tm59 Γ B → Tm59 Γ (prod59 A B))
     (fst   : ∀ Γ A B   , Tm59 Γ (prod59 A B) → Tm59 Γ A)
     (snd   : ∀ Γ A B   , Tm59 Γ (prod59 A B) → Tm59 Γ B)
     (left  : ∀ Γ A B   , Tm59 Γ A → Tm59 Γ (sum59 A B))
     (right : ∀ Γ A B   , Tm59 Γ B → Tm59 Γ (sum59 A B))
     (case  : ∀ Γ A B C , Tm59 Γ (sum59 A B) → Tm59 Γ (arr59 A C) → Tm59 Γ (arr59 B C) → Tm59 Γ C)
     (zero  : ∀ Γ       , Tm59 Γ nat59)
     (suc   : ∀ Γ       , Tm59 Γ nat59 → Tm59 Γ nat59)
     (rec   : ∀ Γ A     , Tm59 Γ nat59 → Tm59 Γ (arr59 nat59 (arr59 A A)) → Tm59 Γ A → Tm59 Γ A)
   , Tm59 Γ A.

Definition var59 {Γ A} : Var59 Γ A → Tm59 Γ A
 := λ x Tm59 var59 lam app tt pair fst snd left right case zero suc rec ,
     var59 _ _ x.

Definition lam59 {Γ A B} : Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B)
 := λ t Tm59 var59 lam59 app tt pair fst snd left right case zero suc rec ,
     lam59 _ _ _ (t Tm59 var59 lam59 app tt pair fst snd left right case zero suc rec).

Definition app59 {Γ A B} : Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B
 := λ t u Tm59 var59 lam59 app59 tt pair fst snd left right case zero suc rec ,
     app59 _ _ _
         (t Tm59 var59 lam59 app59 tt pair fst snd left right case zero suc rec)
         (u Tm59 var59 lam59 app59 tt pair fst snd left right case zero suc rec).

Definition tt59 {Γ} : Tm59 Γ top59
 := λ Tm59 var59 lam59 app59 tt59 pair fst snd left right case zero suc rec , tt59 _.

Definition pair59 {Γ A B} : Tm59 Γ A → Tm59 Γ B → Tm59 Γ (prod59 A B)
 := λ t u Tm59 var59 lam59 app59 tt59 pair59 fst snd left right case zero suc rec ,
     pair59 _ _ _
          (t Tm59 var59 lam59 app59 tt59 pair59 fst snd left right case zero suc rec)
          (u Tm59 var59 lam59 app59 tt59 pair59 fst snd left right case zero suc rec).

Definition fst59 {Γ A B} : Tm59 Γ (prod59 A B) → Tm59 Γ A
 := λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd left right case zero suc rec ,
     fst59 _ _ _
         (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd left right case zero suc rec).

Definition snd59 {Γ A B} : Tm59 Γ (prod59 A B) → Tm59 Γ B
 := λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left right case zero suc rec ,
     snd59 _ _ _
          (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left right case zero suc rec).

Definition left59 {Γ A B} : Tm59 Γ A → Tm59 Γ (sum59 A B)
 := λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right case zero suc rec ,
     left59 _ _ _
          (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right case zero suc rec).

Definition right59 {Γ A B} : Tm59 Γ B → Tm59 Γ (sum59 A B)
 := λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case zero suc rec ,
     right59 _ _ _
            (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case zero suc rec).

Definition case59 {Γ A B C} : Tm59 Γ (sum59 A B) → Tm59 Γ (arr59 A C) → Tm59 Γ (arr59 B C) → Tm59 Γ C
 := λ t u v Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero suc rec ,
     case59 _ _ _ _
           (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero suc rec)
           (u Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero suc rec)
           (v Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero suc rec).

Definition zero59  {Γ} : Tm59 Γ nat59
 := λ Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc rec , zero59 _.

Definition suc59 {Γ} : Tm59 Γ nat59 → Tm59 Γ nat59
 := λ t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec ,
   suc59 _ (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec).

Definition rec59 {Γ A} : Tm59 Γ nat59 → Tm59 Γ (arr59 nat59 (arr59 A A)) → Tm59 Γ A → Tm59 Γ A
 := λ t u v Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec59 ,
     rec59 _ _
         (t Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec59)
         (u Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec59)
         (v Tm59 var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 case59 zero59 suc59 rec59).

Definition v059 {Γ A} : Tm59 (snoc59 Γ A) A
 := var59 vz59.

Definition v159 {Γ A B} : Tm59 (snoc59 (snoc59 Γ A) B) A
 := var59 (vs59 vz59).

Definition v259 {Γ A B C} : Tm59 (snoc59 (snoc59 (snoc59 Γ A) B) C) A
 := var59 (vs59 (vs59 vz59)).

Definition v359 {Γ A B C D} : Tm59 (snoc59 (snoc59 (snoc59 (snoc59 Γ A) B) C) D) A
 := var59 (vs59 (vs59 (vs59 vz59))).

Definition tbool59 : Ty59
 := sum59 top59 top59.

Definition ttrue59 {Γ} : Tm59 Γ tbool59
 := left59 tt59.

Definition tfalse59 {Γ} : Tm59 Γ tbool59
 := right59 tt59.

Definition ifthenelse59 {Γ A} : Tm59 Γ (arr59 tbool59 (arr59 A (arr59 A A)))
 := lam59 (lam59 (lam59 (case59 v259 (lam59 v259) (lam59 v159)))).

Definition times459 {Γ A} : Tm59 Γ (arr59 (arr59 A A) (arr59 A A))
  := lam59 (lam59 (app59 v159 (app59 v159 (app59 v159 (app59 v159 v059))))).

Definition add59 {Γ} : Tm59 Γ (arr59 nat59 (arr59 nat59 nat59))
 := lam59 (rec59 v059
      (lam59 (lam59 (lam59 (suc59 (app59 v159 v059)))))
      (lam59 v059)).

Definition mul59 {Γ} : Tm59 Γ (arr59 nat59 (arr59 nat59 nat59))
 := lam59 (rec59 v059
     (lam59 (lam59 (lam59 (app59 (app59 add59 (app59 v159 v059)) v059))))
     (lam59 zero59)).

Definition fact59 {Γ} : Tm59 Γ (arr59 nat59 nat59)
 := lam59 (rec59 v059 (lam59 (lam59 (app59 (app59 mul59 (suc59 v159)) v059)))
        (suc59 zero59)).

Require Import Coq.Unicode.Utf8.

Definition Ty60 : Set
 := ∀ (Ty60           : Set)
      (nat top bot  : Ty60)
      (arr prod sum : Ty60 → Ty60 → Ty60)
    , Ty60.

Definition nat60 : Ty60 := λ _ nat60 _ _ _ _ _ , nat60.
Definition top60 : Ty60 := λ _ _ top60 _ _ _ _ , top60.
Definition bot60 : Ty60 := λ _ _ _ bot60 _ _ _ , bot60.

Definition arr60 : Ty60 → Ty60 → Ty60
 := λ A B Ty60 nat60 top60 bot60 arr60 prod sum ,
     arr60 (A Ty60 nat60 top60 bot60 arr60 prod sum) (B Ty60 nat60 top60 bot60 arr60 prod sum).

Definition prod60 : Ty60 → Ty60 → Ty60
 := λ A B Ty60 nat60 top60 bot60 arr60 prod60 sum ,
     prod60 (A Ty60 nat60 top60 bot60 arr60 prod60 sum) (B Ty60 nat60 top60 bot60 arr60 prod60 sum).

Definition sum60 : Ty60 → Ty60 → Ty60
 := λ A B Ty60 nat60 top60 bot60 arr60 prod60 sum60 ,
     sum60 (A Ty60 nat60 top60 bot60 arr60 prod60 sum60) (B Ty60 nat60 top60 bot60 arr60 prod60 sum60).

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
     (tt    : ∀ Γ       , Tm60 Γ top60)
     (pair  : ∀ Γ A B   , Tm60 Γ A → Tm60 Γ B → Tm60 Γ (prod60 A B))
     (fst   : ∀ Γ A B   , Tm60 Γ (prod60 A B) → Tm60 Γ A)
     (snd   : ∀ Γ A B   , Tm60 Γ (prod60 A B) → Tm60 Γ B)
     (left  : ∀ Γ A B   , Tm60 Γ A → Tm60 Γ (sum60 A B))
     (right : ∀ Γ A B   , Tm60 Γ B → Tm60 Γ (sum60 A B))
     (case  : ∀ Γ A B C , Tm60 Γ (sum60 A B) → Tm60 Γ (arr60 A C) → Tm60 Γ (arr60 B C) → Tm60 Γ C)
     (zero  : ∀ Γ       , Tm60 Γ nat60)
     (suc   : ∀ Γ       , Tm60 Γ nat60 → Tm60 Γ nat60)
     (rec   : ∀ Γ A     , Tm60 Γ nat60 → Tm60 Γ (arr60 nat60 (arr60 A A)) → Tm60 Γ A → Tm60 Γ A)
   , Tm60 Γ A.

Definition var60 {Γ A} : Var60 Γ A → Tm60 Γ A
 := λ x Tm60 var60 lam app tt pair fst snd left right case zero suc rec ,
     var60 _ _ x.

Definition lam60 {Γ A B} : Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B)
 := λ t Tm60 var60 lam60 app tt pair fst snd left right case zero suc rec ,
     lam60 _ _ _ (t Tm60 var60 lam60 app tt pair fst snd left right case zero suc rec).

Definition app60 {Γ A B} : Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B
 := λ t u Tm60 var60 lam60 app60 tt pair fst snd left right case zero suc rec ,
     app60 _ _ _
         (t Tm60 var60 lam60 app60 tt pair fst snd left right case zero suc rec)
         (u Tm60 var60 lam60 app60 tt pair fst snd left right case zero suc rec).

Definition tt60 {Γ} : Tm60 Γ top60
 := λ Tm60 var60 lam60 app60 tt60 pair fst snd left right case zero suc rec , tt60 _.

Definition pair60 {Γ A B} : Tm60 Γ A → Tm60 Γ B → Tm60 Γ (prod60 A B)
 := λ t u Tm60 var60 lam60 app60 tt60 pair60 fst snd left right case zero suc rec ,
     pair60 _ _ _
          (t Tm60 var60 lam60 app60 tt60 pair60 fst snd left right case zero suc rec)
          (u Tm60 var60 lam60 app60 tt60 pair60 fst snd left right case zero suc rec).

Definition fst60 {Γ A B} : Tm60 Γ (prod60 A B) → Tm60 Γ A
 := λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd left right case zero suc rec ,
     fst60 _ _ _
         (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd left right case zero suc rec).

Definition snd60 {Γ A B} : Tm60 Γ (prod60 A B) → Tm60 Γ B
 := λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left right case zero suc rec ,
     snd60 _ _ _
          (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left right case zero suc rec).

Definition left60 {Γ A B} : Tm60 Γ A → Tm60 Γ (sum60 A B)
 := λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right case zero suc rec ,
     left60 _ _ _
          (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right case zero suc rec).

Definition right60 {Γ A B} : Tm60 Γ B → Tm60 Γ (sum60 A B)
 := λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case zero suc rec ,
     right60 _ _ _
            (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case zero suc rec).

Definition case60 {Γ A B C} : Tm60 Γ (sum60 A B) → Tm60 Γ (arr60 A C) → Tm60 Γ (arr60 B C) → Tm60 Γ C
 := λ t u v Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero suc rec ,
     case60 _ _ _ _
           (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero suc rec)
           (u Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero suc rec)
           (v Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero suc rec).

Definition zero60  {Γ} : Tm60 Γ nat60
 := λ Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc rec , zero60 _.

Definition suc60 {Γ} : Tm60 Γ nat60 → Tm60 Γ nat60
 := λ t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec ,
   suc60 _ (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec).

Definition rec60 {Γ A} : Tm60 Γ nat60 → Tm60 Γ (arr60 nat60 (arr60 A A)) → Tm60 Γ A → Tm60 Γ A
 := λ t u v Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec60 ,
     rec60 _ _
         (t Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec60)
         (u Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec60)
         (v Tm60 var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 case60 zero60 suc60 rec60).

Definition v060 {Γ A} : Tm60 (snoc60 Γ A) A
 := var60 vz60.

Definition v160 {Γ A B} : Tm60 (snoc60 (snoc60 Γ A) B) A
 := var60 (vs60 vz60).

Definition v260 {Γ A B C} : Tm60 (snoc60 (snoc60 (snoc60 Γ A) B) C) A
 := var60 (vs60 (vs60 vz60)).

Definition v360 {Γ A B C D} : Tm60 (snoc60 (snoc60 (snoc60 (snoc60 Γ A) B) C) D) A
 := var60 (vs60 (vs60 (vs60 vz60))).

Definition tbool60 : Ty60
 := sum60 top60 top60.

Definition ttrue60 {Γ} : Tm60 Γ tbool60
 := left60 tt60.

Definition tfalse60 {Γ} : Tm60 Γ tbool60
 := right60 tt60.

Definition ifthenelse60 {Γ A} : Tm60 Γ (arr60 tbool60 (arr60 A (arr60 A A)))
 := lam60 (lam60 (lam60 (case60 v260 (lam60 v260) (lam60 v160)))).

Definition times460 {Γ A} : Tm60 Γ (arr60 (arr60 A A) (arr60 A A))
  := lam60 (lam60 (app60 v160 (app60 v160 (app60 v160 (app60 v160 v060))))).

Definition add60 {Γ} : Tm60 Γ (arr60 nat60 (arr60 nat60 nat60))
 := lam60 (rec60 v060
      (lam60 (lam60 (lam60 (suc60 (app60 v160 v060)))))
      (lam60 v060)).

Definition mul60 {Γ} : Tm60 Γ (arr60 nat60 (arr60 nat60 nat60))
 := lam60 (rec60 v060
     (lam60 (lam60 (lam60 (app60 (app60 add60 (app60 v160 v060)) v060))))
     (lam60 zero60)).

Definition fact60 {Γ} : Tm60 Γ (arr60 nat60 nat60)
 := lam60 (rec60 v060 (lam60 (lam60 (app60 (app60 mul60 (suc60 v160)) v060)))
        (suc60 zero60)).

Require Import Coq.Unicode.Utf8.

Definition Ty61 : Set
 := ∀ (Ty61           : Set)
      (nat top bot  : Ty61)
      (arr prod sum : Ty61 → Ty61 → Ty61)
    , Ty61.

Definition nat61 : Ty61 := λ _ nat61 _ _ _ _ _ , nat61.
Definition top61 : Ty61 := λ _ _ top61 _ _ _ _ , top61.
Definition bot61 : Ty61 := λ _ _ _ bot61 _ _ _ , bot61.

Definition arr61 : Ty61 → Ty61 → Ty61
 := λ A B Ty61 nat61 top61 bot61 arr61 prod sum ,
     arr61 (A Ty61 nat61 top61 bot61 arr61 prod sum) (B Ty61 nat61 top61 bot61 arr61 prod sum).

Definition prod61 : Ty61 → Ty61 → Ty61
 := λ A B Ty61 nat61 top61 bot61 arr61 prod61 sum ,
     prod61 (A Ty61 nat61 top61 bot61 arr61 prod61 sum) (B Ty61 nat61 top61 bot61 arr61 prod61 sum).

Definition sum61 : Ty61 → Ty61 → Ty61
 := λ A B Ty61 nat61 top61 bot61 arr61 prod61 sum61 ,
     sum61 (A Ty61 nat61 top61 bot61 arr61 prod61 sum61) (B Ty61 nat61 top61 bot61 arr61 prod61 sum61).

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
     (tt    : ∀ Γ       , Tm61 Γ top61)
     (pair  : ∀ Γ A B   , Tm61 Γ A → Tm61 Γ B → Tm61 Γ (prod61 A B))
     (fst   : ∀ Γ A B   , Tm61 Γ (prod61 A B) → Tm61 Γ A)
     (snd   : ∀ Γ A B   , Tm61 Γ (prod61 A B) → Tm61 Γ B)
     (left  : ∀ Γ A B   , Tm61 Γ A → Tm61 Γ (sum61 A B))
     (right : ∀ Γ A B   , Tm61 Γ B → Tm61 Γ (sum61 A B))
     (case  : ∀ Γ A B C , Tm61 Γ (sum61 A B) → Tm61 Γ (arr61 A C) → Tm61 Γ (arr61 B C) → Tm61 Γ C)
     (zero  : ∀ Γ       , Tm61 Γ nat61)
     (suc   : ∀ Γ       , Tm61 Γ nat61 → Tm61 Γ nat61)
     (rec   : ∀ Γ A     , Tm61 Γ nat61 → Tm61 Γ (arr61 nat61 (arr61 A A)) → Tm61 Γ A → Tm61 Γ A)
   , Tm61 Γ A.

Definition var61 {Γ A} : Var61 Γ A → Tm61 Γ A
 := λ x Tm61 var61 lam app tt pair fst snd left right case zero suc rec ,
     var61 _ _ x.

Definition lam61 {Γ A B} : Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B)
 := λ t Tm61 var61 lam61 app tt pair fst snd left right case zero suc rec ,
     lam61 _ _ _ (t Tm61 var61 lam61 app tt pair fst snd left right case zero suc rec).

Definition app61 {Γ A B} : Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B
 := λ t u Tm61 var61 lam61 app61 tt pair fst snd left right case zero suc rec ,
     app61 _ _ _
         (t Tm61 var61 lam61 app61 tt pair fst snd left right case zero suc rec)
         (u Tm61 var61 lam61 app61 tt pair fst snd left right case zero suc rec).

Definition tt61 {Γ} : Tm61 Γ top61
 := λ Tm61 var61 lam61 app61 tt61 pair fst snd left right case zero suc rec , tt61 _.

Definition pair61 {Γ A B} : Tm61 Γ A → Tm61 Γ B → Tm61 Γ (prod61 A B)
 := λ t u Tm61 var61 lam61 app61 tt61 pair61 fst snd left right case zero suc rec ,
     pair61 _ _ _
          (t Tm61 var61 lam61 app61 tt61 pair61 fst snd left right case zero suc rec)
          (u Tm61 var61 lam61 app61 tt61 pair61 fst snd left right case zero suc rec).

Definition fst61 {Γ A B} : Tm61 Γ (prod61 A B) → Tm61 Γ A
 := λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd left right case zero suc rec ,
     fst61 _ _ _
         (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd left right case zero suc rec).

Definition snd61 {Γ A B} : Tm61 Γ (prod61 A B) → Tm61 Γ B
 := λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left right case zero suc rec ,
     snd61 _ _ _
          (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left right case zero suc rec).

Definition left61 {Γ A B} : Tm61 Γ A → Tm61 Γ (sum61 A B)
 := λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right case zero suc rec ,
     left61 _ _ _
          (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right case zero suc rec).

Definition right61 {Γ A B} : Tm61 Γ B → Tm61 Γ (sum61 A B)
 := λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case zero suc rec ,
     right61 _ _ _
            (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case zero suc rec).

Definition case61 {Γ A B C} : Tm61 Γ (sum61 A B) → Tm61 Γ (arr61 A C) → Tm61 Γ (arr61 B C) → Tm61 Γ C
 := λ t u v Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero suc rec ,
     case61 _ _ _ _
           (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero suc rec)
           (u Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero suc rec)
           (v Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero suc rec).

Definition zero61  {Γ} : Tm61 Γ nat61
 := λ Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc rec , zero61 _.

Definition suc61 {Γ} : Tm61 Γ nat61 → Tm61 Γ nat61
 := λ t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec ,
   suc61 _ (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec).

Definition rec61 {Γ A} : Tm61 Γ nat61 → Tm61 Γ (arr61 nat61 (arr61 A A)) → Tm61 Γ A → Tm61 Γ A
 := λ t u v Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec61 ,
     rec61 _ _
         (t Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec61)
         (u Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec61)
         (v Tm61 var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 case61 zero61 suc61 rec61).

Definition v061 {Γ A} : Tm61 (snoc61 Γ A) A
 := var61 vz61.

Definition v161 {Γ A B} : Tm61 (snoc61 (snoc61 Γ A) B) A
 := var61 (vs61 vz61).

Definition v261 {Γ A B C} : Tm61 (snoc61 (snoc61 (snoc61 Γ A) B) C) A
 := var61 (vs61 (vs61 vz61)).

Definition v361 {Γ A B C D} : Tm61 (snoc61 (snoc61 (snoc61 (snoc61 Γ A) B) C) D) A
 := var61 (vs61 (vs61 (vs61 vz61))).

Definition tbool61 : Ty61
 := sum61 top61 top61.

Definition ttrue61 {Γ} : Tm61 Γ tbool61
 := left61 tt61.

Definition tfalse61 {Γ} : Tm61 Γ tbool61
 := right61 tt61.

Definition ifthenelse61 {Γ A} : Tm61 Γ (arr61 tbool61 (arr61 A (arr61 A A)))
 := lam61 (lam61 (lam61 (case61 v261 (lam61 v261) (lam61 v161)))).

Definition times461 {Γ A} : Tm61 Γ (arr61 (arr61 A A) (arr61 A A))
  := lam61 (lam61 (app61 v161 (app61 v161 (app61 v161 (app61 v161 v061))))).

Definition add61 {Γ} : Tm61 Γ (arr61 nat61 (arr61 nat61 nat61))
 := lam61 (rec61 v061
      (lam61 (lam61 (lam61 (suc61 (app61 v161 v061)))))
      (lam61 v061)).

Definition mul61 {Γ} : Tm61 Γ (arr61 nat61 (arr61 nat61 nat61))
 := lam61 (rec61 v061
     (lam61 (lam61 (lam61 (app61 (app61 add61 (app61 v161 v061)) v061))))
     (lam61 zero61)).

Definition fact61 {Γ} : Tm61 Γ (arr61 nat61 nat61)
 := lam61 (rec61 v061 (lam61 (lam61 (app61 (app61 mul61 (suc61 v161)) v061)))
        (suc61 zero61)).

Require Import Coq.Unicode.Utf8.

Definition Ty62 : Set
 := ∀ (Ty62           : Set)
      (nat top bot  : Ty62)
      (arr prod sum : Ty62 → Ty62 → Ty62)
    , Ty62.

Definition nat62 : Ty62 := λ _ nat62 _ _ _ _ _ , nat62.
Definition top62 : Ty62 := λ _ _ top62 _ _ _ _ , top62.
Definition bot62 : Ty62 := λ _ _ _ bot62 _ _ _ , bot62.

Definition arr62 : Ty62 → Ty62 → Ty62
 := λ A B Ty62 nat62 top62 bot62 arr62 prod sum ,
     arr62 (A Ty62 nat62 top62 bot62 arr62 prod sum) (B Ty62 nat62 top62 bot62 arr62 prod sum).

Definition prod62 : Ty62 → Ty62 → Ty62
 := λ A B Ty62 nat62 top62 bot62 arr62 prod62 sum ,
     prod62 (A Ty62 nat62 top62 bot62 arr62 prod62 sum) (B Ty62 nat62 top62 bot62 arr62 prod62 sum).

Definition sum62 : Ty62 → Ty62 → Ty62
 := λ A B Ty62 nat62 top62 bot62 arr62 prod62 sum62 ,
     sum62 (A Ty62 nat62 top62 bot62 arr62 prod62 sum62) (B Ty62 nat62 top62 bot62 arr62 prod62 sum62).

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
     (tt    : ∀ Γ       , Tm62 Γ top62)
     (pair  : ∀ Γ A B   , Tm62 Γ A → Tm62 Γ B → Tm62 Γ (prod62 A B))
     (fst   : ∀ Γ A B   , Tm62 Γ (prod62 A B) → Tm62 Γ A)
     (snd   : ∀ Γ A B   , Tm62 Γ (prod62 A B) → Tm62 Γ B)
     (left  : ∀ Γ A B   , Tm62 Γ A → Tm62 Γ (sum62 A B))
     (right : ∀ Γ A B   , Tm62 Γ B → Tm62 Γ (sum62 A B))
     (case  : ∀ Γ A B C , Tm62 Γ (sum62 A B) → Tm62 Γ (arr62 A C) → Tm62 Γ (arr62 B C) → Tm62 Γ C)
     (zero  : ∀ Γ       , Tm62 Γ nat62)
     (suc   : ∀ Γ       , Tm62 Γ nat62 → Tm62 Γ nat62)
     (rec   : ∀ Γ A     , Tm62 Γ nat62 → Tm62 Γ (arr62 nat62 (arr62 A A)) → Tm62 Γ A → Tm62 Γ A)
   , Tm62 Γ A.

Definition var62 {Γ A} : Var62 Γ A → Tm62 Γ A
 := λ x Tm62 var62 lam app tt pair fst snd left right case zero suc rec ,
     var62 _ _ x.

Definition lam62 {Γ A B} : Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B)
 := λ t Tm62 var62 lam62 app tt pair fst snd left right case zero suc rec ,
     lam62 _ _ _ (t Tm62 var62 lam62 app tt pair fst snd left right case zero suc rec).

Definition app62 {Γ A B} : Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B
 := λ t u Tm62 var62 lam62 app62 tt pair fst snd left right case zero suc rec ,
     app62 _ _ _
         (t Tm62 var62 lam62 app62 tt pair fst snd left right case zero suc rec)
         (u Tm62 var62 lam62 app62 tt pair fst snd left right case zero suc rec).

Definition tt62 {Γ} : Tm62 Γ top62
 := λ Tm62 var62 lam62 app62 tt62 pair fst snd left right case zero suc rec , tt62 _.

Definition pair62 {Γ A B} : Tm62 Γ A → Tm62 Γ B → Tm62 Γ (prod62 A B)
 := λ t u Tm62 var62 lam62 app62 tt62 pair62 fst snd left right case zero suc rec ,
     pair62 _ _ _
          (t Tm62 var62 lam62 app62 tt62 pair62 fst snd left right case zero suc rec)
          (u Tm62 var62 lam62 app62 tt62 pair62 fst snd left right case zero suc rec).

Definition fst62 {Γ A B} : Tm62 Γ (prod62 A B) → Tm62 Γ A
 := λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd left right case zero suc rec ,
     fst62 _ _ _
         (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd left right case zero suc rec).

Definition snd62 {Γ A B} : Tm62 Γ (prod62 A B) → Tm62 Γ B
 := λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left right case zero suc rec ,
     snd62 _ _ _
          (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left right case zero suc rec).

Definition left62 {Γ A B} : Tm62 Γ A → Tm62 Γ (sum62 A B)
 := λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right case zero suc rec ,
     left62 _ _ _
          (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right case zero suc rec).

Definition right62 {Γ A B} : Tm62 Γ B → Tm62 Γ (sum62 A B)
 := λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case zero suc rec ,
     right62 _ _ _
            (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case zero suc rec).

Definition case62 {Γ A B C} : Tm62 Γ (sum62 A B) → Tm62 Γ (arr62 A C) → Tm62 Γ (arr62 B C) → Tm62 Γ C
 := λ t u v Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero suc rec ,
     case62 _ _ _ _
           (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero suc rec)
           (u Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero suc rec)
           (v Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero suc rec).

Definition zero62  {Γ} : Tm62 Γ nat62
 := λ Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc rec , zero62 _.

Definition suc62 {Γ} : Tm62 Γ nat62 → Tm62 Γ nat62
 := λ t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec ,
   suc62 _ (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec).

Definition rec62 {Γ A} : Tm62 Γ nat62 → Tm62 Γ (arr62 nat62 (arr62 A A)) → Tm62 Γ A → Tm62 Γ A
 := λ t u v Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec62 ,
     rec62 _ _
         (t Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec62)
         (u Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec62)
         (v Tm62 var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 case62 zero62 suc62 rec62).

Definition v062 {Γ A} : Tm62 (snoc62 Γ A) A
 := var62 vz62.

Definition v162 {Γ A B} : Tm62 (snoc62 (snoc62 Γ A) B) A
 := var62 (vs62 vz62).

Definition v262 {Γ A B C} : Tm62 (snoc62 (snoc62 (snoc62 Γ A) B) C) A
 := var62 (vs62 (vs62 vz62)).

Definition v362 {Γ A B C D} : Tm62 (snoc62 (snoc62 (snoc62 (snoc62 Γ A) B) C) D) A
 := var62 (vs62 (vs62 (vs62 vz62))).

Definition tbool62 : Ty62
 := sum62 top62 top62.

Definition ttrue62 {Γ} : Tm62 Γ tbool62
 := left62 tt62.

Definition tfalse62 {Γ} : Tm62 Γ tbool62
 := right62 tt62.

Definition ifthenelse62 {Γ A} : Tm62 Γ (arr62 tbool62 (arr62 A (arr62 A A)))
 := lam62 (lam62 (lam62 (case62 v262 (lam62 v262) (lam62 v162)))).

Definition times462 {Γ A} : Tm62 Γ (arr62 (arr62 A A) (arr62 A A))
  := lam62 (lam62 (app62 v162 (app62 v162 (app62 v162 (app62 v162 v062))))).

Definition add62 {Γ} : Tm62 Γ (arr62 nat62 (arr62 nat62 nat62))
 := lam62 (rec62 v062
      (lam62 (lam62 (lam62 (suc62 (app62 v162 v062)))))
      (lam62 v062)).

Definition mul62 {Γ} : Tm62 Γ (arr62 nat62 (arr62 nat62 nat62))
 := lam62 (rec62 v062
     (lam62 (lam62 (lam62 (app62 (app62 add62 (app62 v162 v062)) v062))))
     (lam62 zero62)).

Definition fact62 {Γ} : Tm62 Γ (arr62 nat62 nat62)
 := lam62 (rec62 v062 (lam62 (lam62 (app62 (app62 mul62 (suc62 v162)) v062)))
        (suc62 zero62)).

Require Import Coq.Unicode.Utf8.

Definition Ty63 : Set
 := ∀ (Ty63           : Set)
      (nat top bot  : Ty63)
      (arr prod sum : Ty63 → Ty63 → Ty63)
    , Ty63.

Definition nat63 : Ty63 := λ _ nat63 _ _ _ _ _ , nat63.
Definition top63 : Ty63 := λ _ _ top63 _ _ _ _ , top63.
Definition bot63 : Ty63 := λ _ _ _ bot63 _ _ _ , bot63.

Definition arr63 : Ty63 → Ty63 → Ty63
 := λ A B Ty63 nat63 top63 bot63 arr63 prod sum ,
     arr63 (A Ty63 nat63 top63 bot63 arr63 prod sum) (B Ty63 nat63 top63 bot63 arr63 prod sum).

Definition prod63 : Ty63 → Ty63 → Ty63
 := λ A B Ty63 nat63 top63 bot63 arr63 prod63 sum ,
     prod63 (A Ty63 nat63 top63 bot63 arr63 prod63 sum) (B Ty63 nat63 top63 bot63 arr63 prod63 sum).

Definition sum63 : Ty63 → Ty63 → Ty63
 := λ A B Ty63 nat63 top63 bot63 arr63 prod63 sum63 ,
     sum63 (A Ty63 nat63 top63 bot63 arr63 prod63 sum63) (B Ty63 nat63 top63 bot63 arr63 prod63 sum63).

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
     (tt    : ∀ Γ       , Tm63 Γ top63)
     (pair  : ∀ Γ A B   , Tm63 Γ A → Tm63 Γ B → Tm63 Γ (prod63 A B))
     (fst   : ∀ Γ A B   , Tm63 Γ (prod63 A B) → Tm63 Γ A)
     (snd   : ∀ Γ A B   , Tm63 Γ (prod63 A B) → Tm63 Γ B)
     (left  : ∀ Γ A B   , Tm63 Γ A → Tm63 Γ (sum63 A B))
     (right : ∀ Γ A B   , Tm63 Γ B → Tm63 Γ (sum63 A B))
     (case  : ∀ Γ A B C , Tm63 Γ (sum63 A B) → Tm63 Γ (arr63 A C) → Tm63 Γ (arr63 B C) → Tm63 Γ C)
     (zero  : ∀ Γ       , Tm63 Γ nat63)
     (suc   : ∀ Γ       , Tm63 Γ nat63 → Tm63 Γ nat63)
     (rec   : ∀ Γ A     , Tm63 Γ nat63 → Tm63 Γ (arr63 nat63 (arr63 A A)) → Tm63 Γ A → Tm63 Γ A)
   , Tm63 Γ A.

Definition var63 {Γ A} : Var63 Γ A → Tm63 Γ A
 := λ x Tm63 var63 lam app tt pair fst snd left right case zero suc rec ,
     var63 _ _ x.

Definition lam63 {Γ A B} : Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B)
 := λ t Tm63 var63 lam63 app tt pair fst snd left right case zero suc rec ,
     lam63 _ _ _ (t Tm63 var63 lam63 app tt pair fst snd left right case zero suc rec).

Definition app63 {Γ A B} : Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B
 := λ t u Tm63 var63 lam63 app63 tt pair fst snd left right case zero suc rec ,
     app63 _ _ _
         (t Tm63 var63 lam63 app63 tt pair fst snd left right case zero suc rec)
         (u Tm63 var63 lam63 app63 tt pair fst snd left right case zero suc rec).

Definition tt63 {Γ} : Tm63 Γ top63
 := λ Tm63 var63 lam63 app63 tt63 pair fst snd left right case zero suc rec , tt63 _.

Definition pair63 {Γ A B} : Tm63 Γ A → Tm63 Γ B → Tm63 Γ (prod63 A B)
 := λ t u Tm63 var63 lam63 app63 tt63 pair63 fst snd left right case zero suc rec ,
     pair63 _ _ _
          (t Tm63 var63 lam63 app63 tt63 pair63 fst snd left right case zero suc rec)
          (u Tm63 var63 lam63 app63 tt63 pair63 fst snd left right case zero suc rec).

Definition fst63 {Γ A B} : Tm63 Γ (prod63 A B) → Tm63 Γ A
 := λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd left right case zero suc rec ,
     fst63 _ _ _
         (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd left right case zero suc rec).

Definition snd63 {Γ A B} : Tm63 Γ (prod63 A B) → Tm63 Γ B
 := λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left right case zero suc rec ,
     snd63 _ _ _
          (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left right case zero suc rec).

Definition left63 {Γ A B} : Tm63 Γ A → Tm63 Γ (sum63 A B)
 := λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right case zero suc rec ,
     left63 _ _ _
          (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right case zero suc rec).

Definition right63 {Γ A B} : Tm63 Γ B → Tm63 Γ (sum63 A B)
 := λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case zero suc rec ,
     right63 _ _ _
            (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case zero suc rec).

Definition case63 {Γ A B C} : Tm63 Γ (sum63 A B) → Tm63 Γ (arr63 A C) → Tm63 Γ (arr63 B C) → Tm63 Γ C
 := λ t u v Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero suc rec ,
     case63 _ _ _ _
           (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero suc rec)
           (u Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero suc rec)
           (v Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero suc rec).

Definition zero63  {Γ} : Tm63 Γ nat63
 := λ Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc rec , zero63 _.

Definition suc63 {Γ} : Tm63 Γ nat63 → Tm63 Γ nat63
 := λ t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec ,
   suc63 _ (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec).

Definition rec63 {Γ A} : Tm63 Γ nat63 → Tm63 Γ (arr63 nat63 (arr63 A A)) → Tm63 Γ A → Tm63 Γ A
 := λ t u v Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec63 ,
     rec63 _ _
         (t Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec63)
         (u Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec63)
         (v Tm63 var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 case63 zero63 suc63 rec63).

Definition v063 {Γ A} : Tm63 (snoc63 Γ A) A
 := var63 vz63.

Definition v163 {Γ A B} : Tm63 (snoc63 (snoc63 Γ A) B) A
 := var63 (vs63 vz63).

Definition v263 {Γ A B C} : Tm63 (snoc63 (snoc63 (snoc63 Γ A) B) C) A
 := var63 (vs63 (vs63 vz63)).

Definition v363 {Γ A B C D} : Tm63 (snoc63 (snoc63 (snoc63 (snoc63 Γ A) B) C) D) A
 := var63 (vs63 (vs63 (vs63 vz63))).

Definition tbool63 : Ty63
 := sum63 top63 top63.

Definition ttrue63 {Γ} : Tm63 Γ tbool63
 := left63 tt63.

Definition tfalse63 {Γ} : Tm63 Γ tbool63
 := right63 tt63.

Definition ifthenelse63 {Γ A} : Tm63 Γ (arr63 tbool63 (arr63 A (arr63 A A)))
 := lam63 (lam63 (lam63 (case63 v263 (lam63 v263) (lam63 v163)))).

Definition times463 {Γ A} : Tm63 Γ (arr63 (arr63 A A) (arr63 A A))
  := lam63 (lam63 (app63 v163 (app63 v163 (app63 v163 (app63 v163 v063))))).

Definition add63 {Γ} : Tm63 Γ (arr63 nat63 (arr63 nat63 nat63))
 := lam63 (rec63 v063
      (lam63 (lam63 (lam63 (suc63 (app63 v163 v063)))))
      (lam63 v063)).

Definition mul63 {Γ} : Tm63 Γ (arr63 nat63 (arr63 nat63 nat63))
 := lam63 (rec63 v063
     (lam63 (lam63 (lam63 (app63 (app63 add63 (app63 v163 v063)) v063))))
     (lam63 zero63)).

Definition fact63 {Γ} : Tm63 Γ (arr63 nat63 nat63)
 := lam63 (rec63 v063 (lam63 (lam63 (app63 (app63 mul63 (suc63 v163)) v063)))
        (suc63 zero63)).

Require Import Coq.Unicode.Utf8.

Definition Ty64 : Set
 := ∀ (Ty64           : Set)
      (nat top bot  : Ty64)
      (arr prod sum : Ty64 → Ty64 → Ty64)
    , Ty64.

Definition nat64 : Ty64 := λ _ nat64 _ _ _ _ _ , nat64.
Definition top64 : Ty64 := λ _ _ top64 _ _ _ _ , top64.
Definition bot64 : Ty64 := λ _ _ _ bot64 _ _ _ , bot64.

Definition arr64 : Ty64 → Ty64 → Ty64
 := λ A B Ty64 nat64 top64 bot64 arr64 prod sum ,
     arr64 (A Ty64 nat64 top64 bot64 arr64 prod sum) (B Ty64 nat64 top64 bot64 arr64 prod sum).

Definition prod64 : Ty64 → Ty64 → Ty64
 := λ A B Ty64 nat64 top64 bot64 arr64 prod64 sum ,
     prod64 (A Ty64 nat64 top64 bot64 arr64 prod64 sum) (B Ty64 nat64 top64 bot64 arr64 prod64 sum).

Definition sum64 : Ty64 → Ty64 → Ty64
 := λ A B Ty64 nat64 top64 bot64 arr64 prod64 sum64 ,
     sum64 (A Ty64 nat64 top64 bot64 arr64 prod64 sum64) (B Ty64 nat64 top64 bot64 arr64 prod64 sum64).

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
     (tt    : ∀ Γ       , Tm64 Γ top64)
     (pair  : ∀ Γ A B   , Tm64 Γ A → Tm64 Γ B → Tm64 Γ (prod64 A B))
     (fst   : ∀ Γ A B   , Tm64 Γ (prod64 A B) → Tm64 Γ A)
     (snd   : ∀ Γ A B   , Tm64 Γ (prod64 A B) → Tm64 Γ B)
     (left  : ∀ Γ A B   , Tm64 Γ A → Tm64 Γ (sum64 A B))
     (right : ∀ Γ A B   , Tm64 Γ B → Tm64 Γ (sum64 A B))
     (case  : ∀ Γ A B C , Tm64 Γ (sum64 A B) → Tm64 Γ (arr64 A C) → Tm64 Γ (arr64 B C) → Tm64 Γ C)
     (zero  : ∀ Γ       , Tm64 Γ nat64)
     (suc   : ∀ Γ       , Tm64 Γ nat64 → Tm64 Γ nat64)
     (rec   : ∀ Γ A     , Tm64 Γ nat64 → Tm64 Γ (arr64 nat64 (arr64 A A)) → Tm64 Γ A → Tm64 Γ A)
   , Tm64 Γ A.

Definition var64 {Γ A} : Var64 Γ A → Tm64 Γ A
 := λ x Tm64 var64 lam app tt pair fst snd left right case zero suc rec ,
     var64 _ _ x.

Definition lam64 {Γ A B} : Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B)
 := λ t Tm64 var64 lam64 app tt pair fst snd left right case zero suc rec ,
     lam64 _ _ _ (t Tm64 var64 lam64 app tt pair fst snd left right case zero suc rec).

Definition app64 {Γ A B} : Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B
 := λ t u Tm64 var64 lam64 app64 tt pair fst snd left right case zero suc rec ,
     app64 _ _ _
         (t Tm64 var64 lam64 app64 tt pair fst snd left right case zero suc rec)
         (u Tm64 var64 lam64 app64 tt pair fst snd left right case zero suc rec).

Definition tt64 {Γ} : Tm64 Γ top64
 := λ Tm64 var64 lam64 app64 tt64 pair fst snd left right case zero suc rec , tt64 _.

Definition pair64 {Γ A B} : Tm64 Γ A → Tm64 Γ B → Tm64 Γ (prod64 A B)
 := λ t u Tm64 var64 lam64 app64 tt64 pair64 fst snd left right case zero suc rec ,
     pair64 _ _ _
          (t Tm64 var64 lam64 app64 tt64 pair64 fst snd left right case zero suc rec)
          (u Tm64 var64 lam64 app64 tt64 pair64 fst snd left right case zero suc rec).

Definition fst64 {Γ A B} : Tm64 Γ (prod64 A B) → Tm64 Γ A
 := λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd left right case zero suc rec ,
     fst64 _ _ _
         (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd left right case zero suc rec).

Definition snd64 {Γ A B} : Tm64 Γ (prod64 A B) → Tm64 Γ B
 := λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left right case zero suc rec ,
     snd64 _ _ _
          (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left right case zero suc rec).

Definition left64 {Γ A B} : Tm64 Γ A → Tm64 Γ (sum64 A B)
 := λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right case zero suc rec ,
     left64 _ _ _
          (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right case zero suc rec).

Definition right64 {Γ A B} : Tm64 Γ B → Tm64 Γ (sum64 A B)
 := λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case zero suc rec ,
     right64 _ _ _
            (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case zero suc rec).

Definition case64 {Γ A B C} : Tm64 Γ (sum64 A B) → Tm64 Γ (arr64 A C) → Tm64 Γ (arr64 B C) → Tm64 Γ C
 := λ t u v Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero suc rec ,
     case64 _ _ _ _
           (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero suc rec)
           (u Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero suc rec)
           (v Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero suc rec).

Definition zero64  {Γ} : Tm64 Γ nat64
 := λ Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc rec , zero64 _.

Definition suc64 {Γ} : Tm64 Γ nat64 → Tm64 Γ nat64
 := λ t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec ,
   suc64 _ (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec).

Definition rec64 {Γ A} : Tm64 Γ nat64 → Tm64 Γ (arr64 nat64 (arr64 A A)) → Tm64 Γ A → Tm64 Γ A
 := λ t u v Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec64 ,
     rec64 _ _
         (t Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec64)
         (u Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec64)
         (v Tm64 var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 case64 zero64 suc64 rec64).

Definition v064 {Γ A} : Tm64 (snoc64 Γ A) A
 := var64 vz64.

Definition v164 {Γ A B} : Tm64 (snoc64 (snoc64 Γ A) B) A
 := var64 (vs64 vz64).

Definition v264 {Γ A B C} : Tm64 (snoc64 (snoc64 (snoc64 Γ A) B) C) A
 := var64 (vs64 (vs64 vz64)).

Definition v364 {Γ A B C D} : Tm64 (snoc64 (snoc64 (snoc64 (snoc64 Γ A) B) C) D) A
 := var64 (vs64 (vs64 (vs64 vz64))).

Definition tbool64 : Ty64
 := sum64 top64 top64.

Definition ttrue64 {Γ} : Tm64 Γ tbool64
 := left64 tt64.

Definition tfalse64 {Γ} : Tm64 Γ tbool64
 := right64 tt64.

Definition ifthenelse64 {Γ A} : Tm64 Γ (arr64 tbool64 (arr64 A (arr64 A A)))
 := lam64 (lam64 (lam64 (case64 v264 (lam64 v264) (lam64 v164)))).

Definition times464 {Γ A} : Tm64 Γ (arr64 (arr64 A A) (arr64 A A))
  := lam64 (lam64 (app64 v164 (app64 v164 (app64 v164 (app64 v164 v064))))).

Definition add64 {Γ} : Tm64 Γ (arr64 nat64 (arr64 nat64 nat64))
 := lam64 (rec64 v064
      (lam64 (lam64 (lam64 (suc64 (app64 v164 v064)))))
      (lam64 v064)).

Definition mul64 {Γ} : Tm64 Γ (arr64 nat64 (arr64 nat64 nat64))
 := lam64 (rec64 v064
     (lam64 (lam64 (lam64 (app64 (app64 add64 (app64 v164 v064)) v064))))
     (lam64 zero64)).

Definition fact64 {Γ} : Tm64 Γ (arr64 nat64 nat64)
 := lam64 (rec64 v064 (lam64 (lam64 (app64 (app64 mul64 (suc64 v164)) v064)))
        (suc64 zero64)).

Require Import Coq.Unicode.Utf8.

Definition Ty65 : Set
 := ∀ (Ty65           : Set)
      (nat top bot  : Ty65)
      (arr prod sum : Ty65 → Ty65 → Ty65)
    , Ty65.

Definition nat65 : Ty65 := λ _ nat65 _ _ _ _ _ , nat65.
Definition top65 : Ty65 := λ _ _ top65 _ _ _ _ , top65.
Definition bot65 : Ty65 := λ _ _ _ bot65 _ _ _ , bot65.

Definition arr65 : Ty65 → Ty65 → Ty65
 := λ A B Ty65 nat65 top65 bot65 arr65 prod sum ,
     arr65 (A Ty65 nat65 top65 bot65 arr65 prod sum) (B Ty65 nat65 top65 bot65 arr65 prod sum).

Definition prod65 : Ty65 → Ty65 → Ty65
 := λ A B Ty65 nat65 top65 bot65 arr65 prod65 sum ,
     prod65 (A Ty65 nat65 top65 bot65 arr65 prod65 sum) (B Ty65 nat65 top65 bot65 arr65 prod65 sum).

Definition sum65 : Ty65 → Ty65 → Ty65
 := λ A B Ty65 nat65 top65 bot65 arr65 prod65 sum65 ,
     sum65 (A Ty65 nat65 top65 bot65 arr65 prod65 sum65) (B Ty65 nat65 top65 bot65 arr65 prod65 sum65).

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
     (tt    : ∀ Γ       , Tm65 Γ top65)
     (pair  : ∀ Γ A B   , Tm65 Γ A → Tm65 Γ B → Tm65 Γ (prod65 A B))
     (fst   : ∀ Γ A B   , Tm65 Γ (prod65 A B) → Tm65 Γ A)
     (snd   : ∀ Γ A B   , Tm65 Γ (prod65 A B) → Tm65 Γ B)
     (left  : ∀ Γ A B   , Tm65 Γ A → Tm65 Γ (sum65 A B))
     (right : ∀ Γ A B   , Tm65 Γ B → Tm65 Γ (sum65 A B))
     (case  : ∀ Γ A B C , Tm65 Γ (sum65 A B) → Tm65 Γ (arr65 A C) → Tm65 Γ (arr65 B C) → Tm65 Γ C)
     (zero  : ∀ Γ       , Tm65 Γ nat65)
     (suc   : ∀ Γ       , Tm65 Γ nat65 → Tm65 Γ nat65)
     (rec   : ∀ Γ A     , Tm65 Γ nat65 → Tm65 Γ (arr65 nat65 (arr65 A A)) → Tm65 Γ A → Tm65 Γ A)
   , Tm65 Γ A.

Definition var65 {Γ A} : Var65 Γ A → Tm65 Γ A
 := λ x Tm65 var65 lam app tt pair fst snd left right case zero suc rec ,
     var65 _ _ x.

Definition lam65 {Γ A B} : Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B)
 := λ t Tm65 var65 lam65 app tt pair fst snd left right case zero suc rec ,
     lam65 _ _ _ (t Tm65 var65 lam65 app tt pair fst snd left right case zero suc rec).

Definition app65 {Γ A B} : Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B
 := λ t u Tm65 var65 lam65 app65 tt pair fst snd left right case zero suc rec ,
     app65 _ _ _
         (t Tm65 var65 lam65 app65 tt pair fst snd left right case zero suc rec)
         (u Tm65 var65 lam65 app65 tt pair fst snd left right case zero suc rec).

Definition tt65 {Γ} : Tm65 Γ top65
 := λ Tm65 var65 lam65 app65 tt65 pair fst snd left right case zero suc rec , tt65 _.

Definition pair65 {Γ A B} : Tm65 Γ A → Tm65 Γ B → Tm65 Γ (prod65 A B)
 := λ t u Tm65 var65 lam65 app65 tt65 pair65 fst snd left right case zero suc rec ,
     pair65 _ _ _
          (t Tm65 var65 lam65 app65 tt65 pair65 fst snd left right case zero suc rec)
          (u Tm65 var65 lam65 app65 tt65 pair65 fst snd left right case zero suc rec).

Definition fst65 {Γ A B} : Tm65 Γ (prod65 A B) → Tm65 Γ A
 := λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd left right case zero suc rec ,
     fst65 _ _ _
         (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd left right case zero suc rec).

Definition snd65 {Γ A B} : Tm65 Γ (prod65 A B) → Tm65 Γ B
 := λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left right case zero suc rec ,
     snd65 _ _ _
          (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left right case zero suc rec).

Definition left65 {Γ A B} : Tm65 Γ A → Tm65 Γ (sum65 A B)
 := λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right case zero suc rec ,
     left65 _ _ _
          (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right case zero suc rec).

Definition right65 {Γ A B} : Tm65 Γ B → Tm65 Γ (sum65 A B)
 := λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case zero suc rec ,
     right65 _ _ _
            (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case zero suc rec).

Definition case65 {Γ A B C} : Tm65 Γ (sum65 A B) → Tm65 Γ (arr65 A C) → Tm65 Γ (arr65 B C) → Tm65 Γ C
 := λ t u v Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero suc rec ,
     case65 _ _ _ _
           (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero suc rec)
           (u Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero suc rec)
           (v Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero suc rec).

Definition zero65  {Γ} : Tm65 Γ nat65
 := λ Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc rec , zero65 _.

Definition suc65 {Γ} : Tm65 Γ nat65 → Tm65 Γ nat65
 := λ t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec ,
   suc65 _ (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec).

Definition rec65 {Γ A} : Tm65 Γ nat65 → Tm65 Γ (arr65 nat65 (arr65 A A)) → Tm65 Γ A → Tm65 Γ A
 := λ t u v Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec65 ,
     rec65 _ _
         (t Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec65)
         (u Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec65)
         (v Tm65 var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 case65 zero65 suc65 rec65).

Definition v065 {Γ A} : Tm65 (snoc65 Γ A) A
 := var65 vz65.

Definition v165 {Γ A B} : Tm65 (snoc65 (snoc65 Γ A) B) A
 := var65 (vs65 vz65).

Definition v265 {Γ A B C} : Tm65 (snoc65 (snoc65 (snoc65 Γ A) B) C) A
 := var65 (vs65 (vs65 vz65)).

Definition v365 {Γ A B C D} : Tm65 (snoc65 (snoc65 (snoc65 (snoc65 Γ A) B) C) D) A
 := var65 (vs65 (vs65 (vs65 vz65))).

Definition tbool65 : Ty65
 := sum65 top65 top65.

Definition ttrue65 {Γ} : Tm65 Γ tbool65
 := left65 tt65.

Definition tfalse65 {Γ} : Tm65 Γ tbool65
 := right65 tt65.

Definition ifthenelse65 {Γ A} : Tm65 Γ (arr65 tbool65 (arr65 A (arr65 A A)))
 := lam65 (lam65 (lam65 (case65 v265 (lam65 v265) (lam65 v165)))).

Definition times465 {Γ A} : Tm65 Γ (arr65 (arr65 A A) (arr65 A A))
  := lam65 (lam65 (app65 v165 (app65 v165 (app65 v165 (app65 v165 v065))))).

Definition add65 {Γ} : Tm65 Γ (arr65 nat65 (arr65 nat65 nat65))
 := lam65 (rec65 v065
      (lam65 (lam65 (lam65 (suc65 (app65 v165 v065)))))
      (lam65 v065)).

Definition mul65 {Γ} : Tm65 Γ (arr65 nat65 (arr65 nat65 nat65))
 := lam65 (rec65 v065
     (lam65 (lam65 (lam65 (app65 (app65 add65 (app65 v165 v065)) v065))))
     (lam65 zero65)).

Definition fact65 {Γ} : Tm65 Γ (arr65 nat65 nat65)
 := lam65 (rec65 v065 (lam65 (lam65 (app65 (app65 mul65 (suc65 v165)) v065)))
        (suc65 zero65)).

Require Import Coq.Unicode.Utf8.

Definition Ty66 : Set
 := ∀ (Ty66           : Set)
      (nat top bot  : Ty66)
      (arr prod sum : Ty66 → Ty66 → Ty66)
    , Ty66.

Definition nat66 : Ty66 := λ _ nat66 _ _ _ _ _ , nat66.
Definition top66 : Ty66 := λ _ _ top66 _ _ _ _ , top66.
Definition bot66 : Ty66 := λ _ _ _ bot66 _ _ _ , bot66.

Definition arr66 : Ty66 → Ty66 → Ty66
 := λ A B Ty66 nat66 top66 bot66 arr66 prod sum ,
     arr66 (A Ty66 nat66 top66 bot66 arr66 prod sum) (B Ty66 nat66 top66 bot66 arr66 prod sum).

Definition prod66 : Ty66 → Ty66 → Ty66
 := λ A B Ty66 nat66 top66 bot66 arr66 prod66 sum ,
     prod66 (A Ty66 nat66 top66 bot66 arr66 prod66 sum) (B Ty66 nat66 top66 bot66 arr66 prod66 sum).

Definition sum66 : Ty66 → Ty66 → Ty66
 := λ A B Ty66 nat66 top66 bot66 arr66 prod66 sum66 ,
     sum66 (A Ty66 nat66 top66 bot66 arr66 prod66 sum66) (B Ty66 nat66 top66 bot66 arr66 prod66 sum66).

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
     (tt    : ∀ Γ       , Tm66 Γ top66)
     (pair  : ∀ Γ A B   , Tm66 Γ A → Tm66 Γ B → Tm66 Γ (prod66 A B))
     (fst   : ∀ Γ A B   , Tm66 Γ (prod66 A B) → Tm66 Γ A)
     (snd   : ∀ Γ A B   , Tm66 Γ (prod66 A B) → Tm66 Γ B)
     (left  : ∀ Γ A B   , Tm66 Γ A → Tm66 Γ (sum66 A B))
     (right : ∀ Γ A B   , Tm66 Γ B → Tm66 Γ (sum66 A B))
     (case  : ∀ Γ A B C , Tm66 Γ (sum66 A B) → Tm66 Γ (arr66 A C) → Tm66 Γ (arr66 B C) → Tm66 Γ C)
     (zero  : ∀ Γ       , Tm66 Γ nat66)
     (suc   : ∀ Γ       , Tm66 Γ nat66 → Tm66 Γ nat66)
     (rec   : ∀ Γ A     , Tm66 Γ nat66 → Tm66 Γ (arr66 nat66 (arr66 A A)) → Tm66 Γ A → Tm66 Γ A)
   , Tm66 Γ A.

Definition var66 {Γ A} : Var66 Γ A → Tm66 Γ A
 := λ x Tm66 var66 lam app tt pair fst snd left right case zero suc rec ,
     var66 _ _ x.

Definition lam66 {Γ A B} : Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B)
 := λ t Tm66 var66 lam66 app tt pair fst snd left right case zero suc rec ,
     lam66 _ _ _ (t Tm66 var66 lam66 app tt pair fst snd left right case zero suc rec).

Definition app66 {Γ A B} : Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B
 := λ t u Tm66 var66 lam66 app66 tt pair fst snd left right case zero suc rec ,
     app66 _ _ _
         (t Tm66 var66 lam66 app66 tt pair fst snd left right case zero suc rec)
         (u Tm66 var66 lam66 app66 tt pair fst snd left right case zero suc rec).

Definition tt66 {Γ} : Tm66 Γ top66
 := λ Tm66 var66 lam66 app66 tt66 pair fst snd left right case zero suc rec , tt66 _.

Definition pair66 {Γ A B} : Tm66 Γ A → Tm66 Γ B → Tm66 Γ (prod66 A B)
 := λ t u Tm66 var66 lam66 app66 tt66 pair66 fst snd left right case zero suc rec ,
     pair66 _ _ _
          (t Tm66 var66 lam66 app66 tt66 pair66 fst snd left right case zero suc rec)
          (u Tm66 var66 lam66 app66 tt66 pair66 fst snd left right case zero suc rec).

Definition fst66 {Γ A B} : Tm66 Γ (prod66 A B) → Tm66 Γ A
 := λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd left right case zero suc rec ,
     fst66 _ _ _
         (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd left right case zero suc rec).

Definition snd66 {Γ A B} : Tm66 Γ (prod66 A B) → Tm66 Γ B
 := λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left right case zero suc rec ,
     snd66 _ _ _
          (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left right case zero suc rec).

Definition left66 {Γ A B} : Tm66 Γ A → Tm66 Γ (sum66 A B)
 := λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right case zero suc rec ,
     left66 _ _ _
          (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right case zero suc rec).

Definition right66 {Γ A B} : Tm66 Γ B → Tm66 Γ (sum66 A B)
 := λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case zero suc rec ,
     right66 _ _ _
            (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case zero suc rec).

Definition case66 {Γ A B C} : Tm66 Γ (sum66 A B) → Tm66 Γ (arr66 A C) → Tm66 Γ (arr66 B C) → Tm66 Γ C
 := λ t u v Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero suc rec ,
     case66 _ _ _ _
           (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero suc rec)
           (u Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero suc rec)
           (v Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero suc rec).

Definition zero66  {Γ} : Tm66 Γ nat66
 := λ Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc rec , zero66 _.

Definition suc66 {Γ} : Tm66 Γ nat66 → Tm66 Γ nat66
 := λ t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec ,
   suc66 _ (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec).

Definition rec66 {Γ A} : Tm66 Γ nat66 → Tm66 Γ (arr66 nat66 (arr66 A A)) → Tm66 Γ A → Tm66 Γ A
 := λ t u v Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec66 ,
     rec66 _ _
         (t Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec66)
         (u Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec66)
         (v Tm66 var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 case66 zero66 suc66 rec66).

Definition v066 {Γ A} : Tm66 (snoc66 Γ A) A
 := var66 vz66.

Definition v166 {Γ A B} : Tm66 (snoc66 (snoc66 Γ A) B) A
 := var66 (vs66 vz66).

Definition v266 {Γ A B C} : Tm66 (snoc66 (snoc66 (snoc66 Γ A) B) C) A
 := var66 (vs66 (vs66 vz66)).

Definition v366 {Γ A B C D} : Tm66 (snoc66 (snoc66 (snoc66 (snoc66 Γ A) B) C) D) A
 := var66 (vs66 (vs66 (vs66 vz66))).

Definition tbool66 : Ty66
 := sum66 top66 top66.

Definition ttrue66 {Γ} : Tm66 Γ tbool66
 := left66 tt66.

Definition tfalse66 {Γ} : Tm66 Γ tbool66
 := right66 tt66.

Definition ifthenelse66 {Γ A} : Tm66 Γ (arr66 tbool66 (arr66 A (arr66 A A)))
 := lam66 (lam66 (lam66 (case66 v266 (lam66 v266) (lam66 v166)))).

Definition times466 {Γ A} : Tm66 Γ (arr66 (arr66 A A) (arr66 A A))
  := lam66 (lam66 (app66 v166 (app66 v166 (app66 v166 (app66 v166 v066))))).

Definition add66 {Γ} : Tm66 Γ (arr66 nat66 (arr66 nat66 nat66))
 := lam66 (rec66 v066
      (lam66 (lam66 (lam66 (suc66 (app66 v166 v066)))))
      (lam66 v066)).

Definition mul66 {Γ} : Tm66 Γ (arr66 nat66 (arr66 nat66 nat66))
 := lam66 (rec66 v066
     (lam66 (lam66 (lam66 (app66 (app66 add66 (app66 v166 v066)) v066))))
     (lam66 zero66)).

Definition fact66 {Γ} : Tm66 Γ (arr66 nat66 nat66)
 := lam66 (rec66 v066 (lam66 (lam66 (app66 (app66 mul66 (suc66 v166)) v066)))
        (suc66 zero66)).

Require Import Coq.Unicode.Utf8.

Definition Ty67 : Set
 := ∀ (Ty67           : Set)
      (nat top bot  : Ty67)
      (arr prod sum : Ty67 → Ty67 → Ty67)
    , Ty67.

Definition nat67 : Ty67 := λ _ nat67 _ _ _ _ _ , nat67.
Definition top67 : Ty67 := λ _ _ top67 _ _ _ _ , top67.
Definition bot67 : Ty67 := λ _ _ _ bot67 _ _ _ , bot67.

Definition arr67 : Ty67 → Ty67 → Ty67
 := λ A B Ty67 nat67 top67 bot67 arr67 prod sum ,
     arr67 (A Ty67 nat67 top67 bot67 arr67 prod sum) (B Ty67 nat67 top67 bot67 arr67 prod sum).

Definition prod67 : Ty67 → Ty67 → Ty67
 := λ A B Ty67 nat67 top67 bot67 arr67 prod67 sum ,
     prod67 (A Ty67 nat67 top67 bot67 arr67 prod67 sum) (B Ty67 nat67 top67 bot67 arr67 prod67 sum).

Definition sum67 : Ty67 → Ty67 → Ty67
 := λ A B Ty67 nat67 top67 bot67 arr67 prod67 sum67 ,
     sum67 (A Ty67 nat67 top67 bot67 arr67 prod67 sum67) (B Ty67 nat67 top67 bot67 arr67 prod67 sum67).

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
     (tt    : ∀ Γ       , Tm67 Γ top67)
     (pair  : ∀ Γ A B   , Tm67 Γ A → Tm67 Γ B → Tm67 Γ (prod67 A B))
     (fst   : ∀ Γ A B   , Tm67 Γ (prod67 A B) → Tm67 Γ A)
     (snd   : ∀ Γ A B   , Tm67 Γ (prod67 A B) → Tm67 Γ B)
     (left  : ∀ Γ A B   , Tm67 Γ A → Tm67 Γ (sum67 A B))
     (right : ∀ Γ A B   , Tm67 Γ B → Tm67 Γ (sum67 A B))
     (case  : ∀ Γ A B C , Tm67 Γ (sum67 A B) → Tm67 Γ (arr67 A C) → Tm67 Γ (arr67 B C) → Tm67 Γ C)
     (zero  : ∀ Γ       , Tm67 Γ nat67)
     (suc   : ∀ Γ       , Tm67 Γ nat67 → Tm67 Γ nat67)
     (rec   : ∀ Γ A     , Tm67 Γ nat67 → Tm67 Γ (arr67 nat67 (arr67 A A)) → Tm67 Γ A → Tm67 Γ A)
   , Tm67 Γ A.

Definition var67 {Γ A} : Var67 Γ A → Tm67 Γ A
 := λ x Tm67 var67 lam app tt pair fst snd left right case zero suc rec ,
     var67 _ _ x.

Definition lam67 {Γ A B} : Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B)
 := λ t Tm67 var67 lam67 app tt pair fst snd left right case zero suc rec ,
     lam67 _ _ _ (t Tm67 var67 lam67 app tt pair fst snd left right case zero suc rec).

Definition app67 {Γ A B} : Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B
 := λ t u Tm67 var67 lam67 app67 tt pair fst snd left right case zero suc rec ,
     app67 _ _ _
         (t Tm67 var67 lam67 app67 tt pair fst snd left right case zero suc rec)
         (u Tm67 var67 lam67 app67 tt pair fst snd left right case zero suc rec).

Definition tt67 {Γ} : Tm67 Γ top67
 := λ Tm67 var67 lam67 app67 tt67 pair fst snd left right case zero suc rec , tt67 _.

Definition pair67 {Γ A B} : Tm67 Γ A → Tm67 Γ B → Tm67 Γ (prod67 A B)
 := λ t u Tm67 var67 lam67 app67 tt67 pair67 fst snd left right case zero suc rec ,
     pair67 _ _ _
          (t Tm67 var67 lam67 app67 tt67 pair67 fst snd left right case zero suc rec)
          (u Tm67 var67 lam67 app67 tt67 pair67 fst snd left right case zero suc rec).

Definition fst67 {Γ A B} : Tm67 Γ (prod67 A B) → Tm67 Γ A
 := λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd left right case zero suc rec ,
     fst67 _ _ _
         (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd left right case zero suc rec).

Definition snd67 {Γ A B} : Tm67 Γ (prod67 A B) → Tm67 Γ B
 := λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left right case zero suc rec ,
     snd67 _ _ _
          (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left right case zero suc rec).

Definition left67 {Γ A B} : Tm67 Γ A → Tm67 Γ (sum67 A B)
 := λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right case zero suc rec ,
     left67 _ _ _
          (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right case zero suc rec).

Definition right67 {Γ A B} : Tm67 Γ B → Tm67 Γ (sum67 A B)
 := λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case zero suc rec ,
     right67 _ _ _
            (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case zero suc rec).

Definition case67 {Γ A B C} : Tm67 Γ (sum67 A B) → Tm67 Γ (arr67 A C) → Tm67 Γ (arr67 B C) → Tm67 Γ C
 := λ t u v Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero suc rec ,
     case67 _ _ _ _
           (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero suc rec)
           (u Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero suc rec)
           (v Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero suc rec).

Definition zero67  {Γ} : Tm67 Γ nat67
 := λ Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc rec , zero67 _.

Definition suc67 {Γ} : Tm67 Γ nat67 → Tm67 Γ nat67
 := λ t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec ,
   suc67 _ (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec).

Definition rec67 {Γ A} : Tm67 Γ nat67 → Tm67 Γ (arr67 nat67 (arr67 A A)) → Tm67 Γ A → Tm67 Γ A
 := λ t u v Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec67 ,
     rec67 _ _
         (t Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec67)
         (u Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec67)
         (v Tm67 var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 case67 zero67 suc67 rec67).

Definition v067 {Γ A} : Tm67 (snoc67 Γ A) A
 := var67 vz67.

Definition v167 {Γ A B} : Tm67 (snoc67 (snoc67 Γ A) B) A
 := var67 (vs67 vz67).

Definition v267 {Γ A B C} : Tm67 (snoc67 (snoc67 (snoc67 Γ A) B) C) A
 := var67 (vs67 (vs67 vz67)).

Definition v367 {Γ A B C D} : Tm67 (snoc67 (snoc67 (snoc67 (snoc67 Γ A) B) C) D) A
 := var67 (vs67 (vs67 (vs67 vz67))).

Definition tbool67 : Ty67
 := sum67 top67 top67.

Definition ttrue67 {Γ} : Tm67 Γ tbool67
 := left67 tt67.

Definition tfalse67 {Γ} : Tm67 Γ tbool67
 := right67 tt67.

Definition ifthenelse67 {Γ A} : Tm67 Γ (arr67 tbool67 (arr67 A (arr67 A A)))
 := lam67 (lam67 (lam67 (case67 v267 (lam67 v267) (lam67 v167)))).

Definition times467 {Γ A} : Tm67 Γ (arr67 (arr67 A A) (arr67 A A))
  := lam67 (lam67 (app67 v167 (app67 v167 (app67 v167 (app67 v167 v067))))).

Definition add67 {Γ} : Tm67 Γ (arr67 nat67 (arr67 nat67 nat67))
 := lam67 (rec67 v067
      (lam67 (lam67 (lam67 (suc67 (app67 v167 v067)))))
      (lam67 v067)).

Definition mul67 {Γ} : Tm67 Γ (arr67 nat67 (arr67 nat67 nat67))
 := lam67 (rec67 v067
     (lam67 (lam67 (lam67 (app67 (app67 add67 (app67 v167 v067)) v067))))
     (lam67 zero67)).

Definition fact67 {Γ} : Tm67 Γ (arr67 nat67 nat67)
 := lam67 (rec67 v067 (lam67 (lam67 (app67 (app67 mul67 (suc67 v167)) v067)))
        (suc67 zero67)).

Require Import Coq.Unicode.Utf8.

Definition Ty68 : Set
 := ∀ (Ty68           : Set)
      (nat top bot  : Ty68)
      (arr prod sum : Ty68 → Ty68 → Ty68)
    , Ty68.

Definition nat68 : Ty68 := λ _ nat68 _ _ _ _ _ , nat68.
Definition top68 : Ty68 := λ _ _ top68 _ _ _ _ , top68.
Definition bot68 : Ty68 := λ _ _ _ bot68 _ _ _ , bot68.

Definition arr68 : Ty68 → Ty68 → Ty68
 := λ A B Ty68 nat68 top68 bot68 arr68 prod sum ,
     arr68 (A Ty68 nat68 top68 bot68 arr68 prod sum) (B Ty68 nat68 top68 bot68 arr68 prod sum).

Definition prod68 : Ty68 → Ty68 → Ty68
 := λ A B Ty68 nat68 top68 bot68 arr68 prod68 sum ,
     prod68 (A Ty68 nat68 top68 bot68 arr68 prod68 sum) (B Ty68 nat68 top68 bot68 arr68 prod68 sum).

Definition sum68 : Ty68 → Ty68 → Ty68
 := λ A B Ty68 nat68 top68 bot68 arr68 prod68 sum68 ,
     sum68 (A Ty68 nat68 top68 bot68 arr68 prod68 sum68) (B Ty68 nat68 top68 bot68 arr68 prod68 sum68).

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
     (tt    : ∀ Γ       , Tm68 Γ top68)
     (pair  : ∀ Γ A B   , Tm68 Γ A → Tm68 Γ B → Tm68 Γ (prod68 A B))
     (fst   : ∀ Γ A B   , Tm68 Γ (prod68 A B) → Tm68 Γ A)
     (snd   : ∀ Γ A B   , Tm68 Γ (prod68 A B) → Tm68 Γ B)
     (left  : ∀ Γ A B   , Tm68 Γ A → Tm68 Γ (sum68 A B))
     (right : ∀ Γ A B   , Tm68 Γ B → Tm68 Γ (sum68 A B))
     (case  : ∀ Γ A B C , Tm68 Γ (sum68 A B) → Tm68 Γ (arr68 A C) → Tm68 Γ (arr68 B C) → Tm68 Γ C)
     (zero  : ∀ Γ       , Tm68 Γ nat68)
     (suc   : ∀ Γ       , Tm68 Γ nat68 → Tm68 Γ nat68)
     (rec   : ∀ Γ A     , Tm68 Γ nat68 → Tm68 Γ (arr68 nat68 (arr68 A A)) → Tm68 Γ A → Tm68 Γ A)
   , Tm68 Γ A.

Definition var68 {Γ A} : Var68 Γ A → Tm68 Γ A
 := λ x Tm68 var68 lam app tt pair fst snd left right case zero suc rec ,
     var68 _ _ x.

Definition lam68 {Γ A B} : Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B)
 := λ t Tm68 var68 lam68 app tt pair fst snd left right case zero suc rec ,
     lam68 _ _ _ (t Tm68 var68 lam68 app tt pair fst snd left right case zero suc rec).

Definition app68 {Γ A B} : Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B
 := λ t u Tm68 var68 lam68 app68 tt pair fst snd left right case zero suc rec ,
     app68 _ _ _
         (t Tm68 var68 lam68 app68 tt pair fst snd left right case zero suc rec)
         (u Tm68 var68 lam68 app68 tt pair fst snd left right case zero suc rec).

Definition tt68 {Γ} : Tm68 Γ top68
 := λ Tm68 var68 lam68 app68 tt68 pair fst snd left right case zero suc rec , tt68 _.

Definition pair68 {Γ A B} : Tm68 Γ A → Tm68 Γ B → Tm68 Γ (prod68 A B)
 := λ t u Tm68 var68 lam68 app68 tt68 pair68 fst snd left right case zero suc rec ,
     pair68 _ _ _
          (t Tm68 var68 lam68 app68 tt68 pair68 fst snd left right case zero suc rec)
          (u Tm68 var68 lam68 app68 tt68 pair68 fst snd left right case zero suc rec).

Definition fst68 {Γ A B} : Tm68 Γ (prod68 A B) → Tm68 Γ A
 := λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd left right case zero suc rec ,
     fst68 _ _ _
         (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd left right case zero suc rec).

Definition snd68 {Γ A B} : Tm68 Γ (prod68 A B) → Tm68 Γ B
 := λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left right case zero suc rec ,
     snd68 _ _ _
          (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left right case zero suc rec).

Definition left68 {Γ A B} : Tm68 Γ A → Tm68 Γ (sum68 A B)
 := λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right case zero suc rec ,
     left68 _ _ _
          (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right case zero suc rec).

Definition right68 {Γ A B} : Tm68 Γ B → Tm68 Γ (sum68 A B)
 := λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case zero suc rec ,
     right68 _ _ _
            (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case zero suc rec).

Definition case68 {Γ A B C} : Tm68 Γ (sum68 A B) → Tm68 Γ (arr68 A C) → Tm68 Γ (arr68 B C) → Tm68 Γ C
 := λ t u v Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero suc rec ,
     case68 _ _ _ _
           (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero suc rec)
           (u Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero suc rec)
           (v Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero suc rec).

Definition zero68  {Γ} : Tm68 Γ nat68
 := λ Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc rec , zero68 _.

Definition suc68 {Γ} : Tm68 Γ nat68 → Tm68 Γ nat68
 := λ t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec ,
   suc68 _ (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec).

Definition rec68 {Γ A} : Tm68 Γ nat68 → Tm68 Γ (arr68 nat68 (arr68 A A)) → Tm68 Γ A → Tm68 Γ A
 := λ t u v Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec68 ,
     rec68 _ _
         (t Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec68)
         (u Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec68)
         (v Tm68 var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 case68 zero68 suc68 rec68).

Definition v068 {Γ A} : Tm68 (snoc68 Γ A) A
 := var68 vz68.

Definition v168 {Γ A B} : Tm68 (snoc68 (snoc68 Γ A) B) A
 := var68 (vs68 vz68).

Definition v268 {Γ A B C} : Tm68 (snoc68 (snoc68 (snoc68 Γ A) B) C) A
 := var68 (vs68 (vs68 vz68)).

Definition v368 {Γ A B C D} : Tm68 (snoc68 (snoc68 (snoc68 (snoc68 Γ A) B) C) D) A
 := var68 (vs68 (vs68 (vs68 vz68))).

Definition tbool68 : Ty68
 := sum68 top68 top68.

Definition ttrue68 {Γ} : Tm68 Γ tbool68
 := left68 tt68.

Definition tfalse68 {Γ} : Tm68 Γ tbool68
 := right68 tt68.

Definition ifthenelse68 {Γ A} : Tm68 Γ (arr68 tbool68 (arr68 A (arr68 A A)))
 := lam68 (lam68 (lam68 (case68 v268 (lam68 v268) (lam68 v168)))).

Definition times468 {Γ A} : Tm68 Γ (arr68 (arr68 A A) (arr68 A A))
  := lam68 (lam68 (app68 v168 (app68 v168 (app68 v168 (app68 v168 v068))))).

Definition add68 {Γ} : Tm68 Γ (arr68 nat68 (arr68 nat68 nat68))
 := lam68 (rec68 v068
      (lam68 (lam68 (lam68 (suc68 (app68 v168 v068)))))
      (lam68 v068)).

Definition mul68 {Γ} : Tm68 Γ (arr68 nat68 (arr68 nat68 nat68))
 := lam68 (rec68 v068
     (lam68 (lam68 (lam68 (app68 (app68 add68 (app68 v168 v068)) v068))))
     (lam68 zero68)).

Definition fact68 {Γ} : Tm68 Γ (arr68 nat68 nat68)
 := lam68 (rec68 v068 (lam68 (lam68 (app68 (app68 mul68 (suc68 v168)) v068)))
        (suc68 zero68)).

Require Import Coq.Unicode.Utf8.

Definition Ty69 : Set
 := ∀ (Ty69           : Set)
      (nat top bot  : Ty69)
      (arr prod sum : Ty69 → Ty69 → Ty69)
    , Ty69.

Definition nat69 : Ty69 := λ _ nat69 _ _ _ _ _ , nat69.
Definition top69 : Ty69 := λ _ _ top69 _ _ _ _ , top69.
Definition bot69 : Ty69 := λ _ _ _ bot69 _ _ _ , bot69.

Definition arr69 : Ty69 → Ty69 → Ty69
 := λ A B Ty69 nat69 top69 bot69 arr69 prod sum ,
     arr69 (A Ty69 nat69 top69 bot69 arr69 prod sum) (B Ty69 nat69 top69 bot69 arr69 prod sum).

Definition prod69 : Ty69 → Ty69 → Ty69
 := λ A B Ty69 nat69 top69 bot69 arr69 prod69 sum ,
     prod69 (A Ty69 nat69 top69 bot69 arr69 prod69 sum) (B Ty69 nat69 top69 bot69 arr69 prod69 sum).

Definition sum69 : Ty69 → Ty69 → Ty69
 := λ A B Ty69 nat69 top69 bot69 arr69 prod69 sum69 ,
     sum69 (A Ty69 nat69 top69 bot69 arr69 prod69 sum69) (B Ty69 nat69 top69 bot69 arr69 prod69 sum69).

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
     (tt    : ∀ Γ       , Tm69 Γ top69)
     (pair  : ∀ Γ A B   , Tm69 Γ A → Tm69 Γ B → Tm69 Γ (prod69 A B))
     (fst   : ∀ Γ A B   , Tm69 Γ (prod69 A B) → Tm69 Γ A)
     (snd   : ∀ Γ A B   , Tm69 Γ (prod69 A B) → Tm69 Γ B)
     (left  : ∀ Γ A B   , Tm69 Γ A → Tm69 Γ (sum69 A B))
     (right : ∀ Γ A B   , Tm69 Γ B → Tm69 Γ (sum69 A B))
     (case  : ∀ Γ A B C , Tm69 Γ (sum69 A B) → Tm69 Γ (arr69 A C) → Tm69 Γ (arr69 B C) → Tm69 Γ C)
     (zero  : ∀ Γ       , Tm69 Γ nat69)
     (suc   : ∀ Γ       , Tm69 Γ nat69 → Tm69 Γ nat69)
     (rec   : ∀ Γ A     , Tm69 Γ nat69 → Tm69 Γ (arr69 nat69 (arr69 A A)) → Tm69 Γ A → Tm69 Γ A)
   , Tm69 Γ A.

Definition var69 {Γ A} : Var69 Γ A → Tm69 Γ A
 := λ x Tm69 var69 lam app tt pair fst snd left right case zero suc rec ,
     var69 _ _ x.

Definition lam69 {Γ A B} : Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B)
 := λ t Tm69 var69 lam69 app tt pair fst snd left right case zero suc rec ,
     lam69 _ _ _ (t Tm69 var69 lam69 app tt pair fst snd left right case zero suc rec).

Definition app69 {Γ A B} : Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B
 := λ t u Tm69 var69 lam69 app69 tt pair fst snd left right case zero suc rec ,
     app69 _ _ _
         (t Tm69 var69 lam69 app69 tt pair fst snd left right case zero suc rec)
         (u Tm69 var69 lam69 app69 tt pair fst snd left right case zero suc rec).

Definition tt69 {Γ} : Tm69 Γ top69
 := λ Tm69 var69 lam69 app69 tt69 pair fst snd left right case zero suc rec , tt69 _.

Definition pair69 {Γ A B} : Tm69 Γ A → Tm69 Γ B → Tm69 Γ (prod69 A B)
 := λ t u Tm69 var69 lam69 app69 tt69 pair69 fst snd left right case zero suc rec ,
     pair69 _ _ _
          (t Tm69 var69 lam69 app69 tt69 pair69 fst snd left right case zero suc rec)
          (u Tm69 var69 lam69 app69 tt69 pair69 fst snd left right case zero suc rec).

Definition fst69 {Γ A B} : Tm69 Γ (prod69 A B) → Tm69 Γ A
 := λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd left right case zero suc rec ,
     fst69 _ _ _
         (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd left right case zero suc rec).

Definition snd69 {Γ A B} : Tm69 Γ (prod69 A B) → Tm69 Γ B
 := λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left right case zero suc rec ,
     snd69 _ _ _
          (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left right case zero suc rec).

Definition left69 {Γ A B} : Tm69 Γ A → Tm69 Γ (sum69 A B)
 := λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right case zero suc rec ,
     left69 _ _ _
          (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right case zero suc rec).

Definition right69 {Γ A B} : Tm69 Γ B → Tm69 Γ (sum69 A B)
 := λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case zero suc rec ,
     right69 _ _ _
            (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case zero suc rec).

Definition case69 {Γ A B C} : Tm69 Γ (sum69 A B) → Tm69 Γ (arr69 A C) → Tm69 Γ (arr69 B C) → Tm69 Γ C
 := λ t u v Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero suc rec ,
     case69 _ _ _ _
           (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero suc rec)
           (u Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero suc rec)
           (v Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero suc rec).

Definition zero69  {Γ} : Tm69 Γ nat69
 := λ Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc rec , zero69 _.

Definition suc69 {Γ} : Tm69 Γ nat69 → Tm69 Γ nat69
 := λ t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec ,
   suc69 _ (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec).

Definition rec69 {Γ A} : Tm69 Γ nat69 → Tm69 Γ (arr69 nat69 (arr69 A A)) → Tm69 Γ A → Tm69 Γ A
 := λ t u v Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec69 ,
     rec69 _ _
         (t Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec69)
         (u Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec69)
         (v Tm69 var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 case69 zero69 suc69 rec69).

Definition v069 {Γ A} : Tm69 (snoc69 Γ A) A
 := var69 vz69.

Definition v169 {Γ A B} : Tm69 (snoc69 (snoc69 Γ A) B) A
 := var69 (vs69 vz69).

Definition v269 {Γ A B C} : Tm69 (snoc69 (snoc69 (snoc69 Γ A) B) C) A
 := var69 (vs69 (vs69 vz69)).

Definition v369 {Γ A B C D} : Tm69 (snoc69 (snoc69 (snoc69 (snoc69 Γ A) B) C) D) A
 := var69 (vs69 (vs69 (vs69 vz69))).

Definition tbool69 : Ty69
 := sum69 top69 top69.

Definition ttrue69 {Γ} : Tm69 Γ tbool69
 := left69 tt69.

Definition tfalse69 {Γ} : Tm69 Γ tbool69
 := right69 tt69.

Definition ifthenelse69 {Γ A} : Tm69 Γ (arr69 tbool69 (arr69 A (arr69 A A)))
 := lam69 (lam69 (lam69 (case69 v269 (lam69 v269) (lam69 v169)))).

Definition times469 {Γ A} : Tm69 Γ (arr69 (arr69 A A) (arr69 A A))
  := lam69 (lam69 (app69 v169 (app69 v169 (app69 v169 (app69 v169 v069))))).

Definition add69 {Γ} : Tm69 Γ (arr69 nat69 (arr69 nat69 nat69))
 := lam69 (rec69 v069
      (lam69 (lam69 (lam69 (suc69 (app69 v169 v069)))))
      (lam69 v069)).

Definition mul69 {Γ} : Tm69 Γ (arr69 nat69 (arr69 nat69 nat69))
 := lam69 (rec69 v069
     (lam69 (lam69 (lam69 (app69 (app69 add69 (app69 v169 v069)) v069))))
     (lam69 zero69)).

Definition fact69 {Γ} : Tm69 Γ (arr69 nat69 nat69)
 := lam69 (rec69 v069 (lam69 (lam69 (app69 (app69 mul69 (suc69 v169)) v069)))
        (suc69 zero69)).

Require Import Coq.Unicode.Utf8.

Definition Ty70 : Set
 := ∀ (Ty70           : Set)
      (nat top bot  : Ty70)
      (arr prod sum : Ty70 → Ty70 → Ty70)
    , Ty70.

Definition nat70 : Ty70 := λ _ nat70 _ _ _ _ _ , nat70.
Definition top70 : Ty70 := λ _ _ top70 _ _ _ _ , top70.
Definition bot70 : Ty70 := λ _ _ _ bot70 _ _ _ , bot70.

Definition arr70 : Ty70 → Ty70 → Ty70
 := λ A B Ty70 nat70 top70 bot70 arr70 prod sum ,
     arr70 (A Ty70 nat70 top70 bot70 arr70 prod sum) (B Ty70 nat70 top70 bot70 arr70 prod sum).

Definition prod70 : Ty70 → Ty70 → Ty70
 := λ A B Ty70 nat70 top70 bot70 arr70 prod70 sum ,
     prod70 (A Ty70 nat70 top70 bot70 arr70 prod70 sum) (B Ty70 nat70 top70 bot70 arr70 prod70 sum).

Definition sum70 : Ty70 → Ty70 → Ty70
 := λ A B Ty70 nat70 top70 bot70 arr70 prod70 sum70 ,
     sum70 (A Ty70 nat70 top70 bot70 arr70 prod70 sum70) (B Ty70 nat70 top70 bot70 arr70 prod70 sum70).

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
     (tt    : ∀ Γ       , Tm70 Γ top70)
     (pair  : ∀ Γ A B   , Tm70 Γ A → Tm70 Γ B → Tm70 Γ (prod70 A B))
     (fst   : ∀ Γ A B   , Tm70 Γ (prod70 A B) → Tm70 Γ A)
     (snd   : ∀ Γ A B   , Tm70 Γ (prod70 A B) → Tm70 Γ B)
     (left  : ∀ Γ A B   , Tm70 Γ A → Tm70 Γ (sum70 A B))
     (right : ∀ Γ A B   , Tm70 Γ B → Tm70 Γ (sum70 A B))
     (case  : ∀ Γ A B C , Tm70 Γ (sum70 A B) → Tm70 Γ (arr70 A C) → Tm70 Γ (arr70 B C) → Tm70 Γ C)
     (zero  : ∀ Γ       , Tm70 Γ nat70)
     (suc   : ∀ Γ       , Tm70 Γ nat70 → Tm70 Γ nat70)
     (rec   : ∀ Γ A     , Tm70 Γ nat70 → Tm70 Γ (arr70 nat70 (arr70 A A)) → Tm70 Γ A → Tm70 Γ A)
   , Tm70 Γ A.

Definition var70 {Γ A} : Var70 Γ A → Tm70 Γ A
 := λ x Tm70 var70 lam app tt pair fst snd left right case zero suc rec ,
     var70 _ _ x.

Definition lam70 {Γ A B} : Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B)
 := λ t Tm70 var70 lam70 app tt pair fst snd left right case zero suc rec ,
     lam70 _ _ _ (t Tm70 var70 lam70 app tt pair fst snd left right case zero suc rec).

Definition app70 {Γ A B} : Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B
 := λ t u Tm70 var70 lam70 app70 tt pair fst snd left right case zero suc rec ,
     app70 _ _ _
         (t Tm70 var70 lam70 app70 tt pair fst snd left right case zero suc rec)
         (u Tm70 var70 lam70 app70 tt pair fst snd left right case zero suc rec).

Definition tt70 {Γ} : Tm70 Γ top70
 := λ Tm70 var70 lam70 app70 tt70 pair fst snd left right case zero suc rec , tt70 _.

Definition pair70 {Γ A B} : Tm70 Γ A → Tm70 Γ B → Tm70 Γ (prod70 A B)
 := λ t u Tm70 var70 lam70 app70 tt70 pair70 fst snd left right case zero suc rec ,
     pair70 _ _ _
          (t Tm70 var70 lam70 app70 tt70 pair70 fst snd left right case zero suc rec)
          (u Tm70 var70 lam70 app70 tt70 pair70 fst snd left right case zero suc rec).

Definition fst70 {Γ A B} : Tm70 Γ (prod70 A B) → Tm70 Γ A
 := λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd left right case zero suc rec ,
     fst70 _ _ _
         (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd left right case zero suc rec).

Definition snd70 {Γ A B} : Tm70 Γ (prod70 A B) → Tm70 Γ B
 := λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left right case zero suc rec ,
     snd70 _ _ _
          (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left right case zero suc rec).

Definition left70 {Γ A B} : Tm70 Γ A → Tm70 Γ (sum70 A B)
 := λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right case zero suc rec ,
     left70 _ _ _
          (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right case zero suc rec).

Definition right70 {Γ A B} : Tm70 Γ B → Tm70 Γ (sum70 A B)
 := λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case zero suc rec ,
     right70 _ _ _
            (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case zero suc rec).

Definition case70 {Γ A B C} : Tm70 Γ (sum70 A B) → Tm70 Γ (arr70 A C) → Tm70 Γ (arr70 B C) → Tm70 Γ C
 := λ t u v Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero suc rec ,
     case70 _ _ _ _
           (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero suc rec)
           (u Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero suc rec)
           (v Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero suc rec).

Definition zero70  {Γ} : Tm70 Γ nat70
 := λ Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc rec , zero70 _.

Definition suc70 {Γ} : Tm70 Γ nat70 → Tm70 Γ nat70
 := λ t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec ,
   suc70 _ (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec).

Definition rec70 {Γ A} : Tm70 Γ nat70 → Tm70 Γ (arr70 nat70 (arr70 A A)) → Tm70 Γ A → Tm70 Γ A
 := λ t u v Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec70 ,
     rec70 _ _
         (t Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec70)
         (u Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec70)
         (v Tm70 var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 case70 zero70 suc70 rec70).

Definition v070 {Γ A} : Tm70 (snoc70 Γ A) A
 := var70 vz70.

Definition v170 {Γ A B} : Tm70 (snoc70 (snoc70 Γ A) B) A
 := var70 (vs70 vz70).

Definition v270 {Γ A B C} : Tm70 (snoc70 (snoc70 (snoc70 Γ A) B) C) A
 := var70 (vs70 (vs70 vz70)).

Definition v370 {Γ A B C D} : Tm70 (snoc70 (snoc70 (snoc70 (snoc70 Γ A) B) C) D) A
 := var70 (vs70 (vs70 (vs70 vz70))).

Definition tbool70 : Ty70
 := sum70 top70 top70.

Definition ttrue70 {Γ} : Tm70 Γ tbool70
 := left70 tt70.

Definition tfalse70 {Γ} : Tm70 Γ tbool70
 := right70 tt70.

Definition ifthenelse70 {Γ A} : Tm70 Γ (arr70 tbool70 (arr70 A (arr70 A A)))
 := lam70 (lam70 (lam70 (case70 v270 (lam70 v270) (lam70 v170)))).

Definition times470 {Γ A} : Tm70 Γ (arr70 (arr70 A A) (arr70 A A))
  := lam70 (lam70 (app70 v170 (app70 v170 (app70 v170 (app70 v170 v070))))).

Definition add70 {Γ} : Tm70 Γ (arr70 nat70 (arr70 nat70 nat70))
 := lam70 (rec70 v070
      (lam70 (lam70 (lam70 (suc70 (app70 v170 v070)))))
      (lam70 v070)).

Definition mul70 {Γ} : Tm70 Γ (arr70 nat70 (arr70 nat70 nat70))
 := lam70 (rec70 v070
     (lam70 (lam70 (lam70 (app70 (app70 add70 (app70 v170 v070)) v070))))
     (lam70 zero70)).

Definition fact70 {Γ} : Tm70 Γ (arr70 nat70 nat70)
 := lam70 (rec70 v070 (lam70 (lam70 (app70 (app70 mul70 (suc70 v170)) v070)))
        (suc70 zero70)).

Require Import Coq.Unicode.Utf8.

Definition Ty71 : Set
 := ∀ (Ty71           : Set)
      (nat top bot  : Ty71)
      (arr prod sum : Ty71 → Ty71 → Ty71)
    , Ty71.

Definition nat71 : Ty71 := λ _ nat71 _ _ _ _ _ , nat71.
Definition top71 : Ty71 := λ _ _ top71 _ _ _ _ , top71.
Definition bot71 : Ty71 := λ _ _ _ bot71 _ _ _ , bot71.

Definition arr71 : Ty71 → Ty71 → Ty71
 := λ A B Ty71 nat71 top71 bot71 arr71 prod sum ,
     arr71 (A Ty71 nat71 top71 bot71 arr71 prod sum) (B Ty71 nat71 top71 bot71 arr71 prod sum).

Definition prod71 : Ty71 → Ty71 → Ty71
 := λ A B Ty71 nat71 top71 bot71 arr71 prod71 sum ,
     prod71 (A Ty71 nat71 top71 bot71 arr71 prod71 sum) (B Ty71 nat71 top71 bot71 arr71 prod71 sum).

Definition sum71 : Ty71 → Ty71 → Ty71
 := λ A B Ty71 nat71 top71 bot71 arr71 prod71 sum71 ,
     sum71 (A Ty71 nat71 top71 bot71 arr71 prod71 sum71) (B Ty71 nat71 top71 bot71 arr71 prod71 sum71).

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
     (tt    : ∀ Γ       , Tm71 Γ top71)
     (pair  : ∀ Γ A B   , Tm71 Γ A → Tm71 Γ B → Tm71 Γ (prod71 A B))
     (fst   : ∀ Γ A B   , Tm71 Γ (prod71 A B) → Tm71 Γ A)
     (snd   : ∀ Γ A B   , Tm71 Γ (prod71 A B) → Tm71 Γ B)
     (left  : ∀ Γ A B   , Tm71 Γ A → Tm71 Γ (sum71 A B))
     (right : ∀ Γ A B   , Tm71 Γ B → Tm71 Γ (sum71 A B))
     (case  : ∀ Γ A B C , Tm71 Γ (sum71 A B) → Tm71 Γ (arr71 A C) → Tm71 Γ (arr71 B C) → Tm71 Γ C)
     (zero  : ∀ Γ       , Tm71 Γ nat71)
     (suc   : ∀ Γ       , Tm71 Γ nat71 → Tm71 Γ nat71)
     (rec   : ∀ Γ A     , Tm71 Γ nat71 → Tm71 Γ (arr71 nat71 (arr71 A A)) → Tm71 Γ A → Tm71 Γ A)
   , Tm71 Γ A.

Definition var71 {Γ A} : Var71 Γ A → Tm71 Γ A
 := λ x Tm71 var71 lam app tt pair fst snd left right case zero suc rec ,
     var71 _ _ x.

Definition lam71 {Γ A B} : Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B)
 := λ t Tm71 var71 lam71 app tt pair fst snd left right case zero suc rec ,
     lam71 _ _ _ (t Tm71 var71 lam71 app tt pair fst snd left right case zero suc rec).

Definition app71 {Γ A B} : Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B
 := λ t u Tm71 var71 lam71 app71 tt pair fst snd left right case zero suc rec ,
     app71 _ _ _
         (t Tm71 var71 lam71 app71 tt pair fst snd left right case zero suc rec)
         (u Tm71 var71 lam71 app71 tt pair fst snd left right case zero suc rec).

Definition tt71 {Γ} : Tm71 Γ top71
 := λ Tm71 var71 lam71 app71 tt71 pair fst snd left right case zero suc rec , tt71 _.

Definition pair71 {Γ A B} : Tm71 Γ A → Tm71 Γ B → Tm71 Γ (prod71 A B)
 := λ t u Tm71 var71 lam71 app71 tt71 pair71 fst snd left right case zero suc rec ,
     pair71 _ _ _
          (t Tm71 var71 lam71 app71 tt71 pair71 fst snd left right case zero suc rec)
          (u Tm71 var71 lam71 app71 tt71 pair71 fst snd left right case zero suc rec).

Definition fst71 {Γ A B} : Tm71 Γ (prod71 A B) → Tm71 Γ A
 := λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd left right case zero suc rec ,
     fst71 _ _ _
         (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd left right case zero suc rec).

Definition snd71 {Γ A B} : Tm71 Γ (prod71 A B) → Tm71 Γ B
 := λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left right case zero suc rec ,
     snd71 _ _ _
          (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left right case zero suc rec).

Definition left71 {Γ A B} : Tm71 Γ A → Tm71 Γ (sum71 A B)
 := λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right case zero suc rec ,
     left71 _ _ _
          (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right case zero suc rec).

Definition right71 {Γ A B} : Tm71 Γ B → Tm71 Γ (sum71 A B)
 := λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case zero suc rec ,
     right71 _ _ _
            (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case zero suc rec).

Definition case71 {Γ A B C} : Tm71 Γ (sum71 A B) → Tm71 Γ (arr71 A C) → Tm71 Γ (arr71 B C) → Tm71 Γ C
 := λ t u v Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero suc rec ,
     case71 _ _ _ _
           (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero suc rec)
           (u Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero suc rec)
           (v Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero suc rec).

Definition zero71  {Γ} : Tm71 Γ nat71
 := λ Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc rec , zero71 _.

Definition suc71 {Γ} : Tm71 Γ nat71 → Tm71 Γ nat71
 := λ t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec ,
   suc71 _ (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec).

Definition rec71 {Γ A} : Tm71 Γ nat71 → Tm71 Γ (arr71 nat71 (arr71 A A)) → Tm71 Γ A → Tm71 Γ A
 := λ t u v Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec71 ,
     rec71 _ _
         (t Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec71)
         (u Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec71)
         (v Tm71 var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 case71 zero71 suc71 rec71).

Definition v071 {Γ A} : Tm71 (snoc71 Γ A) A
 := var71 vz71.

Definition v171 {Γ A B} : Tm71 (snoc71 (snoc71 Γ A) B) A
 := var71 (vs71 vz71).

Definition v271 {Γ A B C} : Tm71 (snoc71 (snoc71 (snoc71 Γ A) B) C) A
 := var71 (vs71 (vs71 vz71)).

Definition v371 {Γ A B C D} : Tm71 (snoc71 (snoc71 (snoc71 (snoc71 Γ A) B) C) D) A
 := var71 (vs71 (vs71 (vs71 vz71))).

Definition tbool71 : Ty71
 := sum71 top71 top71.

Definition ttrue71 {Γ} : Tm71 Γ tbool71
 := left71 tt71.

Definition tfalse71 {Γ} : Tm71 Γ tbool71
 := right71 tt71.

Definition ifthenelse71 {Γ A} : Tm71 Γ (arr71 tbool71 (arr71 A (arr71 A A)))
 := lam71 (lam71 (lam71 (case71 v271 (lam71 v271) (lam71 v171)))).

Definition times471 {Γ A} : Tm71 Γ (arr71 (arr71 A A) (arr71 A A))
  := lam71 (lam71 (app71 v171 (app71 v171 (app71 v171 (app71 v171 v071))))).

Definition add71 {Γ} : Tm71 Γ (arr71 nat71 (arr71 nat71 nat71))
 := lam71 (rec71 v071
      (lam71 (lam71 (lam71 (suc71 (app71 v171 v071)))))
      (lam71 v071)).

Definition mul71 {Γ} : Tm71 Γ (arr71 nat71 (arr71 nat71 nat71))
 := lam71 (rec71 v071
     (lam71 (lam71 (lam71 (app71 (app71 add71 (app71 v171 v071)) v071))))
     (lam71 zero71)).

Definition fact71 {Γ} : Tm71 Γ (arr71 nat71 nat71)
 := lam71 (rec71 v071 (lam71 (lam71 (app71 (app71 mul71 (suc71 v171)) v071)))
        (suc71 zero71)).

Require Import Coq.Unicode.Utf8.

Definition Ty72 : Set
 := ∀ (Ty72           : Set)
      (nat top bot  : Ty72)
      (arr prod sum : Ty72 → Ty72 → Ty72)
    , Ty72.

Definition nat72 : Ty72 := λ _ nat72 _ _ _ _ _ , nat72.
Definition top72 : Ty72 := λ _ _ top72 _ _ _ _ , top72.
Definition bot72 : Ty72 := λ _ _ _ bot72 _ _ _ , bot72.

Definition arr72 : Ty72 → Ty72 → Ty72
 := λ A B Ty72 nat72 top72 bot72 arr72 prod sum ,
     arr72 (A Ty72 nat72 top72 bot72 arr72 prod sum) (B Ty72 nat72 top72 bot72 arr72 prod sum).

Definition prod72 : Ty72 → Ty72 → Ty72
 := λ A B Ty72 nat72 top72 bot72 arr72 prod72 sum ,
     prod72 (A Ty72 nat72 top72 bot72 arr72 prod72 sum) (B Ty72 nat72 top72 bot72 arr72 prod72 sum).

Definition sum72 : Ty72 → Ty72 → Ty72
 := λ A B Ty72 nat72 top72 bot72 arr72 prod72 sum72 ,
     sum72 (A Ty72 nat72 top72 bot72 arr72 prod72 sum72) (B Ty72 nat72 top72 bot72 arr72 prod72 sum72).

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
     (tt    : ∀ Γ       , Tm72 Γ top72)
     (pair  : ∀ Γ A B   , Tm72 Γ A → Tm72 Γ B → Tm72 Γ (prod72 A B))
     (fst   : ∀ Γ A B   , Tm72 Γ (prod72 A B) → Tm72 Γ A)
     (snd   : ∀ Γ A B   , Tm72 Γ (prod72 A B) → Tm72 Γ B)
     (left  : ∀ Γ A B   , Tm72 Γ A → Tm72 Γ (sum72 A B))
     (right : ∀ Γ A B   , Tm72 Γ B → Tm72 Γ (sum72 A B))
     (case  : ∀ Γ A B C , Tm72 Γ (sum72 A B) → Tm72 Γ (arr72 A C) → Tm72 Γ (arr72 B C) → Tm72 Γ C)
     (zero  : ∀ Γ       , Tm72 Γ nat72)
     (suc   : ∀ Γ       , Tm72 Γ nat72 → Tm72 Γ nat72)
     (rec   : ∀ Γ A     , Tm72 Γ nat72 → Tm72 Γ (arr72 nat72 (arr72 A A)) → Tm72 Γ A → Tm72 Γ A)
   , Tm72 Γ A.

Definition var72 {Γ A} : Var72 Γ A → Tm72 Γ A
 := λ x Tm72 var72 lam app tt pair fst snd left right case zero suc rec ,
     var72 _ _ x.

Definition lam72 {Γ A B} : Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B)
 := λ t Tm72 var72 lam72 app tt pair fst snd left right case zero suc rec ,
     lam72 _ _ _ (t Tm72 var72 lam72 app tt pair fst snd left right case zero suc rec).

Definition app72 {Γ A B} : Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B
 := λ t u Tm72 var72 lam72 app72 tt pair fst snd left right case zero suc rec ,
     app72 _ _ _
         (t Tm72 var72 lam72 app72 tt pair fst snd left right case zero suc rec)
         (u Tm72 var72 lam72 app72 tt pair fst snd left right case zero suc rec).

Definition tt72 {Γ} : Tm72 Γ top72
 := λ Tm72 var72 lam72 app72 tt72 pair fst snd left right case zero suc rec , tt72 _.

Definition pair72 {Γ A B} : Tm72 Γ A → Tm72 Γ B → Tm72 Γ (prod72 A B)
 := λ t u Tm72 var72 lam72 app72 tt72 pair72 fst snd left right case zero suc rec ,
     pair72 _ _ _
          (t Tm72 var72 lam72 app72 tt72 pair72 fst snd left right case zero suc rec)
          (u Tm72 var72 lam72 app72 tt72 pair72 fst snd left right case zero suc rec).

Definition fst72 {Γ A B} : Tm72 Γ (prod72 A B) → Tm72 Γ A
 := λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd left right case zero suc rec ,
     fst72 _ _ _
         (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd left right case zero suc rec).

Definition snd72 {Γ A B} : Tm72 Γ (prod72 A B) → Tm72 Γ B
 := λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left right case zero suc rec ,
     snd72 _ _ _
          (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left right case zero suc rec).

Definition left72 {Γ A B} : Tm72 Γ A → Tm72 Γ (sum72 A B)
 := λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right case zero suc rec ,
     left72 _ _ _
          (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right case zero suc rec).

Definition right72 {Γ A B} : Tm72 Γ B → Tm72 Γ (sum72 A B)
 := λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case zero suc rec ,
     right72 _ _ _
            (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case zero suc rec).

Definition case72 {Γ A B C} : Tm72 Γ (sum72 A B) → Tm72 Γ (arr72 A C) → Tm72 Γ (arr72 B C) → Tm72 Γ C
 := λ t u v Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero suc rec ,
     case72 _ _ _ _
           (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero suc rec)
           (u Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero suc rec)
           (v Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero suc rec).

Definition zero72  {Γ} : Tm72 Γ nat72
 := λ Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc rec , zero72 _.

Definition suc72 {Γ} : Tm72 Γ nat72 → Tm72 Γ nat72
 := λ t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec ,
   suc72 _ (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec).

Definition rec72 {Γ A} : Tm72 Γ nat72 → Tm72 Γ (arr72 nat72 (arr72 A A)) → Tm72 Γ A → Tm72 Γ A
 := λ t u v Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec72 ,
     rec72 _ _
         (t Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec72)
         (u Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec72)
         (v Tm72 var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 case72 zero72 suc72 rec72).

Definition v072 {Γ A} : Tm72 (snoc72 Γ A) A
 := var72 vz72.

Definition v172 {Γ A B} : Tm72 (snoc72 (snoc72 Γ A) B) A
 := var72 (vs72 vz72).

Definition v272 {Γ A B C} : Tm72 (snoc72 (snoc72 (snoc72 Γ A) B) C) A
 := var72 (vs72 (vs72 vz72)).

Definition v372 {Γ A B C D} : Tm72 (snoc72 (snoc72 (snoc72 (snoc72 Γ A) B) C) D) A
 := var72 (vs72 (vs72 (vs72 vz72))).

Definition tbool72 : Ty72
 := sum72 top72 top72.

Definition ttrue72 {Γ} : Tm72 Γ tbool72
 := left72 tt72.

Definition tfalse72 {Γ} : Tm72 Γ tbool72
 := right72 tt72.

Definition ifthenelse72 {Γ A} : Tm72 Γ (arr72 tbool72 (arr72 A (arr72 A A)))
 := lam72 (lam72 (lam72 (case72 v272 (lam72 v272) (lam72 v172)))).

Definition times472 {Γ A} : Tm72 Γ (arr72 (arr72 A A) (arr72 A A))
  := lam72 (lam72 (app72 v172 (app72 v172 (app72 v172 (app72 v172 v072))))).

Definition add72 {Γ} : Tm72 Γ (arr72 nat72 (arr72 nat72 nat72))
 := lam72 (rec72 v072
      (lam72 (lam72 (lam72 (suc72 (app72 v172 v072)))))
      (lam72 v072)).

Definition mul72 {Γ} : Tm72 Γ (arr72 nat72 (arr72 nat72 nat72))
 := lam72 (rec72 v072
     (lam72 (lam72 (lam72 (app72 (app72 add72 (app72 v172 v072)) v072))))
     (lam72 zero72)).

Definition fact72 {Γ} : Tm72 Γ (arr72 nat72 nat72)
 := lam72 (rec72 v072 (lam72 (lam72 (app72 (app72 mul72 (suc72 v172)) v072)))
        (suc72 zero72)).

Require Import Coq.Unicode.Utf8.

Definition Ty73 : Set
 := ∀ (Ty73           : Set)
      (nat top bot  : Ty73)
      (arr prod sum : Ty73 → Ty73 → Ty73)
    , Ty73.

Definition nat73 : Ty73 := λ _ nat73 _ _ _ _ _ , nat73.
Definition top73 : Ty73 := λ _ _ top73 _ _ _ _ , top73.
Definition bot73 : Ty73 := λ _ _ _ bot73 _ _ _ , bot73.

Definition arr73 : Ty73 → Ty73 → Ty73
 := λ A B Ty73 nat73 top73 bot73 arr73 prod sum ,
     arr73 (A Ty73 nat73 top73 bot73 arr73 prod sum) (B Ty73 nat73 top73 bot73 arr73 prod sum).

Definition prod73 : Ty73 → Ty73 → Ty73
 := λ A B Ty73 nat73 top73 bot73 arr73 prod73 sum ,
     prod73 (A Ty73 nat73 top73 bot73 arr73 prod73 sum) (B Ty73 nat73 top73 bot73 arr73 prod73 sum).

Definition sum73 : Ty73 → Ty73 → Ty73
 := λ A B Ty73 nat73 top73 bot73 arr73 prod73 sum73 ,
     sum73 (A Ty73 nat73 top73 bot73 arr73 prod73 sum73) (B Ty73 nat73 top73 bot73 arr73 prod73 sum73).

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
     (tt    : ∀ Γ       , Tm73 Γ top73)
     (pair  : ∀ Γ A B   , Tm73 Γ A → Tm73 Γ B → Tm73 Γ (prod73 A B))
     (fst   : ∀ Γ A B   , Tm73 Γ (prod73 A B) → Tm73 Γ A)
     (snd   : ∀ Γ A B   , Tm73 Γ (prod73 A B) → Tm73 Γ B)
     (left  : ∀ Γ A B   , Tm73 Γ A → Tm73 Γ (sum73 A B))
     (right : ∀ Γ A B   , Tm73 Γ B → Tm73 Γ (sum73 A B))
     (case  : ∀ Γ A B C , Tm73 Γ (sum73 A B) → Tm73 Γ (arr73 A C) → Tm73 Γ (arr73 B C) → Tm73 Γ C)
     (zero  : ∀ Γ       , Tm73 Γ nat73)
     (suc   : ∀ Γ       , Tm73 Γ nat73 → Tm73 Γ nat73)
     (rec   : ∀ Γ A     , Tm73 Γ nat73 → Tm73 Γ (arr73 nat73 (arr73 A A)) → Tm73 Γ A → Tm73 Γ A)
   , Tm73 Γ A.

Definition var73 {Γ A} : Var73 Γ A → Tm73 Γ A
 := λ x Tm73 var73 lam app tt pair fst snd left right case zero suc rec ,
     var73 _ _ x.

Definition lam73 {Γ A B} : Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B)
 := λ t Tm73 var73 lam73 app tt pair fst snd left right case zero suc rec ,
     lam73 _ _ _ (t Tm73 var73 lam73 app tt pair fst snd left right case zero suc rec).

Definition app73 {Γ A B} : Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B
 := λ t u Tm73 var73 lam73 app73 tt pair fst snd left right case zero suc rec ,
     app73 _ _ _
         (t Tm73 var73 lam73 app73 tt pair fst snd left right case zero suc rec)
         (u Tm73 var73 lam73 app73 tt pair fst snd left right case zero suc rec).

Definition tt73 {Γ} : Tm73 Γ top73
 := λ Tm73 var73 lam73 app73 tt73 pair fst snd left right case zero suc rec , tt73 _.

Definition pair73 {Γ A B} : Tm73 Γ A → Tm73 Γ B → Tm73 Γ (prod73 A B)
 := λ t u Tm73 var73 lam73 app73 tt73 pair73 fst snd left right case zero suc rec ,
     pair73 _ _ _
          (t Tm73 var73 lam73 app73 tt73 pair73 fst snd left right case zero suc rec)
          (u Tm73 var73 lam73 app73 tt73 pair73 fst snd left right case zero suc rec).

Definition fst73 {Γ A B} : Tm73 Γ (prod73 A B) → Tm73 Γ A
 := λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd left right case zero suc rec ,
     fst73 _ _ _
         (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd left right case zero suc rec).

Definition snd73 {Γ A B} : Tm73 Γ (prod73 A B) → Tm73 Γ B
 := λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left right case zero suc rec ,
     snd73 _ _ _
          (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left right case zero suc rec).

Definition left73 {Γ A B} : Tm73 Γ A → Tm73 Γ (sum73 A B)
 := λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right case zero suc rec ,
     left73 _ _ _
          (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right case zero suc rec).

Definition right73 {Γ A B} : Tm73 Γ B → Tm73 Γ (sum73 A B)
 := λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case zero suc rec ,
     right73 _ _ _
            (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case zero suc rec).

Definition case73 {Γ A B C} : Tm73 Γ (sum73 A B) → Tm73 Γ (arr73 A C) → Tm73 Γ (arr73 B C) → Tm73 Γ C
 := λ t u v Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero suc rec ,
     case73 _ _ _ _
           (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero suc rec)
           (u Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero suc rec)
           (v Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero suc rec).

Definition zero73  {Γ} : Tm73 Γ nat73
 := λ Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc rec , zero73 _.

Definition suc73 {Γ} : Tm73 Γ nat73 → Tm73 Γ nat73
 := λ t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec ,
   suc73 _ (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec).

Definition rec73 {Γ A} : Tm73 Γ nat73 → Tm73 Γ (arr73 nat73 (arr73 A A)) → Tm73 Γ A → Tm73 Γ A
 := λ t u v Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec73 ,
     rec73 _ _
         (t Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec73)
         (u Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec73)
         (v Tm73 var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 case73 zero73 suc73 rec73).

Definition v073 {Γ A} : Tm73 (snoc73 Γ A) A
 := var73 vz73.

Definition v173 {Γ A B} : Tm73 (snoc73 (snoc73 Γ A) B) A
 := var73 (vs73 vz73).

Definition v273 {Γ A B C} : Tm73 (snoc73 (snoc73 (snoc73 Γ A) B) C) A
 := var73 (vs73 (vs73 vz73)).

Definition v373 {Γ A B C D} : Tm73 (snoc73 (snoc73 (snoc73 (snoc73 Γ A) B) C) D) A
 := var73 (vs73 (vs73 (vs73 vz73))).

Definition tbool73 : Ty73
 := sum73 top73 top73.

Definition ttrue73 {Γ} : Tm73 Γ tbool73
 := left73 tt73.

Definition tfalse73 {Γ} : Tm73 Γ tbool73
 := right73 tt73.

Definition ifthenelse73 {Γ A} : Tm73 Γ (arr73 tbool73 (arr73 A (arr73 A A)))
 := lam73 (lam73 (lam73 (case73 v273 (lam73 v273) (lam73 v173)))).

Definition times473 {Γ A} : Tm73 Γ (arr73 (arr73 A A) (arr73 A A))
  := lam73 (lam73 (app73 v173 (app73 v173 (app73 v173 (app73 v173 v073))))).

Definition add73 {Γ} : Tm73 Γ (arr73 nat73 (arr73 nat73 nat73))
 := lam73 (rec73 v073
      (lam73 (lam73 (lam73 (suc73 (app73 v173 v073)))))
      (lam73 v073)).

Definition mul73 {Γ} : Tm73 Γ (arr73 nat73 (arr73 nat73 nat73))
 := lam73 (rec73 v073
     (lam73 (lam73 (lam73 (app73 (app73 add73 (app73 v173 v073)) v073))))
     (lam73 zero73)).

Definition fact73 {Γ} : Tm73 Γ (arr73 nat73 nat73)
 := lam73 (rec73 v073 (lam73 (lam73 (app73 (app73 mul73 (suc73 v173)) v073)))
        (suc73 zero73)).

Require Import Coq.Unicode.Utf8.

Definition Ty74 : Set
 := ∀ (Ty74           : Set)
      (nat top bot  : Ty74)
      (arr prod sum : Ty74 → Ty74 → Ty74)
    , Ty74.

Definition nat74 : Ty74 := λ _ nat74 _ _ _ _ _ , nat74.
Definition top74 : Ty74 := λ _ _ top74 _ _ _ _ , top74.
Definition bot74 : Ty74 := λ _ _ _ bot74 _ _ _ , bot74.

Definition arr74 : Ty74 → Ty74 → Ty74
 := λ A B Ty74 nat74 top74 bot74 arr74 prod sum ,
     arr74 (A Ty74 nat74 top74 bot74 arr74 prod sum) (B Ty74 nat74 top74 bot74 arr74 prod sum).

Definition prod74 : Ty74 → Ty74 → Ty74
 := λ A B Ty74 nat74 top74 bot74 arr74 prod74 sum ,
     prod74 (A Ty74 nat74 top74 bot74 arr74 prod74 sum) (B Ty74 nat74 top74 bot74 arr74 prod74 sum).

Definition sum74 : Ty74 → Ty74 → Ty74
 := λ A B Ty74 nat74 top74 bot74 arr74 prod74 sum74 ,
     sum74 (A Ty74 nat74 top74 bot74 arr74 prod74 sum74) (B Ty74 nat74 top74 bot74 arr74 prod74 sum74).

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
     (tt    : ∀ Γ       , Tm74 Γ top74)
     (pair  : ∀ Γ A B   , Tm74 Γ A → Tm74 Γ B → Tm74 Γ (prod74 A B))
     (fst   : ∀ Γ A B   , Tm74 Γ (prod74 A B) → Tm74 Γ A)
     (snd   : ∀ Γ A B   , Tm74 Γ (prod74 A B) → Tm74 Γ B)
     (left  : ∀ Γ A B   , Tm74 Γ A → Tm74 Γ (sum74 A B))
     (right : ∀ Γ A B   , Tm74 Γ B → Tm74 Γ (sum74 A B))
     (case  : ∀ Γ A B C , Tm74 Γ (sum74 A B) → Tm74 Γ (arr74 A C) → Tm74 Γ (arr74 B C) → Tm74 Γ C)
     (zero  : ∀ Γ       , Tm74 Γ nat74)
     (suc   : ∀ Γ       , Tm74 Γ nat74 → Tm74 Γ nat74)
     (rec   : ∀ Γ A     , Tm74 Γ nat74 → Tm74 Γ (arr74 nat74 (arr74 A A)) → Tm74 Γ A → Tm74 Γ A)
   , Tm74 Γ A.

Definition var74 {Γ A} : Var74 Γ A → Tm74 Γ A
 := λ x Tm74 var74 lam app tt pair fst snd left right case zero suc rec ,
     var74 _ _ x.

Definition lam74 {Γ A B} : Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B)
 := λ t Tm74 var74 lam74 app tt pair fst snd left right case zero suc rec ,
     lam74 _ _ _ (t Tm74 var74 lam74 app tt pair fst snd left right case zero suc rec).

Definition app74 {Γ A B} : Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B
 := λ t u Tm74 var74 lam74 app74 tt pair fst snd left right case zero suc rec ,
     app74 _ _ _
         (t Tm74 var74 lam74 app74 tt pair fst snd left right case zero suc rec)
         (u Tm74 var74 lam74 app74 tt pair fst snd left right case zero suc rec).

Definition tt74 {Γ} : Tm74 Γ top74
 := λ Tm74 var74 lam74 app74 tt74 pair fst snd left right case zero suc rec , tt74 _.

Definition pair74 {Γ A B} : Tm74 Γ A → Tm74 Γ B → Tm74 Γ (prod74 A B)
 := λ t u Tm74 var74 lam74 app74 tt74 pair74 fst snd left right case zero suc rec ,
     pair74 _ _ _
          (t Tm74 var74 lam74 app74 tt74 pair74 fst snd left right case zero suc rec)
          (u Tm74 var74 lam74 app74 tt74 pair74 fst snd left right case zero suc rec).

Definition fst74 {Γ A B} : Tm74 Γ (prod74 A B) → Tm74 Γ A
 := λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd left right case zero suc rec ,
     fst74 _ _ _
         (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd left right case zero suc rec).

Definition snd74 {Γ A B} : Tm74 Γ (prod74 A B) → Tm74 Γ B
 := λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left right case zero suc rec ,
     snd74 _ _ _
          (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left right case zero suc rec).

Definition left74 {Γ A B} : Tm74 Γ A → Tm74 Γ (sum74 A B)
 := λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right case zero suc rec ,
     left74 _ _ _
          (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right case zero suc rec).

Definition right74 {Γ A B} : Tm74 Γ B → Tm74 Γ (sum74 A B)
 := λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case zero suc rec ,
     right74 _ _ _
            (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case zero suc rec).

Definition case74 {Γ A B C} : Tm74 Γ (sum74 A B) → Tm74 Γ (arr74 A C) → Tm74 Γ (arr74 B C) → Tm74 Γ C
 := λ t u v Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero suc rec ,
     case74 _ _ _ _
           (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero suc rec)
           (u Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero suc rec)
           (v Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero suc rec).

Definition zero74  {Γ} : Tm74 Γ nat74
 := λ Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc rec , zero74 _.

Definition suc74 {Γ} : Tm74 Γ nat74 → Tm74 Γ nat74
 := λ t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec ,
   suc74 _ (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec).

Definition rec74 {Γ A} : Tm74 Γ nat74 → Tm74 Γ (arr74 nat74 (arr74 A A)) → Tm74 Γ A → Tm74 Γ A
 := λ t u v Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec74 ,
     rec74 _ _
         (t Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec74)
         (u Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec74)
         (v Tm74 var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 case74 zero74 suc74 rec74).

Definition v074 {Γ A} : Tm74 (snoc74 Γ A) A
 := var74 vz74.

Definition v174 {Γ A B} : Tm74 (snoc74 (snoc74 Γ A) B) A
 := var74 (vs74 vz74).

Definition v274 {Γ A B C} : Tm74 (snoc74 (snoc74 (snoc74 Γ A) B) C) A
 := var74 (vs74 (vs74 vz74)).

Definition v374 {Γ A B C D} : Tm74 (snoc74 (snoc74 (snoc74 (snoc74 Γ A) B) C) D) A
 := var74 (vs74 (vs74 (vs74 vz74))).

Definition tbool74 : Ty74
 := sum74 top74 top74.

Definition ttrue74 {Γ} : Tm74 Γ tbool74
 := left74 tt74.

Definition tfalse74 {Γ} : Tm74 Γ tbool74
 := right74 tt74.

Definition ifthenelse74 {Γ A} : Tm74 Γ (arr74 tbool74 (arr74 A (arr74 A A)))
 := lam74 (lam74 (lam74 (case74 v274 (lam74 v274) (lam74 v174)))).

Definition times474 {Γ A} : Tm74 Γ (arr74 (arr74 A A) (arr74 A A))
  := lam74 (lam74 (app74 v174 (app74 v174 (app74 v174 (app74 v174 v074))))).

Definition add74 {Γ} : Tm74 Γ (arr74 nat74 (arr74 nat74 nat74))
 := lam74 (rec74 v074
      (lam74 (lam74 (lam74 (suc74 (app74 v174 v074)))))
      (lam74 v074)).

Definition mul74 {Γ} : Tm74 Γ (arr74 nat74 (arr74 nat74 nat74))
 := lam74 (rec74 v074
     (lam74 (lam74 (lam74 (app74 (app74 add74 (app74 v174 v074)) v074))))
     (lam74 zero74)).

Definition fact74 {Γ} : Tm74 Γ (arr74 nat74 nat74)
 := lam74 (rec74 v074 (lam74 (lam74 (app74 (app74 mul74 (suc74 v174)) v074)))
        (suc74 zero74)).

Require Import Coq.Unicode.Utf8.

Definition Ty75 : Set
 := ∀ (Ty75           : Set)
      (nat top bot  : Ty75)
      (arr prod sum : Ty75 → Ty75 → Ty75)
    , Ty75.

Definition nat75 : Ty75 := λ _ nat75 _ _ _ _ _ , nat75.
Definition top75 : Ty75 := λ _ _ top75 _ _ _ _ , top75.
Definition bot75 : Ty75 := λ _ _ _ bot75 _ _ _ , bot75.

Definition arr75 : Ty75 → Ty75 → Ty75
 := λ A B Ty75 nat75 top75 bot75 arr75 prod sum ,
     arr75 (A Ty75 nat75 top75 bot75 arr75 prod sum) (B Ty75 nat75 top75 bot75 arr75 prod sum).

Definition prod75 : Ty75 → Ty75 → Ty75
 := λ A B Ty75 nat75 top75 bot75 arr75 prod75 sum ,
     prod75 (A Ty75 nat75 top75 bot75 arr75 prod75 sum) (B Ty75 nat75 top75 bot75 arr75 prod75 sum).

Definition sum75 : Ty75 → Ty75 → Ty75
 := λ A B Ty75 nat75 top75 bot75 arr75 prod75 sum75 ,
     sum75 (A Ty75 nat75 top75 bot75 arr75 prod75 sum75) (B Ty75 nat75 top75 bot75 arr75 prod75 sum75).

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
     (tt    : ∀ Γ       , Tm75 Γ top75)
     (pair  : ∀ Γ A B   , Tm75 Γ A → Tm75 Γ B → Tm75 Γ (prod75 A B))
     (fst   : ∀ Γ A B   , Tm75 Γ (prod75 A B) → Tm75 Γ A)
     (snd   : ∀ Γ A B   , Tm75 Γ (prod75 A B) → Tm75 Γ B)
     (left  : ∀ Γ A B   , Tm75 Γ A → Tm75 Γ (sum75 A B))
     (right : ∀ Γ A B   , Tm75 Γ B → Tm75 Γ (sum75 A B))
     (case  : ∀ Γ A B C , Tm75 Γ (sum75 A B) → Tm75 Γ (arr75 A C) → Tm75 Γ (arr75 B C) → Tm75 Γ C)
     (zero  : ∀ Γ       , Tm75 Γ nat75)
     (suc   : ∀ Γ       , Tm75 Γ nat75 → Tm75 Γ nat75)
     (rec   : ∀ Γ A     , Tm75 Γ nat75 → Tm75 Γ (arr75 nat75 (arr75 A A)) → Tm75 Γ A → Tm75 Γ A)
   , Tm75 Γ A.

Definition var75 {Γ A} : Var75 Γ A → Tm75 Γ A
 := λ x Tm75 var75 lam app tt pair fst snd left right case zero suc rec ,
     var75 _ _ x.

Definition lam75 {Γ A B} : Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B)
 := λ t Tm75 var75 lam75 app tt pair fst snd left right case zero suc rec ,
     lam75 _ _ _ (t Tm75 var75 lam75 app tt pair fst snd left right case zero suc rec).

Definition app75 {Γ A B} : Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B
 := λ t u Tm75 var75 lam75 app75 tt pair fst snd left right case zero suc rec ,
     app75 _ _ _
         (t Tm75 var75 lam75 app75 tt pair fst snd left right case zero suc rec)
         (u Tm75 var75 lam75 app75 tt pair fst snd left right case zero suc rec).

Definition tt75 {Γ} : Tm75 Γ top75
 := λ Tm75 var75 lam75 app75 tt75 pair fst snd left right case zero suc rec , tt75 _.

Definition pair75 {Γ A B} : Tm75 Γ A → Tm75 Γ B → Tm75 Γ (prod75 A B)
 := λ t u Tm75 var75 lam75 app75 tt75 pair75 fst snd left right case zero suc rec ,
     pair75 _ _ _
          (t Tm75 var75 lam75 app75 tt75 pair75 fst snd left right case zero suc rec)
          (u Tm75 var75 lam75 app75 tt75 pair75 fst snd left right case zero suc rec).

Definition fst75 {Γ A B} : Tm75 Γ (prod75 A B) → Tm75 Γ A
 := λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd left right case zero suc rec ,
     fst75 _ _ _
         (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd left right case zero suc rec).

Definition snd75 {Γ A B} : Tm75 Γ (prod75 A B) → Tm75 Γ B
 := λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left right case zero suc rec ,
     snd75 _ _ _
          (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left right case zero suc rec).

Definition left75 {Γ A B} : Tm75 Γ A → Tm75 Γ (sum75 A B)
 := λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right case zero suc rec ,
     left75 _ _ _
          (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right case zero suc rec).

Definition right75 {Γ A B} : Tm75 Γ B → Tm75 Γ (sum75 A B)
 := λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case zero suc rec ,
     right75 _ _ _
            (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case zero suc rec).

Definition case75 {Γ A B C} : Tm75 Γ (sum75 A B) → Tm75 Γ (arr75 A C) → Tm75 Γ (arr75 B C) → Tm75 Γ C
 := λ t u v Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero suc rec ,
     case75 _ _ _ _
           (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero suc rec)
           (u Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero suc rec)
           (v Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero suc rec).

Definition zero75  {Γ} : Tm75 Γ nat75
 := λ Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc rec , zero75 _.

Definition suc75 {Γ} : Tm75 Γ nat75 → Tm75 Γ nat75
 := λ t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec ,
   suc75 _ (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec).

Definition rec75 {Γ A} : Tm75 Γ nat75 → Tm75 Γ (arr75 nat75 (arr75 A A)) → Tm75 Γ A → Tm75 Γ A
 := λ t u v Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec75 ,
     rec75 _ _
         (t Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec75)
         (u Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec75)
         (v Tm75 var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 case75 zero75 suc75 rec75).

Definition v075 {Γ A} : Tm75 (snoc75 Γ A) A
 := var75 vz75.

Definition v175 {Γ A B} : Tm75 (snoc75 (snoc75 Γ A) B) A
 := var75 (vs75 vz75).

Definition v275 {Γ A B C} : Tm75 (snoc75 (snoc75 (snoc75 Γ A) B) C) A
 := var75 (vs75 (vs75 vz75)).

Definition v375 {Γ A B C D} : Tm75 (snoc75 (snoc75 (snoc75 (snoc75 Γ A) B) C) D) A
 := var75 (vs75 (vs75 (vs75 vz75))).

Definition tbool75 : Ty75
 := sum75 top75 top75.

Definition ttrue75 {Γ} : Tm75 Γ tbool75
 := left75 tt75.

Definition tfalse75 {Γ} : Tm75 Γ tbool75
 := right75 tt75.

Definition ifthenelse75 {Γ A} : Tm75 Γ (arr75 tbool75 (arr75 A (arr75 A A)))
 := lam75 (lam75 (lam75 (case75 v275 (lam75 v275) (lam75 v175)))).

Definition times475 {Γ A} : Tm75 Γ (arr75 (arr75 A A) (arr75 A A))
  := lam75 (lam75 (app75 v175 (app75 v175 (app75 v175 (app75 v175 v075))))).

Definition add75 {Γ} : Tm75 Γ (arr75 nat75 (arr75 nat75 nat75))
 := lam75 (rec75 v075
      (lam75 (lam75 (lam75 (suc75 (app75 v175 v075)))))
      (lam75 v075)).

Definition mul75 {Γ} : Tm75 Γ (arr75 nat75 (arr75 nat75 nat75))
 := lam75 (rec75 v075
     (lam75 (lam75 (lam75 (app75 (app75 add75 (app75 v175 v075)) v075))))
     (lam75 zero75)).

Definition fact75 {Γ} : Tm75 Γ (arr75 nat75 nat75)
 := lam75 (rec75 v075 (lam75 (lam75 (app75 (app75 mul75 (suc75 v175)) v075)))
        (suc75 zero75)).

Require Import Coq.Unicode.Utf8.

Definition Ty76 : Set
 := ∀ (Ty76           : Set)
      (nat top bot  : Ty76)
      (arr prod sum : Ty76 → Ty76 → Ty76)
    , Ty76.

Definition nat76 : Ty76 := λ _ nat76 _ _ _ _ _ , nat76.
Definition top76 : Ty76 := λ _ _ top76 _ _ _ _ , top76.
Definition bot76 : Ty76 := λ _ _ _ bot76 _ _ _ , bot76.

Definition arr76 : Ty76 → Ty76 → Ty76
 := λ A B Ty76 nat76 top76 bot76 arr76 prod sum ,
     arr76 (A Ty76 nat76 top76 bot76 arr76 prod sum) (B Ty76 nat76 top76 bot76 arr76 prod sum).

Definition prod76 : Ty76 → Ty76 → Ty76
 := λ A B Ty76 nat76 top76 bot76 arr76 prod76 sum ,
     prod76 (A Ty76 nat76 top76 bot76 arr76 prod76 sum) (B Ty76 nat76 top76 bot76 arr76 prod76 sum).

Definition sum76 : Ty76 → Ty76 → Ty76
 := λ A B Ty76 nat76 top76 bot76 arr76 prod76 sum76 ,
     sum76 (A Ty76 nat76 top76 bot76 arr76 prod76 sum76) (B Ty76 nat76 top76 bot76 arr76 prod76 sum76).

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
     (tt    : ∀ Γ       , Tm76 Γ top76)
     (pair  : ∀ Γ A B   , Tm76 Γ A → Tm76 Γ B → Tm76 Γ (prod76 A B))
     (fst   : ∀ Γ A B   , Tm76 Γ (prod76 A B) → Tm76 Γ A)
     (snd   : ∀ Γ A B   , Tm76 Γ (prod76 A B) → Tm76 Γ B)
     (left  : ∀ Γ A B   , Tm76 Γ A → Tm76 Γ (sum76 A B))
     (right : ∀ Γ A B   , Tm76 Γ B → Tm76 Γ (sum76 A B))
     (case  : ∀ Γ A B C , Tm76 Γ (sum76 A B) → Tm76 Γ (arr76 A C) → Tm76 Γ (arr76 B C) → Tm76 Γ C)
     (zero  : ∀ Γ       , Tm76 Γ nat76)
     (suc   : ∀ Γ       , Tm76 Γ nat76 → Tm76 Γ nat76)
     (rec   : ∀ Γ A     , Tm76 Γ nat76 → Tm76 Γ (arr76 nat76 (arr76 A A)) → Tm76 Γ A → Tm76 Γ A)
   , Tm76 Γ A.

Definition var76 {Γ A} : Var76 Γ A → Tm76 Γ A
 := λ x Tm76 var76 lam app tt pair fst snd left right case zero suc rec ,
     var76 _ _ x.

Definition lam76 {Γ A B} : Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B)
 := λ t Tm76 var76 lam76 app tt pair fst snd left right case zero suc rec ,
     lam76 _ _ _ (t Tm76 var76 lam76 app tt pair fst snd left right case zero suc rec).

Definition app76 {Γ A B} : Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B
 := λ t u Tm76 var76 lam76 app76 tt pair fst snd left right case zero suc rec ,
     app76 _ _ _
         (t Tm76 var76 lam76 app76 tt pair fst snd left right case zero suc rec)
         (u Tm76 var76 lam76 app76 tt pair fst snd left right case zero suc rec).

Definition tt76 {Γ} : Tm76 Γ top76
 := λ Tm76 var76 lam76 app76 tt76 pair fst snd left right case zero suc rec , tt76 _.

Definition pair76 {Γ A B} : Tm76 Γ A → Tm76 Γ B → Tm76 Γ (prod76 A B)
 := λ t u Tm76 var76 lam76 app76 tt76 pair76 fst snd left right case zero suc rec ,
     pair76 _ _ _
          (t Tm76 var76 lam76 app76 tt76 pair76 fst snd left right case zero suc rec)
          (u Tm76 var76 lam76 app76 tt76 pair76 fst snd left right case zero suc rec).

Definition fst76 {Γ A B} : Tm76 Γ (prod76 A B) → Tm76 Γ A
 := λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd left right case zero suc rec ,
     fst76 _ _ _
         (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd left right case zero suc rec).

Definition snd76 {Γ A B} : Tm76 Γ (prod76 A B) → Tm76 Γ B
 := λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left right case zero suc rec ,
     snd76 _ _ _
          (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left right case zero suc rec).

Definition left76 {Γ A B} : Tm76 Γ A → Tm76 Γ (sum76 A B)
 := λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right case zero suc rec ,
     left76 _ _ _
          (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right case zero suc rec).

Definition right76 {Γ A B} : Tm76 Γ B → Tm76 Γ (sum76 A B)
 := λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case zero suc rec ,
     right76 _ _ _
            (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case zero suc rec).

Definition case76 {Γ A B C} : Tm76 Γ (sum76 A B) → Tm76 Γ (arr76 A C) → Tm76 Γ (arr76 B C) → Tm76 Γ C
 := λ t u v Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero suc rec ,
     case76 _ _ _ _
           (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero suc rec)
           (u Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero suc rec)
           (v Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero suc rec).

Definition zero76  {Γ} : Tm76 Γ nat76
 := λ Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc rec , zero76 _.

Definition suc76 {Γ} : Tm76 Γ nat76 → Tm76 Γ nat76
 := λ t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec ,
   suc76 _ (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec).

Definition rec76 {Γ A} : Tm76 Γ nat76 → Tm76 Γ (arr76 nat76 (arr76 A A)) → Tm76 Γ A → Tm76 Γ A
 := λ t u v Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec76 ,
     rec76 _ _
         (t Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec76)
         (u Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec76)
         (v Tm76 var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 case76 zero76 suc76 rec76).

Definition v076 {Γ A} : Tm76 (snoc76 Γ A) A
 := var76 vz76.

Definition v176 {Γ A B} : Tm76 (snoc76 (snoc76 Γ A) B) A
 := var76 (vs76 vz76).

Definition v276 {Γ A B C} : Tm76 (snoc76 (snoc76 (snoc76 Γ A) B) C) A
 := var76 (vs76 (vs76 vz76)).

Definition v376 {Γ A B C D} : Tm76 (snoc76 (snoc76 (snoc76 (snoc76 Γ A) B) C) D) A
 := var76 (vs76 (vs76 (vs76 vz76))).

Definition tbool76 : Ty76
 := sum76 top76 top76.

Definition ttrue76 {Γ} : Tm76 Γ tbool76
 := left76 tt76.

Definition tfalse76 {Γ} : Tm76 Γ tbool76
 := right76 tt76.

Definition ifthenelse76 {Γ A} : Tm76 Γ (arr76 tbool76 (arr76 A (arr76 A A)))
 := lam76 (lam76 (lam76 (case76 v276 (lam76 v276) (lam76 v176)))).

Definition times476 {Γ A} : Tm76 Γ (arr76 (arr76 A A) (arr76 A A))
  := lam76 (lam76 (app76 v176 (app76 v176 (app76 v176 (app76 v176 v076))))).

Definition add76 {Γ} : Tm76 Γ (arr76 nat76 (arr76 nat76 nat76))
 := lam76 (rec76 v076
      (lam76 (lam76 (lam76 (suc76 (app76 v176 v076)))))
      (lam76 v076)).

Definition mul76 {Γ} : Tm76 Γ (arr76 nat76 (arr76 nat76 nat76))
 := lam76 (rec76 v076
     (lam76 (lam76 (lam76 (app76 (app76 add76 (app76 v176 v076)) v076))))
     (lam76 zero76)).

Definition fact76 {Γ} : Tm76 Γ (arr76 nat76 nat76)
 := lam76 (rec76 v076 (lam76 (lam76 (app76 (app76 mul76 (suc76 v176)) v076)))
        (suc76 zero76)).

Require Import Coq.Unicode.Utf8.

Definition Ty77 : Set
 := ∀ (Ty77           : Set)
      (nat top bot  : Ty77)
      (arr prod sum : Ty77 → Ty77 → Ty77)
    , Ty77.

Definition nat77 : Ty77 := λ _ nat77 _ _ _ _ _ , nat77.
Definition top77 : Ty77 := λ _ _ top77 _ _ _ _ , top77.
Definition bot77 : Ty77 := λ _ _ _ bot77 _ _ _ , bot77.

Definition arr77 : Ty77 → Ty77 → Ty77
 := λ A B Ty77 nat77 top77 bot77 arr77 prod sum ,
     arr77 (A Ty77 nat77 top77 bot77 arr77 prod sum) (B Ty77 nat77 top77 bot77 arr77 prod sum).

Definition prod77 : Ty77 → Ty77 → Ty77
 := λ A B Ty77 nat77 top77 bot77 arr77 prod77 sum ,
     prod77 (A Ty77 nat77 top77 bot77 arr77 prod77 sum) (B Ty77 nat77 top77 bot77 arr77 prod77 sum).

Definition sum77 : Ty77 → Ty77 → Ty77
 := λ A B Ty77 nat77 top77 bot77 arr77 prod77 sum77 ,
     sum77 (A Ty77 nat77 top77 bot77 arr77 prod77 sum77) (B Ty77 nat77 top77 bot77 arr77 prod77 sum77).

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
     (tt    : ∀ Γ       , Tm77 Γ top77)
     (pair  : ∀ Γ A B   , Tm77 Γ A → Tm77 Γ B → Tm77 Γ (prod77 A B))
     (fst   : ∀ Γ A B   , Tm77 Γ (prod77 A B) → Tm77 Γ A)
     (snd   : ∀ Γ A B   , Tm77 Γ (prod77 A B) → Tm77 Γ B)
     (left  : ∀ Γ A B   , Tm77 Γ A → Tm77 Γ (sum77 A B))
     (right : ∀ Γ A B   , Tm77 Γ B → Tm77 Γ (sum77 A B))
     (case  : ∀ Γ A B C , Tm77 Γ (sum77 A B) → Tm77 Γ (arr77 A C) → Tm77 Γ (arr77 B C) → Tm77 Γ C)
     (zero  : ∀ Γ       , Tm77 Γ nat77)
     (suc   : ∀ Γ       , Tm77 Γ nat77 → Tm77 Γ nat77)
     (rec   : ∀ Γ A     , Tm77 Γ nat77 → Tm77 Γ (arr77 nat77 (arr77 A A)) → Tm77 Γ A → Tm77 Γ A)
   , Tm77 Γ A.

Definition var77 {Γ A} : Var77 Γ A → Tm77 Γ A
 := λ x Tm77 var77 lam app tt pair fst snd left right case zero suc rec ,
     var77 _ _ x.

Definition lam77 {Γ A B} : Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B)
 := λ t Tm77 var77 lam77 app tt pair fst snd left right case zero suc rec ,
     lam77 _ _ _ (t Tm77 var77 lam77 app tt pair fst snd left right case zero suc rec).

Definition app77 {Γ A B} : Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B
 := λ t u Tm77 var77 lam77 app77 tt pair fst snd left right case zero suc rec ,
     app77 _ _ _
         (t Tm77 var77 lam77 app77 tt pair fst snd left right case zero suc rec)
         (u Tm77 var77 lam77 app77 tt pair fst snd left right case zero suc rec).

Definition tt77 {Γ} : Tm77 Γ top77
 := λ Tm77 var77 lam77 app77 tt77 pair fst snd left right case zero suc rec , tt77 _.

Definition pair77 {Γ A B} : Tm77 Γ A → Tm77 Γ B → Tm77 Γ (prod77 A B)
 := λ t u Tm77 var77 lam77 app77 tt77 pair77 fst snd left right case zero suc rec ,
     pair77 _ _ _
          (t Tm77 var77 lam77 app77 tt77 pair77 fst snd left right case zero suc rec)
          (u Tm77 var77 lam77 app77 tt77 pair77 fst snd left right case zero suc rec).

Definition fst77 {Γ A B} : Tm77 Γ (prod77 A B) → Tm77 Γ A
 := λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd left right case zero suc rec ,
     fst77 _ _ _
         (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd left right case zero suc rec).

Definition snd77 {Γ A B} : Tm77 Γ (prod77 A B) → Tm77 Γ B
 := λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left right case zero suc rec ,
     snd77 _ _ _
          (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left right case zero suc rec).

Definition left77 {Γ A B} : Tm77 Γ A → Tm77 Γ (sum77 A B)
 := λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right case zero suc rec ,
     left77 _ _ _
          (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right case zero suc rec).

Definition right77 {Γ A B} : Tm77 Γ B → Tm77 Γ (sum77 A B)
 := λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case zero suc rec ,
     right77 _ _ _
            (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case zero suc rec).

Definition case77 {Γ A B C} : Tm77 Γ (sum77 A B) → Tm77 Γ (arr77 A C) → Tm77 Γ (arr77 B C) → Tm77 Γ C
 := λ t u v Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero suc rec ,
     case77 _ _ _ _
           (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero suc rec)
           (u Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero suc rec)
           (v Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero suc rec).

Definition zero77  {Γ} : Tm77 Γ nat77
 := λ Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc rec , zero77 _.

Definition suc77 {Γ} : Tm77 Γ nat77 → Tm77 Γ nat77
 := λ t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec ,
   suc77 _ (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec).

Definition rec77 {Γ A} : Tm77 Γ nat77 → Tm77 Γ (arr77 nat77 (arr77 A A)) → Tm77 Γ A → Tm77 Γ A
 := λ t u v Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec77 ,
     rec77 _ _
         (t Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec77)
         (u Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec77)
         (v Tm77 var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 case77 zero77 suc77 rec77).

Definition v077 {Γ A} : Tm77 (snoc77 Γ A) A
 := var77 vz77.

Definition v177 {Γ A B} : Tm77 (snoc77 (snoc77 Γ A) B) A
 := var77 (vs77 vz77).

Definition v277 {Γ A B C} : Tm77 (snoc77 (snoc77 (snoc77 Γ A) B) C) A
 := var77 (vs77 (vs77 vz77)).

Definition v377 {Γ A B C D} : Tm77 (snoc77 (snoc77 (snoc77 (snoc77 Γ A) B) C) D) A
 := var77 (vs77 (vs77 (vs77 vz77))).

Definition tbool77 : Ty77
 := sum77 top77 top77.

Definition ttrue77 {Γ} : Tm77 Γ tbool77
 := left77 tt77.

Definition tfalse77 {Γ} : Tm77 Γ tbool77
 := right77 tt77.

Definition ifthenelse77 {Γ A} : Tm77 Γ (arr77 tbool77 (arr77 A (arr77 A A)))
 := lam77 (lam77 (lam77 (case77 v277 (lam77 v277) (lam77 v177)))).

Definition times477 {Γ A} : Tm77 Γ (arr77 (arr77 A A) (arr77 A A))
  := lam77 (lam77 (app77 v177 (app77 v177 (app77 v177 (app77 v177 v077))))).

Definition add77 {Γ} : Tm77 Γ (arr77 nat77 (arr77 nat77 nat77))
 := lam77 (rec77 v077
      (lam77 (lam77 (lam77 (suc77 (app77 v177 v077)))))
      (lam77 v077)).

Definition mul77 {Γ} : Tm77 Γ (arr77 nat77 (arr77 nat77 nat77))
 := lam77 (rec77 v077
     (lam77 (lam77 (lam77 (app77 (app77 add77 (app77 v177 v077)) v077))))
     (lam77 zero77)).

Definition fact77 {Γ} : Tm77 Γ (arr77 nat77 nat77)
 := lam77 (rec77 v077 (lam77 (lam77 (app77 (app77 mul77 (suc77 v177)) v077)))
        (suc77 zero77)).

Require Import Coq.Unicode.Utf8.

Definition Ty78 : Set
 := ∀ (Ty78           : Set)
      (nat top bot  : Ty78)
      (arr prod sum : Ty78 → Ty78 → Ty78)
    , Ty78.

Definition nat78 : Ty78 := λ _ nat78 _ _ _ _ _ , nat78.
Definition top78 : Ty78 := λ _ _ top78 _ _ _ _ , top78.
Definition bot78 : Ty78 := λ _ _ _ bot78 _ _ _ , bot78.

Definition arr78 : Ty78 → Ty78 → Ty78
 := λ A B Ty78 nat78 top78 bot78 arr78 prod sum ,
     arr78 (A Ty78 nat78 top78 bot78 arr78 prod sum) (B Ty78 nat78 top78 bot78 arr78 prod sum).

Definition prod78 : Ty78 → Ty78 → Ty78
 := λ A B Ty78 nat78 top78 bot78 arr78 prod78 sum ,
     prod78 (A Ty78 nat78 top78 bot78 arr78 prod78 sum) (B Ty78 nat78 top78 bot78 arr78 prod78 sum).

Definition sum78 : Ty78 → Ty78 → Ty78
 := λ A B Ty78 nat78 top78 bot78 arr78 prod78 sum78 ,
     sum78 (A Ty78 nat78 top78 bot78 arr78 prod78 sum78) (B Ty78 nat78 top78 bot78 arr78 prod78 sum78).

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
     (tt    : ∀ Γ       , Tm78 Γ top78)
     (pair  : ∀ Γ A B   , Tm78 Γ A → Tm78 Γ B → Tm78 Γ (prod78 A B))
     (fst   : ∀ Γ A B   , Tm78 Γ (prod78 A B) → Tm78 Γ A)
     (snd   : ∀ Γ A B   , Tm78 Γ (prod78 A B) → Tm78 Γ B)
     (left  : ∀ Γ A B   , Tm78 Γ A → Tm78 Γ (sum78 A B))
     (right : ∀ Γ A B   , Tm78 Γ B → Tm78 Γ (sum78 A B))
     (case  : ∀ Γ A B C , Tm78 Γ (sum78 A B) → Tm78 Γ (arr78 A C) → Tm78 Γ (arr78 B C) → Tm78 Γ C)
     (zero  : ∀ Γ       , Tm78 Γ nat78)
     (suc   : ∀ Γ       , Tm78 Γ nat78 → Tm78 Γ nat78)
     (rec   : ∀ Γ A     , Tm78 Γ nat78 → Tm78 Γ (arr78 nat78 (arr78 A A)) → Tm78 Γ A → Tm78 Γ A)
   , Tm78 Γ A.

Definition var78 {Γ A} : Var78 Γ A → Tm78 Γ A
 := λ x Tm78 var78 lam app tt pair fst snd left right case zero suc rec ,
     var78 _ _ x.

Definition lam78 {Γ A B} : Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B)
 := λ t Tm78 var78 lam78 app tt pair fst snd left right case zero suc rec ,
     lam78 _ _ _ (t Tm78 var78 lam78 app tt pair fst snd left right case zero suc rec).

Definition app78 {Γ A B} : Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B
 := λ t u Tm78 var78 lam78 app78 tt pair fst snd left right case zero suc rec ,
     app78 _ _ _
         (t Tm78 var78 lam78 app78 tt pair fst snd left right case zero suc rec)
         (u Tm78 var78 lam78 app78 tt pair fst snd left right case zero suc rec).

Definition tt78 {Γ} : Tm78 Γ top78
 := λ Tm78 var78 lam78 app78 tt78 pair fst snd left right case zero suc rec , tt78 _.

Definition pair78 {Γ A B} : Tm78 Γ A → Tm78 Γ B → Tm78 Γ (prod78 A B)
 := λ t u Tm78 var78 lam78 app78 tt78 pair78 fst snd left right case zero suc rec ,
     pair78 _ _ _
          (t Tm78 var78 lam78 app78 tt78 pair78 fst snd left right case zero suc rec)
          (u Tm78 var78 lam78 app78 tt78 pair78 fst snd left right case zero suc rec).

Definition fst78 {Γ A B} : Tm78 Γ (prod78 A B) → Tm78 Γ A
 := λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd left right case zero suc rec ,
     fst78 _ _ _
         (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd left right case zero suc rec).

Definition snd78 {Γ A B} : Tm78 Γ (prod78 A B) → Tm78 Γ B
 := λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left right case zero suc rec ,
     snd78 _ _ _
          (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left right case zero suc rec).

Definition left78 {Γ A B} : Tm78 Γ A → Tm78 Γ (sum78 A B)
 := λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right case zero suc rec ,
     left78 _ _ _
          (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right case zero suc rec).

Definition right78 {Γ A B} : Tm78 Γ B → Tm78 Γ (sum78 A B)
 := λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case zero suc rec ,
     right78 _ _ _
            (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case zero suc rec).

Definition case78 {Γ A B C} : Tm78 Γ (sum78 A B) → Tm78 Γ (arr78 A C) → Tm78 Γ (arr78 B C) → Tm78 Γ C
 := λ t u v Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero suc rec ,
     case78 _ _ _ _
           (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero suc rec)
           (u Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero suc rec)
           (v Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero suc rec).

Definition zero78  {Γ} : Tm78 Γ nat78
 := λ Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc rec , zero78 _.

Definition suc78 {Γ} : Tm78 Γ nat78 → Tm78 Γ nat78
 := λ t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec ,
   suc78 _ (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec).

Definition rec78 {Γ A} : Tm78 Γ nat78 → Tm78 Γ (arr78 nat78 (arr78 A A)) → Tm78 Γ A → Tm78 Γ A
 := λ t u v Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec78 ,
     rec78 _ _
         (t Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec78)
         (u Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec78)
         (v Tm78 var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 case78 zero78 suc78 rec78).

Definition v078 {Γ A} : Tm78 (snoc78 Γ A) A
 := var78 vz78.

Definition v178 {Γ A B} : Tm78 (snoc78 (snoc78 Γ A) B) A
 := var78 (vs78 vz78).

Definition v278 {Γ A B C} : Tm78 (snoc78 (snoc78 (snoc78 Γ A) B) C) A
 := var78 (vs78 (vs78 vz78)).

Definition v378 {Γ A B C D} : Tm78 (snoc78 (snoc78 (snoc78 (snoc78 Γ A) B) C) D) A
 := var78 (vs78 (vs78 (vs78 vz78))).

Definition tbool78 : Ty78
 := sum78 top78 top78.

Definition ttrue78 {Γ} : Tm78 Γ tbool78
 := left78 tt78.

Definition tfalse78 {Γ} : Tm78 Γ tbool78
 := right78 tt78.

Definition ifthenelse78 {Γ A} : Tm78 Γ (arr78 tbool78 (arr78 A (arr78 A A)))
 := lam78 (lam78 (lam78 (case78 v278 (lam78 v278) (lam78 v178)))).

Definition times478 {Γ A} : Tm78 Γ (arr78 (arr78 A A) (arr78 A A))
  := lam78 (lam78 (app78 v178 (app78 v178 (app78 v178 (app78 v178 v078))))).

Definition add78 {Γ} : Tm78 Γ (arr78 nat78 (arr78 nat78 nat78))
 := lam78 (rec78 v078
      (lam78 (lam78 (lam78 (suc78 (app78 v178 v078)))))
      (lam78 v078)).

Definition mul78 {Γ} : Tm78 Γ (arr78 nat78 (arr78 nat78 nat78))
 := lam78 (rec78 v078
     (lam78 (lam78 (lam78 (app78 (app78 add78 (app78 v178 v078)) v078))))
     (lam78 zero78)).

Definition fact78 {Γ} : Tm78 Γ (arr78 nat78 nat78)
 := lam78 (rec78 v078 (lam78 (lam78 (app78 (app78 mul78 (suc78 v178)) v078)))
        (suc78 zero78)).

Require Import Coq.Unicode.Utf8.

Definition Ty79 : Set
 := ∀ (Ty79           : Set)
      (nat top bot  : Ty79)
      (arr prod sum : Ty79 → Ty79 → Ty79)
    , Ty79.

Definition nat79 : Ty79 := λ _ nat79 _ _ _ _ _ , nat79.
Definition top79 : Ty79 := λ _ _ top79 _ _ _ _ , top79.
Definition bot79 : Ty79 := λ _ _ _ bot79 _ _ _ , bot79.

Definition arr79 : Ty79 → Ty79 → Ty79
 := λ A B Ty79 nat79 top79 bot79 arr79 prod sum ,
     arr79 (A Ty79 nat79 top79 bot79 arr79 prod sum) (B Ty79 nat79 top79 bot79 arr79 prod sum).

Definition prod79 : Ty79 → Ty79 → Ty79
 := λ A B Ty79 nat79 top79 bot79 arr79 prod79 sum ,
     prod79 (A Ty79 nat79 top79 bot79 arr79 prod79 sum) (B Ty79 nat79 top79 bot79 arr79 prod79 sum).

Definition sum79 : Ty79 → Ty79 → Ty79
 := λ A B Ty79 nat79 top79 bot79 arr79 prod79 sum79 ,
     sum79 (A Ty79 nat79 top79 bot79 arr79 prod79 sum79) (B Ty79 nat79 top79 bot79 arr79 prod79 sum79).

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
     (tt    : ∀ Γ       , Tm79 Γ top79)
     (pair  : ∀ Γ A B   , Tm79 Γ A → Tm79 Γ B → Tm79 Γ (prod79 A B))
     (fst   : ∀ Γ A B   , Tm79 Γ (prod79 A B) → Tm79 Γ A)
     (snd   : ∀ Γ A B   , Tm79 Γ (prod79 A B) → Tm79 Γ B)
     (left  : ∀ Γ A B   , Tm79 Γ A → Tm79 Γ (sum79 A B))
     (right : ∀ Γ A B   , Tm79 Γ B → Tm79 Γ (sum79 A B))
     (case  : ∀ Γ A B C , Tm79 Γ (sum79 A B) → Tm79 Γ (arr79 A C) → Tm79 Γ (arr79 B C) → Tm79 Γ C)
     (zero  : ∀ Γ       , Tm79 Γ nat79)
     (suc   : ∀ Γ       , Tm79 Γ nat79 → Tm79 Γ nat79)
     (rec   : ∀ Γ A     , Tm79 Γ nat79 → Tm79 Γ (arr79 nat79 (arr79 A A)) → Tm79 Γ A → Tm79 Γ A)
   , Tm79 Γ A.

Definition var79 {Γ A} : Var79 Γ A → Tm79 Γ A
 := λ x Tm79 var79 lam app tt pair fst snd left right case zero suc rec ,
     var79 _ _ x.

Definition lam79 {Γ A B} : Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B)
 := λ t Tm79 var79 lam79 app tt pair fst snd left right case zero suc rec ,
     lam79 _ _ _ (t Tm79 var79 lam79 app tt pair fst snd left right case zero suc rec).

Definition app79 {Γ A B} : Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B
 := λ t u Tm79 var79 lam79 app79 tt pair fst snd left right case zero suc rec ,
     app79 _ _ _
         (t Tm79 var79 lam79 app79 tt pair fst snd left right case zero suc rec)
         (u Tm79 var79 lam79 app79 tt pair fst snd left right case zero suc rec).

Definition tt79 {Γ} : Tm79 Γ top79
 := λ Tm79 var79 lam79 app79 tt79 pair fst snd left right case zero suc rec , tt79 _.

Definition pair79 {Γ A B} : Tm79 Γ A → Tm79 Γ B → Tm79 Γ (prod79 A B)
 := λ t u Tm79 var79 lam79 app79 tt79 pair79 fst snd left right case zero suc rec ,
     pair79 _ _ _
          (t Tm79 var79 lam79 app79 tt79 pair79 fst snd left right case zero suc rec)
          (u Tm79 var79 lam79 app79 tt79 pair79 fst snd left right case zero suc rec).

Definition fst79 {Γ A B} : Tm79 Γ (prod79 A B) → Tm79 Γ A
 := λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd left right case zero suc rec ,
     fst79 _ _ _
         (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd left right case zero suc rec).

Definition snd79 {Γ A B} : Tm79 Γ (prod79 A B) → Tm79 Γ B
 := λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left right case zero suc rec ,
     snd79 _ _ _
          (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left right case zero suc rec).

Definition left79 {Γ A B} : Tm79 Γ A → Tm79 Γ (sum79 A B)
 := λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right case zero suc rec ,
     left79 _ _ _
          (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right case zero suc rec).

Definition right79 {Γ A B} : Tm79 Γ B → Tm79 Γ (sum79 A B)
 := λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case zero suc rec ,
     right79 _ _ _
            (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case zero suc rec).

Definition case79 {Γ A B C} : Tm79 Γ (sum79 A B) → Tm79 Γ (arr79 A C) → Tm79 Γ (arr79 B C) → Tm79 Γ C
 := λ t u v Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero suc rec ,
     case79 _ _ _ _
           (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero suc rec)
           (u Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero suc rec)
           (v Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero suc rec).

Definition zero79  {Γ} : Tm79 Γ nat79
 := λ Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc rec , zero79 _.

Definition suc79 {Γ} : Tm79 Γ nat79 → Tm79 Γ nat79
 := λ t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec ,
   suc79 _ (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec).

Definition rec79 {Γ A} : Tm79 Γ nat79 → Tm79 Γ (arr79 nat79 (arr79 A A)) → Tm79 Γ A → Tm79 Γ A
 := λ t u v Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec79 ,
     rec79 _ _
         (t Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec79)
         (u Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec79)
         (v Tm79 var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 case79 zero79 suc79 rec79).

Definition v079 {Γ A} : Tm79 (snoc79 Γ A) A
 := var79 vz79.

Definition v179 {Γ A B} : Tm79 (snoc79 (snoc79 Γ A) B) A
 := var79 (vs79 vz79).

Definition v279 {Γ A B C} : Tm79 (snoc79 (snoc79 (snoc79 Γ A) B) C) A
 := var79 (vs79 (vs79 vz79)).

Definition v379 {Γ A B C D} : Tm79 (snoc79 (snoc79 (snoc79 (snoc79 Γ A) B) C) D) A
 := var79 (vs79 (vs79 (vs79 vz79))).

Definition tbool79 : Ty79
 := sum79 top79 top79.

Definition ttrue79 {Γ} : Tm79 Γ tbool79
 := left79 tt79.

Definition tfalse79 {Γ} : Tm79 Γ tbool79
 := right79 tt79.

Definition ifthenelse79 {Γ A} : Tm79 Γ (arr79 tbool79 (arr79 A (arr79 A A)))
 := lam79 (lam79 (lam79 (case79 v279 (lam79 v279) (lam79 v179)))).

Definition times479 {Γ A} : Tm79 Γ (arr79 (arr79 A A) (arr79 A A))
  := lam79 (lam79 (app79 v179 (app79 v179 (app79 v179 (app79 v179 v079))))).

Definition add79 {Γ} : Tm79 Γ (arr79 nat79 (arr79 nat79 nat79))
 := lam79 (rec79 v079
      (lam79 (lam79 (lam79 (suc79 (app79 v179 v079)))))
      (lam79 v079)).

Definition mul79 {Γ} : Tm79 Γ (arr79 nat79 (arr79 nat79 nat79))
 := lam79 (rec79 v079
     (lam79 (lam79 (lam79 (app79 (app79 add79 (app79 v179 v079)) v079))))
     (lam79 zero79)).

Definition fact79 {Γ} : Tm79 Γ (arr79 nat79 nat79)
 := lam79 (rec79 v079 (lam79 (lam79 (app79 (app79 mul79 (suc79 v179)) v079)))
        (suc79 zero79)).

