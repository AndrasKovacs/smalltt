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
