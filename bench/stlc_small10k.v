
Definition Ty : Set
 := forall (Ty : Set)
      (base   : Ty)
      (arr : Ty -> Ty -> Ty)
    , Ty.

Definition base : Ty := fun _ base _ => base.

Definition arr : Ty -> Ty -> Ty
 := fun A B Ty base arr =>
     arr (A Ty base arr) (B Ty base arr).

Definition Con : Set
 := forall (Con  : Set)
      (nil  : Con)
      (snoc : Con -> Ty -> Con)
    , Con.

Definition nil : Con
 := fun Con nil snoc => nil.

Definition snoc : Con -> Ty -> Con
 := fun Γ A Con nil snoc => snoc (Γ Con nil snoc) A.

Definition Var : Con -> Ty -> Set
 := fun Γ A =>
   forall (Var : Con -> Ty -> Set)
     (vz  : forall Γ A, Var (snoc Γ A) A)
     (vs  : forall Γ B A, Var Γ A -> Var (snoc Γ B) A)
   , Var Γ A.

Definition vz {Γ A} : Var (snoc Γ A) A
 := fun Var vz vs => vz _ _.

Definition vs {Γ B A} : Var Γ A -> Var (snoc Γ B) A
 := fun x Var vz vs => vs _ _ _ (x Var vz vs).

Definition Tm : Con -> Ty -> Set
 := fun Γ A =>
   forall (Tm  : Con -> Ty -> Set)
     (var   : forall Γ A     , Var Γ A -> Tm Γ A)
     (lam   : forall Γ A B   , Tm (snoc Γ A) B -> Tm Γ (arr A B))
     (app   : forall Γ A B   , Tm Γ (arr A B) -> Tm Γ A -> Tm Γ B)
   , Tm Γ A.

Definition var {Γ A} : Var Γ A -> Tm Γ A
 := fun x Tm var lam app =>
     var _ _ x.

Definition lam {Γ A B} : Tm (snoc Γ A) B -> Tm Γ (arr A B)
 := fun t Tm var lam app =>
     lam _ _ _ (t Tm var lam app).

Definition app {Γ A B} : Tm Γ (arr A B) -> Tm Γ A -> Tm Γ B
 := fun t u Tm var lam app =>
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


Definition Ty1 : Set
 := forall (Ty1 : Set)
      (base   : Ty1)
      (arr : Ty1 -> Ty1 -> Ty1)
    , Ty1.

Definition base1 : Ty1 := fun _ base1 _ => base1.

Definition arr1 : Ty1 -> Ty1 -> Ty1
 := fun A B Ty1 base1 arr1 =>
     arr1 (A Ty1 base1 arr1) (B Ty1 base1 arr1).

Definition Con1 : Set
 := forall (Con1  : Set)
      (nil  : Con1)
      (snoc : Con1 -> Ty1 -> Con1)
    , Con1.

Definition nil1 : Con1
 := fun Con1 nil1 snoc => nil1.

Definition snoc1 : Con1 -> Ty1 -> Con1
 := fun Γ A Con1 nil1 snoc1 => snoc1 (Γ Con1 nil1 snoc1) A.

Definition Var1 : Con1 -> Ty1 -> Set
 := fun Γ A =>
   forall (Var1 : Con1 -> Ty1 -> Set)
     (vz  : forall Γ A, Var1 (snoc1 Γ A) A)
     (vs  : forall Γ B A, Var1 Γ A -> Var1 (snoc1 Γ B) A)
   , Var1 Γ A.

Definition vz1 {Γ A} : Var1 (snoc1 Γ A) A
 := fun Var1 vz1 vs => vz1 _ _.

Definition vs1 {Γ B A} : Var1 Γ A -> Var1 (snoc1 Γ B) A
 := fun x Var1 vz1 vs1 => vs1 _ _ _ (x Var1 vz1 vs1).

Definition Tm1 : Con1 -> Ty1 -> Set
 := fun Γ A =>
   forall (Tm1  : Con1 -> Ty1 -> Set)
     (var   : forall Γ A     , Var1 Γ A -> Tm1 Γ A)
     (lam   : forall Γ A B   , Tm1 (snoc1 Γ A) B -> Tm1 Γ (arr1 A B))
     (app   : forall Γ A B   , Tm1 Γ (arr1 A B) -> Tm1 Γ A -> Tm1 Γ B)
   , Tm1 Γ A.

Definition var1 {Γ A} : Var1 Γ A -> Tm1 Γ A
 := fun x Tm1 var1 lam app =>
     var1 _ _ x.

Definition lam1 {Γ A B} : Tm1 (snoc1 Γ A) B -> Tm1 Γ (arr1 A B)
 := fun t Tm1 var1 lam1 app =>
     lam1 _ _ _ (t Tm1 var1 lam1 app).

Definition app1 {Γ A B} : Tm1 Γ (arr1 A B) -> Tm1 Γ A -> Tm1 Γ B
 := fun t u Tm1 var1 lam1 app1 =>
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


Definition Ty2 : Set
 := forall (Ty2 : Set)
      (base   : Ty2)
      (arr : Ty2 -> Ty2 -> Ty2)
    , Ty2.

Definition base2 : Ty2 := fun _ base2 _ => base2.

Definition arr2 : Ty2 -> Ty2 -> Ty2
 := fun A B Ty2 base2 arr2 =>
     arr2 (A Ty2 base2 arr2) (B Ty2 base2 arr2).

Definition Con2 : Set
 := forall (Con2  : Set)
      (nil  : Con2)
      (snoc : Con2 -> Ty2 -> Con2)
    , Con2.

Definition nil2 : Con2
 := fun Con2 nil2 snoc => nil2.

Definition snoc2 : Con2 -> Ty2 -> Con2
 := fun Γ A Con2 nil2 snoc2 => snoc2 (Γ Con2 nil2 snoc2) A.

Definition Var2 : Con2 -> Ty2 -> Set
 := fun Γ A =>
   forall (Var2 : Con2 -> Ty2 -> Set)
     (vz  : forall Γ A, Var2 (snoc2 Γ A) A)
     (vs  : forall Γ B A, Var2 Γ A -> Var2 (snoc2 Γ B) A)
   , Var2 Γ A.

Definition vz2 {Γ A} : Var2 (snoc2 Γ A) A
 := fun Var2 vz2 vs => vz2 _ _.

Definition vs2 {Γ B A} : Var2 Γ A -> Var2 (snoc2 Γ B) A
 := fun x Var2 vz2 vs2 => vs2 _ _ _ (x Var2 vz2 vs2).

Definition Tm2 : Con2 -> Ty2 -> Set
 := fun Γ A =>
   forall (Tm2  : Con2 -> Ty2 -> Set)
     (var   : forall Γ A     , Var2 Γ A -> Tm2 Γ A)
     (lam   : forall Γ A B   , Tm2 (snoc2 Γ A) B -> Tm2 Γ (arr2 A B))
     (app   : forall Γ A B   , Tm2 Γ (arr2 A B) -> Tm2 Γ A -> Tm2 Γ B)
   , Tm2 Γ A.

Definition var2 {Γ A} : Var2 Γ A -> Tm2 Γ A
 := fun x Tm2 var2 lam app =>
     var2 _ _ x.

Definition lam2 {Γ A B} : Tm2 (snoc2 Γ A) B -> Tm2 Γ (arr2 A B)
 := fun t Tm2 var2 lam2 app =>
     lam2 _ _ _ (t Tm2 var2 lam2 app).

Definition app2 {Γ A B} : Tm2 Γ (arr2 A B) -> Tm2 Γ A -> Tm2 Γ B
 := fun t u Tm2 var2 lam2 app2 =>
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


Definition Ty3 : Set
 := forall (Ty3 : Set)
      (base   : Ty3)
      (arr : Ty3 -> Ty3 -> Ty3)
    , Ty3.

Definition base3 : Ty3 := fun _ base3 _ => base3.

Definition arr3 : Ty3 -> Ty3 -> Ty3
 := fun A B Ty3 base3 arr3 =>
     arr3 (A Ty3 base3 arr3) (B Ty3 base3 arr3).

Definition Con3 : Set
 := forall (Con3  : Set)
      (nil  : Con3)
      (snoc : Con3 -> Ty3 -> Con3)
    , Con3.

Definition nil3 : Con3
 := fun Con3 nil3 snoc => nil3.

Definition snoc3 : Con3 -> Ty3 -> Con3
 := fun Γ A Con3 nil3 snoc3 => snoc3 (Γ Con3 nil3 snoc3) A.

Definition Var3 : Con3 -> Ty3 -> Set
 := fun Γ A =>
   forall (Var3 : Con3 -> Ty3 -> Set)
     (vz  : forall Γ A, Var3 (snoc3 Γ A) A)
     (vs  : forall Γ B A, Var3 Γ A -> Var3 (snoc3 Γ B) A)
   , Var3 Γ A.

Definition vz3 {Γ A} : Var3 (snoc3 Γ A) A
 := fun Var3 vz3 vs => vz3 _ _.

Definition vs3 {Γ B A} : Var3 Γ A -> Var3 (snoc3 Γ B) A
 := fun x Var3 vz3 vs3 => vs3 _ _ _ (x Var3 vz3 vs3).

Definition Tm3 : Con3 -> Ty3 -> Set
 := fun Γ A =>
   forall (Tm3  : Con3 -> Ty3 -> Set)
     (var   : forall Γ A     , Var3 Γ A -> Tm3 Γ A)
     (lam   : forall Γ A B   , Tm3 (snoc3 Γ A) B -> Tm3 Γ (arr3 A B))
     (app   : forall Γ A B   , Tm3 Γ (arr3 A B) -> Tm3 Γ A -> Tm3 Γ B)
   , Tm3 Γ A.

Definition var3 {Γ A} : Var3 Γ A -> Tm3 Γ A
 := fun x Tm3 var3 lam app =>
     var3 _ _ x.

Definition lam3 {Γ A B} : Tm3 (snoc3 Γ A) B -> Tm3 Γ (arr3 A B)
 := fun t Tm3 var3 lam3 app =>
     lam3 _ _ _ (t Tm3 var3 lam3 app).

Definition app3 {Γ A B} : Tm3 Γ (arr3 A B) -> Tm3 Γ A -> Tm3 Γ B
 := fun t u Tm3 var3 lam3 app3 =>
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


Definition Ty4 : Set
 := forall (Ty4 : Set)
      (base   : Ty4)
      (arr : Ty4 -> Ty4 -> Ty4)
    , Ty4.

Definition base4 : Ty4 := fun _ base4 _ => base4.

Definition arr4 : Ty4 -> Ty4 -> Ty4
 := fun A B Ty4 base4 arr4 =>
     arr4 (A Ty4 base4 arr4) (B Ty4 base4 arr4).

Definition Con4 : Set
 := forall (Con4  : Set)
      (nil  : Con4)
      (snoc : Con4 -> Ty4 -> Con4)
    , Con4.

Definition nil4 : Con4
 := fun Con4 nil4 snoc => nil4.

Definition snoc4 : Con4 -> Ty4 -> Con4
 := fun Γ A Con4 nil4 snoc4 => snoc4 (Γ Con4 nil4 snoc4) A.

Definition Var4 : Con4 -> Ty4 -> Set
 := fun Γ A =>
   forall (Var4 : Con4 -> Ty4 -> Set)
     (vz  : forall Γ A, Var4 (snoc4 Γ A) A)
     (vs  : forall Γ B A, Var4 Γ A -> Var4 (snoc4 Γ B) A)
   , Var4 Γ A.

Definition vz4 {Γ A} : Var4 (snoc4 Γ A) A
 := fun Var4 vz4 vs => vz4 _ _.

Definition vs4 {Γ B A} : Var4 Γ A -> Var4 (snoc4 Γ B) A
 := fun x Var4 vz4 vs4 => vs4 _ _ _ (x Var4 vz4 vs4).

Definition Tm4 : Con4 -> Ty4 -> Set
 := fun Γ A =>
   forall (Tm4  : Con4 -> Ty4 -> Set)
     (var   : forall Γ A     , Var4 Γ A -> Tm4 Γ A)
     (lam   : forall Γ A B   , Tm4 (snoc4 Γ A) B -> Tm4 Γ (arr4 A B))
     (app   : forall Γ A B   , Tm4 Γ (arr4 A B) -> Tm4 Γ A -> Tm4 Γ B)
   , Tm4 Γ A.

Definition var4 {Γ A} : Var4 Γ A -> Tm4 Γ A
 := fun x Tm4 var4 lam app =>
     var4 _ _ x.

Definition lam4 {Γ A B} : Tm4 (snoc4 Γ A) B -> Tm4 Γ (arr4 A B)
 := fun t Tm4 var4 lam4 app =>
     lam4 _ _ _ (t Tm4 var4 lam4 app).

Definition app4 {Γ A B} : Tm4 Γ (arr4 A B) -> Tm4 Γ A -> Tm4 Γ B
 := fun t u Tm4 var4 lam4 app4 =>
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


Definition Ty5 : Set
 := forall (Ty5 : Set)
      (base   : Ty5)
      (arr : Ty5 -> Ty5 -> Ty5)
    , Ty5.

Definition base5 : Ty5 := fun _ base5 _ => base5.

Definition arr5 : Ty5 -> Ty5 -> Ty5
 := fun A B Ty5 base5 arr5 =>
     arr5 (A Ty5 base5 arr5) (B Ty5 base5 arr5).

Definition Con5 : Set
 := forall (Con5  : Set)
      (nil  : Con5)
      (snoc : Con5 -> Ty5 -> Con5)
    , Con5.

Definition nil5 : Con5
 := fun Con5 nil5 snoc => nil5.

Definition snoc5 : Con5 -> Ty5 -> Con5
 := fun Γ A Con5 nil5 snoc5 => snoc5 (Γ Con5 nil5 snoc5) A.

Definition Var5 : Con5 -> Ty5 -> Set
 := fun Γ A =>
   forall (Var5 : Con5 -> Ty5 -> Set)
     (vz  : forall Γ A, Var5 (snoc5 Γ A) A)
     (vs  : forall Γ B A, Var5 Γ A -> Var5 (snoc5 Γ B) A)
   , Var5 Γ A.

Definition vz5 {Γ A} : Var5 (snoc5 Γ A) A
 := fun Var5 vz5 vs => vz5 _ _.

Definition vs5 {Γ B A} : Var5 Γ A -> Var5 (snoc5 Γ B) A
 := fun x Var5 vz5 vs5 => vs5 _ _ _ (x Var5 vz5 vs5).

Definition Tm5 : Con5 -> Ty5 -> Set
 := fun Γ A =>
   forall (Tm5  : Con5 -> Ty5 -> Set)
     (var   : forall Γ A     , Var5 Γ A -> Tm5 Γ A)
     (lam   : forall Γ A B   , Tm5 (snoc5 Γ A) B -> Tm5 Γ (arr5 A B))
     (app   : forall Γ A B   , Tm5 Γ (arr5 A B) -> Tm5 Γ A -> Tm5 Γ B)
   , Tm5 Γ A.

Definition var5 {Γ A} : Var5 Γ A -> Tm5 Γ A
 := fun x Tm5 var5 lam app =>
     var5 _ _ x.

Definition lam5 {Γ A B} : Tm5 (snoc5 Γ A) B -> Tm5 Γ (arr5 A B)
 := fun t Tm5 var5 lam5 app =>
     lam5 _ _ _ (t Tm5 var5 lam5 app).

Definition app5 {Γ A B} : Tm5 Γ (arr5 A B) -> Tm5 Γ A -> Tm5 Γ B
 := fun t u Tm5 var5 lam5 app5 =>
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


Definition Ty6 : Set
 := forall (Ty6 : Set)
      (base   : Ty6)
      (arr : Ty6 -> Ty6 -> Ty6)
    , Ty6.

Definition base6 : Ty6 := fun _ base6 _ => base6.

Definition arr6 : Ty6 -> Ty6 -> Ty6
 := fun A B Ty6 base6 arr6 =>
     arr6 (A Ty6 base6 arr6) (B Ty6 base6 arr6).

Definition Con6 : Set
 := forall (Con6  : Set)
      (nil  : Con6)
      (snoc : Con6 -> Ty6 -> Con6)
    , Con6.

Definition nil6 : Con6
 := fun Con6 nil6 snoc => nil6.

Definition snoc6 : Con6 -> Ty6 -> Con6
 := fun Γ A Con6 nil6 snoc6 => snoc6 (Γ Con6 nil6 snoc6) A.

Definition Var6 : Con6 -> Ty6 -> Set
 := fun Γ A =>
   forall (Var6 : Con6 -> Ty6 -> Set)
     (vz  : forall Γ A, Var6 (snoc6 Γ A) A)
     (vs  : forall Γ B A, Var6 Γ A -> Var6 (snoc6 Γ B) A)
   , Var6 Γ A.

Definition vz6 {Γ A} : Var6 (snoc6 Γ A) A
 := fun Var6 vz6 vs => vz6 _ _.

Definition vs6 {Γ B A} : Var6 Γ A -> Var6 (snoc6 Γ B) A
 := fun x Var6 vz6 vs6 => vs6 _ _ _ (x Var6 vz6 vs6).

Definition Tm6 : Con6 -> Ty6 -> Set
 := fun Γ A =>
   forall (Tm6  : Con6 -> Ty6 -> Set)
     (var   : forall Γ A     , Var6 Γ A -> Tm6 Γ A)
     (lam   : forall Γ A B   , Tm6 (snoc6 Γ A) B -> Tm6 Γ (arr6 A B))
     (app   : forall Γ A B   , Tm6 Γ (arr6 A B) -> Tm6 Γ A -> Tm6 Γ B)
   , Tm6 Γ A.

Definition var6 {Γ A} : Var6 Γ A -> Tm6 Γ A
 := fun x Tm6 var6 lam app =>
     var6 _ _ x.

Definition lam6 {Γ A B} : Tm6 (snoc6 Γ A) B -> Tm6 Γ (arr6 A B)
 := fun t Tm6 var6 lam6 app =>
     lam6 _ _ _ (t Tm6 var6 lam6 app).

Definition app6 {Γ A B} : Tm6 Γ (arr6 A B) -> Tm6 Γ A -> Tm6 Γ B
 := fun t u Tm6 var6 lam6 app6 =>
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


Definition Ty7 : Set
 := forall (Ty7 : Set)
      (base   : Ty7)
      (arr : Ty7 -> Ty7 -> Ty7)
    , Ty7.

Definition base7 : Ty7 := fun _ base7 _ => base7.

Definition arr7 : Ty7 -> Ty7 -> Ty7
 := fun A B Ty7 base7 arr7 =>
     arr7 (A Ty7 base7 arr7) (B Ty7 base7 arr7).

Definition Con7 : Set
 := forall (Con7  : Set)
      (nil  : Con7)
      (snoc : Con7 -> Ty7 -> Con7)
    , Con7.

Definition nil7 : Con7
 := fun Con7 nil7 snoc => nil7.

Definition snoc7 : Con7 -> Ty7 -> Con7
 := fun Γ A Con7 nil7 snoc7 => snoc7 (Γ Con7 nil7 snoc7) A.

Definition Var7 : Con7 -> Ty7 -> Set
 := fun Γ A =>
   forall (Var7 : Con7 -> Ty7 -> Set)
     (vz  : forall Γ A, Var7 (snoc7 Γ A) A)
     (vs  : forall Γ B A, Var7 Γ A -> Var7 (snoc7 Γ B) A)
   , Var7 Γ A.

Definition vz7 {Γ A} : Var7 (snoc7 Γ A) A
 := fun Var7 vz7 vs => vz7 _ _.

Definition vs7 {Γ B A} : Var7 Γ A -> Var7 (snoc7 Γ B) A
 := fun x Var7 vz7 vs7 => vs7 _ _ _ (x Var7 vz7 vs7).

Definition Tm7 : Con7 -> Ty7 -> Set
 := fun Γ A =>
   forall (Tm7  : Con7 -> Ty7 -> Set)
     (var   : forall Γ A     , Var7 Γ A -> Tm7 Γ A)
     (lam   : forall Γ A B   , Tm7 (snoc7 Γ A) B -> Tm7 Γ (arr7 A B))
     (app   : forall Γ A B   , Tm7 Γ (arr7 A B) -> Tm7 Γ A -> Tm7 Γ B)
   , Tm7 Γ A.

Definition var7 {Γ A} : Var7 Γ A -> Tm7 Γ A
 := fun x Tm7 var7 lam app =>
     var7 _ _ x.

Definition lam7 {Γ A B} : Tm7 (snoc7 Γ A) B -> Tm7 Γ (arr7 A B)
 := fun t Tm7 var7 lam7 app =>
     lam7 _ _ _ (t Tm7 var7 lam7 app).

Definition app7 {Γ A B} : Tm7 Γ (arr7 A B) -> Tm7 Γ A -> Tm7 Γ B
 := fun t u Tm7 var7 lam7 app7 =>
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


Definition Ty8 : Set
 := forall (Ty8 : Set)
      (base   : Ty8)
      (arr : Ty8 -> Ty8 -> Ty8)
    , Ty8.

Definition base8 : Ty8 := fun _ base8 _ => base8.

Definition arr8 : Ty8 -> Ty8 -> Ty8
 := fun A B Ty8 base8 arr8 =>
     arr8 (A Ty8 base8 arr8) (B Ty8 base8 arr8).

Definition Con8 : Set
 := forall (Con8  : Set)
      (nil  : Con8)
      (snoc : Con8 -> Ty8 -> Con8)
    , Con8.

Definition nil8 : Con8
 := fun Con8 nil8 snoc => nil8.

Definition snoc8 : Con8 -> Ty8 -> Con8
 := fun Γ A Con8 nil8 snoc8 => snoc8 (Γ Con8 nil8 snoc8) A.

Definition Var8 : Con8 -> Ty8 -> Set
 := fun Γ A =>
   forall (Var8 : Con8 -> Ty8 -> Set)
     (vz  : forall Γ A, Var8 (snoc8 Γ A) A)
     (vs  : forall Γ B A, Var8 Γ A -> Var8 (snoc8 Γ B) A)
   , Var8 Γ A.

Definition vz8 {Γ A} : Var8 (snoc8 Γ A) A
 := fun Var8 vz8 vs => vz8 _ _.

Definition vs8 {Γ B A} : Var8 Γ A -> Var8 (snoc8 Γ B) A
 := fun x Var8 vz8 vs8 => vs8 _ _ _ (x Var8 vz8 vs8).

Definition Tm8 : Con8 -> Ty8 -> Set
 := fun Γ A =>
   forall (Tm8  : Con8 -> Ty8 -> Set)
     (var   : forall Γ A     , Var8 Γ A -> Tm8 Γ A)
     (lam   : forall Γ A B   , Tm8 (snoc8 Γ A) B -> Tm8 Γ (arr8 A B))
     (app   : forall Γ A B   , Tm8 Γ (arr8 A B) -> Tm8 Γ A -> Tm8 Γ B)
   , Tm8 Γ A.

Definition var8 {Γ A} : Var8 Γ A -> Tm8 Γ A
 := fun x Tm8 var8 lam app =>
     var8 _ _ x.

Definition lam8 {Γ A B} : Tm8 (snoc8 Γ A) B -> Tm8 Γ (arr8 A B)
 := fun t Tm8 var8 lam8 app =>
     lam8 _ _ _ (t Tm8 var8 lam8 app).

Definition app8 {Γ A B} : Tm8 Γ (arr8 A B) -> Tm8 Γ A -> Tm8 Γ B
 := fun t u Tm8 var8 lam8 app8 =>
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


Definition Ty9 : Set
 := forall (Ty9 : Set)
      (base   : Ty9)
      (arr : Ty9 -> Ty9 -> Ty9)
    , Ty9.

Definition base9 : Ty9 := fun _ base9 _ => base9.

Definition arr9 : Ty9 -> Ty9 -> Ty9
 := fun A B Ty9 base9 arr9 =>
     arr9 (A Ty9 base9 arr9) (B Ty9 base9 arr9).

Definition Con9 : Set
 := forall (Con9  : Set)
      (nil  : Con9)
      (snoc : Con9 -> Ty9 -> Con9)
    , Con9.

Definition nil9 : Con9
 := fun Con9 nil9 snoc => nil9.

Definition snoc9 : Con9 -> Ty9 -> Con9
 := fun Γ A Con9 nil9 snoc9 => snoc9 (Γ Con9 nil9 snoc9) A.

Definition Var9 : Con9 -> Ty9 -> Set
 := fun Γ A =>
   forall (Var9 : Con9 -> Ty9 -> Set)
     (vz  : forall Γ A, Var9 (snoc9 Γ A) A)
     (vs  : forall Γ B A, Var9 Γ A -> Var9 (snoc9 Γ B) A)
   , Var9 Γ A.

Definition vz9 {Γ A} : Var9 (snoc9 Γ A) A
 := fun Var9 vz9 vs => vz9 _ _.

Definition vs9 {Γ B A} : Var9 Γ A -> Var9 (snoc9 Γ B) A
 := fun x Var9 vz9 vs9 => vs9 _ _ _ (x Var9 vz9 vs9).

Definition Tm9 : Con9 -> Ty9 -> Set
 := fun Γ A =>
   forall (Tm9  : Con9 -> Ty9 -> Set)
     (var   : forall Γ A     , Var9 Γ A -> Tm9 Γ A)
     (lam   : forall Γ A B   , Tm9 (snoc9 Γ A) B -> Tm9 Γ (arr9 A B))
     (app   : forall Γ A B   , Tm9 Γ (arr9 A B) -> Tm9 Γ A -> Tm9 Γ B)
   , Tm9 Γ A.

Definition var9 {Γ A} : Var9 Γ A -> Tm9 Γ A
 := fun x Tm9 var9 lam app =>
     var9 _ _ x.

Definition lam9 {Γ A B} : Tm9 (snoc9 Γ A) B -> Tm9 Γ (arr9 A B)
 := fun t Tm9 var9 lam9 app =>
     lam9 _ _ _ (t Tm9 var9 lam9 app).

Definition app9 {Γ A B} : Tm9 Γ (arr9 A B) -> Tm9 Γ A -> Tm9 Γ B
 := fun t u Tm9 var9 lam9 app9 =>
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


Definition Ty10 : Set
 := forall (Ty10 : Set)
      (base   : Ty10)
      (arr : Ty10 -> Ty10 -> Ty10)
    , Ty10.

Definition base10 : Ty10 := fun _ base10 _ => base10.

Definition arr10 : Ty10 -> Ty10 -> Ty10
 := fun A B Ty10 base10 arr10 =>
     arr10 (A Ty10 base10 arr10) (B Ty10 base10 arr10).

Definition Con10 : Set
 := forall (Con10  : Set)
      (nil  : Con10)
      (snoc : Con10 -> Ty10 -> Con10)
    , Con10.

Definition nil10 : Con10
 := fun Con10 nil10 snoc => nil10.

Definition snoc10 : Con10 -> Ty10 -> Con10
 := fun Γ A Con10 nil10 snoc10 => snoc10 (Γ Con10 nil10 snoc10) A.

Definition Var10 : Con10 -> Ty10 -> Set
 := fun Γ A =>
   forall (Var10 : Con10 -> Ty10 -> Set)
     (vz  : forall Γ A, Var10 (snoc10 Γ A) A)
     (vs  : forall Γ B A, Var10 Γ A -> Var10 (snoc10 Γ B) A)
   , Var10 Γ A.

Definition vz10 {Γ A} : Var10 (snoc10 Γ A) A
 := fun Var10 vz10 vs => vz10 _ _.

Definition vs10 {Γ B A} : Var10 Γ A -> Var10 (snoc10 Γ B) A
 := fun x Var10 vz10 vs10 => vs10 _ _ _ (x Var10 vz10 vs10).

Definition Tm10 : Con10 -> Ty10 -> Set
 := fun Γ A =>
   forall (Tm10  : Con10 -> Ty10 -> Set)
     (var   : forall Γ A     , Var10 Γ A -> Tm10 Γ A)
     (lam   : forall Γ A B   , Tm10 (snoc10 Γ A) B -> Tm10 Γ (arr10 A B))
     (app   : forall Γ A B   , Tm10 Γ (arr10 A B) -> Tm10 Γ A -> Tm10 Γ B)
   , Tm10 Γ A.

Definition var10 {Γ A} : Var10 Γ A -> Tm10 Γ A
 := fun x Tm10 var10 lam app =>
     var10 _ _ x.

Definition lam10 {Γ A B} : Tm10 (snoc10 Γ A) B -> Tm10 Γ (arr10 A B)
 := fun t Tm10 var10 lam10 app =>
     lam10 _ _ _ (t Tm10 var10 lam10 app).

Definition app10 {Γ A B} : Tm10 Γ (arr10 A B) -> Tm10 Γ A -> Tm10 Γ B
 := fun t u Tm10 var10 lam10 app10 =>
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


Definition Ty11 : Set
 := forall (Ty11 : Set)
      (base   : Ty11)
      (arr : Ty11 -> Ty11 -> Ty11)
    , Ty11.

Definition base11 : Ty11 := fun _ base11 _ => base11.

Definition arr11 : Ty11 -> Ty11 -> Ty11
 := fun A B Ty11 base11 arr11 =>
     arr11 (A Ty11 base11 arr11) (B Ty11 base11 arr11).

Definition Con11 : Set
 := forall (Con11  : Set)
      (nil  : Con11)
      (snoc : Con11 -> Ty11 -> Con11)
    , Con11.

Definition nil11 : Con11
 := fun Con11 nil11 snoc => nil11.

Definition snoc11 : Con11 -> Ty11 -> Con11
 := fun Γ A Con11 nil11 snoc11 => snoc11 (Γ Con11 nil11 snoc11) A.

Definition Var11 : Con11 -> Ty11 -> Set
 := fun Γ A =>
   forall (Var11 : Con11 -> Ty11 -> Set)
     (vz  : forall Γ A, Var11 (snoc11 Γ A) A)
     (vs  : forall Γ B A, Var11 Γ A -> Var11 (snoc11 Γ B) A)
   , Var11 Γ A.

Definition vz11 {Γ A} : Var11 (snoc11 Γ A) A
 := fun Var11 vz11 vs => vz11 _ _.

Definition vs11 {Γ B A} : Var11 Γ A -> Var11 (snoc11 Γ B) A
 := fun x Var11 vz11 vs11 => vs11 _ _ _ (x Var11 vz11 vs11).

Definition Tm11 : Con11 -> Ty11 -> Set
 := fun Γ A =>
   forall (Tm11  : Con11 -> Ty11 -> Set)
     (var   : forall Γ A     , Var11 Γ A -> Tm11 Γ A)
     (lam   : forall Γ A B   , Tm11 (snoc11 Γ A) B -> Tm11 Γ (arr11 A B))
     (app   : forall Γ A B   , Tm11 Γ (arr11 A B) -> Tm11 Γ A -> Tm11 Γ B)
   , Tm11 Γ A.

Definition var11 {Γ A} : Var11 Γ A -> Tm11 Γ A
 := fun x Tm11 var11 lam app =>
     var11 _ _ x.

Definition lam11 {Γ A B} : Tm11 (snoc11 Γ A) B -> Tm11 Γ (arr11 A B)
 := fun t Tm11 var11 lam11 app =>
     lam11 _ _ _ (t Tm11 var11 lam11 app).

Definition app11 {Γ A B} : Tm11 Γ (arr11 A B) -> Tm11 Γ A -> Tm11 Γ B
 := fun t u Tm11 var11 lam11 app11 =>
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


Definition Ty12 : Set
 := forall (Ty12 : Set)
      (base   : Ty12)
      (arr : Ty12 -> Ty12 -> Ty12)
    , Ty12.

Definition base12 : Ty12 := fun _ base12 _ => base12.

Definition arr12 : Ty12 -> Ty12 -> Ty12
 := fun A B Ty12 base12 arr12 =>
     arr12 (A Ty12 base12 arr12) (B Ty12 base12 arr12).

Definition Con12 : Set
 := forall (Con12  : Set)
      (nil  : Con12)
      (snoc : Con12 -> Ty12 -> Con12)
    , Con12.

Definition nil12 : Con12
 := fun Con12 nil12 snoc => nil12.

Definition snoc12 : Con12 -> Ty12 -> Con12
 := fun Γ A Con12 nil12 snoc12 => snoc12 (Γ Con12 nil12 snoc12) A.

Definition Var12 : Con12 -> Ty12 -> Set
 := fun Γ A =>
   forall (Var12 : Con12 -> Ty12 -> Set)
     (vz  : forall Γ A, Var12 (snoc12 Γ A) A)
     (vs  : forall Γ B A, Var12 Γ A -> Var12 (snoc12 Γ B) A)
   , Var12 Γ A.

Definition vz12 {Γ A} : Var12 (snoc12 Γ A) A
 := fun Var12 vz12 vs => vz12 _ _.

Definition vs12 {Γ B A} : Var12 Γ A -> Var12 (snoc12 Γ B) A
 := fun x Var12 vz12 vs12 => vs12 _ _ _ (x Var12 vz12 vs12).

Definition Tm12 : Con12 -> Ty12 -> Set
 := fun Γ A =>
   forall (Tm12  : Con12 -> Ty12 -> Set)
     (var   : forall Γ A     , Var12 Γ A -> Tm12 Γ A)
     (lam   : forall Γ A B   , Tm12 (snoc12 Γ A) B -> Tm12 Γ (arr12 A B))
     (app   : forall Γ A B   , Tm12 Γ (arr12 A B) -> Tm12 Γ A -> Tm12 Γ B)
   , Tm12 Γ A.

Definition var12 {Γ A} : Var12 Γ A -> Tm12 Γ A
 := fun x Tm12 var12 lam app =>
     var12 _ _ x.

Definition lam12 {Γ A B} : Tm12 (snoc12 Γ A) B -> Tm12 Γ (arr12 A B)
 := fun t Tm12 var12 lam12 app =>
     lam12 _ _ _ (t Tm12 var12 lam12 app).

Definition app12 {Γ A B} : Tm12 Γ (arr12 A B) -> Tm12 Γ A -> Tm12 Γ B
 := fun t u Tm12 var12 lam12 app12 =>
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


Definition Ty13 : Set
 := forall (Ty13 : Set)
      (base   : Ty13)
      (arr : Ty13 -> Ty13 -> Ty13)
    , Ty13.

Definition base13 : Ty13 := fun _ base13 _ => base13.

Definition arr13 : Ty13 -> Ty13 -> Ty13
 := fun A B Ty13 base13 arr13 =>
     arr13 (A Ty13 base13 arr13) (B Ty13 base13 arr13).

Definition Con13 : Set
 := forall (Con13  : Set)
      (nil  : Con13)
      (snoc : Con13 -> Ty13 -> Con13)
    , Con13.

Definition nil13 : Con13
 := fun Con13 nil13 snoc => nil13.

Definition snoc13 : Con13 -> Ty13 -> Con13
 := fun Γ A Con13 nil13 snoc13 => snoc13 (Γ Con13 nil13 snoc13) A.

Definition Var13 : Con13 -> Ty13 -> Set
 := fun Γ A =>
   forall (Var13 : Con13 -> Ty13 -> Set)
     (vz  : forall Γ A, Var13 (snoc13 Γ A) A)
     (vs  : forall Γ B A, Var13 Γ A -> Var13 (snoc13 Γ B) A)
   , Var13 Γ A.

Definition vz13 {Γ A} : Var13 (snoc13 Γ A) A
 := fun Var13 vz13 vs => vz13 _ _.

Definition vs13 {Γ B A} : Var13 Γ A -> Var13 (snoc13 Γ B) A
 := fun x Var13 vz13 vs13 => vs13 _ _ _ (x Var13 vz13 vs13).

Definition Tm13 : Con13 -> Ty13 -> Set
 := fun Γ A =>
   forall (Tm13  : Con13 -> Ty13 -> Set)
     (var   : forall Γ A     , Var13 Γ A -> Tm13 Γ A)
     (lam   : forall Γ A B   , Tm13 (snoc13 Γ A) B -> Tm13 Γ (arr13 A B))
     (app   : forall Γ A B   , Tm13 Γ (arr13 A B) -> Tm13 Γ A -> Tm13 Γ B)
   , Tm13 Γ A.

Definition var13 {Γ A} : Var13 Γ A -> Tm13 Γ A
 := fun x Tm13 var13 lam app =>
     var13 _ _ x.

Definition lam13 {Γ A B} : Tm13 (snoc13 Γ A) B -> Tm13 Γ (arr13 A B)
 := fun t Tm13 var13 lam13 app =>
     lam13 _ _ _ (t Tm13 var13 lam13 app).

Definition app13 {Γ A B} : Tm13 Γ (arr13 A B) -> Tm13 Γ A -> Tm13 Γ B
 := fun t u Tm13 var13 lam13 app13 =>
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


Definition Ty14 : Set
 := forall (Ty14 : Set)
      (base   : Ty14)
      (arr : Ty14 -> Ty14 -> Ty14)
    , Ty14.

Definition base14 : Ty14 := fun _ base14 _ => base14.

Definition arr14 : Ty14 -> Ty14 -> Ty14
 := fun A B Ty14 base14 arr14 =>
     arr14 (A Ty14 base14 arr14) (B Ty14 base14 arr14).

Definition Con14 : Set
 := forall (Con14  : Set)
      (nil  : Con14)
      (snoc : Con14 -> Ty14 -> Con14)
    , Con14.

Definition nil14 : Con14
 := fun Con14 nil14 snoc => nil14.

Definition snoc14 : Con14 -> Ty14 -> Con14
 := fun Γ A Con14 nil14 snoc14 => snoc14 (Γ Con14 nil14 snoc14) A.

Definition Var14 : Con14 -> Ty14 -> Set
 := fun Γ A =>
   forall (Var14 : Con14 -> Ty14 -> Set)
     (vz  : forall Γ A, Var14 (snoc14 Γ A) A)
     (vs  : forall Γ B A, Var14 Γ A -> Var14 (snoc14 Γ B) A)
   , Var14 Γ A.

Definition vz14 {Γ A} : Var14 (snoc14 Γ A) A
 := fun Var14 vz14 vs => vz14 _ _.

Definition vs14 {Γ B A} : Var14 Γ A -> Var14 (snoc14 Γ B) A
 := fun x Var14 vz14 vs14 => vs14 _ _ _ (x Var14 vz14 vs14).

Definition Tm14 : Con14 -> Ty14 -> Set
 := fun Γ A =>
   forall (Tm14  : Con14 -> Ty14 -> Set)
     (var   : forall Γ A     , Var14 Γ A -> Tm14 Γ A)
     (lam   : forall Γ A B   , Tm14 (snoc14 Γ A) B -> Tm14 Γ (arr14 A B))
     (app   : forall Γ A B   , Tm14 Γ (arr14 A B) -> Tm14 Γ A -> Tm14 Γ B)
   , Tm14 Γ A.

Definition var14 {Γ A} : Var14 Γ A -> Tm14 Γ A
 := fun x Tm14 var14 lam app =>
     var14 _ _ x.

Definition lam14 {Γ A B} : Tm14 (snoc14 Γ A) B -> Tm14 Γ (arr14 A B)
 := fun t Tm14 var14 lam14 app =>
     lam14 _ _ _ (t Tm14 var14 lam14 app).

Definition app14 {Γ A B} : Tm14 Γ (arr14 A B) -> Tm14 Γ A -> Tm14 Γ B
 := fun t u Tm14 var14 lam14 app14 =>
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


Definition Ty15 : Set
 := forall (Ty15 : Set)
      (base   : Ty15)
      (arr : Ty15 -> Ty15 -> Ty15)
    , Ty15.

Definition base15 : Ty15 := fun _ base15 _ => base15.

Definition arr15 : Ty15 -> Ty15 -> Ty15
 := fun A B Ty15 base15 arr15 =>
     arr15 (A Ty15 base15 arr15) (B Ty15 base15 arr15).

Definition Con15 : Set
 := forall (Con15  : Set)
      (nil  : Con15)
      (snoc : Con15 -> Ty15 -> Con15)
    , Con15.

Definition nil15 : Con15
 := fun Con15 nil15 snoc => nil15.

Definition snoc15 : Con15 -> Ty15 -> Con15
 := fun Γ A Con15 nil15 snoc15 => snoc15 (Γ Con15 nil15 snoc15) A.

Definition Var15 : Con15 -> Ty15 -> Set
 := fun Γ A =>
   forall (Var15 : Con15 -> Ty15 -> Set)
     (vz  : forall Γ A, Var15 (snoc15 Γ A) A)
     (vs  : forall Γ B A, Var15 Γ A -> Var15 (snoc15 Γ B) A)
   , Var15 Γ A.

Definition vz15 {Γ A} : Var15 (snoc15 Γ A) A
 := fun Var15 vz15 vs => vz15 _ _.

Definition vs15 {Γ B A} : Var15 Γ A -> Var15 (snoc15 Γ B) A
 := fun x Var15 vz15 vs15 => vs15 _ _ _ (x Var15 vz15 vs15).

Definition Tm15 : Con15 -> Ty15 -> Set
 := fun Γ A =>
   forall (Tm15  : Con15 -> Ty15 -> Set)
     (var   : forall Γ A     , Var15 Γ A -> Tm15 Γ A)
     (lam   : forall Γ A B   , Tm15 (snoc15 Γ A) B -> Tm15 Γ (arr15 A B))
     (app   : forall Γ A B   , Tm15 Γ (arr15 A B) -> Tm15 Γ A -> Tm15 Γ B)
   , Tm15 Γ A.

Definition var15 {Γ A} : Var15 Γ A -> Tm15 Γ A
 := fun x Tm15 var15 lam app =>
     var15 _ _ x.

Definition lam15 {Γ A B} : Tm15 (snoc15 Γ A) B -> Tm15 Γ (arr15 A B)
 := fun t Tm15 var15 lam15 app =>
     lam15 _ _ _ (t Tm15 var15 lam15 app).

Definition app15 {Γ A B} : Tm15 Γ (arr15 A B) -> Tm15 Γ A -> Tm15 Γ B
 := fun t u Tm15 var15 lam15 app15 =>
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


Definition Ty16 : Set
 := forall (Ty16 : Set)
      (base   : Ty16)
      (arr : Ty16 -> Ty16 -> Ty16)
    , Ty16.

Definition base16 : Ty16 := fun _ base16 _ => base16.

Definition arr16 : Ty16 -> Ty16 -> Ty16
 := fun A B Ty16 base16 arr16 =>
     arr16 (A Ty16 base16 arr16) (B Ty16 base16 arr16).

Definition Con16 : Set
 := forall (Con16  : Set)
      (nil  : Con16)
      (snoc : Con16 -> Ty16 -> Con16)
    , Con16.

Definition nil16 : Con16
 := fun Con16 nil16 snoc => nil16.

Definition snoc16 : Con16 -> Ty16 -> Con16
 := fun Γ A Con16 nil16 snoc16 => snoc16 (Γ Con16 nil16 snoc16) A.

Definition Var16 : Con16 -> Ty16 -> Set
 := fun Γ A =>
   forall (Var16 : Con16 -> Ty16 -> Set)
     (vz  : forall Γ A, Var16 (snoc16 Γ A) A)
     (vs  : forall Γ B A, Var16 Γ A -> Var16 (snoc16 Γ B) A)
   , Var16 Γ A.

Definition vz16 {Γ A} : Var16 (snoc16 Γ A) A
 := fun Var16 vz16 vs => vz16 _ _.

Definition vs16 {Γ B A} : Var16 Γ A -> Var16 (snoc16 Γ B) A
 := fun x Var16 vz16 vs16 => vs16 _ _ _ (x Var16 vz16 vs16).

Definition Tm16 : Con16 -> Ty16 -> Set
 := fun Γ A =>
   forall (Tm16  : Con16 -> Ty16 -> Set)
     (var   : forall Γ A     , Var16 Γ A -> Tm16 Γ A)
     (lam   : forall Γ A B   , Tm16 (snoc16 Γ A) B -> Tm16 Γ (arr16 A B))
     (app   : forall Γ A B   , Tm16 Γ (arr16 A B) -> Tm16 Γ A -> Tm16 Γ B)
   , Tm16 Γ A.

Definition var16 {Γ A} : Var16 Γ A -> Tm16 Γ A
 := fun x Tm16 var16 lam app =>
     var16 _ _ x.

Definition lam16 {Γ A B} : Tm16 (snoc16 Γ A) B -> Tm16 Γ (arr16 A B)
 := fun t Tm16 var16 lam16 app =>
     lam16 _ _ _ (t Tm16 var16 lam16 app).

Definition app16 {Γ A B} : Tm16 Γ (arr16 A B) -> Tm16 Γ A -> Tm16 Γ B
 := fun t u Tm16 var16 lam16 app16 =>
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


Definition Ty17 : Set
 := forall (Ty17 : Set)
      (base   : Ty17)
      (arr : Ty17 -> Ty17 -> Ty17)
    , Ty17.

Definition base17 : Ty17 := fun _ base17 _ => base17.

Definition arr17 : Ty17 -> Ty17 -> Ty17
 := fun A B Ty17 base17 arr17 =>
     arr17 (A Ty17 base17 arr17) (B Ty17 base17 arr17).

Definition Con17 : Set
 := forall (Con17  : Set)
      (nil  : Con17)
      (snoc : Con17 -> Ty17 -> Con17)
    , Con17.

Definition nil17 : Con17
 := fun Con17 nil17 snoc => nil17.

Definition snoc17 : Con17 -> Ty17 -> Con17
 := fun Γ A Con17 nil17 snoc17 => snoc17 (Γ Con17 nil17 snoc17) A.

Definition Var17 : Con17 -> Ty17 -> Set
 := fun Γ A =>
   forall (Var17 : Con17 -> Ty17 -> Set)
     (vz  : forall Γ A, Var17 (snoc17 Γ A) A)
     (vs  : forall Γ B A, Var17 Γ A -> Var17 (snoc17 Γ B) A)
   , Var17 Γ A.

Definition vz17 {Γ A} : Var17 (snoc17 Γ A) A
 := fun Var17 vz17 vs => vz17 _ _.

Definition vs17 {Γ B A} : Var17 Γ A -> Var17 (snoc17 Γ B) A
 := fun x Var17 vz17 vs17 => vs17 _ _ _ (x Var17 vz17 vs17).

Definition Tm17 : Con17 -> Ty17 -> Set
 := fun Γ A =>
   forall (Tm17  : Con17 -> Ty17 -> Set)
     (var   : forall Γ A     , Var17 Γ A -> Tm17 Γ A)
     (lam   : forall Γ A B   , Tm17 (snoc17 Γ A) B -> Tm17 Γ (arr17 A B))
     (app   : forall Γ A B   , Tm17 Γ (arr17 A B) -> Tm17 Γ A -> Tm17 Γ B)
   , Tm17 Γ A.

Definition var17 {Γ A} : Var17 Γ A -> Tm17 Γ A
 := fun x Tm17 var17 lam app =>
     var17 _ _ x.

Definition lam17 {Γ A B} : Tm17 (snoc17 Γ A) B -> Tm17 Γ (arr17 A B)
 := fun t Tm17 var17 lam17 app =>
     lam17 _ _ _ (t Tm17 var17 lam17 app).

Definition app17 {Γ A B} : Tm17 Γ (arr17 A B) -> Tm17 Γ A -> Tm17 Γ B
 := fun t u Tm17 var17 lam17 app17 =>
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


Definition Ty18 : Set
 := forall (Ty18 : Set)
      (base   : Ty18)
      (arr : Ty18 -> Ty18 -> Ty18)
    , Ty18.

Definition base18 : Ty18 := fun _ base18 _ => base18.

Definition arr18 : Ty18 -> Ty18 -> Ty18
 := fun A B Ty18 base18 arr18 =>
     arr18 (A Ty18 base18 arr18) (B Ty18 base18 arr18).

Definition Con18 : Set
 := forall (Con18  : Set)
      (nil  : Con18)
      (snoc : Con18 -> Ty18 -> Con18)
    , Con18.

Definition nil18 : Con18
 := fun Con18 nil18 snoc => nil18.

Definition snoc18 : Con18 -> Ty18 -> Con18
 := fun Γ A Con18 nil18 snoc18 => snoc18 (Γ Con18 nil18 snoc18) A.

Definition Var18 : Con18 -> Ty18 -> Set
 := fun Γ A =>
   forall (Var18 : Con18 -> Ty18 -> Set)
     (vz  : forall Γ A, Var18 (snoc18 Γ A) A)
     (vs  : forall Γ B A, Var18 Γ A -> Var18 (snoc18 Γ B) A)
   , Var18 Γ A.

Definition vz18 {Γ A} : Var18 (snoc18 Γ A) A
 := fun Var18 vz18 vs => vz18 _ _.

Definition vs18 {Γ B A} : Var18 Γ A -> Var18 (snoc18 Γ B) A
 := fun x Var18 vz18 vs18 => vs18 _ _ _ (x Var18 vz18 vs18).

Definition Tm18 : Con18 -> Ty18 -> Set
 := fun Γ A =>
   forall (Tm18  : Con18 -> Ty18 -> Set)
     (var   : forall Γ A     , Var18 Γ A -> Tm18 Γ A)
     (lam   : forall Γ A B   , Tm18 (snoc18 Γ A) B -> Tm18 Γ (arr18 A B))
     (app   : forall Γ A B   , Tm18 Γ (arr18 A B) -> Tm18 Γ A -> Tm18 Γ B)
   , Tm18 Γ A.

Definition var18 {Γ A} : Var18 Γ A -> Tm18 Γ A
 := fun x Tm18 var18 lam app =>
     var18 _ _ x.

Definition lam18 {Γ A B} : Tm18 (snoc18 Γ A) B -> Tm18 Γ (arr18 A B)
 := fun t Tm18 var18 lam18 app =>
     lam18 _ _ _ (t Tm18 var18 lam18 app).

Definition app18 {Γ A B} : Tm18 Γ (arr18 A B) -> Tm18 Γ A -> Tm18 Γ B
 := fun t u Tm18 var18 lam18 app18 =>
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


Definition Ty19 : Set
 := forall (Ty19 : Set)
      (base   : Ty19)
      (arr : Ty19 -> Ty19 -> Ty19)
    , Ty19.

Definition base19 : Ty19 := fun _ base19 _ => base19.

Definition arr19 : Ty19 -> Ty19 -> Ty19
 := fun A B Ty19 base19 arr19 =>
     arr19 (A Ty19 base19 arr19) (B Ty19 base19 arr19).

Definition Con19 : Set
 := forall (Con19  : Set)
      (nil  : Con19)
      (snoc : Con19 -> Ty19 -> Con19)
    , Con19.

Definition nil19 : Con19
 := fun Con19 nil19 snoc => nil19.

Definition snoc19 : Con19 -> Ty19 -> Con19
 := fun Γ A Con19 nil19 snoc19 => snoc19 (Γ Con19 nil19 snoc19) A.

Definition Var19 : Con19 -> Ty19 -> Set
 := fun Γ A =>
   forall (Var19 : Con19 -> Ty19 -> Set)
     (vz  : forall Γ A, Var19 (snoc19 Γ A) A)
     (vs  : forall Γ B A, Var19 Γ A -> Var19 (snoc19 Γ B) A)
   , Var19 Γ A.

Definition vz19 {Γ A} : Var19 (snoc19 Γ A) A
 := fun Var19 vz19 vs => vz19 _ _.

Definition vs19 {Γ B A} : Var19 Γ A -> Var19 (snoc19 Γ B) A
 := fun x Var19 vz19 vs19 => vs19 _ _ _ (x Var19 vz19 vs19).

Definition Tm19 : Con19 -> Ty19 -> Set
 := fun Γ A =>
   forall (Tm19  : Con19 -> Ty19 -> Set)
     (var   : forall Γ A     , Var19 Γ A -> Tm19 Γ A)
     (lam   : forall Γ A B   , Tm19 (snoc19 Γ A) B -> Tm19 Γ (arr19 A B))
     (app   : forall Γ A B   , Tm19 Γ (arr19 A B) -> Tm19 Γ A -> Tm19 Γ B)
   , Tm19 Γ A.

Definition var19 {Γ A} : Var19 Γ A -> Tm19 Γ A
 := fun x Tm19 var19 lam app =>
     var19 _ _ x.

Definition lam19 {Γ A B} : Tm19 (snoc19 Γ A) B -> Tm19 Γ (arr19 A B)
 := fun t Tm19 var19 lam19 app =>
     lam19 _ _ _ (t Tm19 var19 lam19 app).

Definition app19 {Γ A B} : Tm19 Γ (arr19 A B) -> Tm19 Γ A -> Tm19 Γ B
 := fun t u Tm19 var19 lam19 app19 =>
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


Definition Ty20 : Set
 := forall (Ty20 : Set)
      (base   : Ty20)
      (arr : Ty20 -> Ty20 -> Ty20)
    , Ty20.

Definition base20 : Ty20 := fun _ base20 _ => base20.

Definition arr20 : Ty20 -> Ty20 -> Ty20
 := fun A B Ty20 base20 arr20 =>
     arr20 (A Ty20 base20 arr20) (B Ty20 base20 arr20).

Definition Con20 : Set
 := forall (Con20  : Set)
      (nil  : Con20)
      (snoc : Con20 -> Ty20 -> Con20)
    , Con20.

Definition nil20 : Con20
 := fun Con20 nil20 snoc => nil20.

Definition snoc20 : Con20 -> Ty20 -> Con20
 := fun Γ A Con20 nil20 snoc20 => snoc20 (Γ Con20 nil20 snoc20) A.

Definition Var20 : Con20 -> Ty20 -> Set
 := fun Γ A =>
   forall (Var20 : Con20 -> Ty20 -> Set)
     (vz  : forall Γ A, Var20 (snoc20 Γ A) A)
     (vs  : forall Γ B A, Var20 Γ A -> Var20 (snoc20 Γ B) A)
   , Var20 Γ A.

Definition vz20 {Γ A} : Var20 (snoc20 Γ A) A
 := fun Var20 vz20 vs => vz20 _ _.

Definition vs20 {Γ B A} : Var20 Γ A -> Var20 (snoc20 Γ B) A
 := fun x Var20 vz20 vs20 => vs20 _ _ _ (x Var20 vz20 vs20).

Definition Tm20 : Con20 -> Ty20 -> Set
 := fun Γ A =>
   forall (Tm20  : Con20 -> Ty20 -> Set)
     (var   : forall Γ A     , Var20 Γ A -> Tm20 Γ A)
     (lam   : forall Γ A B   , Tm20 (snoc20 Γ A) B -> Tm20 Γ (arr20 A B))
     (app   : forall Γ A B   , Tm20 Γ (arr20 A B) -> Tm20 Γ A -> Tm20 Γ B)
   , Tm20 Γ A.

Definition var20 {Γ A} : Var20 Γ A -> Tm20 Γ A
 := fun x Tm20 var20 lam app =>
     var20 _ _ x.

Definition lam20 {Γ A B} : Tm20 (snoc20 Γ A) B -> Tm20 Γ (arr20 A B)
 := fun t Tm20 var20 lam20 app =>
     lam20 _ _ _ (t Tm20 var20 lam20 app).

Definition app20 {Γ A B} : Tm20 Γ (arr20 A B) -> Tm20 Γ A -> Tm20 Γ B
 := fun t u Tm20 var20 lam20 app20 =>
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


Definition Ty21 : Set
 := forall (Ty21 : Set)
      (base   : Ty21)
      (arr : Ty21 -> Ty21 -> Ty21)
    , Ty21.

Definition base21 : Ty21 := fun _ base21 _ => base21.

Definition arr21 : Ty21 -> Ty21 -> Ty21
 := fun A B Ty21 base21 arr21 =>
     arr21 (A Ty21 base21 arr21) (B Ty21 base21 arr21).

Definition Con21 : Set
 := forall (Con21  : Set)
      (nil  : Con21)
      (snoc : Con21 -> Ty21 -> Con21)
    , Con21.

Definition nil21 : Con21
 := fun Con21 nil21 snoc => nil21.

Definition snoc21 : Con21 -> Ty21 -> Con21
 := fun Γ A Con21 nil21 snoc21 => snoc21 (Γ Con21 nil21 snoc21) A.

Definition Var21 : Con21 -> Ty21 -> Set
 := fun Γ A =>
   forall (Var21 : Con21 -> Ty21 -> Set)
     (vz  : forall Γ A, Var21 (snoc21 Γ A) A)
     (vs  : forall Γ B A, Var21 Γ A -> Var21 (snoc21 Γ B) A)
   , Var21 Γ A.

Definition vz21 {Γ A} : Var21 (snoc21 Γ A) A
 := fun Var21 vz21 vs => vz21 _ _.

Definition vs21 {Γ B A} : Var21 Γ A -> Var21 (snoc21 Γ B) A
 := fun x Var21 vz21 vs21 => vs21 _ _ _ (x Var21 vz21 vs21).

Definition Tm21 : Con21 -> Ty21 -> Set
 := fun Γ A =>
   forall (Tm21  : Con21 -> Ty21 -> Set)
     (var   : forall Γ A     , Var21 Γ A -> Tm21 Γ A)
     (lam   : forall Γ A B   , Tm21 (snoc21 Γ A) B -> Tm21 Γ (arr21 A B))
     (app   : forall Γ A B   , Tm21 Γ (arr21 A B) -> Tm21 Γ A -> Tm21 Γ B)
   , Tm21 Γ A.

Definition var21 {Γ A} : Var21 Γ A -> Tm21 Γ A
 := fun x Tm21 var21 lam app =>
     var21 _ _ x.

Definition lam21 {Γ A B} : Tm21 (snoc21 Γ A) B -> Tm21 Γ (arr21 A B)
 := fun t Tm21 var21 lam21 app =>
     lam21 _ _ _ (t Tm21 var21 lam21 app).

Definition app21 {Γ A B} : Tm21 Γ (arr21 A B) -> Tm21 Γ A -> Tm21 Γ B
 := fun t u Tm21 var21 lam21 app21 =>
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


Definition Ty22 : Set
 := forall (Ty22 : Set)
      (base   : Ty22)
      (arr : Ty22 -> Ty22 -> Ty22)
    , Ty22.

Definition base22 : Ty22 := fun _ base22 _ => base22.

Definition arr22 : Ty22 -> Ty22 -> Ty22
 := fun A B Ty22 base22 arr22 =>
     arr22 (A Ty22 base22 arr22) (B Ty22 base22 arr22).

Definition Con22 : Set
 := forall (Con22  : Set)
      (nil  : Con22)
      (snoc : Con22 -> Ty22 -> Con22)
    , Con22.

Definition nil22 : Con22
 := fun Con22 nil22 snoc => nil22.

Definition snoc22 : Con22 -> Ty22 -> Con22
 := fun Γ A Con22 nil22 snoc22 => snoc22 (Γ Con22 nil22 snoc22) A.

Definition Var22 : Con22 -> Ty22 -> Set
 := fun Γ A =>
   forall (Var22 : Con22 -> Ty22 -> Set)
     (vz  : forall Γ A, Var22 (snoc22 Γ A) A)
     (vs  : forall Γ B A, Var22 Γ A -> Var22 (snoc22 Γ B) A)
   , Var22 Γ A.

Definition vz22 {Γ A} : Var22 (snoc22 Γ A) A
 := fun Var22 vz22 vs => vz22 _ _.

Definition vs22 {Γ B A} : Var22 Γ A -> Var22 (snoc22 Γ B) A
 := fun x Var22 vz22 vs22 => vs22 _ _ _ (x Var22 vz22 vs22).

Definition Tm22 : Con22 -> Ty22 -> Set
 := fun Γ A =>
   forall (Tm22  : Con22 -> Ty22 -> Set)
     (var   : forall Γ A     , Var22 Γ A -> Tm22 Γ A)
     (lam   : forall Γ A B   , Tm22 (snoc22 Γ A) B -> Tm22 Γ (arr22 A B))
     (app   : forall Γ A B   , Tm22 Γ (arr22 A B) -> Tm22 Γ A -> Tm22 Γ B)
   , Tm22 Γ A.

Definition var22 {Γ A} : Var22 Γ A -> Tm22 Γ A
 := fun x Tm22 var22 lam app =>
     var22 _ _ x.

Definition lam22 {Γ A B} : Tm22 (snoc22 Γ A) B -> Tm22 Γ (arr22 A B)
 := fun t Tm22 var22 lam22 app =>
     lam22 _ _ _ (t Tm22 var22 lam22 app).

Definition app22 {Γ A B} : Tm22 Γ (arr22 A B) -> Tm22 Γ A -> Tm22 Γ B
 := fun t u Tm22 var22 lam22 app22 =>
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


Definition Ty23 : Set
 := forall (Ty23 : Set)
      (base   : Ty23)
      (arr : Ty23 -> Ty23 -> Ty23)
    , Ty23.

Definition base23 : Ty23 := fun _ base23 _ => base23.

Definition arr23 : Ty23 -> Ty23 -> Ty23
 := fun A B Ty23 base23 arr23 =>
     arr23 (A Ty23 base23 arr23) (B Ty23 base23 arr23).

Definition Con23 : Set
 := forall (Con23  : Set)
      (nil  : Con23)
      (snoc : Con23 -> Ty23 -> Con23)
    , Con23.

Definition nil23 : Con23
 := fun Con23 nil23 snoc => nil23.

Definition snoc23 : Con23 -> Ty23 -> Con23
 := fun Γ A Con23 nil23 snoc23 => snoc23 (Γ Con23 nil23 snoc23) A.

Definition Var23 : Con23 -> Ty23 -> Set
 := fun Γ A =>
   forall (Var23 : Con23 -> Ty23 -> Set)
     (vz  : forall Γ A, Var23 (snoc23 Γ A) A)
     (vs  : forall Γ B A, Var23 Γ A -> Var23 (snoc23 Γ B) A)
   , Var23 Γ A.

Definition vz23 {Γ A} : Var23 (snoc23 Γ A) A
 := fun Var23 vz23 vs => vz23 _ _.

Definition vs23 {Γ B A} : Var23 Γ A -> Var23 (snoc23 Γ B) A
 := fun x Var23 vz23 vs23 => vs23 _ _ _ (x Var23 vz23 vs23).

Definition Tm23 : Con23 -> Ty23 -> Set
 := fun Γ A =>
   forall (Tm23  : Con23 -> Ty23 -> Set)
     (var   : forall Γ A     , Var23 Γ A -> Tm23 Γ A)
     (lam   : forall Γ A B   , Tm23 (snoc23 Γ A) B -> Tm23 Γ (arr23 A B))
     (app   : forall Γ A B   , Tm23 Γ (arr23 A B) -> Tm23 Γ A -> Tm23 Γ B)
   , Tm23 Γ A.

Definition var23 {Γ A} : Var23 Γ A -> Tm23 Γ A
 := fun x Tm23 var23 lam app =>
     var23 _ _ x.

Definition lam23 {Γ A B} : Tm23 (snoc23 Γ A) B -> Tm23 Γ (arr23 A B)
 := fun t Tm23 var23 lam23 app =>
     lam23 _ _ _ (t Tm23 var23 lam23 app).

Definition app23 {Γ A B} : Tm23 Γ (arr23 A B) -> Tm23 Γ A -> Tm23 Γ B
 := fun t u Tm23 var23 lam23 app23 =>
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


Definition Ty24 : Set
 := forall (Ty24 : Set)
      (base   : Ty24)
      (arr : Ty24 -> Ty24 -> Ty24)
    , Ty24.

Definition base24 : Ty24 := fun _ base24 _ => base24.

Definition arr24 : Ty24 -> Ty24 -> Ty24
 := fun A B Ty24 base24 arr24 =>
     arr24 (A Ty24 base24 arr24) (B Ty24 base24 arr24).

Definition Con24 : Set
 := forall (Con24  : Set)
      (nil  : Con24)
      (snoc : Con24 -> Ty24 -> Con24)
    , Con24.

Definition nil24 : Con24
 := fun Con24 nil24 snoc => nil24.

Definition snoc24 : Con24 -> Ty24 -> Con24
 := fun Γ A Con24 nil24 snoc24 => snoc24 (Γ Con24 nil24 snoc24) A.

Definition Var24 : Con24 -> Ty24 -> Set
 := fun Γ A =>
   forall (Var24 : Con24 -> Ty24 -> Set)
     (vz  : forall Γ A, Var24 (snoc24 Γ A) A)
     (vs  : forall Γ B A, Var24 Γ A -> Var24 (snoc24 Γ B) A)
   , Var24 Γ A.

Definition vz24 {Γ A} : Var24 (snoc24 Γ A) A
 := fun Var24 vz24 vs => vz24 _ _.

Definition vs24 {Γ B A} : Var24 Γ A -> Var24 (snoc24 Γ B) A
 := fun x Var24 vz24 vs24 => vs24 _ _ _ (x Var24 vz24 vs24).

Definition Tm24 : Con24 -> Ty24 -> Set
 := fun Γ A =>
   forall (Tm24  : Con24 -> Ty24 -> Set)
     (var   : forall Γ A     , Var24 Γ A -> Tm24 Γ A)
     (lam   : forall Γ A B   , Tm24 (snoc24 Γ A) B -> Tm24 Γ (arr24 A B))
     (app   : forall Γ A B   , Tm24 Γ (arr24 A B) -> Tm24 Γ A -> Tm24 Γ B)
   , Tm24 Γ A.

Definition var24 {Γ A} : Var24 Γ A -> Tm24 Γ A
 := fun x Tm24 var24 lam app =>
     var24 _ _ x.

Definition lam24 {Γ A B} : Tm24 (snoc24 Γ A) B -> Tm24 Γ (arr24 A B)
 := fun t Tm24 var24 lam24 app =>
     lam24 _ _ _ (t Tm24 var24 lam24 app).

Definition app24 {Γ A B} : Tm24 Γ (arr24 A B) -> Tm24 Γ A -> Tm24 Γ B
 := fun t u Tm24 var24 lam24 app24 =>
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


Definition Ty25 : Set
 := forall (Ty25 : Set)
      (base   : Ty25)
      (arr : Ty25 -> Ty25 -> Ty25)
    , Ty25.

Definition base25 : Ty25 := fun _ base25 _ => base25.

Definition arr25 : Ty25 -> Ty25 -> Ty25
 := fun A B Ty25 base25 arr25 =>
     arr25 (A Ty25 base25 arr25) (B Ty25 base25 arr25).

Definition Con25 : Set
 := forall (Con25  : Set)
      (nil  : Con25)
      (snoc : Con25 -> Ty25 -> Con25)
    , Con25.

Definition nil25 : Con25
 := fun Con25 nil25 snoc => nil25.

Definition snoc25 : Con25 -> Ty25 -> Con25
 := fun Γ A Con25 nil25 snoc25 => snoc25 (Γ Con25 nil25 snoc25) A.

Definition Var25 : Con25 -> Ty25 -> Set
 := fun Γ A =>
   forall (Var25 : Con25 -> Ty25 -> Set)
     (vz  : forall Γ A, Var25 (snoc25 Γ A) A)
     (vs  : forall Γ B A, Var25 Γ A -> Var25 (snoc25 Γ B) A)
   , Var25 Γ A.

Definition vz25 {Γ A} : Var25 (snoc25 Γ A) A
 := fun Var25 vz25 vs => vz25 _ _.

Definition vs25 {Γ B A} : Var25 Γ A -> Var25 (snoc25 Γ B) A
 := fun x Var25 vz25 vs25 => vs25 _ _ _ (x Var25 vz25 vs25).

Definition Tm25 : Con25 -> Ty25 -> Set
 := fun Γ A =>
   forall (Tm25  : Con25 -> Ty25 -> Set)
     (var   : forall Γ A     , Var25 Γ A -> Tm25 Γ A)
     (lam   : forall Γ A B   , Tm25 (snoc25 Γ A) B -> Tm25 Γ (arr25 A B))
     (app   : forall Γ A B   , Tm25 Γ (arr25 A B) -> Tm25 Γ A -> Tm25 Γ B)
   , Tm25 Γ A.

Definition var25 {Γ A} : Var25 Γ A -> Tm25 Γ A
 := fun x Tm25 var25 lam app =>
     var25 _ _ x.

Definition lam25 {Γ A B} : Tm25 (snoc25 Γ A) B -> Tm25 Γ (arr25 A B)
 := fun t Tm25 var25 lam25 app =>
     lam25 _ _ _ (t Tm25 var25 lam25 app).

Definition app25 {Γ A B} : Tm25 Γ (arr25 A B) -> Tm25 Γ A -> Tm25 Γ B
 := fun t u Tm25 var25 lam25 app25 =>
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


Definition Ty26 : Set
 := forall (Ty26 : Set)
      (base   : Ty26)
      (arr : Ty26 -> Ty26 -> Ty26)
    , Ty26.

Definition base26 : Ty26 := fun _ base26 _ => base26.

Definition arr26 : Ty26 -> Ty26 -> Ty26
 := fun A B Ty26 base26 arr26 =>
     arr26 (A Ty26 base26 arr26) (B Ty26 base26 arr26).

Definition Con26 : Set
 := forall (Con26  : Set)
      (nil  : Con26)
      (snoc : Con26 -> Ty26 -> Con26)
    , Con26.

Definition nil26 : Con26
 := fun Con26 nil26 snoc => nil26.

Definition snoc26 : Con26 -> Ty26 -> Con26
 := fun Γ A Con26 nil26 snoc26 => snoc26 (Γ Con26 nil26 snoc26) A.

Definition Var26 : Con26 -> Ty26 -> Set
 := fun Γ A =>
   forall (Var26 : Con26 -> Ty26 -> Set)
     (vz  : forall Γ A, Var26 (snoc26 Γ A) A)
     (vs  : forall Γ B A, Var26 Γ A -> Var26 (snoc26 Γ B) A)
   , Var26 Γ A.

Definition vz26 {Γ A} : Var26 (snoc26 Γ A) A
 := fun Var26 vz26 vs => vz26 _ _.

Definition vs26 {Γ B A} : Var26 Γ A -> Var26 (snoc26 Γ B) A
 := fun x Var26 vz26 vs26 => vs26 _ _ _ (x Var26 vz26 vs26).

Definition Tm26 : Con26 -> Ty26 -> Set
 := fun Γ A =>
   forall (Tm26  : Con26 -> Ty26 -> Set)
     (var   : forall Γ A     , Var26 Γ A -> Tm26 Γ A)
     (lam   : forall Γ A B   , Tm26 (snoc26 Γ A) B -> Tm26 Γ (arr26 A B))
     (app   : forall Γ A B   , Tm26 Γ (arr26 A B) -> Tm26 Γ A -> Tm26 Γ B)
   , Tm26 Γ A.

Definition var26 {Γ A} : Var26 Γ A -> Tm26 Γ A
 := fun x Tm26 var26 lam app =>
     var26 _ _ x.

Definition lam26 {Γ A B} : Tm26 (snoc26 Γ A) B -> Tm26 Γ (arr26 A B)
 := fun t Tm26 var26 lam26 app =>
     lam26 _ _ _ (t Tm26 var26 lam26 app).

Definition app26 {Γ A B} : Tm26 Γ (arr26 A B) -> Tm26 Γ A -> Tm26 Γ B
 := fun t u Tm26 var26 lam26 app26 =>
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


Definition Ty27 : Set
 := forall (Ty27 : Set)
      (base   : Ty27)
      (arr : Ty27 -> Ty27 -> Ty27)
    , Ty27.

Definition base27 : Ty27 := fun _ base27 _ => base27.

Definition arr27 : Ty27 -> Ty27 -> Ty27
 := fun A B Ty27 base27 arr27 =>
     arr27 (A Ty27 base27 arr27) (B Ty27 base27 arr27).

Definition Con27 : Set
 := forall (Con27  : Set)
      (nil  : Con27)
      (snoc : Con27 -> Ty27 -> Con27)
    , Con27.

Definition nil27 : Con27
 := fun Con27 nil27 snoc => nil27.

Definition snoc27 : Con27 -> Ty27 -> Con27
 := fun Γ A Con27 nil27 snoc27 => snoc27 (Γ Con27 nil27 snoc27) A.

Definition Var27 : Con27 -> Ty27 -> Set
 := fun Γ A =>
   forall (Var27 : Con27 -> Ty27 -> Set)
     (vz  : forall Γ A, Var27 (snoc27 Γ A) A)
     (vs  : forall Γ B A, Var27 Γ A -> Var27 (snoc27 Γ B) A)
   , Var27 Γ A.

Definition vz27 {Γ A} : Var27 (snoc27 Γ A) A
 := fun Var27 vz27 vs => vz27 _ _.

Definition vs27 {Γ B A} : Var27 Γ A -> Var27 (snoc27 Γ B) A
 := fun x Var27 vz27 vs27 => vs27 _ _ _ (x Var27 vz27 vs27).

Definition Tm27 : Con27 -> Ty27 -> Set
 := fun Γ A =>
   forall (Tm27  : Con27 -> Ty27 -> Set)
     (var   : forall Γ A     , Var27 Γ A -> Tm27 Γ A)
     (lam   : forall Γ A B   , Tm27 (snoc27 Γ A) B -> Tm27 Γ (arr27 A B))
     (app   : forall Γ A B   , Tm27 Γ (arr27 A B) -> Tm27 Γ A -> Tm27 Γ B)
   , Tm27 Γ A.

Definition var27 {Γ A} : Var27 Γ A -> Tm27 Γ A
 := fun x Tm27 var27 lam app =>
     var27 _ _ x.

Definition lam27 {Γ A B} : Tm27 (snoc27 Γ A) B -> Tm27 Γ (arr27 A B)
 := fun t Tm27 var27 lam27 app =>
     lam27 _ _ _ (t Tm27 var27 lam27 app).

Definition app27 {Γ A B} : Tm27 Γ (arr27 A B) -> Tm27 Γ A -> Tm27 Γ B
 := fun t u Tm27 var27 lam27 app27 =>
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


Definition Ty28 : Set
 := forall (Ty28 : Set)
      (base   : Ty28)
      (arr : Ty28 -> Ty28 -> Ty28)
    , Ty28.

Definition base28 : Ty28 := fun _ base28 _ => base28.

Definition arr28 : Ty28 -> Ty28 -> Ty28
 := fun A B Ty28 base28 arr28 =>
     arr28 (A Ty28 base28 arr28) (B Ty28 base28 arr28).

Definition Con28 : Set
 := forall (Con28  : Set)
      (nil  : Con28)
      (snoc : Con28 -> Ty28 -> Con28)
    , Con28.

Definition nil28 : Con28
 := fun Con28 nil28 snoc => nil28.

Definition snoc28 : Con28 -> Ty28 -> Con28
 := fun Γ A Con28 nil28 snoc28 => snoc28 (Γ Con28 nil28 snoc28) A.

Definition Var28 : Con28 -> Ty28 -> Set
 := fun Γ A =>
   forall (Var28 : Con28 -> Ty28 -> Set)
     (vz  : forall Γ A, Var28 (snoc28 Γ A) A)
     (vs  : forall Γ B A, Var28 Γ A -> Var28 (snoc28 Γ B) A)
   , Var28 Γ A.

Definition vz28 {Γ A} : Var28 (snoc28 Γ A) A
 := fun Var28 vz28 vs => vz28 _ _.

Definition vs28 {Γ B A} : Var28 Γ A -> Var28 (snoc28 Γ B) A
 := fun x Var28 vz28 vs28 => vs28 _ _ _ (x Var28 vz28 vs28).

Definition Tm28 : Con28 -> Ty28 -> Set
 := fun Γ A =>
   forall (Tm28  : Con28 -> Ty28 -> Set)
     (var   : forall Γ A     , Var28 Γ A -> Tm28 Γ A)
     (lam   : forall Γ A B   , Tm28 (snoc28 Γ A) B -> Tm28 Γ (arr28 A B))
     (app   : forall Γ A B   , Tm28 Γ (arr28 A B) -> Tm28 Γ A -> Tm28 Γ B)
   , Tm28 Γ A.

Definition var28 {Γ A} : Var28 Γ A -> Tm28 Γ A
 := fun x Tm28 var28 lam app =>
     var28 _ _ x.

Definition lam28 {Γ A B} : Tm28 (snoc28 Γ A) B -> Tm28 Γ (arr28 A B)
 := fun t Tm28 var28 lam28 app =>
     lam28 _ _ _ (t Tm28 var28 lam28 app).

Definition app28 {Γ A B} : Tm28 Γ (arr28 A B) -> Tm28 Γ A -> Tm28 Γ B
 := fun t u Tm28 var28 lam28 app28 =>
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


Definition Ty29 : Set
 := forall (Ty29 : Set)
      (base   : Ty29)
      (arr : Ty29 -> Ty29 -> Ty29)
    , Ty29.

Definition base29 : Ty29 := fun _ base29 _ => base29.

Definition arr29 : Ty29 -> Ty29 -> Ty29
 := fun A B Ty29 base29 arr29 =>
     arr29 (A Ty29 base29 arr29) (B Ty29 base29 arr29).

Definition Con29 : Set
 := forall (Con29  : Set)
      (nil  : Con29)
      (snoc : Con29 -> Ty29 -> Con29)
    , Con29.

Definition nil29 : Con29
 := fun Con29 nil29 snoc => nil29.

Definition snoc29 : Con29 -> Ty29 -> Con29
 := fun Γ A Con29 nil29 snoc29 => snoc29 (Γ Con29 nil29 snoc29) A.

Definition Var29 : Con29 -> Ty29 -> Set
 := fun Γ A =>
   forall (Var29 : Con29 -> Ty29 -> Set)
     (vz  : forall Γ A, Var29 (snoc29 Γ A) A)
     (vs  : forall Γ B A, Var29 Γ A -> Var29 (snoc29 Γ B) A)
   , Var29 Γ A.

Definition vz29 {Γ A} : Var29 (snoc29 Γ A) A
 := fun Var29 vz29 vs => vz29 _ _.

Definition vs29 {Γ B A} : Var29 Γ A -> Var29 (snoc29 Γ B) A
 := fun x Var29 vz29 vs29 => vs29 _ _ _ (x Var29 vz29 vs29).

Definition Tm29 : Con29 -> Ty29 -> Set
 := fun Γ A =>
   forall (Tm29  : Con29 -> Ty29 -> Set)
     (var   : forall Γ A     , Var29 Γ A -> Tm29 Γ A)
     (lam   : forall Γ A B   , Tm29 (snoc29 Γ A) B -> Tm29 Γ (arr29 A B))
     (app   : forall Γ A B   , Tm29 Γ (arr29 A B) -> Tm29 Γ A -> Tm29 Γ B)
   , Tm29 Γ A.

Definition var29 {Γ A} : Var29 Γ A -> Tm29 Γ A
 := fun x Tm29 var29 lam app =>
     var29 _ _ x.

Definition lam29 {Γ A B} : Tm29 (snoc29 Γ A) B -> Tm29 Γ (arr29 A B)
 := fun t Tm29 var29 lam29 app =>
     lam29 _ _ _ (t Tm29 var29 lam29 app).

Definition app29 {Γ A B} : Tm29 Γ (arr29 A B) -> Tm29 Γ A -> Tm29 Γ B
 := fun t u Tm29 var29 lam29 app29 =>
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


Definition Ty30 : Set
 := forall (Ty30 : Set)
      (base   : Ty30)
      (arr : Ty30 -> Ty30 -> Ty30)
    , Ty30.

Definition base30 : Ty30 := fun _ base30 _ => base30.

Definition arr30 : Ty30 -> Ty30 -> Ty30
 := fun A B Ty30 base30 arr30 =>
     arr30 (A Ty30 base30 arr30) (B Ty30 base30 arr30).

Definition Con30 : Set
 := forall (Con30  : Set)
      (nil  : Con30)
      (snoc : Con30 -> Ty30 -> Con30)
    , Con30.

Definition nil30 : Con30
 := fun Con30 nil30 snoc => nil30.

Definition snoc30 : Con30 -> Ty30 -> Con30
 := fun Γ A Con30 nil30 snoc30 => snoc30 (Γ Con30 nil30 snoc30) A.

Definition Var30 : Con30 -> Ty30 -> Set
 := fun Γ A =>
   forall (Var30 : Con30 -> Ty30 -> Set)
     (vz  : forall Γ A, Var30 (snoc30 Γ A) A)
     (vs  : forall Γ B A, Var30 Γ A -> Var30 (snoc30 Γ B) A)
   , Var30 Γ A.

Definition vz30 {Γ A} : Var30 (snoc30 Γ A) A
 := fun Var30 vz30 vs => vz30 _ _.

Definition vs30 {Γ B A} : Var30 Γ A -> Var30 (snoc30 Γ B) A
 := fun x Var30 vz30 vs30 => vs30 _ _ _ (x Var30 vz30 vs30).

Definition Tm30 : Con30 -> Ty30 -> Set
 := fun Γ A =>
   forall (Tm30  : Con30 -> Ty30 -> Set)
     (var   : forall Γ A     , Var30 Γ A -> Tm30 Γ A)
     (lam   : forall Γ A B   , Tm30 (snoc30 Γ A) B -> Tm30 Γ (arr30 A B))
     (app   : forall Γ A B   , Tm30 Γ (arr30 A B) -> Tm30 Γ A -> Tm30 Γ B)
   , Tm30 Γ A.

Definition var30 {Γ A} : Var30 Γ A -> Tm30 Γ A
 := fun x Tm30 var30 lam app =>
     var30 _ _ x.

Definition lam30 {Γ A B} : Tm30 (snoc30 Γ A) B -> Tm30 Γ (arr30 A B)
 := fun t Tm30 var30 lam30 app =>
     lam30 _ _ _ (t Tm30 var30 lam30 app).

Definition app30 {Γ A B} : Tm30 Γ (arr30 A B) -> Tm30 Γ A -> Tm30 Γ B
 := fun t u Tm30 var30 lam30 app30 =>
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


Definition Ty31 : Set
 := forall (Ty31 : Set)
      (base   : Ty31)
      (arr : Ty31 -> Ty31 -> Ty31)
    , Ty31.

Definition base31 : Ty31 := fun _ base31 _ => base31.

Definition arr31 : Ty31 -> Ty31 -> Ty31
 := fun A B Ty31 base31 arr31 =>
     arr31 (A Ty31 base31 arr31) (B Ty31 base31 arr31).

Definition Con31 : Set
 := forall (Con31  : Set)
      (nil  : Con31)
      (snoc : Con31 -> Ty31 -> Con31)
    , Con31.

Definition nil31 : Con31
 := fun Con31 nil31 snoc => nil31.

Definition snoc31 : Con31 -> Ty31 -> Con31
 := fun Γ A Con31 nil31 snoc31 => snoc31 (Γ Con31 nil31 snoc31) A.

Definition Var31 : Con31 -> Ty31 -> Set
 := fun Γ A =>
   forall (Var31 : Con31 -> Ty31 -> Set)
     (vz  : forall Γ A, Var31 (snoc31 Γ A) A)
     (vs  : forall Γ B A, Var31 Γ A -> Var31 (snoc31 Γ B) A)
   , Var31 Γ A.

Definition vz31 {Γ A} : Var31 (snoc31 Γ A) A
 := fun Var31 vz31 vs => vz31 _ _.

Definition vs31 {Γ B A} : Var31 Γ A -> Var31 (snoc31 Γ B) A
 := fun x Var31 vz31 vs31 => vs31 _ _ _ (x Var31 vz31 vs31).

Definition Tm31 : Con31 -> Ty31 -> Set
 := fun Γ A =>
   forall (Tm31  : Con31 -> Ty31 -> Set)
     (var   : forall Γ A     , Var31 Γ A -> Tm31 Γ A)
     (lam   : forall Γ A B   , Tm31 (snoc31 Γ A) B -> Tm31 Γ (arr31 A B))
     (app   : forall Γ A B   , Tm31 Γ (arr31 A B) -> Tm31 Γ A -> Tm31 Γ B)
   , Tm31 Γ A.

Definition var31 {Γ A} : Var31 Γ A -> Tm31 Γ A
 := fun x Tm31 var31 lam app =>
     var31 _ _ x.

Definition lam31 {Γ A B} : Tm31 (snoc31 Γ A) B -> Tm31 Γ (arr31 A B)
 := fun t Tm31 var31 lam31 app =>
     lam31 _ _ _ (t Tm31 var31 lam31 app).

Definition app31 {Γ A B} : Tm31 Γ (arr31 A B) -> Tm31 Γ A -> Tm31 Γ B
 := fun t u Tm31 var31 lam31 app31 =>
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


Definition Ty32 : Set
 := forall (Ty32 : Set)
      (base   : Ty32)
      (arr : Ty32 -> Ty32 -> Ty32)
    , Ty32.

Definition base32 : Ty32 := fun _ base32 _ => base32.

Definition arr32 : Ty32 -> Ty32 -> Ty32
 := fun A B Ty32 base32 arr32 =>
     arr32 (A Ty32 base32 arr32) (B Ty32 base32 arr32).

Definition Con32 : Set
 := forall (Con32  : Set)
      (nil  : Con32)
      (snoc : Con32 -> Ty32 -> Con32)
    , Con32.

Definition nil32 : Con32
 := fun Con32 nil32 snoc => nil32.

Definition snoc32 : Con32 -> Ty32 -> Con32
 := fun Γ A Con32 nil32 snoc32 => snoc32 (Γ Con32 nil32 snoc32) A.

Definition Var32 : Con32 -> Ty32 -> Set
 := fun Γ A =>
   forall (Var32 : Con32 -> Ty32 -> Set)
     (vz  : forall Γ A, Var32 (snoc32 Γ A) A)
     (vs  : forall Γ B A, Var32 Γ A -> Var32 (snoc32 Γ B) A)
   , Var32 Γ A.

Definition vz32 {Γ A} : Var32 (snoc32 Γ A) A
 := fun Var32 vz32 vs => vz32 _ _.

Definition vs32 {Γ B A} : Var32 Γ A -> Var32 (snoc32 Γ B) A
 := fun x Var32 vz32 vs32 => vs32 _ _ _ (x Var32 vz32 vs32).

Definition Tm32 : Con32 -> Ty32 -> Set
 := fun Γ A =>
   forall (Tm32  : Con32 -> Ty32 -> Set)
     (var   : forall Γ A     , Var32 Γ A -> Tm32 Γ A)
     (lam   : forall Γ A B   , Tm32 (snoc32 Γ A) B -> Tm32 Γ (arr32 A B))
     (app   : forall Γ A B   , Tm32 Γ (arr32 A B) -> Tm32 Γ A -> Tm32 Γ B)
   , Tm32 Γ A.

Definition var32 {Γ A} : Var32 Γ A -> Tm32 Γ A
 := fun x Tm32 var32 lam app =>
     var32 _ _ x.

Definition lam32 {Γ A B} : Tm32 (snoc32 Γ A) B -> Tm32 Γ (arr32 A B)
 := fun t Tm32 var32 lam32 app =>
     lam32 _ _ _ (t Tm32 var32 lam32 app).

Definition app32 {Γ A B} : Tm32 Γ (arr32 A B) -> Tm32 Γ A -> Tm32 Γ B
 := fun t u Tm32 var32 lam32 app32 =>
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


Definition Ty33 : Set
 := forall (Ty33 : Set)
      (base   : Ty33)
      (arr : Ty33 -> Ty33 -> Ty33)
    , Ty33.

Definition base33 : Ty33 := fun _ base33 _ => base33.

Definition arr33 : Ty33 -> Ty33 -> Ty33
 := fun A B Ty33 base33 arr33 =>
     arr33 (A Ty33 base33 arr33) (B Ty33 base33 arr33).

Definition Con33 : Set
 := forall (Con33  : Set)
      (nil  : Con33)
      (snoc : Con33 -> Ty33 -> Con33)
    , Con33.

Definition nil33 : Con33
 := fun Con33 nil33 snoc => nil33.

Definition snoc33 : Con33 -> Ty33 -> Con33
 := fun Γ A Con33 nil33 snoc33 => snoc33 (Γ Con33 nil33 snoc33) A.

Definition Var33 : Con33 -> Ty33 -> Set
 := fun Γ A =>
   forall (Var33 : Con33 -> Ty33 -> Set)
     (vz  : forall Γ A, Var33 (snoc33 Γ A) A)
     (vs  : forall Γ B A, Var33 Γ A -> Var33 (snoc33 Γ B) A)
   , Var33 Γ A.

Definition vz33 {Γ A} : Var33 (snoc33 Γ A) A
 := fun Var33 vz33 vs => vz33 _ _.

Definition vs33 {Γ B A} : Var33 Γ A -> Var33 (snoc33 Γ B) A
 := fun x Var33 vz33 vs33 => vs33 _ _ _ (x Var33 vz33 vs33).

Definition Tm33 : Con33 -> Ty33 -> Set
 := fun Γ A =>
   forall (Tm33  : Con33 -> Ty33 -> Set)
     (var   : forall Γ A     , Var33 Γ A -> Tm33 Γ A)
     (lam   : forall Γ A B   , Tm33 (snoc33 Γ A) B -> Tm33 Γ (arr33 A B))
     (app   : forall Γ A B   , Tm33 Γ (arr33 A B) -> Tm33 Γ A -> Tm33 Γ B)
   , Tm33 Γ A.

Definition var33 {Γ A} : Var33 Γ A -> Tm33 Γ A
 := fun x Tm33 var33 lam app =>
     var33 _ _ x.

Definition lam33 {Γ A B} : Tm33 (snoc33 Γ A) B -> Tm33 Γ (arr33 A B)
 := fun t Tm33 var33 lam33 app =>
     lam33 _ _ _ (t Tm33 var33 lam33 app).

Definition app33 {Γ A B} : Tm33 Γ (arr33 A B) -> Tm33 Γ A -> Tm33 Γ B
 := fun t u Tm33 var33 lam33 app33 =>
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


Definition Ty34 : Set
 := forall (Ty34 : Set)
      (base   : Ty34)
      (arr : Ty34 -> Ty34 -> Ty34)
    , Ty34.

Definition base34 : Ty34 := fun _ base34 _ => base34.

Definition arr34 : Ty34 -> Ty34 -> Ty34
 := fun A B Ty34 base34 arr34 =>
     arr34 (A Ty34 base34 arr34) (B Ty34 base34 arr34).

Definition Con34 : Set
 := forall (Con34  : Set)
      (nil  : Con34)
      (snoc : Con34 -> Ty34 -> Con34)
    , Con34.

Definition nil34 : Con34
 := fun Con34 nil34 snoc => nil34.

Definition snoc34 : Con34 -> Ty34 -> Con34
 := fun Γ A Con34 nil34 snoc34 => snoc34 (Γ Con34 nil34 snoc34) A.

Definition Var34 : Con34 -> Ty34 -> Set
 := fun Γ A =>
   forall (Var34 : Con34 -> Ty34 -> Set)
     (vz  : forall Γ A, Var34 (snoc34 Γ A) A)
     (vs  : forall Γ B A, Var34 Γ A -> Var34 (snoc34 Γ B) A)
   , Var34 Γ A.

Definition vz34 {Γ A} : Var34 (snoc34 Γ A) A
 := fun Var34 vz34 vs => vz34 _ _.

Definition vs34 {Γ B A} : Var34 Γ A -> Var34 (snoc34 Γ B) A
 := fun x Var34 vz34 vs34 => vs34 _ _ _ (x Var34 vz34 vs34).

Definition Tm34 : Con34 -> Ty34 -> Set
 := fun Γ A =>
   forall (Tm34  : Con34 -> Ty34 -> Set)
     (var   : forall Γ A     , Var34 Γ A -> Tm34 Γ A)
     (lam   : forall Γ A B   , Tm34 (snoc34 Γ A) B -> Tm34 Γ (arr34 A B))
     (app   : forall Γ A B   , Tm34 Γ (arr34 A B) -> Tm34 Γ A -> Tm34 Γ B)
   , Tm34 Γ A.

Definition var34 {Γ A} : Var34 Γ A -> Tm34 Γ A
 := fun x Tm34 var34 lam app =>
     var34 _ _ x.

Definition lam34 {Γ A B} : Tm34 (snoc34 Γ A) B -> Tm34 Γ (arr34 A B)
 := fun t Tm34 var34 lam34 app =>
     lam34 _ _ _ (t Tm34 var34 lam34 app).

Definition app34 {Γ A B} : Tm34 Γ (arr34 A B) -> Tm34 Γ A -> Tm34 Γ B
 := fun t u Tm34 var34 lam34 app34 =>
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


Definition Ty35 : Set
 := forall (Ty35 : Set)
      (base   : Ty35)
      (arr : Ty35 -> Ty35 -> Ty35)
    , Ty35.

Definition base35 : Ty35 := fun _ base35 _ => base35.

Definition arr35 : Ty35 -> Ty35 -> Ty35
 := fun A B Ty35 base35 arr35 =>
     arr35 (A Ty35 base35 arr35) (B Ty35 base35 arr35).

Definition Con35 : Set
 := forall (Con35  : Set)
      (nil  : Con35)
      (snoc : Con35 -> Ty35 -> Con35)
    , Con35.

Definition nil35 : Con35
 := fun Con35 nil35 snoc => nil35.

Definition snoc35 : Con35 -> Ty35 -> Con35
 := fun Γ A Con35 nil35 snoc35 => snoc35 (Γ Con35 nil35 snoc35) A.

Definition Var35 : Con35 -> Ty35 -> Set
 := fun Γ A =>
   forall (Var35 : Con35 -> Ty35 -> Set)
     (vz  : forall Γ A, Var35 (snoc35 Γ A) A)
     (vs  : forall Γ B A, Var35 Γ A -> Var35 (snoc35 Γ B) A)
   , Var35 Γ A.

Definition vz35 {Γ A} : Var35 (snoc35 Γ A) A
 := fun Var35 vz35 vs => vz35 _ _.

Definition vs35 {Γ B A} : Var35 Γ A -> Var35 (snoc35 Γ B) A
 := fun x Var35 vz35 vs35 => vs35 _ _ _ (x Var35 vz35 vs35).

Definition Tm35 : Con35 -> Ty35 -> Set
 := fun Γ A =>
   forall (Tm35  : Con35 -> Ty35 -> Set)
     (var   : forall Γ A     , Var35 Γ A -> Tm35 Γ A)
     (lam   : forall Γ A B   , Tm35 (snoc35 Γ A) B -> Tm35 Γ (arr35 A B))
     (app   : forall Γ A B   , Tm35 Γ (arr35 A B) -> Tm35 Γ A -> Tm35 Γ B)
   , Tm35 Γ A.

Definition var35 {Γ A} : Var35 Γ A -> Tm35 Γ A
 := fun x Tm35 var35 lam app =>
     var35 _ _ x.

Definition lam35 {Γ A B} : Tm35 (snoc35 Γ A) B -> Tm35 Γ (arr35 A B)
 := fun t Tm35 var35 lam35 app =>
     lam35 _ _ _ (t Tm35 var35 lam35 app).

Definition app35 {Γ A B} : Tm35 Γ (arr35 A B) -> Tm35 Γ A -> Tm35 Γ B
 := fun t u Tm35 var35 lam35 app35 =>
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


Definition Ty36 : Set
 := forall (Ty36 : Set)
      (base   : Ty36)
      (arr : Ty36 -> Ty36 -> Ty36)
    , Ty36.

Definition base36 : Ty36 := fun _ base36 _ => base36.

Definition arr36 : Ty36 -> Ty36 -> Ty36
 := fun A B Ty36 base36 arr36 =>
     arr36 (A Ty36 base36 arr36) (B Ty36 base36 arr36).

Definition Con36 : Set
 := forall (Con36  : Set)
      (nil  : Con36)
      (snoc : Con36 -> Ty36 -> Con36)
    , Con36.

Definition nil36 : Con36
 := fun Con36 nil36 snoc => nil36.

Definition snoc36 : Con36 -> Ty36 -> Con36
 := fun Γ A Con36 nil36 snoc36 => snoc36 (Γ Con36 nil36 snoc36) A.

Definition Var36 : Con36 -> Ty36 -> Set
 := fun Γ A =>
   forall (Var36 : Con36 -> Ty36 -> Set)
     (vz  : forall Γ A, Var36 (snoc36 Γ A) A)
     (vs  : forall Γ B A, Var36 Γ A -> Var36 (snoc36 Γ B) A)
   , Var36 Γ A.

Definition vz36 {Γ A} : Var36 (snoc36 Γ A) A
 := fun Var36 vz36 vs => vz36 _ _.

Definition vs36 {Γ B A} : Var36 Γ A -> Var36 (snoc36 Γ B) A
 := fun x Var36 vz36 vs36 => vs36 _ _ _ (x Var36 vz36 vs36).

Definition Tm36 : Con36 -> Ty36 -> Set
 := fun Γ A =>
   forall (Tm36  : Con36 -> Ty36 -> Set)
     (var   : forall Γ A     , Var36 Γ A -> Tm36 Γ A)
     (lam   : forall Γ A B   , Tm36 (snoc36 Γ A) B -> Tm36 Γ (arr36 A B))
     (app   : forall Γ A B   , Tm36 Γ (arr36 A B) -> Tm36 Γ A -> Tm36 Γ B)
   , Tm36 Γ A.

Definition var36 {Γ A} : Var36 Γ A -> Tm36 Γ A
 := fun x Tm36 var36 lam app =>
     var36 _ _ x.

Definition lam36 {Γ A B} : Tm36 (snoc36 Γ A) B -> Tm36 Γ (arr36 A B)
 := fun t Tm36 var36 lam36 app =>
     lam36 _ _ _ (t Tm36 var36 lam36 app).

Definition app36 {Γ A B} : Tm36 Γ (arr36 A B) -> Tm36 Γ A -> Tm36 Γ B
 := fun t u Tm36 var36 lam36 app36 =>
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


Definition Ty37 : Set
 := forall (Ty37 : Set)
      (base   : Ty37)
      (arr : Ty37 -> Ty37 -> Ty37)
    , Ty37.

Definition base37 : Ty37 := fun _ base37 _ => base37.

Definition arr37 : Ty37 -> Ty37 -> Ty37
 := fun A B Ty37 base37 arr37 =>
     arr37 (A Ty37 base37 arr37) (B Ty37 base37 arr37).

Definition Con37 : Set
 := forall (Con37  : Set)
      (nil  : Con37)
      (snoc : Con37 -> Ty37 -> Con37)
    , Con37.

Definition nil37 : Con37
 := fun Con37 nil37 snoc => nil37.

Definition snoc37 : Con37 -> Ty37 -> Con37
 := fun Γ A Con37 nil37 snoc37 => snoc37 (Γ Con37 nil37 snoc37) A.

Definition Var37 : Con37 -> Ty37 -> Set
 := fun Γ A =>
   forall (Var37 : Con37 -> Ty37 -> Set)
     (vz  : forall Γ A, Var37 (snoc37 Γ A) A)
     (vs  : forall Γ B A, Var37 Γ A -> Var37 (snoc37 Γ B) A)
   , Var37 Γ A.

Definition vz37 {Γ A} : Var37 (snoc37 Γ A) A
 := fun Var37 vz37 vs => vz37 _ _.

Definition vs37 {Γ B A} : Var37 Γ A -> Var37 (snoc37 Γ B) A
 := fun x Var37 vz37 vs37 => vs37 _ _ _ (x Var37 vz37 vs37).

Definition Tm37 : Con37 -> Ty37 -> Set
 := fun Γ A =>
   forall (Tm37  : Con37 -> Ty37 -> Set)
     (var   : forall Γ A     , Var37 Γ A -> Tm37 Γ A)
     (lam   : forall Γ A B   , Tm37 (snoc37 Γ A) B -> Tm37 Γ (arr37 A B))
     (app   : forall Γ A B   , Tm37 Γ (arr37 A B) -> Tm37 Γ A -> Tm37 Γ B)
   , Tm37 Γ A.

Definition var37 {Γ A} : Var37 Γ A -> Tm37 Γ A
 := fun x Tm37 var37 lam app =>
     var37 _ _ x.

Definition lam37 {Γ A B} : Tm37 (snoc37 Γ A) B -> Tm37 Γ (arr37 A B)
 := fun t Tm37 var37 lam37 app =>
     lam37 _ _ _ (t Tm37 var37 lam37 app).

Definition app37 {Γ A B} : Tm37 Γ (arr37 A B) -> Tm37 Γ A -> Tm37 Γ B
 := fun t u Tm37 var37 lam37 app37 =>
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


Definition Ty38 : Set
 := forall (Ty38 : Set)
      (base   : Ty38)
      (arr : Ty38 -> Ty38 -> Ty38)
    , Ty38.

Definition base38 : Ty38 := fun _ base38 _ => base38.

Definition arr38 : Ty38 -> Ty38 -> Ty38
 := fun A B Ty38 base38 arr38 =>
     arr38 (A Ty38 base38 arr38) (B Ty38 base38 arr38).

Definition Con38 : Set
 := forall (Con38  : Set)
      (nil  : Con38)
      (snoc : Con38 -> Ty38 -> Con38)
    , Con38.

Definition nil38 : Con38
 := fun Con38 nil38 snoc => nil38.

Definition snoc38 : Con38 -> Ty38 -> Con38
 := fun Γ A Con38 nil38 snoc38 => snoc38 (Γ Con38 nil38 snoc38) A.

Definition Var38 : Con38 -> Ty38 -> Set
 := fun Γ A =>
   forall (Var38 : Con38 -> Ty38 -> Set)
     (vz  : forall Γ A, Var38 (snoc38 Γ A) A)
     (vs  : forall Γ B A, Var38 Γ A -> Var38 (snoc38 Γ B) A)
   , Var38 Γ A.

Definition vz38 {Γ A} : Var38 (snoc38 Γ A) A
 := fun Var38 vz38 vs => vz38 _ _.

Definition vs38 {Γ B A} : Var38 Γ A -> Var38 (snoc38 Γ B) A
 := fun x Var38 vz38 vs38 => vs38 _ _ _ (x Var38 vz38 vs38).

Definition Tm38 : Con38 -> Ty38 -> Set
 := fun Γ A =>
   forall (Tm38  : Con38 -> Ty38 -> Set)
     (var   : forall Γ A     , Var38 Γ A -> Tm38 Γ A)
     (lam   : forall Γ A B   , Tm38 (snoc38 Γ A) B -> Tm38 Γ (arr38 A B))
     (app   : forall Γ A B   , Tm38 Γ (arr38 A B) -> Tm38 Γ A -> Tm38 Γ B)
   , Tm38 Γ A.

Definition var38 {Γ A} : Var38 Γ A -> Tm38 Γ A
 := fun x Tm38 var38 lam app =>
     var38 _ _ x.

Definition lam38 {Γ A B} : Tm38 (snoc38 Γ A) B -> Tm38 Γ (arr38 A B)
 := fun t Tm38 var38 lam38 app =>
     lam38 _ _ _ (t Tm38 var38 lam38 app).

Definition app38 {Γ A B} : Tm38 Γ (arr38 A B) -> Tm38 Γ A -> Tm38 Γ B
 := fun t u Tm38 var38 lam38 app38 =>
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


Definition Ty39 : Set
 := forall (Ty39 : Set)
      (base   : Ty39)
      (arr : Ty39 -> Ty39 -> Ty39)
    , Ty39.

Definition base39 : Ty39 := fun _ base39 _ => base39.

Definition arr39 : Ty39 -> Ty39 -> Ty39
 := fun A B Ty39 base39 arr39 =>
     arr39 (A Ty39 base39 arr39) (B Ty39 base39 arr39).

Definition Con39 : Set
 := forall (Con39  : Set)
      (nil  : Con39)
      (snoc : Con39 -> Ty39 -> Con39)
    , Con39.

Definition nil39 : Con39
 := fun Con39 nil39 snoc => nil39.

Definition snoc39 : Con39 -> Ty39 -> Con39
 := fun Γ A Con39 nil39 snoc39 => snoc39 (Γ Con39 nil39 snoc39) A.

Definition Var39 : Con39 -> Ty39 -> Set
 := fun Γ A =>
   forall (Var39 : Con39 -> Ty39 -> Set)
     (vz  : forall Γ A, Var39 (snoc39 Γ A) A)
     (vs  : forall Γ B A, Var39 Γ A -> Var39 (snoc39 Γ B) A)
   , Var39 Γ A.

Definition vz39 {Γ A} : Var39 (snoc39 Γ A) A
 := fun Var39 vz39 vs => vz39 _ _.

Definition vs39 {Γ B A} : Var39 Γ A -> Var39 (snoc39 Γ B) A
 := fun x Var39 vz39 vs39 => vs39 _ _ _ (x Var39 vz39 vs39).

Definition Tm39 : Con39 -> Ty39 -> Set
 := fun Γ A =>
   forall (Tm39  : Con39 -> Ty39 -> Set)
     (var   : forall Γ A     , Var39 Γ A -> Tm39 Γ A)
     (lam   : forall Γ A B   , Tm39 (snoc39 Γ A) B -> Tm39 Γ (arr39 A B))
     (app   : forall Γ A B   , Tm39 Γ (arr39 A B) -> Tm39 Γ A -> Tm39 Γ B)
   , Tm39 Γ A.

Definition var39 {Γ A} : Var39 Γ A -> Tm39 Γ A
 := fun x Tm39 var39 lam app =>
     var39 _ _ x.

Definition lam39 {Γ A B} : Tm39 (snoc39 Γ A) B -> Tm39 Γ (arr39 A B)
 := fun t Tm39 var39 lam39 app =>
     lam39 _ _ _ (t Tm39 var39 lam39 app).

Definition app39 {Γ A B} : Tm39 Γ (arr39 A B) -> Tm39 Γ A -> Tm39 Γ B
 := fun t u Tm39 var39 lam39 app39 =>
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


Definition Ty40 : Set
 := forall (Ty40 : Set)
      (base   : Ty40)
      (arr : Ty40 -> Ty40 -> Ty40)
    , Ty40.

Definition base40 : Ty40 := fun _ base40 _ => base40.

Definition arr40 : Ty40 -> Ty40 -> Ty40
 := fun A B Ty40 base40 arr40 =>
     arr40 (A Ty40 base40 arr40) (B Ty40 base40 arr40).

Definition Con40 : Set
 := forall (Con40  : Set)
      (nil  : Con40)
      (snoc : Con40 -> Ty40 -> Con40)
    , Con40.

Definition nil40 : Con40
 := fun Con40 nil40 snoc => nil40.

Definition snoc40 : Con40 -> Ty40 -> Con40
 := fun Γ A Con40 nil40 snoc40 => snoc40 (Γ Con40 nil40 snoc40) A.

Definition Var40 : Con40 -> Ty40 -> Set
 := fun Γ A =>
   forall (Var40 : Con40 -> Ty40 -> Set)
     (vz  : forall Γ A, Var40 (snoc40 Γ A) A)
     (vs  : forall Γ B A, Var40 Γ A -> Var40 (snoc40 Γ B) A)
   , Var40 Γ A.

Definition vz40 {Γ A} : Var40 (snoc40 Γ A) A
 := fun Var40 vz40 vs => vz40 _ _.

Definition vs40 {Γ B A} : Var40 Γ A -> Var40 (snoc40 Γ B) A
 := fun x Var40 vz40 vs40 => vs40 _ _ _ (x Var40 vz40 vs40).

Definition Tm40 : Con40 -> Ty40 -> Set
 := fun Γ A =>
   forall (Tm40  : Con40 -> Ty40 -> Set)
     (var   : forall Γ A     , Var40 Γ A -> Tm40 Γ A)
     (lam   : forall Γ A B   , Tm40 (snoc40 Γ A) B -> Tm40 Γ (arr40 A B))
     (app   : forall Γ A B   , Tm40 Γ (arr40 A B) -> Tm40 Γ A -> Tm40 Γ B)
   , Tm40 Γ A.

Definition var40 {Γ A} : Var40 Γ A -> Tm40 Γ A
 := fun x Tm40 var40 lam app =>
     var40 _ _ x.

Definition lam40 {Γ A B} : Tm40 (snoc40 Γ A) B -> Tm40 Γ (arr40 A B)
 := fun t Tm40 var40 lam40 app =>
     lam40 _ _ _ (t Tm40 var40 lam40 app).

Definition app40 {Γ A B} : Tm40 Γ (arr40 A B) -> Tm40 Γ A -> Tm40 Γ B
 := fun t u Tm40 var40 lam40 app40 =>
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


Definition Ty41 : Set
 := forall (Ty41 : Set)
      (base   : Ty41)
      (arr : Ty41 -> Ty41 -> Ty41)
    , Ty41.

Definition base41 : Ty41 := fun _ base41 _ => base41.

Definition arr41 : Ty41 -> Ty41 -> Ty41
 := fun A B Ty41 base41 arr41 =>
     arr41 (A Ty41 base41 arr41) (B Ty41 base41 arr41).

Definition Con41 : Set
 := forall (Con41  : Set)
      (nil  : Con41)
      (snoc : Con41 -> Ty41 -> Con41)
    , Con41.

Definition nil41 : Con41
 := fun Con41 nil41 snoc => nil41.

Definition snoc41 : Con41 -> Ty41 -> Con41
 := fun Γ A Con41 nil41 snoc41 => snoc41 (Γ Con41 nil41 snoc41) A.

Definition Var41 : Con41 -> Ty41 -> Set
 := fun Γ A =>
   forall (Var41 : Con41 -> Ty41 -> Set)
     (vz  : forall Γ A, Var41 (snoc41 Γ A) A)
     (vs  : forall Γ B A, Var41 Γ A -> Var41 (snoc41 Γ B) A)
   , Var41 Γ A.

Definition vz41 {Γ A} : Var41 (snoc41 Γ A) A
 := fun Var41 vz41 vs => vz41 _ _.

Definition vs41 {Γ B A} : Var41 Γ A -> Var41 (snoc41 Γ B) A
 := fun x Var41 vz41 vs41 => vs41 _ _ _ (x Var41 vz41 vs41).

Definition Tm41 : Con41 -> Ty41 -> Set
 := fun Γ A =>
   forall (Tm41  : Con41 -> Ty41 -> Set)
     (var   : forall Γ A     , Var41 Γ A -> Tm41 Γ A)
     (lam   : forall Γ A B   , Tm41 (snoc41 Γ A) B -> Tm41 Γ (arr41 A B))
     (app   : forall Γ A B   , Tm41 Γ (arr41 A B) -> Tm41 Γ A -> Tm41 Γ B)
   , Tm41 Γ A.

Definition var41 {Γ A} : Var41 Γ A -> Tm41 Γ A
 := fun x Tm41 var41 lam app =>
     var41 _ _ x.

Definition lam41 {Γ A B} : Tm41 (snoc41 Γ A) B -> Tm41 Γ (arr41 A B)
 := fun t Tm41 var41 lam41 app =>
     lam41 _ _ _ (t Tm41 var41 lam41 app).

Definition app41 {Γ A B} : Tm41 Γ (arr41 A B) -> Tm41 Γ A -> Tm41 Γ B
 := fun t u Tm41 var41 lam41 app41 =>
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


Definition Ty42 : Set
 := forall (Ty42 : Set)
      (base   : Ty42)
      (arr : Ty42 -> Ty42 -> Ty42)
    , Ty42.

Definition base42 : Ty42 := fun _ base42 _ => base42.

Definition arr42 : Ty42 -> Ty42 -> Ty42
 := fun A B Ty42 base42 arr42 =>
     arr42 (A Ty42 base42 arr42) (B Ty42 base42 arr42).

Definition Con42 : Set
 := forall (Con42  : Set)
      (nil  : Con42)
      (snoc : Con42 -> Ty42 -> Con42)
    , Con42.

Definition nil42 : Con42
 := fun Con42 nil42 snoc => nil42.

Definition snoc42 : Con42 -> Ty42 -> Con42
 := fun Γ A Con42 nil42 snoc42 => snoc42 (Γ Con42 nil42 snoc42) A.

Definition Var42 : Con42 -> Ty42 -> Set
 := fun Γ A =>
   forall (Var42 : Con42 -> Ty42 -> Set)
     (vz  : forall Γ A, Var42 (snoc42 Γ A) A)
     (vs  : forall Γ B A, Var42 Γ A -> Var42 (snoc42 Γ B) A)
   , Var42 Γ A.

Definition vz42 {Γ A} : Var42 (snoc42 Γ A) A
 := fun Var42 vz42 vs => vz42 _ _.

Definition vs42 {Γ B A} : Var42 Γ A -> Var42 (snoc42 Γ B) A
 := fun x Var42 vz42 vs42 => vs42 _ _ _ (x Var42 vz42 vs42).

Definition Tm42 : Con42 -> Ty42 -> Set
 := fun Γ A =>
   forall (Tm42  : Con42 -> Ty42 -> Set)
     (var   : forall Γ A     , Var42 Γ A -> Tm42 Γ A)
     (lam   : forall Γ A B   , Tm42 (snoc42 Γ A) B -> Tm42 Γ (arr42 A B))
     (app   : forall Γ A B   , Tm42 Γ (arr42 A B) -> Tm42 Γ A -> Tm42 Γ B)
   , Tm42 Γ A.

Definition var42 {Γ A} : Var42 Γ A -> Tm42 Γ A
 := fun x Tm42 var42 lam app =>
     var42 _ _ x.

Definition lam42 {Γ A B} : Tm42 (snoc42 Γ A) B -> Tm42 Γ (arr42 A B)
 := fun t Tm42 var42 lam42 app =>
     lam42 _ _ _ (t Tm42 var42 lam42 app).

Definition app42 {Γ A B} : Tm42 Γ (arr42 A B) -> Tm42 Γ A -> Tm42 Γ B
 := fun t u Tm42 var42 lam42 app42 =>
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


Definition Ty43 : Set
 := forall (Ty43 : Set)
      (base   : Ty43)
      (arr : Ty43 -> Ty43 -> Ty43)
    , Ty43.

Definition base43 : Ty43 := fun _ base43 _ => base43.

Definition arr43 : Ty43 -> Ty43 -> Ty43
 := fun A B Ty43 base43 arr43 =>
     arr43 (A Ty43 base43 arr43) (B Ty43 base43 arr43).

Definition Con43 : Set
 := forall (Con43  : Set)
      (nil  : Con43)
      (snoc : Con43 -> Ty43 -> Con43)
    , Con43.

Definition nil43 : Con43
 := fun Con43 nil43 snoc => nil43.

Definition snoc43 : Con43 -> Ty43 -> Con43
 := fun Γ A Con43 nil43 snoc43 => snoc43 (Γ Con43 nil43 snoc43) A.

Definition Var43 : Con43 -> Ty43 -> Set
 := fun Γ A =>
   forall (Var43 : Con43 -> Ty43 -> Set)
     (vz  : forall Γ A, Var43 (snoc43 Γ A) A)
     (vs  : forall Γ B A, Var43 Γ A -> Var43 (snoc43 Γ B) A)
   , Var43 Γ A.

Definition vz43 {Γ A} : Var43 (snoc43 Γ A) A
 := fun Var43 vz43 vs => vz43 _ _.

Definition vs43 {Γ B A} : Var43 Γ A -> Var43 (snoc43 Γ B) A
 := fun x Var43 vz43 vs43 => vs43 _ _ _ (x Var43 vz43 vs43).

Definition Tm43 : Con43 -> Ty43 -> Set
 := fun Γ A =>
   forall (Tm43  : Con43 -> Ty43 -> Set)
     (var   : forall Γ A     , Var43 Γ A -> Tm43 Γ A)
     (lam   : forall Γ A B   , Tm43 (snoc43 Γ A) B -> Tm43 Γ (arr43 A B))
     (app   : forall Γ A B   , Tm43 Γ (arr43 A B) -> Tm43 Γ A -> Tm43 Γ B)
   , Tm43 Γ A.

Definition var43 {Γ A} : Var43 Γ A -> Tm43 Γ A
 := fun x Tm43 var43 lam app =>
     var43 _ _ x.

Definition lam43 {Γ A B} : Tm43 (snoc43 Γ A) B -> Tm43 Γ (arr43 A B)
 := fun t Tm43 var43 lam43 app =>
     lam43 _ _ _ (t Tm43 var43 lam43 app).

Definition app43 {Γ A B} : Tm43 Γ (arr43 A B) -> Tm43 Γ A -> Tm43 Γ B
 := fun t u Tm43 var43 lam43 app43 =>
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


Definition Ty44 : Set
 := forall (Ty44 : Set)
      (base   : Ty44)
      (arr : Ty44 -> Ty44 -> Ty44)
    , Ty44.

Definition base44 : Ty44 := fun _ base44 _ => base44.

Definition arr44 : Ty44 -> Ty44 -> Ty44
 := fun A B Ty44 base44 arr44 =>
     arr44 (A Ty44 base44 arr44) (B Ty44 base44 arr44).

Definition Con44 : Set
 := forall (Con44  : Set)
      (nil  : Con44)
      (snoc : Con44 -> Ty44 -> Con44)
    , Con44.

Definition nil44 : Con44
 := fun Con44 nil44 snoc => nil44.

Definition snoc44 : Con44 -> Ty44 -> Con44
 := fun Γ A Con44 nil44 snoc44 => snoc44 (Γ Con44 nil44 snoc44) A.

Definition Var44 : Con44 -> Ty44 -> Set
 := fun Γ A =>
   forall (Var44 : Con44 -> Ty44 -> Set)
     (vz  : forall Γ A, Var44 (snoc44 Γ A) A)
     (vs  : forall Γ B A, Var44 Γ A -> Var44 (snoc44 Γ B) A)
   , Var44 Γ A.

Definition vz44 {Γ A} : Var44 (snoc44 Γ A) A
 := fun Var44 vz44 vs => vz44 _ _.

Definition vs44 {Γ B A} : Var44 Γ A -> Var44 (snoc44 Γ B) A
 := fun x Var44 vz44 vs44 => vs44 _ _ _ (x Var44 vz44 vs44).

Definition Tm44 : Con44 -> Ty44 -> Set
 := fun Γ A =>
   forall (Tm44  : Con44 -> Ty44 -> Set)
     (var   : forall Γ A     , Var44 Γ A -> Tm44 Γ A)
     (lam   : forall Γ A B   , Tm44 (snoc44 Γ A) B -> Tm44 Γ (arr44 A B))
     (app   : forall Γ A B   , Tm44 Γ (arr44 A B) -> Tm44 Γ A -> Tm44 Γ B)
   , Tm44 Γ A.

Definition var44 {Γ A} : Var44 Γ A -> Tm44 Γ A
 := fun x Tm44 var44 lam app =>
     var44 _ _ x.

Definition lam44 {Γ A B} : Tm44 (snoc44 Γ A) B -> Tm44 Γ (arr44 A B)
 := fun t Tm44 var44 lam44 app =>
     lam44 _ _ _ (t Tm44 var44 lam44 app).

Definition app44 {Γ A B} : Tm44 Γ (arr44 A B) -> Tm44 Γ A -> Tm44 Γ B
 := fun t u Tm44 var44 lam44 app44 =>
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


Definition Ty45 : Set
 := forall (Ty45 : Set)
      (base   : Ty45)
      (arr : Ty45 -> Ty45 -> Ty45)
    , Ty45.

Definition base45 : Ty45 := fun _ base45 _ => base45.

Definition arr45 : Ty45 -> Ty45 -> Ty45
 := fun A B Ty45 base45 arr45 =>
     arr45 (A Ty45 base45 arr45) (B Ty45 base45 arr45).

Definition Con45 : Set
 := forall (Con45  : Set)
      (nil  : Con45)
      (snoc : Con45 -> Ty45 -> Con45)
    , Con45.

Definition nil45 : Con45
 := fun Con45 nil45 snoc => nil45.

Definition snoc45 : Con45 -> Ty45 -> Con45
 := fun Γ A Con45 nil45 snoc45 => snoc45 (Γ Con45 nil45 snoc45) A.

Definition Var45 : Con45 -> Ty45 -> Set
 := fun Γ A =>
   forall (Var45 : Con45 -> Ty45 -> Set)
     (vz  : forall Γ A, Var45 (snoc45 Γ A) A)
     (vs  : forall Γ B A, Var45 Γ A -> Var45 (snoc45 Γ B) A)
   , Var45 Γ A.

Definition vz45 {Γ A} : Var45 (snoc45 Γ A) A
 := fun Var45 vz45 vs => vz45 _ _.

Definition vs45 {Γ B A} : Var45 Γ A -> Var45 (snoc45 Γ B) A
 := fun x Var45 vz45 vs45 => vs45 _ _ _ (x Var45 vz45 vs45).

Definition Tm45 : Con45 -> Ty45 -> Set
 := fun Γ A =>
   forall (Tm45  : Con45 -> Ty45 -> Set)
     (var   : forall Γ A     , Var45 Γ A -> Tm45 Γ A)
     (lam   : forall Γ A B   , Tm45 (snoc45 Γ A) B -> Tm45 Γ (arr45 A B))
     (app   : forall Γ A B   , Tm45 Γ (arr45 A B) -> Tm45 Γ A -> Tm45 Γ B)
   , Tm45 Γ A.

Definition var45 {Γ A} : Var45 Γ A -> Tm45 Γ A
 := fun x Tm45 var45 lam app =>
     var45 _ _ x.

Definition lam45 {Γ A B} : Tm45 (snoc45 Γ A) B -> Tm45 Γ (arr45 A B)
 := fun t Tm45 var45 lam45 app =>
     lam45 _ _ _ (t Tm45 var45 lam45 app).

Definition app45 {Γ A B} : Tm45 Γ (arr45 A B) -> Tm45 Γ A -> Tm45 Γ B
 := fun t u Tm45 var45 lam45 app45 =>
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


Definition Ty46 : Set
 := forall (Ty46 : Set)
      (base   : Ty46)
      (arr : Ty46 -> Ty46 -> Ty46)
    , Ty46.

Definition base46 : Ty46 := fun _ base46 _ => base46.

Definition arr46 : Ty46 -> Ty46 -> Ty46
 := fun A B Ty46 base46 arr46 =>
     arr46 (A Ty46 base46 arr46) (B Ty46 base46 arr46).

Definition Con46 : Set
 := forall (Con46  : Set)
      (nil  : Con46)
      (snoc : Con46 -> Ty46 -> Con46)
    , Con46.

Definition nil46 : Con46
 := fun Con46 nil46 snoc => nil46.

Definition snoc46 : Con46 -> Ty46 -> Con46
 := fun Γ A Con46 nil46 snoc46 => snoc46 (Γ Con46 nil46 snoc46) A.

Definition Var46 : Con46 -> Ty46 -> Set
 := fun Γ A =>
   forall (Var46 : Con46 -> Ty46 -> Set)
     (vz  : forall Γ A, Var46 (snoc46 Γ A) A)
     (vs  : forall Γ B A, Var46 Γ A -> Var46 (snoc46 Γ B) A)
   , Var46 Γ A.

Definition vz46 {Γ A} : Var46 (snoc46 Γ A) A
 := fun Var46 vz46 vs => vz46 _ _.

Definition vs46 {Γ B A} : Var46 Γ A -> Var46 (snoc46 Γ B) A
 := fun x Var46 vz46 vs46 => vs46 _ _ _ (x Var46 vz46 vs46).

Definition Tm46 : Con46 -> Ty46 -> Set
 := fun Γ A =>
   forall (Tm46  : Con46 -> Ty46 -> Set)
     (var   : forall Γ A     , Var46 Γ A -> Tm46 Γ A)
     (lam   : forall Γ A B   , Tm46 (snoc46 Γ A) B -> Tm46 Γ (arr46 A B))
     (app   : forall Γ A B   , Tm46 Γ (arr46 A B) -> Tm46 Γ A -> Tm46 Γ B)
   , Tm46 Γ A.

Definition var46 {Γ A} : Var46 Γ A -> Tm46 Γ A
 := fun x Tm46 var46 lam app =>
     var46 _ _ x.

Definition lam46 {Γ A B} : Tm46 (snoc46 Γ A) B -> Tm46 Γ (arr46 A B)
 := fun t Tm46 var46 lam46 app =>
     lam46 _ _ _ (t Tm46 var46 lam46 app).

Definition app46 {Γ A B} : Tm46 Γ (arr46 A B) -> Tm46 Γ A -> Tm46 Γ B
 := fun t u Tm46 var46 lam46 app46 =>
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


Definition Ty47 : Set
 := forall (Ty47 : Set)
      (base   : Ty47)
      (arr : Ty47 -> Ty47 -> Ty47)
    , Ty47.

Definition base47 : Ty47 := fun _ base47 _ => base47.

Definition arr47 : Ty47 -> Ty47 -> Ty47
 := fun A B Ty47 base47 arr47 =>
     arr47 (A Ty47 base47 arr47) (B Ty47 base47 arr47).

Definition Con47 : Set
 := forall (Con47  : Set)
      (nil  : Con47)
      (snoc : Con47 -> Ty47 -> Con47)
    , Con47.

Definition nil47 : Con47
 := fun Con47 nil47 snoc => nil47.

Definition snoc47 : Con47 -> Ty47 -> Con47
 := fun Γ A Con47 nil47 snoc47 => snoc47 (Γ Con47 nil47 snoc47) A.

Definition Var47 : Con47 -> Ty47 -> Set
 := fun Γ A =>
   forall (Var47 : Con47 -> Ty47 -> Set)
     (vz  : forall Γ A, Var47 (snoc47 Γ A) A)
     (vs  : forall Γ B A, Var47 Γ A -> Var47 (snoc47 Γ B) A)
   , Var47 Γ A.

Definition vz47 {Γ A} : Var47 (snoc47 Γ A) A
 := fun Var47 vz47 vs => vz47 _ _.

Definition vs47 {Γ B A} : Var47 Γ A -> Var47 (snoc47 Γ B) A
 := fun x Var47 vz47 vs47 => vs47 _ _ _ (x Var47 vz47 vs47).

Definition Tm47 : Con47 -> Ty47 -> Set
 := fun Γ A =>
   forall (Tm47  : Con47 -> Ty47 -> Set)
     (var   : forall Γ A     , Var47 Γ A -> Tm47 Γ A)
     (lam   : forall Γ A B   , Tm47 (snoc47 Γ A) B -> Tm47 Γ (arr47 A B))
     (app   : forall Γ A B   , Tm47 Γ (arr47 A B) -> Tm47 Γ A -> Tm47 Γ B)
   , Tm47 Γ A.

Definition var47 {Γ A} : Var47 Γ A -> Tm47 Γ A
 := fun x Tm47 var47 lam app =>
     var47 _ _ x.

Definition lam47 {Γ A B} : Tm47 (snoc47 Γ A) B -> Tm47 Γ (arr47 A B)
 := fun t Tm47 var47 lam47 app =>
     lam47 _ _ _ (t Tm47 var47 lam47 app).

Definition app47 {Γ A B} : Tm47 Γ (arr47 A B) -> Tm47 Γ A -> Tm47 Γ B
 := fun t u Tm47 var47 lam47 app47 =>
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


Definition Ty48 : Set
 := forall (Ty48 : Set)
      (base   : Ty48)
      (arr : Ty48 -> Ty48 -> Ty48)
    , Ty48.

Definition base48 : Ty48 := fun _ base48 _ => base48.

Definition arr48 : Ty48 -> Ty48 -> Ty48
 := fun A B Ty48 base48 arr48 =>
     arr48 (A Ty48 base48 arr48) (B Ty48 base48 arr48).

Definition Con48 : Set
 := forall (Con48  : Set)
      (nil  : Con48)
      (snoc : Con48 -> Ty48 -> Con48)
    , Con48.

Definition nil48 : Con48
 := fun Con48 nil48 snoc => nil48.

Definition snoc48 : Con48 -> Ty48 -> Con48
 := fun Γ A Con48 nil48 snoc48 => snoc48 (Γ Con48 nil48 snoc48) A.

Definition Var48 : Con48 -> Ty48 -> Set
 := fun Γ A =>
   forall (Var48 : Con48 -> Ty48 -> Set)
     (vz  : forall Γ A, Var48 (snoc48 Γ A) A)
     (vs  : forall Γ B A, Var48 Γ A -> Var48 (snoc48 Γ B) A)
   , Var48 Γ A.

Definition vz48 {Γ A} : Var48 (snoc48 Γ A) A
 := fun Var48 vz48 vs => vz48 _ _.

Definition vs48 {Γ B A} : Var48 Γ A -> Var48 (snoc48 Γ B) A
 := fun x Var48 vz48 vs48 => vs48 _ _ _ (x Var48 vz48 vs48).

Definition Tm48 : Con48 -> Ty48 -> Set
 := fun Γ A =>
   forall (Tm48  : Con48 -> Ty48 -> Set)
     (var   : forall Γ A     , Var48 Γ A -> Tm48 Γ A)
     (lam   : forall Γ A B   , Tm48 (snoc48 Γ A) B -> Tm48 Γ (arr48 A B))
     (app   : forall Γ A B   , Tm48 Γ (arr48 A B) -> Tm48 Γ A -> Tm48 Γ B)
   , Tm48 Γ A.

Definition var48 {Γ A} : Var48 Γ A -> Tm48 Γ A
 := fun x Tm48 var48 lam app =>
     var48 _ _ x.

Definition lam48 {Γ A B} : Tm48 (snoc48 Γ A) B -> Tm48 Γ (arr48 A B)
 := fun t Tm48 var48 lam48 app =>
     lam48 _ _ _ (t Tm48 var48 lam48 app).

Definition app48 {Γ A B} : Tm48 Γ (arr48 A B) -> Tm48 Γ A -> Tm48 Γ B
 := fun t u Tm48 var48 lam48 app48 =>
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


Definition Ty49 : Set
 := forall (Ty49 : Set)
      (base   : Ty49)
      (arr : Ty49 -> Ty49 -> Ty49)
    , Ty49.

Definition base49 : Ty49 := fun _ base49 _ => base49.

Definition arr49 : Ty49 -> Ty49 -> Ty49
 := fun A B Ty49 base49 arr49 =>
     arr49 (A Ty49 base49 arr49) (B Ty49 base49 arr49).

Definition Con49 : Set
 := forall (Con49  : Set)
      (nil  : Con49)
      (snoc : Con49 -> Ty49 -> Con49)
    , Con49.

Definition nil49 : Con49
 := fun Con49 nil49 snoc => nil49.

Definition snoc49 : Con49 -> Ty49 -> Con49
 := fun Γ A Con49 nil49 snoc49 => snoc49 (Γ Con49 nil49 snoc49) A.

Definition Var49 : Con49 -> Ty49 -> Set
 := fun Γ A =>
   forall (Var49 : Con49 -> Ty49 -> Set)
     (vz  : forall Γ A, Var49 (snoc49 Γ A) A)
     (vs  : forall Γ B A, Var49 Γ A -> Var49 (snoc49 Γ B) A)
   , Var49 Γ A.

Definition vz49 {Γ A} : Var49 (snoc49 Γ A) A
 := fun Var49 vz49 vs => vz49 _ _.

Definition vs49 {Γ B A} : Var49 Γ A -> Var49 (snoc49 Γ B) A
 := fun x Var49 vz49 vs49 => vs49 _ _ _ (x Var49 vz49 vs49).

Definition Tm49 : Con49 -> Ty49 -> Set
 := fun Γ A =>
   forall (Tm49  : Con49 -> Ty49 -> Set)
     (var   : forall Γ A     , Var49 Γ A -> Tm49 Γ A)
     (lam   : forall Γ A B   , Tm49 (snoc49 Γ A) B -> Tm49 Γ (arr49 A B))
     (app   : forall Γ A B   , Tm49 Γ (arr49 A B) -> Tm49 Γ A -> Tm49 Γ B)
   , Tm49 Γ A.

Definition var49 {Γ A} : Var49 Γ A -> Tm49 Γ A
 := fun x Tm49 var49 lam app =>
     var49 _ _ x.

Definition lam49 {Γ A B} : Tm49 (snoc49 Γ A) B -> Tm49 Γ (arr49 A B)
 := fun t Tm49 var49 lam49 app =>
     lam49 _ _ _ (t Tm49 var49 lam49 app).

Definition app49 {Γ A B} : Tm49 Γ (arr49 A B) -> Tm49 Γ A -> Tm49 Γ B
 := fun t u Tm49 var49 lam49 app49 =>
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


Definition Ty50 : Set
 := forall (Ty50 : Set)
      (base   : Ty50)
      (arr : Ty50 -> Ty50 -> Ty50)
    , Ty50.

Definition base50 : Ty50 := fun _ base50 _ => base50.

Definition arr50 : Ty50 -> Ty50 -> Ty50
 := fun A B Ty50 base50 arr50 =>
     arr50 (A Ty50 base50 arr50) (B Ty50 base50 arr50).

Definition Con50 : Set
 := forall (Con50  : Set)
      (nil  : Con50)
      (snoc : Con50 -> Ty50 -> Con50)
    , Con50.

Definition nil50 : Con50
 := fun Con50 nil50 snoc => nil50.

Definition snoc50 : Con50 -> Ty50 -> Con50
 := fun Γ A Con50 nil50 snoc50 => snoc50 (Γ Con50 nil50 snoc50) A.

Definition Var50 : Con50 -> Ty50 -> Set
 := fun Γ A =>
   forall (Var50 : Con50 -> Ty50 -> Set)
     (vz  : forall Γ A, Var50 (snoc50 Γ A) A)
     (vs  : forall Γ B A, Var50 Γ A -> Var50 (snoc50 Γ B) A)
   , Var50 Γ A.

Definition vz50 {Γ A} : Var50 (snoc50 Γ A) A
 := fun Var50 vz50 vs => vz50 _ _.

Definition vs50 {Γ B A} : Var50 Γ A -> Var50 (snoc50 Γ B) A
 := fun x Var50 vz50 vs50 => vs50 _ _ _ (x Var50 vz50 vs50).

Definition Tm50 : Con50 -> Ty50 -> Set
 := fun Γ A =>
   forall (Tm50  : Con50 -> Ty50 -> Set)
     (var   : forall Γ A     , Var50 Γ A -> Tm50 Γ A)
     (lam   : forall Γ A B   , Tm50 (snoc50 Γ A) B -> Tm50 Γ (arr50 A B))
     (app   : forall Γ A B   , Tm50 Γ (arr50 A B) -> Tm50 Γ A -> Tm50 Γ B)
   , Tm50 Γ A.

Definition var50 {Γ A} : Var50 Γ A -> Tm50 Γ A
 := fun x Tm50 var50 lam app =>
     var50 _ _ x.

Definition lam50 {Γ A B} : Tm50 (snoc50 Γ A) B -> Tm50 Γ (arr50 A B)
 := fun t Tm50 var50 lam50 app =>
     lam50 _ _ _ (t Tm50 var50 lam50 app).

Definition app50 {Γ A B} : Tm50 Γ (arr50 A B) -> Tm50 Γ A -> Tm50 Γ B
 := fun t u Tm50 var50 lam50 app50 =>
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


Definition Ty51 : Set
 := forall (Ty51 : Set)
      (base   : Ty51)
      (arr : Ty51 -> Ty51 -> Ty51)
    , Ty51.

Definition base51 : Ty51 := fun _ base51 _ => base51.

Definition arr51 : Ty51 -> Ty51 -> Ty51
 := fun A B Ty51 base51 arr51 =>
     arr51 (A Ty51 base51 arr51) (B Ty51 base51 arr51).

Definition Con51 : Set
 := forall (Con51  : Set)
      (nil  : Con51)
      (snoc : Con51 -> Ty51 -> Con51)
    , Con51.

Definition nil51 : Con51
 := fun Con51 nil51 snoc => nil51.

Definition snoc51 : Con51 -> Ty51 -> Con51
 := fun Γ A Con51 nil51 snoc51 => snoc51 (Γ Con51 nil51 snoc51) A.

Definition Var51 : Con51 -> Ty51 -> Set
 := fun Γ A =>
   forall (Var51 : Con51 -> Ty51 -> Set)
     (vz  : forall Γ A, Var51 (snoc51 Γ A) A)
     (vs  : forall Γ B A, Var51 Γ A -> Var51 (snoc51 Γ B) A)
   , Var51 Γ A.

Definition vz51 {Γ A} : Var51 (snoc51 Γ A) A
 := fun Var51 vz51 vs => vz51 _ _.

Definition vs51 {Γ B A} : Var51 Γ A -> Var51 (snoc51 Γ B) A
 := fun x Var51 vz51 vs51 => vs51 _ _ _ (x Var51 vz51 vs51).

Definition Tm51 : Con51 -> Ty51 -> Set
 := fun Γ A =>
   forall (Tm51  : Con51 -> Ty51 -> Set)
     (var   : forall Γ A     , Var51 Γ A -> Tm51 Γ A)
     (lam   : forall Γ A B   , Tm51 (snoc51 Γ A) B -> Tm51 Γ (arr51 A B))
     (app   : forall Γ A B   , Tm51 Γ (arr51 A B) -> Tm51 Γ A -> Tm51 Γ B)
   , Tm51 Γ A.

Definition var51 {Γ A} : Var51 Γ A -> Tm51 Γ A
 := fun x Tm51 var51 lam app =>
     var51 _ _ x.

Definition lam51 {Γ A B} : Tm51 (snoc51 Γ A) B -> Tm51 Γ (arr51 A B)
 := fun t Tm51 var51 lam51 app =>
     lam51 _ _ _ (t Tm51 var51 lam51 app).

Definition app51 {Γ A B} : Tm51 Γ (arr51 A B) -> Tm51 Γ A -> Tm51 Γ B
 := fun t u Tm51 var51 lam51 app51 =>
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


Definition Ty52 : Set
 := forall (Ty52 : Set)
      (base   : Ty52)
      (arr : Ty52 -> Ty52 -> Ty52)
    , Ty52.

Definition base52 : Ty52 := fun _ base52 _ => base52.

Definition arr52 : Ty52 -> Ty52 -> Ty52
 := fun A B Ty52 base52 arr52 =>
     arr52 (A Ty52 base52 arr52) (B Ty52 base52 arr52).

Definition Con52 : Set
 := forall (Con52  : Set)
      (nil  : Con52)
      (snoc : Con52 -> Ty52 -> Con52)
    , Con52.

Definition nil52 : Con52
 := fun Con52 nil52 snoc => nil52.

Definition snoc52 : Con52 -> Ty52 -> Con52
 := fun Γ A Con52 nil52 snoc52 => snoc52 (Γ Con52 nil52 snoc52) A.

Definition Var52 : Con52 -> Ty52 -> Set
 := fun Γ A =>
   forall (Var52 : Con52 -> Ty52 -> Set)
     (vz  : forall Γ A, Var52 (snoc52 Γ A) A)
     (vs  : forall Γ B A, Var52 Γ A -> Var52 (snoc52 Γ B) A)
   , Var52 Γ A.

Definition vz52 {Γ A} : Var52 (snoc52 Γ A) A
 := fun Var52 vz52 vs => vz52 _ _.

Definition vs52 {Γ B A} : Var52 Γ A -> Var52 (snoc52 Γ B) A
 := fun x Var52 vz52 vs52 => vs52 _ _ _ (x Var52 vz52 vs52).

Definition Tm52 : Con52 -> Ty52 -> Set
 := fun Γ A =>
   forall (Tm52  : Con52 -> Ty52 -> Set)
     (var   : forall Γ A     , Var52 Γ A -> Tm52 Γ A)
     (lam   : forall Γ A B   , Tm52 (snoc52 Γ A) B -> Tm52 Γ (arr52 A B))
     (app   : forall Γ A B   , Tm52 Γ (arr52 A B) -> Tm52 Γ A -> Tm52 Γ B)
   , Tm52 Γ A.

Definition var52 {Γ A} : Var52 Γ A -> Tm52 Γ A
 := fun x Tm52 var52 lam app =>
     var52 _ _ x.

Definition lam52 {Γ A B} : Tm52 (snoc52 Γ A) B -> Tm52 Γ (arr52 A B)
 := fun t Tm52 var52 lam52 app =>
     lam52 _ _ _ (t Tm52 var52 lam52 app).

Definition app52 {Γ A B} : Tm52 Γ (arr52 A B) -> Tm52 Γ A -> Tm52 Γ B
 := fun t u Tm52 var52 lam52 app52 =>
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


Definition Ty53 : Set
 := forall (Ty53 : Set)
      (base   : Ty53)
      (arr : Ty53 -> Ty53 -> Ty53)
    , Ty53.

Definition base53 : Ty53 := fun _ base53 _ => base53.

Definition arr53 : Ty53 -> Ty53 -> Ty53
 := fun A B Ty53 base53 arr53 =>
     arr53 (A Ty53 base53 arr53) (B Ty53 base53 arr53).

Definition Con53 : Set
 := forall (Con53  : Set)
      (nil  : Con53)
      (snoc : Con53 -> Ty53 -> Con53)
    , Con53.

Definition nil53 : Con53
 := fun Con53 nil53 snoc => nil53.

Definition snoc53 : Con53 -> Ty53 -> Con53
 := fun Γ A Con53 nil53 snoc53 => snoc53 (Γ Con53 nil53 snoc53) A.

Definition Var53 : Con53 -> Ty53 -> Set
 := fun Γ A =>
   forall (Var53 : Con53 -> Ty53 -> Set)
     (vz  : forall Γ A, Var53 (snoc53 Γ A) A)
     (vs  : forall Γ B A, Var53 Γ A -> Var53 (snoc53 Γ B) A)
   , Var53 Γ A.

Definition vz53 {Γ A} : Var53 (snoc53 Γ A) A
 := fun Var53 vz53 vs => vz53 _ _.

Definition vs53 {Γ B A} : Var53 Γ A -> Var53 (snoc53 Γ B) A
 := fun x Var53 vz53 vs53 => vs53 _ _ _ (x Var53 vz53 vs53).

Definition Tm53 : Con53 -> Ty53 -> Set
 := fun Γ A =>
   forall (Tm53  : Con53 -> Ty53 -> Set)
     (var   : forall Γ A     , Var53 Γ A -> Tm53 Γ A)
     (lam   : forall Γ A B   , Tm53 (snoc53 Γ A) B -> Tm53 Γ (arr53 A B))
     (app   : forall Γ A B   , Tm53 Γ (arr53 A B) -> Tm53 Γ A -> Tm53 Γ B)
   , Tm53 Γ A.

Definition var53 {Γ A} : Var53 Γ A -> Tm53 Γ A
 := fun x Tm53 var53 lam app =>
     var53 _ _ x.

Definition lam53 {Γ A B} : Tm53 (snoc53 Γ A) B -> Tm53 Γ (arr53 A B)
 := fun t Tm53 var53 lam53 app =>
     lam53 _ _ _ (t Tm53 var53 lam53 app).

Definition app53 {Γ A B} : Tm53 Γ (arr53 A B) -> Tm53 Γ A -> Tm53 Γ B
 := fun t u Tm53 var53 lam53 app53 =>
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


Definition Ty54 : Set
 := forall (Ty54 : Set)
      (base   : Ty54)
      (arr : Ty54 -> Ty54 -> Ty54)
    , Ty54.

Definition base54 : Ty54 := fun _ base54 _ => base54.

Definition arr54 : Ty54 -> Ty54 -> Ty54
 := fun A B Ty54 base54 arr54 =>
     arr54 (A Ty54 base54 arr54) (B Ty54 base54 arr54).

Definition Con54 : Set
 := forall (Con54  : Set)
      (nil  : Con54)
      (snoc : Con54 -> Ty54 -> Con54)
    , Con54.

Definition nil54 : Con54
 := fun Con54 nil54 snoc => nil54.

Definition snoc54 : Con54 -> Ty54 -> Con54
 := fun Γ A Con54 nil54 snoc54 => snoc54 (Γ Con54 nil54 snoc54) A.

Definition Var54 : Con54 -> Ty54 -> Set
 := fun Γ A =>
   forall (Var54 : Con54 -> Ty54 -> Set)
     (vz  : forall Γ A, Var54 (snoc54 Γ A) A)
     (vs  : forall Γ B A, Var54 Γ A -> Var54 (snoc54 Γ B) A)
   , Var54 Γ A.

Definition vz54 {Γ A} : Var54 (snoc54 Γ A) A
 := fun Var54 vz54 vs => vz54 _ _.

Definition vs54 {Γ B A} : Var54 Γ A -> Var54 (snoc54 Γ B) A
 := fun x Var54 vz54 vs54 => vs54 _ _ _ (x Var54 vz54 vs54).

Definition Tm54 : Con54 -> Ty54 -> Set
 := fun Γ A =>
   forall (Tm54  : Con54 -> Ty54 -> Set)
     (var   : forall Γ A     , Var54 Γ A -> Tm54 Γ A)
     (lam   : forall Γ A B   , Tm54 (snoc54 Γ A) B -> Tm54 Γ (arr54 A B))
     (app   : forall Γ A B   , Tm54 Γ (arr54 A B) -> Tm54 Γ A -> Tm54 Γ B)
   , Tm54 Γ A.

Definition var54 {Γ A} : Var54 Γ A -> Tm54 Γ A
 := fun x Tm54 var54 lam app =>
     var54 _ _ x.

Definition lam54 {Γ A B} : Tm54 (snoc54 Γ A) B -> Tm54 Γ (arr54 A B)
 := fun t Tm54 var54 lam54 app =>
     lam54 _ _ _ (t Tm54 var54 lam54 app).

Definition app54 {Γ A B} : Tm54 Γ (arr54 A B) -> Tm54 Γ A -> Tm54 Γ B
 := fun t u Tm54 var54 lam54 app54 =>
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


Definition Ty55 : Set
 := forall (Ty55 : Set)
      (base   : Ty55)
      (arr : Ty55 -> Ty55 -> Ty55)
    , Ty55.

Definition base55 : Ty55 := fun _ base55 _ => base55.

Definition arr55 : Ty55 -> Ty55 -> Ty55
 := fun A B Ty55 base55 arr55 =>
     arr55 (A Ty55 base55 arr55) (B Ty55 base55 arr55).

Definition Con55 : Set
 := forall (Con55  : Set)
      (nil  : Con55)
      (snoc : Con55 -> Ty55 -> Con55)
    , Con55.

Definition nil55 : Con55
 := fun Con55 nil55 snoc => nil55.

Definition snoc55 : Con55 -> Ty55 -> Con55
 := fun Γ A Con55 nil55 snoc55 => snoc55 (Γ Con55 nil55 snoc55) A.

Definition Var55 : Con55 -> Ty55 -> Set
 := fun Γ A =>
   forall (Var55 : Con55 -> Ty55 -> Set)
     (vz  : forall Γ A, Var55 (snoc55 Γ A) A)
     (vs  : forall Γ B A, Var55 Γ A -> Var55 (snoc55 Γ B) A)
   , Var55 Γ A.

Definition vz55 {Γ A} : Var55 (snoc55 Γ A) A
 := fun Var55 vz55 vs => vz55 _ _.

Definition vs55 {Γ B A} : Var55 Γ A -> Var55 (snoc55 Γ B) A
 := fun x Var55 vz55 vs55 => vs55 _ _ _ (x Var55 vz55 vs55).

Definition Tm55 : Con55 -> Ty55 -> Set
 := fun Γ A =>
   forall (Tm55  : Con55 -> Ty55 -> Set)
     (var   : forall Γ A     , Var55 Γ A -> Tm55 Γ A)
     (lam   : forall Γ A B   , Tm55 (snoc55 Γ A) B -> Tm55 Γ (arr55 A B))
     (app   : forall Γ A B   , Tm55 Γ (arr55 A B) -> Tm55 Γ A -> Tm55 Γ B)
   , Tm55 Γ A.

Definition var55 {Γ A} : Var55 Γ A -> Tm55 Γ A
 := fun x Tm55 var55 lam app =>
     var55 _ _ x.

Definition lam55 {Γ A B} : Tm55 (snoc55 Γ A) B -> Tm55 Γ (arr55 A B)
 := fun t Tm55 var55 lam55 app =>
     lam55 _ _ _ (t Tm55 var55 lam55 app).

Definition app55 {Γ A B} : Tm55 Γ (arr55 A B) -> Tm55 Γ A -> Tm55 Γ B
 := fun t u Tm55 var55 lam55 app55 =>
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


Definition Ty56 : Set
 := forall (Ty56 : Set)
      (base   : Ty56)
      (arr : Ty56 -> Ty56 -> Ty56)
    , Ty56.

Definition base56 : Ty56 := fun _ base56 _ => base56.

Definition arr56 : Ty56 -> Ty56 -> Ty56
 := fun A B Ty56 base56 arr56 =>
     arr56 (A Ty56 base56 arr56) (B Ty56 base56 arr56).

Definition Con56 : Set
 := forall (Con56  : Set)
      (nil  : Con56)
      (snoc : Con56 -> Ty56 -> Con56)
    , Con56.

Definition nil56 : Con56
 := fun Con56 nil56 snoc => nil56.

Definition snoc56 : Con56 -> Ty56 -> Con56
 := fun Γ A Con56 nil56 snoc56 => snoc56 (Γ Con56 nil56 snoc56) A.

Definition Var56 : Con56 -> Ty56 -> Set
 := fun Γ A =>
   forall (Var56 : Con56 -> Ty56 -> Set)
     (vz  : forall Γ A, Var56 (snoc56 Γ A) A)
     (vs  : forall Γ B A, Var56 Γ A -> Var56 (snoc56 Γ B) A)
   , Var56 Γ A.

Definition vz56 {Γ A} : Var56 (snoc56 Γ A) A
 := fun Var56 vz56 vs => vz56 _ _.

Definition vs56 {Γ B A} : Var56 Γ A -> Var56 (snoc56 Γ B) A
 := fun x Var56 vz56 vs56 => vs56 _ _ _ (x Var56 vz56 vs56).

Definition Tm56 : Con56 -> Ty56 -> Set
 := fun Γ A =>
   forall (Tm56  : Con56 -> Ty56 -> Set)
     (var   : forall Γ A     , Var56 Γ A -> Tm56 Γ A)
     (lam   : forall Γ A B   , Tm56 (snoc56 Γ A) B -> Tm56 Γ (arr56 A B))
     (app   : forall Γ A B   , Tm56 Γ (arr56 A B) -> Tm56 Γ A -> Tm56 Γ B)
   , Tm56 Γ A.

Definition var56 {Γ A} : Var56 Γ A -> Tm56 Γ A
 := fun x Tm56 var56 lam app =>
     var56 _ _ x.

Definition lam56 {Γ A B} : Tm56 (snoc56 Γ A) B -> Tm56 Γ (arr56 A B)
 := fun t Tm56 var56 lam56 app =>
     lam56 _ _ _ (t Tm56 var56 lam56 app).

Definition app56 {Γ A B} : Tm56 Γ (arr56 A B) -> Tm56 Γ A -> Tm56 Γ B
 := fun t u Tm56 var56 lam56 app56 =>
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


Definition Ty57 : Set
 := forall (Ty57 : Set)
      (base   : Ty57)
      (arr : Ty57 -> Ty57 -> Ty57)
    , Ty57.

Definition base57 : Ty57 := fun _ base57 _ => base57.

Definition arr57 : Ty57 -> Ty57 -> Ty57
 := fun A B Ty57 base57 arr57 =>
     arr57 (A Ty57 base57 arr57) (B Ty57 base57 arr57).

Definition Con57 : Set
 := forall (Con57  : Set)
      (nil  : Con57)
      (snoc : Con57 -> Ty57 -> Con57)
    , Con57.

Definition nil57 : Con57
 := fun Con57 nil57 snoc => nil57.

Definition snoc57 : Con57 -> Ty57 -> Con57
 := fun Γ A Con57 nil57 snoc57 => snoc57 (Γ Con57 nil57 snoc57) A.

Definition Var57 : Con57 -> Ty57 -> Set
 := fun Γ A =>
   forall (Var57 : Con57 -> Ty57 -> Set)
     (vz  : forall Γ A, Var57 (snoc57 Γ A) A)
     (vs  : forall Γ B A, Var57 Γ A -> Var57 (snoc57 Γ B) A)
   , Var57 Γ A.

Definition vz57 {Γ A} : Var57 (snoc57 Γ A) A
 := fun Var57 vz57 vs => vz57 _ _.

Definition vs57 {Γ B A} : Var57 Γ A -> Var57 (snoc57 Γ B) A
 := fun x Var57 vz57 vs57 => vs57 _ _ _ (x Var57 vz57 vs57).

Definition Tm57 : Con57 -> Ty57 -> Set
 := fun Γ A =>
   forall (Tm57  : Con57 -> Ty57 -> Set)
     (var   : forall Γ A     , Var57 Γ A -> Tm57 Γ A)
     (lam   : forall Γ A B   , Tm57 (snoc57 Γ A) B -> Tm57 Γ (arr57 A B))
     (app   : forall Γ A B   , Tm57 Γ (arr57 A B) -> Tm57 Γ A -> Tm57 Γ B)
   , Tm57 Γ A.

Definition var57 {Γ A} : Var57 Γ A -> Tm57 Γ A
 := fun x Tm57 var57 lam app =>
     var57 _ _ x.

Definition lam57 {Γ A B} : Tm57 (snoc57 Γ A) B -> Tm57 Γ (arr57 A B)
 := fun t Tm57 var57 lam57 app =>
     lam57 _ _ _ (t Tm57 var57 lam57 app).

Definition app57 {Γ A B} : Tm57 Γ (arr57 A B) -> Tm57 Γ A -> Tm57 Γ B
 := fun t u Tm57 var57 lam57 app57 =>
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


Definition Ty58 : Set
 := forall (Ty58 : Set)
      (base   : Ty58)
      (arr : Ty58 -> Ty58 -> Ty58)
    , Ty58.

Definition base58 : Ty58 := fun _ base58 _ => base58.

Definition arr58 : Ty58 -> Ty58 -> Ty58
 := fun A B Ty58 base58 arr58 =>
     arr58 (A Ty58 base58 arr58) (B Ty58 base58 arr58).

Definition Con58 : Set
 := forall (Con58  : Set)
      (nil  : Con58)
      (snoc : Con58 -> Ty58 -> Con58)
    , Con58.

Definition nil58 : Con58
 := fun Con58 nil58 snoc => nil58.

Definition snoc58 : Con58 -> Ty58 -> Con58
 := fun Γ A Con58 nil58 snoc58 => snoc58 (Γ Con58 nil58 snoc58) A.

Definition Var58 : Con58 -> Ty58 -> Set
 := fun Γ A =>
   forall (Var58 : Con58 -> Ty58 -> Set)
     (vz  : forall Γ A, Var58 (snoc58 Γ A) A)
     (vs  : forall Γ B A, Var58 Γ A -> Var58 (snoc58 Γ B) A)
   , Var58 Γ A.

Definition vz58 {Γ A} : Var58 (snoc58 Γ A) A
 := fun Var58 vz58 vs => vz58 _ _.

Definition vs58 {Γ B A} : Var58 Γ A -> Var58 (snoc58 Γ B) A
 := fun x Var58 vz58 vs58 => vs58 _ _ _ (x Var58 vz58 vs58).

Definition Tm58 : Con58 -> Ty58 -> Set
 := fun Γ A =>
   forall (Tm58  : Con58 -> Ty58 -> Set)
     (var   : forall Γ A     , Var58 Γ A -> Tm58 Γ A)
     (lam   : forall Γ A B   , Tm58 (snoc58 Γ A) B -> Tm58 Γ (arr58 A B))
     (app   : forall Γ A B   , Tm58 Γ (arr58 A B) -> Tm58 Γ A -> Tm58 Γ B)
   , Tm58 Γ A.

Definition var58 {Γ A} : Var58 Γ A -> Tm58 Γ A
 := fun x Tm58 var58 lam app =>
     var58 _ _ x.

Definition lam58 {Γ A B} : Tm58 (snoc58 Γ A) B -> Tm58 Γ (arr58 A B)
 := fun t Tm58 var58 lam58 app =>
     lam58 _ _ _ (t Tm58 var58 lam58 app).

Definition app58 {Γ A B} : Tm58 Γ (arr58 A B) -> Tm58 Γ A -> Tm58 Γ B
 := fun t u Tm58 var58 lam58 app58 =>
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


Definition Ty59 : Set
 := forall (Ty59 : Set)
      (base   : Ty59)
      (arr : Ty59 -> Ty59 -> Ty59)
    , Ty59.

Definition base59 : Ty59 := fun _ base59 _ => base59.

Definition arr59 : Ty59 -> Ty59 -> Ty59
 := fun A B Ty59 base59 arr59 =>
     arr59 (A Ty59 base59 arr59) (B Ty59 base59 arr59).

Definition Con59 : Set
 := forall (Con59  : Set)
      (nil  : Con59)
      (snoc : Con59 -> Ty59 -> Con59)
    , Con59.

Definition nil59 : Con59
 := fun Con59 nil59 snoc => nil59.

Definition snoc59 : Con59 -> Ty59 -> Con59
 := fun Γ A Con59 nil59 snoc59 => snoc59 (Γ Con59 nil59 snoc59) A.

Definition Var59 : Con59 -> Ty59 -> Set
 := fun Γ A =>
   forall (Var59 : Con59 -> Ty59 -> Set)
     (vz  : forall Γ A, Var59 (snoc59 Γ A) A)
     (vs  : forall Γ B A, Var59 Γ A -> Var59 (snoc59 Γ B) A)
   , Var59 Γ A.

Definition vz59 {Γ A} : Var59 (snoc59 Γ A) A
 := fun Var59 vz59 vs => vz59 _ _.

Definition vs59 {Γ B A} : Var59 Γ A -> Var59 (snoc59 Γ B) A
 := fun x Var59 vz59 vs59 => vs59 _ _ _ (x Var59 vz59 vs59).

Definition Tm59 : Con59 -> Ty59 -> Set
 := fun Γ A =>
   forall (Tm59  : Con59 -> Ty59 -> Set)
     (var   : forall Γ A     , Var59 Γ A -> Tm59 Γ A)
     (lam   : forall Γ A B   , Tm59 (snoc59 Γ A) B -> Tm59 Γ (arr59 A B))
     (app   : forall Γ A B   , Tm59 Γ (arr59 A B) -> Tm59 Γ A -> Tm59 Γ B)
   , Tm59 Γ A.

Definition var59 {Γ A} : Var59 Γ A -> Tm59 Γ A
 := fun x Tm59 var59 lam app =>
     var59 _ _ x.

Definition lam59 {Γ A B} : Tm59 (snoc59 Γ A) B -> Tm59 Γ (arr59 A B)
 := fun t Tm59 var59 lam59 app =>
     lam59 _ _ _ (t Tm59 var59 lam59 app).

Definition app59 {Γ A B} : Tm59 Γ (arr59 A B) -> Tm59 Γ A -> Tm59 Γ B
 := fun t u Tm59 var59 lam59 app59 =>
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


Definition Ty60 : Set
 := forall (Ty60 : Set)
      (base   : Ty60)
      (arr : Ty60 -> Ty60 -> Ty60)
    , Ty60.

Definition base60 : Ty60 := fun _ base60 _ => base60.

Definition arr60 : Ty60 -> Ty60 -> Ty60
 := fun A B Ty60 base60 arr60 =>
     arr60 (A Ty60 base60 arr60) (B Ty60 base60 arr60).

Definition Con60 : Set
 := forall (Con60  : Set)
      (nil  : Con60)
      (snoc : Con60 -> Ty60 -> Con60)
    , Con60.

Definition nil60 : Con60
 := fun Con60 nil60 snoc => nil60.

Definition snoc60 : Con60 -> Ty60 -> Con60
 := fun Γ A Con60 nil60 snoc60 => snoc60 (Γ Con60 nil60 snoc60) A.

Definition Var60 : Con60 -> Ty60 -> Set
 := fun Γ A =>
   forall (Var60 : Con60 -> Ty60 -> Set)
     (vz  : forall Γ A, Var60 (snoc60 Γ A) A)
     (vs  : forall Γ B A, Var60 Γ A -> Var60 (snoc60 Γ B) A)
   , Var60 Γ A.

Definition vz60 {Γ A} : Var60 (snoc60 Γ A) A
 := fun Var60 vz60 vs => vz60 _ _.

Definition vs60 {Γ B A} : Var60 Γ A -> Var60 (snoc60 Γ B) A
 := fun x Var60 vz60 vs60 => vs60 _ _ _ (x Var60 vz60 vs60).

Definition Tm60 : Con60 -> Ty60 -> Set
 := fun Γ A =>
   forall (Tm60  : Con60 -> Ty60 -> Set)
     (var   : forall Γ A     , Var60 Γ A -> Tm60 Γ A)
     (lam   : forall Γ A B   , Tm60 (snoc60 Γ A) B -> Tm60 Γ (arr60 A B))
     (app   : forall Γ A B   , Tm60 Γ (arr60 A B) -> Tm60 Γ A -> Tm60 Γ B)
   , Tm60 Γ A.

Definition var60 {Γ A} : Var60 Γ A -> Tm60 Γ A
 := fun x Tm60 var60 lam app =>
     var60 _ _ x.

Definition lam60 {Γ A B} : Tm60 (snoc60 Γ A) B -> Tm60 Γ (arr60 A B)
 := fun t Tm60 var60 lam60 app =>
     lam60 _ _ _ (t Tm60 var60 lam60 app).

Definition app60 {Γ A B} : Tm60 Γ (arr60 A B) -> Tm60 Γ A -> Tm60 Γ B
 := fun t u Tm60 var60 lam60 app60 =>
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


Definition Ty61 : Set
 := forall (Ty61 : Set)
      (base   : Ty61)
      (arr : Ty61 -> Ty61 -> Ty61)
    , Ty61.

Definition base61 : Ty61 := fun _ base61 _ => base61.

Definition arr61 : Ty61 -> Ty61 -> Ty61
 := fun A B Ty61 base61 arr61 =>
     arr61 (A Ty61 base61 arr61) (B Ty61 base61 arr61).

Definition Con61 : Set
 := forall (Con61  : Set)
      (nil  : Con61)
      (snoc : Con61 -> Ty61 -> Con61)
    , Con61.

Definition nil61 : Con61
 := fun Con61 nil61 snoc => nil61.

Definition snoc61 : Con61 -> Ty61 -> Con61
 := fun Γ A Con61 nil61 snoc61 => snoc61 (Γ Con61 nil61 snoc61) A.

Definition Var61 : Con61 -> Ty61 -> Set
 := fun Γ A =>
   forall (Var61 : Con61 -> Ty61 -> Set)
     (vz  : forall Γ A, Var61 (snoc61 Γ A) A)
     (vs  : forall Γ B A, Var61 Γ A -> Var61 (snoc61 Γ B) A)
   , Var61 Γ A.

Definition vz61 {Γ A} : Var61 (snoc61 Γ A) A
 := fun Var61 vz61 vs => vz61 _ _.

Definition vs61 {Γ B A} : Var61 Γ A -> Var61 (snoc61 Γ B) A
 := fun x Var61 vz61 vs61 => vs61 _ _ _ (x Var61 vz61 vs61).

Definition Tm61 : Con61 -> Ty61 -> Set
 := fun Γ A =>
   forall (Tm61  : Con61 -> Ty61 -> Set)
     (var   : forall Γ A     , Var61 Γ A -> Tm61 Γ A)
     (lam   : forall Γ A B   , Tm61 (snoc61 Γ A) B -> Tm61 Γ (arr61 A B))
     (app   : forall Γ A B   , Tm61 Γ (arr61 A B) -> Tm61 Γ A -> Tm61 Γ B)
   , Tm61 Γ A.

Definition var61 {Γ A} : Var61 Γ A -> Tm61 Γ A
 := fun x Tm61 var61 lam app =>
     var61 _ _ x.

Definition lam61 {Γ A B} : Tm61 (snoc61 Γ A) B -> Tm61 Γ (arr61 A B)
 := fun t Tm61 var61 lam61 app =>
     lam61 _ _ _ (t Tm61 var61 lam61 app).

Definition app61 {Γ A B} : Tm61 Γ (arr61 A B) -> Tm61 Γ A -> Tm61 Γ B
 := fun t u Tm61 var61 lam61 app61 =>
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


Definition Ty62 : Set
 := forall (Ty62 : Set)
      (base   : Ty62)
      (arr : Ty62 -> Ty62 -> Ty62)
    , Ty62.

Definition base62 : Ty62 := fun _ base62 _ => base62.

Definition arr62 : Ty62 -> Ty62 -> Ty62
 := fun A B Ty62 base62 arr62 =>
     arr62 (A Ty62 base62 arr62) (B Ty62 base62 arr62).

Definition Con62 : Set
 := forall (Con62  : Set)
      (nil  : Con62)
      (snoc : Con62 -> Ty62 -> Con62)
    , Con62.

Definition nil62 : Con62
 := fun Con62 nil62 snoc => nil62.

Definition snoc62 : Con62 -> Ty62 -> Con62
 := fun Γ A Con62 nil62 snoc62 => snoc62 (Γ Con62 nil62 snoc62) A.

Definition Var62 : Con62 -> Ty62 -> Set
 := fun Γ A =>
   forall (Var62 : Con62 -> Ty62 -> Set)
     (vz  : forall Γ A, Var62 (snoc62 Γ A) A)
     (vs  : forall Γ B A, Var62 Γ A -> Var62 (snoc62 Γ B) A)
   , Var62 Γ A.

Definition vz62 {Γ A} : Var62 (snoc62 Γ A) A
 := fun Var62 vz62 vs => vz62 _ _.

Definition vs62 {Γ B A} : Var62 Γ A -> Var62 (snoc62 Γ B) A
 := fun x Var62 vz62 vs62 => vs62 _ _ _ (x Var62 vz62 vs62).

Definition Tm62 : Con62 -> Ty62 -> Set
 := fun Γ A =>
   forall (Tm62  : Con62 -> Ty62 -> Set)
     (var   : forall Γ A     , Var62 Γ A -> Tm62 Γ A)
     (lam   : forall Γ A B   , Tm62 (snoc62 Γ A) B -> Tm62 Γ (arr62 A B))
     (app   : forall Γ A B   , Tm62 Γ (arr62 A B) -> Tm62 Γ A -> Tm62 Γ B)
   , Tm62 Γ A.

Definition var62 {Γ A} : Var62 Γ A -> Tm62 Γ A
 := fun x Tm62 var62 lam app =>
     var62 _ _ x.

Definition lam62 {Γ A B} : Tm62 (snoc62 Γ A) B -> Tm62 Γ (arr62 A B)
 := fun t Tm62 var62 lam62 app =>
     lam62 _ _ _ (t Tm62 var62 lam62 app).

Definition app62 {Γ A B} : Tm62 Γ (arr62 A B) -> Tm62 Γ A -> Tm62 Γ B
 := fun t u Tm62 var62 lam62 app62 =>
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


Definition Ty63 : Set
 := forall (Ty63 : Set)
      (base   : Ty63)
      (arr : Ty63 -> Ty63 -> Ty63)
    , Ty63.

Definition base63 : Ty63 := fun _ base63 _ => base63.

Definition arr63 : Ty63 -> Ty63 -> Ty63
 := fun A B Ty63 base63 arr63 =>
     arr63 (A Ty63 base63 arr63) (B Ty63 base63 arr63).

Definition Con63 : Set
 := forall (Con63  : Set)
      (nil  : Con63)
      (snoc : Con63 -> Ty63 -> Con63)
    , Con63.

Definition nil63 : Con63
 := fun Con63 nil63 snoc => nil63.

Definition snoc63 : Con63 -> Ty63 -> Con63
 := fun Γ A Con63 nil63 snoc63 => snoc63 (Γ Con63 nil63 snoc63) A.

Definition Var63 : Con63 -> Ty63 -> Set
 := fun Γ A =>
   forall (Var63 : Con63 -> Ty63 -> Set)
     (vz  : forall Γ A, Var63 (snoc63 Γ A) A)
     (vs  : forall Γ B A, Var63 Γ A -> Var63 (snoc63 Γ B) A)
   , Var63 Γ A.

Definition vz63 {Γ A} : Var63 (snoc63 Γ A) A
 := fun Var63 vz63 vs => vz63 _ _.

Definition vs63 {Γ B A} : Var63 Γ A -> Var63 (snoc63 Γ B) A
 := fun x Var63 vz63 vs63 => vs63 _ _ _ (x Var63 vz63 vs63).

Definition Tm63 : Con63 -> Ty63 -> Set
 := fun Γ A =>
   forall (Tm63  : Con63 -> Ty63 -> Set)
     (var   : forall Γ A     , Var63 Γ A -> Tm63 Γ A)
     (lam   : forall Γ A B   , Tm63 (snoc63 Γ A) B -> Tm63 Γ (arr63 A B))
     (app   : forall Γ A B   , Tm63 Γ (arr63 A B) -> Tm63 Γ A -> Tm63 Γ B)
   , Tm63 Γ A.

Definition var63 {Γ A} : Var63 Γ A -> Tm63 Γ A
 := fun x Tm63 var63 lam app =>
     var63 _ _ x.

Definition lam63 {Γ A B} : Tm63 (snoc63 Γ A) B -> Tm63 Γ (arr63 A B)
 := fun t Tm63 var63 lam63 app =>
     lam63 _ _ _ (t Tm63 var63 lam63 app).

Definition app63 {Γ A B} : Tm63 Γ (arr63 A B) -> Tm63 Γ A -> Tm63 Γ B
 := fun t u Tm63 var63 lam63 app63 =>
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


Definition Ty64 : Set
 := forall (Ty64 : Set)
      (base   : Ty64)
      (arr : Ty64 -> Ty64 -> Ty64)
    , Ty64.

Definition base64 : Ty64 := fun _ base64 _ => base64.

Definition arr64 : Ty64 -> Ty64 -> Ty64
 := fun A B Ty64 base64 arr64 =>
     arr64 (A Ty64 base64 arr64) (B Ty64 base64 arr64).

Definition Con64 : Set
 := forall (Con64  : Set)
      (nil  : Con64)
      (snoc : Con64 -> Ty64 -> Con64)
    , Con64.

Definition nil64 : Con64
 := fun Con64 nil64 snoc => nil64.

Definition snoc64 : Con64 -> Ty64 -> Con64
 := fun Γ A Con64 nil64 snoc64 => snoc64 (Γ Con64 nil64 snoc64) A.

Definition Var64 : Con64 -> Ty64 -> Set
 := fun Γ A =>
   forall (Var64 : Con64 -> Ty64 -> Set)
     (vz  : forall Γ A, Var64 (snoc64 Γ A) A)
     (vs  : forall Γ B A, Var64 Γ A -> Var64 (snoc64 Γ B) A)
   , Var64 Γ A.

Definition vz64 {Γ A} : Var64 (snoc64 Γ A) A
 := fun Var64 vz64 vs => vz64 _ _.

Definition vs64 {Γ B A} : Var64 Γ A -> Var64 (snoc64 Γ B) A
 := fun x Var64 vz64 vs64 => vs64 _ _ _ (x Var64 vz64 vs64).

Definition Tm64 : Con64 -> Ty64 -> Set
 := fun Γ A =>
   forall (Tm64  : Con64 -> Ty64 -> Set)
     (var   : forall Γ A     , Var64 Γ A -> Tm64 Γ A)
     (lam   : forall Γ A B   , Tm64 (snoc64 Γ A) B -> Tm64 Γ (arr64 A B))
     (app   : forall Γ A B   , Tm64 Γ (arr64 A B) -> Tm64 Γ A -> Tm64 Γ B)
   , Tm64 Γ A.

Definition var64 {Γ A} : Var64 Γ A -> Tm64 Γ A
 := fun x Tm64 var64 lam app =>
     var64 _ _ x.

Definition lam64 {Γ A B} : Tm64 (snoc64 Γ A) B -> Tm64 Γ (arr64 A B)
 := fun t Tm64 var64 lam64 app =>
     lam64 _ _ _ (t Tm64 var64 lam64 app).

Definition app64 {Γ A B} : Tm64 Γ (arr64 A B) -> Tm64 Γ A -> Tm64 Γ B
 := fun t u Tm64 var64 lam64 app64 =>
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


Definition Ty65 : Set
 := forall (Ty65 : Set)
      (base   : Ty65)
      (arr : Ty65 -> Ty65 -> Ty65)
    , Ty65.

Definition base65 : Ty65 := fun _ base65 _ => base65.

Definition arr65 : Ty65 -> Ty65 -> Ty65
 := fun A B Ty65 base65 arr65 =>
     arr65 (A Ty65 base65 arr65) (B Ty65 base65 arr65).

Definition Con65 : Set
 := forall (Con65  : Set)
      (nil  : Con65)
      (snoc : Con65 -> Ty65 -> Con65)
    , Con65.

Definition nil65 : Con65
 := fun Con65 nil65 snoc => nil65.

Definition snoc65 : Con65 -> Ty65 -> Con65
 := fun Γ A Con65 nil65 snoc65 => snoc65 (Γ Con65 nil65 snoc65) A.

Definition Var65 : Con65 -> Ty65 -> Set
 := fun Γ A =>
   forall (Var65 : Con65 -> Ty65 -> Set)
     (vz  : forall Γ A, Var65 (snoc65 Γ A) A)
     (vs  : forall Γ B A, Var65 Γ A -> Var65 (snoc65 Γ B) A)
   , Var65 Γ A.

Definition vz65 {Γ A} : Var65 (snoc65 Γ A) A
 := fun Var65 vz65 vs => vz65 _ _.

Definition vs65 {Γ B A} : Var65 Γ A -> Var65 (snoc65 Γ B) A
 := fun x Var65 vz65 vs65 => vs65 _ _ _ (x Var65 vz65 vs65).

Definition Tm65 : Con65 -> Ty65 -> Set
 := fun Γ A =>
   forall (Tm65  : Con65 -> Ty65 -> Set)
     (var   : forall Γ A     , Var65 Γ A -> Tm65 Γ A)
     (lam   : forall Γ A B   , Tm65 (snoc65 Γ A) B -> Tm65 Γ (arr65 A B))
     (app   : forall Γ A B   , Tm65 Γ (arr65 A B) -> Tm65 Γ A -> Tm65 Γ B)
   , Tm65 Γ A.

Definition var65 {Γ A} : Var65 Γ A -> Tm65 Γ A
 := fun x Tm65 var65 lam app =>
     var65 _ _ x.

Definition lam65 {Γ A B} : Tm65 (snoc65 Γ A) B -> Tm65 Γ (arr65 A B)
 := fun t Tm65 var65 lam65 app =>
     lam65 _ _ _ (t Tm65 var65 lam65 app).

Definition app65 {Γ A B} : Tm65 Γ (arr65 A B) -> Tm65 Γ A -> Tm65 Γ B
 := fun t u Tm65 var65 lam65 app65 =>
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


Definition Ty66 : Set
 := forall (Ty66 : Set)
      (base   : Ty66)
      (arr : Ty66 -> Ty66 -> Ty66)
    , Ty66.

Definition base66 : Ty66 := fun _ base66 _ => base66.

Definition arr66 : Ty66 -> Ty66 -> Ty66
 := fun A B Ty66 base66 arr66 =>
     arr66 (A Ty66 base66 arr66) (B Ty66 base66 arr66).

Definition Con66 : Set
 := forall (Con66  : Set)
      (nil  : Con66)
      (snoc : Con66 -> Ty66 -> Con66)
    , Con66.

Definition nil66 : Con66
 := fun Con66 nil66 snoc => nil66.

Definition snoc66 : Con66 -> Ty66 -> Con66
 := fun Γ A Con66 nil66 snoc66 => snoc66 (Γ Con66 nil66 snoc66) A.

Definition Var66 : Con66 -> Ty66 -> Set
 := fun Γ A =>
   forall (Var66 : Con66 -> Ty66 -> Set)
     (vz  : forall Γ A, Var66 (snoc66 Γ A) A)
     (vs  : forall Γ B A, Var66 Γ A -> Var66 (snoc66 Γ B) A)
   , Var66 Γ A.

Definition vz66 {Γ A} : Var66 (snoc66 Γ A) A
 := fun Var66 vz66 vs => vz66 _ _.

Definition vs66 {Γ B A} : Var66 Γ A -> Var66 (snoc66 Γ B) A
 := fun x Var66 vz66 vs66 => vs66 _ _ _ (x Var66 vz66 vs66).

Definition Tm66 : Con66 -> Ty66 -> Set
 := fun Γ A =>
   forall (Tm66  : Con66 -> Ty66 -> Set)
     (var   : forall Γ A     , Var66 Γ A -> Tm66 Γ A)
     (lam   : forall Γ A B   , Tm66 (snoc66 Γ A) B -> Tm66 Γ (arr66 A B))
     (app   : forall Γ A B   , Tm66 Γ (arr66 A B) -> Tm66 Γ A -> Tm66 Γ B)
   , Tm66 Γ A.

Definition var66 {Γ A} : Var66 Γ A -> Tm66 Γ A
 := fun x Tm66 var66 lam app =>
     var66 _ _ x.

Definition lam66 {Γ A B} : Tm66 (snoc66 Γ A) B -> Tm66 Γ (arr66 A B)
 := fun t Tm66 var66 lam66 app =>
     lam66 _ _ _ (t Tm66 var66 lam66 app).

Definition app66 {Γ A B} : Tm66 Γ (arr66 A B) -> Tm66 Γ A -> Tm66 Γ B
 := fun t u Tm66 var66 lam66 app66 =>
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


Definition Ty67 : Set
 := forall (Ty67 : Set)
      (base   : Ty67)
      (arr : Ty67 -> Ty67 -> Ty67)
    , Ty67.

Definition base67 : Ty67 := fun _ base67 _ => base67.

Definition arr67 : Ty67 -> Ty67 -> Ty67
 := fun A B Ty67 base67 arr67 =>
     arr67 (A Ty67 base67 arr67) (B Ty67 base67 arr67).

Definition Con67 : Set
 := forall (Con67  : Set)
      (nil  : Con67)
      (snoc : Con67 -> Ty67 -> Con67)
    , Con67.

Definition nil67 : Con67
 := fun Con67 nil67 snoc => nil67.

Definition snoc67 : Con67 -> Ty67 -> Con67
 := fun Γ A Con67 nil67 snoc67 => snoc67 (Γ Con67 nil67 snoc67) A.

Definition Var67 : Con67 -> Ty67 -> Set
 := fun Γ A =>
   forall (Var67 : Con67 -> Ty67 -> Set)
     (vz  : forall Γ A, Var67 (snoc67 Γ A) A)
     (vs  : forall Γ B A, Var67 Γ A -> Var67 (snoc67 Γ B) A)
   , Var67 Γ A.

Definition vz67 {Γ A} : Var67 (snoc67 Γ A) A
 := fun Var67 vz67 vs => vz67 _ _.

Definition vs67 {Γ B A} : Var67 Γ A -> Var67 (snoc67 Γ B) A
 := fun x Var67 vz67 vs67 => vs67 _ _ _ (x Var67 vz67 vs67).

Definition Tm67 : Con67 -> Ty67 -> Set
 := fun Γ A =>
   forall (Tm67  : Con67 -> Ty67 -> Set)
     (var   : forall Γ A     , Var67 Γ A -> Tm67 Γ A)
     (lam   : forall Γ A B   , Tm67 (snoc67 Γ A) B -> Tm67 Γ (arr67 A B))
     (app   : forall Γ A B   , Tm67 Γ (arr67 A B) -> Tm67 Γ A -> Tm67 Γ B)
   , Tm67 Γ A.

Definition var67 {Γ A} : Var67 Γ A -> Tm67 Γ A
 := fun x Tm67 var67 lam app =>
     var67 _ _ x.

Definition lam67 {Γ A B} : Tm67 (snoc67 Γ A) B -> Tm67 Γ (arr67 A B)
 := fun t Tm67 var67 lam67 app =>
     lam67 _ _ _ (t Tm67 var67 lam67 app).

Definition app67 {Γ A B} : Tm67 Γ (arr67 A B) -> Tm67 Γ A -> Tm67 Γ B
 := fun t u Tm67 var67 lam67 app67 =>
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


Definition Ty68 : Set
 := forall (Ty68 : Set)
      (base   : Ty68)
      (arr : Ty68 -> Ty68 -> Ty68)
    , Ty68.

Definition base68 : Ty68 := fun _ base68 _ => base68.

Definition arr68 : Ty68 -> Ty68 -> Ty68
 := fun A B Ty68 base68 arr68 =>
     arr68 (A Ty68 base68 arr68) (B Ty68 base68 arr68).

Definition Con68 : Set
 := forall (Con68  : Set)
      (nil  : Con68)
      (snoc : Con68 -> Ty68 -> Con68)
    , Con68.

Definition nil68 : Con68
 := fun Con68 nil68 snoc => nil68.

Definition snoc68 : Con68 -> Ty68 -> Con68
 := fun Γ A Con68 nil68 snoc68 => snoc68 (Γ Con68 nil68 snoc68) A.

Definition Var68 : Con68 -> Ty68 -> Set
 := fun Γ A =>
   forall (Var68 : Con68 -> Ty68 -> Set)
     (vz  : forall Γ A, Var68 (snoc68 Γ A) A)
     (vs  : forall Γ B A, Var68 Γ A -> Var68 (snoc68 Γ B) A)
   , Var68 Γ A.

Definition vz68 {Γ A} : Var68 (snoc68 Γ A) A
 := fun Var68 vz68 vs => vz68 _ _.

Definition vs68 {Γ B A} : Var68 Γ A -> Var68 (snoc68 Γ B) A
 := fun x Var68 vz68 vs68 => vs68 _ _ _ (x Var68 vz68 vs68).

Definition Tm68 : Con68 -> Ty68 -> Set
 := fun Γ A =>
   forall (Tm68  : Con68 -> Ty68 -> Set)
     (var   : forall Γ A     , Var68 Γ A -> Tm68 Γ A)
     (lam   : forall Γ A B   , Tm68 (snoc68 Γ A) B -> Tm68 Γ (arr68 A B))
     (app   : forall Γ A B   , Tm68 Γ (arr68 A B) -> Tm68 Γ A -> Tm68 Γ B)
   , Tm68 Γ A.

Definition var68 {Γ A} : Var68 Γ A -> Tm68 Γ A
 := fun x Tm68 var68 lam app =>
     var68 _ _ x.

Definition lam68 {Γ A B} : Tm68 (snoc68 Γ A) B -> Tm68 Γ (arr68 A B)
 := fun t Tm68 var68 lam68 app =>
     lam68 _ _ _ (t Tm68 var68 lam68 app).

Definition app68 {Γ A B} : Tm68 Γ (arr68 A B) -> Tm68 Γ A -> Tm68 Γ B
 := fun t u Tm68 var68 lam68 app68 =>
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


Definition Ty69 : Set
 := forall (Ty69 : Set)
      (base   : Ty69)
      (arr : Ty69 -> Ty69 -> Ty69)
    , Ty69.

Definition base69 : Ty69 := fun _ base69 _ => base69.

Definition arr69 : Ty69 -> Ty69 -> Ty69
 := fun A B Ty69 base69 arr69 =>
     arr69 (A Ty69 base69 arr69) (B Ty69 base69 arr69).

Definition Con69 : Set
 := forall (Con69  : Set)
      (nil  : Con69)
      (snoc : Con69 -> Ty69 -> Con69)
    , Con69.

Definition nil69 : Con69
 := fun Con69 nil69 snoc => nil69.

Definition snoc69 : Con69 -> Ty69 -> Con69
 := fun Γ A Con69 nil69 snoc69 => snoc69 (Γ Con69 nil69 snoc69) A.

Definition Var69 : Con69 -> Ty69 -> Set
 := fun Γ A =>
   forall (Var69 : Con69 -> Ty69 -> Set)
     (vz  : forall Γ A, Var69 (snoc69 Γ A) A)
     (vs  : forall Γ B A, Var69 Γ A -> Var69 (snoc69 Γ B) A)
   , Var69 Γ A.

Definition vz69 {Γ A} : Var69 (snoc69 Γ A) A
 := fun Var69 vz69 vs => vz69 _ _.

Definition vs69 {Γ B A} : Var69 Γ A -> Var69 (snoc69 Γ B) A
 := fun x Var69 vz69 vs69 => vs69 _ _ _ (x Var69 vz69 vs69).

Definition Tm69 : Con69 -> Ty69 -> Set
 := fun Γ A =>
   forall (Tm69  : Con69 -> Ty69 -> Set)
     (var   : forall Γ A     , Var69 Γ A -> Tm69 Γ A)
     (lam   : forall Γ A B   , Tm69 (snoc69 Γ A) B -> Tm69 Γ (arr69 A B))
     (app   : forall Γ A B   , Tm69 Γ (arr69 A B) -> Tm69 Γ A -> Tm69 Γ B)
   , Tm69 Γ A.

Definition var69 {Γ A} : Var69 Γ A -> Tm69 Γ A
 := fun x Tm69 var69 lam app =>
     var69 _ _ x.

Definition lam69 {Γ A B} : Tm69 (snoc69 Γ A) B -> Tm69 Γ (arr69 A B)
 := fun t Tm69 var69 lam69 app =>
     lam69 _ _ _ (t Tm69 var69 lam69 app).

Definition app69 {Γ A B} : Tm69 Γ (arr69 A B) -> Tm69 Γ A -> Tm69 Γ B
 := fun t u Tm69 var69 lam69 app69 =>
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


Definition Ty70 : Set
 := forall (Ty70 : Set)
      (base   : Ty70)
      (arr : Ty70 -> Ty70 -> Ty70)
    , Ty70.

Definition base70 : Ty70 := fun _ base70 _ => base70.

Definition arr70 : Ty70 -> Ty70 -> Ty70
 := fun A B Ty70 base70 arr70 =>
     arr70 (A Ty70 base70 arr70) (B Ty70 base70 arr70).

Definition Con70 : Set
 := forall (Con70  : Set)
      (nil  : Con70)
      (snoc : Con70 -> Ty70 -> Con70)
    , Con70.

Definition nil70 : Con70
 := fun Con70 nil70 snoc => nil70.

Definition snoc70 : Con70 -> Ty70 -> Con70
 := fun Γ A Con70 nil70 snoc70 => snoc70 (Γ Con70 nil70 snoc70) A.

Definition Var70 : Con70 -> Ty70 -> Set
 := fun Γ A =>
   forall (Var70 : Con70 -> Ty70 -> Set)
     (vz  : forall Γ A, Var70 (snoc70 Γ A) A)
     (vs  : forall Γ B A, Var70 Γ A -> Var70 (snoc70 Γ B) A)
   , Var70 Γ A.

Definition vz70 {Γ A} : Var70 (snoc70 Γ A) A
 := fun Var70 vz70 vs => vz70 _ _.

Definition vs70 {Γ B A} : Var70 Γ A -> Var70 (snoc70 Γ B) A
 := fun x Var70 vz70 vs70 => vs70 _ _ _ (x Var70 vz70 vs70).

Definition Tm70 : Con70 -> Ty70 -> Set
 := fun Γ A =>
   forall (Tm70  : Con70 -> Ty70 -> Set)
     (var   : forall Γ A     , Var70 Γ A -> Tm70 Γ A)
     (lam   : forall Γ A B   , Tm70 (snoc70 Γ A) B -> Tm70 Γ (arr70 A B))
     (app   : forall Γ A B   , Tm70 Γ (arr70 A B) -> Tm70 Γ A -> Tm70 Γ B)
   , Tm70 Γ A.

Definition var70 {Γ A} : Var70 Γ A -> Tm70 Γ A
 := fun x Tm70 var70 lam app =>
     var70 _ _ x.

Definition lam70 {Γ A B} : Tm70 (snoc70 Γ A) B -> Tm70 Γ (arr70 A B)
 := fun t Tm70 var70 lam70 app =>
     lam70 _ _ _ (t Tm70 var70 lam70 app).

Definition app70 {Γ A B} : Tm70 Γ (arr70 A B) -> Tm70 Γ A -> Tm70 Γ B
 := fun t u Tm70 var70 lam70 app70 =>
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


Definition Ty71 : Set
 := forall (Ty71 : Set)
      (base   : Ty71)
      (arr : Ty71 -> Ty71 -> Ty71)
    , Ty71.

Definition base71 : Ty71 := fun _ base71 _ => base71.

Definition arr71 : Ty71 -> Ty71 -> Ty71
 := fun A B Ty71 base71 arr71 =>
     arr71 (A Ty71 base71 arr71) (B Ty71 base71 arr71).

Definition Con71 : Set
 := forall (Con71  : Set)
      (nil  : Con71)
      (snoc : Con71 -> Ty71 -> Con71)
    , Con71.

Definition nil71 : Con71
 := fun Con71 nil71 snoc => nil71.

Definition snoc71 : Con71 -> Ty71 -> Con71
 := fun Γ A Con71 nil71 snoc71 => snoc71 (Γ Con71 nil71 snoc71) A.

Definition Var71 : Con71 -> Ty71 -> Set
 := fun Γ A =>
   forall (Var71 : Con71 -> Ty71 -> Set)
     (vz  : forall Γ A, Var71 (snoc71 Γ A) A)
     (vs  : forall Γ B A, Var71 Γ A -> Var71 (snoc71 Γ B) A)
   , Var71 Γ A.

Definition vz71 {Γ A} : Var71 (snoc71 Γ A) A
 := fun Var71 vz71 vs => vz71 _ _.

Definition vs71 {Γ B A} : Var71 Γ A -> Var71 (snoc71 Γ B) A
 := fun x Var71 vz71 vs71 => vs71 _ _ _ (x Var71 vz71 vs71).

Definition Tm71 : Con71 -> Ty71 -> Set
 := fun Γ A =>
   forall (Tm71  : Con71 -> Ty71 -> Set)
     (var   : forall Γ A     , Var71 Γ A -> Tm71 Γ A)
     (lam   : forall Γ A B   , Tm71 (snoc71 Γ A) B -> Tm71 Γ (arr71 A B))
     (app   : forall Γ A B   , Tm71 Γ (arr71 A B) -> Tm71 Γ A -> Tm71 Γ B)
   , Tm71 Γ A.

Definition var71 {Γ A} : Var71 Γ A -> Tm71 Γ A
 := fun x Tm71 var71 lam app =>
     var71 _ _ x.

Definition lam71 {Γ A B} : Tm71 (snoc71 Γ A) B -> Tm71 Γ (arr71 A B)
 := fun t Tm71 var71 lam71 app =>
     lam71 _ _ _ (t Tm71 var71 lam71 app).

Definition app71 {Γ A B} : Tm71 Γ (arr71 A B) -> Tm71 Γ A -> Tm71 Γ B
 := fun t u Tm71 var71 lam71 app71 =>
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


Definition Ty72 : Set
 := forall (Ty72 : Set)
      (base   : Ty72)
      (arr : Ty72 -> Ty72 -> Ty72)
    , Ty72.

Definition base72 : Ty72 := fun _ base72 _ => base72.

Definition arr72 : Ty72 -> Ty72 -> Ty72
 := fun A B Ty72 base72 arr72 =>
     arr72 (A Ty72 base72 arr72) (B Ty72 base72 arr72).

Definition Con72 : Set
 := forall (Con72  : Set)
      (nil  : Con72)
      (snoc : Con72 -> Ty72 -> Con72)
    , Con72.

Definition nil72 : Con72
 := fun Con72 nil72 snoc => nil72.

Definition snoc72 : Con72 -> Ty72 -> Con72
 := fun Γ A Con72 nil72 snoc72 => snoc72 (Γ Con72 nil72 snoc72) A.

Definition Var72 : Con72 -> Ty72 -> Set
 := fun Γ A =>
   forall (Var72 : Con72 -> Ty72 -> Set)
     (vz  : forall Γ A, Var72 (snoc72 Γ A) A)
     (vs  : forall Γ B A, Var72 Γ A -> Var72 (snoc72 Γ B) A)
   , Var72 Γ A.

Definition vz72 {Γ A} : Var72 (snoc72 Γ A) A
 := fun Var72 vz72 vs => vz72 _ _.

Definition vs72 {Γ B A} : Var72 Γ A -> Var72 (snoc72 Γ B) A
 := fun x Var72 vz72 vs72 => vs72 _ _ _ (x Var72 vz72 vs72).

Definition Tm72 : Con72 -> Ty72 -> Set
 := fun Γ A =>
   forall (Tm72  : Con72 -> Ty72 -> Set)
     (var   : forall Γ A     , Var72 Γ A -> Tm72 Γ A)
     (lam   : forall Γ A B   , Tm72 (snoc72 Γ A) B -> Tm72 Γ (arr72 A B))
     (app   : forall Γ A B   , Tm72 Γ (arr72 A B) -> Tm72 Γ A -> Tm72 Γ B)
   , Tm72 Γ A.

Definition var72 {Γ A} : Var72 Γ A -> Tm72 Γ A
 := fun x Tm72 var72 lam app =>
     var72 _ _ x.

Definition lam72 {Γ A B} : Tm72 (snoc72 Γ A) B -> Tm72 Γ (arr72 A B)
 := fun t Tm72 var72 lam72 app =>
     lam72 _ _ _ (t Tm72 var72 lam72 app).

Definition app72 {Γ A B} : Tm72 Γ (arr72 A B) -> Tm72 Γ A -> Tm72 Γ B
 := fun t u Tm72 var72 lam72 app72 =>
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


Definition Ty73 : Set
 := forall (Ty73 : Set)
      (base   : Ty73)
      (arr : Ty73 -> Ty73 -> Ty73)
    , Ty73.

Definition base73 : Ty73 := fun _ base73 _ => base73.

Definition arr73 : Ty73 -> Ty73 -> Ty73
 := fun A B Ty73 base73 arr73 =>
     arr73 (A Ty73 base73 arr73) (B Ty73 base73 arr73).

Definition Con73 : Set
 := forall (Con73  : Set)
      (nil  : Con73)
      (snoc : Con73 -> Ty73 -> Con73)
    , Con73.

Definition nil73 : Con73
 := fun Con73 nil73 snoc => nil73.

Definition snoc73 : Con73 -> Ty73 -> Con73
 := fun Γ A Con73 nil73 snoc73 => snoc73 (Γ Con73 nil73 snoc73) A.

Definition Var73 : Con73 -> Ty73 -> Set
 := fun Γ A =>
   forall (Var73 : Con73 -> Ty73 -> Set)
     (vz  : forall Γ A, Var73 (snoc73 Γ A) A)
     (vs  : forall Γ B A, Var73 Γ A -> Var73 (snoc73 Γ B) A)
   , Var73 Γ A.

Definition vz73 {Γ A} : Var73 (snoc73 Γ A) A
 := fun Var73 vz73 vs => vz73 _ _.

Definition vs73 {Γ B A} : Var73 Γ A -> Var73 (snoc73 Γ B) A
 := fun x Var73 vz73 vs73 => vs73 _ _ _ (x Var73 vz73 vs73).

Definition Tm73 : Con73 -> Ty73 -> Set
 := fun Γ A =>
   forall (Tm73  : Con73 -> Ty73 -> Set)
     (var   : forall Γ A     , Var73 Γ A -> Tm73 Γ A)
     (lam   : forall Γ A B   , Tm73 (snoc73 Γ A) B -> Tm73 Γ (arr73 A B))
     (app   : forall Γ A B   , Tm73 Γ (arr73 A B) -> Tm73 Γ A -> Tm73 Γ B)
   , Tm73 Γ A.

Definition var73 {Γ A} : Var73 Γ A -> Tm73 Γ A
 := fun x Tm73 var73 lam app =>
     var73 _ _ x.

Definition lam73 {Γ A B} : Tm73 (snoc73 Γ A) B -> Tm73 Γ (arr73 A B)
 := fun t Tm73 var73 lam73 app =>
     lam73 _ _ _ (t Tm73 var73 lam73 app).

Definition app73 {Γ A B} : Tm73 Γ (arr73 A B) -> Tm73 Γ A -> Tm73 Γ B
 := fun t u Tm73 var73 lam73 app73 =>
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


Definition Ty74 : Set
 := forall (Ty74 : Set)
      (base   : Ty74)
      (arr : Ty74 -> Ty74 -> Ty74)
    , Ty74.

Definition base74 : Ty74 := fun _ base74 _ => base74.

Definition arr74 : Ty74 -> Ty74 -> Ty74
 := fun A B Ty74 base74 arr74 =>
     arr74 (A Ty74 base74 arr74) (B Ty74 base74 arr74).

Definition Con74 : Set
 := forall (Con74  : Set)
      (nil  : Con74)
      (snoc : Con74 -> Ty74 -> Con74)
    , Con74.

Definition nil74 : Con74
 := fun Con74 nil74 snoc => nil74.

Definition snoc74 : Con74 -> Ty74 -> Con74
 := fun Γ A Con74 nil74 snoc74 => snoc74 (Γ Con74 nil74 snoc74) A.

Definition Var74 : Con74 -> Ty74 -> Set
 := fun Γ A =>
   forall (Var74 : Con74 -> Ty74 -> Set)
     (vz  : forall Γ A, Var74 (snoc74 Γ A) A)
     (vs  : forall Γ B A, Var74 Γ A -> Var74 (snoc74 Γ B) A)
   , Var74 Γ A.

Definition vz74 {Γ A} : Var74 (snoc74 Γ A) A
 := fun Var74 vz74 vs => vz74 _ _.

Definition vs74 {Γ B A} : Var74 Γ A -> Var74 (snoc74 Γ B) A
 := fun x Var74 vz74 vs74 => vs74 _ _ _ (x Var74 vz74 vs74).

Definition Tm74 : Con74 -> Ty74 -> Set
 := fun Γ A =>
   forall (Tm74  : Con74 -> Ty74 -> Set)
     (var   : forall Γ A     , Var74 Γ A -> Tm74 Γ A)
     (lam   : forall Γ A B   , Tm74 (snoc74 Γ A) B -> Tm74 Γ (arr74 A B))
     (app   : forall Γ A B   , Tm74 Γ (arr74 A B) -> Tm74 Γ A -> Tm74 Γ B)
   , Tm74 Γ A.

Definition var74 {Γ A} : Var74 Γ A -> Tm74 Γ A
 := fun x Tm74 var74 lam app =>
     var74 _ _ x.

Definition lam74 {Γ A B} : Tm74 (snoc74 Γ A) B -> Tm74 Γ (arr74 A B)
 := fun t Tm74 var74 lam74 app =>
     lam74 _ _ _ (t Tm74 var74 lam74 app).

Definition app74 {Γ A B} : Tm74 Γ (arr74 A B) -> Tm74 Γ A -> Tm74 Γ B
 := fun t u Tm74 var74 lam74 app74 =>
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


Definition Ty75 : Set
 := forall (Ty75 : Set)
      (base   : Ty75)
      (arr : Ty75 -> Ty75 -> Ty75)
    , Ty75.

Definition base75 : Ty75 := fun _ base75 _ => base75.

Definition arr75 : Ty75 -> Ty75 -> Ty75
 := fun A B Ty75 base75 arr75 =>
     arr75 (A Ty75 base75 arr75) (B Ty75 base75 arr75).

Definition Con75 : Set
 := forall (Con75  : Set)
      (nil  : Con75)
      (snoc : Con75 -> Ty75 -> Con75)
    , Con75.

Definition nil75 : Con75
 := fun Con75 nil75 snoc => nil75.

Definition snoc75 : Con75 -> Ty75 -> Con75
 := fun Γ A Con75 nil75 snoc75 => snoc75 (Γ Con75 nil75 snoc75) A.

Definition Var75 : Con75 -> Ty75 -> Set
 := fun Γ A =>
   forall (Var75 : Con75 -> Ty75 -> Set)
     (vz  : forall Γ A, Var75 (snoc75 Γ A) A)
     (vs  : forall Γ B A, Var75 Γ A -> Var75 (snoc75 Γ B) A)
   , Var75 Γ A.

Definition vz75 {Γ A} : Var75 (snoc75 Γ A) A
 := fun Var75 vz75 vs => vz75 _ _.

Definition vs75 {Γ B A} : Var75 Γ A -> Var75 (snoc75 Γ B) A
 := fun x Var75 vz75 vs75 => vs75 _ _ _ (x Var75 vz75 vs75).

Definition Tm75 : Con75 -> Ty75 -> Set
 := fun Γ A =>
   forall (Tm75  : Con75 -> Ty75 -> Set)
     (var   : forall Γ A     , Var75 Γ A -> Tm75 Γ A)
     (lam   : forall Γ A B   , Tm75 (snoc75 Γ A) B -> Tm75 Γ (arr75 A B))
     (app   : forall Γ A B   , Tm75 Γ (arr75 A B) -> Tm75 Γ A -> Tm75 Γ B)
   , Tm75 Γ A.

Definition var75 {Γ A} : Var75 Γ A -> Tm75 Γ A
 := fun x Tm75 var75 lam app =>
     var75 _ _ x.

Definition lam75 {Γ A B} : Tm75 (snoc75 Γ A) B -> Tm75 Γ (arr75 A B)
 := fun t Tm75 var75 lam75 app =>
     lam75 _ _ _ (t Tm75 var75 lam75 app).

Definition app75 {Γ A B} : Tm75 Γ (arr75 A B) -> Tm75 Γ A -> Tm75 Γ B
 := fun t u Tm75 var75 lam75 app75 =>
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


Definition Ty76 : Set
 := forall (Ty76 : Set)
      (base   : Ty76)
      (arr : Ty76 -> Ty76 -> Ty76)
    , Ty76.

Definition base76 : Ty76 := fun _ base76 _ => base76.

Definition arr76 : Ty76 -> Ty76 -> Ty76
 := fun A B Ty76 base76 arr76 =>
     arr76 (A Ty76 base76 arr76) (B Ty76 base76 arr76).

Definition Con76 : Set
 := forall (Con76  : Set)
      (nil  : Con76)
      (snoc : Con76 -> Ty76 -> Con76)
    , Con76.

Definition nil76 : Con76
 := fun Con76 nil76 snoc => nil76.

Definition snoc76 : Con76 -> Ty76 -> Con76
 := fun Γ A Con76 nil76 snoc76 => snoc76 (Γ Con76 nil76 snoc76) A.

Definition Var76 : Con76 -> Ty76 -> Set
 := fun Γ A =>
   forall (Var76 : Con76 -> Ty76 -> Set)
     (vz  : forall Γ A, Var76 (snoc76 Γ A) A)
     (vs  : forall Γ B A, Var76 Γ A -> Var76 (snoc76 Γ B) A)
   , Var76 Γ A.

Definition vz76 {Γ A} : Var76 (snoc76 Γ A) A
 := fun Var76 vz76 vs => vz76 _ _.

Definition vs76 {Γ B A} : Var76 Γ A -> Var76 (snoc76 Γ B) A
 := fun x Var76 vz76 vs76 => vs76 _ _ _ (x Var76 vz76 vs76).

Definition Tm76 : Con76 -> Ty76 -> Set
 := fun Γ A =>
   forall (Tm76  : Con76 -> Ty76 -> Set)
     (var   : forall Γ A     , Var76 Γ A -> Tm76 Γ A)
     (lam   : forall Γ A B   , Tm76 (snoc76 Γ A) B -> Tm76 Γ (arr76 A B))
     (app   : forall Γ A B   , Tm76 Γ (arr76 A B) -> Tm76 Γ A -> Tm76 Γ B)
   , Tm76 Γ A.

Definition var76 {Γ A} : Var76 Γ A -> Tm76 Γ A
 := fun x Tm76 var76 lam app =>
     var76 _ _ x.

Definition lam76 {Γ A B} : Tm76 (snoc76 Γ A) B -> Tm76 Γ (arr76 A B)
 := fun t Tm76 var76 lam76 app =>
     lam76 _ _ _ (t Tm76 var76 lam76 app).

Definition app76 {Γ A B} : Tm76 Γ (arr76 A B) -> Tm76 Γ A -> Tm76 Γ B
 := fun t u Tm76 var76 lam76 app76 =>
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


Definition Ty77 : Set
 := forall (Ty77 : Set)
      (base   : Ty77)
      (arr : Ty77 -> Ty77 -> Ty77)
    , Ty77.

Definition base77 : Ty77 := fun _ base77 _ => base77.

Definition arr77 : Ty77 -> Ty77 -> Ty77
 := fun A B Ty77 base77 arr77 =>
     arr77 (A Ty77 base77 arr77) (B Ty77 base77 arr77).

Definition Con77 : Set
 := forall (Con77  : Set)
      (nil  : Con77)
      (snoc : Con77 -> Ty77 -> Con77)
    , Con77.

Definition nil77 : Con77
 := fun Con77 nil77 snoc => nil77.

Definition snoc77 : Con77 -> Ty77 -> Con77
 := fun Γ A Con77 nil77 snoc77 => snoc77 (Γ Con77 nil77 snoc77) A.

Definition Var77 : Con77 -> Ty77 -> Set
 := fun Γ A =>
   forall (Var77 : Con77 -> Ty77 -> Set)
     (vz  : forall Γ A, Var77 (snoc77 Γ A) A)
     (vs  : forall Γ B A, Var77 Γ A -> Var77 (snoc77 Γ B) A)
   , Var77 Γ A.

Definition vz77 {Γ A} : Var77 (snoc77 Γ A) A
 := fun Var77 vz77 vs => vz77 _ _.

Definition vs77 {Γ B A} : Var77 Γ A -> Var77 (snoc77 Γ B) A
 := fun x Var77 vz77 vs77 => vs77 _ _ _ (x Var77 vz77 vs77).

Definition Tm77 : Con77 -> Ty77 -> Set
 := fun Γ A =>
   forall (Tm77  : Con77 -> Ty77 -> Set)
     (var   : forall Γ A     , Var77 Γ A -> Tm77 Γ A)
     (lam   : forall Γ A B   , Tm77 (snoc77 Γ A) B -> Tm77 Γ (arr77 A B))
     (app   : forall Γ A B   , Tm77 Γ (arr77 A B) -> Tm77 Γ A -> Tm77 Γ B)
   , Tm77 Γ A.

Definition var77 {Γ A} : Var77 Γ A -> Tm77 Γ A
 := fun x Tm77 var77 lam app =>
     var77 _ _ x.

Definition lam77 {Γ A B} : Tm77 (snoc77 Γ A) B -> Tm77 Γ (arr77 A B)
 := fun t Tm77 var77 lam77 app =>
     lam77 _ _ _ (t Tm77 var77 lam77 app).

Definition app77 {Γ A B} : Tm77 Γ (arr77 A B) -> Tm77 Γ A -> Tm77 Γ B
 := fun t u Tm77 var77 lam77 app77 =>
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


Definition Ty78 : Set
 := forall (Ty78 : Set)
      (base   : Ty78)
      (arr : Ty78 -> Ty78 -> Ty78)
    , Ty78.

Definition base78 : Ty78 := fun _ base78 _ => base78.

Definition arr78 : Ty78 -> Ty78 -> Ty78
 := fun A B Ty78 base78 arr78 =>
     arr78 (A Ty78 base78 arr78) (B Ty78 base78 arr78).

Definition Con78 : Set
 := forall (Con78  : Set)
      (nil  : Con78)
      (snoc : Con78 -> Ty78 -> Con78)
    , Con78.

Definition nil78 : Con78
 := fun Con78 nil78 snoc => nil78.

Definition snoc78 : Con78 -> Ty78 -> Con78
 := fun Γ A Con78 nil78 snoc78 => snoc78 (Γ Con78 nil78 snoc78) A.

Definition Var78 : Con78 -> Ty78 -> Set
 := fun Γ A =>
   forall (Var78 : Con78 -> Ty78 -> Set)
     (vz  : forall Γ A, Var78 (snoc78 Γ A) A)
     (vs  : forall Γ B A, Var78 Γ A -> Var78 (snoc78 Γ B) A)
   , Var78 Γ A.

Definition vz78 {Γ A} : Var78 (snoc78 Γ A) A
 := fun Var78 vz78 vs => vz78 _ _.

Definition vs78 {Γ B A} : Var78 Γ A -> Var78 (snoc78 Γ B) A
 := fun x Var78 vz78 vs78 => vs78 _ _ _ (x Var78 vz78 vs78).

Definition Tm78 : Con78 -> Ty78 -> Set
 := fun Γ A =>
   forall (Tm78  : Con78 -> Ty78 -> Set)
     (var   : forall Γ A     , Var78 Γ A -> Tm78 Γ A)
     (lam   : forall Γ A B   , Tm78 (snoc78 Γ A) B -> Tm78 Γ (arr78 A B))
     (app   : forall Γ A B   , Tm78 Γ (arr78 A B) -> Tm78 Γ A -> Tm78 Γ B)
   , Tm78 Γ A.

Definition var78 {Γ A} : Var78 Γ A -> Tm78 Γ A
 := fun x Tm78 var78 lam app =>
     var78 _ _ x.

Definition lam78 {Γ A B} : Tm78 (snoc78 Γ A) B -> Tm78 Γ (arr78 A B)
 := fun t Tm78 var78 lam78 app =>
     lam78 _ _ _ (t Tm78 var78 lam78 app).

Definition app78 {Γ A B} : Tm78 Γ (arr78 A B) -> Tm78 Γ A -> Tm78 Γ B
 := fun t u Tm78 var78 lam78 app78 =>
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


Definition Ty79 : Set
 := forall (Ty79 : Set)
      (base   : Ty79)
      (arr : Ty79 -> Ty79 -> Ty79)
    , Ty79.

Definition base79 : Ty79 := fun _ base79 _ => base79.

Definition arr79 : Ty79 -> Ty79 -> Ty79
 := fun A B Ty79 base79 arr79 =>
     arr79 (A Ty79 base79 arr79) (B Ty79 base79 arr79).

Definition Con79 : Set
 := forall (Con79  : Set)
      (nil  : Con79)
      (snoc : Con79 -> Ty79 -> Con79)
    , Con79.

Definition nil79 : Con79
 := fun Con79 nil79 snoc => nil79.

Definition snoc79 : Con79 -> Ty79 -> Con79
 := fun Γ A Con79 nil79 snoc79 => snoc79 (Γ Con79 nil79 snoc79) A.

Definition Var79 : Con79 -> Ty79 -> Set
 := fun Γ A =>
   forall (Var79 : Con79 -> Ty79 -> Set)
     (vz  : forall Γ A, Var79 (snoc79 Γ A) A)
     (vs  : forall Γ B A, Var79 Γ A -> Var79 (snoc79 Γ B) A)
   , Var79 Γ A.

Definition vz79 {Γ A} : Var79 (snoc79 Γ A) A
 := fun Var79 vz79 vs => vz79 _ _.

Definition vs79 {Γ B A} : Var79 Γ A -> Var79 (snoc79 Γ B) A
 := fun x Var79 vz79 vs79 => vs79 _ _ _ (x Var79 vz79 vs79).

Definition Tm79 : Con79 -> Ty79 -> Set
 := fun Γ A =>
   forall (Tm79  : Con79 -> Ty79 -> Set)
     (var   : forall Γ A     , Var79 Γ A -> Tm79 Γ A)
     (lam   : forall Γ A B   , Tm79 (snoc79 Γ A) B -> Tm79 Γ (arr79 A B))
     (app   : forall Γ A B   , Tm79 Γ (arr79 A B) -> Tm79 Γ A -> Tm79 Γ B)
   , Tm79 Γ A.

Definition var79 {Γ A} : Var79 Γ A -> Tm79 Γ A
 := fun x Tm79 var79 lam app =>
     var79 _ _ x.

Definition lam79 {Γ A B} : Tm79 (snoc79 Γ A) B -> Tm79 Γ (arr79 A B)
 := fun t Tm79 var79 lam79 app =>
     lam79 _ _ _ (t Tm79 var79 lam79 app).

Definition app79 {Γ A B} : Tm79 Γ (arr79 A B) -> Tm79 Γ A -> Tm79 Γ B
 := fun t u Tm79 var79 lam79 app79 =>
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


Definition Ty80 : Set
 := forall (Ty80 : Set)
      (base   : Ty80)
      (arr : Ty80 -> Ty80 -> Ty80)
    , Ty80.

Definition base80 : Ty80 := fun _ base80 _ => base80.

Definition arr80 : Ty80 -> Ty80 -> Ty80
 := fun A B Ty80 base80 arr80 =>
     arr80 (A Ty80 base80 arr80) (B Ty80 base80 arr80).

Definition Con80 : Set
 := forall (Con80  : Set)
      (nil  : Con80)
      (snoc : Con80 -> Ty80 -> Con80)
    , Con80.

Definition nil80 : Con80
 := fun Con80 nil80 snoc => nil80.

Definition snoc80 : Con80 -> Ty80 -> Con80
 := fun Γ A Con80 nil80 snoc80 => snoc80 (Γ Con80 nil80 snoc80) A.

Definition Var80 : Con80 -> Ty80 -> Set
 := fun Γ A =>
   forall (Var80 : Con80 -> Ty80 -> Set)
     (vz  : forall Γ A, Var80 (snoc80 Γ A) A)
     (vs  : forall Γ B A, Var80 Γ A -> Var80 (snoc80 Γ B) A)
   , Var80 Γ A.

Definition vz80 {Γ A} : Var80 (snoc80 Γ A) A
 := fun Var80 vz80 vs => vz80 _ _.

Definition vs80 {Γ B A} : Var80 Γ A -> Var80 (snoc80 Γ B) A
 := fun x Var80 vz80 vs80 => vs80 _ _ _ (x Var80 vz80 vs80).

Definition Tm80 : Con80 -> Ty80 -> Set
 := fun Γ A =>
   forall (Tm80  : Con80 -> Ty80 -> Set)
     (var   : forall Γ A     , Var80 Γ A -> Tm80 Γ A)
     (lam   : forall Γ A B   , Tm80 (snoc80 Γ A) B -> Tm80 Γ (arr80 A B))
     (app   : forall Γ A B   , Tm80 Γ (arr80 A B) -> Tm80 Γ A -> Tm80 Γ B)
   , Tm80 Γ A.

Definition var80 {Γ A} : Var80 Γ A -> Tm80 Γ A
 := fun x Tm80 var80 lam app =>
     var80 _ _ x.

Definition lam80 {Γ A B} : Tm80 (snoc80 Γ A) B -> Tm80 Γ (arr80 A B)
 := fun t Tm80 var80 lam80 app =>
     lam80 _ _ _ (t Tm80 var80 lam80 app).

Definition app80 {Γ A B} : Tm80 Γ (arr80 A B) -> Tm80 Γ A -> Tm80 Γ B
 := fun t u Tm80 var80 lam80 app80 =>
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


Definition Ty81 : Set
 := forall (Ty81 : Set)
      (base   : Ty81)
      (arr : Ty81 -> Ty81 -> Ty81)
    , Ty81.

Definition base81 : Ty81 := fun _ base81 _ => base81.

Definition arr81 : Ty81 -> Ty81 -> Ty81
 := fun A B Ty81 base81 arr81 =>
     arr81 (A Ty81 base81 arr81) (B Ty81 base81 arr81).

Definition Con81 : Set
 := forall (Con81  : Set)
      (nil  : Con81)
      (snoc : Con81 -> Ty81 -> Con81)
    , Con81.

Definition nil81 : Con81
 := fun Con81 nil81 snoc => nil81.

Definition snoc81 : Con81 -> Ty81 -> Con81
 := fun Γ A Con81 nil81 snoc81 => snoc81 (Γ Con81 nil81 snoc81) A.

Definition Var81 : Con81 -> Ty81 -> Set
 := fun Γ A =>
   forall (Var81 : Con81 -> Ty81 -> Set)
     (vz  : forall Γ A, Var81 (snoc81 Γ A) A)
     (vs  : forall Γ B A, Var81 Γ A -> Var81 (snoc81 Γ B) A)
   , Var81 Γ A.

Definition vz81 {Γ A} : Var81 (snoc81 Γ A) A
 := fun Var81 vz81 vs => vz81 _ _.

Definition vs81 {Γ B A} : Var81 Γ A -> Var81 (snoc81 Γ B) A
 := fun x Var81 vz81 vs81 => vs81 _ _ _ (x Var81 vz81 vs81).

Definition Tm81 : Con81 -> Ty81 -> Set
 := fun Γ A =>
   forall (Tm81  : Con81 -> Ty81 -> Set)
     (var   : forall Γ A     , Var81 Γ A -> Tm81 Γ A)
     (lam   : forall Γ A B   , Tm81 (snoc81 Γ A) B -> Tm81 Γ (arr81 A B))
     (app   : forall Γ A B   , Tm81 Γ (arr81 A B) -> Tm81 Γ A -> Tm81 Γ B)
   , Tm81 Γ A.

Definition var81 {Γ A} : Var81 Γ A -> Tm81 Γ A
 := fun x Tm81 var81 lam app =>
     var81 _ _ x.

Definition lam81 {Γ A B} : Tm81 (snoc81 Γ A) B -> Tm81 Γ (arr81 A B)
 := fun t Tm81 var81 lam81 app =>
     lam81 _ _ _ (t Tm81 var81 lam81 app).

Definition app81 {Γ A B} : Tm81 Γ (arr81 A B) -> Tm81 Γ A -> Tm81 Γ B
 := fun t u Tm81 var81 lam81 app81 =>
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


Definition Ty82 : Set
 := forall (Ty82 : Set)
      (base   : Ty82)
      (arr : Ty82 -> Ty82 -> Ty82)
    , Ty82.

Definition base82 : Ty82 := fun _ base82 _ => base82.

Definition arr82 : Ty82 -> Ty82 -> Ty82
 := fun A B Ty82 base82 arr82 =>
     arr82 (A Ty82 base82 arr82) (B Ty82 base82 arr82).

Definition Con82 : Set
 := forall (Con82  : Set)
      (nil  : Con82)
      (snoc : Con82 -> Ty82 -> Con82)
    , Con82.

Definition nil82 : Con82
 := fun Con82 nil82 snoc => nil82.

Definition snoc82 : Con82 -> Ty82 -> Con82
 := fun Γ A Con82 nil82 snoc82 => snoc82 (Γ Con82 nil82 snoc82) A.

Definition Var82 : Con82 -> Ty82 -> Set
 := fun Γ A =>
   forall (Var82 : Con82 -> Ty82 -> Set)
     (vz  : forall Γ A, Var82 (snoc82 Γ A) A)
     (vs  : forall Γ B A, Var82 Γ A -> Var82 (snoc82 Γ B) A)
   , Var82 Γ A.

Definition vz82 {Γ A} : Var82 (snoc82 Γ A) A
 := fun Var82 vz82 vs => vz82 _ _.

Definition vs82 {Γ B A} : Var82 Γ A -> Var82 (snoc82 Γ B) A
 := fun x Var82 vz82 vs82 => vs82 _ _ _ (x Var82 vz82 vs82).

Definition Tm82 : Con82 -> Ty82 -> Set
 := fun Γ A =>
   forall (Tm82  : Con82 -> Ty82 -> Set)
     (var   : forall Γ A     , Var82 Γ A -> Tm82 Γ A)
     (lam   : forall Γ A B   , Tm82 (snoc82 Γ A) B -> Tm82 Γ (arr82 A B))
     (app   : forall Γ A B   , Tm82 Γ (arr82 A B) -> Tm82 Γ A -> Tm82 Γ B)
   , Tm82 Γ A.

Definition var82 {Γ A} : Var82 Γ A -> Tm82 Γ A
 := fun x Tm82 var82 lam app =>
     var82 _ _ x.

Definition lam82 {Γ A B} : Tm82 (snoc82 Γ A) B -> Tm82 Γ (arr82 A B)
 := fun t Tm82 var82 lam82 app =>
     lam82 _ _ _ (t Tm82 var82 lam82 app).

Definition app82 {Γ A B} : Tm82 Γ (arr82 A B) -> Tm82 Γ A -> Tm82 Γ B
 := fun t u Tm82 var82 lam82 app82 =>
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


Definition Ty83 : Set
 := forall (Ty83 : Set)
      (base   : Ty83)
      (arr : Ty83 -> Ty83 -> Ty83)
    , Ty83.

Definition base83 : Ty83 := fun _ base83 _ => base83.

Definition arr83 : Ty83 -> Ty83 -> Ty83
 := fun A B Ty83 base83 arr83 =>
     arr83 (A Ty83 base83 arr83) (B Ty83 base83 arr83).

Definition Con83 : Set
 := forall (Con83  : Set)
      (nil  : Con83)
      (snoc : Con83 -> Ty83 -> Con83)
    , Con83.

Definition nil83 : Con83
 := fun Con83 nil83 snoc => nil83.

Definition snoc83 : Con83 -> Ty83 -> Con83
 := fun Γ A Con83 nil83 snoc83 => snoc83 (Γ Con83 nil83 snoc83) A.

Definition Var83 : Con83 -> Ty83 -> Set
 := fun Γ A =>
   forall (Var83 : Con83 -> Ty83 -> Set)
     (vz  : forall Γ A, Var83 (snoc83 Γ A) A)
     (vs  : forall Γ B A, Var83 Γ A -> Var83 (snoc83 Γ B) A)
   , Var83 Γ A.

Definition vz83 {Γ A} : Var83 (snoc83 Γ A) A
 := fun Var83 vz83 vs => vz83 _ _.

Definition vs83 {Γ B A} : Var83 Γ A -> Var83 (snoc83 Γ B) A
 := fun x Var83 vz83 vs83 => vs83 _ _ _ (x Var83 vz83 vs83).

Definition Tm83 : Con83 -> Ty83 -> Set
 := fun Γ A =>
   forall (Tm83  : Con83 -> Ty83 -> Set)
     (var   : forall Γ A     , Var83 Γ A -> Tm83 Γ A)
     (lam   : forall Γ A B   , Tm83 (snoc83 Γ A) B -> Tm83 Γ (arr83 A B))
     (app   : forall Γ A B   , Tm83 Γ (arr83 A B) -> Tm83 Γ A -> Tm83 Γ B)
   , Tm83 Γ A.

Definition var83 {Γ A} : Var83 Γ A -> Tm83 Γ A
 := fun x Tm83 var83 lam app =>
     var83 _ _ x.

Definition lam83 {Γ A B} : Tm83 (snoc83 Γ A) B -> Tm83 Γ (arr83 A B)
 := fun t Tm83 var83 lam83 app =>
     lam83 _ _ _ (t Tm83 var83 lam83 app).

Definition app83 {Γ A B} : Tm83 Γ (arr83 A B) -> Tm83 Γ A -> Tm83 Γ B
 := fun t u Tm83 var83 lam83 app83 =>
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


Definition Ty84 : Set
 := forall (Ty84 : Set)
      (base   : Ty84)
      (arr : Ty84 -> Ty84 -> Ty84)
    , Ty84.

Definition base84 : Ty84 := fun _ base84 _ => base84.

Definition arr84 : Ty84 -> Ty84 -> Ty84
 := fun A B Ty84 base84 arr84 =>
     arr84 (A Ty84 base84 arr84) (B Ty84 base84 arr84).

Definition Con84 : Set
 := forall (Con84  : Set)
      (nil  : Con84)
      (snoc : Con84 -> Ty84 -> Con84)
    , Con84.

Definition nil84 : Con84
 := fun Con84 nil84 snoc => nil84.

Definition snoc84 : Con84 -> Ty84 -> Con84
 := fun Γ A Con84 nil84 snoc84 => snoc84 (Γ Con84 nil84 snoc84) A.

Definition Var84 : Con84 -> Ty84 -> Set
 := fun Γ A =>
   forall (Var84 : Con84 -> Ty84 -> Set)
     (vz  : forall Γ A, Var84 (snoc84 Γ A) A)
     (vs  : forall Γ B A, Var84 Γ A -> Var84 (snoc84 Γ B) A)
   , Var84 Γ A.

Definition vz84 {Γ A} : Var84 (snoc84 Γ A) A
 := fun Var84 vz84 vs => vz84 _ _.

Definition vs84 {Γ B A} : Var84 Γ A -> Var84 (snoc84 Γ B) A
 := fun x Var84 vz84 vs84 => vs84 _ _ _ (x Var84 vz84 vs84).

Definition Tm84 : Con84 -> Ty84 -> Set
 := fun Γ A =>
   forall (Tm84  : Con84 -> Ty84 -> Set)
     (var   : forall Γ A     , Var84 Γ A -> Tm84 Γ A)
     (lam   : forall Γ A B   , Tm84 (snoc84 Γ A) B -> Tm84 Γ (arr84 A B))
     (app   : forall Γ A B   , Tm84 Γ (arr84 A B) -> Tm84 Γ A -> Tm84 Γ B)
   , Tm84 Γ A.

Definition var84 {Γ A} : Var84 Γ A -> Tm84 Γ A
 := fun x Tm84 var84 lam app =>
     var84 _ _ x.

Definition lam84 {Γ A B} : Tm84 (snoc84 Γ A) B -> Tm84 Γ (arr84 A B)
 := fun t Tm84 var84 lam84 app =>
     lam84 _ _ _ (t Tm84 var84 lam84 app).

Definition app84 {Γ A B} : Tm84 Γ (arr84 A B) -> Tm84 Γ A -> Tm84 Γ B
 := fun t u Tm84 var84 lam84 app84 =>
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


Definition Ty85 : Set
 := forall (Ty85 : Set)
      (base   : Ty85)
      (arr : Ty85 -> Ty85 -> Ty85)
    , Ty85.

Definition base85 : Ty85 := fun _ base85 _ => base85.

Definition arr85 : Ty85 -> Ty85 -> Ty85
 := fun A B Ty85 base85 arr85 =>
     arr85 (A Ty85 base85 arr85) (B Ty85 base85 arr85).

Definition Con85 : Set
 := forall (Con85  : Set)
      (nil  : Con85)
      (snoc : Con85 -> Ty85 -> Con85)
    , Con85.

Definition nil85 : Con85
 := fun Con85 nil85 snoc => nil85.

Definition snoc85 : Con85 -> Ty85 -> Con85
 := fun Γ A Con85 nil85 snoc85 => snoc85 (Γ Con85 nil85 snoc85) A.

Definition Var85 : Con85 -> Ty85 -> Set
 := fun Γ A =>
   forall (Var85 : Con85 -> Ty85 -> Set)
     (vz  : forall Γ A, Var85 (snoc85 Γ A) A)
     (vs  : forall Γ B A, Var85 Γ A -> Var85 (snoc85 Γ B) A)
   , Var85 Γ A.

Definition vz85 {Γ A} : Var85 (snoc85 Γ A) A
 := fun Var85 vz85 vs => vz85 _ _.

Definition vs85 {Γ B A} : Var85 Γ A -> Var85 (snoc85 Γ B) A
 := fun x Var85 vz85 vs85 => vs85 _ _ _ (x Var85 vz85 vs85).

Definition Tm85 : Con85 -> Ty85 -> Set
 := fun Γ A =>
   forall (Tm85  : Con85 -> Ty85 -> Set)
     (var   : forall Γ A     , Var85 Γ A -> Tm85 Γ A)
     (lam   : forall Γ A B   , Tm85 (snoc85 Γ A) B -> Tm85 Γ (arr85 A B))
     (app   : forall Γ A B   , Tm85 Γ (arr85 A B) -> Tm85 Γ A -> Tm85 Γ B)
   , Tm85 Γ A.

Definition var85 {Γ A} : Var85 Γ A -> Tm85 Γ A
 := fun x Tm85 var85 lam app =>
     var85 _ _ x.

Definition lam85 {Γ A B} : Tm85 (snoc85 Γ A) B -> Tm85 Γ (arr85 A B)
 := fun t Tm85 var85 lam85 app =>
     lam85 _ _ _ (t Tm85 var85 lam85 app).

Definition app85 {Γ A B} : Tm85 Γ (arr85 A B) -> Tm85 Γ A -> Tm85 Γ B
 := fun t u Tm85 var85 lam85 app85 =>
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


Definition Ty86 : Set
 := forall (Ty86 : Set)
      (base   : Ty86)
      (arr : Ty86 -> Ty86 -> Ty86)
    , Ty86.

Definition base86 : Ty86 := fun _ base86 _ => base86.

Definition arr86 : Ty86 -> Ty86 -> Ty86
 := fun A B Ty86 base86 arr86 =>
     arr86 (A Ty86 base86 arr86) (B Ty86 base86 arr86).

Definition Con86 : Set
 := forall (Con86  : Set)
      (nil  : Con86)
      (snoc : Con86 -> Ty86 -> Con86)
    , Con86.

Definition nil86 : Con86
 := fun Con86 nil86 snoc => nil86.

Definition snoc86 : Con86 -> Ty86 -> Con86
 := fun Γ A Con86 nil86 snoc86 => snoc86 (Γ Con86 nil86 snoc86) A.

Definition Var86 : Con86 -> Ty86 -> Set
 := fun Γ A =>
   forall (Var86 : Con86 -> Ty86 -> Set)
     (vz  : forall Γ A, Var86 (snoc86 Γ A) A)
     (vs  : forall Γ B A, Var86 Γ A -> Var86 (snoc86 Γ B) A)
   , Var86 Γ A.

Definition vz86 {Γ A} : Var86 (snoc86 Γ A) A
 := fun Var86 vz86 vs => vz86 _ _.

Definition vs86 {Γ B A} : Var86 Γ A -> Var86 (snoc86 Γ B) A
 := fun x Var86 vz86 vs86 => vs86 _ _ _ (x Var86 vz86 vs86).

Definition Tm86 : Con86 -> Ty86 -> Set
 := fun Γ A =>
   forall (Tm86  : Con86 -> Ty86 -> Set)
     (var   : forall Γ A     , Var86 Γ A -> Tm86 Γ A)
     (lam   : forall Γ A B   , Tm86 (snoc86 Γ A) B -> Tm86 Γ (arr86 A B))
     (app   : forall Γ A B   , Tm86 Γ (arr86 A B) -> Tm86 Γ A -> Tm86 Γ B)
   , Tm86 Γ A.

Definition var86 {Γ A} : Var86 Γ A -> Tm86 Γ A
 := fun x Tm86 var86 lam app =>
     var86 _ _ x.

Definition lam86 {Γ A B} : Tm86 (snoc86 Γ A) B -> Tm86 Γ (arr86 A B)
 := fun t Tm86 var86 lam86 app =>
     lam86 _ _ _ (t Tm86 var86 lam86 app).

Definition app86 {Γ A B} : Tm86 Γ (arr86 A B) -> Tm86 Γ A -> Tm86 Γ B
 := fun t u Tm86 var86 lam86 app86 =>
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


Definition Ty87 : Set
 := forall (Ty87 : Set)
      (base   : Ty87)
      (arr : Ty87 -> Ty87 -> Ty87)
    , Ty87.

Definition base87 : Ty87 := fun _ base87 _ => base87.

Definition arr87 : Ty87 -> Ty87 -> Ty87
 := fun A B Ty87 base87 arr87 =>
     arr87 (A Ty87 base87 arr87) (B Ty87 base87 arr87).

Definition Con87 : Set
 := forall (Con87  : Set)
      (nil  : Con87)
      (snoc : Con87 -> Ty87 -> Con87)
    , Con87.

Definition nil87 : Con87
 := fun Con87 nil87 snoc => nil87.

Definition snoc87 : Con87 -> Ty87 -> Con87
 := fun Γ A Con87 nil87 snoc87 => snoc87 (Γ Con87 nil87 snoc87) A.

Definition Var87 : Con87 -> Ty87 -> Set
 := fun Γ A =>
   forall (Var87 : Con87 -> Ty87 -> Set)
     (vz  : forall Γ A, Var87 (snoc87 Γ A) A)
     (vs  : forall Γ B A, Var87 Γ A -> Var87 (snoc87 Γ B) A)
   , Var87 Γ A.

Definition vz87 {Γ A} : Var87 (snoc87 Γ A) A
 := fun Var87 vz87 vs => vz87 _ _.

Definition vs87 {Γ B A} : Var87 Γ A -> Var87 (snoc87 Γ B) A
 := fun x Var87 vz87 vs87 => vs87 _ _ _ (x Var87 vz87 vs87).

Definition Tm87 : Con87 -> Ty87 -> Set
 := fun Γ A =>
   forall (Tm87  : Con87 -> Ty87 -> Set)
     (var   : forall Γ A     , Var87 Γ A -> Tm87 Γ A)
     (lam   : forall Γ A B   , Tm87 (snoc87 Γ A) B -> Tm87 Γ (arr87 A B))
     (app   : forall Γ A B   , Tm87 Γ (arr87 A B) -> Tm87 Γ A -> Tm87 Γ B)
   , Tm87 Γ A.

Definition var87 {Γ A} : Var87 Γ A -> Tm87 Γ A
 := fun x Tm87 var87 lam app =>
     var87 _ _ x.

Definition lam87 {Γ A B} : Tm87 (snoc87 Γ A) B -> Tm87 Γ (arr87 A B)
 := fun t Tm87 var87 lam87 app =>
     lam87 _ _ _ (t Tm87 var87 lam87 app).

Definition app87 {Γ A B} : Tm87 Γ (arr87 A B) -> Tm87 Γ A -> Tm87 Γ B
 := fun t u Tm87 var87 lam87 app87 =>
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


Definition Ty88 : Set
 := forall (Ty88 : Set)
      (base   : Ty88)
      (arr : Ty88 -> Ty88 -> Ty88)
    , Ty88.

Definition base88 : Ty88 := fun _ base88 _ => base88.

Definition arr88 : Ty88 -> Ty88 -> Ty88
 := fun A B Ty88 base88 arr88 =>
     arr88 (A Ty88 base88 arr88) (B Ty88 base88 arr88).

Definition Con88 : Set
 := forall (Con88  : Set)
      (nil  : Con88)
      (snoc : Con88 -> Ty88 -> Con88)
    , Con88.

Definition nil88 : Con88
 := fun Con88 nil88 snoc => nil88.

Definition snoc88 : Con88 -> Ty88 -> Con88
 := fun Γ A Con88 nil88 snoc88 => snoc88 (Γ Con88 nil88 snoc88) A.

Definition Var88 : Con88 -> Ty88 -> Set
 := fun Γ A =>
   forall (Var88 : Con88 -> Ty88 -> Set)
     (vz  : forall Γ A, Var88 (snoc88 Γ A) A)
     (vs  : forall Γ B A, Var88 Γ A -> Var88 (snoc88 Γ B) A)
   , Var88 Γ A.

Definition vz88 {Γ A} : Var88 (snoc88 Γ A) A
 := fun Var88 vz88 vs => vz88 _ _.

Definition vs88 {Γ B A} : Var88 Γ A -> Var88 (snoc88 Γ B) A
 := fun x Var88 vz88 vs88 => vs88 _ _ _ (x Var88 vz88 vs88).

Definition Tm88 : Con88 -> Ty88 -> Set
 := fun Γ A =>
   forall (Tm88  : Con88 -> Ty88 -> Set)
     (var   : forall Γ A     , Var88 Γ A -> Tm88 Γ A)
     (lam   : forall Γ A B   , Tm88 (snoc88 Γ A) B -> Tm88 Γ (arr88 A B))
     (app   : forall Γ A B   , Tm88 Γ (arr88 A B) -> Tm88 Γ A -> Tm88 Γ B)
   , Tm88 Γ A.

Definition var88 {Γ A} : Var88 Γ A -> Tm88 Γ A
 := fun x Tm88 var88 lam app =>
     var88 _ _ x.

Definition lam88 {Γ A B} : Tm88 (snoc88 Γ A) B -> Tm88 Γ (arr88 A B)
 := fun t Tm88 var88 lam88 app =>
     lam88 _ _ _ (t Tm88 var88 lam88 app).

Definition app88 {Γ A B} : Tm88 Γ (arr88 A B) -> Tm88 Γ A -> Tm88 Γ B
 := fun t u Tm88 var88 lam88 app88 =>
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


Definition Ty89 : Set
 := forall (Ty89 : Set)
      (base   : Ty89)
      (arr : Ty89 -> Ty89 -> Ty89)
    , Ty89.

Definition base89 : Ty89 := fun _ base89 _ => base89.

Definition arr89 : Ty89 -> Ty89 -> Ty89
 := fun A B Ty89 base89 arr89 =>
     arr89 (A Ty89 base89 arr89) (B Ty89 base89 arr89).

Definition Con89 : Set
 := forall (Con89  : Set)
      (nil  : Con89)
      (snoc : Con89 -> Ty89 -> Con89)
    , Con89.

Definition nil89 : Con89
 := fun Con89 nil89 snoc => nil89.

Definition snoc89 : Con89 -> Ty89 -> Con89
 := fun Γ A Con89 nil89 snoc89 => snoc89 (Γ Con89 nil89 snoc89) A.

Definition Var89 : Con89 -> Ty89 -> Set
 := fun Γ A =>
   forall (Var89 : Con89 -> Ty89 -> Set)
     (vz  : forall Γ A, Var89 (snoc89 Γ A) A)
     (vs  : forall Γ B A, Var89 Γ A -> Var89 (snoc89 Γ B) A)
   , Var89 Γ A.

Definition vz89 {Γ A} : Var89 (snoc89 Γ A) A
 := fun Var89 vz89 vs => vz89 _ _.

Definition vs89 {Γ B A} : Var89 Γ A -> Var89 (snoc89 Γ B) A
 := fun x Var89 vz89 vs89 => vs89 _ _ _ (x Var89 vz89 vs89).

Definition Tm89 : Con89 -> Ty89 -> Set
 := fun Γ A =>
   forall (Tm89  : Con89 -> Ty89 -> Set)
     (var   : forall Γ A     , Var89 Γ A -> Tm89 Γ A)
     (lam   : forall Γ A B   , Tm89 (snoc89 Γ A) B -> Tm89 Γ (arr89 A B))
     (app   : forall Γ A B   , Tm89 Γ (arr89 A B) -> Tm89 Γ A -> Tm89 Γ B)
   , Tm89 Γ A.

Definition var89 {Γ A} : Var89 Γ A -> Tm89 Γ A
 := fun x Tm89 var89 lam app =>
     var89 _ _ x.

Definition lam89 {Γ A B} : Tm89 (snoc89 Γ A) B -> Tm89 Γ (arr89 A B)
 := fun t Tm89 var89 lam89 app =>
     lam89 _ _ _ (t Tm89 var89 lam89 app).

Definition app89 {Γ A B} : Tm89 Γ (arr89 A B) -> Tm89 Γ A -> Tm89 Γ B
 := fun t u Tm89 var89 lam89 app89 =>
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


Definition Ty90 : Set
 := forall (Ty90 : Set)
      (base   : Ty90)
      (arr : Ty90 -> Ty90 -> Ty90)
    , Ty90.

Definition base90 : Ty90 := fun _ base90 _ => base90.

Definition arr90 : Ty90 -> Ty90 -> Ty90
 := fun A B Ty90 base90 arr90 =>
     arr90 (A Ty90 base90 arr90) (B Ty90 base90 arr90).

Definition Con90 : Set
 := forall (Con90  : Set)
      (nil  : Con90)
      (snoc : Con90 -> Ty90 -> Con90)
    , Con90.

Definition nil90 : Con90
 := fun Con90 nil90 snoc => nil90.

Definition snoc90 : Con90 -> Ty90 -> Con90
 := fun Γ A Con90 nil90 snoc90 => snoc90 (Γ Con90 nil90 snoc90) A.

Definition Var90 : Con90 -> Ty90 -> Set
 := fun Γ A =>
   forall (Var90 : Con90 -> Ty90 -> Set)
     (vz  : forall Γ A, Var90 (snoc90 Γ A) A)
     (vs  : forall Γ B A, Var90 Γ A -> Var90 (snoc90 Γ B) A)
   , Var90 Γ A.

Definition vz90 {Γ A} : Var90 (snoc90 Γ A) A
 := fun Var90 vz90 vs => vz90 _ _.

Definition vs90 {Γ B A} : Var90 Γ A -> Var90 (snoc90 Γ B) A
 := fun x Var90 vz90 vs90 => vs90 _ _ _ (x Var90 vz90 vs90).

Definition Tm90 : Con90 -> Ty90 -> Set
 := fun Γ A =>
   forall (Tm90  : Con90 -> Ty90 -> Set)
     (var   : forall Γ A     , Var90 Γ A -> Tm90 Γ A)
     (lam   : forall Γ A B   , Tm90 (snoc90 Γ A) B -> Tm90 Γ (arr90 A B))
     (app   : forall Γ A B   , Tm90 Γ (arr90 A B) -> Tm90 Γ A -> Tm90 Γ B)
   , Tm90 Γ A.

Definition var90 {Γ A} : Var90 Γ A -> Tm90 Γ A
 := fun x Tm90 var90 lam app =>
     var90 _ _ x.

Definition lam90 {Γ A B} : Tm90 (snoc90 Γ A) B -> Tm90 Γ (arr90 A B)
 := fun t Tm90 var90 lam90 app =>
     lam90 _ _ _ (t Tm90 var90 lam90 app).

Definition app90 {Γ A B} : Tm90 Γ (arr90 A B) -> Tm90 Γ A -> Tm90 Γ B
 := fun t u Tm90 var90 lam90 app90 =>
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


Definition Ty91 : Set
 := forall (Ty91 : Set)
      (base   : Ty91)
      (arr : Ty91 -> Ty91 -> Ty91)
    , Ty91.

Definition base91 : Ty91 := fun _ base91 _ => base91.

Definition arr91 : Ty91 -> Ty91 -> Ty91
 := fun A B Ty91 base91 arr91 =>
     arr91 (A Ty91 base91 arr91) (B Ty91 base91 arr91).

Definition Con91 : Set
 := forall (Con91  : Set)
      (nil  : Con91)
      (snoc : Con91 -> Ty91 -> Con91)
    , Con91.

Definition nil91 : Con91
 := fun Con91 nil91 snoc => nil91.

Definition snoc91 : Con91 -> Ty91 -> Con91
 := fun Γ A Con91 nil91 snoc91 => snoc91 (Γ Con91 nil91 snoc91) A.

Definition Var91 : Con91 -> Ty91 -> Set
 := fun Γ A =>
   forall (Var91 : Con91 -> Ty91 -> Set)
     (vz  : forall Γ A, Var91 (snoc91 Γ A) A)
     (vs  : forall Γ B A, Var91 Γ A -> Var91 (snoc91 Γ B) A)
   , Var91 Γ A.

Definition vz91 {Γ A} : Var91 (snoc91 Γ A) A
 := fun Var91 vz91 vs => vz91 _ _.

Definition vs91 {Γ B A} : Var91 Γ A -> Var91 (snoc91 Γ B) A
 := fun x Var91 vz91 vs91 => vs91 _ _ _ (x Var91 vz91 vs91).

Definition Tm91 : Con91 -> Ty91 -> Set
 := fun Γ A =>
   forall (Tm91  : Con91 -> Ty91 -> Set)
     (var   : forall Γ A     , Var91 Γ A -> Tm91 Γ A)
     (lam   : forall Γ A B   , Tm91 (snoc91 Γ A) B -> Tm91 Γ (arr91 A B))
     (app   : forall Γ A B   , Tm91 Γ (arr91 A B) -> Tm91 Γ A -> Tm91 Γ B)
   , Tm91 Γ A.

Definition var91 {Γ A} : Var91 Γ A -> Tm91 Γ A
 := fun x Tm91 var91 lam app =>
     var91 _ _ x.

Definition lam91 {Γ A B} : Tm91 (snoc91 Γ A) B -> Tm91 Γ (arr91 A B)
 := fun t Tm91 var91 lam91 app =>
     lam91 _ _ _ (t Tm91 var91 lam91 app).

Definition app91 {Γ A B} : Tm91 Γ (arr91 A B) -> Tm91 Γ A -> Tm91 Γ B
 := fun t u Tm91 var91 lam91 app91 =>
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


Definition Ty92 : Set
 := forall (Ty92 : Set)
      (base   : Ty92)
      (arr : Ty92 -> Ty92 -> Ty92)
    , Ty92.

Definition base92 : Ty92 := fun _ base92 _ => base92.

Definition arr92 : Ty92 -> Ty92 -> Ty92
 := fun A B Ty92 base92 arr92 =>
     arr92 (A Ty92 base92 arr92) (B Ty92 base92 arr92).

Definition Con92 : Set
 := forall (Con92  : Set)
      (nil  : Con92)
      (snoc : Con92 -> Ty92 -> Con92)
    , Con92.

Definition nil92 : Con92
 := fun Con92 nil92 snoc => nil92.

Definition snoc92 : Con92 -> Ty92 -> Con92
 := fun Γ A Con92 nil92 snoc92 => snoc92 (Γ Con92 nil92 snoc92) A.

Definition Var92 : Con92 -> Ty92 -> Set
 := fun Γ A =>
   forall (Var92 : Con92 -> Ty92 -> Set)
     (vz  : forall Γ A, Var92 (snoc92 Γ A) A)
     (vs  : forall Γ B A, Var92 Γ A -> Var92 (snoc92 Γ B) A)
   , Var92 Γ A.

Definition vz92 {Γ A} : Var92 (snoc92 Γ A) A
 := fun Var92 vz92 vs => vz92 _ _.

Definition vs92 {Γ B A} : Var92 Γ A -> Var92 (snoc92 Γ B) A
 := fun x Var92 vz92 vs92 => vs92 _ _ _ (x Var92 vz92 vs92).

Definition Tm92 : Con92 -> Ty92 -> Set
 := fun Γ A =>
   forall (Tm92  : Con92 -> Ty92 -> Set)
     (var   : forall Γ A     , Var92 Γ A -> Tm92 Γ A)
     (lam   : forall Γ A B   , Tm92 (snoc92 Γ A) B -> Tm92 Γ (arr92 A B))
     (app   : forall Γ A B   , Tm92 Γ (arr92 A B) -> Tm92 Γ A -> Tm92 Γ B)
   , Tm92 Γ A.

Definition var92 {Γ A} : Var92 Γ A -> Tm92 Γ A
 := fun x Tm92 var92 lam app =>
     var92 _ _ x.

Definition lam92 {Γ A B} : Tm92 (snoc92 Γ A) B -> Tm92 Γ (arr92 A B)
 := fun t Tm92 var92 lam92 app =>
     lam92 _ _ _ (t Tm92 var92 lam92 app).

Definition app92 {Γ A B} : Tm92 Γ (arr92 A B) -> Tm92 Γ A -> Tm92 Γ B
 := fun t u Tm92 var92 lam92 app92 =>
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


Definition Ty93 : Set
 := forall (Ty93 : Set)
      (base   : Ty93)
      (arr : Ty93 -> Ty93 -> Ty93)
    , Ty93.

Definition base93 : Ty93 := fun _ base93 _ => base93.

Definition arr93 : Ty93 -> Ty93 -> Ty93
 := fun A B Ty93 base93 arr93 =>
     arr93 (A Ty93 base93 arr93) (B Ty93 base93 arr93).

Definition Con93 : Set
 := forall (Con93  : Set)
      (nil  : Con93)
      (snoc : Con93 -> Ty93 -> Con93)
    , Con93.

Definition nil93 : Con93
 := fun Con93 nil93 snoc => nil93.

Definition snoc93 : Con93 -> Ty93 -> Con93
 := fun Γ A Con93 nil93 snoc93 => snoc93 (Γ Con93 nil93 snoc93) A.

Definition Var93 : Con93 -> Ty93 -> Set
 := fun Γ A =>
   forall (Var93 : Con93 -> Ty93 -> Set)
     (vz  : forall Γ A, Var93 (snoc93 Γ A) A)
     (vs  : forall Γ B A, Var93 Γ A -> Var93 (snoc93 Γ B) A)
   , Var93 Γ A.

Definition vz93 {Γ A} : Var93 (snoc93 Γ A) A
 := fun Var93 vz93 vs => vz93 _ _.

Definition vs93 {Γ B A} : Var93 Γ A -> Var93 (snoc93 Γ B) A
 := fun x Var93 vz93 vs93 => vs93 _ _ _ (x Var93 vz93 vs93).

Definition Tm93 : Con93 -> Ty93 -> Set
 := fun Γ A =>
   forall (Tm93  : Con93 -> Ty93 -> Set)
     (var   : forall Γ A     , Var93 Γ A -> Tm93 Γ A)
     (lam   : forall Γ A B   , Tm93 (snoc93 Γ A) B -> Tm93 Γ (arr93 A B))
     (app   : forall Γ A B   , Tm93 Γ (arr93 A B) -> Tm93 Γ A -> Tm93 Γ B)
   , Tm93 Γ A.

Definition var93 {Γ A} : Var93 Γ A -> Tm93 Γ A
 := fun x Tm93 var93 lam app =>
     var93 _ _ x.

Definition lam93 {Γ A B} : Tm93 (snoc93 Γ A) B -> Tm93 Γ (arr93 A B)
 := fun t Tm93 var93 lam93 app =>
     lam93 _ _ _ (t Tm93 var93 lam93 app).

Definition app93 {Γ A B} : Tm93 Γ (arr93 A B) -> Tm93 Γ A -> Tm93 Γ B
 := fun t u Tm93 var93 lam93 app93 =>
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


Definition Ty94 : Set
 := forall (Ty94 : Set)
      (base   : Ty94)
      (arr : Ty94 -> Ty94 -> Ty94)
    , Ty94.

Definition base94 : Ty94 := fun _ base94 _ => base94.

Definition arr94 : Ty94 -> Ty94 -> Ty94
 := fun A B Ty94 base94 arr94 =>
     arr94 (A Ty94 base94 arr94) (B Ty94 base94 arr94).

Definition Con94 : Set
 := forall (Con94  : Set)
      (nil  : Con94)
      (snoc : Con94 -> Ty94 -> Con94)
    , Con94.

Definition nil94 : Con94
 := fun Con94 nil94 snoc => nil94.

Definition snoc94 : Con94 -> Ty94 -> Con94
 := fun Γ A Con94 nil94 snoc94 => snoc94 (Γ Con94 nil94 snoc94) A.

Definition Var94 : Con94 -> Ty94 -> Set
 := fun Γ A =>
   forall (Var94 : Con94 -> Ty94 -> Set)
     (vz  : forall Γ A, Var94 (snoc94 Γ A) A)
     (vs  : forall Γ B A, Var94 Γ A -> Var94 (snoc94 Γ B) A)
   , Var94 Γ A.

Definition vz94 {Γ A} : Var94 (snoc94 Γ A) A
 := fun Var94 vz94 vs => vz94 _ _.

Definition vs94 {Γ B A} : Var94 Γ A -> Var94 (snoc94 Γ B) A
 := fun x Var94 vz94 vs94 => vs94 _ _ _ (x Var94 vz94 vs94).

Definition Tm94 : Con94 -> Ty94 -> Set
 := fun Γ A =>
   forall (Tm94  : Con94 -> Ty94 -> Set)
     (var   : forall Γ A     , Var94 Γ A -> Tm94 Γ A)
     (lam   : forall Γ A B   , Tm94 (snoc94 Γ A) B -> Tm94 Γ (arr94 A B))
     (app   : forall Γ A B   , Tm94 Γ (arr94 A B) -> Tm94 Γ A -> Tm94 Γ B)
   , Tm94 Γ A.

Definition var94 {Γ A} : Var94 Γ A -> Tm94 Γ A
 := fun x Tm94 var94 lam app =>
     var94 _ _ x.

Definition lam94 {Γ A B} : Tm94 (snoc94 Γ A) B -> Tm94 Γ (arr94 A B)
 := fun t Tm94 var94 lam94 app =>
     lam94 _ _ _ (t Tm94 var94 lam94 app).

Definition app94 {Γ A B} : Tm94 Γ (arr94 A B) -> Tm94 Γ A -> Tm94 Γ B
 := fun t u Tm94 var94 lam94 app94 =>
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


Definition Ty95 : Set
 := forall (Ty95 : Set)
      (base   : Ty95)
      (arr : Ty95 -> Ty95 -> Ty95)
    , Ty95.

Definition base95 : Ty95 := fun _ base95 _ => base95.

Definition arr95 : Ty95 -> Ty95 -> Ty95
 := fun A B Ty95 base95 arr95 =>
     arr95 (A Ty95 base95 arr95) (B Ty95 base95 arr95).

Definition Con95 : Set
 := forall (Con95  : Set)
      (nil  : Con95)
      (snoc : Con95 -> Ty95 -> Con95)
    , Con95.

Definition nil95 : Con95
 := fun Con95 nil95 snoc => nil95.

Definition snoc95 : Con95 -> Ty95 -> Con95
 := fun Γ A Con95 nil95 snoc95 => snoc95 (Γ Con95 nil95 snoc95) A.

Definition Var95 : Con95 -> Ty95 -> Set
 := fun Γ A =>
   forall (Var95 : Con95 -> Ty95 -> Set)
     (vz  : forall Γ A, Var95 (snoc95 Γ A) A)
     (vs  : forall Γ B A, Var95 Γ A -> Var95 (snoc95 Γ B) A)
   , Var95 Γ A.

Definition vz95 {Γ A} : Var95 (snoc95 Γ A) A
 := fun Var95 vz95 vs => vz95 _ _.

Definition vs95 {Γ B A} : Var95 Γ A -> Var95 (snoc95 Γ B) A
 := fun x Var95 vz95 vs95 => vs95 _ _ _ (x Var95 vz95 vs95).

Definition Tm95 : Con95 -> Ty95 -> Set
 := fun Γ A =>
   forall (Tm95  : Con95 -> Ty95 -> Set)
     (var   : forall Γ A     , Var95 Γ A -> Tm95 Γ A)
     (lam   : forall Γ A B   , Tm95 (snoc95 Γ A) B -> Tm95 Γ (arr95 A B))
     (app   : forall Γ A B   , Tm95 Γ (arr95 A B) -> Tm95 Γ A -> Tm95 Γ B)
   , Tm95 Γ A.

Definition var95 {Γ A} : Var95 Γ A -> Tm95 Γ A
 := fun x Tm95 var95 lam app =>
     var95 _ _ x.

Definition lam95 {Γ A B} : Tm95 (snoc95 Γ A) B -> Tm95 Γ (arr95 A B)
 := fun t Tm95 var95 lam95 app =>
     lam95 _ _ _ (t Tm95 var95 lam95 app).

Definition app95 {Γ A B} : Tm95 Γ (arr95 A B) -> Tm95 Γ A -> Tm95 Γ B
 := fun t u Tm95 var95 lam95 app95 =>
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


Definition Ty96 : Set
 := forall (Ty96 : Set)
      (base   : Ty96)
      (arr : Ty96 -> Ty96 -> Ty96)
    , Ty96.

Definition base96 : Ty96 := fun _ base96 _ => base96.

Definition arr96 : Ty96 -> Ty96 -> Ty96
 := fun A B Ty96 base96 arr96 =>
     arr96 (A Ty96 base96 arr96) (B Ty96 base96 arr96).

Definition Con96 : Set
 := forall (Con96  : Set)
      (nil  : Con96)
      (snoc : Con96 -> Ty96 -> Con96)
    , Con96.

Definition nil96 : Con96
 := fun Con96 nil96 snoc => nil96.

Definition snoc96 : Con96 -> Ty96 -> Con96
 := fun Γ A Con96 nil96 snoc96 => snoc96 (Γ Con96 nil96 snoc96) A.

Definition Var96 : Con96 -> Ty96 -> Set
 := fun Γ A =>
   forall (Var96 : Con96 -> Ty96 -> Set)
     (vz  : forall Γ A, Var96 (snoc96 Γ A) A)
     (vs  : forall Γ B A, Var96 Γ A -> Var96 (snoc96 Γ B) A)
   , Var96 Γ A.

Definition vz96 {Γ A} : Var96 (snoc96 Γ A) A
 := fun Var96 vz96 vs => vz96 _ _.

Definition vs96 {Γ B A} : Var96 Γ A -> Var96 (snoc96 Γ B) A
 := fun x Var96 vz96 vs96 => vs96 _ _ _ (x Var96 vz96 vs96).

Definition Tm96 : Con96 -> Ty96 -> Set
 := fun Γ A =>
   forall (Tm96  : Con96 -> Ty96 -> Set)
     (var   : forall Γ A     , Var96 Γ A -> Tm96 Γ A)
     (lam   : forall Γ A B   , Tm96 (snoc96 Γ A) B -> Tm96 Γ (arr96 A B))
     (app   : forall Γ A B   , Tm96 Γ (arr96 A B) -> Tm96 Γ A -> Tm96 Γ B)
   , Tm96 Γ A.

Definition var96 {Γ A} : Var96 Γ A -> Tm96 Γ A
 := fun x Tm96 var96 lam app =>
     var96 _ _ x.

Definition lam96 {Γ A B} : Tm96 (snoc96 Γ A) B -> Tm96 Γ (arr96 A B)
 := fun t Tm96 var96 lam96 app =>
     lam96 _ _ _ (t Tm96 var96 lam96 app).

Definition app96 {Γ A B} : Tm96 Γ (arr96 A B) -> Tm96 Γ A -> Tm96 Γ B
 := fun t u Tm96 var96 lam96 app96 =>
     app96 _ _ _
         (t Tm96 var96 lam96 app96)
         (u Tm96 var96 lam96 app96).

Definition v096 {Γ A} : Tm96 (snoc96 Γ A) A
 := var96 vz96.

Definition v196 {Γ A B} : Tm96 (snoc96 (snoc96 Γ A) B) A
 := var96 (vs96 vz96).

Definition v296 {Γ A B C} : Tm96 (snoc96 (snoc96 (snoc96 Γ A) B) C) A
 := var96 (vs96 (vs96 vz96)).

Definition v396 {Γ A B C D} : Tm96 (snoc96 (snoc96 (snoc96 (snoc96 Γ A) B) C) D) A
 := var96 (vs96 (vs96 (vs96 vz96))).

Definition v496 {Γ A B C D E} : Tm96 (snoc96 (snoc96 (snoc96 (snoc96 (snoc96 Γ A) B) C) D) E) A
 := var96 (vs96 (vs96 (vs96 (vs96 vz96)))).

Definition test96 {Γ A} : Tm96 Γ (arr96 (arr96 A A) (arr96 A A))
 := lam96 (lam96 (app96 v196 (app96 v196 (app96 v196 (app96 v196 (app96 v196 (app96 v196 v096))))))).


Definition Ty97 : Set
 := forall (Ty97 : Set)
      (base   : Ty97)
      (arr : Ty97 -> Ty97 -> Ty97)
    , Ty97.

Definition base97 : Ty97 := fun _ base97 _ => base97.

Definition arr97 : Ty97 -> Ty97 -> Ty97
 := fun A B Ty97 base97 arr97 =>
     arr97 (A Ty97 base97 arr97) (B Ty97 base97 arr97).

Definition Con97 : Set
 := forall (Con97  : Set)
      (nil  : Con97)
      (snoc : Con97 -> Ty97 -> Con97)
    , Con97.

Definition nil97 : Con97
 := fun Con97 nil97 snoc => nil97.

Definition snoc97 : Con97 -> Ty97 -> Con97
 := fun Γ A Con97 nil97 snoc97 => snoc97 (Γ Con97 nil97 snoc97) A.

Definition Var97 : Con97 -> Ty97 -> Set
 := fun Γ A =>
   forall (Var97 : Con97 -> Ty97 -> Set)
     (vz  : forall Γ A, Var97 (snoc97 Γ A) A)
     (vs  : forall Γ B A, Var97 Γ A -> Var97 (snoc97 Γ B) A)
   , Var97 Γ A.

Definition vz97 {Γ A} : Var97 (snoc97 Γ A) A
 := fun Var97 vz97 vs => vz97 _ _.

Definition vs97 {Γ B A} : Var97 Γ A -> Var97 (snoc97 Γ B) A
 := fun x Var97 vz97 vs97 => vs97 _ _ _ (x Var97 vz97 vs97).

Definition Tm97 : Con97 -> Ty97 -> Set
 := fun Γ A =>
   forall (Tm97  : Con97 -> Ty97 -> Set)
     (var   : forall Γ A     , Var97 Γ A -> Tm97 Γ A)
     (lam   : forall Γ A B   , Tm97 (snoc97 Γ A) B -> Tm97 Γ (arr97 A B))
     (app   : forall Γ A B   , Tm97 Γ (arr97 A B) -> Tm97 Γ A -> Tm97 Γ B)
   , Tm97 Γ A.

Definition var97 {Γ A} : Var97 Γ A -> Tm97 Γ A
 := fun x Tm97 var97 lam app =>
     var97 _ _ x.

Definition lam97 {Γ A B} : Tm97 (snoc97 Γ A) B -> Tm97 Γ (arr97 A B)
 := fun t Tm97 var97 lam97 app =>
     lam97 _ _ _ (t Tm97 var97 lam97 app).

Definition app97 {Γ A B} : Tm97 Γ (arr97 A B) -> Tm97 Γ A -> Tm97 Γ B
 := fun t u Tm97 var97 lam97 app97 =>
     app97 _ _ _
         (t Tm97 var97 lam97 app97)
         (u Tm97 var97 lam97 app97).

Definition v097 {Γ A} : Tm97 (snoc97 Γ A) A
 := var97 vz97.

Definition v197 {Γ A B} : Tm97 (snoc97 (snoc97 Γ A) B) A
 := var97 (vs97 vz97).

Definition v297 {Γ A B C} : Tm97 (snoc97 (snoc97 (snoc97 Γ A) B) C) A
 := var97 (vs97 (vs97 vz97)).

Definition v397 {Γ A B C D} : Tm97 (snoc97 (snoc97 (snoc97 (snoc97 Γ A) B) C) D) A
 := var97 (vs97 (vs97 (vs97 vz97))).

Definition v497 {Γ A B C D E} : Tm97 (snoc97 (snoc97 (snoc97 (snoc97 (snoc97 Γ A) B) C) D) E) A
 := var97 (vs97 (vs97 (vs97 (vs97 vz97)))).

Definition test97 {Γ A} : Tm97 Γ (arr97 (arr97 A A) (arr97 A A))
 := lam97 (lam97 (app97 v197 (app97 v197 (app97 v197 (app97 v197 (app97 v197 (app97 v197 v097))))))).


Definition Ty98 : Set
 := forall (Ty98 : Set)
      (base   : Ty98)
      (arr : Ty98 -> Ty98 -> Ty98)
    , Ty98.

Definition base98 : Ty98 := fun _ base98 _ => base98.

Definition arr98 : Ty98 -> Ty98 -> Ty98
 := fun A B Ty98 base98 arr98 =>
     arr98 (A Ty98 base98 arr98) (B Ty98 base98 arr98).

Definition Con98 : Set
 := forall (Con98  : Set)
      (nil  : Con98)
      (snoc : Con98 -> Ty98 -> Con98)
    , Con98.

Definition nil98 : Con98
 := fun Con98 nil98 snoc => nil98.

Definition snoc98 : Con98 -> Ty98 -> Con98
 := fun Γ A Con98 nil98 snoc98 => snoc98 (Γ Con98 nil98 snoc98) A.

Definition Var98 : Con98 -> Ty98 -> Set
 := fun Γ A =>
   forall (Var98 : Con98 -> Ty98 -> Set)
     (vz  : forall Γ A, Var98 (snoc98 Γ A) A)
     (vs  : forall Γ B A, Var98 Γ A -> Var98 (snoc98 Γ B) A)
   , Var98 Γ A.

Definition vz98 {Γ A} : Var98 (snoc98 Γ A) A
 := fun Var98 vz98 vs => vz98 _ _.

Definition vs98 {Γ B A} : Var98 Γ A -> Var98 (snoc98 Γ B) A
 := fun x Var98 vz98 vs98 => vs98 _ _ _ (x Var98 vz98 vs98).

Definition Tm98 : Con98 -> Ty98 -> Set
 := fun Γ A =>
   forall (Tm98  : Con98 -> Ty98 -> Set)
     (var   : forall Γ A     , Var98 Γ A -> Tm98 Γ A)
     (lam   : forall Γ A B   , Tm98 (snoc98 Γ A) B -> Tm98 Γ (arr98 A B))
     (app   : forall Γ A B   , Tm98 Γ (arr98 A B) -> Tm98 Γ A -> Tm98 Γ B)
   , Tm98 Γ A.

Definition var98 {Γ A} : Var98 Γ A -> Tm98 Γ A
 := fun x Tm98 var98 lam app =>
     var98 _ _ x.

Definition lam98 {Γ A B} : Tm98 (snoc98 Γ A) B -> Tm98 Γ (arr98 A B)
 := fun t Tm98 var98 lam98 app =>
     lam98 _ _ _ (t Tm98 var98 lam98 app).

Definition app98 {Γ A B} : Tm98 Γ (arr98 A B) -> Tm98 Γ A -> Tm98 Γ B
 := fun t u Tm98 var98 lam98 app98 =>
     app98 _ _ _
         (t Tm98 var98 lam98 app98)
         (u Tm98 var98 lam98 app98).

Definition v098 {Γ A} : Tm98 (snoc98 Γ A) A
 := var98 vz98.

Definition v198 {Γ A B} : Tm98 (snoc98 (snoc98 Γ A) B) A
 := var98 (vs98 vz98).

Definition v298 {Γ A B C} : Tm98 (snoc98 (snoc98 (snoc98 Γ A) B) C) A
 := var98 (vs98 (vs98 vz98)).

Definition v398 {Γ A B C D} : Tm98 (snoc98 (snoc98 (snoc98 (snoc98 Γ A) B) C) D) A
 := var98 (vs98 (vs98 (vs98 vz98))).

Definition v498 {Γ A B C D E} : Tm98 (snoc98 (snoc98 (snoc98 (snoc98 (snoc98 Γ A) B) C) D) E) A
 := var98 (vs98 (vs98 (vs98 (vs98 vz98)))).

Definition test98 {Γ A} : Tm98 Γ (arr98 (arr98 A A) (arr98 A A))
 := lam98 (lam98 (app98 v198 (app98 v198 (app98 v198 (app98 v198 (app98 v198 (app98 v198 v098))))))).


Definition Ty99 : Set
 := forall (Ty99 : Set)
      (base   : Ty99)
      (arr : Ty99 -> Ty99 -> Ty99)
    , Ty99.

Definition base99 : Ty99 := fun _ base99 _ => base99.

Definition arr99 : Ty99 -> Ty99 -> Ty99
 := fun A B Ty99 base99 arr99 =>
     arr99 (A Ty99 base99 arr99) (B Ty99 base99 arr99).

Definition Con99 : Set
 := forall (Con99  : Set)
      (nil  : Con99)
      (snoc : Con99 -> Ty99 -> Con99)
    , Con99.

Definition nil99 : Con99
 := fun Con99 nil99 snoc => nil99.

Definition snoc99 : Con99 -> Ty99 -> Con99
 := fun Γ A Con99 nil99 snoc99 => snoc99 (Γ Con99 nil99 snoc99) A.

Definition Var99 : Con99 -> Ty99 -> Set
 := fun Γ A =>
   forall (Var99 : Con99 -> Ty99 -> Set)
     (vz  : forall Γ A, Var99 (snoc99 Γ A) A)
     (vs  : forall Γ B A, Var99 Γ A -> Var99 (snoc99 Γ B) A)
   , Var99 Γ A.

Definition vz99 {Γ A} : Var99 (snoc99 Γ A) A
 := fun Var99 vz99 vs => vz99 _ _.

Definition vs99 {Γ B A} : Var99 Γ A -> Var99 (snoc99 Γ B) A
 := fun x Var99 vz99 vs99 => vs99 _ _ _ (x Var99 vz99 vs99).

Definition Tm99 : Con99 -> Ty99 -> Set
 := fun Γ A =>
   forall (Tm99  : Con99 -> Ty99 -> Set)
     (var   : forall Γ A     , Var99 Γ A -> Tm99 Γ A)
     (lam   : forall Γ A B   , Tm99 (snoc99 Γ A) B -> Tm99 Γ (arr99 A B))
     (app   : forall Γ A B   , Tm99 Γ (arr99 A B) -> Tm99 Γ A -> Tm99 Γ B)
   , Tm99 Γ A.

Definition var99 {Γ A} : Var99 Γ A -> Tm99 Γ A
 := fun x Tm99 var99 lam app =>
     var99 _ _ x.

Definition lam99 {Γ A B} : Tm99 (snoc99 Γ A) B -> Tm99 Γ (arr99 A B)
 := fun t Tm99 var99 lam99 app =>
     lam99 _ _ _ (t Tm99 var99 lam99 app).

Definition app99 {Γ A B} : Tm99 Γ (arr99 A B) -> Tm99 Γ A -> Tm99 Γ B
 := fun t u Tm99 var99 lam99 app99 =>
     app99 _ _ _
         (t Tm99 var99 lam99 app99)
         (u Tm99 var99 lam99 app99).

Definition v099 {Γ A} : Tm99 (snoc99 Γ A) A
 := var99 vz99.

Definition v199 {Γ A B} : Tm99 (snoc99 (snoc99 Γ A) B) A
 := var99 (vs99 vz99).

Definition v299 {Γ A B C} : Tm99 (snoc99 (snoc99 (snoc99 Γ A) B) C) A
 := var99 (vs99 (vs99 vz99)).

Definition v399 {Γ A B C D} : Tm99 (snoc99 (snoc99 (snoc99 (snoc99 Γ A) B) C) D) A
 := var99 (vs99 (vs99 (vs99 vz99))).

Definition v499 {Γ A B C D E} : Tm99 (snoc99 (snoc99 (snoc99 (snoc99 (snoc99 Γ A) B) C) D) E) A
 := var99 (vs99 (vs99 (vs99 (vs99 vz99)))).

Definition test99 {Γ A} : Tm99 Γ (arr99 (arr99 A A) (arr99 A A))
 := lam99 (lam99 (app99 v199 (app99 v199 (app99 v199 (app99 v199 (app99 v199 (app99 v199 v099))))))).


Definition Ty100 : Set
 := forall (Ty100 : Set)
      (base   : Ty100)
      (arr : Ty100 -> Ty100 -> Ty100)
    , Ty100.

Definition base100 : Ty100 := fun _ base100 _ => base100.

Definition arr100 : Ty100 -> Ty100 -> Ty100
 := fun A B Ty100 base100 arr100 =>
     arr100 (A Ty100 base100 arr100) (B Ty100 base100 arr100).

Definition Con100 : Set
 := forall (Con100  : Set)
      (nil  : Con100)
      (snoc : Con100 -> Ty100 -> Con100)
    , Con100.

Definition nil100 : Con100
 := fun Con100 nil100 snoc => nil100.

Definition snoc100 : Con100 -> Ty100 -> Con100
 := fun Γ A Con100 nil100 snoc100 => snoc100 (Γ Con100 nil100 snoc100) A.

Definition Var100 : Con100 -> Ty100 -> Set
 := fun Γ A =>
   forall (Var100 : Con100 -> Ty100 -> Set)
     (vz  : forall Γ A, Var100 (snoc100 Γ A) A)
     (vs  : forall Γ B A, Var100 Γ A -> Var100 (snoc100 Γ B) A)
   , Var100 Γ A.

Definition vz100 {Γ A} : Var100 (snoc100 Γ A) A
 := fun Var100 vz100 vs => vz100 _ _.

Definition vs100 {Γ B A} : Var100 Γ A -> Var100 (snoc100 Γ B) A
 := fun x Var100 vz100 vs100 => vs100 _ _ _ (x Var100 vz100 vs100).

Definition Tm100 : Con100 -> Ty100 -> Set
 := fun Γ A =>
   forall (Tm100  : Con100 -> Ty100 -> Set)
     (var   : forall Γ A     , Var100 Γ A -> Tm100 Γ A)
     (lam   : forall Γ A B   , Tm100 (snoc100 Γ A) B -> Tm100 Γ (arr100 A B))
     (app   : forall Γ A B   , Tm100 Γ (arr100 A B) -> Tm100 Γ A -> Tm100 Γ B)
   , Tm100 Γ A.

Definition var100 {Γ A} : Var100 Γ A -> Tm100 Γ A
 := fun x Tm100 var100 lam app =>
     var100 _ _ x.

Definition lam100 {Γ A B} : Tm100 (snoc100 Γ A) B -> Tm100 Γ (arr100 A B)
 := fun t Tm100 var100 lam100 app =>
     lam100 _ _ _ (t Tm100 var100 lam100 app).

Definition app100 {Γ A B} : Tm100 Γ (arr100 A B) -> Tm100 Γ A -> Tm100 Γ B
 := fun t u Tm100 var100 lam100 app100 =>
     app100 _ _ _
         (t Tm100 var100 lam100 app100)
         (u Tm100 var100 lam100 app100).

Definition v0100 {Γ A} : Tm100 (snoc100 Γ A) A
 := var100 vz100.

Definition v1100 {Γ A B} : Tm100 (snoc100 (snoc100 Γ A) B) A
 := var100 (vs100 vz100).

Definition v2100 {Γ A B C} : Tm100 (snoc100 (snoc100 (snoc100 Γ A) B) C) A
 := var100 (vs100 (vs100 vz100)).

Definition v3100 {Γ A B C D} : Tm100 (snoc100 (snoc100 (snoc100 (snoc100 Γ A) B) C) D) A
 := var100 (vs100 (vs100 (vs100 vz100))).

Definition v4100 {Γ A B C D E} : Tm100 (snoc100 (snoc100 (snoc100 (snoc100 (snoc100 Γ A) B) C) D) E) A
 := var100 (vs100 (vs100 (vs100 (vs100 vz100)))).

Definition test100 {Γ A} : Tm100 Γ (arr100 (arr100 A A) (arr100 A A))
 := lam100 (lam100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 v0100))))))).


Definition Ty101 : Set
 := forall (Ty101 : Set)
      (base   : Ty101)
      (arr : Ty101 -> Ty101 -> Ty101)
    , Ty101.

Definition base101 : Ty101 := fun _ base101 _ => base101.

Definition arr101 : Ty101 -> Ty101 -> Ty101
 := fun A B Ty101 base101 arr101 =>
     arr101 (A Ty101 base101 arr101) (B Ty101 base101 arr101).

Definition Con101 : Set
 := forall (Con101  : Set)
      (nil  : Con101)
      (snoc : Con101 -> Ty101 -> Con101)
    , Con101.

Definition nil101 : Con101
 := fun Con101 nil101 snoc => nil101.

Definition snoc101 : Con101 -> Ty101 -> Con101
 := fun Γ A Con101 nil101 snoc101 => snoc101 (Γ Con101 nil101 snoc101) A.

Definition Var101 : Con101 -> Ty101 -> Set
 := fun Γ A =>
   forall (Var101 : Con101 -> Ty101 -> Set)
     (vz  : forall Γ A, Var101 (snoc101 Γ A) A)
     (vs  : forall Γ B A, Var101 Γ A -> Var101 (snoc101 Γ B) A)
   , Var101 Γ A.

Definition vz101 {Γ A} : Var101 (snoc101 Γ A) A
 := fun Var101 vz101 vs => vz101 _ _.

Definition vs101 {Γ B A} : Var101 Γ A -> Var101 (snoc101 Γ B) A
 := fun x Var101 vz101 vs101 => vs101 _ _ _ (x Var101 vz101 vs101).

Definition Tm101 : Con101 -> Ty101 -> Set
 := fun Γ A =>
   forall (Tm101  : Con101 -> Ty101 -> Set)
     (var   : forall Γ A     , Var101 Γ A -> Tm101 Γ A)
     (lam   : forall Γ A B   , Tm101 (snoc101 Γ A) B -> Tm101 Γ (arr101 A B))
     (app   : forall Γ A B   , Tm101 Γ (arr101 A B) -> Tm101 Γ A -> Tm101 Γ B)
   , Tm101 Γ A.

Definition var101 {Γ A} : Var101 Γ A -> Tm101 Γ A
 := fun x Tm101 var101 lam app =>
     var101 _ _ x.

Definition lam101 {Γ A B} : Tm101 (snoc101 Γ A) B -> Tm101 Γ (arr101 A B)
 := fun t Tm101 var101 lam101 app =>
     lam101 _ _ _ (t Tm101 var101 lam101 app).

Definition app101 {Γ A B} : Tm101 Γ (arr101 A B) -> Tm101 Γ A -> Tm101 Γ B
 := fun t u Tm101 var101 lam101 app101 =>
     app101 _ _ _
         (t Tm101 var101 lam101 app101)
         (u Tm101 var101 lam101 app101).

Definition v0101 {Γ A} : Tm101 (snoc101 Γ A) A
 := var101 vz101.

Definition v1101 {Γ A B} : Tm101 (snoc101 (snoc101 Γ A) B) A
 := var101 (vs101 vz101).

Definition v2101 {Γ A B C} : Tm101 (snoc101 (snoc101 (snoc101 Γ A) B) C) A
 := var101 (vs101 (vs101 vz101)).

Definition v3101 {Γ A B C D} : Tm101 (snoc101 (snoc101 (snoc101 (snoc101 Γ A) B) C) D) A
 := var101 (vs101 (vs101 (vs101 vz101))).

Definition v4101 {Γ A B C D E} : Tm101 (snoc101 (snoc101 (snoc101 (snoc101 (snoc101 Γ A) B) C) D) E) A
 := var101 (vs101 (vs101 (vs101 (vs101 vz101)))).

Definition test101 {Γ A} : Tm101 Γ (arr101 (arr101 A A) (arr101 A A))
 := lam101 (lam101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 v0101))))))).


Definition Ty102 : Set
 := forall (Ty102 : Set)
      (base   : Ty102)
      (arr : Ty102 -> Ty102 -> Ty102)
    , Ty102.

Definition base102 : Ty102 := fun _ base102 _ => base102.

Definition arr102 : Ty102 -> Ty102 -> Ty102
 := fun A B Ty102 base102 arr102 =>
     arr102 (A Ty102 base102 arr102) (B Ty102 base102 arr102).

Definition Con102 : Set
 := forall (Con102  : Set)
      (nil  : Con102)
      (snoc : Con102 -> Ty102 -> Con102)
    , Con102.

Definition nil102 : Con102
 := fun Con102 nil102 snoc => nil102.

Definition snoc102 : Con102 -> Ty102 -> Con102
 := fun Γ A Con102 nil102 snoc102 => snoc102 (Γ Con102 nil102 snoc102) A.

Definition Var102 : Con102 -> Ty102 -> Set
 := fun Γ A =>
   forall (Var102 : Con102 -> Ty102 -> Set)
     (vz  : forall Γ A, Var102 (snoc102 Γ A) A)
     (vs  : forall Γ B A, Var102 Γ A -> Var102 (snoc102 Γ B) A)
   , Var102 Γ A.

Definition vz102 {Γ A} : Var102 (snoc102 Γ A) A
 := fun Var102 vz102 vs => vz102 _ _.

Definition vs102 {Γ B A} : Var102 Γ A -> Var102 (snoc102 Γ B) A
 := fun x Var102 vz102 vs102 => vs102 _ _ _ (x Var102 vz102 vs102).

Definition Tm102 : Con102 -> Ty102 -> Set
 := fun Γ A =>
   forall (Tm102  : Con102 -> Ty102 -> Set)
     (var   : forall Γ A     , Var102 Γ A -> Tm102 Γ A)
     (lam   : forall Γ A B   , Tm102 (snoc102 Γ A) B -> Tm102 Γ (arr102 A B))
     (app   : forall Γ A B   , Tm102 Γ (arr102 A B) -> Tm102 Γ A -> Tm102 Γ B)
   , Tm102 Γ A.

Definition var102 {Γ A} : Var102 Γ A -> Tm102 Γ A
 := fun x Tm102 var102 lam app =>
     var102 _ _ x.

Definition lam102 {Γ A B} : Tm102 (snoc102 Γ A) B -> Tm102 Γ (arr102 A B)
 := fun t Tm102 var102 lam102 app =>
     lam102 _ _ _ (t Tm102 var102 lam102 app).

Definition app102 {Γ A B} : Tm102 Γ (arr102 A B) -> Tm102 Γ A -> Tm102 Γ B
 := fun t u Tm102 var102 lam102 app102 =>
     app102 _ _ _
         (t Tm102 var102 lam102 app102)
         (u Tm102 var102 lam102 app102).

Definition v0102 {Γ A} : Tm102 (snoc102 Γ A) A
 := var102 vz102.

Definition v1102 {Γ A B} : Tm102 (snoc102 (snoc102 Γ A) B) A
 := var102 (vs102 vz102).

Definition v2102 {Γ A B C} : Tm102 (snoc102 (snoc102 (snoc102 Γ A) B) C) A
 := var102 (vs102 (vs102 vz102)).

Definition v3102 {Γ A B C D} : Tm102 (snoc102 (snoc102 (snoc102 (snoc102 Γ A) B) C) D) A
 := var102 (vs102 (vs102 (vs102 vz102))).

Definition v4102 {Γ A B C D E} : Tm102 (snoc102 (snoc102 (snoc102 (snoc102 (snoc102 Γ A) B) C) D) E) A
 := var102 (vs102 (vs102 (vs102 (vs102 vz102)))).

Definition test102 {Γ A} : Tm102 Γ (arr102 (arr102 A A) (arr102 A A))
 := lam102 (lam102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 v0102))))))).


Definition Ty103 : Set
 := forall (Ty103 : Set)
      (base   : Ty103)
      (arr : Ty103 -> Ty103 -> Ty103)
    , Ty103.

Definition base103 : Ty103 := fun _ base103 _ => base103.

Definition arr103 : Ty103 -> Ty103 -> Ty103
 := fun A B Ty103 base103 arr103 =>
     arr103 (A Ty103 base103 arr103) (B Ty103 base103 arr103).

Definition Con103 : Set
 := forall (Con103  : Set)
      (nil  : Con103)
      (snoc : Con103 -> Ty103 -> Con103)
    , Con103.

Definition nil103 : Con103
 := fun Con103 nil103 snoc => nil103.

Definition snoc103 : Con103 -> Ty103 -> Con103
 := fun Γ A Con103 nil103 snoc103 => snoc103 (Γ Con103 nil103 snoc103) A.

Definition Var103 : Con103 -> Ty103 -> Set
 := fun Γ A =>
   forall (Var103 : Con103 -> Ty103 -> Set)
     (vz  : forall Γ A, Var103 (snoc103 Γ A) A)
     (vs  : forall Γ B A, Var103 Γ A -> Var103 (snoc103 Γ B) A)
   , Var103 Γ A.

Definition vz103 {Γ A} : Var103 (snoc103 Γ A) A
 := fun Var103 vz103 vs => vz103 _ _.

Definition vs103 {Γ B A} : Var103 Γ A -> Var103 (snoc103 Γ B) A
 := fun x Var103 vz103 vs103 => vs103 _ _ _ (x Var103 vz103 vs103).

Definition Tm103 : Con103 -> Ty103 -> Set
 := fun Γ A =>
   forall (Tm103  : Con103 -> Ty103 -> Set)
     (var   : forall Γ A     , Var103 Γ A -> Tm103 Γ A)
     (lam   : forall Γ A B   , Tm103 (snoc103 Γ A) B -> Tm103 Γ (arr103 A B))
     (app   : forall Γ A B   , Tm103 Γ (arr103 A B) -> Tm103 Γ A -> Tm103 Γ B)
   , Tm103 Γ A.

Definition var103 {Γ A} : Var103 Γ A -> Tm103 Γ A
 := fun x Tm103 var103 lam app =>
     var103 _ _ x.

Definition lam103 {Γ A B} : Tm103 (snoc103 Γ A) B -> Tm103 Γ (arr103 A B)
 := fun t Tm103 var103 lam103 app =>
     lam103 _ _ _ (t Tm103 var103 lam103 app).

Definition app103 {Γ A B} : Tm103 Γ (arr103 A B) -> Tm103 Γ A -> Tm103 Γ B
 := fun t u Tm103 var103 lam103 app103 =>
     app103 _ _ _
         (t Tm103 var103 lam103 app103)
         (u Tm103 var103 lam103 app103).

Definition v0103 {Γ A} : Tm103 (snoc103 Γ A) A
 := var103 vz103.

Definition v1103 {Γ A B} : Tm103 (snoc103 (snoc103 Γ A) B) A
 := var103 (vs103 vz103).

Definition v2103 {Γ A B C} : Tm103 (snoc103 (snoc103 (snoc103 Γ A) B) C) A
 := var103 (vs103 (vs103 vz103)).

Definition v3103 {Γ A B C D} : Tm103 (snoc103 (snoc103 (snoc103 (snoc103 Γ A) B) C) D) A
 := var103 (vs103 (vs103 (vs103 vz103))).

Definition v4103 {Γ A B C D E} : Tm103 (snoc103 (snoc103 (snoc103 (snoc103 (snoc103 Γ A) B) C) D) E) A
 := var103 (vs103 (vs103 (vs103 (vs103 vz103)))).

Definition test103 {Γ A} : Tm103 Γ (arr103 (arr103 A A) (arr103 A A))
 := lam103 (lam103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 v0103))))))).


Definition Ty104 : Set
 := forall (Ty104 : Set)
      (base   : Ty104)
      (arr : Ty104 -> Ty104 -> Ty104)
    , Ty104.

Definition base104 : Ty104 := fun _ base104 _ => base104.

Definition arr104 : Ty104 -> Ty104 -> Ty104
 := fun A B Ty104 base104 arr104 =>
     arr104 (A Ty104 base104 arr104) (B Ty104 base104 arr104).

Definition Con104 : Set
 := forall (Con104  : Set)
      (nil  : Con104)
      (snoc : Con104 -> Ty104 -> Con104)
    , Con104.

Definition nil104 : Con104
 := fun Con104 nil104 snoc => nil104.

Definition snoc104 : Con104 -> Ty104 -> Con104
 := fun Γ A Con104 nil104 snoc104 => snoc104 (Γ Con104 nil104 snoc104) A.

Definition Var104 : Con104 -> Ty104 -> Set
 := fun Γ A =>
   forall (Var104 : Con104 -> Ty104 -> Set)
     (vz  : forall Γ A, Var104 (snoc104 Γ A) A)
     (vs  : forall Γ B A, Var104 Γ A -> Var104 (snoc104 Γ B) A)
   , Var104 Γ A.

Definition vz104 {Γ A} : Var104 (snoc104 Γ A) A
 := fun Var104 vz104 vs => vz104 _ _.

Definition vs104 {Γ B A} : Var104 Γ A -> Var104 (snoc104 Γ B) A
 := fun x Var104 vz104 vs104 => vs104 _ _ _ (x Var104 vz104 vs104).

Definition Tm104 : Con104 -> Ty104 -> Set
 := fun Γ A =>
   forall (Tm104  : Con104 -> Ty104 -> Set)
     (var   : forall Γ A     , Var104 Γ A -> Tm104 Γ A)
     (lam   : forall Γ A B   , Tm104 (snoc104 Γ A) B -> Tm104 Γ (arr104 A B))
     (app   : forall Γ A B   , Tm104 Γ (arr104 A B) -> Tm104 Γ A -> Tm104 Γ B)
   , Tm104 Γ A.

Definition var104 {Γ A} : Var104 Γ A -> Tm104 Γ A
 := fun x Tm104 var104 lam app =>
     var104 _ _ x.

Definition lam104 {Γ A B} : Tm104 (snoc104 Γ A) B -> Tm104 Γ (arr104 A B)
 := fun t Tm104 var104 lam104 app =>
     lam104 _ _ _ (t Tm104 var104 lam104 app).

Definition app104 {Γ A B} : Tm104 Γ (arr104 A B) -> Tm104 Γ A -> Tm104 Γ B
 := fun t u Tm104 var104 lam104 app104 =>
     app104 _ _ _
         (t Tm104 var104 lam104 app104)
         (u Tm104 var104 lam104 app104).

Definition v0104 {Γ A} : Tm104 (snoc104 Γ A) A
 := var104 vz104.

Definition v1104 {Γ A B} : Tm104 (snoc104 (snoc104 Γ A) B) A
 := var104 (vs104 vz104).

Definition v2104 {Γ A B C} : Tm104 (snoc104 (snoc104 (snoc104 Γ A) B) C) A
 := var104 (vs104 (vs104 vz104)).

Definition v3104 {Γ A B C D} : Tm104 (snoc104 (snoc104 (snoc104 (snoc104 Γ A) B) C) D) A
 := var104 (vs104 (vs104 (vs104 vz104))).

Definition v4104 {Γ A B C D E} : Tm104 (snoc104 (snoc104 (snoc104 (snoc104 (snoc104 Γ A) B) C) D) E) A
 := var104 (vs104 (vs104 (vs104 (vs104 vz104)))).

Definition test104 {Γ A} : Tm104 Γ (arr104 (arr104 A A) (arr104 A A))
 := lam104 (lam104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 v0104))))))).


Definition Ty105 : Set
 := forall (Ty105 : Set)
      (base   : Ty105)
      (arr : Ty105 -> Ty105 -> Ty105)
    , Ty105.

Definition base105 : Ty105 := fun _ base105 _ => base105.

Definition arr105 : Ty105 -> Ty105 -> Ty105
 := fun A B Ty105 base105 arr105 =>
     arr105 (A Ty105 base105 arr105) (B Ty105 base105 arr105).

Definition Con105 : Set
 := forall (Con105  : Set)
      (nil  : Con105)
      (snoc : Con105 -> Ty105 -> Con105)
    , Con105.

Definition nil105 : Con105
 := fun Con105 nil105 snoc => nil105.

Definition snoc105 : Con105 -> Ty105 -> Con105
 := fun Γ A Con105 nil105 snoc105 => snoc105 (Γ Con105 nil105 snoc105) A.

Definition Var105 : Con105 -> Ty105 -> Set
 := fun Γ A =>
   forall (Var105 : Con105 -> Ty105 -> Set)
     (vz  : forall Γ A, Var105 (snoc105 Γ A) A)
     (vs  : forall Γ B A, Var105 Γ A -> Var105 (snoc105 Γ B) A)
   , Var105 Γ A.

Definition vz105 {Γ A} : Var105 (snoc105 Γ A) A
 := fun Var105 vz105 vs => vz105 _ _.

Definition vs105 {Γ B A} : Var105 Γ A -> Var105 (snoc105 Γ B) A
 := fun x Var105 vz105 vs105 => vs105 _ _ _ (x Var105 vz105 vs105).

Definition Tm105 : Con105 -> Ty105 -> Set
 := fun Γ A =>
   forall (Tm105  : Con105 -> Ty105 -> Set)
     (var   : forall Γ A     , Var105 Γ A -> Tm105 Γ A)
     (lam   : forall Γ A B   , Tm105 (snoc105 Γ A) B -> Tm105 Γ (arr105 A B))
     (app   : forall Γ A B   , Tm105 Γ (arr105 A B) -> Tm105 Γ A -> Tm105 Γ B)
   , Tm105 Γ A.

Definition var105 {Γ A} : Var105 Γ A -> Tm105 Γ A
 := fun x Tm105 var105 lam app =>
     var105 _ _ x.

Definition lam105 {Γ A B} : Tm105 (snoc105 Γ A) B -> Tm105 Γ (arr105 A B)
 := fun t Tm105 var105 lam105 app =>
     lam105 _ _ _ (t Tm105 var105 lam105 app).

Definition app105 {Γ A B} : Tm105 Γ (arr105 A B) -> Tm105 Γ A -> Tm105 Γ B
 := fun t u Tm105 var105 lam105 app105 =>
     app105 _ _ _
         (t Tm105 var105 lam105 app105)
         (u Tm105 var105 lam105 app105).

Definition v0105 {Γ A} : Tm105 (snoc105 Γ A) A
 := var105 vz105.

Definition v1105 {Γ A B} : Tm105 (snoc105 (snoc105 Γ A) B) A
 := var105 (vs105 vz105).

Definition v2105 {Γ A B C} : Tm105 (snoc105 (snoc105 (snoc105 Γ A) B) C) A
 := var105 (vs105 (vs105 vz105)).

Definition v3105 {Γ A B C D} : Tm105 (snoc105 (snoc105 (snoc105 (snoc105 Γ A) B) C) D) A
 := var105 (vs105 (vs105 (vs105 vz105))).

Definition v4105 {Γ A B C D E} : Tm105 (snoc105 (snoc105 (snoc105 (snoc105 (snoc105 Γ A) B) C) D) E) A
 := var105 (vs105 (vs105 (vs105 (vs105 vz105)))).

Definition test105 {Γ A} : Tm105 Γ (arr105 (arr105 A A) (arr105 A A))
 := lam105 (lam105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 v0105))))))).


Definition Ty106 : Set
 := forall (Ty106 : Set)
      (base   : Ty106)
      (arr : Ty106 -> Ty106 -> Ty106)
    , Ty106.

Definition base106 : Ty106 := fun _ base106 _ => base106.

Definition arr106 : Ty106 -> Ty106 -> Ty106
 := fun A B Ty106 base106 arr106 =>
     arr106 (A Ty106 base106 arr106) (B Ty106 base106 arr106).

Definition Con106 : Set
 := forall (Con106  : Set)
      (nil  : Con106)
      (snoc : Con106 -> Ty106 -> Con106)
    , Con106.

Definition nil106 : Con106
 := fun Con106 nil106 snoc => nil106.

Definition snoc106 : Con106 -> Ty106 -> Con106
 := fun Γ A Con106 nil106 snoc106 => snoc106 (Γ Con106 nil106 snoc106) A.

Definition Var106 : Con106 -> Ty106 -> Set
 := fun Γ A =>
   forall (Var106 : Con106 -> Ty106 -> Set)
     (vz  : forall Γ A, Var106 (snoc106 Γ A) A)
     (vs  : forall Γ B A, Var106 Γ A -> Var106 (snoc106 Γ B) A)
   , Var106 Γ A.

Definition vz106 {Γ A} : Var106 (snoc106 Γ A) A
 := fun Var106 vz106 vs => vz106 _ _.

Definition vs106 {Γ B A} : Var106 Γ A -> Var106 (snoc106 Γ B) A
 := fun x Var106 vz106 vs106 => vs106 _ _ _ (x Var106 vz106 vs106).

Definition Tm106 : Con106 -> Ty106 -> Set
 := fun Γ A =>
   forall (Tm106  : Con106 -> Ty106 -> Set)
     (var   : forall Γ A     , Var106 Γ A -> Tm106 Γ A)
     (lam   : forall Γ A B   , Tm106 (snoc106 Γ A) B -> Tm106 Γ (arr106 A B))
     (app   : forall Γ A B   , Tm106 Γ (arr106 A B) -> Tm106 Γ A -> Tm106 Γ B)
   , Tm106 Γ A.

Definition var106 {Γ A} : Var106 Γ A -> Tm106 Γ A
 := fun x Tm106 var106 lam app =>
     var106 _ _ x.

Definition lam106 {Γ A B} : Tm106 (snoc106 Γ A) B -> Tm106 Γ (arr106 A B)
 := fun t Tm106 var106 lam106 app =>
     lam106 _ _ _ (t Tm106 var106 lam106 app).

Definition app106 {Γ A B} : Tm106 Γ (arr106 A B) -> Tm106 Γ A -> Tm106 Γ B
 := fun t u Tm106 var106 lam106 app106 =>
     app106 _ _ _
         (t Tm106 var106 lam106 app106)
         (u Tm106 var106 lam106 app106).

Definition v0106 {Γ A} : Tm106 (snoc106 Γ A) A
 := var106 vz106.

Definition v1106 {Γ A B} : Tm106 (snoc106 (snoc106 Γ A) B) A
 := var106 (vs106 vz106).

Definition v2106 {Γ A B C} : Tm106 (snoc106 (snoc106 (snoc106 Γ A) B) C) A
 := var106 (vs106 (vs106 vz106)).

Definition v3106 {Γ A B C D} : Tm106 (snoc106 (snoc106 (snoc106 (snoc106 Γ A) B) C) D) A
 := var106 (vs106 (vs106 (vs106 vz106))).

Definition v4106 {Γ A B C D E} : Tm106 (snoc106 (snoc106 (snoc106 (snoc106 (snoc106 Γ A) B) C) D) E) A
 := var106 (vs106 (vs106 (vs106 (vs106 vz106)))).

Definition test106 {Γ A} : Tm106 Γ (arr106 (arr106 A A) (arr106 A A))
 := lam106 (lam106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 v0106))))))).


Definition Ty107 : Set
 := forall (Ty107 : Set)
      (base   : Ty107)
      (arr : Ty107 -> Ty107 -> Ty107)
    , Ty107.

Definition base107 : Ty107 := fun _ base107 _ => base107.

Definition arr107 : Ty107 -> Ty107 -> Ty107
 := fun A B Ty107 base107 arr107 =>
     arr107 (A Ty107 base107 arr107) (B Ty107 base107 arr107).

Definition Con107 : Set
 := forall (Con107  : Set)
      (nil  : Con107)
      (snoc : Con107 -> Ty107 -> Con107)
    , Con107.

Definition nil107 : Con107
 := fun Con107 nil107 snoc => nil107.

Definition snoc107 : Con107 -> Ty107 -> Con107
 := fun Γ A Con107 nil107 snoc107 => snoc107 (Γ Con107 nil107 snoc107) A.

Definition Var107 : Con107 -> Ty107 -> Set
 := fun Γ A =>
   forall (Var107 : Con107 -> Ty107 -> Set)
     (vz  : forall Γ A, Var107 (snoc107 Γ A) A)
     (vs  : forall Γ B A, Var107 Γ A -> Var107 (snoc107 Γ B) A)
   , Var107 Γ A.

Definition vz107 {Γ A} : Var107 (snoc107 Γ A) A
 := fun Var107 vz107 vs => vz107 _ _.

Definition vs107 {Γ B A} : Var107 Γ A -> Var107 (snoc107 Γ B) A
 := fun x Var107 vz107 vs107 => vs107 _ _ _ (x Var107 vz107 vs107).

Definition Tm107 : Con107 -> Ty107 -> Set
 := fun Γ A =>
   forall (Tm107  : Con107 -> Ty107 -> Set)
     (var   : forall Γ A     , Var107 Γ A -> Tm107 Γ A)
     (lam   : forall Γ A B   , Tm107 (snoc107 Γ A) B -> Tm107 Γ (arr107 A B))
     (app   : forall Γ A B   , Tm107 Γ (arr107 A B) -> Tm107 Γ A -> Tm107 Γ B)
   , Tm107 Γ A.

Definition var107 {Γ A} : Var107 Γ A -> Tm107 Γ A
 := fun x Tm107 var107 lam app =>
     var107 _ _ x.

Definition lam107 {Γ A B} : Tm107 (snoc107 Γ A) B -> Tm107 Γ (arr107 A B)
 := fun t Tm107 var107 lam107 app =>
     lam107 _ _ _ (t Tm107 var107 lam107 app).

Definition app107 {Γ A B} : Tm107 Γ (arr107 A B) -> Tm107 Γ A -> Tm107 Γ B
 := fun t u Tm107 var107 lam107 app107 =>
     app107 _ _ _
         (t Tm107 var107 lam107 app107)
         (u Tm107 var107 lam107 app107).

Definition v0107 {Γ A} : Tm107 (snoc107 Γ A) A
 := var107 vz107.

Definition v1107 {Γ A B} : Tm107 (snoc107 (snoc107 Γ A) B) A
 := var107 (vs107 vz107).

Definition v2107 {Γ A B C} : Tm107 (snoc107 (snoc107 (snoc107 Γ A) B) C) A
 := var107 (vs107 (vs107 vz107)).

Definition v3107 {Γ A B C D} : Tm107 (snoc107 (snoc107 (snoc107 (snoc107 Γ A) B) C) D) A
 := var107 (vs107 (vs107 (vs107 vz107))).

Definition v4107 {Γ A B C D E} : Tm107 (snoc107 (snoc107 (snoc107 (snoc107 (snoc107 Γ A) B) C) D) E) A
 := var107 (vs107 (vs107 (vs107 (vs107 vz107)))).

Definition test107 {Γ A} : Tm107 Γ (arr107 (arr107 A A) (arr107 A A))
 := lam107 (lam107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 v0107))))))).


Definition Ty108 : Set
 := forall (Ty108 : Set)
      (base   : Ty108)
      (arr : Ty108 -> Ty108 -> Ty108)
    , Ty108.

Definition base108 : Ty108 := fun _ base108 _ => base108.

Definition arr108 : Ty108 -> Ty108 -> Ty108
 := fun A B Ty108 base108 arr108 =>
     arr108 (A Ty108 base108 arr108) (B Ty108 base108 arr108).

Definition Con108 : Set
 := forall (Con108  : Set)
      (nil  : Con108)
      (snoc : Con108 -> Ty108 -> Con108)
    , Con108.

Definition nil108 : Con108
 := fun Con108 nil108 snoc => nil108.

Definition snoc108 : Con108 -> Ty108 -> Con108
 := fun Γ A Con108 nil108 snoc108 => snoc108 (Γ Con108 nil108 snoc108) A.

Definition Var108 : Con108 -> Ty108 -> Set
 := fun Γ A =>
   forall (Var108 : Con108 -> Ty108 -> Set)
     (vz  : forall Γ A, Var108 (snoc108 Γ A) A)
     (vs  : forall Γ B A, Var108 Γ A -> Var108 (snoc108 Γ B) A)
   , Var108 Γ A.

Definition vz108 {Γ A} : Var108 (snoc108 Γ A) A
 := fun Var108 vz108 vs => vz108 _ _.

Definition vs108 {Γ B A} : Var108 Γ A -> Var108 (snoc108 Γ B) A
 := fun x Var108 vz108 vs108 => vs108 _ _ _ (x Var108 vz108 vs108).

Definition Tm108 : Con108 -> Ty108 -> Set
 := fun Γ A =>
   forall (Tm108  : Con108 -> Ty108 -> Set)
     (var   : forall Γ A     , Var108 Γ A -> Tm108 Γ A)
     (lam   : forall Γ A B   , Tm108 (snoc108 Γ A) B -> Tm108 Γ (arr108 A B))
     (app   : forall Γ A B   , Tm108 Γ (arr108 A B) -> Tm108 Γ A -> Tm108 Γ B)
   , Tm108 Γ A.

Definition var108 {Γ A} : Var108 Γ A -> Tm108 Γ A
 := fun x Tm108 var108 lam app =>
     var108 _ _ x.

Definition lam108 {Γ A B} : Tm108 (snoc108 Γ A) B -> Tm108 Γ (arr108 A B)
 := fun t Tm108 var108 lam108 app =>
     lam108 _ _ _ (t Tm108 var108 lam108 app).

Definition app108 {Γ A B} : Tm108 Γ (arr108 A B) -> Tm108 Γ A -> Tm108 Γ B
 := fun t u Tm108 var108 lam108 app108 =>
     app108 _ _ _
         (t Tm108 var108 lam108 app108)
         (u Tm108 var108 lam108 app108).

Definition v0108 {Γ A} : Tm108 (snoc108 Γ A) A
 := var108 vz108.

Definition v1108 {Γ A B} : Tm108 (snoc108 (snoc108 Γ A) B) A
 := var108 (vs108 vz108).

Definition v2108 {Γ A B C} : Tm108 (snoc108 (snoc108 (snoc108 Γ A) B) C) A
 := var108 (vs108 (vs108 vz108)).

Definition v3108 {Γ A B C D} : Tm108 (snoc108 (snoc108 (snoc108 (snoc108 Γ A) B) C) D) A
 := var108 (vs108 (vs108 (vs108 vz108))).

Definition v4108 {Γ A B C D E} : Tm108 (snoc108 (snoc108 (snoc108 (snoc108 (snoc108 Γ A) B) C) D) E) A
 := var108 (vs108 (vs108 (vs108 (vs108 vz108)))).

Definition test108 {Γ A} : Tm108 Γ (arr108 (arr108 A A) (arr108 A A))
 := lam108 (lam108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 v0108))))))).


Definition Ty109 : Set
 := forall (Ty109 : Set)
      (base   : Ty109)
      (arr : Ty109 -> Ty109 -> Ty109)
    , Ty109.

Definition base109 : Ty109 := fun _ base109 _ => base109.

Definition arr109 : Ty109 -> Ty109 -> Ty109
 := fun A B Ty109 base109 arr109 =>
     arr109 (A Ty109 base109 arr109) (B Ty109 base109 arr109).

Definition Con109 : Set
 := forall (Con109  : Set)
      (nil  : Con109)
      (snoc : Con109 -> Ty109 -> Con109)
    , Con109.

Definition nil109 : Con109
 := fun Con109 nil109 snoc => nil109.

Definition snoc109 : Con109 -> Ty109 -> Con109
 := fun Γ A Con109 nil109 snoc109 => snoc109 (Γ Con109 nil109 snoc109) A.

Definition Var109 : Con109 -> Ty109 -> Set
 := fun Γ A =>
   forall (Var109 : Con109 -> Ty109 -> Set)
     (vz  : forall Γ A, Var109 (snoc109 Γ A) A)
     (vs  : forall Γ B A, Var109 Γ A -> Var109 (snoc109 Γ B) A)
   , Var109 Γ A.

Definition vz109 {Γ A} : Var109 (snoc109 Γ A) A
 := fun Var109 vz109 vs => vz109 _ _.

Definition vs109 {Γ B A} : Var109 Γ A -> Var109 (snoc109 Γ B) A
 := fun x Var109 vz109 vs109 => vs109 _ _ _ (x Var109 vz109 vs109).

Definition Tm109 : Con109 -> Ty109 -> Set
 := fun Γ A =>
   forall (Tm109  : Con109 -> Ty109 -> Set)
     (var   : forall Γ A     , Var109 Γ A -> Tm109 Γ A)
     (lam   : forall Γ A B   , Tm109 (snoc109 Γ A) B -> Tm109 Γ (arr109 A B))
     (app   : forall Γ A B   , Tm109 Γ (arr109 A B) -> Tm109 Γ A -> Tm109 Γ B)
   , Tm109 Γ A.

Definition var109 {Γ A} : Var109 Γ A -> Tm109 Γ A
 := fun x Tm109 var109 lam app =>
     var109 _ _ x.

Definition lam109 {Γ A B} : Tm109 (snoc109 Γ A) B -> Tm109 Γ (arr109 A B)
 := fun t Tm109 var109 lam109 app =>
     lam109 _ _ _ (t Tm109 var109 lam109 app).

Definition app109 {Γ A B} : Tm109 Γ (arr109 A B) -> Tm109 Γ A -> Tm109 Γ B
 := fun t u Tm109 var109 lam109 app109 =>
     app109 _ _ _
         (t Tm109 var109 lam109 app109)
         (u Tm109 var109 lam109 app109).

Definition v0109 {Γ A} : Tm109 (snoc109 Γ A) A
 := var109 vz109.

Definition v1109 {Γ A B} : Tm109 (snoc109 (snoc109 Γ A) B) A
 := var109 (vs109 vz109).

Definition v2109 {Γ A B C} : Tm109 (snoc109 (snoc109 (snoc109 Γ A) B) C) A
 := var109 (vs109 (vs109 vz109)).

Definition v3109 {Γ A B C D} : Tm109 (snoc109 (snoc109 (snoc109 (snoc109 Γ A) B) C) D) A
 := var109 (vs109 (vs109 (vs109 vz109))).

Definition v4109 {Γ A B C D E} : Tm109 (snoc109 (snoc109 (snoc109 (snoc109 (snoc109 Γ A) B) C) D) E) A
 := var109 (vs109 (vs109 (vs109 (vs109 vz109)))).

Definition test109 {Γ A} : Tm109 Γ (arr109 (arr109 A A) (arr109 A A))
 := lam109 (lam109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 v0109))))))).


Definition Ty110 : Set
 := forall (Ty110 : Set)
      (base   : Ty110)
      (arr : Ty110 -> Ty110 -> Ty110)
    , Ty110.

Definition base110 : Ty110 := fun _ base110 _ => base110.

Definition arr110 : Ty110 -> Ty110 -> Ty110
 := fun A B Ty110 base110 arr110 =>
     arr110 (A Ty110 base110 arr110) (B Ty110 base110 arr110).

Definition Con110 : Set
 := forall (Con110  : Set)
      (nil  : Con110)
      (snoc : Con110 -> Ty110 -> Con110)
    , Con110.

Definition nil110 : Con110
 := fun Con110 nil110 snoc => nil110.

Definition snoc110 : Con110 -> Ty110 -> Con110
 := fun Γ A Con110 nil110 snoc110 => snoc110 (Γ Con110 nil110 snoc110) A.

Definition Var110 : Con110 -> Ty110 -> Set
 := fun Γ A =>
   forall (Var110 : Con110 -> Ty110 -> Set)
     (vz  : forall Γ A, Var110 (snoc110 Γ A) A)
     (vs  : forall Γ B A, Var110 Γ A -> Var110 (snoc110 Γ B) A)
   , Var110 Γ A.

Definition vz110 {Γ A} : Var110 (snoc110 Γ A) A
 := fun Var110 vz110 vs => vz110 _ _.

Definition vs110 {Γ B A} : Var110 Γ A -> Var110 (snoc110 Γ B) A
 := fun x Var110 vz110 vs110 => vs110 _ _ _ (x Var110 vz110 vs110).

Definition Tm110 : Con110 -> Ty110 -> Set
 := fun Γ A =>
   forall (Tm110  : Con110 -> Ty110 -> Set)
     (var   : forall Γ A     , Var110 Γ A -> Tm110 Γ A)
     (lam   : forall Γ A B   , Tm110 (snoc110 Γ A) B -> Tm110 Γ (arr110 A B))
     (app   : forall Γ A B   , Tm110 Γ (arr110 A B) -> Tm110 Γ A -> Tm110 Γ B)
   , Tm110 Γ A.

Definition var110 {Γ A} : Var110 Γ A -> Tm110 Γ A
 := fun x Tm110 var110 lam app =>
     var110 _ _ x.

Definition lam110 {Γ A B} : Tm110 (snoc110 Γ A) B -> Tm110 Γ (arr110 A B)
 := fun t Tm110 var110 lam110 app =>
     lam110 _ _ _ (t Tm110 var110 lam110 app).

Definition app110 {Γ A B} : Tm110 Γ (arr110 A B) -> Tm110 Γ A -> Tm110 Γ B
 := fun t u Tm110 var110 lam110 app110 =>
     app110 _ _ _
         (t Tm110 var110 lam110 app110)
         (u Tm110 var110 lam110 app110).

Definition v0110 {Γ A} : Tm110 (snoc110 Γ A) A
 := var110 vz110.

Definition v1110 {Γ A B} : Tm110 (snoc110 (snoc110 Γ A) B) A
 := var110 (vs110 vz110).

Definition v2110 {Γ A B C} : Tm110 (snoc110 (snoc110 (snoc110 Γ A) B) C) A
 := var110 (vs110 (vs110 vz110)).

Definition v3110 {Γ A B C D} : Tm110 (snoc110 (snoc110 (snoc110 (snoc110 Γ A) B) C) D) A
 := var110 (vs110 (vs110 (vs110 vz110))).

Definition v4110 {Γ A B C D E} : Tm110 (snoc110 (snoc110 (snoc110 (snoc110 (snoc110 Γ A) B) C) D) E) A
 := var110 (vs110 (vs110 (vs110 (vs110 vz110)))).

Definition test110 {Γ A} : Tm110 Γ (arr110 (arr110 A A) (arr110 A A))
 := lam110 (lam110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 v0110))))))).


Definition Ty111 : Set
 := forall (Ty111 : Set)
      (base   : Ty111)
      (arr : Ty111 -> Ty111 -> Ty111)
    , Ty111.

Definition base111 : Ty111 := fun _ base111 _ => base111.

Definition arr111 : Ty111 -> Ty111 -> Ty111
 := fun A B Ty111 base111 arr111 =>
     arr111 (A Ty111 base111 arr111) (B Ty111 base111 arr111).

Definition Con111 : Set
 := forall (Con111  : Set)
      (nil  : Con111)
      (snoc : Con111 -> Ty111 -> Con111)
    , Con111.

Definition nil111 : Con111
 := fun Con111 nil111 snoc => nil111.

Definition snoc111 : Con111 -> Ty111 -> Con111
 := fun Γ A Con111 nil111 snoc111 => snoc111 (Γ Con111 nil111 snoc111) A.

Definition Var111 : Con111 -> Ty111 -> Set
 := fun Γ A =>
   forall (Var111 : Con111 -> Ty111 -> Set)
     (vz  : forall Γ A, Var111 (snoc111 Γ A) A)
     (vs  : forall Γ B A, Var111 Γ A -> Var111 (snoc111 Γ B) A)
   , Var111 Γ A.

Definition vz111 {Γ A} : Var111 (snoc111 Γ A) A
 := fun Var111 vz111 vs => vz111 _ _.

Definition vs111 {Γ B A} : Var111 Γ A -> Var111 (snoc111 Γ B) A
 := fun x Var111 vz111 vs111 => vs111 _ _ _ (x Var111 vz111 vs111).

Definition Tm111 : Con111 -> Ty111 -> Set
 := fun Γ A =>
   forall (Tm111  : Con111 -> Ty111 -> Set)
     (var   : forall Γ A     , Var111 Γ A -> Tm111 Γ A)
     (lam   : forall Γ A B   , Tm111 (snoc111 Γ A) B -> Tm111 Γ (arr111 A B))
     (app   : forall Γ A B   , Tm111 Γ (arr111 A B) -> Tm111 Γ A -> Tm111 Γ B)
   , Tm111 Γ A.

Definition var111 {Γ A} : Var111 Γ A -> Tm111 Γ A
 := fun x Tm111 var111 lam app =>
     var111 _ _ x.

Definition lam111 {Γ A B} : Tm111 (snoc111 Γ A) B -> Tm111 Γ (arr111 A B)
 := fun t Tm111 var111 lam111 app =>
     lam111 _ _ _ (t Tm111 var111 lam111 app).

Definition app111 {Γ A B} : Tm111 Γ (arr111 A B) -> Tm111 Γ A -> Tm111 Γ B
 := fun t u Tm111 var111 lam111 app111 =>
     app111 _ _ _
         (t Tm111 var111 lam111 app111)
         (u Tm111 var111 lam111 app111).

Definition v0111 {Γ A} : Tm111 (snoc111 Γ A) A
 := var111 vz111.

Definition v1111 {Γ A B} : Tm111 (snoc111 (snoc111 Γ A) B) A
 := var111 (vs111 vz111).

Definition v2111 {Γ A B C} : Tm111 (snoc111 (snoc111 (snoc111 Γ A) B) C) A
 := var111 (vs111 (vs111 vz111)).

Definition v3111 {Γ A B C D} : Tm111 (snoc111 (snoc111 (snoc111 (snoc111 Γ A) B) C) D) A
 := var111 (vs111 (vs111 (vs111 vz111))).

Definition v4111 {Γ A B C D E} : Tm111 (snoc111 (snoc111 (snoc111 (snoc111 (snoc111 Γ A) B) C) D) E) A
 := var111 (vs111 (vs111 (vs111 (vs111 vz111)))).

Definition test111 {Γ A} : Tm111 Γ (arr111 (arr111 A A) (arr111 A A))
 := lam111 (lam111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 v0111))))))).


Definition Ty112 : Set
 := forall (Ty112 : Set)
      (base   : Ty112)
      (arr : Ty112 -> Ty112 -> Ty112)
    , Ty112.

Definition base112 : Ty112 := fun _ base112 _ => base112.

Definition arr112 : Ty112 -> Ty112 -> Ty112
 := fun A B Ty112 base112 arr112 =>
     arr112 (A Ty112 base112 arr112) (B Ty112 base112 arr112).

Definition Con112 : Set
 := forall (Con112  : Set)
      (nil  : Con112)
      (snoc : Con112 -> Ty112 -> Con112)
    , Con112.

Definition nil112 : Con112
 := fun Con112 nil112 snoc => nil112.

Definition snoc112 : Con112 -> Ty112 -> Con112
 := fun Γ A Con112 nil112 snoc112 => snoc112 (Γ Con112 nil112 snoc112) A.

Definition Var112 : Con112 -> Ty112 -> Set
 := fun Γ A =>
   forall (Var112 : Con112 -> Ty112 -> Set)
     (vz  : forall Γ A, Var112 (snoc112 Γ A) A)
     (vs  : forall Γ B A, Var112 Γ A -> Var112 (snoc112 Γ B) A)
   , Var112 Γ A.

Definition vz112 {Γ A} : Var112 (snoc112 Γ A) A
 := fun Var112 vz112 vs => vz112 _ _.

Definition vs112 {Γ B A} : Var112 Γ A -> Var112 (snoc112 Γ B) A
 := fun x Var112 vz112 vs112 => vs112 _ _ _ (x Var112 vz112 vs112).

Definition Tm112 : Con112 -> Ty112 -> Set
 := fun Γ A =>
   forall (Tm112  : Con112 -> Ty112 -> Set)
     (var   : forall Γ A     , Var112 Γ A -> Tm112 Γ A)
     (lam   : forall Γ A B   , Tm112 (snoc112 Γ A) B -> Tm112 Γ (arr112 A B))
     (app   : forall Γ A B   , Tm112 Γ (arr112 A B) -> Tm112 Γ A -> Tm112 Γ B)
   , Tm112 Γ A.

Definition var112 {Γ A} : Var112 Γ A -> Tm112 Γ A
 := fun x Tm112 var112 lam app =>
     var112 _ _ x.

Definition lam112 {Γ A B} : Tm112 (snoc112 Γ A) B -> Tm112 Γ (arr112 A B)
 := fun t Tm112 var112 lam112 app =>
     lam112 _ _ _ (t Tm112 var112 lam112 app).

Definition app112 {Γ A B} : Tm112 Γ (arr112 A B) -> Tm112 Γ A -> Tm112 Γ B
 := fun t u Tm112 var112 lam112 app112 =>
     app112 _ _ _
         (t Tm112 var112 lam112 app112)
         (u Tm112 var112 lam112 app112).

Definition v0112 {Γ A} : Tm112 (snoc112 Γ A) A
 := var112 vz112.

Definition v1112 {Γ A B} : Tm112 (snoc112 (snoc112 Γ A) B) A
 := var112 (vs112 vz112).

Definition v2112 {Γ A B C} : Tm112 (snoc112 (snoc112 (snoc112 Γ A) B) C) A
 := var112 (vs112 (vs112 vz112)).

Definition v3112 {Γ A B C D} : Tm112 (snoc112 (snoc112 (snoc112 (snoc112 Γ A) B) C) D) A
 := var112 (vs112 (vs112 (vs112 vz112))).

Definition v4112 {Γ A B C D E} : Tm112 (snoc112 (snoc112 (snoc112 (snoc112 (snoc112 Γ A) B) C) D) E) A
 := var112 (vs112 (vs112 (vs112 (vs112 vz112)))).

Definition test112 {Γ A} : Tm112 Γ (arr112 (arr112 A A) (arr112 A A))
 := lam112 (lam112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 v0112))))))).


Definition Ty113 : Set
 := forall (Ty113 : Set)
      (base   : Ty113)
      (arr : Ty113 -> Ty113 -> Ty113)
    , Ty113.

Definition base113 : Ty113 := fun _ base113 _ => base113.

Definition arr113 : Ty113 -> Ty113 -> Ty113
 := fun A B Ty113 base113 arr113 =>
     arr113 (A Ty113 base113 arr113) (B Ty113 base113 arr113).

Definition Con113 : Set
 := forall (Con113  : Set)
      (nil  : Con113)
      (snoc : Con113 -> Ty113 -> Con113)
    , Con113.

Definition nil113 : Con113
 := fun Con113 nil113 snoc => nil113.

Definition snoc113 : Con113 -> Ty113 -> Con113
 := fun Γ A Con113 nil113 snoc113 => snoc113 (Γ Con113 nil113 snoc113) A.

Definition Var113 : Con113 -> Ty113 -> Set
 := fun Γ A =>
   forall (Var113 : Con113 -> Ty113 -> Set)
     (vz  : forall Γ A, Var113 (snoc113 Γ A) A)
     (vs  : forall Γ B A, Var113 Γ A -> Var113 (snoc113 Γ B) A)
   , Var113 Γ A.

Definition vz113 {Γ A} : Var113 (snoc113 Γ A) A
 := fun Var113 vz113 vs => vz113 _ _.

Definition vs113 {Γ B A} : Var113 Γ A -> Var113 (snoc113 Γ B) A
 := fun x Var113 vz113 vs113 => vs113 _ _ _ (x Var113 vz113 vs113).

Definition Tm113 : Con113 -> Ty113 -> Set
 := fun Γ A =>
   forall (Tm113  : Con113 -> Ty113 -> Set)
     (var   : forall Γ A     , Var113 Γ A -> Tm113 Γ A)
     (lam   : forall Γ A B   , Tm113 (snoc113 Γ A) B -> Tm113 Γ (arr113 A B))
     (app   : forall Γ A B   , Tm113 Γ (arr113 A B) -> Tm113 Γ A -> Tm113 Γ B)
   , Tm113 Γ A.

Definition var113 {Γ A} : Var113 Γ A -> Tm113 Γ A
 := fun x Tm113 var113 lam app =>
     var113 _ _ x.

Definition lam113 {Γ A B} : Tm113 (snoc113 Γ A) B -> Tm113 Γ (arr113 A B)
 := fun t Tm113 var113 lam113 app =>
     lam113 _ _ _ (t Tm113 var113 lam113 app).

Definition app113 {Γ A B} : Tm113 Γ (arr113 A B) -> Tm113 Γ A -> Tm113 Γ B
 := fun t u Tm113 var113 lam113 app113 =>
     app113 _ _ _
         (t Tm113 var113 lam113 app113)
         (u Tm113 var113 lam113 app113).

Definition v0113 {Γ A} : Tm113 (snoc113 Γ A) A
 := var113 vz113.

Definition v1113 {Γ A B} : Tm113 (snoc113 (snoc113 Γ A) B) A
 := var113 (vs113 vz113).

Definition v2113 {Γ A B C} : Tm113 (snoc113 (snoc113 (snoc113 Γ A) B) C) A
 := var113 (vs113 (vs113 vz113)).

Definition v3113 {Γ A B C D} : Tm113 (snoc113 (snoc113 (snoc113 (snoc113 Γ A) B) C) D) A
 := var113 (vs113 (vs113 (vs113 vz113))).

Definition v4113 {Γ A B C D E} : Tm113 (snoc113 (snoc113 (snoc113 (snoc113 (snoc113 Γ A) B) C) D) E) A
 := var113 (vs113 (vs113 (vs113 (vs113 vz113)))).

Definition test113 {Γ A} : Tm113 Γ (arr113 (arr113 A A) (arr113 A A))
 := lam113 (lam113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 v0113))))))).


Definition Ty114 : Set
 := forall (Ty114 : Set)
      (base   : Ty114)
      (arr : Ty114 -> Ty114 -> Ty114)
    , Ty114.

Definition base114 : Ty114 := fun _ base114 _ => base114.

Definition arr114 : Ty114 -> Ty114 -> Ty114
 := fun A B Ty114 base114 arr114 =>
     arr114 (A Ty114 base114 arr114) (B Ty114 base114 arr114).

Definition Con114 : Set
 := forall (Con114  : Set)
      (nil  : Con114)
      (snoc : Con114 -> Ty114 -> Con114)
    , Con114.

Definition nil114 : Con114
 := fun Con114 nil114 snoc => nil114.

Definition snoc114 : Con114 -> Ty114 -> Con114
 := fun Γ A Con114 nil114 snoc114 => snoc114 (Γ Con114 nil114 snoc114) A.

Definition Var114 : Con114 -> Ty114 -> Set
 := fun Γ A =>
   forall (Var114 : Con114 -> Ty114 -> Set)
     (vz  : forall Γ A, Var114 (snoc114 Γ A) A)
     (vs  : forall Γ B A, Var114 Γ A -> Var114 (snoc114 Γ B) A)
   , Var114 Γ A.

Definition vz114 {Γ A} : Var114 (snoc114 Γ A) A
 := fun Var114 vz114 vs => vz114 _ _.

Definition vs114 {Γ B A} : Var114 Γ A -> Var114 (snoc114 Γ B) A
 := fun x Var114 vz114 vs114 => vs114 _ _ _ (x Var114 vz114 vs114).

Definition Tm114 : Con114 -> Ty114 -> Set
 := fun Γ A =>
   forall (Tm114  : Con114 -> Ty114 -> Set)
     (var   : forall Γ A     , Var114 Γ A -> Tm114 Γ A)
     (lam   : forall Γ A B   , Tm114 (snoc114 Γ A) B -> Tm114 Γ (arr114 A B))
     (app   : forall Γ A B   , Tm114 Γ (arr114 A B) -> Tm114 Γ A -> Tm114 Γ B)
   , Tm114 Γ A.

Definition var114 {Γ A} : Var114 Γ A -> Tm114 Γ A
 := fun x Tm114 var114 lam app =>
     var114 _ _ x.

Definition lam114 {Γ A B} : Tm114 (snoc114 Γ A) B -> Tm114 Γ (arr114 A B)
 := fun t Tm114 var114 lam114 app =>
     lam114 _ _ _ (t Tm114 var114 lam114 app).

Definition app114 {Γ A B} : Tm114 Γ (arr114 A B) -> Tm114 Γ A -> Tm114 Γ B
 := fun t u Tm114 var114 lam114 app114 =>
     app114 _ _ _
         (t Tm114 var114 lam114 app114)
         (u Tm114 var114 lam114 app114).

Definition v0114 {Γ A} : Tm114 (snoc114 Γ A) A
 := var114 vz114.

Definition v1114 {Γ A B} : Tm114 (snoc114 (snoc114 Γ A) B) A
 := var114 (vs114 vz114).

Definition v2114 {Γ A B C} : Tm114 (snoc114 (snoc114 (snoc114 Γ A) B) C) A
 := var114 (vs114 (vs114 vz114)).

Definition v3114 {Γ A B C D} : Tm114 (snoc114 (snoc114 (snoc114 (snoc114 Γ A) B) C) D) A
 := var114 (vs114 (vs114 (vs114 vz114))).

Definition v4114 {Γ A B C D E} : Tm114 (snoc114 (snoc114 (snoc114 (snoc114 (snoc114 Γ A) B) C) D) E) A
 := var114 (vs114 (vs114 (vs114 (vs114 vz114)))).

Definition test114 {Γ A} : Tm114 Γ (arr114 (arr114 A A) (arr114 A A))
 := lam114 (lam114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 v0114))))))).


Definition Ty115 : Set
 := forall (Ty115 : Set)
      (base   : Ty115)
      (arr : Ty115 -> Ty115 -> Ty115)
    , Ty115.

Definition base115 : Ty115 := fun _ base115 _ => base115.

Definition arr115 : Ty115 -> Ty115 -> Ty115
 := fun A B Ty115 base115 arr115 =>
     arr115 (A Ty115 base115 arr115) (B Ty115 base115 arr115).

Definition Con115 : Set
 := forall (Con115  : Set)
      (nil  : Con115)
      (snoc : Con115 -> Ty115 -> Con115)
    , Con115.

Definition nil115 : Con115
 := fun Con115 nil115 snoc => nil115.

Definition snoc115 : Con115 -> Ty115 -> Con115
 := fun Γ A Con115 nil115 snoc115 => snoc115 (Γ Con115 nil115 snoc115) A.

Definition Var115 : Con115 -> Ty115 -> Set
 := fun Γ A =>
   forall (Var115 : Con115 -> Ty115 -> Set)
     (vz  : forall Γ A, Var115 (snoc115 Γ A) A)
     (vs  : forall Γ B A, Var115 Γ A -> Var115 (snoc115 Γ B) A)
   , Var115 Γ A.

Definition vz115 {Γ A} : Var115 (snoc115 Γ A) A
 := fun Var115 vz115 vs => vz115 _ _.

Definition vs115 {Γ B A} : Var115 Γ A -> Var115 (snoc115 Γ B) A
 := fun x Var115 vz115 vs115 => vs115 _ _ _ (x Var115 vz115 vs115).

Definition Tm115 : Con115 -> Ty115 -> Set
 := fun Γ A =>
   forall (Tm115  : Con115 -> Ty115 -> Set)
     (var   : forall Γ A     , Var115 Γ A -> Tm115 Γ A)
     (lam   : forall Γ A B   , Tm115 (snoc115 Γ A) B -> Tm115 Γ (arr115 A B))
     (app   : forall Γ A B   , Tm115 Γ (arr115 A B) -> Tm115 Γ A -> Tm115 Γ B)
   , Tm115 Γ A.

Definition var115 {Γ A} : Var115 Γ A -> Tm115 Γ A
 := fun x Tm115 var115 lam app =>
     var115 _ _ x.

Definition lam115 {Γ A B} : Tm115 (snoc115 Γ A) B -> Tm115 Γ (arr115 A B)
 := fun t Tm115 var115 lam115 app =>
     lam115 _ _ _ (t Tm115 var115 lam115 app).

Definition app115 {Γ A B} : Tm115 Γ (arr115 A B) -> Tm115 Γ A -> Tm115 Γ B
 := fun t u Tm115 var115 lam115 app115 =>
     app115 _ _ _
         (t Tm115 var115 lam115 app115)
         (u Tm115 var115 lam115 app115).

Definition v0115 {Γ A} : Tm115 (snoc115 Γ A) A
 := var115 vz115.

Definition v1115 {Γ A B} : Tm115 (snoc115 (snoc115 Γ A) B) A
 := var115 (vs115 vz115).

Definition v2115 {Γ A B C} : Tm115 (snoc115 (snoc115 (snoc115 Γ A) B) C) A
 := var115 (vs115 (vs115 vz115)).

Definition v3115 {Γ A B C D} : Tm115 (snoc115 (snoc115 (snoc115 (snoc115 Γ A) B) C) D) A
 := var115 (vs115 (vs115 (vs115 vz115))).

Definition v4115 {Γ A B C D E} : Tm115 (snoc115 (snoc115 (snoc115 (snoc115 (snoc115 Γ A) B) C) D) E) A
 := var115 (vs115 (vs115 (vs115 (vs115 vz115)))).

Definition test115 {Γ A} : Tm115 Γ (arr115 (arr115 A A) (arr115 A A))
 := lam115 (lam115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 v0115))))))).


Definition Ty116 : Set
 := forall (Ty116 : Set)
      (base   : Ty116)
      (arr : Ty116 -> Ty116 -> Ty116)
    , Ty116.

Definition base116 : Ty116 := fun _ base116 _ => base116.

Definition arr116 : Ty116 -> Ty116 -> Ty116
 := fun A B Ty116 base116 arr116 =>
     arr116 (A Ty116 base116 arr116) (B Ty116 base116 arr116).

Definition Con116 : Set
 := forall (Con116  : Set)
      (nil  : Con116)
      (snoc : Con116 -> Ty116 -> Con116)
    , Con116.

Definition nil116 : Con116
 := fun Con116 nil116 snoc => nil116.

Definition snoc116 : Con116 -> Ty116 -> Con116
 := fun Γ A Con116 nil116 snoc116 => snoc116 (Γ Con116 nil116 snoc116) A.

Definition Var116 : Con116 -> Ty116 -> Set
 := fun Γ A =>
   forall (Var116 : Con116 -> Ty116 -> Set)
     (vz  : forall Γ A, Var116 (snoc116 Γ A) A)
     (vs  : forall Γ B A, Var116 Γ A -> Var116 (snoc116 Γ B) A)
   , Var116 Γ A.

Definition vz116 {Γ A} : Var116 (snoc116 Γ A) A
 := fun Var116 vz116 vs => vz116 _ _.

Definition vs116 {Γ B A} : Var116 Γ A -> Var116 (snoc116 Γ B) A
 := fun x Var116 vz116 vs116 => vs116 _ _ _ (x Var116 vz116 vs116).

Definition Tm116 : Con116 -> Ty116 -> Set
 := fun Γ A =>
   forall (Tm116  : Con116 -> Ty116 -> Set)
     (var   : forall Γ A     , Var116 Γ A -> Tm116 Γ A)
     (lam   : forall Γ A B   , Tm116 (snoc116 Γ A) B -> Tm116 Γ (arr116 A B))
     (app   : forall Γ A B   , Tm116 Γ (arr116 A B) -> Tm116 Γ A -> Tm116 Γ B)
   , Tm116 Γ A.

Definition var116 {Γ A} : Var116 Γ A -> Tm116 Γ A
 := fun x Tm116 var116 lam app =>
     var116 _ _ x.

Definition lam116 {Γ A B} : Tm116 (snoc116 Γ A) B -> Tm116 Γ (arr116 A B)
 := fun t Tm116 var116 lam116 app =>
     lam116 _ _ _ (t Tm116 var116 lam116 app).

Definition app116 {Γ A B} : Tm116 Γ (arr116 A B) -> Tm116 Γ A -> Tm116 Γ B
 := fun t u Tm116 var116 lam116 app116 =>
     app116 _ _ _
         (t Tm116 var116 lam116 app116)
         (u Tm116 var116 lam116 app116).

Definition v0116 {Γ A} : Tm116 (snoc116 Γ A) A
 := var116 vz116.

Definition v1116 {Γ A B} : Tm116 (snoc116 (snoc116 Γ A) B) A
 := var116 (vs116 vz116).

Definition v2116 {Γ A B C} : Tm116 (snoc116 (snoc116 (snoc116 Γ A) B) C) A
 := var116 (vs116 (vs116 vz116)).

Definition v3116 {Γ A B C D} : Tm116 (snoc116 (snoc116 (snoc116 (snoc116 Γ A) B) C) D) A
 := var116 (vs116 (vs116 (vs116 vz116))).

Definition v4116 {Γ A B C D E} : Tm116 (snoc116 (snoc116 (snoc116 (snoc116 (snoc116 Γ A) B) C) D) E) A
 := var116 (vs116 (vs116 (vs116 (vs116 vz116)))).

Definition test116 {Γ A} : Tm116 Γ (arr116 (arr116 A A) (arr116 A A))
 := lam116 (lam116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 v0116))))))).


Definition Ty117 : Set
 := forall (Ty117 : Set)
      (base   : Ty117)
      (arr : Ty117 -> Ty117 -> Ty117)
    , Ty117.

Definition base117 : Ty117 := fun _ base117 _ => base117.

Definition arr117 : Ty117 -> Ty117 -> Ty117
 := fun A B Ty117 base117 arr117 =>
     arr117 (A Ty117 base117 arr117) (B Ty117 base117 arr117).

Definition Con117 : Set
 := forall (Con117  : Set)
      (nil  : Con117)
      (snoc : Con117 -> Ty117 -> Con117)
    , Con117.

Definition nil117 : Con117
 := fun Con117 nil117 snoc => nil117.

Definition snoc117 : Con117 -> Ty117 -> Con117
 := fun Γ A Con117 nil117 snoc117 => snoc117 (Γ Con117 nil117 snoc117) A.

Definition Var117 : Con117 -> Ty117 -> Set
 := fun Γ A =>
   forall (Var117 : Con117 -> Ty117 -> Set)
     (vz  : forall Γ A, Var117 (snoc117 Γ A) A)
     (vs  : forall Γ B A, Var117 Γ A -> Var117 (snoc117 Γ B) A)
   , Var117 Γ A.

Definition vz117 {Γ A} : Var117 (snoc117 Γ A) A
 := fun Var117 vz117 vs => vz117 _ _.

Definition vs117 {Γ B A} : Var117 Γ A -> Var117 (snoc117 Γ B) A
 := fun x Var117 vz117 vs117 => vs117 _ _ _ (x Var117 vz117 vs117).

Definition Tm117 : Con117 -> Ty117 -> Set
 := fun Γ A =>
   forall (Tm117  : Con117 -> Ty117 -> Set)
     (var   : forall Γ A     , Var117 Γ A -> Tm117 Γ A)
     (lam   : forall Γ A B   , Tm117 (snoc117 Γ A) B -> Tm117 Γ (arr117 A B))
     (app   : forall Γ A B   , Tm117 Γ (arr117 A B) -> Tm117 Γ A -> Tm117 Γ B)
   , Tm117 Γ A.

Definition var117 {Γ A} : Var117 Γ A -> Tm117 Γ A
 := fun x Tm117 var117 lam app =>
     var117 _ _ x.

Definition lam117 {Γ A B} : Tm117 (snoc117 Γ A) B -> Tm117 Γ (arr117 A B)
 := fun t Tm117 var117 lam117 app =>
     lam117 _ _ _ (t Tm117 var117 lam117 app).

Definition app117 {Γ A B} : Tm117 Γ (arr117 A B) -> Tm117 Γ A -> Tm117 Γ B
 := fun t u Tm117 var117 lam117 app117 =>
     app117 _ _ _
         (t Tm117 var117 lam117 app117)
         (u Tm117 var117 lam117 app117).

Definition v0117 {Γ A} : Tm117 (snoc117 Γ A) A
 := var117 vz117.

Definition v1117 {Γ A B} : Tm117 (snoc117 (snoc117 Γ A) B) A
 := var117 (vs117 vz117).

Definition v2117 {Γ A B C} : Tm117 (snoc117 (snoc117 (snoc117 Γ A) B) C) A
 := var117 (vs117 (vs117 vz117)).

Definition v3117 {Γ A B C D} : Tm117 (snoc117 (snoc117 (snoc117 (snoc117 Γ A) B) C) D) A
 := var117 (vs117 (vs117 (vs117 vz117))).

Definition v4117 {Γ A B C D E} : Tm117 (snoc117 (snoc117 (snoc117 (snoc117 (snoc117 Γ A) B) C) D) E) A
 := var117 (vs117 (vs117 (vs117 (vs117 vz117)))).

Definition test117 {Γ A} : Tm117 Γ (arr117 (arr117 A A) (arr117 A A))
 := lam117 (lam117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 v0117))))))).


Definition Ty118 : Set
 := forall (Ty118 : Set)
      (base   : Ty118)
      (arr : Ty118 -> Ty118 -> Ty118)
    , Ty118.

Definition base118 : Ty118 := fun _ base118 _ => base118.

Definition arr118 : Ty118 -> Ty118 -> Ty118
 := fun A B Ty118 base118 arr118 =>
     arr118 (A Ty118 base118 arr118) (B Ty118 base118 arr118).

Definition Con118 : Set
 := forall (Con118  : Set)
      (nil  : Con118)
      (snoc : Con118 -> Ty118 -> Con118)
    , Con118.

Definition nil118 : Con118
 := fun Con118 nil118 snoc => nil118.

Definition snoc118 : Con118 -> Ty118 -> Con118
 := fun Γ A Con118 nil118 snoc118 => snoc118 (Γ Con118 nil118 snoc118) A.

Definition Var118 : Con118 -> Ty118 -> Set
 := fun Γ A =>
   forall (Var118 : Con118 -> Ty118 -> Set)
     (vz  : forall Γ A, Var118 (snoc118 Γ A) A)
     (vs  : forall Γ B A, Var118 Γ A -> Var118 (snoc118 Γ B) A)
   , Var118 Γ A.

Definition vz118 {Γ A} : Var118 (snoc118 Γ A) A
 := fun Var118 vz118 vs => vz118 _ _.

Definition vs118 {Γ B A} : Var118 Γ A -> Var118 (snoc118 Γ B) A
 := fun x Var118 vz118 vs118 => vs118 _ _ _ (x Var118 vz118 vs118).

Definition Tm118 : Con118 -> Ty118 -> Set
 := fun Γ A =>
   forall (Tm118  : Con118 -> Ty118 -> Set)
     (var   : forall Γ A     , Var118 Γ A -> Tm118 Γ A)
     (lam   : forall Γ A B   , Tm118 (snoc118 Γ A) B -> Tm118 Γ (arr118 A B))
     (app   : forall Γ A B   , Tm118 Γ (arr118 A B) -> Tm118 Γ A -> Tm118 Γ B)
   , Tm118 Γ A.

Definition var118 {Γ A} : Var118 Γ A -> Tm118 Γ A
 := fun x Tm118 var118 lam app =>
     var118 _ _ x.

Definition lam118 {Γ A B} : Tm118 (snoc118 Γ A) B -> Tm118 Γ (arr118 A B)
 := fun t Tm118 var118 lam118 app =>
     lam118 _ _ _ (t Tm118 var118 lam118 app).

Definition app118 {Γ A B} : Tm118 Γ (arr118 A B) -> Tm118 Γ A -> Tm118 Γ B
 := fun t u Tm118 var118 lam118 app118 =>
     app118 _ _ _
         (t Tm118 var118 lam118 app118)
         (u Tm118 var118 lam118 app118).

Definition v0118 {Γ A} : Tm118 (snoc118 Γ A) A
 := var118 vz118.

Definition v1118 {Γ A B} : Tm118 (snoc118 (snoc118 Γ A) B) A
 := var118 (vs118 vz118).

Definition v2118 {Γ A B C} : Tm118 (snoc118 (snoc118 (snoc118 Γ A) B) C) A
 := var118 (vs118 (vs118 vz118)).

Definition v3118 {Γ A B C D} : Tm118 (snoc118 (snoc118 (snoc118 (snoc118 Γ A) B) C) D) A
 := var118 (vs118 (vs118 (vs118 vz118))).

Definition v4118 {Γ A B C D E} : Tm118 (snoc118 (snoc118 (snoc118 (snoc118 (snoc118 Γ A) B) C) D) E) A
 := var118 (vs118 (vs118 (vs118 (vs118 vz118)))).

Definition test118 {Γ A} : Tm118 Γ (arr118 (arr118 A A) (arr118 A A))
 := lam118 (lam118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 v0118))))))).


Definition Ty119 : Set
 := forall (Ty119 : Set)
      (base   : Ty119)
      (arr : Ty119 -> Ty119 -> Ty119)
    , Ty119.

Definition base119 : Ty119 := fun _ base119 _ => base119.

Definition arr119 : Ty119 -> Ty119 -> Ty119
 := fun A B Ty119 base119 arr119 =>
     arr119 (A Ty119 base119 arr119) (B Ty119 base119 arr119).

Definition Con119 : Set
 := forall (Con119  : Set)
      (nil  : Con119)
      (snoc : Con119 -> Ty119 -> Con119)
    , Con119.

Definition nil119 : Con119
 := fun Con119 nil119 snoc => nil119.

Definition snoc119 : Con119 -> Ty119 -> Con119
 := fun Γ A Con119 nil119 snoc119 => snoc119 (Γ Con119 nil119 snoc119) A.

Definition Var119 : Con119 -> Ty119 -> Set
 := fun Γ A =>
   forall (Var119 : Con119 -> Ty119 -> Set)
     (vz  : forall Γ A, Var119 (snoc119 Γ A) A)
     (vs  : forall Γ B A, Var119 Γ A -> Var119 (snoc119 Γ B) A)
   , Var119 Γ A.

Definition vz119 {Γ A} : Var119 (snoc119 Γ A) A
 := fun Var119 vz119 vs => vz119 _ _.

Definition vs119 {Γ B A} : Var119 Γ A -> Var119 (snoc119 Γ B) A
 := fun x Var119 vz119 vs119 => vs119 _ _ _ (x Var119 vz119 vs119).

Definition Tm119 : Con119 -> Ty119 -> Set
 := fun Γ A =>
   forall (Tm119  : Con119 -> Ty119 -> Set)
     (var   : forall Γ A     , Var119 Γ A -> Tm119 Γ A)
     (lam   : forall Γ A B   , Tm119 (snoc119 Γ A) B -> Tm119 Γ (arr119 A B))
     (app   : forall Γ A B   , Tm119 Γ (arr119 A B) -> Tm119 Γ A -> Tm119 Γ B)
   , Tm119 Γ A.

Definition var119 {Γ A} : Var119 Γ A -> Tm119 Γ A
 := fun x Tm119 var119 lam app =>
     var119 _ _ x.

Definition lam119 {Γ A B} : Tm119 (snoc119 Γ A) B -> Tm119 Γ (arr119 A B)
 := fun t Tm119 var119 lam119 app =>
     lam119 _ _ _ (t Tm119 var119 lam119 app).

Definition app119 {Γ A B} : Tm119 Γ (arr119 A B) -> Tm119 Γ A -> Tm119 Γ B
 := fun t u Tm119 var119 lam119 app119 =>
     app119 _ _ _
         (t Tm119 var119 lam119 app119)
         (u Tm119 var119 lam119 app119).

Definition v0119 {Γ A} : Tm119 (snoc119 Γ A) A
 := var119 vz119.

Definition v1119 {Γ A B} : Tm119 (snoc119 (snoc119 Γ A) B) A
 := var119 (vs119 vz119).

Definition v2119 {Γ A B C} : Tm119 (snoc119 (snoc119 (snoc119 Γ A) B) C) A
 := var119 (vs119 (vs119 vz119)).

Definition v3119 {Γ A B C D} : Tm119 (snoc119 (snoc119 (snoc119 (snoc119 Γ A) B) C) D) A
 := var119 (vs119 (vs119 (vs119 vz119))).

Definition v4119 {Γ A B C D E} : Tm119 (snoc119 (snoc119 (snoc119 (snoc119 (snoc119 Γ A) B) C) D) E) A
 := var119 (vs119 (vs119 (vs119 (vs119 vz119)))).

Definition test119 {Γ A} : Tm119 Γ (arr119 (arr119 A A) (arr119 A A))
 := lam119 (lam119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 v0119))))))).


Definition Ty120 : Set
 := forall (Ty120 : Set)
      (base   : Ty120)
      (arr : Ty120 -> Ty120 -> Ty120)
    , Ty120.

Definition base120 : Ty120 := fun _ base120 _ => base120.

Definition arr120 : Ty120 -> Ty120 -> Ty120
 := fun A B Ty120 base120 arr120 =>
     arr120 (A Ty120 base120 arr120) (B Ty120 base120 arr120).

Definition Con120 : Set
 := forall (Con120  : Set)
      (nil  : Con120)
      (snoc : Con120 -> Ty120 -> Con120)
    , Con120.

Definition nil120 : Con120
 := fun Con120 nil120 snoc => nil120.

Definition snoc120 : Con120 -> Ty120 -> Con120
 := fun Γ A Con120 nil120 snoc120 => snoc120 (Γ Con120 nil120 snoc120) A.

Definition Var120 : Con120 -> Ty120 -> Set
 := fun Γ A =>
   forall (Var120 : Con120 -> Ty120 -> Set)
     (vz  : forall Γ A, Var120 (snoc120 Γ A) A)
     (vs  : forall Γ B A, Var120 Γ A -> Var120 (snoc120 Γ B) A)
   , Var120 Γ A.

Definition vz120 {Γ A} : Var120 (snoc120 Γ A) A
 := fun Var120 vz120 vs => vz120 _ _.

Definition vs120 {Γ B A} : Var120 Γ A -> Var120 (snoc120 Γ B) A
 := fun x Var120 vz120 vs120 => vs120 _ _ _ (x Var120 vz120 vs120).

Definition Tm120 : Con120 -> Ty120 -> Set
 := fun Γ A =>
   forall (Tm120  : Con120 -> Ty120 -> Set)
     (var   : forall Γ A     , Var120 Γ A -> Tm120 Γ A)
     (lam   : forall Γ A B   , Tm120 (snoc120 Γ A) B -> Tm120 Γ (arr120 A B))
     (app   : forall Γ A B   , Tm120 Γ (arr120 A B) -> Tm120 Γ A -> Tm120 Γ B)
   , Tm120 Γ A.

Definition var120 {Γ A} : Var120 Γ A -> Tm120 Γ A
 := fun x Tm120 var120 lam app =>
     var120 _ _ x.

Definition lam120 {Γ A B} : Tm120 (snoc120 Γ A) B -> Tm120 Γ (arr120 A B)
 := fun t Tm120 var120 lam120 app =>
     lam120 _ _ _ (t Tm120 var120 lam120 app).

Definition app120 {Γ A B} : Tm120 Γ (arr120 A B) -> Tm120 Γ A -> Tm120 Γ B
 := fun t u Tm120 var120 lam120 app120 =>
     app120 _ _ _
         (t Tm120 var120 lam120 app120)
         (u Tm120 var120 lam120 app120).

Definition v0120 {Γ A} : Tm120 (snoc120 Γ A) A
 := var120 vz120.

Definition v1120 {Γ A B} : Tm120 (snoc120 (snoc120 Γ A) B) A
 := var120 (vs120 vz120).

Definition v2120 {Γ A B C} : Tm120 (snoc120 (snoc120 (snoc120 Γ A) B) C) A
 := var120 (vs120 (vs120 vz120)).

Definition v3120 {Γ A B C D} : Tm120 (snoc120 (snoc120 (snoc120 (snoc120 Γ A) B) C) D) A
 := var120 (vs120 (vs120 (vs120 vz120))).

Definition v4120 {Γ A B C D E} : Tm120 (snoc120 (snoc120 (snoc120 (snoc120 (snoc120 Γ A) B) C) D) E) A
 := var120 (vs120 (vs120 (vs120 (vs120 vz120)))).

Definition test120 {Γ A} : Tm120 Γ (arr120 (arr120 A A) (arr120 A A))
 := lam120 (lam120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 v0120))))))).


Definition Ty121 : Set
 := forall (Ty121 : Set)
      (base   : Ty121)
      (arr : Ty121 -> Ty121 -> Ty121)
    , Ty121.

Definition base121 : Ty121 := fun _ base121 _ => base121.

Definition arr121 : Ty121 -> Ty121 -> Ty121
 := fun A B Ty121 base121 arr121 =>
     arr121 (A Ty121 base121 arr121) (B Ty121 base121 arr121).

Definition Con121 : Set
 := forall (Con121  : Set)
      (nil  : Con121)
      (snoc : Con121 -> Ty121 -> Con121)
    , Con121.

Definition nil121 : Con121
 := fun Con121 nil121 snoc => nil121.

Definition snoc121 : Con121 -> Ty121 -> Con121
 := fun Γ A Con121 nil121 snoc121 => snoc121 (Γ Con121 nil121 snoc121) A.

Definition Var121 : Con121 -> Ty121 -> Set
 := fun Γ A =>
   forall (Var121 : Con121 -> Ty121 -> Set)
     (vz  : forall Γ A, Var121 (snoc121 Γ A) A)
     (vs  : forall Γ B A, Var121 Γ A -> Var121 (snoc121 Γ B) A)
   , Var121 Γ A.

Definition vz121 {Γ A} : Var121 (snoc121 Γ A) A
 := fun Var121 vz121 vs => vz121 _ _.

Definition vs121 {Γ B A} : Var121 Γ A -> Var121 (snoc121 Γ B) A
 := fun x Var121 vz121 vs121 => vs121 _ _ _ (x Var121 vz121 vs121).

Definition Tm121 : Con121 -> Ty121 -> Set
 := fun Γ A =>
   forall (Tm121  : Con121 -> Ty121 -> Set)
     (var   : forall Γ A     , Var121 Γ A -> Tm121 Γ A)
     (lam   : forall Γ A B   , Tm121 (snoc121 Γ A) B -> Tm121 Γ (arr121 A B))
     (app   : forall Γ A B   , Tm121 Γ (arr121 A B) -> Tm121 Γ A -> Tm121 Γ B)
   , Tm121 Γ A.

Definition var121 {Γ A} : Var121 Γ A -> Tm121 Γ A
 := fun x Tm121 var121 lam app =>
     var121 _ _ x.

Definition lam121 {Γ A B} : Tm121 (snoc121 Γ A) B -> Tm121 Γ (arr121 A B)
 := fun t Tm121 var121 lam121 app =>
     lam121 _ _ _ (t Tm121 var121 lam121 app).

Definition app121 {Γ A B} : Tm121 Γ (arr121 A B) -> Tm121 Γ A -> Tm121 Γ B
 := fun t u Tm121 var121 lam121 app121 =>
     app121 _ _ _
         (t Tm121 var121 lam121 app121)
         (u Tm121 var121 lam121 app121).

Definition v0121 {Γ A} : Tm121 (snoc121 Γ A) A
 := var121 vz121.

Definition v1121 {Γ A B} : Tm121 (snoc121 (snoc121 Γ A) B) A
 := var121 (vs121 vz121).

Definition v2121 {Γ A B C} : Tm121 (snoc121 (snoc121 (snoc121 Γ A) B) C) A
 := var121 (vs121 (vs121 vz121)).

Definition v3121 {Γ A B C D} : Tm121 (snoc121 (snoc121 (snoc121 (snoc121 Γ A) B) C) D) A
 := var121 (vs121 (vs121 (vs121 vz121))).

Definition v4121 {Γ A B C D E} : Tm121 (snoc121 (snoc121 (snoc121 (snoc121 (snoc121 Γ A) B) C) D) E) A
 := var121 (vs121 (vs121 (vs121 (vs121 vz121)))).

Definition test121 {Γ A} : Tm121 Γ (arr121 (arr121 A A) (arr121 A A))
 := lam121 (lam121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 v0121))))))).


Definition Ty122 : Set
 := forall (Ty122 : Set)
      (base   : Ty122)
      (arr : Ty122 -> Ty122 -> Ty122)
    , Ty122.

Definition base122 : Ty122 := fun _ base122 _ => base122.

Definition arr122 : Ty122 -> Ty122 -> Ty122
 := fun A B Ty122 base122 arr122 =>
     arr122 (A Ty122 base122 arr122) (B Ty122 base122 arr122).

Definition Con122 : Set
 := forall (Con122  : Set)
      (nil  : Con122)
      (snoc : Con122 -> Ty122 -> Con122)
    , Con122.

Definition nil122 : Con122
 := fun Con122 nil122 snoc => nil122.

Definition snoc122 : Con122 -> Ty122 -> Con122
 := fun Γ A Con122 nil122 snoc122 => snoc122 (Γ Con122 nil122 snoc122) A.

Definition Var122 : Con122 -> Ty122 -> Set
 := fun Γ A =>
   forall (Var122 : Con122 -> Ty122 -> Set)
     (vz  : forall Γ A, Var122 (snoc122 Γ A) A)
     (vs  : forall Γ B A, Var122 Γ A -> Var122 (snoc122 Γ B) A)
   , Var122 Γ A.

Definition vz122 {Γ A} : Var122 (snoc122 Γ A) A
 := fun Var122 vz122 vs => vz122 _ _.

Definition vs122 {Γ B A} : Var122 Γ A -> Var122 (snoc122 Γ B) A
 := fun x Var122 vz122 vs122 => vs122 _ _ _ (x Var122 vz122 vs122).

Definition Tm122 : Con122 -> Ty122 -> Set
 := fun Γ A =>
   forall (Tm122  : Con122 -> Ty122 -> Set)
     (var   : forall Γ A     , Var122 Γ A -> Tm122 Γ A)
     (lam   : forall Γ A B   , Tm122 (snoc122 Γ A) B -> Tm122 Γ (arr122 A B))
     (app   : forall Γ A B   , Tm122 Γ (arr122 A B) -> Tm122 Γ A -> Tm122 Γ B)
   , Tm122 Γ A.

Definition var122 {Γ A} : Var122 Γ A -> Tm122 Γ A
 := fun x Tm122 var122 lam app =>
     var122 _ _ x.

Definition lam122 {Γ A B} : Tm122 (snoc122 Γ A) B -> Tm122 Γ (arr122 A B)
 := fun t Tm122 var122 lam122 app =>
     lam122 _ _ _ (t Tm122 var122 lam122 app).

Definition app122 {Γ A B} : Tm122 Γ (arr122 A B) -> Tm122 Γ A -> Tm122 Γ B
 := fun t u Tm122 var122 lam122 app122 =>
     app122 _ _ _
         (t Tm122 var122 lam122 app122)
         (u Tm122 var122 lam122 app122).

Definition v0122 {Γ A} : Tm122 (snoc122 Γ A) A
 := var122 vz122.

Definition v1122 {Γ A B} : Tm122 (snoc122 (snoc122 Γ A) B) A
 := var122 (vs122 vz122).

Definition v2122 {Γ A B C} : Tm122 (snoc122 (snoc122 (snoc122 Γ A) B) C) A
 := var122 (vs122 (vs122 vz122)).

Definition v3122 {Γ A B C D} : Tm122 (snoc122 (snoc122 (snoc122 (snoc122 Γ A) B) C) D) A
 := var122 (vs122 (vs122 (vs122 vz122))).

Definition v4122 {Γ A B C D E} : Tm122 (snoc122 (snoc122 (snoc122 (snoc122 (snoc122 Γ A) B) C) D) E) A
 := var122 (vs122 (vs122 (vs122 (vs122 vz122)))).

Definition test122 {Γ A} : Tm122 Γ (arr122 (arr122 A A) (arr122 A A))
 := lam122 (lam122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 v0122))))))).


Definition Ty123 : Set
 := forall (Ty123 : Set)
      (base   : Ty123)
      (arr : Ty123 -> Ty123 -> Ty123)
    , Ty123.

Definition base123 : Ty123 := fun _ base123 _ => base123.

Definition arr123 : Ty123 -> Ty123 -> Ty123
 := fun A B Ty123 base123 arr123 =>
     arr123 (A Ty123 base123 arr123) (B Ty123 base123 arr123).

Definition Con123 : Set
 := forall (Con123  : Set)
      (nil  : Con123)
      (snoc : Con123 -> Ty123 -> Con123)
    , Con123.

Definition nil123 : Con123
 := fun Con123 nil123 snoc => nil123.

Definition snoc123 : Con123 -> Ty123 -> Con123
 := fun Γ A Con123 nil123 snoc123 => snoc123 (Γ Con123 nil123 snoc123) A.

Definition Var123 : Con123 -> Ty123 -> Set
 := fun Γ A =>
   forall (Var123 : Con123 -> Ty123 -> Set)
     (vz  : forall Γ A, Var123 (snoc123 Γ A) A)
     (vs  : forall Γ B A, Var123 Γ A -> Var123 (snoc123 Γ B) A)
   , Var123 Γ A.

Definition vz123 {Γ A} : Var123 (snoc123 Γ A) A
 := fun Var123 vz123 vs => vz123 _ _.

Definition vs123 {Γ B A} : Var123 Γ A -> Var123 (snoc123 Γ B) A
 := fun x Var123 vz123 vs123 => vs123 _ _ _ (x Var123 vz123 vs123).

Definition Tm123 : Con123 -> Ty123 -> Set
 := fun Γ A =>
   forall (Tm123  : Con123 -> Ty123 -> Set)
     (var   : forall Γ A     , Var123 Γ A -> Tm123 Γ A)
     (lam   : forall Γ A B   , Tm123 (snoc123 Γ A) B -> Tm123 Γ (arr123 A B))
     (app   : forall Γ A B   , Tm123 Γ (arr123 A B) -> Tm123 Γ A -> Tm123 Γ B)
   , Tm123 Γ A.

Definition var123 {Γ A} : Var123 Γ A -> Tm123 Γ A
 := fun x Tm123 var123 lam app =>
     var123 _ _ x.

Definition lam123 {Γ A B} : Tm123 (snoc123 Γ A) B -> Tm123 Γ (arr123 A B)
 := fun t Tm123 var123 lam123 app =>
     lam123 _ _ _ (t Tm123 var123 lam123 app).

Definition app123 {Γ A B} : Tm123 Γ (arr123 A B) -> Tm123 Γ A -> Tm123 Γ B
 := fun t u Tm123 var123 lam123 app123 =>
     app123 _ _ _
         (t Tm123 var123 lam123 app123)
         (u Tm123 var123 lam123 app123).

Definition v0123 {Γ A} : Tm123 (snoc123 Γ A) A
 := var123 vz123.

Definition v1123 {Γ A B} : Tm123 (snoc123 (snoc123 Γ A) B) A
 := var123 (vs123 vz123).

Definition v2123 {Γ A B C} : Tm123 (snoc123 (snoc123 (snoc123 Γ A) B) C) A
 := var123 (vs123 (vs123 vz123)).

Definition v3123 {Γ A B C D} : Tm123 (snoc123 (snoc123 (snoc123 (snoc123 Γ A) B) C) D) A
 := var123 (vs123 (vs123 (vs123 vz123))).

Definition v4123 {Γ A B C D E} : Tm123 (snoc123 (snoc123 (snoc123 (snoc123 (snoc123 Γ A) B) C) D) E) A
 := var123 (vs123 (vs123 (vs123 (vs123 vz123)))).

Definition test123 {Γ A} : Tm123 Γ (arr123 (arr123 A A) (arr123 A A))
 := lam123 (lam123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 v0123))))))).


Definition Ty124 : Set
 := forall (Ty124 : Set)
      (base   : Ty124)
      (arr : Ty124 -> Ty124 -> Ty124)
    , Ty124.

Definition base124 : Ty124 := fun _ base124 _ => base124.

Definition arr124 : Ty124 -> Ty124 -> Ty124
 := fun A B Ty124 base124 arr124 =>
     arr124 (A Ty124 base124 arr124) (B Ty124 base124 arr124).

Definition Con124 : Set
 := forall (Con124  : Set)
      (nil  : Con124)
      (snoc : Con124 -> Ty124 -> Con124)
    , Con124.

Definition nil124 : Con124
 := fun Con124 nil124 snoc => nil124.

Definition snoc124 : Con124 -> Ty124 -> Con124
 := fun Γ A Con124 nil124 snoc124 => snoc124 (Γ Con124 nil124 snoc124) A.

Definition Var124 : Con124 -> Ty124 -> Set
 := fun Γ A =>
   forall (Var124 : Con124 -> Ty124 -> Set)
     (vz  : forall Γ A, Var124 (snoc124 Γ A) A)
     (vs  : forall Γ B A, Var124 Γ A -> Var124 (snoc124 Γ B) A)
   , Var124 Γ A.

Definition vz124 {Γ A} : Var124 (snoc124 Γ A) A
 := fun Var124 vz124 vs => vz124 _ _.

Definition vs124 {Γ B A} : Var124 Γ A -> Var124 (snoc124 Γ B) A
 := fun x Var124 vz124 vs124 => vs124 _ _ _ (x Var124 vz124 vs124).

Definition Tm124 : Con124 -> Ty124 -> Set
 := fun Γ A =>
   forall (Tm124  : Con124 -> Ty124 -> Set)
     (var   : forall Γ A     , Var124 Γ A -> Tm124 Γ A)
     (lam   : forall Γ A B   , Tm124 (snoc124 Γ A) B -> Tm124 Γ (arr124 A B))
     (app   : forall Γ A B   , Tm124 Γ (arr124 A B) -> Tm124 Γ A -> Tm124 Γ B)
   , Tm124 Γ A.

Definition var124 {Γ A} : Var124 Γ A -> Tm124 Γ A
 := fun x Tm124 var124 lam app =>
     var124 _ _ x.

Definition lam124 {Γ A B} : Tm124 (snoc124 Γ A) B -> Tm124 Γ (arr124 A B)
 := fun t Tm124 var124 lam124 app =>
     lam124 _ _ _ (t Tm124 var124 lam124 app).

Definition app124 {Γ A B} : Tm124 Γ (arr124 A B) -> Tm124 Γ A -> Tm124 Γ B
 := fun t u Tm124 var124 lam124 app124 =>
     app124 _ _ _
         (t Tm124 var124 lam124 app124)
         (u Tm124 var124 lam124 app124).

Definition v0124 {Γ A} : Tm124 (snoc124 Γ A) A
 := var124 vz124.

Definition v1124 {Γ A B} : Tm124 (snoc124 (snoc124 Γ A) B) A
 := var124 (vs124 vz124).

Definition v2124 {Γ A B C} : Tm124 (snoc124 (snoc124 (snoc124 Γ A) B) C) A
 := var124 (vs124 (vs124 vz124)).

Definition v3124 {Γ A B C D} : Tm124 (snoc124 (snoc124 (snoc124 (snoc124 Γ A) B) C) D) A
 := var124 (vs124 (vs124 (vs124 vz124))).

Definition v4124 {Γ A B C D E} : Tm124 (snoc124 (snoc124 (snoc124 (snoc124 (snoc124 Γ A) B) C) D) E) A
 := var124 (vs124 (vs124 (vs124 (vs124 vz124)))).

Definition test124 {Γ A} : Tm124 Γ (arr124 (arr124 A A) (arr124 A A))
 := lam124 (lam124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 v0124))))))).


Definition Ty125 : Set
 := forall (Ty125 : Set)
      (base   : Ty125)
      (arr : Ty125 -> Ty125 -> Ty125)
    , Ty125.

Definition base125 : Ty125 := fun _ base125 _ => base125.

Definition arr125 : Ty125 -> Ty125 -> Ty125
 := fun A B Ty125 base125 arr125 =>
     arr125 (A Ty125 base125 arr125) (B Ty125 base125 arr125).

Definition Con125 : Set
 := forall (Con125  : Set)
      (nil  : Con125)
      (snoc : Con125 -> Ty125 -> Con125)
    , Con125.

Definition nil125 : Con125
 := fun Con125 nil125 snoc => nil125.

Definition snoc125 : Con125 -> Ty125 -> Con125
 := fun Γ A Con125 nil125 snoc125 => snoc125 (Γ Con125 nil125 snoc125) A.

Definition Var125 : Con125 -> Ty125 -> Set
 := fun Γ A =>
   forall (Var125 : Con125 -> Ty125 -> Set)
     (vz  : forall Γ A, Var125 (snoc125 Γ A) A)
     (vs  : forall Γ B A, Var125 Γ A -> Var125 (snoc125 Γ B) A)
   , Var125 Γ A.

Definition vz125 {Γ A} : Var125 (snoc125 Γ A) A
 := fun Var125 vz125 vs => vz125 _ _.

Definition vs125 {Γ B A} : Var125 Γ A -> Var125 (snoc125 Γ B) A
 := fun x Var125 vz125 vs125 => vs125 _ _ _ (x Var125 vz125 vs125).

Definition Tm125 : Con125 -> Ty125 -> Set
 := fun Γ A =>
   forall (Tm125  : Con125 -> Ty125 -> Set)
     (var   : forall Γ A     , Var125 Γ A -> Tm125 Γ A)
     (lam   : forall Γ A B   , Tm125 (snoc125 Γ A) B -> Tm125 Γ (arr125 A B))
     (app   : forall Γ A B   , Tm125 Γ (arr125 A B) -> Tm125 Γ A -> Tm125 Γ B)
   , Tm125 Γ A.

Definition var125 {Γ A} : Var125 Γ A -> Tm125 Γ A
 := fun x Tm125 var125 lam app =>
     var125 _ _ x.

Definition lam125 {Γ A B} : Tm125 (snoc125 Γ A) B -> Tm125 Γ (arr125 A B)
 := fun t Tm125 var125 lam125 app =>
     lam125 _ _ _ (t Tm125 var125 lam125 app).

Definition app125 {Γ A B} : Tm125 Γ (arr125 A B) -> Tm125 Γ A -> Tm125 Γ B
 := fun t u Tm125 var125 lam125 app125 =>
     app125 _ _ _
         (t Tm125 var125 lam125 app125)
         (u Tm125 var125 lam125 app125).

Definition v0125 {Γ A} : Tm125 (snoc125 Γ A) A
 := var125 vz125.

Definition v1125 {Γ A B} : Tm125 (snoc125 (snoc125 Γ A) B) A
 := var125 (vs125 vz125).

Definition v2125 {Γ A B C} : Tm125 (snoc125 (snoc125 (snoc125 Γ A) B) C) A
 := var125 (vs125 (vs125 vz125)).

Definition v3125 {Γ A B C D} : Tm125 (snoc125 (snoc125 (snoc125 (snoc125 Γ A) B) C) D) A
 := var125 (vs125 (vs125 (vs125 vz125))).

Definition v4125 {Γ A B C D E} : Tm125 (snoc125 (snoc125 (snoc125 (snoc125 (snoc125 Γ A) B) C) D) E) A
 := var125 (vs125 (vs125 (vs125 (vs125 vz125)))).

Definition test125 {Γ A} : Tm125 Γ (arr125 (arr125 A A) (arr125 A A))
 := lam125 (lam125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 v0125))))))).


Definition Ty126 : Set
 := forall (Ty126 : Set)
      (base   : Ty126)
      (arr : Ty126 -> Ty126 -> Ty126)
    , Ty126.

Definition base126 : Ty126 := fun _ base126 _ => base126.

Definition arr126 : Ty126 -> Ty126 -> Ty126
 := fun A B Ty126 base126 arr126 =>
     arr126 (A Ty126 base126 arr126) (B Ty126 base126 arr126).

Definition Con126 : Set
 := forall (Con126  : Set)
      (nil  : Con126)
      (snoc : Con126 -> Ty126 -> Con126)
    , Con126.

Definition nil126 : Con126
 := fun Con126 nil126 snoc => nil126.

Definition snoc126 : Con126 -> Ty126 -> Con126
 := fun Γ A Con126 nil126 snoc126 => snoc126 (Γ Con126 nil126 snoc126) A.

Definition Var126 : Con126 -> Ty126 -> Set
 := fun Γ A =>
   forall (Var126 : Con126 -> Ty126 -> Set)
     (vz  : forall Γ A, Var126 (snoc126 Γ A) A)
     (vs  : forall Γ B A, Var126 Γ A -> Var126 (snoc126 Γ B) A)
   , Var126 Γ A.

Definition vz126 {Γ A} : Var126 (snoc126 Γ A) A
 := fun Var126 vz126 vs => vz126 _ _.

Definition vs126 {Γ B A} : Var126 Γ A -> Var126 (snoc126 Γ B) A
 := fun x Var126 vz126 vs126 => vs126 _ _ _ (x Var126 vz126 vs126).

Definition Tm126 : Con126 -> Ty126 -> Set
 := fun Γ A =>
   forall (Tm126  : Con126 -> Ty126 -> Set)
     (var   : forall Γ A     , Var126 Γ A -> Tm126 Γ A)
     (lam   : forall Γ A B   , Tm126 (snoc126 Γ A) B -> Tm126 Γ (arr126 A B))
     (app   : forall Γ A B   , Tm126 Γ (arr126 A B) -> Tm126 Γ A -> Tm126 Γ B)
   , Tm126 Γ A.

Definition var126 {Γ A} : Var126 Γ A -> Tm126 Γ A
 := fun x Tm126 var126 lam app =>
     var126 _ _ x.

Definition lam126 {Γ A B} : Tm126 (snoc126 Γ A) B -> Tm126 Γ (arr126 A B)
 := fun t Tm126 var126 lam126 app =>
     lam126 _ _ _ (t Tm126 var126 lam126 app).

Definition app126 {Γ A B} : Tm126 Γ (arr126 A B) -> Tm126 Γ A -> Tm126 Γ B
 := fun t u Tm126 var126 lam126 app126 =>
     app126 _ _ _
         (t Tm126 var126 lam126 app126)
         (u Tm126 var126 lam126 app126).

Definition v0126 {Γ A} : Tm126 (snoc126 Γ A) A
 := var126 vz126.

Definition v1126 {Γ A B} : Tm126 (snoc126 (snoc126 Γ A) B) A
 := var126 (vs126 vz126).

Definition v2126 {Γ A B C} : Tm126 (snoc126 (snoc126 (snoc126 Γ A) B) C) A
 := var126 (vs126 (vs126 vz126)).

Definition v3126 {Γ A B C D} : Tm126 (snoc126 (snoc126 (snoc126 (snoc126 Γ A) B) C) D) A
 := var126 (vs126 (vs126 (vs126 vz126))).

Definition v4126 {Γ A B C D E} : Tm126 (snoc126 (snoc126 (snoc126 (snoc126 (snoc126 Γ A) B) C) D) E) A
 := var126 (vs126 (vs126 (vs126 (vs126 vz126)))).

Definition test126 {Γ A} : Tm126 Γ (arr126 (arr126 A A) (arr126 A A))
 := lam126 (lam126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 v0126))))))).


Definition Ty127 : Set
 := forall (Ty127 : Set)
      (base   : Ty127)
      (arr : Ty127 -> Ty127 -> Ty127)
    , Ty127.

Definition base127 : Ty127 := fun _ base127 _ => base127.

Definition arr127 : Ty127 -> Ty127 -> Ty127
 := fun A B Ty127 base127 arr127 =>
     arr127 (A Ty127 base127 arr127) (B Ty127 base127 arr127).

Definition Con127 : Set
 := forall (Con127  : Set)
      (nil  : Con127)
      (snoc : Con127 -> Ty127 -> Con127)
    , Con127.

Definition nil127 : Con127
 := fun Con127 nil127 snoc => nil127.

Definition snoc127 : Con127 -> Ty127 -> Con127
 := fun Γ A Con127 nil127 snoc127 => snoc127 (Γ Con127 nil127 snoc127) A.

Definition Var127 : Con127 -> Ty127 -> Set
 := fun Γ A =>
   forall (Var127 : Con127 -> Ty127 -> Set)
     (vz  : forall Γ A, Var127 (snoc127 Γ A) A)
     (vs  : forall Γ B A, Var127 Γ A -> Var127 (snoc127 Γ B) A)
   , Var127 Γ A.

Definition vz127 {Γ A} : Var127 (snoc127 Γ A) A
 := fun Var127 vz127 vs => vz127 _ _.

Definition vs127 {Γ B A} : Var127 Γ A -> Var127 (snoc127 Γ B) A
 := fun x Var127 vz127 vs127 => vs127 _ _ _ (x Var127 vz127 vs127).

Definition Tm127 : Con127 -> Ty127 -> Set
 := fun Γ A =>
   forall (Tm127  : Con127 -> Ty127 -> Set)
     (var   : forall Γ A     , Var127 Γ A -> Tm127 Γ A)
     (lam   : forall Γ A B   , Tm127 (snoc127 Γ A) B -> Tm127 Γ (arr127 A B))
     (app   : forall Γ A B   , Tm127 Γ (arr127 A B) -> Tm127 Γ A -> Tm127 Γ B)
   , Tm127 Γ A.

Definition var127 {Γ A} : Var127 Γ A -> Tm127 Γ A
 := fun x Tm127 var127 lam app =>
     var127 _ _ x.

Definition lam127 {Γ A B} : Tm127 (snoc127 Γ A) B -> Tm127 Γ (arr127 A B)
 := fun t Tm127 var127 lam127 app =>
     lam127 _ _ _ (t Tm127 var127 lam127 app).

Definition app127 {Γ A B} : Tm127 Γ (arr127 A B) -> Tm127 Γ A -> Tm127 Γ B
 := fun t u Tm127 var127 lam127 app127 =>
     app127 _ _ _
         (t Tm127 var127 lam127 app127)
         (u Tm127 var127 lam127 app127).

Definition v0127 {Γ A} : Tm127 (snoc127 Γ A) A
 := var127 vz127.

Definition v1127 {Γ A B} : Tm127 (snoc127 (snoc127 Γ A) B) A
 := var127 (vs127 vz127).

Definition v2127 {Γ A B C} : Tm127 (snoc127 (snoc127 (snoc127 Γ A) B) C) A
 := var127 (vs127 (vs127 vz127)).

Definition v3127 {Γ A B C D} : Tm127 (snoc127 (snoc127 (snoc127 (snoc127 Γ A) B) C) D) A
 := var127 (vs127 (vs127 (vs127 vz127))).

Definition v4127 {Γ A B C D E} : Tm127 (snoc127 (snoc127 (snoc127 (snoc127 (snoc127 Γ A) B) C) D) E) A
 := var127 (vs127 (vs127 (vs127 (vs127 vz127)))).

Definition test127 {Γ A} : Tm127 Γ (arr127 (arr127 A A) (arr127 A A))
 := lam127 (lam127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 v0127))))))).


Definition Ty128 : Set
 := forall (Ty128 : Set)
      (base   : Ty128)
      (arr : Ty128 -> Ty128 -> Ty128)
    , Ty128.

Definition base128 : Ty128 := fun _ base128 _ => base128.

Definition arr128 : Ty128 -> Ty128 -> Ty128
 := fun A B Ty128 base128 arr128 =>
     arr128 (A Ty128 base128 arr128) (B Ty128 base128 arr128).

Definition Con128 : Set
 := forall (Con128  : Set)
      (nil  : Con128)
      (snoc : Con128 -> Ty128 -> Con128)
    , Con128.

Definition nil128 : Con128
 := fun Con128 nil128 snoc => nil128.

Definition snoc128 : Con128 -> Ty128 -> Con128
 := fun Γ A Con128 nil128 snoc128 => snoc128 (Γ Con128 nil128 snoc128) A.

Definition Var128 : Con128 -> Ty128 -> Set
 := fun Γ A =>
   forall (Var128 : Con128 -> Ty128 -> Set)
     (vz  : forall Γ A, Var128 (snoc128 Γ A) A)
     (vs  : forall Γ B A, Var128 Γ A -> Var128 (snoc128 Γ B) A)
   , Var128 Γ A.

Definition vz128 {Γ A} : Var128 (snoc128 Γ A) A
 := fun Var128 vz128 vs => vz128 _ _.

Definition vs128 {Γ B A} : Var128 Γ A -> Var128 (snoc128 Γ B) A
 := fun x Var128 vz128 vs128 => vs128 _ _ _ (x Var128 vz128 vs128).

Definition Tm128 : Con128 -> Ty128 -> Set
 := fun Γ A =>
   forall (Tm128  : Con128 -> Ty128 -> Set)
     (var   : forall Γ A     , Var128 Γ A -> Tm128 Γ A)
     (lam   : forall Γ A B   , Tm128 (snoc128 Γ A) B -> Tm128 Γ (arr128 A B))
     (app   : forall Γ A B   , Tm128 Γ (arr128 A B) -> Tm128 Γ A -> Tm128 Γ B)
   , Tm128 Γ A.

Definition var128 {Γ A} : Var128 Γ A -> Tm128 Γ A
 := fun x Tm128 var128 lam app =>
     var128 _ _ x.

Definition lam128 {Γ A B} : Tm128 (snoc128 Γ A) B -> Tm128 Γ (arr128 A B)
 := fun t Tm128 var128 lam128 app =>
     lam128 _ _ _ (t Tm128 var128 lam128 app).

Definition app128 {Γ A B} : Tm128 Γ (arr128 A B) -> Tm128 Γ A -> Tm128 Γ B
 := fun t u Tm128 var128 lam128 app128 =>
     app128 _ _ _
         (t Tm128 var128 lam128 app128)
         (u Tm128 var128 lam128 app128).

Definition v0128 {Γ A} : Tm128 (snoc128 Γ A) A
 := var128 vz128.

Definition v1128 {Γ A B} : Tm128 (snoc128 (snoc128 Γ A) B) A
 := var128 (vs128 vz128).

Definition v2128 {Γ A B C} : Tm128 (snoc128 (snoc128 (snoc128 Γ A) B) C) A
 := var128 (vs128 (vs128 vz128)).

Definition v3128 {Γ A B C D} : Tm128 (snoc128 (snoc128 (snoc128 (snoc128 Γ A) B) C) D) A
 := var128 (vs128 (vs128 (vs128 vz128))).

Definition v4128 {Γ A B C D E} : Tm128 (snoc128 (snoc128 (snoc128 (snoc128 (snoc128 Γ A) B) C) D) E) A
 := var128 (vs128 (vs128 (vs128 (vs128 vz128)))).

Definition test128 {Γ A} : Tm128 Γ (arr128 (arr128 A A) (arr128 A A))
 := lam128 (lam128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 v0128))))))).


Definition Ty129 : Set
 := forall (Ty129 : Set)
      (base   : Ty129)
      (arr : Ty129 -> Ty129 -> Ty129)
    , Ty129.

Definition base129 : Ty129 := fun _ base129 _ => base129.

Definition arr129 : Ty129 -> Ty129 -> Ty129
 := fun A B Ty129 base129 arr129 =>
     arr129 (A Ty129 base129 arr129) (B Ty129 base129 arr129).

Definition Con129 : Set
 := forall (Con129  : Set)
      (nil  : Con129)
      (snoc : Con129 -> Ty129 -> Con129)
    , Con129.

Definition nil129 : Con129
 := fun Con129 nil129 snoc => nil129.

Definition snoc129 : Con129 -> Ty129 -> Con129
 := fun Γ A Con129 nil129 snoc129 => snoc129 (Γ Con129 nil129 snoc129) A.

Definition Var129 : Con129 -> Ty129 -> Set
 := fun Γ A =>
   forall (Var129 : Con129 -> Ty129 -> Set)
     (vz  : forall Γ A, Var129 (snoc129 Γ A) A)
     (vs  : forall Γ B A, Var129 Γ A -> Var129 (snoc129 Γ B) A)
   , Var129 Γ A.

Definition vz129 {Γ A} : Var129 (snoc129 Γ A) A
 := fun Var129 vz129 vs => vz129 _ _.

Definition vs129 {Γ B A} : Var129 Γ A -> Var129 (snoc129 Γ B) A
 := fun x Var129 vz129 vs129 => vs129 _ _ _ (x Var129 vz129 vs129).

Definition Tm129 : Con129 -> Ty129 -> Set
 := fun Γ A =>
   forall (Tm129  : Con129 -> Ty129 -> Set)
     (var   : forall Γ A     , Var129 Γ A -> Tm129 Γ A)
     (lam   : forall Γ A B   , Tm129 (snoc129 Γ A) B -> Tm129 Γ (arr129 A B))
     (app   : forall Γ A B   , Tm129 Γ (arr129 A B) -> Tm129 Γ A -> Tm129 Γ B)
   , Tm129 Γ A.

Definition var129 {Γ A} : Var129 Γ A -> Tm129 Γ A
 := fun x Tm129 var129 lam app =>
     var129 _ _ x.

Definition lam129 {Γ A B} : Tm129 (snoc129 Γ A) B -> Tm129 Γ (arr129 A B)
 := fun t Tm129 var129 lam129 app =>
     lam129 _ _ _ (t Tm129 var129 lam129 app).

Definition app129 {Γ A B} : Tm129 Γ (arr129 A B) -> Tm129 Γ A -> Tm129 Γ B
 := fun t u Tm129 var129 lam129 app129 =>
     app129 _ _ _
         (t Tm129 var129 lam129 app129)
         (u Tm129 var129 lam129 app129).

Definition v0129 {Γ A} : Tm129 (snoc129 Γ A) A
 := var129 vz129.

Definition v1129 {Γ A B} : Tm129 (snoc129 (snoc129 Γ A) B) A
 := var129 (vs129 vz129).

Definition v2129 {Γ A B C} : Tm129 (snoc129 (snoc129 (snoc129 Γ A) B) C) A
 := var129 (vs129 (vs129 vz129)).

Definition v3129 {Γ A B C D} : Tm129 (snoc129 (snoc129 (snoc129 (snoc129 Γ A) B) C) D) A
 := var129 (vs129 (vs129 (vs129 vz129))).

Definition v4129 {Γ A B C D E} : Tm129 (snoc129 (snoc129 (snoc129 (snoc129 (snoc129 Γ A) B) C) D) E) A
 := var129 (vs129 (vs129 (vs129 (vs129 vz129)))).

Definition test129 {Γ A} : Tm129 Γ (arr129 (arr129 A A) (arr129 A A))
 := lam129 (lam129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 v0129))))))).


Definition Ty130 : Set
 := forall (Ty130 : Set)
      (base   : Ty130)
      (arr : Ty130 -> Ty130 -> Ty130)
    , Ty130.

Definition base130 : Ty130 := fun _ base130 _ => base130.

Definition arr130 : Ty130 -> Ty130 -> Ty130
 := fun A B Ty130 base130 arr130 =>
     arr130 (A Ty130 base130 arr130) (B Ty130 base130 arr130).

Definition Con130 : Set
 := forall (Con130  : Set)
      (nil  : Con130)
      (snoc : Con130 -> Ty130 -> Con130)
    , Con130.

Definition nil130 : Con130
 := fun Con130 nil130 snoc => nil130.

Definition snoc130 : Con130 -> Ty130 -> Con130
 := fun Γ A Con130 nil130 snoc130 => snoc130 (Γ Con130 nil130 snoc130) A.

Definition Var130 : Con130 -> Ty130 -> Set
 := fun Γ A =>
   forall (Var130 : Con130 -> Ty130 -> Set)
     (vz  : forall Γ A, Var130 (snoc130 Γ A) A)
     (vs  : forall Γ B A, Var130 Γ A -> Var130 (snoc130 Γ B) A)
   , Var130 Γ A.

Definition vz130 {Γ A} : Var130 (snoc130 Γ A) A
 := fun Var130 vz130 vs => vz130 _ _.

Definition vs130 {Γ B A} : Var130 Γ A -> Var130 (snoc130 Γ B) A
 := fun x Var130 vz130 vs130 => vs130 _ _ _ (x Var130 vz130 vs130).

Definition Tm130 : Con130 -> Ty130 -> Set
 := fun Γ A =>
   forall (Tm130  : Con130 -> Ty130 -> Set)
     (var   : forall Γ A     , Var130 Γ A -> Tm130 Γ A)
     (lam   : forall Γ A B   , Tm130 (snoc130 Γ A) B -> Tm130 Γ (arr130 A B))
     (app   : forall Γ A B   , Tm130 Γ (arr130 A B) -> Tm130 Γ A -> Tm130 Γ B)
   , Tm130 Γ A.

Definition var130 {Γ A} : Var130 Γ A -> Tm130 Γ A
 := fun x Tm130 var130 lam app =>
     var130 _ _ x.

Definition lam130 {Γ A B} : Tm130 (snoc130 Γ A) B -> Tm130 Γ (arr130 A B)
 := fun t Tm130 var130 lam130 app =>
     lam130 _ _ _ (t Tm130 var130 lam130 app).

Definition app130 {Γ A B} : Tm130 Γ (arr130 A B) -> Tm130 Γ A -> Tm130 Γ B
 := fun t u Tm130 var130 lam130 app130 =>
     app130 _ _ _
         (t Tm130 var130 lam130 app130)
         (u Tm130 var130 lam130 app130).

Definition v0130 {Γ A} : Tm130 (snoc130 Γ A) A
 := var130 vz130.

Definition v1130 {Γ A B} : Tm130 (snoc130 (snoc130 Γ A) B) A
 := var130 (vs130 vz130).

Definition v2130 {Γ A B C} : Tm130 (snoc130 (snoc130 (snoc130 Γ A) B) C) A
 := var130 (vs130 (vs130 vz130)).

Definition v3130 {Γ A B C D} : Tm130 (snoc130 (snoc130 (snoc130 (snoc130 Γ A) B) C) D) A
 := var130 (vs130 (vs130 (vs130 vz130))).

Definition v4130 {Γ A B C D E} : Tm130 (snoc130 (snoc130 (snoc130 (snoc130 (snoc130 Γ A) B) C) D) E) A
 := var130 (vs130 (vs130 (vs130 (vs130 vz130)))).

Definition test130 {Γ A} : Tm130 Γ (arr130 (arr130 A A) (arr130 A A))
 := lam130 (lam130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 v0130))))))).


Definition Ty131 : Set
 := forall (Ty131 : Set)
      (base   : Ty131)
      (arr : Ty131 -> Ty131 -> Ty131)
    , Ty131.

Definition base131 : Ty131 := fun _ base131 _ => base131.

Definition arr131 : Ty131 -> Ty131 -> Ty131
 := fun A B Ty131 base131 arr131 =>
     arr131 (A Ty131 base131 arr131) (B Ty131 base131 arr131).

Definition Con131 : Set
 := forall (Con131  : Set)
      (nil  : Con131)
      (snoc : Con131 -> Ty131 -> Con131)
    , Con131.

Definition nil131 : Con131
 := fun Con131 nil131 snoc => nil131.

Definition snoc131 : Con131 -> Ty131 -> Con131
 := fun Γ A Con131 nil131 snoc131 => snoc131 (Γ Con131 nil131 snoc131) A.

Definition Var131 : Con131 -> Ty131 -> Set
 := fun Γ A =>
   forall (Var131 : Con131 -> Ty131 -> Set)
     (vz  : forall Γ A, Var131 (snoc131 Γ A) A)
     (vs  : forall Γ B A, Var131 Γ A -> Var131 (snoc131 Γ B) A)
   , Var131 Γ A.

Definition vz131 {Γ A} : Var131 (snoc131 Γ A) A
 := fun Var131 vz131 vs => vz131 _ _.

Definition vs131 {Γ B A} : Var131 Γ A -> Var131 (snoc131 Γ B) A
 := fun x Var131 vz131 vs131 => vs131 _ _ _ (x Var131 vz131 vs131).

Definition Tm131 : Con131 -> Ty131 -> Set
 := fun Γ A =>
   forall (Tm131  : Con131 -> Ty131 -> Set)
     (var   : forall Γ A     , Var131 Γ A -> Tm131 Γ A)
     (lam   : forall Γ A B   , Tm131 (snoc131 Γ A) B -> Tm131 Γ (arr131 A B))
     (app   : forall Γ A B   , Tm131 Γ (arr131 A B) -> Tm131 Γ A -> Tm131 Γ B)
   , Tm131 Γ A.

Definition var131 {Γ A} : Var131 Γ A -> Tm131 Γ A
 := fun x Tm131 var131 lam app =>
     var131 _ _ x.

Definition lam131 {Γ A B} : Tm131 (snoc131 Γ A) B -> Tm131 Γ (arr131 A B)
 := fun t Tm131 var131 lam131 app =>
     lam131 _ _ _ (t Tm131 var131 lam131 app).

Definition app131 {Γ A B} : Tm131 Γ (arr131 A B) -> Tm131 Γ A -> Tm131 Γ B
 := fun t u Tm131 var131 lam131 app131 =>
     app131 _ _ _
         (t Tm131 var131 lam131 app131)
         (u Tm131 var131 lam131 app131).

Definition v0131 {Γ A} : Tm131 (snoc131 Γ A) A
 := var131 vz131.

Definition v1131 {Γ A B} : Tm131 (snoc131 (snoc131 Γ A) B) A
 := var131 (vs131 vz131).

Definition v2131 {Γ A B C} : Tm131 (snoc131 (snoc131 (snoc131 Γ A) B) C) A
 := var131 (vs131 (vs131 vz131)).

Definition v3131 {Γ A B C D} : Tm131 (snoc131 (snoc131 (snoc131 (snoc131 Γ A) B) C) D) A
 := var131 (vs131 (vs131 (vs131 vz131))).

Definition v4131 {Γ A B C D E} : Tm131 (snoc131 (snoc131 (snoc131 (snoc131 (snoc131 Γ A) B) C) D) E) A
 := var131 (vs131 (vs131 (vs131 (vs131 vz131)))).

Definition test131 {Γ A} : Tm131 Γ (arr131 (arr131 A A) (arr131 A A))
 := lam131 (lam131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 v0131))))))).


Definition Ty132 : Set
 := forall (Ty132 : Set)
      (base   : Ty132)
      (arr : Ty132 -> Ty132 -> Ty132)
    , Ty132.

Definition base132 : Ty132 := fun _ base132 _ => base132.

Definition arr132 : Ty132 -> Ty132 -> Ty132
 := fun A B Ty132 base132 arr132 =>
     arr132 (A Ty132 base132 arr132) (B Ty132 base132 arr132).

Definition Con132 : Set
 := forall (Con132  : Set)
      (nil  : Con132)
      (snoc : Con132 -> Ty132 -> Con132)
    , Con132.

Definition nil132 : Con132
 := fun Con132 nil132 snoc => nil132.

Definition snoc132 : Con132 -> Ty132 -> Con132
 := fun Γ A Con132 nil132 snoc132 => snoc132 (Γ Con132 nil132 snoc132) A.

Definition Var132 : Con132 -> Ty132 -> Set
 := fun Γ A =>
   forall (Var132 : Con132 -> Ty132 -> Set)
     (vz  : forall Γ A, Var132 (snoc132 Γ A) A)
     (vs  : forall Γ B A, Var132 Γ A -> Var132 (snoc132 Γ B) A)
   , Var132 Γ A.

Definition vz132 {Γ A} : Var132 (snoc132 Γ A) A
 := fun Var132 vz132 vs => vz132 _ _.

Definition vs132 {Γ B A} : Var132 Γ A -> Var132 (snoc132 Γ B) A
 := fun x Var132 vz132 vs132 => vs132 _ _ _ (x Var132 vz132 vs132).

Definition Tm132 : Con132 -> Ty132 -> Set
 := fun Γ A =>
   forall (Tm132  : Con132 -> Ty132 -> Set)
     (var   : forall Γ A     , Var132 Γ A -> Tm132 Γ A)
     (lam   : forall Γ A B   , Tm132 (snoc132 Γ A) B -> Tm132 Γ (arr132 A B))
     (app   : forall Γ A B   , Tm132 Γ (arr132 A B) -> Tm132 Γ A -> Tm132 Γ B)
   , Tm132 Γ A.

Definition var132 {Γ A} : Var132 Γ A -> Tm132 Γ A
 := fun x Tm132 var132 lam app =>
     var132 _ _ x.

Definition lam132 {Γ A B} : Tm132 (snoc132 Γ A) B -> Tm132 Γ (arr132 A B)
 := fun t Tm132 var132 lam132 app =>
     lam132 _ _ _ (t Tm132 var132 lam132 app).

Definition app132 {Γ A B} : Tm132 Γ (arr132 A B) -> Tm132 Γ A -> Tm132 Γ B
 := fun t u Tm132 var132 lam132 app132 =>
     app132 _ _ _
         (t Tm132 var132 lam132 app132)
         (u Tm132 var132 lam132 app132).

Definition v0132 {Γ A} : Tm132 (snoc132 Γ A) A
 := var132 vz132.

Definition v1132 {Γ A B} : Tm132 (snoc132 (snoc132 Γ A) B) A
 := var132 (vs132 vz132).

Definition v2132 {Γ A B C} : Tm132 (snoc132 (snoc132 (snoc132 Γ A) B) C) A
 := var132 (vs132 (vs132 vz132)).

Definition v3132 {Γ A B C D} : Tm132 (snoc132 (snoc132 (snoc132 (snoc132 Γ A) B) C) D) A
 := var132 (vs132 (vs132 (vs132 vz132))).

Definition v4132 {Γ A B C D E} : Tm132 (snoc132 (snoc132 (snoc132 (snoc132 (snoc132 Γ A) B) C) D) E) A
 := var132 (vs132 (vs132 (vs132 (vs132 vz132)))).

Definition test132 {Γ A} : Tm132 Γ (arr132 (arr132 A A) (arr132 A A))
 := lam132 (lam132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 v0132))))))).


Definition Ty133 : Set
 := forall (Ty133 : Set)
      (base   : Ty133)
      (arr : Ty133 -> Ty133 -> Ty133)
    , Ty133.

Definition base133 : Ty133 := fun _ base133 _ => base133.

Definition arr133 : Ty133 -> Ty133 -> Ty133
 := fun A B Ty133 base133 arr133 =>
     arr133 (A Ty133 base133 arr133) (B Ty133 base133 arr133).

Definition Con133 : Set
 := forall (Con133  : Set)
      (nil  : Con133)
      (snoc : Con133 -> Ty133 -> Con133)
    , Con133.

Definition nil133 : Con133
 := fun Con133 nil133 snoc => nil133.

Definition snoc133 : Con133 -> Ty133 -> Con133
 := fun Γ A Con133 nil133 snoc133 => snoc133 (Γ Con133 nil133 snoc133) A.

Definition Var133 : Con133 -> Ty133 -> Set
 := fun Γ A =>
   forall (Var133 : Con133 -> Ty133 -> Set)
     (vz  : forall Γ A, Var133 (snoc133 Γ A) A)
     (vs  : forall Γ B A, Var133 Γ A -> Var133 (snoc133 Γ B) A)
   , Var133 Γ A.

Definition vz133 {Γ A} : Var133 (snoc133 Γ A) A
 := fun Var133 vz133 vs => vz133 _ _.

Definition vs133 {Γ B A} : Var133 Γ A -> Var133 (snoc133 Γ B) A
 := fun x Var133 vz133 vs133 => vs133 _ _ _ (x Var133 vz133 vs133).

Definition Tm133 : Con133 -> Ty133 -> Set
 := fun Γ A =>
   forall (Tm133  : Con133 -> Ty133 -> Set)
     (var   : forall Γ A     , Var133 Γ A -> Tm133 Γ A)
     (lam   : forall Γ A B   , Tm133 (snoc133 Γ A) B -> Tm133 Γ (arr133 A B))
     (app   : forall Γ A B   , Tm133 Γ (arr133 A B) -> Tm133 Γ A -> Tm133 Γ B)
   , Tm133 Γ A.

Definition var133 {Γ A} : Var133 Γ A -> Tm133 Γ A
 := fun x Tm133 var133 lam app =>
     var133 _ _ x.

Definition lam133 {Γ A B} : Tm133 (snoc133 Γ A) B -> Tm133 Γ (arr133 A B)
 := fun t Tm133 var133 lam133 app =>
     lam133 _ _ _ (t Tm133 var133 lam133 app).

Definition app133 {Γ A B} : Tm133 Γ (arr133 A B) -> Tm133 Γ A -> Tm133 Γ B
 := fun t u Tm133 var133 lam133 app133 =>
     app133 _ _ _
         (t Tm133 var133 lam133 app133)
         (u Tm133 var133 lam133 app133).

Definition v0133 {Γ A} : Tm133 (snoc133 Γ A) A
 := var133 vz133.

Definition v1133 {Γ A B} : Tm133 (snoc133 (snoc133 Γ A) B) A
 := var133 (vs133 vz133).

Definition v2133 {Γ A B C} : Tm133 (snoc133 (snoc133 (snoc133 Γ A) B) C) A
 := var133 (vs133 (vs133 vz133)).

Definition v3133 {Γ A B C D} : Tm133 (snoc133 (snoc133 (snoc133 (snoc133 Γ A) B) C) D) A
 := var133 (vs133 (vs133 (vs133 vz133))).

Definition v4133 {Γ A B C D E} : Tm133 (snoc133 (snoc133 (snoc133 (snoc133 (snoc133 Γ A) B) C) D) E) A
 := var133 (vs133 (vs133 (vs133 (vs133 vz133)))).

Definition test133 {Γ A} : Tm133 Γ (arr133 (arr133 A A) (arr133 A A))
 := lam133 (lam133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 v0133))))))).


Definition Ty134 : Set
 := forall (Ty134 : Set)
      (base   : Ty134)
      (arr : Ty134 -> Ty134 -> Ty134)
    , Ty134.

Definition base134 : Ty134 := fun _ base134 _ => base134.

Definition arr134 : Ty134 -> Ty134 -> Ty134
 := fun A B Ty134 base134 arr134 =>
     arr134 (A Ty134 base134 arr134) (B Ty134 base134 arr134).

Definition Con134 : Set
 := forall (Con134  : Set)
      (nil  : Con134)
      (snoc : Con134 -> Ty134 -> Con134)
    , Con134.

Definition nil134 : Con134
 := fun Con134 nil134 snoc => nil134.

Definition snoc134 : Con134 -> Ty134 -> Con134
 := fun Γ A Con134 nil134 snoc134 => snoc134 (Γ Con134 nil134 snoc134) A.

Definition Var134 : Con134 -> Ty134 -> Set
 := fun Γ A =>
   forall (Var134 : Con134 -> Ty134 -> Set)
     (vz  : forall Γ A, Var134 (snoc134 Γ A) A)
     (vs  : forall Γ B A, Var134 Γ A -> Var134 (snoc134 Γ B) A)
   , Var134 Γ A.

Definition vz134 {Γ A} : Var134 (snoc134 Γ A) A
 := fun Var134 vz134 vs => vz134 _ _.

Definition vs134 {Γ B A} : Var134 Γ A -> Var134 (snoc134 Γ B) A
 := fun x Var134 vz134 vs134 => vs134 _ _ _ (x Var134 vz134 vs134).

Definition Tm134 : Con134 -> Ty134 -> Set
 := fun Γ A =>
   forall (Tm134  : Con134 -> Ty134 -> Set)
     (var   : forall Γ A     , Var134 Γ A -> Tm134 Γ A)
     (lam   : forall Γ A B   , Tm134 (snoc134 Γ A) B -> Tm134 Γ (arr134 A B))
     (app   : forall Γ A B   , Tm134 Γ (arr134 A B) -> Tm134 Γ A -> Tm134 Γ B)
   , Tm134 Γ A.

Definition var134 {Γ A} : Var134 Γ A -> Tm134 Γ A
 := fun x Tm134 var134 lam app =>
     var134 _ _ x.

Definition lam134 {Γ A B} : Tm134 (snoc134 Γ A) B -> Tm134 Γ (arr134 A B)
 := fun t Tm134 var134 lam134 app =>
     lam134 _ _ _ (t Tm134 var134 lam134 app).

Definition app134 {Γ A B} : Tm134 Γ (arr134 A B) -> Tm134 Γ A -> Tm134 Γ B
 := fun t u Tm134 var134 lam134 app134 =>
     app134 _ _ _
         (t Tm134 var134 lam134 app134)
         (u Tm134 var134 lam134 app134).

Definition v0134 {Γ A} : Tm134 (snoc134 Γ A) A
 := var134 vz134.

Definition v1134 {Γ A B} : Tm134 (snoc134 (snoc134 Γ A) B) A
 := var134 (vs134 vz134).

Definition v2134 {Γ A B C} : Tm134 (snoc134 (snoc134 (snoc134 Γ A) B) C) A
 := var134 (vs134 (vs134 vz134)).

Definition v3134 {Γ A B C D} : Tm134 (snoc134 (snoc134 (snoc134 (snoc134 Γ A) B) C) D) A
 := var134 (vs134 (vs134 (vs134 vz134))).

Definition v4134 {Γ A B C D E} : Tm134 (snoc134 (snoc134 (snoc134 (snoc134 (snoc134 Γ A) B) C) D) E) A
 := var134 (vs134 (vs134 (vs134 (vs134 vz134)))).

Definition test134 {Γ A} : Tm134 Γ (arr134 (arr134 A A) (arr134 A A))
 := lam134 (lam134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 v0134))))))).


Definition Ty135 : Set
 := forall (Ty135 : Set)
      (base   : Ty135)
      (arr : Ty135 -> Ty135 -> Ty135)
    , Ty135.

Definition base135 : Ty135 := fun _ base135 _ => base135.

Definition arr135 : Ty135 -> Ty135 -> Ty135
 := fun A B Ty135 base135 arr135 =>
     arr135 (A Ty135 base135 arr135) (B Ty135 base135 arr135).

Definition Con135 : Set
 := forall (Con135  : Set)
      (nil  : Con135)
      (snoc : Con135 -> Ty135 -> Con135)
    , Con135.

Definition nil135 : Con135
 := fun Con135 nil135 snoc => nil135.

Definition snoc135 : Con135 -> Ty135 -> Con135
 := fun Γ A Con135 nil135 snoc135 => snoc135 (Γ Con135 nil135 snoc135) A.

Definition Var135 : Con135 -> Ty135 -> Set
 := fun Γ A =>
   forall (Var135 : Con135 -> Ty135 -> Set)
     (vz  : forall Γ A, Var135 (snoc135 Γ A) A)
     (vs  : forall Γ B A, Var135 Γ A -> Var135 (snoc135 Γ B) A)
   , Var135 Γ A.

Definition vz135 {Γ A} : Var135 (snoc135 Γ A) A
 := fun Var135 vz135 vs => vz135 _ _.

Definition vs135 {Γ B A} : Var135 Γ A -> Var135 (snoc135 Γ B) A
 := fun x Var135 vz135 vs135 => vs135 _ _ _ (x Var135 vz135 vs135).

Definition Tm135 : Con135 -> Ty135 -> Set
 := fun Γ A =>
   forall (Tm135  : Con135 -> Ty135 -> Set)
     (var   : forall Γ A     , Var135 Γ A -> Tm135 Γ A)
     (lam   : forall Γ A B   , Tm135 (snoc135 Γ A) B -> Tm135 Γ (arr135 A B))
     (app   : forall Γ A B   , Tm135 Γ (arr135 A B) -> Tm135 Γ A -> Tm135 Γ B)
   , Tm135 Γ A.

Definition var135 {Γ A} : Var135 Γ A -> Tm135 Γ A
 := fun x Tm135 var135 lam app =>
     var135 _ _ x.

Definition lam135 {Γ A B} : Tm135 (snoc135 Γ A) B -> Tm135 Γ (arr135 A B)
 := fun t Tm135 var135 lam135 app =>
     lam135 _ _ _ (t Tm135 var135 lam135 app).

Definition app135 {Γ A B} : Tm135 Γ (arr135 A B) -> Tm135 Γ A -> Tm135 Γ B
 := fun t u Tm135 var135 lam135 app135 =>
     app135 _ _ _
         (t Tm135 var135 lam135 app135)
         (u Tm135 var135 lam135 app135).

Definition v0135 {Γ A} : Tm135 (snoc135 Γ A) A
 := var135 vz135.

Definition v1135 {Γ A B} : Tm135 (snoc135 (snoc135 Γ A) B) A
 := var135 (vs135 vz135).

Definition v2135 {Γ A B C} : Tm135 (snoc135 (snoc135 (snoc135 Γ A) B) C) A
 := var135 (vs135 (vs135 vz135)).

Definition v3135 {Γ A B C D} : Tm135 (snoc135 (snoc135 (snoc135 (snoc135 Γ A) B) C) D) A
 := var135 (vs135 (vs135 (vs135 vz135))).

Definition v4135 {Γ A B C D E} : Tm135 (snoc135 (snoc135 (snoc135 (snoc135 (snoc135 Γ A) B) C) D) E) A
 := var135 (vs135 (vs135 (vs135 (vs135 vz135)))).

Definition test135 {Γ A} : Tm135 Γ (arr135 (arr135 A A) (arr135 A A))
 := lam135 (lam135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 v0135))))))).


Definition Ty136 : Set
 := forall (Ty136 : Set)
      (base   : Ty136)
      (arr : Ty136 -> Ty136 -> Ty136)
    , Ty136.

Definition base136 : Ty136 := fun _ base136 _ => base136.

Definition arr136 : Ty136 -> Ty136 -> Ty136
 := fun A B Ty136 base136 arr136 =>
     arr136 (A Ty136 base136 arr136) (B Ty136 base136 arr136).

Definition Con136 : Set
 := forall (Con136  : Set)
      (nil  : Con136)
      (snoc : Con136 -> Ty136 -> Con136)
    , Con136.

Definition nil136 : Con136
 := fun Con136 nil136 snoc => nil136.

Definition snoc136 : Con136 -> Ty136 -> Con136
 := fun Γ A Con136 nil136 snoc136 => snoc136 (Γ Con136 nil136 snoc136) A.

Definition Var136 : Con136 -> Ty136 -> Set
 := fun Γ A =>
   forall (Var136 : Con136 -> Ty136 -> Set)
     (vz  : forall Γ A, Var136 (snoc136 Γ A) A)
     (vs  : forall Γ B A, Var136 Γ A -> Var136 (snoc136 Γ B) A)
   , Var136 Γ A.

Definition vz136 {Γ A} : Var136 (snoc136 Γ A) A
 := fun Var136 vz136 vs => vz136 _ _.

Definition vs136 {Γ B A} : Var136 Γ A -> Var136 (snoc136 Γ B) A
 := fun x Var136 vz136 vs136 => vs136 _ _ _ (x Var136 vz136 vs136).

Definition Tm136 : Con136 -> Ty136 -> Set
 := fun Γ A =>
   forall (Tm136  : Con136 -> Ty136 -> Set)
     (var   : forall Γ A     , Var136 Γ A -> Tm136 Γ A)
     (lam   : forall Γ A B   , Tm136 (snoc136 Γ A) B -> Tm136 Γ (arr136 A B))
     (app   : forall Γ A B   , Tm136 Γ (arr136 A B) -> Tm136 Γ A -> Tm136 Γ B)
   , Tm136 Γ A.

Definition var136 {Γ A} : Var136 Γ A -> Tm136 Γ A
 := fun x Tm136 var136 lam app =>
     var136 _ _ x.

Definition lam136 {Γ A B} : Tm136 (snoc136 Γ A) B -> Tm136 Γ (arr136 A B)
 := fun t Tm136 var136 lam136 app =>
     lam136 _ _ _ (t Tm136 var136 lam136 app).

Definition app136 {Γ A B} : Tm136 Γ (arr136 A B) -> Tm136 Γ A -> Tm136 Γ B
 := fun t u Tm136 var136 lam136 app136 =>
     app136 _ _ _
         (t Tm136 var136 lam136 app136)
         (u Tm136 var136 lam136 app136).

Definition v0136 {Γ A} : Tm136 (snoc136 Γ A) A
 := var136 vz136.

Definition v1136 {Γ A B} : Tm136 (snoc136 (snoc136 Γ A) B) A
 := var136 (vs136 vz136).

Definition v2136 {Γ A B C} : Tm136 (snoc136 (snoc136 (snoc136 Γ A) B) C) A
 := var136 (vs136 (vs136 vz136)).

Definition v3136 {Γ A B C D} : Tm136 (snoc136 (snoc136 (snoc136 (snoc136 Γ A) B) C) D) A
 := var136 (vs136 (vs136 (vs136 vz136))).

Definition v4136 {Γ A B C D E} : Tm136 (snoc136 (snoc136 (snoc136 (snoc136 (snoc136 Γ A) B) C) D) E) A
 := var136 (vs136 (vs136 (vs136 (vs136 vz136)))).

Definition test136 {Γ A} : Tm136 Γ (arr136 (arr136 A A) (arr136 A A))
 := lam136 (lam136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 v0136))))))).


Definition Ty137 : Set
 := forall (Ty137 : Set)
      (base   : Ty137)
      (arr : Ty137 -> Ty137 -> Ty137)
    , Ty137.

Definition base137 : Ty137 := fun _ base137 _ => base137.

Definition arr137 : Ty137 -> Ty137 -> Ty137
 := fun A B Ty137 base137 arr137 =>
     arr137 (A Ty137 base137 arr137) (B Ty137 base137 arr137).

Definition Con137 : Set
 := forall (Con137  : Set)
      (nil  : Con137)
      (snoc : Con137 -> Ty137 -> Con137)
    , Con137.

Definition nil137 : Con137
 := fun Con137 nil137 snoc => nil137.

Definition snoc137 : Con137 -> Ty137 -> Con137
 := fun Γ A Con137 nil137 snoc137 => snoc137 (Γ Con137 nil137 snoc137) A.

Definition Var137 : Con137 -> Ty137 -> Set
 := fun Γ A =>
   forall (Var137 : Con137 -> Ty137 -> Set)
     (vz  : forall Γ A, Var137 (snoc137 Γ A) A)
     (vs  : forall Γ B A, Var137 Γ A -> Var137 (snoc137 Γ B) A)
   , Var137 Γ A.

Definition vz137 {Γ A} : Var137 (snoc137 Γ A) A
 := fun Var137 vz137 vs => vz137 _ _.

Definition vs137 {Γ B A} : Var137 Γ A -> Var137 (snoc137 Γ B) A
 := fun x Var137 vz137 vs137 => vs137 _ _ _ (x Var137 vz137 vs137).

Definition Tm137 : Con137 -> Ty137 -> Set
 := fun Γ A =>
   forall (Tm137  : Con137 -> Ty137 -> Set)
     (var   : forall Γ A     , Var137 Γ A -> Tm137 Γ A)
     (lam   : forall Γ A B   , Tm137 (snoc137 Γ A) B -> Tm137 Γ (arr137 A B))
     (app   : forall Γ A B   , Tm137 Γ (arr137 A B) -> Tm137 Γ A -> Tm137 Γ B)
   , Tm137 Γ A.

Definition var137 {Γ A} : Var137 Γ A -> Tm137 Γ A
 := fun x Tm137 var137 lam app =>
     var137 _ _ x.

Definition lam137 {Γ A B} : Tm137 (snoc137 Γ A) B -> Tm137 Γ (arr137 A B)
 := fun t Tm137 var137 lam137 app =>
     lam137 _ _ _ (t Tm137 var137 lam137 app).

Definition app137 {Γ A B} : Tm137 Γ (arr137 A B) -> Tm137 Γ A -> Tm137 Γ B
 := fun t u Tm137 var137 lam137 app137 =>
     app137 _ _ _
         (t Tm137 var137 lam137 app137)
         (u Tm137 var137 lam137 app137).

Definition v0137 {Γ A} : Tm137 (snoc137 Γ A) A
 := var137 vz137.

Definition v1137 {Γ A B} : Tm137 (snoc137 (snoc137 Γ A) B) A
 := var137 (vs137 vz137).

Definition v2137 {Γ A B C} : Tm137 (snoc137 (snoc137 (snoc137 Γ A) B) C) A
 := var137 (vs137 (vs137 vz137)).

Definition v3137 {Γ A B C D} : Tm137 (snoc137 (snoc137 (snoc137 (snoc137 Γ A) B) C) D) A
 := var137 (vs137 (vs137 (vs137 vz137))).

Definition v4137 {Γ A B C D E} : Tm137 (snoc137 (snoc137 (snoc137 (snoc137 (snoc137 Γ A) B) C) D) E) A
 := var137 (vs137 (vs137 (vs137 (vs137 vz137)))).

Definition test137 {Γ A} : Tm137 Γ (arr137 (arr137 A A) (arr137 A A))
 := lam137 (lam137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 v0137))))))).


Definition Ty138 : Set
 := forall (Ty138 : Set)
      (base   : Ty138)
      (arr : Ty138 -> Ty138 -> Ty138)
    , Ty138.

Definition base138 : Ty138 := fun _ base138 _ => base138.

Definition arr138 : Ty138 -> Ty138 -> Ty138
 := fun A B Ty138 base138 arr138 =>
     arr138 (A Ty138 base138 arr138) (B Ty138 base138 arr138).

Definition Con138 : Set
 := forall (Con138  : Set)
      (nil  : Con138)
      (snoc : Con138 -> Ty138 -> Con138)
    , Con138.

Definition nil138 : Con138
 := fun Con138 nil138 snoc => nil138.

Definition snoc138 : Con138 -> Ty138 -> Con138
 := fun Γ A Con138 nil138 snoc138 => snoc138 (Γ Con138 nil138 snoc138) A.

Definition Var138 : Con138 -> Ty138 -> Set
 := fun Γ A =>
   forall (Var138 : Con138 -> Ty138 -> Set)
     (vz  : forall Γ A, Var138 (snoc138 Γ A) A)
     (vs  : forall Γ B A, Var138 Γ A -> Var138 (snoc138 Γ B) A)
   , Var138 Γ A.

Definition vz138 {Γ A} : Var138 (snoc138 Γ A) A
 := fun Var138 vz138 vs => vz138 _ _.

Definition vs138 {Γ B A} : Var138 Γ A -> Var138 (snoc138 Γ B) A
 := fun x Var138 vz138 vs138 => vs138 _ _ _ (x Var138 vz138 vs138).

Definition Tm138 : Con138 -> Ty138 -> Set
 := fun Γ A =>
   forall (Tm138  : Con138 -> Ty138 -> Set)
     (var   : forall Γ A     , Var138 Γ A -> Tm138 Γ A)
     (lam   : forall Γ A B   , Tm138 (snoc138 Γ A) B -> Tm138 Γ (arr138 A B))
     (app   : forall Γ A B   , Tm138 Γ (arr138 A B) -> Tm138 Γ A -> Tm138 Γ B)
   , Tm138 Γ A.

Definition var138 {Γ A} : Var138 Γ A -> Tm138 Γ A
 := fun x Tm138 var138 lam app =>
     var138 _ _ x.

Definition lam138 {Γ A B} : Tm138 (snoc138 Γ A) B -> Tm138 Γ (arr138 A B)
 := fun t Tm138 var138 lam138 app =>
     lam138 _ _ _ (t Tm138 var138 lam138 app).

Definition app138 {Γ A B} : Tm138 Γ (arr138 A B) -> Tm138 Γ A -> Tm138 Γ B
 := fun t u Tm138 var138 lam138 app138 =>
     app138 _ _ _
         (t Tm138 var138 lam138 app138)
         (u Tm138 var138 lam138 app138).

Definition v0138 {Γ A} : Tm138 (snoc138 Γ A) A
 := var138 vz138.

Definition v1138 {Γ A B} : Tm138 (snoc138 (snoc138 Γ A) B) A
 := var138 (vs138 vz138).

Definition v2138 {Γ A B C} : Tm138 (snoc138 (snoc138 (snoc138 Γ A) B) C) A
 := var138 (vs138 (vs138 vz138)).

Definition v3138 {Γ A B C D} : Tm138 (snoc138 (snoc138 (snoc138 (snoc138 Γ A) B) C) D) A
 := var138 (vs138 (vs138 (vs138 vz138))).

Definition v4138 {Γ A B C D E} : Tm138 (snoc138 (snoc138 (snoc138 (snoc138 (snoc138 Γ A) B) C) D) E) A
 := var138 (vs138 (vs138 (vs138 (vs138 vz138)))).

Definition test138 {Γ A} : Tm138 Γ (arr138 (arr138 A A) (arr138 A A))
 := lam138 (lam138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 v0138))))))).


Definition Ty139 : Set
 := forall (Ty139 : Set)
      (base   : Ty139)
      (arr : Ty139 -> Ty139 -> Ty139)
    , Ty139.

Definition base139 : Ty139 := fun _ base139 _ => base139.

Definition arr139 : Ty139 -> Ty139 -> Ty139
 := fun A B Ty139 base139 arr139 =>
     arr139 (A Ty139 base139 arr139) (B Ty139 base139 arr139).

Definition Con139 : Set
 := forall (Con139  : Set)
      (nil  : Con139)
      (snoc : Con139 -> Ty139 -> Con139)
    , Con139.

Definition nil139 : Con139
 := fun Con139 nil139 snoc => nil139.

Definition snoc139 : Con139 -> Ty139 -> Con139
 := fun Γ A Con139 nil139 snoc139 => snoc139 (Γ Con139 nil139 snoc139) A.

Definition Var139 : Con139 -> Ty139 -> Set
 := fun Γ A =>
   forall (Var139 : Con139 -> Ty139 -> Set)
     (vz  : forall Γ A, Var139 (snoc139 Γ A) A)
     (vs  : forall Γ B A, Var139 Γ A -> Var139 (snoc139 Γ B) A)
   , Var139 Γ A.

Definition vz139 {Γ A} : Var139 (snoc139 Γ A) A
 := fun Var139 vz139 vs => vz139 _ _.

Definition vs139 {Γ B A} : Var139 Γ A -> Var139 (snoc139 Γ B) A
 := fun x Var139 vz139 vs139 => vs139 _ _ _ (x Var139 vz139 vs139).

Definition Tm139 : Con139 -> Ty139 -> Set
 := fun Γ A =>
   forall (Tm139  : Con139 -> Ty139 -> Set)
     (var   : forall Γ A     , Var139 Γ A -> Tm139 Γ A)
     (lam   : forall Γ A B   , Tm139 (snoc139 Γ A) B -> Tm139 Γ (arr139 A B))
     (app   : forall Γ A B   , Tm139 Γ (arr139 A B) -> Tm139 Γ A -> Tm139 Γ B)
   , Tm139 Γ A.

Definition var139 {Γ A} : Var139 Γ A -> Tm139 Γ A
 := fun x Tm139 var139 lam app =>
     var139 _ _ x.

Definition lam139 {Γ A B} : Tm139 (snoc139 Γ A) B -> Tm139 Γ (arr139 A B)
 := fun t Tm139 var139 lam139 app =>
     lam139 _ _ _ (t Tm139 var139 lam139 app).

Definition app139 {Γ A B} : Tm139 Γ (arr139 A B) -> Tm139 Γ A -> Tm139 Γ B
 := fun t u Tm139 var139 lam139 app139 =>
     app139 _ _ _
         (t Tm139 var139 lam139 app139)
         (u Tm139 var139 lam139 app139).

Definition v0139 {Γ A} : Tm139 (snoc139 Γ A) A
 := var139 vz139.

Definition v1139 {Γ A B} : Tm139 (snoc139 (snoc139 Γ A) B) A
 := var139 (vs139 vz139).

Definition v2139 {Γ A B C} : Tm139 (snoc139 (snoc139 (snoc139 Γ A) B) C) A
 := var139 (vs139 (vs139 vz139)).

Definition v3139 {Γ A B C D} : Tm139 (snoc139 (snoc139 (snoc139 (snoc139 Γ A) B) C) D) A
 := var139 (vs139 (vs139 (vs139 vz139))).

Definition v4139 {Γ A B C D E} : Tm139 (snoc139 (snoc139 (snoc139 (snoc139 (snoc139 Γ A) B) C) D) E) A
 := var139 (vs139 (vs139 (vs139 (vs139 vz139)))).

Definition test139 {Γ A} : Tm139 Γ (arr139 (arr139 A A) (arr139 A A))
 := lam139 (lam139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 v0139))))))).


Definition Ty140 : Set
 := forall (Ty140 : Set)
      (base   : Ty140)
      (arr : Ty140 -> Ty140 -> Ty140)
    , Ty140.

Definition base140 : Ty140 := fun _ base140 _ => base140.

Definition arr140 : Ty140 -> Ty140 -> Ty140
 := fun A B Ty140 base140 arr140 =>
     arr140 (A Ty140 base140 arr140) (B Ty140 base140 arr140).

Definition Con140 : Set
 := forall (Con140  : Set)
      (nil  : Con140)
      (snoc : Con140 -> Ty140 -> Con140)
    , Con140.

Definition nil140 : Con140
 := fun Con140 nil140 snoc => nil140.

Definition snoc140 : Con140 -> Ty140 -> Con140
 := fun Γ A Con140 nil140 snoc140 => snoc140 (Γ Con140 nil140 snoc140) A.

Definition Var140 : Con140 -> Ty140 -> Set
 := fun Γ A =>
   forall (Var140 : Con140 -> Ty140 -> Set)
     (vz  : forall Γ A, Var140 (snoc140 Γ A) A)
     (vs  : forall Γ B A, Var140 Γ A -> Var140 (snoc140 Γ B) A)
   , Var140 Γ A.

Definition vz140 {Γ A} : Var140 (snoc140 Γ A) A
 := fun Var140 vz140 vs => vz140 _ _.

Definition vs140 {Γ B A} : Var140 Γ A -> Var140 (snoc140 Γ B) A
 := fun x Var140 vz140 vs140 => vs140 _ _ _ (x Var140 vz140 vs140).

Definition Tm140 : Con140 -> Ty140 -> Set
 := fun Γ A =>
   forall (Tm140  : Con140 -> Ty140 -> Set)
     (var   : forall Γ A     , Var140 Γ A -> Tm140 Γ A)
     (lam   : forall Γ A B   , Tm140 (snoc140 Γ A) B -> Tm140 Γ (arr140 A B))
     (app   : forall Γ A B   , Tm140 Γ (arr140 A B) -> Tm140 Γ A -> Tm140 Γ B)
   , Tm140 Γ A.

Definition var140 {Γ A} : Var140 Γ A -> Tm140 Γ A
 := fun x Tm140 var140 lam app =>
     var140 _ _ x.

Definition lam140 {Γ A B} : Tm140 (snoc140 Γ A) B -> Tm140 Γ (arr140 A B)
 := fun t Tm140 var140 lam140 app =>
     lam140 _ _ _ (t Tm140 var140 lam140 app).

Definition app140 {Γ A B} : Tm140 Γ (arr140 A B) -> Tm140 Γ A -> Tm140 Γ B
 := fun t u Tm140 var140 lam140 app140 =>
     app140 _ _ _
         (t Tm140 var140 lam140 app140)
         (u Tm140 var140 lam140 app140).

Definition v0140 {Γ A} : Tm140 (snoc140 Γ A) A
 := var140 vz140.

Definition v1140 {Γ A B} : Tm140 (snoc140 (snoc140 Γ A) B) A
 := var140 (vs140 vz140).

Definition v2140 {Γ A B C} : Tm140 (snoc140 (snoc140 (snoc140 Γ A) B) C) A
 := var140 (vs140 (vs140 vz140)).

Definition v3140 {Γ A B C D} : Tm140 (snoc140 (snoc140 (snoc140 (snoc140 Γ A) B) C) D) A
 := var140 (vs140 (vs140 (vs140 vz140))).

Definition v4140 {Γ A B C D E} : Tm140 (snoc140 (snoc140 (snoc140 (snoc140 (snoc140 Γ A) B) C) D) E) A
 := var140 (vs140 (vs140 (vs140 (vs140 vz140)))).

Definition test140 {Γ A} : Tm140 Γ (arr140 (arr140 A A) (arr140 A A))
 := lam140 (lam140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 v0140))))))).


Definition Ty141 : Set
 := forall (Ty141 : Set)
      (base   : Ty141)
      (arr : Ty141 -> Ty141 -> Ty141)
    , Ty141.

Definition base141 : Ty141 := fun _ base141 _ => base141.

Definition arr141 : Ty141 -> Ty141 -> Ty141
 := fun A B Ty141 base141 arr141 =>
     arr141 (A Ty141 base141 arr141) (B Ty141 base141 arr141).

Definition Con141 : Set
 := forall (Con141  : Set)
      (nil  : Con141)
      (snoc : Con141 -> Ty141 -> Con141)
    , Con141.

Definition nil141 : Con141
 := fun Con141 nil141 snoc => nil141.

Definition snoc141 : Con141 -> Ty141 -> Con141
 := fun Γ A Con141 nil141 snoc141 => snoc141 (Γ Con141 nil141 snoc141) A.

Definition Var141 : Con141 -> Ty141 -> Set
 := fun Γ A =>
   forall (Var141 : Con141 -> Ty141 -> Set)
     (vz  : forall Γ A, Var141 (snoc141 Γ A) A)
     (vs  : forall Γ B A, Var141 Γ A -> Var141 (snoc141 Γ B) A)
   , Var141 Γ A.

Definition vz141 {Γ A} : Var141 (snoc141 Γ A) A
 := fun Var141 vz141 vs => vz141 _ _.

Definition vs141 {Γ B A} : Var141 Γ A -> Var141 (snoc141 Γ B) A
 := fun x Var141 vz141 vs141 => vs141 _ _ _ (x Var141 vz141 vs141).

Definition Tm141 : Con141 -> Ty141 -> Set
 := fun Γ A =>
   forall (Tm141  : Con141 -> Ty141 -> Set)
     (var   : forall Γ A     , Var141 Γ A -> Tm141 Γ A)
     (lam   : forall Γ A B   , Tm141 (snoc141 Γ A) B -> Tm141 Γ (arr141 A B))
     (app   : forall Γ A B   , Tm141 Γ (arr141 A B) -> Tm141 Γ A -> Tm141 Γ B)
   , Tm141 Γ A.

Definition var141 {Γ A} : Var141 Γ A -> Tm141 Γ A
 := fun x Tm141 var141 lam app =>
     var141 _ _ x.

Definition lam141 {Γ A B} : Tm141 (snoc141 Γ A) B -> Tm141 Γ (arr141 A B)
 := fun t Tm141 var141 lam141 app =>
     lam141 _ _ _ (t Tm141 var141 lam141 app).

Definition app141 {Γ A B} : Tm141 Γ (arr141 A B) -> Tm141 Γ A -> Tm141 Γ B
 := fun t u Tm141 var141 lam141 app141 =>
     app141 _ _ _
         (t Tm141 var141 lam141 app141)
         (u Tm141 var141 lam141 app141).

Definition v0141 {Γ A} : Tm141 (snoc141 Γ A) A
 := var141 vz141.

Definition v1141 {Γ A B} : Tm141 (snoc141 (snoc141 Γ A) B) A
 := var141 (vs141 vz141).

Definition v2141 {Γ A B C} : Tm141 (snoc141 (snoc141 (snoc141 Γ A) B) C) A
 := var141 (vs141 (vs141 vz141)).

Definition v3141 {Γ A B C D} : Tm141 (snoc141 (snoc141 (snoc141 (snoc141 Γ A) B) C) D) A
 := var141 (vs141 (vs141 (vs141 vz141))).

Definition v4141 {Γ A B C D E} : Tm141 (snoc141 (snoc141 (snoc141 (snoc141 (snoc141 Γ A) B) C) D) E) A
 := var141 (vs141 (vs141 (vs141 (vs141 vz141)))).

Definition test141 {Γ A} : Tm141 Γ (arr141 (arr141 A A) (arr141 A A))
 := lam141 (lam141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 v0141))))))).


Definition Ty142 : Set
 := forall (Ty142 : Set)
      (base   : Ty142)
      (arr : Ty142 -> Ty142 -> Ty142)
    , Ty142.

Definition base142 : Ty142 := fun _ base142 _ => base142.

Definition arr142 : Ty142 -> Ty142 -> Ty142
 := fun A B Ty142 base142 arr142 =>
     arr142 (A Ty142 base142 arr142) (B Ty142 base142 arr142).

Definition Con142 : Set
 := forall (Con142  : Set)
      (nil  : Con142)
      (snoc : Con142 -> Ty142 -> Con142)
    , Con142.

Definition nil142 : Con142
 := fun Con142 nil142 snoc => nil142.

Definition snoc142 : Con142 -> Ty142 -> Con142
 := fun Γ A Con142 nil142 snoc142 => snoc142 (Γ Con142 nil142 snoc142) A.

Definition Var142 : Con142 -> Ty142 -> Set
 := fun Γ A =>
   forall (Var142 : Con142 -> Ty142 -> Set)
     (vz  : forall Γ A, Var142 (snoc142 Γ A) A)
     (vs  : forall Γ B A, Var142 Γ A -> Var142 (snoc142 Γ B) A)
   , Var142 Γ A.

Definition vz142 {Γ A} : Var142 (snoc142 Γ A) A
 := fun Var142 vz142 vs => vz142 _ _.

Definition vs142 {Γ B A} : Var142 Γ A -> Var142 (snoc142 Γ B) A
 := fun x Var142 vz142 vs142 => vs142 _ _ _ (x Var142 vz142 vs142).

Definition Tm142 : Con142 -> Ty142 -> Set
 := fun Γ A =>
   forall (Tm142  : Con142 -> Ty142 -> Set)
     (var   : forall Γ A     , Var142 Γ A -> Tm142 Γ A)
     (lam   : forall Γ A B   , Tm142 (snoc142 Γ A) B -> Tm142 Γ (arr142 A B))
     (app   : forall Γ A B   , Tm142 Γ (arr142 A B) -> Tm142 Γ A -> Tm142 Γ B)
   , Tm142 Γ A.

Definition var142 {Γ A} : Var142 Γ A -> Tm142 Γ A
 := fun x Tm142 var142 lam app =>
     var142 _ _ x.

Definition lam142 {Γ A B} : Tm142 (snoc142 Γ A) B -> Tm142 Γ (arr142 A B)
 := fun t Tm142 var142 lam142 app =>
     lam142 _ _ _ (t Tm142 var142 lam142 app).

Definition app142 {Γ A B} : Tm142 Γ (arr142 A B) -> Tm142 Γ A -> Tm142 Γ B
 := fun t u Tm142 var142 lam142 app142 =>
     app142 _ _ _
         (t Tm142 var142 lam142 app142)
         (u Tm142 var142 lam142 app142).

Definition v0142 {Γ A} : Tm142 (snoc142 Γ A) A
 := var142 vz142.

Definition v1142 {Γ A B} : Tm142 (snoc142 (snoc142 Γ A) B) A
 := var142 (vs142 vz142).

Definition v2142 {Γ A B C} : Tm142 (snoc142 (snoc142 (snoc142 Γ A) B) C) A
 := var142 (vs142 (vs142 vz142)).

Definition v3142 {Γ A B C D} : Tm142 (snoc142 (snoc142 (snoc142 (snoc142 Γ A) B) C) D) A
 := var142 (vs142 (vs142 (vs142 vz142))).

Definition v4142 {Γ A B C D E} : Tm142 (snoc142 (snoc142 (snoc142 (snoc142 (snoc142 Γ A) B) C) D) E) A
 := var142 (vs142 (vs142 (vs142 (vs142 vz142)))).

Definition test142 {Γ A} : Tm142 Γ (arr142 (arr142 A A) (arr142 A A))
 := lam142 (lam142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 v0142))))))).


Definition Ty143 : Set
 := forall (Ty143 : Set)
      (base   : Ty143)
      (arr : Ty143 -> Ty143 -> Ty143)
    , Ty143.

Definition base143 : Ty143 := fun _ base143 _ => base143.

Definition arr143 : Ty143 -> Ty143 -> Ty143
 := fun A B Ty143 base143 arr143 =>
     arr143 (A Ty143 base143 arr143) (B Ty143 base143 arr143).

Definition Con143 : Set
 := forall (Con143  : Set)
      (nil  : Con143)
      (snoc : Con143 -> Ty143 -> Con143)
    , Con143.

Definition nil143 : Con143
 := fun Con143 nil143 snoc => nil143.

Definition snoc143 : Con143 -> Ty143 -> Con143
 := fun Γ A Con143 nil143 snoc143 => snoc143 (Γ Con143 nil143 snoc143) A.

Definition Var143 : Con143 -> Ty143 -> Set
 := fun Γ A =>
   forall (Var143 : Con143 -> Ty143 -> Set)
     (vz  : forall Γ A, Var143 (snoc143 Γ A) A)
     (vs  : forall Γ B A, Var143 Γ A -> Var143 (snoc143 Γ B) A)
   , Var143 Γ A.

Definition vz143 {Γ A} : Var143 (snoc143 Γ A) A
 := fun Var143 vz143 vs => vz143 _ _.

Definition vs143 {Γ B A} : Var143 Γ A -> Var143 (snoc143 Γ B) A
 := fun x Var143 vz143 vs143 => vs143 _ _ _ (x Var143 vz143 vs143).

Definition Tm143 : Con143 -> Ty143 -> Set
 := fun Γ A =>
   forall (Tm143  : Con143 -> Ty143 -> Set)
     (var   : forall Γ A     , Var143 Γ A -> Tm143 Γ A)
     (lam   : forall Γ A B   , Tm143 (snoc143 Γ A) B -> Tm143 Γ (arr143 A B))
     (app   : forall Γ A B   , Tm143 Γ (arr143 A B) -> Tm143 Γ A -> Tm143 Γ B)
   , Tm143 Γ A.

Definition var143 {Γ A} : Var143 Γ A -> Tm143 Γ A
 := fun x Tm143 var143 lam app =>
     var143 _ _ x.

Definition lam143 {Γ A B} : Tm143 (snoc143 Γ A) B -> Tm143 Γ (arr143 A B)
 := fun t Tm143 var143 lam143 app =>
     lam143 _ _ _ (t Tm143 var143 lam143 app).

Definition app143 {Γ A B} : Tm143 Γ (arr143 A B) -> Tm143 Γ A -> Tm143 Γ B
 := fun t u Tm143 var143 lam143 app143 =>
     app143 _ _ _
         (t Tm143 var143 lam143 app143)
         (u Tm143 var143 lam143 app143).

Definition v0143 {Γ A} : Tm143 (snoc143 Γ A) A
 := var143 vz143.

Definition v1143 {Γ A B} : Tm143 (snoc143 (snoc143 Γ A) B) A
 := var143 (vs143 vz143).

Definition v2143 {Γ A B C} : Tm143 (snoc143 (snoc143 (snoc143 Γ A) B) C) A
 := var143 (vs143 (vs143 vz143)).

Definition v3143 {Γ A B C D} : Tm143 (snoc143 (snoc143 (snoc143 (snoc143 Γ A) B) C) D) A
 := var143 (vs143 (vs143 (vs143 vz143))).

Definition v4143 {Γ A B C D E} : Tm143 (snoc143 (snoc143 (snoc143 (snoc143 (snoc143 Γ A) B) C) D) E) A
 := var143 (vs143 (vs143 (vs143 (vs143 vz143)))).

Definition test143 {Γ A} : Tm143 Γ (arr143 (arr143 A A) (arr143 A A))
 := lam143 (lam143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 v0143))))))).


Definition Ty144 : Set
 := forall (Ty144 : Set)
      (base   : Ty144)
      (arr : Ty144 -> Ty144 -> Ty144)
    , Ty144.

Definition base144 : Ty144 := fun _ base144 _ => base144.

Definition arr144 : Ty144 -> Ty144 -> Ty144
 := fun A B Ty144 base144 arr144 =>
     arr144 (A Ty144 base144 arr144) (B Ty144 base144 arr144).

Definition Con144 : Set
 := forall (Con144  : Set)
      (nil  : Con144)
      (snoc : Con144 -> Ty144 -> Con144)
    , Con144.

Definition nil144 : Con144
 := fun Con144 nil144 snoc => nil144.

Definition snoc144 : Con144 -> Ty144 -> Con144
 := fun Γ A Con144 nil144 snoc144 => snoc144 (Γ Con144 nil144 snoc144) A.

Definition Var144 : Con144 -> Ty144 -> Set
 := fun Γ A =>
   forall (Var144 : Con144 -> Ty144 -> Set)
     (vz  : forall Γ A, Var144 (snoc144 Γ A) A)
     (vs  : forall Γ B A, Var144 Γ A -> Var144 (snoc144 Γ B) A)
   , Var144 Γ A.

Definition vz144 {Γ A} : Var144 (snoc144 Γ A) A
 := fun Var144 vz144 vs => vz144 _ _.

Definition vs144 {Γ B A} : Var144 Γ A -> Var144 (snoc144 Γ B) A
 := fun x Var144 vz144 vs144 => vs144 _ _ _ (x Var144 vz144 vs144).

Definition Tm144 : Con144 -> Ty144 -> Set
 := fun Γ A =>
   forall (Tm144  : Con144 -> Ty144 -> Set)
     (var   : forall Γ A     , Var144 Γ A -> Tm144 Γ A)
     (lam   : forall Γ A B   , Tm144 (snoc144 Γ A) B -> Tm144 Γ (arr144 A B))
     (app   : forall Γ A B   , Tm144 Γ (arr144 A B) -> Tm144 Γ A -> Tm144 Γ B)
   , Tm144 Γ A.

Definition var144 {Γ A} : Var144 Γ A -> Tm144 Γ A
 := fun x Tm144 var144 lam app =>
     var144 _ _ x.

Definition lam144 {Γ A B} : Tm144 (snoc144 Γ A) B -> Tm144 Γ (arr144 A B)
 := fun t Tm144 var144 lam144 app =>
     lam144 _ _ _ (t Tm144 var144 lam144 app).

Definition app144 {Γ A B} : Tm144 Γ (arr144 A B) -> Tm144 Γ A -> Tm144 Γ B
 := fun t u Tm144 var144 lam144 app144 =>
     app144 _ _ _
         (t Tm144 var144 lam144 app144)
         (u Tm144 var144 lam144 app144).

Definition v0144 {Γ A} : Tm144 (snoc144 Γ A) A
 := var144 vz144.

Definition v1144 {Γ A B} : Tm144 (snoc144 (snoc144 Γ A) B) A
 := var144 (vs144 vz144).

Definition v2144 {Γ A B C} : Tm144 (snoc144 (snoc144 (snoc144 Γ A) B) C) A
 := var144 (vs144 (vs144 vz144)).

Definition v3144 {Γ A B C D} : Tm144 (snoc144 (snoc144 (snoc144 (snoc144 Γ A) B) C) D) A
 := var144 (vs144 (vs144 (vs144 vz144))).

Definition v4144 {Γ A B C D E} : Tm144 (snoc144 (snoc144 (snoc144 (snoc144 (snoc144 Γ A) B) C) D) E) A
 := var144 (vs144 (vs144 (vs144 (vs144 vz144)))).

Definition test144 {Γ A} : Tm144 Γ (arr144 (arr144 A A) (arr144 A A))
 := lam144 (lam144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 v0144))))))).


Definition Ty145 : Set
 := forall (Ty145 : Set)
      (base   : Ty145)
      (arr : Ty145 -> Ty145 -> Ty145)
    , Ty145.

Definition base145 : Ty145 := fun _ base145 _ => base145.

Definition arr145 : Ty145 -> Ty145 -> Ty145
 := fun A B Ty145 base145 arr145 =>
     arr145 (A Ty145 base145 arr145) (B Ty145 base145 arr145).

Definition Con145 : Set
 := forall (Con145  : Set)
      (nil  : Con145)
      (snoc : Con145 -> Ty145 -> Con145)
    , Con145.

Definition nil145 : Con145
 := fun Con145 nil145 snoc => nil145.

Definition snoc145 : Con145 -> Ty145 -> Con145
 := fun Γ A Con145 nil145 snoc145 => snoc145 (Γ Con145 nil145 snoc145) A.

Definition Var145 : Con145 -> Ty145 -> Set
 := fun Γ A =>
   forall (Var145 : Con145 -> Ty145 -> Set)
     (vz  : forall Γ A, Var145 (snoc145 Γ A) A)
     (vs  : forall Γ B A, Var145 Γ A -> Var145 (snoc145 Γ B) A)
   , Var145 Γ A.

Definition vz145 {Γ A} : Var145 (snoc145 Γ A) A
 := fun Var145 vz145 vs => vz145 _ _.

Definition vs145 {Γ B A} : Var145 Γ A -> Var145 (snoc145 Γ B) A
 := fun x Var145 vz145 vs145 => vs145 _ _ _ (x Var145 vz145 vs145).

Definition Tm145 : Con145 -> Ty145 -> Set
 := fun Γ A =>
   forall (Tm145  : Con145 -> Ty145 -> Set)
     (var   : forall Γ A     , Var145 Γ A -> Tm145 Γ A)
     (lam   : forall Γ A B   , Tm145 (snoc145 Γ A) B -> Tm145 Γ (arr145 A B))
     (app   : forall Γ A B   , Tm145 Γ (arr145 A B) -> Tm145 Γ A -> Tm145 Γ B)
   , Tm145 Γ A.

Definition var145 {Γ A} : Var145 Γ A -> Tm145 Γ A
 := fun x Tm145 var145 lam app =>
     var145 _ _ x.

Definition lam145 {Γ A B} : Tm145 (snoc145 Γ A) B -> Tm145 Γ (arr145 A B)
 := fun t Tm145 var145 lam145 app =>
     lam145 _ _ _ (t Tm145 var145 lam145 app).

Definition app145 {Γ A B} : Tm145 Γ (arr145 A B) -> Tm145 Γ A -> Tm145 Γ B
 := fun t u Tm145 var145 lam145 app145 =>
     app145 _ _ _
         (t Tm145 var145 lam145 app145)
         (u Tm145 var145 lam145 app145).

Definition v0145 {Γ A} : Tm145 (snoc145 Γ A) A
 := var145 vz145.

Definition v1145 {Γ A B} : Tm145 (snoc145 (snoc145 Γ A) B) A
 := var145 (vs145 vz145).

Definition v2145 {Γ A B C} : Tm145 (snoc145 (snoc145 (snoc145 Γ A) B) C) A
 := var145 (vs145 (vs145 vz145)).

Definition v3145 {Γ A B C D} : Tm145 (snoc145 (snoc145 (snoc145 (snoc145 Γ A) B) C) D) A
 := var145 (vs145 (vs145 (vs145 vz145))).

Definition v4145 {Γ A B C D E} : Tm145 (snoc145 (snoc145 (snoc145 (snoc145 (snoc145 Γ A) B) C) D) E) A
 := var145 (vs145 (vs145 (vs145 (vs145 vz145)))).

Definition test145 {Γ A} : Tm145 Γ (arr145 (arr145 A A) (arr145 A A))
 := lam145 (lam145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 v0145))))))).


Definition Ty146 : Set
 := forall (Ty146 : Set)
      (base   : Ty146)
      (arr : Ty146 -> Ty146 -> Ty146)
    , Ty146.

Definition base146 : Ty146 := fun _ base146 _ => base146.

Definition arr146 : Ty146 -> Ty146 -> Ty146
 := fun A B Ty146 base146 arr146 =>
     arr146 (A Ty146 base146 arr146) (B Ty146 base146 arr146).

Definition Con146 : Set
 := forall (Con146  : Set)
      (nil  : Con146)
      (snoc : Con146 -> Ty146 -> Con146)
    , Con146.

Definition nil146 : Con146
 := fun Con146 nil146 snoc => nil146.

Definition snoc146 : Con146 -> Ty146 -> Con146
 := fun Γ A Con146 nil146 snoc146 => snoc146 (Γ Con146 nil146 snoc146) A.

Definition Var146 : Con146 -> Ty146 -> Set
 := fun Γ A =>
   forall (Var146 : Con146 -> Ty146 -> Set)
     (vz  : forall Γ A, Var146 (snoc146 Γ A) A)
     (vs  : forall Γ B A, Var146 Γ A -> Var146 (snoc146 Γ B) A)
   , Var146 Γ A.

Definition vz146 {Γ A} : Var146 (snoc146 Γ A) A
 := fun Var146 vz146 vs => vz146 _ _.

Definition vs146 {Γ B A} : Var146 Γ A -> Var146 (snoc146 Γ B) A
 := fun x Var146 vz146 vs146 => vs146 _ _ _ (x Var146 vz146 vs146).

Definition Tm146 : Con146 -> Ty146 -> Set
 := fun Γ A =>
   forall (Tm146  : Con146 -> Ty146 -> Set)
     (var   : forall Γ A     , Var146 Γ A -> Tm146 Γ A)
     (lam   : forall Γ A B   , Tm146 (snoc146 Γ A) B -> Tm146 Γ (arr146 A B))
     (app   : forall Γ A B   , Tm146 Γ (arr146 A B) -> Tm146 Γ A -> Tm146 Γ B)
   , Tm146 Γ A.

Definition var146 {Γ A} : Var146 Γ A -> Tm146 Γ A
 := fun x Tm146 var146 lam app =>
     var146 _ _ x.

Definition lam146 {Γ A B} : Tm146 (snoc146 Γ A) B -> Tm146 Γ (arr146 A B)
 := fun t Tm146 var146 lam146 app =>
     lam146 _ _ _ (t Tm146 var146 lam146 app).

Definition app146 {Γ A B} : Tm146 Γ (arr146 A B) -> Tm146 Γ A -> Tm146 Γ B
 := fun t u Tm146 var146 lam146 app146 =>
     app146 _ _ _
         (t Tm146 var146 lam146 app146)
         (u Tm146 var146 lam146 app146).

Definition v0146 {Γ A} : Tm146 (snoc146 Γ A) A
 := var146 vz146.

Definition v1146 {Γ A B} : Tm146 (snoc146 (snoc146 Γ A) B) A
 := var146 (vs146 vz146).

Definition v2146 {Γ A B C} : Tm146 (snoc146 (snoc146 (snoc146 Γ A) B) C) A
 := var146 (vs146 (vs146 vz146)).

Definition v3146 {Γ A B C D} : Tm146 (snoc146 (snoc146 (snoc146 (snoc146 Γ A) B) C) D) A
 := var146 (vs146 (vs146 (vs146 vz146))).

Definition v4146 {Γ A B C D E} : Tm146 (snoc146 (snoc146 (snoc146 (snoc146 (snoc146 Γ A) B) C) D) E) A
 := var146 (vs146 (vs146 (vs146 (vs146 vz146)))).

Definition test146 {Γ A} : Tm146 Γ (arr146 (arr146 A A) (arr146 A A))
 := lam146 (lam146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 v0146))))))).


Definition Ty147 : Set
 := forall (Ty147 : Set)
      (base   : Ty147)
      (arr : Ty147 -> Ty147 -> Ty147)
    , Ty147.

Definition base147 : Ty147 := fun _ base147 _ => base147.

Definition arr147 : Ty147 -> Ty147 -> Ty147
 := fun A B Ty147 base147 arr147 =>
     arr147 (A Ty147 base147 arr147) (B Ty147 base147 arr147).

Definition Con147 : Set
 := forall (Con147  : Set)
      (nil  : Con147)
      (snoc : Con147 -> Ty147 -> Con147)
    , Con147.

Definition nil147 : Con147
 := fun Con147 nil147 snoc => nil147.

Definition snoc147 : Con147 -> Ty147 -> Con147
 := fun Γ A Con147 nil147 snoc147 => snoc147 (Γ Con147 nil147 snoc147) A.

Definition Var147 : Con147 -> Ty147 -> Set
 := fun Γ A =>
   forall (Var147 : Con147 -> Ty147 -> Set)
     (vz  : forall Γ A, Var147 (snoc147 Γ A) A)
     (vs  : forall Γ B A, Var147 Γ A -> Var147 (snoc147 Γ B) A)
   , Var147 Γ A.

Definition vz147 {Γ A} : Var147 (snoc147 Γ A) A
 := fun Var147 vz147 vs => vz147 _ _.

Definition vs147 {Γ B A} : Var147 Γ A -> Var147 (snoc147 Γ B) A
 := fun x Var147 vz147 vs147 => vs147 _ _ _ (x Var147 vz147 vs147).

Definition Tm147 : Con147 -> Ty147 -> Set
 := fun Γ A =>
   forall (Tm147  : Con147 -> Ty147 -> Set)
     (var   : forall Γ A     , Var147 Γ A -> Tm147 Γ A)
     (lam   : forall Γ A B   , Tm147 (snoc147 Γ A) B -> Tm147 Γ (arr147 A B))
     (app   : forall Γ A B   , Tm147 Γ (arr147 A B) -> Tm147 Γ A -> Tm147 Γ B)
   , Tm147 Γ A.

Definition var147 {Γ A} : Var147 Γ A -> Tm147 Γ A
 := fun x Tm147 var147 lam app =>
     var147 _ _ x.

Definition lam147 {Γ A B} : Tm147 (snoc147 Γ A) B -> Tm147 Γ (arr147 A B)
 := fun t Tm147 var147 lam147 app =>
     lam147 _ _ _ (t Tm147 var147 lam147 app).

Definition app147 {Γ A B} : Tm147 Γ (arr147 A B) -> Tm147 Γ A -> Tm147 Γ B
 := fun t u Tm147 var147 lam147 app147 =>
     app147 _ _ _
         (t Tm147 var147 lam147 app147)
         (u Tm147 var147 lam147 app147).

Definition v0147 {Γ A} : Tm147 (snoc147 Γ A) A
 := var147 vz147.

Definition v1147 {Γ A B} : Tm147 (snoc147 (snoc147 Γ A) B) A
 := var147 (vs147 vz147).

Definition v2147 {Γ A B C} : Tm147 (snoc147 (snoc147 (snoc147 Γ A) B) C) A
 := var147 (vs147 (vs147 vz147)).

Definition v3147 {Γ A B C D} : Tm147 (snoc147 (snoc147 (snoc147 (snoc147 Γ A) B) C) D) A
 := var147 (vs147 (vs147 (vs147 vz147))).

Definition v4147 {Γ A B C D E} : Tm147 (snoc147 (snoc147 (snoc147 (snoc147 (snoc147 Γ A) B) C) D) E) A
 := var147 (vs147 (vs147 (vs147 (vs147 vz147)))).

Definition test147 {Γ A} : Tm147 Γ (arr147 (arr147 A A) (arr147 A A))
 := lam147 (lam147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 v0147))))))).


Definition Ty148 : Set
 := forall (Ty148 : Set)
      (base   : Ty148)
      (arr : Ty148 -> Ty148 -> Ty148)
    , Ty148.

Definition base148 : Ty148 := fun _ base148 _ => base148.

Definition arr148 : Ty148 -> Ty148 -> Ty148
 := fun A B Ty148 base148 arr148 =>
     arr148 (A Ty148 base148 arr148) (B Ty148 base148 arr148).

Definition Con148 : Set
 := forall (Con148  : Set)
      (nil  : Con148)
      (snoc : Con148 -> Ty148 -> Con148)
    , Con148.

Definition nil148 : Con148
 := fun Con148 nil148 snoc => nil148.

Definition snoc148 : Con148 -> Ty148 -> Con148
 := fun Γ A Con148 nil148 snoc148 => snoc148 (Γ Con148 nil148 snoc148) A.

Definition Var148 : Con148 -> Ty148 -> Set
 := fun Γ A =>
   forall (Var148 : Con148 -> Ty148 -> Set)
     (vz  : forall Γ A, Var148 (snoc148 Γ A) A)
     (vs  : forall Γ B A, Var148 Γ A -> Var148 (snoc148 Γ B) A)
   , Var148 Γ A.

Definition vz148 {Γ A} : Var148 (snoc148 Γ A) A
 := fun Var148 vz148 vs => vz148 _ _.

Definition vs148 {Γ B A} : Var148 Γ A -> Var148 (snoc148 Γ B) A
 := fun x Var148 vz148 vs148 => vs148 _ _ _ (x Var148 vz148 vs148).

Definition Tm148 : Con148 -> Ty148 -> Set
 := fun Γ A =>
   forall (Tm148  : Con148 -> Ty148 -> Set)
     (var   : forall Γ A     , Var148 Γ A -> Tm148 Γ A)
     (lam   : forall Γ A B   , Tm148 (snoc148 Γ A) B -> Tm148 Γ (arr148 A B))
     (app   : forall Γ A B   , Tm148 Γ (arr148 A B) -> Tm148 Γ A -> Tm148 Γ B)
   , Tm148 Γ A.

Definition var148 {Γ A} : Var148 Γ A -> Tm148 Γ A
 := fun x Tm148 var148 lam app =>
     var148 _ _ x.

Definition lam148 {Γ A B} : Tm148 (snoc148 Γ A) B -> Tm148 Γ (arr148 A B)
 := fun t Tm148 var148 lam148 app =>
     lam148 _ _ _ (t Tm148 var148 lam148 app).

Definition app148 {Γ A B} : Tm148 Γ (arr148 A B) -> Tm148 Γ A -> Tm148 Γ B
 := fun t u Tm148 var148 lam148 app148 =>
     app148 _ _ _
         (t Tm148 var148 lam148 app148)
         (u Tm148 var148 lam148 app148).

Definition v0148 {Γ A} : Tm148 (snoc148 Γ A) A
 := var148 vz148.

Definition v1148 {Γ A B} : Tm148 (snoc148 (snoc148 Γ A) B) A
 := var148 (vs148 vz148).

Definition v2148 {Γ A B C} : Tm148 (snoc148 (snoc148 (snoc148 Γ A) B) C) A
 := var148 (vs148 (vs148 vz148)).

Definition v3148 {Γ A B C D} : Tm148 (snoc148 (snoc148 (snoc148 (snoc148 Γ A) B) C) D) A
 := var148 (vs148 (vs148 (vs148 vz148))).

Definition v4148 {Γ A B C D E} : Tm148 (snoc148 (snoc148 (snoc148 (snoc148 (snoc148 Γ A) B) C) D) E) A
 := var148 (vs148 (vs148 (vs148 (vs148 vz148)))).

Definition test148 {Γ A} : Tm148 Γ (arr148 (arr148 A A) (arr148 A A))
 := lam148 (lam148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 v0148))))))).


Definition Ty149 : Set
 := forall (Ty149 : Set)
      (base   : Ty149)
      (arr : Ty149 -> Ty149 -> Ty149)
    , Ty149.

Definition base149 : Ty149 := fun _ base149 _ => base149.

Definition arr149 : Ty149 -> Ty149 -> Ty149
 := fun A B Ty149 base149 arr149 =>
     arr149 (A Ty149 base149 arr149) (B Ty149 base149 arr149).

Definition Con149 : Set
 := forall (Con149  : Set)
      (nil  : Con149)
      (snoc : Con149 -> Ty149 -> Con149)
    , Con149.

Definition nil149 : Con149
 := fun Con149 nil149 snoc => nil149.

Definition snoc149 : Con149 -> Ty149 -> Con149
 := fun Γ A Con149 nil149 snoc149 => snoc149 (Γ Con149 nil149 snoc149) A.

Definition Var149 : Con149 -> Ty149 -> Set
 := fun Γ A =>
   forall (Var149 : Con149 -> Ty149 -> Set)
     (vz  : forall Γ A, Var149 (snoc149 Γ A) A)
     (vs  : forall Γ B A, Var149 Γ A -> Var149 (snoc149 Γ B) A)
   , Var149 Γ A.

Definition vz149 {Γ A} : Var149 (snoc149 Γ A) A
 := fun Var149 vz149 vs => vz149 _ _.

Definition vs149 {Γ B A} : Var149 Γ A -> Var149 (snoc149 Γ B) A
 := fun x Var149 vz149 vs149 => vs149 _ _ _ (x Var149 vz149 vs149).

Definition Tm149 : Con149 -> Ty149 -> Set
 := fun Γ A =>
   forall (Tm149  : Con149 -> Ty149 -> Set)
     (var   : forall Γ A     , Var149 Γ A -> Tm149 Γ A)
     (lam   : forall Γ A B   , Tm149 (snoc149 Γ A) B -> Tm149 Γ (arr149 A B))
     (app   : forall Γ A B   , Tm149 Γ (arr149 A B) -> Tm149 Γ A -> Tm149 Γ B)
   , Tm149 Γ A.

Definition var149 {Γ A} : Var149 Γ A -> Tm149 Γ A
 := fun x Tm149 var149 lam app =>
     var149 _ _ x.

Definition lam149 {Γ A B} : Tm149 (snoc149 Γ A) B -> Tm149 Γ (arr149 A B)
 := fun t Tm149 var149 lam149 app =>
     lam149 _ _ _ (t Tm149 var149 lam149 app).

Definition app149 {Γ A B} : Tm149 Γ (arr149 A B) -> Tm149 Γ A -> Tm149 Γ B
 := fun t u Tm149 var149 lam149 app149 =>
     app149 _ _ _
         (t Tm149 var149 lam149 app149)
         (u Tm149 var149 lam149 app149).

Definition v0149 {Γ A} : Tm149 (snoc149 Γ A) A
 := var149 vz149.

Definition v1149 {Γ A B} : Tm149 (snoc149 (snoc149 Γ A) B) A
 := var149 (vs149 vz149).

Definition v2149 {Γ A B C} : Tm149 (snoc149 (snoc149 (snoc149 Γ A) B) C) A
 := var149 (vs149 (vs149 vz149)).

Definition v3149 {Γ A B C D} : Tm149 (snoc149 (snoc149 (snoc149 (snoc149 Γ A) B) C) D) A
 := var149 (vs149 (vs149 (vs149 vz149))).

Definition v4149 {Γ A B C D E} : Tm149 (snoc149 (snoc149 (snoc149 (snoc149 (snoc149 Γ A) B) C) D) E) A
 := var149 (vs149 (vs149 (vs149 (vs149 vz149)))).

Definition test149 {Γ A} : Tm149 Γ (arr149 (arr149 A A) (arr149 A A))
 := lam149 (lam149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 v0149))))))).


Definition Ty150 : Set
 := forall (Ty150 : Set)
      (base   : Ty150)
      (arr : Ty150 -> Ty150 -> Ty150)
    , Ty150.

Definition base150 : Ty150 := fun _ base150 _ => base150.

Definition arr150 : Ty150 -> Ty150 -> Ty150
 := fun A B Ty150 base150 arr150 =>
     arr150 (A Ty150 base150 arr150) (B Ty150 base150 arr150).

Definition Con150 : Set
 := forall (Con150  : Set)
      (nil  : Con150)
      (snoc : Con150 -> Ty150 -> Con150)
    , Con150.

Definition nil150 : Con150
 := fun Con150 nil150 snoc => nil150.

Definition snoc150 : Con150 -> Ty150 -> Con150
 := fun Γ A Con150 nil150 snoc150 => snoc150 (Γ Con150 nil150 snoc150) A.

Definition Var150 : Con150 -> Ty150 -> Set
 := fun Γ A =>
   forall (Var150 : Con150 -> Ty150 -> Set)
     (vz  : forall Γ A, Var150 (snoc150 Γ A) A)
     (vs  : forall Γ B A, Var150 Γ A -> Var150 (snoc150 Γ B) A)
   , Var150 Γ A.

Definition vz150 {Γ A} : Var150 (snoc150 Γ A) A
 := fun Var150 vz150 vs => vz150 _ _.

Definition vs150 {Γ B A} : Var150 Γ A -> Var150 (snoc150 Γ B) A
 := fun x Var150 vz150 vs150 => vs150 _ _ _ (x Var150 vz150 vs150).

Definition Tm150 : Con150 -> Ty150 -> Set
 := fun Γ A =>
   forall (Tm150  : Con150 -> Ty150 -> Set)
     (var   : forall Γ A     , Var150 Γ A -> Tm150 Γ A)
     (lam   : forall Γ A B   , Tm150 (snoc150 Γ A) B -> Tm150 Γ (arr150 A B))
     (app   : forall Γ A B   , Tm150 Γ (arr150 A B) -> Tm150 Γ A -> Tm150 Γ B)
   , Tm150 Γ A.

Definition var150 {Γ A} : Var150 Γ A -> Tm150 Γ A
 := fun x Tm150 var150 lam app =>
     var150 _ _ x.

Definition lam150 {Γ A B} : Tm150 (snoc150 Γ A) B -> Tm150 Γ (arr150 A B)
 := fun t Tm150 var150 lam150 app =>
     lam150 _ _ _ (t Tm150 var150 lam150 app).

Definition app150 {Γ A B} : Tm150 Γ (arr150 A B) -> Tm150 Γ A -> Tm150 Γ B
 := fun t u Tm150 var150 lam150 app150 =>
     app150 _ _ _
         (t Tm150 var150 lam150 app150)
         (u Tm150 var150 lam150 app150).

Definition v0150 {Γ A} : Tm150 (snoc150 Γ A) A
 := var150 vz150.

Definition v1150 {Γ A B} : Tm150 (snoc150 (snoc150 Γ A) B) A
 := var150 (vs150 vz150).

Definition v2150 {Γ A B C} : Tm150 (snoc150 (snoc150 (snoc150 Γ A) B) C) A
 := var150 (vs150 (vs150 vz150)).

Definition v3150 {Γ A B C D} : Tm150 (snoc150 (snoc150 (snoc150 (snoc150 Γ A) B) C) D) A
 := var150 (vs150 (vs150 (vs150 vz150))).

Definition v4150 {Γ A B C D E} : Tm150 (snoc150 (snoc150 (snoc150 (snoc150 (snoc150 Γ A) B) C) D) E) A
 := var150 (vs150 (vs150 (vs150 (vs150 vz150)))).

Definition test150 {Γ A} : Tm150 Γ (arr150 (arr150 A A) (arr150 A A))
 := lam150 (lam150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 v0150))))))).


Definition Ty151 : Set
 := forall (Ty151 : Set)
      (base   : Ty151)
      (arr : Ty151 -> Ty151 -> Ty151)
    , Ty151.

Definition base151 : Ty151 := fun _ base151 _ => base151.

Definition arr151 : Ty151 -> Ty151 -> Ty151
 := fun A B Ty151 base151 arr151 =>
     arr151 (A Ty151 base151 arr151) (B Ty151 base151 arr151).

Definition Con151 : Set
 := forall (Con151  : Set)
      (nil  : Con151)
      (snoc : Con151 -> Ty151 -> Con151)
    , Con151.

Definition nil151 : Con151
 := fun Con151 nil151 snoc => nil151.

Definition snoc151 : Con151 -> Ty151 -> Con151
 := fun Γ A Con151 nil151 snoc151 => snoc151 (Γ Con151 nil151 snoc151) A.

Definition Var151 : Con151 -> Ty151 -> Set
 := fun Γ A =>
   forall (Var151 : Con151 -> Ty151 -> Set)
     (vz  : forall Γ A, Var151 (snoc151 Γ A) A)
     (vs  : forall Γ B A, Var151 Γ A -> Var151 (snoc151 Γ B) A)
   , Var151 Γ A.

Definition vz151 {Γ A} : Var151 (snoc151 Γ A) A
 := fun Var151 vz151 vs => vz151 _ _.

Definition vs151 {Γ B A} : Var151 Γ A -> Var151 (snoc151 Γ B) A
 := fun x Var151 vz151 vs151 => vs151 _ _ _ (x Var151 vz151 vs151).

Definition Tm151 : Con151 -> Ty151 -> Set
 := fun Γ A =>
   forall (Tm151  : Con151 -> Ty151 -> Set)
     (var   : forall Γ A     , Var151 Γ A -> Tm151 Γ A)
     (lam   : forall Γ A B   , Tm151 (snoc151 Γ A) B -> Tm151 Γ (arr151 A B))
     (app   : forall Γ A B   , Tm151 Γ (arr151 A B) -> Tm151 Γ A -> Tm151 Γ B)
   , Tm151 Γ A.

Definition var151 {Γ A} : Var151 Γ A -> Tm151 Γ A
 := fun x Tm151 var151 lam app =>
     var151 _ _ x.

Definition lam151 {Γ A B} : Tm151 (snoc151 Γ A) B -> Tm151 Γ (arr151 A B)
 := fun t Tm151 var151 lam151 app =>
     lam151 _ _ _ (t Tm151 var151 lam151 app).

Definition app151 {Γ A B} : Tm151 Γ (arr151 A B) -> Tm151 Γ A -> Tm151 Γ B
 := fun t u Tm151 var151 lam151 app151 =>
     app151 _ _ _
         (t Tm151 var151 lam151 app151)
         (u Tm151 var151 lam151 app151).

Definition v0151 {Γ A} : Tm151 (snoc151 Γ A) A
 := var151 vz151.

Definition v1151 {Γ A B} : Tm151 (snoc151 (snoc151 Γ A) B) A
 := var151 (vs151 vz151).

Definition v2151 {Γ A B C} : Tm151 (snoc151 (snoc151 (snoc151 Γ A) B) C) A
 := var151 (vs151 (vs151 vz151)).

Definition v3151 {Γ A B C D} : Tm151 (snoc151 (snoc151 (snoc151 (snoc151 Γ A) B) C) D) A
 := var151 (vs151 (vs151 (vs151 vz151))).

Definition v4151 {Γ A B C D E} : Tm151 (snoc151 (snoc151 (snoc151 (snoc151 (snoc151 Γ A) B) C) D) E) A
 := var151 (vs151 (vs151 (vs151 (vs151 vz151)))).

Definition test151 {Γ A} : Tm151 Γ (arr151 (arr151 A A) (arr151 A A))
 := lam151 (lam151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 v0151))))))).


Definition Ty152 : Set
 := forall (Ty152 : Set)
      (base   : Ty152)
      (arr : Ty152 -> Ty152 -> Ty152)
    , Ty152.

Definition base152 : Ty152 := fun _ base152 _ => base152.

Definition arr152 : Ty152 -> Ty152 -> Ty152
 := fun A B Ty152 base152 arr152 =>
     arr152 (A Ty152 base152 arr152) (B Ty152 base152 arr152).

Definition Con152 : Set
 := forall (Con152  : Set)
      (nil  : Con152)
      (snoc : Con152 -> Ty152 -> Con152)
    , Con152.

Definition nil152 : Con152
 := fun Con152 nil152 snoc => nil152.

Definition snoc152 : Con152 -> Ty152 -> Con152
 := fun Γ A Con152 nil152 snoc152 => snoc152 (Γ Con152 nil152 snoc152) A.

Definition Var152 : Con152 -> Ty152 -> Set
 := fun Γ A =>
   forall (Var152 : Con152 -> Ty152 -> Set)
     (vz  : forall Γ A, Var152 (snoc152 Γ A) A)
     (vs  : forall Γ B A, Var152 Γ A -> Var152 (snoc152 Γ B) A)
   , Var152 Γ A.

Definition vz152 {Γ A} : Var152 (snoc152 Γ A) A
 := fun Var152 vz152 vs => vz152 _ _.

Definition vs152 {Γ B A} : Var152 Γ A -> Var152 (snoc152 Γ B) A
 := fun x Var152 vz152 vs152 => vs152 _ _ _ (x Var152 vz152 vs152).

Definition Tm152 : Con152 -> Ty152 -> Set
 := fun Γ A =>
   forall (Tm152  : Con152 -> Ty152 -> Set)
     (var   : forall Γ A     , Var152 Γ A -> Tm152 Γ A)
     (lam   : forall Γ A B   , Tm152 (snoc152 Γ A) B -> Tm152 Γ (arr152 A B))
     (app   : forall Γ A B   , Tm152 Γ (arr152 A B) -> Tm152 Γ A -> Tm152 Γ B)
   , Tm152 Γ A.

Definition var152 {Γ A} : Var152 Γ A -> Tm152 Γ A
 := fun x Tm152 var152 lam app =>
     var152 _ _ x.

Definition lam152 {Γ A B} : Tm152 (snoc152 Γ A) B -> Tm152 Γ (arr152 A B)
 := fun t Tm152 var152 lam152 app =>
     lam152 _ _ _ (t Tm152 var152 lam152 app).

Definition app152 {Γ A B} : Tm152 Γ (arr152 A B) -> Tm152 Γ A -> Tm152 Γ B
 := fun t u Tm152 var152 lam152 app152 =>
     app152 _ _ _
         (t Tm152 var152 lam152 app152)
         (u Tm152 var152 lam152 app152).

Definition v0152 {Γ A} : Tm152 (snoc152 Γ A) A
 := var152 vz152.

Definition v1152 {Γ A B} : Tm152 (snoc152 (snoc152 Γ A) B) A
 := var152 (vs152 vz152).

Definition v2152 {Γ A B C} : Tm152 (snoc152 (snoc152 (snoc152 Γ A) B) C) A
 := var152 (vs152 (vs152 vz152)).

Definition v3152 {Γ A B C D} : Tm152 (snoc152 (snoc152 (snoc152 (snoc152 Γ A) B) C) D) A
 := var152 (vs152 (vs152 (vs152 vz152))).

Definition v4152 {Γ A B C D E} : Tm152 (snoc152 (snoc152 (snoc152 (snoc152 (snoc152 Γ A) B) C) D) E) A
 := var152 (vs152 (vs152 (vs152 (vs152 vz152)))).

Definition test152 {Γ A} : Tm152 Γ (arr152 (arr152 A A) (arr152 A A))
 := lam152 (lam152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 v0152))))))).


Definition Ty153 : Set
 := forall (Ty153 : Set)
      (base   : Ty153)
      (arr : Ty153 -> Ty153 -> Ty153)
    , Ty153.

Definition base153 : Ty153 := fun _ base153 _ => base153.

Definition arr153 : Ty153 -> Ty153 -> Ty153
 := fun A B Ty153 base153 arr153 =>
     arr153 (A Ty153 base153 arr153) (B Ty153 base153 arr153).

Definition Con153 : Set
 := forall (Con153  : Set)
      (nil  : Con153)
      (snoc : Con153 -> Ty153 -> Con153)
    , Con153.

Definition nil153 : Con153
 := fun Con153 nil153 snoc => nil153.

Definition snoc153 : Con153 -> Ty153 -> Con153
 := fun Γ A Con153 nil153 snoc153 => snoc153 (Γ Con153 nil153 snoc153) A.

Definition Var153 : Con153 -> Ty153 -> Set
 := fun Γ A =>
   forall (Var153 : Con153 -> Ty153 -> Set)
     (vz  : forall Γ A, Var153 (snoc153 Γ A) A)
     (vs  : forall Γ B A, Var153 Γ A -> Var153 (snoc153 Γ B) A)
   , Var153 Γ A.

Definition vz153 {Γ A} : Var153 (snoc153 Γ A) A
 := fun Var153 vz153 vs => vz153 _ _.

Definition vs153 {Γ B A} : Var153 Γ A -> Var153 (snoc153 Γ B) A
 := fun x Var153 vz153 vs153 => vs153 _ _ _ (x Var153 vz153 vs153).

Definition Tm153 : Con153 -> Ty153 -> Set
 := fun Γ A =>
   forall (Tm153  : Con153 -> Ty153 -> Set)
     (var   : forall Γ A     , Var153 Γ A -> Tm153 Γ A)
     (lam   : forall Γ A B   , Tm153 (snoc153 Γ A) B -> Tm153 Γ (arr153 A B))
     (app   : forall Γ A B   , Tm153 Γ (arr153 A B) -> Tm153 Γ A -> Tm153 Γ B)
   , Tm153 Γ A.

Definition var153 {Γ A} : Var153 Γ A -> Tm153 Γ A
 := fun x Tm153 var153 lam app =>
     var153 _ _ x.

Definition lam153 {Γ A B} : Tm153 (snoc153 Γ A) B -> Tm153 Γ (arr153 A B)
 := fun t Tm153 var153 lam153 app =>
     lam153 _ _ _ (t Tm153 var153 lam153 app).

Definition app153 {Γ A B} : Tm153 Γ (arr153 A B) -> Tm153 Γ A -> Tm153 Γ B
 := fun t u Tm153 var153 lam153 app153 =>
     app153 _ _ _
         (t Tm153 var153 lam153 app153)
         (u Tm153 var153 lam153 app153).

Definition v0153 {Γ A} : Tm153 (snoc153 Γ A) A
 := var153 vz153.

Definition v1153 {Γ A B} : Tm153 (snoc153 (snoc153 Γ A) B) A
 := var153 (vs153 vz153).

Definition v2153 {Γ A B C} : Tm153 (snoc153 (snoc153 (snoc153 Γ A) B) C) A
 := var153 (vs153 (vs153 vz153)).

Definition v3153 {Γ A B C D} : Tm153 (snoc153 (snoc153 (snoc153 (snoc153 Γ A) B) C) D) A
 := var153 (vs153 (vs153 (vs153 vz153))).

Definition v4153 {Γ A B C D E} : Tm153 (snoc153 (snoc153 (snoc153 (snoc153 (snoc153 Γ A) B) C) D) E) A
 := var153 (vs153 (vs153 (vs153 (vs153 vz153)))).

Definition test153 {Γ A} : Tm153 Γ (arr153 (arr153 A A) (arr153 A A))
 := lam153 (lam153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 v0153))))))).


Definition Ty154 : Set
 := forall (Ty154 : Set)
      (base   : Ty154)
      (arr : Ty154 -> Ty154 -> Ty154)
    , Ty154.

Definition base154 : Ty154 := fun _ base154 _ => base154.

Definition arr154 : Ty154 -> Ty154 -> Ty154
 := fun A B Ty154 base154 arr154 =>
     arr154 (A Ty154 base154 arr154) (B Ty154 base154 arr154).

Definition Con154 : Set
 := forall (Con154  : Set)
      (nil  : Con154)
      (snoc : Con154 -> Ty154 -> Con154)
    , Con154.

Definition nil154 : Con154
 := fun Con154 nil154 snoc => nil154.

Definition snoc154 : Con154 -> Ty154 -> Con154
 := fun Γ A Con154 nil154 snoc154 => snoc154 (Γ Con154 nil154 snoc154) A.

Definition Var154 : Con154 -> Ty154 -> Set
 := fun Γ A =>
   forall (Var154 : Con154 -> Ty154 -> Set)
     (vz  : forall Γ A, Var154 (snoc154 Γ A) A)
     (vs  : forall Γ B A, Var154 Γ A -> Var154 (snoc154 Γ B) A)
   , Var154 Γ A.

Definition vz154 {Γ A} : Var154 (snoc154 Γ A) A
 := fun Var154 vz154 vs => vz154 _ _.

Definition vs154 {Γ B A} : Var154 Γ A -> Var154 (snoc154 Γ B) A
 := fun x Var154 vz154 vs154 => vs154 _ _ _ (x Var154 vz154 vs154).

Definition Tm154 : Con154 -> Ty154 -> Set
 := fun Γ A =>
   forall (Tm154  : Con154 -> Ty154 -> Set)
     (var   : forall Γ A     , Var154 Γ A -> Tm154 Γ A)
     (lam   : forall Γ A B   , Tm154 (snoc154 Γ A) B -> Tm154 Γ (arr154 A B))
     (app   : forall Γ A B   , Tm154 Γ (arr154 A B) -> Tm154 Γ A -> Tm154 Γ B)
   , Tm154 Γ A.

Definition var154 {Γ A} : Var154 Γ A -> Tm154 Γ A
 := fun x Tm154 var154 lam app =>
     var154 _ _ x.

Definition lam154 {Γ A B} : Tm154 (snoc154 Γ A) B -> Tm154 Γ (arr154 A B)
 := fun t Tm154 var154 lam154 app =>
     lam154 _ _ _ (t Tm154 var154 lam154 app).

Definition app154 {Γ A B} : Tm154 Γ (arr154 A B) -> Tm154 Γ A -> Tm154 Γ B
 := fun t u Tm154 var154 lam154 app154 =>
     app154 _ _ _
         (t Tm154 var154 lam154 app154)
         (u Tm154 var154 lam154 app154).

Definition v0154 {Γ A} : Tm154 (snoc154 Γ A) A
 := var154 vz154.

Definition v1154 {Γ A B} : Tm154 (snoc154 (snoc154 Γ A) B) A
 := var154 (vs154 vz154).

Definition v2154 {Γ A B C} : Tm154 (snoc154 (snoc154 (snoc154 Γ A) B) C) A
 := var154 (vs154 (vs154 vz154)).

Definition v3154 {Γ A B C D} : Tm154 (snoc154 (snoc154 (snoc154 (snoc154 Γ A) B) C) D) A
 := var154 (vs154 (vs154 (vs154 vz154))).

Definition v4154 {Γ A B C D E} : Tm154 (snoc154 (snoc154 (snoc154 (snoc154 (snoc154 Γ A) B) C) D) E) A
 := var154 (vs154 (vs154 (vs154 (vs154 vz154)))).

Definition test154 {Γ A} : Tm154 Γ (arr154 (arr154 A A) (arr154 A A))
 := lam154 (lam154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 v0154))))))).


Definition Ty155 : Set
 := forall (Ty155 : Set)
      (base   : Ty155)
      (arr : Ty155 -> Ty155 -> Ty155)
    , Ty155.

Definition base155 : Ty155 := fun _ base155 _ => base155.

Definition arr155 : Ty155 -> Ty155 -> Ty155
 := fun A B Ty155 base155 arr155 =>
     arr155 (A Ty155 base155 arr155) (B Ty155 base155 arr155).

Definition Con155 : Set
 := forall (Con155  : Set)
      (nil  : Con155)
      (snoc : Con155 -> Ty155 -> Con155)
    , Con155.

Definition nil155 : Con155
 := fun Con155 nil155 snoc => nil155.

Definition snoc155 : Con155 -> Ty155 -> Con155
 := fun Γ A Con155 nil155 snoc155 => snoc155 (Γ Con155 nil155 snoc155) A.

Definition Var155 : Con155 -> Ty155 -> Set
 := fun Γ A =>
   forall (Var155 : Con155 -> Ty155 -> Set)
     (vz  : forall Γ A, Var155 (snoc155 Γ A) A)
     (vs  : forall Γ B A, Var155 Γ A -> Var155 (snoc155 Γ B) A)
   , Var155 Γ A.

Definition vz155 {Γ A} : Var155 (snoc155 Γ A) A
 := fun Var155 vz155 vs => vz155 _ _.

Definition vs155 {Γ B A} : Var155 Γ A -> Var155 (snoc155 Γ B) A
 := fun x Var155 vz155 vs155 => vs155 _ _ _ (x Var155 vz155 vs155).

Definition Tm155 : Con155 -> Ty155 -> Set
 := fun Γ A =>
   forall (Tm155  : Con155 -> Ty155 -> Set)
     (var   : forall Γ A     , Var155 Γ A -> Tm155 Γ A)
     (lam   : forall Γ A B   , Tm155 (snoc155 Γ A) B -> Tm155 Γ (arr155 A B))
     (app   : forall Γ A B   , Tm155 Γ (arr155 A B) -> Tm155 Γ A -> Tm155 Γ B)
   , Tm155 Γ A.

Definition var155 {Γ A} : Var155 Γ A -> Tm155 Γ A
 := fun x Tm155 var155 lam app =>
     var155 _ _ x.

Definition lam155 {Γ A B} : Tm155 (snoc155 Γ A) B -> Tm155 Γ (arr155 A B)
 := fun t Tm155 var155 lam155 app =>
     lam155 _ _ _ (t Tm155 var155 lam155 app).

Definition app155 {Γ A B} : Tm155 Γ (arr155 A B) -> Tm155 Γ A -> Tm155 Γ B
 := fun t u Tm155 var155 lam155 app155 =>
     app155 _ _ _
         (t Tm155 var155 lam155 app155)
         (u Tm155 var155 lam155 app155).

Definition v0155 {Γ A} : Tm155 (snoc155 Γ A) A
 := var155 vz155.

Definition v1155 {Γ A B} : Tm155 (snoc155 (snoc155 Γ A) B) A
 := var155 (vs155 vz155).

Definition v2155 {Γ A B C} : Tm155 (snoc155 (snoc155 (snoc155 Γ A) B) C) A
 := var155 (vs155 (vs155 vz155)).

Definition v3155 {Γ A B C D} : Tm155 (snoc155 (snoc155 (snoc155 (snoc155 Γ A) B) C) D) A
 := var155 (vs155 (vs155 (vs155 vz155))).

Definition v4155 {Γ A B C D E} : Tm155 (snoc155 (snoc155 (snoc155 (snoc155 (snoc155 Γ A) B) C) D) E) A
 := var155 (vs155 (vs155 (vs155 (vs155 vz155)))).

Definition test155 {Γ A} : Tm155 Γ (arr155 (arr155 A A) (arr155 A A))
 := lam155 (lam155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 v0155))))))).


Definition Ty156 : Set
 := forall (Ty156 : Set)
      (base   : Ty156)
      (arr : Ty156 -> Ty156 -> Ty156)
    , Ty156.

Definition base156 : Ty156 := fun _ base156 _ => base156.

Definition arr156 : Ty156 -> Ty156 -> Ty156
 := fun A B Ty156 base156 arr156 =>
     arr156 (A Ty156 base156 arr156) (B Ty156 base156 arr156).

Definition Con156 : Set
 := forall (Con156  : Set)
      (nil  : Con156)
      (snoc : Con156 -> Ty156 -> Con156)
    , Con156.

Definition nil156 : Con156
 := fun Con156 nil156 snoc => nil156.

Definition snoc156 : Con156 -> Ty156 -> Con156
 := fun Γ A Con156 nil156 snoc156 => snoc156 (Γ Con156 nil156 snoc156) A.

Definition Var156 : Con156 -> Ty156 -> Set
 := fun Γ A =>
   forall (Var156 : Con156 -> Ty156 -> Set)
     (vz  : forall Γ A, Var156 (snoc156 Γ A) A)
     (vs  : forall Γ B A, Var156 Γ A -> Var156 (snoc156 Γ B) A)
   , Var156 Γ A.

Definition vz156 {Γ A} : Var156 (snoc156 Γ A) A
 := fun Var156 vz156 vs => vz156 _ _.

Definition vs156 {Γ B A} : Var156 Γ A -> Var156 (snoc156 Γ B) A
 := fun x Var156 vz156 vs156 => vs156 _ _ _ (x Var156 vz156 vs156).

Definition Tm156 : Con156 -> Ty156 -> Set
 := fun Γ A =>
   forall (Tm156  : Con156 -> Ty156 -> Set)
     (var   : forall Γ A     , Var156 Γ A -> Tm156 Γ A)
     (lam   : forall Γ A B   , Tm156 (snoc156 Γ A) B -> Tm156 Γ (arr156 A B))
     (app   : forall Γ A B   , Tm156 Γ (arr156 A B) -> Tm156 Γ A -> Tm156 Γ B)
   , Tm156 Γ A.

Definition var156 {Γ A} : Var156 Γ A -> Tm156 Γ A
 := fun x Tm156 var156 lam app =>
     var156 _ _ x.

Definition lam156 {Γ A B} : Tm156 (snoc156 Γ A) B -> Tm156 Γ (arr156 A B)
 := fun t Tm156 var156 lam156 app =>
     lam156 _ _ _ (t Tm156 var156 lam156 app).

Definition app156 {Γ A B} : Tm156 Γ (arr156 A B) -> Tm156 Γ A -> Tm156 Γ B
 := fun t u Tm156 var156 lam156 app156 =>
     app156 _ _ _
         (t Tm156 var156 lam156 app156)
         (u Tm156 var156 lam156 app156).

Definition v0156 {Γ A} : Tm156 (snoc156 Γ A) A
 := var156 vz156.

Definition v1156 {Γ A B} : Tm156 (snoc156 (snoc156 Γ A) B) A
 := var156 (vs156 vz156).

Definition v2156 {Γ A B C} : Tm156 (snoc156 (snoc156 (snoc156 Γ A) B) C) A
 := var156 (vs156 (vs156 vz156)).

Definition v3156 {Γ A B C D} : Tm156 (snoc156 (snoc156 (snoc156 (snoc156 Γ A) B) C) D) A
 := var156 (vs156 (vs156 (vs156 vz156))).

Definition v4156 {Γ A B C D E} : Tm156 (snoc156 (snoc156 (snoc156 (snoc156 (snoc156 Γ A) B) C) D) E) A
 := var156 (vs156 (vs156 (vs156 (vs156 vz156)))).

Definition test156 {Γ A} : Tm156 Γ (arr156 (arr156 A A) (arr156 A A))
 := lam156 (lam156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 v0156))))))).


Definition Ty157 : Set
 := forall (Ty157 : Set)
      (base   : Ty157)
      (arr : Ty157 -> Ty157 -> Ty157)
    , Ty157.

Definition base157 : Ty157 := fun _ base157 _ => base157.

Definition arr157 : Ty157 -> Ty157 -> Ty157
 := fun A B Ty157 base157 arr157 =>
     arr157 (A Ty157 base157 arr157) (B Ty157 base157 arr157).

Definition Con157 : Set
 := forall (Con157  : Set)
      (nil  : Con157)
      (snoc : Con157 -> Ty157 -> Con157)
    , Con157.

Definition nil157 : Con157
 := fun Con157 nil157 snoc => nil157.

Definition snoc157 : Con157 -> Ty157 -> Con157
 := fun Γ A Con157 nil157 snoc157 => snoc157 (Γ Con157 nil157 snoc157) A.

Definition Var157 : Con157 -> Ty157 -> Set
 := fun Γ A =>
   forall (Var157 : Con157 -> Ty157 -> Set)
     (vz  : forall Γ A, Var157 (snoc157 Γ A) A)
     (vs  : forall Γ B A, Var157 Γ A -> Var157 (snoc157 Γ B) A)
   , Var157 Γ A.

Definition vz157 {Γ A} : Var157 (snoc157 Γ A) A
 := fun Var157 vz157 vs => vz157 _ _.

Definition vs157 {Γ B A} : Var157 Γ A -> Var157 (snoc157 Γ B) A
 := fun x Var157 vz157 vs157 => vs157 _ _ _ (x Var157 vz157 vs157).

Definition Tm157 : Con157 -> Ty157 -> Set
 := fun Γ A =>
   forall (Tm157  : Con157 -> Ty157 -> Set)
     (var   : forall Γ A     , Var157 Γ A -> Tm157 Γ A)
     (lam   : forall Γ A B   , Tm157 (snoc157 Γ A) B -> Tm157 Γ (arr157 A B))
     (app   : forall Γ A B   , Tm157 Γ (arr157 A B) -> Tm157 Γ A -> Tm157 Γ B)
   , Tm157 Γ A.

Definition var157 {Γ A} : Var157 Γ A -> Tm157 Γ A
 := fun x Tm157 var157 lam app =>
     var157 _ _ x.

Definition lam157 {Γ A B} : Tm157 (snoc157 Γ A) B -> Tm157 Γ (arr157 A B)
 := fun t Tm157 var157 lam157 app =>
     lam157 _ _ _ (t Tm157 var157 lam157 app).

Definition app157 {Γ A B} : Tm157 Γ (arr157 A B) -> Tm157 Γ A -> Tm157 Γ B
 := fun t u Tm157 var157 lam157 app157 =>
     app157 _ _ _
         (t Tm157 var157 lam157 app157)
         (u Tm157 var157 lam157 app157).

Definition v0157 {Γ A} : Tm157 (snoc157 Γ A) A
 := var157 vz157.

Definition v1157 {Γ A B} : Tm157 (snoc157 (snoc157 Γ A) B) A
 := var157 (vs157 vz157).

Definition v2157 {Γ A B C} : Tm157 (snoc157 (snoc157 (snoc157 Γ A) B) C) A
 := var157 (vs157 (vs157 vz157)).

Definition v3157 {Γ A B C D} : Tm157 (snoc157 (snoc157 (snoc157 (snoc157 Γ A) B) C) D) A
 := var157 (vs157 (vs157 (vs157 vz157))).

Definition v4157 {Γ A B C D E} : Tm157 (snoc157 (snoc157 (snoc157 (snoc157 (snoc157 Γ A) B) C) D) E) A
 := var157 (vs157 (vs157 (vs157 (vs157 vz157)))).

Definition test157 {Γ A} : Tm157 Γ (arr157 (arr157 A A) (arr157 A A))
 := lam157 (lam157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 v0157))))))).


Definition Ty158 : Set
 := forall (Ty158 : Set)
      (base   : Ty158)
      (arr : Ty158 -> Ty158 -> Ty158)
    , Ty158.

Definition base158 : Ty158 := fun _ base158 _ => base158.

Definition arr158 : Ty158 -> Ty158 -> Ty158
 := fun A B Ty158 base158 arr158 =>
     arr158 (A Ty158 base158 arr158) (B Ty158 base158 arr158).

Definition Con158 : Set
 := forall (Con158  : Set)
      (nil  : Con158)
      (snoc : Con158 -> Ty158 -> Con158)
    , Con158.

Definition nil158 : Con158
 := fun Con158 nil158 snoc => nil158.

Definition snoc158 : Con158 -> Ty158 -> Con158
 := fun Γ A Con158 nil158 snoc158 => snoc158 (Γ Con158 nil158 snoc158) A.

Definition Var158 : Con158 -> Ty158 -> Set
 := fun Γ A =>
   forall (Var158 : Con158 -> Ty158 -> Set)
     (vz  : forall Γ A, Var158 (snoc158 Γ A) A)
     (vs  : forall Γ B A, Var158 Γ A -> Var158 (snoc158 Γ B) A)
   , Var158 Γ A.

Definition vz158 {Γ A} : Var158 (snoc158 Γ A) A
 := fun Var158 vz158 vs => vz158 _ _.

Definition vs158 {Γ B A} : Var158 Γ A -> Var158 (snoc158 Γ B) A
 := fun x Var158 vz158 vs158 => vs158 _ _ _ (x Var158 vz158 vs158).

Definition Tm158 : Con158 -> Ty158 -> Set
 := fun Γ A =>
   forall (Tm158  : Con158 -> Ty158 -> Set)
     (var   : forall Γ A     , Var158 Γ A -> Tm158 Γ A)
     (lam   : forall Γ A B   , Tm158 (snoc158 Γ A) B -> Tm158 Γ (arr158 A B))
     (app   : forall Γ A B   , Tm158 Γ (arr158 A B) -> Tm158 Γ A -> Tm158 Γ B)
   , Tm158 Γ A.

Definition var158 {Γ A} : Var158 Γ A -> Tm158 Γ A
 := fun x Tm158 var158 lam app =>
     var158 _ _ x.

Definition lam158 {Γ A B} : Tm158 (snoc158 Γ A) B -> Tm158 Γ (arr158 A B)
 := fun t Tm158 var158 lam158 app =>
     lam158 _ _ _ (t Tm158 var158 lam158 app).

Definition app158 {Γ A B} : Tm158 Γ (arr158 A B) -> Tm158 Γ A -> Tm158 Γ B
 := fun t u Tm158 var158 lam158 app158 =>
     app158 _ _ _
         (t Tm158 var158 lam158 app158)
         (u Tm158 var158 lam158 app158).

Definition v0158 {Γ A} : Tm158 (snoc158 Γ A) A
 := var158 vz158.

Definition v1158 {Γ A B} : Tm158 (snoc158 (snoc158 Γ A) B) A
 := var158 (vs158 vz158).

Definition v2158 {Γ A B C} : Tm158 (snoc158 (snoc158 (snoc158 Γ A) B) C) A
 := var158 (vs158 (vs158 vz158)).

Definition v3158 {Γ A B C D} : Tm158 (snoc158 (snoc158 (snoc158 (snoc158 Γ A) B) C) D) A
 := var158 (vs158 (vs158 (vs158 vz158))).

Definition v4158 {Γ A B C D E} : Tm158 (snoc158 (snoc158 (snoc158 (snoc158 (snoc158 Γ A) B) C) D) E) A
 := var158 (vs158 (vs158 (vs158 (vs158 vz158)))).

Definition test158 {Γ A} : Tm158 Γ (arr158 (arr158 A A) (arr158 A A))
 := lam158 (lam158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 v0158))))))).


Definition Ty159 : Set
 := forall (Ty159 : Set)
      (base   : Ty159)
      (arr : Ty159 -> Ty159 -> Ty159)
    , Ty159.

Definition base159 : Ty159 := fun _ base159 _ => base159.

Definition arr159 : Ty159 -> Ty159 -> Ty159
 := fun A B Ty159 base159 arr159 =>
     arr159 (A Ty159 base159 arr159) (B Ty159 base159 arr159).

Definition Con159 : Set
 := forall (Con159  : Set)
      (nil  : Con159)
      (snoc : Con159 -> Ty159 -> Con159)
    , Con159.

Definition nil159 : Con159
 := fun Con159 nil159 snoc => nil159.

Definition snoc159 : Con159 -> Ty159 -> Con159
 := fun Γ A Con159 nil159 snoc159 => snoc159 (Γ Con159 nil159 snoc159) A.

Definition Var159 : Con159 -> Ty159 -> Set
 := fun Γ A =>
   forall (Var159 : Con159 -> Ty159 -> Set)
     (vz  : forall Γ A, Var159 (snoc159 Γ A) A)
     (vs  : forall Γ B A, Var159 Γ A -> Var159 (snoc159 Γ B) A)
   , Var159 Γ A.

Definition vz159 {Γ A} : Var159 (snoc159 Γ A) A
 := fun Var159 vz159 vs => vz159 _ _.

Definition vs159 {Γ B A} : Var159 Γ A -> Var159 (snoc159 Γ B) A
 := fun x Var159 vz159 vs159 => vs159 _ _ _ (x Var159 vz159 vs159).

Definition Tm159 : Con159 -> Ty159 -> Set
 := fun Γ A =>
   forall (Tm159  : Con159 -> Ty159 -> Set)
     (var   : forall Γ A     , Var159 Γ A -> Tm159 Γ A)
     (lam   : forall Γ A B   , Tm159 (snoc159 Γ A) B -> Tm159 Γ (arr159 A B))
     (app   : forall Γ A B   , Tm159 Γ (arr159 A B) -> Tm159 Γ A -> Tm159 Γ B)
   , Tm159 Γ A.

Definition var159 {Γ A} : Var159 Γ A -> Tm159 Γ A
 := fun x Tm159 var159 lam app =>
     var159 _ _ x.

Definition lam159 {Γ A B} : Tm159 (snoc159 Γ A) B -> Tm159 Γ (arr159 A B)
 := fun t Tm159 var159 lam159 app =>
     lam159 _ _ _ (t Tm159 var159 lam159 app).

Definition app159 {Γ A B} : Tm159 Γ (arr159 A B) -> Tm159 Γ A -> Tm159 Γ B
 := fun t u Tm159 var159 lam159 app159 =>
     app159 _ _ _
         (t Tm159 var159 lam159 app159)
         (u Tm159 var159 lam159 app159).

Definition v0159 {Γ A} : Tm159 (snoc159 Γ A) A
 := var159 vz159.

Definition v1159 {Γ A B} : Tm159 (snoc159 (snoc159 Γ A) B) A
 := var159 (vs159 vz159).

Definition v2159 {Γ A B C} : Tm159 (snoc159 (snoc159 (snoc159 Γ A) B) C) A
 := var159 (vs159 (vs159 vz159)).

Definition v3159 {Γ A B C D} : Tm159 (snoc159 (snoc159 (snoc159 (snoc159 Γ A) B) C) D) A
 := var159 (vs159 (vs159 (vs159 vz159))).

Definition v4159 {Γ A B C D E} : Tm159 (snoc159 (snoc159 (snoc159 (snoc159 (snoc159 Γ A) B) C) D) E) A
 := var159 (vs159 (vs159 (vs159 (vs159 vz159)))).

Definition test159 {Γ A} : Tm159 Γ (arr159 (arr159 A A) (arr159 A A))
 := lam159 (lam159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 v0159))))))).


Definition Ty160 : Set
 := forall (Ty160 : Set)
      (base   : Ty160)
      (arr : Ty160 -> Ty160 -> Ty160)
    , Ty160.

Definition base160 : Ty160 := fun _ base160 _ => base160.

Definition arr160 : Ty160 -> Ty160 -> Ty160
 := fun A B Ty160 base160 arr160 =>
     arr160 (A Ty160 base160 arr160) (B Ty160 base160 arr160).

Definition Con160 : Set
 := forall (Con160  : Set)
      (nil  : Con160)
      (snoc : Con160 -> Ty160 -> Con160)
    , Con160.

Definition nil160 : Con160
 := fun Con160 nil160 snoc => nil160.

Definition snoc160 : Con160 -> Ty160 -> Con160
 := fun Γ A Con160 nil160 snoc160 => snoc160 (Γ Con160 nil160 snoc160) A.

Definition Var160 : Con160 -> Ty160 -> Set
 := fun Γ A =>
   forall (Var160 : Con160 -> Ty160 -> Set)
     (vz  : forall Γ A, Var160 (snoc160 Γ A) A)
     (vs  : forall Γ B A, Var160 Γ A -> Var160 (snoc160 Γ B) A)
   , Var160 Γ A.

Definition vz160 {Γ A} : Var160 (snoc160 Γ A) A
 := fun Var160 vz160 vs => vz160 _ _.

Definition vs160 {Γ B A} : Var160 Γ A -> Var160 (snoc160 Γ B) A
 := fun x Var160 vz160 vs160 => vs160 _ _ _ (x Var160 vz160 vs160).

Definition Tm160 : Con160 -> Ty160 -> Set
 := fun Γ A =>
   forall (Tm160  : Con160 -> Ty160 -> Set)
     (var   : forall Γ A     , Var160 Γ A -> Tm160 Γ A)
     (lam   : forall Γ A B   , Tm160 (snoc160 Γ A) B -> Tm160 Γ (arr160 A B))
     (app   : forall Γ A B   , Tm160 Γ (arr160 A B) -> Tm160 Γ A -> Tm160 Γ B)
   , Tm160 Γ A.

Definition var160 {Γ A} : Var160 Γ A -> Tm160 Γ A
 := fun x Tm160 var160 lam app =>
     var160 _ _ x.

Definition lam160 {Γ A B} : Tm160 (snoc160 Γ A) B -> Tm160 Γ (arr160 A B)
 := fun t Tm160 var160 lam160 app =>
     lam160 _ _ _ (t Tm160 var160 lam160 app).

Definition app160 {Γ A B} : Tm160 Γ (arr160 A B) -> Tm160 Γ A -> Tm160 Γ B
 := fun t u Tm160 var160 lam160 app160 =>
     app160 _ _ _
         (t Tm160 var160 lam160 app160)
         (u Tm160 var160 lam160 app160).

Definition v0160 {Γ A} : Tm160 (snoc160 Γ A) A
 := var160 vz160.

Definition v1160 {Γ A B} : Tm160 (snoc160 (snoc160 Γ A) B) A
 := var160 (vs160 vz160).

Definition v2160 {Γ A B C} : Tm160 (snoc160 (snoc160 (snoc160 Γ A) B) C) A
 := var160 (vs160 (vs160 vz160)).

Definition v3160 {Γ A B C D} : Tm160 (snoc160 (snoc160 (snoc160 (snoc160 Γ A) B) C) D) A
 := var160 (vs160 (vs160 (vs160 vz160))).

Definition v4160 {Γ A B C D E} : Tm160 (snoc160 (snoc160 (snoc160 (snoc160 (snoc160 Γ A) B) C) D) E) A
 := var160 (vs160 (vs160 (vs160 (vs160 vz160)))).

Definition test160 {Γ A} : Tm160 Γ (arr160 (arr160 A A) (arr160 A A))
 := lam160 (lam160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 v0160))))))).


Definition Ty161 : Set
 := forall (Ty161 : Set)
      (base   : Ty161)
      (arr : Ty161 -> Ty161 -> Ty161)
    , Ty161.

Definition base161 : Ty161 := fun _ base161 _ => base161.

Definition arr161 : Ty161 -> Ty161 -> Ty161
 := fun A B Ty161 base161 arr161 =>
     arr161 (A Ty161 base161 arr161) (B Ty161 base161 arr161).

Definition Con161 : Set
 := forall (Con161  : Set)
      (nil  : Con161)
      (snoc : Con161 -> Ty161 -> Con161)
    , Con161.

Definition nil161 : Con161
 := fun Con161 nil161 snoc => nil161.

Definition snoc161 : Con161 -> Ty161 -> Con161
 := fun Γ A Con161 nil161 snoc161 => snoc161 (Γ Con161 nil161 snoc161) A.

Definition Var161 : Con161 -> Ty161 -> Set
 := fun Γ A =>
   forall (Var161 : Con161 -> Ty161 -> Set)
     (vz  : forall Γ A, Var161 (snoc161 Γ A) A)
     (vs  : forall Γ B A, Var161 Γ A -> Var161 (snoc161 Γ B) A)
   , Var161 Γ A.

Definition vz161 {Γ A} : Var161 (snoc161 Γ A) A
 := fun Var161 vz161 vs => vz161 _ _.

Definition vs161 {Γ B A} : Var161 Γ A -> Var161 (snoc161 Γ B) A
 := fun x Var161 vz161 vs161 => vs161 _ _ _ (x Var161 vz161 vs161).

Definition Tm161 : Con161 -> Ty161 -> Set
 := fun Γ A =>
   forall (Tm161  : Con161 -> Ty161 -> Set)
     (var   : forall Γ A     , Var161 Γ A -> Tm161 Γ A)
     (lam   : forall Γ A B   , Tm161 (snoc161 Γ A) B -> Tm161 Γ (arr161 A B))
     (app   : forall Γ A B   , Tm161 Γ (arr161 A B) -> Tm161 Γ A -> Tm161 Γ B)
   , Tm161 Γ A.

Definition var161 {Γ A} : Var161 Γ A -> Tm161 Γ A
 := fun x Tm161 var161 lam app =>
     var161 _ _ x.

Definition lam161 {Γ A B} : Tm161 (snoc161 Γ A) B -> Tm161 Γ (arr161 A B)
 := fun t Tm161 var161 lam161 app =>
     lam161 _ _ _ (t Tm161 var161 lam161 app).

Definition app161 {Γ A B} : Tm161 Γ (arr161 A B) -> Tm161 Γ A -> Tm161 Γ B
 := fun t u Tm161 var161 lam161 app161 =>
     app161 _ _ _
         (t Tm161 var161 lam161 app161)
         (u Tm161 var161 lam161 app161).

Definition v0161 {Γ A} : Tm161 (snoc161 Γ A) A
 := var161 vz161.

Definition v1161 {Γ A B} : Tm161 (snoc161 (snoc161 Γ A) B) A
 := var161 (vs161 vz161).

Definition v2161 {Γ A B C} : Tm161 (snoc161 (snoc161 (snoc161 Γ A) B) C) A
 := var161 (vs161 (vs161 vz161)).

Definition v3161 {Γ A B C D} : Tm161 (snoc161 (snoc161 (snoc161 (snoc161 Γ A) B) C) D) A
 := var161 (vs161 (vs161 (vs161 vz161))).

Definition v4161 {Γ A B C D E} : Tm161 (snoc161 (snoc161 (snoc161 (snoc161 (snoc161 Γ A) B) C) D) E) A
 := var161 (vs161 (vs161 (vs161 (vs161 vz161)))).

Definition test161 {Γ A} : Tm161 Γ (arr161 (arr161 A A) (arr161 A A))
 := lam161 (lam161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 v0161))))))).


Definition Ty162 : Set
 := forall (Ty162 : Set)
      (base   : Ty162)
      (arr : Ty162 -> Ty162 -> Ty162)
    , Ty162.

Definition base162 : Ty162 := fun _ base162 _ => base162.

Definition arr162 : Ty162 -> Ty162 -> Ty162
 := fun A B Ty162 base162 arr162 =>
     arr162 (A Ty162 base162 arr162) (B Ty162 base162 arr162).

Definition Con162 : Set
 := forall (Con162  : Set)
      (nil  : Con162)
      (snoc : Con162 -> Ty162 -> Con162)
    , Con162.

Definition nil162 : Con162
 := fun Con162 nil162 snoc => nil162.

Definition snoc162 : Con162 -> Ty162 -> Con162
 := fun Γ A Con162 nil162 snoc162 => snoc162 (Γ Con162 nil162 snoc162) A.

Definition Var162 : Con162 -> Ty162 -> Set
 := fun Γ A =>
   forall (Var162 : Con162 -> Ty162 -> Set)
     (vz  : forall Γ A, Var162 (snoc162 Γ A) A)
     (vs  : forall Γ B A, Var162 Γ A -> Var162 (snoc162 Γ B) A)
   , Var162 Γ A.

Definition vz162 {Γ A} : Var162 (snoc162 Γ A) A
 := fun Var162 vz162 vs => vz162 _ _.

Definition vs162 {Γ B A} : Var162 Γ A -> Var162 (snoc162 Γ B) A
 := fun x Var162 vz162 vs162 => vs162 _ _ _ (x Var162 vz162 vs162).

Definition Tm162 : Con162 -> Ty162 -> Set
 := fun Γ A =>
   forall (Tm162  : Con162 -> Ty162 -> Set)
     (var   : forall Γ A     , Var162 Γ A -> Tm162 Γ A)
     (lam   : forall Γ A B   , Tm162 (snoc162 Γ A) B -> Tm162 Γ (arr162 A B))
     (app   : forall Γ A B   , Tm162 Γ (arr162 A B) -> Tm162 Γ A -> Tm162 Γ B)
   , Tm162 Γ A.

Definition var162 {Γ A} : Var162 Γ A -> Tm162 Γ A
 := fun x Tm162 var162 lam app =>
     var162 _ _ x.

Definition lam162 {Γ A B} : Tm162 (snoc162 Γ A) B -> Tm162 Γ (arr162 A B)
 := fun t Tm162 var162 lam162 app =>
     lam162 _ _ _ (t Tm162 var162 lam162 app).

Definition app162 {Γ A B} : Tm162 Γ (arr162 A B) -> Tm162 Γ A -> Tm162 Γ B
 := fun t u Tm162 var162 lam162 app162 =>
     app162 _ _ _
         (t Tm162 var162 lam162 app162)
         (u Tm162 var162 lam162 app162).

Definition v0162 {Γ A} : Tm162 (snoc162 Γ A) A
 := var162 vz162.

Definition v1162 {Γ A B} : Tm162 (snoc162 (snoc162 Γ A) B) A
 := var162 (vs162 vz162).

Definition v2162 {Γ A B C} : Tm162 (snoc162 (snoc162 (snoc162 Γ A) B) C) A
 := var162 (vs162 (vs162 vz162)).

Definition v3162 {Γ A B C D} : Tm162 (snoc162 (snoc162 (snoc162 (snoc162 Γ A) B) C) D) A
 := var162 (vs162 (vs162 (vs162 vz162))).

Definition v4162 {Γ A B C D E} : Tm162 (snoc162 (snoc162 (snoc162 (snoc162 (snoc162 Γ A) B) C) D) E) A
 := var162 (vs162 (vs162 (vs162 (vs162 vz162)))).

Definition test162 {Γ A} : Tm162 Γ (arr162 (arr162 A A) (arr162 A A))
 := lam162 (lam162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 v0162))))))).


Definition Ty163 : Set
 := forall (Ty163 : Set)
      (base   : Ty163)
      (arr : Ty163 -> Ty163 -> Ty163)
    , Ty163.

Definition base163 : Ty163 := fun _ base163 _ => base163.

Definition arr163 : Ty163 -> Ty163 -> Ty163
 := fun A B Ty163 base163 arr163 =>
     arr163 (A Ty163 base163 arr163) (B Ty163 base163 arr163).

Definition Con163 : Set
 := forall (Con163  : Set)
      (nil  : Con163)
      (snoc : Con163 -> Ty163 -> Con163)
    , Con163.

Definition nil163 : Con163
 := fun Con163 nil163 snoc => nil163.

Definition snoc163 : Con163 -> Ty163 -> Con163
 := fun Γ A Con163 nil163 snoc163 => snoc163 (Γ Con163 nil163 snoc163) A.

Definition Var163 : Con163 -> Ty163 -> Set
 := fun Γ A =>
   forall (Var163 : Con163 -> Ty163 -> Set)
     (vz  : forall Γ A, Var163 (snoc163 Γ A) A)
     (vs  : forall Γ B A, Var163 Γ A -> Var163 (snoc163 Γ B) A)
   , Var163 Γ A.

Definition vz163 {Γ A} : Var163 (snoc163 Γ A) A
 := fun Var163 vz163 vs => vz163 _ _.

Definition vs163 {Γ B A} : Var163 Γ A -> Var163 (snoc163 Γ B) A
 := fun x Var163 vz163 vs163 => vs163 _ _ _ (x Var163 vz163 vs163).

Definition Tm163 : Con163 -> Ty163 -> Set
 := fun Γ A =>
   forall (Tm163  : Con163 -> Ty163 -> Set)
     (var   : forall Γ A     , Var163 Γ A -> Tm163 Γ A)
     (lam   : forall Γ A B   , Tm163 (snoc163 Γ A) B -> Tm163 Γ (arr163 A B))
     (app   : forall Γ A B   , Tm163 Γ (arr163 A B) -> Tm163 Γ A -> Tm163 Γ B)
   , Tm163 Γ A.

Definition var163 {Γ A} : Var163 Γ A -> Tm163 Γ A
 := fun x Tm163 var163 lam app =>
     var163 _ _ x.

Definition lam163 {Γ A B} : Tm163 (snoc163 Γ A) B -> Tm163 Γ (arr163 A B)
 := fun t Tm163 var163 lam163 app =>
     lam163 _ _ _ (t Tm163 var163 lam163 app).

Definition app163 {Γ A B} : Tm163 Γ (arr163 A B) -> Tm163 Γ A -> Tm163 Γ B
 := fun t u Tm163 var163 lam163 app163 =>
     app163 _ _ _
         (t Tm163 var163 lam163 app163)
         (u Tm163 var163 lam163 app163).

Definition v0163 {Γ A} : Tm163 (snoc163 Γ A) A
 := var163 vz163.

Definition v1163 {Γ A B} : Tm163 (snoc163 (snoc163 Γ A) B) A
 := var163 (vs163 vz163).

Definition v2163 {Γ A B C} : Tm163 (snoc163 (snoc163 (snoc163 Γ A) B) C) A
 := var163 (vs163 (vs163 vz163)).

Definition v3163 {Γ A B C D} : Tm163 (snoc163 (snoc163 (snoc163 (snoc163 Γ A) B) C) D) A
 := var163 (vs163 (vs163 (vs163 vz163))).

Definition v4163 {Γ A B C D E} : Tm163 (snoc163 (snoc163 (snoc163 (snoc163 (snoc163 Γ A) B) C) D) E) A
 := var163 (vs163 (vs163 (vs163 (vs163 vz163)))).

Definition test163 {Γ A} : Tm163 Γ (arr163 (arr163 A A) (arr163 A A))
 := lam163 (lam163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 v0163))))))).


Definition Ty164 : Set
 := forall (Ty164 : Set)
      (base   : Ty164)
      (arr : Ty164 -> Ty164 -> Ty164)
    , Ty164.

Definition base164 : Ty164 := fun _ base164 _ => base164.

Definition arr164 : Ty164 -> Ty164 -> Ty164
 := fun A B Ty164 base164 arr164 =>
     arr164 (A Ty164 base164 arr164) (B Ty164 base164 arr164).

Definition Con164 : Set
 := forall (Con164  : Set)
      (nil  : Con164)
      (snoc : Con164 -> Ty164 -> Con164)
    , Con164.

Definition nil164 : Con164
 := fun Con164 nil164 snoc => nil164.

Definition snoc164 : Con164 -> Ty164 -> Con164
 := fun Γ A Con164 nil164 snoc164 => snoc164 (Γ Con164 nil164 snoc164) A.

Definition Var164 : Con164 -> Ty164 -> Set
 := fun Γ A =>
   forall (Var164 : Con164 -> Ty164 -> Set)
     (vz  : forall Γ A, Var164 (snoc164 Γ A) A)
     (vs  : forall Γ B A, Var164 Γ A -> Var164 (snoc164 Γ B) A)
   , Var164 Γ A.

Definition vz164 {Γ A} : Var164 (snoc164 Γ A) A
 := fun Var164 vz164 vs => vz164 _ _.

Definition vs164 {Γ B A} : Var164 Γ A -> Var164 (snoc164 Γ B) A
 := fun x Var164 vz164 vs164 => vs164 _ _ _ (x Var164 vz164 vs164).

Definition Tm164 : Con164 -> Ty164 -> Set
 := fun Γ A =>
   forall (Tm164  : Con164 -> Ty164 -> Set)
     (var   : forall Γ A     , Var164 Γ A -> Tm164 Γ A)
     (lam   : forall Γ A B   , Tm164 (snoc164 Γ A) B -> Tm164 Γ (arr164 A B))
     (app   : forall Γ A B   , Tm164 Γ (arr164 A B) -> Tm164 Γ A -> Tm164 Γ B)
   , Tm164 Γ A.

Definition var164 {Γ A} : Var164 Γ A -> Tm164 Γ A
 := fun x Tm164 var164 lam app =>
     var164 _ _ x.

Definition lam164 {Γ A B} : Tm164 (snoc164 Γ A) B -> Tm164 Γ (arr164 A B)
 := fun t Tm164 var164 lam164 app =>
     lam164 _ _ _ (t Tm164 var164 lam164 app).

Definition app164 {Γ A B} : Tm164 Γ (arr164 A B) -> Tm164 Γ A -> Tm164 Γ B
 := fun t u Tm164 var164 lam164 app164 =>
     app164 _ _ _
         (t Tm164 var164 lam164 app164)
         (u Tm164 var164 lam164 app164).

Definition v0164 {Γ A} : Tm164 (snoc164 Γ A) A
 := var164 vz164.

Definition v1164 {Γ A B} : Tm164 (snoc164 (snoc164 Γ A) B) A
 := var164 (vs164 vz164).

Definition v2164 {Γ A B C} : Tm164 (snoc164 (snoc164 (snoc164 Γ A) B) C) A
 := var164 (vs164 (vs164 vz164)).

Definition v3164 {Γ A B C D} : Tm164 (snoc164 (snoc164 (snoc164 (snoc164 Γ A) B) C) D) A
 := var164 (vs164 (vs164 (vs164 vz164))).

Definition v4164 {Γ A B C D E} : Tm164 (snoc164 (snoc164 (snoc164 (snoc164 (snoc164 Γ A) B) C) D) E) A
 := var164 (vs164 (vs164 (vs164 (vs164 vz164)))).

Definition test164 {Γ A} : Tm164 Γ (arr164 (arr164 A A) (arr164 A A))
 := lam164 (lam164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 v0164))))))).


Definition Ty165 : Set
 := forall (Ty165 : Set)
      (base   : Ty165)
      (arr : Ty165 -> Ty165 -> Ty165)
    , Ty165.

Definition base165 : Ty165 := fun _ base165 _ => base165.

Definition arr165 : Ty165 -> Ty165 -> Ty165
 := fun A B Ty165 base165 arr165 =>
     arr165 (A Ty165 base165 arr165) (B Ty165 base165 arr165).

Definition Con165 : Set
 := forall (Con165  : Set)
      (nil  : Con165)
      (snoc : Con165 -> Ty165 -> Con165)
    , Con165.

Definition nil165 : Con165
 := fun Con165 nil165 snoc => nil165.

Definition snoc165 : Con165 -> Ty165 -> Con165
 := fun Γ A Con165 nil165 snoc165 => snoc165 (Γ Con165 nil165 snoc165) A.

Definition Var165 : Con165 -> Ty165 -> Set
 := fun Γ A =>
   forall (Var165 : Con165 -> Ty165 -> Set)
     (vz  : forall Γ A, Var165 (snoc165 Γ A) A)
     (vs  : forall Γ B A, Var165 Γ A -> Var165 (snoc165 Γ B) A)
   , Var165 Γ A.

Definition vz165 {Γ A} : Var165 (snoc165 Γ A) A
 := fun Var165 vz165 vs => vz165 _ _.

Definition vs165 {Γ B A} : Var165 Γ A -> Var165 (snoc165 Γ B) A
 := fun x Var165 vz165 vs165 => vs165 _ _ _ (x Var165 vz165 vs165).

Definition Tm165 : Con165 -> Ty165 -> Set
 := fun Γ A =>
   forall (Tm165  : Con165 -> Ty165 -> Set)
     (var   : forall Γ A     , Var165 Γ A -> Tm165 Γ A)
     (lam   : forall Γ A B   , Tm165 (snoc165 Γ A) B -> Tm165 Γ (arr165 A B))
     (app   : forall Γ A B   , Tm165 Γ (arr165 A B) -> Tm165 Γ A -> Tm165 Γ B)
   , Tm165 Γ A.

Definition var165 {Γ A} : Var165 Γ A -> Tm165 Γ A
 := fun x Tm165 var165 lam app =>
     var165 _ _ x.

Definition lam165 {Γ A B} : Tm165 (snoc165 Γ A) B -> Tm165 Γ (arr165 A B)
 := fun t Tm165 var165 lam165 app =>
     lam165 _ _ _ (t Tm165 var165 lam165 app).

Definition app165 {Γ A B} : Tm165 Γ (arr165 A B) -> Tm165 Γ A -> Tm165 Γ B
 := fun t u Tm165 var165 lam165 app165 =>
     app165 _ _ _
         (t Tm165 var165 lam165 app165)
         (u Tm165 var165 lam165 app165).

Definition v0165 {Γ A} : Tm165 (snoc165 Γ A) A
 := var165 vz165.

Definition v1165 {Γ A B} : Tm165 (snoc165 (snoc165 Γ A) B) A
 := var165 (vs165 vz165).

Definition v2165 {Γ A B C} : Tm165 (snoc165 (snoc165 (snoc165 Γ A) B) C) A
 := var165 (vs165 (vs165 vz165)).

Definition v3165 {Γ A B C D} : Tm165 (snoc165 (snoc165 (snoc165 (snoc165 Γ A) B) C) D) A
 := var165 (vs165 (vs165 (vs165 vz165))).

Definition v4165 {Γ A B C D E} : Tm165 (snoc165 (snoc165 (snoc165 (snoc165 (snoc165 Γ A) B) C) D) E) A
 := var165 (vs165 (vs165 (vs165 (vs165 vz165)))).

Definition test165 {Γ A} : Tm165 Γ (arr165 (arr165 A A) (arr165 A A))
 := lam165 (lam165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 v0165))))))).


Definition Ty166 : Set
 := forall (Ty166 : Set)
      (base   : Ty166)
      (arr : Ty166 -> Ty166 -> Ty166)
    , Ty166.

Definition base166 : Ty166 := fun _ base166 _ => base166.

Definition arr166 : Ty166 -> Ty166 -> Ty166
 := fun A B Ty166 base166 arr166 =>
     arr166 (A Ty166 base166 arr166) (B Ty166 base166 arr166).

Definition Con166 : Set
 := forall (Con166  : Set)
      (nil  : Con166)
      (snoc : Con166 -> Ty166 -> Con166)
    , Con166.

Definition nil166 : Con166
 := fun Con166 nil166 snoc => nil166.

Definition snoc166 : Con166 -> Ty166 -> Con166
 := fun Γ A Con166 nil166 snoc166 => snoc166 (Γ Con166 nil166 snoc166) A.

Definition Var166 : Con166 -> Ty166 -> Set
 := fun Γ A =>
   forall (Var166 : Con166 -> Ty166 -> Set)
     (vz  : forall Γ A, Var166 (snoc166 Γ A) A)
     (vs  : forall Γ B A, Var166 Γ A -> Var166 (snoc166 Γ B) A)
   , Var166 Γ A.

Definition vz166 {Γ A} : Var166 (snoc166 Γ A) A
 := fun Var166 vz166 vs => vz166 _ _.

Definition vs166 {Γ B A} : Var166 Γ A -> Var166 (snoc166 Γ B) A
 := fun x Var166 vz166 vs166 => vs166 _ _ _ (x Var166 vz166 vs166).

Definition Tm166 : Con166 -> Ty166 -> Set
 := fun Γ A =>
   forall (Tm166  : Con166 -> Ty166 -> Set)
     (var   : forall Γ A     , Var166 Γ A -> Tm166 Γ A)
     (lam   : forall Γ A B   , Tm166 (snoc166 Γ A) B -> Tm166 Γ (arr166 A B))
     (app   : forall Γ A B   , Tm166 Γ (arr166 A B) -> Tm166 Γ A -> Tm166 Γ B)
   , Tm166 Γ A.

Definition var166 {Γ A} : Var166 Γ A -> Tm166 Γ A
 := fun x Tm166 var166 lam app =>
     var166 _ _ x.

Definition lam166 {Γ A B} : Tm166 (snoc166 Γ A) B -> Tm166 Γ (arr166 A B)
 := fun t Tm166 var166 lam166 app =>
     lam166 _ _ _ (t Tm166 var166 lam166 app).

Definition app166 {Γ A B} : Tm166 Γ (arr166 A B) -> Tm166 Γ A -> Tm166 Γ B
 := fun t u Tm166 var166 lam166 app166 =>
     app166 _ _ _
         (t Tm166 var166 lam166 app166)
         (u Tm166 var166 lam166 app166).

Definition v0166 {Γ A} : Tm166 (snoc166 Γ A) A
 := var166 vz166.

Definition v1166 {Γ A B} : Tm166 (snoc166 (snoc166 Γ A) B) A
 := var166 (vs166 vz166).

Definition v2166 {Γ A B C} : Tm166 (snoc166 (snoc166 (snoc166 Γ A) B) C) A
 := var166 (vs166 (vs166 vz166)).

Definition v3166 {Γ A B C D} : Tm166 (snoc166 (snoc166 (snoc166 (snoc166 Γ A) B) C) D) A
 := var166 (vs166 (vs166 (vs166 vz166))).

Definition v4166 {Γ A B C D E} : Tm166 (snoc166 (snoc166 (snoc166 (snoc166 (snoc166 Γ A) B) C) D) E) A
 := var166 (vs166 (vs166 (vs166 (vs166 vz166)))).

Definition test166 {Γ A} : Tm166 Γ (arr166 (arr166 A A) (arr166 A A))
 := lam166 (lam166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 v0166))))))).


Definition Ty167 : Set
 := forall (Ty167 : Set)
      (base   : Ty167)
      (arr : Ty167 -> Ty167 -> Ty167)
    , Ty167.

Definition base167 : Ty167 := fun _ base167 _ => base167.

Definition arr167 : Ty167 -> Ty167 -> Ty167
 := fun A B Ty167 base167 arr167 =>
     arr167 (A Ty167 base167 arr167) (B Ty167 base167 arr167).

Definition Con167 : Set
 := forall (Con167  : Set)
      (nil  : Con167)
      (snoc : Con167 -> Ty167 -> Con167)
    , Con167.

Definition nil167 : Con167
 := fun Con167 nil167 snoc => nil167.

Definition snoc167 : Con167 -> Ty167 -> Con167
 := fun Γ A Con167 nil167 snoc167 => snoc167 (Γ Con167 nil167 snoc167) A.

Definition Var167 : Con167 -> Ty167 -> Set
 := fun Γ A =>
   forall (Var167 : Con167 -> Ty167 -> Set)
     (vz  : forall Γ A, Var167 (snoc167 Γ A) A)
     (vs  : forall Γ B A, Var167 Γ A -> Var167 (snoc167 Γ B) A)
   , Var167 Γ A.

Definition vz167 {Γ A} : Var167 (snoc167 Γ A) A
 := fun Var167 vz167 vs => vz167 _ _.

Definition vs167 {Γ B A} : Var167 Γ A -> Var167 (snoc167 Γ B) A
 := fun x Var167 vz167 vs167 => vs167 _ _ _ (x Var167 vz167 vs167).

Definition Tm167 : Con167 -> Ty167 -> Set
 := fun Γ A =>
   forall (Tm167  : Con167 -> Ty167 -> Set)
     (var   : forall Γ A     , Var167 Γ A -> Tm167 Γ A)
     (lam   : forall Γ A B   , Tm167 (snoc167 Γ A) B -> Tm167 Γ (arr167 A B))
     (app   : forall Γ A B   , Tm167 Γ (arr167 A B) -> Tm167 Γ A -> Tm167 Γ B)
   , Tm167 Γ A.

Definition var167 {Γ A} : Var167 Γ A -> Tm167 Γ A
 := fun x Tm167 var167 lam app =>
     var167 _ _ x.

Definition lam167 {Γ A B} : Tm167 (snoc167 Γ A) B -> Tm167 Γ (arr167 A B)
 := fun t Tm167 var167 lam167 app =>
     lam167 _ _ _ (t Tm167 var167 lam167 app).

Definition app167 {Γ A B} : Tm167 Γ (arr167 A B) -> Tm167 Γ A -> Tm167 Γ B
 := fun t u Tm167 var167 lam167 app167 =>
     app167 _ _ _
         (t Tm167 var167 lam167 app167)
         (u Tm167 var167 lam167 app167).

Definition v0167 {Γ A} : Tm167 (snoc167 Γ A) A
 := var167 vz167.

Definition v1167 {Γ A B} : Tm167 (snoc167 (snoc167 Γ A) B) A
 := var167 (vs167 vz167).

Definition v2167 {Γ A B C} : Tm167 (snoc167 (snoc167 (snoc167 Γ A) B) C) A
 := var167 (vs167 (vs167 vz167)).

Definition v3167 {Γ A B C D} : Tm167 (snoc167 (snoc167 (snoc167 (snoc167 Γ A) B) C) D) A
 := var167 (vs167 (vs167 (vs167 vz167))).

Definition v4167 {Γ A B C D E} : Tm167 (snoc167 (snoc167 (snoc167 (snoc167 (snoc167 Γ A) B) C) D) E) A
 := var167 (vs167 (vs167 (vs167 (vs167 vz167)))).

Definition test167 {Γ A} : Tm167 Γ (arr167 (arr167 A A) (arr167 A A))
 := lam167 (lam167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 v0167))))))).


Definition Ty168 : Set
 := forall (Ty168 : Set)
      (base   : Ty168)
      (arr : Ty168 -> Ty168 -> Ty168)
    , Ty168.

Definition base168 : Ty168 := fun _ base168 _ => base168.

Definition arr168 : Ty168 -> Ty168 -> Ty168
 := fun A B Ty168 base168 arr168 =>
     arr168 (A Ty168 base168 arr168) (B Ty168 base168 arr168).

Definition Con168 : Set
 := forall (Con168  : Set)
      (nil  : Con168)
      (snoc : Con168 -> Ty168 -> Con168)
    , Con168.

Definition nil168 : Con168
 := fun Con168 nil168 snoc => nil168.

Definition snoc168 : Con168 -> Ty168 -> Con168
 := fun Γ A Con168 nil168 snoc168 => snoc168 (Γ Con168 nil168 snoc168) A.

Definition Var168 : Con168 -> Ty168 -> Set
 := fun Γ A =>
   forall (Var168 : Con168 -> Ty168 -> Set)
     (vz  : forall Γ A, Var168 (snoc168 Γ A) A)
     (vs  : forall Γ B A, Var168 Γ A -> Var168 (snoc168 Γ B) A)
   , Var168 Γ A.

Definition vz168 {Γ A} : Var168 (snoc168 Γ A) A
 := fun Var168 vz168 vs => vz168 _ _.

Definition vs168 {Γ B A} : Var168 Γ A -> Var168 (snoc168 Γ B) A
 := fun x Var168 vz168 vs168 => vs168 _ _ _ (x Var168 vz168 vs168).

Definition Tm168 : Con168 -> Ty168 -> Set
 := fun Γ A =>
   forall (Tm168  : Con168 -> Ty168 -> Set)
     (var   : forall Γ A     , Var168 Γ A -> Tm168 Γ A)
     (lam   : forall Γ A B   , Tm168 (snoc168 Γ A) B -> Tm168 Γ (arr168 A B))
     (app   : forall Γ A B   , Tm168 Γ (arr168 A B) -> Tm168 Γ A -> Tm168 Γ B)
   , Tm168 Γ A.

Definition var168 {Γ A} : Var168 Γ A -> Tm168 Γ A
 := fun x Tm168 var168 lam app =>
     var168 _ _ x.

Definition lam168 {Γ A B} : Tm168 (snoc168 Γ A) B -> Tm168 Γ (arr168 A B)
 := fun t Tm168 var168 lam168 app =>
     lam168 _ _ _ (t Tm168 var168 lam168 app).

Definition app168 {Γ A B} : Tm168 Γ (arr168 A B) -> Tm168 Γ A -> Tm168 Γ B
 := fun t u Tm168 var168 lam168 app168 =>
     app168 _ _ _
         (t Tm168 var168 lam168 app168)
         (u Tm168 var168 lam168 app168).

Definition v0168 {Γ A} : Tm168 (snoc168 Γ A) A
 := var168 vz168.

Definition v1168 {Γ A B} : Tm168 (snoc168 (snoc168 Γ A) B) A
 := var168 (vs168 vz168).

Definition v2168 {Γ A B C} : Tm168 (snoc168 (snoc168 (snoc168 Γ A) B) C) A
 := var168 (vs168 (vs168 vz168)).

Definition v3168 {Γ A B C D} : Tm168 (snoc168 (snoc168 (snoc168 (snoc168 Γ A) B) C) D) A
 := var168 (vs168 (vs168 (vs168 vz168))).

Definition v4168 {Γ A B C D E} : Tm168 (snoc168 (snoc168 (snoc168 (snoc168 (snoc168 Γ A) B) C) D) E) A
 := var168 (vs168 (vs168 (vs168 (vs168 vz168)))).

Definition test168 {Γ A} : Tm168 Γ (arr168 (arr168 A A) (arr168 A A))
 := lam168 (lam168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 v0168))))))).


Definition Ty169 : Set
 := forall (Ty169 : Set)
      (base   : Ty169)
      (arr : Ty169 -> Ty169 -> Ty169)
    , Ty169.

Definition base169 : Ty169 := fun _ base169 _ => base169.

Definition arr169 : Ty169 -> Ty169 -> Ty169
 := fun A B Ty169 base169 arr169 =>
     arr169 (A Ty169 base169 arr169) (B Ty169 base169 arr169).

Definition Con169 : Set
 := forall (Con169  : Set)
      (nil  : Con169)
      (snoc : Con169 -> Ty169 -> Con169)
    , Con169.

Definition nil169 : Con169
 := fun Con169 nil169 snoc => nil169.

Definition snoc169 : Con169 -> Ty169 -> Con169
 := fun Γ A Con169 nil169 snoc169 => snoc169 (Γ Con169 nil169 snoc169) A.

Definition Var169 : Con169 -> Ty169 -> Set
 := fun Γ A =>
   forall (Var169 : Con169 -> Ty169 -> Set)
     (vz  : forall Γ A, Var169 (snoc169 Γ A) A)
     (vs  : forall Γ B A, Var169 Γ A -> Var169 (snoc169 Γ B) A)
   , Var169 Γ A.

Definition vz169 {Γ A} : Var169 (snoc169 Γ A) A
 := fun Var169 vz169 vs => vz169 _ _.

Definition vs169 {Γ B A} : Var169 Γ A -> Var169 (snoc169 Γ B) A
 := fun x Var169 vz169 vs169 => vs169 _ _ _ (x Var169 vz169 vs169).

Definition Tm169 : Con169 -> Ty169 -> Set
 := fun Γ A =>
   forall (Tm169  : Con169 -> Ty169 -> Set)
     (var   : forall Γ A     , Var169 Γ A -> Tm169 Γ A)
     (lam   : forall Γ A B   , Tm169 (snoc169 Γ A) B -> Tm169 Γ (arr169 A B))
     (app   : forall Γ A B   , Tm169 Γ (arr169 A B) -> Tm169 Γ A -> Tm169 Γ B)
   , Tm169 Γ A.

Definition var169 {Γ A} : Var169 Γ A -> Tm169 Γ A
 := fun x Tm169 var169 lam app =>
     var169 _ _ x.

Definition lam169 {Γ A B} : Tm169 (snoc169 Γ A) B -> Tm169 Γ (arr169 A B)
 := fun t Tm169 var169 lam169 app =>
     lam169 _ _ _ (t Tm169 var169 lam169 app).

Definition app169 {Γ A B} : Tm169 Γ (arr169 A B) -> Tm169 Γ A -> Tm169 Γ B
 := fun t u Tm169 var169 lam169 app169 =>
     app169 _ _ _
         (t Tm169 var169 lam169 app169)
         (u Tm169 var169 lam169 app169).

Definition v0169 {Γ A} : Tm169 (snoc169 Γ A) A
 := var169 vz169.

Definition v1169 {Γ A B} : Tm169 (snoc169 (snoc169 Γ A) B) A
 := var169 (vs169 vz169).

Definition v2169 {Γ A B C} : Tm169 (snoc169 (snoc169 (snoc169 Γ A) B) C) A
 := var169 (vs169 (vs169 vz169)).

Definition v3169 {Γ A B C D} : Tm169 (snoc169 (snoc169 (snoc169 (snoc169 Γ A) B) C) D) A
 := var169 (vs169 (vs169 (vs169 vz169))).

Definition v4169 {Γ A B C D E} : Tm169 (snoc169 (snoc169 (snoc169 (snoc169 (snoc169 Γ A) B) C) D) E) A
 := var169 (vs169 (vs169 (vs169 (vs169 vz169)))).

Definition test169 {Γ A} : Tm169 Γ (arr169 (arr169 A A) (arr169 A A))
 := lam169 (lam169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 v0169))))))).


Definition Ty170 : Set
 := forall (Ty170 : Set)
      (base   : Ty170)
      (arr : Ty170 -> Ty170 -> Ty170)
    , Ty170.

Definition base170 : Ty170 := fun _ base170 _ => base170.

Definition arr170 : Ty170 -> Ty170 -> Ty170
 := fun A B Ty170 base170 arr170 =>
     arr170 (A Ty170 base170 arr170) (B Ty170 base170 arr170).

Definition Con170 : Set
 := forall (Con170  : Set)
      (nil  : Con170)
      (snoc : Con170 -> Ty170 -> Con170)
    , Con170.

Definition nil170 : Con170
 := fun Con170 nil170 snoc => nil170.

Definition snoc170 : Con170 -> Ty170 -> Con170
 := fun Γ A Con170 nil170 snoc170 => snoc170 (Γ Con170 nil170 snoc170) A.

Definition Var170 : Con170 -> Ty170 -> Set
 := fun Γ A =>
   forall (Var170 : Con170 -> Ty170 -> Set)
     (vz  : forall Γ A, Var170 (snoc170 Γ A) A)
     (vs  : forall Γ B A, Var170 Γ A -> Var170 (snoc170 Γ B) A)
   , Var170 Γ A.

Definition vz170 {Γ A} : Var170 (snoc170 Γ A) A
 := fun Var170 vz170 vs => vz170 _ _.

Definition vs170 {Γ B A} : Var170 Γ A -> Var170 (snoc170 Γ B) A
 := fun x Var170 vz170 vs170 => vs170 _ _ _ (x Var170 vz170 vs170).

Definition Tm170 : Con170 -> Ty170 -> Set
 := fun Γ A =>
   forall (Tm170  : Con170 -> Ty170 -> Set)
     (var   : forall Γ A     , Var170 Γ A -> Tm170 Γ A)
     (lam   : forall Γ A B   , Tm170 (snoc170 Γ A) B -> Tm170 Γ (arr170 A B))
     (app   : forall Γ A B   , Tm170 Γ (arr170 A B) -> Tm170 Γ A -> Tm170 Γ B)
   , Tm170 Γ A.

Definition var170 {Γ A} : Var170 Γ A -> Tm170 Γ A
 := fun x Tm170 var170 lam app =>
     var170 _ _ x.

Definition lam170 {Γ A B} : Tm170 (snoc170 Γ A) B -> Tm170 Γ (arr170 A B)
 := fun t Tm170 var170 lam170 app =>
     lam170 _ _ _ (t Tm170 var170 lam170 app).

Definition app170 {Γ A B} : Tm170 Γ (arr170 A B) -> Tm170 Γ A -> Tm170 Γ B
 := fun t u Tm170 var170 lam170 app170 =>
     app170 _ _ _
         (t Tm170 var170 lam170 app170)
         (u Tm170 var170 lam170 app170).

Definition v0170 {Γ A} : Tm170 (snoc170 Γ A) A
 := var170 vz170.

Definition v1170 {Γ A B} : Tm170 (snoc170 (snoc170 Γ A) B) A
 := var170 (vs170 vz170).

Definition v2170 {Γ A B C} : Tm170 (snoc170 (snoc170 (snoc170 Γ A) B) C) A
 := var170 (vs170 (vs170 vz170)).

Definition v3170 {Γ A B C D} : Tm170 (snoc170 (snoc170 (snoc170 (snoc170 Γ A) B) C) D) A
 := var170 (vs170 (vs170 (vs170 vz170))).

Definition v4170 {Γ A B C D E} : Tm170 (snoc170 (snoc170 (snoc170 (snoc170 (snoc170 Γ A) B) C) D) E) A
 := var170 (vs170 (vs170 (vs170 (vs170 vz170)))).

Definition test170 {Γ A} : Tm170 Γ (arr170 (arr170 A A) (arr170 A A))
 := lam170 (lam170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 v0170))))))).


Definition Ty171 : Set
 := forall (Ty171 : Set)
      (base   : Ty171)
      (arr : Ty171 -> Ty171 -> Ty171)
    , Ty171.

Definition base171 : Ty171 := fun _ base171 _ => base171.

Definition arr171 : Ty171 -> Ty171 -> Ty171
 := fun A B Ty171 base171 arr171 =>
     arr171 (A Ty171 base171 arr171) (B Ty171 base171 arr171).

Definition Con171 : Set
 := forall (Con171  : Set)
      (nil  : Con171)
      (snoc : Con171 -> Ty171 -> Con171)
    , Con171.

Definition nil171 : Con171
 := fun Con171 nil171 snoc => nil171.

Definition snoc171 : Con171 -> Ty171 -> Con171
 := fun Γ A Con171 nil171 snoc171 => snoc171 (Γ Con171 nil171 snoc171) A.

Definition Var171 : Con171 -> Ty171 -> Set
 := fun Γ A =>
   forall (Var171 : Con171 -> Ty171 -> Set)
     (vz  : forall Γ A, Var171 (snoc171 Γ A) A)
     (vs  : forall Γ B A, Var171 Γ A -> Var171 (snoc171 Γ B) A)
   , Var171 Γ A.

Definition vz171 {Γ A} : Var171 (snoc171 Γ A) A
 := fun Var171 vz171 vs => vz171 _ _.

Definition vs171 {Γ B A} : Var171 Γ A -> Var171 (snoc171 Γ B) A
 := fun x Var171 vz171 vs171 => vs171 _ _ _ (x Var171 vz171 vs171).

Definition Tm171 : Con171 -> Ty171 -> Set
 := fun Γ A =>
   forall (Tm171  : Con171 -> Ty171 -> Set)
     (var   : forall Γ A     , Var171 Γ A -> Tm171 Γ A)
     (lam   : forall Γ A B   , Tm171 (snoc171 Γ A) B -> Tm171 Γ (arr171 A B))
     (app   : forall Γ A B   , Tm171 Γ (arr171 A B) -> Tm171 Γ A -> Tm171 Γ B)
   , Tm171 Γ A.

Definition var171 {Γ A} : Var171 Γ A -> Tm171 Γ A
 := fun x Tm171 var171 lam app =>
     var171 _ _ x.

Definition lam171 {Γ A B} : Tm171 (snoc171 Γ A) B -> Tm171 Γ (arr171 A B)
 := fun t Tm171 var171 lam171 app =>
     lam171 _ _ _ (t Tm171 var171 lam171 app).

Definition app171 {Γ A B} : Tm171 Γ (arr171 A B) -> Tm171 Γ A -> Tm171 Γ B
 := fun t u Tm171 var171 lam171 app171 =>
     app171 _ _ _
         (t Tm171 var171 lam171 app171)
         (u Tm171 var171 lam171 app171).

Definition v0171 {Γ A} : Tm171 (snoc171 Γ A) A
 := var171 vz171.

Definition v1171 {Γ A B} : Tm171 (snoc171 (snoc171 Γ A) B) A
 := var171 (vs171 vz171).

Definition v2171 {Γ A B C} : Tm171 (snoc171 (snoc171 (snoc171 Γ A) B) C) A
 := var171 (vs171 (vs171 vz171)).

Definition v3171 {Γ A B C D} : Tm171 (snoc171 (snoc171 (snoc171 (snoc171 Γ A) B) C) D) A
 := var171 (vs171 (vs171 (vs171 vz171))).

Definition v4171 {Γ A B C D E} : Tm171 (snoc171 (snoc171 (snoc171 (snoc171 (snoc171 Γ A) B) C) D) E) A
 := var171 (vs171 (vs171 (vs171 (vs171 vz171)))).

Definition test171 {Γ A} : Tm171 Γ (arr171 (arr171 A A) (arr171 A A))
 := lam171 (lam171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 v0171))))))).


Definition Ty172 : Set
 := forall (Ty172 : Set)
      (base   : Ty172)
      (arr : Ty172 -> Ty172 -> Ty172)
    , Ty172.

Definition base172 : Ty172 := fun _ base172 _ => base172.

Definition arr172 : Ty172 -> Ty172 -> Ty172
 := fun A B Ty172 base172 arr172 =>
     arr172 (A Ty172 base172 arr172) (B Ty172 base172 arr172).

Definition Con172 : Set
 := forall (Con172  : Set)
      (nil  : Con172)
      (snoc : Con172 -> Ty172 -> Con172)
    , Con172.

Definition nil172 : Con172
 := fun Con172 nil172 snoc => nil172.

Definition snoc172 : Con172 -> Ty172 -> Con172
 := fun Γ A Con172 nil172 snoc172 => snoc172 (Γ Con172 nil172 snoc172) A.

Definition Var172 : Con172 -> Ty172 -> Set
 := fun Γ A =>
   forall (Var172 : Con172 -> Ty172 -> Set)
     (vz  : forall Γ A, Var172 (snoc172 Γ A) A)
     (vs  : forall Γ B A, Var172 Γ A -> Var172 (snoc172 Γ B) A)
   , Var172 Γ A.

Definition vz172 {Γ A} : Var172 (snoc172 Γ A) A
 := fun Var172 vz172 vs => vz172 _ _.

Definition vs172 {Γ B A} : Var172 Γ A -> Var172 (snoc172 Γ B) A
 := fun x Var172 vz172 vs172 => vs172 _ _ _ (x Var172 vz172 vs172).

Definition Tm172 : Con172 -> Ty172 -> Set
 := fun Γ A =>
   forall (Tm172  : Con172 -> Ty172 -> Set)
     (var   : forall Γ A     , Var172 Γ A -> Tm172 Γ A)
     (lam   : forall Γ A B   , Tm172 (snoc172 Γ A) B -> Tm172 Γ (arr172 A B))
     (app   : forall Γ A B   , Tm172 Γ (arr172 A B) -> Tm172 Γ A -> Tm172 Γ B)
   , Tm172 Γ A.

Definition var172 {Γ A} : Var172 Γ A -> Tm172 Γ A
 := fun x Tm172 var172 lam app =>
     var172 _ _ x.

Definition lam172 {Γ A B} : Tm172 (snoc172 Γ A) B -> Tm172 Γ (arr172 A B)
 := fun t Tm172 var172 lam172 app =>
     lam172 _ _ _ (t Tm172 var172 lam172 app).

Definition app172 {Γ A B} : Tm172 Γ (arr172 A B) -> Tm172 Γ A -> Tm172 Γ B
 := fun t u Tm172 var172 lam172 app172 =>
     app172 _ _ _
         (t Tm172 var172 lam172 app172)
         (u Tm172 var172 lam172 app172).

Definition v0172 {Γ A} : Tm172 (snoc172 Γ A) A
 := var172 vz172.

Definition v1172 {Γ A B} : Tm172 (snoc172 (snoc172 Γ A) B) A
 := var172 (vs172 vz172).

Definition v2172 {Γ A B C} : Tm172 (snoc172 (snoc172 (snoc172 Γ A) B) C) A
 := var172 (vs172 (vs172 vz172)).

Definition v3172 {Γ A B C D} : Tm172 (snoc172 (snoc172 (snoc172 (snoc172 Γ A) B) C) D) A
 := var172 (vs172 (vs172 (vs172 vz172))).

Definition v4172 {Γ A B C D E} : Tm172 (snoc172 (snoc172 (snoc172 (snoc172 (snoc172 Γ A) B) C) D) E) A
 := var172 (vs172 (vs172 (vs172 (vs172 vz172)))).

Definition test172 {Γ A} : Tm172 Γ (arr172 (arr172 A A) (arr172 A A))
 := lam172 (lam172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 v0172))))))).


Definition Ty173 : Set
 := forall (Ty173 : Set)
      (base   : Ty173)
      (arr : Ty173 -> Ty173 -> Ty173)
    , Ty173.

Definition base173 : Ty173 := fun _ base173 _ => base173.

Definition arr173 : Ty173 -> Ty173 -> Ty173
 := fun A B Ty173 base173 arr173 =>
     arr173 (A Ty173 base173 arr173) (B Ty173 base173 arr173).

Definition Con173 : Set
 := forall (Con173  : Set)
      (nil  : Con173)
      (snoc : Con173 -> Ty173 -> Con173)
    , Con173.

Definition nil173 : Con173
 := fun Con173 nil173 snoc => nil173.

Definition snoc173 : Con173 -> Ty173 -> Con173
 := fun Γ A Con173 nil173 snoc173 => snoc173 (Γ Con173 nil173 snoc173) A.

Definition Var173 : Con173 -> Ty173 -> Set
 := fun Γ A =>
   forall (Var173 : Con173 -> Ty173 -> Set)
     (vz  : forall Γ A, Var173 (snoc173 Γ A) A)
     (vs  : forall Γ B A, Var173 Γ A -> Var173 (snoc173 Γ B) A)
   , Var173 Γ A.

Definition vz173 {Γ A} : Var173 (snoc173 Γ A) A
 := fun Var173 vz173 vs => vz173 _ _.

Definition vs173 {Γ B A} : Var173 Γ A -> Var173 (snoc173 Γ B) A
 := fun x Var173 vz173 vs173 => vs173 _ _ _ (x Var173 vz173 vs173).

Definition Tm173 : Con173 -> Ty173 -> Set
 := fun Γ A =>
   forall (Tm173  : Con173 -> Ty173 -> Set)
     (var   : forall Γ A     , Var173 Γ A -> Tm173 Γ A)
     (lam   : forall Γ A B   , Tm173 (snoc173 Γ A) B -> Tm173 Γ (arr173 A B))
     (app   : forall Γ A B   , Tm173 Γ (arr173 A B) -> Tm173 Γ A -> Tm173 Γ B)
   , Tm173 Γ A.

Definition var173 {Γ A} : Var173 Γ A -> Tm173 Γ A
 := fun x Tm173 var173 lam app =>
     var173 _ _ x.

Definition lam173 {Γ A B} : Tm173 (snoc173 Γ A) B -> Tm173 Γ (arr173 A B)
 := fun t Tm173 var173 lam173 app =>
     lam173 _ _ _ (t Tm173 var173 lam173 app).

Definition app173 {Γ A B} : Tm173 Γ (arr173 A B) -> Tm173 Γ A -> Tm173 Γ B
 := fun t u Tm173 var173 lam173 app173 =>
     app173 _ _ _
         (t Tm173 var173 lam173 app173)
         (u Tm173 var173 lam173 app173).

Definition v0173 {Γ A} : Tm173 (snoc173 Γ A) A
 := var173 vz173.

Definition v1173 {Γ A B} : Tm173 (snoc173 (snoc173 Γ A) B) A
 := var173 (vs173 vz173).

Definition v2173 {Γ A B C} : Tm173 (snoc173 (snoc173 (snoc173 Γ A) B) C) A
 := var173 (vs173 (vs173 vz173)).

Definition v3173 {Γ A B C D} : Tm173 (snoc173 (snoc173 (snoc173 (snoc173 Γ A) B) C) D) A
 := var173 (vs173 (vs173 (vs173 vz173))).

Definition v4173 {Γ A B C D E} : Tm173 (snoc173 (snoc173 (snoc173 (snoc173 (snoc173 Γ A) B) C) D) E) A
 := var173 (vs173 (vs173 (vs173 (vs173 vz173)))).

Definition test173 {Γ A} : Tm173 Γ (arr173 (arr173 A A) (arr173 A A))
 := lam173 (lam173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 v0173))))))).


Definition Ty174 : Set
 := forall (Ty174 : Set)
      (base   : Ty174)
      (arr : Ty174 -> Ty174 -> Ty174)
    , Ty174.

Definition base174 : Ty174 := fun _ base174 _ => base174.

Definition arr174 : Ty174 -> Ty174 -> Ty174
 := fun A B Ty174 base174 arr174 =>
     arr174 (A Ty174 base174 arr174) (B Ty174 base174 arr174).

Definition Con174 : Set
 := forall (Con174  : Set)
      (nil  : Con174)
      (snoc : Con174 -> Ty174 -> Con174)
    , Con174.

Definition nil174 : Con174
 := fun Con174 nil174 snoc => nil174.

Definition snoc174 : Con174 -> Ty174 -> Con174
 := fun Γ A Con174 nil174 snoc174 => snoc174 (Γ Con174 nil174 snoc174) A.

Definition Var174 : Con174 -> Ty174 -> Set
 := fun Γ A =>
   forall (Var174 : Con174 -> Ty174 -> Set)
     (vz  : forall Γ A, Var174 (snoc174 Γ A) A)
     (vs  : forall Γ B A, Var174 Γ A -> Var174 (snoc174 Γ B) A)
   , Var174 Γ A.

Definition vz174 {Γ A} : Var174 (snoc174 Γ A) A
 := fun Var174 vz174 vs => vz174 _ _.

Definition vs174 {Γ B A} : Var174 Γ A -> Var174 (snoc174 Γ B) A
 := fun x Var174 vz174 vs174 => vs174 _ _ _ (x Var174 vz174 vs174).

Definition Tm174 : Con174 -> Ty174 -> Set
 := fun Γ A =>
   forall (Tm174  : Con174 -> Ty174 -> Set)
     (var   : forall Γ A     , Var174 Γ A -> Tm174 Γ A)
     (lam   : forall Γ A B   , Tm174 (snoc174 Γ A) B -> Tm174 Γ (arr174 A B))
     (app   : forall Γ A B   , Tm174 Γ (arr174 A B) -> Tm174 Γ A -> Tm174 Γ B)
   , Tm174 Γ A.

Definition var174 {Γ A} : Var174 Γ A -> Tm174 Γ A
 := fun x Tm174 var174 lam app =>
     var174 _ _ x.

Definition lam174 {Γ A B} : Tm174 (snoc174 Γ A) B -> Tm174 Γ (arr174 A B)
 := fun t Tm174 var174 lam174 app =>
     lam174 _ _ _ (t Tm174 var174 lam174 app).

Definition app174 {Γ A B} : Tm174 Γ (arr174 A B) -> Tm174 Γ A -> Tm174 Γ B
 := fun t u Tm174 var174 lam174 app174 =>
     app174 _ _ _
         (t Tm174 var174 lam174 app174)
         (u Tm174 var174 lam174 app174).

Definition v0174 {Γ A} : Tm174 (snoc174 Γ A) A
 := var174 vz174.

Definition v1174 {Γ A B} : Tm174 (snoc174 (snoc174 Γ A) B) A
 := var174 (vs174 vz174).

Definition v2174 {Γ A B C} : Tm174 (snoc174 (snoc174 (snoc174 Γ A) B) C) A
 := var174 (vs174 (vs174 vz174)).

Definition v3174 {Γ A B C D} : Tm174 (snoc174 (snoc174 (snoc174 (snoc174 Γ A) B) C) D) A
 := var174 (vs174 (vs174 (vs174 vz174))).

Definition v4174 {Γ A B C D E} : Tm174 (snoc174 (snoc174 (snoc174 (snoc174 (snoc174 Γ A) B) C) D) E) A
 := var174 (vs174 (vs174 (vs174 (vs174 vz174)))).

Definition test174 {Γ A} : Tm174 Γ (arr174 (arr174 A A) (arr174 A A))
 := lam174 (lam174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 v0174))))))).


Definition Ty175 : Set
 := forall (Ty175 : Set)
      (base   : Ty175)
      (arr : Ty175 -> Ty175 -> Ty175)
    , Ty175.

Definition base175 : Ty175 := fun _ base175 _ => base175.

Definition arr175 : Ty175 -> Ty175 -> Ty175
 := fun A B Ty175 base175 arr175 =>
     arr175 (A Ty175 base175 arr175) (B Ty175 base175 arr175).

Definition Con175 : Set
 := forall (Con175  : Set)
      (nil  : Con175)
      (snoc : Con175 -> Ty175 -> Con175)
    , Con175.

Definition nil175 : Con175
 := fun Con175 nil175 snoc => nil175.

Definition snoc175 : Con175 -> Ty175 -> Con175
 := fun Γ A Con175 nil175 snoc175 => snoc175 (Γ Con175 nil175 snoc175) A.

Definition Var175 : Con175 -> Ty175 -> Set
 := fun Γ A =>
   forall (Var175 : Con175 -> Ty175 -> Set)
     (vz  : forall Γ A, Var175 (snoc175 Γ A) A)
     (vs  : forall Γ B A, Var175 Γ A -> Var175 (snoc175 Γ B) A)
   , Var175 Γ A.

Definition vz175 {Γ A} : Var175 (snoc175 Γ A) A
 := fun Var175 vz175 vs => vz175 _ _.

Definition vs175 {Γ B A} : Var175 Γ A -> Var175 (snoc175 Γ B) A
 := fun x Var175 vz175 vs175 => vs175 _ _ _ (x Var175 vz175 vs175).

Definition Tm175 : Con175 -> Ty175 -> Set
 := fun Γ A =>
   forall (Tm175  : Con175 -> Ty175 -> Set)
     (var   : forall Γ A     , Var175 Γ A -> Tm175 Γ A)
     (lam   : forall Γ A B   , Tm175 (snoc175 Γ A) B -> Tm175 Γ (arr175 A B))
     (app   : forall Γ A B   , Tm175 Γ (arr175 A B) -> Tm175 Γ A -> Tm175 Γ B)
   , Tm175 Γ A.

Definition var175 {Γ A} : Var175 Γ A -> Tm175 Γ A
 := fun x Tm175 var175 lam app =>
     var175 _ _ x.

Definition lam175 {Γ A B} : Tm175 (snoc175 Γ A) B -> Tm175 Γ (arr175 A B)
 := fun t Tm175 var175 lam175 app =>
     lam175 _ _ _ (t Tm175 var175 lam175 app).

Definition app175 {Γ A B} : Tm175 Γ (arr175 A B) -> Tm175 Γ A -> Tm175 Γ B
 := fun t u Tm175 var175 lam175 app175 =>
     app175 _ _ _
         (t Tm175 var175 lam175 app175)
         (u Tm175 var175 lam175 app175).

Definition v0175 {Γ A} : Tm175 (snoc175 Γ A) A
 := var175 vz175.

Definition v1175 {Γ A B} : Tm175 (snoc175 (snoc175 Γ A) B) A
 := var175 (vs175 vz175).

Definition v2175 {Γ A B C} : Tm175 (snoc175 (snoc175 (snoc175 Γ A) B) C) A
 := var175 (vs175 (vs175 vz175)).

Definition v3175 {Γ A B C D} : Tm175 (snoc175 (snoc175 (snoc175 (snoc175 Γ A) B) C) D) A
 := var175 (vs175 (vs175 (vs175 vz175))).

Definition v4175 {Γ A B C D E} : Tm175 (snoc175 (snoc175 (snoc175 (snoc175 (snoc175 Γ A) B) C) D) E) A
 := var175 (vs175 (vs175 (vs175 (vs175 vz175)))).

Definition test175 {Γ A} : Tm175 Γ (arr175 (arr175 A A) (arr175 A A))
 := lam175 (lam175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 v0175))))))).


Definition Ty176 : Set
 := forall (Ty176 : Set)
      (base   : Ty176)
      (arr : Ty176 -> Ty176 -> Ty176)
    , Ty176.

Definition base176 : Ty176 := fun _ base176 _ => base176.

Definition arr176 : Ty176 -> Ty176 -> Ty176
 := fun A B Ty176 base176 arr176 =>
     arr176 (A Ty176 base176 arr176) (B Ty176 base176 arr176).

Definition Con176 : Set
 := forall (Con176  : Set)
      (nil  : Con176)
      (snoc : Con176 -> Ty176 -> Con176)
    , Con176.

Definition nil176 : Con176
 := fun Con176 nil176 snoc => nil176.

Definition snoc176 : Con176 -> Ty176 -> Con176
 := fun Γ A Con176 nil176 snoc176 => snoc176 (Γ Con176 nil176 snoc176) A.

Definition Var176 : Con176 -> Ty176 -> Set
 := fun Γ A =>
   forall (Var176 : Con176 -> Ty176 -> Set)
     (vz  : forall Γ A, Var176 (snoc176 Γ A) A)
     (vs  : forall Γ B A, Var176 Γ A -> Var176 (snoc176 Γ B) A)
   , Var176 Γ A.

Definition vz176 {Γ A} : Var176 (snoc176 Γ A) A
 := fun Var176 vz176 vs => vz176 _ _.

Definition vs176 {Γ B A} : Var176 Γ A -> Var176 (snoc176 Γ B) A
 := fun x Var176 vz176 vs176 => vs176 _ _ _ (x Var176 vz176 vs176).

Definition Tm176 : Con176 -> Ty176 -> Set
 := fun Γ A =>
   forall (Tm176  : Con176 -> Ty176 -> Set)
     (var   : forall Γ A     , Var176 Γ A -> Tm176 Γ A)
     (lam   : forall Γ A B   , Tm176 (snoc176 Γ A) B -> Tm176 Γ (arr176 A B))
     (app   : forall Γ A B   , Tm176 Γ (arr176 A B) -> Tm176 Γ A -> Tm176 Γ B)
   , Tm176 Γ A.

Definition var176 {Γ A} : Var176 Γ A -> Tm176 Γ A
 := fun x Tm176 var176 lam app =>
     var176 _ _ x.

Definition lam176 {Γ A B} : Tm176 (snoc176 Γ A) B -> Tm176 Γ (arr176 A B)
 := fun t Tm176 var176 lam176 app =>
     lam176 _ _ _ (t Tm176 var176 lam176 app).

Definition app176 {Γ A B} : Tm176 Γ (arr176 A B) -> Tm176 Γ A -> Tm176 Γ B
 := fun t u Tm176 var176 lam176 app176 =>
     app176 _ _ _
         (t Tm176 var176 lam176 app176)
         (u Tm176 var176 lam176 app176).

Definition v0176 {Γ A} : Tm176 (snoc176 Γ A) A
 := var176 vz176.

Definition v1176 {Γ A B} : Tm176 (snoc176 (snoc176 Γ A) B) A
 := var176 (vs176 vz176).

Definition v2176 {Γ A B C} : Tm176 (snoc176 (snoc176 (snoc176 Γ A) B) C) A
 := var176 (vs176 (vs176 vz176)).

Definition v3176 {Γ A B C D} : Tm176 (snoc176 (snoc176 (snoc176 (snoc176 Γ A) B) C) D) A
 := var176 (vs176 (vs176 (vs176 vz176))).

Definition v4176 {Γ A B C D E} : Tm176 (snoc176 (snoc176 (snoc176 (snoc176 (snoc176 Γ A) B) C) D) E) A
 := var176 (vs176 (vs176 (vs176 (vs176 vz176)))).

Definition test176 {Γ A} : Tm176 Γ (arr176 (arr176 A A) (arr176 A A))
 := lam176 (lam176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 v0176))))))).


Definition Ty177 : Set
 := forall (Ty177 : Set)
      (base   : Ty177)
      (arr : Ty177 -> Ty177 -> Ty177)
    , Ty177.

Definition base177 : Ty177 := fun _ base177 _ => base177.

Definition arr177 : Ty177 -> Ty177 -> Ty177
 := fun A B Ty177 base177 arr177 =>
     arr177 (A Ty177 base177 arr177) (B Ty177 base177 arr177).

Definition Con177 : Set
 := forall (Con177  : Set)
      (nil  : Con177)
      (snoc : Con177 -> Ty177 -> Con177)
    , Con177.

Definition nil177 : Con177
 := fun Con177 nil177 snoc => nil177.

Definition snoc177 : Con177 -> Ty177 -> Con177
 := fun Γ A Con177 nil177 snoc177 => snoc177 (Γ Con177 nil177 snoc177) A.

Definition Var177 : Con177 -> Ty177 -> Set
 := fun Γ A =>
   forall (Var177 : Con177 -> Ty177 -> Set)
     (vz  : forall Γ A, Var177 (snoc177 Γ A) A)
     (vs  : forall Γ B A, Var177 Γ A -> Var177 (snoc177 Γ B) A)
   , Var177 Γ A.

Definition vz177 {Γ A} : Var177 (snoc177 Γ A) A
 := fun Var177 vz177 vs => vz177 _ _.

Definition vs177 {Γ B A} : Var177 Γ A -> Var177 (snoc177 Γ B) A
 := fun x Var177 vz177 vs177 => vs177 _ _ _ (x Var177 vz177 vs177).

Definition Tm177 : Con177 -> Ty177 -> Set
 := fun Γ A =>
   forall (Tm177  : Con177 -> Ty177 -> Set)
     (var   : forall Γ A     , Var177 Γ A -> Tm177 Γ A)
     (lam   : forall Γ A B   , Tm177 (snoc177 Γ A) B -> Tm177 Γ (arr177 A B))
     (app   : forall Γ A B   , Tm177 Γ (arr177 A B) -> Tm177 Γ A -> Tm177 Γ B)
   , Tm177 Γ A.

Definition var177 {Γ A} : Var177 Γ A -> Tm177 Γ A
 := fun x Tm177 var177 lam app =>
     var177 _ _ x.

Definition lam177 {Γ A B} : Tm177 (snoc177 Γ A) B -> Tm177 Γ (arr177 A B)
 := fun t Tm177 var177 lam177 app =>
     lam177 _ _ _ (t Tm177 var177 lam177 app).

Definition app177 {Γ A B} : Tm177 Γ (arr177 A B) -> Tm177 Γ A -> Tm177 Γ B
 := fun t u Tm177 var177 lam177 app177 =>
     app177 _ _ _
         (t Tm177 var177 lam177 app177)
         (u Tm177 var177 lam177 app177).

Definition v0177 {Γ A} : Tm177 (snoc177 Γ A) A
 := var177 vz177.

Definition v1177 {Γ A B} : Tm177 (snoc177 (snoc177 Γ A) B) A
 := var177 (vs177 vz177).

Definition v2177 {Γ A B C} : Tm177 (snoc177 (snoc177 (snoc177 Γ A) B) C) A
 := var177 (vs177 (vs177 vz177)).

Definition v3177 {Γ A B C D} : Tm177 (snoc177 (snoc177 (snoc177 (snoc177 Γ A) B) C) D) A
 := var177 (vs177 (vs177 (vs177 vz177))).

Definition v4177 {Γ A B C D E} : Tm177 (snoc177 (snoc177 (snoc177 (snoc177 (snoc177 Γ A) B) C) D) E) A
 := var177 (vs177 (vs177 (vs177 (vs177 vz177)))).

Definition test177 {Γ A} : Tm177 Γ (arr177 (arr177 A A) (arr177 A A))
 := lam177 (lam177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 v0177))))))).


Definition Ty178 : Set
 := forall (Ty178 : Set)
      (base   : Ty178)
      (arr : Ty178 -> Ty178 -> Ty178)
    , Ty178.

Definition base178 : Ty178 := fun _ base178 _ => base178.

Definition arr178 : Ty178 -> Ty178 -> Ty178
 := fun A B Ty178 base178 arr178 =>
     arr178 (A Ty178 base178 arr178) (B Ty178 base178 arr178).

Definition Con178 : Set
 := forall (Con178  : Set)
      (nil  : Con178)
      (snoc : Con178 -> Ty178 -> Con178)
    , Con178.

Definition nil178 : Con178
 := fun Con178 nil178 snoc => nil178.

Definition snoc178 : Con178 -> Ty178 -> Con178
 := fun Γ A Con178 nil178 snoc178 => snoc178 (Γ Con178 nil178 snoc178) A.

Definition Var178 : Con178 -> Ty178 -> Set
 := fun Γ A =>
   forall (Var178 : Con178 -> Ty178 -> Set)
     (vz  : forall Γ A, Var178 (snoc178 Γ A) A)
     (vs  : forall Γ B A, Var178 Γ A -> Var178 (snoc178 Γ B) A)
   , Var178 Γ A.

Definition vz178 {Γ A} : Var178 (snoc178 Γ A) A
 := fun Var178 vz178 vs => vz178 _ _.

Definition vs178 {Γ B A} : Var178 Γ A -> Var178 (snoc178 Γ B) A
 := fun x Var178 vz178 vs178 => vs178 _ _ _ (x Var178 vz178 vs178).

Definition Tm178 : Con178 -> Ty178 -> Set
 := fun Γ A =>
   forall (Tm178  : Con178 -> Ty178 -> Set)
     (var   : forall Γ A     , Var178 Γ A -> Tm178 Γ A)
     (lam   : forall Γ A B   , Tm178 (snoc178 Γ A) B -> Tm178 Γ (arr178 A B))
     (app   : forall Γ A B   , Tm178 Γ (arr178 A B) -> Tm178 Γ A -> Tm178 Γ B)
   , Tm178 Γ A.

Definition var178 {Γ A} : Var178 Γ A -> Tm178 Γ A
 := fun x Tm178 var178 lam app =>
     var178 _ _ x.

Definition lam178 {Γ A B} : Tm178 (snoc178 Γ A) B -> Tm178 Γ (arr178 A B)
 := fun t Tm178 var178 lam178 app =>
     lam178 _ _ _ (t Tm178 var178 lam178 app).

Definition app178 {Γ A B} : Tm178 Γ (arr178 A B) -> Tm178 Γ A -> Tm178 Γ B
 := fun t u Tm178 var178 lam178 app178 =>
     app178 _ _ _
         (t Tm178 var178 lam178 app178)
         (u Tm178 var178 lam178 app178).

Definition v0178 {Γ A} : Tm178 (snoc178 Γ A) A
 := var178 vz178.

Definition v1178 {Γ A B} : Tm178 (snoc178 (snoc178 Γ A) B) A
 := var178 (vs178 vz178).

Definition v2178 {Γ A B C} : Tm178 (snoc178 (snoc178 (snoc178 Γ A) B) C) A
 := var178 (vs178 (vs178 vz178)).

Definition v3178 {Γ A B C D} : Tm178 (snoc178 (snoc178 (snoc178 (snoc178 Γ A) B) C) D) A
 := var178 (vs178 (vs178 (vs178 vz178))).

Definition v4178 {Γ A B C D E} : Tm178 (snoc178 (snoc178 (snoc178 (snoc178 (snoc178 Γ A) B) C) D) E) A
 := var178 (vs178 (vs178 (vs178 (vs178 vz178)))).

Definition test178 {Γ A} : Tm178 Γ (arr178 (arr178 A A) (arr178 A A))
 := lam178 (lam178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 v0178))))))).


Definition Ty179 : Set
 := forall (Ty179 : Set)
      (base   : Ty179)
      (arr : Ty179 -> Ty179 -> Ty179)
    , Ty179.

Definition base179 : Ty179 := fun _ base179 _ => base179.

Definition arr179 : Ty179 -> Ty179 -> Ty179
 := fun A B Ty179 base179 arr179 =>
     arr179 (A Ty179 base179 arr179) (B Ty179 base179 arr179).

Definition Con179 : Set
 := forall (Con179  : Set)
      (nil  : Con179)
      (snoc : Con179 -> Ty179 -> Con179)
    , Con179.

Definition nil179 : Con179
 := fun Con179 nil179 snoc => nil179.

Definition snoc179 : Con179 -> Ty179 -> Con179
 := fun Γ A Con179 nil179 snoc179 => snoc179 (Γ Con179 nil179 snoc179) A.

Definition Var179 : Con179 -> Ty179 -> Set
 := fun Γ A =>
   forall (Var179 : Con179 -> Ty179 -> Set)
     (vz  : forall Γ A, Var179 (snoc179 Γ A) A)
     (vs  : forall Γ B A, Var179 Γ A -> Var179 (snoc179 Γ B) A)
   , Var179 Γ A.

Definition vz179 {Γ A} : Var179 (snoc179 Γ A) A
 := fun Var179 vz179 vs => vz179 _ _.

Definition vs179 {Γ B A} : Var179 Γ A -> Var179 (snoc179 Γ B) A
 := fun x Var179 vz179 vs179 => vs179 _ _ _ (x Var179 vz179 vs179).

Definition Tm179 : Con179 -> Ty179 -> Set
 := fun Γ A =>
   forall (Tm179  : Con179 -> Ty179 -> Set)
     (var   : forall Γ A     , Var179 Γ A -> Tm179 Γ A)
     (lam   : forall Γ A B   , Tm179 (snoc179 Γ A) B -> Tm179 Γ (arr179 A B))
     (app   : forall Γ A B   , Tm179 Γ (arr179 A B) -> Tm179 Γ A -> Tm179 Γ B)
   , Tm179 Γ A.

Definition var179 {Γ A} : Var179 Γ A -> Tm179 Γ A
 := fun x Tm179 var179 lam app =>
     var179 _ _ x.

Definition lam179 {Γ A B} : Tm179 (snoc179 Γ A) B -> Tm179 Γ (arr179 A B)
 := fun t Tm179 var179 lam179 app =>
     lam179 _ _ _ (t Tm179 var179 lam179 app).

Definition app179 {Γ A B} : Tm179 Γ (arr179 A B) -> Tm179 Γ A -> Tm179 Γ B
 := fun t u Tm179 var179 lam179 app179 =>
     app179 _ _ _
         (t Tm179 var179 lam179 app179)
         (u Tm179 var179 lam179 app179).

Definition v0179 {Γ A} : Tm179 (snoc179 Γ A) A
 := var179 vz179.

Definition v1179 {Γ A B} : Tm179 (snoc179 (snoc179 Γ A) B) A
 := var179 (vs179 vz179).

Definition v2179 {Γ A B C} : Tm179 (snoc179 (snoc179 (snoc179 Γ A) B) C) A
 := var179 (vs179 (vs179 vz179)).

Definition v3179 {Γ A B C D} : Tm179 (snoc179 (snoc179 (snoc179 (snoc179 Γ A) B) C) D) A
 := var179 (vs179 (vs179 (vs179 vz179))).

Definition v4179 {Γ A B C D E} : Tm179 (snoc179 (snoc179 (snoc179 (snoc179 (snoc179 Γ A) B) C) D) E) A
 := var179 (vs179 (vs179 (vs179 (vs179 vz179)))).

Definition test179 {Γ A} : Tm179 Γ (arr179 (arr179 A A) (arr179 A A))
 := lam179 (lam179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 v0179))))))).


Definition Ty180 : Set
 := forall (Ty180 : Set)
      (base   : Ty180)
      (arr : Ty180 -> Ty180 -> Ty180)
    , Ty180.

Definition base180 : Ty180 := fun _ base180 _ => base180.

Definition arr180 : Ty180 -> Ty180 -> Ty180
 := fun A B Ty180 base180 arr180 =>
     arr180 (A Ty180 base180 arr180) (B Ty180 base180 arr180).

Definition Con180 : Set
 := forall (Con180  : Set)
      (nil  : Con180)
      (snoc : Con180 -> Ty180 -> Con180)
    , Con180.

Definition nil180 : Con180
 := fun Con180 nil180 snoc => nil180.

Definition snoc180 : Con180 -> Ty180 -> Con180
 := fun Γ A Con180 nil180 snoc180 => snoc180 (Γ Con180 nil180 snoc180) A.

Definition Var180 : Con180 -> Ty180 -> Set
 := fun Γ A =>
   forall (Var180 : Con180 -> Ty180 -> Set)
     (vz  : forall Γ A, Var180 (snoc180 Γ A) A)
     (vs  : forall Γ B A, Var180 Γ A -> Var180 (snoc180 Γ B) A)
   , Var180 Γ A.

Definition vz180 {Γ A} : Var180 (snoc180 Γ A) A
 := fun Var180 vz180 vs => vz180 _ _.

Definition vs180 {Γ B A} : Var180 Γ A -> Var180 (snoc180 Γ B) A
 := fun x Var180 vz180 vs180 => vs180 _ _ _ (x Var180 vz180 vs180).

Definition Tm180 : Con180 -> Ty180 -> Set
 := fun Γ A =>
   forall (Tm180  : Con180 -> Ty180 -> Set)
     (var   : forall Γ A     , Var180 Γ A -> Tm180 Γ A)
     (lam   : forall Γ A B   , Tm180 (snoc180 Γ A) B -> Tm180 Γ (arr180 A B))
     (app   : forall Γ A B   , Tm180 Γ (arr180 A B) -> Tm180 Γ A -> Tm180 Γ B)
   , Tm180 Γ A.

Definition var180 {Γ A} : Var180 Γ A -> Tm180 Γ A
 := fun x Tm180 var180 lam app =>
     var180 _ _ x.

Definition lam180 {Γ A B} : Tm180 (snoc180 Γ A) B -> Tm180 Γ (arr180 A B)
 := fun t Tm180 var180 lam180 app =>
     lam180 _ _ _ (t Tm180 var180 lam180 app).

Definition app180 {Γ A B} : Tm180 Γ (arr180 A B) -> Tm180 Γ A -> Tm180 Γ B
 := fun t u Tm180 var180 lam180 app180 =>
     app180 _ _ _
         (t Tm180 var180 lam180 app180)
         (u Tm180 var180 lam180 app180).

Definition v0180 {Γ A} : Tm180 (snoc180 Γ A) A
 := var180 vz180.

Definition v1180 {Γ A B} : Tm180 (snoc180 (snoc180 Γ A) B) A
 := var180 (vs180 vz180).

Definition v2180 {Γ A B C} : Tm180 (snoc180 (snoc180 (snoc180 Γ A) B) C) A
 := var180 (vs180 (vs180 vz180)).

Definition v3180 {Γ A B C D} : Tm180 (snoc180 (snoc180 (snoc180 (snoc180 Γ A) B) C) D) A
 := var180 (vs180 (vs180 (vs180 vz180))).

Definition v4180 {Γ A B C D E} : Tm180 (snoc180 (snoc180 (snoc180 (snoc180 (snoc180 Γ A) B) C) D) E) A
 := var180 (vs180 (vs180 (vs180 (vs180 vz180)))).

Definition test180 {Γ A} : Tm180 Γ (arr180 (arr180 A A) (arr180 A A))
 := lam180 (lam180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 v0180))))))).


Definition Ty181 : Set
 := forall (Ty181 : Set)
      (base   : Ty181)
      (arr : Ty181 -> Ty181 -> Ty181)
    , Ty181.

Definition base181 : Ty181 := fun _ base181 _ => base181.

Definition arr181 : Ty181 -> Ty181 -> Ty181
 := fun A B Ty181 base181 arr181 =>
     arr181 (A Ty181 base181 arr181) (B Ty181 base181 arr181).

Definition Con181 : Set
 := forall (Con181  : Set)
      (nil  : Con181)
      (snoc : Con181 -> Ty181 -> Con181)
    , Con181.

Definition nil181 : Con181
 := fun Con181 nil181 snoc => nil181.

Definition snoc181 : Con181 -> Ty181 -> Con181
 := fun Γ A Con181 nil181 snoc181 => snoc181 (Γ Con181 nil181 snoc181) A.

Definition Var181 : Con181 -> Ty181 -> Set
 := fun Γ A =>
   forall (Var181 : Con181 -> Ty181 -> Set)
     (vz  : forall Γ A, Var181 (snoc181 Γ A) A)
     (vs  : forall Γ B A, Var181 Γ A -> Var181 (snoc181 Γ B) A)
   , Var181 Γ A.

Definition vz181 {Γ A} : Var181 (snoc181 Γ A) A
 := fun Var181 vz181 vs => vz181 _ _.

Definition vs181 {Γ B A} : Var181 Γ A -> Var181 (snoc181 Γ B) A
 := fun x Var181 vz181 vs181 => vs181 _ _ _ (x Var181 vz181 vs181).

Definition Tm181 : Con181 -> Ty181 -> Set
 := fun Γ A =>
   forall (Tm181  : Con181 -> Ty181 -> Set)
     (var   : forall Γ A     , Var181 Γ A -> Tm181 Γ A)
     (lam   : forall Γ A B   , Tm181 (snoc181 Γ A) B -> Tm181 Γ (arr181 A B))
     (app   : forall Γ A B   , Tm181 Γ (arr181 A B) -> Tm181 Γ A -> Tm181 Γ B)
   , Tm181 Γ A.

Definition var181 {Γ A} : Var181 Γ A -> Tm181 Γ A
 := fun x Tm181 var181 lam app =>
     var181 _ _ x.

Definition lam181 {Γ A B} : Tm181 (snoc181 Γ A) B -> Tm181 Γ (arr181 A B)
 := fun t Tm181 var181 lam181 app =>
     lam181 _ _ _ (t Tm181 var181 lam181 app).

Definition app181 {Γ A B} : Tm181 Γ (arr181 A B) -> Tm181 Γ A -> Tm181 Γ B
 := fun t u Tm181 var181 lam181 app181 =>
     app181 _ _ _
         (t Tm181 var181 lam181 app181)
         (u Tm181 var181 lam181 app181).

Definition v0181 {Γ A} : Tm181 (snoc181 Γ A) A
 := var181 vz181.

Definition v1181 {Γ A B} : Tm181 (snoc181 (snoc181 Γ A) B) A
 := var181 (vs181 vz181).

Definition v2181 {Γ A B C} : Tm181 (snoc181 (snoc181 (snoc181 Γ A) B) C) A
 := var181 (vs181 (vs181 vz181)).

Definition v3181 {Γ A B C D} : Tm181 (snoc181 (snoc181 (snoc181 (snoc181 Γ A) B) C) D) A
 := var181 (vs181 (vs181 (vs181 vz181))).

Definition v4181 {Γ A B C D E} : Tm181 (snoc181 (snoc181 (snoc181 (snoc181 (snoc181 Γ A) B) C) D) E) A
 := var181 (vs181 (vs181 (vs181 (vs181 vz181)))).

Definition test181 {Γ A} : Tm181 Γ (arr181 (arr181 A A) (arr181 A A))
 := lam181 (lam181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 v0181))))))).


Definition Ty182 : Set
 := forall (Ty182 : Set)
      (base   : Ty182)
      (arr : Ty182 -> Ty182 -> Ty182)
    , Ty182.

Definition base182 : Ty182 := fun _ base182 _ => base182.

Definition arr182 : Ty182 -> Ty182 -> Ty182
 := fun A B Ty182 base182 arr182 =>
     arr182 (A Ty182 base182 arr182) (B Ty182 base182 arr182).

Definition Con182 : Set
 := forall (Con182  : Set)
      (nil  : Con182)
      (snoc : Con182 -> Ty182 -> Con182)
    , Con182.

Definition nil182 : Con182
 := fun Con182 nil182 snoc => nil182.

Definition snoc182 : Con182 -> Ty182 -> Con182
 := fun Γ A Con182 nil182 snoc182 => snoc182 (Γ Con182 nil182 snoc182) A.

Definition Var182 : Con182 -> Ty182 -> Set
 := fun Γ A =>
   forall (Var182 : Con182 -> Ty182 -> Set)
     (vz  : forall Γ A, Var182 (snoc182 Γ A) A)
     (vs  : forall Γ B A, Var182 Γ A -> Var182 (snoc182 Γ B) A)
   , Var182 Γ A.

Definition vz182 {Γ A} : Var182 (snoc182 Γ A) A
 := fun Var182 vz182 vs => vz182 _ _.

Definition vs182 {Γ B A} : Var182 Γ A -> Var182 (snoc182 Γ B) A
 := fun x Var182 vz182 vs182 => vs182 _ _ _ (x Var182 vz182 vs182).

Definition Tm182 : Con182 -> Ty182 -> Set
 := fun Γ A =>
   forall (Tm182  : Con182 -> Ty182 -> Set)
     (var   : forall Γ A     , Var182 Γ A -> Tm182 Γ A)
     (lam   : forall Γ A B   , Tm182 (snoc182 Γ A) B -> Tm182 Γ (arr182 A B))
     (app   : forall Γ A B   , Tm182 Γ (arr182 A B) -> Tm182 Γ A -> Tm182 Γ B)
   , Tm182 Γ A.

Definition var182 {Γ A} : Var182 Γ A -> Tm182 Γ A
 := fun x Tm182 var182 lam app =>
     var182 _ _ x.

Definition lam182 {Γ A B} : Tm182 (snoc182 Γ A) B -> Tm182 Γ (arr182 A B)
 := fun t Tm182 var182 lam182 app =>
     lam182 _ _ _ (t Tm182 var182 lam182 app).

Definition app182 {Γ A B} : Tm182 Γ (arr182 A B) -> Tm182 Γ A -> Tm182 Γ B
 := fun t u Tm182 var182 lam182 app182 =>
     app182 _ _ _
         (t Tm182 var182 lam182 app182)
         (u Tm182 var182 lam182 app182).

Definition v0182 {Γ A} : Tm182 (snoc182 Γ A) A
 := var182 vz182.

Definition v1182 {Γ A B} : Tm182 (snoc182 (snoc182 Γ A) B) A
 := var182 (vs182 vz182).

Definition v2182 {Γ A B C} : Tm182 (snoc182 (snoc182 (snoc182 Γ A) B) C) A
 := var182 (vs182 (vs182 vz182)).

Definition v3182 {Γ A B C D} : Tm182 (snoc182 (snoc182 (snoc182 (snoc182 Γ A) B) C) D) A
 := var182 (vs182 (vs182 (vs182 vz182))).

Definition v4182 {Γ A B C D E} : Tm182 (snoc182 (snoc182 (snoc182 (snoc182 (snoc182 Γ A) B) C) D) E) A
 := var182 (vs182 (vs182 (vs182 (vs182 vz182)))).

Definition test182 {Γ A} : Tm182 Γ (arr182 (arr182 A A) (arr182 A A))
 := lam182 (lam182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 v0182))))))).


Definition Ty183 : Set
 := forall (Ty183 : Set)
      (base   : Ty183)
      (arr : Ty183 -> Ty183 -> Ty183)
    , Ty183.

Definition base183 : Ty183 := fun _ base183 _ => base183.

Definition arr183 : Ty183 -> Ty183 -> Ty183
 := fun A B Ty183 base183 arr183 =>
     arr183 (A Ty183 base183 arr183) (B Ty183 base183 arr183).

Definition Con183 : Set
 := forall (Con183  : Set)
      (nil  : Con183)
      (snoc : Con183 -> Ty183 -> Con183)
    , Con183.

Definition nil183 : Con183
 := fun Con183 nil183 snoc => nil183.

Definition snoc183 : Con183 -> Ty183 -> Con183
 := fun Γ A Con183 nil183 snoc183 => snoc183 (Γ Con183 nil183 snoc183) A.

Definition Var183 : Con183 -> Ty183 -> Set
 := fun Γ A =>
   forall (Var183 : Con183 -> Ty183 -> Set)
     (vz  : forall Γ A, Var183 (snoc183 Γ A) A)
     (vs  : forall Γ B A, Var183 Γ A -> Var183 (snoc183 Γ B) A)
   , Var183 Γ A.

Definition vz183 {Γ A} : Var183 (snoc183 Γ A) A
 := fun Var183 vz183 vs => vz183 _ _.

Definition vs183 {Γ B A} : Var183 Γ A -> Var183 (snoc183 Γ B) A
 := fun x Var183 vz183 vs183 => vs183 _ _ _ (x Var183 vz183 vs183).

Definition Tm183 : Con183 -> Ty183 -> Set
 := fun Γ A =>
   forall (Tm183  : Con183 -> Ty183 -> Set)
     (var   : forall Γ A     , Var183 Γ A -> Tm183 Γ A)
     (lam   : forall Γ A B   , Tm183 (snoc183 Γ A) B -> Tm183 Γ (arr183 A B))
     (app   : forall Γ A B   , Tm183 Γ (arr183 A B) -> Tm183 Γ A -> Tm183 Γ B)
   , Tm183 Γ A.

Definition var183 {Γ A} : Var183 Γ A -> Tm183 Γ A
 := fun x Tm183 var183 lam app =>
     var183 _ _ x.

Definition lam183 {Γ A B} : Tm183 (snoc183 Γ A) B -> Tm183 Γ (arr183 A B)
 := fun t Tm183 var183 lam183 app =>
     lam183 _ _ _ (t Tm183 var183 lam183 app).

Definition app183 {Γ A B} : Tm183 Γ (arr183 A B) -> Tm183 Γ A -> Tm183 Γ B
 := fun t u Tm183 var183 lam183 app183 =>
     app183 _ _ _
         (t Tm183 var183 lam183 app183)
         (u Tm183 var183 lam183 app183).

Definition v0183 {Γ A} : Tm183 (snoc183 Γ A) A
 := var183 vz183.

Definition v1183 {Γ A B} : Tm183 (snoc183 (snoc183 Γ A) B) A
 := var183 (vs183 vz183).

Definition v2183 {Γ A B C} : Tm183 (snoc183 (snoc183 (snoc183 Γ A) B) C) A
 := var183 (vs183 (vs183 vz183)).

Definition v3183 {Γ A B C D} : Tm183 (snoc183 (snoc183 (snoc183 (snoc183 Γ A) B) C) D) A
 := var183 (vs183 (vs183 (vs183 vz183))).

Definition v4183 {Γ A B C D E} : Tm183 (snoc183 (snoc183 (snoc183 (snoc183 (snoc183 Γ A) B) C) D) E) A
 := var183 (vs183 (vs183 (vs183 (vs183 vz183)))).

Definition test183 {Γ A} : Tm183 Γ (arr183 (arr183 A A) (arr183 A A))
 := lam183 (lam183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 v0183))))))).


Definition Ty184 : Set
 := forall (Ty184 : Set)
      (base   : Ty184)
      (arr : Ty184 -> Ty184 -> Ty184)
    , Ty184.

Definition base184 : Ty184 := fun _ base184 _ => base184.

Definition arr184 : Ty184 -> Ty184 -> Ty184
 := fun A B Ty184 base184 arr184 =>
     arr184 (A Ty184 base184 arr184) (B Ty184 base184 arr184).

Definition Con184 : Set
 := forall (Con184  : Set)
      (nil  : Con184)
      (snoc : Con184 -> Ty184 -> Con184)
    , Con184.

Definition nil184 : Con184
 := fun Con184 nil184 snoc => nil184.

Definition snoc184 : Con184 -> Ty184 -> Con184
 := fun Γ A Con184 nil184 snoc184 => snoc184 (Γ Con184 nil184 snoc184) A.

Definition Var184 : Con184 -> Ty184 -> Set
 := fun Γ A =>
   forall (Var184 : Con184 -> Ty184 -> Set)
     (vz  : forall Γ A, Var184 (snoc184 Γ A) A)
     (vs  : forall Γ B A, Var184 Γ A -> Var184 (snoc184 Γ B) A)
   , Var184 Γ A.

Definition vz184 {Γ A} : Var184 (snoc184 Γ A) A
 := fun Var184 vz184 vs => vz184 _ _.

Definition vs184 {Γ B A} : Var184 Γ A -> Var184 (snoc184 Γ B) A
 := fun x Var184 vz184 vs184 => vs184 _ _ _ (x Var184 vz184 vs184).

Definition Tm184 : Con184 -> Ty184 -> Set
 := fun Γ A =>
   forall (Tm184  : Con184 -> Ty184 -> Set)
     (var   : forall Γ A     , Var184 Γ A -> Tm184 Γ A)
     (lam   : forall Γ A B   , Tm184 (snoc184 Γ A) B -> Tm184 Γ (arr184 A B))
     (app   : forall Γ A B   , Tm184 Γ (arr184 A B) -> Tm184 Γ A -> Tm184 Γ B)
   , Tm184 Γ A.

Definition var184 {Γ A} : Var184 Γ A -> Tm184 Γ A
 := fun x Tm184 var184 lam app =>
     var184 _ _ x.

Definition lam184 {Γ A B} : Tm184 (snoc184 Γ A) B -> Tm184 Γ (arr184 A B)
 := fun t Tm184 var184 lam184 app =>
     lam184 _ _ _ (t Tm184 var184 lam184 app).

Definition app184 {Γ A B} : Tm184 Γ (arr184 A B) -> Tm184 Γ A -> Tm184 Γ B
 := fun t u Tm184 var184 lam184 app184 =>
     app184 _ _ _
         (t Tm184 var184 lam184 app184)
         (u Tm184 var184 lam184 app184).

Definition v0184 {Γ A} : Tm184 (snoc184 Γ A) A
 := var184 vz184.

Definition v1184 {Γ A B} : Tm184 (snoc184 (snoc184 Γ A) B) A
 := var184 (vs184 vz184).

Definition v2184 {Γ A B C} : Tm184 (snoc184 (snoc184 (snoc184 Γ A) B) C) A
 := var184 (vs184 (vs184 vz184)).

Definition v3184 {Γ A B C D} : Tm184 (snoc184 (snoc184 (snoc184 (snoc184 Γ A) B) C) D) A
 := var184 (vs184 (vs184 (vs184 vz184))).

Definition v4184 {Γ A B C D E} : Tm184 (snoc184 (snoc184 (snoc184 (snoc184 (snoc184 Γ A) B) C) D) E) A
 := var184 (vs184 (vs184 (vs184 (vs184 vz184)))).

Definition test184 {Γ A} : Tm184 Γ (arr184 (arr184 A A) (arr184 A A))
 := lam184 (lam184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 v0184))))))).


Definition Ty185 : Set
 := forall (Ty185 : Set)
      (base   : Ty185)
      (arr : Ty185 -> Ty185 -> Ty185)
    , Ty185.

Definition base185 : Ty185 := fun _ base185 _ => base185.

Definition arr185 : Ty185 -> Ty185 -> Ty185
 := fun A B Ty185 base185 arr185 =>
     arr185 (A Ty185 base185 arr185) (B Ty185 base185 arr185).

Definition Con185 : Set
 := forall (Con185  : Set)
      (nil  : Con185)
      (snoc : Con185 -> Ty185 -> Con185)
    , Con185.

Definition nil185 : Con185
 := fun Con185 nil185 snoc => nil185.

Definition snoc185 : Con185 -> Ty185 -> Con185
 := fun Γ A Con185 nil185 snoc185 => snoc185 (Γ Con185 nil185 snoc185) A.

Definition Var185 : Con185 -> Ty185 -> Set
 := fun Γ A =>
   forall (Var185 : Con185 -> Ty185 -> Set)
     (vz  : forall Γ A, Var185 (snoc185 Γ A) A)
     (vs  : forall Γ B A, Var185 Γ A -> Var185 (snoc185 Γ B) A)
   , Var185 Γ A.

Definition vz185 {Γ A} : Var185 (snoc185 Γ A) A
 := fun Var185 vz185 vs => vz185 _ _.

Definition vs185 {Γ B A} : Var185 Γ A -> Var185 (snoc185 Γ B) A
 := fun x Var185 vz185 vs185 => vs185 _ _ _ (x Var185 vz185 vs185).

Definition Tm185 : Con185 -> Ty185 -> Set
 := fun Γ A =>
   forall (Tm185  : Con185 -> Ty185 -> Set)
     (var   : forall Γ A     , Var185 Γ A -> Tm185 Γ A)
     (lam   : forall Γ A B   , Tm185 (snoc185 Γ A) B -> Tm185 Γ (arr185 A B))
     (app   : forall Γ A B   , Tm185 Γ (arr185 A B) -> Tm185 Γ A -> Tm185 Γ B)
   , Tm185 Γ A.

Definition var185 {Γ A} : Var185 Γ A -> Tm185 Γ A
 := fun x Tm185 var185 lam app =>
     var185 _ _ x.

Definition lam185 {Γ A B} : Tm185 (snoc185 Γ A) B -> Tm185 Γ (arr185 A B)
 := fun t Tm185 var185 lam185 app =>
     lam185 _ _ _ (t Tm185 var185 lam185 app).

Definition app185 {Γ A B} : Tm185 Γ (arr185 A B) -> Tm185 Γ A -> Tm185 Γ B
 := fun t u Tm185 var185 lam185 app185 =>
     app185 _ _ _
         (t Tm185 var185 lam185 app185)
         (u Tm185 var185 lam185 app185).

Definition v0185 {Γ A} : Tm185 (snoc185 Γ A) A
 := var185 vz185.

Definition v1185 {Γ A B} : Tm185 (snoc185 (snoc185 Γ A) B) A
 := var185 (vs185 vz185).

Definition v2185 {Γ A B C} : Tm185 (snoc185 (snoc185 (snoc185 Γ A) B) C) A
 := var185 (vs185 (vs185 vz185)).

Definition v3185 {Γ A B C D} : Tm185 (snoc185 (snoc185 (snoc185 (snoc185 Γ A) B) C) D) A
 := var185 (vs185 (vs185 (vs185 vz185))).

Definition v4185 {Γ A B C D E} : Tm185 (snoc185 (snoc185 (snoc185 (snoc185 (snoc185 Γ A) B) C) D) E) A
 := var185 (vs185 (vs185 (vs185 (vs185 vz185)))).

Definition test185 {Γ A} : Tm185 Γ (arr185 (arr185 A A) (arr185 A A))
 := lam185 (lam185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 v0185))))))).


Definition Ty186 : Set
 := forall (Ty186 : Set)
      (base   : Ty186)
      (arr : Ty186 -> Ty186 -> Ty186)
    , Ty186.

Definition base186 : Ty186 := fun _ base186 _ => base186.

Definition arr186 : Ty186 -> Ty186 -> Ty186
 := fun A B Ty186 base186 arr186 =>
     arr186 (A Ty186 base186 arr186) (B Ty186 base186 arr186).

Definition Con186 : Set
 := forall (Con186  : Set)
      (nil  : Con186)
      (snoc : Con186 -> Ty186 -> Con186)
    , Con186.

Definition nil186 : Con186
 := fun Con186 nil186 snoc => nil186.

Definition snoc186 : Con186 -> Ty186 -> Con186
 := fun Γ A Con186 nil186 snoc186 => snoc186 (Γ Con186 nil186 snoc186) A.

Definition Var186 : Con186 -> Ty186 -> Set
 := fun Γ A =>
   forall (Var186 : Con186 -> Ty186 -> Set)
     (vz  : forall Γ A, Var186 (snoc186 Γ A) A)
     (vs  : forall Γ B A, Var186 Γ A -> Var186 (snoc186 Γ B) A)
   , Var186 Γ A.

Definition vz186 {Γ A} : Var186 (snoc186 Γ A) A
 := fun Var186 vz186 vs => vz186 _ _.

Definition vs186 {Γ B A} : Var186 Γ A -> Var186 (snoc186 Γ B) A
 := fun x Var186 vz186 vs186 => vs186 _ _ _ (x Var186 vz186 vs186).

Definition Tm186 : Con186 -> Ty186 -> Set
 := fun Γ A =>
   forall (Tm186  : Con186 -> Ty186 -> Set)
     (var   : forall Γ A     , Var186 Γ A -> Tm186 Γ A)
     (lam   : forall Γ A B   , Tm186 (snoc186 Γ A) B -> Tm186 Γ (arr186 A B))
     (app   : forall Γ A B   , Tm186 Γ (arr186 A B) -> Tm186 Γ A -> Tm186 Γ B)
   , Tm186 Γ A.

Definition var186 {Γ A} : Var186 Γ A -> Tm186 Γ A
 := fun x Tm186 var186 lam app =>
     var186 _ _ x.

Definition lam186 {Γ A B} : Tm186 (snoc186 Γ A) B -> Tm186 Γ (arr186 A B)
 := fun t Tm186 var186 lam186 app =>
     lam186 _ _ _ (t Tm186 var186 lam186 app).

Definition app186 {Γ A B} : Tm186 Γ (arr186 A B) -> Tm186 Γ A -> Tm186 Γ B
 := fun t u Tm186 var186 lam186 app186 =>
     app186 _ _ _
         (t Tm186 var186 lam186 app186)
         (u Tm186 var186 lam186 app186).

Definition v0186 {Γ A} : Tm186 (snoc186 Γ A) A
 := var186 vz186.

Definition v1186 {Γ A B} : Tm186 (snoc186 (snoc186 Γ A) B) A
 := var186 (vs186 vz186).

Definition v2186 {Γ A B C} : Tm186 (snoc186 (snoc186 (snoc186 Γ A) B) C) A
 := var186 (vs186 (vs186 vz186)).

Definition v3186 {Γ A B C D} : Tm186 (snoc186 (snoc186 (snoc186 (snoc186 Γ A) B) C) D) A
 := var186 (vs186 (vs186 (vs186 vz186))).

Definition v4186 {Γ A B C D E} : Tm186 (snoc186 (snoc186 (snoc186 (snoc186 (snoc186 Γ A) B) C) D) E) A
 := var186 (vs186 (vs186 (vs186 (vs186 vz186)))).

Definition test186 {Γ A} : Tm186 Γ (arr186 (arr186 A A) (arr186 A A))
 := lam186 (lam186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 v0186))))))).


Definition Ty187 : Set
 := forall (Ty187 : Set)
      (base   : Ty187)
      (arr : Ty187 -> Ty187 -> Ty187)
    , Ty187.

Definition base187 : Ty187 := fun _ base187 _ => base187.

Definition arr187 : Ty187 -> Ty187 -> Ty187
 := fun A B Ty187 base187 arr187 =>
     arr187 (A Ty187 base187 arr187) (B Ty187 base187 arr187).

Definition Con187 : Set
 := forall (Con187  : Set)
      (nil  : Con187)
      (snoc : Con187 -> Ty187 -> Con187)
    , Con187.

Definition nil187 : Con187
 := fun Con187 nil187 snoc => nil187.

Definition snoc187 : Con187 -> Ty187 -> Con187
 := fun Γ A Con187 nil187 snoc187 => snoc187 (Γ Con187 nil187 snoc187) A.

Definition Var187 : Con187 -> Ty187 -> Set
 := fun Γ A =>
   forall (Var187 : Con187 -> Ty187 -> Set)
     (vz  : forall Γ A, Var187 (snoc187 Γ A) A)
     (vs  : forall Γ B A, Var187 Γ A -> Var187 (snoc187 Γ B) A)
   , Var187 Γ A.

Definition vz187 {Γ A} : Var187 (snoc187 Γ A) A
 := fun Var187 vz187 vs => vz187 _ _.

Definition vs187 {Γ B A} : Var187 Γ A -> Var187 (snoc187 Γ B) A
 := fun x Var187 vz187 vs187 => vs187 _ _ _ (x Var187 vz187 vs187).

Definition Tm187 : Con187 -> Ty187 -> Set
 := fun Γ A =>
   forall (Tm187  : Con187 -> Ty187 -> Set)
     (var   : forall Γ A     , Var187 Γ A -> Tm187 Γ A)
     (lam   : forall Γ A B   , Tm187 (snoc187 Γ A) B -> Tm187 Γ (arr187 A B))
     (app   : forall Γ A B   , Tm187 Γ (arr187 A B) -> Tm187 Γ A -> Tm187 Γ B)
   , Tm187 Γ A.

Definition var187 {Γ A} : Var187 Γ A -> Tm187 Γ A
 := fun x Tm187 var187 lam app =>
     var187 _ _ x.

Definition lam187 {Γ A B} : Tm187 (snoc187 Γ A) B -> Tm187 Γ (arr187 A B)
 := fun t Tm187 var187 lam187 app =>
     lam187 _ _ _ (t Tm187 var187 lam187 app).

Definition app187 {Γ A B} : Tm187 Γ (arr187 A B) -> Tm187 Γ A -> Tm187 Γ B
 := fun t u Tm187 var187 lam187 app187 =>
     app187 _ _ _
         (t Tm187 var187 lam187 app187)
         (u Tm187 var187 lam187 app187).

Definition v0187 {Γ A} : Tm187 (snoc187 Γ A) A
 := var187 vz187.

Definition v1187 {Γ A B} : Tm187 (snoc187 (snoc187 Γ A) B) A
 := var187 (vs187 vz187).

Definition v2187 {Γ A B C} : Tm187 (snoc187 (snoc187 (snoc187 Γ A) B) C) A
 := var187 (vs187 (vs187 vz187)).

Definition v3187 {Γ A B C D} : Tm187 (snoc187 (snoc187 (snoc187 (snoc187 Γ A) B) C) D) A
 := var187 (vs187 (vs187 (vs187 vz187))).

Definition v4187 {Γ A B C D E} : Tm187 (snoc187 (snoc187 (snoc187 (snoc187 (snoc187 Γ A) B) C) D) E) A
 := var187 (vs187 (vs187 (vs187 (vs187 vz187)))).

Definition test187 {Γ A} : Tm187 Γ (arr187 (arr187 A A) (arr187 A A))
 := lam187 (lam187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 v0187))))))).


Definition Ty188 : Set
 := forall (Ty188 : Set)
      (base   : Ty188)
      (arr : Ty188 -> Ty188 -> Ty188)
    , Ty188.

Definition base188 : Ty188 := fun _ base188 _ => base188.

Definition arr188 : Ty188 -> Ty188 -> Ty188
 := fun A B Ty188 base188 arr188 =>
     arr188 (A Ty188 base188 arr188) (B Ty188 base188 arr188).

Definition Con188 : Set
 := forall (Con188  : Set)
      (nil  : Con188)
      (snoc : Con188 -> Ty188 -> Con188)
    , Con188.

Definition nil188 : Con188
 := fun Con188 nil188 snoc => nil188.

Definition snoc188 : Con188 -> Ty188 -> Con188
 := fun Γ A Con188 nil188 snoc188 => snoc188 (Γ Con188 nil188 snoc188) A.

Definition Var188 : Con188 -> Ty188 -> Set
 := fun Γ A =>
   forall (Var188 : Con188 -> Ty188 -> Set)
     (vz  : forall Γ A, Var188 (snoc188 Γ A) A)
     (vs  : forall Γ B A, Var188 Γ A -> Var188 (snoc188 Γ B) A)
   , Var188 Γ A.

Definition vz188 {Γ A} : Var188 (snoc188 Γ A) A
 := fun Var188 vz188 vs => vz188 _ _.

Definition vs188 {Γ B A} : Var188 Γ A -> Var188 (snoc188 Γ B) A
 := fun x Var188 vz188 vs188 => vs188 _ _ _ (x Var188 vz188 vs188).

Definition Tm188 : Con188 -> Ty188 -> Set
 := fun Γ A =>
   forall (Tm188  : Con188 -> Ty188 -> Set)
     (var   : forall Γ A     , Var188 Γ A -> Tm188 Γ A)
     (lam   : forall Γ A B   , Tm188 (snoc188 Γ A) B -> Tm188 Γ (arr188 A B))
     (app   : forall Γ A B   , Tm188 Γ (arr188 A B) -> Tm188 Γ A -> Tm188 Γ B)
   , Tm188 Γ A.

Definition var188 {Γ A} : Var188 Γ A -> Tm188 Γ A
 := fun x Tm188 var188 lam app =>
     var188 _ _ x.

Definition lam188 {Γ A B} : Tm188 (snoc188 Γ A) B -> Tm188 Γ (arr188 A B)
 := fun t Tm188 var188 lam188 app =>
     lam188 _ _ _ (t Tm188 var188 lam188 app).

Definition app188 {Γ A B} : Tm188 Γ (arr188 A B) -> Tm188 Γ A -> Tm188 Γ B
 := fun t u Tm188 var188 lam188 app188 =>
     app188 _ _ _
         (t Tm188 var188 lam188 app188)
         (u Tm188 var188 lam188 app188).

Definition v0188 {Γ A} : Tm188 (snoc188 Γ A) A
 := var188 vz188.

Definition v1188 {Γ A B} : Tm188 (snoc188 (snoc188 Γ A) B) A
 := var188 (vs188 vz188).

Definition v2188 {Γ A B C} : Tm188 (snoc188 (snoc188 (snoc188 Γ A) B) C) A
 := var188 (vs188 (vs188 vz188)).

Definition v3188 {Γ A B C D} : Tm188 (snoc188 (snoc188 (snoc188 (snoc188 Γ A) B) C) D) A
 := var188 (vs188 (vs188 (vs188 vz188))).

Definition v4188 {Γ A B C D E} : Tm188 (snoc188 (snoc188 (snoc188 (snoc188 (snoc188 Γ A) B) C) D) E) A
 := var188 (vs188 (vs188 (vs188 (vs188 vz188)))).

Definition test188 {Γ A} : Tm188 Γ (arr188 (arr188 A A) (arr188 A A))
 := lam188 (lam188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 v0188))))))).


Definition Ty189 : Set
 := forall (Ty189 : Set)
      (base   : Ty189)
      (arr : Ty189 -> Ty189 -> Ty189)
    , Ty189.

Definition base189 : Ty189 := fun _ base189 _ => base189.

Definition arr189 : Ty189 -> Ty189 -> Ty189
 := fun A B Ty189 base189 arr189 =>
     arr189 (A Ty189 base189 arr189) (B Ty189 base189 arr189).

Definition Con189 : Set
 := forall (Con189  : Set)
      (nil  : Con189)
      (snoc : Con189 -> Ty189 -> Con189)
    , Con189.

Definition nil189 : Con189
 := fun Con189 nil189 snoc => nil189.

Definition snoc189 : Con189 -> Ty189 -> Con189
 := fun Γ A Con189 nil189 snoc189 => snoc189 (Γ Con189 nil189 snoc189) A.

Definition Var189 : Con189 -> Ty189 -> Set
 := fun Γ A =>
   forall (Var189 : Con189 -> Ty189 -> Set)
     (vz  : forall Γ A, Var189 (snoc189 Γ A) A)
     (vs  : forall Γ B A, Var189 Γ A -> Var189 (snoc189 Γ B) A)
   , Var189 Γ A.

Definition vz189 {Γ A} : Var189 (snoc189 Γ A) A
 := fun Var189 vz189 vs => vz189 _ _.

Definition vs189 {Γ B A} : Var189 Γ A -> Var189 (snoc189 Γ B) A
 := fun x Var189 vz189 vs189 => vs189 _ _ _ (x Var189 vz189 vs189).

Definition Tm189 : Con189 -> Ty189 -> Set
 := fun Γ A =>
   forall (Tm189  : Con189 -> Ty189 -> Set)
     (var   : forall Γ A     , Var189 Γ A -> Tm189 Γ A)
     (lam   : forall Γ A B   , Tm189 (snoc189 Γ A) B -> Tm189 Γ (arr189 A B))
     (app   : forall Γ A B   , Tm189 Γ (arr189 A B) -> Tm189 Γ A -> Tm189 Γ B)
   , Tm189 Γ A.

Definition var189 {Γ A} : Var189 Γ A -> Tm189 Γ A
 := fun x Tm189 var189 lam app =>
     var189 _ _ x.

Definition lam189 {Γ A B} : Tm189 (snoc189 Γ A) B -> Tm189 Γ (arr189 A B)
 := fun t Tm189 var189 lam189 app =>
     lam189 _ _ _ (t Tm189 var189 lam189 app).

Definition app189 {Γ A B} : Tm189 Γ (arr189 A B) -> Tm189 Γ A -> Tm189 Γ B
 := fun t u Tm189 var189 lam189 app189 =>
     app189 _ _ _
         (t Tm189 var189 lam189 app189)
         (u Tm189 var189 lam189 app189).

Definition v0189 {Γ A} : Tm189 (snoc189 Γ A) A
 := var189 vz189.

Definition v1189 {Γ A B} : Tm189 (snoc189 (snoc189 Γ A) B) A
 := var189 (vs189 vz189).

Definition v2189 {Γ A B C} : Tm189 (snoc189 (snoc189 (snoc189 Γ A) B) C) A
 := var189 (vs189 (vs189 vz189)).

Definition v3189 {Γ A B C D} : Tm189 (snoc189 (snoc189 (snoc189 (snoc189 Γ A) B) C) D) A
 := var189 (vs189 (vs189 (vs189 vz189))).

Definition v4189 {Γ A B C D E} : Tm189 (snoc189 (snoc189 (snoc189 (snoc189 (snoc189 Γ A) B) C) D) E) A
 := var189 (vs189 (vs189 (vs189 (vs189 vz189)))).

Definition test189 {Γ A} : Tm189 Γ (arr189 (arr189 A A) (arr189 A A))
 := lam189 (lam189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 v0189))))))).


Definition Ty190 : Set
 := forall (Ty190 : Set)
      (base   : Ty190)
      (arr : Ty190 -> Ty190 -> Ty190)
    , Ty190.

Definition base190 : Ty190 := fun _ base190 _ => base190.

Definition arr190 : Ty190 -> Ty190 -> Ty190
 := fun A B Ty190 base190 arr190 =>
     arr190 (A Ty190 base190 arr190) (B Ty190 base190 arr190).

Definition Con190 : Set
 := forall (Con190  : Set)
      (nil  : Con190)
      (snoc : Con190 -> Ty190 -> Con190)
    , Con190.

Definition nil190 : Con190
 := fun Con190 nil190 snoc => nil190.

Definition snoc190 : Con190 -> Ty190 -> Con190
 := fun Γ A Con190 nil190 snoc190 => snoc190 (Γ Con190 nil190 snoc190) A.

Definition Var190 : Con190 -> Ty190 -> Set
 := fun Γ A =>
   forall (Var190 : Con190 -> Ty190 -> Set)
     (vz  : forall Γ A, Var190 (snoc190 Γ A) A)
     (vs  : forall Γ B A, Var190 Γ A -> Var190 (snoc190 Γ B) A)
   , Var190 Γ A.

Definition vz190 {Γ A} : Var190 (snoc190 Γ A) A
 := fun Var190 vz190 vs => vz190 _ _.

Definition vs190 {Γ B A} : Var190 Γ A -> Var190 (snoc190 Γ B) A
 := fun x Var190 vz190 vs190 => vs190 _ _ _ (x Var190 vz190 vs190).

Definition Tm190 : Con190 -> Ty190 -> Set
 := fun Γ A =>
   forall (Tm190  : Con190 -> Ty190 -> Set)
     (var   : forall Γ A     , Var190 Γ A -> Tm190 Γ A)
     (lam   : forall Γ A B   , Tm190 (snoc190 Γ A) B -> Tm190 Γ (arr190 A B))
     (app   : forall Γ A B   , Tm190 Γ (arr190 A B) -> Tm190 Γ A -> Tm190 Γ B)
   , Tm190 Γ A.

Definition var190 {Γ A} : Var190 Γ A -> Tm190 Γ A
 := fun x Tm190 var190 lam app =>
     var190 _ _ x.

Definition lam190 {Γ A B} : Tm190 (snoc190 Γ A) B -> Tm190 Γ (arr190 A B)
 := fun t Tm190 var190 lam190 app =>
     lam190 _ _ _ (t Tm190 var190 lam190 app).

Definition app190 {Γ A B} : Tm190 Γ (arr190 A B) -> Tm190 Γ A -> Tm190 Γ B
 := fun t u Tm190 var190 lam190 app190 =>
     app190 _ _ _
         (t Tm190 var190 lam190 app190)
         (u Tm190 var190 lam190 app190).

Definition v0190 {Γ A} : Tm190 (snoc190 Γ A) A
 := var190 vz190.

Definition v1190 {Γ A B} : Tm190 (snoc190 (snoc190 Γ A) B) A
 := var190 (vs190 vz190).

Definition v2190 {Γ A B C} : Tm190 (snoc190 (snoc190 (snoc190 Γ A) B) C) A
 := var190 (vs190 (vs190 vz190)).

Definition v3190 {Γ A B C D} : Tm190 (snoc190 (snoc190 (snoc190 (snoc190 Γ A) B) C) D) A
 := var190 (vs190 (vs190 (vs190 vz190))).

Definition v4190 {Γ A B C D E} : Tm190 (snoc190 (snoc190 (snoc190 (snoc190 (snoc190 Γ A) B) C) D) E) A
 := var190 (vs190 (vs190 (vs190 (vs190 vz190)))).

Definition test190 {Γ A} : Tm190 Γ (arr190 (arr190 A A) (arr190 A A))
 := lam190 (lam190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 v0190))))))).


Definition Ty191 : Set
 := forall (Ty191 : Set)
      (base   : Ty191)
      (arr : Ty191 -> Ty191 -> Ty191)
    , Ty191.

Definition base191 : Ty191 := fun _ base191 _ => base191.

Definition arr191 : Ty191 -> Ty191 -> Ty191
 := fun A B Ty191 base191 arr191 =>
     arr191 (A Ty191 base191 arr191) (B Ty191 base191 arr191).

Definition Con191 : Set
 := forall (Con191  : Set)
      (nil  : Con191)
      (snoc : Con191 -> Ty191 -> Con191)
    , Con191.

Definition nil191 : Con191
 := fun Con191 nil191 snoc => nil191.

Definition snoc191 : Con191 -> Ty191 -> Con191
 := fun Γ A Con191 nil191 snoc191 => snoc191 (Γ Con191 nil191 snoc191) A.

Definition Var191 : Con191 -> Ty191 -> Set
 := fun Γ A =>
   forall (Var191 : Con191 -> Ty191 -> Set)
     (vz  : forall Γ A, Var191 (snoc191 Γ A) A)
     (vs  : forall Γ B A, Var191 Γ A -> Var191 (snoc191 Γ B) A)
   , Var191 Γ A.

Definition vz191 {Γ A} : Var191 (snoc191 Γ A) A
 := fun Var191 vz191 vs => vz191 _ _.

Definition vs191 {Γ B A} : Var191 Γ A -> Var191 (snoc191 Γ B) A
 := fun x Var191 vz191 vs191 => vs191 _ _ _ (x Var191 vz191 vs191).

Definition Tm191 : Con191 -> Ty191 -> Set
 := fun Γ A =>
   forall (Tm191  : Con191 -> Ty191 -> Set)
     (var   : forall Γ A     , Var191 Γ A -> Tm191 Γ A)
     (lam   : forall Γ A B   , Tm191 (snoc191 Γ A) B -> Tm191 Γ (arr191 A B))
     (app   : forall Γ A B   , Tm191 Γ (arr191 A B) -> Tm191 Γ A -> Tm191 Γ B)
   , Tm191 Γ A.

Definition var191 {Γ A} : Var191 Γ A -> Tm191 Γ A
 := fun x Tm191 var191 lam app =>
     var191 _ _ x.

Definition lam191 {Γ A B} : Tm191 (snoc191 Γ A) B -> Tm191 Γ (arr191 A B)
 := fun t Tm191 var191 lam191 app =>
     lam191 _ _ _ (t Tm191 var191 lam191 app).

Definition app191 {Γ A B} : Tm191 Γ (arr191 A B) -> Tm191 Γ A -> Tm191 Γ B
 := fun t u Tm191 var191 lam191 app191 =>
     app191 _ _ _
         (t Tm191 var191 lam191 app191)
         (u Tm191 var191 lam191 app191).

Definition v0191 {Γ A} : Tm191 (snoc191 Γ A) A
 := var191 vz191.

Definition v1191 {Γ A B} : Tm191 (snoc191 (snoc191 Γ A) B) A
 := var191 (vs191 vz191).

Definition v2191 {Γ A B C} : Tm191 (snoc191 (snoc191 (snoc191 Γ A) B) C) A
 := var191 (vs191 (vs191 vz191)).

Definition v3191 {Γ A B C D} : Tm191 (snoc191 (snoc191 (snoc191 (snoc191 Γ A) B) C) D) A
 := var191 (vs191 (vs191 (vs191 vz191))).

Definition v4191 {Γ A B C D E} : Tm191 (snoc191 (snoc191 (snoc191 (snoc191 (snoc191 Γ A) B) C) D) E) A
 := var191 (vs191 (vs191 (vs191 (vs191 vz191)))).

Definition test191 {Γ A} : Tm191 Γ (arr191 (arr191 A A) (arr191 A A))
 := lam191 (lam191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 v0191))))))).

