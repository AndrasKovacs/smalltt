
def Ty : Type 1
 := ∀ (Ty : Type)
      (ι   : Ty)
      (arr : Ty → Ty → Ty)
    , Ty

def ι : Ty := λ _ ι _ => ι

def arr : Ty → Ty → Ty
 := λ A B Ty ι arr =>
     arr (A Ty ι arr) (B Ty ι arr)

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
     (vz  : ∀ Γ A, Var (snoc Γ A) A)
     (vs  : ∀ Γ B A, Var Γ A → Var (snoc Γ B) A)
   , Var Γ A

def vz {Γ A} : Var (snoc Γ A) A
 := λ Var vz vs => vz _ _

def vs {Γ B A} : Var Γ A → Var (snoc Γ B) A
 := λ x Var vz vs => vs _ _ _ (x Var vz vs)

def Tm : Con → Ty → Type 1
 := λ Γ A =>
   ∀ (Tm  : Con → Ty → Type)
     (var   : ∀ Γ A     , Var Γ A → Tm Γ A)
     (lam   : ∀ Γ A B   , Tm (snoc Γ A) B → Tm Γ (arr A B))
     (app   : ∀ Γ A B   , Tm Γ (arr A B) → Tm Γ A → Tm Γ B)
   , Tm Γ A

def var {Γ A} : Var Γ A → Tm Γ A
 := λ x Tm var lam app =>
     var _ _ x

def lam {Γ A B} : Tm (snoc Γ A) B → Tm Γ (arr A B)
 := λ t Tm var lam app =>
     lam _ _ _ (t Tm var lam app)

def app {Γ A B} : Tm Γ (arr A B) → Tm Γ A → Tm Γ B
 := λ t u Tm var lam app =>
     app _ _ _
         (t Tm var lam app)
         (u Tm var lam app)

def v0 {Γ A} : Tm (snoc Γ A) A
 := var vz

def v1 {Γ A B} : Tm (snoc (snoc Γ A) B) A
 := var (vs vz)

def v2 {Γ A B C} : Tm (snoc (snoc (snoc Γ A) B) C) A
 := var (vs (vs vz))

def v3 {Γ A B C D} : Tm (snoc (snoc (snoc (snoc Γ A) B) C) D) A
 := var (vs (vs (vs vz)))

def v4 {Γ A B C D E} : Tm (snoc (snoc (snoc (snoc (snoc Γ A) B) C) D) E) A
 := var (vs (vs (vs (vs vz))))

def test {Γ A} : Tm Γ (arr (arr A A) (arr A A))
 := lam (lam (app v1 (app v1 (app v1 (app v1 (app v1 (app v1 v0)))))))


def Ty1 : Type 1
 := ∀ (Ty1 : Type)
      (ι   : Ty1)
      (arr : Ty1 → Ty1 → Ty1)
    , Ty1

def ι1 : Ty1 := λ _ ι1 _ => ι1

def arr1 : Ty1 → Ty1 → Ty1
 := λ A B Ty1 ι1 arr1 =>
     arr1 (A Ty1 ι1 arr1) (B Ty1 ι1 arr1)

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
     (vz  : ∀ Γ A, Var1 (snoc1 Γ A) A)
     (vs  : ∀ Γ B A, Var1 Γ A → Var1 (snoc1 Γ B) A)
   , Var1 Γ A

def vz1 {Γ A} : Var1 (snoc1 Γ A) A
 := λ Var1 vz1 vs => vz1 _ _

def vs1 {Γ B A} : Var1 Γ A → Var1 (snoc1 Γ B) A
 := λ x Var1 vz1 vs1 => vs1 _ _ _ (x Var1 vz1 vs1)

def Tm1 : Con1 → Ty1 → Type 1
 := λ Γ A =>
   ∀ (Tm1  : Con1 → Ty1 → Type)
     (var   : ∀ Γ A     , Var1 Γ A → Tm1 Γ A)
     (lam   : ∀ Γ A B   , Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B))
     (app   : ∀ Γ A B   , Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B)
   , Tm1 Γ A

def var1 {Γ A} : Var1 Γ A → Tm1 Γ A
 := λ x Tm1 var1 lam app =>
     var1 _ _ x

def lam1 {Γ A B} : Tm1 (snoc1 Γ A) B → Tm1 Γ (arr1 A B)
 := λ t Tm1 var1 lam1 app =>
     lam1 _ _ _ (t Tm1 var1 lam1 app)

def app1 {Γ A B} : Tm1 Γ (arr1 A B) → Tm1 Γ A → Tm1 Γ B
 := λ t u Tm1 var1 lam1 app1 =>
     app1 _ _ _
         (t Tm1 var1 lam1 app1)
         (u Tm1 var1 lam1 app1)

def v01 {Γ A} : Tm1 (snoc1 Γ A) A
 := var1 vz1

def v11 {Γ A B} : Tm1 (snoc1 (snoc1 Γ A) B) A
 := var1 (vs1 vz1)

def v21 {Γ A B C} : Tm1 (snoc1 (snoc1 (snoc1 Γ A) B) C) A
 := var1 (vs1 (vs1 vz1))

def v31 {Γ A B C D} : Tm1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) A
 := var1 (vs1 (vs1 (vs1 vz1)))

def v41 {Γ A B C D E} : Tm1 (snoc1 (snoc1 (snoc1 (snoc1 (snoc1 Γ A) B) C) D) E) A
 := var1 (vs1 (vs1 (vs1 (vs1 vz1))))

def test1 {Γ A} : Tm1 Γ (arr1 (arr1 A A) (arr1 A A))
 := lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01)))))))


def Ty2 : Type 1
 := ∀ (Ty2 : Type)
      (ι   : Ty2)
      (arr : Ty2 → Ty2 → Ty2)
    , Ty2

def ι2 : Ty2 := λ _ ι2 _ => ι2

def arr2 : Ty2 → Ty2 → Ty2
 := λ A B Ty2 ι2 arr2 =>
     arr2 (A Ty2 ι2 arr2) (B Ty2 ι2 arr2)

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
     (vz  : ∀ Γ A, Var2 (snoc2 Γ A) A)
     (vs  : ∀ Γ B A, Var2 Γ A → Var2 (snoc2 Γ B) A)
   , Var2 Γ A

def vz2 {Γ A} : Var2 (snoc2 Γ A) A
 := λ Var2 vz2 vs => vz2 _ _

def vs2 {Γ B A} : Var2 Γ A → Var2 (snoc2 Γ B) A
 := λ x Var2 vz2 vs2 => vs2 _ _ _ (x Var2 vz2 vs2)

def Tm2 : Con2 → Ty2 → Type 1
 := λ Γ A =>
   ∀ (Tm2  : Con2 → Ty2 → Type)
     (var   : ∀ Γ A     , Var2 Γ A → Tm2 Γ A)
     (lam   : ∀ Γ A B   , Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B))
     (app   : ∀ Γ A B   , Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B)
   , Tm2 Γ A

def var2 {Γ A} : Var2 Γ A → Tm2 Γ A
 := λ x Tm2 var2 lam app =>
     var2 _ _ x

def lam2 {Γ A B} : Tm2 (snoc2 Γ A) B → Tm2 Γ (arr2 A B)
 := λ t Tm2 var2 lam2 app =>
     lam2 _ _ _ (t Tm2 var2 lam2 app)

def app2 {Γ A B} : Tm2 Γ (arr2 A B) → Tm2 Γ A → Tm2 Γ B
 := λ t u Tm2 var2 lam2 app2 =>
     app2 _ _ _
         (t Tm2 var2 lam2 app2)
         (u Tm2 var2 lam2 app2)

def v02 {Γ A} : Tm2 (snoc2 Γ A) A
 := var2 vz2

def v12 {Γ A B} : Tm2 (snoc2 (snoc2 Γ A) B) A
 := var2 (vs2 vz2)

def v22 {Γ A B C} : Tm2 (snoc2 (snoc2 (snoc2 Γ A) B) C) A
 := var2 (vs2 (vs2 vz2))

def v32 {Γ A B C D} : Tm2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) A
 := var2 (vs2 (vs2 (vs2 vz2)))

def v42 {Γ A B C D E} : Tm2 (snoc2 (snoc2 (snoc2 (snoc2 (snoc2 Γ A) B) C) D) E) A
 := var2 (vs2 (vs2 (vs2 (vs2 vz2))))

def test2 {Γ A} : Tm2 Γ (arr2 (arr2 A A) (arr2 A A))
 := lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02)))))))


def Ty3 : Type 1
 := ∀ (Ty3 : Type)
      (ι   : Ty3)
      (arr : Ty3 → Ty3 → Ty3)
    , Ty3

def ι3 : Ty3 := λ _ ι3 _ => ι3

def arr3 : Ty3 → Ty3 → Ty3
 := λ A B Ty3 ι3 arr3 =>
     arr3 (A Ty3 ι3 arr3) (B Ty3 ι3 arr3)

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
     (vz  : ∀ Γ A, Var3 (snoc3 Γ A) A)
     (vs  : ∀ Γ B A, Var3 Γ A → Var3 (snoc3 Γ B) A)
   , Var3 Γ A

def vz3 {Γ A} : Var3 (snoc3 Γ A) A
 := λ Var3 vz3 vs => vz3 _ _

def vs3 {Γ B A} : Var3 Γ A → Var3 (snoc3 Γ B) A
 := λ x Var3 vz3 vs3 => vs3 _ _ _ (x Var3 vz3 vs3)

def Tm3 : Con3 → Ty3 → Type 1
 := λ Γ A =>
   ∀ (Tm3  : Con3 → Ty3 → Type)
     (var   : ∀ Γ A     , Var3 Γ A → Tm3 Γ A)
     (lam   : ∀ Γ A B   , Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B))
     (app   : ∀ Γ A B   , Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B)
   , Tm3 Γ A

def var3 {Γ A} : Var3 Γ A → Tm3 Γ A
 := λ x Tm3 var3 lam app =>
     var3 _ _ x

def lam3 {Γ A B} : Tm3 (snoc3 Γ A) B → Tm3 Γ (arr3 A B)
 := λ t Tm3 var3 lam3 app =>
     lam3 _ _ _ (t Tm3 var3 lam3 app)

def app3 {Γ A B} : Tm3 Γ (arr3 A B) → Tm3 Γ A → Tm3 Γ B
 := λ t u Tm3 var3 lam3 app3 =>
     app3 _ _ _
         (t Tm3 var3 lam3 app3)
         (u Tm3 var3 lam3 app3)

def v03 {Γ A} : Tm3 (snoc3 Γ A) A
 := var3 vz3

def v13 {Γ A B} : Tm3 (snoc3 (snoc3 Γ A) B) A
 := var3 (vs3 vz3)

def v23 {Γ A B C} : Tm3 (snoc3 (snoc3 (snoc3 Γ A) B) C) A
 := var3 (vs3 (vs3 vz3))

def v33 {Γ A B C D} : Tm3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) A
 := var3 (vs3 (vs3 (vs3 vz3)))

def v43 {Γ A B C D E} : Tm3 (snoc3 (snoc3 (snoc3 (snoc3 (snoc3 Γ A) B) C) D) E) A
 := var3 (vs3 (vs3 (vs3 (vs3 vz3))))

def test3 {Γ A} : Tm3 Γ (arr3 (arr3 A A) (arr3 A A))
 := lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03)))))))


def Ty4 : Type 1
 := ∀ (Ty4 : Type)
      (ι   : Ty4)
      (arr : Ty4 → Ty4 → Ty4)
    , Ty4

def ι4 : Ty4 := λ _ ι4 _ => ι4

def arr4 : Ty4 → Ty4 → Ty4
 := λ A B Ty4 ι4 arr4 =>
     arr4 (A Ty4 ι4 arr4) (B Ty4 ι4 arr4)

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
     (vz  : ∀ Γ A, Var4 (snoc4 Γ A) A)
     (vs  : ∀ Γ B A, Var4 Γ A → Var4 (snoc4 Γ B) A)
   , Var4 Γ A

def vz4 {Γ A} : Var4 (snoc4 Γ A) A
 := λ Var4 vz4 vs => vz4 _ _

def vs4 {Γ B A} : Var4 Γ A → Var4 (snoc4 Γ B) A
 := λ x Var4 vz4 vs4 => vs4 _ _ _ (x Var4 vz4 vs4)

def Tm4 : Con4 → Ty4 → Type 1
 := λ Γ A =>
   ∀ (Tm4  : Con4 → Ty4 → Type)
     (var   : ∀ Γ A     , Var4 Γ A → Tm4 Γ A)
     (lam   : ∀ Γ A B   , Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B))
     (app   : ∀ Γ A B   , Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B)
   , Tm4 Γ A

def var4 {Γ A} : Var4 Γ A → Tm4 Γ A
 := λ x Tm4 var4 lam app =>
     var4 _ _ x

def lam4 {Γ A B} : Tm4 (snoc4 Γ A) B → Tm4 Γ (arr4 A B)
 := λ t Tm4 var4 lam4 app =>
     lam4 _ _ _ (t Tm4 var4 lam4 app)

def app4 {Γ A B} : Tm4 Γ (arr4 A B) → Tm4 Γ A → Tm4 Γ B
 := λ t u Tm4 var4 lam4 app4 =>
     app4 _ _ _
         (t Tm4 var4 lam4 app4)
         (u Tm4 var4 lam4 app4)

def v04 {Γ A} : Tm4 (snoc4 Γ A) A
 := var4 vz4

def v14 {Γ A B} : Tm4 (snoc4 (snoc4 Γ A) B) A
 := var4 (vs4 vz4)

def v24 {Γ A B C} : Tm4 (snoc4 (snoc4 (snoc4 Γ A) B) C) A
 := var4 (vs4 (vs4 vz4))

def v34 {Γ A B C D} : Tm4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) A
 := var4 (vs4 (vs4 (vs4 vz4)))

def v44 {Γ A B C D E} : Tm4 (snoc4 (snoc4 (snoc4 (snoc4 (snoc4 Γ A) B) C) D) E) A
 := var4 (vs4 (vs4 (vs4 (vs4 vz4))))

def test4 {Γ A} : Tm4 Γ (arr4 (arr4 A A) (arr4 A A))
 := lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04)))))))


def Ty5 : Type 1
 := ∀ (Ty5 : Type)
      (ι   : Ty5)
      (arr : Ty5 → Ty5 → Ty5)
    , Ty5

def ι5 : Ty5 := λ _ ι5 _ => ι5

def arr5 : Ty5 → Ty5 → Ty5
 := λ A B Ty5 ι5 arr5 =>
     arr5 (A Ty5 ι5 arr5) (B Ty5 ι5 arr5)

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
     (vz  : ∀ Γ A, Var5 (snoc5 Γ A) A)
     (vs  : ∀ Γ B A, Var5 Γ A → Var5 (snoc5 Γ B) A)
   , Var5 Γ A

def vz5 {Γ A} : Var5 (snoc5 Γ A) A
 := λ Var5 vz5 vs => vz5 _ _

def vs5 {Γ B A} : Var5 Γ A → Var5 (snoc5 Γ B) A
 := λ x Var5 vz5 vs5 => vs5 _ _ _ (x Var5 vz5 vs5)

def Tm5 : Con5 → Ty5 → Type 1
 := λ Γ A =>
   ∀ (Tm5  : Con5 → Ty5 → Type)
     (var   : ∀ Γ A     , Var5 Γ A → Tm5 Γ A)
     (lam   : ∀ Γ A B   , Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B))
     (app   : ∀ Γ A B   , Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B)
   , Tm5 Γ A

def var5 {Γ A} : Var5 Γ A → Tm5 Γ A
 := λ x Tm5 var5 lam app =>
     var5 _ _ x

def lam5 {Γ A B} : Tm5 (snoc5 Γ A) B → Tm5 Γ (arr5 A B)
 := λ t Tm5 var5 lam5 app =>
     lam5 _ _ _ (t Tm5 var5 lam5 app)

def app5 {Γ A B} : Tm5 Γ (arr5 A B) → Tm5 Γ A → Tm5 Γ B
 := λ t u Tm5 var5 lam5 app5 =>
     app5 _ _ _
         (t Tm5 var5 lam5 app5)
         (u Tm5 var5 lam5 app5)

def v05 {Γ A} : Tm5 (snoc5 Γ A) A
 := var5 vz5

def v15 {Γ A B} : Tm5 (snoc5 (snoc5 Γ A) B) A
 := var5 (vs5 vz5)

def v25 {Γ A B C} : Tm5 (snoc5 (snoc5 (snoc5 Γ A) B) C) A
 := var5 (vs5 (vs5 vz5))

def v35 {Γ A B C D} : Tm5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) A
 := var5 (vs5 (vs5 (vs5 vz5)))

def v45 {Γ A B C D E} : Tm5 (snoc5 (snoc5 (snoc5 (snoc5 (snoc5 Γ A) B) C) D) E) A
 := var5 (vs5 (vs5 (vs5 (vs5 vz5))))

def test5 {Γ A} : Tm5 Γ (arr5 (arr5 A A) (arr5 A A))
 := lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05)))))))


def Ty6 : Type 1
 := ∀ (Ty6 : Type)
      (ι   : Ty6)
      (arr : Ty6 → Ty6 → Ty6)
    , Ty6

def ι6 : Ty6 := λ _ ι6 _ => ι6

def arr6 : Ty6 → Ty6 → Ty6
 := λ A B Ty6 ι6 arr6 =>
     arr6 (A Ty6 ι6 arr6) (B Ty6 ι6 arr6)

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
     (vz  : ∀ Γ A, Var6 (snoc6 Γ A) A)
     (vs  : ∀ Γ B A, Var6 Γ A → Var6 (snoc6 Γ B) A)
   , Var6 Γ A

def vz6 {Γ A} : Var6 (snoc6 Γ A) A
 := λ Var6 vz6 vs => vz6 _ _

def vs6 {Γ B A} : Var6 Γ A → Var6 (snoc6 Γ B) A
 := λ x Var6 vz6 vs6 => vs6 _ _ _ (x Var6 vz6 vs6)

def Tm6 : Con6 → Ty6 → Type 1
 := λ Γ A =>
   ∀ (Tm6  : Con6 → Ty6 → Type)
     (var   : ∀ Γ A     , Var6 Γ A → Tm6 Γ A)
     (lam   : ∀ Γ A B   , Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B))
     (app   : ∀ Γ A B   , Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B)
   , Tm6 Γ A

def var6 {Γ A} : Var6 Γ A → Tm6 Γ A
 := λ x Tm6 var6 lam app =>
     var6 _ _ x

def lam6 {Γ A B} : Tm6 (snoc6 Γ A) B → Tm6 Γ (arr6 A B)
 := λ t Tm6 var6 lam6 app =>
     lam6 _ _ _ (t Tm6 var6 lam6 app)

def app6 {Γ A B} : Tm6 Γ (arr6 A B) → Tm6 Γ A → Tm6 Γ B
 := λ t u Tm6 var6 lam6 app6 =>
     app6 _ _ _
         (t Tm6 var6 lam6 app6)
         (u Tm6 var6 lam6 app6)

def v06 {Γ A} : Tm6 (snoc6 Γ A) A
 := var6 vz6

def v16 {Γ A B} : Tm6 (snoc6 (snoc6 Γ A) B) A
 := var6 (vs6 vz6)

def v26 {Γ A B C} : Tm6 (snoc6 (snoc6 (snoc6 Γ A) B) C) A
 := var6 (vs6 (vs6 vz6))

def v36 {Γ A B C D} : Tm6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) A
 := var6 (vs6 (vs6 (vs6 vz6)))

def v46 {Γ A B C D E} : Tm6 (snoc6 (snoc6 (snoc6 (snoc6 (snoc6 Γ A) B) C) D) E) A
 := var6 (vs6 (vs6 (vs6 (vs6 vz6))))

def test6 {Γ A} : Tm6 Γ (arr6 (arr6 A A) (arr6 A A))
 := lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06)))))))


def Ty7 : Type 1
 := ∀ (Ty7 : Type)
      (ι   : Ty7)
      (arr : Ty7 → Ty7 → Ty7)
    , Ty7

def ι7 : Ty7 := λ _ ι7 _ => ι7

def arr7 : Ty7 → Ty7 → Ty7
 := λ A B Ty7 ι7 arr7 =>
     arr7 (A Ty7 ι7 arr7) (B Ty7 ι7 arr7)

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
     (vz  : ∀ Γ A, Var7 (snoc7 Γ A) A)
     (vs  : ∀ Γ B A, Var7 Γ A → Var7 (snoc7 Γ B) A)
   , Var7 Γ A

def vz7 {Γ A} : Var7 (snoc7 Γ A) A
 := λ Var7 vz7 vs => vz7 _ _

def vs7 {Γ B A} : Var7 Γ A → Var7 (snoc7 Γ B) A
 := λ x Var7 vz7 vs7 => vs7 _ _ _ (x Var7 vz7 vs7)

def Tm7 : Con7 → Ty7 → Type 1
 := λ Γ A =>
   ∀ (Tm7  : Con7 → Ty7 → Type)
     (var   : ∀ Γ A     , Var7 Γ A → Tm7 Γ A)
     (lam   : ∀ Γ A B   , Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B))
     (app   : ∀ Γ A B   , Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B)
   , Tm7 Γ A

def var7 {Γ A} : Var7 Γ A → Tm7 Γ A
 := λ x Tm7 var7 lam app =>
     var7 _ _ x

def lam7 {Γ A B} : Tm7 (snoc7 Γ A) B → Tm7 Γ (arr7 A B)
 := λ t Tm7 var7 lam7 app =>
     lam7 _ _ _ (t Tm7 var7 lam7 app)

def app7 {Γ A B} : Tm7 Γ (arr7 A B) → Tm7 Γ A → Tm7 Γ B
 := λ t u Tm7 var7 lam7 app7 =>
     app7 _ _ _
         (t Tm7 var7 lam7 app7)
         (u Tm7 var7 lam7 app7)

def v07 {Γ A} : Tm7 (snoc7 Γ A) A
 := var7 vz7

def v17 {Γ A B} : Tm7 (snoc7 (snoc7 Γ A) B) A
 := var7 (vs7 vz7)

def v27 {Γ A B C} : Tm7 (snoc7 (snoc7 (snoc7 Γ A) B) C) A
 := var7 (vs7 (vs7 vz7))

def v37 {Γ A B C D} : Tm7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) A
 := var7 (vs7 (vs7 (vs7 vz7)))

def v47 {Γ A B C D E} : Tm7 (snoc7 (snoc7 (snoc7 (snoc7 (snoc7 Γ A) B) C) D) E) A
 := var7 (vs7 (vs7 (vs7 (vs7 vz7))))

def test7 {Γ A} : Tm7 Γ (arr7 (arr7 A A) (arr7 A A))
 := lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07)))))))


def Ty8 : Type 1
 := ∀ (Ty8 : Type)
      (ι   : Ty8)
      (arr : Ty8 → Ty8 → Ty8)
    , Ty8

def ι8 : Ty8 := λ _ ι8 _ => ι8

def arr8 : Ty8 → Ty8 → Ty8
 := λ A B Ty8 ι8 arr8 =>
     arr8 (A Ty8 ι8 arr8) (B Ty8 ι8 arr8)

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
     (vz  : ∀ Γ A, Var8 (snoc8 Γ A) A)
     (vs  : ∀ Γ B A, Var8 Γ A → Var8 (snoc8 Γ B) A)
   , Var8 Γ A

def vz8 {Γ A} : Var8 (snoc8 Γ A) A
 := λ Var8 vz8 vs => vz8 _ _

def vs8 {Γ B A} : Var8 Γ A → Var8 (snoc8 Γ B) A
 := λ x Var8 vz8 vs8 => vs8 _ _ _ (x Var8 vz8 vs8)

def Tm8 : Con8 → Ty8 → Type 1
 := λ Γ A =>
   ∀ (Tm8  : Con8 → Ty8 → Type)
     (var   : ∀ Γ A     , Var8 Γ A → Tm8 Γ A)
     (lam   : ∀ Γ A B   , Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B))
     (app   : ∀ Γ A B   , Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B)
   , Tm8 Γ A

def var8 {Γ A} : Var8 Γ A → Tm8 Γ A
 := λ x Tm8 var8 lam app =>
     var8 _ _ x

def lam8 {Γ A B} : Tm8 (snoc8 Γ A) B → Tm8 Γ (arr8 A B)
 := λ t Tm8 var8 lam8 app =>
     lam8 _ _ _ (t Tm8 var8 lam8 app)

def app8 {Γ A B} : Tm8 Γ (arr8 A B) → Tm8 Γ A → Tm8 Γ B
 := λ t u Tm8 var8 lam8 app8 =>
     app8 _ _ _
         (t Tm8 var8 lam8 app8)
         (u Tm8 var8 lam8 app8)

def v08 {Γ A} : Tm8 (snoc8 Γ A) A
 := var8 vz8

def v18 {Γ A B} : Tm8 (snoc8 (snoc8 Γ A) B) A
 := var8 (vs8 vz8)

def v28 {Γ A B C} : Tm8 (snoc8 (snoc8 (snoc8 Γ A) B) C) A
 := var8 (vs8 (vs8 vz8))

def v38 {Γ A B C D} : Tm8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) A
 := var8 (vs8 (vs8 (vs8 vz8)))

def v48 {Γ A B C D E} : Tm8 (snoc8 (snoc8 (snoc8 (snoc8 (snoc8 Γ A) B) C) D) E) A
 := var8 (vs8 (vs8 (vs8 (vs8 vz8))))

def test8 {Γ A} : Tm8 Γ (arr8 (arr8 A A) (arr8 A A))
 := lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08)))))))


def Ty9 : Type 1
 := ∀ (Ty9 : Type)
      (ι   : Ty9)
      (arr : Ty9 → Ty9 → Ty9)
    , Ty9

def ι9 : Ty9 := λ _ ι9 _ => ι9

def arr9 : Ty9 → Ty9 → Ty9
 := λ A B Ty9 ι9 arr9 =>
     arr9 (A Ty9 ι9 arr9) (B Ty9 ι9 arr9)

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
     (vz  : ∀ Γ A, Var9 (snoc9 Γ A) A)
     (vs  : ∀ Γ B A, Var9 Γ A → Var9 (snoc9 Γ B) A)
   , Var9 Γ A

def vz9 {Γ A} : Var9 (snoc9 Γ A) A
 := λ Var9 vz9 vs => vz9 _ _

def vs9 {Γ B A} : Var9 Γ A → Var9 (snoc9 Γ B) A
 := λ x Var9 vz9 vs9 => vs9 _ _ _ (x Var9 vz9 vs9)

def Tm9 : Con9 → Ty9 → Type 1
 := λ Γ A =>
   ∀ (Tm9  : Con9 → Ty9 → Type)
     (var   : ∀ Γ A     , Var9 Γ A → Tm9 Γ A)
     (lam   : ∀ Γ A B   , Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B))
     (app   : ∀ Γ A B   , Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B)
   , Tm9 Γ A

def var9 {Γ A} : Var9 Γ A → Tm9 Γ A
 := λ x Tm9 var9 lam app =>
     var9 _ _ x

def lam9 {Γ A B} : Tm9 (snoc9 Γ A) B → Tm9 Γ (arr9 A B)
 := λ t Tm9 var9 lam9 app =>
     lam9 _ _ _ (t Tm9 var9 lam9 app)

def app9 {Γ A B} : Tm9 Γ (arr9 A B) → Tm9 Γ A → Tm9 Γ B
 := λ t u Tm9 var9 lam9 app9 =>
     app9 _ _ _
         (t Tm9 var9 lam9 app9)
         (u Tm9 var9 lam9 app9)

def v09 {Γ A} : Tm9 (snoc9 Γ A) A
 := var9 vz9

def v19 {Γ A B} : Tm9 (snoc9 (snoc9 Γ A) B) A
 := var9 (vs9 vz9)

def v29 {Γ A B C} : Tm9 (snoc9 (snoc9 (snoc9 Γ A) B) C) A
 := var9 (vs9 (vs9 vz9))

def v39 {Γ A B C D} : Tm9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) A
 := var9 (vs9 (vs9 (vs9 vz9)))

def v49 {Γ A B C D E} : Tm9 (snoc9 (snoc9 (snoc9 (snoc9 (snoc9 Γ A) B) C) D) E) A
 := var9 (vs9 (vs9 (vs9 (vs9 vz9))))

def test9 {Γ A} : Tm9 Γ (arr9 (arr9 A A) (arr9 A A))
 := lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09)))))))


def Ty10 : Type 1
 := ∀ (Ty10 : Type)
      (ι   : Ty10)
      (arr : Ty10 → Ty10 → Ty10)
    , Ty10

def ι10 : Ty10 := λ _ ι10 _ => ι10

def arr10 : Ty10 → Ty10 → Ty10
 := λ A B Ty10 ι10 arr10 =>
     arr10 (A Ty10 ι10 arr10) (B Ty10 ι10 arr10)

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
     (vz  : ∀ Γ A, Var10 (snoc10 Γ A) A)
     (vs  : ∀ Γ B A, Var10 Γ A → Var10 (snoc10 Γ B) A)
   , Var10 Γ A

def vz10 {Γ A} : Var10 (snoc10 Γ A) A
 := λ Var10 vz10 vs => vz10 _ _

def vs10 {Γ B A} : Var10 Γ A → Var10 (snoc10 Γ B) A
 := λ x Var10 vz10 vs10 => vs10 _ _ _ (x Var10 vz10 vs10)

def Tm10 : Con10 → Ty10 → Type 1
 := λ Γ A =>
   ∀ (Tm10  : Con10 → Ty10 → Type)
     (var   : ∀ Γ A     , Var10 Γ A → Tm10 Γ A)
     (lam   : ∀ Γ A B   , Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B))
     (app   : ∀ Γ A B   , Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B)
   , Tm10 Γ A

def var10 {Γ A} : Var10 Γ A → Tm10 Γ A
 := λ x Tm10 var10 lam app =>
     var10 _ _ x

def lam10 {Γ A B} : Tm10 (snoc10 Γ A) B → Tm10 Γ (arr10 A B)
 := λ t Tm10 var10 lam10 app =>
     lam10 _ _ _ (t Tm10 var10 lam10 app)

def app10 {Γ A B} : Tm10 Γ (arr10 A B) → Tm10 Γ A → Tm10 Γ B
 := λ t u Tm10 var10 lam10 app10 =>
     app10 _ _ _
         (t Tm10 var10 lam10 app10)
         (u Tm10 var10 lam10 app10)

def v010 {Γ A} : Tm10 (snoc10 Γ A) A
 := var10 vz10

def v110 {Γ A B} : Tm10 (snoc10 (snoc10 Γ A) B) A
 := var10 (vs10 vz10)

def v210 {Γ A B C} : Tm10 (snoc10 (snoc10 (snoc10 Γ A) B) C) A
 := var10 (vs10 (vs10 vz10))

def v310 {Γ A B C D} : Tm10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) A
 := var10 (vs10 (vs10 (vs10 vz10)))

def v410 {Γ A B C D E} : Tm10 (snoc10 (snoc10 (snoc10 (snoc10 (snoc10 Γ A) B) C) D) E) A
 := var10 (vs10 (vs10 (vs10 (vs10 vz10))))

def test10 {Γ A} : Tm10 Γ (arr10 (arr10 A A) (arr10 A A))
 := lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010)))))))


def Ty11 : Type 1
 := ∀ (Ty11 : Type)
      (ι   : Ty11)
      (arr : Ty11 → Ty11 → Ty11)
    , Ty11

def ι11 : Ty11 := λ _ ι11 _ => ι11

def arr11 : Ty11 → Ty11 → Ty11
 := λ A B Ty11 ι11 arr11 =>
     arr11 (A Ty11 ι11 arr11) (B Ty11 ι11 arr11)

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
     (vz  : ∀ Γ A, Var11 (snoc11 Γ A) A)
     (vs  : ∀ Γ B A, Var11 Γ A → Var11 (snoc11 Γ B) A)
   , Var11 Γ A

def vz11 {Γ A} : Var11 (snoc11 Γ A) A
 := λ Var11 vz11 vs => vz11 _ _

def vs11 {Γ B A} : Var11 Γ A → Var11 (snoc11 Γ B) A
 := λ x Var11 vz11 vs11 => vs11 _ _ _ (x Var11 vz11 vs11)

def Tm11 : Con11 → Ty11 → Type 1
 := λ Γ A =>
   ∀ (Tm11  : Con11 → Ty11 → Type)
     (var   : ∀ Γ A     , Var11 Γ A → Tm11 Γ A)
     (lam   : ∀ Γ A B   , Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B))
     (app   : ∀ Γ A B   , Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B)
   , Tm11 Γ A

def var11 {Γ A} : Var11 Γ A → Tm11 Γ A
 := λ x Tm11 var11 lam app =>
     var11 _ _ x

def lam11 {Γ A B} : Tm11 (snoc11 Γ A) B → Tm11 Γ (arr11 A B)
 := λ t Tm11 var11 lam11 app =>
     lam11 _ _ _ (t Tm11 var11 lam11 app)

def app11 {Γ A B} : Tm11 Γ (arr11 A B) → Tm11 Γ A → Tm11 Γ B
 := λ t u Tm11 var11 lam11 app11 =>
     app11 _ _ _
         (t Tm11 var11 lam11 app11)
         (u Tm11 var11 lam11 app11)

def v011 {Γ A} : Tm11 (snoc11 Γ A) A
 := var11 vz11

def v111 {Γ A B} : Tm11 (snoc11 (snoc11 Γ A) B) A
 := var11 (vs11 vz11)

def v211 {Γ A B C} : Tm11 (snoc11 (snoc11 (snoc11 Γ A) B) C) A
 := var11 (vs11 (vs11 vz11))

def v311 {Γ A B C D} : Tm11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) A
 := var11 (vs11 (vs11 (vs11 vz11)))

def v411 {Γ A B C D E} : Tm11 (snoc11 (snoc11 (snoc11 (snoc11 (snoc11 Γ A) B) C) D) E) A
 := var11 (vs11 (vs11 (vs11 (vs11 vz11))))

def test11 {Γ A} : Tm11 Γ (arr11 (arr11 A A) (arr11 A A))
 := lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011)))))))


def Ty12 : Type 1
 := ∀ (Ty12 : Type)
      (ι   : Ty12)
      (arr : Ty12 → Ty12 → Ty12)
    , Ty12

def ι12 : Ty12 := λ _ ι12 _ => ι12

def arr12 : Ty12 → Ty12 → Ty12
 := λ A B Ty12 ι12 arr12 =>
     arr12 (A Ty12 ι12 arr12) (B Ty12 ι12 arr12)

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
     (vz  : ∀ Γ A, Var12 (snoc12 Γ A) A)
     (vs  : ∀ Γ B A, Var12 Γ A → Var12 (snoc12 Γ B) A)
   , Var12 Γ A

def vz12 {Γ A} : Var12 (snoc12 Γ A) A
 := λ Var12 vz12 vs => vz12 _ _

def vs12 {Γ B A} : Var12 Γ A → Var12 (snoc12 Γ B) A
 := λ x Var12 vz12 vs12 => vs12 _ _ _ (x Var12 vz12 vs12)

def Tm12 : Con12 → Ty12 → Type 1
 := λ Γ A =>
   ∀ (Tm12  : Con12 → Ty12 → Type)
     (var   : ∀ Γ A     , Var12 Γ A → Tm12 Γ A)
     (lam   : ∀ Γ A B   , Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B))
     (app   : ∀ Γ A B   , Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B)
   , Tm12 Γ A

def var12 {Γ A} : Var12 Γ A → Tm12 Γ A
 := λ x Tm12 var12 lam app =>
     var12 _ _ x

def lam12 {Γ A B} : Tm12 (snoc12 Γ A) B → Tm12 Γ (arr12 A B)
 := λ t Tm12 var12 lam12 app =>
     lam12 _ _ _ (t Tm12 var12 lam12 app)

def app12 {Γ A B} : Tm12 Γ (arr12 A B) → Tm12 Γ A → Tm12 Γ B
 := λ t u Tm12 var12 lam12 app12 =>
     app12 _ _ _
         (t Tm12 var12 lam12 app12)
         (u Tm12 var12 lam12 app12)

def v012 {Γ A} : Tm12 (snoc12 Γ A) A
 := var12 vz12

def v112 {Γ A B} : Tm12 (snoc12 (snoc12 Γ A) B) A
 := var12 (vs12 vz12)

def v212 {Γ A B C} : Tm12 (snoc12 (snoc12 (snoc12 Γ A) B) C) A
 := var12 (vs12 (vs12 vz12))

def v312 {Γ A B C D} : Tm12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) A
 := var12 (vs12 (vs12 (vs12 vz12)))

def v412 {Γ A B C D E} : Tm12 (snoc12 (snoc12 (snoc12 (snoc12 (snoc12 Γ A) B) C) D) E) A
 := var12 (vs12 (vs12 (vs12 (vs12 vz12))))

def test12 {Γ A} : Tm12 Γ (arr12 (arr12 A A) (arr12 A A))
 := lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012)))))))


def Ty13 : Type 1
 := ∀ (Ty13 : Type)
      (ι   : Ty13)
      (arr : Ty13 → Ty13 → Ty13)
    , Ty13

def ι13 : Ty13 := λ _ ι13 _ => ι13

def arr13 : Ty13 → Ty13 → Ty13
 := λ A B Ty13 ι13 arr13 =>
     arr13 (A Ty13 ι13 arr13) (B Ty13 ι13 arr13)

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
     (vz  : ∀ Γ A, Var13 (snoc13 Γ A) A)
     (vs  : ∀ Γ B A, Var13 Γ A → Var13 (snoc13 Γ B) A)
   , Var13 Γ A

def vz13 {Γ A} : Var13 (snoc13 Γ A) A
 := λ Var13 vz13 vs => vz13 _ _

def vs13 {Γ B A} : Var13 Γ A → Var13 (snoc13 Γ B) A
 := λ x Var13 vz13 vs13 => vs13 _ _ _ (x Var13 vz13 vs13)

def Tm13 : Con13 → Ty13 → Type 1
 := λ Γ A =>
   ∀ (Tm13  : Con13 → Ty13 → Type)
     (var   : ∀ Γ A     , Var13 Γ A → Tm13 Γ A)
     (lam   : ∀ Γ A B   , Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B))
     (app   : ∀ Γ A B   , Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B)
   , Tm13 Γ A

def var13 {Γ A} : Var13 Γ A → Tm13 Γ A
 := λ x Tm13 var13 lam app =>
     var13 _ _ x

def lam13 {Γ A B} : Tm13 (snoc13 Γ A) B → Tm13 Γ (arr13 A B)
 := λ t Tm13 var13 lam13 app =>
     lam13 _ _ _ (t Tm13 var13 lam13 app)

def app13 {Γ A B} : Tm13 Γ (arr13 A B) → Tm13 Γ A → Tm13 Γ B
 := λ t u Tm13 var13 lam13 app13 =>
     app13 _ _ _
         (t Tm13 var13 lam13 app13)
         (u Tm13 var13 lam13 app13)

def v013 {Γ A} : Tm13 (snoc13 Γ A) A
 := var13 vz13

def v113 {Γ A B} : Tm13 (snoc13 (snoc13 Γ A) B) A
 := var13 (vs13 vz13)

def v213 {Γ A B C} : Tm13 (snoc13 (snoc13 (snoc13 Γ A) B) C) A
 := var13 (vs13 (vs13 vz13))

def v313 {Γ A B C D} : Tm13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) A
 := var13 (vs13 (vs13 (vs13 vz13)))

def v413 {Γ A B C D E} : Tm13 (snoc13 (snoc13 (snoc13 (snoc13 (snoc13 Γ A) B) C) D) E) A
 := var13 (vs13 (vs13 (vs13 (vs13 vz13))))

def test13 {Γ A} : Tm13 Γ (arr13 (arr13 A A) (arr13 A A))
 := lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013)))))))


def Ty14 : Type 1
 := ∀ (Ty14 : Type)
      (ι   : Ty14)
      (arr : Ty14 → Ty14 → Ty14)
    , Ty14

def ι14 : Ty14 := λ _ ι14 _ => ι14

def arr14 : Ty14 → Ty14 → Ty14
 := λ A B Ty14 ι14 arr14 =>
     arr14 (A Ty14 ι14 arr14) (B Ty14 ι14 arr14)

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
     (vz  : ∀ Γ A, Var14 (snoc14 Γ A) A)
     (vs  : ∀ Γ B A, Var14 Γ A → Var14 (snoc14 Γ B) A)
   , Var14 Γ A

def vz14 {Γ A} : Var14 (snoc14 Γ A) A
 := λ Var14 vz14 vs => vz14 _ _

def vs14 {Γ B A} : Var14 Γ A → Var14 (snoc14 Γ B) A
 := λ x Var14 vz14 vs14 => vs14 _ _ _ (x Var14 vz14 vs14)

def Tm14 : Con14 → Ty14 → Type 1
 := λ Γ A =>
   ∀ (Tm14  : Con14 → Ty14 → Type)
     (var   : ∀ Γ A     , Var14 Γ A → Tm14 Γ A)
     (lam   : ∀ Γ A B   , Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B))
     (app   : ∀ Γ A B   , Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B)
   , Tm14 Γ A

def var14 {Γ A} : Var14 Γ A → Tm14 Γ A
 := λ x Tm14 var14 lam app =>
     var14 _ _ x

def lam14 {Γ A B} : Tm14 (snoc14 Γ A) B → Tm14 Γ (arr14 A B)
 := λ t Tm14 var14 lam14 app =>
     lam14 _ _ _ (t Tm14 var14 lam14 app)

def app14 {Γ A B} : Tm14 Γ (arr14 A B) → Tm14 Γ A → Tm14 Γ B
 := λ t u Tm14 var14 lam14 app14 =>
     app14 _ _ _
         (t Tm14 var14 lam14 app14)
         (u Tm14 var14 lam14 app14)

def v014 {Γ A} : Tm14 (snoc14 Γ A) A
 := var14 vz14

def v114 {Γ A B} : Tm14 (snoc14 (snoc14 Γ A) B) A
 := var14 (vs14 vz14)

def v214 {Γ A B C} : Tm14 (snoc14 (snoc14 (snoc14 Γ A) B) C) A
 := var14 (vs14 (vs14 vz14))

def v314 {Γ A B C D} : Tm14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) A
 := var14 (vs14 (vs14 (vs14 vz14)))

def v414 {Γ A B C D E} : Tm14 (snoc14 (snoc14 (snoc14 (snoc14 (snoc14 Γ A) B) C) D) E) A
 := var14 (vs14 (vs14 (vs14 (vs14 vz14))))

def test14 {Γ A} : Tm14 Γ (arr14 (arr14 A A) (arr14 A A))
 := lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014)))))))


def Ty15 : Type 1
 := ∀ (Ty15 : Type)
      (ι   : Ty15)
      (arr : Ty15 → Ty15 → Ty15)
    , Ty15

def ι15 : Ty15 := λ _ ι15 _ => ι15

def arr15 : Ty15 → Ty15 → Ty15
 := λ A B Ty15 ι15 arr15 =>
     arr15 (A Ty15 ι15 arr15) (B Ty15 ι15 arr15)

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
     (vz  : ∀ Γ A, Var15 (snoc15 Γ A) A)
     (vs  : ∀ Γ B A, Var15 Γ A → Var15 (snoc15 Γ B) A)
   , Var15 Γ A

def vz15 {Γ A} : Var15 (snoc15 Γ A) A
 := λ Var15 vz15 vs => vz15 _ _

def vs15 {Γ B A} : Var15 Γ A → Var15 (snoc15 Γ B) A
 := λ x Var15 vz15 vs15 => vs15 _ _ _ (x Var15 vz15 vs15)

def Tm15 : Con15 → Ty15 → Type 1
 := λ Γ A =>
   ∀ (Tm15  : Con15 → Ty15 → Type)
     (var   : ∀ Γ A     , Var15 Γ A → Tm15 Γ A)
     (lam   : ∀ Γ A B   , Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B))
     (app   : ∀ Γ A B   , Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B)
   , Tm15 Γ A

def var15 {Γ A} : Var15 Γ A → Tm15 Γ A
 := λ x Tm15 var15 lam app =>
     var15 _ _ x

def lam15 {Γ A B} : Tm15 (snoc15 Γ A) B → Tm15 Γ (arr15 A B)
 := λ t Tm15 var15 lam15 app =>
     lam15 _ _ _ (t Tm15 var15 lam15 app)

def app15 {Γ A B} : Tm15 Γ (arr15 A B) → Tm15 Γ A → Tm15 Γ B
 := λ t u Tm15 var15 lam15 app15 =>
     app15 _ _ _
         (t Tm15 var15 lam15 app15)
         (u Tm15 var15 lam15 app15)

def v015 {Γ A} : Tm15 (snoc15 Γ A) A
 := var15 vz15

def v115 {Γ A B} : Tm15 (snoc15 (snoc15 Γ A) B) A
 := var15 (vs15 vz15)

def v215 {Γ A B C} : Tm15 (snoc15 (snoc15 (snoc15 Γ A) B) C) A
 := var15 (vs15 (vs15 vz15))

def v315 {Γ A B C D} : Tm15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) A
 := var15 (vs15 (vs15 (vs15 vz15)))

def v415 {Γ A B C D E} : Tm15 (snoc15 (snoc15 (snoc15 (snoc15 (snoc15 Γ A) B) C) D) E) A
 := var15 (vs15 (vs15 (vs15 (vs15 vz15))))

def test15 {Γ A} : Tm15 Γ (arr15 (arr15 A A) (arr15 A A))
 := lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015)))))))


def Ty16 : Type 1
 := ∀ (Ty16 : Type)
      (ι   : Ty16)
      (arr : Ty16 → Ty16 → Ty16)
    , Ty16

def ι16 : Ty16 := λ _ ι16 _ => ι16

def arr16 : Ty16 → Ty16 → Ty16
 := λ A B Ty16 ι16 arr16 =>
     arr16 (A Ty16 ι16 arr16) (B Ty16 ι16 arr16)

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
     (vz  : ∀ Γ A, Var16 (snoc16 Γ A) A)
     (vs  : ∀ Γ B A, Var16 Γ A → Var16 (snoc16 Γ B) A)
   , Var16 Γ A

def vz16 {Γ A} : Var16 (snoc16 Γ A) A
 := λ Var16 vz16 vs => vz16 _ _

def vs16 {Γ B A} : Var16 Γ A → Var16 (snoc16 Γ B) A
 := λ x Var16 vz16 vs16 => vs16 _ _ _ (x Var16 vz16 vs16)

def Tm16 : Con16 → Ty16 → Type 1
 := λ Γ A =>
   ∀ (Tm16  : Con16 → Ty16 → Type)
     (var   : ∀ Γ A     , Var16 Γ A → Tm16 Γ A)
     (lam   : ∀ Γ A B   , Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B))
     (app   : ∀ Γ A B   , Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B)
   , Tm16 Γ A

def var16 {Γ A} : Var16 Γ A → Tm16 Γ A
 := λ x Tm16 var16 lam app =>
     var16 _ _ x

def lam16 {Γ A B} : Tm16 (snoc16 Γ A) B → Tm16 Γ (arr16 A B)
 := λ t Tm16 var16 lam16 app =>
     lam16 _ _ _ (t Tm16 var16 lam16 app)

def app16 {Γ A B} : Tm16 Γ (arr16 A B) → Tm16 Γ A → Tm16 Γ B
 := λ t u Tm16 var16 lam16 app16 =>
     app16 _ _ _
         (t Tm16 var16 lam16 app16)
         (u Tm16 var16 lam16 app16)

def v016 {Γ A} : Tm16 (snoc16 Γ A) A
 := var16 vz16

def v116 {Γ A B} : Tm16 (snoc16 (snoc16 Γ A) B) A
 := var16 (vs16 vz16)

def v216 {Γ A B C} : Tm16 (snoc16 (snoc16 (snoc16 Γ A) B) C) A
 := var16 (vs16 (vs16 vz16))

def v316 {Γ A B C D} : Tm16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) A
 := var16 (vs16 (vs16 (vs16 vz16)))

def v416 {Γ A B C D E} : Tm16 (snoc16 (snoc16 (snoc16 (snoc16 (snoc16 Γ A) B) C) D) E) A
 := var16 (vs16 (vs16 (vs16 (vs16 vz16))))

def test16 {Γ A} : Tm16 Γ (arr16 (arr16 A A) (arr16 A A))
 := lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016)))))))


def Ty17 : Type 1
 := ∀ (Ty17 : Type)
      (ι   : Ty17)
      (arr : Ty17 → Ty17 → Ty17)
    , Ty17

def ι17 : Ty17 := λ _ ι17 _ => ι17

def arr17 : Ty17 → Ty17 → Ty17
 := λ A B Ty17 ι17 arr17 =>
     arr17 (A Ty17 ι17 arr17) (B Ty17 ι17 arr17)

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
     (vz  : ∀ Γ A, Var17 (snoc17 Γ A) A)
     (vs  : ∀ Γ B A, Var17 Γ A → Var17 (snoc17 Γ B) A)
   , Var17 Γ A

def vz17 {Γ A} : Var17 (snoc17 Γ A) A
 := λ Var17 vz17 vs => vz17 _ _

def vs17 {Γ B A} : Var17 Γ A → Var17 (snoc17 Γ B) A
 := λ x Var17 vz17 vs17 => vs17 _ _ _ (x Var17 vz17 vs17)

def Tm17 : Con17 → Ty17 → Type 1
 := λ Γ A =>
   ∀ (Tm17  : Con17 → Ty17 → Type)
     (var   : ∀ Γ A     , Var17 Γ A → Tm17 Γ A)
     (lam   : ∀ Γ A B   , Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B))
     (app   : ∀ Γ A B   , Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B)
   , Tm17 Γ A

def var17 {Γ A} : Var17 Γ A → Tm17 Γ A
 := λ x Tm17 var17 lam app =>
     var17 _ _ x

def lam17 {Γ A B} : Tm17 (snoc17 Γ A) B → Tm17 Γ (arr17 A B)
 := λ t Tm17 var17 lam17 app =>
     lam17 _ _ _ (t Tm17 var17 lam17 app)

def app17 {Γ A B} : Tm17 Γ (arr17 A B) → Tm17 Γ A → Tm17 Γ B
 := λ t u Tm17 var17 lam17 app17 =>
     app17 _ _ _
         (t Tm17 var17 lam17 app17)
         (u Tm17 var17 lam17 app17)

def v017 {Γ A} : Tm17 (snoc17 Γ A) A
 := var17 vz17

def v117 {Γ A B} : Tm17 (snoc17 (snoc17 Γ A) B) A
 := var17 (vs17 vz17)

def v217 {Γ A B C} : Tm17 (snoc17 (snoc17 (snoc17 Γ A) B) C) A
 := var17 (vs17 (vs17 vz17))

def v317 {Γ A B C D} : Tm17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) A
 := var17 (vs17 (vs17 (vs17 vz17)))

def v417 {Γ A B C D E} : Tm17 (snoc17 (snoc17 (snoc17 (snoc17 (snoc17 Γ A) B) C) D) E) A
 := var17 (vs17 (vs17 (vs17 (vs17 vz17))))

def test17 {Γ A} : Tm17 Γ (arr17 (arr17 A A) (arr17 A A))
 := lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017)))))))


def Ty18 : Type 1
 := ∀ (Ty18 : Type)
      (ι   : Ty18)
      (arr : Ty18 → Ty18 → Ty18)
    , Ty18

def ι18 : Ty18 := λ _ ι18 _ => ι18

def arr18 : Ty18 → Ty18 → Ty18
 := λ A B Ty18 ι18 arr18 =>
     arr18 (A Ty18 ι18 arr18) (B Ty18 ι18 arr18)

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
     (vz  : ∀ Γ A, Var18 (snoc18 Γ A) A)
     (vs  : ∀ Γ B A, Var18 Γ A → Var18 (snoc18 Γ B) A)
   , Var18 Γ A

def vz18 {Γ A} : Var18 (snoc18 Γ A) A
 := λ Var18 vz18 vs => vz18 _ _

def vs18 {Γ B A} : Var18 Γ A → Var18 (snoc18 Γ B) A
 := λ x Var18 vz18 vs18 => vs18 _ _ _ (x Var18 vz18 vs18)

def Tm18 : Con18 → Ty18 → Type 1
 := λ Γ A =>
   ∀ (Tm18  : Con18 → Ty18 → Type)
     (var   : ∀ Γ A     , Var18 Γ A → Tm18 Γ A)
     (lam   : ∀ Γ A B   , Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B))
     (app   : ∀ Γ A B   , Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B)
   , Tm18 Γ A

def var18 {Γ A} : Var18 Γ A → Tm18 Γ A
 := λ x Tm18 var18 lam app =>
     var18 _ _ x

def lam18 {Γ A B} : Tm18 (snoc18 Γ A) B → Tm18 Γ (arr18 A B)
 := λ t Tm18 var18 lam18 app =>
     lam18 _ _ _ (t Tm18 var18 lam18 app)

def app18 {Γ A B} : Tm18 Γ (arr18 A B) → Tm18 Γ A → Tm18 Γ B
 := λ t u Tm18 var18 lam18 app18 =>
     app18 _ _ _
         (t Tm18 var18 lam18 app18)
         (u Tm18 var18 lam18 app18)

def v018 {Γ A} : Tm18 (snoc18 Γ A) A
 := var18 vz18

def v118 {Γ A B} : Tm18 (snoc18 (snoc18 Γ A) B) A
 := var18 (vs18 vz18)

def v218 {Γ A B C} : Tm18 (snoc18 (snoc18 (snoc18 Γ A) B) C) A
 := var18 (vs18 (vs18 vz18))

def v318 {Γ A B C D} : Tm18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) A
 := var18 (vs18 (vs18 (vs18 vz18)))

def v418 {Γ A B C D E} : Tm18 (snoc18 (snoc18 (snoc18 (snoc18 (snoc18 Γ A) B) C) D) E) A
 := var18 (vs18 (vs18 (vs18 (vs18 vz18))))

def test18 {Γ A} : Tm18 Γ (arr18 (arr18 A A) (arr18 A A))
 := lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018)))))))


def Ty19 : Type 1
 := ∀ (Ty19 : Type)
      (ι   : Ty19)
      (arr : Ty19 → Ty19 → Ty19)
    , Ty19

def ι19 : Ty19 := λ _ ι19 _ => ι19

def arr19 : Ty19 → Ty19 → Ty19
 := λ A B Ty19 ι19 arr19 =>
     arr19 (A Ty19 ι19 arr19) (B Ty19 ι19 arr19)

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
     (vz  : ∀ Γ A, Var19 (snoc19 Γ A) A)
     (vs  : ∀ Γ B A, Var19 Γ A → Var19 (snoc19 Γ B) A)
   , Var19 Γ A

def vz19 {Γ A} : Var19 (snoc19 Γ A) A
 := λ Var19 vz19 vs => vz19 _ _

def vs19 {Γ B A} : Var19 Γ A → Var19 (snoc19 Γ B) A
 := λ x Var19 vz19 vs19 => vs19 _ _ _ (x Var19 vz19 vs19)

def Tm19 : Con19 → Ty19 → Type 1
 := λ Γ A =>
   ∀ (Tm19  : Con19 → Ty19 → Type)
     (var   : ∀ Γ A     , Var19 Γ A → Tm19 Γ A)
     (lam   : ∀ Γ A B   , Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B))
     (app   : ∀ Γ A B   , Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B)
   , Tm19 Γ A

def var19 {Γ A} : Var19 Γ A → Tm19 Γ A
 := λ x Tm19 var19 lam app =>
     var19 _ _ x

def lam19 {Γ A B} : Tm19 (snoc19 Γ A) B → Tm19 Γ (arr19 A B)
 := λ t Tm19 var19 lam19 app =>
     lam19 _ _ _ (t Tm19 var19 lam19 app)

def app19 {Γ A B} : Tm19 Γ (arr19 A B) → Tm19 Γ A → Tm19 Γ B
 := λ t u Tm19 var19 lam19 app19 =>
     app19 _ _ _
         (t Tm19 var19 lam19 app19)
         (u Tm19 var19 lam19 app19)

def v019 {Γ A} : Tm19 (snoc19 Γ A) A
 := var19 vz19

def v119 {Γ A B} : Tm19 (snoc19 (snoc19 Γ A) B) A
 := var19 (vs19 vz19)

def v219 {Γ A B C} : Tm19 (snoc19 (snoc19 (snoc19 Γ A) B) C) A
 := var19 (vs19 (vs19 vz19))

def v319 {Γ A B C D} : Tm19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) A
 := var19 (vs19 (vs19 (vs19 vz19)))

def v419 {Γ A B C D E} : Tm19 (snoc19 (snoc19 (snoc19 (snoc19 (snoc19 Γ A) B) C) D) E) A
 := var19 (vs19 (vs19 (vs19 (vs19 vz19))))

def test19 {Γ A} : Tm19 Γ (arr19 (arr19 A A) (arr19 A A))
 := lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019)))))))


def Ty20 : Type 1
 := ∀ (Ty20 : Type)
      (ι   : Ty20)
      (arr : Ty20 → Ty20 → Ty20)
    , Ty20

def ι20 : Ty20 := λ _ ι20 _ => ι20

def arr20 : Ty20 → Ty20 → Ty20
 := λ A B Ty20 ι20 arr20 =>
     arr20 (A Ty20 ι20 arr20) (B Ty20 ι20 arr20)

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
     (vz  : ∀ Γ A, Var20 (snoc20 Γ A) A)
     (vs  : ∀ Γ B A, Var20 Γ A → Var20 (snoc20 Γ B) A)
   , Var20 Γ A

def vz20 {Γ A} : Var20 (snoc20 Γ A) A
 := λ Var20 vz20 vs => vz20 _ _

def vs20 {Γ B A} : Var20 Γ A → Var20 (snoc20 Γ B) A
 := λ x Var20 vz20 vs20 => vs20 _ _ _ (x Var20 vz20 vs20)

def Tm20 : Con20 → Ty20 → Type 1
 := λ Γ A =>
   ∀ (Tm20  : Con20 → Ty20 → Type)
     (var   : ∀ Γ A     , Var20 Γ A → Tm20 Γ A)
     (lam   : ∀ Γ A B   , Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B))
     (app   : ∀ Γ A B   , Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B)
   , Tm20 Γ A

def var20 {Γ A} : Var20 Γ A → Tm20 Γ A
 := λ x Tm20 var20 lam app =>
     var20 _ _ x

def lam20 {Γ A B} : Tm20 (snoc20 Γ A) B → Tm20 Γ (arr20 A B)
 := λ t Tm20 var20 lam20 app =>
     lam20 _ _ _ (t Tm20 var20 lam20 app)

def app20 {Γ A B} : Tm20 Γ (arr20 A B) → Tm20 Γ A → Tm20 Γ B
 := λ t u Tm20 var20 lam20 app20 =>
     app20 _ _ _
         (t Tm20 var20 lam20 app20)
         (u Tm20 var20 lam20 app20)

def v020 {Γ A} : Tm20 (snoc20 Γ A) A
 := var20 vz20

def v120 {Γ A B} : Tm20 (snoc20 (snoc20 Γ A) B) A
 := var20 (vs20 vz20)

def v220 {Γ A B C} : Tm20 (snoc20 (snoc20 (snoc20 Γ A) B) C) A
 := var20 (vs20 (vs20 vz20))

def v320 {Γ A B C D} : Tm20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) A
 := var20 (vs20 (vs20 (vs20 vz20)))

def v420 {Γ A B C D E} : Tm20 (snoc20 (snoc20 (snoc20 (snoc20 (snoc20 Γ A) B) C) D) E) A
 := var20 (vs20 (vs20 (vs20 (vs20 vz20))))

def test20 {Γ A} : Tm20 Γ (arr20 (arr20 A A) (arr20 A A))
 := lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020)))))))


def Ty21 : Type 1
 := ∀ (Ty21 : Type)
      (ι   : Ty21)
      (arr : Ty21 → Ty21 → Ty21)
    , Ty21

def ι21 : Ty21 := λ _ ι21 _ => ι21

def arr21 : Ty21 → Ty21 → Ty21
 := λ A B Ty21 ι21 arr21 =>
     arr21 (A Ty21 ι21 arr21) (B Ty21 ι21 arr21)

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
     (vz  : ∀ Γ A, Var21 (snoc21 Γ A) A)
     (vs  : ∀ Γ B A, Var21 Γ A → Var21 (snoc21 Γ B) A)
   , Var21 Γ A

def vz21 {Γ A} : Var21 (snoc21 Γ A) A
 := λ Var21 vz21 vs => vz21 _ _

def vs21 {Γ B A} : Var21 Γ A → Var21 (snoc21 Γ B) A
 := λ x Var21 vz21 vs21 => vs21 _ _ _ (x Var21 vz21 vs21)

def Tm21 : Con21 → Ty21 → Type 1
 := λ Γ A =>
   ∀ (Tm21  : Con21 → Ty21 → Type)
     (var   : ∀ Γ A     , Var21 Γ A → Tm21 Γ A)
     (lam   : ∀ Γ A B   , Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B))
     (app   : ∀ Γ A B   , Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B)
   , Tm21 Γ A

def var21 {Γ A} : Var21 Γ A → Tm21 Γ A
 := λ x Tm21 var21 lam app =>
     var21 _ _ x

def lam21 {Γ A B} : Tm21 (snoc21 Γ A) B → Tm21 Γ (arr21 A B)
 := λ t Tm21 var21 lam21 app =>
     lam21 _ _ _ (t Tm21 var21 lam21 app)

def app21 {Γ A B} : Tm21 Γ (arr21 A B) → Tm21 Γ A → Tm21 Γ B
 := λ t u Tm21 var21 lam21 app21 =>
     app21 _ _ _
         (t Tm21 var21 lam21 app21)
         (u Tm21 var21 lam21 app21)

def v021 {Γ A} : Tm21 (snoc21 Γ A) A
 := var21 vz21

def v121 {Γ A B} : Tm21 (snoc21 (snoc21 Γ A) B) A
 := var21 (vs21 vz21)

def v221 {Γ A B C} : Tm21 (snoc21 (snoc21 (snoc21 Γ A) B) C) A
 := var21 (vs21 (vs21 vz21))

def v321 {Γ A B C D} : Tm21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) A
 := var21 (vs21 (vs21 (vs21 vz21)))

def v421 {Γ A B C D E} : Tm21 (snoc21 (snoc21 (snoc21 (snoc21 (snoc21 Γ A) B) C) D) E) A
 := var21 (vs21 (vs21 (vs21 (vs21 vz21))))

def test21 {Γ A} : Tm21 Γ (arr21 (arr21 A A) (arr21 A A))
 := lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021)))))))


def Ty22 : Type 1
 := ∀ (Ty22 : Type)
      (ι   : Ty22)
      (arr : Ty22 → Ty22 → Ty22)
    , Ty22

def ι22 : Ty22 := λ _ ι22 _ => ι22

def arr22 : Ty22 → Ty22 → Ty22
 := λ A B Ty22 ι22 arr22 =>
     arr22 (A Ty22 ι22 arr22) (B Ty22 ι22 arr22)

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
     (vz  : ∀ Γ A, Var22 (snoc22 Γ A) A)
     (vs  : ∀ Γ B A, Var22 Γ A → Var22 (snoc22 Γ B) A)
   , Var22 Γ A

def vz22 {Γ A} : Var22 (snoc22 Γ A) A
 := λ Var22 vz22 vs => vz22 _ _

def vs22 {Γ B A} : Var22 Γ A → Var22 (snoc22 Γ B) A
 := λ x Var22 vz22 vs22 => vs22 _ _ _ (x Var22 vz22 vs22)

def Tm22 : Con22 → Ty22 → Type 1
 := λ Γ A =>
   ∀ (Tm22  : Con22 → Ty22 → Type)
     (var   : ∀ Γ A     , Var22 Γ A → Tm22 Γ A)
     (lam   : ∀ Γ A B   , Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B))
     (app   : ∀ Γ A B   , Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B)
   , Tm22 Γ A

def var22 {Γ A} : Var22 Γ A → Tm22 Γ A
 := λ x Tm22 var22 lam app =>
     var22 _ _ x

def lam22 {Γ A B} : Tm22 (snoc22 Γ A) B → Tm22 Γ (arr22 A B)
 := λ t Tm22 var22 lam22 app =>
     lam22 _ _ _ (t Tm22 var22 lam22 app)

def app22 {Γ A B} : Tm22 Γ (arr22 A B) → Tm22 Γ A → Tm22 Γ B
 := λ t u Tm22 var22 lam22 app22 =>
     app22 _ _ _
         (t Tm22 var22 lam22 app22)
         (u Tm22 var22 lam22 app22)

def v022 {Γ A} : Tm22 (snoc22 Γ A) A
 := var22 vz22

def v122 {Γ A B} : Tm22 (snoc22 (snoc22 Γ A) B) A
 := var22 (vs22 vz22)

def v222 {Γ A B C} : Tm22 (snoc22 (snoc22 (snoc22 Γ A) B) C) A
 := var22 (vs22 (vs22 vz22))

def v322 {Γ A B C D} : Tm22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) A
 := var22 (vs22 (vs22 (vs22 vz22)))

def v422 {Γ A B C D E} : Tm22 (snoc22 (snoc22 (snoc22 (snoc22 (snoc22 Γ A) B) C) D) E) A
 := var22 (vs22 (vs22 (vs22 (vs22 vz22))))

def test22 {Γ A} : Tm22 Γ (arr22 (arr22 A A) (arr22 A A))
 := lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022)))))))


def Ty23 : Type 1
 := ∀ (Ty23 : Type)
      (ι   : Ty23)
      (arr : Ty23 → Ty23 → Ty23)
    , Ty23

def ι23 : Ty23 := λ _ ι23 _ => ι23

def arr23 : Ty23 → Ty23 → Ty23
 := λ A B Ty23 ι23 arr23 =>
     arr23 (A Ty23 ι23 arr23) (B Ty23 ι23 arr23)

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
     (vz  : ∀ Γ A, Var23 (snoc23 Γ A) A)
     (vs  : ∀ Γ B A, Var23 Γ A → Var23 (snoc23 Γ B) A)
   , Var23 Γ A

def vz23 {Γ A} : Var23 (snoc23 Γ A) A
 := λ Var23 vz23 vs => vz23 _ _

def vs23 {Γ B A} : Var23 Γ A → Var23 (snoc23 Γ B) A
 := λ x Var23 vz23 vs23 => vs23 _ _ _ (x Var23 vz23 vs23)

def Tm23 : Con23 → Ty23 → Type 1
 := λ Γ A =>
   ∀ (Tm23  : Con23 → Ty23 → Type)
     (var   : ∀ Γ A     , Var23 Γ A → Tm23 Γ A)
     (lam   : ∀ Γ A B   , Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B))
     (app   : ∀ Γ A B   , Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B)
   , Tm23 Γ A

def var23 {Γ A} : Var23 Γ A → Tm23 Γ A
 := λ x Tm23 var23 lam app =>
     var23 _ _ x

def lam23 {Γ A B} : Tm23 (snoc23 Γ A) B → Tm23 Γ (arr23 A B)
 := λ t Tm23 var23 lam23 app =>
     lam23 _ _ _ (t Tm23 var23 lam23 app)

def app23 {Γ A B} : Tm23 Γ (arr23 A B) → Tm23 Γ A → Tm23 Γ B
 := λ t u Tm23 var23 lam23 app23 =>
     app23 _ _ _
         (t Tm23 var23 lam23 app23)
         (u Tm23 var23 lam23 app23)

def v023 {Γ A} : Tm23 (snoc23 Γ A) A
 := var23 vz23

def v123 {Γ A B} : Tm23 (snoc23 (snoc23 Γ A) B) A
 := var23 (vs23 vz23)

def v223 {Γ A B C} : Tm23 (snoc23 (snoc23 (snoc23 Γ A) B) C) A
 := var23 (vs23 (vs23 vz23))

def v323 {Γ A B C D} : Tm23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) A
 := var23 (vs23 (vs23 (vs23 vz23)))

def v423 {Γ A B C D E} : Tm23 (snoc23 (snoc23 (snoc23 (snoc23 (snoc23 Γ A) B) C) D) E) A
 := var23 (vs23 (vs23 (vs23 (vs23 vz23))))

def test23 {Γ A} : Tm23 Γ (arr23 (arr23 A A) (arr23 A A))
 := lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023)))))))


def Ty24 : Type 1
 := ∀ (Ty24 : Type)
      (ι   : Ty24)
      (arr : Ty24 → Ty24 → Ty24)
    , Ty24

def ι24 : Ty24 := λ _ ι24 _ => ι24

def arr24 : Ty24 → Ty24 → Ty24
 := λ A B Ty24 ι24 arr24 =>
     arr24 (A Ty24 ι24 arr24) (B Ty24 ι24 arr24)

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
     (vz  : ∀ Γ A, Var24 (snoc24 Γ A) A)
     (vs  : ∀ Γ B A, Var24 Γ A → Var24 (snoc24 Γ B) A)
   , Var24 Γ A

def vz24 {Γ A} : Var24 (snoc24 Γ A) A
 := λ Var24 vz24 vs => vz24 _ _

def vs24 {Γ B A} : Var24 Γ A → Var24 (snoc24 Γ B) A
 := λ x Var24 vz24 vs24 => vs24 _ _ _ (x Var24 vz24 vs24)

def Tm24 : Con24 → Ty24 → Type 1
 := λ Γ A =>
   ∀ (Tm24  : Con24 → Ty24 → Type)
     (var   : ∀ Γ A     , Var24 Γ A → Tm24 Γ A)
     (lam   : ∀ Γ A B   , Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B))
     (app   : ∀ Γ A B   , Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B)
   , Tm24 Γ A

def var24 {Γ A} : Var24 Γ A → Tm24 Γ A
 := λ x Tm24 var24 lam app =>
     var24 _ _ x

def lam24 {Γ A B} : Tm24 (snoc24 Γ A) B → Tm24 Γ (arr24 A B)
 := λ t Tm24 var24 lam24 app =>
     lam24 _ _ _ (t Tm24 var24 lam24 app)

def app24 {Γ A B} : Tm24 Γ (arr24 A B) → Tm24 Γ A → Tm24 Γ B
 := λ t u Tm24 var24 lam24 app24 =>
     app24 _ _ _
         (t Tm24 var24 lam24 app24)
         (u Tm24 var24 lam24 app24)

def v024 {Γ A} : Tm24 (snoc24 Γ A) A
 := var24 vz24

def v124 {Γ A B} : Tm24 (snoc24 (snoc24 Γ A) B) A
 := var24 (vs24 vz24)

def v224 {Γ A B C} : Tm24 (snoc24 (snoc24 (snoc24 Γ A) B) C) A
 := var24 (vs24 (vs24 vz24))

def v324 {Γ A B C D} : Tm24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) A
 := var24 (vs24 (vs24 (vs24 vz24)))

def v424 {Γ A B C D E} : Tm24 (snoc24 (snoc24 (snoc24 (snoc24 (snoc24 Γ A) B) C) D) E) A
 := var24 (vs24 (vs24 (vs24 (vs24 vz24))))

def test24 {Γ A} : Tm24 Γ (arr24 (arr24 A A) (arr24 A A))
 := lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024)))))))


def Ty25 : Type 1
 := ∀ (Ty25 : Type)
      (ι   : Ty25)
      (arr : Ty25 → Ty25 → Ty25)
    , Ty25

def ι25 : Ty25 := λ _ ι25 _ => ι25

def arr25 : Ty25 → Ty25 → Ty25
 := λ A B Ty25 ι25 arr25 =>
     arr25 (A Ty25 ι25 arr25) (B Ty25 ι25 arr25)

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
     (vz  : ∀ Γ A, Var25 (snoc25 Γ A) A)
     (vs  : ∀ Γ B A, Var25 Γ A → Var25 (snoc25 Γ B) A)
   , Var25 Γ A

def vz25 {Γ A} : Var25 (snoc25 Γ A) A
 := λ Var25 vz25 vs => vz25 _ _

def vs25 {Γ B A} : Var25 Γ A → Var25 (snoc25 Γ B) A
 := λ x Var25 vz25 vs25 => vs25 _ _ _ (x Var25 vz25 vs25)

def Tm25 : Con25 → Ty25 → Type 1
 := λ Γ A =>
   ∀ (Tm25  : Con25 → Ty25 → Type)
     (var   : ∀ Γ A     , Var25 Γ A → Tm25 Γ A)
     (lam   : ∀ Γ A B   , Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B))
     (app   : ∀ Γ A B   , Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B)
   , Tm25 Γ A

def var25 {Γ A} : Var25 Γ A → Tm25 Γ A
 := λ x Tm25 var25 lam app =>
     var25 _ _ x

def lam25 {Γ A B} : Tm25 (snoc25 Γ A) B → Tm25 Γ (arr25 A B)
 := λ t Tm25 var25 lam25 app =>
     lam25 _ _ _ (t Tm25 var25 lam25 app)

def app25 {Γ A B} : Tm25 Γ (arr25 A B) → Tm25 Γ A → Tm25 Γ B
 := λ t u Tm25 var25 lam25 app25 =>
     app25 _ _ _
         (t Tm25 var25 lam25 app25)
         (u Tm25 var25 lam25 app25)

def v025 {Γ A} : Tm25 (snoc25 Γ A) A
 := var25 vz25

def v125 {Γ A B} : Tm25 (snoc25 (snoc25 Γ A) B) A
 := var25 (vs25 vz25)

def v225 {Γ A B C} : Tm25 (snoc25 (snoc25 (snoc25 Γ A) B) C) A
 := var25 (vs25 (vs25 vz25))

def v325 {Γ A B C D} : Tm25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) A
 := var25 (vs25 (vs25 (vs25 vz25)))

def v425 {Γ A B C D E} : Tm25 (snoc25 (snoc25 (snoc25 (snoc25 (snoc25 Γ A) B) C) D) E) A
 := var25 (vs25 (vs25 (vs25 (vs25 vz25))))

def test25 {Γ A} : Tm25 Γ (arr25 (arr25 A A) (arr25 A A))
 := lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025)))))))


def Ty26 : Type 1
 := ∀ (Ty26 : Type)
      (ι   : Ty26)
      (arr : Ty26 → Ty26 → Ty26)
    , Ty26

def ι26 : Ty26 := λ _ ι26 _ => ι26

def arr26 : Ty26 → Ty26 → Ty26
 := λ A B Ty26 ι26 arr26 =>
     arr26 (A Ty26 ι26 arr26) (B Ty26 ι26 arr26)

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
     (vz  : ∀ Γ A, Var26 (snoc26 Γ A) A)
     (vs  : ∀ Γ B A, Var26 Γ A → Var26 (snoc26 Γ B) A)
   , Var26 Γ A

def vz26 {Γ A} : Var26 (snoc26 Γ A) A
 := λ Var26 vz26 vs => vz26 _ _

def vs26 {Γ B A} : Var26 Γ A → Var26 (snoc26 Γ B) A
 := λ x Var26 vz26 vs26 => vs26 _ _ _ (x Var26 vz26 vs26)

def Tm26 : Con26 → Ty26 → Type 1
 := λ Γ A =>
   ∀ (Tm26  : Con26 → Ty26 → Type)
     (var   : ∀ Γ A     , Var26 Γ A → Tm26 Γ A)
     (lam   : ∀ Γ A B   , Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B))
     (app   : ∀ Γ A B   , Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B)
   , Tm26 Γ A

def var26 {Γ A} : Var26 Γ A → Tm26 Γ A
 := λ x Tm26 var26 lam app =>
     var26 _ _ x

def lam26 {Γ A B} : Tm26 (snoc26 Γ A) B → Tm26 Γ (arr26 A B)
 := λ t Tm26 var26 lam26 app =>
     lam26 _ _ _ (t Tm26 var26 lam26 app)

def app26 {Γ A B} : Tm26 Γ (arr26 A B) → Tm26 Γ A → Tm26 Γ B
 := λ t u Tm26 var26 lam26 app26 =>
     app26 _ _ _
         (t Tm26 var26 lam26 app26)
         (u Tm26 var26 lam26 app26)

def v026 {Γ A} : Tm26 (snoc26 Γ A) A
 := var26 vz26

def v126 {Γ A B} : Tm26 (snoc26 (snoc26 Γ A) B) A
 := var26 (vs26 vz26)

def v226 {Γ A B C} : Tm26 (snoc26 (snoc26 (snoc26 Γ A) B) C) A
 := var26 (vs26 (vs26 vz26))

def v326 {Γ A B C D} : Tm26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) A
 := var26 (vs26 (vs26 (vs26 vz26)))

def v426 {Γ A B C D E} : Tm26 (snoc26 (snoc26 (snoc26 (snoc26 (snoc26 Γ A) B) C) D) E) A
 := var26 (vs26 (vs26 (vs26 (vs26 vz26))))

def test26 {Γ A} : Tm26 Γ (arr26 (arr26 A A) (arr26 A A))
 := lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026)))))))


def Ty27 : Type 1
 := ∀ (Ty27 : Type)
      (ι   : Ty27)
      (arr : Ty27 → Ty27 → Ty27)
    , Ty27

def ι27 : Ty27 := λ _ ι27 _ => ι27

def arr27 : Ty27 → Ty27 → Ty27
 := λ A B Ty27 ι27 arr27 =>
     arr27 (A Ty27 ι27 arr27) (B Ty27 ι27 arr27)

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
     (vz  : ∀ Γ A, Var27 (snoc27 Γ A) A)
     (vs  : ∀ Γ B A, Var27 Γ A → Var27 (snoc27 Γ B) A)
   , Var27 Γ A

def vz27 {Γ A} : Var27 (snoc27 Γ A) A
 := λ Var27 vz27 vs => vz27 _ _

def vs27 {Γ B A} : Var27 Γ A → Var27 (snoc27 Γ B) A
 := λ x Var27 vz27 vs27 => vs27 _ _ _ (x Var27 vz27 vs27)

def Tm27 : Con27 → Ty27 → Type 1
 := λ Γ A =>
   ∀ (Tm27  : Con27 → Ty27 → Type)
     (var   : ∀ Γ A     , Var27 Γ A → Tm27 Γ A)
     (lam   : ∀ Γ A B   , Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B))
     (app   : ∀ Γ A B   , Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B)
   , Tm27 Γ A

def var27 {Γ A} : Var27 Γ A → Tm27 Γ A
 := λ x Tm27 var27 lam app =>
     var27 _ _ x

def lam27 {Γ A B} : Tm27 (snoc27 Γ A) B → Tm27 Γ (arr27 A B)
 := λ t Tm27 var27 lam27 app =>
     lam27 _ _ _ (t Tm27 var27 lam27 app)

def app27 {Γ A B} : Tm27 Γ (arr27 A B) → Tm27 Γ A → Tm27 Γ B
 := λ t u Tm27 var27 lam27 app27 =>
     app27 _ _ _
         (t Tm27 var27 lam27 app27)
         (u Tm27 var27 lam27 app27)

def v027 {Γ A} : Tm27 (snoc27 Γ A) A
 := var27 vz27

def v127 {Γ A B} : Tm27 (snoc27 (snoc27 Γ A) B) A
 := var27 (vs27 vz27)

def v227 {Γ A B C} : Tm27 (snoc27 (snoc27 (snoc27 Γ A) B) C) A
 := var27 (vs27 (vs27 vz27))

def v327 {Γ A B C D} : Tm27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) A
 := var27 (vs27 (vs27 (vs27 vz27)))

def v427 {Γ A B C D E} : Tm27 (snoc27 (snoc27 (snoc27 (snoc27 (snoc27 Γ A) B) C) D) E) A
 := var27 (vs27 (vs27 (vs27 (vs27 vz27))))

def test27 {Γ A} : Tm27 Γ (arr27 (arr27 A A) (arr27 A A))
 := lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027)))))))


def Ty28 : Type 1
 := ∀ (Ty28 : Type)
      (ι   : Ty28)
      (arr : Ty28 → Ty28 → Ty28)
    , Ty28

def ι28 : Ty28 := λ _ ι28 _ => ι28

def arr28 : Ty28 → Ty28 → Ty28
 := λ A B Ty28 ι28 arr28 =>
     arr28 (A Ty28 ι28 arr28) (B Ty28 ι28 arr28)

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
     (vz  : ∀ Γ A, Var28 (snoc28 Γ A) A)
     (vs  : ∀ Γ B A, Var28 Γ A → Var28 (snoc28 Γ B) A)
   , Var28 Γ A

def vz28 {Γ A} : Var28 (snoc28 Γ A) A
 := λ Var28 vz28 vs => vz28 _ _

def vs28 {Γ B A} : Var28 Γ A → Var28 (snoc28 Γ B) A
 := λ x Var28 vz28 vs28 => vs28 _ _ _ (x Var28 vz28 vs28)

def Tm28 : Con28 → Ty28 → Type 1
 := λ Γ A =>
   ∀ (Tm28  : Con28 → Ty28 → Type)
     (var   : ∀ Γ A     , Var28 Γ A → Tm28 Γ A)
     (lam   : ∀ Γ A B   , Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B))
     (app   : ∀ Γ A B   , Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B)
   , Tm28 Γ A

def var28 {Γ A} : Var28 Γ A → Tm28 Γ A
 := λ x Tm28 var28 lam app =>
     var28 _ _ x

def lam28 {Γ A B} : Tm28 (snoc28 Γ A) B → Tm28 Γ (arr28 A B)
 := λ t Tm28 var28 lam28 app =>
     lam28 _ _ _ (t Tm28 var28 lam28 app)

def app28 {Γ A B} : Tm28 Γ (arr28 A B) → Tm28 Γ A → Tm28 Γ B
 := λ t u Tm28 var28 lam28 app28 =>
     app28 _ _ _
         (t Tm28 var28 lam28 app28)
         (u Tm28 var28 lam28 app28)

def v028 {Γ A} : Tm28 (snoc28 Γ A) A
 := var28 vz28

def v128 {Γ A B} : Tm28 (snoc28 (snoc28 Γ A) B) A
 := var28 (vs28 vz28)

def v228 {Γ A B C} : Tm28 (snoc28 (snoc28 (snoc28 Γ A) B) C) A
 := var28 (vs28 (vs28 vz28))

def v328 {Γ A B C D} : Tm28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) A
 := var28 (vs28 (vs28 (vs28 vz28)))

def v428 {Γ A B C D E} : Tm28 (snoc28 (snoc28 (snoc28 (snoc28 (snoc28 Γ A) B) C) D) E) A
 := var28 (vs28 (vs28 (vs28 (vs28 vz28))))

def test28 {Γ A} : Tm28 Γ (arr28 (arr28 A A) (arr28 A A))
 := lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028)))))))


def Ty29 : Type 1
 := ∀ (Ty29 : Type)
      (ι   : Ty29)
      (arr : Ty29 → Ty29 → Ty29)
    , Ty29

def ι29 : Ty29 := λ _ ι29 _ => ι29

def arr29 : Ty29 → Ty29 → Ty29
 := λ A B Ty29 ι29 arr29 =>
     arr29 (A Ty29 ι29 arr29) (B Ty29 ι29 arr29)

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
     (vz  : ∀ Γ A, Var29 (snoc29 Γ A) A)
     (vs  : ∀ Γ B A, Var29 Γ A → Var29 (snoc29 Γ B) A)
   , Var29 Γ A

def vz29 {Γ A} : Var29 (snoc29 Γ A) A
 := λ Var29 vz29 vs => vz29 _ _

def vs29 {Γ B A} : Var29 Γ A → Var29 (snoc29 Γ B) A
 := λ x Var29 vz29 vs29 => vs29 _ _ _ (x Var29 vz29 vs29)

def Tm29 : Con29 → Ty29 → Type 1
 := λ Γ A =>
   ∀ (Tm29  : Con29 → Ty29 → Type)
     (var   : ∀ Γ A     , Var29 Γ A → Tm29 Γ A)
     (lam   : ∀ Γ A B   , Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B))
     (app   : ∀ Γ A B   , Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B)
   , Tm29 Γ A

def var29 {Γ A} : Var29 Γ A → Tm29 Γ A
 := λ x Tm29 var29 lam app =>
     var29 _ _ x

def lam29 {Γ A B} : Tm29 (snoc29 Γ A) B → Tm29 Γ (arr29 A B)
 := λ t Tm29 var29 lam29 app =>
     lam29 _ _ _ (t Tm29 var29 lam29 app)

def app29 {Γ A B} : Tm29 Γ (arr29 A B) → Tm29 Γ A → Tm29 Γ B
 := λ t u Tm29 var29 lam29 app29 =>
     app29 _ _ _
         (t Tm29 var29 lam29 app29)
         (u Tm29 var29 lam29 app29)

def v029 {Γ A} : Tm29 (snoc29 Γ A) A
 := var29 vz29

def v129 {Γ A B} : Tm29 (snoc29 (snoc29 Γ A) B) A
 := var29 (vs29 vz29)

def v229 {Γ A B C} : Tm29 (snoc29 (snoc29 (snoc29 Γ A) B) C) A
 := var29 (vs29 (vs29 vz29))

def v329 {Γ A B C D} : Tm29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) A
 := var29 (vs29 (vs29 (vs29 vz29)))

def v429 {Γ A B C D E} : Tm29 (snoc29 (snoc29 (snoc29 (snoc29 (snoc29 Γ A) B) C) D) E) A
 := var29 (vs29 (vs29 (vs29 (vs29 vz29))))

def test29 {Γ A} : Tm29 Γ (arr29 (arr29 A A) (arr29 A A))
 := lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029)))))))


def Ty30 : Type 1
 := ∀ (Ty30 : Type)
      (ι   : Ty30)
      (arr : Ty30 → Ty30 → Ty30)
    , Ty30

def ι30 : Ty30 := λ _ ι30 _ => ι30

def arr30 : Ty30 → Ty30 → Ty30
 := λ A B Ty30 ι30 arr30 =>
     arr30 (A Ty30 ι30 arr30) (B Ty30 ι30 arr30)

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
     (vz  : ∀ Γ A, Var30 (snoc30 Γ A) A)
     (vs  : ∀ Γ B A, Var30 Γ A → Var30 (snoc30 Γ B) A)
   , Var30 Γ A

def vz30 {Γ A} : Var30 (snoc30 Γ A) A
 := λ Var30 vz30 vs => vz30 _ _

def vs30 {Γ B A} : Var30 Γ A → Var30 (snoc30 Γ B) A
 := λ x Var30 vz30 vs30 => vs30 _ _ _ (x Var30 vz30 vs30)

def Tm30 : Con30 → Ty30 → Type 1
 := λ Γ A =>
   ∀ (Tm30  : Con30 → Ty30 → Type)
     (var   : ∀ Γ A     , Var30 Γ A → Tm30 Γ A)
     (lam   : ∀ Γ A B   , Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B))
     (app   : ∀ Γ A B   , Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B)
   , Tm30 Γ A

def var30 {Γ A} : Var30 Γ A → Tm30 Γ A
 := λ x Tm30 var30 lam app =>
     var30 _ _ x

def lam30 {Γ A B} : Tm30 (snoc30 Γ A) B → Tm30 Γ (arr30 A B)
 := λ t Tm30 var30 lam30 app =>
     lam30 _ _ _ (t Tm30 var30 lam30 app)

def app30 {Γ A B} : Tm30 Γ (arr30 A B) → Tm30 Γ A → Tm30 Γ B
 := λ t u Tm30 var30 lam30 app30 =>
     app30 _ _ _
         (t Tm30 var30 lam30 app30)
         (u Tm30 var30 lam30 app30)

def v030 {Γ A} : Tm30 (snoc30 Γ A) A
 := var30 vz30

def v130 {Γ A B} : Tm30 (snoc30 (snoc30 Γ A) B) A
 := var30 (vs30 vz30)

def v230 {Γ A B C} : Tm30 (snoc30 (snoc30 (snoc30 Γ A) B) C) A
 := var30 (vs30 (vs30 vz30))

def v330 {Γ A B C D} : Tm30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) A
 := var30 (vs30 (vs30 (vs30 vz30)))

def v430 {Γ A B C D E} : Tm30 (snoc30 (snoc30 (snoc30 (snoc30 (snoc30 Γ A) B) C) D) E) A
 := var30 (vs30 (vs30 (vs30 (vs30 vz30))))

def test30 {Γ A} : Tm30 Γ (arr30 (arr30 A A) (arr30 A A))
 := lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030)))))))


def Ty31 : Type 1
 := ∀ (Ty31 : Type)
      (ι   : Ty31)
      (arr : Ty31 → Ty31 → Ty31)
    , Ty31

def ι31 : Ty31 := λ _ ι31 _ => ι31

def arr31 : Ty31 → Ty31 → Ty31
 := λ A B Ty31 ι31 arr31 =>
     arr31 (A Ty31 ι31 arr31) (B Ty31 ι31 arr31)

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
     (vz  : ∀ Γ A, Var31 (snoc31 Γ A) A)
     (vs  : ∀ Γ B A, Var31 Γ A → Var31 (snoc31 Γ B) A)
   , Var31 Γ A

def vz31 {Γ A} : Var31 (snoc31 Γ A) A
 := λ Var31 vz31 vs => vz31 _ _

def vs31 {Γ B A} : Var31 Γ A → Var31 (snoc31 Γ B) A
 := λ x Var31 vz31 vs31 => vs31 _ _ _ (x Var31 vz31 vs31)

def Tm31 : Con31 → Ty31 → Type 1
 := λ Γ A =>
   ∀ (Tm31  : Con31 → Ty31 → Type)
     (var   : ∀ Γ A     , Var31 Γ A → Tm31 Γ A)
     (lam   : ∀ Γ A B   , Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B))
     (app   : ∀ Γ A B   , Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B)
   , Tm31 Γ A

def var31 {Γ A} : Var31 Γ A → Tm31 Γ A
 := λ x Tm31 var31 lam app =>
     var31 _ _ x

def lam31 {Γ A B} : Tm31 (snoc31 Γ A) B → Tm31 Γ (arr31 A B)
 := λ t Tm31 var31 lam31 app =>
     lam31 _ _ _ (t Tm31 var31 lam31 app)

def app31 {Γ A B} : Tm31 Γ (arr31 A B) → Tm31 Γ A → Tm31 Γ B
 := λ t u Tm31 var31 lam31 app31 =>
     app31 _ _ _
         (t Tm31 var31 lam31 app31)
         (u Tm31 var31 lam31 app31)

def v031 {Γ A} : Tm31 (snoc31 Γ A) A
 := var31 vz31

def v131 {Γ A B} : Tm31 (snoc31 (snoc31 Γ A) B) A
 := var31 (vs31 vz31)

def v231 {Γ A B C} : Tm31 (snoc31 (snoc31 (snoc31 Γ A) B) C) A
 := var31 (vs31 (vs31 vz31))

def v331 {Γ A B C D} : Tm31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) A
 := var31 (vs31 (vs31 (vs31 vz31)))

def v431 {Γ A B C D E} : Tm31 (snoc31 (snoc31 (snoc31 (snoc31 (snoc31 Γ A) B) C) D) E) A
 := var31 (vs31 (vs31 (vs31 (vs31 vz31))))

def test31 {Γ A} : Tm31 Γ (arr31 (arr31 A A) (arr31 A A))
 := lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031)))))))


def Ty32 : Type 1
 := ∀ (Ty32 : Type)
      (ι   : Ty32)
      (arr : Ty32 → Ty32 → Ty32)
    , Ty32

def ι32 : Ty32 := λ _ ι32 _ => ι32

def arr32 : Ty32 → Ty32 → Ty32
 := λ A B Ty32 ι32 arr32 =>
     arr32 (A Ty32 ι32 arr32) (B Ty32 ι32 arr32)

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
     (vz  : ∀ Γ A, Var32 (snoc32 Γ A) A)
     (vs  : ∀ Γ B A, Var32 Γ A → Var32 (snoc32 Γ B) A)
   , Var32 Γ A

def vz32 {Γ A} : Var32 (snoc32 Γ A) A
 := λ Var32 vz32 vs => vz32 _ _

def vs32 {Γ B A} : Var32 Γ A → Var32 (snoc32 Γ B) A
 := λ x Var32 vz32 vs32 => vs32 _ _ _ (x Var32 vz32 vs32)

def Tm32 : Con32 → Ty32 → Type 1
 := λ Γ A =>
   ∀ (Tm32  : Con32 → Ty32 → Type)
     (var   : ∀ Γ A     , Var32 Γ A → Tm32 Γ A)
     (lam   : ∀ Γ A B   , Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B))
     (app   : ∀ Γ A B   , Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B)
   , Tm32 Γ A

def var32 {Γ A} : Var32 Γ A → Tm32 Γ A
 := λ x Tm32 var32 lam app =>
     var32 _ _ x

def lam32 {Γ A B} : Tm32 (snoc32 Γ A) B → Tm32 Γ (arr32 A B)
 := λ t Tm32 var32 lam32 app =>
     lam32 _ _ _ (t Tm32 var32 lam32 app)

def app32 {Γ A B} : Tm32 Γ (arr32 A B) → Tm32 Γ A → Tm32 Γ B
 := λ t u Tm32 var32 lam32 app32 =>
     app32 _ _ _
         (t Tm32 var32 lam32 app32)
         (u Tm32 var32 lam32 app32)

def v032 {Γ A} : Tm32 (snoc32 Γ A) A
 := var32 vz32

def v132 {Γ A B} : Tm32 (snoc32 (snoc32 Γ A) B) A
 := var32 (vs32 vz32)

def v232 {Γ A B C} : Tm32 (snoc32 (snoc32 (snoc32 Γ A) B) C) A
 := var32 (vs32 (vs32 vz32))

def v332 {Γ A B C D} : Tm32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) A
 := var32 (vs32 (vs32 (vs32 vz32)))

def v432 {Γ A B C D E} : Tm32 (snoc32 (snoc32 (snoc32 (snoc32 (snoc32 Γ A) B) C) D) E) A
 := var32 (vs32 (vs32 (vs32 (vs32 vz32))))

def test32 {Γ A} : Tm32 Γ (arr32 (arr32 A A) (arr32 A A))
 := lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032)))))))


def Ty33 : Type 1
 := ∀ (Ty33 : Type)
      (ι   : Ty33)
      (arr : Ty33 → Ty33 → Ty33)
    , Ty33

def ι33 : Ty33 := λ _ ι33 _ => ι33

def arr33 : Ty33 → Ty33 → Ty33
 := λ A B Ty33 ι33 arr33 =>
     arr33 (A Ty33 ι33 arr33) (B Ty33 ι33 arr33)

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
     (vz  : ∀ Γ A, Var33 (snoc33 Γ A) A)
     (vs  : ∀ Γ B A, Var33 Γ A → Var33 (snoc33 Γ B) A)
   , Var33 Γ A

def vz33 {Γ A} : Var33 (snoc33 Γ A) A
 := λ Var33 vz33 vs => vz33 _ _

def vs33 {Γ B A} : Var33 Γ A → Var33 (snoc33 Γ B) A
 := λ x Var33 vz33 vs33 => vs33 _ _ _ (x Var33 vz33 vs33)

def Tm33 : Con33 → Ty33 → Type 1
 := λ Γ A =>
   ∀ (Tm33  : Con33 → Ty33 → Type)
     (var   : ∀ Γ A     , Var33 Γ A → Tm33 Γ A)
     (lam   : ∀ Γ A B   , Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B))
     (app   : ∀ Γ A B   , Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B)
   , Tm33 Γ A

def var33 {Γ A} : Var33 Γ A → Tm33 Γ A
 := λ x Tm33 var33 lam app =>
     var33 _ _ x

def lam33 {Γ A B} : Tm33 (snoc33 Γ A) B → Tm33 Γ (arr33 A B)
 := λ t Tm33 var33 lam33 app =>
     lam33 _ _ _ (t Tm33 var33 lam33 app)

def app33 {Γ A B} : Tm33 Γ (arr33 A B) → Tm33 Γ A → Tm33 Γ B
 := λ t u Tm33 var33 lam33 app33 =>
     app33 _ _ _
         (t Tm33 var33 lam33 app33)
         (u Tm33 var33 lam33 app33)

def v033 {Γ A} : Tm33 (snoc33 Γ A) A
 := var33 vz33

def v133 {Γ A B} : Tm33 (snoc33 (snoc33 Γ A) B) A
 := var33 (vs33 vz33)

def v233 {Γ A B C} : Tm33 (snoc33 (snoc33 (snoc33 Γ A) B) C) A
 := var33 (vs33 (vs33 vz33))

def v333 {Γ A B C D} : Tm33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) A
 := var33 (vs33 (vs33 (vs33 vz33)))

def v433 {Γ A B C D E} : Tm33 (snoc33 (snoc33 (snoc33 (snoc33 (snoc33 Γ A) B) C) D) E) A
 := var33 (vs33 (vs33 (vs33 (vs33 vz33))))

def test33 {Γ A} : Tm33 Γ (arr33 (arr33 A A) (arr33 A A))
 := lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033)))))))


def Ty34 : Type 1
 := ∀ (Ty34 : Type)
      (ι   : Ty34)
      (arr : Ty34 → Ty34 → Ty34)
    , Ty34

def ι34 : Ty34 := λ _ ι34 _ => ι34

def arr34 : Ty34 → Ty34 → Ty34
 := λ A B Ty34 ι34 arr34 =>
     arr34 (A Ty34 ι34 arr34) (B Ty34 ι34 arr34)

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
     (vz  : ∀ Γ A, Var34 (snoc34 Γ A) A)
     (vs  : ∀ Γ B A, Var34 Γ A → Var34 (snoc34 Γ B) A)
   , Var34 Γ A

def vz34 {Γ A} : Var34 (snoc34 Γ A) A
 := λ Var34 vz34 vs => vz34 _ _

def vs34 {Γ B A} : Var34 Γ A → Var34 (snoc34 Γ B) A
 := λ x Var34 vz34 vs34 => vs34 _ _ _ (x Var34 vz34 vs34)

def Tm34 : Con34 → Ty34 → Type 1
 := λ Γ A =>
   ∀ (Tm34  : Con34 → Ty34 → Type)
     (var   : ∀ Γ A     , Var34 Γ A → Tm34 Γ A)
     (lam   : ∀ Γ A B   , Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B))
     (app   : ∀ Γ A B   , Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B)
   , Tm34 Γ A

def var34 {Γ A} : Var34 Γ A → Tm34 Γ A
 := λ x Tm34 var34 lam app =>
     var34 _ _ x

def lam34 {Γ A B} : Tm34 (snoc34 Γ A) B → Tm34 Γ (arr34 A B)
 := λ t Tm34 var34 lam34 app =>
     lam34 _ _ _ (t Tm34 var34 lam34 app)

def app34 {Γ A B} : Tm34 Γ (arr34 A B) → Tm34 Γ A → Tm34 Γ B
 := λ t u Tm34 var34 lam34 app34 =>
     app34 _ _ _
         (t Tm34 var34 lam34 app34)
         (u Tm34 var34 lam34 app34)

def v034 {Γ A} : Tm34 (snoc34 Γ A) A
 := var34 vz34

def v134 {Γ A B} : Tm34 (snoc34 (snoc34 Γ A) B) A
 := var34 (vs34 vz34)

def v234 {Γ A B C} : Tm34 (snoc34 (snoc34 (snoc34 Γ A) B) C) A
 := var34 (vs34 (vs34 vz34))

def v334 {Γ A B C D} : Tm34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) A
 := var34 (vs34 (vs34 (vs34 vz34)))

def v434 {Γ A B C D E} : Tm34 (snoc34 (snoc34 (snoc34 (snoc34 (snoc34 Γ A) B) C) D) E) A
 := var34 (vs34 (vs34 (vs34 (vs34 vz34))))

def test34 {Γ A} : Tm34 Γ (arr34 (arr34 A A) (arr34 A A))
 := lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034)))))))


def Ty35 : Type 1
 := ∀ (Ty35 : Type)
      (ι   : Ty35)
      (arr : Ty35 → Ty35 → Ty35)
    , Ty35

def ι35 : Ty35 := λ _ ι35 _ => ι35

def arr35 : Ty35 → Ty35 → Ty35
 := λ A B Ty35 ι35 arr35 =>
     arr35 (A Ty35 ι35 arr35) (B Ty35 ι35 arr35)

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
     (vz  : ∀ Γ A, Var35 (snoc35 Γ A) A)
     (vs  : ∀ Γ B A, Var35 Γ A → Var35 (snoc35 Γ B) A)
   , Var35 Γ A

def vz35 {Γ A} : Var35 (snoc35 Γ A) A
 := λ Var35 vz35 vs => vz35 _ _

def vs35 {Γ B A} : Var35 Γ A → Var35 (snoc35 Γ B) A
 := λ x Var35 vz35 vs35 => vs35 _ _ _ (x Var35 vz35 vs35)

def Tm35 : Con35 → Ty35 → Type 1
 := λ Γ A =>
   ∀ (Tm35  : Con35 → Ty35 → Type)
     (var   : ∀ Γ A     , Var35 Γ A → Tm35 Γ A)
     (lam   : ∀ Γ A B   , Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B))
     (app   : ∀ Γ A B   , Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B)
   , Tm35 Γ A

def var35 {Γ A} : Var35 Γ A → Tm35 Γ A
 := λ x Tm35 var35 lam app =>
     var35 _ _ x

def lam35 {Γ A B} : Tm35 (snoc35 Γ A) B → Tm35 Γ (arr35 A B)
 := λ t Tm35 var35 lam35 app =>
     lam35 _ _ _ (t Tm35 var35 lam35 app)

def app35 {Γ A B} : Tm35 Γ (arr35 A B) → Tm35 Γ A → Tm35 Γ B
 := λ t u Tm35 var35 lam35 app35 =>
     app35 _ _ _
         (t Tm35 var35 lam35 app35)
         (u Tm35 var35 lam35 app35)

def v035 {Γ A} : Tm35 (snoc35 Γ A) A
 := var35 vz35

def v135 {Γ A B} : Tm35 (snoc35 (snoc35 Γ A) B) A
 := var35 (vs35 vz35)

def v235 {Γ A B C} : Tm35 (snoc35 (snoc35 (snoc35 Γ A) B) C) A
 := var35 (vs35 (vs35 vz35))

def v335 {Γ A B C D} : Tm35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) A
 := var35 (vs35 (vs35 (vs35 vz35)))

def v435 {Γ A B C D E} : Tm35 (snoc35 (snoc35 (snoc35 (snoc35 (snoc35 Γ A) B) C) D) E) A
 := var35 (vs35 (vs35 (vs35 (vs35 vz35))))

def test35 {Γ A} : Tm35 Γ (arr35 (arr35 A A) (arr35 A A))
 := lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035)))))))


def Ty36 : Type 1
 := ∀ (Ty36 : Type)
      (ι   : Ty36)
      (arr : Ty36 → Ty36 → Ty36)
    , Ty36

def ι36 : Ty36 := λ _ ι36 _ => ι36

def arr36 : Ty36 → Ty36 → Ty36
 := λ A B Ty36 ι36 arr36 =>
     arr36 (A Ty36 ι36 arr36) (B Ty36 ι36 arr36)

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
     (vz  : ∀ Γ A, Var36 (snoc36 Γ A) A)
     (vs  : ∀ Γ B A, Var36 Γ A → Var36 (snoc36 Γ B) A)
   , Var36 Γ A

def vz36 {Γ A} : Var36 (snoc36 Γ A) A
 := λ Var36 vz36 vs => vz36 _ _

def vs36 {Γ B A} : Var36 Γ A → Var36 (snoc36 Γ B) A
 := λ x Var36 vz36 vs36 => vs36 _ _ _ (x Var36 vz36 vs36)

def Tm36 : Con36 → Ty36 → Type 1
 := λ Γ A =>
   ∀ (Tm36  : Con36 → Ty36 → Type)
     (var   : ∀ Γ A     , Var36 Γ A → Tm36 Γ A)
     (lam   : ∀ Γ A B   , Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B))
     (app   : ∀ Γ A B   , Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B)
   , Tm36 Γ A

def var36 {Γ A} : Var36 Γ A → Tm36 Γ A
 := λ x Tm36 var36 lam app =>
     var36 _ _ x

def lam36 {Γ A B} : Tm36 (snoc36 Γ A) B → Tm36 Γ (arr36 A B)
 := λ t Tm36 var36 lam36 app =>
     lam36 _ _ _ (t Tm36 var36 lam36 app)

def app36 {Γ A B} : Tm36 Γ (arr36 A B) → Tm36 Γ A → Tm36 Γ B
 := λ t u Tm36 var36 lam36 app36 =>
     app36 _ _ _
         (t Tm36 var36 lam36 app36)
         (u Tm36 var36 lam36 app36)

def v036 {Γ A} : Tm36 (snoc36 Γ A) A
 := var36 vz36

def v136 {Γ A B} : Tm36 (snoc36 (snoc36 Γ A) B) A
 := var36 (vs36 vz36)

def v236 {Γ A B C} : Tm36 (snoc36 (snoc36 (snoc36 Γ A) B) C) A
 := var36 (vs36 (vs36 vz36))

def v336 {Γ A B C D} : Tm36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) A
 := var36 (vs36 (vs36 (vs36 vz36)))

def v436 {Γ A B C D E} : Tm36 (snoc36 (snoc36 (snoc36 (snoc36 (snoc36 Γ A) B) C) D) E) A
 := var36 (vs36 (vs36 (vs36 (vs36 vz36))))

def test36 {Γ A} : Tm36 Γ (arr36 (arr36 A A) (arr36 A A))
 := lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036)))))))


def Ty37 : Type 1
 := ∀ (Ty37 : Type)
      (ι   : Ty37)
      (arr : Ty37 → Ty37 → Ty37)
    , Ty37

def ι37 : Ty37 := λ _ ι37 _ => ι37

def arr37 : Ty37 → Ty37 → Ty37
 := λ A B Ty37 ι37 arr37 =>
     arr37 (A Ty37 ι37 arr37) (B Ty37 ι37 arr37)

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
     (vz  : ∀ Γ A, Var37 (snoc37 Γ A) A)
     (vs  : ∀ Γ B A, Var37 Γ A → Var37 (snoc37 Γ B) A)
   , Var37 Γ A

def vz37 {Γ A} : Var37 (snoc37 Γ A) A
 := λ Var37 vz37 vs => vz37 _ _

def vs37 {Γ B A} : Var37 Γ A → Var37 (snoc37 Γ B) A
 := λ x Var37 vz37 vs37 => vs37 _ _ _ (x Var37 vz37 vs37)

def Tm37 : Con37 → Ty37 → Type 1
 := λ Γ A =>
   ∀ (Tm37  : Con37 → Ty37 → Type)
     (var   : ∀ Γ A     , Var37 Γ A → Tm37 Γ A)
     (lam   : ∀ Γ A B   , Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B))
     (app   : ∀ Γ A B   , Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B)
   , Tm37 Γ A

def var37 {Γ A} : Var37 Γ A → Tm37 Γ A
 := λ x Tm37 var37 lam app =>
     var37 _ _ x

def lam37 {Γ A B} : Tm37 (snoc37 Γ A) B → Tm37 Γ (arr37 A B)
 := λ t Tm37 var37 lam37 app =>
     lam37 _ _ _ (t Tm37 var37 lam37 app)

def app37 {Γ A B} : Tm37 Γ (arr37 A B) → Tm37 Γ A → Tm37 Γ B
 := λ t u Tm37 var37 lam37 app37 =>
     app37 _ _ _
         (t Tm37 var37 lam37 app37)
         (u Tm37 var37 lam37 app37)

def v037 {Γ A} : Tm37 (snoc37 Γ A) A
 := var37 vz37

def v137 {Γ A B} : Tm37 (snoc37 (snoc37 Γ A) B) A
 := var37 (vs37 vz37)

def v237 {Γ A B C} : Tm37 (snoc37 (snoc37 (snoc37 Γ A) B) C) A
 := var37 (vs37 (vs37 vz37))

def v337 {Γ A B C D} : Tm37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) A
 := var37 (vs37 (vs37 (vs37 vz37)))

def v437 {Γ A B C D E} : Tm37 (snoc37 (snoc37 (snoc37 (snoc37 (snoc37 Γ A) B) C) D) E) A
 := var37 (vs37 (vs37 (vs37 (vs37 vz37))))

def test37 {Γ A} : Tm37 Γ (arr37 (arr37 A A) (arr37 A A))
 := lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037)))))))


def Ty38 : Type 1
 := ∀ (Ty38 : Type)
      (ι   : Ty38)
      (arr : Ty38 → Ty38 → Ty38)
    , Ty38

def ι38 : Ty38 := λ _ ι38 _ => ι38

def arr38 : Ty38 → Ty38 → Ty38
 := λ A B Ty38 ι38 arr38 =>
     arr38 (A Ty38 ι38 arr38) (B Ty38 ι38 arr38)

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
     (vz  : ∀ Γ A, Var38 (snoc38 Γ A) A)
     (vs  : ∀ Γ B A, Var38 Γ A → Var38 (snoc38 Γ B) A)
   , Var38 Γ A

def vz38 {Γ A} : Var38 (snoc38 Γ A) A
 := λ Var38 vz38 vs => vz38 _ _

def vs38 {Γ B A} : Var38 Γ A → Var38 (snoc38 Γ B) A
 := λ x Var38 vz38 vs38 => vs38 _ _ _ (x Var38 vz38 vs38)

def Tm38 : Con38 → Ty38 → Type 1
 := λ Γ A =>
   ∀ (Tm38  : Con38 → Ty38 → Type)
     (var   : ∀ Γ A     , Var38 Γ A → Tm38 Γ A)
     (lam   : ∀ Γ A B   , Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B))
     (app   : ∀ Γ A B   , Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B)
   , Tm38 Γ A

def var38 {Γ A} : Var38 Γ A → Tm38 Γ A
 := λ x Tm38 var38 lam app =>
     var38 _ _ x

def lam38 {Γ A B} : Tm38 (snoc38 Γ A) B → Tm38 Γ (arr38 A B)
 := λ t Tm38 var38 lam38 app =>
     lam38 _ _ _ (t Tm38 var38 lam38 app)

def app38 {Γ A B} : Tm38 Γ (arr38 A B) → Tm38 Γ A → Tm38 Γ B
 := λ t u Tm38 var38 lam38 app38 =>
     app38 _ _ _
         (t Tm38 var38 lam38 app38)
         (u Tm38 var38 lam38 app38)

def v038 {Γ A} : Tm38 (snoc38 Γ A) A
 := var38 vz38

def v138 {Γ A B} : Tm38 (snoc38 (snoc38 Γ A) B) A
 := var38 (vs38 vz38)

def v238 {Γ A B C} : Tm38 (snoc38 (snoc38 (snoc38 Γ A) B) C) A
 := var38 (vs38 (vs38 vz38))

def v338 {Γ A B C D} : Tm38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) A
 := var38 (vs38 (vs38 (vs38 vz38)))

def v438 {Γ A B C D E} : Tm38 (snoc38 (snoc38 (snoc38 (snoc38 (snoc38 Γ A) B) C) D) E) A
 := var38 (vs38 (vs38 (vs38 (vs38 vz38))))

def test38 {Γ A} : Tm38 Γ (arr38 (arr38 A A) (arr38 A A))
 := lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038)))))))


def Ty39 : Type 1
 := ∀ (Ty39 : Type)
      (ι   : Ty39)
      (arr : Ty39 → Ty39 → Ty39)
    , Ty39

def ι39 : Ty39 := λ _ ι39 _ => ι39

def arr39 : Ty39 → Ty39 → Ty39
 := λ A B Ty39 ι39 arr39 =>
     arr39 (A Ty39 ι39 arr39) (B Ty39 ι39 arr39)

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
     (vz  : ∀ Γ A, Var39 (snoc39 Γ A) A)
     (vs  : ∀ Γ B A, Var39 Γ A → Var39 (snoc39 Γ B) A)
   , Var39 Γ A

def vz39 {Γ A} : Var39 (snoc39 Γ A) A
 := λ Var39 vz39 vs => vz39 _ _

def vs39 {Γ B A} : Var39 Γ A → Var39 (snoc39 Γ B) A
 := λ x Var39 vz39 vs39 => vs39 _ _ _ (x Var39 vz39 vs39)

def Tm39 : Con39 → Ty39 → Type 1
 := λ Γ A =>
   ∀ (Tm39  : Con39 → Ty39 → Type)
     (var   : ∀ Γ A     , Var39 Γ A → Tm39 Γ A)
     (lam   : ∀ Γ A B   , Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B))
     (app   : ∀ Γ A B   , Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B)
   , Tm39 Γ A

def var39 {Γ A} : Var39 Γ A → Tm39 Γ A
 := λ x Tm39 var39 lam app =>
     var39 _ _ x

def lam39 {Γ A B} : Tm39 (snoc39 Γ A) B → Tm39 Γ (arr39 A B)
 := λ t Tm39 var39 lam39 app =>
     lam39 _ _ _ (t Tm39 var39 lam39 app)

def app39 {Γ A B} : Tm39 Γ (arr39 A B) → Tm39 Γ A → Tm39 Γ B
 := λ t u Tm39 var39 lam39 app39 =>
     app39 _ _ _
         (t Tm39 var39 lam39 app39)
         (u Tm39 var39 lam39 app39)

def v039 {Γ A} : Tm39 (snoc39 Γ A) A
 := var39 vz39

def v139 {Γ A B} : Tm39 (snoc39 (snoc39 Γ A) B) A
 := var39 (vs39 vz39)

def v239 {Γ A B C} : Tm39 (snoc39 (snoc39 (snoc39 Γ A) B) C) A
 := var39 (vs39 (vs39 vz39))

def v339 {Γ A B C D} : Tm39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) A
 := var39 (vs39 (vs39 (vs39 vz39)))

def v439 {Γ A B C D E} : Tm39 (snoc39 (snoc39 (snoc39 (snoc39 (snoc39 Γ A) B) C) D) E) A
 := var39 (vs39 (vs39 (vs39 (vs39 vz39))))

def test39 {Γ A} : Tm39 Γ (arr39 (arr39 A A) (arr39 A A))
 := lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039)))))))


def Ty40 : Type 1
 := ∀ (Ty40 : Type)
      (ι   : Ty40)
      (arr : Ty40 → Ty40 → Ty40)
    , Ty40

def ι40 : Ty40 := λ _ ι40 _ => ι40

def arr40 : Ty40 → Ty40 → Ty40
 := λ A B Ty40 ι40 arr40 =>
     arr40 (A Ty40 ι40 arr40) (B Ty40 ι40 arr40)

def Con40 : Type 1
 := ∀ (Con40  : Type)
      (nil  : Con40)
      (snoc : Con40 → Ty40 → Con40)
    , Con40

def nil40 : Con40
 := λ Con40 nil40 snoc => nil40

def snoc40 : Con40 → Ty40 → Con40
 := λ Γ A Con40 nil40 snoc40 => snoc40 (Γ Con40 nil40 snoc40) A

def Var40 : Con40 → Ty40 → Type 1
 := λ Γ A =>
   ∀ (Var40 : Con40 → Ty40 → Type)
     (vz  : ∀ Γ A, Var40 (snoc40 Γ A) A)
     (vs  : ∀ Γ B A, Var40 Γ A → Var40 (snoc40 Γ B) A)
   , Var40 Γ A

def vz40 {Γ A} : Var40 (snoc40 Γ A) A
 := λ Var40 vz40 vs => vz40 _ _

def vs40 {Γ B A} : Var40 Γ A → Var40 (snoc40 Γ B) A
 := λ x Var40 vz40 vs40 => vs40 _ _ _ (x Var40 vz40 vs40)

def Tm40 : Con40 → Ty40 → Type 1
 := λ Γ A =>
   ∀ (Tm40  : Con40 → Ty40 → Type)
     (var   : ∀ Γ A     , Var40 Γ A → Tm40 Γ A)
     (lam   : ∀ Γ A B   , Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B))
     (app   : ∀ Γ A B   , Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B)
   , Tm40 Γ A

def var40 {Γ A} : Var40 Γ A → Tm40 Γ A
 := λ x Tm40 var40 lam app =>
     var40 _ _ x

def lam40 {Γ A B} : Tm40 (snoc40 Γ A) B → Tm40 Γ (arr40 A B)
 := λ t Tm40 var40 lam40 app =>
     lam40 _ _ _ (t Tm40 var40 lam40 app)

def app40 {Γ A B} : Tm40 Γ (arr40 A B) → Tm40 Γ A → Tm40 Γ B
 := λ t u Tm40 var40 lam40 app40 =>
     app40 _ _ _
         (t Tm40 var40 lam40 app40)
         (u Tm40 var40 lam40 app40)

def v040 {Γ A} : Tm40 (snoc40 Γ A) A
 := var40 vz40

def v140 {Γ A B} : Tm40 (snoc40 (snoc40 Γ A) B) A
 := var40 (vs40 vz40)

def v240 {Γ A B C} : Tm40 (snoc40 (snoc40 (snoc40 Γ A) B) C) A
 := var40 (vs40 (vs40 vz40))

def v340 {Γ A B C D} : Tm40 (snoc40 (snoc40 (snoc40 (snoc40 Γ A) B) C) D) A
 := var40 (vs40 (vs40 (vs40 vz40)))

def v440 {Γ A B C D E} : Tm40 (snoc40 (snoc40 (snoc40 (snoc40 (snoc40 Γ A) B) C) D) E) A
 := var40 (vs40 (vs40 (vs40 (vs40 vz40))))

def test40 {Γ A} : Tm40 Γ (arr40 (arr40 A A) (arr40 A A))
 := lam40 (lam40 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 v040)))))))


def Ty41 : Type 1
 := ∀ (Ty41 : Type)
      (ι   : Ty41)
      (arr : Ty41 → Ty41 → Ty41)
    , Ty41

def ι41 : Ty41 := λ _ ι41 _ => ι41

def arr41 : Ty41 → Ty41 → Ty41
 := λ A B Ty41 ι41 arr41 =>
     arr41 (A Ty41 ι41 arr41) (B Ty41 ι41 arr41)

def Con41 : Type 1
 := ∀ (Con41  : Type)
      (nil  : Con41)
      (snoc : Con41 → Ty41 → Con41)
    , Con41

def nil41 : Con41
 := λ Con41 nil41 snoc => nil41

def snoc41 : Con41 → Ty41 → Con41
 := λ Γ A Con41 nil41 snoc41 => snoc41 (Γ Con41 nil41 snoc41) A

def Var41 : Con41 → Ty41 → Type 1
 := λ Γ A =>
   ∀ (Var41 : Con41 → Ty41 → Type)
     (vz  : ∀ Γ A, Var41 (snoc41 Γ A) A)
     (vs  : ∀ Γ B A, Var41 Γ A → Var41 (snoc41 Γ B) A)
   , Var41 Γ A

def vz41 {Γ A} : Var41 (snoc41 Γ A) A
 := λ Var41 vz41 vs => vz41 _ _

def vs41 {Γ B A} : Var41 Γ A → Var41 (snoc41 Γ B) A
 := λ x Var41 vz41 vs41 => vs41 _ _ _ (x Var41 vz41 vs41)

def Tm41 : Con41 → Ty41 → Type 1
 := λ Γ A =>
   ∀ (Tm41  : Con41 → Ty41 → Type)
     (var   : ∀ Γ A     , Var41 Γ A → Tm41 Γ A)
     (lam   : ∀ Γ A B   , Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B))
     (app   : ∀ Γ A B   , Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B)
   , Tm41 Γ A

def var41 {Γ A} : Var41 Γ A → Tm41 Γ A
 := λ x Tm41 var41 lam app =>
     var41 _ _ x

def lam41 {Γ A B} : Tm41 (snoc41 Γ A) B → Tm41 Γ (arr41 A B)
 := λ t Tm41 var41 lam41 app =>
     lam41 _ _ _ (t Tm41 var41 lam41 app)

def app41 {Γ A B} : Tm41 Γ (arr41 A B) → Tm41 Γ A → Tm41 Γ B
 := λ t u Tm41 var41 lam41 app41 =>
     app41 _ _ _
         (t Tm41 var41 lam41 app41)
         (u Tm41 var41 lam41 app41)

def v041 {Γ A} : Tm41 (snoc41 Γ A) A
 := var41 vz41

def v141 {Γ A B} : Tm41 (snoc41 (snoc41 Γ A) B) A
 := var41 (vs41 vz41)

def v241 {Γ A B C} : Tm41 (snoc41 (snoc41 (snoc41 Γ A) B) C) A
 := var41 (vs41 (vs41 vz41))

def v341 {Γ A B C D} : Tm41 (snoc41 (snoc41 (snoc41 (snoc41 Γ A) B) C) D) A
 := var41 (vs41 (vs41 (vs41 vz41)))

def v441 {Γ A B C D E} : Tm41 (snoc41 (snoc41 (snoc41 (snoc41 (snoc41 Γ A) B) C) D) E) A
 := var41 (vs41 (vs41 (vs41 (vs41 vz41))))

def test41 {Γ A} : Tm41 Γ (arr41 (arr41 A A) (arr41 A A))
 := lam41 (lam41 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 v041)))))))


def Ty42 : Type 1
 := ∀ (Ty42 : Type)
      (ι   : Ty42)
      (arr : Ty42 → Ty42 → Ty42)
    , Ty42

def ι42 : Ty42 := λ _ ι42 _ => ι42

def arr42 : Ty42 → Ty42 → Ty42
 := λ A B Ty42 ι42 arr42 =>
     arr42 (A Ty42 ι42 arr42) (B Ty42 ι42 arr42)

def Con42 : Type 1
 := ∀ (Con42  : Type)
      (nil  : Con42)
      (snoc : Con42 → Ty42 → Con42)
    , Con42

def nil42 : Con42
 := λ Con42 nil42 snoc => nil42

def snoc42 : Con42 → Ty42 → Con42
 := λ Γ A Con42 nil42 snoc42 => snoc42 (Γ Con42 nil42 snoc42) A

def Var42 : Con42 → Ty42 → Type 1
 := λ Γ A =>
   ∀ (Var42 : Con42 → Ty42 → Type)
     (vz  : ∀ Γ A, Var42 (snoc42 Γ A) A)
     (vs  : ∀ Γ B A, Var42 Γ A → Var42 (snoc42 Γ B) A)
   , Var42 Γ A

def vz42 {Γ A} : Var42 (snoc42 Γ A) A
 := λ Var42 vz42 vs => vz42 _ _

def vs42 {Γ B A} : Var42 Γ A → Var42 (snoc42 Γ B) A
 := λ x Var42 vz42 vs42 => vs42 _ _ _ (x Var42 vz42 vs42)

def Tm42 : Con42 → Ty42 → Type 1
 := λ Γ A =>
   ∀ (Tm42  : Con42 → Ty42 → Type)
     (var   : ∀ Γ A     , Var42 Γ A → Tm42 Γ A)
     (lam   : ∀ Γ A B   , Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B))
     (app   : ∀ Γ A B   , Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B)
   , Tm42 Γ A

def var42 {Γ A} : Var42 Γ A → Tm42 Γ A
 := λ x Tm42 var42 lam app =>
     var42 _ _ x

def lam42 {Γ A B} : Tm42 (snoc42 Γ A) B → Tm42 Γ (arr42 A B)
 := λ t Tm42 var42 lam42 app =>
     lam42 _ _ _ (t Tm42 var42 lam42 app)

def app42 {Γ A B} : Tm42 Γ (arr42 A B) → Tm42 Γ A → Tm42 Γ B
 := λ t u Tm42 var42 lam42 app42 =>
     app42 _ _ _
         (t Tm42 var42 lam42 app42)
         (u Tm42 var42 lam42 app42)

def v042 {Γ A} : Tm42 (snoc42 Γ A) A
 := var42 vz42

def v142 {Γ A B} : Tm42 (snoc42 (snoc42 Γ A) B) A
 := var42 (vs42 vz42)

def v242 {Γ A B C} : Tm42 (snoc42 (snoc42 (snoc42 Γ A) B) C) A
 := var42 (vs42 (vs42 vz42))

def v342 {Γ A B C D} : Tm42 (snoc42 (snoc42 (snoc42 (snoc42 Γ A) B) C) D) A
 := var42 (vs42 (vs42 (vs42 vz42)))

def v442 {Γ A B C D E} : Tm42 (snoc42 (snoc42 (snoc42 (snoc42 (snoc42 Γ A) B) C) D) E) A
 := var42 (vs42 (vs42 (vs42 (vs42 vz42))))

def test42 {Γ A} : Tm42 Γ (arr42 (arr42 A A) (arr42 A A))
 := lam42 (lam42 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 v042)))))))


def Ty43 : Type 1
 := ∀ (Ty43 : Type)
      (ι   : Ty43)
      (arr : Ty43 → Ty43 → Ty43)
    , Ty43

def ι43 : Ty43 := λ _ ι43 _ => ι43

def arr43 : Ty43 → Ty43 → Ty43
 := λ A B Ty43 ι43 arr43 =>
     arr43 (A Ty43 ι43 arr43) (B Ty43 ι43 arr43)

def Con43 : Type 1
 := ∀ (Con43  : Type)
      (nil  : Con43)
      (snoc : Con43 → Ty43 → Con43)
    , Con43

def nil43 : Con43
 := λ Con43 nil43 snoc => nil43

def snoc43 : Con43 → Ty43 → Con43
 := λ Γ A Con43 nil43 snoc43 => snoc43 (Γ Con43 nil43 snoc43) A

def Var43 : Con43 → Ty43 → Type 1
 := λ Γ A =>
   ∀ (Var43 : Con43 → Ty43 → Type)
     (vz  : ∀ Γ A, Var43 (snoc43 Γ A) A)
     (vs  : ∀ Γ B A, Var43 Γ A → Var43 (snoc43 Γ B) A)
   , Var43 Γ A

def vz43 {Γ A} : Var43 (snoc43 Γ A) A
 := λ Var43 vz43 vs => vz43 _ _

def vs43 {Γ B A} : Var43 Γ A → Var43 (snoc43 Γ B) A
 := λ x Var43 vz43 vs43 => vs43 _ _ _ (x Var43 vz43 vs43)

def Tm43 : Con43 → Ty43 → Type 1
 := λ Γ A =>
   ∀ (Tm43  : Con43 → Ty43 → Type)
     (var   : ∀ Γ A     , Var43 Γ A → Tm43 Γ A)
     (lam   : ∀ Γ A B   , Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B))
     (app   : ∀ Γ A B   , Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B)
   , Tm43 Γ A

def var43 {Γ A} : Var43 Γ A → Tm43 Γ A
 := λ x Tm43 var43 lam app =>
     var43 _ _ x

def lam43 {Γ A B} : Tm43 (snoc43 Γ A) B → Tm43 Γ (arr43 A B)
 := λ t Tm43 var43 lam43 app =>
     lam43 _ _ _ (t Tm43 var43 lam43 app)

def app43 {Γ A B} : Tm43 Γ (arr43 A B) → Tm43 Γ A → Tm43 Γ B
 := λ t u Tm43 var43 lam43 app43 =>
     app43 _ _ _
         (t Tm43 var43 lam43 app43)
         (u Tm43 var43 lam43 app43)

def v043 {Γ A} : Tm43 (snoc43 Γ A) A
 := var43 vz43

def v143 {Γ A B} : Tm43 (snoc43 (snoc43 Γ A) B) A
 := var43 (vs43 vz43)

def v243 {Γ A B C} : Tm43 (snoc43 (snoc43 (snoc43 Γ A) B) C) A
 := var43 (vs43 (vs43 vz43))

def v343 {Γ A B C D} : Tm43 (snoc43 (snoc43 (snoc43 (snoc43 Γ A) B) C) D) A
 := var43 (vs43 (vs43 (vs43 vz43)))

def v443 {Γ A B C D E} : Tm43 (snoc43 (snoc43 (snoc43 (snoc43 (snoc43 Γ A) B) C) D) E) A
 := var43 (vs43 (vs43 (vs43 (vs43 vz43))))

def test43 {Γ A} : Tm43 Γ (arr43 (arr43 A A) (arr43 A A))
 := lam43 (lam43 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 v043)))))))


def Ty44 : Type 1
 := ∀ (Ty44 : Type)
      (ι   : Ty44)
      (arr : Ty44 → Ty44 → Ty44)
    , Ty44

def ι44 : Ty44 := λ _ ι44 _ => ι44

def arr44 : Ty44 → Ty44 → Ty44
 := λ A B Ty44 ι44 arr44 =>
     arr44 (A Ty44 ι44 arr44) (B Ty44 ι44 arr44)

def Con44 : Type 1
 := ∀ (Con44  : Type)
      (nil  : Con44)
      (snoc : Con44 → Ty44 → Con44)
    , Con44

def nil44 : Con44
 := λ Con44 nil44 snoc => nil44

def snoc44 : Con44 → Ty44 → Con44
 := λ Γ A Con44 nil44 snoc44 => snoc44 (Γ Con44 nil44 snoc44) A

def Var44 : Con44 → Ty44 → Type 1
 := λ Γ A =>
   ∀ (Var44 : Con44 → Ty44 → Type)
     (vz  : ∀ Γ A, Var44 (snoc44 Γ A) A)
     (vs  : ∀ Γ B A, Var44 Γ A → Var44 (snoc44 Γ B) A)
   , Var44 Γ A

def vz44 {Γ A} : Var44 (snoc44 Γ A) A
 := λ Var44 vz44 vs => vz44 _ _

def vs44 {Γ B A} : Var44 Γ A → Var44 (snoc44 Γ B) A
 := λ x Var44 vz44 vs44 => vs44 _ _ _ (x Var44 vz44 vs44)

def Tm44 : Con44 → Ty44 → Type 1
 := λ Γ A =>
   ∀ (Tm44  : Con44 → Ty44 → Type)
     (var   : ∀ Γ A     , Var44 Γ A → Tm44 Γ A)
     (lam   : ∀ Γ A B   , Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B))
     (app   : ∀ Γ A B   , Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B)
   , Tm44 Γ A

def var44 {Γ A} : Var44 Γ A → Tm44 Γ A
 := λ x Tm44 var44 lam app =>
     var44 _ _ x

def lam44 {Γ A B} : Tm44 (snoc44 Γ A) B → Tm44 Γ (arr44 A B)
 := λ t Tm44 var44 lam44 app =>
     lam44 _ _ _ (t Tm44 var44 lam44 app)

def app44 {Γ A B} : Tm44 Γ (arr44 A B) → Tm44 Γ A → Tm44 Γ B
 := λ t u Tm44 var44 lam44 app44 =>
     app44 _ _ _
         (t Tm44 var44 lam44 app44)
         (u Tm44 var44 lam44 app44)

def v044 {Γ A} : Tm44 (snoc44 Γ A) A
 := var44 vz44

def v144 {Γ A B} : Tm44 (snoc44 (snoc44 Γ A) B) A
 := var44 (vs44 vz44)

def v244 {Γ A B C} : Tm44 (snoc44 (snoc44 (snoc44 Γ A) B) C) A
 := var44 (vs44 (vs44 vz44))

def v344 {Γ A B C D} : Tm44 (snoc44 (snoc44 (snoc44 (snoc44 Γ A) B) C) D) A
 := var44 (vs44 (vs44 (vs44 vz44)))

def v444 {Γ A B C D E} : Tm44 (snoc44 (snoc44 (snoc44 (snoc44 (snoc44 Γ A) B) C) D) E) A
 := var44 (vs44 (vs44 (vs44 (vs44 vz44))))

def test44 {Γ A} : Tm44 Γ (arr44 (arr44 A A) (arr44 A A))
 := lam44 (lam44 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 v044)))))))


def Ty45 : Type 1
 := ∀ (Ty45 : Type)
      (ι   : Ty45)
      (arr : Ty45 → Ty45 → Ty45)
    , Ty45

def ι45 : Ty45 := λ _ ι45 _ => ι45

def arr45 : Ty45 → Ty45 → Ty45
 := λ A B Ty45 ι45 arr45 =>
     arr45 (A Ty45 ι45 arr45) (B Ty45 ι45 arr45)

def Con45 : Type 1
 := ∀ (Con45  : Type)
      (nil  : Con45)
      (snoc : Con45 → Ty45 → Con45)
    , Con45

def nil45 : Con45
 := λ Con45 nil45 snoc => nil45

def snoc45 : Con45 → Ty45 → Con45
 := λ Γ A Con45 nil45 snoc45 => snoc45 (Γ Con45 nil45 snoc45) A

def Var45 : Con45 → Ty45 → Type 1
 := λ Γ A =>
   ∀ (Var45 : Con45 → Ty45 → Type)
     (vz  : ∀ Γ A, Var45 (snoc45 Γ A) A)
     (vs  : ∀ Γ B A, Var45 Γ A → Var45 (snoc45 Γ B) A)
   , Var45 Γ A

def vz45 {Γ A} : Var45 (snoc45 Γ A) A
 := λ Var45 vz45 vs => vz45 _ _

def vs45 {Γ B A} : Var45 Γ A → Var45 (snoc45 Γ B) A
 := λ x Var45 vz45 vs45 => vs45 _ _ _ (x Var45 vz45 vs45)

def Tm45 : Con45 → Ty45 → Type 1
 := λ Γ A =>
   ∀ (Tm45  : Con45 → Ty45 → Type)
     (var   : ∀ Γ A     , Var45 Γ A → Tm45 Γ A)
     (lam   : ∀ Γ A B   , Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B))
     (app   : ∀ Γ A B   , Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B)
   , Tm45 Γ A

def var45 {Γ A} : Var45 Γ A → Tm45 Γ A
 := λ x Tm45 var45 lam app =>
     var45 _ _ x

def lam45 {Γ A B} : Tm45 (snoc45 Γ A) B → Tm45 Γ (arr45 A B)
 := λ t Tm45 var45 lam45 app =>
     lam45 _ _ _ (t Tm45 var45 lam45 app)

def app45 {Γ A B} : Tm45 Γ (arr45 A B) → Tm45 Γ A → Tm45 Γ B
 := λ t u Tm45 var45 lam45 app45 =>
     app45 _ _ _
         (t Tm45 var45 lam45 app45)
         (u Tm45 var45 lam45 app45)

def v045 {Γ A} : Tm45 (snoc45 Γ A) A
 := var45 vz45

def v145 {Γ A B} : Tm45 (snoc45 (snoc45 Γ A) B) A
 := var45 (vs45 vz45)

def v245 {Γ A B C} : Tm45 (snoc45 (snoc45 (snoc45 Γ A) B) C) A
 := var45 (vs45 (vs45 vz45))

def v345 {Γ A B C D} : Tm45 (snoc45 (snoc45 (snoc45 (snoc45 Γ A) B) C) D) A
 := var45 (vs45 (vs45 (vs45 vz45)))

def v445 {Γ A B C D E} : Tm45 (snoc45 (snoc45 (snoc45 (snoc45 (snoc45 Γ A) B) C) D) E) A
 := var45 (vs45 (vs45 (vs45 (vs45 vz45))))

def test45 {Γ A} : Tm45 Γ (arr45 (arr45 A A) (arr45 A A))
 := lam45 (lam45 (app45 v145 (app45 v145 (app45 v145 (app45 v145 (app45 v145 (app45 v145 v045)))))))


def Ty46 : Type 1
 := ∀ (Ty46 : Type)
      (ι   : Ty46)
      (arr : Ty46 → Ty46 → Ty46)
    , Ty46

def ι46 : Ty46 := λ _ ι46 _ => ι46

def arr46 : Ty46 → Ty46 → Ty46
 := λ A B Ty46 ι46 arr46 =>
     arr46 (A Ty46 ι46 arr46) (B Ty46 ι46 arr46)

def Con46 : Type 1
 := ∀ (Con46  : Type)
      (nil  : Con46)
      (snoc : Con46 → Ty46 → Con46)
    , Con46

def nil46 : Con46
 := λ Con46 nil46 snoc => nil46

def snoc46 : Con46 → Ty46 → Con46
 := λ Γ A Con46 nil46 snoc46 => snoc46 (Γ Con46 nil46 snoc46) A

def Var46 : Con46 → Ty46 → Type 1
 := λ Γ A =>
   ∀ (Var46 : Con46 → Ty46 → Type)
     (vz  : ∀ Γ A, Var46 (snoc46 Γ A) A)
     (vs  : ∀ Γ B A, Var46 Γ A → Var46 (snoc46 Γ B) A)
   , Var46 Γ A

def vz46 {Γ A} : Var46 (snoc46 Γ A) A
 := λ Var46 vz46 vs => vz46 _ _

def vs46 {Γ B A} : Var46 Γ A → Var46 (snoc46 Γ B) A
 := λ x Var46 vz46 vs46 => vs46 _ _ _ (x Var46 vz46 vs46)

def Tm46 : Con46 → Ty46 → Type 1
 := λ Γ A =>
   ∀ (Tm46  : Con46 → Ty46 → Type)
     (var   : ∀ Γ A     , Var46 Γ A → Tm46 Γ A)
     (lam   : ∀ Γ A B   , Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B))
     (app   : ∀ Γ A B   , Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B)
   , Tm46 Γ A

def var46 {Γ A} : Var46 Γ A → Tm46 Γ A
 := λ x Tm46 var46 lam app =>
     var46 _ _ x

def lam46 {Γ A B} : Tm46 (snoc46 Γ A) B → Tm46 Γ (arr46 A B)
 := λ t Tm46 var46 lam46 app =>
     lam46 _ _ _ (t Tm46 var46 lam46 app)

def app46 {Γ A B} : Tm46 Γ (arr46 A B) → Tm46 Γ A → Tm46 Γ B
 := λ t u Tm46 var46 lam46 app46 =>
     app46 _ _ _
         (t Tm46 var46 lam46 app46)
         (u Tm46 var46 lam46 app46)

def v046 {Γ A} : Tm46 (snoc46 Γ A) A
 := var46 vz46

def v146 {Γ A B} : Tm46 (snoc46 (snoc46 Γ A) B) A
 := var46 (vs46 vz46)

def v246 {Γ A B C} : Tm46 (snoc46 (snoc46 (snoc46 Γ A) B) C) A
 := var46 (vs46 (vs46 vz46))

def v346 {Γ A B C D} : Tm46 (snoc46 (snoc46 (snoc46 (snoc46 Γ A) B) C) D) A
 := var46 (vs46 (vs46 (vs46 vz46)))

def v446 {Γ A B C D E} : Tm46 (snoc46 (snoc46 (snoc46 (snoc46 (snoc46 Γ A) B) C) D) E) A
 := var46 (vs46 (vs46 (vs46 (vs46 vz46))))

def test46 {Γ A} : Tm46 Γ (arr46 (arr46 A A) (arr46 A A))
 := lam46 (lam46 (app46 v146 (app46 v146 (app46 v146 (app46 v146 (app46 v146 (app46 v146 v046)))))))


def Ty47 : Type 1
 := ∀ (Ty47 : Type)
      (ι   : Ty47)
      (arr : Ty47 → Ty47 → Ty47)
    , Ty47

def ι47 : Ty47 := λ _ ι47 _ => ι47

def arr47 : Ty47 → Ty47 → Ty47
 := λ A B Ty47 ι47 arr47 =>
     arr47 (A Ty47 ι47 arr47) (B Ty47 ι47 arr47)

def Con47 : Type 1
 := ∀ (Con47  : Type)
      (nil  : Con47)
      (snoc : Con47 → Ty47 → Con47)
    , Con47

def nil47 : Con47
 := λ Con47 nil47 snoc => nil47

def snoc47 : Con47 → Ty47 → Con47
 := λ Γ A Con47 nil47 snoc47 => snoc47 (Γ Con47 nil47 snoc47) A

def Var47 : Con47 → Ty47 → Type 1
 := λ Γ A =>
   ∀ (Var47 : Con47 → Ty47 → Type)
     (vz  : ∀ Γ A, Var47 (snoc47 Γ A) A)
     (vs  : ∀ Γ B A, Var47 Γ A → Var47 (snoc47 Γ B) A)
   , Var47 Γ A

def vz47 {Γ A} : Var47 (snoc47 Γ A) A
 := λ Var47 vz47 vs => vz47 _ _

def vs47 {Γ B A} : Var47 Γ A → Var47 (snoc47 Γ B) A
 := λ x Var47 vz47 vs47 => vs47 _ _ _ (x Var47 vz47 vs47)

def Tm47 : Con47 → Ty47 → Type 1
 := λ Γ A =>
   ∀ (Tm47  : Con47 → Ty47 → Type)
     (var   : ∀ Γ A     , Var47 Γ A → Tm47 Γ A)
     (lam   : ∀ Γ A B   , Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B))
     (app   : ∀ Γ A B   , Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B)
   , Tm47 Γ A

def var47 {Γ A} : Var47 Γ A → Tm47 Γ A
 := λ x Tm47 var47 lam app =>
     var47 _ _ x

def lam47 {Γ A B} : Tm47 (snoc47 Γ A) B → Tm47 Γ (arr47 A B)
 := λ t Tm47 var47 lam47 app =>
     lam47 _ _ _ (t Tm47 var47 lam47 app)

def app47 {Γ A B} : Tm47 Γ (arr47 A B) → Tm47 Γ A → Tm47 Γ B
 := λ t u Tm47 var47 lam47 app47 =>
     app47 _ _ _
         (t Tm47 var47 lam47 app47)
         (u Tm47 var47 lam47 app47)

def v047 {Γ A} : Tm47 (snoc47 Γ A) A
 := var47 vz47

def v147 {Γ A B} : Tm47 (snoc47 (snoc47 Γ A) B) A
 := var47 (vs47 vz47)

def v247 {Γ A B C} : Tm47 (snoc47 (snoc47 (snoc47 Γ A) B) C) A
 := var47 (vs47 (vs47 vz47))

def v347 {Γ A B C D} : Tm47 (snoc47 (snoc47 (snoc47 (snoc47 Γ A) B) C) D) A
 := var47 (vs47 (vs47 (vs47 vz47)))

def v447 {Γ A B C D E} : Tm47 (snoc47 (snoc47 (snoc47 (snoc47 (snoc47 Γ A) B) C) D) E) A
 := var47 (vs47 (vs47 (vs47 (vs47 vz47))))

def test47 {Γ A} : Tm47 Γ (arr47 (arr47 A A) (arr47 A A))
 := lam47 (lam47 (app47 v147 (app47 v147 (app47 v147 (app47 v147 (app47 v147 (app47 v147 v047)))))))


def Ty48 : Type 1
 := ∀ (Ty48 : Type)
      (ι   : Ty48)
      (arr : Ty48 → Ty48 → Ty48)
    , Ty48

def ι48 : Ty48 := λ _ ι48 _ => ι48

def arr48 : Ty48 → Ty48 → Ty48
 := λ A B Ty48 ι48 arr48 =>
     arr48 (A Ty48 ι48 arr48) (B Ty48 ι48 arr48)

def Con48 : Type 1
 := ∀ (Con48  : Type)
      (nil  : Con48)
      (snoc : Con48 → Ty48 → Con48)
    , Con48

def nil48 : Con48
 := λ Con48 nil48 snoc => nil48

def snoc48 : Con48 → Ty48 → Con48
 := λ Γ A Con48 nil48 snoc48 => snoc48 (Γ Con48 nil48 snoc48) A

def Var48 : Con48 → Ty48 → Type 1
 := λ Γ A =>
   ∀ (Var48 : Con48 → Ty48 → Type)
     (vz  : ∀ Γ A, Var48 (snoc48 Γ A) A)
     (vs  : ∀ Γ B A, Var48 Γ A → Var48 (snoc48 Γ B) A)
   , Var48 Γ A

def vz48 {Γ A} : Var48 (snoc48 Γ A) A
 := λ Var48 vz48 vs => vz48 _ _

def vs48 {Γ B A} : Var48 Γ A → Var48 (snoc48 Γ B) A
 := λ x Var48 vz48 vs48 => vs48 _ _ _ (x Var48 vz48 vs48)

def Tm48 : Con48 → Ty48 → Type 1
 := λ Γ A =>
   ∀ (Tm48  : Con48 → Ty48 → Type)
     (var   : ∀ Γ A     , Var48 Γ A → Tm48 Γ A)
     (lam   : ∀ Γ A B   , Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B))
     (app   : ∀ Γ A B   , Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B)
   , Tm48 Γ A

def var48 {Γ A} : Var48 Γ A → Tm48 Γ A
 := λ x Tm48 var48 lam app =>
     var48 _ _ x

def lam48 {Γ A B} : Tm48 (snoc48 Γ A) B → Tm48 Γ (arr48 A B)
 := λ t Tm48 var48 lam48 app =>
     lam48 _ _ _ (t Tm48 var48 lam48 app)

def app48 {Γ A B} : Tm48 Γ (arr48 A B) → Tm48 Γ A → Tm48 Γ B
 := λ t u Tm48 var48 lam48 app48 =>
     app48 _ _ _
         (t Tm48 var48 lam48 app48)
         (u Tm48 var48 lam48 app48)

def v048 {Γ A} : Tm48 (snoc48 Γ A) A
 := var48 vz48

def v148 {Γ A B} : Tm48 (snoc48 (snoc48 Γ A) B) A
 := var48 (vs48 vz48)

def v248 {Γ A B C} : Tm48 (snoc48 (snoc48 (snoc48 Γ A) B) C) A
 := var48 (vs48 (vs48 vz48))

def v348 {Γ A B C D} : Tm48 (snoc48 (snoc48 (snoc48 (snoc48 Γ A) B) C) D) A
 := var48 (vs48 (vs48 (vs48 vz48)))

def v448 {Γ A B C D E} : Tm48 (snoc48 (snoc48 (snoc48 (snoc48 (snoc48 Γ A) B) C) D) E) A
 := var48 (vs48 (vs48 (vs48 (vs48 vz48))))

def test48 {Γ A} : Tm48 Γ (arr48 (arr48 A A) (arr48 A A))
 := lam48 (lam48 (app48 v148 (app48 v148 (app48 v148 (app48 v148 (app48 v148 (app48 v148 v048)))))))


def Ty49 : Type 1
 := ∀ (Ty49 : Type)
      (ι   : Ty49)
      (arr : Ty49 → Ty49 → Ty49)
    , Ty49

def ι49 : Ty49 := λ _ ι49 _ => ι49

def arr49 : Ty49 → Ty49 → Ty49
 := λ A B Ty49 ι49 arr49 =>
     arr49 (A Ty49 ι49 arr49) (B Ty49 ι49 arr49)

def Con49 : Type 1
 := ∀ (Con49  : Type)
      (nil  : Con49)
      (snoc : Con49 → Ty49 → Con49)
    , Con49

def nil49 : Con49
 := λ Con49 nil49 snoc => nil49

def snoc49 : Con49 → Ty49 → Con49
 := λ Γ A Con49 nil49 snoc49 => snoc49 (Γ Con49 nil49 snoc49) A

def Var49 : Con49 → Ty49 → Type 1
 := λ Γ A =>
   ∀ (Var49 : Con49 → Ty49 → Type)
     (vz  : ∀ Γ A, Var49 (snoc49 Γ A) A)
     (vs  : ∀ Γ B A, Var49 Γ A → Var49 (snoc49 Γ B) A)
   , Var49 Γ A

def vz49 {Γ A} : Var49 (snoc49 Γ A) A
 := λ Var49 vz49 vs => vz49 _ _

def vs49 {Γ B A} : Var49 Γ A → Var49 (snoc49 Γ B) A
 := λ x Var49 vz49 vs49 => vs49 _ _ _ (x Var49 vz49 vs49)

def Tm49 : Con49 → Ty49 → Type 1
 := λ Γ A =>
   ∀ (Tm49  : Con49 → Ty49 → Type)
     (var   : ∀ Γ A     , Var49 Γ A → Tm49 Γ A)
     (lam   : ∀ Γ A B   , Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B))
     (app   : ∀ Γ A B   , Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B)
   , Tm49 Γ A

def var49 {Γ A} : Var49 Γ A → Tm49 Γ A
 := λ x Tm49 var49 lam app =>
     var49 _ _ x

def lam49 {Γ A B} : Tm49 (snoc49 Γ A) B → Tm49 Γ (arr49 A B)
 := λ t Tm49 var49 lam49 app =>
     lam49 _ _ _ (t Tm49 var49 lam49 app)

def app49 {Γ A B} : Tm49 Γ (arr49 A B) → Tm49 Γ A → Tm49 Γ B
 := λ t u Tm49 var49 lam49 app49 =>
     app49 _ _ _
         (t Tm49 var49 lam49 app49)
         (u Tm49 var49 lam49 app49)

def v049 {Γ A} : Tm49 (snoc49 Γ A) A
 := var49 vz49

def v149 {Γ A B} : Tm49 (snoc49 (snoc49 Γ A) B) A
 := var49 (vs49 vz49)

def v249 {Γ A B C} : Tm49 (snoc49 (snoc49 (snoc49 Γ A) B) C) A
 := var49 (vs49 (vs49 vz49))

def v349 {Γ A B C D} : Tm49 (snoc49 (snoc49 (snoc49 (snoc49 Γ A) B) C) D) A
 := var49 (vs49 (vs49 (vs49 vz49)))

def v449 {Γ A B C D E} : Tm49 (snoc49 (snoc49 (snoc49 (snoc49 (snoc49 Γ A) B) C) D) E) A
 := var49 (vs49 (vs49 (vs49 (vs49 vz49))))

def test49 {Γ A} : Tm49 Γ (arr49 (arr49 A A) (arr49 A A))
 := lam49 (lam49 (app49 v149 (app49 v149 (app49 v149 (app49 v149 (app49 v149 (app49 v149 v049)))))))


def Ty50 : Type 1
 := ∀ (Ty50 : Type)
      (ι   : Ty50)
      (arr : Ty50 → Ty50 → Ty50)
    , Ty50

def ι50 : Ty50 := λ _ ι50 _ => ι50

def arr50 : Ty50 → Ty50 → Ty50
 := λ A B Ty50 ι50 arr50 =>
     arr50 (A Ty50 ι50 arr50) (B Ty50 ι50 arr50)

def Con50 : Type 1
 := ∀ (Con50  : Type)
      (nil  : Con50)
      (snoc : Con50 → Ty50 → Con50)
    , Con50

def nil50 : Con50
 := λ Con50 nil50 snoc => nil50

def snoc50 : Con50 → Ty50 → Con50
 := λ Γ A Con50 nil50 snoc50 => snoc50 (Γ Con50 nil50 snoc50) A

def Var50 : Con50 → Ty50 → Type 1
 := λ Γ A =>
   ∀ (Var50 : Con50 → Ty50 → Type)
     (vz  : ∀ Γ A, Var50 (snoc50 Γ A) A)
     (vs  : ∀ Γ B A, Var50 Γ A → Var50 (snoc50 Γ B) A)
   , Var50 Γ A

def vz50 {Γ A} : Var50 (snoc50 Γ A) A
 := λ Var50 vz50 vs => vz50 _ _

def vs50 {Γ B A} : Var50 Γ A → Var50 (snoc50 Γ B) A
 := λ x Var50 vz50 vs50 => vs50 _ _ _ (x Var50 vz50 vs50)

def Tm50 : Con50 → Ty50 → Type 1
 := λ Γ A =>
   ∀ (Tm50  : Con50 → Ty50 → Type)
     (var   : ∀ Γ A     , Var50 Γ A → Tm50 Γ A)
     (lam   : ∀ Γ A B   , Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B))
     (app   : ∀ Γ A B   , Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B)
   , Tm50 Γ A

def var50 {Γ A} : Var50 Γ A → Tm50 Γ A
 := λ x Tm50 var50 lam app =>
     var50 _ _ x

def lam50 {Γ A B} : Tm50 (snoc50 Γ A) B → Tm50 Γ (arr50 A B)
 := λ t Tm50 var50 lam50 app =>
     lam50 _ _ _ (t Tm50 var50 lam50 app)

def app50 {Γ A B} : Tm50 Γ (arr50 A B) → Tm50 Γ A → Tm50 Γ B
 := λ t u Tm50 var50 lam50 app50 =>
     app50 _ _ _
         (t Tm50 var50 lam50 app50)
         (u Tm50 var50 lam50 app50)

def v050 {Γ A} : Tm50 (snoc50 Γ A) A
 := var50 vz50

def v150 {Γ A B} : Tm50 (snoc50 (snoc50 Γ A) B) A
 := var50 (vs50 vz50)

def v250 {Γ A B C} : Tm50 (snoc50 (snoc50 (snoc50 Γ A) B) C) A
 := var50 (vs50 (vs50 vz50))

def v350 {Γ A B C D} : Tm50 (snoc50 (snoc50 (snoc50 (snoc50 Γ A) B) C) D) A
 := var50 (vs50 (vs50 (vs50 vz50)))

def v450 {Γ A B C D E} : Tm50 (snoc50 (snoc50 (snoc50 (snoc50 (snoc50 Γ A) B) C) D) E) A
 := var50 (vs50 (vs50 (vs50 (vs50 vz50))))

def test50 {Γ A} : Tm50 Γ (arr50 (arr50 A A) (arr50 A A))
 := lam50 (lam50 (app50 v150 (app50 v150 (app50 v150 (app50 v150 (app50 v150 (app50 v150 v050)))))))


def Ty51 : Type 1
 := ∀ (Ty51 : Type)
      (ι   : Ty51)
      (arr : Ty51 → Ty51 → Ty51)
    , Ty51

def ι51 : Ty51 := λ _ ι51 _ => ι51

def arr51 : Ty51 → Ty51 → Ty51
 := λ A B Ty51 ι51 arr51 =>
     arr51 (A Ty51 ι51 arr51) (B Ty51 ι51 arr51)

def Con51 : Type 1
 := ∀ (Con51  : Type)
      (nil  : Con51)
      (snoc : Con51 → Ty51 → Con51)
    , Con51

def nil51 : Con51
 := λ Con51 nil51 snoc => nil51

def snoc51 : Con51 → Ty51 → Con51
 := λ Γ A Con51 nil51 snoc51 => snoc51 (Γ Con51 nil51 snoc51) A

def Var51 : Con51 → Ty51 → Type 1
 := λ Γ A =>
   ∀ (Var51 : Con51 → Ty51 → Type)
     (vz  : ∀ Γ A, Var51 (snoc51 Γ A) A)
     (vs  : ∀ Γ B A, Var51 Γ A → Var51 (snoc51 Γ B) A)
   , Var51 Γ A

def vz51 {Γ A} : Var51 (snoc51 Γ A) A
 := λ Var51 vz51 vs => vz51 _ _

def vs51 {Γ B A} : Var51 Γ A → Var51 (snoc51 Γ B) A
 := λ x Var51 vz51 vs51 => vs51 _ _ _ (x Var51 vz51 vs51)

def Tm51 : Con51 → Ty51 → Type 1
 := λ Γ A =>
   ∀ (Tm51  : Con51 → Ty51 → Type)
     (var   : ∀ Γ A     , Var51 Γ A → Tm51 Γ A)
     (lam   : ∀ Γ A B   , Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B))
     (app   : ∀ Γ A B   , Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B)
   , Tm51 Γ A

def var51 {Γ A} : Var51 Γ A → Tm51 Γ A
 := λ x Tm51 var51 lam app =>
     var51 _ _ x

def lam51 {Γ A B} : Tm51 (snoc51 Γ A) B → Tm51 Γ (arr51 A B)
 := λ t Tm51 var51 lam51 app =>
     lam51 _ _ _ (t Tm51 var51 lam51 app)

def app51 {Γ A B} : Tm51 Γ (arr51 A B) → Tm51 Γ A → Tm51 Γ B
 := λ t u Tm51 var51 lam51 app51 =>
     app51 _ _ _
         (t Tm51 var51 lam51 app51)
         (u Tm51 var51 lam51 app51)

def v051 {Γ A} : Tm51 (snoc51 Γ A) A
 := var51 vz51

def v151 {Γ A B} : Tm51 (snoc51 (snoc51 Γ A) B) A
 := var51 (vs51 vz51)

def v251 {Γ A B C} : Tm51 (snoc51 (snoc51 (snoc51 Γ A) B) C) A
 := var51 (vs51 (vs51 vz51))

def v351 {Γ A B C D} : Tm51 (snoc51 (snoc51 (snoc51 (snoc51 Γ A) B) C) D) A
 := var51 (vs51 (vs51 (vs51 vz51)))

def v451 {Γ A B C D E} : Tm51 (snoc51 (snoc51 (snoc51 (snoc51 (snoc51 Γ A) B) C) D) E) A
 := var51 (vs51 (vs51 (vs51 (vs51 vz51))))

def test51 {Γ A} : Tm51 Γ (arr51 (arr51 A A) (arr51 A A))
 := lam51 (lam51 (app51 v151 (app51 v151 (app51 v151 (app51 v151 (app51 v151 (app51 v151 v051)))))))


def Ty52 : Type 1
 := ∀ (Ty52 : Type)
      (ι   : Ty52)
      (arr : Ty52 → Ty52 → Ty52)
    , Ty52

def ι52 : Ty52 := λ _ ι52 _ => ι52

def arr52 : Ty52 → Ty52 → Ty52
 := λ A B Ty52 ι52 arr52 =>
     arr52 (A Ty52 ι52 arr52) (B Ty52 ι52 arr52)

def Con52 : Type 1
 := ∀ (Con52  : Type)
      (nil  : Con52)
      (snoc : Con52 → Ty52 → Con52)
    , Con52

def nil52 : Con52
 := λ Con52 nil52 snoc => nil52

def snoc52 : Con52 → Ty52 → Con52
 := λ Γ A Con52 nil52 snoc52 => snoc52 (Γ Con52 nil52 snoc52) A

def Var52 : Con52 → Ty52 → Type 1
 := λ Γ A =>
   ∀ (Var52 : Con52 → Ty52 → Type)
     (vz  : ∀ Γ A, Var52 (snoc52 Γ A) A)
     (vs  : ∀ Γ B A, Var52 Γ A → Var52 (snoc52 Γ B) A)
   , Var52 Γ A

def vz52 {Γ A} : Var52 (snoc52 Γ A) A
 := λ Var52 vz52 vs => vz52 _ _

def vs52 {Γ B A} : Var52 Γ A → Var52 (snoc52 Γ B) A
 := λ x Var52 vz52 vs52 => vs52 _ _ _ (x Var52 vz52 vs52)

def Tm52 : Con52 → Ty52 → Type 1
 := λ Γ A =>
   ∀ (Tm52  : Con52 → Ty52 → Type)
     (var   : ∀ Γ A     , Var52 Γ A → Tm52 Γ A)
     (lam   : ∀ Γ A B   , Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B))
     (app   : ∀ Γ A B   , Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B)
   , Tm52 Γ A

def var52 {Γ A} : Var52 Γ A → Tm52 Γ A
 := λ x Tm52 var52 lam app =>
     var52 _ _ x

def lam52 {Γ A B} : Tm52 (snoc52 Γ A) B → Tm52 Γ (arr52 A B)
 := λ t Tm52 var52 lam52 app =>
     lam52 _ _ _ (t Tm52 var52 lam52 app)

def app52 {Γ A B} : Tm52 Γ (arr52 A B) → Tm52 Γ A → Tm52 Γ B
 := λ t u Tm52 var52 lam52 app52 =>
     app52 _ _ _
         (t Tm52 var52 lam52 app52)
         (u Tm52 var52 lam52 app52)

def v052 {Γ A} : Tm52 (snoc52 Γ A) A
 := var52 vz52

def v152 {Γ A B} : Tm52 (snoc52 (snoc52 Γ A) B) A
 := var52 (vs52 vz52)

def v252 {Γ A B C} : Tm52 (snoc52 (snoc52 (snoc52 Γ A) B) C) A
 := var52 (vs52 (vs52 vz52))

def v352 {Γ A B C D} : Tm52 (snoc52 (snoc52 (snoc52 (snoc52 Γ A) B) C) D) A
 := var52 (vs52 (vs52 (vs52 vz52)))

def v452 {Γ A B C D E} : Tm52 (snoc52 (snoc52 (snoc52 (snoc52 (snoc52 Γ A) B) C) D) E) A
 := var52 (vs52 (vs52 (vs52 (vs52 vz52))))

def test52 {Γ A} : Tm52 Γ (arr52 (arr52 A A) (arr52 A A))
 := lam52 (lam52 (app52 v152 (app52 v152 (app52 v152 (app52 v152 (app52 v152 (app52 v152 v052)))))))


def Ty53 : Type 1
 := ∀ (Ty53 : Type)
      (ι   : Ty53)
      (arr : Ty53 → Ty53 → Ty53)
    , Ty53

def ι53 : Ty53 := λ _ ι53 _ => ι53

def arr53 : Ty53 → Ty53 → Ty53
 := λ A B Ty53 ι53 arr53 =>
     arr53 (A Ty53 ι53 arr53) (B Ty53 ι53 arr53)

def Con53 : Type 1
 := ∀ (Con53  : Type)
      (nil  : Con53)
      (snoc : Con53 → Ty53 → Con53)
    , Con53

def nil53 : Con53
 := λ Con53 nil53 snoc => nil53

def snoc53 : Con53 → Ty53 → Con53
 := λ Γ A Con53 nil53 snoc53 => snoc53 (Γ Con53 nil53 snoc53) A

def Var53 : Con53 → Ty53 → Type 1
 := λ Γ A =>
   ∀ (Var53 : Con53 → Ty53 → Type)
     (vz  : ∀ Γ A, Var53 (snoc53 Γ A) A)
     (vs  : ∀ Γ B A, Var53 Γ A → Var53 (snoc53 Γ B) A)
   , Var53 Γ A

def vz53 {Γ A} : Var53 (snoc53 Γ A) A
 := λ Var53 vz53 vs => vz53 _ _

def vs53 {Γ B A} : Var53 Γ A → Var53 (snoc53 Γ B) A
 := λ x Var53 vz53 vs53 => vs53 _ _ _ (x Var53 vz53 vs53)

def Tm53 : Con53 → Ty53 → Type 1
 := λ Γ A =>
   ∀ (Tm53  : Con53 → Ty53 → Type)
     (var   : ∀ Γ A     , Var53 Γ A → Tm53 Γ A)
     (lam   : ∀ Γ A B   , Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B))
     (app   : ∀ Γ A B   , Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B)
   , Tm53 Γ A

def var53 {Γ A} : Var53 Γ A → Tm53 Γ A
 := λ x Tm53 var53 lam app =>
     var53 _ _ x

def lam53 {Γ A B} : Tm53 (snoc53 Γ A) B → Tm53 Γ (arr53 A B)
 := λ t Tm53 var53 lam53 app =>
     lam53 _ _ _ (t Tm53 var53 lam53 app)

def app53 {Γ A B} : Tm53 Γ (arr53 A B) → Tm53 Γ A → Tm53 Γ B
 := λ t u Tm53 var53 lam53 app53 =>
     app53 _ _ _
         (t Tm53 var53 lam53 app53)
         (u Tm53 var53 lam53 app53)

def v053 {Γ A} : Tm53 (snoc53 Γ A) A
 := var53 vz53

def v153 {Γ A B} : Tm53 (snoc53 (snoc53 Γ A) B) A
 := var53 (vs53 vz53)

def v253 {Γ A B C} : Tm53 (snoc53 (snoc53 (snoc53 Γ A) B) C) A
 := var53 (vs53 (vs53 vz53))

def v353 {Γ A B C D} : Tm53 (snoc53 (snoc53 (snoc53 (snoc53 Γ A) B) C) D) A
 := var53 (vs53 (vs53 (vs53 vz53)))

def v453 {Γ A B C D E} : Tm53 (snoc53 (snoc53 (snoc53 (snoc53 (snoc53 Γ A) B) C) D) E) A
 := var53 (vs53 (vs53 (vs53 (vs53 vz53))))

def test53 {Γ A} : Tm53 Γ (arr53 (arr53 A A) (arr53 A A))
 := lam53 (lam53 (app53 v153 (app53 v153 (app53 v153 (app53 v153 (app53 v153 (app53 v153 v053)))))))


def Ty54 : Type 1
 := ∀ (Ty54 : Type)
      (ι   : Ty54)
      (arr : Ty54 → Ty54 → Ty54)
    , Ty54

def ι54 : Ty54 := λ _ ι54 _ => ι54

def arr54 : Ty54 → Ty54 → Ty54
 := λ A B Ty54 ι54 arr54 =>
     arr54 (A Ty54 ι54 arr54) (B Ty54 ι54 arr54)

def Con54 : Type 1
 := ∀ (Con54  : Type)
      (nil  : Con54)
      (snoc : Con54 → Ty54 → Con54)
    , Con54

def nil54 : Con54
 := λ Con54 nil54 snoc => nil54

def snoc54 : Con54 → Ty54 → Con54
 := λ Γ A Con54 nil54 snoc54 => snoc54 (Γ Con54 nil54 snoc54) A

def Var54 : Con54 → Ty54 → Type 1
 := λ Γ A =>
   ∀ (Var54 : Con54 → Ty54 → Type)
     (vz  : ∀ Γ A, Var54 (snoc54 Γ A) A)
     (vs  : ∀ Γ B A, Var54 Γ A → Var54 (snoc54 Γ B) A)
   , Var54 Γ A

def vz54 {Γ A} : Var54 (snoc54 Γ A) A
 := λ Var54 vz54 vs => vz54 _ _

def vs54 {Γ B A} : Var54 Γ A → Var54 (snoc54 Γ B) A
 := λ x Var54 vz54 vs54 => vs54 _ _ _ (x Var54 vz54 vs54)

def Tm54 : Con54 → Ty54 → Type 1
 := λ Γ A =>
   ∀ (Tm54  : Con54 → Ty54 → Type)
     (var   : ∀ Γ A     , Var54 Γ A → Tm54 Γ A)
     (lam   : ∀ Γ A B   , Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B))
     (app   : ∀ Γ A B   , Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B)
   , Tm54 Γ A

def var54 {Γ A} : Var54 Γ A → Tm54 Γ A
 := λ x Tm54 var54 lam app =>
     var54 _ _ x

def lam54 {Γ A B} : Tm54 (snoc54 Γ A) B → Tm54 Γ (arr54 A B)
 := λ t Tm54 var54 lam54 app =>
     lam54 _ _ _ (t Tm54 var54 lam54 app)

def app54 {Γ A B} : Tm54 Γ (arr54 A B) → Tm54 Γ A → Tm54 Γ B
 := λ t u Tm54 var54 lam54 app54 =>
     app54 _ _ _
         (t Tm54 var54 lam54 app54)
         (u Tm54 var54 lam54 app54)

def v054 {Γ A} : Tm54 (snoc54 Γ A) A
 := var54 vz54

def v154 {Γ A B} : Tm54 (snoc54 (snoc54 Γ A) B) A
 := var54 (vs54 vz54)

def v254 {Γ A B C} : Tm54 (snoc54 (snoc54 (snoc54 Γ A) B) C) A
 := var54 (vs54 (vs54 vz54))

def v354 {Γ A B C D} : Tm54 (snoc54 (snoc54 (snoc54 (snoc54 Γ A) B) C) D) A
 := var54 (vs54 (vs54 (vs54 vz54)))

def v454 {Γ A B C D E} : Tm54 (snoc54 (snoc54 (snoc54 (snoc54 (snoc54 Γ A) B) C) D) E) A
 := var54 (vs54 (vs54 (vs54 (vs54 vz54))))

def test54 {Γ A} : Tm54 Γ (arr54 (arr54 A A) (arr54 A A))
 := lam54 (lam54 (app54 v154 (app54 v154 (app54 v154 (app54 v154 (app54 v154 (app54 v154 v054)))))))


def Ty55 : Type 1
 := ∀ (Ty55 : Type)
      (ι   : Ty55)
      (arr : Ty55 → Ty55 → Ty55)
    , Ty55

def ι55 : Ty55 := λ _ ι55 _ => ι55

def arr55 : Ty55 → Ty55 → Ty55
 := λ A B Ty55 ι55 arr55 =>
     arr55 (A Ty55 ι55 arr55) (B Ty55 ι55 arr55)

def Con55 : Type 1
 := ∀ (Con55  : Type)
      (nil  : Con55)
      (snoc : Con55 → Ty55 → Con55)
    , Con55

def nil55 : Con55
 := λ Con55 nil55 snoc => nil55

def snoc55 : Con55 → Ty55 → Con55
 := λ Γ A Con55 nil55 snoc55 => snoc55 (Γ Con55 nil55 snoc55) A

def Var55 : Con55 → Ty55 → Type 1
 := λ Γ A =>
   ∀ (Var55 : Con55 → Ty55 → Type)
     (vz  : ∀ Γ A, Var55 (snoc55 Γ A) A)
     (vs  : ∀ Γ B A, Var55 Γ A → Var55 (snoc55 Γ B) A)
   , Var55 Γ A

def vz55 {Γ A} : Var55 (snoc55 Γ A) A
 := λ Var55 vz55 vs => vz55 _ _

def vs55 {Γ B A} : Var55 Γ A → Var55 (snoc55 Γ B) A
 := λ x Var55 vz55 vs55 => vs55 _ _ _ (x Var55 vz55 vs55)

def Tm55 : Con55 → Ty55 → Type 1
 := λ Γ A =>
   ∀ (Tm55  : Con55 → Ty55 → Type)
     (var   : ∀ Γ A     , Var55 Γ A → Tm55 Γ A)
     (lam   : ∀ Γ A B   , Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B))
     (app   : ∀ Γ A B   , Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B)
   , Tm55 Γ A

def var55 {Γ A} : Var55 Γ A → Tm55 Γ A
 := λ x Tm55 var55 lam app =>
     var55 _ _ x

def lam55 {Γ A B} : Tm55 (snoc55 Γ A) B → Tm55 Γ (arr55 A B)
 := λ t Tm55 var55 lam55 app =>
     lam55 _ _ _ (t Tm55 var55 lam55 app)

def app55 {Γ A B} : Tm55 Γ (arr55 A B) → Tm55 Γ A → Tm55 Γ B
 := λ t u Tm55 var55 lam55 app55 =>
     app55 _ _ _
         (t Tm55 var55 lam55 app55)
         (u Tm55 var55 lam55 app55)

def v055 {Γ A} : Tm55 (snoc55 Γ A) A
 := var55 vz55

def v155 {Γ A B} : Tm55 (snoc55 (snoc55 Γ A) B) A
 := var55 (vs55 vz55)

def v255 {Γ A B C} : Tm55 (snoc55 (snoc55 (snoc55 Γ A) B) C) A
 := var55 (vs55 (vs55 vz55))

def v355 {Γ A B C D} : Tm55 (snoc55 (snoc55 (snoc55 (snoc55 Γ A) B) C) D) A
 := var55 (vs55 (vs55 (vs55 vz55)))

def v455 {Γ A B C D E} : Tm55 (snoc55 (snoc55 (snoc55 (snoc55 (snoc55 Γ A) B) C) D) E) A
 := var55 (vs55 (vs55 (vs55 (vs55 vz55))))

def test55 {Γ A} : Tm55 Γ (arr55 (arr55 A A) (arr55 A A))
 := lam55 (lam55 (app55 v155 (app55 v155 (app55 v155 (app55 v155 (app55 v155 (app55 v155 v055)))))))


def Ty56 : Type 1
 := ∀ (Ty56 : Type)
      (ι   : Ty56)
      (arr : Ty56 → Ty56 → Ty56)
    , Ty56

def ι56 : Ty56 := λ _ ι56 _ => ι56

def arr56 : Ty56 → Ty56 → Ty56
 := λ A B Ty56 ι56 arr56 =>
     arr56 (A Ty56 ι56 arr56) (B Ty56 ι56 arr56)

def Con56 : Type 1
 := ∀ (Con56  : Type)
      (nil  : Con56)
      (snoc : Con56 → Ty56 → Con56)
    , Con56

def nil56 : Con56
 := λ Con56 nil56 snoc => nil56

def snoc56 : Con56 → Ty56 → Con56
 := λ Γ A Con56 nil56 snoc56 => snoc56 (Γ Con56 nil56 snoc56) A

def Var56 : Con56 → Ty56 → Type 1
 := λ Γ A =>
   ∀ (Var56 : Con56 → Ty56 → Type)
     (vz  : ∀ Γ A, Var56 (snoc56 Γ A) A)
     (vs  : ∀ Γ B A, Var56 Γ A → Var56 (snoc56 Γ B) A)
   , Var56 Γ A

def vz56 {Γ A} : Var56 (snoc56 Γ A) A
 := λ Var56 vz56 vs => vz56 _ _

def vs56 {Γ B A} : Var56 Γ A → Var56 (snoc56 Γ B) A
 := λ x Var56 vz56 vs56 => vs56 _ _ _ (x Var56 vz56 vs56)

def Tm56 : Con56 → Ty56 → Type 1
 := λ Γ A =>
   ∀ (Tm56  : Con56 → Ty56 → Type)
     (var   : ∀ Γ A     , Var56 Γ A → Tm56 Γ A)
     (lam   : ∀ Γ A B   , Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B))
     (app   : ∀ Γ A B   , Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B)
   , Tm56 Γ A

def var56 {Γ A} : Var56 Γ A → Tm56 Γ A
 := λ x Tm56 var56 lam app =>
     var56 _ _ x

def lam56 {Γ A B} : Tm56 (snoc56 Γ A) B → Tm56 Γ (arr56 A B)
 := λ t Tm56 var56 lam56 app =>
     lam56 _ _ _ (t Tm56 var56 lam56 app)

def app56 {Γ A B} : Tm56 Γ (arr56 A B) → Tm56 Γ A → Tm56 Γ B
 := λ t u Tm56 var56 lam56 app56 =>
     app56 _ _ _
         (t Tm56 var56 lam56 app56)
         (u Tm56 var56 lam56 app56)

def v056 {Γ A} : Tm56 (snoc56 Γ A) A
 := var56 vz56

def v156 {Γ A B} : Tm56 (snoc56 (snoc56 Γ A) B) A
 := var56 (vs56 vz56)

def v256 {Γ A B C} : Tm56 (snoc56 (snoc56 (snoc56 Γ A) B) C) A
 := var56 (vs56 (vs56 vz56))

def v356 {Γ A B C D} : Tm56 (snoc56 (snoc56 (snoc56 (snoc56 Γ A) B) C) D) A
 := var56 (vs56 (vs56 (vs56 vz56)))

def v456 {Γ A B C D E} : Tm56 (snoc56 (snoc56 (snoc56 (snoc56 (snoc56 Γ A) B) C) D) E) A
 := var56 (vs56 (vs56 (vs56 (vs56 vz56))))

def test56 {Γ A} : Tm56 Γ (arr56 (arr56 A A) (arr56 A A))
 := lam56 (lam56 (app56 v156 (app56 v156 (app56 v156 (app56 v156 (app56 v156 (app56 v156 v056)))))))


def Ty57 : Type 1
 := ∀ (Ty57 : Type)
      (ι   : Ty57)
      (arr : Ty57 → Ty57 → Ty57)
    , Ty57

def ι57 : Ty57 := λ _ ι57 _ => ι57

def arr57 : Ty57 → Ty57 → Ty57
 := λ A B Ty57 ι57 arr57 =>
     arr57 (A Ty57 ι57 arr57) (B Ty57 ι57 arr57)

def Con57 : Type 1
 := ∀ (Con57  : Type)
      (nil  : Con57)
      (snoc : Con57 → Ty57 → Con57)
    , Con57

def nil57 : Con57
 := λ Con57 nil57 snoc => nil57

def snoc57 : Con57 → Ty57 → Con57
 := λ Γ A Con57 nil57 snoc57 => snoc57 (Γ Con57 nil57 snoc57) A

def Var57 : Con57 → Ty57 → Type 1
 := λ Γ A =>
   ∀ (Var57 : Con57 → Ty57 → Type)
     (vz  : ∀ Γ A, Var57 (snoc57 Γ A) A)
     (vs  : ∀ Γ B A, Var57 Γ A → Var57 (snoc57 Γ B) A)
   , Var57 Γ A

def vz57 {Γ A} : Var57 (snoc57 Γ A) A
 := λ Var57 vz57 vs => vz57 _ _

def vs57 {Γ B A} : Var57 Γ A → Var57 (snoc57 Γ B) A
 := λ x Var57 vz57 vs57 => vs57 _ _ _ (x Var57 vz57 vs57)

def Tm57 : Con57 → Ty57 → Type 1
 := λ Γ A =>
   ∀ (Tm57  : Con57 → Ty57 → Type)
     (var   : ∀ Γ A     , Var57 Γ A → Tm57 Γ A)
     (lam   : ∀ Γ A B   , Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B))
     (app   : ∀ Γ A B   , Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B)
   , Tm57 Γ A

def var57 {Γ A} : Var57 Γ A → Tm57 Γ A
 := λ x Tm57 var57 lam app =>
     var57 _ _ x

def lam57 {Γ A B} : Tm57 (snoc57 Γ A) B → Tm57 Γ (arr57 A B)
 := λ t Tm57 var57 lam57 app =>
     lam57 _ _ _ (t Tm57 var57 lam57 app)

def app57 {Γ A B} : Tm57 Γ (arr57 A B) → Tm57 Γ A → Tm57 Γ B
 := λ t u Tm57 var57 lam57 app57 =>
     app57 _ _ _
         (t Tm57 var57 lam57 app57)
         (u Tm57 var57 lam57 app57)

def v057 {Γ A} : Tm57 (snoc57 Γ A) A
 := var57 vz57

def v157 {Γ A B} : Tm57 (snoc57 (snoc57 Γ A) B) A
 := var57 (vs57 vz57)

def v257 {Γ A B C} : Tm57 (snoc57 (snoc57 (snoc57 Γ A) B) C) A
 := var57 (vs57 (vs57 vz57))

def v357 {Γ A B C D} : Tm57 (snoc57 (snoc57 (snoc57 (snoc57 Γ A) B) C) D) A
 := var57 (vs57 (vs57 (vs57 vz57)))

def v457 {Γ A B C D E} : Tm57 (snoc57 (snoc57 (snoc57 (snoc57 (snoc57 Γ A) B) C) D) E) A
 := var57 (vs57 (vs57 (vs57 (vs57 vz57))))

def test57 {Γ A} : Tm57 Γ (arr57 (arr57 A A) (arr57 A A))
 := lam57 (lam57 (app57 v157 (app57 v157 (app57 v157 (app57 v157 (app57 v157 (app57 v157 v057)))))))


def Ty58 : Type 1
 := ∀ (Ty58 : Type)
      (ι   : Ty58)
      (arr : Ty58 → Ty58 → Ty58)
    , Ty58

def ι58 : Ty58 := λ _ ι58 _ => ι58

def arr58 : Ty58 → Ty58 → Ty58
 := λ A B Ty58 ι58 arr58 =>
     arr58 (A Ty58 ι58 arr58) (B Ty58 ι58 arr58)

def Con58 : Type 1
 := ∀ (Con58  : Type)
      (nil  : Con58)
      (snoc : Con58 → Ty58 → Con58)
    , Con58

def nil58 : Con58
 := λ Con58 nil58 snoc => nil58

def snoc58 : Con58 → Ty58 → Con58
 := λ Γ A Con58 nil58 snoc58 => snoc58 (Γ Con58 nil58 snoc58) A

def Var58 : Con58 → Ty58 → Type 1
 := λ Γ A =>
   ∀ (Var58 : Con58 → Ty58 → Type)
     (vz  : ∀ Γ A, Var58 (snoc58 Γ A) A)
     (vs  : ∀ Γ B A, Var58 Γ A → Var58 (snoc58 Γ B) A)
   , Var58 Γ A

def vz58 {Γ A} : Var58 (snoc58 Γ A) A
 := λ Var58 vz58 vs => vz58 _ _

def vs58 {Γ B A} : Var58 Γ A → Var58 (snoc58 Γ B) A
 := λ x Var58 vz58 vs58 => vs58 _ _ _ (x Var58 vz58 vs58)

def Tm58 : Con58 → Ty58 → Type 1
 := λ Γ A =>
   ∀ (Tm58  : Con58 → Ty58 → Type)
     (var   : ∀ Γ A     , Var58 Γ A → Tm58 Γ A)
     (lam   : ∀ Γ A B   , Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B))
     (app   : ∀ Γ A B   , Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B)
   , Tm58 Γ A

def var58 {Γ A} : Var58 Γ A → Tm58 Γ A
 := λ x Tm58 var58 lam app =>
     var58 _ _ x

def lam58 {Γ A B} : Tm58 (snoc58 Γ A) B → Tm58 Γ (arr58 A B)
 := λ t Tm58 var58 lam58 app =>
     lam58 _ _ _ (t Tm58 var58 lam58 app)

def app58 {Γ A B} : Tm58 Γ (arr58 A B) → Tm58 Γ A → Tm58 Γ B
 := λ t u Tm58 var58 lam58 app58 =>
     app58 _ _ _
         (t Tm58 var58 lam58 app58)
         (u Tm58 var58 lam58 app58)

def v058 {Γ A} : Tm58 (snoc58 Γ A) A
 := var58 vz58

def v158 {Γ A B} : Tm58 (snoc58 (snoc58 Γ A) B) A
 := var58 (vs58 vz58)

def v258 {Γ A B C} : Tm58 (snoc58 (snoc58 (snoc58 Γ A) B) C) A
 := var58 (vs58 (vs58 vz58))

def v358 {Γ A B C D} : Tm58 (snoc58 (snoc58 (snoc58 (snoc58 Γ A) B) C) D) A
 := var58 (vs58 (vs58 (vs58 vz58)))

def v458 {Γ A B C D E} : Tm58 (snoc58 (snoc58 (snoc58 (snoc58 (snoc58 Γ A) B) C) D) E) A
 := var58 (vs58 (vs58 (vs58 (vs58 vz58))))

def test58 {Γ A} : Tm58 Γ (arr58 (arr58 A A) (arr58 A A))
 := lam58 (lam58 (app58 v158 (app58 v158 (app58 v158 (app58 v158 (app58 v158 (app58 v158 v058)))))))


def Ty59 : Type 1
 := ∀ (Ty59 : Type)
      (ι   : Ty59)
      (arr : Ty59 → Ty59 → Ty59)
    , Ty59

def ι59 : Ty59 := λ _ ι59 _ => ι59

def arr59 : Ty59 → Ty59 → Ty59
 := λ A B Ty59 ι59 arr59 =>
     arr59 (A Ty59 ι59 arr59) (B Ty59 ι59 arr59)

def Con59 : Type 1
 := ∀ (Con59  : Type)
      (nil  : Con59)
      (snoc : Con59 → Ty59 → Con59)
    , Con59

def nil59 : Con59
 := λ Con59 nil59 snoc => nil59

def snoc59 : Con59 → Ty59 → Con59
 := λ Γ A Con59 nil59 snoc59 => snoc59 (Γ Con59 nil59 snoc59) A

def Var59 : Con59 → Ty59 → Type 1
 := λ Γ A =>
   ∀ (Var59 : Con59 → Ty59 → Type)
     (vz  : ∀ Γ A, Var59 (snoc59 Γ A) A)
     (vs  : ∀ Γ B A, Var59 Γ A → Var59 (snoc59 Γ B) A)
   , Var59 Γ A

def vz59 {Γ A} : Var59 (snoc59 Γ A) A
 := λ Var59 vz59 vs => vz59 _ _

def vs59 {Γ B A} : Var59 Γ A → Var59 (snoc59 Γ B) A
 := λ x Var59 vz59 vs59 => vs59 _ _ _ (x Var59 vz59 vs59)

def Tm59 : Con59 → Ty59 → Type 1
 := λ Γ A =>
   ∀ (Tm59  : Con59 → Ty59 → Type)
     (var   : ∀ Γ A     , Var59 Γ A → Tm59 Γ A)
     (lam   : ∀ Γ A B   , Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B))
     (app   : ∀ Γ A B   , Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B)
   , Tm59 Γ A

def var59 {Γ A} : Var59 Γ A → Tm59 Γ A
 := λ x Tm59 var59 lam app =>
     var59 _ _ x

def lam59 {Γ A B} : Tm59 (snoc59 Γ A) B → Tm59 Γ (arr59 A B)
 := λ t Tm59 var59 lam59 app =>
     lam59 _ _ _ (t Tm59 var59 lam59 app)

def app59 {Γ A B} : Tm59 Γ (arr59 A B) → Tm59 Γ A → Tm59 Γ B
 := λ t u Tm59 var59 lam59 app59 =>
     app59 _ _ _
         (t Tm59 var59 lam59 app59)
         (u Tm59 var59 lam59 app59)

def v059 {Γ A} : Tm59 (snoc59 Γ A) A
 := var59 vz59

def v159 {Γ A B} : Tm59 (snoc59 (snoc59 Γ A) B) A
 := var59 (vs59 vz59)

def v259 {Γ A B C} : Tm59 (snoc59 (snoc59 (snoc59 Γ A) B) C) A
 := var59 (vs59 (vs59 vz59))

def v359 {Γ A B C D} : Tm59 (snoc59 (snoc59 (snoc59 (snoc59 Γ A) B) C) D) A
 := var59 (vs59 (vs59 (vs59 vz59)))

def v459 {Γ A B C D E} : Tm59 (snoc59 (snoc59 (snoc59 (snoc59 (snoc59 Γ A) B) C) D) E) A
 := var59 (vs59 (vs59 (vs59 (vs59 vz59))))

def test59 {Γ A} : Tm59 Γ (arr59 (arr59 A A) (arr59 A A))
 := lam59 (lam59 (app59 v159 (app59 v159 (app59 v159 (app59 v159 (app59 v159 (app59 v159 v059)))))))


def Ty60 : Type 1
 := ∀ (Ty60 : Type)
      (ι   : Ty60)
      (arr : Ty60 → Ty60 → Ty60)
    , Ty60

def ι60 : Ty60 := λ _ ι60 _ => ι60

def arr60 : Ty60 → Ty60 → Ty60
 := λ A B Ty60 ι60 arr60 =>
     arr60 (A Ty60 ι60 arr60) (B Ty60 ι60 arr60)

def Con60 : Type 1
 := ∀ (Con60  : Type)
      (nil  : Con60)
      (snoc : Con60 → Ty60 → Con60)
    , Con60

def nil60 : Con60
 := λ Con60 nil60 snoc => nil60

def snoc60 : Con60 → Ty60 → Con60
 := λ Γ A Con60 nil60 snoc60 => snoc60 (Γ Con60 nil60 snoc60) A

def Var60 : Con60 → Ty60 → Type 1
 := λ Γ A =>
   ∀ (Var60 : Con60 → Ty60 → Type)
     (vz  : ∀ Γ A, Var60 (snoc60 Γ A) A)
     (vs  : ∀ Γ B A, Var60 Γ A → Var60 (snoc60 Γ B) A)
   , Var60 Γ A

def vz60 {Γ A} : Var60 (snoc60 Γ A) A
 := λ Var60 vz60 vs => vz60 _ _

def vs60 {Γ B A} : Var60 Γ A → Var60 (snoc60 Γ B) A
 := λ x Var60 vz60 vs60 => vs60 _ _ _ (x Var60 vz60 vs60)

def Tm60 : Con60 → Ty60 → Type 1
 := λ Γ A =>
   ∀ (Tm60  : Con60 → Ty60 → Type)
     (var   : ∀ Γ A     , Var60 Γ A → Tm60 Γ A)
     (lam   : ∀ Γ A B   , Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B))
     (app   : ∀ Γ A B   , Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B)
   , Tm60 Γ A

def var60 {Γ A} : Var60 Γ A → Tm60 Γ A
 := λ x Tm60 var60 lam app =>
     var60 _ _ x

def lam60 {Γ A B} : Tm60 (snoc60 Γ A) B → Tm60 Γ (arr60 A B)
 := λ t Tm60 var60 lam60 app =>
     lam60 _ _ _ (t Tm60 var60 lam60 app)

def app60 {Γ A B} : Tm60 Γ (arr60 A B) → Tm60 Γ A → Tm60 Γ B
 := λ t u Tm60 var60 lam60 app60 =>
     app60 _ _ _
         (t Tm60 var60 lam60 app60)
         (u Tm60 var60 lam60 app60)

def v060 {Γ A} : Tm60 (snoc60 Γ A) A
 := var60 vz60

def v160 {Γ A B} : Tm60 (snoc60 (snoc60 Γ A) B) A
 := var60 (vs60 vz60)

def v260 {Γ A B C} : Tm60 (snoc60 (snoc60 (snoc60 Γ A) B) C) A
 := var60 (vs60 (vs60 vz60))

def v360 {Γ A B C D} : Tm60 (snoc60 (snoc60 (snoc60 (snoc60 Γ A) B) C) D) A
 := var60 (vs60 (vs60 (vs60 vz60)))

def v460 {Γ A B C D E} : Tm60 (snoc60 (snoc60 (snoc60 (snoc60 (snoc60 Γ A) B) C) D) E) A
 := var60 (vs60 (vs60 (vs60 (vs60 vz60))))

def test60 {Γ A} : Tm60 Γ (arr60 (arr60 A A) (arr60 A A))
 := lam60 (lam60 (app60 v160 (app60 v160 (app60 v160 (app60 v160 (app60 v160 (app60 v160 v060)))))))


def Ty61 : Type 1
 := ∀ (Ty61 : Type)
      (ι   : Ty61)
      (arr : Ty61 → Ty61 → Ty61)
    , Ty61

def ι61 : Ty61 := λ _ ι61 _ => ι61

def arr61 : Ty61 → Ty61 → Ty61
 := λ A B Ty61 ι61 arr61 =>
     arr61 (A Ty61 ι61 arr61) (B Ty61 ι61 arr61)

def Con61 : Type 1
 := ∀ (Con61  : Type)
      (nil  : Con61)
      (snoc : Con61 → Ty61 → Con61)
    , Con61

def nil61 : Con61
 := λ Con61 nil61 snoc => nil61

def snoc61 : Con61 → Ty61 → Con61
 := λ Γ A Con61 nil61 snoc61 => snoc61 (Γ Con61 nil61 snoc61) A

def Var61 : Con61 → Ty61 → Type 1
 := λ Γ A =>
   ∀ (Var61 : Con61 → Ty61 → Type)
     (vz  : ∀ Γ A, Var61 (snoc61 Γ A) A)
     (vs  : ∀ Γ B A, Var61 Γ A → Var61 (snoc61 Γ B) A)
   , Var61 Γ A

def vz61 {Γ A} : Var61 (snoc61 Γ A) A
 := λ Var61 vz61 vs => vz61 _ _

def vs61 {Γ B A} : Var61 Γ A → Var61 (snoc61 Γ B) A
 := λ x Var61 vz61 vs61 => vs61 _ _ _ (x Var61 vz61 vs61)

def Tm61 : Con61 → Ty61 → Type 1
 := λ Γ A =>
   ∀ (Tm61  : Con61 → Ty61 → Type)
     (var   : ∀ Γ A     , Var61 Γ A → Tm61 Γ A)
     (lam   : ∀ Γ A B   , Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B))
     (app   : ∀ Γ A B   , Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B)
   , Tm61 Γ A

def var61 {Γ A} : Var61 Γ A → Tm61 Γ A
 := λ x Tm61 var61 lam app =>
     var61 _ _ x

def lam61 {Γ A B} : Tm61 (snoc61 Γ A) B → Tm61 Γ (arr61 A B)
 := λ t Tm61 var61 lam61 app =>
     lam61 _ _ _ (t Tm61 var61 lam61 app)

def app61 {Γ A B} : Tm61 Γ (arr61 A B) → Tm61 Γ A → Tm61 Γ B
 := λ t u Tm61 var61 lam61 app61 =>
     app61 _ _ _
         (t Tm61 var61 lam61 app61)
         (u Tm61 var61 lam61 app61)

def v061 {Γ A} : Tm61 (snoc61 Γ A) A
 := var61 vz61

def v161 {Γ A B} : Tm61 (snoc61 (snoc61 Γ A) B) A
 := var61 (vs61 vz61)

def v261 {Γ A B C} : Tm61 (snoc61 (snoc61 (snoc61 Γ A) B) C) A
 := var61 (vs61 (vs61 vz61))

def v361 {Γ A B C D} : Tm61 (snoc61 (snoc61 (snoc61 (snoc61 Γ A) B) C) D) A
 := var61 (vs61 (vs61 (vs61 vz61)))

def v461 {Γ A B C D E} : Tm61 (snoc61 (snoc61 (snoc61 (snoc61 (snoc61 Γ A) B) C) D) E) A
 := var61 (vs61 (vs61 (vs61 (vs61 vz61))))

def test61 {Γ A} : Tm61 Γ (arr61 (arr61 A A) (arr61 A A))
 := lam61 (lam61 (app61 v161 (app61 v161 (app61 v161 (app61 v161 (app61 v161 (app61 v161 v061)))))))


def Ty62 : Type 1
 := ∀ (Ty62 : Type)
      (ι   : Ty62)
      (arr : Ty62 → Ty62 → Ty62)
    , Ty62

def ι62 : Ty62 := λ _ ι62 _ => ι62

def arr62 : Ty62 → Ty62 → Ty62
 := λ A B Ty62 ι62 arr62 =>
     arr62 (A Ty62 ι62 arr62) (B Ty62 ι62 arr62)

def Con62 : Type 1
 := ∀ (Con62  : Type)
      (nil  : Con62)
      (snoc : Con62 → Ty62 → Con62)
    , Con62

def nil62 : Con62
 := λ Con62 nil62 snoc => nil62

def snoc62 : Con62 → Ty62 → Con62
 := λ Γ A Con62 nil62 snoc62 => snoc62 (Γ Con62 nil62 snoc62) A

def Var62 : Con62 → Ty62 → Type 1
 := λ Γ A =>
   ∀ (Var62 : Con62 → Ty62 → Type)
     (vz  : ∀ Γ A, Var62 (snoc62 Γ A) A)
     (vs  : ∀ Γ B A, Var62 Γ A → Var62 (snoc62 Γ B) A)
   , Var62 Γ A

def vz62 {Γ A} : Var62 (snoc62 Γ A) A
 := λ Var62 vz62 vs => vz62 _ _

def vs62 {Γ B A} : Var62 Γ A → Var62 (snoc62 Γ B) A
 := λ x Var62 vz62 vs62 => vs62 _ _ _ (x Var62 vz62 vs62)

def Tm62 : Con62 → Ty62 → Type 1
 := λ Γ A =>
   ∀ (Tm62  : Con62 → Ty62 → Type)
     (var   : ∀ Γ A     , Var62 Γ A → Tm62 Γ A)
     (lam   : ∀ Γ A B   , Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B))
     (app   : ∀ Γ A B   , Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B)
   , Tm62 Γ A

def var62 {Γ A} : Var62 Γ A → Tm62 Γ A
 := λ x Tm62 var62 lam app =>
     var62 _ _ x

def lam62 {Γ A B} : Tm62 (snoc62 Γ A) B → Tm62 Γ (arr62 A B)
 := λ t Tm62 var62 lam62 app =>
     lam62 _ _ _ (t Tm62 var62 lam62 app)

def app62 {Γ A B} : Tm62 Γ (arr62 A B) → Tm62 Γ A → Tm62 Γ B
 := λ t u Tm62 var62 lam62 app62 =>
     app62 _ _ _
         (t Tm62 var62 lam62 app62)
         (u Tm62 var62 lam62 app62)

def v062 {Γ A} : Tm62 (snoc62 Γ A) A
 := var62 vz62

def v162 {Γ A B} : Tm62 (snoc62 (snoc62 Γ A) B) A
 := var62 (vs62 vz62)

def v262 {Γ A B C} : Tm62 (snoc62 (snoc62 (snoc62 Γ A) B) C) A
 := var62 (vs62 (vs62 vz62))

def v362 {Γ A B C D} : Tm62 (snoc62 (snoc62 (snoc62 (snoc62 Γ A) B) C) D) A
 := var62 (vs62 (vs62 (vs62 vz62)))

def v462 {Γ A B C D E} : Tm62 (snoc62 (snoc62 (snoc62 (snoc62 (snoc62 Γ A) B) C) D) E) A
 := var62 (vs62 (vs62 (vs62 (vs62 vz62))))

def test62 {Γ A} : Tm62 Γ (arr62 (arr62 A A) (arr62 A A))
 := lam62 (lam62 (app62 v162 (app62 v162 (app62 v162 (app62 v162 (app62 v162 (app62 v162 v062)))))))


def Ty63 : Type 1
 := ∀ (Ty63 : Type)
      (ι   : Ty63)
      (arr : Ty63 → Ty63 → Ty63)
    , Ty63

def ι63 : Ty63 := λ _ ι63 _ => ι63

def arr63 : Ty63 → Ty63 → Ty63
 := λ A B Ty63 ι63 arr63 =>
     arr63 (A Ty63 ι63 arr63) (B Ty63 ι63 arr63)

def Con63 : Type 1
 := ∀ (Con63  : Type)
      (nil  : Con63)
      (snoc : Con63 → Ty63 → Con63)
    , Con63

def nil63 : Con63
 := λ Con63 nil63 snoc => nil63

def snoc63 : Con63 → Ty63 → Con63
 := λ Γ A Con63 nil63 snoc63 => snoc63 (Γ Con63 nil63 snoc63) A

def Var63 : Con63 → Ty63 → Type 1
 := λ Γ A =>
   ∀ (Var63 : Con63 → Ty63 → Type)
     (vz  : ∀ Γ A, Var63 (snoc63 Γ A) A)
     (vs  : ∀ Γ B A, Var63 Γ A → Var63 (snoc63 Γ B) A)
   , Var63 Γ A

def vz63 {Γ A} : Var63 (snoc63 Γ A) A
 := λ Var63 vz63 vs => vz63 _ _

def vs63 {Γ B A} : Var63 Γ A → Var63 (snoc63 Γ B) A
 := λ x Var63 vz63 vs63 => vs63 _ _ _ (x Var63 vz63 vs63)

def Tm63 : Con63 → Ty63 → Type 1
 := λ Γ A =>
   ∀ (Tm63  : Con63 → Ty63 → Type)
     (var   : ∀ Γ A     , Var63 Γ A → Tm63 Γ A)
     (lam   : ∀ Γ A B   , Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B))
     (app   : ∀ Γ A B   , Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B)
   , Tm63 Γ A

def var63 {Γ A} : Var63 Γ A → Tm63 Γ A
 := λ x Tm63 var63 lam app =>
     var63 _ _ x

def lam63 {Γ A B} : Tm63 (snoc63 Γ A) B → Tm63 Γ (arr63 A B)
 := λ t Tm63 var63 lam63 app =>
     lam63 _ _ _ (t Tm63 var63 lam63 app)

def app63 {Γ A B} : Tm63 Γ (arr63 A B) → Tm63 Γ A → Tm63 Γ B
 := λ t u Tm63 var63 lam63 app63 =>
     app63 _ _ _
         (t Tm63 var63 lam63 app63)
         (u Tm63 var63 lam63 app63)

def v063 {Γ A} : Tm63 (snoc63 Γ A) A
 := var63 vz63

def v163 {Γ A B} : Tm63 (snoc63 (snoc63 Γ A) B) A
 := var63 (vs63 vz63)

def v263 {Γ A B C} : Tm63 (snoc63 (snoc63 (snoc63 Γ A) B) C) A
 := var63 (vs63 (vs63 vz63))

def v363 {Γ A B C D} : Tm63 (snoc63 (snoc63 (snoc63 (snoc63 Γ A) B) C) D) A
 := var63 (vs63 (vs63 (vs63 vz63)))

def v463 {Γ A B C D E} : Tm63 (snoc63 (snoc63 (snoc63 (snoc63 (snoc63 Γ A) B) C) D) E) A
 := var63 (vs63 (vs63 (vs63 (vs63 vz63))))

def test63 {Γ A} : Tm63 Γ (arr63 (arr63 A A) (arr63 A A))
 := lam63 (lam63 (app63 v163 (app63 v163 (app63 v163 (app63 v163 (app63 v163 (app63 v163 v063)))))))


def Ty64 : Type 1
 := ∀ (Ty64 : Type)
      (ι   : Ty64)
      (arr : Ty64 → Ty64 → Ty64)
    , Ty64

def ι64 : Ty64 := λ _ ι64 _ => ι64

def arr64 : Ty64 → Ty64 → Ty64
 := λ A B Ty64 ι64 arr64 =>
     arr64 (A Ty64 ι64 arr64) (B Ty64 ι64 arr64)

def Con64 : Type 1
 := ∀ (Con64  : Type)
      (nil  : Con64)
      (snoc : Con64 → Ty64 → Con64)
    , Con64

def nil64 : Con64
 := λ Con64 nil64 snoc => nil64

def snoc64 : Con64 → Ty64 → Con64
 := λ Γ A Con64 nil64 snoc64 => snoc64 (Γ Con64 nil64 snoc64) A

def Var64 : Con64 → Ty64 → Type 1
 := λ Γ A =>
   ∀ (Var64 : Con64 → Ty64 → Type)
     (vz  : ∀ Γ A, Var64 (snoc64 Γ A) A)
     (vs  : ∀ Γ B A, Var64 Γ A → Var64 (snoc64 Γ B) A)
   , Var64 Γ A

def vz64 {Γ A} : Var64 (snoc64 Γ A) A
 := λ Var64 vz64 vs => vz64 _ _

def vs64 {Γ B A} : Var64 Γ A → Var64 (snoc64 Γ B) A
 := λ x Var64 vz64 vs64 => vs64 _ _ _ (x Var64 vz64 vs64)

def Tm64 : Con64 → Ty64 → Type 1
 := λ Γ A =>
   ∀ (Tm64  : Con64 → Ty64 → Type)
     (var   : ∀ Γ A     , Var64 Γ A → Tm64 Γ A)
     (lam   : ∀ Γ A B   , Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B))
     (app   : ∀ Γ A B   , Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B)
   , Tm64 Γ A

def var64 {Γ A} : Var64 Γ A → Tm64 Γ A
 := λ x Tm64 var64 lam app =>
     var64 _ _ x

def lam64 {Γ A B} : Tm64 (snoc64 Γ A) B → Tm64 Γ (arr64 A B)
 := λ t Tm64 var64 lam64 app =>
     lam64 _ _ _ (t Tm64 var64 lam64 app)

def app64 {Γ A B} : Tm64 Γ (arr64 A B) → Tm64 Γ A → Tm64 Γ B
 := λ t u Tm64 var64 lam64 app64 =>
     app64 _ _ _
         (t Tm64 var64 lam64 app64)
         (u Tm64 var64 lam64 app64)

def v064 {Γ A} : Tm64 (snoc64 Γ A) A
 := var64 vz64

def v164 {Γ A B} : Tm64 (snoc64 (snoc64 Γ A) B) A
 := var64 (vs64 vz64)

def v264 {Γ A B C} : Tm64 (snoc64 (snoc64 (snoc64 Γ A) B) C) A
 := var64 (vs64 (vs64 vz64))

def v364 {Γ A B C D} : Tm64 (snoc64 (snoc64 (snoc64 (snoc64 Γ A) B) C) D) A
 := var64 (vs64 (vs64 (vs64 vz64)))

def v464 {Γ A B C D E} : Tm64 (snoc64 (snoc64 (snoc64 (snoc64 (snoc64 Γ A) B) C) D) E) A
 := var64 (vs64 (vs64 (vs64 (vs64 vz64))))

def test64 {Γ A} : Tm64 Γ (arr64 (arr64 A A) (arr64 A A))
 := lam64 (lam64 (app64 v164 (app64 v164 (app64 v164 (app64 v164 (app64 v164 (app64 v164 v064)))))))


def Ty65 : Type 1
 := ∀ (Ty65 : Type)
      (ι   : Ty65)
      (arr : Ty65 → Ty65 → Ty65)
    , Ty65

def ι65 : Ty65 := λ _ ι65 _ => ι65

def arr65 : Ty65 → Ty65 → Ty65
 := λ A B Ty65 ι65 arr65 =>
     arr65 (A Ty65 ι65 arr65) (B Ty65 ι65 arr65)

def Con65 : Type 1
 := ∀ (Con65  : Type)
      (nil  : Con65)
      (snoc : Con65 → Ty65 → Con65)
    , Con65

def nil65 : Con65
 := λ Con65 nil65 snoc => nil65

def snoc65 : Con65 → Ty65 → Con65
 := λ Γ A Con65 nil65 snoc65 => snoc65 (Γ Con65 nil65 snoc65) A

def Var65 : Con65 → Ty65 → Type 1
 := λ Γ A =>
   ∀ (Var65 : Con65 → Ty65 → Type)
     (vz  : ∀ Γ A, Var65 (snoc65 Γ A) A)
     (vs  : ∀ Γ B A, Var65 Γ A → Var65 (snoc65 Γ B) A)
   , Var65 Γ A

def vz65 {Γ A} : Var65 (snoc65 Γ A) A
 := λ Var65 vz65 vs => vz65 _ _

def vs65 {Γ B A} : Var65 Γ A → Var65 (snoc65 Γ B) A
 := λ x Var65 vz65 vs65 => vs65 _ _ _ (x Var65 vz65 vs65)

def Tm65 : Con65 → Ty65 → Type 1
 := λ Γ A =>
   ∀ (Tm65  : Con65 → Ty65 → Type)
     (var   : ∀ Γ A     , Var65 Γ A → Tm65 Γ A)
     (lam   : ∀ Γ A B   , Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B))
     (app   : ∀ Γ A B   , Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B)
   , Tm65 Γ A

def var65 {Γ A} : Var65 Γ A → Tm65 Γ A
 := λ x Tm65 var65 lam app =>
     var65 _ _ x

def lam65 {Γ A B} : Tm65 (snoc65 Γ A) B → Tm65 Γ (arr65 A B)
 := λ t Tm65 var65 lam65 app =>
     lam65 _ _ _ (t Tm65 var65 lam65 app)

def app65 {Γ A B} : Tm65 Γ (arr65 A B) → Tm65 Γ A → Tm65 Γ B
 := λ t u Tm65 var65 lam65 app65 =>
     app65 _ _ _
         (t Tm65 var65 lam65 app65)
         (u Tm65 var65 lam65 app65)

def v065 {Γ A} : Tm65 (snoc65 Γ A) A
 := var65 vz65

def v165 {Γ A B} : Tm65 (snoc65 (snoc65 Γ A) B) A
 := var65 (vs65 vz65)

def v265 {Γ A B C} : Tm65 (snoc65 (snoc65 (snoc65 Γ A) B) C) A
 := var65 (vs65 (vs65 vz65))

def v365 {Γ A B C D} : Tm65 (snoc65 (snoc65 (snoc65 (snoc65 Γ A) B) C) D) A
 := var65 (vs65 (vs65 (vs65 vz65)))

def v465 {Γ A B C D E} : Tm65 (snoc65 (snoc65 (snoc65 (snoc65 (snoc65 Γ A) B) C) D) E) A
 := var65 (vs65 (vs65 (vs65 (vs65 vz65))))

def test65 {Γ A} : Tm65 Γ (arr65 (arr65 A A) (arr65 A A))
 := lam65 (lam65 (app65 v165 (app65 v165 (app65 v165 (app65 v165 (app65 v165 (app65 v165 v065)))))))


def Ty66 : Type 1
 := ∀ (Ty66 : Type)
      (ι   : Ty66)
      (arr : Ty66 → Ty66 → Ty66)
    , Ty66

def ι66 : Ty66 := λ _ ι66 _ => ι66

def arr66 : Ty66 → Ty66 → Ty66
 := λ A B Ty66 ι66 arr66 =>
     arr66 (A Ty66 ι66 arr66) (B Ty66 ι66 arr66)

def Con66 : Type 1
 := ∀ (Con66  : Type)
      (nil  : Con66)
      (snoc : Con66 → Ty66 → Con66)
    , Con66

def nil66 : Con66
 := λ Con66 nil66 snoc => nil66

def snoc66 : Con66 → Ty66 → Con66
 := λ Γ A Con66 nil66 snoc66 => snoc66 (Γ Con66 nil66 snoc66) A

def Var66 : Con66 → Ty66 → Type 1
 := λ Γ A =>
   ∀ (Var66 : Con66 → Ty66 → Type)
     (vz  : ∀ Γ A, Var66 (snoc66 Γ A) A)
     (vs  : ∀ Γ B A, Var66 Γ A → Var66 (snoc66 Γ B) A)
   , Var66 Γ A

def vz66 {Γ A} : Var66 (snoc66 Γ A) A
 := λ Var66 vz66 vs => vz66 _ _

def vs66 {Γ B A} : Var66 Γ A → Var66 (snoc66 Γ B) A
 := λ x Var66 vz66 vs66 => vs66 _ _ _ (x Var66 vz66 vs66)

def Tm66 : Con66 → Ty66 → Type 1
 := λ Γ A =>
   ∀ (Tm66  : Con66 → Ty66 → Type)
     (var   : ∀ Γ A     , Var66 Γ A → Tm66 Γ A)
     (lam   : ∀ Γ A B   , Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B))
     (app   : ∀ Γ A B   , Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B)
   , Tm66 Γ A

def var66 {Γ A} : Var66 Γ A → Tm66 Γ A
 := λ x Tm66 var66 lam app =>
     var66 _ _ x

def lam66 {Γ A B} : Tm66 (snoc66 Γ A) B → Tm66 Γ (arr66 A B)
 := λ t Tm66 var66 lam66 app =>
     lam66 _ _ _ (t Tm66 var66 lam66 app)

def app66 {Γ A B} : Tm66 Γ (arr66 A B) → Tm66 Γ A → Tm66 Γ B
 := λ t u Tm66 var66 lam66 app66 =>
     app66 _ _ _
         (t Tm66 var66 lam66 app66)
         (u Tm66 var66 lam66 app66)

def v066 {Γ A} : Tm66 (snoc66 Γ A) A
 := var66 vz66

def v166 {Γ A B} : Tm66 (snoc66 (snoc66 Γ A) B) A
 := var66 (vs66 vz66)

def v266 {Γ A B C} : Tm66 (snoc66 (snoc66 (snoc66 Γ A) B) C) A
 := var66 (vs66 (vs66 vz66))

def v366 {Γ A B C D} : Tm66 (snoc66 (snoc66 (snoc66 (snoc66 Γ A) B) C) D) A
 := var66 (vs66 (vs66 (vs66 vz66)))

def v466 {Γ A B C D E} : Tm66 (snoc66 (snoc66 (snoc66 (snoc66 (snoc66 Γ A) B) C) D) E) A
 := var66 (vs66 (vs66 (vs66 (vs66 vz66))))

def test66 {Γ A} : Tm66 Γ (arr66 (arr66 A A) (arr66 A A))
 := lam66 (lam66 (app66 v166 (app66 v166 (app66 v166 (app66 v166 (app66 v166 (app66 v166 v066)))))))


def Ty67 : Type 1
 := ∀ (Ty67 : Type)
      (ι   : Ty67)
      (arr : Ty67 → Ty67 → Ty67)
    , Ty67

def ι67 : Ty67 := λ _ ι67 _ => ι67

def arr67 : Ty67 → Ty67 → Ty67
 := λ A B Ty67 ι67 arr67 =>
     arr67 (A Ty67 ι67 arr67) (B Ty67 ι67 arr67)

def Con67 : Type 1
 := ∀ (Con67  : Type)
      (nil  : Con67)
      (snoc : Con67 → Ty67 → Con67)
    , Con67

def nil67 : Con67
 := λ Con67 nil67 snoc => nil67

def snoc67 : Con67 → Ty67 → Con67
 := λ Γ A Con67 nil67 snoc67 => snoc67 (Γ Con67 nil67 snoc67) A

def Var67 : Con67 → Ty67 → Type 1
 := λ Γ A =>
   ∀ (Var67 : Con67 → Ty67 → Type)
     (vz  : ∀ Γ A, Var67 (snoc67 Γ A) A)
     (vs  : ∀ Γ B A, Var67 Γ A → Var67 (snoc67 Γ B) A)
   , Var67 Γ A

def vz67 {Γ A} : Var67 (snoc67 Γ A) A
 := λ Var67 vz67 vs => vz67 _ _

def vs67 {Γ B A} : Var67 Γ A → Var67 (snoc67 Γ B) A
 := λ x Var67 vz67 vs67 => vs67 _ _ _ (x Var67 vz67 vs67)

def Tm67 : Con67 → Ty67 → Type 1
 := λ Γ A =>
   ∀ (Tm67  : Con67 → Ty67 → Type)
     (var   : ∀ Γ A     , Var67 Γ A → Tm67 Γ A)
     (lam   : ∀ Γ A B   , Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B))
     (app   : ∀ Γ A B   , Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B)
   , Tm67 Γ A

def var67 {Γ A} : Var67 Γ A → Tm67 Γ A
 := λ x Tm67 var67 lam app =>
     var67 _ _ x

def lam67 {Γ A B} : Tm67 (snoc67 Γ A) B → Tm67 Γ (arr67 A B)
 := λ t Tm67 var67 lam67 app =>
     lam67 _ _ _ (t Tm67 var67 lam67 app)

def app67 {Γ A B} : Tm67 Γ (arr67 A B) → Tm67 Γ A → Tm67 Γ B
 := λ t u Tm67 var67 lam67 app67 =>
     app67 _ _ _
         (t Tm67 var67 lam67 app67)
         (u Tm67 var67 lam67 app67)

def v067 {Γ A} : Tm67 (snoc67 Γ A) A
 := var67 vz67

def v167 {Γ A B} : Tm67 (snoc67 (snoc67 Γ A) B) A
 := var67 (vs67 vz67)

def v267 {Γ A B C} : Tm67 (snoc67 (snoc67 (snoc67 Γ A) B) C) A
 := var67 (vs67 (vs67 vz67))

def v367 {Γ A B C D} : Tm67 (snoc67 (snoc67 (snoc67 (snoc67 Γ A) B) C) D) A
 := var67 (vs67 (vs67 (vs67 vz67)))

def v467 {Γ A B C D E} : Tm67 (snoc67 (snoc67 (snoc67 (snoc67 (snoc67 Γ A) B) C) D) E) A
 := var67 (vs67 (vs67 (vs67 (vs67 vz67))))

def test67 {Γ A} : Tm67 Γ (arr67 (arr67 A A) (arr67 A A))
 := lam67 (lam67 (app67 v167 (app67 v167 (app67 v167 (app67 v167 (app67 v167 (app67 v167 v067)))))))


def Ty68 : Type 1
 := ∀ (Ty68 : Type)
      (ι   : Ty68)
      (arr : Ty68 → Ty68 → Ty68)
    , Ty68

def ι68 : Ty68 := λ _ ι68 _ => ι68

def arr68 : Ty68 → Ty68 → Ty68
 := λ A B Ty68 ι68 arr68 =>
     arr68 (A Ty68 ι68 arr68) (B Ty68 ι68 arr68)

def Con68 : Type 1
 := ∀ (Con68  : Type)
      (nil  : Con68)
      (snoc : Con68 → Ty68 → Con68)
    , Con68

def nil68 : Con68
 := λ Con68 nil68 snoc => nil68

def snoc68 : Con68 → Ty68 → Con68
 := λ Γ A Con68 nil68 snoc68 => snoc68 (Γ Con68 nil68 snoc68) A

def Var68 : Con68 → Ty68 → Type 1
 := λ Γ A =>
   ∀ (Var68 : Con68 → Ty68 → Type)
     (vz  : ∀ Γ A, Var68 (snoc68 Γ A) A)
     (vs  : ∀ Γ B A, Var68 Γ A → Var68 (snoc68 Γ B) A)
   , Var68 Γ A

def vz68 {Γ A} : Var68 (snoc68 Γ A) A
 := λ Var68 vz68 vs => vz68 _ _

def vs68 {Γ B A} : Var68 Γ A → Var68 (snoc68 Γ B) A
 := λ x Var68 vz68 vs68 => vs68 _ _ _ (x Var68 vz68 vs68)

def Tm68 : Con68 → Ty68 → Type 1
 := λ Γ A =>
   ∀ (Tm68  : Con68 → Ty68 → Type)
     (var   : ∀ Γ A     , Var68 Γ A → Tm68 Γ A)
     (lam   : ∀ Γ A B   , Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B))
     (app   : ∀ Γ A B   , Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B)
   , Tm68 Γ A

def var68 {Γ A} : Var68 Γ A → Tm68 Γ A
 := λ x Tm68 var68 lam app =>
     var68 _ _ x

def lam68 {Γ A B} : Tm68 (snoc68 Γ A) B → Tm68 Γ (arr68 A B)
 := λ t Tm68 var68 lam68 app =>
     lam68 _ _ _ (t Tm68 var68 lam68 app)

def app68 {Γ A B} : Tm68 Γ (arr68 A B) → Tm68 Γ A → Tm68 Γ B
 := λ t u Tm68 var68 lam68 app68 =>
     app68 _ _ _
         (t Tm68 var68 lam68 app68)
         (u Tm68 var68 lam68 app68)

def v068 {Γ A} : Tm68 (snoc68 Γ A) A
 := var68 vz68

def v168 {Γ A B} : Tm68 (snoc68 (snoc68 Γ A) B) A
 := var68 (vs68 vz68)

def v268 {Γ A B C} : Tm68 (snoc68 (snoc68 (snoc68 Γ A) B) C) A
 := var68 (vs68 (vs68 vz68))

def v368 {Γ A B C D} : Tm68 (snoc68 (snoc68 (snoc68 (snoc68 Γ A) B) C) D) A
 := var68 (vs68 (vs68 (vs68 vz68)))

def v468 {Γ A B C D E} : Tm68 (snoc68 (snoc68 (snoc68 (snoc68 (snoc68 Γ A) B) C) D) E) A
 := var68 (vs68 (vs68 (vs68 (vs68 vz68))))

def test68 {Γ A} : Tm68 Γ (arr68 (arr68 A A) (arr68 A A))
 := lam68 (lam68 (app68 v168 (app68 v168 (app68 v168 (app68 v168 (app68 v168 (app68 v168 v068)))))))


def Ty69 : Type 1
 := ∀ (Ty69 : Type)
      (ι   : Ty69)
      (arr : Ty69 → Ty69 → Ty69)
    , Ty69

def ι69 : Ty69 := λ _ ι69 _ => ι69

def arr69 : Ty69 → Ty69 → Ty69
 := λ A B Ty69 ι69 arr69 =>
     arr69 (A Ty69 ι69 arr69) (B Ty69 ι69 arr69)

def Con69 : Type 1
 := ∀ (Con69  : Type)
      (nil  : Con69)
      (snoc : Con69 → Ty69 → Con69)
    , Con69

def nil69 : Con69
 := λ Con69 nil69 snoc => nil69

def snoc69 : Con69 → Ty69 → Con69
 := λ Γ A Con69 nil69 snoc69 => snoc69 (Γ Con69 nil69 snoc69) A

def Var69 : Con69 → Ty69 → Type 1
 := λ Γ A =>
   ∀ (Var69 : Con69 → Ty69 → Type)
     (vz  : ∀ Γ A, Var69 (snoc69 Γ A) A)
     (vs  : ∀ Γ B A, Var69 Γ A → Var69 (snoc69 Γ B) A)
   , Var69 Γ A

def vz69 {Γ A} : Var69 (snoc69 Γ A) A
 := λ Var69 vz69 vs => vz69 _ _

def vs69 {Γ B A} : Var69 Γ A → Var69 (snoc69 Γ B) A
 := λ x Var69 vz69 vs69 => vs69 _ _ _ (x Var69 vz69 vs69)

def Tm69 : Con69 → Ty69 → Type 1
 := λ Γ A =>
   ∀ (Tm69  : Con69 → Ty69 → Type)
     (var   : ∀ Γ A     , Var69 Γ A → Tm69 Γ A)
     (lam   : ∀ Γ A B   , Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B))
     (app   : ∀ Γ A B   , Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B)
   , Tm69 Γ A

def var69 {Γ A} : Var69 Γ A → Tm69 Γ A
 := λ x Tm69 var69 lam app =>
     var69 _ _ x

def lam69 {Γ A B} : Tm69 (snoc69 Γ A) B → Tm69 Γ (arr69 A B)
 := λ t Tm69 var69 lam69 app =>
     lam69 _ _ _ (t Tm69 var69 lam69 app)

def app69 {Γ A B} : Tm69 Γ (arr69 A B) → Tm69 Γ A → Tm69 Γ B
 := λ t u Tm69 var69 lam69 app69 =>
     app69 _ _ _
         (t Tm69 var69 lam69 app69)
         (u Tm69 var69 lam69 app69)

def v069 {Γ A} : Tm69 (snoc69 Γ A) A
 := var69 vz69

def v169 {Γ A B} : Tm69 (snoc69 (snoc69 Γ A) B) A
 := var69 (vs69 vz69)

def v269 {Γ A B C} : Tm69 (snoc69 (snoc69 (snoc69 Γ A) B) C) A
 := var69 (vs69 (vs69 vz69))

def v369 {Γ A B C D} : Tm69 (snoc69 (snoc69 (snoc69 (snoc69 Γ A) B) C) D) A
 := var69 (vs69 (vs69 (vs69 vz69)))

def v469 {Γ A B C D E} : Tm69 (snoc69 (snoc69 (snoc69 (snoc69 (snoc69 Γ A) B) C) D) E) A
 := var69 (vs69 (vs69 (vs69 (vs69 vz69))))

def test69 {Γ A} : Tm69 Γ (arr69 (arr69 A A) (arr69 A A))
 := lam69 (lam69 (app69 v169 (app69 v169 (app69 v169 (app69 v169 (app69 v169 (app69 v169 v069)))))))


def Ty70 : Type 1
 := ∀ (Ty70 : Type)
      (ι   : Ty70)
      (arr : Ty70 → Ty70 → Ty70)
    , Ty70

def ι70 : Ty70 := λ _ ι70 _ => ι70

def arr70 : Ty70 → Ty70 → Ty70
 := λ A B Ty70 ι70 arr70 =>
     arr70 (A Ty70 ι70 arr70) (B Ty70 ι70 arr70)

def Con70 : Type 1
 := ∀ (Con70  : Type)
      (nil  : Con70)
      (snoc : Con70 → Ty70 → Con70)
    , Con70

def nil70 : Con70
 := λ Con70 nil70 snoc => nil70

def snoc70 : Con70 → Ty70 → Con70
 := λ Γ A Con70 nil70 snoc70 => snoc70 (Γ Con70 nil70 snoc70) A

def Var70 : Con70 → Ty70 → Type 1
 := λ Γ A =>
   ∀ (Var70 : Con70 → Ty70 → Type)
     (vz  : ∀ Γ A, Var70 (snoc70 Γ A) A)
     (vs  : ∀ Γ B A, Var70 Γ A → Var70 (snoc70 Γ B) A)
   , Var70 Γ A

def vz70 {Γ A} : Var70 (snoc70 Γ A) A
 := λ Var70 vz70 vs => vz70 _ _

def vs70 {Γ B A} : Var70 Γ A → Var70 (snoc70 Γ B) A
 := λ x Var70 vz70 vs70 => vs70 _ _ _ (x Var70 vz70 vs70)

def Tm70 : Con70 → Ty70 → Type 1
 := λ Γ A =>
   ∀ (Tm70  : Con70 → Ty70 → Type)
     (var   : ∀ Γ A     , Var70 Γ A → Tm70 Γ A)
     (lam   : ∀ Γ A B   , Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B))
     (app   : ∀ Γ A B   , Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B)
   , Tm70 Γ A

def var70 {Γ A} : Var70 Γ A → Tm70 Γ A
 := λ x Tm70 var70 lam app =>
     var70 _ _ x

def lam70 {Γ A B} : Tm70 (snoc70 Γ A) B → Tm70 Γ (arr70 A B)
 := λ t Tm70 var70 lam70 app =>
     lam70 _ _ _ (t Tm70 var70 lam70 app)

def app70 {Γ A B} : Tm70 Γ (arr70 A B) → Tm70 Γ A → Tm70 Γ B
 := λ t u Tm70 var70 lam70 app70 =>
     app70 _ _ _
         (t Tm70 var70 lam70 app70)
         (u Tm70 var70 lam70 app70)

def v070 {Γ A} : Tm70 (snoc70 Γ A) A
 := var70 vz70

def v170 {Γ A B} : Tm70 (snoc70 (snoc70 Γ A) B) A
 := var70 (vs70 vz70)

def v270 {Γ A B C} : Tm70 (snoc70 (snoc70 (snoc70 Γ A) B) C) A
 := var70 (vs70 (vs70 vz70))

def v370 {Γ A B C D} : Tm70 (snoc70 (snoc70 (snoc70 (snoc70 Γ A) B) C) D) A
 := var70 (vs70 (vs70 (vs70 vz70)))

def v470 {Γ A B C D E} : Tm70 (snoc70 (snoc70 (snoc70 (snoc70 (snoc70 Γ A) B) C) D) E) A
 := var70 (vs70 (vs70 (vs70 (vs70 vz70))))

def test70 {Γ A} : Tm70 Γ (arr70 (arr70 A A) (arr70 A A))
 := lam70 (lam70 (app70 v170 (app70 v170 (app70 v170 (app70 v170 (app70 v170 (app70 v170 v070)))))))


def Ty71 : Type 1
 := ∀ (Ty71 : Type)
      (ι   : Ty71)
      (arr : Ty71 → Ty71 → Ty71)
    , Ty71

def ι71 : Ty71 := λ _ ι71 _ => ι71

def arr71 : Ty71 → Ty71 → Ty71
 := λ A B Ty71 ι71 arr71 =>
     arr71 (A Ty71 ι71 arr71) (B Ty71 ι71 arr71)

def Con71 : Type 1
 := ∀ (Con71  : Type)
      (nil  : Con71)
      (snoc : Con71 → Ty71 → Con71)
    , Con71

def nil71 : Con71
 := λ Con71 nil71 snoc => nil71

def snoc71 : Con71 → Ty71 → Con71
 := λ Γ A Con71 nil71 snoc71 => snoc71 (Γ Con71 nil71 snoc71) A

def Var71 : Con71 → Ty71 → Type 1
 := λ Γ A =>
   ∀ (Var71 : Con71 → Ty71 → Type)
     (vz  : ∀ Γ A, Var71 (snoc71 Γ A) A)
     (vs  : ∀ Γ B A, Var71 Γ A → Var71 (snoc71 Γ B) A)
   , Var71 Γ A

def vz71 {Γ A} : Var71 (snoc71 Γ A) A
 := λ Var71 vz71 vs => vz71 _ _

def vs71 {Γ B A} : Var71 Γ A → Var71 (snoc71 Γ B) A
 := λ x Var71 vz71 vs71 => vs71 _ _ _ (x Var71 vz71 vs71)

def Tm71 : Con71 → Ty71 → Type 1
 := λ Γ A =>
   ∀ (Tm71  : Con71 → Ty71 → Type)
     (var   : ∀ Γ A     , Var71 Γ A → Tm71 Γ A)
     (lam   : ∀ Γ A B   , Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B))
     (app   : ∀ Γ A B   , Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B)
   , Tm71 Γ A

def var71 {Γ A} : Var71 Γ A → Tm71 Γ A
 := λ x Tm71 var71 lam app =>
     var71 _ _ x

def lam71 {Γ A B} : Tm71 (snoc71 Γ A) B → Tm71 Γ (arr71 A B)
 := λ t Tm71 var71 lam71 app =>
     lam71 _ _ _ (t Tm71 var71 lam71 app)

def app71 {Γ A B} : Tm71 Γ (arr71 A B) → Tm71 Γ A → Tm71 Γ B
 := λ t u Tm71 var71 lam71 app71 =>
     app71 _ _ _
         (t Tm71 var71 lam71 app71)
         (u Tm71 var71 lam71 app71)

def v071 {Γ A} : Tm71 (snoc71 Γ A) A
 := var71 vz71

def v171 {Γ A B} : Tm71 (snoc71 (snoc71 Γ A) B) A
 := var71 (vs71 vz71)

def v271 {Γ A B C} : Tm71 (snoc71 (snoc71 (snoc71 Γ A) B) C) A
 := var71 (vs71 (vs71 vz71))

def v371 {Γ A B C D} : Tm71 (snoc71 (snoc71 (snoc71 (snoc71 Γ A) B) C) D) A
 := var71 (vs71 (vs71 (vs71 vz71)))

def v471 {Γ A B C D E} : Tm71 (snoc71 (snoc71 (snoc71 (snoc71 (snoc71 Γ A) B) C) D) E) A
 := var71 (vs71 (vs71 (vs71 (vs71 vz71))))

def test71 {Γ A} : Tm71 Γ (arr71 (arr71 A A) (arr71 A A))
 := lam71 (lam71 (app71 v171 (app71 v171 (app71 v171 (app71 v171 (app71 v171 (app71 v171 v071)))))))


def Ty72 : Type 1
 := ∀ (Ty72 : Type)
      (ι   : Ty72)
      (arr : Ty72 → Ty72 → Ty72)
    , Ty72

def ι72 : Ty72 := λ _ ι72 _ => ι72

def arr72 : Ty72 → Ty72 → Ty72
 := λ A B Ty72 ι72 arr72 =>
     arr72 (A Ty72 ι72 arr72) (B Ty72 ι72 arr72)

def Con72 : Type 1
 := ∀ (Con72  : Type)
      (nil  : Con72)
      (snoc : Con72 → Ty72 → Con72)
    , Con72

def nil72 : Con72
 := λ Con72 nil72 snoc => nil72

def snoc72 : Con72 → Ty72 → Con72
 := λ Γ A Con72 nil72 snoc72 => snoc72 (Γ Con72 nil72 snoc72) A

def Var72 : Con72 → Ty72 → Type 1
 := λ Γ A =>
   ∀ (Var72 : Con72 → Ty72 → Type)
     (vz  : ∀ Γ A, Var72 (snoc72 Γ A) A)
     (vs  : ∀ Γ B A, Var72 Γ A → Var72 (snoc72 Γ B) A)
   , Var72 Γ A

def vz72 {Γ A} : Var72 (snoc72 Γ A) A
 := λ Var72 vz72 vs => vz72 _ _

def vs72 {Γ B A} : Var72 Γ A → Var72 (snoc72 Γ B) A
 := λ x Var72 vz72 vs72 => vs72 _ _ _ (x Var72 vz72 vs72)

def Tm72 : Con72 → Ty72 → Type 1
 := λ Γ A =>
   ∀ (Tm72  : Con72 → Ty72 → Type)
     (var   : ∀ Γ A     , Var72 Γ A → Tm72 Γ A)
     (lam   : ∀ Γ A B   , Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B))
     (app   : ∀ Γ A B   , Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B)
   , Tm72 Γ A

def var72 {Γ A} : Var72 Γ A → Tm72 Γ A
 := λ x Tm72 var72 lam app =>
     var72 _ _ x

def lam72 {Γ A B} : Tm72 (snoc72 Γ A) B → Tm72 Γ (arr72 A B)
 := λ t Tm72 var72 lam72 app =>
     lam72 _ _ _ (t Tm72 var72 lam72 app)

def app72 {Γ A B} : Tm72 Γ (arr72 A B) → Tm72 Γ A → Tm72 Γ B
 := λ t u Tm72 var72 lam72 app72 =>
     app72 _ _ _
         (t Tm72 var72 lam72 app72)
         (u Tm72 var72 lam72 app72)

def v072 {Γ A} : Tm72 (snoc72 Γ A) A
 := var72 vz72

def v172 {Γ A B} : Tm72 (snoc72 (snoc72 Γ A) B) A
 := var72 (vs72 vz72)

def v272 {Γ A B C} : Tm72 (snoc72 (snoc72 (snoc72 Γ A) B) C) A
 := var72 (vs72 (vs72 vz72))

def v372 {Γ A B C D} : Tm72 (snoc72 (snoc72 (snoc72 (snoc72 Γ A) B) C) D) A
 := var72 (vs72 (vs72 (vs72 vz72)))

def v472 {Γ A B C D E} : Tm72 (snoc72 (snoc72 (snoc72 (snoc72 (snoc72 Γ A) B) C) D) E) A
 := var72 (vs72 (vs72 (vs72 (vs72 vz72))))

def test72 {Γ A} : Tm72 Γ (arr72 (arr72 A A) (arr72 A A))
 := lam72 (lam72 (app72 v172 (app72 v172 (app72 v172 (app72 v172 (app72 v172 (app72 v172 v072)))))))


def Ty73 : Type 1
 := ∀ (Ty73 : Type)
      (ι   : Ty73)
      (arr : Ty73 → Ty73 → Ty73)
    , Ty73

def ι73 : Ty73 := λ _ ι73 _ => ι73

def arr73 : Ty73 → Ty73 → Ty73
 := λ A B Ty73 ι73 arr73 =>
     arr73 (A Ty73 ι73 arr73) (B Ty73 ι73 arr73)

def Con73 : Type 1
 := ∀ (Con73  : Type)
      (nil  : Con73)
      (snoc : Con73 → Ty73 → Con73)
    , Con73

def nil73 : Con73
 := λ Con73 nil73 snoc => nil73

def snoc73 : Con73 → Ty73 → Con73
 := λ Γ A Con73 nil73 snoc73 => snoc73 (Γ Con73 nil73 snoc73) A

def Var73 : Con73 → Ty73 → Type 1
 := λ Γ A =>
   ∀ (Var73 : Con73 → Ty73 → Type)
     (vz  : ∀ Γ A, Var73 (snoc73 Γ A) A)
     (vs  : ∀ Γ B A, Var73 Γ A → Var73 (snoc73 Γ B) A)
   , Var73 Γ A

def vz73 {Γ A} : Var73 (snoc73 Γ A) A
 := λ Var73 vz73 vs => vz73 _ _

def vs73 {Γ B A} : Var73 Γ A → Var73 (snoc73 Γ B) A
 := λ x Var73 vz73 vs73 => vs73 _ _ _ (x Var73 vz73 vs73)

def Tm73 : Con73 → Ty73 → Type 1
 := λ Γ A =>
   ∀ (Tm73  : Con73 → Ty73 → Type)
     (var   : ∀ Γ A     , Var73 Γ A → Tm73 Γ A)
     (lam   : ∀ Γ A B   , Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B))
     (app   : ∀ Γ A B   , Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B)
   , Tm73 Γ A

def var73 {Γ A} : Var73 Γ A → Tm73 Γ A
 := λ x Tm73 var73 lam app =>
     var73 _ _ x

def lam73 {Γ A B} : Tm73 (snoc73 Γ A) B → Tm73 Γ (arr73 A B)
 := λ t Tm73 var73 lam73 app =>
     lam73 _ _ _ (t Tm73 var73 lam73 app)

def app73 {Γ A B} : Tm73 Γ (arr73 A B) → Tm73 Γ A → Tm73 Γ B
 := λ t u Tm73 var73 lam73 app73 =>
     app73 _ _ _
         (t Tm73 var73 lam73 app73)
         (u Tm73 var73 lam73 app73)

def v073 {Γ A} : Tm73 (snoc73 Γ A) A
 := var73 vz73

def v173 {Γ A B} : Tm73 (snoc73 (snoc73 Γ A) B) A
 := var73 (vs73 vz73)

def v273 {Γ A B C} : Tm73 (snoc73 (snoc73 (snoc73 Γ A) B) C) A
 := var73 (vs73 (vs73 vz73))

def v373 {Γ A B C D} : Tm73 (snoc73 (snoc73 (snoc73 (snoc73 Γ A) B) C) D) A
 := var73 (vs73 (vs73 (vs73 vz73)))

def v473 {Γ A B C D E} : Tm73 (snoc73 (snoc73 (snoc73 (snoc73 (snoc73 Γ A) B) C) D) E) A
 := var73 (vs73 (vs73 (vs73 (vs73 vz73))))

def test73 {Γ A} : Tm73 Γ (arr73 (arr73 A A) (arr73 A A))
 := lam73 (lam73 (app73 v173 (app73 v173 (app73 v173 (app73 v173 (app73 v173 (app73 v173 v073)))))))


def Ty74 : Type 1
 := ∀ (Ty74 : Type)
      (ι   : Ty74)
      (arr : Ty74 → Ty74 → Ty74)
    , Ty74

def ι74 : Ty74 := λ _ ι74 _ => ι74

def arr74 : Ty74 → Ty74 → Ty74
 := λ A B Ty74 ι74 arr74 =>
     arr74 (A Ty74 ι74 arr74) (B Ty74 ι74 arr74)

def Con74 : Type 1
 := ∀ (Con74  : Type)
      (nil  : Con74)
      (snoc : Con74 → Ty74 → Con74)
    , Con74

def nil74 : Con74
 := λ Con74 nil74 snoc => nil74

def snoc74 : Con74 → Ty74 → Con74
 := λ Γ A Con74 nil74 snoc74 => snoc74 (Γ Con74 nil74 snoc74) A

def Var74 : Con74 → Ty74 → Type 1
 := λ Γ A =>
   ∀ (Var74 : Con74 → Ty74 → Type)
     (vz  : ∀ Γ A, Var74 (snoc74 Γ A) A)
     (vs  : ∀ Γ B A, Var74 Γ A → Var74 (snoc74 Γ B) A)
   , Var74 Γ A

def vz74 {Γ A} : Var74 (snoc74 Γ A) A
 := λ Var74 vz74 vs => vz74 _ _

def vs74 {Γ B A} : Var74 Γ A → Var74 (snoc74 Γ B) A
 := λ x Var74 vz74 vs74 => vs74 _ _ _ (x Var74 vz74 vs74)

def Tm74 : Con74 → Ty74 → Type 1
 := λ Γ A =>
   ∀ (Tm74  : Con74 → Ty74 → Type)
     (var   : ∀ Γ A     , Var74 Γ A → Tm74 Γ A)
     (lam   : ∀ Γ A B   , Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B))
     (app   : ∀ Γ A B   , Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B)
   , Tm74 Γ A

def var74 {Γ A} : Var74 Γ A → Tm74 Γ A
 := λ x Tm74 var74 lam app =>
     var74 _ _ x

def lam74 {Γ A B} : Tm74 (snoc74 Γ A) B → Tm74 Γ (arr74 A B)
 := λ t Tm74 var74 lam74 app =>
     lam74 _ _ _ (t Tm74 var74 lam74 app)

def app74 {Γ A B} : Tm74 Γ (arr74 A B) → Tm74 Γ A → Tm74 Γ B
 := λ t u Tm74 var74 lam74 app74 =>
     app74 _ _ _
         (t Tm74 var74 lam74 app74)
         (u Tm74 var74 lam74 app74)

def v074 {Γ A} : Tm74 (snoc74 Γ A) A
 := var74 vz74

def v174 {Γ A B} : Tm74 (snoc74 (snoc74 Γ A) B) A
 := var74 (vs74 vz74)

def v274 {Γ A B C} : Tm74 (snoc74 (snoc74 (snoc74 Γ A) B) C) A
 := var74 (vs74 (vs74 vz74))

def v374 {Γ A B C D} : Tm74 (snoc74 (snoc74 (snoc74 (snoc74 Γ A) B) C) D) A
 := var74 (vs74 (vs74 (vs74 vz74)))

def v474 {Γ A B C D E} : Tm74 (snoc74 (snoc74 (snoc74 (snoc74 (snoc74 Γ A) B) C) D) E) A
 := var74 (vs74 (vs74 (vs74 (vs74 vz74))))

def test74 {Γ A} : Tm74 Γ (arr74 (arr74 A A) (arr74 A A))
 := lam74 (lam74 (app74 v174 (app74 v174 (app74 v174 (app74 v174 (app74 v174 (app74 v174 v074)))))))


def Ty75 : Type 1
 := ∀ (Ty75 : Type)
      (ι   : Ty75)
      (arr : Ty75 → Ty75 → Ty75)
    , Ty75

def ι75 : Ty75 := λ _ ι75 _ => ι75

def arr75 : Ty75 → Ty75 → Ty75
 := λ A B Ty75 ι75 arr75 =>
     arr75 (A Ty75 ι75 arr75) (B Ty75 ι75 arr75)

def Con75 : Type 1
 := ∀ (Con75  : Type)
      (nil  : Con75)
      (snoc : Con75 → Ty75 → Con75)
    , Con75

def nil75 : Con75
 := λ Con75 nil75 snoc => nil75

def snoc75 : Con75 → Ty75 → Con75
 := λ Γ A Con75 nil75 snoc75 => snoc75 (Γ Con75 nil75 snoc75) A

def Var75 : Con75 → Ty75 → Type 1
 := λ Γ A =>
   ∀ (Var75 : Con75 → Ty75 → Type)
     (vz  : ∀ Γ A, Var75 (snoc75 Γ A) A)
     (vs  : ∀ Γ B A, Var75 Γ A → Var75 (snoc75 Γ B) A)
   , Var75 Γ A

def vz75 {Γ A} : Var75 (snoc75 Γ A) A
 := λ Var75 vz75 vs => vz75 _ _

def vs75 {Γ B A} : Var75 Γ A → Var75 (snoc75 Γ B) A
 := λ x Var75 vz75 vs75 => vs75 _ _ _ (x Var75 vz75 vs75)

def Tm75 : Con75 → Ty75 → Type 1
 := λ Γ A =>
   ∀ (Tm75  : Con75 → Ty75 → Type)
     (var   : ∀ Γ A     , Var75 Γ A → Tm75 Γ A)
     (lam   : ∀ Γ A B   , Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B))
     (app   : ∀ Γ A B   , Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B)
   , Tm75 Γ A

def var75 {Γ A} : Var75 Γ A → Tm75 Γ A
 := λ x Tm75 var75 lam app =>
     var75 _ _ x

def lam75 {Γ A B} : Tm75 (snoc75 Γ A) B → Tm75 Γ (arr75 A B)
 := λ t Tm75 var75 lam75 app =>
     lam75 _ _ _ (t Tm75 var75 lam75 app)

def app75 {Γ A B} : Tm75 Γ (arr75 A B) → Tm75 Γ A → Tm75 Γ B
 := λ t u Tm75 var75 lam75 app75 =>
     app75 _ _ _
         (t Tm75 var75 lam75 app75)
         (u Tm75 var75 lam75 app75)

def v075 {Γ A} : Tm75 (snoc75 Γ A) A
 := var75 vz75

def v175 {Γ A B} : Tm75 (snoc75 (snoc75 Γ A) B) A
 := var75 (vs75 vz75)

def v275 {Γ A B C} : Tm75 (snoc75 (snoc75 (snoc75 Γ A) B) C) A
 := var75 (vs75 (vs75 vz75))

def v375 {Γ A B C D} : Tm75 (snoc75 (snoc75 (snoc75 (snoc75 Γ A) B) C) D) A
 := var75 (vs75 (vs75 (vs75 vz75)))

def v475 {Γ A B C D E} : Tm75 (snoc75 (snoc75 (snoc75 (snoc75 (snoc75 Γ A) B) C) D) E) A
 := var75 (vs75 (vs75 (vs75 (vs75 vz75))))

def test75 {Γ A} : Tm75 Γ (arr75 (arr75 A A) (arr75 A A))
 := lam75 (lam75 (app75 v175 (app75 v175 (app75 v175 (app75 v175 (app75 v175 (app75 v175 v075)))))))


def Ty76 : Type 1
 := ∀ (Ty76 : Type)
      (ι   : Ty76)
      (arr : Ty76 → Ty76 → Ty76)
    , Ty76

def ι76 : Ty76 := λ _ ι76 _ => ι76

def arr76 : Ty76 → Ty76 → Ty76
 := λ A B Ty76 ι76 arr76 =>
     arr76 (A Ty76 ι76 arr76) (B Ty76 ι76 arr76)

def Con76 : Type 1
 := ∀ (Con76  : Type)
      (nil  : Con76)
      (snoc : Con76 → Ty76 → Con76)
    , Con76

def nil76 : Con76
 := λ Con76 nil76 snoc => nil76

def snoc76 : Con76 → Ty76 → Con76
 := λ Γ A Con76 nil76 snoc76 => snoc76 (Γ Con76 nil76 snoc76) A

def Var76 : Con76 → Ty76 → Type 1
 := λ Γ A =>
   ∀ (Var76 : Con76 → Ty76 → Type)
     (vz  : ∀ Γ A, Var76 (snoc76 Γ A) A)
     (vs  : ∀ Γ B A, Var76 Γ A → Var76 (snoc76 Γ B) A)
   , Var76 Γ A

def vz76 {Γ A} : Var76 (snoc76 Γ A) A
 := λ Var76 vz76 vs => vz76 _ _

def vs76 {Γ B A} : Var76 Γ A → Var76 (snoc76 Γ B) A
 := λ x Var76 vz76 vs76 => vs76 _ _ _ (x Var76 vz76 vs76)

def Tm76 : Con76 → Ty76 → Type 1
 := λ Γ A =>
   ∀ (Tm76  : Con76 → Ty76 → Type)
     (var   : ∀ Γ A     , Var76 Γ A → Tm76 Γ A)
     (lam   : ∀ Γ A B   , Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B))
     (app   : ∀ Γ A B   , Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B)
   , Tm76 Γ A

def var76 {Γ A} : Var76 Γ A → Tm76 Γ A
 := λ x Tm76 var76 lam app =>
     var76 _ _ x

def lam76 {Γ A B} : Tm76 (snoc76 Γ A) B → Tm76 Γ (arr76 A B)
 := λ t Tm76 var76 lam76 app =>
     lam76 _ _ _ (t Tm76 var76 lam76 app)

def app76 {Γ A B} : Tm76 Γ (arr76 A B) → Tm76 Γ A → Tm76 Γ B
 := λ t u Tm76 var76 lam76 app76 =>
     app76 _ _ _
         (t Tm76 var76 lam76 app76)
         (u Tm76 var76 lam76 app76)

def v076 {Γ A} : Tm76 (snoc76 Γ A) A
 := var76 vz76

def v176 {Γ A B} : Tm76 (snoc76 (snoc76 Γ A) B) A
 := var76 (vs76 vz76)

def v276 {Γ A B C} : Tm76 (snoc76 (snoc76 (snoc76 Γ A) B) C) A
 := var76 (vs76 (vs76 vz76))

def v376 {Γ A B C D} : Tm76 (snoc76 (snoc76 (snoc76 (snoc76 Γ A) B) C) D) A
 := var76 (vs76 (vs76 (vs76 vz76)))

def v476 {Γ A B C D E} : Tm76 (snoc76 (snoc76 (snoc76 (snoc76 (snoc76 Γ A) B) C) D) E) A
 := var76 (vs76 (vs76 (vs76 (vs76 vz76))))

def test76 {Γ A} : Tm76 Γ (arr76 (arr76 A A) (arr76 A A))
 := lam76 (lam76 (app76 v176 (app76 v176 (app76 v176 (app76 v176 (app76 v176 (app76 v176 v076)))))))


def Ty77 : Type 1
 := ∀ (Ty77 : Type)
      (ι   : Ty77)
      (arr : Ty77 → Ty77 → Ty77)
    , Ty77

def ι77 : Ty77 := λ _ ι77 _ => ι77

def arr77 : Ty77 → Ty77 → Ty77
 := λ A B Ty77 ι77 arr77 =>
     arr77 (A Ty77 ι77 arr77) (B Ty77 ι77 arr77)

def Con77 : Type 1
 := ∀ (Con77  : Type)
      (nil  : Con77)
      (snoc : Con77 → Ty77 → Con77)
    , Con77

def nil77 : Con77
 := λ Con77 nil77 snoc => nil77

def snoc77 : Con77 → Ty77 → Con77
 := λ Γ A Con77 nil77 snoc77 => snoc77 (Γ Con77 nil77 snoc77) A

def Var77 : Con77 → Ty77 → Type 1
 := λ Γ A =>
   ∀ (Var77 : Con77 → Ty77 → Type)
     (vz  : ∀ Γ A, Var77 (snoc77 Γ A) A)
     (vs  : ∀ Γ B A, Var77 Γ A → Var77 (snoc77 Γ B) A)
   , Var77 Γ A

def vz77 {Γ A} : Var77 (snoc77 Γ A) A
 := λ Var77 vz77 vs => vz77 _ _

def vs77 {Γ B A} : Var77 Γ A → Var77 (snoc77 Γ B) A
 := λ x Var77 vz77 vs77 => vs77 _ _ _ (x Var77 vz77 vs77)

def Tm77 : Con77 → Ty77 → Type 1
 := λ Γ A =>
   ∀ (Tm77  : Con77 → Ty77 → Type)
     (var   : ∀ Γ A     , Var77 Γ A → Tm77 Γ A)
     (lam   : ∀ Γ A B   , Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B))
     (app   : ∀ Γ A B   , Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B)
   , Tm77 Γ A

def var77 {Γ A} : Var77 Γ A → Tm77 Γ A
 := λ x Tm77 var77 lam app =>
     var77 _ _ x

def lam77 {Γ A B} : Tm77 (snoc77 Γ A) B → Tm77 Γ (arr77 A B)
 := λ t Tm77 var77 lam77 app =>
     lam77 _ _ _ (t Tm77 var77 lam77 app)

def app77 {Γ A B} : Tm77 Γ (arr77 A B) → Tm77 Γ A → Tm77 Γ B
 := λ t u Tm77 var77 lam77 app77 =>
     app77 _ _ _
         (t Tm77 var77 lam77 app77)
         (u Tm77 var77 lam77 app77)

def v077 {Γ A} : Tm77 (snoc77 Γ A) A
 := var77 vz77

def v177 {Γ A B} : Tm77 (snoc77 (snoc77 Γ A) B) A
 := var77 (vs77 vz77)

def v277 {Γ A B C} : Tm77 (snoc77 (snoc77 (snoc77 Γ A) B) C) A
 := var77 (vs77 (vs77 vz77))

def v377 {Γ A B C D} : Tm77 (snoc77 (snoc77 (snoc77 (snoc77 Γ A) B) C) D) A
 := var77 (vs77 (vs77 (vs77 vz77)))

def v477 {Γ A B C D E} : Tm77 (snoc77 (snoc77 (snoc77 (snoc77 (snoc77 Γ A) B) C) D) E) A
 := var77 (vs77 (vs77 (vs77 (vs77 vz77))))

def test77 {Γ A} : Tm77 Γ (arr77 (arr77 A A) (arr77 A A))
 := lam77 (lam77 (app77 v177 (app77 v177 (app77 v177 (app77 v177 (app77 v177 (app77 v177 v077)))))))


def Ty78 : Type 1
 := ∀ (Ty78 : Type)
      (ι   : Ty78)
      (arr : Ty78 → Ty78 → Ty78)
    , Ty78

def ι78 : Ty78 := λ _ ι78 _ => ι78

def arr78 : Ty78 → Ty78 → Ty78
 := λ A B Ty78 ι78 arr78 =>
     arr78 (A Ty78 ι78 arr78) (B Ty78 ι78 arr78)

def Con78 : Type 1
 := ∀ (Con78  : Type)
      (nil  : Con78)
      (snoc : Con78 → Ty78 → Con78)
    , Con78

def nil78 : Con78
 := λ Con78 nil78 snoc => nil78

def snoc78 : Con78 → Ty78 → Con78
 := λ Γ A Con78 nil78 snoc78 => snoc78 (Γ Con78 nil78 snoc78) A

def Var78 : Con78 → Ty78 → Type 1
 := λ Γ A =>
   ∀ (Var78 : Con78 → Ty78 → Type)
     (vz  : ∀ Γ A, Var78 (snoc78 Γ A) A)
     (vs  : ∀ Γ B A, Var78 Γ A → Var78 (snoc78 Γ B) A)
   , Var78 Γ A

def vz78 {Γ A} : Var78 (snoc78 Γ A) A
 := λ Var78 vz78 vs => vz78 _ _

def vs78 {Γ B A} : Var78 Γ A → Var78 (snoc78 Γ B) A
 := λ x Var78 vz78 vs78 => vs78 _ _ _ (x Var78 vz78 vs78)

def Tm78 : Con78 → Ty78 → Type 1
 := λ Γ A =>
   ∀ (Tm78  : Con78 → Ty78 → Type)
     (var   : ∀ Γ A     , Var78 Γ A → Tm78 Γ A)
     (lam   : ∀ Γ A B   , Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B))
     (app   : ∀ Γ A B   , Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B)
   , Tm78 Γ A

def var78 {Γ A} : Var78 Γ A → Tm78 Γ A
 := λ x Tm78 var78 lam app =>
     var78 _ _ x

def lam78 {Γ A B} : Tm78 (snoc78 Γ A) B → Tm78 Γ (arr78 A B)
 := λ t Tm78 var78 lam78 app =>
     lam78 _ _ _ (t Tm78 var78 lam78 app)

def app78 {Γ A B} : Tm78 Γ (arr78 A B) → Tm78 Γ A → Tm78 Γ B
 := λ t u Tm78 var78 lam78 app78 =>
     app78 _ _ _
         (t Tm78 var78 lam78 app78)
         (u Tm78 var78 lam78 app78)

def v078 {Γ A} : Tm78 (snoc78 Γ A) A
 := var78 vz78

def v178 {Γ A B} : Tm78 (snoc78 (snoc78 Γ A) B) A
 := var78 (vs78 vz78)

def v278 {Γ A B C} : Tm78 (snoc78 (snoc78 (snoc78 Γ A) B) C) A
 := var78 (vs78 (vs78 vz78))

def v378 {Γ A B C D} : Tm78 (snoc78 (snoc78 (snoc78 (snoc78 Γ A) B) C) D) A
 := var78 (vs78 (vs78 (vs78 vz78)))

def v478 {Γ A B C D E} : Tm78 (snoc78 (snoc78 (snoc78 (snoc78 (snoc78 Γ A) B) C) D) E) A
 := var78 (vs78 (vs78 (vs78 (vs78 vz78))))

def test78 {Γ A} : Tm78 Γ (arr78 (arr78 A A) (arr78 A A))
 := lam78 (lam78 (app78 v178 (app78 v178 (app78 v178 (app78 v178 (app78 v178 (app78 v178 v078)))))))


def Ty79 : Type 1
 := ∀ (Ty79 : Type)
      (ι   : Ty79)
      (arr : Ty79 → Ty79 → Ty79)
    , Ty79

def ι79 : Ty79 := λ _ ι79 _ => ι79

def arr79 : Ty79 → Ty79 → Ty79
 := λ A B Ty79 ι79 arr79 =>
     arr79 (A Ty79 ι79 arr79) (B Ty79 ι79 arr79)

def Con79 : Type 1
 := ∀ (Con79  : Type)
      (nil  : Con79)
      (snoc : Con79 → Ty79 → Con79)
    , Con79

def nil79 : Con79
 := λ Con79 nil79 snoc => nil79

def snoc79 : Con79 → Ty79 → Con79
 := λ Γ A Con79 nil79 snoc79 => snoc79 (Γ Con79 nil79 snoc79) A

def Var79 : Con79 → Ty79 → Type 1
 := λ Γ A =>
   ∀ (Var79 : Con79 → Ty79 → Type)
     (vz  : ∀ Γ A, Var79 (snoc79 Γ A) A)
     (vs  : ∀ Γ B A, Var79 Γ A → Var79 (snoc79 Γ B) A)
   , Var79 Γ A

def vz79 {Γ A} : Var79 (snoc79 Γ A) A
 := λ Var79 vz79 vs => vz79 _ _

def vs79 {Γ B A} : Var79 Γ A → Var79 (snoc79 Γ B) A
 := λ x Var79 vz79 vs79 => vs79 _ _ _ (x Var79 vz79 vs79)

def Tm79 : Con79 → Ty79 → Type 1
 := λ Γ A =>
   ∀ (Tm79  : Con79 → Ty79 → Type)
     (var   : ∀ Γ A     , Var79 Γ A → Tm79 Γ A)
     (lam   : ∀ Γ A B   , Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B))
     (app   : ∀ Γ A B   , Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B)
   , Tm79 Γ A

def var79 {Γ A} : Var79 Γ A → Tm79 Γ A
 := λ x Tm79 var79 lam app =>
     var79 _ _ x

def lam79 {Γ A B} : Tm79 (snoc79 Γ A) B → Tm79 Γ (arr79 A B)
 := λ t Tm79 var79 lam79 app =>
     lam79 _ _ _ (t Tm79 var79 lam79 app)

def app79 {Γ A B} : Tm79 Γ (arr79 A B) → Tm79 Γ A → Tm79 Γ B
 := λ t u Tm79 var79 lam79 app79 =>
     app79 _ _ _
         (t Tm79 var79 lam79 app79)
         (u Tm79 var79 lam79 app79)

def v079 {Γ A} : Tm79 (snoc79 Γ A) A
 := var79 vz79

def v179 {Γ A B} : Tm79 (snoc79 (snoc79 Γ A) B) A
 := var79 (vs79 vz79)

def v279 {Γ A B C} : Tm79 (snoc79 (snoc79 (snoc79 Γ A) B) C) A
 := var79 (vs79 (vs79 vz79))

def v379 {Γ A B C D} : Tm79 (snoc79 (snoc79 (snoc79 (snoc79 Γ A) B) C) D) A
 := var79 (vs79 (vs79 (vs79 vz79)))

def v479 {Γ A B C D E} : Tm79 (snoc79 (snoc79 (snoc79 (snoc79 (snoc79 Γ A) B) C) D) E) A
 := var79 (vs79 (vs79 (vs79 (vs79 vz79))))

def test79 {Γ A} : Tm79 Γ (arr79 (arr79 A A) (arr79 A A))
 := lam79 (lam79 (app79 v179 (app79 v179 (app79 v179 (app79 v179 (app79 v179 (app79 v179 v079)))))))


def Ty80 : Type 1
 := ∀ (Ty80 : Type)
      (ι   : Ty80)
      (arr : Ty80 → Ty80 → Ty80)
    , Ty80

def ι80 : Ty80 := λ _ ι80 _ => ι80

def arr80 : Ty80 → Ty80 → Ty80
 := λ A B Ty80 ι80 arr80 =>
     arr80 (A Ty80 ι80 arr80) (B Ty80 ι80 arr80)

def Con80 : Type 1
 := ∀ (Con80  : Type)
      (nil  : Con80)
      (snoc : Con80 → Ty80 → Con80)
    , Con80

def nil80 : Con80
 := λ Con80 nil80 snoc => nil80

def snoc80 : Con80 → Ty80 → Con80
 := λ Γ A Con80 nil80 snoc80 => snoc80 (Γ Con80 nil80 snoc80) A

def Var80 : Con80 → Ty80 → Type 1
 := λ Γ A =>
   ∀ (Var80 : Con80 → Ty80 → Type)
     (vz  : ∀ Γ A, Var80 (snoc80 Γ A) A)
     (vs  : ∀ Γ B A, Var80 Γ A → Var80 (snoc80 Γ B) A)
   , Var80 Γ A

def vz80 {Γ A} : Var80 (snoc80 Γ A) A
 := λ Var80 vz80 vs => vz80 _ _

def vs80 {Γ B A} : Var80 Γ A → Var80 (snoc80 Γ B) A
 := λ x Var80 vz80 vs80 => vs80 _ _ _ (x Var80 vz80 vs80)

def Tm80 : Con80 → Ty80 → Type 1
 := λ Γ A =>
   ∀ (Tm80  : Con80 → Ty80 → Type)
     (var   : ∀ Γ A     , Var80 Γ A → Tm80 Γ A)
     (lam   : ∀ Γ A B   , Tm80 (snoc80 Γ A) B → Tm80 Γ (arr80 A B))
     (app   : ∀ Γ A B   , Tm80 Γ (arr80 A B) → Tm80 Γ A → Tm80 Γ B)
   , Tm80 Γ A

def var80 {Γ A} : Var80 Γ A → Tm80 Γ A
 := λ x Tm80 var80 lam app =>
     var80 _ _ x

def lam80 {Γ A B} : Tm80 (snoc80 Γ A) B → Tm80 Γ (arr80 A B)
 := λ t Tm80 var80 lam80 app =>
     lam80 _ _ _ (t Tm80 var80 lam80 app)

def app80 {Γ A B} : Tm80 Γ (arr80 A B) → Tm80 Γ A → Tm80 Γ B
 := λ t u Tm80 var80 lam80 app80 =>
     app80 _ _ _
         (t Tm80 var80 lam80 app80)
         (u Tm80 var80 lam80 app80)

def v080 {Γ A} : Tm80 (snoc80 Γ A) A
 := var80 vz80

def v180 {Γ A B} : Tm80 (snoc80 (snoc80 Γ A) B) A
 := var80 (vs80 vz80)

def v280 {Γ A B C} : Tm80 (snoc80 (snoc80 (snoc80 Γ A) B) C) A
 := var80 (vs80 (vs80 vz80))

def v380 {Γ A B C D} : Tm80 (snoc80 (snoc80 (snoc80 (snoc80 Γ A) B) C) D) A
 := var80 (vs80 (vs80 (vs80 vz80)))

def v480 {Γ A B C D E} : Tm80 (snoc80 (snoc80 (snoc80 (snoc80 (snoc80 Γ A) B) C) D) E) A
 := var80 (vs80 (vs80 (vs80 (vs80 vz80))))

def test80 {Γ A} : Tm80 Γ (arr80 (arr80 A A) (arr80 A A))
 := lam80 (lam80 (app80 v180 (app80 v180 (app80 v180 (app80 v180 (app80 v180 (app80 v180 v080)))))))


def Ty81 : Type 1
 := ∀ (Ty81 : Type)
      (ι   : Ty81)
      (arr : Ty81 → Ty81 → Ty81)
    , Ty81

def ι81 : Ty81 := λ _ ι81 _ => ι81

def arr81 : Ty81 → Ty81 → Ty81
 := λ A B Ty81 ι81 arr81 =>
     arr81 (A Ty81 ι81 arr81) (B Ty81 ι81 arr81)

def Con81 : Type 1
 := ∀ (Con81  : Type)
      (nil  : Con81)
      (snoc : Con81 → Ty81 → Con81)
    , Con81

def nil81 : Con81
 := λ Con81 nil81 snoc => nil81

def snoc81 : Con81 → Ty81 → Con81
 := λ Γ A Con81 nil81 snoc81 => snoc81 (Γ Con81 nil81 snoc81) A

def Var81 : Con81 → Ty81 → Type 1
 := λ Γ A =>
   ∀ (Var81 : Con81 → Ty81 → Type)
     (vz  : ∀ Γ A, Var81 (snoc81 Γ A) A)
     (vs  : ∀ Γ B A, Var81 Γ A → Var81 (snoc81 Γ B) A)
   , Var81 Γ A

def vz81 {Γ A} : Var81 (snoc81 Γ A) A
 := λ Var81 vz81 vs => vz81 _ _

def vs81 {Γ B A} : Var81 Γ A → Var81 (snoc81 Γ B) A
 := λ x Var81 vz81 vs81 => vs81 _ _ _ (x Var81 vz81 vs81)

def Tm81 : Con81 → Ty81 → Type 1
 := λ Γ A =>
   ∀ (Tm81  : Con81 → Ty81 → Type)
     (var   : ∀ Γ A     , Var81 Γ A → Tm81 Γ A)
     (lam   : ∀ Γ A B   , Tm81 (snoc81 Γ A) B → Tm81 Γ (arr81 A B))
     (app   : ∀ Γ A B   , Tm81 Γ (arr81 A B) → Tm81 Γ A → Tm81 Γ B)
   , Tm81 Γ A

def var81 {Γ A} : Var81 Γ A → Tm81 Γ A
 := λ x Tm81 var81 lam app =>
     var81 _ _ x

def lam81 {Γ A B} : Tm81 (snoc81 Γ A) B → Tm81 Γ (arr81 A B)
 := λ t Tm81 var81 lam81 app =>
     lam81 _ _ _ (t Tm81 var81 lam81 app)

def app81 {Γ A B} : Tm81 Γ (arr81 A B) → Tm81 Γ A → Tm81 Γ B
 := λ t u Tm81 var81 lam81 app81 =>
     app81 _ _ _
         (t Tm81 var81 lam81 app81)
         (u Tm81 var81 lam81 app81)

def v081 {Γ A} : Tm81 (snoc81 Γ A) A
 := var81 vz81

def v181 {Γ A B} : Tm81 (snoc81 (snoc81 Γ A) B) A
 := var81 (vs81 vz81)

def v281 {Γ A B C} : Tm81 (snoc81 (snoc81 (snoc81 Γ A) B) C) A
 := var81 (vs81 (vs81 vz81))

def v381 {Γ A B C D} : Tm81 (snoc81 (snoc81 (snoc81 (snoc81 Γ A) B) C) D) A
 := var81 (vs81 (vs81 (vs81 vz81)))

def v481 {Γ A B C D E} : Tm81 (snoc81 (snoc81 (snoc81 (snoc81 (snoc81 Γ A) B) C) D) E) A
 := var81 (vs81 (vs81 (vs81 (vs81 vz81))))

def test81 {Γ A} : Tm81 Γ (arr81 (arr81 A A) (arr81 A A))
 := lam81 (lam81 (app81 v181 (app81 v181 (app81 v181 (app81 v181 (app81 v181 (app81 v181 v081)))))))


def Ty82 : Type 1
 := ∀ (Ty82 : Type)
      (ι   : Ty82)
      (arr : Ty82 → Ty82 → Ty82)
    , Ty82

def ι82 : Ty82 := λ _ ι82 _ => ι82

def arr82 : Ty82 → Ty82 → Ty82
 := λ A B Ty82 ι82 arr82 =>
     arr82 (A Ty82 ι82 arr82) (B Ty82 ι82 arr82)

def Con82 : Type 1
 := ∀ (Con82  : Type)
      (nil  : Con82)
      (snoc : Con82 → Ty82 → Con82)
    , Con82

def nil82 : Con82
 := λ Con82 nil82 snoc => nil82

def snoc82 : Con82 → Ty82 → Con82
 := λ Γ A Con82 nil82 snoc82 => snoc82 (Γ Con82 nil82 snoc82) A

def Var82 : Con82 → Ty82 → Type 1
 := λ Γ A =>
   ∀ (Var82 : Con82 → Ty82 → Type)
     (vz  : ∀ Γ A, Var82 (snoc82 Γ A) A)
     (vs  : ∀ Γ B A, Var82 Γ A → Var82 (snoc82 Γ B) A)
   , Var82 Γ A

def vz82 {Γ A} : Var82 (snoc82 Γ A) A
 := λ Var82 vz82 vs => vz82 _ _

def vs82 {Γ B A} : Var82 Γ A → Var82 (snoc82 Γ B) A
 := λ x Var82 vz82 vs82 => vs82 _ _ _ (x Var82 vz82 vs82)

def Tm82 : Con82 → Ty82 → Type 1
 := λ Γ A =>
   ∀ (Tm82  : Con82 → Ty82 → Type)
     (var   : ∀ Γ A     , Var82 Γ A → Tm82 Γ A)
     (lam   : ∀ Γ A B   , Tm82 (snoc82 Γ A) B → Tm82 Γ (arr82 A B))
     (app   : ∀ Γ A B   , Tm82 Γ (arr82 A B) → Tm82 Γ A → Tm82 Γ B)
   , Tm82 Γ A

def var82 {Γ A} : Var82 Γ A → Tm82 Γ A
 := λ x Tm82 var82 lam app =>
     var82 _ _ x

def lam82 {Γ A B} : Tm82 (snoc82 Γ A) B → Tm82 Γ (arr82 A B)
 := λ t Tm82 var82 lam82 app =>
     lam82 _ _ _ (t Tm82 var82 lam82 app)

def app82 {Γ A B} : Tm82 Γ (arr82 A B) → Tm82 Γ A → Tm82 Γ B
 := λ t u Tm82 var82 lam82 app82 =>
     app82 _ _ _
         (t Tm82 var82 lam82 app82)
         (u Tm82 var82 lam82 app82)

def v082 {Γ A} : Tm82 (snoc82 Γ A) A
 := var82 vz82

def v182 {Γ A B} : Tm82 (snoc82 (snoc82 Γ A) B) A
 := var82 (vs82 vz82)

def v282 {Γ A B C} : Tm82 (snoc82 (snoc82 (snoc82 Γ A) B) C) A
 := var82 (vs82 (vs82 vz82))

def v382 {Γ A B C D} : Tm82 (snoc82 (snoc82 (snoc82 (snoc82 Γ A) B) C) D) A
 := var82 (vs82 (vs82 (vs82 vz82)))

def v482 {Γ A B C D E} : Tm82 (snoc82 (snoc82 (snoc82 (snoc82 (snoc82 Γ A) B) C) D) E) A
 := var82 (vs82 (vs82 (vs82 (vs82 vz82))))

def test82 {Γ A} : Tm82 Γ (arr82 (arr82 A A) (arr82 A A))
 := lam82 (lam82 (app82 v182 (app82 v182 (app82 v182 (app82 v182 (app82 v182 (app82 v182 v082)))))))


def Ty83 : Type 1
 := ∀ (Ty83 : Type)
      (ι   : Ty83)
      (arr : Ty83 → Ty83 → Ty83)
    , Ty83

def ι83 : Ty83 := λ _ ι83 _ => ι83

def arr83 : Ty83 → Ty83 → Ty83
 := λ A B Ty83 ι83 arr83 =>
     arr83 (A Ty83 ι83 arr83) (B Ty83 ι83 arr83)

def Con83 : Type 1
 := ∀ (Con83  : Type)
      (nil  : Con83)
      (snoc : Con83 → Ty83 → Con83)
    , Con83

def nil83 : Con83
 := λ Con83 nil83 snoc => nil83

def snoc83 : Con83 → Ty83 → Con83
 := λ Γ A Con83 nil83 snoc83 => snoc83 (Γ Con83 nil83 snoc83) A

def Var83 : Con83 → Ty83 → Type 1
 := λ Γ A =>
   ∀ (Var83 : Con83 → Ty83 → Type)
     (vz  : ∀ Γ A, Var83 (snoc83 Γ A) A)
     (vs  : ∀ Γ B A, Var83 Γ A → Var83 (snoc83 Γ B) A)
   , Var83 Γ A

def vz83 {Γ A} : Var83 (snoc83 Γ A) A
 := λ Var83 vz83 vs => vz83 _ _

def vs83 {Γ B A} : Var83 Γ A → Var83 (snoc83 Γ B) A
 := λ x Var83 vz83 vs83 => vs83 _ _ _ (x Var83 vz83 vs83)

def Tm83 : Con83 → Ty83 → Type 1
 := λ Γ A =>
   ∀ (Tm83  : Con83 → Ty83 → Type)
     (var   : ∀ Γ A     , Var83 Γ A → Tm83 Γ A)
     (lam   : ∀ Γ A B   , Tm83 (snoc83 Γ A) B → Tm83 Γ (arr83 A B))
     (app   : ∀ Γ A B   , Tm83 Γ (arr83 A B) → Tm83 Γ A → Tm83 Γ B)
   , Tm83 Γ A

def var83 {Γ A} : Var83 Γ A → Tm83 Γ A
 := λ x Tm83 var83 lam app =>
     var83 _ _ x

def lam83 {Γ A B} : Tm83 (snoc83 Γ A) B → Tm83 Γ (arr83 A B)
 := λ t Tm83 var83 lam83 app =>
     lam83 _ _ _ (t Tm83 var83 lam83 app)

def app83 {Γ A B} : Tm83 Γ (arr83 A B) → Tm83 Γ A → Tm83 Γ B
 := λ t u Tm83 var83 lam83 app83 =>
     app83 _ _ _
         (t Tm83 var83 lam83 app83)
         (u Tm83 var83 lam83 app83)

def v083 {Γ A} : Tm83 (snoc83 Γ A) A
 := var83 vz83

def v183 {Γ A B} : Tm83 (snoc83 (snoc83 Γ A) B) A
 := var83 (vs83 vz83)

def v283 {Γ A B C} : Tm83 (snoc83 (snoc83 (snoc83 Γ A) B) C) A
 := var83 (vs83 (vs83 vz83))

def v383 {Γ A B C D} : Tm83 (snoc83 (snoc83 (snoc83 (snoc83 Γ A) B) C) D) A
 := var83 (vs83 (vs83 (vs83 vz83)))

def v483 {Γ A B C D E} : Tm83 (snoc83 (snoc83 (snoc83 (snoc83 (snoc83 Γ A) B) C) D) E) A
 := var83 (vs83 (vs83 (vs83 (vs83 vz83))))

def test83 {Γ A} : Tm83 Γ (arr83 (arr83 A A) (arr83 A A))
 := lam83 (lam83 (app83 v183 (app83 v183 (app83 v183 (app83 v183 (app83 v183 (app83 v183 v083)))))))


def Ty84 : Type 1
 := ∀ (Ty84 : Type)
      (ι   : Ty84)
      (arr : Ty84 → Ty84 → Ty84)
    , Ty84

def ι84 : Ty84 := λ _ ι84 _ => ι84

def arr84 : Ty84 → Ty84 → Ty84
 := λ A B Ty84 ι84 arr84 =>
     arr84 (A Ty84 ι84 arr84) (B Ty84 ι84 arr84)

def Con84 : Type 1
 := ∀ (Con84  : Type)
      (nil  : Con84)
      (snoc : Con84 → Ty84 → Con84)
    , Con84

def nil84 : Con84
 := λ Con84 nil84 snoc => nil84

def snoc84 : Con84 → Ty84 → Con84
 := λ Γ A Con84 nil84 snoc84 => snoc84 (Γ Con84 nil84 snoc84) A

def Var84 : Con84 → Ty84 → Type 1
 := λ Γ A =>
   ∀ (Var84 : Con84 → Ty84 → Type)
     (vz  : ∀ Γ A, Var84 (snoc84 Γ A) A)
     (vs  : ∀ Γ B A, Var84 Γ A → Var84 (snoc84 Γ B) A)
   , Var84 Γ A

def vz84 {Γ A} : Var84 (snoc84 Γ A) A
 := λ Var84 vz84 vs => vz84 _ _

def vs84 {Γ B A} : Var84 Γ A → Var84 (snoc84 Γ B) A
 := λ x Var84 vz84 vs84 => vs84 _ _ _ (x Var84 vz84 vs84)

def Tm84 : Con84 → Ty84 → Type 1
 := λ Γ A =>
   ∀ (Tm84  : Con84 → Ty84 → Type)
     (var   : ∀ Γ A     , Var84 Γ A → Tm84 Γ A)
     (lam   : ∀ Γ A B   , Tm84 (snoc84 Γ A) B → Tm84 Γ (arr84 A B))
     (app   : ∀ Γ A B   , Tm84 Γ (arr84 A B) → Tm84 Γ A → Tm84 Γ B)
   , Tm84 Γ A

def var84 {Γ A} : Var84 Γ A → Tm84 Γ A
 := λ x Tm84 var84 lam app =>
     var84 _ _ x

def lam84 {Γ A B} : Tm84 (snoc84 Γ A) B → Tm84 Γ (arr84 A B)
 := λ t Tm84 var84 lam84 app =>
     lam84 _ _ _ (t Tm84 var84 lam84 app)

def app84 {Γ A B} : Tm84 Γ (arr84 A B) → Tm84 Γ A → Tm84 Γ B
 := λ t u Tm84 var84 lam84 app84 =>
     app84 _ _ _
         (t Tm84 var84 lam84 app84)
         (u Tm84 var84 lam84 app84)

def v084 {Γ A} : Tm84 (snoc84 Γ A) A
 := var84 vz84

def v184 {Γ A B} : Tm84 (snoc84 (snoc84 Γ A) B) A
 := var84 (vs84 vz84)

def v284 {Γ A B C} : Tm84 (snoc84 (snoc84 (snoc84 Γ A) B) C) A
 := var84 (vs84 (vs84 vz84))

def v384 {Γ A B C D} : Tm84 (snoc84 (snoc84 (snoc84 (snoc84 Γ A) B) C) D) A
 := var84 (vs84 (vs84 (vs84 vz84)))

def v484 {Γ A B C D E} : Tm84 (snoc84 (snoc84 (snoc84 (snoc84 (snoc84 Γ A) B) C) D) E) A
 := var84 (vs84 (vs84 (vs84 (vs84 vz84))))

def test84 {Γ A} : Tm84 Γ (arr84 (arr84 A A) (arr84 A A))
 := lam84 (lam84 (app84 v184 (app84 v184 (app84 v184 (app84 v184 (app84 v184 (app84 v184 v084)))))))


def Ty85 : Type 1
 := ∀ (Ty85 : Type)
      (ι   : Ty85)
      (arr : Ty85 → Ty85 → Ty85)
    , Ty85

def ι85 : Ty85 := λ _ ι85 _ => ι85

def arr85 : Ty85 → Ty85 → Ty85
 := λ A B Ty85 ι85 arr85 =>
     arr85 (A Ty85 ι85 arr85) (B Ty85 ι85 arr85)

def Con85 : Type 1
 := ∀ (Con85  : Type)
      (nil  : Con85)
      (snoc : Con85 → Ty85 → Con85)
    , Con85

def nil85 : Con85
 := λ Con85 nil85 snoc => nil85

def snoc85 : Con85 → Ty85 → Con85
 := λ Γ A Con85 nil85 snoc85 => snoc85 (Γ Con85 nil85 snoc85) A

def Var85 : Con85 → Ty85 → Type 1
 := λ Γ A =>
   ∀ (Var85 : Con85 → Ty85 → Type)
     (vz  : ∀ Γ A, Var85 (snoc85 Γ A) A)
     (vs  : ∀ Γ B A, Var85 Γ A → Var85 (snoc85 Γ B) A)
   , Var85 Γ A

def vz85 {Γ A} : Var85 (snoc85 Γ A) A
 := λ Var85 vz85 vs => vz85 _ _

def vs85 {Γ B A} : Var85 Γ A → Var85 (snoc85 Γ B) A
 := λ x Var85 vz85 vs85 => vs85 _ _ _ (x Var85 vz85 vs85)

def Tm85 : Con85 → Ty85 → Type 1
 := λ Γ A =>
   ∀ (Tm85  : Con85 → Ty85 → Type)
     (var   : ∀ Γ A     , Var85 Γ A → Tm85 Γ A)
     (lam   : ∀ Γ A B   , Tm85 (snoc85 Γ A) B → Tm85 Γ (arr85 A B))
     (app   : ∀ Γ A B   , Tm85 Γ (arr85 A B) → Tm85 Γ A → Tm85 Γ B)
   , Tm85 Γ A

def var85 {Γ A} : Var85 Γ A → Tm85 Γ A
 := λ x Tm85 var85 lam app =>
     var85 _ _ x

def lam85 {Γ A B} : Tm85 (snoc85 Γ A) B → Tm85 Γ (arr85 A B)
 := λ t Tm85 var85 lam85 app =>
     lam85 _ _ _ (t Tm85 var85 lam85 app)

def app85 {Γ A B} : Tm85 Γ (arr85 A B) → Tm85 Γ A → Tm85 Γ B
 := λ t u Tm85 var85 lam85 app85 =>
     app85 _ _ _
         (t Tm85 var85 lam85 app85)
         (u Tm85 var85 lam85 app85)

def v085 {Γ A} : Tm85 (snoc85 Γ A) A
 := var85 vz85

def v185 {Γ A B} : Tm85 (snoc85 (snoc85 Γ A) B) A
 := var85 (vs85 vz85)

def v285 {Γ A B C} : Tm85 (snoc85 (snoc85 (snoc85 Γ A) B) C) A
 := var85 (vs85 (vs85 vz85))

def v385 {Γ A B C D} : Tm85 (snoc85 (snoc85 (snoc85 (snoc85 Γ A) B) C) D) A
 := var85 (vs85 (vs85 (vs85 vz85)))

def v485 {Γ A B C D E} : Tm85 (snoc85 (snoc85 (snoc85 (snoc85 (snoc85 Γ A) B) C) D) E) A
 := var85 (vs85 (vs85 (vs85 (vs85 vz85))))

def test85 {Γ A} : Tm85 Γ (arr85 (arr85 A A) (arr85 A A))
 := lam85 (lam85 (app85 v185 (app85 v185 (app85 v185 (app85 v185 (app85 v185 (app85 v185 v085)))))))


def Ty86 : Type 1
 := ∀ (Ty86 : Type)
      (ι   : Ty86)
      (arr : Ty86 → Ty86 → Ty86)
    , Ty86

def ι86 : Ty86 := λ _ ι86 _ => ι86

def arr86 : Ty86 → Ty86 → Ty86
 := λ A B Ty86 ι86 arr86 =>
     arr86 (A Ty86 ι86 arr86) (B Ty86 ι86 arr86)

def Con86 : Type 1
 := ∀ (Con86  : Type)
      (nil  : Con86)
      (snoc : Con86 → Ty86 → Con86)
    , Con86

def nil86 : Con86
 := λ Con86 nil86 snoc => nil86

def snoc86 : Con86 → Ty86 → Con86
 := λ Γ A Con86 nil86 snoc86 => snoc86 (Γ Con86 nil86 snoc86) A

def Var86 : Con86 → Ty86 → Type 1
 := λ Γ A =>
   ∀ (Var86 : Con86 → Ty86 → Type)
     (vz  : ∀ Γ A, Var86 (snoc86 Γ A) A)
     (vs  : ∀ Γ B A, Var86 Γ A → Var86 (snoc86 Γ B) A)
   , Var86 Γ A

def vz86 {Γ A} : Var86 (snoc86 Γ A) A
 := λ Var86 vz86 vs => vz86 _ _

def vs86 {Γ B A} : Var86 Γ A → Var86 (snoc86 Γ B) A
 := λ x Var86 vz86 vs86 => vs86 _ _ _ (x Var86 vz86 vs86)

def Tm86 : Con86 → Ty86 → Type 1
 := λ Γ A =>
   ∀ (Tm86  : Con86 → Ty86 → Type)
     (var   : ∀ Γ A     , Var86 Γ A → Tm86 Γ A)
     (lam   : ∀ Γ A B   , Tm86 (snoc86 Γ A) B → Tm86 Γ (arr86 A B))
     (app   : ∀ Γ A B   , Tm86 Γ (arr86 A B) → Tm86 Γ A → Tm86 Γ B)
   , Tm86 Γ A

def var86 {Γ A} : Var86 Γ A → Tm86 Γ A
 := λ x Tm86 var86 lam app =>
     var86 _ _ x

def lam86 {Γ A B} : Tm86 (snoc86 Γ A) B → Tm86 Γ (arr86 A B)
 := λ t Tm86 var86 lam86 app =>
     lam86 _ _ _ (t Tm86 var86 lam86 app)

def app86 {Γ A B} : Tm86 Γ (arr86 A B) → Tm86 Γ A → Tm86 Γ B
 := λ t u Tm86 var86 lam86 app86 =>
     app86 _ _ _
         (t Tm86 var86 lam86 app86)
         (u Tm86 var86 lam86 app86)

def v086 {Γ A} : Tm86 (snoc86 Γ A) A
 := var86 vz86

def v186 {Γ A B} : Tm86 (snoc86 (snoc86 Γ A) B) A
 := var86 (vs86 vz86)

def v286 {Γ A B C} : Tm86 (snoc86 (snoc86 (snoc86 Γ A) B) C) A
 := var86 (vs86 (vs86 vz86))

def v386 {Γ A B C D} : Tm86 (snoc86 (snoc86 (snoc86 (snoc86 Γ A) B) C) D) A
 := var86 (vs86 (vs86 (vs86 vz86)))

def v486 {Γ A B C D E} : Tm86 (snoc86 (snoc86 (snoc86 (snoc86 (snoc86 Γ A) B) C) D) E) A
 := var86 (vs86 (vs86 (vs86 (vs86 vz86))))

def test86 {Γ A} : Tm86 Γ (arr86 (arr86 A A) (arr86 A A))
 := lam86 (lam86 (app86 v186 (app86 v186 (app86 v186 (app86 v186 (app86 v186 (app86 v186 v086)))))))


def Ty87 : Type 1
 := ∀ (Ty87 : Type)
      (ι   : Ty87)
      (arr : Ty87 → Ty87 → Ty87)
    , Ty87

def ι87 : Ty87 := λ _ ι87 _ => ι87

def arr87 : Ty87 → Ty87 → Ty87
 := λ A B Ty87 ι87 arr87 =>
     arr87 (A Ty87 ι87 arr87) (B Ty87 ι87 arr87)

def Con87 : Type 1
 := ∀ (Con87  : Type)
      (nil  : Con87)
      (snoc : Con87 → Ty87 → Con87)
    , Con87

def nil87 : Con87
 := λ Con87 nil87 snoc => nil87

def snoc87 : Con87 → Ty87 → Con87
 := λ Γ A Con87 nil87 snoc87 => snoc87 (Γ Con87 nil87 snoc87) A

def Var87 : Con87 → Ty87 → Type 1
 := λ Γ A =>
   ∀ (Var87 : Con87 → Ty87 → Type)
     (vz  : ∀ Γ A, Var87 (snoc87 Γ A) A)
     (vs  : ∀ Γ B A, Var87 Γ A → Var87 (snoc87 Γ B) A)
   , Var87 Γ A

def vz87 {Γ A} : Var87 (snoc87 Γ A) A
 := λ Var87 vz87 vs => vz87 _ _

def vs87 {Γ B A} : Var87 Γ A → Var87 (snoc87 Γ B) A
 := λ x Var87 vz87 vs87 => vs87 _ _ _ (x Var87 vz87 vs87)

def Tm87 : Con87 → Ty87 → Type 1
 := λ Γ A =>
   ∀ (Tm87  : Con87 → Ty87 → Type)
     (var   : ∀ Γ A     , Var87 Γ A → Tm87 Γ A)
     (lam   : ∀ Γ A B   , Tm87 (snoc87 Γ A) B → Tm87 Γ (arr87 A B))
     (app   : ∀ Γ A B   , Tm87 Γ (arr87 A B) → Tm87 Γ A → Tm87 Γ B)
   , Tm87 Γ A

def var87 {Γ A} : Var87 Γ A → Tm87 Γ A
 := λ x Tm87 var87 lam app =>
     var87 _ _ x

def lam87 {Γ A B} : Tm87 (snoc87 Γ A) B → Tm87 Γ (arr87 A B)
 := λ t Tm87 var87 lam87 app =>
     lam87 _ _ _ (t Tm87 var87 lam87 app)

def app87 {Γ A B} : Tm87 Γ (arr87 A B) → Tm87 Γ A → Tm87 Γ B
 := λ t u Tm87 var87 lam87 app87 =>
     app87 _ _ _
         (t Tm87 var87 lam87 app87)
         (u Tm87 var87 lam87 app87)

def v087 {Γ A} : Tm87 (snoc87 Γ A) A
 := var87 vz87

def v187 {Γ A B} : Tm87 (snoc87 (snoc87 Γ A) B) A
 := var87 (vs87 vz87)

def v287 {Γ A B C} : Tm87 (snoc87 (snoc87 (snoc87 Γ A) B) C) A
 := var87 (vs87 (vs87 vz87))

def v387 {Γ A B C D} : Tm87 (snoc87 (snoc87 (snoc87 (snoc87 Γ A) B) C) D) A
 := var87 (vs87 (vs87 (vs87 vz87)))

def v487 {Γ A B C D E} : Tm87 (snoc87 (snoc87 (snoc87 (snoc87 (snoc87 Γ A) B) C) D) E) A
 := var87 (vs87 (vs87 (vs87 (vs87 vz87))))

def test87 {Γ A} : Tm87 Γ (arr87 (arr87 A A) (arr87 A A))
 := lam87 (lam87 (app87 v187 (app87 v187 (app87 v187 (app87 v187 (app87 v187 (app87 v187 v087)))))))


def Ty88 : Type 1
 := ∀ (Ty88 : Type)
      (ι   : Ty88)
      (arr : Ty88 → Ty88 → Ty88)
    , Ty88

def ι88 : Ty88 := λ _ ι88 _ => ι88

def arr88 : Ty88 → Ty88 → Ty88
 := λ A B Ty88 ι88 arr88 =>
     arr88 (A Ty88 ι88 arr88) (B Ty88 ι88 arr88)

def Con88 : Type 1
 := ∀ (Con88  : Type)
      (nil  : Con88)
      (snoc : Con88 → Ty88 → Con88)
    , Con88

def nil88 : Con88
 := λ Con88 nil88 snoc => nil88

def snoc88 : Con88 → Ty88 → Con88
 := λ Γ A Con88 nil88 snoc88 => snoc88 (Γ Con88 nil88 snoc88) A

def Var88 : Con88 → Ty88 → Type 1
 := λ Γ A =>
   ∀ (Var88 : Con88 → Ty88 → Type)
     (vz  : ∀ Γ A, Var88 (snoc88 Γ A) A)
     (vs  : ∀ Γ B A, Var88 Γ A → Var88 (snoc88 Γ B) A)
   , Var88 Γ A

def vz88 {Γ A} : Var88 (snoc88 Γ A) A
 := λ Var88 vz88 vs => vz88 _ _

def vs88 {Γ B A} : Var88 Γ A → Var88 (snoc88 Γ B) A
 := λ x Var88 vz88 vs88 => vs88 _ _ _ (x Var88 vz88 vs88)

def Tm88 : Con88 → Ty88 → Type 1
 := λ Γ A =>
   ∀ (Tm88  : Con88 → Ty88 → Type)
     (var   : ∀ Γ A     , Var88 Γ A → Tm88 Γ A)
     (lam   : ∀ Γ A B   , Tm88 (snoc88 Γ A) B → Tm88 Γ (arr88 A B))
     (app   : ∀ Γ A B   , Tm88 Γ (arr88 A B) → Tm88 Γ A → Tm88 Γ B)
   , Tm88 Γ A

def var88 {Γ A} : Var88 Γ A → Tm88 Γ A
 := λ x Tm88 var88 lam app =>
     var88 _ _ x

def lam88 {Γ A B} : Tm88 (snoc88 Γ A) B → Tm88 Γ (arr88 A B)
 := λ t Tm88 var88 lam88 app =>
     lam88 _ _ _ (t Tm88 var88 lam88 app)

def app88 {Γ A B} : Tm88 Γ (arr88 A B) → Tm88 Γ A → Tm88 Γ B
 := λ t u Tm88 var88 lam88 app88 =>
     app88 _ _ _
         (t Tm88 var88 lam88 app88)
         (u Tm88 var88 lam88 app88)

def v088 {Γ A} : Tm88 (snoc88 Γ A) A
 := var88 vz88

def v188 {Γ A B} : Tm88 (snoc88 (snoc88 Γ A) B) A
 := var88 (vs88 vz88)

def v288 {Γ A B C} : Tm88 (snoc88 (snoc88 (snoc88 Γ A) B) C) A
 := var88 (vs88 (vs88 vz88))

def v388 {Γ A B C D} : Tm88 (snoc88 (snoc88 (snoc88 (snoc88 Γ A) B) C) D) A
 := var88 (vs88 (vs88 (vs88 vz88)))

def v488 {Γ A B C D E} : Tm88 (snoc88 (snoc88 (snoc88 (snoc88 (snoc88 Γ A) B) C) D) E) A
 := var88 (vs88 (vs88 (vs88 (vs88 vz88))))

def test88 {Γ A} : Tm88 Γ (arr88 (arr88 A A) (arr88 A A))
 := lam88 (lam88 (app88 v188 (app88 v188 (app88 v188 (app88 v188 (app88 v188 (app88 v188 v088)))))))


def Ty89 : Type 1
 := ∀ (Ty89 : Type)
      (ι   : Ty89)
      (arr : Ty89 → Ty89 → Ty89)
    , Ty89

def ι89 : Ty89 := λ _ ι89 _ => ι89

def arr89 : Ty89 → Ty89 → Ty89
 := λ A B Ty89 ι89 arr89 =>
     arr89 (A Ty89 ι89 arr89) (B Ty89 ι89 arr89)

def Con89 : Type 1
 := ∀ (Con89  : Type)
      (nil  : Con89)
      (snoc : Con89 → Ty89 → Con89)
    , Con89

def nil89 : Con89
 := λ Con89 nil89 snoc => nil89

def snoc89 : Con89 → Ty89 → Con89
 := λ Γ A Con89 nil89 snoc89 => snoc89 (Γ Con89 nil89 snoc89) A

def Var89 : Con89 → Ty89 → Type 1
 := λ Γ A =>
   ∀ (Var89 : Con89 → Ty89 → Type)
     (vz  : ∀ Γ A, Var89 (snoc89 Γ A) A)
     (vs  : ∀ Γ B A, Var89 Γ A → Var89 (snoc89 Γ B) A)
   , Var89 Γ A

def vz89 {Γ A} : Var89 (snoc89 Γ A) A
 := λ Var89 vz89 vs => vz89 _ _

def vs89 {Γ B A} : Var89 Γ A → Var89 (snoc89 Γ B) A
 := λ x Var89 vz89 vs89 => vs89 _ _ _ (x Var89 vz89 vs89)

def Tm89 : Con89 → Ty89 → Type 1
 := λ Γ A =>
   ∀ (Tm89  : Con89 → Ty89 → Type)
     (var   : ∀ Γ A     , Var89 Γ A → Tm89 Γ A)
     (lam   : ∀ Γ A B   , Tm89 (snoc89 Γ A) B → Tm89 Γ (arr89 A B))
     (app   : ∀ Γ A B   , Tm89 Γ (arr89 A B) → Tm89 Γ A → Tm89 Γ B)
   , Tm89 Γ A

def var89 {Γ A} : Var89 Γ A → Tm89 Γ A
 := λ x Tm89 var89 lam app =>
     var89 _ _ x

def lam89 {Γ A B} : Tm89 (snoc89 Γ A) B → Tm89 Γ (arr89 A B)
 := λ t Tm89 var89 lam89 app =>
     lam89 _ _ _ (t Tm89 var89 lam89 app)

def app89 {Γ A B} : Tm89 Γ (arr89 A B) → Tm89 Γ A → Tm89 Γ B
 := λ t u Tm89 var89 lam89 app89 =>
     app89 _ _ _
         (t Tm89 var89 lam89 app89)
         (u Tm89 var89 lam89 app89)

def v089 {Γ A} : Tm89 (snoc89 Γ A) A
 := var89 vz89

def v189 {Γ A B} : Tm89 (snoc89 (snoc89 Γ A) B) A
 := var89 (vs89 vz89)

def v289 {Γ A B C} : Tm89 (snoc89 (snoc89 (snoc89 Γ A) B) C) A
 := var89 (vs89 (vs89 vz89))

def v389 {Γ A B C D} : Tm89 (snoc89 (snoc89 (snoc89 (snoc89 Γ A) B) C) D) A
 := var89 (vs89 (vs89 (vs89 vz89)))

def v489 {Γ A B C D E} : Tm89 (snoc89 (snoc89 (snoc89 (snoc89 (snoc89 Γ A) B) C) D) E) A
 := var89 (vs89 (vs89 (vs89 (vs89 vz89))))

def test89 {Γ A} : Tm89 Γ (arr89 (arr89 A A) (arr89 A A))
 := lam89 (lam89 (app89 v189 (app89 v189 (app89 v189 (app89 v189 (app89 v189 (app89 v189 v089)))))))


def Ty90 : Type 1
 := ∀ (Ty90 : Type)
      (ι   : Ty90)
      (arr : Ty90 → Ty90 → Ty90)
    , Ty90

def ι90 : Ty90 := λ _ ι90 _ => ι90

def arr90 : Ty90 → Ty90 → Ty90
 := λ A B Ty90 ι90 arr90 =>
     arr90 (A Ty90 ι90 arr90) (B Ty90 ι90 arr90)

def Con90 : Type 1
 := ∀ (Con90  : Type)
      (nil  : Con90)
      (snoc : Con90 → Ty90 → Con90)
    , Con90

def nil90 : Con90
 := λ Con90 nil90 snoc => nil90

def snoc90 : Con90 → Ty90 → Con90
 := λ Γ A Con90 nil90 snoc90 => snoc90 (Γ Con90 nil90 snoc90) A

def Var90 : Con90 → Ty90 → Type 1
 := λ Γ A =>
   ∀ (Var90 : Con90 → Ty90 → Type)
     (vz  : ∀ Γ A, Var90 (snoc90 Γ A) A)
     (vs  : ∀ Γ B A, Var90 Γ A → Var90 (snoc90 Γ B) A)
   , Var90 Γ A

def vz90 {Γ A} : Var90 (snoc90 Γ A) A
 := λ Var90 vz90 vs => vz90 _ _

def vs90 {Γ B A} : Var90 Γ A → Var90 (snoc90 Γ B) A
 := λ x Var90 vz90 vs90 => vs90 _ _ _ (x Var90 vz90 vs90)

def Tm90 : Con90 → Ty90 → Type 1
 := λ Γ A =>
   ∀ (Tm90  : Con90 → Ty90 → Type)
     (var   : ∀ Γ A     , Var90 Γ A → Tm90 Γ A)
     (lam   : ∀ Γ A B   , Tm90 (snoc90 Γ A) B → Tm90 Γ (arr90 A B))
     (app   : ∀ Γ A B   , Tm90 Γ (arr90 A B) → Tm90 Γ A → Tm90 Γ B)
   , Tm90 Γ A

def var90 {Γ A} : Var90 Γ A → Tm90 Γ A
 := λ x Tm90 var90 lam app =>
     var90 _ _ x

def lam90 {Γ A B} : Tm90 (snoc90 Γ A) B → Tm90 Γ (arr90 A B)
 := λ t Tm90 var90 lam90 app =>
     lam90 _ _ _ (t Tm90 var90 lam90 app)

def app90 {Γ A B} : Tm90 Γ (arr90 A B) → Tm90 Γ A → Tm90 Γ B
 := λ t u Tm90 var90 lam90 app90 =>
     app90 _ _ _
         (t Tm90 var90 lam90 app90)
         (u Tm90 var90 lam90 app90)

def v090 {Γ A} : Tm90 (snoc90 Γ A) A
 := var90 vz90

def v190 {Γ A B} : Tm90 (snoc90 (snoc90 Γ A) B) A
 := var90 (vs90 vz90)

def v290 {Γ A B C} : Tm90 (snoc90 (snoc90 (snoc90 Γ A) B) C) A
 := var90 (vs90 (vs90 vz90))

def v390 {Γ A B C D} : Tm90 (snoc90 (snoc90 (snoc90 (snoc90 Γ A) B) C) D) A
 := var90 (vs90 (vs90 (vs90 vz90)))

def v490 {Γ A B C D E} : Tm90 (snoc90 (snoc90 (snoc90 (snoc90 (snoc90 Γ A) B) C) D) E) A
 := var90 (vs90 (vs90 (vs90 (vs90 vz90))))

def test90 {Γ A} : Tm90 Γ (arr90 (arr90 A A) (arr90 A A))
 := lam90 (lam90 (app90 v190 (app90 v190 (app90 v190 (app90 v190 (app90 v190 (app90 v190 v090)))))))


def Ty91 : Type 1
 := ∀ (Ty91 : Type)
      (ι   : Ty91)
      (arr : Ty91 → Ty91 → Ty91)
    , Ty91

def ι91 : Ty91 := λ _ ι91 _ => ι91

def arr91 : Ty91 → Ty91 → Ty91
 := λ A B Ty91 ι91 arr91 =>
     arr91 (A Ty91 ι91 arr91) (B Ty91 ι91 arr91)

def Con91 : Type 1
 := ∀ (Con91  : Type)
      (nil  : Con91)
      (snoc : Con91 → Ty91 → Con91)
    , Con91

def nil91 : Con91
 := λ Con91 nil91 snoc => nil91

def snoc91 : Con91 → Ty91 → Con91
 := λ Γ A Con91 nil91 snoc91 => snoc91 (Γ Con91 nil91 snoc91) A

def Var91 : Con91 → Ty91 → Type 1
 := λ Γ A =>
   ∀ (Var91 : Con91 → Ty91 → Type)
     (vz  : ∀ Γ A, Var91 (snoc91 Γ A) A)
     (vs  : ∀ Γ B A, Var91 Γ A → Var91 (snoc91 Γ B) A)
   , Var91 Γ A

def vz91 {Γ A} : Var91 (snoc91 Γ A) A
 := λ Var91 vz91 vs => vz91 _ _

def vs91 {Γ B A} : Var91 Γ A → Var91 (snoc91 Γ B) A
 := λ x Var91 vz91 vs91 => vs91 _ _ _ (x Var91 vz91 vs91)

def Tm91 : Con91 → Ty91 → Type 1
 := λ Γ A =>
   ∀ (Tm91  : Con91 → Ty91 → Type)
     (var   : ∀ Γ A     , Var91 Γ A → Tm91 Γ A)
     (lam   : ∀ Γ A B   , Tm91 (snoc91 Γ A) B → Tm91 Γ (arr91 A B))
     (app   : ∀ Γ A B   , Tm91 Γ (arr91 A B) → Tm91 Γ A → Tm91 Γ B)
   , Tm91 Γ A

def var91 {Γ A} : Var91 Γ A → Tm91 Γ A
 := λ x Tm91 var91 lam app =>
     var91 _ _ x

def lam91 {Γ A B} : Tm91 (snoc91 Γ A) B → Tm91 Γ (arr91 A B)
 := λ t Tm91 var91 lam91 app =>
     lam91 _ _ _ (t Tm91 var91 lam91 app)

def app91 {Γ A B} : Tm91 Γ (arr91 A B) → Tm91 Γ A → Tm91 Γ B
 := λ t u Tm91 var91 lam91 app91 =>
     app91 _ _ _
         (t Tm91 var91 lam91 app91)
         (u Tm91 var91 lam91 app91)

def v091 {Γ A} : Tm91 (snoc91 Γ A) A
 := var91 vz91

def v191 {Γ A B} : Tm91 (snoc91 (snoc91 Γ A) B) A
 := var91 (vs91 vz91)

def v291 {Γ A B C} : Tm91 (snoc91 (snoc91 (snoc91 Γ A) B) C) A
 := var91 (vs91 (vs91 vz91))

def v391 {Γ A B C D} : Tm91 (snoc91 (snoc91 (snoc91 (snoc91 Γ A) B) C) D) A
 := var91 (vs91 (vs91 (vs91 vz91)))

def v491 {Γ A B C D E} : Tm91 (snoc91 (snoc91 (snoc91 (snoc91 (snoc91 Γ A) B) C) D) E) A
 := var91 (vs91 (vs91 (vs91 (vs91 vz91))))

def test91 {Γ A} : Tm91 Γ (arr91 (arr91 A A) (arr91 A A))
 := lam91 (lam91 (app91 v191 (app91 v191 (app91 v191 (app91 v191 (app91 v191 (app91 v191 v091)))))))


def Ty92 : Type 1
 := ∀ (Ty92 : Type)
      (ι   : Ty92)
      (arr : Ty92 → Ty92 → Ty92)
    , Ty92

def ι92 : Ty92 := λ _ ι92 _ => ι92

def arr92 : Ty92 → Ty92 → Ty92
 := λ A B Ty92 ι92 arr92 =>
     arr92 (A Ty92 ι92 arr92) (B Ty92 ι92 arr92)

def Con92 : Type 1
 := ∀ (Con92  : Type)
      (nil  : Con92)
      (snoc : Con92 → Ty92 → Con92)
    , Con92

def nil92 : Con92
 := λ Con92 nil92 snoc => nil92

def snoc92 : Con92 → Ty92 → Con92
 := λ Γ A Con92 nil92 snoc92 => snoc92 (Γ Con92 nil92 snoc92) A

def Var92 : Con92 → Ty92 → Type 1
 := λ Γ A =>
   ∀ (Var92 : Con92 → Ty92 → Type)
     (vz  : ∀ Γ A, Var92 (snoc92 Γ A) A)
     (vs  : ∀ Γ B A, Var92 Γ A → Var92 (snoc92 Γ B) A)
   , Var92 Γ A

def vz92 {Γ A} : Var92 (snoc92 Γ A) A
 := λ Var92 vz92 vs => vz92 _ _

def vs92 {Γ B A} : Var92 Γ A → Var92 (snoc92 Γ B) A
 := λ x Var92 vz92 vs92 => vs92 _ _ _ (x Var92 vz92 vs92)

def Tm92 : Con92 → Ty92 → Type 1
 := λ Γ A =>
   ∀ (Tm92  : Con92 → Ty92 → Type)
     (var   : ∀ Γ A     , Var92 Γ A → Tm92 Γ A)
     (lam   : ∀ Γ A B   , Tm92 (snoc92 Γ A) B → Tm92 Γ (arr92 A B))
     (app   : ∀ Γ A B   , Tm92 Γ (arr92 A B) → Tm92 Γ A → Tm92 Γ B)
   , Tm92 Γ A

def var92 {Γ A} : Var92 Γ A → Tm92 Γ A
 := λ x Tm92 var92 lam app =>
     var92 _ _ x

def lam92 {Γ A B} : Tm92 (snoc92 Γ A) B → Tm92 Γ (arr92 A B)
 := λ t Tm92 var92 lam92 app =>
     lam92 _ _ _ (t Tm92 var92 lam92 app)

def app92 {Γ A B} : Tm92 Γ (arr92 A B) → Tm92 Γ A → Tm92 Γ B
 := λ t u Tm92 var92 lam92 app92 =>
     app92 _ _ _
         (t Tm92 var92 lam92 app92)
         (u Tm92 var92 lam92 app92)

def v092 {Γ A} : Tm92 (snoc92 Γ A) A
 := var92 vz92

def v192 {Γ A B} : Tm92 (snoc92 (snoc92 Γ A) B) A
 := var92 (vs92 vz92)

def v292 {Γ A B C} : Tm92 (snoc92 (snoc92 (snoc92 Γ A) B) C) A
 := var92 (vs92 (vs92 vz92))

def v392 {Γ A B C D} : Tm92 (snoc92 (snoc92 (snoc92 (snoc92 Γ A) B) C) D) A
 := var92 (vs92 (vs92 (vs92 vz92)))

def v492 {Γ A B C D E} : Tm92 (snoc92 (snoc92 (snoc92 (snoc92 (snoc92 Γ A) B) C) D) E) A
 := var92 (vs92 (vs92 (vs92 (vs92 vz92))))

def test92 {Γ A} : Tm92 Γ (arr92 (arr92 A A) (arr92 A A))
 := lam92 (lam92 (app92 v192 (app92 v192 (app92 v192 (app92 v192 (app92 v192 (app92 v192 v092)))))))


def Ty93 : Type 1
 := ∀ (Ty93 : Type)
      (ι   : Ty93)
      (arr : Ty93 → Ty93 → Ty93)
    , Ty93

def ι93 : Ty93 := λ _ ι93 _ => ι93

def arr93 : Ty93 → Ty93 → Ty93
 := λ A B Ty93 ι93 arr93 =>
     arr93 (A Ty93 ι93 arr93) (B Ty93 ι93 arr93)

def Con93 : Type 1
 := ∀ (Con93  : Type)
      (nil  : Con93)
      (snoc : Con93 → Ty93 → Con93)
    , Con93

def nil93 : Con93
 := λ Con93 nil93 snoc => nil93

def snoc93 : Con93 → Ty93 → Con93
 := λ Γ A Con93 nil93 snoc93 => snoc93 (Γ Con93 nil93 snoc93) A

def Var93 : Con93 → Ty93 → Type 1
 := λ Γ A =>
   ∀ (Var93 : Con93 → Ty93 → Type)
     (vz  : ∀ Γ A, Var93 (snoc93 Γ A) A)
     (vs  : ∀ Γ B A, Var93 Γ A → Var93 (snoc93 Γ B) A)
   , Var93 Γ A

def vz93 {Γ A} : Var93 (snoc93 Γ A) A
 := λ Var93 vz93 vs => vz93 _ _

def vs93 {Γ B A} : Var93 Γ A → Var93 (snoc93 Γ B) A
 := λ x Var93 vz93 vs93 => vs93 _ _ _ (x Var93 vz93 vs93)

def Tm93 : Con93 → Ty93 → Type 1
 := λ Γ A =>
   ∀ (Tm93  : Con93 → Ty93 → Type)
     (var   : ∀ Γ A     , Var93 Γ A → Tm93 Γ A)
     (lam   : ∀ Γ A B   , Tm93 (snoc93 Γ A) B → Tm93 Γ (arr93 A B))
     (app   : ∀ Γ A B   , Tm93 Γ (arr93 A B) → Tm93 Γ A → Tm93 Γ B)
   , Tm93 Γ A

def var93 {Γ A} : Var93 Γ A → Tm93 Γ A
 := λ x Tm93 var93 lam app =>
     var93 _ _ x

def lam93 {Γ A B} : Tm93 (snoc93 Γ A) B → Tm93 Γ (arr93 A B)
 := λ t Tm93 var93 lam93 app =>
     lam93 _ _ _ (t Tm93 var93 lam93 app)

def app93 {Γ A B} : Tm93 Γ (arr93 A B) → Tm93 Γ A → Tm93 Γ B
 := λ t u Tm93 var93 lam93 app93 =>
     app93 _ _ _
         (t Tm93 var93 lam93 app93)
         (u Tm93 var93 lam93 app93)

def v093 {Γ A} : Tm93 (snoc93 Γ A) A
 := var93 vz93

def v193 {Γ A B} : Tm93 (snoc93 (snoc93 Γ A) B) A
 := var93 (vs93 vz93)

def v293 {Γ A B C} : Tm93 (snoc93 (snoc93 (snoc93 Γ A) B) C) A
 := var93 (vs93 (vs93 vz93))

def v393 {Γ A B C D} : Tm93 (snoc93 (snoc93 (snoc93 (snoc93 Γ A) B) C) D) A
 := var93 (vs93 (vs93 (vs93 vz93)))

def v493 {Γ A B C D E} : Tm93 (snoc93 (snoc93 (snoc93 (snoc93 (snoc93 Γ A) B) C) D) E) A
 := var93 (vs93 (vs93 (vs93 (vs93 vz93))))

def test93 {Γ A} : Tm93 Γ (arr93 (arr93 A A) (arr93 A A))
 := lam93 (lam93 (app93 v193 (app93 v193 (app93 v193 (app93 v193 (app93 v193 (app93 v193 v093)))))))


def Ty94 : Type 1
 := ∀ (Ty94 : Type)
      (ι   : Ty94)
      (arr : Ty94 → Ty94 → Ty94)
    , Ty94

def ι94 : Ty94 := λ _ ι94 _ => ι94

def arr94 : Ty94 → Ty94 → Ty94
 := λ A B Ty94 ι94 arr94 =>
     arr94 (A Ty94 ι94 arr94) (B Ty94 ι94 arr94)

def Con94 : Type 1
 := ∀ (Con94  : Type)
      (nil  : Con94)
      (snoc : Con94 → Ty94 → Con94)
    , Con94

def nil94 : Con94
 := λ Con94 nil94 snoc => nil94

def snoc94 : Con94 → Ty94 → Con94
 := λ Γ A Con94 nil94 snoc94 => snoc94 (Γ Con94 nil94 snoc94) A

def Var94 : Con94 → Ty94 → Type 1
 := λ Γ A =>
   ∀ (Var94 : Con94 → Ty94 → Type)
     (vz  : ∀ Γ A, Var94 (snoc94 Γ A) A)
     (vs  : ∀ Γ B A, Var94 Γ A → Var94 (snoc94 Γ B) A)
   , Var94 Γ A

def vz94 {Γ A} : Var94 (snoc94 Γ A) A
 := λ Var94 vz94 vs => vz94 _ _

def vs94 {Γ B A} : Var94 Γ A → Var94 (snoc94 Γ B) A
 := λ x Var94 vz94 vs94 => vs94 _ _ _ (x Var94 vz94 vs94)

def Tm94 : Con94 → Ty94 → Type 1
 := λ Γ A =>
   ∀ (Tm94  : Con94 → Ty94 → Type)
     (var   : ∀ Γ A     , Var94 Γ A → Tm94 Γ A)
     (lam   : ∀ Γ A B   , Tm94 (snoc94 Γ A) B → Tm94 Γ (arr94 A B))
     (app   : ∀ Γ A B   , Tm94 Γ (arr94 A B) → Tm94 Γ A → Tm94 Γ B)
   , Tm94 Γ A

def var94 {Γ A} : Var94 Γ A → Tm94 Γ A
 := λ x Tm94 var94 lam app =>
     var94 _ _ x

def lam94 {Γ A B} : Tm94 (snoc94 Γ A) B → Tm94 Γ (arr94 A B)
 := λ t Tm94 var94 lam94 app =>
     lam94 _ _ _ (t Tm94 var94 lam94 app)

def app94 {Γ A B} : Tm94 Γ (arr94 A B) → Tm94 Γ A → Tm94 Γ B
 := λ t u Tm94 var94 lam94 app94 =>
     app94 _ _ _
         (t Tm94 var94 lam94 app94)
         (u Tm94 var94 lam94 app94)

def v094 {Γ A} : Tm94 (snoc94 Γ A) A
 := var94 vz94

def v194 {Γ A B} : Tm94 (snoc94 (snoc94 Γ A) B) A
 := var94 (vs94 vz94)

def v294 {Γ A B C} : Tm94 (snoc94 (snoc94 (snoc94 Γ A) B) C) A
 := var94 (vs94 (vs94 vz94))

def v394 {Γ A B C D} : Tm94 (snoc94 (snoc94 (snoc94 (snoc94 Γ A) B) C) D) A
 := var94 (vs94 (vs94 (vs94 vz94)))

def v494 {Γ A B C D E} : Tm94 (snoc94 (snoc94 (snoc94 (snoc94 (snoc94 Γ A) B) C) D) E) A
 := var94 (vs94 (vs94 (vs94 (vs94 vz94))))

def test94 {Γ A} : Tm94 Γ (arr94 (arr94 A A) (arr94 A A))
 := lam94 (lam94 (app94 v194 (app94 v194 (app94 v194 (app94 v194 (app94 v194 (app94 v194 v094)))))))


def Ty95 : Type 1
 := ∀ (Ty95 : Type)
      (ι   : Ty95)
      (arr : Ty95 → Ty95 → Ty95)
    , Ty95

def ι95 : Ty95 := λ _ ι95 _ => ι95

def arr95 : Ty95 → Ty95 → Ty95
 := λ A B Ty95 ι95 arr95 =>
     arr95 (A Ty95 ι95 arr95) (B Ty95 ι95 arr95)

def Con95 : Type 1
 := ∀ (Con95  : Type)
      (nil  : Con95)
      (snoc : Con95 → Ty95 → Con95)
    , Con95

def nil95 : Con95
 := λ Con95 nil95 snoc => nil95

def snoc95 : Con95 → Ty95 → Con95
 := λ Γ A Con95 nil95 snoc95 => snoc95 (Γ Con95 nil95 snoc95) A

def Var95 : Con95 → Ty95 → Type 1
 := λ Γ A =>
   ∀ (Var95 : Con95 → Ty95 → Type)
     (vz  : ∀ Γ A, Var95 (snoc95 Γ A) A)
     (vs  : ∀ Γ B A, Var95 Γ A → Var95 (snoc95 Γ B) A)
   , Var95 Γ A

def vz95 {Γ A} : Var95 (snoc95 Γ A) A
 := λ Var95 vz95 vs => vz95 _ _

def vs95 {Γ B A} : Var95 Γ A → Var95 (snoc95 Γ B) A
 := λ x Var95 vz95 vs95 => vs95 _ _ _ (x Var95 vz95 vs95)

def Tm95 : Con95 → Ty95 → Type 1
 := λ Γ A =>
   ∀ (Tm95  : Con95 → Ty95 → Type)
     (var   : ∀ Γ A     , Var95 Γ A → Tm95 Γ A)
     (lam   : ∀ Γ A B   , Tm95 (snoc95 Γ A) B → Tm95 Γ (arr95 A B))
     (app   : ∀ Γ A B   , Tm95 Γ (arr95 A B) → Tm95 Γ A → Tm95 Γ B)
   , Tm95 Γ A

def var95 {Γ A} : Var95 Γ A → Tm95 Γ A
 := λ x Tm95 var95 lam app =>
     var95 _ _ x

def lam95 {Γ A B} : Tm95 (snoc95 Γ A) B → Tm95 Γ (arr95 A B)
 := λ t Tm95 var95 lam95 app =>
     lam95 _ _ _ (t Tm95 var95 lam95 app)

def app95 {Γ A B} : Tm95 Γ (arr95 A B) → Tm95 Γ A → Tm95 Γ B
 := λ t u Tm95 var95 lam95 app95 =>
     app95 _ _ _
         (t Tm95 var95 lam95 app95)
         (u Tm95 var95 lam95 app95)

def v095 {Γ A} : Tm95 (snoc95 Γ A) A
 := var95 vz95

def v195 {Γ A B} : Tm95 (snoc95 (snoc95 Γ A) B) A
 := var95 (vs95 vz95)

def v295 {Γ A B C} : Tm95 (snoc95 (snoc95 (snoc95 Γ A) B) C) A
 := var95 (vs95 (vs95 vz95))

def v395 {Γ A B C D} : Tm95 (snoc95 (snoc95 (snoc95 (snoc95 Γ A) B) C) D) A
 := var95 (vs95 (vs95 (vs95 vz95)))

def v495 {Γ A B C D E} : Tm95 (snoc95 (snoc95 (snoc95 (snoc95 (snoc95 Γ A) B) C) D) E) A
 := var95 (vs95 (vs95 (vs95 (vs95 vz95))))

def test95 {Γ A} : Tm95 Γ (arr95 (arr95 A A) (arr95 A A))
 := lam95 (lam95 (app95 v195 (app95 v195 (app95 v195 (app95 v195 (app95 v195 (app95 v195 v095)))))))


def Ty96 : Type 1
 := ∀ (Ty96 : Type)
      (ι   : Ty96)
      (arr : Ty96 → Ty96 → Ty96)
    , Ty96

def ι96 : Ty96 := λ _ ι96 _ => ι96

def arr96 : Ty96 → Ty96 → Ty96
 := λ A B Ty96 ι96 arr96 =>
     arr96 (A Ty96 ι96 arr96) (B Ty96 ι96 arr96)

def Con96 : Type 1
 := ∀ (Con96  : Type)
      (nil  : Con96)
      (snoc : Con96 → Ty96 → Con96)
    , Con96

def nil96 : Con96
 := λ Con96 nil96 snoc => nil96

def snoc96 : Con96 → Ty96 → Con96
 := λ Γ A Con96 nil96 snoc96 => snoc96 (Γ Con96 nil96 snoc96) A

def Var96 : Con96 → Ty96 → Type 1
 := λ Γ A =>
   ∀ (Var96 : Con96 → Ty96 → Type)
     (vz  : ∀ Γ A, Var96 (snoc96 Γ A) A)
     (vs  : ∀ Γ B A, Var96 Γ A → Var96 (snoc96 Γ B) A)
   , Var96 Γ A

def vz96 {Γ A} : Var96 (snoc96 Γ A) A
 := λ Var96 vz96 vs => vz96 _ _

def vs96 {Γ B A} : Var96 Γ A → Var96 (snoc96 Γ B) A
 := λ x Var96 vz96 vs96 => vs96 _ _ _ (x Var96 vz96 vs96)

def Tm96 : Con96 → Ty96 → Type 1
 := λ Γ A =>
   ∀ (Tm96  : Con96 → Ty96 → Type)
     (var   : ∀ Γ A     , Var96 Γ A → Tm96 Γ A)
     (lam   : ∀ Γ A B   , Tm96 (snoc96 Γ A) B → Tm96 Γ (arr96 A B))
     (app   : ∀ Γ A B   , Tm96 Γ (arr96 A B) → Tm96 Γ A → Tm96 Γ B)
   , Tm96 Γ A

def var96 {Γ A} : Var96 Γ A → Tm96 Γ A
 := λ x Tm96 var96 lam app =>
     var96 _ _ x

def lam96 {Γ A B} : Tm96 (snoc96 Γ A) B → Tm96 Γ (arr96 A B)
 := λ t Tm96 var96 lam96 app =>
     lam96 _ _ _ (t Tm96 var96 lam96 app)

def app96 {Γ A B} : Tm96 Γ (arr96 A B) → Tm96 Γ A → Tm96 Γ B
 := λ t u Tm96 var96 lam96 app96 =>
     app96 _ _ _
         (t Tm96 var96 lam96 app96)
         (u Tm96 var96 lam96 app96)

def v096 {Γ A} : Tm96 (snoc96 Γ A) A
 := var96 vz96

def v196 {Γ A B} : Tm96 (snoc96 (snoc96 Γ A) B) A
 := var96 (vs96 vz96)

def v296 {Γ A B C} : Tm96 (snoc96 (snoc96 (snoc96 Γ A) B) C) A
 := var96 (vs96 (vs96 vz96))

def v396 {Γ A B C D} : Tm96 (snoc96 (snoc96 (snoc96 (snoc96 Γ A) B) C) D) A
 := var96 (vs96 (vs96 (vs96 vz96)))

def v496 {Γ A B C D E} : Tm96 (snoc96 (snoc96 (snoc96 (snoc96 (snoc96 Γ A) B) C) D) E) A
 := var96 (vs96 (vs96 (vs96 (vs96 vz96))))

def test96 {Γ A} : Tm96 Γ (arr96 (arr96 A A) (arr96 A A))
 := lam96 (lam96 (app96 v196 (app96 v196 (app96 v196 (app96 v196 (app96 v196 (app96 v196 v096)))))))


def Ty97 : Type 1
 := ∀ (Ty97 : Type)
      (ι   : Ty97)
      (arr : Ty97 → Ty97 → Ty97)
    , Ty97

def ι97 : Ty97 := λ _ ι97 _ => ι97

def arr97 : Ty97 → Ty97 → Ty97
 := λ A B Ty97 ι97 arr97 =>
     arr97 (A Ty97 ι97 arr97) (B Ty97 ι97 arr97)

def Con97 : Type 1
 := ∀ (Con97  : Type)
      (nil  : Con97)
      (snoc : Con97 → Ty97 → Con97)
    , Con97

def nil97 : Con97
 := λ Con97 nil97 snoc => nil97

def snoc97 : Con97 → Ty97 → Con97
 := λ Γ A Con97 nil97 snoc97 => snoc97 (Γ Con97 nil97 snoc97) A

def Var97 : Con97 → Ty97 → Type 1
 := λ Γ A =>
   ∀ (Var97 : Con97 → Ty97 → Type)
     (vz  : ∀ Γ A, Var97 (snoc97 Γ A) A)
     (vs  : ∀ Γ B A, Var97 Γ A → Var97 (snoc97 Γ B) A)
   , Var97 Γ A

def vz97 {Γ A} : Var97 (snoc97 Γ A) A
 := λ Var97 vz97 vs => vz97 _ _

def vs97 {Γ B A} : Var97 Γ A → Var97 (snoc97 Γ B) A
 := λ x Var97 vz97 vs97 => vs97 _ _ _ (x Var97 vz97 vs97)

def Tm97 : Con97 → Ty97 → Type 1
 := λ Γ A =>
   ∀ (Tm97  : Con97 → Ty97 → Type)
     (var   : ∀ Γ A     , Var97 Γ A → Tm97 Γ A)
     (lam   : ∀ Γ A B   , Tm97 (snoc97 Γ A) B → Tm97 Γ (arr97 A B))
     (app   : ∀ Γ A B   , Tm97 Γ (arr97 A B) → Tm97 Γ A → Tm97 Γ B)
   , Tm97 Γ A

def var97 {Γ A} : Var97 Γ A → Tm97 Γ A
 := λ x Tm97 var97 lam app =>
     var97 _ _ x

def lam97 {Γ A B} : Tm97 (snoc97 Γ A) B → Tm97 Γ (arr97 A B)
 := λ t Tm97 var97 lam97 app =>
     lam97 _ _ _ (t Tm97 var97 lam97 app)

def app97 {Γ A B} : Tm97 Γ (arr97 A B) → Tm97 Γ A → Tm97 Γ B
 := λ t u Tm97 var97 lam97 app97 =>
     app97 _ _ _
         (t Tm97 var97 lam97 app97)
         (u Tm97 var97 lam97 app97)

def v097 {Γ A} : Tm97 (snoc97 Γ A) A
 := var97 vz97

def v197 {Γ A B} : Tm97 (snoc97 (snoc97 Γ A) B) A
 := var97 (vs97 vz97)

def v297 {Γ A B C} : Tm97 (snoc97 (snoc97 (snoc97 Γ A) B) C) A
 := var97 (vs97 (vs97 vz97))

def v397 {Γ A B C D} : Tm97 (snoc97 (snoc97 (snoc97 (snoc97 Γ A) B) C) D) A
 := var97 (vs97 (vs97 (vs97 vz97)))

def v497 {Γ A B C D E} : Tm97 (snoc97 (snoc97 (snoc97 (snoc97 (snoc97 Γ A) B) C) D) E) A
 := var97 (vs97 (vs97 (vs97 (vs97 vz97))))

def test97 {Γ A} : Tm97 Γ (arr97 (arr97 A A) (arr97 A A))
 := lam97 (lam97 (app97 v197 (app97 v197 (app97 v197 (app97 v197 (app97 v197 (app97 v197 v097)))))))


def Ty98 : Type 1
 := ∀ (Ty98 : Type)
      (ι   : Ty98)
      (arr : Ty98 → Ty98 → Ty98)
    , Ty98

def ι98 : Ty98 := λ _ ι98 _ => ι98

def arr98 : Ty98 → Ty98 → Ty98
 := λ A B Ty98 ι98 arr98 =>
     arr98 (A Ty98 ι98 arr98) (B Ty98 ι98 arr98)

def Con98 : Type 1
 := ∀ (Con98  : Type)
      (nil  : Con98)
      (snoc : Con98 → Ty98 → Con98)
    , Con98

def nil98 : Con98
 := λ Con98 nil98 snoc => nil98

def snoc98 : Con98 → Ty98 → Con98
 := λ Γ A Con98 nil98 snoc98 => snoc98 (Γ Con98 nil98 snoc98) A

def Var98 : Con98 → Ty98 → Type 1
 := λ Γ A =>
   ∀ (Var98 : Con98 → Ty98 → Type)
     (vz  : ∀ Γ A, Var98 (snoc98 Γ A) A)
     (vs  : ∀ Γ B A, Var98 Γ A → Var98 (snoc98 Γ B) A)
   , Var98 Γ A

def vz98 {Γ A} : Var98 (snoc98 Γ A) A
 := λ Var98 vz98 vs => vz98 _ _

def vs98 {Γ B A} : Var98 Γ A → Var98 (snoc98 Γ B) A
 := λ x Var98 vz98 vs98 => vs98 _ _ _ (x Var98 vz98 vs98)

def Tm98 : Con98 → Ty98 → Type 1
 := λ Γ A =>
   ∀ (Tm98  : Con98 → Ty98 → Type)
     (var   : ∀ Γ A     , Var98 Γ A → Tm98 Γ A)
     (lam   : ∀ Γ A B   , Tm98 (snoc98 Γ A) B → Tm98 Γ (arr98 A B))
     (app   : ∀ Γ A B   , Tm98 Γ (arr98 A B) → Tm98 Γ A → Tm98 Γ B)
   , Tm98 Γ A

def var98 {Γ A} : Var98 Γ A → Tm98 Γ A
 := λ x Tm98 var98 lam app =>
     var98 _ _ x

def lam98 {Γ A B} : Tm98 (snoc98 Γ A) B → Tm98 Γ (arr98 A B)
 := λ t Tm98 var98 lam98 app =>
     lam98 _ _ _ (t Tm98 var98 lam98 app)

def app98 {Γ A B} : Tm98 Γ (arr98 A B) → Tm98 Γ A → Tm98 Γ B
 := λ t u Tm98 var98 lam98 app98 =>
     app98 _ _ _
         (t Tm98 var98 lam98 app98)
         (u Tm98 var98 lam98 app98)

def v098 {Γ A} : Tm98 (snoc98 Γ A) A
 := var98 vz98

def v198 {Γ A B} : Tm98 (snoc98 (snoc98 Γ A) B) A
 := var98 (vs98 vz98)

def v298 {Γ A B C} : Tm98 (snoc98 (snoc98 (snoc98 Γ A) B) C) A
 := var98 (vs98 (vs98 vz98))

def v398 {Γ A B C D} : Tm98 (snoc98 (snoc98 (snoc98 (snoc98 Γ A) B) C) D) A
 := var98 (vs98 (vs98 (vs98 vz98)))

def v498 {Γ A B C D E} : Tm98 (snoc98 (snoc98 (snoc98 (snoc98 (snoc98 Γ A) B) C) D) E) A
 := var98 (vs98 (vs98 (vs98 (vs98 vz98))))

def test98 {Γ A} : Tm98 Γ (arr98 (arr98 A A) (arr98 A A))
 := lam98 (lam98 (app98 v198 (app98 v198 (app98 v198 (app98 v198 (app98 v198 (app98 v198 v098)))))))


def Ty99 : Type 1
 := ∀ (Ty99 : Type)
      (ι   : Ty99)
      (arr : Ty99 → Ty99 → Ty99)
    , Ty99

def ι99 : Ty99 := λ _ ι99 _ => ι99

def arr99 : Ty99 → Ty99 → Ty99
 := λ A B Ty99 ι99 arr99 =>
     arr99 (A Ty99 ι99 arr99) (B Ty99 ι99 arr99)

def Con99 : Type 1
 := ∀ (Con99  : Type)
      (nil  : Con99)
      (snoc : Con99 → Ty99 → Con99)
    , Con99

def nil99 : Con99
 := λ Con99 nil99 snoc => nil99

def snoc99 : Con99 → Ty99 → Con99
 := λ Γ A Con99 nil99 snoc99 => snoc99 (Γ Con99 nil99 snoc99) A

def Var99 : Con99 → Ty99 → Type 1
 := λ Γ A =>
   ∀ (Var99 : Con99 → Ty99 → Type)
     (vz  : ∀ Γ A, Var99 (snoc99 Γ A) A)
     (vs  : ∀ Γ B A, Var99 Γ A → Var99 (snoc99 Γ B) A)
   , Var99 Γ A

def vz99 {Γ A} : Var99 (snoc99 Γ A) A
 := λ Var99 vz99 vs => vz99 _ _

def vs99 {Γ B A} : Var99 Γ A → Var99 (snoc99 Γ B) A
 := λ x Var99 vz99 vs99 => vs99 _ _ _ (x Var99 vz99 vs99)

def Tm99 : Con99 → Ty99 → Type 1
 := λ Γ A =>
   ∀ (Tm99  : Con99 → Ty99 → Type)
     (var   : ∀ Γ A     , Var99 Γ A → Tm99 Γ A)
     (lam   : ∀ Γ A B   , Tm99 (snoc99 Γ A) B → Tm99 Γ (arr99 A B))
     (app   : ∀ Γ A B   , Tm99 Γ (arr99 A B) → Tm99 Γ A → Tm99 Γ B)
   , Tm99 Γ A

def var99 {Γ A} : Var99 Γ A → Tm99 Γ A
 := λ x Tm99 var99 lam app =>
     var99 _ _ x

def lam99 {Γ A B} : Tm99 (snoc99 Γ A) B → Tm99 Γ (arr99 A B)
 := λ t Tm99 var99 lam99 app =>
     lam99 _ _ _ (t Tm99 var99 lam99 app)

def app99 {Γ A B} : Tm99 Γ (arr99 A B) → Tm99 Γ A → Tm99 Γ B
 := λ t u Tm99 var99 lam99 app99 =>
     app99 _ _ _
         (t Tm99 var99 lam99 app99)
         (u Tm99 var99 lam99 app99)

def v099 {Γ A} : Tm99 (snoc99 Γ A) A
 := var99 vz99

def v199 {Γ A B} : Tm99 (snoc99 (snoc99 Γ A) B) A
 := var99 (vs99 vz99)

def v299 {Γ A B C} : Tm99 (snoc99 (snoc99 (snoc99 Γ A) B) C) A
 := var99 (vs99 (vs99 vz99))

def v399 {Γ A B C D} : Tm99 (snoc99 (snoc99 (snoc99 (snoc99 Γ A) B) C) D) A
 := var99 (vs99 (vs99 (vs99 vz99)))

def v499 {Γ A B C D E} : Tm99 (snoc99 (snoc99 (snoc99 (snoc99 (snoc99 Γ A) B) C) D) E) A
 := var99 (vs99 (vs99 (vs99 (vs99 vz99))))

def test99 {Γ A} : Tm99 Γ (arr99 (arr99 A A) (arr99 A A))
 := lam99 (lam99 (app99 v199 (app99 v199 (app99 v199 (app99 v199 (app99 v199 (app99 v199 v099)))))))


def Ty100 : Type 1
 := ∀ (Ty100 : Type)
      (ι   : Ty100)
      (arr : Ty100 → Ty100 → Ty100)
    , Ty100

def ι100 : Ty100 := λ _ ι100 _ => ι100

def arr100 : Ty100 → Ty100 → Ty100
 := λ A B Ty100 ι100 arr100 =>
     arr100 (A Ty100 ι100 arr100) (B Ty100 ι100 arr100)

def Con100 : Type 1
 := ∀ (Con100  : Type)
      (nil  : Con100)
      (snoc : Con100 → Ty100 → Con100)
    , Con100

def nil100 : Con100
 := λ Con100 nil100 snoc => nil100

def snoc100 : Con100 → Ty100 → Con100
 := λ Γ A Con100 nil100 snoc100 => snoc100 (Γ Con100 nil100 snoc100) A

def Var100 : Con100 → Ty100 → Type 1
 := λ Γ A =>
   ∀ (Var100 : Con100 → Ty100 → Type)
     (vz  : ∀ Γ A, Var100 (snoc100 Γ A) A)
     (vs  : ∀ Γ B A, Var100 Γ A → Var100 (snoc100 Γ B) A)
   , Var100 Γ A

def vz100 {Γ A} : Var100 (snoc100 Γ A) A
 := λ Var100 vz100 vs => vz100 _ _

def vs100 {Γ B A} : Var100 Γ A → Var100 (snoc100 Γ B) A
 := λ x Var100 vz100 vs100 => vs100 _ _ _ (x Var100 vz100 vs100)

def Tm100 : Con100 → Ty100 → Type 1
 := λ Γ A =>
   ∀ (Tm100  : Con100 → Ty100 → Type)
     (var   : ∀ Γ A     , Var100 Γ A → Tm100 Γ A)
     (lam   : ∀ Γ A B   , Tm100 (snoc100 Γ A) B → Tm100 Γ (arr100 A B))
     (app   : ∀ Γ A B   , Tm100 Γ (arr100 A B) → Tm100 Γ A → Tm100 Γ B)
   , Tm100 Γ A

def var100 {Γ A} : Var100 Γ A → Tm100 Γ A
 := λ x Tm100 var100 lam app =>
     var100 _ _ x

def lam100 {Γ A B} : Tm100 (snoc100 Γ A) B → Tm100 Γ (arr100 A B)
 := λ t Tm100 var100 lam100 app =>
     lam100 _ _ _ (t Tm100 var100 lam100 app)

def app100 {Γ A B} : Tm100 Γ (arr100 A B) → Tm100 Γ A → Tm100 Γ B
 := λ t u Tm100 var100 lam100 app100 =>
     app100 _ _ _
         (t Tm100 var100 lam100 app100)
         (u Tm100 var100 lam100 app100)

def v0100 {Γ A} : Tm100 (snoc100 Γ A) A
 := var100 vz100

def v1100 {Γ A B} : Tm100 (snoc100 (snoc100 Γ A) B) A
 := var100 (vs100 vz100)

def v2100 {Γ A B C} : Tm100 (snoc100 (snoc100 (snoc100 Γ A) B) C) A
 := var100 (vs100 (vs100 vz100))

def v3100 {Γ A B C D} : Tm100 (snoc100 (snoc100 (snoc100 (snoc100 Γ A) B) C) D) A
 := var100 (vs100 (vs100 (vs100 vz100)))

def v4100 {Γ A B C D E} : Tm100 (snoc100 (snoc100 (snoc100 (snoc100 (snoc100 Γ A) B) C) D) E) A
 := var100 (vs100 (vs100 (vs100 (vs100 vz100))))

def test100 {Γ A} : Tm100 Γ (arr100 (arr100 A A) (arr100 A A))
 := lam100 (lam100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 (app100 v1100 v0100)))))))


def Ty101 : Type 1
 := ∀ (Ty101 : Type)
      (ι   : Ty101)
      (arr : Ty101 → Ty101 → Ty101)
    , Ty101

def ι101 : Ty101 := λ _ ι101 _ => ι101

def arr101 : Ty101 → Ty101 → Ty101
 := λ A B Ty101 ι101 arr101 =>
     arr101 (A Ty101 ι101 arr101) (B Ty101 ι101 arr101)

def Con101 : Type 1
 := ∀ (Con101  : Type)
      (nil  : Con101)
      (snoc : Con101 → Ty101 → Con101)
    , Con101

def nil101 : Con101
 := λ Con101 nil101 snoc => nil101

def snoc101 : Con101 → Ty101 → Con101
 := λ Γ A Con101 nil101 snoc101 => snoc101 (Γ Con101 nil101 snoc101) A

def Var101 : Con101 → Ty101 → Type 1
 := λ Γ A =>
   ∀ (Var101 : Con101 → Ty101 → Type)
     (vz  : ∀ Γ A, Var101 (snoc101 Γ A) A)
     (vs  : ∀ Γ B A, Var101 Γ A → Var101 (snoc101 Γ B) A)
   , Var101 Γ A

def vz101 {Γ A} : Var101 (snoc101 Γ A) A
 := λ Var101 vz101 vs => vz101 _ _

def vs101 {Γ B A} : Var101 Γ A → Var101 (snoc101 Γ B) A
 := λ x Var101 vz101 vs101 => vs101 _ _ _ (x Var101 vz101 vs101)

def Tm101 : Con101 → Ty101 → Type 1
 := λ Γ A =>
   ∀ (Tm101  : Con101 → Ty101 → Type)
     (var   : ∀ Γ A     , Var101 Γ A → Tm101 Γ A)
     (lam   : ∀ Γ A B   , Tm101 (snoc101 Γ A) B → Tm101 Γ (arr101 A B))
     (app   : ∀ Γ A B   , Tm101 Γ (arr101 A B) → Tm101 Γ A → Tm101 Γ B)
   , Tm101 Γ A

def var101 {Γ A} : Var101 Γ A → Tm101 Γ A
 := λ x Tm101 var101 lam app =>
     var101 _ _ x

def lam101 {Γ A B} : Tm101 (snoc101 Γ A) B → Tm101 Γ (arr101 A B)
 := λ t Tm101 var101 lam101 app =>
     lam101 _ _ _ (t Tm101 var101 lam101 app)

def app101 {Γ A B} : Tm101 Γ (arr101 A B) → Tm101 Γ A → Tm101 Γ B
 := λ t u Tm101 var101 lam101 app101 =>
     app101 _ _ _
         (t Tm101 var101 lam101 app101)
         (u Tm101 var101 lam101 app101)

def v0101 {Γ A} : Tm101 (snoc101 Γ A) A
 := var101 vz101

def v1101 {Γ A B} : Tm101 (snoc101 (snoc101 Γ A) B) A
 := var101 (vs101 vz101)

def v2101 {Γ A B C} : Tm101 (snoc101 (snoc101 (snoc101 Γ A) B) C) A
 := var101 (vs101 (vs101 vz101))

def v3101 {Γ A B C D} : Tm101 (snoc101 (snoc101 (snoc101 (snoc101 Γ A) B) C) D) A
 := var101 (vs101 (vs101 (vs101 vz101)))

def v4101 {Γ A B C D E} : Tm101 (snoc101 (snoc101 (snoc101 (snoc101 (snoc101 Γ A) B) C) D) E) A
 := var101 (vs101 (vs101 (vs101 (vs101 vz101))))

def test101 {Γ A} : Tm101 Γ (arr101 (arr101 A A) (arr101 A A))
 := lam101 (lam101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 (app101 v1101 v0101)))))))


def Ty102 : Type 1
 := ∀ (Ty102 : Type)
      (ι   : Ty102)
      (arr : Ty102 → Ty102 → Ty102)
    , Ty102

def ι102 : Ty102 := λ _ ι102 _ => ι102

def arr102 : Ty102 → Ty102 → Ty102
 := λ A B Ty102 ι102 arr102 =>
     arr102 (A Ty102 ι102 arr102) (B Ty102 ι102 arr102)

def Con102 : Type 1
 := ∀ (Con102  : Type)
      (nil  : Con102)
      (snoc : Con102 → Ty102 → Con102)
    , Con102

def nil102 : Con102
 := λ Con102 nil102 snoc => nil102

def snoc102 : Con102 → Ty102 → Con102
 := λ Γ A Con102 nil102 snoc102 => snoc102 (Γ Con102 nil102 snoc102) A

def Var102 : Con102 → Ty102 → Type 1
 := λ Γ A =>
   ∀ (Var102 : Con102 → Ty102 → Type)
     (vz  : ∀ Γ A, Var102 (snoc102 Γ A) A)
     (vs  : ∀ Γ B A, Var102 Γ A → Var102 (snoc102 Γ B) A)
   , Var102 Γ A

def vz102 {Γ A} : Var102 (snoc102 Γ A) A
 := λ Var102 vz102 vs => vz102 _ _

def vs102 {Γ B A} : Var102 Γ A → Var102 (snoc102 Γ B) A
 := λ x Var102 vz102 vs102 => vs102 _ _ _ (x Var102 vz102 vs102)

def Tm102 : Con102 → Ty102 → Type 1
 := λ Γ A =>
   ∀ (Tm102  : Con102 → Ty102 → Type)
     (var   : ∀ Γ A     , Var102 Γ A → Tm102 Γ A)
     (lam   : ∀ Γ A B   , Tm102 (snoc102 Γ A) B → Tm102 Γ (arr102 A B))
     (app   : ∀ Γ A B   , Tm102 Γ (arr102 A B) → Tm102 Γ A → Tm102 Γ B)
   , Tm102 Γ A

def var102 {Γ A} : Var102 Γ A → Tm102 Γ A
 := λ x Tm102 var102 lam app =>
     var102 _ _ x

def lam102 {Γ A B} : Tm102 (snoc102 Γ A) B → Tm102 Γ (arr102 A B)
 := λ t Tm102 var102 lam102 app =>
     lam102 _ _ _ (t Tm102 var102 lam102 app)

def app102 {Γ A B} : Tm102 Γ (arr102 A B) → Tm102 Γ A → Tm102 Γ B
 := λ t u Tm102 var102 lam102 app102 =>
     app102 _ _ _
         (t Tm102 var102 lam102 app102)
         (u Tm102 var102 lam102 app102)

def v0102 {Γ A} : Tm102 (snoc102 Γ A) A
 := var102 vz102

def v1102 {Γ A B} : Tm102 (snoc102 (snoc102 Γ A) B) A
 := var102 (vs102 vz102)

def v2102 {Γ A B C} : Tm102 (snoc102 (snoc102 (snoc102 Γ A) B) C) A
 := var102 (vs102 (vs102 vz102))

def v3102 {Γ A B C D} : Tm102 (snoc102 (snoc102 (snoc102 (snoc102 Γ A) B) C) D) A
 := var102 (vs102 (vs102 (vs102 vz102)))

def v4102 {Γ A B C D E} : Tm102 (snoc102 (snoc102 (snoc102 (snoc102 (snoc102 Γ A) B) C) D) E) A
 := var102 (vs102 (vs102 (vs102 (vs102 vz102))))

def test102 {Γ A} : Tm102 Γ (arr102 (arr102 A A) (arr102 A A))
 := lam102 (lam102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 (app102 v1102 v0102)))))))


def Ty103 : Type 1
 := ∀ (Ty103 : Type)
      (ι   : Ty103)
      (arr : Ty103 → Ty103 → Ty103)
    , Ty103

def ι103 : Ty103 := λ _ ι103 _ => ι103

def arr103 : Ty103 → Ty103 → Ty103
 := λ A B Ty103 ι103 arr103 =>
     arr103 (A Ty103 ι103 arr103) (B Ty103 ι103 arr103)

def Con103 : Type 1
 := ∀ (Con103  : Type)
      (nil  : Con103)
      (snoc : Con103 → Ty103 → Con103)
    , Con103

def nil103 : Con103
 := λ Con103 nil103 snoc => nil103

def snoc103 : Con103 → Ty103 → Con103
 := λ Γ A Con103 nil103 snoc103 => snoc103 (Γ Con103 nil103 snoc103) A

def Var103 : Con103 → Ty103 → Type 1
 := λ Γ A =>
   ∀ (Var103 : Con103 → Ty103 → Type)
     (vz  : ∀ Γ A, Var103 (snoc103 Γ A) A)
     (vs  : ∀ Γ B A, Var103 Γ A → Var103 (snoc103 Γ B) A)
   , Var103 Γ A

def vz103 {Γ A} : Var103 (snoc103 Γ A) A
 := λ Var103 vz103 vs => vz103 _ _

def vs103 {Γ B A} : Var103 Γ A → Var103 (snoc103 Γ B) A
 := λ x Var103 vz103 vs103 => vs103 _ _ _ (x Var103 vz103 vs103)

def Tm103 : Con103 → Ty103 → Type 1
 := λ Γ A =>
   ∀ (Tm103  : Con103 → Ty103 → Type)
     (var   : ∀ Γ A     , Var103 Γ A → Tm103 Γ A)
     (lam   : ∀ Γ A B   , Tm103 (snoc103 Γ A) B → Tm103 Γ (arr103 A B))
     (app   : ∀ Γ A B   , Tm103 Γ (arr103 A B) → Tm103 Γ A → Tm103 Γ B)
   , Tm103 Γ A

def var103 {Γ A} : Var103 Γ A → Tm103 Γ A
 := λ x Tm103 var103 lam app =>
     var103 _ _ x

def lam103 {Γ A B} : Tm103 (snoc103 Γ A) B → Tm103 Γ (arr103 A B)
 := λ t Tm103 var103 lam103 app =>
     lam103 _ _ _ (t Tm103 var103 lam103 app)

def app103 {Γ A B} : Tm103 Γ (arr103 A B) → Tm103 Γ A → Tm103 Γ B
 := λ t u Tm103 var103 lam103 app103 =>
     app103 _ _ _
         (t Tm103 var103 lam103 app103)
         (u Tm103 var103 lam103 app103)

def v0103 {Γ A} : Tm103 (snoc103 Γ A) A
 := var103 vz103

def v1103 {Γ A B} : Tm103 (snoc103 (snoc103 Γ A) B) A
 := var103 (vs103 vz103)

def v2103 {Γ A B C} : Tm103 (snoc103 (snoc103 (snoc103 Γ A) B) C) A
 := var103 (vs103 (vs103 vz103))

def v3103 {Γ A B C D} : Tm103 (snoc103 (snoc103 (snoc103 (snoc103 Γ A) B) C) D) A
 := var103 (vs103 (vs103 (vs103 vz103)))

def v4103 {Γ A B C D E} : Tm103 (snoc103 (snoc103 (snoc103 (snoc103 (snoc103 Γ A) B) C) D) E) A
 := var103 (vs103 (vs103 (vs103 (vs103 vz103))))

def test103 {Γ A} : Tm103 Γ (arr103 (arr103 A A) (arr103 A A))
 := lam103 (lam103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 (app103 v1103 v0103)))))))


def Ty104 : Type 1
 := ∀ (Ty104 : Type)
      (ι   : Ty104)
      (arr : Ty104 → Ty104 → Ty104)
    , Ty104

def ι104 : Ty104 := λ _ ι104 _ => ι104

def arr104 : Ty104 → Ty104 → Ty104
 := λ A B Ty104 ι104 arr104 =>
     arr104 (A Ty104 ι104 arr104) (B Ty104 ι104 arr104)

def Con104 : Type 1
 := ∀ (Con104  : Type)
      (nil  : Con104)
      (snoc : Con104 → Ty104 → Con104)
    , Con104

def nil104 : Con104
 := λ Con104 nil104 snoc => nil104

def snoc104 : Con104 → Ty104 → Con104
 := λ Γ A Con104 nil104 snoc104 => snoc104 (Γ Con104 nil104 snoc104) A

def Var104 : Con104 → Ty104 → Type 1
 := λ Γ A =>
   ∀ (Var104 : Con104 → Ty104 → Type)
     (vz  : ∀ Γ A, Var104 (snoc104 Γ A) A)
     (vs  : ∀ Γ B A, Var104 Γ A → Var104 (snoc104 Γ B) A)
   , Var104 Γ A

def vz104 {Γ A} : Var104 (snoc104 Γ A) A
 := λ Var104 vz104 vs => vz104 _ _

def vs104 {Γ B A} : Var104 Γ A → Var104 (snoc104 Γ B) A
 := λ x Var104 vz104 vs104 => vs104 _ _ _ (x Var104 vz104 vs104)

def Tm104 : Con104 → Ty104 → Type 1
 := λ Γ A =>
   ∀ (Tm104  : Con104 → Ty104 → Type)
     (var   : ∀ Γ A     , Var104 Γ A → Tm104 Γ A)
     (lam   : ∀ Γ A B   , Tm104 (snoc104 Γ A) B → Tm104 Γ (arr104 A B))
     (app   : ∀ Γ A B   , Tm104 Γ (arr104 A B) → Tm104 Γ A → Tm104 Γ B)
   , Tm104 Γ A

def var104 {Γ A} : Var104 Γ A → Tm104 Γ A
 := λ x Tm104 var104 lam app =>
     var104 _ _ x

def lam104 {Γ A B} : Tm104 (snoc104 Γ A) B → Tm104 Γ (arr104 A B)
 := λ t Tm104 var104 lam104 app =>
     lam104 _ _ _ (t Tm104 var104 lam104 app)

def app104 {Γ A B} : Tm104 Γ (arr104 A B) → Tm104 Γ A → Tm104 Γ B
 := λ t u Tm104 var104 lam104 app104 =>
     app104 _ _ _
         (t Tm104 var104 lam104 app104)
         (u Tm104 var104 lam104 app104)

def v0104 {Γ A} : Tm104 (snoc104 Γ A) A
 := var104 vz104

def v1104 {Γ A B} : Tm104 (snoc104 (snoc104 Γ A) B) A
 := var104 (vs104 vz104)

def v2104 {Γ A B C} : Tm104 (snoc104 (snoc104 (snoc104 Γ A) B) C) A
 := var104 (vs104 (vs104 vz104))

def v3104 {Γ A B C D} : Tm104 (snoc104 (snoc104 (snoc104 (snoc104 Γ A) B) C) D) A
 := var104 (vs104 (vs104 (vs104 vz104)))

def v4104 {Γ A B C D E} : Tm104 (snoc104 (snoc104 (snoc104 (snoc104 (snoc104 Γ A) B) C) D) E) A
 := var104 (vs104 (vs104 (vs104 (vs104 vz104))))

def test104 {Γ A} : Tm104 Γ (arr104 (arr104 A A) (arr104 A A))
 := lam104 (lam104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 (app104 v1104 v0104)))))))


def Ty105 : Type 1
 := ∀ (Ty105 : Type)
      (ι   : Ty105)
      (arr : Ty105 → Ty105 → Ty105)
    , Ty105

def ι105 : Ty105 := λ _ ι105 _ => ι105

def arr105 : Ty105 → Ty105 → Ty105
 := λ A B Ty105 ι105 arr105 =>
     arr105 (A Ty105 ι105 arr105) (B Ty105 ι105 arr105)

def Con105 : Type 1
 := ∀ (Con105  : Type)
      (nil  : Con105)
      (snoc : Con105 → Ty105 → Con105)
    , Con105

def nil105 : Con105
 := λ Con105 nil105 snoc => nil105

def snoc105 : Con105 → Ty105 → Con105
 := λ Γ A Con105 nil105 snoc105 => snoc105 (Γ Con105 nil105 snoc105) A

def Var105 : Con105 → Ty105 → Type 1
 := λ Γ A =>
   ∀ (Var105 : Con105 → Ty105 → Type)
     (vz  : ∀ Γ A, Var105 (snoc105 Γ A) A)
     (vs  : ∀ Γ B A, Var105 Γ A → Var105 (snoc105 Γ B) A)
   , Var105 Γ A

def vz105 {Γ A} : Var105 (snoc105 Γ A) A
 := λ Var105 vz105 vs => vz105 _ _

def vs105 {Γ B A} : Var105 Γ A → Var105 (snoc105 Γ B) A
 := λ x Var105 vz105 vs105 => vs105 _ _ _ (x Var105 vz105 vs105)

def Tm105 : Con105 → Ty105 → Type 1
 := λ Γ A =>
   ∀ (Tm105  : Con105 → Ty105 → Type)
     (var   : ∀ Γ A     , Var105 Γ A → Tm105 Γ A)
     (lam   : ∀ Γ A B   , Tm105 (snoc105 Γ A) B → Tm105 Γ (arr105 A B))
     (app   : ∀ Γ A B   , Tm105 Γ (arr105 A B) → Tm105 Γ A → Tm105 Γ B)
   , Tm105 Γ A

def var105 {Γ A} : Var105 Γ A → Tm105 Γ A
 := λ x Tm105 var105 lam app =>
     var105 _ _ x

def lam105 {Γ A B} : Tm105 (snoc105 Γ A) B → Tm105 Γ (arr105 A B)
 := λ t Tm105 var105 lam105 app =>
     lam105 _ _ _ (t Tm105 var105 lam105 app)

def app105 {Γ A B} : Tm105 Γ (arr105 A B) → Tm105 Γ A → Tm105 Γ B
 := λ t u Tm105 var105 lam105 app105 =>
     app105 _ _ _
         (t Tm105 var105 lam105 app105)
         (u Tm105 var105 lam105 app105)

def v0105 {Γ A} : Tm105 (snoc105 Γ A) A
 := var105 vz105

def v1105 {Γ A B} : Tm105 (snoc105 (snoc105 Γ A) B) A
 := var105 (vs105 vz105)

def v2105 {Γ A B C} : Tm105 (snoc105 (snoc105 (snoc105 Γ A) B) C) A
 := var105 (vs105 (vs105 vz105))

def v3105 {Γ A B C D} : Tm105 (snoc105 (snoc105 (snoc105 (snoc105 Γ A) B) C) D) A
 := var105 (vs105 (vs105 (vs105 vz105)))

def v4105 {Γ A B C D E} : Tm105 (snoc105 (snoc105 (snoc105 (snoc105 (snoc105 Γ A) B) C) D) E) A
 := var105 (vs105 (vs105 (vs105 (vs105 vz105))))

def test105 {Γ A} : Tm105 Γ (arr105 (arr105 A A) (arr105 A A))
 := lam105 (lam105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 (app105 v1105 v0105)))))))


def Ty106 : Type 1
 := ∀ (Ty106 : Type)
      (ι   : Ty106)
      (arr : Ty106 → Ty106 → Ty106)
    , Ty106

def ι106 : Ty106 := λ _ ι106 _ => ι106

def arr106 : Ty106 → Ty106 → Ty106
 := λ A B Ty106 ι106 arr106 =>
     arr106 (A Ty106 ι106 arr106) (B Ty106 ι106 arr106)

def Con106 : Type 1
 := ∀ (Con106  : Type)
      (nil  : Con106)
      (snoc : Con106 → Ty106 → Con106)
    , Con106

def nil106 : Con106
 := λ Con106 nil106 snoc => nil106

def snoc106 : Con106 → Ty106 → Con106
 := λ Γ A Con106 nil106 snoc106 => snoc106 (Γ Con106 nil106 snoc106) A

def Var106 : Con106 → Ty106 → Type 1
 := λ Γ A =>
   ∀ (Var106 : Con106 → Ty106 → Type)
     (vz  : ∀ Γ A, Var106 (snoc106 Γ A) A)
     (vs  : ∀ Γ B A, Var106 Γ A → Var106 (snoc106 Γ B) A)
   , Var106 Γ A

def vz106 {Γ A} : Var106 (snoc106 Γ A) A
 := λ Var106 vz106 vs => vz106 _ _

def vs106 {Γ B A} : Var106 Γ A → Var106 (snoc106 Γ B) A
 := λ x Var106 vz106 vs106 => vs106 _ _ _ (x Var106 vz106 vs106)

def Tm106 : Con106 → Ty106 → Type 1
 := λ Γ A =>
   ∀ (Tm106  : Con106 → Ty106 → Type)
     (var   : ∀ Γ A     , Var106 Γ A → Tm106 Γ A)
     (lam   : ∀ Γ A B   , Tm106 (snoc106 Γ A) B → Tm106 Γ (arr106 A B))
     (app   : ∀ Γ A B   , Tm106 Γ (arr106 A B) → Tm106 Γ A → Tm106 Γ B)
   , Tm106 Γ A

def var106 {Γ A} : Var106 Γ A → Tm106 Γ A
 := λ x Tm106 var106 lam app =>
     var106 _ _ x

def lam106 {Γ A B} : Tm106 (snoc106 Γ A) B → Tm106 Γ (arr106 A B)
 := λ t Tm106 var106 lam106 app =>
     lam106 _ _ _ (t Tm106 var106 lam106 app)

def app106 {Γ A B} : Tm106 Γ (arr106 A B) → Tm106 Γ A → Tm106 Γ B
 := λ t u Tm106 var106 lam106 app106 =>
     app106 _ _ _
         (t Tm106 var106 lam106 app106)
         (u Tm106 var106 lam106 app106)

def v0106 {Γ A} : Tm106 (snoc106 Γ A) A
 := var106 vz106

def v1106 {Γ A B} : Tm106 (snoc106 (snoc106 Γ A) B) A
 := var106 (vs106 vz106)

def v2106 {Γ A B C} : Tm106 (snoc106 (snoc106 (snoc106 Γ A) B) C) A
 := var106 (vs106 (vs106 vz106))

def v3106 {Γ A B C D} : Tm106 (snoc106 (snoc106 (snoc106 (snoc106 Γ A) B) C) D) A
 := var106 (vs106 (vs106 (vs106 vz106)))

def v4106 {Γ A B C D E} : Tm106 (snoc106 (snoc106 (snoc106 (snoc106 (snoc106 Γ A) B) C) D) E) A
 := var106 (vs106 (vs106 (vs106 (vs106 vz106))))

def test106 {Γ A} : Tm106 Γ (arr106 (arr106 A A) (arr106 A A))
 := lam106 (lam106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 (app106 v1106 v0106)))))))


def Ty107 : Type 1
 := ∀ (Ty107 : Type)
      (ι   : Ty107)
      (arr : Ty107 → Ty107 → Ty107)
    , Ty107

def ι107 : Ty107 := λ _ ι107 _ => ι107

def arr107 : Ty107 → Ty107 → Ty107
 := λ A B Ty107 ι107 arr107 =>
     arr107 (A Ty107 ι107 arr107) (B Ty107 ι107 arr107)

def Con107 : Type 1
 := ∀ (Con107  : Type)
      (nil  : Con107)
      (snoc : Con107 → Ty107 → Con107)
    , Con107

def nil107 : Con107
 := λ Con107 nil107 snoc => nil107

def snoc107 : Con107 → Ty107 → Con107
 := λ Γ A Con107 nil107 snoc107 => snoc107 (Γ Con107 nil107 snoc107) A

def Var107 : Con107 → Ty107 → Type 1
 := λ Γ A =>
   ∀ (Var107 : Con107 → Ty107 → Type)
     (vz  : ∀ Γ A, Var107 (snoc107 Γ A) A)
     (vs  : ∀ Γ B A, Var107 Γ A → Var107 (snoc107 Γ B) A)
   , Var107 Γ A

def vz107 {Γ A} : Var107 (snoc107 Γ A) A
 := λ Var107 vz107 vs => vz107 _ _

def vs107 {Γ B A} : Var107 Γ A → Var107 (snoc107 Γ B) A
 := λ x Var107 vz107 vs107 => vs107 _ _ _ (x Var107 vz107 vs107)

def Tm107 : Con107 → Ty107 → Type 1
 := λ Γ A =>
   ∀ (Tm107  : Con107 → Ty107 → Type)
     (var   : ∀ Γ A     , Var107 Γ A → Tm107 Γ A)
     (lam   : ∀ Γ A B   , Tm107 (snoc107 Γ A) B → Tm107 Γ (arr107 A B))
     (app   : ∀ Γ A B   , Tm107 Γ (arr107 A B) → Tm107 Γ A → Tm107 Γ B)
   , Tm107 Γ A

def var107 {Γ A} : Var107 Γ A → Tm107 Γ A
 := λ x Tm107 var107 lam app =>
     var107 _ _ x

def lam107 {Γ A B} : Tm107 (snoc107 Γ A) B → Tm107 Γ (arr107 A B)
 := λ t Tm107 var107 lam107 app =>
     lam107 _ _ _ (t Tm107 var107 lam107 app)

def app107 {Γ A B} : Tm107 Γ (arr107 A B) → Tm107 Γ A → Tm107 Γ B
 := λ t u Tm107 var107 lam107 app107 =>
     app107 _ _ _
         (t Tm107 var107 lam107 app107)
         (u Tm107 var107 lam107 app107)

def v0107 {Γ A} : Tm107 (snoc107 Γ A) A
 := var107 vz107

def v1107 {Γ A B} : Tm107 (snoc107 (snoc107 Γ A) B) A
 := var107 (vs107 vz107)

def v2107 {Γ A B C} : Tm107 (snoc107 (snoc107 (snoc107 Γ A) B) C) A
 := var107 (vs107 (vs107 vz107))

def v3107 {Γ A B C D} : Tm107 (snoc107 (snoc107 (snoc107 (snoc107 Γ A) B) C) D) A
 := var107 (vs107 (vs107 (vs107 vz107)))

def v4107 {Γ A B C D E} : Tm107 (snoc107 (snoc107 (snoc107 (snoc107 (snoc107 Γ A) B) C) D) E) A
 := var107 (vs107 (vs107 (vs107 (vs107 vz107))))

def test107 {Γ A} : Tm107 Γ (arr107 (arr107 A A) (arr107 A A))
 := lam107 (lam107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 (app107 v1107 v0107)))))))


def Ty108 : Type 1
 := ∀ (Ty108 : Type)
      (ι   : Ty108)
      (arr : Ty108 → Ty108 → Ty108)
    , Ty108

def ι108 : Ty108 := λ _ ι108 _ => ι108

def arr108 : Ty108 → Ty108 → Ty108
 := λ A B Ty108 ι108 arr108 =>
     arr108 (A Ty108 ι108 arr108) (B Ty108 ι108 arr108)

def Con108 : Type 1
 := ∀ (Con108  : Type)
      (nil  : Con108)
      (snoc : Con108 → Ty108 → Con108)
    , Con108

def nil108 : Con108
 := λ Con108 nil108 snoc => nil108

def snoc108 : Con108 → Ty108 → Con108
 := λ Γ A Con108 nil108 snoc108 => snoc108 (Γ Con108 nil108 snoc108) A

def Var108 : Con108 → Ty108 → Type 1
 := λ Γ A =>
   ∀ (Var108 : Con108 → Ty108 → Type)
     (vz  : ∀ Γ A, Var108 (snoc108 Γ A) A)
     (vs  : ∀ Γ B A, Var108 Γ A → Var108 (snoc108 Γ B) A)
   , Var108 Γ A

def vz108 {Γ A} : Var108 (snoc108 Γ A) A
 := λ Var108 vz108 vs => vz108 _ _

def vs108 {Γ B A} : Var108 Γ A → Var108 (snoc108 Γ B) A
 := λ x Var108 vz108 vs108 => vs108 _ _ _ (x Var108 vz108 vs108)

def Tm108 : Con108 → Ty108 → Type 1
 := λ Γ A =>
   ∀ (Tm108  : Con108 → Ty108 → Type)
     (var   : ∀ Γ A     , Var108 Γ A → Tm108 Γ A)
     (lam   : ∀ Γ A B   , Tm108 (snoc108 Γ A) B → Tm108 Γ (arr108 A B))
     (app   : ∀ Γ A B   , Tm108 Γ (arr108 A B) → Tm108 Γ A → Tm108 Γ B)
   , Tm108 Γ A

def var108 {Γ A} : Var108 Γ A → Tm108 Γ A
 := λ x Tm108 var108 lam app =>
     var108 _ _ x

def lam108 {Γ A B} : Tm108 (snoc108 Γ A) B → Tm108 Γ (arr108 A B)
 := λ t Tm108 var108 lam108 app =>
     lam108 _ _ _ (t Tm108 var108 lam108 app)

def app108 {Γ A B} : Tm108 Γ (arr108 A B) → Tm108 Γ A → Tm108 Γ B
 := λ t u Tm108 var108 lam108 app108 =>
     app108 _ _ _
         (t Tm108 var108 lam108 app108)
         (u Tm108 var108 lam108 app108)

def v0108 {Γ A} : Tm108 (snoc108 Γ A) A
 := var108 vz108

def v1108 {Γ A B} : Tm108 (snoc108 (snoc108 Γ A) B) A
 := var108 (vs108 vz108)

def v2108 {Γ A B C} : Tm108 (snoc108 (snoc108 (snoc108 Γ A) B) C) A
 := var108 (vs108 (vs108 vz108))

def v3108 {Γ A B C D} : Tm108 (snoc108 (snoc108 (snoc108 (snoc108 Γ A) B) C) D) A
 := var108 (vs108 (vs108 (vs108 vz108)))

def v4108 {Γ A B C D E} : Tm108 (snoc108 (snoc108 (snoc108 (snoc108 (snoc108 Γ A) B) C) D) E) A
 := var108 (vs108 (vs108 (vs108 (vs108 vz108))))

def test108 {Γ A} : Tm108 Γ (arr108 (arr108 A A) (arr108 A A))
 := lam108 (lam108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 (app108 v1108 v0108)))))))


def Ty109 : Type 1
 := ∀ (Ty109 : Type)
      (ι   : Ty109)
      (arr : Ty109 → Ty109 → Ty109)
    , Ty109

def ι109 : Ty109 := λ _ ι109 _ => ι109

def arr109 : Ty109 → Ty109 → Ty109
 := λ A B Ty109 ι109 arr109 =>
     arr109 (A Ty109 ι109 arr109) (B Ty109 ι109 arr109)

def Con109 : Type 1
 := ∀ (Con109  : Type)
      (nil  : Con109)
      (snoc : Con109 → Ty109 → Con109)
    , Con109

def nil109 : Con109
 := λ Con109 nil109 snoc => nil109

def snoc109 : Con109 → Ty109 → Con109
 := λ Γ A Con109 nil109 snoc109 => snoc109 (Γ Con109 nil109 snoc109) A

def Var109 : Con109 → Ty109 → Type 1
 := λ Γ A =>
   ∀ (Var109 : Con109 → Ty109 → Type)
     (vz  : ∀ Γ A, Var109 (snoc109 Γ A) A)
     (vs  : ∀ Γ B A, Var109 Γ A → Var109 (snoc109 Γ B) A)
   , Var109 Γ A

def vz109 {Γ A} : Var109 (snoc109 Γ A) A
 := λ Var109 vz109 vs => vz109 _ _

def vs109 {Γ B A} : Var109 Γ A → Var109 (snoc109 Γ B) A
 := λ x Var109 vz109 vs109 => vs109 _ _ _ (x Var109 vz109 vs109)

def Tm109 : Con109 → Ty109 → Type 1
 := λ Γ A =>
   ∀ (Tm109  : Con109 → Ty109 → Type)
     (var   : ∀ Γ A     , Var109 Γ A → Tm109 Γ A)
     (lam   : ∀ Γ A B   , Tm109 (snoc109 Γ A) B → Tm109 Γ (arr109 A B))
     (app   : ∀ Γ A B   , Tm109 Γ (arr109 A B) → Tm109 Γ A → Tm109 Γ B)
   , Tm109 Γ A

def var109 {Γ A} : Var109 Γ A → Tm109 Γ A
 := λ x Tm109 var109 lam app =>
     var109 _ _ x

def lam109 {Γ A B} : Tm109 (snoc109 Γ A) B → Tm109 Γ (arr109 A B)
 := λ t Tm109 var109 lam109 app =>
     lam109 _ _ _ (t Tm109 var109 lam109 app)

def app109 {Γ A B} : Tm109 Γ (arr109 A B) → Tm109 Γ A → Tm109 Γ B
 := λ t u Tm109 var109 lam109 app109 =>
     app109 _ _ _
         (t Tm109 var109 lam109 app109)
         (u Tm109 var109 lam109 app109)

def v0109 {Γ A} : Tm109 (snoc109 Γ A) A
 := var109 vz109

def v1109 {Γ A B} : Tm109 (snoc109 (snoc109 Γ A) B) A
 := var109 (vs109 vz109)

def v2109 {Γ A B C} : Tm109 (snoc109 (snoc109 (snoc109 Γ A) B) C) A
 := var109 (vs109 (vs109 vz109))

def v3109 {Γ A B C D} : Tm109 (snoc109 (snoc109 (snoc109 (snoc109 Γ A) B) C) D) A
 := var109 (vs109 (vs109 (vs109 vz109)))

def v4109 {Γ A B C D E} : Tm109 (snoc109 (snoc109 (snoc109 (snoc109 (snoc109 Γ A) B) C) D) E) A
 := var109 (vs109 (vs109 (vs109 (vs109 vz109))))

def test109 {Γ A} : Tm109 Γ (arr109 (arr109 A A) (arr109 A A))
 := lam109 (lam109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 (app109 v1109 v0109)))))))


def Ty110 : Type 1
 := ∀ (Ty110 : Type)
      (ι   : Ty110)
      (arr : Ty110 → Ty110 → Ty110)
    , Ty110

def ι110 : Ty110 := λ _ ι110 _ => ι110

def arr110 : Ty110 → Ty110 → Ty110
 := λ A B Ty110 ι110 arr110 =>
     arr110 (A Ty110 ι110 arr110) (B Ty110 ι110 arr110)

def Con110 : Type 1
 := ∀ (Con110  : Type)
      (nil  : Con110)
      (snoc : Con110 → Ty110 → Con110)
    , Con110

def nil110 : Con110
 := λ Con110 nil110 snoc => nil110

def snoc110 : Con110 → Ty110 → Con110
 := λ Γ A Con110 nil110 snoc110 => snoc110 (Γ Con110 nil110 snoc110) A

def Var110 : Con110 → Ty110 → Type 1
 := λ Γ A =>
   ∀ (Var110 : Con110 → Ty110 → Type)
     (vz  : ∀ Γ A, Var110 (snoc110 Γ A) A)
     (vs  : ∀ Γ B A, Var110 Γ A → Var110 (snoc110 Γ B) A)
   , Var110 Γ A

def vz110 {Γ A} : Var110 (snoc110 Γ A) A
 := λ Var110 vz110 vs => vz110 _ _

def vs110 {Γ B A} : Var110 Γ A → Var110 (snoc110 Γ B) A
 := λ x Var110 vz110 vs110 => vs110 _ _ _ (x Var110 vz110 vs110)

def Tm110 : Con110 → Ty110 → Type 1
 := λ Γ A =>
   ∀ (Tm110  : Con110 → Ty110 → Type)
     (var   : ∀ Γ A     , Var110 Γ A → Tm110 Γ A)
     (lam   : ∀ Γ A B   , Tm110 (snoc110 Γ A) B → Tm110 Γ (arr110 A B))
     (app   : ∀ Γ A B   , Tm110 Γ (arr110 A B) → Tm110 Γ A → Tm110 Γ B)
   , Tm110 Γ A

def var110 {Γ A} : Var110 Γ A → Tm110 Γ A
 := λ x Tm110 var110 lam app =>
     var110 _ _ x

def lam110 {Γ A B} : Tm110 (snoc110 Γ A) B → Tm110 Γ (arr110 A B)
 := λ t Tm110 var110 lam110 app =>
     lam110 _ _ _ (t Tm110 var110 lam110 app)

def app110 {Γ A B} : Tm110 Γ (arr110 A B) → Tm110 Γ A → Tm110 Γ B
 := λ t u Tm110 var110 lam110 app110 =>
     app110 _ _ _
         (t Tm110 var110 lam110 app110)
         (u Tm110 var110 lam110 app110)

def v0110 {Γ A} : Tm110 (snoc110 Γ A) A
 := var110 vz110

def v1110 {Γ A B} : Tm110 (snoc110 (snoc110 Γ A) B) A
 := var110 (vs110 vz110)

def v2110 {Γ A B C} : Tm110 (snoc110 (snoc110 (snoc110 Γ A) B) C) A
 := var110 (vs110 (vs110 vz110))

def v3110 {Γ A B C D} : Tm110 (snoc110 (snoc110 (snoc110 (snoc110 Γ A) B) C) D) A
 := var110 (vs110 (vs110 (vs110 vz110)))

def v4110 {Γ A B C D E} : Tm110 (snoc110 (snoc110 (snoc110 (snoc110 (snoc110 Γ A) B) C) D) E) A
 := var110 (vs110 (vs110 (vs110 (vs110 vz110))))

def test110 {Γ A} : Tm110 Γ (arr110 (arr110 A A) (arr110 A A))
 := lam110 (lam110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 (app110 v1110 v0110)))))))


def Ty111 : Type 1
 := ∀ (Ty111 : Type)
      (ι   : Ty111)
      (arr : Ty111 → Ty111 → Ty111)
    , Ty111

def ι111 : Ty111 := λ _ ι111 _ => ι111

def arr111 : Ty111 → Ty111 → Ty111
 := λ A B Ty111 ι111 arr111 =>
     arr111 (A Ty111 ι111 arr111) (B Ty111 ι111 arr111)

def Con111 : Type 1
 := ∀ (Con111  : Type)
      (nil  : Con111)
      (snoc : Con111 → Ty111 → Con111)
    , Con111

def nil111 : Con111
 := λ Con111 nil111 snoc => nil111

def snoc111 : Con111 → Ty111 → Con111
 := λ Γ A Con111 nil111 snoc111 => snoc111 (Γ Con111 nil111 snoc111) A

def Var111 : Con111 → Ty111 → Type 1
 := λ Γ A =>
   ∀ (Var111 : Con111 → Ty111 → Type)
     (vz  : ∀ Γ A, Var111 (snoc111 Γ A) A)
     (vs  : ∀ Γ B A, Var111 Γ A → Var111 (snoc111 Γ B) A)
   , Var111 Γ A

def vz111 {Γ A} : Var111 (snoc111 Γ A) A
 := λ Var111 vz111 vs => vz111 _ _

def vs111 {Γ B A} : Var111 Γ A → Var111 (snoc111 Γ B) A
 := λ x Var111 vz111 vs111 => vs111 _ _ _ (x Var111 vz111 vs111)

def Tm111 : Con111 → Ty111 → Type 1
 := λ Γ A =>
   ∀ (Tm111  : Con111 → Ty111 → Type)
     (var   : ∀ Γ A     , Var111 Γ A → Tm111 Γ A)
     (lam   : ∀ Γ A B   , Tm111 (snoc111 Γ A) B → Tm111 Γ (arr111 A B))
     (app   : ∀ Γ A B   , Tm111 Γ (arr111 A B) → Tm111 Γ A → Tm111 Γ B)
   , Tm111 Γ A

def var111 {Γ A} : Var111 Γ A → Tm111 Γ A
 := λ x Tm111 var111 lam app =>
     var111 _ _ x

def lam111 {Γ A B} : Tm111 (snoc111 Γ A) B → Tm111 Γ (arr111 A B)
 := λ t Tm111 var111 lam111 app =>
     lam111 _ _ _ (t Tm111 var111 lam111 app)

def app111 {Γ A B} : Tm111 Γ (arr111 A B) → Tm111 Γ A → Tm111 Γ B
 := λ t u Tm111 var111 lam111 app111 =>
     app111 _ _ _
         (t Tm111 var111 lam111 app111)
         (u Tm111 var111 lam111 app111)

def v0111 {Γ A} : Tm111 (snoc111 Γ A) A
 := var111 vz111

def v1111 {Γ A B} : Tm111 (snoc111 (snoc111 Γ A) B) A
 := var111 (vs111 vz111)

def v2111 {Γ A B C} : Tm111 (snoc111 (snoc111 (snoc111 Γ A) B) C) A
 := var111 (vs111 (vs111 vz111))

def v3111 {Γ A B C D} : Tm111 (snoc111 (snoc111 (snoc111 (snoc111 Γ A) B) C) D) A
 := var111 (vs111 (vs111 (vs111 vz111)))

def v4111 {Γ A B C D E} : Tm111 (snoc111 (snoc111 (snoc111 (snoc111 (snoc111 Γ A) B) C) D) E) A
 := var111 (vs111 (vs111 (vs111 (vs111 vz111))))

def test111 {Γ A} : Tm111 Γ (arr111 (arr111 A A) (arr111 A A))
 := lam111 (lam111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 (app111 v1111 v0111)))))))


def Ty112 : Type 1
 := ∀ (Ty112 : Type)
      (ι   : Ty112)
      (arr : Ty112 → Ty112 → Ty112)
    , Ty112

def ι112 : Ty112 := λ _ ι112 _ => ι112

def arr112 : Ty112 → Ty112 → Ty112
 := λ A B Ty112 ι112 arr112 =>
     arr112 (A Ty112 ι112 arr112) (B Ty112 ι112 arr112)

def Con112 : Type 1
 := ∀ (Con112  : Type)
      (nil  : Con112)
      (snoc : Con112 → Ty112 → Con112)
    , Con112

def nil112 : Con112
 := λ Con112 nil112 snoc => nil112

def snoc112 : Con112 → Ty112 → Con112
 := λ Γ A Con112 nil112 snoc112 => snoc112 (Γ Con112 nil112 snoc112) A

def Var112 : Con112 → Ty112 → Type 1
 := λ Γ A =>
   ∀ (Var112 : Con112 → Ty112 → Type)
     (vz  : ∀ Γ A, Var112 (snoc112 Γ A) A)
     (vs  : ∀ Γ B A, Var112 Γ A → Var112 (snoc112 Γ B) A)
   , Var112 Γ A

def vz112 {Γ A} : Var112 (snoc112 Γ A) A
 := λ Var112 vz112 vs => vz112 _ _

def vs112 {Γ B A} : Var112 Γ A → Var112 (snoc112 Γ B) A
 := λ x Var112 vz112 vs112 => vs112 _ _ _ (x Var112 vz112 vs112)

def Tm112 : Con112 → Ty112 → Type 1
 := λ Γ A =>
   ∀ (Tm112  : Con112 → Ty112 → Type)
     (var   : ∀ Γ A     , Var112 Γ A → Tm112 Γ A)
     (lam   : ∀ Γ A B   , Tm112 (snoc112 Γ A) B → Tm112 Γ (arr112 A B))
     (app   : ∀ Γ A B   , Tm112 Γ (arr112 A B) → Tm112 Γ A → Tm112 Γ B)
   , Tm112 Γ A

def var112 {Γ A} : Var112 Γ A → Tm112 Γ A
 := λ x Tm112 var112 lam app =>
     var112 _ _ x

def lam112 {Γ A B} : Tm112 (snoc112 Γ A) B → Tm112 Γ (arr112 A B)
 := λ t Tm112 var112 lam112 app =>
     lam112 _ _ _ (t Tm112 var112 lam112 app)

def app112 {Γ A B} : Tm112 Γ (arr112 A B) → Tm112 Γ A → Tm112 Γ B
 := λ t u Tm112 var112 lam112 app112 =>
     app112 _ _ _
         (t Tm112 var112 lam112 app112)
         (u Tm112 var112 lam112 app112)

def v0112 {Γ A} : Tm112 (snoc112 Γ A) A
 := var112 vz112

def v1112 {Γ A B} : Tm112 (snoc112 (snoc112 Γ A) B) A
 := var112 (vs112 vz112)

def v2112 {Γ A B C} : Tm112 (snoc112 (snoc112 (snoc112 Γ A) B) C) A
 := var112 (vs112 (vs112 vz112))

def v3112 {Γ A B C D} : Tm112 (snoc112 (snoc112 (snoc112 (snoc112 Γ A) B) C) D) A
 := var112 (vs112 (vs112 (vs112 vz112)))

def v4112 {Γ A B C D E} : Tm112 (snoc112 (snoc112 (snoc112 (snoc112 (snoc112 Γ A) B) C) D) E) A
 := var112 (vs112 (vs112 (vs112 (vs112 vz112))))

def test112 {Γ A} : Tm112 Γ (arr112 (arr112 A A) (arr112 A A))
 := lam112 (lam112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 (app112 v1112 v0112)))))))


def Ty113 : Type 1
 := ∀ (Ty113 : Type)
      (ι   : Ty113)
      (arr : Ty113 → Ty113 → Ty113)
    , Ty113

def ι113 : Ty113 := λ _ ι113 _ => ι113

def arr113 : Ty113 → Ty113 → Ty113
 := λ A B Ty113 ι113 arr113 =>
     arr113 (A Ty113 ι113 arr113) (B Ty113 ι113 arr113)

def Con113 : Type 1
 := ∀ (Con113  : Type)
      (nil  : Con113)
      (snoc : Con113 → Ty113 → Con113)
    , Con113

def nil113 : Con113
 := λ Con113 nil113 snoc => nil113

def snoc113 : Con113 → Ty113 → Con113
 := λ Γ A Con113 nil113 snoc113 => snoc113 (Γ Con113 nil113 snoc113) A

def Var113 : Con113 → Ty113 → Type 1
 := λ Γ A =>
   ∀ (Var113 : Con113 → Ty113 → Type)
     (vz  : ∀ Γ A, Var113 (snoc113 Γ A) A)
     (vs  : ∀ Γ B A, Var113 Γ A → Var113 (snoc113 Γ B) A)
   , Var113 Γ A

def vz113 {Γ A} : Var113 (snoc113 Γ A) A
 := λ Var113 vz113 vs => vz113 _ _

def vs113 {Γ B A} : Var113 Γ A → Var113 (snoc113 Γ B) A
 := λ x Var113 vz113 vs113 => vs113 _ _ _ (x Var113 vz113 vs113)

def Tm113 : Con113 → Ty113 → Type 1
 := λ Γ A =>
   ∀ (Tm113  : Con113 → Ty113 → Type)
     (var   : ∀ Γ A     , Var113 Γ A → Tm113 Γ A)
     (lam   : ∀ Γ A B   , Tm113 (snoc113 Γ A) B → Tm113 Γ (arr113 A B))
     (app   : ∀ Γ A B   , Tm113 Γ (arr113 A B) → Tm113 Γ A → Tm113 Γ B)
   , Tm113 Γ A

def var113 {Γ A} : Var113 Γ A → Tm113 Γ A
 := λ x Tm113 var113 lam app =>
     var113 _ _ x

def lam113 {Γ A B} : Tm113 (snoc113 Γ A) B → Tm113 Γ (arr113 A B)
 := λ t Tm113 var113 lam113 app =>
     lam113 _ _ _ (t Tm113 var113 lam113 app)

def app113 {Γ A B} : Tm113 Γ (arr113 A B) → Tm113 Γ A → Tm113 Γ B
 := λ t u Tm113 var113 lam113 app113 =>
     app113 _ _ _
         (t Tm113 var113 lam113 app113)
         (u Tm113 var113 lam113 app113)

def v0113 {Γ A} : Tm113 (snoc113 Γ A) A
 := var113 vz113

def v1113 {Γ A B} : Tm113 (snoc113 (snoc113 Γ A) B) A
 := var113 (vs113 vz113)

def v2113 {Γ A B C} : Tm113 (snoc113 (snoc113 (snoc113 Γ A) B) C) A
 := var113 (vs113 (vs113 vz113))

def v3113 {Γ A B C D} : Tm113 (snoc113 (snoc113 (snoc113 (snoc113 Γ A) B) C) D) A
 := var113 (vs113 (vs113 (vs113 vz113)))

def v4113 {Γ A B C D E} : Tm113 (snoc113 (snoc113 (snoc113 (snoc113 (snoc113 Γ A) B) C) D) E) A
 := var113 (vs113 (vs113 (vs113 (vs113 vz113))))

def test113 {Γ A} : Tm113 Γ (arr113 (arr113 A A) (arr113 A A))
 := lam113 (lam113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 (app113 v1113 v0113)))))))


def Ty114 : Type 1
 := ∀ (Ty114 : Type)
      (ι   : Ty114)
      (arr : Ty114 → Ty114 → Ty114)
    , Ty114

def ι114 : Ty114 := λ _ ι114 _ => ι114

def arr114 : Ty114 → Ty114 → Ty114
 := λ A B Ty114 ι114 arr114 =>
     arr114 (A Ty114 ι114 arr114) (B Ty114 ι114 arr114)

def Con114 : Type 1
 := ∀ (Con114  : Type)
      (nil  : Con114)
      (snoc : Con114 → Ty114 → Con114)
    , Con114

def nil114 : Con114
 := λ Con114 nil114 snoc => nil114

def snoc114 : Con114 → Ty114 → Con114
 := λ Γ A Con114 nil114 snoc114 => snoc114 (Γ Con114 nil114 snoc114) A

def Var114 : Con114 → Ty114 → Type 1
 := λ Γ A =>
   ∀ (Var114 : Con114 → Ty114 → Type)
     (vz  : ∀ Γ A, Var114 (snoc114 Γ A) A)
     (vs  : ∀ Γ B A, Var114 Γ A → Var114 (snoc114 Γ B) A)
   , Var114 Γ A

def vz114 {Γ A} : Var114 (snoc114 Γ A) A
 := λ Var114 vz114 vs => vz114 _ _

def vs114 {Γ B A} : Var114 Γ A → Var114 (snoc114 Γ B) A
 := λ x Var114 vz114 vs114 => vs114 _ _ _ (x Var114 vz114 vs114)

def Tm114 : Con114 → Ty114 → Type 1
 := λ Γ A =>
   ∀ (Tm114  : Con114 → Ty114 → Type)
     (var   : ∀ Γ A     , Var114 Γ A → Tm114 Γ A)
     (lam   : ∀ Γ A B   , Tm114 (snoc114 Γ A) B → Tm114 Γ (arr114 A B))
     (app   : ∀ Γ A B   , Tm114 Γ (arr114 A B) → Tm114 Γ A → Tm114 Γ B)
   , Tm114 Γ A

def var114 {Γ A} : Var114 Γ A → Tm114 Γ A
 := λ x Tm114 var114 lam app =>
     var114 _ _ x

def lam114 {Γ A B} : Tm114 (snoc114 Γ A) B → Tm114 Γ (arr114 A B)
 := λ t Tm114 var114 lam114 app =>
     lam114 _ _ _ (t Tm114 var114 lam114 app)

def app114 {Γ A B} : Tm114 Γ (arr114 A B) → Tm114 Γ A → Tm114 Γ B
 := λ t u Tm114 var114 lam114 app114 =>
     app114 _ _ _
         (t Tm114 var114 lam114 app114)
         (u Tm114 var114 lam114 app114)

def v0114 {Γ A} : Tm114 (snoc114 Γ A) A
 := var114 vz114

def v1114 {Γ A B} : Tm114 (snoc114 (snoc114 Γ A) B) A
 := var114 (vs114 vz114)

def v2114 {Γ A B C} : Tm114 (snoc114 (snoc114 (snoc114 Γ A) B) C) A
 := var114 (vs114 (vs114 vz114))

def v3114 {Γ A B C D} : Tm114 (snoc114 (snoc114 (snoc114 (snoc114 Γ A) B) C) D) A
 := var114 (vs114 (vs114 (vs114 vz114)))

def v4114 {Γ A B C D E} : Tm114 (snoc114 (snoc114 (snoc114 (snoc114 (snoc114 Γ A) B) C) D) E) A
 := var114 (vs114 (vs114 (vs114 (vs114 vz114))))

def test114 {Γ A} : Tm114 Γ (arr114 (arr114 A A) (arr114 A A))
 := lam114 (lam114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 (app114 v1114 v0114)))))))


def Ty115 : Type 1
 := ∀ (Ty115 : Type)
      (ι   : Ty115)
      (arr : Ty115 → Ty115 → Ty115)
    , Ty115

def ι115 : Ty115 := λ _ ι115 _ => ι115

def arr115 : Ty115 → Ty115 → Ty115
 := λ A B Ty115 ι115 arr115 =>
     arr115 (A Ty115 ι115 arr115) (B Ty115 ι115 arr115)

def Con115 : Type 1
 := ∀ (Con115  : Type)
      (nil  : Con115)
      (snoc : Con115 → Ty115 → Con115)
    , Con115

def nil115 : Con115
 := λ Con115 nil115 snoc => nil115

def snoc115 : Con115 → Ty115 → Con115
 := λ Γ A Con115 nil115 snoc115 => snoc115 (Γ Con115 nil115 snoc115) A

def Var115 : Con115 → Ty115 → Type 1
 := λ Γ A =>
   ∀ (Var115 : Con115 → Ty115 → Type)
     (vz  : ∀ Γ A, Var115 (snoc115 Γ A) A)
     (vs  : ∀ Γ B A, Var115 Γ A → Var115 (snoc115 Γ B) A)
   , Var115 Γ A

def vz115 {Γ A} : Var115 (snoc115 Γ A) A
 := λ Var115 vz115 vs => vz115 _ _

def vs115 {Γ B A} : Var115 Γ A → Var115 (snoc115 Γ B) A
 := λ x Var115 vz115 vs115 => vs115 _ _ _ (x Var115 vz115 vs115)

def Tm115 : Con115 → Ty115 → Type 1
 := λ Γ A =>
   ∀ (Tm115  : Con115 → Ty115 → Type)
     (var   : ∀ Γ A     , Var115 Γ A → Tm115 Γ A)
     (lam   : ∀ Γ A B   , Tm115 (snoc115 Γ A) B → Tm115 Γ (arr115 A B))
     (app   : ∀ Γ A B   , Tm115 Γ (arr115 A B) → Tm115 Γ A → Tm115 Γ B)
   , Tm115 Γ A

def var115 {Γ A} : Var115 Γ A → Tm115 Γ A
 := λ x Tm115 var115 lam app =>
     var115 _ _ x

def lam115 {Γ A B} : Tm115 (snoc115 Γ A) B → Tm115 Γ (arr115 A B)
 := λ t Tm115 var115 lam115 app =>
     lam115 _ _ _ (t Tm115 var115 lam115 app)

def app115 {Γ A B} : Tm115 Γ (arr115 A B) → Tm115 Γ A → Tm115 Γ B
 := λ t u Tm115 var115 lam115 app115 =>
     app115 _ _ _
         (t Tm115 var115 lam115 app115)
         (u Tm115 var115 lam115 app115)

def v0115 {Γ A} : Tm115 (snoc115 Γ A) A
 := var115 vz115

def v1115 {Γ A B} : Tm115 (snoc115 (snoc115 Γ A) B) A
 := var115 (vs115 vz115)

def v2115 {Γ A B C} : Tm115 (snoc115 (snoc115 (snoc115 Γ A) B) C) A
 := var115 (vs115 (vs115 vz115))

def v3115 {Γ A B C D} : Tm115 (snoc115 (snoc115 (snoc115 (snoc115 Γ A) B) C) D) A
 := var115 (vs115 (vs115 (vs115 vz115)))

def v4115 {Γ A B C D E} : Tm115 (snoc115 (snoc115 (snoc115 (snoc115 (snoc115 Γ A) B) C) D) E) A
 := var115 (vs115 (vs115 (vs115 (vs115 vz115))))

def test115 {Γ A} : Tm115 Γ (arr115 (arr115 A A) (arr115 A A))
 := lam115 (lam115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 (app115 v1115 v0115)))))))


def Ty116 : Type 1
 := ∀ (Ty116 : Type)
      (ι   : Ty116)
      (arr : Ty116 → Ty116 → Ty116)
    , Ty116

def ι116 : Ty116 := λ _ ι116 _ => ι116

def arr116 : Ty116 → Ty116 → Ty116
 := λ A B Ty116 ι116 arr116 =>
     arr116 (A Ty116 ι116 arr116) (B Ty116 ι116 arr116)

def Con116 : Type 1
 := ∀ (Con116  : Type)
      (nil  : Con116)
      (snoc : Con116 → Ty116 → Con116)
    , Con116

def nil116 : Con116
 := λ Con116 nil116 snoc => nil116

def snoc116 : Con116 → Ty116 → Con116
 := λ Γ A Con116 nil116 snoc116 => snoc116 (Γ Con116 nil116 snoc116) A

def Var116 : Con116 → Ty116 → Type 1
 := λ Γ A =>
   ∀ (Var116 : Con116 → Ty116 → Type)
     (vz  : ∀ Γ A, Var116 (snoc116 Γ A) A)
     (vs  : ∀ Γ B A, Var116 Γ A → Var116 (snoc116 Γ B) A)
   , Var116 Γ A

def vz116 {Γ A} : Var116 (snoc116 Γ A) A
 := λ Var116 vz116 vs => vz116 _ _

def vs116 {Γ B A} : Var116 Γ A → Var116 (snoc116 Γ B) A
 := λ x Var116 vz116 vs116 => vs116 _ _ _ (x Var116 vz116 vs116)

def Tm116 : Con116 → Ty116 → Type 1
 := λ Γ A =>
   ∀ (Tm116  : Con116 → Ty116 → Type)
     (var   : ∀ Γ A     , Var116 Γ A → Tm116 Γ A)
     (lam   : ∀ Γ A B   , Tm116 (snoc116 Γ A) B → Tm116 Γ (arr116 A B))
     (app   : ∀ Γ A B   , Tm116 Γ (arr116 A B) → Tm116 Γ A → Tm116 Γ B)
   , Tm116 Γ A

def var116 {Γ A} : Var116 Γ A → Tm116 Γ A
 := λ x Tm116 var116 lam app =>
     var116 _ _ x

def lam116 {Γ A B} : Tm116 (snoc116 Γ A) B → Tm116 Γ (arr116 A B)
 := λ t Tm116 var116 lam116 app =>
     lam116 _ _ _ (t Tm116 var116 lam116 app)

def app116 {Γ A B} : Tm116 Γ (arr116 A B) → Tm116 Γ A → Tm116 Γ B
 := λ t u Tm116 var116 lam116 app116 =>
     app116 _ _ _
         (t Tm116 var116 lam116 app116)
         (u Tm116 var116 lam116 app116)

def v0116 {Γ A} : Tm116 (snoc116 Γ A) A
 := var116 vz116

def v1116 {Γ A B} : Tm116 (snoc116 (snoc116 Γ A) B) A
 := var116 (vs116 vz116)

def v2116 {Γ A B C} : Tm116 (snoc116 (snoc116 (snoc116 Γ A) B) C) A
 := var116 (vs116 (vs116 vz116))

def v3116 {Γ A B C D} : Tm116 (snoc116 (snoc116 (snoc116 (snoc116 Γ A) B) C) D) A
 := var116 (vs116 (vs116 (vs116 vz116)))

def v4116 {Γ A B C D E} : Tm116 (snoc116 (snoc116 (snoc116 (snoc116 (snoc116 Γ A) B) C) D) E) A
 := var116 (vs116 (vs116 (vs116 (vs116 vz116))))

def test116 {Γ A} : Tm116 Γ (arr116 (arr116 A A) (arr116 A A))
 := lam116 (lam116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 (app116 v1116 v0116)))))))


def Ty117 : Type 1
 := ∀ (Ty117 : Type)
      (ι   : Ty117)
      (arr : Ty117 → Ty117 → Ty117)
    , Ty117

def ι117 : Ty117 := λ _ ι117 _ => ι117

def arr117 : Ty117 → Ty117 → Ty117
 := λ A B Ty117 ι117 arr117 =>
     arr117 (A Ty117 ι117 arr117) (B Ty117 ι117 arr117)

def Con117 : Type 1
 := ∀ (Con117  : Type)
      (nil  : Con117)
      (snoc : Con117 → Ty117 → Con117)
    , Con117

def nil117 : Con117
 := λ Con117 nil117 snoc => nil117

def snoc117 : Con117 → Ty117 → Con117
 := λ Γ A Con117 nil117 snoc117 => snoc117 (Γ Con117 nil117 snoc117) A

def Var117 : Con117 → Ty117 → Type 1
 := λ Γ A =>
   ∀ (Var117 : Con117 → Ty117 → Type)
     (vz  : ∀ Γ A, Var117 (snoc117 Γ A) A)
     (vs  : ∀ Γ B A, Var117 Γ A → Var117 (snoc117 Γ B) A)
   , Var117 Γ A

def vz117 {Γ A} : Var117 (snoc117 Γ A) A
 := λ Var117 vz117 vs => vz117 _ _

def vs117 {Γ B A} : Var117 Γ A → Var117 (snoc117 Γ B) A
 := λ x Var117 vz117 vs117 => vs117 _ _ _ (x Var117 vz117 vs117)

def Tm117 : Con117 → Ty117 → Type 1
 := λ Γ A =>
   ∀ (Tm117  : Con117 → Ty117 → Type)
     (var   : ∀ Γ A     , Var117 Γ A → Tm117 Γ A)
     (lam   : ∀ Γ A B   , Tm117 (snoc117 Γ A) B → Tm117 Γ (arr117 A B))
     (app   : ∀ Γ A B   , Tm117 Γ (arr117 A B) → Tm117 Γ A → Tm117 Γ B)
   , Tm117 Γ A

def var117 {Γ A} : Var117 Γ A → Tm117 Γ A
 := λ x Tm117 var117 lam app =>
     var117 _ _ x

def lam117 {Γ A B} : Tm117 (snoc117 Γ A) B → Tm117 Γ (arr117 A B)
 := λ t Tm117 var117 lam117 app =>
     lam117 _ _ _ (t Tm117 var117 lam117 app)

def app117 {Γ A B} : Tm117 Γ (arr117 A B) → Tm117 Γ A → Tm117 Γ B
 := λ t u Tm117 var117 lam117 app117 =>
     app117 _ _ _
         (t Tm117 var117 lam117 app117)
         (u Tm117 var117 lam117 app117)

def v0117 {Γ A} : Tm117 (snoc117 Γ A) A
 := var117 vz117

def v1117 {Γ A B} : Tm117 (snoc117 (snoc117 Γ A) B) A
 := var117 (vs117 vz117)

def v2117 {Γ A B C} : Tm117 (snoc117 (snoc117 (snoc117 Γ A) B) C) A
 := var117 (vs117 (vs117 vz117))

def v3117 {Γ A B C D} : Tm117 (snoc117 (snoc117 (snoc117 (snoc117 Γ A) B) C) D) A
 := var117 (vs117 (vs117 (vs117 vz117)))

def v4117 {Γ A B C D E} : Tm117 (snoc117 (snoc117 (snoc117 (snoc117 (snoc117 Γ A) B) C) D) E) A
 := var117 (vs117 (vs117 (vs117 (vs117 vz117))))

def test117 {Γ A} : Tm117 Γ (arr117 (arr117 A A) (arr117 A A))
 := lam117 (lam117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 (app117 v1117 v0117)))))))


def Ty118 : Type 1
 := ∀ (Ty118 : Type)
      (ι   : Ty118)
      (arr : Ty118 → Ty118 → Ty118)
    , Ty118

def ι118 : Ty118 := λ _ ι118 _ => ι118

def arr118 : Ty118 → Ty118 → Ty118
 := λ A B Ty118 ι118 arr118 =>
     arr118 (A Ty118 ι118 arr118) (B Ty118 ι118 arr118)

def Con118 : Type 1
 := ∀ (Con118  : Type)
      (nil  : Con118)
      (snoc : Con118 → Ty118 → Con118)
    , Con118

def nil118 : Con118
 := λ Con118 nil118 snoc => nil118

def snoc118 : Con118 → Ty118 → Con118
 := λ Γ A Con118 nil118 snoc118 => snoc118 (Γ Con118 nil118 snoc118) A

def Var118 : Con118 → Ty118 → Type 1
 := λ Γ A =>
   ∀ (Var118 : Con118 → Ty118 → Type)
     (vz  : ∀ Γ A, Var118 (snoc118 Γ A) A)
     (vs  : ∀ Γ B A, Var118 Γ A → Var118 (snoc118 Γ B) A)
   , Var118 Γ A

def vz118 {Γ A} : Var118 (snoc118 Γ A) A
 := λ Var118 vz118 vs => vz118 _ _

def vs118 {Γ B A} : Var118 Γ A → Var118 (snoc118 Γ B) A
 := λ x Var118 vz118 vs118 => vs118 _ _ _ (x Var118 vz118 vs118)

def Tm118 : Con118 → Ty118 → Type 1
 := λ Γ A =>
   ∀ (Tm118  : Con118 → Ty118 → Type)
     (var   : ∀ Γ A     , Var118 Γ A → Tm118 Γ A)
     (lam   : ∀ Γ A B   , Tm118 (snoc118 Γ A) B → Tm118 Γ (arr118 A B))
     (app   : ∀ Γ A B   , Tm118 Γ (arr118 A B) → Tm118 Γ A → Tm118 Γ B)
   , Tm118 Γ A

def var118 {Γ A} : Var118 Γ A → Tm118 Γ A
 := λ x Tm118 var118 lam app =>
     var118 _ _ x

def lam118 {Γ A B} : Tm118 (snoc118 Γ A) B → Tm118 Γ (arr118 A B)
 := λ t Tm118 var118 lam118 app =>
     lam118 _ _ _ (t Tm118 var118 lam118 app)

def app118 {Γ A B} : Tm118 Γ (arr118 A B) → Tm118 Γ A → Tm118 Γ B
 := λ t u Tm118 var118 lam118 app118 =>
     app118 _ _ _
         (t Tm118 var118 lam118 app118)
         (u Tm118 var118 lam118 app118)

def v0118 {Γ A} : Tm118 (snoc118 Γ A) A
 := var118 vz118

def v1118 {Γ A B} : Tm118 (snoc118 (snoc118 Γ A) B) A
 := var118 (vs118 vz118)

def v2118 {Γ A B C} : Tm118 (snoc118 (snoc118 (snoc118 Γ A) B) C) A
 := var118 (vs118 (vs118 vz118))

def v3118 {Γ A B C D} : Tm118 (snoc118 (snoc118 (snoc118 (snoc118 Γ A) B) C) D) A
 := var118 (vs118 (vs118 (vs118 vz118)))

def v4118 {Γ A B C D E} : Tm118 (snoc118 (snoc118 (snoc118 (snoc118 (snoc118 Γ A) B) C) D) E) A
 := var118 (vs118 (vs118 (vs118 (vs118 vz118))))

def test118 {Γ A} : Tm118 Γ (arr118 (arr118 A A) (arr118 A A))
 := lam118 (lam118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 (app118 v1118 v0118)))))))


def Ty119 : Type 1
 := ∀ (Ty119 : Type)
      (ι   : Ty119)
      (arr : Ty119 → Ty119 → Ty119)
    , Ty119

def ι119 : Ty119 := λ _ ι119 _ => ι119

def arr119 : Ty119 → Ty119 → Ty119
 := λ A B Ty119 ι119 arr119 =>
     arr119 (A Ty119 ι119 arr119) (B Ty119 ι119 arr119)

def Con119 : Type 1
 := ∀ (Con119  : Type)
      (nil  : Con119)
      (snoc : Con119 → Ty119 → Con119)
    , Con119

def nil119 : Con119
 := λ Con119 nil119 snoc => nil119

def snoc119 : Con119 → Ty119 → Con119
 := λ Γ A Con119 nil119 snoc119 => snoc119 (Γ Con119 nil119 snoc119) A

def Var119 : Con119 → Ty119 → Type 1
 := λ Γ A =>
   ∀ (Var119 : Con119 → Ty119 → Type)
     (vz  : ∀ Γ A, Var119 (snoc119 Γ A) A)
     (vs  : ∀ Γ B A, Var119 Γ A → Var119 (snoc119 Γ B) A)
   , Var119 Γ A

def vz119 {Γ A} : Var119 (snoc119 Γ A) A
 := λ Var119 vz119 vs => vz119 _ _

def vs119 {Γ B A} : Var119 Γ A → Var119 (snoc119 Γ B) A
 := λ x Var119 vz119 vs119 => vs119 _ _ _ (x Var119 vz119 vs119)

def Tm119 : Con119 → Ty119 → Type 1
 := λ Γ A =>
   ∀ (Tm119  : Con119 → Ty119 → Type)
     (var   : ∀ Γ A     , Var119 Γ A → Tm119 Γ A)
     (lam   : ∀ Γ A B   , Tm119 (snoc119 Γ A) B → Tm119 Γ (arr119 A B))
     (app   : ∀ Γ A B   , Tm119 Γ (arr119 A B) → Tm119 Γ A → Tm119 Γ B)
   , Tm119 Γ A

def var119 {Γ A} : Var119 Γ A → Tm119 Γ A
 := λ x Tm119 var119 lam app =>
     var119 _ _ x

def lam119 {Γ A B} : Tm119 (snoc119 Γ A) B → Tm119 Γ (arr119 A B)
 := λ t Tm119 var119 lam119 app =>
     lam119 _ _ _ (t Tm119 var119 lam119 app)

def app119 {Γ A B} : Tm119 Γ (arr119 A B) → Tm119 Γ A → Tm119 Γ B
 := λ t u Tm119 var119 lam119 app119 =>
     app119 _ _ _
         (t Tm119 var119 lam119 app119)
         (u Tm119 var119 lam119 app119)

def v0119 {Γ A} : Tm119 (snoc119 Γ A) A
 := var119 vz119

def v1119 {Γ A B} : Tm119 (snoc119 (snoc119 Γ A) B) A
 := var119 (vs119 vz119)

def v2119 {Γ A B C} : Tm119 (snoc119 (snoc119 (snoc119 Γ A) B) C) A
 := var119 (vs119 (vs119 vz119))

def v3119 {Γ A B C D} : Tm119 (snoc119 (snoc119 (snoc119 (snoc119 Γ A) B) C) D) A
 := var119 (vs119 (vs119 (vs119 vz119)))

def v4119 {Γ A B C D E} : Tm119 (snoc119 (snoc119 (snoc119 (snoc119 (snoc119 Γ A) B) C) D) E) A
 := var119 (vs119 (vs119 (vs119 (vs119 vz119))))

def test119 {Γ A} : Tm119 Γ (arr119 (arr119 A A) (arr119 A A))
 := lam119 (lam119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 (app119 v1119 v0119)))))))


def Ty120 : Type 1
 := ∀ (Ty120 : Type)
      (ι   : Ty120)
      (arr : Ty120 → Ty120 → Ty120)
    , Ty120

def ι120 : Ty120 := λ _ ι120 _ => ι120

def arr120 : Ty120 → Ty120 → Ty120
 := λ A B Ty120 ι120 arr120 =>
     arr120 (A Ty120 ι120 arr120) (B Ty120 ι120 arr120)

def Con120 : Type 1
 := ∀ (Con120  : Type)
      (nil  : Con120)
      (snoc : Con120 → Ty120 → Con120)
    , Con120

def nil120 : Con120
 := λ Con120 nil120 snoc => nil120

def snoc120 : Con120 → Ty120 → Con120
 := λ Γ A Con120 nil120 snoc120 => snoc120 (Γ Con120 nil120 snoc120) A

def Var120 : Con120 → Ty120 → Type 1
 := λ Γ A =>
   ∀ (Var120 : Con120 → Ty120 → Type)
     (vz  : ∀ Γ A, Var120 (snoc120 Γ A) A)
     (vs  : ∀ Γ B A, Var120 Γ A → Var120 (snoc120 Γ B) A)
   , Var120 Γ A

def vz120 {Γ A} : Var120 (snoc120 Γ A) A
 := λ Var120 vz120 vs => vz120 _ _

def vs120 {Γ B A} : Var120 Γ A → Var120 (snoc120 Γ B) A
 := λ x Var120 vz120 vs120 => vs120 _ _ _ (x Var120 vz120 vs120)

def Tm120 : Con120 → Ty120 → Type 1
 := λ Γ A =>
   ∀ (Tm120  : Con120 → Ty120 → Type)
     (var   : ∀ Γ A     , Var120 Γ A → Tm120 Γ A)
     (lam   : ∀ Γ A B   , Tm120 (snoc120 Γ A) B → Tm120 Γ (arr120 A B))
     (app   : ∀ Γ A B   , Tm120 Γ (arr120 A B) → Tm120 Γ A → Tm120 Γ B)
   , Tm120 Γ A

def var120 {Γ A} : Var120 Γ A → Tm120 Γ A
 := λ x Tm120 var120 lam app =>
     var120 _ _ x

def lam120 {Γ A B} : Tm120 (snoc120 Γ A) B → Tm120 Γ (arr120 A B)
 := λ t Tm120 var120 lam120 app =>
     lam120 _ _ _ (t Tm120 var120 lam120 app)

def app120 {Γ A B} : Tm120 Γ (arr120 A B) → Tm120 Γ A → Tm120 Γ B
 := λ t u Tm120 var120 lam120 app120 =>
     app120 _ _ _
         (t Tm120 var120 lam120 app120)
         (u Tm120 var120 lam120 app120)

def v0120 {Γ A} : Tm120 (snoc120 Γ A) A
 := var120 vz120

def v1120 {Γ A B} : Tm120 (snoc120 (snoc120 Γ A) B) A
 := var120 (vs120 vz120)

def v2120 {Γ A B C} : Tm120 (snoc120 (snoc120 (snoc120 Γ A) B) C) A
 := var120 (vs120 (vs120 vz120))

def v3120 {Γ A B C D} : Tm120 (snoc120 (snoc120 (snoc120 (snoc120 Γ A) B) C) D) A
 := var120 (vs120 (vs120 (vs120 vz120)))

def v4120 {Γ A B C D E} : Tm120 (snoc120 (snoc120 (snoc120 (snoc120 (snoc120 Γ A) B) C) D) E) A
 := var120 (vs120 (vs120 (vs120 (vs120 vz120))))

def test120 {Γ A} : Tm120 Γ (arr120 (arr120 A A) (arr120 A A))
 := lam120 (lam120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 (app120 v1120 v0120)))))))


def Ty121 : Type 1
 := ∀ (Ty121 : Type)
      (ι   : Ty121)
      (arr : Ty121 → Ty121 → Ty121)
    , Ty121

def ι121 : Ty121 := λ _ ι121 _ => ι121

def arr121 : Ty121 → Ty121 → Ty121
 := λ A B Ty121 ι121 arr121 =>
     arr121 (A Ty121 ι121 arr121) (B Ty121 ι121 arr121)

def Con121 : Type 1
 := ∀ (Con121  : Type)
      (nil  : Con121)
      (snoc : Con121 → Ty121 → Con121)
    , Con121

def nil121 : Con121
 := λ Con121 nil121 snoc => nil121

def snoc121 : Con121 → Ty121 → Con121
 := λ Γ A Con121 nil121 snoc121 => snoc121 (Γ Con121 nil121 snoc121) A

def Var121 : Con121 → Ty121 → Type 1
 := λ Γ A =>
   ∀ (Var121 : Con121 → Ty121 → Type)
     (vz  : ∀ Γ A, Var121 (snoc121 Γ A) A)
     (vs  : ∀ Γ B A, Var121 Γ A → Var121 (snoc121 Γ B) A)
   , Var121 Γ A

def vz121 {Γ A} : Var121 (snoc121 Γ A) A
 := λ Var121 vz121 vs => vz121 _ _

def vs121 {Γ B A} : Var121 Γ A → Var121 (snoc121 Γ B) A
 := λ x Var121 vz121 vs121 => vs121 _ _ _ (x Var121 vz121 vs121)

def Tm121 : Con121 → Ty121 → Type 1
 := λ Γ A =>
   ∀ (Tm121  : Con121 → Ty121 → Type)
     (var   : ∀ Γ A     , Var121 Γ A → Tm121 Γ A)
     (lam   : ∀ Γ A B   , Tm121 (snoc121 Γ A) B → Tm121 Γ (arr121 A B))
     (app   : ∀ Γ A B   , Tm121 Γ (arr121 A B) → Tm121 Γ A → Tm121 Γ B)
   , Tm121 Γ A

def var121 {Γ A} : Var121 Γ A → Tm121 Γ A
 := λ x Tm121 var121 lam app =>
     var121 _ _ x

def lam121 {Γ A B} : Tm121 (snoc121 Γ A) B → Tm121 Γ (arr121 A B)
 := λ t Tm121 var121 lam121 app =>
     lam121 _ _ _ (t Tm121 var121 lam121 app)

def app121 {Γ A B} : Tm121 Γ (arr121 A B) → Tm121 Γ A → Tm121 Γ B
 := λ t u Tm121 var121 lam121 app121 =>
     app121 _ _ _
         (t Tm121 var121 lam121 app121)
         (u Tm121 var121 lam121 app121)

def v0121 {Γ A} : Tm121 (snoc121 Γ A) A
 := var121 vz121

def v1121 {Γ A B} : Tm121 (snoc121 (snoc121 Γ A) B) A
 := var121 (vs121 vz121)

def v2121 {Γ A B C} : Tm121 (snoc121 (snoc121 (snoc121 Γ A) B) C) A
 := var121 (vs121 (vs121 vz121))

def v3121 {Γ A B C D} : Tm121 (snoc121 (snoc121 (snoc121 (snoc121 Γ A) B) C) D) A
 := var121 (vs121 (vs121 (vs121 vz121)))

def v4121 {Γ A B C D E} : Tm121 (snoc121 (snoc121 (snoc121 (snoc121 (snoc121 Γ A) B) C) D) E) A
 := var121 (vs121 (vs121 (vs121 (vs121 vz121))))

def test121 {Γ A} : Tm121 Γ (arr121 (arr121 A A) (arr121 A A))
 := lam121 (lam121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 (app121 v1121 v0121)))))))


def Ty122 : Type 1
 := ∀ (Ty122 : Type)
      (ι   : Ty122)
      (arr : Ty122 → Ty122 → Ty122)
    , Ty122

def ι122 : Ty122 := λ _ ι122 _ => ι122

def arr122 : Ty122 → Ty122 → Ty122
 := λ A B Ty122 ι122 arr122 =>
     arr122 (A Ty122 ι122 arr122) (B Ty122 ι122 arr122)

def Con122 : Type 1
 := ∀ (Con122  : Type)
      (nil  : Con122)
      (snoc : Con122 → Ty122 → Con122)
    , Con122

def nil122 : Con122
 := λ Con122 nil122 snoc => nil122

def snoc122 : Con122 → Ty122 → Con122
 := λ Γ A Con122 nil122 snoc122 => snoc122 (Γ Con122 nil122 snoc122) A

def Var122 : Con122 → Ty122 → Type 1
 := λ Γ A =>
   ∀ (Var122 : Con122 → Ty122 → Type)
     (vz  : ∀ Γ A, Var122 (snoc122 Γ A) A)
     (vs  : ∀ Γ B A, Var122 Γ A → Var122 (snoc122 Γ B) A)
   , Var122 Γ A

def vz122 {Γ A} : Var122 (snoc122 Γ A) A
 := λ Var122 vz122 vs => vz122 _ _

def vs122 {Γ B A} : Var122 Γ A → Var122 (snoc122 Γ B) A
 := λ x Var122 vz122 vs122 => vs122 _ _ _ (x Var122 vz122 vs122)

def Tm122 : Con122 → Ty122 → Type 1
 := λ Γ A =>
   ∀ (Tm122  : Con122 → Ty122 → Type)
     (var   : ∀ Γ A     , Var122 Γ A → Tm122 Γ A)
     (lam   : ∀ Γ A B   , Tm122 (snoc122 Γ A) B → Tm122 Γ (arr122 A B))
     (app   : ∀ Γ A B   , Tm122 Γ (arr122 A B) → Tm122 Γ A → Tm122 Γ B)
   , Tm122 Γ A

def var122 {Γ A} : Var122 Γ A → Tm122 Γ A
 := λ x Tm122 var122 lam app =>
     var122 _ _ x

def lam122 {Γ A B} : Tm122 (snoc122 Γ A) B → Tm122 Γ (arr122 A B)
 := λ t Tm122 var122 lam122 app =>
     lam122 _ _ _ (t Tm122 var122 lam122 app)

def app122 {Γ A B} : Tm122 Γ (arr122 A B) → Tm122 Γ A → Tm122 Γ B
 := λ t u Tm122 var122 lam122 app122 =>
     app122 _ _ _
         (t Tm122 var122 lam122 app122)
         (u Tm122 var122 lam122 app122)

def v0122 {Γ A} : Tm122 (snoc122 Γ A) A
 := var122 vz122

def v1122 {Γ A B} : Tm122 (snoc122 (snoc122 Γ A) B) A
 := var122 (vs122 vz122)

def v2122 {Γ A B C} : Tm122 (snoc122 (snoc122 (snoc122 Γ A) B) C) A
 := var122 (vs122 (vs122 vz122))

def v3122 {Γ A B C D} : Tm122 (snoc122 (snoc122 (snoc122 (snoc122 Γ A) B) C) D) A
 := var122 (vs122 (vs122 (vs122 vz122)))

def v4122 {Γ A B C D E} : Tm122 (snoc122 (snoc122 (snoc122 (snoc122 (snoc122 Γ A) B) C) D) E) A
 := var122 (vs122 (vs122 (vs122 (vs122 vz122))))

def test122 {Γ A} : Tm122 Γ (arr122 (arr122 A A) (arr122 A A))
 := lam122 (lam122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 (app122 v1122 v0122)))))))


def Ty123 : Type 1
 := ∀ (Ty123 : Type)
      (ι   : Ty123)
      (arr : Ty123 → Ty123 → Ty123)
    , Ty123

def ι123 : Ty123 := λ _ ι123 _ => ι123

def arr123 : Ty123 → Ty123 → Ty123
 := λ A B Ty123 ι123 arr123 =>
     arr123 (A Ty123 ι123 arr123) (B Ty123 ι123 arr123)

def Con123 : Type 1
 := ∀ (Con123  : Type)
      (nil  : Con123)
      (snoc : Con123 → Ty123 → Con123)
    , Con123

def nil123 : Con123
 := λ Con123 nil123 snoc => nil123

def snoc123 : Con123 → Ty123 → Con123
 := λ Γ A Con123 nil123 snoc123 => snoc123 (Γ Con123 nil123 snoc123) A

def Var123 : Con123 → Ty123 → Type 1
 := λ Γ A =>
   ∀ (Var123 : Con123 → Ty123 → Type)
     (vz  : ∀ Γ A, Var123 (snoc123 Γ A) A)
     (vs  : ∀ Γ B A, Var123 Γ A → Var123 (snoc123 Γ B) A)
   , Var123 Γ A

def vz123 {Γ A} : Var123 (snoc123 Γ A) A
 := λ Var123 vz123 vs => vz123 _ _

def vs123 {Γ B A} : Var123 Γ A → Var123 (snoc123 Γ B) A
 := λ x Var123 vz123 vs123 => vs123 _ _ _ (x Var123 vz123 vs123)

def Tm123 : Con123 → Ty123 → Type 1
 := λ Γ A =>
   ∀ (Tm123  : Con123 → Ty123 → Type)
     (var   : ∀ Γ A     , Var123 Γ A → Tm123 Γ A)
     (lam   : ∀ Γ A B   , Tm123 (snoc123 Γ A) B → Tm123 Γ (arr123 A B))
     (app   : ∀ Γ A B   , Tm123 Γ (arr123 A B) → Tm123 Γ A → Tm123 Γ B)
   , Tm123 Γ A

def var123 {Γ A} : Var123 Γ A → Tm123 Γ A
 := λ x Tm123 var123 lam app =>
     var123 _ _ x

def lam123 {Γ A B} : Tm123 (snoc123 Γ A) B → Tm123 Γ (arr123 A B)
 := λ t Tm123 var123 lam123 app =>
     lam123 _ _ _ (t Tm123 var123 lam123 app)

def app123 {Γ A B} : Tm123 Γ (arr123 A B) → Tm123 Γ A → Tm123 Γ B
 := λ t u Tm123 var123 lam123 app123 =>
     app123 _ _ _
         (t Tm123 var123 lam123 app123)
         (u Tm123 var123 lam123 app123)

def v0123 {Γ A} : Tm123 (snoc123 Γ A) A
 := var123 vz123

def v1123 {Γ A B} : Tm123 (snoc123 (snoc123 Γ A) B) A
 := var123 (vs123 vz123)

def v2123 {Γ A B C} : Tm123 (snoc123 (snoc123 (snoc123 Γ A) B) C) A
 := var123 (vs123 (vs123 vz123))

def v3123 {Γ A B C D} : Tm123 (snoc123 (snoc123 (snoc123 (snoc123 Γ A) B) C) D) A
 := var123 (vs123 (vs123 (vs123 vz123)))

def v4123 {Γ A B C D E} : Tm123 (snoc123 (snoc123 (snoc123 (snoc123 (snoc123 Γ A) B) C) D) E) A
 := var123 (vs123 (vs123 (vs123 (vs123 vz123))))

def test123 {Γ A} : Tm123 Γ (arr123 (arr123 A A) (arr123 A A))
 := lam123 (lam123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 (app123 v1123 v0123)))))))


def Ty124 : Type 1
 := ∀ (Ty124 : Type)
      (ι   : Ty124)
      (arr : Ty124 → Ty124 → Ty124)
    , Ty124

def ι124 : Ty124 := λ _ ι124 _ => ι124

def arr124 : Ty124 → Ty124 → Ty124
 := λ A B Ty124 ι124 arr124 =>
     arr124 (A Ty124 ι124 arr124) (B Ty124 ι124 arr124)

def Con124 : Type 1
 := ∀ (Con124  : Type)
      (nil  : Con124)
      (snoc : Con124 → Ty124 → Con124)
    , Con124

def nil124 : Con124
 := λ Con124 nil124 snoc => nil124

def snoc124 : Con124 → Ty124 → Con124
 := λ Γ A Con124 nil124 snoc124 => snoc124 (Γ Con124 nil124 snoc124) A

def Var124 : Con124 → Ty124 → Type 1
 := λ Γ A =>
   ∀ (Var124 : Con124 → Ty124 → Type)
     (vz  : ∀ Γ A, Var124 (snoc124 Γ A) A)
     (vs  : ∀ Γ B A, Var124 Γ A → Var124 (snoc124 Γ B) A)
   , Var124 Γ A

def vz124 {Γ A} : Var124 (snoc124 Γ A) A
 := λ Var124 vz124 vs => vz124 _ _

def vs124 {Γ B A} : Var124 Γ A → Var124 (snoc124 Γ B) A
 := λ x Var124 vz124 vs124 => vs124 _ _ _ (x Var124 vz124 vs124)

def Tm124 : Con124 → Ty124 → Type 1
 := λ Γ A =>
   ∀ (Tm124  : Con124 → Ty124 → Type)
     (var   : ∀ Γ A     , Var124 Γ A → Tm124 Γ A)
     (lam   : ∀ Γ A B   , Tm124 (snoc124 Γ A) B → Tm124 Γ (arr124 A B))
     (app   : ∀ Γ A B   , Tm124 Γ (arr124 A B) → Tm124 Γ A → Tm124 Γ B)
   , Tm124 Γ A

def var124 {Γ A} : Var124 Γ A → Tm124 Γ A
 := λ x Tm124 var124 lam app =>
     var124 _ _ x

def lam124 {Γ A B} : Tm124 (snoc124 Γ A) B → Tm124 Γ (arr124 A B)
 := λ t Tm124 var124 lam124 app =>
     lam124 _ _ _ (t Tm124 var124 lam124 app)

def app124 {Γ A B} : Tm124 Γ (arr124 A B) → Tm124 Γ A → Tm124 Γ B
 := λ t u Tm124 var124 lam124 app124 =>
     app124 _ _ _
         (t Tm124 var124 lam124 app124)
         (u Tm124 var124 lam124 app124)

def v0124 {Γ A} : Tm124 (snoc124 Γ A) A
 := var124 vz124

def v1124 {Γ A B} : Tm124 (snoc124 (snoc124 Γ A) B) A
 := var124 (vs124 vz124)

def v2124 {Γ A B C} : Tm124 (snoc124 (snoc124 (snoc124 Γ A) B) C) A
 := var124 (vs124 (vs124 vz124))

def v3124 {Γ A B C D} : Tm124 (snoc124 (snoc124 (snoc124 (snoc124 Γ A) B) C) D) A
 := var124 (vs124 (vs124 (vs124 vz124)))

def v4124 {Γ A B C D E} : Tm124 (snoc124 (snoc124 (snoc124 (snoc124 (snoc124 Γ A) B) C) D) E) A
 := var124 (vs124 (vs124 (vs124 (vs124 vz124))))

def test124 {Γ A} : Tm124 Γ (arr124 (arr124 A A) (arr124 A A))
 := lam124 (lam124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 (app124 v1124 v0124)))))))


def Ty125 : Type 1
 := ∀ (Ty125 : Type)
      (ι   : Ty125)
      (arr : Ty125 → Ty125 → Ty125)
    , Ty125

def ι125 : Ty125 := λ _ ι125 _ => ι125

def arr125 : Ty125 → Ty125 → Ty125
 := λ A B Ty125 ι125 arr125 =>
     arr125 (A Ty125 ι125 arr125) (B Ty125 ι125 arr125)

def Con125 : Type 1
 := ∀ (Con125  : Type)
      (nil  : Con125)
      (snoc : Con125 → Ty125 → Con125)
    , Con125

def nil125 : Con125
 := λ Con125 nil125 snoc => nil125

def snoc125 : Con125 → Ty125 → Con125
 := λ Γ A Con125 nil125 snoc125 => snoc125 (Γ Con125 nil125 snoc125) A

def Var125 : Con125 → Ty125 → Type 1
 := λ Γ A =>
   ∀ (Var125 : Con125 → Ty125 → Type)
     (vz  : ∀ Γ A, Var125 (snoc125 Γ A) A)
     (vs  : ∀ Γ B A, Var125 Γ A → Var125 (snoc125 Γ B) A)
   , Var125 Γ A

def vz125 {Γ A} : Var125 (snoc125 Γ A) A
 := λ Var125 vz125 vs => vz125 _ _

def vs125 {Γ B A} : Var125 Γ A → Var125 (snoc125 Γ B) A
 := λ x Var125 vz125 vs125 => vs125 _ _ _ (x Var125 vz125 vs125)

def Tm125 : Con125 → Ty125 → Type 1
 := λ Γ A =>
   ∀ (Tm125  : Con125 → Ty125 → Type)
     (var   : ∀ Γ A     , Var125 Γ A → Tm125 Γ A)
     (lam   : ∀ Γ A B   , Tm125 (snoc125 Γ A) B → Tm125 Γ (arr125 A B))
     (app   : ∀ Γ A B   , Tm125 Γ (arr125 A B) → Tm125 Γ A → Tm125 Γ B)
   , Tm125 Γ A

def var125 {Γ A} : Var125 Γ A → Tm125 Γ A
 := λ x Tm125 var125 lam app =>
     var125 _ _ x

def lam125 {Γ A B} : Tm125 (snoc125 Γ A) B → Tm125 Γ (arr125 A B)
 := λ t Tm125 var125 lam125 app =>
     lam125 _ _ _ (t Tm125 var125 lam125 app)

def app125 {Γ A B} : Tm125 Γ (arr125 A B) → Tm125 Γ A → Tm125 Γ B
 := λ t u Tm125 var125 lam125 app125 =>
     app125 _ _ _
         (t Tm125 var125 lam125 app125)
         (u Tm125 var125 lam125 app125)

def v0125 {Γ A} : Tm125 (snoc125 Γ A) A
 := var125 vz125

def v1125 {Γ A B} : Tm125 (snoc125 (snoc125 Γ A) B) A
 := var125 (vs125 vz125)

def v2125 {Γ A B C} : Tm125 (snoc125 (snoc125 (snoc125 Γ A) B) C) A
 := var125 (vs125 (vs125 vz125))

def v3125 {Γ A B C D} : Tm125 (snoc125 (snoc125 (snoc125 (snoc125 Γ A) B) C) D) A
 := var125 (vs125 (vs125 (vs125 vz125)))

def v4125 {Γ A B C D E} : Tm125 (snoc125 (snoc125 (snoc125 (snoc125 (snoc125 Γ A) B) C) D) E) A
 := var125 (vs125 (vs125 (vs125 (vs125 vz125))))

def test125 {Γ A} : Tm125 Γ (arr125 (arr125 A A) (arr125 A A))
 := lam125 (lam125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 (app125 v1125 v0125)))))))


def Ty126 : Type 1
 := ∀ (Ty126 : Type)
      (ι   : Ty126)
      (arr : Ty126 → Ty126 → Ty126)
    , Ty126

def ι126 : Ty126 := λ _ ι126 _ => ι126

def arr126 : Ty126 → Ty126 → Ty126
 := λ A B Ty126 ι126 arr126 =>
     arr126 (A Ty126 ι126 arr126) (B Ty126 ι126 arr126)

def Con126 : Type 1
 := ∀ (Con126  : Type)
      (nil  : Con126)
      (snoc : Con126 → Ty126 → Con126)
    , Con126

def nil126 : Con126
 := λ Con126 nil126 snoc => nil126

def snoc126 : Con126 → Ty126 → Con126
 := λ Γ A Con126 nil126 snoc126 => snoc126 (Γ Con126 nil126 snoc126) A

def Var126 : Con126 → Ty126 → Type 1
 := λ Γ A =>
   ∀ (Var126 : Con126 → Ty126 → Type)
     (vz  : ∀ Γ A, Var126 (snoc126 Γ A) A)
     (vs  : ∀ Γ B A, Var126 Γ A → Var126 (snoc126 Γ B) A)
   , Var126 Γ A

def vz126 {Γ A} : Var126 (snoc126 Γ A) A
 := λ Var126 vz126 vs => vz126 _ _

def vs126 {Γ B A} : Var126 Γ A → Var126 (snoc126 Γ B) A
 := λ x Var126 vz126 vs126 => vs126 _ _ _ (x Var126 vz126 vs126)

def Tm126 : Con126 → Ty126 → Type 1
 := λ Γ A =>
   ∀ (Tm126  : Con126 → Ty126 → Type)
     (var   : ∀ Γ A     , Var126 Γ A → Tm126 Γ A)
     (lam   : ∀ Γ A B   , Tm126 (snoc126 Γ A) B → Tm126 Γ (arr126 A B))
     (app   : ∀ Γ A B   , Tm126 Γ (arr126 A B) → Tm126 Γ A → Tm126 Γ B)
   , Tm126 Γ A

def var126 {Γ A} : Var126 Γ A → Tm126 Γ A
 := λ x Tm126 var126 lam app =>
     var126 _ _ x

def lam126 {Γ A B} : Tm126 (snoc126 Γ A) B → Tm126 Γ (arr126 A B)
 := λ t Tm126 var126 lam126 app =>
     lam126 _ _ _ (t Tm126 var126 lam126 app)

def app126 {Γ A B} : Tm126 Γ (arr126 A B) → Tm126 Γ A → Tm126 Γ B
 := λ t u Tm126 var126 lam126 app126 =>
     app126 _ _ _
         (t Tm126 var126 lam126 app126)
         (u Tm126 var126 lam126 app126)

def v0126 {Γ A} : Tm126 (snoc126 Γ A) A
 := var126 vz126

def v1126 {Γ A B} : Tm126 (snoc126 (snoc126 Γ A) B) A
 := var126 (vs126 vz126)

def v2126 {Γ A B C} : Tm126 (snoc126 (snoc126 (snoc126 Γ A) B) C) A
 := var126 (vs126 (vs126 vz126))

def v3126 {Γ A B C D} : Tm126 (snoc126 (snoc126 (snoc126 (snoc126 Γ A) B) C) D) A
 := var126 (vs126 (vs126 (vs126 vz126)))

def v4126 {Γ A B C D E} : Tm126 (snoc126 (snoc126 (snoc126 (snoc126 (snoc126 Γ A) B) C) D) E) A
 := var126 (vs126 (vs126 (vs126 (vs126 vz126))))

def test126 {Γ A} : Tm126 Γ (arr126 (arr126 A A) (arr126 A A))
 := lam126 (lam126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 (app126 v1126 v0126)))))))


def Ty127 : Type 1
 := ∀ (Ty127 : Type)
      (ι   : Ty127)
      (arr : Ty127 → Ty127 → Ty127)
    , Ty127

def ι127 : Ty127 := λ _ ι127 _ => ι127

def arr127 : Ty127 → Ty127 → Ty127
 := λ A B Ty127 ι127 arr127 =>
     arr127 (A Ty127 ι127 arr127) (B Ty127 ι127 arr127)

def Con127 : Type 1
 := ∀ (Con127  : Type)
      (nil  : Con127)
      (snoc : Con127 → Ty127 → Con127)
    , Con127

def nil127 : Con127
 := λ Con127 nil127 snoc => nil127

def snoc127 : Con127 → Ty127 → Con127
 := λ Γ A Con127 nil127 snoc127 => snoc127 (Γ Con127 nil127 snoc127) A

def Var127 : Con127 → Ty127 → Type 1
 := λ Γ A =>
   ∀ (Var127 : Con127 → Ty127 → Type)
     (vz  : ∀ Γ A, Var127 (snoc127 Γ A) A)
     (vs  : ∀ Γ B A, Var127 Γ A → Var127 (snoc127 Γ B) A)
   , Var127 Γ A

def vz127 {Γ A} : Var127 (snoc127 Γ A) A
 := λ Var127 vz127 vs => vz127 _ _

def vs127 {Γ B A} : Var127 Γ A → Var127 (snoc127 Γ B) A
 := λ x Var127 vz127 vs127 => vs127 _ _ _ (x Var127 vz127 vs127)

def Tm127 : Con127 → Ty127 → Type 1
 := λ Γ A =>
   ∀ (Tm127  : Con127 → Ty127 → Type)
     (var   : ∀ Γ A     , Var127 Γ A → Tm127 Γ A)
     (lam   : ∀ Γ A B   , Tm127 (snoc127 Γ A) B → Tm127 Γ (arr127 A B))
     (app   : ∀ Γ A B   , Tm127 Γ (arr127 A B) → Tm127 Γ A → Tm127 Γ B)
   , Tm127 Γ A

def var127 {Γ A} : Var127 Γ A → Tm127 Γ A
 := λ x Tm127 var127 lam app =>
     var127 _ _ x

def lam127 {Γ A B} : Tm127 (snoc127 Γ A) B → Tm127 Γ (arr127 A B)
 := λ t Tm127 var127 lam127 app =>
     lam127 _ _ _ (t Tm127 var127 lam127 app)

def app127 {Γ A B} : Tm127 Γ (arr127 A B) → Tm127 Γ A → Tm127 Γ B
 := λ t u Tm127 var127 lam127 app127 =>
     app127 _ _ _
         (t Tm127 var127 lam127 app127)
         (u Tm127 var127 lam127 app127)

def v0127 {Γ A} : Tm127 (snoc127 Γ A) A
 := var127 vz127

def v1127 {Γ A B} : Tm127 (snoc127 (snoc127 Γ A) B) A
 := var127 (vs127 vz127)

def v2127 {Γ A B C} : Tm127 (snoc127 (snoc127 (snoc127 Γ A) B) C) A
 := var127 (vs127 (vs127 vz127))

def v3127 {Γ A B C D} : Tm127 (snoc127 (snoc127 (snoc127 (snoc127 Γ A) B) C) D) A
 := var127 (vs127 (vs127 (vs127 vz127)))

def v4127 {Γ A B C D E} : Tm127 (snoc127 (snoc127 (snoc127 (snoc127 (snoc127 Γ A) B) C) D) E) A
 := var127 (vs127 (vs127 (vs127 (vs127 vz127))))

def test127 {Γ A} : Tm127 Γ (arr127 (arr127 A A) (arr127 A A))
 := lam127 (lam127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 (app127 v1127 v0127)))))))


def Ty128 : Type 1
 := ∀ (Ty128 : Type)
      (ι   : Ty128)
      (arr : Ty128 → Ty128 → Ty128)
    , Ty128

def ι128 : Ty128 := λ _ ι128 _ => ι128

def arr128 : Ty128 → Ty128 → Ty128
 := λ A B Ty128 ι128 arr128 =>
     arr128 (A Ty128 ι128 arr128) (B Ty128 ι128 arr128)

def Con128 : Type 1
 := ∀ (Con128  : Type)
      (nil  : Con128)
      (snoc : Con128 → Ty128 → Con128)
    , Con128

def nil128 : Con128
 := λ Con128 nil128 snoc => nil128

def snoc128 : Con128 → Ty128 → Con128
 := λ Γ A Con128 nil128 snoc128 => snoc128 (Γ Con128 nil128 snoc128) A

def Var128 : Con128 → Ty128 → Type 1
 := λ Γ A =>
   ∀ (Var128 : Con128 → Ty128 → Type)
     (vz  : ∀ Γ A, Var128 (snoc128 Γ A) A)
     (vs  : ∀ Γ B A, Var128 Γ A → Var128 (snoc128 Γ B) A)
   , Var128 Γ A

def vz128 {Γ A} : Var128 (snoc128 Γ A) A
 := λ Var128 vz128 vs => vz128 _ _

def vs128 {Γ B A} : Var128 Γ A → Var128 (snoc128 Γ B) A
 := λ x Var128 vz128 vs128 => vs128 _ _ _ (x Var128 vz128 vs128)

def Tm128 : Con128 → Ty128 → Type 1
 := λ Γ A =>
   ∀ (Tm128  : Con128 → Ty128 → Type)
     (var   : ∀ Γ A     , Var128 Γ A → Tm128 Γ A)
     (lam   : ∀ Γ A B   , Tm128 (snoc128 Γ A) B → Tm128 Γ (arr128 A B))
     (app   : ∀ Γ A B   , Tm128 Γ (arr128 A B) → Tm128 Γ A → Tm128 Γ B)
   , Tm128 Γ A

def var128 {Γ A} : Var128 Γ A → Tm128 Γ A
 := λ x Tm128 var128 lam app =>
     var128 _ _ x

def lam128 {Γ A B} : Tm128 (snoc128 Γ A) B → Tm128 Γ (arr128 A B)
 := λ t Tm128 var128 lam128 app =>
     lam128 _ _ _ (t Tm128 var128 lam128 app)

def app128 {Γ A B} : Tm128 Γ (arr128 A B) → Tm128 Γ A → Tm128 Γ B
 := λ t u Tm128 var128 lam128 app128 =>
     app128 _ _ _
         (t Tm128 var128 lam128 app128)
         (u Tm128 var128 lam128 app128)

def v0128 {Γ A} : Tm128 (snoc128 Γ A) A
 := var128 vz128

def v1128 {Γ A B} : Tm128 (snoc128 (snoc128 Γ A) B) A
 := var128 (vs128 vz128)

def v2128 {Γ A B C} : Tm128 (snoc128 (snoc128 (snoc128 Γ A) B) C) A
 := var128 (vs128 (vs128 vz128))

def v3128 {Γ A B C D} : Tm128 (snoc128 (snoc128 (snoc128 (snoc128 Γ A) B) C) D) A
 := var128 (vs128 (vs128 (vs128 vz128)))

def v4128 {Γ A B C D E} : Tm128 (snoc128 (snoc128 (snoc128 (snoc128 (snoc128 Γ A) B) C) D) E) A
 := var128 (vs128 (vs128 (vs128 (vs128 vz128))))

def test128 {Γ A} : Tm128 Γ (arr128 (arr128 A A) (arr128 A A))
 := lam128 (lam128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 (app128 v1128 v0128)))))))


def Ty129 : Type 1
 := ∀ (Ty129 : Type)
      (ι   : Ty129)
      (arr : Ty129 → Ty129 → Ty129)
    , Ty129

def ι129 : Ty129 := λ _ ι129 _ => ι129

def arr129 : Ty129 → Ty129 → Ty129
 := λ A B Ty129 ι129 arr129 =>
     arr129 (A Ty129 ι129 arr129) (B Ty129 ι129 arr129)

def Con129 : Type 1
 := ∀ (Con129  : Type)
      (nil  : Con129)
      (snoc : Con129 → Ty129 → Con129)
    , Con129

def nil129 : Con129
 := λ Con129 nil129 snoc => nil129

def snoc129 : Con129 → Ty129 → Con129
 := λ Γ A Con129 nil129 snoc129 => snoc129 (Γ Con129 nil129 snoc129) A

def Var129 : Con129 → Ty129 → Type 1
 := λ Γ A =>
   ∀ (Var129 : Con129 → Ty129 → Type)
     (vz  : ∀ Γ A, Var129 (snoc129 Γ A) A)
     (vs  : ∀ Γ B A, Var129 Γ A → Var129 (snoc129 Γ B) A)
   , Var129 Γ A

def vz129 {Γ A} : Var129 (snoc129 Γ A) A
 := λ Var129 vz129 vs => vz129 _ _

def vs129 {Γ B A} : Var129 Γ A → Var129 (snoc129 Γ B) A
 := λ x Var129 vz129 vs129 => vs129 _ _ _ (x Var129 vz129 vs129)

def Tm129 : Con129 → Ty129 → Type 1
 := λ Γ A =>
   ∀ (Tm129  : Con129 → Ty129 → Type)
     (var   : ∀ Γ A     , Var129 Γ A → Tm129 Γ A)
     (lam   : ∀ Γ A B   , Tm129 (snoc129 Γ A) B → Tm129 Γ (arr129 A B))
     (app   : ∀ Γ A B   , Tm129 Γ (arr129 A B) → Tm129 Γ A → Tm129 Γ B)
   , Tm129 Γ A

def var129 {Γ A} : Var129 Γ A → Tm129 Γ A
 := λ x Tm129 var129 lam app =>
     var129 _ _ x

def lam129 {Γ A B} : Tm129 (snoc129 Γ A) B → Tm129 Γ (arr129 A B)
 := λ t Tm129 var129 lam129 app =>
     lam129 _ _ _ (t Tm129 var129 lam129 app)

def app129 {Γ A B} : Tm129 Γ (arr129 A B) → Tm129 Γ A → Tm129 Γ B
 := λ t u Tm129 var129 lam129 app129 =>
     app129 _ _ _
         (t Tm129 var129 lam129 app129)
         (u Tm129 var129 lam129 app129)

def v0129 {Γ A} : Tm129 (snoc129 Γ A) A
 := var129 vz129

def v1129 {Γ A B} : Tm129 (snoc129 (snoc129 Γ A) B) A
 := var129 (vs129 vz129)

def v2129 {Γ A B C} : Tm129 (snoc129 (snoc129 (snoc129 Γ A) B) C) A
 := var129 (vs129 (vs129 vz129))

def v3129 {Γ A B C D} : Tm129 (snoc129 (snoc129 (snoc129 (snoc129 Γ A) B) C) D) A
 := var129 (vs129 (vs129 (vs129 vz129)))

def v4129 {Γ A B C D E} : Tm129 (snoc129 (snoc129 (snoc129 (snoc129 (snoc129 Γ A) B) C) D) E) A
 := var129 (vs129 (vs129 (vs129 (vs129 vz129))))

def test129 {Γ A} : Tm129 Γ (arr129 (arr129 A A) (arr129 A A))
 := lam129 (lam129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 (app129 v1129 v0129)))))))


def Ty130 : Type 1
 := ∀ (Ty130 : Type)
      (ι   : Ty130)
      (arr : Ty130 → Ty130 → Ty130)
    , Ty130

def ι130 : Ty130 := λ _ ι130 _ => ι130

def arr130 : Ty130 → Ty130 → Ty130
 := λ A B Ty130 ι130 arr130 =>
     arr130 (A Ty130 ι130 arr130) (B Ty130 ι130 arr130)

def Con130 : Type 1
 := ∀ (Con130  : Type)
      (nil  : Con130)
      (snoc : Con130 → Ty130 → Con130)
    , Con130

def nil130 : Con130
 := λ Con130 nil130 snoc => nil130

def snoc130 : Con130 → Ty130 → Con130
 := λ Γ A Con130 nil130 snoc130 => snoc130 (Γ Con130 nil130 snoc130) A

def Var130 : Con130 → Ty130 → Type 1
 := λ Γ A =>
   ∀ (Var130 : Con130 → Ty130 → Type)
     (vz  : ∀ Γ A, Var130 (snoc130 Γ A) A)
     (vs  : ∀ Γ B A, Var130 Γ A → Var130 (snoc130 Γ B) A)
   , Var130 Γ A

def vz130 {Γ A} : Var130 (snoc130 Γ A) A
 := λ Var130 vz130 vs => vz130 _ _

def vs130 {Γ B A} : Var130 Γ A → Var130 (snoc130 Γ B) A
 := λ x Var130 vz130 vs130 => vs130 _ _ _ (x Var130 vz130 vs130)

def Tm130 : Con130 → Ty130 → Type 1
 := λ Γ A =>
   ∀ (Tm130  : Con130 → Ty130 → Type)
     (var   : ∀ Γ A     , Var130 Γ A → Tm130 Γ A)
     (lam   : ∀ Γ A B   , Tm130 (snoc130 Γ A) B → Tm130 Γ (arr130 A B))
     (app   : ∀ Γ A B   , Tm130 Γ (arr130 A B) → Tm130 Γ A → Tm130 Γ B)
   , Tm130 Γ A

def var130 {Γ A} : Var130 Γ A → Tm130 Γ A
 := λ x Tm130 var130 lam app =>
     var130 _ _ x

def lam130 {Γ A B} : Tm130 (snoc130 Γ A) B → Tm130 Γ (arr130 A B)
 := λ t Tm130 var130 lam130 app =>
     lam130 _ _ _ (t Tm130 var130 lam130 app)

def app130 {Γ A B} : Tm130 Γ (arr130 A B) → Tm130 Γ A → Tm130 Γ B
 := λ t u Tm130 var130 lam130 app130 =>
     app130 _ _ _
         (t Tm130 var130 lam130 app130)
         (u Tm130 var130 lam130 app130)

def v0130 {Γ A} : Tm130 (snoc130 Γ A) A
 := var130 vz130

def v1130 {Γ A B} : Tm130 (snoc130 (snoc130 Γ A) B) A
 := var130 (vs130 vz130)

def v2130 {Γ A B C} : Tm130 (snoc130 (snoc130 (snoc130 Γ A) B) C) A
 := var130 (vs130 (vs130 vz130))

def v3130 {Γ A B C D} : Tm130 (snoc130 (snoc130 (snoc130 (snoc130 Γ A) B) C) D) A
 := var130 (vs130 (vs130 (vs130 vz130)))

def v4130 {Γ A B C D E} : Tm130 (snoc130 (snoc130 (snoc130 (snoc130 (snoc130 Γ A) B) C) D) E) A
 := var130 (vs130 (vs130 (vs130 (vs130 vz130))))

def test130 {Γ A} : Tm130 Γ (arr130 (arr130 A A) (arr130 A A))
 := lam130 (lam130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 (app130 v1130 v0130)))))))


def Ty131 : Type 1
 := ∀ (Ty131 : Type)
      (ι   : Ty131)
      (arr : Ty131 → Ty131 → Ty131)
    , Ty131

def ι131 : Ty131 := λ _ ι131 _ => ι131

def arr131 : Ty131 → Ty131 → Ty131
 := λ A B Ty131 ι131 arr131 =>
     arr131 (A Ty131 ι131 arr131) (B Ty131 ι131 arr131)

def Con131 : Type 1
 := ∀ (Con131  : Type)
      (nil  : Con131)
      (snoc : Con131 → Ty131 → Con131)
    , Con131

def nil131 : Con131
 := λ Con131 nil131 snoc => nil131

def snoc131 : Con131 → Ty131 → Con131
 := λ Γ A Con131 nil131 snoc131 => snoc131 (Γ Con131 nil131 snoc131) A

def Var131 : Con131 → Ty131 → Type 1
 := λ Γ A =>
   ∀ (Var131 : Con131 → Ty131 → Type)
     (vz  : ∀ Γ A, Var131 (snoc131 Γ A) A)
     (vs  : ∀ Γ B A, Var131 Γ A → Var131 (snoc131 Γ B) A)
   , Var131 Γ A

def vz131 {Γ A} : Var131 (snoc131 Γ A) A
 := λ Var131 vz131 vs => vz131 _ _

def vs131 {Γ B A} : Var131 Γ A → Var131 (snoc131 Γ B) A
 := λ x Var131 vz131 vs131 => vs131 _ _ _ (x Var131 vz131 vs131)

def Tm131 : Con131 → Ty131 → Type 1
 := λ Γ A =>
   ∀ (Tm131  : Con131 → Ty131 → Type)
     (var   : ∀ Γ A     , Var131 Γ A → Tm131 Γ A)
     (lam   : ∀ Γ A B   , Tm131 (snoc131 Γ A) B → Tm131 Γ (arr131 A B))
     (app   : ∀ Γ A B   , Tm131 Γ (arr131 A B) → Tm131 Γ A → Tm131 Γ B)
   , Tm131 Γ A

def var131 {Γ A} : Var131 Γ A → Tm131 Γ A
 := λ x Tm131 var131 lam app =>
     var131 _ _ x

def lam131 {Γ A B} : Tm131 (snoc131 Γ A) B → Tm131 Γ (arr131 A B)
 := λ t Tm131 var131 lam131 app =>
     lam131 _ _ _ (t Tm131 var131 lam131 app)

def app131 {Γ A B} : Tm131 Γ (arr131 A B) → Tm131 Γ A → Tm131 Γ B
 := λ t u Tm131 var131 lam131 app131 =>
     app131 _ _ _
         (t Tm131 var131 lam131 app131)
         (u Tm131 var131 lam131 app131)

def v0131 {Γ A} : Tm131 (snoc131 Γ A) A
 := var131 vz131

def v1131 {Γ A B} : Tm131 (snoc131 (snoc131 Γ A) B) A
 := var131 (vs131 vz131)

def v2131 {Γ A B C} : Tm131 (snoc131 (snoc131 (snoc131 Γ A) B) C) A
 := var131 (vs131 (vs131 vz131))

def v3131 {Γ A B C D} : Tm131 (snoc131 (snoc131 (snoc131 (snoc131 Γ A) B) C) D) A
 := var131 (vs131 (vs131 (vs131 vz131)))

def v4131 {Γ A B C D E} : Tm131 (snoc131 (snoc131 (snoc131 (snoc131 (snoc131 Γ A) B) C) D) E) A
 := var131 (vs131 (vs131 (vs131 (vs131 vz131))))

def test131 {Γ A} : Tm131 Γ (arr131 (arr131 A A) (arr131 A A))
 := lam131 (lam131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 (app131 v1131 v0131)))))))


def Ty132 : Type 1
 := ∀ (Ty132 : Type)
      (ι   : Ty132)
      (arr : Ty132 → Ty132 → Ty132)
    , Ty132

def ι132 : Ty132 := λ _ ι132 _ => ι132

def arr132 : Ty132 → Ty132 → Ty132
 := λ A B Ty132 ι132 arr132 =>
     arr132 (A Ty132 ι132 arr132) (B Ty132 ι132 arr132)

def Con132 : Type 1
 := ∀ (Con132  : Type)
      (nil  : Con132)
      (snoc : Con132 → Ty132 → Con132)
    , Con132

def nil132 : Con132
 := λ Con132 nil132 snoc => nil132

def snoc132 : Con132 → Ty132 → Con132
 := λ Γ A Con132 nil132 snoc132 => snoc132 (Γ Con132 nil132 snoc132) A

def Var132 : Con132 → Ty132 → Type 1
 := λ Γ A =>
   ∀ (Var132 : Con132 → Ty132 → Type)
     (vz  : ∀ Γ A, Var132 (snoc132 Γ A) A)
     (vs  : ∀ Γ B A, Var132 Γ A → Var132 (snoc132 Γ B) A)
   , Var132 Γ A

def vz132 {Γ A} : Var132 (snoc132 Γ A) A
 := λ Var132 vz132 vs => vz132 _ _

def vs132 {Γ B A} : Var132 Γ A → Var132 (snoc132 Γ B) A
 := λ x Var132 vz132 vs132 => vs132 _ _ _ (x Var132 vz132 vs132)

def Tm132 : Con132 → Ty132 → Type 1
 := λ Γ A =>
   ∀ (Tm132  : Con132 → Ty132 → Type)
     (var   : ∀ Γ A     , Var132 Γ A → Tm132 Γ A)
     (lam   : ∀ Γ A B   , Tm132 (snoc132 Γ A) B → Tm132 Γ (arr132 A B))
     (app   : ∀ Γ A B   , Tm132 Γ (arr132 A B) → Tm132 Γ A → Tm132 Γ B)
   , Tm132 Γ A

def var132 {Γ A} : Var132 Γ A → Tm132 Γ A
 := λ x Tm132 var132 lam app =>
     var132 _ _ x

def lam132 {Γ A B} : Tm132 (snoc132 Γ A) B → Tm132 Γ (arr132 A B)
 := λ t Tm132 var132 lam132 app =>
     lam132 _ _ _ (t Tm132 var132 lam132 app)

def app132 {Γ A B} : Tm132 Γ (arr132 A B) → Tm132 Γ A → Tm132 Γ B
 := λ t u Tm132 var132 lam132 app132 =>
     app132 _ _ _
         (t Tm132 var132 lam132 app132)
         (u Tm132 var132 lam132 app132)

def v0132 {Γ A} : Tm132 (snoc132 Γ A) A
 := var132 vz132

def v1132 {Γ A B} : Tm132 (snoc132 (snoc132 Γ A) B) A
 := var132 (vs132 vz132)

def v2132 {Γ A B C} : Tm132 (snoc132 (snoc132 (snoc132 Γ A) B) C) A
 := var132 (vs132 (vs132 vz132))

def v3132 {Γ A B C D} : Tm132 (snoc132 (snoc132 (snoc132 (snoc132 Γ A) B) C) D) A
 := var132 (vs132 (vs132 (vs132 vz132)))

def v4132 {Γ A B C D E} : Tm132 (snoc132 (snoc132 (snoc132 (snoc132 (snoc132 Γ A) B) C) D) E) A
 := var132 (vs132 (vs132 (vs132 (vs132 vz132))))

def test132 {Γ A} : Tm132 Γ (arr132 (arr132 A A) (arr132 A A))
 := lam132 (lam132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 (app132 v1132 v0132)))))))


def Ty133 : Type 1
 := ∀ (Ty133 : Type)
      (ι   : Ty133)
      (arr : Ty133 → Ty133 → Ty133)
    , Ty133

def ι133 : Ty133 := λ _ ι133 _ => ι133

def arr133 : Ty133 → Ty133 → Ty133
 := λ A B Ty133 ι133 arr133 =>
     arr133 (A Ty133 ι133 arr133) (B Ty133 ι133 arr133)

def Con133 : Type 1
 := ∀ (Con133  : Type)
      (nil  : Con133)
      (snoc : Con133 → Ty133 → Con133)
    , Con133

def nil133 : Con133
 := λ Con133 nil133 snoc => nil133

def snoc133 : Con133 → Ty133 → Con133
 := λ Γ A Con133 nil133 snoc133 => snoc133 (Γ Con133 nil133 snoc133) A

def Var133 : Con133 → Ty133 → Type 1
 := λ Γ A =>
   ∀ (Var133 : Con133 → Ty133 → Type)
     (vz  : ∀ Γ A, Var133 (snoc133 Γ A) A)
     (vs  : ∀ Γ B A, Var133 Γ A → Var133 (snoc133 Γ B) A)
   , Var133 Γ A

def vz133 {Γ A} : Var133 (snoc133 Γ A) A
 := λ Var133 vz133 vs => vz133 _ _

def vs133 {Γ B A} : Var133 Γ A → Var133 (snoc133 Γ B) A
 := λ x Var133 vz133 vs133 => vs133 _ _ _ (x Var133 vz133 vs133)

def Tm133 : Con133 → Ty133 → Type 1
 := λ Γ A =>
   ∀ (Tm133  : Con133 → Ty133 → Type)
     (var   : ∀ Γ A     , Var133 Γ A → Tm133 Γ A)
     (lam   : ∀ Γ A B   , Tm133 (snoc133 Γ A) B → Tm133 Γ (arr133 A B))
     (app   : ∀ Γ A B   , Tm133 Γ (arr133 A B) → Tm133 Γ A → Tm133 Γ B)
   , Tm133 Γ A

def var133 {Γ A} : Var133 Γ A → Tm133 Γ A
 := λ x Tm133 var133 lam app =>
     var133 _ _ x

def lam133 {Γ A B} : Tm133 (snoc133 Γ A) B → Tm133 Γ (arr133 A B)
 := λ t Tm133 var133 lam133 app =>
     lam133 _ _ _ (t Tm133 var133 lam133 app)

def app133 {Γ A B} : Tm133 Γ (arr133 A B) → Tm133 Γ A → Tm133 Γ B
 := λ t u Tm133 var133 lam133 app133 =>
     app133 _ _ _
         (t Tm133 var133 lam133 app133)
         (u Tm133 var133 lam133 app133)

def v0133 {Γ A} : Tm133 (snoc133 Γ A) A
 := var133 vz133

def v1133 {Γ A B} : Tm133 (snoc133 (snoc133 Γ A) B) A
 := var133 (vs133 vz133)

def v2133 {Γ A B C} : Tm133 (snoc133 (snoc133 (snoc133 Γ A) B) C) A
 := var133 (vs133 (vs133 vz133))

def v3133 {Γ A B C D} : Tm133 (snoc133 (snoc133 (snoc133 (snoc133 Γ A) B) C) D) A
 := var133 (vs133 (vs133 (vs133 vz133)))

def v4133 {Γ A B C D E} : Tm133 (snoc133 (snoc133 (snoc133 (snoc133 (snoc133 Γ A) B) C) D) E) A
 := var133 (vs133 (vs133 (vs133 (vs133 vz133))))

def test133 {Γ A} : Tm133 Γ (arr133 (arr133 A A) (arr133 A A))
 := lam133 (lam133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 (app133 v1133 v0133)))))))


def Ty134 : Type 1
 := ∀ (Ty134 : Type)
      (ι   : Ty134)
      (arr : Ty134 → Ty134 → Ty134)
    , Ty134

def ι134 : Ty134 := λ _ ι134 _ => ι134

def arr134 : Ty134 → Ty134 → Ty134
 := λ A B Ty134 ι134 arr134 =>
     arr134 (A Ty134 ι134 arr134) (B Ty134 ι134 arr134)

def Con134 : Type 1
 := ∀ (Con134  : Type)
      (nil  : Con134)
      (snoc : Con134 → Ty134 → Con134)
    , Con134

def nil134 : Con134
 := λ Con134 nil134 snoc => nil134

def snoc134 : Con134 → Ty134 → Con134
 := λ Γ A Con134 nil134 snoc134 => snoc134 (Γ Con134 nil134 snoc134) A

def Var134 : Con134 → Ty134 → Type 1
 := λ Γ A =>
   ∀ (Var134 : Con134 → Ty134 → Type)
     (vz  : ∀ Γ A, Var134 (snoc134 Γ A) A)
     (vs  : ∀ Γ B A, Var134 Γ A → Var134 (snoc134 Γ B) A)
   , Var134 Γ A

def vz134 {Γ A} : Var134 (snoc134 Γ A) A
 := λ Var134 vz134 vs => vz134 _ _

def vs134 {Γ B A} : Var134 Γ A → Var134 (snoc134 Γ B) A
 := λ x Var134 vz134 vs134 => vs134 _ _ _ (x Var134 vz134 vs134)

def Tm134 : Con134 → Ty134 → Type 1
 := λ Γ A =>
   ∀ (Tm134  : Con134 → Ty134 → Type)
     (var   : ∀ Γ A     , Var134 Γ A → Tm134 Γ A)
     (lam   : ∀ Γ A B   , Tm134 (snoc134 Γ A) B → Tm134 Γ (arr134 A B))
     (app   : ∀ Γ A B   , Tm134 Γ (arr134 A B) → Tm134 Γ A → Tm134 Γ B)
   , Tm134 Γ A

def var134 {Γ A} : Var134 Γ A → Tm134 Γ A
 := λ x Tm134 var134 lam app =>
     var134 _ _ x

def lam134 {Γ A B} : Tm134 (snoc134 Γ A) B → Tm134 Γ (arr134 A B)
 := λ t Tm134 var134 lam134 app =>
     lam134 _ _ _ (t Tm134 var134 lam134 app)

def app134 {Γ A B} : Tm134 Γ (arr134 A B) → Tm134 Γ A → Tm134 Γ B
 := λ t u Tm134 var134 lam134 app134 =>
     app134 _ _ _
         (t Tm134 var134 lam134 app134)
         (u Tm134 var134 lam134 app134)

def v0134 {Γ A} : Tm134 (snoc134 Γ A) A
 := var134 vz134

def v1134 {Γ A B} : Tm134 (snoc134 (snoc134 Γ A) B) A
 := var134 (vs134 vz134)

def v2134 {Γ A B C} : Tm134 (snoc134 (snoc134 (snoc134 Γ A) B) C) A
 := var134 (vs134 (vs134 vz134))

def v3134 {Γ A B C D} : Tm134 (snoc134 (snoc134 (snoc134 (snoc134 Γ A) B) C) D) A
 := var134 (vs134 (vs134 (vs134 vz134)))

def v4134 {Γ A B C D E} : Tm134 (snoc134 (snoc134 (snoc134 (snoc134 (snoc134 Γ A) B) C) D) E) A
 := var134 (vs134 (vs134 (vs134 (vs134 vz134))))

def test134 {Γ A} : Tm134 Γ (arr134 (arr134 A A) (arr134 A A))
 := lam134 (lam134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 (app134 v1134 v0134)))))))


def Ty135 : Type 1
 := ∀ (Ty135 : Type)
      (ι   : Ty135)
      (arr : Ty135 → Ty135 → Ty135)
    , Ty135

def ι135 : Ty135 := λ _ ι135 _ => ι135

def arr135 : Ty135 → Ty135 → Ty135
 := λ A B Ty135 ι135 arr135 =>
     arr135 (A Ty135 ι135 arr135) (B Ty135 ι135 arr135)

def Con135 : Type 1
 := ∀ (Con135  : Type)
      (nil  : Con135)
      (snoc : Con135 → Ty135 → Con135)
    , Con135

def nil135 : Con135
 := λ Con135 nil135 snoc => nil135

def snoc135 : Con135 → Ty135 → Con135
 := λ Γ A Con135 nil135 snoc135 => snoc135 (Γ Con135 nil135 snoc135) A

def Var135 : Con135 → Ty135 → Type 1
 := λ Γ A =>
   ∀ (Var135 : Con135 → Ty135 → Type)
     (vz  : ∀ Γ A, Var135 (snoc135 Γ A) A)
     (vs  : ∀ Γ B A, Var135 Γ A → Var135 (snoc135 Γ B) A)
   , Var135 Γ A

def vz135 {Γ A} : Var135 (snoc135 Γ A) A
 := λ Var135 vz135 vs => vz135 _ _

def vs135 {Γ B A} : Var135 Γ A → Var135 (snoc135 Γ B) A
 := λ x Var135 vz135 vs135 => vs135 _ _ _ (x Var135 vz135 vs135)

def Tm135 : Con135 → Ty135 → Type 1
 := λ Γ A =>
   ∀ (Tm135  : Con135 → Ty135 → Type)
     (var   : ∀ Γ A     , Var135 Γ A → Tm135 Γ A)
     (lam   : ∀ Γ A B   , Tm135 (snoc135 Γ A) B → Tm135 Γ (arr135 A B))
     (app   : ∀ Γ A B   , Tm135 Γ (arr135 A B) → Tm135 Γ A → Tm135 Γ B)
   , Tm135 Γ A

def var135 {Γ A} : Var135 Γ A → Tm135 Γ A
 := λ x Tm135 var135 lam app =>
     var135 _ _ x

def lam135 {Γ A B} : Tm135 (snoc135 Γ A) B → Tm135 Γ (arr135 A B)
 := λ t Tm135 var135 lam135 app =>
     lam135 _ _ _ (t Tm135 var135 lam135 app)

def app135 {Γ A B} : Tm135 Γ (arr135 A B) → Tm135 Γ A → Tm135 Γ B
 := λ t u Tm135 var135 lam135 app135 =>
     app135 _ _ _
         (t Tm135 var135 lam135 app135)
         (u Tm135 var135 lam135 app135)

def v0135 {Γ A} : Tm135 (snoc135 Γ A) A
 := var135 vz135

def v1135 {Γ A B} : Tm135 (snoc135 (snoc135 Γ A) B) A
 := var135 (vs135 vz135)

def v2135 {Γ A B C} : Tm135 (snoc135 (snoc135 (snoc135 Γ A) B) C) A
 := var135 (vs135 (vs135 vz135))

def v3135 {Γ A B C D} : Tm135 (snoc135 (snoc135 (snoc135 (snoc135 Γ A) B) C) D) A
 := var135 (vs135 (vs135 (vs135 vz135)))

def v4135 {Γ A B C D E} : Tm135 (snoc135 (snoc135 (snoc135 (snoc135 (snoc135 Γ A) B) C) D) E) A
 := var135 (vs135 (vs135 (vs135 (vs135 vz135))))

def test135 {Γ A} : Tm135 Γ (arr135 (arr135 A A) (arr135 A A))
 := lam135 (lam135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 (app135 v1135 v0135)))))))


def Ty136 : Type 1
 := ∀ (Ty136 : Type)
      (ι   : Ty136)
      (arr : Ty136 → Ty136 → Ty136)
    , Ty136

def ι136 : Ty136 := λ _ ι136 _ => ι136

def arr136 : Ty136 → Ty136 → Ty136
 := λ A B Ty136 ι136 arr136 =>
     arr136 (A Ty136 ι136 arr136) (B Ty136 ι136 arr136)

def Con136 : Type 1
 := ∀ (Con136  : Type)
      (nil  : Con136)
      (snoc : Con136 → Ty136 → Con136)
    , Con136

def nil136 : Con136
 := λ Con136 nil136 snoc => nil136

def snoc136 : Con136 → Ty136 → Con136
 := λ Γ A Con136 nil136 snoc136 => snoc136 (Γ Con136 nil136 snoc136) A

def Var136 : Con136 → Ty136 → Type 1
 := λ Γ A =>
   ∀ (Var136 : Con136 → Ty136 → Type)
     (vz  : ∀ Γ A, Var136 (snoc136 Γ A) A)
     (vs  : ∀ Γ B A, Var136 Γ A → Var136 (snoc136 Γ B) A)
   , Var136 Γ A

def vz136 {Γ A} : Var136 (snoc136 Γ A) A
 := λ Var136 vz136 vs => vz136 _ _

def vs136 {Γ B A} : Var136 Γ A → Var136 (snoc136 Γ B) A
 := λ x Var136 vz136 vs136 => vs136 _ _ _ (x Var136 vz136 vs136)

def Tm136 : Con136 → Ty136 → Type 1
 := λ Γ A =>
   ∀ (Tm136  : Con136 → Ty136 → Type)
     (var   : ∀ Γ A     , Var136 Γ A → Tm136 Γ A)
     (lam   : ∀ Γ A B   , Tm136 (snoc136 Γ A) B → Tm136 Γ (arr136 A B))
     (app   : ∀ Γ A B   , Tm136 Γ (arr136 A B) → Tm136 Γ A → Tm136 Γ B)
   , Tm136 Γ A

def var136 {Γ A} : Var136 Γ A → Tm136 Γ A
 := λ x Tm136 var136 lam app =>
     var136 _ _ x

def lam136 {Γ A B} : Tm136 (snoc136 Γ A) B → Tm136 Γ (arr136 A B)
 := λ t Tm136 var136 lam136 app =>
     lam136 _ _ _ (t Tm136 var136 lam136 app)

def app136 {Γ A B} : Tm136 Γ (arr136 A B) → Tm136 Γ A → Tm136 Γ B
 := λ t u Tm136 var136 lam136 app136 =>
     app136 _ _ _
         (t Tm136 var136 lam136 app136)
         (u Tm136 var136 lam136 app136)

def v0136 {Γ A} : Tm136 (snoc136 Γ A) A
 := var136 vz136

def v1136 {Γ A B} : Tm136 (snoc136 (snoc136 Γ A) B) A
 := var136 (vs136 vz136)

def v2136 {Γ A B C} : Tm136 (snoc136 (snoc136 (snoc136 Γ A) B) C) A
 := var136 (vs136 (vs136 vz136))

def v3136 {Γ A B C D} : Tm136 (snoc136 (snoc136 (snoc136 (snoc136 Γ A) B) C) D) A
 := var136 (vs136 (vs136 (vs136 vz136)))

def v4136 {Γ A B C D E} : Tm136 (snoc136 (snoc136 (snoc136 (snoc136 (snoc136 Γ A) B) C) D) E) A
 := var136 (vs136 (vs136 (vs136 (vs136 vz136))))

def test136 {Γ A} : Tm136 Γ (arr136 (arr136 A A) (arr136 A A))
 := lam136 (lam136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 (app136 v1136 v0136)))))))


def Ty137 : Type 1
 := ∀ (Ty137 : Type)
      (ι   : Ty137)
      (arr : Ty137 → Ty137 → Ty137)
    , Ty137

def ι137 : Ty137 := λ _ ι137 _ => ι137

def arr137 : Ty137 → Ty137 → Ty137
 := λ A B Ty137 ι137 arr137 =>
     arr137 (A Ty137 ι137 arr137) (B Ty137 ι137 arr137)

def Con137 : Type 1
 := ∀ (Con137  : Type)
      (nil  : Con137)
      (snoc : Con137 → Ty137 → Con137)
    , Con137

def nil137 : Con137
 := λ Con137 nil137 snoc => nil137

def snoc137 : Con137 → Ty137 → Con137
 := λ Γ A Con137 nil137 snoc137 => snoc137 (Γ Con137 nil137 snoc137) A

def Var137 : Con137 → Ty137 → Type 1
 := λ Γ A =>
   ∀ (Var137 : Con137 → Ty137 → Type)
     (vz  : ∀ Γ A, Var137 (snoc137 Γ A) A)
     (vs  : ∀ Γ B A, Var137 Γ A → Var137 (snoc137 Γ B) A)
   , Var137 Γ A

def vz137 {Γ A} : Var137 (snoc137 Γ A) A
 := λ Var137 vz137 vs => vz137 _ _

def vs137 {Γ B A} : Var137 Γ A → Var137 (snoc137 Γ B) A
 := λ x Var137 vz137 vs137 => vs137 _ _ _ (x Var137 vz137 vs137)

def Tm137 : Con137 → Ty137 → Type 1
 := λ Γ A =>
   ∀ (Tm137  : Con137 → Ty137 → Type)
     (var   : ∀ Γ A     , Var137 Γ A → Tm137 Γ A)
     (lam   : ∀ Γ A B   , Tm137 (snoc137 Γ A) B → Tm137 Γ (arr137 A B))
     (app   : ∀ Γ A B   , Tm137 Γ (arr137 A B) → Tm137 Γ A → Tm137 Γ B)
   , Tm137 Γ A

def var137 {Γ A} : Var137 Γ A → Tm137 Γ A
 := λ x Tm137 var137 lam app =>
     var137 _ _ x

def lam137 {Γ A B} : Tm137 (snoc137 Γ A) B → Tm137 Γ (arr137 A B)
 := λ t Tm137 var137 lam137 app =>
     lam137 _ _ _ (t Tm137 var137 lam137 app)

def app137 {Γ A B} : Tm137 Γ (arr137 A B) → Tm137 Γ A → Tm137 Γ B
 := λ t u Tm137 var137 lam137 app137 =>
     app137 _ _ _
         (t Tm137 var137 lam137 app137)
         (u Tm137 var137 lam137 app137)

def v0137 {Γ A} : Tm137 (snoc137 Γ A) A
 := var137 vz137

def v1137 {Γ A B} : Tm137 (snoc137 (snoc137 Γ A) B) A
 := var137 (vs137 vz137)

def v2137 {Γ A B C} : Tm137 (snoc137 (snoc137 (snoc137 Γ A) B) C) A
 := var137 (vs137 (vs137 vz137))

def v3137 {Γ A B C D} : Tm137 (snoc137 (snoc137 (snoc137 (snoc137 Γ A) B) C) D) A
 := var137 (vs137 (vs137 (vs137 vz137)))

def v4137 {Γ A B C D E} : Tm137 (snoc137 (snoc137 (snoc137 (snoc137 (snoc137 Γ A) B) C) D) E) A
 := var137 (vs137 (vs137 (vs137 (vs137 vz137))))

def test137 {Γ A} : Tm137 Γ (arr137 (arr137 A A) (arr137 A A))
 := lam137 (lam137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 (app137 v1137 v0137)))))))


def Ty138 : Type 1
 := ∀ (Ty138 : Type)
      (ι   : Ty138)
      (arr : Ty138 → Ty138 → Ty138)
    , Ty138

def ι138 : Ty138 := λ _ ι138 _ => ι138

def arr138 : Ty138 → Ty138 → Ty138
 := λ A B Ty138 ι138 arr138 =>
     arr138 (A Ty138 ι138 arr138) (B Ty138 ι138 arr138)

def Con138 : Type 1
 := ∀ (Con138  : Type)
      (nil  : Con138)
      (snoc : Con138 → Ty138 → Con138)
    , Con138

def nil138 : Con138
 := λ Con138 nil138 snoc => nil138

def snoc138 : Con138 → Ty138 → Con138
 := λ Γ A Con138 nil138 snoc138 => snoc138 (Γ Con138 nil138 snoc138) A

def Var138 : Con138 → Ty138 → Type 1
 := λ Γ A =>
   ∀ (Var138 : Con138 → Ty138 → Type)
     (vz  : ∀ Γ A, Var138 (snoc138 Γ A) A)
     (vs  : ∀ Γ B A, Var138 Γ A → Var138 (snoc138 Γ B) A)
   , Var138 Γ A

def vz138 {Γ A} : Var138 (snoc138 Γ A) A
 := λ Var138 vz138 vs => vz138 _ _

def vs138 {Γ B A} : Var138 Γ A → Var138 (snoc138 Γ B) A
 := λ x Var138 vz138 vs138 => vs138 _ _ _ (x Var138 vz138 vs138)

def Tm138 : Con138 → Ty138 → Type 1
 := λ Γ A =>
   ∀ (Tm138  : Con138 → Ty138 → Type)
     (var   : ∀ Γ A     , Var138 Γ A → Tm138 Γ A)
     (lam   : ∀ Γ A B   , Tm138 (snoc138 Γ A) B → Tm138 Γ (arr138 A B))
     (app   : ∀ Γ A B   , Tm138 Γ (arr138 A B) → Tm138 Γ A → Tm138 Γ B)
   , Tm138 Γ A

def var138 {Γ A} : Var138 Γ A → Tm138 Γ A
 := λ x Tm138 var138 lam app =>
     var138 _ _ x

def lam138 {Γ A B} : Tm138 (snoc138 Γ A) B → Tm138 Γ (arr138 A B)
 := λ t Tm138 var138 lam138 app =>
     lam138 _ _ _ (t Tm138 var138 lam138 app)

def app138 {Γ A B} : Tm138 Γ (arr138 A B) → Tm138 Γ A → Tm138 Γ B
 := λ t u Tm138 var138 lam138 app138 =>
     app138 _ _ _
         (t Tm138 var138 lam138 app138)
         (u Tm138 var138 lam138 app138)

def v0138 {Γ A} : Tm138 (snoc138 Γ A) A
 := var138 vz138

def v1138 {Γ A B} : Tm138 (snoc138 (snoc138 Γ A) B) A
 := var138 (vs138 vz138)

def v2138 {Γ A B C} : Tm138 (snoc138 (snoc138 (snoc138 Γ A) B) C) A
 := var138 (vs138 (vs138 vz138))

def v3138 {Γ A B C D} : Tm138 (snoc138 (snoc138 (snoc138 (snoc138 Γ A) B) C) D) A
 := var138 (vs138 (vs138 (vs138 vz138)))

def v4138 {Γ A B C D E} : Tm138 (snoc138 (snoc138 (snoc138 (snoc138 (snoc138 Γ A) B) C) D) E) A
 := var138 (vs138 (vs138 (vs138 (vs138 vz138))))

def test138 {Γ A} : Tm138 Γ (arr138 (arr138 A A) (arr138 A A))
 := lam138 (lam138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 (app138 v1138 v0138)))))))


def Ty139 : Type 1
 := ∀ (Ty139 : Type)
      (ι   : Ty139)
      (arr : Ty139 → Ty139 → Ty139)
    , Ty139

def ι139 : Ty139 := λ _ ι139 _ => ι139

def arr139 : Ty139 → Ty139 → Ty139
 := λ A B Ty139 ι139 arr139 =>
     arr139 (A Ty139 ι139 arr139) (B Ty139 ι139 arr139)

def Con139 : Type 1
 := ∀ (Con139  : Type)
      (nil  : Con139)
      (snoc : Con139 → Ty139 → Con139)
    , Con139

def nil139 : Con139
 := λ Con139 nil139 snoc => nil139

def snoc139 : Con139 → Ty139 → Con139
 := λ Γ A Con139 nil139 snoc139 => snoc139 (Γ Con139 nil139 snoc139) A

def Var139 : Con139 → Ty139 → Type 1
 := λ Γ A =>
   ∀ (Var139 : Con139 → Ty139 → Type)
     (vz  : ∀ Γ A, Var139 (snoc139 Γ A) A)
     (vs  : ∀ Γ B A, Var139 Γ A → Var139 (snoc139 Γ B) A)
   , Var139 Γ A

def vz139 {Γ A} : Var139 (snoc139 Γ A) A
 := λ Var139 vz139 vs => vz139 _ _

def vs139 {Γ B A} : Var139 Γ A → Var139 (snoc139 Γ B) A
 := λ x Var139 vz139 vs139 => vs139 _ _ _ (x Var139 vz139 vs139)

def Tm139 : Con139 → Ty139 → Type 1
 := λ Γ A =>
   ∀ (Tm139  : Con139 → Ty139 → Type)
     (var   : ∀ Γ A     , Var139 Γ A → Tm139 Γ A)
     (lam   : ∀ Γ A B   , Tm139 (snoc139 Γ A) B → Tm139 Γ (arr139 A B))
     (app   : ∀ Γ A B   , Tm139 Γ (arr139 A B) → Tm139 Γ A → Tm139 Γ B)
   , Tm139 Γ A

def var139 {Γ A} : Var139 Γ A → Tm139 Γ A
 := λ x Tm139 var139 lam app =>
     var139 _ _ x

def lam139 {Γ A B} : Tm139 (snoc139 Γ A) B → Tm139 Γ (arr139 A B)
 := λ t Tm139 var139 lam139 app =>
     lam139 _ _ _ (t Tm139 var139 lam139 app)

def app139 {Γ A B} : Tm139 Γ (arr139 A B) → Tm139 Γ A → Tm139 Γ B
 := λ t u Tm139 var139 lam139 app139 =>
     app139 _ _ _
         (t Tm139 var139 lam139 app139)
         (u Tm139 var139 lam139 app139)

def v0139 {Γ A} : Tm139 (snoc139 Γ A) A
 := var139 vz139

def v1139 {Γ A B} : Tm139 (snoc139 (snoc139 Γ A) B) A
 := var139 (vs139 vz139)

def v2139 {Γ A B C} : Tm139 (snoc139 (snoc139 (snoc139 Γ A) B) C) A
 := var139 (vs139 (vs139 vz139))

def v3139 {Γ A B C D} : Tm139 (snoc139 (snoc139 (snoc139 (snoc139 Γ A) B) C) D) A
 := var139 (vs139 (vs139 (vs139 vz139)))

def v4139 {Γ A B C D E} : Tm139 (snoc139 (snoc139 (snoc139 (snoc139 (snoc139 Γ A) B) C) D) E) A
 := var139 (vs139 (vs139 (vs139 (vs139 vz139))))

def test139 {Γ A} : Tm139 Γ (arr139 (arr139 A A) (arr139 A A))
 := lam139 (lam139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 (app139 v1139 v0139)))))))


def Ty140 : Type 1
 := ∀ (Ty140 : Type)
      (ι   : Ty140)
      (arr : Ty140 → Ty140 → Ty140)
    , Ty140

def ι140 : Ty140 := λ _ ι140 _ => ι140

def arr140 : Ty140 → Ty140 → Ty140
 := λ A B Ty140 ι140 arr140 =>
     arr140 (A Ty140 ι140 arr140) (B Ty140 ι140 arr140)

def Con140 : Type 1
 := ∀ (Con140  : Type)
      (nil  : Con140)
      (snoc : Con140 → Ty140 → Con140)
    , Con140

def nil140 : Con140
 := λ Con140 nil140 snoc => nil140

def snoc140 : Con140 → Ty140 → Con140
 := λ Γ A Con140 nil140 snoc140 => snoc140 (Γ Con140 nil140 snoc140) A

def Var140 : Con140 → Ty140 → Type 1
 := λ Γ A =>
   ∀ (Var140 : Con140 → Ty140 → Type)
     (vz  : ∀ Γ A, Var140 (snoc140 Γ A) A)
     (vs  : ∀ Γ B A, Var140 Γ A → Var140 (snoc140 Γ B) A)
   , Var140 Γ A

def vz140 {Γ A} : Var140 (snoc140 Γ A) A
 := λ Var140 vz140 vs => vz140 _ _

def vs140 {Γ B A} : Var140 Γ A → Var140 (snoc140 Γ B) A
 := λ x Var140 vz140 vs140 => vs140 _ _ _ (x Var140 vz140 vs140)

def Tm140 : Con140 → Ty140 → Type 1
 := λ Γ A =>
   ∀ (Tm140  : Con140 → Ty140 → Type)
     (var   : ∀ Γ A     , Var140 Γ A → Tm140 Γ A)
     (lam   : ∀ Γ A B   , Tm140 (snoc140 Γ A) B → Tm140 Γ (arr140 A B))
     (app   : ∀ Γ A B   , Tm140 Γ (arr140 A B) → Tm140 Γ A → Tm140 Γ B)
   , Tm140 Γ A

def var140 {Γ A} : Var140 Γ A → Tm140 Γ A
 := λ x Tm140 var140 lam app =>
     var140 _ _ x

def lam140 {Γ A B} : Tm140 (snoc140 Γ A) B → Tm140 Γ (arr140 A B)
 := λ t Tm140 var140 lam140 app =>
     lam140 _ _ _ (t Tm140 var140 lam140 app)

def app140 {Γ A B} : Tm140 Γ (arr140 A B) → Tm140 Γ A → Tm140 Γ B
 := λ t u Tm140 var140 lam140 app140 =>
     app140 _ _ _
         (t Tm140 var140 lam140 app140)
         (u Tm140 var140 lam140 app140)

def v0140 {Γ A} : Tm140 (snoc140 Γ A) A
 := var140 vz140

def v1140 {Γ A B} : Tm140 (snoc140 (snoc140 Γ A) B) A
 := var140 (vs140 vz140)

def v2140 {Γ A B C} : Tm140 (snoc140 (snoc140 (snoc140 Γ A) B) C) A
 := var140 (vs140 (vs140 vz140))

def v3140 {Γ A B C D} : Tm140 (snoc140 (snoc140 (snoc140 (snoc140 Γ A) B) C) D) A
 := var140 (vs140 (vs140 (vs140 vz140)))

def v4140 {Γ A B C D E} : Tm140 (snoc140 (snoc140 (snoc140 (snoc140 (snoc140 Γ A) B) C) D) E) A
 := var140 (vs140 (vs140 (vs140 (vs140 vz140))))

def test140 {Γ A} : Tm140 Γ (arr140 (arr140 A A) (arr140 A A))
 := lam140 (lam140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 (app140 v1140 v0140)))))))


def Ty141 : Type 1
 := ∀ (Ty141 : Type)
      (ι   : Ty141)
      (arr : Ty141 → Ty141 → Ty141)
    , Ty141

def ι141 : Ty141 := λ _ ι141 _ => ι141

def arr141 : Ty141 → Ty141 → Ty141
 := λ A B Ty141 ι141 arr141 =>
     arr141 (A Ty141 ι141 arr141) (B Ty141 ι141 arr141)

def Con141 : Type 1
 := ∀ (Con141  : Type)
      (nil  : Con141)
      (snoc : Con141 → Ty141 → Con141)
    , Con141

def nil141 : Con141
 := λ Con141 nil141 snoc => nil141

def snoc141 : Con141 → Ty141 → Con141
 := λ Γ A Con141 nil141 snoc141 => snoc141 (Γ Con141 nil141 snoc141) A

def Var141 : Con141 → Ty141 → Type 1
 := λ Γ A =>
   ∀ (Var141 : Con141 → Ty141 → Type)
     (vz  : ∀ Γ A, Var141 (snoc141 Γ A) A)
     (vs  : ∀ Γ B A, Var141 Γ A → Var141 (snoc141 Γ B) A)
   , Var141 Γ A

def vz141 {Γ A} : Var141 (snoc141 Γ A) A
 := λ Var141 vz141 vs => vz141 _ _

def vs141 {Γ B A} : Var141 Γ A → Var141 (snoc141 Γ B) A
 := λ x Var141 vz141 vs141 => vs141 _ _ _ (x Var141 vz141 vs141)

def Tm141 : Con141 → Ty141 → Type 1
 := λ Γ A =>
   ∀ (Tm141  : Con141 → Ty141 → Type)
     (var   : ∀ Γ A     , Var141 Γ A → Tm141 Γ A)
     (lam   : ∀ Γ A B   , Tm141 (snoc141 Γ A) B → Tm141 Γ (arr141 A B))
     (app   : ∀ Γ A B   , Tm141 Γ (arr141 A B) → Tm141 Γ A → Tm141 Γ B)
   , Tm141 Γ A

def var141 {Γ A} : Var141 Γ A → Tm141 Γ A
 := λ x Tm141 var141 lam app =>
     var141 _ _ x

def lam141 {Γ A B} : Tm141 (snoc141 Γ A) B → Tm141 Γ (arr141 A B)
 := λ t Tm141 var141 lam141 app =>
     lam141 _ _ _ (t Tm141 var141 lam141 app)

def app141 {Γ A B} : Tm141 Γ (arr141 A B) → Tm141 Γ A → Tm141 Γ B
 := λ t u Tm141 var141 lam141 app141 =>
     app141 _ _ _
         (t Tm141 var141 lam141 app141)
         (u Tm141 var141 lam141 app141)

def v0141 {Γ A} : Tm141 (snoc141 Γ A) A
 := var141 vz141

def v1141 {Γ A B} : Tm141 (snoc141 (snoc141 Γ A) B) A
 := var141 (vs141 vz141)

def v2141 {Γ A B C} : Tm141 (snoc141 (snoc141 (snoc141 Γ A) B) C) A
 := var141 (vs141 (vs141 vz141))

def v3141 {Γ A B C D} : Tm141 (snoc141 (snoc141 (snoc141 (snoc141 Γ A) B) C) D) A
 := var141 (vs141 (vs141 (vs141 vz141)))

def v4141 {Γ A B C D E} : Tm141 (snoc141 (snoc141 (snoc141 (snoc141 (snoc141 Γ A) B) C) D) E) A
 := var141 (vs141 (vs141 (vs141 (vs141 vz141))))

def test141 {Γ A} : Tm141 Γ (arr141 (arr141 A A) (arr141 A A))
 := lam141 (lam141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 (app141 v1141 v0141)))))))


def Ty142 : Type 1
 := ∀ (Ty142 : Type)
      (ι   : Ty142)
      (arr : Ty142 → Ty142 → Ty142)
    , Ty142

def ι142 : Ty142 := λ _ ι142 _ => ι142

def arr142 : Ty142 → Ty142 → Ty142
 := λ A B Ty142 ι142 arr142 =>
     arr142 (A Ty142 ι142 arr142) (B Ty142 ι142 arr142)

def Con142 : Type 1
 := ∀ (Con142  : Type)
      (nil  : Con142)
      (snoc : Con142 → Ty142 → Con142)
    , Con142

def nil142 : Con142
 := λ Con142 nil142 snoc => nil142

def snoc142 : Con142 → Ty142 → Con142
 := λ Γ A Con142 nil142 snoc142 => snoc142 (Γ Con142 nil142 snoc142) A

def Var142 : Con142 → Ty142 → Type 1
 := λ Γ A =>
   ∀ (Var142 : Con142 → Ty142 → Type)
     (vz  : ∀ Γ A, Var142 (snoc142 Γ A) A)
     (vs  : ∀ Γ B A, Var142 Γ A → Var142 (snoc142 Γ B) A)
   , Var142 Γ A

def vz142 {Γ A} : Var142 (snoc142 Γ A) A
 := λ Var142 vz142 vs => vz142 _ _

def vs142 {Γ B A} : Var142 Γ A → Var142 (snoc142 Γ B) A
 := λ x Var142 vz142 vs142 => vs142 _ _ _ (x Var142 vz142 vs142)

def Tm142 : Con142 → Ty142 → Type 1
 := λ Γ A =>
   ∀ (Tm142  : Con142 → Ty142 → Type)
     (var   : ∀ Γ A     , Var142 Γ A → Tm142 Γ A)
     (lam   : ∀ Γ A B   , Tm142 (snoc142 Γ A) B → Tm142 Γ (arr142 A B))
     (app   : ∀ Γ A B   , Tm142 Γ (arr142 A B) → Tm142 Γ A → Tm142 Γ B)
   , Tm142 Γ A

def var142 {Γ A} : Var142 Γ A → Tm142 Γ A
 := λ x Tm142 var142 lam app =>
     var142 _ _ x

def lam142 {Γ A B} : Tm142 (snoc142 Γ A) B → Tm142 Γ (arr142 A B)
 := λ t Tm142 var142 lam142 app =>
     lam142 _ _ _ (t Tm142 var142 lam142 app)

def app142 {Γ A B} : Tm142 Γ (arr142 A B) → Tm142 Γ A → Tm142 Γ B
 := λ t u Tm142 var142 lam142 app142 =>
     app142 _ _ _
         (t Tm142 var142 lam142 app142)
         (u Tm142 var142 lam142 app142)

def v0142 {Γ A} : Tm142 (snoc142 Γ A) A
 := var142 vz142

def v1142 {Γ A B} : Tm142 (snoc142 (snoc142 Γ A) B) A
 := var142 (vs142 vz142)

def v2142 {Γ A B C} : Tm142 (snoc142 (snoc142 (snoc142 Γ A) B) C) A
 := var142 (vs142 (vs142 vz142))

def v3142 {Γ A B C D} : Tm142 (snoc142 (snoc142 (snoc142 (snoc142 Γ A) B) C) D) A
 := var142 (vs142 (vs142 (vs142 vz142)))

def v4142 {Γ A B C D E} : Tm142 (snoc142 (snoc142 (snoc142 (snoc142 (snoc142 Γ A) B) C) D) E) A
 := var142 (vs142 (vs142 (vs142 (vs142 vz142))))

def test142 {Γ A} : Tm142 Γ (arr142 (arr142 A A) (arr142 A A))
 := lam142 (lam142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 (app142 v1142 v0142)))))))


def Ty143 : Type 1
 := ∀ (Ty143 : Type)
      (ι   : Ty143)
      (arr : Ty143 → Ty143 → Ty143)
    , Ty143

def ι143 : Ty143 := λ _ ι143 _ => ι143

def arr143 : Ty143 → Ty143 → Ty143
 := λ A B Ty143 ι143 arr143 =>
     arr143 (A Ty143 ι143 arr143) (B Ty143 ι143 arr143)

def Con143 : Type 1
 := ∀ (Con143  : Type)
      (nil  : Con143)
      (snoc : Con143 → Ty143 → Con143)
    , Con143

def nil143 : Con143
 := λ Con143 nil143 snoc => nil143

def snoc143 : Con143 → Ty143 → Con143
 := λ Γ A Con143 nil143 snoc143 => snoc143 (Γ Con143 nil143 snoc143) A

def Var143 : Con143 → Ty143 → Type 1
 := λ Γ A =>
   ∀ (Var143 : Con143 → Ty143 → Type)
     (vz  : ∀ Γ A, Var143 (snoc143 Γ A) A)
     (vs  : ∀ Γ B A, Var143 Γ A → Var143 (snoc143 Γ B) A)
   , Var143 Γ A

def vz143 {Γ A} : Var143 (snoc143 Γ A) A
 := λ Var143 vz143 vs => vz143 _ _

def vs143 {Γ B A} : Var143 Γ A → Var143 (snoc143 Γ B) A
 := λ x Var143 vz143 vs143 => vs143 _ _ _ (x Var143 vz143 vs143)

def Tm143 : Con143 → Ty143 → Type 1
 := λ Γ A =>
   ∀ (Tm143  : Con143 → Ty143 → Type)
     (var   : ∀ Γ A     , Var143 Γ A → Tm143 Γ A)
     (lam   : ∀ Γ A B   , Tm143 (snoc143 Γ A) B → Tm143 Γ (arr143 A B))
     (app   : ∀ Γ A B   , Tm143 Γ (arr143 A B) → Tm143 Γ A → Tm143 Γ B)
   , Tm143 Γ A

def var143 {Γ A} : Var143 Γ A → Tm143 Γ A
 := λ x Tm143 var143 lam app =>
     var143 _ _ x

def lam143 {Γ A B} : Tm143 (snoc143 Γ A) B → Tm143 Γ (arr143 A B)
 := λ t Tm143 var143 lam143 app =>
     lam143 _ _ _ (t Tm143 var143 lam143 app)

def app143 {Γ A B} : Tm143 Γ (arr143 A B) → Tm143 Γ A → Tm143 Γ B
 := λ t u Tm143 var143 lam143 app143 =>
     app143 _ _ _
         (t Tm143 var143 lam143 app143)
         (u Tm143 var143 lam143 app143)

def v0143 {Γ A} : Tm143 (snoc143 Γ A) A
 := var143 vz143

def v1143 {Γ A B} : Tm143 (snoc143 (snoc143 Γ A) B) A
 := var143 (vs143 vz143)

def v2143 {Γ A B C} : Tm143 (snoc143 (snoc143 (snoc143 Γ A) B) C) A
 := var143 (vs143 (vs143 vz143))

def v3143 {Γ A B C D} : Tm143 (snoc143 (snoc143 (snoc143 (snoc143 Γ A) B) C) D) A
 := var143 (vs143 (vs143 (vs143 vz143)))

def v4143 {Γ A B C D E} : Tm143 (snoc143 (snoc143 (snoc143 (snoc143 (snoc143 Γ A) B) C) D) E) A
 := var143 (vs143 (vs143 (vs143 (vs143 vz143))))

def test143 {Γ A} : Tm143 Γ (arr143 (arr143 A A) (arr143 A A))
 := lam143 (lam143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 (app143 v1143 v0143)))))))


def Ty144 : Type 1
 := ∀ (Ty144 : Type)
      (ι   : Ty144)
      (arr : Ty144 → Ty144 → Ty144)
    , Ty144

def ι144 : Ty144 := λ _ ι144 _ => ι144

def arr144 : Ty144 → Ty144 → Ty144
 := λ A B Ty144 ι144 arr144 =>
     arr144 (A Ty144 ι144 arr144) (B Ty144 ι144 arr144)

def Con144 : Type 1
 := ∀ (Con144  : Type)
      (nil  : Con144)
      (snoc : Con144 → Ty144 → Con144)
    , Con144

def nil144 : Con144
 := λ Con144 nil144 snoc => nil144

def snoc144 : Con144 → Ty144 → Con144
 := λ Γ A Con144 nil144 snoc144 => snoc144 (Γ Con144 nil144 snoc144) A

def Var144 : Con144 → Ty144 → Type 1
 := λ Γ A =>
   ∀ (Var144 : Con144 → Ty144 → Type)
     (vz  : ∀ Γ A, Var144 (snoc144 Γ A) A)
     (vs  : ∀ Γ B A, Var144 Γ A → Var144 (snoc144 Γ B) A)
   , Var144 Γ A

def vz144 {Γ A} : Var144 (snoc144 Γ A) A
 := λ Var144 vz144 vs => vz144 _ _

def vs144 {Γ B A} : Var144 Γ A → Var144 (snoc144 Γ B) A
 := λ x Var144 vz144 vs144 => vs144 _ _ _ (x Var144 vz144 vs144)

def Tm144 : Con144 → Ty144 → Type 1
 := λ Γ A =>
   ∀ (Tm144  : Con144 → Ty144 → Type)
     (var   : ∀ Γ A     , Var144 Γ A → Tm144 Γ A)
     (lam   : ∀ Γ A B   , Tm144 (snoc144 Γ A) B → Tm144 Γ (arr144 A B))
     (app   : ∀ Γ A B   , Tm144 Γ (arr144 A B) → Tm144 Γ A → Tm144 Γ B)
   , Tm144 Γ A

def var144 {Γ A} : Var144 Γ A → Tm144 Γ A
 := λ x Tm144 var144 lam app =>
     var144 _ _ x

def lam144 {Γ A B} : Tm144 (snoc144 Γ A) B → Tm144 Γ (arr144 A B)
 := λ t Tm144 var144 lam144 app =>
     lam144 _ _ _ (t Tm144 var144 lam144 app)

def app144 {Γ A B} : Tm144 Γ (arr144 A B) → Tm144 Γ A → Tm144 Γ B
 := λ t u Tm144 var144 lam144 app144 =>
     app144 _ _ _
         (t Tm144 var144 lam144 app144)
         (u Tm144 var144 lam144 app144)

def v0144 {Γ A} : Tm144 (snoc144 Γ A) A
 := var144 vz144

def v1144 {Γ A B} : Tm144 (snoc144 (snoc144 Γ A) B) A
 := var144 (vs144 vz144)

def v2144 {Γ A B C} : Tm144 (snoc144 (snoc144 (snoc144 Γ A) B) C) A
 := var144 (vs144 (vs144 vz144))

def v3144 {Γ A B C D} : Tm144 (snoc144 (snoc144 (snoc144 (snoc144 Γ A) B) C) D) A
 := var144 (vs144 (vs144 (vs144 vz144)))

def v4144 {Γ A B C D E} : Tm144 (snoc144 (snoc144 (snoc144 (snoc144 (snoc144 Γ A) B) C) D) E) A
 := var144 (vs144 (vs144 (vs144 (vs144 vz144))))

def test144 {Γ A} : Tm144 Γ (arr144 (arr144 A A) (arr144 A A))
 := lam144 (lam144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 (app144 v1144 v0144)))))))


def Ty145 : Type 1
 := ∀ (Ty145 : Type)
      (ι   : Ty145)
      (arr : Ty145 → Ty145 → Ty145)
    , Ty145

def ι145 : Ty145 := λ _ ι145 _ => ι145

def arr145 : Ty145 → Ty145 → Ty145
 := λ A B Ty145 ι145 arr145 =>
     arr145 (A Ty145 ι145 arr145) (B Ty145 ι145 arr145)

def Con145 : Type 1
 := ∀ (Con145  : Type)
      (nil  : Con145)
      (snoc : Con145 → Ty145 → Con145)
    , Con145

def nil145 : Con145
 := λ Con145 nil145 snoc => nil145

def snoc145 : Con145 → Ty145 → Con145
 := λ Γ A Con145 nil145 snoc145 => snoc145 (Γ Con145 nil145 snoc145) A

def Var145 : Con145 → Ty145 → Type 1
 := λ Γ A =>
   ∀ (Var145 : Con145 → Ty145 → Type)
     (vz  : ∀ Γ A, Var145 (snoc145 Γ A) A)
     (vs  : ∀ Γ B A, Var145 Γ A → Var145 (snoc145 Γ B) A)
   , Var145 Γ A

def vz145 {Γ A} : Var145 (snoc145 Γ A) A
 := λ Var145 vz145 vs => vz145 _ _

def vs145 {Γ B A} : Var145 Γ A → Var145 (snoc145 Γ B) A
 := λ x Var145 vz145 vs145 => vs145 _ _ _ (x Var145 vz145 vs145)

def Tm145 : Con145 → Ty145 → Type 1
 := λ Γ A =>
   ∀ (Tm145  : Con145 → Ty145 → Type)
     (var   : ∀ Γ A     , Var145 Γ A → Tm145 Γ A)
     (lam   : ∀ Γ A B   , Tm145 (snoc145 Γ A) B → Tm145 Γ (arr145 A B))
     (app   : ∀ Γ A B   , Tm145 Γ (arr145 A B) → Tm145 Γ A → Tm145 Γ B)
   , Tm145 Γ A

def var145 {Γ A} : Var145 Γ A → Tm145 Γ A
 := λ x Tm145 var145 lam app =>
     var145 _ _ x

def lam145 {Γ A B} : Tm145 (snoc145 Γ A) B → Tm145 Γ (arr145 A B)
 := λ t Tm145 var145 lam145 app =>
     lam145 _ _ _ (t Tm145 var145 lam145 app)

def app145 {Γ A B} : Tm145 Γ (arr145 A B) → Tm145 Γ A → Tm145 Γ B
 := λ t u Tm145 var145 lam145 app145 =>
     app145 _ _ _
         (t Tm145 var145 lam145 app145)
         (u Tm145 var145 lam145 app145)

def v0145 {Γ A} : Tm145 (snoc145 Γ A) A
 := var145 vz145

def v1145 {Γ A B} : Tm145 (snoc145 (snoc145 Γ A) B) A
 := var145 (vs145 vz145)

def v2145 {Γ A B C} : Tm145 (snoc145 (snoc145 (snoc145 Γ A) B) C) A
 := var145 (vs145 (vs145 vz145))

def v3145 {Γ A B C D} : Tm145 (snoc145 (snoc145 (snoc145 (snoc145 Γ A) B) C) D) A
 := var145 (vs145 (vs145 (vs145 vz145)))

def v4145 {Γ A B C D E} : Tm145 (snoc145 (snoc145 (snoc145 (snoc145 (snoc145 Γ A) B) C) D) E) A
 := var145 (vs145 (vs145 (vs145 (vs145 vz145))))

def test145 {Γ A} : Tm145 Γ (arr145 (arr145 A A) (arr145 A A))
 := lam145 (lam145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 (app145 v1145 v0145)))))))


def Ty146 : Type 1
 := ∀ (Ty146 : Type)
      (ι   : Ty146)
      (arr : Ty146 → Ty146 → Ty146)
    , Ty146

def ι146 : Ty146 := λ _ ι146 _ => ι146

def arr146 : Ty146 → Ty146 → Ty146
 := λ A B Ty146 ι146 arr146 =>
     arr146 (A Ty146 ι146 arr146) (B Ty146 ι146 arr146)

def Con146 : Type 1
 := ∀ (Con146  : Type)
      (nil  : Con146)
      (snoc : Con146 → Ty146 → Con146)
    , Con146

def nil146 : Con146
 := λ Con146 nil146 snoc => nil146

def snoc146 : Con146 → Ty146 → Con146
 := λ Γ A Con146 nil146 snoc146 => snoc146 (Γ Con146 nil146 snoc146) A

def Var146 : Con146 → Ty146 → Type 1
 := λ Γ A =>
   ∀ (Var146 : Con146 → Ty146 → Type)
     (vz  : ∀ Γ A, Var146 (snoc146 Γ A) A)
     (vs  : ∀ Γ B A, Var146 Γ A → Var146 (snoc146 Γ B) A)
   , Var146 Γ A

def vz146 {Γ A} : Var146 (snoc146 Γ A) A
 := λ Var146 vz146 vs => vz146 _ _

def vs146 {Γ B A} : Var146 Γ A → Var146 (snoc146 Γ B) A
 := λ x Var146 vz146 vs146 => vs146 _ _ _ (x Var146 vz146 vs146)

def Tm146 : Con146 → Ty146 → Type 1
 := λ Γ A =>
   ∀ (Tm146  : Con146 → Ty146 → Type)
     (var   : ∀ Γ A     , Var146 Γ A → Tm146 Γ A)
     (lam   : ∀ Γ A B   , Tm146 (snoc146 Γ A) B → Tm146 Γ (arr146 A B))
     (app   : ∀ Γ A B   , Tm146 Γ (arr146 A B) → Tm146 Γ A → Tm146 Γ B)
   , Tm146 Γ A

def var146 {Γ A} : Var146 Γ A → Tm146 Γ A
 := λ x Tm146 var146 lam app =>
     var146 _ _ x

def lam146 {Γ A B} : Tm146 (snoc146 Γ A) B → Tm146 Γ (arr146 A B)
 := λ t Tm146 var146 lam146 app =>
     lam146 _ _ _ (t Tm146 var146 lam146 app)

def app146 {Γ A B} : Tm146 Γ (arr146 A B) → Tm146 Γ A → Tm146 Γ B
 := λ t u Tm146 var146 lam146 app146 =>
     app146 _ _ _
         (t Tm146 var146 lam146 app146)
         (u Tm146 var146 lam146 app146)

def v0146 {Γ A} : Tm146 (snoc146 Γ A) A
 := var146 vz146

def v1146 {Γ A B} : Tm146 (snoc146 (snoc146 Γ A) B) A
 := var146 (vs146 vz146)

def v2146 {Γ A B C} : Tm146 (snoc146 (snoc146 (snoc146 Γ A) B) C) A
 := var146 (vs146 (vs146 vz146))

def v3146 {Γ A B C D} : Tm146 (snoc146 (snoc146 (snoc146 (snoc146 Γ A) B) C) D) A
 := var146 (vs146 (vs146 (vs146 vz146)))

def v4146 {Γ A B C D E} : Tm146 (snoc146 (snoc146 (snoc146 (snoc146 (snoc146 Γ A) B) C) D) E) A
 := var146 (vs146 (vs146 (vs146 (vs146 vz146))))

def test146 {Γ A} : Tm146 Γ (arr146 (arr146 A A) (arr146 A A))
 := lam146 (lam146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 (app146 v1146 v0146)))))))


def Ty147 : Type 1
 := ∀ (Ty147 : Type)
      (ι   : Ty147)
      (arr : Ty147 → Ty147 → Ty147)
    , Ty147

def ι147 : Ty147 := λ _ ι147 _ => ι147

def arr147 : Ty147 → Ty147 → Ty147
 := λ A B Ty147 ι147 arr147 =>
     arr147 (A Ty147 ι147 arr147) (B Ty147 ι147 arr147)

def Con147 : Type 1
 := ∀ (Con147  : Type)
      (nil  : Con147)
      (snoc : Con147 → Ty147 → Con147)
    , Con147

def nil147 : Con147
 := λ Con147 nil147 snoc => nil147

def snoc147 : Con147 → Ty147 → Con147
 := λ Γ A Con147 nil147 snoc147 => snoc147 (Γ Con147 nil147 snoc147) A

def Var147 : Con147 → Ty147 → Type 1
 := λ Γ A =>
   ∀ (Var147 : Con147 → Ty147 → Type)
     (vz  : ∀ Γ A, Var147 (snoc147 Γ A) A)
     (vs  : ∀ Γ B A, Var147 Γ A → Var147 (snoc147 Γ B) A)
   , Var147 Γ A

def vz147 {Γ A} : Var147 (snoc147 Γ A) A
 := λ Var147 vz147 vs => vz147 _ _

def vs147 {Γ B A} : Var147 Γ A → Var147 (snoc147 Γ B) A
 := λ x Var147 vz147 vs147 => vs147 _ _ _ (x Var147 vz147 vs147)

def Tm147 : Con147 → Ty147 → Type 1
 := λ Γ A =>
   ∀ (Tm147  : Con147 → Ty147 → Type)
     (var   : ∀ Γ A     , Var147 Γ A → Tm147 Γ A)
     (lam   : ∀ Γ A B   , Tm147 (snoc147 Γ A) B → Tm147 Γ (arr147 A B))
     (app   : ∀ Γ A B   , Tm147 Γ (arr147 A B) → Tm147 Γ A → Tm147 Γ B)
   , Tm147 Γ A

def var147 {Γ A} : Var147 Γ A → Tm147 Γ A
 := λ x Tm147 var147 lam app =>
     var147 _ _ x

def lam147 {Γ A B} : Tm147 (snoc147 Γ A) B → Tm147 Γ (arr147 A B)
 := λ t Tm147 var147 lam147 app =>
     lam147 _ _ _ (t Tm147 var147 lam147 app)

def app147 {Γ A B} : Tm147 Γ (arr147 A B) → Tm147 Γ A → Tm147 Γ B
 := λ t u Tm147 var147 lam147 app147 =>
     app147 _ _ _
         (t Tm147 var147 lam147 app147)
         (u Tm147 var147 lam147 app147)

def v0147 {Γ A} : Tm147 (snoc147 Γ A) A
 := var147 vz147

def v1147 {Γ A B} : Tm147 (snoc147 (snoc147 Γ A) B) A
 := var147 (vs147 vz147)

def v2147 {Γ A B C} : Tm147 (snoc147 (snoc147 (snoc147 Γ A) B) C) A
 := var147 (vs147 (vs147 vz147))

def v3147 {Γ A B C D} : Tm147 (snoc147 (snoc147 (snoc147 (snoc147 Γ A) B) C) D) A
 := var147 (vs147 (vs147 (vs147 vz147)))

def v4147 {Γ A B C D E} : Tm147 (snoc147 (snoc147 (snoc147 (snoc147 (snoc147 Γ A) B) C) D) E) A
 := var147 (vs147 (vs147 (vs147 (vs147 vz147))))

def test147 {Γ A} : Tm147 Γ (arr147 (arr147 A A) (arr147 A A))
 := lam147 (lam147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 (app147 v1147 v0147)))))))


def Ty148 : Type 1
 := ∀ (Ty148 : Type)
      (ι   : Ty148)
      (arr : Ty148 → Ty148 → Ty148)
    , Ty148

def ι148 : Ty148 := λ _ ι148 _ => ι148

def arr148 : Ty148 → Ty148 → Ty148
 := λ A B Ty148 ι148 arr148 =>
     arr148 (A Ty148 ι148 arr148) (B Ty148 ι148 arr148)

def Con148 : Type 1
 := ∀ (Con148  : Type)
      (nil  : Con148)
      (snoc : Con148 → Ty148 → Con148)
    , Con148

def nil148 : Con148
 := λ Con148 nil148 snoc => nil148

def snoc148 : Con148 → Ty148 → Con148
 := λ Γ A Con148 nil148 snoc148 => snoc148 (Γ Con148 nil148 snoc148) A

def Var148 : Con148 → Ty148 → Type 1
 := λ Γ A =>
   ∀ (Var148 : Con148 → Ty148 → Type)
     (vz  : ∀ Γ A, Var148 (snoc148 Γ A) A)
     (vs  : ∀ Γ B A, Var148 Γ A → Var148 (snoc148 Γ B) A)
   , Var148 Γ A

def vz148 {Γ A} : Var148 (snoc148 Γ A) A
 := λ Var148 vz148 vs => vz148 _ _

def vs148 {Γ B A} : Var148 Γ A → Var148 (snoc148 Γ B) A
 := λ x Var148 vz148 vs148 => vs148 _ _ _ (x Var148 vz148 vs148)

def Tm148 : Con148 → Ty148 → Type 1
 := λ Γ A =>
   ∀ (Tm148  : Con148 → Ty148 → Type)
     (var   : ∀ Γ A     , Var148 Γ A → Tm148 Γ A)
     (lam   : ∀ Γ A B   , Tm148 (snoc148 Γ A) B → Tm148 Γ (arr148 A B))
     (app   : ∀ Γ A B   , Tm148 Γ (arr148 A B) → Tm148 Γ A → Tm148 Γ B)
   , Tm148 Γ A

def var148 {Γ A} : Var148 Γ A → Tm148 Γ A
 := λ x Tm148 var148 lam app =>
     var148 _ _ x

def lam148 {Γ A B} : Tm148 (snoc148 Γ A) B → Tm148 Γ (arr148 A B)
 := λ t Tm148 var148 lam148 app =>
     lam148 _ _ _ (t Tm148 var148 lam148 app)

def app148 {Γ A B} : Tm148 Γ (arr148 A B) → Tm148 Γ A → Tm148 Γ B
 := λ t u Tm148 var148 lam148 app148 =>
     app148 _ _ _
         (t Tm148 var148 lam148 app148)
         (u Tm148 var148 lam148 app148)

def v0148 {Γ A} : Tm148 (snoc148 Γ A) A
 := var148 vz148

def v1148 {Γ A B} : Tm148 (snoc148 (snoc148 Γ A) B) A
 := var148 (vs148 vz148)

def v2148 {Γ A B C} : Tm148 (snoc148 (snoc148 (snoc148 Γ A) B) C) A
 := var148 (vs148 (vs148 vz148))

def v3148 {Γ A B C D} : Tm148 (snoc148 (snoc148 (snoc148 (snoc148 Γ A) B) C) D) A
 := var148 (vs148 (vs148 (vs148 vz148)))

def v4148 {Γ A B C D E} : Tm148 (snoc148 (snoc148 (snoc148 (snoc148 (snoc148 Γ A) B) C) D) E) A
 := var148 (vs148 (vs148 (vs148 (vs148 vz148))))

def test148 {Γ A} : Tm148 Γ (arr148 (arr148 A A) (arr148 A A))
 := lam148 (lam148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 (app148 v1148 v0148)))))))


def Ty149 : Type 1
 := ∀ (Ty149 : Type)
      (ι   : Ty149)
      (arr : Ty149 → Ty149 → Ty149)
    , Ty149

def ι149 : Ty149 := λ _ ι149 _ => ι149

def arr149 : Ty149 → Ty149 → Ty149
 := λ A B Ty149 ι149 arr149 =>
     arr149 (A Ty149 ι149 arr149) (B Ty149 ι149 arr149)

def Con149 : Type 1
 := ∀ (Con149  : Type)
      (nil  : Con149)
      (snoc : Con149 → Ty149 → Con149)
    , Con149

def nil149 : Con149
 := λ Con149 nil149 snoc => nil149

def snoc149 : Con149 → Ty149 → Con149
 := λ Γ A Con149 nil149 snoc149 => snoc149 (Γ Con149 nil149 snoc149) A

def Var149 : Con149 → Ty149 → Type 1
 := λ Γ A =>
   ∀ (Var149 : Con149 → Ty149 → Type)
     (vz  : ∀ Γ A, Var149 (snoc149 Γ A) A)
     (vs  : ∀ Γ B A, Var149 Γ A → Var149 (snoc149 Γ B) A)
   , Var149 Γ A

def vz149 {Γ A} : Var149 (snoc149 Γ A) A
 := λ Var149 vz149 vs => vz149 _ _

def vs149 {Γ B A} : Var149 Γ A → Var149 (snoc149 Γ B) A
 := λ x Var149 vz149 vs149 => vs149 _ _ _ (x Var149 vz149 vs149)

def Tm149 : Con149 → Ty149 → Type 1
 := λ Γ A =>
   ∀ (Tm149  : Con149 → Ty149 → Type)
     (var   : ∀ Γ A     , Var149 Γ A → Tm149 Γ A)
     (lam   : ∀ Γ A B   , Tm149 (snoc149 Γ A) B → Tm149 Γ (arr149 A B))
     (app   : ∀ Γ A B   , Tm149 Γ (arr149 A B) → Tm149 Γ A → Tm149 Γ B)
   , Tm149 Γ A

def var149 {Γ A} : Var149 Γ A → Tm149 Γ A
 := λ x Tm149 var149 lam app =>
     var149 _ _ x

def lam149 {Γ A B} : Tm149 (snoc149 Γ A) B → Tm149 Γ (arr149 A B)
 := λ t Tm149 var149 lam149 app =>
     lam149 _ _ _ (t Tm149 var149 lam149 app)

def app149 {Γ A B} : Tm149 Γ (arr149 A B) → Tm149 Γ A → Tm149 Γ B
 := λ t u Tm149 var149 lam149 app149 =>
     app149 _ _ _
         (t Tm149 var149 lam149 app149)
         (u Tm149 var149 lam149 app149)

def v0149 {Γ A} : Tm149 (snoc149 Γ A) A
 := var149 vz149

def v1149 {Γ A B} : Tm149 (snoc149 (snoc149 Γ A) B) A
 := var149 (vs149 vz149)

def v2149 {Γ A B C} : Tm149 (snoc149 (snoc149 (snoc149 Γ A) B) C) A
 := var149 (vs149 (vs149 vz149))

def v3149 {Γ A B C D} : Tm149 (snoc149 (snoc149 (snoc149 (snoc149 Γ A) B) C) D) A
 := var149 (vs149 (vs149 (vs149 vz149)))

def v4149 {Γ A B C D E} : Tm149 (snoc149 (snoc149 (snoc149 (snoc149 (snoc149 Γ A) B) C) D) E) A
 := var149 (vs149 (vs149 (vs149 (vs149 vz149))))

def test149 {Γ A} : Tm149 Γ (arr149 (arr149 A A) (arr149 A A))
 := lam149 (lam149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 (app149 v1149 v0149)))))))


def Ty150 : Type 1
 := ∀ (Ty150 : Type)
      (ι   : Ty150)
      (arr : Ty150 → Ty150 → Ty150)
    , Ty150

def ι150 : Ty150 := λ _ ι150 _ => ι150

def arr150 : Ty150 → Ty150 → Ty150
 := λ A B Ty150 ι150 arr150 =>
     arr150 (A Ty150 ι150 arr150) (B Ty150 ι150 arr150)

def Con150 : Type 1
 := ∀ (Con150  : Type)
      (nil  : Con150)
      (snoc : Con150 → Ty150 → Con150)
    , Con150

def nil150 : Con150
 := λ Con150 nil150 snoc => nil150

def snoc150 : Con150 → Ty150 → Con150
 := λ Γ A Con150 nil150 snoc150 => snoc150 (Γ Con150 nil150 snoc150) A

def Var150 : Con150 → Ty150 → Type 1
 := λ Γ A =>
   ∀ (Var150 : Con150 → Ty150 → Type)
     (vz  : ∀ Γ A, Var150 (snoc150 Γ A) A)
     (vs  : ∀ Γ B A, Var150 Γ A → Var150 (snoc150 Γ B) A)
   , Var150 Γ A

def vz150 {Γ A} : Var150 (snoc150 Γ A) A
 := λ Var150 vz150 vs => vz150 _ _

def vs150 {Γ B A} : Var150 Γ A → Var150 (snoc150 Γ B) A
 := λ x Var150 vz150 vs150 => vs150 _ _ _ (x Var150 vz150 vs150)

def Tm150 : Con150 → Ty150 → Type 1
 := λ Γ A =>
   ∀ (Tm150  : Con150 → Ty150 → Type)
     (var   : ∀ Γ A     , Var150 Γ A → Tm150 Γ A)
     (lam   : ∀ Γ A B   , Tm150 (snoc150 Γ A) B → Tm150 Γ (arr150 A B))
     (app   : ∀ Γ A B   , Tm150 Γ (arr150 A B) → Tm150 Γ A → Tm150 Γ B)
   , Tm150 Γ A

def var150 {Γ A} : Var150 Γ A → Tm150 Γ A
 := λ x Tm150 var150 lam app =>
     var150 _ _ x

def lam150 {Γ A B} : Tm150 (snoc150 Γ A) B → Tm150 Γ (arr150 A B)
 := λ t Tm150 var150 lam150 app =>
     lam150 _ _ _ (t Tm150 var150 lam150 app)

def app150 {Γ A B} : Tm150 Γ (arr150 A B) → Tm150 Γ A → Tm150 Γ B
 := λ t u Tm150 var150 lam150 app150 =>
     app150 _ _ _
         (t Tm150 var150 lam150 app150)
         (u Tm150 var150 lam150 app150)

def v0150 {Γ A} : Tm150 (snoc150 Γ A) A
 := var150 vz150

def v1150 {Γ A B} : Tm150 (snoc150 (snoc150 Γ A) B) A
 := var150 (vs150 vz150)

def v2150 {Γ A B C} : Tm150 (snoc150 (snoc150 (snoc150 Γ A) B) C) A
 := var150 (vs150 (vs150 vz150))

def v3150 {Γ A B C D} : Tm150 (snoc150 (snoc150 (snoc150 (snoc150 Γ A) B) C) D) A
 := var150 (vs150 (vs150 (vs150 vz150)))

def v4150 {Γ A B C D E} : Tm150 (snoc150 (snoc150 (snoc150 (snoc150 (snoc150 Γ A) B) C) D) E) A
 := var150 (vs150 (vs150 (vs150 (vs150 vz150))))

def test150 {Γ A} : Tm150 Γ (arr150 (arr150 A A) (arr150 A A))
 := lam150 (lam150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 (app150 v1150 v0150)))))))


def Ty151 : Type 1
 := ∀ (Ty151 : Type)
      (ι   : Ty151)
      (arr : Ty151 → Ty151 → Ty151)
    , Ty151

def ι151 : Ty151 := λ _ ι151 _ => ι151

def arr151 : Ty151 → Ty151 → Ty151
 := λ A B Ty151 ι151 arr151 =>
     arr151 (A Ty151 ι151 arr151) (B Ty151 ι151 arr151)

def Con151 : Type 1
 := ∀ (Con151  : Type)
      (nil  : Con151)
      (snoc : Con151 → Ty151 → Con151)
    , Con151

def nil151 : Con151
 := λ Con151 nil151 snoc => nil151

def snoc151 : Con151 → Ty151 → Con151
 := λ Γ A Con151 nil151 snoc151 => snoc151 (Γ Con151 nil151 snoc151) A

def Var151 : Con151 → Ty151 → Type 1
 := λ Γ A =>
   ∀ (Var151 : Con151 → Ty151 → Type)
     (vz  : ∀ Γ A, Var151 (snoc151 Γ A) A)
     (vs  : ∀ Γ B A, Var151 Γ A → Var151 (snoc151 Γ B) A)
   , Var151 Γ A

def vz151 {Γ A} : Var151 (snoc151 Γ A) A
 := λ Var151 vz151 vs => vz151 _ _

def vs151 {Γ B A} : Var151 Γ A → Var151 (snoc151 Γ B) A
 := λ x Var151 vz151 vs151 => vs151 _ _ _ (x Var151 vz151 vs151)

def Tm151 : Con151 → Ty151 → Type 1
 := λ Γ A =>
   ∀ (Tm151  : Con151 → Ty151 → Type)
     (var   : ∀ Γ A     , Var151 Γ A → Tm151 Γ A)
     (lam   : ∀ Γ A B   , Tm151 (snoc151 Γ A) B → Tm151 Γ (arr151 A B))
     (app   : ∀ Γ A B   , Tm151 Γ (arr151 A B) → Tm151 Γ A → Tm151 Γ B)
   , Tm151 Γ A

def var151 {Γ A} : Var151 Γ A → Tm151 Γ A
 := λ x Tm151 var151 lam app =>
     var151 _ _ x

def lam151 {Γ A B} : Tm151 (snoc151 Γ A) B → Tm151 Γ (arr151 A B)
 := λ t Tm151 var151 lam151 app =>
     lam151 _ _ _ (t Tm151 var151 lam151 app)

def app151 {Γ A B} : Tm151 Γ (arr151 A B) → Tm151 Γ A → Tm151 Γ B
 := λ t u Tm151 var151 lam151 app151 =>
     app151 _ _ _
         (t Tm151 var151 lam151 app151)
         (u Tm151 var151 lam151 app151)

def v0151 {Γ A} : Tm151 (snoc151 Γ A) A
 := var151 vz151

def v1151 {Γ A B} : Tm151 (snoc151 (snoc151 Γ A) B) A
 := var151 (vs151 vz151)

def v2151 {Γ A B C} : Tm151 (snoc151 (snoc151 (snoc151 Γ A) B) C) A
 := var151 (vs151 (vs151 vz151))

def v3151 {Γ A B C D} : Tm151 (snoc151 (snoc151 (snoc151 (snoc151 Γ A) B) C) D) A
 := var151 (vs151 (vs151 (vs151 vz151)))

def v4151 {Γ A B C D E} : Tm151 (snoc151 (snoc151 (snoc151 (snoc151 (snoc151 Γ A) B) C) D) E) A
 := var151 (vs151 (vs151 (vs151 (vs151 vz151))))

def test151 {Γ A} : Tm151 Γ (arr151 (arr151 A A) (arr151 A A))
 := lam151 (lam151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 (app151 v1151 v0151)))))))


def Ty152 : Type 1
 := ∀ (Ty152 : Type)
      (ι   : Ty152)
      (arr : Ty152 → Ty152 → Ty152)
    , Ty152

def ι152 : Ty152 := λ _ ι152 _ => ι152

def arr152 : Ty152 → Ty152 → Ty152
 := λ A B Ty152 ι152 arr152 =>
     arr152 (A Ty152 ι152 arr152) (B Ty152 ι152 arr152)

def Con152 : Type 1
 := ∀ (Con152  : Type)
      (nil  : Con152)
      (snoc : Con152 → Ty152 → Con152)
    , Con152

def nil152 : Con152
 := λ Con152 nil152 snoc => nil152

def snoc152 : Con152 → Ty152 → Con152
 := λ Γ A Con152 nil152 snoc152 => snoc152 (Γ Con152 nil152 snoc152) A

def Var152 : Con152 → Ty152 → Type 1
 := λ Γ A =>
   ∀ (Var152 : Con152 → Ty152 → Type)
     (vz  : ∀ Γ A, Var152 (snoc152 Γ A) A)
     (vs  : ∀ Γ B A, Var152 Γ A → Var152 (snoc152 Γ B) A)
   , Var152 Γ A

def vz152 {Γ A} : Var152 (snoc152 Γ A) A
 := λ Var152 vz152 vs => vz152 _ _

def vs152 {Γ B A} : Var152 Γ A → Var152 (snoc152 Γ B) A
 := λ x Var152 vz152 vs152 => vs152 _ _ _ (x Var152 vz152 vs152)

def Tm152 : Con152 → Ty152 → Type 1
 := λ Γ A =>
   ∀ (Tm152  : Con152 → Ty152 → Type)
     (var   : ∀ Γ A     , Var152 Γ A → Tm152 Γ A)
     (lam   : ∀ Γ A B   , Tm152 (snoc152 Γ A) B → Tm152 Γ (arr152 A B))
     (app   : ∀ Γ A B   , Tm152 Γ (arr152 A B) → Tm152 Γ A → Tm152 Γ B)
   , Tm152 Γ A

def var152 {Γ A} : Var152 Γ A → Tm152 Γ A
 := λ x Tm152 var152 lam app =>
     var152 _ _ x

def lam152 {Γ A B} : Tm152 (snoc152 Γ A) B → Tm152 Γ (arr152 A B)
 := λ t Tm152 var152 lam152 app =>
     lam152 _ _ _ (t Tm152 var152 lam152 app)

def app152 {Γ A B} : Tm152 Γ (arr152 A B) → Tm152 Γ A → Tm152 Γ B
 := λ t u Tm152 var152 lam152 app152 =>
     app152 _ _ _
         (t Tm152 var152 lam152 app152)
         (u Tm152 var152 lam152 app152)

def v0152 {Γ A} : Tm152 (snoc152 Γ A) A
 := var152 vz152

def v1152 {Γ A B} : Tm152 (snoc152 (snoc152 Γ A) B) A
 := var152 (vs152 vz152)

def v2152 {Γ A B C} : Tm152 (snoc152 (snoc152 (snoc152 Γ A) B) C) A
 := var152 (vs152 (vs152 vz152))

def v3152 {Γ A B C D} : Tm152 (snoc152 (snoc152 (snoc152 (snoc152 Γ A) B) C) D) A
 := var152 (vs152 (vs152 (vs152 vz152)))

def v4152 {Γ A B C D E} : Tm152 (snoc152 (snoc152 (snoc152 (snoc152 (snoc152 Γ A) B) C) D) E) A
 := var152 (vs152 (vs152 (vs152 (vs152 vz152))))

def test152 {Γ A} : Tm152 Γ (arr152 (arr152 A A) (arr152 A A))
 := lam152 (lam152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 (app152 v1152 v0152)))))))


def Ty153 : Type 1
 := ∀ (Ty153 : Type)
      (ι   : Ty153)
      (arr : Ty153 → Ty153 → Ty153)
    , Ty153

def ι153 : Ty153 := λ _ ι153 _ => ι153

def arr153 : Ty153 → Ty153 → Ty153
 := λ A B Ty153 ι153 arr153 =>
     arr153 (A Ty153 ι153 arr153) (B Ty153 ι153 arr153)

def Con153 : Type 1
 := ∀ (Con153  : Type)
      (nil  : Con153)
      (snoc : Con153 → Ty153 → Con153)
    , Con153

def nil153 : Con153
 := λ Con153 nil153 snoc => nil153

def snoc153 : Con153 → Ty153 → Con153
 := λ Γ A Con153 nil153 snoc153 => snoc153 (Γ Con153 nil153 snoc153) A

def Var153 : Con153 → Ty153 → Type 1
 := λ Γ A =>
   ∀ (Var153 : Con153 → Ty153 → Type)
     (vz  : ∀ Γ A, Var153 (snoc153 Γ A) A)
     (vs  : ∀ Γ B A, Var153 Γ A → Var153 (snoc153 Γ B) A)
   , Var153 Γ A

def vz153 {Γ A} : Var153 (snoc153 Γ A) A
 := λ Var153 vz153 vs => vz153 _ _

def vs153 {Γ B A} : Var153 Γ A → Var153 (snoc153 Γ B) A
 := λ x Var153 vz153 vs153 => vs153 _ _ _ (x Var153 vz153 vs153)

def Tm153 : Con153 → Ty153 → Type 1
 := λ Γ A =>
   ∀ (Tm153  : Con153 → Ty153 → Type)
     (var   : ∀ Γ A     , Var153 Γ A → Tm153 Γ A)
     (lam   : ∀ Γ A B   , Tm153 (snoc153 Γ A) B → Tm153 Γ (arr153 A B))
     (app   : ∀ Γ A B   , Tm153 Γ (arr153 A B) → Tm153 Γ A → Tm153 Γ B)
   , Tm153 Γ A

def var153 {Γ A} : Var153 Γ A → Tm153 Γ A
 := λ x Tm153 var153 lam app =>
     var153 _ _ x

def lam153 {Γ A B} : Tm153 (snoc153 Γ A) B → Tm153 Γ (arr153 A B)
 := λ t Tm153 var153 lam153 app =>
     lam153 _ _ _ (t Tm153 var153 lam153 app)

def app153 {Γ A B} : Tm153 Γ (arr153 A B) → Tm153 Γ A → Tm153 Γ B
 := λ t u Tm153 var153 lam153 app153 =>
     app153 _ _ _
         (t Tm153 var153 lam153 app153)
         (u Tm153 var153 lam153 app153)

def v0153 {Γ A} : Tm153 (snoc153 Γ A) A
 := var153 vz153

def v1153 {Γ A B} : Tm153 (snoc153 (snoc153 Γ A) B) A
 := var153 (vs153 vz153)

def v2153 {Γ A B C} : Tm153 (snoc153 (snoc153 (snoc153 Γ A) B) C) A
 := var153 (vs153 (vs153 vz153))

def v3153 {Γ A B C D} : Tm153 (snoc153 (snoc153 (snoc153 (snoc153 Γ A) B) C) D) A
 := var153 (vs153 (vs153 (vs153 vz153)))

def v4153 {Γ A B C D E} : Tm153 (snoc153 (snoc153 (snoc153 (snoc153 (snoc153 Γ A) B) C) D) E) A
 := var153 (vs153 (vs153 (vs153 (vs153 vz153))))

def test153 {Γ A} : Tm153 Γ (arr153 (arr153 A A) (arr153 A A))
 := lam153 (lam153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 (app153 v1153 v0153)))))))


def Ty154 : Type 1
 := ∀ (Ty154 : Type)
      (ι   : Ty154)
      (arr : Ty154 → Ty154 → Ty154)
    , Ty154

def ι154 : Ty154 := λ _ ι154 _ => ι154

def arr154 : Ty154 → Ty154 → Ty154
 := λ A B Ty154 ι154 arr154 =>
     arr154 (A Ty154 ι154 arr154) (B Ty154 ι154 arr154)

def Con154 : Type 1
 := ∀ (Con154  : Type)
      (nil  : Con154)
      (snoc : Con154 → Ty154 → Con154)
    , Con154

def nil154 : Con154
 := λ Con154 nil154 snoc => nil154

def snoc154 : Con154 → Ty154 → Con154
 := λ Γ A Con154 nil154 snoc154 => snoc154 (Γ Con154 nil154 snoc154) A

def Var154 : Con154 → Ty154 → Type 1
 := λ Γ A =>
   ∀ (Var154 : Con154 → Ty154 → Type)
     (vz  : ∀ Γ A, Var154 (snoc154 Γ A) A)
     (vs  : ∀ Γ B A, Var154 Γ A → Var154 (snoc154 Γ B) A)
   , Var154 Γ A

def vz154 {Γ A} : Var154 (snoc154 Γ A) A
 := λ Var154 vz154 vs => vz154 _ _

def vs154 {Γ B A} : Var154 Γ A → Var154 (snoc154 Γ B) A
 := λ x Var154 vz154 vs154 => vs154 _ _ _ (x Var154 vz154 vs154)

def Tm154 : Con154 → Ty154 → Type 1
 := λ Γ A =>
   ∀ (Tm154  : Con154 → Ty154 → Type)
     (var   : ∀ Γ A     , Var154 Γ A → Tm154 Γ A)
     (lam   : ∀ Γ A B   , Tm154 (snoc154 Γ A) B → Tm154 Γ (arr154 A B))
     (app   : ∀ Γ A B   , Tm154 Γ (arr154 A B) → Tm154 Γ A → Tm154 Γ B)
   , Tm154 Γ A

def var154 {Γ A} : Var154 Γ A → Tm154 Γ A
 := λ x Tm154 var154 lam app =>
     var154 _ _ x

def lam154 {Γ A B} : Tm154 (snoc154 Γ A) B → Tm154 Γ (arr154 A B)
 := λ t Tm154 var154 lam154 app =>
     lam154 _ _ _ (t Tm154 var154 lam154 app)

def app154 {Γ A B} : Tm154 Γ (arr154 A B) → Tm154 Γ A → Tm154 Γ B
 := λ t u Tm154 var154 lam154 app154 =>
     app154 _ _ _
         (t Tm154 var154 lam154 app154)
         (u Tm154 var154 lam154 app154)

def v0154 {Γ A} : Tm154 (snoc154 Γ A) A
 := var154 vz154

def v1154 {Γ A B} : Tm154 (snoc154 (snoc154 Γ A) B) A
 := var154 (vs154 vz154)

def v2154 {Γ A B C} : Tm154 (snoc154 (snoc154 (snoc154 Γ A) B) C) A
 := var154 (vs154 (vs154 vz154))

def v3154 {Γ A B C D} : Tm154 (snoc154 (snoc154 (snoc154 (snoc154 Γ A) B) C) D) A
 := var154 (vs154 (vs154 (vs154 vz154)))

def v4154 {Γ A B C D E} : Tm154 (snoc154 (snoc154 (snoc154 (snoc154 (snoc154 Γ A) B) C) D) E) A
 := var154 (vs154 (vs154 (vs154 (vs154 vz154))))

def test154 {Γ A} : Tm154 Γ (arr154 (arr154 A A) (arr154 A A))
 := lam154 (lam154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 (app154 v1154 v0154)))))))


def Ty155 : Type 1
 := ∀ (Ty155 : Type)
      (ι   : Ty155)
      (arr : Ty155 → Ty155 → Ty155)
    , Ty155

def ι155 : Ty155 := λ _ ι155 _ => ι155

def arr155 : Ty155 → Ty155 → Ty155
 := λ A B Ty155 ι155 arr155 =>
     arr155 (A Ty155 ι155 arr155) (B Ty155 ι155 arr155)

def Con155 : Type 1
 := ∀ (Con155  : Type)
      (nil  : Con155)
      (snoc : Con155 → Ty155 → Con155)
    , Con155

def nil155 : Con155
 := λ Con155 nil155 snoc => nil155

def snoc155 : Con155 → Ty155 → Con155
 := λ Γ A Con155 nil155 snoc155 => snoc155 (Γ Con155 nil155 snoc155) A

def Var155 : Con155 → Ty155 → Type 1
 := λ Γ A =>
   ∀ (Var155 : Con155 → Ty155 → Type)
     (vz  : ∀ Γ A, Var155 (snoc155 Γ A) A)
     (vs  : ∀ Γ B A, Var155 Γ A → Var155 (snoc155 Γ B) A)
   , Var155 Γ A

def vz155 {Γ A} : Var155 (snoc155 Γ A) A
 := λ Var155 vz155 vs => vz155 _ _

def vs155 {Γ B A} : Var155 Γ A → Var155 (snoc155 Γ B) A
 := λ x Var155 vz155 vs155 => vs155 _ _ _ (x Var155 vz155 vs155)

def Tm155 : Con155 → Ty155 → Type 1
 := λ Γ A =>
   ∀ (Tm155  : Con155 → Ty155 → Type)
     (var   : ∀ Γ A     , Var155 Γ A → Tm155 Γ A)
     (lam   : ∀ Γ A B   , Tm155 (snoc155 Γ A) B → Tm155 Γ (arr155 A B))
     (app   : ∀ Γ A B   , Tm155 Γ (arr155 A B) → Tm155 Γ A → Tm155 Γ B)
   , Tm155 Γ A

def var155 {Γ A} : Var155 Γ A → Tm155 Γ A
 := λ x Tm155 var155 lam app =>
     var155 _ _ x

def lam155 {Γ A B} : Tm155 (snoc155 Γ A) B → Tm155 Γ (arr155 A B)
 := λ t Tm155 var155 lam155 app =>
     lam155 _ _ _ (t Tm155 var155 lam155 app)

def app155 {Γ A B} : Tm155 Γ (arr155 A B) → Tm155 Γ A → Tm155 Γ B
 := λ t u Tm155 var155 lam155 app155 =>
     app155 _ _ _
         (t Tm155 var155 lam155 app155)
         (u Tm155 var155 lam155 app155)

def v0155 {Γ A} : Tm155 (snoc155 Γ A) A
 := var155 vz155

def v1155 {Γ A B} : Tm155 (snoc155 (snoc155 Γ A) B) A
 := var155 (vs155 vz155)

def v2155 {Γ A B C} : Tm155 (snoc155 (snoc155 (snoc155 Γ A) B) C) A
 := var155 (vs155 (vs155 vz155))

def v3155 {Γ A B C D} : Tm155 (snoc155 (snoc155 (snoc155 (snoc155 Γ A) B) C) D) A
 := var155 (vs155 (vs155 (vs155 vz155)))

def v4155 {Γ A B C D E} : Tm155 (snoc155 (snoc155 (snoc155 (snoc155 (snoc155 Γ A) B) C) D) E) A
 := var155 (vs155 (vs155 (vs155 (vs155 vz155))))

def test155 {Γ A} : Tm155 Γ (arr155 (arr155 A A) (arr155 A A))
 := lam155 (lam155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 (app155 v1155 v0155)))))))


def Ty156 : Type 1
 := ∀ (Ty156 : Type)
      (ι   : Ty156)
      (arr : Ty156 → Ty156 → Ty156)
    , Ty156

def ι156 : Ty156 := λ _ ι156 _ => ι156

def arr156 : Ty156 → Ty156 → Ty156
 := λ A B Ty156 ι156 arr156 =>
     arr156 (A Ty156 ι156 arr156) (B Ty156 ι156 arr156)

def Con156 : Type 1
 := ∀ (Con156  : Type)
      (nil  : Con156)
      (snoc : Con156 → Ty156 → Con156)
    , Con156

def nil156 : Con156
 := λ Con156 nil156 snoc => nil156

def snoc156 : Con156 → Ty156 → Con156
 := λ Γ A Con156 nil156 snoc156 => snoc156 (Γ Con156 nil156 snoc156) A

def Var156 : Con156 → Ty156 → Type 1
 := λ Γ A =>
   ∀ (Var156 : Con156 → Ty156 → Type)
     (vz  : ∀ Γ A, Var156 (snoc156 Γ A) A)
     (vs  : ∀ Γ B A, Var156 Γ A → Var156 (snoc156 Γ B) A)
   , Var156 Γ A

def vz156 {Γ A} : Var156 (snoc156 Γ A) A
 := λ Var156 vz156 vs => vz156 _ _

def vs156 {Γ B A} : Var156 Γ A → Var156 (snoc156 Γ B) A
 := λ x Var156 vz156 vs156 => vs156 _ _ _ (x Var156 vz156 vs156)

def Tm156 : Con156 → Ty156 → Type 1
 := λ Γ A =>
   ∀ (Tm156  : Con156 → Ty156 → Type)
     (var   : ∀ Γ A     , Var156 Γ A → Tm156 Γ A)
     (lam   : ∀ Γ A B   , Tm156 (snoc156 Γ A) B → Tm156 Γ (arr156 A B))
     (app   : ∀ Γ A B   , Tm156 Γ (arr156 A B) → Tm156 Γ A → Tm156 Γ B)
   , Tm156 Γ A

def var156 {Γ A} : Var156 Γ A → Tm156 Γ A
 := λ x Tm156 var156 lam app =>
     var156 _ _ x

def lam156 {Γ A B} : Tm156 (snoc156 Γ A) B → Tm156 Γ (arr156 A B)
 := λ t Tm156 var156 lam156 app =>
     lam156 _ _ _ (t Tm156 var156 lam156 app)

def app156 {Γ A B} : Tm156 Γ (arr156 A B) → Tm156 Γ A → Tm156 Γ B
 := λ t u Tm156 var156 lam156 app156 =>
     app156 _ _ _
         (t Tm156 var156 lam156 app156)
         (u Tm156 var156 lam156 app156)

def v0156 {Γ A} : Tm156 (snoc156 Γ A) A
 := var156 vz156

def v1156 {Γ A B} : Tm156 (snoc156 (snoc156 Γ A) B) A
 := var156 (vs156 vz156)

def v2156 {Γ A B C} : Tm156 (snoc156 (snoc156 (snoc156 Γ A) B) C) A
 := var156 (vs156 (vs156 vz156))

def v3156 {Γ A B C D} : Tm156 (snoc156 (snoc156 (snoc156 (snoc156 Γ A) B) C) D) A
 := var156 (vs156 (vs156 (vs156 vz156)))

def v4156 {Γ A B C D E} : Tm156 (snoc156 (snoc156 (snoc156 (snoc156 (snoc156 Γ A) B) C) D) E) A
 := var156 (vs156 (vs156 (vs156 (vs156 vz156))))

def test156 {Γ A} : Tm156 Γ (arr156 (arr156 A A) (arr156 A A))
 := lam156 (lam156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 (app156 v1156 v0156)))))))


def Ty157 : Type 1
 := ∀ (Ty157 : Type)
      (ι   : Ty157)
      (arr : Ty157 → Ty157 → Ty157)
    , Ty157

def ι157 : Ty157 := λ _ ι157 _ => ι157

def arr157 : Ty157 → Ty157 → Ty157
 := λ A B Ty157 ι157 arr157 =>
     arr157 (A Ty157 ι157 arr157) (B Ty157 ι157 arr157)

def Con157 : Type 1
 := ∀ (Con157  : Type)
      (nil  : Con157)
      (snoc : Con157 → Ty157 → Con157)
    , Con157

def nil157 : Con157
 := λ Con157 nil157 snoc => nil157

def snoc157 : Con157 → Ty157 → Con157
 := λ Γ A Con157 nil157 snoc157 => snoc157 (Γ Con157 nil157 snoc157) A

def Var157 : Con157 → Ty157 → Type 1
 := λ Γ A =>
   ∀ (Var157 : Con157 → Ty157 → Type)
     (vz  : ∀ Γ A, Var157 (snoc157 Γ A) A)
     (vs  : ∀ Γ B A, Var157 Γ A → Var157 (snoc157 Γ B) A)
   , Var157 Γ A

def vz157 {Γ A} : Var157 (snoc157 Γ A) A
 := λ Var157 vz157 vs => vz157 _ _

def vs157 {Γ B A} : Var157 Γ A → Var157 (snoc157 Γ B) A
 := λ x Var157 vz157 vs157 => vs157 _ _ _ (x Var157 vz157 vs157)

def Tm157 : Con157 → Ty157 → Type 1
 := λ Γ A =>
   ∀ (Tm157  : Con157 → Ty157 → Type)
     (var   : ∀ Γ A     , Var157 Γ A → Tm157 Γ A)
     (lam   : ∀ Γ A B   , Tm157 (snoc157 Γ A) B → Tm157 Γ (arr157 A B))
     (app   : ∀ Γ A B   , Tm157 Γ (arr157 A B) → Tm157 Γ A → Tm157 Γ B)
   , Tm157 Γ A

def var157 {Γ A} : Var157 Γ A → Tm157 Γ A
 := λ x Tm157 var157 lam app =>
     var157 _ _ x

def lam157 {Γ A B} : Tm157 (snoc157 Γ A) B → Tm157 Γ (arr157 A B)
 := λ t Tm157 var157 lam157 app =>
     lam157 _ _ _ (t Tm157 var157 lam157 app)

def app157 {Γ A B} : Tm157 Γ (arr157 A B) → Tm157 Γ A → Tm157 Γ B
 := λ t u Tm157 var157 lam157 app157 =>
     app157 _ _ _
         (t Tm157 var157 lam157 app157)
         (u Tm157 var157 lam157 app157)

def v0157 {Γ A} : Tm157 (snoc157 Γ A) A
 := var157 vz157

def v1157 {Γ A B} : Tm157 (snoc157 (snoc157 Γ A) B) A
 := var157 (vs157 vz157)

def v2157 {Γ A B C} : Tm157 (snoc157 (snoc157 (snoc157 Γ A) B) C) A
 := var157 (vs157 (vs157 vz157))

def v3157 {Γ A B C D} : Tm157 (snoc157 (snoc157 (snoc157 (snoc157 Γ A) B) C) D) A
 := var157 (vs157 (vs157 (vs157 vz157)))

def v4157 {Γ A B C D E} : Tm157 (snoc157 (snoc157 (snoc157 (snoc157 (snoc157 Γ A) B) C) D) E) A
 := var157 (vs157 (vs157 (vs157 (vs157 vz157))))

def test157 {Γ A} : Tm157 Γ (arr157 (arr157 A A) (arr157 A A))
 := lam157 (lam157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 (app157 v1157 v0157)))))))


def Ty158 : Type 1
 := ∀ (Ty158 : Type)
      (ι   : Ty158)
      (arr : Ty158 → Ty158 → Ty158)
    , Ty158

def ι158 : Ty158 := λ _ ι158 _ => ι158

def arr158 : Ty158 → Ty158 → Ty158
 := λ A B Ty158 ι158 arr158 =>
     arr158 (A Ty158 ι158 arr158) (B Ty158 ι158 arr158)

def Con158 : Type 1
 := ∀ (Con158  : Type)
      (nil  : Con158)
      (snoc : Con158 → Ty158 → Con158)
    , Con158

def nil158 : Con158
 := λ Con158 nil158 snoc => nil158

def snoc158 : Con158 → Ty158 → Con158
 := λ Γ A Con158 nil158 snoc158 => snoc158 (Γ Con158 nil158 snoc158) A

def Var158 : Con158 → Ty158 → Type 1
 := λ Γ A =>
   ∀ (Var158 : Con158 → Ty158 → Type)
     (vz  : ∀ Γ A, Var158 (snoc158 Γ A) A)
     (vs  : ∀ Γ B A, Var158 Γ A → Var158 (snoc158 Γ B) A)
   , Var158 Γ A

def vz158 {Γ A} : Var158 (snoc158 Γ A) A
 := λ Var158 vz158 vs => vz158 _ _

def vs158 {Γ B A} : Var158 Γ A → Var158 (snoc158 Γ B) A
 := λ x Var158 vz158 vs158 => vs158 _ _ _ (x Var158 vz158 vs158)

def Tm158 : Con158 → Ty158 → Type 1
 := λ Γ A =>
   ∀ (Tm158  : Con158 → Ty158 → Type)
     (var   : ∀ Γ A     , Var158 Γ A → Tm158 Γ A)
     (lam   : ∀ Γ A B   , Tm158 (snoc158 Γ A) B → Tm158 Γ (arr158 A B))
     (app   : ∀ Γ A B   , Tm158 Γ (arr158 A B) → Tm158 Γ A → Tm158 Γ B)
   , Tm158 Γ A

def var158 {Γ A} : Var158 Γ A → Tm158 Γ A
 := λ x Tm158 var158 lam app =>
     var158 _ _ x

def lam158 {Γ A B} : Tm158 (snoc158 Γ A) B → Tm158 Γ (arr158 A B)
 := λ t Tm158 var158 lam158 app =>
     lam158 _ _ _ (t Tm158 var158 lam158 app)

def app158 {Γ A B} : Tm158 Γ (arr158 A B) → Tm158 Γ A → Tm158 Γ B
 := λ t u Tm158 var158 lam158 app158 =>
     app158 _ _ _
         (t Tm158 var158 lam158 app158)
         (u Tm158 var158 lam158 app158)

def v0158 {Γ A} : Tm158 (snoc158 Γ A) A
 := var158 vz158

def v1158 {Γ A B} : Tm158 (snoc158 (snoc158 Γ A) B) A
 := var158 (vs158 vz158)

def v2158 {Γ A B C} : Tm158 (snoc158 (snoc158 (snoc158 Γ A) B) C) A
 := var158 (vs158 (vs158 vz158))

def v3158 {Γ A B C D} : Tm158 (snoc158 (snoc158 (snoc158 (snoc158 Γ A) B) C) D) A
 := var158 (vs158 (vs158 (vs158 vz158)))

def v4158 {Γ A B C D E} : Tm158 (snoc158 (snoc158 (snoc158 (snoc158 (snoc158 Γ A) B) C) D) E) A
 := var158 (vs158 (vs158 (vs158 (vs158 vz158))))

def test158 {Γ A} : Tm158 Γ (arr158 (arr158 A A) (arr158 A A))
 := lam158 (lam158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 (app158 v1158 v0158)))))))


def Ty159 : Type 1
 := ∀ (Ty159 : Type)
      (ι   : Ty159)
      (arr : Ty159 → Ty159 → Ty159)
    , Ty159

def ι159 : Ty159 := λ _ ι159 _ => ι159

def arr159 : Ty159 → Ty159 → Ty159
 := λ A B Ty159 ι159 arr159 =>
     arr159 (A Ty159 ι159 arr159) (B Ty159 ι159 arr159)

def Con159 : Type 1
 := ∀ (Con159  : Type)
      (nil  : Con159)
      (snoc : Con159 → Ty159 → Con159)
    , Con159

def nil159 : Con159
 := λ Con159 nil159 snoc => nil159

def snoc159 : Con159 → Ty159 → Con159
 := λ Γ A Con159 nil159 snoc159 => snoc159 (Γ Con159 nil159 snoc159) A

def Var159 : Con159 → Ty159 → Type 1
 := λ Γ A =>
   ∀ (Var159 : Con159 → Ty159 → Type)
     (vz  : ∀ Γ A, Var159 (snoc159 Γ A) A)
     (vs  : ∀ Γ B A, Var159 Γ A → Var159 (snoc159 Γ B) A)
   , Var159 Γ A

def vz159 {Γ A} : Var159 (snoc159 Γ A) A
 := λ Var159 vz159 vs => vz159 _ _

def vs159 {Γ B A} : Var159 Γ A → Var159 (snoc159 Γ B) A
 := λ x Var159 vz159 vs159 => vs159 _ _ _ (x Var159 vz159 vs159)

def Tm159 : Con159 → Ty159 → Type 1
 := λ Γ A =>
   ∀ (Tm159  : Con159 → Ty159 → Type)
     (var   : ∀ Γ A     , Var159 Γ A → Tm159 Γ A)
     (lam   : ∀ Γ A B   , Tm159 (snoc159 Γ A) B → Tm159 Γ (arr159 A B))
     (app   : ∀ Γ A B   , Tm159 Γ (arr159 A B) → Tm159 Γ A → Tm159 Γ B)
   , Tm159 Γ A

def var159 {Γ A} : Var159 Γ A → Tm159 Γ A
 := λ x Tm159 var159 lam app =>
     var159 _ _ x

def lam159 {Γ A B} : Tm159 (snoc159 Γ A) B → Tm159 Γ (arr159 A B)
 := λ t Tm159 var159 lam159 app =>
     lam159 _ _ _ (t Tm159 var159 lam159 app)

def app159 {Γ A B} : Tm159 Γ (arr159 A B) → Tm159 Γ A → Tm159 Γ B
 := λ t u Tm159 var159 lam159 app159 =>
     app159 _ _ _
         (t Tm159 var159 lam159 app159)
         (u Tm159 var159 lam159 app159)

def v0159 {Γ A} : Tm159 (snoc159 Γ A) A
 := var159 vz159

def v1159 {Γ A B} : Tm159 (snoc159 (snoc159 Γ A) B) A
 := var159 (vs159 vz159)

def v2159 {Γ A B C} : Tm159 (snoc159 (snoc159 (snoc159 Γ A) B) C) A
 := var159 (vs159 (vs159 vz159))

def v3159 {Γ A B C D} : Tm159 (snoc159 (snoc159 (snoc159 (snoc159 Γ A) B) C) D) A
 := var159 (vs159 (vs159 (vs159 vz159)))

def v4159 {Γ A B C D E} : Tm159 (snoc159 (snoc159 (snoc159 (snoc159 (snoc159 Γ A) B) C) D) E) A
 := var159 (vs159 (vs159 (vs159 (vs159 vz159))))

def test159 {Γ A} : Tm159 Γ (arr159 (arr159 A A) (arr159 A A))
 := lam159 (lam159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 (app159 v1159 v0159)))))))


def Ty160 : Type 1
 := ∀ (Ty160 : Type)
      (ι   : Ty160)
      (arr : Ty160 → Ty160 → Ty160)
    , Ty160

def ι160 : Ty160 := λ _ ι160 _ => ι160

def arr160 : Ty160 → Ty160 → Ty160
 := λ A B Ty160 ι160 arr160 =>
     arr160 (A Ty160 ι160 arr160) (B Ty160 ι160 arr160)

def Con160 : Type 1
 := ∀ (Con160  : Type)
      (nil  : Con160)
      (snoc : Con160 → Ty160 → Con160)
    , Con160

def nil160 : Con160
 := λ Con160 nil160 snoc => nil160

def snoc160 : Con160 → Ty160 → Con160
 := λ Γ A Con160 nil160 snoc160 => snoc160 (Γ Con160 nil160 snoc160) A

def Var160 : Con160 → Ty160 → Type 1
 := λ Γ A =>
   ∀ (Var160 : Con160 → Ty160 → Type)
     (vz  : ∀ Γ A, Var160 (snoc160 Γ A) A)
     (vs  : ∀ Γ B A, Var160 Γ A → Var160 (snoc160 Γ B) A)
   , Var160 Γ A

def vz160 {Γ A} : Var160 (snoc160 Γ A) A
 := λ Var160 vz160 vs => vz160 _ _

def vs160 {Γ B A} : Var160 Γ A → Var160 (snoc160 Γ B) A
 := λ x Var160 vz160 vs160 => vs160 _ _ _ (x Var160 vz160 vs160)

def Tm160 : Con160 → Ty160 → Type 1
 := λ Γ A =>
   ∀ (Tm160  : Con160 → Ty160 → Type)
     (var   : ∀ Γ A     , Var160 Γ A → Tm160 Γ A)
     (lam   : ∀ Γ A B   , Tm160 (snoc160 Γ A) B → Tm160 Γ (arr160 A B))
     (app   : ∀ Γ A B   , Tm160 Γ (arr160 A B) → Tm160 Γ A → Tm160 Γ B)
   , Tm160 Γ A

def var160 {Γ A} : Var160 Γ A → Tm160 Γ A
 := λ x Tm160 var160 lam app =>
     var160 _ _ x

def lam160 {Γ A B} : Tm160 (snoc160 Γ A) B → Tm160 Γ (arr160 A B)
 := λ t Tm160 var160 lam160 app =>
     lam160 _ _ _ (t Tm160 var160 lam160 app)

def app160 {Γ A B} : Tm160 Γ (arr160 A B) → Tm160 Γ A → Tm160 Γ B
 := λ t u Tm160 var160 lam160 app160 =>
     app160 _ _ _
         (t Tm160 var160 lam160 app160)
         (u Tm160 var160 lam160 app160)

def v0160 {Γ A} : Tm160 (snoc160 Γ A) A
 := var160 vz160

def v1160 {Γ A B} : Tm160 (snoc160 (snoc160 Γ A) B) A
 := var160 (vs160 vz160)

def v2160 {Γ A B C} : Tm160 (snoc160 (snoc160 (snoc160 Γ A) B) C) A
 := var160 (vs160 (vs160 vz160))

def v3160 {Γ A B C D} : Tm160 (snoc160 (snoc160 (snoc160 (snoc160 Γ A) B) C) D) A
 := var160 (vs160 (vs160 (vs160 vz160)))

def v4160 {Γ A B C D E} : Tm160 (snoc160 (snoc160 (snoc160 (snoc160 (snoc160 Γ A) B) C) D) E) A
 := var160 (vs160 (vs160 (vs160 (vs160 vz160))))

def test160 {Γ A} : Tm160 Γ (arr160 (arr160 A A) (arr160 A A))
 := lam160 (lam160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 (app160 v1160 v0160)))))))


def Ty161 : Type 1
 := ∀ (Ty161 : Type)
      (ι   : Ty161)
      (arr : Ty161 → Ty161 → Ty161)
    , Ty161

def ι161 : Ty161 := λ _ ι161 _ => ι161

def arr161 : Ty161 → Ty161 → Ty161
 := λ A B Ty161 ι161 arr161 =>
     arr161 (A Ty161 ι161 arr161) (B Ty161 ι161 arr161)

def Con161 : Type 1
 := ∀ (Con161  : Type)
      (nil  : Con161)
      (snoc : Con161 → Ty161 → Con161)
    , Con161

def nil161 : Con161
 := λ Con161 nil161 snoc => nil161

def snoc161 : Con161 → Ty161 → Con161
 := λ Γ A Con161 nil161 snoc161 => snoc161 (Γ Con161 nil161 snoc161) A

def Var161 : Con161 → Ty161 → Type 1
 := λ Γ A =>
   ∀ (Var161 : Con161 → Ty161 → Type)
     (vz  : ∀ Γ A, Var161 (snoc161 Γ A) A)
     (vs  : ∀ Γ B A, Var161 Γ A → Var161 (snoc161 Γ B) A)
   , Var161 Γ A

def vz161 {Γ A} : Var161 (snoc161 Γ A) A
 := λ Var161 vz161 vs => vz161 _ _

def vs161 {Γ B A} : Var161 Γ A → Var161 (snoc161 Γ B) A
 := λ x Var161 vz161 vs161 => vs161 _ _ _ (x Var161 vz161 vs161)

def Tm161 : Con161 → Ty161 → Type 1
 := λ Γ A =>
   ∀ (Tm161  : Con161 → Ty161 → Type)
     (var   : ∀ Γ A     , Var161 Γ A → Tm161 Γ A)
     (lam   : ∀ Γ A B   , Tm161 (snoc161 Γ A) B → Tm161 Γ (arr161 A B))
     (app   : ∀ Γ A B   , Tm161 Γ (arr161 A B) → Tm161 Γ A → Tm161 Γ B)
   , Tm161 Γ A

def var161 {Γ A} : Var161 Γ A → Tm161 Γ A
 := λ x Tm161 var161 lam app =>
     var161 _ _ x

def lam161 {Γ A B} : Tm161 (snoc161 Γ A) B → Tm161 Γ (arr161 A B)
 := λ t Tm161 var161 lam161 app =>
     lam161 _ _ _ (t Tm161 var161 lam161 app)

def app161 {Γ A B} : Tm161 Γ (arr161 A B) → Tm161 Γ A → Tm161 Γ B
 := λ t u Tm161 var161 lam161 app161 =>
     app161 _ _ _
         (t Tm161 var161 lam161 app161)
         (u Tm161 var161 lam161 app161)

def v0161 {Γ A} : Tm161 (snoc161 Γ A) A
 := var161 vz161

def v1161 {Γ A B} : Tm161 (snoc161 (snoc161 Γ A) B) A
 := var161 (vs161 vz161)

def v2161 {Γ A B C} : Tm161 (snoc161 (snoc161 (snoc161 Γ A) B) C) A
 := var161 (vs161 (vs161 vz161))

def v3161 {Γ A B C D} : Tm161 (snoc161 (snoc161 (snoc161 (snoc161 Γ A) B) C) D) A
 := var161 (vs161 (vs161 (vs161 vz161)))

def v4161 {Γ A B C D E} : Tm161 (snoc161 (snoc161 (snoc161 (snoc161 (snoc161 Γ A) B) C) D) E) A
 := var161 (vs161 (vs161 (vs161 (vs161 vz161))))

def test161 {Γ A} : Tm161 Γ (arr161 (arr161 A A) (arr161 A A))
 := lam161 (lam161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 (app161 v1161 v0161)))))))


def Ty162 : Type 1
 := ∀ (Ty162 : Type)
      (ι   : Ty162)
      (arr : Ty162 → Ty162 → Ty162)
    , Ty162

def ι162 : Ty162 := λ _ ι162 _ => ι162

def arr162 : Ty162 → Ty162 → Ty162
 := λ A B Ty162 ι162 arr162 =>
     arr162 (A Ty162 ι162 arr162) (B Ty162 ι162 arr162)

def Con162 : Type 1
 := ∀ (Con162  : Type)
      (nil  : Con162)
      (snoc : Con162 → Ty162 → Con162)
    , Con162

def nil162 : Con162
 := λ Con162 nil162 snoc => nil162

def snoc162 : Con162 → Ty162 → Con162
 := λ Γ A Con162 nil162 snoc162 => snoc162 (Γ Con162 nil162 snoc162) A

def Var162 : Con162 → Ty162 → Type 1
 := λ Γ A =>
   ∀ (Var162 : Con162 → Ty162 → Type)
     (vz  : ∀ Γ A, Var162 (snoc162 Γ A) A)
     (vs  : ∀ Γ B A, Var162 Γ A → Var162 (snoc162 Γ B) A)
   , Var162 Γ A

def vz162 {Γ A} : Var162 (snoc162 Γ A) A
 := λ Var162 vz162 vs => vz162 _ _

def vs162 {Γ B A} : Var162 Γ A → Var162 (snoc162 Γ B) A
 := λ x Var162 vz162 vs162 => vs162 _ _ _ (x Var162 vz162 vs162)

def Tm162 : Con162 → Ty162 → Type 1
 := λ Γ A =>
   ∀ (Tm162  : Con162 → Ty162 → Type)
     (var   : ∀ Γ A     , Var162 Γ A → Tm162 Γ A)
     (lam   : ∀ Γ A B   , Tm162 (snoc162 Γ A) B → Tm162 Γ (arr162 A B))
     (app   : ∀ Γ A B   , Tm162 Γ (arr162 A B) → Tm162 Γ A → Tm162 Γ B)
   , Tm162 Γ A

def var162 {Γ A} : Var162 Γ A → Tm162 Γ A
 := λ x Tm162 var162 lam app =>
     var162 _ _ x

def lam162 {Γ A B} : Tm162 (snoc162 Γ A) B → Tm162 Γ (arr162 A B)
 := λ t Tm162 var162 lam162 app =>
     lam162 _ _ _ (t Tm162 var162 lam162 app)

def app162 {Γ A B} : Tm162 Γ (arr162 A B) → Tm162 Γ A → Tm162 Γ B
 := λ t u Tm162 var162 lam162 app162 =>
     app162 _ _ _
         (t Tm162 var162 lam162 app162)
         (u Tm162 var162 lam162 app162)

def v0162 {Γ A} : Tm162 (snoc162 Γ A) A
 := var162 vz162

def v1162 {Γ A B} : Tm162 (snoc162 (snoc162 Γ A) B) A
 := var162 (vs162 vz162)

def v2162 {Γ A B C} : Tm162 (snoc162 (snoc162 (snoc162 Γ A) B) C) A
 := var162 (vs162 (vs162 vz162))

def v3162 {Γ A B C D} : Tm162 (snoc162 (snoc162 (snoc162 (snoc162 Γ A) B) C) D) A
 := var162 (vs162 (vs162 (vs162 vz162)))

def v4162 {Γ A B C D E} : Tm162 (snoc162 (snoc162 (snoc162 (snoc162 (snoc162 Γ A) B) C) D) E) A
 := var162 (vs162 (vs162 (vs162 (vs162 vz162))))

def test162 {Γ A} : Tm162 Γ (arr162 (arr162 A A) (arr162 A A))
 := lam162 (lam162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 (app162 v1162 v0162)))))))


def Ty163 : Type 1
 := ∀ (Ty163 : Type)
      (ι   : Ty163)
      (arr : Ty163 → Ty163 → Ty163)
    , Ty163

def ι163 : Ty163 := λ _ ι163 _ => ι163

def arr163 : Ty163 → Ty163 → Ty163
 := λ A B Ty163 ι163 arr163 =>
     arr163 (A Ty163 ι163 arr163) (B Ty163 ι163 arr163)

def Con163 : Type 1
 := ∀ (Con163  : Type)
      (nil  : Con163)
      (snoc : Con163 → Ty163 → Con163)
    , Con163

def nil163 : Con163
 := λ Con163 nil163 snoc => nil163

def snoc163 : Con163 → Ty163 → Con163
 := λ Γ A Con163 nil163 snoc163 => snoc163 (Γ Con163 nil163 snoc163) A

def Var163 : Con163 → Ty163 → Type 1
 := λ Γ A =>
   ∀ (Var163 : Con163 → Ty163 → Type)
     (vz  : ∀ Γ A, Var163 (snoc163 Γ A) A)
     (vs  : ∀ Γ B A, Var163 Γ A → Var163 (snoc163 Γ B) A)
   , Var163 Γ A

def vz163 {Γ A} : Var163 (snoc163 Γ A) A
 := λ Var163 vz163 vs => vz163 _ _

def vs163 {Γ B A} : Var163 Γ A → Var163 (snoc163 Γ B) A
 := λ x Var163 vz163 vs163 => vs163 _ _ _ (x Var163 vz163 vs163)

def Tm163 : Con163 → Ty163 → Type 1
 := λ Γ A =>
   ∀ (Tm163  : Con163 → Ty163 → Type)
     (var   : ∀ Γ A     , Var163 Γ A → Tm163 Γ A)
     (lam   : ∀ Γ A B   , Tm163 (snoc163 Γ A) B → Tm163 Γ (arr163 A B))
     (app   : ∀ Γ A B   , Tm163 Γ (arr163 A B) → Tm163 Γ A → Tm163 Γ B)
   , Tm163 Γ A

def var163 {Γ A} : Var163 Γ A → Tm163 Γ A
 := λ x Tm163 var163 lam app =>
     var163 _ _ x

def lam163 {Γ A B} : Tm163 (snoc163 Γ A) B → Tm163 Γ (arr163 A B)
 := λ t Tm163 var163 lam163 app =>
     lam163 _ _ _ (t Tm163 var163 lam163 app)

def app163 {Γ A B} : Tm163 Γ (arr163 A B) → Tm163 Γ A → Tm163 Γ B
 := λ t u Tm163 var163 lam163 app163 =>
     app163 _ _ _
         (t Tm163 var163 lam163 app163)
         (u Tm163 var163 lam163 app163)

def v0163 {Γ A} : Tm163 (snoc163 Γ A) A
 := var163 vz163

def v1163 {Γ A B} : Tm163 (snoc163 (snoc163 Γ A) B) A
 := var163 (vs163 vz163)

def v2163 {Γ A B C} : Tm163 (snoc163 (snoc163 (snoc163 Γ A) B) C) A
 := var163 (vs163 (vs163 vz163))

def v3163 {Γ A B C D} : Tm163 (snoc163 (snoc163 (snoc163 (snoc163 Γ A) B) C) D) A
 := var163 (vs163 (vs163 (vs163 vz163)))

def v4163 {Γ A B C D E} : Tm163 (snoc163 (snoc163 (snoc163 (snoc163 (snoc163 Γ A) B) C) D) E) A
 := var163 (vs163 (vs163 (vs163 (vs163 vz163))))

def test163 {Γ A} : Tm163 Γ (arr163 (arr163 A A) (arr163 A A))
 := lam163 (lam163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 (app163 v1163 v0163)))))))


def Ty164 : Type 1
 := ∀ (Ty164 : Type)
      (ι   : Ty164)
      (arr : Ty164 → Ty164 → Ty164)
    , Ty164

def ι164 : Ty164 := λ _ ι164 _ => ι164

def arr164 : Ty164 → Ty164 → Ty164
 := λ A B Ty164 ι164 arr164 =>
     arr164 (A Ty164 ι164 arr164) (B Ty164 ι164 arr164)

def Con164 : Type 1
 := ∀ (Con164  : Type)
      (nil  : Con164)
      (snoc : Con164 → Ty164 → Con164)
    , Con164

def nil164 : Con164
 := λ Con164 nil164 snoc => nil164

def snoc164 : Con164 → Ty164 → Con164
 := λ Γ A Con164 nil164 snoc164 => snoc164 (Γ Con164 nil164 snoc164) A

def Var164 : Con164 → Ty164 → Type 1
 := λ Γ A =>
   ∀ (Var164 : Con164 → Ty164 → Type)
     (vz  : ∀ Γ A, Var164 (snoc164 Γ A) A)
     (vs  : ∀ Γ B A, Var164 Γ A → Var164 (snoc164 Γ B) A)
   , Var164 Γ A

def vz164 {Γ A} : Var164 (snoc164 Γ A) A
 := λ Var164 vz164 vs => vz164 _ _

def vs164 {Γ B A} : Var164 Γ A → Var164 (snoc164 Γ B) A
 := λ x Var164 vz164 vs164 => vs164 _ _ _ (x Var164 vz164 vs164)

def Tm164 : Con164 → Ty164 → Type 1
 := λ Γ A =>
   ∀ (Tm164  : Con164 → Ty164 → Type)
     (var   : ∀ Γ A     , Var164 Γ A → Tm164 Γ A)
     (lam   : ∀ Γ A B   , Tm164 (snoc164 Γ A) B → Tm164 Γ (arr164 A B))
     (app   : ∀ Γ A B   , Tm164 Γ (arr164 A B) → Tm164 Γ A → Tm164 Γ B)
   , Tm164 Γ A

def var164 {Γ A} : Var164 Γ A → Tm164 Γ A
 := λ x Tm164 var164 lam app =>
     var164 _ _ x

def lam164 {Γ A B} : Tm164 (snoc164 Γ A) B → Tm164 Γ (arr164 A B)
 := λ t Tm164 var164 lam164 app =>
     lam164 _ _ _ (t Tm164 var164 lam164 app)

def app164 {Γ A B} : Tm164 Γ (arr164 A B) → Tm164 Γ A → Tm164 Γ B
 := λ t u Tm164 var164 lam164 app164 =>
     app164 _ _ _
         (t Tm164 var164 lam164 app164)
         (u Tm164 var164 lam164 app164)

def v0164 {Γ A} : Tm164 (snoc164 Γ A) A
 := var164 vz164

def v1164 {Γ A B} : Tm164 (snoc164 (snoc164 Γ A) B) A
 := var164 (vs164 vz164)

def v2164 {Γ A B C} : Tm164 (snoc164 (snoc164 (snoc164 Γ A) B) C) A
 := var164 (vs164 (vs164 vz164))

def v3164 {Γ A B C D} : Tm164 (snoc164 (snoc164 (snoc164 (snoc164 Γ A) B) C) D) A
 := var164 (vs164 (vs164 (vs164 vz164)))

def v4164 {Γ A B C D E} : Tm164 (snoc164 (snoc164 (snoc164 (snoc164 (snoc164 Γ A) B) C) D) E) A
 := var164 (vs164 (vs164 (vs164 (vs164 vz164))))

def test164 {Γ A} : Tm164 Γ (arr164 (arr164 A A) (arr164 A A))
 := lam164 (lam164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 (app164 v1164 v0164)))))))


def Ty165 : Type 1
 := ∀ (Ty165 : Type)
      (ι   : Ty165)
      (arr : Ty165 → Ty165 → Ty165)
    , Ty165

def ι165 : Ty165 := λ _ ι165 _ => ι165

def arr165 : Ty165 → Ty165 → Ty165
 := λ A B Ty165 ι165 arr165 =>
     arr165 (A Ty165 ι165 arr165) (B Ty165 ι165 arr165)

def Con165 : Type 1
 := ∀ (Con165  : Type)
      (nil  : Con165)
      (snoc : Con165 → Ty165 → Con165)
    , Con165

def nil165 : Con165
 := λ Con165 nil165 snoc => nil165

def snoc165 : Con165 → Ty165 → Con165
 := λ Γ A Con165 nil165 snoc165 => snoc165 (Γ Con165 nil165 snoc165) A

def Var165 : Con165 → Ty165 → Type 1
 := λ Γ A =>
   ∀ (Var165 : Con165 → Ty165 → Type)
     (vz  : ∀ Γ A, Var165 (snoc165 Γ A) A)
     (vs  : ∀ Γ B A, Var165 Γ A → Var165 (snoc165 Γ B) A)
   , Var165 Γ A

def vz165 {Γ A} : Var165 (snoc165 Γ A) A
 := λ Var165 vz165 vs => vz165 _ _

def vs165 {Γ B A} : Var165 Γ A → Var165 (snoc165 Γ B) A
 := λ x Var165 vz165 vs165 => vs165 _ _ _ (x Var165 vz165 vs165)

def Tm165 : Con165 → Ty165 → Type 1
 := λ Γ A =>
   ∀ (Tm165  : Con165 → Ty165 → Type)
     (var   : ∀ Γ A     , Var165 Γ A → Tm165 Γ A)
     (lam   : ∀ Γ A B   , Tm165 (snoc165 Γ A) B → Tm165 Γ (arr165 A B))
     (app   : ∀ Γ A B   , Tm165 Γ (arr165 A B) → Tm165 Γ A → Tm165 Γ B)
   , Tm165 Γ A

def var165 {Γ A} : Var165 Γ A → Tm165 Γ A
 := λ x Tm165 var165 lam app =>
     var165 _ _ x

def lam165 {Γ A B} : Tm165 (snoc165 Γ A) B → Tm165 Γ (arr165 A B)
 := λ t Tm165 var165 lam165 app =>
     lam165 _ _ _ (t Tm165 var165 lam165 app)

def app165 {Γ A B} : Tm165 Γ (arr165 A B) → Tm165 Γ A → Tm165 Γ B
 := λ t u Tm165 var165 lam165 app165 =>
     app165 _ _ _
         (t Tm165 var165 lam165 app165)
         (u Tm165 var165 lam165 app165)

def v0165 {Γ A} : Tm165 (snoc165 Γ A) A
 := var165 vz165

def v1165 {Γ A B} : Tm165 (snoc165 (snoc165 Γ A) B) A
 := var165 (vs165 vz165)

def v2165 {Γ A B C} : Tm165 (snoc165 (snoc165 (snoc165 Γ A) B) C) A
 := var165 (vs165 (vs165 vz165))

def v3165 {Γ A B C D} : Tm165 (snoc165 (snoc165 (snoc165 (snoc165 Γ A) B) C) D) A
 := var165 (vs165 (vs165 (vs165 vz165)))

def v4165 {Γ A B C D E} : Tm165 (snoc165 (snoc165 (snoc165 (snoc165 (snoc165 Γ A) B) C) D) E) A
 := var165 (vs165 (vs165 (vs165 (vs165 vz165))))

def test165 {Γ A} : Tm165 Γ (arr165 (arr165 A A) (arr165 A A))
 := lam165 (lam165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 (app165 v1165 v0165)))))))


def Ty166 : Type 1
 := ∀ (Ty166 : Type)
      (ι   : Ty166)
      (arr : Ty166 → Ty166 → Ty166)
    , Ty166

def ι166 : Ty166 := λ _ ι166 _ => ι166

def arr166 : Ty166 → Ty166 → Ty166
 := λ A B Ty166 ι166 arr166 =>
     arr166 (A Ty166 ι166 arr166) (B Ty166 ι166 arr166)

def Con166 : Type 1
 := ∀ (Con166  : Type)
      (nil  : Con166)
      (snoc : Con166 → Ty166 → Con166)
    , Con166

def nil166 : Con166
 := λ Con166 nil166 snoc => nil166

def snoc166 : Con166 → Ty166 → Con166
 := λ Γ A Con166 nil166 snoc166 => snoc166 (Γ Con166 nil166 snoc166) A

def Var166 : Con166 → Ty166 → Type 1
 := λ Γ A =>
   ∀ (Var166 : Con166 → Ty166 → Type)
     (vz  : ∀ Γ A, Var166 (snoc166 Γ A) A)
     (vs  : ∀ Γ B A, Var166 Γ A → Var166 (snoc166 Γ B) A)
   , Var166 Γ A

def vz166 {Γ A} : Var166 (snoc166 Γ A) A
 := λ Var166 vz166 vs => vz166 _ _

def vs166 {Γ B A} : Var166 Γ A → Var166 (snoc166 Γ B) A
 := λ x Var166 vz166 vs166 => vs166 _ _ _ (x Var166 vz166 vs166)

def Tm166 : Con166 → Ty166 → Type 1
 := λ Γ A =>
   ∀ (Tm166  : Con166 → Ty166 → Type)
     (var   : ∀ Γ A     , Var166 Γ A → Tm166 Γ A)
     (lam   : ∀ Γ A B   , Tm166 (snoc166 Γ A) B → Tm166 Γ (arr166 A B))
     (app   : ∀ Γ A B   , Tm166 Γ (arr166 A B) → Tm166 Γ A → Tm166 Γ B)
   , Tm166 Γ A

def var166 {Γ A} : Var166 Γ A → Tm166 Γ A
 := λ x Tm166 var166 lam app =>
     var166 _ _ x

def lam166 {Γ A B} : Tm166 (snoc166 Γ A) B → Tm166 Γ (arr166 A B)
 := λ t Tm166 var166 lam166 app =>
     lam166 _ _ _ (t Tm166 var166 lam166 app)

def app166 {Γ A B} : Tm166 Γ (arr166 A B) → Tm166 Γ A → Tm166 Γ B
 := λ t u Tm166 var166 lam166 app166 =>
     app166 _ _ _
         (t Tm166 var166 lam166 app166)
         (u Tm166 var166 lam166 app166)

def v0166 {Γ A} : Tm166 (snoc166 Γ A) A
 := var166 vz166

def v1166 {Γ A B} : Tm166 (snoc166 (snoc166 Γ A) B) A
 := var166 (vs166 vz166)

def v2166 {Γ A B C} : Tm166 (snoc166 (snoc166 (snoc166 Γ A) B) C) A
 := var166 (vs166 (vs166 vz166))

def v3166 {Γ A B C D} : Tm166 (snoc166 (snoc166 (snoc166 (snoc166 Γ A) B) C) D) A
 := var166 (vs166 (vs166 (vs166 vz166)))

def v4166 {Γ A B C D E} : Tm166 (snoc166 (snoc166 (snoc166 (snoc166 (snoc166 Γ A) B) C) D) E) A
 := var166 (vs166 (vs166 (vs166 (vs166 vz166))))

def test166 {Γ A} : Tm166 Γ (arr166 (arr166 A A) (arr166 A A))
 := lam166 (lam166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 (app166 v1166 v0166)))))))


def Ty167 : Type 1
 := ∀ (Ty167 : Type)
      (ι   : Ty167)
      (arr : Ty167 → Ty167 → Ty167)
    , Ty167

def ι167 : Ty167 := λ _ ι167 _ => ι167

def arr167 : Ty167 → Ty167 → Ty167
 := λ A B Ty167 ι167 arr167 =>
     arr167 (A Ty167 ι167 arr167) (B Ty167 ι167 arr167)

def Con167 : Type 1
 := ∀ (Con167  : Type)
      (nil  : Con167)
      (snoc : Con167 → Ty167 → Con167)
    , Con167

def nil167 : Con167
 := λ Con167 nil167 snoc => nil167

def snoc167 : Con167 → Ty167 → Con167
 := λ Γ A Con167 nil167 snoc167 => snoc167 (Γ Con167 nil167 snoc167) A

def Var167 : Con167 → Ty167 → Type 1
 := λ Γ A =>
   ∀ (Var167 : Con167 → Ty167 → Type)
     (vz  : ∀ Γ A, Var167 (snoc167 Γ A) A)
     (vs  : ∀ Γ B A, Var167 Γ A → Var167 (snoc167 Γ B) A)
   , Var167 Γ A

def vz167 {Γ A} : Var167 (snoc167 Γ A) A
 := λ Var167 vz167 vs => vz167 _ _

def vs167 {Γ B A} : Var167 Γ A → Var167 (snoc167 Γ B) A
 := λ x Var167 vz167 vs167 => vs167 _ _ _ (x Var167 vz167 vs167)

def Tm167 : Con167 → Ty167 → Type 1
 := λ Γ A =>
   ∀ (Tm167  : Con167 → Ty167 → Type)
     (var   : ∀ Γ A     , Var167 Γ A → Tm167 Γ A)
     (lam   : ∀ Γ A B   , Tm167 (snoc167 Γ A) B → Tm167 Γ (arr167 A B))
     (app   : ∀ Γ A B   , Tm167 Γ (arr167 A B) → Tm167 Γ A → Tm167 Γ B)
   , Tm167 Γ A

def var167 {Γ A} : Var167 Γ A → Tm167 Γ A
 := λ x Tm167 var167 lam app =>
     var167 _ _ x

def lam167 {Γ A B} : Tm167 (snoc167 Γ A) B → Tm167 Γ (arr167 A B)
 := λ t Tm167 var167 lam167 app =>
     lam167 _ _ _ (t Tm167 var167 lam167 app)

def app167 {Γ A B} : Tm167 Γ (arr167 A B) → Tm167 Γ A → Tm167 Γ B
 := λ t u Tm167 var167 lam167 app167 =>
     app167 _ _ _
         (t Tm167 var167 lam167 app167)
         (u Tm167 var167 lam167 app167)

def v0167 {Γ A} : Tm167 (snoc167 Γ A) A
 := var167 vz167

def v1167 {Γ A B} : Tm167 (snoc167 (snoc167 Γ A) B) A
 := var167 (vs167 vz167)

def v2167 {Γ A B C} : Tm167 (snoc167 (snoc167 (snoc167 Γ A) B) C) A
 := var167 (vs167 (vs167 vz167))

def v3167 {Γ A B C D} : Tm167 (snoc167 (snoc167 (snoc167 (snoc167 Γ A) B) C) D) A
 := var167 (vs167 (vs167 (vs167 vz167)))

def v4167 {Γ A B C D E} : Tm167 (snoc167 (snoc167 (snoc167 (snoc167 (snoc167 Γ A) B) C) D) E) A
 := var167 (vs167 (vs167 (vs167 (vs167 vz167))))

def test167 {Γ A} : Tm167 Γ (arr167 (arr167 A A) (arr167 A A))
 := lam167 (lam167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 (app167 v1167 v0167)))))))


def Ty168 : Type 1
 := ∀ (Ty168 : Type)
      (ι   : Ty168)
      (arr : Ty168 → Ty168 → Ty168)
    , Ty168

def ι168 : Ty168 := λ _ ι168 _ => ι168

def arr168 : Ty168 → Ty168 → Ty168
 := λ A B Ty168 ι168 arr168 =>
     arr168 (A Ty168 ι168 arr168) (B Ty168 ι168 arr168)

def Con168 : Type 1
 := ∀ (Con168  : Type)
      (nil  : Con168)
      (snoc : Con168 → Ty168 → Con168)
    , Con168

def nil168 : Con168
 := λ Con168 nil168 snoc => nil168

def snoc168 : Con168 → Ty168 → Con168
 := λ Γ A Con168 nil168 snoc168 => snoc168 (Γ Con168 nil168 snoc168) A

def Var168 : Con168 → Ty168 → Type 1
 := λ Γ A =>
   ∀ (Var168 : Con168 → Ty168 → Type)
     (vz  : ∀ Γ A, Var168 (snoc168 Γ A) A)
     (vs  : ∀ Γ B A, Var168 Γ A → Var168 (snoc168 Γ B) A)
   , Var168 Γ A

def vz168 {Γ A} : Var168 (snoc168 Γ A) A
 := λ Var168 vz168 vs => vz168 _ _

def vs168 {Γ B A} : Var168 Γ A → Var168 (snoc168 Γ B) A
 := λ x Var168 vz168 vs168 => vs168 _ _ _ (x Var168 vz168 vs168)

def Tm168 : Con168 → Ty168 → Type 1
 := λ Γ A =>
   ∀ (Tm168  : Con168 → Ty168 → Type)
     (var   : ∀ Γ A     , Var168 Γ A → Tm168 Γ A)
     (lam   : ∀ Γ A B   , Tm168 (snoc168 Γ A) B → Tm168 Γ (arr168 A B))
     (app   : ∀ Γ A B   , Tm168 Γ (arr168 A B) → Tm168 Γ A → Tm168 Γ B)
   , Tm168 Γ A

def var168 {Γ A} : Var168 Γ A → Tm168 Γ A
 := λ x Tm168 var168 lam app =>
     var168 _ _ x

def lam168 {Γ A B} : Tm168 (snoc168 Γ A) B → Tm168 Γ (arr168 A B)
 := λ t Tm168 var168 lam168 app =>
     lam168 _ _ _ (t Tm168 var168 lam168 app)

def app168 {Γ A B} : Tm168 Γ (arr168 A B) → Tm168 Γ A → Tm168 Γ B
 := λ t u Tm168 var168 lam168 app168 =>
     app168 _ _ _
         (t Tm168 var168 lam168 app168)
         (u Tm168 var168 lam168 app168)

def v0168 {Γ A} : Tm168 (snoc168 Γ A) A
 := var168 vz168

def v1168 {Γ A B} : Tm168 (snoc168 (snoc168 Γ A) B) A
 := var168 (vs168 vz168)

def v2168 {Γ A B C} : Tm168 (snoc168 (snoc168 (snoc168 Γ A) B) C) A
 := var168 (vs168 (vs168 vz168))

def v3168 {Γ A B C D} : Tm168 (snoc168 (snoc168 (snoc168 (snoc168 Γ A) B) C) D) A
 := var168 (vs168 (vs168 (vs168 vz168)))

def v4168 {Γ A B C D E} : Tm168 (snoc168 (snoc168 (snoc168 (snoc168 (snoc168 Γ A) B) C) D) E) A
 := var168 (vs168 (vs168 (vs168 (vs168 vz168))))

def test168 {Γ A} : Tm168 Γ (arr168 (arr168 A A) (arr168 A A))
 := lam168 (lam168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 (app168 v1168 v0168)))))))


def Ty169 : Type 1
 := ∀ (Ty169 : Type)
      (ι   : Ty169)
      (arr : Ty169 → Ty169 → Ty169)
    , Ty169

def ι169 : Ty169 := λ _ ι169 _ => ι169

def arr169 : Ty169 → Ty169 → Ty169
 := λ A B Ty169 ι169 arr169 =>
     arr169 (A Ty169 ι169 arr169) (B Ty169 ι169 arr169)

def Con169 : Type 1
 := ∀ (Con169  : Type)
      (nil  : Con169)
      (snoc : Con169 → Ty169 → Con169)
    , Con169

def nil169 : Con169
 := λ Con169 nil169 snoc => nil169

def snoc169 : Con169 → Ty169 → Con169
 := λ Γ A Con169 nil169 snoc169 => snoc169 (Γ Con169 nil169 snoc169) A

def Var169 : Con169 → Ty169 → Type 1
 := λ Γ A =>
   ∀ (Var169 : Con169 → Ty169 → Type)
     (vz  : ∀ Γ A, Var169 (snoc169 Γ A) A)
     (vs  : ∀ Γ B A, Var169 Γ A → Var169 (snoc169 Γ B) A)
   , Var169 Γ A

def vz169 {Γ A} : Var169 (snoc169 Γ A) A
 := λ Var169 vz169 vs => vz169 _ _

def vs169 {Γ B A} : Var169 Γ A → Var169 (snoc169 Γ B) A
 := λ x Var169 vz169 vs169 => vs169 _ _ _ (x Var169 vz169 vs169)

def Tm169 : Con169 → Ty169 → Type 1
 := λ Γ A =>
   ∀ (Tm169  : Con169 → Ty169 → Type)
     (var   : ∀ Γ A     , Var169 Γ A → Tm169 Γ A)
     (lam   : ∀ Γ A B   , Tm169 (snoc169 Γ A) B → Tm169 Γ (arr169 A B))
     (app   : ∀ Γ A B   , Tm169 Γ (arr169 A B) → Tm169 Γ A → Tm169 Γ B)
   , Tm169 Γ A

def var169 {Γ A} : Var169 Γ A → Tm169 Γ A
 := λ x Tm169 var169 lam app =>
     var169 _ _ x

def lam169 {Γ A B} : Tm169 (snoc169 Γ A) B → Tm169 Γ (arr169 A B)
 := λ t Tm169 var169 lam169 app =>
     lam169 _ _ _ (t Tm169 var169 lam169 app)

def app169 {Γ A B} : Tm169 Γ (arr169 A B) → Tm169 Γ A → Tm169 Γ B
 := λ t u Tm169 var169 lam169 app169 =>
     app169 _ _ _
         (t Tm169 var169 lam169 app169)
         (u Tm169 var169 lam169 app169)

def v0169 {Γ A} : Tm169 (snoc169 Γ A) A
 := var169 vz169

def v1169 {Γ A B} : Tm169 (snoc169 (snoc169 Γ A) B) A
 := var169 (vs169 vz169)

def v2169 {Γ A B C} : Tm169 (snoc169 (snoc169 (snoc169 Γ A) B) C) A
 := var169 (vs169 (vs169 vz169))

def v3169 {Γ A B C D} : Tm169 (snoc169 (snoc169 (snoc169 (snoc169 Γ A) B) C) D) A
 := var169 (vs169 (vs169 (vs169 vz169)))

def v4169 {Γ A B C D E} : Tm169 (snoc169 (snoc169 (snoc169 (snoc169 (snoc169 Γ A) B) C) D) E) A
 := var169 (vs169 (vs169 (vs169 (vs169 vz169))))

def test169 {Γ A} : Tm169 Γ (arr169 (arr169 A A) (arr169 A A))
 := lam169 (lam169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 (app169 v1169 v0169)))))))


def Ty170 : Type 1
 := ∀ (Ty170 : Type)
      (ι   : Ty170)
      (arr : Ty170 → Ty170 → Ty170)
    , Ty170

def ι170 : Ty170 := λ _ ι170 _ => ι170

def arr170 : Ty170 → Ty170 → Ty170
 := λ A B Ty170 ι170 arr170 =>
     arr170 (A Ty170 ι170 arr170) (B Ty170 ι170 arr170)

def Con170 : Type 1
 := ∀ (Con170  : Type)
      (nil  : Con170)
      (snoc : Con170 → Ty170 → Con170)
    , Con170

def nil170 : Con170
 := λ Con170 nil170 snoc => nil170

def snoc170 : Con170 → Ty170 → Con170
 := λ Γ A Con170 nil170 snoc170 => snoc170 (Γ Con170 nil170 snoc170) A

def Var170 : Con170 → Ty170 → Type 1
 := λ Γ A =>
   ∀ (Var170 : Con170 → Ty170 → Type)
     (vz  : ∀ Γ A, Var170 (snoc170 Γ A) A)
     (vs  : ∀ Γ B A, Var170 Γ A → Var170 (snoc170 Γ B) A)
   , Var170 Γ A

def vz170 {Γ A} : Var170 (snoc170 Γ A) A
 := λ Var170 vz170 vs => vz170 _ _

def vs170 {Γ B A} : Var170 Γ A → Var170 (snoc170 Γ B) A
 := λ x Var170 vz170 vs170 => vs170 _ _ _ (x Var170 vz170 vs170)

def Tm170 : Con170 → Ty170 → Type 1
 := λ Γ A =>
   ∀ (Tm170  : Con170 → Ty170 → Type)
     (var   : ∀ Γ A     , Var170 Γ A → Tm170 Γ A)
     (lam   : ∀ Γ A B   , Tm170 (snoc170 Γ A) B → Tm170 Γ (arr170 A B))
     (app   : ∀ Γ A B   , Tm170 Γ (arr170 A B) → Tm170 Γ A → Tm170 Γ B)
   , Tm170 Γ A

def var170 {Γ A} : Var170 Γ A → Tm170 Γ A
 := λ x Tm170 var170 lam app =>
     var170 _ _ x

def lam170 {Γ A B} : Tm170 (snoc170 Γ A) B → Tm170 Γ (arr170 A B)
 := λ t Tm170 var170 lam170 app =>
     lam170 _ _ _ (t Tm170 var170 lam170 app)

def app170 {Γ A B} : Tm170 Γ (arr170 A B) → Tm170 Γ A → Tm170 Γ B
 := λ t u Tm170 var170 lam170 app170 =>
     app170 _ _ _
         (t Tm170 var170 lam170 app170)
         (u Tm170 var170 lam170 app170)

def v0170 {Γ A} : Tm170 (snoc170 Γ A) A
 := var170 vz170

def v1170 {Γ A B} : Tm170 (snoc170 (snoc170 Γ A) B) A
 := var170 (vs170 vz170)

def v2170 {Γ A B C} : Tm170 (snoc170 (snoc170 (snoc170 Γ A) B) C) A
 := var170 (vs170 (vs170 vz170))

def v3170 {Γ A B C D} : Tm170 (snoc170 (snoc170 (snoc170 (snoc170 Γ A) B) C) D) A
 := var170 (vs170 (vs170 (vs170 vz170)))

def v4170 {Γ A B C D E} : Tm170 (snoc170 (snoc170 (snoc170 (snoc170 (snoc170 Γ A) B) C) D) E) A
 := var170 (vs170 (vs170 (vs170 (vs170 vz170))))

def test170 {Γ A} : Tm170 Γ (arr170 (arr170 A A) (arr170 A A))
 := lam170 (lam170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 (app170 v1170 v0170)))))))


def Ty171 : Type 1
 := ∀ (Ty171 : Type)
      (ι   : Ty171)
      (arr : Ty171 → Ty171 → Ty171)
    , Ty171

def ι171 : Ty171 := λ _ ι171 _ => ι171

def arr171 : Ty171 → Ty171 → Ty171
 := λ A B Ty171 ι171 arr171 =>
     arr171 (A Ty171 ι171 arr171) (B Ty171 ι171 arr171)

def Con171 : Type 1
 := ∀ (Con171  : Type)
      (nil  : Con171)
      (snoc : Con171 → Ty171 → Con171)
    , Con171

def nil171 : Con171
 := λ Con171 nil171 snoc => nil171

def snoc171 : Con171 → Ty171 → Con171
 := λ Γ A Con171 nil171 snoc171 => snoc171 (Γ Con171 nil171 snoc171) A

def Var171 : Con171 → Ty171 → Type 1
 := λ Γ A =>
   ∀ (Var171 : Con171 → Ty171 → Type)
     (vz  : ∀ Γ A, Var171 (snoc171 Γ A) A)
     (vs  : ∀ Γ B A, Var171 Γ A → Var171 (snoc171 Γ B) A)
   , Var171 Γ A

def vz171 {Γ A} : Var171 (snoc171 Γ A) A
 := λ Var171 vz171 vs => vz171 _ _

def vs171 {Γ B A} : Var171 Γ A → Var171 (snoc171 Γ B) A
 := λ x Var171 vz171 vs171 => vs171 _ _ _ (x Var171 vz171 vs171)

def Tm171 : Con171 → Ty171 → Type 1
 := λ Γ A =>
   ∀ (Tm171  : Con171 → Ty171 → Type)
     (var   : ∀ Γ A     , Var171 Γ A → Tm171 Γ A)
     (lam   : ∀ Γ A B   , Tm171 (snoc171 Γ A) B → Tm171 Γ (arr171 A B))
     (app   : ∀ Γ A B   , Tm171 Γ (arr171 A B) → Tm171 Γ A → Tm171 Γ B)
   , Tm171 Γ A

def var171 {Γ A} : Var171 Γ A → Tm171 Γ A
 := λ x Tm171 var171 lam app =>
     var171 _ _ x

def lam171 {Γ A B} : Tm171 (snoc171 Γ A) B → Tm171 Γ (arr171 A B)
 := λ t Tm171 var171 lam171 app =>
     lam171 _ _ _ (t Tm171 var171 lam171 app)

def app171 {Γ A B} : Tm171 Γ (arr171 A B) → Tm171 Γ A → Tm171 Γ B
 := λ t u Tm171 var171 lam171 app171 =>
     app171 _ _ _
         (t Tm171 var171 lam171 app171)
         (u Tm171 var171 lam171 app171)

def v0171 {Γ A} : Tm171 (snoc171 Γ A) A
 := var171 vz171

def v1171 {Γ A B} : Tm171 (snoc171 (snoc171 Γ A) B) A
 := var171 (vs171 vz171)

def v2171 {Γ A B C} : Tm171 (snoc171 (snoc171 (snoc171 Γ A) B) C) A
 := var171 (vs171 (vs171 vz171))

def v3171 {Γ A B C D} : Tm171 (snoc171 (snoc171 (snoc171 (snoc171 Γ A) B) C) D) A
 := var171 (vs171 (vs171 (vs171 vz171)))

def v4171 {Γ A B C D E} : Tm171 (snoc171 (snoc171 (snoc171 (snoc171 (snoc171 Γ A) B) C) D) E) A
 := var171 (vs171 (vs171 (vs171 (vs171 vz171))))

def test171 {Γ A} : Tm171 Γ (arr171 (arr171 A A) (arr171 A A))
 := lam171 (lam171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 (app171 v1171 v0171)))))))


def Ty172 : Type 1
 := ∀ (Ty172 : Type)
      (ι   : Ty172)
      (arr : Ty172 → Ty172 → Ty172)
    , Ty172

def ι172 : Ty172 := λ _ ι172 _ => ι172

def arr172 : Ty172 → Ty172 → Ty172
 := λ A B Ty172 ι172 arr172 =>
     arr172 (A Ty172 ι172 arr172) (B Ty172 ι172 arr172)

def Con172 : Type 1
 := ∀ (Con172  : Type)
      (nil  : Con172)
      (snoc : Con172 → Ty172 → Con172)
    , Con172

def nil172 : Con172
 := λ Con172 nil172 snoc => nil172

def snoc172 : Con172 → Ty172 → Con172
 := λ Γ A Con172 nil172 snoc172 => snoc172 (Γ Con172 nil172 snoc172) A

def Var172 : Con172 → Ty172 → Type 1
 := λ Γ A =>
   ∀ (Var172 : Con172 → Ty172 → Type)
     (vz  : ∀ Γ A, Var172 (snoc172 Γ A) A)
     (vs  : ∀ Γ B A, Var172 Γ A → Var172 (snoc172 Γ B) A)
   , Var172 Γ A

def vz172 {Γ A} : Var172 (snoc172 Γ A) A
 := λ Var172 vz172 vs => vz172 _ _

def vs172 {Γ B A} : Var172 Γ A → Var172 (snoc172 Γ B) A
 := λ x Var172 vz172 vs172 => vs172 _ _ _ (x Var172 vz172 vs172)

def Tm172 : Con172 → Ty172 → Type 1
 := λ Γ A =>
   ∀ (Tm172  : Con172 → Ty172 → Type)
     (var   : ∀ Γ A     , Var172 Γ A → Tm172 Γ A)
     (lam   : ∀ Γ A B   , Tm172 (snoc172 Γ A) B → Tm172 Γ (arr172 A B))
     (app   : ∀ Γ A B   , Tm172 Γ (arr172 A B) → Tm172 Γ A → Tm172 Γ B)
   , Tm172 Γ A

def var172 {Γ A} : Var172 Γ A → Tm172 Γ A
 := λ x Tm172 var172 lam app =>
     var172 _ _ x

def lam172 {Γ A B} : Tm172 (snoc172 Γ A) B → Tm172 Γ (arr172 A B)
 := λ t Tm172 var172 lam172 app =>
     lam172 _ _ _ (t Tm172 var172 lam172 app)

def app172 {Γ A B} : Tm172 Γ (arr172 A B) → Tm172 Γ A → Tm172 Γ B
 := λ t u Tm172 var172 lam172 app172 =>
     app172 _ _ _
         (t Tm172 var172 lam172 app172)
         (u Tm172 var172 lam172 app172)

def v0172 {Γ A} : Tm172 (snoc172 Γ A) A
 := var172 vz172

def v1172 {Γ A B} : Tm172 (snoc172 (snoc172 Γ A) B) A
 := var172 (vs172 vz172)

def v2172 {Γ A B C} : Tm172 (snoc172 (snoc172 (snoc172 Γ A) B) C) A
 := var172 (vs172 (vs172 vz172))

def v3172 {Γ A B C D} : Tm172 (snoc172 (snoc172 (snoc172 (snoc172 Γ A) B) C) D) A
 := var172 (vs172 (vs172 (vs172 vz172)))

def v4172 {Γ A B C D E} : Tm172 (snoc172 (snoc172 (snoc172 (snoc172 (snoc172 Γ A) B) C) D) E) A
 := var172 (vs172 (vs172 (vs172 (vs172 vz172))))

def test172 {Γ A} : Tm172 Γ (arr172 (arr172 A A) (arr172 A A))
 := lam172 (lam172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 (app172 v1172 v0172)))))))


def Ty173 : Type 1
 := ∀ (Ty173 : Type)
      (ι   : Ty173)
      (arr : Ty173 → Ty173 → Ty173)
    , Ty173

def ι173 : Ty173 := λ _ ι173 _ => ι173

def arr173 : Ty173 → Ty173 → Ty173
 := λ A B Ty173 ι173 arr173 =>
     arr173 (A Ty173 ι173 arr173) (B Ty173 ι173 arr173)

def Con173 : Type 1
 := ∀ (Con173  : Type)
      (nil  : Con173)
      (snoc : Con173 → Ty173 → Con173)
    , Con173

def nil173 : Con173
 := λ Con173 nil173 snoc => nil173

def snoc173 : Con173 → Ty173 → Con173
 := λ Γ A Con173 nil173 snoc173 => snoc173 (Γ Con173 nil173 snoc173) A

def Var173 : Con173 → Ty173 → Type 1
 := λ Γ A =>
   ∀ (Var173 : Con173 → Ty173 → Type)
     (vz  : ∀ Γ A, Var173 (snoc173 Γ A) A)
     (vs  : ∀ Γ B A, Var173 Γ A → Var173 (snoc173 Γ B) A)
   , Var173 Γ A

def vz173 {Γ A} : Var173 (snoc173 Γ A) A
 := λ Var173 vz173 vs => vz173 _ _

def vs173 {Γ B A} : Var173 Γ A → Var173 (snoc173 Γ B) A
 := λ x Var173 vz173 vs173 => vs173 _ _ _ (x Var173 vz173 vs173)

def Tm173 : Con173 → Ty173 → Type 1
 := λ Γ A =>
   ∀ (Tm173  : Con173 → Ty173 → Type)
     (var   : ∀ Γ A     , Var173 Γ A → Tm173 Γ A)
     (lam   : ∀ Γ A B   , Tm173 (snoc173 Γ A) B → Tm173 Γ (arr173 A B))
     (app   : ∀ Γ A B   , Tm173 Γ (arr173 A B) → Tm173 Γ A → Tm173 Γ B)
   , Tm173 Γ A

def var173 {Γ A} : Var173 Γ A → Tm173 Γ A
 := λ x Tm173 var173 lam app =>
     var173 _ _ x

def lam173 {Γ A B} : Tm173 (snoc173 Γ A) B → Tm173 Γ (arr173 A B)
 := λ t Tm173 var173 lam173 app =>
     lam173 _ _ _ (t Tm173 var173 lam173 app)

def app173 {Γ A B} : Tm173 Γ (arr173 A B) → Tm173 Γ A → Tm173 Γ B
 := λ t u Tm173 var173 lam173 app173 =>
     app173 _ _ _
         (t Tm173 var173 lam173 app173)
         (u Tm173 var173 lam173 app173)

def v0173 {Γ A} : Tm173 (snoc173 Γ A) A
 := var173 vz173

def v1173 {Γ A B} : Tm173 (snoc173 (snoc173 Γ A) B) A
 := var173 (vs173 vz173)

def v2173 {Γ A B C} : Tm173 (snoc173 (snoc173 (snoc173 Γ A) B) C) A
 := var173 (vs173 (vs173 vz173))

def v3173 {Γ A B C D} : Tm173 (snoc173 (snoc173 (snoc173 (snoc173 Γ A) B) C) D) A
 := var173 (vs173 (vs173 (vs173 vz173)))

def v4173 {Γ A B C D E} : Tm173 (snoc173 (snoc173 (snoc173 (snoc173 (snoc173 Γ A) B) C) D) E) A
 := var173 (vs173 (vs173 (vs173 (vs173 vz173))))

def test173 {Γ A} : Tm173 Γ (arr173 (arr173 A A) (arr173 A A))
 := lam173 (lam173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 (app173 v1173 v0173)))))))


def Ty174 : Type 1
 := ∀ (Ty174 : Type)
      (ι   : Ty174)
      (arr : Ty174 → Ty174 → Ty174)
    , Ty174

def ι174 : Ty174 := λ _ ι174 _ => ι174

def arr174 : Ty174 → Ty174 → Ty174
 := λ A B Ty174 ι174 arr174 =>
     arr174 (A Ty174 ι174 arr174) (B Ty174 ι174 arr174)

def Con174 : Type 1
 := ∀ (Con174  : Type)
      (nil  : Con174)
      (snoc : Con174 → Ty174 → Con174)
    , Con174

def nil174 : Con174
 := λ Con174 nil174 snoc => nil174

def snoc174 : Con174 → Ty174 → Con174
 := λ Γ A Con174 nil174 snoc174 => snoc174 (Γ Con174 nil174 snoc174) A

def Var174 : Con174 → Ty174 → Type 1
 := λ Γ A =>
   ∀ (Var174 : Con174 → Ty174 → Type)
     (vz  : ∀ Γ A, Var174 (snoc174 Γ A) A)
     (vs  : ∀ Γ B A, Var174 Γ A → Var174 (snoc174 Γ B) A)
   , Var174 Γ A

def vz174 {Γ A} : Var174 (snoc174 Γ A) A
 := λ Var174 vz174 vs => vz174 _ _

def vs174 {Γ B A} : Var174 Γ A → Var174 (snoc174 Γ B) A
 := λ x Var174 vz174 vs174 => vs174 _ _ _ (x Var174 vz174 vs174)

def Tm174 : Con174 → Ty174 → Type 1
 := λ Γ A =>
   ∀ (Tm174  : Con174 → Ty174 → Type)
     (var   : ∀ Γ A     , Var174 Γ A → Tm174 Γ A)
     (lam   : ∀ Γ A B   , Tm174 (snoc174 Γ A) B → Tm174 Γ (arr174 A B))
     (app   : ∀ Γ A B   , Tm174 Γ (arr174 A B) → Tm174 Γ A → Tm174 Γ B)
   , Tm174 Γ A

def var174 {Γ A} : Var174 Γ A → Tm174 Γ A
 := λ x Tm174 var174 lam app =>
     var174 _ _ x

def lam174 {Γ A B} : Tm174 (snoc174 Γ A) B → Tm174 Γ (arr174 A B)
 := λ t Tm174 var174 lam174 app =>
     lam174 _ _ _ (t Tm174 var174 lam174 app)

def app174 {Γ A B} : Tm174 Γ (arr174 A B) → Tm174 Γ A → Tm174 Γ B
 := λ t u Tm174 var174 lam174 app174 =>
     app174 _ _ _
         (t Tm174 var174 lam174 app174)
         (u Tm174 var174 lam174 app174)

def v0174 {Γ A} : Tm174 (snoc174 Γ A) A
 := var174 vz174

def v1174 {Γ A B} : Tm174 (snoc174 (snoc174 Γ A) B) A
 := var174 (vs174 vz174)

def v2174 {Γ A B C} : Tm174 (snoc174 (snoc174 (snoc174 Γ A) B) C) A
 := var174 (vs174 (vs174 vz174))

def v3174 {Γ A B C D} : Tm174 (snoc174 (snoc174 (snoc174 (snoc174 Γ A) B) C) D) A
 := var174 (vs174 (vs174 (vs174 vz174)))

def v4174 {Γ A B C D E} : Tm174 (snoc174 (snoc174 (snoc174 (snoc174 (snoc174 Γ A) B) C) D) E) A
 := var174 (vs174 (vs174 (vs174 (vs174 vz174))))

def test174 {Γ A} : Tm174 Γ (arr174 (arr174 A A) (arr174 A A))
 := lam174 (lam174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 (app174 v1174 v0174)))))))


def Ty175 : Type 1
 := ∀ (Ty175 : Type)
      (ι   : Ty175)
      (arr : Ty175 → Ty175 → Ty175)
    , Ty175

def ι175 : Ty175 := λ _ ι175 _ => ι175

def arr175 : Ty175 → Ty175 → Ty175
 := λ A B Ty175 ι175 arr175 =>
     arr175 (A Ty175 ι175 arr175) (B Ty175 ι175 arr175)

def Con175 : Type 1
 := ∀ (Con175  : Type)
      (nil  : Con175)
      (snoc : Con175 → Ty175 → Con175)
    , Con175

def nil175 : Con175
 := λ Con175 nil175 snoc => nil175

def snoc175 : Con175 → Ty175 → Con175
 := λ Γ A Con175 nil175 snoc175 => snoc175 (Γ Con175 nil175 snoc175) A

def Var175 : Con175 → Ty175 → Type 1
 := λ Γ A =>
   ∀ (Var175 : Con175 → Ty175 → Type)
     (vz  : ∀ Γ A, Var175 (snoc175 Γ A) A)
     (vs  : ∀ Γ B A, Var175 Γ A → Var175 (snoc175 Γ B) A)
   , Var175 Γ A

def vz175 {Γ A} : Var175 (snoc175 Γ A) A
 := λ Var175 vz175 vs => vz175 _ _

def vs175 {Γ B A} : Var175 Γ A → Var175 (snoc175 Γ B) A
 := λ x Var175 vz175 vs175 => vs175 _ _ _ (x Var175 vz175 vs175)

def Tm175 : Con175 → Ty175 → Type 1
 := λ Γ A =>
   ∀ (Tm175  : Con175 → Ty175 → Type)
     (var   : ∀ Γ A     , Var175 Γ A → Tm175 Γ A)
     (lam   : ∀ Γ A B   , Tm175 (snoc175 Γ A) B → Tm175 Γ (arr175 A B))
     (app   : ∀ Γ A B   , Tm175 Γ (arr175 A B) → Tm175 Γ A → Tm175 Γ B)
   , Tm175 Γ A

def var175 {Γ A} : Var175 Γ A → Tm175 Γ A
 := λ x Tm175 var175 lam app =>
     var175 _ _ x

def lam175 {Γ A B} : Tm175 (snoc175 Γ A) B → Tm175 Γ (arr175 A B)
 := λ t Tm175 var175 lam175 app =>
     lam175 _ _ _ (t Tm175 var175 lam175 app)

def app175 {Γ A B} : Tm175 Γ (arr175 A B) → Tm175 Γ A → Tm175 Γ B
 := λ t u Tm175 var175 lam175 app175 =>
     app175 _ _ _
         (t Tm175 var175 lam175 app175)
         (u Tm175 var175 lam175 app175)

def v0175 {Γ A} : Tm175 (snoc175 Γ A) A
 := var175 vz175

def v1175 {Γ A B} : Tm175 (snoc175 (snoc175 Γ A) B) A
 := var175 (vs175 vz175)

def v2175 {Γ A B C} : Tm175 (snoc175 (snoc175 (snoc175 Γ A) B) C) A
 := var175 (vs175 (vs175 vz175))

def v3175 {Γ A B C D} : Tm175 (snoc175 (snoc175 (snoc175 (snoc175 Γ A) B) C) D) A
 := var175 (vs175 (vs175 (vs175 vz175)))

def v4175 {Γ A B C D E} : Tm175 (snoc175 (snoc175 (snoc175 (snoc175 (snoc175 Γ A) B) C) D) E) A
 := var175 (vs175 (vs175 (vs175 (vs175 vz175))))

def test175 {Γ A} : Tm175 Γ (arr175 (arr175 A A) (arr175 A A))
 := lam175 (lam175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 (app175 v1175 v0175)))))))


def Ty176 : Type 1
 := ∀ (Ty176 : Type)
      (ι   : Ty176)
      (arr : Ty176 → Ty176 → Ty176)
    , Ty176

def ι176 : Ty176 := λ _ ι176 _ => ι176

def arr176 : Ty176 → Ty176 → Ty176
 := λ A B Ty176 ι176 arr176 =>
     arr176 (A Ty176 ι176 arr176) (B Ty176 ι176 arr176)

def Con176 : Type 1
 := ∀ (Con176  : Type)
      (nil  : Con176)
      (snoc : Con176 → Ty176 → Con176)
    , Con176

def nil176 : Con176
 := λ Con176 nil176 snoc => nil176

def snoc176 : Con176 → Ty176 → Con176
 := λ Γ A Con176 nil176 snoc176 => snoc176 (Γ Con176 nil176 snoc176) A

def Var176 : Con176 → Ty176 → Type 1
 := λ Γ A =>
   ∀ (Var176 : Con176 → Ty176 → Type)
     (vz  : ∀ Γ A, Var176 (snoc176 Γ A) A)
     (vs  : ∀ Γ B A, Var176 Γ A → Var176 (snoc176 Γ B) A)
   , Var176 Γ A

def vz176 {Γ A} : Var176 (snoc176 Γ A) A
 := λ Var176 vz176 vs => vz176 _ _

def vs176 {Γ B A} : Var176 Γ A → Var176 (snoc176 Γ B) A
 := λ x Var176 vz176 vs176 => vs176 _ _ _ (x Var176 vz176 vs176)

def Tm176 : Con176 → Ty176 → Type 1
 := λ Γ A =>
   ∀ (Tm176  : Con176 → Ty176 → Type)
     (var   : ∀ Γ A     , Var176 Γ A → Tm176 Γ A)
     (lam   : ∀ Γ A B   , Tm176 (snoc176 Γ A) B → Tm176 Γ (arr176 A B))
     (app   : ∀ Γ A B   , Tm176 Γ (arr176 A B) → Tm176 Γ A → Tm176 Γ B)
   , Tm176 Γ A

def var176 {Γ A} : Var176 Γ A → Tm176 Γ A
 := λ x Tm176 var176 lam app =>
     var176 _ _ x

def lam176 {Γ A B} : Tm176 (snoc176 Γ A) B → Tm176 Γ (arr176 A B)
 := λ t Tm176 var176 lam176 app =>
     lam176 _ _ _ (t Tm176 var176 lam176 app)

def app176 {Γ A B} : Tm176 Γ (arr176 A B) → Tm176 Γ A → Tm176 Γ B
 := λ t u Tm176 var176 lam176 app176 =>
     app176 _ _ _
         (t Tm176 var176 lam176 app176)
         (u Tm176 var176 lam176 app176)

def v0176 {Γ A} : Tm176 (snoc176 Γ A) A
 := var176 vz176

def v1176 {Γ A B} : Tm176 (snoc176 (snoc176 Γ A) B) A
 := var176 (vs176 vz176)

def v2176 {Γ A B C} : Tm176 (snoc176 (snoc176 (snoc176 Γ A) B) C) A
 := var176 (vs176 (vs176 vz176))

def v3176 {Γ A B C D} : Tm176 (snoc176 (snoc176 (snoc176 (snoc176 Γ A) B) C) D) A
 := var176 (vs176 (vs176 (vs176 vz176)))

def v4176 {Γ A B C D E} : Tm176 (snoc176 (snoc176 (snoc176 (snoc176 (snoc176 Γ A) B) C) D) E) A
 := var176 (vs176 (vs176 (vs176 (vs176 vz176))))

def test176 {Γ A} : Tm176 Γ (arr176 (arr176 A A) (arr176 A A))
 := lam176 (lam176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 (app176 v1176 v0176)))))))


def Ty177 : Type 1
 := ∀ (Ty177 : Type)
      (ι   : Ty177)
      (arr : Ty177 → Ty177 → Ty177)
    , Ty177

def ι177 : Ty177 := λ _ ι177 _ => ι177

def arr177 : Ty177 → Ty177 → Ty177
 := λ A B Ty177 ι177 arr177 =>
     arr177 (A Ty177 ι177 arr177) (B Ty177 ι177 arr177)

def Con177 : Type 1
 := ∀ (Con177  : Type)
      (nil  : Con177)
      (snoc : Con177 → Ty177 → Con177)
    , Con177

def nil177 : Con177
 := λ Con177 nil177 snoc => nil177

def snoc177 : Con177 → Ty177 → Con177
 := λ Γ A Con177 nil177 snoc177 => snoc177 (Γ Con177 nil177 snoc177) A

def Var177 : Con177 → Ty177 → Type 1
 := λ Γ A =>
   ∀ (Var177 : Con177 → Ty177 → Type)
     (vz  : ∀ Γ A, Var177 (snoc177 Γ A) A)
     (vs  : ∀ Γ B A, Var177 Γ A → Var177 (snoc177 Γ B) A)
   , Var177 Γ A

def vz177 {Γ A} : Var177 (snoc177 Γ A) A
 := λ Var177 vz177 vs => vz177 _ _

def vs177 {Γ B A} : Var177 Γ A → Var177 (snoc177 Γ B) A
 := λ x Var177 vz177 vs177 => vs177 _ _ _ (x Var177 vz177 vs177)

def Tm177 : Con177 → Ty177 → Type 1
 := λ Γ A =>
   ∀ (Tm177  : Con177 → Ty177 → Type)
     (var   : ∀ Γ A     , Var177 Γ A → Tm177 Γ A)
     (lam   : ∀ Γ A B   , Tm177 (snoc177 Γ A) B → Tm177 Γ (arr177 A B))
     (app   : ∀ Γ A B   , Tm177 Γ (arr177 A B) → Tm177 Γ A → Tm177 Γ B)
   , Tm177 Γ A

def var177 {Γ A} : Var177 Γ A → Tm177 Γ A
 := λ x Tm177 var177 lam app =>
     var177 _ _ x

def lam177 {Γ A B} : Tm177 (snoc177 Γ A) B → Tm177 Γ (arr177 A B)
 := λ t Tm177 var177 lam177 app =>
     lam177 _ _ _ (t Tm177 var177 lam177 app)

def app177 {Γ A B} : Tm177 Γ (arr177 A B) → Tm177 Γ A → Tm177 Γ B
 := λ t u Tm177 var177 lam177 app177 =>
     app177 _ _ _
         (t Tm177 var177 lam177 app177)
         (u Tm177 var177 lam177 app177)

def v0177 {Γ A} : Tm177 (snoc177 Γ A) A
 := var177 vz177

def v1177 {Γ A B} : Tm177 (snoc177 (snoc177 Γ A) B) A
 := var177 (vs177 vz177)

def v2177 {Γ A B C} : Tm177 (snoc177 (snoc177 (snoc177 Γ A) B) C) A
 := var177 (vs177 (vs177 vz177))

def v3177 {Γ A B C D} : Tm177 (snoc177 (snoc177 (snoc177 (snoc177 Γ A) B) C) D) A
 := var177 (vs177 (vs177 (vs177 vz177)))

def v4177 {Γ A B C D E} : Tm177 (snoc177 (snoc177 (snoc177 (snoc177 (snoc177 Γ A) B) C) D) E) A
 := var177 (vs177 (vs177 (vs177 (vs177 vz177))))

def test177 {Γ A} : Tm177 Γ (arr177 (arr177 A A) (arr177 A A))
 := lam177 (lam177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 (app177 v1177 v0177)))))))


def Ty178 : Type 1
 := ∀ (Ty178 : Type)
      (ι   : Ty178)
      (arr : Ty178 → Ty178 → Ty178)
    , Ty178

def ι178 : Ty178 := λ _ ι178 _ => ι178

def arr178 : Ty178 → Ty178 → Ty178
 := λ A B Ty178 ι178 arr178 =>
     arr178 (A Ty178 ι178 arr178) (B Ty178 ι178 arr178)

def Con178 : Type 1
 := ∀ (Con178  : Type)
      (nil  : Con178)
      (snoc : Con178 → Ty178 → Con178)
    , Con178

def nil178 : Con178
 := λ Con178 nil178 snoc => nil178

def snoc178 : Con178 → Ty178 → Con178
 := λ Γ A Con178 nil178 snoc178 => snoc178 (Γ Con178 nil178 snoc178) A

def Var178 : Con178 → Ty178 → Type 1
 := λ Γ A =>
   ∀ (Var178 : Con178 → Ty178 → Type)
     (vz  : ∀ Γ A, Var178 (snoc178 Γ A) A)
     (vs  : ∀ Γ B A, Var178 Γ A → Var178 (snoc178 Γ B) A)
   , Var178 Γ A

def vz178 {Γ A} : Var178 (snoc178 Γ A) A
 := λ Var178 vz178 vs => vz178 _ _

def vs178 {Γ B A} : Var178 Γ A → Var178 (snoc178 Γ B) A
 := λ x Var178 vz178 vs178 => vs178 _ _ _ (x Var178 vz178 vs178)

def Tm178 : Con178 → Ty178 → Type 1
 := λ Γ A =>
   ∀ (Tm178  : Con178 → Ty178 → Type)
     (var   : ∀ Γ A     , Var178 Γ A → Tm178 Γ A)
     (lam   : ∀ Γ A B   , Tm178 (snoc178 Γ A) B → Tm178 Γ (arr178 A B))
     (app   : ∀ Γ A B   , Tm178 Γ (arr178 A B) → Tm178 Γ A → Tm178 Γ B)
   , Tm178 Γ A

def var178 {Γ A} : Var178 Γ A → Tm178 Γ A
 := λ x Tm178 var178 lam app =>
     var178 _ _ x

def lam178 {Γ A B} : Tm178 (snoc178 Γ A) B → Tm178 Γ (arr178 A B)
 := λ t Tm178 var178 lam178 app =>
     lam178 _ _ _ (t Tm178 var178 lam178 app)

def app178 {Γ A B} : Tm178 Γ (arr178 A B) → Tm178 Γ A → Tm178 Γ B
 := λ t u Tm178 var178 lam178 app178 =>
     app178 _ _ _
         (t Tm178 var178 lam178 app178)
         (u Tm178 var178 lam178 app178)

def v0178 {Γ A} : Tm178 (snoc178 Γ A) A
 := var178 vz178

def v1178 {Γ A B} : Tm178 (snoc178 (snoc178 Γ A) B) A
 := var178 (vs178 vz178)

def v2178 {Γ A B C} : Tm178 (snoc178 (snoc178 (snoc178 Γ A) B) C) A
 := var178 (vs178 (vs178 vz178))

def v3178 {Γ A B C D} : Tm178 (snoc178 (snoc178 (snoc178 (snoc178 Γ A) B) C) D) A
 := var178 (vs178 (vs178 (vs178 vz178)))

def v4178 {Γ A B C D E} : Tm178 (snoc178 (snoc178 (snoc178 (snoc178 (snoc178 Γ A) B) C) D) E) A
 := var178 (vs178 (vs178 (vs178 (vs178 vz178))))

def test178 {Γ A} : Tm178 Γ (arr178 (arr178 A A) (arr178 A A))
 := lam178 (lam178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 (app178 v1178 v0178)))))))


def Ty179 : Type 1
 := ∀ (Ty179 : Type)
      (ι   : Ty179)
      (arr : Ty179 → Ty179 → Ty179)
    , Ty179

def ι179 : Ty179 := λ _ ι179 _ => ι179

def arr179 : Ty179 → Ty179 → Ty179
 := λ A B Ty179 ι179 arr179 =>
     arr179 (A Ty179 ι179 arr179) (B Ty179 ι179 arr179)

def Con179 : Type 1
 := ∀ (Con179  : Type)
      (nil  : Con179)
      (snoc : Con179 → Ty179 → Con179)
    , Con179

def nil179 : Con179
 := λ Con179 nil179 snoc => nil179

def snoc179 : Con179 → Ty179 → Con179
 := λ Γ A Con179 nil179 snoc179 => snoc179 (Γ Con179 nil179 snoc179) A

def Var179 : Con179 → Ty179 → Type 1
 := λ Γ A =>
   ∀ (Var179 : Con179 → Ty179 → Type)
     (vz  : ∀ Γ A, Var179 (snoc179 Γ A) A)
     (vs  : ∀ Γ B A, Var179 Γ A → Var179 (snoc179 Γ B) A)
   , Var179 Γ A

def vz179 {Γ A} : Var179 (snoc179 Γ A) A
 := λ Var179 vz179 vs => vz179 _ _

def vs179 {Γ B A} : Var179 Γ A → Var179 (snoc179 Γ B) A
 := λ x Var179 vz179 vs179 => vs179 _ _ _ (x Var179 vz179 vs179)

def Tm179 : Con179 → Ty179 → Type 1
 := λ Γ A =>
   ∀ (Tm179  : Con179 → Ty179 → Type)
     (var   : ∀ Γ A     , Var179 Γ A → Tm179 Γ A)
     (lam   : ∀ Γ A B   , Tm179 (snoc179 Γ A) B → Tm179 Γ (arr179 A B))
     (app   : ∀ Γ A B   , Tm179 Γ (arr179 A B) → Tm179 Γ A → Tm179 Γ B)
   , Tm179 Γ A

def var179 {Γ A} : Var179 Γ A → Tm179 Γ A
 := λ x Tm179 var179 lam app =>
     var179 _ _ x

def lam179 {Γ A B} : Tm179 (snoc179 Γ A) B → Tm179 Γ (arr179 A B)
 := λ t Tm179 var179 lam179 app =>
     lam179 _ _ _ (t Tm179 var179 lam179 app)

def app179 {Γ A B} : Tm179 Γ (arr179 A B) → Tm179 Γ A → Tm179 Γ B
 := λ t u Tm179 var179 lam179 app179 =>
     app179 _ _ _
         (t Tm179 var179 lam179 app179)
         (u Tm179 var179 lam179 app179)

def v0179 {Γ A} : Tm179 (snoc179 Γ A) A
 := var179 vz179

def v1179 {Γ A B} : Tm179 (snoc179 (snoc179 Γ A) B) A
 := var179 (vs179 vz179)

def v2179 {Γ A B C} : Tm179 (snoc179 (snoc179 (snoc179 Γ A) B) C) A
 := var179 (vs179 (vs179 vz179))

def v3179 {Γ A B C D} : Tm179 (snoc179 (snoc179 (snoc179 (snoc179 Γ A) B) C) D) A
 := var179 (vs179 (vs179 (vs179 vz179)))

def v4179 {Γ A B C D E} : Tm179 (snoc179 (snoc179 (snoc179 (snoc179 (snoc179 Γ A) B) C) D) E) A
 := var179 (vs179 (vs179 (vs179 (vs179 vz179))))

def test179 {Γ A} : Tm179 Γ (arr179 (arr179 A A) (arr179 A A))
 := lam179 (lam179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 (app179 v1179 v0179)))))))


def Ty180 : Type 1
 := ∀ (Ty180 : Type)
      (ι   : Ty180)
      (arr : Ty180 → Ty180 → Ty180)
    , Ty180

def ι180 : Ty180 := λ _ ι180 _ => ι180

def arr180 : Ty180 → Ty180 → Ty180
 := λ A B Ty180 ι180 arr180 =>
     arr180 (A Ty180 ι180 arr180) (B Ty180 ι180 arr180)

def Con180 : Type 1
 := ∀ (Con180  : Type)
      (nil  : Con180)
      (snoc : Con180 → Ty180 → Con180)
    , Con180

def nil180 : Con180
 := λ Con180 nil180 snoc => nil180

def snoc180 : Con180 → Ty180 → Con180
 := λ Γ A Con180 nil180 snoc180 => snoc180 (Γ Con180 nil180 snoc180) A

def Var180 : Con180 → Ty180 → Type 1
 := λ Γ A =>
   ∀ (Var180 : Con180 → Ty180 → Type)
     (vz  : ∀ Γ A, Var180 (snoc180 Γ A) A)
     (vs  : ∀ Γ B A, Var180 Γ A → Var180 (snoc180 Γ B) A)
   , Var180 Γ A

def vz180 {Γ A} : Var180 (snoc180 Γ A) A
 := λ Var180 vz180 vs => vz180 _ _

def vs180 {Γ B A} : Var180 Γ A → Var180 (snoc180 Γ B) A
 := λ x Var180 vz180 vs180 => vs180 _ _ _ (x Var180 vz180 vs180)

def Tm180 : Con180 → Ty180 → Type 1
 := λ Γ A =>
   ∀ (Tm180  : Con180 → Ty180 → Type)
     (var   : ∀ Γ A     , Var180 Γ A → Tm180 Γ A)
     (lam   : ∀ Γ A B   , Tm180 (snoc180 Γ A) B → Tm180 Γ (arr180 A B))
     (app   : ∀ Γ A B   , Tm180 Γ (arr180 A B) → Tm180 Γ A → Tm180 Γ B)
   , Tm180 Γ A

def var180 {Γ A} : Var180 Γ A → Tm180 Γ A
 := λ x Tm180 var180 lam app =>
     var180 _ _ x

def lam180 {Γ A B} : Tm180 (snoc180 Γ A) B → Tm180 Γ (arr180 A B)
 := λ t Tm180 var180 lam180 app =>
     lam180 _ _ _ (t Tm180 var180 lam180 app)

def app180 {Γ A B} : Tm180 Γ (arr180 A B) → Tm180 Γ A → Tm180 Γ B
 := λ t u Tm180 var180 lam180 app180 =>
     app180 _ _ _
         (t Tm180 var180 lam180 app180)
         (u Tm180 var180 lam180 app180)

def v0180 {Γ A} : Tm180 (snoc180 Γ A) A
 := var180 vz180

def v1180 {Γ A B} : Tm180 (snoc180 (snoc180 Γ A) B) A
 := var180 (vs180 vz180)

def v2180 {Γ A B C} : Tm180 (snoc180 (snoc180 (snoc180 Γ A) B) C) A
 := var180 (vs180 (vs180 vz180))

def v3180 {Γ A B C D} : Tm180 (snoc180 (snoc180 (snoc180 (snoc180 Γ A) B) C) D) A
 := var180 (vs180 (vs180 (vs180 vz180)))

def v4180 {Γ A B C D E} : Tm180 (snoc180 (snoc180 (snoc180 (snoc180 (snoc180 Γ A) B) C) D) E) A
 := var180 (vs180 (vs180 (vs180 (vs180 vz180))))

def test180 {Γ A} : Tm180 Γ (arr180 (arr180 A A) (arr180 A A))
 := lam180 (lam180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 (app180 v1180 v0180)))))))


def Ty181 : Type 1
 := ∀ (Ty181 : Type)
      (ι   : Ty181)
      (arr : Ty181 → Ty181 → Ty181)
    , Ty181

def ι181 : Ty181 := λ _ ι181 _ => ι181

def arr181 : Ty181 → Ty181 → Ty181
 := λ A B Ty181 ι181 arr181 =>
     arr181 (A Ty181 ι181 arr181) (B Ty181 ι181 arr181)

def Con181 : Type 1
 := ∀ (Con181  : Type)
      (nil  : Con181)
      (snoc : Con181 → Ty181 → Con181)
    , Con181

def nil181 : Con181
 := λ Con181 nil181 snoc => nil181

def snoc181 : Con181 → Ty181 → Con181
 := λ Γ A Con181 nil181 snoc181 => snoc181 (Γ Con181 nil181 snoc181) A

def Var181 : Con181 → Ty181 → Type 1
 := λ Γ A =>
   ∀ (Var181 : Con181 → Ty181 → Type)
     (vz  : ∀ Γ A, Var181 (snoc181 Γ A) A)
     (vs  : ∀ Γ B A, Var181 Γ A → Var181 (snoc181 Γ B) A)
   , Var181 Γ A

def vz181 {Γ A} : Var181 (snoc181 Γ A) A
 := λ Var181 vz181 vs => vz181 _ _

def vs181 {Γ B A} : Var181 Γ A → Var181 (snoc181 Γ B) A
 := λ x Var181 vz181 vs181 => vs181 _ _ _ (x Var181 vz181 vs181)

def Tm181 : Con181 → Ty181 → Type 1
 := λ Γ A =>
   ∀ (Tm181  : Con181 → Ty181 → Type)
     (var   : ∀ Γ A     , Var181 Γ A → Tm181 Γ A)
     (lam   : ∀ Γ A B   , Tm181 (snoc181 Γ A) B → Tm181 Γ (arr181 A B))
     (app   : ∀ Γ A B   , Tm181 Γ (arr181 A B) → Tm181 Γ A → Tm181 Γ B)
   , Tm181 Γ A

def var181 {Γ A} : Var181 Γ A → Tm181 Γ A
 := λ x Tm181 var181 lam app =>
     var181 _ _ x

def lam181 {Γ A B} : Tm181 (snoc181 Γ A) B → Tm181 Γ (arr181 A B)
 := λ t Tm181 var181 lam181 app =>
     lam181 _ _ _ (t Tm181 var181 lam181 app)

def app181 {Γ A B} : Tm181 Γ (arr181 A B) → Tm181 Γ A → Tm181 Γ B
 := λ t u Tm181 var181 lam181 app181 =>
     app181 _ _ _
         (t Tm181 var181 lam181 app181)
         (u Tm181 var181 lam181 app181)

def v0181 {Γ A} : Tm181 (snoc181 Γ A) A
 := var181 vz181

def v1181 {Γ A B} : Tm181 (snoc181 (snoc181 Γ A) B) A
 := var181 (vs181 vz181)

def v2181 {Γ A B C} : Tm181 (snoc181 (snoc181 (snoc181 Γ A) B) C) A
 := var181 (vs181 (vs181 vz181))

def v3181 {Γ A B C D} : Tm181 (snoc181 (snoc181 (snoc181 (snoc181 Γ A) B) C) D) A
 := var181 (vs181 (vs181 (vs181 vz181)))

def v4181 {Γ A B C D E} : Tm181 (snoc181 (snoc181 (snoc181 (snoc181 (snoc181 Γ A) B) C) D) E) A
 := var181 (vs181 (vs181 (vs181 (vs181 vz181))))

def test181 {Γ A} : Tm181 Γ (arr181 (arr181 A A) (arr181 A A))
 := lam181 (lam181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 (app181 v1181 v0181)))))))


def Ty182 : Type 1
 := ∀ (Ty182 : Type)
      (ι   : Ty182)
      (arr : Ty182 → Ty182 → Ty182)
    , Ty182

def ι182 : Ty182 := λ _ ι182 _ => ι182

def arr182 : Ty182 → Ty182 → Ty182
 := λ A B Ty182 ι182 arr182 =>
     arr182 (A Ty182 ι182 arr182) (B Ty182 ι182 arr182)

def Con182 : Type 1
 := ∀ (Con182  : Type)
      (nil  : Con182)
      (snoc : Con182 → Ty182 → Con182)
    , Con182

def nil182 : Con182
 := λ Con182 nil182 snoc => nil182

def snoc182 : Con182 → Ty182 → Con182
 := λ Γ A Con182 nil182 snoc182 => snoc182 (Γ Con182 nil182 snoc182) A

def Var182 : Con182 → Ty182 → Type 1
 := λ Γ A =>
   ∀ (Var182 : Con182 → Ty182 → Type)
     (vz  : ∀ Γ A, Var182 (snoc182 Γ A) A)
     (vs  : ∀ Γ B A, Var182 Γ A → Var182 (snoc182 Γ B) A)
   , Var182 Γ A

def vz182 {Γ A} : Var182 (snoc182 Γ A) A
 := λ Var182 vz182 vs => vz182 _ _

def vs182 {Γ B A} : Var182 Γ A → Var182 (snoc182 Γ B) A
 := λ x Var182 vz182 vs182 => vs182 _ _ _ (x Var182 vz182 vs182)

def Tm182 : Con182 → Ty182 → Type 1
 := λ Γ A =>
   ∀ (Tm182  : Con182 → Ty182 → Type)
     (var   : ∀ Γ A     , Var182 Γ A → Tm182 Γ A)
     (lam   : ∀ Γ A B   , Tm182 (snoc182 Γ A) B → Tm182 Γ (arr182 A B))
     (app   : ∀ Γ A B   , Tm182 Γ (arr182 A B) → Tm182 Γ A → Tm182 Γ B)
   , Tm182 Γ A

def var182 {Γ A} : Var182 Γ A → Tm182 Γ A
 := λ x Tm182 var182 lam app =>
     var182 _ _ x

def lam182 {Γ A B} : Tm182 (snoc182 Γ A) B → Tm182 Γ (arr182 A B)
 := λ t Tm182 var182 lam182 app =>
     lam182 _ _ _ (t Tm182 var182 lam182 app)

def app182 {Γ A B} : Tm182 Γ (arr182 A B) → Tm182 Γ A → Tm182 Γ B
 := λ t u Tm182 var182 lam182 app182 =>
     app182 _ _ _
         (t Tm182 var182 lam182 app182)
         (u Tm182 var182 lam182 app182)

def v0182 {Γ A} : Tm182 (snoc182 Γ A) A
 := var182 vz182

def v1182 {Γ A B} : Tm182 (snoc182 (snoc182 Γ A) B) A
 := var182 (vs182 vz182)

def v2182 {Γ A B C} : Tm182 (snoc182 (snoc182 (snoc182 Γ A) B) C) A
 := var182 (vs182 (vs182 vz182))

def v3182 {Γ A B C D} : Tm182 (snoc182 (snoc182 (snoc182 (snoc182 Γ A) B) C) D) A
 := var182 (vs182 (vs182 (vs182 vz182)))

def v4182 {Γ A B C D E} : Tm182 (snoc182 (snoc182 (snoc182 (snoc182 (snoc182 Γ A) B) C) D) E) A
 := var182 (vs182 (vs182 (vs182 (vs182 vz182))))

def test182 {Γ A} : Tm182 Γ (arr182 (arr182 A A) (arr182 A A))
 := lam182 (lam182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 (app182 v1182 v0182)))))))


def Ty183 : Type 1
 := ∀ (Ty183 : Type)
      (ι   : Ty183)
      (arr : Ty183 → Ty183 → Ty183)
    , Ty183

def ι183 : Ty183 := λ _ ι183 _ => ι183

def arr183 : Ty183 → Ty183 → Ty183
 := λ A B Ty183 ι183 arr183 =>
     arr183 (A Ty183 ι183 arr183) (B Ty183 ι183 arr183)

def Con183 : Type 1
 := ∀ (Con183  : Type)
      (nil  : Con183)
      (snoc : Con183 → Ty183 → Con183)
    , Con183

def nil183 : Con183
 := λ Con183 nil183 snoc => nil183

def snoc183 : Con183 → Ty183 → Con183
 := λ Γ A Con183 nil183 snoc183 => snoc183 (Γ Con183 nil183 snoc183) A

def Var183 : Con183 → Ty183 → Type 1
 := λ Γ A =>
   ∀ (Var183 : Con183 → Ty183 → Type)
     (vz  : ∀ Γ A, Var183 (snoc183 Γ A) A)
     (vs  : ∀ Γ B A, Var183 Γ A → Var183 (snoc183 Γ B) A)
   , Var183 Γ A

def vz183 {Γ A} : Var183 (snoc183 Γ A) A
 := λ Var183 vz183 vs => vz183 _ _

def vs183 {Γ B A} : Var183 Γ A → Var183 (snoc183 Γ B) A
 := λ x Var183 vz183 vs183 => vs183 _ _ _ (x Var183 vz183 vs183)

def Tm183 : Con183 → Ty183 → Type 1
 := λ Γ A =>
   ∀ (Tm183  : Con183 → Ty183 → Type)
     (var   : ∀ Γ A     , Var183 Γ A → Tm183 Γ A)
     (lam   : ∀ Γ A B   , Tm183 (snoc183 Γ A) B → Tm183 Γ (arr183 A B))
     (app   : ∀ Γ A B   , Tm183 Γ (arr183 A B) → Tm183 Γ A → Tm183 Γ B)
   , Tm183 Γ A

def var183 {Γ A} : Var183 Γ A → Tm183 Γ A
 := λ x Tm183 var183 lam app =>
     var183 _ _ x

def lam183 {Γ A B} : Tm183 (snoc183 Γ A) B → Tm183 Γ (arr183 A B)
 := λ t Tm183 var183 lam183 app =>
     lam183 _ _ _ (t Tm183 var183 lam183 app)

def app183 {Γ A B} : Tm183 Γ (arr183 A B) → Tm183 Γ A → Tm183 Γ B
 := λ t u Tm183 var183 lam183 app183 =>
     app183 _ _ _
         (t Tm183 var183 lam183 app183)
         (u Tm183 var183 lam183 app183)

def v0183 {Γ A} : Tm183 (snoc183 Γ A) A
 := var183 vz183

def v1183 {Γ A B} : Tm183 (snoc183 (snoc183 Γ A) B) A
 := var183 (vs183 vz183)

def v2183 {Γ A B C} : Tm183 (snoc183 (snoc183 (snoc183 Γ A) B) C) A
 := var183 (vs183 (vs183 vz183))

def v3183 {Γ A B C D} : Tm183 (snoc183 (snoc183 (snoc183 (snoc183 Γ A) B) C) D) A
 := var183 (vs183 (vs183 (vs183 vz183)))

def v4183 {Γ A B C D E} : Tm183 (snoc183 (snoc183 (snoc183 (snoc183 (snoc183 Γ A) B) C) D) E) A
 := var183 (vs183 (vs183 (vs183 (vs183 vz183))))

def test183 {Γ A} : Tm183 Γ (arr183 (arr183 A A) (arr183 A A))
 := lam183 (lam183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 (app183 v1183 v0183)))))))


def Ty184 : Type 1
 := ∀ (Ty184 : Type)
      (ι   : Ty184)
      (arr : Ty184 → Ty184 → Ty184)
    , Ty184

def ι184 : Ty184 := λ _ ι184 _ => ι184

def arr184 : Ty184 → Ty184 → Ty184
 := λ A B Ty184 ι184 arr184 =>
     arr184 (A Ty184 ι184 arr184) (B Ty184 ι184 arr184)

def Con184 : Type 1
 := ∀ (Con184  : Type)
      (nil  : Con184)
      (snoc : Con184 → Ty184 → Con184)
    , Con184

def nil184 : Con184
 := λ Con184 nil184 snoc => nil184

def snoc184 : Con184 → Ty184 → Con184
 := λ Γ A Con184 nil184 snoc184 => snoc184 (Γ Con184 nil184 snoc184) A

def Var184 : Con184 → Ty184 → Type 1
 := λ Γ A =>
   ∀ (Var184 : Con184 → Ty184 → Type)
     (vz  : ∀ Γ A, Var184 (snoc184 Γ A) A)
     (vs  : ∀ Γ B A, Var184 Γ A → Var184 (snoc184 Γ B) A)
   , Var184 Γ A

def vz184 {Γ A} : Var184 (snoc184 Γ A) A
 := λ Var184 vz184 vs => vz184 _ _

def vs184 {Γ B A} : Var184 Γ A → Var184 (snoc184 Γ B) A
 := λ x Var184 vz184 vs184 => vs184 _ _ _ (x Var184 vz184 vs184)

def Tm184 : Con184 → Ty184 → Type 1
 := λ Γ A =>
   ∀ (Tm184  : Con184 → Ty184 → Type)
     (var   : ∀ Γ A     , Var184 Γ A → Tm184 Γ A)
     (lam   : ∀ Γ A B   , Tm184 (snoc184 Γ A) B → Tm184 Γ (arr184 A B))
     (app   : ∀ Γ A B   , Tm184 Γ (arr184 A B) → Tm184 Γ A → Tm184 Γ B)
   , Tm184 Γ A

def var184 {Γ A} : Var184 Γ A → Tm184 Γ A
 := λ x Tm184 var184 lam app =>
     var184 _ _ x

def lam184 {Γ A B} : Tm184 (snoc184 Γ A) B → Tm184 Γ (arr184 A B)
 := λ t Tm184 var184 lam184 app =>
     lam184 _ _ _ (t Tm184 var184 lam184 app)

def app184 {Γ A B} : Tm184 Γ (arr184 A B) → Tm184 Γ A → Tm184 Γ B
 := λ t u Tm184 var184 lam184 app184 =>
     app184 _ _ _
         (t Tm184 var184 lam184 app184)
         (u Tm184 var184 lam184 app184)

def v0184 {Γ A} : Tm184 (snoc184 Γ A) A
 := var184 vz184

def v1184 {Γ A B} : Tm184 (snoc184 (snoc184 Γ A) B) A
 := var184 (vs184 vz184)

def v2184 {Γ A B C} : Tm184 (snoc184 (snoc184 (snoc184 Γ A) B) C) A
 := var184 (vs184 (vs184 vz184))

def v3184 {Γ A B C D} : Tm184 (snoc184 (snoc184 (snoc184 (snoc184 Γ A) B) C) D) A
 := var184 (vs184 (vs184 (vs184 vz184)))

def v4184 {Γ A B C D E} : Tm184 (snoc184 (snoc184 (snoc184 (snoc184 (snoc184 Γ A) B) C) D) E) A
 := var184 (vs184 (vs184 (vs184 (vs184 vz184))))

def test184 {Γ A} : Tm184 Γ (arr184 (arr184 A A) (arr184 A A))
 := lam184 (lam184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 (app184 v1184 v0184)))))))


def Ty185 : Type 1
 := ∀ (Ty185 : Type)
      (ι   : Ty185)
      (arr : Ty185 → Ty185 → Ty185)
    , Ty185

def ι185 : Ty185 := λ _ ι185 _ => ι185

def arr185 : Ty185 → Ty185 → Ty185
 := λ A B Ty185 ι185 arr185 =>
     arr185 (A Ty185 ι185 arr185) (B Ty185 ι185 arr185)

def Con185 : Type 1
 := ∀ (Con185  : Type)
      (nil  : Con185)
      (snoc : Con185 → Ty185 → Con185)
    , Con185

def nil185 : Con185
 := λ Con185 nil185 snoc => nil185

def snoc185 : Con185 → Ty185 → Con185
 := λ Γ A Con185 nil185 snoc185 => snoc185 (Γ Con185 nil185 snoc185) A

def Var185 : Con185 → Ty185 → Type 1
 := λ Γ A =>
   ∀ (Var185 : Con185 → Ty185 → Type)
     (vz  : ∀ Γ A, Var185 (snoc185 Γ A) A)
     (vs  : ∀ Γ B A, Var185 Γ A → Var185 (snoc185 Γ B) A)
   , Var185 Γ A

def vz185 {Γ A} : Var185 (snoc185 Γ A) A
 := λ Var185 vz185 vs => vz185 _ _

def vs185 {Γ B A} : Var185 Γ A → Var185 (snoc185 Γ B) A
 := λ x Var185 vz185 vs185 => vs185 _ _ _ (x Var185 vz185 vs185)

def Tm185 : Con185 → Ty185 → Type 1
 := λ Γ A =>
   ∀ (Tm185  : Con185 → Ty185 → Type)
     (var   : ∀ Γ A     , Var185 Γ A → Tm185 Γ A)
     (lam   : ∀ Γ A B   , Tm185 (snoc185 Γ A) B → Tm185 Γ (arr185 A B))
     (app   : ∀ Γ A B   , Tm185 Γ (arr185 A B) → Tm185 Γ A → Tm185 Γ B)
   , Tm185 Γ A

def var185 {Γ A} : Var185 Γ A → Tm185 Γ A
 := λ x Tm185 var185 lam app =>
     var185 _ _ x

def lam185 {Γ A B} : Tm185 (snoc185 Γ A) B → Tm185 Γ (arr185 A B)
 := λ t Tm185 var185 lam185 app =>
     lam185 _ _ _ (t Tm185 var185 lam185 app)

def app185 {Γ A B} : Tm185 Γ (arr185 A B) → Tm185 Γ A → Tm185 Γ B
 := λ t u Tm185 var185 lam185 app185 =>
     app185 _ _ _
         (t Tm185 var185 lam185 app185)
         (u Tm185 var185 lam185 app185)

def v0185 {Γ A} : Tm185 (snoc185 Γ A) A
 := var185 vz185

def v1185 {Γ A B} : Tm185 (snoc185 (snoc185 Γ A) B) A
 := var185 (vs185 vz185)

def v2185 {Γ A B C} : Tm185 (snoc185 (snoc185 (snoc185 Γ A) B) C) A
 := var185 (vs185 (vs185 vz185))

def v3185 {Γ A B C D} : Tm185 (snoc185 (snoc185 (snoc185 (snoc185 Γ A) B) C) D) A
 := var185 (vs185 (vs185 (vs185 vz185)))

def v4185 {Γ A B C D E} : Tm185 (snoc185 (snoc185 (snoc185 (snoc185 (snoc185 Γ A) B) C) D) E) A
 := var185 (vs185 (vs185 (vs185 (vs185 vz185))))

def test185 {Γ A} : Tm185 Γ (arr185 (arr185 A A) (arr185 A A))
 := lam185 (lam185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 (app185 v1185 v0185)))))))


def Ty186 : Type 1
 := ∀ (Ty186 : Type)
      (ι   : Ty186)
      (arr : Ty186 → Ty186 → Ty186)
    , Ty186

def ι186 : Ty186 := λ _ ι186 _ => ι186

def arr186 : Ty186 → Ty186 → Ty186
 := λ A B Ty186 ι186 arr186 =>
     arr186 (A Ty186 ι186 arr186) (B Ty186 ι186 arr186)

def Con186 : Type 1
 := ∀ (Con186  : Type)
      (nil  : Con186)
      (snoc : Con186 → Ty186 → Con186)
    , Con186

def nil186 : Con186
 := λ Con186 nil186 snoc => nil186

def snoc186 : Con186 → Ty186 → Con186
 := λ Γ A Con186 nil186 snoc186 => snoc186 (Γ Con186 nil186 snoc186) A

def Var186 : Con186 → Ty186 → Type 1
 := λ Γ A =>
   ∀ (Var186 : Con186 → Ty186 → Type)
     (vz  : ∀ Γ A, Var186 (snoc186 Γ A) A)
     (vs  : ∀ Γ B A, Var186 Γ A → Var186 (snoc186 Γ B) A)
   , Var186 Γ A

def vz186 {Γ A} : Var186 (snoc186 Γ A) A
 := λ Var186 vz186 vs => vz186 _ _

def vs186 {Γ B A} : Var186 Γ A → Var186 (snoc186 Γ B) A
 := λ x Var186 vz186 vs186 => vs186 _ _ _ (x Var186 vz186 vs186)

def Tm186 : Con186 → Ty186 → Type 1
 := λ Γ A =>
   ∀ (Tm186  : Con186 → Ty186 → Type)
     (var   : ∀ Γ A     , Var186 Γ A → Tm186 Γ A)
     (lam   : ∀ Γ A B   , Tm186 (snoc186 Γ A) B → Tm186 Γ (arr186 A B))
     (app   : ∀ Γ A B   , Tm186 Γ (arr186 A B) → Tm186 Γ A → Tm186 Γ B)
   , Tm186 Γ A

def var186 {Γ A} : Var186 Γ A → Tm186 Γ A
 := λ x Tm186 var186 lam app =>
     var186 _ _ x

def lam186 {Γ A B} : Tm186 (snoc186 Γ A) B → Tm186 Γ (arr186 A B)
 := λ t Tm186 var186 lam186 app =>
     lam186 _ _ _ (t Tm186 var186 lam186 app)

def app186 {Γ A B} : Tm186 Γ (arr186 A B) → Tm186 Γ A → Tm186 Γ B
 := λ t u Tm186 var186 lam186 app186 =>
     app186 _ _ _
         (t Tm186 var186 lam186 app186)
         (u Tm186 var186 lam186 app186)

def v0186 {Γ A} : Tm186 (snoc186 Γ A) A
 := var186 vz186

def v1186 {Γ A B} : Tm186 (snoc186 (snoc186 Γ A) B) A
 := var186 (vs186 vz186)

def v2186 {Γ A B C} : Tm186 (snoc186 (snoc186 (snoc186 Γ A) B) C) A
 := var186 (vs186 (vs186 vz186))

def v3186 {Γ A B C D} : Tm186 (snoc186 (snoc186 (snoc186 (snoc186 Γ A) B) C) D) A
 := var186 (vs186 (vs186 (vs186 vz186)))

def v4186 {Γ A B C D E} : Tm186 (snoc186 (snoc186 (snoc186 (snoc186 (snoc186 Γ A) B) C) D) E) A
 := var186 (vs186 (vs186 (vs186 (vs186 vz186))))

def test186 {Γ A} : Tm186 Γ (arr186 (arr186 A A) (arr186 A A))
 := lam186 (lam186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 (app186 v1186 v0186)))))))


def Ty187 : Type 1
 := ∀ (Ty187 : Type)
      (ι   : Ty187)
      (arr : Ty187 → Ty187 → Ty187)
    , Ty187

def ι187 : Ty187 := λ _ ι187 _ => ι187

def arr187 : Ty187 → Ty187 → Ty187
 := λ A B Ty187 ι187 arr187 =>
     arr187 (A Ty187 ι187 arr187) (B Ty187 ι187 arr187)

def Con187 : Type 1
 := ∀ (Con187  : Type)
      (nil  : Con187)
      (snoc : Con187 → Ty187 → Con187)
    , Con187

def nil187 : Con187
 := λ Con187 nil187 snoc => nil187

def snoc187 : Con187 → Ty187 → Con187
 := λ Γ A Con187 nil187 snoc187 => snoc187 (Γ Con187 nil187 snoc187) A

def Var187 : Con187 → Ty187 → Type 1
 := λ Γ A =>
   ∀ (Var187 : Con187 → Ty187 → Type)
     (vz  : ∀ Γ A, Var187 (snoc187 Γ A) A)
     (vs  : ∀ Γ B A, Var187 Γ A → Var187 (snoc187 Γ B) A)
   , Var187 Γ A

def vz187 {Γ A} : Var187 (snoc187 Γ A) A
 := λ Var187 vz187 vs => vz187 _ _

def vs187 {Γ B A} : Var187 Γ A → Var187 (snoc187 Γ B) A
 := λ x Var187 vz187 vs187 => vs187 _ _ _ (x Var187 vz187 vs187)

def Tm187 : Con187 → Ty187 → Type 1
 := λ Γ A =>
   ∀ (Tm187  : Con187 → Ty187 → Type)
     (var   : ∀ Γ A     , Var187 Γ A → Tm187 Γ A)
     (lam   : ∀ Γ A B   , Tm187 (snoc187 Γ A) B → Tm187 Γ (arr187 A B))
     (app   : ∀ Γ A B   , Tm187 Γ (arr187 A B) → Tm187 Γ A → Tm187 Γ B)
   , Tm187 Γ A

def var187 {Γ A} : Var187 Γ A → Tm187 Γ A
 := λ x Tm187 var187 lam app =>
     var187 _ _ x

def lam187 {Γ A B} : Tm187 (snoc187 Γ A) B → Tm187 Γ (arr187 A B)
 := λ t Tm187 var187 lam187 app =>
     lam187 _ _ _ (t Tm187 var187 lam187 app)

def app187 {Γ A B} : Tm187 Γ (arr187 A B) → Tm187 Γ A → Tm187 Γ B
 := λ t u Tm187 var187 lam187 app187 =>
     app187 _ _ _
         (t Tm187 var187 lam187 app187)
         (u Tm187 var187 lam187 app187)

def v0187 {Γ A} : Tm187 (snoc187 Γ A) A
 := var187 vz187

def v1187 {Γ A B} : Tm187 (snoc187 (snoc187 Γ A) B) A
 := var187 (vs187 vz187)

def v2187 {Γ A B C} : Tm187 (snoc187 (snoc187 (snoc187 Γ A) B) C) A
 := var187 (vs187 (vs187 vz187))

def v3187 {Γ A B C D} : Tm187 (snoc187 (snoc187 (snoc187 (snoc187 Γ A) B) C) D) A
 := var187 (vs187 (vs187 (vs187 vz187)))

def v4187 {Γ A B C D E} : Tm187 (snoc187 (snoc187 (snoc187 (snoc187 (snoc187 Γ A) B) C) D) E) A
 := var187 (vs187 (vs187 (vs187 (vs187 vz187))))

def test187 {Γ A} : Tm187 Γ (arr187 (arr187 A A) (arr187 A A))
 := lam187 (lam187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 (app187 v1187 v0187)))))))


def Ty188 : Type 1
 := ∀ (Ty188 : Type)
      (ι   : Ty188)
      (arr : Ty188 → Ty188 → Ty188)
    , Ty188

def ι188 : Ty188 := λ _ ι188 _ => ι188

def arr188 : Ty188 → Ty188 → Ty188
 := λ A B Ty188 ι188 arr188 =>
     arr188 (A Ty188 ι188 arr188) (B Ty188 ι188 arr188)

def Con188 : Type 1
 := ∀ (Con188  : Type)
      (nil  : Con188)
      (snoc : Con188 → Ty188 → Con188)
    , Con188

def nil188 : Con188
 := λ Con188 nil188 snoc => nil188

def snoc188 : Con188 → Ty188 → Con188
 := λ Γ A Con188 nil188 snoc188 => snoc188 (Γ Con188 nil188 snoc188) A

def Var188 : Con188 → Ty188 → Type 1
 := λ Γ A =>
   ∀ (Var188 : Con188 → Ty188 → Type)
     (vz  : ∀ Γ A, Var188 (snoc188 Γ A) A)
     (vs  : ∀ Γ B A, Var188 Γ A → Var188 (snoc188 Γ B) A)
   , Var188 Γ A

def vz188 {Γ A} : Var188 (snoc188 Γ A) A
 := λ Var188 vz188 vs => vz188 _ _

def vs188 {Γ B A} : Var188 Γ A → Var188 (snoc188 Γ B) A
 := λ x Var188 vz188 vs188 => vs188 _ _ _ (x Var188 vz188 vs188)

def Tm188 : Con188 → Ty188 → Type 1
 := λ Γ A =>
   ∀ (Tm188  : Con188 → Ty188 → Type)
     (var   : ∀ Γ A     , Var188 Γ A → Tm188 Γ A)
     (lam   : ∀ Γ A B   , Tm188 (snoc188 Γ A) B → Tm188 Γ (arr188 A B))
     (app   : ∀ Γ A B   , Tm188 Γ (arr188 A B) → Tm188 Γ A → Tm188 Γ B)
   , Tm188 Γ A

def var188 {Γ A} : Var188 Γ A → Tm188 Γ A
 := λ x Tm188 var188 lam app =>
     var188 _ _ x

def lam188 {Γ A B} : Tm188 (snoc188 Γ A) B → Tm188 Γ (arr188 A B)
 := λ t Tm188 var188 lam188 app =>
     lam188 _ _ _ (t Tm188 var188 lam188 app)

def app188 {Γ A B} : Tm188 Γ (arr188 A B) → Tm188 Γ A → Tm188 Γ B
 := λ t u Tm188 var188 lam188 app188 =>
     app188 _ _ _
         (t Tm188 var188 lam188 app188)
         (u Tm188 var188 lam188 app188)

def v0188 {Γ A} : Tm188 (snoc188 Γ A) A
 := var188 vz188

def v1188 {Γ A B} : Tm188 (snoc188 (snoc188 Γ A) B) A
 := var188 (vs188 vz188)

def v2188 {Γ A B C} : Tm188 (snoc188 (snoc188 (snoc188 Γ A) B) C) A
 := var188 (vs188 (vs188 vz188))

def v3188 {Γ A B C D} : Tm188 (snoc188 (snoc188 (snoc188 (snoc188 Γ A) B) C) D) A
 := var188 (vs188 (vs188 (vs188 vz188)))

def v4188 {Γ A B C D E} : Tm188 (snoc188 (snoc188 (snoc188 (snoc188 (snoc188 Γ A) B) C) D) E) A
 := var188 (vs188 (vs188 (vs188 (vs188 vz188))))

def test188 {Γ A} : Tm188 Γ (arr188 (arr188 A A) (arr188 A A))
 := lam188 (lam188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 (app188 v1188 v0188)))))))


def Ty189 : Type 1
 := ∀ (Ty189 : Type)
      (ι   : Ty189)
      (arr : Ty189 → Ty189 → Ty189)
    , Ty189

def ι189 : Ty189 := λ _ ι189 _ => ι189

def arr189 : Ty189 → Ty189 → Ty189
 := λ A B Ty189 ι189 arr189 =>
     arr189 (A Ty189 ι189 arr189) (B Ty189 ι189 arr189)

def Con189 : Type 1
 := ∀ (Con189  : Type)
      (nil  : Con189)
      (snoc : Con189 → Ty189 → Con189)
    , Con189

def nil189 : Con189
 := λ Con189 nil189 snoc => nil189

def snoc189 : Con189 → Ty189 → Con189
 := λ Γ A Con189 nil189 snoc189 => snoc189 (Γ Con189 nil189 snoc189) A

def Var189 : Con189 → Ty189 → Type 1
 := λ Γ A =>
   ∀ (Var189 : Con189 → Ty189 → Type)
     (vz  : ∀ Γ A, Var189 (snoc189 Γ A) A)
     (vs  : ∀ Γ B A, Var189 Γ A → Var189 (snoc189 Γ B) A)
   , Var189 Γ A

def vz189 {Γ A} : Var189 (snoc189 Γ A) A
 := λ Var189 vz189 vs => vz189 _ _

def vs189 {Γ B A} : Var189 Γ A → Var189 (snoc189 Γ B) A
 := λ x Var189 vz189 vs189 => vs189 _ _ _ (x Var189 vz189 vs189)

def Tm189 : Con189 → Ty189 → Type 1
 := λ Γ A =>
   ∀ (Tm189  : Con189 → Ty189 → Type)
     (var   : ∀ Γ A     , Var189 Γ A → Tm189 Γ A)
     (lam   : ∀ Γ A B   , Tm189 (snoc189 Γ A) B → Tm189 Γ (arr189 A B))
     (app   : ∀ Γ A B   , Tm189 Γ (arr189 A B) → Tm189 Γ A → Tm189 Γ B)
   , Tm189 Γ A

def var189 {Γ A} : Var189 Γ A → Tm189 Γ A
 := λ x Tm189 var189 lam app =>
     var189 _ _ x

def lam189 {Γ A B} : Tm189 (snoc189 Γ A) B → Tm189 Γ (arr189 A B)
 := λ t Tm189 var189 lam189 app =>
     lam189 _ _ _ (t Tm189 var189 lam189 app)

def app189 {Γ A B} : Tm189 Γ (arr189 A B) → Tm189 Γ A → Tm189 Γ B
 := λ t u Tm189 var189 lam189 app189 =>
     app189 _ _ _
         (t Tm189 var189 lam189 app189)
         (u Tm189 var189 lam189 app189)

def v0189 {Γ A} : Tm189 (snoc189 Γ A) A
 := var189 vz189

def v1189 {Γ A B} : Tm189 (snoc189 (snoc189 Γ A) B) A
 := var189 (vs189 vz189)

def v2189 {Γ A B C} : Tm189 (snoc189 (snoc189 (snoc189 Γ A) B) C) A
 := var189 (vs189 (vs189 vz189))

def v3189 {Γ A B C D} : Tm189 (snoc189 (snoc189 (snoc189 (snoc189 Γ A) B) C) D) A
 := var189 (vs189 (vs189 (vs189 vz189)))

def v4189 {Γ A B C D E} : Tm189 (snoc189 (snoc189 (snoc189 (snoc189 (snoc189 Γ A) B) C) D) E) A
 := var189 (vs189 (vs189 (vs189 (vs189 vz189))))

def test189 {Γ A} : Tm189 Γ (arr189 (arr189 A A) (arr189 A A))
 := lam189 (lam189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 (app189 v1189 v0189)))))))


def Ty190 : Type 1
 := ∀ (Ty190 : Type)
      (ι   : Ty190)
      (arr : Ty190 → Ty190 → Ty190)
    , Ty190

def ι190 : Ty190 := λ _ ι190 _ => ι190

def arr190 : Ty190 → Ty190 → Ty190
 := λ A B Ty190 ι190 arr190 =>
     arr190 (A Ty190 ι190 arr190) (B Ty190 ι190 arr190)

def Con190 : Type 1
 := ∀ (Con190  : Type)
      (nil  : Con190)
      (snoc : Con190 → Ty190 → Con190)
    , Con190

def nil190 : Con190
 := λ Con190 nil190 snoc => nil190

def snoc190 : Con190 → Ty190 → Con190
 := λ Γ A Con190 nil190 snoc190 => snoc190 (Γ Con190 nil190 snoc190) A

def Var190 : Con190 → Ty190 → Type 1
 := λ Γ A =>
   ∀ (Var190 : Con190 → Ty190 → Type)
     (vz  : ∀ Γ A, Var190 (snoc190 Γ A) A)
     (vs  : ∀ Γ B A, Var190 Γ A → Var190 (snoc190 Γ B) A)
   , Var190 Γ A

def vz190 {Γ A} : Var190 (snoc190 Γ A) A
 := λ Var190 vz190 vs => vz190 _ _

def vs190 {Γ B A} : Var190 Γ A → Var190 (snoc190 Γ B) A
 := λ x Var190 vz190 vs190 => vs190 _ _ _ (x Var190 vz190 vs190)

def Tm190 : Con190 → Ty190 → Type 1
 := λ Γ A =>
   ∀ (Tm190  : Con190 → Ty190 → Type)
     (var   : ∀ Γ A     , Var190 Γ A → Tm190 Γ A)
     (lam   : ∀ Γ A B   , Tm190 (snoc190 Γ A) B → Tm190 Γ (arr190 A B))
     (app   : ∀ Γ A B   , Tm190 Γ (arr190 A B) → Tm190 Γ A → Tm190 Γ B)
   , Tm190 Γ A

def var190 {Γ A} : Var190 Γ A → Tm190 Γ A
 := λ x Tm190 var190 lam app =>
     var190 _ _ x

def lam190 {Γ A B} : Tm190 (snoc190 Γ A) B → Tm190 Γ (arr190 A B)
 := λ t Tm190 var190 lam190 app =>
     lam190 _ _ _ (t Tm190 var190 lam190 app)

def app190 {Γ A B} : Tm190 Γ (arr190 A B) → Tm190 Γ A → Tm190 Γ B
 := λ t u Tm190 var190 lam190 app190 =>
     app190 _ _ _
         (t Tm190 var190 lam190 app190)
         (u Tm190 var190 lam190 app190)

def v0190 {Γ A} : Tm190 (snoc190 Γ A) A
 := var190 vz190

def v1190 {Γ A B} : Tm190 (snoc190 (snoc190 Γ A) B) A
 := var190 (vs190 vz190)

def v2190 {Γ A B C} : Tm190 (snoc190 (snoc190 (snoc190 Γ A) B) C) A
 := var190 (vs190 (vs190 vz190))

def v3190 {Γ A B C D} : Tm190 (snoc190 (snoc190 (snoc190 (snoc190 Γ A) B) C) D) A
 := var190 (vs190 (vs190 (vs190 vz190)))

def v4190 {Γ A B C D E} : Tm190 (snoc190 (snoc190 (snoc190 (snoc190 (snoc190 Γ A) B) C) D) E) A
 := var190 (vs190 (vs190 (vs190 (vs190 vz190))))

def test190 {Γ A} : Tm190 Γ (arr190 (arr190 A A) (arr190 A A))
 := lam190 (lam190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 (app190 v1190 v0190)))))))


def Ty191 : Type 1
 := ∀ (Ty191 : Type)
      (ι   : Ty191)
      (arr : Ty191 → Ty191 → Ty191)
    , Ty191

def ι191 : Ty191 := λ _ ι191 _ => ι191

def arr191 : Ty191 → Ty191 → Ty191
 := λ A B Ty191 ι191 arr191 =>
     arr191 (A Ty191 ι191 arr191) (B Ty191 ι191 arr191)

def Con191 : Type 1
 := ∀ (Con191  : Type)
      (nil  : Con191)
      (snoc : Con191 → Ty191 → Con191)
    , Con191

def nil191 : Con191
 := λ Con191 nil191 snoc => nil191

def snoc191 : Con191 → Ty191 → Con191
 := λ Γ A Con191 nil191 snoc191 => snoc191 (Γ Con191 nil191 snoc191) A

def Var191 : Con191 → Ty191 → Type 1
 := λ Γ A =>
   ∀ (Var191 : Con191 → Ty191 → Type)
     (vz  : ∀ Γ A, Var191 (snoc191 Γ A) A)
     (vs  : ∀ Γ B A, Var191 Γ A → Var191 (snoc191 Γ B) A)
   , Var191 Γ A

def vz191 {Γ A} : Var191 (snoc191 Γ A) A
 := λ Var191 vz191 vs => vz191 _ _

def vs191 {Γ B A} : Var191 Γ A → Var191 (snoc191 Γ B) A
 := λ x Var191 vz191 vs191 => vs191 _ _ _ (x Var191 vz191 vs191)

def Tm191 : Con191 → Ty191 → Type 1
 := λ Γ A =>
   ∀ (Tm191  : Con191 → Ty191 → Type)
     (var   : ∀ Γ A     , Var191 Γ A → Tm191 Γ A)
     (lam   : ∀ Γ A B   , Tm191 (snoc191 Γ A) B → Tm191 Γ (arr191 A B))
     (app   : ∀ Γ A B   , Tm191 Γ (arr191 A B) → Tm191 Γ A → Tm191 Γ B)
   , Tm191 Γ A

def var191 {Γ A} : Var191 Γ A → Tm191 Γ A
 := λ x Tm191 var191 lam app =>
     var191 _ _ x

def lam191 {Γ A B} : Tm191 (snoc191 Γ A) B → Tm191 Γ (arr191 A B)
 := λ t Tm191 var191 lam191 app =>
     lam191 _ _ _ (t Tm191 var191 lam191 app)

def app191 {Γ A B} : Tm191 Γ (arr191 A B) → Tm191 Γ A → Tm191 Γ B
 := λ t u Tm191 var191 lam191 app191 =>
     app191 _ _ _
         (t Tm191 var191 lam191 app191)
         (u Tm191 var191 lam191 app191)

def v0191 {Γ A} : Tm191 (snoc191 Γ A) A
 := var191 vz191

def v1191 {Γ A B} : Tm191 (snoc191 (snoc191 Γ A) B) A
 := var191 (vs191 vz191)

def v2191 {Γ A B C} : Tm191 (snoc191 (snoc191 (snoc191 Γ A) B) C) A
 := var191 (vs191 (vs191 vz191))

def v3191 {Γ A B C D} : Tm191 (snoc191 (snoc191 (snoc191 (snoc191 Γ A) B) C) D) A
 := var191 (vs191 (vs191 (vs191 vz191)))

def v4191 {Γ A B C D E} : Tm191 (snoc191 (snoc191 (snoc191 (snoc191 (snoc191 Γ A) B) C) D) E) A
 := var191 (vs191 (vs191 (vs191 (vs191 vz191))))

def test191 {Γ A} : Tm191 Γ (arr191 (arr191 A A) (arr191 A A))
 := lam191 (lam191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 (app191 v1191 v0191)))))))

