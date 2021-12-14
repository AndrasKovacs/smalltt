
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

