Ty : Type
Ty = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty : Ty
empty = \ _, empty, _ => empty

arr : Ty -> Ty -> Ty
arr = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con : Type
Con = (Con : Type)
 ->(nil  : Con)
 ->(snoc : Con -> Ty -> Con)
 -> Con

nil : Con
nil = \ con, nil, snoc => nil

snoc : Con -> Ty -> Con
snoc = \ g, a, con, nil, snoc => snoc (g con nil snoc) a

Var : Con -> Ty -> Type
Var = \ g, a =>
    (Var : Con -> Ty -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var (snoc g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var g a -> Var (snoc g b) a)
 -> Var g a

vz : {g : _}-> {a : _} -> Var (snoc g a) a
vz = \ var, vz, vs => vz _ _

vs : {g : _} -> {B : _} -> {a : _} -> Var g a -> Var (snoc g B) a
vs = \ x, var, vz, vs => vs _ _ _ (x var vz vs)

Tm : Con -> Ty -> Type
Tm = \ g, a =>
    (Tm    : Con -> Ty -> Type)
 -> (var   : (g : _) -> (a : _) -> Var g a -> Tm g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm (snoc g a) B -> Tm g (arr a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm g (arr a B) -> Tm g a -> Tm g B)
 -> Tm g a

var : {g : _} -> {a : _} -> Var g a -> Tm g a
var = \ x, tm, var, lam, app => var _ _ x

lam : {g : _} -> {a : _} -> {B : _} -> Tm (snoc g a) B -> Tm g (arr a B)
lam = \ t, tm, var, lam, app => lam _ _ _ (t tm var lam app)

app : {g:_}->{a:_}->{B:_} -> Tm g (arr a B) -> Tm g a -> Tm g B
app = \ t, u, tm, var, lam, app => app _ _ _ (t tm var lam app) (u tm var lam app)

v0 : {g:_}->{a:_} -> Tm (snoc g a) a
v0 = var vz

v1 : {g:_}->{a:_}-> {B:_}-> Tm (snoc (snoc g a) B) a
v1 = var (vs vz)

v2 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm (snoc (snoc (snoc g a) B) C) a
v2 = var (vs (vs vz))

v3 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm (snoc (snoc (snoc (snoc g a) B) C) D) a
v3 = var (vs (vs (vs vz)))

v4 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm (snoc (snoc (snoc (snoc (snoc g a) B) C) D) E) a
v4 = var (vs (vs (vs (vs vz))))

test : {g:_}-> {a:_} -> Tm g (arr (arr a a) (arr a a))
test  = lam (lam (app v1 (app v1 (app v1 (app v1 (app v1 (app v1 v0)))))))
Ty1 : Type
Ty1 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty1 : Ty1
empty1 = \ _, empty, _ => empty

arr1 : Ty1 -> Ty1 -> Ty1
arr1 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con1 : Type
Con1 = (Con1 : Type)
 ->(nil  : Con1)
 ->(snoc : Con1 -> Ty1 -> Con1)
 -> Con1

nil1 : Con1
nil1 = \ con, nil1, snoc => nil1

snoc1 : Con1 -> Ty1 -> Con1
snoc1 = \ g, a, con, nil1, snoc1 => snoc1 (g con nil1 snoc1) a

Var1 : Con1 -> Ty1 -> Type
Var1 = \ g, a =>
    (Var1 : Con1 -> Ty1 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var1 (snoc1 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var1 g a -> Var1 (snoc1 g b) a)
 -> Var1 g a

vz1 : {g : _}-> {a : _} -> Var1 (snoc1 g a) a
vz1 = \ var, vz1, vs => vz1 _ _

vs1 : {g : _} -> {B : _} -> {a : _} -> Var1 g a -> Var1 (snoc1 g B) a
vs1 = \ x, var, vz1, vs1 => vs1 _ _ _ (x var vz1 vs1)

Tm1 : Con1 -> Ty1 -> Type
Tm1 = \ g, a =>
    (Tm1    : Con1 -> Ty1 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var1 g a -> Tm1 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm1 (snoc1 g a) B -> Tm1 g (arr1 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm1 g (arr1 a B) -> Tm1 g a -> Tm1 g B)
 -> Tm1 g a

var1 : {g : _} -> {a : _} -> Var1 g a -> Tm1 g a
var1 = \ x, tm, var1, lam, app => var1 _ _ x

lam1 : {g : _} -> {a : _} -> {B : _} -> Tm1 (snoc1 g a) B -> Tm1 g (arr1 a B)
lam1 = \ t, tm, var1, lam1, app => lam1 _ _ _ (t tm var1 lam1 app)

app1 : {g:_}->{a:_}->{B:_} -> Tm1 g (arr1 a B) -> Tm1 g a -> Tm1 g B
app1 = \ t, u, tm, var1, lam1, app1 => app1 _ _ _ (t tm var1 lam1 app1) (u tm var1 lam1 app1)

v01 : {g:_}->{a:_} -> Tm1 (snoc1 g a) a
v01 = var1 vz1

v11 : {g:_}->{a:_}-> {B:_}-> Tm1 (snoc1 (snoc1 g a) B) a
v11 = var1 (vs1 vz1)

v21 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm1 (snoc1 (snoc1 (snoc1 g a) B) C) a
v21 = var1 (vs1 (vs1 vz1))

v31 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm1 (snoc1 (snoc1 (snoc1 (snoc1 g a) B) C) D) a
v31 = var1 (vs1 (vs1 (vs1 vz1)))

v41 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm1 (snoc1 (snoc1 (snoc1 (snoc1 (snoc1 g a) B) C) D) E) a
v41 = var1 (vs1 (vs1 (vs1 (vs1 vz1))))

test1 : {g:_}-> {a:_} -> Tm1 g (arr1 (arr1 a a) (arr1 a a))
test1  = lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01)))))))
Ty2 : Type
Ty2 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty2 : Ty2
empty2 = \ _, empty, _ => empty

arr2 : Ty2 -> Ty2 -> Ty2
arr2 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con2 : Type
Con2 = (Con2 : Type)
 ->(nil  : Con2)
 ->(snoc : Con2 -> Ty2 -> Con2)
 -> Con2

nil2 : Con2
nil2 = \ con, nil2, snoc => nil2

snoc2 : Con2 -> Ty2 -> Con2
snoc2 = \ g, a, con, nil2, snoc2 => snoc2 (g con nil2 snoc2) a

Var2 : Con2 -> Ty2 -> Type
Var2 = \ g, a =>
    (Var2 : Con2 -> Ty2 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var2 (snoc2 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var2 g a -> Var2 (snoc2 g b) a)
 -> Var2 g a

vz2 : {g : _}-> {a : _} -> Var2 (snoc2 g a) a
vz2 = \ var, vz2, vs => vz2 _ _

vs2 : {g : _} -> {B : _} -> {a : _} -> Var2 g a -> Var2 (snoc2 g B) a
vs2 = \ x, var, vz2, vs2 => vs2 _ _ _ (x var vz2 vs2)

Tm2 : Con2 -> Ty2 -> Type
Tm2 = \ g, a =>
    (Tm2    : Con2 -> Ty2 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var2 g a -> Tm2 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm2 (snoc2 g a) B -> Tm2 g (arr2 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm2 g (arr2 a B) -> Tm2 g a -> Tm2 g B)
 -> Tm2 g a

var2 : {g : _} -> {a : _} -> Var2 g a -> Tm2 g a
var2 = \ x, tm, var2, lam, app => var2 _ _ x

lam2 : {g : _} -> {a : _} -> {B : _} -> Tm2 (snoc2 g a) B -> Tm2 g (arr2 a B)
lam2 = \ t, tm, var2, lam2, app => lam2 _ _ _ (t tm var2 lam2 app)

app2 : {g:_}->{a:_}->{B:_} -> Tm2 g (arr2 a B) -> Tm2 g a -> Tm2 g B
app2 = \ t, u, tm, var2, lam2, app2 => app2 _ _ _ (t tm var2 lam2 app2) (u tm var2 lam2 app2)

v02 : {g:_}->{a:_} -> Tm2 (snoc2 g a) a
v02 = var2 vz2

v12 : {g:_}->{a:_}-> {B:_}-> Tm2 (snoc2 (snoc2 g a) B) a
v12 = var2 (vs2 vz2)

v22 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm2 (snoc2 (snoc2 (snoc2 g a) B) C) a
v22 = var2 (vs2 (vs2 vz2))

v32 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm2 (snoc2 (snoc2 (snoc2 (snoc2 g a) B) C) D) a
v32 = var2 (vs2 (vs2 (vs2 vz2)))

v42 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm2 (snoc2 (snoc2 (snoc2 (snoc2 (snoc2 g a) B) C) D) E) a
v42 = var2 (vs2 (vs2 (vs2 (vs2 vz2))))

test2 : {g:_}-> {a:_} -> Tm2 g (arr2 (arr2 a a) (arr2 a a))
test2  = lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02)))))))
Ty3 : Type
Ty3 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty3 : Ty3
empty3 = \ _, empty, _ => empty

arr3 : Ty3 -> Ty3 -> Ty3
arr3 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con3 : Type
Con3 = (Con3 : Type)
 ->(nil  : Con3)
 ->(snoc : Con3 -> Ty3 -> Con3)
 -> Con3

nil3 : Con3
nil3 = \ con, nil3, snoc => nil3

snoc3 : Con3 -> Ty3 -> Con3
snoc3 = \ g, a, con, nil3, snoc3 => snoc3 (g con nil3 snoc3) a

Var3 : Con3 -> Ty3 -> Type
Var3 = \ g, a =>
    (Var3 : Con3 -> Ty3 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var3 (snoc3 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var3 g a -> Var3 (snoc3 g b) a)
 -> Var3 g a

vz3 : {g : _}-> {a : _} -> Var3 (snoc3 g a) a
vz3 = \ var, vz3, vs => vz3 _ _

vs3 : {g : _} -> {B : _} -> {a : _} -> Var3 g a -> Var3 (snoc3 g B) a
vs3 = \ x, var, vz3, vs3 => vs3 _ _ _ (x var vz3 vs3)

Tm3 : Con3 -> Ty3 -> Type
Tm3 = \ g, a =>
    (Tm3    : Con3 -> Ty3 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var3 g a -> Tm3 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm3 (snoc3 g a) B -> Tm3 g (arr3 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm3 g (arr3 a B) -> Tm3 g a -> Tm3 g B)
 -> Tm3 g a

var3 : {g : _} -> {a : _} -> Var3 g a -> Tm3 g a
var3 = \ x, tm, var3, lam, app => var3 _ _ x

lam3 : {g : _} -> {a : _} -> {B : _} -> Tm3 (snoc3 g a) B -> Tm3 g (arr3 a B)
lam3 = \ t, tm, var3, lam3, app => lam3 _ _ _ (t tm var3 lam3 app)

app3 : {g:_}->{a:_}->{B:_} -> Tm3 g (arr3 a B) -> Tm3 g a -> Tm3 g B
app3 = \ t, u, tm, var3, lam3, app3 => app3 _ _ _ (t tm var3 lam3 app3) (u tm var3 lam3 app3)

v03 : {g:_}->{a:_} -> Tm3 (snoc3 g a) a
v03 = var3 vz3

v13 : {g:_}->{a:_}-> {B:_}-> Tm3 (snoc3 (snoc3 g a) B) a
v13 = var3 (vs3 vz3)

v23 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm3 (snoc3 (snoc3 (snoc3 g a) B) C) a
v23 = var3 (vs3 (vs3 vz3))

v33 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm3 (snoc3 (snoc3 (snoc3 (snoc3 g a) B) C) D) a
v33 = var3 (vs3 (vs3 (vs3 vz3)))

v43 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm3 (snoc3 (snoc3 (snoc3 (snoc3 (snoc3 g a) B) C) D) E) a
v43 = var3 (vs3 (vs3 (vs3 (vs3 vz3))))

test3 : {g:_}-> {a:_} -> Tm3 g (arr3 (arr3 a a) (arr3 a a))
test3  = lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03)))))))
Ty4 : Type
Ty4 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty4 : Ty4
empty4 = \ _, empty, _ => empty

arr4 : Ty4 -> Ty4 -> Ty4
arr4 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con4 : Type
Con4 = (Con4 : Type)
 ->(nil  : Con4)
 ->(snoc : Con4 -> Ty4 -> Con4)
 -> Con4

nil4 : Con4
nil4 = \ con, nil4, snoc => nil4

snoc4 : Con4 -> Ty4 -> Con4
snoc4 = \ g, a, con, nil4, snoc4 => snoc4 (g con nil4 snoc4) a

Var4 : Con4 -> Ty4 -> Type
Var4 = \ g, a =>
    (Var4 : Con4 -> Ty4 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var4 (snoc4 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var4 g a -> Var4 (snoc4 g b) a)
 -> Var4 g a

vz4 : {g : _}-> {a : _} -> Var4 (snoc4 g a) a
vz4 = \ var, vz4, vs => vz4 _ _

vs4 : {g : _} -> {B : _} -> {a : _} -> Var4 g a -> Var4 (snoc4 g B) a
vs4 = \ x, var, vz4, vs4 => vs4 _ _ _ (x var vz4 vs4)

Tm4 : Con4 -> Ty4 -> Type
Tm4 = \ g, a =>
    (Tm4    : Con4 -> Ty4 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var4 g a -> Tm4 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm4 (snoc4 g a) B -> Tm4 g (arr4 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm4 g (arr4 a B) -> Tm4 g a -> Tm4 g B)
 -> Tm4 g a

var4 : {g : _} -> {a : _} -> Var4 g a -> Tm4 g a
var4 = \ x, tm, var4, lam, app => var4 _ _ x

lam4 : {g : _} -> {a : _} -> {B : _} -> Tm4 (snoc4 g a) B -> Tm4 g (arr4 a B)
lam4 = \ t, tm, var4, lam4, app => lam4 _ _ _ (t tm var4 lam4 app)

app4 : {g:_}->{a:_}->{B:_} -> Tm4 g (arr4 a B) -> Tm4 g a -> Tm4 g B
app4 = \ t, u, tm, var4, lam4, app4 => app4 _ _ _ (t tm var4 lam4 app4) (u tm var4 lam4 app4)

v04 : {g:_}->{a:_} -> Tm4 (snoc4 g a) a
v04 = var4 vz4

v14 : {g:_}->{a:_}-> {B:_}-> Tm4 (snoc4 (snoc4 g a) B) a
v14 = var4 (vs4 vz4)

v24 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm4 (snoc4 (snoc4 (snoc4 g a) B) C) a
v24 = var4 (vs4 (vs4 vz4))

v34 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm4 (snoc4 (snoc4 (snoc4 (snoc4 g a) B) C) D) a
v34 = var4 (vs4 (vs4 (vs4 vz4)))

v44 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm4 (snoc4 (snoc4 (snoc4 (snoc4 (snoc4 g a) B) C) D) E) a
v44 = var4 (vs4 (vs4 (vs4 (vs4 vz4))))

test4 : {g:_}-> {a:_} -> Tm4 g (arr4 (arr4 a a) (arr4 a a))
test4  = lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04)))))))
Ty5 : Type
Ty5 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty5 : Ty5
empty5 = \ _, empty, _ => empty

arr5 : Ty5 -> Ty5 -> Ty5
arr5 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con5 : Type
Con5 = (Con5 : Type)
 ->(nil  : Con5)
 ->(snoc : Con5 -> Ty5 -> Con5)
 -> Con5

nil5 : Con5
nil5 = \ con, nil5, snoc => nil5

snoc5 : Con5 -> Ty5 -> Con5
snoc5 = \ g, a, con, nil5, snoc5 => snoc5 (g con nil5 snoc5) a

Var5 : Con5 -> Ty5 -> Type
Var5 = \ g, a =>
    (Var5 : Con5 -> Ty5 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var5 (snoc5 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var5 g a -> Var5 (snoc5 g b) a)
 -> Var5 g a

vz5 : {g : _}-> {a : _} -> Var5 (snoc5 g a) a
vz5 = \ var, vz5, vs => vz5 _ _

vs5 : {g : _} -> {B : _} -> {a : _} -> Var5 g a -> Var5 (snoc5 g B) a
vs5 = \ x, var, vz5, vs5 => vs5 _ _ _ (x var vz5 vs5)

Tm5 : Con5 -> Ty5 -> Type
Tm5 = \ g, a =>
    (Tm5    : Con5 -> Ty5 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var5 g a -> Tm5 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm5 (snoc5 g a) B -> Tm5 g (arr5 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm5 g (arr5 a B) -> Tm5 g a -> Tm5 g B)
 -> Tm5 g a

var5 : {g : _} -> {a : _} -> Var5 g a -> Tm5 g a
var5 = \ x, tm, var5, lam, app => var5 _ _ x

lam5 : {g : _} -> {a : _} -> {B : _} -> Tm5 (snoc5 g a) B -> Tm5 g (arr5 a B)
lam5 = \ t, tm, var5, lam5, app => lam5 _ _ _ (t tm var5 lam5 app)

app5 : {g:_}->{a:_}->{B:_} -> Tm5 g (arr5 a B) -> Tm5 g a -> Tm5 g B
app5 = \ t, u, tm, var5, lam5, app5 => app5 _ _ _ (t tm var5 lam5 app5) (u tm var5 lam5 app5)

v05 : {g:_}->{a:_} -> Tm5 (snoc5 g a) a
v05 = var5 vz5

v15 : {g:_}->{a:_}-> {B:_}-> Tm5 (snoc5 (snoc5 g a) B) a
v15 = var5 (vs5 vz5)

v25 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm5 (snoc5 (snoc5 (snoc5 g a) B) C) a
v25 = var5 (vs5 (vs5 vz5))

v35 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm5 (snoc5 (snoc5 (snoc5 (snoc5 g a) B) C) D) a
v35 = var5 (vs5 (vs5 (vs5 vz5)))

v45 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm5 (snoc5 (snoc5 (snoc5 (snoc5 (snoc5 g a) B) C) D) E) a
v45 = var5 (vs5 (vs5 (vs5 (vs5 vz5))))

test5 : {g:_}-> {a:_} -> Tm5 g (arr5 (arr5 a a) (arr5 a a))
test5  = lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05)))))))
Ty6 : Type
Ty6 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty6 : Ty6
empty6 = \ _, empty, _ => empty

arr6 : Ty6 -> Ty6 -> Ty6
arr6 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con6 : Type
Con6 = (Con6 : Type)
 ->(nil  : Con6)
 ->(snoc : Con6 -> Ty6 -> Con6)
 -> Con6

nil6 : Con6
nil6 = \ con, nil6, snoc => nil6

snoc6 : Con6 -> Ty6 -> Con6
snoc6 = \ g, a, con, nil6, snoc6 => snoc6 (g con nil6 snoc6) a

Var6 : Con6 -> Ty6 -> Type
Var6 = \ g, a =>
    (Var6 : Con6 -> Ty6 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var6 (snoc6 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var6 g a -> Var6 (snoc6 g b) a)
 -> Var6 g a

vz6 : {g : _}-> {a : _} -> Var6 (snoc6 g a) a
vz6 = \ var, vz6, vs => vz6 _ _

vs6 : {g : _} -> {B : _} -> {a : _} -> Var6 g a -> Var6 (snoc6 g B) a
vs6 = \ x, var, vz6, vs6 => vs6 _ _ _ (x var vz6 vs6)

Tm6 : Con6 -> Ty6 -> Type
Tm6 = \ g, a =>
    (Tm6    : Con6 -> Ty6 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var6 g a -> Tm6 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm6 (snoc6 g a) B -> Tm6 g (arr6 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm6 g (arr6 a B) -> Tm6 g a -> Tm6 g B)
 -> Tm6 g a

var6 : {g : _} -> {a : _} -> Var6 g a -> Tm6 g a
var6 = \ x, tm, var6, lam, app => var6 _ _ x

lam6 : {g : _} -> {a : _} -> {B : _} -> Tm6 (snoc6 g a) B -> Tm6 g (arr6 a B)
lam6 = \ t, tm, var6, lam6, app => lam6 _ _ _ (t tm var6 lam6 app)

app6 : {g:_}->{a:_}->{B:_} -> Tm6 g (arr6 a B) -> Tm6 g a -> Tm6 g B
app6 = \ t, u, tm, var6, lam6, app6 => app6 _ _ _ (t tm var6 lam6 app6) (u tm var6 lam6 app6)

v06 : {g:_}->{a:_} -> Tm6 (snoc6 g a) a
v06 = var6 vz6

v16 : {g:_}->{a:_}-> {B:_}-> Tm6 (snoc6 (snoc6 g a) B) a
v16 = var6 (vs6 vz6)

v26 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm6 (snoc6 (snoc6 (snoc6 g a) B) C) a
v26 = var6 (vs6 (vs6 vz6))

v36 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm6 (snoc6 (snoc6 (snoc6 (snoc6 g a) B) C) D) a
v36 = var6 (vs6 (vs6 (vs6 vz6)))

v46 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm6 (snoc6 (snoc6 (snoc6 (snoc6 (snoc6 g a) B) C) D) E) a
v46 = var6 (vs6 (vs6 (vs6 (vs6 vz6))))

test6 : {g:_}-> {a:_} -> Tm6 g (arr6 (arr6 a a) (arr6 a a))
test6  = lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06)))))))
Ty7 : Type
Ty7 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty7 : Ty7
empty7 = \ _, empty, _ => empty

arr7 : Ty7 -> Ty7 -> Ty7
arr7 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con7 : Type
Con7 = (Con7 : Type)
 ->(nil  : Con7)
 ->(snoc : Con7 -> Ty7 -> Con7)
 -> Con7

nil7 : Con7
nil7 = \ con, nil7, snoc => nil7

snoc7 : Con7 -> Ty7 -> Con7
snoc7 = \ g, a, con, nil7, snoc7 => snoc7 (g con nil7 snoc7) a

Var7 : Con7 -> Ty7 -> Type
Var7 = \ g, a =>
    (Var7 : Con7 -> Ty7 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var7 (snoc7 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var7 g a -> Var7 (snoc7 g b) a)
 -> Var7 g a

vz7 : {g : _}-> {a : _} -> Var7 (snoc7 g a) a
vz7 = \ var, vz7, vs => vz7 _ _

vs7 : {g : _} -> {B : _} -> {a : _} -> Var7 g a -> Var7 (snoc7 g B) a
vs7 = \ x, var, vz7, vs7 => vs7 _ _ _ (x var vz7 vs7)

Tm7 : Con7 -> Ty7 -> Type
Tm7 = \ g, a =>
    (Tm7    : Con7 -> Ty7 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var7 g a -> Tm7 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm7 (snoc7 g a) B -> Tm7 g (arr7 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm7 g (arr7 a B) -> Tm7 g a -> Tm7 g B)
 -> Tm7 g a

var7 : {g : _} -> {a : _} -> Var7 g a -> Tm7 g a
var7 = \ x, tm, var7, lam, app => var7 _ _ x

lam7 : {g : _} -> {a : _} -> {B : _} -> Tm7 (snoc7 g a) B -> Tm7 g (arr7 a B)
lam7 = \ t, tm, var7, lam7, app => lam7 _ _ _ (t tm var7 lam7 app)

app7 : {g:_}->{a:_}->{B:_} -> Tm7 g (arr7 a B) -> Tm7 g a -> Tm7 g B
app7 = \ t, u, tm, var7, lam7, app7 => app7 _ _ _ (t tm var7 lam7 app7) (u tm var7 lam7 app7)

v07 : {g:_}->{a:_} -> Tm7 (snoc7 g a) a
v07 = var7 vz7

v17 : {g:_}->{a:_}-> {B:_}-> Tm7 (snoc7 (snoc7 g a) B) a
v17 = var7 (vs7 vz7)

v27 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm7 (snoc7 (snoc7 (snoc7 g a) B) C) a
v27 = var7 (vs7 (vs7 vz7))

v37 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm7 (snoc7 (snoc7 (snoc7 (snoc7 g a) B) C) D) a
v37 = var7 (vs7 (vs7 (vs7 vz7)))

v47 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm7 (snoc7 (snoc7 (snoc7 (snoc7 (snoc7 g a) B) C) D) E) a
v47 = var7 (vs7 (vs7 (vs7 (vs7 vz7))))

test7 : {g:_}-> {a:_} -> Tm7 g (arr7 (arr7 a a) (arr7 a a))
test7  = lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07)))))))
Ty8 : Type
Ty8 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty8 : Ty8
empty8 = \ _, empty, _ => empty

arr8 : Ty8 -> Ty8 -> Ty8
arr8 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con8 : Type
Con8 = (Con8 : Type)
 ->(nil  : Con8)
 ->(snoc : Con8 -> Ty8 -> Con8)
 -> Con8

nil8 : Con8
nil8 = \ con, nil8, snoc => nil8

snoc8 : Con8 -> Ty8 -> Con8
snoc8 = \ g, a, con, nil8, snoc8 => snoc8 (g con nil8 snoc8) a

Var8 : Con8 -> Ty8 -> Type
Var8 = \ g, a =>
    (Var8 : Con8 -> Ty8 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var8 (snoc8 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var8 g a -> Var8 (snoc8 g b) a)
 -> Var8 g a

vz8 : {g : _}-> {a : _} -> Var8 (snoc8 g a) a
vz8 = \ var, vz8, vs => vz8 _ _

vs8 : {g : _} -> {B : _} -> {a : _} -> Var8 g a -> Var8 (snoc8 g B) a
vs8 = \ x, var, vz8, vs8 => vs8 _ _ _ (x var vz8 vs8)

Tm8 : Con8 -> Ty8 -> Type
Tm8 = \ g, a =>
    (Tm8    : Con8 -> Ty8 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var8 g a -> Tm8 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm8 (snoc8 g a) B -> Tm8 g (arr8 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm8 g (arr8 a B) -> Tm8 g a -> Tm8 g B)
 -> Tm8 g a

var8 : {g : _} -> {a : _} -> Var8 g a -> Tm8 g a
var8 = \ x, tm, var8, lam, app => var8 _ _ x

lam8 : {g : _} -> {a : _} -> {B : _} -> Tm8 (snoc8 g a) B -> Tm8 g (arr8 a B)
lam8 = \ t, tm, var8, lam8, app => lam8 _ _ _ (t tm var8 lam8 app)

app8 : {g:_}->{a:_}->{B:_} -> Tm8 g (arr8 a B) -> Tm8 g a -> Tm8 g B
app8 = \ t, u, tm, var8, lam8, app8 => app8 _ _ _ (t tm var8 lam8 app8) (u tm var8 lam8 app8)

v08 : {g:_}->{a:_} -> Tm8 (snoc8 g a) a
v08 = var8 vz8

v18 : {g:_}->{a:_}-> {B:_}-> Tm8 (snoc8 (snoc8 g a) B) a
v18 = var8 (vs8 vz8)

v28 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm8 (snoc8 (snoc8 (snoc8 g a) B) C) a
v28 = var8 (vs8 (vs8 vz8))

v38 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm8 (snoc8 (snoc8 (snoc8 (snoc8 g a) B) C) D) a
v38 = var8 (vs8 (vs8 (vs8 vz8)))

v48 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm8 (snoc8 (snoc8 (snoc8 (snoc8 (snoc8 g a) B) C) D) E) a
v48 = var8 (vs8 (vs8 (vs8 (vs8 vz8))))

test8 : {g:_}-> {a:_} -> Tm8 g (arr8 (arr8 a a) (arr8 a a))
test8  = lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08)))))))
Ty9 : Type
Ty9 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty9 : Ty9
empty9 = \ _, empty, _ => empty

arr9 : Ty9 -> Ty9 -> Ty9
arr9 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con9 : Type
Con9 = (Con9 : Type)
 ->(nil  : Con9)
 ->(snoc : Con9 -> Ty9 -> Con9)
 -> Con9

nil9 : Con9
nil9 = \ con, nil9, snoc => nil9

snoc9 : Con9 -> Ty9 -> Con9
snoc9 = \ g, a, con, nil9, snoc9 => snoc9 (g con nil9 snoc9) a

Var9 : Con9 -> Ty9 -> Type
Var9 = \ g, a =>
    (Var9 : Con9 -> Ty9 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var9 (snoc9 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var9 g a -> Var9 (snoc9 g b) a)
 -> Var9 g a

vz9 : {g : _}-> {a : _} -> Var9 (snoc9 g a) a
vz9 = \ var, vz9, vs => vz9 _ _

vs9 : {g : _} -> {B : _} -> {a : _} -> Var9 g a -> Var9 (snoc9 g B) a
vs9 = \ x, var, vz9, vs9 => vs9 _ _ _ (x var vz9 vs9)

Tm9 : Con9 -> Ty9 -> Type
Tm9 = \ g, a =>
    (Tm9    : Con9 -> Ty9 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var9 g a -> Tm9 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm9 (snoc9 g a) B -> Tm9 g (arr9 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm9 g (arr9 a B) -> Tm9 g a -> Tm9 g B)
 -> Tm9 g a

var9 : {g : _} -> {a : _} -> Var9 g a -> Tm9 g a
var9 = \ x, tm, var9, lam, app => var9 _ _ x

lam9 : {g : _} -> {a : _} -> {B : _} -> Tm9 (snoc9 g a) B -> Tm9 g (arr9 a B)
lam9 = \ t, tm, var9, lam9, app => lam9 _ _ _ (t tm var9 lam9 app)

app9 : {g:_}->{a:_}->{B:_} -> Tm9 g (arr9 a B) -> Tm9 g a -> Tm9 g B
app9 = \ t, u, tm, var9, lam9, app9 => app9 _ _ _ (t tm var9 lam9 app9) (u tm var9 lam9 app9)

v09 : {g:_}->{a:_} -> Tm9 (snoc9 g a) a
v09 = var9 vz9

v19 : {g:_}->{a:_}-> {B:_}-> Tm9 (snoc9 (snoc9 g a) B) a
v19 = var9 (vs9 vz9)

v29 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm9 (snoc9 (snoc9 (snoc9 g a) B) C) a
v29 = var9 (vs9 (vs9 vz9))

v39 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm9 (snoc9 (snoc9 (snoc9 (snoc9 g a) B) C) D) a
v39 = var9 (vs9 (vs9 (vs9 vz9)))

v49 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm9 (snoc9 (snoc9 (snoc9 (snoc9 (snoc9 g a) B) C) D) E) a
v49 = var9 (vs9 (vs9 (vs9 (vs9 vz9))))

test9 : {g:_}-> {a:_} -> Tm9 g (arr9 (arr9 a a) (arr9 a a))
test9  = lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09)))))))
Ty10 : Type
Ty10 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty10 : Ty10
empty10 = \ _, empty, _ => empty

arr10 : Ty10 -> Ty10 -> Ty10
arr10 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con10 : Type
Con10 = (Con10 : Type)
 ->(nil  : Con10)
 ->(snoc : Con10 -> Ty10 -> Con10)
 -> Con10

nil10 : Con10
nil10 = \ con, nil10, snoc => nil10

snoc10 : Con10 -> Ty10 -> Con10
snoc10 = \ g, a, con, nil10, snoc10 => snoc10 (g con nil10 snoc10) a

Var10 : Con10 -> Ty10 -> Type
Var10 = \ g, a =>
    (Var10 : Con10 -> Ty10 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var10 (snoc10 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var10 g a -> Var10 (snoc10 g b) a)
 -> Var10 g a

vz10 : {g : _}-> {a : _} -> Var10 (snoc10 g a) a
vz10 = \ var, vz10, vs => vz10 _ _

vs10 : {g : _} -> {B : _} -> {a : _} -> Var10 g a -> Var10 (snoc10 g B) a
vs10 = \ x, var, vz10, vs10 => vs10 _ _ _ (x var vz10 vs10)

Tm10 : Con10 -> Ty10 -> Type
Tm10 = \ g, a =>
    (Tm10    : Con10 -> Ty10 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var10 g a -> Tm10 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm10 (snoc10 g a) B -> Tm10 g (arr10 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm10 g (arr10 a B) -> Tm10 g a -> Tm10 g B)
 -> Tm10 g a

var10 : {g : _} -> {a : _} -> Var10 g a -> Tm10 g a
var10 = \ x, tm, var10, lam, app => var10 _ _ x

lam10 : {g : _} -> {a : _} -> {B : _} -> Tm10 (snoc10 g a) B -> Tm10 g (arr10 a B)
lam10 = \ t, tm, var10, lam10, app => lam10 _ _ _ (t tm var10 lam10 app)

app10 : {g:_}->{a:_}->{B:_} -> Tm10 g (arr10 a B) -> Tm10 g a -> Tm10 g B
app10 = \ t, u, tm, var10, lam10, app10 => app10 _ _ _ (t tm var10 lam10 app10) (u tm var10 lam10 app10)

v010 : {g:_}->{a:_} -> Tm10 (snoc10 g a) a
v010 = var10 vz10

v110 : {g:_}->{a:_}-> {B:_}-> Tm10 (snoc10 (snoc10 g a) B) a
v110 = var10 (vs10 vz10)

v210 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm10 (snoc10 (snoc10 (snoc10 g a) B) C) a
v210 = var10 (vs10 (vs10 vz10))

v310 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm10 (snoc10 (snoc10 (snoc10 (snoc10 g a) B) C) D) a
v310 = var10 (vs10 (vs10 (vs10 vz10)))

v410 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm10 (snoc10 (snoc10 (snoc10 (snoc10 (snoc10 g a) B) C) D) E) a
v410 = var10 (vs10 (vs10 (vs10 (vs10 vz10))))

test10 : {g:_}-> {a:_} -> Tm10 g (arr10 (arr10 a a) (arr10 a a))
test10  = lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010)))))))
Ty11 : Type
Ty11 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty11 : Ty11
empty11 = \ _, empty, _ => empty

arr11 : Ty11 -> Ty11 -> Ty11
arr11 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con11 : Type
Con11 = (Con11 : Type)
 ->(nil  : Con11)
 ->(snoc : Con11 -> Ty11 -> Con11)
 -> Con11

nil11 : Con11
nil11 = \ con, nil11, snoc => nil11

snoc11 : Con11 -> Ty11 -> Con11
snoc11 = \ g, a, con, nil11, snoc11 => snoc11 (g con nil11 snoc11) a

Var11 : Con11 -> Ty11 -> Type
Var11 = \ g, a =>
    (Var11 : Con11 -> Ty11 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var11 (snoc11 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var11 g a -> Var11 (snoc11 g b) a)
 -> Var11 g a

vz11 : {g : _}-> {a : _} -> Var11 (snoc11 g a) a
vz11 = \ var, vz11, vs => vz11 _ _

vs11 : {g : _} -> {B : _} -> {a : _} -> Var11 g a -> Var11 (snoc11 g B) a
vs11 = \ x, var, vz11, vs11 => vs11 _ _ _ (x var vz11 vs11)

Tm11 : Con11 -> Ty11 -> Type
Tm11 = \ g, a =>
    (Tm11    : Con11 -> Ty11 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var11 g a -> Tm11 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm11 (snoc11 g a) B -> Tm11 g (arr11 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm11 g (arr11 a B) -> Tm11 g a -> Tm11 g B)
 -> Tm11 g a

var11 : {g : _} -> {a : _} -> Var11 g a -> Tm11 g a
var11 = \ x, tm, var11, lam, app => var11 _ _ x

lam11 : {g : _} -> {a : _} -> {B : _} -> Tm11 (snoc11 g a) B -> Tm11 g (arr11 a B)
lam11 = \ t, tm, var11, lam11, app => lam11 _ _ _ (t tm var11 lam11 app)

app11 : {g:_}->{a:_}->{B:_} -> Tm11 g (arr11 a B) -> Tm11 g a -> Tm11 g B
app11 = \ t, u, tm, var11, lam11, app11 => app11 _ _ _ (t tm var11 lam11 app11) (u tm var11 lam11 app11)

v011 : {g:_}->{a:_} -> Tm11 (snoc11 g a) a
v011 = var11 vz11

v111 : {g:_}->{a:_}-> {B:_}-> Tm11 (snoc11 (snoc11 g a) B) a
v111 = var11 (vs11 vz11)

v211 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm11 (snoc11 (snoc11 (snoc11 g a) B) C) a
v211 = var11 (vs11 (vs11 vz11))

v311 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm11 (snoc11 (snoc11 (snoc11 (snoc11 g a) B) C) D) a
v311 = var11 (vs11 (vs11 (vs11 vz11)))

v411 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm11 (snoc11 (snoc11 (snoc11 (snoc11 (snoc11 g a) B) C) D) E) a
v411 = var11 (vs11 (vs11 (vs11 (vs11 vz11))))

test11 : {g:_}-> {a:_} -> Tm11 g (arr11 (arr11 a a) (arr11 a a))
test11  = lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011)))))))
Ty12 : Type
Ty12 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty12 : Ty12
empty12 = \ _, empty, _ => empty

arr12 : Ty12 -> Ty12 -> Ty12
arr12 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con12 : Type
Con12 = (Con12 : Type)
 ->(nil  : Con12)
 ->(snoc : Con12 -> Ty12 -> Con12)
 -> Con12

nil12 : Con12
nil12 = \ con, nil12, snoc => nil12

snoc12 : Con12 -> Ty12 -> Con12
snoc12 = \ g, a, con, nil12, snoc12 => snoc12 (g con nil12 snoc12) a

Var12 : Con12 -> Ty12 -> Type
Var12 = \ g, a =>
    (Var12 : Con12 -> Ty12 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var12 (snoc12 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var12 g a -> Var12 (snoc12 g b) a)
 -> Var12 g a

vz12 : {g : _}-> {a : _} -> Var12 (snoc12 g a) a
vz12 = \ var, vz12, vs => vz12 _ _

vs12 : {g : _} -> {B : _} -> {a : _} -> Var12 g a -> Var12 (snoc12 g B) a
vs12 = \ x, var, vz12, vs12 => vs12 _ _ _ (x var vz12 vs12)

Tm12 : Con12 -> Ty12 -> Type
Tm12 = \ g, a =>
    (Tm12    : Con12 -> Ty12 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var12 g a -> Tm12 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm12 (snoc12 g a) B -> Tm12 g (arr12 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm12 g (arr12 a B) -> Tm12 g a -> Tm12 g B)
 -> Tm12 g a

var12 : {g : _} -> {a : _} -> Var12 g a -> Tm12 g a
var12 = \ x, tm, var12, lam, app => var12 _ _ x

lam12 : {g : _} -> {a : _} -> {B : _} -> Tm12 (snoc12 g a) B -> Tm12 g (arr12 a B)
lam12 = \ t, tm, var12, lam12, app => lam12 _ _ _ (t tm var12 lam12 app)

app12 : {g:_}->{a:_}->{B:_} -> Tm12 g (arr12 a B) -> Tm12 g a -> Tm12 g B
app12 = \ t, u, tm, var12, lam12, app12 => app12 _ _ _ (t tm var12 lam12 app12) (u tm var12 lam12 app12)

v012 : {g:_}->{a:_} -> Tm12 (snoc12 g a) a
v012 = var12 vz12

v112 : {g:_}->{a:_}-> {B:_}-> Tm12 (snoc12 (snoc12 g a) B) a
v112 = var12 (vs12 vz12)

v212 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm12 (snoc12 (snoc12 (snoc12 g a) B) C) a
v212 = var12 (vs12 (vs12 vz12))

v312 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm12 (snoc12 (snoc12 (snoc12 (snoc12 g a) B) C) D) a
v312 = var12 (vs12 (vs12 (vs12 vz12)))

v412 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm12 (snoc12 (snoc12 (snoc12 (snoc12 (snoc12 g a) B) C) D) E) a
v412 = var12 (vs12 (vs12 (vs12 (vs12 vz12))))

test12 : {g:_}-> {a:_} -> Tm12 g (arr12 (arr12 a a) (arr12 a a))
test12  = lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012)))))))
Ty13 : Type
Ty13 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty13 : Ty13
empty13 = \ _, empty, _ => empty

arr13 : Ty13 -> Ty13 -> Ty13
arr13 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con13 : Type
Con13 = (Con13 : Type)
 ->(nil  : Con13)
 ->(snoc : Con13 -> Ty13 -> Con13)
 -> Con13

nil13 : Con13
nil13 = \ con, nil13, snoc => nil13

snoc13 : Con13 -> Ty13 -> Con13
snoc13 = \ g, a, con, nil13, snoc13 => snoc13 (g con nil13 snoc13) a

Var13 : Con13 -> Ty13 -> Type
Var13 = \ g, a =>
    (Var13 : Con13 -> Ty13 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var13 (snoc13 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var13 g a -> Var13 (snoc13 g b) a)
 -> Var13 g a

vz13 : {g : _}-> {a : _} -> Var13 (snoc13 g a) a
vz13 = \ var, vz13, vs => vz13 _ _

vs13 : {g : _} -> {B : _} -> {a : _} -> Var13 g a -> Var13 (snoc13 g B) a
vs13 = \ x, var, vz13, vs13 => vs13 _ _ _ (x var vz13 vs13)

Tm13 : Con13 -> Ty13 -> Type
Tm13 = \ g, a =>
    (Tm13    : Con13 -> Ty13 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var13 g a -> Tm13 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm13 (snoc13 g a) B -> Tm13 g (arr13 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm13 g (arr13 a B) -> Tm13 g a -> Tm13 g B)
 -> Tm13 g a

var13 : {g : _} -> {a : _} -> Var13 g a -> Tm13 g a
var13 = \ x, tm, var13, lam, app => var13 _ _ x

lam13 : {g : _} -> {a : _} -> {B : _} -> Tm13 (snoc13 g a) B -> Tm13 g (arr13 a B)
lam13 = \ t, tm, var13, lam13, app => lam13 _ _ _ (t tm var13 lam13 app)

app13 : {g:_}->{a:_}->{B:_} -> Tm13 g (arr13 a B) -> Tm13 g a -> Tm13 g B
app13 = \ t, u, tm, var13, lam13, app13 => app13 _ _ _ (t tm var13 lam13 app13) (u tm var13 lam13 app13)

v013 : {g:_}->{a:_} -> Tm13 (snoc13 g a) a
v013 = var13 vz13

v113 : {g:_}->{a:_}-> {B:_}-> Tm13 (snoc13 (snoc13 g a) B) a
v113 = var13 (vs13 vz13)

v213 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm13 (snoc13 (snoc13 (snoc13 g a) B) C) a
v213 = var13 (vs13 (vs13 vz13))

v313 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm13 (snoc13 (snoc13 (snoc13 (snoc13 g a) B) C) D) a
v313 = var13 (vs13 (vs13 (vs13 vz13)))

v413 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm13 (snoc13 (snoc13 (snoc13 (snoc13 (snoc13 g a) B) C) D) E) a
v413 = var13 (vs13 (vs13 (vs13 (vs13 vz13))))

test13 : {g:_}-> {a:_} -> Tm13 g (arr13 (arr13 a a) (arr13 a a))
test13  = lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013)))))))
Ty14 : Type
Ty14 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty14 : Ty14
empty14 = \ _, empty, _ => empty

arr14 : Ty14 -> Ty14 -> Ty14
arr14 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con14 : Type
Con14 = (Con14 : Type)
 ->(nil  : Con14)
 ->(snoc : Con14 -> Ty14 -> Con14)
 -> Con14

nil14 : Con14
nil14 = \ con, nil14, snoc => nil14

snoc14 : Con14 -> Ty14 -> Con14
snoc14 = \ g, a, con, nil14, snoc14 => snoc14 (g con nil14 snoc14) a

Var14 : Con14 -> Ty14 -> Type
Var14 = \ g, a =>
    (Var14 : Con14 -> Ty14 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var14 (snoc14 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var14 g a -> Var14 (snoc14 g b) a)
 -> Var14 g a

vz14 : {g : _}-> {a : _} -> Var14 (snoc14 g a) a
vz14 = \ var, vz14, vs => vz14 _ _

vs14 : {g : _} -> {B : _} -> {a : _} -> Var14 g a -> Var14 (snoc14 g B) a
vs14 = \ x, var, vz14, vs14 => vs14 _ _ _ (x var vz14 vs14)

Tm14 : Con14 -> Ty14 -> Type
Tm14 = \ g, a =>
    (Tm14    : Con14 -> Ty14 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var14 g a -> Tm14 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm14 (snoc14 g a) B -> Tm14 g (arr14 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm14 g (arr14 a B) -> Tm14 g a -> Tm14 g B)
 -> Tm14 g a

var14 : {g : _} -> {a : _} -> Var14 g a -> Tm14 g a
var14 = \ x, tm, var14, lam, app => var14 _ _ x

lam14 : {g : _} -> {a : _} -> {B : _} -> Tm14 (snoc14 g a) B -> Tm14 g (arr14 a B)
lam14 = \ t, tm, var14, lam14, app => lam14 _ _ _ (t tm var14 lam14 app)

app14 : {g:_}->{a:_}->{B:_} -> Tm14 g (arr14 a B) -> Tm14 g a -> Tm14 g B
app14 = \ t, u, tm, var14, lam14, app14 => app14 _ _ _ (t tm var14 lam14 app14) (u tm var14 lam14 app14)

v014 : {g:_}->{a:_} -> Tm14 (snoc14 g a) a
v014 = var14 vz14

v114 : {g:_}->{a:_}-> {B:_}-> Tm14 (snoc14 (snoc14 g a) B) a
v114 = var14 (vs14 vz14)

v214 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm14 (snoc14 (snoc14 (snoc14 g a) B) C) a
v214 = var14 (vs14 (vs14 vz14))

v314 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm14 (snoc14 (snoc14 (snoc14 (snoc14 g a) B) C) D) a
v314 = var14 (vs14 (vs14 (vs14 vz14)))

v414 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm14 (snoc14 (snoc14 (snoc14 (snoc14 (snoc14 g a) B) C) D) E) a
v414 = var14 (vs14 (vs14 (vs14 (vs14 vz14))))

test14 : {g:_}-> {a:_} -> Tm14 g (arr14 (arr14 a a) (arr14 a a))
test14  = lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014)))))))
Ty15 : Type
Ty15 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty15 : Ty15
empty15 = \ _, empty, _ => empty

arr15 : Ty15 -> Ty15 -> Ty15
arr15 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con15 : Type
Con15 = (Con15 : Type)
 ->(nil  : Con15)
 ->(snoc : Con15 -> Ty15 -> Con15)
 -> Con15

nil15 : Con15
nil15 = \ con, nil15, snoc => nil15

snoc15 : Con15 -> Ty15 -> Con15
snoc15 = \ g, a, con, nil15, snoc15 => snoc15 (g con nil15 snoc15) a

Var15 : Con15 -> Ty15 -> Type
Var15 = \ g, a =>
    (Var15 : Con15 -> Ty15 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var15 (snoc15 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var15 g a -> Var15 (snoc15 g b) a)
 -> Var15 g a

vz15 : {g : _}-> {a : _} -> Var15 (snoc15 g a) a
vz15 = \ var, vz15, vs => vz15 _ _

vs15 : {g : _} -> {B : _} -> {a : _} -> Var15 g a -> Var15 (snoc15 g B) a
vs15 = \ x, var, vz15, vs15 => vs15 _ _ _ (x var vz15 vs15)

Tm15 : Con15 -> Ty15 -> Type
Tm15 = \ g, a =>
    (Tm15    : Con15 -> Ty15 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var15 g a -> Tm15 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm15 (snoc15 g a) B -> Tm15 g (arr15 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm15 g (arr15 a B) -> Tm15 g a -> Tm15 g B)
 -> Tm15 g a

var15 : {g : _} -> {a : _} -> Var15 g a -> Tm15 g a
var15 = \ x, tm, var15, lam, app => var15 _ _ x

lam15 : {g : _} -> {a : _} -> {B : _} -> Tm15 (snoc15 g a) B -> Tm15 g (arr15 a B)
lam15 = \ t, tm, var15, lam15, app => lam15 _ _ _ (t tm var15 lam15 app)

app15 : {g:_}->{a:_}->{B:_} -> Tm15 g (arr15 a B) -> Tm15 g a -> Tm15 g B
app15 = \ t, u, tm, var15, lam15, app15 => app15 _ _ _ (t tm var15 lam15 app15) (u tm var15 lam15 app15)

v015 : {g:_}->{a:_} -> Tm15 (snoc15 g a) a
v015 = var15 vz15

v115 : {g:_}->{a:_}-> {B:_}-> Tm15 (snoc15 (snoc15 g a) B) a
v115 = var15 (vs15 vz15)

v215 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm15 (snoc15 (snoc15 (snoc15 g a) B) C) a
v215 = var15 (vs15 (vs15 vz15))

v315 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm15 (snoc15 (snoc15 (snoc15 (snoc15 g a) B) C) D) a
v315 = var15 (vs15 (vs15 (vs15 vz15)))

v415 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm15 (snoc15 (snoc15 (snoc15 (snoc15 (snoc15 g a) B) C) D) E) a
v415 = var15 (vs15 (vs15 (vs15 (vs15 vz15))))

test15 : {g:_}-> {a:_} -> Tm15 g (arr15 (arr15 a a) (arr15 a a))
test15  = lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015)))))))
Ty16 : Type
Ty16 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty16 : Ty16
empty16 = \ _, empty, _ => empty

arr16 : Ty16 -> Ty16 -> Ty16
arr16 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con16 : Type
Con16 = (Con16 : Type)
 ->(nil  : Con16)
 ->(snoc : Con16 -> Ty16 -> Con16)
 -> Con16

nil16 : Con16
nil16 = \ con, nil16, snoc => nil16

snoc16 : Con16 -> Ty16 -> Con16
snoc16 = \ g, a, con, nil16, snoc16 => snoc16 (g con nil16 snoc16) a

Var16 : Con16 -> Ty16 -> Type
Var16 = \ g, a =>
    (Var16 : Con16 -> Ty16 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var16 (snoc16 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var16 g a -> Var16 (snoc16 g b) a)
 -> Var16 g a

vz16 : {g : _}-> {a : _} -> Var16 (snoc16 g a) a
vz16 = \ var, vz16, vs => vz16 _ _

vs16 : {g : _} -> {B : _} -> {a : _} -> Var16 g a -> Var16 (snoc16 g B) a
vs16 = \ x, var, vz16, vs16 => vs16 _ _ _ (x var vz16 vs16)

Tm16 : Con16 -> Ty16 -> Type
Tm16 = \ g, a =>
    (Tm16    : Con16 -> Ty16 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var16 g a -> Tm16 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm16 (snoc16 g a) B -> Tm16 g (arr16 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm16 g (arr16 a B) -> Tm16 g a -> Tm16 g B)
 -> Tm16 g a

var16 : {g : _} -> {a : _} -> Var16 g a -> Tm16 g a
var16 = \ x, tm, var16, lam, app => var16 _ _ x

lam16 : {g : _} -> {a : _} -> {B : _} -> Tm16 (snoc16 g a) B -> Tm16 g (arr16 a B)
lam16 = \ t, tm, var16, lam16, app => lam16 _ _ _ (t tm var16 lam16 app)

app16 : {g:_}->{a:_}->{B:_} -> Tm16 g (arr16 a B) -> Tm16 g a -> Tm16 g B
app16 = \ t, u, tm, var16, lam16, app16 => app16 _ _ _ (t tm var16 lam16 app16) (u tm var16 lam16 app16)

v016 : {g:_}->{a:_} -> Tm16 (snoc16 g a) a
v016 = var16 vz16

v116 : {g:_}->{a:_}-> {B:_}-> Tm16 (snoc16 (snoc16 g a) B) a
v116 = var16 (vs16 vz16)

v216 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm16 (snoc16 (snoc16 (snoc16 g a) B) C) a
v216 = var16 (vs16 (vs16 vz16))

v316 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm16 (snoc16 (snoc16 (snoc16 (snoc16 g a) B) C) D) a
v316 = var16 (vs16 (vs16 (vs16 vz16)))

v416 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm16 (snoc16 (snoc16 (snoc16 (snoc16 (snoc16 g a) B) C) D) E) a
v416 = var16 (vs16 (vs16 (vs16 (vs16 vz16))))

test16 : {g:_}-> {a:_} -> Tm16 g (arr16 (arr16 a a) (arr16 a a))
test16  = lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016)))))))
Ty17 : Type
Ty17 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty17 : Ty17
empty17 = \ _, empty, _ => empty

arr17 : Ty17 -> Ty17 -> Ty17
arr17 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con17 : Type
Con17 = (Con17 : Type)
 ->(nil  : Con17)
 ->(snoc : Con17 -> Ty17 -> Con17)
 -> Con17

nil17 : Con17
nil17 = \ con, nil17, snoc => nil17

snoc17 : Con17 -> Ty17 -> Con17
snoc17 = \ g, a, con, nil17, snoc17 => snoc17 (g con nil17 snoc17) a

Var17 : Con17 -> Ty17 -> Type
Var17 = \ g, a =>
    (Var17 : Con17 -> Ty17 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var17 (snoc17 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var17 g a -> Var17 (snoc17 g b) a)
 -> Var17 g a

vz17 : {g : _}-> {a : _} -> Var17 (snoc17 g a) a
vz17 = \ var, vz17, vs => vz17 _ _

vs17 : {g : _} -> {B : _} -> {a : _} -> Var17 g a -> Var17 (snoc17 g B) a
vs17 = \ x, var, vz17, vs17 => vs17 _ _ _ (x var vz17 vs17)

Tm17 : Con17 -> Ty17 -> Type
Tm17 = \ g, a =>
    (Tm17    : Con17 -> Ty17 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var17 g a -> Tm17 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm17 (snoc17 g a) B -> Tm17 g (arr17 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm17 g (arr17 a B) -> Tm17 g a -> Tm17 g B)
 -> Tm17 g a

var17 : {g : _} -> {a : _} -> Var17 g a -> Tm17 g a
var17 = \ x, tm, var17, lam, app => var17 _ _ x

lam17 : {g : _} -> {a : _} -> {B : _} -> Tm17 (snoc17 g a) B -> Tm17 g (arr17 a B)
lam17 = \ t, tm, var17, lam17, app => lam17 _ _ _ (t tm var17 lam17 app)

app17 : {g:_}->{a:_}->{B:_} -> Tm17 g (arr17 a B) -> Tm17 g a -> Tm17 g B
app17 = \ t, u, tm, var17, lam17, app17 => app17 _ _ _ (t tm var17 lam17 app17) (u tm var17 lam17 app17)

v017 : {g:_}->{a:_} -> Tm17 (snoc17 g a) a
v017 = var17 vz17

v117 : {g:_}->{a:_}-> {B:_}-> Tm17 (snoc17 (snoc17 g a) B) a
v117 = var17 (vs17 vz17)

v217 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm17 (snoc17 (snoc17 (snoc17 g a) B) C) a
v217 = var17 (vs17 (vs17 vz17))

v317 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm17 (snoc17 (snoc17 (snoc17 (snoc17 g a) B) C) D) a
v317 = var17 (vs17 (vs17 (vs17 vz17)))

v417 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm17 (snoc17 (snoc17 (snoc17 (snoc17 (snoc17 g a) B) C) D) E) a
v417 = var17 (vs17 (vs17 (vs17 (vs17 vz17))))

test17 : {g:_}-> {a:_} -> Tm17 g (arr17 (arr17 a a) (arr17 a a))
test17  = lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017)))))))
Ty18 : Type
Ty18 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty18 : Ty18
empty18 = \ _, empty, _ => empty

arr18 : Ty18 -> Ty18 -> Ty18
arr18 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con18 : Type
Con18 = (Con18 : Type)
 ->(nil  : Con18)
 ->(snoc : Con18 -> Ty18 -> Con18)
 -> Con18

nil18 : Con18
nil18 = \ con, nil18, snoc => nil18

snoc18 : Con18 -> Ty18 -> Con18
snoc18 = \ g, a, con, nil18, snoc18 => snoc18 (g con nil18 snoc18) a

Var18 : Con18 -> Ty18 -> Type
Var18 = \ g, a =>
    (Var18 : Con18 -> Ty18 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var18 (snoc18 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var18 g a -> Var18 (snoc18 g b) a)
 -> Var18 g a

vz18 : {g : _}-> {a : _} -> Var18 (snoc18 g a) a
vz18 = \ var, vz18, vs => vz18 _ _

vs18 : {g : _} -> {B : _} -> {a : _} -> Var18 g a -> Var18 (snoc18 g B) a
vs18 = \ x, var, vz18, vs18 => vs18 _ _ _ (x var vz18 vs18)

Tm18 : Con18 -> Ty18 -> Type
Tm18 = \ g, a =>
    (Tm18    : Con18 -> Ty18 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var18 g a -> Tm18 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm18 (snoc18 g a) B -> Tm18 g (arr18 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm18 g (arr18 a B) -> Tm18 g a -> Tm18 g B)
 -> Tm18 g a

var18 : {g : _} -> {a : _} -> Var18 g a -> Tm18 g a
var18 = \ x, tm, var18, lam, app => var18 _ _ x

lam18 : {g : _} -> {a : _} -> {B : _} -> Tm18 (snoc18 g a) B -> Tm18 g (arr18 a B)
lam18 = \ t, tm, var18, lam18, app => lam18 _ _ _ (t tm var18 lam18 app)

app18 : {g:_}->{a:_}->{B:_} -> Tm18 g (arr18 a B) -> Tm18 g a -> Tm18 g B
app18 = \ t, u, tm, var18, lam18, app18 => app18 _ _ _ (t tm var18 lam18 app18) (u tm var18 lam18 app18)

v018 : {g:_}->{a:_} -> Tm18 (snoc18 g a) a
v018 = var18 vz18

v118 : {g:_}->{a:_}-> {B:_}-> Tm18 (snoc18 (snoc18 g a) B) a
v118 = var18 (vs18 vz18)

v218 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm18 (snoc18 (snoc18 (snoc18 g a) B) C) a
v218 = var18 (vs18 (vs18 vz18))

v318 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm18 (snoc18 (snoc18 (snoc18 (snoc18 g a) B) C) D) a
v318 = var18 (vs18 (vs18 (vs18 vz18)))

v418 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm18 (snoc18 (snoc18 (snoc18 (snoc18 (snoc18 g a) B) C) D) E) a
v418 = var18 (vs18 (vs18 (vs18 (vs18 vz18))))

test18 : {g:_}-> {a:_} -> Tm18 g (arr18 (arr18 a a) (arr18 a a))
test18  = lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018)))))))
