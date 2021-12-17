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
Ty19 : Type
Ty19 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty19 : Ty19
empty19 = \ _, empty, _ => empty

arr19 : Ty19 -> Ty19 -> Ty19
arr19 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con19 : Type
Con19 = (Con19 : Type)
 ->(nil  : Con19)
 ->(snoc : Con19 -> Ty19 -> Con19)
 -> Con19

nil19 : Con19
nil19 = \ con, nil19, snoc => nil19

snoc19 : Con19 -> Ty19 -> Con19
snoc19 = \ g, a, con, nil19, snoc19 => snoc19 (g con nil19 snoc19) a

Var19 : Con19 -> Ty19 -> Type
Var19 = \ g, a =>
    (Var19 : Con19 -> Ty19 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var19 (snoc19 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var19 g a -> Var19 (snoc19 g b) a)
 -> Var19 g a

vz19 : {g : _}-> {a : _} -> Var19 (snoc19 g a) a
vz19 = \ var, vz19, vs => vz19 _ _

vs19 : {g : _} -> {B : _} -> {a : _} -> Var19 g a -> Var19 (snoc19 g B) a
vs19 = \ x, var, vz19, vs19 => vs19 _ _ _ (x var vz19 vs19)

Tm19 : Con19 -> Ty19 -> Type
Tm19 = \ g, a =>
    (Tm19    : Con19 -> Ty19 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var19 g a -> Tm19 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm19 (snoc19 g a) B -> Tm19 g (arr19 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm19 g (arr19 a B) -> Tm19 g a -> Tm19 g B)
 -> Tm19 g a

var19 : {g : _} -> {a : _} -> Var19 g a -> Tm19 g a
var19 = \ x, tm, var19, lam, app => var19 _ _ x

lam19 : {g : _} -> {a : _} -> {B : _} -> Tm19 (snoc19 g a) B -> Tm19 g (arr19 a B)
lam19 = \ t, tm, var19, lam19, app => lam19 _ _ _ (t tm var19 lam19 app)

app19 : {g:_}->{a:_}->{B:_} -> Tm19 g (arr19 a B) -> Tm19 g a -> Tm19 g B
app19 = \ t, u, tm, var19, lam19, app19 => app19 _ _ _ (t tm var19 lam19 app19) (u tm var19 lam19 app19)

v019 : {g:_}->{a:_} -> Tm19 (snoc19 g a) a
v019 = var19 vz19

v119 : {g:_}->{a:_}-> {B:_}-> Tm19 (snoc19 (snoc19 g a) B) a
v119 = var19 (vs19 vz19)

v219 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm19 (snoc19 (snoc19 (snoc19 g a) B) C) a
v219 = var19 (vs19 (vs19 vz19))

v319 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm19 (snoc19 (snoc19 (snoc19 (snoc19 g a) B) C) D) a
v319 = var19 (vs19 (vs19 (vs19 vz19)))

v419 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm19 (snoc19 (snoc19 (snoc19 (snoc19 (snoc19 g a) B) C) D) E) a
v419 = var19 (vs19 (vs19 (vs19 (vs19 vz19))))

test19 : {g:_}-> {a:_} -> Tm19 g (arr19 (arr19 a a) (arr19 a a))
test19  = lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019)))))))
Ty20 : Type
Ty20 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty20 : Ty20
empty20 = \ _, empty, _ => empty

arr20 : Ty20 -> Ty20 -> Ty20
arr20 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con20 : Type
Con20 = (Con20 : Type)
 ->(nil  : Con20)
 ->(snoc : Con20 -> Ty20 -> Con20)
 -> Con20

nil20 : Con20
nil20 = \ con, nil20, snoc => nil20

snoc20 : Con20 -> Ty20 -> Con20
snoc20 = \ g, a, con, nil20, snoc20 => snoc20 (g con nil20 snoc20) a

Var20 : Con20 -> Ty20 -> Type
Var20 = \ g, a =>
    (Var20 : Con20 -> Ty20 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var20 (snoc20 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var20 g a -> Var20 (snoc20 g b) a)
 -> Var20 g a

vz20 : {g : _}-> {a : _} -> Var20 (snoc20 g a) a
vz20 = \ var, vz20, vs => vz20 _ _

vs20 : {g : _} -> {B : _} -> {a : _} -> Var20 g a -> Var20 (snoc20 g B) a
vs20 = \ x, var, vz20, vs20 => vs20 _ _ _ (x var vz20 vs20)

Tm20 : Con20 -> Ty20 -> Type
Tm20 = \ g, a =>
    (Tm20    : Con20 -> Ty20 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var20 g a -> Tm20 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm20 (snoc20 g a) B -> Tm20 g (arr20 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm20 g (arr20 a B) -> Tm20 g a -> Tm20 g B)
 -> Tm20 g a

var20 : {g : _} -> {a : _} -> Var20 g a -> Tm20 g a
var20 = \ x, tm, var20, lam, app => var20 _ _ x

lam20 : {g : _} -> {a : _} -> {B : _} -> Tm20 (snoc20 g a) B -> Tm20 g (arr20 a B)
lam20 = \ t, tm, var20, lam20, app => lam20 _ _ _ (t tm var20 lam20 app)

app20 : {g:_}->{a:_}->{B:_} -> Tm20 g (arr20 a B) -> Tm20 g a -> Tm20 g B
app20 = \ t, u, tm, var20, lam20, app20 => app20 _ _ _ (t tm var20 lam20 app20) (u tm var20 lam20 app20)

v020 : {g:_}->{a:_} -> Tm20 (snoc20 g a) a
v020 = var20 vz20

v120 : {g:_}->{a:_}-> {B:_}-> Tm20 (snoc20 (snoc20 g a) B) a
v120 = var20 (vs20 vz20)

v220 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm20 (snoc20 (snoc20 (snoc20 g a) B) C) a
v220 = var20 (vs20 (vs20 vz20))

v320 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm20 (snoc20 (snoc20 (snoc20 (snoc20 g a) B) C) D) a
v320 = var20 (vs20 (vs20 (vs20 vz20)))

v420 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm20 (snoc20 (snoc20 (snoc20 (snoc20 (snoc20 g a) B) C) D) E) a
v420 = var20 (vs20 (vs20 (vs20 (vs20 vz20))))

test20 : {g:_}-> {a:_} -> Tm20 g (arr20 (arr20 a a) (arr20 a a))
test20  = lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020)))))))
Ty21 : Type
Ty21 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty21 : Ty21
empty21 = \ _, empty, _ => empty

arr21 : Ty21 -> Ty21 -> Ty21
arr21 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con21 : Type
Con21 = (Con21 : Type)
 ->(nil  : Con21)
 ->(snoc : Con21 -> Ty21 -> Con21)
 -> Con21

nil21 : Con21
nil21 = \ con, nil21, snoc => nil21

snoc21 : Con21 -> Ty21 -> Con21
snoc21 = \ g, a, con, nil21, snoc21 => snoc21 (g con nil21 snoc21) a

Var21 : Con21 -> Ty21 -> Type
Var21 = \ g, a =>
    (Var21 : Con21 -> Ty21 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var21 (snoc21 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var21 g a -> Var21 (snoc21 g b) a)
 -> Var21 g a

vz21 : {g : _}-> {a : _} -> Var21 (snoc21 g a) a
vz21 = \ var, vz21, vs => vz21 _ _

vs21 : {g : _} -> {B : _} -> {a : _} -> Var21 g a -> Var21 (snoc21 g B) a
vs21 = \ x, var, vz21, vs21 => vs21 _ _ _ (x var vz21 vs21)

Tm21 : Con21 -> Ty21 -> Type
Tm21 = \ g, a =>
    (Tm21    : Con21 -> Ty21 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var21 g a -> Tm21 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm21 (snoc21 g a) B -> Tm21 g (arr21 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm21 g (arr21 a B) -> Tm21 g a -> Tm21 g B)
 -> Tm21 g a

var21 : {g : _} -> {a : _} -> Var21 g a -> Tm21 g a
var21 = \ x, tm, var21, lam, app => var21 _ _ x

lam21 : {g : _} -> {a : _} -> {B : _} -> Tm21 (snoc21 g a) B -> Tm21 g (arr21 a B)
lam21 = \ t, tm, var21, lam21, app => lam21 _ _ _ (t tm var21 lam21 app)

app21 : {g:_}->{a:_}->{B:_} -> Tm21 g (arr21 a B) -> Tm21 g a -> Tm21 g B
app21 = \ t, u, tm, var21, lam21, app21 => app21 _ _ _ (t tm var21 lam21 app21) (u tm var21 lam21 app21)

v021 : {g:_}->{a:_} -> Tm21 (snoc21 g a) a
v021 = var21 vz21

v121 : {g:_}->{a:_}-> {B:_}-> Tm21 (snoc21 (snoc21 g a) B) a
v121 = var21 (vs21 vz21)

v221 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm21 (snoc21 (snoc21 (snoc21 g a) B) C) a
v221 = var21 (vs21 (vs21 vz21))

v321 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm21 (snoc21 (snoc21 (snoc21 (snoc21 g a) B) C) D) a
v321 = var21 (vs21 (vs21 (vs21 vz21)))

v421 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm21 (snoc21 (snoc21 (snoc21 (snoc21 (snoc21 g a) B) C) D) E) a
v421 = var21 (vs21 (vs21 (vs21 (vs21 vz21))))

test21 : {g:_}-> {a:_} -> Tm21 g (arr21 (arr21 a a) (arr21 a a))
test21  = lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021)))))))
Ty22 : Type
Ty22 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty22 : Ty22
empty22 = \ _, empty, _ => empty

arr22 : Ty22 -> Ty22 -> Ty22
arr22 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con22 : Type
Con22 = (Con22 : Type)
 ->(nil  : Con22)
 ->(snoc : Con22 -> Ty22 -> Con22)
 -> Con22

nil22 : Con22
nil22 = \ con, nil22, snoc => nil22

snoc22 : Con22 -> Ty22 -> Con22
snoc22 = \ g, a, con, nil22, snoc22 => snoc22 (g con nil22 snoc22) a

Var22 : Con22 -> Ty22 -> Type
Var22 = \ g, a =>
    (Var22 : Con22 -> Ty22 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var22 (snoc22 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var22 g a -> Var22 (snoc22 g b) a)
 -> Var22 g a

vz22 : {g : _}-> {a : _} -> Var22 (snoc22 g a) a
vz22 = \ var, vz22, vs => vz22 _ _

vs22 : {g : _} -> {B : _} -> {a : _} -> Var22 g a -> Var22 (snoc22 g B) a
vs22 = \ x, var, vz22, vs22 => vs22 _ _ _ (x var vz22 vs22)

Tm22 : Con22 -> Ty22 -> Type
Tm22 = \ g, a =>
    (Tm22    : Con22 -> Ty22 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var22 g a -> Tm22 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm22 (snoc22 g a) B -> Tm22 g (arr22 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm22 g (arr22 a B) -> Tm22 g a -> Tm22 g B)
 -> Tm22 g a

var22 : {g : _} -> {a : _} -> Var22 g a -> Tm22 g a
var22 = \ x, tm, var22, lam, app => var22 _ _ x

lam22 : {g : _} -> {a : _} -> {B : _} -> Tm22 (snoc22 g a) B -> Tm22 g (arr22 a B)
lam22 = \ t, tm, var22, lam22, app => lam22 _ _ _ (t tm var22 lam22 app)

app22 : {g:_}->{a:_}->{B:_} -> Tm22 g (arr22 a B) -> Tm22 g a -> Tm22 g B
app22 = \ t, u, tm, var22, lam22, app22 => app22 _ _ _ (t tm var22 lam22 app22) (u tm var22 lam22 app22)

v022 : {g:_}->{a:_} -> Tm22 (snoc22 g a) a
v022 = var22 vz22

v122 : {g:_}->{a:_}-> {B:_}-> Tm22 (snoc22 (snoc22 g a) B) a
v122 = var22 (vs22 vz22)

v222 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm22 (snoc22 (snoc22 (snoc22 g a) B) C) a
v222 = var22 (vs22 (vs22 vz22))

v322 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm22 (snoc22 (snoc22 (snoc22 (snoc22 g a) B) C) D) a
v322 = var22 (vs22 (vs22 (vs22 vz22)))

v422 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm22 (snoc22 (snoc22 (snoc22 (snoc22 (snoc22 g a) B) C) D) E) a
v422 = var22 (vs22 (vs22 (vs22 (vs22 vz22))))

test22 : {g:_}-> {a:_} -> Tm22 g (arr22 (arr22 a a) (arr22 a a))
test22  = lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022)))))))
Ty23 : Type
Ty23 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty23 : Ty23
empty23 = \ _, empty, _ => empty

arr23 : Ty23 -> Ty23 -> Ty23
arr23 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con23 : Type
Con23 = (Con23 : Type)
 ->(nil  : Con23)
 ->(snoc : Con23 -> Ty23 -> Con23)
 -> Con23

nil23 : Con23
nil23 = \ con, nil23, snoc => nil23

snoc23 : Con23 -> Ty23 -> Con23
snoc23 = \ g, a, con, nil23, snoc23 => snoc23 (g con nil23 snoc23) a

Var23 : Con23 -> Ty23 -> Type
Var23 = \ g, a =>
    (Var23 : Con23 -> Ty23 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var23 (snoc23 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var23 g a -> Var23 (snoc23 g b) a)
 -> Var23 g a

vz23 : {g : _}-> {a : _} -> Var23 (snoc23 g a) a
vz23 = \ var, vz23, vs => vz23 _ _

vs23 : {g : _} -> {B : _} -> {a : _} -> Var23 g a -> Var23 (snoc23 g B) a
vs23 = \ x, var, vz23, vs23 => vs23 _ _ _ (x var vz23 vs23)

Tm23 : Con23 -> Ty23 -> Type
Tm23 = \ g, a =>
    (Tm23    : Con23 -> Ty23 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var23 g a -> Tm23 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm23 (snoc23 g a) B -> Tm23 g (arr23 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm23 g (arr23 a B) -> Tm23 g a -> Tm23 g B)
 -> Tm23 g a

var23 : {g : _} -> {a : _} -> Var23 g a -> Tm23 g a
var23 = \ x, tm, var23, lam, app => var23 _ _ x

lam23 : {g : _} -> {a : _} -> {B : _} -> Tm23 (snoc23 g a) B -> Tm23 g (arr23 a B)
lam23 = \ t, tm, var23, lam23, app => lam23 _ _ _ (t tm var23 lam23 app)

app23 : {g:_}->{a:_}->{B:_} -> Tm23 g (arr23 a B) -> Tm23 g a -> Tm23 g B
app23 = \ t, u, tm, var23, lam23, app23 => app23 _ _ _ (t tm var23 lam23 app23) (u tm var23 lam23 app23)

v023 : {g:_}->{a:_} -> Tm23 (snoc23 g a) a
v023 = var23 vz23

v123 : {g:_}->{a:_}-> {B:_}-> Tm23 (snoc23 (snoc23 g a) B) a
v123 = var23 (vs23 vz23)

v223 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm23 (snoc23 (snoc23 (snoc23 g a) B) C) a
v223 = var23 (vs23 (vs23 vz23))

v323 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm23 (snoc23 (snoc23 (snoc23 (snoc23 g a) B) C) D) a
v323 = var23 (vs23 (vs23 (vs23 vz23)))

v423 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm23 (snoc23 (snoc23 (snoc23 (snoc23 (snoc23 g a) B) C) D) E) a
v423 = var23 (vs23 (vs23 (vs23 (vs23 vz23))))

test23 : {g:_}-> {a:_} -> Tm23 g (arr23 (arr23 a a) (arr23 a a))
test23  = lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023)))))))
Ty24 : Type
Ty24 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty24 : Ty24
empty24 = \ _, empty, _ => empty

arr24 : Ty24 -> Ty24 -> Ty24
arr24 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con24 : Type
Con24 = (Con24 : Type)
 ->(nil  : Con24)
 ->(snoc : Con24 -> Ty24 -> Con24)
 -> Con24

nil24 : Con24
nil24 = \ con, nil24, snoc => nil24

snoc24 : Con24 -> Ty24 -> Con24
snoc24 = \ g, a, con, nil24, snoc24 => snoc24 (g con nil24 snoc24) a

Var24 : Con24 -> Ty24 -> Type
Var24 = \ g, a =>
    (Var24 : Con24 -> Ty24 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var24 (snoc24 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var24 g a -> Var24 (snoc24 g b) a)
 -> Var24 g a

vz24 : {g : _}-> {a : _} -> Var24 (snoc24 g a) a
vz24 = \ var, vz24, vs => vz24 _ _

vs24 : {g : _} -> {B : _} -> {a : _} -> Var24 g a -> Var24 (snoc24 g B) a
vs24 = \ x, var, vz24, vs24 => vs24 _ _ _ (x var vz24 vs24)

Tm24 : Con24 -> Ty24 -> Type
Tm24 = \ g, a =>
    (Tm24    : Con24 -> Ty24 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var24 g a -> Tm24 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm24 (snoc24 g a) B -> Tm24 g (arr24 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm24 g (arr24 a B) -> Tm24 g a -> Tm24 g B)
 -> Tm24 g a

var24 : {g : _} -> {a : _} -> Var24 g a -> Tm24 g a
var24 = \ x, tm, var24, lam, app => var24 _ _ x

lam24 : {g : _} -> {a : _} -> {B : _} -> Tm24 (snoc24 g a) B -> Tm24 g (arr24 a B)
lam24 = \ t, tm, var24, lam24, app => lam24 _ _ _ (t tm var24 lam24 app)

app24 : {g:_}->{a:_}->{B:_} -> Tm24 g (arr24 a B) -> Tm24 g a -> Tm24 g B
app24 = \ t, u, tm, var24, lam24, app24 => app24 _ _ _ (t tm var24 lam24 app24) (u tm var24 lam24 app24)

v024 : {g:_}->{a:_} -> Tm24 (snoc24 g a) a
v024 = var24 vz24

v124 : {g:_}->{a:_}-> {B:_}-> Tm24 (snoc24 (snoc24 g a) B) a
v124 = var24 (vs24 vz24)

v224 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm24 (snoc24 (snoc24 (snoc24 g a) B) C) a
v224 = var24 (vs24 (vs24 vz24))

v324 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm24 (snoc24 (snoc24 (snoc24 (snoc24 g a) B) C) D) a
v324 = var24 (vs24 (vs24 (vs24 vz24)))

v424 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm24 (snoc24 (snoc24 (snoc24 (snoc24 (snoc24 g a) B) C) D) E) a
v424 = var24 (vs24 (vs24 (vs24 (vs24 vz24))))

test24 : {g:_}-> {a:_} -> Tm24 g (arr24 (arr24 a a) (arr24 a a))
test24  = lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024)))))))
Ty25 : Type
Ty25 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty25 : Ty25
empty25 = \ _, empty, _ => empty

arr25 : Ty25 -> Ty25 -> Ty25
arr25 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con25 : Type
Con25 = (Con25 : Type)
 ->(nil  : Con25)
 ->(snoc : Con25 -> Ty25 -> Con25)
 -> Con25

nil25 : Con25
nil25 = \ con, nil25, snoc => nil25

snoc25 : Con25 -> Ty25 -> Con25
snoc25 = \ g, a, con, nil25, snoc25 => snoc25 (g con nil25 snoc25) a

Var25 : Con25 -> Ty25 -> Type
Var25 = \ g, a =>
    (Var25 : Con25 -> Ty25 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var25 (snoc25 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var25 g a -> Var25 (snoc25 g b) a)
 -> Var25 g a

vz25 : {g : _}-> {a : _} -> Var25 (snoc25 g a) a
vz25 = \ var, vz25, vs => vz25 _ _

vs25 : {g : _} -> {B : _} -> {a : _} -> Var25 g a -> Var25 (snoc25 g B) a
vs25 = \ x, var, vz25, vs25 => vs25 _ _ _ (x var vz25 vs25)

Tm25 : Con25 -> Ty25 -> Type
Tm25 = \ g, a =>
    (Tm25    : Con25 -> Ty25 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var25 g a -> Tm25 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm25 (snoc25 g a) B -> Tm25 g (arr25 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm25 g (arr25 a B) -> Tm25 g a -> Tm25 g B)
 -> Tm25 g a

var25 : {g : _} -> {a : _} -> Var25 g a -> Tm25 g a
var25 = \ x, tm, var25, lam, app => var25 _ _ x

lam25 : {g : _} -> {a : _} -> {B : _} -> Tm25 (snoc25 g a) B -> Tm25 g (arr25 a B)
lam25 = \ t, tm, var25, lam25, app => lam25 _ _ _ (t tm var25 lam25 app)

app25 : {g:_}->{a:_}->{B:_} -> Tm25 g (arr25 a B) -> Tm25 g a -> Tm25 g B
app25 = \ t, u, tm, var25, lam25, app25 => app25 _ _ _ (t tm var25 lam25 app25) (u tm var25 lam25 app25)

v025 : {g:_}->{a:_} -> Tm25 (snoc25 g a) a
v025 = var25 vz25

v125 : {g:_}->{a:_}-> {B:_}-> Tm25 (snoc25 (snoc25 g a) B) a
v125 = var25 (vs25 vz25)

v225 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm25 (snoc25 (snoc25 (snoc25 g a) B) C) a
v225 = var25 (vs25 (vs25 vz25))

v325 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm25 (snoc25 (snoc25 (snoc25 (snoc25 g a) B) C) D) a
v325 = var25 (vs25 (vs25 (vs25 vz25)))

v425 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm25 (snoc25 (snoc25 (snoc25 (snoc25 (snoc25 g a) B) C) D) E) a
v425 = var25 (vs25 (vs25 (vs25 (vs25 vz25))))

test25 : {g:_}-> {a:_} -> Tm25 g (arr25 (arr25 a a) (arr25 a a))
test25  = lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025)))))))
Ty26 : Type
Ty26 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty26 : Ty26
empty26 = \ _, empty, _ => empty

arr26 : Ty26 -> Ty26 -> Ty26
arr26 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con26 : Type
Con26 = (Con26 : Type)
 ->(nil  : Con26)
 ->(snoc : Con26 -> Ty26 -> Con26)
 -> Con26

nil26 : Con26
nil26 = \ con, nil26, snoc => nil26

snoc26 : Con26 -> Ty26 -> Con26
snoc26 = \ g, a, con, nil26, snoc26 => snoc26 (g con nil26 snoc26) a

Var26 : Con26 -> Ty26 -> Type
Var26 = \ g, a =>
    (Var26 : Con26 -> Ty26 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var26 (snoc26 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var26 g a -> Var26 (snoc26 g b) a)
 -> Var26 g a

vz26 : {g : _}-> {a : _} -> Var26 (snoc26 g a) a
vz26 = \ var, vz26, vs => vz26 _ _

vs26 : {g : _} -> {B : _} -> {a : _} -> Var26 g a -> Var26 (snoc26 g B) a
vs26 = \ x, var, vz26, vs26 => vs26 _ _ _ (x var vz26 vs26)

Tm26 : Con26 -> Ty26 -> Type
Tm26 = \ g, a =>
    (Tm26    : Con26 -> Ty26 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var26 g a -> Tm26 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm26 (snoc26 g a) B -> Tm26 g (arr26 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm26 g (arr26 a B) -> Tm26 g a -> Tm26 g B)
 -> Tm26 g a

var26 : {g : _} -> {a : _} -> Var26 g a -> Tm26 g a
var26 = \ x, tm, var26, lam, app => var26 _ _ x

lam26 : {g : _} -> {a : _} -> {B : _} -> Tm26 (snoc26 g a) B -> Tm26 g (arr26 a B)
lam26 = \ t, tm, var26, lam26, app => lam26 _ _ _ (t tm var26 lam26 app)

app26 : {g:_}->{a:_}->{B:_} -> Tm26 g (arr26 a B) -> Tm26 g a -> Tm26 g B
app26 = \ t, u, tm, var26, lam26, app26 => app26 _ _ _ (t tm var26 lam26 app26) (u tm var26 lam26 app26)

v026 : {g:_}->{a:_} -> Tm26 (snoc26 g a) a
v026 = var26 vz26

v126 : {g:_}->{a:_}-> {B:_}-> Tm26 (snoc26 (snoc26 g a) B) a
v126 = var26 (vs26 vz26)

v226 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm26 (snoc26 (snoc26 (snoc26 g a) B) C) a
v226 = var26 (vs26 (vs26 vz26))

v326 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm26 (snoc26 (snoc26 (snoc26 (snoc26 g a) B) C) D) a
v326 = var26 (vs26 (vs26 (vs26 vz26)))

v426 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm26 (snoc26 (snoc26 (snoc26 (snoc26 (snoc26 g a) B) C) D) E) a
v426 = var26 (vs26 (vs26 (vs26 (vs26 vz26))))

test26 : {g:_}-> {a:_} -> Tm26 g (arr26 (arr26 a a) (arr26 a a))
test26  = lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026)))))))
Ty27 : Type
Ty27 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty27 : Ty27
empty27 = \ _, empty, _ => empty

arr27 : Ty27 -> Ty27 -> Ty27
arr27 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con27 : Type
Con27 = (Con27 : Type)
 ->(nil  : Con27)
 ->(snoc : Con27 -> Ty27 -> Con27)
 -> Con27

nil27 : Con27
nil27 = \ con, nil27, snoc => nil27

snoc27 : Con27 -> Ty27 -> Con27
snoc27 = \ g, a, con, nil27, snoc27 => snoc27 (g con nil27 snoc27) a

Var27 : Con27 -> Ty27 -> Type
Var27 = \ g, a =>
    (Var27 : Con27 -> Ty27 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var27 (snoc27 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var27 g a -> Var27 (snoc27 g b) a)
 -> Var27 g a

vz27 : {g : _}-> {a : _} -> Var27 (snoc27 g a) a
vz27 = \ var, vz27, vs => vz27 _ _

vs27 : {g : _} -> {B : _} -> {a : _} -> Var27 g a -> Var27 (snoc27 g B) a
vs27 = \ x, var, vz27, vs27 => vs27 _ _ _ (x var vz27 vs27)

Tm27 : Con27 -> Ty27 -> Type
Tm27 = \ g, a =>
    (Tm27    : Con27 -> Ty27 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var27 g a -> Tm27 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm27 (snoc27 g a) B -> Tm27 g (arr27 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm27 g (arr27 a B) -> Tm27 g a -> Tm27 g B)
 -> Tm27 g a

var27 : {g : _} -> {a : _} -> Var27 g a -> Tm27 g a
var27 = \ x, tm, var27, lam, app => var27 _ _ x

lam27 : {g : _} -> {a : _} -> {B : _} -> Tm27 (snoc27 g a) B -> Tm27 g (arr27 a B)
lam27 = \ t, tm, var27, lam27, app => lam27 _ _ _ (t tm var27 lam27 app)

app27 : {g:_}->{a:_}->{B:_} -> Tm27 g (arr27 a B) -> Tm27 g a -> Tm27 g B
app27 = \ t, u, tm, var27, lam27, app27 => app27 _ _ _ (t tm var27 lam27 app27) (u tm var27 lam27 app27)

v027 : {g:_}->{a:_} -> Tm27 (snoc27 g a) a
v027 = var27 vz27

v127 : {g:_}->{a:_}-> {B:_}-> Tm27 (snoc27 (snoc27 g a) B) a
v127 = var27 (vs27 vz27)

v227 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm27 (snoc27 (snoc27 (snoc27 g a) B) C) a
v227 = var27 (vs27 (vs27 vz27))

v327 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm27 (snoc27 (snoc27 (snoc27 (snoc27 g a) B) C) D) a
v327 = var27 (vs27 (vs27 (vs27 vz27)))

v427 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm27 (snoc27 (snoc27 (snoc27 (snoc27 (snoc27 g a) B) C) D) E) a
v427 = var27 (vs27 (vs27 (vs27 (vs27 vz27))))

test27 : {g:_}-> {a:_} -> Tm27 g (arr27 (arr27 a a) (arr27 a a))
test27  = lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027)))))))
Ty28 : Type
Ty28 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty28 : Ty28
empty28 = \ _, empty, _ => empty

arr28 : Ty28 -> Ty28 -> Ty28
arr28 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con28 : Type
Con28 = (Con28 : Type)
 ->(nil  : Con28)
 ->(snoc : Con28 -> Ty28 -> Con28)
 -> Con28

nil28 : Con28
nil28 = \ con, nil28, snoc => nil28

snoc28 : Con28 -> Ty28 -> Con28
snoc28 = \ g, a, con, nil28, snoc28 => snoc28 (g con nil28 snoc28) a

Var28 : Con28 -> Ty28 -> Type
Var28 = \ g, a =>
    (Var28 : Con28 -> Ty28 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var28 (snoc28 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var28 g a -> Var28 (snoc28 g b) a)
 -> Var28 g a

vz28 : {g : _}-> {a : _} -> Var28 (snoc28 g a) a
vz28 = \ var, vz28, vs => vz28 _ _

vs28 : {g : _} -> {B : _} -> {a : _} -> Var28 g a -> Var28 (snoc28 g B) a
vs28 = \ x, var, vz28, vs28 => vs28 _ _ _ (x var vz28 vs28)

Tm28 : Con28 -> Ty28 -> Type
Tm28 = \ g, a =>
    (Tm28    : Con28 -> Ty28 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var28 g a -> Tm28 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm28 (snoc28 g a) B -> Tm28 g (arr28 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm28 g (arr28 a B) -> Tm28 g a -> Tm28 g B)
 -> Tm28 g a

var28 : {g : _} -> {a : _} -> Var28 g a -> Tm28 g a
var28 = \ x, tm, var28, lam, app => var28 _ _ x

lam28 : {g : _} -> {a : _} -> {B : _} -> Tm28 (snoc28 g a) B -> Tm28 g (arr28 a B)
lam28 = \ t, tm, var28, lam28, app => lam28 _ _ _ (t tm var28 lam28 app)

app28 : {g:_}->{a:_}->{B:_} -> Tm28 g (arr28 a B) -> Tm28 g a -> Tm28 g B
app28 = \ t, u, tm, var28, lam28, app28 => app28 _ _ _ (t tm var28 lam28 app28) (u tm var28 lam28 app28)

v028 : {g:_}->{a:_} -> Tm28 (snoc28 g a) a
v028 = var28 vz28

v128 : {g:_}->{a:_}-> {B:_}-> Tm28 (snoc28 (snoc28 g a) B) a
v128 = var28 (vs28 vz28)

v228 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm28 (snoc28 (snoc28 (snoc28 g a) B) C) a
v228 = var28 (vs28 (vs28 vz28))

v328 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm28 (snoc28 (snoc28 (snoc28 (snoc28 g a) B) C) D) a
v328 = var28 (vs28 (vs28 (vs28 vz28)))

v428 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm28 (snoc28 (snoc28 (snoc28 (snoc28 (snoc28 g a) B) C) D) E) a
v428 = var28 (vs28 (vs28 (vs28 (vs28 vz28))))

test28 : {g:_}-> {a:_} -> Tm28 g (arr28 (arr28 a a) (arr28 a a))
test28  = lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028)))))))
Ty29 : Type
Ty29 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty29 : Ty29
empty29 = \ _, empty, _ => empty

arr29 : Ty29 -> Ty29 -> Ty29
arr29 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con29 : Type
Con29 = (Con29 : Type)
 ->(nil  : Con29)
 ->(snoc : Con29 -> Ty29 -> Con29)
 -> Con29

nil29 : Con29
nil29 = \ con, nil29, snoc => nil29

snoc29 : Con29 -> Ty29 -> Con29
snoc29 = \ g, a, con, nil29, snoc29 => snoc29 (g con nil29 snoc29) a

Var29 : Con29 -> Ty29 -> Type
Var29 = \ g, a =>
    (Var29 : Con29 -> Ty29 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var29 (snoc29 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var29 g a -> Var29 (snoc29 g b) a)
 -> Var29 g a

vz29 : {g : _}-> {a : _} -> Var29 (snoc29 g a) a
vz29 = \ var, vz29, vs => vz29 _ _

vs29 : {g : _} -> {B : _} -> {a : _} -> Var29 g a -> Var29 (snoc29 g B) a
vs29 = \ x, var, vz29, vs29 => vs29 _ _ _ (x var vz29 vs29)

Tm29 : Con29 -> Ty29 -> Type
Tm29 = \ g, a =>
    (Tm29    : Con29 -> Ty29 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var29 g a -> Tm29 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm29 (snoc29 g a) B -> Tm29 g (arr29 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm29 g (arr29 a B) -> Tm29 g a -> Tm29 g B)
 -> Tm29 g a

var29 : {g : _} -> {a : _} -> Var29 g a -> Tm29 g a
var29 = \ x, tm, var29, lam, app => var29 _ _ x

lam29 : {g : _} -> {a : _} -> {B : _} -> Tm29 (snoc29 g a) B -> Tm29 g (arr29 a B)
lam29 = \ t, tm, var29, lam29, app => lam29 _ _ _ (t tm var29 lam29 app)

app29 : {g:_}->{a:_}->{B:_} -> Tm29 g (arr29 a B) -> Tm29 g a -> Tm29 g B
app29 = \ t, u, tm, var29, lam29, app29 => app29 _ _ _ (t tm var29 lam29 app29) (u tm var29 lam29 app29)

v029 : {g:_}->{a:_} -> Tm29 (snoc29 g a) a
v029 = var29 vz29

v129 : {g:_}->{a:_}-> {B:_}-> Tm29 (snoc29 (snoc29 g a) B) a
v129 = var29 (vs29 vz29)

v229 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm29 (snoc29 (snoc29 (snoc29 g a) B) C) a
v229 = var29 (vs29 (vs29 vz29))

v329 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm29 (snoc29 (snoc29 (snoc29 (snoc29 g a) B) C) D) a
v329 = var29 (vs29 (vs29 (vs29 vz29)))

v429 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm29 (snoc29 (snoc29 (snoc29 (snoc29 (snoc29 g a) B) C) D) E) a
v429 = var29 (vs29 (vs29 (vs29 (vs29 vz29))))

test29 : {g:_}-> {a:_} -> Tm29 g (arr29 (arr29 a a) (arr29 a a))
test29  = lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029)))))))
Ty30 : Type
Ty30 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty30 : Ty30
empty30 = \ _, empty, _ => empty

arr30 : Ty30 -> Ty30 -> Ty30
arr30 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con30 : Type
Con30 = (Con30 : Type)
 ->(nil  : Con30)
 ->(snoc : Con30 -> Ty30 -> Con30)
 -> Con30

nil30 : Con30
nil30 = \ con, nil30, snoc => nil30

snoc30 : Con30 -> Ty30 -> Con30
snoc30 = \ g, a, con, nil30, snoc30 => snoc30 (g con nil30 snoc30) a

Var30 : Con30 -> Ty30 -> Type
Var30 = \ g, a =>
    (Var30 : Con30 -> Ty30 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var30 (snoc30 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var30 g a -> Var30 (snoc30 g b) a)
 -> Var30 g a

vz30 : {g : _}-> {a : _} -> Var30 (snoc30 g a) a
vz30 = \ var, vz30, vs => vz30 _ _

vs30 : {g : _} -> {B : _} -> {a : _} -> Var30 g a -> Var30 (snoc30 g B) a
vs30 = \ x, var, vz30, vs30 => vs30 _ _ _ (x var vz30 vs30)

Tm30 : Con30 -> Ty30 -> Type
Tm30 = \ g, a =>
    (Tm30    : Con30 -> Ty30 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var30 g a -> Tm30 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm30 (snoc30 g a) B -> Tm30 g (arr30 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm30 g (arr30 a B) -> Tm30 g a -> Tm30 g B)
 -> Tm30 g a

var30 : {g : _} -> {a : _} -> Var30 g a -> Tm30 g a
var30 = \ x, tm, var30, lam, app => var30 _ _ x

lam30 : {g : _} -> {a : _} -> {B : _} -> Tm30 (snoc30 g a) B -> Tm30 g (arr30 a B)
lam30 = \ t, tm, var30, lam30, app => lam30 _ _ _ (t tm var30 lam30 app)

app30 : {g:_}->{a:_}->{B:_} -> Tm30 g (arr30 a B) -> Tm30 g a -> Tm30 g B
app30 = \ t, u, tm, var30, lam30, app30 => app30 _ _ _ (t tm var30 lam30 app30) (u tm var30 lam30 app30)

v030 : {g:_}->{a:_} -> Tm30 (snoc30 g a) a
v030 = var30 vz30

v130 : {g:_}->{a:_}-> {B:_}-> Tm30 (snoc30 (snoc30 g a) B) a
v130 = var30 (vs30 vz30)

v230 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm30 (snoc30 (snoc30 (snoc30 g a) B) C) a
v230 = var30 (vs30 (vs30 vz30))

v330 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm30 (snoc30 (snoc30 (snoc30 (snoc30 g a) B) C) D) a
v330 = var30 (vs30 (vs30 (vs30 vz30)))

v430 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm30 (snoc30 (snoc30 (snoc30 (snoc30 (snoc30 g a) B) C) D) E) a
v430 = var30 (vs30 (vs30 (vs30 (vs30 vz30))))

test30 : {g:_}-> {a:_} -> Tm30 g (arr30 (arr30 a a) (arr30 a a))
test30  = lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030)))))))
Ty31 : Type
Ty31 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty31 : Ty31
empty31 = \ _, empty, _ => empty

arr31 : Ty31 -> Ty31 -> Ty31
arr31 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con31 : Type
Con31 = (Con31 : Type)
 ->(nil  : Con31)
 ->(snoc : Con31 -> Ty31 -> Con31)
 -> Con31

nil31 : Con31
nil31 = \ con, nil31, snoc => nil31

snoc31 : Con31 -> Ty31 -> Con31
snoc31 = \ g, a, con, nil31, snoc31 => snoc31 (g con nil31 snoc31) a

Var31 : Con31 -> Ty31 -> Type
Var31 = \ g, a =>
    (Var31 : Con31 -> Ty31 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var31 (snoc31 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var31 g a -> Var31 (snoc31 g b) a)
 -> Var31 g a

vz31 : {g : _}-> {a : _} -> Var31 (snoc31 g a) a
vz31 = \ var, vz31, vs => vz31 _ _

vs31 : {g : _} -> {B : _} -> {a : _} -> Var31 g a -> Var31 (snoc31 g B) a
vs31 = \ x, var, vz31, vs31 => vs31 _ _ _ (x var vz31 vs31)

Tm31 : Con31 -> Ty31 -> Type
Tm31 = \ g, a =>
    (Tm31    : Con31 -> Ty31 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var31 g a -> Tm31 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm31 (snoc31 g a) B -> Tm31 g (arr31 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm31 g (arr31 a B) -> Tm31 g a -> Tm31 g B)
 -> Tm31 g a

var31 : {g : _} -> {a : _} -> Var31 g a -> Tm31 g a
var31 = \ x, tm, var31, lam, app => var31 _ _ x

lam31 : {g : _} -> {a : _} -> {B : _} -> Tm31 (snoc31 g a) B -> Tm31 g (arr31 a B)
lam31 = \ t, tm, var31, lam31, app => lam31 _ _ _ (t tm var31 lam31 app)

app31 : {g:_}->{a:_}->{B:_} -> Tm31 g (arr31 a B) -> Tm31 g a -> Tm31 g B
app31 = \ t, u, tm, var31, lam31, app31 => app31 _ _ _ (t tm var31 lam31 app31) (u tm var31 lam31 app31)

v031 : {g:_}->{a:_} -> Tm31 (snoc31 g a) a
v031 = var31 vz31

v131 : {g:_}->{a:_}-> {B:_}-> Tm31 (snoc31 (snoc31 g a) B) a
v131 = var31 (vs31 vz31)

v231 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm31 (snoc31 (snoc31 (snoc31 g a) B) C) a
v231 = var31 (vs31 (vs31 vz31))

v331 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm31 (snoc31 (snoc31 (snoc31 (snoc31 g a) B) C) D) a
v331 = var31 (vs31 (vs31 (vs31 vz31)))

v431 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm31 (snoc31 (snoc31 (snoc31 (snoc31 (snoc31 g a) B) C) D) E) a
v431 = var31 (vs31 (vs31 (vs31 (vs31 vz31))))

test31 : {g:_}-> {a:_} -> Tm31 g (arr31 (arr31 a a) (arr31 a a))
test31  = lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031)))))))
Ty32 : Type
Ty32 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty32 : Ty32
empty32 = \ _, empty, _ => empty

arr32 : Ty32 -> Ty32 -> Ty32
arr32 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con32 : Type
Con32 = (Con32 : Type)
 ->(nil  : Con32)
 ->(snoc : Con32 -> Ty32 -> Con32)
 -> Con32

nil32 : Con32
nil32 = \ con, nil32, snoc => nil32

snoc32 : Con32 -> Ty32 -> Con32
snoc32 = \ g, a, con, nil32, snoc32 => snoc32 (g con nil32 snoc32) a

Var32 : Con32 -> Ty32 -> Type
Var32 = \ g, a =>
    (Var32 : Con32 -> Ty32 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var32 (snoc32 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var32 g a -> Var32 (snoc32 g b) a)
 -> Var32 g a

vz32 : {g : _}-> {a : _} -> Var32 (snoc32 g a) a
vz32 = \ var, vz32, vs => vz32 _ _

vs32 : {g : _} -> {B : _} -> {a : _} -> Var32 g a -> Var32 (snoc32 g B) a
vs32 = \ x, var, vz32, vs32 => vs32 _ _ _ (x var vz32 vs32)

Tm32 : Con32 -> Ty32 -> Type
Tm32 = \ g, a =>
    (Tm32    : Con32 -> Ty32 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var32 g a -> Tm32 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm32 (snoc32 g a) B -> Tm32 g (arr32 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm32 g (arr32 a B) -> Tm32 g a -> Tm32 g B)
 -> Tm32 g a

var32 : {g : _} -> {a : _} -> Var32 g a -> Tm32 g a
var32 = \ x, tm, var32, lam, app => var32 _ _ x

lam32 : {g : _} -> {a : _} -> {B : _} -> Tm32 (snoc32 g a) B -> Tm32 g (arr32 a B)
lam32 = \ t, tm, var32, lam32, app => lam32 _ _ _ (t tm var32 lam32 app)

app32 : {g:_}->{a:_}->{B:_} -> Tm32 g (arr32 a B) -> Tm32 g a -> Tm32 g B
app32 = \ t, u, tm, var32, lam32, app32 => app32 _ _ _ (t tm var32 lam32 app32) (u tm var32 lam32 app32)

v032 : {g:_}->{a:_} -> Tm32 (snoc32 g a) a
v032 = var32 vz32

v132 : {g:_}->{a:_}-> {B:_}-> Tm32 (snoc32 (snoc32 g a) B) a
v132 = var32 (vs32 vz32)

v232 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm32 (snoc32 (snoc32 (snoc32 g a) B) C) a
v232 = var32 (vs32 (vs32 vz32))

v332 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm32 (snoc32 (snoc32 (snoc32 (snoc32 g a) B) C) D) a
v332 = var32 (vs32 (vs32 (vs32 vz32)))

v432 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm32 (snoc32 (snoc32 (snoc32 (snoc32 (snoc32 g a) B) C) D) E) a
v432 = var32 (vs32 (vs32 (vs32 (vs32 vz32))))

test32 : {g:_}-> {a:_} -> Tm32 g (arr32 (arr32 a a) (arr32 a a))
test32  = lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032)))))))
Ty33 : Type
Ty33 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty33 : Ty33
empty33 = \ _, empty, _ => empty

arr33 : Ty33 -> Ty33 -> Ty33
arr33 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con33 : Type
Con33 = (Con33 : Type)
 ->(nil  : Con33)
 ->(snoc : Con33 -> Ty33 -> Con33)
 -> Con33

nil33 : Con33
nil33 = \ con, nil33, snoc => nil33

snoc33 : Con33 -> Ty33 -> Con33
snoc33 = \ g, a, con, nil33, snoc33 => snoc33 (g con nil33 snoc33) a

Var33 : Con33 -> Ty33 -> Type
Var33 = \ g, a =>
    (Var33 : Con33 -> Ty33 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var33 (snoc33 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var33 g a -> Var33 (snoc33 g b) a)
 -> Var33 g a

vz33 : {g : _}-> {a : _} -> Var33 (snoc33 g a) a
vz33 = \ var, vz33, vs => vz33 _ _

vs33 : {g : _} -> {B : _} -> {a : _} -> Var33 g a -> Var33 (snoc33 g B) a
vs33 = \ x, var, vz33, vs33 => vs33 _ _ _ (x var vz33 vs33)

Tm33 : Con33 -> Ty33 -> Type
Tm33 = \ g, a =>
    (Tm33    : Con33 -> Ty33 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var33 g a -> Tm33 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm33 (snoc33 g a) B -> Tm33 g (arr33 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm33 g (arr33 a B) -> Tm33 g a -> Tm33 g B)
 -> Tm33 g a

var33 : {g : _} -> {a : _} -> Var33 g a -> Tm33 g a
var33 = \ x, tm, var33, lam, app => var33 _ _ x

lam33 : {g : _} -> {a : _} -> {B : _} -> Tm33 (snoc33 g a) B -> Tm33 g (arr33 a B)
lam33 = \ t, tm, var33, lam33, app => lam33 _ _ _ (t tm var33 lam33 app)

app33 : {g:_}->{a:_}->{B:_} -> Tm33 g (arr33 a B) -> Tm33 g a -> Tm33 g B
app33 = \ t, u, tm, var33, lam33, app33 => app33 _ _ _ (t tm var33 lam33 app33) (u tm var33 lam33 app33)

v033 : {g:_}->{a:_} -> Tm33 (snoc33 g a) a
v033 = var33 vz33

v133 : {g:_}->{a:_}-> {B:_}-> Tm33 (snoc33 (snoc33 g a) B) a
v133 = var33 (vs33 vz33)

v233 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm33 (snoc33 (snoc33 (snoc33 g a) B) C) a
v233 = var33 (vs33 (vs33 vz33))

v333 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm33 (snoc33 (snoc33 (snoc33 (snoc33 g a) B) C) D) a
v333 = var33 (vs33 (vs33 (vs33 vz33)))

v433 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm33 (snoc33 (snoc33 (snoc33 (snoc33 (snoc33 g a) B) C) D) E) a
v433 = var33 (vs33 (vs33 (vs33 (vs33 vz33))))

test33 : {g:_}-> {a:_} -> Tm33 g (arr33 (arr33 a a) (arr33 a a))
test33  = lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033)))))))
Ty34 : Type
Ty34 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty34 : Ty34
empty34 = \ _, empty, _ => empty

arr34 : Ty34 -> Ty34 -> Ty34
arr34 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con34 : Type
Con34 = (Con34 : Type)
 ->(nil  : Con34)
 ->(snoc : Con34 -> Ty34 -> Con34)
 -> Con34

nil34 : Con34
nil34 = \ con, nil34, snoc => nil34

snoc34 : Con34 -> Ty34 -> Con34
snoc34 = \ g, a, con, nil34, snoc34 => snoc34 (g con nil34 snoc34) a

Var34 : Con34 -> Ty34 -> Type
Var34 = \ g, a =>
    (Var34 : Con34 -> Ty34 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var34 (snoc34 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var34 g a -> Var34 (snoc34 g b) a)
 -> Var34 g a

vz34 : {g : _}-> {a : _} -> Var34 (snoc34 g a) a
vz34 = \ var, vz34, vs => vz34 _ _

vs34 : {g : _} -> {B : _} -> {a : _} -> Var34 g a -> Var34 (snoc34 g B) a
vs34 = \ x, var, vz34, vs34 => vs34 _ _ _ (x var vz34 vs34)

Tm34 : Con34 -> Ty34 -> Type
Tm34 = \ g, a =>
    (Tm34    : Con34 -> Ty34 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var34 g a -> Tm34 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm34 (snoc34 g a) B -> Tm34 g (arr34 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm34 g (arr34 a B) -> Tm34 g a -> Tm34 g B)
 -> Tm34 g a

var34 : {g : _} -> {a : _} -> Var34 g a -> Tm34 g a
var34 = \ x, tm, var34, lam, app => var34 _ _ x

lam34 : {g : _} -> {a : _} -> {B : _} -> Tm34 (snoc34 g a) B -> Tm34 g (arr34 a B)
lam34 = \ t, tm, var34, lam34, app => lam34 _ _ _ (t tm var34 lam34 app)

app34 : {g:_}->{a:_}->{B:_} -> Tm34 g (arr34 a B) -> Tm34 g a -> Tm34 g B
app34 = \ t, u, tm, var34, lam34, app34 => app34 _ _ _ (t tm var34 lam34 app34) (u tm var34 lam34 app34)

v034 : {g:_}->{a:_} -> Tm34 (snoc34 g a) a
v034 = var34 vz34

v134 : {g:_}->{a:_}-> {B:_}-> Tm34 (snoc34 (snoc34 g a) B) a
v134 = var34 (vs34 vz34)

v234 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm34 (snoc34 (snoc34 (snoc34 g a) B) C) a
v234 = var34 (vs34 (vs34 vz34))

v334 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm34 (snoc34 (snoc34 (snoc34 (snoc34 g a) B) C) D) a
v334 = var34 (vs34 (vs34 (vs34 vz34)))

v434 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm34 (snoc34 (snoc34 (snoc34 (snoc34 (snoc34 g a) B) C) D) E) a
v434 = var34 (vs34 (vs34 (vs34 (vs34 vz34))))

test34 : {g:_}-> {a:_} -> Tm34 g (arr34 (arr34 a a) (arr34 a a))
test34  = lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034)))))))
Ty35 : Type
Ty35 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty35 : Ty35
empty35 = \ _, empty, _ => empty

arr35 : Ty35 -> Ty35 -> Ty35
arr35 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con35 : Type
Con35 = (Con35 : Type)
 ->(nil  : Con35)
 ->(snoc : Con35 -> Ty35 -> Con35)
 -> Con35

nil35 : Con35
nil35 = \ con, nil35, snoc => nil35

snoc35 : Con35 -> Ty35 -> Con35
snoc35 = \ g, a, con, nil35, snoc35 => snoc35 (g con nil35 snoc35) a

Var35 : Con35 -> Ty35 -> Type
Var35 = \ g, a =>
    (Var35 : Con35 -> Ty35 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var35 (snoc35 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var35 g a -> Var35 (snoc35 g b) a)
 -> Var35 g a

vz35 : {g : _}-> {a : _} -> Var35 (snoc35 g a) a
vz35 = \ var, vz35, vs => vz35 _ _

vs35 : {g : _} -> {B : _} -> {a : _} -> Var35 g a -> Var35 (snoc35 g B) a
vs35 = \ x, var, vz35, vs35 => vs35 _ _ _ (x var vz35 vs35)

Tm35 : Con35 -> Ty35 -> Type
Tm35 = \ g, a =>
    (Tm35    : Con35 -> Ty35 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var35 g a -> Tm35 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm35 (snoc35 g a) B -> Tm35 g (arr35 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm35 g (arr35 a B) -> Tm35 g a -> Tm35 g B)
 -> Tm35 g a

var35 : {g : _} -> {a : _} -> Var35 g a -> Tm35 g a
var35 = \ x, tm, var35, lam, app => var35 _ _ x

lam35 : {g : _} -> {a : _} -> {B : _} -> Tm35 (snoc35 g a) B -> Tm35 g (arr35 a B)
lam35 = \ t, tm, var35, lam35, app => lam35 _ _ _ (t tm var35 lam35 app)

app35 : {g:_}->{a:_}->{B:_} -> Tm35 g (arr35 a B) -> Tm35 g a -> Tm35 g B
app35 = \ t, u, tm, var35, lam35, app35 => app35 _ _ _ (t tm var35 lam35 app35) (u tm var35 lam35 app35)

v035 : {g:_}->{a:_} -> Tm35 (snoc35 g a) a
v035 = var35 vz35

v135 : {g:_}->{a:_}-> {B:_}-> Tm35 (snoc35 (snoc35 g a) B) a
v135 = var35 (vs35 vz35)

v235 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm35 (snoc35 (snoc35 (snoc35 g a) B) C) a
v235 = var35 (vs35 (vs35 vz35))

v335 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm35 (snoc35 (snoc35 (snoc35 (snoc35 g a) B) C) D) a
v335 = var35 (vs35 (vs35 (vs35 vz35)))

v435 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm35 (snoc35 (snoc35 (snoc35 (snoc35 (snoc35 g a) B) C) D) E) a
v435 = var35 (vs35 (vs35 (vs35 (vs35 vz35))))

test35 : {g:_}-> {a:_} -> Tm35 g (arr35 (arr35 a a) (arr35 a a))
test35  = lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035)))))))
Ty36 : Type
Ty36 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty36 : Ty36
empty36 = \ _, empty, _ => empty

arr36 : Ty36 -> Ty36 -> Ty36
arr36 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con36 : Type
Con36 = (Con36 : Type)
 ->(nil  : Con36)
 ->(snoc : Con36 -> Ty36 -> Con36)
 -> Con36

nil36 : Con36
nil36 = \ con, nil36, snoc => nil36

snoc36 : Con36 -> Ty36 -> Con36
snoc36 = \ g, a, con, nil36, snoc36 => snoc36 (g con nil36 snoc36) a

Var36 : Con36 -> Ty36 -> Type
Var36 = \ g, a =>
    (Var36 : Con36 -> Ty36 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var36 (snoc36 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var36 g a -> Var36 (snoc36 g b) a)
 -> Var36 g a

vz36 : {g : _}-> {a : _} -> Var36 (snoc36 g a) a
vz36 = \ var, vz36, vs => vz36 _ _

vs36 : {g : _} -> {B : _} -> {a : _} -> Var36 g a -> Var36 (snoc36 g B) a
vs36 = \ x, var, vz36, vs36 => vs36 _ _ _ (x var vz36 vs36)

Tm36 : Con36 -> Ty36 -> Type
Tm36 = \ g, a =>
    (Tm36    : Con36 -> Ty36 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var36 g a -> Tm36 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm36 (snoc36 g a) B -> Tm36 g (arr36 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm36 g (arr36 a B) -> Tm36 g a -> Tm36 g B)
 -> Tm36 g a

var36 : {g : _} -> {a : _} -> Var36 g a -> Tm36 g a
var36 = \ x, tm, var36, lam, app => var36 _ _ x

lam36 : {g : _} -> {a : _} -> {B : _} -> Tm36 (snoc36 g a) B -> Tm36 g (arr36 a B)
lam36 = \ t, tm, var36, lam36, app => lam36 _ _ _ (t tm var36 lam36 app)

app36 : {g:_}->{a:_}->{B:_} -> Tm36 g (arr36 a B) -> Tm36 g a -> Tm36 g B
app36 = \ t, u, tm, var36, lam36, app36 => app36 _ _ _ (t tm var36 lam36 app36) (u tm var36 lam36 app36)

v036 : {g:_}->{a:_} -> Tm36 (snoc36 g a) a
v036 = var36 vz36

v136 : {g:_}->{a:_}-> {B:_}-> Tm36 (snoc36 (snoc36 g a) B) a
v136 = var36 (vs36 vz36)

v236 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm36 (snoc36 (snoc36 (snoc36 g a) B) C) a
v236 = var36 (vs36 (vs36 vz36))

v336 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm36 (snoc36 (snoc36 (snoc36 (snoc36 g a) B) C) D) a
v336 = var36 (vs36 (vs36 (vs36 vz36)))

v436 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm36 (snoc36 (snoc36 (snoc36 (snoc36 (snoc36 g a) B) C) D) E) a
v436 = var36 (vs36 (vs36 (vs36 (vs36 vz36))))

test36 : {g:_}-> {a:_} -> Tm36 g (arr36 (arr36 a a) (arr36 a a))
test36  = lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036)))))))
Ty37 : Type
Ty37 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty37 : Ty37
empty37 = \ _, empty, _ => empty

arr37 : Ty37 -> Ty37 -> Ty37
arr37 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con37 : Type
Con37 = (Con37 : Type)
 ->(nil  : Con37)
 ->(snoc : Con37 -> Ty37 -> Con37)
 -> Con37

nil37 : Con37
nil37 = \ con, nil37, snoc => nil37

snoc37 : Con37 -> Ty37 -> Con37
snoc37 = \ g, a, con, nil37, snoc37 => snoc37 (g con nil37 snoc37) a

Var37 : Con37 -> Ty37 -> Type
Var37 = \ g, a =>
    (Var37 : Con37 -> Ty37 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var37 (snoc37 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var37 g a -> Var37 (snoc37 g b) a)
 -> Var37 g a

vz37 : {g : _}-> {a : _} -> Var37 (snoc37 g a) a
vz37 = \ var, vz37, vs => vz37 _ _

vs37 : {g : _} -> {B : _} -> {a : _} -> Var37 g a -> Var37 (snoc37 g B) a
vs37 = \ x, var, vz37, vs37 => vs37 _ _ _ (x var vz37 vs37)

Tm37 : Con37 -> Ty37 -> Type
Tm37 = \ g, a =>
    (Tm37    : Con37 -> Ty37 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var37 g a -> Tm37 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm37 (snoc37 g a) B -> Tm37 g (arr37 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm37 g (arr37 a B) -> Tm37 g a -> Tm37 g B)
 -> Tm37 g a

var37 : {g : _} -> {a : _} -> Var37 g a -> Tm37 g a
var37 = \ x, tm, var37, lam, app => var37 _ _ x

lam37 : {g : _} -> {a : _} -> {B : _} -> Tm37 (snoc37 g a) B -> Tm37 g (arr37 a B)
lam37 = \ t, tm, var37, lam37, app => lam37 _ _ _ (t tm var37 lam37 app)

app37 : {g:_}->{a:_}->{B:_} -> Tm37 g (arr37 a B) -> Tm37 g a -> Tm37 g B
app37 = \ t, u, tm, var37, lam37, app37 => app37 _ _ _ (t tm var37 lam37 app37) (u tm var37 lam37 app37)

v037 : {g:_}->{a:_} -> Tm37 (snoc37 g a) a
v037 = var37 vz37

v137 : {g:_}->{a:_}-> {B:_}-> Tm37 (snoc37 (snoc37 g a) B) a
v137 = var37 (vs37 vz37)

v237 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm37 (snoc37 (snoc37 (snoc37 g a) B) C) a
v237 = var37 (vs37 (vs37 vz37))

v337 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm37 (snoc37 (snoc37 (snoc37 (snoc37 g a) B) C) D) a
v337 = var37 (vs37 (vs37 (vs37 vz37)))

v437 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm37 (snoc37 (snoc37 (snoc37 (snoc37 (snoc37 g a) B) C) D) E) a
v437 = var37 (vs37 (vs37 (vs37 (vs37 vz37))))

test37 : {g:_}-> {a:_} -> Tm37 g (arr37 (arr37 a a) (arr37 a a))
test37  = lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037)))))))
Ty38 : Type
Ty38 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty38 : Ty38
empty38 = \ _, empty, _ => empty

arr38 : Ty38 -> Ty38 -> Ty38
arr38 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con38 : Type
Con38 = (Con38 : Type)
 ->(nil  : Con38)
 ->(snoc : Con38 -> Ty38 -> Con38)
 -> Con38

nil38 : Con38
nil38 = \ con, nil38, snoc => nil38

snoc38 : Con38 -> Ty38 -> Con38
snoc38 = \ g, a, con, nil38, snoc38 => snoc38 (g con nil38 snoc38) a

Var38 : Con38 -> Ty38 -> Type
Var38 = \ g, a =>
    (Var38 : Con38 -> Ty38 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var38 (snoc38 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var38 g a -> Var38 (snoc38 g b) a)
 -> Var38 g a

vz38 : {g : _}-> {a : _} -> Var38 (snoc38 g a) a
vz38 = \ var, vz38, vs => vz38 _ _

vs38 : {g : _} -> {B : _} -> {a : _} -> Var38 g a -> Var38 (snoc38 g B) a
vs38 = \ x, var, vz38, vs38 => vs38 _ _ _ (x var vz38 vs38)

Tm38 : Con38 -> Ty38 -> Type
Tm38 = \ g, a =>
    (Tm38    : Con38 -> Ty38 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var38 g a -> Tm38 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm38 (snoc38 g a) B -> Tm38 g (arr38 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm38 g (arr38 a B) -> Tm38 g a -> Tm38 g B)
 -> Tm38 g a

var38 : {g : _} -> {a : _} -> Var38 g a -> Tm38 g a
var38 = \ x, tm, var38, lam, app => var38 _ _ x

lam38 : {g : _} -> {a : _} -> {B : _} -> Tm38 (snoc38 g a) B -> Tm38 g (arr38 a B)
lam38 = \ t, tm, var38, lam38, app => lam38 _ _ _ (t tm var38 lam38 app)

app38 : {g:_}->{a:_}->{B:_} -> Tm38 g (arr38 a B) -> Tm38 g a -> Tm38 g B
app38 = \ t, u, tm, var38, lam38, app38 => app38 _ _ _ (t tm var38 lam38 app38) (u tm var38 lam38 app38)

v038 : {g:_}->{a:_} -> Tm38 (snoc38 g a) a
v038 = var38 vz38

v138 : {g:_}->{a:_}-> {B:_}-> Tm38 (snoc38 (snoc38 g a) B) a
v138 = var38 (vs38 vz38)

v238 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm38 (snoc38 (snoc38 (snoc38 g a) B) C) a
v238 = var38 (vs38 (vs38 vz38))

v338 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm38 (snoc38 (snoc38 (snoc38 (snoc38 g a) B) C) D) a
v338 = var38 (vs38 (vs38 (vs38 vz38)))

v438 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm38 (snoc38 (snoc38 (snoc38 (snoc38 (snoc38 g a) B) C) D) E) a
v438 = var38 (vs38 (vs38 (vs38 (vs38 vz38))))

test38 : {g:_}-> {a:_} -> Tm38 g (arr38 (arr38 a a) (arr38 a a))
test38  = lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038)))))))
Ty39 : Type
Ty39 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty39 : Ty39
empty39 = \ _, empty, _ => empty

arr39 : Ty39 -> Ty39 -> Ty39
arr39 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con39 : Type
Con39 = (Con39 : Type)
 ->(nil  : Con39)
 ->(snoc : Con39 -> Ty39 -> Con39)
 -> Con39

nil39 : Con39
nil39 = \ con, nil39, snoc => nil39

snoc39 : Con39 -> Ty39 -> Con39
snoc39 = \ g, a, con, nil39, snoc39 => snoc39 (g con nil39 snoc39) a

Var39 : Con39 -> Ty39 -> Type
Var39 = \ g, a =>
    (Var39 : Con39 -> Ty39 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var39 (snoc39 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var39 g a -> Var39 (snoc39 g b) a)
 -> Var39 g a

vz39 : {g : _}-> {a : _} -> Var39 (snoc39 g a) a
vz39 = \ var, vz39, vs => vz39 _ _

vs39 : {g : _} -> {B : _} -> {a : _} -> Var39 g a -> Var39 (snoc39 g B) a
vs39 = \ x, var, vz39, vs39 => vs39 _ _ _ (x var vz39 vs39)

Tm39 : Con39 -> Ty39 -> Type
Tm39 = \ g, a =>
    (Tm39    : Con39 -> Ty39 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var39 g a -> Tm39 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm39 (snoc39 g a) B -> Tm39 g (arr39 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm39 g (arr39 a B) -> Tm39 g a -> Tm39 g B)
 -> Tm39 g a

var39 : {g : _} -> {a : _} -> Var39 g a -> Tm39 g a
var39 = \ x, tm, var39, lam, app => var39 _ _ x

lam39 : {g : _} -> {a : _} -> {B : _} -> Tm39 (snoc39 g a) B -> Tm39 g (arr39 a B)
lam39 = \ t, tm, var39, lam39, app => lam39 _ _ _ (t tm var39 lam39 app)

app39 : {g:_}->{a:_}->{B:_} -> Tm39 g (arr39 a B) -> Tm39 g a -> Tm39 g B
app39 = \ t, u, tm, var39, lam39, app39 => app39 _ _ _ (t tm var39 lam39 app39) (u tm var39 lam39 app39)

v039 : {g:_}->{a:_} -> Tm39 (snoc39 g a) a
v039 = var39 vz39

v139 : {g:_}->{a:_}-> {B:_}-> Tm39 (snoc39 (snoc39 g a) B) a
v139 = var39 (vs39 vz39)

v239 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm39 (snoc39 (snoc39 (snoc39 g a) B) C) a
v239 = var39 (vs39 (vs39 vz39))

v339 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm39 (snoc39 (snoc39 (snoc39 (snoc39 g a) B) C) D) a
v339 = var39 (vs39 (vs39 (vs39 vz39)))

v439 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm39 (snoc39 (snoc39 (snoc39 (snoc39 (snoc39 g a) B) C) D) E) a
v439 = var39 (vs39 (vs39 (vs39 (vs39 vz39))))

test39 : {g:_}-> {a:_} -> Tm39 g (arr39 (arr39 a a) (arr39 a a))
test39  = lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039)))))))
Ty40 : Type
Ty40 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty40 : Ty40
empty40 = \ _, empty, _ => empty

arr40 : Ty40 -> Ty40 -> Ty40
arr40 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con40 : Type
Con40 = (Con40 : Type)
 ->(nil  : Con40)
 ->(snoc : Con40 -> Ty40 -> Con40)
 -> Con40

nil40 : Con40
nil40 = \ con, nil40, snoc => nil40

snoc40 : Con40 -> Ty40 -> Con40
snoc40 = \ g, a, con, nil40, snoc40 => snoc40 (g con nil40 snoc40) a

Var40 : Con40 -> Ty40 -> Type
Var40 = \ g, a =>
    (Var40 : Con40 -> Ty40 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var40 (snoc40 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var40 g a -> Var40 (snoc40 g b) a)
 -> Var40 g a

vz40 : {g : _}-> {a : _} -> Var40 (snoc40 g a) a
vz40 = \ var, vz40, vs => vz40 _ _

vs40 : {g : _} -> {B : _} -> {a : _} -> Var40 g a -> Var40 (snoc40 g B) a
vs40 = \ x, var, vz40, vs40 => vs40 _ _ _ (x var vz40 vs40)

Tm40 : Con40 -> Ty40 -> Type
Tm40 = \ g, a =>
    (Tm40    : Con40 -> Ty40 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var40 g a -> Tm40 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm40 (snoc40 g a) B -> Tm40 g (arr40 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm40 g (arr40 a B) -> Tm40 g a -> Tm40 g B)
 -> Tm40 g a

var40 : {g : _} -> {a : _} -> Var40 g a -> Tm40 g a
var40 = \ x, tm, var40, lam, app => var40 _ _ x

lam40 : {g : _} -> {a : _} -> {B : _} -> Tm40 (snoc40 g a) B -> Tm40 g (arr40 a B)
lam40 = \ t, tm, var40, lam40, app => lam40 _ _ _ (t tm var40 lam40 app)

app40 : {g:_}->{a:_}->{B:_} -> Tm40 g (arr40 a B) -> Tm40 g a -> Tm40 g B
app40 = \ t, u, tm, var40, lam40, app40 => app40 _ _ _ (t tm var40 lam40 app40) (u tm var40 lam40 app40)

v040 : {g:_}->{a:_} -> Tm40 (snoc40 g a) a
v040 = var40 vz40

v140 : {g:_}->{a:_}-> {B:_}-> Tm40 (snoc40 (snoc40 g a) B) a
v140 = var40 (vs40 vz40)

v240 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm40 (snoc40 (snoc40 (snoc40 g a) B) C) a
v240 = var40 (vs40 (vs40 vz40))

v340 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm40 (snoc40 (snoc40 (snoc40 (snoc40 g a) B) C) D) a
v340 = var40 (vs40 (vs40 (vs40 vz40)))

v440 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm40 (snoc40 (snoc40 (snoc40 (snoc40 (snoc40 g a) B) C) D) E) a
v440 = var40 (vs40 (vs40 (vs40 (vs40 vz40))))

test40 : {g:_}-> {a:_} -> Tm40 g (arr40 (arr40 a a) (arr40 a a))
test40  = lam40 (lam40 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 (app40 v140 v040)))))))
Ty41 : Type
Ty41 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty41 : Ty41
empty41 = \ _, empty, _ => empty

arr41 : Ty41 -> Ty41 -> Ty41
arr41 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con41 : Type
Con41 = (Con41 : Type)
 ->(nil  : Con41)
 ->(snoc : Con41 -> Ty41 -> Con41)
 -> Con41

nil41 : Con41
nil41 = \ con, nil41, snoc => nil41

snoc41 : Con41 -> Ty41 -> Con41
snoc41 = \ g, a, con, nil41, snoc41 => snoc41 (g con nil41 snoc41) a

Var41 : Con41 -> Ty41 -> Type
Var41 = \ g, a =>
    (Var41 : Con41 -> Ty41 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var41 (snoc41 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var41 g a -> Var41 (snoc41 g b) a)
 -> Var41 g a

vz41 : {g : _}-> {a : _} -> Var41 (snoc41 g a) a
vz41 = \ var, vz41, vs => vz41 _ _

vs41 : {g : _} -> {B : _} -> {a : _} -> Var41 g a -> Var41 (snoc41 g B) a
vs41 = \ x, var, vz41, vs41 => vs41 _ _ _ (x var vz41 vs41)

Tm41 : Con41 -> Ty41 -> Type
Tm41 = \ g, a =>
    (Tm41    : Con41 -> Ty41 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var41 g a -> Tm41 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm41 (snoc41 g a) B -> Tm41 g (arr41 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm41 g (arr41 a B) -> Tm41 g a -> Tm41 g B)
 -> Tm41 g a

var41 : {g : _} -> {a : _} -> Var41 g a -> Tm41 g a
var41 = \ x, tm, var41, lam, app => var41 _ _ x

lam41 : {g : _} -> {a : _} -> {B : _} -> Tm41 (snoc41 g a) B -> Tm41 g (arr41 a B)
lam41 = \ t, tm, var41, lam41, app => lam41 _ _ _ (t tm var41 lam41 app)

app41 : {g:_}->{a:_}->{B:_} -> Tm41 g (arr41 a B) -> Tm41 g a -> Tm41 g B
app41 = \ t, u, tm, var41, lam41, app41 => app41 _ _ _ (t tm var41 lam41 app41) (u tm var41 lam41 app41)

v041 : {g:_}->{a:_} -> Tm41 (snoc41 g a) a
v041 = var41 vz41

v141 : {g:_}->{a:_}-> {B:_}-> Tm41 (snoc41 (snoc41 g a) B) a
v141 = var41 (vs41 vz41)

v241 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm41 (snoc41 (snoc41 (snoc41 g a) B) C) a
v241 = var41 (vs41 (vs41 vz41))

v341 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm41 (snoc41 (snoc41 (snoc41 (snoc41 g a) B) C) D) a
v341 = var41 (vs41 (vs41 (vs41 vz41)))

v441 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm41 (snoc41 (snoc41 (snoc41 (snoc41 (snoc41 g a) B) C) D) E) a
v441 = var41 (vs41 (vs41 (vs41 (vs41 vz41))))

test41 : {g:_}-> {a:_} -> Tm41 g (arr41 (arr41 a a) (arr41 a a))
test41  = lam41 (lam41 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 (app41 v141 v041)))))))
Ty42 : Type
Ty42 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty42 : Ty42
empty42 = \ _, empty, _ => empty

arr42 : Ty42 -> Ty42 -> Ty42
arr42 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con42 : Type
Con42 = (Con42 : Type)
 ->(nil  : Con42)
 ->(snoc : Con42 -> Ty42 -> Con42)
 -> Con42

nil42 : Con42
nil42 = \ con, nil42, snoc => nil42

snoc42 : Con42 -> Ty42 -> Con42
snoc42 = \ g, a, con, nil42, snoc42 => snoc42 (g con nil42 snoc42) a

Var42 : Con42 -> Ty42 -> Type
Var42 = \ g, a =>
    (Var42 : Con42 -> Ty42 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var42 (snoc42 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var42 g a -> Var42 (snoc42 g b) a)
 -> Var42 g a

vz42 : {g : _}-> {a : _} -> Var42 (snoc42 g a) a
vz42 = \ var, vz42, vs => vz42 _ _

vs42 : {g : _} -> {B : _} -> {a : _} -> Var42 g a -> Var42 (snoc42 g B) a
vs42 = \ x, var, vz42, vs42 => vs42 _ _ _ (x var vz42 vs42)

Tm42 : Con42 -> Ty42 -> Type
Tm42 = \ g, a =>
    (Tm42    : Con42 -> Ty42 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var42 g a -> Tm42 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm42 (snoc42 g a) B -> Tm42 g (arr42 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm42 g (arr42 a B) -> Tm42 g a -> Tm42 g B)
 -> Tm42 g a

var42 : {g : _} -> {a : _} -> Var42 g a -> Tm42 g a
var42 = \ x, tm, var42, lam, app => var42 _ _ x

lam42 : {g : _} -> {a : _} -> {B : _} -> Tm42 (snoc42 g a) B -> Tm42 g (arr42 a B)
lam42 = \ t, tm, var42, lam42, app => lam42 _ _ _ (t tm var42 lam42 app)

app42 : {g:_}->{a:_}->{B:_} -> Tm42 g (arr42 a B) -> Tm42 g a -> Tm42 g B
app42 = \ t, u, tm, var42, lam42, app42 => app42 _ _ _ (t tm var42 lam42 app42) (u tm var42 lam42 app42)

v042 : {g:_}->{a:_} -> Tm42 (snoc42 g a) a
v042 = var42 vz42

v142 : {g:_}->{a:_}-> {B:_}-> Tm42 (snoc42 (snoc42 g a) B) a
v142 = var42 (vs42 vz42)

v242 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm42 (snoc42 (snoc42 (snoc42 g a) B) C) a
v242 = var42 (vs42 (vs42 vz42))

v342 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm42 (snoc42 (snoc42 (snoc42 (snoc42 g a) B) C) D) a
v342 = var42 (vs42 (vs42 (vs42 vz42)))

v442 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm42 (snoc42 (snoc42 (snoc42 (snoc42 (snoc42 g a) B) C) D) E) a
v442 = var42 (vs42 (vs42 (vs42 (vs42 vz42))))

test42 : {g:_}-> {a:_} -> Tm42 g (arr42 (arr42 a a) (arr42 a a))
test42  = lam42 (lam42 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 (app42 v142 v042)))))))
Ty43 : Type
Ty43 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty43 : Ty43
empty43 = \ _, empty, _ => empty

arr43 : Ty43 -> Ty43 -> Ty43
arr43 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con43 : Type
Con43 = (Con43 : Type)
 ->(nil  : Con43)
 ->(snoc : Con43 -> Ty43 -> Con43)
 -> Con43

nil43 : Con43
nil43 = \ con, nil43, snoc => nil43

snoc43 : Con43 -> Ty43 -> Con43
snoc43 = \ g, a, con, nil43, snoc43 => snoc43 (g con nil43 snoc43) a

Var43 : Con43 -> Ty43 -> Type
Var43 = \ g, a =>
    (Var43 : Con43 -> Ty43 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var43 (snoc43 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var43 g a -> Var43 (snoc43 g b) a)
 -> Var43 g a

vz43 : {g : _}-> {a : _} -> Var43 (snoc43 g a) a
vz43 = \ var, vz43, vs => vz43 _ _

vs43 : {g : _} -> {B : _} -> {a : _} -> Var43 g a -> Var43 (snoc43 g B) a
vs43 = \ x, var, vz43, vs43 => vs43 _ _ _ (x var vz43 vs43)

Tm43 : Con43 -> Ty43 -> Type
Tm43 = \ g, a =>
    (Tm43    : Con43 -> Ty43 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var43 g a -> Tm43 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm43 (snoc43 g a) B -> Tm43 g (arr43 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm43 g (arr43 a B) -> Tm43 g a -> Tm43 g B)
 -> Tm43 g a

var43 : {g : _} -> {a : _} -> Var43 g a -> Tm43 g a
var43 = \ x, tm, var43, lam, app => var43 _ _ x

lam43 : {g : _} -> {a : _} -> {B : _} -> Tm43 (snoc43 g a) B -> Tm43 g (arr43 a B)
lam43 = \ t, tm, var43, lam43, app => lam43 _ _ _ (t tm var43 lam43 app)

app43 : {g:_}->{a:_}->{B:_} -> Tm43 g (arr43 a B) -> Tm43 g a -> Tm43 g B
app43 = \ t, u, tm, var43, lam43, app43 => app43 _ _ _ (t tm var43 lam43 app43) (u tm var43 lam43 app43)

v043 : {g:_}->{a:_} -> Tm43 (snoc43 g a) a
v043 = var43 vz43

v143 : {g:_}->{a:_}-> {B:_}-> Tm43 (snoc43 (snoc43 g a) B) a
v143 = var43 (vs43 vz43)

v243 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm43 (snoc43 (snoc43 (snoc43 g a) B) C) a
v243 = var43 (vs43 (vs43 vz43))

v343 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm43 (snoc43 (snoc43 (snoc43 (snoc43 g a) B) C) D) a
v343 = var43 (vs43 (vs43 (vs43 vz43)))

v443 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm43 (snoc43 (snoc43 (snoc43 (snoc43 (snoc43 g a) B) C) D) E) a
v443 = var43 (vs43 (vs43 (vs43 (vs43 vz43))))

test43 : {g:_}-> {a:_} -> Tm43 g (arr43 (arr43 a a) (arr43 a a))
test43  = lam43 (lam43 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 (app43 v143 v043)))))))
Ty44 : Type
Ty44 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty44 : Ty44
empty44 = \ _, empty, _ => empty

arr44 : Ty44 -> Ty44 -> Ty44
arr44 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con44 : Type
Con44 = (Con44 : Type)
 ->(nil  : Con44)
 ->(snoc : Con44 -> Ty44 -> Con44)
 -> Con44

nil44 : Con44
nil44 = \ con, nil44, snoc => nil44

snoc44 : Con44 -> Ty44 -> Con44
snoc44 = \ g, a, con, nil44, snoc44 => snoc44 (g con nil44 snoc44) a

Var44 : Con44 -> Ty44 -> Type
Var44 = \ g, a =>
    (Var44 : Con44 -> Ty44 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var44 (snoc44 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var44 g a -> Var44 (snoc44 g b) a)
 -> Var44 g a

vz44 : {g : _}-> {a : _} -> Var44 (snoc44 g a) a
vz44 = \ var, vz44, vs => vz44 _ _

vs44 : {g : _} -> {B : _} -> {a : _} -> Var44 g a -> Var44 (snoc44 g B) a
vs44 = \ x, var, vz44, vs44 => vs44 _ _ _ (x var vz44 vs44)

Tm44 : Con44 -> Ty44 -> Type
Tm44 = \ g, a =>
    (Tm44    : Con44 -> Ty44 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var44 g a -> Tm44 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm44 (snoc44 g a) B -> Tm44 g (arr44 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm44 g (arr44 a B) -> Tm44 g a -> Tm44 g B)
 -> Tm44 g a

var44 : {g : _} -> {a : _} -> Var44 g a -> Tm44 g a
var44 = \ x, tm, var44, lam, app => var44 _ _ x

lam44 : {g : _} -> {a : _} -> {B : _} -> Tm44 (snoc44 g a) B -> Tm44 g (arr44 a B)
lam44 = \ t, tm, var44, lam44, app => lam44 _ _ _ (t tm var44 lam44 app)

app44 : {g:_}->{a:_}->{B:_} -> Tm44 g (arr44 a B) -> Tm44 g a -> Tm44 g B
app44 = \ t, u, tm, var44, lam44, app44 => app44 _ _ _ (t tm var44 lam44 app44) (u tm var44 lam44 app44)

v044 : {g:_}->{a:_} -> Tm44 (snoc44 g a) a
v044 = var44 vz44

v144 : {g:_}->{a:_}-> {B:_}-> Tm44 (snoc44 (snoc44 g a) B) a
v144 = var44 (vs44 vz44)

v244 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm44 (snoc44 (snoc44 (snoc44 g a) B) C) a
v244 = var44 (vs44 (vs44 vz44))

v344 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm44 (snoc44 (snoc44 (snoc44 (snoc44 g a) B) C) D) a
v344 = var44 (vs44 (vs44 (vs44 vz44)))

v444 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm44 (snoc44 (snoc44 (snoc44 (snoc44 (snoc44 g a) B) C) D) E) a
v444 = var44 (vs44 (vs44 (vs44 (vs44 vz44))))

test44 : {g:_}-> {a:_} -> Tm44 g (arr44 (arr44 a a) (arr44 a a))
test44  = lam44 (lam44 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 (app44 v144 v044)))))))
Ty45 : Type
Ty45 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty45 : Ty45
empty45 = \ _, empty, _ => empty

arr45 : Ty45 -> Ty45 -> Ty45
arr45 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con45 : Type
Con45 = (Con45 : Type)
 ->(nil  : Con45)
 ->(snoc : Con45 -> Ty45 -> Con45)
 -> Con45

nil45 : Con45
nil45 = \ con, nil45, snoc => nil45

snoc45 : Con45 -> Ty45 -> Con45
snoc45 = \ g, a, con, nil45, snoc45 => snoc45 (g con nil45 snoc45) a

Var45 : Con45 -> Ty45 -> Type
Var45 = \ g, a =>
    (Var45 : Con45 -> Ty45 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var45 (snoc45 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var45 g a -> Var45 (snoc45 g b) a)
 -> Var45 g a

vz45 : {g : _}-> {a : _} -> Var45 (snoc45 g a) a
vz45 = \ var, vz45, vs => vz45 _ _

vs45 : {g : _} -> {B : _} -> {a : _} -> Var45 g a -> Var45 (snoc45 g B) a
vs45 = \ x, var, vz45, vs45 => vs45 _ _ _ (x var vz45 vs45)

Tm45 : Con45 -> Ty45 -> Type
Tm45 = \ g, a =>
    (Tm45    : Con45 -> Ty45 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var45 g a -> Tm45 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm45 (snoc45 g a) B -> Tm45 g (arr45 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm45 g (arr45 a B) -> Tm45 g a -> Tm45 g B)
 -> Tm45 g a

var45 : {g : _} -> {a : _} -> Var45 g a -> Tm45 g a
var45 = \ x, tm, var45, lam, app => var45 _ _ x

lam45 : {g : _} -> {a : _} -> {B : _} -> Tm45 (snoc45 g a) B -> Tm45 g (arr45 a B)
lam45 = \ t, tm, var45, lam45, app => lam45 _ _ _ (t tm var45 lam45 app)

app45 : {g:_}->{a:_}->{B:_} -> Tm45 g (arr45 a B) -> Tm45 g a -> Tm45 g B
app45 = \ t, u, tm, var45, lam45, app45 => app45 _ _ _ (t tm var45 lam45 app45) (u tm var45 lam45 app45)

v045 : {g:_}->{a:_} -> Tm45 (snoc45 g a) a
v045 = var45 vz45

v145 : {g:_}->{a:_}-> {B:_}-> Tm45 (snoc45 (snoc45 g a) B) a
v145 = var45 (vs45 vz45)

v245 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm45 (snoc45 (snoc45 (snoc45 g a) B) C) a
v245 = var45 (vs45 (vs45 vz45))

v345 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm45 (snoc45 (snoc45 (snoc45 (snoc45 g a) B) C) D) a
v345 = var45 (vs45 (vs45 (vs45 vz45)))

v445 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm45 (snoc45 (snoc45 (snoc45 (snoc45 (snoc45 g a) B) C) D) E) a
v445 = var45 (vs45 (vs45 (vs45 (vs45 vz45))))

test45 : {g:_}-> {a:_} -> Tm45 g (arr45 (arr45 a a) (arr45 a a))
test45  = lam45 (lam45 (app45 v145 (app45 v145 (app45 v145 (app45 v145 (app45 v145 (app45 v145 v045)))))))
Ty46 : Type
Ty46 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty46 : Ty46
empty46 = \ _, empty, _ => empty

arr46 : Ty46 -> Ty46 -> Ty46
arr46 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con46 : Type
Con46 = (Con46 : Type)
 ->(nil  : Con46)
 ->(snoc : Con46 -> Ty46 -> Con46)
 -> Con46

nil46 : Con46
nil46 = \ con, nil46, snoc => nil46

snoc46 : Con46 -> Ty46 -> Con46
snoc46 = \ g, a, con, nil46, snoc46 => snoc46 (g con nil46 snoc46) a

Var46 : Con46 -> Ty46 -> Type
Var46 = \ g, a =>
    (Var46 : Con46 -> Ty46 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var46 (snoc46 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var46 g a -> Var46 (snoc46 g b) a)
 -> Var46 g a

vz46 : {g : _}-> {a : _} -> Var46 (snoc46 g a) a
vz46 = \ var, vz46, vs => vz46 _ _

vs46 : {g : _} -> {B : _} -> {a : _} -> Var46 g a -> Var46 (snoc46 g B) a
vs46 = \ x, var, vz46, vs46 => vs46 _ _ _ (x var vz46 vs46)

Tm46 : Con46 -> Ty46 -> Type
Tm46 = \ g, a =>
    (Tm46    : Con46 -> Ty46 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var46 g a -> Tm46 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm46 (snoc46 g a) B -> Tm46 g (arr46 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm46 g (arr46 a B) -> Tm46 g a -> Tm46 g B)
 -> Tm46 g a

var46 : {g : _} -> {a : _} -> Var46 g a -> Tm46 g a
var46 = \ x, tm, var46, lam, app => var46 _ _ x

lam46 : {g : _} -> {a : _} -> {B : _} -> Tm46 (snoc46 g a) B -> Tm46 g (arr46 a B)
lam46 = \ t, tm, var46, lam46, app => lam46 _ _ _ (t tm var46 lam46 app)

app46 : {g:_}->{a:_}->{B:_} -> Tm46 g (arr46 a B) -> Tm46 g a -> Tm46 g B
app46 = \ t, u, tm, var46, lam46, app46 => app46 _ _ _ (t tm var46 lam46 app46) (u tm var46 lam46 app46)

v046 : {g:_}->{a:_} -> Tm46 (snoc46 g a) a
v046 = var46 vz46

v146 : {g:_}->{a:_}-> {B:_}-> Tm46 (snoc46 (snoc46 g a) B) a
v146 = var46 (vs46 vz46)

v246 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm46 (snoc46 (snoc46 (snoc46 g a) B) C) a
v246 = var46 (vs46 (vs46 vz46))

v346 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm46 (snoc46 (snoc46 (snoc46 (snoc46 g a) B) C) D) a
v346 = var46 (vs46 (vs46 (vs46 vz46)))

v446 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm46 (snoc46 (snoc46 (snoc46 (snoc46 (snoc46 g a) B) C) D) E) a
v446 = var46 (vs46 (vs46 (vs46 (vs46 vz46))))

test46 : {g:_}-> {a:_} -> Tm46 g (arr46 (arr46 a a) (arr46 a a))
test46  = lam46 (lam46 (app46 v146 (app46 v146 (app46 v146 (app46 v146 (app46 v146 (app46 v146 v046)))))))
Ty47 : Type
Ty47 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty47 : Ty47
empty47 = \ _, empty, _ => empty

arr47 : Ty47 -> Ty47 -> Ty47
arr47 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con47 : Type
Con47 = (Con47 : Type)
 ->(nil  : Con47)
 ->(snoc : Con47 -> Ty47 -> Con47)
 -> Con47

nil47 : Con47
nil47 = \ con, nil47, snoc => nil47

snoc47 : Con47 -> Ty47 -> Con47
snoc47 = \ g, a, con, nil47, snoc47 => snoc47 (g con nil47 snoc47) a

Var47 : Con47 -> Ty47 -> Type
Var47 = \ g, a =>
    (Var47 : Con47 -> Ty47 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var47 (snoc47 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var47 g a -> Var47 (snoc47 g b) a)
 -> Var47 g a

vz47 : {g : _}-> {a : _} -> Var47 (snoc47 g a) a
vz47 = \ var, vz47, vs => vz47 _ _

vs47 : {g : _} -> {B : _} -> {a : _} -> Var47 g a -> Var47 (snoc47 g B) a
vs47 = \ x, var, vz47, vs47 => vs47 _ _ _ (x var vz47 vs47)

Tm47 : Con47 -> Ty47 -> Type
Tm47 = \ g, a =>
    (Tm47    : Con47 -> Ty47 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var47 g a -> Tm47 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm47 (snoc47 g a) B -> Tm47 g (arr47 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm47 g (arr47 a B) -> Tm47 g a -> Tm47 g B)
 -> Tm47 g a

var47 : {g : _} -> {a : _} -> Var47 g a -> Tm47 g a
var47 = \ x, tm, var47, lam, app => var47 _ _ x

lam47 : {g : _} -> {a : _} -> {B : _} -> Tm47 (snoc47 g a) B -> Tm47 g (arr47 a B)
lam47 = \ t, tm, var47, lam47, app => lam47 _ _ _ (t tm var47 lam47 app)

app47 : {g:_}->{a:_}->{B:_} -> Tm47 g (arr47 a B) -> Tm47 g a -> Tm47 g B
app47 = \ t, u, tm, var47, lam47, app47 => app47 _ _ _ (t tm var47 lam47 app47) (u tm var47 lam47 app47)

v047 : {g:_}->{a:_} -> Tm47 (snoc47 g a) a
v047 = var47 vz47

v147 : {g:_}->{a:_}-> {B:_}-> Tm47 (snoc47 (snoc47 g a) B) a
v147 = var47 (vs47 vz47)

v247 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm47 (snoc47 (snoc47 (snoc47 g a) B) C) a
v247 = var47 (vs47 (vs47 vz47))

v347 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm47 (snoc47 (snoc47 (snoc47 (snoc47 g a) B) C) D) a
v347 = var47 (vs47 (vs47 (vs47 vz47)))

v447 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm47 (snoc47 (snoc47 (snoc47 (snoc47 (snoc47 g a) B) C) D) E) a
v447 = var47 (vs47 (vs47 (vs47 (vs47 vz47))))

test47 : {g:_}-> {a:_} -> Tm47 g (arr47 (arr47 a a) (arr47 a a))
test47  = lam47 (lam47 (app47 v147 (app47 v147 (app47 v147 (app47 v147 (app47 v147 (app47 v147 v047)))))))
Ty48 : Type
Ty48 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty48 : Ty48
empty48 = \ _, empty, _ => empty

arr48 : Ty48 -> Ty48 -> Ty48
arr48 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con48 : Type
Con48 = (Con48 : Type)
 ->(nil  : Con48)
 ->(snoc : Con48 -> Ty48 -> Con48)
 -> Con48

nil48 : Con48
nil48 = \ con, nil48, snoc => nil48

snoc48 : Con48 -> Ty48 -> Con48
snoc48 = \ g, a, con, nil48, snoc48 => snoc48 (g con nil48 snoc48) a

Var48 : Con48 -> Ty48 -> Type
Var48 = \ g, a =>
    (Var48 : Con48 -> Ty48 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var48 (snoc48 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var48 g a -> Var48 (snoc48 g b) a)
 -> Var48 g a

vz48 : {g : _}-> {a : _} -> Var48 (snoc48 g a) a
vz48 = \ var, vz48, vs => vz48 _ _

vs48 : {g : _} -> {B : _} -> {a : _} -> Var48 g a -> Var48 (snoc48 g B) a
vs48 = \ x, var, vz48, vs48 => vs48 _ _ _ (x var vz48 vs48)

Tm48 : Con48 -> Ty48 -> Type
Tm48 = \ g, a =>
    (Tm48    : Con48 -> Ty48 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var48 g a -> Tm48 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm48 (snoc48 g a) B -> Tm48 g (arr48 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm48 g (arr48 a B) -> Tm48 g a -> Tm48 g B)
 -> Tm48 g a

var48 : {g : _} -> {a : _} -> Var48 g a -> Tm48 g a
var48 = \ x, tm, var48, lam, app => var48 _ _ x

lam48 : {g : _} -> {a : _} -> {B : _} -> Tm48 (snoc48 g a) B -> Tm48 g (arr48 a B)
lam48 = \ t, tm, var48, lam48, app => lam48 _ _ _ (t tm var48 lam48 app)

app48 : {g:_}->{a:_}->{B:_} -> Tm48 g (arr48 a B) -> Tm48 g a -> Tm48 g B
app48 = \ t, u, tm, var48, lam48, app48 => app48 _ _ _ (t tm var48 lam48 app48) (u tm var48 lam48 app48)

v048 : {g:_}->{a:_} -> Tm48 (snoc48 g a) a
v048 = var48 vz48

v148 : {g:_}->{a:_}-> {B:_}-> Tm48 (snoc48 (snoc48 g a) B) a
v148 = var48 (vs48 vz48)

v248 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm48 (snoc48 (snoc48 (snoc48 g a) B) C) a
v248 = var48 (vs48 (vs48 vz48))

v348 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm48 (snoc48 (snoc48 (snoc48 (snoc48 g a) B) C) D) a
v348 = var48 (vs48 (vs48 (vs48 vz48)))

v448 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm48 (snoc48 (snoc48 (snoc48 (snoc48 (snoc48 g a) B) C) D) E) a
v448 = var48 (vs48 (vs48 (vs48 (vs48 vz48))))

test48 : {g:_}-> {a:_} -> Tm48 g (arr48 (arr48 a a) (arr48 a a))
test48  = lam48 (lam48 (app48 v148 (app48 v148 (app48 v148 (app48 v148 (app48 v148 (app48 v148 v048)))))))
Ty49 : Type
Ty49 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty49 : Ty49
empty49 = \ _, empty, _ => empty

arr49 : Ty49 -> Ty49 -> Ty49
arr49 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con49 : Type
Con49 = (Con49 : Type)
 ->(nil  : Con49)
 ->(snoc : Con49 -> Ty49 -> Con49)
 -> Con49

nil49 : Con49
nil49 = \ con, nil49, snoc => nil49

snoc49 : Con49 -> Ty49 -> Con49
snoc49 = \ g, a, con, nil49, snoc49 => snoc49 (g con nil49 snoc49) a

Var49 : Con49 -> Ty49 -> Type
Var49 = \ g, a =>
    (Var49 : Con49 -> Ty49 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var49 (snoc49 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var49 g a -> Var49 (snoc49 g b) a)
 -> Var49 g a

vz49 : {g : _}-> {a : _} -> Var49 (snoc49 g a) a
vz49 = \ var, vz49, vs => vz49 _ _

vs49 : {g : _} -> {B : _} -> {a : _} -> Var49 g a -> Var49 (snoc49 g B) a
vs49 = \ x, var, vz49, vs49 => vs49 _ _ _ (x var vz49 vs49)

Tm49 : Con49 -> Ty49 -> Type
Tm49 = \ g, a =>
    (Tm49    : Con49 -> Ty49 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var49 g a -> Tm49 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm49 (snoc49 g a) B -> Tm49 g (arr49 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm49 g (arr49 a B) -> Tm49 g a -> Tm49 g B)
 -> Tm49 g a

var49 : {g : _} -> {a : _} -> Var49 g a -> Tm49 g a
var49 = \ x, tm, var49, lam, app => var49 _ _ x

lam49 : {g : _} -> {a : _} -> {B : _} -> Tm49 (snoc49 g a) B -> Tm49 g (arr49 a B)
lam49 = \ t, tm, var49, lam49, app => lam49 _ _ _ (t tm var49 lam49 app)

app49 : {g:_}->{a:_}->{B:_} -> Tm49 g (arr49 a B) -> Tm49 g a -> Tm49 g B
app49 = \ t, u, tm, var49, lam49, app49 => app49 _ _ _ (t tm var49 lam49 app49) (u tm var49 lam49 app49)

v049 : {g:_}->{a:_} -> Tm49 (snoc49 g a) a
v049 = var49 vz49

v149 : {g:_}->{a:_}-> {B:_}-> Tm49 (snoc49 (snoc49 g a) B) a
v149 = var49 (vs49 vz49)

v249 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm49 (snoc49 (snoc49 (snoc49 g a) B) C) a
v249 = var49 (vs49 (vs49 vz49))

v349 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm49 (snoc49 (snoc49 (snoc49 (snoc49 g a) B) C) D) a
v349 = var49 (vs49 (vs49 (vs49 vz49)))

v449 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm49 (snoc49 (snoc49 (snoc49 (snoc49 (snoc49 g a) B) C) D) E) a
v449 = var49 (vs49 (vs49 (vs49 (vs49 vz49))))

test49 : {g:_}-> {a:_} -> Tm49 g (arr49 (arr49 a a) (arr49 a a))
test49  = lam49 (lam49 (app49 v149 (app49 v149 (app49 v149 (app49 v149 (app49 v149 (app49 v149 v049)))))))
Ty50 : Type
Ty50 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty50 : Ty50
empty50 = \ _, empty, _ => empty

arr50 : Ty50 -> Ty50 -> Ty50
arr50 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con50 : Type
Con50 = (Con50 : Type)
 ->(nil  : Con50)
 ->(snoc : Con50 -> Ty50 -> Con50)
 -> Con50

nil50 : Con50
nil50 = \ con, nil50, snoc => nil50

snoc50 : Con50 -> Ty50 -> Con50
snoc50 = \ g, a, con, nil50, snoc50 => snoc50 (g con nil50 snoc50) a

Var50 : Con50 -> Ty50 -> Type
Var50 = \ g, a =>
    (Var50 : Con50 -> Ty50 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var50 (snoc50 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var50 g a -> Var50 (snoc50 g b) a)
 -> Var50 g a

vz50 : {g : _}-> {a : _} -> Var50 (snoc50 g a) a
vz50 = \ var, vz50, vs => vz50 _ _

vs50 : {g : _} -> {B : _} -> {a : _} -> Var50 g a -> Var50 (snoc50 g B) a
vs50 = \ x, var, vz50, vs50 => vs50 _ _ _ (x var vz50 vs50)

Tm50 : Con50 -> Ty50 -> Type
Tm50 = \ g, a =>
    (Tm50    : Con50 -> Ty50 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var50 g a -> Tm50 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm50 (snoc50 g a) B -> Tm50 g (arr50 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm50 g (arr50 a B) -> Tm50 g a -> Tm50 g B)
 -> Tm50 g a

var50 : {g : _} -> {a : _} -> Var50 g a -> Tm50 g a
var50 = \ x, tm, var50, lam, app => var50 _ _ x

lam50 : {g : _} -> {a : _} -> {B : _} -> Tm50 (snoc50 g a) B -> Tm50 g (arr50 a B)
lam50 = \ t, tm, var50, lam50, app => lam50 _ _ _ (t tm var50 lam50 app)

app50 : {g:_}->{a:_}->{B:_} -> Tm50 g (arr50 a B) -> Tm50 g a -> Tm50 g B
app50 = \ t, u, tm, var50, lam50, app50 => app50 _ _ _ (t tm var50 lam50 app50) (u tm var50 lam50 app50)

v050 : {g:_}->{a:_} -> Tm50 (snoc50 g a) a
v050 = var50 vz50

v150 : {g:_}->{a:_}-> {B:_}-> Tm50 (snoc50 (snoc50 g a) B) a
v150 = var50 (vs50 vz50)

v250 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm50 (snoc50 (snoc50 (snoc50 g a) B) C) a
v250 = var50 (vs50 (vs50 vz50))

v350 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm50 (snoc50 (snoc50 (snoc50 (snoc50 g a) B) C) D) a
v350 = var50 (vs50 (vs50 (vs50 vz50)))

v450 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm50 (snoc50 (snoc50 (snoc50 (snoc50 (snoc50 g a) B) C) D) E) a
v450 = var50 (vs50 (vs50 (vs50 (vs50 vz50))))

test50 : {g:_}-> {a:_} -> Tm50 g (arr50 (arr50 a a) (arr50 a a))
test50  = lam50 (lam50 (app50 v150 (app50 v150 (app50 v150 (app50 v150 (app50 v150 (app50 v150 v050)))))))
Ty51 : Type
Ty51 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty51 : Ty51
empty51 = \ _, empty, _ => empty

arr51 : Ty51 -> Ty51 -> Ty51
arr51 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con51 : Type
Con51 = (Con51 : Type)
 ->(nil  : Con51)
 ->(snoc : Con51 -> Ty51 -> Con51)
 -> Con51

nil51 : Con51
nil51 = \ con, nil51, snoc => nil51

snoc51 : Con51 -> Ty51 -> Con51
snoc51 = \ g, a, con, nil51, snoc51 => snoc51 (g con nil51 snoc51) a

Var51 : Con51 -> Ty51 -> Type
Var51 = \ g, a =>
    (Var51 : Con51 -> Ty51 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var51 (snoc51 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var51 g a -> Var51 (snoc51 g b) a)
 -> Var51 g a

vz51 : {g : _}-> {a : _} -> Var51 (snoc51 g a) a
vz51 = \ var, vz51, vs => vz51 _ _

vs51 : {g : _} -> {B : _} -> {a : _} -> Var51 g a -> Var51 (snoc51 g B) a
vs51 = \ x, var, vz51, vs51 => vs51 _ _ _ (x var vz51 vs51)

Tm51 : Con51 -> Ty51 -> Type
Tm51 = \ g, a =>
    (Tm51    : Con51 -> Ty51 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var51 g a -> Tm51 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm51 (snoc51 g a) B -> Tm51 g (arr51 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm51 g (arr51 a B) -> Tm51 g a -> Tm51 g B)
 -> Tm51 g a

var51 : {g : _} -> {a : _} -> Var51 g a -> Tm51 g a
var51 = \ x, tm, var51, lam, app => var51 _ _ x

lam51 : {g : _} -> {a : _} -> {B : _} -> Tm51 (snoc51 g a) B -> Tm51 g (arr51 a B)
lam51 = \ t, tm, var51, lam51, app => lam51 _ _ _ (t tm var51 lam51 app)

app51 : {g:_}->{a:_}->{B:_} -> Tm51 g (arr51 a B) -> Tm51 g a -> Tm51 g B
app51 = \ t, u, tm, var51, lam51, app51 => app51 _ _ _ (t tm var51 lam51 app51) (u tm var51 lam51 app51)

v051 : {g:_}->{a:_} -> Tm51 (snoc51 g a) a
v051 = var51 vz51

v151 : {g:_}->{a:_}-> {B:_}-> Tm51 (snoc51 (snoc51 g a) B) a
v151 = var51 (vs51 vz51)

v251 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm51 (snoc51 (snoc51 (snoc51 g a) B) C) a
v251 = var51 (vs51 (vs51 vz51))

v351 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm51 (snoc51 (snoc51 (snoc51 (snoc51 g a) B) C) D) a
v351 = var51 (vs51 (vs51 (vs51 vz51)))

v451 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm51 (snoc51 (snoc51 (snoc51 (snoc51 (snoc51 g a) B) C) D) E) a
v451 = var51 (vs51 (vs51 (vs51 (vs51 vz51))))

test51 : {g:_}-> {a:_} -> Tm51 g (arr51 (arr51 a a) (arr51 a a))
test51  = lam51 (lam51 (app51 v151 (app51 v151 (app51 v151 (app51 v151 (app51 v151 (app51 v151 v051)))))))
Ty52 : Type
Ty52 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty52 : Ty52
empty52 = \ _, empty, _ => empty

arr52 : Ty52 -> Ty52 -> Ty52
arr52 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con52 : Type
Con52 = (Con52 : Type)
 ->(nil  : Con52)
 ->(snoc : Con52 -> Ty52 -> Con52)
 -> Con52

nil52 : Con52
nil52 = \ con, nil52, snoc => nil52

snoc52 : Con52 -> Ty52 -> Con52
snoc52 = \ g, a, con, nil52, snoc52 => snoc52 (g con nil52 snoc52) a

Var52 : Con52 -> Ty52 -> Type
Var52 = \ g, a =>
    (Var52 : Con52 -> Ty52 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var52 (snoc52 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var52 g a -> Var52 (snoc52 g b) a)
 -> Var52 g a

vz52 : {g : _}-> {a : _} -> Var52 (snoc52 g a) a
vz52 = \ var, vz52, vs => vz52 _ _

vs52 : {g : _} -> {B : _} -> {a : _} -> Var52 g a -> Var52 (snoc52 g B) a
vs52 = \ x, var, vz52, vs52 => vs52 _ _ _ (x var vz52 vs52)

Tm52 : Con52 -> Ty52 -> Type
Tm52 = \ g, a =>
    (Tm52    : Con52 -> Ty52 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var52 g a -> Tm52 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm52 (snoc52 g a) B -> Tm52 g (arr52 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm52 g (arr52 a B) -> Tm52 g a -> Tm52 g B)
 -> Tm52 g a

var52 : {g : _} -> {a : _} -> Var52 g a -> Tm52 g a
var52 = \ x, tm, var52, lam, app => var52 _ _ x

lam52 : {g : _} -> {a : _} -> {B : _} -> Tm52 (snoc52 g a) B -> Tm52 g (arr52 a B)
lam52 = \ t, tm, var52, lam52, app => lam52 _ _ _ (t tm var52 lam52 app)

app52 : {g:_}->{a:_}->{B:_} -> Tm52 g (arr52 a B) -> Tm52 g a -> Tm52 g B
app52 = \ t, u, tm, var52, lam52, app52 => app52 _ _ _ (t tm var52 lam52 app52) (u tm var52 lam52 app52)

v052 : {g:_}->{a:_} -> Tm52 (snoc52 g a) a
v052 = var52 vz52

v152 : {g:_}->{a:_}-> {B:_}-> Tm52 (snoc52 (snoc52 g a) B) a
v152 = var52 (vs52 vz52)

v252 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm52 (snoc52 (snoc52 (snoc52 g a) B) C) a
v252 = var52 (vs52 (vs52 vz52))

v352 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm52 (snoc52 (snoc52 (snoc52 (snoc52 g a) B) C) D) a
v352 = var52 (vs52 (vs52 (vs52 vz52)))

v452 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm52 (snoc52 (snoc52 (snoc52 (snoc52 (snoc52 g a) B) C) D) E) a
v452 = var52 (vs52 (vs52 (vs52 (vs52 vz52))))

test52 : {g:_}-> {a:_} -> Tm52 g (arr52 (arr52 a a) (arr52 a a))
test52  = lam52 (lam52 (app52 v152 (app52 v152 (app52 v152 (app52 v152 (app52 v152 (app52 v152 v052)))))))
Ty53 : Type
Ty53 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty53 : Ty53
empty53 = \ _, empty, _ => empty

arr53 : Ty53 -> Ty53 -> Ty53
arr53 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con53 : Type
Con53 = (Con53 : Type)
 ->(nil  : Con53)
 ->(snoc : Con53 -> Ty53 -> Con53)
 -> Con53

nil53 : Con53
nil53 = \ con, nil53, snoc => nil53

snoc53 : Con53 -> Ty53 -> Con53
snoc53 = \ g, a, con, nil53, snoc53 => snoc53 (g con nil53 snoc53) a

Var53 : Con53 -> Ty53 -> Type
Var53 = \ g, a =>
    (Var53 : Con53 -> Ty53 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var53 (snoc53 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var53 g a -> Var53 (snoc53 g b) a)
 -> Var53 g a

vz53 : {g : _}-> {a : _} -> Var53 (snoc53 g a) a
vz53 = \ var, vz53, vs => vz53 _ _

vs53 : {g : _} -> {B : _} -> {a : _} -> Var53 g a -> Var53 (snoc53 g B) a
vs53 = \ x, var, vz53, vs53 => vs53 _ _ _ (x var vz53 vs53)

Tm53 : Con53 -> Ty53 -> Type
Tm53 = \ g, a =>
    (Tm53    : Con53 -> Ty53 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var53 g a -> Tm53 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm53 (snoc53 g a) B -> Tm53 g (arr53 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm53 g (arr53 a B) -> Tm53 g a -> Tm53 g B)
 -> Tm53 g a

var53 : {g : _} -> {a : _} -> Var53 g a -> Tm53 g a
var53 = \ x, tm, var53, lam, app => var53 _ _ x

lam53 : {g : _} -> {a : _} -> {B : _} -> Tm53 (snoc53 g a) B -> Tm53 g (arr53 a B)
lam53 = \ t, tm, var53, lam53, app => lam53 _ _ _ (t tm var53 lam53 app)

app53 : {g:_}->{a:_}->{B:_} -> Tm53 g (arr53 a B) -> Tm53 g a -> Tm53 g B
app53 = \ t, u, tm, var53, lam53, app53 => app53 _ _ _ (t tm var53 lam53 app53) (u tm var53 lam53 app53)

v053 : {g:_}->{a:_} -> Tm53 (snoc53 g a) a
v053 = var53 vz53

v153 : {g:_}->{a:_}-> {B:_}-> Tm53 (snoc53 (snoc53 g a) B) a
v153 = var53 (vs53 vz53)

v253 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm53 (snoc53 (snoc53 (snoc53 g a) B) C) a
v253 = var53 (vs53 (vs53 vz53))

v353 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm53 (snoc53 (snoc53 (snoc53 (snoc53 g a) B) C) D) a
v353 = var53 (vs53 (vs53 (vs53 vz53)))

v453 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm53 (snoc53 (snoc53 (snoc53 (snoc53 (snoc53 g a) B) C) D) E) a
v453 = var53 (vs53 (vs53 (vs53 (vs53 vz53))))

test53 : {g:_}-> {a:_} -> Tm53 g (arr53 (arr53 a a) (arr53 a a))
test53  = lam53 (lam53 (app53 v153 (app53 v153 (app53 v153 (app53 v153 (app53 v153 (app53 v153 v053)))))))
Ty54 : Type
Ty54 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty54 : Ty54
empty54 = \ _, empty, _ => empty

arr54 : Ty54 -> Ty54 -> Ty54
arr54 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con54 : Type
Con54 = (Con54 : Type)
 ->(nil  : Con54)
 ->(snoc : Con54 -> Ty54 -> Con54)
 -> Con54

nil54 : Con54
nil54 = \ con, nil54, snoc => nil54

snoc54 : Con54 -> Ty54 -> Con54
snoc54 = \ g, a, con, nil54, snoc54 => snoc54 (g con nil54 snoc54) a

Var54 : Con54 -> Ty54 -> Type
Var54 = \ g, a =>
    (Var54 : Con54 -> Ty54 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var54 (snoc54 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var54 g a -> Var54 (snoc54 g b) a)
 -> Var54 g a

vz54 : {g : _}-> {a : _} -> Var54 (snoc54 g a) a
vz54 = \ var, vz54, vs => vz54 _ _

vs54 : {g : _} -> {B : _} -> {a : _} -> Var54 g a -> Var54 (snoc54 g B) a
vs54 = \ x, var, vz54, vs54 => vs54 _ _ _ (x var vz54 vs54)

Tm54 : Con54 -> Ty54 -> Type
Tm54 = \ g, a =>
    (Tm54    : Con54 -> Ty54 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var54 g a -> Tm54 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm54 (snoc54 g a) B -> Tm54 g (arr54 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm54 g (arr54 a B) -> Tm54 g a -> Tm54 g B)
 -> Tm54 g a

var54 : {g : _} -> {a : _} -> Var54 g a -> Tm54 g a
var54 = \ x, tm, var54, lam, app => var54 _ _ x

lam54 : {g : _} -> {a : _} -> {B : _} -> Tm54 (snoc54 g a) B -> Tm54 g (arr54 a B)
lam54 = \ t, tm, var54, lam54, app => lam54 _ _ _ (t tm var54 lam54 app)

app54 : {g:_}->{a:_}->{B:_} -> Tm54 g (arr54 a B) -> Tm54 g a -> Tm54 g B
app54 = \ t, u, tm, var54, lam54, app54 => app54 _ _ _ (t tm var54 lam54 app54) (u tm var54 lam54 app54)

v054 : {g:_}->{a:_} -> Tm54 (snoc54 g a) a
v054 = var54 vz54

v154 : {g:_}->{a:_}-> {B:_}-> Tm54 (snoc54 (snoc54 g a) B) a
v154 = var54 (vs54 vz54)

v254 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm54 (snoc54 (snoc54 (snoc54 g a) B) C) a
v254 = var54 (vs54 (vs54 vz54))

v354 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm54 (snoc54 (snoc54 (snoc54 (snoc54 g a) B) C) D) a
v354 = var54 (vs54 (vs54 (vs54 vz54)))

v454 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm54 (snoc54 (snoc54 (snoc54 (snoc54 (snoc54 g a) B) C) D) E) a
v454 = var54 (vs54 (vs54 (vs54 (vs54 vz54))))

test54 : {g:_}-> {a:_} -> Tm54 g (arr54 (arr54 a a) (arr54 a a))
test54  = lam54 (lam54 (app54 v154 (app54 v154 (app54 v154 (app54 v154 (app54 v154 (app54 v154 v054)))))))
Ty55 : Type
Ty55 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty55 : Ty55
empty55 = \ _, empty, _ => empty

arr55 : Ty55 -> Ty55 -> Ty55
arr55 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con55 : Type
Con55 = (Con55 : Type)
 ->(nil  : Con55)
 ->(snoc : Con55 -> Ty55 -> Con55)
 -> Con55

nil55 : Con55
nil55 = \ con, nil55, snoc => nil55

snoc55 : Con55 -> Ty55 -> Con55
snoc55 = \ g, a, con, nil55, snoc55 => snoc55 (g con nil55 snoc55) a

Var55 : Con55 -> Ty55 -> Type
Var55 = \ g, a =>
    (Var55 : Con55 -> Ty55 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var55 (snoc55 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var55 g a -> Var55 (snoc55 g b) a)
 -> Var55 g a

vz55 : {g : _}-> {a : _} -> Var55 (snoc55 g a) a
vz55 = \ var, vz55, vs => vz55 _ _

vs55 : {g : _} -> {B : _} -> {a : _} -> Var55 g a -> Var55 (snoc55 g B) a
vs55 = \ x, var, vz55, vs55 => vs55 _ _ _ (x var vz55 vs55)

Tm55 : Con55 -> Ty55 -> Type
Tm55 = \ g, a =>
    (Tm55    : Con55 -> Ty55 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var55 g a -> Tm55 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm55 (snoc55 g a) B -> Tm55 g (arr55 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm55 g (arr55 a B) -> Tm55 g a -> Tm55 g B)
 -> Tm55 g a

var55 : {g : _} -> {a : _} -> Var55 g a -> Tm55 g a
var55 = \ x, tm, var55, lam, app => var55 _ _ x

lam55 : {g : _} -> {a : _} -> {B : _} -> Tm55 (snoc55 g a) B -> Tm55 g (arr55 a B)
lam55 = \ t, tm, var55, lam55, app => lam55 _ _ _ (t tm var55 lam55 app)

app55 : {g:_}->{a:_}->{B:_} -> Tm55 g (arr55 a B) -> Tm55 g a -> Tm55 g B
app55 = \ t, u, tm, var55, lam55, app55 => app55 _ _ _ (t tm var55 lam55 app55) (u tm var55 lam55 app55)

v055 : {g:_}->{a:_} -> Tm55 (snoc55 g a) a
v055 = var55 vz55

v155 : {g:_}->{a:_}-> {B:_}-> Tm55 (snoc55 (snoc55 g a) B) a
v155 = var55 (vs55 vz55)

v255 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm55 (snoc55 (snoc55 (snoc55 g a) B) C) a
v255 = var55 (vs55 (vs55 vz55))

v355 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm55 (snoc55 (snoc55 (snoc55 (snoc55 g a) B) C) D) a
v355 = var55 (vs55 (vs55 (vs55 vz55)))

v455 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm55 (snoc55 (snoc55 (snoc55 (snoc55 (snoc55 g a) B) C) D) E) a
v455 = var55 (vs55 (vs55 (vs55 (vs55 vz55))))

test55 : {g:_}-> {a:_} -> Tm55 g (arr55 (arr55 a a) (arr55 a a))
test55  = lam55 (lam55 (app55 v155 (app55 v155 (app55 v155 (app55 v155 (app55 v155 (app55 v155 v055)))))))
Ty56 : Type
Ty56 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty56 : Ty56
empty56 = \ _, empty, _ => empty

arr56 : Ty56 -> Ty56 -> Ty56
arr56 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con56 : Type
Con56 = (Con56 : Type)
 ->(nil  : Con56)
 ->(snoc : Con56 -> Ty56 -> Con56)
 -> Con56

nil56 : Con56
nil56 = \ con, nil56, snoc => nil56

snoc56 : Con56 -> Ty56 -> Con56
snoc56 = \ g, a, con, nil56, snoc56 => snoc56 (g con nil56 snoc56) a

Var56 : Con56 -> Ty56 -> Type
Var56 = \ g, a =>
    (Var56 : Con56 -> Ty56 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var56 (snoc56 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var56 g a -> Var56 (snoc56 g b) a)
 -> Var56 g a

vz56 : {g : _}-> {a : _} -> Var56 (snoc56 g a) a
vz56 = \ var, vz56, vs => vz56 _ _

vs56 : {g : _} -> {B : _} -> {a : _} -> Var56 g a -> Var56 (snoc56 g B) a
vs56 = \ x, var, vz56, vs56 => vs56 _ _ _ (x var vz56 vs56)

Tm56 : Con56 -> Ty56 -> Type
Tm56 = \ g, a =>
    (Tm56    : Con56 -> Ty56 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var56 g a -> Tm56 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm56 (snoc56 g a) B -> Tm56 g (arr56 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm56 g (arr56 a B) -> Tm56 g a -> Tm56 g B)
 -> Tm56 g a

var56 : {g : _} -> {a : _} -> Var56 g a -> Tm56 g a
var56 = \ x, tm, var56, lam, app => var56 _ _ x

lam56 : {g : _} -> {a : _} -> {B : _} -> Tm56 (snoc56 g a) B -> Tm56 g (arr56 a B)
lam56 = \ t, tm, var56, lam56, app => lam56 _ _ _ (t tm var56 lam56 app)

app56 : {g:_}->{a:_}->{B:_} -> Tm56 g (arr56 a B) -> Tm56 g a -> Tm56 g B
app56 = \ t, u, tm, var56, lam56, app56 => app56 _ _ _ (t tm var56 lam56 app56) (u tm var56 lam56 app56)

v056 : {g:_}->{a:_} -> Tm56 (snoc56 g a) a
v056 = var56 vz56

v156 : {g:_}->{a:_}-> {B:_}-> Tm56 (snoc56 (snoc56 g a) B) a
v156 = var56 (vs56 vz56)

v256 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm56 (snoc56 (snoc56 (snoc56 g a) B) C) a
v256 = var56 (vs56 (vs56 vz56))

v356 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm56 (snoc56 (snoc56 (snoc56 (snoc56 g a) B) C) D) a
v356 = var56 (vs56 (vs56 (vs56 vz56)))

v456 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm56 (snoc56 (snoc56 (snoc56 (snoc56 (snoc56 g a) B) C) D) E) a
v456 = var56 (vs56 (vs56 (vs56 (vs56 vz56))))

test56 : {g:_}-> {a:_} -> Tm56 g (arr56 (arr56 a a) (arr56 a a))
test56  = lam56 (lam56 (app56 v156 (app56 v156 (app56 v156 (app56 v156 (app56 v156 (app56 v156 v056)))))))
Ty57 : Type
Ty57 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty57 : Ty57
empty57 = \ _, empty, _ => empty

arr57 : Ty57 -> Ty57 -> Ty57
arr57 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con57 : Type
Con57 = (Con57 : Type)
 ->(nil  : Con57)
 ->(snoc : Con57 -> Ty57 -> Con57)
 -> Con57

nil57 : Con57
nil57 = \ con, nil57, snoc => nil57

snoc57 : Con57 -> Ty57 -> Con57
snoc57 = \ g, a, con, nil57, snoc57 => snoc57 (g con nil57 snoc57) a

Var57 : Con57 -> Ty57 -> Type
Var57 = \ g, a =>
    (Var57 : Con57 -> Ty57 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var57 (snoc57 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var57 g a -> Var57 (snoc57 g b) a)
 -> Var57 g a

vz57 : {g : _}-> {a : _} -> Var57 (snoc57 g a) a
vz57 = \ var, vz57, vs => vz57 _ _

vs57 : {g : _} -> {B : _} -> {a : _} -> Var57 g a -> Var57 (snoc57 g B) a
vs57 = \ x, var, vz57, vs57 => vs57 _ _ _ (x var vz57 vs57)

Tm57 : Con57 -> Ty57 -> Type
Tm57 = \ g, a =>
    (Tm57    : Con57 -> Ty57 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var57 g a -> Tm57 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm57 (snoc57 g a) B -> Tm57 g (arr57 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm57 g (arr57 a B) -> Tm57 g a -> Tm57 g B)
 -> Tm57 g a

var57 : {g : _} -> {a : _} -> Var57 g a -> Tm57 g a
var57 = \ x, tm, var57, lam, app => var57 _ _ x

lam57 : {g : _} -> {a : _} -> {B : _} -> Tm57 (snoc57 g a) B -> Tm57 g (arr57 a B)
lam57 = \ t, tm, var57, lam57, app => lam57 _ _ _ (t tm var57 lam57 app)

app57 : {g:_}->{a:_}->{B:_} -> Tm57 g (arr57 a B) -> Tm57 g a -> Tm57 g B
app57 = \ t, u, tm, var57, lam57, app57 => app57 _ _ _ (t tm var57 lam57 app57) (u tm var57 lam57 app57)

v057 : {g:_}->{a:_} -> Tm57 (snoc57 g a) a
v057 = var57 vz57

v157 : {g:_}->{a:_}-> {B:_}-> Tm57 (snoc57 (snoc57 g a) B) a
v157 = var57 (vs57 vz57)

v257 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm57 (snoc57 (snoc57 (snoc57 g a) B) C) a
v257 = var57 (vs57 (vs57 vz57))

v357 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm57 (snoc57 (snoc57 (snoc57 (snoc57 g a) B) C) D) a
v357 = var57 (vs57 (vs57 (vs57 vz57)))

v457 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm57 (snoc57 (snoc57 (snoc57 (snoc57 (snoc57 g a) B) C) D) E) a
v457 = var57 (vs57 (vs57 (vs57 (vs57 vz57))))

test57 : {g:_}-> {a:_} -> Tm57 g (arr57 (arr57 a a) (arr57 a a))
test57  = lam57 (lam57 (app57 v157 (app57 v157 (app57 v157 (app57 v157 (app57 v157 (app57 v157 v057)))))))
Ty58 : Type
Ty58 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty58 : Ty58
empty58 = \ _, empty, _ => empty

arr58 : Ty58 -> Ty58 -> Ty58
arr58 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con58 : Type
Con58 = (Con58 : Type)
 ->(nil  : Con58)
 ->(snoc : Con58 -> Ty58 -> Con58)
 -> Con58

nil58 : Con58
nil58 = \ con, nil58, snoc => nil58

snoc58 : Con58 -> Ty58 -> Con58
snoc58 = \ g, a, con, nil58, snoc58 => snoc58 (g con nil58 snoc58) a

Var58 : Con58 -> Ty58 -> Type
Var58 = \ g, a =>
    (Var58 : Con58 -> Ty58 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var58 (snoc58 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var58 g a -> Var58 (snoc58 g b) a)
 -> Var58 g a

vz58 : {g : _}-> {a : _} -> Var58 (snoc58 g a) a
vz58 = \ var, vz58, vs => vz58 _ _

vs58 : {g : _} -> {B : _} -> {a : _} -> Var58 g a -> Var58 (snoc58 g B) a
vs58 = \ x, var, vz58, vs58 => vs58 _ _ _ (x var vz58 vs58)

Tm58 : Con58 -> Ty58 -> Type
Tm58 = \ g, a =>
    (Tm58    : Con58 -> Ty58 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var58 g a -> Tm58 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm58 (snoc58 g a) B -> Tm58 g (arr58 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm58 g (arr58 a B) -> Tm58 g a -> Tm58 g B)
 -> Tm58 g a

var58 : {g : _} -> {a : _} -> Var58 g a -> Tm58 g a
var58 = \ x, tm, var58, lam, app => var58 _ _ x

lam58 : {g : _} -> {a : _} -> {B : _} -> Tm58 (snoc58 g a) B -> Tm58 g (arr58 a B)
lam58 = \ t, tm, var58, lam58, app => lam58 _ _ _ (t tm var58 lam58 app)

app58 : {g:_}->{a:_}->{B:_} -> Tm58 g (arr58 a B) -> Tm58 g a -> Tm58 g B
app58 = \ t, u, tm, var58, lam58, app58 => app58 _ _ _ (t tm var58 lam58 app58) (u tm var58 lam58 app58)

v058 : {g:_}->{a:_} -> Tm58 (snoc58 g a) a
v058 = var58 vz58

v158 : {g:_}->{a:_}-> {B:_}-> Tm58 (snoc58 (snoc58 g a) B) a
v158 = var58 (vs58 vz58)

v258 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm58 (snoc58 (snoc58 (snoc58 g a) B) C) a
v258 = var58 (vs58 (vs58 vz58))

v358 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm58 (snoc58 (snoc58 (snoc58 (snoc58 g a) B) C) D) a
v358 = var58 (vs58 (vs58 (vs58 vz58)))

v458 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm58 (snoc58 (snoc58 (snoc58 (snoc58 (snoc58 g a) B) C) D) E) a
v458 = var58 (vs58 (vs58 (vs58 (vs58 vz58))))

test58 : {g:_}-> {a:_} -> Tm58 g (arr58 (arr58 a a) (arr58 a a))
test58  = lam58 (lam58 (app58 v158 (app58 v158 (app58 v158 (app58 v158 (app58 v158 (app58 v158 v058)))))))
Ty59 : Type
Ty59 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty59 : Ty59
empty59 = \ _, empty, _ => empty

arr59 : Ty59 -> Ty59 -> Ty59
arr59 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con59 : Type
Con59 = (Con59 : Type)
 ->(nil  : Con59)
 ->(snoc : Con59 -> Ty59 -> Con59)
 -> Con59

nil59 : Con59
nil59 = \ con, nil59, snoc => nil59

snoc59 : Con59 -> Ty59 -> Con59
snoc59 = \ g, a, con, nil59, snoc59 => snoc59 (g con nil59 snoc59) a

Var59 : Con59 -> Ty59 -> Type
Var59 = \ g, a =>
    (Var59 : Con59 -> Ty59 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var59 (snoc59 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var59 g a -> Var59 (snoc59 g b) a)
 -> Var59 g a

vz59 : {g : _}-> {a : _} -> Var59 (snoc59 g a) a
vz59 = \ var, vz59, vs => vz59 _ _

vs59 : {g : _} -> {B : _} -> {a : _} -> Var59 g a -> Var59 (snoc59 g B) a
vs59 = \ x, var, vz59, vs59 => vs59 _ _ _ (x var vz59 vs59)

Tm59 : Con59 -> Ty59 -> Type
Tm59 = \ g, a =>
    (Tm59    : Con59 -> Ty59 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var59 g a -> Tm59 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm59 (snoc59 g a) B -> Tm59 g (arr59 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm59 g (arr59 a B) -> Tm59 g a -> Tm59 g B)
 -> Tm59 g a

var59 : {g : _} -> {a : _} -> Var59 g a -> Tm59 g a
var59 = \ x, tm, var59, lam, app => var59 _ _ x

lam59 : {g : _} -> {a : _} -> {B : _} -> Tm59 (snoc59 g a) B -> Tm59 g (arr59 a B)
lam59 = \ t, tm, var59, lam59, app => lam59 _ _ _ (t tm var59 lam59 app)

app59 : {g:_}->{a:_}->{B:_} -> Tm59 g (arr59 a B) -> Tm59 g a -> Tm59 g B
app59 = \ t, u, tm, var59, lam59, app59 => app59 _ _ _ (t tm var59 lam59 app59) (u tm var59 lam59 app59)

v059 : {g:_}->{a:_} -> Tm59 (snoc59 g a) a
v059 = var59 vz59

v159 : {g:_}->{a:_}-> {B:_}-> Tm59 (snoc59 (snoc59 g a) B) a
v159 = var59 (vs59 vz59)

v259 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm59 (snoc59 (snoc59 (snoc59 g a) B) C) a
v259 = var59 (vs59 (vs59 vz59))

v359 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm59 (snoc59 (snoc59 (snoc59 (snoc59 g a) B) C) D) a
v359 = var59 (vs59 (vs59 (vs59 vz59)))

v459 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm59 (snoc59 (snoc59 (snoc59 (snoc59 (snoc59 g a) B) C) D) E) a
v459 = var59 (vs59 (vs59 (vs59 (vs59 vz59))))

test59 : {g:_}-> {a:_} -> Tm59 g (arr59 (arr59 a a) (arr59 a a))
test59  = lam59 (lam59 (app59 v159 (app59 v159 (app59 v159 (app59 v159 (app59 v159 (app59 v159 v059)))))))
Ty60 : Type
Ty60 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty60 : Ty60
empty60 = \ _, empty, _ => empty

arr60 : Ty60 -> Ty60 -> Ty60
arr60 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con60 : Type
Con60 = (Con60 : Type)
 ->(nil  : Con60)
 ->(snoc : Con60 -> Ty60 -> Con60)
 -> Con60

nil60 : Con60
nil60 = \ con, nil60, snoc => nil60

snoc60 : Con60 -> Ty60 -> Con60
snoc60 = \ g, a, con, nil60, snoc60 => snoc60 (g con nil60 snoc60) a

Var60 : Con60 -> Ty60 -> Type
Var60 = \ g, a =>
    (Var60 : Con60 -> Ty60 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var60 (snoc60 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var60 g a -> Var60 (snoc60 g b) a)
 -> Var60 g a

vz60 : {g : _}-> {a : _} -> Var60 (snoc60 g a) a
vz60 = \ var, vz60, vs => vz60 _ _

vs60 : {g : _} -> {B : _} -> {a : _} -> Var60 g a -> Var60 (snoc60 g B) a
vs60 = \ x, var, vz60, vs60 => vs60 _ _ _ (x var vz60 vs60)

Tm60 : Con60 -> Ty60 -> Type
Tm60 = \ g, a =>
    (Tm60    : Con60 -> Ty60 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var60 g a -> Tm60 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm60 (snoc60 g a) B -> Tm60 g (arr60 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm60 g (arr60 a B) -> Tm60 g a -> Tm60 g B)
 -> Tm60 g a

var60 : {g : _} -> {a : _} -> Var60 g a -> Tm60 g a
var60 = \ x, tm, var60, lam, app => var60 _ _ x

lam60 : {g : _} -> {a : _} -> {B : _} -> Tm60 (snoc60 g a) B -> Tm60 g (arr60 a B)
lam60 = \ t, tm, var60, lam60, app => lam60 _ _ _ (t tm var60 lam60 app)

app60 : {g:_}->{a:_}->{B:_} -> Tm60 g (arr60 a B) -> Tm60 g a -> Tm60 g B
app60 = \ t, u, tm, var60, lam60, app60 => app60 _ _ _ (t tm var60 lam60 app60) (u tm var60 lam60 app60)

v060 : {g:_}->{a:_} -> Tm60 (snoc60 g a) a
v060 = var60 vz60

v160 : {g:_}->{a:_}-> {B:_}-> Tm60 (snoc60 (snoc60 g a) B) a
v160 = var60 (vs60 vz60)

v260 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm60 (snoc60 (snoc60 (snoc60 g a) B) C) a
v260 = var60 (vs60 (vs60 vz60))

v360 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm60 (snoc60 (snoc60 (snoc60 (snoc60 g a) B) C) D) a
v360 = var60 (vs60 (vs60 (vs60 vz60)))

v460 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm60 (snoc60 (snoc60 (snoc60 (snoc60 (snoc60 g a) B) C) D) E) a
v460 = var60 (vs60 (vs60 (vs60 (vs60 vz60))))

test60 : {g:_}-> {a:_} -> Tm60 g (arr60 (arr60 a a) (arr60 a a))
test60  = lam60 (lam60 (app60 v160 (app60 v160 (app60 v160 (app60 v160 (app60 v160 (app60 v160 v060)))))))
Ty61 : Type
Ty61 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty61 : Ty61
empty61 = \ _, empty, _ => empty

arr61 : Ty61 -> Ty61 -> Ty61
arr61 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con61 : Type
Con61 = (Con61 : Type)
 ->(nil  : Con61)
 ->(snoc : Con61 -> Ty61 -> Con61)
 -> Con61

nil61 : Con61
nil61 = \ con, nil61, snoc => nil61

snoc61 : Con61 -> Ty61 -> Con61
snoc61 = \ g, a, con, nil61, snoc61 => snoc61 (g con nil61 snoc61) a

Var61 : Con61 -> Ty61 -> Type
Var61 = \ g, a =>
    (Var61 : Con61 -> Ty61 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var61 (snoc61 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var61 g a -> Var61 (snoc61 g b) a)
 -> Var61 g a

vz61 : {g : _}-> {a : _} -> Var61 (snoc61 g a) a
vz61 = \ var, vz61, vs => vz61 _ _

vs61 : {g : _} -> {B : _} -> {a : _} -> Var61 g a -> Var61 (snoc61 g B) a
vs61 = \ x, var, vz61, vs61 => vs61 _ _ _ (x var vz61 vs61)

Tm61 : Con61 -> Ty61 -> Type
Tm61 = \ g, a =>
    (Tm61    : Con61 -> Ty61 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var61 g a -> Tm61 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm61 (snoc61 g a) B -> Tm61 g (arr61 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm61 g (arr61 a B) -> Tm61 g a -> Tm61 g B)
 -> Tm61 g a

var61 : {g : _} -> {a : _} -> Var61 g a -> Tm61 g a
var61 = \ x, tm, var61, lam, app => var61 _ _ x

lam61 : {g : _} -> {a : _} -> {B : _} -> Tm61 (snoc61 g a) B -> Tm61 g (arr61 a B)
lam61 = \ t, tm, var61, lam61, app => lam61 _ _ _ (t tm var61 lam61 app)

app61 : {g:_}->{a:_}->{B:_} -> Tm61 g (arr61 a B) -> Tm61 g a -> Tm61 g B
app61 = \ t, u, tm, var61, lam61, app61 => app61 _ _ _ (t tm var61 lam61 app61) (u tm var61 lam61 app61)

v061 : {g:_}->{a:_} -> Tm61 (snoc61 g a) a
v061 = var61 vz61

v161 : {g:_}->{a:_}-> {B:_}-> Tm61 (snoc61 (snoc61 g a) B) a
v161 = var61 (vs61 vz61)

v261 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm61 (snoc61 (snoc61 (snoc61 g a) B) C) a
v261 = var61 (vs61 (vs61 vz61))

v361 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm61 (snoc61 (snoc61 (snoc61 (snoc61 g a) B) C) D) a
v361 = var61 (vs61 (vs61 (vs61 vz61)))

v461 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm61 (snoc61 (snoc61 (snoc61 (snoc61 (snoc61 g a) B) C) D) E) a
v461 = var61 (vs61 (vs61 (vs61 (vs61 vz61))))

test61 : {g:_}-> {a:_} -> Tm61 g (arr61 (arr61 a a) (arr61 a a))
test61  = lam61 (lam61 (app61 v161 (app61 v161 (app61 v161 (app61 v161 (app61 v161 (app61 v161 v061)))))))
Ty62 : Type
Ty62 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty62 : Ty62
empty62 = \ _, empty, _ => empty

arr62 : Ty62 -> Ty62 -> Ty62
arr62 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con62 : Type
Con62 = (Con62 : Type)
 ->(nil  : Con62)
 ->(snoc : Con62 -> Ty62 -> Con62)
 -> Con62

nil62 : Con62
nil62 = \ con, nil62, snoc => nil62

snoc62 : Con62 -> Ty62 -> Con62
snoc62 = \ g, a, con, nil62, snoc62 => snoc62 (g con nil62 snoc62) a

Var62 : Con62 -> Ty62 -> Type
Var62 = \ g, a =>
    (Var62 : Con62 -> Ty62 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var62 (snoc62 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var62 g a -> Var62 (snoc62 g b) a)
 -> Var62 g a

vz62 : {g : _}-> {a : _} -> Var62 (snoc62 g a) a
vz62 = \ var, vz62, vs => vz62 _ _

vs62 : {g : _} -> {B : _} -> {a : _} -> Var62 g a -> Var62 (snoc62 g B) a
vs62 = \ x, var, vz62, vs62 => vs62 _ _ _ (x var vz62 vs62)

Tm62 : Con62 -> Ty62 -> Type
Tm62 = \ g, a =>
    (Tm62    : Con62 -> Ty62 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var62 g a -> Tm62 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm62 (snoc62 g a) B -> Tm62 g (arr62 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm62 g (arr62 a B) -> Tm62 g a -> Tm62 g B)
 -> Tm62 g a

var62 : {g : _} -> {a : _} -> Var62 g a -> Tm62 g a
var62 = \ x, tm, var62, lam, app => var62 _ _ x

lam62 : {g : _} -> {a : _} -> {B : _} -> Tm62 (snoc62 g a) B -> Tm62 g (arr62 a B)
lam62 = \ t, tm, var62, lam62, app => lam62 _ _ _ (t tm var62 lam62 app)

app62 : {g:_}->{a:_}->{B:_} -> Tm62 g (arr62 a B) -> Tm62 g a -> Tm62 g B
app62 = \ t, u, tm, var62, lam62, app62 => app62 _ _ _ (t tm var62 lam62 app62) (u tm var62 lam62 app62)

v062 : {g:_}->{a:_} -> Tm62 (snoc62 g a) a
v062 = var62 vz62

v162 : {g:_}->{a:_}-> {B:_}-> Tm62 (snoc62 (snoc62 g a) B) a
v162 = var62 (vs62 vz62)

v262 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm62 (snoc62 (snoc62 (snoc62 g a) B) C) a
v262 = var62 (vs62 (vs62 vz62))

v362 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm62 (snoc62 (snoc62 (snoc62 (snoc62 g a) B) C) D) a
v362 = var62 (vs62 (vs62 (vs62 vz62)))

v462 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm62 (snoc62 (snoc62 (snoc62 (snoc62 (snoc62 g a) B) C) D) E) a
v462 = var62 (vs62 (vs62 (vs62 (vs62 vz62))))

test62 : {g:_}-> {a:_} -> Tm62 g (arr62 (arr62 a a) (arr62 a a))
test62  = lam62 (lam62 (app62 v162 (app62 v162 (app62 v162 (app62 v162 (app62 v162 (app62 v162 v062)))))))
Ty63 : Type
Ty63 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty63 : Ty63
empty63 = \ _, empty, _ => empty

arr63 : Ty63 -> Ty63 -> Ty63
arr63 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con63 : Type
Con63 = (Con63 : Type)
 ->(nil  : Con63)
 ->(snoc : Con63 -> Ty63 -> Con63)
 -> Con63

nil63 : Con63
nil63 = \ con, nil63, snoc => nil63

snoc63 : Con63 -> Ty63 -> Con63
snoc63 = \ g, a, con, nil63, snoc63 => snoc63 (g con nil63 snoc63) a

Var63 : Con63 -> Ty63 -> Type
Var63 = \ g, a =>
    (Var63 : Con63 -> Ty63 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var63 (snoc63 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var63 g a -> Var63 (snoc63 g b) a)
 -> Var63 g a

vz63 : {g : _}-> {a : _} -> Var63 (snoc63 g a) a
vz63 = \ var, vz63, vs => vz63 _ _

vs63 : {g : _} -> {B : _} -> {a : _} -> Var63 g a -> Var63 (snoc63 g B) a
vs63 = \ x, var, vz63, vs63 => vs63 _ _ _ (x var vz63 vs63)

Tm63 : Con63 -> Ty63 -> Type
Tm63 = \ g, a =>
    (Tm63    : Con63 -> Ty63 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var63 g a -> Tm63 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm63 (snoc63 g a) B -> Tm63 g (arr63 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm63 g (arr63 a B) -> Tm63 g a -> Tm63 g B)
 -> Tm63 g a

var63 : {g : _} -> {a : _} -> Var63 g a -> Tm63 g a
var63 = \ x, tm, var63, lam, app => var63 _ _ x

lam63 : {g : _} -> {a : _} -> {B : _} -> Tm63 (snoc63 g a) B -> Tm63 g (arr63 a B)
lam63 = \ t, tm, var63, lam63, app => lam63 _ _ _ (t tm var63 lam63 app)

app63 : {g:_}->{a:_}->{B:_} -> Tm63 g (arr63 a B) -> Tm63 g a -> Tm63 g B
app63 = \ t, u, tm, var63, lam63, app63 => app63 _ _ _ (t tm var63 lam63 app63) (u tm var63 lam63 app63)

v063 : {g:_}->{a:_} -> Tm63 (snoc63 g a) a
v063 = var63 vz63

v163 : {g:_}->{a:_}-> {B:_}-> Tm63 (snoc63 (snoc63 g a) B) a
v163 = var63 (vs63 vz63)

v263 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm63 (snoc63 (snoc63 (snoc63 g a) B) C) a
v263 = var63 (vs63 (vs63 vz63))

v363 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm63 (snoc63 (snoc63 (snoc63 (snoc63 g a) B) C) D) a
v363 = var63 (vs63 (vs63 (vs63 vz63)))

v463 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm63 (snoc63 (snoc63 (snoc63 (snoc63 (snoc63 g a) B) C) D) E) a
v463 = var63 (vs63 (vs63 (vs63 (vs63 vz63))))

test63 : {g:_}-> {a:_} -> Tm63 g (arr63 (arr63 a a) (arr63 a a))
test63  = lam63 (lam63 (app63 v163 (app63 v163 (app63 v163 (app63 v163 (app63 v163 (app63 v163 v063)))))))
Ty64 : Type
Ty64 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty64 : Ty64
empty64 = \ _, empty, _ => empty

arr64 : Ty64 -> Ty64 -> Ty64
arr64 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con64 : Type
Con64 = (Con64 : Type)
 ->(nil  : Con64)
 ->(snoc : Con64 -> Ty64 -> Con64)
 -> Con64

nil64 : Con64
nil64 = \ con, nil64, snoc => nil64

snoc64 : Con64 -> Ty64 -> Con64
snoc64 = \ g, a, con, nil64, snoc64 => snoc64 (g con nil64 snoc64) a

Var64 : Con64 -> Ty64 -> Type
Var64 = \ g, a =>
    (Var64 : Con64 -> Ty64 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var64 (snoc64 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var64 g a -> Var64 (snoc64 g b) a)
 -> Var64 g a

vz64 : {g : _}-> {a : _} -> Var64 (snoc64 g a) a
vz64 = \ var, vz64, vs => vz64 _ _

vs64 : {g : _} -> {B : _} -> {a : _} -> Var64 g a -> Var64 (snoc64 g B) a
vs64 = \ x, var, vz64, vs64 => vs64 _ _ _ (x var vz64 vs64)

Tm64 : Con64 -> Ty64 -> Type
Tm64 = \ g, a =>
    (Tm64    : Con64 -> Ty64 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var64 g a -> Tm64 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm64 (snoc64 g a) B -> Tm64 g (arr64 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm64 g (arr64 a B) -> Tm64 g a -> Tm64 g B)
 -> Tm64 g a

var64 : {g : _} -> {a : _} -> Var64 g a -> Tm64 g a
var64 = \ x, tm, var64, lam, app => var64 _ _ x

lam64 : {g : _} -> {a : _} -> {B : _} -> Tm64 (snoc64 g a) B -> Tm64 g (arr64 a B)
lam64 = \ t, tm, var64, lam64, app => lam64 _ _ _ (t tm var64 lam64 app)

app64 : {g:_}->{a:_}->{B:_} -> Tm64 g (arr64 a B) -> Tm64 g a -> Tm64 g B
app64 = \ t, u, tm, var64, lam64, app64 => app64 _ _ _ (t tm var64 lam64 app64) (u tm var64 lam64 app64)

v064 : {g:_}->{a:_} -> Tm64 (snoc64 g a) a
v064 = var64 vz64

v164 : {g:_}->{a:_}-> {B:_}-> Tm64 (snoc64 (snoc64 g a) B) a
v164 = var64 (vs64 vz64)

v264 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm64 (snoc64 (snoc64 (snoc64 g a) B) C) a
v264 = var64 (vs64 (vs64 vz64))

v364 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm64 (snoc64 (snoc64 (snoc64 (snoc64 g a) B) C) D) a
v364 = var64 (vs64 (vs64 (vs64 vz64)))

v464 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm64 (snoc64 (snoc64 (snoc64 (snoc64 (snoc64 g a) B) C) D) E) a
v464 = var64 (vs64 (vs64 (vs64 (vs64 vz64))))

test64 : {g:_}-> {a:_} -> Tm64 g (arr64 (arr64 a a) (arr64 a a))
test64  = lam64 (lam64 (app64 v164 (app64 v164 (app64 v164 (app64 v164 (app64 v164 (app64 v164 v064)))))))
Ty65 : Type
Ty65 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty65 : Ty65
empty65 = \ _, empty, _ => empty

arr65 : Ty65 -> Ty65 -> Ty65
arr65 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con65 : Type
Con65 = (Con65 : Type)
 ->(nil  : Con65)
 ->(snoc : Con65 -> Ty65 -> Con65)
 -> Con65

nil65 : Con65
nil65 = \ con, nil65, snoc => nil65

snoc65 : Con65 -> Ty65 -> Con65
snoc65 = \ g, a, con, nil65, snoc65 => snoc65 (g con nil65 snoc65) a

Var65 : Con65 -> Ty65 -> Type
Var65 = \ g, a =>
    (Var65 : Con65 -> Ty65 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var65 (snoc65 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var65 g a -> Var65 (snoc65 g b) a)
 -> Var65 g a

vz65 : {g : _}-> {a : _} -> Var65 (snoc65 g a) a
vz65 = \ var, vz65, vs => vz65 _ _

vs65 : {g : _} -> {B : _} -> {a : _} -> Var65 g a -> Var65 (snoc65 g B) a
vs65 = \ x, var, vz65, vs65 => vs65 _ _ _ (x var vz65 vs65)

Tm65 : Con65 -> Ty65 -> Type
Tm65 = \ g, a =>
    (Tm65    : Con65 -> Ty65 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var65 g a -> Tm65 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm65 (snoc65 g a) B -> Tm65 g (arr65 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm65 g (arr65 a B) -> Tm65 g a -> Tm65 g B)
 -> Tm65 g a

var65 : {g : _} -> {a : _} -> Var65 g a -> Tm65 g a
var65 = \ x, tm, var65, lam, app => var65 _ _ x

lam65 : {g : _} -> {a : _} -> {B : _} -> Tm65 (snoc65 g a) B -> Tm65 g (arr65 a B)
lam65 = \ t, tm, var65, lam65, app => lam65 _ _ _ (t tm var65 lam65 app)

app65 : {g:_}->{a:_}->{B:_} -> Tm65 g (arr65 a B) -> Tm65 g a -> Tm65 g B
app65 = \ t, u, tm, var65, lam65, app65 => app65 _ _ _ (t tm var65 lam65 app65) (u tm var65 lam65 app65)

v065 : {g:_}->{a:_} -> Tm65 (snoc65 g a) a
v065 = var65 vz65

v165 : {g:_}->{a:_}-> {B:_}-> Tm65 (snoc65 (snoc65 g a) B) a
v165 = var65 (vs65 vz65)

v265 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm65 (snoc65 (snoc65 (snoc65 g a) B) C) a
v265 = var65 (vs65 (vs65 vz65))

v365 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm65 (snoc65 (snoc65 (snoc65 (snoc65 g a) B) C) D) a
v365 = var65 (vs65 (vs65 (vs65 vz65)))

v465 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm65 (snoc65 (snoc65 (snoc65 (snoc65 (snoc65 g a) B) C) D) E) a
v465 = var65 (vs65 (vs65 (vs65 (vs65 vz65))))

test65 : {g:_}-> {a:_} -> Tm65 g (arr65 (arr65 a a) (arr65 a a))
test65  = lam65 (lam65 (app65 v165 (app65 v165 (app65 v165 (app65 v165 (app65 v165 (app65 v165 v065)))))))
Ty66 : Type
Ty66 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty66 : Ty66
empty66 = \ _, empty, _ => empty

arr66 : Ty66 -> Ty66 -> Ty66
arr66 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con66 : Type
Con66 = (Con66 : Type)
 ->(nil  : Con66)
 ->(snoc : Con66 -> Ty66 -> Con66)
 -> Con66

nil66 : Con66
nil66 = \ con, nil66, snoc => nil66

snoc66 : Con66 -> Ty66 -> Con66
snoc66 = \ g, a, con, nil66, snoc66 => snoc66 (g con nil66 snoc66) a

Var66 : Con66 -> Ty66 -> Type
Var66 = \ g, a =>
    (Var66 : Con66 -> Ty66 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var66 (snoc66 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var66 g a -> Var66 (snoc66 g b) a)
 -> Var66 g a

vz66 : {g : _}-> {a : _} -> Var66 (snoc66 g a) a
vz66 = \ var, vz66, vs => vz66 _ _

vs66 : {g : _} -> {B : _} -> {a : _} -> Var66 g a -> Var66 (snoc66 g B) a
vs66 = \ x, var, vz66, vs66 => vs66 _ _ _ (x var vz66 vs66)

Tm66 : Con66 -> Ty66 -> Type
Tm66 = \ g, a =>
    (Tm66    : Con66 -> Ty66 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var66 g a -> Tm66 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm66 (snoc66 g a) B -> Tm66 g (arr66 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm66 g (arr66 a B) -> Tm66 g a -> Tm66 g B)
 -> Tm66 g a

var66 : {g : _} -> {a : _} -> Var66 g a -> Tm66 g a
var66 = \ x, tm, var66, lam, app => var66 _ _ x

lam66 : {g : _} -> {a : _} -> {B : _} -> Tm66 (snoc66 g a) B -> Tm66 g (arr66 a B)
lam66 = \ t, tm, var66, lam66, app => lam66 _ _ _ (t tm var66 lam66 app)

app66 : {g:_}->{a:_}->{B:_} -> Tm66 g (arr66 a B) -> Tm66 g a -> Tm66 g B
app66 = \ t, u, tm, var66, lam66, app66 => app66 _ _ _ (t tm var66 lam66 app66) (u tm var66 lam66 app66)

v066 : {g:_}->{a:_} -> Tm66 (snoc66 g a) a
v066 = var66 vz66

v166 : {g:_}->{a:_}-> {B:_}-> Tm66 (snoc66 (snoc66 g a) B) a
v166 = var66 (vs66 vz66)

v266 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm66 (snoc66 (snoc66 (snoc66 g a) B) C) a
v266 = var66 (vs66 (vs66 vz66))

v366 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm66 (snoc66 (snoc66 (snoc66 (snoc66 g a) B) C) D) a
v366 = var66 (vs66 (vs66 (vs66 vz66)))

v466 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm66 (snoc66 (snoc66 (snoc66 (snoc66 (snoc66 g a) B) C) D) E) a
v466 = var66 (vs66 (vs66 (vs66 (vs66 vz66))))

test66 : {g:_}-> {a:_} -> Tm66 g (arr66 (arr66 a a) (arr66 a a))
test66  = lam66 (lam66 (app66 v166 (app66 v166 (app66 v166 (app66 v166 (app66 v166 (app66 v166 v066)))))))
Ty67 : Type
Ty67 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty67 : Ty67
empty67 = \ _, empty, _ => empty

arr67 : Ty67 -> Ty67 -> Ty67
arr67 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con67 : Type
Con67 = (Con67 : Type)
 ->(nil  : Con67)
 ->(snoc : Con67 -> Ty67 -> Con67)
 -> Con67

nil67 : Con67
nil67 = \ con, nil67, snoc => nil67

snoc67 : Con67 -> Ty67 -> Con67
snoc67 = \ g, a, con, nil67, snoc67 => snoc67 (g con nil67 snoc67) a

Var67 : Con67 -> Ty67 -> Type
Var67 = \ g, a =>
    (Var67 : Con67 -> Ty67 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var67 (snoc67 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var67 g a -> Var67 (snoc67 g b) a)
 -> Var67 g a

vz67 : {g : _}-> {a : _} -> Var67 (snoc67 g a) a
vz67 = \ var, vz67, vs => vz67 _ _

vs67 : {g : _} -> {B : _} -> {a : _} -> Var67 g a -> Var67 (snoc67 g B) a
vs67 = \ x, var, vz67, vs67 => vs67 _ _ _ (x var vz67 vs67)

Tm67 : Con67 -> Ty67 -> Type
Tm67 = \ g, a =>
    (Tm67    : Con67 -> Ty67 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var67 g a -> Tm67 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm67 (snoc67 g a) B -> Tm67 g (arr67 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm67 g (arr67 a B) -> Tm67 g a -> Tm67 g B)
 -> Tm67 g a

var67 : {g : _} -> {a : _} -> Var67 g a -> Tm67 g a
var67 = \ x, tm, var67, lam, app => var67 _ _ x

lam67 : {g : _} -> {a : _} -> {B : _} -> Tm67 (snoc67 g a) B -> Tm67 g (arr67 a B)
lam67 = \ t, tm, var67, lam67, app => lam67 _ _ _ (t tm var67 lam67 app)

app67 : {g:_}->{a:_}->{B:_} -> Tm67 g (arr67 a B) -> Tm67 g a -> Tm67 g B
app67 = \ t, u, tm, var67, lam67, app67 => app67 _ _ _ (t tm var67 lam67 app67) (u tm var67 lam67 app67)

v067 : {g:_}->{a:_} -> Tm67 (snoc67 g a) a
v067 = var67 vz67

v167 : {g:_}->{a:_}-> {B:_}-> Tm67 (snoc67 (snoc67 g a) B) a
v167 = var67 (vs67 vz67)

v267 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm67 (snoc67 (snoc67 (snoc67 g a) B) C) a
v267 = var67 (vs67 (vs67 vz67))

v367 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm67 (snoc67 (snoc67 (snoc67 (snoc67 g a) B) C) D) a
v367 = var67 (vs67 (vs67 (vs67 vz67)))

v467 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm67 (snoc67 (snoc67 (snoc67 (snoc67 (snoc67 g a) B) C) D) E) a
v467 = var67 (vs67 (vs67 (vs67 (vs67 vz67))))

test67 : {g:_}-> {a:_} -> Tm67 g (arr67 (arr67 a a) (arr67 a a))
test67  = lam67 (lam67 (app67 v167 (app67 v167 (app67 v167 (app67 v167 (app67 v167 (app67 v167 v067)))))))
Ty68 : Type
Ty68 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty68 : Ty68
empty68 = \ _, empty, _ => empty

arr68 : Ty68 -> Ty68 -> Ty68
arr68 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con68 : Type
Con68 = (Con68 : Type)
 ->(nil  : Con68)
 ->(snoc : Con68 -> Ty68 -> Con68)
 -> Con68

nil68 : Con68
nil68 = \ con, nil68, snoc => nil68

snoc68 : Con68 -> Ty68 -> Con68
snoc68 = \ g, a, con, nil68, snoc68 => snoc68 (g con nil68 snoc68) a

Var68 : Con68 -> Ty68 -> Type
Var68 = \ g, a =>
    (Var68 : Con68 -> Ty68 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var68 (snoc68 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var68 g a -> Var68 (snoc68 g b) a)
 -> Var68 g a

vz68 : {g : _}-> {a : _} -> Var68 (snoc68 g a) a
vz68 = \ var, vz68, vs => vz68 _ _

vs68 : {g : _} -> {B : _} -> {a : _} -> Var68 g a -> Var68 (snoc68 g B) a
vs68 = \ x, var, vz68, vs68 => vs68 _ _ _ (x var vz68 vs68)

Tm68 : Con68 -> Ty68 -> Type
Tm68 = \ g, a =>
    (Tm68    : Con68 -> Ty68 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var68 g a -> Tm68 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm68 (snoc68 g a) B -> Tm68 g (arr68 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm68 g (arr68 a B) -> Tm68 g a -> Tm68 g B)
 -> Tm68 g a

var68 : {g : _} -> {a : _} -> Var68 g a -> Tm68 g a
var68 = \ x, tm, var68, lam, app => var68 _ _ x

lam68 : {g : _} -> {a : _} -> {B : _} -> Tm68 (snoc68 g a) B -> Tm68 g (arr68 a B)
lam68 = \ t, tm, var68, lam68, app => lam68 _ _ _ (t tm var68 lam68 app)

app68 : {g:_}->{a:_}->{B:_} -> Tm68 g (arr68 a B) -> Tm68 g a -> Tm68 g B
app68 = \ t, u, tm, var68, lam68, app68 => app68 _ _ _ (t tm var68 lam68 app68) (u tm var68 lam68 app68)

v068 : {g:_}->{a:_} -> Tm68 (snoc68 g a) a
v068 = var68 vz68

v168 : {g:_}->{a:_}-> {B:_}-> Tm68 (snoc68 (snoc68 g a) B) a
v168 = var68 (vs68 vz68)

v268 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm68 (snoc68 (snoc68 (snoc68 g a) B) C) a
v268 = var68 (vs68 (vs68 vz68))

v368 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm68 (snoc68 (snoc68 (snoc68 (snoc68 g a) B) C) D) a
v368 = var68 (vs68 (vs68 (vs68 vz68)))

v468 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm68 (snoc68 (snoc68 (snoc68 (snoc68 (snoc68 g a) B) C) D) E) a
v468 = var68 (vs68 (vs68 (vs68 (vs68 vz68))))

test68 : {g:_}-> {a:_} -> Tm68 g (arr68 (arr68 a a) (arr68 a a))
test68  = lam68 (lam68 (app68 v168 (app68 v168 (app68 v168 (app68 v168 (app68 v168 (app68 v168 v068)))))))
Ty69 : Type
Ty69 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty69 : Ty69
empty69 = \ _, empty, _ => empty

arr69 : Ty69 -> Ty69 -> Ty69
arr69 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con69 : Type
Con69 = (Con69 : Type)
 ->(nil  : Con69)
 ->(snoc : Con69 -> Ty69 -> Con69)
 -> Con69

nil69 : Con69
nil69 = \ con, nil69, snoc => nil69

snoc69 : Con69 -> Ty69 -> Con69
snoc69 = \ g, a, con, nil69, snoc69 => snoc69 (g con nil69 snoc69) a

Var69 : Con69 -> Ty69 -> Type
Var69 = \ g, a =>
    (Var69 : Con69 -> Ty69 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var69 (snoc69 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var69 g a -> Var69 (snoc69 g b) a)
 -> Var69 g a

vz69 : {g : _}-> {a : _} -> Var69 (snoc69 g a) a
vz69 = \ var, vz69, vs => vz69 _ _

vs69 : {g : _} -> {B : _} -> {a : _} -> Var69 g a -> Var69 (snoc69 g B) a
vs69 = \ x, var, vz69, vs69 => vs69 _ _ _ (x var vz69 vs69)

Tm69 : Con69 -> Ty69 -> Type
Tm69 = \ g, a =>
    (Tm69    : Con69 -> Ty69 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var69 g a -> Tm69 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm69 (snoc69 g a) B -> Tm69 g (arr69 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm69 g (arr69 a B) -> Tm69 g a -> Tm69 g B)
 -> Tm69 g a

var69 : {g : _} -> {a : _} -> Var69 g a -> Tm69 g a
var69 = \ x, tm, var69, lam, app => var69 _ _ x

lam69 : {g : _} -> {a : _} -> {B : _} -> Tm69 (snoc69 g a) B -> Tm69 g (arr69 a B)
lam69 = \ t, tm, var69, lam69, app => lam69 _ _ _ (t tm var69 lam69 app)

app69 : {g:_}->{a:_}->{B:_} -> Tm69 g (arr69 a B) -> Tm69 g a -> Tm69 g B
app69 = \ t, u, tm, var69, lam69, app69 => app69 _ _ _ (t tm var69 lam69 app69) (u tm var69 lam69 app69)

v069 : {g:_}->{a:_} -> Tm69 (snoc69 g a) a
v069 = var69 vz69

v169 : {g:_}->{a:_}-> {B:_}-> Tm69 (snoc69 (snoc69 g a) B) a
v169 = var69 (vs69 vz69)

v269 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm69 (snoc69 (snoc69 (snoc69 g a) B) C) a
v269 = var69 (vs69 (vs69 vz69))

v369 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm69 (snoc69 (snoc69 (snoc69 (snoc69 g a) B) C) D) a
v369 = var69 (vs69 (vs69 (vs69 vz69)))

v469 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm69 (snoc69 (snoc69 (snoc69 (snoc69 (snoc69 g a) B) C) D) E) a
v469 = var69 (vs69 (vs69 (vs69 (vs69 vz69))))

test69 : {g:_}-> {a:_} -> Tm69 g (arr69 (arr69 a a) (arr69 a a))
test69  = lam69 (lam69 (app69 v169 (app69 v169 (app69 v169 (app69 v169 (app69 v169 (app69 v169 v069)))))))
Ty70 : Type
Ty70 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty70 : Ty70
empty70 = \ _, empty, _ => empty

arr70 : Ty70 -> Ty70 -> Ty70
arr70 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con70 : Type
Con70 = (Con70 : Type)
 ->(nil  : Con70)
 ->(snoc : Con70 -> Ty70 -> Con70)
 -> Con70

nil70 : Con70
nil70 = \ con, nil70, snoc => nil70

snoc70 : Con70 -> Ty70 -> Con70
snoc70 = \ g, a, con, nil70, snoc70 => snoc70 (g con nil70 snoc70) a

Var70 : Con70 -> Ty70 -> Type
Var70 = \ g, a =>
    (Var70 : Con70 -> Ty70 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var70 (snoc70 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var70 g a -> Var70 (snoc70 g b) a)
 -> Var70 g a

vz70 : {g : _}-> {a : _} -> Var70 (snoc70 g a) a
vz70 = \ var, vz70, vs => vz70 _ _

vs70 : {g : _} -> {B : _} -> {a : _} -> Var70 g a -> Var70 (snoc70 g B) a
vs70 = \ x, var, vz70, vs70 => vs70 _ _ _ (x var vz70 vs70)

Tm70 : Con70 -> Ty70 -> Type
Tm70 = \ g, a =>
    (Tm70    : Con70 -> Ty70 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var70 g a -> Tm70 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm70 (snoc70 g a) B -> Tm70 g (arr70 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm70 g (arr70 a B) -> Tm70 g a -> Tm70 g B)
 -> Tm70 g a

var70 : {g : _} -> {a : _} -> Var70 g a -> Tm70 g a
var70 = \ x, tm, var70, lam, app => var70 _ _ x

lam70 : {g : _} -> {a : _} -> {B : _} -> Tm70 (snoc70 g a) B -> Tm70 g (arr70 a B)
lam70 = \ t, tm, var70, lam70, app => lam70 _ _ _ (t tm var70 lam70 app)

app70 : {g:_}->{a:_}->{B:_} -> Tm70 g (arr70 a B) -> Tm70 g a -> Tm70 g B
app70 = \ t, u, tm, var70, lam70, app70 => app70 _ _ _ (t tm var70 lam70 app70) (u tm var70 lam70 app70)

v070 : {g:_}->{a:_} -> Tm70 (snoc70 g a) a
v070 = var70 vz70

v170 : {g:_}->{a:_}-> {B:_}-> Tm70 (snoc70 (snoc70 g a) B) a
v170 = var70 (vs70 vz70)

v270 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm70 (snoc70 (snoc70 (snoc70 g a) B) C) a
v270 = var70 (vs70 (vs70 vz70))

v370 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm70 (snoc70 (snoc70 (snoc70 (snoc70 g a) B) C) D) a
v370 = var70 (vs70 (vs70 (vs70 vz70)))

v470 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm70 (snoc70 (snoc70 (snoc70 (snoc70 (snoc70 g a) B) C) D) E) a
v470 = var70 (vs70 (vs70 (vs70 (vs70 vz70))))

test70 : {g:_}-> {a:_} -> Tm70 g (arr70 (arr70 a a) (arr70 a a))
test70  = lam70 (lam70 (app70 v170 (app70 v170 (app70 v170 (app70 v170 (app70 v170 (app70 v170 v070)))))))
Ty71 : Type
Ty71 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty71 : Ty71
empty71 = \ _, empty, _ => empty

arr71 : Ty71 -> Ty71 -> Ty71
arr71 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con71 : Type
Con71 = (Con71 : Type)
 ->(nil  : Con71)
 ->(snoc : Con71 -> Ty71 -> Con71)
 -> Con71

nil71 : Con71
nil71 = \ con, nil71, snoc => nil71

snoc71 : Con71 -> Ty71 -> Con71
snoc71 = \ g, a, con, nil71, snoc71 => snoc71 (g con nil71 snoc71) a

Var71 : Con71 -> Ty71 -> Type
Var71 = \ g, a =>
    (Var71 : Con71 -> Ty71 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var71 (snoc71 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var71 g a -> Var71 (snoc71 g b) a)
 -> Var71 g a

vz71 : {g : _}-> {a : _} -> Var71 (snoc71 g a) a
vz71 = \ var, vz71, vs => vz71 _ _

vs71 : {g : _} -> {B : _} -> {a : _} -> Var71 g a -> Var71 (snoc71 g B) a
vs71 = \ x, var, vz71, vs71 => vs71 _ _ _ (x var vz71 vs71)

Tm71 : Con71 -> Ty71 -> Type
Tm71 = \ g, a =>
    (Tm71    : Con71 -> Ty71 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var71 g a -> Tm71 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm71 (snoc71 g a) B -> Tm71 g (arr71 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm71 g (arr71 a B) -> Tm71 g a -> Tm71 g B)
 -> Tm71 g a

var71 : {g : _} -> {a : _} -> Var71 g a -> Tm71 g a
var71 = \ x, tm, var71, lam, app => var71 _ _ x

lam71 : {g : _} -> {a : _} -> {B : _} -> Tm71 (snoc71 g a) B -> Tm71 g (arr71 a B)
lam71 = \ t, tm, var71, lam71, app => lam71 _ _ _ (t tm var71 lam71 app)

app71 : {g:_}->{a:_}->{B:_} -> Tm71 g (arr71 a B) -> Tm71 g a -> Tm71 g B
app71 = \ t, u, tm, var71, lam71, app71 => app71 _ _ _ (t tm var71 lam71 app71) (u tm var71 lam71 app71)

v071 : {g:_}->{a:_} -> Tm71 (snoc71 g a) a
v071 = var71 vz71

v171 : {g:_}->{a:_}-> {B:_}-> Tm71 (snoc71 (snoc71 g a) B) a
v171 = var71 (vs71 vz71)

v271 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm71 (snoc71 (snoc71 (snoc71 g a) B) C) a
v271 = var71 (vs71 (vs71 vz71))

v371 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm71 (snoc71 (snoc71 (snoc71 (snoc71 g a) B) C) D) a
v371 = var71 (vs71 (vs71 (vs71 vz71)))

v471 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm71 (snoc71 (snoc71 (snoc71 (snoc71 (snoc71 g a) B) C) D) E) a
v471 = var71 (vs71 (vs71 (vs71 (vs71 vz71))))

test71 : {g:_}-> {a:_} -> Tm71 g (arr71 (arr71 a a) (arr71 a a))
test71  = lam71 (lam71 (app71 v171 (app71 v171 (app71 v171 (app71 v171 (app71 v171 (app71 v171 v071)))))))
Ty72 : Type
Ty72 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty72 : Ty72
empty72 = \ _, empty, _ => empty

arr72 : Ty72 -> Ty72 -> Ty72
arr72 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con72 : Type
Con72 = (Con72 : Type)
 ->(nil  : Con72)
 ->(snoc : Con72 -> Ty72 -> Con72)
 -> Con72

nil72 : Con72
nil72 = \ con, nil72, snoc => nil72

snoc72 : Con72 -> Ty72 -> Con72
snoc72 = \ g, a, con, nil72, snoc72 => snoc72 (g con nil72 snoc72) a

Var72 : Con72 -> Ty72 -> Type
Var72 = \ g, a =>
    (Var72 : Con72 -> Ty72 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var72 (snoc72 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var72 g a -> Var72 (snoc72 g b) a)
 -> Var72 g a

vz72 : {g : _}-> {a : _} -> Var72 (snoc72 g a) a
vz72 = \ var, vz72, vs => vz72 _ _

vs72 : {g : _} -> {B : _} -> {a : _} -> Var72 g a -> Var72 (snoc72 g B) a
vs72 = \ x, var, vz72, vs72 => vs72 _ _ _ (x var vz72 vs72)

Tm72 : Con72 -> Ty72 -> Type
Tm72 = \ g, a =>
    (Tm72    : Con72 -> Ty72 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var72 g a -> Tm72 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm72 (snoc72 g a) B -> Tm72 g (arr72 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm72 g (arr72 a B) -> Tm72 g a -> Tm72 g B)
 -> Tm72 g a

var72 : {g : _} -> {a : _} -> Var72 g a -> Tm72 g a
var72 = \ x, tm, var72, lam, app => var72 _ _ x

lam72 : {g : _} -> {a : _} -> {B : _} -> Tm72 (snoc72 g a) B -> Tm72 g (arr72 a B)
lam72 = \ t, tm, var72, lam72, app => lam72 _ _ _ (t tm var72 lam72 app)

app72 : {g:_}->{a:_}->{B:_} -> Tm72 g (arr72 a B) -> Tm72 g a -> Tm72 g B
app72 = \ t, u, tm, var72, lam72, app72 => app72 _ _ _ (t tm var72 lam72 app72) (u tm var72 lam72 app72)

v072 : {g:_}->{a:_} -> Tm72 (snoc72 g a) a
v072 = var72 vz72

v172 : {g:_}->{a:_}-> {B:_}-> Tm72 (snoc72 (snoc72 g a) B) a
v172 = var72 (vs72 vz72)

v272 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm72 (snoc72 (snoc72 (snoc72 g a) B) C) a
v272 = var72 (vs72 (vs72 vz72))

v372 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm72 (snoc72 (snoc72 (snoc72 (snoc72 g a) B) C) D) a
v372 = var72 (vs72 (vs72 (vs72 vz72)))

v472 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm72 (snoc72 (snoc72 (snoc72 (snoc72 (snoc72 g a) B) C) D) E) a
v472 = var72 (vs72 (vs72 (vs72 (vs72 vz72))))

test72 : {g:_}-> {a:_} -> Tm72 g (arr72 (arr72 a a) (arr72 a a))
test72  = lam72 (lam72 (app72 v172 (app72 v172 (app72 v172 (app72 v172 (app72 v172 (app72 v172 v072)))))))
Ty73 : Type
Ty73 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty73 : Ty73
empty73 = \ _, empty, _ => empty

arr73 : Ty73 -> Ty73 -> Ty73
arr73 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con73 : Type
Con73 = (Con73 : Type)
 ->(nil  : Con73)
 ->(snoc : Con73 -> Ty73 -> Con73)
 -> Con73

nil73 : Con73
nil73 = \ con, nil73, snoc => nil73

snoc73 : Con73 -> Ty73 -> Con73
snoc73 = \ g, a, con, nil73, snoc73 => snoc73 (g con nil73 snoc73) a

Var73 : Con73 -> Ty73 -> Type
Var73 = \ g, a =>
    (Var73 : Con73 -> Ty73 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var73 (snoc73 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var73 g a -> Var73 (snoc73 g b) a)
 -> Var73 g a

vz73 : {g : _}-> {a : _} -> Var73 (snoc73 g a) a
vz73 = \ var, vz73, vs => vz73 _ _

vs73 : {g : _} -> {B : _} -> {a : _} -> Var73 g a -> Var73 (snoc73 g B) a
vs73 = \ x, var, vz73, vs73 => vs73 _ _ _ (x var vz73 vs73)

Tm73 : Con73 -> Ty73 -> Type
Tm73 = \ g, a =>
    (Tm73    : Con73 -> Ty73 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var73 g a -> Tm73 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm73 (snoc73 g a) B -> Tm73 g (arr73 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm73 g (arr73 a B) -> Tm73 g a -> Tm73 g B)
 -> Tm73 g a

var73 : {g : _} -> {a : _} -> Var73 g a -> Tm73 g a
var73 = \ x, tm, var73, lam, app => var73 _ _ x

lam73 : {g : _} -> {a : _} -> {B : _} -> Tm73 (snoc73 g a) B -> Tm73 g (arr73 a B)
lam73 = \ t, tm, var73, lam73, app => lam73 _ _ _ (t tm var73 lam73 app)

app73 : {g:_}->{a:_}->{B:_} -> Tm73 g (arr73 a B) -> Tm73 g a -> Tm73 g B
app73 = \ t, u, tm, var73, lam73, app73 => app73 _ _ _ (t tm var73 lam73 app73) (u tm var73 lam73 app73)

v073 : {g:_}->{a:_} -> Tm73 (snoc73 g a) a
v073 = var73 vz73

v173 : {g:_}->{a:_}-> {B:_}-> Tm73 (snoc73 (snoc73 g a) B) a
v173 = var73 (vs73 vz73)

v273 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm73 (snoc73 (snoc73 (snoc73 g a) B) C) a
v273 = var73 (vs73 (vs73 vz73))

v373 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm73 (snoc73 (snoc73 (snoc73 (snoc73 g a) B) C) D) a
v373 = var73 (vs73 (vs73 (vs73 vz73)))

v473 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm73 (snoc73 (snoc73 (snoc73 (snoc73 (snoc73 g a) B) C) D) E) a
v473 = var73 (vs73 (vs73 (vs73 (vs73 vz73))))

test73 : {g:_}-> {a:_} -> Tm73 g (arr73 (arr73 a a) (arr73 a a))
test73  = lam73 (lam73 (app73 v173 (app73 v173 (app73 v173 (app73 v173 (app73 v173 (app73 v173 v073)))))))
Ty74 : Type
Ty74 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty74 : Ty74
empty74 = \ _, empty, _ => empty

arr74 : Ty74 -> Ty74 -> Ty74
arr74 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con74 : Type
Con74 = (Con74 : Type)
 ->(nil  : Con74)
 ->(snoc : Con74 -> Ty74 -> Con74)
 -> Con74

nil74 : Con74
nil74 = \ con, nil74, snoc => nil74

snoc74 : Con74 -> Ty74 -> Con74
snoc74 = \ g, a, con, nil74, snoc74 => snoc74 (g con nil74 snoc74) a

Var74 : Con74 -> Ty74 -> Type
Var74 = \ g, a =>
    (Var74 : Con74 -> Ty74 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var74 (snoc74 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var74 g a -> Var74 (snoc74 g b) a)
 -> Var74 g a

vz74 : {g : _}-> {a : _} -> Var74 (snoc74 g a) a
vz74 = \ var, vz74, vs => vz74 _ _

vs74 : {g : _} -> {B : _} -> {a : _} -> Var74 g a -> Var74 (snoc74 g B) a
vs74 = \ x, var, vz74, vs74 => vs74 _ _ _ (x var vz74 vs74)

Tm74 : Con74 -> Ty74 -> Type
Tm74 = \ g, a =>
    (Tm74    : Con74 -> Ty74 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var74 g a -> Tm74 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm74 (snoc74 g a) B -> Tm74 g (arr74 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm74 g (arr74 a B) -> Tm74 g a -> Tm74 g B)
 -> Tm74 g a

var74 : {g : _} -> {a : _} -> Var74 g a -> Tm74 g a
var74 = \ x, tm, var74, lam, app => var74 _ _ x

lam74 : {g : _} -> {a : _} -> {B : _} -> Tm74 (snoc74 g a) B -> Tm74 g (arr74 a B)
lam74 = \ t, tm, var74, lam74, app => lam74 _ _ _ (t tm var74 lam74 app)

app74 : {g:_}->{a:_}->{B:_} -> Tm74 g (arr74 a B) -> Tm74 g a -> Tm74 g B
app74 = \ t, u, tm, var74, lam74, app74 => app74 _ _ _ (t tm var74 lam74 app74) (u tm var74 lam74 app74)

v074 : {g:_}->{a:_} -> Tm74 (snoc74 g a) a
v074 = var74 vz74

v174 : {g:_}->{a:_}-> {B:_}-> Tm74 (snoc74 (snoc74 g a) B) a
v174 = var74 (vs74 vz74)

v274 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm74 (snoc74 (snoc74 (snoc74 g a) B) C) a
v274 = var74 (vs74 (vs74 vz74))

v374 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm74 (snoc74 (snoc74 (snoc74 (snoc74 g a) B) C) D) a
v374 = var74 (vs74 (vs74 (vs74 vz74)))

v474 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm74 (snoc74 (snoc74 (snoc74 (snoc74 (snoc74 g a) B) C) D) E) a
v474 = var74 (vs74 (vs74 (vs74 (vs74 vz74))))

test74 : {g:_}-> {a:_} -> Tm74 g (arr74 (arr74 a a) (arr74 a a))
test74  = lam74 (lam74 (app74 v174 (app74 v174 (app74 v174 (app74 v174 (app74 v174 (app74 v174 v074)))))))
Ty75 : Type
Ty75 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty75 : Ty75
empty75 = \ _, empty, _ => empty

arr75 : Ty75 -> Ty75 -> Ty75
arr75 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con75 : Type
Con75 = (Con75 : Type)
 ->(nil  : Con75)
 ->(snoc : Con75 -> Ty75 -> Con75)
 -> Con75

nil75 : Con75
nil75 = \ con, nil75, snoc => nil75

snoc75 : Con75 -> Ty75 -> Con75
snoc75 = \ g, a, con, nil75, snoc75 => snoc75 (g con nil75 snoc75) a

Var75 : Con75 -> Ty75 -> Type
Var75 = \ g, a =>
    (Var75 : Con75 -> Ty75 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var75 (snoc75 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var75 g a -> Var75 (snoc75 g b) a)
 -> Var75 g a

vz75 : {g : _}-> {a : _} -> Var75 (snoc75 g a) a
vz75 = \ var, vz75, vs => vz75 _ _

vs75 : {g : _} -> {B : _} -> {a : _} -> Var75 g a -> Var75 (snoc75 g B) a
vs75 = \ x, var, vz75, vs75 => vs75 _ _ _ (x var vz75 vs75)

Tm75 : Con75 -> Ty75 -> Type
Tm75 = \ g, a =>
    (Tm75    : Con75 -> Ty75 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var75 g a -> Tm75 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm75 (snoc75 g a) B -> Tm75 g (arr75 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm75 g (arr75 a B) -> Tm75 g a -> Tm75 g B)
 -> Tm75 g a

var75 : {g : _} -> {a : _} -> Var75 g a -> Tm75 g a
var75 = \ x, tm, var75, lam, app => var75 _ _ x

lam75 : {g : _} -> {a : _} -> {B : _} -> Tm75 (snoc75 g a) B -> Tm75 g (arr75 a B)
lam75 = \ t, tm, var75, lam75, app => lam75 _ _ _ (t tm var75 lam75 app)

app75 : {g:_}->{a:_}->{B:_} -> Tm75 g (arr75 a B) -> Tm75 g a -> Tm75 g B
app75 = \ t, u, tm, var75, lam75, app75 => app75 _ _ _ (t tm var75 lam75 app75) (u tm var75 lam75 app75)

v075 : {g:_}->{a:_} -> Tm75 (snoc75 g a) a
v075 = var75 vz75

v175 : {g:_}->{a:_}-> {B:_}-> Tm75 (snoc75 (snoc75 g a) B) a
v175 = var75 (vs75 vz75)

v275 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm75 (snoc75 (snoc75 (snoc75 g a) B) C) a
v275 = var75 (vs75 (vs75 vz75))

v375 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm75 (snoc75 (snoc75 (snoc75 (snoc75 g a) B) C) D) a
v375 = var75 (vs75 (vs75 (vs75 vz75)))

v475 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm75 (snoc75 (snoc75 (snoc75 (snoc75 (snoc75 g a) B) C) D) E) a
v475 = var75 (vs75 (vs75 (vs75 (vs75 vz75))))

test75 : {g:_}-> {a:_} -> Tm75 g (arr75 (arr75 a a) (arr75 a a))
test75  = lam75 (lam75 (app75 v175 (app75 v175 (app75 v175 (app75 v175 (app75 v175 (app75 v175 v075)))))))
Ty76 : Type
Ty76 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty76 : Ty76
empty76 = \ _, empty, _ => empty

arr76 : Ty76 -> Ty76 -> Ty76
arr76 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con76 : Type
Con76 = (Con76 : Type)
 ->(nil  : Con76)
 ->(snoc : Con76 -> Ty76 -> Con76)
 -> Con76

nil76 : Con76
nil76 = \ con, nil76, snoc => nil76

snoc76 : Con76 -> Ty76 -> Con76
snoc76 = \ g, a, con, nil76, snoc76 => snoc76 (g con nil76 snoc76) a

Var76 : Con76 -> Ty76 -> Type
Var76 = \ g, a =>
    (Var76 : Con76 -> Ty76 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var76 (snoc76 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var76 g a -> Var76 (snoc76 g b) a)
 -> Var76 g a

vz76 : {g : _}-> {a : _} -> Var76 (snoc76 g a) a
vz76 = \ var, vz76, vs => vz76 _ _

vs76 : {g : _} -> {B : _} -> {a : _} -> Var76 g a -> Var76 (snoc76 g B) a
vs76 = \ x, var, vz76, vs76 => vs76 _ _ _ (x var vz76 vs76)

Tm76 : Con76 -> Ty76 -> Type
Tm76 = \ g, a =>
    (Tm76    : Con76 -> Ty76 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var76 g a -> Tm76 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm76 (snoc76 g a) B -> Tm76 g (arr76 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm76 g (arr76 a B) -> Tm76 g a -> Tm76 g B)
 -> Tm76 g a

var76 : {g : _} -> {a : _} -> Var76 g a -> Tm76 g a
var76 = \ x, tm, var76, lam, app => var76 _ _ x

lam76 : {g : _} -> {a : _} -> {B : _} -> Tm76 (snoc76 g a) B -> Tm76 g (arr76 a B)
lam76 = \ t, tm, var76, lam76, app => lam76 _ _ _ (t tm var76 lam76 app)

app76 : {g:_}->{a:_}->{B:_} -> Tm76 g (arr76 a B) -> Tm76 g a -> Tm76 g B
app76 = \ t, u, tm, var76, lam76, app76 => app76 _ _ _ (t tm var76 lam76 app76) (u tm var76 lam76 app76)

v076 : {g:_}->{a:_} -> Tm76 (snoc76 g a) a
v076 = var76 vz76

v176 : {g:_}->{a:_}-> {B:_}-> Tm76 (snoc76 (snoc76 g a) B) a
v176 = var76 (vs76 vz76)

v276 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm76 (snoc76 (snoc76 (snoc76 g a) B) C) a
v276 = var76 (vs76 (vs76 vz76))

v376 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm76 (snoc76 (snoc76 (snoc76 (snoc76 g a) B) C) D) a
v376 = var76 (vs76 (vs76 (vs76 vz76)))

v476 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm76 (snoc76 (snoc76 (snoc76 (snoc76 (snoc76 g a) B) C) D) E) a
v476 = var76 (vs76 (vs76 (vs76 (vs76 vz76))))

test76 : {g:_}-> {a:_} -> Tm76 g (arr76 (arr76 a a) (arr76 a a))
test76  = lam76 (lam76 (app76 v176 (app76 v176 (app76 v176 (app76 v176 (app76 v176 (app76 v176 v076)))))))
Ty77 : Type
Ty77 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty77 : Ty77
empty77 = \ _, empty, _ => empty

arr77 : Ty77 -> Ty77 -> Ty77
arr77 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con77 : Type
Con77 = (Con77 : Type)
 ->(nil  : Con77)
 ->(snoc : Con77 -> Ty77 -> Con77)
 -> Con77

nil77 : Con77
nil77 = \ con, nil77, snoc => nil77

snoc77 : Con77 -> Ty77 -> Con77
snoc77 = \ g, a, con, nil77, snoc77 => snoc77 (g con nil77 snoc77) a

Var77 : Con77 -> Ty77 -> Type
Var77 = \ g, a =>
    (Var77 : Con77 -> Ty77 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var77 (snoc77 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var77 g a -> Var77 (snoc77 g b) a)
 -> Var77 g a

vz77 : {g : _}-> {a : _} -> Var77 (snoc77 g a) a
vz77 = \ var, vz77, vs => vz77 _ _

vs77 : {g : _} -> {B : _} -> {a : _} -> Var77 g a -> Var77 (snoc77 g B) a
vs77 = \ x, var, vz77, vs77 => vs77 _ _ _ (x var vz77 vs77)

Tm77 : Con77 -> Ty77 -> Type
Tm77 = \ g, a =>
    (Tm77    : Con77 -> Ty77 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var77 g a -> Tm77 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm77 (snoc77 g a) B -> Tm77 g (arr77 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm77 g (arr77 a B) -> Tm77 g a -> Tm77 g B)
 -> Tm77 g a

var77 : {g : _} -> {a : _} -> Var77 g a -> Tm77 g a
var77 = \ x, tm, var77, lam, app => var77 _ _ x

lam77 : {g : _} -> {a : _} -> {B : _} -> Tm77 (snoc77 g a) B -> Tm77 g (arr77 a B)
lam77 = \ t, tm, var77, lam77, app => lam77 _ _ _ (t tm var77 lam77 app)

app77 : {g:_}->{a:_}->{B:_} -> Tm77 g (arr77 a B) -> Tm77 g a -> Tm77 g B
app77 = \ t, u, tm, var77, lam77, app77 => app77 _ _ _ (t tm var77 lam77 app77) (u tm var77 lam77 app77)

v077 : {g:_}->{a:_} -> Tm77 (snoc77 g a) a
v077 = var77 vz77

v177 : {g:_}->{a:_}-> {B:_}-> Tm77 (snoc77 (snoc77 g a) B) a
v177 = var77 (vs77 vz77)

v277 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm77 (snoc77 (snoc77 (snoc77 g a) B) C) a
v277 = var77 (vs77 (vs77 vz77))

v377 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm77 (snoc77 (snoc77 (snoc77 (snoc77 g a) B) C) D) a
v377 = var77 (vs77 (vs77 (vs77 vz77)))

v477 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm77 (snoc77 (snoc77 (snoc77 (snoc77 (snoc77 g a) B) C) D) E) a
v477 = var77 (vs77 (vs77 (vs77 (vs77 vz77))))

test77 : {g:_}-> {a:_} -> Tm77 g (arr77 (arr77 a a) (arr77 a a))
test77  = lam77 (lam77 (app77 v177 (app77 v177 (app77 v177 (app77 v177 (app77 v177 (app77 v177 v077)))))))
Ty78 : Type
Ty78 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty78 : Ty78
empty78 = \ _, empty, _ => empty

arr78 : Ty78 -> Ty78 -> Ty78
arr78 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con78 : Type
Con78 = (Con78 : Type)
 ->(nil  : Con78)
 ->(snoc : Con78 -> Ty78 -> Con78)
 -> Con78

nil78 : Con78
nil78 = \ con, nil78, snoc => nil78

snoc78 : Con78 -> Ty78 -> Con78
snoc78 = \ g, a, con, nil78, snoc78 => snoc78 (g con nil78 snoc78) a

Var78 : Con78 -> Ty78 -> Type
Var78 = \ g, a =>
    (Var78 : Con78 -> Ty78 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var78 (snoc78 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var78 g a -> Var78 (snoc78 g b) a)
 -> Var78 g a

vz78 : {g : _}-> {a : _} -> Var78 (snoc78 g a) a
vz78 = \ var, vz78, vs => vz78 _ _

vs78 : {g : _} -> {B : _} -> {a : _} -> Var78 g a -> Var78 (snoc78 g B) a
vs78 = \ x, var, vz78, vs78 => vs78 _ _ _ (x var vz78 vs78)

Tm78 : Con78 -> Ty78 -> Type
Tm78 = \ g, a =>
    (Tm78    : Con78 -> Ty78 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var78 g a -> Tm78 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm78 (snoc78 g a) B -> Tm78 g (arr78 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm78 g (arr78 a B) -> Tm78 g a -> Tm78 g B)
 -> Tm78 g a

var78 : {g : _} -> {a : _} -> Var78 g a -> Tm78 g a
var78 = \ x, tm, var78, lam, app => var78 _ _ x

lam78 : {g : _} -> {a : _} -> {B : _} -> Tm78 (snoc78 g a) B -> Tm78 g (arr78 a B)
lam78 = \ t, tm, var78, lam78, app => lam78 _ _ _ (t tm var78 lam78 app)

app78 : {g:_}->{a:_}->{B:_} -> Tm78 g (arr78 a B) -> Tm78 g a -> Tm78 g B
app78 = \ t, u, tm, var78, lam78, app78 => app78 _ _ _ (t tm var78 lam78 app78) (u tm var78 lam78 app78)

v078 : {g:_}->{a:_} -> Tm78 (snoc78 g a) a
v078 = var78 vz78

v178 : {g:_}->{a:_}-> {B:_}-> Tm78 (snoc78 (snoc78 g a) B) a
v178 = var78 (vs78 vz78)

v278 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm78 (snoc78 (snoc78 (snoc78 g a) B) C) a
v278 = var78 (vs78 (vs78 vz78))

v378 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm78 (snoc78 (snoc78 (snoc78 (snoc78 g a) B) C) D) a
v378 = var78 (vs78 (vs78 (vs78 vz78)))

v478 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm78 (snoc78 (snoc78 (snoc78 (snoc78 (snoc78 g a) B) C) D) E) a
v478 = var78 (vs78 (vs78 (vs78 (vs78 vz78))))

test78 : {g:_}-> {a:_} -> Tm78 g (arr78 (arr78 a a) (arr78 a a))
test78  = lam78 (lam78 (app78 v178 (app78 v178 (app78 v178 (app78 v178 (app78 v178 (app78 v178 v078)))))))
Ty79 : Type
Ty79 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty79 : Ty79
empty79 = \ _, empty, _ => empty

arr79 : Ty79 -> Ty79 -> Ty79
arr79 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con79 : Type
Con79 = (Con79 : Type)
 ->(nil  : Con79)
 ->(snoc : Con79 -> Ty79 -> Con79)
 -> Con79

nil79 : Con79
nil79 = \ con, nil79, snoc => nil79

snoc79 : Con79 -> Ty79 -> Con79
snoc79 = \ g, a, con, nil79, snoc79 => snoc79 (g con nil79 snoc79) a

Var79 : Con79 -> Ty79 -> Type
Var79 = \ g, a =>
    (Var79 : Con79 -> Ty79 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var79 (snoc79 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var79 g a -> Var79 (snoc79 g b) a)
 -> Var79 g a

vz79 : {g : _}-> {a : _} -> Var79 (snoc79 g a) a
vz79 = \ var, vz79, vs => vz79 _ _

vs79 : {g : _} -> {B : _} -> {a : _} -> Var79 g a -> Var79 (snoc79 g B) a
vs79 = \ x, var, vz79, vs79 => vs79 _ _ _ (x var vz79 vs79)

Tm79 : Con79 -> Ty79 -> Type
Tm79 = \ g, a =>
    (Tm79    : Con79 -> Ty79 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var79 g a -> Tm79 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm79 (snoc79 g a) B -> Tm79 g (arr79 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm79 g (arr79 a B) -> Tm79 g a -> Tm79 g B)
 -> Tm79 g a

var79 : {g : _} -> {a : _} -> Var79 g a -> Tm79 g a
var79 = \ x, tm, var79, lam, app => var79 _ _ x

lam79 : {g : _} -> {a : _} -> {B : _} -> Tm79 (snoc79 g a) B -> Tm79 g (arr79 a B)
lam79 = \ t, tm, var79, lam79, app => lam79 _ _ _ (t tm var79 lam79 app)

app79 : {g:_}->{a:_}->{B:_} -> Tm79 g (arr79 a B) -> Tm79 g a -> Tm79 g B
app79 = \ t, u, tm, var79, lam79, app79 => app79 _ _ _ (t tm var79 lam79 app79) (u tm var79 lam79 app79)

v079 : {g:_}->{a:_} -> Tm79 (snoc79 g a) a
v079 = var79 vz79

v179 : {g:_}->{a:_}-> {B:_}-> Tm79 (snoc79 (snoc79 g a) B) a
v179 = var79 (vs79 vz79)

v279 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm79 (snoc79 (snoc79 (snoc79 g a) B) C) a
v279 = var79 (vs79 (vs79 vz79))

v379 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm79 (snoc79 (snoc79 (snoc79 (snoc79 g a) B) C) D) a
v379 = var79 (vs79 (vs79 (vs79 vz79)))

v479 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm79 (snoc79 (snoc79 (snoc79 (snoc79 (snoc79 g a) B) C) D) E) a
v479 = var79 (vs79 (vs79 (vs79 (vs79 vz79))))

test79 : {g:_}-> {a:_} -> Tm79 g (arr79 (arr79 a a) (arr79 a a))
test79  = lam79 (lam79 (app79 v179 (app79 v179 (app79 v179 (app79 v179 (app79 v179 (app79 v179 v079)))))))
Ty80 : Type
Ty80 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty80 : Ty80
empty80 = \ _, empty, _ => empty

arr80 : Ty80 -> Ty80 -> Ty80
arr80 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con80 : Type
Con80 = (Con80 : Type)
 ->(nil  : Con80)
 ->(snoc : Con80 -> Ty80 -> Con80)
 -> Con80

nil80 : Con80
nil80 = \ con, nil80, snoc => nil80

snoc80 : Con80 -> Ty80 -> Con80
snoc80 = \ g, a, con, nil80, snoc80 => snoc80 (g con nil80 snoc80) a

Var80 : Con80 -> Ty80 -> Type
Var80 = \ g, a =>
    (Var80 : Con80 -> Ty80 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var80 (snoc80 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var80 g a -> Var80 (snoc80 g b) a)
 -> Var80 g a

vz80 : {g : _}-> {a : _} -> Var80 (snoc80 g a) a
vz80 = \ var, vz80, vs => vz80 _ _

vs80 : {g : _} -> {B : _} -> {a : _} -> Var80 g a -> Var80 (snoc80 g B) a
vs80 = \ x, var, vz80, vs80 => vs80 _ _ _ (x var vz80 vs80)

Tm80 : Con80 -> Ty80 -> Type
Tm80 = \ g, a =>
    (Tm80    : Con80 -> Ty80 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var80 g a -> Tm80 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm80 (snoc80 g a) B -> Tm80 g (arr80 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm80 g (arr80 a B) -> Tm80 g a -> Tm80 g B)
 -> Tm80 g a

var80 : {g : _} -> {a : _} -> Var80 g a -> Tm80 g a
var80 = \ x, tm, var80, lam, app => var80 _ _ x

lam80 : {g : _} -> {a : _} -> {B : _} -> Tm80 (snoc80 g a) B -> Tm80 g (arr80 a B)
lam80 = \ t, tm, var80, lam80, app => lam80 _ _ _ (t tm var80 lam80 app)

app80 : {g:_}->{a:_}->{B:_} -> Tm80 g (arr80 a B) -> Tm80 g a -> Tm80 g B
app80 = \ t, u, tm, var80, lam80, app80 => app80 _ _ _ (t tm var80 lam80 app80) (u tm var80 lam80 app80)

v080 : {g:_}->{a:_} -> Tm80 (snoc80 g a) a
v080 = var80 vz80

v180 : {g:_}->{a:_}-> {B:_}-> Tm80 (snoc80 (snoc80 g a) B) a
v180 = var80 (vs80 vz80)

v280 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm80 (snoc80 (snoc80 (snoc80 g a) B) C) a
v280 = var80 (vs80 (vs80 vz80))

v380 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm80 (snoc80 (snoc80 (snoc80 (snoc80 g a) B) C) D) a
v380 = var80 (vs80 (vs80 (vs80 vz80)))

v480 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm80 (snoc80 (snoc80 (snoc80 (snoc80 (snoc80 g a) B) C) D) E) a
v480 = var80 (vs80 (vs80 (vs80 (vs80 vz80))))

test80 : {g:_}-> {a:_} -> Tm80 g (arr80 (arr80 a a) (arr80 a a))
test80  = lam80 (lam80 (app80 v180 (app80 v180 (app80 v180 (app80 v180 (app80 v180 (app80 v180 v080)))))))
Ty81 : Type
Ty81 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty81 : Ty81
empty81 = \ _, empty, _ => empty

arr81 : Ty81 -> Ty81 -> Ty81
arr81 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con81 : Type
Con81 = (Con81 : Type)
 ->(nil  : Con81)
 ->(snoc : Con81 -> Ty81 -> Con81)
 -> Con81

nil81 : Con81
nil81 = \ con, nil81, snoc => nil81

snoc81 : Con81 -> Ty81 -> Con81
snoc81 = \ g, a, con, nil81, snoc81 => snoc81 (g con nil81 snoc81) a

Var81 : Con81 -> Ty81 -> Type
Var81 = \ g, a =>
    (Var81 : Con81 -> Ty81 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var81 (snoc81 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var81 g a -> Var81 (snoc81 g b) a)
 -> Var81 g a

vz81 : {g : _}-> {a : _} -> Var81 (snoc81 g a) a
vz81 = \ var, vz81, vs => vz81 _ _

vs81 : {g : _} -> {B : _} -> {a : _} -> Var81 g a -> Var81 (snoc81 g B) a
vs81 = \ x, var, vz81, vs81 => vs81 _ _ _ (x var vz81 vs81)

Tm81 : Con81 -> Ty81 -> Type
Tm81 = \ g, a =>
    (Tm81    : Con81 -> Ty81 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var81 g a -> Tm81 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm81 (snoc81 g a) B -> Tm81 g (arr81 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm81 g (arr81 a B) -> Tm81 g a -> Tm81 g B)
 -> Tm81 g a

var81 : {g : _} -> {a : _} -> Var81 g a -> Tm81 g a
var81 = \ x, tm, var81, lam, app => var81 _ _ x

lam81 : {g : _} -> {a : _} -> {B : _} -> Tm81 (snoc81 g a) B -> Tm81 g (arr81 a B)
lam81 = \ t, tm, var81, lam81, app => lam81 _ _ _ (t tm var81 lam81 app)

app81 : {g:_}->{a:_}->{B:_} -> Tm81 g (arr81 a B) -> Tm81 g a -> Tm81 g B
app81 = \ t, u, tm, var81, lam81, app81 => app81 _ _ _ (t tm var81 lam81 app81) (u tm var81 lam81 app81)

v081 : {g:_}->{a:_} -> Tm81 (snoc81 g a) a
v081 = var81 vz81

v181 : {g:_}->{a:_}-> {B:_}-> Tm81 (snoc81 (snoc81 g a) B) a
v181 = var81 (vs81 vz81)

v281 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm81 (snoc81 (snoc81 (snoc81 g a) B) C) a
v281 = var81 (vs81 (vs81 vz81))

v381 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm81 (snoc81 (snoc81 (snoc81 (snoc81 g a) B) C) D) a
v381 = var81 (vs81 (vs81 (vs81 vz81)))

v481 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm81 (snoc81 (snoc81 (snoc81 (snoc81 (snoc81 g a) B) C) D) E) a
v481 = var81 (vs81 (vs81 (vs81 (vs81 vz81))))

test81 : {g:_}-> {a:_} -> Tm81 g (arr81 (arr81 a a) (arr81 a a))
test81  = lam81 (lam81 (app81 v181 (app81 v181 (app81 v181 (app81 v181 (app81 v181 (app81 v181 v081)))))))
Ty82 : Type
Ty82 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty82 : Ty82
empty82 = \ _, empty, _ => empty

arr82 : Ty82 -> Ty82 -> Ty82
arr82 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con82 : Type
Con82 = (Con82 : Type)
 ->(nil  : Con82)
 ->(snoc : Con82 -> Ty82 -> Con82)
 -> Con82

nil82 : Con82
nil82 = \ con, nil82, snoc => nil82

snoc82 : Con82 -> Ty82 -> Con82
snoc82 = \ g, a, con, nil82, snoc82 => snoc82 (g con nil82 snoc82) a

Var82 : Con82 -> Ty82 -> Type
Var82 = \ g, a =>
    (Var82 : Con82 -> Ty82 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var82 (snoc82 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var82 g a -> Var82 (snoc82 g b) a)
 -> Var82 g a

vz82 : {g : _}-> {a : _} -> Var82 (snoc82 g a) a
vz82 = \ var, vz82, vs => vz82 _ _

vs82 : {g : _} -> {B : _} -> {a : _} -> Var82 g a -> Var82 (snoc82 g B) a
vs82 = \ x, var, vz82, vs82 => vs82 _ _ _ (x var vz82 vs82)

Tm82 : Con82 -> Ty82 -> Type
Tm82 = \ g, a =>
    (Tm82    : Con82 -> Ty82 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var82 g a -> Tm82 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm82 (snoc82 g a) B -> Tm82 g (arr82 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm82 g (arr82 a B) -> Tm82 g a -> Tm82 g B)
 -> Tm82 g a

var82 : {g : _} -> {a : _} -> Var82 g a -> Tm82 g a
var82 = \ x, tm, var82, lam, app => var82 _ _ x

lam82 : {g : _} -> {a : _} -> {B : _} -> Tm82 (snoc82 g a) B -> Tm82 g (arr82 a B)
lam82 = \ t, tm, var82, lam82, app => lam82 _ _ _ (t tm var82 lam82 app)

app82 : {g:_}->{a:_}->{B:_} -> Tm82 g (arr82 a B) -> Tm82 g a -> Tm82 g B
app82 = \ t, u, tm, var82, lam82, app82 => app82 _ _ _ (t tm var82 lam82 app82) (u tm var82 lam82 app82)

v082 : {g:_}->{a:_} -> Tm82 (snoc82 g a) a
v082 = var82 vz82

v182 : {g:_}->{a:_}-> {B:_}-> Tm82 (snoc82 (snoc82 g a) B) a
v182 = var82 (vs82 vz82)

v282 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm82 (snoc82 (snoc82 (snoc82 g a) B) C) a
v282 = var82 (vs82 (vs82 vz82))

v382 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm82 (snoc82 (snoc82 (snoc82 (snoc82 g a) B) C) D) a
v382 = var82 (vs82 (vs82 (vs82 vz82)))

v482 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm82 (snoc82 (snoc82 (snoc82 (snoc82 (snoc82 g a) B) C) D) E) a
v482 = var82 (vs82 (vs82 (vs82 (vs82 vz82))))

test82 : {g:_}-> {a:_} -> Tm82 g (arr82 (arr82 a a) (arr82 a a))
test82  = lam82 (lam82 (app82 v182 (app82 v182 (app82 v182 (app82 v182 (app82 v182 (app82 v182 v082)))))))
Ty83 : Type
Ty83 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty83 : Ty83
empty83 = \ _, empty, _ => empty

arr83 : Ty83 -> Ty83 -> Ty83
arr83 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con83 : Type
Con83 = (Con83 : Type)
 ->(nil  : Con83)
 ->(snoc : Con83 -> Ty83 -> Con83)
 -> Con83

nil83 : Con83
nil83 = \ con, nil83, snoc => nil83

snoc83 : Con83 -> Ty83 -> Con83
snoc83 = \ g, a, con, nil83, snoc83 => snoc83 (g con nil83 snoc83) a

Var83 : Con83 -> Ty83 -> Type
Var83 = \ g, a =>
    (Var83 : Con83 -> Ty83 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var83 (snoc83 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var83 g a -> Var83 (snoc83 g b) a)
 -> Var83 g a

vz83 : {g : _}-> {a : _} -> Var83 (snoc83 g a) a
vz83 = \ var, vz83, vs => vz83 _ _

vs83 : {g : _} -> {B : _} -> {a : _} -> Var83 g a -> Var83 (snoc83 g B) a
vs83 = \ x, var, vz83, vs83 => vs83 _ _ _ (x var vz83 vs83)

Tm83 : Con83 -> Ty83 -> Type
Tm83 = \ g, a =>
    (Tm83    : Con83 -> Ty83 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var83 g a -> Tm83 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm83 (snoc83 g a) B -> Tm83 g (arr83 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm83 g (arr83 a B) -> Tm83 g a -> Tm83 g B)
 -> Tm83 g a

var83 : {g : _} -> {a : _} -> Var83 g a -> Tm83 g a
var83 = \ x, tm, var83, lam, app => var83 _ _ x

lam83 : {g : _} -> {a : _} -> {B : _} -> Tm83 (snoc83 g a) B -> Tm83 g (arr83 a B)
lam83 = \ t, tm, var83, lam83, app => lam83 _ _ _ (t tm var83 lam83 app)

app83 : {g:_}->{a:_}->{B:_} -> Tm83 g (arr83 a B) -> Tm83 g a -> Tm83 g B
app83 = \ t, u, tm, var83, lam83, app83 => app83 _ _ _ (t tm var83 lam83 app83) (u tm var83 lam83 app83)

v083 : {g:_}->{a:_} -> Tm83 (snoc83 g a) a
v083 = var83 vz83

v183 : {g:_}->{a:_}-> {B:_}-> Tm83 (snoc83 (snoc83 g a) B) a
v183 = var83 (vs83 vz83)

v283 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm83 (snoc83 (snoc83 (snoc83 g a) B) C) a
v283 = var83 (vs83 (vs83 vz83))

v383 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm83 (snoc83 (snoc83 (snoc83 (snoc83 g a) B) C) D) a
v383 = var83 (vs83 (vs83 (vs83 vz83)))

v483 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm83 (snoc83 (snoc83 (snoc83 (snoc83 (snoc83 g a) B) C) D) E) a
v483 = var83 (vs83 (vs83 (vs83 (vs83 vz83))))

test83 : {g:_}-> {a:_} -> Tm83 g (arr83 (arr83 a a) (arr83 a a))
test83  = lam83 (lam83 (app83 v183 (app83 v183 (app83 v183 (app83 v183 (app83 v183 (app83 v183 v083)))))))
Ty84 : Type
Ty84 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty84 : Ty84
empty84 = \ _, empty, _ => empty

arr84 : Ty84 -> Ty84 -> Ty84
arr84 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con84 : Type
Con84 = (Con84 : Type)
 ->(nil  : Con84)
 ->(snoc : Con84 -> Ty84 -> Con84)
 -> Con84

nil84 : Con84
nil84 = \ con, nil84, snoc => nil84

snoc84 : Con84 -> Ty84 -> Con84
snoc84 = \ g, a, con, nil84, snoc84 => snoc84 (g con nil84 snoc84) a

Var84 : Con84 -> Ty84 -> Type
Var84 = \ g, a =>
    (Var84 : Con84 -> Ty84 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var84 (snoc84 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var84 g a -> Var84 (snoc84 g b) a)
 -> Var84 g a

vz84 : {g : _}-> {a : _} -> Var84 (snoc84 g a) a
vz84 = \ var, vz84, vs => vz84 _ _

vs84 : {g : _} -> {B : _} -> {a : _} -> Var84 g a -> Var84 (snoc84 g B) a
vs84 = \ x, var, vz84, vs84 => vs84 _ _ _ (x var vz84 vs84)

Tm84 : Con84 -> Ty84 -> Type
Tm84 = \ g, a =>
    (Tm84    : Con84 -> Ty84 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var84 g a -> Tm84 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm84 (snoc84 g a) B -> Tm84 g (arr84 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm84 g (arr84 a B) -> Tm84 g a -> Tm84 g B)
 -> Tm84 g a

var84 : {g : _} -> {a : _} -> Var84 g a -> Tm84 g a
var84 = \ x, tm, var84, lam, app => var84 _ _ x

lam84 : {g : _} -> {a : _} -> {B : _} -> Tm84 (snoc84 g a) B -> Tm84 g (arr84 a B)
lam84 = \ t, tm, var84, lam84, app => lam84 _ _ _ (t tm var84 lam84 app)

app84 : {g:_}->{a:_}->{B:_} -> Tm84 g (arr84 a B) -> Tm84 g a -> Tm84 g B
app84 = \ t, u, tm, var84, lam84, app84 => app84 _ _ _ (t tm var84 lam84 app84) (u tm var84 lam84 app84)

v084 : {g:_}->{a:_} -> Tm84 (snoc84 g a) a
v084 = var84 vz84

v184 : {g:_}->{a:_}-> {B:_}-> Tm84 (snoc84 (snoc84 g a) B) a
v184 = var84 (vs84 vz84)

v284 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm84 (snoc84 (snoc84 (snoc84 g a) B) C) a
v284 = var84 (vs84 (vs84 vz84))

v384 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm84 (snoc84 (snoc84 (snoc84 (snoc84 g a) B) C) D) a
v384 = var84 (vs84 (vs84 (vs84 vz84)))

v484 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm84 (snoc84 (snoc84 (snoc84 (snoc84 (snoc84 g a) B) C) D) E) a
v484 = var84 (vs84 (vs84 (vs84 (vs84 vz84))))

test84 : {g:_}-> {a:_} -> Tm84 g (arr84 (arr84 a a) (arr84 a a))
test84  = lam84 (lam84 (app84 v184 (app84 v184 (app84 v184 (app84 v184 (app84 v184 (app84 v184 v084)))))))
Ty85 : Type
Ty85 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty85 : Ty85
empty85 = \ _, empty, _ => empty

arr85 : Ty85 -> Ty85 -> Ty85
arr85 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con85 : Type
Con85 = (Con85 : Type)
 ->(nil  : Con85)
 ->(snoc : Con85 -> Ty85 -> Con85)
 -> Con85

nil85 : Con85
nil85 = \ con, nil85, snoc => nil85

snoc85 : Con85 -> Ty85 -> Con85
snoc85 = \ g, a, con, nil85, snoc85 => snoc85 (g con nil85 snoc85) a

Var85 : Con85 -> Ty85 -> Type
Var85 = \ g, a =>
    (Var85 : Con85 -> Ty85 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var85 (snoc85 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var85 g a -> Var85 (snoc85 g b) a)
 -> Var85 g a

vz85 : {g : _}-> {a : _} -> Var85 (snoc85 g a) a
vz85 = \ var, vz85, vs => vz85 _ _

vs85 : {g : _} -> {B : _} -> {a : _} -> Var85 g a -> Var85 (snoc85 g B) a
vs85 = \ x, var, vz85, vs85 => vs85 _ _ _ (x var vz85 vs85)

Tm85 : Con85 -> Ty85 -> Type
Tm85 = \ g, a =>
    (Tm85    : Con85 -> Ty85 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var85 g a -> Tm85 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm85 (snoc85 g a) B -> Tm85 g (arr85 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm85 g (arr85 a B) -> Tm85 g a -> Tm85 g B)
 -> Tm85 g a

var85 : {g : _} -> {a : _} -> Var85 g a -> Tm85 g a
var85 = \ x, tm, var85, lam, app => var85 _ _ x

lam85 : {g : _} -> {a : _} -> {B : _} -> Tm85 (snoc85 g a) B -> Tm85 g (arr85 a B)
lam85 = \ t, tm, var85, lam85, app => lam85 _ _ _ (t tm var85 lam85 app)

app85 : {g:_}->{a:_}->{B:_} -> Tm85 g (arr85 a B) -> Tm85 g a -> Tm85 g B
app85 = \ t, u, tm, var85, lam85, app85 => app85 _ _ _ (t tm var85 lam85 app85) (u tm var85 lam85 app85)

v085 : {g:_}->{a:_} -> Tm85 (snoc85 g a) a
v085 = var85 vz85

v185 : {g:_}->{a:_}-> {B:_}-> Tm85 (snoc85 (snoc85 g a) B) a
v185 = var85 (vs85 vz85)

v285 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm85 (snoc85 (snoc85 (snoc85 g a) B) C) a
v285 = var85 (vs85 (vs85 vz85))

v385 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm85 (snoc85 (snoc85 (snoc85 (snoc85 g a) B) C) D) a
v385 = var85 (vs85 (vs85 (vs85 vz85)))

v485 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm85 (snoc85 (snoc85 (snoc85 (snoc85 (snoc85 g a) B) C) D) E) a
v485 = var85 (vs85 (vs85 (vs85 (vs85 vz85))))

test85 : {g:_}-> {a:_} -> Tm85 g (arr85 (arr85 a a) (arr85 a a))
test85  = lam85 (lam85 (app85 v185 (app85 v185 (app85 v185 (app85 v185 (app85 v185 (app85 v185 v085)))))))
Ty86 : Type
Ty86 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty86 : Ty86
empty86 = \ _, empty, _ => empty

arr86 : Ty86 -> Ty86 -> Ty86
arr86 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con86 : Type
Con86 = (Con86 : Type)
 ->(nil  : Con86)
 ->(snoc : Con86 -> Ty86 -> Con86)
 -> Con86

nil86 : Con86
nil86 = \ con, nil86, snoc => nil86

snoc86 : Con86 -> Ty86 -> Con86
snoc86 = \ g, a, con, nil86, snoc86 => snoc86 (g con nil86 snoc86) a

Var86 : Con86 -> Ty86 -> Type
Var86 = \ g, a =>
    (Var86 : Con86 -> Ty86 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var86 (snoc86 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var86 g a -> Var86 (snoc86 g b) a)
 -> Var86 g a

vz86 : {g : _}-> {a : _} -> Var86 (snoc86 g a) a
vz86 = \ var, vz86, vs => vz86 _ _

vs86 : {g : _} -> {B : _} -> {a : _} -> Var86 g a -> Var86 (snoc86 g B) a
vs86 = \ x, var, vz86, vs86 => vs86 _ _ _ (x var vz86 vs86)

Tm86 : Con86 -> Ty86 -> Type
Tm86 = \ g, a =>
    (Tm86    : Con86 -> Ty86 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var86 g a -> Tm86 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm86 (snoc86 g a) B -> Tm86 g (arr86 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm86 g (arr86 a B) -> Tm86 g a -> Tm86 g B)
 -> Tm86 g a

var86 : {g : _} -> {a : _} -> Var86 g a -> Tm86 g a
var86 = \ x, tm, var86, lam, app => var86 _ _ x

lam86 : {g : _} -> {a : _} -> {B : _} -> Tm86 (snoc86 g a) B -> Tm86 g (arr86 a B)
lam86 = \ t, tm, var86, lam86, app => lam86 _ _ _ (t tm var86 lam86 app)

app86 : {g:_}->{a:_}->{B:_} -> Tm86 g (arr86 a B) -> Tm86 g a -> Tm86 g B
app86 = \ t, u, tm, var86, lam86, app86 => app86 _ _ _ (t tm var86 lam86 app86) (u tm var86 lam86 app86)

v086 : {g:_}->{a:_} -> Tm86 (snoc86 g a) a
v086 = var86 vz86

v186 : {g:_}->{a:_}-> {B:_}-> Tm86 (snoc86 (snoc86 g a) B) a
v186 = var86 (vs86 vz86)

v286 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm86 (snoc86 (snoc86 (snoc86 g a) B) C) a
v286 = var86 (vs86 (vs86 vz86))

v386 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm86 (snoc86 (snoc86 (snoc86 (snoc86 g a) B) C) D) a
v386 = var86 (vs86 (vs86 (vs86 vz86)))

v486 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm86 (snoc86 (snoc86 (snoc86 (snoc86 (snoc86 g a) B) C) D) E) a
v486 = var86 (vs86 (vs86 (vs86 (vs86 vz86))))

test86 : {g:_}-> {a:_} -> Tm86 g (arr86 (arr86 a a) (arr86 a a))
test86  = lam86 (lam86 (app86 v186 (app86 v186 (app86 v186 (app86 v186 (app86 v186 (app86 v186 v086)))))))
Ty87 : Type
Ty87 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty87 : Ty87
empty87 = \ _, empty, _ => empty

arr87 : Ty87 -> Ty87 -> Ty87
arr87 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con87 : Type
Con87 = (Con87 : Type)
 ->(nil  : Con87)
 ->(snoc : Con87 -> Ty87 -> Con87)
 -> Con87

nil87 : Con87
nil87 = \ con, nil87, snoc => nil87

snoc87 : Con87 -> Ty87 -> Con87
snoc87 = \ g, a, con, nil87, snoc87 => snoc87 (g con nil87 snoc87) a

Var87 : Con87 -> Ty87 -> Type
Var87 = \ g, a =>
    (Var87 : Con87 -> Ty87 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var87 (snoc87 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var87 g a -> Var87 (snoc87 g b) a)
 -> Var87 g a

vz87 : {g : _}-> {a : _} -> Var87 (snoc87 g a) a
vz87 = \ var, vz87, vs => vz87 _ _

vs87 : {g : _} -> {B : _} -> {a : _} -> Var87 g a -> Var87 (snoc87 g B) a
vs87 = \ x, var, vz87, vs87 => vs87 _ _ _ (x var vz87 vs87)

Tm87 : Con87 -> Ty87 -> Type
Tm87 = \ g, a =>
    (Tm87    : Con87 -> Ty87 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var87 g a -> Tm87 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm87 (snoc87 g a) B -> Tm87 g (arr87 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm87 g (arr87 a B) -> Tm87 g a -> Tm87 g B)
 -> Tm87 g a

var87 : {g : _} -> {a : _} -> Var87 g a -> Tm87 g a
var87 = \ x, tm, var87, lam, app => var87 _ _ x

lam87 : {g : _} -> {a : _} -> {B : _} -> Tm87 (snoc87 g a) B -> Tm87 g (arr87 a B)
lam87 = \ t, tm, var87, lam87, app => lam87 _ _ _ (t tm var87 lam87 app)

app87 : {g:_}->{a:_}->{B:_} -> Tm87 g (arr87 a B) -> Tm87 g a -> Tm87 g B
app87 = \ t, u, tm, var87, lam87, app87 => app87 _ _ _ (t tm var87 lam87 app87) (u tm var87 lam87 app87)

v087 : {g:_}->{a:_} -> Tm87 (snoc87 g a) a
v087 = var87 vz87

v187 : {g:_}->{a:_}-> {B:_}-> Tm87 (snoc87 (snoc87 g a) B) a
v187 = var87 (vs87 vz87)

v287 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm87 (snoc87 (snoc87 (snoc87 g a) B) C) a
v287 = var87 (vs87 (vs87 vz87))

v387 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm87 (snoc87 (snoc87 (snoc87 (snoc87 g a) B) C) D) a
v387 = var87 (vs87 (vs87 (vs87 vz87)))

v487 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm87 (snoc87 (snoc87 (snoc87 (snoc87 (snoc87 g a) B) C) D) E) a
v487 = var87 (vs87 (vs87 (vs87 (vs87 vz87))))

test87 : {g:_}-> {a:_} -> Tm87 g (arr87 (arr87 a a) (arr87 a a))
test87  = lam87 (lam87 (app87 v187 (app87 v187 (app87 v187 (app87 v187 (app87 v187 (app87 v187 v087)))))))
Ty88 : Type
Ty88 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty88 : Ty88
empty88 = \ _, empty, _ => empty

arr88 : Ty88 -> Ty88 -> Ty88
arr88 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con88 : Type
Con88 = (Con88 : Type)
 ->(nil  : Con88)
 ->(snoc : Con88 -> Ty88 -> Con88)
 -> Con88

nil88 : Con88
nil88 = \ con, nil88, snoc => nil88

snoc88 : Con88 -> Ty88 -> Con88
snoc88 = \ g, a, con, nil88, snoc88 => snoc88 (g con nil88 snoc88) a

Var88 : Con88 -> Ty88 -> Type
Var88 = \ g, a =>
    (Var88 : Con88 -> Ty88 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var88 (snoc88 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var88 g a -> Var88 (snoc88 g b) a)
 -> Var88 g a

vz88 : {g : _}-> {a : _} -> Var88 (snoc88 g a) a
vz88 = \ var, vz88, vs => vz88 _ _

vs88 : {g : _} -> {B : _} -> {a : _} -> Var88 g a -> Var88 (snoc88 g B) a
vs88 = \ x, var, vz88, vs88 => vs88 _ _ _ (x var vz88 vs88)

Tm88 : Con88 -> Ty88 -> Type
Tm88 = \ g, a =>
    (Tm88    : Con88 -> Ty88 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var88 g a -> Tm88 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm88 (snoc88 g a) B -> Tm88 g (arr88 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm88 g (arr88 a B) -> Tm88 g a -> Tm88 g B)
 -> Tm88 g a

var88 : {g : _} -> {a : _} -> Var88 g a -> Tm88 g a
var88 = \ x, tm, var88, lam, app => var88 _ _ x

lam88 : {g : _} -> {a : _} -> {B : _} -> Tm88 (snoc88 g a) B -> Tm88 g (arr88 a B)
lam88 = \ t, tm, var88, lam88, app => lam88 _ _ _ (t tm var88 lam88 app)

app88 : {g:_}->{a:_}->{B:_} -> Tm88 g (arr88 a B) -> Tm88 g a -> Tm88 g B
app88 = \ t, u, tm, var88, lam88, app88 => app88 _ _ _ (t tm var88 lam88 app88) (u tm var88 lam88 app88)

v088 : {g:_}->{a:_} -> Tm88 (snoc88 g a) a
v088 = var88 vz88

v188 : {g:_}->{a:_}-> {B:_}-> Tm88 (snoc88 (snoc88 g a) B) a
v188 = var88 (vs88 vz88)

v288 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm88 (snoc88 (snoc88 (snoc88 g a) B) C) a
v288 = var88 (vs88 (vs88 vz88))

v388 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm88 (snoc88 (snoc88 (snoc88 (snoc88 g a) B) C) D) a
v388 = var88 (vs88 (vs88 (vs88 vz88)))

v488 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm88 (snoc88 (snoc88 (snoc88 (snoc88 (snoc88 g a) B) C) D) E) a
v488 = var88 (vs88 (vs88 (vs88 (vs88 vz88))))

test88 : {g:_}-> {a:_} -> Tm88 g (arr88 (arr88 a a) (arr88 a a))
test88  = lam88 (lam88 (app88 v188 (app88 v188 (app88 v188 (app88 v188 (app88 v188 (app88 v188 v088)))))))
Ty89 : Type
Ty89 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty89 : Ty89
empty89 = \ _, empty, _ => empty

arr89 : Ty89 -> Ty89 -> Ty89
arr89 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con89 : Type
Con89 = (Con89 : Type)
 ->(nil  : Con89)
 ->(snoc : Con89 -> Ty89 -> Con89)
 -> Con89

nil89 : Con89
nil89 = \ con, nil89, snoc => nil89

snoc89 : Con89 -> Ty89 -> Con89
snoc89 = \ g, a, con, nil89, snoc89 => snoc89 (g con nil89 snoc89) a

Var89 : Con89 -> Ty89 -> Type
Var89 = \ g, a =>
    (Var89 : Con89 -> Ty89 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var89 (snoc89 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var89 g a -> Var89 (snoc89 g b) a)
 -> Var89 g a

vz89 : {g : _}-> {a : _} -> Var89 (snoc89 g a) a
vz89 = \ var, vz89, vs => vz89 _ _

vs89 : {g : _} -> {B : _} -> {a : _} -> Var89 g a -> Var89 (snoc89 g B) a
vs89 = \ x, var, vz89, vs89 => vs89 _ _ _ (x var vz89 vs89)

Tm89 : Con89 -> Ty89 -> Type
Tm89 = \ g, a =>
    (Tm89    : Con89 -> Ty89 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var89 g a -> Tm89 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm89 (snoc89 g a) B -> Tm89 g (arr89 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm89 g (arr89 a B) -> Tm89 g a -> Tm89 g B)
 -> Tm89 g a

var89 : {g : _} -> {a : _} -> Var89 g a -> Tm89 g a
var89 = \ x, tm, var89, lam, app => var89 _ _ x

lam89 : {g : _} -> {a : _} -> {B : _} -> Tm89 (snoc89 g a) B -> Tm89 g (arr89 a B)
lam89 = \ t, tm, var89, lam89, app => lam89 _ _ _ (t tm var89 lam89 app)

app89 : {g:_}->{a:_}->{B:_} -> Tm89 g (arr89 a B) -> Tm89 g a -> Tm89 g B
app89 = \ t, u, tm, var89, lam89, app89 => app89 _ _ _ (t tm var89 lam89 app89) (u tm var89 lam89 app89)

v089 : {g:_}->{a:_} -> Tm89 (snoc89 g a) a
v089 = var89 vz89

v189 : {g:_}->{a:_}-> {B:_}-> Tm89 (snoc89 (snoc89 g a) B) a
v189 = var89 (vs89 vz89)

v289 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm89 (snoc89 (snoc89 (snoc89 g a) B) C) a
v289 = var89 (vs89 (vs89 vz89))

v389 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm89 (snoc89 (snoc89 (snoc89 (snoc89 g a) B) C) D) a
v389 = var89 (vs89 (vs89 (vs89 vz89)))

v489 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm89 (snoc89 (snoc89 (snoc89 (snoc89 (snoc89 g a) B) C) D) E) a
v489 = var89 (vs89 (vs89 (vs89 (vs89 vz89))))

test89 : {g:_}-> {a:_} -> Tm89 g (arr89 (arr89 a a) (arr89 a a))
test89  = lam89 (lam89 (app89 v189 (app89 v189 (app89 v189 (app89 v189 (app89 v189 (app89 v189 v089)))))))
Ty90 : Type
Ty90 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty90 : Ty90
empty90 = \ _, empty, _ => empty

arr90 : Ty90 -> Ty90 -> Ty90
arr90 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con90 : Type
Con90 = (Con90 : Type)
 ->(nil  : Con90)
 ->(snoc : Con90 -> Ty90 -> Con90)
 -> Con90

nil90 : Con90
nil90 = \ con, nil90, snoc => nil90

snoc90 : Con90 -> Ty90 -> Con90
snoc90 = \ g, a, con, nil90, snoc90 => snoc90 (g con nil90 snoc90) a

Var90 : Con90 -> Ty90 -> Type
Var90 = \ g, a =>
    (Var90 : Con90 -> Ty90 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var90 (snoc90 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var90 g a -> Var90 (snoc90 g b) a)
 -> Var90 g a

vz90 : {g : _}-> {a : _} -> Var90 (snoc90 g a) a
vz90 = \ var, vz90, vs => vz90 _ _

vs90 : {g : _} -> {B : _} -> {a : _} -> Var90 g a -> Var90 (snoc90 g B) a
vs90 = \ x, var, vz90, vs90 => vs90 _ _ _ (x var vz90 vs90)

Tm90 : Con90 -> Ty90 -> Type
Tm90 = \ g, a =>
    (Tm90    : Con90 -> Ty90 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var90 g a -> Tm90 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm90 (snoc90 g a) B -> Tm90 g (arr90 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm90 g (arr90 a B) -> Tm90 g a -> Tm90 g B)
 -> Tm90 g a

var90 : {g : _} -> {a : _} -> Var90 g a -> Tm90 g a
var90 = \ x, tm, var90, lam, app => var90 _ _ x

lam90 : {g : _} -> {a : _} -> {B : _} -> Tm90 (snoc90 g a) B -> Tm90 g (arr90 a B)
lam90 = \ t, tm, var90, lam90, app => lam90 _ _ _ (t tm var90 lam90 app)

app90 : {g:_}->{a:_}->{B:_} -> Tm90 g (arr90 a B) -> Tm90 g a -> Tm90 g B
app90 = \ t, u, tm, var90, lam90, app90 => app90 _ _ _ (t tm var90 lam90 app90) (u tm var90 lam90 app90)

v090 : {g:_}->{a:_} -> Tm90 (snoc90 g a) a
v090 = var90 vz90

v190 : {g:_}->{a:_}-> {B:_}-> Tm90 (snoc90 (snoc90 g a) B) a
v190 = var90 (vs90 vz90)

v290 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm90 (snoc90 (snoc90 (snoc90 g a) B) C) a
v290 = var90 (vs90 (vs90 vz90))

v390 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm90 (snoc90 (snoc90 (snoc90 (snoc90 g a) B) C) D) a
v390 = var90 (vs90 (vs90 (vs90 vz90)))

v490 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm90 (snoc90 (snoc90 (snoc90 (snoc90 (snoc90 g a) B) C) D) E) a
v490 = var90 (vs90 (vs90 (vs90 (vs90 vz90))))

test90 : {g:_}-> {a:_} -> Tm90 g (arr90 (arr90 a a) (arr90 a a))
test90  = lam90 (lam90 (app90 v190 (app90 v190 (app90 v190 (app90 v190 (app90 v190 (app90 v190 v090)))))))
Ty91 : Type
Ty91 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty91 : Ty91
empty91 = \ _, empty, _ => empty

arr91 : Ty91 -> Ty91 -> Ty91
arr91 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con91 : Type
Con91 = (Con91 : Type)
 ->(nil  : Con91)
 ->(snoc : Con91 -> Ty91 -> Con91)
 -> Con91

nil91 : Con91
nil91 = \ con, nil91, snoc => nil91

snoc91 : Con91 -> Ty91 -> Con91
snoc91 = \ g, a, con, nil91, snoc91 => snoc91 (g con nil91 snoc91) a

Var91 : Con91 -> Ty91 -> Type
Var91 = \ g, a =>
    (Var91 : Con91 -> Ty91 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var91 (snoc91 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var91 g a -> Var91 (snoc91 g b) a)
 -> Var91 g a

vz91 : {g : _}-> {a : _} -> Var91 (snoc91 g a) a
vz91 = \ var, vz91, vs => vz91 _ _

vs91 : {g : _} -> {B : _} -> {a : _} -> Var91 g a -> Var91 (snoc91 g B) a
vs91 = \ x, var, vz91, vs91 => vs91 _ _ _ (x var vz91 vs91)

Tm91 : Con91 -> Ty91 -> Type
Tm91 = \ g, a =>
    (Tm91    : Con91 -> Ty91 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var91 g a -> Tm91 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm91 (snoc91 g a) B -> Tm91 g (arr91 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm91 g (arr91 a B) -> Tm91 g a -> Tm91 g B)
 -> Tm91 g a

var91 : {g : _} -> {a : _} -> Var91 g a -> Tm91 g a
var91 = \ x, tm, var91, lam, app => var91 _ _ x

lam91 : {g : _} -> {a : _} -> {B : _} -> Tm91 (snoc91 g a) B -> Tm91 g (arr91 a B)
lam91 = \ t, tm, var91, lam91, app => lam91 _ _ _ (t tm var91 lam91 app)

app91 : {g:_}->{a:_}->{B:_} -> Tm91 g (arr91 a B) -> Tm91 g a -> Tm91 g B
app91 = \ t, u, tm, var91, lam91, app91 => app91 _ _ _ (t tm var91 lam91 app91) (u tm var91 lam91 app91)

v091 : {g:_}->{a:_} -> Tm91 (snoc91 g a) a
v091 = var91 vz91

v191 : {g:_}->{a:_}-> {B:_}-> Tm91 (snoc91 (snoc91 g a) B) a
v191 = var91 (vs91 vz91)

v291 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm91 (snoc91 (snoc91 (snoc91 g a) B) C) a
v291 = var91 (vs91 (vs91 vz91))

v391 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm91 (snoc91 (snoc91 (snoc91 (snoc91 g a) B) C) D) a
v391 = var91 (vs91 (vs91 (vs91 vz91)))

v491 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm91 (snoc91 (snoc91 (snoc91 (snoc91 (snoc91 g a) B) C) D) E) a
v491 = var91 (vs91 (vs91 (vs91 (vs91 vz91))))

test91 : {g:_}-> {a:_} -> Tm91 g (arr91 (arr91 a a) (arr91 a a))
test91  = lam91 (lam91 (app91 v191 (app91 v191 (app91 v191 (app91 v191 (app91 v191 (app91 v191 v091)))))))
Ty92 : Type
Ty92 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty92 : Ty92
empty92 = \ _, empty, _ => empty

arr92 : Ty92 -> Ty92 -> Ty92
arr92 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con92 : Type
Con92 = (Con92 : Type)
 ->(nil  : Con92)
 ->(snoc : Con92 -> Ty92 -> Con92)
 -> Con92

nil92 : Con92
nil92 = \ con, nil92, snoc => nil92

snoc92 : Con92 -> Ty92 -> Con92
snoc92 = \ g, a, con, nil92, snoc92 => snoc92 (g con nil92 snoc92) a

Var92 : Con92 -> Ty92 -> Type
Var92 = \ g, a =>
    (Var92 : Con92 -> Ty92 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var92 (snoc92 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var92 g a -> Var92 (snoc92 g b) a)
 -> Var92 g a

vz92 : {g : _}-> {a : _} -> Var92 (snoc92 g a) a
vz92 = \ var, vz92, vs => vz92 _ _

vs92 : {g : _} -> {B : _} -> {a : _} -> Var92 g a -> Var92 (snoc92 g B) a
vs92 = \ x, var, vz92, vs92 => vs92 _ _ _ (x var vz92 vs92)

Tm92 : Con92 -> Ty92 -> Type
Tm92 = \ g, a =>
    (Tm92    : Con92 -> Ty92 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var92 g a -> Tm92 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm92 (snoc92 g a) B -> Tm92 g (arr92 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm92 g (arr92 a B) -> Tm92 g a -> Tm92 g B)
 -> Tm92 g a

var92 : {g : _} -> {a : _} -> Var92 g a -> Tm92 g a
var92 = \ x, tm, var92, lam, app => var92 _ _ x

lam92 : {g : _} -> {a : _} -> {B : _} -> Tm92 (snoc92 g a) B -> Tm92 g (arr92 a B)
lam92 = \ t, tm, var92, lam92, app => lam92 _ _ _ (t tm var92 lam92 app)

app92 : {g:_}->{a:_}->{B:_} -> Tm92 g (arr92 a B) -> Tm92 g a -> Tm92 g B
app92 = \ t, u, tm, var92, lam92, app92 => app92 _ _ _ (t tm var92 lam92 app92) (u tm var92 lam92 app92)

v092 : {g:_}->{a:_} -> Tm92 (snoc92 g a) a
v092 = var92 vz92

v192 : {g:_}->{a:_}-> {B:_}-> Tm92 (snoc92 (snoc92 g a) B) a
v192 = var92 (vs92 vz92)

v292 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm92 (snoc92 (snoc92 (snoc92 g a) B) C) a
v292 = var92 (vs92 (vs92 vz92))

v392 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm92 (snoc92 (snoc92 (snoc92 (snoc92 g a) B) C) D) a
v392 = var92 (vs92 (vs92 (vs92 vz92)))

v492 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm92 (snoc92 (snoc92 (snoc92 (snoc92 (snoc92 g a) B) C) D) E) a
v492 = var92 (vs92 (vs92 (vs92 (vs92 vz92))))

test92 : {g:_}-> {a:_} -> Tm92 g (arr92 (arr92 a a) (arr92 a a))
test92  = lam92 (lam92 (app92 v192 (app92 v192 (app92 v192 (app92 v192 (app92 v192 (app92 v192 v092)))))))
Ty93 : Type
Ty93 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty93 : Ty93
empty93 = \ _, empty, _ => empty

arr93 : Ty93 -> Ty93 -> Ty93
arr93 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con93 : Type
Con93 = (Con93 : Type)
 ->(nil  : Con93)
 ->(snoc : Con93 -> Ty93 -> Con93)
 -> Con93

nil93 : Con93
nil93 = \ con, nil93, snoc => nil93

snoc93 : Con93 -> Ty93 -> Con93
snoc93 = \ g, a, con, nil93, snoc93 => snoc93 (g con nil93 snoc93) a

Var93 : Con93 -> Ty93 -> Type
Var93 = \ g, a =>
    (Var93 : Con93 -> Ty93 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var93 (snoc93 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var93 g a -> Var93 (snoc93 g b) a)
 -> Var93 g a

vz93 : {g : _}-> {a : _} -> Var93 (snoc93 g a) a
vz93 = \ var, vz93, vs => vz93 _ _

vs93 : {g : _} -> {B : _} -> {a : _} -> Var93 g a -> Var93 (snoc93 g B) a
vs93 = \ x, var, vz93, vs93 => vs93 _ _ _ (x var vz93 vs93)

Tm93 : Con93 -> Ty93 -> Type
Tm93 = \ g, a =>
    (Tm93    : Con93 -> Ty93 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var93 g a -> Tm93 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm93 (snoc93 g a) B -> Tm93 g (arr93 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm93 g (arr93 a B) -> Tm93 g a -> Tm93 g B)
 -> Tm93 g a

var93 : {g : _} -> {a : _} -> Var93 g a -> Tm93 g a
var93 = \ x, tm, var93, lam, app => var93 _ _ x

lam93 : {g : _} -> {a : _} -> {B : _} -> Tm93 (snoc93 g a) B -> Tm93 g (arr93 a B)
lam93 = \ t, tm, var93, lam93, app => lam93 _ _ _ (t tm var93 lam93 app)

app93 : {g:_}->{a:_}->{B:_} -> Tm93 g (arr93 a B) -> Tm93 g a -> Tm93 g B
app93 = \ t, u, tm, var93, lam93, app93 => app93 _ _ _ (t tm var93 lam93 app93) (u tm var93 lam93 app93)

v093 : {g:_}->{a:_} -> Tm93 (snoc93 g a) a
v093 = var93 vz93

v193 : {g:_}->{a:_}-> {B:_}-> Tm93 (snoc93 (snoc93 g a) B) a
v193 = var93 (vs93 vz93)

v293 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm93 (snoc93 (snoc93 (snoc93 g a) B) C) a
v293 = var93 (vs93 (vs93 vz93))

v393 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm93 (snoc93 (snoc93 (snoc93 (snoc93 g a) B) C) D) a
v393 = var93 (vs93 (vs93 (vs93 vz93)))

v493 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm93 (snoc93 (snoc93 (snoc93 (snoc93 (snoc93 g a) B) C) D) E) a
v493 = var93 (vs93 (vs93 (vs93 (vs93 vz93))))

test93 : {g:_}-> {a:_} -> Tm93 g (arr93 (arr93 a a) (arr93 a a))
test93  = lam93 (lam93 (app93 v193 (app93 v193 (app93 v193 (app93 v193 (app93 v193 (app93 v193 v093)))))))
Ty94 : Type
Ty94 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty94 : Ty94
empty94 = \ _, empty, _ => empty

arr94 : Ty94 -> Ty94 -> Ty94
arr94 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con94 : Type
Con94 = (Con94 : Type)
 ->(nil  : Con94)
 ->(snoc : Con94 -> Ty94 -> Con94)
 -> Con94

nil94 : Con94
nil94 = \ con, nil94, snoc => nil94

snoc94 : Con94 -> Ty94 -> Con94
snoc94 = \ g, a, con, nil94, snoc94 => snoc94 (g con nil94 snoc94) a

Var94 : Con94 -> Ty94 -> Type
Var94 = \ g, a =>
    (Var94 : Con94 -> Ty94 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var94 (snoc94 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var94 g a -> Var94 (snoc94 g b) a)
 -> Var94 g a

vz94 : {g : _}-> {a : _} -> Var94 (snoc94 g a) a
vz94 = \ var, vz94, vs => vz94 _ _

vs94 : {g : _} -> {B : _} -> {a : _} -> Var94 g a -> Var94 (snoc94 g B) a
vs94 = \ x, var, vz94, vs94 => vs94 _ _ _ (x var vz94 vs94)

Tm94 : Con94 -> Ty94 -> Type
Tm94 = \ g, a =>
    (Tm94    : Con94 -> Ty94 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var94 g a -> Tm94 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm94 (snoc94 g a) B -> Tm94 g (arr94 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm94 g (arr94 a B) -> Tm94 g a -> Tm94 g B)
 -> Tm94 g a

var94 : {g : _} -> {a : _} -> Var94 g a -> Tm94 g a
var94 = \ x, tm, var94, lam, app => var94 _ _ x

lam94 : {g : _} -> {a : _} -> {B : _} -> Tm94 (snoc94 g a) B -> Tm94 g (arr94 a B)
lam94 = \ t, tm, var94, lam94, app => lam94 _ _ _ (t tm var94 lam94 app)

app94 : {g:_}->{a:_}->{B:_} -> Tm94 g (arr94 a B) -> Tm94 g a -> Tm94 g B
app94 = \ t, u, tm, var94, lam94, app94 => app94 _ _ _ (t tm var94 lam94 app94) (u tm var94 lam94 app94)

v094 : {g:_}->{a:_} -> Tm94 (snoc94 g a) a
v094 = var94 vz94

v194 : {g:_}->{a:_}-> {B:_}-> Tm94 (snoc94 (snoc94 g a) B) a
v194 = var94 (vs94 vz94)

v294 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm94 (snoc94 (snoc94 (snoc94 g a) B) C) a
v294 = var94 (vs94 (vs94 vz94))

v394 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm94 (snoc94 (snoc94 (snoc94 (snoc94 g a) B) C) D) a
v394 = var94 (vs94 (vs94 (vs94 vz94)))

v494 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm94 (snoc94 (snoc94 (snoc94 (snoc94 (snoc94 g a) B) C) D) E) a
v494 = var94 (vs94 (vs94 (vs94 (vs94 vz94))))

test94 : {g:_}-> {a:_} -> Tm94 g (arr94 (arr94 a a) (arr94 a a))
test94  = lam94 (lam94 (app94 v194 (app94 v194 (app94 v194 (app94 v194 (app94 v194 (app94 v194 v094)))))))
Ty95 : Type
Ty95 = (Ty    : Type)
   ->(empty : Ty)
   ->(arr   : Ty -> Ty -> Ty)
   -> Ty

empty95 : Ty95
empty95 = \ _, empty, _ => empty

arr95 : Ty95 -> Ty95 -> Ty95
arr95 = \ a, b, ty, empty, arr => arr (a ty empty arr) (b ty empty arr)

Con95 : Type
Con95 = (Con95 : Type)
 ->(nil  : Con95)
 ->(snoc : Con95 -> Ty95 -> Con95)
 -> Con95

nil95 : Con95
nil95 = \ con, nil95, snoc => nil95

snoc95 : Con95 -> Ty95 -> Con95
snoc95 = \ g, a, con, nil95, snoc95 => snoc95 (g con nil95 snoc95) a

Var95 : Con95 -> Ty95 -> Type
Var95 = \ g, a =>
    (Var95 : Con95 -> Ty95 -> Type)
 -> (vz  : (g : _)-> (a : _) -> Var95 (snoc95 g a) a)
 -> (vs  : (g : _)-> (b : _) ->  (a : _) -> Var95 g a -> Var95 (snoc95 g b) a)
 -> Var95 g a

vz95 : {g : _}-> {a : _} -> Var95 (snoc95 g a) a
vz95 = \ var, vz95, vs => vz95 _ _

vs95 : {g : _} -> {B : _} -> {a : _} -> Var95 g a -> Var95 (snoc95 g B) a
vs95 = \ x, var, vz95, vs95 => vs95 _ _ _ (x var vz95 vs95)

Tm95 : Con95 -> Ty95 -> Type
Tm95 = \ g, a =>
    (Tm95    : Con95 -> Ty95 -> Type)
 -> (var   : (g : _) -> (a : _) -> Var95 g a -> Tm95 g a)
 -> (lam   : (g : _) -> (a : _) -> (B : _) -> Tm95 (snoc95 g a) B -> Tm95 g (arr95 a B))
 -> (app   : (g : _) -> (a : _) -> (B : _) -> Tm95 g (arr95 a B) -> Tm95 g a -> Tm95 g B)
 -> Tm95 g a

var95 : {g : _} -> {a : _} -> Var95 g a -> Tm95 g a
var95 = \ x, tm, var95, lam, app => var95 _ _ x

lam95 : {g : _} -> {a : _} -> {B : _} -> Tm95 (snoc95 g a) B -> Tm95 g (arr95 a B)
lam95 = \ t, tm, var95, lam95, app => lam95 _ _ _ (t tm var95 lam95 app)

app95 : {g:_}->{a:_}->{B:_} -> Tm95 g (arr95 a B) -> Tm95 g a -> Tm95 g B
app95 = \ t, u, tm, var95, lam95, app95 => app95 _ _ _ (t tm var95 lam95 app95) (u tm var95 lam95 app95)

v095 : {g:_}->{a:_} -> Tm95 (snoc95 g a) a
v095 = var95 vz95

v195 : {g:_}->{a:_}-> {B:_}-> Tm95 (snoc95 (snoc95 g a) B) a
v195 = var95 (vs95 vz95)

v295 : {g:_}-> {a:_}-> {B:_}-> {C:_} -> Tm95 (snoc95 (snoc95 (snoc95 g a) B) C) a
v295 = var95 (vs95 (vs95 vz95))

v395 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_} -> Tm95 (snoc95 (snoc95 (snoc95 (snoc95 g a) B) C) D) a
v395 = var95 (vs95 (vs95 (vs95 vz95)))

v495 : {g:_}-> {a:_}-> {B:_}-> {C:_}-> {D:_}-> {E:_}-> Tm95 (snoc95 (snoc95 (snoc95 (snoc95 (snoc95 g a) B) C) D) E) a
v495 = var95 (vs95 (vs95 (vs95 (vs95 vz95))))

test95 : {g:_}-> {a:_} -> Tm95 g (arr95 (arr95 a a) (arr95 a a))
test95  = lam95 (lam95 (app95 v195 (app95 v195 (app95 v195 (app95 v195 (app95 v195 (app95 v195 v095)))))))
