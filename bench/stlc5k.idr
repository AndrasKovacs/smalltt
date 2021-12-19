
Ty : Type
Ty = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat : Ty
nat = \ _, nat, _, _, _, _, _ => nat
top : Ty
top = \ _, _, top, _, _, _, _ => top
bot : Ty
bot = \ _, _, _, bot, _, _, _ => bot

arr : Ty-> Ty-> Ty
arr = \ a, b, ty, nat, top, bot, arr, prod, sum =>
     arr (a ty nat top bot arr prod sum) (b ty nat top bot arr prod sum)

prod : Ty-> Ty-> Ty
prod = \ a, b, ty, nat, top, bot, arr, prod, sum =>
     prod (a ty nat top bot arr prod sum) (b ty nat top bot arr prod sum)

sum : Ty-> Ty-> Ty
sum = \ a, b, ty, nat, top, bot, arr, prod, sum =>
     sum (a ty nat top bot arr prod sum) (b ty nat top bot arr prod sum)

Con : Type
Con = (Con : Type)
 -> (nil  : Con)
 -> (snoc : Con -> Ty-> Con)
 -> Con

nil : Con
nil = \ con, nil, snoc => nil

snoc : Con -> Ty-> Con
snoc = \ g, a, con, nil, snoc => snoc (g con nil snoc) a

Var : Con -> Ty-> Type
Var = \ g, a =>
    (Var : Con -> Ty-> Type)
 -> (vz  : {g:_}->{a:_} -> Var (snoc g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var g a -> Var (snoc g b) a)
 -> Var g a

vz : {g:_}->{a:_} -> Var (snoc g a) a
vz = \ var, vz, vs => vz

vs : {g:_}->{b:_}->{a:_} -> Var g a -> Var (snoc g b) a
vs = \ x, var, vz, vs => vs (x var vz vs)

Tm : Con -> Ty-> Type
Tm = \ g, a =>
    (Tm    : Con -> Ty-> Type)
 -> (var   : {g:_}->{a:_}-> Var g a -> Tm g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm (snoc g a) b -> Tm g (arr a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm g (arr a b) -> Tm g a -> Tm g b)
 -> (tt    : {g:_}-> Tm g top)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm g a -> Tm g b -> Tm g (prod a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm g (prod a b) -> Tm g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm g (prod a b) -> Tm g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm g a -> Tm g (sum a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm g b -> Tm g (sum a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm g (sum a b) -> Tm g (arr a c) -> Tm g (arr b c) -> Tm g c)
 -> (zero  : {g:_}-> Tm g nat)
 -> (suc   : {g:_}-> Tm g nat -> Tm g nat)
 -> (rec   : {g:_}->{a:_} -> Tm g nat -> Tm g (arr nat (arr a a)) -> Tm g a -> Tm g a)
 -> Tm g a

var : {g:_}->{a:_} -> Var g a -> Tm g a
var = \ x, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var x

lam : {g:_}->{a:_}->{b:_}-> Tm (snoc g a) b -> Tm g (arr a b)
lam = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam (t tm var lam app tt pair fst snd left right split zero suc rec)

app : {g:_}->{a:_}->{b:_} -> Tm g (arr a b) -> Tm g a -> Tm g b
app = \ t, u, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app (t tm var lam app tt pair fst snd left right split zero suc rec)
         (u tm var lam app tt pair fst snd left right split zero suc rec)

tt : {g:_} -> Tm g Main.top
tt = \ tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => tt

pair : {g:_}->{a:_}->{b:_} -> Tm g a -> Tm g b -> Tm g (prod a b)
pair = \ t, u, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     pair (t tm var lam app tt pair fst snd left right split zero suc rec)
          (u tm var lam app tt pair fst snd left right split zero suc rec)

fst : {g:_}->{a:_}->{b:_}-> Tm g (prod a b) -> Tm g a
fst = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     fst (t tm var lam app tt pair fst snd left right split zero suc rec)

snd : {g:_}->{a:_}->{b:_} -> Tm g (prod a b) -> Tm g b
snd = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     snd (t tm var lam app tt pair fst snd left right split zero suc rec)

left : {g:_}->{a:_}->{b:_} -> Tm g a -> Tm g (sum a b)
left = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     left (t tm var lam app tt pair fst snd left right split zero suc rec)

right : {g:_}->{a:_}->{b:_} -> Tm g b -> Tm g (sum a b)
right = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     right (t tm var lam app tt pair fst snd left right split zero suc rec)

split : {g:_}->{a:_}->{b:_}->{c:_} -> Tm g (sum a b) -> Tm g (arr a c) -> Tm g (arr b c) -> Tm g c
split = \ t, u, v, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     split (t tm var lam app tt pair fst snd left right split zero suc rec)
          (u tm var lam app tt pair fst snd left right split zero suc rec)
          (v tm var lam app tt pair fst snd left right split zero suc rec)

zero : {g:_} -> Tm g Main.nat
zero = \ tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => zero

suc : {g:_} -> Tm g Main.nat -> Tm g Main.nat
suc = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
   suc (t tm var lam app tt pair fst snd left right split zero suc rec)

rec : {g:_}->{a:_} -> Tm g Main.nat -> Tm g (arr Main.nat (arr a a)) -> Tm g a -> Tm g a
rec = \ t, u, v, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     rec (t tm var lam app tt pair fst snd left right split zero suc rec)
         (u tm var lam app tt pair fst snd left right split zero suc rec)
         (v tm var lam app tt pair fst snd left right split zero suc rec)

v0 : {g:_}->{a:_} -> Tm (snoc g a) a
v0 = var vz

v1 : {g:_}->{a:_}->{b:_} -> Tm (snoc (snoc g a) b) a
v1 = var (vs vz)

v2 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm (snoc (snoc (snoc g a) b) c) a
v2 = var (vs (vs vz))

v3 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm (snoc (snoc (snoc (snoc g a) b) c) d) a
v3 = var (vs (vs (vs vz)))

tbool : Ty
tbool = sum top top

ttrue : {g:_} -> Tm g Main.tbool
ttrue = left tt

tfalse : {g:_} -> Tm g Main.tbool
tfalse = right tt

ifthenelse : {g:_}->{a:_} -> Tm g (arr Main.tbool (arr a (arr a a)))
ifthenelse = lam (lam (lam (split v2 (lam v2) (lam v1))))

times4 : {g:_}->{a:_} -> Tm g (arr (arr a a) (arr a a))
times4  = lam (lam (app v1 (app v1 (app v1 (app v1 v0)))))

add : {g:_} -> Tm g (arr Main.nat (arr Main.nat Main.nat))
add = lam (rec v0
       (lam (lam (lam (suc (app v1 v0)))))
       (lam v0))

mul : {g:_} -> Tm g (arr Main.nat (arr Main.nat Main.nat))
mul = lam (rec v0
       (lam (lam (lam (app (app add (app v1 v0)) v0))))
       (lam zero))

fact : {g:_} -> Tm g (arr Main.nat Main.nat)
fact = lam (rec v0 (lam (lam (app (app mul (suc v1)) v0)))
                 (suc zero))

Ty1 : Type
Ty1 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat1 : Ty1
nat1 = \ _, nat1, _, _, _, _, _ => nat1
top1 : Ty1
top1 = \ _, _, top1, _, _, _, _ => top1
bot1 : Ty1
bot1 = \ _, _, _, bot1, _, _, _ => bot1

arr1 : Ty1-> Ty1-> Ty1
arr1 = \ a, b, ty, nat1, top1, bot1, arr1, prod, sum =>
     arr1 (a ty nat1 top1 bot1 arr1 prod sum) (b ty nat1 top1 bot1 arr1 prod sum)

prod1 : Ty1-> Ty1-> Ty1
prod1 = \ a, b, ty, nat1, top1, bot1, arr1, prod1, sum =>
     prod1 (a ty nat1 top1 bot1 arr1 prod1 sum) (b ty nat1 top1 bot1 arr1 prod1 sum)

sum1 : Ty1-> Ty1-> Ty1
sum1 = \ a, b, ty, nat1, top1, bot1, arr1, prod1, sum1 =>
     sum1 (a ty nat1 top1 bot1 arr1 prod1 sum1) (b ty nat1 top1 bot1 arr1 prod1 sum1)

Con1 : Type
Con1 = (Con1 : Type)
 -> (nil  : Con1)
 -> (snoc : Con1 -> Ty1-> Con1)
 -> Con1

nil1 : Con1
nil1 = \ con, nil1, snoc => nil1

snoc1 : Con1 -> Ty1-> Con1
snoc1 = \ g, a, con, nil1, snoc1 => snoc1 (g con nil1 snoc1) a

Var1 : Con1 -> Ty1-> Type
Var1 = \ g, a =>
    (Var1 : Con1 -> Ty1-> Type)
 -> (vz  : {g:_}->{a:_} -> Var1 (snoc1 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var1 g a -> Var1 (snoc1 g b) a)
 -> Var1 g a

vz1 : {g:_}->{a:_} -> Var1 (snoc1 g a) a
vz1 = \ var, vz1, vs => vz1

vs1 : {g:_}->{b:_}->{a:_} -> Var1 g a -> Var1 (snoc1 g b) a
vs1 = \ x, var, vz1, vs1 => vs1 (x var vz1 vs1)

Tm1 : Con1 -> Ty1-> Type
Tm1 = \ g, a =>
    (Tm1    : Con1 -> Ty1-> Type)
 -> (var   : {g:_}->{a:_}-> Var1 g a -> Tm1 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm1 (snoc1 g a) b -> Tm1 g (arr1 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm1 g (arr1 a b) -> Tm1 g a -> Tm1 g b)
 -> (tt    : {g:_}-> Tm1 g top1)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm1 g a -> Tm1 g b -> Tm1 g (prod1 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm1 g (prod1 a b) -> Tm1 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm1 g (prod1 a b) -> Tm1 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm1 g a -> Tm1 g (sum1 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm1 g b -> Tm1 g (sum1 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm1 g (sum1 a b) -> Tm1 g (arr1 a c) -> Tm1 g (arr1 b c) -> Tm1 g c)
 -> (zero  : {g:_}-> Tm1 g nat1)
 -> (suc   : {g:_}-> Tm1 g nat1 -> Tm1 g nat1)
 -> (rec   : {g:_}->{a:_} -> Tm1 g nat1 -> Tm1 g (arr1 nat1 (arr1 a a)) -> Tm1 g a -> Tm1 g a)
 -> Tm1 g a

var1 : {g:_}->{a:_} -> Var1 g a -> Tm1 g a
var1 = \ x, tm, var1, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var1 x

lam1 : {g:_}->{a:_}->{b:_}-> Tm1 (snoc1 g a) b -> Tm1 g (arr1 a b)
lam1 = \ t, tm, var1, lam1, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam1 (t tm var1 lam1 app tt pair fst snd left right split zero suc rec)

app1 : {g:_}->{a:_}->{b:_} -> Tm1 g (arr1 a b) -> Tm1 g a -> Tm1 g b
app1 = \ t, u, tm, var1, lam1, app1, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app1 (t tm var1 lam1 app1 tt pair fst snd left right split zero suc rec)
         (u tm var1 lam1 app1 tt pair fst snd left right split zero suc rec)

tt1 : {g:_} -> Tm1 g Main.top1
tt1 = \ tm, var1, lam1, app1, tt1, pair, fst, snd, left, right, split, zero, suc, rec => tt1

pair1 : {g:_}->{a:_}->{b:_} -> Tm1 g a -> Tm1 g b -> Tm1 g (prod1 a b)
pair1 = \ t, u, tm, var1, lam1, app1, tt1, pair1, fst, snd, left, right, split, zero, suc, rec =>
     pair1 (t tm var1 lam1 app1 tt1 pair1 fst snd left right split zero suc rec)
          (u tm var1 lam1 app1 tt1 pair1 fst snd left right split zero suc rec)

fst1 : {g:_}->{a:_}->{b:_}-> Tm1 g (prod1 a b) -> Tm1 g a
fst1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd, left, right, split, zero, suc, rec =>
     fst1 (t tm var1 lam1 app1 tt1 pair1 fst1 snd left right split zero suc rec)

snd1 : {g:_}->{a:_}->{b:_} -> Tm1 g (prod1 a b) -> Tm1 g b
snd1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left, right, split, zero, suc, rec =>
     snd1 (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left right split zero suc rec)

left1 : {g:_}->{a:_}->{b:_} -> Tm1 g a -> Tm1 g (sum1 a b)
left1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right, split, zero, suc, rec =>
     left1 (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right split zero suc rec)

right1 : {g:_}->{a:_}->{b:_} -> Tm1 g b -> Tm1 g (sum1 a b)
right1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split, zero, suc, rec =>
     right1 (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split zero suc rec)

split1 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm1 g (sum1 a b) -> Tm1 g (arr1 a c) -> Tm1 g (arr1 b c) -> Tm1 g c
split1 = \ t, u, v, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split1, zero, suc, rec =>
     split1 (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero suc rec)
          (u tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero suc rec)
          (v tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero suc rec)

zero1 : {g:_} -> Tm1 g Main.nat1
zero1 = \ tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split1, zero1, suc, rec => zero1

suc1 : {g:_} -> Tm1 g Main.nat1 -> Tm1 g Main.nat1
suc1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split1, zero1, suc1, rec =>
   suc1 (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero1 suc1 rec)

rec1 : {g:_}->{a:_} -> Tm1 g Main.nat1 -> Tm1 g (arr1 Main.nat1 (arr1 a a)) -> Tm1 g a -> Tm1 g a
rec1 = \ t, u, v, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split1, zero1, suc1, rec1 =>
     rec1 (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero1 suc1 rec1)
         (u tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero1 suc1 rec1)
         (v tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero1 suc1 rec1)

v01 : {g:_}->{a:_} -> Tm1 (snoc1 g a) a
v01 = var1 vz1

v11 : {g:_}->{a:_}->{b:_} -> Tm1 (snoc1 (snoc1 g a) b) a
v11 = var1 (vs1 vz1)

v21 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm1 (snoc1 (snoc1 (snoc1 g a) b) c) a
v21 = var1 (vs1 (vs1 vz1))

v31 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm1 (snoc1 (snoc1 (snoc1 (snoc1 g a) b) c) d) a
v31 = var1 (vs1 (vs1 (vs1 vz1)))

tbool1 : Ty1
tbool1 = sum1 top1 top1

ttrue1 : {g:_} -> Tm1 g Main.tbool1
ttrue1 = left1 tt1

tfalse1 : {g:_} -> Tm1 g Main.tbool1
tfalse1 = right1 tt1

ifthenelse1 : {g:_}->{a:_} -> Tm1 g (arr1 Main.tbool1 (arr1 a (arr1 a a)))
ifthenelse1 = lam1 (lam1 (lam1 (split1 v21 (lam1 v21) (lam1 v11))))

times41 : {g:_}->{a:_} -> Tm1 g (arr1 (arr1 a a) (arr1 a a))
times41  = lam1 (lam1 (app1 v11 (app1 v11 (app1 v11 (app1 v11 v01)))))

add1 : {g:_} -> Tm1 g (arr1 Main.nat1 (arr1 Main.nat1 Main.nat1))
add1 = lam1 (rec1 v01
       (lam1 (lam1 (lam1 (suc1 (app1 v11 v01)))))
       (lam1 v01))

mul1 : {g:_} -> Tm1 g (arr1 Main.nat1 (arr1 Main.nat1 Main.nat1))
mul1 = lam1 (rec1 v01
       (lam1 (lam1 (lam1 (app1 (app1 add1 (app1 v11 v01)) v01))))
       (lam1 zero1))

fact1 : {g:_} -> Tm1 g (arr1 Main.nat1 Main.nat1)
fact1 = lam1 (rec1 v01 (lam1 (lam1 (app1 (app1 mul1 (suc1 v11)) v01)))
                 (suc1 zero1))

Ty2 : Type
Ty2 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat2 : Ty2
nat2 = \ _, nat2, _, _, _, _, _ => nat2
top2 : Ty2
top2 = \ _, _, top2, _, _, _, _ => top2
bot2 : Ty2
bot2 = \ _, _, _, bot2, _, _, _ => bot2

arr2 : Ty2-> Ty2-> Ty2
arr2 = \ a, b, ty, nat2, top2, bot2, arr2, prod, sum =>
     arr2 (a ty nat2 top2 bot2 arr2 prod sum) (b ty nat2 top2 bot2 arr2 prod sum)

prod2 : Ty2-> Ty2-> Ty2
prod2 = \ a, b, ty, nat2, top2, bot2, arr2, prod2, sum =>
     prod2 (a ty nat2 top2 bot2 arr2 prod2 sum) (b ty nat2 top2 bot2 arr2 prod2 sum)

sum2 : Ty2-> Ty2-> Ty2
sum2 = \ a, b, ty, nat2, top2, bot2, arr2, prod2, sum2 =>
     sum2 (a ty nat2 top2 bot2 arr2 prod2 sum2) (b ty nat2 top2 bot2 arr2 prod2 sum2)

Con2 : Type
Con2 = (Con2 : Type)
 -> (nil  : Con2)
 -> (snoc : Con2 -> Ty2-> Con2)
 -> Con2

nil2 : Con2
nil2 = \ con, nil2, snoc => nil2

snoc2 : Con2 -> Ty2-> Con2
snoc2 = \ g, a, con, nil2, snoc2 => snoc2 (g con nil2 snoc2) a

Var2 : Con2 -> Ty2-> Type
Var2 = \ g, a =>
    (Var2 : Con2 -> Ty2-> Type)
 -> (vz  : {g:_}->{a:_} -> Var2 (snoc2 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var2 g a -> Var2 (snoc2 g b) a)
 -> Var2 g a

vz2 : {g:_}->{a:_} -> Var2 (snoc2 g a) a
vz2 = \ var, vz2, vs => vz2

vs2 : {g:_}->{b:_}->{a:_} -> Var2 g a -> Var2 (snoc2 g b) a
vs2 = \ x, var, vz2, vs2 => vs2 (x var vz2 vs2)

Tm2 : Con2 -> Ty2-> Type
Tm2 = \ g, a =>
    (Tm2    : Con2 -> Ty2-> Type)
 -> (var   : {g:_}->{a:_}-> Var2 g a -> Tm2 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm2 (snoc2 g a) b -> Tm2 g (arr2 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm2 g (arr2 a b) -> Tm2 g a -> Tm2 g b)
 -> (tt    : {g:_}-> Tm2 g top2)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm2 g a -> Tm2 g b -> Tm2 g (prod2 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm2 g (prod2 a b) -> Tm2 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm2 g (prod2 a b) -> Tm2 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm2 g a -> Tm2 g (sum2 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm2 g b -> Tm2 g (sum2 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm2 g (sum2 a b) -> Tm2 g (arr2 a c) -> Tm2 g (arr2 b c) -> Tm2 g c)
 -> (zero  : {g:_}-> Tm2 g nat2)
 -> (suc   : {g:_}-> Tm2 g nat2 -> Tm2 g nat2)
 -> (rec   : {g:_}->{a:_} -> Tm2 g nat2 -> Tm2 g (arr2 nat2 (arr2 a a)) -> Tm2 g a -> Tm2 g a)
 -> Tm2 g a

var2 : {g:_}->{a:_} -> Var2 g a -> Tm2 g a
var2 = \ x, tm, var2, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var2 x

lam2 : {g:_}->{a:_}->{b:_}-> Tm2 (snoc2 g a) b -> Tm2 g (arr2 a b)
lam2 = \ t, tm, var2, lam2, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam2 (t tm var2 lam2 app tt pair fst snd left right split zero suc rec)

app2 : {g:_}->{a:_}->{b:_} -> Tm2 g (arr2 a b) -> Tm2 g a -> Tm2 g b
app2 = \ t, u, tm, var2, lam2, app2, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app2 (t tm var2 lam2 app2 tt pair fst snd left right split zero suc rec)
         (u tm var2 lam2 app2 tt pair fst snd left right split zero suc rec)

tt2 : {g:_} -> Tm2 g Main.top2
tt2 = \ tm, var2, lam2, app2, tt2, pair, fst, snd, left, right, split, zero, suc, rec => tt2

pair2 : {g:_}->{a:_}->{b:_} -> Tm2 g a -> Tm2 g b -> Tm2 g (prod2 a b)
pair2 = \ t, u, tm, var2, lam2, app2, tt2, pair2, fst, snd, left, right, split, zero, suc, rec =>
     pair2 (t tm var2 lam2 app2 tt2 pair2 fst snd left right split zero suc rec)
          (u tm var2 lam2 app2 tt2 pair2 fst snd left right split zero suc rec)

fst2 : {g:_}->{a:_}->{b:_}-> Tm2 g (prod2 a b) -> Tm2 g a
fst2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd, left, right, split, zero, suc, rec =>
     fst2 (t tm var2 lam2 app2 tt2 pair2 fst2 snd left right split zero suc rec)

snd2 : {g:_}->{a:_}->{b:_} -> Tm2 g (prod2 a b) -> Tm2 g b
snd2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left, right, split, zero, suc, rec =>
     snd2 (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left right split zero suc rec)

left2 : {g:_}->{a:_}->{b:_} -> Tm2 g a -> Tm2 g (sum2 a b)
left2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right, split, zero, suc, rec =>
     left2 (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right split zero suc rec)

right2 : {g:_}->{a:_}->{b:_} -> Tm2 g b -> Tm2 g (sum2 a b)
right2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split, zero, suc, rec =>
     right2 (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split zero suc rec)

split2 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm2 g (sum2 a b) -> Tm2 g (arr2 a c) -> Tm2 g (arr2 b c) -> Tm2 g c
split2 = \ t, u, v, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split2, zero, suc, rec =>
     split2 (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero suc rec)
          (u tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero suc rec)
          (v tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero suc rec)

zero2 : {g:_} -> Tm2 g Main.nat2
zero2 = \ tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split2, zero2, suc, rec => zero2

suc2 : {g:_} -> Tm2 g Main.nat2 -> Tm2 g Main.nat2
suc2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split2, zero2, suc2, rec =>
   suc2 (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero2 suc2 rec)

rec2 : {g:_}->{a:_} -> Tm2 g Main.nat2 -> Tm2 g (arr2 Main.nat2 (arr2 a a)) -> Tm2 g a -> Tm2 g a
rec2 = \ t, u, v, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split2, zero2, suc2, rec2 =>
     rec2 (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero2 suc2 rec2)
         (u tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero2 suc2 rec2)
         (v tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero2 suc2 rec2)

v02 : {g:_}->{a:_} -> Tm2 (snoc2 g a) a
v02 = var2 vz2

v12 : {g:_}->{a:_}->{b:_} -> Tm2 (snoc2 (snoc2 g a) b) a
v12 = var2 (vs2 vz2)

v22 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm2 (snoc2 (snoc2 (snoc2 g a) b) c) a
v22 = var2 (vs2 (vs2 vz2))

v32 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm2 (snoc2 (snoc2 (snoc2 (snoc2 g a) b) c) d) a
v32 = var2 (vs2 (vs2 (vs2 vz2)))

tbool2 : Ty2
tbool2 = sum2 top2 top2

ttrue2 : {g:_} -> Tm2 g Main.tbool2
ttrue2 = left2 tt2

tfalse2 : {g:_} -> Tm2 g Main.tbool2
tfalse2 = right2 tt2

ifthenelse2 : {g:_}->{a:_} -> Tm2 g (arr2 Main.tbool2 (arr2 a (arr2 a a)))
ifthenelse2 = lam2 (lam2 (lam2 (split2 v22 (lam2 v22) (lam2 v12))))

times42 : {g:_}->{a:_} -> Tm2 g (arr2 (arr2 a a) (arr2 a a))
times42  = lam2 (lam2 (app2 v12 (app2 v12 (app2 v12 (app2 v12 v02)))))

add2 : {g:_} -> Tm2 g (arr2 Main.nat2 (arr2 Main.nat2 Main.nat2))
add2 = lam2 (rec2 v02
       (lam2 (lam2 (lam2 (suc2 (app2 v12 v02)))))
       (lam2 v02))

mul2 : {g:_} -> Tm2 g (arr2 Main.nat2 (arr2 Main.nat2 Main.nat2))
mul2 = lam2 (rec2 v02
       (lam2 (lam2 (lam2 (app2 (app2 add2 (app2 v12 v02)) v02))))
       (lam2 zero2))

fact2 : {g:_} -> Tm2 g (arr2 Main.nat2 Main.nat2)
fact2 = lam2 (rec2 v02 (lam2 (lam2 (app2 (app2 mul2 (suc2 v12)) v02)))
                 (suc2 zero2))

Ty3 : Type
Ty3 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat3 : Ty3
nat3 = \ _, nat3, _, _, _, _, _ => nat3
top3 : Ty3
top3 = \ _, _, top3, _, _, _, _ => top3
bot3 : Ty3
bot3 = \ _, _, _, bot3, _, _, _ => bot3

arr3 : Ty3-> Ty3-> Ty3
arr3 = \ a, b, ty, nat3, top3, bot3, arr3, prod, sum =>
     arr3 (a ty nat3 top3 bot3 arr3 prod sum) (b ty nat3 top3 bot3 arr3 prod sum)

prod3 : Ty3-> Ty3-> Ty3
prod3 = \ a, b, ty, nat3, top3, bot3, arr3, prod3, sum =>
     prod3 (a ty nat3 top3 bot3 arr3 prod3 sum) (b ty nat3 top3 bot3 arr3 prod3 sum)

sum3 : Ty3-> Ty3-> Ty3
sum3 = \ a, b, ty, nat3, top3, bot3, arr3, prod3, sum3 =>
     sum3 (a ty nat3 top3 bot3 arr3 prod3 sum3) (b ty nat3 top3 bot3 arr3 prod3 sum3)

Con3 : Type
Con3 = (Con3 : Type)
 -> (nil  : Con3)
 -> (snoc : Con3 -> Ty3-> Con3)
 -> Con3

nil3 : Con3
nil3 = \ con, nil3, snoc => nil3

snoc3 : Con3 -> Ty3-> Con3
snoc3 = \ g, a, con, nil3, snoc3 => snoc3 (g con nil3 snoc3) a

Var3 : Con3 -> Ty3-> Type
Var3 = \ g, a =>
    (Var3 : Con3 -> Ty3-> Type)
 -> (vz  : {g:_}->{a:_} -> Var3 (snoc3 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var3 g a -> Var3 (snoc3 g b) a)
 -> Var3 g a

vz3 : {g:_}->{a:_} -> Var3 (snoc3 g a) a
vz3 = \ var, vz3, vs => vz3

vs3 : {g:_}->{b:_}->{a:_} -> Var3 g a -> Var3 (snoc3 g b) a
vs3 = \ x, var, vz3, vs3 => vs3 (x var vz3 vs3)

Tm3 : Con3 -> Ty3-> Type
Tm3 = \ g, a =>
    (Tm3    : Con3 -> Ty3-> Type)
 -> (var   : {g:_}->{a:_}-> Var3 g a -> Tm3 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm3 (snoc3 g a) b -> Tm3 g (arr3 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm3 g (arr3 a b) -> Tm3 g a -> Tm3 g b)
 -> (tt    : {g:_}-> Tm3 g top3)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm3 g a -> Tm3 g b -> Tm3 g (prod3 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm3 g (prod3 a b) -> Tm3 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm3 g (prod3 a b) -> Tm3 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm3 g a -> Tm3 g (sum3 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm3 g b -> Tm3 g (sum3 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm3 g (sum3 a b) -> Tm3 g (arr3 a c) -> Tm3 g (arr3 b c) -> Tm3 g c)
 -> (zero  : {g:_}-> Tm3 g nat3)
 -> (suc   : {g:_}-> Tm3 g nat3 -> Tm3 g nat3)
 -> (rec   : {g:_}->{a:_} -> Tm3 g nat3 -> Tm3 g (arr3 nat3 (arr3 a a)) -> Tm3 g a -> Tm3 g a)
 -> Tm3 g a

var3 : {g:_}->{a:_} -> Var3 g a -> Tm3 g a
var3 = \ x, tm, var3, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var3 x

lam3 : {g:_}->{a:_}->{b:_}-> Tm3 (snoc3 g a) b -> Tm3 g (arr3 a b)
lam3 = \ t, tm, var3, lam3, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam3 (t tm var3 lam3 app tt pair fst snd left right split zero suc rec)

app3 : {g:_}->{a:_}->{b:_} -> Tm3 g (arr3 a b) -> Tm3 g a -> Tm3 g b
app3 = \ t, u, tm, var3, lam3, app3, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app3 (t tm var3 lam3 app3 tt pair fst snd left right split zero suc rec)
         (u tm var3 lam3 app3 tt pair fst snd left right split zero suc rec)

tt3 : {g:_} -> Tm3 g Main.top3
tt3 = \ tm, var3, lam3, app3, tt3, pair, fst, snd, left, right, split, zero, suc, rec => tt3

pair3 : {g:_}->{a:_}->{b:_} -> Tm3 g a -> Tm3 g b -> Tm3 g (prod3 a b)
pair3 = \ t, u, tm, var3, lam3, app3, tt3, pair3, fst, snd, left, right, split, zero, suc, rec =>
     pair3 (t tm var3 lam3 app3 tt3 pair3 fst snd left right split zero suc rec)
          (u tm var3 lam3 app3 tt3 pair3 fst snd left right split zero suc rec)

fst3 : {g:_}->{a:_}->{b:_}-> Tm3 g (prod3 a b) -> Tm3 g a
fst3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd, left, right, split, zero, suc, rec =>
     fst3 (t tm var3 lam3 app3 tt3 pair3 fst3 snd left right split zero suc rec)

snd3 : {g:_}->{a:_}->{b:_} -> Tm3 g (prod3 a b) -> Tm3 g b
snd3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left, right, split, zero, suc, rec =>
     snd3 (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left right split zero suc rec)

left3 : {g:_}->{a:_}->{b:_} -> Tm3 g a -> Tm3 g (sum3 a b)
left3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right, split, zero, suc, rec =>
     left3 (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right split zero suc rec)

right3 : {g:_}->{a:_}->{b:_} -> Tm3 g b -> Tm3 g (sum3 a b)
right3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split, zero, suc, rec =>
     right3 (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split zero suc rec)

split3 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm3 g (sum3 a b) -> Tm3 g (arr3 a c) -> Tm3 g (arr3 b c) -> Tm3 g c
split3 = \ t, u, v, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split3, zero, suc, rec =>
     split3 (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero suc rec)
          (u tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero suc rec)
          (v tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero suc rec)

zero3 : {g:_} -> Tm3 g Main.nat3
zero3 = \ tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split3, zero3, suc, rec => zero3

suc3 : {g:_} -> Tm3 g Main.nat3 -> Tm3 g Main.nat3
suc3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split3, zero3, suc3, rec =>
   suc3 (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero3 suc3 rec)

rec3 : {g:_}->{a:_} -> Tm3 g Main.nat3 -> Tm3 g (arr3 Main.nat3 (arr3 a a)) -> Tm3 g a -> Tm3 g a
rec3 = \ t, u, v, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split3, zero3, suc3, rec3 =>
     rec3 (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero3 suc3 rec3)
         (u tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero3 suc3 rec3)
         (v tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero3 suc3 rec3)

v03 : {g:_}->{a:_} -> Tm3 (snoc3 g a) a
v03 = var3 vz3

v13 : {g:_}->{a:_}->{b:_} -> Tm3 (snoc3 (snoc3 g a) b) a
v13 = var3 (vs3 vz3)

v23 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm3 (snoc3 (snoc3 (snoc3 g a) b) c) a
v23 = var3 (vs3 (vs3 vz3))

v33 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm3 (snoc3 (snoc3 (snoc3 (snoc3 g a) b) c) d) a
v33 = var3 (vs3 (vs3 (vs3 vz3)))

tbool3 : Ty3
tbool3 = sum3 top3 top3

ttrue3 : {g:_} -> Tm3 g Main.tbool3
ttrue3 = left3 tt3

tfalse3 : {g:_} -> Tm3 g Main.tbool3
tfalse3 = right3 tt3

ifthenelse3 : {g:_}->{a:_} -> Tm3 g (arr3 Main.tbool3 (arr3 a (arr3 a a)))
ifthenelse3 = lam3 (lam3 (lam3 (split3 v23 (lam3 v23) (lam3 v13))))

times43 : {g:_}->{a:_} -> Tm3 g (arr3 (arr3 a a) (arr3 a a))
times43  = lam3 (lam3 (app3 v13 (app3 v13 (app3 v13 (app3 v13 v03)))))

add3 : {g:_} -> Tm3 g (arr3 Main.nat3 (arr3 Main.nat3 Main.nat3))
add3 = lam3 (rec3 v03
       (lam3 (lam3 (lam3 (suc3 (app3 v13 v03)))))
       (lam3 v03))

mul3 : {g:_} -> Tm3 g (arr3 Main.nat3 (arr3 Main.nat3 Main.nat3))
mul3 = lam3 (rec3 v03
       (lam3 (lam3 (lam3 (app3 (app3 add3 (app3 v13 v03)) v03))))
       (lam3 zero3))

fact3 : {g:_} -> Tm3 g (arr3 Main.nat3 Main.nat3)
fact3 = lam3 (rec3 v03 (lam3 (lam3 (app3 (app3 mul3 (suc3 v13)) v03)))
                 (suc3 zero3))

Ty4 : Type
Ty4 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat4 : Ty4
nat4 = \ _, nat4, _, _, _, _, _ => nat4
top4 : Ty4
top4 = \ _, _, top4, _, _, _, _ => top4
bot4 : Ty4
bot4 = \ _, _, _, bot4, _, _, _ => bot4

arr4 : Ty4-> Ty4-> Ty4
arr4 = \ a, b, ty, nat4, top4, bot4, arr4, prod, sum =>
     arr4 (a ty nat4 top4 bot4 arr4 prod sum) (b ty nat4 top4 bot4 arr4 prod sum)

prod4 : Ty4-> Ty4-> Ty4
prod4 = \ a, b, ty, nat4, top4, bot4, arr4, prod4, sum =>
     prod4 (a ty nat4 top4 bot4 arr4 prod4 sum) (b ty nat4 top4 bot4 arr4 prod4 sum)

sum4 : Ty4-> Ty4-> Ty4
sum4 = \ a, b, ty, nat4, top4, bot4, arr4, prod4, sum4 =>
     sum4 (a ty nat4 top4 bot4 arr4 prod4 sum4) (b ty nat4 top4 bot4 arr4 prod4 sum4)

Con4 : Type
Con4 = (Con4 : Type)
 -> (nil  : Con4)
 -> (snoc : Con4 -> Ty4-> Con4)
 -> Con4

nil4 : Con4
nil4 = \ con, nil4, snoc => nil4

snoc4 : Con4 -> Ty4-> Con4
snoc4 = \ g, a, con, nil4, snoc4 => snoc4 (g con nil4 snoc4) a

Var4 : Con4 -> Ty4-> Type
Var4 = \ g, a =>
    (Var4 : Con4 -> Ty4-> Type)
 -> (vz  : {g:_}->{a:_} -> Var4 (snoc4 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var4 g a -> Var4 (snoc4 g b) a)
 -> Var4 g a

vz4 : {g:_}->{a:_} -> Var4 (snoc4 g a) a
vz4 = \ var, vz4, vs => vz4

vs4 : {g:_}->{b:_}->{a:_} -> Var4 g a -> Var4 (snoc4 g b) a
vs4 = \ x, var, vz4, vs4 => vs4 (x var vz4 vs4)

Tm4 : Con4 -> Ty4-> Type
Tm4 = \ g, a =>
    (Tm4    : Con4 -> Ty4-> Type)
 -> (var   : {g:_}->{a:_}-> Var4 g a -> Tm4 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm4 (snoc4 g a) b -> Tm4 g (arr4 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm4 g (arr4 a b) -> Tm4 g a -> Tm4 g b)
 -> (tt    : {g:_}-> Tm4 g top4)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm4 g a -> Tm4 g b -> Tm4 g (prod4 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm4 g (prod4 a b) -> Tm4 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm4 g (prod4 a b) -> Tm4 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm4 g a -> Tm4 g (sum4 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm4 g b -> Tm4 g (sum4 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm4 g (sum4 a b) -> Tm4 g (arr4 a c) -> Tm4 g (arr4 b c) -> Tm4 g c)
 -> (zero  : {g:_}-> Tm4 g nat4)
 -> (suc   : {g:_}-> Tm4 g nat4 -> Tm4 g nat4)
 -> (rec   : {g:_}->{a:_} -> Tm4 g nat4 -> Tm4 g (arr4 nat4 (arr4 a a)) -> Tm4 g a -> Tm4 g a)
 -> Tm4 g a

var4 : {g:_}->{a:_} -> Var4 g a -> Tm4 g a
var4 = \ x, tm, var4, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var4 x

lam4 : {g:_}->{a:_}->{b:_}-> Tm4 (snoc4 g a) b -> Tm4 g (arr4 a b)
lam4 = \ t, tm, var4, lam4, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam4 (t tm var4 lam4 app tt pair fst snd left right split zero suc rec)

app4 : {g:_}->{a:_}->{b:_} -> Tm4 g (arr4 a b) -> Tm4 g a -> Tm4 g b
app4 = \ t, u, tm, var4, lam4, app4, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app4 (t tm var4 lam4 app4 tt pair fst snd left right split zero suc rec)
         (u tm var4 lam4 app4 tt pair fst snd left right split zero suc rec)

tt4 : {g:_} -> Tm4 g Main.top4
tt4 = \ tm, var4, lam4, app4, tt4, pair, fst, snd, left, right, split, zero, suc, rec => tt4

pair4 : {g:_}->{a:_}->{b:_} -> Tm4 g a -> Tm4 g b -> Tm4 g (prod4 a b)
pair4 = \ t, u, tm, var4, lam4, app4, tt4, pair4, fst, snd, left, right, split, zero, suc, rec =>
     pair4 (t tm var4 lam4 app4 tt4 pair4 fst snd left right split zero suc rec)
          (u tm var4 lam4 app4 tt4 pair4 fst snd left right split zero suc rec)

fst4 : {g:_}->{a:_}->{b:_}-> Tm4 g (prod4 a b) -> Tm4 g a
fst4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd, left, right, split, zero, suc, rec =>
     fst4 (t tm var4 lam4 app4 tt4 pair4 fst4 snd left right split zero suc rec)

snd4 : {g:_}->{a:_}->{b:_} -> Tm4 g (prod4 a b) -> Tm4 g b
snd4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left, right, split, zero, suc, rec =>
     snd4 (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left right split zero suc rec)

left4 : {g:_}->{a:_}->{b:_} -> Tm4 g a -> Tm4 g (sum4 a b)
left4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right, split, zero, suc, rec =>
     left4 (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right split zero suc rec)

right4 : {g:_}->{a:_}->{b:_} -> Tm4 g b -> Tm4 g (sum4 a b)
right4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split, zero, suc, rec =>
     right4 (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split zero suc rec)

split4 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm4 g (sum4 a b) -> Tm4 g (arr4 a c) -> Tm4 g (arr4 b c) -> Tm4 g c
split4 = \ t, u, v, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split4, zero, suc, rec =>
     split4 (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero suc rec)
          (u tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero suc rec)
          (v tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero suc rec)

zero4 : {g:_} -> Tm4 g Main.nat4
zero4 = \ tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split4, zero4, suc, rec => zero4

suc4 : {g:_} -> Tm4 g Main.nat4 -> Tm4 g Main.nat4
suc4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split4, zero4, suc4, rec =>
   suc4 (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero4 suc4 rec)

rec4 : {g:_}->{a:_} -> Tm4 g Main.nat4 -> Tm4 g (arr4 Main.nat4 (arr4 a a)) -> Tm4 g a -> Tm4 g a
rec4 = \ t, u, v, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split4, zero4, suc4, rec4 =>
     rec4 (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero4 suc4 rec4)
         (u tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero4 suc4 rec4)
         (v tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero4 suc4 rec4)

v04 : {g:_}->{a:_} -> Tm4 (snoc4 g a) a
v04 = var4 vz4

v14 : {g:_}->{a:_}->{b:_} -> Tm4 (snoc4 (snoc4 g a) b) a
v14 = var4 (vs4 vz4)

v24 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm4 (snoc4 (snoc4 (snoc4 g a) b) c) a
v24 = var4 (vs4 (vs4 vz4))

v34 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm4 (snoc4 (snoc4 (snoc4 (snoc4 g a) b) c) d) a
v34 = var4 (vs4 (vs4 (vs4 vz4)))

tbool4 : Ty4
tbool4 = sum4 top4 top4

ttrue4 : {g:_} -> Tm4 g Main.tbool4
ttrue4 = left4 tt4

tfalse4 : {g:_} -> Tm4 g Main.tbool4
tfalse4 = right4 tt4

ifthenelse4 : {g:_}->{a:_} -> Tm4 g (arr4 Main.tbool4 (arr4 a (arr4 a a)))
ifthenelse4 = lam4 (lam4 (lam4 (split4 v24 (lam4 v24) (lam4 v14))))

times44 : {g:_}->{a:_} -> Tm4 g (arr4 (arr4 a a) (arr4 a a))
times44  = lam4 (lam4 (app4 v14 (app4 v14 (app4 v14 (app4 v14 v04)))))

add4 : {g:_} -> Tm4 g (arr4 Main.nat4 (arr4 Main.nat4 Main.nat4))
add4 = lam4 (rec4 v04
       (lam4 (lam4 (lam4 (suc4 (app4 v14 v04)))))
       (lam4 v04))

mul4 : {g:_} -> Tm4 g (arr4 Main.nat4 (arr4 Main.nat4 Main.nat4))
mul4 = lam4 (rec4 v04
       (lam4 (lam4 (lam4 (app4 (app4 add4 (app4 v14 v04)) v04))))
       (lam4 zero4))

fact4 : {g:_} -> Tm4 g (arr4 Main.nat4 Main.nat4)
fact4 = lam4 (rec4 v04 (lam4 (lam4 (app4 (app4 mul4 (suc4 v14)) v04)))
                 (suc4 zero4))

Ty5 : Type
Ty5 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat5 : Ty5
nat5 = \ _, nat5, _, _, _, _, _ => nat5
top5 : Ty5
top5 = \ _, _, top5, _, _, _, _ => top5
bot5 : Ty5
bot5 = \ _, _, _, bot5, _, _, _ => bot5

arr5 : Ty5-> Ty5-> Ty5
arr5 = \ a, b, ty, nat5, top5, bot5, arr5, prod, sum =>
     arr5 (a ty nat5 top5 bot5 arr5 prod sum) (b ty nat5 top5 bot5 arr5 prod sum)

prod5 : Ty5-> Ty5-> Ty5
prod5 = \ a, b, ty, nat5, top5, bot5, arr5, prod5, sum =>
     prod5 (a ty nat5 top5 bot5 arr5 prod5 sum) (b ty nat5 top5 bot5 arr5 prod5 sum)

sum5 : Ty5-> Ty5-> Ty5
sum5 = \ a, b, ty, nat5, top5, bot5, arr5, prod5, sum5 =>
     sum5 (a ty nat5 top5 bot5 arr5 prod5 sum5) (b ty nat5 top5 bot5 arr5 prod5 sum5)

Con5 : Type
Con5 = (Con5 : Type)
 -> (nil  : Con5)
 -> (snoc : Con5 -> Ty5-> Con5)
 -> Con5

nil5 : Con5
nil5 = \ con, nil5, snoc => nil5

snoc5 : Con5 -> Ty5-> Con5
snoc5 = \ g, a, con, nil5, snoc5 => snoc5 (g con nil5 snoc5) a

Var5 : Con5 -> Ty5-> Type
Var5 = \ g, a =>
    (Var5 : Con5 -> Ty5-> Type)
 -> (vz  : {g:_}->{a:_} -> Var5 (snoc5 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var5 g a -> Var5 (snoc5 g b) a)
 -> Var5 g a

vz5 : {g:_}->{a:_} -> Var5 (snoc5 g a) a
vz5 = \ var, vz5, vs => vz5

vs5 : {g:_}->{b:_}->{a:_} -> Var5 g a -> Var5 (snoc5 g b) a
vs5 = \ x, var, vz5, vs5 => vs5 (x var vz5 vs5)

Tm5 : Con5 -> Ty5-> Type
Tm5 = \ g, a =>
    (Tm5    : Con5 -> Ty5-> Type)
 -> (var   : {g:_}->{a:_}-> Var5 g a -> Tm5 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm5 (snoc5 g a) b -> Tm5 g (arr5 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm5 g (arr5 a b) -> Tm5 g a -> Tm5 g b)
 -> (tt    : {g:_}-> Tm5 g top5)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm5 g a -> Tm5 g b -> Tm5 g (prod5 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm5 g (prod5 a b) -> Tm5 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm5 g (prod5 a b) -> Tm5 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm5 g a -> Tm5 g (sum5 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm5 g b -> Tm5 g (sum5 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm5 g (sum5 a b) -> Tm5 g (arr5 a c) -> Tm5 g (arr5 b c) -> Tm5 g c)
 -> (zero  : {g:_}-> Tm5 g nat5)
 -> (suc   : {g:_}-> Tm5 g nat5 -> Tm5 g nat5)
 -> (rec   : {g:_}->{a:_} -> Tm5 g nat5 -> Tm5 g (arr5 nat5 (arr5 a a)) -> Tm5 g a -> Tm5 g a)
 -> Tm5 g a

var5 : {g:_}->{a:_} -> Var5 g a -> Tm5 g a
var5 = \ x, tm, var5, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var5 x

lam5 : {g:_}->{a:_}->{b:_}-> Tm5 (snoc5 g a) b -> Tm5 g (arr5 a b)
lam5 = \ t, tm, var5, lam5, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam5 (t tm var5 lam5 app tt pair fst snd left right split zero suc rec)

app5 : {g:_}->{a:_}->{b:_} -> Tm5 g (arr5 a b) -> Tm5 g a -> Tm5 g b
app5 = \ t, u, tm, var5, lam5, app5, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app5 (t tm var5 lam5 app5 tt pair fst snd left right split zero suc rec)
         (u tm var5 lam5 app5 tt pair fst snd left right split zero suc rec)

tt5 : {g:_} -> Tm5 g Main.top5
tt5 = \ tm, var5, lam5, app5, tt5, pair, fst, snd, left, right, split, zero, suc, rec => tt5

pair5 : {g:_}->{a:_}->{b:_} -> Tm5 g a -> Tm5 g b -> Tm5 g (prod5 a b)
pair5 = \ t, u, tm, var5, lam5, app5, tt5, pair5, fst, snd, left, right, split, zero, suc, rec =>
     pair5 (t tm var5 lam5 app5 tt5 pair5 fst snd left right split zero suc rec)
          (u tm var5 lam5 app5 tt5 pair5 fst snd left right split zero suc rec)

fst5 : {g:_}->{a:_}->{b:_}-> Tm5 g (prod5 a b) -> Tm5 g a
fst5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd, left, right, split, zero, suc, rec =>
     fst5 (t tm var5 lam5 app5 tt5 pair5 fst5 snd left right split zero suc rec)

snd5 : {g:_}->{a:_}->{b:_} -> Tm5 g (prod5 a b) -> Tm5 g b
snd5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left, right, split, zero, suc, rec =>
     snd5 (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left right split zero suc rec)

left5 : {g:_}->{a:_}->{b:_} -> Tm5 g a -> Tm5 g (sum5 a b)
left5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right, split, zero, suc, rec =>
     left5 (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right split zero suc rec)

right5 : {g:_}->{a:_}->{b:_} -> Tm5 g b -> Tm5 g (sum5 a b)
right5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split, zero, suc, rec =>
     right5 (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split zero suc rec)

split5 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm5 g (sum5 a b) -> Tm5 g (arr5 a c) -> Tm5 g (arr5 b c) -> Tm5 g c
split5 = \ t, u, v, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split5, zero, suc, rec =>
     split5 (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero suc rec)
          (u tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero suc rec)
          (v tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero suc rec)

zero5 : {g:_} -> Tm5 g Main.nat5
zero5 = \ tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split5, zero5, suc, rec => zero5

suc5 : {g:_} -> Tm5 g Main.nat5 -> Tm5 g Main.nat5
suc5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split5, zero5, suc5, rec =>
   suc5 (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero5 suc5 rec)

rec5 : {g:_}->{a:_} -> Tm5 g Main.nat5 -> Tm5 g (arr5 Main.nat5 (arr5 a a)) -> Tm5 g a -> Tm5 g a
rec5 = \ t, u, v, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split5, zero5, suc5, rec5 =>
     rec5 (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero5 suc5 rec5)
         (u tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero5 suc5 rec5)
         (v tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero5 suc5 rec5)

v05 : {g:_}->{a:_} -> Tm5 (snoc5 g a) a
v05 = var5 vz5

v15 : {g:_}->{a:_}->{b:_} -> Tm5 (snoc5 (snoc5 g a) b) a
v15 = var5 (vs5 vz5)

v25 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm5 (snoc5 (snoc5 (snoc5 g a) b) c) a
v25 = var5 (vs5 (vs5 vz5))

v35 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm5 (snoc5 (snoc5 (snoc5 (snoc5 g a) b) c) d) a
v35 = var5 (vs5 (vs5 (vs5 vz5)))

tbool5 : Ty5
tbool5 = sum5 top5 top5

ttrue5 : {g:_} -> Tm5 g Main.tbool5
ttrue5 = left5 tt5

tfalse5 : {g:_} -> Tm5 g Main.tbool5
tfalse5 = right5 tt5

ifthenelse5 : {g:_}->{a:_} -> Tm5 g (arr5 Main.tbool5 (arr5 a (arr5 a a)))
ifthenelse5 = lam5 (lam5 (lam5 (split5 v25 (lam5 v25) (lam5 v15))))

times45 : {g:_}->{a:_} -> Tm5 g (arr5 (arr5 a a) (arr5 a a))
times45  = lam5 (lam5 (app5 v15 (app5 v15 (app5 v15 (app5 v15 v05)))))

add5 : {g:_} -> Tm5 g (arr5 Main.nat5 (arr5 Main.nat5 Main.nat5))
add5 = lam5 (rec5 v05
       (lam5 (lam5 (lam5 (suc5 (app5 v15 v05)))))
       (lam5 v05))

mul5 : {g:_} -> Tm5 g (arr5 Main.nat5 (arr5 Main.nat5 Main.nat5))
mul5 = lam5 (rec5 v05
       (lam5 (lam5 (lam5 (app5 (app5 add5 (app5 v15 v05)) v05))))
       (lam5 zero5))

fact5 : {g:_} -> Tm5 g (arr5 Main.nat5 Main.nat5)
fact5 = lam5 (rec5 v05 (lam5 (lam5 (app5 (app5 mul5 (suc5 v15)) v05)))
                 (suc5 zero5))

Ty6 : Type
Ty6 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat6 : Ty6
nat6 = \ _, nat6, _, _, _, _, _ => nat6
top6 : Ty6
top6 = \ _, _, top6, _, _, _, _ => top6
bot6 : Ty6
bot6 = \ _, _, _, bot6, _, _, _ => bot6

arr6 : Ty6-> Ty6-> Ty6
arr6 = \ a, b, ty, nat6, top6, bot6, arr6, prod, sum =>
     arr6 (a ty nat6 top6 bot6 arr6 prod sum) (b ty nat6 top6 bot6 arr6 prod sum)

prod6 : Ty6-> Ty6-> Ty6
prod6 = \ a, b, ty, nat6, top6, bot6, arr6, prod6, sum =>
     prod6 (a ty nat6 top6 bot6 arr6 prod6 sum) (b ty nat6 top6 bot6 arr6 prod6 sum)

sum6 : Ty6-> Ty6-> Ty6
sum6 = \ a, b, ty, nat6, top6, bot6, arr6, prod6, sum6 =>
     sum6 (a ty nat6 top6 bot6 arr6 prod6 sum6) (b ty nat6 top6 bot6 arr6 prod6 sum6)

Con6 : Type
Con6 = (Con6 : Type)
 -> (nil  : Con6)
 -> (snoc : Con6 -> Ty6-> Con6)
 -> Con6

nil6 : Con6
nil6 = \ con, nil6, snoc => nil6

snoc6 : Con6 -> Ty6-> Con6
snoc6 = \ g, a, con, nil6, snoc6 => snoc6 (g con nil6 snoc6) a

Var6 : Con6 -> Ty6-> Type
Var6 = \ g, a =>
    (Var6 : Con6 -> Ty6-> Type)
 -> (vz  : {g:_}->{a:_} -> Var6 (snoc6 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var6 g a -> Var6 (snoc6 g b) a)
 -> Var6 g a

vz6 : {g:_}->{a:_} -> Var6 (snoc6 g a) a
vz6 = \ var, vz6, vs => vz6

vs6 : {g:_}->{b:_}->{a:_} -> Var6 g a -> Var6 (snoc6 g b) a
vs6 = \ x, var, vz6, vs6 => vs6 (x var vz6 vs6)

Tm6 : Con6 -> Ty6-> Type
Tm6 = \ g, a =>
    (Tm6    : Con6 -> Ty6-> Type)
 -> (var   : {g:_}->{a:_}-> Var6 g a -> Tm6 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm6 (snoc6 g a) b -> Tm6 g (arr6 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm6 g (arr6 a b) -> Tm6 g a -> Tm6 g b)
 -> (tt    : {g:_}-> Tm6 g top6)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm6 g a -> Tm6 g b -> Tm6 g (prod6 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm6 g (prod6 a b) -> Tm6 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm6 g (prod6 a b) -> Tm6 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm6 g a -> Tm6 g (sum6 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm6 g b -> Tm6 g (sum6 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm6 g (sum6 a b) -> Tm6 g (arr6 a c) -> Tm6 g (arr6 b c) -> Tm6 g c)
 -> (zero  : {g:_}-> Tm6 g nat6)
 -> (suc   : {g:_}-> Tm6 g nat6 -> Tm6 g nat6)
 -> (rec   : {g:_}->{a:_} -> Tm6 g nat6 -> Tm6 g (arr6 nat6 (arr6 a a)) -> Tm6 g a -> Tm6 g a)
 -> Tm6 g a

var6 : {g:_}->{a:_} -> Var6 g a -> Tm6 g a
var6 = \ x, tm, var6, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var6 x

lam6 : {g:_}->{a:_}->{b:_}-> Tm6 (snoc6 g a) b -> Tm6 g (arr6 a b)
lam6 = \ t, tm, var6, lam6, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam6 (t tm var6 lam6 app tt pair fst snd left right split zero suc rec)

app6 : {g:_}->{a:_}->{b:_} -> Tm6 g (arr6 a b) -> Tm6 g a -> Tm6 g b
app6 = \ t, u, tm, var6, lam6, app6, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app6 (t tm var6 lam6 app6 tt pair fst snd left right split zero suc rec)
         (u tm var6 lam6 app6 tt pair fst snd left right split zero suc rec)

tt6 : {g:_} -> Tm6 g Main.top6
tt6 = \ tm, var6, lam6, app6, tt6, pair, fst, snd, left, right, split, zero, suc, rec => tt6

pair6 : {g:_}->{a:_}->{b:_} -> Tm6 g a -> Tm6 g b -> Tm6 g (prod6 a b)
pair6 = \ t, u, tm, var6, lam6, app6, tt6, pair6, fst, snd, left, right, split, zero, suc, rec =>
     pair6 (t tm var6 lam6 app6 tt6 pair6 fst snd left right split zero suc rec)
          (u tm var6 lam6 app6 tt6 pair6 fst snd left right split zero suc rec)

fst6 : {g:_}->{a:_}->{b:_}-> Tm6 g (prod6 a b) -> Tm6 g a
fst6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd, left, right, split, zero, suc, rec =>
     fst6 (t tm var6 lam6 app6 tt6 pair6 fst6 snd left right split zero suc rec)

snd6 : {g:_}->{a:_}->{b:_} -> Tm6 g (prod6 a b) -> Tm6 g b
snd6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left, right, split, zero, suc, rec =>
     snd6 (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left right split zero suc rec)

left6 : {g:_}->{a:_}->{b:_} -> Tm6 g a -> Tm6 g (sum6 a b)
left6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right, split, zero, suc, rec =>
     left6 (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right split zero suc rec)

right6 : {g:_}->{a:_}->{b:_} -> Tm6 g b -> Tm6 g (sum6 a b)
right6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split, zero, suc, rec =>
     right6 (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split zero suc rec)

split6 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm6 g (sum6 a b) -> Tm6 g (arr6 a c) -> Tm6 g (arr6 b c) -> Tm6 g c
split6 = \ t, u, v, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split6, zero, suc, rec =>
     split6 (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero suc rec)
          (u tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero suc rec)
          (v tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero suc rec)

zero6 : {g:_} -> Tm6 g Main.nat6
zero6 = \ tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split6, zero6, suc, rec => zero6

suc6 : {g:_} -> Tm6 g Main.nat6 -> Tm6 g Main.nat6
suc6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split6, zero6, suc6, rec =>
   suc6 (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero6 suc6 rec)

rec6 : {g:_}->{a:_} -> Tm6 g Main.nat6 -> Tm6 g (arr6 Main.nat6 (arr6 a a)) -> Tm6 g a -> Tm6 g a
rec6 = \ t, u, v, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split6, zero6, suc6, rec6 =>
     rec6 (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero6 suc6 rec6)
         (u tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero6 suc6 rec6)
         (v tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero6 suc6 rec6)

v06 : {g:_}->{a:_} -> Tm6 (snoc6 g a) a
v06 = var6 vz6

v16 : {g:_}->{a:_}->{b:_} -> Tm6 (snoc6 (snoc6 g a) b) a
v16 = var6 (vs6 vz6)

v26 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm6 (snoc6 (snoc6 (snoc6 g a) b) c) a
v26 = var6 (vs6 (vs6 vz6))

v36 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm6 (snoc6 (snoc6 (snoc6 (snoc6 g a) b) c) d) a
v36 = var6 (vs6 (vs6 (vs6 vz6)))

tbool6 : Ty6
tbool6 = sum6 top6 top6

ttrue6 : {g:_} -> Tm6 g Main.tbool6
ttrue6 = left6 tt6

tfalse6 : {g:_} -> Tm6 g Main.tbool6
tfalse6 = right6 tt6

ifthenelse6 : {g:_}->{a:_} -> Tm6 g (arr6 Main.tbool6 (arr6 a (arr6 a a)))
ifthenelse6 = lam6 (lam6 (lam6 (split6 v26 (lam6 v26) (lam6 v16))))

times46 : {g:_}->{a:_} -> Tm6 g (arr6 (arr6 a a) (arr6 a a))
times46  = lam6 (lam6 (app6 v16 (app6 v16 (app6 v16 (app6 v16 v06)))))

add6 : {g:_} -> Tm6 g (arr6 Main.nat6 (arr6 Main.nat6 Main.nat6))
add6 = lam6 (rec6 v06
       (lam6 (lam6 (lam6 (suc6 (app6 v16 v06)))))
       (lam6 v06))

mul6 : {g:_} -> Tm6 g (arr6 Main.nat6 (arr6 Main.nat6 Main.nat6))
mul6 = lam6 (rec6 v06
       (lam6 (lam6 (lam6 (app6 (app6 add6 (app6 v16 v06)) v06))))
       (lam6 zero6))

fact6 : {g:_} -> Tm6 g (arr6 Main.nat6 Main.nat6)
fact6 = lam6 (rec6 v06 (lam6 (lam6 (app6 (app6 mul6 (suc6 v16)) v06)))
                 (suc6 zero6))

Ty7 : Type
Ty7 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat7 : Ty7
nat7 = \ _, nat7, _, _, _, _, _ => nat7
top7 : Ty7
top7 = \ _, _, top7, _, _, _, _ => top7
bot7 : Ty7
bot7 = \ _, _, _, bot7, _, _, _ => bot7

arr7 : Ty7-> Ty7-> Ty7
arr7 = \ a, b, ty, nat7, top7, bot7, arr7, prod, sum =>
     arr7 (a ty nat7 top7 bot7 arr7 prod sum) (b ty nat7 top7 bot7 arr7 prod sum)

prod7 : Ty7-> Ty7-> Ty7
prod7 = \ a, b, ty, nat7, top7, bot7, arr7, prod7, sum =>
     prod7 (a ty nat7 top7 bot7 arr7 prod7 sum) (b ty nat7 top7 bot7 arr7 prod7 sum)

sum7 : Ty7-> Ty7-> Ty7
sum7 = \ a, b, ty, nat7, top7, bot7, arr7, prod7, sum7 =>
     sum7 (a ty nat7 top7 bot7 arr7 prod7 sum7) (b ty nat7 top7 bot7 arr7 prod7 sum7)

Con7 : Type
Con7 = (Con7 : Type)
 -> (nil  : Con7)
 -> (snoc : Con7 -> Ty7-> Con7)
 -> Con7

nil7 : Con7
nil7 = \ con, nil7, snoc => nil7

snoc7 : Con7 -> Ty7-> Con7
snoc7 = \ g, a, con, nil7, snoc7 => snoc7 (g con nil7 snoc7) a

Var7 : Con7 -> Ty7-> Type
Var7 = \ g, a =>
    (Var7 : Con7 -> Ty7-> Type)
 -> (vz  : {g:_}->{a:_} -> Var7 (snoc7 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var7 g a -> Var7 (snoc7 g b) a)
 -> Var7 g a

vz7 : {g:_}->{a:_} -> Var7 (snoc7 g a) a
vz7 = \ var, vz7, vs => vz7

vs7 : {g:_}->{b:_}->{a:_} -> Var7 g a -> Var7 (snoc7 g b) a
vs7 = \ x, var, vz7, vs7 => vs7 (x var vz7 vs7)

Tm7 : Con7 -> Ty7-> Type
Tm7 = \ g, a =>
    (Tm7    : Con7 -> Ty7-> Type)
 -> (var   : {g:_}->{a:_}-> Var7 g a -> Tm7 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm7 (snoc7 g a) b -> Tm7 g (arr7 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm7 g (arr7 a b) -> Tm7 g a -> Tm7 g b)
 -> (tt    : {g:_}-> Tm7 g top7)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm7 g a -> Tm7 g b -> Tm7 g (prod7 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm7 g (prod7 a b) -> Tm7 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm7 g (prod7 a b) -> Tm7 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm7 g a -> Tm7 g (sum7 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm7 g b -> Tm7 g (sum7 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm7 g (sum7 a b) -> Tm7 g (arr7 a c) -> Tm7 g (arr7 b c) -> Tm7 g c)
 -> (zero  : {g:_}-> Tm7 g nat7)
 -> (suc   : {g:_}-> Tm7 g nat7 -> Tm7 g nat7)
 -> (rec   : {g:_}->{a:_} -> Tm7 g nat7 -> Tm7 g (arr7 nat7 (arr7 a a)) -> Tm7 g a -> Tm7 g a)
 -> Tm7 g a

var7 : {g:_}->{a:_} -> Var7 g a -> Tm7 g a
var7 = \ x, tm, var7, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var7 x

lam7 : {g:_}->{a:_}->{b:_}-> Tm7 (snoc7 g a) b -> Tm7 g (arr7 a b)
lam7 = \ t, tm, var7, lam7, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam7 (t tm var7 lam7 app tt pair fst snd left right split zero suc rec)

app7 : {g:_}->{a:_}->{b:_} -> Tm7 g (arr7 a b) -> Tm7 g a -> Tm7 g b
app7 = \ t, u, tm, var7, lam7, app7, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app7 (t tm var7 lam7 app7 tt pair fst snd left right split zero suc rec)
         (u tm var7 lam7 app7 tt pair fst snd left right split zero suc rec)

tt7 : {g:_} -> Tm7 g Main.top7
tt7 = \ tm, var7, lam7, app7, tt7, pair, fst, snd, left, right, split, zero, suc, rec => tt7

pair7 : {g:_}->{a:_}->{b:_} -> Tm7 g a -> Tm7 g b -> Tm7 g (prod7 a b)
pair7 = \ t, u, tm, var7, lam7, app7, tt7, pair7, fst, snd, left, right, split, zero, suc, rec =>
     pair7 (t tm var7 lam7 app7 tt7 pair7 fst snd left right split zero suc rec)
          (u tm var7 lam7 app7 tt7 pair7 fst snd left right split zero suc rec)

fst7 : {g:_}->{a:_}->{b:_}-> Tm7 g (prod7 a b) -> Tm7 g a
fst7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd, left, right, split, zero, suc, rec =>
     fst7 (t tm var7 lam7 app7 tt7 pair7 fst7 snd left right split zero suc rec)

snd7 : {g:_}->{a:_}->{b:_} -> Tm7 g (prod7 a b) -> Tm7 g b
snd7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left, right, split, zero, suc, rec =>
     snd7 (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left right split zero suc rec)

left7 : {g:_}->{a:_}->{b:_} -> Tm7 g a -> Tm7 g (sum7 a b)
left7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right, split, zero, suc, rec =>
     left7 (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right split zero suc rec)

right7 : {g:_}->{a:_}->{b:_} -> Tm7 g b -> Tm7 g (sum7 a b)
right7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split, zero, suc, rec =>
     right7 (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split zero suc rec)

split7 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm7 g (sum7 a b) -> Tm7 g (arr7 a c) -> Tm7 g (arr7 b c) -> Tm7 g c
split7 = \ t, u, v, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split7, zero, suc, rec =>
     split7 (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero suc rec)
          (u tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero suc rec)
          (v tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero suc rec)

zero7 : {g:_} -> Tm7 g Main.nat7
zero7 = \ tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split7, zero7, suc, rec => zero7

suc7 : {g:_} -> Tm7 g Main.nat7 -> Tm7 g Main.nat7
suc7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split7, zero7, suc7, rec =>
   suc7 (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero7 suc7 rec)

rec7 : {g:_}->{a:_} -> Tm7 g Main.nat7 -> Tm7 g (arr7 Main.nat7 (arr7 a a)) -> Tm7 g a -> Tm7 g a
rec7 = \ t, u, v, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split7, zero7, suc7, rec7 =>
     rec7 (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero7 suc7 rec7)
         (u tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero7 suc7 rec7)
         (v tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero7 suc7 rec7)

v07 : {g:_}->{a:_} -> Tm7 (snoc7 g a) a
v07 = var7 vz7

v17 : {g:_}->{a:_}->{b:_} -> Tm7 (snoc7 (snoc7 g a) b) a
v17 = var7 (vs7 vz7)

v27 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm7 (snoc7 (snoc7 (snoc7 g a) b) c) a
v27 = var7 (vs7 (vs7 vz7))

v37 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm7 (snoc7 (snoc7 (snoc7 (snoc7 g a) b) c) d) a
v37 = var7 (vs7 (vs7 (vs7 vz7)))

tbool7 : Ty7
tbool7 = sum7 top7 top7

ttrue7 : {g:_} -> Tm7 g Main.tbool7
ttrue7 = left7 tt7

tfalse7 : {g:_} -> Tm7 g Main.tbool7
tfalse7 = right7 tt7

ifthenelse7 : {g:_}->{a:_} -> Tm7 g (arr7 Main.tbool7 (arr7 a (arr7 a a)))
ifthenelse7 = lam7 (lam7 (lam7 (split7 v27 (lam7 v27) (lam7 v17))))

times47 : {g:_}->{a:_} -> Tm7 g (arr7 (arr7 a a) (arr7 a a))
times47  = lam7 (lam7 (app7 v17 (app7 v17 (app7 v17 (app7 v17 v07)))))

add7 : {g:_} -> Tm7 g (arr7 Main.nat7 (arr7 Main.nat7 Main.nat7))
add7 = lam7 (rec7 v07
       (lam7 (lam7 (lam7 (suc7 (app7 v17 v07)))))
       (lam7 v07))

mul7 : {g:_} -> Tm7 g (arr7 Main.nat7 (arr7 Main.nat7 Main.nat7))
mul7 = lam7 (rec7 v07
       (lam7 (lam7 (lam7 (app7 (app7 add7 (app7 v17 v07)) v07))))
       (lam7 zero7))

fact7 : {g:_} -> Tm7 g (arr7 Main.nat7 Main.nat7)
fact7 = lam7 (rec7 v07 (lam7 (lam7 (app7 (app7 mul7 (suc7 v17)) v07)))
                 (suc7 zero7))

Ty8 : Type
Ty8 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat8 : Ty8
nat8 = \ _, nat8, _, _, _, _, _ => nat8
top8 : Ty8
top8 = \ _, _, top8, _, _, _, _ => top8
bot8 : Ty8
bot8 = \ _, _, _, bot8, _, _, _ => bot8

arr8 : Ty8-> Ty8-> Ty8
arr8 = \ a, b, ty, nat8, top8, bot8, arr8, prod, sum =>
     arr8 (a ty nat8 top8 bot8 arr8 prod sum) (b ty nat8 top8 bot8 arr8 prod sum)

prod8 : Ty8-> Ty8-> Ty8
prod8 = \ a, b, ty, nat8, top8, bot8, arr8, prod8, sum =>
     prod8 (a ty nat8 top8 bot8 arr8 prod8 sum) (b ty nat8 top8 bot8 arr8 prod8 sum)

sum8 : Ty8-> Ty8-> Ty8
sum8 = \ a, b, ty, nat8, top8, bot8, arr8, prod8, sum8 =>
     sum8 (a ty nat8 top8 bot8 arr8 prod8 sum8) (b ty nat8 top8 bot8 arr8 prod8 sum8)

Con8 : Type
Con8 = (Con8 : Type)
 -> (nil  : Con8)
 -> (snoc : Con8 -> Ty8-> Con8)
 -> Con8

nil8 : Con8
nil8 = \ con, nil8, snoc => nil8

snoc8 : Con8 -> Ty8-> Con8
snoc8 = \ g, a, con, nil8, snoc8 => snoc8 (g con nil8 snoc8) a

Var8 : Con8 -> Ty8-> Type
Var8 = \ g, a =>
    (Var8 : Con8 -> Ty8-> Type)
 -> (vz  : {g:_}->{a:_} -> Var8 (snoc8 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var8 g a -> Var8 (snoc8 g b) a)
 -> Var8 g a

vz8 : {g:_}->{a:_} -> Var8 (snoc8 g a) a
vz8 = \ var, vz8, vs => vz8

vs8 : {g:_}->{b:_}->{a:_} -> Var8 g a -> Var8 (snoc8 g b) a
vs8 = \ x, var, vz8, vs8 => vs8 (x var vz8 vs8)

Tm8 : Con8 -> Ty8-> Type
Tm8 = \ g, a =>
    (Tm8    : Con8 -> Ty8-> Type)
 -> (var   : {g:_}->{a:_}-> Var8 g a -> Tm8 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm8 (snoc8 g a) b -> Tm8 g (arr8 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm8 g (arr8 a b) -> Tm8 g a -> Tm8 g b)
 -> (tt    : {g:_}-> Tm8 g top8)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm8 g a -> Tm8 g b -> Tm8 g (prod8 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm8 g (prod8 a b) -> Tm8 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm8 g (prod8 a b) -> Tm8 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm8 g a -> Tm8 g (sum8 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm8 g b -> Tm8 g (sum8 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm8 g (sum8 a b) -> Tm8 g (arr8 a c) -> Tm8 g (arr8 b c) -> Tm8 g c)
 -> (zero  : {g:_}-> Tm8 g nat8)
 -> (suc   : {g:_}-> Tm8 g nat8 -> Tm8 g nat8)
 -> (rec   : {g:_}->{a:_} -> Tm8 g nat8 -> Tm8 g (arr8 nat8 (arr8 a a)) -> Tm8 g a -> Tm8 g a)
 -> Tm8 g a

var8 : {g:_}->{a:_} -> Var8 g a -> Tm8 g a
var8 = \ x, tm, var8, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var8 x

lam8 : {g:_}->{a:_}->{b:_}-> Tm8 (snoc8 g a) b -> Tm8 g (arr8 a b)
lam8 = \ t, tm, var8, lam8, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam8 (t tm var8 lam8 app tt pair fst snd left right split zero suc rec)

app8 : {g:_}->{a:_}->{b:_} -> Tm8 g (arr8 a b) -> Tm8 g a -> Tm8 g b
app8 = \ t, u, tm, var8, lam8, app8, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app8 (t tm var8 lam8 app8 tt pair fst snd left right split zero suc rec)
         (u tm var8 lam8 app8 tt pair fst snd left right split zero suc rec)

tt8 : {g:_} -> Tm8 g Main.top8
tt8 = \ tm, var8, lam8, app8, tt8, pair, fst, snd, left, right, split, zero, suc, rec => tt8

pair8 : {g:_}->{a:_}->{b:_} -> Tm8 g a -> Tm8 g b -> Tm8 g (prod8 a b)
pair8 = \ t, u, tm, var8, lam8, app8, tt8, pair8, fst, snd, left, right, split, zero, suc, rec =>
     pair8 (t tm var8 lam8 app8 tt8 pair8 fst snd left right split zero suc rec)
          (u tm var8 lam8 app8 tt8 pair8 fst snd left right split zero suc rec)

fst8 : {g:_}->{a:_}->{b:_}-> Tm8 g (prod8 a b) -> Tm8 g a
fst8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd, left, right, split, zero, suc, rec =>
     fst8 (t tm var8 lam8 app8 tt8 pair8 fst8 snd left right split zero suc rec)

snd8 : {g:_}->{a:_}->{b:_} -> Tm8 g (prod8 a b) -> Tm8 g b
snd8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left, right, split, zero, suc, rec =>
     snd8 (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left right split zero suc rec)

left8 : {g:_}->{a:_}->{b:_} -> Tm8 g a -> Tm8 g (sum8 a b)
left8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right, split, zero, suc, rec =>
     left8 (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right split zero suc rec)

right8 : {g:_}->{a:_}->{b:_} -> Tm8 g b -> Tm8 g (sum8 a b)
right8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split, zero, suc, rec =>
     right8 (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split zero suc rec)

split8 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm8 g (sum8 a b) -> Tm8 g (arr8 a c) -> Tm8 g (arr8 b c) -> Tm8 g c
split8 = \ t, u, v, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split8, zero, suc, rec =>
     split8 (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero suc rec)
          (u tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero suc rec)
          (v tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero suc rec)

zero8 : {g:_} -> Tm8 g Main.nat8
zero8 = \ tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split8, zero8, suc, rec => zero8

suc8 : {g:_} -> Tm8 g Main.nat8 -> Tm8 g Main.nat8
suc8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split8, zero8, suc8, rec =>
   suc8 (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero8 suc8 rec)

rec8 : {g:_}->{a:_} -> Tm8 g Main.nat8 -> Tm8 g (arr8 Main.nat8 (arr8 a a)) -> Tm8 g a -> Tm8 g a
rec8 = \ t, u, v, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split8, zero8, suc8, rec8 =>
     rec8 (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero8 suc8 rec8)
         (u tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero8 suc8 rec8)
         (v tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero8 suc8 rec8)

v08 : {g:_}->{a:_} -> Tm8 (snoc8 g a) a
v08 = var8 vz8

v18 : {g:_}->{a:_}->{b:_} -> Tm8 (snoc8 (snoc8 g a) b) a
v18 = var8 (vs8 vz8)

v28 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm8 (snoc8 (snoc8 (snoc8 g a) b) c) a
v28 = var8 (vs8 (vs8 vz8))

v38 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm8 (snoc8 (snoc8 (snoc8 (snoc8 g a) b) c) d) a
v38 = var8 (vs8 (vs8 (vs8 vz8)))

tbool8 : Ty8
tbool8 = sum8 top8 top8

ttrue8 : {g:_} -> Tm8 g Main.tbool8
ttrue8 = left8 tt8

tfalse8 : {g:_} -> Tm8 g Main.tbool8
tfalse8 = right8 tt8

ifthenelse8 : {g:_}->{a:_} -> Tm8 g (arr8 Main.tbool8 (arr8 a (arr8 a a)))
ifthenelse8 = lam8 (lam8 (lam8 (split8 v28 (lam8 v28) (lam8 v18))))

times48 : {g:_}->{a:_} -> Tm8 g (arr8 (arr8 a a) (arr8 a a))
times48  = lam8 (lam8 (app8 v18 (app8 v18 (app8 v18 (app8 v18 v08)))))

add8 : {g:_} -> Tm8 g (arr8 Main.nat8 (arr8 Main.nat8 Main.nat8))
add8 = lam8 (rec8 v08
       (lam8 (lam8 (lam8 (suc8 (app8 v18 v08)))))
       (lam8 v08))

mul8 : {g:_} -> Tm8 g (arr8 Main.nat8 (arr8 Main.nat8 Main.nat8))
mul8 = lam8 (rec8 v08
       (lam8 (lam8 (lam8 (app8 (app8 add8 (app8 v18 v08)) v08))))
       (lam8 zero8))

fact8 : {g:_} -> Tm8 g (arr8 Main.nat8 Main.nat8)
fact8 = lam8 (rec8 v08 (lam8 (lam8 (app8 (app8 mul8 (suc8 v18)) v08)))
                 (suc8 zero8))

Ty9 : Type
Ty9 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat9 : Ty9
nat9 = \ _, nat9, _, _, _, _, _ => nat9
top9 : Ty9
top9 = \ _, _, top9, _, _, _, _ => top9
bot9 : Ty9
bot9 = \ _, _, _, bot9, _, _, _ => bot9

arr9 : Ty9-> Ty9-> Ty9
arr9 = \ a, b, ty, nat9, top9, bot9, arr9, prod, sum =>
     arr9 (a ty nat9 top9 bot9 arr9 prod sum) (b ty nat9 top9 bot9 arr9 prod sum)

prod9 : Ty9-> Ty9-> Ty9
prod9 = \ a, b, ty, nat9, top9, bot9, arr9, prod9, sum =>
     prod9 (a ty nat9 top9 bot9 arr9 prod9 sum) (b ty nat9 top9 bot9 arr9 prod9 sum)

sum9 : Ty9-> Ty9-> Ty9
sum9 = \ a, b, ty, nat9, top9, bot9, arr9, prod9, sum9 =>
     sum9 (a ty nat9 top9 bot9 arr9 prod9 sum9) (b ty nat9 top9 bot9 arr9 prod9 sum9)

Con9 : Type
Con9 = (Con9 : Type)
 -> (nil  : Con9)
 -> (snoc : Con9 -> Ty9-> Con9)
 -> Con9

nil9 : Con9
nil9 = \ con, nil9, snoc => nil9

snoc9 : Con9 -> Ty9-> Con9
snoc9 = \ g, a, con, nil9, snoc9 => snoc9 (g con nil9 snoc9) a

Var9 : Con9 -> Ty9-> Type
Var9 = \ g, a =>
    (Var9 : Con9 -> Ty9-> Type)
 -> (vz  : {g:_}->{a:_} -> Var9 (snoc9 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var9 g a -> Var9 (snoc9 g b) a)
 -> Var9 g a

vz9 : {g:_}->{a:_} -> Var9 (snoc9 g a) a
vz9 = \ var, vz9, vs => vz9

vs9 : {g:_}->{b:_}->{a:_} -> Var9 g a -> Var9 (snoc9 g b) a
vs9 = \ x, var, vz9, vs9 => vs9 (x var vz9 vs9)

Tm9 : Con9 -> Ty9-> Type
Tm9 = \ g, a =>
    (Tm9    : Con9 -> Ty9-> Type)
 -> (var   : {g:_}->{a:_}-> Var9 g a -> Tm9 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm9 (snoc9 g a) b -> Tm9 g (arr9 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm9 g (arr9 a b) -> Tm9 g a -> Tm9 g b)
 -> (tt    : {g:_}-> Tm9 g top9)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm9 g a -> Tm9 g b -> Tm9 g (prod9 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm9 g (prod9 a b) -> Tm9 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm9 g (prod9 a b) -> Tm9 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm9 g a -> Tm9 g (sum9 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm9 g b -> Tm9 g (sum9 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm9 g (sum9 a b) -> Tm9 g (arr9 a c) -> Tm9 g (arr9 b c) -> Tm9 g c)
 -> (zero  : {g:_}-> Tm9 g nat9)
 -> (suc   : {g:_}-> Tm9 g nat9 -> Tm9 g nat9)
 -> (rec   : {g:_}->{a:_} -> Tm9 g nat9 -> Tm9 g (arr9 nat9 (arr9 a a)) -> Tm9 g a -> Tm9 g a)
 -> Tm9 g a

var9 : {g:_}->{a:_} -> Var9 g a -> Tm9 g a
var9 = \ x, tm, var9, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var9 x

lam9 : {g:_}->{a:_}->{b:_}-> Tm9 (snoc9 g a) b -> Tm9 g (arr9 a b)
lam9 = \ t, tm, var9, lam9, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam9 (t tm var9 lam9 app tt pair fst snd left right split zero suc rec)

app9 : {g:_}->{a:_}->{b:_} -> Tm9 g (arr9 a b) -> Tm9 g a -> Tm9 g b
app9 = \ t, u, tm, var9, lam9, app9, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app9 (t tm var9 lam9 app9 tt pair fst snd left right split zero suc rec)
         (u tm var9 lam9 app9 tt pair fst snd left right split zero suc rec)

tt9 : {g:_} -> Tm9 g Main.top9
tt9 = \ tm, var9, lam9, app9, tt9, pair, fst, snd, left, right, split, zero, suc, rec => tt9

pair9 : {g:_}->{a:_}->{b:_} -> Tm9 g a -> Tm9 g b -> Tm9 g (prod9 a b)
pair9 = \ t, u, tm, var9, lam9, app9, tt9, pair9, fst, snd, left, right, split, zero, suc, rec =>
     pair9 (t tm var9 lam9 app9 tt9 pair9 fst snd left right split zero suc rec)
          (u tm var9 lam9 app9 tt9 pair9 fst snd left right split zero suc rec)

fst9 : {g:_}->{a:_}->{b:_}-> Tm9 g (prod9 a b) -> Tm9 g a
fst9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd, left, right, split, zero, suc, rec =>
     fst9 (t tm var9 lam9 app9 tt9 pair9 fst9 snd left right split zero suc rec)

snd9 : {g:_}->{a:_}->{b:_} -> Tm9 g (prod9 a b) -> Tm9 g b
snd9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left, right, split, zero, suc, rec =>
     snd9 (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left right split zero suc rec)

left9 : {g:_}->{a:_}->{b:_} -> Tm9 g a -> Tm9 g (sum9 a b)
left9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right, split, zero, suc, rec =>
     left9 (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right split zero suc rec)

right9 : {g:_}->{a:_}->{b:_} -> Tm9 g b -> Tm9 g (sum9 a b)
right9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split, zero, suc, rec =>
     right9 (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split zero suc rec)

split9 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm9 g (sum9 a b) -> Tm9 g (arr9 a c) -> Tm9 g (arr9 b c) -> Tm9 g c
split9 = \ t, u, v, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split9, zero, suc, rec =>
     split9 (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero suc rec)
          (u tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero suc rec)
          (v tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero suc rec)

zero9 : {g:_} -> Tm9 g Main.nat9
zero9 = \ tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split9, zero9, suc, rec => zero9

suc9 : {g:_} -> Tm9 g Main.nat9 -> Tm9 g Main.nat9
suc9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split9, zero9, suc9, rec =>
   suc9 (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero9 suc9 rec)

rec9 : {g:_}->{a:_} -> Tm9 g Main.nat9 -> Tm9 g (arr9 Main.nat9 (arr9 a a)) -> Tm9 g a -> Tm9 g a
rec9 = \ t, u, v, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split9, zero9, suc9, rec9 =>
     rec9 (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero9 suc9 rec9)
         (u tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero9 suc9 rec9)
         (v tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero9 suc9 rec9)

v09 : {g:_}->{a:_} -> Tm9 (snoc9 g a) a
v09 = var9 vz9

v19 : {g:_}->{a:_}->{b:_} -> Tm9 (snoc9 (snoc9 g a) b) a
v19 = var9 (vs9 vz9)

v29 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm9 (snoc9 (snoc9 (snoc9 g a) b) c) a
v29 = var9 (vs9 (vs9 vz9))

v39 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm9 (snoc9 (snoc9 (snoc9 (snoc9 g a) b) c) d) a
v39 = var9 (vs9 (vs9 (vs9 vz9)))

tbool9 : Ty9
tbool9 = sum9 top9 top9

ttrue9 : {g:_} -> Tm9 g Main.tbool9
ttrue9 = left9 tt9

tfalse9 : {g:_} -> Tm9 g Main.tbool9
tfalse9 = right9 tt9

ifthenelse9 : {g:_}->{a:_} -> Tm9 g (arr9 Main.tbool9 (arr9 a (arr9 a a)))
ifthenelse9 = lam9 (lam9 (lam9 (split9 v29 (lam9 v29) (lam9 v19))))

times49 : {g:_}->{a:_} -> Tm9 g (arr9 (arr9 a a) (arr9 a a))
times49  = lam9 (lam9 (app9 v19 (app9 v19 (app9 v19 (app9 v19 v09)))))

add9 : {g:_} -> Tm9 g (arr9 Main.nat9 (arr9 Main.nat9 Main.nat9))
add9 = lam9 (rec9 v09
       (lam9 (lam9 (lam9 (suc9 (app9 v19 v09)))))
       (lam9 v09))

mul9 : {g:_} -> Tm9 g (arr9 Main.nat9 (arr9 Main.nat9 Main.nat9))
mul9 = lam9 (rec9 v09
       (lam9 (lam9 (lam9 (app9 (app9 add9 (app9 v19 v09)) v09))))
       (lam9 zero9))

fact9 : {g:_} -> Tm9 g (arr9 Main.nat9 Main.nat9)
fact9 = lam9 (rec9 v09 (lam9 (lam9 (app9 (app9 mul9 (suc9 v19)) v09)))
                 (suc9 zero9))

Ty10 : Type
Ty10 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat10 : Ty10
nat10 = \ _, nat10, _, _, _, _, _ => nat10
top10 : Ty10
top10 = \ _, _, top10, _, _, _, _ => top10
bot10 : Ty10
bot10 = \ _, _, _, bot10, _, _, _ => bot10

arr10 : Ty10-> Ty10-> Ty10
arr10 = \ a, b, ty, nat10, top10, bot10, arr10, prod, sum =>
     arr10 (a ty nat10 top10 bot10 arr10 prod sum) (b ty nat10 top10 bot10 arr10 prod sum)

prod10 : Ty10-> Ty10-> Ty10
prod10 = \ a, b, ty, nat10, top10, bot10, arr10, prod10, sum =>
     prod10 (a ty nat10 top10 bot10 arr10 prod10 sum) (b ty nat10 top10 bot10 arr10 prod10 sum)

sum10 : Ty10-> Ty10-> Ty10
sum10 = \ a, b, ty, nat10, top10, bot10, arr10, prod10, sum10 =>
     sum10 (a ty nat10 top10 bot10 arr10 prod10 sum10) (b ty nat10 top10 bot10 arr10 prod10 sum10)

Con10 : Type
Con10 = (Con10 : Type)
 -> (nil  : Con10)
 -> (snoc : Con10 -> Ty10-> Con10)
 -> Con10

nil10 : Con10
nil10 = \ con, nil10, snoc => nil10

snoc10 : Con10 -> Ty10-> Con10
snoc10 = \ g, a, con, nil10, snoc10 => snoc10 (g con nil10 snoc10) a

Var10 : Con10 -> Ty10-> Type
Var10 = \ g, a =>
    (Var10 : Con10 -> Ty10-> Type)
 -> (vz  : {g:_}->{a:_} -> Var10 (snoc10 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var10 g a -> Var10 (snoc10 g b) a)
 -> Var10 g a

vz10 : {g:_}->{a:_} -> Var10 (snoc10 g a) a
vz10 = \ var, vz10, vs => vz10

vs10 : {g:_}->{b:_}->{a:_} -> Var10 g a -> Var10 (snoc10 g b) a
vs10 = \ x, var, vz10, vs10 => vs10 (x var vz10 vs10)

Tm10 : Con10 -> Ty10-> Type
Tm10 = \ g, a =>
    (Tm10    : Con10 -> Ty10-> Type)
 -> (var   : {g:_}->{a:_}-> Var10 g a -> Tm10 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm10 (snoc10 g a) b -> Tm10 g (arr10 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm10 g (arr10 a b) -> Tm10 g a -> Tm10 g b)
 -> (tt    : {g:_}-> Tm10 g top10)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm10 g a -> Tm10 g b -> Tm10 g (prod10 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm10 g (prod10 a b) -> Tm10 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm10 g (prod10 a b) -> Tm10 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm10 g a -> Tm10 g (sum10 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm10 g b -> Tm10 g (sum10 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm10 g (sum10 a b) -> Tm10 g (arr10 a c) -> Tm10 g (arr10 b c) -> Tm10 g c)
 -> (zero  : {g:_}-> Tm10 g nat10)
 -> (suc   : {g:_}-> Tm10 g nat10 -> Tm10 g nat10)
 -> (rec   : {g:_}->{a:_} -> Tm10 g nat10 -> Tm10 g (arr10 nat10 (arr10 a a)) -> Tm10 g a -> Tm10 g a)
 -> Tm10 g a

var10 : {g:_}->{a:_} -> Var10 g a -> Tm10 g a
var10 = \ x, tm, var10, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var10 x

lam10 : {g:_}->{a:_}->{b:_}-> Tm10 (snoc10 g a) b -> Tm10 g (arr10 a b)
lam10 = \ t, tm, var10, lam10, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam10 (t tm var10 lam10 app tt pair fst snd left right split zero suc rec)

app10 : {g:_}->{a:_}->{b:_} -> Tm10 g (arr10 a b) -> Tm10 g a -> Tm10 g b
app10 = \ t, u, tm, var10, lam10, app10, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app10 (t tm var10 lam10 app10 tt pair fst snd left right split zero suc rec)
         (u tm var10 lam10 app10 tt pair fst snd left right split zero suc rec)

tt10 : {g:_} -> Tm10 g Main.top10
tt10 = \ tm, var10, lam10, app10, tt10, pair, fst, snd, left, right, split, zero, suc, rec => tt10

pair10 : {g:_}->{a:_}->{b:_} -> Tm10 g a -> Tm10 g b -> Tm10 g (prod10 a b)
pair10 = \ t, u, tm, var10, lam10, app10, tt10, pair10, fst, snd, left, right, split, zero, suc, rec =>
     pair10 (t tm var10 lam10 app10 tt10 pair10 fst snd left right split zero suc rec)
          (u tm var10 lam10 app10 tt10 pair10 fst snd left right split zero suc rec)

fst10 : {g:_}->{a:_}->{b:_}-> Tm10 g (prod10 a b) -> Tm10 g a
fst10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd, left, right, split, zero, suc, rec =>
     fst10 (t tm var10 lam10 app10 tt10 pair10 fst10 snd left right split zero suc rec)

snd10 : {g:_}->{a:_}->{b:_} -> Tm10 g (prod10 a b) -> Tm10 g b
snd10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left, right, split, zero, suc, rec =>
     snd10 (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left right split zero suc rec)

left10 : {g:_}->{a:_}->{b:_} -> Tm10 g a -> Tm10 g (sum10 a b)
left10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right, split, zero, suc, rec =>
     left10 (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right split zero suc rec)

right10 : {g:_}->{a:_}->{b:_} -> Tm10 g b -> Tm10 g (sum10 a b)
right10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split, zero, suc, rec =>
     right10 (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split zero suc rec)

split10 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm10 g (sum10 a b) -> Tm10 g (arr10 a c) -> Tm10 g (arr10 b c) -> Tm10 g c
split10 = \ t, u, v, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split10, zero, suc, rec =>
     split10 (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero suc rec)
          (u tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero suc rec)
          (v tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero suc rec)

zero10 : {g:_} -> Tm10 g Main.nat10
zero10 = \ tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split10, zero10, suc, rec => zero10

suc10 : {g:_} -> Tm10 g Main.nat10 -> Tm10 g Main.nat10
suc10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split10, zero10, suc10, rec =>
   suc10 (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero10 suc10 rec)

rec10 : {g:_}->{a:_} -> Tm10 g Main.nat10 -> Tm10 g (arr10 Main.nat10 (arr10 a a)) -> Tm10 g a -> Tm10 g a
rec10 = \ t, u, v, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split10, zero10, suc10, rec10 =>
     rec10 (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero10 suc10 rec10)
         (u tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero10 suc10 rec10)
         (v tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero10 suc10 rec10)

v010 : {g:_}->{a:_} -> Tm10 (snoc10 g a) a
v010 = var10 vz10

v110 : {g:_}->{a:_}->{b:_} -> Tm10 (snoc10 (snoc10 g a) b) a
v110 = var10 (vs10 vz10)

v210 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm10 (snoc10 (snoc10 (snoc10 g a) b) c) a
v210 = var10 (vs10 (vs10 vz10))

v310 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm10 (snoc10 (snoc10 (snoc10 (snoc10 g a) b) c) d) a
v310 = var10 (vs10 (vs10 (vs10 vz10)))

tbool10 : Ty10
tbool10 = sum10 top10 top10

ttrue10 : {g:_} -> Tm10 g Main.tbool10
ttrue10 = left10 tt10

tfalse10 : {g:_} -> Tm10 g Main.tbool10
tfalse10 = right10 tt10

ifthenelse10 : {g:_}->{a:_} -> Tm10 g (arr10 Main.tbool10 (arr10 a (arr10 a a)))
ifthenelse10 = lam10 (lam10 (lam10 (split10 v210 (lam10 v210) (lam10 v110))))

times410 : {g:_}->{a:_} -> Tm10 g (arr10 (arr10 a a) (arr10 a a))
times410  = lam10 (lam10 (app10 v110 (app10 v110 (app10 v110 (app10 v110 v010)))))

add10 : {g:_} -> Tm10 g (arr10 Main.nat10 (arr10 Main.nat10 Main.nat10))
add10 = lam10 (rec10 v010
       (lam10 (lam10 (lam10 (suc10 (app10 v110 v010)))))
       (lam10 v010))

mul10 : {g:_} -> Tm10 g (arr10 Main.nat10 (arr10 Main.nat10 Main.nat10))
mul10 = lam10 (rec10 v010
       (lam10 (lam10 (lam10 (app10 (app10 add10 (app10 v110 v010)) v010))))
       (lam10 zero10))

fact10 : {g:_} -> Tm10 g (arr10 Main.nat10 Main.nat10)
fact10 = lam10 (rec10 v010 (lam10 (lam10 (app10 (app10 mul10 (suc10 v110)) v010)))
                 (suc10 zero10))

Ty11 : Type
Ty11 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat11 : Ty11
nat11 = \ _, nat11, _, _, _, _, _ => nat11
top11 : Ty11
top11 = \ _, _, top11, _, _, _, _ => top11
bot11 : Ty11
bot11 = \ _, _, _, bot11, _, _, _ => bot11

arr11 : Ty11-> Ty11-> Ty11
arr11 = \ a, b, ty, nat11, top11, bot11, arr11, prod, sum =>
     arr11 (a ty nat11 top11 bot11 arr11 prod sum) (b ty nat11 top11 bot11 arr11 prod sum)

prod11 : Ty11-> Ty11-> Ty11
prod11 = \ a, b, ty, nat11, top11, bot11, arr11, prod11, sum =>
     prod11 (a ty nat11 top11 bot11 arr11 prod11 sum) (b ty nat11 top11 bot11 arr11 prod11 sum)

sum11 : Ty11-> Ty11-> Ty11
sum11 = \ a, b, ty, nat11, top11, bot11, arr11, prod11, sum11 =>
     sum11 (a ty nat11 top11 bot11 arr11 prod11 sum11) (b ty nat11 top11 bot11 arr11 prod11 sum11)

Con11 : Type
Con11 = (Con11 : Type)
 -> (nil  : Con11)
 -> (snoc : Con11 -> Ty11-> Con11)
 -> Con11

nil11 : Con11
nil11 = \ con, nil11, snoc => nil11

snoc11 : Con11 -> Ty11-> Con11
snoc11 = \ g, a, con, nil11, snoc11 => snoc11 (g con nil11 snoc11) a

Var11 : Con11 -> Ty11-> Type
Var11 = \ g, a =>
    (Var11 : Con11 -> Ty11-> Type)
 -> (vz  : {g:_}->{a:_} -> Var11 (snoc11 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var11 g a -> Var11 (snoc11 g b) a)
 -> Var11 g a

vz11 : {g:_}->{a:_} -> Var11 (snoc11 g a) a
vz11 = \ var, vz11, vs => vz11

vs11 : {g:_}->{b:_}->{a:_} -> Var11 g a -> Var11 (snoc11 g b) a
vs11 = \ x, var, vz11, vs11 => vs11 (x var vz11 vs11)

Tm11 : Con11 -> Ty11-> Type
Tm11 = \ g, a =>
    (Tm11    : Con11 -> Ty11-> Type)
 -> (var   : {g:_}->{a:_}-> Var11 g a -> Tm11 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm11 (snoc11 g a) b -> Tm11 g (arr11 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm11 g (arr11 a b) -> Tm11 g a -> Tm11 g b)
 -> (tt    : {g:_}-> Tm11 g top11)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm11 g a -> Tm11 g b -> Tm11 g (prod11 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm11 g (prod11 a b) -> Tm11 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm11 g (prod11 a b) -> Tm11 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm11 g a -> Tm11 g (sum11 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm11 g b -> Tm11 g (sum11 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm11 g (sum11 a b) -> Tm11 g (arr11 a c) -> Tm11 g (arr11 b c) -> Tm11 g c)
 -> (zero  : {g:_}-> Tm11 g nat11)
 -> (suc   : {g:_}-> Tm11 g nat11 -> Tm11 g nat11)
 -> (rec   : {g:_}->{a:_} -> Tm11 g nat11 -> Tm11 g (arr11 nat11 (arr11 a a)) -> Tm11 g a -> Tm11 g a)
 -> Tm11 g a

var11 : {g:_}->{a:_} -> Var11 g a -> Tm11 g a
var11 = \ x, tm, var11, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var11 x

lam11 : {g:_}->{a:_}->{b:_}-> Tm11 (snoc11 g a) b -> Tm11 g (arr11 a b)
lam11 = \ t, tm, var11, lam11, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam11 (t tm var11 lam11 app tt pair fst snd left right split zero suc rec)

app11 : {g:_}->{a:_}->{b:_} -> Tm11 g (arr11 a b) -> Tm11 g a -> Tm11 g b
app11 = \ t, u, tm, var11, lam11, app11, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app11 (t tm var11 lam11 app11 tt pair fst snd left right split zero suc rec)
         (u tm var11 lam11 app11 tt pair fst snd left right split zero suc rec)

tt11 : {g:_} -> Tm11 g Main.top11
tt11 = \ tm, var11, lam11, app11, tt11, pair, fst, snd, left, right, split, zero, suc, rec => tt11

pair11 : {g:_}->{a:_}->{b:_} -> Tm11 g a -> Tm11 g b -> Tm11 g (prod11 a b)
pair11 = \ t, u, tm, var11, lam11, app11, tt11, pair11, fst, snd, left, right, split, zero, suc, rec =>
     pair11 (t tm var11 lam11 app11 tt11 pair11 fst snd left right split zero suc rec)
          (u tm var11 lam11 app11 tt11 pair11 fst snd left right split zero suc rec)

fst11 : {g:_}->{a:_}->{b:_}-> Tm11 g (prod11 a b) -> Tm11 g a
fst11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd, left, right, split, zero, suc, rec =>
     fst11 (t tm var11 lam11 app11 tt11 pair11 fst11 snd left right split zero suc rec)

snd11 : {g:_}->{a:_}->{b:_} -> Tm11 g (prod11 a b) -> Tm11 g b
snd11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left, right, split, zero, suc, rec =>
     snd11 (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left right split zero suc rec)

left11 : {g:_}->{a:_}->{b:_} -> Tm11 g a -> Tm11 g (sum11 a b)
left11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right, split, zero, suc, rec =>
     left11 (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right split zero suc rec)

right11 : {g:_}->{a:_}->{b:_} -> Tm11 g b -> Tm11 g (sum11 a b)
right11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split, zero, suc, rec =>
     right11 (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split zero suc rec)

split11 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm11 g (sum11 a b) -> Tm11 g (arr11 a c) -> Tm11 g (arr11 b c) -> Tm11 g c
split11 = \ t, u, v, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split11, zero, suc, rec =>
     split11 (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero suc rec)
          (u tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero suc rec)
          (v tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero suc rec)

zero11 : {g:_} -> Tm11 g Main.nat11
zero11 = \ tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split11, zero11, suc, rec => zero11

suc11 : {g:_} -> Tm11 g Main.nat11 -> Tm11 g Main.nat11
suc11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split11, zero11, suc11, rec =>
   suc11 (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero11 suc11 rec)

rec11 : {g:_}->{a:_} -> Tm11 g Main.nat11 -> Tm11 g (arr11 Main.nat11 (arr11 a a)) -> Tm11 g a -> Tm11 g a
rec11 = \ t, u, v, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split11, zero11, suc11, rec11 =>
     rec11 (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero11 suc11 rec11)
         (u tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero11 suc11 rec11)
         (v tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero11 suc11 rec11)

v011 : {g:_}->{a:_} -> Tm11 (snoc11 g a) a
v011 = var11 vz11

v111 : {g:_}->{a:_}->{b:_} -> Tm11 (snoc11 (snoc11 g a) b) a
v111 = var11 (vs11 vz11)

v211 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm11 (snoc11 (snoc11 (snoc11 g a) b) c) a
v211 = var11 (vs11 (vs11 vz11))

v311 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm11 (snoc11 (snoc11 (snoc11 (snoc11 g a) b) c) d) a
v311 = var11 (vs11 (vs11 (vs11 vz11)))

tbool11 : Ty11
tbool11 = sum11 top11 top11

ttrue11 : {g:_} -> Tm11 g Main.tbool11
ttrue11 = left11 tt11

tfalse11 : {g:_} -> Tm11 g Main.tbool11
tfalse11 = right11 tt11

ifthenelse11 : {g:_}->{a:_} -> Tm11 g (arr11 Main.tbool11 (arr11 a (arr11 a a)))
ifthenelse11 = lam11 (lam11 (lam11 (split11 v211 (lam11 v211) (lam11 v111))))

times411 : {g:_}->{a:_} -> Tm11 g (arr11 (arr11 a a) (arr11 a a))
times411  = lam11 (lam11 (app11 v111 (app11 v111 (app11 v111 (app11 v111 v011)))))

add11 : {g:_} -> Tm11 g (arr11 Main.nat11 (arr11 Main.nat11 Main.nat11))
add11 = lam11 (rec11 v011
       (lam11 (lam11 (lam11 (suc11 (app11 v111 v011)))))
       (lam11 v011))

mul11 : {g:_} -> Tm11 g (arr11 Main.nat11 (arr11 Main.nat11 Main.nat11))
mul11 = lam11 (rec11 v011
       (lam11 (lam11 (lam11 (app11 (app11 add11 (app11 v111 v011)) v011))))
       (lam11 zero11))

fact11 : {g:_} -> Tm11 g (arr11 Main.nat11 Main.nat11)
fact11 = lam11 (rec11 v011 (lam11 (lam11 (app11 (app11 mul11 (suc11 v111)) v011)))
                 (suc11 zero11))

Ty12 : Type
Ty12 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat12 : Ty12
nat12 = \ _, nat12, _, _, _, _, _ => nat12
top12 : Ty12
top12 = \ _, _, top12, _, _, _, _ => top12
bot12 : Ty12
bot12 = \ _, _, _, bot12, _, _, _ => bot12

arr12 : Ty12-> Ty12-> Ty12
arr12 = \ a, b, ty, nat12, top12, bot12, arr12, prod, sum =>
     arr12 (a ty nat12 top12 bot12 arr12 prod sum) (b ty nat12 top12 bot12 arr12 prod sum)

prod12 : Ty12-> Ty12-> Ty12
prod12 = \ a, b, ty, nat12, top12, bot12, arr12, prod12, sum =>
     prod12 (a ty nat12 top12 bot12 arr12 prod12 sum) (b ty nat12 top12 bot12 arr12 prod12 sum)

sum12 : Ty12-> Ty12-> Ty12
sum12 = \ a, b, ty, nat12, top12, bot12, arr12, prod12, sum12 =>
     sum12 (a ty nat12 top12 bot12 arr12 prod12 sum12) (b ty nat12 top12 bot12 arr12 prod12 sum12)

Con12 : Type
Con12 = (Con12 : Type)
 -> (nil  : Con12)
 -> (snoc : Con12 -> Ty12-> Con12)
 -> Con12

nil12 : Con12
nil12 = \ con, nil12, snoc => nil12

snoc12 : Con12 -> Ty12-> Con12
snoc12 = \ g, a, con, nil12, snoc12 => snoc12 (g con nil12 snoc12) a

Var12 : Con12 -> Ty12-> Type
Var12 = \ g, a =>
    (Var12 : Con12 -> Ty12-> Type)
 -> (vz  : {g:_}->{a:_} -> Var12 (snoc12 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var12 g a -> Var12 (snoc12 g b) a)
 -> Var12 g a

vz12 : {g:_}->{a:_} -> Var12 (snoc12 g a) a
vz12 = \ var, vz12, vs => vz12

vs12 : {g:_}->{b:_}->{a:_} -> Var12 g a -> Var12 (snoc12 g b) a
vs12 = \ x, var, vz12, vs12 => vs12 (x var vz12 vs12)

Tm12 : Con12 -> Ty12-> Type
Tm12 = \ g, a =>
    (Tm12    : Con12 -> Ty12-> Type)
 -> (var   : {g:_}->{a:_}-> Var12 g a -> Tm12 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm12 (snoc12 g a) b -> Tm12 g (arr12 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm12 g (arr12 a b) -> Tm12 g a -> Tm12 g b)
 -> (tt    : {g:_}-> Tm12 g top12)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm12 g a -> Tm12 g b -> Tm12 g (prod12 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm12 g (prod12 a b) -> Tm12 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm12 g (prod12 a b) -> Tm12 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm12 g a -> Tm12 g (sum12 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm12 g b -> Tm12 g (sum12 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm12 g (sum12 a b) -> Tm12 g (arr12 a c) -> Tm12 g (arr12 b c) -> Tm12 g c)
 -> (zero  : {g:_}-> Tm12 g nat12)
 -> (suc   : {g:_}-> Tm12 g nat12 -> Tm12 g nat12)
 -> (rec   : {g:_}->{a:_} -> Tm12 g nat12 -> Tm12 g (arr12 nat12 (arr12 a a)) -> Tm12 g a -> Tm12 g a)
 -> Tm12 g a

var12 : {g:_}->{a:_} -> Var12 g a -> Tm12 g a
var12 = \ x, tm, var12, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var12 x

lam12 : {g:_}->{a:_}->{b:_}-> Tm12 (snoc12 g a) b -> Tm12 g (arr12 a b)
lam12 = \ t, tm, var12, lam12, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam12 (t tm var12 lam12 app tt pair fst snd left right split zero suc rec)

app12 : {g:_}->{a:_}->{b:_} -> Tm12 g (arr12 a b) -> Tm12 g a -> Tm12 g b
app12 = \ t, u, tm, var12, lam12, app12, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app12 (t tm var12 lam12 app12 tt pair fst snd left right split zero suc rec)
         (u tm var12 lam12 app12 tt pair fst snd left right split zero suc rec)

tt12 : {g:_} -> Tm12 g Main.top12
tt12 = \ tm, var12, lam12, app12, tt12, pair, fst, snd, left, right, split, zero, suc, rec => tt12

pair12 : {g:_}->{a:_}->{b:_} -> Tm12 g a -> Tm12 g b -> Tm12 g (prod12 a b)
pair12 = \ t, u, tm, var12, lam12, app12, tt12, pair12, fst, snd, left, right, split, zero, suc, rec =>
     pair12 (t tm var12 lam12 app12 tt12 pair12 fst snd left right split zero suc rec)
          (u tm var12 lam12 app12 tt12 pair12 fst snd left right split zero suc rec)

fst12 : {g:_}->{a:_}->{b:_}-> Tm12 g (prod12 a b) -> Tm12 g a
fst12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd, left, right, split, zero, suc, rec =>
     fst12 (t tm var12 lam12 app12 tt12 pair12 fst12 snd left right split zero suc rec)

snd12 : {g:_}->{a:_}->{b:_} -> Tm12 g (prod12 a b) -> Tm12 g b
snd12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left, right, split, zero, suc, rec =>
     snd12 (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left right split zero suc rec)

left12 : {g:_}->{a:_}->{b:_} -> Tm12 g a -> Tm12 g (sum12 a b)
left12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right, split, zero, suc, rec =>
     left12 (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right split zero suc rec)

right12 : {g:_}->{a:_}->{b:_} -> Tm12 g b -> Tm12 g (sum12 a b)
right12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split, zero, suc, rec =>
     right12 (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split zero suc rec)

split12 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm12 g (sum12 a b) -> Tm12 g (arr12 a c) -> Tm12 g (arr12 b c) -> Tm12 g c
split12 = \ t, u, v, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split12, zero, suc, rec =>
     split12 (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero suc rec)
          (u tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero suc rec)
          (v tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero suc rec)

zero12 : {g:_} -> Tm12 g Main.nat12
zero12 = \ tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split12, zero12, suc, rec => zero12

suc12 : {g:_} -> Tm12 g Main.nat12 -> Tm12 g Main.nat12
suc12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split12, zero12, suc12, rec =>
   suc12 (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero12 suc12 rec)

rec12 : {g:_}->{a:_} -> Tm12 g Main.nat12 -> Tm12 g (arr12 Main.nat12 (arr12 a a)) -> Tm12 g a -> Tm12 g a
rec12 = \ t, u, v, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split12, zero12, suc12, rec12 =>
     rec12 (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero12 suc12 rec12)
         (u tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero12 suc12 rec12)
         (v tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero12 suc12 rec12)

v012 : {g:_}->{a:_} -> Tm12 (snoc12 g a) a
v012 = var12 vz12

v112 : {g:_}->{a:_}->{b:_} -> Tm12 (snoc12 (snoc12 g a) b) a
v112 = var12 (vs12 vz12)

v212 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm12 (snoc12 (snoc12 (snoc12 g a) b) c) a
v212 = var12 (vs12 (vs12 vz12))

v312 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm12 (snoc12 (snoc12 (snoc12 (snoc12 g a) b) c) d) a
v312 = var12 (vs12 (vs12 (vs12 vz12)))

tbool12 : Ty12
tbool12 = sum12 top12 top12

ttrue12 : {g:_} -> Tm12 g Main.tbool12
ttrue12 = left12 tt12

tfalse12 : {g:_} -> Tm12 g Main.tbool12
tfalse12 = right12 tt12

ifthenelse12 : {g:_}->{a:_} -> Tm12 g (arr12 Main.tbool12 (arr12 a (arr12 a a)))
ifthenelse12 = lam12 (lam12 (lam12 (split12 v212 (lam12 v212) (lam12 v112))))

times412 : {g:_}->{a:_} -> Tm12 g (arr12 (arr12 a a) (arr12 a a))
times412  = lam12 (lam12 (app12 v112 (app12 v112 (app12 v112 (app12 v112 v012)))))

add12 : {g:_} -> Tm12 g (arr12 Main.nat12 (arr12 Main.nat12 Main.nat12))
add12 = lam12 (rec12 v012
       (lam12 (lam12 (lam12 (suc12 (app12 v112 v012)))))
       (lam12 v012))

mul12 : {g:_} -> Tm12 g (arr12 Main.nat12 (arr12 Main.nat12 Main.nat12))
mul12 = lam12 (rec12 v012
       (lam12 (lam12 (lam12 (app12 (app12 add12 (app12 v112 v012)) v012))))
       (lam12 zero12))

fact12 : {g:_} -> Tm12 g (arr12 Main.nat12 Main.nat12)
fact12 = lam12 (rec12 v012 (lam12 (lam12 (app12 (app12 mul12 (suc12 v112)) v012)))
                 (suc12 zero12))

Ty13 : Type
Ty13 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat13 : Ty13
nat13 = \ _, nat13, _, _, _, _, _ => nat13
top13 : Ty13
top13 = \ _, _, top13, _, _, _, _ => top13
bot13 : Ty13
bot13 = \ _, _, _, bot13, _, _, _ => bot13

arr13 : Ty13-> Ty13-> Ty13
arr13 = \ a, b, ty, nat13, top13, bot13, arr13, prod, sum =>
     arr13 (a ty nat13 top13 bot13 arr13 prod sum) (b ty nat13 top13 bot13 arr13 prod sum)

prod13 : Ty13-> Ty13-> Ty13
prod13 = \ a, b, ty, nat13, top13, bot13, arr13, prod13, sum =>
     prod13 (a ty nat13 top13 bot13 arr13 prod13 sum) (b ty nat13 top13 bot13 arr13 prod13 sum)

sum13 : Ty13-> Ty13-> Ty13
sum13 = \ a, b, ty, nat13, top13, bot13, arr13, prod13, sum13 =>
     sum13 (a ty nat13 top13 bot13 arr13 prod13 sum13) (b ty nat13 top13 bot13 arr13 prod13 sum13)

Con13 : Type
Con13 = (Con13 : Type)
 -> (nil  : Con13)
 -> (snoc : Con13 -> Ty13-> Con13)
 -> Con13

nil13 : Con13
nil13 = \ con, nil13, snoc => nil13

snoc13 : Con13 -> Ty13-> Con13
snoc13 = \ g, a, con, nil13, snoc13 => snoc13 (g con nil13 snoc13) a

Var13 : Con13 -> Ty13-> Type
Var13 = \ g, a =>
    (Var13 : Con13 -> Ty13-> Type)
 -> (vz  : {g:_}->{a:_} -> Var13 (snoc13 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var13 g a -> Var13 (snoc13 g b) a)
 -> Var13 g a

vz13 : {g:_}->{a:_} -> Var13 (snoc13 g a) a
vz13 = \ var, vz13, vs => vz13

vs13 : {g:_}->{b:_}->{a:_} -> Var13 g a -> Var13 (snoc13 g b) a
vs13 = \ x, var, vz13, vs13 => vs13 (x var vz13 vs13)

Tm13 : Con13 -> Ty13-> Type
Tm13 = \ g, a =>
    (Tm13    : Con13 -> Ty13-> Type)
 -> (var   : {g:_}->{a:_}-> Var13 g a -> Tm13 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm13 (snoc13 g a) b -> Tm13 g (arr13 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm13 g (arr13 a b) -> Tm13 g a -> Tm13 g b)
 -> (tt    : {g:_}-> Tm13 g top13)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm13 g a -> Tm13 g b -> Tm13 g (prod13 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm13 g (prod13 a b) -> Tm13 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm13 g (prod13 a b) -> Tm13 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm13 g a -> Tm13 g (sum13 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm13 g b -> Tm13 g (sum13 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm13 g (sum13 a b) -> Tm13 g (arr13 a c) -> Tm13 g (arr13 b c) -> Tm13 g c)
 -> (zero  : {g:_}-> Tm13 g nat13)
 -> (suc   : {g:_}-> Tm13 g nat13 -> Tm13 g nat13)
 -> (rec   : {g:_}->{a:_} -> Tm13 g nat13 -> Tm13 g (arr13 nat13 (arr13 a a)) -> Tm13 g a -> Tm13 g a)
 -> Tm13 g a

var13 : {g:_}->{a:_} -> Var13 g a -> Tm13 g a
var13 = \ x, tm, var13, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var13 x

lam13 : {g:_}->{a:_}->{b:_}-> Tm13 (snoc13 g a) b -> Tm13 g (arr13 a b)
lam13 = \ t, tm, var13, lam13, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam13 (t tm var13 lam13 app tt pair fst snd left right split zero suc rec)

app13 : {g:_}->{a:_}->{b:_} -> Tm13 g (arr13 a b) -> Tm13 g a -> Tm13 g b
app13 = \ t, u, tm, var13, lam13, app13, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app13 (t tm var13 lam13 app13 tt pair fst snd left right split zero suc rec)
         (u tm var13 lam13 app13 tt pair fst snd left right split zero suc rec)

tt13 : {g:_} -> Tm13 g Main.top13
tt13 = \ tm, var13, lam13, app13, tt13, pair, fst, snd, left, right, split, zero, suc, rec => tt13

pair13 : {g:_}->{a:_}->{b:_} -> Tm13 g a -> Tm13 g b -> Tm13 g (prod13 a b)
pair13 = \ t, u, tm, var13, lam13, app13, tt13, pair13, fst, snd, left, right, split, zero, suc, rec =>
     pair13 (t tm var13 lam13 app13 tt13 pair13 fst snd left right split zero suc rec)
          (u tm var13 lam13 app13 tt13 pair13 fst snd left right split zero suc rec)

fst13 : {g:_}->{a:_}->{b:_}-> Tm13 g (prod13 a b) -> Tm13 g a
fst13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd, left, right, split, zero, suc, rec =>
     fst13 (t tm var13 lam13 app13 tt13 pair13 fst13 snd left right split zero suc rec)

snd13 : {g:_}->{a:_}->{b:_} -> Tm13 g (prod13 a b) -> Tm13 g b
snd13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left, right, split, zero, suc, rec =>
     snd13 (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left right split zero suc rec)

left13 : {g:_}->{a:_}->{b:_} -> Tm13 g a -> Tm13 g (sum13 a b)
left13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right, split, zero, suc, rec =>
     left13 (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right split zero suc rec)

right13 : {g:_}->{a:_}->{b:_} -> Tm13 g b -> Tm13 g (sum13 a b)
right13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split, zero, suc, rec =>
     right13 (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split zero suc rec)

split13 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm13 g (sum13 a b) -> Tm13 g (arr13 a c) -> Tm13 g (arr13 b c) -> Tm13 g c
split13 = \ t, u, v, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split13, zero, suc, rec =>
     split13 (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero suc rec)
          (u tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero suc rec)
          (v tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero suc rec)

zero13 : {g:_} -> Tm13 g Main.nat13
zero13 = \ tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split13, zero13, suc, rec => zero13

suc13 : {g:_} -> Tm13 g Main.nat13 -> Tm13 g Main.nat13
suc13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split13, zero13, suc13, rec =>
   suc13 (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero13 suc13 rec)

rec13 : {g:_}->{a:_} -> Tm13 g Main.nat13 -> Tm13 g (arr13 Main.nat13 (arr13 a a)) -> Tm13 g a -> Tm13 g a
rec13 = \ t, u, v, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split13, zero13, suc13, rec13 =>
     rec13 (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero13 suc13 rec13)
         (u tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero13 suc13 rec13)
         (v tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero13 suc13 rec13)

v013 : {g:_}->{a:_} -> Tm13 (snoc13 g a) a
v013 = var13 vz13

v113 : {g:_}->{a:_}->{b:_} -> Tm13 (snoc13 (snoc13 g a) b) a
v113 = var13 (vs13 vz13)

v213 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm13 (snoc13 (snoc13 (snoc13 g a) b) c) a
v213 = var13 (vs13 (vs13 vz13))

v313 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm13 (snoc13 (snoc13 (snoc13 (snoc13 g a) b) c) d) a
v313 = var13 (vs13 (vs13 (vs13 vz13)))

tbool13 : Ty13
tbool13 = sum13 top13 top13

ttrue13 : {g:_} -> Tm13 g Main.tbool13
ttrue13 = left13 tt13

tfalse13 : {g:_} -> Tm13 g Main.tbool13
tfalse13 = right13 tt13

ifthenelse13 : {g:_}->{a:_} -> Tm13 g (arr13 Main.tbool13 (arr13 a (arr13 a a)))
ifthenelse13 = lam13 (lam13 (lam13 (split13 v213 (lam13 v213) (lam13 v113))))

times413 : {g:_}->{a:_} -> Tm13 g (arr13 (arr13 a a) (arr13 a a))
times413  = lam13 (lam13 (app13 v113 (app13 v113 (app13 v113 (app13 v113 v013)))))

add13 : {g:_} -> Tm13 g (arr13 Main.nat13 (arr13 Main.nat13 Main.nat13))
add13 = lam13 (rec13 v013
       (lam13 (lam13 (lam13 (suc13 (app13 v113 v013)))))
       (lam13 v013))

mul13 : {g:_} -> Tm13 g (arr13 Main.nat13 (arr13 Main.nat13 Main.nat13))
mul13 = lam13 (rec13 v013
       (lam13 (lam13 (lam13 (app13 (app13 add13 (app13 v113 v013)) v013))))
       (lam13 zero13))

fact13 : {g:_} -> Tm13 g (arr13 Main.nat13 Main.nat13)
fact13 = lam13 (rec13 v013 (lam13 (lam13 (app13 (app13 mul13 (suc13 v113)) v013)))
                 (suc13 zero13))

Ty14 : Type
Ty14 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat14 : Ty14
nat14 = \ _, nat14, _, _, _, _, _ => nat14
top14 : Ty14
top14 = \ _, _, top14, _, _, _, _ => top14
bot14 : Ty14
bot14 = \ _, _, _, bot14, _, _, _ => bot14

arr14 : Ty14-> Ty14-> Ty14
arr14 = \ a, b, ty, nat14, top14, bot14, arr14, prod, sum =>
     arr14 (a ty nat14 top14 bot14 arr14 prod sum) (b ty nat14 top14 bot14 arr14 prod sum)

prod14 : Ty14-> Ty14-> Ty14
prod14 = \ a, b, ty, nat14, top14, bot14, arr14, prod14, sum =>
     prod14 (a ty nat14 top14 bot14 arr14 prod14 sum) (b ty nat14 top14 bot14 arr14 prod14 sum)

sum14 : Ty14-> Ty14-> Ty14
sum14 = \ a, b, ty, nat14, top14, bot14, arr14, prod14, sum14 =>
     sum14 (a ty nat14 top14 bot14 arr14 prod14 sum14) (b ty nat14 top14 bot14 arr14 prod14 sum14)

Con14 : Type
Con14 = (Con14 : Type)
 -> (nil  : Con14)
 -> (snoc : Con14 -> Ty14-> Con14)
 -> Con14

nil14 : Con14
nil14 = \ con, nil14, snoc => nil14

snoc14 : Con14 -> Ty14-> Con14
snoc14 = \ g, a, con, nil14, snoc14 => snoc14 (g con nil14 snoc14) a

Var14 : Con14 -> Ty14-> Type
Var14 = \ g, a =>
    (Var14 : Con14 -> Ty14-> Type)
 -> (vz  : {g:_}->{a:_} -> Var14 (snoc14 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var14 g a -> Var14 (snoc14 g b) a)
 -> Var14 g a

vz14 : {g:_}->{a:_} -> Var14 (snoc14 g a) a
vz14 = \ var, vz14, vs => vz14

vs14 : {g:_}->{b:_}->{a:_} -> Var14 g a -> Var14 (snoc14 g b) a
vs14 = \ x, var, vz14, vs14 => vs14 (x var vz14 vs14)

Tm14 : Con14 -> Ty14-> Type
Tm14 = \ g, a =>
    (Tm14    : Con14 -> Ty14-> Type)
 -> (var   : {g:_}->{a:_}-> Var14 g a -> Tm14 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm14 (snoc14 g a) b -> Tm14 g (arr14 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm14 g (arr14 a b) -> Tm14 g a -> Tm14 g b)
 -> (tt    : {g:_}-> Tm14 g top14)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm14 g a -> Tm14 g b -> Tm14 g (prod14 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm14 g (prod14 a b) -> Tm14 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm14 g (prod14 a b) -> Tm14 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm14 g a -> Tm14 g (sum14 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm14 g b -> Tm14 g (sum14 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm14 g (sum14 a b) -> Tm14 g (arr14 a c) -> Tm14 g (arr14 b c) -> Tm14 g c)
 -> (zero  : {g:_}-> Tm14 g nat14)
 -> (suc   : {g:_}-> Tm14 g nat14 -> Tm14 g nat14)
 -> (rec   : {g:_}->{a:_} -> Tm14 g nat14 -> Tm14 g (arr14 nat14 (arr14 a a)) -> Tm14 g a -> Tm14 g a)
 -> Tm14 g a

var14 : {g:_}->{a:_} -> Var14 g a -> Tm14 g a
var14 = \ x, tm, var14, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var14 x

lam14 : {g:_}->{a:_}->{b:_}-> Tm14 (snoc14 g a) b -> Tm14 g (arr14 a b)
lam14 = \ t, tm, var14, lam14, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam14 (t tm var14 lam14 app tt pair fst snd left right split zero suc rec)

app14 : {g:_}->{a:_}->{b:_} -> Tm14 g (arr14 a b) -> Tm14 g a -> Tm14 g b
app14 = \ t, u, tm, var14, lam14, app14, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app14 (t tm var14 lam14 app14 tt pair fst snd left right split zero suc rec)
         (u tm var14 lam14 app14 tt pair fst snd left right split zero suc rec)

tt14 : {g:_} -> Tm14 g Main.top14
tt14 = \ tm, var14, lam14, app14, tt14, pair, fst, snd, left, right, split, zero, suc, rec => tt14

pair14 : {g:_}->{a:_}->{b:_} -> Tm14 g a -> Tm14 g b -> Tm14 g (prod14 a b)
pair14 = \ t, u, tm, var14, lam14, app14, tt14, pair14, fst, snd, left, right, split, zero, suc, rec =>
     pair14 (t tm var14 lam14 app14 tt14 pair14 fst snd left right split zero suc rec)
          (u tm var14 lam14 app14 tt14 pair14 fst snd left right split zero suc rec)

fst14 : {g:_}->{a:_}->{b:_}-> Tm14 g (prod14 a b) -> Tm14 g a
fst14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd, left, right, split, zero, suc, rec =>
     fst14 (t tm var14 lam14 app14 tt14 pair14 fst14 snd left right split zero suc rec)

snd14 : {g:_}->{a:_}->{b:_} -> Tm14 g (prod14 a b) -> Tm14 g b
snd14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left, right, split, zero, suc, rec =>
     snd14 (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left right split zero suc rec)

left14 : {g:_}->{a:_}->{b:_} -> Tm14 g a -> Tm14 g (sum14 a b)
left14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right, split, zero, suc, rec =>
     left14 (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right split zero suc rec)

right14 : {g:_}->{a:_}->{b:_} -> Tm14 g b -> Tm14 g (sum14 a b)
right14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split, zero, suc, rec =>
     right14 (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split zero suc rec)

split14 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm14 g (sum14 a b) -> Tm14 g (arr14 a c) -> Tm14 g (arr14 b c) -> Tm14 g c
split14 = \ t, u, v, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split14, zero, suc, rec =>
     split14 (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero suc rec)
          (u tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero suc rec)
          (v tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero suc rec)

zero14 : {g:_} -> Tm14 g Main.nat14
zero14 = \ tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split14, zero14, suc, rec => zero14

suc14 : {g:_} -> Tm14 g Main.nat14 -> Tm14 g Main.nat14
suc14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split14, zero14, suc14, rec =>
   suc14 (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero14 suc14 rec)

rec14 : {g:_}->{a:_} -> Tm14 g Main.nat14 -> Tm14 g (arr14 Main.nat14 (arr14 a a)) -> Tm14 g a -> Tm14 g a
rec14 = \ t, u, v, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split14, zero14, suc14, rec14 =>
     rec14 (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero14 suc14 rec14)
         (u tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero14 suc14 rec14)
         (v tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero14 suc14 rec14)

v014 : {g:_}->{a:_} -> Tm14 (snoc14 g a) a
v014 = var14 vz14

v114 : {g:_}->{a:_}->{b:_} -> Tm14 (snoc14 (snoc14 g a) b) a
v114 = var14 (vs14 vz14)

v214 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm14 (snoc14 (snoc14 (snoc14 g a) b) c) a
v214 = var14 (vs14 (vs14 vz14))

v314 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm14 (snoc14 (snoc14 (snoc14 (snoc14 g a) b) c) d) a
v314 = var14 (vs14 (vs14 (vs14 vz14)))

tbool14 : Ty14
tbool14 = sum14 top14 top14

ttrue14 : {g:_} -> Tm14 g Main.tbool14
ttrue14 = left14 tt14

tfalse14 : {g:_} -> Tm14 g Main.tbool14
tfalse14 = right14 tt14

ifthenelse14 : {g:_}->{a:_} -> Tm14 g (arr14 Main.tbool14 (arr14 a (arr14 a a)))
ifthenelse14 = lam14 (lam14 (lam14 (split14 v214 (lam14 v214) (lam14 v114))))

times414 : {g:_}->{a:_} -> Tm14 g (arr14 (arr14 a a) (arr14 a a))
times414  = lam14 (lam14 (app14 v114 (app14 v114 (app14 v114 (app14 v114 v014)))))

add14 : {g:_} -> Tm14 g (arr14 Main.nat14 (arr14 Main.nat14 Main.nat14))
add14 = lam14 (rec14 v014
       (lam14 (lam14 (lam14 (suc14 (app14 v114 v014)))))
       (lam14 v014))

mul14 : {g:_} -> Tm14 g (arr14 Main.nat14 (arr14 Main.nat14 Main.nat14))
mul14 = lam14 (rec14 v014
       (lam14 (lam14 (lam14 (app14 (app14 add14 (app14 v114 v014)) v014))))
       (lam14 zero14))

fact14 : {g:_} -> Tm14 g (arr14 Main.nat14 Main.nat14)
fact14 = lam14 (rec14 v014 (lam14 (lam14 (app14 (app14 mul14 (suc14 v114)) v014)))
                 (suc14 zero14))

Ty15 : Type
Ty15 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat15 : Ty15
nat15 = \ _, nat15, _, _, _, _, _ => nat15
top15 : Ty15
top15 = \ _, _, top15, _, _, _, _ => top15
bot15 : Ty15
bot15 = \ _, _, _, bot15, _, _, _ => bot15

arr15 : Ty15-> Ty15-> Ty15
arr15 = \ a, b, ty, nat15, top15, bot15, arr15, prod, sum =>
     arr15 (a ty nat15 top15 bot15 arr15 prod sum) (b ty nat15 top15 bot15 arr15 prod sum)

prod15 : Ty15-> Ty15-> Ty15
prod15 = \ a, b, ty, nat15, top15, bot15, arr15, prod15, sum =>
     prod15 (a ty nat15 top15 bot15 arr15 prod15 sum) (b ty nat15 top15 bot15 arr15 prod15 sum)

sum15 : Ty15-> Ty15-> Ty15
sum15 = \ a, b, ty, nat15, top15, bot15, arr15, prod15, sum15 =>
     sum15 (a ty nat15 top15 bot15 arr15 prod15 sum15) (b ty nat15 top15 bot15 arr15 prod15 sum15)

Con15 : Type
Con15 = (Con15 : Type)
 -> (nil  : Con15)
 -> (snoc : Con15 -> Ty15-> Con15)
 -> Con15

nil15 : Con15
nil15 = \ con, nil15, snoc => nil15

snoc15 : Con15 -> Ty15-> Con15
snoc15 = \ g, a, con, nil15, snoc15 => snoc15 (g con nil15 snoc15) a

Var15 : Con15 -> Ty15-> Type
Var15 = \ g, a =>
    (Var15 : Con15 -> Ty15-> Type)
 -> (vz  : {g:_}->{a:_} -> Var15 (snoc15 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var15 g a -> Var15 (snoc15 g b) a)
 -> Var15 g a

vz15 : {g:_}->{a:_} -> Var15 (snoc15 g a) a
vz15 = \ var, vz15, vs => vz15

vs15 : {g:_}->{b:_}->{a:_} -> Var15 g a -> Var15 (snoc15 g b) a
vs15 = \ x, var, vz15, vs15 => vs15 (x var vz15 vs15)

Tm15 : Con15 -> Ty15-> Type
Tm15 = \ g, a =>
    (Tm15    : Con15 -> Ty15-> Type)
 -> (var   : {g:_}->{a:_}-> Var15 g a -> Tm15 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm15 (snoc15 g a) b -> Tm15 g (arr15 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm15 g (arr15 a b) -> Tm15 g a -> Tm15 g b)
 -> (tt    : {g:_}-> Tm15 g top15)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm15 g a -> Tm15 g b -> Tm15 g (prod15 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm15 g (prod15 a b) -> Tm15 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm15 g (prod15 a b) -> Tm15 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm15 g a -> Tm15 g (sum15 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm15 g b -> Tm15 g (sum15 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm15 g (sum15 a b) -> Tm15 g (arr15 a c) -> Tm15 g (arr15 b c) -> Tm15 g c)
 -> (zero  : {g:_}-> Tm15 g nat15)
 -> (suc   : {g:_}-> Tm15 g nat15 -> Tm15 g nat15)
 -> (rec   : {g:_}->{a:_} -> Tm15 g nat15 -> Tm15 g (arr15 nat15 (arr15 a a)) -> Tm15 g a -> Tm15 g a)
 -> Tm15 g a

var15 : {g:_}->{a:_} -> Var15 g a -> Tm15 g a
var15 = \ x, tm, var15, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var15 x

lam15 : {g:_}->{a:_}->{b:_}-> Tm15 (snoc15 g a) b -> Tm15 g (arr15 a b)
lam15 = \ t, tm, var15, lam15, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam15 (t tm var15 lam15 app tt pair fst snd left right split zero suc rec)

app15 : {g:_}->{a:_}->{b:_} -> Tm15 g (arr15 a b) -> Tm15 g a -> Tm15 g b
app15 = \ t, u, tm, var15, lam15, app15, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app15 (t tm var15 lam15 app15 tt pair fst snd left right split zero suc rec)
         (u tm var15 lam15 app15 tt pair fst snd left right split zero suc rec)

tt15 : {g:_} -> Tm15 g Main.top15
tt15 = \ tm, var15, lam15, app15, tt15, pair, fst, snd, left, right, split, zero, suc, rec => tt15

pair15 : {g:_}->{a:_}->{b:_} -> Tm15 g a -> Tm15 g b -> Tm15 g (prod15 a b)
pair15 = \ t, u, tm, var15, lam15, app15, tt15, pair15, fst, snd, left, right, split, zero, suc, rec =>
     pair15 (t tm var15 lam15 app15 tt15 pair15 fst snd left right split zero suc rec)
          (u tm var15 lam15 app15 tt15 pair15 fst snd left right split zero suc rec)

fst15 : {g:_}->{a:_}->{b:_}-> Tm15 g (prod15 a b) -> Tm15 g a
fst15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd, left, right, split, zero, suc, rec =>
     fst15 (t tm var15 lam15 app15 tt15 pair15 fst15 snd left right split zero suc rec)

snd15 : {g:_}->{a:_}->{b:_} -> Tm15 g (prod15 a b) -> Tm15 g b
snd15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left, right, split, zero, suc, rec =>
     snd15 (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left right split zero suc rec)

left15 : {g:_}->{a:_}->{b:_} -> Tm15 g a -> Tm15 g (sum15 a b)
left15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right, split, zero, suc, rec =>
     left15 (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right split zero suc rec)

right15 : {g:_}->{a:_}->{b:_} -> Tm15 g b -> Tm15 g (sum15 a b)
right15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split, zero, suc, rec =>
     right15 (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split zero suc rec)

split15 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm15 g (sum15 a b) -> Tm15 g (arr15 a c) -> Tm15 g (arr15 b c) -> Tm15 g c
split15 = \ t, u, v, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split15, zero, suc, rec =>
     split15 (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero suc rec)
          (u tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero suc rec)
          (v tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero suc rec)

zero15 : {g:_} -> Tm15 g Main.nat15
zero15 = \ tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split15, zero15, suc, rec => zero15

suc15 : {g:_} -> Tm15 g Main.nat15 -> Tm15 g Main.nat15
suc15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split15, zero15, suc15, rec =>
   suc15 (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero15 suc15 rec)

rec15 : {g:_}->{a:_} -> Tm15 g Main.nat15 -> Tm15 g (arr15 Main.nat15 (arr15 a a)) -> Tm15 g a -> Tm15 g a
rec15 = \ t, u, v, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split15, zero15, suc15, rec15 =>
     rec15 (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero15 suc15 rec15)
         (u tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero15 suc15 rec15)
         (v tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero15 suc15 rec15)

v015 : {g:_}->{a:_} -> Tm15 (snoc15 g a) a
v015 = var15 vz15

v115 : {g:_}->{a:_}->{b:_} -> Tm15 (snoc15 (snoc15 g a) b) a
v115 = var15 (vs15 vz15)

v215 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm15 (snoc15 (snoc15 (snoc15 g a) b) c) a
v215 = var15 (vs15 (vs15 vz15))

v315 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm15 (snoc15 (snoc15 (snoc15 (snoc15 g a) b) c) d) a
v315 = var15 (vs15 (vs15 (vs15 vz15)))

tbool15 : Ty15
tbool15 = sum15 top15 top15

ttrue15 : {g:_} -> Tm15 g Main.tbool15
ttrue15 = left15 tt15

tfalse15 : {g:_} -> Tm15 g Main.tbool15
tfalse15 = right15 tt15

ifthenelse15 : {g:_}->{a:_} -> Tm15 g (arr15 Main.tbool15 (arr15 a (arr15 a a)))
ifthenelse15 = lam15 (lam15 (lam15 (split15 v215 (lam15 v215) (lam15 v115))))

times415 : {g:_}->{a:_} -> Tm15 g (arr15 (arr15 a a) (arr15 a a))
times415  = lam15 (lam15 (app15 v115 (app15 v115 (app15 v115 (app15 v115 v015)))))

add15 : {g:_} -> Tm15 g (arr15 Main.nat15 (arr15 Main.nat15 Main.nat15))
add15 = lam15 (rec15 v015
       (lam15 (lam15 (lam15 (suc15 (app15 v115 v015)))))
       (lam15 v015))

mul15 : {g:_} -> Tm15 g (arr15 Main.nat15 (arr15 Main.nat15 Main.nat15))
mul15 = lam15 (rec15 v015
       (lam15 (lam15 (lam15 (app15 (app15 add15 (app15 v115 v015)) v015))))
       (lam15 zero15))

fact15 : {g:_} -> Tm15 g (arr15 Main.nat15 Main.nat15)
fact15 = lam15 (rec15 v015 (lam15 (lam15 (app15 (app15 mul15 (suc15 v115)) v015)))
                 (suc15 zero15))

Ty16 : Type
Ty16 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat16 : Ty16
nat16 = \ _, nat16, _, _, _, _, _ => nat16
top16 : Ty16
top16 = \ _, _, top16, _, _, _, _ => top16
bot16 : Ty16
bot16 = \ _, _, _, bot16, _, _, _ => bot16

arr16 : Ty16-> Ty16-> Ty16
arr16 = \ a, b, ty, nat16, top16, bot16, arr16, prod, sum =>
     arr16 (a ty nat16 top16 bot16 arr16 prod sum) (b ty nat16 top16 bot16 arr16 prod sum)

prod16 : Ty16-> Ty16-> Ty16
prod16 = \ a, b, ty, nat16, top16, bot16, arr16, prod16, sum =>
     prod16 (a ty nat16 top16 bot16 arr16 prod16 sum) (b ty nat16 top16 bot16 arr16 prod16 sum)

sum16 : Ty16-> Ty16-> Ty16
sum16 = \ a, b, ty, nat16, top16, bot16, arr16, prod16, sum16 =>
     sum16 (a ty nat16 top16 bot16 arr16 prod16 sum16) (b ty nat16 top16 bot16 arr16 prod16 sum16)

Con16 : Type
Con16 = (Con16 : Type)
 -> (nil  : Con16)
 -> (snoc : Con16 -> Ty16-> Con16)
 -> Con16

nil16 : Con16
nil16 = \ con, nil16, snoc => nil16

snoc16 : Con16 -> Ty16-> Con16
snoc16 = \ g, a, con, nil16, snoc16 => snoc16 (g con nil16 snoc16) a

Var16 : Con16 -> Ty16-> Type
Var16 = \ g, a =>
    (Var16 : Con16 -> Ty16-> Type)
 -> (vz  : {g:_}->{a:_} -> Var16 (snoc16 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var16 g a -> Var16 (snoc16 g b) a)
 -> Var16 g a

vz16 : {g:_}->{a:_} -> Var16 (snoc16 g a) a
vz16 = \ var, vz16, vs => vz16

vs16 : {g:_}->{b:_}->{a:_} -> Var16 g a -> Var16 (snoc16 g b) a
vs16 = \ x, var, vz16, vs16 => vs16 (x var vz16 vs16)

Tm16 : Con16 -> Ty16-> Type
Tm16 = \ g, a =>
    (Tm16    : Con16 -> Ty16-> Type)
 -> (var   : {g:_}->{a:_}-> Var16 g a -> Tm16 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm16 (snoc16 g a) b -> Tm16 g (arr16 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm16 g (arr16 a b) -> Tm16 g a -> Tm16 g b)
 -> (tt    : {g:_}-> Tm16 g top16)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm16 g a -> Tm16 g b -> Tm16 g (prod16 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm16 g (prod16 a b) -> Tm16 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm16 g (prod16 a b) -> Tm16 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm16 g a -> Tm16 g (sum16 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm16 g b -> Tm16 g (sum16 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm16 g (sum16 a b) -> Tm16 g (arr16 a c) -> Tm16 g (arr16 b c) -> Tm16 g c)
 -> (zero  : {g:_}-> Tm16 g nat16)
 -> (suc   : {g:_}-> Tm16 g nat16 -> Tm16 g nat16)
 -> (rec   : {g:_}->{a:_} -> Tm16 g nat16 -> Tm16 g (arr16 nat16 (arr16 a a)) -> Tm16 g a -> Tm16 g a)
 -> Tm16 g a

var16 : {g:_}->{a:_} -> Var16 g a -> Tm16 g a
var16 = \ x, tm, var16, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var16 x

lam16 : {g:_}->{a:_}->{b:_}-> Tm16 (snoc16 g a) b -> Tm16 g (arr16 a b)
lam16 = \ t, tm, var16, lam16, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam16 (t tm var16 lam16 app tt pair fst snd left right split zero suc rec)

app16 : {g:_}->{a:_}->{b:_} -> Tm16 g (arr16 a b) -> Tm16 g a -> Tm16 g b
app16 = \ t, u, tm, var16, lam16, app16, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app16 (t tm var16 lam16 app16 tt pair fst snd left right split zero suc rec)
         (u tm var16 lam16 app16 tt pair fst snd left right split zero suc rec)

tt16 : {g:_} -> Tm16 g Main.top16
tt16 = \ tm, var16, lam16, app16, tt16, pair, fst, snd, left, right, split, zero, suc, rec => tt16

pair16 : {g:_}->{a:_}->{b:_} -> Tm16 g a -> Tm16 g b -> Tm16 g (prod16 a b)
pair16 = \ t, u, tm, var16, lam16, app16, tt16, pair16, fst, snd, left, right, split, zero, suc, rec =>
     pair16 (t tm var16 lam16 app16 tt16 pair16 fst snd left right split zero suc rec)
          (u tm var16 lam16 app16 tt16 pair16 fst snd left right split zero suc rec)

fst16 : {g:_}->{a:_}->{b:_}-> Tm16 g (prod16 a b) -> Tm16 g a
fst16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd, left, right, split, zero, suc, rec =>
     fst16 (t tm var16 lam16 app16 tt16 pair16 fst16 snd left right split zero suc rec)

snd16 : {g:_}->{a:_}->{b:_} -> Tm16 g (prod16 a b) -> Tm16 g b
snd16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left, right, split, zero, suc, rec =>
     snd16 (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left right split zero suc rec)

left16 : {g:_}->{a:_}->{b:_} -> Tm16 g a -> Tm16 g (sum16 a b)
left16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right, split, zero, suc, rec =>
     left16 (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right split zero suc rec)

right16 : {g:_}->{a:_}->{b:_} -> Tm16 g b -> Tm16 g (sum16 a b)
right16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split, zero, suc, rec =>
     right16 (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split zero suc rec)

split16 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm16 g (sum16 a b) -> Tm16 g (arr16 a c) -> Tm16 g (arr16 b c) -> Tm16 g c
split16 = \ t, u, v, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split16, zero, suc, rec =>
     split16 (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero suc rec)
          (u tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero suc rec)
          (v tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero suc rec)

zero16 : {g:_} -> Tm16 g Main.nat16
zero16 = \ tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split16, zero16, suc, rec => zero16

suc16 : {g:_} -> Tm16 g Main.nat16 -> Tm16 g Main.nat16
suc16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split16, zero16, suc16, rec =>
   suc16 (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero16 suc16 rec)

rec16 : {g:_}->{a:_} -> Tm16 g Main.nat16 -> Tm16 g (arr16 Main.nat16 (arr16 a a)) -> Tm16 g a -> Tm16 g a
rec16 = \ t, u, v, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split16, zero16, suc16, rec16 =>
     rec16 (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero16 suc16 rec16)
         (u tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero16 suc16 rec16)
         (v tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero16 suc16 rec16)

v016 : {g:_}->{a:_} -> Tm16 (snoc16 g a) a
v016 = var16 vz16

v116 : {g:_}->{a:_}->{b:_} -> Tm16 (snoc16 (snoc16 g a) b) a
v116 = var16 (vs16 vz16)

v216 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm16 (snoc16 (snoc16 (snoc16 g a) b) c) a
v216 = var16 (vs16 (vs16 vz16))

v316 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm16 (snoc16 (snoc16 (snoc16 (snoc16 g a) b) c) d) a
v316 = var16 (vs16 (vs16 (vs16 vz16)))

tbool16 : Ty16
tbool16 = sum16 top16 top16

ttrue16 : {g:_} -> Tm16 g Main.tbool16
ttrue16 = left16 tt16

tfalse16 : {g:_} -> Tm16 g Main.tbool16
tfalse16 = right16 tt16

ifthenelse16 : {g:_}->{a:_} -> Tm16 g (arr16 Main.tbool16 (arr16 a (arr16 a a)))
ifthenelse16 = lam16 (lam16 (lam16 (split16 v216 (lam16 v216) (lam16 v116))))

times416 : {g:_}->{a:_} -> Tm16 g (arr16 (arr16 a a) (arr16 a a))
times416  = lam16 (lam16 (app16 v116 (app16 v116 (app16 v116 (app16 v116 v016)))))

add16 : {g:_} -> Tm16 g (arr16 Main.nat16 (arr16 Main.nat16 Main.nat16))
add16 = lam16 (rec16 v016
       (lam16 (lam16 (lam16 (suc16 (app16 v116 v016)))))
       (lam16 v016))

mul16 : {g:_} -> Tm16 g (arr16 Main.nat16 (arr16 Main.nat16 Main.nat16))
mul16 = lam16 (rec16 v016
       (lam16 (lam16 (lam16 (app16 (app16 add16 (app16 v116 v016)) v016))))
       (lam16 zero16))

fact16 : {g:_} -> Tm16 g (arr16 Main.nat16 Main.nat16)
fact16 = lam16 (rec16 v016 (lam16 (lam16 (app16 (app16 mul16 (suc16 v116)) v016)))
                 (suc16 zero16))

Ty17 : Type
Ty17 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat17 : Ty17
nat17 = \ _, nat17, _, _, _, _, _ => nat17
top17 : Ty17
top17 = \ _, _, top17, _, _, _, _ => top17
bot17 : Ty17
bot17 = \ _, _, _, bot17, _, _, _ => bot17

arr17 : Ty17-> Ty17-> Ty17
arr17 = \ a, b, ty, nat17, top17, bot17, arr17, prod, sum =>
     arr17 (a ty nat17 top17 bot17 arr17 prod sum) (b ty nat17 top17 bot17 arr17 prod sum)

prod17 : Ty17-> Ty17-> Ty17
prod17 = \ a, b, ty, nat17, top17, bot17, arr17, prod17, sum =>
     prod17 (a ty nat17 top17 bot17 arr17 prod17 sum) (b ty nat17 top17 bot17 arr17 prod17 sum)

sum17 : Ty17-> Ty17-> Ty17
sum17 = \ a, b, ty, nat17, top17, bot17, arr17, prod17, sum17 =>
     sum17 (a ty nat17 top17 bot17 arr17 prod17 sum17) (b ty nat17 top17 bot17 arr17 prod17 sum17)

Con17 : Type
Con17 = (Con17 : Type)
 -> (nil  : Con17)
 -> (snoc : Con17 -> Ty17-> Con17)
 -> Con17

nil17 : Con17
nil17 = \ con, nil17, snoc => nil17

snoc17 : Con17 -> Ty17-> Con17
snoc17 = \ g, a, con, nil17, snoc17 => snoc17 (g con nil17 snoc17) a

Var17 : Con17 -> Ty17-> Type
Var17 = \ g, a =>
    (Var17 : Con17 -> Ty17-> Type)
 -> (vz  : {g:_}->{a:_} -> Var17 (snoc17 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var17 g a -> Var17 (snoc17 g b) a)
 -> Var17 g a

vz17 : {g:_}->{a:_} -> Var17 (snoc17 g a) a
vz17 = \ var, vz17, vs => vz17

vs17 : {g:_}->{b:_}->{a:_} -> Var17 g a -> Var17 (snoc17 g b) a
vs17 = \ x, var, vz17, vs17 => vs17 (x var vz17 vs17)

Tm17 : Con17 -> Ty17-> Type
Tm17 = \ g, a =>
    (Tm17    : Con17 -> Ty17-> Type)
 -> (var   : {g:_}->{a:_}-> Var17 g a -> Tm17 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm17 (snoc17 g a) b -> Tm17 g (arr17 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm17 g (arr17 a b) -> Tm17 g a -> Tm17 g b)
 -> (tt    : {g:_}-> Tm17 g top17)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm17 g a -> Tm17 g b -> Tm17 g (prod17 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm17 g (prod17 a b) -> Tm17 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm17 g (prod17 a b) -> Tm17 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm17 g a -> Tm17 g (sum17 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm17 g b -> Tm17 g (sum17 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm17 g (sum17 a b) -> Tm17 g (arr17 a c) -> Tm17 g (arr17 b c) -> Tm17 g c)
 -> (zero  : {g:_}-> Tm17 g nat17)
 -> (suc   : {g:_}-> Tm17 g nat17 -> Tm17 g nat17)
 -> (rec   : {g:_}->{a:_} -> Tm17 g nat17 -> Tm17 g (arr17 nat17 (arr17 a a)) -> Tm17 g a -> Tm17 g a)
 -> Tm17 g a

var17 : {g:_}->{a:_} -> Var17 g a -> Tm17 g a
var17 = \ x, tm, var17, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var17 x

lam17 : {g:_}->{a:_}->{b:_}-> Tm17 (snoc17 g a) b -> Tm17 g (arr17 a b)
lam17 = \ t, tm, var17, lam17, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam17 (t tm var17 lam17 app tt pair fst snd left right split zero suc rec)

app17 : {g:_}->{a:_}->{b:_} -> Tm17 g (arr17 a b) -> Tm17 g a -> Tm17 g b
app17 = \ t, u, tm, var17, lam17, app17, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app17 (t tm var17 lam17 app17 tt pair fst snd left right split zero suc rec)
         (u tm var17 lam17 app17 tt pair fst snd left right split zero suc rec)

tt17 : {g:_} -> Tm17 g Main.top17
tt17 = \ tm, var17, lam17, app17, tt17, pair, fst, snd, left, right, split, zero, suc, rec => tt17

pair17 : {g:_}->{a:_}->{b:_} -> Tm17 g a -> Tm17 g b -> Tm17 g (prod17 a b)
pair17 = \ t, u, tm, var17, lam17, app17, tt17, pair17, fst, snd, left, right, split, zero, suc, rec =>
     pair17 (t tm var17 lam17 app17 tt17 pair17 fst snd left right split zero suc rec)
          (u tm var17 lam17 app17 tt17 pair17 fst snd left right split zero suc rec)

fst17 : {g:_}->{a:_}->{b:_}-> Tm17 g (prod17 a b) -> Tm17 g a
fst17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd, left, right, split, zero, suc, rec =>
     fst17 (t tm var17 lam17 app17 tt17 pair17 fst17 snd left right split zero suc rec)

snd17 : {g:_}->{a:_}->{b:_} -> Tm17 g (prod17 a b) -> Tm17 g b
snd17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left, right, split, zero, suc, rec =>
     snd17 (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left right split zero suc rec)

left17 : {g:_}->{a:_}->{b:_} -> Tm17 g a -> Tm17 g (sum17 a b)
left17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right, split, zero, suc, rec =>
     left17 (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right split zero suc rec)

right17 : {g:_}->{a:_}->{b:_} -> Tm17 g b -> Tm17 g (sum17 a b)
right17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split, zero, suc, rec =>
     right17 (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split zero suc rec)

split17 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm17 g (sum17 a b) -> Tm17 g (arr17 a c) -> Tm17 g (arr17 b c) -> Tm17 g c
split17 = \ t, u, v, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split17, zero, suc, rec =>
     split17 (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero suc rec)
          (u tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero suc rec)
          (v tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero suc rec)

zero17 : {g:_} -> Tm17 g Main.nat17
zero17 = \ tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split17, zero17, suc, rec => zero17

suc17 : {g:_} -> Tm17 g Main.nat17 -> Tm17 g Main.nat17
suc17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split17, zero17, suc17, rec =>
   suc17 (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero17 suc17 rec)

rec17 : {g:_}->{a:_} -> Tm17 g Main.nat17 -> Tm17 g (arr17 Main.nat17 (arr17 a a)) -> Tm17 g a -> Tm17 g a
rec17 = \ t, u, v, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split17, zero17, suc17, rec17 =>
     rec17 (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero17 suc17 rec17)
         (u tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero17 suc17 rec17)
         (v tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero17 suc17 rec17)

v017 : {g:_}->{a:_} -> Tm17 (snoc17 g a) a
v017 = var17 vz17

v117 : {g:_}->{a:_}->{b:_} -> Tm17 (snoc17 (snoc17 g a) b) a
v117 = var17 (vs17 vz17)

v217 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm17 (snoc17 (snoc17 (snoc17 g a) b) c) a
v217 = var17 (vs17 (vs17 vz17))

v317 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm17 (snoc17 (snoc17 (snoc17 (snoc17 g a) b) c) d) a
v317 = var17 (vs17 (vs17 (vs17 vz17)))

tbool17 : Ty17
tbool17 = sum17 top17 top17

ttrue17 : {g:_} -> Tm17 g Main.tbool17
ttrue17 = left17 tt17

tfalse17 : {g:_} -> Tm17 g Main.tbool17
tfalse17 = right17 tt17

ifthenelse17 : {g:_}->{a:_} -> Tm17 g (arr17 Main.tbool17 (arr17 a (arr17 a a)))
ifthenelse17 = lam17 (lam17 (lam17 (split17 v217 (lam17 v217) (lam17 v117))))

times417 : {g:_}->{a:_} -> Tm17 g (arr17 (arr17 a a) (arr17 a a))
times417  = lam17 (lam17 (app17 v117 (app17 v117 (app17 v117 (app17 v117 v017)))))

add17 : {g:_} -> Tm17 g (arr17 Main.nat17 (arr17 Main.nat17 Main.nat17))
add17 = lam17 (rec17 v017
       (lam17 (lam17 (lam17 (suc17 (app17 v117 v017)))))
       (lam17 v017))

mul17 : {g:_} -> Tm17 g (arr17 Main.nat17 (arr17 Main.nat17 Main.nat17))
mul17 = lam17 (rec17 v017
       (lam17 (lam17 (lam17 (app17 (app17 add17 (app17 v117 v017)) v017))))
       (lam17 zero17))

fact17 : {g:_} -> Tm17 g (arr17 Main.nat17 Main.nat17)
fact17 = lam17 (rec17 v017 (lam17 (lam17 (app17 (app17 mul17 (suc17 v117)) v017)))
                 (suc17 zero17))

Ty18 : Type
Ty18 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat18 : Ty18
nat18 = \ _, nat18, _, _, _, _, _ => nat18
top18 : Ty18
top18 = \ _, _, top18, _, _, _, _ => top18
bot18 : Ty18
bot18 = \ _, _, _, bot18, _, _, _ => bot18

arr18 : Ty18-> Ty18-> Ty18
arr18 = \ a, b, ty, nat18, top18, bot18, arr18, prod, sum =>
     arr18 (a ty nat18 top18 bot18 arr18 prod sum) (b ty nat18 top18 bot18 arr18 prod sum)

prod18 : Ty18-> Ty18-> Ty18
prod18 = \ a, b, ty, nat18, top18, bot18, arr18, prod18, sum =>
     prod18 (a ty nat18 top18 bot18 arr18 prod18 sum) (b ty nat18 top18 bot18 arr18 prod18 sum)

sum18 : Ty18-> Ty18-> Ty18
sum18 = \ a, b, ty, nat18, top18, bot18, arr18, prod18, sum18 =>
     sum18 (a ty nat18 top18 bot18 arr18 prod18 sum18) (b ty nat18 top18 bot18 arr18 prod18 sum18)

Con18 : Type
Con18 = (Con18 : Type)
 -> (nil  : Con18)
 -> (snoc : Con18 -> Ty18-> Con18)
 -> Con18

nil18 : Con18
nil18 = \ con, nil18, snoc => nil18

snoc18 : Con18 -> Ty18-> Con18
snoc18 = \ g, a, con, nil18, snoc18 => snoc18 (g con nil18 snoc18) a

Var18 : Con18 -> Ty18-> Type
Var18 = \ g, a =>
    (Var18 : Con18 -> Ty18-> Type)
 -> (vz  : {g:_}->{a:_} -> Var18 (snoc18 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var18 g a -> Var18 (snoc18 g b) a)
 -> Var18 g a

vz18 : {g:_}->{a:_} -> Var18 (snoc18 g a) a
vz18 = \ var, vz18, vs => vz18

vs18 : {g:_}->{b:_}->{a:_} -> Var18 g a -> Var18 (snoc18 g b) a
vs18 = \ x, var, vz18, vs18 => vs18 (x var vz18 vs18)

Tm18 : Con18 -> Ty18-> Type
Tm18 = \ g, a =>
    (Tm18    : Con18 -> Ty18-> Type)
 -> (var   : {g:_}->{a:_}-> Var18 g a -> Tm18 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm18 (snoc18 g a) b -> Tm18 g (arr18 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm18 g (arr18 a b) -> Tm18 g a -> Tm18 g b)
 -> (tt    : {g:_}-> Tm18 g top18)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm18 g a -> Tm18 g b -> Tm18 g (prod18 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm18 g (prod18 a b) -> Tm18 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm18 g (prod18 a b) -> Tm18 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm18 g a -> Tm18 g (sum18 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm18 g b -> Tm18 g (sum18 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm18 g (sum18 a b) -> Tm18 g (arr18 a c) -> Tm18 g (arr18 b c) -> Tm18 g c)
 -> (zero  : {g:_}-> Tm18 g nat18)
 -> (suc   : {g:_}-> Tm18 g nat18 -> Tm18 g nat18)
 -> (rec   : {g:_}->{a:_} -> Tm18 g nat18 -> Tm18 g (arr18 nat18 (arr18 a a)) -> Tm18 g a -> Tm18 g a)
 -> Tm18 g a

var18 : {g:_}->{a:_} -> Var18 g a -> Tm18 g a
var18 = \ x, tm, var18, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var18 x

lam18 : {g:_}->{a:_}->{b:_}-> Tm18 (snoc18 g a) b -> Tm18 g (arr18 a b)
lam18 = \ t, tm, var18, lam18, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam18 (t tm var18 lam18 app tt pair fst snd left right split zero suc rec)

app18 : {g:_}->{a:_}->{b:_} -> Tm18 g (arr18 a b) -> Tm18 g a -> Tm18 g b
app18 = \ t, u, tm, var18, lam18, app18, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app18 (t tm var18 lam18 app18 tt pair fst snd left right split zero suc rec)
         (u tm var18 lam18 app18 tt pair fst snd left right split zero suc rec)

tt18 : {g:_} -> Tm18 g Main.top18
tt18 = \ tm, var18, lam18, app18, tt18, pair, fst, snd, left, right, split, zero, suc, rec => tt18

pair18 : {g:_}->{a:_}->{b:_} -> Tm18 g a -> Tm18 g b -> Tm18 g (prod18 a b)
pair18 = \ t, u, tm, var18, lam18, app18, tt18, pair18, fst, snd, left, right, split, zero, suc, rec =>
     pair18 (t tm var18 lam18 app18 tt18 pair18 fst snd left right split zero suc rec)
          (u tm var18 lam18 app18 tt18 pair18 fst snd left right split zero suc rec)

fst18 : {g:_}->{a:_}->{b:_}-> Tm18 g (prod18 a b) -> Tm18 g a
fst18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd, left, right, split, zero, suc, rec =>
     fst18 (t tm var18 lam18 app18 tt18 pair18 fst18 snd left right split zero suc rec)

snd18 : {g:_}->{a:_}->{b:_} -> Tm18 g (prod18 a b) -> Tm18 g b
snd18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left, right, split, zero, suc, rec =>
     snd18 (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left right split zero suc rec)

left18 : {g:_}->{a:_}->{b:_} -> Tm18 g a -> Tm18 g (sum18 a b)
left18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right, split, zero, suc, rec =>
     left18 (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right split zero suc rec)

right18 : {g:_}->{a:_}->{b:_} -> Tm18 g b -> Tm18 g (sum18 a b)
right18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split, zero, suc, rec =>
     right18 (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split zero suc rec)

split18 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm18 g (sum18 a b) -> Tm18 g (arr18 a c) -> Tm18 g (arr18 b c) -> Tm18 g c
split18 = \ t, u, v, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split18, zero, suc, rec =>
     split18 (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero suc rec)
          (u tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero suc rec)
          (v tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero suc rec)

zero18 : {g:_} -> Tm18 g Main.nat18
zero18 = \ tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split18, zero18, suc, rec => zero18

suc18 : {g:_} -> Tm18 g Main.nat18 -> Tm18 g Main.nat18
suc18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split18, zero18, suc18, rec =>
   suc18 (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero18 suc18 rec)

rec18 : {g:_}->{a:_} -> Tm18 g Main.nat18 -> Tm18 g (arr18 Main.nat18 (arr18 a a)) -> Tm18 g a -> Tm18 g a
rec18 = \ t, u, v, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split18, zero18, suc18, rec18 =>
     rec18 (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero18 suc18 rec18)
         (u tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero18 suc18 rec18)
         (v tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero18 suc18 rec18)

v018 : {g:_}->{a:_} -> Tm18 (snoc18 g a) a
v018 = var18 vz18

v118 : {g:_}->{a:_}->{b:_} -> Tm18 (snoc18 (snoc18 g a) b) a
v118 = var18 (vs18 vz18)

v218 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm18 (snoc18 (snoc18 (snoc18 g a) b) c) a
v218 = var18 (vs18 (vs18 vz18))

v318 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm18 (snoc18 (snoc18 (snoc18 (snoc18 g a) b) c) d) a
v318 = var18 (vs18 (vs18 (vs18 vz18)))

tbool18 : Ty18
tbool18 = sum18 top18 top18

ttrue18 : {g:_} -> Tm18 g Main.tbool18
ttrue18 = left18 tt18

tfalse18 : {g:_} -> Tm18 g Main.tbool18
tfalse18 = right18 tt18

ifthenelse18 : {g:_}->{a:_} -> Tm18 g (arr18 Main.tbool18 (arr18 a (arr18 a a)))
ifthenelse18 = lam18 (lam18 (lam18 (split18 v218 (lam18 v218) (lam18 v118))))

times418 : {g:_}->{a:_} -> Tm18 g (arr18 (arr18 a a) (arr18 a a))
times418  = lam18 (lam18 (app18 v118 (app18 v118 (app18 v118 (app18 v118 v018)))))

add18 : {g:_} -> Tm18 g (arr18 Main.nat18 (arr18 Main.nat18 Main.nat18))
add18 = lam18 (rec18 v018
       (lam18 (lam18 (lam18 (suc18 (app18 v118 v018)))))
       (lam18 v018))

mul18 : {g:_} -> Tm18 g (arr18 Main.nat18 (arr18 Main.nat18 Main.nat18))
mul18 = lam18 (rec18 v018
       (lam18 (lam18 (lam18 (app18 (app18 add18 (app18 v118 v018)) v018))))
       (lam18 zero18))

fact18 : {g:_} -> Tm18 g (arr18 Main.nat18 Main.nat18)
fact18 = lam18 (rec18 v018 (lam18 (lam18 (app18 (app18 mul18 (suc18 v118)) v018)))
                 (suc18 zero18))

Ty19 : Type
Ty19 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat19 : Ty19
nat19 = \ _, nat19, _, _, _, _, _ => nat19
top19 : Ty19
top19 = \ _, _, top19, _, _, _, _ => top19
bot19 : Ty19
bot19 = \ _, _, _, bot19, _, _, _ => bot19

arr19 : Ty19-> Ty19-> Ty19
arr19 = \ a, b, ty, nat19, top19, bot19, arr19, prod, sum =>
     arr19 (a ty nat19 top19 bot19 arr19 prod sum) (b ty nat19 top19 bot19 arr19 prod sum)

prod19 : Ty19-> Ty19-> Ty19
prod19 = \ a, b, ty, nat19, top19, bot19, arr19, prod19, sum =>
     prod19 (a ty nat19 top19 bot19 arr19 prod19 sum) (b ty nat19 top19 bot19 arr19 prod19 sum)

sum19 : Ty19-> Ty19-> Ty19
sum19 = \ a, b, ty, nat19, top19, bot19, arr19, prod19, sum19 =>
     sum19 (a ty nat19 top19 bot19 arr19 prod19 sum19) (b ty nat19 top19 bot19 arr19 prod19 sum19)

Con19 : Type
Con19 = (Con19 : Type)
 -> (nil  : Con19)
 -> (snoc : Con19 -> Ty19-> Con19)
 -> Con19

nil19 : Con19
nil19 = \ con, nil19, snoc => nil19

snoc19 : Con19 -> Ty19-> Con19
snoc19 = \ g, a, con, nil19, snoc19 => snoc19 (g con nil19 snoc19) a

Var19 : Con19 -> Ty19-> Type
Var19 = \ g, a =>
    (Var19 : Con19 -> Ty19-> Type)
 -> (vz  : {g:_}->{a:_} -> Var19 (snoc19 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var19 g a -> Var19 (snoc19 g b) a)
 -> Var19 g a

vz19 : {g:_}->{a:_} -> Var19 (snoc19 g a) a
vz19 = \ var, vz19, vs => vz19

vs19 : {g:_}->{b:_}->{a:_} -> Var19 g a -> Var19 (snoc19 g b) a
vs19 = \ x, var, vz19, vs19 => vs19 (x var vz19 vs19)

Tm19 : Con19 -> Ty19-> Type
Tm19 = \ g, a =>
    (Tm19    : Con19 -> Ty19-> Type)
 -> (var   : {g:_}->{a:_}-> Var19 g a -> Tm19 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm19 (snoc19 g a) b -> Tm19 g (arr19 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm19 g (arr19 a b) -> Tm19 g a -> Tm19 g b)
 -> (tt    : {g:_}-> Tm19 g top19)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm19 g a -> Tm19 g b -> Tm19 g (prod19 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm19 g (prod19 a b) -> Tm19 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm19 g (prod19 a b) -> Tm19 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm19 g a -> Tm19 g (sum19 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm19 g b -> Tm19 g (sum19 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm19 g (sum19 a b) -> Tm19 g (arr19 a c) -> Tm19 g (arr19 b c) -> Tm19 g c)
 -> (zero  : {g:_}-> Tm19 g nat19)
 -> (suc   : {g:_}-> Tm19 g nat19 -> Tm19 g nat19)
 -> (rec   : {g:_}->{a:_} -> Tm19 g nat19 -> Tm19 g (arr19 nat19 (arr19 a a)) -> Tm19 g a -> Tm19 g a)
 -> Tm19 g a

var19 : {g:_}->{a:_} -> Var19 g a -> Tm19 g a
var19 = \ x, tm, var19, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var19 x

lam19 : {g:_}->{a:_}->{b:_}-> Tm19 (snoc19 g a) b -> Tm19 g (arr19 a b)
lam19 = \ t, tm, var19, lam19, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam19 (t tm var19 lam19 app tt pair fst snd left right split zero suc rec)

app19 : {g:_}->{a:_}->{b:_} -> Tm19 g (arr19 a b) -> Tm19 g a -> Tm19 g b
app19 = \ t, u, tm, var19, lam19, app19, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app19 (t tm var19 lam19 app19 tt pair fst snd left right split zero suc rec)
         (u tm var19 lam19 app19 tt pair fst snd left right split zero suc rec)

tt19 : {g:_} -> Tm19 g Main.top19
tt19 = \ tm, var19, lam19, app19, tt19, pair, fst, snd, left, right, split, zero, suc, rec => tt19

pair19 : {g:_}->{a:_}->{b:_} -> Tm19 g a -> Tm19 g b -> Tm19 g (prod19 a b)
pair19 = \ t, u, tm, var19, lam19, app19, tt19, pair19, fst, snd, left, right, split, zero, suc, rec =>
     pair19 (t tm var19 lam19 app19 tt19 pair19 fst snd left right split zero suc rec)
          (u tm var19 lam19 app19 tt19 pair19 fst snd left right split zero suc rec)

fst19 : {g:_}->{a:_}->{b:_}-> Tm19 g (prod19 a b) -> Tm19 g a
fst19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd, left, right, split, zero, suc, rec =>
     fst19 (t tm var19 lam19 app19 tt19 pair19 fst19 snd left right split zero suc rec)

snd19 : {g:_}->{a:_}->{b:_} -> Tm19 g (prod19 a b) -> Tm19 g b
snd19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left, right, split, zero, suc, rec =>
     snd19 (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left right split zero suc rec)

left19 : {g:_}->{a:_}->{b:_} -> Tm19 g a -> Tm19 g (sum19 a b)
left19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right, split, zero, suc, rec =>
     left19 (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right split zero suc rec)

right19 : {g:_}->{a:_}->{b:_} -> Tm19 g b -> Tm19 g (sum19 a b)
right19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split, zero, suc, rec =>
     right19 (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split zero suc rec)

split19 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm19 g (sum19 a b) -> Tm19 g (arr19 a c) -> Tm19 g (arr19 b c) -> Tm19 g c
split19 = \ t, u, v, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split19, zero, suc, rec =>
     split19 (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero suc rec)
          (u tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero suc rec)
          (v tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero suc rec)

zero19 : {g:_} -> Tm19 g Main.nat19
zero19 = \ tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split19, zero19, suc, rec => zero19

suc19 : {g:_} -> Tm19 g Main.nat19 -> Tm19 g Main.nat19
suc19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split19, zero19, suc19, rec =>
   suc19 (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero19 suc19 rec)

rec19 : {g:_}->{a:_} -> Tm19 g Main.nat19 -> Tm19 g (arr19 Main.nat19 (arr19 a a)) -> Tm19 g a -> Tm19 g a
rec19 = \ t, u, v, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split19, zero19, suc19, rec19 =>
     rec19 (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero19 suc19 rec19)
         (u tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero19 suc19 rec19)
         (v tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero19 suc19 rec19)

v019 : {g:_}->{a:_} -> Tm19 (snoc19 g a) a
v019 = var19 vz19

v119 : {g:_}->{a:_}->{b:_} -> Tm19 (snoc19 (snoc19 g a) b) a
v119 = var19 (vs19 vz19)

v219 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm19 (snoc19 (snoc19 (snoc19 g a) b) c) a
v219 = var19 (vs19 (vs19 vz19))

v319 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm19 (snoc19 (snoc19 (snoc19 (snoc19 g a) b) c) d) a
v319 = var19 (vs19 (vs19 (vs19 vz19)))

tbool19 : Ty19
tbool19 = sum19 top19 top19

ttrue19 : {g:_} -> Tm19 g Main.tbool19
ttrue19 = left19 tt19

tfalse19 : {g:_} -> Tm19 g Main.tbool19
tfalse19 = right19 tt19

ifthenelse19 : {g:_}->{a:_} -> Tm19 g (arr19 Main.tbool19 (arr19 a (arr19 a a)))
ifthenelse19 = lam19 (lam19 (lam19 (split19 v219 (lam19 v219) (lam19 v119))))

times419 : {g:_}->{a:_} -> Tm19 g (arr19 (arr19 a a) (arr19 a a))
times419  = lam19 (lam19 (app19 v119 (app19 v119 (app19 v119 (app19 v119 v019)))))

add19 : {g:_} -> Tm19 g (arr19 Main.nat19 (arr19 Main.nat19 Main.nat19))
add19 = lam19 (rec19 v019
       (lam19 (lam19 (lam19 (suc19 (app19 v119 v019)))))
       (lam19 v019))

mul19 : {g:_} -> Tm19 g (arr19 Main.nat19 (arr19 Main.nat19 Main.nat19))
mul19 = lam19 (rec19 v019
       (lam19 (lam19 (lam19 (app19 (app19 add19 (app19 v119 v019)) v019))))
       (lam19 zero19))

fact19 : {g:_} -> Tm19 g (arr19 Main.nat19 Main.nat19)
fact19 = lam19 (rec19 v019 (lam19 (lam19 (app19 (app19 mul19 (suc19 v119)) v019)))
                 (suc19 zero19))

Ty20 : Type
Ty20 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat20 : Ty20
nat20 = \ _, nat20, _, _, _, _, _ => nat20
top20 : Ty20
top20 = \ _, _, top20, _, _, _, _ => top20
bot20 : Ty20
bot20 = \ _, _, _, bot20, _, _, _ => bot20

arr20 : Ty20-> Ty20-> Ty20
arr20 = \ a, b, ty, nat20, top20, bot20, arr20, prod, sum =>
     arr20 (a ty nat20 top20 bot20 arr20 prod sum) (b ty nat20 top20 bot20 arr20 prod sum)

prod20 : Ty20-> Ty20-> Ty20
prod20 = \ a, b, ty, nat20, top20, bot20, arr20, prod20, sum =>
     prod20 (a ty nat20 top20 bot20 arr20 prod20 sum) (b ty nat20 top20 bot20 arr20 prod20 sum)

sum20 : Ty20-> Ty20-> Ty20
sum20 = \ a, b, ty, nat20, top20, bot20, arr20, prod20, sum20 =>
     sum20 (a ty nat20 top20 bot20 arr20 prod20 sum20) (b ty nat20 top20 bot20 arr20 prod20 sum20)

Con20 : Type
Con20 = (Con20 : Type)
 -> (nil  : Con20)
 -> (snoc : Con20 -> Ty20-> Con20)
 -> Con20

nil20 : Con20
nil20 = \ con, nil20, snoc => nil20

snoc20 : Con20 -> Ty20-> Con20
snoc20 = \ g, a, con, nil20, snoc20 => snoc20 (g con nil20 snoc20) a

Var20 : Con20 -> Ty20-> Type
Var20 = \ g, a =>
    (Var20 : Con20 -> Ty20-> Type)
 -> (vz  : {g:_}->{a:_} -> Var20 (snoc20 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var20 g a -> Var20 (snoc20 g b) a)
 -> Var20 g a

vz20 : {g:_}->{a:_} -> Var20 (snoc20 g a) a
vz20 = \ var, vz20, vs => vz20

vs20 : {g:_}->{b:_}->{a:_} -> Var20 g a -> Var20 (snoc20 g b) a
vs20 = \ x, var, vz20, vs20 => vs20 (x var vz20 vs20)

Tm20 : Con20 -> Ty20-> Type
Tm20 = \ g, a =>
    (Tm20    : Con20 -> Ty20-> Type)
 -> (var   : {g:_}->{a:_}-> Var20 g a -> Tm20 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm20 (snoc20 g a) b -> Tm20 g (arr20 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm20 g (arr20 a b) -> Tm20 g a -> Tm20 g b)
 -> (tt    : {g:_}-> Tm20 g top20)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm20 g a -> Tm20 g b -> Tm20 g (prod20 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm20 g (prod20 a b) -> Tm20 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm20 g (prod20 a b) -> Tm20 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm20 g a -> Tm20 g (sum20 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm20 g b -> Tm20 g (sum20 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm20 g (sum20 a b) -> Tm20 g (arr20 a c) -> Tm20 g (arr20 b c) -> Tm20 g c)
 -> (zero  : {g:_}-> Tm20 g nat20)
 -> (suc   : {g:_}-> Tm20 g nat20 -> Tm20 g nat20)
 -> (rec   : {g:_}->{a:_} -> Tm20 g nat20 -> Tm20 g (arr20 nat20 (arr20 a a)) -> Tm20 g a -> Tm20 g a)
 -> Tm20 g a

var20 : {g:_}->{a:_} -> Var20 g a -> Tm20 g a
var20 = \ x, tm, var20, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var20 x

lam20 : {g:_}->{a:_}->{b:_}-> Tm20 (snoc20 g a) b -> Tm20 g (arr20 a b)
lam20 = \ t, tm, var20, lam20, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam20 (t tm var20 lam20 app tt pair fst snd left right split zero suc rec)

app20 : {g:_}->{a:_}->{b:_} -> Tm20 g (arr20 a b) -> Tm20 g a -> Tm20 g b
app20 = \ t, u, tm, var20, lam20, app20, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app20 (t tm var20 lam20 app20 tt pair fst snd left right split zero suc rec)
         (u tm var20 lam20 app20 tt pair fst snd left right split zero suc rec)

tt20 : {g:_} -> Tm20 g Main.top20
tt20 = \ tm, var20, lam20, app20, tt20, pair, fst, snd, left, right, split, zero, suc, rec => tt20

pair20 : {g:_}->{a:_}->{b:_} -> Tm20 g a -> Tm20 g b -> Tm20 g (prod20 a b)
pair20 = \ t, u, tm, var20, lam20, app20, tt20, pair20, fst, snd, left, right, split, zero, suc, rec =>
     pair20 (t tm var20 lam20 app20 tt20 pair20 fst snd left right split zero suc rec)
          (u tm var20 lam20 app20 tt20 pair20 fst snd left right split zero suc rec)

fst20 : {g:_}->{a:_}->{b:_}-> Tm20 g (prod20 a b) -> Tm20 g a
fst20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd, left, right, split, zero, suc, rec =>
     fst20 (t tm var20 lam20 app20 tt20 pair20 fst20 snd left right split zero suc rec)

snd20 : {g:_}->{a:_}->{b:_} -> Tm20 g (prod20 a b) -> Tm20 g b
snd20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left, right, split, zero, suc, rec =>
     snd20 (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left right split zero suc rec)

left20 : {g:_}->{a:_}->{b:_} -> Tm20 g a -> Tm20 g (sum20 a b)
left20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right, split, zero, suc, rec =>
     left20 (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right split zero suc rec)

right20 : {g:_}->{a:_}->{b:_} -> Tm20 g b -> Tm20 g (sum20 a b)
right20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split, zero, suc, rec =>
     right20 (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split zero suc rec)

split20 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm20 g (sum20 a b) -> Tm20 g (arr20 a c) -> Tm20 g (arr20 b c) -> Tm20 g c
split20 = \ t, u, v, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split20, zero, suc, rec =>
     split20 (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero suc rec)
          (u tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero suc rec)
          (v tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero suc rec)

zero20 : {g:_} -> Tm20 g Main.nat20
zero20 = \ tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split20, zero20, suc, rec => zero20

suc20 : {g:_} -> Tm20 g Main.nat20 -> Tm20 g Main.nat20
suc20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split20, zero20, suc20, rec =>
   suc20 (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero20 suc20 rec)

rec20 : {g:_}->{a:_} -> Tm20 g Main.nat20 -> Tm20 g (arr20 Main.nat20 (arr20 a a)) -> Tm20 g a -> Tm20 g a
rec20 = \ t, u, v, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split20, zero20, suc20, rec20 =>
     rec20 (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero20 suc20 rec20)
         (u tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero20 suc20 rec20)
         (v tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero20 suc20 rec20)

v020 : {g:_}->{a:_} -> Tm20 (snoc20 g a) a
v020 = var20 vz20

v120 : {g:_}->{a:_}->{b:_} -> Tm20 (snoc20 (snoc20 g a) b) a
v120 = var20 (vs20 vz20)

v220 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm20 (snoc20 (snoc20 (snoc20 g a) b) c) a
v220 = var20 (vs20 (vs20 vz20))

v320 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm20 (snoc20 (snoc20 (snoc20 (snoc20 g a) b) c) d) a
v320 = var20 (vs20 (vs20 (vs20 vz20)))

tbool20 : Ty20
tbool20 = sum20 top20 top20

ttrue20 : {g:_} -> Tm20 g Main.tbool20
ttrue20 = left20 tt20

tfalse20 : {g:_} -> Tm20 g Main.tbool20
tfalse20 = right20 tt20

ifthenelse20 : {g:_}->{a:_} -> Tm20 g (arr20 Main.tbool20 (arr20 a (arr20 a a)))
ifthenelse20 = lam20 (lam20 (lam20 (split20 v220 (lam20 v220) (lam20 v120))))

times420 : {g:_}->{a:_} -> Tm20 g (arr20 (arr20 a a) (arr20 a a))
times420  = lam20 (lam20 (app20 v120 (app20 v120 (app20 v120 (app20 v120 v020)))))

add20 : {g:_} -> Tm20 g (arr20 Main.nat20 (arr20 Main.nat20 Main.nat20))
add20 = lam20 (rec20 v020
       (lam20 (lam20 (lam20 (suc20 (app20 v120 v020)))))
       (lam20 v020))

mul20 : {g:_} -> Tm20 g (arr20 Main.nat20 (arr20 Main.nat20 Main.nat20))
mul20 = lam20 (rec20 v020
       (lam20 (lam20 (lam20 (app20 (app20 add20 (app20 v120 v020)) v020))))
       (lam20 zero20))

fact20 : {g:_} -> Tm20 g (arr20 Main.nat20 Main.nat20)
fact20 = lam20 (rec20 v020 (lam20 (lam20 (app20 (app20 mul20 (suc20 v120)) v020)))
                 (suc20 zero20))

Ty21 : Type
Ty21 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat21 : Ty21
nat21 = \ _, nat21, _, _, _, _, _ => nat21
top21 : Ty21
top21 = \ _, _, top21, _, _, _, _ => top21
bot21 : Ty21
bot21 = \ _, _, _, bot21, _, _, _ => bot21

arr21 : Ty21-> Ty21-> Ty21
arr21 = \ a, b, ty, nat21, top21, bot21, arr21, prod, sum =>
     arr21 (a ty nat21 top21 bot21 arr21 prod sum) (b ty nat21 top21 bot21 arr21 prod sum)

prod21 : Ty21-> Ty21-> Ty21
prod21 = \ a, b, ty, nat21, top21, bot21, arr21, prod21, sum =>
     prod21 (a ty nat21 top21 bot21 arr21 prod21 sum) (b ty nat21 top21 bot21 arr21 prod21 sum)

sum21 : Ty21-> Ty21-> Ty21
sum21 = \ a, b, ty, nat21, top21, bot21, arr21, prod21, sum21 =>
     sum21 (a ty nat21 top21 bot21 arr21 prod21 sum21) (b ty nat21 top21 bot21 arr21 prod21 sum21)

Con21 : Type
Con21 = (Con21 : Type)
 -> (nil  : Con21)
 -> (snoc : Con21 -> Ty21-> Con21)
 -> Con21

nil21 : Con21
nil21 = \ con, nil21, snoc => nil21

snoc21 : Con21 -> Ty21-> Con21
snoc21 = \ g, a, con, nil21, snoc21 => snoc21 (g con nil21 snoc21) a

Var21 : Con21 -> Ty21-> Type
Var21 = \ g, a =>
    (Var21 : Con21 -> Ty21-> Type)
 -> (vz  : {g:_}->{a:_} -> Var21 (snoc21 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var21 g a -> Var21 (snoc21 g b) a)
 -> Var21 g a

vz21 : {g:_}->{a:_} -> Var21 (snoc21 g a) a
vz21 = \ var, vz21, vs => vz21

vs21 : {g:_}->{b:_}->{a:_} -> Var21 g a -> Var21 (snoc21 g b) a
vs21 = \ x, var, vz21, vs21 => vs21 (x var vz21 vs21)

Tm21 : Con21 -> Ty21-> Type
Tm21 = \ g, a =>
    (Tm21    : Con21 -> Ty21-> Type)
 -> (var   : {g:_}->{a:_}-> Var21 g a -> Tm21 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm21 (snoc21 g a) b -> Tm21 g (arr21 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm21 g (arr21 a b) -> Tm21 g a -> Tm21 g b)
 -> (tt    : {g:_}-> Tm21 g top21)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm21 g a -> Tm21 g b -> Tm21 g (prod21 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm21 g (prod21 a b) -> Tm21 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm21 g (prod21 a b) -> Tm21 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm21 g a -> Tm21 g (sum21 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm21 g b -> Tm21 g (sum21 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm21 g (sum21 a b) -> Tm21 g (arr21 a c) -> Tm21 g (arr21 b c) -> Tm21 g c)
 -> (zero  : {g:_}-> Tm21 g nat21)
 -> (suc   : {g:_}-> Tm21 g nat21 -> Tm21 g nat21)
 -> (rec   : {g:_}->{a:_} -> Tm21 g nat21 -> Tm21 g (arr21 nat21 (arr21 a a)) -> Tm21 g a -> Tm21 g a)
 -> Tm21 g a

var21 : {g:_}->{a:_} -> Var21 g a -> Tm21 g a
var21 = \ x, tm, var21, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var21 x

lam21 : {g:_}->{a:_}->{b:_}-> Tm21 (snoc21 g a) b -> Tm21 g (arr21 a b)
lam21 = \ t, tm, var21, lam21, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam21 (t tm var21 lam21 app tt pair fst snd left right split zero suc rec)

app21 : {g:_}->{a:_}->{b:_} -> Tm21 g (arr21 a b) -> Tm21 g a -> Tm21 g b
app21 = \ t, u, tm, var21, lam21, app21, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app21 (t tm var21 lam21 app21 tt pair fst snd left right split zero suc rec)
         (u tm var21 lam21 app21 tt pair fst snd left right split zero suc rec)

tt21 : {g:_} -> Tm21 g Main.top21
tt21 = \ tm, var21, lam21, app21, tt21, pair, fst, snd, left, right, split, zero, suc, rec => tt21

pair21 : {g:_}->{a:_}->{b:_} -> Tm21 g a -> Tm21 g b -> Tm21 g (prod21 a b)
pair21 = \ t, u, tm, var21, lam21, app21, tt21, pair21, fst, snd, left, right, split, zero, suc, rec =>
     pair21 (t tm var21 lam21 app21 tt21 pair21 fst snd left right split zero suc rec)
          (u tm var21 lam21 app21 tt21 pair21 fst snd left right split zero suc rec)

fst21 : {g:_}->{a:_}->{b:_}-> Tm21 g (prod21 a b) -> Tm21 g a
fst21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd, left, right, split, zero, suc, rec =>
     fst21 (t tm var21 lam21 app21 tt21 pair21 fst21 snd left right split zero suc rec)

snd21 : {g:_}->{a:_}->{b:_} -> Tm21 g (prod21 a b) -> Tm21 g b
snd21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left, right, split, zero, suc, rec =>
     snd21 (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left right split zero suc rec)

left21 : {g:_}->{a:_}->{b:_} -> Tm21 g a -> Tm21 g (sum21 a b)
left21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right, split, zero, suc, rec =>
     left21 (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right split zero suc rec)

right21 : {g:_}->{a:_}->{b:_} -> Tm21 g b -> Tm21 g (sum21 a b)
right21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split, zero, suc, rec =>
     right21 (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split zero suc rec)

split21 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm21 g (sum21 a b) -> Tm21 g (arr21 a c) -> Tm21 g (arr21 b c) -> Tm21 g c
split21 = \ t, u, v, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split21, zero, suc, rec =>
     split21 (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero suc rec)
          (u tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero suc rec)
          (v tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero suc rec)

zero21 : {g:_} -> Tm21 g Main.nat21
zero21 = \ tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split21, zero21, suc, rec => zero21

suc21 : {g:_} -> Tm21 g Main.nat21 -> Tm21 g Main.nat21
suc21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split21, zero21, suc21, rec =>
   suc21 (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero21 suc21 rec)

rec21 : {g:_}->{a:_} -> Tm21 g Main.nat21 -> Tm21 g (arr21 Main.nat21 (arr21 a a)) -> Tm21 g a -> Tm21 g a
rec21 = \ t, u, v, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split21, zero21, suc21, rec21 =>
     rec21 (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero21 suc21 rec21)
         (u tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero21 suc21 rec21)
         (v tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero21 suc21 rec21)

v021 : {g:_}->{a:_} -> Tm21 (snoc21 g a) a
v021 = var21 vz21

v121 : {g:_}->{a:_}->{b:_} -> Tm21 (snoc21 (snoc21 g a) b) a
v121 = var21 (vs21 vz21)

v221 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm21 (snoc21 (snoc21 (snoc21 g a) b) c) a
v221 = var21 (vs21 (vs21 vz21))

v321 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm21 (snoc21 (snoc21 (snoc21 (snoc21 g a) b) c) d) a
v321 = var21 (vs21 (vs21 (vs21 vz21)))

tbool21 : Ty21
tbool21 = sum21 top21 top21

ttrue21 : {g:_} -> Tm21 g Main.tbool21
ttrue21 = left21 tt21

tfalse21 : {g:_} -> Tm21 g Main.tbool21
tfalse21 = right21 tt21

ifthenelse21 : {g:_}->{a:_} -> Tm21 g (arr21 Main.tbool21 (arr21 a (arr21 a a)))
ifthenelse21 = lam21 (lam21 (lam21 (split21 v221 (lam21 v221) (lam21 v121))))

times421 : {g:_}->{a:_} -> Tm21 g (arr21 (arr21 a a) (arr21 a a))
times421  = lam21 (lam21 (app21 v121 (app21 v121 (app21 v121 (app21 v121 v021)))))

add21 : {g:_} -> Tm21 g (arr21 Main.nat21 (arr21 Main.nat21 Main.nat21))
add21 = lam21 (rec21 v021
       (lam21 (lam21 (lam21 (suc21 (app21 v121 v021)))))
       (lam21 v021))

mul21 : {g:_} -> Tm21 g (arr21 Main.nat21 (arr21 Main.nat21 Main.nat21))
mul21 = lam21 (rec21 v021
       (lam21 (lam21 (lam21 (app21 (app21 add21 (app21 v121 v021)) v021))))
       (lam21 zero21))

fact21 : {g:_} -> Tm21 g (arr21 Main.nat21 Main.nat21)
fact21 = lam21 (rec21 v021 (lam21 (lam21 (app21 (app21 mul21 (suc21 v121)) v021)))
                 (suc21 zero21))

Ty22 : Type
Ty22 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat22 : Ty22
nat22 = \ _, nat22, _, _, _, _, _ => nat22
top22 : Ty22
top22 = \ _, _, top22, _, _, _, _ => top22
bot22 : Ty22
bot22 = \ _, _, _, bot22, _, _, _ => bot22

arr22 : Ty22-> Ty22-> Ty22
arr22 = \ a, b, ty, nat22, top22, bot22, arr22, prod, sum =>
     arr22 (a ty nat22 top22 bot22 arr22 prod sum) (b ty nat22 top22 bot22 arr22 prod sum)

prod22 : Ty22-> Ty22-> Ty22
prod22 = \ a, b, ty, nat22, top22, bot22, arr22, prod22, sum =>
     prod22 (a ty nat22 top22 bot22 arr22 prod22 sum) (b ty nat22 top22 bot22 arr22 prod22 sum)

sum22 : Ty22-> Ty22-> Ty22
sum22 = \ a, b, ty, nat22, top22, bot22, arr22, prod22, sum22 =>
     sum22 (a ty nat22 top22 bot22 arr22 prod22 sum22) (b ty nat22 top22 bot22 arr22 prod22 sum22)

Con22 : Type
Con22 = (Con22 : Type)
 -> (nil  : Con22)
 -> (snoc : Con22 -> Ty22-> Con22)
 -> Con22

nil22 : Con22
nil22 = \ con, nil22, snoc => nil22

snoc22 : Con22 -> Ty22-> Con22
snoc22 = \ g, a, con, nil22, snoc22 => snoc22 (g con nil22 snoc22) a

Var22 : Con22 -> Ty22-> Type
Var22 = \ g, a =>
    (Var22 : Con22 -> Ty22-> Type)
 -> (vz  : {g:_}->{a:_} -> Var22 (snoc22 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var22 g a -> Var22 (snoc22 g b) a)
 -> Var22 g a

vz22 : {g:_}->{a:_} -> Var22 (snoc22 g a) a
vz22 = \ var, vz22, vs => vz22

vs22 : {g:_}->{b:_}->{a:_} -> Var22 g a -> Var22 (snoc22 g b) a
vs22 = \ x, var, vz22, vs22 => vs22 (x var vz22 vs22)

Tm22 : Con22 -> Ty22-> Type
Tm22 = \ g, a =>
    (Tm22    : Con22 -> Ty22-> Type)
 -> (var   : {g:_}->{a:_}-> Var22 g a -> Tm22 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm22 (snoc22 g a) b -> Tm22 g (arr22 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm22 g (arr22 a b) -> Tm22 g a -> Tm22 g b)
 -> (tt    : {g:_}-> Tm22 g top22)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm22 g a -> Tm22 g b -> Tm22 g (prod22 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm22 g (prod22 a b) -> Tm22 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm22 g (prod22 a b) -> Tm22 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm22 g a -> Tm22 g (sum22 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm22 g b -> Tm22 g (sum22 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm22 g (sum22 a b) -> Tm22 g (arr22 a c) -> Tm22 g (arr22 b c) -> Tm22 g c)
 -> (zero  : {g:_}-> Tm22 g nat22)
 -> (suc   : {g:_}-> Tm22 g nat22 -> Tm22 g nat22)
 -> (rec   : {g:_}->{a:_} -> Tm22 g nat22 -> Tm22 g (arr22 nat22 (arr22 a a)) -> Tm22 g a -> Tm22 g a)
 -> Tm22 g a

var22 : {g:_}->{a:_} -> Var22 g a -> Tm22 g a
var22 = \ x, tm, var22, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var22 x

lam22 : {g:_}->{a:_}->{b:_}-> Tm22 (snoc22 g a) b -> Tm22 g (arr22 a b)
lam22 = \ t, tm, var22, lam22, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam22 (t tm var22 lam22 app tt pair fst snd left right split zero suc rec)

app22 : {g:_}->{a:_}->{b:_} -> Tm22 g (arr22 a b) -> Tm22 g a -> Tm22 g b
app22 = \ t, u, tm, var22, lam22, app22, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app22 (t tm var22 lam22 app22 tt pair fst snd left right split zero suc rec)
         (u tm var22 lam22 app22 tt pair fst snd left right split zero suc rec)

tt22 : {g:_} -> Tm22 g Main.top22
tt22 = \ tm, var22, lam22, app22, tt22, pair, fst, snd, left, right, split, zero, suc, rec => tt22

pair22 : {g:_}->{a:_}->{b:_} -> Tm22 g a -> Tm22 g b -> Tm22 g (prod22 a b)
pair22 = \ t, u, tm, var22, lam22, app22, tt22, pair22, fst, snd, left, right, split, zero, suc, rec =>
     pair22 (t tm var22 lam22 app22 tt22 pair22 fst snd left right split zero suc rec)
          (u tm var22 lam22 app22 tt22 pair22 fst snd left right split zero suc rec)

fst22 : {g:_}->{a:_}->{b:_}-> Tm22 g (prod22 a b) -> Tm22 g a
fst22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd, left, right, split, zero, suc, rec =>
     fst22 (t tm var22 lam22 app22 tt22 pair22 fst22 snd left right split zero suc rec)

snd22 : {g:_}->{a:_}->{b:_} -> Tm22 g (prod22 a b) -> Tm22 g b
snd22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left, right, split, zero, suc, rec =>
     snd22 (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left right split zero suc rec)

left22 : {g:_}->{a:_}->{b:_} -> Tm22 g a -> Tm22 g (sum22 a b)
left22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right, split, zero, suc, rec =>
     left22 (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right split zero suc rec)

right22 : {g:_}->{a:_}->{b:_} -> Tm22 g b -> Tm22 g (sum22 a b)
right22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split, zero, suc, rec =>
     right22 (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split zero suc rec)

split22 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm22 g (sum22 a b) -> Tm22 g (arr22 a c) -> Tm22 g (arr22 b c) -> Tm22 g c
split22 = \ t, u, v, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split22, zero, suc, rec =>
     split22 (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero suc rec)
          (u tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero suc rec)
          (v tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero suc rec)

zero22 : {g:_} -> Tm22 g Main.nat22
zero22 = \ tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split22, zero22, suc, rec => zero22

suc22 : {g:_} -> Tm22 g Main.nat22 -> Tm22 g Main.nat22
suc22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split22, zero22, suc22, rec =>
   suc22 (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero22 suc22 rec)

rec22 : {g:_}->{a:_} -> Tm22 g Main.nat22 -> Tm22 g (arr22 Main.nat22 (arr22 a a)) -> Tm22 g a -> Tm22 g a
rec22 = \ t, u, v, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split22, zero22, suc22, rec22 =>
     rec22 (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero22 suc22 rec22)
         (u tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero22 suc22 rec22)
         (v tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero22 suc22 rec22)

v022 : {g:_}->{a:_} -> Tm22 (snoc22 g a) a
v022 = var22 vz22

v122 : {g:_}->{a:_}->{b:_} -> Tm22 (snoc22 (snoc22 g a) b) a
v122 = var22 (vs22 vz22)

v222 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm22 (snoc22 (snoc22 (snoc22 g a) b) c) a
v222 = var22 (vs22 (vs22 vz22))

v322 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm22 (snoc22 (snoc22 (snoc22 (snoc22 g a) b) c) d) a
v322 = var22 (vs22 (vs22 (vs22 vz22)))

tbool22 : Ty22
tbool22 = sum22 top22 top22

ttrue22 : {g:_} -> Tm22 g Main.tbool22
ttrue22 = left22 tt22

tfalse22 : {g:_} -> Tm22 g Main.tbool22
tfalse22 = right22 tt22

ifthenelse22 : {g:_}->{a:_} -> Tm22 g (arr22 Main.tbool22 (arr22 a (arr22 a a)))
ifthenelse22 = lam22 (lam22 (lam22 (split22 v222 (lam22 v222) (lam22 v122))))

times422 : {g:_}->{a:_} -> Tm22 g (arr22 (arr22 a a) (arr22 a a))
times422  = lam22 (lam22 (app22 v122 (app22 v122 (app22 v122 (app22 v122 v022)))))

add22 : {g:_} -> Tm22 g (arr22 Main.nat22 (arr22 Main.nat22 Main.nat22))
add22 = lam22 (rec22 v022
       (lam22 (lam22 (lam22 (suc22 (app22 v122 v022)))))
       (lam22 v022))

mul22 : {g:_} -> Tm22 g (arr22 Main.nat22 (arr22 Main.nat22 Main.nat22))
mul22 = lam22 (rec22 v022
       (lam22 (lam22 (lam22 (app22 (app22 add22 (app22 v122 v022)) v022))))
       (lam22 zero22))

fact22 : {g:_} -> Tm22 g (arr22 Main.nat22 Main.nat22)
fact22 = lam22 (rec22 v022 (lam22 (lam22 (app22 (app22 mul22 (suc22 v122)) v022)))
                 (suc22 zero22))

Ty23 : Type
Ty23 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat23 : Ty23
nat23 = \ _, nat23, _, _, _, _, _ => nat23
top23 : Ty23
top23 = \ _, _, top23, _, _, _, _ => top23
bot23 : Ty23
bot23 = \ _, _, _, bot23, _, _, _ => bot23

arr23 : Ty23-> Ty23-> Ty23
arr23 = \ a, b, ty, nat23, top23, bot23, arr23, prod, sum =>
     arr23 (a ty nat23 top23 bot23 arr23 prod sum) (b ty nat23 top23 bot23 arr23 prod sum)

prod23 : Ty23-> Ty23-> Ty23
prod23 = \ a, b, ty, nat23, top23, bot23, arr23, prod23, sum =>
     prod23 (a ty nat23 top23 bot23 arr23 prod23 sum) (b ty nat23 top23 bot23 arr23 prod23 sum)

sum23 : Ty23-> Ty23-> Ty23
sum23 = \ a, b, ty, nat23, top23, bot23, arr23, prod23, sum23 =>
     sum23 (a ty nat23 top23 bot23 arr23 prod23 sum23) (b ty nat23 top23 bot23 arr23 prod23 sum23)

Con23 : Type
Con23 = (Con23 : Type)
 -> (nil  : Con23)
 -> (snoc : Con23 -> Ty23-> Con23)
 -> Con23

nil23 : Con23
nil23 = \ con, nil23, snoc => nil23

snoc23 : Con23 -> Ty23-> Con23
snoc23 = \ g, a, con, nil23, snoc23 => snoc23 (g con nil23 snoc23) a

Var23 : Con23 -> Ty23-> Type
Var23 = \ g, a =>
    (Var23 : Con23 -> Ty23-> Type)
 -> (vz  : {g:_}->{a:_} -> Var23 (snoc23 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var23 g a -> Var23 (snoc23 g b) a)
 -> Var23 g a

vz23 : {g:_}->{a:_} -> Var23 (snoc23 g a) a
vz23 = \ var, vz23, vs => vz23

vs23 : {g:_}->{b:_}->{a:_} -> Var23 g a -> Var23 (snoc23 g b) a
vs23 = \ x, var, vz23, vs23 => vs23 (x var vz23 vs23)

Tm23 : Con23 -> Ty23-> Type
Tm23 = \ g, a =>
    (Tm23    : Con23 -> Ty23-> Type)
 -> (var   : {g:_}->{a:_}-> Var23 g a -> Tm23 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm23 (snoc23 g a) b -> Tm23 g (arr23 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm23 g (arr23 a b) -> Tm23 g a -> Tm23 g b)
 -> (tt    : {g:_}-> Tm23 g top23)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm23 g a -> Tm23 g b -> Tm23 g (prod23 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm23 g (prod23 a b) -> Tm23 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm23 g (prod23 a b) -> Tm23 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm23 g a -> Tm23 g (sum23 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm23 g b -> Tm23 g (sum23 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm23 g (sum23 a b) -> Tm23 g (arr23 a c) -> Tm23 g (arr23 b c) -> Tm23 g c)
 -> (zero  : {g:_}-> Tm23 g nat23)
 -> (suc   : {g:_}-> Tm23 g nat23 -> Tm23 g nat23)
 -> (rec   : {g:_}->{a:_} -> Tm23 g nat23 -> Tm23 g (arr23 nat23 (arr23 a a)) -> Tm23 g a -> Tm23 g a)
 -> Tm23 g a

var23 : {g:_}->{a:_} -> Var23 g a -> Tm23 g a
var23 = \ x, tm, var23, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var23 x

lam23 : {g:_}->{a:_}->{b:_}-> Tm23 (snoc23 g a) b -> Tm23 g (arr23 a b)
lam23 = \ t, tm, var23, lam23, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam23 (t tm var23 lam23 app tt pair fst snd left right split zero suc rec)

app23 : {g:_}->{a:_}->{b:_} -> Tm23 g (arr23 a b) -> Tm23 g a -> Tm23 g b
app23 = \ t, u, tm, var23, lam23, app23, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app23 (t tm var23 lam23 app23 tt pair fst snd left right split zero suc rec)
         (u tm var23 lam23 app23 tt pair fst snd left right split zero suc rec)

tt23 : {g:_} -> Tm23 g Main.top23
tt23 = \ tm, var23, lam23, app23, tt23, pair, fst, snd, left, right, split, zero, suc, rec => tt23

pair23 : {g:_}->{a:_}->{b:_} -> Tm23 g a -> Tm23 g b -> Tm23 g (prod23 a b)
pair23 = \ t, u, tm, var23, lam23, app23, tt23, pair23, fst, snd, left, right, split, zero, suc, rec =>
     pair23 (t tm var23 lam23 app23 tt23 pair23 fst snd left right split zero suc rec)
          (u tm var23 lam23 app23 tt23 pair23 fst snd left right split zero suc rec)

fst23 : {g:_}->{a:_}->{b:_}-> Tm23 g (prod23 a b) -> Tm23 g a
fst23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd, left, right, split, zero, suc, rec =>
     fst23 (t tm var23 lam23 app23 tt23 pair23 fst23 snd left right split zero suc rec)

snd23 : {g:_}->{a:_}->{b:_} -> Tm23 g (prod23 a b) -> Tm23 g b
snd23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left, right, split, zero, suc, rec =>
     snd23 (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left right split zero suc rec)

left23 : {g:_}->{a:_}->{b:_} -> Tm23 g a -> Tm23 g (sum23 a b)
left23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right, split, zero, suc, rec =>
     left23 (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right split zero suc rec)

right23 : {g:_}->{a:_}->{b:_} -> Tm23 g b -> Tm23 g (sum23 a b)
right23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split, zero, suc, rec =>
     right23 (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split zero suc rec)

split23 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm23 g (sum23 a b) -> Tm23 g (arr23 a c) -> Tm23 g (arr23 b c) -> Tm23 g c
split23 = \ t, u, v, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split23, zero, suc, rec =>
     split23 (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero suc rec)
          (u tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero suc rec)
          (v tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero suc rec)

zero23 : {g:_} -> Tm23 g Main.nat23
zero23 = \ tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split23, zero23, suc, rec => zero23

suc23 : {g:_} -> Tm23 g Main.nat23 -> Tm23 g Main.nat23
suc23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split23, zero23, suc23, rec =>
   suc23 (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero23 suc23 rec)

rec23 : {g:_}->{a:_} -> Tm23 g Main.nat23 -> Tm23 g (arr23 Main.nat23 (arr23 a a)) -> Tm23 g a -> Tm23 g a
rec23 = \ t, u, v, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split23, zero23, suc23, rec23 =>
     rec23 (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero23 suc23 rec23)
         (u tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero23 suc23 rec23)
         (v tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero23 suc23 rec23)

v023 : {g:_}->{a:_} -> Tm23 (snoc23 g a) a
v023 = var23 vz23

v123 : {g:_}->{a:_}->{b:_} -> Tm23 (snoc23 (snoc23 g a) b) a
v123 = var23 (vs23 vz23)

v223 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm23 (snoc23 (snoc23 (snoc23 g a) b) c) a
v223 = var23 (vs23 (vs23 vz23))

v323 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm23 (snoc23 (snoc23 (snoc23 (snoc23 g a) b) c) d) a
v323 = var23 (vs23 (vs23 (vs23 vz23)))

tbool23 : Ty23
tbool23 = sum23 top23 top23

ttrue23 : {g:_} -> Tm23 g Main.tbool23
ttrue23 = left23 tt23

tfalse23 : {g:_} -> Tm23 g Main.tbool23
tfalse23 = right23 tt23

ifthenelse23 : {g:_}->{a:_} -> Tm23 g (arr23 Main.tbool23 (arr23 a (arr23 a a)))
ifthenelse23 = lam23 (lam23 (lam23 (split23 v223 (lam23 v223) (lam23 v123))))

times423 : {g:_}->{a:_} -> Tm23 g (arr23 (arr23 a a) (arr23 a a))
times423  = lam23 (lam23 (app23 v123 (app23 v123 (app23 v123 (app23 v123 v023)))))

add23 : {g:_} -> Tm23 g (arr23 Main.nat23 (arr23 Main.nat23 Main.nat23))
add23 = lam23 (rec23 v023
       (lam23 (lam23 (lam23 (suc23 (app23 v123 v023)))))
       (lam23 v023))

mul23 : {g:_} -> Tm23 g (arr23 Main.nat23 (arr23 Main.nat23 Main.nat23))
mul23 = lam23 (rec23 v023
       (lam23 (lam23 (lam23 (app23 (app23 add23 (app23 v123 v023)) v023))))
       (lam23 zero23))

fact23 : {g:_} -> Tm23 g (arr23 Main.nat23 Main.nat23)
fact23 = lam23 (rec23 v023 (lam23 (lam23 (app23 (app23 mul23 (suc23 v123)) v023)))
                 (suc23 zero23))

Ty24 : Type
Ty24 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat24 : Ty24
nat24 = \ _, nat24, _, _, _, _, _ => nat24
top24 : Ty24
top24 = \ _, _, top24, _, _, _, _ => top24
bot24 : Ty24
bot24 = \ _, _, _, bot24, _, _, _ => bot24

arr24 : Ty24-> Ty24-> Ty24
arr24 = \ a, b, ty, nat24, top24, bot24, arr24, prod, sum =>
     arr24 (a ty nat24 top24 bot24 arr24 prod sum) (b ty nat24 top24 bot24 arr24 prod sum)

prod24 : Ty24-> Ty24-> Ty24
prod24 = \ a, b, ty, nat24, top24, bot24, arr24, prod24, sum =>
     prod24 (a ty nat24 top24 bot24 arr24 prod24 sum) (b ty nat24 top24 bot24 arr24 prod24 sum)

sum24 : Ty24-> Ty24-> Ty24
sum24 = \ a, b, ty, nat24, top24, bot24, arr24, prod24, sum24 =>
     sum24 (a ty nat24 top24 bot24 arr24 prod24 sum24) (b ty nat24 top24 bot24 arr24 prod24 sum24)

Con24 : Type
Con24 = (Con24 : Type)
 -> (nil  : Con24)
 -> (snoc : Con24 -> Ty24-> Con24)
 -> Con24

nil24 : Con24
nil24 = \ con, nil24, snoc => nil24

snoc24 : Con24 -> Ty24-> Con24
snoc24 = \ g, a, con, nil24, snoc24 => snoc24 (g con nil24 snoc24) a

Var24 : Con24 -> Ty24-> Type
Var24 = \ g, a =>
    (Var24 : Con24 -> Ty24-> Type)
 -> (vz  : {g:_}->{a:_} -> Var24 (snoc24 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var24 g a -> Var24 (snoc24 g b) a)
 -> Var24 g a

vz24 : {g:_}->{a:_} -> Var24 (snoc24 g a) a
vz24 = \ var, vz24, vs => vz24

vs24 : {g:_}->{b:_}->{a:_} -> Var24 g a -> Var24 (snoc24 g b) a
vs24 = \ x, var, vz24, vs24 => vs24 (x var vz24 vs24)

Tm24 : Con24 -> Ty24-> Type
Tm24 = \ g, a =>
    (Tm24    : Con24 -> Ty24-> Type)
 -> (var   : {g:_}->{a:_}-> Var24 g a -> Tm24 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm24 (snoc24 g a) b -> Tm24 g (arr24 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm24 g (arr24 a b) -> Tm24 g a -> Tm24 g b)
 -> (tt    : {g:_}-> Tm24 g top24)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm24 g a -> Tm24 g b -> Tm24 g (prod24 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm24 g (prod24 a b) -> Tm24 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm24 g (prod24 a b) -> Tm24 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm24 g a -> Tm24 g (sum24 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm24 g b -> Tm24 g (sum24 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm24 g (sum24 a b) -> Tm24 g (arr24 a c) -> Tm24 g (arr24 b c) -> Tm24 g c)
 -> (zero  : {g:_}-> Tm24 g nat24)
 -> (suc   : {g:_}-> Tm24 g nat24 -> Tm24 g nat24)
 -> (rec   : {g:_}->{a:_} -> Tm24 g nat24 -> Tm24 g (arr24 nat24 (arr24 a a)) -> Tm24 g a -> Tm24 g a)
 -> Tm24 g a

var24 : {g:_}->{a:_} -> Var24 g a -> Tm24 g a
var24 = \ x, tm, var24, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var24 x

lam24 : {g:_}->{a:_}->{b:_}-> Tm24 (snoc24 g a) b -> Tm24 g (arr24 a b)
lam24 = \ t, tm, var24, lam24, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam24 (t tm var24 lam24 app tt pair fst snd left right split zero suc rec)

app24 : {g:_}->{a:_}->{b:_} -> Tm24 g (arr24 a b) -> Tm24 g a -> Tm24 g b
app24 = \ t, u, tm, var24, lam24, app24, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app24 (t tm var24 lam24 app24 tt pair fst snd left right split zero suc rec)
         (u tm var24 lam24 app24 tt pair fst snd left right split zero suc rec)

tt24 : {g:_} -> Tm24 g Main.top24
tt24 = \ tm, var24, lam24, app24, tt24, pair, fst, snd, left, right, split, zero, suc, rec => tt24

pair24 : {g:_}->{a:_}->{b:_} -> Tm24 g a -> Tm24 g b -> Tm24 g (prod24 a b)
pair24 = \ t, u, tm, var24, lam24, app24, tt24, pair24, fst, snd, left, right, split, zero, suc, rec =>
     pair24 (t tm var24 lam24 app24 tt24 pair24 fst snd left right split zero suc rec)
          (u tm var24 lam24 app24 tt24 pair24 fst snd left right split zero suc rec)

fst24 : {g:_}->{a:_}->{b:_}-> Tm24 g (prod24 a b) -> Tm24 g a
fst24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd, left, right, split, zero, suc, rec =>
     fst24 (t tm var24 lam24 app24 tt24 pair24 fst24 snd left right split zero suc rec)

snd24 : {g:_}->{a:_}->{b:_} -> Tm24 g (prod24 a b) -> Tm24 g b
snd24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left, right, split, zero, suc, rec =>
     snd24 (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left right split zero suc rec)

left24 : {g:_}->{a:_}->{b:_} -> Tm24 g a -> Tm24 g (sum24 a b)
left24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right, split, zero, suc, rec =>
     left24 (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right split zero suc rec)

right24 : {g:_}->{a:_}->{b:_} -> Tm24 g b -> Tm24 g (sum24 a b)
right24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split, zero, suc, rec =>
     right24 (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split zero suc rec)

split24 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm24 g (sum24 a b) -> Tm24 g (arr24 a c) -> Tm24 g (arr24 b c) -> Tm24 g c
split24 = \ t, u, v, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split24, zero, suc, rec =>
     split24 (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero suc rec)
          (u tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero suc rec)
          (v tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero suc rec)

zero24 : {g:_} -> Tm24 g Main.nat24
zero24 = \ tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split24, zero24, suc, rec => zero24

suc24 : {g:_} -> Tm24 g Main.nat24 -> Tm24 g Main.nat24
suc24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split24, zero24, suc24, rec =>
   suc24 (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero24 suc24 rec)

rec24 : {g:_}->{a:_} -> Tm24 g Main.nat24 -> Tm24 g (arr24 Main.nat24 (arr24 a a)) -> Tm24 g a -> Tm24 g a
rec24 = \ t, u, v, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split24, zero24, suc24, rec24 =>
     rec24 (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero24 suc24 rec24)
         (u tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero24 suc24 rec24)
         (v tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero24 suc24 rec24)

v024 : {g:_}->{a:_} -> Tm24 (snoc24 g a) a
v024 = var24 vz24

v124 : {g:_}->{a:_}->{b:_} -> Tm24 (snoc24 (snoc24 g a) b) a
v124 = var24 (vs24 vz24)

v224 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm24 (snoc24 (snoc24 (snoc24 g a) b) c) a
v224 = var24 (vs24 (vs24 vz24))

v324 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm24 (snoc24 (snoc24 (snoc24 (snoc24 g a) b) c) d) a
v324 = var24 (vs24 (vs24 (vs24 vz24)))

tbool24 : Ty24
tbool24 = sum24 top24 top24

ttrue24 : {g:_} -> Tm24 g Main.tbool24
ttrue24 = left24 tt24

tfalse24 : {g:_} -> Tm24 g Main.tbool24
tfalse24 = right24 tt24

ifthenelse24 : {g:_}->{a:_} -> Tm24 g (arr24 Main.tbool24 (arr24 a (arr24 a a)))
ifthenelse24 = lam24 (lam24 (lam24 (split24 v224 (lam24 v224) (lam24 v124))))

times424 : {g:_}->{a:_} -> Tm24 g (arr24 (arr24 a a) (arr24 a a))
times424  = lam24 (lam24 (app24 v124 (app24 v124 (app24 v124 (app24 v124 v024)))))

add24 : {g:_} -> Tm24 g (arr24 Main.nat24 (arr24 Main.nat24 Main.nat24))
add24 = lam24 (rec24 v024
       (lam24 (lam24 (lam24 (suc24 (app24 v124 v024)))))
       (lam24 v024))

mul24 : {g:_} -> Tm24 g (arr24 Main.nat24 (arr24 Main.nat24 Main.nat24))
mul24 = lam24 (rec24 v024
       (lam24 (lam24 (lam24 (app24 (app24 add24 (app24 v124 v024)) v024))))
       (lam24 zero24))

fact24 : {g:_} -> Tm24 g (arr24 Main.nat24 Main.nat24)
fact24 = lam24 (rec24 v024 (lam24 (lam24 (app24 (app24 mul24 (suc24 v124)) v024)))
                 (suc24 zero24))

Ty25 : Type
Ty25 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat25 : Ty25
nat25 = \ _, nat25, _, _, _, _, _ => nat25
top25 : Ty25
top25 = \ _, _, top25, _, _, _, _ => top25
bot25 : Ty25
bot25 = \ _, _, _, bot25, _, _, _ => bot25

arr25 : Ty25-> Ty25-> Ty25
arr25 = \ a, b, ty, nat25, top25, bot25, arr25, prod, sum =>
     arr25 (a ty nat25 top25 bot25 arr25 prod sum) (b ty nat25 top25 bot25 arr25 prod sum)

prod25 : Ty25-> Ty25-> Ty25
prod25 = \ a, b, ty, nat25, top25, bot25, arr25, prod25, sum =>
     prod25 (a ty nat25 top25 bot25 arr25 prod25 sum) (b ty nat25 top25 bot25 arr25 prod25 sum)

sum25 : Ty25-> Ty25-> Ty25
sum25 = \ a, b, ty, nat25, top25, bot25, arr25, prod25, sum25 =>
     sum25 (a ty nat25 top25 bot25 arr25 prod25 sum25) (b ty nat25 top25 bot25 arr25 prod25 sum25)

Con25 : Type
Con25 = (Con25 : Type)
 -> (nil  : Con25)
 -> (snoc : Con25 -> Ty25-> Con25)
 -> Con25

nil25 : Con25
nil25 = \ con, nil25, snoc => nil25

snoc25 : Con25 -> Ty25-> Con25
snoc25 = \ g, a, con, nil25, snoc25 => snoc25 (g con nil25 snoc25) a

Var25 : Con25 -> Ty25-> Type
Var25 = \ g, a =>
    (Var25 : Con25 -> Ty25-> Type)
 -> (vz  : {g:_}->{a:_} -> Var25 (snoc25 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var25 g a -> Var25 (snoc25 g b) a)
 -> Var25 g a

vz25 : {g:_}->{a:_} -> Var25 (snoc25 g a) a
vz25 = \ var, vz25, vs => vz25

vs25 : {g:_}->{b:_}->{a:_} -> Var25 g a -> Var25 (snoc25 g b) a
vs25 = \ x, var, vz25, vs25 => vs25 (x var vz25 vs25)

Tm25 : Con25 -> Ty25-> Type
Tm25 = \ g, a =>
    (Tm25    : Con25 -> Ty25-> Type)
 -> (var   : {g:_}->{a:_}-> Var25 g a -> Tm25 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm25 (snoc25 g a) b -> Tm25 g (arr25 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm25 g (arr25 a b) -> Tm25 g a -> Tm25 g b)
 -> (tt    : {g:_}-> Tm25 g top25)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm25 g a -> Tm25 g b -> Tm25 g (prod25 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm25 g (prod25 a b) -> Tm25 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm25 g (prod25 a b) -> Tm25 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm25 g a -> Tm25 g (sum25 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm25 g b -> Tm25 g (sum25 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm25 g (sum25 a b) -> Tm25 g (arr25 a c) -> Tm25 g (arr25 b c) -> Tm25 g c)
 -> (zero  : {g:_}-> Tm25 g nat25)
 -> (suc   : {g:_}-> Tm25 g nat25 -> Tm25 g nat25)
 -> (rec   : {g:_}->{a:_} -> Tm25 g nat25 -> Tm25 g (arr25 nat25 (arr25 a a)) -> Tm25 g a -> Tm25 g a)
 -> Tm25 g a

var25 : {g:_}->{a:_} -> Var25 g a -> Tm25 g a
var25 = \ x, tm, var25, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var25 x

lam25 : {g:_}->{a:_}->{b:_}-> Tm25 (snoc25 g a) b -> Tm25 g (arr25 a b)
lam25 = \ t, tm, var25, lam25, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam25 (t tm var25 lam25 app tt pair fst snd left right split zero suc rec)

app25 : {g:_}->{a:_}->{b:_} -> Tm25 g (arr25 a b) -> Tm25 g a -> Tm25 g b
app25 = \ t, u, tm, var25, lam25, app25, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app25 (t tm var25 lam25 app25 tt pair fst snd left right split zero suc rec)
         (u tm var25 lam25 app25 tt pair fst snd left right split zero suc rec)

tt25 : {g:_} -> Tm25 g Main.top25
tt25 = \ tm, var25, lam25, app25, tt25, pair, fst, snd, left, right, split, zero, suc, rec => tt25

pair25 : {g:_}->{a:_}->{b:_} -> Tm25 g a -> Tm25 g b -> Tm25 g (prod25 a b)
pair25 = \ t, u, tm, var25, lam25, app25, tt25, pair25, fst, snd, left, right, split, zero, suc, rec =>
     pair25 (t tm var25 lam25 app25 tt25 pair25 fst snd left right split zero suc rec)
          (u tm var25 lam25 app25 tt25 pair25 fst snd left right split zero suc rec)

fst25 : {g:_}->{a:_}->{b:_}-> Tm25 g (prod25 a b) -> Tm25 g a
fst25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd, left, right, split, zero, suc, rec =>
     fst25 (t tm var25 lam25 app25 tt25 pair25 fst25 snd left right split zero suc rec)

snd25 : {g:_}->{a:_}->{b:_} -> Tm25 g (prod25 a b) -> Tm25 g b
snd25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left, right, split, zero, suc, rec =>
     snd25 (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left right split zero suc rec)

left25 : {g:_}->{a:_}->{b:_} -> Tm25 g a -> Tm25 g (sum25 a b)
left25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right, split, zero, suc, rec =>
     left25 (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right split zero suc rec)

right25 : {g:_}->{a:_}->{b:_} -> Tm25 g b -> Tm25 g (sum25 a b)
right25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split, zero, suc, rec =>
     right25 (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split zero suc rec)

split25 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm25 g (sum25 a b) -> Tm25 g (arr25 a c) -> Tm25 g (arr25 b c) -> Tm25 g c
split25 = \ t, u, v, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split25, zero, suc, rec =>
     split25 (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero suc rec)
          (u tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero suc rec)
          (v tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero suc rec)

zero25 : {g:_} -> Tm25 g Main.nat25
zero25 = \ tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split25, zero25, suc, rec => zero25

suc25 : {g:_} -> Tm25 g Main.nat25 -> Tm25 g Main.nat25
suc25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split25, zero25, suc25, rec =>
   suc25 (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero25 suc25 rec)

rec25 : {g:_}->{a:_} -> Tm25 g Main.nat25 -> Tm25 g (arr25 Main.nat25 (arr25 a a)) -> Tm25 g a -> Tm25 g a
rec25 = \ t, u, v, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split25, zero25, suc25, rec25 =>
     rec25 (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero25 suc25 rec25)
         (u tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero25 suc25 rec25)
         (v tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero25 suc25 rec25)

v025 : {g:_}->{a:_} -> Tm25 (snoc25 g a) a
v025 = var25 vz25

v125 : {g:_}->{a:_}->{b:_} -> Tm25 (snoc25 (snoc25 g a) b) a
v125 = var25 (vs25 vz25)

v225 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm25 (snoc25 (snoc25 (snoc25 g a) b) c) a
v225 = var25 (vs25 (vs25 vz25))

v325 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm25 (snoc25 (snoc25 (snoc25 (snoc25 g a) b) c) d) a
v325 = var25 (vs25 (vs25 (vs25 vz25)))

tbool25 : Ty25
tbool25 = sum25 top25 top25

ttrue25 : {g:_} -> Tm25 g Main.tbool25
ttrue25 = left25 tt25

tfalse25 : {g:_} -> Tm25 g Main.tbool25
tfalse25 = right25 tt25

ifthenelse25 : {g:_}->{a:_} -> Tm25 g (arr25 Main.tbool25 (arr25 a (arr25 a a)))
ifthenelse25 = lam25 (lam25 (lam25 (split25 v225 (lam25 v225) (lam25 v125))))

times425 : {g:_}->{a:_} -> Tm25 g (arr25 (arr25 a a) (arr25 a a))
times425  = lam25 (lam25 (app25 v125 (app25 v125 (app25 v125 (app25 v125 v025)))))

add25 : {g:_} -> Tm25 g (arr25 Main.nat25 (arr25 Main.nat25 Main.nat25))
add25 = lam25 (rec25 v025
       (lam25 (lam25 (lam25 (suc25 (app25 v125 v025)))))
       (lam25 v025))

mul25 : {g:_} -> Tm25 g (arr25 Main.nat25 (arr25 Main.nat25 Main.nat25))
mul25 = lam25 (rec25 v025
       (lam25 (lam25 (lam25 (app25 (app25 add25 (app25 v125 v025)) v025))))
       (lam25 zero25))

fact25 : {g:_} -> Tm25 g (arr25 Main.nat25 Main.nat25)
fact25 = lam25 (rec25 v025 (lam25 (lam25 (app25 (app25 mul25 (suc25 v125)) v025)))
                 (suc25 zero25))

Ty26 : Type
Ty26 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat26 : Ty26
nat26 = \ _, nat26, _, _, _, _, _ => nat26
top26 : Ty26
top26 = \ _, _, top26, _, _, _, _ => top26
bot26 : Ty26
bot26 = \ _, _, _, bot26, _, _, _ => bot26

arr26 : Ty26-> Ty26-> Ty26
arr26 = \ a, b, ty, nat26, top26, bot26, arr26, prod, sum =>
     arr26 (a ty nat26 top26 bot26 arr26 prod sum) (b ty nat26 top26 bot26 arr26 prod sum)

prod26 : Ty26-> Ty26-> Ty26
prod26 = \ a, b, ty, nat26, top26, bot26, arr26, prod26, sum =>
     prod26 (a ty nat26 top26 bot26 arr26 prod26 sum) (b ty nat26 top26 bot26 arr26 prod26 sum)

sum26 : Ty26-> Ty26-> Ty26
sum26 = \ a, b, ty, nat26, top26, bot26, arr26, prod26, sum26 =>
     sum26 (a ty nat26 top26 bot26 arr26 prod26 sum26) (b ty nat26 top26 bot26 arr26 prod26 sum26)

Con26 : Type
Con26 = (Con26 : Type)
 -> (nil  : Con26)
 -> (snoc : Con26 -> Ty26-> Con26)
 -> Con26

nil26 : Con26
nil26 = \ con, nil26, snoc => nil26

snoc26 : Con26 -> Ty26-> Con26
snoc26 = \ g, a, con, nil26, snoc26 => snoc26 (g con nil26 snoc26) a

Var26 : Con26 -> Ty26-> Type
Var26 = \ g, a =>
    (Var26 : Con26 -> Ty26-> Type)
 -> (vz  : {g:_}->{a:_} -> Var26 (snoc26 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var26 g a -> Var26 (snoc26 g b) a)
 -> Var26 g a

vz26 : {g:_}->{a:_} -> Var26 (snoc26 g a) a
vz26 = \ var, vz26, vs => vz26

vs26 : {g:_}->{b:_}->{a:_} -> Var26 g a -> Var26 (snoc26 g b) a
vs26 = \ x, var, vz26, vs26 => vs26 (x var vz26 vs26)

Tm26 : Con26 -> Ty26-> Type
Tm26 = \ g, a =>
    (Tm26    : Con26 -> Ty26-> Type)
 -> (var   : {g:_}->{a:_}-> Var26 g a -> Tm26 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm26 (snoc26 g a) b -> Tm26 g (arr26 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm26 g (arr26 a b) -> Tm26 g a -> Tm26 g b)
 -> (tt    : {g:_}-> Tm26 g top26)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm26 g a -> Tm26 g b -> Tm26 g (prod26 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm26 g (prod26 a b) -> Tm26 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm26 g (prod26 a b) -> Tm26 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm26 g a -> Tm26 g (sum26 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm26 g b -> Tm26 g (sum26 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm26 g (sum26 a b) -> Tm26 g (arr26 a c) -> Tm26 g (arr26 b c) -> Tm26 g c)
 -> (zero  : {g:_}-> Tm26 g nat26)
 -> (suc   : {g:_}-> Tm26 g nat26 -> Tm26 g nat26)
 -> (rec   : {g:_}->{a:_} -> Tm26 g nat26 -> Tm26 g (arr26 nat26 (arr26 a a)) -> Tm26 g a -> Tm26 g a)
 -> Tm26 g a

var26 : {g:_}->{a:_} -> Var26 g a -> Tm26 g a
var26 = \ x, tm, var26, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var26 x

lam26 : {g:_}->{a:_}->{b:_}-> Tm26 (snoc26 g a) b -> Tm26 g (arr26 a b)
lam26 = \ t, tm, var26, lam26, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam26 (t tm var26 lam26 app tt pair fst snd left right split zero suc rec)

app26 : {g:_}->{a:_}->{b:_} -> Tm26 g (arr26 a b) -> Tm26 g a -> Tm26 g b
app26 = \ t, u, tm, var26, lam26, app26, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app26 (t tm var26 lam26 app26 tt pair fst snd left right split zero suc rec)
         (u tm var26 lam26 app26 tt pair fst snd left right split zero suc rec)

tt26 : {g:_} -> Tm26 g Main.top26
tt26 = \ tm, var26, lam26, app26, tt26, pair, fst, snd, left, right, split, zero, suc, rec => tt26

pair26 : {g:_}->{a:_}->{b:_} -> Tm26 g a -> Tm26 g b -> Tm26 g (prod26 a b)
pair26 = \ t, u, tm, var26, lam26, app26, tt26, pair26, fst, snd, left, right, split, zero, suc, rec =>
     pair26 (t tm var26 lam26 app26 tt26 pair26 fst snd left right split zero suc rec)
          (u tm var26 lam26 app26 tt26 pair26 fst snd left right split zero suc rec)

fst26 : {g:_}->{a:_}->{b:_}-> Tm26 g (prod26 a b) -> Tm26 g a
fst26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd, left, right, split, zero, suc, rec =>
     fst26 (t tm var26 lam26 app26 tt26 pair26 fst26 snd left right split zero suc rec)

snd26 : {g:_}->{a:_}->{b:_} -> Tm26 g (prod26 a b) -> Tm26 g b
snd26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left, right, split, zero, suc, rec =>
     snd26 (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left right split zero suc rec)

left26 : {g:_}->{a:_}->{b:_} -> Tm26 g a -> Tm26 g (sum26 a b)
left26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right, split, zero, suc, rec =>
     left26 (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right split zero suc rec)

right26 : {g:_}->{a:_}->{b:_} -> Tm26 g b -> Tm26 g (sum26 a b)
right26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split, zero, suc, rec =>
     right26 (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split zero suc rec)

split26 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm26 g (sum26 a b) -> Tm26 g (arr26 a c) -> Tm26 g (arr26 b c) -> Tm26 g c
split26 = \ t, u, v, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split26, zero, suc, rec =>
     split26 (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero suc rec)
          (u tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero suc rec)
          (v tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero suc rec)

zero26 : {g:_} -> Tm26 g Main.nat26
zero26 = \ tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split26, zero26, suc, rec => zero26

suc26 : {g:_} -> Tm26 g Main.nat26 -> Tm26 g Main.nat26
suc26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split26, zero26, suc26, rec =>
   suc26 (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero26 suc26 rec)

rec26 : {g:_}->{a:_} -> Tm26 g Main.nat26 -> Tm26 g (arr26 Main.nat26 (arr26 a a)) -> Tm26 g a -> Tm26 g a
rec26 = \ t, u, v, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split26, zero26, suc26, rec26 =>
     rec26 (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero26 suc26 rec26)
         (u tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero26 suc26 rec26)
         (v tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero26 suc26 rec26)

v026 : {g:_}->{a:_} -> Tm26 (snoc26 g a) a
v026 = var26 vz26

v126 : {g:_}->{a:_}->{b:_} -> Tm26 (snoc26 (snoc26 g a) b) a
v126 = var26 (vs26 vz26)

v226 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm26 (snoc26 (snoc26 (snoc26 g a) b) c) a
v226 = var26 (vs26 (vs26 vz26))

v326 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm26 (snoc26 (snoc26 (snoc26 (snoc26 g a) b) c) d) a
v326 = var26 (vs26 (vs26 (vs26 vz26)))

tbool26 : Ty26
tbool26 = sum26 top26 top26

ttrue26 : {g:_} -> Tm26 g Main.tbool26
ttrue26 = left26 tt26

tfalse26 : {g:_} -> Tm26 g Main.tbool26
tfalse26 = right26 tt26

ifthenelse26 : {g:_}->{a:_} -> Tm26 g (arr26 Main.tbool26 (arr26 a (arr26 a a)))
ifthenelse26 = lam26 (lam26 (lam26 (split26 v226 (lam26 v226) (lam26 v126))))

times426 : {g:_}->{a:_} -> Tm26 g (arr26 (arr26 a a) (arr26 a a))
times426  = lam26 (lam26 (app26 v126 (app26 v126 (app26 v126 (app26 v126 v026)))))

add26 : {g:_} -> Tm26 g (arr26 Main.nat26 (arr26 Main.nat26 Main.nat26))
add26 = lam26 (rec26 v026
       (lam26 (lam26 (lam26 (suc26 (app26 v126 v026)))))
       (lam26 v026))

mul26 : {g:_} -> Tm26 g (arr26 Main.nat26 (arr26 Main.nat26 Main.nat26))
mul26 = lam26 (rec26 v026
       (lam26 (lam26 (lam26 (app26 (app26 add26 (app26 v126 v026)) v026))))
       (lam26 zero26))

fact26 : {g:_} -> Tm26 g (arr26 Main.nat26 Main.nat26)
fact26 = lam26 (rec26 v026 (lam26 (lam26 (app26 (app26 mul26 (suc26 v126)) v026)))
                 (suc26 zero26))

Ty27 : Type
Ty27 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat27 : Ty27
nat27 = \ _, nat27, _, _, _, _, _ => nat27
top27 : Ty27
top27 = \ _, _, top27, _, _, _, _ => top27
bot27 : Ty27
bot27 = \ _, _, _, bot27, _, _, _ => bot27

arr27 : Ty27-> Ty27-> Ty27
arr27 = \ a, b, ty, nat27, top27, bot27, arr27, prod, sum =>
     arr27 (a ty nat27 top27 bot27 arr27 prod sum) (b ty nat27 top27 bot27 arr27 prod sum)

prod27 : Ty27-> Ty27-> Ty27
prod27 = \ a, b, ty, nat27, top27, bot27, arr27, prod27, sum =>
     prod27 (a ty nat27 top27 bot27 arr27 prod27 sum) (b ty nat27 top27 bot27 arr27 prod27 sum)

sum27 : Ty27-> Ty27-> Ty27
sum27 = \ a, b, ty, nat27, top27, bot27, arr27, prod27, sum27 =>
     sum27 (a ty nat27 top27 bot27 arr27 prod27 sum27) (b ty nat27 top27 bot27 arr27 prod27 sum27)

Con27 : Type
Con27 = (Con27 : Type)
 -> (nil  : Con27)
 -> (snoc : Con27 -> Ty27-> Con27)
 -> Con27

nil27 : Con27
nil27 = \ con, nil27, snoc => nil27

snoc27 : Con27 -> Ty27-> Con27
snoc27 = \ g, a, con, nil27, snoc27 => snoc27 (g con nil27 snoc27) a

Var27 : Con27 -> Ty27-> Type
Var27 = \ g, a =>
    (Var27 : Con27 -> Ty27-> Type)
 -> (vz  : {g:_}->{a:_} -> Var27 (snoc27 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var27 g a -> Var27 (snoc27 g b) a)
 -> Var27 g a

vz27 : {g:_}->{a:_} -> Var27 (snoc27 g a) a
vz27 = \ var, vz27, vs => vz27

vs27 : {g:_}->{b:_}->{a:_} -> Var27 g a -> Var27 (snoc27 g b) a
vs27 = \ x, var, vz27, vs27 => vs27 (x var vz27 vs27)

Tm27 : Con27 -> Ty27-> Type
Tm27 = \ g, a =>
    (Tm27    : Con27 -> Ty27-> Type)
 -> (var   : {g:_}->{a:_}-> Var27 g a -> Tm27 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm27 (snoc27 g a) b -> Tm27 g (arr27 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm27 g (arr27 a b) -> Tm27 g a -> Tm27 g b)
 -> (tt    : {g:_}-> Tm27 g top27)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm27 g a -> Tm27 g b -> Tm27 g (prod27 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm27 g (prod27 a b) -> Tm27 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm27 g (prod27 a b) -> Tm27 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm27 g a -> Tm27 g (sum27 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm27 g b -> Tm27 g (sum27 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm27 g (sum27 a b) -> Tm27 g (arr27 a c) -> Tm27 g (arr27 b c) -> Tm27 g c)
 -> (zero  : {g:_}-> Tm27 g nat27)
 -> (suc   : {g:_}-> Tm27 g nat27 -> Tm27 g nat27)
 -> (rec   : {g:_}->{a:_} -> Tm27 g nat27 -> Tm27 g (arr27 nat27 (arr27 a a)) -> Tm27 g a -> Tm27 g a)
 -> Tm27 g a

var27 : {g:_}->{a:_} -> Var27 g a -> Tm27 g a
var27 = \ x, tm, var27, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var27 x

lam27 : {g:_}->{a:_}->{b:_}-> Tm27 (snoc27 g a) b -> Tm27 g (arr27 a b)
lam27 = \ t, tm, var27, lam27, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam27 (t tm var27 lam27 app tt pair fst snd left right split zero suc rec)

app27 : {g:_}->{a:_}->{b:_} -> Tm27 g (arr27 a b) -> Tm27 g a -> Tm27 g b
app27 = \ t, u, tm, var27, lam27, app27, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app27 (t tm var27 lam27 app27 tt pair fst snd left right split zero suc rec)
         (u tm var27 lam27 app27 tt pair fst snd left right split zero suc rec)

tt27 : {g:_} -> Tm27 g Main.top27
tt27 = \ tm, var27, lam27, app27, tt27, pair, fst, snd, left, right, split, zero, suc, rec => tt27

pair27 : {g:_}->{a:_}->{b:_} -> Tm27 g a -> Tm27 g b -> Tm27 g (prod27 a b)
pair27 = \ t, u, tm, var27, lam27, app27, tt27, pair27, fst, snd, left, right, split, zero, suc, rec =>
     pair27 (t tm var27 lam27 app27 tt27 pair27 fst snd left right split zero suc rec)
          (u tm var27 lam27 app27 tt27 pair27 fst snd left right split zero suc rec)

fst27 : {g:_}->{a:_}->{b:_}-> Tm27 g (prod27 a b) -> Tm27 g a
fst27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd, left, right, split, zero, suc, rec =>
     fst27 (t tm var27 lam27 app27 tt27 pair27 fst27 snd left right split zero suc rec)

snd27 : {g:_}->{a:_}->{b:_} -> Tm27 g (prod27 a b) -> Tm27 g b
snd27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left, right, split, zero, suc, rec =>
     snd27 (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left right split zero suc rec)

left27 : {g:_}->{a:_}->{b:_} -> Tm27 g a -> Tm27 g (sum27 a b)
left27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right, split, zero, suc, rec =>
     left27 (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right split zero suc rec)

right27 : {g:_}->{a:_}->{b:_} -> Tm27 g b -> Tm27 g (sum27 a b)
right27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split, zero, suc, rec =>
     right27 (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split zero suc rec)

split27 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm27 g (sum27 a b) -> Tm27 g (arr27 a c) -> Tm27 g (arr27 b c) -> Tm27 g c
split27 = \ t, u, v, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split27, zero, suc, rec =>
     split27 (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero suc rec)
          (u tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero suc rec)
          (v tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero suc rec)

zero27 : {g:_} -> Tm27 g Main.nat27
zero27 = \ tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split27, zero27, suc, rec => zero27

suc27 : {g:_} -> Tm27 g Main.nat27 -> Tm27 g Main.nat27
suc27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split27, zero27, suc27, rec =>
   suc27 (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero27 suc27 rec)

rec27 : {g:_}->{a:_} -> Tm27 g Main.nat27 -> Tm27 g (arr27 Main.nat27 (arr27 a a)) -> Tm27 g a -> Tm27 g a
rec27 = \ t, u, v, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split27, zero27, suc27, rec27 =>
     rec27 (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero27 suc27 rec27)
         (u tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero27 suc27 rec27)
         (v tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero27 suc27 rec27)

v027 : {g:_}->{a:_} -> Tm27 (snoc27 g a) a
v027 = var27 vz27

v127 : {g:_}->{a:_}->{b:_} -> Tm27 (snoc27 (snoc27 g a) b) a
v127 = var27 (vs27 vz27)

v227 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm27 (snoc27 (snoc27 (snoc27 g a) b) c) a
v227 = var27 (vs27 (vs27 vz27))

v327 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm27 (snoc27 (snoc27 (snoc27 (snoc27 g a) b) c) d) a
v327 = var27 (vs27 (vs27 (vs27 vz27)))

tbool27 : Ty27
tbool27 = sum27 top27 top27

ttrue27 : {g:_} -> Tm27 g Main.tbool27
ttrue27 = left27 tt27

tfalse27 : {g:_} -> Tm27 g Main.tbool27
tfalse27 = right27 tt27

ifthenelse27 : {g:_}->{a:_} -> Tm27 g (arr27 Main.tbool27 (arr27 a (arr27 a a)))
ifthenelse27 = lam27 (lam27 (lam27 (split27 v227 (lam27 v227) (lam27 v127))))

times427 : {g:_}->{a:_} -> Tm27 g (arr27 (arr27 a a) (arr27 a a))
times427  = lam27 (lam27 (app27 v127 (app27 v127 (app27 v127 (app27 v127 v027)))))

add27 : {g:_} -> Tm27 g (arr27 Main.nat27 (arr27 Main.nat27 Main.nat27))
add27 = lam27 (rec27 v027
       (lam27 (lam27 (lam27 (suc27 (app27 v127 v027)))))
       (lam27 v027))

mul27 : {g:_} -> Tm27 g (arr27 Main.nat27 (arr27 Main.nat27 Main.nat27))
mul27 = lam27 (rec27 v027
       (lam27 (lam27 (lam27 (app27 (app27 add27 (app27 v127 v027)) v027))))
       (lam27 zero27))

fact27 : {g:_} -> Tm27 g (arr27 Main.nat27 Main.nat27)
fact27 = lam27 (rec27 v027 (lam27 (lam27 (app27 (app27 mul27 (suc27 v127)) v027)))
                 (suc27 zero27))

Ty28 : Type
Ty28 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat28 : Ty28
nat28 = \ _, nat28, _, _, _, _, _ => nat28
top28 : Ty28
top28 = \ _, _, top28, _, _, _, _ => top28
bot28 : Ty28
bot28 = \ _, _, _, bot28, _, _, _ => bot28

arr28 : Ty28-> Ty28-> Ty28
arr28 = \ a, b, ty, nat28, top28, bot28, arr28, prod, sum =>
     arr28 (a ty nat28 top28 bot28 arr28 prod sum) (b ty nat28 top28 bot28 arr28 prod sum)

prod28 : Ty28-> Ty28-> Ty28
prod28 = \ a, b, ty, nat28, top28, bot28, arr28, prod28, sum =>
     prod28 (a ty nat28 top28 bot28 arr28 prod28 sum) (b ty nat28 top28 bot28 arr28 prod28 sum)

sum28 : Ty28-> Ty28-> Ty28
sum28 = \ a, b, ty, nat28, top28, bot28, arr28, prod28, sum28 =>
     sum28 (a ty nat28 top28 bot28 arr28 prod28 sum28) (b ty nat28 top28 bot28 arr28 prod28 sum28)

Con28 : Type
Con28 = (Con28 : Type)
 -> (nil  : Con28)
 -> (snoc : Con28 -> Ty28-> Con28)
 -> Con28

nil28 : Con28
nil28 = \ con, nil28, snoc => nil28

snoc28 : Con28 -> Ty28-> Con28
snoc28 = \ g, a, con, nil28, snoc28 => snoc28 (g con nil28 snoc28) a

Var28 : Con28 -> Ty28-> Type
Var28 = \ g, a =>
    (Var28 : Con28 -> Ty28-> Type)
 -> (vz  : {g:_}->{a:_} -> Var28 (snoc28 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var28 g a -> Var28 (snoc28 g b) a)
 -> Var28 g a

vz28 : {g:_}->{a:_} -> Var28 (snoc28 g a) a
vz28 = \ var, vz28, vs => vz28

vs28 : {g:_}->{b:_}->{a:_} -> Var28 g a -> Var28 (snoc28 g b) a
vs28 = \ x, var, vz28, vs28 => vs28 (x var vz28 vs28)

Tm28 : Con28 -> Ty28-> Type
Tm28 = \ g, a =>
    (Tm28    : Con28 -> Ty28-> Type)
 -> (var   : {g:_}->{a:_}-> Var28 g a -> Tm28 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm28 (snoc28 g a) b -> Tm28 g (arr28 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm28 g (arr28 a b) -> Tm28 g a -> Tm28 g b)
 -> (tt    : {g:_}-> Tm28 g top28)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm28 g a -> Tm28 g b -> Tm28 g (prod28 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm28 g (prod28 a b) -> Tm28 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm28 g (prod28 a b) -> Tm28 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm28 g a -> Tm28 g (sum28 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm28 g b -> Tm28 g (sum28 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm28 g (sum28 a b) -> Tm28 g (arr28 a c) -> Tm28 g (arr28 b c) -> Tm28 g c)
 -> (zero  : {g:_}-> Tm28 g nat28)
 -> (suc   : {g:_}-> Tm28 g nat28 -> Tm28 g nat28)
 -> (rec   : {g:_}->{a:_} -> Tm28 g nat28 -> Tm28 g (arr28 nat28 (arr28 a a)) -> Tm28 g a -> Tm28 g a)
 -> Tm28 g a

var28 : {g:_}->{a:_} -> Var28 g a -> Tm28 g a
var28 = \ x, tm, var28, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var28 x

lam28 : {g:_}->{a:_}->{b:_}-> Tm28 (snoc28 g a) b -> Tm28 g (arr28 a b)
lam28 = \ t, tm, var28, lam28, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam28 (t tm var28 lam28 app tt pair fst snd left right split zero suc rec)

app28 : {g:_}->{a:_}->{b:_} -> Tm28 g (arr28 a b) -> Tm28 g a -> Tm28 g b
app28 = \ t, u, tm, var28, lam28, app28, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app28 (t tm var28 lam28 app28 tt pair fst snd left right split zero suc rec)
         (u tm var28 lam28 app28 tt pair fst snd left right split zero suc rec)

tt28 : {g:_} -> Tm28 g Main.top28
tt28 = \ tm, var28, lam28, app28, tt28, pair, fst, snd, left, right, split, zero, suc, rec => tt28

pair28 : {g:_}->{a:_}->{b:_} -> Tm28 g a -> Tm28 g b -> Tm28 g (prod28 a b)
pair28 = \ t, u, tm, var28, lam28, app28, tt28, pair28, fst, snd, left, right, split, zero, suc, rec =>
     pair28 (t tm var28 lam28 app28 tt28 pair28 fst snd left right split zero suc rec)
          (u tm var28 lam28 app28 tt28 pair28 fst snd left right split zero suc rec)

fst28 : {g:_}->{a:_}->{b:_}-> Tm28 g (prod28 a b) -> Tm28 g a
fst28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd, left, right, split, zero, suc, rec =>
     fst28 (t tm var28 lam28 app28 tt28 pair28 fst28 snd left right split zero suc rec)

snd28 : {g:_}->{a:_}->{b:_} -> Tm28 g (prod28 a b) -> Tm28 g b
snd28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left, right, split, zero, suc, rec =>
     snd28 (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left right split zero suc rec)

left28 : {g:_}->{a:_}->{b:_} -> Tm28 g a -> Tm28 g (sum28 a b)
left28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right, split, zero, suc, rec =>
     left28 (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right split zero suc rec)

right28 : {g:_}->{a:_}->{b:_} -> Tm28 g b -> Tm28 g (sum28 a b)
right28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split, zero, suc, rec =>
     right28 (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split zero suc rec)

split28 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm28 g (sum28 a b) -> Tm28 g (arr28 a c) -> Tm28 g (arr28 b c) -> Tm28 g c
split28 = \ t, u, v, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split28, zero, suc, rec =>
     split28 (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero suc rec)
          (u tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero suc rec)
          (v tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero suc rec)

zero28 : {g:_} -> Tm28 g Main.nat28
zero28 = \ tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split28, zero28, suc, rec => zero28

suc28 : {g:_} -> Tm28 g Main.nat28 -> Tm28 g Main.nat28
suc28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split28, zero28, suc28, rec =>
   suc28 (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero28 suc28 rec)

rec28 : {g:_}->{a:_} -> Tm28 g Main.nat28 -> Tm28 g (arr28 Main.nat28 (arr28 a a)) -> Tm28 g a -> Tm28 g a
rec28 = \ t, u, v, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split28, zero28, suc28, rec28 =>
     rec28 (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero28 suc28 rec28)
         (u tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero28 suc28 rec28)
         (v tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero28 suc28 rec28)

v028 : {g:_}->{a:_} -> Tm28 (snoc28 g a) a
v028 = var28 vz28

v128 : {g:_}->{a:_}->{b:_} -> Tm28 (snoc28 (snoc28 g a) b) a
v128 = var28 (vs28 vz28)

v228 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm28 (snoc28 (snoc28 (snoc28 g a) b) c) a
v228 = var28 (vs28 (vs28 vz28))

v328 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm28 (snoc28 (snoc28 (snoc28 (snoc28 g a) b) c) d) a
v328 = var28 (vs28 (vs28 (vs28 vz28)))

tbool28 : Ty28
tbool28 = sum28 top28 top28

ttrue28 : {g:_} -> Tm28 g Main.tbool28
ttrue28 = left28 tt28

tfalse28 : {g:_} -> Tm28 g Main.tbool28
tfalse28 = right28 tt28

ifthenelse28 : {g:_}->{a:_} -> Tm28 g (arr28 Main.tbool28 (arr28 a (arr28 a a)))
ifthenelse28 = lam28 (lam28 (lam28 (split28 v228 (lam28 v228) (lam28 v128))))

times428 : {g:_}->{a:_} -> Tm28 g (arr28 (arr28 a a) (arr28 a a))
times428  = lam28 (lam28 (app28 v128 (app28 v128 (app28 v128 (app28 v128 v028)))))

add28 : {g:_} -> Tm28 g (arr28 Main.nat28 (arr28 Main.nat28 Main.nat28))
add28 = lam28 (rec28 v028
       (lam28 (lam28 (lam28 (suc28 (app28 v128 v028)))))
       (lam28 v028))

mul28 : {g:_} -> Tm28 g (arr28 Main.nat28 (arr28 Main.nat28 Main.nat28))
mul28 = lam28 (rec28 v028
       (lam28 (lam28 (lam28 (app28 (app28 add28 (app28 v128 v028)) v028))))
       (lam28 zero28))

fact28 : {g:_} -> Tm28 g (arr28 Main.nat28 Main.nat28)
fact28 = lam28 (rec28 v028 (lam28 (lam28 (app28 (app28 mul28 (suc28 v128)) v028)))
                 (suc28 zero28))

Ty29 : Type
Ty29 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat29 : Ty29
nat29 = \ _, nat29, _, _, _, _, _ => nat29
top29 : Ty29
top29 = \ _, _, top29, _, _, _, _ => top29
bot29 : Ty29
bot29 = \ _, _, _, bot29, _, _, _ => bot29

arr29 : Ty29-> Ty29-> Ty29
arr29 = \ a, b, ty, nat29, top29, bot29, arr29, prod, sum =>
     arr29 (a ty nat29 top29 bot29 arr29 prod sum) (b ty nat29 top29 bot29 arr29 prod sum)

prod29 : Ty29-> Ty29-> Ty29
prod29 = \ a, b, ty, nat29, top29, bot29, arr29, prod29, sum =>
     prod29 (a ty nat29 top29 bot29 arr29 prod29 sum) (b ty nat29 top29 bot29 arr29 prod29 sum)

sum29 : Ty29-> Ty29-> Ty29
sum29 = \ a, b, ty, nat29, top29, bot29, arr29, prod29, sum29 =>
     sum29 (a ty nat29 top29 bot29 arr29 prod29 sum29) (b ty nat29 top29 bot29 arr29 prod29 sum29)

Con29 : Type
Con29 = (Con29 : Type)
 -> (nil  : Con29)
 -> (snoc : Con29 -> Ty29-> Con29)
 -> Con29

nil29 : Con29
nil29 = \ con, nil29, snoc => nil29

snoc29 : Con29 -> Ty29-> Con29
snoc29 = \ g, a, con, nil29, snoc29 => snoc29 (g con nil29 snoc29) a

Var29 : Con29 -> Ty29-> Type
Var29 = \ g, a =>
    (Var29 : Con29 -> Ty29-> Type)
 -> (vz  : {g:_}->{a:_} -> Var29 (snoc29 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var29 g a -> Var29 (snoc29 g b) a)
 -> Var29 g a

vz29 : {g:_}->{a:_} -> Var29 (snoc29 g a) a
vz29 = \ var, vz29, vs => vz29

vs29 : {g:_}->{b:_}->{a:_} -> Var29 g a -> Var29 (snoc29 g b) a
vs29 = \ x, var, vz29, vs29 => vs29 (x var vz29 vs29)

Tm29 : Con29 -> Ty29-> Type
Tm29 = \ g, a =>
    (Tm29    : Con29 -> Ty29-> Type)
 -> (var   : {g:_}->{a:_}-> Var29 g a -> Tm29 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm29 (snoc29 g a) b -> Tm29 g (arr29 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm29 g (arr29 a b) -> Tm29 g a -> Tm29 g b)
 -> (tt    : {g:_}-> Tm29 g top29)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm29 g a -> Tm29 g b -> Tm29 g (prod29 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm29 g (prod29 a b) -> Tm29 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm29 g (prod29 a b) -> Tm29 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm29 g a -> Tm29 g (sum29 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm29 g b -> Tm29 g (sum29 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm29 g (sum29 a b) -> Tm29 g (arr29 a c) -> Tm29 g (arr29 b c) -> Tm29 g c)
 -> (zero  : {g:_}-> Tm29 g nat29)
 -> (suc   : {g:_}-> Tm29 g nat29 -> Tm29 g nat29)
 -> (rec   : {g:_}->{a:_} -> Tm29 g nat29 -> Tm29 g (arr29 nat29 (arr29 a a)) -> Tm29 g a -> Tm29 g a)
 -> Tm29 g a

var29 : {g:_}->{a:_} -> Var29 g a -> Tm29 g a
var29 = \ x, tm, var29, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var29 x

lam29 : {g:_}->{a:_}->{b:_}-> Tm29 (snoc29 g a) b -> Tm29 g (arr29 a b)
lam29 = \ t, tm, var29, lam29, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam29 (t tm var29 lam29 app tt pair fst snd left right split zero suc rec)

app29 : {g:_}->{a:_}->{b:_} -> Tm29 g (arr29 a b) -> Tm29 g a -> Tm29 g b
app29 = \ t, u, tm, var29, lam29, app29, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app29 (t tm var29 lam29 app29 tt pair fst snd left right split zero suc rec)
         (u tm var29 lam29 app29 tt pair fst snd left right split zero suc rec)

tt29 : {g:_} -> Tm29 g Main.top29
tt29 = \ tm, var29, lam29, app29, tt29, pair, fst, snd, left, right, split, zero, suc, rec => tt29

pair29 : {g:_}->{a:_}->{b:_} -> Tm29 g a -> Tm29 g b -> Tm29 g (prod29 a b)
pair29 = \ t, u, tm, var29, lam29, app29, tt29, pair29, fst, snd, left, right, split, zero, suc, rec =>
     pair29 (t tm var29 lam29 app29 tt29 pair29 fst snd left right split zero suc rec)
          (u tm var29 lam29 app29 tt29 pair29 fst snd left right split zero suc rec)

fst29 : {g:_}->{a:_}->{b:_}-> Tm29 g (prod29 a b) -> Tm29 g a
fst29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd, left, right, split, zero, suc, rec =>
     fst29 (t tm var29 lam29 app29 tt29 pair29 fst29 snd left right split zero suc rec)

snd29 : {g:_}->{a:_}->{b:_} -> Tm29 g (prod29 a b) -> Tm29 g b
snd29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left, right, split, zero, suc, rec =>
     snd29 (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left right split zero suc rec)

left29 : {g:_}->{a:_}->{b:_} -> Tm29 g a -> Tm29 g (sum29 a b)
left29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right, split, zero, suc, rec =>
     left29 (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right split zero suc rec)

right29 : {g:_}->{a:_}->{b:_} -> Tm29 g b -> Tm29 g (sum29 a b)
right29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split, zero, suc, rec =>
     right29 (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split zero suc rec)

split29 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm29 g (sum29 a b) -> Tm29 g (arr29 a c) -> Tm29 g (arr29 b c) -> Tm29 g c
split29 = \ t, u, v, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split29, zero, suc, rec =>
     split29 (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero suc rec)
          (u tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero suc rec)
          (v tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero suc rec)

zero29 : {g:_} -> Tm29 g Main.nat29
zero29 = \ tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split29, zero29, suc, rec => zero29

suc29 : {g:_} -> Tm29 g Main.nat29 -> Tm29 g Main.nat29
suc29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split29, zero29, suc29, rec =>
   suc29 (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero29 suc29 rec)

rec29 : {g:_}->{a:_} -> Tm29 g Main.nat29 -> Tm29 g (arr29 Main.nat29 (arr29 a a)) -> Tm29 g a -> Tm29 g a
rec29 = \ t, u, v, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split29, zero29, suc29, rec29 =>
     rec29 (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero29 suc29 rec29)
         (u tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero29 suc29 rec29)
         (v tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero29 suc29 rec29)

v029 : {g:_}->{a:_} -> Tm29 (snoc29 g a) a
v029 = var29 vz29

v129 : {g:_}->{a:_}->{b:_} -> Tm29 (snoc29 (snoc29 g a) b) a
v129 = var29 (vs29 vz29)

v229 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm29 (snoc29 (snoc29 (snoc29 g a) b) c) a
v229 = var29 (vs29 (vs29 vz29))

v329 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm29 (snoc29 (snoc29 (snoc29 (snoc29 g a) b) c) d) a
v329 = var29 (vs29 (vs29 (vs29 vz29)))

tbool29 : Ty29
tbool29 = sum29 top29 top29

ttrue29 : {g:_} -> Tm29 g Main.tbool29
ttrue29 = left29 tt29

tfalse29 : {g:_} -> Tm29 g Main.tbool29
tfalse29 = right29 tt29

ifthenelse29 : {g:_}->{a:_} -> Tm29 g (arr29 Main.tbool29 (arr29 a (arr29 a a)))
ifthenelse29 = lam29 (lam29 (lam29 (split29 v229 (lam29 v229) (lam29 v129))))

times429 : {g:_}->{a:_} -> Tm29 g (arr29 (arr29 a a) (arr29 a a))
times429  = lam29 (lam29 (app29 v129 (app29 v129 (app29 v129 (app29 v129 v029)))))

add29 : {g:_} -> Tm29 g (arr29 Main.nat29 (arr29 Main.nat29 Main.nat29))
add29 = lam29 (rec29 v029
       (lam29 (lam29 (lam29 (suc29 (app29 v129 v029)))))
       (lam29 v029))

mul29 : {g:_} -> Tm29 g (arr29 Main.nat29 (arr29 Main.nat29 Main.nat29))
mul29 = lam29 (rec29 v029
       (lam29 (lam29 (lam29 (app29 (app29 add29 (app29 v129 v029)) v029))))
       (lam29 zero29))

fact29 : {g:_} -> Tm29 g (arr29 Main.nat29 Main.nat29)
fact29 = lam29 (rec29 v029 (lam29 (lam29 (app29 (app29 mul29 (suc29 v129)) v029)))
                 (suc29 zero29))

Ty30 : Type
Ty30 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat30 : Ty30
nat30 = \ _, nat30, _, _, _, _, _ => nat30
top30 : Ty30
top30 = \ _, _, top30, _, _, _, _ => top30
bot30 : Ty30
bot30 = \ _, _, _, bot30, _, _, _ => bot30

arr30 : Ty30-> Ty30-> Ty30
arr30 = \ a, b, ty, nat30, top30, bot30, arr30, prod, sum =>
     arr30 (a ty nat30 top30 bot30 arr30 prod sum) (b ty nat30 top30 bot30 arr30 prod sum)

prod30 : Ty30-> Ty30-> Ty30
prod30 = \ a, b, ty, nat30, top30, bot30, arr30, prod30, sum =>
     prod30 (a ty nat30 top30 bot30 arr30 prod30 sum) (b ty nat30 top30 bot30 arr30 prod30 sum)

sum30 : Ty30-> Ty30-> Ty30
sum30 = \ a, b, ty, nat30, top30, bot30, arr30, prod30, sum30 =>
     sum30 (a ty nat30 top30 bot30 arr30 prod30 sum30) (b ty nat30 top30 bot30 arr30 prod30 sum30)

Con30 : Type
Con30 = (Con30 : Type)
 -> (nil  : Con30)
 -> (snoc : Con30 -> Ty30-> Con30)
 -> Con30

nil30 : Con30
nil30 = \ con, nil30, snoc => nil30

snoc30 : Con30 -> Ty30-> Con30
snoc30 = \ g, a, con, nil30, snoc30 => snoc30 (g con nil30 snoc30) a

Var30 : Con30 -> Ty30-> Type
Var30 = \ g, a =>
    (Var30 : Con30 -> Ty30-> Type)
 -> (vz  : {g:_}->{a:_} -> Var30 (snoc30 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var30 g a -> Var30 (snoc30 g b) a)
 -> Var30 g a

vz30 : {g:_}->{a:_} -> Var30 (snoc30 g a) a
vz30 = \ var, vz30, vs => vz30

vs30 : {g:_}->{b:_}->{a:_} -> Var30 g a -> Var30 (snoc30 g b) a
vs30 = \ x, var, vz30, vs30 => vs30 (x var vz30 vs30)

Tm30 : Con30 -> Ty30-> Type
Tm30 = \ g, a =>
    (Tm30    : Con30 -> Ty30-> Type)
 -> (var   : {g:_}->{a:_}-> Var30 g a -> Tm30 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm30 (snoc30 g a) b -> Tm30 g (arr30 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm30 g (arr30 a b) -> Tm30 g a -> Tm30 g b)
 -> (tt    : {g:_}-> Tm30 g top30)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm30 g a -> Tm30 g b -> Tm30 g (prod30 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm30 g (prod30 a b) -> Tm30 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm30 g (prod30 a b) -> Tm30 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm30 g a -> Tm30 g (sum30 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm30 g b -> Tm30 g (sum30 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm30 g (sum30 a b) -> Tm30 g (arr30 a c) -> Tm30 g (arr30 b c) -> Tm30 g c)
 -> (zero  : {g:_}-> Tm30 g nat30)
 -> (suc   : {g:_}-> Tm30 g nat30 -> Tm30 g nat30)
 -> (rec   : {g:_}->{a:_} -> Tm30 g nat30 -> Tm30 g (arr30 nat30 (arr30 a a)) -> Tm30 g a -> Tm30 g a)
 -> Tm30 g a

var30 : {g:_}->{a:_} -> Var30 g a -> Tm30 g a
var30 = \ x, tm, var30, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var30 x

lam30 : {g:_}->{a:_}->{b:_}-> Tm30 (snoc30 g a) b -> Tm30 g (arr30 a b)
lam30 = \ t, tm, var30, lam30, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam30 (t tm var30 lam30 app tt pair fst snd left right split zero suc rec)

app30 : {g:_}->{a:_}->{b:_} -> Tm30 g (arr30 a b) -> Tm30 g a -> Tm30 g b
app30 = \ t, u, tm, var30, lam30, app30, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app30 (t tm var30 lam30 app30 tt pair fst snd left right split zero suc rec)
         (u tm var30 lam30 app30 tt pair fst snd left right split zero suc rec)

tt30 : {g:_} -> Tm30 g Main.top30
tt30 = \ tm, var30, lam30, app30, tt30, pair, fst, snd, left, right, split, zero, suc, rec => tt30

pair30 : {g:_}->{a:_}->{b:_} -> Tm30 g a -> Tm30 g b -> Tm30 g (prod30 a b)
pair30 = \ t, u, tm, var30, lam30, app30, tt30, pair30, fst, snd, left, right, split, zero, suc, rec =>
     pair30 (t tm var30 lam30 app30 tt30 pair30 fst snd left right split zero suc rec)
          (u tm var30 lam30 app30 tt30 pair30 fst snd left right split zero suc rec)

fst30 : {g:_}->{a:_}->{b:_}-> Tm30 g (prod30 a b) -> Tm30 g a
fst30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd, left, right, split, zero, suc, rec =>
     fst30 (t tm var30 lam30 app30 tt30 pair30 fst30 snd left right split zero suc rec)

snd30 : {g:_}->{a:_}->{b:_} -> Tm30 g (prod30 a b) -> Tm30 g b
snd30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left, right, split, zero, suc, rec =>
     snd30 (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left right split zero suc rec)

left30 : {g:_}->{a:_}->{b:_} -> Tm30 g a -> Tm30 g (sum30 a b)
left30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right, split, zero, suc, rec =>
     left30 (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right split zero suc rec)

right30 : {g:_}->{a:_}->{b:_} -> Tm30 g b -> Tm30 g (sum30 a b)
right30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split, zero, suc, rec =>
     right30 (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split zero suc rec)

split30 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm30 g (sum30 a b) -> Tm30 g (arr30 a c) -> Tm30 g (arr30 b c) -> Tm30 g c
split30 = \ t, u, v, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split30, zero, suc, rec =>
     split30 (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero suc rec)
          (u tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero suc rec)
          (v tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero suc rec)

zero30 : {g:_} -> Tm30 g Main.nat30
zero30 = \ tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split30, zero30, suc, rec => zero30

suc30 : {g:_} -> Tm30 g Main.nat30 -> Tm30 g Main.nat30
suc30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split30, zero30, suc30, rec =>
   suc30 (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero30 suc30 rec)

rec30 : {g:_}->{a:_} -> Tm30 g Main.nat30 -> Tm30 g (arr30 Main.nat30 (arr30 a a)) -> Tm30 g a -> Tm30 g a
rec30 = \ t, u, v, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split30, zero30, suc30, rec30 =>
     rec30 (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero30 suc30 rec30)
         (u tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero30 suc30 rec30)
         (v tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero30 suc30 rec30)

v030 : {g:_}->{a:_} -> Tm30 (snoc30 g a) a
v030 = var30 vz30

v130 : {g:_}->{a:_}->{b:_} -> Tm30 (snoc30 (snoc30 g a) b) a
v130 = var30 (vs30 vz30)

v230 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm30 (snoc30 (snoc30 (snoc30 g a) b) c) a
v230 = var30 (vs30 (vs30 vz30))

v330 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm30 (snoc30 (snoc30 (snoc30 (snoc30 g a) b) c) d) a
v330 = var30 (vs30 (vs30 (vs30 vz30)))

tbool30 : Ty30
tbool30 = sum30 top30 top30

ttrue30 : {g:_} -> Tm30 g Main.tbool30
ttrue30 = left30 tt30

tfalse30 : {g:_} -> Tm30 g Main.tbool30
tfalse30 = right30 tt30

ifthenelse30 : {g:_}->{a:_} -> Tm30 g (arr30 Main.tbool30 (arr30 a (arr30 a a)))
ifthenelse30 = lam30 (lam30 (lam30 (split30 v230 (lam30 v230) (lam30 v130))))

times430 : {g:_}->{a:_} -> Tm30 g (arr30 (arr30 a a) (arr30 a a))
times430  = lam30 (lam30 (app30 v130 (app30 v130 (app30 v130 (app30 v130 v030)))))

add30 : {g:_} -> Tm30 g (arr30 Main.nat30 (arr30 Main.nat30 Main.nat30))
add30 = lam30 (rec30 v030
       (lam30 (lam30 (lam30 (suc30 (app30 v130 v030)))))
       (lam30 v030))

mul30 : {g:_} -> Tm30 g (arr30 Main.nat30 (arr30 Main.nat30 Main.nat30))
mul30 = lam30 (rec30 v030
       (lam30 (lam30 (lam30 (app30 (app30 add30 (app30 v130 v030)) v030))))
       (lam30 zero30))

fact30 : {g:_} -> Tm30 g (arr30 Main.nat30 Main.nat30)
fact30 = lam30 (rec30 v030 (lam30 (lam30 (app30 (app30 mul30 (suc30 v130)) v030)))
                 (suc30 zero30))

Ty31 : Type
Ty31 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat31 : Ty31
nat31 = \ _, nat31, _, _, _, _, _ => nat31
top31 : Ty31
top31 = \ _, _, top31, _, _, _, _ => top31
bot31 : Ty31
bot31 = \ _, _, _, bot31, _, _, _ => bot31

arr31 : Ty31-> Ty31-> Ty31
arr31 = \ a, b, ty, nat31, top31, bot31, arr31, prod, sum =>
     arr31 (a ty nat31 top31 bot31 arr31 prod sum) (b ty nat31 top31 bot31 arr31 prod sum)

prod31 : Ty31-> Ty31-> Ty31
prod31 = \ a, b, ty, nat31, top31, bot31, arr31, prod31, sum =>
     prod31 (a ty nat31 top31 bot31 arr31 prod31 sum) (b ty nat31 top31 bot31 arr31 prod31 sum)

sum31 : Ty31-> Ty31-> Ty31
sum31 = \ a, b, ty, nat31, top31, bot31, arr31, prod31, sum31 =>
     sum31 (a ty nat31 top31 bot31 arr31 prod31 sum31) (b ty nat31 top31 bot31 arr31 prod31 sum31)

Con31 : Type
Con31 = (Con31 : Type)
 -> (nil  : Con31)
 -> (snoc : Con31 -> Ty31-> Con31)
 -> Con31

nil31 : Con31
nil31 = \ con, nil31, snoc => nil31

snoc31 : Con31 -> Ty31-> Con31
snoc31 = \ g, a, con, nil31, snoc31 => snoc31 (g con nil31 snoc31) a

Var31 : Con31 -> Ty31-> Type
Var31 = \ g, a =>
    (Var31 : Con31 -> Ty31-> Type)
 -> (vz  : {g:_}->{a:_} -> Var31 (snoc31 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var31 g a -> Var31 (snoc31 g b) a)
 -> Var31 g a

vz31 : {g:_}->{a:_} -> Var31 (snoc31 g a) a
vz31 = \ var, vz31, vs => vz31

vs31 : {g:_}->{b:_}->{a:_} -> Var31 g a -> Var31 (snoc31 g b) a
vs31 = \ x, var, vz31, vs31 => vs31 (x var vz31 vs31)

Tm31 : Con31 -> Ty31-> Type
Tm31 = \ g, a =>
    (Tm31    : Con31 -> Ty31-> Type)
 -> (var   : {g:_}->{a:_}-> Var31 g a -> Tm31 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm31 (snoc31 g a) b -> Tm31 g (arr31 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm31 g (arr31 a b) -> Tm31 g a -> Tm31 g b)
 -> (tt    : {g:_}-> Tm31 g top31)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm31 g a -> Tm31 g b -> Tm31 g (prod31 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm31 g (prod31 a b) -> Tm31 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm31 g (prod31 a b) -> Tm31 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm31 g a -> Tm31 g (sum31 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm31 g b -> Tm31 g (sum31 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm31 g (sum31 a b) -> Tm31 g (arr31 a c) -> Tm31 g (arr31 b c) -> Tm31 g c)
 -> (zero  : {g:_}-> Tm31 g nat31)
 -> (suc   : {g:_}-> Tm31 g nat31 -> Tm31 g nat31)
 -> (rec   : {g:_}->{a:_} -> Tm31 g nat31 -> Tm31 g (arr31 nat31 (arr31 a a)) -> Tm31 g a -> Tm31 g a)
 -> Tm31 g a

var31 : {g:_}->{a:_} -> Var31 g a -> Tm31 g a
var31 = \ x, tm, var31, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var31 x

lam31 : {g:_}->{a:_}->{b:_}-> Tm31 (snoc31 g a) b -> Tm31 g (arr31 a b)
lam31 = \ t, tm, var31, lam31, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam31 (t tm var31 lam31 app tt pair fst snd left right split zero suc rec)

app31 : {g:_}->{a:_}->{b:_} -> Tm31 g (arr31 a b) -> Tm31 g a -> Tm31 g b
app31 = \ t, u, tm, var31, lam31, app31, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app31 (t tm var31 lam31 app31 tt pair fst snd left right split zero suc rec)
         (u tm var31 lam31 app31 tt pair fst snd left right split zero suc rec)

tt31 : {g:_} -> Tm31 g Main.top31
tt31 = \ tm, var31, lam31, app31, tt31, pair, fst, snd, left, right, split, zero, suc, rec => tt31

pair31 : {g:_}->{a:_}->{b:_} -> Tm31 g a -> Tm31 g b -> Tm31 g (prod31 a b)
pair31 = \ t, u, tm, var31, lam31, app31, tt31, pair31, fst, snd, left, right, split, zero, suc, rec =>
     pair31 (t tm var31 lam31 app31 tt31 pair31 fst snd left right split zero suc rec)
          (u tm var31 lam31 app31 tt31 pair31 fst snd left right split zero suc rec)

fst31 : {g:_}->{a:_}->{b:_}-> Tm31 g (prod31 a b) -> Tm31 g a
fst31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd, left, right, split, zero, suc, rec =>
     fst31 (t tm var31 lam31 app31 tt31 pair31 fst31 snd left right split zero suc rec)

snd31 : {g:_}->{a:_}->{b:_} -> Tm31 g (prod31 a b) -> Tm31 g b
snd31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left, right, split, zero, suc, rec =>
     snd31 (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left right split zero suc rec)

left31 : {g:_}->{a:_}->{b:_} -> Tm31 g a -> Tm31 g (sum31 a b)
left31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right, split, zero, suc, rec =>
     left31 (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right split zero suc rec)

right31 : {g:_}->{a:_}->{b:_} -> Tm31 g b -> Tm31 g (sum31 a b)
right31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split, zero, suc, rec =>
     right31 (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split zero suc rec)

split31 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm31 g (sum31 a b) -> Tm31 g (arr31 a c) -> Tm31 g (arr31 b c) -> Tm31 g c
split31 = \ t, u, v, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split31, zero, suc, rec =>
     split31 (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero suc rec)
          (u tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero suc rec)
          (v tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero suc rec)

zero31 : {g:_} -> Tm31 g Main.nat31
zero31 = \ tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split31, zero31, suc, rec => zero31

suc31 : {g:_} -> Tm31 g Main.nat31 -> Tm31 g Main.nat31
suc31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split31, zero31, suc31, rec =>
   suc31 (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero31 suc31 rec)

rec31 : {g:_}->{a:_} -> Tm31 g Main.nat31 -> Tm31 g (arr31 Main.nat31 (arr31 a a)) -> Tm31 g a -> Tm31 g a
rec31 = \ t, u, v, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split31, zero31, suc31, rec31 =>
     rec31 (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero31 suc31 rec31)
         (u tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero31 suc31 rec31)
         (v tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero31 suc31 rec31)

v031 : {g:_}->{a:_} -> Tm31 (snoc31 g a) a
v031 = var31 vz31

v131 : {g:_}->{a:_}->{b:_} -> Tm31 (snoc31 (snoc31 g a) b) a
v131 = var31 (vs31 vz31)

v231 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm31 (snoc31 (snoc31 (snoc31 g a) b) c) a
v231 = var31 (vs31 (vs31 vz31))

v331 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm31 (snoc31 (snoc31 (snoc31 (snoc31 g a) b) c) d) a
v331 = var31 (vs31 (vs31 (vs31 vz31)))

tbool31 : Ty31
tbool31 = sum31 top31 top31

ttrue31 : {g:_} -> Tm31 g Main.tbool31
ttrue31 = left31 tt31

tfalse31 : {g:_} -> Tm31 g Main.tbool31
tfalse31 = right31 tt31

ifthenelse31 : {g:_}->{a:_} -> Tm31 g (arr31 Main.tbool31 (arr31 a (arr31 a a)))
ifthenelse31 = lam31 (lam31 (lam31 (split31 v231 (lam31 v231) (lam31 v131))))

times431 : {g:_}->{a:_} -> Tm31 g (arr31 (arr31 a a) (arr31 a a))
times431  = lam31 (lam31 (app31 v131 (app31 v131 (app31 v131 (app31 v131 v031)))))

add31 : {g:_} -> Tm31 g (arr31 Main.nat31 (arr31 Main.nat31 Main.nat31))
add31 = lam31 (rec31 v031
       (lam31 (lam31 (lam31 (suc31 (app31 v131 v031)))))
       (lam31 v031))

mul31 : {g:_} -> Tm31 g (arr31 Main.nat31 (arr31 Main.nat31 Main.nat31))
mul31 = lam31 (rec31 v031
       (lam31 (lam31 (lam31 (app31 (app31 add31 (app31 v131 v031)) v031))))
       (lam31 zero31))

fact31 : {g:_} -> Tm31 g (arr31 Main.nat31 Main.nat31)
fact31 = lam31 (rec31 v031 (lam31 (lam31 (app31 (app31 mul31 (suc31 v131)) v031)))
                 (suc31 zero31))

Ty32 : Type
Ty32 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat32 : Ty32
nat32 = \ _, nat32, _, _, _, _, _ => nat32
top32 : Ty32
top32 = \ _, _, top32, _, _, _, _ => top32
bot32 : Ty32
bot32 = \ _, _, _, bot32, _, _, _ => bot32

arr32 : Ty32-> Ty32-> Ty32
arr32 = \ a, b, ty, nat32, top32, bot32, arr32, prod, sum =>
     arr32 (a ty nat32 top32 bot32 arr32 prod sum) (b ty nat32 top32 bot32 arr32 prod sum)

prod32 : Ty32-> Ty32-> Ty32
prod32 = \ a, b, ty, nat32, top32, bot32, arr32, prod32, sum =>
     prod32 (a ty nat32 top32 bot32 arr32 prod32 sum) (b ty nat32 top32 bot32 arr32 prod32 sum)

sum32 : Ty32-> Ty32-> Ty32
sum32 = \ a, b, ty, nat32, top32, bot32, arr32, prod32, sum32 =>
     sum32 (a ty nat32 top32 bot32 arr32 prod32 sum32) (b ty nat32 top32 bot32 arr32 prod32 sum32)

Con32 : Type
Con32 = (Con32 : Type)
 -> (nil  : Con32)
 -> (snoc : Con32 -> Ty32-> Con32)
 -> Con32

nil32 : Con32
nil32 = \ con, nil32, snoc => nil32

snoc32 : Con32 -> Ty32-> Con32
snoc32 = \ g, a, con, nil32, snoc32 => snoc32 (g con nil32 snoc32) a

Var32 : Con32 -> Ty32-> Type
Var32 = \ g, a =>
    (Var32 : Con32 -> Ty32-> Type)
 -> (vz  : {g:_}->{a:_} -> Var32 (snoc32 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var32 g a -> Var32 (snoc32 g b) a)
 -> Var32 g a

vz32 : {g:_}->{a:_} -> Var32 (snoc32 g a) a
vz32 = \ var, vz32, vs => vz32

vs32 : {g:_}->{b:_}->{a:_} -> Var32 g a -> Var32 (snoc32 g b) a
vs32 = \ x, var, vz32, vs32 => vs32 (x var vz32 vs32)

Tm32 : Con32 -> Ty32-> Type
Tm32 = \ g, a =>
    (Tm32    : Con32 -> Ty32-> Type)
 -> (var   : {g:_}->{a:_}-> Var32 g a -> Tm32 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm32 (snoc32 g a) b -> Tm32 g (arr32 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm32 g (arr32 a b) -> Tm32 g a -> Tm32 g b)
 -> (tt    : {g:_}-> Tm32 g top32)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm32 g a -> Tm32 g b -> Tm32 g (prod32 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm32 g (prod32 a b) -> Tm32 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm32 g (prod32 a b) -> Tm32 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm32 g a -> Tm32 g (sum32 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm32 g b -> Tm32 g (sum32 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm32 g (sum32 a b) -> Tm32 g (arr32 a c) -> Tm32 g (arr32 b c) -> Tm32 g c)
 -> (zero  : {g:_}-> Tm32 g nat32)
 -> (suc   : {g:_}-> Tm32 g nat32 -> Tm32 g nat32)
 -> (rec   : {g:_}->{a:_} -> Tm32 g nat32 -> Tm32 g (arr32 nat32 (arr32 a a)) -> Tm32 g a -> Tm32 g a)
 -> Tm32 g a

var32 : {g:_}->{a:_} -> Var32 g a -> Tm32 g a
var32 = \ x, tm, var32, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var32 x

lam32 : {g:_}->{a:_}->{b:_}-> Tm32 (snoc32 g a) b -> Tm32 g (arr32 a b)
lam32 = \ t, tm, var32, lam32, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam32 (t tm var32 lam32 app tt pair fst snd left right split zero suc rec)

app32 : {g:_}->{a:_}->{b:_} -> Tm32 g (arr32 a b) -> Tm32 g a -> Tm32 g b
app32 = \ t, u, tm, var32, lam32, app32, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app32 (t tm var32 lam32 app32 tt pair fst snd left right split zero suc rec)
         (u tm var32 lam32 app32 tt pair fst snd left right split zero suc rec)

tt32 : {g:_} -> Tm32 g Main.top32
tt32 = \ tm, var32, lam32, app32, tt32, pair, fst, snd, left, right, split, zero, suc, rec => tt32

pair32 : {g:_}->{a:_}->{b:_} -> Tm32 g a -> Tm32 g b -> Tm32 g (prod32 a b)
pair32 = \ t, u, tm, var32, lam32, app32, tt32, pair32, fst, snd, left, right, split, zero, suc, rec =>
     pair32 (t tm var32 lam32 app32 tt32 pair32 fst snd left right split zero suc rec)
          (u tm var32 lam32 app32 tt32 pair32 fst snd left right split zero suc rec)

fst32 : {g:_}->{a:_}->{b:_}-> Tm32 g (prod32 a b) -> Tm32 g a
fst32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd, left, right, split, zero, suc, rec =>
     fst32 (t tm var32 lam32 app32 tt32 pair32 fst32 snd left right split zero suc rec)

snd32 : {g:_}->{a:_}->{b:_} -> Tm32 g (prod32 a b) -> Tm32 g b
snd32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left, right, split, zero, suc, rec =>
     snd32 (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left right split zero suc rec)

left32 : {g:_}->{a:_}->{b:_} -> Tm32 g a -> Tm32 g (sum32 a b)
left32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right, split, zero, suc, rec =>
     left32 (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right split zero suc rec)

right32 : {g:_}->{a:_}->{b:_} -> Tm32 g b -> Tm32 g (sum32 a b)
right32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split, zero, suc, rec =>
     right32 (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split zero suc rec)

split32 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm32 g (sum32 a b) -> Tm32 g (arr32 a c) -> Tm32 g (arr32 b c) -> Tm32 g c
split32 = \ t, u, v, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split32, zero, suc, rec =>
     split32 (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero suc rec)
          (u tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero suc rec)
          (v tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero suc rec)

zero32 : {g:_} -> Tm32 g Main.nat32
zero32 = \ tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split32, zero32, suc, rec => zero32

suc32 : {g:_} -> Tm32 g Main.nat32 -> Tm32 g Main.nat32
suc32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split32, zero32, suc32, rec =>
   suc32 (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero32 suc32 rec)

rec32 : {g:_}->{a:_} -> Tm32 g Main.nat32 -> Tm32 g (arr32 Main.nat32 (arr32 a a)) -> Tm32 g a -> Tm32 g a
rec32 = \ t, u, v, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split32, zero32, suc32, rec32 =>
     rec32 (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero32 suc32 rec32)
         (u tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero32 suc32 rec32)
         (v tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero32 suc32 rec32)

v032 : {g:_}->{a:_} -> Tm32 (snoc32 g a) a
v032 = var32 vz32

v132 : {g:_}->{a:_}->{b:_} -> Tm32 (snoc32 (snoc32 g a) b) a
v132 = var32 (vs32 vz32)

v232 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm32 (snoc32 (snoc32 (snoc32 g a) b) c) a
v232 = var32 (vs32 (vs32 vz32))

v332 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm32 (snoc32 (snoc32 (snoc32 (snoc32 g a) b) c) d) a
v332 = var32 (vs32 (vs32 (vs32 vz32)))

tbool32 : Ty32
tbool32 = sum32 top32 top32

ttrue32 : {g:_} -> Tm32 g Main.tbool32
ttrue32 = left32 tt32

tfalse32 : {g:_} -> Tm32 g Main.tbool32
tfalse32 = right32 tt32

ifthenelse32 : {g:_}->{a:_} -> Tm32 g (arr32 Main.tbool32 (arr32 a (arr32 a a)))
ifthenelse32 = lam32 (lam32 (lam32 (split32 v232 (lam32 v232) (lam32 v132))))

times432 : {g:_}->{a:_} -> Tm32 g (arr32 (arr32 a a) (arr32 a a))
times432  = lam32 (lam32 (app32 v132 (app32 v132 (app32 v132 (app32 v132 v032)))))

add32 : {g:_} -> Tm32 g (arr32 Main.nat32 (arr32 Main.nat32 Main.nat32))
add32 = lam32 (rec32 v032
       (lam32 (lam32 (lam32 (suc32 (app32 v132 v032)))))
       (lam32 v032))

mul32 : {g:_} -> Tm32 g (arr32 Main.nat32 (arr32 Main.nat32 Main.nat32))
mul32 = lam32 (rec32 v032
       (lam32 (lam32 (lam32 (app32 (app32 add32 (app32 v132 v032)) v032))))
       (lam32 zero32))

fact32 : {g:_} -> Tm32 g (arr32 Main.nat32 Main.nat32)
fact32 = lam32 (rec32 v032 (lam32 (lam32 (app32 (app32 mul32 (suc32 v132)) v032)))
                 (suc32 zero32))

Ty33 : Type
Ty33 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat33 : Ty33
nat33 = \ _, nat33, _, _, _, _, _ => nat33
top33 : Ty33
top33 = \ _, _, top33, _, _, _, _ => top33
bot33 : Ty33
bot33 = \ _, _, _, bot33, _, _, _ => bot33

arr33 : Ty33-> Ty33-> Ty33
arr33 = \ a, b, ty, nat33, top33, bot33, arr33, prod, sum =>
     arr33 (a ty nat33 top33 bot33 arr33 prod sum) (b ty nat33 top33 bot33 arr33 prod sum)

prod33 : Ty33-> Ty33-> Ty33
prod33 = \ a, b, ty, nat33, top33, bot33, arr33, prod33, sum =>
     prod33 (a ty nat33 top33 bot33 arr33 prod33 sum) (b ty nat33 top33 bot33 arr33 prod33 sum)

sum33 : Ty33-> Ty33-> Ty33
sum33 = \ a, b, ty, nat33, top33, bot33, arr33, prod33, sum33 =>
     sum33 (a ty nat33 top33 bot33 arr33 prod33 sum33) (b ty nat33 top33 bot33 arr33 prod33 sum33)

Con33 : Type
Con33 = (Con33 : Type)
 -> (nil  : Con33)
 -> (snoc : Con33 -> Ty33-> Con33)
 -> Con33

nil33 : Con33
nil33 = \ con, nil33, snoc => nil33

snoc33 : Con33 -> Ty33-> Con33
snoc33 = \ g, a, con, nil33, snoc33 => snoc33 (g con nil33 snoc33) a

Var33 : Con33 -> Ty33-> Type
Var33 = \ g, a =>
    (Var33 : Con33 -> Ty33-> Type)
 -> (vz  : {g:_}->{a:_} -> Var33 (snoc33 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var33 g a -> Var33 (snoc33 g b) a)
 -> Var33 g a

vz33 : {g:_}->{a:_} -> Var33 (snoc33 g a) a
vz33 = \ var, vz33, vs => vz33

vs33 : {g:_}->{b:_}->{a:_} -> Var33 g a -> Var33 (snoc33 g b) a
vs33 = \ x, var, vz33, vs33 => vs33 (x var vz33 vs33)

Tm33 : Con33 -> Ty33-> Type
Tm33 = \ g, a =>
    (Tm33    : Con33 -> Ty33-> Type)
 -> (var   : {g:_}->{a:_}-> Var33 g a -> Tm33 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm33 (snoc33 g a) b -> Tm33 g (arr33 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm33 g (arr33 a b) -> Tm33 g a -> Tm33 g b)
 -> (tt    : {g:_}-> Tm33 g top33)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm33 g a -> Tm33 g b -> Tm33 g (prod33 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm33 g (prod33 a b) -> Tm33 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm33 g (prod33 a b) -> Tm33 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm33 g a -> Tm33 g (sum33 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm33 g b -> Tm33 g (sum33 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm33 g (sum33 a b) -> Tm33 g (arr33 a c) -> Tm33 g (arr33 b c) -> Tm33 g c)
 -> (zero  : {g:_}-> Tm33 g nat33)
 -> (suc   : {g:_}-> Tm33 g nat33 -> Tm33 g nat33)
 -> (rec   : {g:_}->{a:_} -> Tm33 g nat33 -> Tm33 g (arr33 nat33 (arr33 a a)) -> Tm33 g a -> Tm33 g a)
 -> Tm33 g a

var33 : {g:_}->{a:_} -> Var33 g a -> Tm33 g a
var33 = \ x, tm, var33, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var33 x

lam33 : {g:_}->{a:_}->{b:_}-> Tm33 (snoc33 g a) b -> Tm33 g (arr33 a b)
lam33 = \ t, tm, var33, lam33, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam33 (t tm var33 lam33 app tt pair fst snd left right split zero suc rec)

app33 : {g:_}->{a:_}->{b:_} -> Tm33 g (arr33 a b) -> Tm33 g a -> Tm33 g b
app33 = \ t, u, tm, var33, lam33, app33, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app33 (t tm var33 lam33 app33 tt pair fst snd left right split zero suc rec)
         (u tm var33 lam33 app33 tt pair fst snd left right split zero suc rec)

tt33 : {g:_} -> Tm33 g Main.top33
tt33 = \ tm, var33, lam33, app33, tt33, pair, fst, snd, left, right, split, zero, suc, rec => tt33

pair33 : {g:_}->{a:_}->{b:_} -> Tm33 g a -> Tm33 g b -> Tm33 g (prod33 a b)
pair33 = \ t, u, tm, var33, lam33, app33, tt33, pair33, fst, snd, left, right, split, zero, suc, rec =>
     pair33 (t tm var33 lam33 app33 tt33 pair33 fst snd left right split zero suc rec)
          (u tm var33 lam33 app33 tt33 pair33 fst snd left right split zero suc rec)

fst33 : {g:_}->{a:_}->{b:_}-> Tm33 g (prod33 a b) -> Tm33 g a
fst33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd, left, right, split, zero, suc, rec =>
     fst33 (t tm var33 lam33 app33 tt33 pair33 fst33 snd left right split zero suc rec)

snd33 : {g:_}->{a:_}->{b:_} -> Tm33 g (prod33 a b) -> Tm33 g b
snd33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left, right, split, zero, suc, rec =>
     snd33 (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left right split zero suc rec)

left33 : {g:_}->{a:_}->{b:_} -> Tm33 g a -> Tm33 g (sum33 a b)
left33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right, split, zero, suc, rec =>
     left33 (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right split zero suc rec)

right33 : {g:_}->{a:_}->{b:_} -> Tm33 g b -> Tm33 g (sum33 a b)
right33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split, zero, suc, rec =>
     right33 (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split zero suc rec)

split33 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm33 g (sum33 a b) -> Tm33 g (arr33 a c) -> Tm33 g (arr33 b c) -> Tm33 g c
split33 = \ t, u, v, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split33, zero, suc, rec =>
     split33 (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero suc rec)
          (u tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero suc rec)
          (v tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero suc rec)

zero33 : {g:_} -> Tm33 g Main.nat33
zero33 = \ tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split33, zero33, suc, rec => zero33

suc33 : {g:_} -> Tm33 g Main.nat33 -> Tm33 g Main.nat33
suc33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split33, zero33, suc33, rec =>
   suc33 (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero33 suc33 rec)

rec33 : {g:_}->{a:_} -> Tm33 g Main.nat33 -> Tm33 g (arr33 Main.nat33 (arr33 a a)) -> Tm33 g a -> Tm33 g a
rec33 = \ t, u, v, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split33, zero33, suc33, rec33 =>
     rec33 (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero33 suc33 rec33)
         (u tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero33 suc33 rec33)
         (v tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero33 suc33 rec33)

v033 : {g:_}->{a:_} -> Tm33 (snoc33 g a) a
v033 = var33 vz33

v133 : {g:_}->{a:_}->{b:_} -> Tm33 (snoc33 (snoc33 g a) b) a
v133 = var33 (vs33 vz33)

v233 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm33 (snoc33 (snoc33 (snoc33 g a) b) c) a
v233 = var33 (vs33 (vs33 vz33))

v333 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm33 (snoc33 (snoc33 (snoc33 (snoc33 g a) b) c) d) a
v333 = var33 (vs33 (vs33 (vs33 vz33)))

tbool33 : Ty33
tbool33 = sum33 top33 top33

ttrue33 : {g:_} -> Tm33 g Main.tbool33
ttrue33 = left33 tt33

tfalse33 : {g:_} -> Tm33 g Main.tbool33
tfalse33 = right33 tt33

ifthenelse33 : {g:_}->{a:_} -> Tm33 g (arr33 Main.tbool33 (arr33 a (arr33 a a)))
ifthenelse33 = lam33 (lam33 (lam33 (split33 v233 (lam33 v233) (lam33 v133))))

times433 : {g:_}->{a:_} -> Tm33 g (arr33 (arr33 a a) (arr33 a a))
times433  = lam33 (lam33 (app33 v133 (app33 v133 (app33 v133 (app33 v133 v033)))))

add33 : {g:_} -> Tm33 g (arr33 Main.nat33 (arr33 Main.nat33 Main.nat33))
add33 = lam33 (rec33 v033
       (lam33 (lam33 (lam33 (suc33 (app33 v133 v033)))))
       (lam33 v033))

mul33 : {g:_} -> Tm33 g (arr33 Main.nat33 (arr33 Main.nat33 Main.nat33))
mul33 = lam33 (rec33 v033
       (lam33 (lam33 (lam33 (app33 (app33 add33 (app33 v133 v033)) v033))))
       (lam33 zero33))

fact33 : {g:_} -> Tm33 g (arr33 Main.nat33 Main.nat33)
fact33 = lam33 (rec33 v033 (lam33 (lam33 (app33 (app33 mul33 (suc33 v133)) v033)))
                 (suc33 zero33))

Ty34 : Type
Ty34 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat34 : Ty34
nat34 = \ _, nat34, _, _, _, _, _ => nat34
top34 : Ty34
top34 = \ _, _, top34, _, _, _, _ => top34
bot34 : Ty34
bot34 = \ _, _, _, bot34, _, _, _ => bot34

arr34 : Ty34-> Ty34-> Ty34
arr34 = \ a, b, ty, nat34, top34, bot34, arr34, prod, sum =>
     arr34 (a ty nat34 top34 bot34 arr34 prod sum) (b ty nat34 top34 bot34 arr34 prod sum)

prod34 : Ty34-> Ty34-> Ty34
prod34 = \ a, b, ty, nat34, top34, bot34, arr34, prod34, sum =>
     prod34 (a ty nat34 top34 bot34 arr34 prod34 sum) (b ty nat34 top34 bot34 arr34 prod34 sum)

sum34 : Ty34-> Ty34-> Ty34
sum34 = \ a, b, ty, nat34, top34, bot34, arr34, prod34, sum34 =>
     sum34 (a ty nat34 top34 bot34 arr34 prod34 sum34) (b ty nat34 top34 bot34 arr34 prod34 sum34)

Con34 : Type
Con34 = (Con34 : Type)
 -> (nil  : Con34)
 -> (snoc : Con34 -> Ty34-> Con34)
 -> Con34

nil34 : Con34
nil34 = \ con, nil34, snoc => nil34

snoc34 : Con34 -> Ty34-> Con34
snoc34 = \ g, a, con, nil34, snoc34 => snoc34 (g con nil34 snoc34) a

Var34 : Con34 -> Ty34-> Type
Var34 = \ g, a =>
    (Var34 : Con34 -> Ty34-> Type)
 -> (vz  : {g:_}->{a:_} -> Var34 (snoc34 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var34 g a -> Var34 (snoc34 g b) a)
 -> Var34 g a

vz34 : {g:_}->{a:_} -> Var34 (snoc34 g a) a
vz34 = \ var, vz34, vs => vz34

vs34 : {g:_}->{b:_}->{a:_} -> Var34 g a -> Var34 (snoc34 g b) a
vs34 = \ x, var, vz34, vs34 => vs34 (x var vz34 vs34)

Tm34 : Con34 -> Ty34-> Type
Tm34 = \ g, a =>
    (Tm34    : Con34 -> Ty34-> Type)
 -> (var   : {g:_}->{a:_}-> Var34 g a -> Tm34 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm34 (snoc34 g a) b -> Tm34 g (arr34 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm34 g (arr34 a b) -> Tm34 g a -> Tm34 g b)
 -> (tt    : {g:_}-> Tm34 g top34)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm34 g a -> Tm34 g b -> Tm34 g (prod34 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm34 g (prod34 a b) -> Tm34 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm34 g (prod34 a b) -> Tm34 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm34 g a -> Tm34 g (sum34 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm34 g b -> Tm34 g (sum34 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm34 g (sum34 a b) -> Tm34 g (arr34 a c) -> Tm34 g (arr34 b c) -> Tm34 g c)
 -> (zero  : {g:_}-> Tm34 g nat34)
 -> (suc   : {g:_}-> Tm34 g nat34 -> Tm34 g nat34)
 -> (rec   : {g:_}->{a:_} -> Tm34 g nat34 -> Tm34 g (arr34 nat34 (arr34 a a)) -> Tm34 g a -> Tm34 g a)
 -> Tm34 g a

var34 : {g:_}->{a:_} -> Var34 g a -> Tm34 g a
var34 = \ x, tm, var34, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var34 x

lam34 : {g:_}->{a:_}->{b:_}-> Tm34 (snoc34 g a) b -> Tm34 g (arr34 a b)
lam34 = \ t, tm, var34, lam34, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam34 (t tm var34 lam34 app tt pair fst snd left right split zero suc rec)

app34 : {g:_}->{a:_}->{b:_} -> Tm34 g (arr34 a b) -> Tm34 g a -> Tm34 g b
app34 = \ t, u, tm, var34, lam34, app34, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app34 (t tm var34 lam34 app34 tt pair fst snd left right split zero suc rec)
         (u tm var34 lam34 app34 tt pair fst snd left right split zero suc rec)

tt34 : {g:_} -> Tm34 g Main.top34
tt34 = \ tm, var34, lam34, app34, tt34, pair, fst, snd, left, right, split, zero, suc, rec => tt34

pair34 : {g:_}->{a:_}->{b:_} -> Tm34 g a -> Tm34 g b -> Tm34 g (prod34 a b)
pair34 = \ t, u, tm, var34, lam34, app34, tt34, pair34, fst, snd, left, right, split, zero, suc, rec =>
     pair34 (t tm var34 lam34 app34 tt34 pair34 fst snd left right split zero suc rec)
          (u tm var34 lam34 app34 tt34 pair34 fst snd left right split zero suc rec)

fst34 : {g:_}->{a:_}->{b:_}-> Tm34 g (prod34 a b) -> Tm34 g a
fst34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd, left, right, split, zero, suc, rec =>
     fst34 (t tm var34 lam34 app34 tt34 pair34 fst34 snd left right split zero suc rec)

snd34 : {g:_}->{a:_}->{b:_} -> Tm34 g (prod34 a b) -> Tm34 g b
snd34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left, right, split, zero, suc, rec =>
     snd34 (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left right split zero suc rec)

left34 : {g:_}->{a:_}->{b:_} -> Tm34 g a -> Tm34 g (sum34 a b)
left34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right, split, zero, suc, rec =>
     left34 (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right split zero suc rec)

right34 : {g:_}->{a:_}->{b:_} -> Tm34 g b -> Tm34 g (sum34 a b)
right34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split, zero, suc, rec =>
     right34 (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split zero suc rec)

split34 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm34 g (sum34 a b) -> Tm34 g (arr34 a c) -> Tm34 g (arr34 b c) -> Tm34 g c
split34 = \ t, u, v, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split34, zero, suc, rec =>
     split34 (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero suc rec)
          (u tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero suc rec)
          (v tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero suc rec)

zero34 : {g:_} -> Tm34 g Main.nat34
zero34 = \ tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split34, zero34, suc, rec => zero34

suc34 : {g:_} -> Tm34 g Main.nat34 -> Tm34 g Main.nat34
suc34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split34, zero34, suc34, rec =>
   suc34 (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero34 suc34 rec)

rec34 : {g:_}->{a:_} -> Tm34 g Main.nat34 -> Tm34 g (arr34 Main.nat34 (arr34 a a)) -> Tm34 g a -> Tm34 g a
rec34 = \ t, u, v, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split34, zero34, suc34, rec34 =>
     rec34 (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero34 suc34 rec34)
         (u tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero34 suc34 rec34)
         (v tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero34 suc34 rec34)

v034 : {g:_}->{a:_} -> Tm34 (snoc34 g a) a
v034 = var34 vz34

v134 : {g:_}->{a:_}->{b:_} -> Tm34 (snoc34 (snoc34 g a) b) a
v134 = var34 (vs34 vz34)

v234 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm34 (snoc34 (snoc34 (snoc34 g a) b) c) a
v234 = var34 (vs34 (vs34 vz34))

v334 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm34 (snoc34 (snoc34 (snoc34 (snoc34 g a) b) c) d) a
v334 = var34 (vs34 (vs34 (vs34 vz34)))

tbool34 : Ty34
tbool34 = sum34 top34 top34

ttrue34 : {g:_} -> Tm34 g Main.tbool34
ttrue34 = left34 tt34

tfalse34 : {g:_} -> Tm34 g Main.tbool34
tfalse34 = right34 tt34

ifthenelse34 : {g:_}->{a:_} -> Tm34 g (arr34 Main.tbool34 (arr34 a (arr34 a a)))
ifthenelse34 = lam34 (lam34 (lam34 (split34 v234 (lam34 v234) (lam34 v134))))

times434 : {g:_}->{a:_} -> Tm34 g (arr34 (arr34 a a) (arr34 a a))
times434  = lam34 (lam34 (app34 v134 (app34 v134 (app34 v134 (app34 v134 v034)))))

add34 : {g:_} -> Tm34 g (arr34 Main.nat34 (arr34 Main.nat34 Main.nat34))
add34 = lam34 (rec34 v034
       (lam34 (lam34 (lam34 (suc34 (app34 v134 v034)))))
       (lam34 v034))

mul34 : {g:_} -> Tm34 g (arr34 Main.nat34 (arr34 Main.nat34 Main.nat34))
mul34 = lam34 (rec34 v034
       (lam34 (lam34 (lam34 (app34 (app34 add34 (app34 v134 v034)) v034))))
       (lam34 zero34))

fact34 : {g:_} -> Tm34 g (arr34 Main.nat34 Main.nat34)
fact34 = lam34 (rec34 v034 (lam34 (lam34 (app34 (app34 mul34 (suc34 v134)) v034)))
                 (suc34 zero34))

Ty35 : Type
Ty35 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat35 : Ty35
nat35 = \ _, nat35, _, _, _, _, _ => nat35
top35 : Ty35
top35 = \ _, _, top35, _, _, _, _ => top35
bot35 : Ty35
bot35 = \ _, _, _, bot35, _, _, _ => bot35

arr35 : Ty35-> Ty35-> Ty35
arr35 = \ a, b, ty, nat35, top35, bot35, arr35, prod, sum =>
     arr35 (a ty nat35 top35 bot35 arr35 prod sum) (b ty nat35 top35 bot35 arr35 prod sum)

prod35 : Ty35-> Ty35-> Ty35
prod35 = \ a, b, ty, nat35, top35, bot35, arr35, prod35, sum =>
     prod35 (a ty nat35 top35 bot35 arr35 prod35 sum) (b ty nat35 top35 bot35 arr35 prod35 sum)

sum35 : Ty35-> Ty35-> Ty35
sum35 = \ a, b, ty, nat35, top35, bot35, arr35, prod35, sum35 =>
     sum35 (a ty nat35 top35 bot35 arr35 prod35 sum35) (b ty nat35 top35 bot35 arr35 prod35 sum35)

Con35 : Type
Con35 = (Con35 : Type)
 -> (nil  : Con35)
 -> (snoc : Con35 -> Ty35-> Con35)
 -> Con35

nil35 : Con35
nil35 = \ con, nil35, snoc => nil35

snoc35 : Con35 -> Ty35-> Con35
snoc35 = \ g, a, con, nil35, snoc35 => snoc35 (g con nil35 snoc35) a

Var35 : Con35 -> Ty35-> Type
Var35 = \ g, a =>
    (Var35 : Con35 -> Ty35-> Type)
 -> (vz  : {g:_}->{a:_} -> Var35 (snoc35 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var35 g a -> Var35 (snoc35 g b) a)
 -> Var35 g a

vz35 : {g:_}->{a:_} -> Var35 (snoc35 g a) a
vz35 = \ var, vz35, vs => vz35

vs35 : {g:_}->{b:_}->{a:_} -> Var35 g a -> Var35 (snoc35 g b) a
vs35 = \ x, var, vz35, vs35 => vs35 (x var vz35 vs35)

Tm35 : Con35 -> Ty35-> Type
Tm35 = \ g, a =>
    (Tm35    : Con35 -> Ty35-> Type)
 -> (var   : {g:_}->{a:_}-> Var35 g a -> Tm35 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm35 (snoc35 g a) b -> Tm35 g (arr35 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm35 g (arr35 a b) -> Tm35 g a -> Tm35 g b)
 -> (tt    : {g:_}-> Tm35 g top35)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm35 g a -> Tm35 g b -> Tm35 g (prod35 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm35 g (prod35 a b) -> Tm35 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm35 g (prod35 a b) -> Tm35 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm35 g a -> Tm35 g (sum35 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm35 g b -> Tm35 g (sum35 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm35 g (sum35 a b) -> Tm35 g (arr35 a c) -> Tm35 g (arr35 b c) -> Tm35 g c)
 -> (zero  : {g:_}-> Tm35 g nat35)
 -> (suc   : {g:_}-> Tm35 g nat35 -> Tm35 g nat35)
 -> (rec   : {g:_}->{a:_} -> Tm35 g nat35 -> Tm35 g (arr35 nat35 (arr35 a a)) -> Tm35 g a -> Tm35 g a)
 -> Tm35 g a

var35 : {g:_}->{a:_} -> Var35 g a -> Tm35 g a
var35 = \ x, tm, var35, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var35 x

lam35 : {g:_}->{a:_}->{b:_}-> Tm35 (snoc35 g a) b -> Tm35 g (arr35 a b)
lam35 = \ t, tm, var35, lam35, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam35 (t tm var35 lam35 app tt pair fst snd left right split zero suc rec)

app35 : {g:_}->{a:_}->{b:_} -> Tm35 g (arr35 a b) -> Tm35 g a -> Tm35 g b
app35 = \ t, u, tm, var35, lam35, app35, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app35 (t tm var35 lam35 app35 tt pair fst snd left right split zero suc rec)
         (u tm var35 lam35 app35 tt pair fst snd left right split zero suc rec)

tt35 : {g:_} -> Tm35 g Main.top35
tt35 = \ tm, var35, lam35, app35, tt35, pair, fst, snd, left, right, split, zero, suc, rec => tt35

pair35 : {g:_}->{a:_}->{b:_} -> Tm35 g a -> Tm35 g b -> Tm35 g (prod35 a b)
pair35 = \ t, u, tm, var35, lam35, app35, tt35, pair35, fst, snd, left, right, split, zero, suc, rec =>
     pair35 (t tm var35 lam35 app35 tt35 pair35 fst snd left right split zero suc rec)
          (u tm var35 lam35 app35 tt35 pair35 fst snd left right split zero suc rec)

fst35 : {g:_}->{a:_}->{b:_}-> Tm35 g (prod35 a b) -> Tm35 g a
fst35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd, left, right, split, zero, suc, rec =>
     fst35 (t tm var35 lam35 app35 tt35 pair35 fst35 snd left right split zero suc rec)

snd35 : {g:_}->{a:_}->{b:_} -> Tm35 g (prod35 a b) -> Tm35 g b
snd35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left, right, split, zero, suc, rec =>
     snd35 (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left right split zero suc rec)

left35 : {g:_}->{a:_}->{b:_} -> Tm35 g a -> Tm35 g (sum35 a b)
left35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right, split, zero, suc, rec =>
     left35 (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right split zero suc rec)

right35 : {g:_}->{a:_}->{b:_} -> Tm35 g b -> Tm35 g (sum35 a b)
right35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split, zero, suc, rec =>
     right35 (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split zero suc rec)

split35 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm35 g (sum35 a b) -> Tm35 g (arr35 a c) -> Tm35 g (arr35 b c) -> Tm35 g c
split35 = \ t, u, v, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split35, zero, suc, rec =>
     split35 (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero suc rec)
          (u tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero suc rec)
          (v tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero suc rec)

zero35 : {g:_} -> Tm35 g Main.nat35
zero35 = \ tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split35, zero35, suc, rec => zero35

suc35 : {g:_} -> Tm35 g Main.nat35 -> Tm35 g Main.nat35
suc35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split35, zero35, suc35, rec =>
   suc35 (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero35 suc35 rec)

rec35 : {g:_}->{a:_} -> Tm35 g Main.nat35 -> Tm35 g (arr35 Main.nat35 (arr35 a a)) -> Tm35 g a -> Tm35 g a
rec35 = \ t, u, v, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split35, zero35, suc35, rec35 =>
     rec35 (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero35 suc35 rec35)
         (u tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero35 suc35 rec35)
         (v tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero35 suc35 rec35)

v035 : {g:_}->{a:_} -> Tm35 (snoc35 g a) a
v035 = var35 vz35

v135 : {g:_}->{a:_}->{b:_} -> Tm35 (snoc35 (snoc35 g a) b) a
v135 = var35 (vs35 vz35)

v235 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm35 (snoc35 (snoc35 (snoc35 g a) b) c) a
v235 = var35 (vs35 (vs35 vz35))

v335 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm35 (snoc35 (snoc35 (snoc35 (snoc35 g a) b) c) d) a
v335 = var35 (vs35 (vs35 (vs35 vz35)))

tbool35 : Ty35
tbool35 = sum35 top35 top35

ttrue35 : {g:_} -> Tm35 g Main.tbool35
ttrue35 = left35 tt35

tfalse35 : {g:_} -> Tm35 g Main.tbool35
tfalse35 = right35 tt35

ifthenelse35 : {g:_}->{a:_} -> Tm35 g (arr35 Main.tbool35 (arr35 a (arr35 a a)))
ifthenelse35 = lam35 (lam35 (lam35 (split35 v235 (lam35 v235) (lam35 v135))))

times435 : {g:_}->{a:_} -> Tm35 g (arr35 (arr35 a a) (arr35 a a))
times435  = lam35 (lam35 (app35 v135 (app35 v135 (app35 v135 (app35 v135 v035)))))

add35 : {g:_} -> Tm35 g (arr35 Main.nat35 (arr35 Main.nat35 Main.nat35))
add35 = lam35 (rec35 v035
       (lam35 (lam35 (lam35 (suc35 (app35 v135 v035)))))
       (lam35 v035))

mul35 : {g:_} -> Tm35 g (arr35 Main.nat35 (arr35 Main.nat35 Main.nat35))
mul35 = lam35 (rec35 v035
       (lam35 (lam35 (lam35 (app35 (app35 add35 (app35 v135 v035)) v035))))
       (lam35 zero35))

fact35 : {g:_} -> Tm35 g (arr35 Main.nat35 Main.nat35)
fact35 = lam35 (rec35 v035 (lam35 (lam35 (app35 (app35 mul35 (suc35 v135)) v035)))
                 (suc35 zero35))

Ty36 : Type
Ty36 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat36 : Ty36
nat36 = \ _, nat36, _, _, _, _, _ => nat36
top36 : Ty36
top36 = \ _, _, top36, _, _, _, _ => top36
bot36 : Ty36
bot36 = \ _, _, _, bot36, _, _, _ => bot36

arr36 : Ty36-> Ty36-> Ty36
arr36 = \ a, b, ty, nat36, top36, bot36, arr36, prod, sum =>
     arr36 (a ty nat36 top36 bot36 arr36 prod sum) (b ty nat36 top36 bot36 arr36 prod sum)

prod36 : Ty36-> Ty36-> Ty36
prod36 = \ a, b, ty, nat36, top36, bot36, arr36, prod36, sum =>
     prod36 (a ty nat36 top36 bot36 arr36 prod36 sum) (b ty nat36 top36 bot36 arr36 prod36 sum)

sum36 : Ty36-> Ty36-> Ty36
sum36 = \ a, b, ty, nat36, top36, bot36, arr36, prod36, sum36 =>
     sum36 (a ty nat36 top36 bot36 arr36 prod36 sum36) (b ty nat36 top36 bot36 arr36 prod36 sum36)

Con36 : Type
Con36 = (Con36 : Type)
 -> (nil  : Con36)
 -> (snoc : Con36 -> Ty36-> Con36)
 -> Con36

nil36 : Con36
nil36 = \ con, nil36, snoc => nil36

snoc36 : Con36 -> Ty36-> Con36
snoc36 = \ g, a, con, nil36, snoc36 => snoc36 (g con nil36 snoc36) a

Var36 : Con36 -> Ty36-> Type
Var36 = \ g, a =>
    (Var36 : Con36 -> Ty36-> Type)
 -> (vz  : {g:_}->{a:_} -> Var36 (snoc36 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var36 g a -> Var36 (snoc36 g b) a)
 -> Var36 g a

vz36 : {g:_}->{a:_} -> Var36 (snoc36 g a) a
vz36 = \ var, vz36, vs => vz36

vs36 : {g:_}->{b:_}->{a:_} -> Var36 g a -> Var36 (snoc36 g b) a
vs36 = \ x, var, vz36, vs36 => vs36 (x var vz36 vs36)

Tm36 : Con36 -> Ty36-> Type
Tm36 = \ g, a =>
    (Tm36    : Con36 -> Ty36-> Type)
 -> (var   : {g:_}->{a:_}-> Var36 g a -> Tm36 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm36 (snoc36 g a) b -> Tm36 g (arr36 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm36 g (arr36 a b) -> Tm36 g a -> Tm36 g b)
 -> (tt    : {g:_}-> Tm36 g top36)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm36 g a -> Tm36 g b -> Tm36 g (prod36 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm36 g (prod36 a b) -> Tm36 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm36 g (prod36 a b) -> Tm36 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm36 g a -> Tm36 g (sum36 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm36 g b -> Tm36 g (sum36 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm36 g (sum36 a b) -> Tm36 g (arr36 a c) -> Tm36 g (arr36 b c) -> Tm36 g c)
 -> (zero  : {g:_}-> Tm36 g nat36)
 -> (suc   : {g:_}-> Tm36 g nat36 -> Tm36 g nat36)
 -> (rec   : {g:_}->{a:_} -> Tm36 g nat36 -> Tm36 g (arr36 nat36 (arr36 a a)) -> Tm36 g a -> Tm36 g a)
 -> Tm36 g a

var36 : {g:_}->{a:_} -> Var36 g a -> Tm36 g a
var36 = \ x, tm, var36, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var36 x

lam36 : {g:_}->{a:_}->{b:_}-> Tm36 (snoc36 g a) b -> Tm36 g (arr36 a b)
lam36 = \ t, tm, var36, lam36, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam36 (t tm var36 lam36 app tt pair fst snd left right split zero suc rec)

app36 : {g:_}->{a:_}->{b:_} -> Tm36 g (arr36 a b) -> Tm36 g a -> Tm36 g b
app36 = \ t, u, tm, var36, lam36, app36, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app36 (t tm var36 lam36 app36 tt pair fst snd left right split zero suc rec)
         (u tm var36 lam36 app36 tt pair fst snd left right split zero suc rec)

tt36 : {g:_} -> Tm36 g Main.top36
tt36 = \ tm, var36, lam36, app36, tt36, pair, fst, snd, left, right, split, zero, suc, rec => tt36

pair36 : {g:_}->{a:_}->{b:_} -> Tm36 g a -> Tm36 g b -> Tm36 g (prod36 a b)
pair36 = \ t, u, tm, var36, lam36, app36, tt36, pair36, fst, snd, left, right, split, zero, suc, rec =>
     pair36 (t tm var36 lam36 app36 tt36 pair36 fst snd left right split zero suc rec)
          (u tm var36 lam36 app36 tt36 pair36 fst snd left right split zero suc rec)

fst36 : {g:_}->{a:_}->{b:_}-> Tm36 g (prod36 a b) -> Tm36 g a
fst36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd, left, right, split, zero, suc, rec =>
     fst36 (t tm var36 lam36 app36 tt36 pair36 fst36 snd left right split zero suc rec)

snd36 : {g:_}->{a:_}->{b:_} -> Tm36 g (prod36 a b) -> Tm36 g b
snd36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left, right, split, zero, suc, rec =>
     snd36 (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left right split zero suc rec)

left36 : {g:_}->{a:_}->{b:_} -> Tm36 g a -> Tm36 g (sum36 a b)
left36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right, split, zero, suc, rec =>
     left36 (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right split zero suc rec)

right36 : {g:_}->{a:_}->{b:_} -> Tm36 g b -> Tm36 g (sum36 a b)
right36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split, zero, suc, rec =>
     right36 (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split zero suc rec)

split36 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm36 g (sum36 a b) -> Tm36 g (arr36 a c) -> Tm36 g (arr36 b c) -> Tm36 g c
split36 = \ t, u, v, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split36, zero, suc, rec =>
     split36 (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero suc rec)
          (u tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero suc rec)
          (v tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero suc rec)

zero36 : {g:_} -> Tm36 g Main.nat36
zero36 = \ tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split36, zero36, suc, rec => zero36

suc36 : {g:_} -> Tm36 g Main.nat36 -> Tm36 g Main.nat36
suc36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split36, zero36, suc36, rec =>
   suc36 (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero36 suc36 rec)

rec36 : {g:_}->{a:_} -> Tm36 g Main.nat36 -> Tm36 g (arr36 Main.nat36 (arr36 a a)) -> Tm36 g a -> Tm36 g a
rec36 = \ t, u, v, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split36, zero36, suc36, rec36 =>
     rec36 (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero36 suc36 rec36)
         (u tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero36 suc36 rec36)
         (v tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero36 suc36 rec36)

v036 : {g:_}->{a:_} -> Tm36 (snoc36 g a) a
v036 = var36 vz36

v136 : {g:_}->{a:_}->{b:_} -> Tm36 (snoc36 (snoc36 g a) b) a
v136 = var36 (vs36 vz36)

v236 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm36 (snoc36 (snoc36 (snoc36 g a) b) c) a
v236 = var36 (vs36 (vs36 vz36))

v336 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm36 (snoc36 (snoc36 (snoc36 (snoc36 g a) b) c) d) a
v336 = var36 (vs36 (vs36 (vs36 vz36)))

tbool36 : Ty36
tbool36 = sum36 top36 top36

ttrue36 : {g:_} -> Tm36 g Main.tbool36
ttrue36 = left36 tt36

tfalse36 : {g:_} -> Tm36 g Main.tbool36
tfalse36 = right36 tt36

ifthenelse36 : {g:_}->{a:_} -> Tm36 g (arr36 Main.tbool36 (arr36 a (arr36 a a)))
ifthenelse36 = lam36 (lam36 (lam36 (split36 v236 (lam36 v236) (lam36 v136))))

times436 : {g:_}->{a:_} -> Tm36 g (arr36 (arr36 a a) (arr36 a a))
times436  = lam36 (lam36 (app36 v136 (app36 v136 (app36 v136 (app36 v136 v036)))))

add36 : {g:_} -> Tm36 g (arr36 Main.nat36 (arr36 Main.nat36 Main.nat36))
add36 = lam36 (rec36 v036
       (lam36 (lam36 (lam36 (suc36 (app36 v136 v036)))))
       (lam36 v036))

mul36 : {g:_} -> Tm36 g (arr36 Main.nat36 (arr36 Main.nat36 Main.nat36))
mul36 = lam36 (rec36 v036
       (lam36 (lam36 (lam36 (app36 (app36 add36 (app36 v136 v036)) v036))))
       (lam36 zero36))

fact36 : {g:_} -> Tm36 g (arr36 Main.nat36 Main.nat36)
fact36 = lam36 (rec36 v036 (lam36 (lam36 (app36 (app36 mul36 (suc36 v136)) v036)))
                 (suc36 zero36))

Ty37 : Type
Ty37 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat37 : Ty37
nat37 = \ _, nat37, _, _, _, _, _ => nat37
top37 : Ty37
top37 = \ _, _, top37, _, _, _, _ => top37
bot37 : Ty37
bot37 = \ _, _, _, bot37, _, _, _ => bot37

arr37 : Ty37-> Ty37-> Ty37
arr37 = \ a, b, ty, nat37, top37, bot37, arr37, prod, sum =>
     arr37 (a ty nat37 top37 bot37 arr37 prod sum) (b ty nat37 top37 bot37 arr37 prod sum)

prod37 : Ty37-> Ty37-> Ty37
prod37 = \ a, b, ty, nat37, top37, bot37, arr37, prod37, sum =>
     prod37 (a ty nat37 top37 bot37 arr37 prod37 sum) (b ty nat37 top37 bot37 arr37 prod37 sum)

sum37 : Ty37-> Ty37-> Ty37
sum37 = \ a, b, ty, nat37, top37, bot37, arr37, prod37, sum37 =>
     sum37 (a ty nat37 top37 bot37 arr37 prod37 sum37) (b ty nat37 top37 bot37 arr37 prod37 sum37)

Con37 : Type
Con37 = (Con37 : Type)
 -> (nil  : Con37)
 -> (snoc : Con37 -> Ty37-> Con37)
 -> Con37

nil37 : Con37
nil37 = \ con, nil37, snoc => nil37

snoc37 : Con37 -> Ty37-> Con37
snoc37 = \ g, a, con, nil37, snoc37 => snoc37 (g con nil37 snoc37) a

Var37 : Con37 -> Ty37-> Type
Var37 = \ g, a =>
    (Var37 : Con37 -> Ty37-> Type)
 -> (vz  : {g:_}->{a:_} -> Var37 (snoc37 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var37 g a -> Var37 (snoc37 g b) a)
 -> Var37 g a

vz37 : {g:_}->{a:_} -> Var37 (snoc37 g a) a
vz37 = \ var, vz37, vs => vz37

vs37 : {g:_}->{b:_}->{a:_} -> Var37 g a -> Var37 (snoc37 g b) a
vs37 = \ x, var, vz37, vs37 => vs37 (x var vz37 vs37)

Tm37 : Con37 -> Ty37-> Type
Tm37 = \ g, a =>
    (Tm37    : Con37 -> Ty37-> Type)
 -> (var   : {g:_}->{a:_}-> Var37 g a -> Tm37 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm37 (snoc37 g a) b -> Tm37 g (arr37 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm37 g (arr37 a b) -> Tm37 g a -> Tm37 g b)
 -> (tt    : {g:_}-> Tm37 g top37)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm37 g a -> Tm37 g b -> Tm37 g (prod37 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm37 g (prod37 a b) -> Tm37 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm37 g (prod37 a b) -> Tm37 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm37 g a -> Tm37 g (sum37 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm37 g b -> Tm37 g (sum37 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm37 g (sum37 a b) -> Tm37 g (arr37 a c) -> Tm37 g (arr37 b c) -> Tm37 g c)
 -> (zero  : {g:_}-> Tm37 g nat37)
 -> (suc   : {g:_}-> Tm37 g nat37 -> Tm37 g nat37)
 -> (rec   : {g:_}->{a:_} -> Tm37 g nat37 -> Tm37 g (arr37 nat37 (arr37 a a)) -> Tm37 g a -> Tm37 g a)
 -> Tm37 g a

var37 : {g:_}->{a:_} -> Var37 g a -> Tm37 g a
var37 = \ x, tm, var37, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var37 x

lam37 : {g:_}->{a:_}->{b:_}-> Tm37 (snoc37 g a) b -> Tm37 g (arr37 a b)
lam37 = \ t, tm, var37, lam37, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam37 (t tm var37 lam37 app tt pair fst snd left right split zero suc rec)

app37 : {g:_}->{a:_}->{b:_} -> Tm37 g (arr37 a b) -> Tm37 g a -> Tm37 g b
app37 = \ t, u, tm, var37, lam37, app37, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app37 (t tm var37 lam37 app37 tt pair fst snd left right split zero suc rec)
         (u tm var37 lam37 app37 tt pair fst snd left right split zero suc rec)

tt37 : {g:_} -> Tm37 g Main.top37
tt37 = \ tm, var37, lam37, app37, tt37, pair, fst, snd, left, right, split, zero, suc, rec => tt37

pair37 : {g:_}->{a:_}->{b:_} -> Tm37 g a -> Tm37 g b -> Tm37 g (prod37 a b)
pair37 = \ t, u, tm, var37, lam37, app37, tt37, pair37, fst, snd, left, right, split, zero, suc, rec =>
     pair37 (t tm var37 lam37 app37 tt37 pair37 fst snd left right split zero suc rec)
          (u tm var37 lam37 app37 tt37 pair37 fst snd left right split zero suc rec)

fst37 : {g:_}->{a:_}->{b:_}-> Tm37 g (prod37 a b) -> Tm37 g a
fst37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd, left, right, split, zero, suc, rec =>
     fst37 (t tm var37 lam37 app37 tt37 pair37 fst37 snd left right split zero suc rec)

snd37 : {g:_}->{a:_}->{b:_} -> Tm37 g (prod37 a b) -> Tm37 g b
snd37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left, right, split, zero, suc, rec =>
     snd37 (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left right split zero suc rec)

left37 : {g:_}->{a:_}->{b:_} -> Tm37 g a -> Tm37 g (sum37 a b)
left37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right, split, zero, suc, rec =>
     left37 (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right split zero suc rec)

right37 : {g:_}->{a:_}->{b:_} -> Tm37 g b -> Tm37 g (sum37 a b)
right37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split, zero, suc, rec =>
     right37 (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split zero suc rec)

split37 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm37 g (sum37 a b) -> Tm37 g (arr37 a c) -> Tm37 g (arr37 b c) -> Tm37 g c
split37 = \ t, u, v, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split37, zero, suc, rec =>
     split37 (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero suc rec)
          (u tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero suc rec)
          (v tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero suc rec)

zero37 : {g:_} -> Tm37 g Main.nat37
zero37 = \ tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split37, zero37, suc, rec => zero37

suc37 : {g:_} -> Tm37 g Main.nat37 -> Tm37 g Main.nat37
suc37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split37, zero37, suc37, rec =>
   suc37 (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero37 suc37 rec)

rec37 : {g:_}->{a:_} -> Tm37 g Main.nat37 -> Tm37 g (arr37 Main.nat37 (arr37 a a)) -> Tm37 g a -> Tm37 g a
rec37 = \ t, u, v, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split37, zero37, suc37, rec37 =>
     rec37 (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero37 suc37 rec37)
         (u tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero37 suc37 rec37)
         (v tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero37 suc37 rec37)

v037 : {g:_}->{a:_} -> Tm37 (snoc37 g a) a
v037 = var37 vz37

v137 : {g:_}->{a:_}->{b:_} -> Tm37 (snoc37 (snoc37 g a) b) a
v137 = var37 (vs37 vz37)

v237 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm37 (snoc37 (snoc37 (snoc37 g a) b) c) a
v237 = var37 (vs37 (vs37 vz37))

v337 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm37 (snoc37 (snoc37 (snoc37 (snoc37 g a) b) c) d) a
v337 = var37 (vs37 (vs37 (vs37 vz37)))

tbool37 : Ty37
tbool37 = sum37 top37 top37

ttrue37 : {g:_} -> Tm37 g Main.tbool37
ttrue37 = left37 tt37

tfalse37 : {g:_} -> Tm37 g Main.tbool37
tfalse37 = right37 tt37

ifthenelse37 : {g:_}->{a:_} -> Tm37 g (arr37 Main.tbool37 (arr37 a (arr37 a a)))
ifthenelse37 = lam37 (lam37 (lam37 (split37 v237 (lam37 v237) (lam37 v137))))

times437 : {g:_}->{a:_} -> Tm37 g (arr37 (arr37 a a) (arr37 a a))
times437  = lam37 (lam37 (app37 v137 (app37 v137 (app37 v137 (app37 v137 v037)))))

add37 : {g:_} -> Tm37 g (arr37 Main.nat37 (arr37 Main.nat37 Main.nat37))
add37 = lam37 (rec37 v037
       (lam37 (lam37 (lam37 (suc37 (app37 v137 v037)))))
       (lam37 v037))

mul37 : {g:_} -> Tm37 g (arr37 Main.nat37 (arr37 Main.nat37 Main.nat37))
mul37 = lam37 (rec37 v037
       (lam37 (lam37 (lam37 (app37 (app37 add37 (app37 v137 v037)) v037))))
       (lam37 zero37))

fact37 : {g:_} -> Tm37 g (arr37 Main.nat37 Main.nat37)
fact37 = lam37 (rec37 v037 (lam37 (lam37 (app37 (app37 mul37 (suc37 v137)) v037)))
                 (suc37 zero37))

Ty38 : Type
Ty38 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat38 : Ty38
nat38 = \ _, nat38, _, _, _, _, _ => nat38
top38 : Ty38
top38 = \ _, _, top38, _, _, _, _ => top38
bot38 : Ty38
bot38 = \ _, _, _, bot38, _, _, _ => bot38

arr38 : Ty38-> Ty38-> Ty38
arr38 = \ a, b, ty, nat38, top38, bot38, arr38, prod, sum =>
     arr38 (a ty nat38 top38 bot38 arr38 prod sum) (b ty nat38 top38 bot38 arr38 prod sum)

prod38 : Ty38-> Ty38-> Ty38
prod38 = \ a, b, ty, nat38, top38, bot38, arr38, prod38, sum =>
     prod38 (a ty nat38 top38 bot38 arr38 prod38 sum) (b ty nat38 top38 bot38 arr38 prod38 sum)

sum38 : Ty38-> Ty38-> Ty38
sum38 = \ a, b, ty, nat38, top38, bot38, arr38, prod38, sum38 =>
     sum38 (a ty nat38 top38 bot38 arr38 prod38 sum38) (b ty nat38 top38 bot38 arr38 prod38 sum38)

Con38 : Type
Con38 = (Con38 : Type)
 -> (nil  : Con38)
 -> (snoc : Con38 -> Ty38-> Con38)
 -> Con38

nil38 : Con38
nil38 = \ con, nil38, snoc => nil38

snoc38 : Con38 -> Ty38-> Con38
snoc38 = \ g, a, con, nil38, snoc38 => snoc38 (g con nil38 snoc38) a

Var38 : Con38 -> Ty38-> Type
Var38 = \ g, a =>
    (Var38 : Con38 -> Ty38-> Type)
 -> (vz  : {g:_}->{a:_} -> Var38 (snoc38 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var38 g a -> Var38 (snoc38 g b) a)
 -> Var38 g a

vz38 : {g:_}->{a:_} -> Var38 (snoc38 g a) a
vz38 = \ var, vz38, vs => vz38

vs38 : {g:_}->{b:_}->{a:_} -> Var38 g a -> Var38 (snoc38 g b) a
vs38 = \ x, var, vz38, vs38 => vs38 (x var vz38 vs38)

Tm38 : Con38 -> Ty38-> Type
Tm38 = \ g, a =>
    (Tm38    : Con38 -> Ty38-> Type)
 -> (var   : {g:_}->{a:_}-> Var38 g a -> Tm38 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm38 (snoc38 g a) b -> Tm38 g (arr38 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm38 g (arr38 a b) -> Tm38 g a -> Tm38 g b)
 -> (tt    : {g:_}-> Tm38 g top38)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm38 g a -> Tm38 g b -> Tm38 g (prod38 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm38 g (prod38 a b) -> Tm38 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm38 g (prod38 a b) -> Tm38 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm38 g a -> Tm38 g (sum38 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm38 g b -> Tm38 g (sum38 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm38 g (sum38 a b) -> Tm38 g (arr38 a c) -> Tm38 g (arr38 b c) -> Tm38 g c)
 -> (zero  : {g:_}-> Tm38 g nat38)
 -> (suc   : {g:_}-> Tm38 g nat38 -> Tm38 g nat38)
 -> (rec   : {g:_}->{a:_} -> Tm38 g nat38 -> Tm38 g (arr38 nat38 (arr38 a a)) -> Tm38 g a -> Tm38 g a)
 -> Tm38 g a

var38 : {g:_}->{a:_} -> Var38 g a -> Tm38 g a
var38 = \ x, tm, var38, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var38 x

lam38 : {g:_}->{a:_}->{b:_}-> Tm38 (snoc38 g a) b -> Tm38 g (arr38 a b)
lam38 = \ t, tm, var38, lam38, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam38 (t tm var38 lam38 app tt pair fst snd left right split zero suc rec)

app38 : {g:_}->{a:_}->{b:_} -> Tm38 g (arr38 a b) -> Tm38 g a -> Tm38 g b
app38 = \ t, u, tm, var38, lam38, app38, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app38 (t tm var38 lam38 app38 tt pair fst snd left right split zero suc rec)
         (u tm var38 lam38 app38 tt pair fst snd left right split zero suc rec)

tt38 : {g:_} -> Tm38 g Main.top38
tt38 = \ tm, var38, lam38, app38, tt38, pair, fst, snd, left, right, split, zero, suc, rec => tt38

pair38 : {g:_}->{a:_}->{b:_} -> Tm38 g a -> Tm38 g b -> Tm38 g (prod38 a b)
pair38 = \ t, u, tm, var38, lam38, app38, tt38, pair38, fst, snd, left, right, split, zero, suc, rec =>
     pair38 (t tm var38 lam38 app38 tt38 pair38 fst snd left right split zero suc rec)
          (u tm var38 lam38 app38 tt38 pair38 fst snd left right split zero suc rec)

fst38 : {g:_}->{a:_}->{b:_}-> Tm38 g (prod38 a b) -> Tm38 g a
fst38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd, left, right, split, zero, suc, rec =>
     fst38 (t tm var38 lam38 app38 tt38 pair38 fst38 snd left right split zero suc rec)

snd38 : {g:_}->{a:_}->{b:_} -> Tm38 g (prod38 a b) -> Tm38 g b
snd38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left, right, split, zero, suc, rec =>
     snd38 (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left right split zero suc rec)

left38 : {g:_}->{a:_}->{b:_} -> Tm38 g a -> Tm38 g (sum38 a b)
left38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right, split, zero, suc, rec =>
     left38 (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right split zero suc rec)

right38 : {g:_}->{a:_}->{b:_} -> Tm38 g b -> Tm38 g (sum38 a b)
right38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split, zero, suc, rec =>
     right38 (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split zero suc rec)

split38 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm38 g (sum38 a b) -> Tm38 g (arr38 a c) -> Tm38 g (arr38 b c) -> Tm38 g c
split38 = \ t, u, v, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split38, zero, suc, rec =>
     split38 (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero suc rec)
          (u tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero suc rec)
          (v tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero suc rec)

zero38 : {g:_} -> Tm38 g Main.nat38
zero38 = \ tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split38, zero38, suc, rec => zero38

suc38 : {g:_} -> Tm38 g Main.nat38 -> Tm38 g Main.nat38
suc38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split38, zero38, suc38, rec =>
   suc38 (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero38 suc38 rec)

rec38 : {g:_}->{a:_} -> Tm38 g Main.nat38 -> Tm38 g (arr38 Main.nat38 (arr38 a a)) -> Tm38 g a -> Tm38 g a
rec38 = \ t, u, v, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split38, zero38, suc38, rec38 =>
     rec38 (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero38 suc38 rec38)
         (u tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero38 suc38 rec38)
         (v tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero38 suc38 rec38)

v038 : {g:_}->{a:_} -> Tm38 (snoc38 g a) a
v038 = var38 vz38

v138 : {g:_}->{a:_}->{b:_} -> Tm38 (snoc38 (snoc38 g a) b) a
v138 = var38 (vs38 vz38)

v238 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm38 (snoc38 (snoc38 (snoc38 g a) b) c) a
v238 = var38 (vs38 (vs38 vz38))

v338 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm38 (snoc38 (snoc38 (snoc38 (snoc38 g a) b) c) d) a
v338 = var38 (vs38 (vs38 (vs38 vz38)))

tbool38 : Ty38
tbool38 = sum38 top38 top38

ttrue38 : {g:_} -> Tm38 g Main.tbool38
ttrue38 = left38 tt38

tfalse38 : {g:_} -> Tm38 g Main.tbool38
tfalse38 = right38 tt38

ifthenelse38 : {g:_}->{a:_} -> Tm38 g (arr38 Main.tbool38 (arr38 a (arr38 a a)))
ifthenelse38 = lam38 (lam38 (lam38 (split38 v238 (lam38 v238) (lam38 v138))))

times438 : {g:_}->{a:_} -> Tm38 g (arr38 (arr38 a a) (arr38 a a))
times438  = lam38 (lam38 (app38 v138 (app38 v138 (app38 v138 (app38 v138 v038)))))

add38 : {g:_} -> Tm38 g (arr38 Main.nat38 (arr38 Main.nat38 Main.nat38))
add38 = lam38 (rec38 v038
       (lam38 (lam38 (lam38 (suc38 (app38 v138 v038)))))
       (lam38 v038))

mul38 : {g:_} -> Tm38 g (arr38 Main.nat38 (arr38 Main.nat38 Main.nat38))
mul38 = lam38 (rec38 v038
       (lam38 (lam38 (lam38 (app38 (app38 add38 (app38 v138 v038)) v038))))
       (lam38 zero38))

fact38 : {g:_} -> Tm38 g (arr38 Main.nat38 Main.nat38)
fact38 = lam38 (rec38 v038 (lam38 (lam38 (app38 (app38 mul38 (suc38 v138)) v038)))
                 (suc38 zero38))

Ty39 : Type
Ty39 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat39 : Ty39
nat39 = \ _, nat39, _, _, _, _, _ => nat39
top39 : Ty39
top39 = \ _, _, top39, _, _, _, _ => top39
bot39 : Ty39
bot39 = \ _, _, _, bot39, _, _, _ => bot39

arr39 : Ty39-> Ty39-> Ty39
arr39 = \ a, b, ty, nat39, top39, bot39, arr39, prod, sum =>
     arr39 (a ty nat39 top39 bot39 arr39 prod sum) (b ty nat39 top39 bot39 arr39 prod sum)

prod39 : Ty39-> Ty39-> Ty39
prod39 = \ a, b, ty, nat39, top39, bot39, arr39, prod39, sum =>
     prod39 (a ty nat39 top39 bot39 arr39 prod39 sum) (b ty nat39 top39 bot39 arr39 prod39 sum)

sum39 : Ty39-> Ty39-> Ty39
sum39 = \ a, b, ty, nat39, top39, bot39, arr39, prod39, sum39 =>
     sum39 (a ty nat39 top39 bot39 arr39 prod39 sum39) (b ty nat39 top39 bot39 arr39 prod39 sum39)

Con39 : Type
Con39 = (Con39 : Type)
 -> (nil  : Con39)
 -> (snoc : Con39 -> Ty39-> Con39)
 -> Con39

nil39 : Con39
nil39 = \ con, nil39, snoc => nil39

snoc39 : Con39 -> Ty39-> Con39
snoc39 = \ g, a, con, nil39, snoc39 => snoc39 (g con nil39 snoc39) a

Var39 : Con39 -> Ty39-> Type
Var39 = \ g, a =>
    (Var39 : Con39 -> Ty39-> Type)
 -> (vz  : {g:_}->{a:_} -> Var39 (snoc39 g a) a)
 -> (vs  : {g:_}->{b:_}->{a:_} -> Var39 g a -> Var39 (snoc39 g b) a)
 -> Var39 g a

vz39 : {g:_}->{a:_} -> Var39 (snoc39 g a) a
vz39 = \ var, vz39, vs => vz39

vs39 : {g:_}->{b:_}->{a:_} -> Var39 g a -> Var39 (snoc39 g b) a
vs39 = \ x, var, vz39, vs39 => vs39 (x var vz39 vs39)

Tm39 : Con39 -> Ty39-> Type
Tm39 = \ g, a =>
    (Tm39    : Con39 -> Ty39-> Type)
 -> (var   : {g:_}->{a:_}-> Var39 g a -> Tm39 g a)
 -> (lam   : {g:_}->{a:_}->{b:_} -> Tm39 (snoc39 g a) b -> Tm39 g (arr39 a b))
 -> (app   : {g:_}->{a:_}->{b:_} -> Tm39 g (arr39 a b) -> Tm39 g a -> Tm39 g b)
 -> (tt    : {g:_}-> Tm39 g top39)
 -> (pair  : {g:_}->{a:_}->{b:_} -> Tm39 g a -> Tm39 g b -> Tm39 g (prod39 a b))
 -> (fst   : {g:_}->{a:_}->{b:_} -> Tm39 g (prod39 a b) -> Tm39 g a)
 -> (snd   : {g:_}->{a:_}->{b:_} -> Tm39 g (prod39 a b) -> Tm39 g b)
 -> (left  : {g:_}->{a:_}->{b:_} -> Tm39 g a -> Tm39 g (sum39 a b))
 -> (right : {g:_}->{a:_}->{b:_} -> Tm39 g b -> Tm39 g (sum39 a b))
 -> (split : {g:_}->{a:_}->{b:_}-> {c:_} -> Tm39 g (sum39 a b) -> Tm39 g (arr39 a c) -> Tm39 g (arr39 b c) -> Tm39 g c)
 -> (zero  : {g:_}-> Tm39 g nat39)
 -> (suc   : {g:_}-> Tm39 g nat39 -> Tm39 g nat39)
 -> (rec   : {g:_}->{a:_} -> Tm39 g nat39 -> Tm39 g (arr39 nat39 (arr39 a a)) -> Tm39 g a -> Tm39 g a)
 -> Tm39 g a

var39 : {g:_}->{a:_} -> Var39 g a -> Tm39 g a
var39 = \ x, tm, var39, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var39 x

lam39 : {g:_}->{a:_}->{b:_}-> Tm39 (snoc39 g a) b -> Tm39 g (arr39 a b)
lam39 = \ t, tm, var39, lam39, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam39 (t tm var39 lam39 app tt pair fst snd left right split zero suc rec)

app39 : {g:_}->{a:_}->{b:_} -> Tm39 g (arr39 a b) -> Tm39 g a -> Tm39 g b
app39 = \ t, u, tm, var39, lam39, app39, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app39 (t tm var39 lam39 app39 tt pair fst snd left right split zero suc rec)
         (u tm var39 lam39 app39 tt pair fst snd left right split zero suc rec)

tt39 : {g:_} -> Tm39 g Main.top39
tt39 = \ tm, var39, lam39, app39, tt39, pair, fst, snd, left, right, split, zero, suc, rec => tt39

pair39 : {g:_}->{a:_}->{b:_} -> Tm39 g a -> Tm39 g b -> Tm39 g (prod39 a b)
pair39 = \ t, u, tm, var39, lam39, app39, tt39, pair39, fst, snd, left, right, split, zero, suc, rec =>
     pair39 (t tm var39 lam39 app39 tt39 pair39 fst snd left right split zero suc rec)
          (u tm var39 lam39 app39 tt39 pair39 fst snd left right split zero suc rec)

fst39 : {g:_}->{a:_}->{b:_}-> Tm39 g (prod39 a b) -> Tm39 g a
fst39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd, left, right, split, zero, suc, rec =>
     fst39 (t tm var39 lam39 app39 tt39 pair39 fst39 snd left right split zero suc rec)

snd39 : {g:_}->{a:_}->{b:_} -> Tm39 g (prod39 a b) -> Tm39 g b
snd39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left, right, split, zero, suc, rec =>
     snd39 (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left right split zero suc rec)

left39 : {g:_}->{a:_}->{b:_} -> Tm39 g a -> Tm39 g (sum39 a b)
left39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right, split, zero, suc, rec =>
     left39 (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right split zero suc rec)

right39 : {g:_}->{a:_}->{b:_} -> Tm39 g b -> Tm39 g (sum39 a b)
right39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split, zero, suc, rec =>
     right39 (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split zero suc rec)

split39 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm39 g (sum39 a b) -> Tm39 g (arr39 a c) -> Tm39 g (arr39 b c) -> Tm39 g c
split39 = \ t, u, v, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split39, zero, suc, rec =>
     split39 (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero suc rec)
          (u tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero suc rec)
          (v tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero suc rec)

zero39 : {g:_} -> Tm39 g Main.nat39
zero39 = \ tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split39, zero39, suc, rec => zero39

suc39 : {g:_} -> Tm39 g Main.nat39 -> Tm39 g Main.nat39
suc39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split39, zero39, suc39, rec =>
   suc39 (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero39 suc39 rec)

rec39 : {g:_}->{a:_} -> Tm39 g Main.nat39 -> Tm39 g (arr39 Main.nat39 (arr39 a a)) -> Tm39 g a -> Tm39 g a
rec39 = \ t, u, v, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split39, zero39, suc39, rec39 =>
     rec39 (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero39 suc39 rec39)
         (u tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero39 suc39 rec39)
         (v tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero39 suc39 rec39)

v039 : {g:_}->{a:_} -> Tm39 (snoc39 g a) a
v039 = var39 vz39

v139 : {g:_}->{a:_}->{b:_} -> Tm39 (snoc39 (snoc39 g a) b) a
v139 = var39 (vs39 vz39)

v239 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm39 (snoc39 (snoc39 (snoc39 g a) b) c) a
v239 = var39 (vs39 (vs39 vz39))

v339 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm39 (snoc39 (snoc39 (snoc39 (snoc39 g a) b) c) d) a
v339 = var39 (vs39 (vs39 (vs39 vz39)))

tbool39 : Ty39
tbool39 = sum39 top39 top39

ttrue39 : {g:_} -> Tm39 g Main.tbool39
ttrue39 = left39 tt39

tfalse39 : {g:_} -> Tm39 g Main.tbool39
tfalse39 = right39 tt39

ifthenelse39 : {g:_}->{a:_} -> Tm39 g (arr39 Main.tbool39 (arr39 a (arr39 a a)))
ifthenelse39 = lam39 (lam39 (lam39 (split39 v239 (lam39 v239) (lam39 v139))))

times439 : {g:_}->{a:_} -> Tm39 g (arr39 (arr39 a a) (arr39 a a))
times439  = lam39 (lam39 (app39 v139 (app39 v139 (app39 v139 (app39 v139 v039)))))

add39 : {g:_} -> Tm39 g (arr39 Main.nat39 (arr39 Main.nat39 Main.nat39))
add39 = lam39 (rec39 v039
       (lam39 (lam39 (lam39 (suc39 (app39 v139 v039)))))
       (lam39 v039))

mul39 : {g:_} -> Tm39 g (arr39 Main.nat39 (arr39 Main.nat39 Main.nat39))
mul39 = lam39 (rec39 v039
       (lam39 (lam39 (lam39 (app39 (app39 add39 (app39 v139 v039)) v039))))
       (lam39 zero39))

fact39 : {g:_} -> Tm39 g (arr39 Main.nat39 Main.nat39)
fact39 = lam39 (rec39 v039 (lam39 (lam39 (app39 (app39 mul39 (suc39 v139)) v039)))
                 (suc39 zero39))
