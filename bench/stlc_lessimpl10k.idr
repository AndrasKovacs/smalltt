
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
 -> (vz  : (g:_)->(a:_) -> Var (snoc g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var g a -> Var (snoc g b) a)
 -> Var g a

vz : {g:_}->{a:_} -> Var (snoc g a) a
vz = \ var, vz, vs => vz _ _

vs : {g:_}->{b:_}->{a:_} -> Var g a -> Var (snoc g b) a
vs = \ x, var, vz, vs => vs _ _ _ (x var vz vs)

Tm : Con -> Ty-> Type
Tm = \ g, a =>
    (Tm    : Con -> Ty-> Type)
 -> (var   : (g:_)->(a:_)-> Var g a -> Tm g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm (snoc g a) b -> Tm g (arr a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm g (arr a b) -> Tm g a -> Tm g b)
 -> (tt    : (g:_)-> Tm g top)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm g a -> Tm g b -> Tm g (prod a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm g (prod a b) -> Tm g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm g (prod a b) -> Tm g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm g a -> Tm g (sum a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm g b -> Tm g (sum a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm g (sum a b) -> Tm g (arr a c) -> Tm g (arr b c) -> Tm g c)
 -> (zero  : (g:_)-> Tm g nat)
 -> (suc   : (g:_)-> Tm g nat -> Tm g nat)
 -> (rec   : (g:_)->(a:_) -> Tm g nat -> Tm g (arr nat (arr a a)) -> Tm g a -> Tm g a)
 -> Tm g a

var : {g:_}->{a:_} -> Var g a -> Tm g a
var = \ x, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var _ _ x

lam : {g:_}->{a:_}->{b:_}-> Tm (snoc g a) b -> Tm g (arr a b)
lam = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam _ _ _ (t tm var lam app tt pair fst snd left right split zero suc rec)

app : {g:_}->{a:_}->{b:_} -> Tm g (arr a b) -> Tm g a -> Tm g b
app = \ t, u, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app _ _ _ (t tm var lam app tt pair fst snd left right split zero suc rec)
                (u tm var lam app tt pair fst snd left right split zero suc rec)

tt : {g:_} -> Tm g Main.top
tt = \ tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => tt _

pair : {g:_}->{a:_}->{b:_} -> Tm g a -> Tm g b -> Tm g (prod a b)
pair = \ t, u, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     pair _ _ _ (t tm var lam app tt pair fst snd left right split zero suc rec)
                 (u tm var lam app tt pair fst snd left right split zero suc rec)

fst : {g:_}->{a:_}->{b:_}-> Tm g (prod a b) -> Tm g a
fst = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     fst _ _ _ (t tm var lam app tt pair fst snd left right split zero suc rec)

snd : {g:_}->{a:_}->{b:_} -> Tm g (prod a b) -> Tm g b
snd = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     snd _ _ _ (t tm var lam app tt pair fst snd left right split zero suc rec)

left : {g:_}->{a:_}->{b:_} -> Tm g a -> Tm g (sum a b)
left = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     left _ _ _ (t tm var lam app tt pair fst snd left right split zero suc rec)

right : {g:_}->{a:_}->{b:_} -> Tm g b -> Tm g (sum a b)
right = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     right _ _ _ (t tm var lam app tt pair fst snd left right split zero suc rec)

split : {g:_}->{a:_}->{b:_}->{c:_} -> Tm g (sum a b) -> Tm g (arr a c) -> Tm g (arr b c) -> Tm g c
split = \ t, u, v, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     split _ _ _ _
          (t tm var lam app tt pair fst snd left right split zero suc rec)
          (u tm var lam app tt pair fst snd left right split zero suc rec)
          (v tm var lam app tt pair fst snd left right split zero suc rec)

zero : {g:_} -> Tm g Main.nat
zero = \ tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
  zero _

suc : {g:_} -> Tm g Main.nat -> Tm g Main.nat
suc = \ t, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
   suc _ (t tm var lam app tt pair fst snd left right split zero suc rec)

rec : {g:_}->{a:_} -> Tm g Main.nat -> Tm g (arr Main.nat (arr a a)) -> Tm g a -> Tm g a
rec = \ t, u, v, tm, var, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     rec _ _
       (t tm var lam app tt pair fst snd left right split zero suc rec)
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
 -> (vz  : (g:_)->(a:_) -> Var1 (snoc1 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var1 g a -> Var1 (snoc1 g b) a)
 -> Var1 g a

vz1 : {g:_}->{a:_} -> Var1 (snoc1 g a) a
vz1 = \ var, vz1, vs => vz1 _ _

vs1 : {g:_}->{b:_}->{a:_} -> Var1 g a -> Var1 (snoc1 g b) a
vs1 = \ x, var, vz1, vs1 => vs1 _ _ _ (x var vz1 vs1)

Tm1 : Con1 -> Ty1-> Type
Tm1 = \ g, a =>
    (Tm1    : Con1 -> Ty1-> Type)
 -> (var   : (g:_)->(a:_)-> Var1 g a -> Tm1 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm1 (snoc1 g a) b -> Tm1 g (arr1 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm1 g (arr1 a b) -> Tm1 g a -> Tm1 g b)
 -> (tt    : (g:_)-> Tm1 g top1)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm1 g a -> Tm1 g b -> Tm1 g (prod1 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm1 g (prod1 a b) -> Tm1 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm1 g (prod1 a b) -> Tm1 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm1 g a -> Tm1 g (sum1 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm1 g b -> Tm1 g (sum1 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm1 g (sum1 a b) -> Tm1 g (arr1 a c) -> Tm1 g (arr1 b c) -> Tm1 g c)
 -> (zero  : (g:_)-> Tm1 g nat1)
 -> (suc   : (g:_)-> Tm1 g nat1 -> Tm1 g nat1)
 -> (rec   : (g:_)->(a:_) -> Tm1 g nat1 -> Tm1 g (arr1 nat1 (arr1 a a)) -> Tm1 g a -> Tm1 g a)
 -> Tm1 g a

var1 : {g:_}->{a:_} -> Var1 g a -> Tm1 g a
var1 = \ x, tm, var1, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var1 _ _ x

lam1 : {g:_}->{a:_}->{b:_}-> Tm1 (snoc1 g a) b -> Tm1 g (arr1 a b)
lam1 = \ t, tm, var1, lam1, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam1 _ _ _ (t tm var1 lam1 app tt pair fst snd left right split zero suc rec)

app1 : {g:_}->{a:_}->{b:_} -> Tm1 g (arr1 a b) -> Tm1 g a -> Tm1 g b
app1 = \ t, u, tm, var1, lam1, app1, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app1 _ _ _ (t tm var1 lam1 app1 tt pair fst snd left right split zero suc rec)
                (u tm var1 lam1 app1 tt pair fst snd left right split zero suc rec)

tt1 : {g:_} -> Tm1 g Main.top1
tt1 = \ tm, var1, lam1, app1, tt1, pair, fst, snd, left, right, split, zero, suc, rec => tt1 _

pair1 : {g:_}->{a:_}->{b:_} -> Tm1 g a -> Tm1 g b -> Tm1 g (prod1 a b)
pair1 = \ t, u, tm, var1, lam1, app1, tt1, pair1, fst, snd, left, right, split, zero, suc, rec =>
     pair1 _ _ _ (t tm var1 lam1 app1 tt1 pair1 fst snd left right split zero suc rec)
                 (u tm var1 lam1 app1 tt1 pair1 fst snd left right split zero suc rec)

fst1 : {g:_}->{a:_}->{b:_}-> Tm1 g (prod1 a b) -> Tm1 g a
fst1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd, left, right, split, zero, suc, rec =>
     fst1 _ _ _ (t tm var1 lam1 app1 tt1 pair1 fst1 snd left right split zero suc rec)

snd1 : {g:_}->{a:_}->{b:_} -> Tm1 g (prod1 a b) -> Tm1 g b
snd1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left, right, split, zero, suc, rec =>
     snd1 _ _ _ (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left right split zero suc rec)

left1 : {g:_}->{a:_}->{b:_} -> Tm1 g a -> Tm1 g (sum1 a b)
left1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right, split, zero, suc, rec =>
     left1 _ _ _ (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right split zero suc rec)

right1 : {g:_}->{a:_}->{b:_} -> Tm1 g b -> Tm1 g (sum1 a b)
right1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split, zero, suc, rec =>
     right1 _ _ _ (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split zero suc rec)

split1 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm1 g (sum1 a b) -> Tm1 g (arr1 a c) -> Tm1 g (arr1 b c) -> Tm1 g c
split1 = \ t, u, v, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split1, zero, suc, rec =>
     split1 _ _ _ _
          (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero suc rec)
          (u tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero suc rec)
          (v tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero suc rec)

zero1 : {g:_} -> Tm1 g Main.nat1
zero1 = \ tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split1, zero1, suc, rec =>
  zero1 _

suc1 : {g:_} -> Tm1 g Main.nat1 -> Tm1 g Main.nat1
suc1 = \ t, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split1, zero1, suc1, rec =>
   suc1 _ (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero1 suc1 rec)

rec1 : {g:_}->{a:_} -> Tm1 g Main.nat1 -> Tm1 g (arr1 Main.nat1 (arr1 a a)) -> Tm1 g a -> Tm1 g a
rec1 = \ t, u, v, tm, var1, lam1, app1, tt1, pair1, fst1, snd1, left1, right1, split1, zero1, suc1, rec1 =>
     rec1 _ _
       (t tm var1 lam1 app1 tt1 pair1 fst1 snd1 left1 right1 split1 zero1 suc1 rec1)
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
 -> (vz  : (g:_)->(a:_) -> Var2 (snoc2 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var2 g a -> Var2 (snoc2 g b) a)
 -> Var2 g a

vz2 : {g:_}->{a:_} -> Var2 (snoc2 g a) a
vz2 = \ var, vz2, vs => vz2 _ _

vs2 : {g:_}->{b:_}->{a:_} -> Var2 g a -> Var2 (snoc2 g b) a
vs2 = \ x, var, vz2, vs2 => vs2 _ _ _ (x var vz2 vs2)

Tm2 : Con2 -> Ty2-> Type
Tm2 = \ g, a =>
    (Tm2    : Con2 -> Ty2-> Type)
 -> (var   : (g:_)->(a:_)-> Var2 g a -> Tm2 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm2 (snoc2 g a) b -> Tm2 g (arr2 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm2 g (arr2 a b) -> Tm2 g a -> Tm2 g b)
 -> (tt    : (g:_)-> Tm2 g top2)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm2 g a -> Tm2 g b -> Tm2 g (prod2 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm2 g (prod2 a b) -> Tm2 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm2 g (prod2 a b) -> Tm2 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm2 g a -> Tm2 g (sum2 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm2 g b -> Tm2 g (sum2 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm2 g (sum2 a b) -> Tm2 g (arr2 a c) -> Tm2 g (arr2 b c) -> Tm2 g c)
 -> (zero  : (g:_)-> Tm2 g nat2)
 -> (suc   : (g:_)-> Tm2 g nat2 -> Tm2 g nat2)
 -> (rec   : (g:_)->(a:_) -> Tm2 g nat2 -> Tm2 g (arr2 nat2 (arr2 a a)) -> Tm2 g a -> Tm2 g a)
 -> Tm2 g a

var2 : {g:_}->{a:_} -> Var2 g a -> Tm2 g a
var2 = \ x, tm, var2, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var2 _ _ x

lam2 : {g:_}->{a:_}->{b:_}-> Tm2 (snoc2 g a) b -> Tm2 g (arr2 a b)
lam2 = \ t, tm, var2, lam2, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam2 _ _ _ (t tm var2 lam2 app tt pair fst snd left right split zero suc rec)

app2 : {g:_}->{a:_}->{b:_} -> Tm2 g (arr2 a b) -> Tm2 g a -> Tm2 g b
app2 = \ t, u, tm, var2, lam2, app2, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app2 _ _ _ (t tm var2 lam2 app2 tt pair fst snd left right split zero suc rec)
                (u tm var2 lam2 app2 tt pair fst snd left right split zero suc rec)

tt2 : {g:_} -> Tm2 g Main.top2
tt2 = \ tm, var2, lam2, app2, tt2, pair, fst, snd, left, right, split, zero, suc, rec => tt2 _

pair2 : {g:_}->{a:_}->{b:_} -> Tm2 g a -> Tm2 g b -> Tm2 g (prod2 a b)
pair2 = \ t, u, tm, var2, lam2, app2, tt2, pair2, fst, snd, left, right, split, zero, suc, rec =>
     pair2 _ _ _ (t tm var2 lam2 app2 tt2 pair2 fst snd left right split zero suc rec)
                 (u tm var2 lam2 app2 tt2 pair2 fst snd left right split zero suc rec)

fst2 : {g:_}->{a:_}->{b:_}-> Tm2 g (prod2 a b) -> Tm2 g a
fst2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd, left, right, split, zero, suc, rec =>
     fst2 _ _ _ (t tm var2 lam2 app2 tt2 pair2 fst2 snd left right split zero suc rec)

snd2 : {g:_}->{a:_}->{b:_} -> Tm2 g (prod2 a b) -> Tm2 g b
snd2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left, right, split, zero, suc, rec =>
     snd2 _ _ _ (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left right split zero suc rec)

left2 : {g:_}->{a:_}->{b:_} -> Tm2 g a -> Tm2 g (sum2 a b)
left2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right, split, zero, suc, rec =>
     left2 _ _ _ (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right split zero suc rec)

right2 : {g:_}->{a:_}->{b:_} -> Tm2 g b -> Tm2 g (sum2 a b)
right2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split, zero, suc, rec =>
     right2 _ _ _ (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split zero suc rec)

split2 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm2 g (sum2 a b) -> Tm2 g (arr2 a c) -> Tm2 g (arr2 b c) -> Tm2 g c
split2 = \ t, u, v, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split2, zero, suc, rec =>
     split2 _ _ _ _
          (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero suc rec)
          (u tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero suc rec)
          (v tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero suc rec)

zero2 : {g:_} -> Tm2 g Main.nat2
zero2 = \ tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split2, zero2, suc, rec =>
  zero2 _

suc2 : {g:_} -> Tm2 g Main.nat2 -> Tm2 g Main.nat2
suc2 = \ t, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split2, zero2, suc2, rec =>
   suc2 _ (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero2 suc2 rec)

rec2 : {g:_}->{a:_} -> Tm2 g Main.nat2 -> Tm2 g (arr2 Main.nat2 (arr2 a a)) -> Tm2 g a -> Tm2 g a
rec2 = \ t, u, v, tm, var2, lam2, app2, tt2, pair2, fst2, snd2, left2, right2, split2, zero2, suc2, rec2 =>
     rec2 _ _
       (t tm var2 lam2 app2 tt2 pair2 fst2 snd2 left2 right2 split2 zero2 suc2 rec2)
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
 -> (vz  : (g:_)->(a:_) -> Var3 (snoc3 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var3 g a -> Var3 (snoc3 g b) a)
 -> Var3 g a

vz3 : {g:_}->{a:_} -> Var3 (snoc3 g a) a
vz3 = \ var, vz3, vs => vz3 _ _

vs3 : {g:_}->{b:_}->{a:_} -> Var3 g a -> Var3 (snoc3 g b) a
vs3 = \ x, var, vz3, vs3 => vs3 _ _ _ (x var vz3 vs3)

Tm3 : Con3 -> Ty3-> Type
Tm3 = \ g, a =>
    (Tm3    : Con3 -> Ty3-> Type)
 -> (var   : (g:_)->(a:_)-> Var3 g a -> Tm3 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm3 (snoc3 g a) b -> Tm3 g (arr3 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm3 g (arr3 a b) -> Tm3 g a -> Tm3 g b)
 -> (tt    : (g:_)-> Tm3 g top3)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm3 g a -> Tm3 g b -> Tm3 g (prod3 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm3 g (prod3 a b) -> Tm3 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm3 g (prod3 a b) -> Tm3 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm3 g a -> Tm3 g (sum3 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm3 g b -> Tm3 g (sum3 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm3 g (sum3 a b) -> Tm3 g (arr3 a c) -> Tm3 g (arr3 b c) -> Tm3 g c)
 -> (zero  : (g:_)-> Tm3 g nat3)
 -> (suc   : (g:_)-> Tm3 g nat3 -> Tm3 g nat3)
 -> (rec   : (g:_)->(a:_) -> Tm3 g nat3 -> Tm3 g (arr3 nat3 (arr3 a a)) -> Tm3 g a -> Tm3 g a)
 -> Tm3 g a

var3 : {g:_}->{a:_} -> Var3 g a -> Tm3 g a
var3 = \ x, tm, var3, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var3 _ _ x

lam3 : {g:_}->{a:_}->{b:_}-> Tm3 (snoc3 g a) b -> Tm3 g (arr3 a b)
lam3 = \ t, tm, var3, lam3, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam3 _ _ _ (t tm var3 lam3 app tt pair fst snd left right split zero suc rec)

app3 : {g:_}->{a:_}->{b:_} -> Tm3 g (arr3 a b) -> Tm3 g a -> Tm3 g b
app3 = \ t, u, tm, var3, lam3, app3, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app3 _ _ _ (t tm var3 lam3 app3 tt pair fst snd left right split zero suc rec)
                (u tm var3 lam3 app3 tt pair fst snd left right split zero suc rec)

tt3 : {g:_} -> Tm3 g Main.top3
tt3 = \ tm, var3, lam3, app3, tt3, pair, fst, snd, left, right, split, zero, suc, rec => tt3 _

pair3 : {g:_}->{a:_}->{b:_} -> Tm3 g a -> Tm3 g b -> Tm3 g (prod3 a b)
pair3 = \ t, u, tm, var3, lam3, app3, tt3, pair3, fst, snd, left, right, split, zero, suc, rec =>
     pair3 _ _ _ (t tm var3 lam3 app3 tt3 pair3 fst snd left right split zero suc rec)
                 (u tm var3 lam3 app3 tt3 pair3 fst snd left right split zero suc rec)

fst3 : {g:_}->{a:_}->{b:_}-> Tm3 g (prod3 a b) -> Tm3 g a
fst3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd, left, right, split, zero, suc, rec =>
     fst3 _ _ _ (t tm var3 lam3 app3 tt3 pair3 fst3 snd left right split zero suc rec)

snd3 : {g:_}->{a:_}->{b:_} -> Tm3 g (prod3 a b) -> Tm3 g b
snd3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left, right, split, zero, suc, rec =>
     snd3 _ _ _ (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left right split zero suc rec)

left3 : {g:_}->{a:_}->{b:_} -> Tm3 g a -> Tm3 g (sum3 a b)
left3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right, split, zero, suc, rec =>
     left3 _ _ _ (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right split zero suc rec)

right3 : {g:_}->{a:_}->{b:_} -> Tm3 g b -> Tm3 g (sum3 a b)
right3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split, zero, suc, rec =>
     right3 _ _ _ (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split zero suc rec)

split3 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm3 g (sum3 a b) -> Tm3 g (arr3 a c) -> Tm3 g (arr3 b c) -> Tm3 g c
split3 = \ t, u, v, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split3, zero, suc, rec =>
     split3 _ _ _ _
          (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero suc rec)
          (u tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero suc rec)
          (v tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero suc rec)

zero3 : {g:_} -> Tm3 g Main.nat3
zero3 = \ tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split3, zero3, suc, rec =>
  zero3 _

suc3 : {g:_} -> Tm3 g Main.nat3 -> Tm3 g Main.nat3
suc3 = \ t, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split3, zero3, suc3, rec =>
   suc3 _ (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero3 suc3 rec)

rec3 : {g:_}->{a:_} -> Tm3 g Main.nat3 -> Tm3 g (arr3 Main.nat3 (arr3 a a)) -> Tm3 g a -> Tm3 g a
rec3 = \ t, u, v, tm, var3, lam3, app3, tt3, pair3, fst3, snd3, left3, right3, split3, zero3, suc3, rec3 =>
     rec3 _ _
       (t tm var3 lam3 app3 tt3 pair3 fst3 snd3 left3 right3 split3 zero3 suc3 rec3)
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
 -> (vz  : (g:_)->(a:_) -> Var4 (snoc4 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var4 g a -> Var4 (snoc4 g b) a)
 -> Var4 g a

vz4 : {g:_}->{a:_} -> Var4 (snoc4 g a) a
vz4 = \ var, vz4, vs => vz4 _ _

vs4 : {g:_}->{b:_}->{a:_} -> Var4 g a -> Var4 (snoc4 g b) a
vs4 = \ x, var, vz4, vs4 => vs4 _ _ _ (x var vz4 vs4)

Tm4 : Con4 -> Ty4-> Type
Tm4 = \ g, a =>
    (Tm4    : Con4 -> Ty4-> Type)
 -> (var   : (g:_)->(a:_)-> Var4 g a -> Tm4 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm4 (snoc4 g a) b -> Tm4 g (arr4 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm4 g (arr4 a b) -> Tm4 g a -> Tm4 g b)
 -> (tt    : (g:_)-> Tm4 g top4)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm4 g a -> Tm4 g b -> Tm4 g (prod4 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm4 g (prod4 a b) -> Tm4 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm4 g (prod4 a b) -> Tm4 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm4 g a -> Tm4 g (sum4 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm4 g b -> Tm4 g (sum4 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm4 g (sum4 a b) -> Tm4 g (arr4 a c) -> Tm4 g (arr4 b c) -> Tm4 g c)
 -> (zero  : (g:_)-> Tm4 g nat4)
 -> (suc   : (g:_)-> Tm4 g nat4 -> Tm4 g nat4)
 -> (rec   : (g:_)->(a:_) -> Tm4 g nat4 -> Tm4 g (arr4 nat4 (arr4 a a)) -> Tm4 g a -> Tm4 g a)
 -> Tm4 g a

var4 : {g:_}->{a:_} -> Var4 g a -> Tm4 g a
var4 = \ x, tm, var4, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var4 _ _ x

lam4 : {g:_}->{a:_}->{b:_}-> Tm4 (snoc4 g a) b -> Tm4 g (arr4 a b)
lam4 = \ t, tm, var4, lam4, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam4 _ _ _ (t tm var4 lam4 app tt pair fst snd left right split zero suc rec)

app4 : {g:_}->{a:_}->{b:_} -> Tm4 g (arr4 a b) -> Tm4 g a -> Tm4 g b
app4 = \ t, u, tm, var4, lam4, app4, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app4 _ _ _ (t tm var4 lam4 app4 tt pair fst snd left right split zero suc rec)
                (u tm var4 lam4 app4 tt pair fst snd left right split zero suc rec)

tt4 : {g:_} -> Tm4 g Main.top4
tt4 = \ tm, var4, lam4, app4, tt4, pair, fst, snd, left, right, split, zero, suc, rec => tt4 _

pair4 : {g:_}->{a:_}->{b:_} -> Tm4 g a -> Tm4 g b -> Tm4 g (prod4 a b)
pair4 = \ t, u, tm, var4, lam4, app4, tt4, pair4, fst, snd, left, right, split, zero, suc, rec =>
     pair4 _ _ _ (t tm var4 lam4 app4 tt4 pair4 fst snd left right split zero suc rec)
                 (u tm var4 lam4 app4 tt4 pair4 fst snd left right split zero suc rec)

fst4 : {g:_}->{a:_}->{b:_}-> Tm4 g (prod4 a b) -> Tm4 g a
fst4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd, left, right, split, zero, suc, rec =>
     fst4 _ _ _ (t tm var4 lam4 app4 tt4 pair4 fst4 snd left right split zero suc rec)

snd4 : {g:_}->{a:_}->{b:_} -> Tm4 g (prod4 a b) -> Tm4 g b
snd4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left, right, split, zero, suc, rec =>
     snd4 _ _ _ (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left right split zero suc rec)

left4 : {g:_}->{a:_}->{b:_} -> Tm4 g a -> Tm4 g (sum4 a b)
left4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right, split, zero, suc, rec =>
     left4 _ _ _ (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right split zero suc rec)

right4 : {g:_}->{a:_}->{b:_} -> Tm4 g b -> Tm4 g (sum4 a b)
right4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split, zero, suc, rec =>
     right4 _ _ _ (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split zero suc rec)

split4 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm4 g (sum4 a b) -> Tm4 g (arr4 a c) -> Tm4 g (arr4 b c) -> Tm4 g c
split4 = \ t, u, v, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split4, zero, suc, rec =>
     split4 _ _ _ _
          (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero suc rec)
          (u tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero suc rec)
          (v tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero suc rec)

zero4 : {g:_} -> Tm4 g Main.nat4
zero4 = \ tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split4, zero4, suc, rec =>
  zero4 _

suc4 : {g:_} -> Tm4 g Main.nat4 -> Tm4 g Main.nat4
suc4 = \ t, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split4, zero4, suc4, rec =>
   suc4 _ (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero4 suc4 rec)

rec4 : {g:_}->{a:_} -> Tm4 g Main.nat4 -> Tm4 g (arr4 Main.nat4 (arr4 a a)) -> Tm4 g a -> Tm4 g a
rec4 = \ t, u, v, tm, var4, lam4, app4, tt4, pair4, fst4, snd4, left4, right4, split4, zero4, suc4, rec4 =>
     rec4 _ _
       (t tm var4 lam4 app4 tt4 pair4 fst4 snd4 left4 right4 split4 zero4 suc4 rec4)
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
 -> (vz  : (g:_)->(a:_) -> Var5 (snoc5 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var5 g a -> Var5 (snoc5 g b) a)
 -> Var5 g a

vz5 : {g:_}->{a:_} -> Var5 (snoc5 g a) a
vz5 = \ var, vz5, vs => vz5 _ _

vs5 : {g:_}->{b:_}->{a:_} -> Var5 g a -> Var5 (snoc5 g b) a
vs5 = \ x, var, vz5, vs5 => vs5 _ _ _ (x var vz5 vs5)

Tm5 : Con5 -> Ty5-> Type
Tm5 = \ g, a =>
    (Tm5    : Con5 -> Ty5-> Type)
 -> (var   : (g:_)->(a:_)-> Var5 g a -> Tm5 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm5 (snoc5 g a) b -> Tm5 g (arr5 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm5 g (arr5 a b) -> Tm5 g a -> Tm5 g b)
 -> (tt    : (g:_)-> Tm5 g top5)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm5 g a -> Tm5 g b -> Tm5 g (prod5 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm5 g (prod5 a b) -> Tm5 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm5 g (prod5 a b) -> Tm5 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm5 g a -> Tm5 g (sum5 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm5 g b -> Tm5 g (sum5 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm5 g (sum5 a b) -> Tm5 g (arr5 a c) -> Tm5 g (arr5 b c) -> Tm5 g c)
 -> (zero  : (g:_)-> Tm5 g nat5)
 -> (suc   : (g:_)-> Tm5 g nat5 -> Tm5 g nat5)
 -> (rec   : (g:_)->(a:_) -> Tm5 g nat5 -> Tm5 g (arr5 nat5 (arr5 a a)) -> Tm5 g a -> Tm5 g a)
 -> Tm5 g a

var5 : {g:_}->{a:_} -> Var5 g a -> Tm5 g a
var5 = \ x, tm, var5, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var5 _ _ x

lam5 : {g:_}->{a:_}->{b:_}-> Tm5 (snoc5 g a) b -> Tm5 g (arr5 a b)
lam5 = \ t, tm, var5, lam5, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam5 _ _ _ (t tm var5 lam5 app tt pair fst snd left right split zero suc rec)

app5 : {g:_}->{a:_}->{b:_} -> Tm5 g (arr5 a b) -> Tm5 g a -> Tm5 g b
app5 = \ t, u, tm, var5, lam5, app5, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app5 _ _ _ (t tm var5 lam5 app5 tt pair fst snd left right split zero suc rec)
                (u tm var5 lam5 app5 tt pair fst snd left right split zero suc rec)

tt5 : {g:_} -> Tm5 g Main.top5
tt5 = \ tm, var5, lam5, app5, tt5, pair, fst, snd, left, right, split, zero, suc, rec => tt5 _

pair5 : {g:_}->{a:_}->{b:_} -> Tm5 g a -> Tm5 g b -> Tm5 g (prod5 a b)
pair5 = \ t, u, tm, var5, lam5, app5, tt5, pair5, fst, snd, left, right, split, zero, suc, rec =>
     pair5 _ _ _ (t tm var5 lam5 app5 tt5 pair5 fst snd left right split zero suc rec)
                 (u tm var5 lam5 app5 tt5 pair5 fst snd left right split zero suc rec)

fst5 : {g:_}->{a:_}->{b:_}-> Tm5 g (prod5 a b) -> Tm5 g a
fst5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd, left, right, split, zero, suc, rec =>
     fst5 _ _ _ (t tm var5 lam5 app5 tt5 pair5 fst5 snd left right split zero suc rec)

snd5 : {g:_}->{a:_}->{b:_} -> Tm5 g (prod5 a b) -> Tm5 g b
snd5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left, right, split, zero, suc, rec =>
     snd5 _ _ _ (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left right split zero suc rec)

left5 : {g:_}->{a:_}->{b:_} -> Tm5 g a -> Tm5 g (sum5 a b)
left5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right, split, zero, suc, rec =>
     left5 _ _ _ (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right split zero suc rec)

right5 : {g:_}->{a:_}->{b:_} -> Tm5 g b -> Tm5 g (sum5 a b)
right5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split, zero, suc, rec =>
     right5 _ _ _ (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split zero suc rec)

split5 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm5 g (sum5 a b) -> Tm5 g (arr5 a c) -> Tm5 g (arr5 b c) -> Tm5 g c
split5 = \ t, u, v, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split5, zero, suc, rec =>
     split5 _ _ _ _
          (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero suc rec)
          (u tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero suc rec)
          (v tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero suc rec)

zero5 : {g:_} -> Tm5 g Main.nat5
zero5 = \ tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split5, zero5, suc, rec =>
  zero5 _

suc5 : {g:_} -> Tm5 g Main.nat5 -> Tm5 g Main.nat5
suc5 = \ t, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split5, zero5, suc5, rec =>
   suc5 _ (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero5 suc5 rec)

rec5 : {g:_}->{a:_} -> Tm5 g Main.nat5 -> Tm5 g (arr5 Main.nat5 (arr5 a a)) -> Tm5 g a -> Tm5 g a
rec5 = \ t, u, v, tm, var5, lam5, app5, tt5, pair5, fst5, snd5, left5, right5, split5, zero5, suc5, rec5 =>
     rec5 _ _
       (t tm var5 lam5 app5 tt5 pair5 fst5 snd5 left5 right5 split5 zero5 suc5 rec5)
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
 -> (vz  : (g:_)->(a:_) -> Var6 (snoc6 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var6 g a -> Var6 (snoc6 g b) a)
 -> Var6 g a

vz6 : {g:_}->{a:_} -> Var6 (snoc6 g a) a
vz6 = \ var, vz6, vs => vz6 _ _

vs6 : {g:_}->{b:_}->{a:_} -> Var6 g a -> Var6 (snoc6 g b) a
vs6 = \ x, var, vz6, vs6 => vs6 _ _ _ (x var vz6 vs6)

Tm6 : Con6 -> Ty6-> Type
Tm6 = \ g, a =>
    (Tm6    : Con6 -> Ty6-> Type)
 -> (var   : (g:_)->(a:_)-> Var6 g a -> Tm6 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm6 (snoc6 g a) b -> Tm6 g (arr6 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm6 g (arr6 a b) -> Tm6 g a -> Tm6 g b)
 -> (tt    : (g:_)-> Tm6 g top6)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm6 g a -> Tm6 g b -> Tm6 g (prod6 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm6 g (prod6 a b) -> Tm6 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm6 g (prod6 a b) -> Tm6 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm6 g a -> Tm6 g (sum6 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm6 g b -> Tm6 g (sum6 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm6 g (sum6 a b) -> Tm6 g (arr6 a c) -> Tm6 g (arr6 b c) -> Tm6 g c)
 -> (zero  : (g:_)-> Tm6 g nat6)
 -> (suc   : (g:_)-> Tm6 g nat6 -> Tm6 g nat6)
 -> (rec   : (g:_)->(a:_) -> Tm6 g nat6 -> Tm6 g (arr6 nat6 (arr6 a a)) -> Tm6 g a -> Tm6 g a)
 -> Tm6 g a

var6 : {g:_}->{a:_} -> Var6 g a -> Tm6 g a
var6 = \ x, tm, var6, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var6 _ _ x

lam6 : {g:_}->{a:_}->{b:_}-> Tm6 (snoc6 g a) b -> Tm6 g (arr6 a b)
lam6 = \ t, tm, var6, lam6, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam6 _ _ _ (t tm var6 lam6 app tt pair fst snd left right split zero suc rec)

app6 : {g:_}->{a:_}->{b:_} -> Tm6 g (arr6 a b) -> Tm6 g a -> Tm6 g b
app6 = \ t, u, tm, var6, lam6, app6, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app6 _ _ _ (t tm var6 lam6 app6 tt pair fst snd left right split zero suc rec)
                (u tm var6 lam6 app6 tt pair fst snd left right split zero suc rec)

tt6 : {g:_} -> Tm6 g Main.top6
tt6 = \ tm, var6, lam6, app6, tt6, pair, fst, snd, left, right, split, zero, suc, rec => tt6 _

pair6 : {g:_}->{a:_}->{b:_} -> Tm6 g a -> Tm6 g b -> Tm6 g (prod6 a b)
pair6 = \ t, u, tm, var6, lam6, app6, tt6, pair6, fst, snd, left, right, split, zero, suc, rec =>
     pair6 _ _ _ (t tm var6 lam6 app6 tt6 pair6 fst snd left right split zero suc rec)
                 (u tm var6 lam6 app6 tt6 pair6 fst snd left right split zero suc rec)

fst6 : {g:_}->{a:_}->{b:_}-> Tm6 g (prod6 a b) -> Tm6 g a
fst6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd, left, right, split, zero, suc, rec =>
     fst6 _ _ _ (t tm var6 lam6 app6 tt6 pair6 fst6 snd left right split zero suc rec)

snd6 : {g:_}->{a:_}->{b:_} -> Tm6 g (prod6 a b) -> Tm6 g b
snd6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left, right, split, zero, suc, rec =>
     snd6 _ _ _ (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left right split zero suc rec)

left6 : {g:_}->{a:_}->{b:_} -> Tm6 g a -> Tm6 g (sum6 a b)
left6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right, split, zero, suc, rec =>
     left6 _ _ _ (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right split zero suc rec)

right6 : {g:_}->{a:_}->{b:_} -> Tm6 g b -> Tm6 g (sum6 a b)
right6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split, zero, suc, rec =>
     right6 _ _ _ (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split zero suc rec)

split6 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm6 g (sum6 a b) -> Tm6 g (arr6 a c) -> Tm6 g (arr6 b c) -> Tm6 g c
split6 = \ t, u, v, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split6, zero, suc, rec =>
     split6 _ _ _ _
          (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero suc rec)
          (u tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero suc rec)
          (v tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero suc rec)

zero6 : {g:_} -> Tm6 g Main.nat6
zero6 = \ tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split6, zero6, suc, rec =>
  zero6 _

suc6 : {g:_} -> Tm6 g Main.nat6 -> Tm6 g Main.nat6
suc6 = \ t, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split6, zero6, suc6, rec =>
   suc6 _ (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero6 suc6 rec)

rec6 : {g:_}->{a:_} -> Tm6 g Main.nat6 -> Tm6 g (arr6 Main.nat6 (arr6 a a)) -> Tm6 g a -> Tm6 g a
rec6 = \ t, u, v, tm, var6, lam6, app6, tt6, pair6, fst6, snd6, left6, right6, split6, zero6, suc6, rec6 =>
     rec6 _ _
       (t tm var6 lam6 app6 tt6 pair6 fst6 snd6 left6 right6 split6 zero6 suc6 rec6)
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
 -> (vz  : (g:_)->(a:_) -> Var7 (snoc7 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var7 g a -> Var7 (snoc7 g b) a)
 -> Var7 g a

vz7 : {g:_}->{a:_} -> Var7 (snoc7 g a) a
vz7 = \ var, vz7, vs => vz7 _ _

vs7 : {g:_}->{b:_}->{a:_} -> Var7 g a -> Var7 (snoc7 g b) a
vs7 = \ x, var, vz7, vs7 => vs7 _ _ _ (x var vz7 vs7)

Tm7 : Con7 -> Ty7-> Type
Tm7 = \ g, a =>
    (Tm7    : Con7 -> Ty7-> Type)
 -> (var   : (g:_)->(a:_)-> Var7 g a -> Tm7 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm7 (snoc7 g a) b -> Tm7 g (arr7 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm7 g (arr7 a b) -> Tm7 g a -> Tm7 g b)
 -> (tt    : (g:_)-> Tm7 g top7)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm7 g a -> Tm7 g b -> Tm7 g (prod7 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm7 g (prod7 a b) -> Tm7 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm7 g (prod7 a b) -> Tm7 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm7 g a -> Tm7 g (sum7 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm7 g b -> Tm7 g (sum7 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm7 g (sum7 a b) -> Tm7 g (arr7 a c) -> Tm7 g (arr7 b c) -> Tm7 g c)
 -> (zero  : (g:_)-> Tm7 g nat7)
 -> (suc   : (g:_)-> Tm7 g nat7 -> Tm7 g nat7)
 -> (rec   : (g:_)->(a:_) -> Tm7 g nat7 -> Tm7 g (arr7 nat7 (arr7 a a)) -> Tm7 g a -> Tm7 g a)
 -> Tm7 g a

var7 : {g:_}->{a:_} -> Var7 g a -> Tm7 g a
var7 = \ x, tm, var7, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var7 _ _ x

lam7 : {g:_}->{a:_}->{b:_}-> Tm7 (snoc7 g a) b -> Tm7 g (arr7 a b)
lam7 = \ t, tm, var7, lam7, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam7 _ _ _ (t tm var7 lam7 app tt pair fst snd left right split zero suc rec)

app7 : {g:_}->{a:_}->{b:_} -> Tm7 g (arr7 a b) -> Tm7 g a -> Tm7 g b
app7 = \ t, u, tm, var7, lam7, app7, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app7 _ _ _ (t tm var7 lam7 app7 tt pair fst snd left right split zero suc rec)
                (u tm var7 lam7 app7 tt pair fst snd left right split zero suc rec)

tt7 : {g:_} -> Tm7 g Main.top7
tt7 = \ tm, var7, lam7, app7, tt7, pair, fst, snd, left, right, split, zero, suc, rec => tt7 _

pair7 : {g:_}->{a:_}->{b:_} -> Tm7 g a -> Tm7 g b -> Tm7 g (prod7 a b)
pair7 = \ t, u, tm, var7, lam7, app7, tt7, pair7, fst, snd, left, right, split, zero, suc, rec =>
     pair7 _ _ _ (t tm var7 lam7 app7 tt7 pair7 fst snd left right split zero suc rec)
                 (u tm var7 lam7 app7 tt7 pair7 fst snd left right split zero suc rec)

fst7 : {g:_}->{a:_}->{b:_}-> Tm7 g (prod7 a b) -> Tm7 g a
fst7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd, left, right, split, zero, suc, rec =>
     fst7 _ _ _ (t tm var7 lam7 app7 tt7 pair7 fst7 snd left right split zero suc rec)

snd7 : {g:_}->{a:_}->{b:_} -> Tm7 g (prod7 a b) -> Tm7 g b
snd7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left, right, split, zero, suc, rec =>
     snd7 _ _ _ (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left right split zero suc rec)

left7 : {g:_}->{a:_}->{b:_} -> Tm7 g a -> Tm7 g (sum7 a b)
left7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right, split, zero, suc, rec =>
     left7 _ _ _ (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right split zero suc rec)

right7 : {g:_}->{a:_}->{b:_} -> Tm7 g b -> Tm7 g (sum7 a b)
right7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split, zero, suc, rec =>
     right7 _ _ _ (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split zero suc rec)

split7 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm7 g (sum7 a b) -> Tm7 g (arr7 a c) -> Tm7 g (arr7 b c) -> Tm7 g c
split7 = \ t, u, v, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split7, zero, suc, rec =>
     split7 _ _ _ _
          (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero suc rec)
          (u tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero suc rec)
          (v tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero suc rec)

zero7 : {g:_} -> Tm7 g Main.nat7
zero7 = \ tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split7, zero7, suc, rec =>
  zero7 _

suc7 : {g:_} -> Tm7 g Main.nat7 -> Tm7 g Main.nat7
suc7 = \ t, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split7, zero7, suc7, rec =>
   suc7 _ (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero7 suc7 rec)

rec7 : {g:_}->{a:_} -> Tm7 g Main.nat7 -> Tm7 g (arr7 Main.nat7 (arr7 a a)) -> Tm7 g a -> Tm7 g a
rec7 = \ t, u, v, tm, var7, lam7, app7, tt7, pair7, fst7, snd7, left7, right7, split7, zero7, suc7, rec7 =>
     rec7 _ _
       (t tm var7 lam7 app7 tt7 pair7 fst7 snd7 left7 right7 split7 zero7 suc7 rec7)
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
 -> (vz  : (g:_)->(a:_) -> Var8 (snoc8 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var8 g a -> Var8 (snoc8 g b) a)
 -> Var8 g a

vz8 : {g:_}->{a:_} -> Var8 (snoc8 g a) a
vz8 = \ var, vz8, vs => vz8 _ _

vs8 : {g:_}->{b:_}->{a:_} -> Var8 g a -> Var8 (snoc8 g b) a
vs8 = \ x, var, vz8, vs8 => vs8 _ _ _ (x var vz8 vs8)

Tm8 : Con8 -> Ty8-> Type
Tm8 = \ g, a =>
    (Tm8    : Con8 -> Ty8-> Type)
 -> (var   : (g:_)->(a:_)-> Var8 g a -> Tm8 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm8 (snoc8 g a) b -> Tm8 g (arr8 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm8 g (arr8 a b) -> Tm8 g a -> Tm8 g b)
 -> (tt    : (g:_)-> Tm8 g top8)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm8 g a -> Tm8 g b -> Tm8 g (prod8 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm8 g (prod8 a b) -> Tm8 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm8 g (prod8 a b) -> Tm8 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm8 g a -> Tm8 g (sum8 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm8 g b -> Tm8 g (sum8 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm8 g (sum8 a b) -> Tm8 g (arr8 a c) -> Tm8 g (arr8 b c) -> Tm8 g c)
 -> (zero  : (g:_)-> Tm8 g nat8)
 -> (suc   : (g:_)-> Tm8 g nat8 -> Tm8 g nat8)
 -> (rec   : (g:_)->(a:_) -> Tm8 g nat8 -> Tm8 g (arr8 nat8 (arr8 a a)) -> Tm8 g a -> Tm8 g a)
 -> Tm8 g a

var8 : {g:_}->{a:_} -> Var8 g a -> Tm8 g a
var8 = \ x, tm, var8, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var8 _ _ x

lam8 : {g:_}->{a:_}->{b:_}-> Tm8 (snoc8 g a) b -> Tm8 g (arr8 a b)
lam8 = \ t, tm, var8, lam8, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam8 _ _ _ (t tm var8 lam8 app tt pair fst snd left right split zero suc rec)

app8 : {g:_}->{a:_}->{b:_} -> Tm8 g (arr8 a b) -> Tm8 g a -> Tm8 g b
app8 = \ t, u, tm, var8, lam8, app8, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app8 _ _ _ (t tm var8 lam8 app8 tt pair fst snd left right split zero suc rec)
                (u tm var8 lam8 app8 tt pair fst snd left right split zero suc rec)

tt8 : {g:_} -> Tm8 g Main.top8
tt8 = \ tm, var8, lam8, app8, tt8, pair, fst, snd, left, right, split, zero, suc, rec => tt8 _

pair8 : {g:_}->{a:_}->{b:_} -> Tm8 g a -> Tm8 g b -> Tm8 g (prod8 a b)
pair8 = \ t, u, tm, var8, lam8, app8, tt8, pair8, fst, snd, left, right, split, zero, suc, rec =>
     pair8 _ _ _ (t tm var8 lam8 app8 tt8 pair8 fst snd left right split zero suc rec)
                 (u tm var8 lam8 app8 tt8 pair8 fst snd left right split zero suc rec)

fst8 : {g:_}->{a:_}->{b:_}-> Tm8 g (prod8 a b) -> Tm8 g a
fst8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd, left, right, split, zero, suc, rec =>
     fst8 _ _ _ (t tm var8 lam8 app8 tt8 pair8 fst8 snd left right split zero suc rec)

snd8 : {g:_}->{a:_}->{b:_} -> Tm8 g (prod8 a b) -> Tm8 g b
snd8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left, right, split, zero, suc, rec =>
     snd8 _ _ _ (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left right split zero suc rec)

left8 : {g:_}->{a:_}->{b:_} -> Tm8 g a -> Tm8 g (sum8 a b)
left8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right, split, zero, suc, rec =>
     left8 _ _ _ (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right split zero suc rec)

right8 : {g:_}->{a:_}->{b:_} -> Tm8 g b -> Tm8 g (sum8 a b)
right8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split, zero, suc, rec =>
     right8 _ _ _ (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split zero suc rec)

split8 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm8 g (sum8 a b) -> Tm8 g (arr8 a c) -> Tm8 g (arr8 b c) -> Tm8 g c
split8 = \ t, u, v, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split8, zero, suc, rec =>
     split8 _ _ _ _
          (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero suc rec)
          (u tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero suc rec)
          (v tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero suc rec)

zero8 : {g:_} -> Tm8 g Main.nat8
zero8 = \ tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split8, zero8, suc, rec =>
  zero8 _

suc8 : {g:_} -> Tm8 g Main.nat8 -> Tm8 g Main.nat8
suc8 = \ t, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split8, zero8, suc8, rec =>
   suc8 _ (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero8 suc8 rec)

rec8 : {g:_}->{a:_} -> Tm8 g Main.nat8 -> Tm8 g (arr8 Main.nat8 (arr8 a a)) -> Tm8 g a -> Tm8 g a
rec8 = \ t, u, v, tm, var8, lam8, app8, tt8, pair8, fst8, snd8, left8, right8, split8, zero8, suc8, rec8 =>
     rec8 _ _
       (t tm var8 lam8 app8 tt8 pair8 fst8 snd8 left8 right8 split8 zero8 suc8 rec8)
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
 -> (vz  : (g:_)->(a:_) -> Var9 (snoc9 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var9 g a -> Var9 (snoc9 g b) a)
 -> Var9 g a

vz9 : {g:_}->{a:_} -> Var9 (snoc9 g a) a
vz9 = \ var, vz9, vs => vz9 _ _

vs9 : {g:_}->{b:_}->{a:_} -> Var9 g a -> Var9 (snoc9 g b) a
vs9 = \ x, var, vz9, vs9 => vs9 _ _ _ (x var vz9 vs9)

Tm9 : Con9 -> Ty9-> Type
Tm9 = \ g, a =>
    (Tm9    : Con9 -> Ty9-> Type)
 -> (var   : (g:_)->(a:_)-> Var9 g a -> Tm9 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm9 (snoc9 g a) b -> Tm9 g (arr9 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm9 g (arr9 a b) -> Tm9 g a -> Tm9 g b)
 -> (tt    : (g:_)-> Tm9 g top9)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm9 g a -> Tm9 g b -> Tm9 g (prod9 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm9 g (prod9 a b) -> Tm9 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm9 g (prod9 a b) -> Tm9 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm9 g a -> Tm9 g (sum9 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm9 g b -> Tm9 g (sum9 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm9 g (sum9 a b) -> Tm9 g (arr9 a c) -> Tm9 g (arr9 b c) -> Tm9 g c)
 -> (zero  : (g:_)-> Tm9 g nat9)
 -> (suc   : (g:_)-> Tm9 g nat9 -> Tm9 g nat9)
 -> (rec   : (g:_)->(a:_) -> Tm9 g nat9 -> Tm9 g (arr9 nat9 (arr9 a a)) -> Tm9 g a -> Tm9 g a)
 -> Tm9 g a

var9 : {g:_}->{a:_} -> Var9 g a -> Tm9 g a
var9 = \ x, tm, var9, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var9 _ _ x

lam9 : {g:_}->{a:_}->{b:_}-> Tm9 (snoc9 g a) b -> Tm9 g (arr9 a b)
lam9 = \ t, tm, var9, lam9, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam9 _ _ _ (t tm var9 lam9 app tt pair fst snd left right split zero suc rec)

app9 : {g:_}->{a:_}->{b:_} -> Tm9 g (arr9 a b) -> Tm9 g a -> Tm9 g b
app9 = \ t, u, tm, var9, lam9, app9, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app9 _ _ _ (t tm var9 lam9 app9 tt pair fst snd left right split zero suc rec)
                (u tm var9 lam9 app9 tt pair fst snd left right split zero suc rec)

tt9 : {g:_} -> Tm9 g Main.top9
tt9 = \ tm, var9, lam9, app9, tt9, pair, fst, snd, left, right, split, zero, suc, rec => tt9 _

pair9 : {g:_}->{a:_}->{b:_} -> Tm9 g a -> Tm9 g b -> Tm9 g (prod9 a b)
pair9 = \ t, u, tm, var9, lam9, app9, tt9, pair9, fst, snd, left, right, split, zero, suc, rec =>
     pair9 _ _ _ (t tm var9 lam9 app9 tt9 pair9 fst snd left right split zero suc rec)
                 (u tm var9 lam9 app9 tt9 pair9 fst snd left right split zero suc rec)

fst9 : {g:_}->{a:_}->{b:_}-> Tm9 g (prod9 a b) -> Tm9 g a
fst9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd, left, right, split, zero, suc, rec =>
     fst9 _ _ _ (t tm var9 lam9 app9 tt9 pair9 fst9 snd left right split zero suc rec)

snd9 : {g:_}->{a:_}->{b:_} -> Tm9 g (prod9 a b) -> Tm9 g b
snd9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left, right, split, zero, suc, rec =>
     snd9 _ _ _ (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left right split zero suc rec)

left9 : {g:_}->{a:_}->{b:_} -> Tm9 g a -> Tm9 g (sum9 a b)
left9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right, split, zero, suc, rec =>
     left9 _ _ _ (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right split zero suc rec)

right9 : {g:_}->{a:_}->{b:_} -> Tm9 g b -> Tm9 g (sum9 a b)
right9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split, zero, suc, rec =>
     right9 _ _ _ (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split zero suc rec)

split9 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm9 g (sum9 a b) -> Tm9 g (arr9 a c) -> Tm9 g (arr9 b c) -> Tm9 g c
split9 = \ t, u, v, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split9, zero, suc, rec =>
     split9 _ _ _ _
          (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero suc rec)
          (u tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero suc rec)
          (v tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero suc rec)

zero9 : {g:_} -> Tm9 g Main.nat9
zero9 = \ tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split9, zero9, suc, rec =>
  zero9 _

suc9 : {g:_} -> Tm9 g Main.nat9 -> Tm9 g Main.nat9
suc9 = \ t, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split9, zero9, suc9, rec =>
   suc9 _ (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero9 suc9 rec)

rec9 : {g:_}->{a:_} -> Tm9 g Main.nat9 -> Tm9 g (arr9 Main.nat9 (arr9 a a)) -> Tm9 g a -> Tm9 g a
rec9 = \ t, u, v, tm, var9, lam9, app9, tt9, pair9, fst9, snd9, left9, right9, split9, zero9, suc9, rec9 =>
     rec9 _ _
       (t tm var9 lam9 app9 tt9 pair9 fst9 snd9 left9 right9 split9 zero9 suc9 rec9)
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
 -> (vz  : (g:_)->(a:_) -> Var10 (snoc10 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var10 g a -> Var10 (snoc10 g b) a)
 -> Var10 g a

vz10 : {g:_}->{a:_} -> Var10 (snoc10 g a) a
vz10 = \ var, vz10, vs => vz10 _ _

vs10 : {g:_}->{b:_}->{a:_} -> Var10 g a -> Var10 (snoc10 g b) a
vs10 = \ x, var, vz10, vs10 => vs10 _ _ _ (x var vz10 vs10)

Tm10 : Con10 -> Ty10-> Type
Tm10 = \ g, a =>
    (Tm10    : Con10 -> Ty10-> Type)
 -> (var   : (g:_)->(a:_)-> Var10 g a -> Tm10 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm10 (snoc10 g a) b -> Tm10 g (arr10 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm10 g (arr10 a b) -> Tm10 g a -> Tm10 g b)
 -> (tt    : (g:_)-> Tm10 g top10)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm10 g a -> Tm10 g b -> Tm10 g (prod10 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm10 g (prod10 a b) -> Tm10 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm10 g (prod10 a b) -> Tm10 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm10 g a -> Tm10 g (sum10 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm10 g b -> Tm10 g (sum10 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm10 g (sum10 a b) -> Tm10 g (arr10 a c) -> Tm10 g (arr10 b c) -> Tm10 g c)
 -> (zero  : (g:_)-> Tm10 g nat10)
 -> (suc   : (g:_)-> Tm10 g nat10 -> Tm10 g nat10)
 -> (rec   : (g:_)->(a:_) -> Tm10 g nat10 -> Tm10 g (arr10 nat10 (arr10 a a)) -> Tm10 g a -> Tm10 g a)
 -> Tm10 g a

var10 : {g:_}->{a:_} -> Var10 g a -> Tm10 g a
var10 = \ x, tm, var10, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var10 _ _ x

lam10 : {g:_}->{a:_}->{b:_}-> Tm10 (snoc10 g a) b -> Tm10 g (arr10 a b)
lam10 = \ t, tm, var10, lam10, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam10 _ _ _ (t tm var10 lam10 app tt pair fst snd left right split zero suc rec)

app10 : {g:_}->{a:_}->{b:_} -> Tm10 g (arr10 a b) -> Tm10 g a -> Tm10 g b
app10 = \ t, u, tm, var10, lam10, app10, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app10 _ _ _ (t tm var10 lam10 app10 tt pair fst snd left right split zero suc rec)
                (u tm var10 lam10 app10 tt pair fst snd left right split zero suc rec)

tt10 : {g:_} -> Tm10 g Main.top10
tt10 = \ tm, var10, lam10, app10, tt10, pair, fst, snd, left, right, split, zero, suc, rec => tt10 _

pair10 : {g:_}->{a:_}->{b:_} -> Tm10 g a -> Tm10 g b -> Tm10 g (prod10 a b)
pair10 = \ t, u, tm, var10, lam10, app10, tt10, pair10, fst, snd, left, right, split, zero, suc, rec =>
     pair10 _ _ _ (t tm var10 lam10 app10 tt10 pair10 fst snd left right split zero suc rec)
                 (u tm var10 lam10 app10 tt10 pair10 fst snd left right split zero suc rec)

fst10 : {g:_}->{a:_}->{b:_}-> Tm10 g (prod10 a b) -> Tm10 g a
fst10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd, left, right, split, zero, suc, rec =>
     fst10 _ _ _ (t tm var10 lam10 app10 tt10 pair10 fst10 snd left right split zero suc rec)

snd10 : {g:_}->{a:_}->{b:_} -> Tm10 g (prod10 a b) -> Tm10 g b
snd10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left, right, split, zero, suc, rec =>
     snd10 _ _ _ (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left right split zero suc rec)

left10 : {g:_}->{a:_}->{b:_} -> Tm10 g a -> Tm10 g (sum10 a b)
left10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right, split, zero, suc, rec =>
     left10 _ _ _ (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right split zero suc rec)

right10 : {g:_}->{a:_}->{b:_} -> Tm10 g b -> Tm10 g (sum10 a b)
right10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split, zero, suc, rec =>
     right10 _ _ _ (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split zero suc rec)

split10 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm10 g (sum10 a b) -> Tm10 g (arr10 a c) -> Tm10 g (arr10 b c) -> Tm10 g c
split10 = \ t, u, v, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split10, zero, suc, rec =>
     split10 _ _ _ _
          (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero suc rec)
          (u tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero suc rec)
          (v tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero suc rec)

zero10 : {g:_} -> Tm10 g Main.nat10
zero10 = \ tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split10, zero10, suc, rec =>
  zero10 _

suc10 : {g:_} -> Tm10 g Main.nat10 -> Tm10 g Main.nat10
suc10 = \ t, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split10, zero10, suc10, rec =>
   suc10 _ (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero10 suc10 rec)

rec10 : {g:_}->{a:_} -> Tm10 g Main.nat10 -> Tm10 g (arr10 Main.nat10 (arr10 a a)) -> Tm10 g a -> Tm10 g a
rec10 = \ t, u, v, tm, var10, lam10, app10, tt10, pair10, fst10, snd10, left10, right10, split10, zero10, suc10, rec10 =>
     rec10 _ _
       (t tm var10 lam10 app10 tt10 pair10 fst10 snd10 left10 right10 split10 zero10 suc10 rec10)
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
 -> (vz  : (g:_)->(a:_) -> Var11 (snoc11 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var11 g a -> Var11 (snoc11 g b) a)
 -> Var11 g a

vz11 : {g:_}->{a:_} -> Var11 (snoc11 g a) a
vz11 = \ var, vz11, vs => vz11 _ _

vs11 : {g:_}->{b:_}->{a:_} -> Var11 g a -> Var11 (snoc11 g b) a
vs11 = \ x, var, vz11, vs11 => vs11 _ _ _ (x var vz11 vs11)

Tm11 : Con11 -> Ty11-> Type
Tm11 = \ g, a =>
    (Tm11    : Con11 -> Ty11-> Type)
 -> (var   : (g:_)->(a:_)-> Var11 g a -> Tm11 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm11 (snoc11 g a) b -> Tm11 g (arr11 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm11 g (arr11 a b) -> Tm11 g a -> Tm11 g b)
 -> (tt    : (g:_)-> Tm11 g top11)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm11 g a -> Tm11 g b -> Tm11 g (prod11 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm11 g (prod11 a b) -> Tm11 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm11 g (prod11 a b) -> Tm11 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm11 g a -> Tm11 g (sum11 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm11 g b -> Tm11 g (sum11 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm11 g (sum11 a b) -> Tm11 g (arr11 a c) -> Tm11 g (arr11 b c) -> Tm11 g c)
 -> (zero  : (g:_)-> Tm11 g nat11)
 -> (suc   : (g:_)-> Tm11 g nat11 -> Tm11 g nat11)
 -> (rec   : (g:_)->(a:_) -> Tm11 g nat11 -> Tm11 g (arr11 nat11 (arr11 a a)) -> Tm11 g a -> Tm11 g a)
 -> Tm11 g a

var11 : {g:_}->{a:_} -> Var11 g a -> Tm11 g a
var11 = \ x, tm, var11, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var11 _ _ x

lam11 : {g:_}->{a:_}->{b:_}-> Tm11 (snoc11 g a) b -> Tm11 g (arr11 a b)
lam11 = \ t, tm, var11, lam11, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam11 _ _ _ (t tm var11 lam11 app tt pair fst snd left right split zero suc rec)

app11 : {g:_}->{a:_}->{b:_} -> Tm11 g (arr11 a b) -> Tm11 g a -> Tm11 g b
app11 = \ t, u, tm, var11, lam11, app11, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app11 _ _ _ (t tm var11 lam11 app11 tt pair fst snd left right split zero suc rec)
                (u tm var11 lam11 app11 tt pair fst snd left right split zero suc rec)

tt11 : {g:_} -> Tm11 g Main.top11
tt11 = \ tm, var11, lam11, app11, tt11, pair, fst, snd, left, right, split, zero, suc, rec => tt11 _

pair11 : {g:_}->{a:_}->{b:_} -> Tm11 g a -> Tm11 g b -> Tm11 g (prod11 a b)
pair11 = \ t, u, tm, var11, lam11, app11, tt11, pair11, fst, snd, left, right, split, zero, suc, rec =>
     pair11 _ _ _ (t tm var11 lam11 app11 tt11 pair11 fst snd left right split zero suc rec)
                 (u tm var11 lam11 app11 tt11 pair11 fst snd left right split zero suc rec)

fst11 : {g:_}->{a:_}->{b:_}-> Tm11 g (prod11 a b) -> Tm11 g a
fst11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd, left, right, split, zero, suc, rec =>
     fst11 _ _ _ (t tm var11 lam11 app11 tt11 pair11 fst11 snd left right split zero suc rec)

snd11 : {g:_}->{a:_}->{b:_} -> Tm11 g (prod11 a b) -> Tm11 g b
snd11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left, right, split, zero, suc, rec =>
     snd11 _ _ _ (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left right split zero suc rec)

left11 : {g:_}->{a:_}->{b:_} -> Tm11 g a -> Tm11 g (sum11 a b)
left11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right, split, zero, suc, rec =>
     left11 _ _ _ (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right split zero suc rec)

right11 : {g:_}->{a:_}->{b:_} -> Tm11 g b -> Tm11 g (sum11 a b)
right11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split, zero, suc, rec =>
     right11 _ _ _ (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split zero suc rec)

split11 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm11 g (sum11 a b) -> Tm11 g (arr11 a c) -> Tm11 g (arr11 b c) -> Tm11 g c
split11 = \ t, u, v, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split11, zero, suc, rec =>
     split11 _ _ _ _
          (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero suc rec)
          (u tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero suc rec)
          (v tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero suc rec)

zero11 : {g:_} -> Tm11 g Main.nat11
zero11 = \ tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split11, zero11, suc, rec =>
  zero11 _

suc11 : {g:_} -> Tm11 g Main.nat11 -> Tm11 g Main.nat11
suc11 = \ t, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split11, zero11, suc11, rec =>
   suc11 _ (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero11 suc11 rec)

rec11 : {g:_}->{a:_} -> Tm11 g Main.nat11 -> Tm11 g (arr11 Main.nat11 (arr11 a a)) -> Tm11 g a -> Tm11 g a
rec11 = \ t, u, v, tm, var11, lam11, app11, tt11, pair11, fst11, snd11, left11, right11, split11, zero11, suc11, rec11 =>
     rec11 _ _
       (t tm var11 lam11 app11 tt11 pair11 fst11 snd11 left11 right11 split11 zero11 suc11 rec11)
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
 -> (vz  : (g:_)->(a:_) -> Var12 (snoc12 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var12 g a -> Var12 (snoc12 g b) a)
 -> Var12 g a

vz12 : {g:_}->{a:_} -> Var12 (snoc12 g a) a
vz12 = \ var, vz12, vs => vz12 _ _

vs12 : {g:_}->{b:_}->{a:_} -> Var12 g a -> Var12 (snoc12 g b) a
vs12 = \ x, var, vz12, vs12 => vs12 _ _ _ (x var vz12 vs12)

Tm12 : Con12 -> Ty12-> Type
Tm12 = \ g, a =>
    (Tm12    : Con12 -> Ty12-> Type)
 -> (var   : (g:_)->(a:_)-> Var12 g a -> Tm12 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm12 (snoc12 g a) b -> Tm12 g (arr12 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm12 g (arr12 a b) -> Tm12 g a -> Tm12 g b)
 -> (tt    : (g:_)-> Tm12 g top12)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm12 g a -> Tm12 g b -> Tm12 g (prod12 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm12 g (prod12 a b) -> Tm12 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm12 g (prod12 a b) -> Tm12 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm12 g a -> Tm12 g (sum12 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm12 g b -> Tm12 g (sum12 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm12 g (sum12 a b) -> Tm12 g (arr12 a c) -> Tm12 g (arr12 b c) -> Tm12 g c)
 -> (zero  : (g:_)-> Tm12 g nat12)
 -> (suc   : (g:_)-> Tm12 g nat12 -> Tm12 g nat12)
 -> (rec   : (g:_)->(a:_) -> Tm12 g nat12 -> Tm12 g (arr12 nat12 (arr12 a a)) -> Tm12 g a -> Tm12 g a)
 -> Tm12 g a

var12 : {g:_}->{a:_} -> Var12 g a -> Tm12 g a
var12 = \ x, tm, var12, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var12 _ _ x

lam12 : {g:_}->{a:_}->{b:_}-> Tm12 (snoc12 g a) b -> Tm12 g (arr12 a b)
lam12 = \ t, tm, var12, lam12, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam12 _ _ _ (t tm var12 lam12 app tt pair fst snd left right split zero suc rec)

app12 : {g:_}->{a:_}->{b:_} -> Tm12 g (arr12 a b) -> Tm12 g a -> Tm12 g b
app12 = \ t, u, tm, var12, lam12, app12, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app12 _ _ _ (t tm var12 lam12 app12 tt pair fst snd left right split zero suc rec)
                (u tm var12 lam12 app12 tt pair fst snd left right split zero suc rec)

tt12 : {g:_} -> Tm12 g Main.top12
tt12 = \ tm, var12, lam12, app12, tt12, pair, fst, snd, left, right, split, zero, suc, rec => tt12 _

pair12 : {g:_}->{a:_}->{b:_} -> Tm12 g a -> Tm12 g b -> Tm12 g (prod12 a b)
pair12 = \ t, u, tm, var12, lam12, app12, tt12, pair12, fst, snd, left, right, split, zero, suc, rec =>
     pair12 _ _ _ (t tm var12 lam12 app12 tt12 pair12 fst snd left right split zero suc rec)
                 (u tm var12 lam12 app12 tt12 pair12 fst snd left right split zero suc rec)

fst12 : {g:_}->{a:_}->{b:_}-> Tm12 g (prod12 a b) -> Tm12 g a
fst12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd, left, right, split, zero, suc, rec =>
     fst12 _ _ _ (t tm var12 lam12 app12 tt12 pair12 fst12 snd left right split zero suc rec)

snd12 : {g:_}->{a:_}->{b:_} -> Tm12 g (prod12 a b) -> Tm12 g b
snd12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left, right, split, zero, suc, rec =>
     snd12 _ _ _ (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left right split zero suc rec)

left12 : {g:_}->{a:_}->{b:_} -> Tm12 g a -> Tm12 g (sum12 a b)
left12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right, split, zero, suc, rec =>
     left12 _ _ _ (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right split zero suc rec)

right12 : {g:_}->{a:_}->{b:_} -> Tm12 g b -> Tm12 g (sum12 a b)
right12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split, zero, suc, rec =>
     right12 _ _ _ (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split zero suc rec)

split12 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm12 g (sum12 a b) -> Tm12 g (arr12 a c) -> Tm12 g (arr12 b c) -> Tm12 g c
split12 = \ t, u, v, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split12, zero, suc, rec =>
     split12 _ _ _ _
          (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero suc rec)
          (u tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero suc rec)
          (v tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero suc rec)

zero12 : {g:_} -> Tm12 g Main.nat12
zero12 = \ tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split12, zero12, suc, rec =>
  zero12 _

suc12 : {g:_} -> Tm12 g Main.nat12 -> Tm12 g Main.nat12
suc12 = \ t, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split12, zero12, suc12, rec =>
   suc12 _ (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero12 suc12 rec)

rec12 : {g:_}->{a:_} -> Tm12 g Main.nat12 -> Tm12 g (arr12 Main.nat12 (arr12 a a)) -> Tm12 g a -> Tm12 g a
rec12 = \ t, u, v, tm, var12, lam12, app12, tt12, pair12, fst12, snd12, left12, right12, split12, zero12, suc12, rec12 =>
     rec12 _ _
       (t tm var12 lam12 app12 tt12 pair12 fst12 snd12 left12 right12 split12 zero12 suc12 rec12)
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
 -> (vz  : (g:_)->(a:_) -> Var13 (snoc13 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var13 g a -> Var13 (snoc13 g b) a)
 -> Var13 g a

vz13 : {g:_}->{a:_} -> Var13 (snoc13 g a) a
vz13 = \ var, vz13, vs => vz13 _ _

vs13 : {g:_}->{b:_}->{a:_} -> Var13 g a -> Var13 (snoc13 g b) a
vs13 = \ x, var, vz13, vs13 => vs13 _ _ _ (x var vz13 vs13)

Tm13 : Con13 -> Ty13-> Type
Tm13 = \ g, a =>
    (Tm13    : Con13 -> Ty13-> Type)
 -> (var   : (g:_)->(a:_)-> Var13 g a -> Tm13 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm13 (snoc13 g a) b -> Tm13 g (arr13 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm13 g (arr13 a b) -> Tm13 g a -> Tm13 g b)
 -> (tt    : (g:_)-> Tm13 g top13)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm13 g a -> Tm13 g b -> Tm13 g (prod13 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm13 g (prod13 a b) -> Tm13 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm13 g (prod13 a b) -> Tm13 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm13 g a -> Tm13 g (sum13 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm13 g b -> Tm13 g (sum13 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm13 g (sum13 a b) -> Tm13 g (arr13 a c) -> Tm13 g (arr13 b c) -> Tm13 g c)
 -> (zero  : (g:_)-> Tm13 g nat13)
 -> (suc   : (g:_)-> Tm13 g nat13 -> Tm13 g nat13)
 -> (rec   : (g:_)->(a:_) -> Tm13 g nat13 -> Tm13 g (arr13 nat13 (arr13 a a)) -> Tm13 g a -> Tm13 g a)
 -> Tm13 g a

var13 : {g:_}->{a:_} -> Var13 g a -> Tm13 g a
var13 = \ x, tm, var13, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var13 _ _ x

lam13 : {g:_}->{a:_}->{b:_}-> Tm13 (snoc13 g a) b -> Tm13 g (arr13 a b)
lam13 = \ t, tm, var13, lam13, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam13 _ _ _ (t tm var13 lam13 app tt pair fst snd left right split zero suc rec)

app13 : {g:_}->{a:_}->{b:_} -> Tm13 g (arr13 a b) -> Tm13 g a -> Tm13 g b
app13 = \ t, u, tm, var13, lam13, app13, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app13 _ _ _ (t tm var13 lam13 app13 tt pair fst snd left right split zero suc rec)
                (u tm var13 lam13 app13 tt pair fst snd left right split zero suc rec)

tt13 : {g:_} -> Tm13 g Main.top13
tt13 = \ tm, var13, lam13, app13, tt13, pair, fst, snd, left, right, split, zero, suc, rec => tt13 _

pair13 : {g:_}->{a:_}->{b:_} -> Tm13 g a -> Tm13 g b -> Tm13 g (prod13 a b)
pair13 = \ t, u, tm, var13, lam13, app13, tt13, pair13, fst, snd, left, right, split, zero, suc, rec =>
     pair13 _ _ _ (t tm var13 lam13 app13 tt13 pair13 fst snd left right split zero suc rec)
                 (u tm var13 lam13 app13 tt13 pair13 fst snd left right split zero suc rec)

fst13 : {g:_}->{a:_}->{b:_}-> Tm13 g (prod13 a b) -> Tm13 g a
fst13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd, left, right, split, zero, suc, rec =>
     fst13 _ _ _ (t tm var13 lam13 app13 tt13 pair13 fst13 snd left right split zero suc rec)

snd13 : {g:_}->{a:_}->{b:_} -> Tm13 g (prod13 a b) -> Tm13 g b
snd13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left, right, split, zero, suc, rec =>
     snd13 _ _ _ (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left right split zero suc rec)

left13 : {g:_}->{a:_}->{b:_} -> Tm13 g a -> Tm13 g (sum13 a b)
left13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right, split, zero, suc, rec =>
     left13 _ _ _ (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right split zero suc rec)

right13 : {g:_}->{a:_}->{b:_} -> Tm13 g b -> Tm13 g (sum13 a b)
right13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split, zero, suc, rec =>
     right13 _ _ _ (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split zero suc rec)

split13 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm13 g (sum13 a b) -> Tm13 g (arr13 a c) -> Tm13 g (arr13 b c) -> Tm13 g c
split13 = \ t, u, v, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split13, zero, suc, rec =>
     split13 _ _ _ _
          (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero suc rec)
          (u tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero suc rec)
          (v tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero suc rec)

zero13 : {g:_} -> Tm13 g Main.nat13
zero13 = \ tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split13, zero13, suc, rec =>
  zero13 _

suc13 : {g:_} -> Tm13 g Main.nat13 -> Tm13 g Main.nat13
suc13 = \ t, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split13, zero13, suc13, rec =>
   suc13 _ (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero13 suc13 rec)

rec13 : {g:_}->{a:_} -> Tm13 g Main.nat13 -> Tm13 g (arr13 Main.nat13 (arr13 a a)) -> Tm13 g a -> Tm13 g a
rec13 = \ t, u, v, tm, var13, lam13, app13, tt13, pair13, fst13, snd13, left13, right13, split13, zero13, suc13, rec13 =>
     rec13 _ _
       (t tm var13 lam13 app13 tt13 pair13 fst13 snd13 left13 right13 split13 zero13 suc13 rec13)
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
 -> (vz  : (g:_)->(a:_) -> Var14 (snoc14 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var14 g a -> Var14 (snoc14 g b) a)
 -> Var14 g a

vz14 : {g:_}->{a:_} -> Var14 (snoc14 g a) a
vz14 = \ var, vz14, vs => vz14 _ _

vs14 : {g:_}->{b:_}->{a:_} -> Var14 g a -> Var14 (snoc14 g b) a
vs14 = \ x, var, vz14, vs14 => vs14 _ _ _ (x var vz14 vs14)

Tm14 : Con14 -> Ty14-> Type
Tm14 = \ g, a =>
    (Tm14    : Con14 -> Ty14-> Type)
 -> (var   : (g:_)->(a:_)-> Var14 g a -> Tm14 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm14 (snoc14 g a) b -> Tm14 g (arr14 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm14 g (arr14 a b) -> Tm14 g a -> Tm14 g b)
 -> (tt    : (g:_)-> Tm14 g top14)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm14 g a -> Tm14 g b -> Tm14 g (prod14 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm14 g (prod14 a b) -> Tm14 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm14 g (prod14 a b) -> Tm14 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm14 g a -> Tm14 g (sum14 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm14 g b -> Tm14 g (sum14 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm14 g (sum14 a b) -> Tm14 g (arr14 a c) -> Tm14 g (arr14 b c) -> Tm14 g c)
 -> (zero  : (g:_)-> Tm14 g nat14)
 -> (suc   : (g:_)-> Tm14 g nat14 -> Tm14 g nat14)
 -> (rec   : (g:_)->(a:_) -> Tm14 g nat14 -> Tm14 g (arr14 nat14 (arr14 a a)) -> Tm14 g a -> Tm14 g a)
 -> Tm14 g a

var14 : {g:_}->{a:_} -> Var14 g a -> Tm14 g a
var14 = \ x, tm, var14, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var14 _ _ x

lam14 : {g:_}->{a:_}->{b:_}-> Tm14 (snoc14 g a) b -> Tm14 g (arr14 a b)
lam14 = \ t, tm, var14, lam14, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam14 _ _ _ (t tm var14 lam14 app tt pair fst snd left right split zero suc rec)

app14 : {g:_}->{a:_}->{b:_} -> Tm14 g (arr14 a b) -> Tm14 g a -> Tm14 g b
app14 = \ t, u, tm, var14, lam14, app14, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app14 _ _ _ (t tm var14 lam14 app14 tt pair fst snd left right split zero suc rec)
                (u tm var14 lam14 app14 tt pair fst snd left right split zero suc rec)

tt14 : {g:_} -> Tm14 g Main.top14
tt14 = \ tm, var14, lam14, app14, tt14, pair, fst, snd, left, right, split, zero, suc, rec => tt14 _

pair14 : {g:_}->{a:_}->{b:_} -> Tm14 g a -> Tm14 g b -> Tm14 g (prod14 a b)
pair14 = \ t, u, tm, var14, lam14, app14, tt14, pair14, fst, snd, left, right, split, zero, suc, rec =>
     pair14 _ _ _ (t tm var14 lam14 app14 tt14 pair14 fst snd left right split zero suc rec)
                 (u tm var14 lam14 app14 tt14 pair14 fst snd left right split zero suc rec)

fst14 : {g:_}->{a:_}->{b:_}-> Tm14 g (prod14 a b) -> Tm14 g a
fst14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd, left, right, split, zero, suc, rec =>
     fst14 _ _ _ (t tm var14 lam14 app14 tt14 pair14 fst14 snd left right split zero suc rec)

snd14 : {g:_}->{a:_}->{b:_} -> Tm14 g (prod14 a b) -> Tm14 g b
snd14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left, right, split, zero, suc, rec =>
     snd14 _ _ _ (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left right split zero suc rec)

left14 : {g:_}->{a:_}->{b:_} -> Tm14 g a -> Tm14 g (sum14 a b)
left14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right, split, zero, suc, rec =>
     left14 _ _ _ (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right split zero suc rec)

right14 : {g:_}->{a:_}->{b:_} -> Tm14 g b -> Tm14 g (sum14 a b)
right14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split, zero, suc, rec =>
     right14 _ _ _ (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split zero suc rec)

split14 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm14 g (sum14 a b) -> Tm14 g (arr14 a c) -> Tm14 g (arr14 b c) -> Tm14 g c
split14 = \ t, u, v, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split14, zero, suc, rec =>
     split14 _ _ _ _
          (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero suc rec)
          (u tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero suc rec)
          (v tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero suc rec)

zero14 : {g:_} -> Tm14 g Main.nat14
zero14 = \ tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split14, zero14, suc, rec =>
  zero14 _

suc14 : {g:_} -> Tm14 g Main.nat14 -> Tm14 g Main.nat14
suc14 = \ t, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split14, zero14, suc14, rec =>
   suc14 _ (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero14 suc14 rec)

rec14 : {g:_}->{a:_} -> Tm14 g Main.nat14 -> Tm14 g (arr14 Main.nat14 (arr14 a a)) -> Tm14 g a -> Tm14 g a
rec14 = \ t, u, v, tm, var14, lam14, app14, tt14, pair14, fst14, snd14, left14, right14, split14, zero14, suc14, rec14 =>
     rec14 _ _
       (t tm var14 lam14 app14 tt14 pair14 fst14 snd14 left14 right14 split14 zero14 suc14 rec14)
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
 -> (vz  : (g:_)->(a:_) -> Var15 (snoc15 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var15 g a -> Var15 (snoc15 g b) a)
 -> Var15 g a

vz15 : {g:_}->{a:_} -> Var15 (snoc15 g a) a
vz15 = \ var, vz15, vs => vz15 _ _

vs15 : {g:_}->{b:_}->{a:_} -> Var15 g a -> Var15 (snoc15 g b) a
vs15 = \ x, var, vz15, vs15 => vs15 _ _ _ (x var vz15 vs15)

Tm15 : Con15 -> Ty15-> Type
Tm15 = \ g, a =>
    (Tm15    : Con15 -> Ty15-> Type)
 -> (var   : (g:_)->(a:_)-> Var15 g a -> Tm15 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm15 (snoc15 g a) b -> Tm15 g (arr15 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm15 g (arr15 a b) -> Tm15 g a -> Tm15 g b)
 -> (tt    : (g:_)-> Tm15 g top15)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm15 g a -> Tm15 g b -> Tm15 g (prod15 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm15 g (prod15 a b) -> Tm15 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm15 g (prod15 a b) -> Tm15 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm15 g a -> Tm15 g (sum15 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm15 g b -> Tm15 g (sum15 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm15 g (sum15 a b) -> Tm15 g (arr15 a c) -> Tm15 g (arr15 b c) -> Tm15 g c)
 -> (zero  : (g:_)-> Tm15 g nat15)
 -> (suc   : (g:_)-> Tm15 g nat15 -> Tm15 g nat15)
 -> (rec   : (g:_)->(a:_) -> Tm15 g nat15 -> Tm15 g (arr15 nat15 (arr15 a a)) -> Tm15 g a -> Tm15 g a)
 -> Tm15 g a

var15 : {g:_}->{a:_} -> Var15 g a -> Tm15 g a
var15 = \ x, tm, var15, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var15 _ _ x

lam15 : {g:_}->{a:_}->{b:_}-> Tm15 (snoc15 g a) b -> Tm15 g (arr15 a b)
lam15 = \ t, tm, var15, lam15, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam15 _ _ _ (t tm var15 lam15 app tt pair fst snd left right split zero suc rec)

app15 : {g:_}->{a:_}->{b:_} -> Tm15 g (arr15 a b) -> Tm15 g a -> Tm15 g b
app15 = \ t, u, tm, var15, lam15, app15, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app15 _ _ _ (t tm var15 lam15 app15 tt pair fst snd left right split zero suc rec)
                (u tm var15 lam15 app15 tt pair fst snd left right split zero suc rec)

tt15 : {g:_} -> Tm15 g Main.top15
tt15 = \ tm, var15, lam15, app15, tt15, pair, fst, snd, left, right, split, zero, suc, rec => tt15 _

pair15 : {g:_}->{a:_}->{b:_} -> Tm15 g a -> Tm15 g b -> Tm15 g (prod15 a b)
pair15 = \ t, u, tm, var15, lam15, app15, tt15, pair15, fst, snd, left, right, split, zero, suc, rec =>
     pair15 _ _ _ (t tm var15 lam15 app15 tt15 pair15 fst snd left right split zero suc rec)
                 (u tm var15 lam15 app15 tt15 pair15 fst snd left right split zero suc rec)

fst15 : {g:_}->{a:_}->{b:_}-> Tm15 g (prod15 a b) -> Tm15 g a
fst15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd, left, right, split, zero, suc, rec =>
     fst15 _ _ _ (t tm var15 lam15 app15 tt15 pair15 fst15 snd left right split zero suc rec)

snd15 : {g:_}->{a:_}->{b:_} -> Tm15 g (prod15 a b) -> Tm15 g b
snd15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left, right, split, zero, suc, rec =>
     snd15 _ _ _ (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left right split zero suc rec)

left15 : {g:_}->{a:_}->{b:_} -> Tm15 g a -> Tm15 g (sum15 a b)
left15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right, split, zero, suc, rec =>
     left15 _ _ _ (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right split zero suc rec)

right15 : {g:_}->{a:_}->{b:_} -> Tm15 g b -> Tm15 g (sum15 a b)
right15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split, zero, suc, rec =>
     right15 _ _ _ (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split zero suc rec)

split15 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm15 g (sum15 a b) -> Tm15 g (arr15 a c) -> Tm15 g (arr15 b c) -> Tm15 g c
split15 = \ t, u, v, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split15, zero, suc, rec =>
     split15 _ _ _ _
          (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero suc rec)
          (u tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero suc rec)
          (v tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero suc rec)

zero15 : {g:_} -> Tm15 g Main.nat15
zero15 = \ tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split15, zero15, suc, rec =>
  zero15 _

suc15 : {g:_} -> Tm15 g Main.nat15 -> Tm15 g Main.nat15
suc15 = \ t, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split15, zero15, suc15, rec =>
   suc15 _ (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero15 suc15 rec)

rec15 : {g:_}->{a:_} -> Tm15 g Main.nat15 -> Tm15 g (arr15 Main.nat15 (arr15 a a)) -> Tm15 g a -> Tm15 g a
rec15 = \ t, u, v, tm, var15, lam15, app15, tt15, pair15, fst15, snd15, left15, right15, split15, zero15, suc15, rec15 =>
     rec15 _ _
       (t tm var15 lam15 app15 tt15 pair15 fst15 snd15 left15 right15 split15 zero15 suc15 rec15)
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
 -> (vz  : (g:_)->(a:_) -> Var16 (snoc16 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var16 g a -> Var16 (snoc16 g b) a)
 -> Var16 g a

vz16 : {g:_}->{a:_} -> Var16 (snoc16 g a) a
vz16 = \ var, vz16, vs => vz16 _ _

vs16 : {g:_}->{b:_}->{a:_} -> Var16 g a -> Var16 (snoc16 g b) a
vs16 = \ x, var, vz16, vs16 => vs16 _ _ _ (x var vz16 vs16)

Tm16 : Con16 -> Ty16-> Type
Tm16 = \ g, a =>
    (Tm16    : Con16 -> Ty16-> Type)
 -> (var   : (g:_)->(a:_)-> Var16 g a -> Tm16 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm16 (snoc16 g a) b -> Tm16 g (arr16 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm16 g (arr16 a b) -> Tm16 g a -> Tm16 g b)
 -> (tt    : (g:_)-> Tm16 g top16)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm16 g a -> Tm16 g b -> Tm16 g (prod16 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm16 g (prod16 a b) -> Tm16 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm16 g (prod16 a b) -> Tm16 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm16 g a -> Tm16 g (sum16 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm16 g b -> Tm16 g (sum16 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm16 g (sum16 a b) -> Tm16 g (arr16 a c) -> Tm16 g (arr16 b c) -> Tm16 g c)
 -> (zero  : (g:_)-> Tm16 g nat16)
 -> (suc   : (g:_)-> Tm16 g nat16 -> Tm16 g nat16)
 -> (rec   : (g:_)->(a:_) -> Tm16 g nat16 -> Tm16 g (arr16 nat16 (arr16 a a)) -> Tm16 g a -> Tm16 g a)
 -> Tm16 g a

var16 : {g:_}->{a:_} -> Var16 g a -> Tm16 g a
var16 = \ x, tm, var16, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var16 _ _ x

lam16 : {g:_}->{a:_}->{b:_}-> Tm16 (snoc16 g a) b -> Tm16 g (arr16 a b)
lam16 = \ t, tm, var16, lam16, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam16 _ _ _ (t tm var16 lam16 app tt pair fst snd left right split zero suc rec)

app16 : {g:_}->{a:_}->{b:_} -> Tm16 g (arr16 a b) -> Tm16 g a -> Tm16 g b
app16 = \ t, u, tm, var16, lam16, app16, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app16 _ _ _ (t tm var16 lam16 app16 tt pair fst snd left right split zero suc rec)
                (u tm var16 lam16 app16 tt pair fst snd left right split zero suc rec)

tt16 : {g:_} -> Tm16 g Main.top16
tt16 = \ tm, var16, lam16, app16, tt16, pair, fst, snd, left, right, split, zero, suc, rec => tt16 _

pair16 : {g:_}->{a:_}->{b:_} -> Tm16 g a -> Tm16 g b -> Tm16 g (prod16 a b)
pair16 = \ t, u, tm, var16, lam16, app16, tt16, pair16, fst, snd, left, right, split, zero, suc, rec =>
     pair16 _ _ _ (t tm var16 lam16 app16 tt16 pair16 fst snd left right split zero suc rec)
                 (u tm var16 lam16 app16 tt16 pair16 fst snd left right split zero suc rec)

fst16 : {g:_}->{a:_}->{b:_}-> Tm16 g (prod16 a b) -> Tm16 g a
fst16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd, left, right, split, zero, suc, rec =>
     fst16 _ _ _ (t tm var16 lam16 app16 tt16 pair16 fst16 snd left right split zero suc rec)

snd16 : {g:_}->{a:_}->{b:_} -> Tm16 g (prod16 a b) -> Tm16 g b
snd16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left, right, split, zero, suc, rec =>
     snd16 _ _ _ (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left right split zero suc rec)

left16 : {g:_}->{a:_}->{b:_} -> Tm16 g a -> Tm16 g (sum16 a b)
left16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right, split, zero, suc, rec =>
     left16 _ _ _ (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right split zero suc rec)

right16 : {g:_}->{a:_}->{b:_} -> Tm16 g b -> Tm16 g (sum16 a b)
right16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split, zero, suc, rec =>
     right16 _ _ _ (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split zero suc rec)

split16 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm16 g (sum16 a b) -> Tm16 g (arr16 a c) -> Tm16 g (arr16 b c) -> Tm16 g c
split16 = \ t, u, v, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split16, zero, suc, rec =>
     split16 _ _ _ _
          (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero suc rec)
          (u tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero suc rec)
          (v tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero suc rec)

zero16 : {g:_} -> Tm16 g Main.nat16
zero16 = \ tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split16, zero16, suc, rec =>
  zero16 _

suc16 : {g:_} -> Tm16 g Main.nat16 -> Tm16 g Main.nat16
suc16 = \ t, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split16, zero16, suc16, rec =>
   suc16 _ (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero16 suc16 rec)

rec16 : {g:_}->{a:_} -> Tm16 g Main.nat16 -> Tm16 g (arr16 Main.nat16 (arr16 a a)) -> Tm16 g a -> Tm16 g a
rec16 = \ t, u, v, tm, var16, lam16, app16, tt16, pair16, fst16, snd16, left16, right16, split16, zero16, suc16, rec16 =>
     rec16 _ _
       (t tm var16 lam16 app16 tt16 pair16 fst16 snd16 left16 right16 split16 zero16 suc16 rec16)
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
 -> (vz  : (g:_)->(a:_) -> Var17 (snoc17 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var17 g a -> Var17 (snoc17 g b) a)
 -> Var17 g a

vz17 : {g:_}->{a:_} -> Var17 (snoc17 g a) a
vz17 = \ var, vz17, vs => vz17 _ _

vs17 : {g:_}->{b:_}->{a:_} -> Var17 g a -> Var17 (snoc17 g b) a
vs17 = \ x, var, vz17, vs17 => vs17 _ _ _ (x var vz17 vs17)

Tm17 : Con17 -> Ty17-> Type
Tm17 = \ g, a =>
    (Tm17    : Con17 -> Ty17-> Type)
 -> (var   : (g:_)->(a:_)-> Var17 g a -> Tm17 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm17 (snoc17 g a) b -> Tm17 g (arr17 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm17 g (arr17 a b) -> Tm17 g a -> Tm17 g b)
 -> (tt    : (g:_)-> Tm17 g top17)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm17 g a -> Tm17 g b -> Tm17 g (prod17 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm17 g (prod17 a b) -> Tm17 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm17 g (prod17 a b) -> Tm17 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm17 g a -> Tm17 g (sum17 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm17 g b -> Tm17 g (sum17 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm17 g (sum17 a b) -> Tm17 g (arr17 a c) -> Tm17 g (arr17 b c) -> Tm17 g c)
 -> (zero  : (g:_)-> Tm17 g nat17)
 -> (suc   : (g:_)-> Tm17 g nat17 -> Tm17 g nat17)
 -> (rec   : (g:_)->(a:_) -> Tm17 g nat17 -> Tm17 g (arr17 nat17 (arr17 a a)) -> Tm17 g a -> Tm17 g a)
 -> Tm17 g a

var17 : {g:_}->{a:_} -> Var17 g a -> Tm17 g a
var17 = \ x, tm, var17, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var17 _ _ x

lam17 : {g:_}->{a:_}->{b:_}-> Tm17 (snoc17 g a) b -> Tm17 g (arr17 a b)
lam17 = \ t, tm, var17, lam17, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam17 _ _ _ (t tm var17 lam17 app tt pair fst snd left right split zero suc rec)

app17 : {g:_}->{a:_}->{b:_} -> Tm17 g (arr17 a b) -> Tm17 g a -> Tm17 g b
app17 = \ t, u, tm, var17, lam17, app17, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app17 _ _ _ (t tm var17 lam17 app17 tt pair fst snd left right split zero suc rec)
                (u tm var17 lam17 app17 tt pair fst snd left right split zero suc rec)

tt17 : {g:_} -> Tm17 g Main.top17
tt17 = \ tm, var17, lam17, app17, tt17, pair, fst, snd, left, right, split, zero, suc, rec => tt17 _

pair17 : {g:_}->{a:_}->{b:_} -> Tm17 g a -> Tm17 g b -> Tm17 g (prod17 a b)
pair17 = \ t, u, tm, var17, lam17, app17, tt17, pair17, fst, snd, left, right, split, zero, suc, rec =>
     pair17 _ _ _ (t tm var17 lam17 app17 tt17 pair17 fst snd left right split zero suc rec)
                 (u tm var17 lam17 app17 tt17 pair17 fst snd left right split zero suc rec)

fst17 : {g:_}->{a:_}->{b:_}-> Tm17 g (prod17 a b) -> Tm17 g a
fst17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd, left, right, split, zero, suc, rec =>
     fst17 _ _ _ (t tm var17 lam17 app17 tt17 pair17 fst17 snd left right split zero suc rec)

snd17 : {g:_}->{a:_}->{b:_} -> Tm17 g (prod17 a b) -> Tm17 g b
snd17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left, right, split, zero, suc, rec =>
     snd17 _ _ _ (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left right split zero suc rec)

left17 : {g:_}->{a:_}->{b:_} -> Tm17 g a -> Tm17 g (sum17 a b)
left17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right, split, zero, suc, rec =>
     left17 _ _ _ (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right split zero suc rec)

right17 : {g:_}->{a:_}->{b:_} -> Tm17 g b -> Tm17 g (sum17 a b)
right17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split, zero, suc, rec =>
     right17 _ _ _ (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split zero suc rec)

split17 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm17 g (sum17 a b) -> Tm17 g (arr17 a c) -> Tm17 g (arr17 b c) -> Tm17 g c
split17 = \ t, u, v, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split17, zero, suc, rec =>
     split17 _ _ _ _
          (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero suc rec)
          (u tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero suc rec)
          (v tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero suc rec)

zero17 : {g:_} -> Tm17 g Main.nat17
zero17 = \ tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split17, zero17, suc, rec =>
  zero17 _

suc17 : {g:_} -> Tm17 g Main.nat17 -> Tm17 g Main.nat17
suc17 = \ t, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split17, zero17, suc17, rec =>
   suc17 _ (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero17 suc17 rec)

rec17 : {g:_}->{a:_} -> Tm17 g Main.nat17 -> Tm17 g (arr17 Main.nat17 (arr17 a a)) -> Tm17 g a -> Tm17 g a
rec17 = \ t, u, v, tm, var17, lam17, app17, tt17, pair17, fst17, snd17, left17, right17, split17, zero17, suc17, rec17 =>
     rec17 _ _
       (t tm var17 lam17 app17 tt17 pair17 fst17 snd17 left17 right17 split17 zero17 suc17 rec17)
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
 -> (vz  : (g:_)->(a:_) -> Var18 (snoc18 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var18 g a -> Var18 (snoc18 g b) a)
 -> Var18 g a

vz18 : {g:_}->{a:_} -> Var18 (snoc18 g a) a
vz18 = \ var, vz18, vs => vz18 _ _

vs18 : {g:_}->{b:_}->{a:_} -> Var18 g a -> Var18 (snoc18 g b) a
vs18 = \ x, var, vz18, vs18 => vs18 _ _ _ (x var vz18 vs18)

Tm18 : Con18 -> Ty18-> Type
Tm18 = \ g, a =>
    (Tm18    : Con18 -> Ty18-> Type)
 -> (var   : (g:_)->(a:_)-> Var18 g a -> Tm18 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm18 (snoc18 g a) b -> Tm18 g (arr18 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm18 g (arr18 a b) -> Tm18 g a -> Tm18 g b)
 -> (tt    : (g:_)-> Tm18 g top18)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm18 g a -> Tm18 g b -> Tm18 g (prod18 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm18 g (prod18 a b) -> Tm18 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm18 g (prod18 a b) -> Tm18 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm18 g a -> Tm18 g (sum18 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm18 g b -> Tm18 g (sum18 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm18 g (sum18 a b) -> Tm18 g (arr18 a c) -> Tm18 g (arr18 b c) -> Tm18 g c)
 -> (zero  : (g:_)-> Tm18 g nat18)
 -> (suc   : (g:_)-> Tm18 g nat18 -> Tm18 g nat18)
 -> (rec   : (g:_)->(a:_) -> Tm18 g nat18 -> Tm18 g (arr18 nat18 (arr18 a a)) -> Tm18 g a -> Tm18 g a)
 -> Tm18 g a

var18 : {g:_}->{a:_} -> Var18 g a -> Tm18 g a
var18 = \ x, tm, var18, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var18 _ _ x

lam18 : {g:_}->{a:_}->{b:_}-> Tm18 (snoc18 g a) b -> Tm18 g (arr18 a b)
lam18 = \ t, tm, var18, lam18, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam18 _ _ _ (t tm var18 lam18 app tt pair fst snd left right split zero suc rec)

app18 : {g:_}->{a:_}->{b:_} -> Tm18 g (arr18 a b) -> Tm18 g a -> Tm18 g b
app18 = \ t, u, tm, var18, lam18, app18, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app18 _ _ _ (t tm var18 lam18 app18 tt pair fst snd left right split zero suc rec)
                (u tm var18 lam18 app18 tt pair fst snd left right split zero suc rec)

tt18 : {g:_} -> Tm18 g Main.top18
tt18 = \ tm, var18, lam18, app18, tt18, pair, fst, snd, left, right, split, zero, suc, rec => tt18 _

pair18 : {g:_}->{a:_}->{b:_} -> Tm18 g a -> Tm18 g b -> Tm18 g (prod18 a b)
pair18 = \ t, u, tm, var18, lam18, app18, tt18, pair18, fst, snd, left, right, split, zero, suc, rec =>
     pair18 _ _ _ (t tm var18 lam18 app18 tt18 pair18 fst snd left right split zero suc rec)
                 (u tm var18 lam18 app18 tt18 pair18 fst snd left right split zero suc rec)

fst18 : {g:_}->{a:_}->{b:_}-> Tm18 g (prod18 a b) -> Tm18 g a
fst18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd, left, right, split, zero, suc, rec =>
     fst18 _ _ _ (t tm var18 lam18 app18 tt18 pair18 fst18 snd left right split zero suc rec)

snd18 : {g:_}->{a:_}->{b:_} -> Tm18 g (prod18 a b) -> Tm18 g b
snd18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left, right, split, zero, suc, rec =>
     snd18 _ _ _ (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left right split zero suc rec)

left18 : {g:_}->{a:_}->{b:_} -> Tm18 g a -> Tm18 g (sum18 a b)
left18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right, split, zero, suc, rec =>
     left18 _ _ _ (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right split zero suc rec)

right18 : {g:_}->{a:_}->{b:_} -> Tm18 g b -> Tm18 g (sum18 a b)
right18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split, zero, suc, rec =>
     right18 _ _ _ (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split zero suc rec)

split18 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm18 g (sum18 a b) -> Tm18 g (arr18 a c) -> Tm18 g (arr18 b c) -> Tm18 g c
split18 = \ t, u, v, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split18, zero, suc, rec =>
     split18 _ _ _ _
          (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero suc rec)
          (u tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero suc rec)
          (v tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero suc rec)

zero18 : {g:_} -> Tm18 g Main.nat18
zero18 = \ tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split18, zero18, suc, rec =>
  zero18 _

suc18 : {g:_} -> Tm18 g Main.nat18 -> Tm18 g Main.nat18
suc18 = \ t, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split18, zero18, suc18, rec =>
   suc18 _ (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero18 suc18 rec)

rec18 : {g:_}->{a:_} -> Tm18 g Main.nat18 -> Tm18 g (arr18 Main.nat18 (arr18 a a)) -> Tm18 g a -> Tm18 g a
rec18 = \ t, u, v, tm, var18, lam18, app18, tt18, pair18, fst18, snd18, left18, right18, split18, zero18, suc18, rec18 =>
     rec18 _ _
       (t tm var18 lam18 app18 tt18 pair18 fst18 snd18 left18 right18 split18 zero18 suc18 rec18)
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
 -> (vz  : (g:_)->(a:_) -> Var19 (snoc19 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var19 g a -> Var19 (snoc19 g b) a)
 -> Var19 g a

vz19 : {g:_}->{a:_} -> Var19 (snoc19 g a) a
vz19 = \ var, vz19, vs => vz19 _ _

vs19 : {g:_}->{b:_}->{a:_} -> Var19 g a -> Var19 (snoc19 g b) a
vs19 = \ x, var, vz19, vs19 => vs19 _ _ _ (x var vz19 vs19)

Tm19 : Con19 -> Ty19-> Type
Tm19 = \ g, a =>
    (Tm19    : Con19 -> Ty19-> Type)
 -> (var   : (g:_)->(a:_)-> Var19 g a -> Tm19 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm19 (snoc19 g a) b -> Tm19 g (arr19 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm19 g (arr19 a b) -> Tm19 g a -> Tm19 g b)
 -> (tt    : (g:_)-> Tm19 g top19)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm19 g a -> Tm19 g b -> Tm19 g (prod19 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm19 g (prod19 a b) -> Tm19 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm19 g (prod19 a b) -> Tm19 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm19 g a -> Tm19 g (sum19 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm19 g b -> Tm19 g (sum19 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm19 g (sum19 a b) -> Tm19 g (arr19 a c) -> Tm19 g (arr19 b c) -> Tm19 g c)
 -> (zero  : (g:_)-> Tm19 g nat19)
 -> (suc   : (g:_)-> Tm19 g nat19 -> Tm19 g nat19)
 -> (rec   : (g:_)->(a:_) -> Tm19 g nat19 -> Tm19 g (arr19 nat19 (arr19 a a)) -> Tm19 g a -> Tm19 g a)
 -> Tm19 g a

var19 : {g:_}->{a:_} -> Var19 g a -> Tm19 g a
var19 = \ x, tm, var19, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var19 _ _ x

lam19 : {g:_}->{a:_}->{b:_}-> Tm19 (snoc19 g a) b -> Tm19 g (arr19 a b)
lam19 = \ t, tm, var19, lam19, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam19 _ _ _ (t tm var19 lam19 app tt pair fst snd left right split zero suc rec)

app19 : {g:_}->{a:_}->{b:_} -> Tm19 g (arr19 a b) -> Tm19 g a -> Tm19 g b
app19 = \ t, u, tm, var19, lam19, app19, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app19 _ _ _ (t tm var19 lam19 app19 tt pair fst snd left right split zero suc rec)
                (u tm var19 lam19 app19 tt pair fst snd left right split zero suc rec)

tt19 : {g:_} -> Tm19 g Main.top19
tt19 = \ tm, var19, lam19, app19, tt19, pair, fst, snd, left, right, split, zero, suc, rec => tt19 _

pair19 : {g:_}->{a:_}->{b:_} -> Tm19 g a -> Tm19 g b -> Tm19 g (prod19 a b)
pair19 = \ t, u, tm, var19, lam19, app19, tt19, pair19, fst, snd, left, right, split, zero, suc, rec =>
     pair19 _ _ _ (t tm var19 lam19 app19 tt19 pair19 fst snd left right split zero suc rec)
                 (u tm var19 lam19 app19 tt19 pair19 fst snd left right split zero suc rec)

fst19 : {g:_}->{a:_}->{b:_}-> Tm19 g (prod19 a b) -> Tm19 g a
fst19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd, left, right, split, zero, suc, rec =>
     fst19 _ _ _ (t tm var19 lam19 app19 tt19 pair19 fst19 snd left right split zero suc rec)

snd19 : {g:_}->{a:_}->{b:_} -> Tm19 g (prod19 a b) -> Tm19 g b
snd19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left, right, split, zero, suc, rec =>
     snd19 _ _ _ (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left right split zero suc rec)

left19 : {g:_}->{a:_}->{b:_} -> Tm19 g a -> Tm19 g (sum19 a b)
left19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right, split, zero, suc, rec =>
     left19 _ _ _ (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right split zero suc rec)

right19 : {g:_}->{a:_}->{b:_} -> Tm19 g b -> Tm19 g (sum19 a b)
right19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split, zero, suc, rec =>
     right19 _ _ _ (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split zero suc rec)

split19 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm19 g (sum19 a b) -> Tm19 g (arr19 a c) -> Tm19 g (arr19 b c) -> Tm19 g c
split19 = \ t, u, v, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split19, zero, suc, rec =>
     split19 _ _ _ _
          (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero suc rec)
          (u tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero suc rec)
          (v tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero suc rec)

zero19 : {g:_} -> Tm19 g Main.nat19
zero19 = \ tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split19, zero19, suc, rec =>
  zero19 _

suc19 : {g:_} -> Tm19 g Main.nat19 -> Tm19 g Main.nat19
suc19 = \ t, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split19, zero19, suc19, rec =>
   suc19 _ (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero19 suc19 rec)

rec19 : {g:_}->{a:_} -> Tm19 g Main.nat19 -> Tm19 g (arr19 Main.nat19 (arr19 a a)) -> Tm19 g a -> Tm19 g a
rec19 = \ t, u, v, tm, var19, lam19, app19, tt19, pair19, fst19, snd19, left19, right19, split19, zero19, suc19, rec19 =>
     rec19 _ _
       (t tm var19 lam19 app19 tt19 pair19 fst19 snd19 left19 right19 split19 zero19 suc19 rec19)
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
 -> (vz  : (g:_)->(a:_) -> Var20 (snoc20 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var20 g a -> Var20 (snoc20 g b) a)
 -> Var20 g a

vz20 : {g:_}->{a:_} -> Var20 (snoc20 g a) a
vz20 = \ var, vz20, vs => vz20 _ _

vs20 : {g:_}->{b:_}->{a:_} -> Var20 g a -> Var20 (snoc20 g b) a
vs20 = \ x, var, vz20, vs20 => vs20 _ _ _ (x var vz20 vs20)

Tm20 : Con20 -> Ty20-> Type
Tm20 = \ g, a =>
    (Tm20    : Con20 -> Ty20-> Type)
 -> (var   : (g:_)->(a:_)-> Var20 g a -> Tm20 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm20 (snoc20 g a) b -> Tm20 g (arr20 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm20 g (arr20 a b) -> Tm20 g a -> Tm20 g b)
 -> (tt    : (g:_)-> Tm20 g top20)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm20 g a -> Tm20 g b -> Tm20 g (prod20 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm20 g (prod20 a b) -> Tm20 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm20 g (prod20 a b) -> Tm20 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm20 g a -> Tm20 g (sum20 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm20 g b -> Tm20 g (sum20 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm20 g (sum20 a b) -> Tm20 g (arr20 a c) -> Tm20 g (arr20 b c) -> Tm20 g c)
 -> (zero  : (g:_)-> Tm20 g nat20)
 -> (suc   : (g:_)-> Tm20 g nat20 -> Tm20 g nat20)
 -> (rec   : (g:_)->(a:_) -> Tm20 g nat20 -> Tm20 g (arr20 nat20 (arr20 a a)) -> Tm20 g a -> Tm20 g a)
 -> Tm20 g a

var20 : {g:_}->{a:_} -> Var20 g a -> Tm20 g a
var20 = \ x, tm, var20, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var20 _ _ x

lam20 : {g:_}->{a:_}->{b:_}-> Tm20 (snoc20 g a) b -> Tm20 g (arr20 a b)
lam20 = \ t, tm, var20, lam20, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam20 _ _ _ (t tm var20 lam20 app tt pair fst snd left right split zero suc rec)

app20 : {g:_}->{a:_}->{b:_} -> Tm20 g (arr20 a b) -> Tm20 g a -> Tm20 g b
app20 = \ t, u, tm, var20, lam20, app20, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app20 _ _ _ (t tm var20 lam20 app20 tt pair fst snd left right split zero suc rec)
                (u tm var20 lam20 app20 tt pair fst snd left right split zero suc rec)

tt20 : {g:_} -> Tm20 g Main.top20
tt20 = \ tm, var20, lam20, app20, tt20, pair, fst, snd, left, right, split, zero, suc, rec => tt20 _

pair20 : {g:_}->{a:_}->{b:_} -> Tm20 g a -> Tm20 g b -> Tm20 g (prod20 a b)
pair20 = \ t, u, tm, var20, lam20, app20, tt20, pair20, fst, snd, left, right, split, zero, suc, rec =>
     pair20 _ _ _ (t tm var20 lam20 app20 tt20 pair20 fst snd left right split zero suc rec)
                 (u tm var20 lam20 app20 tt20 pair20 fst snd left right split zero suc rec)

fst20 : {g:_}->{a:_}->{b:_}-> Tm20 g (prod20 a b) -> Tm20 g a
fst20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd, left, right, split, zero, suc, rec =>
     fst20 _ _ _ (t tm var20 lam20 app20 tt20 pair20 fst20 snd left right split zero suc rec)

snd20 : {g:_}->{a:_}->{b:_} -> Tm20 g (prod20 a b) -> Tm20 g b
snd20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left, right, split, zero, suc, rec =>
     snd20 _ _ _ (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left right split zero suc rec)

left20 : {g:_}->{a:_}->{b:_} -> Tm20 g a -> Tm20 g (sum20 a b)
left20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right, split, zero, suc, rec =>
     left20 _ _ _ (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right split zero suc rec)

right20 : {g:_}->{a:_}->{b:_} -> Tm20 g b -> Tm20 g (sum20 a b)
right20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split, zero, suc, rec =>
     right20 _ _ _ (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split zero suc rec)

split20 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm20 g (sum20 a b) -> Tm20 g (arr20 a c) -> Tm20 g (arr20 b c) -> Tm20 g c
split20 = \ t, u, v, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split20, zero, suc, rec =>
     split20 _ _ _ _
          (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero suc rec)
          (u tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero suc rec)
          (v tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero suc rec)

zero20 : {g:_} -> Tm20 g Main.nat20
zero20 = \ tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split20, zero20, suc, rec =>
  zero20 _

suc20 : {g:_} -> Tm20 g Main.nat20 -> Tm20 g Main.nat20
suc20 = \ t, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split20, zero20, suc20, rec =>
   suc20 _ (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero20 suc20 rec)

rec20 : {g:_}->{a:_} -> Tm20 g Main.nat20 -> Tm20 g (arr20 Main.nat20 (arr20 a a)) -> Tm20 g a -> Tm20 g a
rec20 = \ t, u, v, tm, var20, lam20, app20, tt20, pair20, fst20, snd20, left20, right20, split20, zero20, suc20, rec20 =>
     rec20 _ _
       (t tm var20 lam20 app20 tt20 pair20 fst20 snd20 left20 right20 split20 zero20 suc20 rec20)
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
 -> (vz  : (g:_)->(a:_) -> Var21 (snoc21 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var21 g a -> Var21 (snoc21 g b) a)
 -> Var21 g a

vz21 : {g:_}->{a:_} -> Var21 (snoc21 g a) a
vz21 = \ var, vz21, vs => vz21 _ _

vs21 : {g:_}->{b:_}->{a:_} -> Var21 g a -> Var21 (snoc21 g b) a
vs21 = \ x, var, vz21, vs21 => vs21 _ _ _ (x var vz21 vs21)

Tm21 : Con21 -> Ty21-> Type
Tm21 = \ g, a =>
    (Tm21    : Con21 -> Ty21-> Type)
 -> (var   : (g:_)->(a:_)-> Var21 g a -> Tm21 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm21 (snoc21 g a) b -> Tm21 g (arr21 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm21 g (arr21 a b) -> Tm21 g a -> Tm21 g b)
 -> (tt    : (g:_)-> Tm21 g top21)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm21 g a -> Tm21 g b -> Tm21 g (prod21 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm21 g (prod21 a b) -> Tm21 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm21 g (prod21 a b) -> Tm21 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm21 g a -> Tm21 g (sum21 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm21 g b -> Tm21 g (sum21 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm21 g (sum21 a b) -> Tm21 g (arr21 a c) -> Tm21 g (arr21 b c) -> Tm21 g c)
 -> (zero  : (g:_)-> Tm21 g nat21)
 -> (suc   : (g:_)-> Tm21 g nat21 -> Tm21 g nat21)
 -> (rec   : (g:_)->(a:_) -> Tm21 g nat21 -> Tm21 g (arr21 nat21 (arr21 a a)) -> Tm21 g a -> Tm21 g a)
 -> Tm21 g a

var21 : {g:_}->{a:_} -> Var21 g a -> Tm21 g a
var21 = \ x, tm, var21, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var21 _ _ x

lam21 : {g:_}->{a:_}->{b:_}-> Tm21 (snoc21 g a) b -> Tm21 g (arr21 a b)
lam21 = \ t, tm, var21, lam21, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam21 _ _ _ (t tm var21 lam21 app tt pair fst snd left right split zero suc rec)

app21 : {g:_}->{a:_}->{b:_} -> Tm21 g (arr21 a b) -> Tm21 g a -> Tm21 g b
app21 = \ t, u, tm, var21, lam21, app21, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app21 _ _ _ (t tm var21 lam21 app21 tt pair fst snd left right split zero suc rec)
                (u tm var21 lam21 app21 tt pair fst snd left right split zero suc rec)

tt21 : {g:_} -> Tm21 g Main.top21
tt21 = \ tm, var21, lam21, app21, tt21, pair, fst, snd, left, right, split, zero, suc, rec => tt21 _

pair21 : {g:_}->{a:_}->{b:_} -> Tm21 g a -> Tm21 g b -> Tm21 g (prod21 a b)
pair21 = \ t, u, tm, var21, lam21, app21, tt21, pair21, fst, snd, left, right, split, zero, suc, rec =>
     pair21 _ _ _ (t tm var21 lam21 app21 tt21 pair21 fst snd left right split zero suc rec)
                 (u tm var21 lam21 app21 tt21 pair21 fst snd left right split zero suc rec)

fst21 : {g:_}->{a:_}->{b:_}-> Tm21 g (prod21 a b) -> Tm21 g a
fst21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd, left, right, split, zero, suc, rec =>
     fst21 _ _ _ (t tm var21 lam21 app21 tt21 pair21 fst21 snd left right split zero suc rec)

snd21 : {g:_}->{a:_}->{b:_} -> Tm21 g (prod21 a b) -> Tm21 g b
snd21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left, right, split, zero, suc, rec =>
     snd21 _ _ _ (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left right split zero suc rec)

left21 : {g:_}->{a:_}->{b:_} -> Tm21 g a -> Tm21 g (sum21 a b)
left21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right, split, zero, suc, rec =>
     left21 _ _ _ (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right split zero suc rec)

right21 : {g:_}->{a:_}->{b:_} -> Tm21 g b -> Tm21 g (sum21 a b)
right21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split, zero, suc, rec =>
     right21 _ _ _ (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split zero suc rec)

split21 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm21 g (sum21 a b) -> Tm21 g (arr21 a c) -> Tm21 g (arr21 b c) -> Tm21 g c
split21 = \ t, u, v, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split21, zero, suc, rec =>
     split21 _ _ _ _
          (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero suc rec)
          (u tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero suc rec)
          (v tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero suc rec)

zero21 : {g:_} -> Tm21 g Main.nat21
zero21 = \ tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split21, zero21, suc, rec =>
  zero21 _

suc21 : {g:_} -> Tm21 g Main.nat21 -> Tm21 g Main.nat21
suc21 = \ t, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split21, zero21, suc21, rec =>
   suc21 _ (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero21 suc21 rec)

rec21 : {g:_}->{a:_} -> Tm21 g Main.nat21 -> Tm21 g (arr21 Main.nat21 (arr21 a a)) -> Tm21 g a -> Tm21 g a
rec21 = \ t, u, v, tm, var21, lam21, app21, tt21, pair21, fst21, snd21, left21, right21, split21, zero21, suc21, rec21 =>
     rec21 _ _
       (t tm var21 lam21 app21 tt21 pair21 fst21 snd21 left21 right21 split21 zero21 suc21 rec21)
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
 -> (vz  : (g:_)->(a:_) -> Var22 (snoc22 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var22 g a -> Var22 (snoc22 g b) a)
 -> Var22 g a

vz22 : {g:_}->{a:_} -> Var22 (snoc22 g a) a
vz22 = \ var, vz22, vs => vz22 _ _

vs22 : {g:_}->{b:_}->{a:_} -> Var22 g a -> Var22 (snoc22 g b) a
vs22 = \ x, var, vz22, vs22 => vs22 _ _ _ (x var vz22 vs22)

Tm22 : Con22 -> Ty22-> Type
Tm22 = \ g, a =>
    (Tm22    : Con22 -> Ty22-> Type)
 -> (var   : (g:_)->(a:_)-> Var22 g a -> Tm22 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm22 (snoc22 g a) b -> Tm22 g (arr22 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm22 g (arr22 a b) -> Tm22 g a -> Tm22 g b)
 -> (tt    : (g:_)-> Tm22 g top22)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm22 g a -> Tm22 g b -> Tm22 g (prod22 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm22 g (prod22 a b) -> Tm22 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm22 g (prod22 a b) -> Tm22 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm22 g a -> Tm22 g (sum22 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm22 g b -> Tm22 g (sum22 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm22 g (sum22 a b) -> Tm22 g (arr22 a c) -> Tm22 g (arr22 b c) -> Tm22 g c)
 -> (zero  : (g:_)-> Tm22 g nat22)
 -> (suc   : (g:_)-> Tm22 g nat22 -> Tm22 g nat22)
 -> (rec   : (g:_)->(a:_) -> Tm22 g nat22 -> Tm22 g (arr22 nat22 (arr22 a a)) -> Tm22 g a -> Tm22 g a)
 -> Tm22 g a

var22 : {g:_}->{a:_} -> Var22 g a -> Tm22 g a
var22 = \ x, tm, var22, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var22 _ _ x

lam22 : {g:_}->{a:_}->{b:_}-> Tm22 (snoc22 g a) b -> Tm22 g (arr22 a b)
lam22 = \ t, tm, var22, lam22, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam22 _ _ _ (t tm var22 lam22 app tt pair fst snd left right split zero suc rec)

app22 : {g:_}->{a:_}->{b:_} -> Tm22 g (arr22 a b) -> Tm22 g a -> Tm22 g b
app22 = \ t, u, tm, var22, lam22, app22, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app22 _ _ _ (t tm var22 lam22 app22 tt pair fst snd left right split zero suc rec)
                (u tm var22 lam22 app22 tt pair fst snd left right split zero suc rec)

tt22 : {g:_} -> Tm22 g Main.top22
tt22 = \ tm, var22, lam22, app22, tt22, pair, fst, snd, left, right, split, zero, suc, rec => tt22 _

pair22 : {g:_}->{a:_}->{b:_} -> Tm22 g a -> Tm22 g b -> Tm22 g (prod22 a b)
pair22 = \ t, u, tm, var22, lam22, app22, tt22, pair22, fst, snd, left, right, split, zero, suc, rec =>
     pair22 _ _ _ (t tm var22 lam22 app22 tt22 pair22 fst snd left right split zero suc rec)
                 (u tm var22 lam22 app22 tt22 pair22 fst snd left right split zero suc rec)

fst22 : {g:_}->{a:_}->{b:_}-> Tm22 g (prod22 a b) -> Tm22 g a
fst22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd, left, right, split, zero, suc, rec =>
     fst22 _ _ _ (t tm var22 lam22 app22 tt22 pair22 fst22 snd left right split zero suc rec)

snd22 : {g:_}->{a:_}->{b:_} -> Tm22 g (prod22 a b) -> Tm22 g b
snd22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left, right, split, zero, suc, rec =>
     snd22 _ _ _ (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left right split zero suc rec)

left22 : {g:_}->{a:_}->{b:_} -> Tm22 g a -> Tm22 g (sum22 a b)
left22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right, split, zero, suc, rec =>
     left22 _ _ _ (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right split zero suc rec)

right22 : {g:_}->{a:_}->{b:_} -> Tm22 g b -> Tm22 g (sum22 a b)
right22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split, zero, suc, rec =>
     right22 _ _ _ (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split zero suc rec)

split22 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm22 g (sum22 a b) -> Tm22 g (arr22 a c) -> Tm22 g (arr22 b c) -> Tm22 g c
split22 = \ t, u, v, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split22, zero, suc, rec =>
     split22 _ _ _ _
          (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero suc rec)
          (u tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero suc rec)
          (v tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero suc rec)

zero22 : {g:_} -> Tm22 g Main.nat22
zero22 = \ tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split22, zero22, suc, rec =>
  zero22 _

suc22 : {g:_} -> Tm22 g Main.nat22 -> Tm22 g Main.nat22
suc22 = \ t, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split22, zero22, suc22, rec =>
   suc22 _ (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero22 suc22 rec)

rec22 : {g:_}->{a:_} -> Tm22 g Main.nat22 -> Tm22 g (arr22 Main.nat22 (arr22 a a)) -> Tm22 g a -> Tm22 g a
rec22 = \ t, u, v, tm, var22, lam22, app22, tt22, pair22, fst22, snd22, left22, right22, split22, zero22, suc22, rec22 =>
     rec22 _ _
       (t tm var22 lam22 app22 tt22 pair22 fst22 snd22 left22 right22 split22 zero22 suc22 rec22)
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
 -> (vz  : (g:_)->(a:_) -> Var23 (snoc23 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var23 g a -> Var23 (snoc23 g b) a)
 -> Var23 g a

vz23 : {g:_}->{a:_} -> Var23 (snoc23 g a) a
vz23 = \ var, vz23, vs => vz23 _ _

vs23 : {g:_}->{b:_}->{a:_} -> Var23 g a -> Var23 (snoc23 g b) a
vs23 = \ x, var, vz23, vs23 => vs23 _ _ _ (x var vz23 vs23)

Tm23 : Con23 -> Ty23-> Type
Tm23 = \ g, a =>
    (Tm23    : Con23 -> Ty23-> Type)
 -> (var   : (g:_)->(a:_)-> Var23 g a -> Tm23 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm23 (snoc23 g a) b -> Tm23 g (arr23 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm23 g (arr23 a b) -> Tm23 g a -> Tm23 g b)
 -> (tt    : (g:_)-> Tm23 g top23)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm23 g a -> Tm23 g b -> Tm23 g (prod23 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm23 g (prod23 a b) -> Tm23 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm23 g (prod23 a b) -> Tm23 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm23 g a -> Tm23 g (sum23 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm23 g b -> Tm23 g (sum23 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm23 g (sum23 a b) -> Tm23 g (arr23 a c) -> Tm23 g (arr23 b c) -> Tm23 g c)
 -> (zero  : (g:_)-> Tm23 g nat23)
 -> (suc   : (g:_)-> Tm23 g nat23 -> Tm23 g nat23)
 -> (rec   : (g:_)->(a:_) -> Tm23 g nat23 -> Tm23 g (arr23 nat23 (arr23 a a)) -> Tm23 g a -> Tm23 g a)
 -> Tm23 g a

var23 : {g:_}->{a:_} -> Var23 g a -> Tm23 g a
var23 = \ x, tm, var23, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var23 _ _ x

lam23 : {g:_}->{a:_}->{b:_}-> Tm23 (snoc23 g a) b -> Tm23 g (arr23 a b)
lam23 = \ t, tm, var23, lam23, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam23 _ _ _ (t tm var23 lam23 app tt pair fst snd left right split zero suc rec)

app23 : {g:_}->{a:_}->{b:_} -> Tm23 g (arr23 a b) -> Tm23 g a -> Tm23 g b
app23 = \ t, u, tm, var23, lam23, app23, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app23 _ _ _ (t tm var23 lam23 app23 tt pair fst snd left right split zero suc rec)
                (u tm var23 lam23 app23 tt pair fst snd left right split zero suc rec)

tt23 : {g:_} -> Tm23 g Main.top23
tt23 = \ tm, var23, lam23, app23, tt23, pair, fst, snd, left, right, split, zero, suc, rec => tt23 _

pair23 : {g:_}->{a:_}->{b:_} -> Tm23 g a -> Tm23 g b -> Tm23 g (prod23 a b)
pair23 = \ t, u, tm, var23, lam23, app23, tt23, pair23, fst, snd, left, right, split, zero, suc, rec =>
     pair23 _ _ _ (t tm var23 lam23 app23 tt23 pair23 fst snd left right split zero suc rec)
                 (u tm var23 lam23 app23 tt23 pair23 fst snd left right split zero suc rec)

fst23 : {g:_}->{a:_}->{b:_}-> Tm23 g (prod23 a b) -> Tm23 g a
fst23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd, left, right, split, zero, suc, rec =>
     fst23 _ _ _ (t tm var23 lam23 app23 tt23 pair23 fst23 snd left right split zero suc rec)

snd23 : {g:_}->{a:_}->{b:_} -> Tm23 g (prod23 a b) -> Tm23 g b
snd23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left, right, split, zero, suc, rec =>
     snd23 _ _ _ (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left right split zero suc rec)

left23 : {g:_}->{a:_}->{b:_} -> Tm23 g a -> Tm23 g (sum23 a b)
left23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right, split, zero, suc, rec =>
     left23 _ _ _ (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right split zero suc rec)

right23 : {g:_}->{a:_}->{b:_} -> Tm23 g b -> Tm23 g (sum23 a b)
right23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split, zero, suc, rec =>
     right23 _ _ _ (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split zero suc rec)

split23 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm23 g (sum23 a b) -> Tm23 g (arr23 a c) -> Tm23 g (arr23 b c) -> Tm23 g c
split23 = \ t, u, v, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split23, zero, suc, rec =>
     split23 _ _ _ _
          (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero suc rec)
          (u tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero suc rec)
          (v tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero suc rec)

zero23 : {g:_} -> Tm23 g Main.nat23
zero23 = \ tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split23, zero23, suc, rec =>
  zero23 _

suc23 : {g:_} -> Tm23 g Main.nat23 -> Tm23 g Main.nat23
suc23 = \ t, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split23, zero23, suc23, rec =>
   suc23 _ (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero23 suc23 rec)

rec23 : {g:_}->{a:_} -> Tm23 g Main.nat23 -> Tm23 g (arr23 Main.nat23 (arr23 a a)) -> Tm23 g a -> Tm23 g a
rec23 = \ t, u, v, tm, var23, lam23, app23, tt23, pair23, fst23, snd23, left23, right23, split23, zero23, suc23, rec23 =>
     rec23 _ _
       (t tm var23 lam23 app23 tt23 pair23 fst23 snd23 left23 right23 split23 zero23 suc23 rec23)
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
 -> (vz  : (g:_)->(a:_) -> Var24 (snoc24 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var24 g a -> Var24 (snoc24 g b) a)
 -> Var24 g a

vz24 : {g:_}->{a:_} -> Var24 (snoc24 g a) a
vz24 = \ var, vz24, vs => vz24 _ _

vs24 : {g:_}->{b:_}->{a:_} -> Var24 g a -> Var24 (snoc24 g b) a
vs24 = \ x, var, vz24, vs24 => vs24 _ _ _ (x var vz24 vs24)

Tm24 : Con24 -> Ty24-> Type
Tm24 = \ g, a =>
    (Tm24    : Con24 -> Ty24-> Type)
 -> (var   : (g:_)->(a:_)-> Var24 g a -> Tm24 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm24 (snoc24 g a) b -> Tm24 g (arr24 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm24 g (arr24 a b) -> Tm24 g a -> Tm24 g b)
 -> (tt    : (g:_)-> Tm24 g top24)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm24 g a -> Tm24 g b -> Tm24 g (prod24 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm24 g (prod24 a b) -> Tm24 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm24 g (prod24 a b) -> Tm24 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm24 g a -> Tm24 g (sum24 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm24 g b -> Tm24 g (sum24 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm24 g (sum24 a b) -> Tm24 g (arr24 a c) -> Tm24 g (arr24 b c) -> Tm24 g c)
 -> (zero  : (g:_)-> Tm24 g nat24)
 -> (suc   : (g:_)-> Tm24 g nat24 -> Tm24 g nat24)
 -> (rec   : (g:_)->(a:_) -> Tm24 g nat24 -> Tm24 g (arr24 nat24 (arr24 a a)) -> Tm24 g a -> Tm24 g a)
 -> Tm24 g a

var24 : {g:_}->{a:_} -> Var24 g a -> Tm24 g a
var24 = \ x, tm, var24, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var24 _ _ x

lam24 : {g:_}->{a:_}->{b:_}-> Tm24 (snoc24 g a) b -> Tm24 g (arr24 a b)
lam24 = \ t, tm, var24, lam24, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam24 _ _ _ (t tm var24 lam24 app tt pair fst snd left right split zero suc rec)

app24 : {g:_}->{a:_}->{b:_} -> Tm24 g (arr24 a b) -> Tm24 g a -> Tm24 g b
app24 = \ t, u, tm, var24, lam24, app24, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app24 _ _ _ (t tm var24 lam24 app24 tt pair fst snd left right split zero suc rec)
                (u tm var24 lam24 app24 tt pair fst snd left right split zero suc rec)

tt24 : {g:_} -> Tm24 g Main.top24
tt24 = \ tm, var24, lam24, app24, tt24, pair, fst, snd, left, right, split, zero, suc, rec => tt24 _

pair24 : {g:_}->{a:_}->{b:_} -> Tm24 g a -> Tm24 g b -> Tm24 g (prod24 a b)
pair24 = \ t, u, tm, var24, lam24, app24, tt24, pair24, fst, snd, left, right, split, zero, suc, rec =>
     pair24 _ _ _ (t tm var24 lam24 app24 tt24 pair24 fst snd left right split zero suc rec)
                 (u tm var24 lam24 app24 tt24 pair24 fst snd left right split zero suc rec)

fst24 : {g:_}->{a:_}->{b:_}-> Tm24 g (prod24 a b) -> Tm24 g a
fst24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd, left, right, split, zero, suc, rec =>
     fst24 _ _ _ (t tm var24 lam24 app24 tt24 pair24 fst24 snd left right split zero suc rec)

snd24 : {g:_}->{a:_}->{b:_} -> Tm24 g (prod24 a b) -> Tm24 g b
snd24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left, right, split, zero, suc, rec =>
     snd24 _ _ _ (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left right split zero suc rec)

left24 : {g:_}->{a:_}->{b:_} -> Tm24 g a -> Tm24 g (sum24 a b)
left24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right, split, zero, suc, rec =>
     left24 _ _ _ (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right split zero suc rec)

right24 : {g:_}->{a:_}->{b:_} -> Tm24 g b -> Tm24 g (sum24 a b)
right24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split, zero, suc, rec =>
     right24 _ _ _ (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split zero suc rec)

split24 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm24 g (sum24 a b) -> Tm24 g (arr24 a c) -> Tm24 g (arr24 b c) -> Tm24 g c
split24 = \ t, u, v, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split24, zero, suc, rec =>
     split24 _ _ _ _
          (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero suc rec)
          (u tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero suc rec)
          (v tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero suc rec)

zero24 : {g:_} -> Tm24 g Main.nat24
zero24 = \ tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split24, zero24, suc, rec =>
  zero24 _

suc24 : {g:_} -> Tm24 g Main.nat24 -> Tm24 g Main.nat24
suc24 = \ t, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split24, zero24, suc24, rec =>
   suc24 _ (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero24 suc24 rec)

rec24 : {g:_}->{a:_} -> Tm24 g Main.nat24 -> Tm24 g (arr24 Main.nat24 (arr24 a a)) -> Tm24 g a -> Tm24 g a
rec24 = \ t, u, v, tm, var24, lam24, app24, tt24, pair24, fst24, snd24, left24, right24, split24, zero24, suc24, rec24 =>
     rec24 _ _
       (t tm var24 lam24 app24 tt24 pair24 fst24 snd24 left24 right24 split24 zero24 suc24 rec24)
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
 -> (vz  : (g:_)->(a:_) -> Var25 (snoc25 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var25 g a -> Var25 (snoc25 g b) a)
 -> Var25 g a

vz25 : {g:_}->{a:_} -> Var25 (snoc25 g a) a
vz25 = \ var, vz25, vs => vz25 _ _

vs25 : {g:_}->{b:_}->{a:_} -> Var25 g a -> Var25 (snoc25 g b) a
vs25 = \ x, var, vz25, vs25 => vs25 _ _ _ (x var vz25 vs25)

Tm25 : Con25 -> Ty25-> Type
Tm25 = \ g, a =>
    (Tm25    : Con25 -> Ty25-> Type)
 -> (var   : (g:_)->(a:_)-> Var25 g a -> Tm25 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm25 (snoc25 g a) b -> Tm25 g (arr25 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm25 g (arr25 a b) -> Tm25 g a -> Tm25 g b)
 -> (tt    : (g:_)-> Tm25 g top25)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm25 g a -> Tm25 g b -> Tm25 g (prod25 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm25 g (prod25 a b) -> Tm25 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm25 g (prod25 a b) -> Tm25 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm25 g a -> Tm25 g (sum25 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm25 g b -> Tm25 g (sum25 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm25 g (sum25 a b) -> Tm25 g (arr25 a c) -> Tm25 g (arr25 b c) -> Tm25 g c)
 -> (zero  : (g:_)-> Tm25 g nat25)
 -> (suc   : (g:_)-> Tm25 g nat25 -> Tm25 g nat25)
 -> (rec   : (g:_)->(a:_) -> Tm25 g nat25 -> Tm25 g (arr25 nat25 (arr25 a a)) -> Tm25 g a -> Tm25 g a)
 -> Tm25 g a

var25 : {g:_}->{a:_} -> Var25 g a -> Tm25 g a
var25 = \ x, tm, var25, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var25 _ _ x

lam25 : {g:_}->{a:_}->{b:_}-> Tm25 (snoc25 g a) b -> Tm25 g (arr25 a b)
lam25 = \ t, tm, var25, lam25, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam25 _ _ _ (t tm var25 lam25 app tt pair fst snd left right split zero suc rec)

app25 : {g:_}->{a:_}->{b:_} -> Tm25 g (arr25 a b) -> Tm25 g a -> Tm25 g b
app25 = \ t, u, tm, var25, lam25, app25, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app25 _ _ _ (t tm var25 lam25 app25 tt pair fst snd left right split zero suc rec)
                (u tm var25 lam25 app25 tt pair fst snd left right split zero suc rec)

tt25 : {g:_} -> Tm25 g Main.top25
tt25 = \ tm, var25, lam25, app25, tt25, pair, fst, snd, left, right, split, zero, suc, rec => tt25 _

pair25 : {g:_}->{a:_}->{b:_} -> Tm25 g a -> Tm25 g b -> Tm25 g (prod25 a b)
pair25 = \ t, u, tm, var25, lam25, app25, tt25, pair25, fst, snd, left, right, split, zero, suc, rec =>
     pair25 _ _ _ (t tm var25 lam25 app25 tt25 pair25 fst snd left right split zero suc rec)
                 (u tm var25 lam25 app25 tt25 pair25 fst snd left right split zero suc rec)

fst25 : {g:_}->{a:_}->{b:_}-> Tm25 g (prod25 a b) -> Tm25 g a
fst25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd, left, right, split, zero, suc, rec =>
     fst25 _ _ _ (t tm var25 lam25 app25 tt25 pair25 fst25 snd left right split zero suc rec)

snd25 : {g:_}->{a:_}->{b:_} -> Tm25 g (prod25 a b) -> Tm25 g b
snd25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left, right, split, zero, suc, rec =>
     snd25 _ _ _ (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left right split zero suc rec)

left25 : {g:_}->{a:_}->{b:_} -> Tm25 g a -> Tm25 g (sum25 a b)
left25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right, split, zero, suc, rec =>
     left25 _ _ _ (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right split zero suc rec)

right25 : {g:_}->{a:_}->{b:_} -> Tm25 g b -> Tm25 g (sum25 a b)
right25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split, zero, suc, rec =>
     right25 _ _ _ (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split zero suc rec)

split25 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm25 g (sum25 a b) -> Tm25 g (arr25 a c) -> Tm25 g (arr25 b c) -> Tm25 g c
split25 = \ t, u, v, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split25, zero, suc, rec =>
     split25 _ _ _ _
          (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero suc rec)
          (u tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero suc rec)
          (v tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero suc rec)

zero25 : {g:_} -> Tm25 g Main.nat25
zero25 = \ tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split25, zero25, suc, rec =>
  zero25 _

suc25 : {g:_} -> Tm25 g Main.nat25 -> Tm25 g Main.nat25
suc25 = \ t, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split25, zero25, suc25, rec =>
   suc25 _ (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero25 suc25 rec)

rec25 : {g:_}->{a:_} -> Tm25 g Main.nat25 -> Tm25 g (arr25 Main.nat25 (arr25 a a)) -> Tm25 g a -> Tm25 g a
rec25 = \ t, u, v, tm, var25, lam25, app25, tt25, pair25, fst25, snd25, left25, right25, split25, zero25, suc25, rec25 =>
     rec25 _ _
       (t tm var25 lam25 app25 tt25 pair25 fst25 snd25 left25 right25 split25 zero25 suc25 rec25)
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
 -> (vz  : (g:_)->(a:_) -> Var26 (snoc26 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var26 g a -> Var26 (snoc26 g b) a)
 -> Var26 g a

vz26 : {g:_}->{a:_} -> Var26 (snoc26 g a) a
vz26 = \ var, vz26, vs => vz26 _ _

vs26 : {g:_}->{b:_}->{a:_} -> Var26 g a -> Var26 (snoc26 g b) a
vs26 = \ x, var, vz26, vs26 => vs26 _ _ _ (x var vz26 vs26)

Tm26 : Con26 -> Ty26-> Type
Tm26 = \ g, a =>
    (Tm26    : Con26 -> Ty26-> Type)
 -> (var   : (g:_)->(a:_)-> Var26 g a -> Tm26 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm26 (snoc26 g a) b -> Tm26 g (arr26 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm26 g (arr26 a b) -> Tm26 g a -> Tm26 g b)
 -> (tt    : (g:_)-> Tm26 g top26)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm26 g a -> Tm26 g b -> Tm26 g (prod26 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm26 g (prod26 a b) -> Tm26 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm26 g (prod26 a b) -> Tm26 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm26 g a -> Tm26 g (sum26 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm26 g b -> Tm26 g (sum26 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm26 g (sum26 a b) -> Tm26 g (arr26 a c) -> Tm26 g (arr26 b c) -> Tm26 g c)
 -> (zero  : (g:_)-> Tm26 g nat26)
 -> (suc   : (g:_)-> Tm26 g nat26 -> Tm26 g nat26)
 -> (rec   : (g:_)->(a:_) -> Tm26 g nat26 -> Tm26 g (arr26 nat26 (arr26 a a)) -> Tm26 g a -> Tm26 g a)
 -> Tm26 g a

var26 : {g:_}->{a:_} -> Var26 g a -> Tm26 g a
var26 = \ x, tm, var26, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var26 _ _ x

lam26 : {g:_}->{a:_}->{b:_}-> Tm26 (snoc26 g a) b -> Tm26 g (arr26 a b)
lam26 = \ t, tm, var26, lam26, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam26 _ _ _ (t tm var26 lam26 app tt pair fst snd left right split zero suc rec)

app26 : {g:_}->{a:_}->{b:_} -> Tm26 g (arr26 a b) -> Tm26 g a -> Tm26 g b
app26 = \ t, u, tm, var26, lam26, app26, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app26 _ _ _ (t tm var26 lam26 app26 tt pair fst snd left right split zero suc rec)
                (u tm var26 lam26 app26 tt pair fst snd left right split zero suc rec)

tt26 : {g:_} -> Tm26 g Main.top26
tt26 = \ tm, var26, lam26, app26, tt26, pair, fst, snd, left, right, split, zero, suc, rec => tt26 _

pair26 : {g:_}->{a:_}->{b:_} -> Tm26 g a -> Tm26 g b -> Tm26 g (prod26 a b)
pair26 = \ t, u, tm, var26, lam26, app26, tt26, pair26, fst, snd, left, right, split, zero, suc, rec =>
     pair26 _ _ _ (t tm var26 lam26 app26 tt26 pair26 fst snd left right split zero suc rec)
                 (u tm var26 lam26 app26 tt26 pair26 fst snd left right split zero suc rec)

fst26 : {g:_}->{a:_}->{b:_}-> Tm26 g (prod26 a b) -> Tm26 g a
fst26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd, left, right, split, zero, suc, rec =>
     fst26 _ _ _ (t tm var26 lam26 app26 tt26 pair26 fst26 snd left right split zero suc rec)

snd26 : {g:_}->{a:_}->{b:_} -> Tm26 g (prod26 a b) -> Tm26 g b
snd26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left, right, split, zero, suc, rec =>
     snd26 _ _ _ (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left right split zero suc rec)

left26 : {g:_}->{a:_}->{b:_} -> Tm26 g a -> Tm26 g (sum26 a b)
left26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right, split, zero, suc, rec =>
     left26 _ _ _ (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right split zero suc rec)

right26 : {g:_}->{a:_}->{b:_} -> Tm26 g b -> Tm26 g (sum26 a b)
right26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split, zero, suc, rec =>
     right26 _ _ _ (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split zero suc rec)

split26 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm26 g (sum26 a b) -> Tm26 g (arr26 a c) -> Tm26 g (arr26 b c) -> Tm26 g c
split26 = \ t, u, v, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split26, zero, suc, rec =>
     split26 _ _ _ _
          (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero suc rec)
          (u tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero suc rec)
          (v tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero suc rec)

zero26 : {g:_} -> Tm26 g Main.nat26
zero26 = \ tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split26, zero26, suc, rec =>
  zero26 _

suc26 : {g:_} -> Tm26 g Main.nat26 -> Tm26 g Main.nat26
suc26 = \ t, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split26, zero26, suc26, rec =>
   suc26 _ (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero26 suc26 rec)

rec26 : {g:_}->{a:_} -> Tm26 g Main.nat26 -> Tm26 g (arr26 Main.nat26 (arr26 a a)) -> Tm26 g a -> Tm26 g a
rec26 = \ t, u, v, tm, var26, lam26, app26, tt26, pair26, fst26, snd26, left26, right26, split26, zero26, suc26, rec26 =>
     rec26 _ _
       (t tm var26 lam26 app26 tt26 pair26 fst26 snd26 left26 right26 split26 zero26 suc26 rec26)
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
 -> (vz  : (g:_)->(a:_) -> Var27 (snoc27 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var27 g a -> Var27 (snoc27 g b) a)
 -> Var27 g a

vz27 : {g:_}->{a:_} -> Var27 (snoc27 g a) a
vz27 = \ var, vz27, vs => vz27 _ _

vs27 : {g:_}->{b:_}->{a:_} -> Var27 g a -> Var27 (snoc27 g b) a
vs27 = \ x, var, vz27, vs27 => vs27 _ _ _ (x var vz27 vs27)

Tm27 : Con27 -> Ty27-> Type
Tm27 = \ g, a =>
    (Tm27    : Con27 -> Ty27-> Type)
 -> (var   : (g:_)->(a:_)-> Var27 g a -> Tm27 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm27 (snoc27 g a) b -> Tm27 g (arr27 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm27 g (arr27 a b) -> Tm27 g a -> Tm27 g b)
 -> (tt    : (g:_)-> Tm27 g top27)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm27 g a -> Tm27 g b -> Tm27 g (prod27 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm27 g (prod27 a b) -> Tm27 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm27 g (prod27 a b) -> Tm27 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm27 g a -> Tm27 g (sum27 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm27 g b -> Tm27 g (sum27 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm27 g (sum27 a b) -> Tm27 g (arr27 a c) -> Tm27 g (arr27 b c) -> Tm27 g c)
 -> (zero  : (g:_)-> Tm27 g nat27)
 -> (suc   : (g:_)-> Tm27 g nat27 -> Tm27 g nat27)
 -> (rec   : (g:_)->(a:_) -> Tm27 g nat27 -> Tm27 g (arr27 nat27 (arr27 a a)) -> Tm27 g a -> Tm27 g a)
 -> Tm27 g a

var27 : {g:_}->{a:_} -> Var27 g a -> Tm27 g a
var27 = \ x, tm, var27, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var27 _ _ x

lam27 : {g:_}->{a:_}->{b:_}-> Tm27 (snoc27 g a) b -> Tm27 g (arr27 a b)
lam27 = \ t, tm, var27, lam27, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam27 _ _ _ (t tm var27 lam27 app tt pair fst snd left right split zero suc rec)

app27 : {g:_}->{a:_}->{b:_} -> Tm27 g (arr27 a b) -> Tm27 g a -> Tm27 g b
app27 = \ t, u, tm, var27, lam27, app27, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app27 _ _ _ (t tm var27 lam27 app27 tt pair fst snd left right split zero suc rec)
                (u tm var27 lam27 app27 tt pair fst snd left right split zero suc rec)

tt27 : {g:_} -> Tm27 g Main.top27
tt27 = \ tm, var27, lam27, app27, tt27, pair, fst, snd, left, right, split, zero, suc, rec => tt27 _

pair27 : {g:_}->{a:_}->{b:_} -> Tm27 g a -> Tm27 g b -> Tm27 g (prod27 a b)
pair27 = \ t, u, tm, var27, lam27, app27, tt27, pair27, fst, snd, left, right, split, zero, suc, rec =>
     pair27 _ _ _ (t tm var27 lam27 app27 tt27 pair27 fst snd left right split zero suc rec)
                 (u tm var27 lam27 app27 tt27 pair27 fst snd left right split zero suc rec)

fst27 : {g:_}->{a:_}->{b:_}-> Tm27 g (prod27 a b) -> Tm27 g a
fst27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd, left, right, split, zero, suc, rec =>
     fst27 _ _ _ (t tm var27 lam27 app27 tt27 pair27 fst27 snd left right split zero suc rec)

snd27 : {g:_}->{a:_}->{b:_} -> Tm27 g (prod27 a b) -> Tm27 g b
snd27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left, right, split, zero, suc, rec =>
     snd27 _ _ _ (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left right split zero suc rec)

left27 : {g:_}->{a:_}->{b:_} -> Tm27 g a -> Tm27 g (sum27 a b)
left27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right, split, zero, suc, rec =>
     left27 _ _ _ (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right split zero suc rec)

right27 : {g:_}->{a:_}->{b:_} -> Tm27 g b -> Tm27 g (sum27 a b)
right27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split, zero, suc, rec =>
     right27 _ _ _ (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split zero suc rec)

split27 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm27 g (sum27 a b) -> Tm27 g (arr27 a c) -> Tm27 g (arr27 b c) -> Tm27 g c
split27 = \ t, u, v, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split27, zero, suc, rec =>
     split27 _ _ _ _
          (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero suc rec)
          (u tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero suc rec)
          (v tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero suc rec)

zero27 : {g:_} -> Tm27 g Main.nat27
zero27 = \ tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split27, zero27, suc, rec =>
  zero27 _

suc27 : {g:_} -> Tm27 g Main.nat27 -> Tm27 g Main.nat27
suc27 = \ t, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split27, zero27, suc27, rec =>
   suc27 _ (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero27 suc27 rec)

rec27 : {g:_}->{a:_} -> Tm27 g Main.nat27 -> Tm27 g (arr27 Main.nat27 (arr27 a a)) -> Tm27 g a -> Tm27 g a
rec27 = \ t, u, v, tm, var27, lam27, app27, tt27, pair27, fst27, snd27, left27, right27, split27, zero27, suc27, rec27 =>
     rec27 _ _
       (t tm var27 lam27 app27 tt27 pair27 fst27 snd27 left27 right27 split27 zero27 suc27 rec27)
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
 -> (vz  : (g:_)->(a:_) -> Var28 (snoc28 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var28 g a -> Var28 (snoc28 g b) a)
 -> Var28 g a

vz28 : {g:_}->{a:_} -> Var28 (snoc28 g a) a
vz28 = \ var, vz28, vs => vz28 _ _

vs28 : {g:_}->{b:_}->{a:_} -> Var28 g a -> Var28 (snoc28 g b) a
vs28 = \ x, var, vz28, vs28 => vs28 _ _ _ (x var vz28 vs28)

Tm28 : Con28 -> Ty28-> Type
Tm28 = \ g, a =>
    (Tm28    : Con28 -> Ty28-> Type)
 -> (var   : (g:_)->(a:_)-> Var28 g a -> Tm28 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm28 (snoc28 g a) b -> Tm28 g (arr28 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm28 g (arr28 a b) -> Tm28 g a -> Tm28 g b)
 -> (tt    : (g:_)-> Tm28 g top28)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm28 g a -> Tm28 g b -> Tm28 g (prod28 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm28 g (prod28 a b) -> Tm28 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm28 g (prod28 a b) -> Tm28 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm28 g a -> Tm28 g (sum28 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm28 g b -> Tm28 g (sum28 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm28 g (sum28 a b) -> Tm28 g (arr28 a c) -> Tm28 g (arr28 b c) -> Tm28 g c)
 -> (zero  : (g:_)-> Tm28 g nat28)
 -> (suc   : (g:_)-> Tm28 g nat28 -> Tm28 g nat28)
 -> (rec   : (g:_)->(a:_) -> Tm28 g nat28 -> Tm28 g (arr28 nat28 (arr28 a a)) -> Tm28 g a -> Tm28 g a)
 -> Tm28 g a

var28 : {g:_}->{a:_} -> Var28 g a -> Tm28 g a
var28 = \ x, tm, var28, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var28 _ _ x

lam28 : {g:_}->{a:_}->{b:_}-> Tm28 (snoc28 g a) b -> Tm28 g (arr28 a b)
lam28 = \ t, tm, var28, lam28, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam28 _ _ _ (t tm var28 lam28 app tt pair fst snd left right split zero suc rec)

app28 : {g:_}->{a:_}->{b:_} -> Tm28 g (arr28 a b) -> Tm28 g a -> Tm28 g b
app28 = \ t, u, tm, var28, lam28, app28, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app28 _ _ _ (t tm var28 lam28 app28 tt pair fst snd left right split zero suc rec)
                (u tm var28 lam28 app28 tt pair fst snd left right split zero suc rec)

tt28 : {g:_} -> Tm28 g Main.top28
tt28 = \ tm, var28, lam28, app28, tt28, pair, fst, snd, left, right, split, zero, suc, rec => tt28 _

pair28 : {g:_}->{a:_}->{b:_} -> Tm28 g a -> Tm28 g b -> Tm28 g (prod28 a b)
pair28 = \ t, u, tm, var28, lam28, app28, tt28, pair28, fst, snd, left, right, split, zero, suc, rec =>
     pair28 _ _ _ (t tm var28 lam28 app28 tt28 pair28 fst snd left right split zero suc rec)
                 (u tm var28 lam28 app28 tt28 pair28 fst snd left right split zero suc rec)

fst28 : {g:_}->{a:_}->{b:_}-> Tm28 g (prod28 a b) -> Tm28 g a
fst28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd, left, right, split, zero, suc, rec =>
     fst28 _ _ _ (t tm var28 lam28 app28 tt28 pair28 fst28 snd left right split zero suc rec)

snd28 : {g:_}->{a:_}->{b:_} -> Tm28 g (prod28 a b) -> Tm28 g b
snd28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left, right, split, zero, suc, rec =>
     snd28 _ _ _ (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left right split zero suc rec)

left28 : {g:_}->{a:_}->{b:_} -> Tm28 g a -> Tm28 g (sum28 a b)
left28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right, split, zero, suc, rec =>
     left28 _ _ _ (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right split zero suc rec)

right28 : {g:_}->{a:_}->{b:_} -> Tm28 g b -> Tm28 g (sum28 a b)
right28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split, zero, suc, rec =>
     right28 _ _ _ (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split zero suc rec)

split28 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm28 g (sum28 a b) -> Tm28 g (arr28 a c) -> Tm28 g (arr28 b c) -> Tm28 g c
split28 = \ t, u, v, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split28, zero, suc, rec =>
     split28 _ _ _ _
          (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero suc rec)
          (u tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero suc rec)
          (v tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero suc rec)

zero28 : {g:_} -> Tm28 g Main.nat28
zero28 = \ tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split28, zero28, suc, rec =>
  zero28 _

suc28 : {g:_} -> Tm28 g Main.nat28 -> Tm28 g Main.nat28
suc28 = \ t, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split28, zero28, suc28, rec =>
   suc28 _ (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero28 suc28 rec)

rec28 : {g:_}->{a:_} -> Tm28 g Main.nat28 -> Tm28 g (arr28 Main.nat28 (arr28 a a)) -> Tm28 g a -> Tm28 g a
rec28 = \ t, u, v, tm, var28, lam28, app28, tt28, pair28, fst28, snd28, left28, right28, split28, zero28, suc28, rec28 =>
     rec28 _ _
       (t tm var28 lam28 app28 tt28 pair28 fst28 snd28 left28 right28 split28 zero28 suc28 rec28)
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
 -> (vz  : (g:_)->(a:_) -> Var29 (snoc29 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var29 g a -> Var29 (snoc29 g b) a)
 -> Var29 g a

vz29 : {g:_}->{a:_} -> Var29 (snoc29 g a) a
vz29 = \ var, vz29, vs => vz29 _ _

vs29 : {g:_}->{b:_}->{a:_} -> Var29 g a -> Var29 (snoc29 g b) a
vs29 = \ x, var, vz29, vs29 => vs29 _ _ _ (x var vz29 vs29)

Tm29 : Con29 -> Ty29-> Type
Tm29 = \ g, a =>
    (Tm29    : Con29 -> Ty29-> Type)
 -> (var   : (g:_)->(a:_)-> Var29 g a -> Tm29 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm29 (snoc29 g a) b -> Tm29 g (arr29 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm29 g (arr29 a b) -> Tm29 g a -> Tm29 g b)
 -> (tt    : (g:_)-> Tm29 g top29)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm29 g a -> Tm29 g b -> Tm29 g (prod29 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm29 g (prod29 a b) -> Tm29 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm29 g (prod29 a b) -> Tm29 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm29 g a -> Tm29 g (sum29 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm29 g b -> Tm29 g (sum29 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm29 g (sum29 a b) -> Tm29 g (arr29 a c) -> Tm29 g (arr29 b c) -> Tm29 g c)
 -> (zero  : (g:_)-> Tm29 g nat29)
 -> (suc   : (g:_)-> Tm29 g nat29 -> Tm29 g nat29)
 -> (rec   : (g:_)->(a:_) -> Tm29 g nat29 -> Tm29 g (arr29 nat29 (arr29 a a)) -> Tm29 g a -> Tm29 g a)
 -> Tm29 g a

var29 : {g:_}->{a:_} -> Var29 g a -> Tm29 g a
var29 = \ x, tm, var29, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var29 _ _ x

lam29 : {g:_}->{a:_}->{b:_}-> Tm29 (snoc29 g a) b -> Tm29 g (arr29 a b)
lam29 = \ t, tm, var29, lam29, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam29 _ _ _ (t tm var29 lam29 app tt pair fst snd left right split zero suc rec)

app29 : {g:_}->{a:_}->{b:_} -> Tm29 g (arr29 a b) -> Tm29 g a -> Tm29 g b
app29 = \ t, u, tm, var29, lam29, app29, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app29 _ _ _ (t tm var29 lam29 app29 tt pair fst snd left right split zero suc rec)
                (u tm var29 lam29 app29 tt pair fst snd left right split zero suc rec)

tt29 : {g:_} -> Tm29 g Main.top29
tt29 = \ tm, var29, lam29, app29, tt29, pair, fst, snd, left, right, split, zero, suc, rec => tt29 _

pair29 : {g:_}->{a:_}->{b:_} -> Tm29 g a -> Tm29 g b -> Tm29 g (prod29 a b)
pair29 = \ t, u, tm, var29, lam29, app29, tt29, pair29, fst, snd, left, right, split, zero, suc, rec =>
     pair29 _ _ _ (t tm var29 lam29 app29 tt29 pair29 fst snd left right split zero suc rec)
                 (u tm var29 lam29 app29 tt29 pair29 fst snd left right split zero suc rec)

fst29 : {g:_}->{a:_}->{b:_}-> Tm29 g (prod29 a b) -> Tm29 g a
fst29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd, left, right, split, zero, suc, rec =>
     fst29 _ _ _ (t tm var29 lam29 app29 tt29 pair29 fst29 snd left right split zero suc rec)

snd29 : {g:_}->{a:_}->{b:_} -> Tm29 g (prod29 a b) -> Tm29 g b
snd29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left, right, split, zero, suc, rec =>
     snd29 _ _ _ (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left right split zero suc rec)

left29 : {g:_}->{a:_}->{b:_} -> Tm29 g a -> Tm29 g (sum29 a b)
left29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right, split, zero, suc, rec =>
     left29 _ _ _ (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right split zero suc rec)

right29 : {g:_}->{a:_}->{b:_} -> Tm29 g b -> Tm29 g (sum29 a b)
right29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split, zero, suc, rec =>
     right29 _ _ _ (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split zero suc rec)

split29 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm29 g (sum29 a b) -> Tm29 g (arr29 a c) -> Tm29 g (arr29 b c) -> Tm29 g c
split29 = \ t, u, v, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split29, zero, suc, rec =>
     split29 _ _ _ _
          (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero suc rec)
          (u tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero suc rec)
          (v tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero suc rec)

zero29 : {g:_} -> Tm29 g Main.nat29
zero29 = \ tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split29, zero29, suc, rec =>
  zero29 _

suc29 : {g:_} -> Tm29 g Main.nat29 -> Tm29 g Main.nat29
suc29 = \ t, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split29, zero29, suc29, rec =>
   suc29 _ (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero29 suc29 rec)

rec29 : {g:_}->{a:_} -> Tm29 g Main.nat29 -> Tm29 g (arr29 Main.nat29 (arr29 a a)) -> Tm29 g a -> Tm29 g a
rec29 = \ t, u, v, tm, var29, lam29, app29, tt29, pair29, fst29, snd29, left29, right29, split29, zero29, suc29, rec29 =>
     rec29 _ _
       (t tm var29 lam29 app29 tt29 pair29 fst29 snd29 left29 right29 split29 zero29 suc29 rec29)
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
 -> (vz  : (g:_)->(a:_) -> Var30 (snoc30 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var30 g a -> Var30 (snoc30 g b) a)
 -> Var30 g a

vz30 : {g:_}->{a:_} -> Var30 (snoc30 g a) a
vz30 = \ var, vz30, vs => vz30 _ _

vs30 : {g:_}->{b:_}->{a:_} -> Var30 g a -> Var30 (snoc30 g b) a
vs30 = \ x, var, vz30, vs30 => vs30 _ _ _ (x var vz30 vs30)

Tm30 : Con30 -> Ty30-> Type
Tm30 = \ g, a =>
    (Tm30    : Con30 -> Ty30-> Type)
 -> (var   : (g:_)->(a:_)-> Var30 g a -> Tm30 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm30 (snoc30 g a) b -> Tm30 g (arr30 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm30 g (arr30 a b) -> Tm30 g a -> Tm30 g b)
 -> (tt    : (g:_)-> Tm30 g top30)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm30 g a -> Tm30 g b -> Tm30 g (prod30 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm30 g (prod30 a b) -> Tm30 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm30 g (prod30 a b) -> Tm30 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm30 g a -> Tm30 g (sum30 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm30 g b -> Tm30 g (sum30 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm30 g (sum30 a b) -> Tm30 g (arr30 a c) -> Tm30 g (arr30 b c) -> Tm30 g c)
 -> (zero  : (g:_)-> Tm30 g nat30)
 -> (suc   : (g:_)-> Tm30 g nat30 -> Tm30 g nat30)
 -> (rec   : (g:_)->(a:_) -> Tm30 g nat30 -> Tm30 g (arr30 nat30 (arr30 a a)) -> Tm30 g a -> Tm30 g a)
 -> Tm30 g a

var30 : {g:_}->{a:_} -> Var30 g a -> Tm30 g a
var30 = \ x, tm, var30, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var30 _ _ x

lam30 : {g:_}->{a:_}->{b:_}-> Tm30 (snoc30 g a) b -> Tm30 g (arr30 a b)
lam30 = \ t, tm, var30, lam30, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam30 _ _ _ (t tm var30 lam30 app tt pair fst snd left right split zero suc rec)

app30 : {g:_}->{a:_}->{b:_} -> Tm30 g (arr30 a b) -> Tm30 g a -> Tm30 g b
app30 = \ t, u, tm, var30, lam30, app30, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app30 _ _ _ (t tm var30 lam30 app30 tt pair fst snd left right split zero suc rec)
                (u tm var30 lam30 app30 tt pair fst snd left right split zero suc rec)

tt30 : {g:_} -> Tm30 g Main.top30
tt30 = \ tm, var30, lam30, app30, tt30, pair, fst, snd, left, right, split, zero, suc, rec => tt30 _

pair30 : {g:_}->{a:_}->{b:_} -> Tm30 g a -> Tm30 g b -> Tm30 g (prod30 a b)
pair30 = \ t, u, tm, var30, lam30, app30, tt30, pair30, fst, snd, left, right, split, zero, suc, rec =>
     pair30 _ _ _ (t tm var30 lam30 app30 tt30 pair30 fst snd left right split zero suc rec)
                 (u tm var30 lam30 app30 tt30 pair30 fst snd left right split zero suc rec)

fst30 : {g:_}->{a:_}->{b:_}-> Tm30 g (prod30 a b) -> Tm30 g a
fst30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd, left, right, split, zero, suc, rec =>
     fst30 _ _ _ (t tm var30 lam30 app30 tt30 pair30 fst30 snd left right split zero suc rec)

snd30 : {g:_}->{a:_}->{b:_} -> Tm30 g (prod30 a b) -> Tm30 g b
snd30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left, right, split, zero, suc, rec =>
     snd30 _ _ _ (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left right split zero suc rec)

left30 : {g:_}->{a:_}->{b:_} -> Tm30 g a -> Tm30 g (sum30 a b)
left30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right, split, zero, suc, rec =>
     left30 _ _ _ (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right split zero suc rec)

right30 : {g:_}->{a:_}->{b:_} -> Tm30 g b -> Tm30 g (sum30 a b)
right30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split, zero, suc, rec =>
     right30 _ _ _ (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split zero suc rec)

split30 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm30 g (sum30 a b) -> Tm30 g (arr30 a c) -> Tm30 g (arr30 b c) -> Tm30 g c
split30 = \ t, u, v, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split30, zero, suc, rec =>
     split30 _ _ _ _
          (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero suc rec)
          (u tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero suc rec)
          (v tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero suc rec)

zero30 : {g:_} -> Tm30 g Main.nat30
zero30 = \ tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split30, zero30, suc, rec =>
  zero30 _

suc30 : {g:_} -> Tm30 g Main.nat30 -> Tm30 g Main.nat30
suc30 = \ t, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split30, zero30, suc30, rec =>
   suc30 _ (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero30 suc30 rec)

rec30 : {g:_}->{a:_} -> Tm30 g Main.nat30 -> Tm30 g (arr30 Main.nat30 (arr30 a a)) -> Tm30 g a -> Tm30 g a
rec30 = \ t, u, v, tm, var30, lam30, app30, tt30, pair30, fst30, snd30, left30, right30, split30, zero30, suc30, rec30 =>
     rec30 _ _
       (t tm var30 lam30 app30 tt30 pair30 fst30 snd30 left30 right30 split30 zero30 suc30 rec30)
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
 -> (vz  : (g:_)->(a:_) -> Var31 (snoc31 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var31 g a -> Var31 (snoc31 g b) a)
 -> Var31 g a

vz31 : {g:_}->{a:_} -> Var31 (snoc31 g a) a
vz31 = \ var, vz31, vs => vz31 _ _

vs31 : {g:_}->{b:_}->{a:_} -> Var31 g a -> Var31 (snoc31 g b) a
vs31 = \ x, var, vz31, vs31 => vs31 _ _ _ (x var vz31 vs31)

Tm31 : Con31 -> Ty31-> Type
Tm31 = \ g, a =>
    (Tm31    : Con31 -> Ty31-> Type)
 -> (var   : (g:_)->(a:_)-> Var31 g a -> Tm31 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm31 (snoc31 g a) b -> Tm31 g (arr31 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm31 g (arr31 a b) -> Tm31 g a -> Tm31 g b)
 -> (tt    : (g:_)-> Tm31 g top31)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm31 g a -> Tm31 g b -> Tm31 g (prod31 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm31 g (prod31 a b) -> Tm31 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm31 g (prod31 a b) -> Tm31 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm31 g a -> Tm31 g (sum31 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm31 g b -> Tm31 g (sum31 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm31 g (sum31 a b) -> Tm31 g (arr31 a c) -> Tm31 g (arr31 b c) -> Tm31 g c)
 -> (zero  : (g:_)-> Tm31 g nat31)
 -> (suc   : (g:_)-> Tm31 g nat31 -> Tm31 g nat31)
 -> (rec   : (g:_)->(a:_) -> Tm31 g nat31 -> Tm31 g (arr31 nat31 (arr31 a a)) -> Tm31 g a -> Tm31 g a)
 -> Tm31 g a

var31 : {g:_}->{a:_} -> Var31 g a -> Tm31 g a
var31 = \ x, tm, var31, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var31 _ _ x

lam31 : {g:_}->{a:_}->{b:_}-> Tm31 (snoc31 g a) b -> Tm31 g (arr31 a b)
lam31 = \ t, tm, var31, lam31, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam31 _ _ _ (t tm var31 lam31 app tt pair fst snd left right split zero suc rec)

app31 : {g:_}->{a:_}->{b:_} -> Tm31 g (arr31 a b) -> Tm31 g a -> Tm31 g b
app31 = \ t, u, tm, var31, lam31, app31, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app31 _ _ _ (t tm var31 lam31 app31 tt pair fst snd left right split zero suc rec)
                (u tm var31 lam31 app31 tt pair fst snd left right split zero suc rec)

tt31 : {g:_} -> Tm31 g Main.top31
tt31 = \ tm, var31, lam31, app31, tt31, pair, fst, snd, left, right, split, zero, suc, rec => tt31 _

pair31 : {g:_}->{a:_}->{b:_} -> Tm31 g a -> Tm31 g b -> Tm31 g (prod31 a b)
pair31 = \ t, u, tm, var31, lam31, app31, tt31, pair31, fst, snd, left, right, split, zero, suc, rec =>
     pair31 _ _ _ (t tm var31 lam31 app31 tt31 pair31 fst snd left right split zero suc rec)
                 (u tm var31 lam31 app31 tt31 pair31 fst snd left right split zero suc rec)

fst31 : {g:_}->{a:_}->{b:_}-> Tm31 g (prod31 a b) -> Tm31 g a
fst31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd, left, right, split, zero, suc, rec =>
     fst31 _ _ _ (t tm var31 lam31 app31 tt31 pair31 fst31 snd left right split zero suc rec)

snd31 : {g:_}->{a:_}->{b:_} -> Tm31 g (prod31 a b) -> Tm31 g b
snd31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left, right, split, zero, suc, rec =>
     snd31 _ _ _ (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left right split zero suc rec)

left31 : {g:_}->{a:_}->{b:_} -> Tm31 g a -> Tm31 g (sum31 a b)
left31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right, split, zero, suc, rec =>
     left31 _ _ _ (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right split zero suc rec)

right31 : {g:_}->{a:_}->{b:_} -> Tm31 g b -> Tm31 g (sum31 a b)
right31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split, zero, suc, rec =>
     right31 _ _ _ (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split zero suc rec)

split31 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm31 g (sum31 a b) -> Tm31 g (arr31 a c) -> Tm31 g (arr31 b c) -> Tm31 g c
split31 = \ t, u, v, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split31, zero, suc, rec =>
     split31 _ _ _ _
          (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero suc rec)
          (u tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero suc rec)
          (v tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero suc rec)

zero31 : {g:_} -> Tm31 g Main.nat31
zero31 = \ tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split31, zero31, suc, rec =>
  zero31 _

suc31 : {g:_} -> Tm31 g Main.nat31 -> Tm31 g Main.nat31
suc31 = \ t, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split31, zero31, suc31, rec =>
   suc31 _ (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero31 suc31 rec)

rec31 : {g:_}->{a:_} -> Tm31 g Main.nat31 -> Tm31 g (arr31 Main.nat31 (arr31 a a)) -> Tm31 g a -> Tm31 g a
rec31 = \ t, u, v, tm, var31, lam31, app31, tt31, pair31, fst31, snd31, left31, right31, split31, zero31, suc31, rec31 =>
     rec31 _ _
       (t tm var31 lam31 app31 tt31 pair31 fst31 snd31 left31 right31 split31 zero31 suc31 rec31)
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
 -> (vz  : (g:_)->(a:_) -> Var32 (snoc32 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var32 g a -> Var32 (snoc32 g b) a)
 -> Var32 g a

vz32 : {g:_}->{a:_} -> Var32 (snoc32 g a) a
vz32 = \ var, vz32, vs => vz32 _ _

vs32 : {g:_}->{b:_}->{a:_} -> Var32 g a -> Var32 (snoc32 g b) a
vs32 = \ x, var, vz32, vs32 => vs32 _ _ _ (x var vz32 vs32)

Tm32 : Con32 -> Ty32-> Type
Tm32 = \ g, a =>
    (Tm32    : Con32 -> Ty32-> Type)
 -> (var   : (g:_)->(a:_)-> Var32 g a -> Tm32 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm32 (snoc32 g a) b -> Tm32 g (arr32 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm32 g (arr32 a b) -> Tm32 g a -> Tm32 g b)
 -> (tt    : (g:_)-> Tm32 g top32)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm32 g a -> Tm32 g b -> Tm32 g (prod32 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm32 g (prod32 a b) -> Tm32 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm32 g (prod32 a b) -> Tm32 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm32 g a -> Tm32 g (sum32 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm32 g b -> Tm32 g (sum32 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm32 g (sum32 a b) -> Tm32 g (arr32 a c) -> Tm32 g (arr32 b c) -> Tm32 g c)
 -> (zero  : (g:_)-> Tm32 g nat32)
 -> (suc   : (g:_)-> Tm32 g nat32 -> Tm32 g nat32)
 -> (rec   : (g:_)->(a:_) -> Tm32 g nat32 -> Tm32 g (arr32 nat32 (arr32 a a)) -> Tm32 g a -> Tm32 g a)
 -> Tm32 g a

var32 : {g:_}->{a:_} -> Var32 g a -> Tm32 g a
var32 = \ x, tm, var32, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var32 _ _ x

lam32 : {g:_}->{a:_}->{b:_}-> Tm32 (snoc32 g a) b -> Tm32 g (arr32 a b)
lam32 = \ t, tm, var32, lam32, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam32 _ _ _ (t tm var32 lam32 app tt pair fst snd left right split zero suc rec)

app32 : {g:_}->{a:_}->{b:_} -> Tm32 g (arr32 a b) -> Tm32 g a -> Tm32 g b
app32 = \ t, u, tm, var32, lam32, app32, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app32 _ _ _ (t tm var32 lam32 app32 tt pair fst snd left right split zero suc rec)
                (u tm var32 lam32 app32 tt pair fst snd left right split zero suc rec)

tt32 : {g:_} -> Tm32 g Main.top32
tt32 = \ tm, var32, lam32, app32, tt32, pair, fst, snd, left, right, split, zero, suc, rec => tt32 _

pair32 : {g:_}->{a:_}->{b:_} -> Tm32 g a -> Tm32 g b -> Tm32 g (prod32 a b)
pair32 = \ t, u, tm, var32, lam32, app32, tt32, pair32, fst, snd, left, right, split, zero, suc, rec =>
     pair32 _ _ _ (t tm var32 lam32 app32 tt32 pair32 fst snd left right split zero suc rec)
                 (u tm var32 lam32 app32 tt32 pair32 fst snd left right split zero suc rec)

fst32 : {g:_}->{a:_}->{b:_}-> Tm32 g (prod32 a b) -> Tm32 g a
fst32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd, left, right, split, zero, suc, rec =>
     fst32 _ _ _ (t tm var32 lam32 app32 tt32 pair32 fst32 snd left right split zero suc rec)

snd32 : {g:_}->{a:_}->{b:_} -> Tm32 g (prod32 a b) -> Tm32 g b
snd32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left, right, split, zero, suc, rec =>
     snd32 _ _ _ (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left right split zero suc rec)

left32 : {g:_}->{a:_}->{b:_} -> Tm32 g a -> Tm32 g (sum32 a b)
left32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right, split, zero, suc, rec =>
     left32 _ _ _ (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right split zero suc rec)

right32 : {g:_}->{a:_}->{b:_} -> Tm32 g b -> Tm32 g (sum32 a b)
right32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split, zero, suc, rec =>
     right32 _ _ _ (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split zero suc rec)

split32 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm32 g (sum32 a b) -> Tm32 g (arr32 a c) -> Tm32 g (arr32 b c) -> Tm32 g c
split32 = \ t, u, v, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split32, zero, suc, rec =>
     split32 _ _ _ _
          (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero suc rec)
          (u tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero suc rec)
          (v tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero suc rec)

zero32 : {g:_} -> Tm32 g Main.nat32
zero32 = \ tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split32, zero32, suc, rec =>
  zero32 _

suc32 : {g:_} -> Tm32 g Main.nat32 -> Tm32 g Main.nat32
suc32 = \ t, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split32, zero32, suc32, rec =>
   suc32 _ (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero32 suc32 rec)

rec32 : {g:_}->{a:_} -> Tm32 g Main.nat32 -> Tm32 g (arr32 Main.nat32 (arr32 a a)) -> Tm32 g a -> Tm32 g a
rec32 = \ t, u, v, tm, var32, lam32, app32, tt32, pair32, fst32, snd32, left32, right32, split32, zero32, suc32, rec32 =>
     rec32 _ _
       (t tm var32 lam32 app32 tt32 pair32 fst32 snd32 left32 right32 split32 zero32 suc32 rec32)
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
 -> (vz  : (g:_)->(a:_) -> Var33 (snoc33 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var33 g a -> Var33 (snoc33 g b) a)
 -> Var33 g a

vz33 : {g:_}->{a:_} -> Var33 (snoc33 g a) a
vz33 = \ var, vz33, vs => vz33 _ _

vs33 : {g:_}->{b:_}->{a:_} -> Var33 g a -> Var33 (snoc33 g b) a
vs33 = \ x, var, vz33, vs33 => vs33 _ _ _ (x var vz33 vs33)

Tm33 : Con33 -> Ty33-> Type
Tm33 = \ g, a =>
    (Tm33    : Con33 -> Ty33-> Type)
 -> (var   : (g:_)->(a:_)-> Var33 g a -> Tm33 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm33 (snoc33 g a) b -> Tm33 g (arr33 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm33 g (arr33 a b) -> Tm33 g a -> Tm33 g b)
 -> (tt    : (g:_)-> Tm33 g top33)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm33 g a -> Tm33 g b -> Tm33 g (prod33 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm33 g (prod33 a b) -> Tm33 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm33 g (prod33 a b) -> Tm33 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm33 g a -> Tm33 g (sum33 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm33 g b -> Tm33 g (sum33 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm33 g (sum33 a b) -> Tm33 g (arr33 a c) -> Tm33 g (arr33 b c) -> Tm33 g c)
 -> (zero  : (g:_)-> Tm33 g nat33)
 -> (suc   : (g:_)-> Tm33 g nat33 -> Tm33 g nat33)
 -> (rec   : (g:_)->(a:_) -> Tm33 g nat33 -> Tm33 g (arr33 nat33 (arr33 a a)) -> Tm33 g a -> Tm33 g a)
 -> Tm33 g a

var33 : {g:_}->{a:_} -> Var33 g a -> Tm33 g a
var33 = \ x, tm, var33, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var33 _ _ x

lam33 : {g:_}->{a:_}->{b:_}-> Tm33 (snoc33 g a) b -> Tm33 g (arr33 a b)
lam33 = \ t, tm, var33, lam33, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam33 _ _ _ (t tm var33 lam33 app tt pair fst snd left right split zero suc rec)

app33 : {g:_}->{a:_}->{b:_} -> Tm33 g (arr33 a b) -> Tm33 g a -> Tm33 g b
app33 = \ t, u, tm, var33, lam33, app33, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app33 _ _ _ (t tm var33 lam33 app33 tt pair fst snd left right split zero suc rec)
                (u tm var33 lam33 app33 tt pair fst snd left right split zero suc rec)

tt33 : {g:_} -> Tm33 g Main.top33
tt33 = \ tm, var33, lam33, app33, tt33, pair, fst, snd, left, right, split, zero, suc, rec => tt33 _

pair33 : {g:_}->{a:_}->{b:_} -> Tm33 g a -> Tm33 g b -> Tm33 g (prod33 a b)
pair33 = \ t, u, tm, var33, lam33, app33, tt33, pair33, fst, snd, left, right, split, zero, suc, rec =>
     pair33 _ _ _ (t tm var33 lam33 app33 tt33 pair33 fst snd left right split zero suc rec)
                 (u tm var33 lam33 app33 tt33 pair33 fst snd left right split zero suc rec)

fst33 : {g:_}->{a:_}->{b:_}-> Tm33 g (prod33 a b) -> Tm33 g a
fst33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd, left, right, split, zero, suc, rec =>
     fst33 _ _ _ (t tm var33 lam33 app33 tt33 pair33 fst33 snd left right split zero suc rec)

snd33 : {g:_}->{a:_}->{b:_} -> Tm33 g (prod33 a b) -> Tm33 g b
snd33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left, right, split, zero, suc, rec =>
     snd33 _ _ _ (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left right split zero suc rec)

left33 : {g:_}->{a:_}->{b:_} -> Tm33 g a -> Tm33 g (sum33 a b)
left33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right, split, zero, suc, rec =>
     left33 _ _ _ (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right split zero suc rec)

right33 : {g:_}->{a:_}->{b:_} -> Tm33 g b -> Tm33 g (sum33 a b)
right33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split, zero, suc, rec =>
     right33 _ _ _ (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split zero suc rec)

split33 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm33 g (sum33 a b) -> Tm33 g (arr33 a c) -> Tm33 g (arr33 b c) -> Tm33 g c
split33 = \ t, u, v, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split33, zero, suc, rec =>
     split33 _ _ _ _
          (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero suc rec)
          (u tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero suc rec)
          (v tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero suc rec)

zero33 : {g:_} -> Tm33 g Main.nat33
zero33 = \ tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split33, zero33, suc, rec =>
  zero33 _

suc33 : {g:_} -> Tm33 g Main.nat33 -> Tm33 g Main.nat33
suc33 = \ t, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split33, zero33, suc33, rec =>
   suc33 _ (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero33 suc33 rec)

rec33 : {g:_}->{a:_} -> Tm33 g Main.nat33 -> Tm33 g (arr33 Main.nat33 (arr33 a a)) -> Tm33 g a -> Tm33 g a
rec33 = \ t, u, v, tm, var33, lam33, app33, tt33, pair33, fst33, snd33, left33, right33, split33, zero33, suc33, rec33 =>
     rec33 _ _
       (t tm var33 lam33 app33 tt33 pair33 fst33 snd33 left33 right33 split33 zero33 suc33 rec33)
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
 -> (vz  : (g:_)->(a:_) -> Var34 (snoc34 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var34 g a -> Var34 (snoc34 g b) a)
 -> Var34 g a

vz34 : {g:_}->{a:_} -> Var34 (snoc34 g a) a
vz34 = \ var, vz34, vs => vz34 _ _

vs34 : {g:_}->{b:_}->{a:_} -> Var34 g a -> Var34 (snoc34 g b) a
vs34 = \ x, var, vz34, vs34 => vs34 _ _ _ (x var vz34 vs34)

Tm34 : Con34 -> Ty34-> Type
Tm34 = \ g, a =>
    (Tm34    : Con34 -> Ty34-> Type)
 -> (var   : (g:_)->(a:_)-> Var34 g a -> Tm34 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm34 (snoc34 g a) b -> Tm34 g (arr34 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm34 g (arr34 a b) -> Tm34 g a -> Tm34 g b)
 -> (tt    : (g:_)-> Tm34 g top34)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm34 g a -> Tm34 g b -> Tm34 g (prod34 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm34 g (prod34 a b) -> Tm34 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm34 g (prod34 a b) -> Tm34 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm34 g a -> Tm34 g (sum34 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm34 g b -> Tm34 g (sum34 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm34 g (sum34 a b) -> Tm34 g (arr34 a c) -> Tm34 g (arr34 b c) -> Tm34 g c)
 -> (zero  : (g:_)-> Tm34 g nat34)
 -> (suc   : (g:_)-> Tm34 g nat34 -> Tm34 g nat34)
 -> (rec   : (g:_)->(a:_) -> Tm34 g nat34 -> Tm34 g (arr34 nat34 (arr34 a a)) -> Tm34 g a -> Tm34 g a)
 -> Tm34 g a

var34 : {g:_}->{a:_} -> Var34 g a -> Tm34 g a
var34 = \ x, tm, var34, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var34 _ _ x

lam34 : {g:_}->{a:_}->{b:_}-> Tm34 (snoc34 g a) b -> Tm34 g (arr34 a b)
lam34 = \ t, tm, var34, lam34, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam34 _ _ _ (t tm var34 lam34 app tt pair fst snd left right split zero suc rec)

app34 : {g:_}->{a:_}->{b:_} -> Tm34 g (arr34 a b) -> Tm34 g a -> Tm34 g b
app34 = \ t, u, tm, var34, lam34, app34, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app34 _ _ _ (t tm var34 lam34 app34 tt pair fst snd left right split zero suc rec)
                (u tm var34 lam34 app34 tt pair fst snd left right split zero suc rec)

tt34 : {g:_} -> Tm34 g Main.top34
tt34 = \ tm, var34, lam34, app34, tt34, pair, fst, snd, left, right, split, zero, suc, rec => tt34 _

pair34 : {g:_}->{a:_}->{b:_} -> Tm34 g a -> Tm34 g b -> Tm34 g (prod34 a b)
pair34 = \ t, u, tm, var34, lam34, app34, tt34, pair34, fst, snd, left, right, split, zero, suc, rec =>
     pair34 _ _ _ (t tm var34 lam34 app34 tt34 pair34 fst snd left right split zero suc rec)
                 (u tm var34 lam34 app34 tt34 pair34 fst snd left right split zero suc rec)

fst34 : {g:_}->{a:_}->{b:_}-> Tm34 g (prod34 a b) -> Tm34 g a
fst34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd, left, right, split, zero, suc, rec =>
     fst34 _ _ _ (t tm var34 lam34 app34 tt34 pair34 fst34 snd left right split zero suc rec)

snd34 : {g:_}->{a:_}->{b:_} -> Tm34 g (prod34 a b) -> Tm34 g b
snd34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left, right, split, zero, suc, rec =>
     snd34 _ _ _ (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left right split zero suc rec)

left34 : {g:_}->{a:_}->{b:_} -> Tm34 g a -> Tm34 g (sum34 a b)
left34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right, split, zero, suc, rec =>
     left34 _ _ _ (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right split zero suc rec)

right34 : {g:_}->{a:_}->{b:_} -> Tm34 g b -> Tm34 g (sum34 a b)
right34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split, zero, suc, rec =>
     right34 _ _ _ (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split zero suc rec)

split34 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm34 g (sum34 a b) -> Tm34 g (arr34 a c) -> Tm34 g (arr34 b c) -> Tm34 g c
split34 = \ t, u, v, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split34, zero, suc, rec =>
     split34 _ _ _ _
          (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero suc rec)
          (u tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero suc rec)
          (v tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero suc rec)

zero34 : {g:_} -> Tm34 g Main.nat34
zero34 = \ tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split34, zero34, suc, rec =>
  zero34 _

suc34 : {g:_} -> Tm34 g Main.nat34 -> Tm34 g Main.nat34
suc34 = \ t, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split34, zero34, suc34, rec =>
   suc34 _ (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero34 suc34 rec)

rec34 : {g:_}->{a:_} -> Tm34 g Main.nat34 -> Tm34 g (arr34 Main.nat34 (arr34 a a)) -> Tm34 g a -> Tm34 g a
rec34 = \ t, u, v, tm, var34, lam34, app34, tt34, pair34, fst34, snd34, left34, right34, split34, zero34, suc34, rec34 =>
     rec34 _ _
       (t tm var34 lam34 app34 tt34 pair34 fst34 snd34 left34 right34 split34 zero34 suc34 rec34)
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
 -> (vz  : (g:_)->(a:_) -> Var35 (snoc35 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var35 g a -> Var35 (snoc35 g b) a)
 -> Var35 g a

vz35 : {g:_}->{a:_} -> Var35 (snoc35 g a) a
vz35 = \ var, vz35, vs => vz35 _ _

vs35 : {g:_}->{b:_}->{a:_} -> Var35 g a -> Var35 (snoc35 g b) a
vs35 = \ x, var, vz35, vs35 => vs35 _ _ _ (x var vz35 vs35)

Tm35 : Con35 -> Ty35-> Type
Tm35 = \ g, a =>
    (Tm35    : Con35 -> Ty35-> Type)
 -> (var   : (g:_)->(a:_)-> Var35 g a -> Tm35 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm35 (snoc35 g a) b -> Tm35 g (arr35 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm35 g (arr35 a b) -> Tm35 g a -> Tm35 g b)
 -> (tt    : (g:_)-> Tm35 g top35)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm35 g a -> Tm35 g b -> Tm35 g (prod35 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm35 g (prod35 a b) -> Tm35 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm35 g (prod35 a b) -> Tm35 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm35 g a -> Tm35 g (sum35 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm35 g b -> Tm35 g (sum35 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm35 g (sum35 a b) -> Tm35 g (arr35 a c) -> Tm35 g (arr35 b c) -> Tm35 g c)
 -> (zero  : (g:_)-> Tm35 g nat35)
 -> (suc   : (g:_)-> Tm35 g nat35 -> Tm35 g nat35)
 -> (rec   : (g:_)->(a:_) -> Tm35 g nat35 -> Tm35 g (arr35 nat35 (arr35 a a)) -> Tm35 g a -> Tm35 g a)
 -> Tm35 g a

var35 : {g:_}->{a:_} -> Var35 g a -> Tm35 g a
var35 = \ x, tm, var35, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var35 _ _ x

lam35 : {g:_}->{a:_}->{b:_}-> Tm35 (snoc35 g a) b -> Tm35 g (arr35 a b)
lam35 = \ t, tm, var35, lam35, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam35 _ _ _ (t tm var35 lam35 app tt pair fst snd left right split zero suc rec)

app35 : {g:_}->{a:_}->{b:_} -> Tm35 g (arr35 a b) -> Tm35 g a -> Tm35 g b
app35 = \ t, u, tm, var35, lam35, app35, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app35 _ _ _ (t tm var35 lam35 app35 tt pair fst snd left right split zero suc rec)
                (u tm var35 lam35 app35 tt pair fst snd left right split zero suc rec)

tt35 : {g:_} -> Tm35 g Main.top35
tt35 = \ tm, var35, lam35, app35, tt35, pair, fst, snd, left, right, split, zero, suc, rec => tt35 _

pair35 : {g:_}->{a:_}->{b:_} -> Tm35 g a -> Tm35 g b -> Tm35 g (prod35 a b)
pair35 = \ t, u, tm, var35, lam35, app35, tt35, pair35, fst, snd, left, right, split, zero, suc, rec =>
     pair35 _ _ _ (t tm var35 lam35 app35 tt35 pair35 fst snd left right split zero suc rec)
                 (u tm var35 lam35 app35 tt35 pair35 fst snd left right split zero suc rec)

fst35 : {g:_}->{a:_}->{b:_}-> Tm35 g (prod35 a b) -> Tm35 g a
fst35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd, left, right, split, zero, suc, rec =>
     fst35 _ _ _ (t tm var35 lam35 app35 tt35 pair35 fst35 snd left right split zero suc rec)

snd35 : {g:_}->{a:_}->{b:_} -> Tm35 g (prod35 a b) -> Tm35 g b
snd35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left, right, split, zero, suc, rec =>
     snd35 _ _ _ (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left right split zero suc rec)

left35 : {g:_}->{a:_}->{b:_} -> Tm35 g a -> Tm35 g (sum35 a b)
left35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right, split, zero, suc, rec =>
     left35 _ _ _ (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right split zero suc rec)

right35 : {g:_}->{a:_}->{b:_} -> Tm35 g b -> Tm35 g (sum35 a b)
right35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split, zero, suc, rec =>
     right35 _ _ _ (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split zero suc rec)

split35 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm35 g (sum35 a b) -> Tm35 g (arr35 a c) -> Tm35 g (arr35 b c) -> Tm35 g c
split35 = \ t, u, v, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split35, zero, suc, rec =>
     split35 _ _ _ _
          (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero suc rec)
          (u tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero suc rec)
          (v tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero suc rec)

zero35 : {g:_} -> Tm35 g Main.nat35
zero35 = \ tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split35, zero35, suc, rec =>
  zero35 _

suc35 : {g:_} -> Tm35 g Main.nat35 -> Tm35 g Main.nat35
suc35 = \ t, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split35, zero35, suc35, rec =>
   suc35 _ (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero35 suc35 rec)

rec35 : {g:_}->{a:_} -> Tm35 g Main.nat35 -> Tm35 g (arr35 Main.nat35 (arr35 a a)) -> Tm35 g a -> Tm35 g a
rec35 = \ t, u, v, tm, var35, lam35, app35, tt35, pair35, fst35, snd35, left35, right35, split35, zero35, suc35, rec35 =>
     rec35 _ _
       (t tm var35 lam35 app35 tt35 pair35 fst35 snd35 left35 right35 split35 zero35 suc35 rec35)
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
 -> (vz  : (g:_)->(a:_) -> Var36 (snoc36 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var36 g a -> Var36 (snoc36 g b) a)
 -> Var36 g a

vz36 : {g:_}->{a:_} -> Var36 (snoc36 g a) a
vz36 = \ var, vz36, vs => vz36 _ _

vs36 : {g:_}->{b:_}->{a:_} -> Var36 g a -> Var36 (snoc36 g b) a
vs36 = \ x, var, vz36, vs36 => vs36 _ _ _ (x var vz36 vs36)

Tm36 : Con36 -> Ty36-> Type
Tm36 = \ g, a =>
    (Tm36    : Con36 -> Ty36-> Type)
 -> (var   : (g:_)->(a:_)-> Var36 g a -> Tm36 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm36 (snoc36 g a) b -> Tm36 g (arr36 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm36 g (arr36 a b) -> Tm36 g a -> Tm36 g b)
 -> (tt    : (g:_)-> Tm36 g top36)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm36 g a -> Tm36 g b -> Tm36 g (prod36 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm36 g (prod36 a b) -> Tm36 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm36 g (prod36 a b) -> Tm36 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm36 g a -> Tm36 g (sum36 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm36 g b -> Tm36 g (sum36 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm36 g (sum36 a b) -> Tm36 g (arr36 a c) -> Tm36 g (arr36 b c) -> Tm36 g c)
 -> (zero  : (g:_)-> Tm36 g nat36)
 -> (suc   : (g:_)-> Tm36 g nat36 -> Tm36 g nat36)
 -> (rec   : (g:_)->(a:_) -> Tm36 g nat36 -> Tm36 g (arr36 nat36 (arr36 a a)) -> Tm36 g a -> Tm36 g a)
 -> Tm36 g a

var36 : {g:_}->{a:_} -> Var36 g a -> Tm36 g a
var36 = \ x, tm, var36, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var36 _ _ x

lam36 : {g:_}->{a:_}->{b:_}-> Tm36 (snoc36 g a) b -> Tm36 g (arr36 a b)
lam36 = \ t, tm, var36, lam36, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam36 _ _ _ (t tm var36 lam36 app tt pair fst snd left right split zero suc rec)

app36 : {g:_}->{a:_}->{b:_} -> Tm36 g (arr36 a b) -> Tm36 g a -> Tm36 g b
app36 = \ t, u, tm, var36, lam36, app36, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app36 _ _ _ (t tm var36 lam36 app36 tt pair fst snd left right split zero suc rec)
                (u tm var36 lam36 app36 tt pair fst snd left right split zero suc rec)

tt36 : {g:_} -> Tm36 g Main.top36
tt36 = \ tm, var36, lam36, app36, tt36, pair, fst, snd, left, right, split, zero, suc, rec => tt36 _

pair36 : {g:_}->{a:_}->{b:_} -> Tm36 g a -> Tm36 g b -> Tm36 g (prod36 a b)
pair36 = \ t, u, tm, var36, lam36, app36, tt36, pair36, fst, snd, left, right, split, zero, suc, rec =>
     pair36 _ _ _ (t tm var36 lam36 app36 tt36 pair36 fst snd left right split zero suc rec)
                 (u tm var36 lam36 app36 tt36 pair36 fst snd left right split zero suc rec)

fst36 : {g:_}->{a:_}->{b:_}-> Tm36 g (prod36 a b) -> Tm36 g a
fst36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd, left, right, split, zero, suc, rec =>
     fst36 _ _ _ (t tm var36 lam36 app36 tt36 pair36 fst36 snd left right split zero suc rec)

snd36 : {g:_}->{a:_}->{b:_} -> Tm36 g (prod36 a b) -> Tm36 g b
snd36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left, right, split, zero, suc, rec =>
     snd36 _ _ _ (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left right split zero suc rec)

left36 : {g:_}->{a:_}->{b:_} -> Tm36 g a -> Tm36 g (sum36 a b)
left36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right, split, zero, suc, rec =>
     left36 _ _ _ (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right split zero suc rec)

right36 : {g:_}->{a:_}->{b:_} -> Tm36 g b -> Tm36 g (sum36 a b)
right36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split, zero, suc, rec =>
     right36 _ _ _ (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split zero suc rec)

split36 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm36 g (sum36 a b) -> Tm36 g (arr36 a c) -> Tm36 g (arr36 b c) -> Tm36 g c
split36 = \ t, u, v, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split36, zero, suc, rec =>
     split36 _ _ _ _
          (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero suc rec)
          (u tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero suc rec)
          (v tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero suc rec)

zero36 : {g:_} -> Tm36 g Main.nat36
zero36 = \ tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split36, zero36, suc, rec =>
  zero36 _

suc36 : {g:_} -> Tm36 g Main.nat36 -> Tm36 g Main.nat36
suc36 = \ t, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split36, zero36, suc36, rec =>
   suc36 _ (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero36 suc36 rec)

rec36 : {g:_}->{a:_} -> Tm36 g Main.nat36 -> Tm36 g (arr36 Main.nat36 (arr36 a a)) -> Tm36 g a -> Tm36 g a
rec36 = \ t, u, v, tm, var36, lam36, app36, tt36, pair36, fst36, snd36, left36, right36, split36, zero36, suc36, rec36 =>
     rec36 _ _
       (t tm var36 lam36 app36 tt36 pair36 fst36 snd36 left36 right36 split36 zero36 suc36 rec36)
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
 -> (vz  : (g:_)->(a:_) -> Var37 (snoc37 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var37 g a -> Var37 (snoc37 g b) a)
 -> Var37 g a

vz37 : {g:_}->{a:_} -> Var37 (snoc37 g a) a
vz37 = \ var, vz37, vs => vz37 _ _

vs37 : {g:_}->{b:_}->{a:_} -> Var37 g a -> Var37 (snoc37 g b) a
vs37 = \ x, var, vz37, vs37 => vs37 _ _ _ (x var vz37 vs37)

Tm37 : Con37 -> Ty37-> Type
Tm37 = \ g, a =>
    (Tm37    : Con37 -> Ty37-> Type)
 -> (var   : (g:_)->(a:_)-> Var37 g a -> Tm37 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm37 (snoc37 g a) b -> Tm37 g (arr37 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm37 g (arr37 a b) -> Tm37 g a -> Tm37 g b)
 -> (tt    : (g:_)-> Tm37 g top37)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm37 g a -> Tm37 g b -> Tm37 g (prod37 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm37 g (prod37 a b) -> Tm37 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm37 g (prod37 a b) -> Tm37 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm37 g a -> Tm37 g (sum37 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm37 g b -> Tm37 g (sum37 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm37 g (sum37 a b) -> Tm37 g (arr37 a c) -> Tm37 g (arr37 b c) -> Tm37 g c)
 -> (zero  : (g:_)-> Tm37 g nat37)
 -> (suc   : (g:_)-> Tm37 g nat37 -> Tm37 g nat37)
 -> (rec   : (g:_)->(a:_) -> Tm37 g nat37 -> Tm37 g (arr37 nat37 (arr37 a a)) -> Tm37 g a -> Tm37 g a)
 -> Tm37 g a

var37 : {g:_}->{a:_} -> Var37 g a -> Tm37 g a
var37 = \ x, tm, var37, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var37 _ _ x

lam37 : {g:_}->{a:_}->{b:_}-> Tm37 (snoc37 g a) b -> Tm37 g (arr37 a b)
lam37 = \ t, tm, var37, lam37, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam37 _ _ _ (t tm var37 lam37 app tt pair fst snd left right split zero suc rec)

app37 : {g:_}->{a:_}->{b:_} -> Tm37 g (arr37 a b) -> Tm37 g a -> Tm37 g b
app37 = \ t, u, tm, var37, lam37, app37, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app37 _ _ _ (t tm var37 lam37 app37 tt pair fst snd left right split zero suc rec)
                (u tm var37 lam37 app37 tt pair fst snd left right split zero suc rec)

tt37 : {g:_} -> Tm37 g Main.top37
tt37 = \ tm, var37, lam37, app37, tt37, pair, fst, snd, left, right, split, zero, suc, rec => tt37 _

pair37 : {g:_}->{a:_}->{b:_} -> Tm37 g a -> Tm37 g b -> Tm37 g (prod37 a b)
pair37 = \ t, u, tm, var37, lam37, app37, tt37, pair37, fst, snd, left, right, split, zero, suc, rec =>
     pair37 _ _ _ (t tm var37 lam37 app37 tt37 pair37 fst snd left right split zero suc rec)
                 (u tm var37 lam37 app37 tt37 pair37 fst snd left right split zero suc rec)

fst37 : {g:_}->{a:_}->{b:_}-> Tm37 g (prod37 a b) -> Tm37 g a
fst37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd, left, right, split, zero, suc, rec =>
     fst37 _ _ _ (t tm var37 lam37 app37 tt37 pair37 fst37 snd left right split zero suc rec)

snd37 : {g:_}->{a:_}->{b:_} -> Tm37 g (prod37 a b) -> Tm37 g b
snd37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left, right, split, zero, suc, rec =>
     snd37 _ _ _ (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left right split zero suc rec)

left37 : {g:_}->{a:_}->{b:_} -> Tm37 g a -> Tm37 g (sum37 a b)
left37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right, split, zero, suc, rec =>
     left37 _ _ _ (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right split zero suc rec)

right37 : {g:_}->{a:_}->{b:_} -> Tm37 g b -> Tm37 g (sum37 a b)
right37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split, zero, suc, rec =>
     right37 _ _ _ (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split zero suc rec)

split37 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm37 g (sum37 a b) -> Tm37 g (arr37 a c) -> Tm37 g (arr37 b c) -> Tm37 g c
split37 = \ t, u, v, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split37, zero, suc, rec =>
     split37 _ _ _ _
          (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero suc rec)
          (u tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero suc rec)
          (v tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero suc rec)

zero37 : {g:_} -> Tm37 g Main.nat37
zero37 = \ tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split37, zero37, suc, rec =>
  zero37 _

suc37 : {g:_} -> Tm37 g Main.nat37 -> Tm37 g Main.nat37
suc37 = \ t, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split37, zero37, suc37, rec =>
   suc37 _ (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero37 suc37 rec)

rec37 : {g:_}->{a:_} -> Tm37 g Main.nat37 -> Tm37 g (arr37 Main.nat37 (arr37 a a)) -> Tm37 g a -> Tm37 g a
rec37 = \ t, u, v, tm, var37, lam37, app37, tt37, pair37, fst37, snd37, left37, right37, split37, zero37, suc37, rec37 =>
     rec37 _ _
       (t tm var37 lam37 app37 tt37 pair37 fst37 snd37 left37 right37 split37 zero37 suc37 rec37)
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
 -> (vz  : (g:_)->(a:_) -> Var38 (snoc38 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var38 g a -> Var38 (snoc38 g b) a)
 -> Var38 g a

vz38 : {g:_}->{a:_} -> Var38 (snoc38 g a) a
vz38 = \ var, vz38, vs => vz38 _ _

vs38 : {g:_}->{b:_}->{a:_} -> Var38 g a -> Var38 (snoc38 g b) a
vs38 = \ x, var, vz38, vs38 => vs38 _ _ _ (x var vz38 vs38)

Tm38 : Con38 -> Ty38-> Type
Tm38 = \ g, a =>
    (Tm38    : Con38 -> Ty38-> Type)
 -> (var   : (g:_)->(a:_)-> Var38 g a -> Tm38 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm38 (snoc38 g a) b -> Tm38 g (arr38 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm38 g (arr38 a b) -> Tm38 g a -> Tm38 g b)
 -> (tt    : (g:_)-> Tm38 g top38)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm38 g a -> Tm38 g b -> Tm38 g (prod38 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm38 g (prod38 a b) -> Tm38 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm38 g (prod38 a b) -> Tm38 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm38 g a -> Tm38 g (sum38 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm38 g b -> Tm38 g (sum38 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm38 g (sum38 a b) -> Tm38 g (arr38 a c) -> Tm38 g (arr38 b c) -> Tm38 g c)
 -> (zero  : (g:_)-> Tm38 g nat38)
 -> (suc   : (g:_)-> Tm38 g nat38 -> Tm38 g nat38)
 -> (rec   : (g:_)->(a:_) -> Tm38 g nat38 -> Tm38 g (arr38 nat38 (arr38 a a)) -> Tm38 g a -> Tm38 g a)
 -> Tm38 g a

var38 : {g:_}->{a:_} -> Var38 g a -> Tm38 g a
var38 = \ x, tm, var38, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var38 _ _ x

lam38 : {g:_}->{a:_}->{b:_}-> Tm38 (snoc38 g a) b -> Tm38 g (arr38 a b)
lam38 = \ t, tm, var38, lam38, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam38 _ _ _ (t tm var38 lam38 app tt pair fst snd left right split zero suc rec)

app38 : {g:_}->{a:_}->{b:_} -> Tm38 g (arr38 a b) -> Tm38 g a -> Tm38 g b
app38 = \ t, u, tm, var38, lam38, app38, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app38 _ _ _ (t tm var38 lam38 app38 tt pair fst snd left right split zero suc rec)
                (u tm var38 lam38 app38 tt pair fst snd left right split zero suc rec)

tt38 : {g:_} -> Tm38 g Main.top38
tt38 = \ tm, var38, lam38, app38, tt38, pair, fst, snd, left, right, split, zero, suc, rec => tt38 _

pair38 : {g:_}->{a:_}->{b:_} -> Tm38 g a -> Tm38 g b -> Tm38 g (prod38 a b)
pair38 = \ t, u, tm, var38, lam38, app38, tt38, pair38, fst, snd, left, right, split, zero, suc, rec =>
     pair38 _ _ _ (t tm var38 lam38 app38 tt38 pair38 fst snd left right split zero suc rec)
                 (u tm var38 lam38 app38 tt38 pair38 fst snd left right split zero suc rec)

fst38 : {g:_}->{a:_}->{b:_}-> Tm38 g (prod38 a b) -> Tm38 g a
fst38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd, left, right, split, zero, suc, rec =>
     fst38 _ _ _ (t tm var38 lam38 app38 tt38 pair38 fst38 snd left right split zero suc rec)

snd38 : {g:_}->{a:_}->{b:_} -> Tm38 g (prod38 a b) -> Tm38 g b
snd38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left, right, split, zero, suc, rec =>
     snd38 _ _ _ (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left right split zero suc rec)

left38 : {g:_}->{a:_}->{b:_} -> Tm38 g a -> Tm38 g (sum38 a b)
left38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right, split, zero, suc, rec =>
     left38 _ _ _ (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right split zero suc rec)

right38 : {g:_}->{a:_}->{b:_} -> Tm38 g b -> Tm38 g (sum38 a b)
right38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split, zero, suc, rec =>
     right38 _ _ _ (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split zero suc rec)

split38 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm38 g (sum38 a b) -> Tm38 g (arr38 a c) -> Tm38 g (arr38 b c) -> Tm38 g c
split38 = \ t, u, v, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split38, zero, suc, rec =>
     split38 _ _ _ _
          (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero suc rec)
          (u tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero suc rec)
          (v tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero suc rec)

zero38 : {g:_} -> Tm38 g Main.nat38
zero38 = \ tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split38, zero38, suc, rec =>
  zero38 _

suc38 : {g:_} -> Tm38 g Main.nat38 -> Tm38 g Main.nat38
suc38 = \ t, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split38, zero38, suc38, rec =>
   suc38 _ (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero38 suc38 rec)

rec38 : {g:_}->{a:_} -> Tm38 g Main.nat38 -> Tm38 g (arr38 Main.nat38 (arr38 a a)) -> Tm38 g a -> Tm38 g a
rec38 = \ t, u, v, tm, var38, lam38, app38, tt38, pair38, fst38, snd38, left38, right38, split38, zero38, suc38, rec38 =>
     rec38 _ _
       (t tm var38 lam38 app38 tt38 pair38 fst38 snd38 left38 right38 split38 zero38 suc38 rec38)
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
 -> (vz  : (g:_)->(a:_) -> Var39 (snoc39 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var39 g a -> Var39 (snoc39 g b) a)
 -> Var39 g a

vz39 : {g:_}->{a:_} -> Var39 (snoc39 g a) a
vz39 = \ var, vz39, vs => vz39 _ _

vs39 : {g:_}->{b:_}->{a:_} -> Var39 g a -> Var39 (snoc39 g b) a
vs39 = \ x, var, vz39, vs39 => vs39 _ _ _ (x var vz39 vs39)

Tm39 : Con39 -> Ty39-> Type
Tm39 = \ g, a =>
    (Tm39    : Con39 -> Ty39-> Type)
 -> (var   : (g:_)->(a:_)-> Var39 g a -> Tm39 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm39 (snoc39 g a) b -> Tm39 g (arr39 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm39 g (arr39 a b) -> Tm39 g a -> Tm39 g b)
 -> (tt    : (g:_)-> Tm39 g top39)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm39 g a -> Tm39 g b -> Tm39 g (prod39 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm39 g (prod39 a b) -> Tm39 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm39 g (prod39 a b) -> Tm39 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm39 g a -> Tm39 g (sum39 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm39 g b -> Tm39 g (sum39 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm39 g (sum39 a b) -> Tm39 g (arr39 a c) -> Tm39 g (arr39 b c) -> Tm39 g c)
 -> (zero  : (g:_)-> Tm39 g nat39)
 -> (suc   : (g:_)-> Tm39 g nat39 -> Tm39 g nat39)
 -> (rec   : (g:_)->(a:_) -> Tm39 g nat39 -> Tm39 g (arr39 nat39 (arr39 a a)) -> Tm39 g a -> Tm39 g a)
 -> Tm39 g a

var39 : {g:_}->{a:_} -> Var39 g a -> Tm39 g a
var39 = \ x, tm, var39, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var39 _ _ x

lam39 : {g:_}->{a:_}->{b:_}-> Tm39 (snoc39 g a) b -> Tm39 g (arr39 a b)
lam39 = \ t, tm, var39, lam39, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam39 _ _ _ (t tm var39 lam39 app tt pair fst snd left right split zero suc rec)

app39 : {g:_}->{a:_}->{b:_} -> Tm39 g (arr39 a b) -> Tm39 g a -> Tm39 g b
app39 = \ t, u, tm, var39, lam39, app39, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app39 _ _ _ (t tm var39 lam39 app39 tt pair fst snd left right split zero suc rec)
                (u tm var39 lam39 app39 tt pair fst snd left right split zero suc rec)

tt39 : {g:_} -> Tm39 g Main.top39
tt39 = \ tm, var39, lam39, app39, tt39, pair, fst, snd, left, right, split, zero, suc, rec => tt39 _

pair39 : {g:_}->{a:_}->{b:_} -> Tm39 g a -> Tm39 g b -> Tm39 g (prod39 a b)
pair39 = \ t, u, tm, var39, lam39, app39, tt39, pair39, fst, snd, left, right, split, zero, suc, rec =>
     pair39 _ _ _ (t tm var39 lam39 app39 tt39 pair39 fst snd left right split zero suc rec)
                 (u tm var39 lam39 app39 tt39 pair39 fst snd left right split zero suc rec)

fst39 : {g:_}->{a:_}->{b:_}-> Tm39 g (prod39 a b) -> Tm39 g a
fst39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd, left, right, split, zero, suc, rec =>
     fst39 _ _ _ (t tm var39 lam39 app39 tt39 pair39 fst39 snd left right split zero suc rec)

snd39 : {g:_}->{a:_}->{b:_} -> Tm39 g (prod39 a b) -> Tm39 g b
snd39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left, right, split, zero, suc, rec =>
     snd39 _ _ _ (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left right split zero suc rec)

left39 : {g:_}->{a:_}->{b:_} -> Tm39 g a -> Tm39 g (sum39 a b)
left39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right, split, zero, suc, rec =>
     left39 _ _ _ (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right split zero suc rec)

right39 : {g:_}->{a:_}->{b:_} -> Tm39 g b -> Tm39 g (sum39 a b)
right39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split, zero, suc, rec =>
     right39 _ _ _ (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split zero suc rec)

split39 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm39 g (sum39 a b) -> Tm39 g (arr39 a c) -> Tm39 g (arr39 b c) -> Tm39 g c
split39 = \ t, u, v, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split39, zero, suc, rec =>
     split39 _ _ _ _
          (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero suc rec)
          (u tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero suc rec)
          (v tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero suc rec)

zero39 : {g:_} -> Tm39 g Main.nat39
zero39 = \ tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split39, zero39, suc, rec =>
  zero39 _

suc39 : {g:_} -> Tm39 g Main.nat39 -> Tm39 g Main.nat39
suc39 = \ t, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split39, zero39, suc39, rec =>
   suc39 _ (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero39 suc39 rec)

rec39 : {g:_}->{a:_} -> Tm39 g Main.nat39 -> Tm39 g (arr39 Main.nat39 (arr39 a a)) -> Tm39 g a -> Tm39 g a
rec39 = \ t, u, v, tm, var39, lam39, app39, tt39, pair39, fst39, snd39, left39, right39, split39, zero39, suc39, rec39 =>
     rec39 _ _
       (t tm var39 lam39 app39 tt39 pair39 fst39 snd39 left39 right39 split39 zero39 suc39 rec39)
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

Ty40 : Type
Ty40 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat40 : Ty40
nat40 = \ _, nat40, _, _, _, _, _ => nat40
top40 : Ty40
top40 = \ _, _, top40, _, _, _, _ => top40
bot40 : Ty40
bot40 = \ _, _, _, bot40, _, _, _ => bot40

arr40 : Ty40-> Ty40-> Ty40
arr40 = \ a, b, ty, nat40, top40, bot40, arr40, prod, sum =>
     arr40 (a ty nat40 top40 bot40 arr40 prod sum) (b ty nat40 top40 bot40 arr40 prod sum)

prod40 : Ty40-> Ty40-> Ty40
prod40 = \ a, b, ty, nat40, top40, bot40, arr40, prod40, sum =>
     prod40 (a ty nat40 top40 bot40 arr40 prod40 sum) (b ty nat40 top40 bot40 arr40 prod40 sum)

sum40 : Ty40-> Ty40-> Ty40
sum40 = \ a, b, ty, nat40, top40, bot40, arr40, prod40, sum40 =>
     sum40 (a ty nat40 top40 bot40 arr40 prod40 sum40) (b ty nat40 top40 bot40 arr40 prod40 sum40)

Con40 : Type
Con40 = (Con40 : Type)
 -> (nil  : Con40)
 -> (snoc : Con40 -> Ty40-> Con40)
 -> Con40

nil40 : Con40
nil40 = \ con, nil40, snoc => nil40

snoc40 : Con40 -> Ty40-> Con40
snoc40 = \ g, a, con, nil40, snoc40 => snoc40 (g con nil40 snoc40) a

Var40 : Con40 -> Ty40-> Type
Var40 = \ g, a =>
    (Var40 : Con40 -> Ty40-> Type)
 -> (vz  : (g:_)->(a:_) -> Var40 (snoc40 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var40 g a -> Var40 (snoc40 g b) a)
 -> Var40 g a

vz40 : {g:_}->{a:_} -> Var40 (snoc40 g a) a
vz40 = \ var, vz40, vs => vz40 _ _

vs40 : {g:_}->{b:_}->{a:_} -> Var40 g a -> Var40 (snoc40 g b) a
vs40 = \ x, var, vz40, vs40 => vs40 _ _ _ (x var vz40 vs40)

Tm40 : Con40 -> Ty40-> Type
Tm40 = \ g, a =>
    (Tm40    : Con40 -> Ty40-> Type)
 -> (var   : (g:_)->(a:_)-> Var40 g a -> Tm40 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm40 (snoc40 g a) b -> Tm40 g (arr40 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm40 g (arr40 a b) -> Tm40 g a -> Tm40 g b)
 -> (tt    : (g:_)-> Tm40 g top40)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm40 g a -> Tm40 g b -> Tm40 g (prod40 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm40 g (prod40 a b) -> Tm40 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm40 g (prod40 a b) -> Tm40 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm40 g a -> Tm40 g (sum40 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm40 g b -> Tm40 g (sum40 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm40 g (sum40 a b) -> Tm40 g (arr40 a c) -> Tm40 g (arr40 b c) -> Tm40 g c)
 -> (zero  : (g:_)-> Tm40 g nat40)
 -> (suc   : (g:_)-> Tm40 g nat40 -> Tm40 g nat40)
 -> (rec   : (g:_)->(a:_) -> Tm40 g nat40 -> Tm40 g (arr40 nat40 (arr40 a a)) -> Tm40 g a -> Tm40 g a)
 -> Tm40 g a

var40 : {g:_}->{a:_} -> Var40 g a -> Tm40 g a
var40 = \ x, tm, var40, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var40 _ _ x

lam40 : {g:_}->{a:_}->{b:_}-> Tm40 (snoc40 g a) b -> Tm40 g (arr40 a b)
lam40 = \ t, tm, var40, lam40, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam40 _ _ _ (t tm var40 lam40 app tt pair fst snd left right split zero suc rec)

app40 : {g:_}->{a:_}->{b:_} -> Tm40 g (arr40 a b) -> Tm40 g a -> Tm40 g b
app40 = \ t, u, tm, var40, lam40, app40, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app40 _ _ _ (t tm var40 lam40 app40 tt pair fst snd left right split zero suc rec)
                (u tm var40 lam40 app40 tt pair fst snd left right split zero suc rec)

tt40 : {g:_} -> Tm40 g Main.top40
tt40 = \ tm, var40, lam40, app40, tt40, pair, fst, snd, left, right, split, zero, suc, rec => tt40 _

pair40 : {g:_}->{a:_}->{b:_} -> Tm40 g a -> Tm40 g b -> Tm40 g (prod40 a b)
pair40 = \ t, u, tm, var40, lam40, app40, tt40, pair40, fst, snd, left, right, split, zero, suc, rec =>
     pair40 _ _ _ (t tm var40 lam40 app40 tt40 pair40 fst snd left right split zero suc rec)
                 (u tm var40 lam40 app40 tt40 pair40 fst snd left right split zero suc rec)

fst40 : {g:_}->{a:_}->{b:_}-> Tm40 g (prod40 a b) -> Tm40 g a
fst40 = \ t, tm, var40, lam40, app40, tt40, pair40, fst40, snd, left, right, split, zero, suc, rec =>
     fst40 _ _ _ (t tm var40 lam40 app40 tt40 pair40 fst40 snd left right split zero suc rec)

snd40 : {g:_}->{a:_}->{b:_} -> Tm40 g (prod40 a b) -> Tm40 g b
snd40 = \ t, tm, var40, lam40, app40, tt40, pair40, fst40, snd40, left, right, split, zero, suc, rec =>
     snd40 _ _ _ (t tm var40 lam40 app40 tt40 pair40 fst40 snd40 left right split zero suc rec)

left40 : {g:_}->{a:_}->{b:_} -> Tm40 g a -> Tm40 g (sum40 a b)
left40 = \ t, tm, var40, lam40, app40, tt40, pair40, fst40, snd40, left40, right, split, zero, suc, rec =>
     left40 _ _ _ (t tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right split zero suc rec)

right40 : {g:_}->{a:_}->{b:_} -> Tm40 g b -> Tm40 g (sum40 a b)
right40 = \ t, tm, var40, lam40, app40, tt40, pair40, fst40, snd40, left40, right40, split, zero, suc, rec =>
     right40 _ _ _ (t tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 split zero suc rec)

split40 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm40 g (sum40 a b) -> Tm40 g (arr40 a c) -> Tm40 g (arr40 b c) -> Tm40 g c
split40 = \ t, u, v, tm, var40, lam40, app40, tt40, pair40, fst40, snd40, left40, right40, split40, zero, suc, rec =>
     split40 _ _ _ _
          (t tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 split40 zero suc rec)
          (u tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 split40 zero suc rec)
          (v tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 split40 zero suc rec)

zero40 : {g:_} -> Tm40 g Main.nat40
zero40 = \ tm, var40, lam40, app40, tt40, pair40, fst40, snd40, left40, right40, split40, zero40, suc, rec =>
  zero40 _

suc40 : {g:_} -> Tm40 g Main.nat40 -> Tm40 g Main.nat40
suc40 = \ t, tm, var40, lam40, app40, tt40, pair40, fst40, snd40, left40, right40, split40, zero40, suc40, rec =>
   suc40 _ (t tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 split40 zero40 suc40 rec)

rec40 : {g:_}->{a:_} -> Tm40 g Main.nat40 -> Tm40 g (arr40 Main.nat40 (arr40 a a)) -> Tm40 g a -> Tm40 g a
rec40 = \ t, u, v, tm, var40, lam40, app40, tt40, pair40, fst40, snd40, left40, right40, split40, zero40, suc40, rec40 =>
     rec40 _ _
       (t tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 split40 zero40 suc40 rec40)
       (u tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 split40 zero40 suc40 rec40)
       (v tm var40 lam40 app40 tt40 pair40 fst40 snd40 left40 right40 split40 zero40 suc40 rec40)

v040 : {g:_}->{a:_} -> Tm40 (snoc40 g a) a
v040 = var40 vz40

v140 : {g:_}->{a:_}->{b:_} -> Tm40 (snoc40 (snoc40 g a) b) a
v140 = var40 (vs40 vz40)

v240 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm40 (snoc40 (snoc40 (snoc40 g a) b) c) a
v240 = var40 (vs40 (vs40 vz40))

v340 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm40 (snoc40 (snoc40 (snoc40 (snoc40 g a) b) c) d) a
v340 = var40 (vs40 (vs40 (vs40 vz40)))

tbool40 : Ty40
tbool40 = sum40 top40 top40

ttrue40 : {g:_} -> Tm40 g Main.tbool40
ttrue40 = left40 tt40

tfalse40 : {g:_} -> Tm40 g Main.tbool40
tfalse40 = right40 tt40

ifthenelse40 : {g:_}->{a:_} -> Tm40 g (arr40 Main.tbool40 (arr40 a (arr40 a a)))
ifthenelse40 = lam40 (lam40 (lam40 (split40 v240 (lam40 v240) (lam40 v140))))

times440 : {g:_}->{a:_} -> Tm40 g (arr40 (arr40 a a) (arr40 a a))
times440  = lam40 (lam40 (app40 v140 (app40 v140 (app40 v140 (app40 v140 v040)))))

add40 : {g:_} -> Tm40 g (arr40 Main.nat40 (arr40 Main.nat40 Main.nat40))
add40 = lam40 (rec40 v040
       (lam40 (lam40 (lam40 (suc40 (app40 v140 v040)))))
       (lam40 v040))

mul40 : {g:_} -> Tm40 g (arr40 Main.nat40 (arr40 Main.nat40 Main.nat40))
mul40 = lam40 (rec40 v040
       (lam40 (lam40 (lam40 (app40 (app40 add40 (app40 v140 v040)) v040))))
       (lam40 zero40))

fact40 : {g:_} -> Tm40 g (arr40 Main.nat40 Main.nat40)
fact40 = lam40 (rec40 v040 (lam40 (lam40 (app40 (app40 mul40 (suc40 v140)) v040)))
                 (suc40 zero40))

Ty41 : Type
Ty41 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat41 : Ty41
nat41 = \ _, nat41, _, _, _, _, _ => nat41
top41 : Ty41
top41 = \ _, _, top41, _, _, _, _ => top41
bot41 : Ty41
bot41 = \ _, _, _, bot41, _, _, _ => bot41

arr41 : Ty41-> Ty41-> Ty41
arr41 = \ a, b, ty, nat41, top41, bot41, arr41, prod, sum =>
     arr41 (a ty nat41 top41 bot41 arr41 prod sum) (b ty nat41 top41 bot41 arr41 prod sum)

prod41 : Ty41-> Ty41-> Ty41
prod41 = \ a, b, ty, nat41, top41, bot41, arr41, prod41, sum =>
     prod41 (a ty nat41 top41 bot41 arr41 prod41 sum) (b ty nat41 top41 bot41 arr41 prod41 sum)

sum41 : Ty41-> Ty41-> Ty41
sum41 = \ a, b, ty, nat41, top41, bot41, arr41, prod41, sum41 =>
     sum41 (a ty nat41 top41 bot41 arr41 prod41 sum41) (b ty nat41 top41 bot41 arr41 prod41 sum41)

Con41 : Type
Con41 = (Con41 : Type)
 -> (nil  : Con41)
 -> (snoc : Con41 -> Ty41-> Con41)
 -> Con41

nil41 : Con41
nil41 = \ con, nil41, snoc => nil41

snoc41 : Con41 -> Ty41-> Con41
snoc41 = \ g, a, con, nil41, snoc41 => snoc41 (g con nil41 snoc41) a

Var41 : Con41 -> Ty41-> Type
Var41 = \ g, a =>
    (Var41 : Con41 -> Ty41-> Type)
 -> (vz  : (g:_)->(a:_) -> Var41 (snoc41 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var41 g a -> Var41 (snoc41 g b) a)
 -> Var41 g a

vz41 : {g:_}->{a:_} -> Var41 (snoc41 g a) a
vz41 = \ var, vz41, vs => vz41 _ _

vs41 : {g:_}->{b:_}->{a:_} -> Var41 g a -> Var41 (snoc41 g b) a
vs41 = \ x, var, vz41, vs41 => vs41 _ _ _ (x var vz41 vs41)

Tm41 : Con41 -> Ty41-> Type
Tm41 = \ g, a =>
    (Tm41    : Con41 -> Ty41-> Type)
 -> (var   : (g:_)->(a:_)-> Var41 g a -> Tm41 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm41 (snoc41 g a) b -> Tm41 g (arr41 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm41 g (arr41 a b) -> Tm41 g a -> Tm41 g b)
 -> (tt    : (g:_)-> Tm41 g top41)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm41 g a -> Tm41 g b -> Tm41 g (prod41 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm41 g (prod41 a b) -> Tm41 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm41 g (prod41 a b) -> Tm41 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm41 g a -> Tm41 g (sum41 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm41 g b -> Tm41 g (sum41 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm41 g (sum41 a b) -> Tm41 g (arr41 a c) -> Tm41 g (arr41 b c) -> Tm41 g c)
 -> (zero  : (g:_)-> Tm41 g nat41)
 -> (suc   : (g:_)-> Tm41 g nat41 -> Tm41 g nat41)
 -> (rec   : (g:_)->(a:_) -> Tm41 g nat41 -> Tm41 g (arr41 nat41 (arr41 a a)) -> Tm41 g a -> Tm41 g a)
 -> Tm41 g a

var41 : {g:_}->{a:_} -> Var41 g a -> Tm41 g a
var41 = \ x, tm, var41, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var41 _ _ x

lam41 : {g:_}->{a:_}->{b:_}-> Tm41 (snoc41 g a) b -> Tm41 g (arr41 a b)
lam41 = \ t, tm, var41, lam41, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam41 _ _ _ (t tm var41 lam41 app tt pair fst snd left right split zero suc rec)

app41 : {g:_}->{a:_}->{b:_} -> Tm41 g (arr41 a b) -> Tm41 g a -> Tm41 g b
app41 = \ t, u, tm, var41, lam41, app41, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app41 _ _ _ (t tm var41 lam41 app41 tt pair fst snd left right split zero suc rec)
                (u tm var41 lam41 app41 tt pair fst snd left right split zero suc rec)

tt41 : {g:_} -> Tm41 g Main.top41
tt41 = \ tm, var41, lam41, app41, tt41, pair, fst, snd, left, right, split, zero, suc, rec => tt41 _

pair41 : {g:_}->{a:_}->{b:_} -> Tm41 g a -> Tm41 g b -> Tm41 g (prod41 a b)
pair41 = \ t, u, tm, var41, lam41, app41, tt41, pair41, fst, snd, left, right, split, zero, suc, rec =>
     pair41 _ _ _ (t tm var41 lam41 app41 tt41 pair41 fst snd left right split zero suc rec)
                 (u tm var41 lam41 app41 tt41 pair41 fst snd left right split zero suc rec)

fst41 : {g:_}->{a:_}->{b:_}-> Tm41 g (prod41 a b) -> Tm41 g a
fst41 = \ t, tm, var41, lam41, app41, tt41, pair41, fst41, snd, left, right, split, zero, suc, rec =>
     fst41 _ _ _ (t tm var41 lam41 app41 tt41 pair41 fst41 snd left right split zero suc rec)

snd41 : {g:_}->{a:_}->{b:_} -> Tm41 g (prod41 a b) -> Tm41 g b
snd41 = \ t, tm, var41, lam41, app41, tt41, pair41, fst41, snd41, left, right, split, zero, suc, rec =>
     snd41 _ _ _ (t tm var41 lam41 app41 tt41 pair41 fst41 snd41 left right split zero suc rec)

left41 : {g:_}->{a:_}->{b:_} -> Tm41 g a -> Tm41 g (sum41 a b)
left41 = \ t, tm, var41, lam41, app41, tt41, pair41, fst41, snd41, left41, right, split, zero, suc, rec =>
     left41 _ _ _ (t tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right split zero suc rec)

right41 : {g:_}->{a:_}->{b:_} -> Tm41 g b -> Tm41 g (sum41 a b)
right41 = \ t, tm, var41, lam41, app41, tt41, pair41, fst41, snd41, left41, right41, split, zero, suc, rec =>
     right41 _ _ _ (t tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 split zero suc rec)

split41 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm41 g (sum41 a b) -> Tm41 g (arr41 a c) -> Tm41 g (arr41 b c) -> Tm41 g c
split41 = \ t, u, v, tm, var41, lam41, app41, tt41, pair41, fst41, snd41, left41, right41, split41, zero, suc, rec =>
     split41 _ _ _ _
          (t tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 split41 zero suc rec)
          (u tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 split41 zero suc rec)
          (v tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 split41 zero suc rec)

zero41 : {g:_} -> Tm41 g Main.nat41
zero41 = \ tm, var41, lam41, app41, tt41, pair41, fst41, snd41, left41, right41, split41, zero41, suc, rec =>
  zero41 _

suc41 : {g:_} -> Tm41 g Main.nat41 -> Tm41 g Main.nat41
suc41 = \ t, tm, var41, lam41, app41, tt41, pair41, fst41, snd41, left41, right41, split41, zero41, suc41, rec =>
   suc41 _ (t tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 split41 zero41 suc41 rec)

rec41 : {g:_}->{a:_} -> Tm41 g Main.nat41 -> Tm41 g (arr41 Main.nat41 (arr41 a a)) -> Tm41 g a -> Tm41 g a
rec41 = \ t, u, v, tm, var41, lam41, app41, tt41, pair41, fst41, snd41, left41, right41, split41, zero41, suc41, rec41 =>
     rec41 _ _
       (t tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 split41 zero41 suc41 rec41)
       (u tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 split41 zero41 suc41 rec41)
       (v tm var41 lam41 app41 tt41 pair41 fst41 snd41 left41 right41 split41 zero41 suc41 rec41)

v041 : {g:_}->{a:_} -> Tm41 (snoc41 g a) a
v041 = var41 vz41

v141 : {g:_}->{a:_}->{b:_} -> Tm41 (snoc41 (snoc41 g a) b) a
v141 = var41 (vs41 vz41)

v241 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm41 (snoc41 (snoc41 (snoc41 g a) b) c) a
v241 = var41 (vs41 (vs41 vz41))

v341 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm41 (snoc41 (snoc41 (snoc41 (snoc41 g a) b) c) d) a
v341 = var41 (vs41 (vs41 (vs41 vz41)))

tbool41 : Ty41
tbool41 = sum41 top41 top41

ttrue41 : {g:_} -> Tm41 g Main.tbool41
ttrue41 = left41 tt41

tfalse41 : {g:_} -> Tm41 g Main.tbool41
tfalse41 = right41 tt41

ifthenelse41 : {g:_}->{a:_} -> Tm41 g (arr41 Main.tbool41 (arr41 a (arr41 a a)))
ifthenelse41 = lam41 (lam41 (lam41 (split41 v241 (lam41 v241) (lam41 v141))))

times441 : {g:_}->{a:_} -> Tm41 g (arr41 (arr41 a a) (arr41 a a))
times441  = lam41 (lam41 (app41 v141 (app41 v141 (app41 v141 (app41 v141 v041)))))

add41 : {g:_} -> Tm41 g (arr41 Main.nat41 (arr41 Main.nat41 Main.nat41))
add41 = lam41 (rec41 v041
       (lam41 (lam41 (lam41 (suc41 (app41 v141 v041)))))
       (lam41 v041))

mul41 : {g:_} -> Tm41 g (arr41 Main.nat41 (arr41 Main.nat41 Main.nat41))
mul41 = lam41 (rec41 v041
       (lam41 (lam41 (lam41 (app41 (app41 add41 (app41 v141 v041)) v041))))
       (lam41 zero41))

fact41 : {g:_} -> Tm41 g (arr41 Main.nat41 Main.nat41)
fact41 = lam41 (rec41 v041 (lam41 (lam41 (app41 (app41 mul41 (suc41 v141)) v041)))
                 (suc41 zero41))

Ty42 : Type
Ty42 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat42 : Ty42
nat42 = \ _, nat42, _, _, _, _, _ => nat42
top42 : Ty42
top42 = \ _, _, top42, _, _, _, _ => top42
bot42 : Ty42
bot42 = \ _, _, _, bot42, _, _, _ => bot42

arr42 : Ty42-> Ty42-> Ty42
arr42 = \ a, b, ty, nat42, top42, bot42, arr42, prod, sum =>
     arr42 (a ty nat42 top42 bot42 arr42 prod sum) (b ty nat42 top42 bot42 arr42 prod sum)

prod42 : Ty42-> Ty42-> Ty42
prod42 = \ a, b, ty, nat42, top42, bot42, arr42, prod42, sum =>
     prod42 (a ty nat42 top42 bot42 arr42 prod42 sum) (b ty nat42 top42 bot42 arr42 prod42 sum)

sum42 : Ty42-> Ty42-> Ty42
sum42 = \ a, b, ty, nat42, top42, bot42, arr42, prod42, sum42 =>
     sum42 (a ty nat42 top42 bot42 arr42 prod42 sum42) (b ty nat42 top42 bot42 arr42 prod42 sum42)

Con42 : Type
Con42 = (Con42 : Type)
 -> (nil  : Con42)
 -> (snoc : Con42 -> Ty42-> Con42)
 -> Con42

nil42 : Con42
nil42 = \ con, nil42, snoc => nil42

snoc42 : Con42 -> Ty42-> Con42
snoc42 = \ g, a, con, nil42, snoc42 => snoc42 (g con nil42 snoc42) a

Var42 : Con42 -> Ty42-> Type
Var42 = \ g, a =>
    (Var42 : Con42 -> Ty42-> Type)
 -> (vz  : (g:_)->(a:_) -> Var42 (snoc42 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var42 g a -> Var42 (snoc42 g b) a)
 -> Var42 g a

vz42 : {g:_}->{a:_} -> Var42 (snoc42 g a) a
vz42 = \ var, vz42, vs => vz42 _ _

vs42 : {g:_}->{b:_}->{a:_} -> Var42 g a -> Var42 (snoc42 g b) a
vs42 = \ x, var, vz42, vs42 => vs42 _ _ _ (x var vz42 vs42)

Tm42 : Con42 -> Ty42-> Type
Tm42 = \ g, a =>
    (Tm42    : Con42 -> Ty42-> Type)
 -> (var   : (g:_)->(a:_)-> Var42 g a -> Tm42 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm42 (snoc42 g a) b -> Tm42 g (arr42 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm42 g (arr42 a b) -> Tm42 g a -> Tm42 g b)
 -> (tt    : (g:_)-> Tm42 g top42)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm42 g a -> Tm42 g b -> Tm42 g (prod42 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm42 g (prod42 a b) -> Tm42 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm42 g (prod42 a b) -> Tm42 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm42 g a -> Tm42 g (sum42 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm42 g b -> Tm42 g (sum42 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm42 g (sum42 a b) -> Tm42 g (arr42 a c) -> Tm42 g (arr42 b c) -> Tm42 g c)
 -> (zero  : (g:_)-> Tm42 g nat42)
 -> (suc   : (g:_)-> Tm42 g nat42 -> Tm42 g nat42)
 -> (rec   : (g:_)->(a:_) -> Tm42 g nat42 -> Tm42 g (arr42 nat42 (arr42 a a)) -> Tm42 g a -> Tm42 g a)
 -> Tm42 g a

var42 : {g:_}->{a:_} -> Var42 g a -> Tm42 g a
var42 = \ x, tm, var42, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var42 _ _ x

lam42 : {g:_}->{a:_}->{b:_}-> Tm42 (snoc42 g a) b -> Tm42 g (arr42 a b)
lam42 = \ t, tm, var42, lam42, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam42 _ _ _ (t tm var42 lam42 app tt pair fst snd left right split zero suc rec)

app42 : {g:_}->{a:_}->{b:_} -> Tm42 g (arr42 a b) -> Tm42 g a -> Tm42 g b
app42 = \ t, u, tm, var42, lam42, app42, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app42 _ _ _ (t tm var42 lam42 app42 tt pair fst snd left right split zero suc rec)
                (u tm var42 lam42 app42 tt pair fst snd left right split zero suc rec)

tt42 : {g:_} -> Tm42 g Main.top42
tt42 = \ tm, var42, lam42, app42, tt42, pair, fst, snd, left, right, split, zero, suc, rec => tt42 _

pair42 : {g:_}->{a:_}->{b:_} -> Tm42 g a -> Tm42 g b -> Tm42 g (prod42 a b)
pair42 = \ t, u, tm, var42, lam42, app42, tt42, pair42, fst, snd, left, right, split, zero, suc, rec =>
     pair42 _ _ _ (t tm var42 lam42 app42 tt42 pair42 fst snd left right split zero suc rec)
                 (u tm var42 lam42 app42 tt42 pair42 fst snd left right split zero suc rec)

fst42 : {g:_}->{a:_}->{b:_}-> Tm42 g (prod42 a b) -> Tm42 g a
fst42 = \ t, tm, var42, lam42, app42, tt42, pair42, fst42, snd, left, right, split, zero, suc, rec =>
     fst42 _ _ _ (t tm var42 lam42 app42 tt42 pair42 fst42 snd left right split zero suc rec)

snd42 : {g:_}->{a:_}->{b:_} -> Tm42 g (prod42 a b) -> Tm42 g b
snd42 = \ t, tm, var42, lam42, app42, tt42, pair42, fst42, snd42, left, right, split, zero, suc, rec =>
     snd42 _ _ _ (t tm var42 lam42 app42 tt42 pair42 fst42 snd42 left right split zero suc rec)

left42 : {g:_}->{a:_}->{b:_} -> Tm42 g a -> Tm42 g (sum42 a b)
left42 = \ t, tm, var42, lam42, app42, tt42, pair42, fst42, snd42, left42, right, split, zero, suc, rec =>
     left42 _ _ _ (t tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right split zero suc rec)

right42 : {g:_}->{a:_}->{b:_} -> Tm42 g b -> Tm42 g (sum42 a b)
right42 = \ t, tm, var42, lam42, app42, tt42, pair42, fst42, snd42, left42, right42, split, zero, suc, rec =>
     right42 _ _ _ (t tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 split zero suc rec)

split42 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm42 g (sum42 a b) -> Tm42 g (arr42 a c) -> Tm42 g (arr42 b c) -> Tm42 g c
split42 = \ t, u, v, tm, var42, lam42, app42, tt42, pair42, fst42, snd42, left42, right42, split42, zero, suc, rec =>
     split42 _ _ _ _
          (t tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 split42 zero suc rec)
          (u tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 split42 zero suc rec)
          (v tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 split42 zero suc rec)

zero42 : {g:_} -> Tm42 g Main.nat42
zero42 = \ tm, var42, lam42, app42, tt42, pair42, fst42, snd42, left42, right42, split42, zero42, suc, rec =>
  zero42 _

suc42 : {g:_} -> Tm42 g Main.nat42 -> Tm42 g Main.nat42
suc42 = \ t, tm, var42, lam42, app42, tt42, pair42, fst42, snd42, left42, right42, split42, zero42, suc42, rec =>
   suc42 _ (t tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 split42 zero42 suc42 rec)

rec42 : {g:_}->{a:_} -> Tm42 g Main.nat42 -> Tm42 g (arr42 Main.nat42 (arr42 a a)) -> Tm42 g a -> Tm42 g a
rec42 = \ t, u, v, tm, var42, lam42, app42, tt42, pair42, fst42, snd42, left42, right42, split42, zero42, suc42, rec42 =>
     rec42 _ _
       (t tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 split42 zero42 suc42 rec42)
       (u tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 split42 zero42 suc42 rec42)
       (v tm var42 lam42 app42 tt42 pair42 fst42 snd42 left42 right42 split42 zero42 suc42 rec42)

v042 : {g:_}->{a:_} -> Tm42 (snoc42 g a) a
v042 = var42 vz42

v142 : {g:_}->{a:_}->{b:_} -> Tm42 (snoc42 (snoc42 g a) b) a
v142 = var42 (vs42 vz42)

v242 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm42 (snoc42 (snoc42 (snoc42 g a) b) c) a
v242 = var42 (vs42 (vs42 vz42))

v342 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm42 (snoc42 (snoc42 (snoc42 (snoc42 g a) b) c) d) a
v342 = var42 (vs42 (vs42 (vs42 vz42)))

tbool42 : Ty42
tbool42 = sum42 top42 top42

ttrue42 : {g:_} -> Tm42 g Main.tbool42
ttrue42 = left42 tt42

tfalse42 : {g:_} -> Tm42 g Main.tbool42
tfalse42 = right42 tt42

ifthenelse42 : {g:_}->{a:_} -> Tm42 g (arr42 Main.tbool42 (arr42 a (arr42 a a)))
ifthenelse42 = lam42 (lam42 (lam42 (split42 v242 (lam42 v242) (lam42 v142))))

times442 : {g:_}->{a:_} -> Tm42 g (arr42 (arr42 a a) (arr42 a a))
times442  = lam42 (lam42 (app42 v142 (app42 v142 (app42 v142 (app42 v142 v042)))))

add42 : {g:_} -> Tm42 g (arr42 Main.nat42 (arr42 Main.nat42 Main.nat42))
add42 = lam42 (rec42 v042
       (lam42 (lam42 (lam42 (suc42 (app42 v142 v042)))))
       (lam42 v042))

mul42 : {g:_} -> Tm42 g (arr42 Main.nat42 (arr42 Main.nat42 Main.nat42))
mul42 = lam42 (rec42 v042
       (lam42 (lam42 (lam42 (app42 (app42 add42 (app42 v142 v042)) v042))))
       (lam42 zero42))

fact42 : {g:_} -> Tm42 g (arr42 Main.nat42 Main.nat42)
fact42 = lam42 (rec42 v042 (lam42 (lam42 (app42 (app42 mul42 (suc42 v142)) v042)))
                 (suc42 zero42))

Ty43 : Type
Ty43 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat43 : Ty43
nat43 = \ _, nat43, _, _, _, _, _ => nat43
top43 : Ty43
top43 = \ _, _, top43, _, _, _, _ => top43
bot43 : Ty43
bot43 = \ _, _, _, bot43, _, _, _ => bot43

arr43 : Ty43-> Ty43-> Ty43
arr43 = \ a, b, ty, nat43, top43, bot43, arr43, prod, sum =>
     arr43 (a ty nat43 top43 bot43 arr43 prod sum) (b ty nat43 top43 bot43 arr43 prod sum)

prod43 : Ty43-> Ty43-> Ty43
prod43 = \ a, b, ty, nat43, top43, bot43, arr43, prod43, sum =>
     prod43 (a ty nat43 top43 bot43 arr43 prod43 sum) (b ty nat43 top43 bot43 arr43 prod43 sum)

sum43 : Ty43-> Ty43-> Ty43
sum43 = \ a, b, ty, nat43, top43, bot43, arr43, prod43, sum43 =>
     sum43 (a ty nat43 top43 bot43 arr43 prod43 sum43) (b ty nat43 top43 bot43 arr43 prod43 sum43)

Con43 : Type
Con43 = (Con43 : Type)
 -> (nil  : Con43)
 -> (snoc : Con43 -> Ty43-> Con43)
 -> Con43

nil43 : Con43
nil43 = \ con, nil43, snoc => nil43

snoc43 : Con43 -> Ty43-> Con43
snoc43 = \ g, a, con, nil43, snoc43 => snoc43 (g con nil43 snoc43) a

Var43 : Con43 -> Ty43-> Type
Var43 = \ g, a =>
    (Var43 : Con43 -> Ty43-> Type)
 -> (vz  : (g:_)->(a:_) -> Var43 (snoc43 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var43 g a -> Var43 (snoc43 g b) a)
 -> Var43 g a

vz43 : {g:_}->{a:_} -> Var43 (snoc43 g a) a
vz43 = \ var, vz43, vs => vz43 _ _

vs43 : {g:_}->{b:_}->{a:_} -> Var43 g a -> Var43 (snoc43 g b) a
vs43 = \ x, var, vz43, vs43 => vs43 _ _ _ (x var vz43 vs43)

Tm43 : Con43 -> Ty43-> Type
Tm43 = \ g, a =>
    (Tm43    : Con43 -> Ty43-> Type)
 -> (var   : (g:_)->(a:_)-> Var43 g a -> Tm43 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm43 (snoc43 g a) b -> Tm43 g (arr43 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm43 g (arr43 a b) -> Tm43 g a -> Tm43 g b)
 -> (tt    : (g:_)-> Tm43 g top43)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm43 g a -> Tm43 g b -> Tm43 g (prod43 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm43 g (prod43 a b) -> Tm43 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm43 g (prod43 a b) -> Tm43 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm43 g a -> Tm43 g (sum43 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm43 g b -> Tm43 g (sum43 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm43 g (sum43 a b) -> Tm43 g (arr43 a c) -> Tm43 g (arr43 b c) -> Tm43 g c)
 -> (zero  : (g:_)-> Tm43 g nat43)
 -> (suc   : (g:_)-> Tm43 g nat43 -> Tm43 g nat43)
 -> (rec   : (g:_)->(a:_) -> Tm43 g nat43 -> Tm43 g (arr43 nat43 (arr43 a a)) -> Tm43 g a -> Tm43 g a)
 -> Tm43 g a

var43 : {g:_}->{a:_} -> Var43 g a -> Tm43 g a
var43 = \ x, tm, var43, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var43 _ _ x

lam43 : {g:_}->{a:_}->{b:_}-> Tm43 (snoc43 g a) b -> Tm43 g (arr43 a b)
lam43 = \ t, tm, var43, lam43, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam43 _ _ _ (t tm var43 lam43 app tt pair fst snd left right split zero suc rec)

app43 : {g:_}->{a:_}->{b:_} -> Tm43 g (arr43 a b) -> Tm43 g a -> Tm43 g b
app43 = \ t, u, tm, var43, lam43, app43, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app43 _ _ _ (t tm var43 lam43 app43 tt pair fst snd left right split zero suc rec)
                (u tm var43 lam43 app43 tt pair fst snd left right split zero suc rec)

tt43 : {g:_} -> Tm43 g Main.top43
tt43 = \ tm, var43, lam43, app43, tt43, pair, fst, snd, left, right, split, zero, suc, rec => tt43 _

pair43 : {g:_}->{a:_}->{b:_} -> Tm43 g a -> Tm43 g b -> Tm43 g (prod43 a b)
pair43 = \ t, u, tm, var43, lam43, app43, tt43, pair43, fst, snd, left, right, split, zero, suc, rec =>
     pair43 _ _ _ (t tm var43 lam43 app43 tt43 pair43 fst snd left right split zero suc rec)
                 (u tm var43 lam43 app43 tt43 pair43 fst snd left right split zero suc rec)

fst43 : {g:_}->{a:_}->{b:_}-> Tm43 g (prod43 a b) -> Tm43 g a
fst43 = \ t, tm, var43, lam43, app43, tt43, pair43, fst43, snd, left, right, split, zero, suc, rec =>
     fst43 _ _ _ (t tm var43 lam43 app43 tt43 pair43 fst43 snd left right split zero suc rec)

snd43 : {g:_}->{a:_}->{b:_} -> Tm43 g (prod43 a b) -> Tm43 g b
snd43 = \ t, tm, var43, lam43, app43, tt43, pair43, fst43, snd43, left, right, split, zero, suc, rec =>
     snd43 _ _ _ (t tm var43 lam43 app43 tt43 pair43 fst43 snd43 left right split zero suc rec)

left43 : {g:_}->{a:_}->{b:_} -> Tm43 g a -> Tm43 g (sum43 a b)
left43 = \ t, tm, var43, lam43, app43, tt43, pair43, fst43, snd43, left43, right, split, zero, suc, rec =>
     left43 _ _ _ (t tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right split zero suc rec)

right43 : {g:_}->{a:_}->{b:_} -> Tm43 g b -> Tm43 g (sum43 a b)
right43 = \ t, tm, var43, lam43, app43, tt43, pair43, fst43, snd43, left43, right43, split, zero, suc, rec =>
     right43 _ _ _ (t tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 split zero suc rec)

split43 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm43 g (sum43 a b) -> Tm43 g (arr43 a c) -> Tm43 g (arr43 b c) -> Tm43 g c
split43 = \ t, u, v, tm, var43, lam43, app43, tt43, pair43, fst43, snd43, left43, right43, split43, zero, suc, rec =>
     split43 _ _ _ _
          (t tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 split43 zero suc rec)
          (u tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 split43 zero suc rec)
          (v tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 split43 zero suc rec)

zero43 : {g:_} -> Tm43 g Main.nat43
zero43 = \ tm, var43, lam43, app43, tt43, pair43, fst43, snd43, left43, right43, split43, zero43, suc, rec =>
  zero43 _

suc43 : {g:_} -> Tm43 g Main.nat43 -> Tm43 g Main.nat43
suc43 = \ t, tm, var43, lam43, app43, tt43, pair43, fst43, snd43, left43, right43, split43, zero43, suc43, rec =>
   suc43 _ (t tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 split43 zero43 suc43 rec)

rec43 : {g:_}->{a:_} -> Tm43 g Main.nat43 -> Tm43 g (arr43 Main.nat43 (arr43 a a)) -> Tm43 g a -> Tm43 g a
rec43 = \ t, u, v, tm, var43, lam43, app43, tt43, pair43, fst43, snd43, left43, right43, split43, zero43, suc43, rec43 =>
     rec43 _ _
       (t tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 split43 zero43 suc43 rec43)
       (u tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 split43 zero43 suc43 rec43)
       (v tm var43 lam43 app43 tt43 pair43 fst43 snd43 left43 right43 split43 zero43 suc43 rec43)

v043 : {g:_}->{a:_} -> Tm43 (snoc43 g a) a
v043 = var43 vz43

v143 : {g:_}->{a:_}->{b:_} -> Tm43 (snoc43 (snoc43 g a) b) a
v143 = var43 (vs43 vz43)

v243 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm43 (snoc43 (snoc43 (snoc43 g a) b) c) a
v243 = var43 (vs43 (vs43 vz43))

v343 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm43 (snoc43 (snoc43 (snoc43 (snoc43 g a) b) c) d) a
v343 = var43 (vs43 (vs43 (vs43 vz43)))

tbool43 : Ty43
tbool43 = sum43 top43 top43

ttrue43 : {g:_} -> Tm43 g Main.tbool43
ttrue43 = left43 tt43

tfalse43 : {g:_} -> Tm43 g Main.tbool43
tfalse43 = right43 tt43

ifthenelse43 : {g:_}->{a:_} -> Tm43 g (arr43 Main.tbool43 (arr43 a (arr43 a a)))
ifthenelse43 = lam43 (lam43 (lam43 (split43 v243 (lam43 v243) (lam43 v143))))

times443 : {g:_}->{a:_} -> Tm43 g (arr43 (arr43 a a) (arr43 a a))
times443  = lam43 (lam43 (app43 v143 (app43 v143 (app43 v143 (app43 v143 v043)))))

add43 : {g:_} -> Tm43 g (arr43 Main.nat43 (arr43 Main.nat43 Main.nat43))
add43 = lam43 (rec43 v043
       (lam43 (lam43 (lam43 (suc43 (app43 v143 v043)))))
       (lam43 v043))

mul43 : {g:_} -> Tm43 g (arr43 Main.nat43 (arr43 Main.nat43 Main.nat43))
mul43 = lam43 (rec43 v043
       (lam43 (lam43 (lam43 (app43 (app43 add43 (app43 v143 v043)) v043))))
       (lam43 zero43))

fact43 : {g:_} -> Tm43 g (arr43 Main.nat43 Main.nat43)
fact43 = lam43 (rec43 v043 (lam43 (lam43 (app43 (app43 mul43 (suc43 v143)) v043)))
                 (suc43 zero43))

Ty44 : Type
Ty44 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat44 : Ty44
nat44 = \ _, nat44, _, _, _, _, _ => nat44
top44 : Ty44
top44 = \ _, _, top44, _, _, _, _ => top44
bot44 : Ty44
bot44 = \ _, _, _, bot44, _, _, _ => bot44

arr44 : Ty44-> Ty44-> Ty44
arr44 = \ a, b, ty, nat44, top44, bot44, arr44, prod, sum =>
     arr44 (a ty nat44 top44 bot44 arr44 prod sum) (b ty nat44 top44 bot44 arr44 prod sum)

prod44 : Ty44-> Ty44-> Ty44
prod44 = \ a, b, ty, nat44, top44, bot44, arr44, prod44, sum =>
     prod44 (a ty nat44 top44 bot44 arr44 prod44 sum) (b ty nat44 top44 bot44 arr44 prod44 sum)

sum44 : Ty44-> Ty44-> Ty44
sum44 = \ a, b, ty, nat44, top44, bot44, arr44, prod44, sum44 =>
     sum44 (a ty nat44 top44 bot44 arr44 prod44 sum44) (b ty nat44 top44 bot44 arr44 prod44 sum44)

Con44 : Type
Con44 = (Con44 : Type)
 -> (nil  : Con44)
 -> (snoc : Con44 -> Ty44-> Con44)
 -> Con44

nil44 : Con44
nil44 = \ con, nil44, snoc => nil44

snoc44 : Con44 -> Ty44-> Con44
snoc44 = \ g, a, con, nil44, snoc44 => snoc44 (g con nil44 snoc44) a

Var44 : Con44 -> Ty44-> Type
Var44 = \ g, a =>
    (Var44 : Con44 -> Ty44-> Type)
 -> (vz  : (g:_)->(a:_) -> Var44 (snoc44 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var44 g a -> Var44 (snoc44 g b) a)
 -> Var44 g a

vz44 : {g:_}->{a:_} -> Var44 (snoc44 g a) a
vz44 = \ var, vz44, vs => vz44 _ _

vs44 : {g:_}->{b:_}->{a:_} -> Var44 g a -> Var44 (snoc44 g b) a
vs44 = \ x, var, vz44, vs44 => vs44 _ _ _ (x var vz44 vs44)

Tm44 : Con44 -> Ty44-> Type
Tm44 = \ g, a =>
    (Tm44    : Con44 -> Ty44-> Type)
 -> (var   : (g:_)->(a:_)-> Var44 g a -> Tm44 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm44 (snoc44 g a) b -> Tm44 g (arr44 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm44 g (arr44 a b) -> Tm44 g a -> Tm44 g b)
 -> (tt    : (g:_)-> Tm44 g top44)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm44 g a -> Tm44 g b -> Tm44 g (prod44 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm44 g (prod44 a b) -> Tm44 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm44 g (prod44 a b) -> Tm44 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm44 g a -> Tm44 g (sum44 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm44 g b -> Tm44 g (sum44 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm44 g (sum44 a b) -> Tm44 g (arr44 a c) -> Tm44 g (arr44 b c) -> Tm44 g c)
 -> (zero  : (g:_)-> Tm44 g nat44)
 -> (suc   : (g:_)-> Tm44 g nat44 -> Tm44 g nat44)
 -> (rec   : (g:_)->(a:_) -> Tm44 g nat44 -> Tm44 g (arr44 nat44 (arr44 a a)) -> Tm44 g a -> Tm44 g a)
 -> Tm44 g a

var44 : {g:_}->{a:_} -> Var44 g a -> Tm44 g a
var44 = \ x, tm, var44, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var44 _ _ x

lam44 : {g:_}->{a:_}->{b:_}-> Tm44 (snoc44 g a) b -> Tm44 g (arr44 a b)
lam44 = \ t, tm, var44, lam44, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam44 _ _ _ (t tm var44 lam44 app tt pair fst snd left right split zero suc rec)

app44 : {g:_}->{a:_}->{b:_} -> Tm44 g (arr44 a b) -> Tm44 g a -> Tm44 g b
app44 = \ t, u, tm, var44, lam44, app44, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app44 _ _ _ (t tm var44 lam44 app44 tt pair fst snd left right split zero suc rec)
                (u tm var44 lam44 app44 tt pair fst snd left right split zero suc rec)

tt44 : {g:_} -> Tm44 g Main.top44
tt44 = \ tm, var44, lam44, app44, tt44, pair, fst, snd, left, right, split, zero, suc, rec => tt44 _

pair44 : {g:_}->{a:_}->{b:_} -> Tm44 g a -> Tm44 g b -> Tm44 g (prod44 a b)
pair44 = \ t, u, tm, var44, lam44, app44, tt44, pair44, fst, snd, left, right, split, zero, suc, rec =>
     pair44 _ _ _ (t tm var44 lam44 app44 tt44 pair44 fst snd left right split zero suc rec)
                 (u tm var44 lam44 app44 tt44 pair44 fst snd left right split zero suc rec)

fst44 : {g:_}->{a:_}->{b:_}-> Tm44 g (prod44 a b) -> Tm44 g a
fst44 = \ t, tm, var44, lam44, app44, tt44, pair44, fst44, snd, left, right, split, zero, suc, rec =>
     fst44 _ _ _ (t tm var44 lam44 app44 tt44 pair44 fst44 snd left right split zero suc rec)

snd44 : {g:_}->{a:_}->{b:_} -> Tm44 g (prod44 a b) -> Tm44 g b
snd44 = \ t, tm, var44, lam44, app44, tt44, pair44, fst44, snd44, left, right, split, zero, suc, rec =>
     snd44 _ _ _ (t tm var44 lam44 app44 tt44 pair44 fst44 snd44 left right split zero suc rec)

left44 : {g:_}->{a:_}->{b:_} -> Tm44 g a -> Tm44 g (sum44 a b)
left44 = \ t, tm, var44, lam44, app44, tt44, pair44, fst44, snd44, left44, right, split, zero, suc, rec =>
     left44 _ _ _ (t tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right split zero suc rec)

right44 : {g:_}->{a:_}->{b:_} -> Tm44 g b -> Tm44 g (sum44 a b)
right44 = \ t, tm, var44, lam44, app44, tt44, pair44, fst44, snd44, left44, right44, split, zero, suc, rec =>
     right44 _ _ _ (t tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 split zero suc rec)

split44 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm44 g (sum44 a b) -> Tm44 g (arr44 a c) -> Tm44 g (arr44 b c) -> Tm44 g c
split44 = \ t, u, v, tm, var44, lam44, app44, tt44, pair44, fst44, snd44, left44, right44, split44, zero, suc, rec =>
     split44 _ _ _ _
          (t tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 split44 zero suc rec)
          (u tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 split44 zero suc rec)
          (v tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 split44 zero suc rec)

zero44 : {g:_} -> Tm44 g Main.nat44
zero44 = \ tm, var44, lam44, app44, tt44, pair44, fst44, snd44, left44, right44, split44, zero44, suc, rec =>
  zero44 _

suc44 : {g:_} -> Tm44 g Main.nat44 -> Tm44 g Main.nat44
suc44 = \ t, tm, var44, lam44, app44, tt44, pair44, fst44, snd44, left44, right44, split44, zero44, suc44, rec =>
   suc44 _ (t tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 split44 zero44 suc44 rec)

rec44 : {g:_}->{a:_} -> Tm44 g Main.nat44 -> Tm44 g (arr44 Main.nat44 (arr44 a a)) -> Tm44 g a -> Tm44 g a
rec44 = \ t, u, v, tm, var44, lam44, app44, tt44, pair44, fst44, snd44, left44, right44, split44, zero44, suc44, rec44 =>
     rec44 _ _
       (t tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 split44 zero44 suc44 rec44)
       (u tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 split44 zero44 suc44 rec44)
       (v tm var44 lam44 app44 tt44 pair44 fst44 snd44 left44 right44 split44 zero44 suc44 rec44)

v044 : {g:_}->{a:_} -> Tm44 (snoc44 g a) a
v044 = var44 vz44

v144 : {g:_}->{a:_}->{b:_} -> Tm44 (snoc44 (snoc44 g a) b) a
v144 = var44 (vs44 vz44)

v244 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm44 (snoc44 (snoc44 (snoc44 g a) b) c) a
v244 = var44 (vs44 (vs44 vz44))

v344 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm44 (snoc44 (snoc44 (snoc44 (snoc44 g a) b) c) d) a
v344 = var44 (vs44 (vs44 (vs44 vz44)))

tbool44 : Ty44
tbool44 = sum44 top44 top44

ttrue44 : {g:_} -> Tm44 g Main.tbool44
ttrue44 = left44 tt44

tfalse44 : {g:_} -> Tm44 g Main.tbool44
tfalse44 = right44 tt44

ifthenelse44 : {g:_}->{a:_} -> Tm44 g (arr44 Main.tbool44 (arr44 a (arr44 a a)))
ifthenelse44 = lam44 (lam44 (lam44 (split44 v244 (lam44 v244) (lam44 v144))))

times444 : {g:_}->{a:_} -> Tm44 g (arr44 (arr44 a a) (arr44 a a))
times444  = lam44 (lam44 (app44 v144 (app44 v144 (app44 v144 (app44 v144 v044)))))

add44 : {g:_} -> Tm44 g (arr44 Main.nat44 (arr44 Main.nat44 Main.nat44))
add44 = lam44 (rec44 v044
       (lam44 (lam44 (lam44 (suc44 (app44 v144 v044)))))
       (lam44 v044))

mul44 : {g:_} -> Tm44 g (arr44 Main.nat44 (arr44 Main.nat44 Main.nat44))
mul44 = lam44 (rec44 v044
       (lam44 (lam44 (lam44 (app44 (app44 add44 (app44 v144 v044)) v044))))
       (lam44 zero44))

fact44 : {g:_} -> Tm44 g (arr44 Main.nat44 Main.nat44)
fact44 = lam44 (rec44 v044 (lam44 (lam44 (app44 (app44 mul44 (suc44 v144)) v044)))
                 (suc44 zero44))

Ty45 : Type
Ty45 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat45 : Ty45
nat45 = \ _, nat45, _, _, _, _, _ => nat45
top45 : Ty45
top45 = \ _, _, top45, _, _, _, _ => top45
bot45 : Ty45
bot45 = \ _, _, _, bot45, _, _, _ => bot45

arr45 : Ty45-> Ty45-> Ty45
arr45 = \ a, b, ty, nat45, top45, bot45, arr45, prod, sum =>
     arr45 (a ty nat45 top45 bot45 arr45 prod sum) (b ty nat45 top45 bot45 arr45 prod sum)

prod45 : Ty45-> Ty45-> Ty45
prod45 = \ a, b, ty, nat45, top45, bot45, arr45, prod45, sum =>
     prod45 (a ty nat45 top45 bot45 arr45 prod45 sum) (b ty nat45 top45 bot45 arr45 prod45 sum)

sum45 : Ty45-> Ty45-> Ty45
sum45 = \ a, b, ty, nat45, top45, bot45, arr45, prod45, sum45 =>
     sum45 (a ty nat45 top45 bot45 arr45 prod45 sum45) (b ty nat45 top45 bot45 arr45 prod45 sum45)

Con45 : Type
Con45 = (Con45 : Type)
 -> (nil  : Con45)
 -> (snoc : Con45 -> Ty45-> Con45)
 -> Con45

nil45 : Con45
nil45 = \ con, nil45, snoc => nil45

snoc45 : Con45 -> Ty45-> Con45
snoc45 = \ g, a, con, nil45, snoc45 => snoc45 (g con nil45 snoc45) a

Var45 : Con45 -> Ty45-> Type
Var45 = \ g, a =>
    (Var45 : Con45 -> Ty45-> Type)
 -> (vz  : (g:_)->(a:_) -> Var45 (snoc45 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var45 g a -> Var45 (snoc45 g b) a)
 -> Var45 g a

vz45 : {g:_}->{a:_} -> Var45 (snoc45 g a) a
vz45 = \ var, vz45, vs => vz45 _ _

vs45 : {g:_}->{b:_}->{a:_} -> Var45 g a -> Var45 (snoc45 g b) a
vs45 = \ x, var, vz45, vs45 => vs45 _ _ _ (x var vz45 vs45)

Tm45 : Con45 -> Ty45-> Type
Tm45 = \ g, a =>
    (Tm45    : Con45 -> Ty45-> Type)
 -> (var   : (g:_)->(a:_)-> Var45 g a -> Tm45 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm45 (snoc45 g a) b -> Tm45 g (arr45 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm45 g (arr45 a b) -> Tm45 g a -> Tm45 g b)
 -> (tt    : (g:_)-> Tm45 g top45)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm45 g a -> Tm45 g b -> Tm45 g (prod45 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm45 g (prod45 a b) -> Tm45 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm45 g (prod45 a b) -> Tm45 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm45 g a -> Tm45 g (sum45 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm45 g b -> Tm45 g (sum45 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm45 g (sum45 a b) -> Tm45 g (arr45 a c) -> Tm45 g (arr45 b c) -> Tm45 g c)
 -> (zero  : (g:_)-> Tm45 g nat45)
 -> (suc   : (g:_)-> Tm45 g nat45 -> Tm45 g nat45)
 -> (rec   : (g:_)->(a:_) -> Tm45 g nat45 -> Tm45 g (arr45 nat45 (arr45 a a)) -> Tm45 g a -> Tm45 g a)
 -> Tm45 g a

var45 : {g:_}->{a:_} -> Var45 g a -> Tm45 g a
var45 = \ x, tm, var45, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var45 _ _ x

lam45 : {g:_}->{a:_}->{b:_}-> Tm45 (snoc45 g a) b -> Tm45 g (arr45 a b)
lam45 = \ t, tm, var45, lam45, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam45 _ _ _ (t tm var45 lam45 app tt pair fst snd left right split zero suc rec)

app45 : {g:_}->{a:_}->{b:_} -> Tm45 g (arr45 a b) -> Tm45 g a -> Tm45 g b
app45 = \ t, u, tm, var45, lam45, app45, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app45 _ _ _ (t tm var45 lam45 app45 tt pair fst snd left right split zero suc rec)
                (u tm var45 lam45 app45 tt pair fst snd left right split zero suc rec)

tt45 : {g:_} -> Tm45 g Main.top45
tt45 = \ tm, var45, lam45, app45, tt45, pair, fst, snd, left, right, split, zero, suc, rec => tt45 _

pair45 : {g:_}->{a:_}->{b:_} -> Tm45 g a -> Tm45 g b -> Tm45 g (prod45 a b)
pair45 = \ t, u, tm, var45, lam45, app45, tt45, pair45, fst, snd, left, right, split, zero, suc, rec =>
     pair45 _ _ _ (t tm var45 lam45 app45 tt45 pair45 fst snd left right split zero suc rec)
                 (u tm var45 lam45 app45 tt45 pair45 fst snd left right split zero suc rec)

fst45 : {g:_}->{a:_}->{b:_}-> Tm45 g (prod45 a b) -> Tm45 g a
fst45 = \ t, tm, var45, lam45, app45, tt45, pair45, fst45, snd, left, right, split, zero, suc, rec =>
     fst45 _ _ _ (t tm var45 lam45 app45 tt45 pair45 fst45 snd left right split zero suc rec)

snd45 : {g:_}->{a:_}->{b:_} -> Tm45 g (prod45 a b) -> Tm45 g b
snd45 = \ t, tm, var45, lam45, app45, tt45, pair45, fst45, snd45, left, right, split, zero, suc, rec =>
     snd45 _ _ _ (t tm var45 lam45 app45 tt45 pair45 fst45 snd45 left right split zero suc rec)

left45 : {g:_}->{a:_}->{b:_} -> Tm45 g a -> Tm45 g (sum45 a b)
left45 = \ t, tm, var45, lam45, app45, tt45, pair45, fst45, snd45, left45, right, split, zero, suc, rec =>
     left45 _ _ _ (t tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right split zero suc rec)

right45 : {g:_}->{a:_}->{b:_} -> Tm45 g b -> Tm45 g (sum45 a b)
right45 = \ t, tm, var45, lam45, app45, tt45, pair45, fst45, snd45, left45, right45, split, zero, suc, rec =>
     right45 _ _ _ (t tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 split zero suc rec)

split45 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm45 g (sum45 a b) -> Tm45 g (arr45 a c) -> Tm45 g (arr45 b c) -> Tm45 g c
split45 = \ t, u, v, tm, var45, lam45, app45, tt45, pair45, fst45, snd45, left45, right45, split45, zero, suc, rec =>
     split45 _ _ _ _
          (t tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 split45 zero suc rec)
          (u tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 split45 zero suc rec)
          (v tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 split45 zero suc rec)

zero45 : {g:_} -> Tm45 g Main.nat45
zero45 = \ tm, var45, lam45, app45, tt45, pair45, fst45, snd45, left45, right45, split45, zero45, suc, rec =>
  zero45 _

suc45 : {g:_} -> Tm45 g Main.nat45 -> Tm45 g Main.nat45
suc45 = \ t, tm, var45, lam45, app45, tt45, pair45, fst45, snd45, left45, right45, split45, zero45, suc45, rec =>
   suc45 _ (t tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 split45 zero45 suc45 rec)

rec45 : {g:_}->{a:_} -> Tm45 g Main.nat45 -> Tm45 g (arr45 Main.nat45 (arr45 a a)) -> Tm45 g a -> Tm45 g a
rec45 = \ t, u, v, tm, var45, lam45, app45, tt45, pair45, fst45, snd45, left45, right45, split45, zero45, suc45, rec45 =>
     rec45 _ _
       (t tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 split45 zero45 suc45 rec45)
       (u tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 split45 zero45 suc45 rec45)
       (v tm var45 lam45 app45 tt45 pair45 fst45 snd45 left45 right45 split45 zero45 suc45 rec45)

v045 : {g:_}->{a:_} -> Tm45 (snoc45 g a) a
v045 = var45 vz45

v145 : {g:_}->{a:_}->{b:_} -> Tm45 (snoc45 (snoc45 g a) b) a
v145 = var45 (vs45 vz45)

v245 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm45 (snoc45 (snoc45 (snoc45 g a) b) c) a
v245 = var45 (vs45 (vs45 vz45))

v345 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm45 (snoc45 (snoc45 (snoc45 (snoc45 g a) b) c) d) a
v345 = var45 (vs45 (vs45 (vs45 vz45)))

tbool45 : Ty45
tbool45 = sum45 top45 top45

ttrue45 : {g:_} -> Tm45 g Main.tbool45
ttrue45 = left45 tt45

tfalse45 : {g:_} -> Tm45 g Main.tbool45
tfalse45 = right45 tt45

ifthenelse45 : {g:_}->{a:_} -> Tm45 g (arr45 Main.tbool45 (arr45 a (arr45 a a)))
ifthenelse45 = lam45 (lam45 (lam45 (split45 v245 (lam45 v245) (lam45 v145))))

times445 : {g:_}->{a:_} -> Tm45 g (arr45 (arr45 a a) (arr45 a a))
times445  = lam45 (lam45 (app45 v145 (app45 v145 (app45 v145 (app45 v145 v045)))))

add45 : {g:_} -> Tm45 g (arr45 Main.nat45 (arr45 Main.nat45 Main.nat45))
add45 = lam45 (rec45 v045
       (lam45 (lam45 (lam45 (suc45 (app45 v145 v045)))))
       (lam45 v045))

mul45 : {g:_} -> Tm45 g (arr45 Main.nat45 (arr45 Main.nat45 Main.nat45))
mul45 = lam45 (rec45 v045
       (lam45 (lam45 (lam45 (app45 (app45 add45 (app45 v145 v045)) v045))))
       (lam45 zero45))

fact45 : {g:_} -> Tm45 g (arr45 Main.nat45 Main.nat45)
fact45 = lam45 (rec45 v045 (lam45 (lam45 (app45 (app45 mul45 (suc45 v145)) v045)))
                 (suc45 zero45))

Ty46 : Type
Ty46 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat46 : Ty46
nat46 = \ _, nat46, _, _, _, _, _ => nat46
top46 : Ty46
top46 = \ _, _, top46, _, _, _, _ => top46
bot46 : Ty46
bot46 = \ _, _, _, bot46, _, _, _ => bot46

arr46 : Ty46-> Ty46-> Ty46
arr46 = \ a, b, ty, nat46, top46, bot46, arr46, prod, sum =>
     arr46 (a ty nat46 top46 bot46 arr46 prod sum) (b ty nat46 top46 bot46 arr46 prod sum)

prod46 : Ty46-> Ty46-> Ty46
prod46 = \ a, b, ty, nat46, top46, bot46, arr46, prod46, sum =>
     prod46 (a ty nat46 top46 bot46 arr46 prod46 sum) (b ty nat46 top46 bot46 arr46 prod46 sum)

sum46 : Ty46-> Ty46-> Ty46
sum46 = \ a, b, ty, nat46, top46, bot46, arr46, prod46, sum46 =>
     sum46 (a ty nat46 top46 bot46 arr46 prod46 sum46) (b ty nat46 top46 bot46 arr46 prod46 sum46)

Con46 : Type
Con46 = (Con46 : Type)
 -> (nil  : Con46)
 -> (snoc : Con46 -> Ty46-> Con46)
 -> Con46

nil46 : Con46
nil46 = \ con, nil46, snoc => nil46

snoc46 : Con46 -> Ty46-> Con46
snoc46 = \ g, a, con, nil46, snoc46 => snoc46 (g con nil46 snoc46) a

Var46 : Con46 -> Ty46-> Type
Var46 = \ g, a =>
    (Var46 : Con46 -> Ty46-> Type)
 -> (vz  : (g:_)->(a:_) -> Var46 (snoc46 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var46 g a -> Var46 (snoc46 g b) a)
 -> Var46 g a

vz46 : {g:_}->{a:_} -> Var46 (snoc46 g a) a
vz46 = \ var, vz46, vs => vz46 _ _

vs46 : {g:_}->{b:_}->{a:_} -> Var46 g a -> Var46 (snoc46 g b) a
vs46 = \ x, var, vz46, vs46 => vs46 _ _ _ (x var vz46 vs46)

Tm46 : Con46 -> Ty46-> Type
Tm46 = \ g, a =>
    (Tm46    : Con46 -> Ty46-> Type)
 -> (var   : (g:_)->(a:_)-> Var46 g a -> Tm46 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm46 (snoc46 g a) b -> Tm46 g (arr46 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm46 g (arr46 a b) -> Tm46 g a -> Tm46 g b)
 -> (tt    : (g:_)-> Tm46 g top46)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm46 g a -> Tm46 g b -> Tm46 g (prod46 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm46 g (prod46 a b) -> Tm46 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm46 g (prod46 a b) -> Tm46 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm46 g a -> Tm46 g (sum46 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm46 g b -> Tm46 g (sum46 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm46 g (sum46 a b) -> Tm46 g (arr46 a c) -> Tm46 g (arr46 b c) -> Tm46 g c)
 -> (zero  : (g:_)-> Tm46 g nat46)
 -> (suc   : (g:_)-> Tm46 g nat46 -> Tm46 g nat46)
 -> (rec   : (g:_)->(a:_) -> Tm46 g nat46 -> Tm46 g (arr46 nat46 (arr46 a a)) -> Tm46 g a -> Tm46 g a)
 -> Tm46 g a

var46 : {g:_}->{a:_} -> Var46 g a -> Tm46 g a
var46 = \ x, tm, var46, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var46 _ _ x

lam46 : {g:_}->{a:_}->{b:_}-> Tm46 (snoc46 g a) b -> Tm46 g (arr46 a b)
lam46 = \ t, tm, var46, lam46, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam46 _ _ _ (t tm var46 lam46 app tt pair fst snd left right split zero suc rec)

app46 : {g:_}->{a:_}->{b:_} -> Tm46 g (arr46 a b) -> Tm46 g a -> Tm46 g b
app46 = \ t, u, tm, var46, lam46, app46, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app46 _ _ _ (t tm var46 lam46 app46 tt pair fst snd left right split zero suc rec)
                (u tm var46 lam46 app46 tt pair fst snd left right split zero suc rec)

tt46 : {g:_} -> Tm46 g Main.top46
tt46 = \ tm, var46, lam46, app46, tt46, pair, fst, snd, left, right, split, zero, suc, rec => tt46 _

pair46 : {g:_}->{a:_}->{b:_} -> Tm46 g a -> Tm46 g b -> Tm46 g (prod46 a b)
pair46 = \ t, u, tm, var46, lam46, app46, tt46, pair46, fst, snd, left, right, split, zero, suc, rec =>
     pair46 _ _ _ (t tm var46 lam46 app46 tt46 pair46 fst snd left right split zero suc rec)
                 (u tm var46 lam46 app46 tt46 pair46 fst snd left right split zero suc rec)

fst46 : {g:_}->{a:_}->{b:_}-> Tm46 g (prod46 a b) -> Tm46 g a
fst46 = \ t, tm, var46, lam46, app46, tt46, pair46, fst46, snd, left, right, split, zero, suc, rec =>
     fst46 _ _ _ (t tm var46 lam46 app46 tt46 pair46 fst46 snd left right split zero suc rec)

snd46 : {g:_}->{a:_}->{b:_} -> Tm46 g (prod46 a b) -> Tm46 g b
snd46 = \ t, tm, var46, lam46, app46, tt46, pair46, fst46, snd46, left, right, split, zero, suc, rec =>
     snd46 _ _ _ (t tm var46 lam46 app46 tt46 pair46 fst46 snd46 left right split zero suc rec)

left46 : {g:_}->{a:_}->{b:_} -> Tm46 g a -> Tm46 g (sum46 a b)
left46 = \ t, tm, var46, lam46, app46, tt46, pair46, fst46, snd46, left46, right, split, zero, suc, rec =>
     left46 _ _ _ (t tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right split zero suc rec)

right46 : {g:_}->{a:_}->{b:_} -> Tm46 g b -> Tm46 g (sum46 a b)
right46 = \ t, tm, var46, lam46, app46, tt46, pair46, fst46, snd46, left46, right46, split, zero, suc, rec =>
     right46 _ _ _ (t tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 split zero suc rec)

split46 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm46 g (sum46 a b) -> Tm46 g (arr46 a c) -> Tm46 g (arr46 b c) -> Tm46 g c
split46 = \ t, u, v, tm, var46, lam46, app46, tt46, pair46, fst46, snd46, left46, right46, split46, zero, suc, rec =>
     split46 _ _ _ _
          (t tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 split46 zero suc rec)
          (u tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 split46 zero suc rec)
          (v tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 split46 zero suc rec)

zero46 : {g:_} -> Tm46 g Main.nat46
zero46 = \ tm, var46, lam46, app46, tt46, pair46, fst46, snd46, left46, right46, split46, zero46, suc, rec =>
  zero46 _

suc46 : {g:_} -> Tm46 g Main.nat46 -> Tm46 g Main.nat46
suc46 = \ t, tm, var46, lam46, app46, tt46, pair46, fst46, snd46, left46, right46, split46, zero46, suc46, rec =>
   suc46 _ (t tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 split46 zero46 suc46 rec)

rec46 : {g:_}->{a:_} -> Tm46 g Main.nat46 -> Tm46 g (arr46 Main.nat46 (arr46 a a)) -> Tm46 g a -> Tm46 g a
rec46 = \ t, u, v, tm, var46, lam46, app46, tt46, pair46, fst46, snd46, left46, right46, split46, zero46, suc46, rec46 =>
     rec46 _ _
       (t tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 split46 zero46 suc46 rec46)
       (u tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 split46 zero46 suc46 rec46)
       (v tm var46 lam46 app46 tt46 pair46 fst46 snd46 left46 right46 split46 zero46 suc46 rec46)

v046 : {g:_}->{a:_} -> Tm46 (snoc46 g a) a
v046 = var46 vz46

v146 : {g:_}->{a:_}->{b:_} -> Tm46 (snoc46 (snoc46 g a) b) a
v146 = var46 (vs46 vz46)

v246 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm46 (snoc46 (snoc46 (snoc46 g a) b) c) a
v246 = var46 (vs46 (vs46 vz46))

v346 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm46 (snoc46 (snoc46 (snoc46 (snoc46 g a) b) c) d) a
v346 = var46 (vs46 (vs46 (vs46 vz46)))

tbool46 : Ty46
tbool46 = sum46 top46 top46

ttrue46 : {g:_} -> Tm46 g Main.tbool46
ttrue46 = left46 tt46

tfalse46 : {g:_} -> Tm46 g Main.tbool46
tfalse46 = right46 tt46

ifthenelse46 : {g:_}->{a:_} -> Tm46 g (arr46 Main.tbool46 (arr46 a (arr46 a a)))
ifthenelse46 = lam46 (lam46 (lam46 (split46 v246 (lam46 v246) (lam46 v146))))

times446 : {g:_}->{a:_} -> Tm46 g (arr46 (arr46 a a) (arr46 a a))
times446  = lam46 (lam46 (app46 v146 (app46 v146 (app46 v146 (app46 v146 v046)))))

add46 : {g:_} -> Tm46 g (arr46 Main.nat46 (arr46 Main.nat46 Main.nat46))
add46 = lam46 (rec46 v046
       (lam46 (lam46 (lam46 (suc46 (app46 v146 v046)))))
       (lam46 v046))

mul46 : {g:_} -> Tm46 g (arr46 Main.nat46 (arr46 Main.nat46 Main.nat46))
mul46 = lam46 (rec46 v046
       (lam46 (lam46 (lam46 (app46 (app46 add46 (app46 v146 v046)) v046))))
       (lam46 zero46))

fact46 : {g:_} -> Tm46 g (arr46 Main.nat46 Main.nat46)
fact46 = lam46 (rec46 v046 (lam46 (lam46 (app46 (app46 mul46 (suc46 v146)) v046)))
                 (suc46 zero46))

Ty47 : Type
Ty47 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat47 : Ty47
nat47 = \ _, nat47, _, _, _, _, _ => nat47
top47 : Ty47
top47 = \ _, _, top47, _, _, _, _ => top47
bot47 : Ty47
bot47 = \ _, _, _, bot47, _, _, _ => bot47

arr47 : Ty47-> Ty47-> Ty47
arr47 = \ a, b, ty, nat47, top47, bot47, arr47, prod, sum =>
     arr47 (a ty nat47 top47 bot47 arr47 prod sum) (b ty nat47 top47 bot47 arr47 prod sum)

prod47 : Ty47-> Ty47-> Ty47
prod47 = \ a, b, ty, nat47, top47, bot47, arr47, prod47, sum =>
     prod47 (a ty nat47 top47 bot47 arr47 prod47 sum) (b ty nat47 top47 bot47 arr47 prod47 sum)

sum47 : Ty47-> Ty47-> Ty47
sum47 = \ a, b, ty, nat47, top47, bot47, arr47, prod47, sum47 =>
     sum47 (a ty nat47 top47 bot47 arr47 prod47 sum47) (b ty nat47 top47 bot47 arr47 prod47 sum47)

Con47 : Type
Con47 = (Con47 : Type)
 -> (nil  : Con47)
 -> (snoc : Con47 -> Ty47-> Con47)
 -> Con47

nil47 : Con47
nil47 = \ con, nil47, snoc => nil47

snoc47 : Con47 -> Ty47-> Con47
snoc47 = \ g, a, con, nil47, snoc47 => snoc47 (g con nil47 snoc47) a

Var47 : Con47 -> Ty47-> Type
Var47 = \ g, a =>
    (Var47 : Con47 -> Ty47-> Type)
 -> (vz  : (g:_)->(a:_) -> Var47 (snoc47 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var47 g a -> Var47 (snoc47 g b) a)
 -> Var47 g a

vz47 : {g:_}->{a:_} -> Var47 (snoc47 g a) a
vz47 = \ var, vz47, vs => vz47 _ _

vs47 : {g:_}->{b:_}->{a:_} -> Var47 g a -> Var47 (snoc47 g b) a
vs47 = \ x, var, vz47, vs47 => vs47 _ _ _ (x var vz47 vs47)

Tm47 : Con47 -> Ty47-> Type
Tm47 = \ g, a =>
    (Tm47    : Con47 -> Ty47-> Type)
 -> (var   : (g:_)->(a:_)-> Var47 g a -> Tm47 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm47 (snoc47 g a) b -> Tm47 g (arr47 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm47 g (arr47 a b) -> Tm47 g a -> Tm47 g b)
 -> (tt    : (g:_)-> Tm47 g top47)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm47 g a -> Tm47 g b -> Tm47 g (prod47 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm47 g (prod47 a b) -> Tm47 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm47 g (prod47 a b) -> Tm47 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm47 g a -> Tm47 g (sum47 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm47 g b -> Tm47 g (sum47 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm47 g (sum47 a b) -> Tm47 g (arr47 a c) -> Tm47 g (arr47 b c) -> Tm47 g c)
 -> (zero  : (g:_)-> Tm47 g nat47)
 -> (suc   : (g:_)-> Tm47 g nat47 -> Tm47 g nat47)
 -> (rec   : (g:_)->(a:_) -> Tm47 g nat47 -> Tm47 g (arr47 nat47 (arr47 a a)) -> Tm47 g a -> Tm47 g a)
 -> Tm47 g a

var47 : {g:_}->{a:_} -> Var47 g a -> Tm47 g a
var47 = \ x, tm, var47, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var47 _ _ x

lam47 : {g:_}->{a:_}->{b:_}-> Tm47 (snoc47 g a) b -> Tm47 g (arr47 a b)
lam47 = \ t, tm, var47, lam47, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam47 _ _ _ (t tm var47 lam47 app tt pair fst snd left right split zero suc rec)

app47 : {g:_}->{a:_}->{b:_} -> Tm47 g (arr47 a b) -> Tm47 g a -> Tm47 g b
app47 = \ t, u, tm, var47, lam47, app47, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app47 _ _ _ (t tm var47 lam47 app47 tt pair fst snd left right split zero suc rec)
                (u tm var47 lam47 app47 tt pair fst snd left right split zero suc rec)

tt47 : {g:_} -> Tm47 g Main.top47
tt47 = \ tm, var47, lam47, app47, tt47, pair, fst, snd, left, right, split, zero, suc, rec => tt47 _

pair47 : {g:_}->{a:_}->{b:_} -> Tm47 g a -> Tm47 g b -> Tm47 g (prod47 a b)
pair47 = \ t, u, tm, var47, lam47, app47, tt47, pair47, fst, snd, left, right, split, zero, suc, rec =>
     pair47 _ _ _ (t tm var47 lam47 app47 tt47 pair47 fst snd left right split zero suc rec)
                 (u tm var47 lam47 app47 tt47 pair47 fst snd left right split zero suc rec)

fst47 : {g:_}->{a:_}->{b:_}-> Tm47 g (prod47 a b) -> Tm47 g a
fst47 = \ t, tm, var47, lam47, app47, tt47, pair47, fst47, snd, left, right, split, zero, suc, rec =>
     fst47 _ _ _ (t tm var47 lam47 app47 tt47 pair47 fst47 snd left right split zero suc rec)

snd47 : {g:_}->{a:_}->{b:_} -> Tm47 g (prod47 a b) -> Tm47 g b
snd47 = \ t, tm, var47, lam47, app47, tt47, pair47, fst47, snd47, left, right, split, zero, suc, rec =>
     snd47 _ _ _ (t tm var47 lam47 app47 tt47 pair47 fst47 snd47 left right split zero suc rec)

left47 : {g:_}->{a:_}->{b:_} -> Tm47 g a -> Tm47 g (sum47 a b)
left47 = \ t, tm, var47, lam47, app47, tt47, pair47, fst47, snd47, left47, right, split, zero, suc, rec =>
     left47 _ _ _ (t tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right split zero suc rec)

right47 : {g:_}->{a:_}->{b:_} -> Tm47 g b -> Tm47 g (sum47 a b)
right47 = \ t, tm, var47, lam47, app47, tt47, pair47, fst47, snd47, left47, right47, split, zero, suc, rec =>
     right47 _ _ _ (t tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 split zero suc rec)

split47 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm47 g (sum47 a b) -> Tm47 g (arr47 a c) -> Tm47 g (arr47 b c) -> Tm47 g c
split47 = \ t, u, v, tm, var47, lam47, app47, tt47, pair47, fst47, snd47, left47, right47, split47, zero, suc, rec =>
     split47 _ _ _ _
          (t tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 split47 zero suc rec)
          (u tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 split47 zero suc rec)
          (v tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 split47 zero suc rec)

zero47 : {g:_} -> Tm47 g Main.nat47
zero47 = \ tm, var47, lam47, app47, tt47, pair47, fst47, snd47, left47, right47, split47, zero47, suc, rec =>
  zero47 _

suc47 : {g:_} -> Tm47 g Main.nat47 -> Tm47 g Main.nat47
suc47 = \ t, tm, var47, lam47, app47, tt47, pair47, fst47, snd47, left47, right47, split47, zero47, suc47, rec =>
   suc47 _ (t tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 split47 zero47 suc47 rec)

rec47 : {g:_}->{a:_} -> Tm47 g Main.nat47 -> Tm47 g (arr47 Main.nat47 (arr47 a a)) -> Tm47 g a -> Tm47 g a
rec47 = \ t, u, v, tm, var47, lam47, app47, tt47, pair47, fst47, snd47, left47, right47, split47, zero47, suc47, rec47 =>
     rec47 _ _
       (t tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 split47 zero47 suc47 rec47)
       (u tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 split47 zero47 suc47 rec47)
       (v tm var47 lam47 app47 tt47 pair47 fst47 snd47 left47 right47 split47 zero47 suc47 rec47)

v047 : {g:_}->{a:_} -> Tm47 (snoc47 g a) a
v047 = var47 vz47

v147 : {g:_}->{a:_}->{b:_} -> Tm47 (snoc47 (snoc47 g a) b) a
v147 = var47 (vs47 vz47)

v247 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm47 (snoc47 (snoc47 (snoc47 g a) b) c) a
v247 = var47 (vs47 (vs47 vz47))

v347 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm47 (snoc47 (snoc47 (snoc47 (snoc47 g a) b) c) d) a
v347 = var47 (vs47 (vs47 (vs47 vz47)))

tbool47 : Ty47
tbool47 = sum47 top47 top47

ttrue47 : {g:_} -> Tm47 g Main.tbool47
ttrue47 = left47 tt47

tfalse47 : {g:_} -> Tm47 g Main.tbool47
tfalse47 = right47 tt47

ifthenelse47 : {g:_}->{a:_} -> Tm47 g (arr47 Main.tbool47 (arr47 a (arr47 a a)))
ifthenelse47 = lam47 (lam47 (lam47 (split47 v247 (lam47 v247) (lam47 v147))))

times447 : {g:_}->{a:_} -> Tm47 g (arr47 (arr47 a a) (arr47 a a))
times447  = lam47 (lam47 (app47 v147 (app47 v147 (app47 v147 (app47 v147 v047)))))

add47 : {g:_} -> Tm47 g (arr47 Main.nat47 (arr47 Main.nat47 Main.nat47))
add47 = lam47 (rec47 v047
       (lam47 (lam47 (lam47 (suc47 (app47 v147 v047)))))
       (lam47 v047))

mul47 : {g:_} -> Tm47 g (arr47 Main.nat47 (arr47 Main.nat47 Main.nat47))
mul47 = lam47 (rec47 v047
       (lam47 (lam47 (lam47 (app47 (app47 add47 (app47 v147 v047)) v047))))
       (lam47 zero47))

fact47 : {g:_} -> Tm47 g (arr47 Main.nat47 Main.nat47)
fact47 = lam47 (rec47 v047 (lam47 (lam47 (app47 (app47 mul47 (suc47 v147)) v047)))
                 (suc47 zero47))

Ty48 : Type
Ty48 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat48 : Ty48
nat48 = \ _, nat48, _, _, _, _, _ => nat48
top48 : Ty48
top48 = \ _, _, top48, _, _, _, _ => top48
bot48 : Ty48
bot48 = \ _, _, _, bot48, _, _, _ => bot48

arr48 : Ty48-> Ty48-> Ty48
arr48 = \ a, b, ty, nat48, top48, bot48, arr48, prod, sum =>
     arr48 (a ty nat48 top48 bot48 arr48 prod sum) (b ty nat48 top48 bot48 arr48 prod sum)

prod48 : Ty48-> Ty48-> Ty48
prod48 = \ a, b, ty, nat48, top48, bot48, arr48, prod48, sum =>
     prod48 (a ty nat48 top48 bot48 arr48 prod48 sum) (b ty nat48 top48 bot48 arr48 prod48 sum)

sum48 : Ty48-> Ty48-> Ty48
sum48 = \ a, b, ty, nat48, top48, bot48, arr48, prod48, sum48 =>
     sum48 (a ty nat48 top48 bot48 arr48 prod48 sum48) (b ty nat48 top48 bot48 arr48 prod48 sum48)

Con48 : Type
Con48 = (Con48 : Type)
 -> (nil  : Con48)
 -> (snoc : Con48 -> Ty48-> Con48)
 -> Con48

nil48 : Con48
nil48 = \ con, nil48, snoc => nil48

snoc48 : Con48 -> Ty48-> Con48
snoc48 = \ g, a, con, nil48, snoc48 => snoc48 (g con nil48 snoc48) a

Var48 : Con48 -> Ty48-> Type
Var48 = \ g, a =>
    (Var48 : Con48 -> Ty48-> Type)
 -> (vz  : (g:_)->(a:_) -> Var48 (snoc48 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var48 g a -> Var48 (snoc48 g b) a)
 -> Var48 g a

vz48 : {g:_}->{a:_} -> Var48 (snoc48 g a) a
vz48 = \ var, vz48, vs => vz48 _ _

vs48 : {g:_}->{b:_}->{a:_} -> Var48 g a -> Var48 (snoc48 g b) a
vs48 = \ x, var, vz48, vs48 => vs48 _ _ _ (x var vz48 vs48)

Tm48 : Con48 -> Ty48-> Type
Tm48 = \ g, a =>
    (Tm48    : Con48 -> Ty48-> Type)
 -> (var   : (g:_)->(a:_)-> Var48 g a -> Tm48 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm48 (snoc48 g a) b -> Tm48 g (arr48 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm48 g (arr48 a b) -> Tm48 g a -> Tm48 g b)
 -> (tt    : (g:_)-> Tm48 g top48)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm48 g a -> Tm48 g b -> Tm48 g (prod48 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm48 g (prod48 a b) -> Tm48 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm48 g (prod48 a b) -> Tm48 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm48 g a -> Tm48 g (sum48 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm48 g b -> Tm48 g (sum48 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm48 g (sum48 a b) -> Tm48 g (arr48 a c) -> Tm48 g (arr48 b c) -> Tm48 g c)
 -> (zero  : (g:_)-> Tm48 g nat48)
 -> (suc   : (g:_)-> Tm48 g nat48 -> Tm48 g nat48)
 -> (rec   : (g:_)->(a:_) -> Tm48 g nat48 -> Tm48 g (arr48 nat48 (arr48 a a)) -> Tm48 g a -> Tm48 g a)
 -> Tm48 g a

var48 : {g:_}->{a:_} -> Var48 g a -> Tm48 g a
var48 = \ x, tm, var48, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var48 _ _ x

lam48 : {g:_}->{a:_}->{b:_}-> Tm48 (snoc48 g a) b -> Tm48 g (arr48 a b)
lam48 = \ t, tm, var48, lam48, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam48 _ _ _ (t tm var48 lam48 app tt pair fst snd left right split zero suc rec)

app48 : {g:_}->{a:_}->{b:_} -> Tm48 g (arr48 a b) -> Tm48 g a -> Tm48 g b
app48 = \ t, u, tm, var48, lam48, app48, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app48 _ _ _ (t tm var48 lam48 app48 tt pair fst snd left right split zero suc rec)
                (u tm var48 lam48 app48 tt pair fst snd left right split zero suc rec)

tt48 : {g:_} -> Tm48 g Main.top48
tt48 = \ tm, var48, lam48, app48, tt48, pair, fst, snd, left, right, split, zero, suc, rec => tt48 _

pair48 : {g:_}->{a:_}->{b:_} -> Tm48 g a -> Tm48 g b -> Tm48 g (prod48 a b)
pair48 = \ t, u, tm, var48, lam48, app48, tt48, pair48, fst, snd, left, right, split, zero, suc, rec =>
     pair48 _ _ _ (t tm var48 lam48 app48 tt48 pair48 fst snd left right split zero suc rec)
                 (u tm var48 lam48 app48 tt48 pair48 fst snd left right split zero suc rec)

fst48 : {g:_}->{a:_}->{b:_}-> Tm48 g (prod48 a b) -> Tm48 g a
fst48 = \ t, tm, var48, lam48, app48, tt48, pair48, fst48, snd, left, right, split, zero, suc, rec =>
     fst48 _ _ _ (t tm var48 lam48 app48 tt48 pair48 fst48 snd left right split zero suc rec)

snd48 : {g:_}->{a:_}->{b:_} -> Tm48 g (prod48 a b) -> Tm48 g b
snd48 = \ t, tm, var48, lam48, app48, tt48, pair48, fst48, snd48, left, right, split, zero, suc, rec =>
     snd48 _ _ _ (t tm var48 lam48 app48 tt48 pair48 fst48 snd48 left right split zero suc rec)

left48 : {g:_}->{a:_}->{b:_} -> Tm48 g a -> Tm48 g (sum48 a b)
left48 = \ t, tm, var48, lam48, app48, tt48, pair48, fst48, snd48, left48, right, split, zero, suc, rec =>
     left48 _ _ _ (t tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right split zero suc rec)

right48 : {g:_}->{a:_}->{b:_} -> Tm48 g b -> Tm48 g (sum48 a b)
right48 = \ t, tm, var48, lam48, app48, tt48, pair48, fst48, snd48, left48, right48, split, zero, suc, rec =>
     right48 _ _ _ (t tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 split zero suc rec)

split48 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm48 g (sum48 a b) -> Tm48 g (arr48 a c) -> Tm48 g (arr48 b c) -> Tm48 g c
split48 = \ t, u, v, tm, var48, lam48, app48, tt48, pair48, fst48, snd48, left48, right48, split48, zero, suc, rec =>
     split48 _ _ _ _
          (t tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 split48 zero suc rec)
          (u tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 split48 zero suc rec)
          (v tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 split48 zero suc rec)

zero48 : {g:_} -> Tm48 g Main.nat48
zero48 = \ tm, var48, lam48, app48, tt48, pair48, fst48, snd48, left48, right48, split48, zero48, suc, rec =>
  zero48 _

suc48 : {g:_} -> Tm48 g Main.nat48 -> Tm48 g Main.nat48
suc48 = \ t, tm, var48, lam48, app48, tt48, pair48, fst48, snd48, left48, right48, split48, zero48, suc48, rec =>
   suc48 _ (t tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 split48 zero48 suc48 rec)

rec48 : {g:_}->{a:_} -> Tm48 g Main.nat48 -> Tm48 g (arr48 Main.nat48 (arr48 a a)) -> Tm48 g a -> Tm48 g a
rec48 = \ t, u, v, tm, var48, lam48, app48, tt48, pair48, fst48, snd48, left48, right48, split48, zero48, suc48, rec48 =>
     rec48 _ _
       (t tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 split48 zero48 suc48 rec48)
       (u tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 split48 zero48 suc48 rec48)
       (v tm var48 lam48 app48 tt48 pair48 fst48 snd48 left48 right48 split48 zero48 suc48 rec48)

v048 : {g:_}->{a:_} -> Tm48 (snoc48 g a) a
v048 = var48 vz48

v148 : {g:_}->{a:_}->{b:_} -> Tm48 (snoc48 (snoc48 g a) b) a
v148 = var48 (vs48 vz48)

v248 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm48 (snoc48 (snoc48 (snoc48 g a) b) c) a
v248 = var48 (vs48 (vs48 vz48))

v348 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm48 (snoc48 (snoc48 (snoc48 (snoc48 g a) b) c) d) a
v348 = var48 (vs48 (vs48 (vs48 vz48)))

tbool48 : Ty48
tbool48 = sum48 top48 top48

ttrue48 : {g:_} -> Tm48 g Main.tbool48
ttrue48 = left48 tt48

tfalse48 : {g:_} -> Tm48 g Main.tbool48
tfalse48 = right48 tt48

ifthenelse48 : {g:_}->{a:_} -> Tm48 g (arr48 Main.tbool48 (arr48 a (arr48 a a)))
ifthenelse48 = lam48 (lam48 (lam48 (split48 v248 (lam48 v248) (lam48 v148))))

times448 : {g:_}->{a:_} -> Tm48 g (arr48 (arr48 a a) (arr48 a a))
times448  = lam48 (lam48 (app48 v148 (app48 v148 (app48 v148 (app48 v148 v048)))))

add48 : {g:_} -> Tm48 g (arr48 Main.nat48 (arr48 Main.nat48 Main.nat48))
add48 = lam48 (rec48 v048
       (lam48 (lam48 (lam48 (suc48 (app48 v148 v048)))))
       (lam48 v048))

mul48 : {g:_} -> Tm48 g (arr48 Main.nat48 (arr48 Main.nat48 Main.nat48))
mul48 = lam48 (rec48 v048
       (lam48 (lam48 (lam48 (app48 (app48 add48 (app48 v148 v048)) v048))))
       (lam48 zero48))

fact48 : {g:_} -> Tm48 g (arr48 Main.nat48 Main.nat48)
fact48 = lam48 (rec48 v048 (lam48 (lam48 (app48 (app48 mul48 (suc48 v148)) v048)))
                 (suc48 zero48))

Ty49 : Type
Ty49 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat49 : Ty49
nat49 = \ _, nat49, _, _, _, _, _ => nat49
top49 : Ty49
top49 = \ _, _, top49, _, _, _, _ => top49
bot49 : Ty49
bot49 = \ _, _, _, bot49, _, _, _ => bot49

arr49 : Ty49-> Ty49-> Ty49
arr49 = \ a, b, ty, nat49, top49, bot49, arr49, prod, sum =>
     arr49 (a ty nat49 top49 bot49 arr49 prod sum) (b ty nat49 top49 bot49 arr49 prod sum)

prod49 : Ty49-> Ty49-> Ty49
prod49 = \ a, b, ty, nat49, top49, bot49, arr49, prod49, sum =>
     prod49 (a ty nat49 top49 bot49 arr49 prod49 sum) (b ty nat49 top49 bot49 arr49 prod49 sum)

sum49 : Ty49-> Ty49-> Ty49
sum49 = \ a, b, ty, nat49, top49, bot49, arr49, prod49, sum49 =>
     sum49 (a ty nat49 top49 bot49 arr49 prod49 sum49) (b ty nat49 top49 bot49 arr49 prod49 sum49)

Con49 : Type
Con49 = (Con49 : Type)
 -> (nil  : Con49)
 -> (snoc : Con49 -> Ty49-> Con49)
 -> Con49

nil49 : Con49
nil49 = \ con, nil49, snoc => nil49

snoc49 : Con49 -> Ty49-> Con49
snoc49 = \ g, a, con, nil49, snoc49 => snoc49 (g con nil49 snoc49) a

Var49 : Con49 -> Ty49-> Type
Var49 = \ g, a =>
    (Var49 : Con49 -> Ty49-> Type)
 -> (vz  : (g:_)->(a:_) -> Var49 (snoc49 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var49 g a -> Var49 (snoc49 g b) a)
 -> Var49 g a

vz49 : {g:_}->{a:_} -> Var49 (snoc49 g a) a
vz49 = \ var, vz49, vs => vz49 _ _

vs49 : {g:_}->{b:_}->{a:_} -> Var49 g a -> Var49 (snoc49 g b) a
vs49 = \ x, var, vz49, vs49 => vs49 _ _ _ (x var vz49 vs49)

Tm49 : Con49 -> Ty49-> Type
Tm49 = \ g, a =>
    (Tm49    : Con49 -> Ty49-> Type)
 -> (var   : (g:_)->(a:_)-> Var49 g a -> Tm49 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm49 (snoc49 g a) b -> Tm49 g (arr49 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm49 g (arr49 a b) -> Tm49 g a -> Tm49 g b)
 -> (tt    : (g:_)-> Tm49 g top49)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm49 g a -> Tm49 g b -> Tm49 g (prod49 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm49 g (prod49 a b) -> Tm49 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm49 g (prod49 a b) -> Tm49 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm49 g a -> Tm49 g (sum49 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm49 g b -> Tm49 g (sum49 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm49 g (sum49 a b) -> Tm49 g (arr49 a c) -> Tm49 g (arr49 b c) -> Tm49 g c)
 -> (zero  : (g:_)-> Tm49 g nat49)
 -> (suc   : (g:_)-> Tm49 g nat49 -> Tm49 g nat49)
 -> (rec   : (g:_)->(a:_) -> Tm49 g nat49 -> Tm49 g (arr49 nat49 (arr49 a a)) -> Tm49 g a -> Tm49 g a)
 -> Tm49 g a

var49 : {g:_}->{a:_} -> Var49 g a -> Tm49 g a
var49 = \ x, tm, var49, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var49 _ _ x

lam49 : {g:_}->{a:_}->{b:_}-> Tm49 (snoc49 g a) b -> Tm49 g (arr49 a b)
lam49 = \ t, tm, var49, lam49, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam49 _ _ _ (t tm var49 lam49 app tt pair fst snd left right split zero suc rec)

app49 : {g:_}->{a:_}->{b:_} -> Tm49 g (arr49 a b) -> Tm49 g a -> Tm49 g b
app49 = \ t, u, tm, var49, lam49, app49, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app49 _ _ _ (t tm var49 lam49 app49 tt pair fst snd left right split zero suc rec)
                (u tm var49 lam49 app49 tt pair fst snd left right split zero suc rec)

tt49 : {g:_} -> Tm49 g Main.top49
tt49 = \ tm, var49, lam49, app49, tt49, pair, fst, snd, left, right, split, zero, suc, rec => tt49 _

pair49 : {g:_}->{a:_}->{b:_} -> Tm49 g a -> Tm49 g b -> Tm49 g (prod49 a b)
pair49 = \ t, u, tm, var49, lam49, app49, tt49, pair49, fst, snd, left, right, split, zero, suc, rec =>
     pair49 _ _ _ (t tm var49 lam49 app49 tt49 pair49 fst snd left right split zero suc rec)
                 (u tm var49 lam49 app49 tt49 pair49 fst snd left right split zero suc rec)

fst49 : {g:_}->{a:_}->{b:_}-> Tm49 g (prod49 a b) -> Tm49 g a
fst49 = \ t, tm, var49, lam49, app49, tt49, pair49, fst49, snd, left, right, split, zero, suc, rec =>
     fst49 _ _ _ (t tm var49 lam49 app49 tt49 pair49 fst49 snd left right split zero suc rec)

snd49 : {g:_}->{a:_}->{b:_} -> Tm49 g (prod49 a b) -> Tm49 g b
snd49 = \ t, tm, var49, lam49, app49, tt49, pair49, fst49, snd49, left, right, split, zero, suc, rec =>
     snd49 _ _ _ (t tm var49 lam49 app49 tt49 pair49 fst49 snd49 left right split zero suc rec)

left49 : {g:_}->{a:_}->{b:_} -> Tm49 g a -> Tm49 g (sum49 a b)
left49 = \ t, tm, var49, lam49, app49, tt49, pair49, fst49, snd49, left49, right, split, zero, suc, rec =>
     left49 _ _ _ (t tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right split zero suc rec)

right49 : {g:_}->{a:_}->{b:_} -> Tm49 g b -> Tm49 g (sum49 a b)
right49 = \ t, tm, var49, lam49, app49, tt49, pair49, fst49, snd49, left49, right49, split, zero, suc, rec =>
     right49 _ _ _ (t tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 split zero suc rec)

split49 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm49 g (sum49 a b) -> Tm49 g (arr49 a c) -> Tm49 g (arr49 b c) -> Tm49 g c
split49 = \ t, u, v, tm, var49, lam49, app49, tt49, pair49, fst49, snd49, left49, right49, split49, zero, suc, rec =>
     split49 _ _ _ _
          (t tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 split49 zero suc rec)
          (u tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 split49 zero suc rec)
          (v tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 split49 zero suc rec)

zero49 : {g:_} -> Tm49 g Main.nat49
zero49 = \ tm, var49, lam49, app49, tt49, pair49, fst49, snd49, left49, right49, split49, zero49, suc, rec =>
  zero49 _

suc49 : {g:_} -> Tm49 g Main.nat49 -> Tm49 g Main.nat49
suc49 = \ t, tm, var49, lam49, app49, tt49, pair49, fst49, snd49, left49, right49, split49, zero49, suc49, rec =>
   suc49 _ (t tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 split49 zero49 suc49 rec)

rec49 : {g:_}->{a:_} -> Tm49 g Main.nat49 -> Tm49 g (arr49 Main.nat49 (arr49 a a)) -> Tm49 g a -> Tm49 g a
rec49 = \ t, u, v, tm, var49, lam49, app49, tt49, pair49, fst49, snd49, left49, right49, split49, zero49, suc49, rec49 =>
     rec49 _ _
       (t tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 split49 zero49 suc49 rec49)
       (u tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 split49 zero49 suc49 rec49)
       (v tm var49 lam49 app49 tt49 pair49 fst49 snd49 left49 right49 split49 zero49 suc49 rec49)

v049 : {g:_}->{a:_} -> Tm49 (snoc49 g a) a
v049 = var49 vz49

v149 : {g:_}->{a:_}->{b:_} -> Tm49 (snoc49 (snoc49 g a) b) a
v149 = var49 (vs49 vz49)

v249 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm49 (snoc49 (snoc49 (snoc49 g a) b) c) a
v249 = var49 (vs49 (vs49 vz49))

v349 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm49 (snoc49 (snoc49 (snoc49 (snoc49 g a) b) c) d) a
v349 = var49 (vs49 (vs49 (vs49 vz49)))

tbool49 : Ty49
tbool49 = sum49 top49 top49

ttrue49 : {g:_} -> Tm49 g Main.tbool49
ttrue49 = left49 tt49

tfalse49 : {g:_} -> Tm49 g Main.tbool49
tfalse49 = right49 tt49

ifthenelse49 : {g:_}->{a:_} -> Tm49 g (arr49 Main.tbool49 (arr49 a (arr49 a a)))
ifthenelse49 = lam49 (lam49 (lam49 (split49 v249 (lam49 v249) (lam49 v149))))

times449 : {g:_}->{a:_} -> Tm49 g (arr49 (arr49 a a) (arr49 a a))
times449  = lam49 (lam49 (app49 v149 (app49 v149 (app49 v149 (app49 v149 v049)))))

add49 : {g:_} -> Tm49 g (arr49 Main.nat49 (arr49 Main.nat49 Main.nat49))
add49 = lam49 (rec49 v049
       (lam49 (lam49 (lam49 (suc49 (app49 v149 v049)))))
       (lam49 v049))

mul49 : {g:_} -> Tm49 g (arr49 Main.nat49 (arr49 Main.nat49 Main.nat49))
mul49 = lam49 (rec49 v049
       (lam49 (lam49 (lam49 (app49 (app49 add49 (app49 v149 v049)) v049))))
       (lam49 zero49))

fact49 : {g:_} -> Tm49 g (arr49 Main.nat49 Main.nat49)
fact49 = lam49 (rec49 v049 (lam49 (lam49 (app49 (app49 mul49 (suc49 v149)) v049)))
                 (suc49 zero49))

Ty50 : Type
Ty50 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat50 : Ty50
nat50 = \ _, nat50, _, _, _, _, _ => nat50
top50 : Ty50
top50 = \ _, _, top50, _, _, _, _ => top50
bot50 : Ty50
bot50 = \ _, _, _, bot50, _, _, _ => bot50

arr50 : Ty50-> Ty50-> Ty50
arr50 = \ a, b, ty, nat50, top50, bot50, arr50, prod, sum =>
     arr50 (a ty nat50 top50 bot50 arr50 prod sum) (b ty nat50 top50 bot50 arr50 prod sum)

prod50 : Ty50-> Ty50-> Ty50
prod50 = \ a, b, ty, nat50, top50, bot50, arr50, prod50, sum =>
     prod50 (a ty nat50 top50 bot50 arr50 prod50 sum) (b ty nat50 top50 bot50 arr50 prod50 sum)

sum50 : Ty50-> Ty50-> Ty50
sum50 = \ a, b, ty, nat50, top50, bot50, arr50, prod50, sum50 =>
     sum50 (a ty nat50 top50 bot50 arr50 prod50 sum50) (b ty nat50 top50 bot50 arr50 prod50 sum50)

Con50 : Type
Con50 = (Con50 : Type)
 -> (nil  : Con50)
 -> (snoc : Con50 -> Ty50-> Con50)
 -> Con50

nil50 : Con50
nil50 = \ con, nil50, snoc => nil50

snoc50 : Con50 -> Ty50-> Con50
snoc50 = \ g, a, con, nil50, snoc50 => snoc50 (g con nil50 snoc50) a

Var50 : Con50 -> Ty50-> Type
Var50 = \ g, a =>
    (Var50 : Con50 -> Ty50-> Type)
 -> (vz  : (g:_)->(a:_) -> Var50 (snoc50 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var50 g a -> Var50 (snoc50 g b) a)
 -> Var50 g a

vz50 : {g:_}->{a:_} -> Var50 (snoc50 g a) a
vz50 = \ var, vz50, vs => vz50 _ _

vs50 : {g:_}->{b:_}->{a:_} -> Var50 g a -> Var50 (snoc50 g b) a
vs50 = \ x, var, vz50, vs50 => vs50 _ _ _ (x var vz50 vs50)

Tm50 : Con50 -> Ty50-> Type
Tm50 = \ g, a =>
    (Tm50    : Con50 -> Ty50-> Type)
 -> (var   : (g:_)->(a:_)-> Var50 g a -> Tm50 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm50 (snoc50 g a) b -> Tm50 g (arr50 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm50 g (arr50 a b) -> Tm50 g a -> Tm50 g b)
 -> (tt    : (g:_)-> Tm50 g top50)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm50 g a -> Tm50 g b -> Tm50 g (prod50 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm50 g (prod50 a b) -> Tm50 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm50 g (prod50 a b) -> Tm50 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm50 g a -> Tm50 g (sum50 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm50 g b -> Tm50 g (sum50 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm50 g (sum50 a b) -> Tm50 g (arr50 a c) -> Tm50 g (arr50 b c) -> Tm50 g c)
 -> (zero  : (g:_)-> Tm50 g nat50)
 -> (suc   : (g:_)-> Tm50 g nat50 -> Tm50 g nat50)
 -> (rec   : (g:_)->(a:_) -> Tm50 g nat50 -> Tm50 g (arr50 nat50 (arr50 a a)) -> Tm50 g a -> Tm50 g a)
 -> Tm50 g a

var50 : {g:_}->{a:_} -> Var50 g a -> Tm50 g a
var50 = \ x, tm, var50, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var50 _ _ x

lam50 : {g:_}->{a:_}->{b:_}-> Tm50 (snoc50 g a) b -> Tm50 g (arr50 a b)
lam50 = \ t, tm, var50, lam50, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam50 _ _ _ (t tm var50 lam50 app tt pair fst snd left right split zero suc rec)

app50 : {g:_}->{a:_}->{b:_} -> Tm50 g (arr50 a b) -> Tm50 g a -> Tm50 g b
app50 = \ t, u, tm, var50, lam50, app50, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app50 _ _ _ (t tm var50 lam50 app50 tt pair fst snd left right split zero suc rec)
                (u tm var50 lam50 app50 tt pair fst snd left right split zero suc rec)

tt50 : {g:_} -> Tm50 g Main.top50
tt50 = \ tm, var50, lam50, app50, tt50, pair, fst, snd, left, right, split, zero, suc, rec => tt50 _

pair50 : {g:_}->{a:_}->{b:_} -> Tm50 g a -> Tm50 g b -> Tm50 g (prod50 a b)
pair50 = \ t, u, tm, var50, lam50, app50, tt50, pair50, fst, snd, left, right, split, zero, suc, rec =>
     pair50 _ _ _ (t tm var50 lam50 app50 tt50 pair50 fst snd left right split zero suc rec)
                 (u tm var50 lam50 app50 tt50 pair50 fst snd left right split zero suc rec)

fst50 : {g:_}->{a:_}->{b:_}-> Tm50 g (prod50 a b) -> Tm50 g a
fst50 = \ t, tm, var50, lam50, app50, tt50, pair50, fst50, snd, left, right, split, zero, suc, rec =>
     fst50 _ _ _ (t tm var50 lam50 app50 tt50 pair50 fst50 snd left right split zero suc rec)

snd50 : {g:_}->{a:_}->{b:_} -> Tm50 g (prod50 a b) -> Tm50 g b
snd50 = \ t, tm, var50, lam50, app50, tt50, pair50, fst50, snd50, left, right, split, zero, suc, rec =>
     snd50 _ _ _ (t tm var50 lam50 app50 tt50 pair50 fst50 snd50 left right split zero suc rec)

left50 : {g:_}->{a:_}->{b:_} -> Tm50 g a -> Tm50 g (sum50 a b)
left50 = \ t, tm, var50, lam50, app50, tt50, pair50, fst50, snd50, left50, right, split, zero, suc, rec =>
     left50 _ _ _ (t tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right split zero suc rec)

right50 : {g:_}->{a:_}->{b:_} -> Tm50 g b -> Tm50 g (sum50 a b)
right50 = \ t, tm, var50, lam50, app50, tt50, pair50, fst50, snd50, left50, right50, split, zero, suc, rec =>
     right50 _ _ _ (t tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 split zero suc rec)

split50 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm50 g (sum50 a b) -> Tm50 g (arr50 a c) -> Tm50 g (arr50 b c) -> Tm50 g c
split50 = \ t, u, v, tm, var50, lam50, app50, tt50, pair50, fst50, snd50, left50, right50, split50, zero, suc, rec =>
     split50 _ _ _ _
          (t tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 split50 zero suc rec)
          (u tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 split50 zero suc rec)
          (v tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 split50 zero suc rec)

zero50 : {g:_} -> Tm50 g Main.nat50
zero50 = \ tm, var50, lam50, app50, tt50, pair50, fst50, snd50, left50, right50, split50, zero50, suc, rec =>
  zero50 _

suc50 : {g:_} -> Tm50 g Main.nat50 -> Tm50 g Main.nat50
suc50 = \ t, tm, var50, lam50, app50, tt50, pair50, fst50, snd50, left50, right50, split50, zero50, suc50, rec =>
   suc50 _ (t tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 split50 zero50 suc50 rec)

rec50 : {g:_}->{a:_} -> Tm50 g Main.nat50 -> Tm50 g (arr50 Main.nat50 (arr50 a a)) -> Tm50 g a -> Tm50 g a
rec50 = \ t, u, v, tm, var50, lam50, app50, tt50, pair50, fst50, snd50, left50, right50, split50, zero50, suc50, rec50 =>
     rec50 _ _
       (t tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 split50 zero50 suc50 rec50)
       (u tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 split50 zero50 suc50 rec50)
       (v tm var50 lam50 app50 tt50 pair50 fst50 snd50 left50 right50 split50 zero50 suc50 rec50)

v050 : {g:_}->{a:_} -> Tm50 (snoc50 g a) a
v050 = var50 vz50

v150 : {g:_}->{a:_}->{b:_} -> Tm50 (snoc50 (snoc50 g a) b) a
v150 = var50 (vs50 vz50)

v250 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm50 (snoc50 (snoc50 (snoc50 g a) b) c) a
v250 = var50 (vs50 (vs50 vz50))

v350 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm50 (snoc50 (snoc50 (snoc50 (snoc50 g a) b) c) d) a
v350 = var50 (vs50 (vs50 (vs50 vz50)))

tbool50 : Ty50
tbool50 = sum50 top50 top50

ttrue50 : {g:_} -> Tm50 g Main.tbool50
ttrue50 = left50 tt50

tfalse50 : {g:_} -> Tm50 g Main.tbool50
tfalse50 = right50 tt50

ifthenelse50 : {g:_}->{a:_} -> Tm50 g (arr50 Main.tbool50 (arr50 a (arr50 a a)))
ifthenelse50 = lam50 (lam50 (lam50 (split50 v250 (lam50 v250) (lam50 v150))))

times450 : {g:_}->{a:_} -> Tm50 g (arr50 (arr50 a a) (arr50 a a))
times450  = lam50 (lam50 (app50 v150 (app50 v150 (app50 v150 (app50 v150 v050)))))

add50 : {g:_} -> Tm50 g (arr50 Main.nat50 (arr50 Main.nat50 Main.nat50))
add50 = lam50 (rec50 v050
       (lam50 (lam50 (lam50 (suc50 (app50 v150 v050)))))
       (lam50 v050))

mul50 : {g:_} -> Tm50 g (arr50 Main.nat50 (arr50 Main.nat50 Main.nat50))
mul50 = lam50 (rec50 v050
       (lam50 (lam50 (lam50 (app50 (app50 add50 (app50 v150 v050)) v050))))
       (lam50 zero50))

fact50 : {g:_} -> Tm50 g (arr50 Main.nat50 Main.nat50)
fact50 = lam50 (rec50 v050 (lam50 (lam50 (app50 (app50 mul50 (suc50 v150)) v050)))
                 (suc50 zero50))

Ty51 : Type
Ty51 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat51 : Ty51
nat51 = \ _, nat51, _, _, _, _, _ => nat51
top51 : Ty51
top51 = \ _, _, top51, _, _, _, _ => top51
bot51 : Ty51
bot51 = \ _, _, _, bot51, _, _, _ => bot51

arr51 : Ty51-> Ty51-> Ty51
arr51 = \ a, b, ty, nat51, top51, bot51, arr51, prod, sum =>
     arr51 (a ty nat51 top51 bot51 arr51 prod sum) (b ty nat51 top51 bot51 arr51 prod sum)

prod51 : Ty51-> Ty51-> Ty51
prod51 = \ a, b, ty, nat51, top51, bot51, arr51, prod51, sum =>
     prod51 (a ty nat51 top51 bot51 arr51 prod51 sum) (b ty nat51 top51 bot51 arr51 prod51 sum)

sum51 : Ty51-> Ty51-> Ty51
sum51 = \ a, b, ty, nat51, top51, bot51, arr51, prod51, sum51 =>
     sum51 (a ty nat51 top51 bot51 arr51 prod51 sum51) (b ty nat51 top51 bot51 arr51 prod51 sum51)

Con51 : Type
Con51 = (Con51 : Type)
 -> (nil  : Con51)
 -> (snoc : Con51 -> Ty51-> Con51)
 -> Con51

nil51 : Con51
nil51 = \ con, nil51, snoc => nil51

snoc51 : Con51 -> Ty51-> Con51
snoc51 = \ g, a, con, nil51, snoc51 => snoc51 (g con nil51 snoc51) a

Var51 : Con51 -> Ty51-> Type
Var51 = \ g, a =>
    (Var51 : Con51 -> Ty51-> Type)
 -> (vz  : (g:_)->(a:_) -> Var51 (snoc51 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var51 g a -> Var51 (snoc51 g b) a)
 -> Var51 g a

vz51 : {g:_}->{a:_} -> Var51 (snoc51 g a) a
vz51 = \ var, vz51, vs => vz51 _ _

vs51 : {g:_}->{b:_}->{a:_} -> Var51 g a -> Var51 (snoc51 g b) a
vs51 = \ x, var, vz51, vs51 => vs51 _ _ _ (x var vz51 vs51)

Tm51 : Con51 -> Ty51-> Type
Tm51 = \ g, a =>
    (Tm51    : Con51 -> Ty51-> Type)
 -> (var   : (g:_)->(a:_)-> Var51 g a -> Tm51 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm51 (snoc51 g a) b -> Tm51 g (arr51 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm51 g (arr51 a b) -> Tm51 g a -> Tm51 g b)
 -> (tt    : (g:_)-> Tm51 g top51)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm51 g a -> Tm51 g b -> Tm51 g (prod51 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm51 g (prod51 a b) -> Tm51 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm51 g (prod51 a b) -> Tm51 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm51 g a -> Tm51 g (sum51 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm51 g b -> Tm51 g (sum51 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm51 g (sum51 a b) -> Tm51 g (arr51 a c) -> Tm51 g (arr51 b c) -> Tm51 g c)
 -> (zero  : (g:_)-> Tm51 g nat51)
 -> (suc   : (g:_)-> Tm51 g nat51 -> Tm51 g nat51)
 -> (rec   : (g:_)->(a:_) -> Tm51 g nat51 -> Tm51 g (arr51 nat51 (arr51 a a)) -> Tm51 g a -> Tm51 g a)
 -> Tm51 g a

var51 : {g:_}->{a:_} -> Var51 g a -> Tm51 g a
var51 = \ x, tm, var51, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var51 _ _ x

lam51 : {g:_}->{a:_}->{b:_}-> Tm51 (snoc51 g a) b -> Tm51 g (arr51 a b)
lam51 = \ t, tm, var51, lam51, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam51 _ _ _ (t tm var51 lam51 app tt pair fst snd left right split zero suc rec)

app51 : {g:_}->{a:_}->{b:_} -> Tm51 g (arr51 a b) -> Tm51 g a -> Tm51 g b
app51 = \ t, u, tm, var51, lam51, app51, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app51 _ _ _ (t tm var51 lam51 app51 tt pair fst snd left right split zero suc rec)
                (u tm var51 lam51 app51 tt pair fst snd left right split zero suc rec)

tt51 : {g:_} -> Tm51 g Main.top51
tt51 = \ tm, var51, lam51, app51, tt51, pair, fst, snd, left, right, split, zero, suc, rec => tt51 _

pair51 : {g:_}->{a:_}->{b:_} -> Tm51 g a -> Tm51 g b -> Tm51 g (prod51 a b)
pair51 = \ t, u, tm, var51, lam51, app51, tt51, pair51, fst, snd, left, right, split, zero, suc, rec =>
     pair51 _ _ _ (t tm var51 lam51 app51 tt51 pair51 fst snd left right split zero suc rec)
                 (u tm var51 lam51 app51 tt51 pair51 fst snd left right split zero suc rec)

fst51 : {g:_}->{a:_}->{b:_}-> Tm51 g (prod51 a b) -> Tm51 g a
fst51 = \ t, tm, var51, lam51, app51, tt51, pair51, fst51, snd, left, right, split, zero, suc, rec =>
     fst51 _ _ _ (t tm var51 lam51 app51 tt51 pair51 fst51 snd left right split zero suc rec)

snd51 : {g:_}->{a:_}->{b:_} -> Tm51 g (prod51 a b) -> Tm51 g b
snd51 = \ t, tm, var51, lam51, app51, tt51, pair51, fst51, snd51, left, right, split, zero, suc, rec =>
     snd51 _ _ _ (t tm var51 lam51 app51 tt51 pair51 fst51 snd51 left right split zero suc rec)

left51 : {g:_}->{a:_}->{b:_} -> Tm51 g a -> Tm51 g (sum51 a b)
left51 = \ t, tm, var51, lam51, app51, tt51, pair51, fst51, snd51, left51, right, split, zero, suc, rec =>
     left51 _ _ _ (t tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right split zero suc rec)

right51 : {g:_}->{a:_}->{b:_} -> Tm51 g b -> Tm51 g (sum51 a b)
right51 = \ t, tm, var51, lam51, app51, tt51, pair51, fst51, snd51, left51, right51, split, zero, suc, rec =>
     right51 _ _ _ (t tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 split zero suc rec)

split51 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm51 g (sum51 a b) -> Tm51 g (arr51 a c) -> Tm51 g (arr51 b c) -> Tm51 g c
split51 = \ t, u, v, tm, var51, lam51, app51, tt51, pair51, fst51, snd51, left51, right51, split51, zero, suc, rec =>
     split51 _ _ _ _
          (t tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 split51 zero suc rec)
          (u tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 split51 zero suc rec)
          (v tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 split51 zero suc rec)

zero51 : {g:_} -> Tm51 g Main.nat51
zero51 = \ tm, var51, lam51, app51, tt51, pair51, fst51, snd51, left51, right51, split51, zero51, suc, rec =>
  zero51 _

suc51 : {g:_} -> Tm51 g Main.nat51 -> Tm51 g Main.nat51
suc51 = \ t, tm, var51, lam51, app51, tt51, pair51, fst51, snd51, left51, right51, split51, zero51, suc51, rec =>
   suc51 _ (t tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 split51 zero51 suc51 rec)

rec51 : {g:_}->{a:_} -> Tm51 g Main.nat51 -> Tm51 g (arr51 Main.nat51 (arr51 a a)) -> Tm51 g a -> Tm51 g a
rec51 = \ t, u, v, tm, var51, lam51, app51, tt51, pair51, fst51, snd51, left51, right51, split51, zero51, suc51, rec51 =>
     rec51 _ _
       (t tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 split51 zero51 suc51 rec51)
       (u tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 split51 zero51 suc51 rec51)
       (v tm var51 lam51 app51 tt51 pair51 fst51 snd51 left51 right51 split51 zero51 suc51 rec51)

v051 : {g:_}->{a:_} -> Tm51 (snoc51 g a) a
v051 = var51 vz51

v151 : {g:_}->{a:_}->{b:_} -> Tm51 (snoc51 (snoc51 g a) b) a
v151 = var51 (vs51 vz51)

v251 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm51 (snoc51 (snoc51 (snoc51 g a) b) c) a
v251 = var51 (vs51 (vs51 vz51))

v351 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm51 (snoc51 (snoc51 (snoc51 (snoc51 g a) b) c) d) a
v351 = var51 (vs51 (vs51 (vs51 vz51)))

tbool51 : Ty51
tbool51 = sum51 top51 top51

ttrue51 : {g:_} -> Tm51 g Main.tbool51
ttrue51 = left51 tt51

tfalse51 : {g:_} -> Tm51 g Main.tbool51
tfalse51 = right51 tt51

ifthenelse51 : {g:_}->{a:_} -> Tm51 g (arr51 Main.tbool51 (arr51 a (arr51 a a)))
ifthenelse51 = lam51 (lam51 (lam51 (split51 v251 (lam51 v251) (lam51 v151))))

times451 : {g:_}->{a:_} -> Tm51 g (arr51 (arr51 a a) (arr51 a a))
times451  = lam51 (lam51 (app51 v151 (app51 v151 (app51 v151 (app51 v151 v051)))))

add51 : {g:_} -> Tm51 g (arr51 Main.nat51 (arr51 Main.nat51 Main.nat51))
add51 = lam51 (rec51 v051
       (lam51 (lam51 (lam51 (suc51 (app51 v151 v051)))))
       (lam51 v051))

mul51 : {g:_} -> Tm51 g (arr51 Main.nat51 (arr51 Main.nat51 Main.nat51))
mul51 = lam51 (rec51 v051
       (lam51 (lam51 (lam51 (app51 (app51 add51 (app51 v151 v051)) v051))))
       (lam51 zero51))

fact51 : {g:_} -> Tm51 g (arr51 Main.nat51 Main.nat51)
fact51 = lam51 (rec51 v051 (lam51 (lam51 (app51 (app51 mul51 (suc51 v151)) v051)))
                 (suc51 zero51))

Ty52 : Type
Ty52 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat52 : Ty52
nat52 = \ _, nat52, _, _, _, _, _ => nat52
top52 : Ty52
top52 = \ _, _, top52, _, _, _, _ => top52
bot52 : Ty52
bot52 = \ _, _, _, bot52, _, _, _ => bot52

arr52 : Ty52-> Ty52-> Ty52
arr52 = \ a, b, ty, nat52, top52, bot52, arr52, prod, sum =>
     arr52 (a ty nat52 top52 bot52 arr52 prod sum) (b ty nat52 top52 bot52 arr52 prod sum)

prod52 : Ty52-> Ty52-> Ty52
prod52 = \ a, b, ty, nat52, top52, bot52, arr52, prod52, sum =>
     prod52 (a ty nat52 top52 bot52 arr52 prod52 sum) (b ty nat52 top52 bot52 arr52 prod52 sum)

sum52 : Ty52-> Ty52-> Ty52
sum52 = \ a, b, ty, nat52, top52, bot52, arr52, prod52, sum52 =>
     sum52 (a ty nat52 top52 bot52 arr52 prod52 sum52) (b ty nat52 top52 bot52 arr52 prod52 sum52)

Con52 : Type
Con52 = (Con52 : Type)
 -> (nil  : Con52)
 -> (snoc : Con52 -> Ty52-> Con52)
 -> Con52

nil52 : Con52
nil52 = \ con, nil52, snoc => nil52

snoc52 : Con52 -> Ty52-> Con52
snoc52 = \ g, a, con, nil52, snoc52 => snoc52 (g con nil52 snoc52) a

Var52 : Con52 -> Ty52-> Type
Var52 = \ g, a =>
    (Var52 : Con52 -> Ty52-> Type)
 -> (vz  : (g:_)->(a:_) -> Var52 (snoc52 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var52 g a -> Var52 (snoc52 g b) a)
 -> Var52 g a

vz52 : {g:_}->{a:_} -> Var52 (snoc52 g a) a
vz52 = \ var, vz52, vs => vz52 _ _

vs52 : {g:_}->{b:_}->{a:_} -> Var52 g a -> Var52 (snoc52 g b) a
vs52 = \ x, var, vz52, vs52 => vs52 _ _ _ (x var vz52 vs52)

Tm52 : Con52 -> Ty52-> Type
Tm52 = \ g, a =>
    (Tm52    : Con52 -> Ty52-> Type)
 -> (var   : (g:_)->(a:_)-> Var52 g a -> Tm52 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm52 (snoc52 g a) b -> Tm52 g (arr52 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm52 g (arr52 a b) -> Tm52 g a -> Tm52 g b)
 -> (tt    : (g:_)-> Tm52 g top52)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm52 g a -> Tm52 g b -> Tm52 g (prod52 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm52 g (prod52 a b) -> Tm52 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm52 g (prod52 a b) -> Tm52 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm52 g a -> Tm52 g (sum52 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm52 g b -> Tm52 g (sum52 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm52 g (sum52 a b) -> Tm52 g (arr52 a c) -> Tm52 g (arr52 b c) -> Tm52 g c)
 -> (zero  : (g:_)-> Tm52 g nat52)
 -> (suc   : (g:_)-> Tm52 g nat52 -> Tm52 g nat52)
 -> (rec   : (g:_)->(a:_) -> Tm52 g nat52 -> Tm52 g (arr52 nat52 (arr52 a a)) -> Tm52 g a -> Tm52 g a)
 -> Tm52 g a

var52 : {g:_}->{a:_} -> Var52 g a -> Tm52 g a
var52 = \ x, tm, var52, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var52 _ _ x

lam52 : {g:_}->{a:_}->{b:_}-> Tm52 (snoc52 g a) b -> Tm52 g (arr52 a b)
lam52 = \ t, tm, var52, lam52, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam52 _ _ _ (t tm var52 lam52 app tt pair fst snd left right split zero suc rec)

app52 : {g:_}->{a:_}->{b:_} -> Tm52 g (arr52 a b) -> Tm52 g a -> Tm52 g b
app52 = \ t, u, tm, var52, lam52, app52, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app52 _ _ _ (t tm var52 lam52 app52 tt pair fst snd left right split zero suc rec)
                (u tm var52 lam52 app52 tt pair fst snd left right split zero suc rec)

tt52 : {g:_} -> Tm52 g Main.top52
tt52 = \ tm, var52, lam52, app52, tt52, pair, fst, snd, left, right, split, zero, suc, rec => tt52 _

pair52 : {g:_}->{a:_}->{b:_} -> Tm52 g a -> Tm52 g b -> Tm52 g (prod52 a b)
pair52 = \ t, u, tm, var52, lam52, app52, tt52, pair52, fst, snd, left, right, split, zero, suc, rec =>
     pair52 _ _ _ (t tm var52 lam52 app52 tt52 pair52 fst snd left right split zero suc rec)
                 (u tm var52 lam52 app52 tt52 pair52 fst snd left right split zero suc rec)

fst52 : {g:_}->{a:_}->{b:_}-> Tm52 g (prod52 a b) -> Tm52 g a
fst52 = \ t, tm, var52, lam52, app52, tt52, pair52, fst52, snd, left, right, split, zero, suc, rec =>
     fst52 _ _ _ (t tm var52 lam52 app52 tt52 pair52 fst52 snd left right split zero suc rec)

snd52 : {g:_}->{a:_}->{b:_} -> Tm52 g (prod52 a b) -> Tm52 g b
snd52 = \ t, tm, var52, lam52, app52, tt52, pair52, fst52, snd52, left, right, split, zero, suc, rec =>
     snd52 _ _ _ (t tm var52 lam52 app52 tt52 pair52 fst52 snd52 left right split zero suc rec)

left52 : {g:_}->{a:_}->{b:_} -> Tm52 g a -> Tm52 g (sum52 a b)
left52 = \ t, tm, var52, lam52, app52, tt52, pair52, fst52, snd52, left52, right, split, zero, suc, rec =>
     left52 _ _ _ (t tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right split zero suc rec)

right52 : {g:_}->{a:_}->{b:_} -> Tm52 g b -> Tm52 g (sum52 a b)
right52 = \ t, tm, var52, lam52, app52, tt52, pair52, fst52, snd52, left52, right52, split, zero, suc, rec =>
     right52 _ _ _ (t tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 split zero suc rec)

split52 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm52 g (sum52 a b) -> Tm52 g (arr52 a c) -> Tm52 g (arr52 b c) -> Tm52 g c
split52 = \ t, u, v, tm, var52, lam52, app52, tt52, pair52, fst52, snd52, left52, right52, split52, zero, suc, rec =>
     split52 _ _ _ _
          (t tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 split52 zero suc rec)
          (u tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 split52 zero suc rec)
          (v tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 split52 zero suc rec)

zero52 : {g:_} -> Tm52 g Main.nat52
zero52 = \ tm, var52, lam52, app52, tt52, pair52, fst52, snd52, left52, right52, split52, zero52, suc, rec =>
  zero52 _

suc52 : {g:_} -> Tm52 g Main.nat52 -> Tm52 g Main.nat52
suc52 = \ t, tm, var52, lam52, app52, tt52, pair52, fst52, snd52, left52, right52, split52, zero52, suc52, rec =>
   suc52 _ (t tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 split52 zero52 suc52 rec)

rec52 : {g:_}->{a:_} -> Tm52 g Main.nat52 -> Tm52 g (arr52 Main.nat52 (arr52 a a)) -> Tm52 g a -> Tm52 g a
rec52 = \ t, u, v, tm, var52, lam52, app52, tt52, pair52, fst52, snd52, left52, right52, split52, zero52, suc52, rec52 =>
     rec52 _ _
       (t tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 split52 zero52 suc52 rec52)
       (u tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 split52 zero52 suc52 rec52)
       (v tm var52 lam52 app52 tt52 pair52 fst52 snd52 left52 right52 split52 zero52 suc52 rec52)

v052 : {g:_}->{a:_} -> Tm52 (snoc52 g a) a
v052 = var52 vz52

v152 : {g:_}->{a:_}->{b:_} -> Tm52 (snoc52 (snoc52 g a) b) a
v152 = var52 (vs52 vz52)

v252 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm52 (snoc52 (snoc52 (snoc52 g a) b) c) a
v252 = var52 (vs52 (vs52 vz52))

v352 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm52 (snoc52 (snoc52 (snoc52 (snoc52 g a) b) c) d) a
v352 = var52 (vs52 (vs52 (vs52 vz52)))

tbool52 : Ty52
tbool52 = sum52 top52 top52

ttrue52 : {g:_} -> Tm52 g Main.tbool52
ttrue52 = left52 tt52

tfalse52 : {g:_} -> Tm52 g Main.tbool52
tfalse52 = right52 tt52

ifthenelse52 : {g:_}->{a:_} -> Tm52 g (arr52 Main.tbool52 (arr52 a (arr52 a a)))
ifthenelse52 = lam52 (lam52 (lam52 (split52 v252 (lam52 v252) (lam52 v152))))

times452 : {g:_}->{a:_} -> Tm52 g (arr52 (arr52 a a) (arr52 a a))
times452  = lam52 (lam52 (app52 v152 (app52 v152 (app52 v152 (app52 v152 v052)))))

add52 : {g:_} -> Tm52 g (arr52 Main.nat52 (arr52 Main.nat52 Main.nat52))
add52 = lam52 (rec52 v052
       (lam52 (lam52 (lam52 (suc52 (app52 v152 v052)))))
       (lam52 v052))

mul52 : {g:_} -> Tm52 g (arr52 Main.nat52 (arr52 Main.nat52 Main.nat52))
mul52 = lam52 (rec52 v052
       (lam52 (lam52 (lam52 (app52 (app52 add52 (app52 v152 v052)) v052))))
       (lam52 zero52))

fact52 : {g:_} -> Tm52 g (arr52 Main.nat52 Main.nat52)
fact52 = lam52 (rec52 v052 (lam52 (lam52 (app52 (app52 mul52 (suc52 v152)) v052)))
                 (suc52 zero52))

Ty53 : Type
Ty53 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat53 : Ty53
nat53 = \ _, nat53, _, _, _, _, _ => nat53
top53 : Ty53
top53 = \ _, _, top53, _, _, _, _ => top53
bot53 : Ty53
bot53 = \ _, _, _, bot53, _, _, _ => bot53

arr53 : Ty53-> Ty53-> Ty53
arr53 = \ a, b, ty, nat53, top53, bot53, arr53, prod, sum =>
     arr53 (a ty nat53 top53 bot53 arr53 prod sum) (b ty nat53 top53 bot53 arr53 prod sum)

prod53 : Ty53-> Ty53-> Ty53
prod53 = \ a, b, ty, nat53, top53, bot53, arr53, prod53, sum =>
     prod53 (a ty nat53 top53 bot53 arr53 prod53 sum) (b ty nat53 top53 bot53 arr53 prod53 sum)

sum53 : Ty53-> Ty53-> Ty53
sum53 = \ a, b, ty, nat53, top53, bot53, arr53, prod53, sum53 =>
     sum53 (a ty nat53 top53 bot53 arr53 prod53 sum53) (b ty nat53 top53 bot53 arr53 prod53 sum53)

Con53 : Type
Con53 = (Con53 : Type)
 -> (nil  : Con53)
 -> (snoc : Con53 -> Ty53-> Con53)
 -> Con53

nil53 : Con53
nil53 = \ con, nil53, snoc => nil53

snoc53 : Con53 -> Ty53-> Con53
snoc53 = \ g, a, con, nil53, snoc53 => snoc53 (g con nil53 snoc53) a

Var53 : Con53 -> Ty53-> Type
Var53 = \ g, a =>
    (Var53 : Con53 -> Ty53-> Type)
 -> (vz  : (g:_)->(a:_) -> Var53 (snoc53 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var53 g a -> Var53 (snoc53 g b) a)
 -> Var53 g a

vz53 : {g:_}->{a:_} -> Var53 (snoc53 g a) a
vz53 = \ var, vz53, vs => vz53 _ _

vs53 : {g:_}->{b:_}->{a:_} -> Var53 g a -> Var53 (snoc53 g b) a
vs53 = \ x, var, vz53, vs53 => vs53 _ _ _ (x var vz53 vs53)

Tm53 : Con53 -> Ty53-> Type
Tm53 = \ g, a =>
    (Tm53    : Con53 -> Ty53-> Type)
 -> (var   : (g:_)->(a:_)-> Var53 g a -> Tm53 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm53 (snoc53 g a) b -> Tm53 g (arr53 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm53 g (arr53 a b) -> Tm53 g a -> Tm53 g b)
 -> (tt    : (g:_)-> Tm53 g top53)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm53 g a -> Tm53 g b -> Tm53 g (prod53 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm53 g (prod53 a b) -> Tm53 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm53 g (prod53 a b) -> Tm53 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm53 g a -> Tm53 g (sum53 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm53 g b -> Tm53 g (sum53 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm53 g (sum53 a b) -> Tm53 g (arr53 a c) -> Tm53 g (arr53 b c) -> Tm53 g c)
 -> (zero  : (g:_)-> Tm53 g nat53)
 -> (suc   : (g:_)-> Tm53 g nat53 -> Tm53 g nat53)
 -> (rec   : (g:_)->(a:_) -> Tm53 g nat53 -> Tm53 g (arr53 nat53 (arr53 a a)) -> Tm53 g a -> Tm53 g a)
 -> Tm53 g a

var53 : {g:_}->{a:_} -> Var53 g a -> Tm53 g a
var53 = \ x, tm, var53, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var53 _ _ x

lam53 : {g:_}->{a:_}->{b:_}-> Tm53 (snoc53 g a) b -> Tm53 g (arr53 a b)
lam53 = \ t, tm, var53, lam53, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam53 _ _ _ (t tm var53 lam53 app tt pair fst snd left right split zero suc rec)

app53 : {g:_}->{a:_}->{b:_} -> Tm53 g (arr53 a b) -> Tm53 g a -> Tm53 g b
app53 = \ t, u, tm, var53, lam53, app53, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app53 _ _ _ (t tm var53 lam53 app53 tt pair fst snd left right split zero suc rec)
                (u tm var53 lam53 app53 tt pair fst snd left right split zero suc rec)

tt53 : {g:_} -> Tm53 g Main.top53
tt53 = \ tm, var53, lam53, app53, tt53, pair, fst, snd, left, right, split, zero, suc, rec => tt53 _

pair53 : {g:_}->{a:_}->{b:_} -> Tm53 g a -> Tm53 g b -> Tm53 g (prod53 a b)
pair53 = \ t, u, tm, var53, lam53, app53, tt53, pair53, fst, snd, left, right, split, zero, suc, rec =>
     pair53 _ _ _ (t tm var53 lam53 app53 tt53 pair53 fst snd left right split zero suc rec)
                 (u tm var53 lam53 app53 tt53 pair53 fst snd left right split zero suc rec)

fst53 : {g:_}->{a:_}->{b:_}-> Tm53 g (prod53 a b) -> Tm53 g a
fst53 = \ t, tm, var53, lam53, app53, tt53, pair53, fst53, snd, left, right, split, zero, suc, rec =>
     fst53 _ _ _ (t tm var53 lam53 app53 tt53 pair53 fst53 snd left right split zero suc rec)

snd53 : {g:_}->{a:_}->{b:_} -> Tm53 g (prod53 a b) -> Tm53 g b
snd53 = \ t, tm, var53, lam53, app53, tt53, pair53, fst53, snd53, left, right, split, zero, suc, rec =>
     snd53 _ _ _ (t tm var53 lam53 app53 tt53 pair53 fst53 snd53 left right split zero suc rec)

left53 : {g:_}->{a:_}->{b:_} -> Tm53 g a -> Tm53 g (sum53 a b)
left53 = \ t, tm, var53, lam53, app53, tt53, pair53, fst53, snd53, left53, right, split, zero, suc, rec =>
     left53 _ _ _ (t tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right split zero suc rec)

right53 : {g:_}->{a:_}->{b:_} -> Tm53 g b -> Tm53 g (sum53 a b)
right53 = \ t, tm, var53, lam53, app53, tt53, pair53, fst53, snd53, left53, right53, split, zero, suc, rec =>
     right53 _ _ _ (t tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 split zero suc rec)

split53 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm53 g (sum53 a b) -> Tm53 g (arr53 a c) -> Tm53 g (arr53 b c) -> Tm53 g c
split53 = \ t, u, v, tm, var53, lam53, app53, tt53, pair53, fst53, snd53, left53, right53, split53, zero, suc, rec =>
     split53 _ _ _ _
          (t tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 split53 zero suc rec)
          (u tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 split53 zero suc rec)
          (v tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 split53 zero suc rec)

zero53 : {g:_} -> Tm53 g Main.nat53
zero53 = \ tm, var53, lam53, app53, tt53, pair53, fst53, snd53, left53, right53, split53, zero53, suc, rec =>
  zero53 _

suc53 : {g:_} -> Tm53 g Main.nat53 -> Tm53 g Main.nat53
suc53 = \ t, tm, var53, lam53, app53, tt53, pair53, fst53, snd53, left53, right53, split53, zero53, suc53, rec =>
   suc53 _ (t tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 split53 zero53 suc53 rec)

rec53 : {g:_}->{a:_} -> Tm53 g Main.nat53 -> Tm53 g (arr53 Main.nat53 (arr53 a a)) -> Tm53 g a -> Tm53 g a
rec53 = \ t, u, v, tm, var53, lam53, app53, tt53, pair53, fst53, snd53, left53, right53, split53, zero53, suc53, rec53 =>
     rec53 _ _
       (t tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 split53 zero53 suc53 rec53)
       (u tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 split53 zero53 suc53 rec53)
       (v tm var53 lam53 app53 tt53 pair53 fst53 snd53 left53 right53 split53 zero53 suc53 rec53)

v053 : {g:_}->{a:_} -> Tm53 (snoc53 g a) a
v053 = var53 vz53

v153 : {g:_}->{a:_}->{b:_} -> Tm53 (snoc53 (snoc53 g a) b) a
v153 = var53 (vs53 vz53)

v253 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm53 (snoc53 (snoc53 (snoc53 g a) b) c) a
v253 = var53 (vs53 (vs53 vz53))

v353 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm53 (snoc53 (snoc53 (snoc53 (snoc53 g a) b) c) d) a
v353 = var53 (vs53 (vs53 (vs53 vz53)))

tbool53 : Ty53
tbool53 = sum53 top53 top53

ttrue53 : {g:_} -> Tm53 g Main.tbool53
ttrue53 = left53 tt53

tfalse53 : {g:_} -> Tm53 g Main.tbool53
tfalse53 = right53 tt53

ifthenelse53 : {g:_}->{a:_} -> Tm53 g (arr53 Main.tbool53 (arr53 a (arr53 a a)))
ifthenelse53 = lam53 (lam53 (lam53 (split53 v253 (lam53 v253) (lam53 v153))))

times453 : {g:_}->{a:_} -> Tm53 g (arr53 (arr53 a a) (arr53 a a))
times453  = lam53 (lam53 (app53 v153 (app53 v153 (app53 v153 (app53 v153 v053)))))

add53 : {g:_} -> Tm53 g (arr53 Main.nat53 (arr53 Main.nat53 Main.nat53))
add53 = lam53 (rec53 v053
       (lam53 (lam53 (lam53 (suc53 (app53 v153 v053)))))
       (lam53 v053))

mul53 : {g:_} -> Tm53 g (arr53 Main.nat53 (arr53 Main.nat53 Main.nat53))
mul53 = lam53 (rec53 v053
       (lam53 (lam53 (lam53 (app53 (app53 add53 (app53 v153 v053)) v053))))
       (lam53 zero53))

fact53 : {g:_} -> Tm53 g (arr53 Main.nat53 Main.nat53)
fact53 = lam53 (rec53 v053 (lam53 (lam53 (app53 (app53 mul53 (suc53 v153)) v053)))
                 (suc53 zero53))

Ty54 : Type
Ty54 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat54 : Ty54
nat54 = \ _, nat54, _, _, _, _, _ => nat54
top54 : Ty54
top54 = \ _, _, top54, _, _, _, _ => top54
bot54 : Ty54
bot54 = \ _, _, _, bot54, _, _, _ => bot54

arr54 : Ty54-> Ty54-> Ty54
arr54 = \ a, b, ty, nat54, top54, bot54, arr54, prod, sum =>
     arr54 (a ty nat54 top54 bot54 arr54 prod sum) (b ty nat54 top54 bot54 arr54 prod sum)

prod54 : Ty54-> Ty54-> Ty54
prod54 = \ a, b, ty, nat54, top54, bot54, arr54, prod54, sum =>
     prod54 (a ty nat54 top54 bot54 arr54 prod54 sum) (b ty nat54 top54 bot54 arr54 prod54 sum)

sum54 : Ty54-> Ty54-> Ty54
sum54 = \ a, b, ty, nat54, top54, bot54, arr54, prod54, sum54 =>
     sum54 (a ty nat54 top54 bot54 arr54 prod54 sum54) (b ty nat54 top54 bot54 arr54 prod54 sum54)

Con54 : Type
Con54 = (Con54 : Type)
 -> (nil  : Con54)
 -> (snoc : Con54 -> Ty54-> Con54)
 -> Con54

nil54 : Con54
nil54 = \ con, nil54, snoc => nil54

snoc54 : Con54 -> Ty54-> Con54
snoc54 = \ g, a, con, nil54, snoc54 => snoc54 (g con nil54 snoc54) a

Var54 : Con54 -> Ty54-> Type
Var54 = \ g, a =>
    (Var54 : Con54 -> Ty54-> Type)
 -> (vz  : (g:_)->(a:_) -> Var54 (snoc54 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var54 g a -> Var54 (snoc54 g b) a)
 -> Var54 g a

vz54 : {g:_}->{a:_} -> Var54 (snoc54 g a) a
vz54 = \ var, vz54, vs => vz54 _ _

vs54 : {g:_}->{b:_}->{a:_} -> Var54 g a -> Var54 (snoc54 g b) a
vs54 = \ x, var, vz54, vs54 => vs54 _ _ _ (x var vz54 vs54)

Tm54 : Con54 -> Ty54-> Type
Tm54 = \ g, a =>
    (Tm54    : Con54 -> Ty54-> Type)
 -> (var   : (g:_)->(a:_)-> Var54 g a -> Tm54 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm54 (snoc54 g a) b -> Tm54 g (arr54 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm54 g (arr54 a b) -> Tm54 g a -> Tm54 g b)
 -> (tt    : (g:_)-> Tm54 g top54)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm54 g a -> Tm54 g b -> Tm54 g (prod54 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm54 g (prod54 a b) -> Tm54 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm54 g (prod54 a b) -> Tm54 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm54 g a -> Tm54 g (sum54 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm54 g b -> Tm54 g (sum54 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm54 g (sum54 a b) -> Tm54 g (arr54 a c) -> Tm54 g (arr54 b c) -> Tm54 g c)
 -> (zero  : (g:_)-> Tm54 g nat54)
 -> (suc   : (g:_)-> Tm54 g nat54 -> Tm54 g nat54)
 -> (rec   : (g:_)->(a:_) -> Tm54 g nat54 -> Tm54 g (arr54 nat54 (arr54 a a)) -> Tm54 g a -> Tm54 g a)
 -> Tm54 g a

var54 : {g:_}->{a:_} -> Var54 g a -> Tm54 g a
var54 = \ x, tm, var54, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var54 _ _ x

lam54 : {g:_}->{a:_}->{b:_}-> Tm54 (snoc54 g a) b -> Tm54 g (arr54 a b)
lam54 = \ t, tm, var54, lam54, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam54 _ _ _ (t tm var54 lam54 app tt pair fst snd left right split zero suc rec)

app54 : {g:_}->{a:_}->{b:_} -> Tm54 g (arr54 a b) -> Tm54 g a -> Tm54 g b
app54 = \ t, u, tm, var54, lam54, app54, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app54 _ _ _ (t tm var54 lam54 app54 tt pair fst snd left right split zero suc rec)
                (u tm var54 lam54 app54 tt pair fst snd left right split zero suc rec)

tt54 : {g:_} -> Tm54 g Main.top54
tt54 = \ tm, var54, lam54, app54, tt54, pair, fst, snd, left, right, split, zero, suc, rec => tt54 _

pair54 : {g:_}->{a:_}->{b:_} -> Tm54 g a -> Tm54 g b -> Tm54 g (prod54 a b)
pair54 = \ t, u, tm, var54, lam54, app54, tt54, pair54, fst, snd, left, right, split, zero, suc, rec =>
     pair54 _ _ _ (t tm var54 lam54 app54 tt54 pair54 fst snd left right split zero suc rec)
                 (u tm var54 lam54 app54 tt54 pair54 fst snd left right split zero suc rec)

fst54 : {g:_}->{a:_}->{b:_}-> Tm54 g (prod54 a b) -> Tm54 g a
fst54 = \ t, tm, var54, lam54, app54, tt54, pair54, fst54, snd, left, right, split, zero, suc, rec =>
     fst54 _ _ _ (t tm var54 lam54 app54 tt54 pair54 fst54 snd left right split zero suc rec)

snd54 : {g:_}->{a:_}->{b:_} -> Tm54 g (prod54 a b) -> Tm54 g b
snd54 = \ t, tm, var54, lam54, app54, tt54, pair54, fst54, snd54, left, right, split, zero, suc, rec =>
     snd54 _ _ _ (t tm var54 lam54 app54 tt54 pair54 fst54 snd54 left right split zero suc rec)

left54 : {g:_}->{a:_}->{b:_} -> Tm54 g a -> Tm54 g (sum54 a b)
left54 = \ t, tm, var54, lam54, app54, tt54, pair54, fst54, snd54, left54, right, split, zero, suc, rec =>
     left54 _ _ _ (t tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right split zero suc rec)

right54 : {g:_}->{a:_}->{b:_} -> Tm54 g b -> Tm54 g (sum54 a b)
right54 = \ t, tm, var54, lam54, app54, tt54, pair54, fst54, snd54, left54, right54, split, zero, suc, rec =>
     right54 _ _ _ (t tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 split zero suc rec)

split54 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm54 g (sum54 a b) -> Tm54 g (arr54 a c) -> Tm54 g (arr54 b c) -> Tm54 g c
split54 = \ t, u, v, tm, var54, lam54, app54, tt54, pair54, fst54, snd54, left54, right54, split54, zero, suc, rec =>
     split54 _ _ _ _
          (t tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 split54 zero suc rec)
          (u tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 split54 zero suc rec)
          (v tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 split54 zero suc rec)

zero54 : {g:_} -> Tm54 g Main.nat54
zero54 = \ tm, var54, lam54, app54, tt54, pair54, fst54, snd54, left54, right54, split54, zero54, suc, rec =>
  zero54 _

suc54 : {g:_} -> Tm54 g Main.nat54 -> Tm54 g Main.nat54
suc54 = \ t, tm, var54, lam54, app54, tt54, pair54, fst54, snd54, left54, right54, split54, zero54, suc54, rec =>
   suc54 _ (t tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 split54 zero54 suc54 rec)

rec54 : {g:_}->{a:_} -> Tm54 g Main.nat54 -> Tm54 g (arr54 Main.nat54 (arr54 a a)) -> Tm54 g a -> Tm54 g a
rec54 = \ t, u, v, tm, var54, lam54, app54, tt54, pair54, fst54, snd54, left54, right54, split54, zero54, suc54, rec54 =>
     rec54 _ _
       (t tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 split54 zero54 suc54 rec54)
       (u tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 split54 zero54 suc54 rec54)
       (v tm var54 lam54 app54 tt54 pair54 fst54 snd54 left54 right54 split54 zero54 suc54 rec54)

v054 : {g:_}->{a:_} -> Tm54 (snoc54 g a) a
v054 = var54 vz54

v154 : {g:_}->{a:_}->{b:_} -> Tm54 (snoc54 (snoc54 g a) b) a
v154 = var54 (vs54 vz54)

v254 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm54 (snoc54 (snoc54 (snoc54 g a) b) c) a
v254 = var54 (vs54 (vs54 vz54))

v354 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm54 (snoc54 (snoc54 (snoc54 (snoc54 g a) b) c) d) a
v354 = var54 (vs54 (vs54 (vs54 vz54)))

tbool54 : Ty54
tbool54 = sum54 top54 top54

ttrue54 : {g:_} -> Tm54 g Main.tbool54
ttrue54 = left54 tt54

tfalse54 : {g:_} -> Tm54 g Main.tbool54
tfalse54 = right54 tt54

ifthenelse54 : {g:_}->{a:_} -> Tm54 g (arr54 Main.tbool54 (arr54 a (arr54 a a)))
ifthenelse54 = lam54 (lam54 (lam54 (split54 v254 (lam54 v254) (lam54 v154))))

times454 : {g:_}->{a:_} -> Tm54 g (arr54 (arr54 a a) (arr54 a a))
times454  = lam54 (lam54 (app54 v154 (app54 v154 (app54 v154 (app54 v154 v054)))))

add54 : {g:_} -> Tm54 g (arr54 Main.nat54 (arr54 Main.nat54 Main.nat54))
add54 = lam54 (rec54 v054
       (lam54 (lam54 (lam54 (suc54 (app54 v154 v054)))))
       (lam54 v054))

mul54 : {g:_} -> Tm54 g (arr54 Main.nat54 (arr54 Main.nat54 Main.nat54))
mul54 = lam54 (rec54 v054
       (lam54 (lam54 (lam54 (app54 (app54 add54 (app54 v154 v054)) v054))))
       (lam54 zero54))

fact54 : {g:_} -> Tm54 g (arr54 Main.nat54 Main.nat54)
fact54 = lam54 (rec54 v054 (lam54 (lam54 (app54 (app54 mul54 (suc54 v154)) v054)))
                 (suc54 zero54))

Ty55 : Type
Ty55 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat55 : Ty55
nat55 = \ _, nat55, _, _, _, _, _ => nat55
top55 : Ty55
top55 = \ _, _, top55, _, _, _, _ => top55
bot55 : Ty55
bot55 = \ _, _, _, bot55, _, _, _ => bot55

arr55 : Ty55-> Ty55-> Ty55
arr55 = \ a, b, ty, nat55, top55, bot55, arr55, prod, sum =>
     arr55 (a ty nat55 top55 bot55 arr55 prod sum) (b ty nat55 top55 bot55 arr55 prod sum)

prod55 : Ty55-> Ty55-> Ty55
prod55 = \ a, b, ty, nat55, top55, bot55, arr55, prod55, sum =>
     prod55 (a ty nat55 top55 bot55 arr55 prod55 sum) (b ty nat55 top55 bot55 arr55 prod55 sum)

sum55 : Ty55-> Ty55-> Ty55
sum55 = \ a, b, ty, nat55, top55, bot55, arr55, prod55, sum55 =>
     sum55 (a ty nat55 top55 bot55 arr55 prod55 sum55) (b ty nat55 top55 bot55 arr55 prod55 sum55)

Con55 : Type
Con55 = (Con55 : Type)
 -> (nil  : Con55)
 -> (snoc : Con55 -> Ty55-> Con55)
 -> Con55

nil55 : Con55
nil55 = \ con, nil55, snoc => nil55

snoc55 : Con55 -> Ty55-> Con55
snoc55 = \ g, a, con, nil55, snoc55 => snoc55 (g con nil55 snoc55) a

Var55 : Con55 -> Ty55-> Type
Var55 = \ g, a =>
    (Var55 : Con55 -> Ty55-> Type)
 -> (vz  : (g:_)->(a:_) -> Var55 (snoc55 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var55 g a -> Var55 (snoc55 g b) a)
 -> Var55 g a

vz55 : {g:_}->{a:_} -> Var55 (snoc55 g a) a
vz55 = \ var, vz55, vs => vz55 _ _

vs55 : {g:_}->{b:_}->{a:_} -> Var55 g a -> Var55 (snoc55 g b) a
vs55 = \ x, var, vz55, vs55 => vs55 _ _ _ (x var vz55 vs55)

Tm55 : Con55 -> Ty55-> Type
Tm55 = \ g, a =>
    (Tm55    : Con55 -> Ty55-> Type)
 -> (var   : (g:_)->(a:_)-> Var55 g a -> Tm55 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm55 (snoc55 g a) b -> Tm55 g (arr55 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm55 g (arr55 a b) -> Tm55 g a -> Tm55 g b)
 -> (tt    : (g:_)-> Tm55 g top55)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm55 g a -> Tm55 g b -> Tm55 g (prod55 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm55 g (prod55 a b) -> Tm55 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm55 g (prod55 a b) -> Tm55 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm55 g a -> Tm55 g (sum55 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm55 g b -> Tm55 g (sum55 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm55 g (sum55 a b) -> Tm55 g (arr55 a c) -> Tm55 g (arr55 b c) -> Tm55 g c)
 -> (zero  : (g:_)-> Tm55 g nat55)
 -> (suc   : (g:_)-> Tm55 g nat55 -> Tm55 g nat55)
 -> (rec   : (g:_)->(a:_) -> Tm55 g nat55 -> Tm55 g (arr55 nat55 (arr55 a a)) -> Tm55 g a -> Tm55 g a)
 -> Tm55 g a

var55 : {g:_}->{a:_} -> Var55 g a -> Tm55 g a
var55 = \ x, tm, var55, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var55 _ _ x

lam55 : {g:_}->{a:_}->{b:_}-> Tm55 (snoc55 g a) b -> Tm55 g (arr55 a b)
lam55 = \ t, tm, var55, lam55, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam55 _ _ _ (t tm var55 lam55 app tt pair fst snd left right split zero suc rec)

app55 : {g:_}->{a:_}->{b:_} -> Tm55 g (arr55 a b) -> Tm55 g a -> Tm55 g b
app55 = \ t, u, tm, var55, lam55, app55, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app55 _ _ _ (t tm var55 lam55 app55 tt pair fst snd left right split zero suc rec)
                (u tm var55 lam55 app55 tt pair fst snd left right split zero suc rec)

tt55 : {g:_} -> Tm55 g Main.top55
tt55 = \ tm, var55, lam55, app55, tt55, pair, fst, snd, left, right, split, zero, suc, rec => tt55 _

pair55 : {g:_}->{a:_}->{b:_} -> Tm55 g a -> Tm55 g b -> Tm55 g (prod55 a b)
pair55 = \ t, u, tm, var55, lam55, app55, tt55, pair55, fst, snd, left, right, split, zero, suc, rec =>
     pair55 _ _ _ (t tm var55 lam55 app55 tt55 pair55 fst snd left right split zero suc rec)
                 (u tm var55 lam55 app55 tt55 pair55 fst snd left right split zero suc rec)

fst55 : {g:_}->{a:_}->{b:_}-> Tm55 g (prod55 a b) -> Tm55 g a
fst55 = \ t, tm, var55, lam55, app55, tt55, pair55, fst55, snd, left, right, split, zero, suc, rec =>
     fst55 _ _ _ (t tm var55 lam55 app55 tt55 pair55 fst55 snd left right split zero suc rec)

snd55 : {g:_}->{a:_}->{b:_} -> Tm55 g (prod55 a b) -> Tm55 g b
snd55 = \ t, tm, var55, lam55, app55, tt55, pair55, fst55, snd55, left, right, split, zero, suc, rec =>
     snd55 _ _ _ (t tm var55 lam55 app55 tt55 pair55 fst55 snd55 left right split zero suc rec)

left55 : {g:_}->{a:_}->{b:_} -> Tm55 g a -> Tm55 g (sum55 a b)
left55 = \ t, tm, var55, lam55, app55, tt55, pair55, fst55, snd55, left55, right, split, zero, suc, rec =>
     left55 _ _ _ (t tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right split zero suc rec)

right55 : {g:_}->{a:_}->{b:_} -> Tm55 g b -> Tm55 g (sum55 a b)
right55 = \ t, tm, var55, lam55, app55, tt55, pair55, fst55, snd55, left55, right55, split, zero, suc, rec =>
     right55 _ _ _ (t tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 split zero suc rec)

split55 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm55 g (sum55 a b) -> Tm55 g (arr55 a c) -> Tm55 g (arr55 b c) -> Tm55 g c
split55 = \ t, u, v, tm, var55, lam55, app55, tt55, pair55, fst55, snd55, left55, right55, split55, zero, suc, rec =>
     split55 _ _ _ _
          (t tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 split55 zero suc rec)
          (u tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 split55 zero suc rec)
          (v tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 split55 zero suc rec)

zero55 : {g:_} -> Tm55 g Main.nat55
zero55 = \ tm, var55, lam55, app55, tt55, pair55, fst55, snd55, left55, right55, split55, zero55, suc, rec =>
  zero55 _

suc55 : {g:_} -> Tm55 g Main.nat55 -> Tm55 g Main.nat55
suc55 = \ t, tm, var55, lam55, app55, tt55, pair55, fst55, snd55, left55, right55, split55, zero55, suc55, rec =>
   suc55 _ (t tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 split55 zero55 suc55 rec)

rec55 : {g:_}->{a:_} -> Tm55 g Main.nat55 -> Tm55 g (arr55 Main.nat55 (arr55 a a)) -> Tm55 g a -> Tm55 g a
rec55 = \ t, u, v, tm, var55, lam55, app55, tt55, pair55, fst55, snd55, left55, right55, split55, zero55, suc55, rec55 =>
     rec55 _ _
       (t tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 split55 zero55 suc55 rec55)
       (u tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 split55 zero55 suc55 rec55)
       (v tm var55 lam55 app55 tt55 pair55 fst55 snd55 left55 right55 split55 zero55 suc55 rec55)

v055 : {g:_}->{a:_} -> Tm55 (snoc55 g a) a
v055 = var55 vz55

v155 : {g:_}->{a:_}->{b:_} -> Tm55 (snoc55 (snoc55 g a) b) a
v155 = var55 (vs55 vz55)

v255 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm55 (snoc55 (snoc55 (snoc55 g a) b) c) a
v255 = var55 (vs55 (vs55 vz55))

v355 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm55 (snoc55 (snoc55 (snoc55 (snoc55 g a) b) c) d) a
v355 = var55 (vs55 (vs55 (vs55 vz55)))

tbool55 : Ty55
tbool55 = sum55 top55 top55

ttrue55 : {g:_} -> Tm55 g Main.tbool55
ttrue55 = left55 tt55

tfalse55 : {g:_} -> Tm55 g Main.tbool55
tfalse55 = right55 tt55

ifthenelse55 : {g:_}->{a:_} -> Tm55 g (arr55 Main.tbool55 (arr55 a (arr55 a a)))
ifthenelse55 = lam55 (lam55 (lam55 (split55 v255 (lam55 v255) (lam55 v155))))

times455 : {g:_}->{a:_} -> Tm55 g (arr55 (arr55 a a) (arr55 a a))
times455  = lam55 (lam55 (app55 v155 (app55 v155 (app55 v155 (app55 v155 v055)))))

add55 : {g:_} -> Tm55 g (arr55 Main.nat55 (arr55 Main.nat55 Main.nat55))
add55 = lam55 (rec55 v055
       (lam55 (lam55 (lam55 (suc55 (app55 v155 v055)))))
       (lam55 v055))

mul55 : {g:_} -> Tm55 g (arr55 Main.nat55 (arr55 Main.nat55 Main.nat55))
mul55 = lam55 (rec55 v055
       (lam55 (lam55 (lam55 (app55 (app55 add55 (app55 v155 v055)) v055))))
       (lam55 zero55))

fact55 : {g:_} -> Tm55 g (arr55 Main.nat55 Main.nat55)
fact55 = lam55 (rec55 v055 (lam55 (lam55 (app55 (app55 mul55 (suc55 v155)) v055)))
                 (suc55 zero55))

Ty56 : Type
Ty56 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat56 : Ty56
nat56 = \ _, nat56, _, _, _, _, _ => nat56
top56 : Ty56
top56 = \ _, _, top56, _, _, _, _ => top56
bot56 : Ty56
bot56 = \ _, _, _, bot56, _, _, _ => bot56

arr56 : Ty56-> Ty56-> Ty56
arr56 = \ a, b, ty, nat56, top56, bot56, arr56, prod, sum =>
     arr56 (a ty nat56 top56 bot56 arr56 prod sum) (b ty nat56 top56 bot56 arr56 prod sum)

prod56 : Ty56-> Ty56-> Ty56
prod56 = \ a, b, ty, nat56, top56, bot56, arr56, prod56, sum =>
     prod56 (a ty nat56 top56 bot56 arr56 prod56 sum) (b ty nat56 top56 bot56 arr56 prod56 sum)

sum56 : Ty56-> Ty56-> Ty56
sum56 = \ a, b, ty, nat56, top56, bot56, arr56, prod56, sum56 =>
     sum56 (a ty nat56 top56 bot56 arr56 prod56 sum56) (b ty nat56 top56 bot56 arr56 prod56 sum56)

Con56 : Type
Con56 = (Con56 : Type)
 -> (nil  : Con56)
 -> (snoc : Con56 -> Ty56-> Con56)
 -> Con56

nil56 : Con56
nil56 = \ con, nil56, snoc => nil56

snoc56 : Con56 -> Ty56-> Con56
snoc56 = \ g, a, con, nil56, snoc56 => snoc56 (g con nil56 snoc56) a

Var56 : Con56 -> Ty56-> Type
Var56 = \ g, a =>
    (Var56 : Con56 -> Ty56-> Type)
 -> (vz  : (g:_)->(a:_) -> Var56 (snoc56 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var56 g a -> Var56 (snoc56 g b) a)
 -> Var56 g a

vz56 : {g:_}->{a:_} -> Var56 (snoc56 g a) a
vz56 = \ var, vz56, vs => vz56 _ _

vs56 : {g:_}->{b:_}->{a:_} -> Var56 g a -> Var56 (snoc56 g b) a
vs56 = \ x, var, vz56, vs56 => vs56 _ _ _ (x var vz56 vs56)

Tm56 : Con56 -> Ty56-> Type
Tm56 = \ g, a =>
    (Tm56    : Con56 -> Ty56-> Type)
 -> (var   : (g:_)->(a:_)-> Var56 g a -> Tm56 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm56 (snoc56 g a) b -> Tm56 g (arr56 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm56 g (arr56 a b) -> Tm56 g a -> Tm56 g b)
 -> (tt    : (g:_)-> Tm56 g top56)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm56 g a -> Tm56 g b -> Tm56 g (prod56 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm56 g (prod56 a b) -> Tm56 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm56 g (prod56 a b) -> Tm56 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm56 g a -> Tm56 g (sum56 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm56 g b -> Tm56 g (sum56 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm56 g (sum56 a b) -> Tm56 g (arr56 a c) -> Tm56 g (arr56 b c) -> Tm56 g c)
 -> (zero  : (g:_)-> Tm56 g nat56)
 -> (suc   : (g:_)-> Tm56 g nat56 -> Tm56 g nat56)
 -> (rec   : (g:_)->(a:_) -> Tm56 g nat56 -> Tm56 g (arr56 nat56 (arr56 a a)) -> Tm56 g a -> Tm56 g a)
 -> Tm56 g a

var56 : {g:_}->{a:_} -> Var56 g a -> Tm56 g a
var56 = \ x, tm, var56, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var56 _ _ x

lam56 : {g:_}->{a:_}->{b:_}-> Tm56 (snoc56 g a) b -> Tm56 g (arr56 a b)
lam56 = \ t, tm, var56, lam56, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam56 _ _ _ (t tm var56 lam56 app tt pair fst snd left right split zero suc rec)

app56 : {g:_}->{a:_}->{b:_} -> Tm56 g (arr56 a b) -> Tm56 g a -> Tm56 g b
app56 = \ t, u, tm, var56, lam56, app56, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app56 _ _ _ (t tm var56 lam56 app56 tt pair fst snd left right split zero suc rec)
                (u tm var56 lam56 app56 tt pair fst snd left right split zero suc rec)

tt56 : {g:_} -> Tm56 g Main.top56
tt56 = \ tm, var56, lam56, app56, tt56, pair, fst, snd, left, right, split, zero, suc, rec => tt56 _

pair56 : {g:_}->{a:_}->{b:_} -> Tm56 g a -> Tm56 g b -> Tm56 g (prod56 a b)
pair56 = \ t, u, tm, var56, lam56, app56, tt56, pair56, fst, snd, left, right, split, zero, suc, rec =>
     pair56 _ _ _ (t tm var56 lam56 app56 tt56 pair56 fst snd left right split zero suc rec)
                 (u tm var56 lam56 app56 tt56 pair56 fst snd left right split zero suc rec)

fst56 : {g:_}->{a:_}->{b:_}-> Tm56 g (prod56 a b) -> Tm56 g a
fst56 = \ t, tm, var56, lam56, app56, tt56, pair56, fst56, snd, left, right, split, zero, suc, rec =>
     fst56 _ _ _ (t tm var56 lam56 app56 tt56 pair56 fst56 snd left right split zero suc rec)

snd56 : {g:_}->{a:_}->{b:_} -> Tm56 g (prod56 a b) -> Tm56 g b
snd56 = \ t, tm, var56, lam56, app56, tt56, pair56, fst56, snd56, left, right, split, zero, suc, rec =>
     snd56 _ _ _ (t tm var56 lam56 app56 tt56 pair56 fst56 snd56 left right split zero suc rec)

left56 : {g:_}->{a:_}->{b:_} -> Tm56 g a -> Tm56 g (sum56 a b)
left56 = \ t, tm, var56, lam56, app56, tt56, pair56, fst56, snd56, left56, right, split, zero, suc, rec =>
     left56 _ _ _ (t tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right split zero suc rec)

right56 : {g:_}->{a:_}->{b:_} -> Tm56 g b -> Tm56 g (sum56 a b)
right56 = \ t, tm, var56, lam56, app56, tt56, pair56, fst56, snd56, left56, right56, split, zero, suc, rec =>
     right56 _ _ _ (t tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 split zero suc rec)

split56 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm56 g (sum56 a b) -> Tm56 g (arr56 a c) -> Tm56 g (arr56 b c) -> Tm56 g c
split56 = \ t, u, v, tm, var56, lam56, app56, tt56, pair56, fst56, snd56, left56, right56, split56, zero, suc, rec =>
     split56 _ _ _ _
          (t tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 split56 zero suc rec)
          (u tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 split56 zero suc rec)
          (v tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 split56 zero suc rec)

zero56 : {g:_} -> Tm56 g Main.nat56
zero56 = \ tm, var56, lam56, app56, tt56, pair56, fst56, snd56, left56, right56, split56, zero56, suc, rec =>
  zero56 _

suc56 : {g:_} -> Tm56 g Main.nat56 -> Tm56 g Main.nat56
suc56 = \ t, tm, var56, lam56, app56, tt56, pair56, fst56, snd56, left56, right56, split56, zero56, suc56, rec =>
   suc56 _ (t tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 split56 zero56 suc56 rec)

rec56 : {g:_}->{a:_} -> Tm56 g Main.nat56 -> Tm56 g (arr56 Main.nat56 (arr56 a a)) -> Tm56 g a -> Tm56 g a
rec56 = \ t, u, v, tm, var56, lam56, app56, tt56, pair56, fst56, snd56, left56, right56, split56, zero56, suc56, rec56 =>
     rec56 _ _
       (t tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 split56 zero56 suc56 rec56)
       (u tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 split56 zero56 suc56 rec56)
       (v tm var56 lam56 app56 tt56 pair56 fst56 snd56 left56 right56 split56 zero56 suc56 rec56)

v056 : {g:_}->{a:_} -> Tm56 (snoc56 g a) a
v056 = var56 vz56

v156 : {g:_}->{a:_}->{b:_} -> Tm56 (snoc56 (snoc56 g a) b) a
v156 = var56 (vs56 vz56)

v256 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm56 (snoc56 (snoc56 (snoc56 g a) b) c) a
v256 = var56 (vs56 (vs56 vz56))

v356 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm56 (snoc56 (snoc56 (snoc56 (snoc56 g a) b) c) d) a
v356 = var56 (vs56 (vs56 (vs56 vz56)))

tbool56 : Ty56
tbool56 = sum56 top56 top56

ttrue56 : {g:_} -> Tm56 g Main.tbool56
ttrue56 = left56 tt56

tfalse56 : {g:_} -> Tm56 g Main.tbool56
tfalse56 = right56 tt56

ifthenelse56 : {g:_}->{a:_} -> Tm56 g (arr56 Main.tbool56 (arr56 a (arr56 a a)))
ifthenelse56 = lam56 (lam56 (lam56 (split56 v256 (lam56 v256) (lam56 v156))))

times456 : {g:_}->{a:_} -> Tm56 g (arr56 (arr56 a a) (arr56 a a))
times456  = lam56 (lam56 (app56 v156 (app56 v156 (app56 v156 (app56 v156 v056)))))

add56 : {g:_} -> Tm56 g (arr56 Main.nat56 (arr56 Main.nat56 Main.nat56))
add56 = lam56 (rec56 v056
       (lam56 (lam56 (lam56 (suc56 (app56 v156 v056)))))
       (lam56 v056))

mul56 : {g:_} -> Tm56 g (arr56 Main.nat56 (arr56 Main.nat56 Main.nat56))
mul56 = lam56 (rec56 v056
       (lam56 (lam56 (lam56 (app56 (app56 add56 (app56 v156 v056)) v056))))
       (lam56 zero56))

fact56 : {g:_} -> Tm56 g (arr56 Main.nat56 Main.nat56)
fact56 = lam56 (rec56 v056 (lam56 (lam56 (app56 (app56 mul56 (suc56 v156)) v056)))
                 (suc56 zero56))

Ty57 : Type
Ty57 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat57 : Ty57
nat57 = \ _, nat57, _, _, _, _, _ => nat57
top57 : Ty57
top57 = \ _, _, top57, _, _, _, _ => top57
bot57 : Ty57
bot57 = \ _, _, _, bot57, _, _, _ => bot57

arr57 : Ty57-> Ty57-> Ty57
arr57 = \ a, b, ty, nat57, top57, bot57, arr57, prod, sum =>
     arr57 (a ty nat57 top57 bot57 arr57 prod sum) (b ty nat57 top57 bot57 arr57 prod sum)

prod57 : Ty57-> Ty57-> Ty57
prod57 = \ a, b, ty, nat57, top57, bot57, arr57, prod57, sum =>
     prod57 (a ty nat57 top57 bot57 arr57 prod57 sum) (b ty nat57 top57 bot57 arr57 prod57 sum)

sum57 : Ty57-> Ty57-> Ty57
sum57 = \ a, b, ty, nat57, top57, bot57, arr57, prod57, sum57 =>
     sum57 (a ty nat57 top57 bot57 arr57 prod57 sum57) (b ty nat57 top57 bot57 arr57 prod57 sum57)

Con57 : Type
Con57 = (Con57 : Type)
 -> (nil  : Con57)
 -> (snoc : Con57 -> Ty57-> Con57)
 -> Con57

nil57 : Con57
nil57 = \ con, nil57, snoc => nil57

snoc57 : Con57 -> Ty57-> Con57
snoc57 = \ g, a, con, nil57, snoc57 => snoc57 (g con nil57 snoc57) a

Var57 : Con57 -> Ty57-> Type
Var57 = \ g, a =>
    (Var57 : Con57 -> Ty57-> Type)
 -> (vz  : (g:_)->(a:_) -> Var57 (snoc57 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var57 g a -> Var57 (snoc57 g b) a)
 -> Var57 g a

vz57 : {g:_}->{a:_} -> Var57 (snoc57 g a) a
vz57 = \ var, vz57, vs => vz57 _ _

vs57 : {g:_}->{b:_}->{a:_} -> Var57 g a -> Var57 (snoc57 g b) a
vs57 = \ x, var, vz57, vs57 => vs57 _ _ _ (x var vz57 vs57)

Tm57 : Con57 -> Ty57-> Type
Tm57 = \ g, a =>
    (Tm57    : Con57 -> Ty57-> Type)
 -> (var   : (g:_)->(a:_)-> Var57 g a -> Tm57 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm57 (snoc57 g a) b -> Tm57 g (arr57 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm57 g (arr57 a b) -> Tm57 g a -> Tm57 g b)
 -> (tt    : (g:_)-> Tm57 g top57)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm57 g a -> Tm57 g b -> Tm57 g (prod57 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm57 g (prod57 a b) -> Tm57 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm57 g (prod57 a b) -> Tm57 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm57 g a -> Tm57 g (sum57 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm57 g b -> Tm57 g (sum57 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm57 g (sum57 a b) -> Tm57 g (arr57 a c) -> Tm57 g (arr57 b c) -> Tm57 g c)
 -> (zero  : (g:_)-> Tm57 g nat57)
 -> (suc   : (g:_)-> Tm57 g nat57 -> Tm57 g nat57)
 -> (rec   : (g:_)->(a:_) -> Tm57 g nat57 -> Tm57 g (arr57 nat57 (arr57 a a)) -> Tm57 g a -> Tm57 g a)
 -> Tm57 g a

var57 : {g:_}->{a:_} -> Var57 g a -> Tm57 g a
var57 = \ x, tm, var57, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var57 _ _ x

lam57 : {g:_}->{a:_}->{b:_}-> Tm57 (snoc57 g a) b -> Tm57 g (arr57 a b)
lam57 = \ t, tm, var57, lam57, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam57 _ _ _ (t tm var57 lam57 app tt pair fst snd left right split zero suc rec)

app57 : {g:_}->{a:_}->{b:_} -> Tm57 g (arr57 a b) -> Tm57 g a -> Tm57 g b
app57 = \ t, u, tm, var57, lam57, app57, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app57 _ _ _ (t tm var57 lam57 app57 tt pair fst snd left right split zero suc rec)
                (u tm var57 lam57 app57 tt pair fst snd left right split zero suc rec)

tt57 : {g:_} -> Tm57 g Main.top57
tt57 = \ tm, var57, lam57, app57, tt57, pair, fst, snd, left, right, split, zero, suc, rec => tt57 _

pair57 : {g:_}->{a:_}->{b:_} -> Tm57 g a -> Tm57 g b -> Tm57 g (prod57 a b)
pair57 = \ t, u, tm, var57, lam57, app57, tt57, pair57, fst, snd, left, right, split, zero, suc, rec =>
     pair57 _ _ _ (t tm var57 lam57 app57 tt57 pair57 fst snd left right split zero suc rec)
                 (u tm var57 lam57 app57 tt57 pair57 fst snd left right split zero suc rec)

fst57 : {g:_}->{a:_}->{b:_}-> Tm57 g (prod57 a b) -> Tm57 g a
fst57 = \ t, tm, var57, lam57, app57, tt57, pair57, fst57, snd, left, right, split, zero, suc, rec =>
     fst57 _ _ _ (t tm var57 lam57 app57 tt57 pair57 fst57 snd left right split zero suc rec)

snd57 : {g:_}->{a:_}->{b:_} -> Tm57 g (prod57 a b) -> Tm57 g b
snd57 = \ t, tm, var57, lam57, app57, tt57, pair57, fst57, snd57, left, right, split, zero, suc, rec =>
     snd57 _ _ _ (t tm var57 lam57 app57 tt57 pair57 fst57 snd57 left right split zero suc rec)

left57 : {g:_}->{a:_}->{b:_} -> Tm57 g a -> Tm57 g (sum57 a b)
left57 = \ t, tm, var57, lam57, app57, tt57, pair57, fst57, snd57, left57, right, split, zero, suc, rec =>
     left57 _ _ _ (t tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right split zero suc rec)

right57 : {g:_}->{a:_}->{b:_} -> Tm57 g b -> Tm57 g (sum57 a b)
right57 = \ t, tm, var57, lam57, app57, tt57, pair57, fst57, snd57, left57, right57, split, zero, suc, rec =>
     right57 _ _ _ (t tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 split zero suc rec)

split57 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm57 g (sum57 a b) -> Tm57 g (arr57 a c) -> Tm57 g (arr57 b c) -> Tm57 g c
split57 = \ t, u, v, tm, var57, lam57, app57, tt57, pair57, fst57, snd57, left57, right57, split57, zero, suc, rec =>
     split57 _ _ _ _
          (t tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 split57 zero suc rec)
          (u tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 split57 zero suc rec)
          (v tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 split57 zero suc rec)

zero57 : {g:_} -> Tm57 g Main.nat57
zero57 = \ tm, var57, lam57, app57, tt57, pair57, fst57, snd57, left57, right57, split57, zero57, suc, rec =>
  zero57 _

suc57 : {g:_} -> Tm57 g Main.nat57 -> Tm57 g Main.nat57
suc57 = \ t, tm, var57, lam57, app57, tt57, pair57, fst57, snd57, left57, right57, split57, zero57, suc57, rec =>
   suc57 _ (t tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 split57 zero57 suc57 rec)

rec57 : {g:_}->{a:_} -> Tm57 g Main.nat57 -> Tm57 g (arr57 Main.nat57 (arr57 a a)) -> Tm57 g a -> Tm57 g a
rec57 = \ t, u, v, tm, var57, lam57, app57, tt57, pair57, fst57, snd57, left57, right57, split57, zero57, suc57, rec57 =>
     rec57 _ _
       (t tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 split57 zero57 suc57 rec57)
       (u tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 split57 zero57 suc57 rec57)
       (v tm var57 lam57 app57 tt57 pair57 fst57 snd57 left57 right57 split57 zero57 suc57 rec57)

v057 : {g:_}->{a:_} -> Tm57 (snoc57 g a) a
v057 = var57 vz57

v157 : {g:_}->{a:_}->{b:_} -> Tm57 (snoc57 (snoc57 g a) b) a
v157 = var57 (vs57 vz57)

v257 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm57 (snoc57 (snoc57 (snoc57 g a) b) c) a
v257 = var57 (vs57 (vs57 vz57))

v357 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm57 (snoc57 (snoc57 (snoc57 (snoc57 g a) b) c) d) a
v357 = var57 (vs57 (vs57 (vs57 vz57)))

tbool57 : Ty57
tbool57 = sum57 top57 top57

ttrue57 : {g:_} -> Tm57 g Main.tbool57
ttrue57 = left57 tt57

tfalse57 : {g:_} -> Tm57 g Main.tbool57
tfalse57 = right57 tt57

ifthenelse57 : {g:_}->{a:_} -> Tm57 g (arr57 Main.tbool57 (arr57 a (arr57 a a)))
ifthenelse57 = lam57 (lam57 (lam57 (split57 v257 (lam57 v257) (lam57 v157))))

times457 : {g:_}->{a:_} -> Tm57 g (arr57 (arr57 a a) (arr57 a a))
times457  = lam57 (lam57 (app57 v157 (app57 v157 (app57 v157 (app57 v157 v057)))))

add57 : {g:_} -> Tm57 g (arr57 Main.nat57 (arr57 Main.nat57 Main.nat57))
add57 = lam57 (rec57 v057
       (lam57 (lam57 (lam57 (suc57 (app57 v157 v057)))))
       (lam57 v057))

mul57 : {g:_} -> Tm57 g (arr57 Main.nat57 (arr57 Main.nat57 Main.nat57))
mul57 = lam57 (rec57 v057
       (lam57 (lam57 (lam57 (app57 (app57 add57 (app57 v157 v057)) v057))))
       (lam57 zero57))

fact57 : {g:_} -> Tm57 g (arr57 Main.nat57 Main.nat57)
fact57 = lam57 (rec57 v057 (lam57 (lam57 (app57 (app57 mul57 (suc57 v157)) v057)))
                 (suc57 zero57))

Ty58 : Type
Ty58 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat58 : Ty58
nat58 = \ _, nat58, _, _, _, _, _ => nat58
top58 : Ty58
top58 = \ _, _, top58, _, _, _, _ => top58
bot58 : Ty58
bot58 = \ _, _, _, bot58, _, _, _ => bot58

arr58 : Ty58-> Ty58-> Ty58
arr58 = \ a, b, ty, nat58, top58, bot58, arr58, prod, sum =>
     arr58 (a ty nat58 top58 bot58 arr58 prod sum) (b ty nat58 top58 bot58 arr58 prod sum)

prod58 : Ty58-> Ty58-> Ty58
prod58 = \ a, b, ty, nat58, top58, bot58, arr58, prod58, sum =>
     prod58 (a ty nat58 top58 bot58 arr58 prod58 sum) (b ty nat58 top58 bot58 arr58 prod58 sum)

sum58 : Ty58-> Ty58-> Ty58
sum58 = \ a, b, ty, nat58, top58, bot58, arr58, prod58, sum58 =>
     sum58 (a ty nat58 top58 bot58 arr58 prod58 sum58) (b ty nat58 top58 bot58 arr58 prod58 sum58)

Con58 : Type
Con58 = (Con58 : Type)
 -> (nil  : Con58)
 -> (snoc : Con58 -> Ty58-> Con58)
 -> Con58

nil58 : Con58
nil58 = \ con, nil58, snoc => nil58

snoc58 : Con58 -> Ty58-> Con58
snoc58 = \ g, a, con, nil58, snoc58 => snoc58 (g con nil58 snoc58) a

Var58 : Con58 -> Ty58-> Type
Var58 = \ g, a =>
    (Var58 : Con58 -> Ty58-> Type)
 -> (vz  : (g:_)->(a:_) -> Var58 (snoc58 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var58 g a -> Var58 (snoc58 g b) a)
 -> Var58 g a

vz58 : {g:_}->{a:_} -> Var58 (snoc58 g a) a
vz58 = \ var, vz58, vs => vz58 _ _

vs58 : {g:_}->{b:_}->{a:_} -> Var58 g a -> Var58 (snoc58 g b) a
vs58 = \ x, var, vz58, vs58 => vs58 _ _ _ (x var vz58 vs58)

Tm58 : Con58 -> Ty58-> Type
Tm58 = \ g, a =>
    (Tm58    : Con58 -> Ty58-> Type)
 -> (var   : (g:_)->(a:_)-> Var58 g a -> Tm58 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm58 (snoc58 g a) b -> Tm58 g (arr58 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm58 g (arr58 a b) -> Tm58 g a -> Tm58 g b)
 -> (tt    : (g:_)-> Tm58 g top58)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm58 g a -> Tm58 g b -> Tm58 g (prod58 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm58 g (prod58 a b) -> Tm58 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm58 g (prod58 a b) -> Tm58 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm58 g a -> Tm58 g (sum58 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm58 g b -> Tm58 g (sum58 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm58 g (sum58 a b) -> Tm58 g (arr58 a c) -> Tm58 g (arr58 b c) -> Tm58 g c)
 -> (zero  : (g:_)-> Tm58 g nat58)
 -> (suc   : (g:_)-> Tm58 g nat58 -> Tm58 g nat58)
 -> (rec   : (g:_)->(a:_) -> Tm58 g nat58 -> Tm58 g (arr58 nat58 (arr58 a a)) -> Tm58 g a -> Tm58 g a)
 -> Tm58 g a

var58 : {g:_}->{a:_} -> Var58 g a -> Tm58 g a
var58 = \ x, tm, var58, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var58 _ _ x

lam58 : {g:_}->{a:_}->{b:_}-> Tm58 (snoc58 g a) b -> Tm58 g (arr58 a b)
lam58 = \ t, tm, var58, lam58, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam58 _ _ _ (t tm var58 lam58 app tt pair fst snd left right split zero suc rec)

app58 : {g:_}->{a:_}->{b:_} -> Tm58 g (arr58 a b) -> Tm58 g a -> Tm58 g b
app58 = \ t, u, tm, var58, lam58, app58, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app58 _ _ _ (t tm var58 lam58 app58 tt pair fst snd left right split zero suc rec)
                (u tm var58 lam58 app58 tt pair fst snd left right split zero suc rec)

tt58 : {g:_} -> Tm58 g Main.top58
tt58 = \ tm, var58, lam58, app58, tt58, pair, fst, snd, left, right, split, zero, suc, rec => tt58 _

pair58 : {g:_}->{a:_}->{b:_} -> Tm58 g a -> Tm58 g b -> Tm58 g (prod58 a b)
pair58 = \ t, u, tm, var58, lam58, app58, tt58, pair58, fst, snd, left, right, split, zero, suc, rec =>
     pair58 _ _ _ (t tm var58 lam58 app58 tt58 pair58 fst snd left right split zero suc rec)
                 (u tm var58 lam58 app58 tt58 pair58 fst snd left right split zero suc rec)

fst58 : {g:_}->{a:_}->{b:_}-> Tm58 g (prod58 a b) -> Tm58 g a
fst58 = \ t, tm, var58, lam58, app58, tt58, pair58, fst58, snd, left, right, split, zero, suc, rec =>
     fst58 _ _ _ (t tm var58 lam58 app58 tt58 pair58 fst58 snd left right split zero suc rec)

snd58 : {g:_}->{a:_}->{b:_} -> Tm58 g (prod58 a b) -> Tm58 g b
snd58 = \ t, tm, var58, lam58, app58, tt58, pair58, fst58, snd58, left, right, split, zero, suc, rec =>
     snd58 _ _ _ (t tm var58 lam58 app58 tt58 pair58 fst58 snd58 left right split zero suc rec)

left58 : {g:_}->{a:_}->{b:_} -> Tm58 g a -> Tm58 g (sum58 a b)
left58 = \ t, tm, var58, lam58, app58, tt58, pair58, fst58, snd58, left58, right, split, zero, suc, rec =>
     left58 _ _ _ (t tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right split zero suc rec)

right58 : {g:_}->{a:_}->{b:_} -> Tm58 g b -> Tm58 g (sum58 a b)
right58 = \ t, tm, var58, lam58, app58, tt58, pair58, fst58, snd58, left58, right58, split, zero, suc, rec =>
     right58 _ _ _ (t tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 split zero suc rec)

split58 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm58 g (sum58 a b) -> Tm58 g (arr58 a c) -> Tm58 g (arr58 b c) -> Tm58 g c
split58 = \ t, u, v, tm, var58, lam58, app58, tt58, pair58, fst58, snd58, left58, right58, split58, zero, suc, rec =>
     split58 _ _ _ _
          (t tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 split58 zero suc rec)
          (u tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 split58 zero suc rec)
          (v tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 split58 zero suc rec)

zero58 : {g:_} -> Tm58 g Main.nat58
zero58 = \ tm, var58, lam58, app58, tt58, pair58, fst58, snd58, left58, right58, split58, zero58, suc, rec =>
  zero58 _

suc58 : {g:_} -> Tm58 g Main.nat58 -> Tm58 g Main.nat58
suc58 = \ t, tm, var58, lam58, app58, tt58, pair58, fst58, snd58, left58, right58, split58, zero58, suc58, rec =>
   suc58 _ (t tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 split58 zero58 suc58 rec)

rec58 : {g:_}->{a:_} -> Tm58 g Main.nat58 -> Tm58 g (arr58 Main.nat58 (arr58 a a)) -> Tm58 g a -> Tm58 g a
rec58 = \ t, u, v, tm, var58, lam58, app58, tt58, pair58, fst58, snd58, left58, right58, split58, zero58, suc58, rec58 =>
     rec58 _ _
       (t tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 split58 zero58 suc58 rec58)
       (u tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 split58 zero58 suc58 rec58)
       (v tm var58 lam58 app58 tt58 pair58 fst58 snd58 left58 right58 split58 zero58 suc58 rec58)

v058 : {g:_}->{a:_} -> Tm58 (snoc58 g a) a
v058 = var58 vz58

v158 : {g:_}->{a:_}->{b:_} -> Tm58 (snoc58 (snoc58 g a) b) a
v158 = var58 (vs58 vz58)

v258 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm58 (snoc58 (snoc58 (snoc58 g a) b) c) a
v258 = var58 (vs58 (vs58 vz58))

v358 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm58 (snoc58 (snoc58 (snoc58 (snoc58 g a) b) c) d) a
v358 = var58 (vs58 (vs58 (vs58 vz58)))

tbool58 : Ty58
tbool58 = sum58 top58 top58

ttrue58 : {g:_} -> Tm58 g Main.tbool58
ttrue58 = left58 tt58

tfalse58 : {g:_} -> Tm58 g Main.tbool58
tfalse58 = right58 tt58

ifthenelse58 : {g:_}->{a:_} -> Tm58 g (arr58 Main.tbool58 (arr58 a (arr58 a a)))
ifthenelse58 = lam58 (lam58 (lam58 (split58 v258 (lam58 v258) (lam58 v158))))

times458 : {g:_}->{a:_} -> Tm58 g (arr58 (arr58 a a) (arr58 a a))
times458  = lam58 (lam58 (app58 v158 (app58 v158 (app58 v158 (app58 v158 v058)))))

add58 : {g:_} -> Tm58 g (arr58 Main.nat58 (arr58 Main.nat58 Main.nat58))
add58 = lam58 (rec58 v058
       (lam58 (lam58 (lam58 (suc58 (app58 v158 v058)))))
       (lam58 v058))

mul58 : {g:_} -> Tm58 g (arr58 Main.nat58 (arr58 Main.nat58 Main.nat58))
mul58 = lam58 (rec58 v058
       (lam58 (lam58 (lam58 (app58 (app58 add58 (app58 v158 v058)) v058))))
       (lam58 zero58))

fact58 : {g:_} -> Tm58 g (arr58 Main.nat58 Main.nat58)
fact58 = lam58 (rec58 v058 (lam58 (lam58 (app58 (app58 mul58 (suc58 v158)) v058)))
                 (suc58 zero58))

Ty59 : Type
Ty59 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat59 : Ty59
nat59 = \ _, nat59, _, _, _, _, _ => nat59
top59 : Ty59
top59 = \ _, _, top59, _, _, _, _ => top59
bot59 : Ty59
bot59 = \ _, _, _, bot59, _, _, _ => bot59

arr59 : Ty59-> Ty59-> Ty59
arr59 = \ a, b, ty, nat59, top59, bot59, arr59, prod, sum =>
     arr59 (a ty nat59 top59 bot59 arr59 prod sum) (b ty nat59 top59 bot59 arr59 prod sum)

prod59 : Ty59-> Ty59-> Ty59
prod59 = \ a, b, ty, nat59, top59, bot59, arr59, prod59, sum =>
     prod59 (a ty nat59 top59 bot59 arr59 prod59 sum) (b ty nat59 top59 bot59 arr59 prod59 sum)

sum59 : Ty59-> Ty59-> Ty59
sum59 = \ a, b, ty, nat59, top59, bot59, arr59, prod59, sum59 =>
     sum59 (a ty nat59 top59 bot59 arr59 prod59 sum59) (b ty nat59 top59 bot59 arr59 prod59 sum59)

Con59 : Type
Con59 = (Con59 : Type)
 -> (nil  : Con59)
 -> (snoc : Con59 -> Ty59-> Con59)
 -> Con59

nil59 : Con59
nil59 = \ con, nil59, snoc => nil59

snoc59 : Con59 -> Ty59-> Con59
snoc59 = \ g, a, con, nil59, snoc59 => snoc59 (g con nil59 snoc59) a

Var59 : Con59 -> Ty59-> Type
Var59 = \ g, a =>
    (Var59 : Con59 -> Ty59-> Type)
 -> (vz  : (g:_)->(a:_) -> Var59 (snoc59 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var59 g a -> Var59 (snoc59 g b) a)
 -> Var59 g a

vz59 : {g:_}->{a:_} -> Var59 (snoc59 g a) a
vz59 = \ var, vz59, vs => vz59 _ _

vs59 : {g:_}->{b:_}->{a:_} -> Var59 g a -> Var59 (snoc59 g b) a
vs59 = \ x, var, vz59, vs59 => vs59 _ _ _ (x var vz59 vs59)

Tm59 : Con59 -> Ty59-> Type
Tm59 = \ g, a =>
    (Tm59    : Con59 -> Ty59-> Type)
 -> (var   : (g:_)->(a:_)-> Var59 g a -> Tm59 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm59 (snoc59 g a) b -> Tm59 g (arr59 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm59 g (arr59 a b) -> Tm59 g a -> Tm59 g b)
 -> (tt    : (g:_)-> Tm59 g top59)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm59 g a -> Tm59 g b -> Tm59 g (prod59 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm59 g (prod59 a b) -> Tm59 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm59 g (prod59 a b) -> Tm59 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm59 g a -> Tm59 g (sum59 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm59 g b -> Tm59 g (sum59 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm59 g (sum59 a b) -> Tm59 g (arr59 a c) -> Tm59 g (arr59 b c) -> Tm59 g c)
 -> (zero  : (g:_)-> Tm59 g nat59)
 -> (suc   : (g:_)-> Tm59 g nat59 -> Tm59 g nat59)
 -> (rec   : (g:_)->(a:_) -> Tm59 g nat59 -> Tm59 g (arr59 nat59 (arr59 a a)) -> Tm59 g a -> Tm59 g a)
 -> Tm59 g a

var59 : {g:_}->{a:_} -> Var59 g a -> Tm59 g a
var59 = \ x, tm, var59, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var59 _ _ x

lam59 : {g:_}->{a:_}->{b:_}-> Tm59 (snoc59 g a) b -> Tm59 g (arr59 a b)
lam59 = \ t, tm, var59, lam59, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam59 _ _ _ (t tm var59 lam59 app tt pair fst snd left right split zero suc rec)

app59 : {g:_}->{a:_}->{b:_} -> Tm59 g (arr59 a b) -> Tm59 g a -> Tm59 g b
app59 = \ t, u, tm, var59, lam59, app59, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app59 _ _ _ (t tm var59 lam59 app59 tt pair fst snd left right split zero suc rec)
                (u tm var59 lam59 app59 tt pair fst snd left right split zero suc rec)

tt59 : {g:_} -> Tm59 g Main.top59
tt59 = \ tm, var59, lam59, app59, tt59, pair, fst, snd, left, right, split, zero, suc, rec => tt59 _

pair59 : {g:_}->{a:_}->{b:_} -> Tm59 g a -> Tm59 g b -> Tm59 g (prod59 a b)
pair59 = \ t, u, tm, var59, lam59, app59, tt59, pair59, fst, snd, left, right, split, zero, suc, rec =>
     pair59 _ _ _ (t tm var59 lam59 app59 tt59 pair59 fst snd left right split zero suc rec)
                 (u tm var59 lam59 app59 tt59 pair59 fst snd left right split zero suc rec)

fst59 : {g:_}->{a:_}->{b:_}-> Tm59 g (prod59 a b) -> Tm59 g a
fst59 = \ t, tm, var59, lam59, app59, tt59, pair59, fst59, snd, left, right, split, zero, suc, rec =>
     fst59 _ _ _ (t tm var59 lam59 app59 tt59 pair59 fst59 snd left right split zero suc rec)

snd59 : {g:_}->{a:_}->{b:_} -> Tm59 g (prod59 a b) -> Tm59 g b
snd59 = \ t, tm, var59, lam59, app59, tt59, pair59, fst59, snd59, left, right, split, zero, suc, rec =>
     snd59 _ _ _ (t tm var59 lam59 app59 tt59 pair59 fst59 snd59 left right split zero suc rec)

left59 : {g:_}->{a:_}->{b:_} -> Tm59 g a -> Tm59 g (sum59 a b)
left59 = \ t, tm, var59, lam59, app59, tt59, pair59, fst59, snd59, left59, right, split, zero, suc, rec =>
     left59 _ _ _ (t tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right split zero suc rec)

right59 : {g:_}->{a:_}->{b:_} -> Tm59 g b -> Tm59 g (sum59 a b)
right59 = \ t, tm, var59, lam59, app59, tt59, pair59, fst59, snd59, left59, right59, split, zero, suc, rec =>
     right59 _ _ _ (t tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 split zero suc rec)

split59 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm59 g (sum59 a b) -> Tm59 g (arr59 a c) -> Tm59 g (arr59 b c) -> Tm59 g c
split59 = \ t, u, v, tm, var59, lam59, app59, tt59, pair59, fst59, snd59, left59, right59, split59, zero, suc, rec =>
     split59 _ _ _ _
          (t tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 split59 zero suc rec)
          (u tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 split59 zero suc rec)
          (v tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 split59 zero suc rec)

zero59 : {g:_} -> Tm59 g Main.nat59
zero59 = \ tm, var59, lam59, app59, tt59, pair59, fst59, snd59, left59, right59, split59, zero59, suc, rec =>
  zero59 _

suc59 : {g:_} -> Tm59 g Main.nat59 -> Tm59 g Main.nat59
suc59 = \ t, tm, var59, lam59, app59, tt59, pair59, fst59, snd59, left59, right59, split59, zero59, suc59, rec =>
   suc59 _ (t tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 split59 zero59 suc59 rec)

rec59 : {g:_}->{a:_} -> Tm59 g Main.nat59 -> Tm59 g (arr59 Main.nat59 (arr59 a a)) -> Tm59 g a -> Tm59 g a
rec59 = \ t, u, v, tm, var59, lam59, app59, tt59, pair59, fst59, snd59, left59, right59, split59, zero59, suc59, rec59 =>
     rec59 _ _
       (t tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 split59 zero59 suc59 rec59)
       (u tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 split59 zero59 suc59 rec59)
       (v tm var59 lam59 app59 tt59 pair59 fst59 snd59 left59 right59 split59 zero59 suc59 rec59)

v059 : {g:_}->{a:_} -> Tm59 (snoc59 g a) a
v059 = var59 vz59

v159 : {g:_}->{a:_}->{b:_} -> Tm59 (snoc59 (snoc59 g a) b) a
v159 = var59 (vs59 vz59)

v259 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm59 (snoc59 (snoc59 (snoc59 g a) b) c) a
v259 = var59 (vs59 (vs59 vz59))

v359 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm59 (snoc59 (snoc59 (snoc59 (snoc59 g a) b) c) d) a
v359 = var59 (vs59 (vs59 (vs59 vz59)))

tbool59 : Ty59
tbool59 = sum59 top59 top59

ttrue59 : {g:_} -> Tm59 g Main.tbool59
ttrue59 = left59 tt59

tfalse59 : {g:_} -> Tm59 g Main.tbool59
tfalse59 = right59 tt59

ifthenelse59 : {g:_}->{a:_} -> Tm59 g (arr59 Main.tbool59 (arr59 a (arr59 a a)))
ifthenelse59 = lam59 (lam59 (lam59 (split59 v259 (lam59 v259) (lam59 v159))))

times459 : {g:_}->{a:_} -> Tm59 g (arr59 (arr59 a a) (arr59 a a))
times459  = lam59 (lam59 (app59 v159 (app59 v159 (app59 v159 (app59 v159 v059)))))

add59 : {g:_} -> Tm59 g (arr59 Main.nat59 (arr59 Main.nat59 Main.nat59))
add59 = lam59 (rec59 v059
       (lam59 (lam59 (lam59 (suc59 (app59 v159 v059)))))
       (lam59 v059))

mul59 : {g:_} -> Tm59 g (arr59 Main.nat59 (arr59 Main.nat59 Main.nat59))
mul59 = lam59 (rec59 v059
       (lam59 (lam59 (lam59 (app59 (app59 add59 (app59 v159 v059)) v059))))
       (lam59 zero59))

fact59 : {g:_} -> Tm59 g (arr59 Main.nat59 Main.nat59)
fact59 = lam59 (rec59 v059 (lam59 (lam59 (app59 (app59 mul59 (suc59 v159)) v059)))
                 (suc59 zero59))

Ty60 : Type
Ty60 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat60 : Ty60
nat60 = \ _, nat60, _, _, _, _, _ => nat60
top60 : Ty60
top60 = \ _, _, top60, _, _, _, _ => top60
bot60 : Ty60
bot60 = \ _, _, _, bot60, _, _, _ => bot60

arr60 : Ty60-> Ty60-> Ty60
arr60 = \ a, b, ty, nat60, top60, bot60, arr60, prod, sum =>
     arr60 (a ty nat60 top60 bot60 arr60 prod sum) (b ty nat60 top60 bot60 arr60 prod sum)

prod60 : Ty60-> Ty60-> Ty60
prod60 = \ a, b, ty, nat60, top60, bot60, arr60, prod60, sum =>
     prod60 (a ty nat60 top60 bot60 arr60 prod60 sum) (b ty nat60 top60 bot60 arr60 prod60 sum)

sum60 : Ty60-> Ty60-> Ty60
sum60 = \ a, b, ty, nat60, top60, bot60, arr60, prod60, sum60 =>
     sum60 (a ty nat60 top60 bot60 arr60 prod60 sum60) (b ty nat60 top60 bot60 arr60 prod60 sum60)

Con60 : Type
Con60 = (Con60 : Type)
 -> (nil  : Con60)
 -> (snoc : Con60 -> Ty60-> Con60)
 -> Con60

nil60 : Con60
nil60 = \ con, nil60, snoc => nil60

snoc60 : Con60 -> Ty60-> Con60
snoc60 = \ g, a, con, nil60, snoc60 => snoc60 (g con nil60 snoc60) a

Var60 : Con60 -> Ty60-> Type
Var60 = \ g, a =>
    (Var60 : Con60 -> Ty60-> Type)
 -> (vz  : (g:_)->(a:_) -> Var60 (snoc60 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var60 g a -> Var60 (snoc60 g b) a)
 -> Var60 g a

vz60 : {g:_}->{a:_} -> Var60 (snoc60 g a) a
vz60 = \ var, vz60, vs => vz60 _ _

vs60 : {g:_}->{b:_}->{a:_} -> Var60 g a -> Var60 (snoc60 g b) a
vs60 = \ x, var, vz60, vs60 => vs60 _ _ _ (x var vz60 vs60)

Tm60 : Con60 -> Ty60-> Type
Tm60 = \ g, a =>
    (Tm60    : Con60 -> Ty60-> Type)
 -> (var   : (g:_)->(a:_)-> Var60 g a -> Tm60 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm60 (snoc60 g a) b -> Tm60 g (arr60 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm60 g (arr60 a b) -> Tm60 g a -> Tm60 g b)
 -> (tt    : (g:_)-> Tm60 g top60)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm60 g a -> Tm60 g b -> Tm60 g (prod60 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm60 g (prod60 a b) -> Tm60 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm60 g (prod60 a b) -> Tm60 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm60 g a -> Tm60 g (sum60 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm60 g b -> Tm60 g (sum60 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm60 g (sum60 a b) -> Tm60 g (arr60 a c) -> Tm60 g (arr60 b c) -> Tm60 g c)
 -> (zero  : (g:_)-> Tm60 g nat60)
 -> (suc   : (g:_)-> Tm60 g nat60 -> Tm60 g nat60)
 -> (rec   : (g:_)->(a:_) -> Tm60 g nat60 -> Tm60 g (arr60 nat60 (arr60 a a)) -> Tm60 g a -> Tm60 g a)
 -> Tm60 g a

var60 : {g:_}->{a:_} -> Var60 g a -> Tm60 g a
var60 = \ x, tm, var60, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var60 _ _ x

lam60 : {g:_}->{a:_}->{b:_}-> Tm60 (snoc60 g a) b -> Tm60 g (arr60 a b)
lam60 = \ t, tm, var60, lam60, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam60 _ _ _ (t tm var60 lam60 app tt pair fst snd left right split zero suc rec)

app60 : {g:_}->{a:_}->{b:_} -> Tm60 g (arr60 a b) -> Tm60 g a -> Tm60 g b
app60 = \ t, u, tm, var60, lam60, app60, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app60 _ _ _ (t tm var60 lam60 app60 tt pair fst snd left right split zero suc rec)
                (u tm var60 lam60 app60 tt pair fst snd left right split zero suc rec)

tt60 : {g:_} -> Tm60 g Main.top60
tt60 = \ tm, var60, lam60, app60, tt60, pair, fst, snd, left, right, split, zero, suc, rec => tt60 _

pair60 : {g:_}->{a:_}->{b:_} -> Tm60 g a -> Tm60 g b -> Tm60 g (prod60 a b)
pair60 = \ t, u, tm, var60, lam60, app60, tt60, pair60, fst, snd, left, right, split, zero, suc, rec =>
     pair60 _ _ _ (t tm var60 lam60 app60 tt60 pair60 fst snd left right split zero suc rec)
                 (u tm var60 lam60 app60 tt60 pair60 fst snd left right split zero suc rec)

fst60 : {g:_}->{a:_}->{b:_}-> Tm60 g (prod60 a b) -> Tm60 g a
fst60 = \ t, tm, var60, lam60, app60, tt60, pair60, fst60, snd, left, right, split, zero, suc, rec =>
     fst60 _ _ _ (t tm var60 lam60 app60 tt60 pair60 fst60 snd left right split zero suc rec)

snd60 : {g:_}->{a:_}->{b:_} -> Tm60 g (prod60 a b) -> Tm60 g b
snd60 = \ t, tm, var60, lam60, app60, tt60, pair60, fst60, snd60, left, right, split, zero, suc, rec =>
     snd60 _ _ _ (t tm var60 lam60 app60 tt60 pair60 fst60 snd60 left right split zero suc rec)

left60 : {g:_}->{a:_}->{b:_} -> Tm60 g a -> Tm60 g (sum60 a b)
left60 = \ t, tm, var60, lam60, app60, tt60, pair60, fst60, snd60, left60, right, split, zero, suc, rec =>
     left60 _ _ _ (t tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right split zero suc rec)

right60 : {g:_}->{a:_}->{b:_} -> Tm60 g b -> Tm60 g (sum60 a b)
right60 = \ t, tm, var60, lam60, app60, tt60, pair60, fst60, snd60, left60, right60, split, zero, suc, rec =>
     right60 _ _ _ (t tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 split zero suc rec)

split60 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm60 g (sum60 a b) -> Tm60 g (arr60 a c) -> Tm60 g (arr60 b c) -> Tm60 g c
split60 = \ t, u, v, tm, var60, lam60, app60, tt60, pair60, fst60, snd60, left60, right60, split60, zero, suc, rec =>
     split60 _ _ _ _
          (t tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 split60 zero suc rec)
          (u tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 split60 zero suc rec)
          (v tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 split60 zero suc rec)

zero60 : {g:_} -> Tm60 g Main.nat60
zero60 = \ tm, var60, lam60, app60, tt60, pair60, fst60, snd60, left60, right60, split60, zero60, suc, rec =>
  zero60 _

suc60 : {g:_} -> Tm60 g Main.nat60 -> Tm60 g Main.nat60
suc60 = \ t, tm, var60, lam60, app60, tt60, pair60, fst60, snd60, left60, right60, split60, zero60, suc60, rec =>
   suc60 _ (t tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 split60 zero60 suc60 rec)

rec60 : {g:_}->{a:_} -> Tm60 g Main.nat60 -> Tm60 g (arr60 Main.nat60 (arr60 a a)) -> Tm60 g a -> Tm60 g a
rec60 = \ t, u, v, tm, var60, lam60, app60, tt60, pair60, fst60, snd60, left60, right60, split60, zero60, suc60, rec60 =>
     rec60 _ _
       (t tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 split60 zero60 suc60 rec60)
       (u tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 split60 zero60 suc60 rec60)
       (v tm var60 lam60 app60 tt60 pair60 fst60 snd60 left60 right60 split60 zero60 suc60 rec60)

v060 : {g:_}->{a:_} -> Tm60 (snoc60 g a) a
v060 = var60 vz60

v160 : {g:_}->{a:_}->{b:_} -> Tm60 (snoc60 (snoc60 g a) b) a
v160 = var60 (vs60 vz60)

v260 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm60 (snoc60 (snoc60 (snoc60 g a) b) c) a
v260 = var60 (vs60 (vs60 vz60))

v360 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm60 (snoc60 (snoc60 (snoc60 (snoc60 g a) b) c) d) a
v360 = var60 (vs60 (vs60 (vs60 vz60)))

tbool60 : Ty60
tbool60 = sum60 top60 top60

ttrue60 : {g:_} -> Tm60 g Main.tbool60
ttrue60 = left60 tt60

tfalse60 : {g:_} -> Tm60 g Main.tbool60
tfalse60 = right60 tt60

ifthenelse60 : {g:_}->{a:_} -> Tm60 g (arr60 Main.tbool60 (arr60 a (arr60 a a)))
ifthenelse60 = lam60 (lam60 (lam60 (split60 v260 (lam60 v260) (lam60 v160))))

times460 : {g:_}->{a:_} -> Tm60 g (arr60 (arr60 a a) (arr60 a a))
times460  = lam60 (lam60 (app60 v160 (app60 v160 (app60 v160 (app60 v160 v060)))))

add60 : {g:_} -> Tm60 g (arr60 Main.nat60 (arr60 Main.nat60 Main.nat60))
add60 = lam60 (rec60 v060
       (lam60 (lam60 (lam60 (suc60 (app60 v160 v060)))))
       (lam60 v060))

mul60 : {g:_} -> Tm60 g (arr60 Main.nat60 (arr60 Main.nat60 Main.nat60))
mul60 = lam60 (rec60 v060
       (lam60 (lam60 (lam60 (app60 (app60 add60 (app60 v160 v060)) v060))))
       (lam60 zero60))

fact60 : {g:_} -> Tm60 g (arr60 Main.nat60 Main.nat60)
fact60 = lam60 (rec60 v060 (lam60 (lam60 (app60 (app60 mul60 (suc60 v160)) v060)))
                 (suc60 zero60))

Ty61 : Type
Ty61 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat61 : Ty61
nat61 = \ _, nat61, _, _, _, _, _ => nat61
top61 : Ty61
top61 = \ _, _, top61, _, _, _, _ => top61
bot61 : Ty61
bot61 = \ _, _, _, bot61, _, _, _ => bot61

arr61 : Ty61-> Ty61-> Ty61
arr61 = \ a, b, ty, nat61, top61, bot61, arr61, prod, sum =>
     arr61 (a ty nat61 top61 bot61 arr61 prod sum) (b ty nat61 top61 bot61 arr61 prod sum)

prod61 : Ty61-> Ty61-> Ty61
prod61 = \ a, b, ty, nat61, top61, bot61, arr61, prod61, sum =>
     prod61 (a ty nat61 top61 bot61 arr61 prod61 sum) (b ty nat61 top61 bot61 arr61 prod61 sum)

sum61 : Ty61-> Ty61-> Ty61
sum61 = \ a, b, ty, nat61, top61, bot61, arr61, prod61, sum61 =>
     sum61 (a ty nat61 top61 bot61 arr61 prod61 sum61) (b ty nat61 top61 bot61 arr61 prod61 sum61)

Con61 : Type
Con61 = (Con61 : Type)
 -> (nil  : Con61)
 -> (snoc : Con61 -> Ty61-> Con61)
 -> Con61

nil61 : Con61
nil61 = \ con, nil61, snoc => nil61

snoc61 : Con61 -> Ty61-> Con61
snoc61 = \ g, a, con, nil61, snoc61 => snoc61 (g con nil61 snoc61) a

Var61 : Con61 -> Ty61-> Type
Var61 = \ g, a =>
    (Var61 : Con61 -> Ty61-> Type)
 -> (vz  : (g:_)->(a:_) -> Var61 (snoc61 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var61 g a -> Var61 (snoc61 g b) a)
 -> Var61 g a

vz61 : {g:_}->{a:_} -> Var61 (snoc61 g a) a
vz61 = \ var, vz61, vs => vz61 _ _

vs61 : {g:_}->{b:_}->{a:_} -> Var61 g a -> Var61 (snoc61 g b) a
vs61 = \ x, var, vz61, vs61 => vs61 _ _ _ (x var vz61 vs61)

Tm61 : Con61 -> Ty61-> Type
Tm61 = \ g, a =>
    (Tm61    : Con61 -> Ty61-> Type)
 -> (var   : (g:_)->(a:_)-> Var61 g a -> Tm61 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm61 (snoc61 g a) b -> Tm61 g (arr61 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm61 g (arr61 a b) -> Tm61 g a -> Tm61 g b)
 -> (tt    : (g:_)-> Tm61 g top61)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm61 g a -> Tm61 g b -> Tm61 g (prod61 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm61 g (prod61 a b) -> Tm61 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm61 g (prod61 a b) -> Tm61 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm61 g a -> Tm61 g (sum61 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm61 g b -> Tm61 g (sum61 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm61 g (sum61 a b) -> Tm61 g (arr61 a c) -> Tm61 g (arr61 b c) -> Tm61 g c)
 -> (zero  : (g:_)-> Tm61 g nat61)
 -> (suc   : (g:_)-> Tm61 g nat61 -> Tm61 g nat61)
 -> (rec   : (g:_)->(a:_) -> Tm61 g nat61 -> Tm61 g (arr61 nat61 (arr61 a a)) -> Tm61 g a -> Tm61 g a)
 -> Tm61 g a

var61 : {g:_}->{a:_} -> Var61 g a -> Tm61 g a
var61 = \ x, tm, var61, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var61 _ _ x

lam61 : {g:_}->{a:_}->{b:_}-> Tm61 (snoc61 g a) b -> Tm61 g (arr61 a b)
lam61 = \ t, tm, var61, lam61, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam61 _ _ _ (t tm var61 lam61 app tt pair fst snd left right split zero suc rec)

app61 : {g:_}->{a:_}->{b:_} -> Tm61 g (arr61 a b) -> Tm61 g a -> Tm61 g b
app61 = \ t, u, tm, var61, lam61, app61, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app61 _ _ _ (t tm var61 lam61 app61 tt pair fst snd left right split zero suc rec)
                (u tm var61 lam61 app61 tt pair fst snd left right split zero suc rec)

tt61 : {g:_} -> Tm61 g Main.top61
tt61 = \ tm, var61, lam61, app61, tt61, pair, fst, snd, left, right, split, zero, suc, rec => tt61 _

pair61 : {g:_}->{a:_}->{b:_} -> Tm61 g a -> Tm61 g b -> Tm61 g (prod61 a b)
pair61 = \ t, u, tm, var61, lam61, app61, tt61, pair61, fst, snd, left, right, split, zero, suc, rec =>
     pair61 _ _ _ (t tm var61 lam61 app61 tt61 pair61 fst snd left right split zero suc rec)
                 (u tm var61 lam61 app61 tt61 pair61 fst snd left right split zero suc rec)

fst61 : {g:_}->{a:_}->{b:_}-> Tm61 g (prod61 a b) -> Tm61 g a
fst61 = \ t, tm, var61, lam61, app61, tt61, pair61, fst61, snd, left, right, split, zero, suc, rec =>
     fst61 _ _ _ (t tm var61 lam61 app61 tt61 pair61 fst61 snd left right split zero suc rec)

snd61 : {g:_}->{a:_}->{b:_} -> Tm61 g (prod61 a b) -> Tm61 g b
snd61 = \ t, tm, var61, lam61, app61, tt61, pair61, fst61, snd61, left, right, split, zero, suc, rec =>
     snd61 _ _ _ (t tm var61 lam61 app61 tt61 pair61 fst61 snd61 left right split zero suc rec)

left61 : {g:_}->{a:_}->{b:_} -> Tm61 g a -> Tm61 g (sum61 a b)
left61 = \ t, tm, var61, lam61, app61, tt61, pair61, fst61, snd61, left61, right, split, zero, suc, rec =>
     left61 _ _ _ (t tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right split zero suc rec)

right61 : {g:_}->{a:_}->{b:_} -> Tm61 g b -> Tm61 g (sum61 a b)
right61 = \ t, tm, var61, lam61, app61, tt61, pair61, fst61, snd61, left61, right61, split, zero, suc, rec =>
     right61 _ _ _ (t tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 split zero suc rec)

split61 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm61 g (sum61 a b) -> Tm61 g (arr61 a c) -> Tm61 g (arr61 b c) -> Tm61 g c
split61 = \ t, u, v, tm, var61, lam61, app61, tt61, pair61, fst61, snd61, left61, right61, split61, zero, suc, rec =>
     split61 _ _ _ _
          (t tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 split61 zero suc rec)
          (u tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 split61 zero suc rec)
          (v tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 split61 zero suc rec)

zero61 : {g:_} -> Tm61 g Main.nat61
zero61 = \ tm, var61, lam61, app61, tt61, pair61, fst61, snd61, left61, right61, split61, zero61, suc, rec =>
  zero61 _

suc61 : {g:_} -> Tm61 g Main.nat61 -> Tm61 g Main.nat61
suc61 = \ t, tm, var61, lam61, app61, tt61, pair61, fst61, snd61, left61, right61, split61, zero61, suc61, rec =>
   suc61 _ (t tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 split61 zero61 suc61 rec)

rec61 : {g:_}->{a:_} -> Tm61 g Main.nat61 -> Tm61 g (arr61 Main.nat61 (arr61 a a)) -> Tm61 g a -> Tm61 g a
rec61 = \ t, u, v, tm, var61, lam61, app61, tt61, pair61, fst61, snd61, left61, right61, split61, zero61, suc61, rec61 =>
     rec61 _ _
       (t tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 split61 zero61 suc61 rec61)
       (u tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 split61 zero61 suc61 rec61)
       (v tm var61 lam61 app61 tt61 pair61 fst61 snd61 left61 right61 split61 zero61 suc61 rec61)

v061 : {g:_}->{a:_} -> Tm61 (snoc61 g a) a
v061 = var61 vz61

v161 : {g:_}->{a:_}->{b:_} -> Tm61 (snoc61 (snoc61 g a) b) a
v161 = var61 (vs61 vz61)

v261 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm61 (snoc61 (snoc61 (snoc61 g a) b) c) a
v261 = var61 (vs61 (vs61 vz61))

v361 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm61 (snoc61 (snoc61 (snoc61 (snoc61 g a) b) c) d) a
v361 = var61 (vs61 (vs61 (vs61 vz61)))

tbool61 : Ty61
tbool61 = sum61 top61 top61

ttrue61 : {g:_} -> Tm61 g Main.tbool61
ttrue61 = left61 tt61

tfalse61 : {g:_} -> Tm61 g Main.tbool61
tfalse61 = right61 tt61

ifthenelse61 : {g:_}->{a:_} -> Tm61 g (arr61 Main.tbool61 (arr61 a (arr61 a a)))
ifthenelse61 = lam61 (lam61 (lam61 (split61 v261 (lam61 v261) (lam61 v161))))

times461 : {g:_}->{a:_} -> Tm61 g (arr61 (arr61 a a) (arr61 a a))
times461  = lam61 (lam61 (app61 v161 (app61 v161 (app61 v161 (app61 v161 v061)))))

add61 : {g:_} -> Tm61 g (arr61 Main.nat61 (arr61 Main.nat61 Main.nat61))
add61 = lam61 (rec61 v061
       (lam61 (lam61 (lam61 (suc61 (app61 v161 v061)))))
       (lam61 v061))

mul61 : {g:_} -> Tm61 g (arr61 Main.nat61 (arr61 Main.nat61 Main.nat61))
mul61 = lam61 (rec61 v061
       (lam61 (lam61 (lam61 (app61 (app61 add61 (app61 v161 v061)) v061))))
       (lam61 zero61))

fact61 : {g:_} -> Tm61 g (arr61 Main.nat61 Main.nat61)
fact61 = lam61 (rec61 v061 (lam61 (lam61 (app61 (app61 mul61 (suc61 v161)) v061)))
                 (suc61 zero61))

Ty62 : Type
Ty62 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat62 : Ty62
nat62 = \ _, nat62, _, _, _, _, _ => nat62
top62 : Ty62
top62 = \ _, _, top62, _, _, _, _ => top62
bot62 : Ty62
bot62 = \ _, _, _, bot62, _, _, _ => bot62

arr62 : Ty62-> Ty62-> Ty62
arr62 = \ a, b, ty, nat62, top62, bot62, arr62, prod, sum =>
     arr62 (a ty nat62 top62 bot62 arr62 prod sum) (b ty nat62 top62 bot62 arr62 prod sum)

prod62 : Ty62-> Ty62-> Ty62
prod62 = \ a, b, ty, nat62, top62, bot62, arr62, prod62, sum =>
     prod62 (a ty nat62 top62 bot62 arr62 prod62 sum) (b ty nat62 top62 bot62 arr62 prod62 sum)

sum62 : Ty62-> Ty62-> Ty62
sum62 = \ a, b, ty, nat62, top62, bot62, arr62, prod62, sum62 =>
     sum62 (a ty nat62 top62 bot62 arr62 prod62 sum62) (b ty nat62 top62 bot62 arr62 prod62 sum62)

Con62 : Type
Con62 = (Con62 : Type)
 -> (nil  : Con62)
 -> (snoc : Con62 -> Ty62-> Con62)
 -> Con62

nil62 : Con62
nil62 = \ con, nil62, snoc => nil62

snoc62 : Con62 -> Ty62-> Con62
snoc62 = \ g, a, con, nil62, snoc62 => snoc62 (g con nil62 snoc62) a

Var62 : Con62 -> Ty62-> Type
Var62 = \ g, a =>
    (Var62 : Con62 -> Ty62-> Type)
 -> (vz  : (g:_)->(a:_) -> Var62 (snoc62 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var62 g a -> Var62 (snoc62 g b) a)
 -> Var62 g a

vz62 : {g:_}->{a:_} -> Var62 (snoc62 g a) a
vz62 = \ var, vz62, vs => vz62 _ _

vs62 : {g:_}->{b:_}->{a:_} -> Var62 g a -> Var62 (snoc62 g b) a
vs62 = \ x, var, vz62, vs62 => vs62 _ _ _ (x var vz62 vs62)

Tm62 : Con62 -> Ty62-> Type
Tm62 = \ g, a =>
    (Tm62    : Con62 -> Ty62-> Type)
 -> (var   : (g:_)->(a:_)-> Var62 g a -> Tm62 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm62 (snoc62 g a) b -> Tm62 g (arr62 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm62 g (arr62 a b) -> Tm62 g a -> Tm62 g b)
 -> (tt    : (g:_)-> Tm62 g top62)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm62 g a -> Tm62 g b -> Tm62 g (prod62 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm62 g (prod62 a b) -> Tm62 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm62 g (prod62 a b) -> Tm62 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm62 g a -> Tm62 g (sum62 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm62 g b -> Tm62 g (sum62 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm62 g (sum62 a b) -> Tm62 g (arr62 a c) -> Tm62 g (arr62 b c) -> Tm62 g c)
 -> (zero  : (g:_)-> Tm62 g nat62)
 -> (suc   : (g:_)-> Tm62 g nat62 -> Tm62 g nat62)
 -> (rec   : (g:_)->(a:_) -> Tm62 g nat62 -> Tm62 g (arr62 nat62 (arr62 a a)) -> Tm62 g a -> Tm62 g a)
 -> Tm62 g a

var62 : {g:_}->{a:_} -> Var62 g a -> Tm62 g a
var62 = \ x, tm, var62, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var62 _ _ x

lam62 : {g:_}->{a:_}->{b:_}-> Tm62 (snoc62 g a) b -> Tm62 g (arr62 a b)
lam62 = \ t, tm, var62, lam62, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam62 _ _ _ (t tm var62 lam62 app tt pair fst snd left right split zero suc rec)

app62 : {g:_}->{a:_}->{b:_} -> Tm62 g (arr62 a b) -> Tm62 g a -> Tm62 g b
app62 = \ t, u, tm, var62, lam62, app62, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app62 _ _ _ (t tm var62 lam62 app62 tt pair fst snd left right split zero suc rec)
                (u tm var62 lam62 app62 tt pair fst snd left right split zero suc rec)

tt62 : {g:_} -> Tm62 g Main.top62
tt62 = \ tm, var62, lam62, app62, tt62, pair, fst, snd, left, right, split, zero, suc, rec => tt62 _

pair62 : {g:_}->{a:_}->{b:_} -> Tm62 g a -> Tm62 g b -> Tm62 g (prod62 a b)
pair62 = \ t, u, tm, var62, lam62, app62, tt62, pair62, fst, snd, left, right, split, zero, suc, rec =>
     pair62 _ _ _ (t tm var62 lam62 app62 tt62 pair62 fst snd left right split zero suc rec)
                 (u tm var62 lam62 app62 tt62 pair62 fst snd left right split zero suc rec)

fst62 : {g:_}->{a:_}->{b:_}-> Tm62 g (prod62 a b) -> Tm62 g a
fst62 = \ t, tm, var62, lam62, app62, tt62, pair62, fst62, snd, left, right, split, zero, suc, rec =>
     fst62 _ _ _ (t tm var62 lam62 app62 tt62 pair62 fst62 snd left right split zero suc rec)

snd62 : {g:_}->{a:_}->{b:_} -> Tm62 g (prod62 a b) -> Tm62 g b
snd62 = \ t, tm, var62, lam62, app62, tt62, pair62, fst62, snd62, left, right, split, zero, suc, rec =>
     snd62 _ _ _ (t tm var62 lam62 app62 tt62 pair62 fst62 snd62 left right split zero suc rec)

left62 : {g:_}->{a:_}->{b:_} -> Tm62 g a -> Tm62 g (sum62 a b)
left62 = \ t, tm, var62, lam62, app62, tt62, pair62, fst62, snd62, left62, right, split, zero, suc, rec =>
     left62 _ _ _ (t tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right split zero suc rec)

right62 : {g:_}->{a:_}->{b:_} -> Tm62 g b -> Tm62 g (sum62 a b)
right62 = \ t, tm, var62, lam62, app62, tt62, pair62, fst62, snd62, left62, right62, split, zero, suc, rec =>
     right62 _ _ _ (t tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 split zero suc rec)

split62 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm62 g (sum62 a b) -> Tm62 g (arr62 a c) -> Tm62 g (arr62 b c) -> Tm62 g c
split62 = \ t, u, v, tm, var62, lam62, app62, tt62, pair62, fst62, snd62, left62, right62, split62, zero, suc, rec =>
     split62 _ _ _ _
          (t tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 split62 zero suc rec)
          (u tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 split62 zero suc rec)
          (v tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 split62 zero suc rec)

zero62 : {g:_} -> Tm62 g Main.nat62
zero62 = \ tm, var62, lam62, app62, tt62, pair62, fst62, snd62, left62, right62, split62, zero62, suc, rec =>
  zero62 _

suc62 : {g:_} -> Tm62 g Main.nat62 -> Tm62 g Main.nat62
suc62 = \ t, tm, var62, lam62, app62, tt62, pair62, fst62, snd62, left62, right62, split62, zero62, suc62, rec =>
   suc62 _ (t tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 split62 zero62 suc62 rec)

rec62 : {g:_}->{a:_} -> Tm62 g Main.nat62 -> Tm62 g (arr62 Main.nat62 (arr62 a a)) -> Tm62 g a -> Tm62 g a
rec62 = \ t, u, v, tm, var62, lam62, app62, tt62, pair62, fst62, snd62, left62, right62, split62, zero62, suc62, rec62 =>
     rec62 _ _
       (t tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 split62 zero62 suc62 rec62)
       (u tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 split62 zero62 suc62 rec62)
       (v tm var62 lam62 app62 tt62 pair62 fst62 snd62 left62 right62 split62 zero62 suc62 rec62)

v062 : {g:_}->{a:_} -> Tm62 (snoc62 g a) a
v062 = var62 vz62

v162 : {g:_}->{a:_}->{b:_} -> Tm62 (snoc62 (snoc62 g a) b) a
v162 = var62 (vs62 vz62)

v262 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm62 (snoc62 (snoc62 (snoc62 g a) b) c) a
v262 = var62 (vs62 (vs62 vz62))

v362 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm62 (snoc62 (snoc62 (snoc62 (snoc62 g a) b) c) d) a
v362 = var62 (vs62 (vs62 (vs62 vz62)))

tbool62 : Ty62
tbool62 = sum62 top62 top62

ttrue62 : {g:_} -> Tm62 g Main.tbool62
ttrue62 = left62 tt62

tfalse62 : {g:_} -> Tm62 g Main.tbool62
tfalse62 = right62 tt62

ifthenelse62 : {g:_}->{a:_} -> Tm62 g (arr62 Main.tbool62 (arr62 a (arr62 a a)))
ifthenelse62 = lam62 (lam62 (lam62 (split62 v262 (lam62 v262) (lam62 v162))))

times462 : {g:_}->{a:_} -> Tm62 g (arr62 (arr62 a a) (arr62 a a))
times462  = lam62 (lam62 (app62 v162 (app62 v162 (app62 v162 (app62 v162 v062)))))

add62 : {g:_} -> Tm62 g (arr62 Main.nat62 (arr62 Main.nat62 Main.nat62))
add62 = lam62 (rec62 v062
       (lam62 (lam62 (lam62 (suc62 (app62 v162 v062)))))
       (lam62 v062))

mul62 : {g:_} -> Tm62 g (arr62 Main.nat62 (arr62 Main.nat62 Main.nat62))
mul62 = lam62 (rec62 v062
       (lam62 (lam62 (lam62 (app62 (app62 add62 (app62 v162 v062)) v062))))
       (lam62 zero62))

fact62 : {g:_} -> Tm62 g (arr62 Main.nat62 Main.nat62)
fact62 = lam62 (rec62 v062 (lam62 (lam62 (app62 (app62 mul62 (suc62 v162)) v062)))
                 (suc62 zero62))

Ty63 : Type
Ty63 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat63 : Ty63
nat63 = \ _, nat63, _, _, _, _, _ => nat63
top63 : Ty63
top63 = \ _, _, top63, _, _, _, _ => top63
bot63 : Ty63
bot63 = \ _, _, _, bot63, _, _, _ => bot63

arr63 : Ty63-> Ty63-> Ty63
arr63 = \ a, b, ty, nat63, top63, bot63, arr63, prod, sum =>
     arr63 (a ty nat63 top63 bot63 arr63 prod sum) (b ty nat63 top63 bot63 arr63 prod sum)

prod63 : Ty63-> Ty63-> Ty63
prod63 = \ a, b, ty, nat63, top63, bot63, arr63, prod63, sum =>
     prod63 (a ty nat63 top63 bot63 arr63 prod63 sum) (b ty nat63 top63 bot63 arr63 prod63 sum)

sum63 : Ty63-> Ty63-> Ty63
sum63 = \ a, b, ty, nat63, top63, bot63, arr63, prod63, sum63 =>
     sum63 (a ty nat63 top63 bot63 arr63 prod63 sum63) (b ty nat63 top63 bot63 arr63 prod63 sum63)

Con63 : Type
Con63 = (Con63 : Type)
 -> (nil  : Con63)
 -> (snoc : Con63 -> Ty63-> Con63)
 -> Con63

nil63 : Con63
nil63 = \ con, nil63, snoc => nil63

snoc63 : Con63 -> Ty63-> Con63
snoc63 = \ g, a, con, nil63, snoc63 => snoc63 (g con nil63 snoc63) a

Var63 : Con63 -> Ty63-> Type
Var63 = \ g, a =>
    (Var63 : Con63 -> Ty63-> Type)
 -> (vz  : (g:_)->(a:_) -> Var63 (snoc63 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var63 g a -> Var63 (snoc63 g b) a)
 -> Var63 g a

vz63 : {g:_}->{a:_} -> Var63 (snoc63 g a) a
vz63 = \ var, vz63, vs => vz63 _ _

vs63 : {g:_}->{b:_}->{a:_} -> Var63 g a -> Var63 (snoc63 g b) a
vs63 = \ x, var, vz63, vs63 => vs63 _ _ _ (x var vz63 vs63)

Tm63 : Con63 -> Ty63-> Type
Tm63 = \ g, a =>
    (Tm63    : Con63 -> Ty63-> Type)
 -> (var   : (g:_)->(a:_)-> Var63 g a -> Tm63 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm63 (snoc63 g a) b -> Tm63 g (arr63 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm63 g (arr63 a b) -> Tm63 g a -> Tm63 g b)
 -> (tt    : (g:_)-> Tm63 g top63)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm63 g a -> Tm63 g b -> Tm63 g (prod63 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm63 g (prod63 a b) -> Tm63 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm63 g (prod63 a b) -> Tm63 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm63 g a -> Tm63 g (sum63 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm63 g b -> Tm63 g (sum63 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm63 g (sum63 a b) -> Tm63 g (arr63 a c) -> Tm63 g (arr63 b c) -> Tm63 g c)
 -> (zero  : (g:_)-> Tm63 g nat63)
 -> (suc   : (g:_)-> Tm63 g nat63 -> Tm63 g nat63)
 -> (rec   : (g:_)->(a:_) -> Tm63 g nat63 -> Tm63 g (arr63 nat63 (arr63 a a)) -> Tm63 g a -> Tm63 g a)
 -> Tm63 g a

var63 : {g:_}->{a:_} -> Var63 g a -> Tm63 g a
var63 = \ x, tm, var63, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var63 _ _ x

lam63 : {g:_}->{a:_}->{b:_}-> Tm63 (snoc63 g a) b -> Tm63 g (arr63 a b)
lam63 = \ t, tm, var63, lam63, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam63 _ _ _ (t tm var63 lam63 app tt pair fst snd left right split zero suc rec)

app63 : {g:_}->{a:_}->{b:_} -> Tm63 g (arr63 a b) -> Tm63 g a -> Tm63 g b
app63 = \ t, u, tm, var63, lam63, app63, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app63 _ _ _ (t tm var63 lam63 app63 tt pair fst snd left right split zero suc rec)
                (u tm var63 lam63 app63 tt pair fst snd left right split zero suc rec)

tt63 : {g:_} -> Tm63 g Main.top63
tt63 = \ tm, var63, lam63, app63, tt63, pair, fst, snd, left, right, split, zero, suc, rec => tt63 _

pair63 : {g:_}->{a:_}->{b:_} -> Tm63 g a -> Tm63 g b -> Tm63 g (prod63 a b)
pair63 = \ t, u, tm, var63, lam63, app63, tt63, pair63, fst, snd, left, right, split, zero, suc, rec =>
     pair63 _ _ _ (t tm var63 lam63 app63 tt63 pair63 fst snd left right split zero suc rec)
                 (u tm var63 lam63 app63 tt63 pair63 fst snd left right split zero suc rec)

fst63 : {g:_}->{a:_}->{b:_}-> Tm63 g (prod63 a b) -> Tm63 g a
fst63 = \ t, tm, var63, lam63, app63, tt63, pair63, fst63, snd, left, right, split, zero, suc, rec =>
     fst63 _ _ _ (t tm var63 lam63 app63 tt63 pair63 fst63 snd left right split zero suc rec)

snd63 : {g:_}->{a:_}->{b:_} -> Tm63 g (prod63 a b) -> Tm63 g b
snd63 = \ t, tm, var63, lam63, app63, tt63, pair63, fst63, snd63, left, right, split, zero, suc, rec =>
     snd63 _ _ _ (t tm var63 lam63 app63 tt63 pair63 fst63 snd63 left right split zero suc rec)

left63 : {g:_}->{a:_}->{b:_} -> Tm63 g a -> Tm63 g (sum63 a b)
left63 = \ t, tm, var63, lam63, app63, tt63, pair63, fst63, snd63, left63, right, split, zero, suc, rec =>
     left63 _ _ _ (t tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right split zero suc rec)

right63 : {g:_}->{a:_}->{b:_} -> Tm63 g b -> Tm63 g (sum63 a b)
right63 = \ t, tm, var63, lam63, app63, tt63, pair63, fst63, snd63, left63, right63, split, zero, suc, rec =>
     right63 _ _ _ (t tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 split zero suc rec)

split63 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm63 g (sum63 a b) -> Tm63 g (arr63 a c) -> Tm63 g (arr63 b c) -> Tm63 g c
split63 = \ t, u, v, tm, var63, lam63, app63, tt63, pair63, fst63, snd63, left63, right63, split63, zero, suc, rec =>
     split63 _ _ _ _
          (t tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 split63 zero suc rec)
          (u tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 split63 zero suc rec)
          (v tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 split63 zero suc rec)

zero63 : {g:_} -> Tm63 g Main.nat63
zero63 = \ tm, var63, lam63, app63, tt63, pair63, fst63, snd63, left63, right63, split63, zero63, suc, rec =>
  zero63 _

suc63 : {g:_} -> Tm63 g Main.nat63 -> Tm63 g Main.nat63
suc63 = \ t, tm, var63, lam63, app63, tt63, pair63, fst63, snd63, left63, right63, split63, zero63, suc63, rec =>
   suc63 _ (t tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 split63 zero63 suc63 rec)

rec63 : {g:_}->{a:_} -> Tm63 g Main.nat63 -> Tm63 g (arr63 Main.nat63 (arr63 a a)) -> Tm63 g a -> Tm63 g a
rec63 = \ t, u, v, tm, var63, lam63, app63, tt63, pair63, fst63, snd63, left63, right63, split63, zero63, suc63, rec63 =>
     rec63 _ _
       (t tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 split63 zero63 suc63 rec63)
       (u tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 split63 zero63 suc63 rec63)
       (v tm var63 lam63 app63 tt63 pair63 fst63 snd63 left63 right63 split63 zero63 suc63 rec63)

v063 : {g:_}->{a:_} -> Tm63 (snoc63 g a) a
v063 = var63 vz63

v163 : {g:_}->{a:_}->{b:_} -> Tm63 (snoc63 (snoc63 g a) b) a
v163 = var63 (vs63 vz63)

v263 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm63 (snoc63 (snoc63 (snoc63 g a) b) c) a
v263 = var63 (vs63 (vs63 vz63))

v363 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm63 (snoc63 (snoc63 (snoc63 (snoc63 g a) b) c) d) a
v363 = var63 (vs63 (vs63 (vs63 vz63)))

tbool63 : Ty63
tbool63 = sum63 top63 top63

ttrue63 : {g:_} -> Tm63 g Main.tbool63
ttrue63 = left63 tt63

tfalse63 : {g:_} -> Tm63 g Main.tbool63
tfalse63 = right63 tt63

ifthenelse63 : {g:_}->{a:_} -> Tm63 g (arr63 Main.tbool63 (arr63 a (arr63 a a)))
ifthenelse63 = lam63 (lam63 (lam63 (split63 v263 (lam63 v263) (lam63 v163))))

times463 : {g:_}->{a:_} -> Tm63 g (arr63 (arr63 a a) (arr63 a a))
times463  = lam63 (lam63 (app63 v163 (app63 v163 (app63 v163 (app63 v163 v063)))))

add63 : {g:_} -> Tm63 g (arr63 Main.nat63 (arr63 Main.nat63 Main.nat63))
add63 = lam63 (rec63 v063
       (lam63 (lam63 (lam63 (suc63 (app63 v163 v063)))))
       (lam63 v063))

mul63 : {g:_} -> Tm63 g (arr63 Main.nat63 (arr63 Main.nat63 Main.nat63))
mul63 = lam63 (rec63 v063
       (lam63 (lam63 (lam63 (app63 (app63 add63 (app63 v163 v063)) v063))))
       (lam63 zero63))

fact63 : {g:_} -> Tm63 g (arr63 Main.nat63 Main.nat63)
fact63 = lam63 (rec63 v063 (lam63 (lam63 (app63 (app63 mul63 (suc63 v163)) v063)))
                 (suc63 zero63))

Ty64 : Type
Ty64 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat64 : Ty64
nat64 = \ _, nat64, _, _, _, _, _ => nat64
top64 : Ty64
top64 = \ _, _, top64, _, _, _, _ => top64
bot64 : Ty64
bot64 = \ _, _, _, bot64, _, _, _ => bot64

arr64 : Ty64-> Ty64-> Ty64
arr64 = \ a, b, ty, nat64, top64, bot64, arr64, prod, sum =>
     arr64 (a ty nat64 top64 bot64 arr64 prod sum) (b ty nat64 top64 bot64 arr64 prod sum)

prod64 : Ty64-> Ty64-> Ty64
prod64 = \ a, b, ty, nat64, top64, bot64, arr64, prod64, sum =>
     prod64 (a ty nat64 top64 bot64 arr64 prod64 sum) (b ty nat64 top64 bot64 arr64 prod64 sum)

sum64 : Ty64-> Ty64-> Ty64
sum64 = \ a, b, ty, nat64, top64, bot64, arr64, prod64, sum64 =>
     sum64 (a ty nat64 top64 bot64 arr64 prod64 sum64) (b ty nat64 top64 bot64 arr64 prod64 sum64)

Con64 : Type
Con64 = (Con64 : Type)
 -> (nil  : Con64)
 -> (snoc : Con64 -> Ty64-> Con64)
 -> Con64

nil64 : Con64
nil64 = \ con, nil64, snoc => nil64

snoc64 : Con64 -> Ty64-> Con64
snoc64 = \ g, a, con, nil64, snoc64 => snoc64 (g con nil64 snoc64) a

Var64 : Con64 -> Ty64-> Type
Var64 = \ g, a =>
    (Var64 : Con64 -> Ty64-> Type)
 -> (vz  : (g:_)->(a:_) -> Var64 (snoc64 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var64 g a -> Var64 (snoc64 g b) a)
 -> Var64 g a

vz64 : {g:_}->{a:_} -> Var64 (snoc64 g a) a
vz64 = \ var, vz64, vs => vz64 _ _

vs64 : {g:_}->{b:_}->{a:_} -> Var64 g a -> Var64 (snoc64 g b) a
vs64 = \ x, var, vz64, vs64 => vs64 _ _ _ (x var vz64 vs64)

Tm64 : Con64 -> Ty64-> Type
Tm64 = \ g, a =>
    (Tm64    : Con64 -> Ty64-> Type)
 -> (var   : (g:_)->(a:_)-> Var64 g a -> Tm64 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm64 (snoc64 g a) b -> Tm64 g (arr64 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm64 g (arr64 a b) -> Tm64 g a -> Tm64 g b)
 -> (tt    : (g:_)-> Tm64 g top64)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm64 g a -> Tm64 g b -> Tm64 g (prod64 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm64 g (prod64 a b) -> Tm64 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm64 g (prod64 a b) -> Tm64 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm64 g a -> Tm64 g (sum64 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm64 g b -> Tm64 g (sum64 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm64 g (sum64 a b) -> Tm64 g (arr64 a c) -> Tm64 g (arr64 b c) -> Tm64 g c)
 -> (zero  : (g:_)-> Tm64 g nat64)
 -> (suc   : (g:_)-> Tm64 g nat64 -> Tm64 g nat64)
 -> (rec   : (g:_)->(a:_) -> Tm64 g nat64 -> Tm64 g (arr64 nat64 (arr64 a a)) -> Tm64 g a -> Tm64 g a)
 -> Tm64 g a

var64 : {g:_}->{a:_} -> Var64 g a -> Tm64 g a
var64 = \ x, tm, var64, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var64 _ _ x

lam64 : {g:_}->{a:_}->{b:_}-> Tm64 (snoc64 g a) b -> Tm64 g (arr64 a b)
lam64 = \ t, tm, var64, lam64, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam64 _ _ _ (t tm var64 lam64 app tt pair fst snd left right split zero suc rec)

app64 : {g:_}->{a:_}->{b:_} -> Tm64 g (arr64 a b) -> Tm64 g a -> Tm64 g b
app64 = \ t, u, tm, var64, lam64, app64, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app64 _ _ _ (t tm var64 lam64 app64 tt pair fst snd left right split zero suc rec)
                (u tm var64 lam64 app64 tt pair fst snd left right split zero suc rec)

tt64 : {g:_} -> Tm64 g Main.top64
tt64 = \ tm, var64, lam64, app64, tt64, pair, fst, snd, left, right, split, zero, suc, rec => tt64 _

pair64 : {g:_}->{a:_}->{b:_} -> Tm64 g a -> Tm64 g b -> Tm64 g (prod64 a b)
pair64 = \ t, u, tm, var64, lam64, app64, tt64, pair64, fst, snd, left, right, split, zero, suc, rec =>
     pair64 _ _ _ (t tm var64 lam64 app64 tt64 pair64 fst snd left right split zero suc rec)
                 (u tm var64 lam64 app64 tt64 pair64 fst snd left right split zero suc rec)

fst64 : {g:_}->{a:_}->{b:_}-> Tm64 g (prod64 a b) -> Tm64 g a
fst64 = \ t, tm, var64, lam64, app64, tt64, pair64, fst64, snd, left, right, split, zero, suc, rec =>
     fst64 _ _ _ (t tm var64 lam64 app64 tt64 pair64 fst64 snd left right split zero suc rec)

snd64 : {g:_}->{a:_}->{b:_} -> Tm64 g (prod64 a b) -> Tm64 g b
snd64 = \ t, tm, var64, lam64, app64, tt64, pair64, fst64, snd64, left, right, split, zero, suc, rec =>
     snd64 _ _ _ (t tm var64 lam64 app64 tt64 pair64 fst64 snd64 left right split zero suc rec)

left64 : {g:_}->{a:_}->{b:_} -> Tm64 g a -> Tm64 g (sum64 a b)
left64 = \ t, tm, var64, lam64, app64, tt64, pair64, fst64, snd64, left64, right, split, zero, suc, rec =>
     left64 _ _ _ (t tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right split zero suc rec)

right64 : {g:_}->{a:_}->{b:_} -> Tm64 g b -> Tm64 g (sum64 a b)
right64 = \ t, tm, var64, lam64, app64, tt64, pair64, fst64, snd64, left64, right64, split, zero, suc, rec =>
     right64 _ _ _ (t tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 split zero suc rec)

split64 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm64 g (sum64 a b) -> Tm64 g (arr64 a c) -> Tm64 g (arr64 b c) -> Tm64 g c
split64 = \ t, u, v, tm, var64, lam64, app64, tt64, pair64, fst64, snd64, left64, right64, split64, zero, suc, rec =>
     split64 _ _ _ _
          (t tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 split64 zero suc rec)
          (u tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 split64 zero suc rec)
          (v tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 split64 zero suc rec)

zero64 : {g:_} -> Tm64 g Main.nat64
zero64 = \ tm, var64, lam64, app64, tt64, pair64, fst64, snd64, left64, right64, split64, zero64, suc, rec =>
  zero64 _

suc64 : {g:_} -> Tm64 g Main.nat64 -> Tm64 g Main.nat64
suc64 = \ t, tm, var64, lam64, app64, tt64, pair64, fst64, snd64, left64, right64, split64, zero64, suc64, rec =>
   suc64 _ (t tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 split64 zero64 suc64 rec)

rec64 : {g:_}->{a:_} -> Tm64 g Main.nat64 -> Tm64 g (arr64 Main.nat64 (arr64 a a)) -> Tm64 g a -> Tm64 g a
rec64 = \ t, u, v, tm, var64, lam64, app64, tt64, pair64, fst64, snd64, left64, right64, split64, zero64, suc64, rec64 =>
     rec64 _ _
       (t tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 split64 zero64 suc64 rec64)
       (u tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 split64 zero64 suc64 rec64)
       (v tm var64 lam64 app64 tt64 pair64 fst64 snd64 left64 right64 split64 zero64 suc64 rec64)

v064 : {g:_}->{a:_} -> Tm64 (snoc64 g a) a
v064 = var64 vz64

v164 : {g:_}->{a:_}->{b:_} -> Tm64 (snoc64 (snoc64 g a) b) a
v164 = var64 (vs64 vz64)

v264 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm64 (snoc64 (snoc64 (snoc64 g a) b) c) a
v264 = var64 (vs64 (vs64 vz64))

v364 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm64 (snoc64 (snoc64 (snoc64 (snoc64 g a) b) c) d) a
v364 = var64 (vs64 (vs64 (vs64 vz64)))

tbool64 : Ty64
tbool64 = sum64 top64 top64

ttrue64 : {g:_} -> Tm64 g Main.tbool64
ttrue64 = left64 tt64

tfalse64 : {g:_} -> Tm64 g Main.tbool64
tfalse64 = right64 tt64

ifthenelse64 : {g:_}->{a:_} -> Tm64 g (arr64 Main.tbool64 (arr64 a (arr64 a a)))
ifthenelse64 = lam64 (lam64 (lam64 (split64 v264 (lam64 v264) (lam64 v164))))

times464 : {g:_}->{a:_} -> Tm64 g (arr64 (arr64 a a) (arr64 a a))
times464  = lam64 (lam64 (app64 v164 (app64 v164 (app64 v164 (app64 v164 v064)))))

add64 : {g:_} -> Tm64 g (arr64 Main.nat64 (arr64 Main.nat64 Main.nat64))
add64 = lam64 (rec64 v064
       (lam64 (lam64 (lam64 (suc64 (app64 v164 v064)))))
       (lam64 v064))

mul64 : {g:_} -> Tm64 g (arr64 Main.nat64 (arr64 Main.nat64 Main.nat64))
mul64 = lam64 (rec64 v064
       (lam64 (lam64 (lam64 (app64 (app64 add64 (app64 v164 v064)) v064))))
       (lam64 zero64))

fact64 : {g:_} -> Tm64 g (arr64 Main.nat64 Main.nat64)
fact64 = lam64 (rec64 v064 (lam64 (lam64 (app64 (app64 mul64 (suc64 v164)) v064)))
                 (suc64 zero64))

Ty65 : Type
Ty65 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat65 : Ty65
nat65 = \ _, nat65, _, _, _, _, _ => nat65
top65 : Ty65
top65 = \ _, _, top65, _, _, _, _ => top65
bot65 : Ty65
bot65 = \ _, _, _, bot65, _, _, _ => bot65

arr65 : Ty65-> Ty65-> Ty65
arr65 = \ a, b, ty, nat65, top65, bot65, arr65, prod, sum =>
     arr65 (a ty nat65 top65 bot65 arr65 prod sum) (b ty nat65 top65 bot65 arr65 prod sum)

prod65 : Ty65-> Ty65-> Ty65
prod65 = \ a, b, ty, nat65, top65, bot65, arr65, prod65, sum =>
     prod65 (a ty nat65 top65 bot65 arr65 prod65 sum) (b ty nat65 top65 bot65 arr65 prod65 sum)

sum65 : Ty65-> Ty65-> Ty65
sum65 = \ a, b, ty, nat65, top65, bot65, arr65, prod65, sum65 =>
     sum65 (a ty nat65 top65 bot65 arr65 prod65 sum65) (b ty nat65 top65 bot65 arr65 prod65 sum65)

Con65 : Type
Con65 = (Con65 : Type)
 -> (nil  : Con65)
 -> (snoc : Con65 -> Ty65-> Con65)
 -> Con65

nil65 : Con65
nil65 = \ con, nil65, snoc => nil65

snoc65 : Con65 -> Ty65-> Con65
snoc65 = \ g, a, con, nil65, snoc65 => snoc65 (g con nil65 snoc65) a

Var65 : Con65 -> Ty65-> Type
Var65 = \ g, a =>
    (Var65 : Con65 -> Ty65-> Type)
 -> (vz  : (g:_)->(a:_) -> Var65 (snoc65 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var65 g a -> Var65 (snoc65 g b) a)
 -> Var65 g a

vz65 : {g:_}->{a:_} -> Var65 (snoc65 g a) a
vz65 = \ var, vz65, vs => vz65 _ _

vs65 : {g:_}->{b:_}->{a:_} -> Var65 g a -> Var65 (snoc65 g b) a
vs65 = \ x, var, vz65, vs65 => vs65 _ _ _ (x var vz65 vs65)

Tm65 : Con65 -> Ty65-> Type
Tm65 = \ g, a =>
    (Tm65    : Con65 -> Ty65-> Type)
 -> (var   : (g:_)->(a:_)-> Var65 g a -> Tm65 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm65 (snoc65 g a) b -> Tm65 g (arr65 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm65 g (arr65 a b) -> Tm65 g a -> Tm65 g b)
 -> (tt    : (g:_)-> Tm65 g top65)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm65 g a -> Tm65 g b -> Tm65 g (prod65 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm65 g (prod65 a b) -> Tm65 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm65 g (prod65 a b) -> Tm65 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm65 g a -> Tm65 g (sum65 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm65 g b -> Tm65 g (sum65 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm65 g (sum65 a b) -> Tm65 g (arr65 a c) -> Tm65 g (arr65 b c) -> Tm65 g c)
 -> (zero  : (g:_)-> Tm65 g nat65)
 -> (suc   : (g:_)-> Tm65 g nat65 -> Tm65 g nat65)
 -> (rec   : (g:_)->(a:_) -> Tm65 g nat65 -> Tm65 g (arr65 nat65 (arr65 a a)) -> Tm65 g a -> Tm65 g a)
 -> Tm65 g a

var65 : {g:_}->{a:_} -> Var65 g a -> Tm65 g a
var65 = \ x, tm, var65, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var65 _ _ x

lam65 : {g:_}->{a:_}->{b:_}-> Tm65 (snoc65 g a) b -> Tm65 g (arr65 a b)
lam65 = \ t, tm, var65, lam65, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam65 _ _ _ (t tm var65 lam65 app tt pair fst snd left right split zero suc rec)

app65 : {g:_}->{a:_}->{b:_} -> Tm65 g (arr65 a b) -> Tm65 g a -> Tm65 g b
app65 = \ t, u, tm, var65, lam65, app65, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app65 _ _ _ (t tm var65 lam65 app65 tt pair fst snd left right split zero suc rec)
                (u tm var65 lam65 app65 tt pair fst snd left right split zero suc rec)

tt65 : {g:_} -> Tm65 g Main.top65
tt65 = \ tm, var65, lam65, app65, tt65, pair, fst, snd, left, right, split, zero, suc, rec => tt65 _

pair65 : {g:_}->{a:_}->{b:_} -> Tm65 g a -> Tm65 g b -> Tm65 g (prod65 a b)
pair65 = \ t, u, tm, var65, lam65, app65, tt65, pair65, fst, snd, left, right, split, zero, suc, rec =>
     pair65 _ _ _ (t tm var65 lam65 app65 tt65 pair65 fst snd left right split zero suc rec)
                 (u tm var65 lam65 app65 tt65 pair65 fst snd left right split zero suc rec)

fst65 : {g:_}->{a:_}->{b:_}-> Tm65 g (prod65 a b) -> Tm65 g a
fst65 = \ t, tm, var65, lam65, app65, tt65, pair65, fst65, snd, left, right, split, zero, suc, rec =>
     fst65 _ _ _ (t tm var65 lam65 app65 tt65 pair65 fst65 snd left right split zero suc rec)

snd65 : {g:_}->{a:_}->{b:_} -> Tm65 g (prod65 a b) -> Tm65 g b
snd65 = \ t, tm, var65, lam65, app65, tt65, pair65, fst65, snd65, left, right, split, zero, suc, rec =>
     snd65 _ _ _ (t tm var65 lam65 app65 tt65 pair65 fst65 snd65 left right split zero suc rec)

left65 : {g:_}->{a:_}->{b:_} -> Tm65 g a -> Tm65 g (sum65 a b)
left65 = \ t, tm, var65, lam65, app65, tt65, pair65, fst65, snd65, left65, right, split, zero, suc, rec =>
     left65 _ _ _ (t tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right split zero suc rec)

right65 : {g:_}->{a:_}->{b:_} -> Tm65 g b -> Tm65 g (sum65 a b)
right65 = \ t, tm, var65, lam65, app65, tt65, pair65, fst65, snd65, left65, right65, split, zero, suc, rec =>
     right65 _ _ _ (t tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 split zero suc rec)

split65 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm65 g (sum65 a b) -> Tm65 g (arr65 a c) -> Tm65 g (arr65 b c) -> Tm65 g c
split65 = \ t, u, v, tm, var65, lam65, app65, tt65, pair65, fst65, snd65, left65, right65, split65, zero, suc, rec =>
     split65 _ _ _ _
          (t tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 split65 zero suc rec)
          (u tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 split65 zero suc rec)
          (v tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 split65 zero suc rec)

zero65 : {g:_} -> Tm65 g Main.nat65
zero65 = \ tm, var65, lam65, app65, tt65, pair65, fst65, snd65, left65, right65, split65, zero65, suc, rec =>
  zero65 _

suc65 : {g:_} -> Tm65 g Main.nat65 -> Tm65 g Main.nat65
suc65 = \ t, tm, var65, lam65, app65, tt65, pair65, fst65, snd65, left65, right65, split65, zero65, suc65, rec =>
   suc65 _ (t tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 split65 zero65 suc65 rec)

rec65 : {g:_}->{a:_} -> Tm65 g Main.nat65 -> Tm65 g (arr65 Main.nat65 (arr65 a a)) -> Tm65 g a -> Tm65 g a
rec65 = \ t, u, v, tm, var65, lam65, app65, tt65, pair65, fst65, snd65, left65, right65, split65, zero65, suc65, rec65 =>
     rec65 _ _
       (t tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 split65 zero65 suc65 rec65)
       (u tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 split65 zero65 suc65 rec65)
       (v tm var65 lam65 app65 tt65 pair65 fst65 snd65 left65 right65 split65 zero65 suc65 rec65)

v065 : {g:_}->{a:_} -> Tm65 (snoc65 g a) a
v065 = var65 vz65

v165 : {g:_}->{a:_}->{b:_} -> Tm65 (snoc65 (snoc65 g a) b) a
v165 = var65 (vs65 vz65)

v265 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm65 (snoc65 (snoc65 (snoc65 g a) b) c) a
v265 = var65 (vs65 (vs65 vz65))

v365 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm65 (snoc65 (snoc65 (snoc65 (snoc65 g a) b) c) d) a
v365 = var65 (vs65 (vs65 (vs65 vz65)))

tbool65 : Ty65
tbool65 = sum65 top65 top65

ttrue65 : {g:_} -> Tm65 g Main.tbool65
ttrue65 = left65 tt65

tfalse65 : {g:_} -> Tm65 g Main.tbool65
tfalse65 = right65 tt65

ifthenelse65 : {g:_}->{a:_} -> Tm65 g (arr65 Main.tbool65 (arr65 a (arr65 a a)))
ifthenelse65 = lam65 (lam65 (lam65 (split65 v265 (lam65 v265) (lam65 v165))))

times465 : {g:_}->{a:_} -> Tm65 g (arr65 (arr65 a a) (arr65 a a))
times465  = lam65 (lam65 (app65 v165 (app65 v165 (app65 v165 (app65 v165 v065)))))

add65 : {g:_} -> Tm65 g (arr65 Main.nat65 (arr65 Main.nat65 Main.nat65))
add65 = lam65 (rec65 v065
       (lam65 (lam65 (lam65 (suc65 (app65 v165 v065)))))
       (lam65 v065))

mul65 : {g:_} -> Tm65 g (arr65 Main.nat65 (arr65 Main.nat65 Main.nat65))
mul65 = lam65 (rec65 v065
       (lam65 (lam65 (lam65 (app65 (app65 add65 (app65 v165 v065)) v065))))
       (lam65 zero65))

fact65 : {g:_} -> Tm65 g (arr65 Main.nat65 Main.nat65)
fact65 = lam65 (rec65 v065 (lam65 (lam65 (app65 (app65 mul65 (suc65 v165)) v065)))
                 (suc65 zero65))

Ty66 : Type
Ty66 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat66 : Ty66
nat66 = \ _, nat66, _, _, _, _, _ => nat66
top66 : Ty66
top66 = \ _, _, top66, _, _, _, _ => top66
bot66 : Ty66
bot66 = \ _, _, _, bot66, _, _, _ => bot66

arr66 : Ty66-> Ty66-> Ty66
arr66 = \ a, b, ty, nat66, top66, bot66, arr66, prod, sum =>
     arr66 (a ty nat66 top66 bot66 arr66 prod sum) (b ty nat66 top66 bot66 arr66 prod sum)

prod66 : Ty66-> Ty66-> Ty66
prod66 = \ a, b, ty, nat66, top66, bot66, arr66, prod66, sum =>
     prod66 (a ty nat66 top66 bot66 arr66 prod66 sum) (b ty nat66 top66 bot66 arr66 prod66 sum)

sum66 : Ty66-> Ty66-> Ty66
sum66 = \ a, b, ty, nat66, top66, bot66, arr66, prod66, sum66 =>
     sum66 (a ty nat66 top66 bot66 arr66 prod66 sum66) (b ty nat66 top66 bot66 arr66 prod66 sum66)

Con66 : Type
Con66 = (Con66 : Type)
 -> (nil  : Con66)
 -> (snoc : Con66 -> Ty66-> Con66)
 -> Con66

nil66 : Con66
nil66 = \ con, nil66, snoc => nil66

snoc66 : Con66 -> Ty66-> Con66
snoc66 = \ g, a, con, nil66, snoc66 => snoc66 (g con nil66 snoc66) a

Var66 : Con66 -> Ty66-> Type
Var66 = \ g, a =>
    (Var66 : Con66 -> Ty66-> Type)
 -> (vz  : (g:_)->(a:_) -> Var66 (snoc66 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var66 g a -> Var66 (snoc66 g b) a)
 -> Var66 g a

vz66 : {g:_}->{a:_} -> Var66 (snoc66 g a) a
vz66 = \ var, vz66, vs => vz66 _ _

vs66 : {g:_}->{b:_}->{a:_} -> Var66 g a -> Var66 (snoc66 g b) a
vs66 = \ x, var, vz66, vs66 => vs66 _ _ _ (x var vz66 vs66)

Tm66 : Con66 -> Ty66-> Type
Tm66 = \ g, a =>
    (Tm66    : Con66 -> Ty66-> Type)
 -> (var   : (g:_)->(a:_)-> Var66 g a -> Tm66 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm66 (snoc66 g a) b -> Tm66 g (arr66 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm66 g (arr66 a b) -> Tm66 g a -> Tm66 g b)
 -> (tt    : (g:_)-> Tm66 g top66)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm66 g a -> Tm66 g b -> Tm66 g (prod66 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm66 g (prod66 a b) -> Tm66 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm66 g (prod66 a b) -> Tm66 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm66 g a -> Tm66 g (sum66 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm66 g b -> Tm66 g (sum66 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm66 g (sum66 a b) -> Tm66 g (arr66 a c) -> Tm66 g (arr66 b c) -> Tm66 g c)
 -> (zero  : (g:_)-> Tm66 g nat66)
 -> (suc   : (g:_)-> Tm66 g nat66 -> Tm66 g nat66)
 -> (rec   : (g:_)->(a:_) -> Tm66 g nat66 -> Tm66 g (arr66 nat66 (arr66 a a)) -> Tm66 g a -> Tm66 g a)
 -> Tm66 g a

var66 : {g:_}->{a:_} -> Var66 g a -> Tm66 g a
var66 = \ x, tm, var66, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var66 _ _ x

lam66 : {g:_}->{a:_}->{b:_}-> Tm66 (snoc66 g a) b -> Tm66 g (arr66 a b)
lam66 = \ t, tm, var66, lam66, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam66 _ _ _ (t tm var66 lam66 app tt pair fst snd left right split zero suc rec)

app66 : {g:_}->{a:_}->{b:_} -> Tm66 g (arr66 a b) -> Tm66 g a -> Tm66 g b
app66 = \ t, u, tm, var66, lam66, app66, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app66 _ _ _ (t tm var66 lam66 app66 tt pair fst snd left right split zero suc rec)
                (u tm var66 lam66 app66 tt pair fst snd left right split zero suc rec)

tt66 : {g:_} -> Tm66 g Main.top66
tt66 = \ tm, var66, lam66, app66, tt66, pair, fst, snd, left, right, split, zero, suc, rec => tt66 _

pair66 : {g:_}->{a:_}->{b:_} -> Tm66 g a -> Tm66 g b -> Tm66 g (prod66 a b)
pair66 = \ t, u, tm, var66, lam66, app66, tt66, pair66, fst, snd, left, right, split, zero, suc, rec =>
     pair66 _ _ _ (t tm var66 lam66 app66 tt66 pair66 fst snd left right split zero suc rec)
                 (u tm var66 lam66 app66 tt66 pair66 fst snd left right split zero suc rec)

fst66 : {g:_}->{a:_}->{b:_}-> Tm66 g (prod66 a b) -> Tm66 g a
fst66 = \ t, tm, var66, lam66, app66, tt66, pair66, fst66, snd, left, right, split, zero, suc, rec =>
     fst66 _ _ _ (t tm var66 lam66 app66 tt66 pair66 fst66 snd left right split zero suc rec)

snd66 : {g:_}->{a:_}->{b:_} -> Tm66 g (prod66 a b) -> Tm66 g b
snd66 = \ t, tm, var66, lam66, app66, tt66, pair66, fst66, snd66, left, right, split, zero, suc, rec =>
     snd66 _ _ _ (t tm var66 lam66 app66 tt66 pair66 fst66 snd66 left right split zero suc rec)

left66 : {g:_}->{a:_}->{b:_} -> Tm66 g a -> Tm66 g (sum66 a b)
left66 = \ t, tm, var66, lam66, app66, tt66, pair66, fst66, snd66, left66, right, split, zero, suc, rec =>
     left66 _ _ _ (t tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right split zero suc rec)

right66 : {g:_}->{a:_}->{b:_} -> Tm66 g b -> Tm66 g (sum66 a b)
right66 = \ t, tm, var66, lam66, app66, tt66, pair66, fst66, snd66, left66, right66, split, zero, suc, rec =>
     right66 _ _ _ (t tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 split zero suc rec)

split66 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm66 g (sum66 a b) -> Tm66 g (arr66 a c) -> Tm66 g (arr66 b c) -> Tm66 g c
split66 = \ t, u, v, tm, var66, lam66, app66, tt66, pair66, fst66, snd66, left66, right66, split66, zero, suc, rec =>
     split66 _ _ _ _
          (t tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 split66 zero suc rec)
          (u tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 split66 zero suc rec)
          (v tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 split66 zero suc rec)

zero66 : {g:_} -> Tm66 g Main.nat66
zero66 = \ tm, var66, lam66, app66, tt66, pair66, fst66, snd66, left66, right66, split66, zero66, suc, rec =>
  zero66 _

suc66 : {g:_} -> Tm66 g Main.nat66 -> Tm66 g Main.nat66
suc66 = \ t, tm, var66, lam66, app66, tt66, pair66, fst66, snd66, left66, right66, split66, zero66, suc66, rec =>
   suc66 _ (t tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 split66 zero66 suc66 rec)

rec66 : {g:_}->{a:_} -> Tm66 g Main.nat66 -> Tm66 g (arr66 Main.nat66 (arr66 a a)) -> Tm66 g a -> Tm66 g a
rec66 = \ t, u, v, tm, var66, lam66, app66, tt66, pair66, fst66, snd66, left66, right66, split66, zero66, suc66, rec66 =>
     rec66 _ _
       (t tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 split66 zero66 suc66 rec66)
       (u tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 split66 zero66 suc66 rec66)
       (v tm var66 lam66 app66 tt66 pair66 fst66 snd66 left66 right66 split66 zero66 suc66 rec66)

v066 : {g:_}->{a:_} -> Tm66 (snoc66 g a) a
v066 = var66 vz66

v166 : {g:_}->{a:_}->{b:_} -> Tm66 (snoc66 (snoc66 g a) b) a
v166 = var66 (vs66 vz66)

v266 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm66 (snoc66 (snoc66 (snoc66 g a) b) c) a
v266 = var66 (vs66 (vs66 vz66))

v366 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm66 (snoc66 (snoc66 (snoc66 (snoc66 g a) b) c) d) a
v366 = var66 (vs66 (vs66 (vs66 vz66)))

tbool66 : Ty66
tbool66 = sum66 top66 top66

ttrue66 : {g:_} -> Tm66 g Main.tbool66
ttrue66 = left66 tt66

tfalse66 : {g:_} -> Tm66 g Main.tbool66
tfalse66 = right66 tt66

ifthenelse66 : {g:_}->{a:_} -> Tm66 g (arr66 Main.tbool66 (arr66 a (arr66 a a)))
ifthenelse66 = lam66 (lam66 (lam66 (split66 v266 (lam66 v266) (lam66 v166))))

times466 : {g:_}->{a:_} -> Tm66 g (arr66 (arr66 a a) (arr66 a a))
times466  = lam66 (lam66 (app66 v166 (app66 v166 (app66 v166 (app66 v166 v066)))))

add66 : {g:_} -> Tm66 g (arr66 Main.nat66 (arr66 Main.nat66 Main.nat66))
add66 = lam66 (rec66 v066
       (lam66 (lam66 (lam66 (suc66 (app66 v166 v066)))))
       (lam66 v066))

mul66 : {g:_} -> Tm66 g (arr66 Main.nat66 (arr66 Main.nat66 Main.nat66))
mul66 = lam66 (rec66 v066
       (lam66 (lam66 (lam66 (app66 (app66 add66 (app66 v166 v066)) v066))))
       (lam66 zero66))

fact66 : {g:_} -> Tm66 g (arr66 Main.nat66 Main.nat66)
fact66 = lam66 (rec66 v066 (lam66 (lam66 (app66 (app66 mul66 (suc66 v166)) v066)))
                 (suc66 zero66))

Ty67 : Type
Ty67 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat67 : Ty67
nat67 = \ _, nat67, _, _, _, _, _ => nat67
top67 : Ty67
top67 = \ _, _, top67, _, _, _, _ => top67
bot67 : Ty67
bot67 = \ _, _, _, bot67, _, _, _ => bot67

arr67 : Ty67-> Ty67-> Ty67
arr67 = \ a, b, ty, nat67, top67, bot67, arr67, prod, sum =>
     arr67 (a ty nat67 top67 bot67 arr67 prod sum) (b ty nat67 top67 bot67 arr67 prod sum)

prod67 : Ty67-> Ty67-> Ty67
prod67 = \ a, b, ty, nat67, top67, bot67, arr67, prod67, sum =>
     prod67 (a ty nat67 top67 bot67 arr67 prod67 sum) (b ty nat67 top67 bot67 arr67 prod67 sum)

sum67 : Ty67-> Ty67-> Ty67
sum67 = \ a, b, ty, nat67, top67, bot67, arr67, prod67, sum67 =>
     sum67 (a ty nat67 top67 bot67 arr67 prod67 sum67) (b ty nat67 top67 bot67 arr67 prod67 sum67)

Con67 : Type
Con67 = (Con67 : Type)
 -> (nil  : Con67)
 -> (snoc : Con67 -> Ty67-> Con67)
 -> Con67

nil67 : Con67
nil67 = \ con, nil67, snoc => nil67

snoc67 : Con67 -> Ty67-> Con67
snoc67 = \ g, a, con, nil67, snoc67 => snoc67 (g con nil67 snoc67) a

Var67 : Con67 -> Ty67-> Type
Var67 = \ g, a =>
    (Var67 : Con67 -> Ty67-> Type)
 -> (vz  : (g:_)->(a:_) -> Var67 (snoc67 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var67 g a -> Var67 (snoc67 g b) a)
 -> Var67 g a

vz67 : {g:_}->{a:_} -> Var67 (snoc67 g a) a
vz67 = \ var, vz67, vs => vz67 _ _

vs67 : {g:_}->{b:_}->{a:_} -> Var67 g a -> Var67 (snoc67 g b) a
vs67 = \ x, var, vz67, vs67 => vs67 _ _ _ (x var vz67 vs67)

Tm67 : Con67 -> Ty67-> Type
Tm67 = \ g, a =>
    (Tm67    : Con67 -> Ty67-> Type)
 -> (var   : (g:_)->(a:_)-> Var67 g a -> Tm67 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm67 (snoc67 g a) b -> Tm67 g (arr67 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm67 g (arr67 a b) -> Tm67 g a -> Tm67 g b)
 -> (tt    : (g:_)-> Tm67 g top67)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm67 g a -> Tm67 g b -> Tm67 g (prod67 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm67 g (prod67 a b) -> Tm67 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm67 g (prod67 a b) -> Tm67 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm67 g a -> Tm67 g (sum67 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm67 g b -> Tm67 g (sum67 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm67 g (sum67 a b) -> Tm67 g (arr67 a c) -> Tm67 g (arr67 b c) -> Tm67 g c)
 -> (zero  : (g:_)-> Tm67 g nat67)
 -> (suc   : (g:_)-> Tm67 g nat67 -> Tm67 g nat67)
 -> (rec   : (g:_)->(a:_) -> Tm67 g nat67 -> Tm67 g (arr67 nat67 (arr67 a a)) -> Tm67 g a -> Tm67 g a)
 -> Tm67 g a

var67 : {g:_}->{a:_} -> Var67 g a -> Tm67 g a
var67 = \ x, tm, var67, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var67 _ _ x

lam67 : {g:_}->{a:_}->{b:_}-> Tm67 (snoc67 g a) b -> Tm67 g (arr67 a b)
lam67 = \ t, tm, var67, lam67, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam67 _ _ _ (t tm var67 lam67 app tt pair fst snd left right split zero suc rec)

app67 : {g:_}->{a:_}->{b:_} -> Tm67 g (arr67 a b) -> Tm67 g a -> Tm67 g b
app67 = \ t, u, tm, var67, lam67, app67, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app67 _ _ _ (t tm var67 lam67 app67 tt pair fst snd left right split zero suc rec)
                (u tm var67 lam67 app67 tt pair fst snd left right split zero suc rec)

tt67 : {g:_} -> Tm67 g Main.top67
tt67 = \ tm, var67, lam67, app67, tt67, pair, fst, snd, left, right, split, zero, suc, rec => tt67 _

pair67 : {g:_}->{a:_}->{b:_} -> Tm67 g a -> Tm67 g b -> Tm67 g (prod67 a b)
pair67 = \ t, u, tm, var67, lam67, app67, tt67, pair67, fst, snd, left, right, split, zero, suc, rec =>
     pair67 _ _ _ (t tm var67 lam67 app67 tt67 pair67 fst snd left right split zero suc rec)
                 (u tm var67 lam67 app67 tt67 pair67 fst snd left right split zero suc rec)

fst67 : {g:_}->{a:_}->{b:_}-> Tm67 g (prod67 a b) -> Tm67 g a
fst67 = \ t, tm, var67, lam67, app67, tt67, pair67, fst67, snd, left, right, split, zero, suc, rec =>
     fst67 _ _ _ (t tm var67 lam67 app67 tt67 pair67 fst67 snd left right split zero suc rec)

snd67 : {g:_}->{a:_}->{b:_} -> Tm67 g (prod67 a b) -> Tm67 g b
snd67 = \ t, tm, var67, lam67, app67, tt67, pair67, fst67, snd67, left, right, split, zero, suc, rec =>
     snd67 _ _ _ (t tm var67 lam67 app67 tt67 pair67 fst67 snd67 left right split zero suc rec)

left67 : {g:_}->{a:_}->{b:_} -> Tm67 g a -> Tm67 g (sum67 a b)
left67 = \ t, tm, var67, lam67, app67, tt67, pair67, fst67, snd67, left67, right, split, zero, suc, rec =>
     left67 _ _ _ (t tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right split zero suc rec)

right67 : {g:_}->{a:_}->{b:_} -> Tm67 g b -> Tm67 g (sum67 a b)
right67 = \ t, tm, var67, lam67, app67, tt67, pair67, fst67, snd67, left67, right67, split, zero, suc, rec =>
     right67 _ _ _ (t tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 split zero suc rec)

split67 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm67 g (sum67 a b) -> Tm67 g (arr67 a c) -> Tm67 g (arr67 b c) -> Tm67 g c
split67 = \ t, u, v, tm, var67, lam67, app67, tt67, pair67, fst67, snd67, left67, right67, split67, zero, suc, rec =>
     split67 _ _ _ _
          (t tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 split67 zero suc rec)
          (u tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 split67 zero suc rec)
          (v tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 split67 zero suc rec)

zero67 : {g:_} -> Tm67 g Main.nat67
zero67 = \ tm, var67, lam67, app67, tt67, pair67, fst67, snd67, left67, right67, split67, zero67, suc, rec =>
  zero67 _

suc67 : {g:_} -> Tm67 g Main.nat67 -> Tm67 g Main.nat67
suc67 = \ t, tm, var67, lam67, app67, tt67, pair67, fst67, snd67, left67, right67, split67, zero67, suc67, rec =>
   suc67 _ (t tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 split67 zero67 suc67 rec)

rec67 : {g:_}->{a:_} -> Tm67 g Main.nat67 -> Tm67 g (arr67 Main.nat67 (arr67 a a)) -> Tm67 g a -> Tm67 g a
rec67 = \ t, u, v, tm, var67, lam67, app67, tt67, pair67, fst67, snd67, left67, right67, split67, zero67, suc67, rec67 =>
     rec67 _ _
       (t tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 split67 zero67 suc67 rec67)
       (u tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 split67 zero67 suc67 rec67)
       (v tm var67 lam67 app67 tt67 pair67 fst67 snd67 left67 right67 split67 zero67 suc67 rec67)

v067 : {g:_}->{a:_} -> Tm67 (snoc67 g a) a
v067 = var67 vz67

v167 : {g:_}->{a:_}->{b:_} -> Tm67 (snoc67 (snoc67 g a) b) a
v167 = var67 (vs67 vz67)

v267 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm67 (snoc67 (snoc67 (snoc67 g a) b) c) a
v267 = var67 (vs67 (vs67 vz67))

v367 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm67 (snoc67 (snoc67 (snoc67 (snoc67 g a) b) c) d) a
v367 = var67 (vs67 (vs67 (vs67 vz67)))

tbool67 : Ty67
tbool67 = sum67 top67 top67

ttrue67 : {g:_} -> Tm67 g Main.tbool67
ttrue67 = left67 tt67

tfalse67 : {g:_} -> Tm67 g Main.tbool67
tfalse67 = right67 tt67

ifthenelse67 : {g:_}->{a:_} -> Tm67 g (arr67 Main.tbool67 (arr67 a (arr67 a a)))
ifthenelse67 = lam67 (lam67 (lam67 (split67 v267 (lam67 v267) (lam67 v167))))

times467 : {g:_}->{a:_} -> Tm67 g (arr67 (arr67 a a) (arr67 a a))
times467  = lam67 (lam67 (app67 v167 (app67 v167 (app67 v167 (app67 v167 v067)))))

add67 : {g:_} -> Tm67 g (arr67 Main.nat67 (arr67 Main.nat67 Main.nat67))
add67 = lam67 (rec67 v067
       (lam67 (lam67 (lam67 (suc67 (app67 v167 v067)))))
       (lam67 v067))

mul67 : {g:_} -> Tm67 g (arr67 Main.nat67 (arr67 Main.nat67 Main.nat67))
mul67 = lam67 (rec67 v067
       (lam67 (lam67 (lam67 (app67 (app67 add67 (app67 v167 v067)) v067))))
       (lam67 zero67))

fact67 : {g:_} -> Tm67 g (arr67 Main.nat67 Main.nat67)
fact67 = lam67 (rec67 v067 (lam67 (lam67 (app67 (app67 mul67 (suc67 v167)) v067)))
                 (suc67 zero67))

Ty68 : Type
Ty68 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat68 : Ty68
nat68 = \ _, nat68, _, _, _, _, _ => nat68
top68 : Ty68
top68 = \ _, _, top68, _, _, _, _ => top68
bot68 : Ty68
bot68 = \ _, _, _, bot68, _, _, _ => bot68

arr68 : Ty68-> Ty68-> Ty68
arr68 = \ a, b, ty, nat68, top68, bot68, arr68, prod, sum =>
     arr68 (a ty nat68 top68 bot68 arr68 prod sum) (b ty nat68 top68 bot68 arr68 prod sum)

prod68 : Ty68-> Ty68-> Ty68
prod68 = \ a, b, ty, nat68, top68, bot68, arr68, prod68, sum =>
     prod68 (a ty nat68 top68 bot68 arr68 prod68 sum) (b ty nat68 top68 bot68 arr68 prod68 sum)

sum68 : Ty68-> Ty68-> Ty68
sum68 = \ a, b, ty, nat68, top68, bot68, arr68, prod68, sum68 =>
     sum68 (a ty nat68 top68 bot68 arr68 prod68 sum68) (b ty nat68 top68 bot68 arr68 prod68 sum68)

Con68 : Type
Con68 = (Con68 : Type)
 -> (nil  : Con68)
 -> (snoc : Con68 -> Ty68-> Con68)
 -> Con68

nil68 : Con68
nil68 = \ con, nil68, snoc => nil68

snoc68 : Con68 -> Ty68-> Con68
snoc68 = \ g, a, con, nil68, snoc68 => snoc68 (g con nil68 snoc68) a

Var68 : Con68 -> Ty68-> Type
Var68 = \ g, a =>
    (Var68 : Con68 -> Ty68-> Type)
 -> (vz  : (g:_)->(a:_) -> Var68 (snoc68 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var68 g a -> Var68 (snoc68 g b) a)
 -> Var68 g a

vz68 : {g:_}->{a:_} -> Var68 (snoc68 g a) a
vz68 = \ var, vz68, vs => vz68 _ _

vs68 : {g:_}->{b:_}->{a:_} -> Var68 g a -> Var68 (snoc68 g b) a
vs68 = \ x, var, vz68, vs68 => vs68 _ _ _ (x var vz68 vs68)

Tm68 : Con68 -> Ty68-> Type
Tm68 = \ g, a =>
    (Tm68    : Con68 -> Ty68-> Type)
 -> (var   : (g:_)->(a:_)-> Var68 g a -> Tm68 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm68 (snoc68 g a) b -> Tm68 g (arr68 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm68 g (arr68 a b) -> Tm68 g a -> Tm68 g b)
 -> (tt    : (g:_)-> Tm68 g top68)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm68 g a -> Tm68 g b -> Tm68 g (prod68 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm68 g (prod68 a b) -> Tm68 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm68 g (prod68 a b) -> Tm68 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm68 g a -> Tm68 g (sum68 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm68 g b -> Tm68 g (sum68 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm68 g (sum68 a b) -> Tm68 g (arr68 a c) -> Tm68 g (arr68 b c) -> Tm68 g c)
 -> (zero  : (g:_)-> Tm68 g nat68)
 -> (suc   : (g:_)-> Tm68 g nat68 -> Tm68 g nat68)
 -> (rec   : (g:_)->(a:_) -> Tm68 g nat68 -> Tm68 g (arr68 nat68 (arr68 a a)) -> Tm68 g a -> Tm68 g a)
 -> Tm68 g a

var68 : {g:_}->{a:_} -> Var68 g a -> Tm68 g a
var68 = \ x, tm, var68, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var68 _ _ x

lam68 : {g:_}->{a:_}->{b:_}-> Tm68 (snoc68 g a) b -> Tm68 g (arr68 a b)
lam68 = \ t, tm, var68, lam68, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam68 _ _ _ (t tm var68 lam68 app tt pair fst snd left right split zero suc rec)

app68 : {g:_}->{a:_}->{b:_} -> Tm68 g (arr68 a b) -> Tm68 g a -> Tm68 g b
app68 = \ t, u, tm, var68, lam68, app68, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app68 _ _ _ (t tm var68 lam68 app68 tt pair fst snd left right split zero suc rec)
                (u tm var68 lam68 app68 tt pair fst snd left right split zero suc rec)

tt68 : {g:_} -> Tm68 g Main.top68
tt68 = \ tm, var68, lam68, app68, tt68, pair, fst, snd, left, right, split, zero, suc, rec => tt68 _

pair68 : {g:_}->{a:_}->{b:_} -> Tm68 g a -> Tm68 g b -> Tm68 g (prod68 a b)
pair68 = \ t, u, tm, var68, lam68, app68, tt68, pair68, fst, snd, left, right, split, zero, suc, rec =>
     pair68 _ _ _ (t tm var68 lam68 app68 tt68 pair68 fst snd left right split zero suc rec)
                 (u tm var68 lam68 app68 tt68 pair68 fst snd left right split zero suc rec)

fst68 : {g:_}->{a:_}->{b:_}-> Tm68 g (prod68 a b) -> Tm68 g a
fst68 = \ t, tm, var68, lam68, app68, tt68, pair68, fst68, snd, left, right, split, zero, suc, rec =>
     fst68 _ _ _ (t tm var68 lam68 app68 tt68 pair68 fst68 snd left right split zero suc rec)

snd68 : {g:_}->{a:_}->{b:_} -> Tm68 g (prod68 a b) -> Tm68 g b
snd68 = \ t, tm, var68, lam68, app68, tt68, pair68, fst68, snd68, left, right, split, zero, suc, rec =>
     snd68 _ _ _ (t tm var68 lam68 app68 tt68 pair68 fst68 snd68 left right split zero suc rec)

left68 : {g:_}->{a:_}->{b:_} -> Tm68 g a -> Tm68 g (sum68 a b)
left68 = \ t, tm, var68, lam68, app68, tt68, pair68, fst68, snd68, left68, right, split, zero, suc, rec =>
     left68 _ _ _ (t tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right split zero suc rec)

right68 : {g:_}->{a:_}->{b:_} -> Tm68 g b -> Tm68 g (sum68 a b)
right68 = \ t, tm, var68, lam68, app68, tt68, pair68, fst68, snd68, left68, right68, split, zero, suc, rec =>
     right68 _ _ _ (t tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 split zero suc rec)

split68 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm68 g (sum68 a b) -> Tm68 g (arr68 a c) -> Tm68 g (arr68 b c) -> Tm68 g c
split68 = \ t, u, v, tm, var68, lam68, app68, tt68, pair68, fst68, snd68, left68, right68, split68, zero, suc, rec =>
     split68 _ _ _ _
          (t tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 split68 zero suc rec)
          (u tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 split68 zero suc rec)
          (v tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 split68 zero suc rec)

zero68 : {g:_} -> Tm68 g Main.nat68
zero68 = \ tm, var68, lam68, app68, tt68, pair68, fst68, snd68, left68, right68, split68, zero68, suc, rec =>
  zero68 _

suc68 : {g:_} -> Tm68 g Main.nat68 -> Tm68 g Main.nat68
suc68 = \ t, tm, var68, lam68, app68, tt68, pair68, fst68, snd68, left68, right68, split68, zero68, suc68, rec =>
   suc68 _ (t tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 split68 zero68 suc68 rec)

rec68 : {g:_}->{a:_} -> Tm68 g Main.nat68 -> Tm68 g (arr68 Main.nat68 (arr68 a a)) -> Tm68 g a -> Tm68 g a
rec68 = \ t, u, v, tm, var68, lam68, app68, tt68, pair68, fst68, snd68, left68, right68, split68, zero68, suc68, rec68 =>
     rec68 _ _
       (t tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 split68 zero68 suc68 rec68)
       (u tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 split68 zero68 suc68 rec68)
       (v tm var68 lam68 app68 tt68 pair68 fst68 snd68 left68 right68 split68 zero68 suc68 rec68)

v068 : {g:_}->{a:_} -> Tm68 (snoc68 g a) a
v068 = var68 vz68

v168 : {g:_}->{a:_}->{b:_} -> Tm68 (snoc68 (snoc68 g a) b) a
v168 = var68 (vs68 vz68)

v268 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm68 (snoc68 (snoc68 (snoc68 g a) b) c) a
v268 = var68 (vs68 (vs68 vz68))

v368 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm68 (snoc68 (snoc68 (snoc68 (snoc68 g a) b) c) d) a
v368 = var68 (vs68 (vs68 (vs68 vz68)))

tbool68 : Ty68
tbool68 = sum68 top68 top68

ttrue68 : {g:_} -> Tm68 g Main.tbool68
ttrue68 = left68 tt68

tfalse68 : {g:_} -> Tm68 g Main.tbool68
tfalse68 = right68 tt68

ifthenelse68 : {g:_}->{a:_} -> Tm68 g (arr68 Main.tbool68 (arr68 a (arr68 a a)))
ifthenelse68 = lam68 (lam68 (lam68 (split68 v268 (lam68 v268) (lam68 v168))))

times468 : {g:_}->{a:_} -> Tm68 g (arr68 (arr68 a a) (arr68 a a))
times468  = lam68 (lam68 (app68 v168 (app68 v168 (app68 v168 (app68 v168 v068)))))

add68 : {g:_} -> Tm68 g (arr68 Main.nat68 (arr68 Main.nat68 Main.nat68))
add68 = lam68 (rec68 v068
       (lam68 (lam68 (lam68 (suc68 (app68 v168 v068)))))
       (lam68 v068))

mul68 : {g:_} -> Tm68 g (arr68 Main.nat68 (arr68 Main.nat68 Main.nat68))
mul68 = lam68 (rec68 v068
       (lam68 (lam68 (lam68 (app68 (app68 add68 (app68 v168 v068)) v068))))
       (lam68 zero68))

fact68 : {g:_} -> Tm68 g (arr68 Main.nat68 Main.nat68)
fact68 = lam68 (rec68 v068 (lam68 (lam68 (app68 (app68 mul68 (suc68 v168)) v068)))
                 (suc68 zero68))

Ty69 : Type
Ty69 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat69 : Ty69
nat69 = \ _, nat69, _, _, _, _, _ => nat69
top69 : Ty69
top69 = \ _, _, top69, _, _, _, _ => top69
bot69 : Ty69
bot69 = \ _, _, _, bot69, _, _, _ => bot69

arr69 : Ty69-> Ty69-> Ty69
arr69 = \ a, b, ty, nat69, top69, bot69, arr69, prod, sum =>
     arr69 (a ty nat69 top69 bot69 arr69 prod sum) (b ty nat69 top69 bot69 arr69 prod sum)

prod69 : Ty69-> Ty69-> Ty69
prod69 = \ a, b, ty, nat69, top69, bot69, arr69, prod69, sum =>
     prod69 (a ty nat69 top69 bot69 arr69 prod69 sum) (b ty nat69 top69 bot69 arr69 prod69 sum)

sum69 : Ty69-> Ty69-> Ty69
sum69 = \ a, b, ty, nat69, top69, bot69, arr69, prod69, sum69 =>
     sum69 (a ty nat69 top69 bot69 arr69 prod69 sum69) (b ty nat69 top69 bot69 arr69 prod69 sum69)

Con69 : Type
Con69 = (Con69 : Type)
 -> (nil  : Con69)
 -> (snoc : Con69 -> Ty69-> Con69)
 -> Con69

nil69 : Con69
nil69 = \ con, nil69, snoc => nil69

snoc69 : Con69 -> Ty69-> Con69
snoc69 = \ g, a, con, nil69, snoc69 => snoc69 (g con nil69 snoc69) a

Var69 : Con69 -> Ty69-> Type
Var69 = \ g, a =>
    (Var69 : Con69 -> Ty69-> Type)
 -> (vz  : (g:_)->(a:_) -> Var69 (snoc69 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var69 g a -> Var69 (snoc69 g b) a)
 -> Var69 g a

vz69 : {g:_}->{a:_} -> Var69 (snoc69 g a) a
vz69 = \ var, vz69, vs => vz69 _ _

vs69 : {g:_}->{b:_}->{a:_} -> Var69 g a -> Var69 (snoc69 g b) a
vs69 = \ x, var, vz69, vs69 => vs69 _ _ _ (x var vz69 vs69)

Tm69 : Con69 -> Ty69-> Type
Tm69 = \ g, a =>
    (Tm69    : Con69 -> Ty69-> Type)
 -> (var   : (g:_)->(a:_)-> Var69 g a -> Tm69 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm69 (snoc69 g a) b -> Tm69 g (arr69 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm69 g (arr69 a b) -> Tm69 g a -> Tm69 g b)
 -> (tt    : (g:_)-> Tm69 g top69)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm69 g a -> Tm69 g b -> Tm69 g (prod69 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm69 g (prod69 a b) -> Tm69 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm69 g (prod69 a b) -> Tm69 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm69 g a -> Tm69 g (sum69 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm69 g b -> Tm69 g (sum69 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm69 g (sum69 a b) -> Tm69 g (arr69 a c) -> Tm69 g (arr69 b c) -> Tm69 g c)
 -> (zero  : (g:_)-> Tm69 g nat69)
 -> (suc   : (g:_)-> Tm69 g nat69 -> Tm69 g nat69)
 -> (rec   : (g:_)->(a:_) -> Tm69 g nat69 -> Tm69 g (arr69 nat69 (arr69 a a)) -> Tm69 g a -> Tm69 g a)
 -> Tm69 g a

var69 : {g:_}->{a:_} -> Var69 g a -> Tm69 g a
var69 = \ x, tm, var69, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var69 _ _ x

lam69 : {g:_}->{a:_}->{b:_}-> Tm69 (snoc69 g a) b -> Tm69 g (arr69 a b)
lam69 = \ t, tm, var69, lam69, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam69 _ _ _ (t tm var69 lam69 app tt pair fst snd left right split zero suc rec)

app69 : {g:_}->{a:_}->{b:_} -> Tm69 g (arr69 a b) -> Tm69 g a -> Tm69 g b
app69 = \ t, u, tm, var69, lam69, app69, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app69 _ _ _ (t tm var69 lam69 app69 tt pair fst snd left right split zero suc rec)
                (u tm var69 lam69 app69 tt pair fst snd left right split zero suc rec)

tt69 : {g:_} -> Tm69 g Main.top69
tt69 = \ tm, var69, lam69, app69, tt69, pair, fst, snd, left, right, split, zero, suc, rec => tt69 _

pair69 : {g:_}->{a:_}->{b:_} -> Tm69 g a -> Tm69 g b -> Tm69 g (prod69 a b)
pair69 = \ t, u, tm, var69, lam69, app69, tt69, pair69, fst, snd, left, right, split, zero, suc, rec =>
     pair69 _ _ _ (t tm var69 lam69 app69 tt69 pair69 fst snd left right split zero suc rec)
                 (u tm var69 lam69 app69 tt69 pair69 fst snd left right split zero suc rec)

fst69 : {g:_}->{a:_}->{b:_}-> Tm69 g (prod69 a b) -> Tm69 g a
fst69 = \ t, tm, var69, lam69, app69, tt69, pair69, fst69, snd, left, right, split, zero, suc, rec =>
     fst69 _ _ _ (t tm var69 lam69 app69 tt69 pair69 fst69 snd left right split zero suc rec)

snd69 : {g:_}->{a:_}->{b:_} -> Tm69 g (prod69 a b) -> Tm69 g b
snd69 = \ t, tm, var69, lam69, app69, tt69, pair69, fst69, snd69, left, right, split, zero, suc, rec =>
     snd69 _ _ _ (t tm var69 lam69 app69 tt69 pair69 fst69 snd69 left right split zero suc rec)

left69 : {g:_}->{a:_}->{b:_} -> Tm69 g a -> Tm69 g (sum69 a b)
left69 = \ t, tm, var69, lam69, app69, tt69, pair69, fst69, snd69, left69, right, split, zero, suc, rec =>
     left69 _ _ _ (t tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right split zero suc rec)

right69 : {g:_}->{a:_}->{b:_} -> Tm69 g b -> Tm69 g (sum69 a b)
right69 = \ t, tm, var69, lam69, app69, tt69, pair69, fst69, snd69, left69, right69, split, zero, suc, rec =>
     right69 _ _ _ (t tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 split zero suc rec)

split69 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm69 g (sum69 a b) -> Tm69 g (arr69 a c) -> Tm69 g (arr69 b c) -> Tm69 g c
split69 = \ t, u, v, tm, var69, lam69, app69, tt69, pair69, fst69, snd69, left69, right69, split69, zero, suc, rec =>
     split69 _ _ _ _
          (t tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 split69 zero suc rec)
          (u tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 split69 zero suc rec)
          (v tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 split69 zero suc rec)

zero69 : {g:_} -> Tm69 g Main.nat69
zero69 = \ tm, var69, lam69, app69, tt69, pair69, fst69, snd69, left69, right69, split69, zero69, suc, rec =>
  zero69 _

suc69 : {g:_} -> Tm69 g Main.nat69 -> Tm69 g Main.nat69
suc69 = \ t, tm, var69, lam69, app69, tt69, pair69, fst69, snd69, left69, right69, split69, zero69, suc69, rec =>
   suc69 _ (t tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 split69 zero69 suc69 rec)

rec69 : {g:_}->{a:_} -> Tm69 g Main.nat69 -> Tm69 g (arr69 Main.nat69 (arr69 a a)) -> Tm69 g a -> Tm69 g a
rec69 = \ t, u, v, tm, var69, lam69, app69, tt69, pair69, fst69, snd69, left69, right69, split69, zero69, suc69, rec69 =>
     rec69 _ _
       (t tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 split69 zero69 suc69 rec69)
       (u tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 split69 zero69 suc69 rec69)
       (v tm var69 lam69 app69 tt69 pair69 fst69 snd69 left69 right69 split69 zero69 suc69 rec69)

v069 : {g:_}->{a:_} -> Tm69 (snoc69 g a) a
v069 = var69 vz69

v169 : {g:_}->{a:_}->{b:_} -> Tm69 (snoc69 (snoc69 g a) b) a
v169 = var69 (vs69 vz69)

v269 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm69 (snoc69 (snoc69 (snoc69 g a) b) c) a
v269 = var69 (vs69 (vs69 vz69))

v369 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm69 (snoc69 (snoc69 (snoc69 (snoc69 g a) b) c) d) a
v369 = var69 (vs69 (vs69 (vs69 vz69)))

tbool69 : Ty69
tbool69 = sum69 top69 top69

ttrue69 : {g:_} -> Tm69 g Main.tbool69
ttrue69 = left69 tt69

tfalse69 : {g:_} -> Tm69 g Main.tbool69
tfalse69 = right69 tt69

ifthenelse69 : {g:_}->{a:_} -> Tm69 g (arr69 Main.tbool69 (arr69 a (arr69 a a)))
ifthenelse69 = lam69 (lam69 (lam69 (split69 v269 (lam69 v269) (lam69 v169))))

times469 : {g:_}->{a:_} -> Tm69 g (arr69 (arr69 a a) (arr69 a a))
times469  = lam69 (lam69 (app69 v169 (app69 v169 (app69 v169 (app69 v169 v069)))))

add69 : {g:_} -> Tm69 g (arr69 Main.nat69 (arr69 Main.nat69 Main.nat69))
add69 = lam69 (rec69 v069
       (lam69 (lam69 (lam69 (suc69 (app69 v169 v069)))))
       (lam69 v069))

mul69 : {g:_} -> Tm69 g (arr69 Main.nat69 (arr69 Main.nat69 Main.nat69))
mul69 = lam69 (rec69 v069
       (lam69 (lam69 (lam69 (app69 (app69 add69 (app69 v169 v069)) v069))))
       (lam69 zero69))

fact69 : {g:_} -> Tm69 g (arr69 Main.nat69 Main.nat69)
fact69 = lam69 (rec69 v069 (lam69 (lam69 (app69 (app69 mul69 (suc69 v169)) v069)))
                 (suc69 zero69))

Ty70 : Type
Ty70 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat70 : Ty70
nat70 = \ _, nat70, _, _, _, _, _ => nat70
top70 : Ty70
top70 = \ _, _, top70, _, _, _, _ => top70
bot70 : Ty70
bot70 = \ _, _, _, bot70, _, _, _ => bot70

arr70 : Ty70-> Ty70-> Ty70
arr70 = \ a, b, ty, nat70, top70, bot70, arr70, prod, sum =>
     arr70 (a ty nat70 top70 bot70 arr70 prod sum) (b ty nat70 top70 bot70 arr70 prod sum)

prod70 : Ty70-> Ty70-> Ty70
prod70 = \ a, b, ty, nat70, top70, bot70, arr70, prod70, sum =>
     prod70 (a ty nat70 top70 bot70 arr70 prod70 sum) (b ty nat70 top70 bot70 arr70 prod70 sum)

sum70 : Ty70-> Ty70-> Ty70
sum70 = \ a, b, ty, nat70, top70, bot70, arr70, prod70, sum70 =>
     sum70 (a ty nat70 top70 bot70 arr70 prod70 sum70) (b ty nat70 top70 bot70 arr70 prod70 sum70)

Con70 : Type
Con70 = (Con70 : Type)
 -> (nil  : Con70)
 -> (snoc : Con70 -> Ty70-> Con70)
 -> Con70

nil70 : Con70
nil70 = \ con, nil70, snoc => nil70

snoc70 : Con70 -> Ty70-> Con70
snoc70 = \ g, a, con, nil70, snoc70 => snoc70 (g con nil70 snoc70) a

Var70 : Con70 -> Ty70-> Type
Var70 = \ g, a =>
    (Var70 : Con70 -> Ty70-> Type)
 -> (vz  : (g:_)->(a:_) -> Var70 (snoc70 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var70 g a -> Var70 (snoc70 g b) a)
 -> Var70 g a

vz70 : {g:_}->{a:_} -> Var70 (snoc70 g a) a
vz70 = \ var, vz70, vs => vz70 _ _

vs70 : {g:_}->{b:_}->{a:_} -> Var70 g a -> Var70 (snoc70 g b) a
vs70 = \ x, var, vz70, vs70 => vs70 _ _ _ (x var vz70 vs70)

Tm70 : Con70 -> Ty70-> Type
Tm70 = \ g, a =>
    (Tm70    : Con70 -> Ty70-> Type)
 -> (var   : (g:_)->(a:_)-> Var70 g a -> Tm70 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm70 (snoc70 g a) b -> Tm70 g (arr70 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm70 g (arr70 a b) -> Tm70 g a -> Tm70 g b)
 -> (tt    : (g:_)-> Tm70 g top70)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm70 g a -> Tm70 g b -> Tm70 g (prod70 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm70 g (prod70 a b) -> Tm70 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm70 g (prod70 a b) -> Tm70 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm70 g a -> Tm70 g (sum70 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm70 g b -> Tm70 g (sum70 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm70 g (sum70 a b) -> Tm70 g (arr70 a c) -> Tm70 g (arr70 b c) -> Tm70 g c)
 -> (zero  : (g:_)-> Tm70 g nat70)
 -> (suc   : (g:_)-> Tm70 g nat70 -> Tm70 g nat70)
 -> (rec   : (g:_)->(a:_) -> Tm70 g nat70 -> Tm70 g (arr70 nat70 (arr70 a a)) -> Tm70 g a -> Tm70 g a)
 -> Tm70 g a

var70 : {g:_}->{a:_} -> Var70 g a -> Tm70 g a
var70 = \ x, tm, var70, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var70 _ _ x

lam70 : {g:_}->{a:_}->{b:_}-> Tm70 (snoc70 g a) b -> Tm70 g (arr70 a b)
lam70 = \ t, tm, var70, lam70, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam70 _ _ _ (t tm var70 lam70 app tt pair fst snd left right split zero suc rec)

app70 : {g:_}->{a:_}->{b:_} -> Tm70 g (arr70 a b) -> Tm70 g a -> Tm70 g b
app70 = \ t, u, tm, var70, lam70, app70, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app70 _ _ _ (t tm var70 lam70 app70 tt pair fst snd left right split zero suc rec)
                (u tm var70 lam70 app70 tt pair fst snd left right split zero suc rec)

tt70 : {g:_} -> Tm70 g Main.top70
tt70 = \ tm, var70, lam70, app70, tt70, pair, fst, snd, left, right, split, zero, suc, rec => tt70 _

pair70 : {g:_}->{a:_}->{b:_} -> Tm70 g a -> Tm70 g b -> Tm70 g (prod70 a b)
pair70 = \ t, u, tm, var70, lam70, app70, tt70, pair70, fst, snd, left, right, split, zero, suc, rec =>
     pair70 _ _ _ (t tm var70 lam70 app70 tt70 pair70 fst snd left right split zero suc rec)
                 (u tm var70 lam70 app70 tt70 pair70 fst snd left right split zero suc rec)

fst70 : {g:_}->{a:_}->{b:_}-> Tm70 g (prod70 a b) -> Tm70 g a
fst70 = \ t, tm, var70, lam70, app70, tt70, pair70, fst70, snd, left, right, split, zero, suc, rec =>
     fst70 _ _ _ (t tm var70 lam70 app70 tt70 pair70 fst70 snd left right split zero suc rec)

snd70 : {g:_}->{a:_}->{b:_} -> Tm70 g (prod70 a b) -> Tm70 g b
snd70 = \ t, tm, var70, lam70, app70, tt70, pair70, fst70, snd70, left, right, split, zero, suc, rec =>
     snd70 _ _ _ (t tm var70 lam70 app70 tt70 pair70 fst70 snd70 left right split zero suc rec)

left70 : {g:_}->{a:_}->{b:_} -> Tm70 g a -> Tm70 g (sum70 a b)
left70 = \ t, tm, var70, lam70, app70, tt70, pair70, fst70, snd70, left70, right, split, zero, suc, rec =>
     left70 _ _ _ (t tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right split zero suc rec)

right70 : {g:_}->{a:_}->{b:_} -> Tm70 g b -> Tm70 g (sum70 a b)
right70 = \ t, tm, var70, lam70, app70, tt70, pair70, fst70, snd70, left70, right70, split, zero, suc, rec =>
     right70 _ _ _ (t tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 split zero suc rec)

split70 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm70 g (sum70 a b) -> Tm70 g (arr70 a c) -> Tm70 g (arr70 b c) -> Tm70 g c
split70 = \ t, u, v, tm, var70, lam70, app70, tt70, pair70, fst70, snd70, left70, right70, split70, zero, suc, rec =>
     split70 _ _ _ _
          (t tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 split70 zero suc rec)
          (u tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 split70 zero suc rec)
          (v tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 split70 zero suc rec)

zero70 : {g:_} -> Tm70 g Main.nat70
zero70 = \ tm, var70, lam70, app70, tt70, pair70, fst70, snd70, left70, right70, split70, zero70, suc, rec =>
  zero70 _

suc70 : {g:_} -> Tm70 g Main.nat70 -> Tm70 g Main.nat70
suc70 = \ t, tm, var70, lam70, app70, tt70, pair70, fst70, snd70, left70, right70, split70, zero70, suc70, rec =>
   suc70 _ (t tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 split70 zero70 suc70 rec)

rec70 : {g:_}->{a:_} -> Tm70 g Main.nat70 -> Tm70 g (arr70 Main.nat70 (arr70 a a)) -> Tm70 g a -> Tm70 g a
rec70 = \ t, u, v, tm, var70, lam70, app70, tt70, pair70, fst70, snd70, left70, right70, split70, zero70, suc70, rec70 =>
     rec70 _ _
       (t tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 split70 zero70 suc70 rec70)
       (u tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 split70 zero70 suc70 rec70)
       (v tm var70 lam70 app70 tt70 pair70 fst70 snd70 left70 right70 split70 zero70 suc70 rec70)

v070 : {g:_}->{a:_} -> Tm70 (snoc70 g a) a
v070 = var70 vz70

v170 : {g:_}->{a:_}->{b:_} -> Tm70 (snoc70 (snoc70 g a) b) a
v170 = var70 (vs70 vz70)

v270 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm70 (snoc70 (snoc70 (snoc70 g a) b) c) a
v270 = var70 (vs70 (vs70 vz70))

v370 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm70 (snoc70 (snoc70 (snoc70 (snoc70 g a) b) c) d) a
v370 = var70 (vs70 (vs70 (vs70 vz70)))

tbool70 : Ty70
tbool70 = sum70 top70 top70

ttrue70 : {g:_} -> Tm70 g Main.tbool70
ttrue70 = left70 tt70

tfalse70 : {g:_} -> Tm70 g Main.tbool70
tfalse70 = right70 tt70

ifthenelse70 : {g:_}->{a:_} -> Tm70 g (arr70 Main.tbool70 (arr70 a (arr70 a a)))
ifthenelse70 = lam70 (lam70 (lam70 (split70 v270 (lam70 v270) (lam70 v170))))

times470 : {g:_}->{a:_} -> Tm70 g (arr70 (arr70 a a) (arr70 a a))
times470  = lam70 (lam70 (app70 v170 (app70 v170 (app70 v170 (app70 v170 v070)))))

add70 : {g:_} -> Tm70 g (arr70 Main.nat70 (arr70 Main.nat70 Main.nat70))
add70 = lam70 (rec70 v070
       (lam70 (lam70 (lam70 (suc70 (app70 v170 v070)))))
       (lam70 v070))

mul70 : {g:_} -> Tm70 g (arr70 Main.nat70 (arr70 Main.nat70 Main.nat70))
mul70 = lam70 (rec70 v070
       (lam70 (lam70 (lam70 (app70 (app70 add70 (app70 v170 v070)) v070))))
       (lam70 zero70))

fact70 : {g:_} -> Tm70 g (arr70 Main.nat70 Main.nat70)
fact70 = lam70 (rec70 v070 (lam70 (lam70 (app70 (app70 mul70 (suc70 v170)) v070)))
                 (suc70 zero70))

Ty71 : Type
Ty71 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat71 : Ty71
nat71 = \ _, nat71, _, _, _, _, _ => nat71
top71 : Ty71
top71 = \ _, _, top71, _, _, _, _ => top71
bot71 : Ty71
bot71 = \ _, _, _, bot71, _, _, _ => bot71

arr71 : Ty71-> Ty71-> Ty71
arr71 = \ a, b, ty, nat71, top71, bot71, arr71, prod, sum =>
     arr71 (a ty nat71 top71 bot71 arr71 prod sum) (b ty nat71 top71 bot71 arr71 prod sum)

prod71 : Ty71-> Ty71-> Ty71
prod71 = \ a, b, ty, nat71, top71, bot71, arr71, prod71, sum =>
     prod71 (a ty nat71 top71 bot71 arr71 prod71 sum) (b ty nat71 top71 bot71 arr71 prod71 sum)

sum71 : Ty71-> Ty71-> Ty71
sum71 = \ a, b, ty, nat71, top71, bot71, arr71, prod71, sum71 =>
     sum71 (a ty nat71 top71 bot71 arr71 prod71 sum71) (b ty nat71 top71 bot71 arr71 prod71 sum71)

Con71 : Type
Con71 = (Con71 : Type)
 -> (nil  : Con71)
 -> (snoc : Con71 -> Ty71-> Con71)
 -> Con71

nil71 : Con71
nil71 = \ con, nil71, snoc => nil71

snoc71 : Con71 -> Ty71-> Con71
snoc71 = \ g, a, con, nil71, snoc71 => snoc71 (g con nil71 snoc71) a

Var71 : Con71 -> Ty71-> Type
Var71 = \ g, a =>
    (Var71 : Con71 -> Ty71-> Type)
 -> (vz  : (g:_)->(a:_) -> Var71 (snoc71 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var71 g a -> Var71 (snoc71 g b) a)
 -> Var71 g a

vz71 : {g:_}->{a:_} -> Var71 (snoc71 g a) a
vz71 = \ var, vz71, vs => vz71 _ _

vs71 : {g:_}->{b:_}->{a:_} -> Var71 g a -> Var71 (snoc71 g b) a
vs71 = \ x, var, vz71, vs71 => vs71 _ _ _ (x var vz71 vs71)

Tm71 : Con71 -> Ty71-> Type
Tm71 = \ g, a =>
    (Tm71    : Con71 -> Ty71-> Type)
 -> (var   : (g:_)->(a:_)-> Var71 g a -> Tm71 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm71 (snoc71 g a) b -> Tm71 g (arr71 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm71 g (arr71 a b) -> Tm71 g a -> Tm71 g b)
 -> (tt    : (g:_)-> Tm71 g top71)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm71 g a -> Tm71 g b -> Tm71 g (prod71 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm71 g (prod71 a b) -> Tm71 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm71 g (prod71 a b) -> Tm71 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm71 g a -> Tm71 g (sum71 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm71 g b -> Tm71 g (sum71 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm71 g (sum71 a b) -> Tm71 g (arr71 a c) -> Tm71 g (arr71 b c) -> Tm71 g c)
 -> (zero  : (g:_)-> Tm71 g nat71)
 -> (suc   : (g:_)-> Tm71 g nat71 -> Tm71 g nat71)
 -> (rec   : (g:_)->(a:_) -> Tm71 g nat71 -> Tm71 g (arr71 nat71 (arr71 a a)) -> Tm71 g a -> Tm71 g a)
 -> Tm71 g a

var71 : {g:_}->{a:_} -> Var71 g a -> Tm71 g a
var71 = \ x, tm, var71, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var71 _ _ x

lam71 : {g:_}->{a:_}->{b:_}-> Tm71 (snoc71 g a) b -> Tm71 g (arr71 a b)
lam71 = \ t, tm, var71, lam71, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam71 _ _ _ (t tm var71 lam71 app tt pair fst snd left right split zero suc rec)

app71 : {g:_}->{a:_}->{b:_} -> Tm71 g (arr71 a b) -> Tm71 g a -> Tm71 g b
app71 = \ t, u, tm, var71, lam71, app71, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app71 _ _ _ (t tm var71 lam71 app71 tt pair fst snd left right split zero suc rec)
                (u tm var71 lam71 app71 tt pair fst snd left right split zero suc rec)

tt71 : {g:_} -> Tm71 g Main.top71
tt71 = \ tm, var71, lam71, app71, tt71, pair, fst, snd, left, right, split, zero, suc, rec => tt71 _

pair71 : {g:_}->{a:_}->{b:_} -> Tm71 g a -> Tm71 g b -> Tm71 g (prod71 a b)
pair71 = \ t, u, tm, var71, lam71, app71, tt71, pair71, fst, snd, left, right, split, zero, suc, rec =>
     pair71 _ _ _ (t tm var71 lam71 app71 tt71 pair71 fst snd left right split zero suc rec)
                 (u tm var71 lam71 app71 tt71 pair71 fst snd left right split zero suc rec)

fst71 : {g:_}->{a:_}->{b:_}-> Tm71 g (prod71 a b) -> Tm71 g a
fst71 = \ t, tm, var71, lam71, app71, tt71, pair71, fst71, snd, left, right, split, zero, suc, rec =>
     fst71 _ _ _ (t tm var71 lam71 app71 tt71 pair71 fst71 snd left right split zero suc rec)

snd71 : {g:_}->{a:_}->{b:_} -> Tm71 g (prod71 a b) -> Tm71 g b
snd71 = \ t, tm, var71, lam71, app71, tt71, pair71, fst71, snd71, left, right, split, zero, suc, rec =>
     snd71 _ _ _ (t tm var71 lam71 app71 tt71 pair71 fst71 snd71 left right split zero suc rec)

left71 : {g:_}->{a:_}->{b:_} -> Tm71 g a -> Tm71 g (sum71 a b)
left71 = \ t, tm, var71, lam71, app71, tt71, pair71, fst71, snd71, left71, right, split, zero, suc, rec =>
     left71 _ _ _ (t tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right split zero suc rec)

right71 : {g:_}->{a:_}->{b:_} -> Tm71 g b -> Tm71 g (sum71 a b)
right71 = \ t, tm, var71, lam71, app71, tt71, pair71, fst71, snd71, left71, right71, split, zero, suc, rec =>
     right71 _ _ _ (t tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 split zero suc rec)

split71 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm71 g (sum71 a b) -> Tm71 g (arr71 a c) -> Tm71 g (arr71 b c) -> Tm71 g c
split71 = \ t, u, v, tm, var71, lam71, app71, tt71, pair71, fst71, snd71, left71, right71, split71, zero, suc, rec =>
     split71 _ _ _ _
          (t tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 split71 zero suc rec)
          (u tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 split71 zero suc rec)
          (v tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 split71 zero suc rec)

zero71 : {g:_} -> Tm71 g Main.nat71
zero71 = \ tm, var71, lam71, app71, tt71, pair71, fst71, snd71, left71, right71, split71, zero71, suc, rec =>
  zero71 _

suc71 : {g:_} -> Tm71 g Main.nat71 -> Tm71 g Main.nat71
suc71 = \ t, tm, var71, lam71, app71, tt71, pair71, fst71, snd71, left71, right71, split71, zero71, suc71, rec =>
   suc71 _ (t tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 split71 zero71 suc71 rec)

rec71 : {g:_}->{a:_} -> Tm71 g Main.nat71 -> Tm71 g (arr71 Main.nat71 (arr71 a a)) -> Tm71 g a -> Tm71 g a
rec71 = \ t, u, v, tm, var71, lam71, app71, tt71, pair71, fst71, snd71, left71, right71, split71, zero71, suc71, rec71 =>
     rec71 _ _
       (t tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 split71 zero71 suc71 rec71)
       (u tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 split71 zero71 suc71 rec71)
       (v tm var71 lam71 app71 tt71 pair71 fst71 snd71 left71 right71 split71 zero71 suc71 rec71)

v071 : {g:_}->{a:_} -> Tm71 (snoc71 g a) a
v071 = var71 vz71

v171 : {g:_}->{a:_}->{b:_} -> Tm71 (snoc71 (snoc71 g a) b) a
v171 = var71 (vs71 vz71)

v271 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm71 (snoc71 (snoc71 (snoc71 g a) b) c) a
v271 = var71 (vs71 (vs71 vz71))

v371 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm71 (snoc71 (snoc71 (snoc71 (snoc71 g a) b) c) d) a
v371 = var71 (vs71 (vs71 (vs71 vz71)))

tbool71 : Ty71
tbool71 = sum71 top71 top71

ttrue71 : {g:_} -> Tm71 g Main.tbool71
ttrue71 = left71 tt71

tfalse71 : {g:_} -> Tm71 g Main.tbool71
tfalse71 = right71 tt71

ifthenelse71 : {g:_}->{a:_} -> Tm71 g (arr71 Main.tbool71 (arr71 a (arr71 a a)))
ifthenelse71 = lam71 (lam71 (lam71 (split71 v271 (lam71 v271) (lam71 v171))))

times471 : {g:_}->{a:_} -> Tm71 g (arr71 (arr71 a a) (arr71 a a))
times471  = lam71 (lam71 (app71 v171 (app71 v171 (app71 v171 (app71 v171 v071)))))

add71 : {g:_} -> Tm71 g (arr71 Main.nat71 (arr71 Main.nat71 Main.nat71))
add71 = lam71 (rec71 v071
       (lam71 (lam71 (lam71 (suc71 (app71 v171 v071)))))
       (lam71 v071))

mul71 : {g:_} -> Tm71 g (arr71 Main.nat71 (arr71 Main.nat71 Main.nat71))
mul71 = lam71 (rec71 v071
       (lam71 (lam71 (lam71 (app71 (app71 add71 (app71 v171 v071)) v071))))
       (lam71 zero71))

fact71 : {g:_} -> Tm71 g (arr71 Main.nat71 Main.nat71)
fact71 = lam71 (rec71 v071 (lam71 (lam71 (app71 (app71 mul71 (suc71 v171)) v071)))
                 (suc71 zero71))

Ty72 : Type
Ty72 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat72 : Ty72
nat72 = \ _, nat72, _, _, _, _, _ => nat72
top72 : Ty72
top72 = \ _, _, top72, _, _, _, _ => top72
bot72 : Ty72
bot72 = \ _, _, _, bot72, _, _, _ => bot72

arr72 : Ty72-> Ty72-> Ty72
arr72 = \ a, b, ty, nat72, top72, bot72, arr72, prod, sum =>
     arr72 (a ty nat72 top72 bot72 arr72 prod sum) (b ty nat72 top72 bot72 arr72 prod sum)

prod72 : Ty72-> Ty72-> Ty72
prod72 = \ a, b, ty, nat72, top72, bot72, arr72, prod72, sum =>
     prod72 (a ty nat72 top72 bot72 arr72 prod72 sum) (b ty nat72 top72 bot72 arr72 prod72 sum)

sum72 : Ty72-> Ty72-> Ty72
sum72 = \ a, b, ty, nat72, top72, bot72, arr72, prod72, sum72 =>
     sum72 (a ty nat72 top72 bot72 arr72 prod72 sum72) (b ty nat72 top72 bot72 arr72 prod72 sum72)

Con72 : Type
Con72 = (Con72 : Type)
 -> (nil  : Con72)
 -> (snoc : Con72 -> Ty72-> Con72)
 -> Con72

nil72 : Con72
nil72 = \ con, nil72, snoc => nil72

snoc72 : Con72 -> Ty72-> Con72
snoc72 = \ g, a, con, nil72, snoc72 => snoc72 (g con nil72 snoc72) a

Var72 : Con72 -> Ty72-> Type
Var72 = \ g, a =>
    (Var72 : Con72 -> Ty72-> Type)
 -> (vz  : (g:_)->(a:_) -> Var72 (snoc72 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var72 g a -> Var72 (snoc72 g b) a)
 -> Var72 g a

vz72 : {g:_}->{a:_} -> Var72 (snoc72 g a) a
vz72 = \ var, vz72, vs => vz72 _ _

vs72 : {g:_}->{b:_}->{a:_} -> Var72 g a -> Var72 (snoc72 g b) a
vs72 = \ x, var, vz72, vs72 => vs72 _ _ _ (x var vz72 vs72)

Tm72 : Con72 -> Ty72-> Type
Tm72 = \ g, a =>
    (Tm72    : Con72 -> Ty72-> Type)
 -> (var   : (g:_)->(a:_)-> Var72 g a -> Tm72 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm72 (snoc72 g a) b -> Tm72 g (arr72 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm72 g (arr72 a b) -> Tm72 g a -> Tm72 g b)
 -> (tt    : (g:_)-> Tm72 g top72)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm72 g a -> Tm72 g b -> Tm72 g (prod72 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm72 g (prod72 a b) -> Tm72 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm72 g (prod72 a b) -> Tm72 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm72 g a -> Tm72 g (sum72 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm72 g b -> Tm72 g (sum72 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm72 g (sum72 a b) -> Tm72 g (arr72 a c) -> Tm72 g (arr72 b c) -> Tm72 g c)
 -> (zero  : (g:_)-> Tm72 g nat72)
 -> (suc   : (g:_)-> Tm72 g nat72 -> Tm72 g nat72)
 -> (rec   : (g:_)->(a:_) -> Tm72 g nat72 -> Tm72 g (arr72 nat72 (arr72 a a)) -> Tm72 g a -> Tm72 g a)
 -> Tm72 g a

var72 : {g:_}->{a:_} -> Var72 g a -> Tm72 g a
var72 = \ x, tm, var72, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var72 _ _ x

lam72 : {g:_}->{a:_}->{b:_}-> Tm72 (snoc72 g a) b -> Tm72 g (arr72 a b)
lam72 = \ t, tm, var72, lam72, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam72 _ _ _ (t tm var72 lam72 app tt pair fst snd left right split zero suc rec)

app72 : {g:_}->{a:_}->{b:_} -> Tm72 g (arr72 a b) -> Tm72 g a -> Tm72 g b
app72 = \ t, u, tm, var72, lam72, app72, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app72 _ _ _ (t tm var72 lam72 app72 tt pair fst snd left right split zero suc rec)
                (u tm var72 lam72 app72 tt pair fst snd left right split zero suc rec)

tt72 : {g:_} -> Tm72 g Main.top72
tt72 = \ tm, var72, lam72, app72, tt72, pair, fst, snd, left, right, split, zero, suc, rec => tt72 _

pair72 : {g:_}->{a:_}->{b:_} -> Tm72 g a -> Tm72 g b -> Tm72 g (prod72 a b)
pair72 = \ t, u, tm, var72, lam72, app72, tt72, pair72, fst, snd, left, right, split, zero, suc, rec =>
     pair72 _ _ _ (t tm var72 lam72 app72 tt72 pair72 fst snd left right split zero suc rec)
                 (u tm var72 lam72 app72 tt72 pair72 fst snd left right split zero suc rec)

fst72 : {g:_}->{a:_}->{b:_}-> Tm72 g (prod72 a b) -> Tm72 g a
fst72 = \ t, tm, var72, lam72, app72, tt72, pair72, fst72, snd, left, right, split, zero, suc, rec =>
     fst72 _ _ _ (t tm var72 lam72 app72 tt72 pair72 fst72 snd left right split zero suc rec)

snd72 : {g:_}->{a:_}->{b:_} -> Tm72 g (prod72 a b) -> Tm72 g b
snd72 = \ t, tm, var72, lam72, app72, tt72, pair72, fst72, snd72, left, right, split, zero, suc, rec =>
     snd72 _ _ _ (t tm var72 lam72 app72 tt72 pair72 fst72 snd72 left right split zero suc rec)

left72 : {g:_}->{a:_}->{b:_} -> Tm72 g a -> Tm72 g (sum72 a b)
left72 = \ t, tm, var72, lam72, app72, tt72, pair72, fst72, snd72, left72, right, split, zero, suc, rec =>
     left72 _ _ _ (t tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right split zero suc rec)

right72 : {g:_}->{a:_}->{b:_} -> Tm72 g b -> Tm72 g (sum72 a b)
right72 = \ t, tm, var72, lam72, app72, tt72, pair72, fst72, snd72, left72, right72, split, zero, suc, rec =>
     right72 _ _ _ (t tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 split zero suc rec)

split72 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm72 g (sum72 a b) -> Tm72 g (arr72 a c) -> Tm72 g (arr72 b c) -> Tm72 g c
split72 = \ t, u, v, tm, var72, lam72, app72, tt72, pair72, fst72, snd72, left72, right72, split72, zero, suc, rec =>
     split72 _ _ _ _
          (t tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 split72 zero suc rec)
          (u tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 split72 zero suc rec)
          (v tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 split72 zero suc rec)

zero72 : {g:_} -> Tm72 g Main.nat72
zero72 = \ tm, var72, lam72, app72, tt72, pair72, fst72, snd72, left72, right72, split72, zero72, suc, rec =>
  zero72 _

suc72 : {g:_} -> Tm72 g Main.nat72 -> Tm72 g Main.nat72
suc72 = \ t, tm, var72, lam72, app72, tt72, pair72, fst72, snd72, left72, right72, split72, zero72, suc72, rec =>
   suc72 _ (t tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 split72 zero72 suc72 rec)

rec72 : {g:_}->{a:_} -> Tm72 g Main.nat72 -> Tm72 g (arr72 Main.nat72 (arr72 a a)) -> Tm72 g a -> Tm72 g a
rec72 = \ t, u, v, tm, var72, lam72, app72, tt72, pair72, fst72, snd72, left72, right72, split72, zero72, suc72, rec72 =>
     rec72 _ _
       (t tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 split72 zero72 suc72 rec72)
       (u tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 split72 zero72 suc72 rec72)
       (v tm var72 lam72 app72 tt72 pair72 fst72 snd72 left72 right72 split72 zero72 suc72 rec72)

v072 : {g:_}->{a:_} -> Tm72 (snoc72 g a) a
v072 = var72 vz72

v172 : {g:_}->{a:_}->{b:_} -> Tm72 (snoc72 (snoc72 g a) b) a
v172 = var72 (vs72 vz72)

v272 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm72 (snoc72 (snoc72 (snoc72 g a) b) c) a
v272 = var72 (vs72 (vs72 vz72))

v372 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm72 (snoc72 (snoc72 (snoc72 (snoc72 g a) b) c) d) a
v372 = var72 (vs72 (vs72 (vs72 vz72)))

tbool72 : Ty72
tbool72 = sum72 top72 top72

ttrue72 : {g:_} -> Tm72 g Main.tbool72
ttrue72 = left72 tt72

tfalse72 : {g:_} -> Tm72 g Main.tbool72
tfalse72 = right72 tt72

ifthenelse72 : {g:_}->{a:_} -> Tm72 g (arr72 Main.tbool72 (arr72 a (arr72 a a)))
ifthenelse72 = lam72 (lam72 (lam72 (split72 v272 (lam72 v272) (lam72 v172))))

times472 : {g:_}->{a:_} -> Tm72 g (arr72 (arr72 a a) (arr72 a a))
times472  = lam72 (lam72 (app72 v172 (app72 v172 (app72 v172 (app72 v172 v072)))))

add72 : {g:_} -> Tm72 g (arr72 Main.nat72 (arr72 Main.nat72 Main.nat72))
add72 = lam72 (rec72 v072
       (lam72 (lam72 (lam72 (suc72 (app72 v172 v072)))))
       (lam72 v072))

mul72 : {g:_} -> Tm72 g (arr72 Main.nat72 (arr72 Main.nat72 Main.nat72))
mul72 = lam72 (rec72 v072
       (lam72 (lam72 (lam72 (app72 (app72 add72 (app72 v172 v072)) v072))))
       (lam72 zero72))

fact72 : {g:_} -> Tm72 g (arr72 Main.nat72 Main.nat72)
fact72 = lam72 (rec72 v072 (lam72 (lam72 (app72 (app72 mul72 (suc72 v172)) v072)))
                 (suc72 zero72))

Ty73 : Type
Ty73 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat73 : Ty73
nat73 = \ _, nat73, _, _, _, _, _ => nat73
top73 : Ty73
top73 = \ _, _, top73, _, _, _, _ => top73
bot73 : Ty73
bot73 = \ _, _, _, bot73, _, _, _ => bot73

arr73 : Ty73-> Ty73-> Ty73
arr73 = \ a, b, ty, nat73, top73, bot73, arr73, prod, sum =>
     arr73 (a ty nat73 top73 bot73 arr73 prod sum) (b ty nat73 top73 bot73 arr73 prod sum)

prod73 : Ty73-> Ty73-> Ty73
prod73 = \ a, b, ty, nat73, top73, bot73, arr73, prod73, sum =>
     prod73 (a ty nat73 top73 bot73 arr73 prod73 sum) (b ty nat73 top73 bot73 arr73 prod73 sum)

sum73 : Ty73-> Ty73-> Ty73
sum73 = \ a, b, ty, nat73, top73, bot73, arr73, prod73, sum73 =>
     sum73 (a ty nat73 top73 bot73 arr73 prod73 sum73) (b ty nat73 top73 bot73 arr73 prod73 sum73)

Con73 : Type
Con73 = (Con73 : Type)
 -> (nil  : Con73)
 -> (snoc : Con73 -> Ty73-> Con73)
 -> Con73

nil73 : Con73
nil73 = \ con, nil73, snoc => nil73

snoc73 : Con73 -> Ty73-> Con73
snoc73 = \ g, a, con, nil73, snoc73 => snoc73 (g con nil73 snoc73) a

Var73 : Con73 -> Ty73-> Type
Var73 = \ g, a =>
    (Var73 : Con73 -> Ty73-> Type)
 -> (vz  : (g:_)->(a:_) -> Var73 (snoc73 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var73 g a -> Var73 (snoc73 g b) a)
 -> Var73 g a

vz73 : {g:_}->{a:_} -> Var73 (snoc73 g a) a
vz73 = \ var, vz73, vs => vz73 _ _

vs73 : {g:_}->{b:_}->{a:_} -> Var73 g a -> Var73 (snoc73 g b) a
vs73 = \ x, var, vz73, vs73 => vs73 _ _ _ (x var vz73 vs73)

Tm73 : Con73 -> Ty73-> Type
Tm73 = \ g, a =>
    (Tm73    : Con73 -> Ty73-> Type)
 -> (var   : (g:_)->(a:_)-> Var73 g a -> Tm73 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm73 (snoc73 g a) b -> Tm73 g (arr73 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm73 g (arr73 a b) -> Tm73 g a -> Tm73 g b)
 -> (tt    : (g:_)-> Tm73 g top73)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm73 g a -> Tm73 g b -> Tm73 g (prod73 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm73 g (prod73 a b) -> Tm73 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm73 g (prod73 a b) -> Tm73 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm73 g a -> Tm73 g (sum73 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm73 g b -> Tm73 g (sum73 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm73 g (sum73 a b) -> Tm73 g (arr73 a c) -> Tm73 g (arr73 b c) -> Tm73 g c)
 -> (zero  : (g:_)-> Tm73 g nat73)
 -> (suc   : (g:_)-> Tm73 g nat73 -> Tm73 g nat73)
 -> (rec   : (g:_)->(a:_) -> Tm73 g nat73 -> Tm73 g (arr73 nat73 (arr73 a a)) -> Tm73 g a -> Tm73 g a)
 -> Tm73 g a

var73 : {g:_}->{a:_} -> Var73 g a -> Tm73 g a
var73 = \ x, tm, var73, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var73 _ _ x

lam73 : {g:_}->{a:_}->{b:_}-> Tm73 (snoc73 g a) b -> Tm73 g (arr73 a b)
lam73 = \ t, tm, var73, lam73, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam73 _ _ _ (t tm var73 lam73 app tt pair fst snd left right split zero suc rec)

app73 : {g:_}->{a:_}->{b:_} -> Tm73 g (arr73 a b) -> Tm73 g a -> Tm73 g b
app73 = \ t, u, tm, var73, lam73, app73, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app73 _ _ _ (t tm var73 lam73 app73 tt pair fst snd left right split zero suc rec)
                (u tm var73 lam73 app73 tt pair fst snd left right split zero suc rec)

tt73 : {g:_} -> Tm73 g Main.top73
tt73 = \ tm, var73, lam73, app73, tt73, pair, fst, snd, left, right, split, zero, suc, rec => tt73 _

pair73 : {g:_}->{a:_}->{b:_} -> Tm73 g a -> Tm73 g b -> Tm73 g (prod73 a b)
pair73 = \ t, u, tm, var73, lam73, app73, tt73, pair73, fst, snd, left, right, split, zero, suc, rec =>
     pair73 _ _ _ (t tm var73 lam73 app73 tt73 pair73 fst snd left right split zero suc rec)
                 (u tm var73 lam73 app73 tt73 pair73 fst snd left right split zero suc rec)

fst73 : {g:_}->{a:_}->{b:_}-> Tm73 g (prod73 a b) -> Tm73 g a
fst73 = \ t, tm, var73, lam73, app73, tt73, pair73, fst73, snd, left, right, split, zero, suc, rec =>
     fst73 _ _ _ (t tm var73 lam73 app73 tt73 pair73 fst73 snd left right split zero suc rec)

snd73 : {g:_}->{a:_}->{b:_} -> Tm73 g (prod73 a b) -> Tm73 g b
snd73 = \ t, tm, var73, lam73, app73, tt73, pair73, fst73, snd73, left, right, split, zero, suc, rec =>
     snd73 _ _ _ (t tm var73 lam73 app73 tt73 pair73 fst73 snd73 left right split zero suc rec)

left73 : {g:_}->{a:_}->{b:_} -> Tm73 g a -> Tm73 g (sum73 a b)
left73 = \ t, tm, var73, lam73, app73, tt73, pair73, fst73, snd73, left73, right, split, zero, suc, rec =>
     left73 _ _ _ (t tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right split zero suc rec)

right73 : {g:_}->{a:_}->{b:_} -> Tm73 g b -> Tm73 g (sum73 a b)
right73 = \ t, tm, var73, lam73, app73, tt73, pair73, fst73, snd73, left73, right73, split, zero, suc, rec =>
     right73 _ _ _ (t tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 split zero suc rec)

split73 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm73 g (sum73 a b) -> Tm73 g (arr73 a c) -> Tm73 g (arr73 b c) -> Tm73 g c
split73 = \ t, u, v, tm, var73, lam73, app73, tt73, pair73, fst73, snd73, left73, right73, split73, zero, suc, rec =>
     split73 _ _ _ _
          (t tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 split73 zero suc rec)
          (u tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 split73 zero suc rec)
          (v tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 split73 zero suc rec)

zero73 : {g:_} -> Tm73 g Main.nat73
zero73 = \ tm, var73, lam73, app73, tt73, pair73, fst73, snd73, left73, right73, split73, zero73, suc, rec =>
  zero73 _

suc73 : {g:_} -> Tm73 g Main.nat73 -> Tm73 g Main.nat73
suc73 = \ t, tm, var73, lam73, app73, tt73, pair73, fst73, snd73, left73, right73, split73, zero73, suc73, rec =>
   suc73 _ (t tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 split73 zero73 suc73 rec)

rec73 : {g:_}->{a:_} -> Tm73 g Main.nat73 -> Tm73 g (arr73 Main.nat73 (arr73 a a)) -> Tm73 g a -> Tm73 g a
rec73 = \ t, u, v, tm, var73, lam73, app73, tt73, pair73, fst73, snd73, left73, right73, split73, zero73, suc73, rec73 =>
     rec73 _ _
       (t tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 split73 zero73 suc73 rec73)
       (u tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 split73 zero73 suc73 rec73)
       (v tm var73 lam73 app73 tt73 pair73 fst73 snd73 left73 right73 split73 zero73 suc73 rec73)

v073 : {g:_}->{a:_} -> Tm73 (snoc73 g a) a
v073 = var73 vz73

v173 : {g:_}->{a:_}->{b:_} -> Tm73 (snoc73 (snoc73 g a) b) a
v173 = var73 (vs73 vz73)

v273 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm73 (snoc73 (snoc73 (snoc73 g a) b) c) a
v273 = var73 (vs73 (vs73 vz73))

v373 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm73 (snoc73 (snoc73 (snoc73 (snoc73 g a) b) c) d) a
v373 = var73 (vs73 (vs73 (vs73 vz73)))

tbool73 : Ty73
tbool73 = sum73 top73 top73

ttrue73 : {g:_} -> Tm73 g Main.tbool73
ttrue73 = left73 tt73

tfalse73 : {g:_} -> Tm73 g Main.tbool73
tfalse73 = right73 tt73

ifthenelse73 : {g:_}->{a:_} -> Tm73 g (arr73 Main.tbool73 (arr73 a (arr73 a a)))
ifthenelse73 = lam73 (lam73 (lam73 (split73 v273 (lam73 v273) (lam73 v173))))

times473 : {g:_}->{a:_} -> Tm73 g (arr73 (arr73 a a) (arr73 a a))
times473  = lam73 (lam73 (app73 v173 (app73 v173 (app73 v173 (app73 v173 v073)))))

add73 : {g:_} -> Tm73 g (arr73 Main.nat73 (arr73 Main.nat73 Main.nat73))
add73 = lam73 (rec73 v073
       (lam73 (lam73 (lam73 (suc73 (app73 v173 v073)))))
       (lam73 v073))

mul73 : {g:_} -> Tm73 g (arr73 Main.nat73 (arr73 Main.nat73 Main.nat73))
mul73 = lam73 (rec73 v073
       (lam73 (lam73 (lam73 (app73 (app73 add73 (app73 v173 v073)) v073))))
       (lam73 zero73))

fact73 : {g:_} -> Tm73 g (arr73 Main.nat73 Main.nat73)
fact73 = lam73 (rec73 v073 (lam73 (lam73 (app73 (app73 mul73 (suc73 v173)) v073)))
                 (suc73 zero73))

Ty74 : Type
Ty74 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat74 : Ty74
nat74 = \ _, nat74, _, _, _, _, _ => nat74
top74 : Ty74
top74 = \ _, _, top74, _, _, _, _ => top74
bot74 : Ty74
bot74 = \ _, _, _, bot74, _, _, _ => bot74

arr74 : Ty74-> Ty74-> Ty74
arr74 = \ a, b, ty, nat74, top74, bot74, arr74, prod, sum =>
     arr74 (a ty nat74 top74 bot74 arr74 prod sum) (b ty nat74 top74 bot74 arr74 prod sum)

prod74 : Ty74-> Ty74-> Ty74
prod74 = \ a, b, ty, nat74, top74, bot74, arr74, prod74, sum =>
     prod74 (a ty nat74 top74 bot74 arr74 prod74 sum) (b ty nat74 top74 bot74 arr74 prod74 sum)

sum74 : Ty74-> Ty74-> Ty74
sum74 = \ a, b, ty, nat74, top74, bot74, arr74, prod74, sum74 =>
     sum74 (a ty nat74 top74 bot74 arr74 prod74 sum74) (b ty nat74 top74 bot74 arr74 prod74 sum74)

Con74 : Type
Con74 = (Con74 : Type)
 -> (nil  : Con74)
 -> (snoc : Con74 -> Ty74-> Con74)
 -> Con74

nil74 : Con74
nil74 = \ con, nil74, snoc => nil74

snoc74 : Con74 -> Ty74-> Con74
snoc74 = \ g, a, con, nil74, snoc74 => snoc74 (g con nil74 snoc74) a

Var74 : Con74 -> Ty74-> Type
Var74 = \ g, a =>
    (Var74 : Con74 -> Ty74-> Type)
 -> (vz  : (g:_)->(a:_) -> Var74 (snoc74 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var74 g a -> Var74 (snoc74 g b) a)
 -> Var74 g a

vz74 : {g:_}->{a:_} -> Var74 (snoc74 g a) a
vz74 = \ var, vz74, vs => vz74 _ _

vs74 : {g:_}->{b:_}->{a:_} -> Var74 g a -> Var74 (snoc74 g b) a
vs74 = \ x, var, vz74, vs74 => vs74 _ _ _ (x var vz74 vs74)

Tm74 : Con74 -> Ty74-> Type
Tm74 = \ g, a =>
    (Tm74    : Con74 -> Ty74-> Type)
 -> (var   : (g:_)->(a:_)-> Var74 g a -> Tm74 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm74 (snoc74 g a) b -> Tm74 g (arr74 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm74 g (arr74 a b) -> Tm74 g a -> Tm74 g b)
 -> (tt    : (g:_)-> Tm74 g top74)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm74 g a -> Tm74 g b -> Tm74 g (prod74 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm74 g (prod74 a b) -> Tm74 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm74 g (prod74 a b) -> Tm74 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm74 g a -> Tm74 g (sum74 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm74 g b -> Tm74 g (sum74 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm74 g (sum74 a b) -> Tm74 g (arr74 a c) -> Tm74 g (arr74 b c) -> Tm74 g c)
 -> (zero  : (g:_)-> Tm74 g nat74)
 -> (suc   : (g:_)-> Tm74 g nat74 -> Tm74 g nat74)
 -> (rec   : (g:_)->(a:_) -> Tm74 g nat74 -> Tm74 g (arr74 nat74 (arr74 a a)) -> Tm74 g a -> Tm74 g a)
 -> Tm74 g a

var74 : {g:_}->{a:_} -> Var74 g a -> Tm74 g a
var74 = \ x, tm, var74, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var74 _ _ x

lam74 : {g:_}->{a:_}->{b:_}-> Tm74 (snoc74 g a) b -> Tm74 g (arr74 a b)
lam74 = \ t, tm, var74, lam74, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam74 _ _ _ (t tm var74 lam74 app tt pair fst snd left right split zero suc rec)

app74 : {g:_}->{a:_}->{b:_} -> Tm74 g (arr74 a b) -> Tm74 g a -> Tm74 g b
app74 = \ t, u, tm, var74, lam74, app74, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app74 _ _ _ (t tm var74 lam74 app74 tt pair fst snd left right split zero suc rec)
                (u tm var74 lam74 app74 tt pair fst snd left right split zero suc rec)

tt74 : {g:_} -> Tm74 g Main.top74
tt74 = \ tm, var74, lam74, app74, tt74, pair, fst, snd, left, right, split, zero, suc, rec => tt74 _

pair74 : {g:_}->{a:_}->{b:_} -> Tm74 g a -> Tm74 g b -> Tm74 g (prod74 a b)
pair74 = \ t, u, tm, var74, lam74, app74, tt74, pair74, fst, snd, left, right, split, zero, suc, rec =>
     pair74 _ _ _ (t tm var74 lam74 app74 tt74 pair74 fst snd left right split zero suc rec)
                 (u tm var74 lam74 app74 tt74 pair74 fst snd left right split zero suc rec)

fst74 : {g:_}->{a:_}->{b:_}-> Tm74 g (prod74 a b) -> Tm74 g a
fst74 = \ t, tm, var74, lam74, app74, tt74, pair74, fst74, snd, left, right, split, zero, suc, rec =>
     fst74 _ _ _ (t tm var74 lam74 app74 tt74 pair74 fst74 snd left right split zero suc rec)

snd74 : {g:_}->{a:_}->{b:_} -> Tm74 g (prod74 a b) -> Tm74 g b
snd74 = \ t, tm, var74, lam74, app74, tt74, pair74, fst74, snd74, left, right, split, zero, suc, rec =>
     snd74 _ _ _ (t tm var74 lam74 app74 tt74 pair74 fst74 snd74 left right split zero suc rec)

left74 : {g:_}->{a:_}->{b:_} -> Tm74 g a -> Tm74 g (sum74 a b)
left74 = \ t, tm, var74, lam74, app74, tt74, pair74, fst74, snd74, left74, right, split, zero, suc, rec =>
     left74 _ _ _ (t tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right split zero suc rec)

right74 : {g:_}->{a:_}->{b:_} -> Tm74 g b -> Tm74 g (sum74 a b)
right74 = \ t, tm, var74, lam74, app74, tt74, pair74, fst74, snd74, left74, right74, split, zero, suc, rec =>
     right74 _ _ _ (t tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 split zero suc rec)

split74 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm74 g (sum74 a b) -> Tm74 g (arr74 a c) -> Tm74 g (arr74 b c) -> Tm74 g c
split74 = \ t, u, v, tm, var74, lam74, app74, tt74, pair74, fst74, snd74, left74, right74, split74, zero, suc, rec =>
     split74 _ _ _ _
          (t tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 split74 zero suc rec)
          (u tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 split74 zero suc rec)
          (v tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 split74 zero suc rec)

zero74 : {g:_} -> Tm74 g Main.nat74
zero74 = \ tm, var74, lam74, app74, tt74, pair74, fst74, snd74, left74, right74, split74, zero74, suc, rec =>
  zero74 _

suc74 : {g:_} -> Tm74 g Main.nat74 -> Tm74 g Main.nat74
suc74 = \ t, tm, var74, lam74, app74, tt74, pair74, fst74, snd74, left74, right74, split74, zero74, suc74, rec =>
   suc74 _ (t tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 split74 zero74 suc74 rec)

rec74 : {g:_}->{a:_} -> Tm74 g Main.nat74 -> Tm74 g (arr74 Main.nat74 (arr74 a a)) -> Tm74 g a -> Tm74 g a
rec74 = \ t, u, v, tm, var74, lam74, app74, tt74, pair74, fst74, snd74, left74, right74, split74, zero74, suc74, rec74 =>
     rec74 _ _
       (t tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 split74 zero74 suc74 rec74)
       (u tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 split74 zero74 suc74 rec74)
       (v tm var74 lam74 app74 tt74 pair74 fst74 snd74 left74 right74 split74 zero74 suc74 rec74)

v074 : {g:_}->{a:_} -> Tm74 (snoc74 g a) a
v074 = var74 vz74

v174 : {g:_}->{a:_}->{b:_} -> Tm74 (snoc74 (snoc74 g a) b) a
v174 = var74 (vs74 vz74)

v274 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm74 (snoc74 (snoc74 (snoc74 g a) b) c) a
v274 = var74 (vs74 (vs74 vz74))

v374 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm74 (snoc74 (snoc74 (snoc74 (snoc74 g a) b) c) d) a
v374 = var74 (vs74 (vs74 (vs74 vz74)))

tbool74 : Ty74
tbool74 = sum74 top74 top74

ttrue74 : {g:_} -> Tm74 g Main.tbool74
ttrue74 = left74 tt74

tfalse74 : {g:_} -> Tm74 g Main.tbool74
tfalse74 = right74 tt74

ifthenelse74 : {g:_}->{a:_} -> Tm74 g (arr74 Main.tbool74 (arr74 a (arr74 a a)))
ifthenelse74 = lam74 (lam74 (lam74 (split74 v274 (lam74 v274) (lam74 v174))))

times474 : {g:_}->{a:_} -> Tm74 g (arr74 (arr74 a a) (arr74 a a))
times474  = lam74 (lam74 (app74 v174 (app74 v174 (app74 v174 (app74 v174 v074)))))

add74 : {g:_} -> Tm74 g (arr74 Main.nat74 (arr74 Main.nat74 Main.nat74))
add74 = lam74 (rec74 v074
       (lam74 (lam74 (lam74 (suc74 (app74 v174 v074)))))
       (lam74 v074))

mul74 : {g:_} -> Tm74 g (arr74 Main.nat74 (arr74 Main.nat74 Main.nat74))
mul74 = lam74 (rec74 v074
       (lam74 (lam74 (lam74 (app74 (app74 add74 (app74 v174 v074)) v074))))
       (lam74 zero74))

fact74 : {g:_} -> Tm74 g (arr74 Main.nat74 Main.nat74)
fact74 = lam74 (rec74 v074 (lam74 (lam74 (app74 (app74 mul74 (suc74 v174)) v074)))
                 (suc74 zero74))

Ty75 : Type
Ty75 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat75 : Ty75
nat75 = \ _, nat75, _, _, _, _, _ => nat75
top75 : Ty75
top75 = \ _, _, top75, _, _, _, _ => top75
bot75 : Ty75
bot75 = \ _, _, _, bot75, _, _, _ => bot75

arr75 : Ty75-> Ty75-> Ty75
arr75 = \ a, b, ty, nat75, top75, bot75, arr75, prod, sum =>
     arr75 (a ty nat75 top75 bot75 arr75 prod sum) (b ty nat75 top75 bot75 arr75 prod sum)

prod75 : Ty75-> Ty75-> Ty75
prod75 = \ a, b, ty, nat75, top75, bot75, arr75, prod75, sum =>
     prod75 (a ty nat75 top75 bot75 arr75 prod75 sum) (b ty nat75 top75 bot75 arr75 prod75 sum)

sum75 : Ty75-> Ty75-> Ty75
sum75 = \ a, b, ty, nat75, top75, bot75, arr75, prod75, sum75 =>
     sum75 (a ty nat75 top75 bot75 arr75 prod75 sum75) (b ty nat75 top75 bot75 arr75 prod75 sum75)

Con75 : Type
Con75 = (Con75 : Type)
 -> (nil  : Con75)
 -> (snoc : Con75 -> Ty75-> Con75)
 -> Con75

nil75 : Con75
nil75 = \ con, nil75, snoc => nil75

snoc75 : Con75 -> Ty75-> Con75
snoc75 = \ g, a, con, nil75, snoc75 => snoc75 (g con nil75 snoc75) a

Var75 : Con75 -> Ty75-> Type
Var75 = \ g, a =>
    (Var75 : Con75 -> Ty75-> Type)
 -> (vz  : (g:_)->(a:_) -> Var75 (snoc75 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var75 g a -> Var75 (snoc75 g b) a)
 -> Var75 g a

vz75 : {g:_}->{a:_} -> Var75 (snoc75 g a) a
vz75 = \ var, vz75, vs => vz75 _ _

vs75 : {g:_}->{b:_}->{a:_} -> Var75 g a -> Var75 (snoc75 g b) a
vs75 = \ x, var, vz75, vs75 => vs75 _ _ _ (x var vz75 vs75)

Tm75 : Con75 -> Ty75-> Type
Tm75 = \ g, a =>
    (Tm75    : Con75 -> Ty75-> Type)
 -> (var   : (g:_)->(a:_)-> Var75 g a -> Tm75 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm75 (snoc75 g a) b -> Tm75 g (arr75 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm75 g (arr75 a b) -> Tm75 g a -> Tm75 g b)
 -> (tt    : (g:_)-> Tm75 g top75)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm75 g a -> Tm75 g b -> Tm75 g (prod75 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm75 g (prod75 a b) -> Tm75 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm75 g (prod75 a b) -> Tm75 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm75 g a -> Tm75 g (sum75 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm75 g b -> Tm75 g (sum75 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm75 g (sum75 a b) -> Tm75 g (arr75 a c) -> Tm75 g (arr75 b c) -> Tm75 g c)
 -> (zero  : (g:_)-> Tm75 g nat75)
 -> (suc   : (g:_)-> Tm75 g nat75 -> Tm75 g nat75)
 -> (rec   : (g:_)->(a:_) -> Tm75 g nat75 -> Tm75 g (arr75 nat75 (arr75 a a)) -> Tm75 g a -> Tm75 g a)
 -> Tm75 g a

var75 : {g:_}->{a:_} -> Var75 g a -> Tm75 g a
var75 = \ x, tm, var75, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var75 _ _ x

lam75 : {g:_}->{a:_}->{b:_}-> Tm75 (snoc75 g a) b -> Tm75 g (arr75 a b)
lam75 = \ t, tm, var75, lam75, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam75 _ _ _ (t tm var75 lam75 app tt pair fst snd left right split zero suc rec)

app75 : {g:_}->{a:_}->{b:_} -> Tm75 g (arr75 a b) -> Tm75 g a -> Tm75 g b
app75 = \ t, u, tm, var75, lam75, app75, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app75 _ _ _ (t tm var75 lam75 app75 tt pair fst snd left right split zero suc rec)
                (u tm var75 lam75 app75 tt pair fst snd left right split zero suc rec)

tt75 : {g:_} -> Tm75 g Main.top75
tt75 = \ tm, var75, lam75, app75, tt75, pair, fst, snd, left, right, split, zero, suc, rec => tt75 _

pair75 : {g:_}->{a:_}->{b:_} -> Tm75 g a -> Tm75 g b -> Tm75 g (prod75 a b)
pair75 = \ t, u, tm, var75, lam75, app75, tt75, pair75, fst, snd, left, right, split, zero, suc, rec =>
     pair75 _ _ _ (t tm var75 lam75 app75 tt75 pair75 fst snd left right split zero suc rec)
                 (u tm var75 lam75 app75 tt75 pair75 fst snd left right split zero suc rec)

fst75 : {g:_}->{a:_}->{b:_}-> Tm75 g (prod75 a b) -> Tm75 g a
fst75 = \ t, tm, var75, lam75, app75, tt75, pair75, fst75, snd, left, right, split, zero, suc, rec =>
     fst75 _ _ _ (t tm var75 lam75 app75 tt75 pair75 fst75 snd left right split zero suc rec)

snd75 : {g:_}->{a:_}->{b:_} -> Tm75 g (prod75 a b) -> Tm75 g b
snd75 = \ t, tm, var75, lam75, app75, tt75, pair75, fst75, snd75, left, right, split, zero, suc, rec =>
     snd75 _ _ _ (t tm var75 lam75 app75 tt75 pair75 fst75 snd75 left right split zero suc rec)

left75 : {g:_}->{a:_}->{b:_} -> Tm75 g a -> Tm75 g (sum75 a b)
left75 = \ t, tm, var75, lam75, app75, tt75, pair75, fst75, snd75, left75, right, split, zero, suc, rec =>
     left75 _ _ _ (t tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right split zero suc rec)

right75 : {g:_}->{a:_}->{b:_} -> Tm75 g b -> Tm75 g (sum75 a b)
right75 = \ t, tm, var75, lam75, app75, tt75, pair75, fst75, snd75, left75, right75, split, zero, suc, rec =>
     right75 _ _ _ (t tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 split zero suc rec)

split75 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm75 g (sum75 a b) -> Tm75 g (arr75 a c) -> Tm75 g (arr75 b c) -> Tm75 g c
split75 = \ t, u, v, tm, var75, lam75, app75, tt75, pair75, fst75, snd75, left75, right75, split75, zero, suc, rec =>
     split75 _ _ _ _
          (t tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 split75 zero suc rec)
          (u tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 split75 zero suc rec)
          (v tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 split75 zero suc rec)

zero75 : {g:_} -> Tm75 g Main.nat75
zero75 = \ tm, var75, lam75, app75, tt75, pair75, fst75, snd75, left75, right75, split75, zero75, suc, rec =>
  zero75 _

suc75 : {g:_} -> Tm75 g Main.nat75 -> Tm75 g Main.nat75
suc75 = \ t, tm, var75, lam75, app75, tt75, pair75, fst75, snd75, left75, right75, split75, zero75, suc75, rec =>
   suc75 _ (t tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 split75 zero75 suc75 rec)

rec75 : {g:_}->{a:_} -> Tm75 g Main.nat75 -> Tm75 g (arr75 Main.nat75 (arr75 a a)) -> Tm75 g a -> Tm75 g a
rec75 = \ t, u, v, tm, var75, lam75, app75, tt75, pair75, fst75, snd75, left75, right75, split75, zero75, suc75, rec75 =>
     rec75 _ _
       (t tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 split75 zero75 suc75 rec75)
       (u tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 split75 zero75 suc75 rec75)
       (v tm var75 lam75 app75 tt75 pair75 fst75 snd75 left75 right75 split75 zero75 suc75 rec75)

v075 : {g:_}->{a:_} -> Tm75 (snoc75 g a) a
v075 = var75 vz75

v175 : {g:_}->{a:_}->{b:_} -> Tm75 (snoc75 (snoc75 g a) b) a
v175 = var75 (vs75 vz75)

v275 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm75 (snoc75 (snoc75 (snoc75 g a) b) c) a
v275 = var75 (vs75 (vs75 vz75))

v375 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm75 (snoc75 (snoc75 (snoc75 (snoc75 g a) b) c) d) a
v375 = var75 (vs75 (vs75 (vs75 vz75)))

tbool75 : Ty75
tbool75 = sum75 top75 top75

ttrue75 : {g:_} -> Tm75 g Main.tbool75
ttrue75 = left75 tt75

tfalse75 : {g:_} -> Tm75 g Main.tbool75
tfalse75 = right75 tt75

ifthenelse75 : {g:_}->{a:_} -> Tm75 g (arr75 Main.tbool75 (arr75 a (arr75 a a)))
ifthenelse75 = lam75 (lam75 (lam75 (split75 v275 (lam75 v275) (lam75 v175))))

times475 : {g:_}->{a:_} -> Tm75 g (arr75 (arr75 a a) (arr75 a a))
times475  = lam75 (lam75 (app75 v175 (app75 v175 (app75 v175 (app75 v175 v075)))))

add75 : {g:_} -> Tm75 g (arr75 Main.nat75 (arr75 Main.nat75 Main.nat75))
add75 = lam75 (rec75 v075
       (lam75 (lam75 (lam75 (suc75 (app75 v175 v075)))))
       (lam75 v075))

mul75 : {g:_} -> Tm75 g (arr75 Main.nat75 (arr75 Main.nat75 Main.nat75))
mul75 = lam75 (rec75 v075
       (lam75 (lam75 (lam75 (app75 (app75 add75 (app75 v175 v075)) v075))))
       (lam75 zero75))

fact75 : {g:_} -> Tm75 g (arr75 Main.nat75 Main.nat75)
fact75 = lam75 (rec75 v075 (lam75 (lam75 (app75 (app75 mul75 (suc75 v175)) v075)))
                 (suc75 zero75))

Ty76 : Type
Ty76 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat76 : Ty76
nat76 = \ _, nat76, _, _, _, _, _ => nat76
top76 : Ty76
top76 = \ _, _, top76, _, _, _, _ => top76
bot76 : Ty76
bot76 = \ _, _, _, bot76, _, _, _ => bot76

arr76 : Ty76-> Ty76-> Ty76
arr76 = \ a, b, ty, nat76, top76, bot76, arr76, prod, sum =>
     arr76 (a ty nat76 top76 bot76 arr76 prod sum) (b ty nat76 top76 bot76 arr76 prod sum)

prod76 : Ty76-> Ty76-> Ty76
prod76 = \ a, b, ty, nat76, top76, bot76, arr76, prod76, sum =>
     prod76 (a ty nat76 top76 bot76 arr76 prod76 sum) (b ty nat76 top76 bot76 arr76 prod76 sum)

sum76 : Ty76-> Ty76-> Ty76
sum76 = \ a, b, ty, nat76, top76, bot76, arr76, prod76, sum76 =>
     sum76 (a ty nat76 top76 bot76 arr76 prod76 sum76) (b ty nat76 top76 bot76 arr76 prod76 sum76)

Con76 : Type
Con76 = (Con76 : Type)
 -> (nil  : Con76)
 -> (snoc : Con76 -> Ty76-> Con76)
 -> Con76

nil76 : Con76
nil76 = \ con, nil76, snoc => nil76

snoc76 : Con76 -> Ty76-> Con76
snoc76 = \ g, a, con, nil76, snoc76 => snoc76 (g con nil76 snoc76) a

Var76 : Con76 -> Ty76-> Type
Var76 = \ g, a =>
    (Var76 : Con76 -> Ty76-> Type)
 -> (vz  : (g:_)->(a:_) -> Var76 (snoc76 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var76 g a -> Var76 (snoc76 g b) a)
 -> Var76 g a

vz76 : {g:_}->{a:_} -> Var76 (snoc76 g a) a
vz76 = \ var, vz76, vs => vz76 _ _

vs76 : {g:_}->{b:_}->{a:_} -> Var76 g a -> Var76 (snoc76 g b) a
vs76 = \ x, var, vz76, vs76 => vs76 _ _ _ (x var vz76 vs76)

Tm76 : Con76 -> Ty76-> Type
Tm76 = \ g, a =>
    (Tm76    : Con76 -> Ty76-> Type)
 -> (var   : (g:_)->(a:_)-> Var76 g a -> Tm76 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm76 (snoc76 g a) b -> Tm76 g (arr76 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm76 g (arr76 a b) -> Tm76 g a -> Tm76 g b)
 -> (tt    : (g:_)-> Tm76 g top76)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm76 g a -> Tm76 g b -> Tm76 g (prod76 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm76 g (prod76 a b) -> Tm76 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm76 g (prod76 a b) -> Tm76 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm76 g a -> Tm76 g (sum76 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm76 g b -> Tm76 g (sum76 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm76 g (sum76 a b) -> Tm76 g (arr76 a c) -> Tm76 g (arr76 b c) -> Tm76 g c)
 -> (zero  : (g:_)-> Tm76 g nat76)
 -> (suc   : (g:_)-> Tm76 g nat76 -> Tm76 g nat76)
 -> (rec   : (g:_)->(a:_) -> Tm76 g nat76 -> Tm76 g (arr76 nat76 (arr76 a a)) -> Tm76 g a -> Tm76 g a)
 -> Tm76 g a

var76 : {g:_}->{a:_} -> Var76 g a -> Tm76 g a
var76 = \ x, tm, var76, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var76 _ _ x

lam76 : {g:_}->{a:_}->{b:_}-> Tm76 (snoc76 g a) b -> Tm76 g (arr76 a b)
lam76 = \ t, tm, var76, lam76, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam76 _ _ _ (t tm var76 lam76 app tt pair fst snd left right split zero suc rec)

app76 : {g:_}->{a:_}->{b:_} -> Tm76 g (arr76 a b) -> Tm76 g a -> Tm76 g b
app76 = \ t, u, tm, var76, lam76, app76, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app76 _ _ _ (t tm var76 lam76 app76 tt pair fst snd left right split zero suc rec)
                (u tm var76 lam76 app76 tt pair fst snd left right split zero suc rec)

tt76 : {g:_} -> Tm76 g Main.top76
tt76 = \ tm, var76, lam76, app76, tt76, pair, fst, snd, left, right, split, zero, suc, rec => tt76 _

pair76 : {g:_}->{a:_}->{b:_} -> Tm76 g a -> Tm76 g b -> Tm76 g (prod76 a b)
pair76 = \ t, u, tm, var76, lam76, app76, tt76, pair76, fst, snd, left, right, split, zero, suc, rec =>
     pair76 _ _ _ (t tm var76 lam76 app76 tt76 pair76 fst snd left right split zero suc rec)
                 (u tm var76 lam76 app76 tt76 pair76 fst snd left right split zero suc rec)

fst76 : {g:_}->{a:_}->{b:_}-> Tm76 g (prod76 a b) -> Tm76 g a
fst76 = \ t, tm, var76, lam76, app76, tt76, pair76, fst76, snd, left, right, split, zero, suc, rec =>
     fst76 _ _ _ (t tm var76 lam76 app76 tt76 pair76 fst76 snd left right split zero suc rec)

snd76 : {g:_}->{a:_}->{b:_} -> Tm76 g (prod76 a b) -> Tm76 g b
snd76 = \ t, tm, var76, lam76, app76, tt76, pair76, fst76, snd76, left, right, split, zero, suc, rec =>
     snd76 _ _ _ (t tm var76 lam76 app76 tt76 pair76 fst76 snd76 left right split zero suc rec)

left76 : {g:_}->{a:_}->{b:_} -> Tm76 g a -> Tm76 g (sum76 a b)
left76 = \ t, tm, var76, lam76, app76, tt76, pair76, fst76, snd76, left76, right, split, zero, suc, rec =>
     left76 _ _ _ (t tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right split zero suc rec)

right76 : {g:_}->{a:_}->{b:_} -> Tm76 g b -> Tm76 g (sum76 a b)
right76 = \ t, tm, var76, lam76, app76, tt76, pair76, fst76, snd76, left76, right76, split, zero, suc, rec =>
     right76 _ _ _ (t tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 split zero suc rec)

split76 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm76 g (sum76 a b) -> Tm76 g (arr76 a c) -> Tm76 g (arr76 b c) -> Tm76 g c
split76 = \ t, u, v, tm, var76, lam76, app76, tt76, pair76, fst76, snd76, left76, right76, split76, zero, suc, rec =>
     split76 _ _ _ _
          (t tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 split76 zero suc rec)
          (u tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 split76 zero suc rec)
          (v tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 split76 zero suc rec)

zero76 : {g:_} -> Tm76 g Main.nat76
zero76 = \ tm, var76, lam76, app76, tt76, pair76, fst76, snd76, left76, right76, split76, zero76, suc, rec =>
  zero76 _

suc76 : {g:_} -> Tm76 g Main.nat76 -> Tm76 g Main.nat76
suc76 = \ t, tm, var76, lam76, app76, tt76, pair76, fst76, snd76, left76, right76, split76, zero76, suc76, rec =>
   suc76 _ (t tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 split76 zero76 suc76 rec)

rec76 : {g:_}->{a:_} -> Tm76 g Main.nat76 -> Tm76 g (arr76 Main.nat76 (arr76 a a)) -> Tm76 g a -> Tm76 g a
rec76 = \ t, u, v, tm, var76, lam76, app76, tt76, pair76, fst76, snd76, left76, right76, split76, zero76, suc76, rec76 =>
     rec76 _ _
       (t tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 split76 zero76 suc76 rec76)
       (u tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 split76 zero76 suc76 rec76)
       (v tm var76 lam76 app76 tt76 pair76 fst76 snd76 left76 right76 split76 zero76 suc76 rec76)

v076 : {g:_}->{a:_} -> Tm76 (snoc76 g a) a
v076 = var76 vz76

v176 : {g:_}->{a:_}->{b:_} -> Tm76 (snoc76 (snoc76 g a) b) a
v176 = var76 (vs76 vz76)

v276 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm76 (snoc76 (snoc76 (snoc76 g a) b) c) a
v276 = var76 (vs76 (vs76 vz76))

v376 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm76 (snoc76 (snoc76 (snoc76 (snoc76 g a) b) c) d) a
v376 = var76 (vs76 (vs76 (vs76 vz76)))

tbool76 : Ty76
tbool76 = sum76 top76 top76

ttrue76 : {g:_} -> Tm76 g Main.tbool76
ttrue76 = left76 tt76

tfalse76 : {g:_} -> Tm76 g Main.tbool76
tfalse76 = right76 tt76

ifthenelse76 : {g:_}->{a:_} -> Tm76 g (arr76 Main.tbool76 (arr76 a (arr76 a a)))
ifthenelse76 = lam76 (lam76 (lam76 (split76 v276 (lam76 v276) (lam76 v176))))

times476 : {g:_}->{a:_} -> Tm76 g (arr76 (arr76 a a) (arr76 a a))
times476  = lam76 (lam76 (app76 v176 (app76 v176 (app76 v176 (app76 v176 v076)))))

add76 : {g:_} -> Tm76 g (arr76 Main.nat76 (arr76 Main.nat76 Main.nat76))
add76 = lam76 (rec76 v076
       (lam76 (lam76 (lam76 (suc76 (app76 v176 v076)))))
       (lam76 v076))

mul76 : {g:_} -> Tm76 g (arr76 Main.nat76 (arr76 Main.nat76 Main.nat76))
mul76 = lam76 (rec76 v076
       (lam76 (lam76 (lam76 (app76 (app76 add76 (app76 v176 v076)) v076))))
       (lam76 zero76))

fact76 : {g:_} -> Tm76 g (arr76 Main.nat76 Main.nat76)
fact76 = lam76 (rec76 v076 (lam76 (lam76 (app76 (app76 mul76 (suc76 v176)) v076)))
                 (suc76 zero76))

Ty77 : Type
Ty77 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat77 : Ty77
nat77 = \ _, nat77, _, _, _, _, _ => nat77
top77 : Ty77
top77 = \ _, _, top77, _, _, _, _ => top77
bot77 : Ty77
bot77 = \ _, _, _, bot77, _, _, _ => bot77

arr77 : Ty77-> Ty77-> Ty77
arr77 = \ a, b, ty, nat77, top77, bot77, arr77, prod, sum =>
     arr77 (a ty nat77 top77 bot77 arr77 prod sum) (b ty nat77 top77 bot77 arr77 prod sum)

prod77 : Ty77-> Ty77-> Ty77
prod77 = \ a, b, ty, nat77, top77, bot77, arr77, prod77, sum =>
     prod77 (a ty nat77 top77 bot77 arr77 prod77 sum) (b ty nat77 top77 bot77 arr77 prod77 sum)

sum77 : Ty77-> Ty77-> Ty77
sum77 = \ a, b, ty, nat77, top77, bot77, arr77, prod77, sum77 =>
     sum77 (a ty nat77 top77 bot77 arr77 prod77 sum77) (b ty nat77 top77 bot77 arr77 prod77 sum77)

Con77 : Type
Con77 = (Con77 : Type)
 -> (nil  : Con77)
 -> (snoc : Con77 -> Ty77-> Con77)
 -> Con77

nil77 : Con77
nil77 = \ con, nil77, snoc => nil77

snoc77 : Con77 -> Ty77-> Con77
snoc77 = \ g, a, con, nil77, snoc77 => snoc77 (g con nil77 snoc77) a

Var77 : Con77 -> Ty77-> Type
Var77 = \ g, a =>
    (Var77 : Con77 -> Ty77-> Type)
 -> (vz  : (g:_)->(a:_) -> Var77 (snoc77 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var77 g a -> Var77 (snoc77 g b) a)
 -> Var77 g a

vz77 : {g:_}->{a:_} -> Var77 (snoc77 g a) a
vz77 = \ var, vz77, vs => vz77 _ _

vs77 : {g:_}->{b:_}->{a:_} -> Var77 g a -> Var77 (snoc77 g b) a
vs77 = \ x, var, vz77, vs77 => vs77 _ _ _ (x var vz77 vs77)

Tm77 : Con77 -> Ty77-> Type
Tm77 = \ g, a =>
    (Tm77    : Con77 -> Ty77-> Type)
 -> (var   : (g:_)->(a:_)-> Var77 g a -> Tm77 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm77 (snoc77 g a) b -> Tm77 g (arr77 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm77 g (arr77 a b) -> Tm77 g a -> Tm77 g b)
 -> (tt    : (g:_)-> Tm77 g top77)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm77 g a -> Tm77 g b -> Tm77 g (prod77 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm77 g (prod77 a b) -> Tm77 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm77 g (prod77 a b) -> Tm77 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm77 g a -> Tm77 g (sum77 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm77 g b -> Tm77 g (sum77 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm77 g (sum77 a b) -> Tm77 g (arr77 a c) -> Tm77 g (arr77 b c) -> Tm77 g c)
 -> (zero  : (g:_)-> Tm77 g nat77)
 -> (suc   : (g:_)-> Tm77 g nat77 -> Tm77 g nat77)
 -> (rec   : (g:_)->(a:_) -> Tm77 g nat77 -> Tm77 g (arr77 nat77 (arr77 a a)) -> Tm77 g a -> Tm77 g a)
 -> Tm77 g a

var77 : {g:_}->{a:_} -> Var77 g a -> Tm77 g a
var77 = \ x, tm, var77, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var77 _ _ x

lam77 : {g:_}->{a:_}->{b:_}-> Tm77 (snoc77 g a) b -> Tm77 g (arr77 a b)
lam77 = \ t, tm, var77, lam77, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam77 _ _ _ (t tm var77 lam77 app tt pair fst snd left right split zero suc rec)

app77 : {g:_}->{a:_}->{b:_} -> Tm77 g (arr77 a b) -> Tm77 g a -> Tm77 g b
app77 = \ t, u, tm, var77, lam77, app77, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app77 _ _ _ (t tm var77 lam77 app77 tt pair fst snd left right split zero suc rec)
                (u tm var77 lam77 app77 tt pair fst snd left right split zero suc rec)

tt77 : {g:_} -> Tm77 g Main.top77
tt77 = \ tm, var77, lam77, app77, tt77, pair, fst, snd, left, right, split, zero, suc, rec => tt77 _

pair77 : {g:_}->{a:_}->{b:_} -> Tm77 g a -> Tm77 g b -> Tm77 g (prod77 a b)
pair77 = \ t, u, tm, var77, lam77, app77, tt77, pair77, fst, snd, left, right, split, zero, suc, rec =>
     pair77 _ _ _ (t tm var77 lam77 app77 tt77 pair77 fst snd left right split zero suc rec)
                 (u tm var77 lam77 app77 tt77 pair77 fst snd left right split zero suc rec)

fst77 : {g:_}->{a:_}->{b:_}-> Tm77 g (prod77 a b) -> Tm77 g a
fst77 = \ t, tm, var77, lam77, app77, tt77, pair77, fst77, snd, left, right, split, zero, suc, rec =>
     fst77 _ _ _ (t tm var77 lam77 app77 tt77 pair77 fst77 snd left right split zero suc rec)

snd77 : {g:_}->{a:_}->{b:_} -> Tm77 g (prod77 a b) -> Tm77 g b
snd77 = \ t, tm, var77, lam77, app77, tt77, pair77, fst77, snd77, left, right, split, zero, suc, rec =>
     snd77 _ _ _ (t tm var77 lam77 app77 tt77 pair77 fst77 snd77 left right split zero suc rec)

left77 : {g:_}->{a:_}->{b:_} -> Tm77 g a -> Tm77 g (sum77 a b)
left77 = \ t, tm, var77, lam77, app77, tt77, pair77, fst77, snd77, left77, right, split, zero, suc, rec =>
     left77 _ _ _ (t tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right split zero suc rec)

right77 : {g:_}->{a:_}->{b:_} -> Tm77 g b -> Tm77 g (sum77 a b)
right77 = \ t, tm, var77, lam77, app77, tt77, pair77, fst77, snd77, left77, right77, split, zero, suc, rec =>
     right77 _ _ _ (t tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 split zero suc rec)

split77 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm77 g (sum77 a b) -> Tm77 g (arr77 a c) -> Tm77 g (arr77 b c) -> Tm77 g c
split77 = \ t, u, v, tm, var77, lam77, app77, tt77, pair77, fst77, snd77, left77, right77, split77, zero, suc, rec =>
     split77 _ _ _ _
          (t tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 split77 zero suc rec)
          (u tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 split77 zero suc rec)
          (v tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 split77 zero suc rec)

zero77 : {g:_} -> Tm77 g Main.nat77
zero77 = \ tm, var77, lam77, app77, tt77, pair77, fst77, snd77, left77, right77, split77, zero77, suc, rec =>
  zero77 _

suc77 : {g:_} -> Tm77 g Main.nat77 -> Tm77 g Main.nat77
suc77 = \ t, tm, var77, lam77, app77, tt77, pair77, fst77, snd77, left77, right77, split77, zero77, suc77, rec =>
   suc77 _ (t tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 split77 zero77 suc77 rec)

rec77 : {g:_}->{a:_} -> Tm77 g Main.nat77 -> Tm77 g (arr77 Main.nat77 (arr77 a a)) -> Tm77 g a -> Tm77 g a
rec77 = \ t, u, v, tm, var77, lam77, app77, tt77, pair77, fst77, snd77, left77, right77, split77, zero77, suc77, rec77 =>
     rec77 _ _
       (t tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 split77 zero77 suc77 rec77)
       (u tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 split77 zero77 suc77 rec77)
       (v tm var77 lam77 app77 tt77 pair77 fst77 snd77 left77 right77 split77 zero77 suc77 rec77)

v077 : {g:_}->{a:_} -> Tm77 (snoc77 g a) a
v077 = var77 vz77

v177 : {g:_}->{a:_}->{b:_} -> Tm77 (snoc77 (snoc77 g a) b) a
v177 = var77 (vs77 vz77)

v277 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm77 (snoc77 (snoc77 (snoc77 g a) b) c) a
v277 = var77 (vs77 (vs77 vz77))

v377 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm77 (snoc77 (snoc77 (snoc77 (snoc77 g a) b) c) d) a
v377 = var77 (vs77 (vs77 (vs77 vz77)))

tbool77 : Ty77
tbool77 = sum77 top77 top77

ttrue77 : {g:_} -> Tm77 g Main.tbool77
ttrue77 = left77 tt77

tfalse77 : {g:_} -> Tm77 g Main.tbool77
tfalse77 = right77 tt77

ifthenelse77 : {g:_}->{a:_} -> Tm77 g (arr77 Main.tbool77 (arr77 a (arr77 a a)))
ifthenelse77 = lam77 (lam77 (lam77 (split77 v277 (lam77 v277) (lam77 v177))))

times477 : {g:_}->{a:_} -> Tm77 g (arr77 (arr77 a a) (arr77 a a))
times477  = lam77 (lam77 (app77 v177 (app77 v177 (app77 v177 (app77 v177 v077)))))

add77 : {g:_} -> Tm77 g (arr77 Main.nat77 (arr77 Main.nat77 Main.nat77))
add77 = lam77 (rec77 v077
       (lam77 (lam77 (lam77 (suc77 (app77 v177 v077)))))
       (lam77 v077))

mul77 : {g:_} -> Tm77 g (arr77 Main.nat77 (arr77 Main.nat77 Main.nat77))
mul77 = lam77 (rec77 v077
       (lam77 (lam77 (lam77 (app77 (app77 add77 (app77 v177 v077)) v077))))
       (lam77 zero77))

fact77 : {g:_} -> Tm77 g (arr77 Main.nat77 Main.nat77)
fact77 = lam77 (rec77 v077 (lam77 (lam77 (app77 (app77 mul77 (suc77 v177)) v077)))
                 (suc77 zero77))

Ty78 : Type
Ty78 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat78 : Ty78
nat78 = \ _, nat78, _, _, _, _, _ => nat78
top78 : Ty78
top78 = \ _, _, top78, _, _, _, _ => top78
bot78 : Ty78
bot78 = \ _, _, _, bot78, _, _, _ => bot78

arr78 : Ty78-> Ty78-> Ty78
arr78 = \ a, b, ty, nat78, top78, bot78, arr78, prod, sum =>
     arr78 (a ty nat78 top78 bot78 arr78 prod sum) (b ty nat78 top78 bot78 arr78 prod sum)

prod78 : Ty78-> Ty78-> Ty78
prod78 = \ a, b, ty, nat78, top78, bot78, arr78, prod78, sum =>
     prod78 (a ty nat78 top78 bot78 arr78 prod78 sum) (b ty nat78 top78 bot78 arr78 prod78 sum)

sum78 : Ty78-> Ty78-> Ty78
sum78 = \ a, b, ty, nat78, top78, bot78, arr78, prod78, sum78 =>
     sum78 (a ty nat78 top78 bot78 arr78 prod78 sum78) (b ty nat78 top78 bot78 arr78 prod78 sum78)

Con78 : Type
Con78 = (Con78 : Type)
 -> (nil  : Con78)
 -> (snoc : Con78 -> Ty78-> Con78)
 -> Con78

nil78 : Con78
nil78 = \ con, nil78, snoc => nil78

snoc78 : Con78 -> Ty78-> Con78
snoc78 = \ g, a, con, nil78, snoc78 => snoc78 (g con nil78 snoc78) a

Var78 : Con78 -> Ty78-> Type
Var78 = \ g, a =>
    (Var78 : Con78 -> Ty78-> Type)
 -> (vz  : (g:_)->(a:_) -> Var78 (snoc78 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var78 g a -> Var78 (snoc78 g b) a)
 -> Var78 g a

vz78 : {g:_}->{a:_} -> Var78 (snoc78 g a) a
vz78 = \ var, vz78, vs => vz78 _ _

vs78 : {g:_}->{b:_}->{a:_} -> Var78 g a -> Var78 (snoc78 g b) a
vs78 = \ x, var, vz78, vs78 => vs78 _ _ _ (x var vz78 vs78)

Tm78 : Con78 -> Ty78-> Type
Tm78 = \ g, a =>
    (Tm78    : Con78 -> Ty78-> Type)
 -> (var   : (g:_)->(a:_)-> Var78 g a -> Tm78 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm78 (snoc78 g a) b -> Tm78 g (arr78 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm78 g (arr78 a b) -> Tm78 g a -> Tm78 g b)
 -> (tt    : (g:_)-> Tm78 g top78)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm78 g a -> Tm78 g b -> Tm78 g (prod78 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm78 g (prod78 a b) -> Tm78 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm78 g (prod78 a b) -> Tm78 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm78 g a -> Tm78 g (sum78 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm78 g b -> Tm78 g (sum78 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm78 g (sum78 a b) -> Tm78 g (arr78 a c) -> Tm78 g (arr78 b c) -> Tm78 g c)
 -> (zero  : (g:_)-> Tm78 g nat78)
 -> (suc   : (g:_)-> Tm78 g nat78 -> Tm78 g nat78)
 -> (rec   : (g:_)->(a:_) -> Tm78 g nat78 -> Tm78 g (arr78 nat78 (arr78 a a)) -> Tm78 g a -> Tm78 g a)
 -> Tm78 g a

var78 : {g:_}->{a:_} -> Var78 g a -> Tm78 g a
var78 = \ x, tm, var78, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var78 _ _ x

lam78 : {g:_}->{a:_}->{b:_}-> Tm78 (snoc78 g a) b -> Tm78 g (arr78 a b)
lam78 = \ t, tm, var78, lam78, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam78 _ _ _ (t tm var78 lam78 app tt pair fst snd left right split zero suc rec)

app78 : {g:_}->{a:_}->{b:_} -> Tm78 g (arr78 a b) -> Tm78 g a -> Tm78 g b
app78 = \ t, u, tm, var78, lam78, app78, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app78 _ _ _ (t tm var78 lam78 app78 tt pair fst snd left right split zero suc rec)
                (u tm var78 lam78 app78 tt pair fst snd left right split zero suc rec)

tt78 : {g:_} -> Tm78 g Main.top78
tt78 = \ tm, var78, lam78, app78, tt78, pair, fst, snd, left, right, split, zero, suc, rec => tt78 _

pair78 : {g:_}->{a:_}->{b:_} -> Tm78 g a -> Tm78 g b -> Tm78 g (prod78 a b)
pair78 = \ t, u, tm, var78, lam78, app78, tt78, pair78, fst, snd, left, right, split, zero, suc, rec =>
     pair78 _ _ _ (t tm var78 lam78 app78 tt78 pair78 fst snd left right split zero suc rec)
                 (u tm var78 lam78 app78 tt78 pair78 fst snd left right split zero suc rec)

fst78 : {g:_}->{a:_}->{b:_}-> Tm78 g (prod78 a b) -> Tm78 g a
fst78 = \ t, tm, var78, lam78, app78, tt78, pair78, fst78, snd, left, right, split, zero, suc, rec =>
     fst78 _ _ _ (t tm var78 lam78 app78 tt78 pair78 fst78 snd left right split zero suc rec)

snd78 : {g:_}->{a:_}->{b:_} -> Tm78 g (prod78 a b) -> Tm78 g b
snd78 = \ t, tm, var78, lam78, app78, tt78, pair78, fst78, snd78, left, right, split, zero, suc, rec =>
     snd78 _ _ _ (t tm var78 lam78 app78 tt78 pair78 fst78 snd78 left right split zero suc rec)

left78 : {g:_}->{a:_}->{b:_} -> Tm78 g a -> Tm78 g (sum78 a b)
left78 = \ t, tm, var78, lam78, app78, tt78, pair78, fst78, snd78, left78, right, split, zero, suc, rec =>
     left78 _ _ _ (t tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right split zero suc rec)

right78 : {g:_}->{a:_}->{b:_} -> Tm78 g b -> Tm78 g (sum78 a b)
right78 = \ t, tm, var78, lam78, app78, tt78, pair78, fst78, snd78, left78, right78, split, zero, suc, rec =>
     right78 _ _ _ (t tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 split zero suc rec)

split78 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm78 g (sum78 a b) -> Tm78 g (arr78 a c) -> Tm78 g (arr78 b c) -> Tm78 g c
split78 = \ t, u, v, tm, var78, lam78, app78, tt78, pair78, fst78, snd78, left78, right78, split78, zero, suc, rec =>
     split78 _ _ _ _
          (t tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 split78 zero suc rec)
          (u tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 split78 zero suc rec)
          (v tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 split78 zero suc rec)

zero78 : {g:_} -> Tm78 g Main.nat78
zero78 = \ tm, var78, lam78, app78, tt78, pair78, fst78, snd78, left78, right78, split78, zero78, suc, rec =>
  zero78 _

suc78 : {g:_} -> Tm78 g Main.nat78 -> Tm78 g Main.nat78
suc78 = \ t, tm, var78, lam78, app78, tt78, pair78, fst78, snd78, left78, right78, split78, zero78, suc78, rec =>
   suc78 _ (t tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 split78 zero78 suc78 rec)

rec78 : {g:_}->{a:_} -> Tm78 g Main.nat78 -> Tm78 g (arr78 Main.nat78 (arr78 a a)) -> Tm78 g a -> Tm78 g a
rec78 = \ t, u, v, tm, var78, lam78, app78, tt78, pair78, fst78, snd78, left78, right78, split78, zero78, suc78, rec78 =>
     rec78 _ _
       (t tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 split78 zero78 suc78 rec78)
       (u tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 split78 zero78 suc78 rec78)
       (v tm var78 lam78 app78 tt78 pair78 fst78 snd78 left78 right78 split78 zero78 suc78 rec78)

v078 : {g:_}->{a:_} -> Tm78 (snoc78 g a) a
v078 = var78 vz78

v178 : {g:_}->{a:_}->{b:_} -> Tm78 (snoc78 (snoc78 g a) b) a
v178 = var78 (vs78 vz78)

v278 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm78 (snoc78 (snoc78 (snoc78 g a) b) c) a
v278 = var78 (vs78 (vs78 vz78))

v378 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm78 (snoc78 (snoc78 (snoc78 (snoc78 g a) b) c) d) a
v378 = var78 (vs78 (vs78 (vs78 vz78)))

tbool78 : Ty78
tbool78 = sum78 top78 top78

ttrue78 : {g:_} -> Tm78 g Main.tbool78
ttrue78 = left78 tt78

tfalse78 : {g:_} -> Tm78 g Main.tbool78
tfalse78 = right78 tt78

ifthenelse78 : {g:_}->{a:_} -> Tm78 g (arr78 Main.tbool78 (arr78 a (arr78 a a)))
ifthenelse78 = lam78 (lam78 (lam78 (split78 v278 (lam78 v278) (lam78 v178))))

times478 : {g:_}->{a:_} -> Tm78 g (arr78 (arr78 a a) (arr78 a a))
times478  = lam78 (lam78 (app78 v178 (app78 v178 (app78 v178 (app78 v178 v078)))))

add78 : {g:_} -> Tm78 g (arr78 Main.nat78 (arr78 Main.nat78 Main.nat78))
add78 = lam78 (rec78 v078
       (lam78 (lam78 (lam78 (suc78 (app78 v178 v078)))))
       (lam78 v078))

mul78 : {g:_} -> Tm78 g (arr78 Main.nat78 (arr78 Main.nat78 Main.nat78))
mul78 = lam78 (rec78 v078
       (lam78 (lam78 (lam78 (app78 (app78 add78 (app78 v178 v078)) v078))))
       (lam78 zero78))

fact78 : {g:_} -> Tm78 g (arr78 Main.nat78 Main.nat78)
fact78 = lam78 (rec78 v078 (lam78 (lam78 (app78 (app78 mul78 (suc78 v178)) v078)))
                 (suc78 zero78))

Ty79 : Type
Ty79 = (Ty   : Type)
 ->  (nat  : Ty)
 ->  (top  : Ty)
 ->  (bot  : Ty)
 ->  (arr  : Ty -> Ty -> Ty)
 ->  (prod : Ty -> Ty -> Ty)
 ->  (sum  : Ty -> Ty -> Ty)
 ->  Ty

nat79 : Ty79
nat79 = \ _, nat79, _, _, _, _, _ => nat79
top79 : Ty79
top79 = \ _, _, top79, _, _, _, _ => top79
bot79 : Ty79
bot79 = \ _, _, _, bot79, _, _, _ => bot79

arr79 : Ty79-> Ty79-> Ty79
arr79 = \ a, b, ty, nat79, top79, bot79, arr79, prod, sum =>
     arr79 (a ty nat79 top79 bot79 arr79 prod sum) (b ty nat79 top79 bot79 arr79 prod sum)

prod79 : Ty79-> Ty79-> Ty79
prod79 = \ a, b, ty, nat79, top79, bot79, arr79, prod79, sum =>
     prod79 (a ty nat79 top79 bot79 arr79 prod79 sum) (b ty nat79 top79 bot79 arr79 prod79 sum)

sum79 : Ty79-> Ty79-> Ty79
sum79 = \ a, b, ty, nat79, top79, bot79, arr79, prod79, sum79 =>
     sum79 (a ty nat79 top79 bot79 arr79 prod79 sum79) (b ty nat79 top79 bot79 arr79 prod79 sum79)

Con79 : Type
Con79 = (Con79 : Type)
 -> (nil  : Con79)
 -> (snoc : Con79 -> Ty79-> Con79)
 -> Con79

nil79 : Con79
nil79 = \ con, nil79, snoc => nil79

snoc79 : Con79 -> Ty79-> Con79
snoc79 = \ g, a, con, nil79, snoc79 => snoc79 (g con nil79 snoc79) a

Var79 : Con79 -> Ty79-> Type
Var79 = \ g, a =>
    (Var79 : Con79 -> Ty79-> Type)
 -> (vz  : (g:_)->(a:_) -> Var79 (snoc79 g a) a)
 -> (vs  : (g:_)->(b:_)->(a:_) -> Var79 g a -> Var79 (snoc79 g b) a)
 -> Var79 g a

vz79 : {g:_}->{a:_} -> Var79 (snoc79 g a) a
vz79 = \ var, vz79, vs => vz79 _ _

vs79 : {g:_}->{b:_}->{a:_} -> Var79 g a -> Var79 (snoc79 g b) a
vs79 = \ x, var, vz79, vs79 => vs79 _ _ _ (x var vz79 vs79)

Tm79 : Con79 -> Ty79-> Type
Tm79 = \ g, a =>
    (Tm79    : Con79 -> Ty79-> Type)
 -> (var   : (g:_)->(a:_)-> Var79 g a -> Tm79 g a)
 -> (lam   : (g:_)->(a:_)->(b:_) -> Tm79 (snoc79 g a) b -> Tm79 g (arr79 a b))
 -> (app   : (g:_)->(a:_)->(b:_) -> Tm79 g (arr79 a b) -> Tm79 g a -> Tm79 g b)
 -> (tt    : (g:_)-> Tm79 g top79)
 -> (pair  : (g:_)->(a:_)->(b:_) -> Tm79 g a -> Tm79 g b -> Tm79 g (prod79 a b))
 -> (fst   : (g:_)->(a:_)->(b:_) -> Tm79 g (prod79 a b) -> Tm79 g a)
 -> (snd   : (g:_)->(a:_)->(b:_) -> Tm79 g (prod79 a b) -> Tm79 g b)
 -> (left  : (g:_)->(a:_)->(b:_) -> Tm79 g a -> Tm79 g (sum79 a b))
 -> (right : (g:_)->(a:_)->(b:_) -> Tm79 g b -> Tm79 g (sum79 a b))
 -> (split : (g:_)->(a:_)->(b:_)-> (c:_) -> Tm79 g (sum79 a b) -> Tm79 g (arr79 a c) -> Tm79 g (arr79 b c) -> Tm79 g c)
 -> (zero  : (g:_)-> Tm79 g nat79)
 -> (suc   : (g:_)-> Tm79 g nat79 -> Tm79 g nat79)
 -> (rec   : (g:_)->(a:_) -> Tm79 g nat79 -> Tm79 g (arr79 nat79 (arr79 a a)) -> Tm79 g a -> Tm79 g a)
 -> Tm79 g a

var79 : {g:_}->{a:_} -> Var79 g a -> Tm79 g a
var79 = \ x, tm, var79, lam, app, tt, pair, fst, snd, left, right, split, zero, suc, rec => var79 _ _ x

lam79 : {g:_}->{a:_}->{b:_}-> Tm79 (snoc79 g a) b -> Tm79 g (arr79 a b)
lam79 = \ t, tm, var79, lam79, app, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     lam79 _ _ _ (t tm var79 lam79 app tt pair fst snd left right split zero suc rec)

app79 : {g:_}->{a:_}->{b:_} -> Tm79 g (arr79 a b) -> Tm79 g a -> Tm79 g b
app79 = \ t, u, tm, var79, lam79, app79, tt, pair, fst, snd, left, right, split, zero, suc, rec =>
     app79 _ _ _ (t tm var79 lam79 app79 tt pair fst snd left right split zero suc rec)
                (u tm var79 lam79 app79 tt pair fst snd left right split zero suc rec)

tt79 : {g:_} -> Tm79 g Main.top79
tt79 = \ tm, var79, lam79, app79, tt79, pair, fst, snd, left, right, split, zero, suc, rec => tt79 _

pair79 : {g:_}->{a:_}->{b:_} -> Tm79 g a -> Tm79 g b -> Tm79 g (prod79 a b)
pair79 = \ t, u, tm, var79, lam79, app79, tt79, pair79, fst, snd, left, right, split, zero, suc, rec =>
     pair79 _ _ _ (t tm var79 lam79 app79 tt79 pair79 fst snd left right split zero suc rec)
                 (u tm var79 lam79 app79 tt79 pair79 fst snd left right split zero suc rec)

fst79 : {g:_}->{a:_}->{b:_}-> Tm79 g (prod79 a b) -> Tm79 g a
fst79 = \ t, tm, var79, lam79, app79, tt79, pair79, fst79, snd, left, right, split, zero, suc, rec =>
     fst79 _ _ _ (t tm var79 lam79 app79 tt79 pair79 fst79 snd left right split zero suc rec)

snd79 : {g:_}->{a:_}->{b:_} -> Tm79 g (prod79 a b) -> Tm79 g b
snd79 = \ t, tm, var79, lam79, app79, tt79, pair79, fst79, snd79, left, right, split, zero, suc, rec =>
     snd79 _ _ _ (t tm var79 lam79 app79 tt79 pair79 fst79 snd79 left right split zero suc rec)

left79 : {g:_}->{a:_}->{b:_} -> Tm79 g a -> Tm79 g (sum79 a b)
left79 = \ t, tm, var79, lam79, app79, tt79, pair79, fst79, snd79, left79, right, split, zero, suc, rec =>
     left79 _ _ _ (t tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right split zero suc rec)

right79 : {g:_}->{a:_}->{b:_} -> Tm79 g b -> Tm79 g (sum79 a b)
right79 = \ t, tm, var79, lam79, app79, tt79, pair79, fst79, snd79, left79, right79, split, zero, suc, rec =>
     right79 _ _ _ (t tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 split zero suc rec)

split79 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm79 g (sum79 a b) -> Tm79 g (arr79 a c) -> Tm79 g (arr79 b c) -> Tm79 g c
split79 = \ t, u, v, tm, var79, lam79, app79, tt79, pair79, fst79, snd79, left79, right79, split79, zero, suc, rec =>
     split79 _ _ _ _
          (t tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 split79 zero suc rec)
          (u tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 split79 zero suc rec)
          (v tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 split79 zero suc rec)

zero79 : {g:_} -> Tm79 g Main.nat79
zero79 = \ tm, var79, lam79, app79, tt79, pair79, fst79, snd79, left79, right79, split79, zero79, suc, rec =>
  zero79 _

suc79 : {g:_} -> Tm79 g Main.nat79 -> Tm79 g Main.nat79
suc79 = \ t, tm, var79, lam79, app79, tt79, pair79, fst79, snd79, left79, right79, split79, zero79, suc79, rec =>
   suc79 _ (t tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 split79 zero79 suc79 rec)

rec79 : {g:_}->{a:_} -> Tm79 g Main.nat79 -> Tm79 g (arr79 Main.nat79 (arr79 a a)) -> Tm79 g a -> Tm79 g a
rec79 = \ t, u, v, tm, var79, lam79, app79, tt79, pair79, fst79, snd79, left79, right79, split79, zero79, suc79, rec79 =>
     rec79 _ _
       (t tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 split79 zero79 suc79 rec79)
       (u tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 split79 zero79 suc79 rec79)
       (v tm var79 lam79 app79 tt79 pair79 fst79 snd79 left79 right79 split79 zero79 suc79 rec79)

v079 : {g:_}->{a:_} -> Tm79 (snoc79 g a) a
v079 = var79 vz79

v179 : {g:_}->{a:_}->{b:_} -> Tm79 (snoc79 (snoc79 g a) b) a
v179 = var79 (vs79 vz79)

v279 : {g:_}->{a:_}->{b:_}->{c:_} -> Tm79 (snoc79 (snoc79 (snoc79 g a) b) c) a
v279 = var79 (vs79 (vs79 vz79))

v379 : {g:_}->{a:_}->{b:_}->{c:_}->{d:_} -> Tm79 (snoc79 (snoc79 (snoc79 (snoc79 g a) b) c) d) a
v379 = var79 (vs79 (vs79 (vs79 vz79)))

tbool79 : Ty79
tbool79 = sum79 top79 top79

ttrue79 : {g:_} -> Tm79 g Main.tbool79
ttrue79 = left79 tt79

tfalse79 : {g:_} -> Tm79 g Main.tbool79
tfalse79 = right79 tt79

ifthenelse79 : {g:_}->{a:_} -> Tm79 g (arr79 Main.tbool79 (arr79 a (arr79 a a)))
ifthenelse79 = lam79 (lam79 (lam79 (split79 v279 (lam79 v279) (lam79 v179))))

times479 : {g:_}->{a:_} -> Tm79 g (arr79 (arr79 a a) (arr79 a a))
times479  = lam79 (lam79 (app79 v179 (app79 v179 (app79 v179 (app79 v179 v079)))))

add79 : {g:_} -> Tm79 g (arr79 Main.nat79 (arr79 Main.nat79 Main.nat79))
add79 = lam79 (rec79 v079
       (lam79 (lam79 (lam79 (suc79 (app79 v179 v079)))))
       (lam79 v079))

mul79 : {g:_} -> Tm79 g (arr79 Main.nat79 (arr79 Main.nat79 Main.nat79))
mul79 = lam79 (rec79 v079
       (lam79 (lam79 (lam79 (app79 (app79 add79 (app79 v179 v079)) v079))))
       (lam79 zero79))

fact79 : {g:_} -> Tm79 g (arr79 Main.nat79 Main.nat79)
fact79 = lam79 (rec79 v079 (lam79 (lam79 (app79 (app79 mul79 (suc79 v179)) v079)))
                 (suc79 zero79))
