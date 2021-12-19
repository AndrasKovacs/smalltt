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
