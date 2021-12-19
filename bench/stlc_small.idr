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
