{-# OPTIONS --type-in-type #-}

U = Set

id  : {A : Set} → A → A
id = λ x → x

id2 : ∀ {A} → A → A
id2 = id id

id3 : ∀ {A} → A → A
id3 = λ x → id x

id4 : {A : Set} -> A -> A
id4 = \x -> x

the : (A : Set) → A → A
the = λ _ x → x

constTy = {A B : Set} → A → B → A

const : constTy
const = λ x y → x

constU = const {Set}

namedArgTest  = const {B = U} U
namedArgTest2 = the constTy (λ x y → x) {B = U} U


-- Church bools
--------------------------------------------------------------------------------
Bool = (B : U) → B → B → B

true  : Bool
true = λ _ t f → t

false : Bool
false = λ _ t f  → f

Nat : U
Nat = (n : U) → (n → n) → n → n


-- Church natural numbers
--------------------------------------------------------------------------------

zero : Nat
zero = λ n s z → z

suc : Nat → Nat
suc = λ a n s z → s (a n s z)

n2 : Nat
n2 = λ n s z → s (s z)

n5 : Nat
n5 = λ n s z → s (s (s (s (s z))))

mul : Nat → Nat → Nat
mul = λ a b n s z → a n (b n s) z

add : Nat → Nat → Nat
add = λ a b n s z → a n s (b n s z)

n10    = mul n2    n5
n10b   = mul n5    n2
n100   = mul n10   n10
n100b  = mul n10b  n10b
n10k   = mul n100  n100
n10kb  = mul n100b n100b
n100k  = mul n10k  n10
n100kb = mul n10kb n10b
n1M    = mul n10k  n100
n1Mb   = mul n10kb n100b
n10M   = mul n1M   n10
n10Mb  = mul n1Mb  n10b
n100M  = mul n10M  n10
n200M  = mul n2    n100M

-- Church lists
--------------------------------------------------------------------------------

List : U → U
List = λ a → (l : U) → (a → l → l) → l → l

lnil  : ∀{a} → List a
lnil = λ l c n → n

lcons : ∀{a} → a → List a → List a
lcons = λ a as l c n → c a (as l c n)

list1 = lcons true (lcons false (lcons false lnil))

map : ∀{a b} → (a → b) → List a → List b
map = λ f as l c → as l (λ a → c (f a))


-- Church vectors
--------------------------------------------------------------------------------

Vec : U → Nat → U
Vec = λ a n → (V : Nat → U) → V zero → (∀{n} → a → V n → V (suc n)) → V n

vnil : ∀{a} → Vec a zero
vnil = λ V n c → n

vcons : ∀{a n} → a → Vec a n → Vec a (suc n)
vcons = λ a as V n c → c a (as V n c)

vec1 = vcons true (vcons false (vcons true vnil))


-- vecStress =
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true (vcons true (vcons true (vcons true (vcons true
--    (vcons true (vcons true
--    vnil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--        ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--        ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--        ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--        ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--        ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--        ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--        ))))))))))))))))))))))))))))))))))))


-- Leibniz (Church) propositional equality, useful for testing conversion.
--------------------------------------------------------------------------------

Eq : ∀{A : U} → A → A → U
Eq {A} = λ x y → (P : A → U) → P x → P y

refl : ∀{A}{x : A} → Eq x x
refl = λ P px → px

trans : ∀{A}{x y z : A} → Eq x y → Eq y z → Eq x z
trans = λ p q → q _ p

sym : ∀{A}{x y : A} → Eq x y → Eq y x
sym {_}{x}{y} = λ p → p (λ y → Eq y x) refl

ap : ∀{A B}(f : A → B){x y : A} → Eq x y → Eq (f x) (f y)
ap = λ f {x}{y} p → p (λ y → Eq (f x) (f y)) refl


-- Pairs, Top, Bot
--------------------------------------------------------------------------------

Pair : U → U → U
Pair = λ A B → (Pair : U)(pair : A → B → Pair) → Pair

pair : ∀{A B} → A → B → Pair A B
pair = λ a b Pair pair → pair a b

proj1 : ∀{A B} → Pair A B → A
proj1 = λ p → p _ (λ x y → x)

proj2 : ∀{A B} → Pair A B → B
proj2 = λ p → p _ (λ x y → y)

Top : U
Top = (Top : U)(tt : Top) → Top

tt : Top
tt = λ Top tt → tt

Bot : U
Bot = (Bot : U) → Bot


-- Dependent function composition
--------------------------------------------------------------------------------

comp :
  ∀ {A : U}
  {B : A → U}
  {C : ∀{a} → B a → U}
  (f : ∀{a}(b : B a) → C b)
  (g : (a : A) → B a)
  (x : A)
  → C (g x)
comp = λ f g a → f (g a)

compTest1 : Nat → Nat
compTest1 = comp suc suc

compTest2 : ∀{m A} → A → Vec A m → Vec A (suc (suc m))
compTest2 = λ a → comp (vcons a) (vcons a)

-- Some stress tests
--------------------------------------------------------------------------------

nfun : Nat → U
nfun n = n U (λ A → U → A) U

-- OK
synEqTest1 : Eq n1M n1M
synEqTest1 = refl

-- fail
-- synEqTest2 : nfun n10k → nfun n10k
-- synEqTest2 = λ x → x

-- OK
idStress : ∀{A} → A → A
idStress =
   id id id id id id id id id id id id id id id id id id id id
   id id id id id id id id id id id id id id id id id id id id


-- fail
-- pairStress : Top
-- pairStress =
--    let x0  = pair tt tt
--        x1  = pair x0  x0
--        x2  = pair x1  x1
--        x3  = pair x2  x2
--        x4  = pair x3  x3
--        x5  = pair x4  x4
--        x6  = pair x5  x5
--        x7  = pair x6  x6
--        x8  = pair x7  x7
--        x9  = pair x8  x8
--        x10 = pair x9  x9
--        x11 = pair x10 x10
--        x12 = pair x11 x11
--        x13 = pair x12 x12
--        x14 = pair x13 x13
--        x15 = pair x14 x14
--        x16 = pair x15 x15
--        x17 = pair x16 x16
--        x18 = pair x17 x17
--        x19 = pair x18 x18
--        x20 = pair x19 x19
--    in tt

forceNat : Nat → U
forceNat n = n U (λ b → b) U

computeTest = forceNat n10M


-- Conversion checking tests
--------------------------------------------------------------------------------

-- conv100k : Eq n100k n100kb
-- conv100k = refl

-- conv1M : Eq n1M n1Mb
-- conv1M = refl

-- OOM
-- conv10M : Eq n10M n1M0b
-- conv10M = refl

-- convNfun1M : Eq (nfun n1M) (nfun n1Mb)
-- convNfun1M = refl

conv10kmeta : Eq n10k (add n10kb _)
conv10kmeta = refl

-- OOM
-- conv1Mmeta : Eq n1M (add n1Mb _)
-- conv1Mmeta = refl

-- Testing laziness
--------------------------------------------------------------------------------

-- normalized instantly
lazyU = const U (forceNat n10M)


-- Church-coded simply typed lambda calculus
--------------------------------------------------------------------------------

Ty : U
Ty
 = (Ty  : U)
   (ι   : Ty)
   (fun : Ty → Ty → Ty)
 → Ty

ι : Ty
ι
 = λ _ ι _ → ι

fun : Ty → Ty → Ty
fun
 = λ A B Ty ι fun → fun (A Ty ι fun) (B Ty ι fun)

Con : U
Con
 = (Con : U)
   (nil  : Con)
   (cons : Con → Ty → Con)
 → Con

nil : Con
nil
 = λ Con nil cons → nil

cons : Con → Ty → Con
cons
 = λ Γ A Con nil cons → cons (Γ Con nil cons) A

Var : Con → Ty → U
Var
 = λ Γ A →
   (Var : Con → Ty → U)
   (vz  : ∀{Γ A} → Var (cons Γ A) A)
   (vs  : ∀{Γ B A} → Var Γ A → Var (cons Γ B) A)
 → Var Γ A

vz : ∀{Γ A} → Var (cons Γ A) A
vz
 = λ Var vz vs → vz

vs : ∀{Γ B A} → Var Γ A → Var (cons Γ B) A
vs
 = λ x Var vz vs → vs (x Var vz vs)

Tm : Con → Ty → U
Tm
 = λ Γ A →
   (Tm  : Con → Ty → U)
   (var : ∀{Γ A} → Var Γ A → Tm Γ A)
   (lam : ∀{Γ A B} → Tm (cons Γ A) B → Tm Γ (fun A B))
   (app : ∀{Γ A B} → Tm Γ (fun A B) → Tm Γ A → Tm Γ B)
 → Tm Γ A

var : ∀{Γ A} → Var Γ A → Tm Γ A
var
 = λ x Tm var lam app → var x

lam : ∀{Γ A B} → Tm (cons Γ A) B → Tm Γ (fun A B)
lam
 = λ t Tm var lam app → lam (t Tm var lam app)

app : ∀{Γ A B} → Tm Γ (fun A B) → Tm Γ A → Tm Γ B
app
 = λ t u Tm var lam app → app (t Tm var lam app) (u Tm var lam app)


-- Well-typed interpreter for Church-coded STLC
--------------------------------------------------------------------------------

EvalTy : Ty → U
EvalTy
 = λ A → A _ Bot (λ A B → A → B)

EvalCon : Con → U
EvalCon
 = λ Γ → Γ _ Top (λ Δ A → Pair Δ (EvalTy A))

EvalVar : ∀{Γ A} → Var Γ A → EvalCon Γ → EvalTy A
EvalVar
 = λ x → x (λ Γ A → EvalCon Γ → EvalTy A)
           (λ env → proj2 env)
           (λ rec env → rec (proj1 env))

EvalTm : ∀{Γ A} → Tm Γ A → EvalCon Γ → EvalTy A
EvalTm
 = λ t → t (λ Γ A → EvalCon Γ → EvalTy A)
          EvalVar
          (λ t env α → t (pair env α))
          (λ t u env → t env (u env))

-- Large embedded STLC term
--------------------------------------------------------------------------------

-- t1 : Tm nil (fun (fun ι ι) (fun ι ι))
-- t1
--  = lam (lam (
--       app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz)) (app (var (vs vz))
--      (var vz))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--      )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--      )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
--      ))))))))))))))))))))))))))))))))))))))
--      ))

-- -- test evaluation
-- evalTest = EvalTm t1 tt
