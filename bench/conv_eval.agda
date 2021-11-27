{-# OPTIONS --type-in-type #-}

data IBool : Set where
  itrue ifalse : IBool

Bool : Set; Bool
 = (B : Set) → B → B → B

toIBool : Bool → IBool
toIBool b = b _ itrue ifalse

true : Bool; true
 = λ B t f → t

and : Bool → Bool → Bool; and
 = λ a b B t f → a B (b B t f) f

Nat : Set; Nat
 = (n : Set) → (n → n) → n → n

add : Nat → Nat → Nat; add
 = λ a b n s z → a n s (b n s z)

mul : Nat → Nat → Nat; mul
 = λ a b n s → a n (b n s)

suc : Nat → Nat; suc
 = λ a n s z → s (a n s z)

Eq : {A : Set} → A → A → Set
Eq {A} x y = (P : A → Set) → P x → P y

refl : {A : Set}{x : A} → Eq {A} x x; refl
 = λ P px → px

n2  : Nat; n2 = λ N s z → s (s z)
n3  : Nat; n3 = λ N s z → s (s (s z))
n4  : Nat; n4 = λ N s z → s (s (s (s z)))
n5  : Nat; n5 = λ N s z → s (s (s (s (s z))))
n10    = mul n2 n5
n10b   = mul n5 n2
n15    = add n10  n5
n15b   = add n10b n5
n18    = add n15  n3
n18b   = add n15b n3
n19    = add n15  n4
n19b   = add n15b n4
n20    = mul n2 n10
n20b   = mul n2 n10b
n21    = suc n20
n21b   = suc n20b
n22    = suc n21
n22b   = suc n21b
n23    = suc n22
n23b   = suc n22b
n100   = mul n10   n10
n100b  = mul n10b  n10b
n10k   = mul n100  n100
n10kb  = mul n100b n100b
n100k  = mul n10k  n10
n100kb = mul n10kb n10b
n1M    = mul n10k  n100
n1Mb   = mul n10kb n100b
n5M    = mul n1M   n5
n5Mb   = mul n1Mb  n5
n10M   = mul n5M   n2
n10Mb  = mul n5Mb  n2

Tree : Set; Tree = (T : Set) → (T → T → T) → T → T
leaf : Tree; leaf = λ T n l → l
node : Tree → Tree → Tree; node = λ t1 t2 T n l → n (t1 T n l) (t2 T n l)

fullTree : Nat → Tree; fullTree
 = λ n → n Tree (λ t → node t t) leaf

-- full tree with given trees at bottom level
fullTreeWithLeaf : Tree → Nat → Tree; fullTreeWithLeaf
 = λ bottom n → n Tree (λ t → node t t) bottom

forceTree : Tree → Bool; forceTree
 = λ t → t Bool and true

t15  = fullTree n15
t15b = fullTree n15b
t18  = fullTree n18
t18b = fullTree n18b
t19  = fullTree n19
t19b = fullTree n19b
t20  = fullTree n20
t20b = fullTree n20b
t21  = fullTree n21
t21b = fullTree n21b
t22  = fullTree n22
t22b = fullTree n22b
t23  = fullTree n23
t23b = fullTree n23b

-- Nat conversion
--------------------------------------------------------------------------------

-- convn1M : Eq n1M n1Mb; convn1M = refl     -- 2 s
-- convn5M : Eq n5M n5Mb; convn5M = refl     -- 10.4s s
-- convn10M : Eq n10M n10Mb; convn10M = refl -- 19s

-- Full tree conversion
--------------------------------------------------------------------------------

-- convt15  : Eq t15  t15b; convt15  = refl -- 15 ms
-- convt18  : Eq t18  t18b; convt18  = refl -- 20 ms
-- convt19  : Eq t19  t19b; convt19  = refl -- 20 ms
-- convt20  : Eq t20  t20b; convt20  = refl -- 1.7 s
-- convt21  : Eq t21  t21b; convt21  = refl -- 3.4 s
-- convt22  : Eq t22  t22b; convt22  = refl -- 6.6 s
-- convt23  : Eq t23  t23b; convt23  = refl -- 13.1 s

-- Full meta-containing tree conversion
--------------------------------------------------------------------------------

-- convmt15 : Eq t15  (fullTreeWithLeaf _ n15 ); convmt15 = refl -- 770 ms
-- convmt18 : Eq t18  (fullTreeWithLeaf _ n18 ); convmt18 = refl -- 6.3 s
-- convmt19 : Eq t19  (fullTreeWithLeaf _ n19 ); convmt19 = refl -- 12.5 s
-- convmt20 : Eq t20  (fullTreeWithLeaf _ n20 ); convmt20 = refl -- 24.8 s
-- convmt21 : Eq t21  (fullTreeWithLeaf _ n21 ); convmt21 = refl
-- convmt22 : Eq t22  (fullTreeWithLeaf _ n22 ); convmt22 = refl
-- convmt23 : Eq t23  (fullTreeWithLeaf _ n23 ); convmt23 = refl

-- Full tree forcing
--------------------------------------------------------------------------------

-- forcet15 : Eq (toIBool (forceTree t15)) itrue; forcet15 = refl -- 50 ms
-- forcet18 : Eq (toIBool (forceTree t18)) itrue; forcet18 = refl -- 450 ms
-- forcet19 : Eq (toIBool (forceTree t19)) itrue; forcet19 = refl -- 900 ms
-- forcet20 : Eq (toIBool (forceTree t20)) itrue; forcet20 = refl -- 1.75 s
-- forcet21 : Eq (toIBool (forceTree t21)) itrue; forcet21 = refl -- 3.5 s
-- forcet22 : Eq (toIBool (forceTree t22)) itrue; forcet22 = refl -- 7.5 s
-- forcet23 : Eq (toIBool (forceTree t23)) itrue; forcet23 = refl -- 15 s
