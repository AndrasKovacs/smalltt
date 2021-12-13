
-- Notes: some kind of memoization is likely up to tree 1M conversion
--        at 2M it slows down 100x

set_option maxHeartbeats 10000000
set_option maxRecDepth   10000000

universe u v

def CBool := ∀ (B : Type u), B → B → B
def ctrue : CBool := λ B t f => t
def cand  : CBool → CBool → CBool := λ a b B t f => a B (b B t f) f

def CEq {A : Type u}(x y : A) := ∀ (P : A → Type v), P x → P y
def crefl {A}{x:A} : CEq x x := λ P px => px

def CNat := ∀ (N : Type u), (N → N) → N → N
def add : CNat → CNat → CNat := λ a b n s z => a n s (b n s z)
def mul : CNat → CNat → CNat := λ a b N s z => a N (b N s) z
def suc : CNat → CNat := λ a N s z => s (a N s z)
def n2  : CNat := λ N s z => s (s z)
def n3  : CNat := λ N s z => s (s (s z))
def n4  : CNat := λ N s z => s (s (s (s z)))
def n5  : CNat := λ N s z => s (s (s (s (s z))))
def n10    := mul n2 n5
def n10b   := mul n5 n2
def n15    := add n10  n5
def n15b   := add n10b n5
def n18    := add n15  n3
def n18b   := add n15b n3
def n19    := add n15  n4
def n19b   := add n15b n4
def n20    := mul n2 n10
def n20b   := mul n2 n10b
def n21    := suc n20
def n21b   := suc n20b
def n22    := suc n21
def n22b   := suc n21b
def n23    := suc n22
def n23b   := suc n22b
def n100   := mul n10   n10
def n100b  := mul n10b  n10b
def n10k   := mul n100  n100
def n10kb  := mul n100b n100b
def n100k  := mul n10k  n10
def n100kb := mul n10kb n10b
def n1M    := mul n10k  n100
def n1Mb   := mul n10kb n100b
def n5M    := mul n1M   n5
def n5Mb   := mul n1Mb  n5
def n10M   := mul n5M   n2
def n10Mb  := mul n5Mb  n2

def Tree := ∀ (T : Type u), (T → T → T) → T → T
def leaf : Tree := λ T n l => l
def node (t1 t2 : Tree) : Tree := λ T n l => n (t1 T n l) (t2 T n l)
def fullTree (n : CNat) : Tree := n Tree (λ t => node t t) leaf

def fullTree2 (n : CNat) : Tree := n Tree (λ t => node t (node t leaf)) leaf

-- full tree with given trees at bottom level
def fullTreeWithLeaf : Tree → CNat → Tree
 := λ bottom n => n Tree (λ t => node t t) bottom

def forceTree : Tree → Bool
 := λ t => t CBool cand ctrue _ true false

--------------------------------------------------------------------------------

def t15  := fullTree n15
def t15b := fullTree n15b
def t18  := fullTree n18
def t18b := fullTree n18b
def t19  := fullTree n19
def t19b := fullTree n19b
def t20  := fullTree n20
def t20b := fullTree n20b
def t21  := fullTree n21
def t21b := fullTree n21b
def t22  := fullTree n22
def t22b := fullTree n22b
def t23  := fullTree n23
def t23b := fullTree n23b

-- Nat conversion
--------------------------------------------------------------------------------

-- not enough stack space

-- Full tree conversion
--------------------------------------------------------------------------------

-- def convt15  : CEq t15 t15b  := crefl
-- def convt18  : CEq t18 t18b  := crefl
-- def convt19  : CEq t19 t19b  := crefl
-- def convt20  : CEq t20 t20b  := crefl
-- def convt21  : CEq t21 t21b  := crefl
-- def convt22  : CEq t22 t22b  := crefl
-- def convt23  : CEq t23 t23b  := crefl

-- Full meta-containing tree conversion
--------------------------------------------------------------------------------

-- * does not elaborate! "can't synthesize placeholder"
-- def convmt15 : t15 = (fullTreeWithLeaf _ n15 ) := rfl
-- def convmt18 : t18 = (fullTreeWithLeaf _ n18 ) := rfl
-- def convmt19 : t19 = (fullTreeWithLeaf _ n19 ) := rfl
-- def convmt20 : t20 = (fullTreeWithLeaf _ n20 ) := rfl
-- def convmt21 : t21 = (fullTreeWithLeaf _ n21 ) := rfl
-- def convmt22 : t22 = (fullTreeWithLeaf _ n22 ) := rfl
-- def convmt23 : t23 = (fullTreeWithLeaf _ n23 ) := rfl

-- Full tree forcing
--------------------------------------------------------------------------------

-- #reduce forceTree t15
-- #reduce forceTree t18
-- #reduce forceTree t19
-- #reduce forceTree t20
-- #reduce forceTree t21
-- #reduce forceTree t22
-- #reduce forceTree t23

#eval t15
-- #reduce t18
-- #reduce t19
-- #reduce t20
-- #reduce t21
-- #reduce t22
-- #reduce t23

-- #eval forceTree t15
-- #eval forceTree t18
-- #eval forceTree t19
-- #eval forceTree t20
-- #eval forceTree t21
-- #eval forceTree t22
-- #eval forceTree t23
