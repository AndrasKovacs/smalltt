
set_option maxHeartbeats 1000000
set_option maxRecDepth   1000000

universe u

def CBool := ∀ (B : Type u), B → B → B
def ctrue : CBool := λ B t f => t
def cand  : CBool → CBool → CBool := λ a b B t f => a B (b B t f) f

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
def fullTree (n : CNat) : Tree := n _ (λ t => node t t) leaf

def t20k  := fullTree n10
def t20kb := fullTree n10b
def t65k  := fullTree n15
def t65kb := fullTree n15b
def t512k  := fullTree n18
def t512kb := fullTree n18b
def t1M  := fullTree n19
def t1Mb := fullTree n19b
def t2M  := fullTree n20
def t2Mb := fullTree n20b
def t4M  := fullTree n22
def t4Mb := fullTree n22b
def t8M  := fullTree n23
def t8Mb := fullTree n23b

def forceTree : Tree → Bool := λ t => t Bool and true

-- def convt20k : t20k = t20kb := rfl
-- def convt65k : t65k = t65kb := rfl
-- def convt512k : t512k = t512kb := rfl
-- def convt1M  : t1M = t1Mb := rfl
-- def convt2M  : t2M = t2Mb := rfl

-- def convt4M  : t4M = t4Mb := rfl
-- def convt8M  : t8M = t8Mb := rfl

-- #eval forceTree t2M
-- #eval forceTree t4M
-- #eval forceTree t8M
