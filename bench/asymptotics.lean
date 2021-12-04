set_option maxRecDepth 10000

universe i

def CNat : Type 1 := ∀ (N : Type), (N → N) → N → N
def czero : CNat := λ n s z => z
def csuc : CNat → CNat := λ a n s z => s (a n s z)

def Vec : Type → CNat → Type 1
  := λ A n => ∀ (V : CNat → Type), (∀ n, A → V n → V (csuc n)) → V czero → V n

def nil {A:Type} : Vec A czero
 := λ V c n => n

def cons {A:Type} {n:CNat} : A → Vec A n → Vec A (csuc n)
  := λ x xs V c nil => c n x (xs V c nil)

def Pair : Type i -> Type i -> Type (i + 1)
  := λ A B => ∀ (P : Type i), (A → B → P) → P

def dup : ∀ {A : Type i}, A → Pair A A
  := λ a P p => p a a

--------------------------------------------------------------------------------

-- fails
-- def idTest {A : Type} : A → A
--   := id id id id id id id id id id id id id id id id id id id id
--      id id id id id id id id id id id id id id id id id id id id

-- fails, but! 20 still works, memory usage is low constant, and only
-- the "compilation" phase in --profile appears to be exponential

-- def pairTest :=
--   let x0  := dup true ;
--   let x1  := dup x0   ;
--   let x2  := dup x1   ;
--   let x3  := dup x2   ;
--   let x4  := dup x3   ;
--   let x5  := dup x4   ;
--   let x6  := dup x5   ;
--   let x7  := dup x6   ;
--   let x8  := dup x7   ;
--   let x9  := dup x8   ;
--   let x10 := dup x9   ;
--   let x11 := dup x10  ;
--   let x12 := dup x11  ;
--   let x13 := dup x12  ;
--   let x14 := dup x13  ;
--   let x15 := dup x14  ;
--   let x16 := dup x15  ;
--   let x17 := dup x16  ;
--   let x18 := dup x17  ;
--   let x19 := dup x18  ;
--   let x20 := dup x19  ;
--   let x21 := dup x20  ;
--   let x22 := dup x21  ;
--   let x23 := dup x22  ;
--   let x24 := dup x23  ;
--   let x25 := dup x24  ;
--   let x26 := dup x25  ;
--   let x27 := dup x26  ;
--   let x28 := dup x27  ;
--   let x29 := dup x28  ;
--   let x30 := dup x29  ;
--   x30


def vecTest :=
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true
   (cons true (cons true (cons true (cons true (cons true (cons true

   nil

   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
   ))))))))))))))))))))))))))))))
