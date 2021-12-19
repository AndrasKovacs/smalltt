
mid : {A:Type} -> A -> A
mid = \ x => x

CPair : Type -> Type -> Type
CPair = \ a, b => (p : Type) -> (a -> b -> p) -> p

cdup : {A:Type} -> A -> CPair A A
cdup = \ a, x, p => p a a

CNat : Type
CNat = (n : Type) -> (n -> n) -> n -> n

czero : CNat
czero = \ n, s, z => z

csuc : CNat -> CNat
csuc = \ a, n, s, z => s (a n s z)

CVec : Type -> CNat -> Type
CVec = \ a, n => (V : CNat -> Type) -> ({n : CNat} -> a -> V n -> V (csuc n)) -> V czero -> V n

cnil : {A:Type} -> CVec A Main.czero
cnil = \ v, c, n => n

ccons : {A:Type}->{n:CNat} -> A -> CVec A n -> CVec A (csuc n)
ccons = \ a, as, v, c, n => c a (as v c n)

--------------------------------------------------------------------------------

-- fails
-- idTest : {A:Type} -> A -> A
-- idTest =
--     mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid
--     mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid mid

-- fails
-- pairTest =
--   let x0  = cdup Type
--       x1  = cdup x0
--       x2  = cdup x1
--       x3  = cdup x2
--       x4  = cdup x3
--       x5  = cdup x4
--       x6  = cdup x5
--       x7  = cdup x6
--       x8  = cdup x7
--       x9  = cdup x8
--       x10 = cdup x9
--       x11 = cdup x10
--       x12 = cdup x11
--       x13 = cdup x12
--       x14 = cdup x13
--       x15 = cdup x14
--       x16 = cdup x15
--       x17 = cdup x16
--       x18 = cdup x17
--       x19 = cdup x18
--       x20 = cdup x19
--       x21 = cdup x20
--       x22 = cdup x21
--       x23 = cdup x22
--       x24 = cdup x23
--       x25 = cdup x24
--       x26 = cdup x25
--       x27 = cdup x26
--       x28 = cdup x27
--       x29 = cdup x28
--       x30 = cdup x29
--   in x30

vecTest : Type
vecTest =
  let foo =
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type
       (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type (ccons Type

       cnil

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

  in Type
