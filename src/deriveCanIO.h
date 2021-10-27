#define COMMA ,

#define CAN_IO(ty, reprep, rep, ctr, coe)\
type instance UIO.RepRep (ty) = (reprep);\
type family coe (x :: TYPE (reprep)) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
type instance UIO.Rep (ty) = coe (rep);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (rep) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, x #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, rep #);\
  pure# (ctr) s = (# s, x #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}

#define CAN_IO2(ty, rrep1, rrep2, rep1, rep2, ctr, coe)         \
type instance UIO.RepRep (ty) = (TupleRep [rrep1 COMMA rrep2]);\
type family coe (x :: TYPE (TupleRep [rrep1 COMMA rrep2])) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
type instance UIO.Rep (ty) = coe (# rep1, rep2 #);\
\
instance UIO.CanIO (ty) where {\
                               bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (# rep1, rep2 #) #)) \
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# x, y #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, (# rep1, rep2 #) #);\
  pure# (ctr) s = (# s, (# x, y #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}

#define CAN_IO3(ty, rrep1, rrep2, rrep3, rep1, rep2, rep3, ctr, coe)    \
type instance UIO.RepRep (ty) = (TupleRep [rrep1 COMMA rrep2 COMMA rrep3]);\
type family coe (x :: TYPE (TupleRep [rrep1 COMMA rrep2 COMMA rrep3])) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
 type instance UIO.Rep (ty) = coe (# rep1, rep2, rep3 #);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3 #) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# x, y, z #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3 #) #);\
  pure# (ctr) s = (# s, (# x, y, z #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}

#define CAN_IO4(ty, rrep1, rrep2, rrep3, rrep4, rep1, rep2, rep3, rep4, ctr, coe) \
type instance UIO.RepRep (ty) = (TupleRep [rrep1 COMMA rrep2 COMMA rrep3 COMMA rrep4]);\
type family coe (x :: TYPE (TupleRep [rrep1 COMMA rrep2 COMMA rrep3 COMMA rrep4])) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
 type instance UIO.Rep (ty) = coe (# rep1, rep2, rep3, rep4 #);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3, rep4 #) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# a, b, c, d #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3, rep4 #) #);\
  pure# (ctr) s = (# s, (# a, b, c, d #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}

#define CAN_IO5(ty, rrep1, rrep2, rrep3, rrep4, rrep5, rep1, rep2, rep3, rep4, rep5, ctr, coe) \
type instance UIO.RepRep (ty) = (TupleRep [rrep1 COMMA rrep2 COMMA rrep3 COMMA rrep4 COMMA rrep5]);\
type family coe (x :: TYPE (TupleRep [rrep1 COMMA rrep2 COMMA rrep3 COMMA rrep4 COMMA rrep5])) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
 type instance UIO.Rep (ty) = coe (# rep1, rep2, rep3, rep4, rep5 #);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3, rep4, rep5 #) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# a, b, c, d, e #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3, rep4, rep5 #) #);\
  pure# (ctr) s = (# s, (# a, b, c, d, e #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}

#define CAN_IO6(ty, rrep1, rrep2, rrep3, rrep4, rrep5, rrep6, rep1, rep2, rep3, rep4, rep5, rep6, ctr, coe) \
type instance UIO.RepRep (ty) = (TupleRep [rrep1 COMMA rrep2 COMMA rrep3 COMMA rrep4 COMMA rrep5 COMMA rrep6]);\
type family coe (x :: TYPE (TupleRep [rrep1 COMMA rrep2 COMMA rrep3 COMMA rrep4 COMMA rrep5 COMMA rrep6])) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
 type instance UIO.Rep (ty) = coe (# rep1, rep2, rep3, rep4, rep5, rep6 #);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3, rep4, rep5, rep6 #) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# a, b, c, d, e, f #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3, rep4, rep5, rep6 #) #);\
  pure# (ctr) s = (# s, (# a, b, c, d, e, f #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}

#define CAN_IO7(ty, rrep1, rrep2, rrep3, rrep4, rrep5, rrep6, rrep7, rep1, rep2, rep3, rep4, rep5, rep6, rep7, ctr, coe) \
type instance UIO.RepRep (ty) = (TupleRep [rrep1 COMMA rrep2 COMMA rrep3 COMMA rrep4 COMMA rrep5 COMMA rrep6 COMMA rrep7]);\
type family coe (x :: TYPE (TupleRep [rrep1 COMMA rrep2 COMMA rrep3 COMMA rrep4 COMMA rrep5 COMMA rrep6 COMMA rrep7])) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
 type instance UIO.Rep (ty) = coe (# rep1, rep2, rep3, rep4, rep5, rep6, rep7 #);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3, rep4, rep5, rep6, rep7 #) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# a, b, c, d, e, f, g #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, (# rep1, rep2, rep3, rep4, rep5, rep6, rep7 #) #);\
  pure# (ctr) s = (# s, (# a, b, c, d, e, f, g #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}
