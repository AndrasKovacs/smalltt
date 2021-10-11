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

#define CAN_IO2(ty, reprep, rep, ctr, coe)\
type instance UIO.RepRep (ty) = (reprep);\
type family coe (x :: TYPE (reprep)) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
type instance UIO.Rep (ty) = coe (rep);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (rep) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# x, y #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, rep #);\
  pure# (ctr) s = (# s, (# x, y #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}

#define CAN_IO3(ty, reprep, rep, ctr, coe)\
type instance UIO.RepRep (ty) = (reprep);\
type family coe (x :: TYPE (reprep)) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
type instance UIO.Rep (ty) = coe (rep);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (rep) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# x, y, z #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, rep #);\
  pure# (ctr) s = (# s, (# x, y, z #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}

#define CAN_IO4(ty, reprep, rep, ctr, coe)\
type instance UIO.RepRep (ty) = (reprep);\
type family coe (x :: TYPE (reprep)) :: TYPE (UIO.RepRep (ty)) where {\
  coe x = x;};\
type instance UIO.Rep (ty) = coe (rep);\
\
instance UIO.CanIO (ty) where {\
  bind :: forall r (out :: TYPE r). (UIO.RW -> (# UIO.RW, (rep) #))\
       -> ((ty) -> UIO.RW -> (# UIO.RW, out #)) -> UIO.RW -> (# UIO.RW, out #);\
  bind f g s = case f s of {(# s, (# a, b, c, d #) #) -> g (ctr) s};\
\
  pure#  :: (ty) -> UIO.RW -> (# UIO.RW, rep #);\
  pure# (ctr) s = (# s, (# a, b, c, d #) #);\
\
  {-# inline bind #-};\
  {-# inline pure# #-};\
}
