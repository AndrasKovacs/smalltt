
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