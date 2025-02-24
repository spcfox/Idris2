import Data.Vect

total
f : Type -> ()
f (Vect (S n) a) = f a
f _ = ()
