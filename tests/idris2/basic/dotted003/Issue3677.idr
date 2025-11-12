import Data.Vect

foo : (n : Nat) -> Vect n a -> ()
foo Z [] = ()
foo n@(.(S n)) (_ :: xs) = foo _ xs
