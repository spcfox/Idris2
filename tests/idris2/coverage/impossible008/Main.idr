data X : Bool -> Type where
  A : Void -> X True
  B : X False

total
foo : (b : Bool) -> (0 _ : X b) -> Void
foo _ (A v) impossible


data IsMaybe : Maybe a -> Type where
  IsJust : IsMaybe (Just x)
  IsNothing : IsMaybe Nothing

bar : (m : Maybe Void) -> (0 _ : IsMaybe m) -> Void
bar _ IsJust impossible
