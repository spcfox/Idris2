module Libraries.Decidable.Equality

import public Decidable.Equality

toMaybe : Dec a -> Maybe a
toMaybe (Yes a) = Just a
toMaybe (No _)  = Nothing

%inline
public export
maybeEq : DecEq a => (x, y : a) -> Maybe (x = y)
maybeEq x y = toMaybe (decEq x y)
