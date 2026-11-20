module Algebra.Semiring

%default total

export infixl 8 |+|, |-|
export infixl 9 |*|

||| A Semiring has two binary operations and an identity for each
public export
interface Semiring a where
  (|+|) : a -> a -> a
  plusNeutral : a
  (|*|) : a -> a -> a
  timesNeutral : a

public export
interface Semiring a => SubtractiveSemiring a where
  (|-|) : a -> a -> Maybe a

public export
isIdempotent : Semiring a => Eq a => a -> Bool
isIdempotent x = (x |+| x) == x

||| Erased linearity corresponds to the neutral for |+|
public export
erased : Semiring a => a
erased = plusNeutral

||| Purely linear corresponds to the neutral for |*|
public export
linear : Semiring a => a
linear = timesNeutral

||| A semiring eliminator
public export
elimSemi : (Semiring a, Eq a) => (zero : b) -> (one : b) -> (a -> b) -> a -> b
elimSemi zero one other r {a} =
  if r == Semiring.plusNeutral {a}
     then zero
     else if r == Semiring.timesNeutral {a}
             then one
             else other r

export
isErased : (Semiring a, Eq a) => a -> Bool
isErased = elimSemi True False (const False)
