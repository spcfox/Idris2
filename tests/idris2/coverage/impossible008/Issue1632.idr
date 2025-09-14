import Data.Vect

public export
data Split : Vect n a -> Type where
    SplitNil : Split []
    SplitOne : Split [x]
    SplitPair : {n : Nat} -> {m : Nat} ->
                (xs : Vect (S n) a) -> (ys : Vect (S m) a) ->
                Split (xs ++ ys)

total
splitHelp : {lz : Nat} -> (head : a) -> (zs : Vect lz a) ->
            Nat -> Split (head :: zs)
splitHelp head [] _ = SplitOne
splitHelp head (z :: zs) 0 = SplitPair [head] (z :: zs)
splitHelp head (z :: zs) 1 = SplitPair [head] (z :: zs)
splitHelp head (z :: zs) (S (S k))
  = case splitHelp z zs k of
         SplitOne => SplitPair [head] (z :: zs)
         SplitPair (x :: xs) ys => SplitPair (head :: x :: xs) ys
