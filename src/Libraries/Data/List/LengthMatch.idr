module Libraries.Data.List.LengthMatch

import Data.List.HasLength

%default total

public export
data LengthMatch : List a -> List b -> Type where
     NilMatch : LengthMatch [] []
     ConsMatch : LengthMatch xs ys -> LengthMatch (x :: xs) (y :: ys)

export
hasLengthLeft : LengthMatch xs ys -> HasLength (length xs) xs
hasLengthLeft NilMatch = Z
hasLengthLeft (ConsMatch x) = S $ hasLengthLeft x

export
hasLengthRight : LengthMatch xs ys -> HasLength (length ys) ys
hasLengthRight NilMatch = Z
hasLengthRight (ConsMatch x) = S $ hasLengthRight x

export
checkLengthMatch : (xs : List a) -> (ys : List b) -> Maybe (LengthMatch xs ys)
checkLengthMatch [] [] = Just NilMatch
checkLengthMatch [] (x :: xs) = Nothing
checkLengthMatch (x :: xs) [] = Nothing
checkLengthMatch (x :: xs) (y :: ys)
    = Just (ConsMatch !(checkLengthMatch xs ys))

export
lengthsMatch : LengthMatch xs ys -> (length xs) = (length ys)
lengthsMatch NilMatch = Refl
lengthsMatch (ConsMatch x) = cong (S) (lengthsMatch x)
