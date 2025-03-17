module Libraries.Data.SnocList.LengthMatch

import Libraries.Data.SnocList.HasLength

---------------------------------------
-- horrible hack
import Libraries.Data.List.LengthMatch as L

public export
LLengthMatch : List a -> List b -> Type
LLengthMatch = L.LengthMatch
%hide L.LengthMatch
---------------------------------------

%default total

public export
data LengthMatch : SnocList a -> SnocList b -> Type where
     LinMatch : LengthMatch [<] [<]
     SnocMatch : LengthMatch xs ys -> LengthMatch (xs :< x) (ys :< y)

export
checkLengthMatch : (xs : SnocList a) -> (ys : SnocList b) ->
  Maybe (LengthMatch xs ys)
checkLengthMatch [<] [<] = Just LinMatch
checkLengthMatch [<] (_ :< _) = Nothing
checkLengthMatch (_ :< _) [<] = Nothing
checkLengthMatch (xs :< _) (ys :< _)
    = Just (SnocMatch !(checkLengthMatch xs ys))

export
lengthsMatch : LengthMatch xs ys -> (length xs) = (length ys)
lengthsMatch LinMatch = Refl
lengthsMatch (SnocMatch x) = cong S (lengthsMatch x)

export
hasLengthLeft : LengthMatch xs ys -> HasLength (length xs) xs
hasLengthLeft LinMatch = Z
hasLengthLeft (SnocMatch x) = S $ hasLengthLeft x

export
hasLengthRight : LengthMatch xs ys -> HasLength (length ys) ys
hasLengthRight LinMatch = Z
hasLengthRight (SnocMatch x) = S $ hasLengthRight x

export
lengthMatchSameLength : HasLength n sx -> HasLength n sy -> LengthMatch sx sy
lengthMatchSameLength  Z     Z    = LinMatch
lengthMatchSameLength (S n) (S m) = SnocMatch $ lengthMatchSameLength n m

export
symmetric : LengthMatch sx sy -> LengthMatch sy sx
symmetric p = lengthMatchSameLength (hasLengthRight p) $
                rewrite sym $ lengthsMatch p in hasLengthLeft p

export
reverseRight : LengthMatch sx sy -> LengthMatch sx (reverse sy)
reverseRight p = lengthMatchSameLength (hasLengthLeft p) $
                   rewrite lengthsMatch p in hlReverse $ hasLengthRight p

export
reverseLeft : LengthMatch sx sy -> LengthMatch (reverse sx) sy
reverseLeft = symmetric . reverseRight . symmetric

export
reverse : LengthMatch sx sy -> LengthMatch (reverse sx) (reverse sy)
reverse = reverseLeft . reverseRight

export
fromListLengthMatch : LLengthMatch xs ys -> LengthMatch ([<] <>< xs) ([<] <>< ys)
fromListLengthMatch p = lengthMatchSameLength (hlFish Z (hasLengthLeft p)) $
                          rewrite lengthsMatch p in (hlFish Z (hasLengthRight p))
