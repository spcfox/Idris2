data Even : Nat -> Type where
  MkEven : (j: Nat) -> DPair Nat (\n => j = n + n) -> Even j

two : Even 2
two = MkEven 2 (1 ** Refl)

notTwo : Even 2 -> Void
notTwo (MkEven (S (S Z)) (Z ** Refl)) impossible

aVoid : Void
aVoid = notTwo two

trivial : a
trivial = void aVoid
