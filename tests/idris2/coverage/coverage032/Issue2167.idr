import Decidable.Equality

%default total

incrementIfEqual : Nat -> Nat -> Nat
incrementIfEqual k j with (decEq k j)
  incrementIfEqual k j | (Yes prf) = S k
  incrementIfEqual k j | (No contra) = k

data PairView : (Nat, Nat) -> Type where
  PairEq : PairView (x,x)
  PairNeq : Not (x = y) -> PairView (x, y)

data SamePairView : PairView a -> PairView b -> Type where
  BothEq : SamePairView PairEq PairEq
  BothNeq : SamePairView (PairNeq neqA) (PairNeq neqB)

pairViewIncSame : {k : Nat} -> (p : (Nat, Nat)) -> (v : PairView p) -> (w : PairView (incrementIfEqual (fst p) k, incrementIfEqual (snd p) k)) -> SamePairView v w
pairViewIncSame (x, x) PairEq PairEq = BothEq
pairViewIncSame (x, x) PairEq (PairNeq neq) with (decEq x k)
  pairViewIncSame (x, x) PairEq (PairNeq neq) | (Yes prf) = void $ neq Refl
  pairViewIncSame (x, x) PairEq (PairNeq neq) | (No contra) = void $ neq Refl
pairViewIncSame (x, y) (PairNeq _) (PairNeq _) = BothNeq

eqSameNeqAbsurd : SamePairView (PairNeq neq) PairEq -> Void
eqSameNeqAbsurd BothEq impossible
eqSameNeqAbsurd BothNeq impossible

makeVoid : Void
makeVoid = eqSameNeqAbsurd (pairViewIncSame (1,2) (PairNeq oneNotTwo) PairEq {k=1})
  where
    oneNotTwo : Not ((the Nat 1) = 2)
    oneNotTwo Refl impossible
