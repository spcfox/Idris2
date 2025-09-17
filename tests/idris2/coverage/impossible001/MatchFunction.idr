B : () -> Type

data S : a -> Type where
  El : (0 b : a) -> S b

P : S a -> Bool
P s = True

data T : Bool -> Type where
  Y : T False
  X : (arg : S B) -> T (P arg)

foo : (b = False) => T b -> ()
foo Y = ()
foo (X (El B)) impossible
