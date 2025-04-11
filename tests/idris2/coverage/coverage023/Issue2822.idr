f : (b : Bool) -> if b then Nat -> Nat else Void
f True x = x

g : (b : Bool) -> if b then Nat -> Nat else Void
g True x = x
g False x impossible
