id : (a : Type) -> a -> a
const : (a, b : Type) -> a -> b -> a
List : Type -> Type
All : (a : Type) -> (p : a -> Type) -> List a -> Type
remember : (a : _) -> (xs : List a) -> All a (const Type a a) xs

HList : List Type -> Type
HList = All _ (id _)
