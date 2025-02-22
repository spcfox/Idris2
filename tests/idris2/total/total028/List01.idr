%default total

data List01 : (nonEmpty : Bool) -> Type -> Type where
  Nil  : List01 False a
  (::) : a -> List01 ine a -> List01 ne a

foldr1 : (op : a -> a -> a) -> List01 True a -> a
foldr1 op [x]            = x
foldr1 op (x :: y :: ys) = op x $ foldr1 op (y :: ys)

last : List01 True a -> a
last [x] = x
last (_ :: x :: xs) = last (x :: xs)

init : List01 True a -> List01 False a
init [x] = []
init (x :: y :: ys) = x :: init (y :: ys)
