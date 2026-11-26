%auto_lazy off

namespace Example1
  n : Nat
  n = 1

  m : Nat
  m = delay n

  k : Nat
  k = force n

namespace Example2
  main : IO ()
  main = putStrLn "Hello" >> putStrLn {io=IO} "world"

namespace Example3
  data X = A

  f : Lazy X -> X
  f x@A = x

  main : IO ()
  main = ignore $ pure $ f A
