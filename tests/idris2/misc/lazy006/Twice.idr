import Debug.Trace

%noinline
twice : String -> Lazy Nat -> Lazy Nat
twice s n = trace s (2 * n)

calc : Nat -> Nat
calc n0 =
  let n1 = twice "foo" n0
      n2 = twice "bar" n1
      n3 = twice "baz" n2
   in if n0 > 10 then n2 else n3

main : IO ()
main = do printLn (calc 100)
