0 oops : (0 a : Type) -> a
oops Nat = Z

boom : Void
boom = void (oops Void)
