0 oops : (0 x : Int) -> if x == 0 then Unit else Void
oops 0 = ()

boom : Void
boom = void (oops 1)
