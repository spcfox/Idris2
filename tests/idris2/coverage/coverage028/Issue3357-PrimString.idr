0 oops : (0 x : String) -> if x == "" then Unit else Void
oops "" = ()

boom : Void
boom = void (oops "foo")
