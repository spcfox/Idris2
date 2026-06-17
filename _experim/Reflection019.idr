module Reflection019

import Language.Reflection

%language ElabReflection

showsWarning : ty -> Elab Nat
showsWarning n = do
  tm <- quote n
  check tm

x : Nat
x = %runElab showsWarning 0
-- %runElab ignore $ showsWarning "Suspicious" 15
