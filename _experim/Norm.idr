module Norm

import Language.Reflection
import Data.Maybe

%language ElabReflection

T : Type
T = Type

normaliseAs : Type -> TTImp -> Elab TTImp
normaliseAs expected tm = quote !(check {expected} tm)

public export
normaliseAsType : TTImp -> Elab ()
normaliseAsType tm =
  do tm' <- normaliseAs Type tm
     logMsg "debug.normaliseAsType" 0 "input:  \{show tm}"
     logMsg "debug.normaliseAsType" 0 "output  \{show tm'}"

%runElab do
  let tm = `( T -> Type )
  ignore $ normaliseAsType tm
