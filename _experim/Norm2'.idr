module Norm2

import Language.Reflection
import Data.Maybe
import Data.Fin

%language ElabReflection

normaliseAs : Type -> TTImp -> Elab TTImp
normaliseAs expected tm =
  do tm' <- quote !(check {expected} tm)
     logMsg "debug.normaliseAsType" 0 "input: \{show tm}"
     logMsg "debug.normaliseAsType" 0 "output: \{show tm'}"
     pure tm'

normaliseAsType : TTImp -> Elab TTImp
normaliseAsType tm = normaliseAs Type tm

%runElab do
  let tm = `( natToFinLT (S Z) {n = S (S Z)} {prf = ltOpReflectsLT (S Z) (S (S Z)) Oh} )
  ignore $ normaliseAs (Fin (S (S Z))) tm
