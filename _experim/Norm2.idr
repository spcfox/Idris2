module Norm2

import Language.Reflection
import Data.Maybe
import Data.Fin

%language ElabReflection

Y : Fin (S (S Z)) -> Type

normaliseAs : Type -> TTImp -> Elab TTImp
normaliseAs expected tm =
  do tm' <- quote !(check {expected} tm)
     logMsg "debug.normaliseAsType" 0 "input: \{show tm}"
     logMsg "debug.normaliseAsType" 0 "output: \{show tm'}"
     pure tm'

normaliseAsType : TTImp -> Elab TTImp
normaliseAsType tm = normaliseAs Type tm

%runElab do
  let tm = `( Y (natToFinLT (S Z) {n = S (S Z)} {prf = ltOpReflectsLT (S Z) (S (S Z)) Oh}) )
  ignore $ normaliseAsType tm
