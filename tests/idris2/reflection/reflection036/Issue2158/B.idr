module Issue2158.B

import Language.Reflection
import Issue2158.A

%language ElabReflection

export
elabFoo : Elab ()
elabFoo = aNoop
