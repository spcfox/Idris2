module Issue2158.A

import Language.Reflection

export
aNoop : Elaboration m => m ()
aNoop = pure ()
