import Data.SortedSet

import Language.Reflection

%language ElabReflection

scr : List Nat -> Elab Unit
scr xs = ignore $ logMsg "debug" 0 "length: \{show $ length $ SortedSet.toList $ fromList xs}"

%runElab scr [0, 2, 3]
