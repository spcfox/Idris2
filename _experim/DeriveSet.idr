import Data.List
import Data.String
import Deriving.Show

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Sets
--------------------------------------------------------------------------------

public export
Size : Type
Size = Nat

||| A finite set of values.
public export
data Set : (a : Type) -> Type where
  Bin :  Size
      -> a
      -> Set a
      -> Set a
      -> Set a
  Tip : Set a

-- %runElab derive "Set" [Eq,Ord,Show]

showSet : Show a => Show (Set a)
showSet = %runElab derive
