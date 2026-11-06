module Algebra.Parametric

import Algebra.Semiring
import Algebra.Preorder

%default total

export
data Parametric a = Param | Rig a

%name Parametric rig

export
Preorder a => Preorder (Parametric a) where
  Param <= _ = True
  Rig x <= Rig y = x <= y
  _ <= Param = False

  preorderRefl {x = Param} = Refl
  preorderRefl {x = Rig x} = preorderRefl

  preorderTrans {x = Param} _ _ = Refl
  preorderTrans {x = Rig _} {y = Param} _ _ impossible
  preorderTrans {y = Rig _} {z = Param} _ _ impossible
  preorderTrans {x = Rig x} {y = Rig y} {z = Rig z} xy yz = preorderTrans xy yz

public export
Eq a => Eq (Parametric a) where
  Param == Param = True
  Rig x == Rig y = x == y
  _ == _ = False

export
Show a => Show (Parametric a) where
  show Param = "Param"
  show (Rig x) = show x

public export
Semiring a => Semiring (Parametric a) where
  Param |+| y = y
  x |+| Param = x
  Rig x |+| Rig y = Rig (x |+| y)

  Param |*| y = Param
  x |*| Param = Param
  Rig x |*| Rig y = Rig (x |*| y)

  plusNeutral = Param
  timesNeutral = Rig timesNeutral


||| The top value of a lattice
export
Top a => Top (Parametric a) where
  top = Rig top
  topAbs {x = Param} = Refl
  topAbs {x = Rig x} = topAbs

export
parametric : Parametric a
parametric = Param
