module Algebra.ZeroOneOmega

import Algebra.Semiring
import Algebra.Preorder

%default total

export
data ZeroOneOmega = Rig0 | Rig1 | RigW

%name ZeroOneOmega rig

export
Preorder ZeroOneOmega where
  Rig0 <= Rig0 = True
  Rig1 <= Rig1 = True
  _    <= RigW = True
  _    <=    _ = False
  preorderRefl {x = Rig0} = Refl
  preorderRefl {x = Rig1} = Refl
  preorderRefl {x = RigW} = Refl
  preorderTrans {x = Rig0} {y = Rig0} _ yz = yz
  preorderTrans {x = Rig0} {y = RigW} {z = RigW} _ _ = Refl
  preorderTrans {x = Rig1} {y = Rig1} _ yz = yz
  preorderTrans {x = Rig1} {y = RigW} {z = RigW} _ _ = Refl
  preorderTrans {x = RigW} {y = RigW} _ yz = yz

||| Least Upper Bound
export
lub : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
lub Rig0 y = y
lub x Rig0 = x
lub Rig1 x = x
lub x Rig1 = x
lub _ _ = RigW

||| Greatest Lower Bound
export
glb : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
glb RigW y = y
glb x RigW = x
glb Rig1 x = x
glb x Rig1 = x
glb _ _ = Rig0

public export
(<) : ZeroOneOmega -> ZeroOneOmega -> Bool
Rig0 < Rig1 = True
Rig0 < RigW = True
Rig1 < RigW = True
_    < _    = False

public export
Eq ZeroOneOmega where
  (==) Rig0 Rig0 = True
  (==) Rig1 Rig1 = True
  (==) RigW RigW = True
  (==) _ _ = False

export
Show ZeroOneOmega where
  show Rig0 = "Rig0"
  show Rig1 = "Rig1"
  show RigW = "RigW"

export
rigPlus : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigPlus Rig0 a = a
rigPlus a Rig0 = a
rigPlus _ _ = RigW

export
rigMult : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigMult Rig0 _ = Rig0
rigMult _ Rig0 = Rig0
rigMult Rig1 a = a
rigMult a Rig1 = a
rigMult _ _ = RigW


public export
Semiring ZeroOneOmega where
  (|+|) = rigPlus
  (|*|) = rigMult
  plusNeutral = Rig0
  timesNeutral = Rig1

public export
SubtractiveSemiring ZeroOneOmega where
  x    |-| Rig0 = Just x
  Rig0 |-| _    = Nothing
  Rig1 |-| Rig1 = Just Rig0
  Rig1 |-| RigW = Nothing
  RigW |-| _    = Just RigW

||| The top value of a lattice
export
Top ZeroOneOmega where
  top = RigW
  topAbs {x = Rig0} = Refl
  topAbs {x = Rig1} = Refl
  topAbs {x = RigW} = Refl

----------------------------------------

rigPlusAssociative : (x, y, z : ZeroOneOmega) ->
  rigPlus x (rigPlus y z) = rigPlus (rigPlus x y) z
rigPlusAssociative Rig0 _ _ = Refl
rigPlusAssociative Rig1 Rig0 _ = Refl
rigPlusAssociative Rig1 Rig1 Rig0 = Refl
rigPlusAssociative Rig1 Rig1 Rig1 = Refl
rigPlusAssociative Rig1 Rig1 RigW = Refl
rigPlusAssociative Rig1 RigW Rig0 = Refl
rigPlusAssociative Rig1 RigW Rig1 = Refl
rigPlusAssociative Rig1 RigW RigW = Refl
rigPlusAssociative RigW Rig0 _ = Refl
rigPlusAssociative RigW Rig1 Rig0 = Refl
rigPlusAssociative RigW Rig1 Rig1 = Refl
rigPlusAssociative RigW Rig1 RigW = Refl
rigPlusAssociative RigW RigW Rig0 = Refl
rigPlusAssociative RigW RigW Rig1 = Refl
rigPlusAssociative RigW RigW RigW = Refl

rigPlusCommutative : (x, y : ZeroOneOmega) ->
  rigPlus x y = rigPlus y x
rigPlusCommutative Rig0 Rig0 = Refl
rigPlusCommutative Rig0 Rig1 = Refl
rigPlusCommutative Rig0 RigW = Refl
rigPlusCommutative Rig1 Rig0 = Refl
rigPlusCommutative Rig1 Rig1 = Refl
rigPlusCommutative Rig1 RigW = Refl
rigPlusCommutative RigW Rig0 = Refl
rigPlusCommutative RigW Rig1 = Refl
rigPlusCommutative RigW RigW = Refl

rigMultAssociative : (x, y, z : ZeroOneOmega) ->
  rigMult x (rigMult y z) = rigMult (rigMult x y) z
rigMultAssociative Rig0 _ _ = Refl
rigMultAssociative Rig1 Rig0 _ = Refl
rigMultAssociative Rig1 Rig1 Rig0 = Refl
rigMultAssociative Rig1 Rig1 Rig1 = Refl
rigMultAssociative Rig1 Rig1 RigW = Refl
rigMultAssociative Rig1 RigW Rig0 = Refl
rigMultAssociative Rig1 RigW Rig1 = Refl
rigMultAssociative Rig1 RigW RigW = Refl
rigMultAssociative RigW Rig0 _ = Refl
rigMultAssociative RigW Rig1 Rig0 = Refl
rigMultAssociative RigW Rig1 Rig1 = Refl
rigMultAssociative RigW Rig1 RigW = Refl
rigMultAssociative RigW RigW Rig0 = Refl
rigMultAssociative RigW RigW Rig1 = Refl
rigMultAssociative RigW RigW RigW = Refl

rigMultCommutative : (x, y : ZeroOneOmega) ->
  rigMult x y = rigMult y x
rigMultCommutative Rig0 Rig0 = Refl
rigMultCommutative Rig0 Rig1 = Refl
rigMultCommutative Rig0 RigW = Refl
rigMultCommutative Rig1 Rig0 = Refl
rigMultCommutative Rig1 Rig1 = Refl
rigMultCommutative Rig1 RigW = Refl
rigMultCommutative RigW Rig0 = Refl
rigMultCommutative RigW Rig1 = Refl
rigMultCommutative RigW RigW = Refl
