module Algebra

import public Algebra.Parametric
import public Algebra.ZeroOneOmega
import public Algebra.Semiring
import public Algebra.Preorder

%default total

public export
RigCount : Type
RigCount = Parametric ZeroOneOmega

export
showCount : RigCount -> String
showCount  Param     = "## "
showCount (Rig Rig0) = "0 "
showCount (Rig Rig1) = "1 "
showCount (Rig RigW) = ""

export
isErased : RigCount -> Bool
isErased  Param     = True
isErased (Rig Rig0) = True
isErased _          = False

export
isLinear : RigCount -> Bool
isLinear (Rig Rig1) = True
isLinear _ = False

export
isRigOther : RigCount -> Bool
isRigOther (Rig RigW) = True
isRigOther _ = False

export
branchZero : Lazy b -> Lazy b -> RigCount -> b
branchZero yes no rig = if isErased rig then yes else no

export
branchOne : Lazy b -> Lazy b -> RigCount -> b
branchOne yes no rig = if isLinear rig then yes else no

export
branchVal : Lazy b -> Lazy b -> RigCount -> b
branchVal yes no rig = if isRigOther rig then yes else no

||| Erased linearity corresponds to the neutral for |+|
public export
erased : RigCount
erased = Rig Rig0
