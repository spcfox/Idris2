module Algebra.Preorder

%default total

||| Preorder defines a binary relation using the `<=` operator
public export
interface Preorder a where
  (<=) : a -> a -> Bool
  preorderRefl : {x : a} -> x <= x = True
  preorderTrans : {x, y, z : a} -> x <= y = True -> y <= z = True -> x <= z = True

||| The greatest bound of a bounded lattice, we only need to know about preorders however
public export
interface Preorder a => Top a where
  top : a
  topAbs : {x : a} -> x <= top = True
