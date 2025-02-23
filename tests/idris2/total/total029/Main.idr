%default total

f : Bool -> Void
g : Bool -> Void
h : Bool -> Void
i : Bool -> Void
j : Bool -> Void

f True  = g True
f False = f False

g True  = h True
g False = g False

h True  = i True
h False = h False

i True  = j True
i False = i False

j True  = f True
j False = j False
