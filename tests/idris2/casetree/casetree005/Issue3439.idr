f : Lazy Bool -> Bool
f x@True = x
f x@False = x

g : Lazy Bool -> Bool
g b = case b of
  x@True => x
  x@False => x

h : Lazy Bool -> Bool
h b = case b of
  Delay x@True => x
  Delay x@False => x
