-- Primitive type on LHS
intImpossible : Int -> ()
intImpossible Int impossible
intImpossible _ = ()

-- Primitive type on LHS
worldImpossible : Int -> ()
worldImpossible %World impossible
worldImpossible _ = ()

-- Primitive value on LHS
mkWorldImpossible : Int -> ()
mkWorldImpossible %MkWorld impossible
mkWorldImpossible _ = ()

-- Type on LHS
typeImpossible : Int -> ()
typeImpossible Type impossible
typeImpossible _ = ()
