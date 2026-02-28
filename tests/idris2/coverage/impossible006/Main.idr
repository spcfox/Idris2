data X = MkX Void

matchDelayLazy : Lazy X -> Int
matchDelayLazy (Delay (MkX _)) impossible

omitDelayLazy : Lazy X -> Int
omitDelayLazy (MkX _) impossible

matchDelayInf : Inf X -> Int
matchDelayInf (Delay (MkX _)) impossible

omitDelayInf : Inf X -> Int
omitDelayInf (MkX _) impossible
