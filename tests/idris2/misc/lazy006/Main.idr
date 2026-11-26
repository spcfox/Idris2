%auto_lazy off

foo : Lazy ()
foo = ()

bar : Lazy () -> ()
bar x = x
