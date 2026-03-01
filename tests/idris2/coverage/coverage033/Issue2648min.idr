foo : (b ** (b = False)) -> Void
foo (True ** Refl) impossible

boom : Void
boom = foo (False ** Refl)
