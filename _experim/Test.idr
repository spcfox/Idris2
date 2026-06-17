import Language.Reflection

%language ElabReflection

-- Note: this example doesn't quite do what we want yet. Ideally, we'd find
-- a way to block reduction under the 'pure' while running the script
powerFn' : Nat -> Elab (Nat -> Nat)
powerFn' Z = pure (const 1)
powerFn' (S k)
    = do powerk <- powerFn' k
         pure (\x => mult (powerk x) x)

%macro
power' : Nat -> Elab (Nat -> Nat)
power' n = powerFn' n

p0 : Nat -> Nat
p0 = power' 0

p1 : Nat -> Nat
p1 = power' 1

p2 : Nat -> Nat
p2 = power' 2
