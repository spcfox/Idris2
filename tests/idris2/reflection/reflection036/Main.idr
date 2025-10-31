module Main

import Control.Monad.State.Interface

import Data.Ref

import Language.Reflection

%default total

action : MonadState Integer m => Elaboration m => Nat -> m Integer
action Z = get
action w@(S n) = logMsg "info" 0 "current: \{show !get}" >> modify (+ natToInteger w) >> action n

%language ElabReflection

x : Integer
x = %runElab do
  ref <- newRef 0
  action @{ForRef ref} 5
