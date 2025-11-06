module Main

import Control.Monad.State.Interface

import Data.Ref

import Language.Reflection

%default total

action : MonadState Integer m => Elaboration m => Nat -> m Integer
action Z = get
action w@(S n) = do
  v <- get
  logMsg "info" 0 "current: \{show v}"
  modify (+ natToInteger w)
  action n

%language ElabReflection

%runElab do
  ref <- newRef 0
  res <- action @{ForRef ref} 5
  logMsg "info" 0 $ "result: \{show res}"
