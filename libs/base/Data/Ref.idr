module Data.Ref

import public Data.IORef
import public Control.Monad.ST
import Control.Monad.Reader.Interface
import Control.Monad.State.Interface
import Control.Monad.Writer.Interface

%default total

public export
interface Monad m => Ref m r | m where
  newRef : {0 a : Type} -> a -> m (r a)
  readRef : {0 a : Type} -> r a -> m a
  writeRef : r a -> a -> m ()

  ||| Updates a value and returns the previous value
  modifyRef : (a -> a) -> r a -> m a
  modifyRef f ref = do
    old <- readRef ref
    writeRef ref (f old) $> old

public export
modifyRef_ : Ref m r => (a -> a) -> r a -> m ()
modifyRef_ = ignore .: modifyRef

export
HasIO io => Ref io IORef where
  newRef = newIORef
  readRef = readIORef
  writeRef = writeIORef

export
Ref (ST s) (STRef s) where
  newRef = newSTRef
  readRef = readSTRef
  writeRef = writeSTRef

namespace MonadState

  ||| Implementation of `MonadState` that stores the state in a given `Ref`.
  export
  ForRef : Ref m r => Monad m => r a -> MonadState a m
  ForRef ref = MS where
    %inline
    [MS] MonadState a m where
      get = readRef ref
      put = writeRef ref

namespace MonadReader

  ||| Implementation of `MonadReader` that gets the value from a given `Ref`.
  |||
  ||| This implementation assumes strictly sequential (single-thread) execution in monad `m` if `local` is used.
  export
  ForRef : Ref m r => Monad m => r a -> MonadReader a m
  ForRef ref = MR where
    %inline
    [MR] MonadReader a m where
      ask = readRef ref
      local f act = do
        oldA <- modifyRef f ref
        act <* writeRef ref oldA

namespace MonadWriter

  ||| Implementation of `MonadWriter` that stores the resulting value in a given `Ref`.
  |||
  ||| This implementation assumes strictly sequential (single-thread) execution in monad `m` if `listen` is used.
  export
  ForRef : Ref m r => Monad m => Monoid a => r a -> MonadWriter a m
  ForRef ref = MW where
    %inline
    [MW] MonadWriter a m where
      tell val = modifyRef_ (<+> val) ref
      pass act = act >>= \(res, f) => modifyRef f ref $> res
      listen act = do
        oldW <- modifyRef (const neutral) ref
        [| (act, modifyRef (oldW <+>) ref) |]
