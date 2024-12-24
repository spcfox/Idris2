module Idris.Syntax.Views

import Idris.Syntax
import Idris.Syntax.Builtin

%default total

export
getFnArgs : (Name -> nm) -> PTerm' nm -> (PTerm' nm, List (PArg' nm))
getFnArgs embed fts = go fts [] where

  go : PTerm' nm -> List (PArg' nm) -> (PTerm' nm, List (PArg' nm))
  go (PApp fc f t) = go f . (Explicit fc t ::)
  go (PAutoApp fc f t) = go f . (Auto fc t ::)
  go (PNamedApp fc f n t) = go f . (Named fc n t ::)
  go (PBracketed fc f) = go f
  -- we don't care about the binder info here
  go (POp fc leftSide op r) =
    (PRef op.fc op.val.toName,) . (Explicit fc leftSide.val.getLhs ::) . (Explicit fc r ::)
  go (PEq fc l r) = (PRef fc $ embed eqName,) . (Explicit fc l ::) . (Explicit fc r ::)
  -- ambiguous, picking the type constructor here
  go (PPair fc l r) = (PRef fc $ embed pairname,) . (Explicit fc l ::) . (Explicit fc r ::)
  go (PDPair full fc l ty r)
    = (PRef fc $ embed dpairname,)
    . (Explicit fc l ::) . (Explicit fc ty ::) . (Explicit fc r ::)
  go f = (f,)

export
underPis : PTerm' nm -> (List (Maybe Name, Binder (PTerm' nm)), PTerm' nm)
underPis abs = go abs [] where

  go : PTerm' nm -> List (Maybe Name, Binder (PTerm' nm)) ->
       (List (Maybe Name, Binder (PTerm' nm)), PTerm' nm)
  go (PPi fc rig pinfo mn a b) = go b . ((mn, Pi fc rig pinfo a) ::)
  go (PBracketed fc abs) = go abs
  go abs = (, abs)

export
underLams : PTerm' nm -> (List (PTerm' nm, Binder (PTerm' nm)), PTerm' nm)
underLams fs = go fs [] where

  go : PTerm' nm -> List (PTerm' nm, Binder (PTerm' nm)) ->
       (List (PTerm' nm, Binder (PTerm' nm)), PTerm' nm)
  go (PBracketed fc f) = go f
  go (PLam fc rig pinfo pat a sc) = go sc . ((pat, Lam fc rig pinfo a) ::)
  go fs = (,fs)
