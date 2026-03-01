module Core.Case.Util

import Core.Case.CaseTree
import Core.Context
import Core.Value

import Libraries.Data.List.SizeOf

public export
record DataCon where
  constructor MkDataCon
  name  : Name
  tag   : Int
  arity : Nat

||| Given a normalised type, get all the possible constructors for that
||| type family, with their type, name, tag, and arity.
export
getCons : Ref Ctxt Defs => Context -> Name -> Core (Maybe (List DataCon))
getCons gam tn
    = case !(lookupDefExact tn gam) of
           Just (TCon _ _ _ _ _ cons _) => traverseOpt (traverse addTy) cons
           _ => throw $ InternalError $ "Called `getCons` on non-type constructor: " ++ show !(toFullNames tn)
  where
    addTy : Name -> Core DataCon
    addTy cn
        = do Just gdef <- lookupCtxtExact cn gam
                  | Nothing => throw (UndefinedName emptyFC cn)
             case (gdef.definition, gdef.type) of
                  (DCon t arity _, ty) => pure $ MkDataCon cn t arity
                  _ => throw $ InternalError $ "Called `addTy` on non-data constructor: " ++ show !(toFullNames cn)

emptyRHS : FC -> CaseTree vars -> CaseTree vars
emptyRHS fc (Case idx el sc alts) = Case idx el sc (map emptyRHSalt alts)
  where
    emptyRHSalt : CaseAlt vars -> CaseAlt vars
    emptyRHSalt (ConCase n t args sc) = ConCase n t args (emptyRHS fc sc)
    emptyRHSalt (DelayCase c arg sc) = DelayCase c arg (emptyRHS fc sc)
    emptyRHSalt (ConstCase c sc) = ConstCase c (emptyRHS fc sc)
    emptyRHSalt (DefaultCase sc) = DefaultCase (emptyRHS fc sc)
emptyRHS fc (STerm i s) = STerm i (Erased fc Placeholder)
emptyRHS fc sc = sc

export
mkAlt : FC -> CaseTree vars -> DataCon -> CaseAlt vars
mkAlt fc sc (MkDataCon cn t ar)
    = ConCase cn t (map (MN "m") (take ar [0..]))
              (weakenNs (map take) (emptyRHS fc sc))

export
tagIs : Int -> CaseAlt vars -> Bool
tagIs t (ConCase _ t' _ _) = t == t'
tagIs t (ConstCase {}) = False
tagIs t (DelayCase {}) = False
tagIs t (DefaultCase _) = True

export
unfoldDefault : FC -> List DataCon -> CaseAlt vars -> Core (List (CaseAlt vars))
unfoldDefault fc allCons (DefaultCase sc) = pure $ map (mkAlt fc sc) allCons
unfoldDefault _ _ c = pure [c]
