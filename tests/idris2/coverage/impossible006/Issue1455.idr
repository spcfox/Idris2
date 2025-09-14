data PrimRep
  = VoidRep
  | LiftedRep

data DataConRep
  = AlgDataCon      (List PrimRep)
  | UnboxedTupleCon Nat

data DataConId : DataConRep -> Type where
  MkDataConId : {0 r : DataConRep} -> DataConId r

DataConIdSg : Type
DataConIdSg = (r : DataConRep ** DataConId r)

data RepType = SingleValue PrimRep

data AltCon : RepType -> Type where
  AltDataCon : DataConIdSg                     -> AltCon (SingleValue LiftedRep)
  AltDefault : {0 r : RepType}                 -> AltCon r

data SBinder : RepType -> Type where
  MkSBinder
    :  (binderName : String)
    -> SBinder binderRep

DataConRepType : DataConRep -> Type
DataConRepType (AlgDataCon [])     = ()
DataConRepType (AlgDataCon [p])    = SBinder (SingleValue p)
DataConRepType (AlgDataCon (p0 :: p1 :: ps)) = Void
DataConRepType (UnboxedTupleCon n) = Void

AltBinderType : AltCon r -> Type
AltBinderType (AltDataCon d) = DataConRepType (fst d)
AltBinderType AltDefault = ()

data Alt : (altConRep : RepType) -> (exprRep : RepType) -> Type where
  MkAlt
    :  (a : AltCon ar)
    -> (bs : AltBinderType a)
    -> Alt ar er

issueWithPatternMatch : Alt r q -> Int
issueWithPatternMatch (MkAlt AltDefault ()) = 1
issueWithPatternMatch (MkAlt (AltDataCon ((UnboxedTupleCon _) ** _)) unboxed) impossible
issueWithPatternMatch (MkAlt alt@(AltDataCon ((AlgDataCon []) ** _)) binders) = 2
