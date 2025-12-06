module Core.Case.Optimise

import Core.Name.Scoped
import Core.TT.Primitive
import Core.TT.Subst
import Core.TT.Var
import public Core.Case.CaseTree

import Data.Maybe
import Data.List
import Libraries.Data.List.LengthMatch
import Libraries.Data.List.SizeOf

mkSubst : {vars : _} -> (args : List (Var vars)) ->
          (0 _ : LengthMatch args dropped) -> Subst Var dropped vars
mkSubst [] NilMatch = []
mkSubst (x :: xs) (ConsMatch m) = x :: mkSubst xs m

data MatchResult : Scoped where
    ConPat   : Name -> (tag : Int) -> List (Var vars) -> MatchResult vars
    DelayPat : (ty, arg : Var vars) -> MatchResult vars
    ConstPat : Constant -> MatchResult vars

Weaken MatchResult where
  weakenNs s (ConPat n tag args) = ConPat n tag (weakenNs s <$> args)
  weakenNs s (DelayPat ty arg) = DelayPat (weakenNs s ty) (weakenNs s arg)
  weakenNs s (ConstPat c) = ConstPat c

export
optimiseTree : {vars : _} -> List (Var vars, MatchResult vars) -> CaseTree vars -> Maybe (CaseTree vars)

optimiseAlts : {vars : _} -> List (Var vars, MatchResult vars) ->
               Var vars -> List (CaseAlt vars) ->
               (List (Maybe (CaseAlt vars)), Maybe (CaseTree vars))
optimiseAlts ps v [] = ([], Nothing)
optimiseAlts ps v (ConCase n tag args sc :: alts)
    = do let sz = mkSizeOf args
         let v' = weakenNs sz v
         let ps' = map (bimap (weakenNs sz) (weakenNs sz)) ps
         let args' = allVarsPrefix sz
         let alt = ConCase n tag args <$> optimiseTree ((v', ConPat n tag args') :: ps') sc
         mapFst (alt ::) (optimiseAlts ps v alts)
optimiseAlts ps v (DelayCase ty arg sc :: alts)
    = do let sz = mkSizeOf [ty, arg]
         let v' = weakenNs sz v
         let ps' = map (bimap (weakenNs sz) (weakenNs sz)) ps
         let alt = DelayCase ty arg <$> optimiseTree ((v', DelayPat first (later first)) :: ps') sc
         mapFst (alt ::) (optimiseAlts ps v alts)
optimiseAlts ps v (ConstCase c sc :: alts)
    = do let alt = ConstCase c <$> optimiseTree ((v, ConstPat c) :: ps) sc
         mapFst (alt ::) (optimiseAlts ps v alts)
optimiseAlts ps _ (DefaultCase sc :: _)
    = ([], optimiseTree ps sc)

pickAlt : {vars : _} -> List (Var vars, MatchResult vars) ->
          MatchResult vars -> List (CaseAlt vars) -> Maybe (CaseTree vars)
pickAlt _ _ [] = Nothing
pickAlt ps p@(ConPat n t args) (ConCase n' t' args' sc :: alts)
    = if t == t' && n == n'
         then do match <- checkLengthMatch args args' -- lengths should always match
                 optimiseTree ps $ substCaseTree zero (mkSizeOf _) (mkSubst args match) sc
         else pickAlt ps p alts
pickAlt ps (DelayPat ty arg) (DelayCase ty' arg' sc :: _)
    = do let subst : Subst Var [ty', arg'] vars = mkSubst [ty, arg] %search
         optimiseTree ps $ substCaseTree zero (mkSizeOf _) subst sc
pickAlt ps p@(ConstPat c) (ConstCase c' sc :: alts)
    = if c == c'
         then optimiseTree ps sc
         else pickAlt ps p alts
pickAlt ps _ (DefaultCase sc :: _) = optimiseTree ps sc
pickAlt ps p (_ :: alts) = pickAlt ps p alts

optimiseTree ps (Case idx el ty alts)
    = do let var = MkVar el
         case lookup var ps of
           Just p => pickAlt ps p alts
           Nothing => case mapFst catMaybes $ optimiseAlts ps var alts of
                           ([], def) => def
                           (alts, Nothing) => Just $ Case idx el ty alts
                           (alts, Just def) =>
                               Just $ Case idx el ty $ alts ++ [DefaultCase def]
optimiseTree _ tm = Just tm
