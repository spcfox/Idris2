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

mkSubst : {vars : _} -> (args : List Name) ->
          (0 _ : LengthMatch args dropped) -> Subst Var dropped vars
mkSubst [] NilMatch = []
mkSubst (x :: xs) (ConsMatch m)
  = case isVar x vars of
      Just prf => prf :: mkSubst xs m
      Nothing => believe_me () -- TODO: prove that this can't happen

data MatchResult : Type where
    ConPat   : Name -> (tag : Int) -> List Name -> MatchResult
    DelayPat : (ty, arg : Name) -> MatchResult
    ConstPat : Constant -> MatchResult

export
optimiseTree : {vars : _} -> List (Name, MatchResult) -> CaseTree vars -> CaseTree vars

optimiseAlt : {vars : _} -> List (Name, MatchResult) -> Name -> CaseAlt vars -> CaseAlt vars
optimiseAlt ps nm (ConCase n tag args sc)
    = ConCase n tag args (optimiseTree ((nm, ConPat n tag args) :: ps) sc)
optimiseAlt ps nm (DelayCase ty arg sc)
    = DelayCase ty arg (optimiseTree ((nm, DelayPat ty arg) :: ps) sc)
optimiseAlt ps nm (ConstCase c sc)
    = ConstCase c (optimiseTree ((nm, ConstPat c) :: ps) sc)
optimiseAlt ps _ (DefaultCase sc) = DefaultCase (optimiseTree ps sc)

pickAlt : {vars : _} -> List (Name, MatchResult) -> MatchResult -> List (CaseAlt vars) -> Maybe (CaseTree vars)
pickAlt _ _ [] = Nothing
pickAlt ps p@(ConPat n t args) (ConCase n' t' args' sc :: alts)
    = if t == t' && n == n'
         then checkLengthMatch args args' <&> \match => -- lengths should always match
                optimiseTree ps $ substCaseTree zero (mkSizeOf _) (mkSubst args match) sc
         else pickAlt ps p alts
pickAlt ps (DelayPat ty arg) (DelayCase ty' arg' sc :: _)
    = Just $ optimiseTree ps $ substCaseTree zero (mkSizeOf _) (mkSubst {dropped=[_, _]} [ty, arg] %search) sc
pickAlt ps p@(ConstPat c) (ConstCase c' sc :: alts)
    = if c == c'
         then Just $ optimiseTree ps sc
         else pickAlt ps p alts
pickAlt ps _ (DefaultCase sc :: _) = Just $ optimiseTree ps sc
pickAlt ps p (_ :: alts) = pickAlt ps p alts

optimiseTree ps (Case idx el ty alts)
    = do let name = nameAt el
         fromMaybe (Case idx el ty (map (optimiseAlt ps name) alts)) $ do
           p <- lookup name ps
           pickAlt ps p alts
optimiseTree _ tm = tm
