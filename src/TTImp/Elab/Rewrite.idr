module TTImp.Elab.Rewrite

import Core.Env
import Core.GetType
import Core.Metadata
import Core.Unify
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

import Libraries.Data.List.SizeOf

%default covering

-- TODO: Later, we'll get the name of the lemma from the type, if it's one
-- that's generated for a dependent type. For now, always return the default
findRewriteLemma : {auto c : Ref Ctxt Defs} ->
                   FC -> (rulety : Term vars) ->
                   Core Name
findRewriteLemma loc rulety
   = case !getRewrite of
          Nothing => throw (GenericMsg loc "No rewrite lemma defined")
          Just n => pure n

getRewriteTerms : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  FC -> Defs -> NF vars -> Error ->
                  Core (NF vars, NF vars, NF vars)
getRewriteTerms loc defs (NTCon nfc eq a args) err
    = if !(isEqualTy eq)
         then case reverse $ map snd args of
                   (rhs :: lhs :: rhsty :: lhsty :: _) =>
                        pure (!(evalClosure defs lhs),
                              !(evalClosure defs rhs),
                              !(evalClosure defs lhsty))
                   _ => throw err
         else throw err
getRewriteTerms loc defs ty err
    = throw err

rewriteErr : Error -> Bool
rewriteErr (NotRewriteRule {}) = True
rewriteErr (RewriteNoChange {}) = True
rewriteErr (InType _ _ err) = rewriteErr err
rewriteErr (InCon _ err) = rewriteErr err
rewriteErr (InLHS _ _ err) = rewriteErr err
rewriteErr (InRHS _ _ err) = rewriteErr err
rewriteErr (WhenUnifying _ _ _ _ _ err) = rewriteErr err
rewriteErr _ = False

record Lemma vars where
  constructor MkLemma
  ||| The name of the rewriting lemma
  name : Name
  ||| The predicate (\ v => lhs === rhs) to pass to it
  pred : Term vars
  ||| The type ((v : ?) -> Type) of the predicate
  predTy : Term vars
  lhs : Term vars
  rhs : Term vars
  type : Term vars
  returnType : Glued vars

elabRewrite : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> Env Term vars ->
              (expected : Term vars) ->
              (rulety : Term vars) ->
              Core (Lemma vars)
elabRewrite loc env expected rulety
    = do defs <- get Ctxt
         parg <- genVarName "rwarg"
         tynf <- nf defs env rulety
         (lt, rt, lty) <- getRewriteTerms loc defs tynf (NotRewriteRule loc env rulety)
         lemn <- findRewriteLemma loc rulety

         -- Need to normalise again, since we might have been delayed and
         -- the metavariables might have been updated
         expnf <- nf defs env expected

         logNF "elab.rewrite" 5 "Rewriting, lt" env lt
         logNF "elab.rewrite" 5 "Rewriting, rt" env rt
         logNF "elab.rewrite" 5 "Rewriting, lty" env lty
         logNF "elab.rewrite" 5 "Rewriting, expected" env expnf
         rwexp_sc <- replace defs env lt (Ref loc Bound parg) expnf
         logTerm "elab.rewrite" 5 "Rewritten to" rwexp_sc

         empty <- clearDefs defs
         let pred = Bind loc parg (Lam loc top Explicit
                          !(quote empty env lty))
                          (refsToLocals (Add parg parg None) rwexp_sc)
         gpredty <- getType env pred
         predty <- getTerm gpredty
         exptm <- quote defs env expected

         logTerm "elab.rewrite" 5 "Predicate" pred

         rwexp <- replace defs env lt !(quote empty env rt) expnf

         -- if the rewritten expected type converts with the original,
         -- then the rewrite did nothing, which is an error
        --  when !(convert defs env rwexp_sc exptm) $
        --      throw (RewriteNoChange loc env rulety exptm)
         pure $ MkLemma lemn pred predty !(quote defs env lt) !(quote defs env rt) !(quote defs env lty) (gnf env rwexp)

export
checkRewrite : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> RawImp -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkRewrite rigc elabinfo nest env fc rule tm Nothing
    = throw (GenericMsg fc "Can't infer a type for rewrite")
checkRewrite {vars} rigc elabinfo nest env ifc rule tm (Just expected)
    = delayOnFailure ifc rigc env (Just expected) rewriteErr Rewrite $ \delayed =>
        do let vfc = virtualiseFC ifc

           constart <- getNextEntry
           (rulev, grulet) <- check erased elabinfo nest env rule Nothing
           solveConstraintsAfter constart inTerm Normal

           rulet <- getTerm grulet
           expTy <- getTerm expected
           when delayed $ log "elab.rewrite" 5 "Retrying rewrite"
           lemma <- elabRewrite vfc env expTy rulet

          --  rname <- genVarName "_"
          --  pname <- genVarName "_"

          --  let pbind = Let vfc erased lemma.pred lemma.predTy
          --  let rbind = Let vfc erased (weaken rulev) (weaken rulet)

          --  let env' = rbind :: pbind :: env

           log "elab.rewrite" 5 $ "Check term " ++ show tm
           logTerm "elab.rewrite" 5 "  as type" !(getTerm lemma.returnType)
          --  (tmval, _) <- check erased elabinfo nest env tm Nothing
           (tmval, _) <- check erased elabinfo nest env tm $ Just lemma.returnType
           log "elab.rewrite" 5 "Term checked"

           let rtm = apply vfc (Ref vfc Func lemma.name)
                        [ lemma.type
                        , lemma.lhs
                        , lemma.rhs
                        , lemma.pred
                        , rulev
                        , tmval
                        ]
          --  let rtm = Ref vfc Func lemma.name

           logTerm "elab.rewrite" 5 "Rewriting with" rtm
           logTerm "elab.rewrite" 5 "Return type" !(getTerm lemma.returnType)
           logTerm "elab.rewrite" 5 "Expected type" !(getTerm expected)

           pure (rtm, expected)

           -- Nothing we do in this last part will affect the EState,
           -- we're only doing the application this way to make sure the
           -- implicits for the rewriting lemma are in the right place. But,
           -- we still need the right type for the EState, so weaken it once
           -- for each of the let bindings above.
          --  (rwtm, grwty) <-
          --     inScope vfc (pbind :: env) $ \e' =>
          --       inScope {e=e'} vfc env' $ \e'' =>
          --         let offset = mkSizeOf [rname, pname] in
          --         check {e = e''} rigc elabinfo (weakenNs offset nest) env'
          --           (apply (IVar vfc lemma.name)
          --             [ IVar vfc pname
          --             , IVar vfc rname
          --             , tm ])
          --           (Just (gnf env' (weakenNs offset expTy)))
          --  rwty <- getTerm grwty
          --  let binding = Bind vfc pname pbind . Bind vfc rname rbind
          --  pure (binding rwtm, gnf env (binding rwty))
