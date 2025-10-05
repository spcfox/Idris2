module Core.Evaluate.Expand

import Core.Context
import Core.Env
import Core.Context.Log
import Core.Evaluate.Value
import Core.Primitives
import Core.Evaluate.Quote

import Data.Vect
import Data.SnocList
import Libraries.Data.WithDefault


-- If a value is an App or Meta node, then it might be reducible. Expand it
-- just enough that we have the right top level node.
-- Don't expand Apps to a blocked top level cases, unless 'cases' is set.
-- The 'believe_me' are there to save us deconstructing and reconstructing
-- just to change a compile-time only index
expand' : {auto c : Ref Ctxt Defs} ->
          {vars: _} ->
          Bool -> Value f vars -> Core (NF vars)
expand' cases v@(VApp fc nt n sp val)
    = do vis <- getVisibilityWeaked fc n
         m_mult <- getMultiplicityWeaked fc n
         full_name <- toFullNames n
         defs <- get Ctxt
         let ns = currentNS defs :: nestedNS defs
         logC "eval.def.stuck" 50 $ pure "expand App ns: \{show ns}, n: \{show n}, vis: \{show $ collapseDefault vis}, mult: \{show m_mult}, full_name: \{show full_name}"
         if reducibleInAny ns n (collapseDefault vis)
            then do
               Just val' <- logDepth val
                    | Nothing => pure (believe_me v)
               logC "eval.def.stuck" 50 $ do val' <- toFullNames val'
                                             pure "Reduced \{show full_name} to \{show val'}"
               if cases
                  then expand' cases val'
                  else if !(blockedApp val')
                          then pure (believe_me v)
                          else expand' cases val'
            else pure (believe_me v)
  where
    blockedApp : forall f . Value f vars -> Core Bool
    blockedApp (VBind fc _ (Lam {}) sc)
        = blockedApp !(sc $ pure $ VErased fc Placeholder)
    blockedApp (VCase _ PatMatch _ _ _ _) = pure True
    blockedApp (VPrimOp{}) = pure True
    blockedApp _ = pure False

expand' cases (VErased why (Dotted t))
    = do t' <- expand' cases t
         pure (VErased why (Dotted t'))
expand' cases v@(VMeta fc n i args sp val)
    = do logC "eval.def.stuck" 50 $ pure "expand Meta n: \{show n}"
         Just val' <- logDepth val
              | Nothing => pure (believe_me v)
         logC "eval.def.stuck" 50 $ do n' <- toFullNames n
                                       val' <- toFullNames val'
                                       pure "Reduced \{show n'} to \{show val'}"
         expand' cases val'
expand' cases val = pure (believe_me val)

export
expand : {auto c : Ref Ctxt Defs} ->
         {vars: _} ->
         Value f vars -> Core (NF vars)
expand = expand' False

export
expandFull : {auto c : Ref Ctxt Defs} ->
             {vars: _} ->
             Value f vars -> Core (NF vars)
expandFull = expand' True

export
spineVal : {auto c : Ref Ctxt Defs} ->
           {vars: _} ->
           SpineEntry vars -> Core (NF vars)
spineVal e = expand !(value e)
