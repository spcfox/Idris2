module Yaffle.REPL

import Core.AutoSearch
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.FC
import Core.Metadata
import Core.Normalise
import Core.Termination
import Core.TT
import Core.Unify

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Interactive.ExprSearch
import TTImp.Interactive.GenerateDef
import TTImp.Parser
import TTImp.ProcessDecls
import TTImp.TTImp
import TTImp.Unelab

import Parser.Source

%default covering

showInfo : (Name, Int, GlobalDef) -> Core ()
showInfo (n, _, d)
    = coreLift $ putStrLn (show n ++ " ==>\n" ++
                  "\t" ++ show (definition d) ++ "\n" ++
                  "\t" ++ show (sizeChange d) ++ "\n")

-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          ImpREPL -> Core Bool
process (Eval ttimp)
    = do (tm, _) <- elabTerm 0 InExpr [] (MkNested []) [] ttimp Nothing
         defs <- get Ctxt
         tmnf <- normalise defs [] tm
         coreLift (printLn !(unelab [] tmnf))
         pure True
process (Check (IVar _ n))
    = do defs <- get Ctxt
         ns <- lookupTyName n (gamma defs)
         traverse_ printName ns
         pure True
  where
    printName : (Name, Int, ClosedTerm) -> Core ()
    printName (n, _, tyh)
        = do defs <- get Ctxt
             ty <- normaliseHoles defs [] tyh
             coreLift $ putStrLn $ show n ++ " : " ++
                                   show !(unelab [] ty)
process (Check ttimp)
    = do (tm, gty) <- elabTerm 0 InExpr [] (MkNested []) [] ttimp Nothing
         defs <- get Ctxt
         tyh <- getTerm gty
         ty <- normaliseHoles defs [] tyh
         coreLift (printLn !(unelab [] ty))
         pure True
process (ProofSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | ns => ambiguousName (justFC defaultFC) n_in (map fst ns)
         def <- search (justFC defaultFC) top False 1000 n ty []
         defs <- get Ctxt
         defnf <- normaliseHoles defs [] def
         coreLift (printLn !(toFullNames defnf))
         pure True
process (ExprSearch n_in)
    = do defs <- get Ctxt
         [(n, i, ty)] <- lookupTyName n_in (gamma defs)
              | ns => ambiguousName (justFC defaultFC) n_in (map fst ns)
         results <- exprSearchN (justFC defaultFC) 1 n []
         traverse_ (coreLift . printLn) results
         pure True
process (GenerateDef line name)
    = do defs <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine line p)
              | Nothing => do coreLift (putStrLn ("Can't find declaration for " ++ show name))
                              pure True
         case !(lookupDefExact n' (gamma defs)) of
              Just None =>
                  catch
                    (do ((fc, cs) :: _) <- logTime 0 "Generation" $
                                makeDefN (\p, n => onLine line p) 1 n'
                           | _ => coreLift (putStrLn "Failed")
                        coreLift $ putStrLn (show cs))
                    (\err => coreLift $ putStrLn $ "Can't find a definition for " ++ show n')
              Just _ => coreLift $ putStrLn "Already defined"
              Nothing => coreLift $ putStrLn $ "Can't find declaration for " ++ show name
         pure True
process (Missing n_in)
    = do defs <- get Ctxt
         case !(lookupCtxtName n_in (gamma defs)) of
              [] => undefinedName emptyFC n_in
              ts => do traverse_ (\fn =>
                          do tot <- getTotality emptyFC fn
                             case isCovering tot of
                                  MissingCases cs =>
                                     coreLift (putStrLn (show fn ++ ":\n" ++
                                               showSep "\n" (map show cs)))
                                  NonCoveringCall ns =>
                                     coreLift (putStrLn
                                         (show fn ++ ": Calls non covering function"
                                           ++ case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ showSep ", " (map show ns)))
                                  _ => coreLift $ putStrLn (show fn ++ ": All cases covered"))
                        (map fst ts)
                       pure True
process (CheckTotal n)
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => undefinedName emptyFC n
              ts => do traverse_ (\fn =>
                          do ignore $ checkTotal emptyFC fn
                             tot <- getTotality emptyFC fn
                             coreLift (putStrLn (show fn ++ " is " ++ show tot)))
                               (map fst ts)
                       pure True
process (DebugInfo n)
    = do defs <- get Ctxt
         traverse_ showInfo !(lookupCtxtName n (gamma defs))
         pure True
process Quit
    = do coreLift $ putStrLn "Bye for now!"
         pure False

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               ImpREPL -> Core Bool
processCatch cmd
    = catch (process cmd)
            (\err => coreLift (putStrLn $ show err) $> True)

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto m : Ref MD Metadata} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core ()
repl
    = do coreLift (putStr "Yaffle> ")
         inp <- coreLift getLine
         case runParser (Virtual Interactive) Nothing inp command of
              Left err => do coreLift (printLn err)
                             repl
              Right (_, _, cmd) => when !(processCatch cmd) repl
