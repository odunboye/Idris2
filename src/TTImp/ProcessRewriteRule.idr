module TTImp.ProcessRewriteRule

-- Row 33: %rewrite — promote an equality proof to a definitional rewrite rule.
--
-- Usage: %rewrite "lemmaName"
--
-- The lemma must have type of the form
--   (x1 : T1) -> ... -> (xn : Tn) -> lhs = rhs
-- After processing, every occurrence of `lhs` (with xi as pattern
-- variables) will be rewritten to `rhs` in the conversion fallback.

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Normalise.Eval
import Core.Normalise.Quote
import Core.Transform
import Core.TT
import Core.Value

%default covering

-- Peel Pi binders off the front of a term, accumulating an Env.
-- Returns (vars' ** (env, body)) where env : Env Term vars'
-- and body : Term vars', with the Pi-bound names as de Bruijn locals.
peelPis : {vars : _} -> Env Term vars -> Term vars ->
          (vars' ** (Env Term vars', Term vars'))
peelPis env (Bind _ _ binder@(Pi _ _ _ _) sc) = peelPis (binder :: env) sc
peelPis env tm = (_ ** (env, tm))

-- Given a term in scope vars (after Pi-peeling), normalise it and check
-- whether it is an application of the equality type constructor.
-- If so, return (lhsTm, rhsTm) both in scope vars.
extractEqSides : {auto c : Ref Ctxt Defs} -> {vars : _} ->
                 Defs -> Env Term vars -> Term vars ->
                 Core (Maybe (Term vars, Term vars))
extractEqSides defs env body
    = do nfBody <- nf defs env body
         case nfBody of
              NTCon _ eqName _ args =>
                do True <- isEqualTy eqName
                       | False => pure Nothing
                   case reverse (map snd args) of
                        (rhs_c :: lhs_c :: _) =>
                          do lhsTm <- quote defs env !(evalClosure defs lhs_c)
                             rhsTm <- quote defs env !(evalClosure defs rhs_c)
                             pure (Just (lhsTm, rhsTm))
                        _ => pure Nothing
              _ => pure Nothing

||| Register an equality lemma as a definitional rewrite rule.
|||
||| Looks up `lemmaName` in the context, peels its Pi-telescope, extracts
||| the LHS and RHS of the innermost equality, and calls `addTransform`.
||| The LHS head function determines which transforms fire during
||| conversion checking (via `applyTransforms` in the Convert fallback).
export
processRewriteRule : {auto c : Ref Ctxt Defs} ->
                     FC -> Name -> Core ()
processRewriteRule fc lemmaName
    = do defs <- get Ctxt
         ns <- lookupCtxtName lemmaName (gamma defs)
         case ns of
              [] => throw (UndefinedName fc lemmaName)
              (_ :: _ :: _) => throw (AmbiguousName fc (map (\(n, _, _) => n) ns))
              [(fullName, _, gdef)] =>
                do let (_ ** (env, body)) = peelPis [] (type gdef)
                   Just (lhsTm, rhsTm) <- extractEqSides defs env body
                       | Nothing => throw (GenericMsg fc $
                           "Type of " ++ show lemmaName ++
                           " is not an equality: expected (a = b) or " ++
                           "Pi .. -> ... -> a = b")
                   addTransform fc (MkTransform fullName env lhsTm rhsTm)
                   log "rewrite.rule" 3 $
                       "Added rewrite rule from " ++ show fullName
