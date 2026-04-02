module Core.Termination.Productivity

-- Guardedness / productivity checker for corecursive definitions.
--
-- A definition is corecursive if its declared return type is `Inf A`
-- (i.e., the outermost return type is `TDelayed _ LInf _` after stripping
-- Pi binders).  For such definitions the size-change termination check is
-- replaced by a productivity check: every recursive self-call must be
-- guarded by at least one `TDelay LInf` constructor.
--
-- Implementation: re-use the existing `findSC` machinery but start the
-- traversal at `Guarded` instead of `Toplevel`.  A `TDelay LInf` term
-- seen in `Guarded` state transitions into `InDelay`; recursive calls
-- reached in `InDelay` state are *not* recorded as `SCCall`s (they are
-- productive).  Any self-call that *does* appear in the resulting
-- `SCCall` list was reached outside a `Delay` guard and is therefore
-- unguarded.

import Core.Context
import Core.Context.Log
import Core.Normalise
import Core.Termination.CallGraph
import Core.TT
import Core.TT.Term

%default covering

-- Walk a term stripping leading Pi binders and report whether the
-- eventual return position is `TDelayed _ LInf _`.
-- Works for any `vars`, so it can recurse through the scope of a Bind.
returnTypeIsInf : {vars : _} -> Term vars -> Bool
returnTypeIsInf (Bind _ _ (Pi {}) sc) = returnTypeIsInf sc
returnTypeIsInf (TDelayed _ LInf _)   = True
returnTypeIsInf _                     = False

-- True iff the declared type of a definition returns `Inf A`.
export
isCorecursive : GlobalDef -> Bool
isCorecursive gdef = returnTypeIsInf gdef.type

-- Check productivity of `n` by running the SC-call analysis from the
-- `Guarded` initial state.  Any self-call that surfaces in the resulting
-- SCCall list was not guarded by a `Delay` and is therefore unguarded.
export
calcProductive : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Core Terminating
calcProductive loc n
    = do defs <- get Ctxt
         logC "totality.productivity.calc" 7 $
             pure $ "Calculating productivity: " ++ show !(toFullNames n)
         Just def <- lookupCtxtExact n (gamma defs)
             | Nothing => undefinedName loc n
         -- Use the fully-qualified name for comparison with SCCall callees
         fn <- getFullName n
         scs <- getSCFrom defs Guarded (definition def)
         -- Collect self-calls: any SCCall whose callee is `fn`
         let unguarded = mapMaybe (selfCall fn) scs
         if isNil unguarded
            then pure IsTerminating
            else pure $ NotTerminating (NotProductive unguarded)
  where
    selfCall : Name -> SCCall -> Maybe (FC, Name)
    selfCall self (MkSCCall callee _ fc)
        = if callee == self then Just (fc, callee) else Nothing

-- Memoising wrapper: skip re-checking if already computed.
export
checkProductive : {auto c : Ref Ctxt Defs} ->
                  FC -> Name -> Core Terminating
checkProductive loc n
    = do tot <- getTotality loc n
         logC "totality.productivity" 6 $
             pure $ "Checking productivity: " ++ show !(toFullNames n)
         case isTerminating tot of
              Unchecked =>
                  do tot' <- calcProductive loc n
                     setTerminating loc n tot'
                     pure tot'
              t => pure t
