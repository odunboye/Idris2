module Core.Termination.Guarded

-- Guarded recursion checker for clock-based guarded types (Row 41).
--
-- A definition uses guarded recursion if any of its clause RHSs contain
-- a 'TFix' or 'TNext' constructor. For such definitions we ensure recursive
-- self-calls are guarded by a 'TLater' or 'TNext' for the same clock.
--
-- Implementation: Track clock variables during size-change analysis.
-- When we see 'TFix κ body', we record κ as the clock to check.
-- 'TLater κ' and 'TNext κ' transition us into a guarded context for that clock.
-- Recursive calls outside a guarded context are reported as unguarded.

import Core.Case.CaseTree
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Normalise
import Core.Termination.CallGraph
import Core.TT
import Core.TT.Term
import Core.Value

import Data.String

%default covering

-- Check if a term contains TFix (indicating guarded recursion)
export
usesGuardedRecursion : Term vars -> Bool
usesGuardedRecursion (Bind fc n b sc) = usesGuardedRecursion (binderType b) || usesGuardedRecursion sc
usesGuardedRecursion (App fc f a) = usesGuardedRecursion f || usesGuardedRecursion a
usesGuardedRecursion (As fc s a p) = usesGuardedRecursion a || usesGuardedRecursion p
usesGuardedRecursion (TDelayed fc r ty) = usesGuardedRecursion ty
usesGuardedRecursion (TDelay fc r ty tm) = usesGuardedRecursion ty || usesGuardedRecursion tm
usesGuardedRecursion (TForce fc r tm) = usesGuardedRecursion tm
usesGuardedRecursion (TFix fc c body) = True  -- Found a fixpoint!
usesGuardedRecursion (TLater fc c ty) = usesGuardedRecursion c || usesGuardedRecursion ty
usesGuardedRecursion (TNext fc c arg) = usesGuardedRecursion c || usesGuardedRecursion arg
usesGuardedRecursion (TTickAbs fc c body) = usesGuardedRecursion body
usesGuardedRecursion (TTickApp fc fn c) = usesGuardedRecursion fn || usesGuardedRecursion c
usesGuardedRecursion _ = False

-- True iff the definition body contains guarded recursion (TFix or TNext terms).
-- Checks the RHS of each pattern clause, not the type signature.
export
isGuardedRecursive : GlobalDef -> Bool
isGuardedRecursive gdef =
  case definition gdef of
    PMDef _ _ _ _ pats => any (\(_ ** (_, _, rhs)) => usesGuardedRecursion rhs) pats
    _ => False

-- Guardedness state for clock-indexed guarded recursion
-- Similar to Guardedness in CallGraph but tracks which clock we're checking
public export
data GuardedClock = CGTop | CGUnguarded | CGGuarded | CGInLater

-- A guarded recursive call (self-call that was properly guarded)
public export
record GuardedCall where
  constructor MkGuardedCall
  callFn : Name
  callLoc : FC

-- Find unguarded recursive calls in a term.
-- The 'clock' parameter tracks which clock we're checking for (if any).
-- When we see TFix clock body, we enter that clock's scope.
-- When we see TLater clock ty, we enter guarded context.
mutual
  findUnguarded : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  Defs -> Env Term vars -> GuardedClock ->
                  Maybe (Term vars) -> -- The clock we're checking for (if any)
                  Name -> -- The function being checked (for self-call detection)
                  Term vars -> -- The term to check
                  Core (List GuardedCall)
  
  -- Under a binder
  findUnguarded {vars} defs env g mclock self (Bind fc n b sc)
      = do binderSC <- findUnguardedBinder b
           scopeSC <- findUnguarded defs (b :: env) g (map weaken mclock) self sc
           pure (binderSC ++ scopeSC)
    where
      findUnguardedBinder : Binder (Term vars) -> Core (List GuardedCall)
      findUnguardedBinder (Let _ c val ty) = findUnguarded defs env g mclock self val
      findUnguardedBinder _ = pure []

  -- TDelay with LInf is for coinduction, not guarded recursion
  findUnguarded defs env g mclock self (TDelay _ _ _ tm)
      = findUnguarded defs env g mclock self tm
  findUnguarded defs env g mclock self (TDelayed _ _ ty)
      = findUnguarded defs env g mclock self ty
  findUnguarded defs env g mclock self (TForce _ _ tm)
      = findUnguarded defs env CGUnguarded mclock self tm

  -- Row 41: Guarded recursion / clock variables
  -- TLater marks a guarded context for its clock
  findUnguarded defs env g mclock self (TLater fc c ty)
      = do clockSC <- findUnguarded defs env g mclock self c
           -- Check if this TLater guards our target clock
           tySC <- case mclock of
                     Nothing => findUnguarded defs env g Nothing self ty
                     Just targetClock => 
                       if clocksMatch c targetClock
                          then findUnguarded defs env CGInLater mclock self ty
                          else findUnguarded defs env g mclock self ty
           pure (clockSC ++ tySC)

  -- TNext introduces a guarded value
  findUnguarded defs env g mclock self (TNext fc c arg)
      = do clockSC <- findUnguarded defs env g mclock self c
           argSC <- case mclock of
                      Nothing => findUnguarded defs env g Nothing self arg
                      Just targetClock =>
                        if clocksMatch c targetClock
                           then findUnguarded defs env CGInLater mclock self arg
                           else findUnguarded defs env g mclock self arg
           pure (clockSC ++ argSC)

  -- TTickAbs binds a clock variable
  findUnguarded defs env g mclock self (TTickAbs fc c body)
      = findUnguarded defs env g mclock self body

  -- TTickApp applies to a clock
  findUnguarded defs env g mclock self (TTickApp fc fn c)
      = do fnSC <- findUnguarded defs env g mclock self fn
           cSC <- findUnguarded defs env g mclock self c
           pure (fnSC ++ cSC)

  -- TFix is the fixpoint - check body with this clock as target
  findUnguarded defs env g mclock self (TFix fc c body)
      = do clockSC <- findUnguarded defs env g mclock self c
           -- For the body, this clock becomes the target
           bodySC <- findUnguarded defs env CGGuarded (Just c) self body
           pure (clockSC ++ bodySC)

  -- For applications, check for self-calls
  findUnguarded defs env g mclock self tm
      = do let (fn, args) = getFnArgs tm
           -- Check arguments first
           argsSC <- traverse (findUnguarded defs env CGUnguarded mclock self) args
           -- Check if this is a self-call
           selfCallSC <- checkSelfCall fn
           pure (concat argsSC ++ selfCallSC)
    where
      checkSelfCall : Term vars -> Core (List GuardedCall)
      checkSelfCall (Ref fc Func fn)
          = do fnFull <- getFullName fn
               selfFull <- getFullName self
               if fnFull == selfFull
                  then case g of
                         CGInLater => pure []  -- Guarded, OK
                         _ => pure [MkGuardedCall fn fc]  -- Unguarded self-call!
                  else pure []
      checkSelfCall _ = pure []

  -- Check if two clock terms refer to the same clock
  -- For now, simple syntactic equality on local variables
  clocksMatch : Term vars -> Term vars -> Bool
  clocksMatch (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
  clocksMatch (Ref _ _ n) (Ref _ _ n') = n == n'
  clocksMatch _ _ = False  -- Conservative: assume different

-- Find unguarded calls from a pattern clause
findUnguardedCalls : {auto c : Ref Ctxt Defs} ->
                     Defs -> Name ->
                     (vs ** (Env Term vs, Term vs, Term vs)) ->
                     Core (List GuardedCall)
findUnguardedCalls defs self (_ ** (env, lhs, rhs))
    = do rhsNorm <- normaliseOpts tcOnly defs env rhs
         findUnguarded defs env CGTop Nothing self (delazy defs rhsNorm)

-- Check productivity of guarded recursive definition 'n'.
-- Returns NotTerminating (NotProductive calls) if there are unguarded self-calls.
export
calcGuarded : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Core Terminating
calcGuarded loc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
             | Nothing => undefinedName loc n
         -- Get the pattern clauses
         let pats = case definition def of
                      PMDef _ _ _ _ ps => ps
                      _ => []
         -- Find unguarded recursive calls in each clause
         unguarded <- traverse (findUnguardedCalls defs n) pats
         let allUnguarded = concat unguarded
         if isNil allUnguarded
            then pure IsTerminating
            else pure $ NotTerminating $ NotProductive $ 
                        map (\(MkGuardedCall fn fc) => (fc, fn)) allUnguarded

-- Memoising wrapper: skip re-checking if already computed.
export
checkGuarded : {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Core Terminating
checkGuarded loc n
    = do tot <- getTotality loc n
         case isTerminating tot of
              Unchecked =>
                  do tot' <- calcGuarded loc n
                     setTerminating loc n tot'
                     pure tot'
              t => pure t
