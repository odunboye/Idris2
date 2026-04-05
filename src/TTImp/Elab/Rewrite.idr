module TTImp.Elab.Rewrite

import Core.Env
import Core.GetType
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

import Libraries.Data.List.SizeOf

%default covering

-- Check whether a Term contains a Meta node that is a *Delayed* elaboration
-- hole (as opposed to a regular unification meta / Hole).
--
-- Background: when a goal contains a `Delayed` hole, the case-blocks in the
-- goal cannot be reduced yet. Firing auto-sym (strategy 2) in that situation
-- would apply the rule in the *wrong direction* before the hole is resolved.
-- We therefore block strategy 2 until the hole is gone.
--
-- Regular unification metas (`Hole`) are fine: they can be the *target* of
-- auto-sym (e.g. goal `Vect (S ?n) a` where auto-sym finds `rt = S m`).
goalHasDelayed : {auto c : Ref Ctxt Defs} ->
                 {vars : _} ->
                 Term vars -> Core Bool
goalHasDelayed (Meta _ _ idx _)
    = do defs <- get Ctxt
         case !(lookupDefExact (Resolved idx) (gamma defs)) of
              Just Delayed => pure True
              _ => pure False
goalHasDelayed (App _ f a)
    = do r <- goalHasDelayed f
         if r then pure True else goalHasDelayed a
goalHasDelayed (Bind _ _ b sc)
    = do r <- goalHasDelayed (binderType b)
         if r then pure True else goalHasDelayed sc
goalHasDelayed _ = pure False

-- Return the homogeneous rewrite lemma name registered via %rewrite.
findRewriteLemma : {auto c : Ref Ctxt Defs} ->
                   FC -> Core Name
findRewriteLemma loc
   = case !getRewrite of
          Nothing => throw (GenericMsg loc "No rewrite lemma defined")
          Just n  => pure n

-- Return the heterogeneous rewrite lemma name registered via %hrewrite, if any.
findHRewriteLemma : {auto c : Ref Ctxt Defs} ->
                    FC -> Core (Maybe Name)
findHRewriteLemma loc = getHRewrite

-- Extract (lhs, rhs, lhsty, rhsty) from a normalised equality type.
getRewriteTerms : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  FC -> Defs -> NF vars -> Error ->
                  Core (NF vars, NF vars, NF vars, NF vars)
getRewriteTerms loc defs (NTCon nfc eq a args) err
    = if !(isEqualTy eq)
         then case reverse $ map snd args of
                   (rhs :: lhs :: rhsty :: lhsty :: _) =>
                        pure (!(evalClosure defs lhs),
                              !(evalClosure defs rhs),
                              !(evalClosure defs lhsty),
                              !(evalClosure defs rhsty))
                   _ => throw err
         else throw err
getRewriteTerms loc defs ty err = throw err

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
  ||| The name of the rewriting lemma (rewrite__impl or hrewrite__impl)
  name : Name
  ||| The predicate to pass to the lemma.
  |||   Homo:   \v        => goal[lhs := v]
  |||   Hetero: \T => \v  => goal[lhsty := T][lhs := v]
  pred : Term vars
  ||| The type of pred
  predTy : Term vars
  ||| Whether the rule should be applied sym (backwards).
  ||| When True, checkRewrite wraps the proof with sym.
  symRule : Bool

-- Pure check: does the term contain a reference to the named bound variable?
-- Used to determine whether `replace` actually found and substituted the
-- search term, without the side-effecting unification of `convert`.
termContainsRef : Name -> Term vars -> Bool
termContainsRef n (Ref _ _ n')         = n == n'
termContainsRef n (App _ f a)           = termContainsRef n f || termContainsRef n a
termContainsRef n (Bind _ _ b sc)       = termContainsRef n (binderType b) || termContainsRef n sc
termContainsRef n (Meta _ _ _ args)     = any (termContainsRef n) args
termContainsRef n (As _ _ a p)          = termContainsRef n a  || termContainsRef n p
termContainsRef n (TDelayed _ _ t)      = termContainsRef n t
termContainsRef n (TDelay _ _ ty tm)    = termContainsRef n ty || termContainsRef n tm
termContainsRef n (TForce _ _ t)        = termContainsRef n t
termContainsRef n (TFix _ c b)          = termContainsRef n c  || termContainsRef n b
termContainsRef n (TLater _ c t)        = termContainsRef n c  || termContainsRef n t
termContainsRef n (TNext _ c v)         = termContainsRef n c  || termContainsRef n v
termContainsRef n (TTickAbs _ v b)      = termContainsRef n v  || termContainsRef n b
termContainsRef n (TTickApp _ f a)      = termContainsRef n f  || termContainsRef n a
termContainsRef _ _                     = False

-- Like Core.Normalise.replace, but uses UNIFICATION (constraint-creating)
-- instead of pure definitional conversion to match `lhs` against subterms.
-- This is needed for strategy 2 (auto-sym) when the goal contains regular
-- unification metas (e.g. `Vect (S ?k) a`) that are the *target* of the
-- rewrite rather than opaque blockers.
--
-- Must NOT be called when `goalHasDelayed` is True (those cases are guarded
-- in elabRewriteRetry).
replaceWithUnify : {vars : _} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   Int -> FC -> Defs -> Env Term vars ->
                   (lhs : NF vars) -> (parg : Term vars) -> (tm : NF vars) ->
                   Core (Term vars)
replaceWithUnify tmpi fc defs env lhs parg tm
    = do -- Try to unify lhs with tm; if successful, substitute parg.
         -- If unification throws (incompatible terms), fall through.
         unified <- catch (map Just (unify inTerm fc env lhs tm))
                           (const (pure Nothing))
         case unified of
           Just _ => pure parg
           Nothing => repSub tm
  where
    repArg : Closure vars -> Core (Term vars)
    repArg cl = do tmnf <- evalClosure defs cl
                   replaceWithUnify tmpi fc defs env lhs parg tmnf

    repSub : NF vars -> Core (Term vars)
    repSub (NBind bfc x b scfn)
        = do b' <- traverse (\cl => repSub !(evalClosure defs cl)) b
             let x' = MN "tmp" tmpi
             sc' <- replaceWithUnify (tmpi + 1) fc defs env lhs parg
                        !(scfn defs (toClosure defaultOpts env (Ref bfc Bound x')))
             pure (Bind bfc x b' (refsToLocals (Add x x' None) sc'))
    repSub (NApp _ hd []) = do empty <- clearDefs defs; quote empty env (NApp fc hd [])
    repSub (NApp _ hd args)
        = do args' <- traverse (traversePair repArg) args
             pure $ applyStackWithFC
                        !(replaceWithUnify tmpi fc defs env lhs parg (NApp fc hd []))
                        args'
    repSub (NDCon dfc n t a args)
        = do args' <- traverse (traversePair repArg) args
             empty <- clearDefs defs
             pure $ applyStackWithFC !(quote empty env (NDCon dfc n t a [])) args'
    repSub (NTCon tfc n a args)
        = do args' <- traverse (traversePair repArg) args
             empty <- clearDefs defs
             pure $ applyStackWithFC !(quote empty env (NTCon tfc n a [])) args'
    repSub (NDelayed dfc r t) = do t' <- repSub t; pure (TDelayed dfc r t')
    repSub (NDelay  dfc r ty tm)
        = do ty' <- replaceWithUnify tmpi fc defs env lhs parg !(evalClosure defs ty)
             tm' <- replaceWithUnify tmpi fc defs env lhs parg !(evalClosure defs tm)
             pure (TDelay dfc r ty' tm')
    repSub (NForce ffc r t args)
        = do args' <- traverse (traversePair repArg) args
             t' <- repSub t
             pure $ applyStackWithFC (TForce ffc r t') args'
    repSub (NAs asfc s a p) = do a' <- repSub a; p' <- repSub p; pure (As asfc s a' p')
    repSub (NErased efc (Dotted t)) = do t' <- repSub t; pure (Erased efc (Dotted t'))
    repSub other = do empty <- clearDefs defs; quote empty env other


-- Build a lemma using the forward or backward (sym) direction.
-- 'lhsNF' is the value to look for in the goal; 'ltyNF' is its type.
-- 'allowUnify': when True, fall back to replaceWithUnify if the pure
-- convert-based replace finds nothing.  This is used for strategy 2
-- (auto-sym) on the delayed retry pass to handle goals that contain
-- regular unification metas (e.g. `Vect (S ?k) a`).
buildHomoLemma : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 FC -> Env Term vars ->
                 (lemn : Name) ->
                 (symRule : Bool) ->
                 (allowUnify : Bool) ->
                 (lhsNF : NF vars) -> (ltyNF : NF vars) ->
                 (expnf : NF vars) -> (exptm : Term vars) ->
                 Core (Maybe (Lemma vars))
buildHomoLemma loc env lemn sym allowUnify lhsNF ltyNF expnf exptm
    = do defs  <- get Ctxt
         parg  <- genVarName "rwarg"
         rwexp <- replace defs env lhsNF (Ref loc Bound parg) expnf
         noChange <- convert defs env rwexp exptm
         if noChange
           then if allowUnify
                  -- Fallback: try unification-based replace for goals that
                  -- contain unsolved regular metas (e.g. Vect (S ?k) a).
                  then do rwexpU <- replaceWithUnify 0 loc defs env lhsNF
                                        (Ref loc Bound parg) expnf
                          noChangeU <- convert defs env rwexpU exptm
                          if noChangeU
                            then pure Nothing
                            else buildFromRwexp loc env lemn sym lhsNF ltyNF parg rwexpU
                  else pure Nothing
           else buildFromRwexp loc env lemn sym lhsNF ltyNF parg rwexp
  where
    buildFromRwexp : FC -> Env Term vars -> Name -> Bool ->
                     NF vars -> NF vars -> Name -> Term vars ->
                     Core (Maybe (Lemma vars))
    buildFromRwexp loc' env' lemn' sym' lhsNF' ltyNF' parg' rwexp'
        = do defs'  <- get Ctxt
             empty  <- clearDefs defs'
             ltytm  <- quote empty env' ltyNF'
             let pred = Bind loc' parg'
                          (Lam loc' top Explicit ltytm)
                          (refsToLocals (Add parg' parg' None) rwexp')
             gpredty <- getType env' pred
             predty  <- getTerm gpredty
             pure (Just (MkLemma lemn' pred predty sym'))

-- Build a heterogeneous lemma using replaceHet.
-- The motive P : (T : Type) -> T -> Type abstracts over both the type and
-- the value, so that hrewrite__impl can transport across a type boundary.
-- Returns Nothing if neither lhsNF nor ltyNF appear in the goal.
buildHetLemma : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                FC -> Env Term vars ->
                (hlemn : Name) ->
                (lhsNF : NF vars) -> (ltyNF : NF vars) ->
                (expnf : NF vars) ->
                Core (Maybe (Lemma vars))
buildHetLemma loc env hlemn lhsNF ltyNF expnf
    = do defs  <- get Ctxt
         varg  <- genVarName "rwval"
         targ  <- genVarName "rwty"
         pred  <- replaceHet loc defs env ltyNF lhsNF varg targ expnf
         -- At least one of varg or targ must appear in pred for it to
         -- have been a meaningful substitution.
         if not (termContainsRef varg pred || termContainsRef targ pred)
           then pure Nothing
           else do gpredty <- getType env pred
                   predty  <- getTerm gpredty
                   pure (Just (MkLemma hlemn pred predty False))

-- Called when strategy 1 (forward homogeneous) found nothing.
-- On the first pass (delayed=False) we throw so delayOnFailure queues a retry.
-- On the delayed pass we try strategy 2 (auto-sym) then strategy 3 (het).
elabRewriteRetry : {vars : _} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   FC -> Env Term vars ->
                   (delayed : Bool) -> (hetEq : Bool) ->
                   (lemn : Name) -> (mhlemn : Maybe Name) ->
                   (rt : NF vars) -> (rty : NF vars) ->
                   (expnf : NF vars) -> (exptm : Term vars) ->
                   (rulety : Term vars) ->
                   (lt : NF vars) -> (lty : NF vars) ->
                   Core (Lemma vars)
elabRewriteRetry loc env delayed hetEq lemn mhlemn rt rty expnf exptm rulety lt lty
    = if not delayed
        then throw (RewriteNoChange loc env rulety exptm)
        else do
          -- Strategy 2: backward / auto-sym.  Skipped for het rules, and
          -- also skipped when the goal term contains *Delayed* elaboration
          -- holes.  Such holes block case-block reduction; the forward rewrite
          -- will succeed in a later round once they are resolved.  Firing
          -- auto-sym now would apply the rule in the WRONG direction.
          -- (Regular unification metas are fine: they may themselves be the
          -- target of the rewrite.)
          goalDelay <- goalHasDelayed exptm
          mBwd <- if not hetEq && not goalDelay
                    then buildHomoLemma loc env lemn True True rt rty expnf exptm
                    else pure Nothing
          case mBwd of
            Just lemma => pure lemma
            Nothing    =>
              -- Strategy 3: het motive via hrewrite__impl.
              case mhlemn of
                Nothing    => throw (RewriteNoChange loc env rulety exptm)
                Just hlemn =>
                  do mHet <- buildHetLemma loc env hlemn lt lty expnf
                     case mHet of
                       Just lemma => pure lemma
                       Nothing    => throw (RewriteNoChange loc env rulety exptm)

elabRewrite : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> Env Term vars ->
              (delayed : Bool) ->
              (expected : Term vars) ->
              (rulety  : Term vars) ->
              Core (Lemma vars)
elabRewrite loc env delayed expected rulety
    = do defs <- get Ctxt
         tynf <- nf defs env rulety
         (lt, rt, lty, rty) <- getRewriteTerms loc defs tynf
                                    (NotRewriteRule loc env rulety)

         expnf <- nf defs env expected
         exptm <- quote defs env expected    -- identity for Term; kept for compat

         logNF "elab.rewrite" 5 "Rewriting" env lt
         logNF "elab.rewrite" 5 "Rewriting in" env expnf

         lemn   <- findRewriteLemma loc
         mhlemn <- findHRewriteLemma loc

         -- Determine whether the equality is truly heterogeneous (LHS and RHS
         -- inhabit different types).  If so, the homogeneous strategies (1 & 2)
         -- would emit a confusing constraint error, so we skip to strategy 3.
         --
         -- We use SYNTACTIC (not definitional) equality here: quoting both
         -- sides and comparing the resulting Terms structurally.  This is
         -- cheap and side-effect-free (no new unification constraints), but
         -- still correctly catches the JMEq case where lhsty and rhsty are
         -- literally different terms (e.g. Vect m a vs Vect n a).
         lhstm <- quote defs env lty
         rhtm  <- quote defs env rty
         let hetEq : Bool = lhstm /= rhtm

         -- ---------------------------------------------------------------
         -- Strategy 1: forward homogeneous — LHS in goal, same-type rule.
         -- Skipped when the rule is truly heterogeneous (to avoid spurious
         -- type constraints from the homogeneous rewrite__impl).
         -- ---------------------------------------------------------------
         mFwd <- if not hetEq
                   then buildHomoLemma loc env lemn False False lt lty expnf exptm
                   else pure Nothing
         case mFwd of
           Just lemma => pure lemma
           Nothing    =>
             elabRewriteRetry loc env delayed hetEq lemn mhlemn rt rty expnf exptm rulety lt lty

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
           lemma <- elabRewrite vfc env delayed expTy rulet

           rname <- genVarName "_"
           pname <- genVarName "_"

           let pbind = Let vfc erased lemma.pred lemma.predTy
           -- For the auto-sym case, wrap the proof in `sym` before binding it.
           -- We use the raw IVar application so implicits resolve naturally.
           let proofExpr : RawImp
               proofExpr = if lemma.symRule
                              then IApp vfc (IVar vfc (UN (Basic "sym"))) (IVar vfc rname)
                              else IVar vfc rname
           let rbind = Let vfc erased (weaken rulev) (weaken rulet)

           let env' = rbind :: pbind :: env

           (rwtm, grwty) <-
              inScope vfc (pbind :: env) $ \e' =>
                inScope {e=e'} vfc env' $ \e'' =>
                  let offset = mkSizeOf [rname, pname] in
                  check {e = e''} rigc elabinfo (weakenNs offset nest) env'
                    (apply (IVar vfc lemma.name)
                      [ IVar vfc pname
                      , proofExpr
                      , tm ])
                    (Just (gnf env' (weakenNs offset expTy)))
           rwty <- getTerm grwty
           let binding = Bind vfc pname pbind . Bind vfc rname rbind
           pure (binding rwtm, gnf env (binding rwty))
