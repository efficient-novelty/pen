/-
  PEN/CAD/Kappa.lean

  Minimal-effort (κ) search via iterative deepening over CAD derivations.

  Exposed APIs:
    - goalOfDecl : AtomicDecl → (Context → Bool)
    - kappaMin? : Context → (Context → Bool) → List AtomicDecl → Nat → Option (Nat × DerivCert start)
    - kappaMinForDecl? : Context → AtomicDecl → List AtomicDecl → Nat → Option (Nat × DerivCert start)

  The search explores only the finite `actions : List AtomicDecl` you provide.
  This keeps the branching factor bounded and makes the computation predictable.

  Design notes:
    * We use IDDFS (depth-limited DFS inside an outer loop that increases the limit).
      With uniform edge cost (1 per atomic step), this returns a shortest derivation.
    * CAD contexts are monotone: applying a valid step never removes information;
      we skip any step that leaves the context unchanged (prevents trivial loops).
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import Std.Data.HashSet

open Std

namespace PEN.CAD

-- Canonical string key for a context.
def ctxKey (Γ : Context) : String :=
  let ns  := Γ.universes.map toString
  let tfs := Γ.typeFormers
  let cs  := Γ.constructors.map (fun (c,t) => s!"C:{t}:{c}")
  let es  := Γ.eliminators.map  (fun (e,t) => s!"E:{t}:{e}")
  let rs  := Γ.compRules.map    (fun (e,c) => s!"R:{e}:{c}")
  let ms  := Γ.terms.map        (fun (m,t) => s!"M:{t}:{m}")
  String.intercalate "|" (ns ++ tfs ++ cs ++ es ++ rs ++ ms)

-- We memoize by a *string* state key to avoid requiring Hashable instances for Prod.
abbrev Seen := HashSet String

@[inline] def stateKey (Γ : Context) (bound : Nat) : String :=
  s!"{ctxKey Γ}#b{bound}"

/-- Equality test for contexts via componentwise list equality. -/
@[inline] def ctxSame (a b : Context) : Bool :=
  a.universes   == b.universes
  && a.typeFormers == b.typeFormers
  && a.constructors == b.constructors
  && a.eliminators  == b.eliminators
  && a.compRules    == b.compRules
  && a.terms        == b.terms

/-- Turn a target declaration into a "goal reached?" predicate on contexts. -/
@[inline] def goalOfDecl (decl : AtomicDecl) : Context → Bool :=
  match decl with
  | .declareUniverse ℓ      => fun Γ => Γ.hasUniverse ℓ
  | .declareTypeFormer n    => fun Γ => Γ.hasTypeFormer n
  | .declareConstructor c _ => fun Γ => Γ.hasConstructor c
  | .declareEliminator  e _ => fun Γ => Γ.hasEliminator e
  | .declareCompRule e c    => fun Γ => Γ.hasCompRule e c
  | .declareTerm t _        => fun Γ => Γ.hasTerm t

/--
  Internal depth-limited DFS.

  Parameters:
    * start : starting context (for the final certificate)
    * goal  : predicate on contexts (true if target is reached)
    * actions : finite menu of admissible atomic steps
    * limit : maximum remaining depth (number of steps we may still take)
    * Γ     : current context
    * dAcc  : accumulated derivation (forward order)

  Returns the first (lexicographically by `actions` order) certificate at depth ≤ limit.
-/
partial def dfsLimited
  (start : Context)
  (goal : Context → Bool)
  (actions : List AtomicDecl)
  (limit : Nat)
  (Γ : Context)
  (dAcc : Derivation)
  : Option (DerivCert start) := Id.run do
    -- If goal already holds, certify the current derivation.
    if goal Γ then
      match h : runDerivation start dAcc with
      | some fin =>
        return some { deriv := dAcc, finish := fin, witness := by simpa [runDerivation, h] }
      | none     => return none
    -- If no budget left, stop.
    if limit = 0 then
      return none
    -- Otherwise, try each action in order.
    for a in actions do
      if isValidInContext a Γ then
        match step Γ a with
        | some Γ' =>
            -- Skip if the action is a no-op (context unchanged).
            if ctxSame Γ Γ' then
              pure ()
            else
              let d' := dAcc ++ [a]
              match dfsLimited start goal actions (limit-1) Γ' d' with
              | some cert => return some cert
              | none      => pure ()
        | none => pure ()
      else
        pure ()
    return none

/--
  Iterative deepening wrapper: try depth bounds 0..maxDepth (inclusive)
  and return the first certificate found. With unit edge costs, this is
  guaranteed to produce a derivation of minimal length within the bound.

  We drive the outer loop with a *fuel* argument so termination is structural.
-/
def searchMinDerivation
  (start : Context)
  (goal : Context → Bool)
  (actions : List AtomicDecl)
  (maxDepth : Nat)
  : Option (DerivCert start) :=
  -- Early exit: goal already satisfied.
  if goal start then
    DerivCert.mk? start []
  else
    let rec loop (fuel : Nat) (bound : Nat) : Option (DerivCert start) :=
      match fuel with
      | 0 => none
      | Nat.succ fuel' =>
        if bound > maxDepth then
          none
        else
          match dfsLimited start goal actions bound start [] with
          | some cert => some cert
          | none      => loop fuel' (bound + 1)
    loop (maxDepth + 1) 0

partial def dfsLimitedMemo
    (actions : List AtomicDecl)
    (goal    : Context → Bool)
    (bound   : Nat)
    (Γ       : Context)
    (seen    : Seen)
    : Option ((Nat × Context) × Seen) :=

  if goal Γ then some ((0, Γ), seen) else
  if bound = 0 then none else
  let key := stateKey Γ bound
  if seen.contains key then none else
  let seen' := seen.insert key
  let sz := (Γ.universes.length + Γ.typeFormers.length + Γ.constructors.length
            + Γ.eliminators.length + Γ.compRules.length + Γ.terms.length)

  let rec tryList (as : List AtomicDecl) (seen₀ : Seen) : Option ((Nat × Context) × Seen) :=
    match as with
    | [] => none
    | a :: rest =>
      match step Γ a with
      | none      => tryList rest seen₀
      | some Γ'   =>
        if (Γ'.universes.length + Γ'.typeFormers.length + Γ'.constructors.length
            + Γ'.eliminators.length + Γ'.compRules.length + Γ'.terms.length) ≤ sz
        then tryList rest seen₀
        else
          match dfsLimitedMemo actions goal (bound - 1) Γ' seen₀ with
          | some ((k, Γ''), seen₁) => some ((k + 1, Γ''), seen₁)
          | none => tryList rest seen₀
  tryList actions seen'

def iddfsMinMemo
    (actions : List AtomicDecl)
    (goal    : Context → Bool)
    (maxDepth: Nat)
    (start   : Context)
    : Option (Nat × Context) :=
  let rec go (b fuel : Nat) : Option (Nat × Context) :=
    match fuel with
    | 0 => none
    | fuel'+1 =>
      if b > maxDepth then none else
      let seen0 : Seen := HashSet.empty
      match dfsLimitedMemo actions goal b start seen0 with
      | some ((k, Γ'), _) => some (k, Γ')
      | none              => go (b + 1) fuel'
  go 0 (maxDepth + 1)

/-- κ-min with memo speedup: find minimal k via memoized IDDFS, then certify at that k. -/
def kappaMin?
  (B : Context) (goal : Context → Bool) (actions : List AtomicDecl) (maxDepth : Nat)
  : Option (Nat × DerivCert B) :=
  match iddfsMinMemo actions goal maxDepth B with
  | some (kMin, _) =>
      -- Re-run once at exact bound kMin to get the derivation certificate.
      match searchMinDerivation B goal actions kMin with
      | some cert =>
          -- In principle cert.deriv.length = kMin; use the certificate’s length just in case.
          some (cert.deriv.length, cert)
      | none => none   -- Should not happen if the memo pass found kMin
  | none => none

def kappaMinForDecl?
  (B : Context) (Y : AtomicDecl) (actions : List AtomicDecl) (maxDepth : Nat)
  : Option (Nat × DerivCert B) :=
  kappaMin? B (goalOfDecl Y) actions maxDepth



end PEN.CAD
