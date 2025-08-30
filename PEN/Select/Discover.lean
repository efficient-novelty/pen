/-
  PEN/Select/Discover.lean

  Discovery of candidate X bundles directly from the action alphabet:

  Given:
    * B : Context          (current basis)
    * H : Nat              (budget/horizon)
    * actions : List AtomicDecl (finite action menu for search)

  For each atomic goal Y ∈ actions not yet in B, we compute a minimal derivation
  of Y under budget H; the “delta” X := steps \ B (atoms newly introduced) is a
  candidate bundle. We return all such bundles, with their post context and a
  copy of the derivation steps for auditing/foundation checks.
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa

namespace PEN.Select.Discover

open PEN.CAD
open AtomicDecl

/-- Canonical printable key for `AtomicDecl` (constructor tag + names). -/
@[inline] def declKey : AtomicDecl → String
  | .declareUniverse ℓ      => s!"U:{ℓ}"
  | .declareTypeFormer n    => s!"T:{n}"
  | .declareConstructor c T => s!"C:{T}:{c}"
  | .declareEliminator  e T => s!"E:{T}:{e}"
  | .declareCompRule    e c => s!"R:{e}:{c}"
  | .declareTerm        t T => s!"M:{T}:{t}"

/-- Pretty-printing for `AtomicDecl` via `declKey`. -/
instance : ToString AtomicDecl where
  toString := declKey

/-- One discovered candidate bundle X together with audit info. -/
structure DiscoveredX where
  targets : List AtomicDecl   -- X : atoms to install (delta vs B)
  post    : Context           -- B ∪ X (post context from the minimal derivation)
  kX      : Nat               -- size of X (usually targets.length)
  steps   : Derivation        -- the minimal-derivation steps (for audits)
deriving Repr

/-! Context membership for atoms -/
@[inline] def holdsDecl (Γ : Context) : AtomicDecl → Bool
  | .declareUniverse ℓ      => Γ.hasUniverse ℓ
  | .declareTypeFormer n    => Γ.hasTypeFormer n
  | .declareConstructor c _ => Γ.hasConstructor c
  | .declareEliminator e _  => Γ.hasEliminator e
  | .declareCompRule e c    => Γ.hasCompRule e c
  | .declareTerm t _        => Γ.hasTerm t

@[inline] def memBEq [BEq α] (x : α) (xs : List α) : Bool :=
  xs.any (· == x)

@[inline] def dedupBEq [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if memBEq x acc then acc else acc ++ [x]) ([])

/-- Compute the delta X = {a ∈ steps | a ∉ B}, dedup’d, preserving order. -/
@[inline] def deltaTargets (B : Context) (steps : Derivation) : List AtomicDecl :=
  dedupBEq <| steps.filter (fun a => not (holdsDecl B a))

@[inline] def isTypeFormer : AtomicDecl → Bool
  | .declareTypeFormer _ => true
  | _                    => false

@[inline] def isClassifier (s : String) : Bool :=
  s == "Pi" || s == "Sigma" || s == "Man"


/-- Only keep U0 blocked; expose everything else (incl. type formers). -/
private def isExposedGoal : AtomicDecl → Bool
  | .declareUniverse 0   => false
  | _                    => true

@[inline] def truncateAtFirstNewType (B : Context) (steps : Derivation) : List AtomicDecl :=
  -- Keep the entire prefix up to and including the first *new* type former,
  -- then take Δ vs B (this preserves leading universe steps, etc.).
  let rec go (acc : List AtomicDecl) (rest : Derivation) : List AtomicDecl :=
    match rest with
    | [] => deltaTargets B acc
    | a :: rs =>
      match a with
      | .declareTypeFormer _ =>
          if holdsDecl B a then
            go (acc ++ [a]) rs
          else
            -- first *new* TF encountered: keep prefix + this TF, then take Δ
            deltaTargets B (acc ++ [a])
      | _ =>
          go (acc ++ [a]) rs
  go [] steps

/--
  Discover all candidate bundles X derivable under budget H.

  For each atomic goal Y in `actions` not already in B, we ask `kappaMinForDecl?`
  for a minimal derivation. The candidate X is the delta of that derivation
  relative to B. We keep only non-empty deltas.
-/
def discoverCandidates (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let bootstrap := B.universes.isEmpty
  let primitiveAdmissible (Y : AtomicDecl) : Bool :=
    PEN.CAD.isValidInContext Y B
    || (bootstrap && match Y with
                     | AtomicDecl.declareUniverse _ => true   -- allow U₁ at τ=1
                     | _ => false)
  let goals :=
    actions.filter (fun Y =>
      isExposedGoal Y
      && not (holdsDecl B Y)
      && primitiveAdmissible Y)
  goals.foldl
    (fun acc Y =>
      match kappaMinForDecl? B Y actions H with
      | none => acc
      | some (_k, cert) =>
          -- OLD: let X := deltaTargets B cert.deriv
          -- NEW: type-first cut
          let X := truncateAtFirstNewType B cert.deriv
          if X.isEmpty then acc else
            -- recompute post by applying only X on B (not the whole cert)
            match applyAll? B X with
            | some postX =>
                -- avoid duplicates (same targets) to prevent double counting
                if acc.any (fun d => d.targets == X) then acc else
                acc ++ [{
                  targets := X,
                  post    := postX,
                  kX      := X.length,
                  steps   := X      -- foundation audit checks exactly what we install
                }]
            | none => acc   -- should not happen if X comes from a valid derivation
    )
    []

/-- Host type name if applicable (for terms/elims/type formers). -/
@[inline] def hostOf : AtomicDecl → Option String
  | .declareConstructor _ T => some T
  | .declareEliminator  _ T => some T
  | .declareTerm        _ T => some T
  | .declareTypeFormer    n => some n
  | _                      => none

@[inline] def isTypeFormerDecl : AtomicDecl → Bool
  | .declareTypeFormer _ => true
  | _                    => false

/-- Goal predicate "all of ts hold" (local copy). -/
@[inline] def goalAllTargets (ts : List AtomicDecl) : Context → Bool :=
  fun Γ => ts.all (fun t => holdsDecl Γ t)

def elimGoalFor (actions : List AtomicDecl) (host : String) : Option AtomicDecl :=
  actions.find? (fun a =>
    match a with
    | .declareEliminator _ T => T == host
    | _                      => false)

/-- Internal: compute single-seed "seeds" we can reuse for pair bundling. -/
structure Seed (start : Context) where
  goal  : AtomicDecl
  delta : List AtomicDecl
  host? : Option String
  cert  : DerivCert start
deriving Repr

def seeds (B : Context) (H : Nat) (actions : List AtomicDecl) : List (Seed B) :=
  let goals := actions.filter (fun Y => isExposedGoal Y && not (holdsDecl B Y))
  goals.foldl
    (fun acc Y =>
      match kappaMinForDecl? B Y actions H with
      | some (_k, cert) =>
          let d := deltaTargets B cert.deriv
          if d.isEmpty then acc else acc ++ [{ goal := Y, delta := d, host? := hostOf Y, cert := cert }]
      | none => acc)
    []

/-- Pick a canonical "decorator" (non-typeformer) for a given host:
    prefer eliminator; else pick lexicographically by goal name. -/
def pickCanonicalDecorator {B : Context} (ss : List (Seed B)) (host : String) : Option (Seed B) :=
  let cands := ss.filter (fun s => s.host? == some host && not (isTypeFormerDecl s.goal))
  let elimCands := cands.filter (fun s => match s.goal with | .declareEliminator _ _ => true | _ => false)
  let base := if elimCands.isEmpty then cands else elimCands
  match base with
  | [] => none
  | b :: bs =>
      let key (s : Seed B) : String := toString s.goal
      some <| bs.foldl (fun m s => if key s < key m then s else m) b

/- Pair bundling: for unordered classifier host-pairs {hi,hj} (hi < hj) create
    exactly one bundle = {typeFormer hi, typeFormer hj}. -/
/-!
  Generic type-former pair bundler: pick unordered distinct pairs of TF-seeds
  and certify the union of their deltas within H. Names are not hardcoded.
-/
def discoverTFPairBundles (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let ss := seeds B H actions
  let tfSeeds :=
    ss.filter (fun s => match s.goal with | .declareTypeFormer n => isClassifier n | _ => false)
  let rec pairs (xs : List (Seed B)) : List ((Seed B) × (Seed B)) :=
    match xs with | [] => [] | x :: xr => (xr.map (fun y => (x, y))) ++ pairs xr
  (pairs tfSeeds).foldl
    (fun acc (s₁, s₂) =>
      let ts := dedupBEq (s₁.delta ++ s₂.delta)
      match PEN.CAD.kappaMin? B (goalAllTargets ts) actions H with
      | some (_k, cert) =>
          let X := deltaTargets B cert.deriv
          if X.isEmpty then acc else
          match applyAll? B X with
          | some postX =>
              if acc.any (fun d => d.targets == X) then acc else
              acc ++ [{
                targets := X,
                post    := postX,   -- recomputed from delta only
                kX      := X.length,
                steps   := X        -- audit exactly what we install
              }]
          | none => acc
      | none => acc)
    []




private def isCtorFor (host : String) : AtomicDecl → Bool
  | .declareConstructor _ T => T == host
  | _                       => false

private def ctorSeedsFor {B : Context} (ss : List (Seed B)) (host : String) : List (Seed B) :=
  ss.filter (fun s => isCtorFor host s.goal)

private def typeSeedFor {B : Context} (ss : List (Seed B)) (host : String) : Option (Seed B) :=
  ss.find? (fun s => s.goal == AtomicDecl.declareTypeFormer host)

/-- Build 3‑atom HIT “cores”: type former + two constructors (if available). -/
def discoverHITCoreBundles (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let ss := seeds B H actions
  -- candidate hosts: type formers not yet in B that also have ≥ 2 constructor seeds
  let hosts : List String :=
    ss.foldl (fun acc s =>
      match s.goal with
      | .declareTypeFormer n =>
          let ct := ctorSeedsFor ss n
          if ct.length ≥ 2 ∧ ¬acc.any (· == n) then acc ++ [n] else acc
      | _ => acc) []
  -- for each host, pick the first two constructor seeds deterministically
  hosts.foldl
    (fun acc host =>
      match typeSeedFor ss host, (ctorSeedsFor ss host) with
      | some tf, c1 :: c2 :: _ =>
          let ts := dedupBEq (tf.delta ++ c1.delta ++ c2.delta)  -- usually [S1, base, loop]
          match PEN.CAD.kappaMin? B (goalAllTargets ts) actions H with
          | some (_k, cert) =>
            let X := deltaTargets B cert.deriv
            if X.isEmpty then []
            else match applyAll? B X with
                | some postX =>
                    [{
                      targets := X,
                      post    := postX,      -- << recomputed post (no leakage)
                      kX      := X.length,
                      steps   := X           -- << audit exactly what we install
                    }]
                | none => []
          | none => acc
      | _, _ => acc)
    []

private def elimSeedFor {B : Context} (ss : List (Seed B)) (host : String) : Option (Seed B) :=
  ss.find? (fun s => match s.goal with
                     | .declareEliminator _ T => T == host
                     | _ => false)

/-- Local host predicates (parallel to the ones in Engine). -/
private def isElimFor (h : String) : AtomicDecl → Bool
  | .declareEliminator _ T => T == h
  | _ => false

private def isTFFor (h : String) : AtomicDecl → Bool
  | .declareTypeFormer n => n == h
  | _ => false

/-- A full HIT bundle for host h must contain: TF(h), at least two ctors for h, and an eliminator for h. -/
@[inline] def isFullForHost (ts : List AtomicDecl) (h : String) : Bool :=
  let hasTF := ts.any (isTFFor h)
  let hasE  := ts.any (isElimFor h)
  let nC    := ts.foldl (fun s a => s + (if isCtorFor h a then 1 else 0)) 0
  hasTF && hasE && nC ≥ 2

/-- All unordered pairs of a list. -/
private def pairs {α} (xs : List α) : List (α × α) :=
  let rec go (ys : List α) : List (α × α) :=
    match ys with
    | []      => []
    | y :: yr => (yr.map (fun z => (y, z))) ++ go yr
  go xs

/-- All unordered triples of a list. -/
private def triples {α} (xs : List α) : List (α × α × α) :=
  let rec go (ys : List α) : List (α × α × α) :=
    match ys with
    | []        => []
    | y :: yr   =>
        let ps := pairs yr |>.map (fun (a,b) => (y, a, b))
        ps ++ go yr
  go xs


/--
  Generic host bundler: build "full HIT" subsets for each host
  (TF + ≥2 ctors + eliminator). Subsets are constructed from constructor seeds
  (pairs and triples). We add the TF and eliminator *goals* explicitly, then
  certify with κ. No κ-massage here; we just return the minimal delta X.
-/
def discoverHITBundlesGeneric (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let ss : List (Seed B) := seeds B H actions

  -- hosts that have at least two ctor seeds and an eliminator in the actions menu
  let hosts : List String :=
    ss.foldl (fun acc s =>
      match s.goal with
      | .declareTypeFormer n =>
          let cs := ctorSeedsFor ss n
          let hasElim := (actions.any (isElimFor n))
          if cs.length ≥ 2 ∧ hasElim ∧ ¬acc.any (· == n) then acc ++ [n] else acc
      | _ => acc) []

  -- for each host, try ctor pairs/triples, add TF+elim goals, and certify
  hosts.foldl
    (fun acc host =>
      let cs        := ctorSeedsFor ss host
      let ps        := pairs cs
      let ts3       := triples cs
      let elimGoal? := actions.find? (isElimFor host)
      match elimGoal? with
      | none => acc
      | some elimGoal =>
          -- helper to certify one ctor-combo
          let certify (deltas : List (List AtomicDecl)) : List DiscoveredX :=
            let tfGoal := AtomicDecl.declareTypeFormer host
            let ts0    := dedupBEq (deltas.foldl (· ++ ·) [] ++ [elimGoal, tfGoal])
            if isFullForHost ts0 host then
              match PEN.CAD.kappaMin? B (goalAllTargets ts0) actions H with
              | some (_k, cert) =>
                let X := deltaTargets B cert.deriv
                if X.isEmpty then []
                else match applyAll? B X with
                    | some postX =>
                        [{
                          targets := X,
                          post    := postX,      -- << recomputed post (no leakage)
                          kX      := X.length,
                          steps   := X           -- << audit exactly what we install
                        }]
                    | none => []

              | none => []
            else []
          -- try all pairs
          let fromPairs :=
            ps.foldl (fun a (c1, c2) => a ++ certify [c1.delta, c2.delta]) []
          -- and all triples (if present). This keeps it generic for richer HITs.
          let fromTriples :=
            ts3.foldl (fun a (c1, c2, c3) => a ++ certify [c1.delta, c2.delta, c3.delta]) []
          acc ++ fromPairs ++ fromTriples)
    []

/-- Build “full” HIT bundles: two ctors + eliminator (type is added by search if needed).
    Unlike the stricter version, we do **not** require an eliminator seed first;
    we include the eliminator **goal** and let κ-certification decide if H suffices. -/
def discoverHITFullBundles (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let ss := seeds B H actions
  -- hosts having ≥ 2 constructor seeds (even if elim seed isn't in `ss` yet)
  let hosts : List String :=
    ss.foldl (fun acc s =>
      match s.goal with
      | .declareTypeFormer n =>
          let ct := ss.filter (fun t => match t.goal with
                                        | .declareConstructor _ T => T == n
                                        | _ => false)
          if ct.length ≥ 2 ∧ ¬acc.any (· == n) then acc ++ [n] else acc
      | _ => acc) []

  hosts.foldl
    (fun acc host =>
      match elimGoalFor actions host, ss.filter (fun t => match t.goal with
                                                          | .declareConstructor _ T => T == host
                                                          | _ => false) with
      | some elimGoal, c1 :: c2 :: _ =>
          -- target set: elim-goal + two ctor deltas (TF will be added by derivation if needed)
          let ts : List AtomicDecl := dedupBEq (elimGoal :: c1.delta ++ c2.delta)
          match PEN.CAD.kappaMin? B (goalAllTargets ts) actions H with
          | some (_k, cert) =>
            let X := deltaTargets B cert.deriv
            if X.isEmpty then []
            else match applyAll? B X with
                | some postX =>
                    [{
                      targets := X,
                      post    := postX,      -- << recomputed post (no leakage)
                      kX      := X.length,
                      steps   := X           -- << audit exactly what we install
                    }]
                | none => []

          | none => acc
      | _, _ => acc)
    []



end PEN.Select.Discover
