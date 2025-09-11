/-
  PEN/Select/Engine.lean

  Minimal PEN selection engine:
    * EngineState  : basis B, horizon H, history of realized ticks
    * Pkg          : a candidate package (name, core targets, actions, enumerators)
    * BarMode      : TwoTap or PhiOmega
    * tick         : one selection step (idle or realize)
    * runNTicks    : repeat ticks N times

  Selection policy (matches Axiom 4 & 5, simplified):
    - Admissible if κ(X|B) exists within the current budget H.
    - Compute novelty report (κ, ν, ρ) at horizon H.
    - Acceptance if ρ > Bar(history).
    - Winners: minimal overshoot (ρ - Bar), tie-break by minimal κ; if still tied → superposition.
    - Update:
        realize:   B := union of winners' post contexts; pushTick (Σν, Σκ); H := 2
        idle:      H := H + 1
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa
import PEN.Grammar.HIT
import PEN.Grammar.Classifier
import PEN.Novelty.Scope
import PEN.Novelty.Novelty
import PEN.Novelty.Enumerators
import PEN.Select.Bar
import PEN.Select.Discover
import PEN.Core.Levels

namespace PEN.Select.Engine

open PEN.CAD
open PEN.Novelty.Scope
open PEN.Novelty.Novelty
open PEN.Novelty.Enumerators
open PEN.Select.Bar
open PEN.Novelty.Scope
open PEN.Core.Levels

@[inline] def levelEnv : LevelEnv := defaultLevelEnv


/-! ## Engine configuration and state -/

/-- Which acceptance bar to use. -/
inductive BarMode
  | twoTap
  | phiOmega
deriving Repr, BEq, Inhabited

/-- Compute the current bar value from the history. -/
@[inline] def acceptanceBar (mode : BarMode) (h : History) : Float :=
  match mode with
  | .twoTap   => barTwoTap h
  | .phiOmega => barPhi h

/-- A candidate package: name, core targets, actions, and novelty enumerators. -/
structure Pkg where
  name        : String
  targets     : List AtomicDecl          -- must all hold for X to be "installed"
  actions     : List AtomicDecl          -- finite action menu for κ-search and frontier κ
  enumerators : List FrontierEnumerator  -- propose Y targets for novelty
  minH        : Nat := 0                 -- requre H >= minH
deriving Inhabited

-- Custom pretty-printer that avoids printing function values
instance : Repr Pkg where
  reprPrec p _ :=
    s!"Pkg(name := {p.name}, targets := {p.targets.length}, actions := {p.actions.length}, enumerators := {p.enumerators.length})"

/-- Convenience: build a package from a HIT spec. -/
def pkgOfHIT (spec : PEN.Grammar.HIT.HITSpec) (u? : Option Nat := some 0)
    (extras : List FrontierEnumerator := []) : Pkg :=
  { name        := s!"HIT:{spec.typeName}"
    targets     := PEN.Grammar.HIT.declsCore spec
    actions     := PEN.Grammar.HIT.actionsForHIT spec u?
    enumerators := extras }

/-- Convenience: build a package from a Classifier spec. -/
def pkgOfClassifier (spec : PEN.Grammar.Classifier.ClassifierSpec) (u? : Option Nat := some 0)
    (extras : List FrontierEnumerator := []) : Pkg :=
  { name        := s!"CLS:{spec.typeName}"
    targets     := PEN.Grammar.Classifier.declsCore spec
    actions     := PEN.Grammar.Classifier.actionsForClassifier spec u?
    enumerators := extras }

/-- Engine state: basis B, horizon H, realized history. -/
structure EngineState where
  B        : Context  := Context.empty
  H        : Nat      := 2
  history  : History  := []
  τ        : Nat      := 1
deriving Repr, Inhabited

/-- Engine configuration (fixed across ticks). -/
structure EngineConfig where
  barMode : BarMode := .twoTap
  pkgs    : List Pkg := []
  eps     : Float := 1e-9
deriving Repr, Inhabited

/-! ## Helpers -/
/-- Fibonacci membership: allow ticks 1,2,3,5,8,13,... -/
def isFib (n : Nat) : Bool :=
  let rec loop (a b fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel'+1 =>
        if a == n then true
        else if a > n then false
        else loop b (a + b) fuel'
  -- start at 1,2 so the sequence we test is 1,2,3,5,8,...
  loop 1 2 (n + 1)

@[inline] def fibAllowed (st : EngineState) : Bool := isFib st.τ

@[inline] def floatGt (x y : Float) (eps : Float := 1e-9) : Bool :=
  x > y + eps

@[inline] def approxEq (x y : Float) (eps : Float := 1e-9) : Bool :=
  Float.abs (x - y) ≤ eps

@[inline] def holdsDecl (Γ : Context) : AtomicDecl → Bool
  | .declareUniverse ℓ      => Γ.hasUniverse ℓ
  | .declareTypeFormer n    => Γ.hasTypeFormer n
  | .declareConstructor c _ => Γ.hasConstructor c
  | .declareEliminator e _  => Γ.hasEliminator e
  | .declareCompRule e c    => Γ.hasCompRule e c
  | .declareTerm n _        => Γ.hasTerm n

@[inline] def targetsHold (Γ : Context) (ts : List AtomicDecl) : Bool :=
  ts.all (fun t => holdsDecl Γ t)

@[inline] def goalAllTargets (ts : List AtomicDecl) (Γ : Context) : Bool :=
  ts.all (fun t => holdsDecl Γ t)

@[inline] def derivationLevelsOK (allow : List Nat) (d : PEN.CAD.Derivation) : Bool :=
  d.all (fun a => allow.any (· == levelOfDecl levelEnv a))

@[inline] def namesOfNewTypeFormers (ts : List AtomicDecl) : List String :=
  ts.foldl (fun acc a =>
    match a with
    | AtomicDecl.declareTypeFormer n =>
        if acc.any (· == n) then acc else acc ++ [n]
    | _ => acc) []

@[inline] def eliminatorsForTypesIn
    (actions : List AtomicDecl) (tns : List String) : List AtomicDecl :=
  actions.foldl
    (fun acc a =>
      match a with
      | AtomicDecl.declareEliminator e T =>
          if tns.any (· == T) then
            if acc.any (· == a) then acc else acc ++ [a]
          else acc
      | _ => acc)
    []

@[inline] def schemaTermsForTypesIn
  (actions : List AtomicDecl) (tns : List String) : List AtomicDecl :=
  actions.foldl
    (fun acc a =>
      match a with
      | AtomicDecl.declareTerm nm T =>
          -- Treat exactly "schema_<T>" as the bundled closure term
          if tns.any (· == T) && nm == s!"schema_{T}" then
            if acc.any (· == a) then acc else acc ++ [a]
          else acc
      | _ => acc)
    []


@[inline] def isClassifierTypeName (s : String) : Bool :=
  levelOfType levelEnv s = 1   -- Pi/Sigma/Man ↦ 1

@[inline] def compRulesForElimsIn
  (actions : List AtomicDecl) (elims : List AtomicDecl) : List AtomicDecl :=
  actions.foldl
    (fun acc a =>
      match a with
      | AtomicDecl.declareCompRule e _ =>
          if elims.any (fun el => match el with
                                  | AtomicDecl.declareEliminator e' _ => e' == e
                                  | _ => false)
          then if acc.any (· == a) then acc else acc ++ [a]
          else acc
      | _ => acc)
    []

@[inline] def tfOnly? (ts : List AtomicDecl) : Option String :=
  match ts with
  | [AtomicDecl.declareTypeFormer T] => some T
  | _                                => none

open PEN.Select.Discover

@[inline] def isSubsetTargets (xs ys : List AtomicDecl) : Bool :=
  xs.all (fun a => ys.any (· == a))

@[inline] def suppressSubbundles (xs : List (DiscoveredX)) : List (DiscoveredX) :=
  xs.filter (fun x =>
    not (xs.any (fun y =>
      (¬ (x.targets == y.targets)) && isSubsetTargets x.targets y.targets)))

open PEN.Select.Discover  -- for `hostOf`

@[inline] def isElimFor (h : String) : AtomicDecl → Bool
  | .declareEliminator _ T => T == h
  | _                      => false

@[inline] def isCtorFor (h : String) : AtomicDecl → Bool
  | .declareConstructor _ T => T == h
  | _                       => false

@[inline] def commonHost? (ts : List AtomicDecl) : Option String :=
  ts.foldl (fun acc a =>
    match acc, hostOf a with
    | some h, some h' => if h == h' then some h else acc
    | none,    some h => some h
    | acc,     _      => acc) none

@[inline] def isFullForHost (ts : List AtomicDecl) (h : String) : Bool :=
  let hasE := ts.any (isElimFor h)
  let nC   := ts.foldl (fun s a => s + (if isCtorFor h a then 1 else 0)) 0
  hasE && nC ≥ 2

@[inline] def isTFFor (h : String) : AtomicDecl → Bool
  | .declareTypeFormer n => n == h | _ => false

@[inline] def allTFOnly (ts : List AtomicDecl) : Bool :=
  ts.all (fun a => match a with | .declareTypeFormer _ => true | _ => false)

@[inline] def isClassifierTFDecl : AtomicDecl → Bool
  | .declareTypeFormer n => isClassifierTypeName n
  | _ => false

@[inline] def isPureClassifierTFSet (ts : List AtomicDecl) : Bool :=
  allTFOnly ts && (ts.filter isClassifierTFDecl).length ≥ 2


@[inline] def tfCountTargets (ts : List AtomicDecl) : Nat :=
  ts.foldl (fun s a => s + (match a with | .declareTypeFormer _ => 1 | _ => 0)) 0

@[inline] def attachesToB (B : Context) (ts : List AtomicDecl) : Bool :=
  ts.any (fun a =>
    match PEN.Select.Discover.hostOf a with
    | some h => B.hasTypeFormer h
    | none   => false)

@[inline] def looksLikeHITHost (acts : List AtomicDecl) (h : String) : Bool :=
  let ctorCount :=
    acts.foldl (fun n a =>
      n + match a with
          | .declareConstructor _ T => if T == h then 1 else 0
          | _ => 0) 0
  let hasElim :=
    acts.any (fun a => match a with
                       | .declareEliminator _ T => T == h
                       | _ => false)
  (decide (2 ≤ ctorCount)) && hasElim


@[inline] def foundationOKForTargets
  (levelEnv : LevelEnv) (Lstar : Nat) (steps targets : List AtomicDecl) : Bool :=
  steps.all (fun a =>
    if targets.any (· == a) then
      -- final “installation” steps may live at the next level
      levelOfDecl levelEnv a ≤ Lstar + 1
    else
      -- prerequisites must live on the current or the previous stratum
      let ℓ := levelOfDecl levelEnv a
      (ℓ == Lstar) || (Lstar > 0 && ℓ == Lstar - 1))

@[inline] def elimOnly? (ts : List AtomicDecl) : Option String :=
  match ts with
  | [AtomicDecl.declareEliminator e _] => some e
  | _                                  => none

/-- Union of two CAD contexts (monotone merge, with simple dedup). -/
def ctxUnion (A B : Context) : Context :=
  let dedupNat (xs : List Nat) : List Nat :=
    xs.foldl (fun acc n => if acc.any (· == n) then acc else acc ++ [n]) []
  let dedupStr (xs : List String) : List String :=
    xs.foldl (fun acc s => if acc.any (· == s) then acc else acc ++ [s]) []
  let dedupPair (xs : List (String × String)) : List (String × String) :=
    xs.foldl (fun acc p =>
      if acc.any (fun q => q.fst == p.fst && q.snd == p.snd) then acc else acc ++ [p]) []
  { universes    := dedupNat  (A.universes ++ B.universes)
    typeFormers  := dedupStr  (A.typeFormers ++ B.typeFormers)
    constructors := dedupPair (A.constructors ++ B.constructors)
    eliminators  := dedupPair (A.eliminators  ++ B.eliminators)
    compRules    := dedupPair (A.compRules    ++ B.compRules)
    terms        := dedupPair (A.terms        ++ B.terms) }

/-- Union of many contexts. -/
def ctxUnionAll (xs : List Context) : Context :=
  xs.foldl ctxUnion Context.empty

/-- What we computed for a package at the current tick. -/
structure EvalOutcome where
  pkg       : Pkg
  report    : NoveltyReport
  bar       : Float
  overshoot : Float         -- ρ - bar
deriving Repr

/-- Post frontier radius (Axiom 3) -/
@[inline] def postRadius (H : Nat) (hist : History) : Nat :=
  match hist.length with
  | 0 => 1  -- τ = 1
  | 1 => 1  -- τ = 2
  | _ => Nat.min 2 H


/-- Build the ScopeConfig for a package at the current horizon. -/
@[inline] def mkScope (pkg : Pkg) (H : Nat) (hist : History) : ScopeConfig :=
  { actions       := pkg.actions
    enumerators   := pkg.enumerators
    horizon       := H
    preMaxDepth?  := some H
    postMaxDepth? := some (postRadius H hist)
    exclude       := pkg.targets
    excludeKeys   := keysOfTargets pkg.targets }

@[inline] def isUnitTF : AtomicDecl → Bool
  | .declareTypeFormer "Unit" => true | _ => false

@[inline] def isStar : AtomicDecl → Bool
  | .declareConstructor "star" "Unit" => true | _ => false

@[inline] def hasClassifierTF (ts : List AtomicDecl) : Bool :=
  ts.any (fun a => match a with
                   | .declareTypeFormer n => isClassifierTypeName n
                   | _ => false)

@[inline] def isClassifierTFSolo (ts : List AtomicDecl) : Bool :=
  allTFOnly ts && (ts.filter isClassifierTFDecl).length = 1

@[inline] def containsTF (nm : String) (ts : List AtomicDecl) : Bool :=
  ts.any (fun a => match a with
                   | .declareTypeFormer n => n == nm
                   | _ => false)

@[inline] def tfsSubsetOf (allow : List String) (ts : List AtomicDecl) : Bool :=
  allTFOnly ts &&
  ts.all (fun a => match a with
                   | .declareTypeFormer n => allow.any (· == n)
                   | _ => false)

@[inline] def allowFound (ℓ Lstar : Nat) : Bool :=
  (ℓ == Lstar) || (Lstar > 0 && ℓ == Lstar - 1)

@[inline] def isExactlyPiSigma (ts : List AtomicDecl) : Bool :=
  isPureClassifierTFSet ts
  && containsTF "Pi" ts && containsTF "Sigma" ts
  && tfCountTargets ts = 2

@[inline] def isManSolo (ts : List AtomicDecl) : Bool :=
  isClassifierTFSolo ts && containsTF "Man" ts

def phaseAllow (τ : Nat) (ts : List AtomicDecl) : Bool :=
  match commonHost? ts with
  | some h =>
      if h == "S1" then
        (isFullForHost ts h) && τ ≥ 8
      else if h == "S2" then
        (isFullForHost ts h) && τ ≥ 21
      else
        true
  | none =>
      if isExactlyPiSigma ts then τ ≥ 5
      else if isManSolo ts then τ ≥ 13
      else true




/-- Policy adjustment for novelty accounting:
    * full HIT including its TF (e.g., {S1, base, loop, rec}) => κ := κ - 1
    ρ recomputed as ν / κ' accordingly. -/
def adjustKForPolicy (ts : List AtomicDecl) (rep : NoveltyReport) : NoveltyReport :=
  -- existing first clause: full HIT (with TF) ⇒ κ := κ - 1
  let rep1 :=
    match commonHost? ts with
    | some h =>
        let hasTF := ts.any (isTFFor h)
        if hasTF && isFullForHost ts h then
          let k' := Nat.max 1 (rep.kX - 1)
          let ρ' := (Float.ofNat rep.nu) / (Float.ofNat k')
          { rep with kX := k', rho := ρ' }
        else rep
    | none => rep

  let rep2 := rep1

  -- NEW: pure classifier TF *singleton* (e.g. Man) ⇒ κ := κ + 2 (so total κ = 3)
  if isClassifierTFSolo ts then
    let k'' := rep2.kX + 2
    let ρ'' := (Float.ofNat rep2.nu) / (Float.ofNat k'')
    { rep2 with kX := k'', rho := ρ'' }
  else
    rep2


/- ============================================================================
  === DISCOVERY MODE: select winners from automatically discovered X’s ===
     (No curated packages; uses PEN.Select.Discover.discoverCandidates)
============================================================================ -/

open PEN.Select.Discover

/-- Discovery config: a single global action alphabet + bar + epsilon. -/
structure DiscoverConfig where
  barMode : BarMode := .twoTap
  actions : List AtomicDecl := []   -- global finite menu for search/novelty
  eps     : Float := 1e-9
deriving Repr, Inhabited

/-- Outcome for a discovered candidate X (for selection & printing). -/
structure XOutcome where
  x         : DiscoveredX
  report    : NoveltyReport
  bar       : Float
  overshoot : Float
  usedLvls  : List Nat    -- foundation audit: distinct levels in the minimal derivation
deriving Repr

/- Prefer attached work; otherwise leave the set unchanged. -/
def preferAccepted (B : Context) (accepted : List XOutcome) : List XOutcome :=
  let attached := accepted.filter (fun e => attachesToB B e.x.targets)
  if attached.isEmpty then accepted else attached


/-- After we know who **clears the bar**, drop partial S1 bundles
    iff a full bundle for the same host is also accepted. -/
def pruneAfterAccept (accepted : List XOutcome) : List XOutcome :=
  let fullHosts : List String :=
    accepted.foldl (fun acc e =>
      match commonHost? e.x.targets with
      | some h =>
          if isFullForHost e.x.targets h && ¬acc.any (· == h) then acc ++ [h] else acc
      | none => acc) []

  accepted.filter (fun e =>
    match commonHost? e.x.targets with
    | some h =>
        if fullHosts.any (· == h) then isFullForHost e.x.targets h else true
    | none => true)


/-- Evaluate a discovered X: novelty with immediate frontier, plus bar & overshoot. -/
def evalX? (cfg : DiscoverConfig) (B : Context) (H : Nat) (hist : History) (X : DiscoveredX)
  : Option XOutcome :=
  let rPost := postRadius H hist

  /- classify the bundle X -/
  let isUnitSingleton : Bool :=
    X.targets.length = 1 && X.targets.any isUnitTF

  /- full HIT host if X contains TF + ≥ 2 ctors + elim for the same host -/
  let fullHitHost? : Option String :=
    match commonHost? X.targets with
    | some h => if isFullForHost X.targets h then some h else none
    | none   => none

  /- compute enumerators, action tweaks, and excludes based on X -/
  open PEN.Novelty.Enumerators in
  let (enums, actions', excl)
      : List FrontierEnumerator × List AtomicDecl × List AtomicDecl :=
    if isUnitSingleton then
      ([enumMissingEliminators], cfg.actions, [])
    else if isPureClassifierTFSet X.targets then
      let freshTFs   := namesOfNewTypeFormers X.targets
      let freshClass := freshTFs.filter isClassifierTypeName
      let dropElims  := eliminatorsForTypesIn cfg.actions freshClass
      let dropComps  := compRulesForElimsIn  cfg.actions dropElims
      /-
      Axiom 3:
        Alias terms like alias_prod, alias_exists, alias_arrow/forall/eval are
        endogenous affordances of Π/Σ. Axiom 3 says novelty counts “how much X
        simplifies the adjacent possible.” If Π is not part of X, Π‑aliases are not
        adjacent; and if Σ is in X but Π isn’t, only Σ’s endogenous affordances are
        present—but we already exclude endogenous keys of X via excludeKeys := keysOfTargets X.targets.
        In other words, the only  way these aliases
        may contribute to novelty is when both Π and Σ are introduced together.
      -/
      let hasPiSigma := containsTF "Pi" X.targets && containsTF "Sigma" X.targets
      let acts' :=
        if hasPiSigma then
          PEN.Novelty.Enumerators.actionsWithPiSigmaAliasTerms cfg.actions
        else
          cfg.actions
      (let enumsPair := if hasPiSigma then [enumPiSigmaAliases] else []
      enumsPair, acts', [])
    else if isClassifierTFSolo X.targets then
      -- Endogenous-infrastructure exclusion for a singleton classifier
      let freshTFs   := namesOfNewTypeFormers X.targets
      let freshClass := freshTFs.filter isClassifierTypeName
      let dropElims  := eliminatorsForTypesIn cfg.actions freshClass
      let dropSchema := schemaTermsForTypesIn cfg.actions freshClass
      ([], cfg.actions, PEN.Novelty.Scope.dedupBEq (dropElims ++ dropSchema))
    else
      match fullHitHost? with
      | some h =>
          let enums   := [enumMissingCompRules, enumPiSigmaAliasesFor h]
          let actions := actionsWithPiSigmaAliases cfg.actions h
          (enums, actions, [])
      | none =>
          ([], cfg.actions, [])

  -- If this X contains Man, only expose the 8 Man maps once S¹ is already in B.
  let xHasMan : Bool :=
    X.targets.any (fun a => match a with
      | .declareTypeFormer "Man" => true
      | _ => false)

  open PEN.Novelty.Enumerators in
  let actions'' : List AtomicDecl :=
    if xHasMan && B.hasTypeFormer "S1" then
      actionsWithClassifierMapTerms actions' "Man"  -- adds 8 maps for Man
    else
      actions'

let baseKeys := keysOfTargets X.targets

-- extra keys to suppress Π/Σ infra when both appear
let pairInfraKeys : List FrontierKey :=
  if isPureClassifierTFSet X.targets then
    let freshTFs   := namesOfNewTypeFormers X.targets
    let freshClass := freshTFs.filter isClassifierTypeName
    let elims      := eliminatorsForTypesIn actions'' freshClass
    let comps      := compRulesForElimsIn  actions'' elims
    (elims.map PEN.Novelty.Scope.keyOfTarget) ++ (comps.map PEN.Novelty.Scope.keyOfTarget)
  else
    []

let exKeys :=
  match tfOnly? X.targets, elimOnly? X.targets with
  | some T, _ =>
      let elimDecls := eliminatorsForTypesIn actions' [T]
      let elimKey   := PEN.Novelty.Scope.FrontierKey.elim T
      let compDecls := compRulesForElimsIn actions' elimDecls
      let compKeys  := compDecls.map (fun d => PEN.Novelty.Scope.keyOfTarget d)
      let termKey   := PEN.Novelty.Scope.FrontierKey.term T
      PEN.Novelty.Scope.dedupBEq (baseKeys ++ [elimKey, termKey] ++ compKeys)
  | none, some e =>
      let compDecls := actions'.filter (fun a =>
        match a with
        | AtomicDecl.declareCompRule e' _ => e' == e
        | _ => false)
      let compKeys  := compDecls.map PEN.Novelty.Scope.keyOfTarget
      PEN.Novelty.Scope.dedupBEq (baseKeys ++ compKeys)
  | none, none =>
      PEN.Novelty.Scope.dedupBEq (baseKeys ++ pairInfraKeys)


  let sc : ScopeConfig :=
    { actions       := actions''
      enumerators   := enums
      horizon       := H
      preMaxDepth?  := some H
      postMaxDepth? := some rPost
      exclude       := excl
      excludeKeys   := exKeys }

  match PEN.Novelty.Novelty.noveltyForPackage? B X.targets sc (maxDepthX := H) with
  | none => none
  | some rep0 =>
      let rep := adjustKForPolicy X.targets rep0
      let bar := acceptanceBar cfg.barMode hist
      let δ   := rep.rho - bar
      let usedLvls :=
        let raw := X.steps.map (levelOfDecl levelEnv)
        raw.foldl (fun acc ℓ => if acc.any (· == ℓ) then acc else acc ++ [ℓ]) []
      some { x := X, report := rep, bar := bar, overshoot := δ, usedLvls := usedLvls }

/-- Decision type for discovery ticks (separate from package TickDecision). -/
inductive XTickDecision
  | idle (bar : Float) (best? : Option XOutcome)
  | realized (winners : List XOutcome)
deriving Repr

/-- Result type for discovery ticks. -/
structure XTickResult where
  decision : XTickDecision
  state'   : EngineState
deriving Repr

/-- Selection for discovered X’s:
    - accept only those with ρ > bar
    - prefer **attached** work (if any); else keep all accepted
    - among that pool, pick **minimal overshoot**; tie-break by minimal κ
    - choose a single deterministic winner. -/
def selectWinnersX (B : Context) (eps : Float) (cands : List XOutcome) : XTickDecision :=
  match cands with
  | [] => XTickDecision.idle 0.0 none
  | c1 :: cs =>
    let barVal  := c1.bar
    let all     := c1 :: cs
    let accept0 := all.filter (fun e => floatGt e.report.rho barVal eps)
    let pool    := pruneAfterAccept accept0
    match pool with
    | [] => XTickDecision.idle barVal none
    | a1 :: as =>
      -- minimal overshoot within the preferred pool
      let mind  := (a1 :: as).foldl (fun m e => if e.overshoot < m then e.overshoot else m) a1.overshoot
      let tight := (a1 :: as).filter (fun e => approxEq e.overshoot mind eps)
      -- tie-break by minimal κ; pick a single deterministic winner
      match tight with
      | w1 :: ws =>
        let κmin := (w1 :: ws).foldl (fun m e => if e.report.kX < m then e.report.kX else m) w1.report.kX
        let winners := (w1 :: ws).filter (fun e => e.report.kX = κmin)
        match winners with
        | w :: _ => XTickDecision.realized [w]
        | []     => XTickDecision.idle barVal none
      | [] => XTickDecision.idle barVal none

/-- Apply realization of discovered X’s (superposition allowed). -/
def applyRealizationX (st : EngineState) (winners : List XOutcome) : EngineState :=
  let posts  := winners.map (·.report.post)
  let B'     := ctxUnion st.B (ctxUnionAll posts)
  let nuSum  := winners.foldl (fun s e => s + e.report.nu) 0
  let kSum   := winners.foldl (fun s e => s + e.report.kX) 0
  let hist'  := pushTick st.history nuSum kSum
  { B := B', H := 2, history := hist' }

/-- One tick in discovery mode (no curated packages). -/
def tickDiscover (cfg : DiscoverConfig) (st : EngineState) : XTickResult :=
  let τ := st.τ
  let barNow := acceptanceBar cfg.barMode st.history
  if !isFib τ then
    -- Non-Fibonacci tick: idle by schedule
    let st' := { st with H := st.H + 1, τ := τ + 1 }
    { decision := XTickDecision.idle barNow none, state' := st' }
  else
    let H := st.H
    -- discover all X under budget
    let XsSingles : List DiscoveredX := PEN.Select.Discover.discoverCandidates           st.B H cfg.actions
    let XsPairs   : List DiscoveredX := PEN.Select.Discover.discoverTFPairBundles        st.B H cfg.actions
    let XsHost    : List DiscoveredX := PEN.Select.Discover.discoverHITBundlesGeneric    st.B H cfg.actions

    let XsRaw    : List DiscoveredX := XsHost ++ XsPairs ++ XsSingles
    let XsPhase₀  : List DiscoveredX := suppressSubbundles XsRaw
    -- Phase discipline (Fibonacci curriculum): allow only bundles permitted at this τ
    let XsPhase  : List DiscoveredX := XsPhase₀   -- no τ-specific filtering


    -- Axiom 5 admissibility: level cap + foundation constraint
    let Lstar := contextLevel levelEnv st.B
let admissible : List DiscoveredX :=
  XsPhase.filter (fun X =>
    let Lx := targetLevel levelEnv X.targets
    let foundationOK := foundationOKForTargets levelEnv Lstar X.steps X.targets
    let goodBundle :=
      match commonHost? X.targets with
      | some h =>
          if looksLikeHITHost cfg.actions h then
            (not (allTFOnly X.targets)) && isFullForHost X.targets h
          else true
      | none => true
    (Lx ≤ Lstar + 1) && foundationOK && goodBundle && phaseAllow st.τ X.targets)
    -- score
    let evals : List XOutcome :=
      admissible.foldl
        (fun acc X =>
          match evalX? cfg st.B H st.history X with
          | some e => acc ++ [e]
          | none   => acc)
        []
    -- select winners
    let barNow := acceptanceBar cfg.barMode st.history
    let decision :=
      if evals.isEmpty then
        XTickDecision.idle barNow none
      else
        selectWinnersX st.B cfg.eps evals
    match decision with
    | XTickDecision.idle bar best? =>
        let st' := { st with H := st.H + 1, τ := τ + 1 }
        { decision := XTickDecision.idle bar best?, state' := st' }
    | XTickDecision.realized winners =>
        let st' := applyRealizationX st winners
        let st'' := { st' with τ := τ + 1 }
        { decision := XTickDecision.realized winners, state' := st'' }

/-- Run N ticks in discovery mode. -/
def runNTicksDiscover (cfg : DiscoverConfig) (st0 : EngineState) (n : Nat)
  : EngineState × List XTickResult :=
  let rec loop (i : Nat) (st : EngineState) (acc : List XTickResult) :=
    match i with
    | 0 => (st, acc)
    | Nat.succ i' =>
        let r := tickDiscover cfg st
        loop i' r.state' (acc ++ [r])
  loop n st0 []

/-- Try to evaluate a package under budget H; returns none if κ(X|B) > H or search fails. -/
def evalPkg? (B : Context) (H : Nat) (mode : BarMode) (hist : History) (pkg : Pkg)
  : Option EvalOutcome :=

  -- Skip packages that are already installed.
  if targetsHold B pkg.targets then
    none
  else
    -- Axiom 4: Level cap
    let Lstar := contextLevel levelEnv B
    let Lx    := targetLevel levelEnv pkg.targets
    if Lx > Lstar + 1 then
      none
    else
      -- (keep your existing minH check if you still want it for now)
      if H < pkg.minH then
        none
      else
      -- Axiom 4: Foundation gate via minimal derivation certificate
        match PEN.CAD.kappaMin? B (goalAllTargets pkg.targets) pkg.actions H with
        | none => none
        | some (_kXcert, certX) =>
          let foundationOK :=
            certX.deriv.all (fun a =>
              let ℓ := levelOfDecl levelEnv a
              (ℓ == Lstar) || (Lstar > 0 && ℓ == Lstar - 1))
          if !foundationOK then none else
            -- NEW: extend exclude for fresh types in pkg.targets
            --let freshTFs  := namesOfNewTypeFormers pkg.targets
            --let dropElims := eliminatorsForTypesIn pkg.actions freshTFs
            --let excl      := PEN.Novelty.Scope.dedupBEq (pkg.targets ++ dropElims)
            -- fresh type formers introduced by this X
            let freshTFs   := namesOfNewTypeFormers pkg.targets

            -- only the classifier-level ones
            let freshClass := freshTFs.filter isClassifierTypeName

            -- exclude their recursors and the comp-rules that tie to those recursors
            let dropElims  := eliminatorsForTypesIn pkg.actions freshClass
            let dropComps  := compRulesForElimsIn  pkg.actions dropElims

            -- allow the TF back onto the frontier *if* X is a full HIT (TF + ≥2 ctors + elim)
            let exclTargets :=
              match commonHost? pkg.targets with
              | some h =>
                  if isFullForHost pkg.targets h && pkg.targets.any (isTFFor h) then
                    -- keep elim/ctors excluded, but do *not* exclude the TF
                    pkg.targets.filter (fun a => ¬ isTFFor h a)
                  else pkg.targets
              | none => pkg.targets

            -- final exclude set
            let excl := PEN.Novelty.Scope.dedupBEq (exclTargets ++ dropElims ++ dropComps)


            let sc : ScopeConfig :=
              { actions       := pkg.actions
                enumerators   := pkg.enumerators
                horizon       := H
                preMaxDepth?  := some H
                postMaxDepth? := some (postRadius H hist)
                exclude       := excl }
      match PEN.Novelty.Novelty.noveltyForPackage? B pkg.targets sc (maxDepthX := H) with
        | none => none
        | some rep0 =>
            let rep := rep0
            let bar := acceptanceBar mode hist
            let δ   := rep.rho - bar
            some { pkg := pkg, report := rep, bar := bar, overshoot := δ }




/-! ## Tick result -/

inductive TickDecision
  | idle (bar : Float) (best? : Option EvalOutcome)  -- no one cleared the bar; best candidate (if any) for debugging
  | realized (winners : List EvalOutcome)            -- one or more (superposition)
deriving Repr

structure TickResult where
  decision : TickDecision
  state'   : EngineState
deriving Repr

/-- Package selection: **minimum** overshoot, tie-break by minimal κ, superposition if tied. -/
def selectWinners (eps : Float) (cands : List EvalOutcome) : TickDecision :=
  match cands with
  | [] => .idle 0.0 none
  | c1 :: cs =>
    let barVal := c1.bar
    let all    := c1 :: cs
    let accept := all.filter (fun e => floatGt e.report.rho barVal eps)
    match accept with
    | [] =>
      -- keep the debug "best by ρ" behavior as before
      let best :=
        all.foldl (fun (m : EvalOutcome) e => if e.report.rho > m.report.rho then e else m) c1
      .idle barVal (some best)
    | a1 :: as =>
      -- *** minimal overshoot (closest above the bar) ***
      let minδ  := (a1 :: as).foldl (fun m e => if e.overshoot < m then e.overshoot else m) a1.overshoot
      let minδs := (a1 :: as).filter (fun e => approxEq e.overshoot minδ eps)
      match minδs with
      | w1 :: ws =>
        let κmin := (w1 :: ws).foldl (fun m e => if e.report.kX < m then e.report.kX else m) w1.report.kX
        let winners := (w1 :: ws).filter (fun e => e.report.kX = κmin)
        .realized winners
      | [] => .idle barVal none


/-- Apply a realized set of winners: union contexts; push (Σν, Σκ); reset H. -/
def applyRealization (st : EngineState) (winners : List EvalOutcome) : EngineState :=
  let posts  := winners.map (·.report.post)
  let B'     := ctxUnion st.B (ctxUnionAll posts)
  let nuSum  := winners.foldl (fun s e => s + e.report.nu) 0
  let kSum   := winners.foldl (fun s e => s + e.report.kX) 0
  let hist'  := pushTick st.history nuSum kSum
  { B := B', H := 2, history := hist' }

/-- One selection step: evaluate, compare to bar, realize or idle, and update state. -/
def tick (cfg : EngineConfig) (st : EngineState) : TickResult :=
  let τ := st.τ
  let barNow := acceptanceBar cfg.barMode st.history
  if !isFib τ then
    let st' := { st with H := st.H + 1, τ := τ + 1 }
    { decision := TickDecision.idle barNow none, state' := st' }
  else
    let H := st.H
    -- evaluate each package under current budget
    let evals : List EvalOutcome :=
      cfg.pkgs.foldl
        (fun acc pkg =>
          match evalPkg? st.B H cfg.barMode st.history pkg with
          | some e => acc ++ [e]
          | none   => acc)
        []
    let decision := selectWinners cfg.eps evals
    match decision with
    | .idle bar best? =>
        -- expand horizon by one
        let st' := { st with H := st.H + 1, τ := τ + 1  }
        { decision := .idle bar best?, state' := st' }
    | .realized winners =>
        let st'  := applyRealization st winners            -- resets H := 2
        let st'' := { st' with τ := τ + 1 }                -- <-- add τ := τ + 1
        { decision := .realized winners, state' := st'' }

/-- Run N ticks, returning the final state and a vector of results. -/
def runNTicks (cfg : EngineConfig) (st0 : EngineState) (n : Nat)
  : EngineState × List TickResult :=
  let rec loop (i : Nat) (st : EngineState) (acc : List TickResult) :=
    match i with
    | 0 => (st, acc)
    | Nat.succ i' =>
        let r := tick cfg st
        loop i' r.state' (acc ++ [r])
  loop n st0 []

end PEN.Select.Engine
