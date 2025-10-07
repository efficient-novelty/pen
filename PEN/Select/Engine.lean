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
    - Acceptance if ρ ≥ Bar(history).
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
open PEN.Core.Levels

@[inline] def levelEnv : LevelEnv := defaultLevelEnv

/-! ## Engine configuration and state -/

/-- Which acceptance bar to use. -/
inductive BarMode
  | twoTap
  | phiOmega
  | resonance
deriving Repr, BEq, Inhabited

/-- Compute the current bar value from the history. -/
@[inline] def acceptanceBar (mode : BarMode) (beta : Float) (h : History) : Float :=
  match mode with
  | .twoTap    => barTwoTap h
  | .phiOmega  => barPhi h
  | .resonance => barResonance beta h

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
  beta     : Float    := PEN.Select.Bar.phi          -- kept for compatibility with alternate bars
  lastRealizedTau? : Option Nat := none
  layers   : List (List PEN.Novelty.Scope.Target) := []
deriving Repr, Inhabited

@[inline] def updateBetaOnIdle (β : Float) : Float :=
  max 1.0 (β / PEN.Select.Bar.phi)

@[inline] def updateBetaOnRealize (_β : Float) : Float :=
  PEN.Select.Bar.phi

/-- Optional external tick schedule. -/
inductive Schedule
  | none
  | fibonacci
deriving Repr, Inhabited

/-- Engine configuration (fixed across ticks). -/
structure EngineConfig where
  barMode : BarMode := .twoTap
  pkgs    : List Pkg := []
  eps     : Float := 1e-9
  schedule : Schedule := .none
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

@[inline] def floatGt (x y : Float) (eps : Float := 1e-9) : Bool :=
  x > y + eps

@[inline] def floatGe (x y : Float) (eps : Float := 1e-9) : Bool :=
  x + eps ≥ y

@[inline] def approxEq (x y : Float) (eps : Float := 1e-9) : Bool :=
  Float.abs (x - y) ≤ eps

@[inline] def holdsDecl (Γ : Context) : AtomicDecl → Bool
  | .declareUniverse ℓ      => Γ.hasUniverse ℓ
  | .declareInfrastructure n => Γ.hasInfrastructure n
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
      | AtomicDecl.declareEliminator _ T =>
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

@[inline] def tfOnly (ts : List AtomicDecl) : List AtomicDecl :=
  ts.filter (fun
    | .declareTypeFormer _ => true
    | _ => false)


/-- For each constructor c : T in `ts`, propose the two point-neighborhood terms. -/
@[inline] def neighborhoodTermsForCtors (ts : List AtomicDecl) : List AtomicDecl :=
  ts.foldl (fun acc a =>
    match a with
    | .declareConstructor c T =>
        acc ++ [AtomicDecl.declareTerm s!"refl_{c}" T,
                AtomicDecl.declareTerm s!"transport_{c}" T]
    | _ => acc) []

@[inline] def hiDimCtorNeighborhoods (host : String) (ts : List AtomicDecl) : List AtomicDecl :=
  -- Neighborhood terms for non-base constructors (e.g., the 2‑cell "surf0")
  ts.foldl (fun acc a =>
    match a with
    | .declareConstructor c T =>
        if T = host && c ≠ "base0" then
          acc ++ [AtomicDecl.declareTerm s!"refl_{c}" T,
                  AtomicDecl.declareTerm s!"transport_{c}" T]
        else acc
    | _ => acc) []

@[inline] def schemaTermForHost (h : String) : AtomicDecl :=
  AtomicDecl.declareTerm s!"schema_{h}" h


@[inline] def isClassifierTypeName (s : String) : Bool :=
  PEN.Novelty.Scope.isClassifierTFName s

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


open PEN.Select.Discover

@[inline] def isSubsetTargets (xs ys : List AtomicDecl) : Bool :=
  xs.all (fun a => ys.any (· == a))

/-- Keep TF-only cores even if supersets add non-TF atoms. -/
@[inline] def suppressSubbundles (xs : List (DiscoveredX)) : List (DiscoveredX) :=
  xs.filter (fun x =>
    not (xs.any (fun y =>
      (¬ (x.targets == y.targets)) &&
      isSubsetTargets x.targets y.targets &&
      (PEN.Novelty.Scope.allTFOnly x.targets && PEN.Novelty.Scope.allTFOnly y.targets))))

open PEN.Select.Discover  -- for `hostOf`

@[inline] def isElimFor (h : String) : AtomicDecl → Bool
  | .declareEliminator _ T => T == h
  | _                      => false

@[inline] def isCtorFor (h : String) : AtomicDecl → Bool
  | .declareConstructor _ T => T == h
  | _                       => false

@[inline] def commonHost? (ts : List AtomicDecl) : Option String :=
  let hosts :=
    ts.foldl (fun acc a =>
      match PEN.Select.Discover.hostOf a with
      | some h => if acc.any (· == h) then acc else acc ++ [h]
      | none   => acc) []
  match hosts with
  | [h] => some h
  | _   => none

@[inline] def isFullForHost (ts : List AtomicDecl) (h : String) : Bool :=
  let hasE := ts.any (isElimFor h)
  let nC   := ts.foldl (fun s a => s + (if isCtorFor h a then 1 else 0)) 0
  hasE && nC ≥ 2

@[inline] def isTFFor (h : String) : AtomicDecl → Bool
  | .declareTypeFormer n => n == h | _ => false


@[inline] def isClassifierTFDecl : AtomicDecl → Bool
  | .declareTypeFormer n => PEN.Novelty.Scope.isClassifierTFName n
  | _ => false

@[inline] def tfOrInfraOnly (ts : List AtomicDecl) : Bool :=
  ts.all (fun a =>
    match a with
    | .declareTypeFormer _     => true
    | .declareInfrastructure _ => true
    | _                        => false)

@[inline] def classifierTFCount (ts : List AtomicDecl) : Nat :=
  ts.foldl (fun s a =>
    s +
      match a with
      | .declareTypeFormer n => if isClassifierTypeName n then 1 else 0
      | _                    => 0) 0

@[inline] def isClassifierTFSetWithInfra (ts : List AtomicDecl) : Bool :=
  tfOrInfraOnly ts && classifierTFCount ts ≥ 2

@[inline] def isPureClassifierTFSet (ts : List AtomicDecl) : Bool :=
  allTFOnly ts && (ts.filter isClassifierTFDecl).length ≥ 2


@[inline] def isSchemaFor (h : String) : AtomicDecl → Bool
  | .declareTerm nm T => (T = h) && (nm = s!"schema_{h}")
  | _ => false

@[inline] def hasElimFor (h : String) (ts : List AtomicDecl) : Bool :=
  ts.any (fun a =>
    match a with
    | .declareEliminator _ T => T == h
    | _ => false)

@[inline] def sealedClassifierBundle (ts : List AtomicDecl) : Bool :=
  match commonHost? ts with
  | some h =>
      if isClassifierTypeName h then
        hasElimFor h ts && ts.any (isSchemaFor h)
      else
        true
  | none => true

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

@[inline] def ctorNamesFor (actions : List AtomicDecl) (h : String) : List String :=
  actions.foldl (fun acc a =>
    match a with
    | .declareConstructor c T =>
        if T == h then if acc.any (· == c) then acc else acc ++ [c] else acc
    | _ => acc) []

@[inline] def extraSuppressForTFSoloNonHIT
  (actions : List AtomicDecl) (h : String) : List PEN.Novelty.Scope.FrontierKey :=
  if looksLikeHITHost actions h then [] else
    let cs := ctorNamesFor actions h
    let nbs :=
      cs.foldl
        (fun acc c =>
          acc ++
            [ PEN.Novelty.Scope.FrontierKey.termExact h s!"refl_{c}"
            , PEN.Novelty.Scope.FrontierKey.termExact h s!"transport_{c}" ])
        []
    [ PEN.Novelty.Scope.FrontierKey.term h
    , PEN.Novelty.Scope.FrontierKey.termExact h "alias_Pi_family"
    , PEN.Novelty.Scope.FrontierKey.termExact h "alias_Sigma_family"
    ] ++ nbs

@[inline] def isPiSigmaAliasTFName (s : String) : Bool :=
  s == "alias_arrow" || s == "alias_forall" || s == "alias_eval" ||
  s == "alias_prod"  || s == "alias_exists"

@[inline] def isPiSigmaAliasKey : PEN.Novelty.Scope.FrontierKey → Bool
  | .termExact "Pi" "alias_Pi_family"       => true
  | .termExact "Sigma" "alias_Sigma_family" => true
  | .termExact host nm =>
      isPiSigmaAliasTFName host && nm == s!"schema_{host}"
  | .elim host => isPiSigmaAliasTFName host
  | .compElim nm =>
      if nm.startsWith "rec_alias_" then
        let candidate := nm.drop 4
        isPiSigmaAliasTFName candidate
      else
        false
  | _ => false


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
    infrastructure := dedupStr (A.infrastructure ++ B.infrastructure)
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

@[inline] def outcomeTargets (o : EvalOutcome) : List AtomicDecl :=
  match o with
  | ⟨p, _, _, _⟩ => p.targets

@[inline] def dedupByTargets (xs : List EvalOutcome) : List EvalOutcome :=
  xs.foldl
    (fun acc e =>
      let et := outcomeTargets e
      let seen := acc.any (fun f => outcomeTargets f == et)
      if seen then acc else acc ++ [e])
    []

/-- Extract the post-frontier targets (schemas) realized with a candidate. -/
@[inline] def frontierTargets (es : List PEN.Novelty.Scope.FrontierEntry)
  : List PEN.Novelty.Scope.Target :=
  es.map (·.target)

/-- Build the ScopeConfig for a package at the current horizon. -/
@[inline] def mkScope (pkg : Pkg) (H : Nat) (_hist : History) : ScopeConfig :=
  { actions       := pkg.actions
    enumerators   := pkg.enumerators
    horizon       := H
    preMaxDepth?  := some H
    postMaxDepth? := some H
    exclude       := pkg.targets
    excludeKeys   :=
      PEN.Novelty.Scope.dedupBEq
        (keysOfTargets pkg.targets
         ++ endoKeysForTFSet pkg.targets) }

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

@[inline] def isClassifierHost (h : String) : Bool :=
  PEN.Novelty.Scope.isClassifierTFName h   -- Π, Σ, Man live at the classifier level

@[inline] def containsTF (nm : String) (ts : List AtomicDecl) : Bool :=
  ts.any (fun a => match a with
                   | .declareTypeFormer n => n == nm
                   | _ => false)

@[inline] def pickFirstCtors (actions : List AtomicDecl) (h : String) (n : Nat) : List AtomicDecl :=
  let ctors := actions.filter (fun a => match a with
    | .declareConstructor _ T => T == h
    | _ => false)
  ctors.foldl (fun acc a => if acc.length < n && not (acc.any (· == a)) then acc ++ [a] else acc) []

@[inline] def pickElimForHost? (actions : List AtomicDecl) (h : String) : Option AtomicDecl :=
  actions.find? (fun a => match a with
    | .declareEliminator _ T => T == h
    | _ => false)

/-- Add one canonical comp rule e∘c for each host in `hosts`
    when both the elim and (a) constructor are present in `actions`. -/
@[inline] def addEndoCompsForHosts
    (actions : List AtomicDecl) (hosts : List String) : List AtomicDecl :=
  let comps :=
    hosts.foldl (fun acc h =>
      let el? := pickElimForHost? actions h
      let c?  := (pickFirstCtors actions h 1).head?
      match el?, c? with
      | some (.declareEliminator e _), some (.declareConstructor c _) =>
          if actions.any (fun a => match a with
                                   | .declareCompRule e' c' => e' = e && c' = c
                                   | _ => false) then acc
          else acc ++ [AtomicDecl.declareCompRule e c]
      | _, _ => acc) []
  PEN.Novelty.Scope.dedupBEq (actions ++ comps)

/-- If `ts` names a non-classifier host and actions contain a plausible HIT
    (≥2 ctors + an eliminator), augment `ts` to a *full/ sealed* HIT core:
    TF(h) + two ctors + one eliminator (dedup). -/
@[inline] def sealHITTargets (actions : List AtomicDecl) (ts : List AtomicDecl) : List AtomicDecl :=
  match commonHost? ts with
  | some h =>
      if isClassifierTypeName h then
        ts
      else if looksLikeHITHost actions h then
        let tf  := (if ts.any (isTFFor h) then [] else [AtomicDecl.declareTypeFormer h])
        let cs  := pickFirstCtors actions h 2 |>.filter (fun c => not (ts.any (· == c)))
        let el? := pickElimForHost? actions h
        let el  := match el? with | some e => if ts.any (· == e) then [] else [e] | none => []
        PEN.Novelty.Scope.dedupBEq (ts ++ tf ++ cs ++ el)
      else
        ts
  | none => ts

@[inline] def sealHITCoreNoElim (actions : List AtomicDecl) (ts : List AtomicDecl) : List AtomicDecl :=
  match commonHost? ts with
  | some h =>
      if isClassifierTypeName h then ts else
      let tf := (if ts.any (isTFFor h) then [] else [AtomicDecl.declareTypeFormer h])
      let cs :=
        if looksLikeHITHost actions h then
          pickFirstCtors actions h 2 |>.filter (fun c => not (ts.any (· == c)))
        else
          []
      PEN.Novelty.Scope.dedupBEq (ts ++ tf ++ cs)
  | none => ts

@[inline] def isPiSigmaDual (ts : List AtomicDecl) : Bool :=
  containsTF "Pi" ts && containsTF "Sigma" ts

/-- Add a canonical (C,E,R) triple to seal Π/Σ (choose Π deterministically). -/
@[inline] def sealPiSigmaTargets (actions : List AtomicDecl) (ts : List AtomicDecl) : List AtomicDecl :=
  if isPiSigmaDual ts then
      let ctor? : Option AtomicDecl :=
        actions.find? (fun a => match a with
                                | .declareConstructor _c T => T == "Pi"
                                | _ => false)
      let elim? : Option AtomicDecl :=
        actions.find? (fun a => match a with
                                | .declareEliminator _e T => T == "Pi"
                                | _ => false)
    let comp? : Option AtomicDecl :=
      match elim?, ctor? with
      | some (.declareEliminator e _), some (.declareConstructor c _) =>
          some (AtomicDecl.declareCompRule e c)
      | _, _ => none
    let extras := [ctor?, elim?, comp?].filterMap id
    PEN.Novelty.Scope.dedupBEq (ts ++ extras)
  else
    ts

@[inline] def hasEndoTripleFor (host : String) (ts : List AtomicDecl) : Bool :=
  let elims := ts.foldl (fun acc a =>
    match a with
    | .declareEliminator e T  => if T == host then e :: acc else acc
    | _ => acc) []
  let ctors := ts.foldl (fun acc a =>
    match a with
    | .declareConstructor c T => if T == host then c :: acc else acc
    | _ => acc) []
  let comps := ts.foldl (fun acc a =>
    match a with
    | .declareCompRule e c   => (e,c) :: acc
    | _ => acc) []
  elims.any (fun e => ctors.any (fun c => comps.any (· == (e,c))))

@[inline] def isSealedPiSigma (ts : List AtomicDecl) : Bool :=
  containsTF "Pi" ts && containsTF "Sigma" ts &&
  (hasEndoTripleFor "Pi" ts || hasEndoTripleFor "Sigma" ts)

@[inline] def tfsSubsetOf (allow : List String) (ts : List AtomicDecl) : Bool :=
  allTFOnly ts &&
  ts.all (fun a => match a with
                   | .declareTypeFormer n => allow.any (· == n)
                   | _ => false)

@[inline] def allowFound (ℓ Lstar : Nat) : Bool :=
  (ℓ == Lstar) || (Lstar > 0 && ℓ == Lstar - 1)

@[inline] def opensNewStratum (B : Context) (ts : List AtomicDecl) : Bool :=
  match commonHost? ts with
  | some h =>
      let Lstar := contextLevel levelEnv B
      let Lx    := targetLevel levelEnv ts
      (¬ isClassifierHost h) && isFullForHost ts h && (Lx = Lstar + 1)
  | none => false

@[inline] def allUniversesOnly (ts : List AtomicDecl) : Bool :=
  ts.all (fun a => match a with | .declareUniverse _ => true | _ => false)

@[inline] def newTFNamesInTargets (B : Context) (ts : List AtomicDecl) : List String :=
  ts.foldl (fun acc a =>
    match a with
    | .declareTypeFormer n =>
        if B.hasTypeFormer n || acc.any (· == n) then acc else acc ++ [n]
    | _ => acc) []

@[inline] def newCtorCountInTargets (B : Context) (ts : List AtomicDecl) : Nat :=
  ts.foldl (fun s a =>
    s + match a with
        | .declareConstructor c _ => if B.hasConstructor c then 0 else 1
        | _ => 0) 0

/-- Axiom‑3 small‑radius guard:
    At H ≤ 2, forbid multi‑host TF‑only bundles (≥2 new hosts),
    forbid >1 new constructor, and forbid mixing host+ctor in one go. -/
@[inline] def smallRadiusCapOK (B : Context) (H : Nat) (ts : List AtomicDecl) : Bool :=
  if H ≤ 2 then
    let nHosts := (newTFNamesInTargets B ts).length
    let nCtors := newCtorCountInTargets B ts
    let tfOnly := allTFOnly ts
    let noMultiHost := !(tfOnly && nHosts ≥ 2)
    let noCtorBurst := nCtors ≤ 1
    let noMix       := !(nHosts = 1 && nCtors = 1)
    noMultiHost && noCtorBurst && noMix
  else true


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
  debugFrontier : Bool := false
  schedule : Schedule := .none
deriving Repr, Inhabited

/-- Outcome for a discovered candidate X (for selection & printing). -/
structure XOutcome where
  x         : DiscoveredX
  report    : NoveltyReport
  bar       : Float
  overshoot : Float
  usedLvls  : List Nat    -- foundation audit: distinct levels in the minimal derivation
deriving Repr

@[inline] def xOutcomeTargets (o : XOutcome) : List AtomicDecl :=
  match o with
  | ⟨x, _, _, _, _⟩ => x.targets

@[inline] def dedupXByTargets (xs : List XOutcome) : List XOutcome :=
  xs.foldl
    (fun acc e =>
      let et := xOutcomeTargets e
      let seen := acc.any (fun f => xOutcomeTargets f == et)
      if seen then acc else acc ++ [e])
    []

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
def evalX? (cfg : DiscoverConfig) (st : EngineState) (H : Nat) (bar : Float) (X : DiscoveredX)
  : Option XOutcome :=
  /- classify the bundle X -/
  let B := st.B
  let _isUnitSingleton : Bool :=
    X.targets.length = 1 && X.targets.any isUnitTF

  /- full HIT host if X contains TF + ≥ 2 ctors + elim for the same host -/
  let fullHitHost? : Option String :=
    match commonHost? X.targets with
    | some h => if isFullForHost X.targets h then some h else none
    | none   => none

  -- Does X open the next stratum? (used to expose hi-dim ctor neighbors + schema host term)
  let _opensJump := opensNewStratum B X.targets

  let targetsCore := sealHITCoreNoElim cfg.actions X.targets
  let host? := commonHost? targetsCore

  /- compute enumerators, action tweaks, and excludes based on X -/
  open PEN.Novelty.Enumerators in
  let actions' : List AtomicDecl :=
    if isPureClassifierTFSet X.targets || isClassifierTFSetWithInfra X.targets then
      let hasPiSigma := containsTF "Pi" X.targets && containsTF "Sigma" X.targets
      if hasPiSigma && H ≥ 3 then
        let base := PEN.Novelty.Enumerators.actionsWithPiSigmaAliasTerms cfg.actions
        let base' := if H ≤ 3 then keepOnePiSigmaAlias base "alias_arrow" else base
        base'
      else
        cfg.actions
    else if isClassifierTFSolo X.targets then
      cfg.actions
    else
      match host? with
      | some h =>
          if looksLikeHITHost cfg.actions h then
            actionsWithPiSigmaAliases cfg.actions h
          else
            cfg.actions
      | none   => cfg.actions

  -- If this X contains Man, only expose the 8 Man maps once S¹ is already in B.
  let xHasMan : Bool :=
    X.targets.any (fun a => match a with
      | .declareTypeFormer "Man" => true
      | _ => false)

  let actions'' : List AtomicDecl :=
    PEN.Novelty.Scope.dedupBEq (
      if xHasMan && B.hasTypeFormer "S1" then
        actionsWithClassifierMapTerms actions' "Man"
      else
        actions')

  -- keep ctor neighborhoods in the actions menu (for κ computations)
  let nbTerms   := neighborhoodTermsForCtors targetsCore

  -- include the jump extras also in the actions (so κ_post can be computed)
  let jumpExtras : List AtomicDecl :=
    match host? with
    | some h =>
        let hi := hiDimCtorNeighborhoods h targetsCore
        let schema :=
          match fullHitHost? with
          | some h' => if h' == h then [schemaTermForHost h] else []
          | none    => []
        hi ++ schema
    | none   => []

  let actions''' : List AtomicDecl :=
    PEN.Novelty.Scope.dedupBEq (actions'' ++ nbTerms ++ jumpExtras)

  let hostsForEndo : List String :=
    if isPiSigmaDual targetsCore then ["Pi", "Sigma"]
    else match host? with | some h => [h] | none => []
  let actions'''' : List AtomicDecl :=
    addEndoCompsForHosts actions''' hostsForEndo

  let xIsTFSolo := PEN.Novelty.Scope.allTFOnly targetsCore
  let hostSuppress :=
    match host? with
    | some h => if xIsTFSolo then extraSuppressForTFSoloNonHIT cfg.actions h else []
    | none   => []

  let wantsCtor := X.targets.any (fun a => match a with | .declareConstructor _ _ => true | _ => false)
  let wantsElim := X.targets.any (fun a => match a with | .declareEliminator _ _ => true | _ => false)
  let elimSuppress :=
    match host? with
    | some h =>
        if wantsCtor && !wantsElim then
          [ PEN.Novelty.Scope.FrontierKey.elim h
          , PEN.Novelty.Scope.FrontierKey.compElim s!"rec_{h}" ]
        else
          []
    | none => []

  let exTargets : List AtomicDecl :=
    if isPiSigmaDual targetsCore && H ≤ 3 then
      tfOnly targetsCore
    else
      targetsCore

  let baseKeys :=
    keysOfTargets exTargets ++ hostSuppress ++ elimSuppress

  let endo' :=
    if isPiSigmaDual targetsCore then
      (endoKeysForTFSet targetsCore).filter (fun k => !isPiSigmaAliasKey k)
    else
      endoKeysForTFSet targetsCore

  let exKeys := PEN.Novelty.Scope.dedupBEq (baseKeys ++ endo')

  let sc : ScopeConfig :=
    { actions       := actions''''
      horizon       := H
      preMaxDepth?  := some H
      postMaxDepth? := some H
      exclude       := exTargets
      excludeKeys   := exKeys }
  let targets1 := sealHITTargets actions'''' X.targets
  -- Keep Π/Σ pair pure at small radius so κ fits within H=3 (τ≈5).
  let targetsSealed :=
    if isPiSigmaDual targets1 && H ≤ 3 then
      targets1
    else
      sealPiSigmaTargets actions'''' targets1

  let Lstar := contextLevel levelEnv B
  match PEN.CAD.kappaMin? B (goalAllTargets targetsSealed) actions'''' H with
  | none => none
  | some (_kX, certX) =>
      let okFound := foundationOKForTargets levelEnv Lstar certX.deriv targetsSealed
      if !okFound then
        none
      else
        let I := PEN.Novelty.Novelty.interfaceBasis st.layers
        match PEN.Novelty.Novelty.noveltyForPackage? B targetsSealed sc I (maxDepthX := H) with
        | none => none
        | some rep0 => do
            let rep := rep0
            let diag := (PEN.Novelty.Scope.Debug.frontierWithDiag B rep.post sc).2
            if cfg.debugFrontier then
              dbg_trace (PEN.Novelty.Scope.Debug.render diag)
            let δ   := rep.rho - bar
            let usedLvls :=
              let raw := certX.deriv.map (levelOfDecl levelEnv)
              raw.foldl (fun acc ℓ => if acc.any (· == ℓ) then acc else acc ++ [ℓ]) []
            return { x := X, report := rep, bar := bar, overshoot := δ, usedLvls := usedLvls }

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
    - accept only those with ρ ≥ bar
    - prefer **attached** work (if any); else keep all accepted
    - among that pool, pick **minimal overshoot**; tie-break by minimal κ
    - realize all ties (superposition) when κ is also tied. -/
def selectWinnersX (B : Context) (eps : Float) (cands : List XOutcome) : XTickDecision :=
  match cands with
  | [] => XTickDecision.idle 0.0 none
  | c1 :: cs =>
    let barVal  := c1.bar
    let all     := c1 :: cs
    let accept0 := all.filter (fun e => floatGe e.report.rho barVal eps)
    let accept  := preferAccepted B accept0
    let pool    := pruneAfterAccept accept
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
        XTickDecision.realized winners
      | [] => XTickDecision.idle barVal none

/-- Apply realization of discovered X’s (superposition allowed). -/
def applyRealizationX (st : EngineState) (winners : List XOutcome) : EngineState :=
  let posts  := winners.map (·.report.post)
  let B'     := ctxUnion st.B (ctxUnionAll posts)
  let nuSum  := winners.foldl (fun s e => s + e.report.nu) 0
  let kSum   := winners.foldl (fun s e => s + e.report.kX) 0
  let hist'  := pushTick st.history nuSum kSum
  -- was: let Lnew := winners.bind (fun w => frontierTargets w.report.frontier)
  let Lnew  := winners.foldr (fun w acc => frontierTargets w.report.frontier ++ acc) []
  { st with
      B := B', H := 2, history := hist',
      lastRealizedTau? := some st.τ,
      layers := (PEN.Novelty.Scope.dedupBEq Lnew) :: st.layers.take 1 }

/-- One tick in discovery mode (no curated packages). -/
def tickDiscover (cfg : DiscoverConfig) (st : EngineState) : XTickResult :=
  let τ := st.τ
  let barNow := PEN.Select.Bar.barGlobal st.τ st.lastRealizedTau? st.history
  let gatedIdle := match cfg.schedule with
                   | .fibonacci => !isFib τ
                   | .none      => false
  if gatedIdle then
    let st' := { st with H := st.H + 1, τ := τ + 1, beta := updateBetaOnIdle st.beta }
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
    smallRadiusCapOK st.B H X.targets &&
    let Lx := targetLevel levelEnv X.targets
    let foundationOK := foundationOKForTargets levelEnv Lstar X.steps X.targets
    let bootOK :=
      if st.B.hasAnyUniverse then true
      else
        X.targets.all (fun a => match a with | .declareUniverse _ => true | _ => false)
        &&
        X.targets.any (fun a => match a with | .declareUniverse 0 => true | _ => false)
    let goodBundle :=
      match commonHost? X.targets with
      | some h =>
          if isClassifierTypeName h then
            sealedClassifierBundle X.targets
          else if looksLikeHITHost cfg.actions h then
            (not (allTFOnly X.targets)) && isFullForHost X.targets h
          else
            PEN.Novelty.Scope.allTFOnly X.targets ||
            attachesToB st.B X.targets  -- don’t sprout isolated non-HIT TFs
      | none =>
          allUniversesOnly X.targets
          || allTFOnly X.targets
          || isClassifierTFSetWithInfra X.targets

    (Lx ≤ Lstar + 1) && foundationOK && bootOK && goodBundle)
    -- score
    let evals : List XOutcome := dedupXByTargets <|
      admissible.foldl
        (fun acc X =>
          match evalX? cfg st H barNow X with
          | some e => acc ++ [e]
          | none   => acc)
        []
    -- select winners
    let decision :=
      if evals.isEmpty then
        XTickDecision.idle barNow none
      else
        selectWinnersX st.B cfg.eps evals
    match decision with
    | XTickDecision.idle bar best? =>
        let st' := { st with H := st.H + 1, τ := τ + 1, beta := updateBetaOnIdle st.beta }
        { decision := XTickDecision.idle bar best?, state' := st' }
    | XTickDecision.realized winners =>
        let st' := applyRealizationX st winners
        let st'' := { st' with τ := st'.τ + 1, beta := updateBetaOnRealize st'.beta }
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
def evalPkg? (st : EngineState) (H : Nat) (bar : Float) (pkg : Pkg)
  : Option EvalOutcome :=

  let B := st.B
  -- Skip packages that are already installed.
  if targetsHold B pkg.targets then
    none
  else
    -- Axiom 4: Level cap
    let Lstar := contextLevel levelEnv B
    let Lx    := targetLevel levelEnv pkg.targets
    if Lx > Lstar + 1 then
      none
    else if H < pkg.minH then
      none
    else if !smallRadiusCapOK B H pkg.targets then
      none
    else
      -- *** seal the targets before κ/ν ***
      let targets0 := pkg.targets
      let targetsCore := sealHITCoreNoElim pkg.actions targets0
      let targets1 := sealHITTargets pkg.actions targets0
      -- Same policy as discovery: don't bulk up Π/Σ at small radius.
      let targetsSealed :=
        if isPiSigmaDual targets1 && H ≤ 3 then
          targets1
        else
          sealPiSigmaTargets pkg.actions targets1

      -- *** gate AFTER sealing ***
      let goodBundle :=
        match commonHost? targetsSealed with
        | some h =>
            if isClassifierTypeName h then
              sealedClassifierBundle targetsSealed
            else if looksLikeHITHost pkg.actions h then
              isFullForHost targetsSealed h
            else
              PEN.Novelty.Scope.allTFOnly targetsSealed ||
              attachesToB B targetsSealed
        | none => true

      if !goodBundle then
        none
      else
        let host? := commonHost? targetsCore

        -- Build the EXACT action alphabet we’ll also use for novelty
        let fullHitHost? : Option String :=
          match commonHost? targetsSealed with
          | some h => if isFullForHost targetsSealed h then some h else none
          | none   => none

        let _opensJump := opensNewStratum B targetsSealed
        let jumpExtras : List AtomicDecl :=
          match fullHitHost? with
          | some h => hiDimCtorNeighborhoods h targetsSealed ++ [schemaTermForHost h]
          | none   => []

        let xHasManPkg : Bool :=
          targetsSealed.any (fun a => match a with
                                      | .declareTypeFormer "Man" => true
                                      | _ => false)

        let actionsWithMaps : List AtomicDecl :=
          PEN.Novelty.Scope.dedupBEq (
            if xHasManPkg && B.hasTypeFormer "S1" then
              actionsWithClassifierMapTerms pkg.actions "Man"
            else
              pkg.actions)

        let actionsWithAliases : List AtomicDecl :=
          match fullHitHost? with
          | some h => actionsWithPiSigmaAliases actionsWithMaps h
          | none   =>
              if isPureClassifierTFSet targetsSealed || isClassifierTFSetWithInfra targetsSealed then
                let hasPiSigma := containsTF "Pi" targetsSealed && containsTF "Sigma" targetsSealed
                if hasPiSigma && H ≥ 3 then
                  let base := PEN.Novelty.Enumerators.actionsWithPiSigmaAliasTerms actionsWithMaps
                  let base' := if H ≤ 3 then keepOnePiSigmaAlias base "alias_arrow" else base
                  base'
                else
                  actionsWithMaps
              else
                actionsWithMaps

        let nbTerms   := neighborhoodTermsForCtors targetsSealed
        let actionsAug : List AtomicDecl :=
          PEN.Novelty.Scope.dedupBEq (actionsWithAliases ++ nbTerms ++ jumpExtras)

        let hostsForEndo : List String :=
          if isPiSigmaDual targetsSealed then ["Pi", "Sigma"]
          else match commonHost? targetsSealed with | some h => [h] | none => []
        let actionsAug' : List AtomicDecl :=
          addEndoCompsForHosts actionsAug hostsForEndo

        -- *** Use the SAME alphabet for κ-admissibility ***
        match PEN.CAD.kappaMin? B (goalAllTargets targetsSealed) actionsAug' H with
        | none => none
        | some (_kXcert, certX) =>
          let foundationOK :=
            certX.deriv.all (fun a =>
              let ℓ := levelOfDecl levelEnv a
              (ℓ == Lstar) || (Lstar > 0 && ℓ == Lstar - 1))
          if !foundationOK then none else
            let xIsTFSolo := PEN.Novelty.Scope.allTFOnly targetsCore
            let hostSuppress :=
              match host? with
              | some h => if xIsTFSolo then extraSuppressForTFSoloNonHIT pkg.actions h else []
              | none   => []

            let wantsCtor := pkg.targets.any (fun a => match a with | .declareConstructor _ _ => true | _ => false)
            let wantsElim := pkg.targets.any (fun a => match a with | .declareEliminator _ _ => true | _ => false)
            let elimSuppress :=
              match host? with
              | some h =>
                  if wantsCtor && !wantsElim then
                    [ PEN.Novelty.Scope.FrontierKey.elim h
                    , PEN.Novelty.Scope.FrontierKey.compElim s!"rec_{h}" ]
                  else
                    []
              | none => []

            let exTargets : List AtomicDecl :=
              if isPiSigmaDual targetsSealed && H ≤ 3 then
                tfOnly targetsSealed
              else
                targetsSealed

            let baseKeys :=
              keysOfTargets exTargets ++ hostSuppress ++ elimSuppress

            let endo' :=
              if isPiSigmaDual targetsSealed then
                (endoKeysForTFSet targetsSealed).filter (fun k => !isPiSigmaAliasKey k)
              else
                endoKeysForTFSet targetsSealed

            let exKeys := PEN.Novelty.Scope.dedupBEq (baseKeys ++ endo')

            let I := PEN.Novelty.Novelty.interfaceBasis st.layers
            let sc : ScopeConfig :=
              { actions       := actionsAug'
                horizon       := H
                preMaxDepth?  := some H
                postMaxDepth? := some H
                exclude       := exTargets
                excludeKeys   := exKeys }

            match PEN.Novelty.Novelty.noveltyForPackage? B targetsSealed sc I (maxDepthX := H) with
            | none => none
            | some rep0 =>
                let rep := rep0
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
    let accept := all.filter (fun e => floatGe e.report.rho barVal eps)
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
  -- was: let Lnew := winners.bind (fun w => frontierTargets w.report.frontier)
  let Lnew  := winners.foldr (fun w acc => frontierTargets w.report.frontier ++ acc) []
  { st with
      B := B', H := 2, history := hist',
      lastRealizedTau? := some st.τ,
      layers := (PEN.Novelty.Scope.dedupBEq Lnew) :: st.layers.take 1 }

/-- One selection step: evaluate, compare to bar, realize or idle, and update state. -/
def tick (cfg : EngineConfig) (st : EngineState) : TickResult :=
  let τ := st.τ
  let barNow := PEN.Select.Bar.barGlobal st.τ st.lastRealizedTau? st.history
  let gatedIdle := match cfg.schedule with
                   | .fibonacci => !isFib τ
                   | .none      => false
  if gatedIdle then
    let st' := { st with H := st.H + 1, τ := τ + 1, beta := updateBetaOnIdle st.beta }
    { decision := TickDecision.idle barNow none, state' := st' }
  else
    let H := st.H
    -- evaluate each package under current budget
    let evals : List EvalOutcome := dedupByTargets <|
      cfg.pkgs.foldl
        (fun acc pkg =>
          match evalPkg? st H barNow pkg with
          | some e => acc ++ [e]
          | none   => acc)
        []
    let decision := selectWinners cfg.eps evals
    match decision with
    | .idle bar best? =>
        -- expand horizon by one
        let st' := { st with H := st.H + 1, τ := τ + 1, beta := updateBetaOnIdle st.beta }
        { decision := .idle bar best?, state' := st' }
    | .realized winners =>
        let st'  := applyRealization st winners            -- resets H := 2
        let st'' := { st' with τ := st'.τ + 1, beta := updateBetaOnRealize st'.beta }
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
