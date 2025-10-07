/-
  PEN/Novelty/Scope.lean

  Horizon-bounded frontier enumeration for novelty computation.
  Given:
    * pre  : Context  (B)
    * post : Context  (B ∪ {X})
    * cfg  : ScopeConfig (actions, enumerators, horizon ...)

  We:
    1) gather targets Y from the post context using enumerators,
    2) keep only those with post-cost κ(Y | post) ≤ H,
    3) compute a truncated pre-cost κ̃(Y | pre) where failures count as H+1,
    4) return a deduplicated list of (target, κ_post, κ̃_pre).

  Novelty later sums max(0, κ̃_pre - κ_post) over this list.
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa
import PEN.Grammar.HIT

namespace PEN.Novelty.Scope

open PEN.CAD

/-- Targets considered for novelty are `AtomicDecl`-goals (presence in a context). -/
abbrev Target := AtomicDecl

/-- A frontier enumerator lists candidate targets, given the post context. -/
abbrev FrontierEnumerator := Context → List Target

/-- Horizon-bounded frontier entry with both post and truncated pre efforts. -/
structure FrontierEntry where
  target  : Target
  kPost   : Nat       -- κ(Y | post)  (guaranteed ≤ H)
  kPreEff : Nat       -- κ̃(Y | pre)   (pre-cost with truncation to H+1)
deriving Repr

/-! ############################
    Schema key (Axiom 3: K)
############################# -/

/-- Frontier items are keyed coarsely (by host) except Π/Σ aliases,
    which must be counted distinctly (exact-by-name). -/
inductive FrontierKey where
  | universe (lvl : Nat)
  | typeFormer                                 -- collapse all TFs into one class
  | ctor     (typeName : String)               -- all ctors for same host
  | elim     (typeName : String)               -- eliminators by host
  | compElim (elimName : String)               -- comp rules keyed by eliminator
  | term     (typeName : String)               -- all general terms by host
  | termExact (typeName : String) (termName : String)  -- exact key for Π/Σ aliases
  | exact    (t : Target)                      -- fallback (rare)
deriving BEq, Repr, Inhabited

/-!
### Axiom 3 remark (Endogenous attachments don’t score)

When a package X introduces a **classifier** `T`,
frontier targets that are *endogenous* to T’s own installation are keyed to the
same schema class as the type former itself. Because we add the keys of X.targets
to `excludeKeys`, these items never contribute to novelty for that X.

Endogenous items for classifiers:
  • the canonical eliminator (e.g., `hom_T`, `C∞_T`),
  • the bundled closure/schema term `schema_T`,
  • Pi/Sigma syntax aliases (`alias_arrow/forall/eval` on `Pi`;
    `alias_prod/exists` on `Sigma`).

This lets novelty measure **external affordances** (e.g. Man maps) without τ-specific rules.
-/

@[inline] def isClassifierTFName (s : String) : Bool :=
  s == "Pi" || s == "Sigma" || s == "Man"

@[inline] def isSchemaNameFor (nm T : String) : Bool :=
  nm == s!"schema_{T}"

@[inline] def isPiAliasName (nm : String) : Bool :=
  nm == "alias_arrow" || nm == "alias_forall" || nm == "alias_eval"

@[inline] def isSigmaAliasName (nm : String) : Bool :=
  nm == "alias_prod"  || nm == "alias_exists"

@[inline] def isPiSigmaAlias (nm : String) (T : String) : Bool :=
  (T == "Pi"    && isPiAliasName nm) ||
  (T == "Sigma" && isSigmaAliasName nm)

/-- Neighborhood terms for non-base constructors are named
    "refl_<ctor>" / "transport_<ctor>". -/
@[inline] def isCtorNeighborhoodTerm (nm : String) : Bool :=
  nm.startsWith "refl_" || nm.startsWith "transport_"

@[inline] def ctorNameOfNeighborhood? (nm : String) : Option String :=
  if nm.startsWith "refl_" then some (nm.drop 5)
  else if nm.startsWith "transport_" then some (nm.drop 10)
  else none

@[inline] def baseCtorLike (c : String) : Bool :=
  c.endsWith ".base0" || c == "base0"

@[inline] def dimOfCtorName (c : String) : Nat :=
  if baseCtorLike c then
    0
  else if c.endsWith ".loop0" || c == "loop0" then
    1
  else if c.endsWith ".surf0" || c == "surf0" then
    2
  else
    1  -- conservative default for other positive-dim ctors

@[inline] def hostOfElim? (Γ : Context) (e : String) : Option String :=
  (Γ.eliminators.find? (fun (e', _) => e' == e)).map (·.snd)

@[inline] def maxCtorDimForHost (Γ : Context) (host : String) : Nat :=
  Γ.constructors.foldl (fun m (c, T) =>
    if T == host then Nat.max m (dimOfCtorName c) else m) 0

@[inline] def capForKeyWithPost (post : Context) (k : FrontierKey) : Nat :=
  match k with
  | FrontierKey.termExact _ nm =>
      match ctorNameOfNeighborhood? nm with
      | some c =>
          let d := dimOfCtorName c
          if d == 0 then 2 else if d == 1 then 2 else 3
      | none =>
          -- Π/Σ families & closure use cap=2
          if nm == "alias_Pi_family" || nm == "alias_Sigma_family" then 2
          else 2
  | FrontierKey.compElim e =>
      match hostOfElim? post e with
      | some h =>
          let d := maxCtorDimForHost post h
          if d >= 2 then 3 else 2
      | none   => 2
  | _ => 2

/-!
Axiom 3 schema keying:

  • universes → per-level key
  • all type formers → one class (FrontierKey.typeFormer)
  • constructors → key by host (FrontierKey.ctor host)
  • eliminators → key by host (FrontierKey.elim host)
  • comp rules  → key by eliminator (FrontierKey.compElim elim)
  • general terms → keyed by host (FrontierKey.term host)
  • Π/Σ aliases → exact term key (FrontierKey.termExact host name)
  • classifier schema_* → typeFormer
-/

@[inline] def keyOfTarget (t : Target) : FrontierKey :=
  match t with
  | AtomicDecl.declareUniverse ℓ      => FrontierKey.universe ℓ
  | AtomicDecl.declareInfrastructure _ => FrontierKey.exact t
  | AtomicDecl.declareTypeFormer _    => FrontierKey.typeFormer
  | AtomicDecl.declareConstructor _ T => FrontierKey.ctor T
  | AtomicDecl.declareEliminator _ T  => FrontierKey.elim T
  | AtomicDecl.declareCompRule e _ =>
      -- Axiom 3′: comp rules bundle by eliminator
      FrontierKey.compElim e

  | AtomicDecl.declareTerm nm T =>
      if isClassifierTFName T && isSchemaNameFor nm T then
        FrontierKey.typeFormer   -- classifier schema is endogenous
      else if isClassifierTFName T && isPiSigmaAlias nm T then
        FrontierKey.typeFormer   -- Π/Σ aliases are endogenous at classifier level
      else if isCtorNeighborhoodTerm nm then
        FrontierKey.termExact T nm
      else if isSchemaNameFor nm T then
        FrontierKey.termExact T nm
      else if isClassifierTFName T then
        FrontierKey.termExact T nm
      else
        -- Axiom 3′: on non-classifier hosts, split Π/Σ aliases into two families
        if isPiAliasName nm then FrontierKey.termExact T "alias_Pi_family"
        else if isSigmaAliasName nm then FrontierKey.termExact T "alias_Sigma_family"
        else FrontierKey.term T

@[inline] def keysOfTargets (ts : List Target) : List FrontierKey :=
  let rec add (acc : List FrontierKey) (k : FrontierKey) : List FrontierKey :=
    if acc.any (· == k) then acc else acc ++ [k]
  ts.foldl (fun acc t => add acc (keyOfTarget t)) []

@[inline] def hasKey (ks : List FrontierKey) (t : Target) : Bool :=
  ks.any (· == keyOfTarget t)

@[inline] def allTFOnly (ts : List AtomicDecl) : Bool :=
  ts.all (fun a => match a with | .declareTypeFormer _ => true | _ => false)

@[inline] def tfNamesIn (ts : List AtomicDecl) : List String :=
  ts.foldl (fun acc a =>
    match a with
    | AtomicDecl.declareTypeFormer n =>
        if acc.any (· == n) then acc else acc ++ [n]
    | _ => acc) []

/-- Endogenous attachments for any TF-only bundle (incl. classifiers):
    • ctor(host), elim(host), comp(rec_host), schema_host.
    (Do NOT include Π/Σ alias keys here — they are intended to score.) -/
@[inline] def endoKeysForTFSet (ts : List AtomicDecl) : List FrontierKey :=
  if allTFOnly ts then
    let tns := tfNamesIn ts
    tns.foldl (fun acc h =>
      let base : List FrontierKey :=
        [ FrontierKey.compElim s!"rec_{h}"
        , FrontierKey.termExact h s!"schema_{h}" ]
      -- Match unit-test policy: for non-classifier TFs, suppress only the eliminator,
      -- not the constructor. (Pi/Sigma handled elsewhere by keying rules.)
      let extra : List FrontierKey :=
        if h == "Pi" || h == "Sigma" then [] else [FrontierKey.elim h]
      acc ++ extra ++ base) []
  else
    []


@[inline] def declDependsOn (y x : AtomicDecl) : Bool :=
  match y with
  | .declareUniverse _ => false
  | .declareInfrastructure _ => false
  | .declareTypeFormer name =>
      match x with
      | .declareUniverse _ => true
      | .declareInfrastructure infra =>
          (infra == "INFRA.DepBinder") && (name == "Pi" || name == "Sigma")
      | _                  => false
  | .declareConstructor _ T =>
      match x with
      | .declareTypeFormer T' => T == T'
      | .declareUniverse _    => false
      | _                     => false
  | .declareEliminator _ T =>
      match x with
      | .declareTypeFormer T' => T == T'
      | _                     => false
  | .declareCompRule e c =>
      match x with
      | .declareEliminator e' _ => e == e'
      | .declareConstructor c' _ => c == c'
      | _ => false
  | .declareTerm nm T =>
      match x with
      | .declareTypeFormer T' => T == T'
      | .declareConstructor c' _ =>
          match ctorNameOfNeighborhood? nm with
          | some c => c == c'
          | none   => false
      | .declareInfrastructure _ => false
      | _ => false

@[inline] def dependsOnTargets (y : Target) (xs : List Target) : Bool :=
  xs.any (declDependsOn y)

/-- Deduplicate frontier entries by `FrontierKey` (keep the first representative). -/
def dedupFrontierByKey (es : List FrontierEntry) : List FrontierEntry :=
  es.foldl
    (fun acc e =>
      let k := keyOfTarget e.target
      if acc.any (fun e' => keyOfTarget e'.target == k) then acc else acc ++ [e])
    []


/-- Configuration for frontier enumeration. -/
structure ScopeConfig where
  actions      : List AtomicDecl
  enumerators  : List FrontierEnumerator := []  -- additional context-sensitive proposals
  horizon      : Nat
  preMaxDepth? : Option Nat := none             -- same-budget κ_pre truncation
  postMaxDepth?: Option Nat := none             -- defaults to horizon if unspecified
  exclude      : List AtomicDecl := []
  excludeKeys  : List FrontierKey := []           -- schema-key excludes (new)
deriving Inhabited

-- Custom pretty-printer that avoids printing function values
instance : Repr ScopeConfig where
  reprPrec sc _ :=
    s!"ScopeConfig(actions := {sc.actions.length}, enumerators := {sc.enumerators.length}, horizon := {sc.horizon}, preMaxDepth? := {sc.preMaxDepth?}, postMaxDepth? := {sc.postMaxDepth?}, exclude := {sc.exclude.length}, excludeKeys := {sc.excludeKeys.length})"

@[inline] def preMaxDepth (cfg : ScopeConfig) : Nat :=
  cfg.preMaxDepth?.getD cfg.horizon

@[inline] def postMaxDepth (cfg : ScopeConfig) : Nat :=
  cfg.postMaxDepth?.getD cfg.horizon

/-! ## Small list helpers (BEq-based dedup/filter) -/

@[inline] def memBEq [BEq α] (x : α) (xs : List α) : Bool :=
  xs.any (· == x)

@[inline] def dedupBEq [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if memBEq x acc then acc else acc ++ [x]) ([])

@[inline] def filterNotIn [BEq α] (xs bad : List α) : List α :=
  xs.filter (fun x => not (memBEq x bad))

/-! ## Built-in generic enumerators (bind-free) -/

/-- Propose eliminators `rec_T : T` for any declared type former `T` lacking an eliminator. -/
def enumMissingEliminators (recPrefix : String := "rec_") : FrontierEnumerator :=
  fun Γ =>
    let ts := Γ.typeFormers
    ts.filter (fun T => not (Γ.hasEliminatorFor T))
      |>.map (fun T => AtomicDecl.declareEliminator s!"{recPrefix}{T}" T)

/-- Propose comp rules tying each eliminator to each constructor of the same type if missing. -/
def enumMissingCompRules : FrontierEnumerator :=
  fun Γ =>
    let elims := Γ.eliminators
    let ctors := Γ.constructors
    -- For each constructor (cName, tName), collect comp rules for every eliminator on tName
    let candidates :=
      ctors.foldl
        (fun acc (cName, tName) =>
          let forCtor :=
            elims.foldl
              (fun acc2 (eName, tName') =>
                if tName' == tName then
                  let d := AtomicDecl.declareCompRule eName cName
                  if Γ.hasCompRule eName cName then acc2 else acc2 ++ [d]
                else acc2)
              []
          acc ++ forCtor)
        []
    dedupBEq candidates

/-- Lift a fixed list of targets to an enumerator (ignores the context). -/
@[inline] def staticEnumerator (ts : List Target) : FrontierEnumerator :=
  fun _ => ts


/-! ## Frontier construction -/

@[inline] def holdsDecl (Γ : Context) : AtomicDecl → Bool
  | .declareUniverse ℓ       => Γ.hasUniverse ℓ
  | .declareInfrastructure n => Γ.hasInfrastructure n
  | .declareTypeFormer n     => Γ.hasTypeFormer n
  | .declareConstructor c _  => Γ.hasConstructor c
  | .declareEliminator  e _  => Γ.hasEliminator e
  | .declareCompRule e c     => Γ.hasCompRule e c
  | .declareTerm t _         => Γ.hasTerm t

/--
Layered post-closure up to depth `H` (BFS *without* in-layer cascading).

Starting from `post`, at layer 1 we add **all** actions valid in `post`;
at layer 2 we add all actions valid in the context from layer 1; etc.
We record `(target, distance)` for everything that becomes valid at that layer.

This matches Defs 6–7 (post distance = BFS layer index).
-/
def postDistances (post : Context) (actions : List AtomicDecl) (H : Nat)
    : List (AtomicDecl × Nat) :=
  let rec go (fuel : Nat) (depth : Nat) (cur : Context)
      (acc : List (AtomicDecl × Nat)) : List (AtomicDecl × Nat) :=
    match fuel with
    | 0 => acc
    | Nat.succ fuel' =>
      let addables :=
        actions.filter (fun a => isValidInContext a cur && not (holdsDecl cur a))
      if addables.isEmpty then
        acc
      else
        let acc' := acc ++ addables.map (fun a => (a, depth))
        let next := addables.foldl (fun Γ a => (step Γ a).getD Γ) cur
        go fuel' (depth + 1) next acc'
  go H 1 post []

@[inline] def kappaTrunc (actions : List AtomicDecl) (Γ : Context) (Y : AtomicDecl) (budget : Nat) : Nat :=
  match kappaMinForDecl? Γ Y actions budget with
  | some (k, _) => k
  | none        => budget + 1

/-- Gather, exclude, and deduplicate raw targets from the post context. -/
def gatherTargets (post : Context) (cfg : ScopeConfig) : List Target :=
  let fromActions      := cfg.actions
  let fromEnumerators  : List Target :=
    cfg.enumerators.foldl (fun acc en => acc ++ en post) []
  let combined         := dedupBEq (fromActions ++ fromEnumerators)
  let excluded         := dedupBEq cfg.exclude
  filterNotIn combined excluded

/--
  Build the horizon-bounded frontier:
   * keep only targets whose BFS post distance ≤ H,
   * compute truncated pre-cost κ̃(Y|pre) where failures count as H+1.
-/
def frontier (pre post : Context) (cfg : ScopeConfig) : List FrontierEntry :=
  let _H        := cfg.horizon
  let postBound := postMaxDepth cfg
  let preBound  := preMaxDepth cfg
  let ts        := gatherTargets post cfg

  -- Stage 2: BFS post distances (no in-layer cascading)
  let dists : List (Target × Nat) := postDistances post cfg.actions postBound
  let kPostOf (t : Target) : Option Nat :=
    (dists.find? (fun p => p.fst == t)).map (·.snd)

  let raw : List FrontierEntry :=
    ts.foldl
      (fun acc t =>
        match kPostOf t with
        | some kPost =>
            let kPreEff := kappaTrunc cfg.actions pre t preBound
            acc ++ [{ target := t, kPost := kPost, kPreEff := kPreEff }]
        | none => acc)
      []
  -- Frontier membership is determined solely by post-distance and pre-cost rules;
  -- no additional syntactic dependency gate.
  let raw' := raw.filter (fun e => not (hasKey cfg.excludeKeys e.target))
  -- schema collapse (your Axiom‑3 keying)
  dedupFrontierByKey raw'



/-! ## Convenience: novelty contribution from a frontier entry -/
@[inline] def contribBounded (H : Nat) (e : FrontierEntry) : Nat :=
  let kpre := Nat.min e.kPreEff H
  if kpre > e.kPost then kpre - e.kPost else 0

@[inline] def contribWithCap (cap : Nat) (e : FrontierEntry) : Nat :=
  let kpre := Nat.min e.kPreEff cap
  if kpre > e.kPost then kpre - e.kPost else 0

@[inline] def contrib01 (e : FrontierEntry) : Nat :=
  if e.kPreEff > e.kPost then 1 else 0

@[inline] def sumContrib01 (es : List FrontierEntry) : Nat :=
  es.foldl (fun s e => s + contrib01 e) 0

@[inline] def sumContribWithCaps (post : Context) (es : List FrontierEntry) : Nat :=
  es.foldl (fun s e =>
    let k := keyOfTarget e.target
    s + contribWithCap (capForKeyWithPost post k) e) 0

/-- Simple labels for atoms (for discovered X names). -/
def atomLabel : PEN.CAD.AtomicDecl → String
  | .declareUniverse ℓ      => s!"U{ℓ}:U"
  | .declareInfrastructure i  => s!"INFRA {i}"
  | .declareTypeFormer n    => s!"type {n}"
  | .declareConstructor c _ => c
  | .declareEliminator e _  => e
  | .declareCompRule e c    => s!"{e}∘{c}"
  | .declareTerm t _        => t

/-
  ========= Diagnostics for novelty frontier =========
  A structured audit of the frontier construction pipeline:
    enumerate → exclude-by-name → BFS post-distance gate → exclude-by-key → dedup-by-key
-/

namespace Debug

open PEN.CAD

/-- What got dropped by key-level dedup: which key, which entry kept, which dropped. -/
structure DedupDrop where
  key     : FrontierKey
  kept    : FrontierEntry
  dropped : FrontierEntry
deriving Repr

/-- Rollup of the entire frontier-building pipeline for debugging. -/
structure FrontierDiag where
  H              : Nat
  postBound      : Nat
  preBound       : Nat
  enumerated     : List (Target × FrontierKey)                 -- all from enumerators (dedup by decl)
  excludedByName : List (Target × FrontierKey)                 -- removed by cfg.exclude
  postKappaOK    : List (Target × FrontierKey × Nat)           -- post distance found (layer ≤ postBound)
  postKappaFail  : List (Target × FrontierKey)                 -- not reachable within postBound layers
  rawEntries     : List FrontierEntry                          -- after post-distance gate, before excludes-by-key
  excludedByKey  : List (Target × FrontierKey)                 -- removed by cfg.excludeKeys
  dedupDrops     : List DedupDrop                              -- removed by schema-key dedup
  finalEntries   : List FrontierEntry                          -- survivors entering novelty sum
  contributions  : List (Target × FrontierKey × Nat)           -- Δ(Y) per survivor
  nuSum          : Nat                                         -- Σ Δ(Y)
deriving Repr

/-- Pretty name for a frontier key. -/
def ppKey : FrontierKey → String
  | .universe ℓ        => s!"U{ℓ}"
  | .typeFormer        => "TF"
  | .ctor T            => s!"ctor({T})"
  | .elim T            => s!"elim({T})"
  | .compElim e        => s!"comp({e})"
  | .term T            => s!"term({T})"
  | .termExact T nm    => s!"term[{T}]::{nm}"
  | .exact t           => s!"exact({PEN.Novelty.Scope.atomLabel t})"

/-- Keyed dedup with record of which entries were dropped by an existing key. -/
def dedupFrontierByKeyWithDrops (es : List FrontierEntry)
  : List FrontierEntry × List DedupDrop :=
  es.foldl
    (fun (acc, drops) e =>
      let k := PEN.Novelty.Scope.keyOfTarget e.target
      match acc.find? (fun e' => PEN.Novelty.Scope.keyOfTarget e'.target == k) with
      | some keep =>
          (acc, drops ++ [⟨k, keep, e⟩])
      | none =>
          (acc ++ [e], drops))
    ([], [])

/--
  Full audit version of `frontier`:
    returns the *same* final entries as `frontier`, plus a structured diagnostic.
-/
def frontierWithDiag (pre post : Context) (cfg : ScopeConfig)
  : List FrontierEntry × FrontierDiag :=
  let _H        := cfg.horizon
  let postBound := postMaxDepth cfg
  let preBound  := preMaxDepth cfg

  -- Stage 1: enumerate targets (actions + enumerators, with name-based excludes recorded)
  let fromActions := cfg.actions
  let fromEnums   : List Target :=
    cfg.enumerators.foldl (fun acc en => acc ++ en post) []
  let allEnum : List Target := dedupBEq (fromActions ++ fromEnums)
  let enumerated : List (Target × FrontierKey) :=
    allEnum.map (fun t => (t, keyOfTarget t))
  let excludedByName : List (Target × FrontierKey) :=
    allEnum.filter (fun t => memBEq t cfg.exclude)
           |>.map (fun t => (t, keyOfTarget t))
  let ts : List Target := filterNotIn allEnum (dedupBEq cfg.exclude)

  let dists : List (Target × Nat) := postDistances post cfg.actions postBound
  let kPostOf (t : Target) : Option Nat :=
    (dists.find? (fun p => p.fst == t)).map (·.snd)

  let postKappaOK : List (Target × FrontierKey × Nat) :=
    ts.foldl (fun acc t =>
      match kPostOf t with
      | some k => acc ++ [(t, keyOfTarget t, k)]
      | none   => acc) []

  let postKappaFail : List (Target × FrontierKey) :=
    ts.filter (fun t => (kPostOf t).isNone)
      |>.map (fun t => (t, keyOfTarget t))

  -- Stage 3: compute pre effort for successes; build raw entries
  let rawEntries : List FrontierEntry :=
    postKappaOK.map (fun (t, _k, kPost) =>
      let kPreEff := kappaTrunc cfg.actions pre t preBound
      { target := t, kPost := kPost, kPreEff := kPreEff })

  -- Stage 4: exclude by schema keys
  let excludedByKey : List (Target × FrontierKey) :=
    rawEntries.filter (fun e => hasKey cfg.excludeKeys e.target)
              |>.map (fun e => (e.target, keyOfTarget e.target))
  let raw' : List FrontierEntry :=
    rawEntries.filter (fun e => not (hasKey cfg.excludeKeys e.target))

  -- Stage 5: schema-key dedup
  let (finalEntries, dedupDrops) := dedupFrontierByKeyWithDrops raw'

  -- Stage 6: contributions + ν
  let contributions : List (Target × FrontierKey × Nat) :=
    finalEntries.map (fun e =>
      let k := keyOfTarget e.target
      let d := contrib01 e
      (e.target, k, d))
  let nuSum : Nat := contributions.foldl (fun s (_,_,d) => s + d) 0

  let diag : FrontierDiag :=
    { H := cfg.horizon, postBound, preBound
      , enumerated, excludedByName, postKappaOK, postKappaFail
      , rawEntries, excludedByKey, dedupDrops, finalEntries, contributions, nuSum }

  (finalEntries, diag)

/-- Compact human-readable dump of the diagnostic (easy to `dbg_trace`). -/
def render (d : FrontierDiag) : String :=
  let header :=
    s!"[frontier] H={d.H} preBound={d.preBound} postBound={d.postBound}\n"
    ++ s!"  enumerated={d.enumerated.length}  excludedByName={d.excludedByName.length}\n"
    ++ s!"  postOK={d.postKappaOK.length}  postFail={d.postKappaFail.length}\n"
    ++ s!"  afterKeyExclude={d.rawEntries.length - d.excludedByKey.length}\n"
    ++ s!"  dedupDrops={d.dedupDrops.length}  survivors={d.finalEntries.length}\n"
    ++ s!"  ν={d.nuSum}\n"
  let showPair : Target × FrontierKey → String :=
    fun (t, k) => s!"    {PEN.Novelty.Scope.atomLabel t}  ::  {ppKey k}\n"
  let showTriple : Target × FrontierKey × Nat → String :=
    fun (t, k, n) => s!"    {PEN.Novelty.Scope.atomLabel t}  ::  {ppKey k}  = {n}\n"
  let showEntry : FrontierEntry → String :=
    fun e => s!"    {PEN.Novelty.Scope.atomLabel e.target}  ::  {ppKey (keyOfTarget e.target)}  kpost={e.kPost}  kpre~={e.kPreEff}\n"
  let showDrop : DedupDrop → String :=
    fun x => s!"    DROP {ppKey x.key}: {PEN.Novelty.Scope.atomLabel x.dropped.target} (kept {PEN.Novelty.Scope.atomLabel x.kept.target})\n"

  let sec (ttl : String) (body : String) :=
    if body.isEmpty then "" else s!"\n{ttl}\n{body}"

  header
  ++ sec "• Excluded by name:" (String.join (d.excludedByName.map showPair))
  ++ sec "• post distance FAIL:" (String.join (d.postKappaFail.map showPair))
  ++ sec "• After post distance:" (String.join (d.rawEntries.map showEntry))
  ++ sec "• Excluded by key:"  (String.join (d.excludedByKey.map showPair))
  ++ sec "• Dedup drops:"      (String.join (d.dedupDrops.map showDrop))
  ++ sec "• Survivors (Δ per key):"
       (String.join (d.contributions.map showTriple))

end Debug


/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl
open PEN.Grammar.HIT

def Γ0 : Context := Context.empty
def Γu : Context := (step Γ0 (.declareUniverse 0)).getD Γ0

-- Build a HIT (S1) *without* eliminator/comp rules to create a meaningful frontier.
def s1_noRec : HITSpec := { (specS1 "S1") with withEliminator := false, withCompRules := false }
def Γpost? : Option Context := installHIT? Γu s1_noRec none

-- Actions menu: everything needed to later install the missing elim + comp rules as well.
def actionsS1Full : List AtomicDecl :=
  actionsForHIT (specS1 "S1") (some 0)

-- Scope config: horizon 3, enumerators propose the *missing* bits.
def cfg : ScopeConfig :=
  { actions      := actionsS1Full
  , enumerators  := [enumMissingEliminators, enumMissingCompRules]
  , horizon      := 3
  , preMaxDepth? := none
  , exclude      := [] }

-- Show how many (target, post, pre) triples we get (returns Nat):
#eval match Γpost? with
     | none      => 0
     | some Γpost =>
         let es : List FrontierEntry := frontier Γu Γpost cfg
         -- If you just want the count, you could also do: es.length
         let triples := es.map (fun (e : FrontierEntry) => (e.target, e.kPost, e.kPreEff))
         triples.length

-- Sum of novelty contributions (returns Nat):
#eval match Γpost? with
     | none      => 0
     | some Γpost =>
         let es : List FrontierEntry := frontier Γu Γpost cfg
         sumContribWithCaps Γpost es

#eval match Γpost? with
     | none      => ([] : List (Target × Nat × Nat))   -- keep branch types aligned
     | some Γpost =>
         let es : List FrontierEntry := frontier Γu Γpost cfg
         es.map (fun (e : FrontierEntry) => (e.target, e.kPost, e.kPreEff))

--/

end PEN.Novelty.Scope
