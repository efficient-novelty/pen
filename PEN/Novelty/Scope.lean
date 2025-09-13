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
  | AtomicDecl.declareTypeFormer _    => FrontierKey.typeFormer
  | AtomicDecl.declareConstructor _ T => FrontierKey.ctor T
  | AtomicDecl.declareEliminator _ T  => FrontierKey.elim T
  | AtomicDecl.declareCompRule e c =>
      -- count each comp rule separately
      FrontierKey.exact t

  | AtomicDecl.declareTerm nm T =>
      if isClassifierTFName T && isSchemaNameFor nm T then
        -- classifier schemas are endogenous to the TF
        FrontierKey.typeFormer
      else if isPiSigmaAlias nm T then
        -- Π/Σ aliases must never collapse: keep them distinct
        FrontierKey.termExact T nm
      else if isCtorNeighborhoodTerm nm then
        -- hi-dim constructor neighborhoods are distinct targets
        FrontierKey.termExact T nm
      else if isSchemaNameFor nm T then
        -- non-classifier schema_* terms are exact (e.g. schema_S2)
        FrontierKey.termExact T nm
      else if isClassifierTFName T then
        -- external classifier-hosted terms are distinct
        FrontierKey.termExact T nm
      else
        -- everything else attached to a host can be coarse
        FrontierKey.term T

@[inline] def keysOfTargets (ts : List Target) : List FrontierKey :=
  let rec add (acc : List FrontierKey) (k : FrontierKey) : List FrontierKey :=
    if acc.any (· == k) then acc else acc ++ [k]
  ts.foldl (fun acc t => add acc (keyOfTarget t)) []

@[inline] def hasKey (ks : List FrontierKey) (t : Target) : Bool :=
  ks.any (· == keyOfTarget t)

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
  enumerators  : List FrontierEnumerator := []  -- kept for API stability, unused now
  horizon      : Nat
  preMaxDepth? : Option Nat := none             -- same-budget κ_pre truncation
  postMaxDepth?: Option Nat := some 1             -- Axiom 3
  exclude      : List AtomicDecl := []
  excludeKeys  : List FrontierKey := []           -- schema-key excludes (new)
deriving Inhabited

-- Custom pretty-printer that avoids printing function values
instance : Repr ScopeConfig where
  reprPrec sc _ :=
    s!"ScopeConfig(actions := {sc.actions.length}, enumerators := {sc.enumerators.length}, horizon := {sc.horizon}, preMaxDepth? := {sc.preMaxDepth?}, postMaxDepth? := {sc.postMaxDepth?}, exclude := {sc.exclude.length}, excludeKeys := {sc.excludeKeys.length})"

@[inline] def preMaxDepth (cfg : ScopeConfig) : Nat :=
  cfg.preMaxDepth?.getD (cfg.horizon + 1)

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

/-- Union a list of enumerators into one (bind-free). -/
def unionEnumerators (es : List FrontierEnumerator) : FrontierEnumerator :=
  fun Γ =>
    let all := es.foldl (fun acc e => acc ++ e Γ) []
    dedupBEq all

/-! ## Frontier construction -/

@[inline] def kappaTrunc (actions : List AtomicDecl) (Γ : Context) (Y : AtomicDecl) (budget : Nat) : Nat :=
  match kappaMinForDecl? Γ Y actions budget with
  | some (k, _) => k
  | none        => budget + 1

/-- Gather, exclude, and deduplicate raw targets from the post context. -/
def gatherTargets (post : Context) (cfg : ScopeConfig) : List Target :=
  let all := (unionEnumerators cfg.enumerators) post
  filterNotIn (dedupBEq all) (dedupBEq cfg.exclude)

/--
  Build the horizon-bounded frontier:
   * keep only targets with κ(Y|post) ≤ H,
   * compute truncated pre-cost κ̃(Y|pre) where failures count as H+1.
-/
def frontier (pre post : Context) (cfg : ScopeConfig) : List FrontierEntry :=
  let H := cfg.horizon
  let postBound := cfg.postMaxDepth?.getD 1
  let preBound := preMaxDepth cfg
  let ts := gatherTargets post cfg

  -- NEW: fast path for term targets that are explicitly one-step actions
  let goTarget (t : Target) : Option FrontierEntry :=
    match t with
    | AtomicDecl.declareTerm _ _ =>
        if memBEq t cfg.actions then
          -- one step in post by construction; pre still uses truncated solver
          let kPreEff := kappaTrunc cfg.actions pre t preBound
          some { target := t, kPost := 1, kPreEff := kPreEff }
        else
          match kappaMinForDecl? post t cfg.actions postBound with
          | some (kPost, _) =>
              let kPreEff := kappaTrunc cfg.actions pre t preBound
              some { target := t, kPost := kPost, kPreEff := kPreEff }
          | none => none
    | _ =>
        match kappaMinForDecl? post t cfg.actions postBound with
        | some (kPost, _) =>
            let kPreEff := kappaTrunc cfg.actions pre t preBound
            some { target := t, kPost := kPost, kPreEff := kPreEff }
        | none => none

  let raw :=
    ts.foldl
      (fun acc t => match goTarget t with | some e => acc ++ [e] | none => acc)
      []

  let raw' := raw.filter (fun e => not (hasKey cfg.excludeKeys e.target))
  -- schema collapse (your Axiom‑3 keying)
  dedupFrontierByKey raw'



/-! ## Convenience: novelty contribution from a frontier entry -/
@[inline] def contribBounded (H : Nat) (e : FrontierEntry) : Nat :=
  let kpre := Nat.min e.kPreEff H
  if kpre > e.kPost then kpre - e.kPost else 0

/-- Simple labels for atoms (for discovered X names). -/
def atomLabel : PEN.CAD.AtomicDecl → String
  | .declareUniverse ℓ      => s!"U{ℓ}:U"         -- was "U0"
  | .declareTypeFormer n    => s!"type {n}"       -- was just `n`
  | .declareConstructor c _ => c
  | .declareEliminator e _  => e
  | .declareCompRule e c    => s!"{e}∘{c}"
  | .declareTerm t _        => t

/-
  ========= Diagnostics for novelty frontier =========
  A structured audit of the frontier construction pipeline:
    enumerate → exclude-by-name → κ(post) gate → exclude-by-key → dedup-by-key
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
  postKappaOK    : List (Target × FrontierKey × Nat)           -- κ_post found (k ≤ postBound)
  postKappaFail  : List (Target × FrontierKey)                 -- κ_post failed (search miss / > bound)
  rawEntries     : List FrontierEntry                          -- after κ_post, before excludes-by-key
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
  let H         := cfg.horizon
  let postBound := cfg.postMaxDepth?.getD 1
  let preBound  := preMaxDepth cfg

  -- Stage 1: enumerate targets (exactly as in `gatherTargets`, but keep the ones excluded by name)
  let allEnum : List Target := (unionEnumerators cfg.enumerators) post |> dedupBEq
  let enumerated : List (Target × FrontierKey) :=
    allEnum.map (fun t => (t, keyOfTarget t))
  let excludedByName : List (Target × FrontierKey) :=
    allEnum.filter (fun t => memBEq t cfg.exclude)
           |>.map (fun t => (t, keyOfTarget t))
  let ts : List Target := filterNotIn allEnum (dedupBEq cfg.exclude)

  -- Stage 2: κ(post) gate (identical to `frontier` except we record failures)
  let goPost (t : Target) : Option Nat :=
    match kappaMinForDecl? post t cfg.actions postBound with
    | some (kPost, _) => some kPost
    | none            => none

  let postKappaOK : List (Target × FrontierKey × Nat) :=
    ts.foldl (fun acc t =>
      match goPost t with
      | some k => acc ++ [(t, keyOfTarget t, k)]
      | none   => acc) []

  let postKappaFail : List (Target × FrontierKey) :=
    ts.filter (fun t => match goPost t with | some _ => false | none => true)
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
    finalEntries.map (fun e => (e.target, keyOfTarget e.target, contribBounded H e))
  let nuSum : Nat := contributions.foldl (fun s (_,_,d) => s + d) 0

  let diag : FrontierDiag :=
    { H, postBound, preBound
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
  ++ sec "• κ(post) FAIL:"     (String.join (d.postKappaFail.map showPair))
  ++ sec "• After κ(post):"    (String.join (d.rawEntries.map showEntry))
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
         sumContrib es

#eval match Γpost? with
     | none      => ([] : List (Target × Nat × Nat))   -- keep branch types aligned
     | some Γpost =>
         let es : List FrontierEntry := frontier Γu Γpost cfg
         es.map (fun (e : FrontierEntry) => (e.target, e.kPost, e.kPreEff))

--/

end PEN.Novelty.Scope
