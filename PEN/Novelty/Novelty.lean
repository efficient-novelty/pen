/-
  PEN/Novelty/Novelty.lean

  Algorithmic novelty via bounded search (IDDFS) over an action alphabet.

  For a package (targets X), we:
    * find κ(X | B) and post context by IDDFS over actions
    * compute the frontier automatically from actions ∪ enumerators:
        frontier := { Y proposed | κ(Y | post) ≤ H }
      and novelty ν := Σ_Y max(0, κ_H(Y | B) - κ(Y | post)),
      where κ_H truncates pre to the same budget H (or preMaxDepth? if provided).

  This file exposes:
    - NoveltyReport (unchanged)
    - noveltyForPackage? : the engine calls this; enumerators are honored
-/

import Init
import PEN.CAD.Atoms
import PEN.Novelty.Scope
import PEN.CAD.Kappa
import PEN.Select.Discover

namespace PEN.Novelty.Novelty

open PEN.CAD
open PEN.Novelty.Scope
-- Avoid opening Discover to prevent clashes with helper names like `dedupBEq`.
open AtomicDecl

/-- Interface basis from the last two layers, newest first in `layers`. -/
def interfaceBasis (layers : List (List Target)) : List Target :=
  let flat :=
    match layers with
    | xs :: ys :: _ => xs ++ ys
    | xs :: _       => xs
    | []            => []
  PEN.Novelty.Scope.dedupBEq flat


/-- Interaction profile J(X,B): filters Iₙ by applicability to X (syntactic dependency proxy). -/
def interactionProfile (I : List Target) (targetsX : List AtomicDecl) : List Target :=
  I.filter (fun ϕ => dependsOnTargets ϕ targetsX)

/-- What we report back to the engine after evaluating a package X. -/
structure NoveltyReport where
  post     : Context
  kX       : Nat
  frontier : List FrontierEntry
  nuCore   : Nat
  tfBonus  : Nat
  nu       : Nat
  rho      : Float
deriving Repr

/-! ############################
      Basic helpers
############################# -/

/-- Size of a context (strictly increases when we add a genuinely new item). -/
@[inline] def ctxSize (Γ : Context) : Nat :=
  Γ.universes.length
  + Γ.infrastructure.length
  + Γ.typeFormers.length
  + Γ.constructors.length
  + Γ.eliminators.length
  + Γ.compRules.length
  + Γ.terms.length

/-- Does a declaration already "hold" in the context? -/
@[inline] def holds (Γ : Context) : AtomicDecl → Bool
  | .declareUniverse ℓ      => Γ.hasUniverse ℓ
  | .declareInfrastructure n => Γ.hasInfrastructure n
  | .declareTypeFormer n    => Γ.hasTypeFormer n
  | .declareConstructor c _ => Γ.hasConstructor c
  | .declareEliminator e _  => Γ.hasEliminator e
  | .declareCompRule e c    => Γ.hasCompRule e c
  | .declareTerm n _        => Γ.hasTerm n

/-- Goal predicate: all targets hold. -/
@[inline] def goalAll (targets : List AtomicDecl) (Γ : Context) : Bool :=
  targets.all (fun t => holds Γ t)

@[inline] def namesOfNewTypeFormers (ts : List AtomicDecl) : List String :=
  ts.foldl (fun acc a =>
    match a with
    | AtomicDecl.declareTypeFormer n =>
        if acc.any (· == n) then acc else acc ++ [n]
    | _ => acc) []

@[inline] def containsTF (nm : String) (ts : List AtomicDecl) : Bool :=
  ts.any (fun a => match a with
                   | .declareTypeFormer n => n == nm
                   | _ => false)

@[inline] def isPiSigmaDual (ts : List AtomicDecl) : Bool :=
  containsTF "Pi" ts && containsTF "Sigma" ts

@[inline] def liftForSealedDual (targets : List AtomicDecl) : Nat :=
  -- Π/Σ dual package: need +2 raw moves vs the sealed κ (see proof)
  if isPiSigmaDual targets then 2 else 0

@[inline] def commonHost? (ts : List AtomicDecl) : Option String :=
  let hosts :=
    ts.foldl (fun acc a =>
      match PEN.Select.Discover.hostOf a with
      | some h => if acc.any (· == h) then acc else acc ++ [h]
      | none   => acc) []
  match hosts with
  | [h] => some h
  | _   => none

@[inline] def sealedNonClassifierHost? (targets : List AtomicDecl) : Option String :=
  match commonHost? targets with
  | some h =>
      if not (PEN.Novelty.Scope.isClassifierTFName h)
         && PEN.Select.Discover.isFullForHost targets h
      then some h else none
  | none => none

/-! ############################
    Bounded search (IDDFS)
############################# -/

/-- One bounded DFS step: try to reach a goal within `bound`. Returns (cost, post). -/
partial def dfsLimited
    (actions : List AtomicDecl)
    (goal : Context → Bool)
    (bound : Nat)
    (Γ : Context) : Option (Nat × Context) :=
  if goal Γ then
    some (0, Γ)
  else if bound = 0 then
    none
  else
    let sz := ctxSize Γ
    -- try each action that makes progress
    let rec tryList (as : List AtomicDecl) : Option (Nat × Context) :=
      match as with
      | [] => none
      | a :: rest =>
        match step Γ a with
        | none      => tryList rest
        | some Γ'   =>
          if ctxSize Γ' ≤ sz then
            -- no progress; skip to avoid loops on idempotent adds
            tryList rest
          else
            match dfsLimited actions goal (bound - 1) Γ' with
            | some (k, Γ'') => some (k + 1, Γ'')
            | none          => tryList rest
    tryList actions

/-- Iterative deepening: minimal (cost, post) to satisfy `goal`, if any ≤ maxDepth.

We implement IDDFS via a structurally terminating inner loop on an explicit `fuel`
counter (at most `maxDepth+1` iterations). This avoids termination proofs. -/
def iddfsMin
    (actions : List AtomicDecl)
    (goal : Context → Bool)
    (maxDepth : Nat)
    (start : Context) : Option (Nat × Context) :=
  -- `go b fuel`: try bound `b`, then `b+1`, ... for at most `fuel` steps.
  let rec go (b fuel : Nat) : Option (Nat × Context) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if b > maxDepth then
        none
      else
        match dfsLimited actions goal b start with
        | some ans => some ans
        | none     => go (b + 1) fuel'
  go 0 (maxDepth + 1)

@[inline] def kappaTrunc (actions : List AtomicDecl) (Γ : Context) (Y : AtomicDecl) (budget : Nat) : Nat :=
  match PEN.CAD.kappaMinForDecl? Γ Y actions budget with
  | some (k, _) => k
  | none        => budget + 1

/-! ############################
        Frontier and ν
############################# -/

/-- Compute the whole post-frontier at budget H (algorithmic, no enumerators). -/
def frontierAll (actions : List AtomicDecl)
    (B post : Context)
    (H : Nat)
    (preMax? : Option Nat)
    (postMax? : Option Nat)          -- NEW
    (exclude : List AtomicDecl) : List FrontierEntry :=
  let preBudget  := preMax?.getD H
  let postBudget := postMax?.getD H   -- NEW
  let acts   := PEN.Novelty.Scope.dedupBEq actions
  let cands  := acts.filter (fun y => not (exclude.any (· == y)))
  let dists  := PEN.Novelty.Scope.postDistances post actions postBudget
  let kPostOf (t : AtomicDecl) : Option Nat :=
    (dists.find? (fun p => p.fst == t)).map (·.snd)
  let raw : List FrontierEntry :=
    cands.foldl
      (fun acc Y =>
        match kPostOf Y with
        | some kPost =>
            let kPreEff := kappaTrunc actions B Y preBudget
            acc ++ [{ target := Y, kPreEff := kPreEff, kPost := kPost }]
        | none => acc)
      []
  -- … then collapse schema-equivalent targets (all type formers → 1 class).
  dedupFrontierByKey raw



/-! ############################
      Key-aware frontier
############################# -/

@[inline] def gain01 (e : FrontierEntry) : Nat :=
  contrib01 e

/-- Reduce entries to one per key, keeping maximal novelty gain; ties by minimal kPost. -/
def reduceByKeyMaxGain (_post : Context) (es : List FrontierEntry) : List FrontierEntry :=
  let rec upsert (kNew : FrontierKey) (eNew : FrontierEntry)
      (acc : List (FrontierKey × FrontierEntry)) : List (FrontierKey × FrontierEntry) :=
    match acc with
    | [] => [(kNew, eNew)]
    | (kOld, eOld) :: rest =>
        if kOld == kNew then
          let eBest :=
            if gain01 eNew > gain01 eOld then eNew
            else if gain01 eNew == gain01 eOld && eNew.kPost < eOld.kPost then eNew
            else eOld
          (kOld, eBest) :: rest
        else
          (kOld, eOld) :: upsert kNew eNew rest
  let table := es.foldl (fun acc e => upsert (keyOfTarget e.target) e acc) []
  table.map (fun p => p.snd)

def frontierAllScoped (B post : Context) (sc : ScopeConfig) : List FrontierEntry :=
  let preBudget  := preMaxDepth sc
  let postBudget := postMaxDepth sc
  -- Flatten enumerators without List.join/List.bind
  let enumAdds : List AtomicDecl :=
    sc.enumerators.foldl (fun acc en => acc ++ en post) []
  let allTargets := PEN.Novelty.Scope.dedupBEq (sc.actions ++ enumAdds)
  let excluded   := PEN.Novelty.Scope.dedupBEq sc.exclude
  let baseCands  := allTargets.filter (fun y =>
    (not (PEN.Novelty.Scope.memBEq y excluded))
    && (not (hasKey sc.excludeKeys y)))
  let cands      :=
    if sc.exclude.isEmpty then
      baseCands
    else
      baseCands.filter (fun y => dependsOnTargets y sc.exclude)
  let dists      := PEN.Novelty.Scope.postDistances post sc.actions postBudget
  let kPostOf (t : AtomicDecl) : Option Nat :=
    (dists.find? (fun p => p.fst == t)).map (·.snd)
  let raw : List FrontierEntry :=
    cands.foldl
      (fun acc Y =>
        match kPostOf Y with
        | some kPost =>
            let kPreEff := kappaTrunc sc.actions B Y preBudget
            acc ++ [{ target := Y, kPreEff := kPreEff, kPost := kPost }]
        | none => acc)
      []
  reduceByKeyMaxGain post raw



def noveltyFromFrontier (_post : Context) (es : List FrontierEntry) : Nat :=
  sumContrib01 es

/-! ############################
     Package evaluation (X)
############################# -/

/-- Compute novelty report for a package X (targets) under scope config. -/
def noveltyForPackage?
    (B : Context)
    (targets : List AtomicDecl)
    (sc : ScopeConfig)
    (I  : List Target)
    (maxDepthX : Nat := sc.horizon) : Option NoveltyReport :=

  let goal := goalAll targets
  -- NEW: lift raw search budget for sealed Π/Σ
  let rawBound := maxDepthX + liftForSealedDual targets
  match iddfsMin sc.actions goal rawBound B with
  | none => none
  | some (kDeriv, post) =>
    let es := frontierAllScoped B post sc
    let nuCore := PEN.Novelty.Scope.sumContrib01 es
    let J := interactionProfile I targets
    -- charge interface wiring only when evaluating pure TF bundles
    let kX :=
      if PEN.Novelty.Scope.allTFOnly targets then
        kDeriv + J.length
      else
        kDeriv
    let uniBonus := if PEN.Novelty.Scope.allUniversesOnlyTargets targets then 1 else 0
    let tfBonus := uniBonus
    let ν := nuCore + tfBonus
    let ρ := if kX = 0 then 0.0 else (Float.ofNat ν) / (Float.ofNat kX)
    some { post := post
         , kX := kX
         , frontier := es
         , nuCore := nuCore
         , tfBonus := tfBonus
         , nu := ν
         , rho := ρ }

end PEN.Novelty.Novelty
