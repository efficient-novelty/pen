/-
  PEN/Novelty/Novelty.lean

  Algorithmic novelty via bounded search (IDDFS) over an action alphabet.

  For a package (targets X), we:
    * find κ(X | B) and post context by IDDFS over actions
    * compute the frontier automatically from actions (ignoring enumerators):
        frontier := { Y ∈ actions \ exclude | κ(Y | post) ≤ H }
      and novelty ν := Σ_Y max(0, κ_H(Y | B) - κ(Y | post)),
      where κ_H truncates pre to the same budget H (or preMaxDepth? if provided).

  This file exposes:
    - NoveltyReport (unchanged)
    - noveltyForPackage? : the engine calls this; enumerators are ignored
-/

import Init
import PEN.CAD.Atoms
import PEN.Novelty.Scope
import PEN.CAD.Kappa

namespace PEN.Novelty.Novelty

open PEN.CAD
open PEN.Novelty.Scope
open AtomicDecl

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
  + Γ.typeFormers.length
  + Γ.constructors.length
  + Γ.eliminators.length
  + Γ.compRules.length
  + Γ.terms.length

/-- Does a declaration already "hold" in the context? -/
@[inline] def holds (Γ : Context) : AtomicDecl → Bool
  | .declareUniverse ℓ      => Γ.hasUniverse ℓ
  | .declareTypeFormer n    => Γ.hasTypeFormer n
  | .declareConstructor c T => Γ.hasConstructor c
  | .declareEliminator e T  => Γ.hasEliminator e
  | .declareCompRule e c    => Γ.hasCompRule e c
  | .declareTerm n T        => Γ.hasTerm n

/-- Goal predicate: all targets hold. -/
@[inline] def goalAll (targets : List AtomicDecl) (Γ : Context) : Bool :=
  targets.all (fun t => holds Γ t)

@[inline] def namesOfNewTypeFormers (ts : List AtomicDecl) : List String :=
  ts.foldl (fun acc a =>
    match a with
    | AtomicDecl.declareTypeFormer n =>
        if acc.any (· == n) then acc else acc ++ [n]
    | _ => acc) []

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
  let acts   := dedupBEq actions
  let cands  := acts.filter (fun y => not (exclude.any (· == y)))
  -- Collect raw entries first …
  let raw : List FrontierEntry :=
    cands.foldl
      (fun acc Y =>
        -- κ_post(Y) within the *post* budget (immediate frontier if postBudget = 1)
        match iddfsMin actions (PEN.CAD.goalOfDecl Y) postBudget post with
        | none => acc
        | some (kPost, _) =>
          if h : kPost = 0 then
            acc
          else
            let kPreEff := kappaTrunc actions B Y preBudget
            acc ++ [{ target := Y, kPreEff := kPreEff, kPost := kPost }])
      []
  -- … then collapse schema-equivalent targets (all type formers → 1 class).
  dedupFrontierByKey raw



/-! ############################
      Key-aware frontier
############################# -/

@[inline] def gainWithCaps (post : Context) (e : FrontierEntry) : Nat :=
  let k := keyOfTarget e.target
  contribWithCap (capForKeyWithPost post k) e

/-- Reduce entries to one per key, keeping maximal novelty gain; ties by minimal kPost. -/
def reduceByKeyMaxGain (post : Context) (es : List FrontierEntry) : List FrontierEntry :=
  let rec upsert (kNew : FrontierKey) (eNew : FrontierEntry)
      (acc : List (FrontierKey × FrontierEntry)) : List (FrontierKey × FrontierEntry) :=
    match acc with
    | [] => [(kNew, eNew)]
    | (kOld, eOld) :: rest =>
        if kOld == kNew then
          let eBest :=
            if gainWithCaps post eNew > gainWithCaps post eOld then eNew
            else if gainWithCaps post eNew == gainWithCaps post eOld && eNew.kPost < eOld.kPost then eNew
            else eOld
          (kOld, eBest) :: rest
        else
          (kOld, eOld) :: upsert kNew eNew rest
  let table := es.foldl (fun acc e => upsert (keyOfTarget e.target) e acc) []
  table.map (fun p => p.snd)

def frontierAllScoped (B post : Context) (sc : ScopeConfig) : List FrontierEntry :=
  let H          := sc.horizon
  let preBudget  := sc.preMaxDepth?.getD H
  let postBudget := sc.postMaxDepth?.getD H
  let acts       := dedupBEq sc.actions
  let cands      := acts.filter (fun y => (not (memBEq y sc.exclude)) && (not (hasKey sc.excludeKeys y)))
  let raw : List FrontierEntry :=
    cands.foldl
      (fun acc Y =>
        match PEN.CAD.kappaMinForDecl? post Y sc.actions postBudget with
        | none => acc
        | some (kPost, _) =>
          -- Skip anything already true in post: not "future frontier".
          if kPost = 0 then acc else
            -- Honest pre-cost: truncated κ from B (fail ⇒ preBudget+1 inside kappaTrunc).
            let kPreEff := kappaTrunc sc.actions B Y preBudget
            acc ++ [{ target := Y, kPreEff := kPreEff, kPost := kPost }])
      []
  let rawFiltered :=
    if sc.exclude.isEmpty then raw
    else raw.filter (fun e => dependsOnTargets e.target sc.exclude)
  reduceByKeyMaxGain post rawFiltered



def noveltyFromFrontier (post : Context) (es : List FrontierEntry) : Nat :=
  sumContribWithCaps post es

/-! ############################
     Package evaluation (X)
############################# -/

/-- Compute novelty report for a package X (targets) under scope config. -/
def noveltyForPackage?
    (B : Context)
    (targets : List AtomicDecl)
    (sc : ScopeConfig)
    (maxDepthX : Nat := sc.horizon) : Option NoveltyReport :=

  let goal := goalAll targets
  match iddfsMin sc.actions goal maxDepthX B with
  | none => none
  | some (kX, post) =>
    let es := frontierAllScoped B post sc
    let nuCore := PEN.Novelty.Scope.sumContribWithCaps post es

    -- Axiom 3′: add +1 for each freshly introduced NON-classifier TF in X
    let freshTFs   := namesOfNewTypeFormers targets
    let freshNonCl := freshTFs.filter (fun T => not (PEN.Novelty.Scope.isClassifierTFName T))
    let tfBonus := freshNonCl.length
    let ν := nuCore + tfBonus
    let ρ := if kX = 0 then 0.0 else (Float.ofNat ν) / (Float.ofNat kX)
    some { post := post, kX := kX, frontier := es, nuCore := nuCore, tfBonus := tfBonus, nu := ν, rho := ρ }

end PEN.Novelty.Novelty
