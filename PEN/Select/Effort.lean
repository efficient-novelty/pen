/-
  PEN/Select/Effort.lean

  Effort (essential complexity) for a package X:
    ϵ(X) = (#intro rules) + (#essential eliminators) − coherenceDiscount
  Intro rules = type formers + constructors.
  Essential eliminators exclude contractible types (e.g. Unit).
  Coherence discount fires once per host when an eliminator is tied to
  at least one constructor via comp-rules; + an extra 1 for Π/Σ pairs.
-/

import Init
import PEN.CAD.Atoms

namespace PEN.Select.Effort

open PEN.CAD
open AtomicDecl

structure EffortBreakdown where
  introRules        : Nat
  essentialElims    : Nat
  coherenceDiscount : Nat
  total             : Nat
deriving Repr

/-- Minimal contractibility oracle (extend as you refine the library). -/
@[inline] def isContractibleTypeName (T : String) : Bool :=
  T == "Unit"

/-- Is this eliminator essential (i.e., not for a contractible type)? -/
@[inline] def isEssentialElim : AtomicDecl → Bool
  | .declareEliminator _ T => not (isContractibleTypeName T)
  | _                      => false

/-- Intro rules are type formers and constructors. -/
@[inline] def isIntro : AtomicDecl → Bool
  | .declareTypeFormer _    => true
  | .declareConstructor _ _ => true
  | _                       => false

private def elimHostPairs (ts : List AtomicDecl) : List (String × String) :=
  ts.foldl (fun acc a =>
    match a with
    | .declareEliminator e T =>
        if acc.any (fun p => p.fst == e && p.snd == T) then acc else acc ++ [(e, T)]
    | _ => acc) []

private def compElims (ts : List AtomicDecl) : List String :=
  ts.foldl (fun acc a =>
    match a with
    | .declareCompRule e _ => if acc.any (· == e) then acc else acc ++ [e]
    | _                    => acc) []

private def ctorHosts (ts : List AtomicDecl) : List String :=
  ts.foldl (fun acc a =>
    match a with
    | .declareConstructor _ T =>
        if acc.any (· == T) then acc else acc ++ [T]
    | _ => acc) []

/-- One coherence unit per host: elim for host present and at least
    one comp-rule tying that elim to some constructor of that host. -/
private def coherenceUnitsPerHost (ts : List AtomicDecl) : Nat :=
  let elims := elimHostPairs ts
  let comps := compElims ts
  let hostsWithCtors := ctorHosts ts
  elims.foldl (fun s (e, T) =>
    if hostsWithCtors.any (· == T) && comps.any (· == e) then s + 1 else s) 0

/-- Extra coherence for Π/Σ adjunction-like dual: counts once if both appear. -/
@[inline] def piSigmaCoherenceBonus (ts : List AtomicDecl) : Nat :=
  let hasPi    := ts.any (fun a => match a with | .declareTypeFormer "Pi"    => true | _ => false)
  let hasSigma := ts.any (fun a => match a with | .declareTypeFormer "Sigma" => true | _ => false)
  if hasPi && hasSigma then 1 else 0

/-- Compute effort for a *set of targets* (delta). -/
def effortOfTargets (ts : List AtomicDecl) : EffortBreakdown :=
  let intro := ts.foldl (fun n a => n + (if isIntro a then 1 else 0)) 0
  let eEss  := ts.foldl (fun n a => n + (if isEssentialElim a then 1 else 0)) 0
  let coh   := coherenceUnitsPerHost ts + piSigmaCoherenceBonus ts
  let raw   := intro + eEss
  let tot   := if raw = 0 then 0 else Nat.max 1 (raw - coh)
  { introRules := intro, essentialElims := eEss, coherenceDiscount := coh, total := tot }

end PEN.Select.Effort
