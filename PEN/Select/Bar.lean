/-
  PEN/Select/Bar.lean

  Bars and running averages for selection:
    * Tick, History
    * ρ(tick) = ν/κ
    * Ω(history) = (Σν)/(Σκ)
    * Two-tap bar (per Axiom 5, Step 3)
    * Golden-ratio bar: φ ⋅ Ω  (with φ ≈ 1.618...)
    * Snapshot helper

  This module is mathlib-free and uses Float for convenience.
-/

import Init

namespace PEN.Select.Bar

/-- One realized ledger entry. -/
structure Tick where
  nu     : Nat
  kappa  : Nat
deriving Repr, BEq, Inhabited

/-- Chronological list of realized ticks (earliest first). -/
abbrev History := List Tick

/-- Append a new realized tick at the end (chronological order). -/
@[inline] def pushTick (h : History) (nu kappa : Nat) : History :=
  h ++ [Tick.mk nu kappa]

/-- Sum of all ν in the history. -/
@[inline] def sumNu (h : History) : Nat :=
  h.foldl (fun s t => s + t.nu) 0

/-- Sum of all κ in the history. -/
@[inline] def sumKappa (h : History) : Nat :=
  h.foldl (fun s t => s + t.kappa) 0

/-- Efficiency of a single tick as a Float (0.0 if κ=0). -/
@[inline] def rhoTick (t : Tick) : Float :=
  if t.kappa = 0 then 0.0 else (Float.ofNat t.nu) / (Float.ofNat t.kappa)

/-- Running Ω(history) = (Σν)/(Σκ) as Float (0.0 if Σκ=0). -/
@[inline] def omega (h : History) : Float :=
  let n := sumNu h
  let k := sumKappa h
  if k = 0 then 0.0 else (Float.ofNat n) / (Float.ofNat k)

/-- Golden ratio φ as a Float (no sqrt dependency). -/
@[inline] def phi : Float := 1.618033988749895

/-- Golden-ratio bar: φ ⋅ Ω(history). -/
@[inline] def barPhi (h : History) : Float :=
  phi * omega h

/-- Resonance bar: β(τ) ⋅ Ω(τ−1). -/
@[inline] def barResonance (beta : Float) (h : History) : Float :=
  beta * omega h

/-- Global bar per the new axioms: Bar(τ) = Φ(τ) · Ω(τ−1) with Φ(τ)=τ/τ<.
    If no previous realization exists, Bar(τ)=0. -/
@[inline] def barGlobal (tau : Nat) (lastRealizedTau? : Option Nat) (h : History) : Float :=
  match lastRealizedTau? with
  | none      => 0.0
  | some tauPrev =>
      if tauPrev = 0 then 0.0
      else
        let phi : Float := (Float.ofNat tau) / (Float.ofNat tauPrev)
        phi * omega h

/-- Last element of a list, if any. -/
def last1? {α} : List α → Option α
  | []        => none
  | [x]       => some x
  | _ :: xs   => last1? xs

/-- Last two elements of a list, if any (in chronological order). -/
def last2? {α} : List α → Option (α × α)
  | []            => none
  | [_]           => none
  | [x, y]        => some (x, y)
  | _ :: xs       => last2? xs

/--
  Two-tap bar per Axiom 5, Step 3:
   - 0 if no realizations yet;
   - ρ(last) if exactly one prior realization;
   - (ν_last + ν_prev) / (κ_last + κ_prev) if two or more.
-/
def barTwoTap (h : History) : Float :=
  match last2? h with
  | some (tPrev, tLast) =>
      let n := tPrev.nu + tLast.nu
      let k := tPrev.kappa + tLast.kappa
      if k = 0 then 0.0 else (Float.ofNat n) / (Float.ofNat k)
  | none =>
      match last1? h with
      | some t => rhoTick t
      | none   => 0.0

/-- A convenient summary of bars and running averages. -/
structure BarSnapshot where
  sumNu     : Nat
  sumKappa  : Nat
  omega     : Float
  twoTap    : Float
  phiOmega  : Float
deriving Repr

/-- Build a snapshot for the current history. -/
def snapshot (h : History) : BarSnapshot :=
  { sumNu    := sumNu h
    sumKappa := sumKappa h
    omega    := omega h
    twoTap   := barTwoTap h
    phiOmega := barPhi h }

/-! # Tiny sanity checks (uncomment locally)

-- Reproduce the early ledger up to τ = 8 from the paper’s table:
-- τ=1:(ν,κ)=(1,2), τ=2:(1,1), τ=3:(2,1), τ=5:(5,3), τ=8:(7,3).
def hist_τ8 : History :=
  []
  |> fun h => pushTick h 1 2
  |> fun h => pushTick h 1 1
  |> fun h => pushTick h 2 1
  |> fun h => pushTick h 5 3
  |> fun h => pushTick h 7 3

#eval snapshot hist_τ8
-- Expect:
--  sumNu    = 16
--  sumKappa = 10
--  omega    = 1.6
--  twoTap   = (7+5)/(3+3) = 12/6 = 2.0
--  phiOmega ≈ 1.618033988749895 * 1.6 ≈ 2.588854382

-/

end PEN.Select.Bar
