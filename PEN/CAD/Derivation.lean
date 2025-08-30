/-
  PEN/CAD/Derivation.lean

  Well-formed derivations and certificates for CAD (atomic declarations).

  This module provides:
  - `Derivation := List AtomicDecl`
  - `isWellFormed : Derivation → Context → Bool`
  - `runDerivation : Context → Derivation → Option Context`
  - `DerivCert` — a certificate that a derivation runs successfully
  - constructors: `DerivCert.mk?`, `DerivCert.step?`
  - helpers: `kappaOfDerivation` (= length), `append`, `length`

  It’s deliberately computation-first: certificates carry a concrete
  `finish : Context` together with an equality witness
  `applyAll? start deriv = some finish`.
-/

import Init
import PEN.CAD.Atoms

namespace PEN.CAD

/-- A derivation is a finite sequence of atomic declarations. -/
abbrev Derivation := List AtomicDecl

/-- Run a derivation in a starting context. If any step is invalid, return `none`. -/
@[inline] def runDerivation (Γ : Context) (d : Derivation) : Option Context :=
  applyAll? Γ d

/-- A derivation is well-formed in `Γ` iff it runs to some context. -/
@[inline] def isWellFormed (d : Derivation) (Γ : Context) : Bool :=
  (runDerivation Γ d).isSome

/-- The (trivial) effort of a derivation: its length. -/
@[inline] def kappaOfDerivation (d : Derivation) : Nat := d.length

/--
  A derivation certificate: starting from `start`, the list of declarations
  `deriv` executes successfully to produce `finish`.
-/
structure DerivCert (start : Context) where
  deriv  : Derivation
  finish : Context
  witness : runDerivation start deriv = some finish
deriving Repr

namespace DerivCert

/-- The length (effort) of the certified derivation. -/
@[inline] def length {Γ} (c : DerivCert Γ) : Nat := c.deriv.length

/--
  Attempt to build a certificate by actually running the derivation.
  Returns `none` if any step is invalid.
-/
def mk? (start : Context) (d : Derivation) : Option (DerivCert start) :=
  match h : runDerivation start d with
  | none      => none
  | some fin  => some { deriv := d, finish := fin, witness := by simpa [runDerivation, h] }

/-- Single-step certificate (for convenience). -/
def step? (start : Context) (decl : AtomicDecl) : Option (DerivCert start) :=
  mk? start [decl]

/--
  Compute a new certificate for the concatenation `c1.deriv ++ c2.deriv`.
  This does not try to reuse proofs compositionally; it re-runs the concatenated
  derivation to produce a fresh computational witness.
-/
def append {Γ} (c1 : DerivCert Γ) (c2 : DerivCert c1.finish) : Option (DerivCert Γ) :=
  mk? Γ (c1.deriv ++ c2.deriv)

end DerivCert

/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl

def Γ0 : Context := Context.empty

-- Build a short well-formed derivation: U0; Unit; star:Unit
def dU0 : Derivation := [declareUniverse 0]
def dUnit : Derivation := [declareTypeFormer "Unit"]
def dStar : Derivation := [declareConstructor "star" "Unit"]

#eval isWellFormed dUnit Γ0      -- false (no universe yet)
#eval isWellFormed (dU0 ++ dUnit) Γ0  -- true

def cU0?   := DerivCert.mk? Γ0 dU0
#eval cU0?.isSome

def Γ1 : Context := cU0?.get!.finish
def cUnit? := DerivCert.mk? Γ1 dUnit
def Γ2 : Context := cUnit?.get!.finish
def cStar? := DerivCert.mk? Γ2 dStar

#eval cStar?.isSome

-- Compose certificates by recomputing on the concatenated derivation:
def cAll? : Option (DerivCert Γ0) :=
  do
    let c0 ← cU0?
    let c1 ← cUnit?
    let c01 ← DerivCert.append c0 c1
    let c2 ← cStar?
    DerivCert.append c01 c2

#eval cAll?.isSome
#eval cAll?.map (·.length)  -- Some 3

-/

end PEN.CAD
