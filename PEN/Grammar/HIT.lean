/-
  PEN/Grammar/HIT.lean

  Higher‑Inductive-Type schema:
  Generate CAD declarations for a "HIT-like" package consisting of:
    - a type former (e.g., S1, S2, Man, ...)
    - a list of constructors (0/1/2‑cells modeled as constructors)
    - an optional eliminator/recursor, and optional computation rules
      tying the eliminator to each constructor.

  The engine does not need to "know" semantics; names are syntactic.
  This module simply emits `AtomicDecl` lists you can feed to the κ/ν
  machinery (search, novelty, etc.).
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation  -- for `applyAll?` convenience

namespace PEN.Grammar.HIT

open PEN.CAD

/-- Specification for a higher‑order template (HIT‑like package). -/
structure HITSpec where
  /-- Name of the type former to declare. -/
  typeName        : String
  /-- Number of point constructors (0‑cells). -/
  nPoints         : Nat := 0
  /-- Number of 1‑path constructors (1‑cells). -/
  nPaths1         : Nat := 0
  /-- Number of 2‑path constructors (2‑cells). -/
  nPaths2         : Nat := 0
  /-- Name prefix for point constructors (default `"pt"`). -/
  prefixPoint     : String := "pt"
  /-- Name prefix for 1‑path constructors (default `"loop"`). -/
  prefixPath1     : String := "loop"
  /-- Name prefix for 2‑path constructors (default `"surf"`). -/
  prefixPath2     : String := "surf"
  /-- Optional explicit eliminator name; otherwise uses `"rec_" ++ typeName`. -/
  elimName?       : Option String := none
  /-- Whether to include an eliminator/recursor. -/
  withEliminator  : Bool := true
  /-- Whether to include a comp‑rule for each constructor tying to the eliminator. -/
  withCompRules   : Bool := true
deriving Repr, Inhabited

namespace HITSpec

@[inline] def elimName (s : HITSpec) : String :=
  s.elimName?.getD s!"rec_{s.typeName}"

@[inline] def ctorNamesPoints (s : HITSpec) : List String :=
  (List.range s.nPoints).map (fun i => s!"{s.typeName}.{s.prefixPoint}{i}")

@[inline] def ctorNamesPaths1 (s : HITSpec) : List String :=
  (List.range s.nPaths1).map (fun i => s!"{s.typeName}.{s.prefixPath1}{i}")

@[inline] def ctorNamesPaths2 (s : HITSpec) : List String :=
  (List.range s.nPaths2).map (fun i => s!"{s.typeName}.{s.prefixPath2}{i}")

@[inline] def ctorNamesAll (s : HITSpec) : List String :=
  ctorNamesPoints s ++ ctorNamesPaths1 s ++ ctorNamesPaths2 s

end HITSpec

/--
  Core declarations for a HIT package (no universe). The list contains:
    1. `declareTypeFormer typeName`
    2. `declareConstructor name typeName` for every constructor (points/paths)
    3. (optional) `declareEliminator elimName typeName`
    4. (optional) `declareCompRule elimName ctorName` for each constructor
-/
def declsCore (spec : HITSpec) : List AtomicDecl :=
  let tf   : List AtomicDecl := [.declareTypeFormer spec.typeName]
  let cstr : List AtomicDecl :=
    (HITSpec.ctorNamesAll spec).map (fun c => .declareConstructor c spec.typeName)
  let elim : List AtomicDecl :=
    (if spec.withEliminator then
      [.declareEliminator (HITSpec.elimName spec) spec.typeName]
     else [])
  let comps : List AtomicDecl :=
    (if spec.withEliminator && spec.withCompRules then
      (HITSpec.ctorNamesAll spec).map (fun c => .declareCompRule (HITSpec.elimName spec) c)
     else [])
  tf ++ cstr ++ elim ++ comps

/--
  Full action menu for a HIT package. If `u? = some ℓ`, prepends `declareUniverse ℓ`.
  This is useful if you want a self-contained action set for κ‑search from the empty context.
-/
def actionsForHIT (spec : HITSpec) (u? : Option Nat := none) : List AtomicDecl :=
  (match u? with
   | some ℓ => [.declareUniverse ℓ]
   | none   => [])
  ++ declsCore spec

/-- Attempt to apply the HIT package declarations to a context. -/
def installHIT? (Γ : Context) (spec : HITSpec) (u? : Option Nat := none) : Option Context :=
  applyAll? Γ (actionsForHIT spec u?)

/-! ## Convenience specifications

  These are ready‑to‑use HIT specs for common patterns. They auto‑generate constructor
  names from prefixes, with trailing indices starting at 0 (e.g., `S1.base0`, `S1.loop0`).
  Exact names do not matter for the engine; determinism comes from enumeration order.
-/

/-- Circle‑like pattern: 1 point, 1 loop, with eliminator+rules. -/
def specS1 (typeName := "S1") : HITSpec :=
  { typeName       := typeName
  , nPoints        := 1
  , nPaths1        := 1
  , nPaths2        := 0
  , prefixPoint    := "base"
  , prefixPath1    := "loop"
  , prefixPath2    := "surf"
  , elimName?      := some s!"rec_{typeName}"
  , withEliminator := true
  , withCompRules  := true
  }

/-- 2‑sphere‑like pattern: 1 point, 1 surface (2‑cell), with eliminator+rules. -/
def specS2 (typeName := "S2") : HITSpec :=
  { typeName       := typeName
  , nPoints        := 1
  , nPaths1        := 0
  , nPaths2        := 1
  , prefixPoint    := "base"
  , prefixPath1    := "loop"
  , prefixPath2    := "surf"
  , elimName?      := some s!"rec_{typeName}"
  , withEliminator := true
  , withCompRules  := true
  }

/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl

def Γ0 : Context := Context.empty

-- If you want a self-contained installer from ∅, include a universe.
#eval installHIT? Γ0 (specS1 "S1") (some 0) |>.isSome  -- true

-- Look at the declarations the S1 spec would produce (first few).
#eval (actionsForHIT (specS1 "S1") (some 0)).take 6

-- Apply S2 without universe in a context that already contains U0:
def Γu := (step Γ0 (.declareUniverse 0)).getD Γ0
#eval installHIT? Γu (specS2 "S2") none |>.isSome -- true

-/

end PEN.Grammar.HIT
