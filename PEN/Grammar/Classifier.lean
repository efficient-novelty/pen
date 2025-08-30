/-
  PEN/Grammar/Classifier.lean

  Classifier-package schema:
  Generate CAD declarations for a "classifier" consisting of:
    - a type former (e.g., Man)
    - an optional closure schema (bundled rules, counted as one atom)
    - an optional eliminator/recursor (for morphisms in the classifier)
    - optional extra terms (aliases/canonical maps, if you want them in the package)

  Notes:
  * We model the "closure schema" as a `declareTerm` tied to the classifier type.
    This gives it a single-atom cost without introducing new CAD primitives.
  * We do NOT emit comp-rules here (there are no constructors attached to a classifier).
    If you need such ties, they should be part of HIT packages or separate specs.
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation  -- for `applyAll?`

namespace PEN.Grammar.Classifier

open PEN.CAD

/-- Specification for a classifier package. -/
structure ClassifierSpec where
  /-- Name of the classifier type former (e.g., "Man"). -/
  typeName        : String
  /-- Optional explicit eliminator name; default is `"hom_" ++ typeName`. -/
  elimName?       : Option String := none
  /-- Include an eliminator/recursor for classifier morphisms? -/
  withEliminator  : Bool := true
  /-- Include a single-atom "closure schema" term (e.g., product/unit closure)? -/
  withClosure     : Bool := true
  /-- Optional explicit name for the closure schema term; default `"schema_" ++ typeName`. -/
  closureName?    : Option String := none
  /-- Optional extra terms to bundle into the package (by name). -/
  extraTerms      : List String := []
deriving Repr, Inhabited

namespace ClassifierSpec

@[inline] def elimName (s : ClassifierSpec) : String :=
  s.elimName?.getD s!"hom_{s.typeName}"

@[inline] def closureName (s : ClassifierSpec) : String :=
  s.closureName?.getD s!"schema_{s.typeName}"

end ClassifierSpec

/--
  Core declarations for a classifier package (no universe).
  The list contains:
    1. `declareTypeFormer typeName`
    2. (optional) `declareTerm (closureName) typeName`     -- counts as 1 atom for bundled closures
    3. (optional) `declareEliminator (elimName) typeName`
    4. (optional) `declareTerm t typeName` for each `t` in `extraTerms`
-/
def declsCore (spec : ClassifierSpec) : List AtomicDecl :=
  let tf   : List AtomicDecl := [.declareTypeFormer spec.typeName]
  let clos : List AtomicDecl :=
    (if spec.withClosure then
      [.declareTerm (ClassifierSpec.closureName spec) spec.typeName]
     else [])
  let elim : List AtomicDecl :=
    (if spec.withEliminator then
      [.declareEliminator (ClassifierSpec.elimName spec) spec.typeName]
     else [])
  let extras : List AtomicDecl :=
    spec.extraTerms.map (fun nm => .declareTerm nm spec.typeName)
  tf ++ clos ++ elim ++ extras

/--
  Full action menu for a classifier package.
  If `u? = some ℓ`, prepends `declareUniverse ℓ` so the package can be installed from ∅.
-/
def actionsForClassifier (spec : ClassifierSpec) (u? : Option Nat := none) : List AtomicDecl :=
  (match u? with
   | some ℓ => [.declareUniverse ℓ]
   | none   => [])
  ++ declsCore spec

/-- Attempt to apply the classifier package declarations to a context. -/
def installClassifier? (Γ : Context) (spec : ClassifierSpec) (u? : Option Nat := none) : Option Context :=
  applyAll? Γ (actionsForClassifier spec u?)

/-! ## Convenience specifications

  The following predefs are handy starting points. You can always customize
  names or disable elements via the `ClassifierSpec` fields.
-/

/-- Smooth manifold classifier package (3 atoms by default). -/
def specManifold (typeName := "Man") : ClassifierSpec :=
  { typeName       := typeName
  , elimName?      := some s!"C∞_{typeName}"   -- name for "smooth maps" eliminator
  , withEliminator := true
  , withClosure    := true                     -- e.g., product/unit closure, counted as 1 atom
  , closureName?   := some s!"schema_{typeName}"
  , extraTerms     := []                       -- add standard aliases if you want them pre-installed
  }

/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl

def Γ0 : Context := Context.empty

-- Self-contained install from ∅ by including a universe.
#eval installClassifier? Γ0 (specManifold "Man") (some 0) |>.isSome  -- true

-- See the resulting actions list (first few).
#eval (actionsForClassifier (specManifold "Man") (some 0)).take 5

-- Install without a universe when U0 is already present.
def Γu := (step Γ0 (.declareUniverse 0)).getD Γ0
#eval installClassifier? Γu (specManifold "Man") none |>.isSome  -- true

-/

end PEN.Grammar.Classifier
