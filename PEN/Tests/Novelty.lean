/-
  PEN/Tests/Novelty.lean

  Purpose
  -------
  Minimal unit test for Axiom 3 (novelty) accounting.

  We build a tiny action alphabet for `Unit` and check that
    ν(Unit) = 1
  when evaluating the package X = { typeFormer "Unit" } with the same
  exclusion policy used by the engine: endogenous attachments for a
  freshly introduced type former (its eliminator and the comp-rules
  that tie that eliminator to its constructors) do not score.

  Notes
  -----
  • `#eval` must be followed by a single term; we wrap the test in
    parentheses so multi-line `let` bindings are parsed as one term.
  • We mirror the engine’s exclusion using
      `eliminatorsForTypesIn` and `compRulesForElimsIn`.
  • If this test prints "ν(Unit)=1 (expected 1)", it passed.
-/
import Init
import PEN.CAD.Atoms
import PEN.Novelty.Novelty
import PEN.Select.Engine
import PEN.Grammar.HIT

open PEN.Novelty.Novelty
open PEN.Select.Engine
open PEN.CAD

open AtomicDecl

namespace PEN.Tests.Novelty

/-- Build a minimal actions alphabet for Unit. -/
def actionsUnit : List AtomicDecl :=
  [ declareUniverse 0
  , declareTypeFormer "Unit"
  , declareConstructor "star" "Unit"
  , declareEliminator "rec_Unit" "Unit"
  , declareCompRule "rec_Unit" "star"
  ]

  -- ν(Unit)=1 under our Axiom 3 keying: only `star` contributes for the Unit package.
  #eval
    let B      := Context.empty
    let H      := 2
    -- Only the type former itself is excluded; all eliminators key to it.
    let sc     : PEN.Novelty.Scope.ScopeConfig :=
      { actions := actionsUnit
      , horizon := H
      , preMaxDepth?  := some H
      , postMaxDepth? := some 1
      , exclude       := [declareTypeFormer "Unit"]
      , excludeKeys   := PEN.Novelty.Scope.keysOfTargets [declareTypeFormer "Unit"]
                        ++ [PEN.Novelty.Scope.FrontierKey.elim "Unit"] }
    match noveltyForPackage? B [declareTypeFormer "Unit"] sc with
    | none   => "NOVELTY_FAIL"
    | some r => s!"ν(Unit)={r.nu}  (expected 1)"

end PEN.Tests.Novelty
