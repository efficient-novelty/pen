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
