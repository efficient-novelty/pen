import Init
import PEN.CAD.Atoms

namespace PEN.Core.Levels

/-- Abstract level; keep it Nat for now. -/
abbrev Level := Nat

/-- Lookup from type names → Level. -/
structure LevelEnv where
  get : String → Level

/-- Default: base HoTT (0), classifiers (1). Extend as needed. -/
def defaultLevelEnv : LevelEnv :=
  { get := fun s =>
      if s == "Pi" || s == "Sigma" || s == "Man" then 1 else 0 }

open PEN.CAD
open AtomicDecl

/-- Level of a type name via env. -/
@[inline] def levelOfType (env : LevelEnv) (s : String) : Level := env.get s

/-- Level of an atomic decl via env. -/
@[inline] def levelOfDecl (env : LevelEnv) : AtomicDecl → Level
  | .declareUniverse _      => 0
  | .declareTypeFormer n    => levelOfType env n
  | .declareConstructor _ T => levelOfType env T
  | .declareEliminator _ T  => Nat.max 1 (levelOfType env T)
  | .declareCompRule _ _    => 1
  | .declareTerm _ T        => levelOfType env T

/-- Max level present in a context. -/
def contextLevel (env : LevelEnv) (Γ : Context) : Level :=
  let fromTF := Γ.typeFormers.foldl (fun m n => Nat.max m (levelOfType env n)) 0
  let fromElim := if Γ.eliminators.isEmpty then 0 else 1
  let fromComp := if Γ.compRules.isEmpty then 0 else 1
  Nat.max fromTF (Nat.max fromElim fromComp)

/-- Max level among a candidate’s targets. -/
def targetLevel (env : LevelEnv) (ts : List AtomicDecl) : Level :=
  ts.foldl (fun m t => Nat.max m (levelOfDecl env t)) 0

end PEN.Core.Levels

