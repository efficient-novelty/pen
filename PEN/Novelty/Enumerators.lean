/-
  PEN/Novelty/Enumerators.lean

  Reusable enumerators for novelty frontiers, plus helpers to augment
  the action menu so the κ-search can realize the proposed targets.

  Provided sets:
    * Π/Σ aliases:  →, ×, ∀, ∃, eval          (as declareTerm ... hostType)
    * Classifier maps: id, const, pi1, pi2, diag, swap  (declareTerm ... typeName)

  Usage pattern:
    - Choose a host type (e.g., "S1" or "Man").
    - Augment `scope.actions` with `actionsWithPiSigmaAliases` or
      `actionsWithClassifierMaps`, so κ(Y | post) is realizable.
    - Add the corresponding enumerators to `scope.enumerators`.
-/

import Init
import PEN.CAD.Atoms
import PEN.Novelty.Scope

namespace PEN.Novelty.Enumerators

open PEN.CAD
open PEN.Novelty.Scope
open AtomicDecl

/-! ## Π/Σ aliases -/

def piSigmaAliasNames : List String :=
  ["alias_arrow", "alias_prod", "alias_forall", "alias_exists", "alias_eval"]

/-- Fixed-host Π/Σ alias enumerator: proposes aliases as terms on `hostType`. -/
def enumPiSigmaAliasesFor (hostType : String) : FrontierEnumerator :=
  fun Γ =>
    if Γ.hasTypeFormer hostType then
      piSigmaAliasNames.map (fun nm => AtomicDecl.declareTerm nm hostType)
    else
      []

/-- Propose Π/Σ alias families on every non-classifier host present in the context. -/
def enumPiSigmaAliasesOnNonClassifiers : FrontierEnumerator :=
  fun Γ =>
    let hasPi    := Γ.hasTypeFormer "Pi"
    let hasSigma := Γ.hasTypeFormer "Sigma"
    if not (hasPi || hasSigma) then [] else
      let hosts := Γ.typeFormers.filter (fun T => not (isClassifierTFName T))
      let perHost : String → List AtomicDecl := fun T =>
        let piAliases : List AtomicDecl :=
          if hasPi then
            [ AtomicDecl.declareTerm "alias_arrow"  T
            , AtomicDecl.declareTerm "alias_forall" T
            , AtomicDecl.declareTerm "alias_eval"   T ]
          else []
        let sigmaAliases : List AtomicDecl :=
          if hasSigma then
            [ AtomicDecl.declareTerm "alias_prod"   T
            , AtomicDecl.declareTerm "alias_exists" T ]
          else []
        piAliases ++ sigmaAliases
      dedupBEq (hosts.bind perHost)



/-- Augment an actions list with Π/Σ alias declareTerm steps for a given host. -/
def actionsWithPiSigmaAliases (actions : List AtomicDecl) (hostType : String) : List AtomicDecl :=
  actions ++ piSigmaAliasNames.map (fun nm => AtomicDecl.declareTerm nm hostType)

/-! ## Classifier canonical maps -/

def classifierMapBaseNames : List String :=
  ["id", "const", "pi1", "pi2", "diag", "swap"]

/-- For uniqueness, we suffix the names with `_{typeName}`. -/
def classifierMapNames (typeName : String) : List String :=
  classifierMapBaseNames.map (fun nm => s!"{nm}_{typeName}")

/-- Fixed-type classifier maps enumerator: proposes canonical maps as terms on `typeName`. -/
def enumClassifierMapsFor (typeName : String) : FrontierEnumerator :=
  fun Γ =>
    if Γ.hasTypeFormer typeName then
      (classifierMapNames typeName).map (fun nm => AtomicDecl.declareTerm nm typeName)
    else
      []

/-- Augment an actions list with classifier-map declareTerm steps for `typeName`. -/
def actionsWithClassifierMaps (actions : List AtomicDecl) (typeName : String) : List AtomicDecl :=
  actions ++ (classifierMapNames typeName).map (fun nm => AtomicDecl.declareTerm nm typeName)

/-- The five Π/Σ alias declarations, typed so they *depend* on Π/Σ. -/
def aliasTermDeclsPiSigma : List AtomicDecl :=
  [ declareTerm "alias_arrow"  "Pi"     -- →
  , declareTerm "alias_forall" "Pi"     -- ∀
  , declareTerm "alias_eval"   "Pi"     -- eval
  , declareTerm "alias_prod"   "Sigma"  -- ×
  , declareTerm "alias_exists" "Sigma"  -- ∃
  ]

@[inline] def isPiSigmaAliasTF : AtomicDecl → Bool
  | .declareTypeFormer "alias_arrow"  => true
  | .declareTypeFormer "alias_forall" => true
  | .declareTypeFormer "alias_eval"   => true
  | .declareTypeFormer "alias_prod"   => true
  | .declareTypeFormer "alias_exists" => true
  | _ => false

@[inline] def keepOnePiSigmaAlias (xs : List AtomicDecl) (keep : String := "alias_arrow")
    : List AtomicDecl :=
  xs.filter (fun a =>
    if isPiSigmaAliasTF a then
      match a with
      | .declareTypeFormer n => n == keep
      | _ => true
    else
      true)

/-- Emit the 5 Π/Σ alias terms when both Π and Σ are present. -/
def enumPiSigmaAliasesGlobal : FrontierEnumerator :=
  fun Γ =>
    if Γ.hasTypeFormer "Pi" && Γ.hasTypeFormer "Sigma" then
      aliasTermDeclsPiSigma     -- your existing 5-standard-alias list
    else
      []


/-- Enumerator that proposes the five Π/Σ aliases (ignores context). -/
def enumPiSigmaAliasesCore : FrontierEnumerator :=
  fun _ => aliasTermDeclsPiSigma

/-- Optional: add the alias declarations to an action set. -/
def actionsWithPiSigmaAliasTerms (base : List AtomicDecl) : List AtomicDecl :=
  base ++ aliasTermDeclsPiSigma

/-- Eight canonical 1-step “map” terms for a classifier type (e.g. `Man`). -/
def classifierMapTermDecls (typeName : String) : List AtomicDecl :=
  [ declareTerm s!"{typeName}.atlas"       typeName
  , declareTerm s!"{typeName}.chart"       typeName
  , declareTerm s!"{typeName}.transition"  typeName
  , declareTerm s!"{typeName}.frame"       typeName
  , declareTerm s!"{typeName}.coframe"     typeName
  , declareTerm s!"{typeName}.pullback"    typeName
  , declareTerm s!"{typeName}.pushforward" typeName
  , declareTerm s!"{typeName}.jacobian"    typeName
  ]

/-- Add the classifier 1-step map terms to an action set. -/
def actionsWithClassifierMapTerms (base : List AtomicDecl) (typeName : String) : List AtomicDecl :=
  base ++ classifierMapTermDecls typeName

private def holdsDecl (Γ : Context) : AtomicDecl → Bool
  | .declareUniverse ℓ      => Γ.hasUniverse ℓ
  | .declareInfrastructure n => Γ.hasInfrastructure n
  | .declareTypeFormer n    => Γ.hasTypeFormer n
  | .declareConstructor c _ => Γ.hasConstructor c
  | .declareEliminator e _  => Γ.hasEliminator e
  | .declareCompRule e c    => Γ.hasCompRule e c
  | .declareTerm t _        => Γ.hasTerm t

/-- Recognize exactly the five Π/Σ alias declarations in the action alphabet. -/
@[inline] private def isPiSigmaAliasDecl : AtomicDecl → Bool
  | .declareTerm nm T => isPiSigmaAlias nm T
  | _ => false

/-- Simple BEq-based dedup. -/
@[inline] private def dedupBEq [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.any (· == x) then acc else acc ++ [x]) []

/--
If Γ already has both Π and Σ, enumerate the five exact alias terms
(Π: arrow/forall/eval; Σ: prod/exists) that are not yet installed in Γ.
Returning exact atoms yields ν = 5 for the Π/Σ pair.
-/
def enumPiSigmaAliases : FrontierEnumerator :=
  fun Γ =>
    if Γ.hasTypeFormer "Pi" && Γ.hasTypeFormer "Sigma" then
      let notYet := aliasTermDeclsPiSigma.filter (fun a => not (holdsDecl Γ a))
      dedupBEq notYet
    else
      []



end PEN.Novelty.Enumerators
