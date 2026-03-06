import PEN.Core.Codebook
import PEN.Core.Levels
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa
import PEN.Grammar.HIT
import PEN.Grammar.Classifier
import PEN.Novelty.Scope
import PEN.Novelty.Novelty
import PEN.Novelty.Enumerators
import PEN.Select.Bar
import PEN.Select.Engine
import PEN.Cert.Types
import PEN.Cert.Check
import PEN.Genesis
import PEN.Select.Discover
import PEN.Acceptance.ReferenceAssets
import PEN.Tests.Novelty

/-!
open PEN.CAD
open PEN.Novelty.Scope
open PEN.Novelty.Novelty
open PEN.Novelty.Enumerators
open PEN.Grammar.Classifier


def Γ0 : Context := Context.empty
def Manspec := specManifold "Man"


-- Start from ∅, allow the package + canonical maps in κ-search:
def actionsManBase : List AtomicDecl := actionsForClassifier Manspec (some 0)
def actionsMan      : List AtomicDecl := actionsWithClassifierMaps actionsManBase "Man"

def scopeMan : ScopeConfig :=
  { actions      := actionsMan
  , enumerators  := [enumClassifierMapsFor "Man"]   -- propose id/const/pi1/pi2/diag/swap
  , horizon      := 6
  , preMaxDepth? := none
  , exclude      := [] }

#eval noveltyForClassifierSpec? Γ0 Manspec scopeMan (maxDepthX := 7)
  |>.map (fun r => (r.kX, r.nu, r.rho))
-- Expect something like: kX = 4 (U0 + 3 atoms), ν > 0, ρ > 0.




open PEN.CAD
open PEN.Novelty.Scope
open PEN.Novelty.Novelty
open PEN.Novelty.Enumerators
open PEN.Grammar.HIT

def Γ0 : Context := Context.empty
def S1spec := specS1 "S1"

-- Allow full S1 package + Π/Σ aliases over "S1" in κ-search:
def actionsS1Base : List AtomicDecl := actionsForHIT S1spec (some 0)
def actionsS1      : List AtomicDecl := actionsWithPiSigmaAliases actionsS1Base "S1"

def scopeS1 : ScopeConfig :=
  { actions      := actionsS1
  , enumerators  := [enumPiSigmaAliasesFor "S1"]   -- propose →, ×, ∀, ∃, eval aliases
  , horizon      := 3
  , preMaxDepth? := none
  , exclude      := [] }

#eval noveltyForHITSpec? Γ0 S1spec scopeS1 (maxDepthX := 8)
  |>.map (fun r => (r.kX, r.nu, r.rho))
-- With S1 installed post-state, the alias terms are 1-step; pre-state they
-- aren't available (truncated to H+1), so ν should be positive.

-/
