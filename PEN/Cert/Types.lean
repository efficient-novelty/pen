/-
  PEN/Cert/Types.lean

  Certificate record types for auditable runs:
    * PackageCert            — κ-certificate for installing a package X on B
    * FrontierEntryCert      — certificate for a single frontier entry Y
    * NoveltyCert            — bundle: package install + frontier + ν accounting
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa               -- goalOfDecl
import PEN.Novelty.Scope            -- FrontierEntry
import PEN.Novelty.Novelty          -- NoveltyReport (optional, no cycle)

namespace PEN.Cert

open PEN.CAD
open PEN.Novelty.Scope
open PEN.Novelty.Novelty

/-- Do all target declarations hold in the given context? -/
@[inline] def goalsHold (targets : List AtomicDecl) (Γ : Context) : Bool :=
  targets.all (fun t => PEN.CAD.goalOfDecl t Γ)

/-! ###########################################################################
    Package install certificate
############################################################################# -/

/--
  κ-certificate that a *package* (list of target declarations) is installed
  on top of a start context.
-/
structure PackageCert (start : Context) where
  targets : List AtomicDecl
  cert    : DerivCert start
  post    : Context
  kappa   : Nat
  okGoals : Bool
deriving Repr

/-- Smart constructor computing the redundant fields and the boolean check. -/
@[inline] def mkPackageCert
  {start : Context} (targets : List AtomicDecl) (cert : DerivCert start)
  : PackageCert start :=
  { targets := targets
    cert    := cert
    post    := cert.finish
    kappa   := cert.length
    okGoals := goalsHold targets cert.finish }

/-! ###########################################################################
    Frontier entry certificate
############################################################################# -/

/--
  Certificate for a *single* horizon-bounded frontier entry Y, relative to a
  fixed pre/post pair (B, B ∪ X).
-/
structure FrontierEntryCert (pre post : Context) where
  entry      : FrontierEntry
  postCert   : DerivCert post
  preCert?   : Option (DerivCert pre)
  okPostGoal : Bool
  okKPost    : Bool
  okKPreEff  : Bool
deriving Repr

/-- Smart constructor computing the boolean checks. -/
@[inline] def mkFrontierEntryCert
  {pre post : Context}
  (entry : FrontierEntry)
  (postCert : DerivCert post)
  (preCert? : Option (DerivCert pre))
  : FrontierEntryCert pre post :=
  let okPostGoal := PEN.CAD.goalOfDecl entry.target postCert.finish
  let okKPost    := (postCert.length == entry.kPost)
  let okKPreEff  :=
    match preCert? with
    | some c => (c.length == entry.kPreEff)
    | none   => true
  { entry, postCert, preCert?, okPostGoal, okKPost, okKPreEff }

/-! ###########################################################################
    Novelty bundle certificate
############################################################################# -/

/--
  Certificate bundling a novelty computation for a package X from basis B.

  Checks:
    * `okNu` — recomputed Σ max(0, κ̃_pre - κ_post) equals the reported `nu`
               (using just the numeric fields of `entries`)
-/
structure NoveltyCert (pre : Context) where
  pkg        : PackageCert pre
  horizon    : Nat
  entries    : List FrontierEntry
  nu         : Nat
  rho        : Float
  entryCerts : List (FrontierEntryCert pre pkg.post) := []
  okNu       : Bool
deriving Repr

/-- Sum the numeric novelty contributions from a list of frontier entries. -/
@[inline] def sumFrontierContribs (_post : Context) (es : List FrontierEntry) : Nat :=
  PEN.Novelty.Scope.sumContrib01 es

/-- Smart constructor from a `PackageCert` and a `NoveltyReport`. -/
@[inline] def mkNoveltyCertFromReport
  {pre : Context}
  (pkg : PackageCert pre)
  (H   : Nat)
  (rep : NoveltyReport)
  (entryCerts : List (FrontierEntryCert pre pkg.post) := [])
  : NoveltyCert pre :=
  let okNu := sumFrontierContribs pkg.post rep.frontier == rep.nuCore
  { pkg        := pkg
    horizon    := H
    entries    := rep.frontier
    nu         := rep.nu
    rho        := rep.rho
    entryCerts := entryCerts
    okNu       := okNu }

/-! ###########################################################################
    Convenience / small utilities
############################################################################# -/

/-- A compact text line for logs (no functions, just numbers). -/
def asRow (n : NoveltyCert pre) : String :=
  s!"H={n.horizon}, κ={n.pkg.kappa}, ν={n.nu}, ρ={n.rho}"

/-- Verify that every entry cert matches the numeric fields of `entries`. -/
def entryCertsMatch (n : NoveltyCert pre) : Bool :=
  let pairs := n.entries.zip n.entryCerts
  pairs.all (fun (e, c) =>
    c.entry.target == e.target
    && c.okKPost
    && c.okKPreEff
    && c.okPostGoal)

/-! # Tiny sanity checks (uncomment locally)

open PEN.Grammar.HIT
open PEN.Novelty.Scope

def Γ0 : Context := Context.empty
def Γu : Context := (PEN.CAD.step Γ0 (AtomicDecl.declareUniverse 0)).getD Γ0

-- Build a minimal package (S1 without eliminator/comp rules) and certify it:
def S1_noRec := { (specS1 "S1") with withEliminator := false, withCompRules := false }
def targetsX : List AtomicDecl := PEN.Grammar.HIT.declsCore S1_noRec

-- Build a proper DerivCert using the equality from running the derivation:
def certX? : Option (DerivCert Γu) :=
  match h : PEN.CAD.runDerivation Γu targetsX with
  | some post =>
      -- witness: runDerivation Γu targetsX = some post
      let wit := by simpa [PEN.CAD.runDerivation, h]
      some { deriv := targetsX, finish := post, witness := wit }
  | none => none

#eval match certX? with
     | none      => "failed"
     | some cert =>
         let pc := mkPackageCert targetsX cert
         (pc.kappa, pc.okGoals)

-/

end PEN.Cert
