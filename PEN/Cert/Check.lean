/-
  PEN/Cert/Check.lean

  Lightweight certificate checkers and replay utilities.

  What you get:
    * ctxEq                      — Boolean, fieldwise equality for CAD.Context
    * Flag / Summary             — tiny reporting helpers
    * checkPackageCertBasic      — validate a PackageCert (derivation runs, goals hold)
    * checkFrontierEntryCertBasic
    * checkFrontierEntryCertAgainstSearch (re-run κ-search for kPost/kPreEff)
    * checkNoveltyCertBasic      — validate ν sums and ρ consistency
    * checkNoveltyCertAgainstScope
        - replay novelty with a supplied ScopeConfig and compare frontier/ν/ρ

  All checks are *computational* (Bool), easy to print/log and reproduce.
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa
import PEN.Novelty.Scope
import PEN.Novelty.Novelty
import PEN.Cert.Types

namespace PEN.Cert.Check

open PEN.CAD
open PEN.Novelty.Scope
open PEN.Novelty.Novelty
open PEN.Cert
open AtomicDecl

/-! ## Equality on CAD contexts (Boolean, fieldwise) -/

@[inline] def ctxEq (A B : Context) : Bool :=
  A.universes   == B.universes
  && A.typeFormers == B.typeFormers
  && A.constructors == B.constructors
  && A.eliminators  == B.eliminators
  && A.compRules    == B.compRules
  && A.terms        == B.terms

/-! ## Tiny reporting helpers -/

structure Flag where
  label : String
  ok    : Bool
deriving Repr

structure Summary where
  ok    : Bool
  flags : List Flag
deriving Repr

@[inline] def mkSummary (flags : List Flag) : Summary :=
  { ok := flags.all (·.ok), flags }

/-! ## Package checks -/

/-- Recompute the run and compare finish context to the stored one (via `ctxEq`). -/
def checkDerivWitness {start : Context} (c : DerivCert start) : Bool :=
  match runDerivation start c.deriv with
  | some fin => ctxEq fin c.finish
  | none     => false

/-- Validate a package install certificate (derivation runs, goals hold, κ matches length). -/
def checkPackageCertBasic {start : Context} (pc : PackageCert start) : Summary :=
  let fRun    : Flag := { label := "derivation-runs", ok := checkDerivWitness pc.cert }
  let fKappa  : Flag := { label := "kappa=length",    ok := pc.kappa == pc.cert.length }
  let fGoals  : Flag := { label := "goals-hold",      ok := goalsHold pc.targets pc.post }
  mkSummary [fRun, fKappa, fGoals]

/-! ## Frontier entry checks -/

/-- Minimal shape check (no replay): post goal holds and recorded lengths match the certs. -/
def checkFrontierEntryCertBasic
  {pre post : Context} (fc : FrontierEntryCert pre post) : Summary :=
  let fPostGoal : Flag := { label := "post-goal", ok := fc.okPostGoal }
  let fKPost    : Flag := { label := "kPost=length(postCert)", ok := fc.okKPost }
  let fKPreEff  : Flag := { label := "kPreEff=length(preCert?)", ok := fc.okKPreEff }
  mkSummary [fPostGoal, fKPost, fKPreEff]

/--
  Stronger replay check for a frontier entry:
   * Re-run κ(Y|post) at `H` using `actions` and confirm it equals `entry.kPost`.
   * Re-run κ(Y|pre) at `preBound` (default `H+1`) and confirm it equals `entry.kPreEff`
     if found; if not found, confirm that the function returns `none`.
-/
def checkFrontierEntryCertAgainstSearch
  (actions : List AtomicDecl) (H : Nat) (preBound? : Option Nat := none)
  {pre post : Context} (fc : FrontierEntryCert pre post) : Summary :=
  let preBound := preBound?.getD (H + 1)
  let tgt := fc.entry.target
  let postRes := kappaMinForDecl? post tgt actions H
  let preRes  := kappaMinForDecl?  pre tgt actions preBound
  let fPost : Flag :=
    { label := "replay-kPost"
    , ok :=
        match postRes with
        | some (k, _) => k == fc.entry.kPost
        | none => false
    }
  let fPre  : Flag :=
    { label := "replay-kPreEff"
    , ok :=
        match preRes with
        | some (k, _) => k == fc.entry.kPreEff
        | none        => true   -- truncated case is acceptable
    }
  mkSummary [fPost, fPre]

/-! ## Novelty certificate checks -/

/-- Float comparison with small epsilon. -/
@[inline] def approxEq (x y : Float) (eps : Float := 1e-9) : Bool :=
  Float.abs (x - y) ≤ eps

/-- Compare two lists as multisets using a custom equality. -/
def removeFirst [BEq α] (x : α) : List α → Option (List α)
  | []      => none
  | y :: ys => if x == y then some ys else (removeFirst x ys).map (fun zs => y :: zs)

def multisetEq [BEq α] : List α → List α → Bool
  | [], []         => true
  | [], _          => false
  | _ , []         => false
  | x :: xs, ys    =>
      match removeFirst x ys with
      | some ys' => multisetEq xs ys'
      | none     => false

/-- Equality on frontier entries (all fields). -/
@[inline] def frontierEntryEq (a b : FrontierEntry) : Bool :=
  a.target == b.target && a.kPost == b.kPost && a.kPreEff == b.kPreEff

/-- Project entries to a BEq-able view. -/
structure EntryView where
  target  : Target
  kPost   : Nat
  kPreEff : Nat
deriving BEq

@[inline] def toEntryViews (es : List FrontierEntry) : List EntryView :=
  es.map (fun e => { target := e.target, kPost := e.kPost, kPreEff := e.kPreEff })

/-- Basic internal consistency checks for a novelty certificate. -/
def checkNoveltyCertBasic {pre : Context} (nc : NoveltyCert pre) : Summary :=
  let pkgSum := checkPackageCertBasic nc.pkg
  let fNu    : Flag := { label := "nu-sum", ok := (sumFrontierContribs nc.horizon nc.entries == nc.nu) }
  let fRho   : Flag :=
    let denom := if nc.pkg.kappa = 0 then 1 else nc.pkg.kappa
    let rho'  := (Float.ofNat nc.nu) / (Float.ofNat denom)
    { label := "rho=nu/kappa", ok := approxEq nc.rho rho' }
  mkSummary (pkgSum.flags ++ [fNu, fRho])

/--
  Replay novelty with a supplied `ScopeConfig` (actions/enumerators/horizon):
    * Ensure κ_min(X|pre) ≤ pkg.kappa (your stored derivation need not be minimal).
    * Ensure re-built frontier equals stored entries (as a multiset).
    * Ensure ν and ρ match.
-/
def checkNoveltyCertAgainstScope
  {pre : Context} (nc : NoveltyCert pre)
  (scope : ScopeConfig) (maxDepthX : Nat) : Summary :=
  let rep? := noveltyForPackage? pre nc.pkg.targets scope maxDepthX
  match rep? with
  | none =>
      mkSummary [ { label := "replay:report", ok := false } ]
  | some rep =>
      let fKappaLe : Flag :=
        { label := "kappa_min ≤ kappa_cert"
        , ok := rep.kX ≤ nc.pkg.kappa
        }
      let fFrontier : Flag :=
        let eq := multisetEq (toEntryViews rep.frontier) (toEntryViews nc.entries)
        { label := "frontier=stored", ok := eq }
      let fNu : Flag  := { label := "nu=replay",  ok := rep.nu  == nc.nu }
      let fRho : Flag := { label := "rho=replay", ok := approxEq rep.rho nc.rho }
      mkSummary [fKappaLe, fFrontier, fNu, fRho]

/-- Does κ-search find the expected minimal effort for Y under bound H? -/
def checkKappaMinForDecl (B : Context) (Y : AtomicDecl) (actions : List AtomicDecl) (H : Nat) (expect : Nat) : Bool :=
  match kappaMinForDecl? B Y actions H with
  | some (k, _) => k = expect
  | none        => false

end PEN.Cert.Check
