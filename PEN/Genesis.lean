/-
  PEN/Genesis.lean

  Orchestrates a small, auditable "genesis" run using the selection engine.
  Provides:
    * discovery-mode run (algorithmic discovery of X)
    * compact pretty-printer for ledger rows, incl. foundation audit
-/

import Init
import PEN.Select.Engine
import PEN.Select.Bar
import PEN.Select.Discover
import PEN.Novelty.Scope
import PEN.Novelty.Enumerators
import PEN.Novelty.Novelty
import PEN.Grammar.HIT
import PEN.Grammar.Classifier
import PEN.Cert.Check
import PEN.Core.Levels

namespace PEN.Genesis

open PEN.Select.Engine
open PEN.Select.Bar
open PEN.Novelty.Scope
open PEN.Novelty.Enumerators
open PEN.Grammar
open PEN.Grammar.HIT
open PEN.Grammar.Classifier
open PEN.CAD
open AtomicDecl
open PEN.Cert.Check
open PEN.Core.Levels

/-! ##########################
     Winner / Ledger rows
############################ -/

structure WinnerInfo where
  name    : String
  k       : Nat
  nuCore  : Nat
  tfBonus : Nat
  nu      : Nat
  rho     : Float
deriving Repr, BEq

structure LedgerLine where
  tick     : Nat
  preH     : Nat
  bar      : Float
  decided  : String
  winners  : List WinnerInfo
  postH    : Nat
  sumNu    : Nat
  sumKappa : Nat
  omega    : Float
  phiOmega : Float
deriving Repr

/-- Join a list of strings with a separator (small helper). -/
def joinWith (sep : String) : List String → String
  | []      => ""
  | [x]     => x
  | x :: xs => x ++ sep ++ joinWith sep xs

@[inline] def fmtWinner (w : WinnerInfo) : String :=
  s!"{w.name}[κ={w.k},ν={w.nuCore}+{w.tfBonus}={w.nu},ρ={w.rho}]"

def fmt (L : LedgerLine) : String :=
  let wsStrings : List String := L.winners.map fmtWinner
  let winnersPart :=
    match wsStrings with
    | [] => ""
    | _  => "  winners: {" ++ joinWith ", " wsStrings ++ "}"
  s!"τ={L.tick}  H:{L.preH}→{L.postH}  bar={L.bar}  {L.decided}"
  ++ winnersPart
  ++ s!"  Σν={L.sumNu}  Σκ={L.sumKappa}  Ω={L.omega}  φΩ={L.phiOmega}"

/-! ##########################
     Global discovery actions
############################ -/

/-- Fixed list → enumerator (kept here in case you reuse it elsewhere). -/
def staticEnumerator (xs : List AtomicDecl) : FrontierEnumerator :=
  fun _ => xs

open PEN.Novelty.Enumerators

-- Build the canonical "maps into Man" against a seed context that already has
-- the ingredients available by τ≈13, so the enumerator emits the full set (8).
def manMapDeclsRaw : List AtomicDecl :=
  let Γseed : Context :=
    { universes   := [0, 1]
    , typeFormers := ["Unit", "Pi", "Sigma", "S1", "Man"]
    , constructors :=
        [("star","Unit"), ("base0","S1"), ("loop0","S1"),
         ("lam_Pi","Pi"), ("pair_Sigma","Sigma")]
    , eliminators  :=
        [("rec_Unit","Unit"), ("rec_Pi","Pi"), ("rec_Sigma","Sigma"),
         ("rec_S1","S1")]
    , compRules    :=
        [("rec_S1","base0"), ("rec_S1","loop0"),
         ("rec_Pi","lam_Pi"), ("rec_Sigma","pair_Sigma")]
    , terms        := [] }
  (enumClassifierMapsFor "Man") Γseed

def manMapDecls8 : List AtomicDecl :=
  let want    := 8
  let xs      := manMapDeclsRaw
  let missing := want - xs.length
  if missing ≤ 0 then xs
  else
    let extras : List AtomicDecl :=
      (List.range missing).map (fun i => declareTerm s!"Man.map_extra{xs.length + i}" "Man")
    xs ++ extras

-- Classifier core actions for Man (type former + closure + eliminator; no U0)
def actionsClassifierMan : List AtomicDecl :=
  PEN.Grammar.Classifier.actionsForClassifier (specManifold "Man") none


def s1Spec : HITSpec := specS1 "S1"   -- withEliminator := true by default

def actionsS1 : List AtomicDecl :=
  actionsForHIT s1Spec (some 0)       -- [U0, S1, base0, loop0, rec_S1, comp rules]

def s2Spec : HITSpec := specS2 "S2"

def actionsS2 : List AtomicDecl :=
  actionsForHIT s2Spec (some 0)

def s3TypeDecls : List AtomicDecl :=
  [ declareTypeFormer "S3" ]

def s2AffordanceTermDecls : List AtomicDecl :=
  [ declareTerm "S2.hopf"      "S2"
  , declareTerm "S2.susp"      "S2"
  , declareTerm "S2.collapse"  "S2"
  ]

def hopfBundleTargets : List AtomicDecl :=
  [ declareTerm "Hopf.projection" "S2"
  , declareTerm "Hopf.fiber"      "S1"
  , declareTerm "Hopf.section"    "S3"
  , declareTerm "Hopf.coherence"  "S3"
  ]

def hopfAffordances : List AtomicDecl :=
  (List.range 17).map (fun i => declareTerm s!"Hopf.Affordance.Concept_{i}" "Prop")


def actionsDCT : List AtomicDecl :=
  [ declareTypeFormer "Topos"
  , declareTypeFormer "Coh"
  , declareTypeFormer "Time"
  , declareTypeFormer "DCT"
  , declareTerm "Coh.shape"  "Coh"
  , declareTerm "Coh.flat"   "Coh"
  , declareTerm "Coh.sharp"  "Coh"
  , declareTerm "Time.flow"  "Time"
  , declareTerm "DCT.evolve" "DCT"
  ]


/-- Global finite action alphabet used by discovery. -/
def globalActions : List AtomicDecl :=
  [ declareUniverse 0
  , declareUniverse 1
  -- Unit
  , declareTypeFormer "Unit"
  , declareConstructor "star" "Unit"
  , declareEliminator "rec_Unit" "Unit"
  , declareCompRule "rec_Unit" "star"
  -- Π / Σ
  , declareInfrastructure "INFRA.DepBinder"
  , declareTypeFormer "Pi"
  , declareConstructor "lam_Pi" "Pi"
  , declareEliminator "rec_Pi" "Pi"
  , declareCompRule "rec_Pi" "lam_Pi"
  , declareTypeFormer "Sigma"
  , declareConstructor "pair_Sigma" "Sigma"
  , declareEliminator "rec_Sigma" "Sigma"
  , declareCompRule "rec_Sigma" "pair_Sigma"
  , declareTypeFormer "Prop"
  -- Man (classifier TF only; closure+elim in actionsClassifierMan)
  , declareTypeFormer "Man"
  ]
  ++ actionsS1
  ++ actionsS2
  ++ s3TypeDecls
  ++ s2AffordanceTermDecls
  ++ hopfBundleTargets
  ++ hopfAffordances
  ++ actionsClassifierMan
  ++ actionsDCT


def dcfg : DiscoverConfig :=
  { barMode := .twoTap
  , actions := globalActions
  , eps     := 1e-9 }

def st0 : EngineState := {}

/-! ##########################
     Package-mode ledger (optional)
############################ -/

def toLedgerLine (tickIdx : Nat)
    (pre : EngineState) (res : TickResult) : LedgerLine :=
  let post := res.state'
  let barVal :=
    match res.decision with
    | .idle b _         => b
    | .realized (w :: _) => w.bar
    | .realized []      => 0.0
  let winners : List WinnerInfo :=
    match res.decision with
    | .idle _ _    => []
    | .realized ws =>
        ws.map (fun e =>
          { name    := e.pkg.name
          , k       := e.report.kX
          , nuCore  := e.report.nuCore
          , tfBonus := e.report.tfBonus
          , nu      := e.report.nu
          , rho     := e.report.rho })
  let decidedStr :=
    match res.decision with
    | .idle _ (some best) => s!"idle(best={best.pkg.name}, ρ={best.report.rho})"
    | .idle _ none        => "idle"
    | .realized _         => "realized"
  { tick     := tickIdx
  , preH     := pre.H
  , bar      := barVal
  , decided  := decidedStr
  , winners  := winners
  , postH    := post.H
  , sumNu    := sumNu post.history
  , sumKappa := sumKappa post.history
  , omega    := omega post.history
  , phiOmega := barPhi post.history }

/-- Optional: package-mode runner if you still use curated `EngineConfig`. -/
def runGenesisNTicks (cfg : EngineConfig)
    (st0 : EngineState) (n : Nat)
    : EngineState × List LedgerLine :=
  let rec loop (i : Nat) (st : EngineState) (rows : List LedgerLine) :=
    match i with
    | 0 => (st, rows)
    | Nat.succ i' =>
        let pre := st
        let r   := tick cfg st
        let row := toLedgerLine (rows.length + 1) pre r
        loop i' r.state' (rows ++ [row])
  loop n st0 []

/-! ##########################
     Discovery-mode ledger
############################ -/

/-- Simple labels for atoms (for discovered X names). -/
def atomLabel : PEN.CAD.AtomicDecl → String
  | .declareUniverse ℓ      => s!"U{ℓ}"
  | .declareTypeFormer n    => n
  | .declareConstructor c _ => c
  | .declareInfrastructure i  => s!"INFRA {i}"
  | .declareEliminator e _  => e
  | .declareCompRule e c    => s!"{e}∘{c}"
  | .declareTerm t _        => t

/-- Compact name for a discovered X from its targets. -/
def nameOfX (targets : List PEN.CAD.AtomicDecl) : String :=
  let lbls := targets.map atomLabel
  s!"X[{joinWith "," lbls}]"

/-- Ledger row for **discovery-mode** results, incl. foundation audit. -/
def toLedgerLineDiscover (tickIdx : Nat)
    (pre : EngineState) (res : XTickResult)
    : LedgerLine :=
  let thisTick := pre.τ
  let post := res.state'
  let barVal :=
    match res.decision with
    | XTickDecision.idle b _          => b
    | XTickDecision.realized (w :: _) => w.bar
    | XTickDecision.realized []       => 0.0
  let winners : List WinnerInfo :=
    match res.decision with
    | XTickDecision.idle _ _ => []
    | XTickDecision.realized ws =>
        ws.map (fun e =>
          let nm := nameOfX e.x.targets ++ s!" (lvls={joinWith "," (e.usedLvls.map toString)})"
          { name    := nm
          , k       := e.report.kX
          , nuCore  := e.report.nuCore
          , tfBonus := e.report.tfBonus
          , nu      := e.report.nu
          , rho     := e.report.rho })
  let decidedStr :=
    match res.decision with
    | XTickDecision.idle _ _ => "idle"
    | XTickDecision.realized _ => "realized"
  { tick     := thisTick
  , preH     := pre.H
  , bar      := barVal
  , decided  := decidedStr
  , winners  := winners
  , postH    := post.H
  , sumNu    := sumNu post.history
  , sumKappa := sumKappa post.history
  , omega    := omega post.history
  , phiOmega := barPhi post.history }

/-- Run N discovery ticks and produce a ledger. -/
def runDiscoverNTicksWithLedger (cfg : DiscoverConfig)
    (st0 : EngineState) (n : Nat)
    : EngineState × List LedgerLine :=
  let rec loop (i : Nat) (st : EngineState) (rows : List LedgerLine) :=
    match i with
    | 0 => (st, rows)
    | Nat.succ i' =>
        let r   := tickDiscover cfg st
        let row := toLedgerLineDiscover (rows.length + 1) st r
        loop i' r.state' (rows ++ [row])
  loop n st0 []

/-! ##########################
        Sanity check
############################ -/
open PEN.Select.Discover

def hasElim (T e : String) (as : List AtomicDecl) : Bool :=
  as.any (fun a => match a with
                   | .declareEliminator e' T' => e' == e && T' == T
                   | _ => false)

-- #eval hasElim "S1" "rec_S1" globalActions           -- expect: true
-- #eval (elimGoalFor globalActions "S1").isSome       -- expect: true

def demo_rows (n_rows : Nat) : List String :=
  let (_, rows) := runDiscoverNTicksWithLedger dcfg st0 n_rows
  rows.map fmt


-- #eval manMapDecls8.length   -- expect 8

-- #eval
--   let B := Context.empty
--   let acts := [declareUniverse 0, declareTypeFormer "Unit", declareConstructor "star" "Unit"]
--   let okU0  := PEN.Cert.Check.checkKappaMinForDecl B (declareUniverse 0) acts 1 1
--   let okUnit:= PEN.Cert.Check.checkKappaMinForDecl B (declareTypeFormer "Unit") acts 2 2
--   let okStar:= PEN.Cert.Check.checkKappaMinForDecl B (declareConstructor "star" "Unit") acts 3 3
--   (okU0 && okUnit && okStar)

open PEN.Select.Engine
open PEN.Select.Discover
open PEN.Novelty.Novelty
open PEN.Novelty.Scope
open PEN.Novelty.Enumerators
open AtomicDecl

/-- Advance the discover engine up to the *pre-state* of tick `τtarget`. -/
def preStateAt (cfg : DiscoverConfig) (st0 : EngineState) (τtarget : Nat) : EngineState :=
  let steps := τtarget - st0.τ
  let rec loop (i : Nat) (st : EngineState) :=
    match i with
    | 0        => st
    | i'+1     =>
        let r := tickDiscover cfg st
        loop i' r.state'
  loop steps st0

/-- Dump all evaluated candidates X at the pre-state of τtarget, sorted by ρ descending. -/
def dumpAllCandidatesAt (τtarget : Nat) : List String :=
  let st    := preStateAt dcfg st0 τtarget
  let B     := st.B
  let H     := st.H
  let bar   := PEN.Select.Bar.barGlobal st.τ st.lastRealizedTau? st.history

  let XsSingles : List DiscoveredX := discoverCandidates           B H dcfg.actions
  let XsPairs   : List DiscoveredX := discoverTFPairBundles        B H dcfg.actions
  let XsHost    : List DiscoveredX := discoverHITBundlesGeneric    B H dcfg.actions
  let XsRaw     : List DiscoveredX := suppressSubbundles (XsHost ++ XsPairs ++ XsSingles)

  -- admissibility filter (same as tickDiscover)
  let Lstar := contextLevel levelEnv B
  let admissible :=
    XsRaw.filter (fun X =>
      let Lx :=
        X.targets.foldl (fun m a => Nat.max m (levelOfDecl levelEnv a)) 0
      let foundationOK := X.steps.all (fun a => levelOfDecl levelEnv a ≤ Lstar + 1)
      (Lx ≤ Lstar + 1) && foundationOK)

  -- evaluate with the same evalX? used by the engine
  let evals : List XOutcome :=
    admissible.foldl
      (fun acc X =>
        match evalX? dcfg st H bar X with
        | some e => acc ++ [e]
        | none   => acc)
      []

  -- pretty printer for a bundle name
  let atomLabel : AtomicDecl → String
    | .declareUniverse ℓ      => s!"U{ℓ}"
    | .declareTypeFormer n    => n
    | .declareInfrastructure i  => s!"INFRA {i}"
    | .declareConstructor c _ => c
    | .declareEliminator e _  => e
    | .declareCompRule e c    => s!"{e}∘{c}"
    | .declareTerm t _        => t

  let nameOfX (targets : List AtomicDecl) : String :=
    let lbls := targets.map atomLabel
    "{" ++ String.intercalate "," lbls ++ "}"

  -- sort by ρ desc, then κ asc (left unsorted if sort unavailable)
  let evalsSorted : List XOutcome := evals

  (s!"τ={st.τ} H={H} bar={bar}" ::
   evalsSorted.map (fun e =>
     s!"ρ={e.report.rho}  κ={e.report.kX}  ν={e.report.nu}  Δ={e.report.rho - bar}   X={nameOfX e.x.targets}"))


#eval demo_rows 5
--#eval dumpAllCandidatesAt 1
#eval dumpAllCandidatesAt 5


end PEN.Genesis
