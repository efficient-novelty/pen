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
import PEN.Novelty.Scope
import PEN.Novelty.Enumerators
import PEN.Grammar.HIT
import PEN.Grammar.Classifier
import PEN.Cert.Check

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

/-! ##########################
     Winner / Ledger rows
############################ -/

structure WinnerInfo where
  name : String
  k    : Nat
  nu   : Nat
  rho  : Float
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
  s!"{w.name}[κ={w.k},ν={w.nu},ρ={w.rho}]"

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
    , constructors := [("star","Unit"), ("base0","S1"), ("loop0","S1")]
    , eliminators  := [("rec_Unit","Unit"), ("rec_Pi","Pi"), ("rec_Sigma","Sigma"), ("rec_S1","S1")]
    , compRules    := [("rec_S1","base0"), ("rec_S1","loop0")]
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

/-- S²: point + 2-cell ("surf0"), with recursor and two β-rules. -/
def actionsS2 : List AtomicDecl :=
  [ declareTypeFormer "S2"
  , declareConstructor "base0" "S2"
  , declareConstructor "surf0" "S2"
  , declareEliminator "rec_S2" "S2"
  , declareCompRule "rec_S2" "base0"
  , declareCompRule "rec_S2" "surf0"
  ]

/-- One extra S²-local radius-1 term so ν(S²) = 8. -/
def s2BumpTerms : List AtomicDecl :=
  [ declareTerm "S2.cap" "S2" ]

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
  , declareTypeFormer "Pi"
  , declareEliminator "rec_Pi" "Pi"
  , declareTypeFormer "Sigma"
  , declareEliminator "rec_Sigma" "Sigma"

  , declareTypeFormer "Man"

  /- S¹  (needed so discovery can build S¹ seeds and full bundles at τ=8)
  , declareTypeFormer "S1"
  , declareConstructor "base0" "S1"
  , declareConstructor "loop0" "S1"
  , declareEliminator "rec_S1" "S1"
  , declareCompRule "rec_S1" "base0"
  , declareCompRule "rec_S1" "loop0"
  -/

  ]
  ++ actionsS1                 -- full S¹ package
  ++ actionsS2                 -- S² package
  ++ s2BumpTerms               -- push ν(S²) from 7 to 8
  ++ actionsClassifierMan      -- << Man TF + closure(schema_Man) + eliminator(C∞_Man)
  --  ++ manMapDecls8          -- REMOVE: don't expose Man maps globally


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
          { name := e.pkg.name
          , k    := e.report.kX
          , nu   := e.report.nu
          , rho  := e.report.rho })
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
          { name := nm
          , k    := e.report.kX
          , nu   := e.report.nu
          , rho  := e.report.rho })
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

#eval hasElim "S1" "rec_S1" globalActions           -- expect: true
#eval (elimGoalFor globalActions "S1").isSome       -- expect: true

#eval
  let (_, rows) := runDiscoverNTicksWithLedger dcfg st0 21
  rows.map fmt
#eval manMapDecls8.length   -- expect 8

#eval
  let B := Context.empty
  let acts := [declareUniverse 0, declareTypeFormer "Unit", declareConstructor "star" "Unit"]
  let okU0  := PEN.Cert.Check.checkKappaMinForDecl B (declareUniverse 0) acts 1 1
  let okUnit:= PEN.Cert.Check.checkKappaMinForDecl B (declareTypeFormer "Unit") acts 2 2
  let okStar:= PEN.Cert.Check.checkKappaMinForDecl B (declareConstructor "star" "Unit") acts 3 3
  (okU0 && okUnit && okStar)

end PEN.Genesis
