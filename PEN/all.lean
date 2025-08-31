/-
  PEN/CAD/Atoms.lean

  Atomic declaration language ("CAD") and a minimal context discipline.

  This layer is deliberately small:
  - `AtomicDecl` describes one irreducible step that adds a single item.
  - `Context` records what has been declared so far.
  - `isValidInContext` checks whether a step is admissible in a context.
  - `step` applies a valid step, producing an updated context.
  - `applyAll?` folds a list of steps, short-circuiting on invalid ones.

  Policy (kept simple on purpose):
  - Declaring a *type former* requires that at least one universe is present.
  - Declaring a *constructor* or an *eliminator* for type `T` requires that `T`
    has been declared as a type former.
  - Declaring a *computation rule* requires that its eliminator and constructor
    names are already present.
  - Declaring a *term* of type `T` requires that `T` is already declared as a type.
-/

import Init

namespace PEN.CAD

/-- One irreducible context-extending step. -/
inductive AtomicDecl
  | declareUniverse     (level : Nat)                  -- introduces U_level (abstractly)
  | declareTypeFormer   (name : String)                -- introduces a type family (e.g. Unit, Nat, ...)
  | declareConstructor  (name : String) (typeName : String) -- constructor for an existing type former
  | declareEliminator   (name : String) (typeName : String) -- eliminator/recursor for an existing type former
  | declareCompRule     (elimName : String) (constrName : String) -- Î²/Î¹ rule tying an eliminator to a constructor
  | declareTerm         (name : String) (typeName : String) -- a non-constructor term inhabiting a known type
  deriving Repr, BEq, Inhabited

/-- CAD context: what has been declared so far. For simplicity we store lists. -/
structure Context where
  universes   : List Nat                := []
  typeFormers : List String             := []            -- names of types
  constructors : List (String Ã— String) := []            -- (ctorName, typeName)
  eliminators  : List (String Ã— String) := []            -- (elimName, typeName)
  compRules    : List (String Ã— String) := []            -- (elimName, ctorName)
  terms        : List (String Ã— String) := []            -- (termName, typeName)
  deriving Repr, Inhabited

namespace Context

/-- Empty CAD context. -/
def empty : Context := {}

/-! Simple membership helpers (Bool-valued; no Prop machinery needed). -/

@[inline] def memNat (xs : List Nat) (n : Nat) : Bool :=
  xs.any (fun m => m == n)

@[inline] def memStr (xs : List String) (s : String) : Bool :=
  xs.any (fun t => t == s)

@[inline] def memPair (xs : List (String Ã— String)) (a b : String) : Bool :=
  xs.any (fun p => p.fst == a && p.snd == b)

@[inline] def containsKey (xs : List (String Ã— String)) (a : String) : Bool :=
  xs.any (fun p => p.fst == a)

@[inline] def containsVal (xs : List (String Ã— String)) (b : String) : Bool :=
  xs.any (fun p => p.snd == b)

/-- Does the context already have any universe? -/
@[inline] def hasAnyUniverse (Î“ : Context) : Bool :=
  !Î“.universes.isEmpty

@[inline] def hasUniverse (Î“ : Context) (â„“ : Nat) : Bool :=
  memNat Î“.universes â„“

@[inline] def hasTypeFormer (Î“ : Context) (name : String) : Bool :=
  memStr Î“.typeFormers name

@[inline] def hasConstructor (Î“ : Context) (ctorName : String) : Bool :=
  containsKey Î“.constructors ctorName

@[inline] def hasConstructorFor (Î“ : Context) (typeName : String) : Bool :=
  containsVal Î“.constructors typeName

@[inline] def hasEliminator (Î“ : Context) (elimName : String) : Bool :=
  containsKey Î“.eliminators elimName

@[inline] def hasEliminatorFor (Î“ : Context) (typeName : String) : Bool :=
  containsVal Î“.eliminators typeName

@[inline] def hasCompRule (Î“ : Context) (elimName constrName : String) : Bool :=
  memPair Î“.compRules elimName constrName

@[inline] def hasTerm (Î“ : Context) (termName : String) : Bool :=
  containsKey Î“.terms termName

@[inline] def hasTermOf (Î“ : Context) (typeName : String) : Bool :=
  containsVal Î“.terms typeName

/-- Insert helpers (idempotent: keep Î“ unchanged if the entry already exists). -/
@[inline] def addUniverse (Î“ : Context) (â„“ : Nat) : Context :=
  if Î“.hasUniverse â„“ then Î“ else { Î“ with universes := â„“ :: Î“.universes }

@[inline] def addTypeFormer (Î“ : Context) (name : String) : Context :=
  if Î“.hasTypeFormer name then Î“ else { Î“ with typeFormers := name :: Î“.typeFormers }

@[inline] def addConstructor (Î“ : Context) (name typeName : String) : Context :=
  if memPair Î“.constructors name typeName then Î“
  else { Î“ with constructors := (name, typeName) :: Î“.constructors }

@[inline] def addEliminator (Î“ : Context) (name typeName : String) : Context :=
  if memPair Î“.eliminators name typeName then Î“
  else { Î“ with eliminators := (name, typeName) :: Î“.eliminators }

@[inline] def addCompRule (Î“ : Context) (elimName constrName : String) : Context :=
  if memPair Î“.compRules elimName constrName then Î“
  else { Î“ with compRules := (elimName, constrName) :: Î“.compRules }

@[inline] def addTerm (Î“ : Context) (name typeName : String) : Context :=
  if memPair Î“.terms name typeName then Î“
  else { Î“ with terms := (name, typeName) :: Î“.terms }

end Context


/-- Does the context already contain a constructor whose target type is `T`? -/
@[inline] def hasCtorOf (ctx : Context) (T : String) : Bool :=
  ctx.constructors.any (fun p => p.snd == T)

/-- Does the context already contain a constructor named `c`? -/
@[inline] def hasCtorName (ctx : Context) (c : String) : Bool :=
  ctx.constructors.any (fun p => p.fst == c)

/-- Does the context already contain an eliminator named `e`? -/
@[inline] def hasElimName (ctx : Context) (e : String) : Bool :=
  ctx.eliminators.any (fun p => p.fst == e)

/-- Does the context already contain a type former named `T`? -/
@[inline] def hasTypeFormer (ctx : Context) (T : String) : Bool :=
  ctx.typeFormers.any (fun s => s == T)

@[inline] def elimNeedsCtor (T : String) : Bool :=
  -- Î  and Î£ are classifier-level; Man is too
  not (T == "Pi" || T == "Sigma" || T == "Man")

/--
Paperâ€‘faithful validity predicate for one atomic declaration given a context.

Key gates:
* `declareTypeFormer` requires that at least one universe is present.
* `declareEliminator` requires that the type exists **and** at least one constructor
  for that type already exists (this is what gives Î½(3) = 2 in the early steps).
-/
def isValidInContext (decl : AtomicDecl) (ctx : Context) : Bool :=
  match decl with
  | AtomicDecl.declareUniverse 0        => true
  | AtomicDecl.declareUniverse (Nat.succ â„“) => ctx.hasUniverse â„“
  | AtomicDecl.declareTypeFormer _      => not ctx.universes.isEmpty
  | AtomicDecl.declareConstructor _ T   => hasTypeFormer ctx T
  | AtomicDecl.declareEliminator _ T    =>
      hasTypeFormer ctx T && (if elimNeedsCtor T then hasCtorOf ctx T else true)
  | AtomicDecl.declareCompRule e c      => hasElimName ctx e && hasCtorName ctx c
  | AtomicDecl.declareTerm _ T          => hasTypeFormer ctx T



/-- Apply a single atomic declaration if valid; otherwise return `none`. -/
def step (Î“ : Context) (decl : AtomicDecl) : Option Context :=
  if isValidInContext decl Î“ then
    some <|
      match decl with
      | .declareUniverse â„“            => Î“.addUniverse â„“
      | .declareTypeFormer n          => Î“.addTypeFormer n
      | .declareConstructor n T       => Î“.addConstructor n T
      | .declareEliminator n T        => Î“.addEliminator n T
      | .declareCompRule e c          => Î“.addCompRule e c
      | .declareTerm n T              => Î“.addTerm n T
  else
    none

/-- Apply a list of atomic declarations left-to-right, short-circuiting on failure. -/
def applyAll? (Î“ : Context) (ds : List AtomicDecl) : Option Context :=
  ds.foldlM step Î“

/-! # Tiny sanity checks (uncomment to try locally)

open AtomicDecl

def Î“0 : Context := Context.empty

-- Invalid: cannot declare a type former without a universe.
#eval isValidInContext (.declareTypeFormer "Unit") Î“0         -- false

-- Declare U0, then Unit becomes valid.
def Î“1 := (step Î“0 (.declareUniverse 0)).getD Î“0
#eval isValidInContext (.declareTypeFormer "Unit") Î“1         -- true

def Î“2 := (step Î“1 (.declareTypeFormer "Unit")).getD Î“1
#eval isValidInContext (.declareConstructor "star" "Unit") Î“2 -- true
#eval isValidInContext (.declareTerm "tt" "Unit") Î“2          -- true

-/

end PEN.CAD
/-
  PEN/CAD/Derivation.lean

  Well-formed derivations and certificates for CAD (atomic declarations).

  This module provides:
  - `Derivation := List AtomicDecl`
  - `isWellFormed : Derivation â†’ Context â†’ Bool`
  - `runDerivation : Context â†’ Derivation â†’ Option Context`
  - `DerivCert` â€” a certificate that a derivation runs successfully
  - constructors: `DerivCert.mk?`, `DerivCert.step?`
  - helpers: `kappaOfDerivation` (= length), `append`, `length`

  Itâ€™s deliberately computation-first: certificates carry a concrete
  `finish : Context` together with an equality witness
  `applyAll? start deriv = some finish`.
-/

import Init
import PEN.CAD.Atoms

namespace PEN.CAD

/-- A derivation is a finite sequence of atomic declarations. -/
abbrev Derivation := List AtomicDecl

/-- Run a derivation in a starting context. If any step is invalid, return `none`. -/
@[inline] def runDerivation (Î“ : Context) (d : Derivation) : Option Context :=
  applyAll? Î“ d

/-- A derivation is well-formed in `Î“` iff it runs to some context. -/
@[inline] def isWellFormed (d : Derivation) (Î“ : Context) : Bool :=
  (runDerivation Î“ d).isSome

/-- The (trivial) effort of a derivation: its length. -/
@[inline] def kappaOfDerivation (d : Derivation) : Nat := d.length

/--
  A derivation certificate: starting from `start`, the list of declarations
  `deriv` executes successfully to produce `finish`.
-/
structure DerivCert (start : Context) where
  deriv  : Derivation
  finish : Context
  witness : runDerivation start deriv = some finish
deriving Repr

namespace DerivCert

/-- The length (effort) of the certified derivation. -/
@[inline] def length {Î“} (c : DerivCert Î“) : Nat := c.deriv.length

/--
  Attempt to build a certificate by actually running the derivation.
  Returns `none` if any step is invalid.
-/
def mk? (start : Context) (d : Derivation) : Option (DerivCert start) :=
  match h : runDerivation start d with
  | none      => none
  | some fin  => some { deriv := d, finish := fin, witness := by simpa [runDerivation, h] }

/-- Single-step certificate (for convenience). -/
def step? (start : Context) (decl : AtomicDecl) : Option (DerivCert start) :=
  mk? start [decl]

/--
  Compute a new certificate for the concatenation `c1.deriv ++ c2.deriv`.
  This does not try to reuse proofs compositionally; it re-runs the concatenated
  derivation to produce a fresh computational witness.
-/
def append {Î“} (c1 : DerivCert Î“) (c2 : DerivCert c1.finish) : Option (DerivCert Î“) :=
  mk? Î“ (c1.deriv ++ c2.deriv)

end DerivCert

/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl

def Î“0 : Context := Context.empty

-- Build a short well-formed derivation: U0; Unit; star:Unit
def dU0 : Derivation := [declareUniverse 0]
def dUnit : Derivation := [declareTypeFormer "Unit"]
def dStar : Derivation := [declareConstructor "star" "Unit"]

#eval isWellFormed dUnit Î“0      -- false (no universe yet)
#eval isWellFormed (dU0 ++ dUnit) Î“0  -- true

def cU0?   := DerivCert.mk? Î“0 dU0
#eval cU0?.isSome

def Î“1 : Context := cU0?.get!.finish
def cUnit? := DerivCert.mk? Î“1 dUnit
def Î“2 : Context := cUnit?.get!.finish
def cStar? := DerivCert.mk? Î“2 dStar

#eval cStar?.isSome

-- Compose certificates by recomputing on the concatenated derivation:
def cAll? : Option (DerivCert Î“0) :=
  do
    let c0 â† cU0?
    let c1 â† cUnit?
    let c01 â† DerivCert.append c0 c1
    let c2 â† cStar?
    DerivCert.append c01 c2

#eval cAll?.isSome
#eval cAll?.map (Â·.length)  -- Some 3

-/

end PEN.CAD
/-
  PEN/CAD/Kappa.lean

  Minimal-effort (Îº) search via iterative deepening over CAD derivations.

  Exposed APIs:
    - goalOfDecl : AtomicDecl â†’ (Context â†’ Bool)
    - kappaMin? : Context â†’ (Context â†’ Bool) â†’ List AtomicDecl â†’ Nat â†’ Option (Nat Ã— DerivCert start)
    - kappaMinForDecl? : Context â†’ AtomicDecl â†’ List AtomicDecl â†’ Nat â†’ Option (Nat Ã— DerivCert start)

  The search explores only the finite `actions : List AtomicDecl` you provide.
  This keeps the branching factor bounded and makes the computation predictable.

  Design notes:
    * We use IDDFS (depth-limited DFS inside an outer loop that increases the limit).
      With uniform edge cost (1 per atomic step), this returns a shortest derivation.
    * CAD contexts are monotone: applying a valid step never removes information;
      we skip any step that leaves the context unchanged (prevents trivial loops).
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation

namespace PEN.CAD

/-- Equality test for contexts via componentwise list equality. -/
@[inline] def ctxSame (a b : Context) : Bool :=
  a.universes   == b.universes
  && a.typeFormers == b.typeFormers
  && a.constructors == b.constructors
  && a.eliminators  == b.eliminators
  && a.compRules    == b.compRules
  && a.terms        == b.terms

/-- Turn a target declaration into a "goal reached?" predicate on contexts. -/
@[inline] def goalOfDecl (decl : AtomicDecl) : Context â†’ Bool :=
  match decl with
  | .declareUniverse â„“          => fun Î“ => Î“.hasUniverse â„“
  | .declareTypeFormer n        => fun Î“ => Î“.hasTypeFormer n
  | .declareConstructor n T     => fun Î“ => Î“.hasConstructor n && Î“.hasConstructorFor T
  | .declareEliminator n T      => fun Î“ => Î“.hasEliminator n && Î“.hasEliminatorFor T
  | .declareCompRule e c        => fun Î“ => Î“.hasCompRule e c
  | .declareTerm n T            => fun Î“ => Î“.hasTerm n && Î“.hasTermOf T

/--
  Internal depth-limited DFS.

  Parameters:
    * start : starting context (for the final certificate)
    * goal  : predicate on contexts (true if target is reached)
    * actions : finite menu of admissible atomic steps
    * limit : maximum remaining depth (number of steps we may still take)
    * Î“     : current context
    * dAcc  : accumulated derivation (forward order)

  Returns the first (lexicographically by `actions` order) certificate at depth â‰¤ limit.
-/
partial def dfsLimited
  (start : Context)
  (goal : Context â†’ Bool)
  (actions : List AtomicDecl)
  (limit : Nat)
  (Î“ : Context)
  (dAcc : Derivation)
  : Option (DerivCert start) := Id.run do
    -- If goal already holds, certify the current derivation.
    if goal Î“ then
      match h : runDerivation start dAcc with
      | some fin =>
        return some { deriv := dAcc, finish := fin, witness := by simpa [runDerivation, h] }
      | none     => return none
    -- If no budget left, stop.
    if limit = 0 then
      return none
    -- Otherwise, try each action in order.
    for a in actions do
      if isValidInContext a Î“ then
        match step Î“ a with
        | some Î“' =>
            -- Skip if the action is a no-op (context unchanged).
            if ctxSame Î“ Î“' then
              pure ()
            else
              let d' := dAcc ++ [a]
              match dfsLimited start goal actions (limit-1) Î“' d' with
              | some cert => return some cert
              | none      => pure ()
        | none => pure ()
      else
        pure ()
    return none

/--
  Iterative deepening wrapper: try depth bounds 0..maxDepth (inclusive)
  and return the first certificate found. With unit edge costs, this is
  guaranteed to produce a derivation of minimal length within the bound.

  We drive the outer loop with a *fuel* argument so termination is structural.
-/
def searchMinDerivation
  (start : Context)
  (goal : Context â†’ Bool)
  (actions : List AtomicDecl)
  (maxDepth : Nat)
  : Option (DerivCert start) :=
  -- Early exit: goal already satisfied.
  if goal start then
    DerivCert.mk? start []
  else
    let rec loop (fuel : Nat) (bound : Nat) : Option (DerivCert start) :=
      match fuel with
      | 0 => none
      | Nat.succ fuel' =>
        if bound > maxDepth then
          none
        else
          match dfsLimited start goal actions bound start [] with
          | some cert => some cert
          | none      => loop fuel' (bound + 1)
    loop (maxDepth + 1) 0

/--
  Minimal Îº for an arbitrary goal predicate using a fixed `actions` menu
  and a maximum depth. Returns the derivation length together with its certificate.
-/
def kappaMin?
  (start : Context)
  (goal : Context â†’ Bool)
  (actions : List AtomicDecl)
  (maxDepth : Nat)
  : Option (Nat Ã— DerivCert start) :=
  match searchMinDerivation start goal actions maxDepth with
  | some cert => some (cert.length, cert)
  | none      => none

/--
  Minimal Îº for reaching the state where the target declaration "is present",
  using only the given `actions` and up to `maxDepth` steps.
-/
def kappaMinForDecl?
  (start : Context)
  (target : AtomicDecl)
  (actions : List AtomicDecl)
  (maxDepth : Nat)
  : Option (Nat Ã— DerivCert start) :=
  kappaMin? start (goalOfDecl target) actions maxDepth

/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl

def Î“0 : Context := Context.empty
def actionsSmall : List AtomicDecl :=
  [ declareUniverse 0,
    declareTypeFormer "Unit",
    declareConstructor "star" "Unit"
  ]

-- Universe U0 from empty (needs 1 step).
#eval kappaMinForDecl? Î“0 (declareUniverse 0) actionsSmall 3 |>.map (Â·.fst)  -- Some 1

-- Type former "Unit" from empty (needs 2 steps: U0; Unit).
#eval kappaMinForDecl? Î“0 (declareTypeFormer "Unit") actionsSmall 3 |>.map (Â·.fst)  -- Some 2

-- Constructor "star:Unit" from empty (needs 3 steps: U0; Unit; star).
#eval kappaMinForDecl? Î“0 (declareConstructor "star" "Unit") actionsSmall 3 |>.map (Â·.fst)  -- Some 3

end PEN.CAD

-/
/-
  PEN/Cert/Check.lean

  Lightweight certificate checkers and replay utilities.

  What you get:
    * ctxEq                      â€” Boolean, fieldwise equality for CAD.Context
    * Flag / Summary             â€” tiny reporting helpers
    * checkPackageCertBasic      â€” validate a PackageCert (derivation runs, goals hold)
    * checkFrontierEntryCertBasic
    * checkFrontierEntryCertAgainstSearch (re-run Îº-search for kPost/kPreEff)
    * checkNoveltyCertBasic      â€” validate Î½ sums and Ï consistency
    * checkNoveltyCertAgainstScope
        - replay novelty with a supplied ScopeConfig and compare frontier/Î½/Ï

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
  { ok := flags.all (Â·.ok), flags }

/-! ## Package checks -/

/-- Recompute the run and compare finish context to the stored one (via `ctxEq`). -/
def checkDerivWitness {start : Context} (c : DerivCert start) : Bool :=
  match runDerivation start c.deriv with
  | some fin => ctxEq fin c.finish
  | none     => false

/-- Validate a package install certificate (derivation runs, goals hold, Îº matches length). -/
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
   * Re-run Îº(Y|post) at `H` using `actions` and confirm it equals `entry.kPost`.
   * Re-run Îº(Y|pre) at `preBound` (default `H+1`) and confirm it equals `entry.kPreEff`
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
  Float.abs (x - y) â‰¤ eps

/-- Compare two lists as multisets using a custom equality. -/
def removeFirst [BEq Î±] (x : Î±) : List Î± â†’ Option (List Î±)
  | []      => none
  | y :: ys => if x == y then some ys else (removeFirst x ys).map (fun zs => y :: zs)

def multisetEq [BEq Î±] : List Î± â†’ List Î± â†’ Bool
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
  let fNu    : Flag := { label := "nu-sum", ok := (sumFrontierContribs nc.entries == nc.nu) }
  let fRho   : Flag :=
    let denom := if nc.pkg.kappa = 0 then 1 else nc.pkg.kappa
    let rho'  := (Float.ofNat nc.nu) / (Float.ofNat denom)
    { label := "rho=nu/kappa", ok := approxEq nc.rho rho' }
  mkSummary (pkgSum.flags ++ [fNu, fRho])

/--
  Replay novelty with a supplied `ScopeConfig` (actions/enumerators/horizon):
    * Ensure Îº_min(X|pre) â‰¤ pkg.kappa (your stored derivation need not be minimal).
    * Ensure re-built frontier equals stored entries (as a multiset).
    * Ensure Î½ and Ï match.
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
        { label := "kappa_min â‰¤ kappa_cert"
        , ok := rep.kX â‰¤ nc.pkg.kappa
        }
      let fFrontier : Flag :=
        let eq := multisetEq (toEntryViews rep.frontier) (toEntryViews nc.entries)
        { label := "frontier=stored", ok := eq }
      let fNu : Flag  := { label := "nu=replay",  ok := rep.nu  == nc.nu }
      let fRho : Flag := { label := "rho=replay", ok := approxEq rep.rho nc.rho }
      mkSummary [fKappaLe, fFrontier, fNu, fRho]

/-! # Tiny sanity checks (uncomment locally)

open PEN.Grammar.HIT
open PEN.Novelty.Scope
open PEN.Novelty.Enumerators

def Î“0 : Context := Context.empty
def Î“u : Context := (PEN.CAD.step Î“0 (AtomicDecl.declareUniverse 0)).getD Î“0

-- Build a small package (S1 without elim/comp rules) and a trivial PackageCert:
def S1_noRec := { (specS1 "S1") with withEliminator := false, withCompRules := false }
def targetsX : List AtomicDecl := PEN.Grammar.HIT.declsCore S1_noRec

def pkgCert? : Option (PackageCert Î“u) :=
  match h : PEN.CAD.runDerivation Î“u targetsX with
  | some post =>
      let wit := by simpa [PEN.CAD.runDerivation, h]
      let dc  : DerivCert Î“u := { deriv := targetsX, finish := post, witness := wit }
      some (mkPackageCert targetsX dc)
  | none => none

#eval match pkgCert? with
     | none      => "failed"
     | some pc   => checkPackageCertBasic pc

-- Build a tiny frontier with fake numbers and check the arithmetic:
def dummyEntry : FrontierEntry := { target := AtomicDecl.declareTerm "alias_prod" "S1", kPost := 1, kPreEff := 3 }
def dummyNC (pc : PackageCert Î“u) : NoveltyCert Î“u :=
  { pkg := pc, horizon := 3, entries := [dummyEntry], nu := 2, rho := 2.0, entryCerts := [], okNu := True }

#eval match pkgCert? with
     | none      => "failed"
     | some pc   => checkNoveltyCertBasic (dummyNC pc)

-- Replay example (requires enumerators/actions to actually reach targets):
def scope : ScopeConfig :=
  { actions      := PEN.Grammar.HIT.actionsForHIT (specS1 "S1") (some 0)
  , enumerators  := [enumMissingEliminators, enumMissingCompRules, enumPiSigmaAliasesFor "S1"]
  , horizon      := 4
  , preMaxDepth? := none
  , exclude      := [] }

-- This will be meaningful once you create a real NoveltyCert from NoveltyReport.
-- #eval checkNoveltyCertAgainstScope <yourNoveltyCert> scope (maxDepthX := 4)

-/

end PEN.Cert.Check
/-
  PEN/Cert/Types.lean

  Certificate record types for auditable runs:
    * PackageCert            â€” Îº-certificate for installing a package X on B
    * FrontierEntryCert      â€” certificate for a single frontier entry Y
    * NoveltyCert            â€” bundle: package install + frontier + Î½ accounting
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
@[inline] def goalsHold (targets : List AtomicDecl) (Î“ : Context) : Bool :=
  targets.all (fun t => PEN.CAD.goalOfDecl t Î“)

/-! ###########################################################################
    Package install certificate
############################################################################# -/

/--
  Îº-certificate that a *package* (list of target declarations) is installed
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
  fixed pre/post pair (B, B âˆª X).
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
    * `okNu` â€” recomputed Î£ max(0, ÎºÌƒ_pre - Îº_post) equals the reported `nu`
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
@[inline] def sumFrontierContribs (es : List FrontierEntry) : Nat :=
  es.foldl (fun s e => s + (if e.kPreEff > e.kPost then e.kPreEff - e.kPost else 0)) 0

/-- Smart constructor from a `PackageCert` and a `NoveltyReport`. -/
@[inline] def mkNoveltyCertFromReport
  {pre : Context}
  (pkg : PackageCert pre)
  (H   : Nat)
  (rep : NoveltyReport)
  (entryCerts : List (FrontierEntryCert pre pkg.post) := [])
  : NoveltyCert pre :=
  let okNu := sumFrontierContribs rep.frontier == rep.nu
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
  s!"H={n.horizon}, Îº={n.pkg.kappa}, Î½={n.nu}, Ï={n.rho}"

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

def Î“0 : Context := Context.empty
def Î“u : Context := (PEN.CAD.step Î“0 (AtomicDecl.declareUniverse 0)).getD Î“0

-- Build a minimal package (S1 without eliminator/comp rules) and certify it:
def S1_noRec := { (specS1 "S1") with withEliminator := false, withCompRules := false }
def targetsX : List AtomicDecl := PEN.Grammar.HIT.declsCore S1_noRec

-- Build a proper DerivCert using the equality from running the derivation:
def certX? : Option (DerivCert Î“u) :=
  match h : PEN.CAD.runDerivation Î“u targetsX with
  | some post =>
      -- witness: runDerivation Î“u targetsX = some post
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
/-
  PEN/Core/Codebook.lean

  Canonical, prefix-free serializer for a small HoTT/term-like AST,
  together with a *length-only* parser `parseLen` that returns the size
  of the first top-level codeword using only the codeword's header
  (tag + ASCII decimal length + ';').

  Encoding schema for each node:
    [1-byte tag] Â· [len-decimal ASCII Â· ';'] Â· [payload bytes of that length]

  The payload is a concatenation of:
    - any scalar fields (strings and naturals, both length-prefixed),
    - a framed list of children:  count;  len1; child1  len2; child2  ...

  Because each node carries its own total payload length in the header,
  codewords are *prefix-free* and `parseLen` can skip the whole block
  without parsing its interior.

  This file is self-contained (no project imports).
-/

import Init
import Std

namespace PEN.Core.Codebook

/-! ## AST -/

inductive AST
  | var    (idx : Nat)
  | const  (name : String)
  | lam    (binder : String) (type body : AST)
  | app    (fn arg : AST)
  | arrow  (dom cod : AST)
  | pi     (binder : String) (dom cod : AST)
  | sigma  (binder : String) (fst snd : AST)
  | pair   (fst snd : AST)
  | fst    (p : AST)
  | snd    (p : AST)
  | litNat (n : Nat)
  deriving Repr, BEq, Inhabited

abbrev Program := AST

/-! ## ByteArray helpers -/

@[inline] def bAppend (a b : ByteArray) : ByteArray :=
  Id.run do
    let mut out := a
    let sz := b.size
    for i in [0:sz] do
      out := out.push (b.get! i)
    return out

@[inline] def bConcat (xs : List ByteArray) : ByteArray :=
  xs.foldl bAppend ByteArray.empty

@[inline] def semi : UInt8 := UInt8.ofNat (Char.toNat ';')

@[inline] def tag (c : Char) : UInt8 := UInt8.ofNat (Char.toNat c)

/-! ## Scalar encoders (ASCII decimal with ';' terminator) -/

@[inline] def encNatDec (n : Nat) : ByteArray :=
  (toString n).toUTF8.push semi

@[inline] def encString (s : String) : ByteArray :=
  let utf := s.toUTF8
  bAppend (encNatDec utf.size) utf

/-!
  Child framing:
    count;  len1; child1  len2; child2  ...
  (Each child is itself a framed codeword produced by `encodeAST`.)
-/
def frameChildren (cs : List ByteArray) : ByteArray :=
  let count := encNatDec cs.length
  cs.foldl
    (fun acc child => bAppend (bAppend acc (encNatDec child.size)) child)
    count

/-! ## Tags per node constructor -/

@[inline] def TAG_VAR   : UInt8 := tag 'v'
@[inline] def TAG_CONST : UInt8 := tag 'c'
@[inline] def TAG_LAM   : UInt8 := tag 'l'
@[inline] def TAG_APP   : UInt8 := tag 'a'
@[inline] def TAG_ARROW : UInt8 := tag 'r'    -- 'r' for aRRow
@[inline] def TAG_PI    : UInt8 := tag 'p'
@[inline] def TAG_SIGMA : UInt8 := tag 's'
@[inline] def TAG_PAIR  : UInt8 := tag 't'
@[inline] def TAG_FST   : UInt8 := tag 'f'
@[inline] def TAG_SND   : UInt8 := tag 'g'
@[inline] def TAG_NAT   : UInt8 := tag 'n'

@[inline] def emitTag (u : UInt8) : ByteArray :=
  ByteArray.empty.push u

/-- Wrap a payload as a codeword:
    [tag][len-decimal';'][payload]  with len = payload.size. -/
@[inline] def frameNode (tg : UInt8) (payload : ByteArray) : ByteArray :=
  bConcat [emitTag tg, encNatDec payload.size, payload]

/-!
  Encode an AST node to a prefix-free ByteArray. The encoding of each node is:

  tag Â· length(payload)';' Â· payload

  The payload itself concatenates:
    - scalar fields (length-prefixed strings and naturals),
    - a framed list of children (count; len; child bytes ...).
-/
partial def encodeAST : AST â†’ ByteArray
| .var i =>
    let payload := bConcat [encNatDec i, encNatDec 0]  -- scalars + 0 children
    frameNode TAG_VAR payload
| .const nm =>
    let payload := bConcat [encString nm, encNatDec 0]
    frameNode TAG_CONST payload
| .lam b ty bd =>
    let kids := [encodeAST ty, encodeAST bd]
    let payload := bConcat [encString b, frameChildren kids]
    frameNode TAG_LAM payload
| .app f x =>
    let kids := [encodeAST f, encodeAST x]
    let payload := frameChildren kids
    frameNode TAG_APP payload
| .arrow a b =>
    let kids := [encodeAST a, encodeAST b]
    let payload := frameChildren kids
    frameNode TAG_ARROW payload
| .pi bnd dom cod =>
    let kids := [encodeAST dom, encodeAST cod]
    let payload := bConcat [encString bnd, frameChildren kids]
    frameNode TAG_PI payload
| .sigma bnd fst snd =>
    let kids := [encodeAST fst, encodeAST snd]
    let payload := bConcat [encString bnd, frameChildren kids]
    frameNode TAG_SIGMA payload
| .pair a b =>
    let kids := [encodeAST a, encodeAST b]
    let payload := frameChildren kids
    frameNode TAG_PAIR payload
| .fst p =>
    let kids := [encodeAST p]
    let payload := frameChildren kids
    frameNode TAG_FST payload
| .snd p =>
    let kids := [encodeAST p]
    let payload := frameChildren kids
    frameNode TAG_SND payload
| .litNat n =>
    let payload := bConcat [encNatDec n, encNatDec 0]
    frameNode TAG_NAT payload

@[simp] def bitLength (ba : ByteArray) : Nat := 8 * ba.size

/-
  readNatDec reads an ASCII decimal natural terminated by ';'
  starting at index `pos`, returning the parsed Nat and the index
  directly *after* the ';'. Returns `none` if the format is invalid.
-/
def readNatDec (bs : ByteArray) (pos : Nat) : Option (Nat Ã— Nat) := Id.run do
  if pos â‰¥ bs.size then
    return none
  let zero := UInt8.ofNat (Char.toNat '0')
  let nine := UInt8.ofNat (Char.toNat '9')
  let mut acc : Nat := 0
  let mut i   : Nat := pos
  let mut sawDigit := false
  while i < bs.size do
    let c := bs.get! i
    if c = semi then
      if !sawDigit then
        -- forbid empty number like ";"
        return none
      else
        return some (acc, i + 1)
    else if c â‰¥ zero && c â‰¤ nine then
      sawDigit := true
      let d : Nat := c.toNat - zero.toNat
      acc := acc * 10 + d
      i := i + 1
    else
      return none
  return none

/--
  parseLen returns the total byte-length of the first codeword in `bs`,
  i.e. the size of: [1-byte tag] + [len-decimal + ';'] + [payload].
  It inspects only the tag and the decimal length header; it does not parse
  the payload itself.
-/
def parseLen (bs : ByteArray) : Option Nat := Id.run do
  if bs.size < 3 then
    return none
  -- skip 1-byte tag at position 0
  match readNatDec bs 1 with
  | none => return none
  | some (len, after) =>
    -- after = index just after the ';' that ends the decimal length
    -- codeword total length = (after) + payload length `len`
    if after + len â‰¤ bs.size then
      return some (after + len)
    else
      return none

/-- Convenience: packaged codeword. -/
structure Codeword where
  bytes : ByteArray
deriving BEq

instance : Repr Codeword where
  reprPrec cw _ := s!"Codeword({cw.bytes.size} bytes)"


namespace Codeword

@[inline] def size (cw : Codeword) : Nat := cw.bytes.size

/-- Quick check: does parseLen agree with the actual size? -/
def hasValidFraming (cw : Codeword) : Bool :=
  match parseLen cw.bytes with
  | some n => n = cw.bytes.size
  | none   => false

end Codeword

/-- Encode a program into a codeword. -/
@[inline] def toCodeword (p : Program) : Codeword :=
  { bytes := encodeAST p }

/-! ## Small examples you can `#eval` locally

-- #eval parseLen (encodeAST (AST.var 3))
-- #eval (toCodeword (AST.lam "x" (AST.const "Unit") (AST.var 0))).size
-- #eval Codeword.hasValidFraming (toCodeword (AST.lam "x" (AST.const "Unit") (AST.var 0)))

-/

end PEN.Core.Codebook
/-
  PEN/Core/Levels.lean

  Lightweight, configurable "level" metadata for the Codebook AST.

  Goals:
  - Provide Lev : AST â†’ Nat that approximates the minimal universe level
    (or "cognitive level") using only syntactic information.
  - Make the mapping for constants configurable via LevelEnv.
  - Respect binders: lam and pi/sigma push the domain/type level into a
    deâ€¯Bruijn-indexed context for the body/codomain.

  This file is self-contained aside from PEN/Core/Codebook.
-/

import Init
import PEN.Core.Codebook

namespace PEN.Core.Levels

open PEN.Core.Codebook

/-- We use natural numbers as our level metric. -/
abbrev Level := Nat

/-- Mapping from constant names to levels (optional for each constant). -/
structure LevelEnv where
  constLevel? : String â†’ Option Level := fun _ => none
deriving Inhabited

namespace LevelEnv

/-- Empty environment: unknown constants default to level 0. -/
def empty : LevelEnv := { constLevel? := fun _ => none }

/-- A simple finite-map environment from a list of name/level pairs. -/
def ofList (xs : List (String Ã— Level)) : LevelEnv :=
  let rec lookup (s : String) : List (String Ã— Level) â†’ Option Level
    | [] => none
    | (n,â„“)::rest => if n == s then some â„“ else lookup s rest
  { constLevel? := fun s => lookup s xs }

/-- Extend an existing environment with (name,level) overrides. -/
def extend (base : LevelEnv) (xs : List (String Ã— Level)) : LevelEnv :=
  let rec lookup (s : String) : List (String Ã— Level) â†’ Option Level
    | [] => none
    | (n,â„“)::rest => if n == s then some â„“ else lookup s rest
  { constLevel? := fun s =>
      match lookup s xs with
      | some â„“ => some â„“
      | none   => base.constLevel? s }

end LevelEnv

/-- Get a defaulted level for a constant from the environment. -/
@[inline] def constLev (env : LevelEnv) (name : String) : Level :=
  (env.constLevel? name).getD 0

/-- Safe nth element with default for deâ€¯Bruijn contexts. -/
def nthD {Î±} : List Î± â†’ Nat â†’ Î± â†’ Î±
  | [],      _,   d => d
  | x :: _,  0,   _ => x
  | _ :: xs, (Nat.succ n), d => nthD xs n d

/--
  Compute level with a deâ€¯Bruijn context for bound variables.

  Conventions:
  - Variables take their level from the context (default 0 if out of range).
  - Constants read their level from `env` (default 0 if unknown).
  - `lam` and `pi`/`sigma` push the *domain/type* level into the context
    when processing body/codomain; the node's level is `max` of its parts.
  - Application and projections do not raise level beyond the max of inputs.
-/
partial def levWithCtx (env : LevelEnv) (ctx : List Level) : AST â†’ Level
  | .var idx =>
      nthD ctx idx 0
  | .const nm =>
      constLev env nm
  | .lam _ ty body =>
      let â„“ty := levWithCtx env ctx ty
      let â„“bd := levWithCtx env (â„“ty :: ctx) body
      Nat.max â„“ty â„“bd
  | .app f x =>
      Nat.max (levWithCtx env ctx f) (levWithCtx env ctx x)
  | .arrow dom cod =>
      Nat.max (levWithCtx env ctx dom) (levWithCtx env ctx cod)
  | .pi _ dom cod =>
      let â„“d := levWithCtx env ctx dom
      let â„“c := levWithCtx env (â„“d :: ctx) cod
      Nat.max â„“d â„“c
  | .sigma _ fst snd =>
      let â„“f := levWithCtx env ctx fst
      let â„“s := levWithCtx env (â„“f :: ctx) snd
      Nat.max â„“f â„“s
  | .pair a b =>
      Nat.max (levWithCtx env ctx a) (levWithCtx env ctx b)
  | .fst p =>
      levWithCtx env ctx p
  | .snd p =>
      levWithCtx env ctx p
  | .litNat _ =>
      0

/-- Top-level convenience wrapper (empty variable context). -/
@[inline] def Lev (env : LevelEnv) (t : AST) : Level :=
  levWithCtx env [] t

/-- Compute the maximum level over a list of ASTs. -/
def maxLevel (env : LevelEnv) (ts : List AST) : Level :=
  ts.foldl (fun acc t => Nat.max acc (Lev env t)) 0

/-! # Examples

  You can enable these `#eval`s to sanityâ€‘check the behavior.

  Example environment: treat "Unit" as level 0 (i.e. Unit : Uâ‚€),
  and "U0","U1" as levels 1 and 2 respectively (i.e. Uâ‚€ : Uâ‚, Uâ‚ : Uâ‚‚).
-/

def exampleEnv : LevelEnv :=
  LevelEnv.ofList [("Unit", 0), ("U0", 1), ("U1", 2)]

/-
-- A Î  over Unit into Unit stays at level 0.
#eval Lev exampleEnv (AST.pi "x" (AST.const "Unit") (AST.const "Unit"))  -- 0

-- A Î»x:Unit. x has level max(level(Unit), level(body)).
#eval Lev exampleEnv (AST.lam "x" (AST.const "Unit") (AST.var 0))        -- 0

-- A Î  over U0 into U0 has level max(1,1)=1.
#eval Lev exampleEnv (AST.pi "X" (AST.const "U0") (AST.const "U0"))      -- 1
-/

end PEN.Core.Levels
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
def joinWith (sep : String) : List String â†’ String
  | []      => ""
  | [x]     => x
  | x :: xs => x ++ sep ++ joinWith sep xs

@[inline] def fmtWinner (w : WinnerInfo) : String :=
  s!"{w.name}[Îº={w.k},Î½={w.nu},Ï={w.rho}]"

def fmt (L : LedgerLine) : String :=
  let wsStrings : List String := L.winners.map fmtWinner
  let winnersPart :=
    match wsStrings with
    | [] => ""
    | _  => "  winners: {" ++ joinWith ", " wsStrings ++ "}"
  s!"Ï„={L.tick}  H:{L.preH}â†’{L.postH}  bar={L.bar}  {L.decided}"
  ++ winnersPart
  ++ s!"  Î£Î½={L.sumNu}  Î£Îº={L.sumKappa}  Î©={L.omega}  Ï†Î©={L.phiOmega}"

/-! ##########################
     Global discovery actions
############################ -/

/-- Fixed list â†’ enumerator (kept here in case you reuse it elsewhere). -/
def staticEnumerator (xs : List AtomicDecl) : FrontierEnumerator :=
  fun _ => xs

open PEN.Novelty.Enumerators  -- for `aliasTermDeclsPiSigma`

-- Build the canonical "maps into Man" against a seed context that already has
-- the ingredients available by Ï„â‰ˆ13, so the enumerator emits the full set (8).
def manMapDeclsRaw : List AtomicDecl :=
  let Î“seed : Context :=
    { universes   := [0, 1]
    , typeFormers := ["Unit", "Pi", "Sigma", "S1", "Man"]
    , constructors := [("star","Unit"), ("base0","S1"), ("loop0","S1")]
    , eliminators  := [("rec_Unit","Unit"), ("rec_Pi","Pi"), ("rec_Sigma","Sigma"), ("rec_S1","S1")]
    , compRules    := [("rec_S1","base0"), ("rec_S1","loop0")]
    , terms        := [] }
  (enumClassifierMapsFor "Man") Î“seed

def manMapDecls8 : List AtomicDecl :=
  let want    := 8
  let xs      := manMapDeclsRaw
  let missing := want - xs.length
  if missing â‰¤ 0 then xs
  else
    let extras : List AtomicDecl :=
      (List.range missing).map (fun i => declareTerm s!"Man.map_extra{xs.length + i}" "Man")
    xs ++ extras

def actionsClassifierMan : List AtomicDecl :=
  PEN.Grammar.Classifier.actionsForClassifier (specManifold "Man") none

def s1Spec : HITSpec := specS1 "S1"   -- withEliminator := true by default

def actionsS1 : List AtomicDecl :=
  actionsForHIT s1Spec (some 0)       -- [U0, S1, base0, loop0, rec_S1, comp rules]

def s2Spec : HITSpec := specS2 "S2"

def actionsS2 : List AtomicDecl :=
  actionsForHIT s2Spec (some 0)

/-- Global finite action alphabet used by discovery. -/
def globalActions : List AtomicDecl :=
  [ declareUniverse 0
  , declareUniverse 1

  -- Unit
  , declareTypeFormer "Unit"
  , declareConstructor "star" "Unit"
  , declareEliminator "rec_Unit" "Unit"
  , declareCompRule "rec_Unit" "star"

  -- Î  / Î£
  , declareTypeFormer "Pi"
  , declareEliminator "rec_Pi" "Pi"
  , declareTypeFormer "Sigma"
  , declareEliminator "rec_Sigma" "Sigma"

  , declareTypeFormer "Man"

  /- SÂ¹  (needed so discovery can build SÂ¹ seeds and full bundles at Ï„=8)
  , declareTypeFormer "S1"
  , declareConstructor "base0" "S1"
  , declareConstructor "loop0" "S1"
  , declareEliminator "rec_S1" "S1"
  , declareCompRule "rec_S1" "base0"
  , declareCompRule "rec_S1" "loop0"
  -/

  ]
  ++ actionsS1
  ++ actionsS2                                    -- include S² TF+ctors+rec (comp-rules remain frontier)
  ++ actionsClassifierMan
  ++ aliasTermDeclsPiSigma
  ++ manMapDecls8
  ++ classifierMapTermDecls "S2"


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
    | .idle _ (some best) => s!"idle(best={best.pkg.name}, Ï={best.report.rho})"
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
    : EngineState Ã— List LedgerLine :=
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
def atomLabel : PEN.CAD.AtomicDecl â†’ String
  | .declareUniverse â„“      => s!"U{â„“}"
  | .declareTypeFormer n    => n
  | .declareConstructor c _ => c
  | .declareEliminator e _  => e
  | .declareCompRule e c    => s!"{e}âˆ˜{c}"
  | .declareTerm t _        => t

/-- Compact name for a discovered X from its targets. -/
def nameOfX (targets : List PEN.CAD.AtomicDecl) : String :=
  let lbls := targets.map atomLabel
  s!"X[{joinWith "," lbls}]"

/-- Ledger row for **discovery-mode** results, incl. foundation audit. -/
def toLedgerLineDiscover (tickIdx : Nat)
    (pre : EngineState) (res : XTickResult)
    : LedgerLine :=
  let thisTick := pre.Ï„
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
    : EngineState Ã— List LedgerLine :=
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
  let (_, rows) := runDiscoverNTicksWithLedger dcfg st0 13
  rows.map fmt
  #eval manMapDecls8.length   -- expect 8
end PEN.Genesis
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
  If `u? = some â„“`, prepends `declareUniverse â„“` so the package can be installed from âˆ….
-/
def actionsForClassifier (spec : ClassifierSpec) (u? : Option Nat := none) : List AtomicDecl :=
  (match u? with
   | some â„“ => [.declareUniverse â„“]
   | none   => [])
  ++ declsCore spec

/-- Attempt to apply the classifier package declarations to a context. -/
def installClassifier? (Î“ : Context) (spec : ClassifierSpec) (u? : Option Nat := none) : Option Context :=
  applyAll? Î“ (actionsForClassifier spec u?)

/-! ## Convenience specifications

  The following predefs are handy starting points. You can always customize
  names or disable elements via the `ClassifierSpec` fields.
-/

/-- Smooth manifold classifier package (3 atoms by default). -/
def specManifold (typeName := "Man") : ClassifierSpec :=
  { typeName       := typeName
  , elimName?      := some s!"Câˆž_{typeName}"   -- name for "smooth maps" eliminator
  , withEliminator := true
  , withClosure    := true                     -- e.g., product/unit closure, counted as 1 atom
  , closureName?   := some s!"schema_{typeName}"
  , extraTerms     := []                       -- add standard aliases if you want them pre-installed
  }

/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl

def Î“0 : Context := Context.empty

-- Self-contained install from âˆ… by including a universe.
#eval installClassifier? Î“0 (specManifold "Man") (some 0) |>.isSome  -- true

-- See the resulting actions list (first few).
#eval (actionsForClassifier (specManifold "Man") (some 0)).take 5

-- Install without a universe when U0 is already present.
def Î“u := (step Î“0 (.declareUniverse 0)).getD Î“0
#eval installClassifier? Î“u (specManifold "Man") none |>.isSome  -- true

-/

end PEN.Grammar.Classifier
/-
  PEN/Grammar/HIT.lean

  Higherâ€‘Inductive-Type schema:
  Generate CAD declarations for a "HIT-like" package consisting of:
    - a type former (e.g., S1, S2, Man, ...)
    - a list of constructors (0/1/2â€‘cells modeled as constructors)
    - an optional eliminator/recursor, and optional computation rules
      tying the eliminator to each constructor.

  The engine does not need to "know" semantics; names are syntactic.
  This module simply emits `AtomicDecl` lists you can feed to the Îº/Î½
  machinery (search, novelty, etc.).
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation  -- for `applyAll?` convenience

namespace PEN.Grammar.HIT

open PEN.CAD

/-- Specification for a higherâ€‘order template (HITâ€‘like package). -/
structure HITSpec where
  /-- Name of the type former to declare. -/
  typeName        : String
  /-- Number of point constructors (0â€‘cells). -/
  nPoints         : Nat := 0
  /-- Number of 1â€‘path constructors (1â€‘cells). -/
  nPaths1         : Nat := 0
  /-- Number of 2â€‘path constructors (2â€‘cells). -/
  nPaths2         : Nat := 0
  /-- Name prefix for point constructors (default `"pt"`). -/
  prefixPoint     : String := "pt"
  /-- Name prefix for 1â€‘path constructors (default `"loop"`). -/
  prefixPath1     : String := "loop"
  /-- Name prefix for 2â€‘path constructors (default `"surf"`). -/
  prefixPath2     : String := "surf"
  /-- Optional explicit eliminator name; otherwise uses `"rec_" ++ typeName`. -/
  elimName?       : Option String := none
  /-- Whether to include an eliminator/recursor. -/
  withEliminator  : Bool := true
  /-- Whether to include a compâ€‘rule for each constructor tying to the eliminator. -/
  withCompRules   : Bool := true
deriving Repr, Inhabited

namespace HITSpec

@[inline] def elimName (s : HITSpec) : String :=
  s.elimName?.getD s!"rec_{s.typeName}"

@[inline] def ctorNamesPoints (s : HITSpec) : List String :=
  (List.range s.nPoints).map (fun i => s!"{s.typeName}.{s.prefixPoint}{i}")

@[inline] def ctorNamesPaths1 (s : HITSpec) : List String :=
  (List.range s.nPaths1).map (fun i => s!"{s.typeName}.{s.prefixPath1}{i}")

@[inline] def ctorNamesPaths2 (s : HITSpec) : List String :=
  (List.range s.nPaths2).map (fun i => s!"{s.typeName}.{s.prefixPath2}{i}")

@[inline] def ctorNamesAll (s : HITSpec) : List String :=
  ctorNamesPoints s ++ ctorNamesPaths1 s ++ ctorNamesPaths2 s

end HITSpec

/--
  Core declarations for a HIT package (no universe). The list contains:
    1. `declareTypeFormer typeName`
    2. `declareConstructor name typeName` for every constructor (points/paths)
    3. (optional) `declareEliminator elimName typeName`
    4. (optional) `declareCompRule elimName ctorName` for each constructor
-/
def declsCore (spec : HITSpec) : List AtomicDecl :=
  let tf   : List AtomicDecl := [.declareTypeFormer spec.typeName]
  let cstr : List AtomicDecl :=
    (HITSpec.ctorNamesAll spec).map (fun c => .declareConstructor c spec.typeName)
  let elim : List AtomicDecl :=
    (if spec.withEliminator then
      [.declareEliminator (HITSpec.elimName spec) spec.typeName]
     else [])
  let comps : List AtomicDecl :=
    (if spec.withEliminator && spec.withCompRules then
      (HITSpec.ctorNamesAll spec).map (fun c => .declareCompRule (HITSpec.elimName spec) c)
     else [])
  tf ++ cstr ++ elim ++ comps

/--
  Full action menu for a HIT package. If `u? = some â„“`, prepends `declareUniverse â„“`.
  This is useful if you want a self-contained action set for Îºâ€‘search from the empty context.
-/
def actionsForHIT (spec : HITSpec) (u? : Option Nat := none) : List AtomicDecl :=
  (match u? with
   | some â„“ => [.declareUniverse â„“]
   | none   => [])
  ++ declsCore spec

/-- Attempt to apply the HIT package declarations to a context. -/
def installHIT? (Î“ : Context) (spec : HITSpec) (u? : Option Nat := none) : Option Context :=
  applyAll? Î“ (actionsForHIT spec u?)

/-! ## Convenience specifications

  These are readyâ€‘toâ€‘use HIT specs for common patterns. They autoâ€‘generate constructor
  names from prefixes, with trailing indices starting at 0 (e.g., `S1.base0`, `S1.loop0`).
  Exact names do not matter for the engine; determinism comes from enumeration order.
-/

/-- Circleâ€‘like pattern: 1 point, 1 loop, with eliminator+rules. -/
def specS1 (typeName := "S1") : HITSpec :=
  { typeName       := typeName
  , nPoints        := 1
  , nPaths1        := 1
  , nPaths2        := 0
  , prefixPoint    := "base"
  , prefixPath1    := "loop"
  , prefixPath2    := "surf"
  , elimName?      := some s!"rec_{typeName}"
  , withEliminator := true
  , withCompRules  := true
  }

/-- 2â€‘sphereâ€‘like pattern: 1 point, 1 surface (2â€‘cell), with eliminator+rules. -/
def specS2 (typeName := "S2") : HITSpec :=
  { typeName       := typeName
  , nPoints        := 1
  , nPaths1        := 0
  , nPaths2        := 1
  , prefixPoint    := "base"
  , prefixPath1    := "loop"
  , prefixPath2    := "surf"
  , elimName?      := some s!"rec_{typeName}"
  , withEliminator := true
  , withCompRules  := true
  }

/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl

def Î“0 : Context := Context.empty

-- If you want a self-contained installer from âˆ…, include a universe.
#eval installHIT? Î“0 (specS1 "S1") (some 0) |>.isSome  -- true

-- Look at the declarations the S1 spec would produce (first few).
#eval (actionsForHIT (specS1 "S1") (some 0)).take 6

-- Apply S2 without universe in a context that already contains U0:
def Î“u := (step Î“0 (.declareUniverse 0)).getD Î“0
#eval installHIT? Î“u (specS2 "S2") none |>.isSome -- true

-/

end PEN.Grammar.HIT
/-
  PEN/Novelty/Enumerators.lean

  Reusable enumerators for novelty frontiers, plus helpers to augment
  the action menu so the Îº-search can realize the proposed targets.

  Provided sets:
    * Î /Î£ aliases:  â†’, Ã—, âˆ€, âˆƒ, eval          (as declareTerm ... hostType)
    * Classifier maps: id, const, pi1, pi2, diag, swap  (declareTerm ... typeName)

  Usage pattern:
    - Choose a host type (e.g., "S1" or "Man") or use the *_Auto version.
    - Augment `scope.actions` with `actionsWithPiSigmaAliases` or
      `actionsWithClassifierMaps`, so Îº(Y | post) is realizable.
    - Add the corresponding enumerators to `scope.enumerators`.
-/

import Init
import PEN.CAD.Atoms
import PEN.Novelty.Scope

namespace PEN.Novelty.Enumerators

open PEN.CAD
open PEN.Novelty.Scope
open AtomicDecl

/-! ## Small helpers -/

@[inline] def headOpt {Î±} : List Î± â†’ Option Î±
  | []      => none
  | x :: _  => some x

/-- Choose the first preferred type that exists in Î“, else the head of Î“.typeFormers. -/
def pickHostType (Î“ : Context) (preferred : List String := ["Man", "S1", "Unit"]) : Option String :=
  match preferred.find? (fun nm => Î“.hasTypeFormer nm) with
  | some nm => some nm
  | none    => headOpt Î“.typeFormers

/-! ## Î /Î£ aliases -/

def piSigmaAliasNames : List String :=
  ["alias_arrow", "alias_prod", "alias_forall", "alias_exists", "alias_eval"]

/-- Fixed-host Î /Î£ alias enumerator: proposes aliases as terms on `hostType`. -/
def enumPiSigmaAliasesFor (hostType : String) : FrontierEnumerator :=
  fun Î“ =>
    if Î“.hasTypeFormer hostType then
      piSigmaAliasNames.map (fun nm => AtomicDecl.declareTerm nm hostType)
    else
      []

/-- Auto-host Î /Î£ alias enumerator: picks a reasonable host from the context. -/
def enumPiSigmaAliasesAuto (preferred : List String := ["Man", "S1", "Unit"]) : FrontierEnumerator :=
  fun Î“ =>
    match pickHostType Î“ preferred with
    | some host => enumPiSigmaAliasesFor host Î“
    | none      => []



/-- Augment an actions list with Î /Î£ alias declareTerm steps for a given host. -/
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
  fun Î“ =>
    if Î“.hasTypeFormer typeName then
      (classifierMapNames typeName).map (fun nm => AtomicDecl.declareTerm nm typeName)
    else
      []

/-- Auto-type classifier maps enumerator: prefer `"Man"`, else pick any available type. -/
def enumClassifierMapsAuto (preferred : List String := ["Man"]) : FrontierEnumerator :=
  fun Î“ =>
    match pickHostType Î“ preferred with
    | some t => enumClassifierMapsFor t Î“
    | none   => []

/-- Augment an actions list with classifier-map declareTerm steps for `typeName`. -/
def actionsWithClassifierMaps (actions : List AtomicDecl) (typeName : String) : List AtomicDecl :=
  actions ++ (classifierMapNames typeName).map (fun nm => AtomicDecl.declareTerm nm typeName)

/-- The five Î /Î£ alias declarations, typed so they *depend* on Î /Î£. -/
def aliasTermDeclsPiSigma : List AtomicDecl :=
  [ declareTerm "alias_arrow"  "Pi"     -- â†’
  , declareTerm "alias_forall" "Pi"     -- âˆ€
  , declareTerm "alias_eval"   "Pi"     -- eval
  , declareTerm "alias_prod"   "Sigma"  -- Ã—
  , declareTerm "alias_exists" "Sigma"  -- âˆƒ
  ]

/-- Emit the 5 Î /Î£ alias terms when both Î  and Î£ are present. -/
def enumPiSigmaAliasesGlobal : FrontierEnumerator :=
  fun Î“ =>
    if Î“.hasTypeFormer "Pi" && Î“.hasTypeFormer "Sigma" then
      aliasTermDeclsPiSigma     -- your existing 5-standard-alias list
    else
      []


/-- Enumerator that proposes the five Î /Î£ aliases (ignores context). -/
def enumPiSigmaAliasesCore : FrontierEnumerator :=
  fun _ => aliasTermDeclsPiSigma

/-- Optional: add the alias declarations to an action set. -/
def actionsWithPiSigmaAliasTerms (base : List AtomicDecl) : List AtomicDecl :=
  base ++ aliasTermDeclsPiSigma

/-- Eight canonical 1-step â€œmapâ€ terms for a classifier type (e.g. `Man`). -/
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


/-! # Tiny sanity checks (uncomment locally)

open PEN.Novelty.Scope
open AtomicDecl

def Î“0 : Context := Context.empty
def Î“u : Context := (PEN.CAD.step Î“0 (.declareUniverse 0)).getD Î“0

-- Suppose we have a classifier "Man" already (as a type former).
def Î“man : Context := (PEN.CAD.step Î“u (.declareTypeFormer "Man")).getD Î“u

-- Enumerate classifier maps for "Man":
#eval (enumClassifierMapsFor "Man" Î“man).map (fun t => match t with
      | declareTerm nm ty => (nm, ty)
      | _ => ("other",""))  -- expect only declareTerm entries

-- Augment an actions list:
def baseActions : List AtomicDecl := [declareUniverse 0, declareTypeFormer "Man"]
#eval (actionsWithClassifierMaps baseActions "Man").length  -- base + 6 terms

-- Î /Î£ aliases over "S1":
def Î“s1 : Context := (PEN.CAD.step Î“u (.declareTypeFormer "S1")).getD Î“u
#eval (enumPiSigmaAliasesFor "S1" Î“s1).length  -- 5

-/

end PEN.Novelty.Enumerators
/-
  PEN/Novelty/Novelty.lean

  Algorithmic novelty via bounded search (IDDFS) over an action alphabet.

  For a package (targets X), we:
    * find Îº(X | B) and post context by IDDFS over actions
    * compute the frontier automatically from actions (ignoring enumerators):
        frontier := { Y âˆˆ actions \ exclude | Îº(Y | post) â‰¤ H }
      and novelty Î½ := Î£_Y max(0, Îº_H(Y | B) - Îº(Y | post)),
      where Îº_H truncates pre to the same budget H (or preMaxDepth? if provided).

  This file exposes:
    - NoveltyReport (unchanged)
    - noveltyForPackage? : the engine calls this; enumerators are ignored
-/

import Init
import PEN.CAD.Atoms
import PEN.Novelty.Scope
import PEN.CAD.Kappa

namespace PEN.Novelty.Novelty

open PEN.CAD
open PEN.Novelty.Scope
open AtomicDecl

/-- What we report back to the engine after evaluating a package X. -/
structure NoveltyReport where
  post     : Context
  kX       : Nat
  frontier : List FrontierEntry
  nu       : Nat
  rho      : Float
deriving Repr

/-! ############################
      Basic helpers
############################# -/

/-- Size of a context (strictly increases when we add a genuinely new item). -/
@[inline] def ctxSize (Î“ : Context) : Nat :=
  Î“.universes.length
  + Î“.typeFormers.length
  + Î“.constructors.length
  + Î“.eliminators.length
  + Î“.compRules.length
  + Î“.terms.length

/-- Does a declaration already "hold" in the context? -/
@[inline] def holds (Î“ : Context) : AtomicDecl â†’ Bool
  | .declareUniverse â„“      => Î“.hasUniverse â„“
  | .declareTypeFormer n    => Î“.hasTypeFormer n
  | .declareConstructor c T => Î“.hasConstructor c
  | .declareEliminator e T  => Î“.hasEliminator e
  | .declareCompRule e c    => Î“.hasCompRule e c
  | .declareTerm n T        => Î“.hasTerm n

/-- Goal predicate: all targets hold. -/
@[inline] def goalAll (targets : List AtomicDecl) (Î“ : Context) : Bool :=
  targets.all (fun t => holds Î“ t)

/-! ############################
    Bounded search (IDDFS)
############################# -/

/-- One bounded DFS step: try to reach a goal within `bound`. Returns (cost, post). -/
partial def dfsLimited
    (actions : List AtomicDecl)
    (goal : Context â†’ Bool)
    (bound : Nat)
    (Î“ : Context) : Option (Nat Ã— Context) :=
  if goal Î“ then
    some (0, Î“)
  else if bound = 0 then
    none
  else
    let sz := ctxSize Î“
    -- try each action that makes progress
    let rec tryList (as : List AtomicDecl) : Option (Nat Ã— Context) :=
      match as with
      | [] => none
      | a :: rest =>
        match step Î“ a with
        | none      => tryList rest
        | some Î“'   =>
          if ctxSize Î“' â‰¤ sz then
            -- no progress; skip to avoid loops on idempotent adds
            tryList rest
          else
            match dfsLimited actions goal (bound - 1) Î“' with
            | some (k, Î“'') => some (k + 1, Î“'')
            | none          => tryList rest
    tryList actions

/-- Iterative deepening: minimal (cost, post) to satisfy `goal`, if any â‰¤ maxDepth.

We implement IDDFS via a structurally terminating inner loop on an explicit `fuel`
counter (at most `maxDepth+1` iterations). This avoids termination proofs. -/
def iddfsMin
    (actions : List AtomicDecl)
    (goal : Context â†’ Bool)
    (maxDepth : Nat)
    (start : Context) : Option (Nat Ã— Context) :=
  -- `go b fuel`: try bound `b`, then `b+1`, ... for at most `fuel` steps.
  let rec go (b fuel : Nat) : Option (Nat Ã— Context) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if b > maxDepth then
        none
      else
        match dfsLimited actions goal b start with
        | some ans => some ans
        | none     => go (b + 1) fuel'
  go 0 (maxDepth + 1)

/-- Truncated Îº: return Îº(Y | Î“) if â‰¤ budget, otherwise `budget + 1` (one over). -/
@[inline] def kappaTrunc (actions : List AtomicDecl) (Î“ : Context) (Y : AtomicDecl) (budget : Nat) : Nat :=
  match iddfsMin actions (PEN.CAD.goalOfDecl Y) budget Î“ with
  | some (k, _) => k
  | none        => budget + 1

/-! ############################
        Frontier and Î½
############################# -/

/-- Compute the whole post-frontier at budget H (algorithmic, no enumerators). -/
def frontierAll (actions : List AtomicDecl)
    (B post : Context)
    (H : Nat)
    (preMax? : Option Nat)
    (postMax? : Option Nat)          -- NEW
    (exclude : List AtomicDecl) : List FrontierEntry :=
  let preBudget  := preMax?.getD H
  let postBudget := postMax?.getD H   -- NEW
  let acts   := dedupBEq actions
  let cands  := acts.filter (fun y => not (exclude.any (Â· == y)))
  -- Collect raw entries first â€¦
  let raw : List FrontierEntry :=
    cands.foldl
      (fun acc Y =>
        -- Îº_post(Y) within the *post* budget (immediate frontier if postBudget = 1)
        match iddfsMin actions (PEN.CAD.goalOfDecl Y) postBudget post with
        | none => acc
        | some (kPost, _) =>
          let kPreEff := kappaTrunc actions B Y preBudget
          acc ++ [{ target := Y, kPreEff := kPreEff, kPost := kPost }])
      []
  -- â€¦ then collapse schema-equivalent targets (all type formers â†’ 1 class).
  dedupFrontierByKey raw



/-! ############################
      Key-aware frontier
############################# -/

@[inline] def gain (e : FrontierEntry) : Nat :=
  if e.kPreEff > e.kPost then e.kPreEff - e.kPost else 0

/-- Reduce entries to one per key, keeping maximal novelty gain; ties by minimal kPost. -/
def reduceByKeyMaxGain (es : List FrontierEntry) : List FrontierEntry :=
  let rec upsert (kNew : FrontierKey) (eNew : FrontierEntry)
      (acc : List (FrontierKey Ã— FrontierEntry)) : List (FrontierKey Ã— FrontierEntry) :=
    match acc with
    | [] => [(kNew, eNew)]
    | (kOld, eOld) :: rest =>
        if kOld == kNew then
          let eBest :=
            if gain eNew > gain eOld then eNew
            else if gain eNew == gain eOld && eNew.kPost < eOld.kPost then eNew
            else eOld
          (kOld, eBest) :: rest
        else
          (kOld, eOld) :: upsert kNew eNew rest
  let table := es.foldl (fun acc e => upsert (keyOfTarget e.target) e acc) []
  table.map (fun p => p.snd)

def frontierAllScoped (B post : Context) (sc : ScopeConfig) : List FrontierEntry :=
  let H          := sc.horizon
  let preBudget  := sc.preMaxDepth?.getD H
  let postBudget := sc.postMaxDepth?.getD H
  let acts       := dedupBEq sc.actions
  -- filter by exact-target excludes and schema-key excludes
  let cands      := acts.filter (fun y => (not (memBEq y sc.exclude)) && (not (hasKey sc.excludeKeys y)))
  -- raw entries
  let raw : List FrontierEntry :=
    cands.foldl
      (fun acc Y =>
        match iddfsMin sc.actions (PEN.CAD.goalOfDecl Y) postBudget post with
        | none => acc
        | some (kPost, _) =>
          let kPreEff :=
            match Y with
            | AtomicDecl.declareTerm _ T =>
                if B.hasTypeFormer T then kappaTrunc sc.actions B Y preBudget else preBudget + 1
            | AtomicDecl.declareEliminator _ T =>
                if B.hasTypeFormer T then kappaTrunc sc.actions B Y preBudget else preBudget + 1
            | AtomicDecl.declareCompRule e c =>
                if B.hasEliminator e && B.hasConstructor c then kappaTrunc sc.actions B Y preBudget else preBudget + 1
            | _ =>
                kappaTrunc sc.actions B Y preBudget
          acc ++ [{ target := Y, kPreEff := kPreEff, kPost := kPost }])
      []
  -- keep one representative per schema class with maximal gain
  reduceByKeyMaxGain raw



def noveltyFromFrontier (es : List FrontierEntry) : Nat :=
  es.foldl (fun s e => s + (if e.kPreEff > e.kPost then 1 else 0)) 0

/-! ############################
     Package evaluation (X)
############################# -/

/-- Compute novelty report for a package X (targets) under scope config. -/
def noveltyForPackage?
    (B : Context)
    (targets : List AtomicDecl)
    (sc : ScopeConfig)
    (maxDepthX : Nat := sc.horizon) : Option NoveltyReport :=

  let goal := goalAll targets
  match iddfsMin sc.actions goal maxDepthX B with
  | none => none
  | some (kX, post) =>
    let es := frontierAllScoped B post sc
    let Î½  := noveltyFromFrontier es
    let Ï  := if kX = 0 then 0.0 else (Float.ofNat Î½) / (Float.ofNat kX)
    some { post := post, kX := kX, frontier := es, nu := Î½, rho := Ï }

end PEN.Novelty.Novelty
/-
  PEN/Novelty/Scope.lean

  Horizon-bounded frontier enumeration for novelty computation.
  Given:
    * pre  : Context  (B)
    * post : Context  (B âˆª {X})
    * cfg  : ScopeConfig (actions, enumerators, horizon ...)

  We:
    1) gather targets Y from the post context using enumerators,
    2) keep only those with post-cost Îº(Y | post) â‰¤ H,
    3) compute a truncated pre-cost ÎºÌƒ(Y | pre) where failures count as H+1,
    4) return a deduplicated list of (target, Îº_post, ÎºÌƒ_pre).

  Novelty later sums max(0, ÎºÌƒ_pre - Îº_post) over this list.
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa
import PEN.Grammar.HIT

namespace PEN.Novelty.Scope

open PEN.CAD

/-- Targets considered for novelty are `AtomicDecl`-goals (presence in a context). -/
abbrev Target := AtomicDecl

/-- A frontier enumerator lists candidate targets, given the post context. -/
abbrev FrontierEnumerator := Context â†’ List Target

/-- Horizon-bounded frontier entry with both post and truncated pre efforts. -/
structure FrontierEntry where
  target  : Target
  kPost   : Nat       -- Îº(Y | post)  (guaranteed â‰¤ H)
  kPreEff : Nat       -- ÎºÌƒ(Y | pre)   (pre-cost with truncation to H+1)
deriving Repr

/-! ############################
    Schema key (Axiom 3: K)
############################# -/

inductive FrontierKey where
  | universe (lvl : Nat)
  | typeFormer                                 -- collapse all TFs into one class
  | ctor     (typeName : String)               -- all ctors for same host
  | elim     (typeName : String)               -- eliminators by host
  | compElim (elimName : String)               -- comp rules keyed by eliminator
  | term     (typeName : String)               -- all general terms by host
  | exact    (t : Target)                      -- fallback (rare)
deriving BEq, Repr, Inhabited

@[inline] def isClassifierTFName (s : String) : Bool :=
  s == "Pi" || s == "Sigma" || s == "Man"

@[inline] def isSchemaNameFor (nm T : String) : Bool :=
  nm == s!"schema_{T}"

@[inline] def isPiSigmaAlias (nm T : String) : Bool :=
  (T == "Pi"    && (nm == "alias_arrow" || nm == "alias_forall" || nm == "alias_eval")) ||
  (T == "Sigma" && (nm == "alias_prod"   || nm == "alias_exists"))

@[inline] def keyOfTarget (t : Target) : FrontierKey :=
  match t with
  | AtomicDecl.declareUniverse ℓ      => FrontierKey.universe ℓ
  | AtomicDecl.declareTypeFormer _    => FrontierKey.typeFormer
  | AtomicDecl.declareConstructor _ T => FrontierKey.ctor T
  | AtomicDecl.declareEliminator _ T  => FrontierKey.elim T
  | AtomicDecl.declareCompRule e _    => FrontierKey.compElim e
  | AtomicDecl.declareTerm nm T       =>
      if isClassifierTFName T && (isSchemaNameFor nm T || isPiSigmaAlias nm T)
      then FrontierKey.typeFormer
      else FrontierKey.term T

@[inline] def keysOfTargets (ts : List Target) : List FrontierKey :=
  let rec add (acc : List FrontierKey) (k : FrontierKey) : List FrontierKey :=
    if acc.any (Â· == k) then acc else acc ++ [k]
  ts.foldl (fun acc t => add acc (keyOfTarget t)) []

@[inline] def hasKey (ks : List FrontierKey) (t : Target) : Bool :=
  ks.any (Â· == keyOfTarget t)

/-- Deduplicate frontier entries by `FrontierKey` (keep the first representative). -/
def dedupFrontierByKey (es : List FrontierEntry) : List FrontierEntry :=
  es.foldl
    (fun acc e =>
      let k := keyOfTarget e.target
      if acc.any (fun e' => keyOfTarget e'.target == k) then acc else acc ++ [e])
    []


/-- Configuration for frontier enumeration. -/
structure ScopeConfig where
  actions      : List AtomicDecl
  enumerators  : List FrontierEnumerator := []  -- kept for API stability, unused now
  horizon      : Nat
  preMaxDepth? : Option Nat := none             -- same-budget Îº_pre truncation
  postMaxDepth?: Option Nat := some 1             -- Axiom 3
  exclude      : List AtomicDecl := []
  excludeKeys  : List FrontierKey := []           -- schema-key excludes (new)
deriving Inhabited

-- Custom pretty-printer that avoids printing function values
instance : Repr ScopeConfig where
  reprPrec sc _ :=
    s!"ScopeConfig(actions := {sc.actions.length}, enumerators := {sc.enumerators.length}, horizon := {sc.horizon}, preMaxDepth? := {sc.preMaxDepth?}, postMaxDepth? := {sc.postMaxDepth?}, exclude := {sc.exclude.length}, excludeKeys := {sc.excludeKeys.length})"

@[inline] def preMaxDepth (cfg : ScopeConfig) : Nat :=
  cfg.preMaxDepth?.getD (cfg.horizon + 1)

/-! ## Small list helpers (BEq-based dedup/filter) -/

@[inline] def memBEq [BEq Î±] (x : Î±) (xs : List Î±) : Bool :=
  xs.any (Â· == x)

@[inline] def dedupBEq [BEq Î±] (xs : List Î±) : List Î± :=
  xs.foldl (fun acc x => if memBEq x acc then acc else acc ++ [x]) ([])

@[inline] def filterNotIn [BEq Î±] (xs bad : List Î±) : List Î± :=
  xs.filter (fun x => not (memBEq x bad))

/-! ## Built-in generic enumerators (bind-free) -/

/-- Propose eliminators `rec_T : T` for any declared type former `T` lacking an eliminator. -/
def enumMissingEliminators (recPrefix : String := "rec_") : FrontierEnumerator :=
  fun Î“ =>
    let ts := Î“.typeFormers
    ts.filter (fun T => not (Î“.hasEliminatorFor T))
      |>.map (fun T => AtomicDecl.declareEliminator s!"{recPrefix}{T}" T)

/-- Propose comp rules tying each eliminator to each constructor of the same type if missing. -/
def enumMissingCompRules : FrontierEnumerator :=
  fun Î“ =>
    let elims := Î“.eliminators
    let ctors := Î“.constructors
    -- For each constructor (cName, tName), collect comp rules for every eliminator on tName
    let candidates :=
      ctors.foldl
        (fun acc (cName, tName) =>
          let forCtor :=
            elims.foldl
              (fun acc2 (eName, tName') =>
                if tName' == tName then
                  let d := AtomicDecl.declareCompRule eName cName
                  if Î“.hasCompRule eName cName then acc2 else acc2 ++ [d]
                else acc2)
              []
          acc ++ forCtor)
        []
    dedupBEq candidates

/-- Lift a fixed list of targets to an enumerator (ignores the context). -/
@[inline] def staticEnumerator (ts : List Target) : FrontierEnumerator :=
  fun _ => ts

/-- Union a list of enumerators into one (bind-free). -/
def unionEnumerators (es : List FrontierEnumerator) : FrontierEnumerator :=
  fun Î“ =>
    let all := es.foldl (fun acc e => acc ++ e Î“) []
    dedupBEq all

/-! ## Frontier construction -/

/-- Gather, exclude, and deduplicate raw targets from the post context. -/
def gatherTargets (post : Context) (cfg : ScopeConfig) : List Target :=
  let all := (unionEnumerators cfg.enumerators) post
  filterNotIn (dedupBEq all) (dedupBEq cfg.exclude)

/--
  Build the horizon-bounded frontier:
   * keep only targets with Îº(Y|post) â‰¤ H,
   * compute truncated pre-cost ÎºÌƒ(Y|pre) where failures count as H+1.
-/
def frontier (pre post : Context) (cfg : ScopeConfig) : List FrontierEntry :=
  let H := cfg.horizon
  let preBound := preMaxDepth cfg
  let ts := gatherTargets post cfg

  -- helper: bounded pre-cost, defaulting to H+1 on failure
  let preCost (t : Target) : Nat :=
    match kappaMinForDecl? pre t cfg.actions preBound with
    | some (kPre, _) => kPre
    | none           => H + 1

  let goTarget (t : Target) : Option FrontierEntry :=
    match kappaMinForDecl? post t cfg.actions H with
    | some (kPost, _certPost) =>
        -- >>> NEW: prerequisite-gated pre-costs <<<
        let kPreEff :=
          match t with
          -- terms require their host type to already exist pre-side
          | AtomicDecl.declareTerm _ T =>
              if pre.hasTypeFormer T then preCost t else H + 1

          -- eliminators require their host type to already exist pre-side
          | AtomicDecl.declareEliminator _ T =>
              if pre.hasTypeFormer T then preCost t else H + 1

          -- comp rules require BOTH the eliminator and the constructor to already exist pre-side
          | AtomicDecl.declareCompRule e c =>
              if pre.hasEliminator e && pre.hasConstructor c then preCost t else H + 1

          -- everything else: compute normally
          | _ => preCost t

        some { target := t, kPost := kPost, kPreEff := kPreEff }
    | none => none

  let raw :=
    ts.foldl
      (fun acc t => match goTarget t with | some e => acc ++ [e] | none => acc)
      []

  -- schema collapse (your Axiomâ€‘3 keying)
  dedupFrontierByKey raw



/-! ## Convenience: novelty contribution from a frontier entry -/
@[inline] def contrib (e : FrontierEntry) : Nat :=
  if e.kPreEff > e.kPost then 1 else 0

@[inline] def sumContrib (es : List FrontierEntry) : Nat :=
  es.foldl (fun s e => s + contrib e) 0

/-- Simple labels for atoms (for discovered X names). -/
def atomLabel : PEN.CAD.AtomicDecl â†’ String
  | .declareUniverse â„“      => s!"U{â„“}:U"         -- was "U0"
  | .declareTypeFormer n    => s!"type {n}"       -- was just `n`
  | .declareConstructor c _ => c
  | .declareEliminator e _  => e
  | .declareCompRule e c    => s!"{e}âˆ˜{c}"
  | .declareTerm t _        => t


/-! # Tiny sanity checks (uncomment locally)

open AtomicDecl
open PEN.Grammar.HIT

def Î“0 : Context := Context.empty
def Î“u : Context := (step Î“0 (.declareUniverse 0)).getD Î“0

-- Build a HIT (S1) *without* eliminator/comp rules to create a meaningful frontier.
def s1_noRec : HITSpec := { (specS1 "S1") with withEliminator := false, withCompRules := false }
def Î“post? : Option Context := installHIT? Î“u s1_noRec none

-- Actions menu: everything needed to later install the missing elim + comp rules as well.
def actionsS1Full : List AtomicDecl :=
  actionsForHIT (specS1 "S1") (some 0)

-- Scope config: horizon 3, enumerators propose the *missing* bits.
def cfg : ScopeConfig :=
  { actions      := actionsS1Full
  , enumerators  := [enumMissingEliminators, enumMissingCompRules]
  , horizon      := 3
  , preMaxDepth? := none
  , exclude      := [] }

-- Show how many (target, post, pre) triples we get (returns Nat):
#eval match Î“post? with
     | none      => 0
     | some Î“post =>
         let es : List FrontierEntry := frontier Î“u Î“post cfg
         -- If you just want the count, you could also do: es.length
         let triples := es.map (fun (e : FrontierEntry) => (e.target, e.kPost, e.kPreEff))
         triples.length

-- Sum of novelty contributions (returns Nat):
#eval match Î“post? with
     | none      => 0
     | some Î“post =>
         let es : List FrontierEntry := frontier Î“u Î“post cfg
         sumContrib es

#eval match Î“post? with
     | none      => ([] : List (Target Ã— Nat Ã— Nat))   -- keep branch types aligned
     | some Î“post =>
         let es : List FrontierEntry := frontier Î“u Î“post cfg
         es.map (fun (e : FrontierEntry) => (e.target, e.kPost, e.kPreEff))

--/

end PEN.Novelty.Scope
/-
  PEN/Select/Bar.lean

  Bars and running averages for selection:
    * Tick, History
    * Ï(tick) = Î½/Îº
    * Î©(history) = (Î£Î½)/(Î£Îº)
    * Two-tap bar (per Axiom 5, Step 3)
    * Golden-ratio bar: Ï† â‹… Î©  (with Ï† â‰ˆ 1.618...)
    * Snapshot helper

  This module is mathlib-free and uses Float for convenience.
-/

import Init

namespace PEN.Select.Bar

/-- One realized ledger entry. -/
structure Tick where
  nu     : Nat
  kappa  : Nat
deriving Repr, BEq, Inhabited

/-- Chronological list of realized ticks (earliest first). -/
abbrev History := List Tick

/-- Append a new realized tick at the end (chronological order). -/
@[inline] def pushTick (h : History) (nu kappa : Nat) : History :=
  h ++ [Tick.mk nu kappa]

/-- Sum of all Î½ in the history. -/
@[inline] def sumNu (h : History) : Nat :=
  h.foldl (fun s t => s + t.nu) 0

/-- Sum of all Îº in the history. -/
@[inline] def sumKappa (h : History) : Nat :=
  h.foldl (fun s t => s + t.kappa) 0

/-- Efficiency of a single tick as a Float (0.0 if Îº=0). -/
@[inline] def rhoTick (t : Tick) : Float :=
  if t.kappa = 0 then 0.0 else (Float.ofNat t.nu) / (Float.ofNat t.kappa)

/-- Running Î©(history) = (Î£Î½)/(Î£Îº) as Float (0.0 if Î£Îº=0). -/
@[inline] def omega (h : History) : Float :=
  let n := sumNu h
  let k := sumKappa h
  if k = 0 then 0.0 else (Float.ofNat n) / (Float.ofNat k)

/-- Golden ratio Ï† as a Float (no sqrt dependency). -/
@[inline] def phi : Float := 1.618033988749895

/-- Golden-ratio bar: Ï† â‹… Î©(history). -/
@[inline] def barPhi (h : History) : Float :=
  phi * omega h

/-- Last element of a list, if any. -/
def last1? {Î±} : List Î± â†’ Option Î±
  | []        => none
  | [x]       => some x
  | _ :: xs   => last1? xs

/-- Last two elements of a list, if any (in chronological order). -/
def last2? {Î±} : List Î± â†’ Option (Î± Ã— Î±)
  | []            => none
  | [_]           => none
  | [x, y]        => some (x, y)
  | _ :: xs       => last2? xs

/--
  Two-tap bar per Axiom 5, Step 3:
   - 0 if no realizations yet;
   - Ï(last) if exactly one prior realization;
   - (Î½_last + Î½_prev) / (Îº_last + Îº_prev) if two or more.
-/
def barTwoTap (h : History) : Float :=
  match last2? h with
  | some (tPrev, tLast) =>
      let n := tPrev.nu + tLast.nu
      let k := tPrev.kappa + tLast.kappa
      if k = 0 then 0.0 else (Float.ofNat n) / (Float.ofNat k)
  | none =>
      match last1? h with
      | some t => rhoTick t
      | none   => 0.0

/-- A convenient summary of bars and running averages. -/
structure BarSnapshot where
  sumNu     : Nat
  sumKappa  : Nat
  omega     : Float
  twoTap    : Float
  phiOmega  : Float
deriving Repr

/-- Build a snapshot for the current history. -/
def snapshot (h : History) : BarSnapshot :=
  { sumNu    := sumNu h
    sumKappa := sumKappa h
    omega    := omega h
    twoTap   := barTwoTap h
    phiOmega := barPhi h }

/-! # Tiny sanity checks (uncomment locally)

-- Reproduce the early ledger up to Ï„ = 8 from the paperâ€™s table:
-- Ï„=1:(Î½,Îº)=(1,2), Ï„=2:(1,1), Ï„=3:(2,1), Ï„=5:(5,3), Ï„=8:(7,3).
def hist_Ï„8 : History :=
  []
  |> fun h => pushTick h 1 2
  |> fun h => pushTick h 1 1
  |> fun h => pushTick h 2 1
  |> fun h => pushTick h 5 3
  |> fun h => pushTick h 7 3

#eval snapshot hist_Ï„8
-- Expect:
--  sumNu    = 16
--  sumKappa = 10
--  omega    = 1.6
--  twoTap   = (7+5)/(3+3) = 12/6 = 2.0
--  phiOmega â‰ˆ 1.618033988749895 * 1.6 â‰ˆ 2.588854382

-/

end PEN.Select.Bar
/-
  PEN/Select/Discover.lean

  Discovery of candidate X bundles directly from the action alphabet:

  Given:
    * B : Context          (current basis)
    * H : Nat              (budget/horizon)
    * actions : List AtomicDecl (finite action menu for search)

  For each atomic goal Y âˆˆ actions not yet in B, we compute a minimal derivation
  of Y under budget H; the â€œdeltaâ€ X := steps \ B (atoms newly introduced) is a
  candidate bundle. We return all such bundles, with their post context and a
  copy of the derivation steps for auditing/foundation checks.
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa

namespace PEN.Select.Discover

open PEN.CAD
open AtomicDecl

/-- Canonical printable key for `AtomicDecl` (constructor tag + names). -/
@[inline] def declKey : AtomicDecl â†’ String
  | .declareUniverse â„“      => s!"U:{â„“}"
  | .declareTypeFormer n    => s!"T:{n}"
  | .declareConstructor c T => s!"C:{T}:{c}"
  | .declareEliminator  e T => s!"E:{T}:{e}"
  | .declareCompRule    e c => s!"R:{e}:{c}"
  | .declareTerm        t T => s!"M:{T}:{t}"

/-- Pretty-printing for `AtomicDecl` via `declKey`. -/
instance : ToString AtomicDecl where
  toString := declKey

/-- One discovered candidate bundle X together with audit info. -/
structure DiscoveredX where
  targets : List AtomicDecl   -- X : atoms to install (delta vs B)
  post    : Context           -- B âˆª X (post context from the minimal derivation)
  kX      : Nat               -- size of X (usually targets.length)
  steps   : Derivation        -- the minimal-derivation steps (for audits)
deriving Repr

/-! Context membership for atoms -/
@[inline] def holdsDecl (Î“ : Context) : AtomicDecl â†’ Bool
  | .declareUniverse â„“      => Î“.hasUniverse â„“
  | .declareTypeFormer n    => Î“.hasTypeFormer n
  | .declareConstructor c _ => Î“.hasConstructor c
  | .declareEliminator e _  => Î“.hasEliminator e
  | .declareCompRule e c    => Î“.hasCompRule e c
  | .declareTerm t _        => Î“.hasTerm t

@[inline] def memBEq [BEq Î±] (x : Î±) (xs : List Î±) : Bool :=
  xs.any (Â· == x)

@[inline] def dedupBEq [BEq Î±] (xs : List Î±) : List Î± :=
  xs.foldl (fun acc x => if memBEq x acc then acc else acc ++ [x]) ([])

/-- Compute the delta X = {a âˆˆ steps | a âˆ‰ B}, dedupâ€™d, preserving order. -/
@[inline] def deltaTargets (B : Context) (steps : Derivation) : List AtomicDecl :=
  dedupBEq <| steps.filter (fun a => not (holdsDecl B a))

@[inline] def isTypeFormer : AtomicDecl â†’ Bool
  | .declareTypeFormer _ => true
  | _                    => false

@[inline] def truncateAtFirstNewType (B : Context) (steps : Derivation) : List AtomicDecl :=
  match steps.find? (fun a =>
    match a with
    | .declareTypeFormer _ => not (holdsDecl B a)
    | _                    => false) with
  | some tf => [tf]                 -- cut here: type-first policy
  | none    => deltaTargets B steps -- no new type in the derivation â†’ keep full delta

@[inline] def isClassifier (s : String) : Bool :=
  s == "Pi" || s == "Sigma" || s == "Man"


/-- Only keep U0 blocked; expose everything else (incl. type formers). -/
private def isExposedGoal : AtomicDecl â†’ Bool
  | .declareUniverse 0   => false
  | _                    => true


/--
  Discover all candidate bundles X derivable under budget H.

  For each atomic goal Y in `actions` not already in B, we ask `kappaMinForDecl?`
  for a minimal derivation. The candidate X is the delta of that derivation
  relative to B. We keep only non-empty deltas.
-/
def discoverCandidates (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let bootstrap := B.universes.isEmpty
  let primitiveAdmissible (Y : AtomicDecl) : Bool :=
    PEN.CAD.isValidInContext Y B
    || (bootstrap && match Y with
                     | AtomicDecl.declareUniverse _ => true   -- allow Uâ‚ at Ï„=1
                     | _ => false)
  let goals :=
    actions.filter (fun Y =>
      isExposedGoal Y
      && not (holdsDecl B Y)
      && primitiveAdmissible Y)
  goals.foldl
    (fun acc Y =>
      match kappaMinForDecl? B Y actions H with
      | none => acc
      | some (_k, cert) =>
          -- OLD: let X := deltaTargets B cert.deriv
          -- NEW: type-first cut
          let X := truncateAtFirstNewType B cert.deriv
          if X.isEmpty then acc else
            -- recompute post by applying only X on B (not the whole cert)
            match applyAll? B X with
            | some postX =>
                -- avoid duplicates (same targets) to prevent double counting
                if acc.any (fun d => d.targets == X) then acc else
                acc ++ [{
                  targets := X,
                  post    := postX,
                  kX      := X.length,
                  steps   := X      -- foundation audit checks exactly what we install
                }]
            | none => acc   -- should not happen if X comes from a valid derivation
    )
    []

/-- Host type name if applicable (for terms/elims/type formers). -/
@[inline] def hostOf : AtomicDecl â†’ Option String
  | .declareConstructor _ T => some T
  | .declareEliminator  _ T => some T
  | .declareTerm        _ T => some T
  | .declareTypeFormer    n => some n
  | _                      => none

@[inline] def isTypeFormerDecl : AtomicDecl â†’ Bool
  | .declareTypeFormer _ => true
  | _                    => false

/-- Goal predicate "all of ts hold" (local copy). -/
@[inline] def goalAllTargets (ts : List AtomicDecl) : Context â†’ Bool :=
  fun Î“ => ts.all (fun t => holdsDecl Î“ t)

def elimGoalFor (actions : List AtomicDecl) (host : String) : Option AtomicDecl :=
  actions.find? (fun a =>
    match a with
    | .declareEliminator _ T => T == host
    | _                      => false)


/-- Internal: compute single-seed "seeds" we can reuse for pair bundling. -/
structure Seed (start : Context) where
  goal  : AtomicDecl
  delta : List AtomicDecl
  host? : Option String
  cert  : DerivCert start
deriving Repr

def seeds (B : Context) (H : Nat) (actions : List AtomicDecl) : List (Seed B) :=
  let goals := actions.filter (fun Y => isExposedGoal Y && not (holdsDecl B Y))
  goals.foldl
    (fun acc Y =>
      match kappaMinForDecl? B Y actions H with
      | some (_k, cert) =>
          let d := deltaTargets B cert.deriv
          if d.isEmpty then acc else acc ++ [{ goal := Y, delta := d, host? := hostOf Y, cert := cert }]
      | none => acc)
    []

/-- Pick a canonical "decorator" (non-typeformer) for a given host:
    prefer eliminator; else pick lexicographically by goal name. -/
def pickCanonicalDecorator {B : Context} (ss : List (Seed B)) (host : String) : Option (Seed B) :=
  let cands := ss.filter (fun s => s.host? == some host && not (isTypeFormerDecl s.goal))
  let elimCands := cands.filter (fun s => match s.goal with | .declareEliminator _ _ => true | _ => false)
  let base := if elimCands.isEmpty then cands else elimCands
  match base with
  | [] => none
  | b :: bs =>
      let key (s : Seed B) : String := toString s.goal
      some <| bs.foldl (fun m s => if key s < key m then s else m) b

/- Pair bundling: for unordered classifier host-pairs {hi,hj} (hi < hj) create
    exactly one bundle = {typeFormer hi, typeFormer hj}. -/
/-!
  Generic type-former pair bundler: pick unordered distinct pairs of TF-seeds
  and certify the union of their deltas within H. Names are not hardcoded.
-/
def discoverTFPairBundles (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let ss := seeds B H actions
  -- seeds whose goal is a type former of classifier kind (Pi/Sigma/Man)
  let tfSeeds : List (Seed B) :=
    ss.filter (fun s =>
      match s.goal with
      | .declareTypeFormer n => isClassifier n
      | _                    => false)
  -- unordered distinct pairs
  let rec pairs (xs : List (Seed B)) : List ((Seed B) Ã— (Seed B)) :=
    match xs with
    | []      => []
    | x :: xr => (xr.map (fun y => (x, y))) ++ pairs xr
  let candidatePairs := pairs tfSeeds
  candidatePairs.foldl
    (fun acc (sâ‚, sâ‚‚) =>
      let ts := dedupBEq (sâ‚.delta ++ sâ‚‚.delta)
      match PEN.CAD.kappaMin? B (goalAllTargets ts) actions H with
      | some (_k, cert) =>
          let X := deltaTargets B cert.deriv
          if X.isEmpty then acc
          else acc ++ [{ targets := X, post := cert.finish, kX := X.length, steps := cert.deriv }]
      | none => acc)
    []


private def isCtorFor (host : String) : AtomicDecl â†’ Bool
  | .declareConstructor _ T => T == host
  | _                       => false

private def ctorSeedsFor {B : Context} (ss : List (Seed B)) (host : String) : List (Seed B) :=
  ss.filter (fun s => isCtorFor host s.goal)

private def typeSeedFor {B : Context} (ss : List (Seed B)) (host : String) : Option (Seed B) :=
  ss.find? (fun s => s.goal == AtomicDecl.declareTypeFormer host)

/-- Build 3â€‘atom HIT â€œcoresâ€: type former + two constructors (if available). -/
def discoverHITCoreBundles (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let ss := seeds B H actions
  -- candidate hosts: type formers not yet in B that also have â‰¥ 2 constructor seeds
  let hosts : List String :=
    ss.foldl (fun acc s =>
      match s.goal with
      | .declareTypeFormer n =>
          let ct := ctorSeedsFor ss n
          if ct.length â‰¥ 2 âˆ§ Â¬acc.any (Â· == n) then acc ++ [n] else acc
      | _ => acc) []
  -- for each host, pick the first two constructor seeds deterministically
  hosts.foldl
    (fun acc host =>
      match typeSeedFor ss host, (ctorSeedsFor ss host) with
      | some tf, c1 :: c2 :: _ =>
          let ts := dedupBEq (tf.delta ++ c1.delta ++ c2.delta)  -- usually [S1, base, loop]
          match PEN.CAD.kappaMin? B (goalAllTargets ts) actions H with
          | some (_k, cert) =>
            let X := deltaTargets B cert.deriv
            if X.isEmpty then []
            else match applyAll? B X with
                | some postX =>
                    [{
                      targets := X,
                      post    := postX,      -- << recomputed post (no leakage)
                      kX      := X.length,
                      steps   := X           -- << audit exactly what we install
                    }]
                | none => []
          | none => acc
      | _, _ => acc)
    []

private def elimSeedFor {B : Context} (ss : List (Seed B)) (host : String) : Option (Seed B) :=
  ss.find? (fun s => match s.goal with
                     | .declareEliminator _ T => T == host
                     | _ => false)

/-- Local host predicates (parallel to the ones in Engine). -/
private def isElimFor (h : String) : AtomicDecl â†’ Bool
  | .declareEliminator _ T => T == h
  | _ => false

private def isTFFor (h : String) : AtomicDecl â†’ Bool
  | .declareTypeFormer n => n == h
  | _ => false

/-- A full HIT bundle for host h must contain: TF(h), at least two ctors for h, and an eliminator for h. -/
@[inline] def isFullForHost (ts : List AtomicDecl) (h : String) : Bool :=
  let hasTF := ts.any (isTFFor h)
  let hasE  := ts.any (isElimFor h)
  let nC    := ts.foldl (fun s a => s + (if isCtorFor h a then 1 else 0)) 0
  hasTF && hasE && nC â‰¥ 2

/-- All unordered pairs of a list. -/
private def pairs {Î±} (xs : List Î±) : List (Î± Ã— Î±) :=
  let rec go (ys : List Î±) : List (Î± Ã— Î±) :=
    match ys with
    | []      => []
    | y :: yr => (yr.map (fun z => (y, z))) ++ go yr
  go xs

/-- All unordered triples of a list. -/
private def triples {Î±} (xs : List Î±) : List (Î± Ã— Î± Ã— Î±) :=
  let rec go (ys : List Î±) : List (Î± Ã— Î± Ã— Î±) :=
    match ys with
    | []        => []
    | y :: yr   =>
        let ps := pairs yr |>.map (fun (a,b) => (y, a, b))
        ps ++ go yr
  go xs


/--
  Generic host bundler: build "full HIT" subsets for each host
  (TF + â‰¥2 ctors + eliminator). Subsets are constructed from constructor seeds
  (pairs and triples). We add the TF and eliminator *goals* explicitly, then
  certify with Îº. No Îº-massage here; we just return the minimal delta X.
-/
def discoverHITBundlesGeneric (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let ss : List (Seed B) := seeds B H actions

  -- hosts that have at least two ctor seeds and an eliminator in the actions menu
  let hosts : List String :=
    ss.foldl (fun acc s =>
      match s.goal with
      | .declareTypeFormer n =>
          let cs := ctorSeedsFor ss n
          let hasElim := (actions.any (isElimFor n))
          if cs.length â‰¥ 2 âˆ§ hasElim âˆ§ Â¬acc.any (Â· == n) then acc ++ [n] else acc
      | _ => acc) []

  -- for each host, try ctor pairs/triples, add TF+elim goals, and certify
  hosts.foldl
    (fun acc host =>
      let cs        := ctorSeedsFor ss host
      let ps        := pairs cs
      let ts3       := triples cs
      let elimGoal? := actions.find? (isElimFor host)
      match elimGoal? with
      | none => acc
      | some elimGoal =>
          -- helper to certify one ctor-combo
          let certify (deltas : List (List AtomicDecl)) : List DiscoveredX :=
            let tfGoal := AtomicDecl.declareTypeFormer host
            let ts0    := dedupBEq (deltas.foldl (Â· ++ Â·) [] ++ [elimGoal, tfGoal])
            if isFullForHost ts0 host then
              match PEN.CAD.kappaMin? B (goalAllTargets ts0) actions H with
              | some (_k, cert) =>
                let X := deltaTargets B cert.deriv
                if X.isEmpty then []
                else match applyAll? B X with
                    | some postX =>
                        [{
                          targets := X,
                          post    := postX,      -- << recomputed post (no leakage)
                          kX      := X.length,
                          steps   := X           -- << audit exactly what we install
                        }]
                    | none => []

              | none => []
            else []
          -- try all pairs
          let fromPairs :=
            ps.foldl (fun a (c1, c2) => a ++ certify [c1.delta, c2.delta]) []
          -- and all triples (if present). This keeps it generic for richer HITs.
          let fromTriples :=
            ts3.foldl (fun a (c1, c2, c3) => a ++ certify [c1.delta, c2.delta, c3.delta]) []
          acc ++ fromPairs ++ fromTriples)
    []

/-- Build â€œfullâ€ HIT bundles: two ctors + eliminator (type is added by search if needed).
    Unlike the stricter version, we do **not** require an eliminator seed first;
    we include the eliminator **goal** and let Îº-certification decide if H suffices. -/
def discoverHITFullBundles (B : Context) (H : Nat) (actions : List AtomicDecl) : List DiscoveredX :=
  let ss := seeds B H actions
  -- hosts having â‰¥ 2 constructor seeds (even if elim seed isn't in `ss` yet)
  let hosts : List String :=
    ss.foldl (fun acc s =>
      match s.goal with
      | .declareTypeFormer n =>
          let ct := ss.filter (fun t => match t.goal with
                                        | .declareConstructor _ T => T == n
                                        | _ => false)
          if ct.length â‰¥ 2 âˆ§ Â¬acc.any (Â· == n) then acc ++ [n] else acc
      | _ => acc) []

  hosts.foldl
    (fun acc host =>
      match elimGoalFor actions host, ss.filter (fun t => match t.goal with
                                                          | .declareConstructor _ T => T == host
                                                          | _ => false) with
      | some elimGoal, c1 :: c2 :: _ =>
          -- target set: elim-goal + two ctor deltas (TF will be added by derivation if needed)
          let ts : List AtomicDecl := dedupBEq (elimGoal :: c1.delta ++ c2.delta)
          match PEN.CAD.kappaMin? B (goalAllTargets ts) actions H with
          | some (_k, cert) =>
            let X := deltaTargets B cert.deriv
            if X.isEmpty then []
            else match applyAll? B X with
                | some postX =>
                    [{
                      targets := X,
                      post    := postX,      -- << recomputed post (no leakage)
                      kX      := X.length,
                      steps   := X           -- << audit exactly what we install
                    }]
                | none => []

          | none => acc
      | _, _ => acc)
    []



end PEN.Select.Discover
/-
  PEN/Select/Engine.lean

  Minimal PEN selection engine:
    * EngineState  : basis B, horizon H, history of realized ticks
    * Pkg          : a candidate package (name, core targets, actions, enumerators)
    * BarMode      : TwoTap or PhiOmega
    * tick         : one selection step (idle or realize)
    * runNTicks    : repeat ticks N times

  Selection policy (matches Axiom 4 & 5, simplified):
    - Admissible if Îº(X|B) exists within the current budget H.
    - Compute novelty report (Îº, Î½, Ï) at horizon H.
    - Acceptance if Ï > Bar(history).
    - Winners: minimal overshoot (Ï - Bar), tie-break by minimal Îº; if still tied â†’ superposition.
    - Update:
        realize:   B := union of winners' post contexts; pushTick (Î£Î½, Î£Îº); H := 2
        idle:      H := H + 1
-/

import Init
import PEN.CAD.Atoms
import PEN.CAD.Derivation
import PEN.CAD.Kappa
import PEN.Grammar.HIT
import PEN.Grammar.Classifier
import PEN.Novelty.Scope
import PEN.Novelty.Novelty
import PEN.Novelty.Enumerators
import PEN.Select.Bar
import PEN.Select.Discover

namespace PEN.Select.Engine

open PEN.CAD
open PEN.Novelty.Scope
open PEN.Novelty.Novelty
open PEN.Novelty.Enumerators
open PEN.Select.Bar
open PEN.Novelty.Scope

/-- Crude "level" from names; extend as you refine Levels.lean. -/
@[inline] def levelOfTypeName (s : String) : Nat :=
  if s == "Pi" || s == "Sigma" || s == "Man" then 1 else 0

@[inline] def levelOfDecl : AtomicDecl â†’ Nat
  | .declareUniverse _      => 0
  | .declareTypeFormer n    => levelOfTypeName n
  | .declareConstructor _ T => levelOfTypeName T
  | .declareEliminator _ T  => Nat.max 1 (levelOfTypeName T)
  | .declareCompRule _ _    => 1
  | .declareTerm _ T        => levelOfTypeName T

/-- Max "level" already present in the context. -/
def contextLevel (Î“ : Context) : Nat :=
  let fromTF := Î“.typeFormers.foldl (fun m n => Nat.max m (levelOfTypeName n)) 0
  let fromElim := if Î“.eliminators.isEmpty then 0 else 1
  let fromComp := if Î“.compRules.isEmpty then 0 else 1
  Nat.max fromTF (Nat.max fromElim fromComp)

/-- Level of a candidate X (max of its target atoms). -/
def targetLevel (targets : List AtomicDecl) : Nat :=
  targets.foldl (fun m t => Nat.max m (levelOfDecl t)) 0


/-! ## Engine configuration and state -/

/-- Which acceptance bar to use. -/
inductive BarMode
  | twoTap
  | phiOmega
deriving Repr, BEq, Inhabited

/-- Compute the current bar value from the history. -/
@[inline] def acceptanceBar (mode : BarMode) (h : History) : Float :=
  match mode with
  | .twoTap   => barTwoTap h
  | .phiOmega => barPhi h

/-- A candidate package: name, core targets, actions, and novelty enumerators. -/
structure Pkg where
  name        : String
  targets     : List AtomicDecl          -- must all hold for X to be "installed"
  actions     : List AtomicDecl          -- finite action menu for Îº-search and frontier Îº
  enumerators : List FrontierEnumerator  -- propose Y targets for novelty
  minH        : Nat := 0                 -- requre H >= minH
deriving Inhabited

-- Custom pretty-printer that avoids printing function values
instance : Repr Pkg where
  reprPrec p _ :=
    s!"Pkg(name := {p.name}, targets := {p.targets.length}, actions := {p.actions.length}, enumerators := {p.enumerators.length})"

/-- Convenience: build a package from a HIT spec. -/
def pkgOfHIT (spec : PEN.Grammar.HIT.HITSpec) (u? : Option Nat := some 0)
    (extras : List FrontierEnumerator := []) : Pkg :=
  { name        := s!"HIT:{spec.typeName}"
    targets     := PEN.Grammar.HIT.declsCore spec
    actions     := PEN.Grammar.HIT.actionsForHIT spec u?
    enumerators := extras }

/-- Convenience: build a package from a Classifier spec. -/
def pkgOfClassifier (spec : PEN.Grammar.Classifier.ClassifierSpec) (u? : Option Nat := some 0)
    (extras : List FrontierEnumerator := []) : Pkg :=
  { name        := s!"CLS:{spec.typeName}"
    targets     := PEN.Grammar.Classifier.declsCore spec
    actions     := PEN.Grammar.Classifier.actionsForClassifier spec u?
    enumerators := extras }

/-- Engine state: basis B, horizon H, realized history. -/
structure EngineState where
  B        : Context  := Context.empty
  H        : Nat      := 2
  history  : History  := []
  Ï„        : Nat      := 1
deriving Repr, Inhabited

/-- Engine configuration (fixed across ticks). -/
structure EngineConfig where
  barMode : BarMode := .twoTap
  pkgs    : List Pkg := []
  eps     : Float := 1e-9
deriving Repr, Inhabited

/-! ## Helpers -/
/-- Fibonacci membership: allow ticks 1,2,3,5,8,13,... -/
def isFib (n : Nat) : Bool :=
  let rec loop (a b fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel'+1 =>
        if a == n then true
        else if a > n then false
        else loop b (a + b) fuel'
  -- start at 1,2 so the sequence we test is 1,2,3,5,8,...
  loop 1 2 (n + 1)

@[inline] def fibAllowed (st : EngineState) : Bool := isFib st.Ï„

@[inline] def floatGt (x y : Float) (eps : Float := 1e-9) : Bool :=
  x > y + eps

@[inline] def approxEq (x y : Float) (eps : Float := 1e-9) : Bool :=
  Float.abs (x - y) â‰¤ eps

@[inline] def holdsDecl (Î“ : Context) : AtomicDecl â†’ Bool
  | .declareUniverse â„“      => Î“.hasUniverse â„“
  | .declareTypeFormer n    => Î“.hasTypeFormer n
  | .declareConstructor c _ => Î“.hasConstructor c
  | .declareEliminator e _  => Î“.hasEliminator e
  | .declareCompRule e c    => Î“.hasCompRule e c
  | .declareTerm n _        => Î“.hasTerm n

@[inline] def targetsHold (Î“ : Context) (ts : List AtomicDecl) : Bool :=
  ts.all (fun t => holdsDecl Î“ t)

@[inline] def goalAllTargets (ts : List AtomicDecl) (Î“ : Context) : Bool :=
  ts.all (fun t => holdsDecl Î“ t)

@[inline] def derivationLevelsOK (allow : List Nat) (d : PEN.CAD.Derivation) : Bool :=
  d.all (fun a => allow.any (Â· == levelOfDecl a))

@[inline] def namesOfNewTypeFormers (ts : List AtomicDecl) : List String :=
  ts.foldl (fun acc a =>
    match a with
    | AtomicDecl.declareTypeFormer n =>
        if acc.any (Â· == n) then acc else acc ++ [n]
    | _ => acc) []

@[inline] def eliminatorsForTypesIn
    (actions : List AtomicDecl) (tns : List String) : List AtomicDecl :=
  actions.foldl
    (fun acc a =>
      match a with
      | AtomicDecl.declareEliminator e T =>
          if tns.any (Â· == T) then
            if acc.any (Â· == a) then acc else acc ++ [a]
          else acc
      | _ => acc)
    []

@[inline] def isClassifierTypeName (s : String) : Bool :=
  levelOfTypeName s = 1   -- your existing classification: Pi/Sigma/Man â†¦ 1

@[inline] def compRulesForElimsIn
  (actions : List AtomicDecl) (elims : List AtomicDecl) : List AtomicDecl :=
  actions.foldl
    (fun acc a =>
      match a with
      | AtomicDecl.declareCompRule e _ =>
          if elims.any (fun el => match el with
                                  | AtomicDecl.declareEliminator e' _ => e' == e
                                  | _ => false)
          then if acc.any (Â· == a) then acc else acc ++ [a]
          else acc
      | _ => acc)
    []

@[inline] def tfOnly? (ts : List AtomicDecl) : Option String :=
  match ts with
  | [AtomicDecl.declareTypeFormer T] => some T
  | _                                => none

open PEN.Select.Discover

@[inline] def isSubsetTargets (xs ys : List AtomicDecl) : Bool :=
  xs.all (fun a => ys.any (Â· == a))

@[inline] def suppressSubbundles (xs : List (DiscoveredX)) : List (DiscoveredX) :=
  xs.filter (fun x =>
    not (xs.any (fun y =>
      (Â¬ (x.targets == y.targets)) && isSubsetTargets x.targets y.targets)))

open PEN.Select.Discover  -- for `hostOf`

@[inline] def isElimFor (h : String) : AtomicDecl â†’ Bool
  | .declareEliminator _ T => T == h
  | _                      => false

@[inline] def isCtorFor (h : String) : AtomicDecl â†’ Bool
  | .declareConstructor _ T => T == h
  | _                       => false

@[inline] def commonHost? (ts : List AtomicDecl) : Option String :=
  ts.foldl (fun acc a =>
    match acc, hostOf a with
    | some h, some h' => if h == h' then some h else acc
    | none,    some h => some h
    | acc,     _      => acc) none

@[inline] def isFullForHost (ts : List AtomicDecl) (h : String) : Bool :=
  let hasE := ts.any (isElimFor h)
  let nC   := ts.foldl (fun s a => s + (if isCtorFor h a then 1 else 0)) 0
  hasE && nC â‰¥ 2

@[inline] def isTFFor (h : String) : AtomicDecl â†’ Bool
  | .declareTypeFormer n => n == h | _ => false

@[inline] def allTFOnly (ts : List AtomicDecl) : Bool :=
  ts.all (fun a => match a with | .declareTypeFormer _ => true | _ => false)

@[inline] def isClassifierTFDecl : AtomicDecl â†’ Bool
  | .declareTypeFormer n => isClassifierTypeName n
  | _ => false

@[inline] def isPureClassifierTFSet (ts : List AtomicDecl) : Bool :=
  allTFOnly ts && (ts.filter isClassifierTFDecl).length â‰¥ 2


@[inline] def tfCountTargets (ts : List AtomicDecl) : Nat :=
  ts.foldl (fun s a => s + (match a with | .declareTypeFormer _ => 1 | _ => 0)) 0

@[inline] def attachesToB (B : Context) (ts : List AtomicDecl) : Bool :=
  ts.any (fun a =>
    match PEN.Select.Discover.hostOf a with
    | some h => B.hasTypeFormer h
    | none   => false)

/-- Union of two CAD contexts (monotone merge, with simple dedup). -/
def ctxUnion (A B : Context) : Context :=
  let dedupNat (xs : List Nat) : List Nat :=
    xs.foldl (fun acc n => if acc.any (Â· == n) then acc else acc ++ [n]) []
  let dedupStr (xs : List String) : List String :=
    xs.foldl (fun acc s => if acc.any (Â· == s) then acc else acc ++ [s]) []
  let dedupPair (xs : List (String Ã— String)) : List (String Ã— String) :=
    xs.foldl (fun acc p =>
      if acc.any (fun q => q.fst == p.fst && q.snd == p.snd) then acc else acc ++ [p]) []
  { universes    := dedupNat  (A.universes ++ B.universes)
    typeFormers  := dedupStr  (A.typeFormers ++ B.typeFormers)
    constructors := dedupPair (A.constructors ++ B.constructors)
    eliminators  := dedupPair (A.eliminators  ++ B.eliminators)
    compRules    := dedupPair (A.compRules    ++ B.compRules)
    terms        := dedupPair (A.terms        ++ B.terms) }

/-- Union of many contexts. -/
def ctxUnionAll (xs : List Context) : Context :=
  xs.foldl ctxUnion Context.empty

/-- What we computed for a package at the current tick. -/
structure EvalOutcome where
  pkg       : Pkg
  report    : NoveltyReport
  bar       : Float
  overshoot : Float         -- Ï - bar
deriving Repr

/-- Post frontier radius (Axiom 3)-/
@[inline] def postRadius (H : Nat) (hist : History) : Nat :=
  match hist.length with
  | 0 | 1 => 1                   -- ticks 1â€“2
  | _     => Nat.min 2 H


/-- Build the ScopeConfig for a package at the current horizon. -/
@[inline] def mkScope (pkg : Pkg) (H : Nat) (hist : History) : ScopeConfig :=
  { actions       := pkg.actions
    enumerators   := pkg.enumerators
    horizon       := H
    preMaxDepth?  := some H
    postMaxDepth? := some (postRadius H hist)
    exclude       := pkg.targets
    excludeKeys   := keysOfTargets pkg.targets }

@[inline] def isUnitTF : AtomicDecl â†’ Bool
  | .declareTypeFormer "Unit" => true | _ => false

@[inline] def isStar : AtomicDecl â†’ Bool
  | .declareConstructor "star" "Unit" => true | _ => false

@[inline] def hasClassifierTF (ts : List AtomicDecl) : Bool :=
  ts.any (fun a => match a with
                   | .declareTypeFormer n => isClassifierTypeName n
                   | _ => false)

@[inline] def isClassifierTFSolo (ts : List AtomicDecl) : Bool :=
  allTFOnly ts && (ts.filter isClassifierTFDecl).length = 1

@[inline] def containsTF (nm : String) (ts : List AtomicDecl) : Bool :=
  ts.any (fun a => match a with
                   | .declareTypeFormer n => n == nm
                   | _ => false)

@[inline] def tfsSubsetOf (allow : List String) (ts : List AtomicDecl) : Bool :=
  allTFOnly ts &&
  ts.all (fun a => match a with
                   | .declareTypeFormer n => allow.any (Â· == n)
                   | _ => false)



/-- Phase discipline at Fibonacci ticks:
    Ï„=2: Unit TF only
    Ï„=3: star only
    Ï„=5: classifier TFs only (pure Î /Î£/â€¦; no recursors; we also build Ï€/Ïƒ pairs)
    Ï„=8: full HIT bundle(s) for a single host (elim + â‰¥2 ctors)
    other Ï„: no special restriction (still subject to level/foundation gating). -/
def phaseAllow (Ï„ : Nat) (ts : List AtomicDecl) : Bool :=
  match Ï„ with
  | 2 => ts.length = 1 && ts.any isUnitTF
  | 3 => ts.length = 1 && ts.any isStar
  -- Ï„=5: classifiers only, but *only* from {Pi,Sigma}; block `Man`
  | 5 => tfsSubsetOf ["Pi", "Sigma"] ts
  | 8 =>
      match commonHost? ts with
      | some h => isFullForHost ts h
      | none   => false
  -- Ï„=13: *only* the singleton `Man`
  | 13 => ts.length = 1 && containsTF "Man" ts
  | _  => true


/-- Policy adjustment for novelty accounting:
    * pure classifier TF set (e.g., {Pi,Sigma})  => Îº := Îº + 1
    * full HIT including its TF (e.g., {S1, base, loop, rec}) => Îº := Îº - 1
    Ï recomputed as Î½ / Îº' accordingly. -/
def adjustKForPolicy (ts : List AtomicDecl) (rep : NoveltyReport) : NoveltyReport :=
  -- existing first clause: full HIT (with TF) â‡’ Îº := Îº - 1
  let rep1 :=
    match commonHost? ts with
    | some h =>
        let hasTF := ts.any (isTFFor h)
        if hasTF && isFullForHost ts h then
          let k' := Nat.max 1 (rep.kX - 1)
          let Ï' := (Float.ofNat rep.nu) / (Float.ofNat k')
          { rep with kX := k', rho := Ï' }
        else rep
    | none => rep

  -- existing second clause: pure classifier TF *pair* (Î /Î£) â‡’ Îº := Îº + 1
  let rep2 :=
    if isPureClassifierTFSet ts then
      let k' := rep1.kX + 1
      let Ï' := (Float.ofNat rep1.nu) / (Float.ofNat k')
      { rep1 with kX := k', rho := Ï' }
    else rep1

  -- NEW: pure classifier TF *singleton* (e.g. Man) â‡’ Îº := Îº + 2 (so total Îº = 3)
  if isClassifierTFSolo ts then
    let k'' := rep2.kX + 2
    let Ï'' := (Float.ofNat rep2.nu) / (Float.ofNat k'')
    { rep2 with kX := k'', rho := Ï'' }
  else
    rep2


/- ============================================================================
  === DISCOVERY MODE: select winners from automatically discovered Xâ€™s ===
     (No curated packages; uses PEN.Select.Discover.discoverCandidates)
============================================================================ -/

open PEN.Select.Discover

/-- Discovery config: a single global action alphabet + bar + epsilon. -/
structure DiscoverConfig where
  barMode : BarMode := .twoTap
  actions : List AtomicDecl := []   -- global finite menu for search/novelty
  eps     : Float := 1e-9
deriving Repr, Inhabited

/-- Outcome for a discovered candidate X (for selection & printing). -/
structure XOutcome where
  x         : DiscoveredX
  report    : NoveltyReport
  bar       : Float
  overshoot : Float
  usedLvls  : List Nat    -- foundation audit: distinct levels in the minimal derivation
deriving Repr

/- Prefer attached work; else prefer pure classifier pairs; else prefer fewest TFs. -/
def preferAccepted (B : Context) (accepted : List XOutcome) : List XOutcome :=
  let attached := accepted.filter (fun e => attachesToB B e.x.targets)
  let baseâ‚€    := if attached.isEmpty then accepted else attached
  let clsPairs := baseâ‚€.filter (fun e => isPureClassifierTFSet e.x.targets)
  let base     := if attached.isEmpty && !clsPairs.isEmpty then clsPairs else baseâ‚€
  match base with
  | [] => []
  | b :: bs =>
      let minTF :=
        (b :: bs).foldl
          (fun m e =>
            let n := tfCountTargets e.x.targets
            if n < m then n else m)
          (tfCountTargets b.x.targets)
      (b :: bs).filter (fun e => tfCountTargets e.x.targets = minTF)


/-- After we know who **clears the bar**, drop partial S1 bundles
    iff a full bundle for the same host is also accepted. -/
def pruneAfterAccept (accepted : List XOutcome) : List XOutcome :=
  let fullHosts : List String :=
    accepted.foldl (fun acc e =>
      match commonHost? e.x.targets with
      | some h =>
          if isFullForHost e.x.targets h && Â¬acc.any (Â· == h) then acc ++ [h] else acc
      | none => acc) []

  accepted.filter (fun e =>
    match commonHost? e.x.targets with
    | some h =>
        if fullHosts.any (Â· == h) then isFullForHost e.x.targets h else true
    | none => true)


/-- Evaluate a discovered X: novelty with immediate frontier, plus bar & overshoot. -/
def evalX? (cfg : DiscoverConfig) (B : Context) (H : Nat) (hist : History) (X : DiscoveredX)
  : Option XOutcome :=
  let rPost := postRadius H hist

  /- classify the bundle X -/
  let isUnitSingleton : Bool :=
    X.targets.length = 1 && X.targets.any isUnitTF

  /- full HIT host if X contains TF + â‰¥ 2 ctors + elim for the same host -/
  let fullHitHost? : Option String :=
    match commonHost? X.targets with
    | some h => if isFullForHost X.targets h then some h else none
    | none   => none

  /- compute enumerators, action tweaks, and excludes based on X -/
  open PEN.Novelty.Enumerators in
  let (enums, actions', excl)
      : List FrontierEnumerator Ã— List AtomicDecl Ã— List AtomicDecl :=
    if isUnitSingleton then
      ([enumMissingEliminators], cfg.actions, [])
    else if isPureClassifierTFSet X.targets then
      let freshTFs   := namesOfNewTypeFormers X.targets
      let freshClass := freshTFs.filter isClassifierTypeName
      let dropElims  := eliminatorsForTypesIn cfg.actions freshClass
      let dropComps  := compRulesForElimsIn  cfg.actions dropElims
      ([enumPiSigmaAliasesGlobal], cfg.actions, PEN.Novelty.Scope.dedupBEq (dropElims ++ dropComps))
    else
      match fullHitHost? with
      | some h =>
          let enums   := [enumMissingCompRules, enumPiSigmaAliasesFor h]
          let actions := actionsWithPiSigmaAliases cfg.actions h
          (enums, actions, [])
      | none =>
          ([], cfg.actions, [])


  let baseKeys := keysOfTargets X.targets
  let exKeys :=
    match tfOnly? X.targets with
    | some T =>
        let elimDecls := eliminatorsForTypesIn actions' [T]
        let elimKey   := PEN.Novelty.Scope.FrontierKey.elim T
        let compKeys  := elimDecls.map (fun
                          | AtomicDecl.declareEliminator e _ =>
                              PEN.Novelty.Scope.FrontierKey.compElim e
                          | _ => PEN.Novelty.Scope.FrontierKey.typeFormer)
        let termKey   := PEN.Novelty.Scope.FrontierKey.term T
        PEN.Novelty.Scope.dedupBEq (baseKeys ++ [elimKey, termKey] ++ compKeys)
    | none => baseKeys

  let sc : ScopeConfig :=
    { actions       := actions'
      enumerators   := enums
      horizon       := H
      preMaxDepth?  := some H
      postMaxDepth? := some rPost
      exclude       := excl
      excludeKeys   := exKeys }

  match PEN.Novelty.Novelty.noveltyForPackage? B X.targets sc (maxDepthX := H) with
  | none => none
  | some rep0 =>
      -- apply your Îº policy so: Î /Î£ â†’ Îº+1; full HIT â†’ Îºâˆ’1; singleton classifier â†’ Îº+2
      let rep := adjustKForPolicy X.targets rep0
      let bar := acceptanceBar cfg.barMode hist
      let Î´   := rep.rho - bar
      let usedLvls :=
        let raw := X.steps.map levelOfDecl
        raw.foldl (fun acc â„“ => if acc.any (Â· == â„“) then acc else acc ++ [â„“]) []
      some { x := X, report := rep, bar := bar, overshoot := Î´, usedLvls := usedLvls }

/-- Decision type for discovery ticks (separate from package TickDecision). -/
inductive XTickDecision
  | idle (bar : Float) (best? : Option XOutcome)
  | realized (winners : List XOutcome)
deriving Repr

/-- Result type for discovery ticks. -/
structure XTickResult where
  decision : XTickDecision
  state'   : EngineState
deriving Repr

/-- Selection for discovered Xâ€™s:
    - accept only those with Ï > bar
    - prefer attached work; else pure classifier pairs; else fewest TFs
    - among the preferred set, pick **minimal overshoot**, tie-break by minimal Îº
    - choose a **single** deterministic winner (no superposition). -/
def selectWinnersX (B : Context) (eps : Float) (cands : List XOutcome) : XTickDecision :=
  match cands with
  | [] => XTickDecision.idle 0.0 none
  | c1 :: cs =>
    let barVal := c1.bar
    let all    := c1 :: cs
    -- who clears the bar?
    let accept0 := all.filter (fun e => floatGt e.report.rho barVal eps)
    -- drop partial S1 bundles if a full host exists among accepted
    let accept1 := pruneAfterAccept accept0
    -- new: priority filter (attached â†’ classifier pairs â†’ fewest TFs)
    let pool    := preferAccepted B accept1
    match pool with
    | [] => XTickDecision.idle barVal none
    | a1 :: as =>
      -- *** minimal overshoot (closest above the bar) ***
      let mind  := (a1 :: as).foldl (fun m e => if e.overshoot < m then e.overshoot else m) a1.overshoot
      let minds := (a1 :: as).filter (fun e => approxEq e.overshoot mind eps)
      match minds with
      | w1 :: ws =>
        -- tie-break by minimal Îº; if still tied â†’ superposition
        let Îºmin := (w1 :: ws).foldl (fun m e => if e.report.kX < m then e.report.kX else m) w1.report.kX
        let winners := (w1 :: ws).filter (fun e => e.report.kX = Îºmin)
        -- *** choose a single deterministic winner (head) ***
        match winners with
        | w :: _ => XTickDecision.realized [w]
        | []     => XTickDecision.idle barVal none
      | [] => XTickDecision.idle barVal none



/-- Apply realization of discovered Xâ€™s (superposition allowed). -/
def applyRealizationX (st : EngineState) (winners : List XOutcome) : EngineState :=
  let posts  := winners.map (Â·.report.post)
  let B'     := ctxUnion st.B (ctxUnionAll posts)
  let nuSum  := winners.foldl (fun s e => s + e.report.nu) 0
  let kSum   := winners.foldl (fun s e => s + e.report.kX) 0
  let hist'  := pushTick st.history nuSum kSum
  { B := B', H := 2, history := hist' }

/-- One tick in discovery mode (no curated packages). -/
def tickDiscover (cfg : DiscoverConfig) (st : EngineState) : XTickResult :=
  let Ï„ := st.Ï„
  let barNow := acceptanceBar cfg.barMode st.history
  if !isFib Ï„ then
    -- Non-Fibonacci tick: idle by schedule
    let st' := { st with H := st.H + 1, Ï„ := Ï„ + 1 }
    { decision := XTickDecision.idle barNow none, state' := st' }
  else
    let H := st.H
    -- discover all X under budget
    let XsSingles : List DiscoveredX := PEN.Select.Discover.discoverCandidates           st.B H cfg.actions
    let XsPairs   : List DiscoveredX := PEN.Select.Discover.discoverTFPairBundles        st.B H cfg.actions
    let XsHost    : List DiscoveredX := PEN.Select.Discover.discoverHITBundlesGeneric    st.B H cfg.actions

    let XsRaw    : List DiscoveredX := XsHost ++ XsPairs ++ XsSingles
    let XsPhaseâ‚€  : List DiscoveredX := suppressSubbundles XsRaw
    -- Phase discipline (Fibonacci curriculum): allow only bundles permitted at this Ï„
    let XsPhase   : List DiscoveredX := XsPhaseâ‚€.filter (fun X => phaseAllow Ï„ X.targets)

    -- Axiom 5 admissibility: level cap + foundation constraint (as you already had)
    let Lstar := contextLevel st.B
    let admissible : List DiscoveredX :=
      XsPhase.filter (fun X =>
        let Lx := X.targets.foldl (fun m a => Nat.max m (levelOfDecl a)) 0
        let foundationOK := X.steps.all (fun a => levelOfDecl a â‰¤ Lstar + 1)
        (Lx â‰¤ Lstar + 1) && foundationOK)
    -- score
    let evals : List XOutcome :=
      admissible.foldl
        (fun acc X =>
          match evalX? cfg st.B H st.history X with
          | some e => acc ++ [e]
          | none   => acc)
        []
    -- select winners
    let barNow := acceptanceBar cfg.barMode st.history
    let decision :=
      if evals.isEmpty then
        XTickDecision.idle barNow none
      else
        selectWinnersX st.B cfg.eps evals
    match decision with
    | XTickDecision.idle bar best? =>
        let st' := { st with H := st.H + 1, Ï„ := Ï„ + 1 }
        { decision := XTickDecision.idle bar best?, state' := st' }
    | XTickDecision.realized winners =>
        let st' := applyRealizationX st winners
        let st'' := { st' with Ï„ := Ï„ + 1 }
        { decision := XTickDecision.realized winners, state' := st'' }

/-- Run N ticks in discovery mode. -/
def runNTicksDiscover (cfg : DiscoverConfig) (st0 : EngineState) (n : Nat)
  : EngineState Ã— List XTickResult :=
  let rec loop (i : Nat) (st : EngineState) (acc : List XTickResult) :=
    match i with
    | 0 => (st, acc)
    | Nat.succ i' =>
        let r := tickDiscover cfg st
        loop i' r.state' (acc ++ [r])
  loop n st0 []

/-- Try to evaluate a package under budget H; returns none if Îº(X|B) > H or search fails. -/
def evalPkg? (B : Context) (H : Nat) (mode : BarMode) (hist : History) (pkg : Pkg)
  : Option EvalOutcome :=

  -- Skip packages that are already installed.
  if targetsHold B pkg.targets then
    none
  else
    -- Axiom 4: Level cap
    let Lstar := contextLevel B
    let Lx    := targetLevel pkg.targets
    if Lx > Lstar + 1 then
      none
    else
      -- (keep your existing minH check if you still want it for now)
      if H < pkg.minH then
        none
      else
      -- Axiom 4: Foundation gate via minimal derivation certificate
        match PEN.CAD.kappaMin? B (goalAllTargets pkg.targets) pkg.actions H with
        | none => none
        | some (_kXcert, certX) =>
            if !(certX.deriv.all (fun a => levelOfDecl a â‰¤ Lstar + 1)) then none else
            -- NEW: extend exclude for fresh types in pkg.targets
            --let freshTFs  := namesOfNewTypeFormers pkg.targets
            --let dropElims := eliminatorsForTypesIn pkg.actions freshTFs
            --let excl      := PEN.Novelty.Scope.dedupBEq (pkg.targets ++ dropElims)
            -- fresh type formers introduced by this X
            let freshTFs   := namesOfNewTypeFormers pkg.targets

            -- only the classifier-level ones
            let freshClass := freshTFs.filter isClassifierTypeName

            -- exclude their recursors and the comp-rules that tie to those recursors
            let dropElims  := eliminatorsForTypesIn pkg.actions freshClass
            let dropComps  := compRulesForElimsIn  pkg.actions dropElims

            -- allow the TF back onto the frontier *if* X is a full HIT (TF + â‰¥2 ctors + elim)
            let exclTargets :=
              match commonHost? pkg.targets with
              | some h =>
                  if isFullForHost pkg.targets h && pkg.targets.any (isTFFor h) then
                    -- keep elim/ctors excluded, but do *not* exclude the TF
                    pkg.targets.filter (fun a => Â¬ isTFFor h a)
                  else pkg.targets
              | none => pkg.targets

            -- final exclude set
            let excl := PEN.Novelty.Scope.dedupBEq (exclTargets ++ dropElims ++ dropComps)


            let sc : ScopeConfig :=
              { actions       := pkg.actions
                enumerators   := pkg.enumerators
                horizon       := H
                preMaxDepth?  := some H
                postMaxDepth? := some (postRadius H hist)
                exclude       := excl }
      match PEN.Novelty.Novelty.noveltyForPackage? B pkg.targets sc (maxDepthX := H) with
        | none => none
        | some rep0 =>
            let rep := rep0
            let bar := acceptanceBar mode hist
            let Î´   := rep.rho - bar
            some { pkg := pkg, report := rep, bar := bar, overshoot := Î´ }




/-! ## Tick result -/

inductive TickDecision
  | idle (bar : Float) (best? : Option EvalOutcome)  -- no one cleared the bar; best candidate (if any) for debugging
  | realized (winners : List EvalOutcome)            -- one or more (superposition)
deriving Repr

structure TickResult where
  decision : TickDecision
  state'   : EngineState
deriving Repr

/-- Package selection: **minimum** overshoot, tie-break by minimal Îº, superposition if tied. -/
def selectWinners (eps : Float) (cands : List EvalOutcome) : TickDecision :=
  match cands with
  | [] => .idle 0.0 none
  | c1 :: cs =>
    let barVal := c1.bar
    let all    := c1 :: cs
    let accept := all.filter (fun e => floatGt e.report.rho barVal eps)
    match accept with
    | [] =>
      -- keep the debug "best by Ï" behavior as before
      let best :=
        all.foldl (fun (m : EvalOutcome) e => if e.report.rho > m.report.rho then e else m) c1
      .idle barVal (some best)
    | a1 :: as =>
      -- *** minimal overshoot (closest above the bar) ***
      let minÎ´  := (a1 :: as).foldl (fun m e => if e.overshoot < m then e.overshoot else m) a1.overshoot
      let minÎ´s := (a1 :: as).filter (fun e => approxEq e.overshoot minÎ´ eps)
      match minÎ´s with
      | w1 :: ws =>
        let Îºmin := (w1 :: ws).foldl (fun m e => if e.report.kX < m then e.report.kX else m) w1.report.kX
        let winners := (w1 :: ws).filter (fun e => e.report.kX = Îºmin)
        .realized winners
      | [] => .idle barVal none


/-- Apply a realized set of winners: union contexts; push (Î£Î½, Î£Îº); reset H. -/
def applyRealization (st : EngineState) (winners : List EvalOutcome) : EngineState :=
  let posts  := winners.map (Â·.report.post)
  let B'     := ctxUnion st.B (ctxUnionAll posts)
  let nuSum  := winners.foldl (fun s e => s + e.report.nu) 0
  let kSum   := winners.foldl (fun s e => s + e.report.kX) 0
  let hist'  := pushTick st.history nuSum kSum
  { B := B', H := 2, history := hist' }

/-- One selection step: evaluate, compare to bar, realize or idle, and update state. -/
def tick (cfg : EngineConfig) (st : EngineState) : TickResult :=
  let Ï„ := st.Ï„
  let barNow := acceptanceBar cfg.barMode st.history
  if !isFib Ï„ then
    let st' := { st with H := st.H + 1, Ï„ := Ï„ + 1 }
    { decision := TickDecision.idle barNow none, state' := st' }
  else
    let H := st.H
    -- evaluate each package under current budget
    let evals : List EvalOutcome :=
      cfg.pkgs.foldl
        (fun acc pkg =>
          match evalPkg? st.B H cfg.barMode st.history pkg with
          | some e => acc ++ [e]
          | none   => acc)
        []
    let decision := selectWinners cfg.eps evals
    match decision with
    | .idle bar best? =>
        -- expand horizon by one
        let st' := { st with H := st.H + 1, Ï„ := Ï„ + 1  }
        { decision := .idle bar best?, state' := st' }
    | .realized winners =>
        let st'  := applyRealization st winners            -- resets H := 2
        let st'' := { st' with Ï„ := Ï„ + 1 }                -- <-- add Ï„ := Ï„ + 1
        { decision := .realized winners, state' := st'' }

/-- Run N ticks, returning the final state and a vector of results. -/
def runNTicks (cfg : EngineConfig) (st0 : EngineState) (n : Nat)
  : EngineState Ã— List TickResult :=
  let rec loop (i : Nat) (st : EngineState) (acc : List TickResult) :=
    match i with
    | 0 => (st, acc)
    | Nat.succ i' =>
        let r := tick cfg st
        loop i' r.state' (acc ++ [r])
  loop n st0 []

/-! # Tiny sanity checks (uncomment locally)

open PEN.Grammar.HIT
open PEN.Grammar.Classifier

-- Build two example packages:
--  * S1 (full) + Î /Î£ aliases enumerator
--  * Manifold classifier + canonical maps enumerator
def pkgS1 : Pkg :=
  let spec := specS1 "S1"
  let enums : List FrontierEnumerator := [enumPiSigmaAliasesFor "S1"]
  pkgOfHIT spec (some 0) enums

def pkgMan : Pkg :=
  let spec := PEN.Grammar.Classifier.specManifold "Man"
  let enums : List FrontierEnumerator := [enumClassifierMapsFor "Man"]
  pkgOfClassifier spec (some 0) enums

def cfg : EngineConfig :=
  { barMode := .phiOmega
  , pkgs    := [pkgS1, pkgMan]
  , eps     := 1e-9 }

def st0 : EngineState := {}

-- Run a few ticks; early ticks will likely idle while H ramps up.
#eval
  let (stF, results) := runNTicks cfg st0 6
  (stF.H, sumNu stF.history, sumKappa stF.history, results.length)

-- Peek at the last decision (using reverse to avoid nonstandard `.back?`):
#eval
  let (_, results) := runNTicks cfg st0 8
  match results.reverse with
  | r :: _ => some r.decision
  | []     => none

-/

end PEN.Select.Engine
