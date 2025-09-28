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
  | declareCompRule     (elimName : String) (constrName : String) -- β/ι rule tying an eliminator to a constructor
  | declareTerm         (name : String) (typeName : String) -- a non-constructor term inhabiting a known type
  deriving Repr, BEq, Inhabited

/-- CAD context: what has been declared so far. For simplicity we store lists. -/
structure Context where
  universes   : List Nat                := []
  typeFormers : List String             := []            -- names of types
  constructors : List (String × String) := []            -- (ctorName, typeName)
  eliminators  : List (String × String) := []            -- (elimName, typeName)
  compRules    : List (String × String) := []            -- (elimName, ctorName)
  terms        : List (String × String) := []            -- (termName, typeName)
  deriving Repr, Inhabited

namespace Context

/-- Empty CAD context. -/
def empty : Context := {}

/-! Simple membership helpers (Bool-valued; no Prop machinery needed). -/

@[inline] def memNat (xs : List Nat) (n : Nat) : Bool :=
  xs.any (fun m => m == n)

@[inline] def memStr (xs : List String) (s : String) : Bool :=
  xs.any (fun t => t == s)

@[inline] def memPair (xs : List (String × String)) (a b : String) : Bool :=
  xs.any (fun p => p.fst == a && p.snd == b)

@[inline] def containsKey (xs : List (String × String)) (a : String) : Bool :=
  xs.any (fun p => p.fst == a)

@[inline] def containsVal (xs : List (String × String)) (b : String) : Bool :=
  xs.any (fun p => p.snd == b)

/-- Does the context already have any universe? -/
@[inline] def hasAnyUniverse (Γ : Context) : Bool :=
  !Γ.universes.isEmpty

@[inline] def hasUniverse (Γ : Context) (ℓ : Nat) : Bool :=
  memNat Γ.universes ℓ

@[inline] def hasTypeFormer (Γ : Context) (name : String) : Bool :=
  memStr Γ.typeFormers name

@[inline] def hasConstructor (Γ : Context) (ctorName : String) : Bool :=
  containsKey Γ.constructors ctorName

@[inline] def hasConstructorFor (Γ : Context) (typeName : String) : Bool :=
  containsVal Γ.constructors typeName

@[inline] def hasEliminator (Γ : Context) (elimName : String) : Bool :=
  containsKey Γ.eliminators elimName

@[inline] def hasEliminatorFor (Γ : Context) (typeName : String) : Bool :=
  containsVal Γ.eliminators typeName

@[inline] def hasCompRule (Γ : Context) (elimName constrName : String) : Bool :=
  memPair Γ.compRules elimName constrName

@[inline] def hasTerm (Γ : Context) (termName : String) : Bool :=
  containsKey Γ.terms termName

@[inline] def hasTermOf (Γ : Context) (typeName : String) : Bool :=
  containsVal Γ.terms typeName

/-- Insert helpers (idempotent: keep Γ unchanged if the entry already exists). -/
@[inline] def addUniverse (Γ : Context) (ℓ : Nat) : Context :=
  if Γ.hasUniverse ℓ then Γ else { Γ with universes := ℓ :: Γ.universes }

@[inline] def addTypeFormer (Γ : Context) (name : String) : Context :=
  if Γ.hasTypeFormer name then Γ else { Γ with typeFormers := name :: Γ.typeFormers }

@[inline] def addConstructor (Γ : Context) (name typeName : String) : Context :=
  if memPair Γ.constructors name typeName then Γ
  else { Γ with constructors := (name, typeName) :: Γ.constructors }

@[inline] def addEliminator (Γ : Context) (name typeName : String) : Context :=
  if memPair Γ.eliminators name typeName then Γ
  else { Γ with eliminators := (name, typeName) :: Γ.eliminators }

@[inline] def addCompRule (Γ : Context) (elimName constrName : String) : Context :=
  if memPair Γ.compRules elimName constrName then Γ
  else { Γ with compRules := (elimName, constrName) :: Γ.compRules }

@[inline] def addTerm (Γ : Context) (name typeName : String) : Context :=
  if memPair Γ.terms name typeName then Γ
  else { Γ with terms := (name, typeName) :: Γ.terms }

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
  -- Π and Σ are classifier-level; Man is too
  not (T == "Pi" || T == "Sigma" || T == "Man")

/-- If a term name encodes a requirement on a specific constructor, return that constructor name. -/
@[inline] def ctorNameFromTerm? (nm : String) : Option String :=
  let r := "refl_"
  let t := "transport_"
  if nm.startsWith r then some (nm.drop r.length)
  else if nm.startsWith t then some (nm.drop t.length)
  else none

/-- Check whether a term name encodes a dependency on another declaration. -/
@[inline] def termDependency? (nm : String) : Option String :=
  if nm.startsWith "Hopf.Affordance." then
    some "Hopf.coherence"
  else
    none

/--
Paper‑faithful validity predicate for one atomic declaration given a context.

Key gates:
* `declareTypeFormer` requires that at least one universe is present.
* `declareEliminator` requires that the type exists **and** at least one constructor
  for that type already exists (this is what gives ν(3) = 2 in the early steps).
-/
def isValidInContext (decl : AtomicDecl) (ctx : Context) : Bool :=
  match decl with
  | AtomicDecl.declareUniverse 0        => true
  | AtomicDecl.declareUniverse (Nat.succ ℓ) => ctx.hasUniverse ℓ
  | AtomicDecl.declareTypeFormer _      => not ctx.universes.isEmpty
  | AtomicDecl.declareConstructor _ T   => hasTypeFormer ctx T
  | AtomicDecl.declareEliminator _ T    =>
      hasTypeFormer ctx T && (if elimNeedsCtor T then hasCtorOf ctx T else true)
  | AtomicDecl.declareCompRule e c      => hasElimName ctx e && hasCtorName ctx c
  | AtomicDecl.declareTerm nm T =>
      let base := hasTypeFormer ctx T
      let ctorCheck :=
        match ctorNameFromTerm? nm with
        | some c =>
            base && (ctx.constructors.any (fun p => p.fst == c && p.snd == T))
        | none   =>
            base
      match termDependency? nm with
      | some depName => ctorCheck && ctx.hasTerm depName
      | none         => ctorCheck



/-- Apply a single atomic declaration if valid; otherwise return `none`. -/
def step (Γ : Context) (decl : AtomicDecl) : Option Context :=
  if isValidInContext decl Γ then
    some <|
      match decl with
      | .declareUniverse ℓ            => Γ.addUniverse ℓ
      | .declareTypeFormer n          => Γ.addTypeFormer n
      | .declareConstructor n T       => Γ.addConstructor n T
      | .declareEliminator n T        => Γ.addEliminator n T
      | .declareCompRule e c          => Γ.addCompRule e c
      | .declareTerm n T              => Γ.addTerm n T
  else
    none

/-- Apply a list of atomic declarations left-to-right, short-circuiting on failure. -/
def applyAll? (Γ : Context) (ds : List AtomicDecl) : Option Context :=
  ds.foldlM step Γ

/-! # Tiny sanity checks (uncomment to try locally)

open AtomicDecl

def Γ0 : Context := Context.empty

-- Invalid: cannot declare a type former without a universe.
#eval isValidInContext (.declareTypeFormer "Unit") Γ0         -- false

-- Declare U0, then Unit becomes valid.
def Γ1 := (step Γ0 (.declareUniverse 0)).getD Γ0
#eval isValidInContext (.declareTypeFormer "Unit") Γ1         -- true

def Γ2 := (step Γ1 (.declareTypeFormer "Unit")).getD Γ1
#eval isValidInContext (.declareConstructor "star" "Unit") Γ2 -- true
#eval isValidInContext (.declareTerm "tt" "Unit") Γ2          -- true

-/

end PEN.CAD
