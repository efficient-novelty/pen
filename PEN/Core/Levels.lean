/-
  PEN/Core/Levels.lean

  Lightweight, configurable "level" metadata for the Codebook AST.

  Goals:
  - Provide Lev : AST → Nat that approximates the minimal universe level
    (or "cognitive level") using only syntactic information.
  - Make the mapping for constants configurable via LevelEnv.
  - Respect binders: lam and pi/sigma push the domain/type level into a
    de Bruijn-indexed context for the body/codomain.

  This file is self-contained aside from PEN/Core/Codebook.
-/

import Init
import PEN.Core.Codebook
import PEN.CAD.Atoms

namespace PEN.Core.Levels

open PEN.Core.Codebook

/-- We use natural numbers as our level metric. -/
abbrev Level := Nat

/-- Mapping from constant names to levels (optional for each constant). -/
structure LevelEnv where
  constLevel? : String → Option Level := fun _ => none
deriving Inhabited

namespace LevelEnv

/-- Empty environment: unknown constants default to level 0. -/
def empty : LevelEnv := { constLevel? := fun _ => none }

/-- A simple finite-map environment from a list of name/level pairs. -/
def ofList (xs : List (String × Level)) : LevelEnv :=
  let rec lookup (s : String) : List (String × Level) → Option Level
    | [] => none
    | (n,ℓ)::rest => if n == s then some ℓ else lookup s rest
  { constLevel? := fun s => lookup s xs }

/-- Extend an existing environment with (name,level) overrides. -/
def extend (base : LevelEnv) (xs : List (String × Level)) : LevelEnv :=
  let rec lookup (s : String) : List (String × Level) → Option Level
    | [] => none
    | (n,ℓ)::rest => if n == s then some ℓ else lookup s rest
  { constLevel? := fun s =>
      match lookup s xs with
      | some ℓ => some ℓ
      | none   => base.constLevel? s }

end LevelEnv

/-- Get a defaulted level for a constant from the environment. -/
@[inline] def constLev (env : LevelEnv) (name : String) : Level :=
  (env.constLevel? name).getD 0

/-- Safe nth element with default for de Bruijn contexts. -/
def nthD {α} : List α → Nat → α → α
  | [],      _,   d => d
  | x :: _,  0,   _ => x
  | _ :: xs, (Nat.succ n), d => nthD xs n d

/--
  Compute level with a de Bruijn context for bound variables.

  Conventions:
  - Variables take their level from the context (default 0 if out of range).
  - Constants read their level from `env` (default 0 if unknown).
  - `lam` and `pi`/`sigma` push the *domain/type* level into the context
    when processing body/codomain; the node's level is `max` of its parts.
  - Application and projections do not raise level beyond the max of inputs.
-/
partial def levWithCtx (env : LevelEnv) (ctx : List Level) : AST → Level
  | .var idx =>
      nthD ctx idx 0
  | .const nm =>
      constLev env nm
  | .lam _ ty body =>
      let ℓty := levWithCtx env ctx ty
      let ℓbd := levWithCtx env (ℓty :: ctx) body
      Nat.max ℓty ℓbd
  | .app f x =>
      Nat.max (levWithCtx env ctx f) (levWithCtx env ctx x)
  | .arrow dom cod =>
      Nat.max (levWithCtx env ctx dom) (levWithCtx env ctx cod)
  | .pi _ dom cod =>
      let ℓd := levWithCtx env ctx dom
      let ℓc := levWithCtx env (ℓd :: ctx) cod
      Nat.max ℓd ℓc
  | .sigma _ fst snd =>
      let ℓf := levWithCtx env ctx fst
      let ℓs := levWithCtx env (ℓf :: ctx) snd
      Nat.max ℓf ℓs
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

  You can enable these `#eval`s to sanity‑check the behavior.

  Example environment: treat "Unit" as level 0 (i.e. Unit : U₀),
  and "U0","U1" as levels 1 and 2 respectively (i.e. U₀ : U₁, U₁ : U₂).
-/

def exampleEnv : LevelEnv :=
  LevelEnv.ofList [("Unit", 0), ("U0", 1), ("U1", 2)]

/-
-- A Π over Unit into Unit stays at level 0.
#eval Lev exampleEnv (AST.pi "x" (AST.const "Unit") (AST.const "Unit"))  -- 0

-- A λx:Unit. x has level max(level(Unit), level(body)).
#eval Lev exampleEnv (AST.lam "x" (AST.const "Unit") (AST.var 0))        -- 0

-- A Π over U0 into U0 has level max(1,1)=1.
#eval Lev exampleEnv (AST.pi "X" (AST.const "U0") (AST.const "U0"))      -- 1
-/

end PEN.Core.Levels
