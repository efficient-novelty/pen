import Lake
open Lake DSL

/--
  PEN Lean project — Lake configuration.
  - Depends on mathlib4 (which bundles Aesop).
  - Provides a `PEN` library with sources under `PEN/`.
  - Adds a `doc` script for generating HTML docs via doc-gen4 (optional).
--/

package «pen» where
  -- Allow nonfatal warnings from dependencies during bootstrap (optional):
  moreLeanArgs := #[]
  moreServerArgs := #[]

/-- mathlib4 dependency --/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

/-- Optional: doc-gen4 for local documentation builds. Comment out if not needed. --/
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib «PEN» where
  -- You can add `globs := #["PEN/*"]` if you later split multiple packages.
  -- By default, Lake finds files under `PEN/` matching the module namespace.

/-- Build API docs into `build/doc` using doc-gen4. --/
script doc (args) do
  let _ ← IO.Process.run {
    cmd := "lake", args := #["build", "PEN"]
  }
  let _ ← IO.Process.run {
    cmd := "lake", args := #["exe", "doc-gen4", "--", "PEN"]
  }
  return 0
