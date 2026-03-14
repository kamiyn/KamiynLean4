import Lake
open Lake DSL

package "LeanBook" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.22.0"

@[default_target]
lean_lib «LeanBook» where
  globs := #[.submodules `LeanBook]
  -- add library configuration options here
