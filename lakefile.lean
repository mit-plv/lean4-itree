import Lake
open Lake DSL

package «ctree» where
  -- add any package configuration options here

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.1"

@[default_target]
lean_lib «CTree» where
  globs := #[.submodules `CTree]
