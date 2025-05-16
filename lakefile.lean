import Lake
open Lake DSL

package «ctree» where
  -- add any package configuration options here

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CTree» where
  globs := #[.submodules `CTree]
