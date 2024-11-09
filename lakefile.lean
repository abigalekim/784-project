import Lake
open Lake DSL

package "hypergraph" where
  version := v!"0.1.0"

lean_lib «Hypergraph» where
  -- add library configuration options here

@[default_target]
lean_exe "hypergraph" where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
