import Lake
open Lake DSL

package SelectionSort where
  -- add package configuration options here
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib SelectionSort where
  -- add library configuration options here
  globs := #[.submodules `SelectionSort]
