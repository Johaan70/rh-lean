import Lake
open Lake DSL

package rh_lean

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib RhLean where
  roots := #[`RhLean]
