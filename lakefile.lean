import Lake
open Lake DSL

package «Lean4-RH-KIRA» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «RHkira» where
  roots := #[`RHkira]
