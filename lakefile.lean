import Lake
open Lake DSL

package «RiemannHypothesisKIRAKORA» where
  name := "RiemannHypothesisKIRAKORA"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «RHKiraKora» where
  roots := #[`RHkira, `RHkora]
