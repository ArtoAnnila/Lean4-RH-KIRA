import Lake
open Lake DSL

package «RiemannHypothesisKIRA» where
  name := "RiemannHypothesisKIRA"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «RHkira» where
  roots := #[`RHkira]
