# Lean4-RH-KIRA

Lean 4 Formalization of the Kernel–Inversion Reconciliation Axiom (KIRA) as the analytic continuation principle for the Riemann Hypothesis to deduce that any zero of the completed zeta function must lie on the critical line, associated with the preprint “Riemann Hypothesis Revisited”, Arto Annila, 2026, at Zenodo.

## Contents

- `src/RHkira.lean` — the core formalization of the Kernel–Inversion Reconciliation Axiom (KIRA) and its consequence for the Riemann Hypothesis.
- `src/DirichletUnitary.lean` — the conditional proof of RH by axiomatic unitarity.
- `src/CompletedZetaKernelMinimumNorm.lean` — the conditional proof of RH by axiomatic minimum norm.

## Build instructions

```bash
lake exe cache get
lake build
