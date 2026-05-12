# Lean4-RH-KIRA-KORA

Lean 4 formalization of the Kernel–Inversion Reconciliation Axiom (KIRA) and the
Kernel–Orbit Reconciliation Axiom (KORA) as analytic‑continuation principles for the Riemann Hypothesis (RH), together with the
Kernel–Orbit Reconciliation Axiomatic Proof (KORAP) of RH,
accompanied by the preprint Annila A. Riemann Hypothesis Revisited. Zenodo 2026. https://doi.org/10.5281/zenodo.20142736.

## Contents

- `src/RHkira.lean` — the Kernel–Inversion Reconciliation Axiom (KIRA) and its consequence for the Riemann Hypothesis.
- `src/RHkora.lean` — the Kernel–Orbit Reconciliation Axiom (KORA) and its consequence for the Riemann Hypothesis.
- `src/KORAP.lean` — the Kernel–Orbit Reconciliation Axiomatic Proof (KORAP) of RH using the axioms.
- `src/DirichletUnitary.lean` — the conditional proof of RH by axiomatic unitarity.
- `src/CompletedZetaKernelMinimumNorm.lean` — the conditional proof of RH by axiomatic minimum norm.

## Build instructions

```bash
lake exe cache get
lake build
