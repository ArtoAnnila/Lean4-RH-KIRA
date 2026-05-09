# Lean4-RH-KIRA

Lean 4 Formalization of the Kernel–Inversion Reconciliation Axiom (KIRA) and its application to the Riemann Hypothesis, associated with the preprint “Riemann Hypothesis Revisited”, Arto Annila, 2026.

The formalization isolates the Kernel–Inversion Reconciliation Axiom (KIRA) as the analytic continuation principle required to deduce that any zero of the completed zeta function must lie on the critical line.

## Contents

- `src/RHkira.lean` — the core formalization of the Kernel–Inversion Reconciliation Axiom (KIRA) and its consequence for the Riemann Hypothesis.

## Build instructions

```bash
lake exe cache get
lake build
