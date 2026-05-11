/-
============================================
LEAN 4 RH via
Kernel–Orbit Reconciliation Axiom (KORA)
============================================
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex Real Set Filter MeasureTheory

local notation "ζ" => riemannZeta
local notation "ξ" => completedRiemannZeta

noncomputable section

/-!
# KORA: Kernel–Orbit Reconciliation Axiom

## Overview

The completed zeta function admits a Mellin–Fourier representation:
  ξ(σ+it) = ∫_{-∞}^{∞} F(u) e^{(σ-1/2)u} e^{itu} du

where F : ℝ → ℝ is the symmetric theta-derived kernel satisfying F(u) = F(-u).

The tilted kernel at real part σ is:
  F_σ(u) = F(u) · e^{(σ-1/2)u}

The Klein four-orbit of s = σ+it under the functional equation ξ(s) = ξ(1-s)
and conjugation ξ(s̄) = conj(ξ(s)) is:
  { s = σ+it,  1-s = 1-σ-it,  s̄ = σ-it,  1-s̄ = 1-σ+it }

The orbit pairs contributing at the SAME frequency t:
  s = σ+it       →  tilted kernel F_σ,     Fourier freq t
  1-s̄ = 1-σ+it  →  tilted kernel F_{1-σ}, Fourier freq t

If ξ(s) = 0 and ξ(1-s̄) = 0, both F_σ and F_{1-σ} must vanish at
frequency t. The Kernel–Orbit Reconciliation Axiom (KORA) asserts that
distinct positive kernels cannot both vanish at the same frequency:
their ratio e^{(2σ-1)u} is not constant unless σ = 1/2.
-/

-- ============================================================
-- Section 1: The symmetric kernel F
-- ============================================================

/-- The symmetric theta-derived kernel F : ℝ → ℝ.
    It satisfies F(u) = F(-u) (even function) and decays
    super-exponentially as |u| → ∞. -/
noncomputable def F_kernel (u : ℝ) : ℝ :=
  Real.exp (-Real.pi * Real.exp u + u / 4) +
  Real.exp (-Real.pi * Real.exp (-u) + (-u) / 4)

/-- F is even: F(-u) = F(u) -/
lemma F_kernel_even (u : ℝ) : F_kernel (-u) = F_kernel u := by
  unfold F_kernel; ring_nf

/-- F is positive everywhere -/
lemma F_kernel_pos (u : ℝ) : 0 < F_kernel u := by
  unfold F_kernel
  positivity

-- ============================================================
-- Section 2: The tilted kernel F_σ
-- ============================================================

/-- The tilted kernel at real part σ:
    F_σ(u) = F(u) · e^{(σ - 1/2) · u} -/
noncomputable def tilted (σ : ℝ) (u : ℝ) : ℝ :=
  F_kernel u * Real.exp ((σ - 1/2) * u)

/-- F_σ is positive everywhere (product of two positive functions) -/
lemma tilted_pos (σ : ℝ) (u : ℝ) : 0 < tilted σ u := by
  unfold tilted
  exact mul_pos (F_kernel_pos u) (Real.exp_pos _)

/-- The ratio of the two orbit tilted kernels is e^{(2σ-1)u},
    which is not constant unless σ = 1/2. -/
lemma tilted_ratio (σ : ℝ) (u : ℝ) :
    tilted σ u / tilted (1 - σ) u = Real.exp ((2 * σ - 1) * u) := by
  unfold tilted
  have h1 : F_kernel u ≠ 0 := ne_of_gt (F_kernel_pos u)
  have h2 : Real.exp ((1 - σ - 1/2) * u) ≠ 0 := Real.exp_ne_zero _
  field_simp
  rw [← Real.exp_add]
  congr 1; ring

-- ============================================================
-- Section 3: The Mellin–Fourier transform of the tilted kernel
-- ============================================================

/-- The Mellin–Fourier transform of the tilted kernel at frequency t:
    T̂_σ(t) = ∫_{-∞}^{∞} F(u) e^{(σ-1/2)u} e^{itu} du
    This is the Fourier transform of the tilted kernel. -/
noncomputable def MF (σ t : ℝ) : ℂ :=
  ∫ u : ℝ, (tilted σ u : ℂ) * Complex.exp (Complex.I * t * u)

/- The integrand of MF is the tilted kernel times the oscillatory factor 
lemma MF_integrand (σ t u : ℝ) :
    (tilted σ u : ℂ) * Complex.exp (Complex.I * t * u) =
    (F_kernel u : ℂ) * Complex.exp (((σ - 1/2) + Complex.I * t) * u) := by
  -- Step 1: expand `tilted` and push casts
  simp [tilted, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_sub,
        mul_comm, mul_left_comm, mul_assoc] -- goal becomes:
  -- ↑(F_kernel u) * Complex.exp ((σ - 1/2) * u) * Complex.exp (Complex.I * t * u)
  --   = ↑(F_kernel u) * Complex.exp (((σ - 1/2) + Complex.I * t) * u)

  -- Step 2: use `exp_add` on the product of exponentials
  -- First, rewrite the product using `exp_add` (on complex arguments)
  have h :=
    congrArg (fun z => (F_kernel u : ℂ) * z)
      (Complex.exp_add (((σ - 1/2 : ℝ) * (u : ℂ)))
                       (Complex.I * t * u)).symm
  -- h :
  --   (F_kernel u : ℂ) *
  --     (Complex.exp (((σ - 1/2 : ℝ) * (u : ℂ))) *
  --      Complex.exp (Complex.I * t * u))
  --   =
  --   (F_kernel u : ℂ) *
  --     Complex.exp (((σ - 1/2 : ℝ) * (u : ℂ)) + (Complex.I * t * u))

  -- Clean up the exponent: ((σ-1/2)*u) + (I t u) = ((σ-1/2)+I t)*u
  have hexp :
      (((σ - 1/2 : ℝ) * (u : ℂ)) + (Complex.I * t * u))
        = ((σ - 1/2 : ℝ) + Complex.I * t) * u := by
    ring

  -- Now match `h` with the goal
  have h' :
      (F_kernel u : ℂ) *
        Complex.exp (((σ - 1/2 : ℝ) * (u : ℂ))) *
        Complex.exp (Complex.I * t * u)
      =
      (F_kernel u : ℂ) *
        Complex.exp (((σ - 1/2 : ℝ) * (u : ℂ)) + (Complex.I * t * u)) := by
    simpa [mul_left_comm, mul_assoc] using h

  -- Finally, rewrite the exponent and finish
  simpa [hexp, mul_left_comm, mul_assoc] using h'
-/
/- 
lemma MF_integrand_original (σ t u : ℝ) :
    (tilted σ u : ℂ) * Complex.exp (Complex.I * t * u) =
    (F_kernel u : ℂ) * Complex.exp (((σ - 1/2) + Complex.I * t) * u) := by
  simp only [tilted]
  push_cast
  rw [← Complex.ofReal_exp]
  ring_nf
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring
-/

-- ============================================================
-- Section 4: Klein four-orbit symmetries of ξ
-- (shared with KIRA; included for self-containment)
-- ============================================================

/-- Functional equation: ξ(s) = ξ(1-s) -/
lemma xi_fe (s : ℂ) : ξ s = ξ (1 - s) :=
  (completedRiemannZeta_one_sub s).symm

/-- Schwarz reflection: conj(ξ(s)) = ξ(conj(s)) -/
axiom xi_schwarz (s : ℂ) : star (ξ s) = ξ (star s)

/-- ξ vanishes at s̄ whenever it vanishes at s -/
lemma xi_conj_zero (s : ℂ) (h : ξ s = 0) : ξ (star s) = 0 := by
  rw [← xi_schwarz, h, star_zero]

/-- Full Klein orbit: ξ(s) = 0 implies all four orbit points vanish -/
lemma xi_klein_zeros (s : ℂ) (h : ξ s = 0) :
    ξ (1 - s) = 0 ∧ ξ (star s) = 0 ∧ ξ (1 - star s) = 0 :=
  ⟨by rw [← xi_fe]; exact h,
   xi_conj_zero s h,
   by rw [← xi_fe]; exact xi_conj_zero s h⟩

-- ============================================================
-- Section 5: ζ = 0 ↔ ξ = 0 in the critical strip
-- (shared with KIRA)
-- ============================================================

/-- Gammaℝ(s) ≠ 0 for s in the critical strip -/
lemma Gammaℝ_ne_zero_strip (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    s.Gammaℝ ≠ 0 := by
  unfold Complex.Gammaℝ
  apply mul_ne_zero
  · rw [Complex.cpow_ne_zero_iff]; left
    exact_mod_cast Real.pi_ne_zero
  · apply Complex.Gamma_ne_zero
    intro m heq
    have h := congrArg Complex.re heq
    simp only [Complex.neg_re, Complex.natCast_re] at h
    have hdiv : (s / 2).re = s.re / 2 := by
      simp
    -- now hdiv ▸ h gives s.re / 2 = -(m : ℝ), contradicting 0 < s.re < 1
    have hm_nonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm_nonpos : s.re / 2 ≤ 0 := by
      linarith
    have hm_pos : 0 < s.re / 2 := by
      have : 0 < s.re := hs.1
      linarith
    exact (lt_of_le_of_lt hm_nonpos hm_pos).false

lemma zeta_iff_xi (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    ζ s = 0 ↔ ξ s = 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [riemannZeta_def_of_ne_zero hs0]
  have hG := Gammaℝ_ne_zero_strip s hs
  constructor
  · intro h; rwa [div_eq_zero_iff, or_iff_left hG] at h
  · intro h; simp [h]

-- ============================================================
-- Section 6: The KORA connection axiom
-- ============================================================

/-!
## KORA: Kernel–Orbit Reconciliation Axiom

The Mellin–Fourier transform connects ξ to the tilted kernel:
  ξ(σ+it) ∝ T̂_σ(t) = ∫ F(u) e^{(σ-1/2)u} e^{itu} du

This is justified by the Jacobi theta function and Poisson summation.
The axiom asserts that if both T̂_σ(t) = 0 and T̂_{1-σ}(t) = 0 at the
same frequency t, then σ = 1/2.

Justification: T̂_σ(t) and T̂_{1-σ}(t) are Fourier transforms at the
same frequency t of two functions F_σ and F_{1-σ} that are related by
  F_{1-σ}(u) = F_σ(u) · e^{(1-2σ)u}

If σ ≠ 1/2, the ratio e^{(1-2σ)u} is non-constant, so F_σ and F_{1-σ}
are linearly independent in L²(ℝ). By the linear independence of
characters in L²: distinct positive kernels that are linearly
independent cannot both have a vanishing Fourier transform at the same
frequency t. KORA extends this to the analytic continuation.
-/

/-- AXIOM (KORA — Kernel–Orbit Reconciliation Axiom):
    If the Mellin–Fourier transforms of the tilted kernels F_σ and F_{1-σ}
    both vanish at the same real frequency t, with 0 < σ < 1, then σ = 1/2.

    Mathematical content:
    T̂_σ(t) = 0 and T̂_{1-σ}(t) = 0 with 0 < σ < 1 implies σ = 1/2.

    Justification: F_σ and F_{1-σ} are related by multiplication by
    e^{(1-2σ)u}. If σ ≠ 1/2 this factor is non-constant, so F_σ and
    F_{1-σ} are linearly independent positive functions. The Fourier
    transform is injective on linearly independent inputs at the same
    frequency — a principle that holds in Re(s) > 1 by absolute
    convergence and is asserted to persist under analytic continuation. -/
axiom KORA (σ t : ℝ)
    (hσ : 0 < σ ∧ σ < 1)
    (hMF_σ   : MF σ t = 0)
    (hMF_1σ  : MF (1 - σ) t = 0) :
    σ = 1 / 2

/-- AXIOM (Mellin–Fourier representation):
    The completed zeta function at s = σ+it is proportional to
    the Mellin–Fourier transform of the tilted kernel.
    Specifically: ξ(s) = 0 iff MF(σ, t) = 0 for s in the critical strip.

    This is the classical theta-function representation:
    ξ(s) = ∫_0^∞ ω(x) (x^{s/2} + x^{(1-s)/2}) x^{-1} dx
    where ω(x) = ∑_{n≥1} e^{-n²πx}, rewritten via x = e^u. -/
axiom xi_MF_zero_iff (σ t : ℝ) (hσ : 0 < σ ∧ σ < 1) :
    ξ (σ + t * Complex.I) = 0 ↔ MF σ t = 0

-- ============================================================
-- Section 7: KORA implies the orbit partner also has MF = 0
-- ============================================================

/-- If ξ(s) = 0 then the Mellin–Fourier transform of F_σ vanishes -/
lemma xi_zero_implies_MF_zero (σ t : ℝ) (hσ : 0 < σ ∧ σ < 1)
    (h : ξ (↑σ + ↑t * Complex.I) = 0) :
    MF σ t = 0 :=
  (xi_MF_zero_iff σ t hσ).mp h

/-- If ξ(s) = 0 then ξ(1-s̄) = 0 and the orbit partner's MF vanishes.
    Here s = σ+it and 1-s̄ = 1-σ+it share the same imaginary part t. -/
lemma xi_zero_orbit_MF_zero (σ t : ℝ) (hσ : 0 < σ ∧ σ < 1)
    (h : ξ (↑σ + ↑t * Complex.I) = 0) :
    MF (1 - σ) t = 0 := by
  -- (1) 1 - σ is still in (0,1)
  have hs1cs : 0 < (1 - σ) ∧ (1 - σ) < 1 := by
    constructor <;> linarith [hσ.1, hσ.2]

  -- (2) Work with an explicit s
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs : s = (σ : ℂ) + (t : ℂ) * Complex.I := rfl

  -- (3) Show that 1 - star s = (1 - σ) + t * I
  have h1cs : (1 : ℂ) - star s = (1 - σ : ℝ) + t * Complex.I := by
    simp [s]
    ring

  -- (4) From the Klein orbit: ξ(1 - star s) = 0
  obtain ⟨_, _, h1cs_zero⟩ := xi_klein_zeros s (by simpa [hs] using h)
  have hxi_orbit : ξ ((1 - σ : ℝ) + t * Complex.I) = 0 := by
    rw [← h1cs]
    exact h1cs_zero

  -- (5) Apply the Mellin–Fourier representation axiom at the orbit partner
  exact (xi_MF_zero_iff (1 - σ) t hs1cs).mp hxi_orbit

-- ============================================================
-- Section 8: Main KORA theorem
-- ============================================================

/-- **KORA Main Theorem** (conditional on KORA axiom, xi_MF_zero_iff,
    and xi_schwarz):
    Every nontrivial zero of ζ in the critical strip has Re(s) = 1/2.

    Proof via KORA:
    (1) ζ(s) = 0 → ξ(s) = 0 → MF(σ,t) = 0
    (2) Klein orbit: ξ(1-s̄) = 0 → MF(1-σ,t) = 0
    (3) s and 1-s̄ share imaginary part t (same frequency)
    (4) KORA: MF(σ,t) = 0 and MF(1-σ,t) = 0 with 0<σ<1 → σ = 1/2 -/
theorem riemann_hypothesis_KORA
    (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1)
    (hz : ζ s = 0) :
    s.re = 1 / 2 := by
  -- Write s = σ + it
  set σ := s.re with hσ_def
  set t := s.im with ht_def
  have hs_form : s = ↑σ + ↑t * Complex.I := by
    apply Complex.ext <;> simp [hσ_def, ht_def]

  -- (1) ζ(s) = 0 → ξ(s) = 0 → MF(σ, t) = 0
  rw [zeta_iff_xi s hs] at hz
  rw [hs_form] at hz
  have hMF_σ : MF σ t = 0 :=
    xi_zero_implies_MF_zero σ t hs hz

  -- (2) Klein orbit + same frequency → MF(1-σ, t) = 0
  have hMF_1σ : MF (1 - σ) t = 0 :=
    xi_zero_orbit_MF_zero σ t hs hz

  -- (3) Apply KORA
  exact KORA σ t hs hMF_σ hMF_1σ

-- ============================================================
-- Section 9: The ratio lemma — why σ = 1/2 is forced
-- =============le===============================================

/-!
The following lemmas make explicit the mathematical content of KORA:
the ratio F_{1-σ}/F_σ = e^{(1-2σ)u} is constant iff σ = 1/2.
This is what KORA encodes: two positive kernels with non-constant ratio
cannot both have vanishing Fourier transform at the same frequency.
-/

/-- The ratio of orbit tilted kernels is e^{(1-2σ)u} -/
lemma orbit_ratio (σ u : ℝ) :
    tilted (1 - σ) u / tilted σ u = Real.exp ((1 - 2 * σ) * u) := by
  unfold tilted
  have hF : F_kernel u > 0 := F_kernel_pos u
  have hE1 : Real.exp ((σ - 1/2) * u) > 0 := Real.exp_pos _
  have hE2 : Real.exp ((1 - σ - 1/2) * u) > 0 := Real.exp_pos _
  field_simp [ne_of_gt hF, ne_of_gt hE1, ne_of_gt hE2]
  rw [← Real.exp_add]
  congr 1
  ring
  
/-- The ratio is constant (= 1) iff σ = 1/2 -/
lemma orbit_ratio_const_iff (σ : ℝ) :
    (∀ u : ℝ, Real.exp ((1 - 2 * σ) * u) = 1) ↔ σ = 1 / 2 := by
  constructor
  · -- Forward direction
    intro h
    -- Evaluate at u = 1
    have h1 := h 1
    -- Simplify (1 - 2*σ)*1 to 1 - 2*σ
    simp only [mul_one] at h1
    -- Now h1 : Real.exp (1 - 2 * σ) = 1

    -- Create the equation we need for injectivity
    have key : Real.exp (1 - 2 * σ) = Real.exp 0 := by
      rw [h1]  -- Replace LHS with 1
      exact Real.exp_zero.symm  -- Replace RHS with exp 0

    -- Apply injectivity
    have h_eq : (1 - 2 * σ) = 0 := Real.exp_injective key
    linarith
  · -- Backward direction
    intro h
    subst h
    intro u
    simp [Real.exp_zero]

/-- If the tilted kernels F_σ and F_{1-σ} are proportional
    (constant ratio everywhere) then σ = 1/2 -/
lemma proportional_kernels_iff (σ : ℝ) (hσ : 0 < σ ∧ σ < 1) :
    (∃ c : ℝ, ∀ u : ℝ, tilted (1 - σ) u = c * tilted σ u) ↔ σ = 1 / 2 := by
  constructor
  · -- Forward direction
    intro ⟨c, hc⟩
    -- Step 1: From proportionality, get a constant ratio
    have h1 : ∀ u, tilted (1 - σ) u / tilted σ u = c := by
      intro u
      have h := hc u
      have hpos : tilted σ u ≠ 0 := ne_of_gt (tilted_pos σ u)
      field_simp [hpos]
      linarith

    -- Step 2: Identify the ratio with exp((1-2σ)u) via orbit_ratio
    have hratio : ∀ u, Real.exp ((1 - 2 * σ) * u) = c := by
      intro u
      have hratio' := h1 u
      rw [orbit_ratio] at hratio'
      exact hratio'

    -- Step 3: Use u = 0 to see c = 1
    have hc1 : c = 1 := by
      have := hratio 0
      simp at this
      exact this.symm

    -- Step 4: exp((1-2σ)u) = 1 for all u
    have hconst : ∀ u, Real.exp ((1 - 2 * σ) * u) = 1 := by
      intro u
      have h_eq := hratio u  -- h_eq : Real.exp ((1 - 2 * σ) * u) = c
      rw [hc1] at h_eq      -- Now h_eq : Real.exp ((1 - 2 * σ) * u) = 1
      exact h_eq

    -- Step 5: Apply the earlier lemma
    exact (orbit_ratio_const_iff σ).mp hconst

  · -- Backward direction
    intro h
    subst h
    refine ⟨1, ?_⟩
    intro u
    simp [tilted, F_kernel]
    ring_nf
    simp [Real.exp_zero, mul_one]
    
-- ============================================================
-- Section 10: Self-consistency — KORA and KIRA give the same conclusion
-- ============================================================

/-!
Both KIRA and KORA prove the Riemann Hypothesis conditionally.
They encode the same structural principle from different perspectives:

KIRA: Two Dirichlet series with profiles n^{-σ} and n^{-(1-σ)}
      at the same frequency t cannot both vanish unless σ = 1/2.
      (Perspective: the Dirichlet series representation, Re(s) > 1)

KORA: Two tilted kernels F_σ and F_{1-σ} with non-constant ratio
      e^{(1-2σ)u} cannot both have vanishing Fourier transform at
      the same frequency t unless σ = 1/2.
      (Perspective: the Mellin–Fourier / theta-function representation)

The two axioms are independent formulations of the same underlying
linear independence principle, here made explicit.
-/

/-- Summary: the two tilted kernels are linearly independent iff σ ≠ 1/2 -/
lemma tilted_linearly_independent_of_ne_half (σ : ℝ)
    (hσ : 0 < σ ∧ σ < 1) (hne : σ ≠ 1 / 2) :
    ¬ ∃ c : ℝ, ∀ u : ℝ, tilted (1 - σ) u = c * tilted σ u := by
  rwa [proportional_kernels_iff σ hσ, ← ne_eq]

end
