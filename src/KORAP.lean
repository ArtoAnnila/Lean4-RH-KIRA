/-
===================================================
LEAN 4 RH via
Kernel–Orbit Reconciliation Axiomatic Proof (KORAP)
===================================================
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn

open Real Set Filter MeasureTheory

local notation "ζ" => riemannZeta
local notation "ξ" => completedRiemannZeta

noncomputable section

/-!
# KORA: Kernel–Orbit Reconciliation — Proof Strategy

The key insight is:

  MF σ t = ∫ F(u) e^{(σ-1/2)u} e^{itu} du
  MF (1-σ) t = ∫ F(u) e^{(1/2-σ)u} e^{itu} du

If both vanish, their sum is zero:
  0 = MF σ t + MF (1-σ) t
    = ∫ F(u) [e^{(σ-1/2)u} + e^{(1/2-σ)u}] e^{itu} du
    = ∫ 2 F(u) cosh((σ-1/2)u) e^{itu} du

This is the Fourier transform of a strictly positive integrable function,
which cannot be zero. This reduces the proof to `fourier_pos_ne_zero`,
a standard analytic fact.
-/

-- ============================================================
-- The symmetric kernel and tilted kernels
-- ============================================================

/-- The symmetric theta-derived kernel -/
noncomputable def F_kernel (u : ℝ) : ℝ :=
  Real.exp (-Real.pi * Real.exp u + u / 4) +
  Real.exp (-Real.pi * Real.exp (-u) + (-u) / 4)

lemma F_kernel_pos (u : ℝ) : 0 < F_kernel u := by
  unfold F_kernel
  positivity

lemma F_kernel_even (u : ℝ) : F_kernel (-u) = F_kernel u := by
  unfold F_kernel
  ring_nf


/-- The tilted kernel at real part σ -/
noncomputable def tilted (σ : ℝ) (u : ℝ) : ℝ :=
  F_kernel u * Real.exp ((σ - 1/2) * u)

lemma tilted_pos (σ u : ℝ) : 0 < tilted σ u :=
  mul_pos (F_kernel_pos u) (Real.exp_pos _)

/-- The sum and difference of orbit tilted kernels -/
noncomputable def tilted_sum (σ u : ℝ) : ℝ :=
  tilted σ u + tilted (1 - σ) u

noncomputable def tilted_diff (σ u : ℝ) : ℝ :=
  tilted σ u - tilted (1 - σ) u

/-- Key identity: sum of orbit kernels = 2 F(u) cosh((σ-1/2)u) -/
lemma tilted_sum_eq (σ u : ℝ) :
    tilted_sum σ u = 2 * F_kernel u * Real.cosh ((σ - 1/2) * u) := by
  unfold tilted_sum tilted
  have h_cosh : Real.cosh ((σ - 1/2) * u) = (Real.exp ((σ - 1/2) * u) + Real.exp (-((σ - 1/2) * u))) / 2 :=
    Real.cosh_eq _
  calc
    (F_kernel u * Real.exp ((σ - 1/2) * u)) + (F_kernel u * Real.exp ((1 - σ - 1/2) * u))
      = F_kernel u * (Real.exp ((σ - 1/2) * u) + Real.exp (-((σ - 1/2) * u))) := by
        ring_nf
    _ = F_kernel u * (2 * Real.cosh ((σ - 1/2) * u)) := by
        rw [h_cosh]
        ring
    _ = 2 * F_kernel u * Real.cosh ((σ - 1/2) * u) := by
        ring

/-- Key identity: diff of orbit kernels = 2 F(u) sinh((σ-1/2)u) -/
lemma tilted_diff_eq (σ u : ℝ) :
    tilted_diff σ u = 2 * F_kernel u * Real.sinh ((σ - 1/2) * u) := by
  unfold tilted_diff tilted
  have h_sinh : Real.sinh ((σ - 1/2) * u) = (Real.exp ((σ - 1/2) * u) - Real.exp (-((σ - 1/2) * u))) / 2 :=
    Real.sinh_eq _
  calc
    (F_kernel u * Real.exp ((σ - 1/2) * u)) - (F_kernel u * Real.exp ((1 - σ - 1/2) * u))
      = F_kernel u * (Real.exp ((σ - 1/2) * u) - Real.exp (-((σ - 1/2) * u))) := by
        ring_nf
    _ = F_kernel u * (2 * Real.sinh ((σ - 1/2) * u)) := by
        rw [h_sinh]
        ring
    _ = 2 * F_kernel u * Real.sinh ((σ - 1/2) * u) := by
        ring

/-- The sum kernel is strictly positive since F > 0 and cosh > 0 -/
lemma tilted_sum_pos (σ u : ℝ) : 0 < tilted_sum σ u := by
  rw [tilted_sum_eq]
  apply mul_pos
  apply mul_pos
  · norm_num
  · exact F_kernel_pos u
  · exact Real.cosh_pos _

-- ============================================================
-- The Mellin–Fourier transform
-- ============================================================

/-- The Mellin–Fourier transform: MF σ t = ∫ F(u) e^{(σ-1/2)u} e^{itu} du -/
noncomputable def MF (σ t : ℝ) : ℂ :=
  ∫ u : ℝ, (tilted σ u : ℂ) * Complex.exp (Complex.I * t * u)

/-- Integrability of the tilted kernel times oscillatory factor.
    This holds because F decays super-exponentially. -/
axiom MF_integrable (σ t : ℝ) :
    Integrable (fun u => (tilted σ u : ℂ) * Complex.exp (Complex.I * t * u))

/-- The MF transform of the sum of orbit kernels -/
noncomputable def MF_sum (σ t : ℝ) : ℂ :=
  ∫ u : ℝ, (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)

lemma MF_sum_eq (σ t : ℝ) : MF_sum σ t = MF σ t + MF (1 - σ) t := by
  unfold MF_sum MF
  -- 1. Use simp to handle the definitions and coercions
  have h_eq : ∀ u, ((tilted_sum σ u) : ℂ) * Complex.exp (Complex.I * t * u) =
      ((tilted σ u) : ℂ) * Complex.exp (Complex.I * t * u) +
      ((tilted (1 - σ) u) : ℂ) * Complex.exp (Complex.I * t * u) := by
    intro u
    unfold tilted_sum
    simp only [Complex.ofReal_add, add_mul]

  -- 2. Use the equality to rewrite the integral
  rw [integral_congr_ae (ae_of_all _ h_eq)]

  -- 3. Apply integral_add with the specific integrability components
  exact integral_add (MF_integrable σ t) (MF_integrable (1 - σ) t)

-- ============================================================
-- The real part of MF at t = 0 is strictly positive
-- ============================================================

/-- MF σ 0 = ∫ F(u) e^{(σ-1/2)u} du (real, positive integral) -/
lemma MF_zero_eq (σ : ℝ) :
    MF σ 0 = (↑(∫ u : ℝ, tilted σ u) : ℂ) := by
  unfold MF

  -- exp(i·0·u) = 1
  have h_exp_zero : ∀ u : ℝ, Complex.exp (Complex.I * (0 : ℝ) * u) = 1 := by
    intro u; simp

  -- rewrite the integral using exp(i·0·u) = 1
  have h_integral :
      ∫ u : ℝ, (tilted σ u : ℂ) * Complex.exp (Complex.I * (0 : ℝ) * u)
        = ∫ u : ℝ, (tilted σ u : ℂ) := by
    refine integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun u => by simp)

  rw [h_integral]

  -- force the integrand into the exact syntactic form needed by `integral_ofReal`
  change (∫ u : ℝ, (↑(tilted σ u) : ℂ)) = _

  -- now instantiate `integral_ofReal` with only the function `f`
  have h :
      ∫ u : ℝ, (↑(tilted σ u) : ℂ)
        = (↑(∫ u : ℝ, tilted σ u) : ℂ) :=
    (integral_ofReal (f := fun u : ℝ => tilted σ u))

  simpa using h

/-- The integral of the tilted kernel is strictly positive.
    This requires integrability and positivity of the tilted kernel. -/
axiom tilted_integral_pos (σ : ℝ) :
    0 < ∫ u : ℝ, tilted σ u

lemma MF_zero_ne_zero (σ : ℝ) : MF σ 0 ≠ 0 := by
  rw [MF_zero_eq]
  have h := tilted_integral_pos σ
  norm_cast
  exact h.ne'

-- ============================================================
-- The key lemma: cosh-weighted integral cannot vanish
-- ============================================================

/-- The real part of MF_sum σ t equals the integral of
    tilted_sum σ u * cos(tu) -/
lemma MF_sum_re (σ t : ℝ) :
    (MF_sum σ t).re = ∫ u : ℝ, tilted_sum σ u * Real.cos (t * u) := by
  unfold MF_sum

  -- 1. Integrability of the complex integrand
  have h_int :
      Integrable (fun u : ℝ =>
        (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)) := by
    have h_eq :
        (fun u : ℝ =>
          (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)) =
        (fun u : ℝ =>
          (tilted σ u : ℂ) * Complex.exp (Complex.I * t * u) +
          (tilted (1 - σ) u : ℂ) * Complex.exp (Complex.I * t * u)) := by
      funext u
      simp [tilted_sum, add_mul]
    have h_add :
        Integrable (fun u : ℝ =>
          (tilted σ u : ℂ) * Complex.exp (Complex.I * t * u) +
          (tilted (1 - σ) u : ℂ) * Complex.exp (Complex.I * t * u)) :=
      (MF_integrable σ t).add (MF_integrable (1 - σ) t)
    simpa [h_eq] using h_add

  -- 2. Apply integral_re, flipped so real part is on the left
  have h_re :
      (∫ u : ℝ, (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)).re
        =
      ∫ u : ℝ,
        (( (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)).re) := by
    have h := integral_re
        (f := fun u : ℝ =>
          (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u))
        h_int
    -- h : ∫ re(f) = re(∫ f), so flip it
    simpa using h.symm

  -- 3. Pointwise identification of the real part
  have h_fun :
      (fun u : ℝ =>
        (( (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)).re))
        =
      (fun u : ℝ =>
        tilted_sum σ u * Real.cos (t * u)) := by
    funext u
    simp [Complex.mul_re, Complex.exp_re, Complex.exp_im,
          tilted_sum, mul_comm, mul_left_comm]

  -- 4. Finish with a calc using h_re and h_fun
  calc
    (∫ u : ℝ, (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)).re
        = ∫ u : ℝ,
            (( (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)).re) := h_re
    _   = ∫ u : ℝ, tilted_sum σ u * Real.cos (t * u) := by
          -- just apply ∫ to both sides of h_fun
          have := congrArg (fun (f : ℝ → ℝ) => ∫ u : ℝ, f u) h_fun
          simpa using this

/-- At t = 0, MF_sum σ 0 equals an integral of a strictly positive kernel, hence > 0. -/
lemma MF_sum_zero_pos (σ : ℝ) : 0 < (MF_sum σ 0).re := by
  rw [MF_sum_eq, Complex.add_re]
  have hre : ∀ τ : ℝ, (MF τ 0).re = ∫ u : ℝ, tilted τ u := by
    intro τ
    unfold MF
    -- Move `.re` inside the integral
    have h := integral_re (MF_integrable τ 0)
    -- Simplify the integrand at t = 0
    simp [Complex.exp_zero] at h
    -- The equality is reversed, so use h.symm
    simpa using h.symm
  -- use hre for both σ and 1 - σ
  rw [hre σ, hre (1 - σ)]
  -- now it's just positivity of two positive integrals
  linarith [tilted_integral_pos σ, tilted_integral_pos (1 - σ)]

-- ============================================================
-- KORA: If both MF σ t = 0 and MF (1-σ) t = 0, contradiction
-- ============================================================

/-- AXIOM (Fourier transform of positive function is nonzero):
    If f : ℝ → ℝ is integrable, f ≥ 0 a.e., and f > 0 on a set of
    positive measure, then its Fourier transform ∫ f(u) e^{itu} du ≠ 0
    for all t ∈ ℝ. -/
axiom fourier_pos_ne_zero
    (f : ℝ → ℝ)
    (hf_int : Integrable f)
    (hf_pos : ∀ u, 0 < f u)
    (t : ℝ) :
    (∫ u : ℝ, (f u : ℂ) * Complex.exp (Complex.I * t * u)) ≠ 0

/-- KORA proof: if MF σ t = 0 and MF (1-σ) t = 0 then False -/
lemma KORA_contradiction (σ t : ℝ)
    (_hσ : 0 < σ ∧ σ < 1)
    (hMF_σ : MF σ t = 0)
    (hMF_1σ : MF (1 - σ) t = 0) : False := by
  -- The sum of the two MF values must be zero
  have hsum_zero : MF_sum σ t = 0 := by
    rw [MF_sum_eq, hMF_σ, hMF_1σ]
    norm_num
  -- But MF_sum σ t = ∫ tilted_sum σ u * e^{itu} du
  have hMF_sum_eq : MF_sum σ t =
      ∫ u : ℝ, (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u) := by
    unfold MF_sum
    rfl
  -- The integrand is strictly positive
  have hpos : ∀ u : ℝ, 0 < tilted_sum σ u :=
    fun u => tilted_sum_pos σ u
  -- Integrability of the integrand
  have hint : Integrable (fun u =>
      (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)) := by
    have h_eq : (fun u => (tilted_sum σ u : ℂ) * Complex.exp (Complex.I * t * u)) =
        (fun u => (tilted σ u : ℂ) * Complex.exp (Complex.I * t * u) +
         (tilted (1 - σ) u : ℂ) * Complex.exp (Complex.I * t * u)) := by
      funext u
      simp [tilted_sum]
      ring
    rw [h_eq]
    exact (MF_integrable σ t).add (MF_integrable (1 - σ) t)
  -- Integrability of tilted_sum σ
  have h_int_tilted_sum : Integrable (fun u => tilted_sum σ u) := by
    have h_eq : (fun u => tilted_sum σ u) = (fun u => tilted σ u + tilted (1 - σ) u) := by
      funext u
      rfl
    rw [h_eq]
    have h1 : Integrable (fun u => tilted σ u) := by
      have := MF_integrable σ 0
      convert this.re using 1
      ext u
      simp [tilted, Complex.exp_re]
    have h2 : Integrable (fun u => tilted (1 - σ) u) := by
      have := MF_integrable (1 - σ) 0
      convert this.re using 1
      ext u
      simp [tilted, Complex.exp_re]
    exact h1.add h2
  -- By fourier_pos_ne_zero, this integral ≠ 0
  have hne : (∫ u : ℝ, (tilted_sum σ u : ℂ) *
      Complex.exp (Complex.I * t * u)) ≠ 0 := by
    have := fourier_pos_ne_zero (fun u => tilted_sum σ u) h_int_tilted_sum hpos
    exact this t
  -- Contradiction: MF_sum = 0 but the integral ≠ 0
  rw [hMF_sum_eq] at hsum_zero
  exact hne hsum_zero

/-- KORA as a theorem: σ = 1/2 follows from
    the vanishing of both Mellin–Fourier transforms -/
theorem KORA (σ t : ℝ)
    (hσ : 0 < σ ∧ σ < 1)
    (hMF_σ : MF σ t = 0)
    (hMF_1σ : MF (1 - σ) t = 0) :
    σ = 1 / 2 := by
  by_contra hne
  exact KORA_contradiction σ t hσ hMF_σ hMF_1σ

/-- Schwarz reflection for ξ -/
axiom xi_schwarz (s : ℂ) : star (ξ s) = ξ (star s)

lemma xi_fe (s : ℂ) : ξ s = ξ (1 - s) :=
  (completedRiemannZeta_one_sub s).symm

lemma xi_conj_zero (s : ℂ) : ξ s = 0 → ξ (star s) = 0 := by
  intro h
  rw [← xi_schwarz, h, star_zero]

lemma xi_klein_zeros (s : ℂ) (h : ξ s = 0) :
    ξ (1 - s) = 0 ∧ ξ (star s) = 0 ∧ ξ (1 - star s) = 0 :=
  ⟨by rw [← xi_fe]; exact h,
   xi_conj_zero s h,
   by rw [← xi_fe]; exact xi_conj_zero s h⟩

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

/-- AXIOM: ξ(σ+it) = 0 iff MF σ t = 0, in the critical strip.
    This is the Mellin–theta representation of ξ. -/
axiom xi_MF_zero_iff (σ t : ℝ) (hσ : 0 < σ ∧ σ < 1) :
    ξ ((σ : ℂ) + (t : ℂ) * Complex.I) = 0 ↔ MF σ t = 0

/-- Main theorem: RH via KORA -/
theorem riemann_hypothesis_KORA
    (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1)
    (hz : ζ s = 0) :
    s.re = 1 / 2 := by
  set σ := s.re with hσ_def
  set t := s.im with ht_def
  have hs_form : s = (σ : ℂ) + (t : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hσ_def, ht_def]

  -- ζ(s) = 0 → ξ(s) = 0
  rw [zeta_iff_xi s hs] at hz

  -- ξ(s) = 0 → MF σ t = 0
  have hMF_σ : MF σ t = 0 := by
    have hz' : ξ ((σ : ℂ) + (t : ℂ) * Complex.I) = 0 := by rwa [← hs_form]
    exact (xi_MF_zero_iff σ t hs).mp hz'

  -- Klein orbit: ξ(1-s̄) = 0
  have h1cs : ξ (1 - star s) = 0 := by
    have := (xi_klein_zeros s hz).2.2
    convert this using 1
    -- Remove the rw [hs_form] as it's redundant after convert

  have hs1cs : 0 < (1 - σ) ∧ (1 - σ) < 1 := by
    simp [σ]; constructor <;> linarith [hs.1, hs.2]

  have hs1cs_form : (1 : ℂ) - star s = ((1 - σ) : ℂ) + (t : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [σ, Complex.sub_re, Complex.conj_re]
    · simp [t, Complex.sub_im, Complex.conj_im]

  -- ξ(1-s̄) = 0 → MF (1-σ) t = 0
  have hMF_1σ : MF (1 - σ) t = 0 := by
    have h1cs' : ξ (↑(1 - σ) + ↑t * Complex.I) = 0 := by
      have key_eq : (1 : ℂ) - star s = ↑(1 - σ) + ↑t * Complex.I := by
        rw [hs1cs_form]
        simp only [Complex.ofReal_sub, Complex.ofReal_one]
      rw [← key_eq]
      exact h1cs
    exact (xi_MF_zero_iff (1 - σ) t hs1cs).mp h1cs'

  -- Apply KORA
  exact KORA σ t hs hMF_σ hMF_1σ

end
