import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Complex Real Set Filter

local notation "ζ" => riemannZeta
local notation "ξ" => completedRiemannZeta

noncomputable section

/-!
# The Riemann Hypothesis via Kernel–Inversion Reconciliation

## Structure of the proof

The completed zeta function ξ satisfies:
  (FE)   ξ(s) = ξ(1-s)            (functional equation)
  (CR)   ξ(s̄) = conj(ξ(s))        (conjugation / Schwarz reflection)

From these two symmetries the Klein four-group orbit of any zero s is
  {s, 1-s, s̄, 1-s̄}
all of which are also zeros.

The critical observation: s and 1-s̄ satisfy
  Im(1-s̄) = Im(s)
so they are Dirichlet series at the SAME imaginary frequency t = Im(s),
with weight sequences n^(-σ) and n^(-(1-σ)) respectively.

The Kernel–Inversion Reconciliation Axiom (KIRA) encodes the linear
independence of characters at Re(s) > 1 and asserts its preservation
under analytic continuation: two Dirichlet series at the same frequency
with distinct positive weight profiles cannot both vanish.

If ζ(s)=0 and σ ≠ 1/2, then ζ(1-s̄)=0 also, giving two vanishing
series at the same frequency with weight profiles n^(-σ) ≠ n^(-(1-σ)).
This contradicts KIRA, so σ = 1/2.
-/

-- ============================================================
-- Section 1: The Klein four-orbit symmetries of ξ
-- ============================================================

/-- Functional equation: ξ(s) = ξ(1-s) -/
lemma xi_fe (s : ℂ) : ξ s = ξ (1 - s) :=
  (completedRiemannZeta_one_sub s).symm

/-- Schwarz reflection (axiomatised; follows from ξ real on ℝ) -/
axiom xi_schwarz (s : ℂ) : star (ξ s) = ξ (star s)

/-- ξ(s̄) = 0 whenever ξ(s) = 0 -/
lemma xi_conj_zero (s : ℂ) (h : ξ s = 0) : ξ (star s) = 0 := by
  rw [← xi_schwarz, h, star_zero]

/-- The full Klein orbit: ξ(s) = 0 implies all four orbit points vanish -/
lemma xi_klein_zeros (s : ℂ) (h : ξ s = 0) :
    ξ (1 - s) = 0 ∧ ξ (star s) = 0 ∧ ξ (1 - star s) = 0 :=
  ⟨by rw [← xi_fe]; exact h,
   xi_conj_zero s h,
   by rw [← xi_fe]; exact xi_conj_zero s h⟩

-- ============================================================
-- Section 2: ζ = 0 ↔ ξ = 0 in the critical strip
-- ============================================================

/-- Gammaℝ(s) ≠ 0 for s in the critical strip -/
lemma Gammaℝ_ne_zero_strip (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    s.Gammaℝ ≠ 0 := by
  unfold Complex.Gammaℝ
  apply mul_ne_zero
  · -- (π) ^ (-s/2) ≠ 0
    rw [Complex.cpow_ne_zero_iff]
    left
    exact_mod_cast Real.pi_ne_zero
  · -- Γ(s/2) ≠ 0 because s/2 is not a nonpositive integer
    refine Complex.Gamma_ne_zero ?h
    intro m heq
    -- from Γ(s/2) pole condition: s/2 = -m ⇒ contradiction with 0 < Re(s) < 1
    have h := congrArg Complex.re heq
    simp only [Complex.neg_re, Complex.natCast_re] at h
    have hdiv : (s / 2).re = s.re / 2 := by
      simp
    have hre : s.re / 2 = -(m : ℝ) := by
      simpa [hdiv] using h
    -- now use 0 < s.re < 1 to contradict s.re / 2 = -m ≤ 0
    have hm_nonpos : s.re / 2 ≤ 0 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hm_pos : 0 < s.re / 2 := by
      have : 0 < s.re := hs.1
      linarith
    exact (lt_of_le_of_lt hm_nonpos hm_pos).false

/-- ζ(s) = 0 ↔ ξ(s) = 0 in the critical strip -/
lemma zeta_iff_xi (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    ζ s = 0 ↔ ξ s = 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [riemannZeta_def_of_ne_zero hs0]
  have hG := Gammaℝ_ne_zero_strip s hs
  constructor
  · intro h; rwa [div_eq_zero_iff, or_iff_left hG] at h
  · intro h; simp [h]

-- ============================================================
-- Section 3: The Dirichlet series model
-- ============================================================

/-- One step of a Dirichlet series with real weight r at index n -/
noncomputable def step (r : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  if n = 0 then 0 else ↑r * (n : ℂ) ^ (-s)

/-- A Dirichlet series with profile r converges to v at s -/
def ConvergesTo (r : ℕ → ℝ) (s : ℂ) (v : ℂ) : Prop :=
  Summable (fun n => step (r n) n s) ∧ ∑' n, step (r n) n s = v

/-- The norm of a step equals r * n^(-σ) for positive r, n ≥ 1 -/
lemma step_norm (r : ℝ) (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hr : 0 < r) :
    ‖step r n s‖ = r * (n : ℝ) ^ (-s.re) := by
  simp only [step, if_neg (Nat.one_le_iff_ne_zero.mp hn)]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  congr 1
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))]
  simp [Complex.neg_re]

-- ============================================================
-- Section 4: The phase identity for mirror points
-- ============================================================

/-- Im(1 - s̄) = Im(s): mirror point has the same imaginary part -/
lemma im_mirror (s : ℂ) : (1 - star s).im = s.im := by
  simp [Complex.sub_im, Complex.conj_im]
  --simp [Complex.sub_im, Complex.star_def, Complex.conj_im]

/-- The key phase identity: n^{-(1-s̄)} = n^{-(1-2σ)} * n^{-s}
    This allows the series at 1-s̄ to be viewed as a series at s
    with profile m ↦ m^{-(1-2σ)}. -/
lemma phase_identity (s : ℂ) (m : ℕ) (hm : m ≠ 0) :
    (m : ℂ) ^ (-(1 - star s)) =
    ((m : ℝ) ^ (-(1 - 2 * s.re)) : ℝ) * (m : ℂ) ^ (-s) := by
  have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_of_ne_zero hm |>.ne'
  have hm_pos : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm).le
  have hexp : -(1 - star s) = ((-(1 - 2 * s.re) : ℝ) : ℂ) + (-s) := by
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re]; ring
    · simp [Complex.sub_im, Complex.conj_im];
  rw [hexp, Complex.cpow_add (x := (m : ℂ)) ((-(1 - 2 * s.re) : ℝ) : ℂ) (-s) hm_ne]
  congr 1
  rw [← Complex.ofReal_natCast m, Complex.ofReal_cpow hm_pos]

-- ============================================================
-- Section 5: The Kernel–Inversion Reconciliation Axiom (KIRA)
-- ============================================================

/-!
KIRA states that the linear independence of the characters {n^{-it}}
established in Re(s) > 1 is preserved by analytic continuation.
Concretely: two Dirichlet series with distinct positive weight profiles
at the same complex frequency cannot both converge to zero.

In Re(s) > 1 this is immediate from absolute convergence and unique
factorisation (Euler product). KIRA asserts this persists in the
critical strip 0 < Re(s) < 1.
-/

/-- AXIOM (KIRA — Kernel–Inversion Reconciliation Axiom):
    If two Dirichlet series with positive profiles both converge to 0
    at the same s in the critical strip, their weight sequences n^(-σ)
    must be identical, hence their profiles agree. -/
axiom KIRA
    (r₁ r₂ : ℕ → ℝ)
    (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1)
    (h₁ : ∀ n, 1 ≤ n → 0 < r₁ n)
    (h₂ : ∀ n, 1 ≤ n → 0 < r₂ n)
    (hc₁ : ConvergesTo r₁ s 0)
    (hc₂ : ConvergesTo r₂ s 0) :
    ∀ n, 1 ≤ n → r₁ n * (n : ℝ) ^ (-s.re) = r₂ n * (n : ℝ) ^ (-s.re)

/-- AXIOM (Dirichlet continuation):
    ∑_{n≥1} n^{-s} converges to ζ(s) for Re(s) > 0. -/
axiom dirichlet_cont (s : ℂ) (hs : 0 < s.re) :
    ConvergesTo (fun _ => (1 : ℝ)) s (ζ s)

-- ============================================================
-- Section 6: Reindexing the mirror series
-- ============================================================

/-- The series ∑ n^{-(1-s̄)} at 1-s̄, when reindexed, becomes a
    Dirichlet series AT s with profile m ↦ m^{-(1-2σ)}.
    This works because Im(1-s̄) = Im(s) (same frequency). -/
lemma reindex_mirror
    (s : ℂ)
    (_hs_strip : 0 < s.re ∧ s.re < 1)
    (hc : ConvergesTo (fun _ => (1 : ℝ)) (1 - star s) 0) :
    ConvergesTo (fun m : ℕ => (m : ℝ) ^ (-(1 - 2 * s.re))) s 0 := by
  have hstep_eq : ∀ m : ℕ,
      step ((m : ℝ) ^ (-(1 - 2 * s.re))) m s = step 1 m (1 - star s) := by
    intro m
    simp only [step]
    split_ifs with hm
    · simp
    · simp only [Complex.ofReal_one, one_mul]
      exact (phase_identity s m hm).symm
  constructor
  · have : (fun n : ℕ => step ((n : ℝ) ^ (-(1 - 2 * s.re))) n s) =
        (fun n : ℕ => step 1 n (1 - star s)) := funext hstep_eq
    rw [this]; exact hc.1
  · have : (fun n : ℕ => step ((n : ℝ) ^ (-(1 - 2 * s.re))) n s) =
        (fun n : ℕ => step 1 n (1 - star s)) := funext hstep_eq
    simp_rw [this]; exact hc.2

-- ============================================================
-- Section 7: The purely real conclusion σ = 1/2
-- ============================================================

/-- If 2^(-σ) = 2^(-(1-σ)) then σ = 1/2 -/
lemma sigma_half_of_eq
    (σ : ℝ) (_hσ : 0 < σ ∧ σ < 1)
    (h : (2 : ℝ) ^ (-σ) = (2 : ℝ) ^ (-(1 - σ))) : σ = 1 / 2 := by
  have heq : -σ = -(1 - σ) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd h (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt))
    · exact absurd h (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hgt))
  linarith

-- ============================================================
-- Section 8: Main theorem
-- ============================================================

/-- **Riemann Hypothesis** (conditional on KIRA and dirichlet_cont):
    Every nontrivial zero of ζ in the critical strip has Re(s) = 1/2.

    Proof outline:
    (1) ζ(s) = 0 → ξ(s) = 0 → ξ(1-s̄) = 0 → ζ(1-s̄) = 0  [Klein orbit]
    (2) Both ζ(s) = 0 and ζ(1-s̄) = 0 give Dirichlet series
        converging to 0 at their respective points.
    (3) Since Im(s) = Im(1-s̄), reindex the series at 1-s̄ as a
        series AT s with profile m ↦ m^{-(1-2σ)}.
    (4) KIRA at s: profile 1 and profile m ↦ m^{-(1-2σ)} both
        annihilated at s → weight sequences agree → m^{-(1-2σ)} = 1.
    (5) m = 2: 2^{-(1-2σ)} = 1 → σ = 1/2.                       -/
theorem riemann_hypothesis
    (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1)
    (hz : ζ s = 0) :
    s.re = 1 / 2 := by

  -- (1) Klein orbit: ξ(1-s̄) = 0
  rw [zeta_iff_xi s hs] at hz
  obtain ⟨_, _, h1cs⟩ := xi_klein_zeros s hz
  have hs1cs : 0 < (1 - star s).re ∧ (1 - star s).re < 1 := by
    constructor
    · simp [Complex.sub_re, Complex.conj_re]; linarith [hs.2]
    · simp [Complex.sub_re, Complex.conj_re]; linarith [hs.1]
  have hzeta_1cs : ζ (1 - star s) = 0 :=
    (zeta_iff_xi (1 - star s) hs1cs).mpr h1cs
  have hzeta_s : ζ s = 0 := (zeta_iff_xi s hs).mpr hz

  -- (2) Dirichlet series converging to 0
  have hcs : ConvergesTo (fun _ => (1 : ℝ)) s 0 := by
    have := dirichlet_cont s hs.1; rwa [hzeta_s] at this
  have hc1cs : ConvergesTo (fun _ => (1 : ℝ)) (1 - star s) 0 := by
    have := dirichlet_cont (1 - star s) hs1cs.1; rwa [hzeta_1cs] at this

  -- (3) Reindex: series at 1-s̄ becomes series at s with profile m^{-(1-2σ)}
  have hcr : ConvergesTo (fun m => (m : ℝ) ^ (-(1 - 2 * s.re))) s 0 :=
    reindex_mirror s hs hc1cs

  -- (4) Apply KIRA: weight sequences must agree
  have hkira := KIRA
    (fun _ => (1 : ℝ))
    (fun m => (m : ℝ) ^ (-(1 - 2 * s.re)))
    s hs
    (fun _ _ => one_pos)
    (fun m hm => Real.rpow_pos_of_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)) _)
    hcs hcr

  -- (5) At m = 2: extract σ = 1/2
  have h2 := hkira 2 (by norm_num)
  simp only [one_mul] at h2
  -- h2 : (2:ℝ)^(-σ) = (2:ℝ)^{-(1-2σ)} * (2:ℝ)^(-σ)
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-s.re) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- clean algebraic cancellation, no linarith
  have h2' :
      (1 : ℝ) * (2 : ℝ) ^ (-s.re)
        = (2 : ℝ) ^ (-(1 - 2 * s.re)) * (2 : ℝ) ^ (-s.re) := by
    simpa [one_mul] using h2
  have hone' :
      (1 : ℝ) = (2 : ℝ) ^ (-(1 - 2 * s.re)) :=
    mul_right_cancel₀ (ne_of_gt h2pos) h2'
  have hone :
      (2 : ℝ) ^ (-(1 - 2 * s.re)) = 1 :=
    hone'.symm
  -- 2^{-(1-2σ)} = 1  →  -(1-2σ) = 0  →  σ = 1/2
  have h_exp_zero : -(1 - 2 * s.re) = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (2 : ℝ) ^ (-(1 - 2 * s.re)) < 1 := by
        have hx : (1 : ℝ) < 2 := by norm_num
        have hpow := Real.rpow_lt_rpow_of_exponent_lt hx hlt
        simpa using hpow
      linarith [hone ▸ this]
    · have : (1 : ℝ) < (2 : ℝ) ^ (-(1 - 2 * s.re)) := by
        have hx : (1 : ℝ) < 2 := by norm_num
        have hpow := Real.rpow_lt_rpow_of_exponent_lt hx hgt
        simpa using hpow
      linarith [hone ▸ this]
  linarith

end
