/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Analysis.SpecialFunctions.Gaussian.Mellin
import TauCeti.NumberTheory.LSeries.Dilation

/-!
# Gaussian theta sums of Dirichlet coefficients

For a sequence `a`, consider the sum of `a n (n t)^j exp(-π (n t)^2)` over positive integers
`n`. Its Mellin transform factors into the Dirichlet series of `a` and `Γℝ(s+j)/2`. On the
line `Re s = 2`, truncating the Mellin integral below `r ≥ 0` incurs an error linear in `r`
for uniformly bounded coefficients.

This is the unscaled theta sum: `Lib/Analytic/DirichletTheta` of lsernau/grh-lean (`72fead1`)
multiplies it by `t^(1/2)` and shifts the Mellin argument by `-1/2`.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti

/-- The positive-index Gaussian theta sum with coefficients `a` and monomial weight of degree
`j`. The value of `a 0` does not enter the sum. -/
noncomputable def gaussianDirichletTheta (j : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, a (n + 1) * (((n + 1 : ℕ) * t) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) * t) ^ 2) : ℝ)

/-- The defining sum over strictly positive integers. -/
theorem gaussianDirichletTheta_def (j : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    gaussianDirichletTheta j a t =
    ∑' n : ℕ, a (n + 1) *
      (((n + 1 : ℕ) * t) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) * t) ^ 2) : ℝ) :=
  (rfl)

/-- The theta sum with the zero coefficient sequence vanishes. -/
@[simp] theorem gaussianDirichletTheta_zero (j : ℕ) (t : ℝ) :
    gaussianDirichletTheta j 0 t = 0 := by
  simp [gaussianDirichletTheta_def]

/-- A geometric bound for each summand of a Gaussian theta sum with bounded coefficients. -/
private theorem norm_gaussianDirichletTheta_term_le (j : ℕ) {a : ℕ → ℂ} {M t : ℝ}
    {n : ℕ} (ha : ‖a (n + 1)‖ ≤ M) :
    ‖a (n + 1) * (((n + 1 : ℕ) * t) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) * t) ^ 2) : ℝ)‖ ≤
      (M * (j.factorial : ℝ) * Real.exp 1) * Real.exp (-|t|) ^ (n + 1) := by
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  calc
    _ ≤ M * ((j.factorial : ℝ) * Real.exp 1 * Real.exp (-|((n + 1 : ℕ) : ℝ) * t|)) :=
      mul_le_mul ha (abs_pow_mul_exp_neg_pi_mul_sq_le j _) (abs_nonneg _) ((norm_nonneg _).trans ha)
    _ = _ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ)),
        ← Real.exp_natCast_mul, mul_neg]
      ring

/-- For bounded coefficients the Gaussian theta sum converges absolutely at every positive
argument. -/
theorem summable_norm_gaussianDirichletTheta (j : ℕ) {a : ℕ → ℂ} {M t : ℝ}
    (ha : ∀ n ≠ 0, ‖a n‖ ≤ M) (ht : 0 < t) :
    Summable fun n : ℕ ↦ ‖a (n + 1) *
      (((n + 1 : ℕ) * t) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) * t) ^ 2) : ℝ)‖ := by
  have hgeom := (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (Real.exp_nonneg (-t))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)))
  exact (hgeom.mul_left (M * (j.factorial : ℝ) * Real.exp 1)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun n ↦ by
      simpa only [abs_of_pos ht] using
        norm_gaussianDirichletTheta_term_le j (t := t) (ha _ (Nat.succ_ne_zero n))

/-- For coefficients of norm at most `M`, the theta sum at `t > 0` is at most
`M j! e / (exp t − 1)` in norm. -/
theorem norm_gaussianDirichletTheta_le (j : ℕ) {a : ℕ → ℂ} {M t : ℝ}
    (ha : ∀ n ≠ 0, ‖a n‖ ≤ M) (ht : 0 < t) :
    ‖gaussianDirichletTheta j a t‖ ≤ M * (j.factorial : ℝ) * Real.exp 1 / (Real.exp t - 1) := by
  have hq := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hgeom := summable_geometric_of_lt_one (Real.exp_nonneg (-t)) hq
  have hnorm := summable_norm_gaussianDirichletTheta j ha ht
  rw [gaussianDirichletTheta_def]
  refine (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum
    (fun n ↦ by simpa only [abs_of_pos ht] using
      norm_gaussianDirichletTheta_term_le j (t := t) (ha _ (Nat.succ_ne_zero n)))
    (((summable_nat_add_iff 1).2 hgeom).mul_left _)).trans_eq ?_)
  simp_rw [tsum_mul_left, pow_succ, tsum_mul_right, tsum_geometric_of_lt_one (Real.exp_nonneg _) hq,
    Real.exp_neg]
  have he := Real.exp_pos t
  field_simp [he.ne', ne_of_gt (Real.one_lt_exp_iff.mpr ht), ne_of_gt hq]

/-- The Mellin transform of the Gaussian theta sum is `LSeries a s` multiplied by
`Γℝ(s+j)/2` in the common domain of absolute convergence. -/
theorem hasMellin_gaussianDirichletTheta (j : ℕ) {a : ℕ → ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hs : 0 < s.re + j) :
    HasMellin (gaussianDirichletTheta j a) s (LSeries a s * (Gammaℝ (s + j) / 2)) := by
  have h := hasMellin_pow_mul_exp_neg_pi_mul_sq j hs
  simpa only [funext (gaussianDirichletTheta_def j a), h.2] using ha.hasMellin_tsum_dilate h.1

/-- At `Re s = 2`, cutting off the integral for the Gaussian theta sum at `r ≥ 0` changes its
Mellin transform by at most `M j! e r`, uniformly in the imaginary part. -/
theorem norm_integral_gaussianDirichletTheta_sub (j : ℕ) {a : ℕ → ℂ} {M r : ℝ}
    (ha : ∀ n ≠ 0, ‖a n‖ ≤ M) (hr : 0 ≤ r) {s : ℂ} (hs : s.re = 2) :
    ‖(∫ t : ℝ in Ioi r, (t : ℂ) ^ (s - 1) * gaussianDirichletTheta j a t) -
      LSeries a s * (Gammaℝ (s + j) / 2)‖ ≤ M * (j.factorial : ℝ) * Real.exp 1 * r := by
  obtain ⟨hint, hval⟩ := hasMellin_gaussianDirichletTheta j
    (LSeriesSummable_of_bounded_of_one_lt_re ha (s := s) (by linarith)) (by linarith)
  simp only [MellinConvergent, mellin, smul_eq_mul] at hint hval
  rw [← hval, ← Ioc_union_Ioi_eq_Ioi hr, setIntegral_union
    Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hr)), add_comm (_ : ℂ),
    sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 r),
      ‖(t : ℂ) ^ (s - 1) * gaussianDirichletTheta j a t‖ ≤ M * (j.factorial : ℝ) * Real.exp 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, hs, one_re]
    norm_num
    have hden : 0 < Real.exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht.1)
    have hM : 0 ≤ M := (norm_nonneg _).trans (ha 1 one_ne_zero)
    calc
      _ ≤ t * (M * (j.factorial : ℝ) * Real.exp 1 / (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_left (norm_gaussianDirichletTheta_le j ha ht.1) ht.1.le
      _ ≤ _ := by
        rw [mul_comm t, div_mul_eq_mul_div, div_le_iff₀ hden]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) (by positivity)
  simpa [hr, mul_comm] using norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    measure_Ioc_lt_top hbound

end TauCeti
