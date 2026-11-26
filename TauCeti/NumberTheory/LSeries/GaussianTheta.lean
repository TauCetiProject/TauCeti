/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Data.PNat.Basic
public import Mathlib.NumberTheory.LSeries.Basic

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.PNat.Equiv
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Mellin
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.LSeries.Dilation

/-!
# Gaussian theta series with bounded coefficients

We sum rescaled Gaussian monomials `x^j * exp (-π x²)` against positive-index coefficients.
For degrees `j ∈ {0, 1}`, multiplying by the square root of the scale gives the normalized
series, with norm at most `3 * exp (-u) / √u` for unit-bounded coefficients and `u > 0`.

The Mellin transform of the unnormalized sum factors into the Dirichlet series of its
coefficients and half the archimedean gamma factor. On `Re s = 2`, the error from omitting
scales at most `r` is linear in `r` for bounded coefficients.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`. The file
`grh/src/Lib/Analytic/DirichletTheta.lean` supplies `New.gaussianMonomial`, `New.gaussianTheta`,
`New.thetaSeries` and `New.gaussianMellin`. The geometric comparison follows
`New.norm_gaussianMonomial_le` and `New.summable_and_norm_gaussianTheta_le` from that file.
Here the weight bound uses the absolute value of the argument, and the coefficient bound
is imposed only at positive indices. The unnormalized Mellin factorization follows
`mellin_gaussianTheta` from the same file. The cutoff estimate corresponds to the omitted
integral in `New.norm_mul_mollifier_sub_le` in the adjacent `QuadraticTwist.lean`.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti

/-- The Gaussian weight with monomial degree `j`. -/
def gaussianMonomial (j : ℕ) (x : ℝ) : ℝ := x ^ j * exp (-π * x ^ 2)

/-- The Gaussian monomial is a power times the Gaussian. -/
theorem gaussianMonomial_def (j : ℕ) (x : ℝ) :
    gaussianMonomial j x = x ^ j * exp (-π * x ^ 2) := (rfl)

/-- The even Gaussian weight is the Gaussian itself. -/
@[simp] theorem gaussianMonomial_zero (x : ℝ) : gaussianMonomial 0 x = exp (-π * x ^ 2) := by
  simp [gaussianMonomial]

/-- The odd Gaussian weight is the Gaussian multiplied by its argument. -/
@[simp] theorem gaussianMonomial_one (x : ℝ) : gaussianMonomial 1 x = x * exp (-π * x ^ 2) := by
  simp [gaussianMonomial]

/-- The sum of the Gaussian monomials against the positive-index coefficients of `c`. -/
def gaussianTheta (j : ℕ) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ+, c n * gaussianMonomial j (n * u)

/-- Expand the theta sum over the positive integers. -/
theorem gaussianTheta_def (j : ℕ) (c : ℕ → ℂ) (u : ℝ) :
    gaussianTheta j c u = ∑' n : ℕ+, c n * gaussianMonomial j (n * u) := by
  unfold gaussianTheta
  rfl

/-- The theta sum with zero coefficients vanishes. -/
@[simp] theorem gaussianTheta_zero (j : ℕ) (u : ℝ) : gaussianTheta j 0 u = 0 := by
  simp [gaussianTheta_def]

/-- The Gaussian theta series with square-root normalization. -/
def gaussianThetaSeries (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  (√u : ℝ) * gaussianTheta j c u

/-- The normalized theta series is the theta sum times the square root of the scale. -/
theorem gaussianThetaSeries_def (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) :
    gaussianThetaSeries j c u = (√u : ℝ) * gaussianTheta j c u := by
  unfold gaussianThetaSeries
  rfl

/-- The Mellin transform of the Gaussian weight of parity `j`. -/
def gaussianMellin (j : Fin 2) : ℂ → ℂ := mellin fun x ↦ (gaussianMonomial j x : ℂ)

/-- Express the Gaussian Mellin weight as a Mellin transform. -/
theorem gaussianMellin_def (j : Fin 2) :
    gaussianMellin j = mellin (fun x ↦ (gaussianMonomial j x : ℂ)) := by
  unfold gaussianMellin
  rfl

variable {j : Fin 2} {c : ℕ → ℂ}

/-- The Mellin transform of the parity-`j` Gaussian in its half-plane of convergence. -/
theorem gaussianMellin_eq {s : ℂ} (hs : -(j.val : ℝ) < s.re) :
    gaussianMellin j s =
      (1 / 2 : ℂ) * (π : ℂ) ^ (-(s + j.val) / 2) * Complex.Gamma ((s + j.val) / 2) := by
  rw [gaussianMellin_def]
  have h := (hasMellin_pow_mul_exp_neg_pi_mul_sq j.val (s := s) (by linarith)).2
  simpa only [gaussianMonomial_def, Complex.Gammaℝ_def, neg_div, div_eq_inv_mul, one_mul,
    mul_assoc] using h

/-- The unnormalized Gaussian theta series is measurable in the scale. -/
@[fun_prop] theorem measurable_gaussianTheta {k : ℕ} : Measurable (gaussianTheta k c) := by
  rw [funext (gaussianTheta_def k c)]
  fun_prop [gaussianMonomial]

/-- The square-root-normalized Gaussian theta series is measurable in the scale. -/
@[fun_prop] theorem measurable_gaussianThetaSeries : Measurable (gaussianThetaSeries j c) := by
  rw [funext (gaussianThetaSeries_def j c)]
  exact (Complex.measurable_ofReal.comp continuous_sqrt.measurable).mul measurable_gaussianTheta

/-- A pointwise exponential majorant for the Gaussian weights of both parities. -/
private theorem norm_gaussianMonomial_le (j : Fin 2) (x : ℝ) :
    ‖gaussianMonomial j x‖ ≤ 3 * exp (-|x|) ^ 2 := by
  have hpow : |x| ^ j.val ≤ exp |x| :=
    calc |x| ^ j.val ≤ |x| + 1 := by fin_cases j <;> simp
      _ ≤ exp |x| := add_one_le_exp _
  have hexp : |x| + -π * x ^ 2 ≤ 1 + (-|x| + -|x|) := by
    rw [← sq_abs x]
    nlinarith [pi_gt_three, sq_nonneg (|x| - 2⁻¹), sq_nonneg |x|]
  calc ‖gaussianMonomial j x‖ = |x| ^ j.val * exp (-π * x ^ 2) := by
        simp [gaussianMonomial]
    _ ≤ exp |x| * exp (-π * x ^ 2) := by gcongr
    _ ≤ exp (1 + (-|x| + -|x|)) := by rw [← Real.exp_add]; gcongr
    _ = exp 1 * exp (-|x|) ^ 2 := by rw [Real.exp_add, Real.exp_add, sq]
    _ ≤ 3 * exp (-|x|) ^ 2 := by gcongr; exact exp_one_lt_three.le

/-- The Mellin integral of the parity-`j` Gaussian converges for `-j < re s`. -/
theorem mellinConvergent_gaussianMonomial {s : ℂ} (hs : -(j.val : ℝ) < s.re) :
    MellinConvergent (fun x ↦ (gaussianMonomial j x : ℂ)) s := by
  simpa only [gaussianMonomial_def] using
    (hasMellin_pow_mul_exp_neg_pi_mul_sq j.val (s := s) (by linarith)).1

private theorem norm_gaussianTheta_term_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (u : ℝ)
    (n : ℕ+) :
    ‖c n * gaussianMonomial j (n * u)‖ ≤ 3 * (exp (-|u|) ^ 2) ^ (n : ℕ) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  grw [norm_mul, hc, Complex.norm_real, norm_gaussianMonomial_le, abs_mul, abs_of_nonneg hn]
  simp [← Real.exp_natCast_mul, field]

private theorem hasSum_gaussianTheta_majorant {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ+ ↦ 3 * (exp (-u) ^ 2) ^ (n : ℕ))
      (3 * (exp (-u) ^ 2 / (1 - exp (-u) ^ 2))) := by
  have hr : ‖exp (-u) ^ 2‖ < 1 := by simpa using hu
  exact (hasSum_geometric_pnat hr).mul_left 3

private theorem norm_gaussianTheta_term_le_factorial (k : ℕ) {M u : ℝ} (hu : 0 < u)
    (n : ℕ+) (hc : ‖c n‖ ≤ M) :
    ‖c n * gaussianMonomial k (n * u)‖ ≤
      (M * (k.factorial : ℝ) * exp 1) * exp (-u) ^ (n : ℕ) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  rw [norm_mul, Complex.norm_real, gaussianMonomial_def]
  calc
    _ ≤ M * ((k.factorial : ℝ) * exp 1 * exp (-|(n : ℝ) * u|)) :=
      mul_le_mul hc (abs_pow_mul_exp_neg_pi_mul_sq_le k _) (abs_nonneg _) ((norm_nonneg _).trans hc)
    _ = _ := by
      rw [abs_mul, abs_of_nonneg hn, abs_of_pos hu, ← Real.exp_natCast_mul, mul_neg]
      simp only [mul_assoc]

/-- The Gaussian theta sum converges absolutely at positive scales for bounded coefficients. -/
theorem summable_gaussianTheta {k : ℕ} {M : ℝ} (hc : ∀ n : ℕ+, ‖c n‖ ≤ M)
    {u : ℝ} (hu : 0 < u) : Summable fun n : ℕ+ ↦ c n * gaussianMonomial k (n * u) := by
  have hq : ‖exp (-u)‖ < 1 := by simpa using hu
  exact ((hasSum_geometric_pnat hq).mul_left (M * (k.factorial : ℝ) * exp 1)).summable
    |>.of_norm_bounded fun n ↦ norm_gaussianTheta_term_le_factorial k hu n (hc n)

/-- For coefficients of norm at most `M`, the degree-`k` theta sum at `u > 0` is bounded in norm
by `M k! e / (exp u − 1)`. -/
theorem norm_gaussianTheta_le_factorial (k : ℕ) {M u : ℝ} (hc : ∀ n : ℕ+, ‖c n‖ ≤ M)
    (hu : 0 < u) : ‖gaussianTheta k c u‖ ≤ M * (k.factorial : ℝ) * exp 1 / (exp u - 1) := by
  have hq : ‖exp (-u)‖ < 1 := by simpa using hu
  rw [gaussianTheta_def]
  refine (tsum_of_norm_bounded ((hasSum_geometric_pnat hq).mul_left _) fun n ↦
    norm_gaussianTheta_term_le_factorial k hu n (hc n)).trans_eq ?_
  rw [Real.exp_neg]
  field_simp [(exp_pos u).ne', (Real.one_lt_exp_iff.mpr hu).ne']

/-- At positive scales the unnormalized theta sum is bounded by `3 * exp (-u) / u`
for coefficients of norm at most one. -/
theorem norm_gaussianTheta_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    ‖gaussianTheta j c u‖ ≤ 3 * exp (-u) / u := by
  let r : ℝ := exp (-u) ^ 2
  have hexp_mul : exp u * exp (-u) = 1 := by simp [← Real.exp_add]
  have hdenom : u * exp (-u) ≤ 1 - r := by
    nlinarith [add_one_le_exp u, exp_pos (-u), exp_le_one_iff.2 (neg_nonpos.2 hu.le), hexp_mul]
  have hsum : 3 * (r / (1 - r)) ≤ 3 * exp (-u) / u := by
    calc 3 * (r / (1 - r)) ≤ 3 * (r / (u * exp (-u))) := by gcongr
      _ = 3 * exp (-u) / u := by simp [r, field]
  rw [gaussianTheta_def]
  refine (tsum_of_norm_bounded (hasSum_gaussianTheta_majorant hu) fun n ↦ ?_).trans hsum
  simpa only [abs_of_pos hu] using norm_gaussianTheta_term_le (j := j) hc u n

/-- The normalized theta series satisfies the bound `3 * exp (-u) / √u`.
At nonpositive scales both sides vanish under the real square-root convention. -/
theorem norm_gaussianThetaSeries_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (u : ℝ) :
    ‖gaussianThetaSeries j c u‖ ≤ 3 * exp (-u) / √u := by
  obtain hu | hu := le_or_gt u 0
  · simp [gaussianThetaSeries_def, sqrt_eq_zero_of_nonpos hu]
  rw [gaussianThetaSeries_def, norm_mul, Complex.norm_real, norm_of_nonneg (sqrt_nonneg u)]
  calc √u * ‖gaussianTheta j c u‖ ≤ √u * (3 * exp (-u) / u) := by
        gcongr
        exact norm_gaussianTheta_le hc hu
    _ = 3 * exp (-u) * (√u / u) := by ring
    _ = 3 * exp (-u) / √u := by rw [sqrt_div_self', mul_one_div]

/-- The norm of the normalized theta series is integrable against `du / u` on a positive tail. -/
theorem integrableOn_norm_gaussianThetaSeries_div (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {r : ℝ}
    (hr : 0 < r) : IntegrableOn (fun u ↦ ‖gaussianThetaSeries j c u‖ / u) (Ioi r) := by
  have hmajorant : IntegrableOn (fun u ↦ 3 * exp (-u) / √r / r) (Ioi r) :=
    (((integrableOn_exp_neg_Ioi r).const_mul 3).div_const √r).div_const r
  refine hmajorant.mono'
    (measurable_gaussianThetaSeries.norm.div measurable_id).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦ ?_
  have hrle : r ≤ u := le_of_lt hu
  have hu0 : 0 < u := hr.trans_le hrle
  grw [norm_of_nonneg (by positivity), norm_gaussianThetaSeries_le hc]
  gcongr

/-- In the common domain of absolute convergence, the Mellin transform of the theta sum
is the Dirichlet series multiplied by `Γℝ(s+k)/2`. -/
theorem hasMellin_gaussianTheta (k : ℕ) {s : ℂ} (hc : LSeriesSummable c s)
    (hs : 0 < s.re + k) :
    HasMellin (gaussianTheta k c) s (LSeries c s * (Complex.Gammaℝ (s + k) / 2)) := by
  have h := hasMellin_pow_mul_exp_neg_pi_mul_sq k hs
  have heq (u : ℝ) : gaussianTheta k c u =
      ∑' n : ℕ, c (n + 1) * (gaussianMonomial k ((n + 1 : ℕ) * u) : ℂ) := by
    rw [gaussianTheta_def]
    exact (Equiv.pnatEquivNat.symm.tsum_eq (fun n : ℕ+ ↦ c n * gaussianMonomial k (n * u))).symm
  simpa only [funext heq, gaussianMonomial_def, h.2] using hc.hasMellin_tsum_dilate h.1

/-- At `Re s = 2`, omitting scales up to `r ≥ 0` changes the Mellin transform by at most
`M k! e r`, uniformly in the imaginary part of `s`. -/
theorem norm_integral_gaussianTheta_sub_le (k : ℕ) {M r : ℝ} (hc : ∀ n : ℕ+, ‖c n‖ ≤ M)
    (hr : 0 ≤ r) {s : ℂ} (hs : s.re = 2) :
    ‖(∫ t : ℝ in Ioi r, (t : ℂ) ^ (s - 1) * gaussianTheta k c t) -
      LSeries c s * (Complex.Gammaℝ (s + k) / 2)‖ ≤ M * (k.factorial : ℝ) * exp 1 * r := by
  have hc' (n : ℕ) (hn : n ≠ 0) : ‖c n‖ ≤ M := hc ⟨n, Nat.pos_of_ne_zero hn⟩
  obtain ⟨hint, hval⟩ := hasMellin_gaussianTheta k
    (LSeriesSummable_of_bounded_of_one_lt_re hc' (s := s) (by linarith)) (by linarith)
  simp only [MellinConvergent, mellin, smul_eq_mul] at hint hval
  rw [← hval, norm_sub_rev, ← setIntegral_sdiff measurableSet_Ioi hint (Ioi_subset_Ioi hr),
    Ioi_sdiff_Ioi]
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 r),
      ‖(t : ℂ) ^ (s - 1) * gaussianTheta k c t‖ ≤ M * (k.factorial : ℝ) * exp 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hexp : (2 : ℝ) - 1 = 1 := by norm_num
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, hs, Complex.one_re,
      hexp, Real.rpow_one]
    have hden : 0 < exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht.1)
    have hM : 0 ≤ M := (norm_nonneg _).trans (hc 1)
    calc
      _ ≤ t * (M * (k.factorial : ℝ) * exp 1 / (exp t - 1)) :=
        mul_le_mul_of_nonneg_left (norm_gaussianTheta_le_factorial k hc ht.1) ht.1.le
      _ ≤ _ := by
        rw [mul_comm t, div_mul_eq_mul_div, div_le_iff₀ hden]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) (by positivity)
  simpa [hr, mul_comm] using norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    measure_Ioc_lt_top hbound

end TauCeti
