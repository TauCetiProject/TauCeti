/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.PNat.Basic

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian theta series with bounded coefficients

The even and odd Gaussian weights are `exp (-π x²)` and `x * exp (-π x²)`. We sum the
rescaled weights against coefficients indexed by the positive integers, and multiply by the
square root of the scale to form the normalized theta series. A single geometric majorant
gives absolute convergence and the bound `3 * exp (-u) / √u` for positive scales `u`.

The Mellin transform of the Gaussian weight and the joint tail of the theta series and its
Möbius twist are used to bound zeros of quadratic twists of Dirichlet L-functions.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`. The file
`grh/src/Lib/Analytic/DirichletTheta.lean` supplies `New.gaussianMonomial`, `New.gaussianTheta`,
`New.thetaSeries` and `New.gaussianMellin`. The geometric comparison follows
`New.norm_gaussianMonomial_le` and `New.summable_and_norm_gaussianTheta_le` from that file.
Here the weight bound uses the absolute value of the argument, and the coefficient bound
is imposed only at positive indices. The joint tail is adapted from `New.thetaTailIntegral`
in `grh/src/Lib/Analytic/QuadraticTwist.lean`.
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- The Gaussian weight of parity `j ∈ {0, 1}`. -/
def gaussianMonomial (j : Fin 2) (x : ℝ) : ℝ := x ^ j.val * exp (-π * x ^ 2)

/-- The even Gaussian weight is the Gaussian itself. -/
@[simp] theorem gaussianMonomial_zero (x : ℝ) : gaussianMonomial 0 x = exp (-π * x ^ 2) := by
  simp [gaussianMonomial]

/-- The odd Gaussian weight is the Gaussian multiplied by its argument. -/
@[simp] theorem gaussianMonomial_one (x : ℝ) : gaussianMonomial 1 x = x * exp (-π * x ^ 2) := by
  simp [gaussianMonomial]

/-- The sum of the parity-weighted Gaussians against the positive-index coefficients of `c`. -/
def gaussianTheta (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ+, c n * gaussianMonomial j (n * u)

/-- Expand the theta sum over the positive integers. -/
theorem gaussianTheta_def (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) :
    gaussianTheta j c u = ∑' n : ℕ+, c n * gaussianMonomial j (n * u) := by
  unfold gaussianTheta
  rfl

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

/-- The joint theta tail used in quadratic-twist nonvanishing arguments. It integrates the
norms of the normalized theta series of `c` and its Möbius twist against `du / u` above `1 / T`. -/
def quadraticTwistGaussianThetaTailIntegral (j : Fin 2) (c : ℕ → ℂ) (T : ℝ) : ℝ :=
  ∫ u in Ioi T⁻¹, (‖gaussianThetaSeries j c u‖ +
    ‖gaussianThetaSeries j (fun n ↦ c n * μ n) u‖) / u

/-- Expand the joint quadratic-twist tail as a set integral. -/
theorem quadraticTwistGaussianThetaTailIntegral_def (j : Fin 2) (c : ℕ → ℂ) (T : ℝ) :
    quadraticTwistGaussianThetaTailIntegral j c T =
      ∫ u in Ioi T⁻¹, (‖gaussianThetaSeries j c u‖ +
        ‖gaussianThetaSeries j (fun n ↦ c n * μ n) u‖) / u := by
  unfold quadraticTwistGaussianThetaTailIntegral
  rfl

variable {j : Fin 2} {c : ℕ → ℂ}

/-- The unnormalized Gaussian theta series is measurable in the scale. -/
theorem measurable_gaussianTheta : Measurable (gaussianTheta j c) := by
  rw [funext (gaussianTheta_def j c)]
  fun_prop [gaussianMonomial]

/-- The square-root-normalized Gaussian theta series is measurable in the scale. -/
theorem measurable_gaussianThetaSeries : Measurable (gaussianThetaSeries j c) := by
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
  rw [MellinConvergent]
  have hmeas : Measurable (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) • (gaussianMonomial j x : ℂ)) := by
    fun_prop [gaussianMonomial]
  refine (integrable_norm_iff hmeas.aestronglyMeasurable).mp <|
    (integrableOn_rpow_mul_exp_neg_mul_sq pi_pos (s := s.re - 1 + j.val)
      (by linarith)).congr_fun (fun x (hx : 0 < x) ↦ ?_) measurableSet_Ioi
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re,
    Complex.norm_real, gaussianMonomial, norm_mul, norm_of_nonneg (pow_nonneg hx.le _),
    norm_of_nonneg (exp_nonneg _), ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hx]

private theorem norm_gaussianTheta_term_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (u : ℝ)
    (n : ℕ+) :
    ‖c n * gaussianMonomial j (n * u)‖ ≤ 3 * (exp (-|u|) ^ 2) ^ (n : ℕ) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  grw [norm_mul, hc, Complex.norm_real, norm_gaussianMonomial_le, abs_mul, abs_of_nonneg hn]
  simp [← Real.exp_natCast_mul, field]

private theorem hasSum_gaussianTheta_majorant {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ+ ↦ 3 * (exp (-u) ^ 2) ^ (n : ℕ))
      (3 * (1 - exp (-u) ^ 2)⁻¹ - 3) := by
  have hr : |exp (-u) ^ 2| < 1 := by simpa using hu
  refine (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ ↦ 3 * (exp (-u) ^ 2) ^ n)).2 ?_
  simpa using (hasSum_nat_add_iff' 1).2 ((hasSum_geometric_of_abs_lt_one hr).mul_left 3)

/-- The Gaussian theta sum converges absolutely at positive scales for unit-bounded
coefficients. -/
theorem summable_gaussianTheta (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ+ ↦ c n * gaussianMonomial j (n * u) := by
  refine (hasSum_gaussianTheta_majorant hu).summable.of_norm_bounded fun n ↦ ?_
  simpa only [abs_of_pos hu] using norm_gaussianTheta_term_le (j := j) hc u n

/-- At positive scales the unnormalized theta sum is bounded by `3 * exp (-u) / u`
for coefficients of norm at most one. -/
theorem norm_gaussianTheta_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    ‖gaussianTheta j c u‖ ≤ 3 * exp (-u) / u := by
  let r : ℝ := exp (-u) ^ 2
  have hdenom : u * exp (-u) ≤ 1 - r := by
    nlinarith [add_one_le_exp u, exp_pos (-u), exp_le_one_iff.2 (neg_nonpos.2 hu.le),
      show exp u * exp (-u) = 1 by simp [← Real.exp_add]]
  have hsum : 3 * (1 - r)⁻¹ - 3 ≤ 3 * exp (-u) / u := by
    have hpos : 0 < 1 - r := (mul_pos hu (exp_pos _)).trans_le hdenom
    calc 3 * (1 - r)⁻¹ - 3 = 3 * r / (1 - r) := by field
      _ ≤ 3 * r / (u * exp (-u)) := by gcongr
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

/-- The full quadratic-twist theta tail integrand is integrable for positive `T` and
unit-bounded coefficients. -/
theorem integrableOn_quadraticTwistGaussianThetaTailIntegrand (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun u ↦ (‖gaussianThetaSeries j c u‖ +
      ‖gaussianThetaSeries j (fun n ↦ c n * μ n) u‖) / u) (Ioi T⁻¹) := by
  have hμ (n : ℕ+) : ‖c n * (μ n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    have hnorm : ‖(μ n : ℂ)‖ ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    calc ‖c n‖ * ‖(μ n : ℂ)‖ ≤ ‖c n‖ := mul_le_of_le_one_right (norm_nonneg _) hnorm
      _ ≤ 1 := hc n
  have h := (integrableOn_norm_gaussianThetaSeries_div (j := j) hc (inv_pos.mpr hT)).add
    (integrableOn_norm_gaussianThetaSeries_div (j := j) (c := fun n ↦ c n * μ n)
      hμ (inv_pos.mpr hT))
  refine h.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  exact (add_div ..).symm

/-- The quadratic-twist theta tail integral is nonnegative. -/
theorem quadraticTwistGaussianThetaTailIntegral_nonneg (T : ℝ) :
    0 ≤ quadraticTwistGaussianThetaTailIntegral j c T := by
  rw [quadraticTwistGaussianThetaTailIntegral_def]
  refine integral_nonneg fun u ↦ ?_
  obtain hu | hu := le_or_gt u 0
  · simp [gaussianThetaSeries_def, sqrt_eq_zero_of_nonpos hu]
  · positivity

end TauCeti
