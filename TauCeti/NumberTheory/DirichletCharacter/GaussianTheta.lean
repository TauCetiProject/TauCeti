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

/-!
# Gaussian theta series with bounded coefficients

The even and odd Gaussian weights are `exp (-π x²)` and `x * exp (-π x²)`. We sum the
rescaled weights against coefficients indexed by the positive integers, and multiply by the
square root of the scale to form the normalized theta series. A single geometric majorant
gives absolute convergence and the bound `3 * exp (-u) / √u` for positive scales `u`.

The Mellin transform of the weight and the tail integral of the series and its Möbius twist
use the normalization of the ShortGRH zero-free region argument. The definitions and
geometric comparison follow the shorter RH formalization, in `Lib/Analytic/DirichletTheta`
and `Lib/Analytic/QuadraticTwist`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- The Gaussian weight of parity `j ∈ {0, 1}`. -/
def gaussianMonomial (j : Fin 2) (x : ℝ) : ℝ := x ^ j.val * exp (-π * x ^ 2)

/-- The sum of the parity-weighted Gaussians against the positive-index coefficients of `c`. -/
def gaussianTheta (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ+, c n * gaussianMonomial j (n * u)

/-- The Gaussian theta series with square-root normalization. -/
def gaussianThetaSeries (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  (√u : ℝ) * gaussianTheta j c u

/-- The Mellin transform of the Gaussian weight of parity `j`. -/
def gaussianMellin (j : Fin 2) : ℂ → ℂ := mellin fun x ↦ (gaussianMonomial j x : ℂ)

/-- The joint tail of the normalized theta series of `c` and its Möbius twist, above `1 / T`. -/
def gaussianThetaTailIntegral (j : Fin 2) (c : ℕ → ℂ) (T : ℝ) : ℝ :=
  ∫ u in Ioi T⁻¹, (‖gaussianThetaSeries j c u‖ +
    ‖gaussianThetaSeries j (fun n ↦ c n * μ n) u‖) / u

variable {j : Fin 2} {c : ℕ → ℂ}

/-- The unnormalized Gaussian theta series is measurable in the scale. -/
theorem measurable_gaussianTheta : Measurable (gaussianTheta j c) := by
  fun_prop [gaussianTheta, gaussianMonomial]

/-- The square-root-normalized Gaussian theta series is measurable in the scale. -/
theorem measurable_gaussianThetaSeries : Measurable (gaussianThetaSeries j c) :=
  (Complex.measurable_ofReal.comp continuous_sqrt.measurable).mul measurable_gaussianTheta

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

/-- At positive scales the unnormalized theta series converges absolutely and is bounded
by `3 * exp (-u) / u` for coefficients of norm at most one. -/
theorem summable_and_norm_gaussianTheta_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    (Summable fun n : ℕ+ ↦ c n * gaussianMonomial j (n * u)) ∧
      ‖gaussianTheta j c u‖ ≤ 3 * exp (-u) / u := by
  let r : ℝ := exp (-u) ^ 2
  have hr : |r| < 1 := by simpa [r] using hu
  have hgeom : HasSum (fun n : ℕ+ ↦ 3 * r ^ (n : ℕ)) (3 * (1 - r)⁻¹ - 3) :=
    (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ ↦ 3 * r ^ n)).2 <| by
      simpa using (hasSum_nat_add_iff' 1).2 ((hasSum_geometric_of_abs_lt_one hr).mul_left 3)
  have hterm (n : ℕ+) : ‖c n * gaussianMonomial j (n * u)‖ ≤ 3 * r ^ (n : ℕ) := by
    have hn : 0 ≤ (n : ℝ) * u := by positivity
    grw [norm_mul, hc, Complex.norm_real, norm_gaussianMonomial_le, abs_of_nonneg hn]
    simp [r, ← Real.exp_natCast_mul, field]
  have hdenom : u * exp (-u) ≤ 1 - r := by
    nlinarith [add_one_le_exp u, exp_pos (-u), exp_le_one_iff.2 (neg_nonpos.2 hu.le),
      show exp u * exp (-u) = 1 by simp [← Real.exp_add]]
  have hsum : 3 * (1 - r)⁻¹ - 3 ≤ 3 * exp (-u) / u := by
    have hpos : 0 < 1 - r := (mul_pos hu (exp_pos _)).trans_le hdenom
    calc 3 * (1 - r)⁻¹ - 3 = 3 * r / (1 - r) := by field
      _ ≤ 3 * r / (u * exp (-u)) := by gcongr
      _ = 3 * exp (-u) / u := by simp [r, field]
  exact ⟨hgeom.summable.of_norm_bounded hterm, (tsum_of_norm_bounded hgeom hterm).trans hsum⟩

/-- The normalized theta series satisfies the bound `3 * exp (-u) / √u`.
At nonpositive scales both sides vanish under the real square-root convention. -/
theorem norm_gaussianThetaSeries_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (u : ℝ) :
    ‖gaussianThetaSeries j c u‖ ≤ 3 * exp (-u) / √u := by
  obtain hu | hu := le_or_gt u 0
  · simp [gaussianThetaSeries, sqrt_eq_zero_of_nonpos hu]
  rw [gaussianThetaSeries, norm_mul, Complex.norm_real, norm_of_nonneg (sqrt_nonneg u)]
  calc √u * ‖gaussianTheta j c u‖ ≤ √u * (3 * exp (-u) / u) := by
        gcongr
        exact (summable_and_norm_gaussianTheta_le hc hu).2
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

end TauCeti
