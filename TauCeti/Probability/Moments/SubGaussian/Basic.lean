/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Basic properties of sub-Gaussian moment-generating functions

The quadratic MGF bound forces a sub-Gaussian random variable to have mean zero, is monotone in
the variance proxy, and bounds its first absolute moment by `√(2c)`.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace ProbabilityTheory.HasSubgaussianMGF

/-- Monotonicity of `HasSubgaussianMGF` in the variance proxy. -/
theorem mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c₁ c₂ : ℝ≥0}
    (h : HasSubgaussianMGF X c₁ μ) (hle : c₁ ≤ c₂) : HasSubgaussianMGF X c₂ μ :=
  ⟨h.integrable_exp_mul, fun t ↦ (h.mgf_le t).trans <| by gcongr⟩

/-- Under a zero or probability measure, a sub-Gaussian MGF bound forces the expectation to
vanish. -/
theorem integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) : μ[X] = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · simp
  have hset := hX.integrableExpSet_eq_univ
  have hm : 0 ∈ interior (integrableExpSet X μ) := by simp [hset]
  let g : ℝ → ℝ := (fun t ↦ Real.exp ((c : ℝ) * t ^ 2 / 2)) - mgf X μ
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [g, Pi.sub_apply] using sub_nonneg.mpr (hX.mgf_le t)
  have hd : HasDerivAt g (-μ[X]) 0 := by
    have he : HasDerivAt (fun t : ℝ ↦ Real.exp ((c : ℝ) * t ^ 2 / 2)) 0 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (c : ℝ)).div_const 2 |>.exp
        using 1 <;> simp
    have hx : HasDerivAt (mgf X μ) μ[X] 0 := by
      simpa using hasDerivAt_mgf hm
    simpa only [g, zero_sub] using he.sub hx
  exact neg_eq_zero.mp (hmin.hasDerivAt_eq_zero hd)

/-- The first absolute moment of a sub-Gaussian random variable is at most `√(2c)`. -/
theorem integral_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) : ∫ x, |X x| ∂μ ≤ sqrt (2 * c) := by
  by_cases hc : c = 0
  · subst c
    simpa using (integral_congr_ae <|
      h.ae_eq_zero_of_hasSubgaussianMGF_zero.fun_comp abs).le
  have hc' : 0 < (c : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  let t : ℝ := sqrt (2 / c)
  have ht : 0 < t := sqrt_pos.2 (div_pos (by norm_num) hc')
  have ht2 : (c : ℝ) * t ^ 2 / 2 = 1 := by
    dsimp [t]
    rw [sq_sqrt (by positivity)]
    field_simp
  have hts : t * sqrt (2 * c) = 2 := by
    rw [← sqrt_mul (by positivity : 0 ≤ 2 / (c : ℝ))]
    field_simp
    apply (sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  -- Normalize the exponential comparison at the scale of the variance proxy.
  have hpoint (x : Ω) :
      t * |X x| ≤ (exp (t * X x) + exp ((-t) * X x)) * exp (-1) := by
    calc t * |X x|
        ≤ exp (t * |X x| - 1) := by simpa using add_one_le_exp (t * |X x| - 1)
      _ = exp |t * X x| * exp (-1) := by rw [abs_mul, abs_of_pos ht, ← exp_add]; congr 1
      _ ≤ (exp (t * X x) + exp ((-t) * X x)) * exp (-1) := by
        simpa only [neg_mul] using mul_le_mul_of_nonneg_right (exp_abs_le (t * X x))
          (exp_pos (-1)).le
  have hbound : t * ∫ x, |X x| ∂μ ≤ 2 := by
    calc t * ∫ x, |X x| ∂μ
        ≤ (mgf X μ t + mgf X μ (-t)) * exp (-1) := by
          simpa only [Pi.add_apply, integral_const_mul, integral_mul_const,
            integral_add (h.integrable_exp_mul t) (h.integrable_exp_mul (-t)), mgf] using
            integral_mono (h.integrable.abs.const_mul t)
              (((h.integrable_exp_mul t).add (h.integrable_exp_mul (-t))).mul_const
                (exp (-1))) hpoint
      _ ≤ (exp (c * t ^ 2 / 2) + exp (c * (-t) ^ 2 / 2)) * exp (-1) :=
        mul_le_mul_of_nonneg_right (add_le_add (h.mgf_le t) (h.mgf_le (-t)))
          (exp_pos (-1)).le
      _ = 2 := by rw [neg_sq, ht2, ← two_mul, mul_assoc, ← exp_add]; norm_num
  exact (mul_le_mul_iff_right₀ ht).1 (hbound.trans_eq hts.symm)

end ProbabilityTheory.HasSubgaussianMGF
