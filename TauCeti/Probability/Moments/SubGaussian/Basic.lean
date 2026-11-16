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
the variance proxy, and bounds its first absolute moment by `2 exp (c / 2)`.
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

/-- The first absolute moment of a sub-Gaussian random variable is at most `2 exp (c / 2)`. -/
theorem integral_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) : ∫ x, |X x| ∂μ ≤ 2 * exp (c / 2) := by
  calc ∫ x, |X x| ∂μ
      ≤ ∫ x, (exp (1 * X x) + exp ((-1) * X x)) ∂μ :=
        integral_mono h.integrable.abs
          ((h.integrable_exp_mul 1).add (h.integrable_exp_mul (-1))) fun x ↦ by
            simp only [one_mul, neg_one_mul]
            linarith [add_one_le_exp |X x|, exp_abs_le (X x)]
    _ = mgf X μ 1 + mgf X μ (-1) :=
        integral_add (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1))
    _ ≤ exp (c * 1 ^ 2 / 2) + exp (c * (-1) ^ 2 / 2) :=
        add_le_add (h.mgf_le 1) (h.mgf_le (-1))
    _ = 2 * exp (c / 2) := by norm_num; ring

end ProbabilityTheory.HasSubgaussianMGF
