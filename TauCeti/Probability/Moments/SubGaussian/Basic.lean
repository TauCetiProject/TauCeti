/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Basic properties of sub-Gaussian moment-generating functions

Under a zero or probability measure, the quadratic MGF bound forces a sub-Gaussian random
variable to have mean zero and bounds its second moment by the variance proxy. The bound is
monotone in the proxy.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Topology

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

/-- Under a zero or probability measure, the second moment of a sub-Gaussian random variable is at
most its variance proxy. -/
theorem integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ^ 2 ∂μ ≤ c := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · simp
  have hcosh (y : ℝ) : 1 + y ^ 2 / 2 ≤ (exp y + exp (-y)) / 2 := by
    have h := (Real.hasSum_cosh y).summable.sum_le_tsum (Finset.range 2)
      (fun n _ ↦ div_nonneg (by rw [pow_mul]; positivity) (by positivity))
    simpa [Finset.sum_range_succ, Real.cosh_eq, (Real.hasSum_cosh y).tsum_eq] using h
  have hmgf (s : ℝ) (hs : 0 ≤ s) : 1 + s * (∫ ω, X ω ^ 2 ∂μ) ≤ exp (c * s) := by
    let t := √(2 * s)
    have ht : t ^ 2 = 2 * s := sq_sqrt (by positivity)
    have hsq := (hX.memLp 2).integrable_sq
    have hint := integral_mono ((integrable_const (1 : ℝ)).add (hsq.const_mul (t ^ 2 / 2)))
      (((hX.integrable_exp_mul t).add (hX.integrable_exp_mul (-t))).div_const 2)
      (fun ω ↦ by
        simpa only [Pi.add_apply, mul_pow, div_mul_eq_mul_div, neg_mul]
          using hcosh (t * X ω))
    dsimp only [Pi.add_apply] at hint
    rw [integral_add (integrable_const _) (hsq.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul, integral_div,
      integral_add (hX.integrable_exp_mul t) (hX.integrable_exp_mul (-t))] at hint
    have hpos := hX.mgf_le t
    have hneg := hX.mgf_le (-t)
    dsimp only [mgf] at hpos hneg
    simp only [neg_mul, neg_sq] at hneg
    rw [ht] at hint hpos hneg
    have heq : (c : ℝ) * (2 * s) / 2 = c * s := by ring
    rw [heq] at hpos hneg
    simp only [neg_mul] at hint
    linarith
  by_contra! hlt
  let g : ℝ → ℝ := fun s ↦ exp (c * s) - (1 + s * (∫ ω, X ω ^ 2 ∂μ))
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro s
    have hle : 1 + s * (∫ ω, X ω ^ 2 ∂μ) ≤ exp (c * s) := by
      rcases le_total 0 s with hs | hs
      · exact hmgf s hs
      · have h := add_one_le_exp ((c : ℝ) * s)
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlt.le) hs]
    simpa [g] using sub_nonneg.mpr hle
  have hd : HasDerivAt g ((c : ℝ) - ∫ ω, X ω ^ 2 ∂μ) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (c : ℝ)).exp).sub
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (∫ ω, X ω ^ 2 ∂μ))) using 1 <;>
      simp [g, Pi.sub_def, Pi.add_def]
  have hz := hmin.hasDerivAt_eq_zero hd
  linarith

end ProbabilityTheory.HasSubgaussianMGF
