/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.Calculus.DerivativeTest

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
  have hm (t : ℝ) : t ∈ interior (integrableExpSet X μ) := by
    simp [hX.integrableExpSet_eq_univ]
  let g : ℝ → ℝ := (fun t ↦ Real.exp ((c : ℝ) * t ^ 2 / 2)) - mgf X μ
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [g, Pi.sub_apply] using sub_nonneg.mpr (hX.mgf_le t)
  have he (t : ℝ) : HasDerivAt (fun t : ℝ ↦ Real.exp ((c : ℝ) * t ^ 2 / 2))
      (Real.exp ((c : ℝ) * t ^ 2 / 2) * ((c : ℝ) * t)) t := by
    convert! (((hasDerivAt_id t).pow 2).const_mul (c : ℝ)).div_const 2 |>.exp using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have hderiv : deriv g = fun t ↦ Real.exp ((c : ℝ) * t ^ 2 / 2) * ((c : ℝ) * t) -
      deriv (mgf X μ) t := by
    funext t
    exact ((he t).sub (differentiableAt_mgf (hm t)).hasDerivAt).deriv
  have hx : HasDerivAt (deriv (mgf X μ)) (∫ ω, X ω ^ 2 ∂μ) 0 := by
    simpa only [iteratedDeriv_one, Nat.reduceAdd, zero_mul, exp_zero, mul_one] using
      hasDerivAt_iteratedDeriv_mgf (hm 0) 1
  have hsecond : HasDerivAt (deriv g) ((c : ℝ) - ∫ ω, X ω ^ 2 ∂μ) 0 := by
    rw [hderiv]
    convert! ((he 0).mul ((hasDerivAt_id (0 : ℝ)).const_mul (c : ℝ))).sub hx using 1
    simp
  have hnonneg := TauCeti.deriv_deriv_nonneg_of_isLocalMin
    ((he 0).continuousAt.sub (differentiableAt_mgf (hm 0)).continuousAt) hmin
  rw [hsecond.deriv] at hnonneg
  linarith

end ProbabilityTheory.HasSubgaussianMGF
