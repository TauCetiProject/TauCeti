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

The quadratic MGF bound forces a sub-Gaussian random variable to have mean zero.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace ProbabilityTheory.HasSubgaussianMGF

/-- A sub-Gaussian MGF bound forces the expectation to vanish. -/
theorem integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) : μ[X] = 0 := by
  have hset : integrableExpSet X μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true, integrableExpSet]
    exact hX.integrable_exp_mul t
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

end ProbabilityTheory.HasSubgaussianMGF
