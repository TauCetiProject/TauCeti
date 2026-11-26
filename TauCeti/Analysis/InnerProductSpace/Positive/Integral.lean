/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrals of positive operators

The Bochner integral of a family of positive operators on an inner product space is a positive
operator (`ContinuousLinearMap.isPositive_integral`). No integrability or completeness
assumption is needed, since otherwise the integral is `0`. Covariance operators of probability
laws, written as integrals of rank-one operators `(x - m) ⊗ (x - m)`, are positive for this
reason.
-/

public section

open MeasureTheory

namespace ContinuousLinearMap

variable {X 𝕜 E : Type*} [MeasurableSpace X] {μ : Measure X} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The Bochner integral of a family of positive operators on an inner product space is
positive. -/
theorem isPositive_integral {F : X → E →L[𝕜] E} (hF : ∀ x, (F x).IsPositive) :
    (∫ x, F x ∂μ).IsPositive := by
  by_cases hint : Integrable F μ
  swap
  · rw [integral_undef hint]
    exact isPositive_zero
  by_cases hE : CompleteSpace E
  swap
  · have h0 : ∫ x, F x ∂μ = 0 := by
      ext1 v
      rw [integral_apply hint v, integral_of_not_completeSpace hE, zero_apply]
    rw [h0]
    exact isPositive_zero
  -- The sesquilinear form of the integral is the integral of those of `F x`.
  have key (v w : E) : inner 𝕜 v ((∫ x, F x ∂μ) w) = ∫ x, inner 𝕜 v (F x w) ∂μ := by
    rw [integral_apply hint w, integral_inner (hint.apply_continuousLinearMap w) v]
  refine isPositive_def.2 ⟨fun v w ↦ ?_, fun v ↦ ?_⟩
  · rw [coe_coe, key, ← inner_conj_symm, key, ← integral_conj]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by
      dsimp only
      rw [inner_conj_symm, (hF x).inner_left_eq_inner_right])
  · rw [reApplyInnerSelf_apply, inner_re_symm, key,
      ← integral_re ((hint.apply_continuousLinearMap v).const_inner v)]
    exact integral_nonneg fun x ↦ (hF x).re_inner_nonneg_right v

end ContinuousLinearMap
