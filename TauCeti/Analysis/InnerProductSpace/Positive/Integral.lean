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

The Bochner integral of a family of positive operators on a real inner product space is a
positive operator (`ContinuousLinearMap.isPositive_integral`). No integrability or completeness
assumption is needed, since otherwise the integral is `0`. Covariance operators of probability
laws, written as integrals of rank-one operators `(x - m) ⊗ (x - m)`, are positive for this
reason.
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace ContinuousLinearMap

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- The Bochner integral of a family of positive operators on a real inner product space is
positive. -/
theorem isPositive_integral {F : X → E →L[ℝ] E} (hF : ∀ x, (F x).IsPositive) :
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
  -- The quadratic and bilinear forms of the integral are integrals of those of `F x`.
  have key (v w : E) : ⟪v, (∫ x, F x ∂μ) w⟫ = ∫ x, ⟪v, F x w⟫ ∂μ := by
    rw [integral_apply hint w, integral_inner (hint.apply_continuousLinearMap w) v]
  refine (isPositive_iff _).2 ⟨fun v w ↦ ?_, fun v ↦ ?_⟩
  · rw [coe_coe, real_inner_comm, key, key]
    exact integral_congr_ae (ae_of_all _ fun x ↦
      ((hF x).inner_left_eq_inner_right w v).symm.trans (real_inner_comm _ _))
  · rw [real_inner_comm, key]
    exact integral_nonneg fun x ↦ (hF x).inner_nonneg_right v

end ContinuousLinearMap
