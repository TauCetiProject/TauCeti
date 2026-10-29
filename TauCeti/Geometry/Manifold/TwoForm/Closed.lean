/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed

/-!
# Closed smooth differential two-forms

This module supplies the constant-form convenience theorem for smooth two-forms. The generic
closedness predicate and its chartwise API are defined in `DifferentialForm.Closed`.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable (form : SmoothTwoForm I M)

/-- Constant forms on a model space are closed. -/
theorem isClosed_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    (const B : SmoothTwoForm (modelWithCornersSelf ℝ V) V).IsClosed := by
  rw [const_eq]
  exact SmoothForm.isClosed_const
    ((2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ V ℝ B)

end SmoothTwoForm

end TauCeti

end
