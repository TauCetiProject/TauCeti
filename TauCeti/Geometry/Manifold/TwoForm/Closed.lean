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

This module characterizes closed smooth two-forms by vanishing of their chartwise exterior
derivatives and proves that constant two-forms on a model space are closed. The generic
closedness predicate and chartwise API are defined in `DifferentialForm.Closed`.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth two-form is closed exactly when each chart expression has vanishing exterior
derivative within the model range on the chart target. -/
theorem legacySmoothTwoFormEquiv_isClosed_iff
    (φ : TauCeti.SmoothTwoForm I M) :
    (legacySmoothTwoFormEquiv φ).IsClosed ↔
      ∀ x₀ z, z ∈ (extChartAt I x₀).target →
        extDerivWithin ((φ : RoughForm I M ℝ 2).inChartAt x₀) (Set.range I) z = 0 := by
  -- The chartwise criterion requires the C² structure supplied by the section's C∞ instance.
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by norm_num)
  rw [legacySmoothTwoFormEquiv_apply_eq]
  exact SmoothForm.isClosed_iff_forall_extDerivWithin_inChartAt_eq_zero φ

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
