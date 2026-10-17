/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Const
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.TwoForm.Basic

/-!
# Closed smooth differential two-forms

This module keeps the chartwise closedness predicate used by the symplectic API while the carrier
is now the generic `SmoothForm I M ℝ 2`. The coordinate expression is obtained by pulling the
alternating value back through the tangent coordinate change; on a model space it reduces to the
usual flat exterior derivative.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable (form : SmoothTwoForm I M)

/-- The coordinate expression of a two-form in the extended chart at `x₀`. -/
def inChartAt (x₀ : M) (z : E) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  form.altAt ((extChartAt I x₀).symm z) |>.compContinuousLinearMap
    (tangentCoordChange I x₀ ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z))

@[simp] theorem inChartAt_apply (x₀ : M) (z : E) (v : Fin 2 → E) :
    form.inChartAt x₀ z v =
      form ((extChartAt I x₀).symm z)
        (tangentCoordChange I x₀ ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z) (v 0))
        (tangentCoordChange I x₀ ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z) (v 1)) := by
  rw [inChartAt, ContinuousAlternatingMap.compContinuousLinearMap_apply, altAt_apply]
  simp only [Function.comp_apply]

theorem inChartAt_extChartAt_self (x : M) :
    form.inChartAt x (extChartAt I x x) = form.altAt x := by
  ext v
  rw [inChartAt_apply, extChartAt_to_inv, altAt_apply]
  simp only [tangentCoordChange_self (mem_extChartAt_source x)]


@[simp] theorem inChartAt_modelSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (form : SmoothTwoForm (modelWithCornersSelf ℝ V) V) (x₀ : V) :
    form.inChartAt x₀ = form.altAt := by
  ext z v
  rw [inChartAt_apply, altAt_apply, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, id]
  simp only [TangentBundle.coordChange_model_space, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply]

/-- A form is closed when every preferred-chart expression has zero flat exterior derivative. -/
def IsClosed : Prop :=
  ∀ x₀, extDerivWithin (form.inChartAt x₀) (range I) (extChartAt I x₀ x₀) = 0

/-- Constant forms on a model space are closed. -/
theorem isClosed_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) :
    (const B hB : SmoothTwoForm (modelWithCornersSelf ℝ V) V).IsClosed := by
  intro x
  rw [inChartAt_modelSpace]
  have h : (const B hB : SmoothTwoForm (modelWithCornersSelf ℝ V) V).altAt =
      fun _ => (const B hB).altAt x := by
    funext y
    ext v
    rw [SmoothTwoForm.altAt_apply, SmoothTwoForm.altAt_apply]
    change SmoothForm.eval₂ (const B hB) y
        ((NormedSpace.fromTangentSpace y).symm (v 0))
        ((NormedSpace.fromTangentSpace y).symm (v 1)) =
      SmoothForm.eval₂ (const B hB) x
        ((NormedSpace.fromTangentSpace x).symm (v 0))
        ((NormedSpace.fromTangentSpace x).symm (v 1))
    rw [const_model_apply, const_model_apply]
  rw [h]
  exact ContinuousAlternatingMap.extDerivWithin_const (𝕜 := ℝ) _ _ _

end SmoothTwoForm

end TauCeti

end
