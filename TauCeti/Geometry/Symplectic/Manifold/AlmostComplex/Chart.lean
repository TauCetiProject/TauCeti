/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Smooth almost complex structures read in a chart

Let `J` be a smooth almost complex structure on a manifold `M` modelled on `E`. Read in the
trivialization of the tangent bundle at `x`, along the inverse of the extended chart at `x`, the
structure becomes a map `E → (E →L[ℝ] E)`. This file records its basic properties: it squares to
`-1` on the chart target, it is `J x` at the chart point, it is differentiable there, and its
derivative at the chart point anticommutes with `J x`.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.inChart`: the almost complex structure read in a chart.
* `TauCeti.SmoothAlmostComplexStructure.inChart_inChart`: it squares to `-1` on the chart target.
* `TauCeti.SmoothAlmostComplexStructure.inChart_extChartAt_self`: it is `J x` at the chart point.
* `TauCeti.SmoothAlmostComplexStructure.fderivWithin_inChart_apply_apply`: its derivative at the
  chart point anticommutes with `J x`.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M) (x : M)

/-- The almost complex structure read in the trivialization of the tangent bundle at `x`, along
the inverse of the extended chart at `x`. -/
def inChart (z : E) : E →L[ℝ] E :=
  ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x
    ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
      (J.toEndomorphism ((extChartAt I x).symm z))

/-- The defining formula of `inChart`: `J` at `(extChartAt I x).symm z`, written in the
coordinates of the trivialization of the tangent bundle at `x`. -/
theorem inChart_def (z : E) :
    J.inChart x z = ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x
      ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
        (J.toEndomorphism ((extChartAt I x).symm z)) :=
  (rfl)

/-- At the image of a point `y` of the chart at `x`, the almost complex structure read in the chart
is `J y` in the coordinates of the trivialization of the tangent bundle at `x`. -/
theorem inChart_extChartAt_apply {y : M} (hy : y ∈ (extChartAt I x).source) (u : E) :
    J.inChart x (extChartAt I x y) u =
      (trivializationAt E (TangentSpace I) x
        ⟨y, J y ((trivializationAt E (TangentSpace I) x).symm y u)⟩).2 := by
  have hy' : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  simp only [inChart, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [(extChartAt I x).left_inv hy,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hy',
    Trivialization.symmL_apply _ hy']

/-- In the chart, the almost complex structure still squares to `-1`. -/
theorem inChart_inChart {z : E} (hz : z ∈ (extChartAt I x).target) (w : E) :
    J.inChart x z (J.inChart x z w) = -w := by
  have hJ (y : M) (v : TangentSpace I y) : J.toEndomorphism y (J.toEndomorphism y v) = -v :=
    J.apply_apply y v
  simp only [inChart, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_continuousLinearMapAt _
      (TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz), hJ, map_neg,
    Trivialization.continuousLinearMapAt_symmL _
      (TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz)]

/-- At the chart point, the almost complex structure read in the chart is `J x`. -/
theorem inChart_extChartAt_self : J.inChart x (extChartAt I x x) = J.toEndomorphism x := by
  simp only [inChart]
  rw [extChartAt_to_inv]
  ext w
  simp only [ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source H x),
    TangentBundle.symmL_trivializationAt (mem_chart_source H x), mfderiv_extChartAt_self,
    mfderivWithin_range_extChartAt_symm]
  -- Both chart derivatives are identities of tangent spaces that are definitionally `E`.
  rfl

/-- The almost complex structure read in the chart at `x` is differentiable at the chart point. -/
theorem differentiableWithinAt_inChart :
    DifferentiableWithinAt ℝ (J.inChart x) (Set.range I) (extChartAt I x x) := by
  have h := ((contMDiffAt_hom_bundle _).1 (J.toEndomorphism.contMDiff x)).2
  have h' := h.comp_contMDiffWithinAt_of_eq (contMDiffWithinAt_extChartAt_symm_range_self x)
    (extChartAt_to_inv x)
  exact (contMDiffWithinAt_iff_contDiffWithinAt.1 h').differentiableWithinAt (by simp)

/-- Differentiating `J² = -1` in the chart at `x`: the derivative of the almost complex structure
read in the chart anticommutes with its value at the chart point. -/
theorem fderivWithin_inChart_apply_apply (v w : E) :
    fderivWithin ℝ (J.inChart x) (Set.range I) (extChartAt I x x) v
        (J.inChart x (extChartAt I x x) w) =
      -J.inChart x (extChartAt I x x)
        (fderivWithin ℝ (J.inChart x) (Set.range I) (extChartAt I x x) v w) := by
  have hd := (J.differentiableWithinAt_inChart x).hasFDerivWithinAt
  have heq : (fun z ↦ J.inChart x z ∘L J.inChart x z) =ᶠ[𝓝[Set.range I] extChartAt I x x]
      fun _ ↦ -ContinuousLinearMap.id ℝ E := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    ext w
    simp [J.inChart_inChart x hz]
  have h := (I.uniqueDiffOn.uniqueDiffWithinAt (Set.mem_range_self _)).eq
    ((hd.clm_comp hd).congr_of_eventuallyEq heq.symm
      (heq.symm.eq_of_nhdsWithin (Set.mem_range_self _))) (hasFDerivWithinAt_const _ _ _)
  have hvw := congrArg (fun L ↦ L v w) h
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    zero_apply] at hvw
  exact eq_neg_of_add_eq_zero_right hvw

end SmoothAlmostComplexStructure

end TauCeti

end
