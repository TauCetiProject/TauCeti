/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Family
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Coordinates of smooth Riemannian metric families

Joint smoothness of a Riemannian metric family passes to its native tangent coordinates and
to the chart metric obtained by composing with the inverse base chart.

## References

* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section
noncomputable section

open Bundle Set Filter MeasureTheory
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- Cache the canonical nested operator-space instances used by the metric bundle.
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance familyMetricDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance familyMetricDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance familyMetricBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance familyMetricBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

-- The dual tangent fibers carry their canonical continuous addition without a fiber norm.
/-- The canonical continuous addition on dual tangent fibers in the metric bundle. -/
local instance familyMetricFiberContinuousAdd :
    ∀ x : M, ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) := fun _ ↦ inferInstance

variable {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {J : Set ℝ}

/-- A smooth family of native metrics has jointly smooth coefficients in the fixed tangent
trivialization over the chart source. -/
theorem IsSmoothMetricFamilyOn.contMDiffOn_inCoordinates
    (hg : IsSmoothMetricFamilyOn g J) (x₀ : M) :
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun z : ℝ × M ↦ (g z.1).toNondegenerateMetric.inCoordinates x₀ z.2)
      (J ×ˢ (chartAt H x₀).source) := by
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x₀
  have he : MapsTo (fun z : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      z.2 ((g z.1).inner z.2)) (J ×ˢ (chartAt H x₀).source) e.source := by
    intro z hz
    apply (Trivialization.mem_source e).mpr
    -- The nested hom-bundle trivialization has the intersection of its three base sets.
    change z.2 ∈ (chartAt H x₀).source ∩ ((chartAt H x₀).source ∩ univ)
    exact ⟨hz.2, hz.2, mem_univ _⟩
  have hsmooth := hg.contMDiffOn.mono
    (prod_mono (Subset.rfl : J ⊆ J) (subset_univ (chartAt H x₀).source))
  have hmetric (t : ℝ) (x : M) : (g t).toNondegenerateMetric x = (g t).inner x := by
    ext v w
    exact ContMDiffRiemannianMetric.toNondegenerateMetric_apply _ _ _ _
  simp_rw [Manifold.ContMDiffNondegenerateMetric.inCoordinates_eq_tangentBilinFormInCoordinates,
    Manifold.tangentBilinFormInCoordinates_def, hmetric]
  simpa only [hom_trivializationAt_apply, e] using
    ((Trivialization.contMDiffOn_iff (e := e) he).mp hsmooth).2

/-- A smooth metric family gives jointly smooth native chart metric coefficients. -/
theorem IsSmoothMetricFamilyOn.contDiffOn_chartMetric
    (hg : IsSmoothMetricFamilyOn g J) (x₀ : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E ↦ (g z.1).toNondegenerateMetric.chartMetric x₀ z.2)
      (J ×ˢ (extChartAt I x₀).target) := by
  have hpoint : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
      (fun z : ℝ × E ↦ (extChartAt I x₀).symm z.2)
      (J ×ˢ (extChartAt I x₀).target) :=
    (contMDiffOn_extChartAt_symm x₀).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hz ↦ hz.2)
  simpa only [Manifold.ContMDiffNondegenerateMetric.chartMetric_def, Function.comp_def] using
    ((hg.contMDiffOn_inCoordinates x₀).comp (contDiff_fst.contMDiff.contMDiffOn.prodMk hpoint)
    (fun z hz ↦ ⟨hz.1, by simpa only [extChartAt_source] using
      (extChartAt I x₀).map_target hz.2⟩)).contDiffOn

end TauCeti
