/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Transport
public import TauCeti.Geometry.Manifold.ContMDiff.Analytic
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Native analytic submanifolds in manifold charts

The finite-coordinate carrier `TauCeti.IsAnalyticSubmanifold` can be tested in the extended charts
of a boundaryless analytic manifold without introducing another submanifold structure. A continuous
linear identification of the model with `Fin n → 𝕜` supplies its ambient coordinates. The
chart-image criterion is independent of that identification and of the analytic charts used to
test it. In particular, it suffices to find one suitable chart near each point of the subset;
every nonempty intersection with any chart of the maximal analytic atlas then has a native
analytic submanifold image of the same dimension. Empty chart intersections require no nonempty
carrier.

This uses the convergent chart-change theorem from
`TauCeti.Geometry.Manifold.ContMDiff.Analytic` and the flattening-chart transport from
`TauCeti.Analysis.Analytic.Submanifold.Transport`. No new charted-space instance is installed.
-/

public section

open Set IsManifold
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n d : ℕ} {S : Set M}

/-- Analytic changes of extended manifold charts remain analytic after a continuous linear
identification of the model with a normed space. -/
theorem _root_.ContinuousLinearEquiv.analyticOnNhd_coordChange
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : E ≃L[𝕜] F) {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ maximalAtlas I ω M) (he' : e' ∈ maximalAtlas I ω M) :
    AnalyticOnNhd 𝕜
      (((e.transHomeomorph I.toHomeomorph).transHomeomorph L.toHomeomorph).symm.trans
        ((e'.transHomeomorph I.toHomeomorph).transHomeomorph L.toHomeomorph))
      (((e.transHomeomorph I.toHomeomorph).transHomeomorph L.toHomeomorph).symm.trans
        ((e'.transHomeomorph I.toHomeomorph).transHomeomorph L.toHomeomorph)).source := by
  intro y hy
  have hy' : L.symm y ∈ (I.extendCoordChange e e').source := by
    rw [I.extendCoordChange_source, I.image_eq, I.range_eq_univ, inter_univ]
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.transHomeomorph_target,
      OpenPartialHomeomorph.transHomeomorph_source,
      OpenPartialHomeomorph.transHomeomorph_symm_apply, mem_inter_iff, mem_preimage,
      Function.comp_apply, ModelWithCorners.toHomeomorph_symm_apply,
      ContinuousLinearEquiv.coe_symm_toHomeomorph] using hy
  -- In a boundaryless model, postcomposition by I.toHomeomorph has precisely the forward
  -- and inverse functions of the extended chart. The remaining composition is linear.
  simpa only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.transHomeomorph_apply,
    OpenPartialHomeomorph.transHomeomorph_symm_apply, Function.comp_def,
    ModelWithCorners.toHomeomorph_apply, ModelWithCorners.toHomeomorph_symm_apply,
    ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.coe_symm_toHomeomorph] using
    (L.analyticAt _).comp ((I.analyticOnNhd_extendCoordChange he he' _ hy').comp
      (L.symm.analyticAt y))

/-- Native analytic submanifold images in one extended analytic chart near each point suffice
to give native images in every chart of the maximal analytic atlas. The linear identification
of the model space is kept explicit, and empty chart intersections are excluded. -/
theorem _root_.ContinuousLinearEquiv.isAnalyticSubmanifold_chart_image_iff [IsManifold I ω M]
    (L : E ≃L[𝕜] (Fin n → 𝕜)) :
    (∀ e ∈ maximalAtlas I ω M, (e.source ∩ S).Nonempty →
      IsAnalyticSubmanifold d (L '' (e.extend I '' (e.source ∩ S)))) ↔
    ∀ x ∈ S, ∃ e ∈ maximalAtlas I ω M, x ∈ e.source ∧
      IsAnalyticSubmanifold d (L '' (e.extend I '' (e.source ∩ S))) := by
  refine ⟨fun h x hx ↦ ?_, fun h e he hne ↦ ?_⟩
  · exact ⟨chartAt H x, chart_mem_maximalAtlas x, mem_chart_source H x,
      h _ (chart_mem_maximalAtlas x) ⟨x, mem_chart_source H x, hx⟩⟩
  · let eL := (e.transHomeomorph I.toHomeomorph).transHomeomorph L.toHomeomorph
    have hneL : (eL.source ∩ S).Nonempty := by
      simpa only [eL, OpenPartialHomeomorph.transHomeomorph_source] using hne
    have himage := eL.isAnalyticSubmanifold_image_source_inter_of_locally (d := d) hneL ?_
    · simpa only [eL, OpenPartialHomeomorph.transHomeomorph_image_source_inter,
        ← image_comp, OpenPartialHomeomorph.extend_coe, Function.comp_def,
        ModelWithCorners.toHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph] using himage
    · intro x hx
      obtain ⟨c, hc, hxc, hS⟩ := h x hx.2
      refine ⟨(c.transHomeomorph I.toHomeomorph).transHomeomorph L.toHomeomorph,
        ?_, ?_, L.analyticOnNhd_coordChange he hc, ?_⟩
      · simpa only [OpenPartialHomeomorph.transHomeomorph_source] using hxc
      · simpa only [OpenPartialHomeomorph.transHomeomorph_image_source_inter,
          ← image_comp, OpenPartialHomeomorph.extend_coe, Function.comp_def,
          ModelWithCorners.toHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph] using hS
      · exact L.analyticOnNhd_coordChange hc he

/-- The native extended-chart-image criterion can be checked using just the preferred chart
at each point of the subset. -/
theorem _root_.ContinuousLinearEquiv.isAnalyticSubmanifold_chart_image_iff_chartAt
    [IsManifold I ω M]
    (L : E ≃L[𝕜] (Fin n → 𝕜)) :
    (∀ e ∈ maximalAtlas I ω M, (e.source ∩ S).Nonempty →
      IsAnalyticSubmanifold d (L '' (e.extend I '' (e.source ∩ S)))) ↔
    ∀ x ∈ S, IsAnalyticSubmanifold d
      (L '' ((chartAt H x).extend I '' ((chartAt H x).source ∩ S))) := by
  refine ⟨fun h x hx ↦ h _ (chart_mem_maximalAtlas x)
    ⟨x, mem_chart_source H x, hx⟩, fun h ↦ L.isAnalyticSubmanifold_chart_image_iff.2 ?_⟩
  intro x hx
  exact ⟨chartAt H x, chart_mem_maximalAtlas x, mem_chart_source H x, h x hx⟩

end TauCeti
