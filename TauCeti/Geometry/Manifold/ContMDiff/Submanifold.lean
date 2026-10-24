/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Transport
public import TauCeti.Geometry.Manifold.ContMDiff.Analytic

/-!
# Native analytic submanifolds in manifold charts

The finite-coordinate carrier `TauCeti.IsAnalyticSubmanifold` can be tested in the charts of an
analytic manifold without introducing another submanifold structure. A continuous linear
identification of the model with `Fin n → 𝕜` supplies its ambient coordinates. The chart-image
criterion is independent of that identification and of the analytic charts used to test it.
In particular, it suffices to find one suitable chart near each point of the subset; every
nonempty intersection with any chart of the maximal analytic atlas then has a native analytic
submanifold image of the same dimension. Empty chart intersections require no nonempty carrier.

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
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n d : ℕ} {S : Set M}

/-- Analytic changes of manifold charts remain analytic after a continuous linear
identification of the model with finite coordinates. -/
theorem _root_.ContinuousLinearEquiv.analyticOnNhd_coordChange
    (L : E ≃L[𝕜] (Fin n → 𝕜)) {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    AnalyticOnNhd 𝕜
      ((e.trans L.toHomeomorph.toOpenPartialHomeomorph).symm.trans
        (e'.trans L.toHomeomorph.toOpenPartialHomeomorph))
      ((e.trans L.toHomeomorph.toOpenPartialHomeomorph).symm.trans
        (e'.trans L.toHomeomorph.toOpenPartialHomeomorph)).source := by
  have hplain : AnalyticOnNhd 𝕜 (e.symm.trans e') (e.symm.trans e').source := by
    simpa [ModelWithCorners.extendCoordChange, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_target] using
      (𝓘(𝕜, E)).analyticOnNhd_extendCoordChange he he'
  intro y hy
  have hy' : L.symm y ∈ (e.symm.trans e').source := by
    simpa using hy
  simpa only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans_symm,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.coe_symm_toHomeomorph,
    Function.comp_assoc] using
    (L.analyticAt _).comp ((hplain _ hy').comp (L.symm.analyticAt y))

/-- Native analytic submanifold images in one analytic chart near each point suffice to
give native images in every chart of the maximal analytic atlas. The linear identification
of the model space is kept explicit, and empty chart intersections are excluded. -/
theorem _root_.ContinuousLinearEquiv.isAnalyticSubmanifold_chart_image_iff [IsManifold 𝓘(𝕜, E) ω M]
    (L : E ≃L[𝕜] (Fin n → 𝕜)) :
    (∀ e ∈ maximalAtlas 𝓘(𝕜, E) ω M, (e.source ∩ S).Nonempty →
      IsAnalyticSubmanifold d (L '' (e '' (e.source ∩ S)))) ↔
    ∀ x ∈ S, ∃ e ∈ maximalAtlas 𝓘(𝕜, E) ω M, x ∈ e.source ∧
      IsAnalyticSubmanifold d (L '' (e '' (e.source ∩ S))) := by
  refine ⟨fun h x hx ↦ ?_, fun h e he hne ↦ ?_⟩
  · exact ⟨chartAt E x, chart_mem_maximalAtlas x, mem_chart_source E x,
      h _ (chart_mem_maximalAtlas x) ⟨x, mem_chart_source E x, hx⟩⟩
  · let eL := e.trans L.toHomeomorph.toOpenPartialHomeomorph
    have hneL : (eL.source ∩ S).Nonempty := by simpa [eL] using hne
    have himage := eL.isAnalyticSubmanifold_image_source_inter_of_locally (d := d) hneL ?_
    · simpa [eL, image_image] using himage
    · intro x hx
      obtain ⟨c, hc, hxc, hS⟩ := h x hx.2
      refine ⟨c.trans L.toHomeomorph.toOpenPartialHomeomorph, by simpa using hxc,
        ?_, L.analyticOnNhd_coordChange he hc, ?_⟩
      · simpa [image_image] using hS
      · exact L.analyticOnNhd_coordChange hc he

/-- The native chart-image criterion can be checked using just the preferred chart at each
point of the subset. -/
theorem _root_.ContinuousLinearEquiv.isAnalyticSubmanifold_chart_image_iff_chartAt
    [IsManifold 𝓘(𝕜, E) ω M]
    (L : E ≃L[𝕜] (Fin n → 𝕜)) :
    (∀ e ∈ maximalAtlas 𝓘(𝕜, E) ω M, (e.source ∩ S).Nonempty →
      IsAnalyticSubmanifold d (L '' (e '' (e.source ∩ S)))) ↔
    ∀ x ∈ S, IsAnalyticSubmanifold d
      (L '' ((chartAt E x) '' ((chartAt E x).source ∩ S))) := by
  refine ⟨fun h x hx ↦ h _ (chart_mem_maximalAtlas x)
    ⟨x, mem_chart_source E x, hx⟩, fun h ↦ L.isAnalyticSubmanifold_chart_image_iff.2 ?_⟩
  intro x hx
  exact ⟨chartAt E x, chart_mem_maximalAtlas x, mem_chart_source E x, h x hx⟩

end TauCeti
