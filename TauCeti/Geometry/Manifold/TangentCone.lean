/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Analysis.Calculus.TransverseIntersection
public import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import Mathlib.Analysis.Calculus.TangentCone.ProperSpace
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Tangent cones of subsets of a manifold, and transverse intersections

The tangent cone `TauCeti.mtangentConeAt I s y` of a subset `s` of a manifold `M` at a point `y` is
Mathlib's `tangentConeAt` of the image of `s` in the preferred extended chart at `y`, taken at the
image of `y`. It lives in the model vector space, which is `TangentSpace I y`. The image of `s` is
intersected with the range of the model, as in `UniqueMDiffWithinAt`. For a normed space modelled
on itself it is the tangent cone of `s` (`TauCeti.mtangentConeAt_eq_tangentConeAt`); for a manifold
with charts in its model space it is read in the preferred chart itself
(`TauCeti.mtangentConeAt_eq_tangentConeAt_chartAt`); read in any other chart around `y`, it is
carried onto the tangent cone in that chart by the derivative of the transition map
(`TauCeti.image_mtangentConeAt_eq_tangentConeAt`). The velocity of an integral curve that stays
in `s` lies in it (`IsMIntegralCurveAt.mem_mtangentConeAt`).

For a manifold modelled on a vector space `E` with charts in `E`, a chart of the maximal atlas that
flattens `s` onto a closed linear subspace `L` near `y` makes the span of the tangent cone the
tangent space of `s` at `y`: it has the dimension of `L`
(`TauCeti.IsSliceChart.finrank_span_mtangentConeAt`). Two such sets `s₁` and `s₂` meet
**transversally** at a common point `y` when their tangent spaces at `y` span `E`. If `E` is a real
or complex Banach space, the model subspaces are complemented, and the intersection of the tangent
spaces is complemented, then near `y` a chart of the maximal atlas flattens `s₁ ∩ s₂` onto that
intersection. The tangent cone of `s₁ ∩ s₂` itself equals that linear subspace. The same holds for
the cut of a flattened set `s` by a level `g⁻¹ {c}` of a `C^n` map `g` whose differential at `y` is
surjective, when the tangent space of `s` and the kernel of that differential span `E`: the cut is
flattened onto the intersection of the tangent space of `s` with the kernel. All complement
hypotheses are automatic in finite dimensions.

These are the manifold forms of the transverse-intersection results in
`TauCeti.Analysis.Calculus.TransverseIntersection`, obtained by reading everything in the preferred
chart at `y`.

## Main declarations

* `TauCeti.mtangentConeAt`: the tangent cone of a subset of a manifold, read in the preferred
  chart.
* `IsMIntegralCurveAt.mem_mtangentConeAt`: the velocity of an integral curve lies in the tangent
  cone of every set the curve stays in.
* `TauCeti.mtangentConeAt_nonempty_of_accPt`: over a proper model space, the tangent cone at an
  accumulation point of a set contains a nonzero vector.
* `TauCeti.mfderiv_apply_eq_zero_of_mem_mtangentConeAt`: the differential of a function vanishes on
  the tangent cone of a set on which the function is constant.
* `TauCeti.image_mtangentConeAt_eq_tangentConeAt`: read in another chart, the tangent cone is
  carried onto the tangent cone in that chart by the derivative of the transition map.
* `TauCeti.IsSliceChart.finrank_span_mtangentConeAt`: the tangent space of a flattened set has the
  dimension of the model subspace.
* `TauCeti.exists_isSliceChart_inter_of_span_mtangentConeAt_sup_eq_top`: a transverse intersection
  of flattened sets is flattened onto the intersection of their tangent spaces.
* `TauCeti.mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top` and its span form
  `TauCeti.span_mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top`: the tangent cone of a
  transverse intersection is the intersection of the tangent spaces.
* `TauCeti.exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top`,
  `TauCeti.mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top` and
  `TauCeti.span_mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top`: the same
  statements for the cut of a flattened set by a transverse regular level set.

## References

* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §5.
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Defs

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners 𝕜 E H)

/-- The **tangent cone** of a subset `s` of a manifold at a point `y`, read in the preferred
extended chart at `y`: the tangent cone, at the image of `y`, of the image of `s` in that chart,
intersected with the range of the model. It is a subset of the model space `E`, which is the
tangent space `TangentSpace I y`. -/
def mtangentConeAt (s : Set M) (y : M) : Set E :=
  tangentConeAt 𝕜 ((extChartAt I y).symm ⁻¹' s ∩ range I) (extChartAt I y y)

/-- The defining formula of `TauCeti.mtangentConeAt`. -/
theorem mtangentConeAt_def (s : Set M) (y : M) :
    mtangentConeAt I s y =
      tangentConeAt 𝕜 ((extChartAt I y).symm ⁻¹' s ∩ range I) (extChartAt I y y) :=
  (rfl)

variable {I}

/-- The tangent cone is monotone in the set. -/
theorem mtangentConeAt_mono {s t : Set M} (hst : s ⊆ t) (y : M) :
    mtangentConeAt I s y ⊆ mtangentConeAt I t y :=
  tangentConeAt_mono (inter_subset_inter_left _ (preimage_mono hst))

/-- For a normed space modelled on itself, the tangent cone of a subset is its tangent cone in the
usual sense. -/
@[simp]
theorem mtangentConeAt_eq_tangentConeAt (s : Set E) (y : E) :
    mtangentConeAt 𝓘(𝕜, E) s y = tangentConeAt 𝕜 s y := by
  simp [mtangentConeAt_def]

/-- **The tangent cone at a non-isolated point is nontrivial.** If the model space is proper and
`y` is an accumulation point of `s`, then the tangent cone of `s` at `y` contains a nonzero
vector. -/
theorem mtangentConeAt_nonempty_of_accPt [ProperSpace E] {s : Set M} {y : M}
    (hy : AccPt y (𝓟 s)) : (mtangentConeAt I s y ∩ {0}ᶜ).Nonempty := by
  refine tangentConeAt_nonempty_of_properSpace (accPt_iff_nhds.2 fun U hU ↦ ?_)
  obtain ⟨z, ⟨⟨hzs, hzU⟩, hz⟩, hzy⟩ := accPt_iff_nhds.1 hy _
    (inter_mem (extChartAt_source_mem_nhds (I := I) y) (continuousAt_extChartAt y hU))
  refine ⟨extChartAt I y z, ⟨hzU, ?_, ?_⟩, fun h ↦ hzy ((extChartAt I y).injOn hzs
    (mem_extChartAt_source y) h)⟩
  · rw [mem_preimage, (extChartAt I y).left_inv hzs]
    exact hz
  · rw [extChartAt_coe]
    exact mem_range_self _

/-- **The differential kills the tangent cone of a level set.** If `f` is differentiable at `y`
and constant on `s`, with value `f y`, then `df_y` vanishes on the tangent cone of `s` at `y`. -/
theorem mfderiv_apply_eq_zero_of_mem_mtangentConeAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : M → F} {s : Set M} {y : M} (hf : MDifferentiableAt I 𝓘(𝕜, F) f y)
    (hs : s ⊆ f ⁻¹' {f y}) {v : E} (hv : v ∈ mtangentConeAt I s y) :
    mfderiv I 𝓘(𝕜, F) f y v = 0 := by
  have hmaps := (((mdifferentiableAt_iff _ _).1 hf).2.hasFDerivWithinAt.mono
    inter_subset_right).mapsTo_tangent_cone hv
  -- The coordinate expression of `f` is constant on the image of `s` in the chart.
  have himage : writtenInExtChartAt I 𝓘(𝕜, F) y f ''
      ((extChartAt I y).symm ⁻¹' s ∩ range I) ⊆ {f y} := by
    rintro _ ⟨w, hw, rfl⟩
    simpa [writtenInExtChartAt, extChartAt_model_space_eq_id] using hs hw.1
  have hzero : fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, F) y f) (range I)
      (extChartAt I y y) v = 0 := by
    refine tangentConeAt_subset_zero (fun hacc ↦ ?_) hmaps
    obtain ⟨z, ⟨-, hz⟩, hzy⟩ := accPt_iff_nhds.1 hacc univ univ_mem
    exact hzy ((himage hz).trans (by simp [writtenInExtChartAt]))
  -- `mfderiv` is this derivative read through `tangentSpaceCastModel`, the identity of the models.
  rw [hf.mfderiv]
  exact (congrArg (tangentSpaceCastModel 𝓘(𝕜, F) (f y)).symm hzero).trans (map_zero _)

end Defs

end TauCeti

/-- **The velocity of an integral curve is tangent to the sets it stays in.** If `γ` is an integral
curve of `v` near `t₀` and `γ t ∈ s` for all `t` near `t₀`, then `v (γ t₀)` lies in the tangent cone
of `s` at `γ t₀`. -/
theorem IsMIntegralCurveAt.mem_mtangentConeAt {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {t₀ : ℝ}
    {s : Set M}
    (hγ : IsMIntegralCurveAt γ v t₀) (hs : ∀ᶠ t in 𝓝 t₀, γ t ∈ s) :
    v (γ t₀) ∈ TauCeti.mtangentConeAt I s (γ t₀) := by
  have hd := hγ.eventually_hasDerivAt.self_of_nhds.congr_deriv
    (tangentCoordChange_self (I := I) (mem_extChartAt_source (γ t₀)))
  have hsrc : ∀ᶠ t in 𝓝 t₀, γ t ∈ (extChartAt I (γ t₀)).source :=
    hγ.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds _)
  have := hd.mem_tangentConeAt (S := (extChartAt I (γ t₀)).symm ⁻¹' s ∩ range I) <|
    (hs.and hsrc).mono fun t ht ↦
      ⟨by rw [mem_preimage, Function.comp_apply, (extChartAt I (γ t₀)).left_inv ht.2]; exact ht.1,
        by simp⟩
  rw [TauCeti.mtangentConeAt_def]
  exact this

namespace TauCeti

section ModelSpace

variable {𝕜 E M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace M] [ChartedSpace E M] {s : Set M} {y : M}

/-- For a manifold modelled on a vector space `E` with charts in `E`, the tangent cone of `s` at `y`
is the tangent cone of the image of `s` under the preferred chart at `y`. -/
theorem mtangentConeAt_eq_tangentConeAt_chartAt (s : Set M) (y : M) :
    mtangentConeAt 𝓘(𝕜, E) s y = tangentConeAt 𝕜 ((chartAt E y).symm ⁻¹' s) (chartAt E y y) := by
  have hs : (extChartAt 𝓘(𝕜, E) y).symm ⁻¹' s ∩ range 𝓘(𝕜, E) = (chartAt E y).symm ⁻¹' s := by
    ext z
    simp
  rw [mtangentConeAt_def, hs]
  simp

/-- The preferred chart at `y` sends a point `y` of `s` into the chart image of `s`. -/
private theorem chartAt_self_mem_preimage (hys : y ∈ s) :
    chartAt E y y ∈ (chartAt E y).symm ⁻¹' s := by
  rwa [mem_preimage, (chartAt E y).left_inv (mem_chart_source E y)]

end ModelSpace

section SliceChart

variable {𝕜 E M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M]
  {q : OpenPartialHomeomorph M E} {L : Submodule 𝕜 E} {s : Set M} {y : M}

/-- **Chart invariance of the tangent cone.** Let `q` be a chart around `y` and `A` the derivative
at the image of `y` of the transition map from the preferred chart at `y` to `q`. Then `A` maps the
tangent cone of `s` at `y` onto the tangent cone of `s` read in `q`. When `q` is in the maximal
atlas, such an `A` exists by `TauCeti.contDiffAt_symm_trans_of_mem_maximalAtlas` and
`OpenPartialHomeomorph.exists_hasFDerivAt_of_chart`. -/
theorem image_mtangentConeAt_eq_tangentConeAt (hy : y ∈ q.source) {A : E ≃L[𝕜] E}
    (hA : HasFDerivAt ((chartAt E y).symm.trans q) (A : E →L[𝕜] E) (chartAt E y y)) :
    A '' mtangentConeAt 𝓘(𝕜, E) s y = tangentConeAt 𝕜 (q.symm ⁻¹' s) (q y) := by
  set e := (chartAt E y).symm.trans q
  have hy' : chartAt E y y ∈ e.source := by simp [e, hy, mem_chart_source]
  have hey : e (chartAt E y y) = q y := by simp [e, mem_chart_source]
  have ht : e.target ∈ 𝓝 (q y) := hey ▸ e.open_target.mem_nhds (e.map_source hy')
  have hs : e.symm ⁻¹' ((chartAt E y).symm ⁻¹' s) ∩ e.target = q.symm ⁻¹' s ∩ e.target := by
    ext w
    simp only [mem_inter_iff, mem_preimage, e, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target, Function.comp_apply]
    constructor
    · rintro ⟨hw, hwt, hwc⟩
      exact ⟨by rwa [(chartAt E y).left_inv hwc] at hw, hwt, hwc⟩
    · rintro ⟨hw, hwt, hwc⟩
      exact ⟨by rwa [(chartAt E y).left_inv hwc], hwt, hwc⟩
  rw [mtangentConeAt_eq_tangentConeAt_chartAt,
    image_tangentConeAt_eq_tangentConeAt_preimage_symm hy' hA, hey, ← tangentConeAt_inter_nhds ht,
    hs, tangentConeAt_inter_nhds ht]

/-- A chart `q` of the maximal atlas that flattens `s` onto `L`, read in the preferred chart at a
point `y` of its source: the transition map from the preferred chart to `q` is a `C^n` chart of the
model space, with `C^n` inverse, that flattens the image of `s` onto `L` near the image of `y`. -/
private theorem isSliceChart_chartAt_symm_trans (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (hs : IsSliceChart q (L : Set E) s) (hy : y ∈ q.source) :
    chartAt E y y ∈ ((chartAt E y).symm.trans q).source ∧
      (∀ z ∈ ((chartAt E y).symm.trans q).source,
        ContDiffAt 𝕜 n ((chartAt E y).symm.trans q) z) ∧
      (∀ z ∈ ((chartAt E y).symm.trans q).target,
        ContDiffAt 𝕜 n ((chartAt E y).symm.trans q).symm z) ∧
      IsSliceChart ((chartAt E y).symm.trans q) (L : Set E) ((chartAt E y).symm ⁻¹' s) := by
  have hchart := IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := n) y
  refine ⟨?_, fun z hz ↦ contDiffAt_symm_trans_of_mem_maximalAtlas hchart hq hz, fun z hz ↦ ?_,
    isSliceChart_iff.2 fun z hz ↦ ?_⟩
  · simp [hy, mem_chart_source]
  · rw [← OpenPartialHomeomorph.symm_source] at hz
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] at hz ⊢
    exact contDiffAt_symm_trans_of_mem_maximalAtlas hq hchart hz
  · rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage] at hz
    rw [mem_preimage, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    exact isSliceChart_iff.1 hs _ hz.2

/-- **The tangent space of a flattened set.** If a chart `q` of the maximal atlas flattens `s`
onto a closed subspace `L` near a point `y` of `s`, then the span of the tangent cone of `s` at `y`
has the dimension of `L`. -/
theorem IsSliceChart.finrank_span_mtangentConeAt (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : IsSliceChart q (L : Set E) s)
    (hL : IsClosed (L : Set E)) (hy : y ∈ q.source) (hys : y ∈ s) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y)) = Module.finrank 𝕜 L := by
  obtain ⟨hy', hc, hcs, he⟩ := isSliceChart_chartAt_symm_trans hq hs hy
  obtain ⟨A, hA⟩ := OpenPartialHomeomorph.exists_hasFDerivAt_of_chart _ hy'
    ((hc _ hy').differentiableAt hn)
    ((hcs _ (OpenPartialHomeomorph.map_source _ hy')).differentiableAt hn)
  rw [mtangentConeAt_eq_tangentConeAt_chartAt]
  exact he.finrank_span_tangentConeAt hL hy' (chartAt_self_mem_preimage hys) hA

end SliceChart

section Transverse

variable {𝕜 E M : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞ω}
  [IsManifold 𝓘(𝕜, E) n M] {q₁ q₂ : OpenPartialHomeomorph M E} {L₁ L₂ : Submodule 𝕜 E}
  {s₁ s₂ : Set M} {y : M}

/-- **A transverse intersection of embedded submanifolds is an embedded submanifold.** Let charts
`q₁` and `q₂` of the maximal atlas flatten `s₁` and `s₂` onto linear subspaces near a common point
`y`. If the tangent spaces of `s₁` and `s₂` at `y` span the model space, then a chart of the maximal
atlas flattens `s₁ ∩ s₂` near `y` onto the intersection of those tangent spaces. The model
subspaces and the intersection of the tangent spaces must be complemented. -/
theorem exists_isSliceChart_inter_of_span_mtangentConeAt_sup_eq_top (hn : n ≠ 0)
    (hq₁ : q₁ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (hq₂ : q₂ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (h₁ : IsSliceChart q₁ (L₁ : Set E) s₁) (h₂ : IsSliceChart q₂ (L₂ : Set E) s₂)
    (hy₁ : y ∈ q₁.source) (hy₂ : y ∈ q₂.source) (hys₁ : y ∈ s₁) (hys₂ : y ∈ s₂)
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊔
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y) = ⊤)
    (hL₁ : L₁.ClosedComplemented) (hL₂ : L₂.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊓
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y)).ClosedComplemented) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧ q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M ∧
      IsSliceChart q ((Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊓
        Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y) : Submodule 𝕜 E) : Set E) (s₁ ∩ s₂) := by
  obtain ⟨hy₁', hc₁, hcs₁, he₁⟩ := isSliceChart_chartAt_symm_trans hq₁ h₁ hy₁
  obtain ⟨hy₂', hc₂, hcs₂, he₂⟩ := isSliceChart_chartAt_symm_trans hq₂ h₂ hy₂
  rw [mtangentConeAt_eq_tangentConeAt_chartAt, mtangentConeAt_eq_tangentConeAt_chartAt] at htr hI ⊢
  obtain ⟨e, hye, hC, hCs, he⟩ := exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top hn
    he₁ he₂ hy₁' hy₂' (chartAt_self_mem_preimage hys₁) (chartAt_self_mem_preimage hys₂) hc₁ hc₂
    ((hcs₁ _ (OpenPartialHomeomorph.map_source _ hy₁')).differentiableAt hn)
    ((hcs₂ _ (OpenPartialHomeomorph.map_source _ hy₂')).differentiableAt hn) htr
    hL₁ hL₂ hI
  -- The chart is the preferred chart at `y` followed by the flattening chart `e` of the model.
  refine ⟨(chartAt E y).trans e, ⟨mem_chart_source E y, hye⟩,
    trans_mem_maximalAtlas_of_contDiffAt (IsManifold.chart_mem_maximalAtlas y) hC hCs,
    isSliceChart_iff.2 fun z hz ↦ ?_⟩
  rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage] at hz
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, ← isSliceChart_iff.1 he _ hz.2]
  simp [(chartAt E y).left_inv hz.1]

/-- The tangent cone of a transverse intersection of split submanifolds in a Banach model is
exactly the intersection of their tangent spaces, provided that this intersection is
complemented. -/
theorem mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top (hn : n ≠ 0)
    (hq₁ : q₁ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (hq₂ : q₂ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (h₁ : IsSliceChart q₁ (L₁ : Set E) s₁) (h₂ : IsSliceChart q₂ (L₂ : Set E) s₂)
    (hy₁ : y ∈ q₁.source) (hy₂ : y ∈ q₂.source) (hys₁ : y ∈ s₁) (hys₂ : y ∈ s₂)
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊔
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y) = ⊤)
    (hL₁ : L₁.ClosedComplemented) (hL₂ : L₂.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊓
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y)).ClosedComplemented) :
    mtangentConeAt 𝓘(𝕜, E) (s₁ ∩ s₂) y =
      ((Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊓
        Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y) : Submodule 𝕜 E) : Set E) := by
  obtain ⟨hy₁', hc₁, hcs₁, he₁⟩ := isSliceChart_chartAt_symm_trans hq₁ h₁ hy₁
  obtain ⟨hy₂', hc₂, hcs₂, he₂⟩ := isSliceChart_chartAt_symm_trans hq₂ h₂ hy₂
  simp only [mtangentConeAt_eq_tangentConeAt_chartAt, preimage_inter] at htr hI ⊢
  exact tangentConeAt_inter_of_span_tangentConeAt_sup_eq_top hn he₁ he₂ hy₁' hy₂'
    (chartAt_self_mem_preimage hys₁) (chartAt_self_mem_preimage hys₂) hc₁ hc₂
    ((hcs₁ _ (OpenPartialHomeomorph.map_source _ hy₁')).differentiableAt hn)
    ((hcs₂ _ (OpenPartialHomeomorph.map_source _ hy₂')).differentiableAt hn) htr
    hL₁ hL₂ hI

/-- Under the hypotheses of
`TauCeti.exists_isSliceChart_inter_of_span_mtangentConeAt_sup_eq_top`, the tangent space of
`s₁ ∩ s₂`, expressed as the span of its tangent cone, is the intersection of their tangent
spaces. -/
theorem span_mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top (hn : n ≠ 0)
    (hq₁ : q₁ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (hq₂ : q₂ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (h₁ : IsSliceChart q₁ (L₁ : Set E) s₁) (h₂ : IsSliceChart q₂ (L₂ : Set E) s₂)
    (hy₁ : y ∈ q₁.source) (hy₂ : y ∈ q₂.source) (hys₁ : y ∈ s₁) (hys₂ : y ∈ s₂)
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊔
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y) = ⊤)
    (hL₁ : L₁.ClosedComplemented) (hL₂ : L₂.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊓
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y)).ClosedComplemented) :
    Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) (s₁ ∩ s₂) y) =
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₁ y) ⊓
        Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s₂ y) := by
  rw [mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top hn hq₁ hq₂ h₁ h₂ hy₁ hy₂ hys₁ hys₂
    htr hL₁ hL₂ hI, Submodule.span_eq]

end Transverse

section Level

variable {𝕜 E F M : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace M]
  [ChartedSpace E M] {n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M] {q : OpenPartialHomeomorph M E}
  {L : Submodule 𝕜 E} {s : Set M} {y : M} {g : M → F} {c : F} {U : Set M}

/-- A `C^n` map `g` with `g y = c`, read in the preferred chart at `y`: the coordinate expression
of `g - c` is `C^n` on an open neighbourhood of the image of `y`, vanishes there, has strict
derivative the differential of `g` at `y`, and its zero set is the chart image of the level
`g⁻¹ {c}`. -/
private theorem level_chartAt_symm (hn : n ≠ 0) (hU : IsOpen U) (hyU : y ∈ U)
    (hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n g U) (hgy : g y = c) :
    HasStrictFDerivAt (fun z ↦ g ((chartAt E y).symm z) - c) (mvfderiv 𝓘(𝕜, E) g y)
        (chartAt E y y) ∧
      g ((chartAt E y).symm (chartAt E y y)) - c = 0 ∧
      IsOpen ((chartAt E y).target ∩ (chartAt E y).symm ⁻¹' U) ∧
      chartAt E y y ∈ (chartAt E y).target ∩ (chartAt E y).symm ⁻¹' U ∧
      (∀ z ∈ (chartAt E y).target ∩ (chartAt E y).symm ⁻¹' U,
        ContDiffAt 𝕜 n (fun z ↦ g ((chartAt E y).symm z) - c) z) ∧
      (chartAt E y).symm ⁻¹' (s ∩ g ⁻¹' {c}) =
        (chartAt E y).symm ⁻¹' s ∩ (fun z ↦ g ((chartAt E y).symm z) - c) ⁻¹' {0} := by
  set e := chartAt E y
  have hyy : e.symm (e y) = y := e.left_inv (mem_chart_source E y)
  have hU' : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hyU' : e y ∈ e.target ∩ e.symm ⁻¹' U := ⟨mem_chart_target E y, by rwa [mem_preimage, hyy]⟩
  have hgc : ContDiffOn 𝕜 n (g ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) :=
    (hg.comp (contMDiffOn_chart_symm.mono inter_subset_left) fun z hz ↦ hz.2).contDiffOn
  have hC : ∀ z ∈ e.target ∩ e.symm ⁻¹' U, ContDiffAt 𝕜 n (fun z ↦ g (e.symm z) - c) z :=
    fun z hz ↦ ((hgc.contDiffAt (hU'.mem_nhds hz)).sub contDiffAt_const)
  have hd : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) g y :=
    (hg.contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt hn
  have hstrict := (hC _ hyU').hasStrictFDerivAt hn
  rw [fderiv_sub_const] at hstrict
  refine ⟨?_, by simp [hyy, hgy], hU', hyU', hC, ?_⟩
  · rw [← MDifferentiableAt.fderiv_comp_chartAt_symm hd]
    exact hstrict
  · ext z
    simp [sub_eq_zero]

variable [CompleteSpace E] [CompleteSpace F]

/-- **Cutting by a transverse regular level set.** Let a chart `q` of the maximal atlas flatten
`s` onto a linear subspace near a point `y` of `s`, and let `g : M → F` be `C^n` (`n ≠ 0`) near
`y`, with `g y = c` and surjective differential at `y`. If the tangent space of `s` at `y` and the
kernel of the differential of `g` at `y` span the model space, then a chart of the maximal atlas
flattens `s ∩ g⁻¹ {c}` near `y` onto the intersection of the tangent space of `s` with that
kernel. The model subspace, the kernel and that intersection must be complemented. -/
theorem exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : IsSliceChart q (L : Set E) s)
    (hy : y ∈ q.source) (hys : y ∈ s) (hU : IsOpen U) (hyU : y ∈ U)
    (hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n g U) (hgy : g y = c)
    (hg' : (mvfderiv 𝓘(𝕜, E) g y).range = ⊤)
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊔ (mvfderiv 𝓘(𝕜, E) g y).ker = ⊤)
    (hL : L.ClosedComplemented) (hker : (mvfderiv 𝓘(𝕜, E) g y).ker.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓
      (mvfderiv 𝓘(𝕜, E) g y).ker).ClosedComplemented) :
    ∃ q' : OpenPartialHomeomorph M E, y ∈ q'.source ∧
      q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M ∧
      IsSliceChart q' ((Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓
        (mvfderiv 𝓘(𝕜, E) g y).ker : Submodule 𝕜 E) : Set E) (s ∩ g ⁻¹' {c}) := by
  obtain ⟨hy', hc, hcs, he⟩ := isSliceChart_chartAt_symm_trans hq hs hy
  obtain ⟨hG, hGy, hU', hyU', hC, hpre⟩ := level_chartAt_symm (s := s) hn hU hyU hg hgy
  rw [mtangentConeAt_eq_tangentConeAt_chartAt] at htr hI ⊢
  obtain ⟨e, hye, hC, hCs, he⟩ := exists_isSliceChart_inter_preimage_zero hn he hy'
    (chartAt_self_mem_preimage hys) hc
    ((hcs _ (OpenPartialHomeomorph.map_source _ hy')).differentiableAt hn) hG hg' hGy hU' hyU' hC
    htr hL hker hI
  -- The chart is the preferred chart at `y` followed by the flattening chart `e` of the model.
  refine ⟨(chartAt E y).trans e, ⟨mem_chart_source E y, hye⟩,
    trans_mem_maximalAtlas_of_contDiffAt (IsManifold.chart_mem_maximalAtlas y) hC hCs,
    isSliceChart_iff.2 fun z hz ↦ ?_⟩
  rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage] at hz
  have hz' : z ∈ s ∩ g ⁻¹' {c} ↔ chartAt E y z ∈ (chartAt E y).symm ⁻¹' (s ∩ g ⁻¹' {c}) := by
    simp [(chartAt E y).left_inv hz.1]
  rw [hpre] at hz'
  exact hz'.trans (isSliceChart_iff.1 he _ hz.2)

/-- **The tangent cone of a cut by a transverse regular level set.** Under the hypotheses of
`TauCeti.exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top`, the tangent
cone of `s ∩ g⁻¹ {c}` at `y` is the intersection of the tangent space of `s` at `y` with the
kernel of the differential of `g` at `y`. -/
theorem mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : IsSliceChart q (L : Set E) s)
    (hy : y ∈ q.source) (hys : y ∈ s) (hU : IsOpen U) (hyU : y ∈ U)
    (hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n g U) (hgy : g y = c)
    (hg' : (mvfderiv 𝓘(𝕜, E) g y).range = ⊤)
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊔ (mvfderiv 𝓘(𝕜, E) g y).ker = ⊤)
    (hL : L.ClosedComplemented) (hker : (mvfderiv 𝓘(𝕜, E) g y).ker.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓
      (mvfderiv 𝓘(𝕜, E) g y).ker).ClosedComplemented) :
    mtangentConeAt 𝓘(𝕜, E) (s ∩ g ⁻¹' {c}) y =
      ((Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓ (mvfderiv 𝓘(𝕜, E) g y).ker :
        Submodule 𝕜 E) : Set E) := by
  obtain ⟨hy', hc, hcs, he⟩ := isSliceChart_chartAt_symm_trans hq hs hy
  obtain ⟨hG, hGy, hU', hyU', hC, hpre⟩ := level_chartAt_symm (s := s) hn hU hyU hg hgy
  rw [mtangentConeAt_eq_tangentConeAt_chartAt] at htr hI
  rw [mtangentConeAt_eq_tangentConeAt_chartAt, mtangentConeAt_eq_tangentConeAt_chartAt, hpre]
  exact tangentConeAt_inter_preimage_zero hn he hy' (chartAt_self_mem_preimage hys) hc
    ((hcs _ (OpenPartialHomeomorph.map_source _ hy')).differentiableAt hn) hG hg' hGy hU' hyU' hC
    htr hL hker hI

/-- **The tangent space of a cut by a transverse regular level set.** Under the hypotheses of
`TauCeti.exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top`, the tangent
space of `s ∩ g⁻¹ {c}` at `y`, expressed as the span of its tangent cone, is the intersection of
the tangent space of `s` at `y` with the kernel of the differential of `g` at `y`. -/
theorem span_mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : IsSliceChart q (L : Set E) s)
    (hy : y ∈ q.source) (hys : y ∈ s) (hU : IsOpen U) (hyU : y ∈ U)
    (hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, F) n g U) (hgy : g y = c)
    (hg' : (mvfderiv 𝓘(𝕜, E) g y).range = ⊤)
    (htr : Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊔ (mvfderiv 𝓘(𝕜, E) g y).ker = ⊤)
    (hL : L.ClosedComplemented) (hker : (mvfderiv 𝓘(𝕜, E) g y).ker.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓
      (mvfderiv 𝓘(𝕜, E) g y).ker).ClosedComplemented) :
    Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) (s ∩ g ⁻¹' {c}) y) =
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) s y) ⊓ (mvfderiv 𝓘(𝕜, E) g y).ker := by
  rw [mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top hn hq hs hy hys hU hyU hg
    hgy hg' htr hL hker hI, Submodule.span_eq]

end Level

end TauCeti
