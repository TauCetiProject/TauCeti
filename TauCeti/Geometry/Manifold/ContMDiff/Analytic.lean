/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Geometry.Manifold.ContMDiff.Defs
public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Analytic maps on manifolds, read in charts

On a manifold modelled without boundary, Mathlib's `C^ω` maps (`ContMDiffAt I I' ω f x`) are
exactly the maps whose coordinate expressions in charts are analytic in the sense of convergent
power series (`AnalyticAt`). This file records that dictionary, so that results about analytic
functions on open subsets of a normed space (identity theorem, semianalytic presentations,
complexification) can be applied to analytic functions on analytic manifolds chart by chart.

* The change of coordinates between two charts of the maximal `C^ω` atlas is analytic on its
  (open) domain.
* A map is `C^ω` at `x` if and only if it is continuous at `x` and its coordinate expression in
  any charts of the maximal atlases at `x` and `f x` is analytic at the coordinate of `x`; for a
  function with values in a normed space, continuity is automatic. Only the converse direction
  needs a complete target. On an open subset of a chart domain, being `C^ω` is analyticity of the
  coordinate expression on the image of that subset.
* The identity theorem: two functions that are `C^ω` on a preconnected set and agree near one of
  its points agree on all of it.

The model is assumed boundaryless throughout, so that chart images of open sets are open and
`C^ω` within the model's range is `C^ω` on a neighbourhood.

## Main results

* `ModelWithCorners.analyticOnNhd_extendCoordChange`,
  `ModelWithCorners.analyticAt_extendCoordChange` and `TauCeti.analyticOnNhd_ext_coord_change`:
  changes of coordinates in a `C^ω` atlas are analytic.
* `ContMDiffAt.analyticAt_extend_comp_extend_symm`, `ContMDiffAt.analyticAt_writtenInExtChartAt`,
  `TauCeti.contMDiffAt_omega_iff_of_mem_maximalAtlas` and `TauCeti.contMDiffAt_omega_iff`: `C^ω`
  maps between manifolds in arbitrary and in preferred charts.
* `TauCeti.contMDiffAt_iff_contDiffAt_comp_extend_symm`: `C^n` functions with values in a normed
  space are those with a `C^n` coordinate expression.
* `ContMDiffAt.analyticAt_comp_extend_symm`,
  `TauCeti.contMDiffAt_omega_iff_analyticAt_of_mem_maximalAtlas` and
  `TauCeti.contMDiffAt_omega_iff_analyticAt`: `C^ω` functions with values in a normed space.
* `TauCeti.contMDiffOn_omega_iff_analyticOnNhd_of_mem_maximalAtlas`: the same on open subsets of a
  chart domain.
* `TauCeti.eqOn_of_preconnected_of_eventuallyEq_of_contMDiffAt` and
  `ContMDiff.eq_of_eventuallyEq`: the identity theorem.
-/

public section

open Filter Function IsManifold Set Topology

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {e e' : OpenPartialHomeomorph M H} {x : M}

/-! ### Changes of coordinates -/

namespace ModelWithCorners

/-- **Changes of coordinates are analytic.** For a boundaryless model, the change of coordinates
between two charts of the maximal `C^ω` atlas is analytic on its domain. -/
theorem analyticOnNhd_extendCoordChange (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) :
    AnalyticOnNhd 𝕜 (I.extendCoordChange e e') (I.extendCoordChange e e').source :=
  I.isOpen_extendCoordChange_source.analyticOn_iff_analyticOnNhd.1 <|
    (contDiffOn_omega_iff_analyticOn I.uniqueDiffOn_extendCoordChange_source).1 <|
      I.contDiffOn_extendCoordChange he he'

/-- **Changes of coordinates are analytic.** For a boundaryless model, the change of coordinates
between two charts of the maximal `C^ω` atlas is analytic at the coordinate of every point of both
chart domains. -/
theorem analyticAt_extendCoordChange (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) :
    AnalyticAt 𝕜 (I.extendCoordChange e e') (e.extend I x) :=
  I.analyticOnNhd_extendCoordChange he he' _ <|
    e.extend_image_source_inter (I := I) e' ▸ mem_image_of_mem _ ⟨hxe, hxe'⟩

end ModelWithCorners

/-- For a boundaryless model, the change of coordinates between the preferred charts at two
points of a `C^ω` manifold is analytic on its domain. -/
theorem TauCeti.analyticOnNhd_ext_coord_change [IsManifold I ω M] (x x' : M) :
    AnalyticOnNhd 𝕜 (extChartAt I x ∘ (extChartAt I x').symm)
      ((extChartAt I x').symm ≫ extChartAt I x).source :=
  I.analyticOnNhd_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x)

/-! ### `C^ω` maps in charts -/

/-- For a boundaryless model, a function with values in a normed space is `C^n` at `x` if and only
if its coordinate expression in a chart `e` at `x` of the maximal `C^n` atlas is `C^n` at the
coordinate of `x`. -/
theorem TauCeti.contMDiffAt_iff_contDiffAt_comp_extend_symm {n : ℕ∞ω} {f : M → F}
    (he : e ∈ maximalAtlas I n M) (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(𝕜, F) n f x ↔ ContDiffAt 𝕜 n (f ∘ (e.extend I).symm) (e.extend I x) := by
  rw [ContMDiffAt, contMDiffWithinAt_iff_source_of_mem_maximalAtlas he hx]
  simp [I.range_eq_univ, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]

/-- A function with values in a normed space that is `C^ω` at `x` has an analytic coordinate
expression at the coordinate of `x` in any chart at `x` of the maximal `C^ω` atlas. -/
theorem ContMDiffAt.analyticAt_comp_extend_symm {f : M → F}
    (hf : ContMDiffAt I 𝓘(𝕜, F) ω f x) (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source) :
    AnalyticAt 𝕜 (f ∘ (e.extend I).symm) (e.extend I x) :=
  ((TauCeti.contMDiffAt_iff_contDiffAt_comp_extend_symm he hx).1 hf).analyticAt

/-- A map that is `C^ω` at `x` has an analytic coordinate expression at the coordinate of `x` in
any charts `e` at `x` and `e'` at `f x` of the maximal `C^ω` atlases. -/
theorem ContMDiffAt.analyticAt_extend_comp_extend_symm {f : M → M'}
    {e' : OpenPartialHomeomorph M' H'} (hf : ContMDiffAt I I' ω f x)
    (he : e ∈ maximalAtlas I ω M) (he' : e' ∈ maximalAtlas I' ω M') (hx : x ∈ e.source)
    (hy : f x ∈ e'.source) :
    AnalyticAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I x) :=
  (((contMDiffAt_iff_of_mem_maximalAtlas he he' hx hy).1 hf).2.contDiffAt <|
    by simp [I.range_eq_univ]).analyticAt

/-- A map that is `C^ω` at `x` has an analytic coordinate expression in the preferred charts at `x`
and `f x`, at the coordinate of `x`. -/
theorem ContMDiffAt.analyticAt_writtenInExtChartAt {f : M → M'} (hf : ContMDiffAt I I' ω f x) :
    AnalyticAt 𝕜 (writtenInExtChartAt I I' x f) (extChartAt I x x) :=
  ((contMDiffAt_iff.1 hf).2.contDiffAt <| by simp [I.range_eq_univ]).analyticAt

namespace TauCeti

/-- **`C^ω` maps in charts.** For boundaryless models, a map is `C^ω` at `x` if and only if it is
continuous at `x` and its coordinate expression in charts `e` at `x` and `e'` at `f x` of the
maximal `C^ω` atlases is analytic at the coordinate of `x`. -/
theorem contMDiffAt_omega_iff_of_mem_maximalAtlas [CompleteSpace E']
    {f : M → M'} {e' : OpenPartialHomeomorph M' H'} (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I' ω M') (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMDiffAt I I' ω f x ↔
      ContinuousAt f x ∧ AnalyticAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I x) :=
  ⟨fun hf ↦ ⟨hf.continuousAt, hf.analyticAt_extend_comp_extend_symm he he' hx hy⟩,
    fun hf ↦ (contMDiffAt_iff_of_mem_maximalAtlas he he' hx hy).2
      ⟨hf.1, hf.2.contDiffAt.contDiffWithinAt⟩⟩

/-- **`C^ω` maps in charts.** For boundaryless models, a map is `C^ω` at `x` if and only if it is
continuous at `x` and its coordinate expression in the preferred charts at `x` and `f x` is analytic
at the coordinate of `x`. -/
theorem contMDiffAt_omega_iff [CompleteSpace E'] {f : M → M'} :
    ContMDiffAt I I' ω f x ↔
      ContinuousAt f x ∧ AnalyticAt 𝕜 (writtenInExtChartAt I I' x f) (extChartAt I x x) :=
  ⟨fun hf ↦ ⟨hf.continuousAt, hf.analyticAt_writtenInExtChartAt⟩,
    fun hf ↦ contMDiffAt_iff.2 ⟨hf.1, hf.2.contDiffAt.contDiffWithinAt⟩⟩

/-- **Analytic functions in charts.** For a boundaryless model, a function with values in a
complete normed space is `C^ω` at `x` if and only if its coordinate expression in a chart `e` at `x`
of the maximal `C^ω` atlas is analytic at the coordinate of `x`. -/
theorem contMDiffAt_omega_iff_analyticAt_of_mem_maximalAtlas [CompleteSpace F] {f : M → F}
    (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(𝕜, F) ω f x ↔ AnalyticAt 𝕜 (f ∘ (e.extend I).symm) (e.extend I x) :=
  ⟨fun hf ↦ hf.analyticAt_comp_extend_symm he hx,
    fun hf ↦ (contMDiffAt_iff_contDiffAt_comp_extend_symm he hx).2 hf.contDiffAt⟩

/-- **Analytic functions in charts.** For a boundaryless model, a function with values in a
complete normed space is `C^ω` at `x` if and only if its coordinate expression in the preferred
chart at `x` is analytic at the coordinate of `x`. -/
theorem contMDiffAt_omega_iff_analyticAt [CompleteSpace F] {f : M → F} :
    ContMDiffAt I 𝓘(𝕜, F) ω f x ↔
      AnalyticAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  rw [contMDiffAt_iff_source, I.range_eq_univ, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  exact ⟨ContDiffAt.analyticAt, AnalyticAt.contDiffAt⟩

/-- **Analytic functions on a chart domain.** For a boundaryless model and an open subset `U` of
the domain of a chart `e` of the maximal `C^ω` atlas, a function with values in a normed space is
`C^ω` on `U` if and only if its coordinate expression is analytic on the image of `U`. -/
theorem contMDiffOn_omega_iff_analyticOnNhd_of_mem_maximalAtlas {f : M → F}
    {U : Set M} (he : e ∈ maximalAtlas I ω M) (hU : IsOpen U) (hUe : U ⊆ e.source) :
    ContMDiffOn I 𝓘(𝕜, F) ω f U ↔ AnalyticOnNhd 𝕜 (f ∘ (e.extend I).symm) (e.extend I '' U) := by
  have hmem {y : M} (hy : y ∈ U) : e.extend I '' U ∈ 𝓝 (e.extend I y) :=
    e.extend_image_nhds_mem_nhds_of_boundaryless (hUe hy) (hU.mem_nhds hy)
  -- The chart image of `U` is open, so analyticity on it gives `C^ω` coordinate expressions.
  have hUo : IsOpen (e.extend I '' U) := isOpen_iff_mem_nhds.2 fun _ ⟨_, hy, h⟩ ↦ h ▸ hmem hy
  refine ⟨?_, fun hf y hy ↦ ?_⟩
  · rintro hf _ ⟨y, hy, rfl⟩
    exact (hf.contMDiffAt (hU.mem_nhds hy)).analyticAt_comp_extend_symm he (hUe hy)
  · exact ((contMDiffAt_iff_contDiffAt_comp_extend_symm he (hUe hy)).2 <|
      (hf.contDiffOn hUo.uniqueDiffOn).contDiffAt (hmem hy)).contMDiffWithinAt

/-! ### The identity theorem -/

/-- **The identity theorem on analytic manifolds.** On a `C^ω` manifold modelled without boundary
on a locally connected space, two functions with values in a normed space that are `C^ω` at every
point of a preconnected set `U`, and agree on a neighbourhood of a point of `U`, agree on `U`. -/
theorem eqOn_of_preconnected_of_eventuallyEq_of_contMDiffAt [LocallyConnectedSpace E]
    [IsManifold I ω M] {f g : M → F} {U : Set M} (hf : ∀ x ∈ U, ContMDiffAt I 𝓘(𝕜, F) ω f x)
    (hg : ∀ x ∈ U, ContMDiffAt I 𝓘(𝕜, F) ω g x) (hU : IsPreconnected U) {x₀ : M} (h₀ : x₀ ∈ U)
    (hfg : f =ᶠ[𝓝 x₀] g) : EqOn f g U := by
  -- The set of points near which `f` and `g` agree is open; we show that it contains its limit
  -- points in `U`, by applying the identity theorem in a chart.
  set S := {x | f =ᶠ[𝓝 x] g}
  suffices main : closure S ∩ U ⊆ S from fun x hx ↦
    (hU.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨x₀, h₀, hfg⟩ main
      hx).self_of_nhds
  rintro y ⟨hyS, hyU⟩
  set c := extChartAt I y
  -- `f` and `g` are `C^ω` on an open neighbourhood `O` of `U`.
  set O := {x | ContMDiffAt I 𝓘(𝕜, F) ω f x} ∩ {x | ContMDiffAt I 𝓘(𝕜, F) ω g x}
  have hO : IsOpen O := (isOpen_setOfPred_contMDiffAt (by simp)).inter
    (isOpen_setOfPred_contMDiffAt (by simp))
  have hcy : c.symm ⁻¹' O ∩ c.target ∈ 𝓝 (c y) :=
    inter_mem (extChartAt_preimage_mem_nhds (hO.mem_nhds ⟨hf y hyU, hg y hyU⟩))
      (extChartAt_target_mem_nhds y)
  -- A connected open neighbourhood `W` of `c y` on which both coordinate expressions are analytic.
  obtain ⟨W, ⟨hWo, hcW, hWc⟩, hWO⟩ :=
    (LocallyConnectedSpace.open_connected_basis (c y)).mem_iff.1 hcy
  have han {h : M → F} (hh : ∀ w ∈ W, ContMDiffAt I 𝓘(𝕜, F) ω h (c.symm w)) :
      AnalyticOnNhd 𝕜 (h ∘ c.symm) W := fun w hw ↦ by
    have hw' : c.symm w ∈ (chartAt H y).source := by
      rw [← extChartAt_source I]; exact c.map_target (hWO hw).2
    have h₁ : AnalyticAt 𝕜 (h ∘ c.symm) (c (c.symm w)) :=
      (hh w hw).analyticAt_comp_extend_symm (chart_mem_maximalAtlas y) hw'
    rwa [c.right_inv (hWO hw).2] at h₁
  have hF := han fun w hw ↦ (hWO hw).1.1
  have hG := han fun w hw ↦ (hWO hw).1.2
  -- Some point `z ∈ S` has its coordinate in `W`; the coordinate expressions agree near `c z`.
  have hyW : c.source ∩ c ⁻¹' W ∈ 𝓝 y :=
    inter_mem (extChartAt_source_mem_nhds y) ((continuousAt_extChartAt y).preimage_mem_nhds
      (hWo.mem_nhds hcW))
  obtain ⟨z, ⟨hzc, hzW⟩, hzS⟩ := mem_closure_iff_nhds.1 hyS _ hyW
  have hlim : Tendsto c.symm (𝓝 (c z)) (𝓝 z) := by
    have h₁ : Tendsto c.symm (𝓝 (c z)) (𝓝 (c.symm (c z))) :=
      (continuousAt_extChartAt_symm'' (c.map_source hzc)).tendsto
    rwa [c.left_inv hzc] at h₁
  have hFG : f ∘ c.symm =ᶠ[𝓝 (c z)] g ∘ c.symm := EventuallyEq.comp_tendsto hzS hlim
  have hW := hF.eqOn_of_preconnected_of_eventuallyEq hG hWc.isPreconnected hzW hFG
  filter_upwards [hyW] with w ⟨hwc, hwW⟩
  simpa [c.left_inv hwc] using hW hwW

end TauCeti

/-- **The identity theorem on analytic manifolds.** On a preconnected `C^ω` manifold modelled
without boundary on a locally connected space, two `C^ω` functions with values in a normed space
that agree on a neighbourhood of a point are equal. -/
theorem ContMDiff.eq_of_eventuallyEq [LocallyConnectedSpace E] [IsManifold I ω M]
    [PreconnectedSpace M] {f g : M → F} (hf : ContMDiff I 𝓘(𝕜, F) ω f)
    (hg : ContMDiff I 𝓘(𝕜, F) ω g) {x₀ : M} (hfg : f =ᶠ[𝓝 x₀] g) : f = g :=
  funext fun x ↦ TauCeti.eqOn_of_preconnected_of_eventuallyEq_of_contMDiffAt (fun x _ ↦ hf x)
    (fun x _ ↦ hg x) isPreconnected_univ (mem_univ x₀) hfg (mem_univ x)

end
