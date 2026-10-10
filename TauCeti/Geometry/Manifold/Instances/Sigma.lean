/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Disjoint unions of charted spaces

The disjoint union `Σ i, M i` of a family of charted spaces on a common model `H` is charted on
`H`: each copy `Sigma.mk i '' M i` is open, and the chart at `⟨i, x⟩` is the chart of `M i` at `x`
read on that copy. This is the indexed form of Mathlib's binary disjoint union
`ChartedSpace.sum`, and is how a closed manifold with several boundary components, such as a link
exterior, has its boundary presented as one charted space.

## Main definitions

* `ChartedSpace.sigma`: the charted space structure on `Σ i, M i`.

## Main results

* `ChartedSpace.sigma_chartAt`: the chart at `⟨i, x⟩` is the chart of `M i` at `x`, lifted along
  the open embedding `Sigma.mk i`.
* `ChartedSpace.sigma_chartAt_mk_apply`: on the copy of `M i` it agrees with the chart of `M i`.
* `ChartedSpace.mem_atlas_sigma`: the atlas consists of lifted charts of the components.

The construction follows Mathlib's `ChartedSpace.sumOfNonempty` and `ChartedSpace.sum` in
`Mathlib.Geometry.Manifold.ChartedSpace`.
-/

public section

open Set Topology

variable {H : Type*} [TopologicalSpace H] {ι : Type*} {M : ι → Type*}
  [∀ i, TopologicalSpace (M i)] [cm : ∀ i, ChartedSpace H (M i)]

namespace ChartedSpace

/-- The disjoint union of a family of charted spaces modelled on a nonempty space `H` is a charted
space over `H`: the chart at `⟨i, x⟩` is the chart of `M i` at `x`, lifted along `Sigma.mk i`. -/
@[instance_reducible]
noncomputable def sigmaOfNonempty [Nonempty H] : ChartedSpace H (Σ i, M i) where
  atlas := ⋃ i, (fun e ↦ e.lift_openEmbedding (IsOpenEmbedding.sigmaMk (σ := M) (i := i))) ''
    atlas H (M i)
  chartAt x := (chartAt H x.2).lift_openEmbedding IsOpenEmbedding.sigmaMk
  mem_chart_source x := ⟨x.2, mem_chart_source H x.2, rfl⟩
  chart_mem_atlas x := mem_iUnion.2 ⟨x.1, _, chart_mem_atlas H x.2, rfl⟩

/-- The disjoint union of a family of charted spaces on a common model is charted on that
model. When the model is empty, so is every component, and the structure is the empty one. -/
noncomputable instance sigma : ChartedSpace H (Σ i, M i) := by
  by_cases! h : Nonempty H
  · exact sigmaOfNonempty
  have (i : ι) : IsEmpty (M i) := isEmpty_of_chartedSpace H
  exact empty H (Σ i, M i)

/-- The chart of a disjoint union at `⟨i, x⟩` is the chart of `M i` at `x`, lifted along the open
embedding `Sigma.mk i`. -/
lemma sigma_chartAt (x : Σ i, M i) :
    haveI : Nonempty H := nonempty_of_chartedSpace x.2
    chartAt H x = (chartAt H x.2).lift_openEmbedding IsOpenEmbedding.sigmaMk := by
  simp +instances only [chartAt, sigma, nonempty_of_chartedSpace x.2, ↓reduceDIte]
  rfl

/-- On the copy of `M i`, the chart of a disjoint union at `⟨i, x⟩` is the chart of `M i` at
`x`. -/
@[simp, mfld_simps]
lemma sigma_chartAt_mk_apply {i : ι} {x y : M i} :
    chartAt H (⟨i, x⟩ : Σ i, M i) ⟨i, y⟩ = chartAt H x y := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [sigma_chartAt]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

/-- The source of the chart of a disjoint union at `⟨i, x⟩` is the copy of the source of the
chart of `M i` at `x`. -/
@[simp, mfld_simps]
lemma sigma_chartAt_source {i : ι} {x : M i} :
    (chartAt H (⟨i, x⟩ : Σ i, M i)).source = Sigma.mk i '' (chartAt H x).source := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [sigma_chartAt]
  rfl

/-- The target of the chart of a disjoint union at `⟨i, x⟩` is the target of the chart of `M i`
at `x`. -/
@[simp, mfld_simps]
lemma sigma_chartAt_target {i : ι} {x : M i} :
    (chartAt H (⟨i, x⟩ : Σ i, M i)).target = (chartAt H x).target := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [sigma_chartAt]
  rfl

/-- Every chart in the atlas of a disjoint union is a chart in the atlas of one of the components,
lifted along the corresponding open embedding `Sigma.mk i`. -/
lemma mem_atlas_sigma [h : Nonempty H] {e : OpenPartialHomeomorph (Σ i, M i) H}
    (he : e ∈ atlas H (Σ i, M i)) :
    ∃ i, ∃ f ∈ atlas H (M i), e = f.lift_openEmbedding (IsOpenEmbedding.sigmaMk (σ := M)) := by
  simp +instances only [atlas, sigma, h, ↓reduceDIte] at he
  obtain ⟨i, f, hf, rfl⟩ := mem_iUnion.1 he
  exact ⟨i, f, hf, rfl⟩

end ChartedSpace
