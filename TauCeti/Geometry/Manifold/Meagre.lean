/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import TauCeti.Topology.Baire.Lindelof
import TauCeti.Topology.OpenPartialHomeomorph.Baire

/-!
# Meagre images in charts

Whether the image of a set under a map between manifolds is meagre can be read in extended
charts. This holds over any nontrivially normed field, for a target manifold without boundary,
whose extended charts are then open partial homeomorphisms, so their inverses carry meagre sets to
meagre sets.

## Main results

* `TauCeti.isMeagre_image_of_isMeagre_image_extChartAt`: if the coordinate expression of `f` in
  a pair of extended charts sends the chart image of a set `u` in the chart sources to a meagre
  set, then `f '' u` is meagre.
* `TauCeti.isMeagre_image_of_forall_isMeagre_image_extChartAt`: for a map continuous at the
  points of a Lindelöf set `s`, if this holds in the charts at each `x ∈ s` and at `f x` for the
  points of `s` in a neighbourhood of `x`, then `f '' s` is meagre.
-/

public section

open Function Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {s : Set M}

/-- Let `u` be a set in the source of the chart at `x₀` that `f` maps into the source of the chart
at `y₀`. If the coordinate expression `extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm` sends the
chart image of `u` to a meagre subset of the model of `N`, then `f '' u` is meagre. The target is
without boundary, so that its extended charts are open partial homeomorphisms. -/
theorem isMeagre_image_of_isMeagre_image_extChartAt {x₀ : M} {y₀ : N} {u : Set M}
    (hu : u ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source)
    (h : IsMeagre ((extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) '' (extChartAt I x₀ '' u))) :
    IsMeagre (f '' u) := by
  let g : E → E' := extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm
  -- The boundaryless extended chart is an open partial homeomorphism.
  let e := (chartAt H' y₀).transHomeomorph J.toHomeomorph
  -- Both chart constructions have forward map J ∘ chartAt H' y₀: transHomeomorph
  -- composes with J.toHomeomorph, whose forward map is J, while extChartAt extends by J.
  have he (y : N) : e y = extChartAt J y₀ y := rfl
  have hleft (x : M) (hx : x ∈ u) : (extChartAt I x₀).symm (extChartAt I x₀ x) = x :=
    (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact (hu hx).1)
  have hmem : g '' (extChartAt I x₀ '' u) ⊆ e.target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa only [g, comp_apply, hleft x hx, ← he] using e.map_source (hu hx).2
  have himage : e.symm '' (g '' (extChartAt I x₀ '' u)) = f '' u := by
    rw [image_image, image_image]
    refine image_congr fun x hx ↦ ?_
    simp only [comp_apply, g, hleft x hx, ← he, e.left_inv (hu hx).2]
  rw [← himage]
  exact e.symm.isMeagre_image h hmem

/-- **Meagre images can be detected in charts.** Let `f` be continuous at the points of a
Lindelöf set `s`. Suppose that each `x ∈ s` has a neighbourhood `V` such that the coordinate
expression `extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm` sends the chart image of the points of
`s ∩ V` lying in the two chart sources to a meagre subset of the model of `N`. Then `f '' s` is
meagre. The target is without boundary, so that its extended charts are open partial
homeomorphisms. -/
theorem isMeagre_image_of_forall_isMeagre_image_extChartAt [LindelofSpace s]
    (hf : ∀ x ∈ s, ContinuousAt f x)
    (hchart : ∀ x ∈ s, ∃ V ∈ 𝓝 x, IsMeagre ((extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) ''
      (extChartAt I x '' (s ∩ V ∩ (chartAt H x).source ∩ f ⁻¹' (chartAt H' (f x)).source)))) :
    IsMeagre (f '' s) := by
  rw [← inter_self s]
  refine (IsLindelof.of_coe (s := s)).isMeagre_image_inter_of_forall_exists_mem_nhds
    fun x hx ↦ ?_
  obtain ⟨V, hV, hmeagre⟩ := hchart x hx
  -- Near `x`, the points of `s ∩ V` are seen by the charts at `x` and `f x`.
  refine ⟨V ∩ (chartAt H x).source ∩ f ⁻¹' (chartAt H' (f x)).source,
    inter_mem (inter_mem hV (chart_source_mem_nhds H x))
      ((hf x hx).preimage_mem_nhds (chart_source_mem_nhds H' (f x))), ?_⟩
  refine (isMeagre_image_of_isMeagre_image_extChartAt (u := s ∩ V ∩ (chartAt H x).source ∩
    f ⁻¹' (chartAt H' (f x)).source) (fun z hz ↦ ⟨hz.1.2, hz.2⟩) hmeagre).mono
    (image_mono ?_)
  exact fun z hz ↦ ⟨⟨⟨hz.2, hz.1.1.1⟩, hz.1.1.2⟩, hz.1.2⟩

end TauCeti
