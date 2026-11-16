/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Gluing local `Cⁿ` representatives on a manifold

A function on a manifold that agrees almost everywhere near each point of a Lindelöf set `Ω` with
a `Cⁿ` function into a Hausdorff manifold agrees almost everywhere on `Ω` with a single function
that is `Cⁿ` on `Ω`. Two local representatives are continuous and agree almost everywhere on their
common open domain, so for a measure that charges every nonempty open set they agree everywhere
there (`MeasureTheory.Measure.eqOn_open_of_ae_eq`). The value at `y` of any representative near
`y` therefore defines the glued function on `Ω`, and a countable subcover of `Ω` turns the local
almost everywhere equalities into a global one without assuming second countability of the ambient
manifold.

This is the manifold counterpart of `TauCeti.exists_contDiffOn_ae_eq_of_locally`.

## Main results

* `TauCeti.Manifold.exists_contMDiffOn_ae_eq_of_locally`: local `Cⁿ` representatives on a Lindelöf
  subset glue to a single `Cⁿ` representative on that subset.
* `TauCeti.Manifold.exists_contMDiff_ae_eq_of_locally`: global version on a Lindelöf manifold.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [T2Space M'] [ChartedSpace H' M']
  {μ : Measure M} [μ.IsOpenPosMeasure] {n : WithTop ℕ∞} {u : M → M'} {Ω : Set M}

/-- **Gluing local `Cⁿ` representatives on a manifold.** If near each point of a Lindelöf set `Ω`
the function `u` agrees almost everywhere with a function `Cⁿ` on a neighbourhood of that point,
then `u` agrees almost everywhere on `Ω` with a single function `Cⁿ` on `Ω`. The measure must
charge every nonempty open set and the target manifold must be Hausdorff. -/
theorem exists_contMDiffOn_ae_eq_of_locally (hΩ : IsLindelof Ω)
    (h : ∀ x ∈ Ω, ∃ U ∈ 𝓝 x, ∃ g : M → M', ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g) :
    ∃ g : M → M', ContMDiffOn I I' n g Ω ∧ u =ᵐ[μ.restrict Ω] g := by
  classical
  -- Shrink every neighbourhood to an open one.
  have h' : ∀ x ∈ Ω, ∃ U, IsOpen U ∧ x ∈ U ∧
      ∃ g : M → M', ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g := by
    intro x hx
    obtain ⟨U, hU, g, hg, hug⟩ := h x hx
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
      hg.mono interior_subset, ae_restrict_of_ae_restrict_of_subset interior_subset hug⟩
  choose! U hUo hxU g hg hug using h'
  -- Local representatives agree on overlaps since `μ` charges every nonempty open set.
  let G : M → M' := fun y ↦ if hy : y ∈ Ω then g y hy y else u y
  have hGΩ : ∀ y (hy : y ∈ Ω), G y = g y hy y := fun y hy ↦ dite_eq_left hy
  have hGu : ∀ y ∉ Ω, G y = u y := fun y hy ↦ dite_eq_right hy
  have hG : ∀ x (hx : x ∈ Ω), EqOn G (g x hx) (Ω ∩ U x) := fun x hx y hy ↦ by
    rw [hGΩ y hy.1]
    exact Measure.eqOn_open_of_ae_eq (f := g y hy.1) (g := g x hx)
      ((EventuallyEq.symm <| ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (hug y hy.1)).trans (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hug x hx)))
      ((hUo y hy.1).inter (hUo x hx)) ((hg y hy.1).continuousOn.mono inter_subset_left)
      ((hg x hx).continuousOn.mono inter_subset_right) ⟨hxU y hy.1, hy.2⟩
  refine ⟨G, contMDiffOn_of_locally_contMDiffOn fun x hx ↦
    ⟨U x, hUo x hx, hxU x hx, ((hg x hx).mono inter_subset_right).congr (hG x hx)⟩, ?_⟩
  -- A countable subcover of `Ω` turns the local almost everywhere equalities into a global one.
  have hmem : ∀ y, u y ≠ G y → y ∈ Ω := fun y hy ↦ by_contra fun hyΩ ↦ hy (hGu y hyΩ).symm
  obtain ⟨t, htc, htΩ, hΩt⟩ := hΩ.elim_nhds_subcover U fun x hx ↦ (hUo x hx).mem_nhds (hxU x hx)
  have hnull : μ (⋃ x ∈ t, {y | y ∈ U x ∧ u y ≠ G y}) = 0 := by
    refine (measure_biUnion_null_iff htc).2 fun x hx ↦ ?_
    refine measure_mono_null ?_ (ae_iff.1 (ae_imp_of_ae_restrict (hug x (htΩ x hx))))
    intro y hy
    exact not_imp.2 ⟨hy.1, by rw [← hG x (htΩ x hx) ⟨hmem y hy.2, hy.1⟩]; exact hy.2⟩
  refine ae_restrict_of_ae <| ae_iff.2 <| measure_mono_null (fun y hy ↦ ?_) hnull
  obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.1 (hΩt (hmem y hy))
  exact mem_iUnion₂.2 ⟨x, hxt, hyU, hy⟩

/-- **Gluing local `Cⁿ` representatives globally on a Lindelöf manifold.** If near every point of a
Lindelöf manifold `M` the function `u` agrees almost everywhere with a `Cⁿ` function, then `u`
agrees almost everywhere on `M` with a single `Cⁿ` function. -/
theorem exists_contMDiff_ae_eq_of_locally [LindelofSpace M]
    (h : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → M', ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g) :
    ∃ g : M → M', ContMDiff I I' n g ∧ u =ᵐ[μ] g := by
  obtain ⟨g, hg, hug⟩ := exists_contMDiffOn_ae_eq_of_locally isLindelof_univ fun x _ ↦ h x
  exact ⟨g, contMDiffOn_univ.1 hg, by rwa [Measure.restrict_univ] at hug⟩

end TauCeti.Manifold
