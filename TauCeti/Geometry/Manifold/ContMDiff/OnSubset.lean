/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# `C^n` maps on arbitrary subsets of a normed space

A map `f : s → M` from an arbitrary subset `s` of a normed space `E` to a manifold `M` is `C^n`
in the sense of maps on arbitrary subsets when every point of `s` has a neighbourhood in `E` and a
`C^n` map on that neighbourhood which agrees with `f` on `s`. Only these local extensions are
required: for a manifold-valued map they cannot in general be patched into a single `C^n` map on a
neighbourhood of all of `s`, because the target is not a vector space.

This is the regularity of smooth singular simplices, whose domain is the closed standard simplex,
a subset of Euclidean space with corners.

## Main definitions and results

* `TauCeti.ContMDiffOnSubset`: `f : s → M` is `C^n` in the sense of maps on arbitrary subsets.
* `TauCeti.ContMDiffOnSubset.continuous`: such a map is continuous.
* `TauCeti.ContMDiffOnSubset.contMDiffOn`: every ambient map agreeing with it on `s` is `C^n`
  within `s`.
* `ContMDiffOn.contMDiffOnSubset`: the restriction of a map that is `C^n` on a neighbourhood of `s`.
* `TauCeti.ContMDiffOnSubset.comp_contDiff`: precomposition with a `C^n` map of normed spaces.
* `ContMDiff.comp_contMDiffOnSubset`: postcomposition with a `C^n` map of manifolds.
* `TauCeti.ContMDiffOnSubset.prodMk`: a pair of such maps is such a map to the product.
* `TauCeti.ContMDiffOnSubset.subtypeVal_comp_iff`: a map into an open submanifold is such a map
  exactly when its composition with the inclusion is.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 2 (smooth maps on arbitrary
  subsets) and Chapter 18 (smooth singular simplices).
-/

public section

open Set Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 F' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {m n : WithTop ℕ∞}

namespace TauCeti

variable (I n) in
/-- A map `f : s → M` on a subset `s` of a normed space is `C^n` in the sense of maps on arbitrary
subsets: near every point of `s`, it agrees on `s` with a map that is `C^n` on a neighbourhood of
that point. No single extension to a neighbourhood of all of `s` is assumed. -/
def ContMDiffOnSubset {s : Set E} (f : s → M) : Prop :=
  ∀ x : s, ∃ U ∈ 𝓝 (x : E), ∃ g : E → M, ContMDiffOn 𝓘(𝕜, E) I n g U ∧
    ∀ y : s, (y : E) ∈ U → g y = f y

namespace ContMDiffOnSubset

variable {s : Set E} {t : Set E'} {f : s → M}

/-- A map that is `C^n` on an arbitrary subset is continuous. -/
theorem continuous (hf : ContMDiffOnSubset I n f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  obtain ⟨U, hU, g, hg, hgf⟩ := hf x
  refine ((hg.continuousOn.continuousAt hU).comp continuous_subtype_val.continuousAt).congr ?_
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hU] with y hy
    using hgf y hy

/-- A map that is `C^n` on an arbitrary subset is `C^m` there for every `m ≤ n`. -/
theorem of_le (hf : ContMDiffOnSubset I n f) (hmn : m ≤ n) : ContMDiffOnSubset I m f := by
  intro x
  obtain ⟨U, hU, g, hg, hgf⟩ := hf x
  exact ⟨U, hU, g, hg.of_le hmn, hgf⟩

/-- Every map on the ambient space that agrees on `s` with a map that is `C^n` on `s`, in the sense
of maps on arbitrary subsets, is `C^n` within `s` at each point of `s`. -/
theorem contMDiffOn (hf : ContMDiffOnSubset I n f) {g : E → M} (hg : ∀ x : s, g x = f x) :
    ContMDiffOn 𝓘(𝕜, E) I n g s := by
  intro x hx
  obtain ⟨U, hU, g', hg', hgf⟩ := hf ⟨x, hx⟩
  refine ((hg'.contMDiffAt hU).contMDiffWithinAt (s := s)).congr_of_eventuallyEq ?_
    ((hg ⟨x, hx⟩).trans (hgf ⟨x, hx⟩ (mem_of_mem_nhds hU)).symm)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hU] with y hys hyU
  exact (hg ⟨y, hys⟩).trans (hgf ⟨y, hys⟩ hyU).symm

/-- Precomposing a map that is `C^n` on `t` with a `C^n` map of normed spaces sending `s` into
`t` gives a map that is `C^n` on `s`. -/
theorem comp_contDiff {f : t → M} (hf : ContMDiffOnSubset I n f) {A : E → E'}
    (hA : ContDiff 𝕜 n A) (hst : MapsTo A s t) :
    ContMDiffOnSubset I n (f ∘ hst.restrict A s t) := by
  intro x
  obtain ⟨U, hU, g, hg, hgf⟩ := hf (hst.restrict A s t x)
  exact ⟨A ⁻¹' U, hA.continuous.continuousAt.preimage_mem_nhds hU, g ∘ A,
    hg.comp hA.contMDiff.contMDiffOn Subset.rfl, fun y hy ↦ hgf (hst.restrict A s t y) hy⟩

/-- A pair of maps that are `C^n` on `s` is a map to the product that is `C^n` on `s`. -/
theorem prodMk {g : s → N} (hf : ContMDiffOnSubset I n f) (hg : ContMDiffOnSubset J n g) :
    ContMDiffOnSubset (I.prod J) n fun x ↦ (f x, g x) := by
  intro x
  obtain ⟨U, hU, f', hf', hff⟩ := hf x
  obtain ⟨V, hV, g', hg', hgg⟩ := hg x
  exact ⟨U ∩ V, Filter.inter_mem hU hV, fun y ↦ (f' y, g' y),
    (hf'.mono inter_subset_left).prodMk (hg'.mono inter_subset_right),
    fun y hy ↦ Prod.ext (hff y hy.1) (hgg y hy.2)⟩

/-- A map into an open submanifold `V` is `C^n` on `s` exactly when its composition with the
inclusion of `V` is. -/
@[simp]
theorem subtypeVal_comp_iff {V : TopologicalSpace.Opens M} {f : s → V} :
    ContMDiffOnSubset I n (Subtype.val ∘ f) ↔ ContMDiffOnSubset I n f := by
  classical
  refine ⟨fun hf x ↦ ?_, fun hf x ↦ ?_⟩
  · -- A local extension into `M` takes values in the open set `V` near `x`, by continuity, and
    -- there it is a local extension into `V`.
    obtain ⟨U, hU, g, hg, hgf⟩ := hf x
    have hgx : g x ∈ V := by
      rw [hgf x (mem_of_mem_nhds hU)]
      exact (f x).2
    refine ⟨U ∩ g ⁻¹' V, Filter.inter_mem hU
      ((hg.continuousOn.continuousAt hU).preimage_mem_nhds (V.isOpen.mem_nhds hgx)),
      fun y ↦ if h : g y ∈ V then ⟨g y, h⟩ else f x, ?_, fun y hy ↦ Subtype.ext ?_⟩
    · rw [← TauCeti.ContMDiffOn.subtypeVal_comp_iff]
      refine (hg.mono inter_subset_left).congr fun y hy ↦ ?_
      have hyV : g y ∈ V := hy.2
      simp [hyV]
    · have hyV : g y ∈ V := hy.2
      simpa [hyV] using hgf y hy.1
  · obtain ⟨U, hU, g, hg, hgf⟩ := hf x
    exact ⟨U, hU, Subtype.val ∘ g, contMDiff_subtype_val.comp_contMDiffOn hg,
      fun y hy ↦ congrArg Subtype.val (hgf y hy)⟩

end ContMDiffOnSubset

variable (I n) in
/-- A constant map is `C^n` on every subset. -/
theorem contMDiffOnSubset_const {s : Set E} (c : M) :
    ContMDiffOnSubset I n (fun _ : s ↦ c) :=
  fun _ ↦ ⟨univ, Filter.univ_mem, fun _ ↦ c, contMDiffOn_const, fun _ _ ↦ rfl⟩

end TauCeti

open TauCeti

/-- The restriction to `s` of a map that is `C^n` on a neighbourhood of `s` is `C^n` on `s`. -/
theorem ContMDiffOn.contMDiffOnSubset {s U : Set E} {g : E → M}
    (hg : ContMDiffOn 𝓘(𝕜, E) I n g U) (hU : U ∈ 𝓝ˢ s) :
    ContMDiffOnSubset I n (s.domRestrict g) :=
  fun x ↦ ⟨U, mem_nhdsSet_iff_forall.1 hU x x.2, g, hg, fun _ _ ↦ rfl⟩

/-- The restriction to `s` of a `C^n` map is `C^n` on `s`. -/
theorem ContMDiff.contMDiffOnSubset {s : Set E} {g : E → M} (hg : ContMDiff 𝓘(𝕜, E) I n g) :
    ContMDiffOnSubset I n (s.domRestrict g) :=
  hg.contMDiffOn.contMDiffOnSubset Filter.univ_mem

/-- Postcomposing a map that is `C^n` on a subset with a `C^n` map of manifolds gives a map that
is `C^n` on that subset. -/
theorem ContMDiff.comp_contMDiffOnSubset {s : Set E} {φ : M → N} (hφ : ContMDiff I J n φ)
    {f : s → M} (hf : ContMDiffOnSubset I n f) : ContMDiffOnSubset J n (φ ∘ f) := by
  intro x
  obtain ⟨U, hU, g, hg, hgf⟩ := hf x
  exact ⟨U, hU, φ ∘ g, hφ.comp_contMDiffOn hg, fun y hy ↦ congrArg φ (hgf y hy)⟩
