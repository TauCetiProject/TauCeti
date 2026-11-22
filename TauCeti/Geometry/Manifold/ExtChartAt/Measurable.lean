/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Compactness.Paracompact

/-!
# Chart measurability and overlap covers for extended charts

This file provides low-level measurability, image-preimage overlap, and countable coordinate-change
cover lemmas for arbitrary extended charts `e.extend I`, without Jacobian change-of-variables or
Haar integration dependencies.

## Main results

* `OpenPartialHomeomorph.measurableSet_preimage_extend_inter`: Borel preimages under `e.extend I`
  intersected with `e.source` are measurable.
* `OpenPartialHomeomorph.measurableSet_extendCoordChange_source`: the source of an extended
  coordinate change is measurable.
* `OpenPartialHomeomorph.image_extend_preimage_inter`: transporting a preimage under `e₀.extend I`
  intersected with two chart sources into `e₁` equals the coordinate-change image.
* `OpenPartialHomeomorph.exists_countable_coordChange_cover`: extracting a countable subcover of
  `(e.extend I).target` by chart-overlap domains when the model space is second countable.
-/

public section

open scoped Manifold Topology

namespace OpenPartialHomeomorph

section ExtendMeasurable

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M]

/-- The preimage of a Borel measurable set in `E` under `e.extend I`, intersected with `e.source`,
is measurable whenever open subsets of `M` are measurable. -/
theorem measurableSet_preimage_extend_inter [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {A : Set E} (hA : MeasurableSet A) :
    MeasurableSet (e.extend I ⁻¹' A ∩ e.source) := by
  have hcont : Continuous (e.source.domRestrict (e.extend I)) := by
    rw [← continuousOn_iff_continuous_domRestrict, ← e.extend_source (I := I)]
    exact e.continuousOn_extend
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have hseq : e.extend I ⁻¹' A ∩ e.source =
      Subtype.val '' (e.source.domRestrict (e.extend I) ⁻¹' A) := by
    ext x
    simp [and_comm]
  rw [hseq]
  exact hval.measurableSet_image.2 (hcont.measurable hA)

/-- The source of an extended coordinate change is measurable whenever open subsets of `E`
are measurable. -/
theorem measurableSet_extendCoordChange_source [MeasurableSpace E] [OpensMeasurableSpace E]
    (e e' : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H) :
    MeasurableSet (I.extendCoordChange e e').source := by
  rw [I.extendCoordChange_source, I.image_eq]
  exact ((e.symm ≫ₕ e').open_source.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

/-- Transporting the intersection of a preimage under `e₀.extend I` and two chart sources into `e₁`
agrees with the image under `I.extendCoordChange e₀ e₁` restricted to its source. -/
theorem image_extend_preimage_inter (e₀ e₁ : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (A : Set E) :
    e₁.extend I '' ((e₀.extend I ⁻¹' A ∩ e₀.source) ∩ e₁.source) =
      I.extendCoordChange e₀ e₁ '' (A ∩ (I.extendCoordChange e₀ e₁).source) := by
  ext z
  refine ⟨fun ⟨x, ⟨⟨hxA, hx0⟩, hx1⟩, hxz⟩ ↦ ?_, fun ⟨y, ⟨hyA, hyΦ⟩, hyz⟩ ↦ ?_⟩
  · refine ⟨e₀.extend I x, ⟨hxA, ?_⟩, ?_⟩
    · rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e₀) (f' := e₁)]
      exact Set.mem_image_of_mem _ ⟨hx0, hx1⟩
    · have hx0' : x ∈ (e₀.extend I).source := by rwa [e₀.extend_source]
      rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
        (e₀.extend I).left_inv hx0']
      exact hxz
  · have hyT : y ∈ (e₀.extend I).target := hyΦ.1
    have hx1 : (e₀.extend I).symm y ∈ e₁.source := e₁.extend_source (I := I) ▸ hyΦ.2
    refine ⟨(e₀.extend I).symm y,
      ⟨⟨by rw [Set.mem_preimage, (e₀.extend I).right_inv hyT]; exact hyA, ?_⟩, hx1⟩, hyz⟩
    simpa only [← e₀.extend_source (I := I)] using (e₀.extend I).map_target hyT

/-- Extract a countable subcover of `(e.extend I).target` by chart-overlap domains when the model
space is second countable. -/
theorem exists_countable_coordChange_cover [SecondCountableTopology E]
    (e : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H)
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    (hcov_e : ∀ y ∈ (e.extend I).target, ∃ i, y ∈ (I.extendCoordChange e (φ i)).source) :
    ∃ t : Set ι, t.Countable ∧
      (e.extend I).target ⊆ ⋃ i ∈ t, (I.extendCoordChange e (φ i)).source := by
  have hopen (i : ι) : IsOpen (I.symm ⁻¹' (e.symm ≫ₕ φ i).source) :=
    (e.symm ≫ₕ φ i).open_source.preimage I.continuous_symm
  obtain ⟨t, ht, htcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof (e.extend I).target).elim_countable_subcover
      (fun i ↦ I.symm ⁻¹' (e.symm ≫ₕ φ i).source) hopen fun y hy ↦ by
        obtain ⟨i, hyi⟩ := hcov_e y hy
        rw [I.extendCoordChange_source, I.image_eq] at hyi
        exact Set.mem_iUnion.2 ⟨i, hyi.1⟩
  refine ⟨t, ht, fun y hy ↦ ?_⟩
  obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.1 (htcover hy)
  refine Set.mem_iUnion₂.2 ⟨i, hit, ?_⟩
  rw [I.extendCoordChange_source, I.image_eq]
  exact ⟨hyi, e.extend_target_subset_range hy⟩

end ExtendMeasurable

end OpenPartialHomeomorph
