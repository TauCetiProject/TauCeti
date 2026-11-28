/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Domain membership, evaluation, and topology for extended coordinate changes

This file collects basic membership, evaluation, composition, continuity, image-transport, and
countable-subcover lemmas for extended charts `e.extend I` and extended coordinate changes
`I.extendCoordChange e e'`, without smoothness or measure-theoretic assumptions.

## Main results

* `ModelWithCorners.mem_extendCoordChange_source_iff`,
  `ModelWithCorners.mem_extendCoordChange_target_iff`, and their projections: explicit
  characterizations of `(I.extendCoordChange e e').source` and `.target`.
* `ModelWithCorners.extend_mem_extendCoordChange_source` and
  `ModelWithCorners.mem_extendCoordChange_source`: membership in `(I.extendCoordChange e e').source`
  from overlap membership in `M` or in `(e.extend I).target`.
* `ModelWithCorners.extendCoordChange_extend`, `ModelWithCorners.extendCoordChange_apply'`,
  `ModelWithCorners.extend_symm_extendCoordChange`, and
  `ModelWithCorners.extendCoordChange_comp_apply`: evaluation, cancellation, and triple-overlap
  composition of `I.extendCoordChange`.
* `OpenPartialHomeomorph.continuous_domRestrict_extend`: `e.extend I` restricted to `e.source` is
  continuous.
* `OpenPartialHomeomorph.image_extend_preimage_inter`: transporting a preimage under `e₀.extend I`
  intersected with two chart sources into `e₁` equals the coordinate-change image.
* `ModelWithCorners.exists_countable_subcover_extendCoordChange_source`: extracting a countable
  subcover of `(e.extend I).target` by chart-overlap domains when the model space is second
  countable.
-/

public section

open scoped Manifold Topology

section CoordChange

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]

namespace ModelWithCorners

/-- Membership in `(I.extendCoordChange e e').source` expressed in terms of `(e.extend I).target`
and `e'.source`. -/
theorem mem_extendCoordChange_source_iff {e e' : OpenPartialHomeomorph M H} {y : E} :
    y ∈ (I.extendCoordChange e e').source ↔
      y ∈ (e.extend I).target ∧ (e.extend I).symm y ∈ e'.source := by
  rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
    e'.extend_source]
  rfl

/-- A point in `(I.extendCoordChange e e').source` lies in `(e.extend I).target`. -/
theorem mem_extend_target_of_mem_extendCoordChange_source {e e' : OpenPartialHomeomorph M H}
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    y ∈ (e.extend I).target :=
  (I.mem_extendCoordChange_source_iff.1 hy).1

/-- The source of `I.extendCoordChange e e'` is contained in `(e.extend I).target`. -/
theorem extendCoordChange_source_subset_extend_target (I : ModelWithCorners 𝕜 E H)
    (e e' : OpenPartialHomeomorph M H) :
    (I.extendCoordChange e e').source ⊆ (e.extend I).target := fun _ hy ↦
  I.mem_extend_target_of_mem_extendCoordChange_source hy

/-- A point in `(I.extendCoordChange e e').source` maps under `(e.extend I).symm` into
`e'.source`. -/
theorem extend_symm_mem_of_mem_extendCoordChange_source {e e' : OpenPartialHomeomorph M H}
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    (e.extend I).symm y ∈ e'.source :=
  (I.mem_extendCoordChange_source_iff.1 hy).2

/-- A point in `(I.extendCoordChange e e').source` maps under `(e.extend I).symm` into
`e.source`. -/
theorem extend_symm_mem_source_of_mem_extendCoordChange_source {e e' : OpenPartialHomeomorph M H}
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    (e.extend I).symm y ∈ e.source :=
  e.extend_source (I := I) ▸
    (e.extend I).map_target (I.mem_extend_target_of_mem_extendCoordChange_source hy)

/-- Membership in `(I.extendCoordChange e e').target` expressed in terms of `(e'.extend I).target`
and `e.source`. -/
theorem mem_extendCoordChange_target_iff {e e' : OpenPartialHomeomorph M H} {z : E} :
    z ∈ (I.extendCoordChange e e').target ↔
      z ∈ (e'.extend I).target ∧ (e'.extend I).symm z ∈ e.source := by
  rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_target, PartialEquiv.symm_target,
    e.extend_source]
  rfl

/-- A point in `(I.extendCoordChange e e').target` lies in `(e'.extend I).target`. -/
theorem mem_extend_target_of_mem_extendCoordChange_target {e e' : OpenPartialHomeomorph M H}
    {z : E} (hz : z ∈ (I.extendCoordChange e e').target) :
    z ∈ (e'.extend I).target :=
  (I.mem_extendCoordChange_target_iff.1 hz).1

/-- A point in `(I.extendCoordChange e e').target` maps under `(e'.extend I).symm` into
`e.source`. -/
theorem extend_symm_mem_of_mem_extendCoordChange_target {e e' : OpenPartialHomeomorph M H}
    {z : E} (hz : z ∈ (I.extendCoordChange e e').target) :
    (e'.extend I).symm z ∈ e.source :=
  (I.mem_extendCoordChange_target_iff.1 hz).2

/-- An extended coordinate change sends points of its source into `(e'.extend I).target`. -/
theorem extendCoordChange_mem_extend_target {e e' : OpenPartialHomeomorph M H} {y : E}
    (hy : y ∈ (I.extendCoordChange e e').source) :
    I.extendCoordChange e e' y ∈ (e'.extend I).target :=
  I.mem_extend_target_of_mem_extendCoordChange_target ((I.extendCoordChange e e').map_source hy)

/-- The image in `e.extend I` of a point in the overlap `e.source ∩ e'.source` belongs to the
source of `I.extendCoordChange e e'`. -/
theorem extend_mem_extendCoordChange_source {e e' : OpenPartialHomeomorph M H}
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    e.extend I x ∈ (I.extendCoordChange e e').source := by
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact Set.mem_image_of_mem _ ⟨hx, hx'⟩

/-- A point in `(e.extend I).target` whose inverse chart image belongs to `e'.source` lies in
the source of `I.extendCoordChange e e'`. -/
theorem mem_extendCoordChange_source {e e' : OpenPartialHomeomorph M H}
    {y : E} (hy : y ∈ (e.extend I).target) (hy' : (e.extend I).symm y ∈ e'.source) :
    y ∈ (I.extendCoordChange e e').source :=
  I.mem_extendCoordChange_source_iff.2 ⟨hy, hy'⟩

/-- Evaluating `I.extendCoordChange e e'` at any point `y` applies `(e.extend I).symm` followed by
`e'.extend I`. -/
theorem extendCoordChange_apply' {e e' : OpenPartialHomeomorph M H} (y : E) :
    I.extendCoordChange e e' y = e'.extend I ((e.extend I).symm y) :=
  PartialEquiv.trans_apply (e.extend I).symm (e'.extend I)

/-- Evaluating `I.extendCoordChange e e'` at `e.extend I x` for `x ∈ e.source` gives
`e'.extend I x`. -/
theorem extendCoordChange_extend {e e' : OpenPartialHomeomorph M H} {x : M}
    (hx : x ∈ e.source) :
    I.extendCoordChange e e' (e.extend I x) = e'.extend I x := by
  rw [I.extendCoordChange_apply', (e.extend I).left_inv (e.extend_source (I := I) ▸ hx)]

/-- Applying `(e'.extend I).symm` after `I.extendCoordChange e e'` on its source recovers
`(e.extend I).symm`. -/
theorem extend_symm_extendCoordChange {e e' : OpenPartialHomeomorph M H}
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    (e'.extend I).symm (I.extendCoordChange e e' y) = (e.extend I).symm y := by
  rw [I.extendCoordChange_apply']
  exact (e'.extend I).left_inv
    (e'.extend_source (I := I) ▸ I.extend_symm_mem_of_mem_extendCoordChange_source hy)

/-- On the source of `I.extendCoordChange e e'`, composing `I.extendCoordChange e e'` with
`I.extendCoordChange e' e''` agrees with `I.extendCoordChange e e''`. -/
theorem extendCoordChange_comp_apply {e e' e'' : OpenPartialHomeomorph M H} {y : E}
    (hy : y ∈ (I.extendCoordChange e e').source) :
    I.extendCoordChange e' e'' (I.extendCoordChange e e' y) = I.extendCoordChange e e'' y := by
  rw [I.extendCoordChange_apply' y,
    I.extendCoordChange_extend (I.extend_symm_mem_of_mem_extendCoordChange_source hy),
    I.extendCoordChange_apply' y]

/-- Extract a countable subcover of `(e.extend I).target` by chart-overlap domains when the model
space is second countable. -/
theorem exists_countable_subcover_extendCoordChange_source [SecondCountableTopology E]
    (I : ModelWithCorners 𝕜 E H) (e : OpenPartialHomeomorph M H)
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

end ModelWithCorners

namespace OpenPartialHomeomorph

/-- Restricting an extended chart `e.extend I` to `e.source` gives a continuous map. -/
theorem continuous_domRestrict_extend (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) :
    Continuous (e.source.domRestrict (e.extend I)) := by
  rw [← continuousOn_iff_continuous_domRestrict, ← e.extend_source (I := I)]
  exact e.continuousOn_extend

/-- Transporting the intersection of a preimage under `e₀.extend I` and two chart sources into `e₁`
agrees with the image under `I.extendCoordChange e₀ e₁` restricted to its source. -/
theorem image_extend_preimage_inter (e₀ e₁ : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (A : Set E) :
    e₁.extend I '' ((e₀.extend I ⁻¹' A ∩ e₀.source) ∩ e₁.source) =
      I.extendCoordChange e₀ e₁ '' (A ∩ (I.extendCoordChange e₀ e₁).source) := by
  ext z
  refine ⟨fun ⟨x, ⟨⟨hxA, hx0⟩, hx1⟩, hxz⟩ ↦ ?_, fun ⟨y, ⟨hyA, hyΦ⟩, hyz⟩ ↦ ?_⟩
  · refine ⟨e₀.extend I x, ⟨hxA, I.extend_mem_extendCoordChange_source hx0 hx1⟩, ?_⟩
    rwa [I.extendCoordChange_extend hx0]
  · have hyT : y ∈ (e₀.extend I).target := I.mem_extend_target_of_mem_extendCoordChange_source hyΦ
    have hx0 : (e₀.extend I).symm y ∈ e₀.source :=
      I.extend_symm_mem_source_of_mem_extendCoordChange_source hyΦ
    have hx1 : (e₀.extend I).symm y ∈ e₁.source :=
      I.extend_symm_mem_of_mem_extendCoordChange_source hyΦ
    refine ⟨(e₀.extend I).symm y,
      ⟨⟨by rw [Set.mem_preimage, (e₀.extend I).right_inv hyT]; exact hyA, hx0⟩, hx1⟩, ?_⟩
    rwa [I.extendCoordChange_apply'] at hyz

end OpenPartialHomeomorph

end CoordChange
