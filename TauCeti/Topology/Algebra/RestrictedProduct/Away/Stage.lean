/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Decomposition

/-!
# Open-subgroup stage embeddings into a restricted product

For a finite set `S` of indices and a family `B i` of subgroups of `G i`, the product
`(∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)` embeds as a subgroup into the restricted product
`Πʳ i, [G i, B i]` via `TauCeti.stageEmbedding S hS B`, obtained by composing
`RestrictedProduct.structureMap` on the indices away from `S` with the inverse of
`TauCeti.awayDecomposition S hS B`.

Its range is `{x : Πʳ i, [G i, B i] | ∀ i ∉ S, x i ∈ B i}`, and when `B i` is open for every
`i ∉ S` (openness at `S` is not needed) the map is an open embedding. All declarations carry
additive counterparts (`TauCeti.addStageEmbedding`, …).

## Main definitions and results

* `TauCeti.stageEmbedding`, `TauCeti.addStageEmbedding`: the homomorphism
  `((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) →* Πʳ i, [G i, B i]`, coordinatewise the
  identity (`stageEmbedding_apply_of_mem`, `stageEmbedding_apply_of_notMem`).
* `TauCeti.range_stageEmbedding`, `TauCeti.preimage_stageEmbedding_forall_mem`,
  `TauCeti.image_stageEmbedding_prod_univ`: range and box preimage/image characterizations.
* `TauCeti.isOpenEmbedding_stageEmbedding`: `stageEmbedding S hS B` is an open embedding whenever
  `∀ i ∉ S, IsOpen (B i : Set (G i))`.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*, Classics in Mathematics, Springer, 1995.
-/

public section

namespace TauCeti

open Filter Set Topology
open scoped RestrictedProduct

universe u v

variable {ι : Type u} {G : ι → Type v} [∀ i, Group (G i)]

/-- For a finite set `S` of indices, the monoid homomorphism embedding the open-subgroup stage
`(∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)` into `Πʳ i, [G i, B i]`, coordinatewise the
identity. It composes `RestrictedProduct.structureMap` away from `S` with the inverse of
`awayDecomposition S hS B`. -/
@[to_additive addStageEmbedding /-- For a finite set `S` of indices, the additive monoid
homomorphism embedding the open-subgroup stage `(∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)`
into `Πʳ i, [G i, B i]`, coordinatewise the identity. It composes `RestrictedProduct.structureMap`
away from `S` with the inverse of `addAwayDecomposition S hS B`. -/]
noncomputable def stageEmbedding (S : Set ι) (hS : S.Finite) (B : ∀ i, Subgroup (G i)) :
    ((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) →* Πʳ i, [G i, B i] where
  toFun p := (awayDecomposition S hS B).symm
    (p.1, RestrictedProduct.structureMap (fun j : {i // i ∉ S} ↦ G j.1)
      (fun j ↦ (B j.1 : Set (G j.1))) Filter.cofinite p.2)
  map_one' := by
    rw [← MulEquiv.map_one (awayDecomposition S hS B).symm]
    rfl
  map_mul' _ _ := by
    rw [← MulEquiv.map_mul (awayDecomposition S hS B).symm]
    rfl

variable (S : Set ι) (hS : S.Finite) (B : ∀ i, Subgroup (G i))

/-- At an index `i ∈ S`, `stageEmbedding` reads off the first component. -/
@[to_additive (attr := simp) addStageEmbedding_apply_of_mem /-- At an index `i ∈ S`,
`addStageEmbedding` reads off the first component. -/]
theorem stageEmbedding_apply_of_mem (p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1))
    (i : ι) (hi : i ∈ S) :
    stageEmbedding S hS B p i = p.1 ⟨i, hi⟩ :=
  awayDecomposition_symm_apply_of_mem S hS B _ i hi

/-- Subtype-indexed form of `stageEmbedding_apply_of_mem`. -/
@[to_additive addStageEmbedding_apply_coe_mem /-- Subtype-indexed form of
`addStageEmbedding_apply_of_mem`. -/]
theorem stageEmbedding_apply_coe_mem (p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1))
    (i : S) :
    stageEmbedding S hS B p i.1 = p.1 i :=
  stageEmbedding_apply_of_mem S hS B p i.1 i.2

/-- At an index `i ∉ S`, `stageEmbedding` reads off the second component coerced to `G i`. -/
@[to_additive (attr := simp) addStageEmbedding_apply_of_notMem /-- At an index `i ∉ S`,
`addStageEmbedding` reads off the second component coerced to `G i`. -/]
theorem stageEmbedding_apply_of_notMem (p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1))
    (i : ι) (hi : i ∉ S) :
    stageEmbedding S hS B p i = (p.2 ⟨i, hi⟩ : G i) :=
  awayDecomposition_symm_apply_of_notMem S hS B _ i hi

/-- Subtype-indexed form of `stageEmbedding_apply_of_notMem`. -/
@[to_additive (attr := simp) addStageEmbedding_apply_coe_notMem /-- Subtype-indexed form of
`addStageEmbedding_apply_of_notMem`. -/]
theorem stageEmbedding_apply_coe_notMem (p : (∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1))
    (j : {i // i ∉ S}) :
    stageEmbedding S hS B p j.1 = (p.2 j : G j.1) :=
  stageEmbedding_apply_of_notMem S hS B p j.1 j.2

/-- The range of `stageEmbedding S hS B` is the subgroup of elements lying in `B i` at every index
outside `S`. -/
@[to_additive range_addStageEmbedding /-- The range of `addStageEmbedding S hS B` is the additive
subgroup of elements lying in `B i` at every index outside `S`. -/]
theorem range_stageEmbedding :
    range (stageEmbedding S hS B) = {x : Πʳ i, [G i, B i] | ∀ i ∉ S, x i ∈ B i} := by
  ext x
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨?_, fun hx ↦
    ⟨((awayDecomposition S hS B x).1, fun j ↦ ⟨x j.1, hx j.1 j.2⟩), ?_⟩⟩
  · rintro ⟨p, rfl⟩ i hi
    rw [stageEmbedding_apply_of_notMem S hS B p i hi]
    exact (p.2 ⟨i, hi⟩).2
  · ext i
    by_cases hi : i ∈ S
    · rw [stageEmbedding_apply_of_mem S hS B _ i hi, awayDecomposition_fst]
    · rw [stageEmbedding_apply_of_notMem S hS B _ i hi]

/-- Preimage of a coordinatewise box under `stageEmbedding S hS B`. -/
@[to_additive preimage_addStageEmbedding_forall_mem /-- Preimage of a coordinatewise box under
`addStageEmbedding S hS B`. -/]
theorem preimage_stageEmbedding_forall_mem (C : ∀ i, Set (G i)) :
    stageEmbedding S hS B ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} =
      (univ.pi fun i : S ↦ C i.1) ×ˢ
        (univ.pi fun j : {i // i ∉ S} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) := by
  ext ⟨y, z⟩
  simp only [mem_preimage, mem_ofPred_eq, mem_prod, mem_univ_pi]
  refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun j ↦ ?_⟩, fun ⟨hy, hz⟩ i ↦ ?_⟩
  · simpa using h i.1
  · simpa using h j.1
  · by_cases hi : i ∈ S
    · simpa [stageEmbedding_apply_of_mem S hS B (y, z) i hi] using hy ⟨i, hi⟩
    · simpa [stageEmbedding_apply_of_notMem S hS B (y, z) i hi] using hz ⟨i, hi⟩

/-- Image of `(Set.univ.pi t) ×ˢ Set.univ` under `stageEmbedding S hS B`. -/
@[to_additive image_addStageEmbedding_prod_univ /-- Image of `(Set.univ.pi t) ×ˢ Set.univ` under
`addStageEmbedding S hS B`. -/]
theorem image_stageEmbedding_prod_univ (t : ∀ i : S, Set (G i.1)) :
    stageEmbedding S hS B '' ((univ.pi t) ×ˢ univ) =
      {x : Πʳ i, [G i, B i] | (∀ i : S, x i.1 ∈ t i) ∧ ∀ i ∉ S, x i ∈ B i} := by
  ext x
  simp only [mem_image, Prod.exists, mem_prod, mem_univ_pi, mem_univ, and_true, mem_ofPred_eq]
  refine ⟨?_, fun ⟨ht, hB'⟩ ↦
    ⟨(awayDecomposition S hS B x).1, fun j ↦ ⟨x j.1, hB' j.1 j.2⟩,
      fun i ↦ by simpa [awayDecomposition_fst] using ht i, ?_⟩⟩
  · rintro ⟨y, z, hy, rfl⟩
    refine ⟨fun i ↦ ?_, fun i hi ↦ ?_⟩
    · simpa using hy i
    · rw [stageEmbedding_apply_of_notMem S hS B (y, z) i hi]
      exact (z ⟨i, hi⟩).2
  · ext i
    by_cases hi : i ∈ S
    · rw [stageEmbedding_apply_of_mem S hS B _ i hi, awayDecomposition_fst]
    · rw [stageEmbedding_apply_of_notMem S hS B _ i hi]

variable {S hS B}
variable [∀ i, TopologicalSpace (G i)]

/-- When the reference subgroups away from `S` are open, `stageEmbedding S hS B` is an open
embedding; openness of `B i` for `i ∈ S` is not needed. -/
@[to_additive isOpenEmbedding_addStageEmbedding /-- When the reference subgroups away from `S` are
open, `addStageEmbedding S hS B` is an open embedding; openness of `B i` for `i ∈ S` is not
needed. -/]
theorem isOpenEmbedding_stageEmbedding (hBopen : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    IsOpenEmbedding (stageEmbedding S hS B) := by
  let e : ((∀ i : S, G i.1) × Πʳ j : {i // i ∉ S}, [G j.1, B j.1]) ≃ₜ Πʳ i, [G i, B i] :=
    { toEquiv := (awayDecomposition S hS B).symm.toEquiv
      continuous_toFun := continuous_awayDecomposition_symm S hS B hBopen
      continuous_invFun := continuous_awayDecomposition S hS B }
  exact e.isOpenEmbedding.comp (.prodMap .id
    (RestrictedProduct.isOpenEmbedding_structureMap fun j ↦ hBopen j.1 j.2))

end TauCeti
