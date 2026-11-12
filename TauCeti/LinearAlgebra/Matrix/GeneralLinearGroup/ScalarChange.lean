/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# Scalar change and lifting for elementary matrices

A unital homomorphism of arbitrary rings carries the elementary subgroup into the elementary
subgroup. If the ring map is surjective, its image is the entire elementary subgroup, without
changing the matrix size. In particular, Whitehead's elementary matrix `u ⊕ u⁻¹` has an
invertible elementary lift. No lifting assertion for arbitrary invertible matrices is needed.

These facts supply elementary lifts for patching invertible matrices over a quotient ring.
We use `Units.map` of `RingHom.mapMatrix`, which does not require commutative coefficients,
and the elementary subgroup and Whitehead factorization from
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary`.

## References

* C. A. Weibel, *The K-book*, Chapter III, §1, especially Remark 1.2.3 and
  Whitehead's Lemma 1.3.3.
-/

public section

open Matrix TauCeti

namespace RingHom

variable {A B C n : Type*} [Ring A] [Ring B] [Ring C] [Fintype n] [DecidableEq n]

/-- Applying a ring homomorphism entrywise to a transvection applies it to the coefficient.
This holds for noncommutative rings as well. -/
@[simp]
theorem mapMatrix_transvectionUnit (f : A →+* B) {i j : n} (hij : i ≠ j) (a : A) :
    Units.map (f.mapMatrix (m := n) : Matrix n n A →* Matrix n n B)
      (transvectionUnit hij a) = transvectionUnit hij (f a) := by
  ext r s
  simp [Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all

/-- Scalar change carries elementary matrices into elementary matrices, in the same size. -/
theorem map_elementarySubgroup_le (f : A →+* B) :
    (elementarySubgroup n A).map (Units.map (f.mapMatrix (m := n)).toMonoidHom) ≤
      elementarySubgroup n B := by
  refine Subgroup.map_le_iff_le_comap.2 (elementarySubgroup_le_iff.2 fun i j hij a ↦ ?_)
  simpa only [Subgroup.mem_comap, RingHom.toMonoidHom_eq_coe, mapMatrix_transvectionUnit] using
    transvectionUnit_mem_elementarySubgroup hij (f a)

/-- A surjective ring map carries the elementary subgroup onto the elementary subgroup.
Unlike surjectivity on the full general linear group, this holds without stabilization. -/
theorem map_elementarySubgroup_eq_of_surjective (f : A →+* B)
    (hf : Function.Surjective f) :
    (elementarySubgroup n A).map (Units.map (f.mapMatrix (m := n)).toMonoidHom) =
      elementarySubgroup n B := by
  refine le_antisymm f.map_elementarySubgroup_le (elementarySubgroup_le_iff.2 ?_)
  intro i j hij b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨transvectionUnit hij a, transvectionUnit_mem_elementarySubgroup hij a,
    f.mapMatrix_transvectionUnit hij a⟩

/-- An elementary invertible matrix lifts to an elementary invertible matrix of the same size
through any surjective ring map. -/
theorem exists_elementarySubgroup_lift (f : A →+* B) (hf : Function.Surjective f)
    {u : GL n B} (hu : u ∈ elementarySubgroup n B) :
    ∃ v ∈ elementarySubgroup n A,
      Units.map (f.mapMatrix (m := n)).toMonoidHom v = u := by
  rw [← f.map_elementarySubgroup_eq_of_surjective hf] at hu
  exact hu

/-- The homomorphism on elementary subgroups induced by a unital ring map. -/
def elementarySubgroupMap (f : A →+* B) :
    elementarySubgroup n A →* elementarySubgroup n B :=
  ((Units.map (f.mapMatrix (m := n)).toMonoidHom).comp
    (elementarySubgroup n A).subtype).codRestrict (elementarySubgroup n B)
      (fun u ↦ f.map_elementarySubgroup_le ⟨u, u.property, rfl⟩)

/-- The induced map on elementary subgroups is entrywise scalar change. -/
@[simp]
theorem coe_elementarySubgroupMap (f : A →+* B) (u : elementarySubgroup n A) :
    (f.elementarySubgroupMap u : GL n B) =
      Units.map (f.mapMatrix (m := n)).toMonoidHom (u : GL n A) :=
  (rfl)

/-- Extension along the identity ring map is the identity on the elementary subgroup. -/
@[simp]
theorem elementarySubgroupMap_id :
    (RingHom.id A).elementarySubgroupMap (n := n) = MonoidHom.id _ := by
  ext u : 1
  apply Subtype.ext
  simp [coe_elementarySubgroupMap]

/-- Extension on elementary subgroups respects composition of ring maps. -/
@[simp]
theorem elementarySubgroupMap_comp (f : A →+* B) (g : B →+* C) :
    (g.comp f).elementarySubgroupMap (n := n) =
      g.elementarySubgroupMap.comp f.elementarySubgroupMap := by
  ext u : 1
  apply Subtype.ext
  simp only [MonoidHom.comp_apply, coe_elementarySubgroupMap]
  rfl

/-- The induced homomorphism on elementary subgroups is surjective whenever the ring map is. -/
theorem elementarySubgroupMap_surjective (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (f.elementarySubgroupMap (n := n)) := by
  intro u
  obtain ⟨v, hv, h⟩ := f.exists_elementarySubgroup_lift hf u.property
  exact ⟨⟨v, hv⟩, Subtype.ext h⟩

/-- Whitehead's matrix `u ⊕ u⁻¹` lifts to an elementary invertible matrix through every
surjective ring map, even when `u` itself has no invertible lift. -/
theorem exists_fromBlocksGL_inv_lift (f : A →+* B) (hf : Function.Surjective f)
    (u : GL n B) :
    ∃ v ∈ elementarySubgroup (n ⊕ n) A,
      Units.map (f.mapMatrix (m := n ⊕ n)).toMonoidHom v = fromBlocksGL (u, u⁻¹) :=
  f.exists_elementarySubgroup_lift hf (fromBlocksGL_inv_mem_elementarySubgroup u)

end RingHom
