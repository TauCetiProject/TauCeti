/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification
public import TauCeti.GroupTheory.Perm.ComputedCycleType

/-!
# Full cycle types of labelled permutation groups

Conjugate permutation groups exhibit the same full cycle types, including fixed points.
Consequently a transitive-group label determines the set of cycle types, although a collection
of exhibited types need not determine a label. This file proves the comparison and calculates
the complete sets for the five transitive groups of degree five.

The cyclic and dihedral groups exhibit respectively two and three types; the Frobenius group
exhibits four. The alternating and symmetric groups exhibit four and seven types respectively.
In particular, every type of the dihedral group also occurs in the alternating group, while
only the symmetric group exhibits type `(2, 3)`.

The finite calculations use the existing reference generators and orders, together with
`Equiv.Perm.computedCycleType` and its agreement with the canonical full cycle type.

## References

* LMFDB, *Transitive groups*, entries `5T1` through `5T5`.
* G. Butler and J. McKay, *The transitive groups of degree up to eleven*.
-/

public section

open Equiv Equiv.Perm

namespace TauCeti

/-- A labelled permutation subgroup exhibits exactly the full cycle types of its reference
subgroup. The equality keeps the parts equal to one, so both sides are partitions of `n`. -/
theorem TransitiveGroupLabel.image_fullCycleType_eq {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) :
    fullCycleType '' (G : Set (Perm (Fin n))) =
      fullCycleType '' (referenceSubgroup n j : Set (Perm (Fin n))) := by
  obtain ⟨τ, hτ⟩ := h.exists_map_permCongrHom_eq
  rw [← hτ, Equiv.image_fullCycleType_map_permCongrHom]

-- For the three solvable quintic references, enumerate the usual rotation–complement words.
-- Their already-proved orders show that these lists exhaust the groups.
private def quinticWords (s : Perm (Fin 5)) (m : ℕ) : Finset (Perm (Fin 5)) :=
  Finset.univ.image fun i : Fin 5 × Fin m => finRotate 5 ^ (i.1 : ℕ) * s ^ (i.2 : ℕ)

private theorem quinticWords_eq_reference {j : TransitiveGroupIndex 5}
    {s : Perm (Fin 5)} {m : ℕ} (hr : finRotate 5 ∈ referenceSubgroup 5 j)
    (hs : s ∈ referenceSubgroup 5 j)
    (hc : (quinticWords s m).card = Nat.card (referenceSubgroup 5 j)) :
    (quinticWords s m : Set (Perm (Fin 5))) = referenceSubgroup 5 j := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro σ hσ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hσ
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hr _) (Subgroup.pow_mem _ hs _)
  · rw [Set.ncard_coe_finset, hc]
    exact le_of_eq (Nat.card_coe_set_eq _).symm
  · exact Set.toFinite _

-- Simplify the whole image before the defining simp lemmas unfold the reference subgroup.
/-- The cyclic group `5T1` exhibits just the identity type and the five-cycle type. -/
@[simp↓]
theorem image_fullCycleType_referenceSubgroup_five_zero :
    fullCycleType '' (referenceSubgroup 5 ⟨0, by simp⟩ : Set (Perm (Fin 5))) =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}} := by
  have he : (quinticWords 1 1 : Set (Perm (Fin 5))) = referenceSubgroup 5 ⟨0, by simp⟩ :=
    quinticWords_eq_reference (by
      rw [referenceSubgroup_five_zero]; exact Subgroup.subset_closure (by simp))
      (Subgroup.one_mem _) (by rw [natCard_referenceSubgroup_five_zero]; decide)
  have hc : (quinticWords 1 1).image computedCycleType =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}} := by decide +kernel
  rw [← he]
  simpa only [Finset.coe_singleton, Finset.coe_insert] using
    image_fullCycleType_eq_of_computedCycleType hc

/-- The dihedral group `5T2` adds the double-transposition type to the two cyclic types. -/
@[simp↓]
theorem image_fullCycleType_referenceSubgroup_five_one :
    fullCycleType '' (referenceSubgroup 5 ⟨1, by simp⟩ : Set (Perm (Fin 5))) =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}, {2, 2, 1}} := by
  have he : (quinticWords (swap 0 3 * swap 1 2) 2 : Set (Perm (Fin 5))) =
      referenceSubgroup 5 ⟨1, by simp⟩ :=
    quinticWords_eq_reference (by
      rw [referenceSubgroup_five_one]; exact Subgroup.subset_closure (by simp))
      (by rw [referenceSubgroup_five_one]; exact Subgroup.subset_closure (by simp))
      (by rw [natCard_referenceSubgroup_five_one]; decide)
  have hc : (quinticWords (swap 0 3 * swap 1 2) 2).image computedCycleType =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}, {2, 2, 1}} := by decide +kernel
  rw [← he]
  simpa only [Finset.coe_singleton, Finset.coe_insert] using
    image_fullCycleType_eq_of_computedCycleType hc

/-- The Frobenius group `5T3` exhibits the identity, a five-cycle, a double transposition,
and a four-cycle with one fixed point. -/
@[simp↓]
theorem image_fullCycleType_referenceSubgroup_five_two :
    fullCycleType '' (referenceSubgroup 5 ⟨2, by simp⟩ : Set (Perm (Fin 5))) =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}, {2, 2, 1}, {4, 1}} := by
  have he : (quinticWords [0, 1, 3, 2].formPerm 4 : Set (Perm (Fin 5))) =
      referenceSubgroup 5 ⟨2, by simp⟩ :=
    quinticWords_eq_reference (by
      rw [referenceSubgroup_five_two]; exact Subgroup.subset_closure (by simp))
      (by rw [referenceSubgroup_five_two]; exact Subgroup.subset_closure (by simp))
      (by rw [natCard_referenceSubgroup_five_two]; decide)
  have hc : (quinticWords [0, 1, 3, 2].formPerm 4).image computedCycleType =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}, {2, 2, 1}, {4, 1}} := by decide +kernel
  rw [← he]
  simpa only [Finset.coe_singleton, Finset.coe_insert] using
    image_fullCycleType_eq_of_computedCycleType hc

/-- The alternating group `5T4` exhibits precisely the even partitions of five. -/
@[simp↓]
theorem image_fullCycleType_referenceSubgroup_five_three :
    fullCycleType '' (referenceSubgroup 5 ⟨3, by simp⟩ : Set (Perm (Fin 5))) =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}, {2, 2, 1}, {3, 1, 1}} := by
  have he : ((Finset.univ.filter fun σ : Perm (Fin 5) => sign σ = 1) : Set (Perm (Fin 5))) =
      referenceSubgroup 5 ⟨3, by simp⟩ := by
    ext σ
    simp [referenceSubgroup_five_three, mem_alternatingGroup]
  have hc : (Finset.univ.filter fun σ : Perm (Fin 5) => sign σ = 1).image computedCycleType =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}, {2, 2, 1}, {3, 1, 1}} := by decide +kernel
  rw [← he]
  simpa only [Finset.coe_singleton, Finset.coe_insert] using
    image_fullCycleType_eq_of_computedCycleType hc

/-- The symmetric group `5T5` exhibits every partition of five. -/
@[simp↓]
theorem image_fullCycleType_referenceSubgroup_five_four :
    fullCycleType '' (referenceSubgroup 5 ⟨4, by simp⟩ : Set (Perm (Fin 5))) =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}, {2, 2, 1}, {4, 1}, {3, 1, 1}, {2, 1, 1, 1},
        {3, 2}} := by
  have hc : (Finset.univ : Finset (Perm (Fin 5))).image computedCycleType =
      {({1, 1, 1, 1, 1} : Multiset ℕ), {5}, {2, 2, 1}, {4, 1}, {3, 1, 1}, {2, 1, 1, 1},
        {3, 2}} := by decide +kernel
  simpa only [Finset.coe_univ, Finset.coe_singleton, Finset.coe_insert,
    referenceSubgroup_five_four, Subgroup.coe_top] using
    image_fullCycleType_eq_of_computedCycleType hc

end TauCeti
