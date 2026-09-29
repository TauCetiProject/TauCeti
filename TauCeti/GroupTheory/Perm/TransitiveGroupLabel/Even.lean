/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification

/-!
# Transitivity of the even part of a quartic permutation group

Intersecting a transitive subgroup of `S₄` with `A₄` distinguishes the cyclic group `4T1`
from the dihedral group `4T3`. This is the permutation step in the test using the discriminant
quadratic field: its fixing subgroup is the even part of the Galois group, and irreducibility
over that field is equivalent to transitivity of that subgroup on the four roots.

The cyclic group's even part cannot be transitive: the cyclic group has order four but contains
odd permutations. The even part of the dihedral group contains the Klein four-group, which acts
regularly on four points.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm MulAction

/-- The even part of the cyclic quartic reference group is not transitive. -/
theorem not_isPretransitive_referenceSubgroup_four_zero_inf_alternatingGroup :
    ¬ IsPretransitive
      ((referenceSubgroup 4 (⟨0, by simp⟩ : TransitiveGroupIndex 4) ⊓
        alternatingGroup (Fin 4)) : Subgroup (Perm (Fin 4))) (Fin 4) := by
  intro htrans
  let G : Subgroup (Perm (Fin 4)) :=
    referenceSubgroup 4 (⟨0, by simp⟩ : TransitiveGroupIndex 4)
  have hcardG : Nat.card G = 4 := natCard_referenceSubgroup_four_zero
  have hdiv : 4 ∣ Nat.card ((G ⊓ alternatingGroup (Fin 4)) : Subgroup (Perm (Fin 4))) := by
    let _ : IsPretransitive ((G ⊓ alternatingGroup (Fin 4)) : Subgroup (Perm (Fin 4)))
        (Fin 4) := htrans
    simpa using (card_dvd_natCard_and_natCard_dvd_factorial_of_isPretransitive
      ((G ⊓ alternatingGroup (Fin 4)) : Subgroup (Perm (Fin 4)))).1
  have hdiv' : Nat.card ((G ⊓ alternatingGroup (Fin 4)) : Subgroup (Perm (Fin 4))) ∣ 4 := by
    simpa only [hcardG] using
      (Subgroup.card_dvd_of_le (H := G ⊓ alternatingGroup (Fin 4))
        (K := G) inf_le_left)
  have hcard : Nat.card ((G ⊓ alternatingGroup (Fin 4)) : Subgroup (Perm (Fin 4))) = 4 :=
    Nat.dvd_antisymm hdiv' hdiv
  have heq : (G ⊓ alternatingGroup (Fin 4) : Subgroup (Perm (Fin 4))) = G :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardG]; exact hcard.ge)
  have hG : G ≤ alternatingGroup (Fin 4) := by
    rw [← heq]
    exact inf_le_right
  exact not_referenceSubgroup_four_zero_le_alternatingGroup hG

/-- The even part of the dihedral quartic reference group is transitive. -/
theorem isPretransitive_referenceSubgroup_four_two_inf_alternatingGroup :
    IsPretransitive
      ((referenceSubgroup 4 (⟨2, by simp⟩ : TransitiveGroupIndex 4) ⊓
        alternatingGroup (Fin 4)) : Subgroup (Perm (Fin 4))) (Fin 4) := by
  have hle : referenceSubgroup 4 (⟨1, by simp⟩ : TransitiveGroupIndex 4) ≤
      referenceSubgroup 4 (⟨2, by simp⟩ : TransitiveGroupIndex 4) ⊓
        alternatingGroup (Fin 4) := by
    exact le_inf referenceSubgroup_four_one_le_referenceSubgroup_four_two
      referenceSubgroup_four_one_le_alternatingGroup
  exact IsPretransitive.of_compHom (Subgroup.inclusion hle)
    (h := isPretransitive_referenceSubgroup 4 ⟨1, by simp⟩)

/-- The even part of a transitive quartic permutation group is transitive exactly when the group
is not the cyclic group `4T1`. In particular, this separates the cyclic and dihedral groups. -/
@[simp]
theorem TransitiveGroupLabel.isPretransitive_inf_alternatingGroup_iff_ne_zero
    {j : TransitiveGroupIndex 4} {G : Subgroup (Perm (Fin 4))}
    (h : TransitiveGroupLabel j G) :
    IsPretransitive ((G ⊓ alternatingGroup (Fin 4)) : Subgroup (Perm (Fin 4)))
      (Fin 4) ↔ j ≠ ⟨0, by simp⟩ := by
  rw [h.isPretransitive_inf_alternatingGroup_iff]
  obtain ⟨j, hj⟩ := j
  rw [numTransitiveGroups_four] at hj
  interval_cases j
  · exact iff_of_false not_isPretransitive_referenceSubgroup_four_zero_inf_alternatingGroup
      (by simp)
  · rw [inf_eq_left.mpr referenceSubgroup_four_one_le_alternatingGroup]
    exact iff_of_true (isPretransitive_referenceSubgroup 4 ⟨1, by simp⟩) (by simp)
  · exact iff_of_true isPretransitive_referenceSubgroup_four_two_inf_alternatingGroup (by simp)
  · rw [referenceSubgroup_four_three, inf_idem, ← referenceSubgroup_four_three]
    exact iff_of_true (isPretransitive_referenceSubgroup 4 ⟨3, by simp⟩) (by simp)
  · rw [referenceSubgroup_four_four, top_inf_eq, ← referenceSubgroup_four_three]
    exact iff_of_true (isPretransitive_referenceSubgroup 4 ⟨3, by simp⟩) (by simp)

end TauCeti
