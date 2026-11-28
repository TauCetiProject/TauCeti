/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Preorder.Finite

/-!
# Maximal pairwise disjoint subfamilies of a finite family of finite sets

A finite family of finite sets has a subfamily of pairwise disjoint members that is maximal:
every member of the family that is disjoint from all members of the subfamily belongs to it.
The union of such a subfamily meets every nonempty member of the family, which is how it is
used in covering and pigeonhole arguments.
-/

public section

namespace Finset

variable {β : Type*} [DecidableEq β]

/-- Every finite family of finite sets has a maximal subfamily of pairwise disjoint members:
a pairwise disjoint subfamily `D` such that every member of the family that is disjoint from the
union of `D` already belongs to `D`. -/
theorem exists_subset_pairwiseDisjoint_forall_disjoint_biUnion_mem (F : Finset (Finset β)) :
    ∃ D ⊆ F, (D : Set (Finset β)).PairwiseDisjoint id ∧
      ∀ A ∈ F, Disjoint A (D.biUnion id) → A ∈ D := by
  classical
  obtain ⟨D, -, hD⟩ := (F.powerset.filter fun D : Finset (Finset β) ↦
    (D : Set (Finset β)).PairwiseDisjoint id).exists_le_maximal (a := ∅) (by simp)
  have hD' := hD.prop
  simp only [mem_filter, mem_powerset] at hD'
  refine ⟨D, hD'.1, hD'.2, fun A hA hAD ↦ ?_⟩
  refine hD.le_of_ge (y := insert A D) ?_ (subset_insert A D) (mem_insert_self A D)
  simp only [mem_filter, mem_powerset, coe_insert]
  refine ⟨insert_subset hA hD'.1, hD'.2.insert fun B hB _ ↦ ?_⟩
  exact hAD.mono_right (subset_biUnion_of_mem id hB)

end Finset
