/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Generation from two double cosets

If every element outside a subgroup `B` lies in one double coset `B w B`, then `B` and `w`
generate the ambient group, so the only subgroups containing `B` are `B` itself and the whole
group. When that group is nonsolvable, every solvable subgroup containing `B` is therefore equal
to `B`.

## Main statements

* `Subgroup.closure_insert_eq_top_of_notMem_imp_mem_doubleCoset`: a subgroup and a representative
  generate the ambient group when their two double cosets cover it.
* `Subgroup.eq_or_eq_top_of_le_of_notMem_imp_mem_doubleCoset`: every subgroup containing that
  subgroup is either equal to it or is the whole group.
* `Subgroup.eq_of_isSolvable_of_not_isSolvable_of_notMem_imp_mem_doubleCoset`: in a nonsolvable
  group, every solvable subgroup containing that subgroup is equal to it.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- If every element outside a subgroup `B` belongs to the double coset `B w B`, then `B` and
`w` generate the ambient group. -/
theorem closure_insert_eq_top_of_notMem_imp_mem_doubleCoset (B : Subgroup G) (w : G)
    (hcell : ∀ {g : G}, g ∉ B →
      g ∈ DoubleCoset.doubleCoset w (B : Set G) (B : Set G)) :
    closure (insert w (B : Set G)) = ⊤ := by
  have hsub : insert w (B : Set G) ⊆ closure (insert w (B : Set G)) := subset_closure
  refine eq_top_iff.mpr fun g _ ↦ ?_
  by_cases hg : g ∈ B
  · exact hsub (.inr hg)
  · obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp (hcell hg)
    exact mul_mem (mul_mem (hsub (.inr hx)) (hsub (.inl rfl))) (hsub (.inr hy))

/-- If every element outside a subgroup `B` belongs to the double coset `B w B`, then every
subgroup containing `B` is either `B` itself or the whole group. -/
theorem eq_or_eq_top_of_le_of_notMem_imp_mem_doubleCoset (B P : Subgroup G) (w : G)
    (hcell : ∀ {g : G}, g ∉ B →
      g ∈ DoubleCoset.doubleCoset w (B : Set G) (B : Set G))
    (hBP : B ≤ P) : P = B ∨ P = ⊤ := by
  refine or_iff_not_imp_left.mpr fun hPB ↦ ?_
  obtain ⟨g, hgP, hgB⟩ : ∃ g ∈ P, g ∉ B :=
    IsConcreteLE.not_le_iff_exists.mp fun hle ↦ hPB (le_antisymm hle hBP)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp (hcell hgB)
  have hwP : w ∈ P := by
    simpa [mul_assoc] using mul_mem (mul_mem (inv_mem (hBP hx)) hgP) (inv_mem (hBP hy))
  rw [eq_top_iff, ← closure_insert_eq_top_of_notMem_imp_mem_doubleCoset B w hcell]
  exact (closure_le P).mpr (Set.insert_subset hwP hBP)

/-- Suppose every element outside `B` belongs to `B w B`. If the ambient group is not solvable,
then every solvable subgroup containing `B` is equal to `B`. -/
theorem eq_of_isSolvable_of_not_isSolvable_of_notMem_imp_mem_doubleCoset
    (B P : Subgroup G) (w : G) [Group.IsSolvable P] (hG : ¬ Group.IsSolvable G)
    (hcell : ∀ {g : G}, g ∉ B →
      g ∈ DoubleCoset.doubleCoset w (B : Set G) (B : Set G))
    (hBP : B ≤ P) : P = B := by
  refine (eq_or_eq_top_of_le_of_notMem_imp_mem_doubleCoset B P w hcell hBP).resolve_right ?_
  rintro rfl
  exact hG (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
    topEquiv.surjective)

end Subgroup
