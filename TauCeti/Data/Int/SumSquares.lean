/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Order.Units

/-!
# Integer vectors with sum of squares one

An integer vector whose coordinate squares sum to one is a signed coordinate unit. The
classification works over any finite index type and separates this arithmetic fact from
its applications to lattice roots.
-/

public section

namespace TauCeti

/-- An integer vector whose squares sum to one has exactly one nonzero coordinate, equal
to one or minus one. -/
theorem exists_eq_single_or_neg_single_of_sum_sq_eq_one {ι : Type*} [Fintype ι]
    [DecidableEq ι] (z : ι → ℤ) (hz : ∑ i, z i ^ 2 = 1) :
    ∃ i, z = Pi.single i 1 ∨ z = -Pi.single i 1 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ i, z i ^ 2 ≠ 0)
  have hieq : z i ^ 2 = 1 := by
    have hle : z i ^ 2 ≤ 1 := by
      simpa only [hz] using
        (Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i))
    have := sq_nonneg (z i)
    omega
  have hsign := sq_eq_one_iff.mp hieq
  have hrest : ∑ j ∈ Finset.univ.erase i, z j ^ 2 = 0 := by
    have h := Finset.sum_erase_add (s := Finset.univ) (fun j ↦ z j ^ 2)
      (Finset.mem_univ i)
    omega
  have hother {j : ι} (hj : j ≠ i) : z j = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (z j))).mp hrest j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    exact sq_eq_zero_iff.mp this
  refine ⟨i, hsign.imp (fun h ↦ ?_) (fun h ↦ ?_)⟩ <;>
    funext j <;> by_cases hj : j = i
  · subst j
    simp [h]
  · simp [hother hj, Pi.single_eq_of_ne hj]
  · subst j
    simp [h]
  · simp [hother hj, Pi.single_eq_of_ne hj]

end TauCeti
