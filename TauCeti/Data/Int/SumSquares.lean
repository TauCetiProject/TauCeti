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

An integer vector has coordinate squares summing to one exactly when it is a signed coordinate
unit `±eᵢ`. The classification works over any finite index type and separates this arithmetic
fact from its applications to lattice roots.
-/

public section

namespace TauCeti

open Finset

/-- An integer vector has squares summing to one if and only if it has exactly one nonzero
coordinate, equal to one or minus one. -/
theorem sum_sq_eq_one_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ι → ℤ} :
    ∑ i, z i ^ 2 = 1 ↔ ∃ i, z = Pi.single i 1 ∨ z = -Pi.single i 1 := by
  refine ⟨fun hz ↦ ?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero (hz ▸ one_ne_zero)
    have hsplit := add_sum_erase _ (fun j ↦ z j ^ 2) (mem_univ i)
    have hnn : 0 ≤ ∑ j ∈ univ.erase i, z j ^ 2 := sum_nonneg fun j _ ↦ sq_nonneg (z j)
    have := sq_nonneg (z i)
    have hsq : z i ^ 2 = 1 := by omega
    have hother {j} (hj : j ≠ i) : z j = 0 :=
      sq_eq_zero_iff.mp <| (sum_eq_zero_iff_of_nonneg (s := univ.erase i)
        fun j _ ↦ sq_nonneg (z j)).mp (by omega) j (by simp [hj])
    refine ⟨i, (sq_eq_one_iff.mp hsq).imp (fun h ↦ ?_) fun h ↦ ?_⟩ <;> funext j <;>
      by_cases hj : j = i <;> simp [h, hj, hother]
  · rintro ⟨i, rfl | rfl⟩ <;>
      rw [sum_eq_single_of_mem i (mem_univ i) fun j _ hj ↦ by simp [hj]] <;> simp

end TauCeti
