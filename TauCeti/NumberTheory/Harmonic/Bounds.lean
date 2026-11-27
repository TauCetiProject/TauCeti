/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Harmonic bounds for reciprocals of distinct integers

Mathlib's `harmonic_le_one_add_log` bounds `∑_{1 ≤ j ≤ m} 1/j` by `1 + log m`. This file records
the consequence for a sum of reciprocals `∑_{n ∈ [1, m]} (d n)⁻¹` whose positive denominators are
distinct elements of `[1, m]`.

## Main results

* `TauCeti.sum_inv_le_one_add_log_of_injOn`: if `d n ≤ m` on `[1, m]` and `d` is injective
  where it is positive, then `∑_{n ∈ [1, m]} (d n)⁻¹ ≤ 1 + log m`.
-/

public section

namespace TauCeti

open Finset

/-- A map `d` into `[0, m]` that is injective where it is positive has `∑ (d n)⁻¹ ≤ 1 + log m`
over `[1, m]`: its positive values are distinct elements of `[1, m]`. -/
theorem sum_inv_le_one_add_log_of_injOn (m : ℕ) (d : ℕ → ℕ)
    (hd : ∀ n ∈ Icc 1 m, d n ≤ m) (hi : Set.InjOn d ↑((Icc 1 m).filter (fun n ↦ 0 < d n))) :
    (∑ n ∈ Icc 1 m, (d n : ℝ)⁻¹) ≤ 1 + Real.log m := by
  rw [← sum_filter_add_sum_filter_not _ (fun n ↦ 0 < d n)]
  have hz : (∑ n ∈ (Icc 1 m).filter (fun n ↦ ¬0 < d n), (d n : ℝ)⁻¹) = 0 := by
    apply sum_eq_zero
    intro n hn
    simp [Nat.eq_zero_of_not_pos (mem_filter.mp hn).2]
  rw [hz, add_zero, ← sum_image (f := fun j : ℕ ↦ (j : ℝ)⁻¹) hi]
  refine (sum_le_sum_of_subset_of_nonneg (t := Icc 1 m) ?_ (fun n _ _ ↦ by positivity)).trans ?_
  · intro j hj
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hj
    exact mem_Icc.mpr ⟨(mem_filter.mp hn).2, hd n (mem_filter.mp hn).1⟩
  · simpa only [harmonic_eq_sum_Icc (n := m), Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log m

end TauCeti
