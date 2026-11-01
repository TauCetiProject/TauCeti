/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
import TauCeti.Data.Int.Progression

/-!
# Positive odd upper-left entries by translation

A matrix in `SL₂(ℤ)` with positive lower-left entry can be translated by a nonnegative multiple
of any natural divisor of that entry to have positive odd upper-left entry. The determinant
equation ensures that an even translation step already has odd initial entry.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- If `m` divides the positive lower-left entry of `A`, a nonnegative multiple of `m`
translates its upper-left entry to a positive odd integer. -/
theorem exists_pos_odd_T_zpow_mul (A : SL(2, ℤ)) {m : ℕ}
    (hmc : (m : ℤ) ∣ A 1 0) (hc : 0 < A 1 0) :
    ∃ j : ℕ, 0 < (T ^ ((j : ℤ) * m) * A) 0 0 ∧
      Odd ((T ^ ((j : ℤ) * m) * A) 0 0) := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun hm ↦ hc.ne' (by simpa [hm] using hmc)
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [det_fin_two] using A.det_coe
  have hodd : Odd (A 0 0) ∨ Odd ((m : ℤ) * A 1 0) := by
    by_cases ha : Odd (A 0 0)
    · exact Or.inl ha
    · right
      have hcodd : Odd (A 1 0) := by
        by_contra hn
        have heven := ((Int.not_odd_iff_even.mp ha).mul_right (A 1 1)).sub
          ((Int.not_odd_iff_even.mp hn).mul_left (A 0 1))
        rw [hdet] at heven
        exact Int.not_even_one heven
      have hmodd : Odd (m : ℤ) := by
        obtain ⟨t, ht⟩ := hmc
        rw [ht] at hcodd
        exact (Int.odd_mul.mp hcodd).1
      exact hmodd.mul hcodd
  obtain ⟨j, hj, hjodd⟩ := Int.exists_nat_add_mul_pos_odd (A 0 0)
    (mul_pos (Int.natCast_pos.mpr hm) hc) hodd
  refine ⟨j, ?_⟩
  simpa [coe_mul, coe_T_zpow, mul_apply, Fin.sum_univ_two, mul_assoc] using And.intro hj hjodd

end Matrix.SpecialLinearGroup
