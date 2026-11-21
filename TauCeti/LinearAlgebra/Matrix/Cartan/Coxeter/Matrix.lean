/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
import TauCeti.RingTheory.Polynomial.Chebyshev.Growth

/-!
# Infinite entries of the Coxeter matrix of an integer matrix

For an integer matrix `A : Matrix I I ℤ`, the Coxeter matrix
`TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A` has entry `1` on the diagonal and, at two
distinct nodes, `TauCeti.coxeterOrder (A i j * A j i)` (`2, 3, 4, 6` for
`A i j * A j i = 0, 1, 2, 3`) when `A i j * A j i < 4`, and `0` (Mathlib's encoding of `∞`)
otherwise. This file characterizes the infinite entries off the diagonal: they are exactly the
pairs whose Cartan product lies outside `{0, 1, 2, 3}`, that is, for a nonnegative Cartan product,
the pairs with `4 ≤ A i j * A j i`.

This file also exports the rank-two Chebyshev nonnegativity inequalities attached to an integer
`c : ℤ` and its Coxeter order `coxeterOrder c`: over any ordered commutative ring `R`, the
rescaled Chebyshev evaluations `(Polynomial.Chebyshev.S R k).eval ((c : R) - 2)` and their
consecutive sums are nonnegative below the sharp `coxeterOrder c` threshold (and for all `k : ℕ`
when `3 < c`).

## Main results

* `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff_not_mem`,
  `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff`: characterization of the
  infinite (`0`) entries of `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A`.
* `TauCeti.chebyshevS_eval_sub_two_nonneg`, `TauCeti.chebyshevS_sub_one_eval_sub_two_nonneg`,
  `TauCeti.chebyshevS_add_sub_one_eval_sub_two_nonneg`: nonnegativity of rescaled Chebyshev
  evaluations at `(c : R) - 2` below the rank-two Coxeter bound.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.13.
-/

public section

namespace TauCeti

/-! ### Infinite entries of the Coxeter matrix of an integer matrix -/

section CoxeterMatrixEntries

variable {I : Type*} [DecidableEq I] (A : Matrix I I ℤ)

/-- Off the diagonal, the Coxeter entry vanishes (representing `∞`) exactly when the Cartan
product does not lie in `{0, 1, 2, 3}`. -/
theorem coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff_not_mem {i j : I} (hij : i ≠ j) :
    coxeterMatrixOfGeneralizedCartanMatrix A i j = 0 ↔
      A i j * A j i ∉ ({0, 1, 2, 3} : Set ℤ) := by
  rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne A hij]
  split_ifs with h4
  · rw [coxeterOrder_eq_zero_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · simp only [true_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

/-- When `0 ≤ A i j * A j i` and `i ≠ j`, the Coxeter entry vanishes (representing `∞`) exactly
when the Cartan product is at least `4`. -/
theorem coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff {i j : I} (hij : i ≠ j)
    (hnonneg : 0 ≤ A i j * A j i) :
    coxeterMatrixOfGeneralizedCartanMatrix A i j = 0 ↔ 4 ≤ A i j * A j i := by
  rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff_not_mem A hij]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

end CoxeterMatrixEntries

/-! ### Rank-two Chebyshev nonnegativity below the Coxeter bound -/

section ChebyshevCoxeter

open Polynomial.Chebyshev

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- For any integer `c : ℤ`, the rescaled Chebyshev evaluation `(S R k).eval ((c : R) - 2)` is
nonnegative whenever `2 * k + 1 < coxeterOrder c` for `c ≤ 3` (and for every `k : ℕ` when
`3 < c`). -/
theorem chebyshevS_eval_sub_two_nonneg {c : ℤ} {k : ℕ}
    (hk : c ≤ 3 → 2 * k + 1 < coxeterOrder c) :
    0 ≤ (S R k).eval ((c : R) - 2) := by
  rcases le_or_gt c 3 with hle | hgt
  · have hlt := hk hle
    have hne0 : coxeterOrder c ≠ 0 := by omega
    have hmem : c ∈ ({0, 1, 2, 3, 4} : Set ℤ) :=
      not_not.mp (mt coxeterOrder_eq_zero_iff.mpr hne0)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · rw [coxeterOrder_zero] at hlt
      have hk0 : k = 0 := by omega
      subst hk0
      simp [S_zero]
    · rw [coxeterOrder_one] at hlt
      have hk0 : k = 0 := by omega
      subst hk0
      simp [S_zero]
    · rw [coxeterOrder_two] at hlt
      have hk2 : k < 2 := by omega
      interval_cases k
      · simp [S_zero]
      · simp [S_one]
    · rw [coxeterOrder_three] at hlt
      have h3 : ((3 : ℤ) : R) - 2 = 1 := by norm_num
      rw [h3]
      have hk3 : k < 3 := by omega
      interval_cases k
      · simp [S_zero]
      · simp [S_one]
      · simp [S_two]
    · omega
  · have ht : (2 : R) ≤ (c : R) - 2 := by
      rw [← sub_nonneg]
      have h0 : (0 : R) ≤ ((c - 4 : ℤ) : R) := Int.cast_nonneg (by omega)
      simpa [sub_sub, show (2 : R) + 2 = 4 by norm_num] using h0
    exact le_trans zero_le_one (one_le_S_eval ht k)

/-- For any integer `c : ℤ`, the shifted rescaled Chebyshev evaluation
`(S R ((k : ℤ) - 1)).eval ((c : R) - 2)` is nonnegative whenever `2 * k ≤ coxeterOrder c` for
`c ≤ 3` (and for every `k : ℕ` when `3 < c`). -/
theorem chebyshevS_sub_one_eval_sub_two_nonneg {c : ℤ} {k : ℕ}
    (hk : c ≤ 3 → 2 * k ≤ coxeterOrder c) :
    0 ≤ (S R ((k : ℤ) - 1)).eval ((c : R) - 2) := by
  cases k with
  | zero => simp [S_neg_one]
  | succ k =>
    have h := chebyshevS_eval_sub_two_nonneg (R := R) (c := c) (k := k) fun hle ↦ by
      have := hk hle
      omega
    simpa [Nat.cast_add, add_sub_cancel_right] using h

/-- For any integer `c : ℤ`, the consecutive rescaled Chebyshev sum
`(S R k).eval ((c : R) - 2) + (S R ((k : ℤ) - 1)).eval ((c : R) - 2)` is nonnegative whenever
`2 * k < coxeterOrder c` for `c ≤ 3` (and for every `k : ℕ` when `3 < c`). -/
theorem chebyshevS_add_sub_one_eval_sub_two_nonneg {c : ℤ} {k : ℕ}
    (hk : c ≤ 3 → 2 * k < coxeterOrder c) :
    0 ≤ (S R k).eval ((c : R) - 2) + (S R ((k : ℤ) - 1)).eval ((c : R) - 2) := by
  rcases le_or_gt c 3 with hle | hgt
  · have hlt := hk hle
    have hne0 : coxeterOrder c ≠ 0 := by omega
    have hmem : c ∈ ({0, 1, 2, 3, 4} : Set ℤ) :=
      not_not.mp (mt coxeterOrder_eq_zero_iff.mpr hne0)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · rw [coxeterOrder_zero] at hlt
      have hk0 : k = 0 := by omega
      subst hk0
      simp [S_neg_one, S_zero]
    · rw [coxeterOrder_one] at hlt
      have h1 : ((1 : ℤ) : R) - 2 = -1 := by norm_num
      rw [h1]
      have hk2 : k < 2 := by omega
      interval_cases k
      · simp [S_neg_one, S_zero]
      · simp [S_zero, S_one]
    · rw [coxeterOrder_two] at hlt
      have hk2 : k < 2 := by omega
      interval_cases k
      · simp [S_neg_one, S_zero]
      · simp [S_zero, S_one]
    · rw [coxeterOrder_three] at hlt
      have h3 : ((3 : ℤ) : R) - 2 = 1 := by norm_num
      rw [h3]
      have hk3 : k < 3 := by omega
      interval_cases k
      · simp [S_neg_one, S_zero]
      · simp only [Nat.cast_one, sub_self, S_one, S_zero, Polynomial.eval_X, Polynomial.eval_one]
        exact add_nonneg zero_le_one zero_le_one
      · simp [S_one, S_two]
    · omega
  · have ht : (2 : R) ≤ (c : R) - 2 := by
      rw [← sub_nonneg]
      have h0 : (0 : R) ≤ ((c - 4 : ℤ) : R) := Int.cast_nonneg (by omega)
      simpa [sub_sub, show (2 : R) + 2 = 4 by norm_num] using h0
    exact add_nonneg (le_trans zero_le_one (one_le_S_eval ht k)) (nonneg_S_eval_sub_one ht k)

end ChebyshevCoxeter

end TauCeti
