/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
import TauCeti.RingTheory.Polynomial.Chebyshev.Order

/-!
# The Coxeter matrix of an integer matrix

Given an integer matrix `A : Matrix I I ℤ`, `Matrix.cartanCoxeterMatrix A` constructs the
associated `CoxeterMatrix I` by Kac's rule: `1` on the diagonal, `coxeterOrder (A i j * A j i)`
(`2, 3, 4, 6` for `A i j * A j i = 0, 1, 2, 3`) off the diagonal whenever `A i j * A j i ≤ 3`,
and `0` (Mathlib's encoding of `∞`) otherwise. Unlike `TauCeti.coxeterMatrixOfCartanMatrix`, which
assumes all off-diagonal Cartan products lie in `{0, 1, 2, 3}`, this construction works for
arbitrary generalized Cartan matrices (including affine and indefinite types where
`3 < A i j * A j i`) and agrees with `TauCeti.coxeterMatrixOfCartanMatrix` on finite-type
products.

This file also exports the rank-two Chebyshev nonnegativity inequalities attached to an integer
`c : ℤ` and its Coxeter order `coxeterOrder c`: over any ordered commutative ring `R`, the
rescaled Chebyshev evaluations `(Polynomial.Chebyshev.S R k).eval ((c : R) - 2)` and their
consecutive sums are nonnegative below the sharp `coxeterOrder c` threshold (and for all `k : ℕ`
when `3 < c`).

## Main definitions

* `Matrix.cartanCoxeterMatrix`: the `CoxeterMatrix I` read off an integer matrix `A`.

## Main results

* `Matrix.cartanCoxeterMatrix_eq_zero_iff_not_mem`, `Matrix.cartanCoxeterMatrix_eq_zero_iff`,
  `Matrix.cartanCoxeterMatrix_eq_two_iff`: characterization of infinite (`0`) and commuting (`2`)
  entries of `A.cartanCoxeterMatrix`.
* `Matrix.cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix`: agreement with
  `TauCeti.coxeterMatrixOfCartanMatrix` when all off-diagonal products lie in `{0, 1, 2, 3}`.
* `TauCeti.chebyshevS_eval_sub_two_nonneg`, `TauCeti.chebyshevS_sub_one_eval_sub_two_nonneg`,
  `TauCeti.chebyshevS_add_sub_one_eval_sub_two_nonneg`: nonnegativity of rescaled Chebyshev
  evaluations at `(c : R) - 2` below the rank-two Coxeter bound.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.13.
-/

public section

/-! ### The Coxeter matrix of an integer matrix -/

namespace Matrix

section CartanCoxeterMatrix

open TauCeti

variable {I : Type*} [DecidableEq I]

/-- **The Coxeter matrix read off an integer matrix `A`.** On the diagonal its entries are `1`;
off the diagonal its `(i, j)` entry is `coxeterOrder (A i j * A j i)` (`2, 3, 4, 6` on
`0, 1, 2, 3`) when `A i j * A j i ≤ 3`, and `0` (Mathlib's encoding of `∞`) otherwise
(`A i j * A j i ∉ {0, 1, 2, 3}`). -/
def cartanCoxeterMatrix (A : Matrix I I ℤ) : CoxeterMatrix I where
  M := .of fun i j ↦
    if i = j then 1
    else if A i j * A j i ≤ 3 then coxeterOrder (A i j * A j i) else 0
  isSymm := by
    ext i j
    simp only [transpose_apply, of_apply, eq_comm (a := j), mul_comm (A j i)]
  diagonal i := by simp
  off_diagonal i j hij := by
    simp only [of_apply, hij, ↓reduceIte]
    split_ifs with hle
    · by_cases hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)
      · have := two_le_coxeterOrder hmem
        omega
      · have hnot : A i j * A j i ∉ ({0, 1, 2, 3, 4} : Set ℤ) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
          omega
        rw [coxeterOrder_eq_zero_iff.mpr hnot]
        exact Nat.zero_ne_one
    · exact Nat.zero_ne_one

theorem cartanCoxeterMatrix_apply (A : Matrix I I ℤ) (i j : I) :
    A.cartanCoxeterMatrix i j =
      if i = j then 1
      else if A i j * A j i ≤ 3 then coxeterOrder (A i j * A j i) else 0 := (rfl)

theorem cartanCoxeterMatrix_of_ne_of_le {A : Matrix I I ℤ} {i j : I} (hij : i ≠ j)
    (h : A i j * A j i ≤ 3) :
    A.cartanCoxeterMatrix i j = coxeterOrder (A i j * A j i) := by
  simp [cartanCoxeterMatrix_apply, hij, h]

theorem cartanCoxeterMatrix_of_ne_of_lt {A : Matrix I I ℤ} {i j : I} (hij : i ≠ j)
    (h : 3 < A i j * A j i) :
    A.cartanCoxeterMatrix i j = 0 := by
  simp [cartanCoxeterMatrix_apply, hij, not_le.mpr h]

/-- Off the diagonal, the Coxeter entry vanishes (representing `∞`) exactly when the Cartan
product does not lie in `{0, 1, 2, 3}`. -/
theorem cartanCoxeterMatrix_eq_zero_iff_not_mem {A : Matrix I I ℤ} {i j : I} (hij : i ≠ j) :
    A.cartanCoxeterMatrix i j = 0 ↔ A i j * A j i ∉ ({0, 1, 2, 3} : Set ℤ) := by
  rcases le_or_gt (A i j * A j i) 3 with hle | hlt
  · rw [cartanCoxeterMatrix_of_ne_of_le hij hle, coxeterOrder_eq_zero_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rw [cartanCoxeterMatrix_of_ne_of_lt hij hlt]
    simp only [true_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

/-- When `0 ≤ A i j * A j i` and `i ≠ j`, the Coxeter entry vanishes (representing `∞`) exactly
when the Cartan product exceeds `3`. -/
theorem cartanCoxeterMatrix_eq_zero_iff {A : Matrix I I ℤ} {i j : I} (hij : i ≠ j)
    (hnonneg : 0 ≤ A i j * A j i) :
    A.cartanCoxeterMatrix i j = 0 ↔ 3 < A i j * A j i := by
  rw [cartanCoxeterMatrix_eq_zero_iff_not_mem hij]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- When `A i i ≠ 0` and `A j i = 0 → A i j = 0`, the Coxeter entry at `(i, j)` is `2` exactly
when `A i j = 0`. -/
theorem cartanCoxeterMatrix_eq_two_iff {A : Matrix I I ℤ} {i j : I}
    (hdiag : A i i ≠ 0) (hzero : A j i = 0 → A i j = 0) :
    A.cartanCoxeterMatrix i j = 2 ↔ A i j = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hdiag]
  · rcases le_or_gt (A i j * A j i) 3 with hle | hlt
    · rw [cartanCoxeterMatrix_of_ne_of_le hij hle, coxeterOrder_eq_two_iff, mul_eq_zero]
      exact or_iff_left_iff_imp.mpr hzero
    · rw [cartanCoxeterMatrix_of_ne_of_lt hij hlt]
      refine ⟨by omega, fun h₀ ↦ absurd ?_ (not_le.mpr hlt)⟩
      simp [h₀]

/-- When all off-diagonal Cartan products lie in `{0, 1, 2, 3}`, `Matrix.cartanCoxeterMatrix`
agrees with `TauCeti.coxeterMatrixOfCartanMatrix`. -/
theorem cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix (A : Matrix I I ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) :
    A.cartanCoxeterMatrix = coxeterMatrixOfCartanMatrix A hdiag hmem := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have hle : A i j * A j i ≤ 3 := by
      have := hmem i j hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      omega
    rw [cartanCoxeterMatrix_of_ne_of_le hij hle, coxeterMatrixOfCartanMatrix_apply]

end CartanCoxeterMatrix

end Matrix

/-! ### Rank-two Chebyshev nonnegativity below the Coxeter bound -/

namespace TauCeti

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
