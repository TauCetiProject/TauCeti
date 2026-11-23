/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import TauCeti.LinearAlgebra.Matrix.Cartan.Generalized
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
import TauCeti.RingTheory.Polynomial.Chebyshev.Growth

/-!
# Entries, symmetries, and standard values of the Coxeter matrix of an integer matrix

For an integer matrix `A : Matrix I I ℤ`, the Coxeter matrix
`TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A` has entry `1` on the diagonal and, at two
distinct nodes, `TauCeti.coxeterOrder (A i j * A j i)` (`2, 3, 4, 6` for
`A i j * A j i = 0, 1, 2, 3`) when `A i j * A j i < 4`, and `0` (Mathlib's encoding of `∞`)
otherwise. This file characterizes the infinite entries off the diagonal, proves invariance under
transposition and relabelling, specializes the entry characterizations to
`Matrix.IsGeneralizedCartan`, identifies `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix` on
Mathlib's `CartanMatrix.A`, `B`, `C`, `F₄`, `G₂` and on affine `A₁⁽¹⁾`, and exports the rank-two
Chebyshev nonnegativity inequalities below the `coxeterOrder c` threshold.

## Main results

* `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff_not_mem`,
  `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff`: characterization of the
  infinite (`0`) entries of `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A`.
* `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_transpose`,
  `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_submatrix_equiv`: invariance under transposition
  and index equivalence.
* `Matrix.IsGeneralizedCartan.coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff`,
  `Matrix.IsGeneralizedCartan.coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_two_iff`,
  `Matrix.IsGeneralizedCartan.coxeterMatrixOfGeneralizedCartanMatrix_mem_of_ne_of_lt_four`: entry
  characterizations for generalized Cartan matrices.
* `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_A`, `..._B`, `..._C`, `..._F₄`,
  `..._G₂`, and `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_two_neg_two_zero_one`: evaluation
  on standard finite Cartan families and affine `A₁⁽¹⁾`.
* `TauCeti.chebyshevS_eval_sub_two_nonneg`, `TauCeti.chebyshevS_sub_one_eval_sub_two_nonneg`,
  `TauCeti.chebyshevS_add_sub_one_eval_sub_two_nonneg`: nonnegativity of rescaled Chebyshev
  evaluations at `(c : R) - 2` below the rank-two Coxeter bound.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.13.
-/

public section

open scoped Matrix

namespace TauCeti

/-! ### Entries and symmetries of the Coxeter matrix of an integer matrix -/

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

/-- Transposing an integer matrix leaves its generalized Cartan Coxeter matrix unchanged. -/
@[simp]
theorem coxeterMatrixOfGeneralizedCartanMatrix_transpose :
    coxeterMatrixOfGeneralizedCartanMatrix Aᵀ = coxeterMatrixOfGeneralizedCartanMatrix A := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne Aᵀ hij,
      coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne A hij, Matrix.transpose_apply,
      Matrix.transpose_apply, mul_comm]

/-- Reindexing a square integer matrix along `e : J ≃ I` reindexes its Coxeter matrix along
`e.symm`. -/
theorem coxeterMatrixOfGeneralizedCartanMatrix_submatrix_equiv {J : Type*} [DecidableEq J]
    (e : J ≃ I) :
    coxeterMatrixOfGeneralizedCartanMatrix (A.submatrix e e) =
      (coxeterMatrixOfGeneralizedCartanMatrix A).reindex e.symm := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne _ hij, CoxeterMatrix.reindex_apply,
      Equiv.symm_symm, coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne A (e.injective.ne hij),
      Matrix.submatrix_apply, Matrix.submatrix_apply]

end CoxeterMatrixEntries

/-- The off-diagonal Coxeter entry of the affine `A₁⁽¹⁾` matrix `!![2, -2; -2, 2]` is `0`. -/
@[simp]
theorem coxeterMatrixOfGeneralizedCartanMatrix_two_neg_two_zero_one :
    coxeterMatrixOfGeneralizedCartanMatrix (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 :=
  coxeterMatrixOfGeneralizedCartanMatrix_apply_of_four_le _ (by decide) (by decide)

/-! ### Standard finite Cartan families -/

/-- `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix` on `CartanMatrix.A n` recovers Mathlib's
`CoxeterMatrix.A n`. -/
@[simp]
theorem coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_A (n : ℕ) :
    coxeterMatrixOfGeneralizedCartanMatrix (CartanMatrix.A n) = CoxeterMatrix.A n := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [CoxeterMatrix.A]
  · rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne _ hij]
    simp only [CoxeterMatrix.A, CartanMatrix.A, Matrix.of_apply, hij, hij.symm, ↓reduceIte]
    split_ifs <;> simp_all

/-- `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix` on `CartanMatrix.B n` recovers Mathlib's
`CoxeterMatrix.B n`. -/
@[simp]
theorem coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_B (n : ℕ) :
    coxeterMatrixOfGeneralizedCartanMatrix (CartanMatrix.B n) = CoxeterMatrix.B n := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [CoxeterMatrix.B]
  · have hi := i.isLt
    have hj := j.isLt
    rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne _ hij]
    simp only [CoxeterMatrix.B, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | norm_num

/-- `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix` on `CartanMatrix.C n` recovers Mathlib's
`CoxeterMatrix.B n`. -/
@[simp]
theorem coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_C (n : ℕ) :
    coxeterMatrixOfGeneralizedCartanMatrix (CartanMatrix.C n) = CoxeterMatrix.B n := by
  rw [← CartanMatrix.B_transpose, coxeterMatrixOfGeneralizedCartanMatrix_transpose,
    coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_B]

/-- `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix` on `CartanMatrix.F₄` recovers Mathlib's
`CoxeterMatrix.F₄`. -/
@[simp]
theorem coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_F₄ :
    coxeterMatrixOfGeneralizedCartanMatrix CartanMatrix.F₄ = CoxeterMatrix.F₄ := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [CoxeterMatrix.F₄]
  · rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne _ hij]
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.F₄, CartanMatrix.F₄] at hij ⊢

/-- `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix` on `CartanMatrix.G₂` recovers Mathlib's
`CoxeterMatrix.G₂`. -/
@[simp]
theorem coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_G₂ :
    coxeterMatrixOfGeneralizedCartanMatrix CartanMatrix.G₂ = CoxeterMatrix.G₂ := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [CoxeterMatrix.G₂]
  · rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_ne _ hij]
    fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.G₂, CartanMatrix.G₂] at hij ⊢

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

namespace Matrix.IsGeneralizedCartan

variable {I : Type*} [DecidableEq I] {A : Matrix I I ℤ} (hA : A.IsGeneralizedCartan)
include hA

/-- For a generalized Cartan matrix `A`, the `(i, j)`-entry of its Coxeter matrix vanishes
(representing `∞`) if and only if `i ≠ j` and `4 ≤ A i j * A j i`. -/
theorem coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff (i j : I) :
    TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A i j = 0 ↔ i ≠ j ∧ 4 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simpa [hij] using
      TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff A hij (hA.mul_nonneg i j)

/-- For a generalized Cartan matrix `A`, the `(i, j)`-entry of its Coxeter matrix is `2` if and
only if `A i j = 0`. -/
theorem coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_two_iff (i j : I) :
    TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A i j = 2 ↔ A i j = 0 :=
  TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_two_iff A
    (by rw [hA.diag i]; decide) (hA.zero_comm j i).mp

/-- Off the diagonal, any entry of `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A` with
`A i j * A j i < 4` belongs to `{2, 3, 4, 6}`. -/
theorem coxeterMatrixOfGeneralizedCartanMatrix_mem_of_ne_of_lt_four {i j : I} (hij : i ≠ j)
    (hlt : A i j * A j i < 4) :
    TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A i j ∈ ({2, 3, 4, 6} : Set ℕ) := by
  rw [TauCeti.coxeterMatrixOfGeneralizedCartanMatrix_apply_of_lt_four A hij hlt]
  have h0 := hA.mul_nonneg i j
  exact TauCeti.coxeterOrder_mem (TauCeti.mem_zero_one_two_three_iff.mpr ⟨h0, by omega⟩)

end Matrix.IsGeneralizedCartan
