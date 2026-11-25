/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Symmetric tridiagonal Jacobi matrices: algebraic structure and Krylov determinants

A symmetric tridiagonal matrix of size `(n + 1) × (n + 1)` over a type with zero `R` is determined
by its diagonal entries `a : Fin (n + 1) → R` and its subdiagonal (and superdiagonal) entries
`b : Fin n → R`. Over a semiring, its powers propagate bandwidth one step per exponent, with
band-edge entries given over a commutative semiring by products of consecutive entries of `b`. In
particular, the Krylov matrix formed by the first-column vectors `(J ^ m) · 0` is upper triangular
with determinant `∏ j : Fin n, b j ^ (n - j.val)`. Over any semiring without zero divisors, every
nonzero eigenvector of a symmetric Jacobi matrix with nonzero subdiagonal entries has nonzero first
coordinate.

For the general (not necessarily symmetric) three-sequence tridiagonal Jacobi matrix indexed by
`ℕ → R`, see `TauCeti.jacobiMatrix` in `TauCeti.RingTheory.Polynomial.ThreeTermRecurrence`.

## Main definitions

* `TauCeti.symmJacobiMatrix`: the symmetric tridiagonal `(n + 1) × (n + 1)` matrix with diagonal
  `a` and subdiagonal `b`.
* `TauCeti.jacobiKrylovMatrix`: the `(n + 1) × (n + 1)` Krylov matrix with `(i, m)` entry
  `(symmJacobiMatrix a b ^ m.val) i 0`.

## Main results

* `TauCeti.symmJacobiMatrix_inj`:
  `symmJacobiMatrix a₁ b₁ = symmJacobiMatrix a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂`.
* `TauCeti.trace_symmJacobiMatrix_sq`:
  `((symmJacobiMatrix a b) ^ 2).trace = ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2`.
* `TauCeti.symmJacobiMatrix_pow_apply_of_add_lt_left`,
  `TauCeti.symmJacobiMatrix_pow_apply_of_add_lt_right`,
  `TauCeti.symmJacobiMatrix_pow_apply_sub_left`, and
  `TauCeti.symmJacobiMatrix_pow_apply_sub_right`: bandwidth vanishing and band-edge product
  formulas for powers of `symmJacobiMatrix a b`.
* `TauCeti.isUpperTriangular_jacobiKrylovMatrix` and `TauCeti.det_jacobiKrylovMatrix`: the Jacobi
  Krylov matrix is upper triangular, with determinant `∏ j : Fin n, b j ^ (n - j.val)`.
* `TauCeti.eq_zero_of_mulVec_symmJacobiMatrix_eq_smul_of_apply_zero_eq_zero` and
  `TauCeti.apply_zero_ne_zero_of_mulVec_symmJacobiMatrix_eq_smul`: over a semiring without zero
  divisors, any nonzero eigenvector of a symmetric Jacobi matrix with nonzero subdiagonals has
  nonzero first entry.

## References

* I. Dumitriu, A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.5.1.
-/

public section

open Matrix Finset

namespace TauCeti

/-! ### Definition and entrywise properties -/

section Entries

variable {R : Type*} [Zero R] {n : ℕ}

/-- The symmetric tridiagonal `(n + 1) × (n + 1)` Jacobi matrix with diagonal entries `a` and
subdiagonal (and superdiagonal) entries `b`. -/
def symmJacobiMatrix (a : Fin (n + 1) → R) (b : Fin n → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j =>
    if i = j then a i
    else if h : j.val = i.val + 1 then b ⟨i.val, by omega⟩
    else if h' : i.val = j.val + 1 then b ⟨j.val, by omega⟩
    else 0

/-- Unified entrywise formula for `symmJacobiMatrix a b`. -/
theorem symmJacobiMatrix_apply (a : Fin (n + 1) → R) (b : Fin n → R) (i j : Fin (n + 1)) :
    symmJacobiMatrix a b i j =
      if i = j then a i
      else if h : j.val = i.val + 1 then b ⟨i.val, by omega⟩
      else if h' : i.val = j.val + 1 then b ⟨j.val, by omega⟩
      else 0 :=
  (rfl)

/-- The transpose of a symmetric Jacobi matrix is itself. -/
@[simp]
theorem symmJacobiMatrix_transpose (a : Fin (n + 1) → R) (b : Fin n → R) :
    (symmJacobiMatrix a b)ᵀ = symmJacobiMatrix a b := by
  ext i j
  simp only [transpose_apply, symmJacobiMatrix, of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    rw [ite_eq_right hji, ite_eq_right hij]
    by_cases h1 : i.val = j.val + 1
    · have h2 : ¬(j.val = i.val + 1) := by omega
      rw [dite_eq_left h1, dite_eq_right h2, dite_eq_left h1]
    · by_cases h2 : j.val = i.val + 1
      · rw [dite_eq_right h1, dite_eq_left h2, dite_eq_left h2]
      · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h2, dite_eq_right h1]

/-- Every symmetric Jacobi matrix is symmetric. -/
@[simp]
theorem isSymm_symmJacobiMatrix (a : Fin (n + 1) → R) (b : Fin n → R) :
    (symmJacobiMatrix a b).IsSymm :=
  symmJacobiMatrix_transpose a b

/-- Entrywise symmetry of `symmJacobiMatrix a b`. -/
theorem symmJacobiMatrix_apply_symm (a : Fin (n + 1) → R) (b : Fin n → R) (i j : Fin (n + 1)) :
    symmJacobiMatrix a b i j = symmJacobiMatrix a b j i :=
  (isSymm_symmJacobiMatrix a b).apply j i

/-- The `(i, i)` diagonal entry of `symmJacobiMatrix a b` is `a i`. -/
@[simp]
theorem symmJacobiMatrix_apply_self (a : Fin (n + 1) → R) (b : Fin n → R) (i : Fin (n + 1)) :
    symmJacobiMatrix a b i i = a i := by
  simp [symmJacobiMatrix]

/-- The `(k, k + 1)` superdiagonal entry of `symmJacobiMatrix a b` is `b k`. -/
@[simp]
theorem symmJacobiMatrix_apply_castSucc_succ (a : Fin (n + 1) → R) (b : Fin n → R) (k : Fin n) :
    symmJacobiMatrix a b k.castSucc k.succ = b k := by
  have hne : k.castSucc ≠ k.succ := Fin.ne_of_lt (Fin.castSucc_lt_succ (i := k))
  simp [symmJacobiMatrix, hne]

/-- The `(k + 1, k)` subdiagonal entry of `symmJacobiMatrix a b` is `b k`. -/
@[simp]
theorem symmJacobiMatrix_apply_succ_castSucc (a : Fin (n + 1) → R) (b : Fin n → R) (k : Fin n) :
    symmJacobiMatrix a b k.succ k.castSucc = b k := by
  rw [symmJacobiMatrix_apply_symm, symmJacobiMatrix_apply_castSucc_succ]

/-- Entries strictly below the subdiagonal vanish. -/
theorem symmJacobiMatrix_apply_of_add_one_lt_left (a : Fin (n + 1) → R) (b : Fin n → R)
    {i j : Fin (n + 1)} (h : j.val + 1 < i.val) : symmJacobiMatrix a b i j = 0 := by
  have h1 : i ≠ j := fun hij => by subst hij; omega
  have h2 : ¬(j.val = i.val + 1) := by omega
  have h3 : ¬(i.val = j.val + 1) := by omega
  rw [symmJacobiMatrix, of_apply, ite_eq_right h1, dite_eq_right h2, dite_eq_right h3]

/-- Entries strictly above the superdiagonal vanish. -/
theorem symmJacobiMatrix_apply_of_add_one_lt_right (a : Fin (n + 1) → R) (b : Fin n → R)
    {i j : Fin (n + 1)} (h : i.val + 1 < j.val) : symmJacobiMatrix a b i j = 0 := by
  rw [symmJacobiMatrix_apply_symm, symmJacobiMatrix_apply_of_add_one_lt_left a b h]

/-- Two symmetric Jacobi matrices are equal if and only if their diagonal and subdiagonal vectors
agree. -/
@[simp]
theorem symmJacobiMatrix_inj {a₁ a₂ : Fin (n + 1) → R} {b₁ b₂ : Fin n → R} :
    symmJacobiMatrix a₁ b₁ = symmJacobiMatrix a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine ⟨fun h => ⟨funext fun i => ?_, funext fun k => ?_⟩, fun ⟨ha, hb⟩ => by rw [ha, hb]⟩
  · simpa using congrFun (congrFun h i) i
  · simpa using congrFun (congrFun h k.castSucc) k.succ

/-- Over a type with zero and trivial star (such as `ℝ`), every symmetric Jacobi matrix is
Hermitian. -/
theorem isHermitian_symmJacobiMatrix [Star R] [TrivialStar R] (a : Fin (n + 1) → R)
    (b : Fin n → R) : (symmJacobiMatrix a b).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (isSymm_symmJacobiMatrix a b)

/-- Scaling the diagonal and subdiagonal vectors scales the symmetric Jacobi matrix. -/
@[simp]
theorem symmJacobiMatrix_smul {M : Type*} [SMulZeroClass M R] (c : M) (a : Fin (n + 1) → R)
    (b : Fin n → R) : symmJacobiMatrix (c • a) (c • b) = c • symmJacobiMatrix a b := by
  ext i j
  simp only [Matrix.smul_apply, symmJacobiMatrix, of_apply]
  by_cases hij : i = j
  · simp [hij]
  · rw [ite_eq_right hij, ite_eq_right hij]
    by_cases h1 : j.val = i.val + 1
    · simp [h1]
    · by_cases h2 : i.val = j.val + 1
      · rw [dite_eq_right h1, dite_eq_left h2, dite_eq_right h1, dite_eq_left h2, Pi.smul_apply]
      · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h1, dite_eq_right h2, smul_zero]

end Entries

/-! ### Trace identities -/

section Trace

variable {R : Type*} {n : ℕ}

/-- The trace of a symmetric Jacobi matrix is the sum of its diagonal entries. -/
@[simp]
theorem trace_symmJacobiMatrix [AddCommMonoid R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    (symmJacobiMatrix a b).trace = ∑ i, a i := by
  simp [Matrix.trace, Matrix.diag]

/-- Entrywise decomposition of the squared entries in column `i` of `symmJacobiMatrix a b`. -/
private theorem symmJacobiMatrix_col_sq_eq [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    (i j : Fin (n + 1)) :
    symmJacobiMatrix a b j i ^ 2 =
      (if j = i then a i ^ 2 else 0) +
      (if h : i.val < n then if j = ⟨i.val + 1, by omega⟩ then b ⟨i.val, h⟩ ^ 2 else 0 else 0) +
      (if h : 0 < i.val then
        if j = ⟨i.val - 1, by omega⟩ then b ⟨i.val - 1, by omega⟩ ^ 2 else 0 else 0) := by
  simp only [symmJacobiMatrix, of_apply]
  split_ifs <;>
    simp only [Fin.ext_iff] at * <;>
    first
    | omega
    | (simp only [add_zero]; congr 2; ext; omega)
    | (simp only [zero_add]; congr 2; ext; omega)
    | simp

/-- The sum of squared entries in column `i` of `symmJacobiMatrix a b`. -/
private theorem sum_sq_symmJacobiMatrix_col [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    (i : Fin (n + 1)) :
    ∑ j : Fin (n + 1), symmJacobiMatrix a b j i ^ 2 =
      a i ^ 2 + (if h : i.val < n then b ⟨i.val, h⟩ ^ 2 else 0) +
        (if h : 0 < i.val then b ⟨i.val - 1, by omega⟩ ^ 2 else 0) := by
  simp_rw [symmJacobiMatrix_col_sq_eq, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp
    · split_ifs <;> simp
  · split_ifs <;> simp

/-- The trace of the square of a symmetric Jacobi matrix is `∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2`. -/
theorem trace_symmJacobiMatrix_sq [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    ((symmJacobiMatrix a b) ^ 2).trace = ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2 := by
  have hdiag : ∀ i : Fin (n + 1), ((symmJacobiMatrix a b) ^ 2) i i =
      ∑ j : Fin (n + 1), symmJacobiMatrix a b j i ^ 2 := fun i => by
    rw [sq, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [symmJacobiMatrix_apply_symm a b i j, sq]
  simp only [Matrix.trace, Matrix.diag_apply, hdiag, sum_sq_symmJacobiMatrix_col,
    Finset.sum_add_distrib]
  have h1 : ∑ i : Fin (n + 1), (if h : i.val < n then b ⟨i.val, h⟩ ^ 2 else 0) =
      ∑ k : Fin n, b k ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    simp
  have h2 : ∑ i : Fin (n + 1), (if h : 0 < i.val then b ⟨i.val - 1, by omega⟩ ^ 2 else 0) =
      ∑ k : Fin n, b k ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp
  rw [h1, h2, add_assoc, ← two_mul]

end Trace

/-! ### Bandwidth of powers and the Jacobi Krylov matrix -/

section Krylov

variable {R : Type*} {n : ℕ}

/-- Entries of `symmJacobiMatrix a b ^ m` strictly more than `m` steps below the diagonal vanish. -/
theorem symmJacobiMatrix_pow_apply_of_add_lt_left [Semiring R] (a : Fin (n + 1) → R)
    (b : Fin n → R) :
    ∀ (m : ℕ) {i j : Fin (n + 1)}, j.val + m < i.val → (symmJacobiMatrix a b ^ m) i j = 0
  | 0, i, j, hij => by
      have hne : i ≠ j := fun h => by subst h; omega
      simp [hne]
  | m + 1, i, j, hij => by
      rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hkm : j.val + m < k.val
      · rw [symmJacobiMatrix_pow_apply_of_add_lt_left a b m hkm, mul_zero]
      · rw [symmJacobiMatrix_apply_of_add_one_lt_left a b (by omega), zero_mul]

/-- Entries of `symmJacobiMatrix a b ^ m` strictly more than `m` steps above the diagonal vanish. -/
theorem symmJacobiMatrix_pow_apply_of_add_lt_right [Semiring R] (a : Fin (n + 1) → R)
    (b : Fin n → R) :
    ∀ (m : ℕ) {i j : Fin (n + 1)}, i.val + m < j.val → (symmJacobiMatrix a b ^ m) i j = 0
  | 0, i, j, hij => by
      have hne : i ≠ j := fun h => by subst h; omega
      simp [hne]
  | m + 1, i, j, hij => by
      rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hkm : k.val + m < j.val
      · rw [symmJacobiMatrix_pow_apply_of_add_lt_right a b m hkm, mul_zero]
      · rw [symmJacobiMatrix_apply_of_add_one_lt_right a b (by omega), zero_mul]

/-- The `m`-th Krylov vector `(J ^ m) · 0` vanishes below row `m`. -/
theorem symmJacobiMatrix_pow_apply_zero_of_lt [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    (m : ℕ) {i : Fin (n + 1)} (hi : m < i.val) : (symmJacobiMatrix a b ^ m) i 0 = 0 :=
  symmJacobiMatrix_pow_apply_of_add_lt_left a b m (by simpa using hi)

/-- For `j ≤ i`, the `(i, j)` band-edge entry of `symmJacobiMatrix a b ^ (i - j)` is the product of
the subdiagonal entries `b k` with `j ≤ k < i`. -/
theorem symmJacobiMatrix_pow_apply_sub_left [CommSemiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    {i j : Fin (n + 1)} (h : j ≤ i) :
    (symmJacobiMatrix a b ^ (i.val - j.val)) i j =
      ∏ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val), b k := by
  suffices ∀ (d : ℕ) {i : Fin (n + 1)}, j ≤ i → i.val - j.val = d →
      (symmJacobiMatrix a b ^ d) i j =
        ∏ k ∈ Finset.univ.filter (fun k : Fin n => j.val ≤ k.val ∧ k.val < i.val), b k from
    this (i.val - j.val) h rfl
  intro d
  induction d with
  | zero =>
      intro i hji hd
      have hij : i = j := Fin.ext (by have := Fin.le_def.mp hji; omega)
      subst hij
      have hemp : Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val < i.val) = ∅ := by
        ext k; simp
      simp [hemp]
  | succ d ih =>
      intro i hji hd
      have : j.val ≤ i.val := Fin.le_def.mp hji
      let k₀ : Fin n := ⟨j.val + d, by omega⟩
      have hi_eq : i = k₀.succ := Fin.ext (by simp [k₀]; omega)
      rw [hi_eq, pow_succ', Matrix.mul_apply, Finset.sum_eq_single k₀.castSucc]
      · rw [symmJacobiMatrix_apply_succ_castSucc,
          ih (Fin.le_def.mpr (by simp [k₀])) (by simp [k₀])]
        have hfilt : Finset.univ.filter
            (fun k : Fin n => j.val ≤ k.val ∧ k.val < k₀.succ.val) =
            insert k₀ (Finset.univ.filter
              (fun k : Fin n => j.val ≤ k.val ∧ k.val < k₀.castSucc.val)) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Fin.ext_iff, k₀, Fin.val_succ, Fin.val_castSucc]
          omega
        have hk_not : k₀ ∉ Finset.univ.filter
            (fun k : Fin n => j.val ≤ k.val ∧ k.val < k₀.castSucc.val) := by
          simp [k₀]
        rw [hfilt, Finset.prod_insert hk_not]
      · intro l _ hlk
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hlk) with hlt | hgt
        · rw [symmJacobiMatrix_apply_of_add_one_lt_left a b (by simp [k₀] at hlt ⊢; omega),
            zero_mul]
        · rw [symmJacobiMatrix_pow_apply_of_add_lt_left a b d (by simp [k₀] at hgt; omega),
            mul_zero]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- For `i ≤ j`, the `(i, j)` band-edge entry of `symmJacobiMatrix a b ^ (j - i)` is the product of
the superdiagonal entries `b k` with `i ≤ k < j`. -/
theorem symmJacobiMatrix_pow_apply_sub_right [CommSemiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    (symmJacobiMatrix a b ^ (j.val - i.val)) i j =
      ∏ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val ∧ k.val < j.val), b k := by
  rw [← ((isSymm_symmJacobiMatrix a b).pow (j.val - i.val)).apply i j,
    symmJacobiMatrix_pow_apply_sub_left a b h]

/-- The leading entry `(J ^ i) i 0` of the `i`-th Krylov vector is `∏_{j < i} b j`. -/
theorem symmJacobiMatrix_pow_apply_self_zero [CommSemiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    (i : Fin (n + 1)) :
    (symmJacobiMatrix a b ^ i.val) i 0 =
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), b j := by
  simpa using symmJacobiMatrix_pow_apply_sub_left a b (Fin.zero_le i)

/-- The Krylov matrix of `symmJacobiMatrix a b` with `(i, m)` entry `(J ^ m) i 0`. -/
def jacobiKrylovMatrix [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i m => (symmJacobiMatrix a b ^ m.val) i 0

/-- The `(i, m)` entry of `jacobiKrylovMatrix a b` is `(symmJacobiMatrix a b ^ m.val) i 0`. -/
@[simp]
theorem jacobiKrylovMatrix_apply [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    (i m : Fin (n + 1)) :
    jacobiKrylovMatrix a b i m = (symmJacobiMatrix a b ^ m.val) i 0 :=
  (rfl)

/-- The Jacobi Krylov matrix is upper triangular. -/
theorem isUpperTriangular_jacobiKrylovMatrix [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    (jacobiKrylovMatrix a b).IsUpperTriangular := fun _ _ h =>
  symmJacobiMatrix_pow_apply_zero_of_lt a b _ h

/-- The determinant of the Jacobi Krylov matrix is `∏ j : Fin n, b j ^ (n - j.val)`. -/
theorem det_jacobiKrylovMatrix [CommRing R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    (jacobiKrylovMatrix a b).det = ∏ j : Fin n, b j ^ (n - j.val) := by
  rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_jacobiKrylovMatrix a b)]
  simp only [jacobiKrylovMatrix_apply, symmJacobiMatrix_pow_apply_self_zero]
  calc
    ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), b j
        = ∏ i : Fin (n + 1), ∏ j : Fin n, if j.val < i.val then b j else 1 := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Finset.prod_filter]
    _ = ∏ j : Fin n, ∏ i : Fin (n + 1), if j.val < i.val then b j else 1 := Finset.prod_comm
    _ = ∏ j : Fin n, b j ^ (n - j.val) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← Finset.prod_filter, Finset.prod_const]
          congr 1
          have hfilt : Finset.univ.filter (fun i : Fin (n + 1) => j.val < i.val) =
              Finset.Ioi j.castSucc := by
            ext i
            simp [Finset.mem_Ioi, Fin.lt_def]
          rw [hfilt, Fin.card_Ioi]
          simp

end Krylov

/-! ### Nonvanishing of the first coordinate of eigenvectors -/

section Eigenvector

variable {n : ℕ}

/-- Any eigenvector of a symmetric Jacobi matrix with nonzero subdiagonal entries whose first
coordinate vanishes is the zero vector. -/
theorem eq_zero_of_mulVec_symmJacobiMatrix_eq_smul_of_apply_zero_eq_zero {R : Type*}
    [NonUnitalNonAssocSemiring R] [NoZeroDivisors R]
    {a : Fin (n + 1) → R} {b : Fin n → R} (hb : ∀ k, b k ≠ 0) {μ : R}
    {v : Fin (n + 1) → R} (hv : symmJacobiMatrix a b *ᵥ v = μ • v) (h0 : v 0 = 0) :
    v = 0 := by
  ext i
  suffices ∀ m (hm : m < n + 1), v ⟨m, hm⟩ = 0 from this i.val i.isLt
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
      intro hm
      rcases m with _ | k
      · exact h0
      · have hk : k < n := by omega
        let k' : Fin n := ⟨k, hk⟩
        have hrow := congrFun hv k'.castSucc
        simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct] at hrow
        have hzero_k : v k'.castSucc = 0 := ih k (by omega) (by omega)
        rw [hzero_k, mul_zero] at hrow
        have hsum : ∑ j : Fin (n + 1), symmJacobiMatrix a b k'.castSucc j * v j =
            b k' * v k'.succ := by
          rw [Finset.sum_eq_single k'.succ]
          · rw [symmJacobiMatrix_apply_castSucc_succ]
          · intro j _ hjk
            by_cases hjle : j.val ≤ k
            · rw [ih j.val (by omega) j.isLt, mul_zero]
            · rw [symmJacobiMatrix_apply_of_add_one_lt_right a b (by
                have : j.val ≠ k + 1 := fun h => hjk (Fin.ext h)
                simp [k']; omega), zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum] at hrow
        have hsucc : v k'.succ = 0 := (mul_eq_zero.mp hrow).resolve_left (hb k')
        simpa [k'] using hsucc

/-- Every nonzero eigenvector of a symmetric Jacobi matrix with nonzero subdiagonal entries has
nonzero first coordinate. -/
theorem apply_zero_ne_zero_of_mulVec_symmJacobiMatrix_eq_smul {R : Type*}
    [NonUnitalNonAssocSemiring R] [NoZeroDivisors R]
    {a : Fin (n + 1) → R} {b : Fin n → R} (hb : ∀ k, b k ≠ 0) {μ : R}
    {v : Fin (n + 1) → R} (hv : symmJacobiMatrix a b *ᵥ v = μ • v) (hne : v ≠ 0) :
    v 0 ≠ 0 :=
  fun h0 => hne (eq_zero_of_mulVec_symmJacobiMatrix_eq_smul_of_apply_zero_eq_zero hb hv h0)

end Eigenvector

end TauCeti
