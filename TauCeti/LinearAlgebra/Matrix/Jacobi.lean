/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import TauCeti.LinearAlgebra.Matrix.CornerMinor

/-!
# Tridiagonal Jacobi matrices: general recurrences, symmetric forms, and Krylov determinants

A truncated tridiagonal (Jacobi) matrix `TauCeti.jacobiMatrix a b c n` of size `n × n` over a type
with zero `R` has diagonal entries `b₀, …, b_{n-1}`, superdiagonal entries `a₀, …, a_{n-2}`, and
subdiagonal entries `c₁, …, c_{n-1}`. Over a commutative ring its determinants satisfy the
three-term continuant recurrence (`TauCeti.det_jacobiMatrix_add_two`); for the characteristic
polynomial identity connecting `jacobiMatrix` and `symmJacobiMatrix` to orthogonal polynomials, see
`TauCeti.RingTheory.Polynomial.ThreeTermRecurrence`.

An extensional `(n + 1) × (n + 1)` symmetric Jacobi matrix `TauCeti.symmJacobiMatrix a b` is
determined without free tail coordinates by its diagonal `a : Fin (n + 1) → R` and its subdiagonal
(and superdiagonal) `b : Fin n → R`, and coincides with `jacobiMatrix` on zero-extended sequences
(`TauCeti.symmJacobiMatrix_eq_jacobiMatrix`). Over a semiring, its powers propagate bandwidth one
step per exponent, with band-edge entries given over a commutative semiring by products of
consecutive entries of `b`. In particular, the Krylov matrix formed by the first-column vectors
`(J ^ m) · 0` is upper triangular with determinant `∏ j : Fin n, b j ^ (n - j.val)`. Over any
semiring without zero divisors, every nonzero eigenvector of a symmetric Jacobi matrix with nonzero
subdiagonal entries has nonzero first coordinate.

## Main definitions

* `TauCeti.jacobiMatrix`: the `n × n` tridiagonal matrix with superdiagonal `a`, diagonal `b`, and
  subdiagonal `c` indexed by `ℕ → R`.
* `TauCeti.symmJacobiMatrix`: the symmetric tridiagonal `(n + 1) × (n + 1)` matrix with diagonal
  `a : Fin (n + 1) → R` and subdiagonal `b : Fin n → R`.
* `TauCeti.jacobiKrylovMatrix`: the `(n + 1) × (n + 1)` Krylov matrix with `(i, m)` entry
  `(symmJacobiMatrix a b ^ m.val) i 0`.

## Main results

* `TauCeti.isSymm_jacobiMatrix_iff`, `TauCeti.submatrix_castSucc_jacobiMatrix`, and
  `TauCeti.det_jacobiMatrix_add_two`: symmetry criterion, principal corner submatrix, and
  three-term continuant determinant recurrence for `jacobiMatrix`.
* `TauCeti.symmJacobiMatrix_eq_jacobiMatrix`: bridge expressing `symmJacobiMatrix a b` as a
  special case of `jacobiMatrix`.
* `TauCeti.symmJacobiMatrix_inj` and `TauCeti.symmJacobiMatrix_map`: injectivity in `(a, b)` and
  compatibility with zero-preserving maps.
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
* M. E. H. Ismail, *Classical and Quantum Orthogonal Polynomials in One Variable*, Cambridge
  University Press (2005), §2.2.
* *NIST Digital Library of Mathematical Functions*, §18.2, equation 18.2.18.
-/

public section

open Matrix Finset

namespace TauCeti

/-! ### General tridiagonal Jacobi matrices -/

section General

variable {R S : Type*} [Zero R]

/-- The truncated Jacobi (tridiagonal) matrix `J_n` with diagonal `b₀, …, b_{n-1}`, entries `a_i`
at `(i, i + 1)` above the diagonal and `c_i` at `(i, i - 1)` below it (DLMF 18.2.18). -/
def jacobiMatrix (a b c : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j ↦
    if (j : ℕ) = i then b i else if (j : ℕ) = i + 1 then a i else if (i : ℕ) = j + 1 then c i
    else 0

variable (a b c : ℕ → R)

/-- Unified entrywise formula for `jacobiMatrix a b c n`. -/
theorem jacobiMatrix_apply {n : ℕ} (i j : Fin n) :
    jacobiMatrix a b c n i j =
      if (j : ℕ) = i then b i else if (j : ℕ) = i + 1 then a i else if (i : ℕ) = j + 1 then c i
      else 0 :=
  (rfl)

/-- Congruence for `jacobiMatrix a b c n` from agreement on the active index ranges. -/
theorem jacobiMatrix_congr {a₁ a₂ b₁ b₂ c₁ c₂ : ℕ → R} {n : ℕ}
    (ha : ∀ k, k + 1 < n → a₁ k = a₂ k) (hb : ∀ k, k < n → b₁ k = b₂ k)
    (hc : ∀ k, 0 < k → k < n → c₁ k = c₂ k) :
    jacobiMatrix a₁ b₁ c₁ n = jacobiMatrix a₂ b₂ c₂ n := by
  ext i j
  simp only [jacobiMatrix_apply]
  split_ifs with h1 h2 h3
  · exact hb i i.isLt
  · exact ha i (h2 ▸ j.isLt)
  · exact hc i (by omega) i.isLt
  · rfl

/-- The `(i, i)` diagonal entry of `jacobiMatrix a b c n` is `b i`. -/
@[simp]
theorem jacobiMatrix_apply_self {n : ℕ} (i : Fin n) : jacobiMatrix a b c n i i = b i := by
  simp [jacobiMatrix_apply]

/-- The entries `a_i` above the diagonal of a Jacobi matrix. -/
theorem jacobiMatrix_apply_superdiag {n : ℕ} {i j : Fin n} (h : (j : ℕ) = i + 1) :
    jacobiMatrix a b c n i j = a i := by
  simp [jacobiMatrix_apply, h]

/-- The entries `c_i` below the diagonal of a Jacobi matrix. -/
theorem jacobiMatrix_apply_subdiag {n : ℕ} {i j : Fin n} (h : (i : ℕ) = j + 1) :
    jacobiMatrix a b c n i j = c i := by
  simp only [jacobiMatrix_apply]
  split_ifs <;> first | rfl | omega

/-- A Jacobi matrix vanishes off the three central diagonals. -/
theorem jacobiMatrix_apply_eq_zero {n : ℕ} {i j : Fin n} (h : (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) :
    jacobiMatrix a b c n i j = 0 := by
  simp only [jacobiMatrix_apply]
  split_ifs <;> first | rfl | omega

/-- Jacobi matrices commute with zero-preserving maps applied to their entries. -/
@[simp]
theorem jacobiMatrix_map [Zero S] {f : R → S} (hf : f 0 = 0) (n : ℕ) :
    (jacobiMatrix a b c n).map f = jacobiMatrix (f ∘ a) (f ∘ b) (f ∘ c) n := by
  ext i j
  simp only [Matrix.map_apply, jacobiMatrix_apply, Function.comp_apply]
  split_ifs <;> simp [hf]

/-- A Jacobi matrix `J_n` is symmetric exactly when `c_k = a_{k-1}` for `1 ≤ k < n`. -/
theorem isSymm_jacobiMatrix_iff {n : ℕ} :
    (jacobiMatrix a b c n).IsSymm ↔ ∀ k, 0 < k → k < n → c k = a (k - 1) := by
  refine ⟨fun h k hk hkn ↦ ?_, fun h ↦ Matrix.IsSymm.ext fun i j ↦ ?_⟩
  · have := h.apply (⟨k - 1, by omega⟩ : Fin n) ⟨k, hkn⟩
    rwa [jacobiMatrix_apply_subdiag _ _ _ (by simp only; omega),
      jacobiMatrix_apply_superdiag _ _ _ (by simp only; omega)] at this
  · obtain h₁ | h₁ | h₁ | h₁ : (i : ℕ) = j ∨ (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 ∨
        ((i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) := by omega
    · rw [Fin.ext h₁]
    · rw [jacobiMatrix_apply_subdiag _ _ _ h₁, jacobiMatrix_apply_superdiag _ _ _ h₁,
        h _ (by omega) j.isLt, h₁, Nat.add_sub_cancel]
    · rw [jacobiMatrix_apply_superdiag _ _ _ h₁, jacobiMatrix_apply_subdiag _ _ _ h₁,
        h _ (by omega) i.isLt, h₁, Nat.add_sub_cancel]
    · rw [jacobiMatrix_apply_eq_zero _ _ _ h₁.symm, jacobiMatrix_apply_eq_zero _ _ _ h₁]

/-- The leading principal `n × n` submatrix of `J_{n+1}` is `J_n`. -/
@[simp]
theorem submatrix_castSucc_jacobiMatrix (n : ℕ) :
    (jacobiMatrix a b c (n + 1)).submatrix Fin.castSucc Fin.castSucc = jacobiMatrix a b c n := by
  ext i j
  simp [jacobiMatrix_apply]

end General

section GeneralTraceDet

/-- The trace of a Jacobi matrix is the sum of its diagonal entries. -/
@[simp]
theorem trace_jacobiMatrix {R : Type*} [AddCommMonoid R] (a b c : ℕ → R) (n : ℕ) :
    (jacobiMatrix a b c n).trace = ∑ i : Fin n, b i := by
  simp [Matrix.trace, Matrix.diag]

section CommRing

variable {R : Type*} [CommRing R] (a b c : ℕ → R)

/-- The minor of `J_{n+2}` obtained by deleting the last row and column `n` is `a_n det J_n`. -/
private theorem det_submatrix_jacobiMatrix (n : ℕ) :
    ((jacobiMatrix a b c (n + 2)).submatrix Fin.castSucc
      (Fin.last n).castSucc.succAbove).det = a n * (jacobiMatrix a b c n).det := by
  have hcol : (Fin.last n).castSucc.succAbove (Fin.last n) = Fin.last (n + 1) := by
    rw [Fin.succAbove_castSucc_self, Fin.succ_last]
  have hminor : (Fin.last n).castSucc.succAbove ∘ Fin.castSucc = Fin.castSucc ∘ Fin.castSucc :=
    funext fun k ↦ Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last k)
  -- Expand along the last column, whose only nonzero entry is the corner `a_n`.
  rw [Matrix.det_eq_mul_det_submatrix_castSucc_of_col _ fun i hi ↦ by
      rw [Matrix.submatrix_apply, hcol, jacobiMatrix_apply_eq_zero _ _ _ (Or.inl (by
        simp only [Fin.val_castSucc, Fin.val_last]; exact Nat.succ_lt_succ (Fin.val_lt_last hi)))],
    Matrix.submatrix_apply, hcol, jacobiMatrix_apply_superdiag _ _ _ (by simp),
    Matrix.submatrix_submatrix, hminor, ← Matrix.submatrix_submatrix,
    submatrix_castSucc_jacobiMatrix, submatrix_castSucc_jacobiMatrix, Fin.val_castSucc,
    Fin.val_last]

/-- **The continuant recurrence of tridiagonal determinants**:
`det J_{n+2} = b_{n+1} det J_{n+1} - a_n c_{n+1} det J_n`. -/
theorem det_jacobiMatrix_add_two (n : ℕ) :
    (jacobiMatrix a b c (n + 2)).det =
      b (n + 1) * (jacobiMatrix a b c (n + 1)).det -
        a n * c (n + 1) * (jacobiMatrix a b c n).det := by
  have hrow (j : Fin n) : jacobiMatrix a b c (n + 2) (Fin.last (n + 1)) j.castSucc.castSucc = 0 :=
    jacobiMatrix_apply_eq_zero _ _ _ (Or.inr (by simp only [Fin.val_castSucc, Fin.val_last]; omega))
  -- Expand along the last row: only the entries `c_{n+1}` and `b_{n+1}` survive.
  rw [Matrix.det_succ_row _ (Fin.last (n + 1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hrow, mul_zero, zero_mul, sum_const_zero, zero_add]
  rw [jacobiMatrix_apply_subdiag _ _ _ (by simp), jacobiMatrix_apply_self, Fin.succAbove_last,
    det_submatrix_jacobiMatrix, submatrix_castSucc_jacobiMatrix, Fin.val_last, Fin.val_castSucc,
    Fin.val_last, Odd.neg_one_pow ⟨n, by ring⟩, Even.neg_one_pow ⟨n + 1, rfl⟩]
  ring

end CommRing

end GeneralTraceDet

/-! ### Symmetric `(n + 1) × (n + 1)` Jacobi matrices and entrywise properties -/

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

/-- Bridge expressing `symmJacobiMatrix a b` as an instance of `jacobiMatrix` on zero-extended
sequences. -/
theorem symmJacobiMatrix_eq_jacobiMatrix (a : Fin (n + 1) → R) (b : Fin n → R) :
    symmJacobiMatrix a b =
      jacobiMatrix
        (fun k => if hk : k < n then b ⟨k, hk⟩ else 0)
        (fun k => if hk : k < n + 1 then a ⟨k, hk⟩ else 0)
        (fun k => if hk : k - 1 < n then b ⟨k - 1, hk⟩ else 0)
        (n + 1) := by
  ext i j
  simp only [symmJacobiMatrix, jacobiMatrix, of_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | (congr 1; ext; simp; omega)

/-- Every symmetric Jacobi matrix is symmetric. -/
@[simp]
theorem isSymm_symmJacobiMatrix (a : Fin (n + 1) → R) (b : Fin n → R) :
    (symmJacobiMatrix a b).IsSymm := by
  rw [symmJacobiMatrix_eq_jacobiMatrix]
  exact (isSymm_jacobiMatrix_iff _ _ _).mpr fun _ _ _ => rfl

/-- The transpose of a symmetric Jacobi matrix is itself. -/
@[simp]
theorem symmJacobiMatrix_transpose (a : Fin (n + 1) → R) (b : Fin n → R) :
    (symmJacobiMatrix a b)ᵀ = symmJacobiMatrix a b :=
  isSymm_symmJacobiMatrix a b

/-- Entrywise symmetry of `symmJacobiMatrix a b`. -/
theorem symmJacobiMatrix_apply_symm (a : Fin (n + 1) → R) (b : Fin n → R) (i j : Fin (n + 1)) :
    symmJacobiMatrix a b i j = symmJacobiMatrix a b j i :=
  (isSymm_symmJacobiMatrix a b).apply j i

/-- The `(i, i)` diagonal entry of `symmJacobiMatrix a b` is `a i`. -/
@[simp]
theorem symmJacobiMatrix_apply_self (a : Fin (n + 1) → R) (b : Fin n → R) (i : Fin (n + 1)) :
    symmJacobiMatrix a b i i = a i := by
  rw [symmJacobiMatrix_eq_jacobiMatrix, jacobiMatrix_apply_self, dite_eq_left i.isLt]

/-- The `(k, k + 1)` superdiagonal entry of `symmJacobiMatrix a b` is `b k`. -/
@[simp]
theorem symmJacobiMatrix_apply_castSucc_succ (a : Fin (n + 1) → R) (b : Fin n → R) (k : Fin n) :
    symmJacobiMatrix a b k.castSucc k.succ = b k := by
  rw [symmJacobiMatrix_eq_jacobiMatrix, jacobiMatrix_apply_superdiag _ _ _ (by simp)]
  simp [k.isLt]

/-- The `(k + 1, k)` subdiagonal entry of `symmJacobiMatrix a b` is `b k`. -/
@[simp]
theorem symmJacobiMatrix_apply_succ_castSucc (a : Fin (n + 1) → R) (b : Fin n → R) (k : Fin n) :
    symmJacobiMatrix a b k.succ k.castSucc = b k := by
  rw [symmJacobiMatrix_eq_jacobiMatrix, jacobiMatrix_apply_subdiag _ _ _ (by simp)]
  simp [k.isLt]

/-- Entries strictly below the subdiagonal vanish. -/
theorem symmJacobiMatrix_apply_of_add_one_lt_left (a : Fin (n + 1) → R) (b : Fin n → R)
    {i j : Fin (n + 1)} (h : j.val + 1 < i.val) : symmJacobiMatrix a b i j = 0 := by
  rw [symmJacobiMatrix_eq_jacobiMatrix]
  exact jacobiMatrix_apply_eq_zero _ _ _ (Or.inr h)

/-- Entries strictly above the superdiagonal vanish. -/
theorem symmJacobiMatrix_apply_of_add_one_lt_right (a : Fin (n + 1) → R) (b : Fin n → R)
    {i j : Fin (n + 1)} (h : i.val + 1 < j.val) : symmJacobiMatrix a b i j = 0 := by
  rw [symmJacobiMatrix_eq_jacobiMatrix]
  exact jacobiMatrix_apply_eq_zero _ _ _ (Or.inl h)

/-- The leading principal `(n + 1) × (n + 1)` submatrix of `symmJacobiMatrix a b` on
`Fin (n + 2)` restricts `a` and `b` along `Fin.castSucc`. -/
@[simp]
theorem submatrix_castSucc_symmJacobiMatrix (a : Fin (n + 2) → R) (b : Fin (n + 1) → R) :
    (symmJacobiMatrix a b).submatrix Fin.castSucc Fin.castSucc =
      symmJacobiMatrix (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) := by
  rw [symmJacobiMatrix_eq_jacobiMatrix, submatrix_castSucc_jacobiMatrix,
    symmJacobiMatrix_eq_jacobiMatrix]
  refine jacobiMatrix_congr (fun k hk => ?_) (fun k hk => ?_) (fun k hk0 hk => ?_)
  · have hk' : k < n := by omega
    have hk'' : k < n + 1 := by omega
    simp [hk', hk'', Fin.castSucc_mk]
  · have hk' : k < n + 2 := by omega
    simp [hk, hk', Fin.castSucc_mk]
  · have hk' : k - 1 < n := by omega
    have hk'' : k - 1 < n + 1 := by omega
    simp [hk', hk'', Fin.castSucc_mk]

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

/-- Symmetric Jacobi matrices commute with zero-preserving maps applied to their entries. -/
@[simp]
theorem symmJacobiMatrix_map {S : Type*} [Zero S] {f : R → S} (hf : f 0 = 0)
    (a : Fin (n + 1) → R) (b : Fin n → R) :
    (symmJacobiMatrix a b).map f = symmJacobiMatrix (f ∘ a) (f ∘ b) := by
  rw [symmJacobiMatrix_eq_jacobiMatrix, symmJacobiMatrix_eq_jacobiMatrix, jacobiMatrix_map _ _ _ hf]
  refine jacobiMatrix_congr (fun k _ => ?_) (fun k _ => ?_) (fun k _ _ => ?_) <;>
    simp [Function.comp_apply, apply_dite f, hf]

/-- Scaling the diagonal and subdiagonal vectors scales the symmetric Jacobi matrix. -/
@[simp]
theorem symmJacobiMatrix_smul {M : Type*} [SMulZeroClass M R] (c : M) (a : Fin (n + 1) → R)
    (b : Fin n → R) : symmJacobiMatrix (c • a) (c • b) = c • symmJacobiMatrix a b :=
  (symmJacobiMatrix_map (f := (c • ·)) (smul_zero c) a b).symm

end Entries

/-! ### Trace identities -/

section Trace

variable {R : Type*}

/-- The trace of a symmetric Jacobi matrix is the sum of its diagonal entries. -/
@[simp]
theorem trace_symmJacobiMatrix {n : ℕ} [AddCommMonoid R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    (symmJacobiMatrix a b).trace = ∑ i, a i := by
  rw [symmJacobiMatrix_eq_jacobiMatrix, trace_jacobiMatrix]
  exact Finset.sum_congr rfl fun i _ => dite_eq_left i.isLt

/-- The sum of squares of all entries of `symmJacobiMatrix a b` is
`∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2`. -/
private theorem sum_sq_symmJacobiMatrix_entries [Semiring R] :
    ∀ {n : ℕ} (a : Fin (n + 1) → R) (b : Fin n → R),
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), symmJacobiMatrix a b i j ^ 2) =
        ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2
  | 0, a, b => by
      simp
  | n + 1, a, b => by
      have hsub :
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), symmJacobiMatrix a b i.castSucc j.castSucc ^ 2) =
            ∑ i : Fin (n + 1), a i.castSucc ^ 2 + 2 * ∑ k : Fin n, b k.castSucc ^ 2 := by
        have hblock (i j : Fin (n + 1)) :
            symmJacobiMatrix a b i.castSucc j.castSucc =
              symmJacobiMatrix (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) i j := by
          rw [← submatrix_castSucc_symmJacobiMatrix, Matrix.submatrix_apply]
        simp_rw [hblock]
        exact sum_sq_symmJacobiMatrix_entries (a ∘ Fin.castSucc) (b ∘ Fin.castSucc)
      have hcol : ∑ i : Fin (n + 1), symmJacobiMatrix a b i.castSucc (Fin.last (n + 1)) ^ 2 =
          b (Fin.last n) ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        have h0 : ∑ k : Fin n, symmJacobiMatrix a b k.castSucc.castSucc (Fin.last (n + 1)) ^ 2 =
            0 :=
          Finset.sum_eq_zero fun k _ => by
            rw [symmJacobiMatrix_apply_of_add_one_lt_right a b
              (by simp only [Fin.val_castSucc, Fin.val_last]; omega), sq, zero_mul]
        rw [h0, zero_add, ← Fin.succ_last, symmJacobiMatrix_apply_castSucc_succ]
      have hrow : ∑ j : Fin (n + 1), symmJacobiMatrix a b (Fin.last (n + 1)) j.castSucc ^ 2 =
          b (Fin.last n) ^ 2 := by
        simp_rw [symmJacobiMatrix_apply_symm a b (Fin.last (n + 1))]
        exact hcol
      have hsplit :
          (∑ i : Fin (n + 2), ∑ j : Fin (n + 2), symmJacobiMatrix a b i j ^ 2) =
            (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), symmJacobiMatrix a b i.castSucc j.castSucc ^ 2) +
              (∑ i : Fin (n + 1), symmJacobiMatrix a b i.castSucc (Fin.last (n + 1)) ^ 2) +
              ((∑ j : Fin (n + 1), symmJacobiMatrix a b (Fin.last (n + 1)) j.castSucc ^ 2) +
                symmJacobiMatrix a b (Fin.last (n + 1)) (Fin.last (n + 1)) ^ 2) := by
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (f := fun j =>
          symmJacobiMatrix a b (Fin.last (n + 1)) j ^ 2)]
        congr 1
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_castSucc _
      rw [hsplit, hsub, hcol, hrow, symmJacobiMatrix_apply_self,
        Fin.sum_univ_castSucc (f := fun i => a i ^ 2),
        Fin.sum_univ_castSucc (f := fun k => b k ^ 2)]
      simp only [mul_add, two_mul, add_assoc, add_left_comm, add_comm]

/-- The trace of the square of a symmetric Jacobi matrix is `∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2`. -/
theorem trace_symmJacobiMatrix_sq {n : ℕ} [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    ((symmJacobiMatrix a b) ^ 2).trace = ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2 := by
  have hdiag (i : Fin (n + 1)) : ((symmJacobiMatrix a b) ^ 2) i i =
      ∑ j : Fin (n + 1), symmJacobiMatrix a b i j ^ 2 := by
    rw [sq, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [symmJacobiMatrix_apply_symm a b j i, sq]
  simp only [Matrix.trace, Matrix.diag_apply, hdiag]
  exact sum_sq_symmJacobiMatrix_entries a b

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
