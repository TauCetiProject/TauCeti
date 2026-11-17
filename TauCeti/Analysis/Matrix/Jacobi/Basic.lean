/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Vandermonde
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous

/-!
# Symmetric tridiagonal Jacobi matrices and their spectral data

A symmetric tridiagonal matrix of size `(n + 1) × (n + 1)` is determined by its diagonal entries
`a : Fin (n + 1) → R` and its subdiagonal entries `b : Fin n → R`. When `R = ℝ` and every
subdiagonal entry is nonzero, `TauCeti.jacobiMatrix a b` is a classical Jacobi matrix: all `n + 1`
eigenvalues are simple, so the decreasingly ordered spectrum `TauCeti.jacobiEigenvalues a b` is
strictly antitone, and every eigenvector has nonzero first coordinate.

The spectral weights `q k = (v k 0) ^ 2` — the squared first coordinates of unit eigenvectors for
the ordered eigenvalues `λ k` — are independent of eigenvector sign choices and sum to `1`. We
define `TauCeti.jacobiSpectralWeight` directly by the Lagrange interpolation formula in the
matrix and its ordered eigenvalues, which makes it canonically defined, globally measurable, and
continuous on the open locus of nonvanishing subdiagonals, while agreeing with `(v k 0) ^ 2`
there.

## Main definitions

* `TauCeti.jacobiMatrix`: the symmetric tridiagonal matrix with diagonal `a` and subdiagonal `b`.
* `TauCeti.krylovMatrix`: the `(n + 1) × (n + 1)` matrix with columns `(J ^ m) · 0`.
* `TauCeti.jacobiEigenvalues`: the decreasingly ordered eigenvalues of a real Jacobi matrix,
  indexed directly by `Fin (n + 1)`.
* `TauCeti.jacobiSpectralWeight`: the canonical spectral weights of a real Jacobi matrix.

## Main results

* `TauCeti.trace_jacobiMatrix_sq`:
  `((jacobiMatrix a b) ^ 2).trace = ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2`.
* `TauCeti.det_krylovMatrix`: the Krylov matrix is upper triangular with determinant
  `∏ j : Fin n, b j ^ (n - j.val)`.
* `TauCeti.strictAnti_jacobiEigenvalues`: a real Jacobi matrix with nonzero subdiagonal entries
  has strictly decreasing eigenvalues.
* `TauCeti.jacobiSpectralWeight_eq_sq_eigenvector`: on the nonvanishing-subdiagonal locus, the
  Lagrange spectral weight equals `(v 0) ^ 2` for any unit eigenvector `v` of that eigenvalue.
* `TauCeti.jacobiMatrix_pow_zero_zero`: moment identity
  `((jacobiMatrix a b) ^ r) 0 0 = ∑ k, jacobiSpectralWeight a b k * jacobiEigenvalues a b k ^ r`.
* `TauCeti.prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_vandermonde`: the Dumitriu–Edelman
  Vandermonde–weight identity linking `∏ j, b j ^ (n - j)` to the spectral weights and the
  Vandermonde product of the eigenvalues.

## References

* I. Dumitriu, A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.5.1.
-/

public section

noncomputable section

open Matrix Finset Polynomial
open scoped RealInnerProductSpace

namespace TauCeti

/-! ### Definition and entrywise properties -/

section Entries

variable {R : Type*} [Zero R] {n : ℕ}

/-- The symmetric tridiagonal `(n + 1) × (n + 1)` Jacobi matrix with diagonal entries `a` and
subdiagonal (and superdiagonal) entries `b`. -/
def jacobiMatrix (a : Fin (n + 1) → R) (b : Fin n → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j =>
    if i = j then a i
    else if h : j.val = i.val + 1 then b ⟨i.val, by omega⟩
    else if h' : i.val = j.val + 1 then b ⟨j.val, by omega⟩
    else 0

/-- The `(i, i)` diagonal entry of `jacobiMatrix a b` is `a i`. -/
@[simp]
theorem jacobiMatrix_apply_self (a : Fin (n + 1) → R) (b : Fin n → R) (i : Fin (n + 1)) :
    jacobiMatrix a b i i = a i := by
  simp [jacobiMatrix]

/-- The `(k, k + 1)` superdiagonal entry of `jacobiMatrix a b` is `b k`. -/
@[simp]
theorem jacobiMatrix_apply_castSucc_succ (a : Fin (n + 1) → R) (b : Fin n → R) (k : Fin n) :
    jacobiMatrix a b k.castSucc k.succ = b k := by
  have hne : k.castSucc ≠ k.succ := Fin.ne_of_lt (Fin.castSucc_lt_succ (i := k))
  simp [jacobiMatrix, hne]

/-- The `(k + 1, k)` subdiagonal entry of `jacobiMatrix a b` is `b k`. -/
@[simp]
theorem jacobiMatrix_apply_succ_castSucc (a : Fin (n + 1) → R) (b : Fin n → R) (k : Fin n) :
    jacobiMatrix a b k.succ k.castSucc = b k := by
  have hne : k.succ ≠ k.castSucc := (Fin.ne_of_lt (Fin.castSucc_lt_succ (i := k))).symm
  have h1 : ¬(k.castSucc.val = k.succ.val + 1) := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  have h2 : k.succ.val = k.castSucc.val + 1 := by simp
  rw [jacobiMatrix, of_apply, ite_eq_right hne, dite_eq_right h1, dite_eq_left h2]
  rfl

/-- Entries strictly below the subdiagonal vanish. -/
theorem jacobiMatrix_apply_of_add_one_lt_left (a : Fin (n + 1) → R) (b : Fin n → R)
    {i j : Fin (n + 1)} (h : j.val + 1 < i.val) : jacobiMatrix a b i j = 0 := by
  have h1 : i ≠ j := fun hij => by subst hij; omega
  have h2 : ¬(j.val = i.val + 1) := by omega
  have h3 : ¬(i.val = j.val + 1) := by omega
  rw [jacobiMatrix, of_apply, ite_eq_right h1, dite_eq_right h2, dite_eq_right h3]

/-- Entries strictly above the superdiagonal vanish. -/
theorem jacobiMatrix_apply_of_add_one_lt_right (a : Fin (n + 1) → R) (b : Fin n → R)
    {i j : Fin (n + 1)} (h : i.val + 1 < j.val) : jacobiMatrix a b i j = 0 := by
  have h1 : i ≠ j := fun hij => by subst hij; omega
  have h2 : ¬(j.val = i.val + 1) := by omega
  have h3 : ¬(i.val = j.val + 1) := by omega
  rw [jacobiMatrix, of_apply, ite_eq_right h1, dite_eq_right h2, dite_eq_right h3]

/-- A Jacobi matrix is symmetric. -/
@[simp]
theorem jacobiMatrix_transpose (a : Fin (n + 1) → R) (b : Fin n → R) :
    (jacobiMatrix a b)ᵀ = jacobiMatrix a b := by
  ext i j
  simp only [transpose_apply, jacobiMatrix, of_apply]
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

/-- Over a ring with trivial star (such as `ℝ`), every Jacobi matrix is Hermitian. -/
theorem isHermitian_jacobiMatrix [Star R] [TrivialStar R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    (jacobiMatrix a b).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, jacobiMatrix_transpose]

/-- Scaling the diagonal and subdiagonal vectors scales the Jacobi matrix. -/
theorem jacobiMatrix_smul {M : Type*} [SMulZeroClass M R] (c : M) (a : Fin (n + 1) → R)
    (b : Fin n → R) : jacobiMatrix (c • a) (c • b) = c • jacobiMatrix a b := by
  ext i j
  simp only [Matrix.smul_apply, jacobiMatrix, of_apply]
  by_cases hij : i = j
  · simp [hij]
  · rw [ite_eq_right hij, ite_eq_right hij]
    by_cases h1 : j.val = i.val + 1
    · simp [h1]
    · by_cases h2 : i.val = j.val + 1
      · rw [dite_eq_right h1, dite_eq_left h2, dite_eq_right h1, dite_eq_left h2, Pi.smul_apply]
      · rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h1, dite_eq_right h2, smul_zero]

/-- The Jacobi matrix depends continuously on its diagonal and subdiagonal entries. -/
@[fun_prop]
theorem continuous_jacobiMatrix [TopologicalSpace R] :
    Continuous fun p : (Fin (n + 1) → R) × (Fin n → R) => jacobiMatrix p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jacobiMatrix, of_apply]
  split_ifs
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply _).comp continuous_snd
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const

/-- The Jacobi matrix depends measurably on its diagonal and subdiagonal entries. -/
@[fun_prop]
theorem measurable_jacobiMatrix [MeasurableSpace R] :
    Measurable fun p : (Fin (n + 1) → R) × (Fin n → R) => jacobiMatrix p.1 p.2 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [jacobiMatrix, of_apply]
  split_ifs
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd
  · exact (measurable_pi_apply _).comp measurable_snd
  · exact measurable_const

end Entries

/-! ### Trace identities -/

section Trace

variable {R : Type*} {n : ℕ}

/-- The trace of a Jacobi matrix is the sum of its diagonal entries. -/
theorem trace_jacobiMatrix [AddCommMonoid R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    (jacobiMatrix a b).trace = ∑ i, a i := by
  simp [Matrix.trace, Matrix.diag]

/-- Entrywise decomposition of the squared entries in column `i` of `jacobiMatrix a b`. -/
private theorem jacobiMatrix_col_sq_eq [CommSemiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    (i j : Fin (n + 1)) :
    jacobiMatrix a b j i ^ 2 =
      (if j = i then a i ^ 2 else 0) +
      (if h : i.val < n then if j = ⟨i.val + 1, by omega⟩ then b ⟨i.val, h⟩ ^ 2 else 0 else 0) +
      (if h : 0 < i.val then
        if j = ⟨i.val - 1, by omega⟩ then b ⟨i.val - 1, by omega⟩ ^ 2 else 0 else 0) := by
  simp only [jacobiMatrix, of_apply]
  split_ifs <;>
    simp only [Fin.ext_iff] at * <;>
    first
    | omega
    | (simp only [add_zero]; congr 2; ext; omega)
    | (simp only [zero_add]; congr 2; ext; omega)
    | simp

/-- The sum of squared entries in column `i` of `jacobiMatrix a b`. -/
private theorem sum_sq_jacobiMatrix_col [CommSemiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    (i : Fin (n + 1)) :
    ∑ j : Fin (n + 1), jacobiMatrix a b j i ^ 2 =
      a i ^ 2 + (if h : i.val < n then b ⟨i.val, h⟩ ^ 2 else 0) +
        (if h : 0 < i.val then b ⟨i.val - 1, by omega⟩ ^ 2 else 0) := by
  simp_rw [jacobiMatrix_col_sq_eq, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp
    · split_ifs <;> simp
  · split_ifs <;> simp

/-- The trace of the square of a Jacobi matrix is `∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2`. -/
theorem trace_jacobiMatrix_sq [CommSemiring R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    ((jacobiMatrix a b) ^ 2).trace = ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2 := by
  have hdiag : ∀ i : Fin (n + 1), ((jacobiMatrix a b) ^ 2) i i =
      ∑ j : Fin (n + 1), jacobiMatrix a b j i ^ 2 := fun i => by
    rw [sq, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsym : jacobiMatrix a b i j = jacobiMatrix a b j i := by
      simpa [transpose_apply] using congrFun (congrFun (jacobiMatrix_transpose a b) j) i
    rw [hsym, sq]
  simp only [Matrix.trace, Matrix.diag_apply, hdiag, sum_sq_jacobiMatrix_col,
    Finset.sum_add_distrib]
  have h1 : ∑ i : Fin (n + 1), (if h : i.val < n then b ⟨i.val, h⟩ ^ 2 else 0) =
      ∑ k : Fin n, b k ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    simp
  have h2 : ∑ i : Fin (n + 1), (if h : 0 < i.val then b ⟨i.val - 1, by omega⟩ ^ 2 else 0) =
      ∑ k : Fin n, b k ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp
  rw [h1, h2]
  ring

end Trace

/-! ### Krylov vectors and the Krylov matrix -/

section Krylov

variable {R : Type*} {n : ℕ}

/-- The `m`-th Krylov vector `(J ^ m) · 0` vanishes below row `m`. -/
theorem jacobiMatrix_pow_apply_zero_of_lt [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    ∀ (m : ℕ) {i : Fin (n + 1)}, m < i.val → (jacobiMatrix a b ^ m) i 0 = 0
  | 0, i, hi => by
      have hne : i ≠ 0 := fun h => by subst h; simp at hi
      simp [hne]
  | m + 1, i, hi => by
      rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hjm : m < j.val
      · rw [jacobiMatrix_pow_apply_zero_of_lt a b m hjm, mul_zero]
      · rw [jacobiMatrix_apply_of_add_one_lt_left a b (by omega), zero_mul]

/-- The leading entry `(J ^ i) i 0` of the `i`-th Krylov vector is `∏_{j < i} b j`. -/
theorem jacobiMatrix_pow_apply_zero_self [CommSemiring R] (a : Fin (n + 1) → R) (b : Fin n → R)
    (i : Fin (n + 1)) :
    (jacobiMatrix a b ^ i.val) i 0 =
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), b j := by
  induction i using Fin.induction with
  | zero => simp
  | succ k ih =>
      rw [Fin.val_succ, pow_succ', Matrix.mul_apply, Finset.sum_eq_single k.castSucc]
      · rw [jacobiMatrix_apply_succ_castSucc]
        have hcast : k.castSucc.val = k.val := Fin.val_castSucc k
        rw [← hcast, ih, hcast]
        have hfilt : Finset.univ.filter (fun j : Fin n => j.val < k.val + 1) =
            insert k (Finset.univ.filter (fun j : Fin n => j.val < k.val)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hk_not : k ∉ Finset.univ.filter (fun j : Fin n => j.val < k.val) := by simp
        rw [hfilt, Finset.prod_insert hk_not]
      · intro j _ hjk
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjk) with hlt | hgt
        · rw [jacobiMatrix_apply_of_add_one_lt_left a b (by simp at hlt ⊢; omega), zero_mul]
        · rw [jacobiMatrix_pow_apply_zero_of_lt a b k.val (by simpa using hgt), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h

/-- The Krylov matrix of `jacobiMatrix a b` with entry `(i, m)` equal to `(J ^ m) i 0`. -/
def krylovMatrix [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i m => (jacobiMatrix a b ^ m.val) i 0

/-- The Krylov matrix is upper triangular. -/
theorem isUpperTriangular_krylovMatrix [Semiring R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    (krylovMatrix a b).IsUpperTriangular := fun _ _ h =>
  jacobiMatrix_pow_apply_zero_of_lt a b _ h

/-- The determinant of the Krylov matrix is `∏ j : Fin n, b j ^ (n - j.val)`. -/
theorem det_krylovMatrix [CommRing R] (a : Fin (n + 1) → R) (b : Fin n → R) :
    (krylovMatrix a b).det = ∏ j : Fin n, b j ^ (n - j.val) := by
  rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_krylovMatrix a b)]
  simp only [krylovMatrix, of_apply, jacobiMatrix_pow_apply_zero_self]
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
          have hcard : (Finset.univ.filter (fun i : Fin (n + 1) => j.val < i.val)).card =
              (Finset.Ioo j.val (n + 1)).card := by
            refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
            · intro i hi
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
              exact Finset.mem_Ioo.mpr ⟨hi, i.isLt⟩
            · intro _ _ _ _ h; exact Fin.ext h
            · intro m hm
              rw [Finset.mem_Ioo] at hm
              exact ⟨⟨m, hm.2⟩, by simp [hm.1], rfl⟩
          rw [hcard, Nat.card_Ioo]
          omega

end Krylov

/-! ### Simplicity of eigenvalues and spectral weights -/

section Spectral

variable {n : ℕ}

/-- Any eigenvector of a Jacobi matrix with nonzero subdiagonal entries whose first coordinate
vanishes is the zero vector. -/
theorem eq_zero_of_mulVec_jacobiMatrix_eq_smul_of_apply_zero {K : Type*} [Field K]
    {a : Fin (n + 1) → K} {b : Fin n → K} (hb : ∀ k, b k ≠ 0) {μ : K}
    {v : Fin (n + 1) → K} (hv : jacobiMatrix a b *ᵥ v = μ • v) (h0 : v 0 = 0) :
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
        have hsum : ∑ j : Fin (n + 1), jacobiMatrix a b k'.castSucc j * v j =
            b k' * v k'.succ := by
          rw [Finset.sum_eq_single k'.succ]
          · rw [jacobiMatrix_apply_castSucc_succ]
          · intro j _ hjk
            by_cases hjle : j.val ≤ k
            · rw [ih j.val (by omega) j.isLt, mul_zero]
            · rw [jacobiMatrix_apply_of_add_one_lt_right a b (by
                have : j.val ≠ k + 1 := fun h => hjk (Fin.ext h)
                simp [k']; omega), zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum] at hrow
        have hsucc : v k'.succ = 0 := (mul_eq_zero.mp hrow).resolve_left (hb k')
        simpa [k'] using hsucc

/-- Every nonzero eigenvector of a Jacobi matrix with nonzero subdiagonal entries has nonzero
first coordinate. -/
theorem apply_zero_ne_zero_of_mulVec_jacobiMatrix_eq_smul {K : Type*} [Field K]
    {a : Fin (n + 1) → K} {b : Fin n → K} (hb : ∀ k, b k ≠ 0) {μ : K}
    {v : Fin (n + 1) → K} (hv : jacobiMatrix a b *ᵥ v = μ • v) (hne : v ≠ 0) :
    v 0 ≠ 0 :=
  fun h0 => hne (eq_zero_of_mulVec_jacobiMatrix_eq_smul_of_apply_zero hb hv h0)

/-- The decreasingly ordered eigenvalues of `jacobiMatrix a b`, indexed directly by `Fin (n + 1)`.
-/
def jacobiEigenvalues (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun k => (isHermitian_jacobiMatrix a b).eigenvalues₀ (k.cast (Fintype.card_fin (n + 1)).symm)

/-- The ordered eigenvalues of `jacobiMatrix a b` are antitone. -/
theorem antitone_jacobiEigenvalues (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    Antitone (jacobiEigenvalues a b) := fun _ _ hij =>
  (isHermitian_jacobiMatrix a b).eigenvalues₀_antitone (Fin.le_def.mpr hij)

/-- The ordered eigenvalues of `jacobiMatrix a b` depend continuously on `(a, b)`. -/
@[fun_prop]
theorem continuous_jacobiEigenvalues :
    Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiEigenvalues p.1 p.2 := by
  refine continuous_pi fun k => (continuous_apply _).comp ?_
  exact Matrix.continuous_eigenvalues₀.comp
    (continuous_jacobiMatrix.subtype_mk fun p => isHermitian_jacobiMatrix p.1 p.2)

/-- The ordered eigenvalues of `jacobiMatrix a b` depend measurably on `(a, b)`. -/
@[fun_prop]
theorem measurable_jacobiEigenvalues :
    Measurable fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiEigenvalues p.1 p.2 :=
  continuous_jacobiEigenvalues.measurable

/-- The orthonormal basis of eigenvectors of `jacobiMatrix a b` aligned with `jacobiEigenvalues`. -/
private def jacobiEigenvectorBasis (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    OrthonormalBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  ((isSymmetric_toEuclideanLin_iff.mpr (isHermitian_jacobiMatrix a b)).eigenvectorBasis
    finrank_euclideanSpace).reindex (finCongr (Fintype.card_fin (n + 1)))

private theorem mulVec_jacobiEigenvectorBasis (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (k : Fin (n + 1)) :
    jacobiMatrix a b *ᵥ ⇑(jacobiEigenvectorBasis a b k) =
      jacobiEigenvalues a b k • ⇑(jacobiEigenvectorBasis a b k) := by
  have h := (isSymmetric_toEuclideanLin_iff.mpr
    (isHermitian_jacobiMatrix a b)).apply_eigenvectorBasis finrank_euclideanSpace
      (k.cast (Fintype.card_fin (n + 1)).symm)
  simpa only [jacobiEigenvectorBasis, OrthonormalBasis.reindex_apply, finCongr_symm,
    finCongr_apply, jacobiEigenvalues, Matrix.IsHermitian.eigenvalues₀, Matrix.toLpLin_apply,
    RCLike.ofReal_real_eq_id, id_eq, WithLp.ofLp_smul] using congrArg WithLp.ofLp h

/-- A real Jacobi matrix with nonzero subdiagonal entries has strictly decreasing eigenvalues. -/
theorem strictAnti_jacobiEigenvalues {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} (hb : ∀ k, b k ≠ 0) :
    StrictAnti (jacobiEigenvalues a b) := by
  refine (antitone_jacobiEigenvalues a b).strictAnti_of_injective fun i j hij => ?_
  by_contra hne
  let vi := jacobiEigenvectorBasis a b i
  let vj := jacobiEigenvectorBasis a b j
  have hvi : jacobiMatrix a b *ᵥ ⇑vi = jacobiEigenvalues a b i • ⇑vi :=
    mulVec_jacobiEigenvectorBasis a b i
  have hvj : jacobiMatrix a b *ᵥ ⇑vj = jacobiEigenvalues a b i • ⇑vj := by
    rw [hij]; exact mulVec_jacobiEigenvectorBasis a b j
  have hcomb : jacobiMatrix a b *ᵥ (vj 0 • ⇑vi - vi 0 • ⇑vj) =
      jacobiEigenvalues a b i • (vj 0 • ⇑vi - vi 0 • ⇑vj) := by
    rw [mulVec_sub, mulVec_smul, mulVec_smul, hvi, hvj, smul_sub, smul_comm (vj 0),
      smul_comm (vi 0)]
  have hlin : vj 0 • ⇑vi - vi 0 • ⇑vj = 0 :=
    eq_zero_of_mulVec_jacobiMatrix_eq_smul_of_apply_zero hb hcomb (by simp [mul_comm])
  have hlinE : vj 0 • vi = vi 0 • vj := by
    ext r
    have hr := congrFun hlin r
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at hr
    simpa [PiLp.smul_apply, smul_eq_mul] using hr
  have hortho : ⟪vi, vj⟫ = 0 := (jacobiEigenvectorBasis a b).orthonormal.2 hne
  have hnorm : ⟪vi, vi⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, (jacobiEigenvectorBasis a b).orthonormal.1 i, one_pow]
  have hvj0 : vj 0 = 0 := by
    have := congrArg (fun x => ⟪vi, x⟫) hlinE
    simp only [inner_smul_right, hnorm, hortho, mul_one, mul_zero] at this
    exact this
  exact apply_zero_ne_zero_of_mulVec_jacobiMatrix_eq_smul hb hvj
    (fun h => (jacobiEigenvectorBasis a b).orthonormal.ne_zero j (PiLp.ext (congrFun h))) hvj0

/-- A Hermitian real matrix whose characteristic polynomial splits along an antitone tuple `lam`
has `eigenvalues₀` matching `lam`. -/
private theorem eigenvalues₀_eq_of_charpoly_eq {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) {lam : Fin m → ℝ} (hlam : Antitone lam)
    (hchar : A.charpoly = ∏ k, (Polynomial.X - Polynomial.C (lam k))) :
    ∀ k : Fin m, hA.eigenvalues₀ (k.cast (Fintype.card_fin m).symm) = lam k := by
  have hroots : A.charpoly.roots = Multiset.map lam Finset.univ.val := by
    rw [hchar, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def,
    RCLike.re_to_real, Multiset.coe_sort] at hsort
  have hmerge : (List.ofFn lam).mergeSort (· ≥ ·) = List.ofFn lam := by
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hlam.sortedGE_ofFn
  rw [hmerge] at hsort
  intro k
  have hget := congrArg (fun L => L[k.val]?) hsort
  simp only [List.getElem?_ofFn, k.isLt, ↓reduceDIte,
    show k.val < Fintype.card (Fin m) by simp, Option.some.injEq] at hget
  exact hget.symm

/-- If the characteristic polynomial of `jacobiMatrix a b` splits over `ℝ` with decreasing roots
`lam`, then `jacobiEigenvalues a b = lam`. -/
theorem jacobiEigenvalues_eq_of_charpoly_eq {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    {lam : Fin (n + 1) → ℝ} (hlam : Antitone lam)
    (hchar : (jacobiMatrix a b).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (lam k))) :
    jacobiEigenvalues a b = lam :=
  funext (eigenvalues₀_eq_of_charpoly_eq (isHermitian_jacobiMatrix a b) hlam hchar)

/-- Scaling a Jacobi matrix by a nonnegative scalar `s` scales its ordered eigenvalues by `s`. -/
theorem jacobiEigenvalues_smul {s : ℝ} (hs : 0 ≤ s) (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    jacobiEigenvalues (s • a) (s • b) = s • jacobiEigenvalues a b := by
  let hJ := isHermitian_jacobiMatrix a b
  have hchar : (jacobiMatrix (s • a) (s • b)).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (s * jacobiEigenvalues a b k)) := by
    rw [jacobiMatrix_smul]
    have hdiag : s • jacobiMatrix a b =
        (hJ.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
          diagonal (s • hJ.eigenvalues) *
          star (hJ.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
      conv_lhs => rw [hJ.spectral_theorem, Unitary.conjStarAlgAut_apply]
      simp only [RCLike.ofReal_real_eq_id, Function.id_comp]
      rw [← smul_mul_assoc, ← mul_smul_comm]
      congr 2
      ext i j
      simp
    rw [hdiag, Matrix.charpoly_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul,
      Matrix.charpoly_diagonal]
    let e : Fin (n + 1) ≃ Fin (n + 1) :=
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin (n + 1))))).symm.trans
        (finCongr (Fintype.card_fin (n + 1)))
    refine Fintype.prod_equiv e _ _ fun i => ?_
    simp [Matrix.IsHermitian.eigenvalues, jacobiEigenvalues, e]
  funext k
  exact eigenvalues₀_eq_of_charpoly_eq (isHermitian_jacobiMatrix (s • a) (s • b))
    (fun _ _ hij => mul_le_mul_of_nonneg_left (antitone_jacobiEigenvalues a b hij) hs) hchar k

/-- The sum of squares of the eigenvalues equals the trace of the square of the Jacobi matrix. -/
theorem sum_jacobiEigenvalues_sq (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    ∑ k : Fin (n + 1), jacobiEigenvalues a b k ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2 := by
  rw [← trace_jacobiMatrix_sq a b]
  let hJ := isHermitian_jacobiMatrix a b
  have hsq : jacobiMatrix a b ^ 2 =
      (hJ.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
        diagonal (fun i => hJ.eigenvalues i ^ 2) *
        star (hJ.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    conv_lhs => rw [sq, hJ.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [RCLike.ofReal_real_eq_id, Function.id_comp]
    calc _ = (hJ.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
          diagonal hJ.eigenvalues *
          (star (hJ.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
            (hJ.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) *
          diagonal hJ.eigenvalues *
          star (hJ.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
            simp only [mul_assoc]
      _ = _ := by
            rw [Unitary.coe_star_mul_self, mul_one, mul_assoc, mul_assoc,
              ← mul_assoc (diagonal hJ.eigenvalues), Matrix.diagonal_mul_diagonal]
            simp only [sq, mul_assoc]
  rw [hsq, Matrix.trace_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul,
    Matrix.trace_diagonal]
  let e : Fin (n + 1) ≃ Fin (n + 1) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin (n + 1))))).symm.trans
      (finCongr (Fintype.card_fin (n + 1)))
  exact (Fintype.sum_equiv e _ _ fun i => by
    simp [Matrix.IsHermitian.eigenvalues, jacobiEigenvalues, e]).symm

/-- For any polynomial `p` and real Jacobi matrix `J`, `(aeval J p) 0 0` is the weighted sum of
`p (λ k)` against the squared first entries of the orthonormal eigenvector basis. -/
private theorem aeval_jacobiMatrix_zero_zero (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (p : ℝ[X]) :
    (Polynomial.aeval (jacobiMatrix a b) p) 0 0 =
      ∑ k : Fin (n + 1), (jacobiEigenvectorBasis a b k 0) ^ 2 *
        p.eval (jacobiEigenvalues a b k) := by
  have hpow : ∀ r : ℕ, (jacobiMatrix a b ^ r) 0 0 =
      ∑ k : Fin (n + 1), (jacobiEigenvectorBasis a b k 0) ^ 2 *
        jacobiEigenvalues a b k ^ r := by
    intro r
    let v := jacobiEigenvectorBasis a b
    let e0 : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
    have hv_pow : ∀ k, (jacobiMatrix a b ^ r) *ᵥ ⇑(v k) =
        jacobiEigenvalues a b k ^ r • ⇑(v k) := by
      intro k
      induction r with
      | zero => simp
      | succ m ihm =>
          rw [pow_succ', ← mulVec_mulVec, ihm, mulVec_smul, mulVec_jacobiEigenvectorBasis,
            smul_smul, ← pow_succ]
    have he0 : e0 = ∑ k, (v k 0) • v k := by
      conv_lhs => rw [← v.sum_repr' e0]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hinner : ⟪v k, e0⟫ = v k 0 := by simp [e0, EuclideanSpace.inner_single_right]
      rw [hinner]
    have hmul : (jacobiMatrix a b ^ r) *ᵥ ⇑e0 =
        ∑ k, (v k 0 * jacobiEigenvalues a b k ^ r) • ⇑(v k) := by
      conv_lhs => rw [he0]
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, mulVec_sum, mulVec_smul, hv_pow, smul_smul]
    have h0 : ((jacobiMatrix a b ^ r) *ᵥ ⇑e0) 0 = (jacobiMatrix a b ^ r) 0 0 := by
      simp [e0, mulVec, dotProduct, EuclideanSpace.single]
    rw [← h0, hmul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => by simp [sq]; ring
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
      simp only [map_add, Matrix.add_apply, Polynomial.eval_add, ihp, ihq, mul_add,
        Finset.sum_add_distrib]
  | monomial r c =>
      simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul, Matrix.smul_apply, smul_eq_mul, Polynomial.eval_monomial, hpow r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring

/-- The canonical spectral weight associated to the `k`-th decreasing eigenvalue of
`jacobiMatrix a b`, defined by the Lagrange interpolation ratio in the matrix and its ordered
eigenvalues. On the nonvanishing-subdiagonal locus it equals `(v k 0) ^ 2` for every unit
eigenvector `v k` of the `k`-th eigenvalue. -/
def jacobiSpectralWeight (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (k : Fin (n + 1)) : ℝ :=
  let J := jacobiMatrix a b
  let lam := jacobiEigenvalues a b
  ((((List.finRange (n + 1)).filter (· ≠ k)).map
      fun j => J - lam j • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).prod) 0 0 /
    ∏ j ∈ Finset.univ.erase k, (lam k - lam j)

private theorem list_prod_sub_smul_eq_aeval (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (k : Fin (n + 1)) :
    (((List.finRange (n + 1)).filter (· ≠ k)).map
      fun j => jacobiMatrix a b - jacobiEigenvalues a b j •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).prod =
      Polynomial.aeval (jacobiMatrix a b)
        (∏ j ∈ Finset.univ.erase k,
          (Polynomial.X - Polynomial.C (jacobiEigenvalues a b j))) := by
  have hcomp : (fun j => jacobiMatrix a b - jacobiEigenvalues a b j •
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) =
      (Polynomial.aeval (jacobiMatrix a b)) ∘
        (fun j => Polynomial.X - Polynomial.C (jacobiEigenvalues a b j)) := by
    funext j
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hcomp, ← List.map_map, ← map_list_prod]
  congr 1
  have hnd : ((List.finRange (n + 1)).filter (· ≠ k)).Nodup :=
    (List.nodup_finRange (n + 1)).filter _
  have hfin : (((List.finRange (n + 1)).filter (· ≠ k)).toFinset) = Finset.univ.erase k := by
    ext j
    simp [Finset.mem_erase]
  rw [← hfin, List.prod_toFinset _ hnd]

private theorem jacobiSpectralWeight_eq_sq_basis {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (hb : ∀ j, b j ≠ 0) (k : Fin (n + 1)) :
    jacobiSpectralWeight a b k = (jacobiEigenvectorBasis a b k 0) ^ 2 := by
  let lam := jacobiEigenvalues a b
  have hstrict : StrictAnti lam := strictAnti_jacobiEigenvalues hb
  have hden : ∏ j ∈ Finset.univ.erase k, (lam k - lam j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj =>
      sub_ne_zero.mpr (hstrict.injective.ne (Finset.ne_of_mem_erase hj).symm)
  unfold jacobiSpectralWeight
  dsimp only
  rw [list_prod_sub_smul_eq_aeval, aeval_jacobiMatrix_zero_zero, Finset.sum_eq_single k]
  · simp [Polynomial.eval_prod, lam, mul_div_cancel_right₀ _ hden]
  · intro m _ hmk
    have hzero : (∏ j ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (lam j))).eval
        (lam m) = 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hmk, Finset.mem_univ m⟩) (by simp)
    rw [hzero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- On the nonvanishing-subdiagonal locus, `jacobiSpectralWeight a b k` equals `(v 0) ^ 2` for
every unit eigenvector `v` of `jacobiMatrix a b` with eigenvalue `jacobiEigenvalues a b k`. -/
theorem jacobiSpectralWeight_eq_sq_eigenvector {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (hb : ∀ j, b j ≠ 0) (k : Fin (n + 1)) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv_norm : ‖v‖ = 1)
    (hv_eig : jacobiMatrix a b *ᵥ ⇑v = jacobiEigenvalues a b k • ⇑v) :
    jacobiSpectralWeight a b k = (v 0) ^ 2 := by
  rw [jacobiSpectralWeight_eq_sq_basis hb k]
  let u := jacobiEigenvectorBasis a b k
  have hu_norm : ‖u‖ = 1 := (jacobiEigenvectorBasis a b).orthonormal.1 k
  have hu : jacobiMatrix a b *ᵥ ⇑u = jacobiEigenvalues a b k • ⇑u :=
    mulVec_jacobiEigenvectorBasis a b k
  have hcomb : jacobiMatrix a b *ᵥ (v 0 • ⇑u - u 0 • ⇑v) =
      jacobiEigenvalues a b k • (v 0 • ⇑u - u 0 • ⇑v) := by
    rw [mulVec_sub, mulVec_smul, mulVec_smul, hu, hv_eig, smul_sub, smul_comm (v 0),
      smul_comm (u 0)]
  have hlin := eq_zero_of_mulVec_jacobiMatrix_eq_smul_of_apply_zero hb hcomb (by simp [mul_comm])
  have hE : v 0 • u = u 0 • v := by
    ext r
    have hr := congrFun hlin r
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at hr
    simpa [PiLp.smul_apply, smul_eq_mul] using hr
  have hnorm := congrArg (fun x => ‖x‖ ^ 2) hE
  simp only [norm_smul, Real.norm_eq_abs, sq_abs, hv_norm, hu_norm, mul_one] at hnorm
  exact hnorm.symm

/-- Every spectral weight of a Jacobi matrix with nonzero subdiagonals is strictly positive. -/
theorem jacobiSpectralWeight_pos {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} (hb : ∀ j, b j ≠ 0)
    (k : Fin (n + 1)) : 0 < jacobiSpectralWeight a b k := by
  rw [jacobiSpectralWeight_eq_sq_basis hb k]
  have hne : jacobiEigenvectorBasis a b k 0 ≠ 0 :=
    apply_zero_ne_zero_of_mulVec_jacobiMatrix_eq_smul hb (mulVec_jacobiEigenvectorBasis a b k)
      (fun h => (jacobiEigenvectorBasis a b).orthonormal.ne_zero k (PiLp.ext (congrFun h)))
  exact sq_pos_of_ne_zero hne

/-- The spectral weights of a Jacobi matrix with nonzero subdiagonals sum to `1`. -/
theorem sum_jacobiSpectralWeight {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} (hb : ∀ j, b j ≠ 0) :
    ∑ k : Fin (n + 1), jacobiSpectralWeight a b k = 1 := by
  simp_rw [jacobiSpectralWeight_eq_sq_basis hb]
  let e0 : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  have hparseval := (jacobiEigenvectorBasis a b).sum_sq_inner_right e0
  have he0 : ‖e0‖ ^ 2 = 1 := by simp [e0]
  rw [he0] at hparseval
  convert hparseval using 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hinner : ⟪jacobiEigenvectorBasis a b k, e0⟫ = jacobiEigenvectorBasis a b k 0 := by
    simp [e0, EuclideanSpace.inner_single_right]
  rw [hinner]

/-- Moment identity: `((jacobiMatrix a b) ^ r) 0 0` is the `r`-th moment of the discrete
spectral measure `∑ k, q k δ_{λ k}`. -/
theorem jacobiMatrix_pow_zero_zero {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} (hb : ∀ j, b j ≠ 0)
    (r : ℕ) :
    (jacobiMatrix a b ^ r) 0 0 =
      ∑ k : Fin (n + 1), jacobiSpectralWeight a b k * jacobiEigenvalues a b k ^ r := by
  simp_rw [jacobiSpectralWeight_eq_sq_basis hb]
  simpa using aeval_jacobiMatrix_zero_zero a b (Polynomial.X ^ r)

/-- Positive scaling of a Jacobi matrix leaves its spectral weights unchanged. -/
theorem jacobiSpectralWeight_smul {s : ℝ} (hs : 0 < s) {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (hb : ∀ j, b j ≠ 0) :
    jacobiSpectralWeight (s • a) (s • b) = jacobiSpectralWeight a b := by
  have hbs : ∀ j, (s • b) j ≠ 0 := fun j => mul_ne_zero hs.ne' (hb j)
  funext k
  rw [jacobiSpectralWeight_eq_sq_eigenvector hbs k
    ((jacobiEigenvectorBasis a b).orthonormal.1 k),
    jacobiSpectralWeight_eq_sq_basis hb k]
  rw [jacobiMatrix_smul, smul_mulVec, mulVec_jacobiEigenvectorBasis,
    jacobiEigenvalues_smul hs.le, Pi.smul_apply, smul_eq_mul, mul_smul]

private theorem continuous_jacobiSpectralWeight_num (k : Fin (n + 1)) :
    Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      ((((List.finRange (n + 1)).filter (· ≠ k)).map
        fun j => jacobiMatrix p.1 p.2 -
          jacobiEigenvalues p.1 p.2 j •
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).prod) 0 0 := by
  have hlam : ∀ j, Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      jacobiEigenvalues p.1 p.2 j := fun j =>
    (continuous_apply j).comp continuous_jacobiEigenvalues
  have hlist : ∀ L : List (Fin (n + 1)),
      Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
        (L.map fun j => jacobiMatrix p.1 p.2 -
          jacobiEigenvalues p.1 p.2 j •
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).prod := by
    intro L
    induction L with
    | nil => simpa using continuous_const
    | cons j tl ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (continuous_jacobiMatrix.sub ((hlam j).smul continuous_const)).mul ih
  exact ((continuous_apply 0).comp ((continuous_apply 0).comp (hlist _)))

private theorem continuous_jacobiSpectralWeight_den (k : Fin (n + 1)) :
    Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      ∏ j ∈ Finset.univ.erase k,
        (jacobiEigenvalues p.1 p.2 k - jacobiEigenvalues p.1 p.2 j) := by
  fun_prop

/-- The spectral weight vector is globally measurable. -/
@[fun_prop]
theorem measurable_jacobiSpectralWeight :
    Measurable fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiSpectralWeight p.1 p.2 := by
  refine measurable_pi_iff.mpr fun k => ?_
  exact (continuous_jacobiSpectralWeight_num k).measurable.div
    (continuous_jacobiSpectralWeight_den k).measurable

/-- The spectral weight vector is continuous on the locus of nonvanishing subdiagonals. -/
theorem continuousOn_jacobiSpectralWeight :
    ContinuousOn (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiSpectralWeight p.1 p.2)
      {p | ∀ j, p.2 j ≠ 0} := by
  refine continuousOn_pi.mpr fun k => ?_
  refine (continuous_jacobiSpectralWeight_num k).continuousOn.div
    (continuous_jacobiSpectralWeight_den k).continuousOn fun p hp => ?_
  exact Finset.prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr ((strictAnti_jacobiEigenvalues hp).injective.ne
      (Finset.ne_of_mem_erase hj).symm)

/-! ### The Dumitriu–Edelman Vandermonde–weight identity -/

private theorem eigenvectorMatrix_transpose_mul_krylov (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    (Matrix.of fun i k => jacobiEigenvectorBasis a b k i)ᵀ * krylovMatrix a b =
      Matrix.diagonal (fun k => jacobiEigenvectorBasis a b k 0) *
        Matrix.vandermonde (jacobiEigenvalues a b) := by
  let lam := jacobiEigenvalues a b
  let v := jacobiEigenvectorBasis a b
  ext k m
  rw [Matrix.mul_apply, Matrix.diagonal_mul, Matrix.vandermonde_apply]
  have hJm : ∀ r : ℕ, ∑ i, v k i * (jacobiMatrix a b ^ r) i 0 = lam k ^ r * v k 0 := by
    intro r
    induction r with
    | zero => simp [Matrix.one_apply]
    | succ r ihr =>
        rw [pow_succ']
        simp_rw [Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        have hstep : ∀ j, ∑ i, v k i * (jacobiMatrix a b i j * (jacobiMatrix a b ^ r) j 0) =
            lam k * (v k j * (jacobiMatrix a b ^ r) j 0) := by
          intro j
          have heig := congrFun (mulVec_jacobiEigenvectorBasis a b k) j
          simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at heig
          calc ∑ i, v k i * (jacobiMatrix a b i j * (jacobiMatrix a b ^ r) j 0)
              = (∑ i, jacobiMatrix a b j i * v k i) * (jacobiMatrix a b ^ r) j 0 := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun i _ => ?_
                have hsym : jacobiMatrix a b i j = jacobiMatrix a b j i := by
                  simpa [transpose_apply] using
                    congrFun (congrFun (jacobiMatrix_transpose a b) j) i
                rw [hsym]
                ring
            _ = lam k * (v k j * (jacobiMatrix a b ^ r) j 0) := by rw [heig]; ring
        simp_rw [hstep, ← Finset.mul_sum, ihr, pow_succ']
        ring
  simpa [krylovMatrix, mul_comm] using hJm m.val

/-- **Vandermonde–weight identity**: for a Jacobi matrix with strictly positive subdiagonal
entries, `∏ j, b j ^ (n - j)` equals the product of the square roots of its spectral weights
times the Vandermonde product of its ordered eigenvalues. -/
theorem prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_vandermonde {a : Fin (n + 1) → ℝ}
    {b : Fin n → ℝ} (hb : ∀ j, 0 < b j) :
    ∏ j : Fin n, b j ^ (n - j.val) =
      (∏ k : Fin (n + 1), Real.sqrt (jacobiSpectralWeight a b k)) *
        ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
          (jacobiEigenvalues a b i - jacobiEigenvalues a b j) := by
  have hbne : ∀ j, b j ≠ 0 := fun j => (hb j).ne'
  let v := jacobiEigenvectorBasis a b
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i k => v k i
  have hUTU : Uᵀ * U = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hinner : ∑ i, v k i * v l i = ⟪v k, v l⟫ := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    simpa [U, hinner] using orthonormal_iff_ite.mp v.orthonormal k l
  have hdetU : |Uᵀ.det| = 1 := by
    have hsq : Uᵀ.det ^ 2 = 1 := by
      calc Uᵀ.det ^ 2 = Uᵀ.det * U.det := by rw [sq, Matrix.det_transpose]
        _ = (Uᵀ * U).det := (Matrix.det_mul _ _).symm
        _ = 1 := by rw [hUTU, Matrix.det_one]
    exact (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp (by rw [sq_abs, hsq, one_pow])
  have hdet : |(Uᵀ * krylovMatrix a b).det| =
      |(Matrix.diagonal (fun k => v k 0) * Matrix.vandermonde (jacobiEigenvalues a b)).det| :=
    congrArg (fun M : Matrix _ _ ℝ => |M.det|) (eigenvectorMatrix_transpose_mul_krylov a b)
  simp only [Matrix.det_mul, abs_mul, hdetU, one_mul, Matrix.det_diagonal,
    Matrix.det_vandermonde, det_krylovMatrix] at hdet
  rw [abs_of_pos (Finset.prod_pos fun j _ => pow_pos (hb j) _)] at hdet
  rw [hdet]
  congr 1
  · rw [Finset.abs_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [jacobiSpectralWeight_eq_sq_basis hbne k, Real.sqrt_sq_eq_abs]
  · rw [Finset.abs_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.abs_prod]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hlt := strictAnti_jacobiEigenvalues (a := a) hbne (Finset.mem_Ioi.mp hj)
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)]

end Spectral

end TauCeti
