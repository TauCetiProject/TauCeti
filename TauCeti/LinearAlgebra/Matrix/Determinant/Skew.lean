/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Int.ModEq
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Determinants of skew-symmetric matrices and of even symmetric matrices

The determinant of a skew-symmetric matrix `M` (`Mᵀ = -M`) with zero diagonal over a field is a
square: the form `x, y ↦ xᵀ M y` is alternating, so when it is nondegenerate it has a symplectic
basis, in which its matrix is `J` of determinant `1`, and `det M` is the square of the inverse of
the determinant of the change of basis. For an integer matrix the diagonal vanishes automatically
and the square root, a rational number, is an integer. Over an arbitrary commutative ring the
statement is Cayley's identity `det M = Pf(M)²`, which needs the Pfaffian and is not proved here.

A symmetric integer matrix `A` with even diagonal, of size `2k`, splits as `A = S + Sᵀ`. The
polynomial `q(X) = det (X • Sᵀ + S)` has degree at most `2k` and is its own reflection at `2k`,
because reflecting the entries transposes the matrix; its coefficients are therefore palindromic.
Comparing `q(1) = det (S + Sᵀ)` with `q(-1) = det (S - Sᵀ)` through the palindromic coefficients
shows that `(-1)^k det (S + Sᵀ) ≡ det (S - Sᵀ)` modulo `4`, over any commutative ring. Since
`S - Sᵀ` is skew-symmetric its determinant is a square, so `(-1)^k det A ≡ 0` or `1` modulo `4`:
the signed determinant of an even symmetric integer matrix of even size is a discriminant. For
the Gram matrix `!![2a, b; b, 2c]` of a binary form this is `b² - 4ac ≡ b² (mod 4)`.

## Main results

* `Matrix.isSquare_det_of_transpose_eq_neg_of_diag_eq_zero`: a skew-symmetric matrix with zero
  diagonal over a field has square determinant.
* `Matrix.isSquare_det_of_transpose_eq_neg`: a skew-symmetric integer matrix has square
  determinant.
* `Matrix.reflect_det_X_smul_transpose_add`: `det (X • Sᵀ + S)` is its own reflection at the
  dimension.
* `Matrix.four_dvd_neg_one_pow_mul_det_add_transpose_sub_det_sub_transpose`: in dimension `2k`,
  `(-1)^k det (S + Sᵀ) ≡ det (S - Sᵀ)` modulo `4`.
* `Matrix.IsSymm.neg_one_pow_mul_det_modEq_zero_or_one`: for a symmetric integer matrix `A` of
  size `2k` with even diagonal, `(-1)^k det A ≡ 0` or `1` modulo `4`.
-/

public section

open Polynomial

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Skew-symmetric matrices -/

/-- **The determinant of a skew-symmetric matrix with zero diagonal over a field is a square.** -/
theorem isSquare_det_of_transpose_eq_neg_of_diag_eq_zero {K : Type*} [Field K]
    {M : Matrix ι ι K} (hM : Mᵀ = -M) (hd : ∀ i, M i i = 0) : IsSquare M.det := by
  by_cases h : M.det = 0
  · exact h ▸ IsSquare.zero
  -- The form `x, y ↦ xᵀ M y` is alternating: its terms pair off under swapping the indices.
  have halt : (toBilin' M).IsAlt := by
    intro x
    have hMji (i j : ι) : M j i = -M i j := by simpa using congrFun (congrFun hM i) j
    rw [toBilin'_apply, ← Finset.sum_product']
    refine Finset.sum_ninvolution Prod.swap (fun p ↦ ?_) (fun p hp hswap ↦ ?_) (by simp)
      Prod.swap_swap
    · simp only [Prod.fst_swap, Prod.snd_swap, hMji p.1 p.2]
      ring
    · obtain ⟨i, j⟩ := p
      obtain rfl : i = j := congrArg Prod.fst hswap.symm
      simp [hd] at hp
  -- A symplectic basis, relabelled by `ι`, carries the matrix `M` to a relabelling of `J`.
  obtain ⟨m, b, hb⟩ := halt.exists_basis_toMatrix_eq_J
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 h)
  let e := b.indexEquiv (Pi.basisFun K ι)
  let c := b.reindex e
  have hc : LinearMap.BilinForm.toMatrix c (toBilin' M) = reindex e e (J (Fin m) K) := by
    ext i j
    simp [c, LinearMap.BilinForm.toMatrix_apply, ← hb]
  have key := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K ι) c (toBilin' M)
  rw [hc, LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at key
  have hdet := congrArg det key
  rw [det_mul, det_mul, det_transpose, det_reindex_self, det_J] at hdet
  have hP : ((Pi.basisFun K ι).toMatrix c).det ≠ 0 := by
    rintro h0
    simp [h0] at hdet
  refine ⟨((Pi.basisFun K ι).toMatrix c).det⁻¹, ?_⟩
  field_simp
  linear_combination hdet

/-- **The determinant of a skew-symmetric integer matrix is a square.** -/
theorem isSquare_det_of_transpose_eq_neg {M : Matrix ι ι ℤ} (hM : Mᵀ = -M) : IsSquare M.det := by
  have hd (i : ι) : M i i = 0 := by
    have := congrFun (congrFun hM i) i
    simp only [transpose_apply, neg_apply] at this
    omega
  rw [← Rat.isSquare_intCast_iff, Int.cast_det]
  refine isSquare_det_of_transpose_eq_neg_of_diag_eq_zero ?_ (by simp [hd])
  rw [← transpose_map, hM]
  ext i j
  simp

/-! ### The determinant of `S + Sᵀ` modulo `4` -/

section Reflect

variable {R : Type*} [CommRing R]

/-- The polynomial `det (X • Sᵀ + S)` is its own reflection at the dimension: reflecting each
entry `X * Sⱼᵢ + Sᵢⱼ` at degree one transposes the matrix. -/
theorem reflect_det_X_smul_transpose_add (S : Matrix ι ι R) :
    reflect (Fintype.card ι) (det ((X : R[X]) • Sᵀ.map C + S.map C)) =
      det ((X : R[X]) • Sᵀ.map C + S.map C) := by
  have hP (i j : ι) : ((X : R[X]) • Sᵀ.map C + S.map C) i j = X * C (S j i) + C (S i j) := by
    simp
  have h := reflect_det_sum_eq_of_natDegree_le ((X : R[X]) • Sᵀ.map C + S.map C) (fun _ ↦ 1)
    fun i j ↦ by rw [hP]; compute_degree
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [h, ← det_transpose]
  congr 1
  refine Matrix.ext fun i j ↦ ?_
  rw [transpose_apply, of_apply, hP, hP, reflect_add, reflect_C, mul_comm X, reflect_C_mul,
    ← pow_one X, reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, mul_one]
  ring

/-- A sum over `0, …, 2k` of a family that is symmetric under `i ↦ 2k - i`, vanishes at the
middle index `k` and takes even values, is divisible by `4`: it is twice the sum over `i < k`. -/
private theorem four_dvd_sum_range (k : ℕ) (h : ℕ → R) (hsym : ∀ i ≤ 2 * k, h (2 * k - i) = h i)
    (hk : h k = 0) (h2 : ∀ i, 2 ∣ h i) : 4 ∣ ∑ i ∈ Finset.range (2 * k + 1), h i := by
  rw [show 2 * k + 1 = (k + 1) + k by ring, Finset.sum_range_add, Finset.sum_range_succ, hk,
    add_zero]
  have : ∑ x ∈ Finset.range k, h (k + 1 + x) = ∑ x ∈ Finset.range k, h x := by
    rw [← Finset.sum_range_reflect h k]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    rw [← hsym (k - 1 - x) (by omega)]
    congr 1
    omega
  rw [this, ← two_mul, show (4 : R) = 2 * 2 by norm_num]
  exact mul_dvd_mul_left 2 (Finset.dvd_sum fun i _ ↦ h2 i)

/-- **`det (S + Sᵀ)` modulo `4`.** For a square matrix `S` of size `2k` over a commutative ring,
`(-1)^k det (S + Sᵀ) ≡ det (S - Sᵀ)` modulo `4`. -/
theorem four_dvd_neg_one_pow_mul_det_add_transpose_sub_det_sub_transpose {k : ℕ}
    (hk : Fintype.card ι = 2 * k) (S : Matrix ι ι R) :
    4 ∣ (-1) ^ k * (S + Sᵀ).det - (S - Sᵀ).det := by
  -- The coefficients of `q = det (X • Sᵀ + S)` are palindromic, and `q(±1) = det (S ± Sᵀ)`.
  let q := det ((X : R[X]) • Sᵀ.map C + S.map C)
  have hdeg : q.natDegree < 2 * k + 1 := Nat.lt_succ_of_le (hk ▸ natDegree_det_X_add_C_le _ _)
  have hrefl : reflect (Fintype.card ι) q = q := reflect_det_X_smul_transpose_add S
  have hc (i : ℕ) (hi : i ≤ 2 * k) : q.coeff (2 * k - i) = q.coeff i := by
    conv_rhs => rw [← hrefl]
    rw [coeff_reflect, hk, revAt_le hi]
  have heval (r : R) : q.eval r = (r • Sᵀ + S).det := by
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j ↦ ?_
    simp only [RingHom.mapMatrix_apply, map_apply, coe_evalRingHom, add_apply, smul_apply,
      transpose_apply, eval_add, eval_mul, eval_X, eval_C, smul_eq_mul]
  have hq : (-1) ^ k * q.eval 1 - q.eval (-1) =
      (-1) ^ k * ∑ i ∈ Finset.range (2 * k + 1), q.coeff i * (1 - (-1) ^ (k + i)) := by
    rw [eval_eq_sum_range' hdeg, eval_eq_sum_range' hdeg, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have : ((-1 : R) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [pow_add]
    linear_combination (q.coeff i * (-1) ^ i) * this
  rw [heval, heval, one_smul, neg_one_smul, add_comm, neg_add_eq_sub] at hq
  rw [hq]
  refine dvd_mul_of_dvd_right (four_dvd_sum_range k _ (fun i hi ↦ ?_) ?_ fun i ↦ ?_) _
  · rw [hc i hi, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := k + i)]
    congr 3
    omega
  · rw [← two_mul, pow_mul, neg_one_sq, one_pow, sub_self, mul_zero]
  · rcases neg_one_pow_eq_or R (k + i) with hi | hi
    · simp [hi]
    · exact ⟨q.coeff i, by rw [hi]; ring⟩

end Reflect

/-! ### Even symmetric integer matrices -/

/-- **The signed determinant of an even symmetric integer matrix is a discriminant.** If `A` is a
symmetric integer matrix of size `2k` with even diagonal entries, then `(-1)^k det A` is
congruent to `0` or `1` modulo `4`. -/
theorem IsSymm.neg_one_pow_mul_det_modEq_zero_or_one {A : Matrix ι ι ℤ} (hA : A.IsSymm)
    (hd : ∀ i, Even (A i i)) {k : ℕ} (hk : Fintype.card ι = 2 * k) :
    (-1) ^ k * A.det ≡ 0 [ZMOD 4] ∨ (-1) ^ k * A.det ≡ 1 [ZMOD 4] := by
  -- Split `A = S + Sᵀ` along an ordering of the indices, halving the diagonal.
  let e := Fintype.equivFin ι
  let S : Matrix ι ι ℤ := of fun i j ↦ if e i < e j then A i j else if i = j then A i i / 2 else 0
  have hS : S + Sᵀ = A := by
    ext i j
    have hji : A j i = A i j := hA.apply i j
    obtain ⟨m, hm⟩ := hd i
    simp only [S, add_apply, transpose_apply, of_apply]
    rcases lt_trichotomy (e i) (e j) with h | h | h
    · simp [h, h.not_gt, e.injective.ne_iff.1 h.ne']
    · obtain rfl := e.injective h
      simp only [lt_irrefl, ite_false, ite_true]
      omega
    · simp [h, h.not_gt, e.injective.ne_iff.1 h.ne', hji]
  -- `det (S - Sᵀ)` is a square `x²`, and `x² ≡ 0` or `1` modulo `4`.
  obtain ⟨x, hx⟩ := isSquare_det_of_transpose_eq_neg (M := S - Sᵀ) (by simp)
  have h4 := four_dvd_neg_one_pow_mul_det_add_transpose_sub_det_sub_transpose hk S
  rw [hS, hx] at h4
  rcases Int.even_or_odd x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · left
    exact (Int.modEq_iff_dvd.2 (by simpa using h4)).symm.trans
      (Int.modEq_iff_dvd.2 ⟨-(y * y), by ring⟩)
  · right
    exact (Int.modEq_iff_dvd.2 (by simpa using h4)).symm.trans
      (Int.modEq_iff_dvd.2 ⟨-(y * y + y), by ring⟩)

end Matrix
