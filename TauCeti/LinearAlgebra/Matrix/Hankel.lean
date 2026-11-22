/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Hankel matrices and Hankel determinants

The `n × n` Hankel matrix of a sequence `m : ℕ → R` over a commutative ring is the matrix
`(m (i + j))_{i,j<n}`, and its determinant is the Hankel determinant `Δ_n(m)`, with `Δ₀ = 1`.
When `m k = L (X ^ k)` are the moments of a linear functional `L` on `R[X]`, the Hankel matrix is
the Gram matrix of the bilinear form `(p, q) ↦ L (p * q)` on the monomials `1, X, …, X ^ (n - 1)`.
Replacing these monomials, in the rows and in the columns, by polynomials `p i` and `q j` of degree
at most `i` and `j` multiplies the Gram determinant by the product of their coefficients in those
degrees. In particular the Gram determinant of monic polynomials of degrees `0, 1, …, n - 1` is
the Hankel determinant. This is the step behind the determinant formulas for orthogonal
polynomials, where the Gram matrix of the monic orthogonal polynomials is diagonal, and behind the
Hankel determinant estimates in Dimitrov's proof of the Schinzel–Zassenhaus conjecture.

The shifted determinant `D_n(a) = det (a (i + j + 1))_{i,j<n}` of a sequence `a`, in which the
coefficient `a 0` does not appear, is `hankelDet (fun k => a (k + 1)) n`.

## Main definitions

* `TauCeti.hankelMatrix m n`: the Hankel matrix `(m (i + j))_{i,j<n}`.
* `TauCeti.hankelDet m n`: its determinant.

## Main results

* `TauCeti.hankelDet_zero`, `TauCeti.hankelDet_one`, `TauCeti.hankelDet_two`: the Hankel
  determinants of size at most two.
* `RingHom.map_hankelDet`, `Int.cast_hankelDet`: Hankel determinants commute with ring
  homomorphisms, in particular with the cast from `ℤ`.
* `TauCeti.one_le_norm_hankelDet_intCast`: a nonzero integer Hankel determinant has norm at least
  `1` in `ℝ` or `ℂ`.
* `TauCeti.of_apply_mul_eq_mul_hankelMatrix_mul`: the Gram matrix of `(p, q) ↦ L (p * q)` on two
  families of polynomials factors through the Hankel matrix of the moments of `L`.
* `TauCeti.det_apply_mul_eq_prod_coeff_mul_hankelDet`,
  `TauCeti.det_apply_mul_eq_hankelDet_of_monic`: the invariance of the Hankel determinant under a
  triangular, respectively monic, change of basis.

## References

* T. S. Chihara, *An Introduction to Orthogonal Polynomials*, Gordon and Breach, 1978, Ch. I,
  §3.
* V. Dimitrov, *A proof of the Schinzel–Zassenhaus conjecture on polynomials*, §4, proof of
  Theorem 4.
-/

public section

open Polynomial Matrix

namespace TauCeti

variable {R : Type*}

section HankelMatrix

/-- The `n × n` Hankel matrix `(m (i + j))_{i,j<n}` of a sequence `m`. -/
def hankelMatrix (m : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => m (i + j)

@[simp]
theorem hankelMatrix_apply (m : ℕ → R) (n : ℕ) (i j : Fin n) :
    hankelMatrix m n i j = m (i + j) :=
  (rfl)

@[simp]
theorem hankelMatrix_transpose (m : ℕ → R) (n : ℕ) : (hankelMatrix m n)ᵀ = hankelMatrix m n := by
  ext i j
  simp [add_comm]

theorem isSymm_hankelMatrix (m : ℕ → R) (n : ℕ) : (hankelMatrix m n).IsSymm :=
  IsSymm.ext fun i j => by simp [add_comm]

@[simp]
theorem hankelMatrix_map {S : Type*} (m : ℕ → R) (n : ℕ) (f : R → S) :
    (hankelMatrix m n).map f = hankelMatrix (fun k => f (m k)) n := by
  ext i j
  simp

variable [CommRing R]

/-- The Hankel determinant `Δ_n(m) = det (m (i + j))_{i,j<n}` of a sequence `m`; `Δ₀ = 1`. -/
def hankelDet (m : ℕ → R) (n : ℕ) : R :=
  (hankelMatrix m n).det

@[simp]
theorem det_hankelMatrix (m : ℕ → R) (n : ℕ) : (hankelMatrix m n).det = hankelDet m n :=
  (rfl)

@[simp]
theorem hankelDet_zero (m : ℕ → R) : hankelDet m 0 = 1 := by
  simp [← det_hankelMatrix]

@[simp]
theorem hankelDet_one (m : ℕ → R) : hankelDet m 1 = m 0 := by
  simp [← det_hankelMatrix]

theorem hankelDet_two (m : ℕ → R) : hankelDet m 2 = m 0 * m 2 - m 1 ^ 2 := by
  simp [← det_hankelMatrix, det_fin_two, sq]

end HankelMatrix

/-- Hankel determinants commute with ring homomorphisms. -/
theorem _root_.RingHom.map_hankelDet [CommRing R] {S : Type*} [CommRing S] (f : R →+* S)
    (m : ℕ → R) (n : ℕ) : f (hankelDet m n) = hankelDet (fun k => f (m k)) n := by
  rw [← det_hankelMatrix, f.map_det, RingHom.mapMatrix_apply, hankelMatrix_map, det_hankelMatrix]

/-- The Hankel determinants of an integer sequence, computed in any commutative ring, are the casts
of its integer Hankel determinants. -/
@[simp, norm_cast]
theorem _root_.Int.cast_hankelDet [CommRing R] (m : ℕ → ℤ) (n : ℕ) :
    ((hankelDet m n : ℤ) : R) = hankelDet (fun k => (m k : R)) n :=
  (Int.castRingHom R).map_hankelDet m n

/-- A nonzero Hankel determinant of an integer sequence has norm at least `1` in `ℝ` or `ℂ`. -/
theorem one_le_norm_hankelDet_intCast {K : Type*} [RCLike K] {m : ℕ → ℤ} {n : ℕ}
    (h : hankelDet m n ≠ 0) : 1 ≤ ‖hankelDet (fun k => (m k : K)) n‖ := by
  rw [← Int.cast_hankelDet, ← RCLike.ofReal_intCast, RCLike.norm_ofReal, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h

section ChangeOfBasis

variable [CommRing R] {n : ℕ} {L : R[X] →ₗ[R] R}

/-- The Gram matrix `(L (p i * q j))_{i,j<n}` of two families of polynomials of degree less than
`n` is `P * H * Qᵀ`, where `H` is the Hankel matrix of the moments `L (X ^ k)` and the rows of `P`
and `Q` are the coefficients of the `p i` and the `q j`. -/
theorem of_apply_mul_eq_mul_hankelMatrix_mul {p q : Fin n → R[X]}
    (hp : ∀ i, (p i).natDegree < n) (hq : ∀ j, (q j).natDegree < n) :
    (Matrix.of fun i j => L (p i * q j)) =
      Matrix.of (fun i k : Fin n => (p i).coeff k) * hankelMatrix (fun k => L (X ^ k)) n *
        (Matrix.of fun j l : Fin n => (q j).coeff l)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, of_apply, transpose_apply, hankelMatrix_apply, Finset.sum_mul]
  -- expand `p i` and `q j` in the monomials `X ^ k`, `k < n`, and use the linearity of `L`
  conv_lhs => rw [(p i).as_sum_range_C_mul_X_pow' (hp i), (q j).as_sum_range_C_mul_X_pow' (hq j)]
  simp_rw [← Fin.sum_univ_eq_sum_range, Finset.sum_mul, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [show C ((p i).coeff k) * X ^ (k : ℕ) * (C ((q j).coeff l) * X ^ (l : ℕ)) =
      ((p i).coeff k * (q j).coeff l) • X ^ ((k : ℕ) + l) by
        rw [smul_eq_C_mul, C_mul, pow_add]; ring,
    map_smul, smul_eq_mul]
  ring

/-- **Invariance of the Hankel determinant under a triangular change of basis.** If `p i` and
`q i` have degree at most `i`, then the Gram determinant `det (L (p i * q j))_{i,j<n}` is the
Hankel determinant of the moments `L (X ^ k)` times the coefficients of the `p i` and the `q i` in
degree `i`. -/
theorem det_apply_mul_eq_prod_coeff_mul_hankelDet {p q : Fin n → R[X]}
    (hp : ∀ i, (p i).natDegree ≤ i) (hq : ∀ j, (q j).natDegree ≤ j) :
    (Matrix.of fun i j => L (p i * q j)).det =
      (∏ i, (p i).coeff i) * (∏ j, (q j).coeff j) * hankelDet (fun k => L (X ^ k)) n := by
  -- the coefficient matrix of such a family is lower triangular
  have hdet {r : Fin n → R[X]} (hr : ∀ i, (r i).natDegree ≤ i) :
      (Matrix.of fun i k : Fin n => (r i).coeff k).det = ∏ i, (r i).coeff i :=
    det_of_isLowerTriangular _ fun i k hik => coeff_eq_zero_of_natDegree_lt ((hr i).trans_lt hik)
  rw [of_apply_mul_eq_mul_hankelMatrix_mul (fun i => (hp i).trans_lt i.isLt)
      (fun j => (hq j).trans_lt j.isLt), det_mul, det_mul, det_transpose, hdet hp, hdet hq,
    det_hankelMatrix]
  ring

/-- **Invariance of the Hankel determinant under a monic change of basis.** Replacing the powers
`X ^ i` in the rows and the columns of the moment matrix `(L (X ^ i * X ^ j))_{i,j<n}` by monic
polynomials of degree `i` leaves its determinant, the Hankel determinant of the moments
`L (X ^ k)`, unchanged. -/
theorem det_apply_mul_eq_hankelDet_of_monic {p q : Fin n → R[X]} (hp : ∀ i, (p i).Monic)
    (hpd : ∀ i, (p i).natDegree = i) (hq : ∀ j, (q j).Monic) (hqd : ∀ j, (q j).natDegree = j) :
    (Matrix.of fun i j => L (p i * q j)).det = hankelDet (fun k => L (X ^ k)) n := by
  rw [det_apply_mul_eq_prod_coeff_mul_hankelDet (fun i => (hpd i).le) (fun j => (hqd j).le)]
  have hp1 (i : Fin n) : (p i).coeff i = 1 := by rw [← hpd i]; exact (hp i).coeff_natDegree
  have hq1 (j : Fin n) : (q j).coeff j = 1 := by rw [← hqd j]; exact (hq j).coeff_natDegree
  simp [hp1, hq1]

end ChangeOfBasis

end TauCeti
