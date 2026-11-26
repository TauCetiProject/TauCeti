/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

import TauCeti.Algebra.Polynomial.Homogenize

/-!
# Homogeneous substitution on univariate polynomials

View a polynomial of degree at most `n` as a binary form of degree `n`, with the second
variable specialized to one. A matrix with rows `(a, b)` and `(c, d)` acts by substituting
`a X + b` and `c X + d` into the two homogeneous variables. This works over any commutative
semiring, including when the degree drops or the matrix is singular. The operation transports
`MvPolynomial.linearSubstRep` to the univariate coordinates and composes in reverse matrix order.
-/

public section

open Matrix

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- Substitute a matrix in the degree-`n` homogenization of `p` and dehomogenize at `(X, 1)`.
Only coefficients of degree at most `n` enter the substitution. -/
noncomputable def homogSubst (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) : R[X] :=
  MvPolynomial.aeval ![X, 1] (MvPolynomial.linearSubst M (p.homogenize n))

/-- The substitution is the evaluation of the homogenization at the two affine linear forms. -/
theorem homogSubst_eq_aeval (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    p.homogSubst n M = MvPolynomial.aeval
      ![C (M 0 0) * X + C (M 0 1), C (M 1 0) * X + C (M 1 1)] (p.homogenize n) := by
  rw [homogSubst, MvPolynomial.aeval_linearSubst]
  congr 1
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Homogeneous substitution is division-free, with one term for each pair of exponents
adding to `n`. -/
theorem homogSubst_eq_sum (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    p.homogSubst n M =
      ∑ k ∈ Finset.range (n + 1), C (p.coeff k) *
        ((C (M 0 0) * X + C (M 0 1)) ^ k * (C (M 1 0) * X + C (M 1 1)) ^ (n - k)) := by
  rw [homogSubst_eq_aeval, aeval_homogenize_eq_sum]
  simpa only [mul_assoc, C_eq_algebraMap] using
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l ↦ C (p.coeff k) *
        ((C (M 0 0) * X + C (M 0 1)) ^ k * (C (M 1 0) * X + C (M 1 1)) ^ l)) n)

/-- The homogeneous substitution of degree `n` has degree at most `n`. -/
theorem natDegree_homogSubst_le (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    (p.homogSubst n M).natDegree ≤ n := by
  rw [homogSubst_eq_aeval]
  apply (isHomogeneous_homogenize p).natDegree_aeval_le
  intro i
  fin_cases i <;> exact natDegree_linear_le

/-- Homogenizing the substituted polynomial recovers the substituted binary form. -/
@[simp]
theorem homogenize_homogSubst (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    (p.homogSubst n M).homogenize n = MvPolynomial.linearSubst M (p.homogenize n) :=
  homogenize_eq_of_isHomogeneous ((isHomogeneous_homogenize p).linearSubst M) (by rw [homogSubst])

/-- In univariate coordinates homogeneous substitution is the action of
`MvPolynomial.linearSubstRep` on binary forms of degree `n`. -/
theorem homogSubst_eq_linearSubstRep (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    p.homogSubst n M = MvPolynomial.aeval ![X, 1]
      (MvPolynomial.linearSubstRep (Fin 2) R n (MulOpposite.op M)
        ⟨p.homogenize n, isHomogeneous_homogenize p⟩ : MvPolynomial (Fin 2) R) := by
  rw [MvPolynomial.coe_linearSubstRep_apply, MulOpposite.unop_op, homogSubst]

/-- The identity matrix recovers the polynomial when its degree is at most the formal degree. -/
@[simp]
theorem homogSubst_one (p : R[X]) {n : ℕ} (hp : p.natDegree ≤ n) :
    p.homogSubst n 1 = p := by
  simp [homogSubst, hp]

/-- Substituting first along `M` and then along `N` substitutes along `M * N`. -/
theorem homogSubst_mul_matrix (p : R[X]) (n : ℕ) (M N : Matrix (Fin 2) (Fin 2) R) :
    p.homogSubst n (M * N) = (p.homogSubst n M).homogSubst n N := by
  conv_rhs => rw [homogSubst]
  rw [homogenize_homogSubst, ← MvPolynomial.linearSubst_mul_apply, homogSubst]

/-- Substituting into the zero polynomial gives zero. -/
@[simp]
theorem zero_homogSubst (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    (0 : R[X]).homogSubst n M = 0 := by
  simp [homogSubst]

/-- Homogeneous substitution is additive in the input polynomial. -/
@[simp]
theorem add_homogSubst (p q : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    (p + q).homogSubst n M = p.homogSubst n M + q.homogSubst n M := by
  simp [homogSubst]

/-- Homogeneous substitution commutes with multiplication by a constant polynomial. -/
@[simp]
theorem C_mul_homogSubst (r : R) (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    (C r * p).homogSubst n M = C r * p.homogSubst n M := by
  simp [homogSubst]

/-- Rescaling the matrix by a scalar multiplies the substituted polynomial by the
scalar to the formal degree. -/
theorem homogSubst_smul_matrix (p : R[X]) (n : ℕ) (r : R) (M : Matrix (Fin 2) (Fin 2) R) :
    p.homogSubst n (r • M) = r ^ n • p.homogSubst n M := by
  simp [homogSubst, (isHomogeneous_homogenize p).linearSubst_smul]

/-- Homogeneous substitution in a product adds the two formal degrees. -/
theorem mul_homogSubst (p q : R[X]) {m n : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (M : Matrix (Fin 2) (Fin 2) R) :
    (p * q).homogSubst (m + n) M = p.homogSubst m M * q.homogSubst n M := by
  simp [homogSubst, homogenize_mul p q hp hq]

/-- Homogeneous substitution commutes with a map of coefficient semirings. -/
@[simp]
theorem map_homogSubst {S : Type*} [CommSemiring S] (φ : R →+* S)
    (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    (p.homogSubst n M).map φ = (p.map φ).homogSubst n (M.map φ) := by
  simp only [homogSubst, ← MvPolynomial.aeval_X_one_map, MvPolynomial.map_linearSubst,
    homogenize_map]

end Polynomial
