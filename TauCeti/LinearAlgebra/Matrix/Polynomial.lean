/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic.ComputeDegree
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Algebra.Polynomial.Reverse

/-!
# Coefficients and determinants of polynomial matrices

Let `A` be a square matrix with polynomial entries whose `j`-th column has degree at most `e j`.
Every term of the Leibniz expansion of `det A` then has degree at most `∑ j, e j`, so `det A` does
too, and its coefficient in that degree is the determinant of the scalar matrix of
top coefficients `(A i j).coeff (e j)`. This is the standard way to show that a determinant of
polynomials is nonzero, by exhibiting a nonsingular matrix of leading coefficients.

Under the same column bounds, reflecting `det A` at `∑ j, e j`, that is, reading it in the
reciprocal variable `X ^ (∑ j, e j) * det A (1 / X)`, gives the determinant of the matrix whose
`j`-th column is reflected at `e j` (`Matrix.reflect_det_sum_eq_of_natDegree_le`). For instance,
when all entries have degree at most one, `det (X • Bᵀ + B)` is its own reflection at the
dimension, being the determinant of the transpose (`Matrix.reflect_det_X_smul_transpose_add`).

Taking entrywise coefficients commutes with multiplication by constant matrices on either side.
In particular, linear coefficients of matrix-valued curves commute with constant conjugation.

Evaluating a polynomial in a matrix commutes with applying a ring homomorphism to the coefficients
and to the entries (`Matrix.aeval_map`). Natural matrix identities valid at unit parameters
extend to all parameters by polynomial specialization (`Matrix.identity_of_units`).
-/

public section

namespace Matrix

open Polynomial

/-- A matrix identity natural under coefficient homomorphisms holds at every parameter if
it holds at every unit of the Laurent polynomial ring. Embed the indeterminate into Laurent
polynomials, where it is a unit, then use injectivity and evaluate back in the original ring. -/
theorem identity_of_units {R : Type u} [CommRing R] {m n : Type*}
    (F G : (S : Type u) → [CommRing S] → S → Matrix m n S)
    (hF : ∀ {S : Type u} [CommRing S] (f : Polynomial R →+* S),
      (F (Polynomial R) X).map f = F S (f X))
    (hG : ∀ {S : Type u} [CommRing S] (f : Polynomial R →+* S),
      (G (Polynomial R) X).map f = G S (f X))
    (hunit : ∀ q : (LaurentPolynomial R)ˣ,
      F _ (q : LaurentPolynomial R) = G _ (q : LaurentPolynomial R))
    (s : R) : F R s = G R s := by
  have hpoly : F (Polynomial R) X = G (Polynomial R) X := by
    apply Matrix.map_injective Polynomial.toLaurent_injective
    obtain ⟨q, hq⟩ := LaurentPolynomial.isUnit_T (R := R) 1
    simpa only [hF Polynomial.toLaurent, hG Polynomial.toLaurent,
      Polynomial.toLaurent_X, ← hq] using hunit q
  have h := congrArg (fun A ↦ A.map (Polynomial.evalRingHom s)) hpoly
  have hX : (Polynomial.evalRingHom s) X = s := Polynomial.eval_X
  rw [hF (Polynomial.evalRingHom s), hG (Polynomial.evalRingHom s), hX] at h
  exact h

variable {n R : Type*} [Fintype n] [DecidableEq n]

/-- Evaluating a polynomial in a matrix commutes with applying a ring homomorphism to the
coefficients of the polynomial and to the entries of the matrix. -/
@[simp]
theorem aeval_map {R S : Type*} [CommSemiring R] [CommSemiring S] (A : Matrix n n R)
    (φ : R →+* S) (f : R[X]) :
    aeval (A.map φ) (f.map φ) = (aeval A f).map φ := by
  refine (map_aeval_eq_aeval_map (S := Matrix n n R) (U := Matrix n n S) (φ := φ)
    (ψ := φ.mapMatrix) (RingHom.ext fun r ↦ ?_) f A).symm
  ext i j
  by_cases h : i = j <;> simp [algebraMap_matrix_apply, h]

omit [DecidableEq n] in
/-- Taking an entrywise polynomial coefficient commutes with multiplication on the left by a
constant matrix. -/
@[simp]
theorem map_coeff_map_C_mul [Semiring R] {m p : Type*}
    (A : Matrix m n R) (P : Matrix n p R[X])
    (d : ℕ) :
    (A.map C * P).map (fun p ↦ p.coeff d) = A * P.map (fun p ↦ p.coeff d) := by
  ext i j
  simp [Matrix.mul_apply, finsetSum_coeff, coeff_C_mul]

omit [DecidableEq n] in
/-- Taking an entrywise polynomial coefficient commutes with multiplication on the right by a
constant matrix. -/
@[simp]
theorem map_coeff_mul_map_C [Semiring R] {m p : Type*}
    (P : Matrix m n R[X]) (A : Matrix n p R)
    (d : ℕ) :
    (P * A.map C).map (fun p ↦ p.coeff d) = P.map (fun p ↦ p.coeff d) * A := by
  ext i j
  simp [Matrix.mul_apply, finsetSum_coeff, coeff_mul_C]

variable [CommRing R]

/-- If the `j`-th column of a polynomial matrix `A` has degree at most `e j`, then the coefficient
of `det A` in degree `∑ j, e j` is the determinant of the matrix of coefficients of the entries
in the degrees `e j`. -/
theorem coeff_det_sum_eq_of_natDegree_le (A : Matrix n n R[X]) (e : n → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ e j) :
    A.det.coeff (∑ j, e j) = (of fun i j ↦ (A i j).coeff (e j)).det := by
  simp only [det_apply', finsetSum_coeff, coeff_intCast_mul, of_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [coeff_prod_sum_eq_of_natDegree_le _ _ _ fun j _ ↦ h (σ j) j]

/-- If the `j`-th column of a polynomial matrix `A` has degree at most `e j`, then `det A` has
degree at most `∑ j, e j`. -/
theorem natDegree_det_le_of_natDegree_le (A : Matrix n n R[X]) (e : n → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ e j) :
    A.det.natDegree ≤ ∑ j, e j := by
  rw [det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ ↦ ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_intCast, zero_add]
  exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ ↦ h (σ j) j)

/-- If the `j`-th column of a polynomial matrix `A` has degree at most `e j`, then the reflection
of `det A` at `∑ j, e j` is the determinant of the matrix whose `j`-th column is reflected at
`e j`. -/
theorem reflect_det_sum_eq_of_natDegree_le (A : Matrix n n R[X]) (e : n → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ e j) :
    A.det.reflect (∑ j, e j) = (of fun i j ↦ (A i j).reflect (e j)).det := by
  let ρ : R[X] →+ R[X] := ⟨⟨reflect (∑ j, e j), reflect_zero⟩, fun f g ↦ reflect_add f g _⟩
  have hsum := map_sum ρ (fun σ : Equiv.Perm n ↦ ((Equiv.Perm.sign σ : ℤ) : R[X]) *
    ∏ i, A (σ i) i) Finset.univ
  simp only [ρ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hsum
  rw [det_apply', det_apply', hsum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← C_eq_intCast, reflect_C_mul, reflect_prod _ _ _ fun i _ ↦ h (σ i) i, C_eq_intCast]
  simp only [of_apply]

/-- The polynomial `det (X • Sᵀ + S)` is its own reflection at the dimension: reflecting each
entry `X * Sⱼᵢ + Sᵢⱼ` at degree one transposes the matrix. -/
theorem reflect_det_X_smul_transpose_add (S : Matrix n n R) :
    reflect (Fintype.card n) (det ((X : R[X]) • Sᵀ.map C + S.map C)) =
      det ((X : R[X]) • Sᵀ.map C + S.map C) := by
  have hP (i j : n) : ((X : R[X]) • Sᵀ.map C + S.map C) i j = C (S j i) * X + C (S i j) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, transpose_apply, map_apply, smul_eq_mul]
    ring
  have h := reflect_det_sum_eq_of_natDegree_le ((X : R[X]) • Sᵀ.map C + S.map C) (fun _ ↦ 1)
    fun i j ↦ by rw [hP]; compute_degree
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [h, ← det_transpose]
  congr 1
  ext i j
  simp [hP, reflect_C_mul, add_comm]

end Matrix
