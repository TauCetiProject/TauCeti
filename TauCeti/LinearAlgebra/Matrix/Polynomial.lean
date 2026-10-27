/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.ComputeDegree
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Algebra.Polynomial.Reverse

/-!
# The top coefficient and the reflection of a determinant of polynomials

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
-/

public section

namespace Matrix

open Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- If the `j`-th column of a polynomial matrix `A` has degree at most `e j`, then the coefficient
of `det A` in degree `∑ j, e j` is the determinant of the matrix of coefficients of the entries
in the degrees `e j`. -/
theorem coeff_det_sum_eq_of_natDegree_le (A : Matrix n n R[X]) (e : n → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ e j) :
    A.det.coeff (∑ j, e j) = (of fun i j ↦ (A i j).coeff (e j)).det := by
  simp only [det_apply', finsetSum_coeff, coeff_intCast_mul, of_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [coeff_prod_sum_eq_of_natDegree_le _ _ _ fun j _ ↦ h (σ j) j]

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
    simp only [add_apply, smul_apply, transpose_apply, map_apply, smul_eq_mul]
    ring
  have h := reflect_det_sum_eq_of_natDegree_le ((X : R[X]) • Sᵀ.map C + S.map C) (fun _ ↦ 1)
    fun i j ↦ by rw [hP]; compute_degree
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [h, ← det_transpose]
  congr 1
  ext i j
  simp [hP, reflect_C_mul, add_comm]

end Matrix
