/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Factorial determinant bounds for norms, embeddings and logarithms

For a square matrix `A` of size `n` whose row `i` is bounded entrywise by `b i`,
`Matrix.abv_det_le_factorial_prod` bounds `abv A.det` by `n! · ∏ i, b i` for every absolute value
`abv`. This file records the forms of that bound used for interpolation determinants:

* the norm form over a normed commutative ring with multiplicative norm, such as `ℂ`;
* the form after a ring homomorphism `σ` into such a ring, applied entrywise, such as a complex
  embedding of a number field, where `‖σ x‖` is `NumberField.place σ x`;
* the logarithmic form for a real-valued absolute value and a nonzero determinant.

In the logarithmic form every `b i` is positive: a nonzero determinant has no zero row, so each
row has an entry of positive absolute value.

## Main results

* `Matrix.norm_det_le_factorial_prod`: `‖A.det‖ ≤ n! · ∏ i, b i` when `‖A i j‖ ≤ b i`.
* `Matrix.norm_map_det_le_factorial_prod`: `‖σ A.det‖ ≤ n! · ∏ i, b i` when `‖σ (A i j)‖ ≤ b i`.
* `Matrix.log_abv_det_le`: `log (abv A.det) ≤ log n! + ∑ i, log (b i)` when `A.det ≠ 0`.

## References

* M. Waldschmidt, *Diophantine approximation on linear algebraic groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Lemma 2.8, p. 43.
-/

public section

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Factorial determinant bound, norm form.** Over a normed commutative ring with multiplicative
norm, such as `ℂ`, if row `i` of `A` is bounded entrywise in norm by `b i`, then
`‖A.det‖ ≤ n! · ∏ i, b i`, where `n` is the size of the matrix. -/
theorem norm_det_le_factorial_prod {R : Type*} [NormedCommRing R] [NormMulClass R]
    (A : Matrix n n R) {b : n → ℝ} (hA : ∀ i j, ‖A i j‖ ≤ b i) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * ∏ i, b i :=
  abv_det_le_factorial_prod A (IsAbsoluteValue.toAbsoluteValue norm) hA

/-- **Factorial determinant bound after a ring homomorphism.** If `σ : R →+* F` maps into a normed
commutative ring with multiplicative norm and `‖σ (A i j)‖ ≤ b i` for all `i, j`, then
`‖σ A.det‖ ≤ n! · ∏ i, b i`. For a complex embedding `σ` of a number field, `‖σ x‖` is
`NumberField.place σ x`. -/
theorem norm_map_det_le_factorial_prod {R F : Type*} [CommRing R] [NormedCommRing F]
    [NormMulClass F] (σ : R →+* F) (A : Matrix n n R) {b : n → ℝ}
    (hA : ∀ i j, ‖σ (A i j)‖ ≤ b i) :
    ‖σ A.det‖ ≤ (Fintype.card n).factorial * ∏ i, b i := by
  rw [σ.map_det]
  exact norm_det_le_factorial_prod _ hA

/-- **Factorial determinant bound, logarithmic form.** For a real-valued absolute value `abv`, if
row `i` of `A` is bounded entrywise in `abv` by `b i` and `A.det ≠ 0`, then
`log (abv A.det) ≤ log n! + ∑ i, log (b i)`, where `n` is the size of the matrix. Every `b i` is
then positive, since a nonzero determinant has no zero row. -/
theorem log_abv_det_le {R : Type*} [CommRing R] (A : Matrix n n R) (abv : AbsoluteValue R ℝ)
    {b : n → ℝ} (hA : ∀ i j, abv (A i j) ≤ b i) (hdet : A.det ≠ 0) :
    Real.log (abv A.det) ≤ Real.log (Fintype.card n).factorial + ∑ i, Real.log (b i) := by
  have hb : ∀ i, 0 < b i := by
    intro i
    by_contra! h
    exact hdet (det_eq_zero_of_row_eq_zero i fun j ↦
      abv.eq_zero.mp (le_antisymm ((hA i j).trans h) (abv.nonneg _)))
  rw [← Real.log_prod fun i _ ↦ (hb i).ne', ← Real.log_mul (by positivity)
    (prod_pos fun i _ ↦ hb i).ne']
  exact Real.log_le_log (abv.pos hdet) (abv_det_le_factorial_prod A abv hA)

end Matrix
