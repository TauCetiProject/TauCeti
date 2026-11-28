/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Factorial determinant bounds for norms and logarithms

For a square matrix `A` of size `n` whose row `i` is bounded entrywise by `b i`,
`Matrix.abv_det_le_factorial_prod` bounds `abv A.det` by `n! · ∏ i, b i` for every absolute value
`abv`. This file records the forms of that bound used for interpolation determinants:

* the norm form over a normed commutative ring with `‖1‖ = 1`, such as `ℂ`; for a matrix over a
  number field after a complex embedding `σ`, apply it to `σ.mapMatrix A` and use `σ.map_det`;
* the logarithmic form for a real-valued absolute value and a nonzero determinant.

In the logarithmic form every `b i` is positive: a nonzero determinant has no zero row, so each
row has an entry of positive absolute value.

## Main results

* `Matrix.norm_det_le_factorial_prod`: `‖A.det‖ ≤ n! · ∏ i, b i` when `‖A i j‖ ≤ b i`.
* `Matrix.norm_det_le_factorial_mul_pow`: `‖A.det‖ ≤ n! · c ^ n` when `‖A i j‖ ≤ c`; for a
  nonempty index type it needs no `‖1‖ = 1` (`Matrix.norm_det_le_factorial_mul_pow_of_nonempty`).
* `Matrix.norm_adjugate_apply_le`: the entries of the adjugate of a matrix of size `k + 1` with
  entries of norm at most `c` have norm at most `k! · c ^ k`.
* `Matrix.log_abv_det_le`: `log (abv A.det) ≤ log n! + ∑ i, log (b i)` when `A.det ≠ 0`.

## References

* M. Waldschmidt, *Diophantine approximation on linear algebraic groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Lemma 2.8, p. 43.
-/

public section

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Factorial determinant bound, norm form.** Over a normed commutative ring with `‖1‖ = 1`,
such as `ℂ`, if row `i` of `A` is bounded entrywise in norm by `b i`, then
`‖A.det‖ ≤ n! · ∏ i, b i`, where `n` is the size of the matrix. The norm need only be
submultiplicative. -/
theorem norm_det_le_factorial_prod {R : Type*} [NormedCommRing R] [NormOneClass R]
    (A : Matrix n n R) {b : n → ℝ} (hA : ∀ i j, ‖A i j‖ ≤ b i) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * ∏ i, b i := by
  -- Each of the `n!` Leibniz terms takes one entry from every row.
  have hterm (σ : Equiv.Perm n) : ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ ∏ i, b i := by
    rw [norm_units_zsmul]
    calc ‖∏ i, A (σ i) i‖ ≤ ∏ i, ‖A (σ i) i‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ i, b (σ i) := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hA _ _
      _ = ∏ i, b i := Equiv.prod_comp σ b
  rw [det_apply]
  calc ‖∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm n, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm n, ∏ i, b i := sum_le_sum fun σ _ ↦ hterm σ
    _ = (Fintype.card n).factorial * ∏ i, b i := by
      rw [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- **Factorial determinant bound for a nonempty index type.** Over a seminormed commutative ring,
with no assumption on `‖1‖`, if the index type is nonempty and every entry of `A` has norm at most
`c`, then `‖A.det‖ ≤ n! · c ^ n`, where `n` is the size of the matrix. -/
theorem norm_det_le_factorial_mul_pow_of_nonempty {R : Type*} [SeminormedCommRing R] [Nonempty n]
    {A : Matrix n n R} {c : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * c ^ Fintype.card n := by
  -- Each Leibniz term is a nonempty product of entries.
  have hterm (σ : Equiv.Perm n) : ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ c ^ Fintype.card n := by
    rw [norm_units_zsmul]
    refine (TauCeti.norm_prod_le_prod_norm_of_nonempty univ_nonempty _).trans ?_
    simpa using prod_le_prod₀ (s := univ) (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hA (σ i) i
  rw [det_apply]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun σ _ ↦ hterm σ).trans_eq ?_)
  rw [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- **Factorial determinant bound for a constant bound.** Over a seminormed commutative ring with
`‖1‖ = 1`, if every entry of `A` has norm at most `c`, then `‖A.det‖ ≤ n! · c ^ n`, where `n` is
the size of the matrix. -/
theorem norm_det_le_factorial_mul_pow {R : Type*} [SeminormedCommRing R] [NormOneClass R]
    {A : Matrix n n R} {c : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A.det‖ ≤ (Fintype.card n).factorial * c ^ Fintype.card n := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  exact norm_det_le_factorial_mul_pow_of_nonempty hA

/-- **Entrywise bound for the adjugate.** Over a seminormed commutative ring with `‖1‖ = 1`, if
every entry of a matrix `A` of size `k + 1` has norm at most `c`, then every entry of its adjugate
has norm at most `k! · c ^ k`. -/
theorem norm_adjugate_apply_le {R : Type*} [SeminormedCommRing R] [NormOneClass R] {k : ℕ}
    {A : Matrix (Fin (k + 1)) (Fin (k + 1)) R} {c : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ c)
    (i j : Fin (k + 1)) : ‖A.adjugate i j‖ ≤ k.factorial * c ^ k := by
  have h := norm_det_le_factorial_mul_pow (A := A.submatrix j.succAbove i.succAbove)
    fun _ _ ↦ hA _ _
  rw [adjugate_fin_succ_eq_det_submatrix]
  -- The sign `(-1) ^ (j + i)` is `1` or `-1`.
  rcases neg_one_pow_eq_or R (j + i : ℕ) with hs | hs <;> simpa [hs] using h

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
