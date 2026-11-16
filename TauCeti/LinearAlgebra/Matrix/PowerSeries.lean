/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Matrices of formal power series

Let `A` be a square matrix over a nontrivial ring `R`, indexed by a finite type `ι`, and let
`M = (1 + X²) I - X A` in the ring of matrices of formal power series over `R`. This file proves
that no column of a right inverse of `M` has polynomial entries
(`Matrix.exists_coeff_ne_zero_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one`); in particular `M` has
no polynomial right inverse unless `ι` is empty. Indeed the coefficient matrices of a right inverse
`N` satisfy `N_{n+2} = A N_{n+1} - N_n`, so if a column of them vanishes from some degree on, then
it vanishes in every degree by descending induction, against `N_0 = I`.

## Main results

* `Matrix.exists_coeff_ne_zero_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one`: every column of a
  right inverse of `(1 + X²) I - X A` has nonzero coefficients in arbitrarily high degree.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Section 3, where `(1 + X²) I - X A` is the Hilbert-series denominator of a
  preprojective algebra.
-/

public section

namespace Matrix

open PowerSeries

/-- **No column of a right inverse of `(1 + X²) I - X A` is polynomial.** If
`((1 + X²) I - X A) N = I` for a matrix `A` over a nontrivial ring `R`, then for every column `j`
and every degree `d`, some entry of the `j`-th column of `N` has a nonzero coefficient in a degree
`n ≥ d`. -/
theorem exists_coeff_ne_zero_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one {R ι : Type*} [Ring R]
    [Nontrivial R] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) {N : Matrix ι ι R⟦X⟧}
    (hN : (((1 : R⟦X⟧) + X ^ 2) • (1 : Matrix ι ι R⟦X⟧) - (X : R⟦X⟧) • A.map C) * N = 1)
    (j : ι) (d : ℕ) : ∃ n ≥ d, ∃ i, coeff n (N i j) ≠ 0 := by
  have happly (i : ι) :
      ((((1 : R⟦X⟧) + X ^ 2) • (1 : Matrix ι ι R⟦X⟧) - (X : R⟦X⟧) • A.map C) * N) i j =
        ((1 : R⟦X⟧) + X ^ 2) * N i j - X * ∑ l, C (A i l) * N l j := by
    rw [sub_mul]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.map_apply]
  -- The coefficients of the `j`-th column of `N` satisfy `N_{n+2} = A N_{n+1} - N_n`.
  have hrec (n : ℕ) (i : ι) : coeff (n + 2) (N i j) + coeff n (N i j) =
      ∑ l, A i l * coeff (n + 1) (N l j) := by
    have h := congrArg (fun P => coeff (n + 2) (P i j)) hN
    simp only [happly, Matrix.one_apply, apply_ite (coeff (n + 2)), coeff_one, map_zero] at h
    simpa [add_mul, coeff_X_pow_mul', coeff_C_mul, sub_eq_zero] using h
  -- Descending induction from degree `d` kills every coefficient of the `j`-th column.
  by_contra! hd
  have hzero (t : ℕ) : ∀ n, d ≤ n + t → ∀ i, coeff n (N i j) = 0 := by
    induction t with
    | zero => simpa using hd
    | succ t ih =>
      intro n hn i
      simpa [ih (n + 1) (by omega), ih (n + 2) (by omega)] using hrec n i
  -- But the constant term of `N` is the identity matrix.
  have h0 := hzero d 0 (by omega) j
  rw [coeff_zero_eq_constantCoeff_apply] at h0
  simpa [happly, h0] using congrArg (fun P => constantCoeff (P j j)) hN

end Matrix
