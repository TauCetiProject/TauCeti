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
that `M` has no right inverse whose entries are polynomials unless `ι` is empty
(`TauCeti.isEmpty_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one`). Indeed the coefficient matrices of
a right inverse `N` satisfy `N_{n+2} = A N_{n+1} - N_n`, so if they vanish from some degree on, then
they vanish in every degree by descending induction, against `N_0 = I`.

## Main results

* `TauCeti.isEmpty_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one`: no polynomial matrix is a right
  inverse of `(1 + X²) I - X A` over a nonempty index type.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Section 3, where `(1 + X²) I - X A` is the Hilbert-series denominator of a
  preprojective algebra.
-/

public section

namespace TauCeti

open PowerSeries

/-- **No polynomial matrix is a right inverse of `(1 + X²) I - X A`** over a nonempty index type. If
`((1 + X²) I - X A) N = I` for a matrix `A` over a nontrivial ring `R`, and the coefficients of
every entry of `N` vanish from degree `d` on, then the index type is empty. -/
theorem isEmpty_of_one_add_X_sq_smul_sub_X_smul_mul_eq_one {R ι : Type*} [Ring R] [Nontrivial R]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) {N : Matrix ι ι R⟦X⟧}
    (hN : (((1 : R⟦X⟧) + X ^ 2) • (1 : Matrix ι ι R⟦X⟧) - (X : R⟦X⟧) • A.map C) * N = 1)
    {d : ℕ} (hd : ∀ n, d ≤ n → ∀ i j, coeff n (N i j) = 0) : IsEmpty ι := by
  have happly (i j : ι) :
      ((((1 : R⟦X⟧) + X ^ 2) • (1 : Matrix ι ι R⟦X⟧) - (X : R⟦X⟧) • A.map C) * N) i j =
        ((1 : R⟦X⟧) + X ^ 2) * N i j - X * ∑ l, C (A i l) * N l j := by
    rw [sub_mul]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.map_apply]
  -- The coefficients of `N` satisfy `N_{n+2} = A N_{n+1} - N_n`.
  have hrec (n : ℕ) (i j : ι) : coeff (n + 2) (N i j) + coeff n (N i j) =
      ∑ l, A i l * coeff (n + 1) (N l j) := by
    have h := congrArg (fun P => coeff (n + 2) (P i j)) hN
    simp only [happly, Matrix.one_apply] at h
    have h0 : coeff (n + 2) (if i = j then (1 : R⟦X⟧) else 0) = 0 := by
      split_ifs <;> simp [coeff_one]
    rw [h0, map_sub, add_mul, one_mul, map_add, coeff_X_pow_mul',
      ite_eq_left (by omega : 2 ≤ n + 2), Nat.add_sub_cancel, coeff_succ_X_mul, map_sum,
      sub_eq_zero] at h
    simpa only [coeff_C_mul] using h
  -- Descending induction from degree `d` kills every coefficient.
  have hzero : ∀ t n, d ≤ n + t → ∀ i j, coeff n (N i j) = 0 := by
    intro t
    induction t with
    | zero => exact fun n hn => hd n hn
    | succ t ih =>
      intro n hn i j
      have h1 := ih (n + 1) (by omega)
      have h2 := ih (n + 2) (by omega)
      have h := hrec n i j
      simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add] at h
      exact h
  -- But the constant term of `N` is the identity matrix.
  refine ⟨fun i => ?_⟩
  have h := congrArg (fun P => constantCoeff (P i i)) hN
  simp only [happly, Matrix.one_apply_eq, map_sub, map_mul, map_add, map_one, map_pow,
    constantCoeff_X, zero_pow two_ne_zero, add_zero, one_mul, zero_mul, sub_zero] at h
  rw [← coeff_zero_eq_constantCoeff_apply, hzero d 0 (by omega)] at h
  exact zero_ne_one h

end TauCeti
