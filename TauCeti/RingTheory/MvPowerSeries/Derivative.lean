/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Partial derivatives and the order of a multivariate power series

A partial derivative lowers the order of a multivariate power series by at most one. Over a
commutative semiring without additive torsion the order is in turn detected by the partial
derivatives: `f` has order at least `n + 1`, for `n : ℕ∞`, exactly when its constant coefficient
vanishes and each of its partial derivatives has order at least `n`.

Applied to the Taylor expansion of a polynomial at a point, this is the characterization of the
order of vanishing of the polynomial at the point by its partial derivatives
(`MvPolynomial.le_orderAt_iff_eval_foldl_pderiv`).

## Main results

* `MvPowerSeries.le_order_pderiv`: if `n + 1 ≤ f.order` then `n ≤ (pderiv i f).order`.
* `MvPowerSeries.succ_le_order_iff`: `n + 1 ≤ f.order` if and only if the constant coefficient of
  `f` vanishes and `n ≤ (pderiv i f).order` for every `i`.
-/

public section

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

/-- A partial derivative lowers the order of a power series by at most one. -/
theorem le_order_pderiv [CommSemiring R] {f : MvPowerSeries σ R} {n : ℕ∞}
    (h : n + 1 ≤ f.order) (i : σ) : n ≤ (pderiv i f).order := by
  refine le_order fun d hd ↦ ?_
  rw [coeff_pderiv, coeff_of_lt_order (lt_of_lt_of_le ?_ h), zero_mul]
  simpa only [map_add, degree_single, Nat.cast_add, Nat.cast_one] using
    (ENat.add_lt_add_iff_right ENat.one_ne_top).mpr hd

variable [CommSemiring R] [IsAddTorsionFree R]

/-- Over a commutative semiring without additive torsion, `f` has order at least `n + 1` if and
only if its constant coefficient vanishes and each partial derivative has order at least `n`. -/
theorem succ_le_order_iff {f : MvPowerSeries σ R} {n : ℕ∞} :
    n + 1 ≤ f.order ↔
      constantCoeff f = 0 ∧ ∀ i, n ≤ (pderiv i f).order := by
  refine ⟨fun h ↦ ⟨?_, le_order_pderiv h⟩, fun ⟨h0, h⟩ ↦ le_order fun d hd ↦ ?_⟩
  · exact one_le_order_iff_constCoeff_eq_zero.mp (le_trans (by simp) h)
  obtain rfl | hi := eq_or_ne d 0
  · rwa [coeff_zero_eq_constantCoeff_apply]
  obtain ⟨i, hi⟩ := ne_iff.mp hi
  -- Write `d = e + single i 1` and read the coefficient of `X ^ e` in `pderiv i f`.
  obtain ⟨e, rfl⟩ : ∃ e, d = e + single i 1 :=
    ⟨d - single i 1, (sub_add_single_one_cancel hi).symm⟩
  have he : (e.degree : ℕ∞) < n := by
    simpa only [map_add, degree_single, Nat.cast_add, Nat.cast_one,
      ENat.add_lt_add_iff_right ENat.one_ne_top] using hd
  have := coeff_of_lt_order (lt_of_lt_of_le he (h i))
  rw [coeff_pderiv, mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul] at this
  exact (nsmul_eq_zero_iff.mp this).resolve_right (Nat.succ_ne_zero _)

end MvPowerSeries
