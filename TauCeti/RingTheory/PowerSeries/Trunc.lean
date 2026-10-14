/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Truncations and finite expansions of power series

Two facts used to compare power series to a finite order `m`: the truncation `trunc m φ`
vanishes exactly when `φ` has order at least `m`, and the coefficients of a finite expansion
`∑_{i < m} aᵢ Xⁱ` are the `aᵢ`, read as zero from degree `m` on.

## Main results

* `PowerSeries.trunc_eq_zero_iff_le_order`: `trunc m φ = 0 ↔ m ≤ order φ`.
* `PowerSeries.coeff_sum_C_mul_X_pow`: the coefficients of `∑ i : Fin m, C (a i) * X ^ i`.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- The truncation below degree `m` of a power series vanishes exactly when the series has
order at least `m`. -/
theorem trunc_eq_zero_iff_le_order {m : ℕ} {φ : R⟦X⟧} : trunc m φ = 0 ↔ (m : ℕ∞) ≤ φ.order := by
  rw [nat_le_order_iff]
  refine ⟨fun h i hi ↦ ?_, fun h ↦ Polynomial.ext fun i ↦ ?_⟩
  · simpa [coeff_trunc, hi] using congrArg (Polynomial.coeff · i) h
  · rw [coeff_trunc, Polynomial.coeff_zero]
    split_ifs with hi
    exacts [h i hi, rfl]

/-- The coefficients of the finite expansion `∑_{i < m} aᵢ Xⁱ` are the `aᵢ`, and vanish from
degree `m` on. -/
theorem coeff_sum_C_mul_X_pow {m : ℕ} (a : Fin m → R) (n : ℕ) :
    coeff n (∑ i : Fin m, C (a i) * X ^ (i : ℕ)) = if h : n < m then a ⟨n, h⟩ else 0 := by
  simp only [map_sum, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨n, h⟩ fun i hi ↦ by
      have hni : n ≠ (i : ℕ) := fun hn ↦ hi (Fin.ext hn.symm)
      simp [hni]]
    simp
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hni : n ≠ (i : ℕ) := (i.2.trans_le (not_lt.mp h)).ne'
    simp [hni]

end PowerSeries
