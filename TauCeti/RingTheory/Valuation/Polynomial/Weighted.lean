/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import TauCeti.RingTheory.Valuation.Sum
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Weighted convolution bounds for polynomial valuations

This file records the generic weighted coefficient convolution bound for products of polynomials
under a valuation `v : Valuation R Γ₀`. It is shared between the Gauss valuation multiplicativity
proof (`TauCeti.RingTheory.Polynomial.Gauss.Valuation.Basic`) and the weighted polynomial bounds
(`TauCeti.RingTheory.Valuation.Polynomial.Basic`).

## Main results

* `Valuation.map_coeff_mul_mul_pow_le_of_le`: if `v (p.coeff i) * r ^ i * s₁ ≤ A₁ * S ^ i` and
  `v (q.coeff j) * r ^ j * s₂ ≤ A₂ * S ^ j`, then
  `v ((p * q).coeff k) * r ^ k * (s₁ * s₂) ≤ (A₁ * A₂) * S ^ k`.
-/

public section

namespace Valuation

open Polynomial

/-- Weighted convolution bound for the coefficients of a product of polynomials: if
`v (p.coeff i) * r ^ i * s₁ ≤ A₁ * S ^ i` and `v (q.coeff j) * r ^ j * s₂ ≤ A₂ * S ^ j`, then
`v ((p * q).coeff k) * r ^ k * (s₁ * s₂) ≤ (A₁ * A₂) * S ^ k`. -/
theorem map_coeff_mul_mul_pow_le_of_le {R Γ₀ : Type*} [Ring R]
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) {p q : R[X]} {r s₁ s₂ A₁ A₂ S : Γ₀}
    (hp : ∀ i, v (p.coeff i) * r ^ i * s₁ ≤ A₁ * S ^ i)
    (hq : ∀ j, v (q.coeff j) * r ^ j * s₂ ≤ A₂ * S ^ j) (k : ℕ) :
    v ((p * q).coeff k) * r ^ k * (s₁ * s₂) ≤ (A₁ * A₂) * S ^ k := by
  rw [coeff_mul, mul_assoc]
  refine v.map_sum_mul_le fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  calc v (p.coeff ij.1 * q.coeff ij.2) * (r ^ k * (s₁ * s₂))
      = v (p.coeff ij.1) * r ^ ij.1 * s₁ * (v (q.coeff ij.2) * r ^ ij.2 * s₂) := by
        simp only [← hij, pow_add, map_mul]
        ac_rfl
    _ ≤ A₁ * S ^ ij.1 * (A₂ * S ^ ij.2) := mul_le_mul' (hp _) (hq _)
    _ = (A₁ * A₂) * S ^ k := by
        rw [← hij, pow_add]
        ac_rfl

end Valuation
