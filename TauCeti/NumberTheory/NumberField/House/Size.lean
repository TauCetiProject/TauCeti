/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.House
import TauCeti.NumberTheory.Height.House
import TauCeti.NumberTheory.NumberField.House

/-!
# Sizes of algebraic numbers

Transcendence proofs measure an element `α` of a number field `K` by a denominator `δ`, an
exponent `a` and a bound `H` such that `δ ^ a * α` is an algebraic integer of house at most `H`.
The numbers such a proof builds are sums and products of powers of finitely many given algebraic
numbers, and their sizes are computed from the sizes of the given numbers. The integrality half of
this bookkeeping holds in any commutative ring (`IsIntegral.pow_add_mul_mul` and its neighbours);
this file supplies the house half, and Liouville's inequality for a number of known size, which
turns such a size into a lower bound for every conjugate of a nonzero number.

Raising the exponent of a size is `NumberField.house_natCast_pow_mul_le_of_le`, and the common
denominator of finitely many algebraic numbers is
`NumberField.exists_natCast_mul_isIntegral_house_le` (inside a number field) or
`NumberField.exists_numberField_denominator` (in a field of characteristic zero).

## Main results

* `NumberField.house_pow_add_mul_mul_le`, `NumberField.house_pow_mul_add_le`,
  `NumberField.house_pow_mul_mul_pow_le`, `NumberField.house_pow_mul_sum_le`,
  `NumberField.house_pow_sum_mul_prod_le`: house bounds for products, sums and powers of numbers
  of known size.
* `NumberField.one_le_pow_mul_norm_embedding_mul_pow`: **Liouville's inequality for a number of
  known size**. If `δ ≠ 0` and `δ ^ a * α` is a nonzero algebraic integer of house at most `H`,
  then `1 ≤ δ ^ a ‖σ α‖ H ^ ([K : ℚ] - 1)` for every complex embedding `σ`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer (2000), §3.5, Proposition 3.14 (Liouville's
  inequality) and §4.6 (the sizes of the Taylor coefficients of the auxiliary function).
-/

public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

variable {δ α β : K} {a b : ℕ} {H H' : ℝ}

/-- If `δ ^ a * α` has house at most `H` and `δ ^ b * β` has house at most `H'`, then
`δ ^ (a + b) * (α * β)` has house at most `H * H'`. -/
theorem house_pow_add_mul_mul_le (hα : house (δ ^ a * α) ≤ H) (hβ : house (δ ^ b * β) ≤ H') :
    house (δ ^ (a + b) * (α * β)) ≤ H * H' := by
  rw [pow_add, mul_mul_mul_comm]
  exact (house_mul_le _ _).trans
    (mul_le_mul hα hβ (house_nonneg _) ((house_nonneg _).trans hα))

/-- If `δ ^ a * α` has house at most `H` and `δ ^ a * β` has house at most `H'`, then
`δ ^ a * (α + β)` has house at most `H + H'`. -/
theorem house_pow_mul_add_le (hα : house (δ ^ a * α) ≤ H) (hβ : house (δ ^ a * β) ≤ H') :
    house (δ ^ a * (α + β)) ≤ H + H' := by
  rw [mul_add]
  exact (house_add_le _ _).trans (add_le_add hα hβ)

/-- If `δ ^ a * α` has house at most `H`, then `δ ^ (a * k) * α ^ k` has house at most `H ^ k`. -/
theorem house_pow_mul_mul_pow_le (hα : house (δ ^ a * α) ≤ H) (k : ℕ) :
    house (δ ^ (a * k) * α ^ k) ≤ H ^ k := by
  rw [pow_mul, ← mul_pow, house_pow]
  exact pow_le_pow_left₀ (house_nonneg _) hα k

/-- If `δ ^ a * f i` has house at most `H i` for every `i ∈ s`, then `δ ^ a * ∑ i ∈ s, f i` has
house at most `∑ i ∈ s, H i`. -/
theorem house_pow_mul_sum_le {ι : Type*} {s : Finset ι} {f : ι → K} {H : ι → ℝ}
    (hf : ∀ i ∈ s, house (δ ^ a * f i) ≤ H i) :
    house (δ ^ a * ∑ i ∈ s, f i) ≤ ∑ i ∈ s, H i := by
  rw [Finset.mul_sum]
  exact (house_sum_le_sum_house _ _).trans (Finset.sum_le_sum hf)

/-- If `δ ^ a i * f i` has house at most `H i` for every `i ∈ s`, then
`δ ^ (∑ i ∈ s, a i) * ∏ i ∈ s, f i` has house at most `∏ i ∈ s, H i`. -/
theorem house_pow_sum_mul_prod_le {ι : Type*} {s : Finset ι} {f : ι → K} {a : ι → ℕ}
    {H : ι → ℝ} (hf : ∀ i ∈ s, house (δ ^ a i * f i) ≤ H i) :
    house (δ ^ (∑ i ∈ s, a i) * ∏ i ∈ s, f i) ≤ ∏ i ∈ s, H i := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact (house_prod_le_prod_house _ _).trans
    (Finset.prod_le_prod₀ (fun _ _ ↦ house_nonneg _) hf)

/-- **Liouville's inequality for a number of known size.** If `δ ≠ 0` and `δ ^ a * α` is a
nonzero algebraic integer of house at most `H`, then `1 ≤ δ ^ a ‖σ α‖ H ^ ([K : ℚ] - 1)` for every
complex embedding `σ` of `K`. -/
theorem one_le_pow_mul_norm_embedding_mul_pow {δ a : ℕ} (hδ : δ ≠ 0) {α : K}
    (hα : α ≠ 0) {H : ℝ} (hint : IsIntegral ℤ ((δ : K) ^ a * α))
    (hH : house ((δ : K) ^ a * α) ≤ H) (σ : K →+* ℂ) :
    1 ≤ (δ : ℝ) ^ a * ‖σ α‖ * H ^ (Module.finrank ℚ K - 1) := by
  have h := one_le_norm_mul_house_pow hint
    (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hδ)) hα) σ
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast] at h
  exact h.trans (by gcongr; exact house_nonneg _)

end NumberField
