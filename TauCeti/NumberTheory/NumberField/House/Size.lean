/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.NumberTheory.Height.House

/-!
# Sizes of algebraic numbers

Transcendence proofs measure an element `α` of a number field `K` by a denominator `δ`, an
exponent `a` and a bound `H` such that `δ ^ a * α` is an algebraic integer of house at most `H`.
The numbers such a proof builds are sums and products of powers of finitely many given algebraic
numbers, and their sizes are computed from the sizes of the given numbers. The integrality half of
this bookkeeping holds in any commutative ring (`IsIntegral.pow_add_mul_mul` and its neighbours);
this file supplies the house half, the common denominator of finitely many elements, and
Liouville's inequality for a number of known size, which turns such a size into a lower bound for
every conjugate of a nonzero number.

The field generated over `ℚ` by finitely many algebraic numbers of a field of characteristic zero
is a number field, by `IntermediateField.finiteDimensional_adjoin` and
`NumberField.of_module_finite`; `NumberField.exists_natCast_mul_isIntegral_and_house_le` then gives
its elements of interest a common denominator.

## Main results

* `NumberField.house_prod_le_prod_house`: the house of a product over an indexed family is at most
  the product of the houses.
* `NumberField.house_pow_add_mul_mul_le`, `NumberField.house_pow_mul_add_le`,
  `NumberField.house_pow_mul_mul_pow_le`, `NumberField.house_pow_mul_sum_le`,
  `NumberField.house_pow_sum_mul_prod_le`: house bounds for products, sums and powers of numbers
  of known size.
* `NumberField.house_pow_mul_le_of_le`: raising the exponent from `a` to `c` multiplies the bound
  by `G ^ (c - a)`, for any `G` bounding the house of `δ`.
* `NumberField.exists_natCast_mul_isIntegral_and_house_le`: finitely many elements of `K` have a
  common denominator `δ ≥ 1` and a common bound `G` for the houses of `δ` times each of them, with
  `1 ≤ G` and `δ ≤ G`.
* `NumberField.one_le_pow_mul_norm_embedding_mul_pow`: **Liouville's inequality for a number of
  known size**. If `δ ≠ 0` and `δ ^ a * α` is a nonzero algebraic integer of house at most `H`,
  then `1 ≤ δ ^ a ‖σ α‖ H ^ ([K : ℚ] - 1)` for every complex embedding `σ`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer (2000), §3.5, Proposition 3.14 (Liouville's
  inequality) and §4.6 (the sizes of the Taylor coefficients of the auxiliary function).
-/

public section

open Finset

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The house of a product over a finite indexed family is at most the product of the houses. -/
theorem house_prod_le_prod_house {ι : Type*} (s : Finset ι) (f : ι → K) :
    house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  simpa [house, map_prod] using Finset.norm_prod_le s fun i ↦ canonicalEmbedding K (f i)

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

/-- If `δ ^ a * α` has house at most `H` and `δ` has house at most `G`, then for `a ≤ c` the
number `δ ^ c * α` has house at most `G ^ (c - a) * H`. For a natural number `δ` one can take
`G = δ`, or any `G ≥ δ`. -/
theorem house_pow_mul_le_of_le (hα : house (δ ^ a * α) ≤ H) {G : ℝ} (hδ : house δ ≤ G) {c : ℕ}
    (hac : a ≤ c) : house (δ ^ c * α) ≤ G ^ (c - a) * H := by
  rw [← Nat.sub_add_cancel hac, pow_add, mul_assoc, Nat.add_sub_cancel]
  refine (house_mul_le _ _).trans (mul_le_mul ?_ hα (house_nonneg _)
    (pow_nonneg ((house_nonneg _).trans hδ) _))
  rw [house_pow]
  exact pow_le_pow_left₀ (house_nonneg _) hδ _

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

/-- **Common denominators.** Finitely many elements `x i` of a number field have a common
denominator: a natural number `δ ≥ 1` such that every `δ * x i` is an algebraic integer. The houses
of the `δ * x i` have a common bound `G`, which can be taken with `1 ≤ G` and `δ ≤ G`. -/
theorem exists_natCast_mul_isIntegral_and_house_le {ι : Type*} [Finite ι] (x : ι → K) :
    ∃ δ : ℕ, 1 ≤ δ ∧ ∃ G : ℝ, 1 ≤ G ∧ (δ : ℝ) ≤ G ∧
      ∀ i, IsIntegral ℤ ((δ : K) * x i) ∧ house ((δ : K) * x i) ≤ G := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (univ.image x)
  have hint (i : ι) : IsIntegral ℤ ((y.natAbs : K) * x i) := by
    have h := hy (x i) (mem_image_of_mem x (mem_univ i))
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with hy' | hy'
    · rwa [hy', Int.cast_natCast] at h
    · rw [hy', Int.cast_neg, Int.cast_natCast, neg_mul] at h
      exact IsIntegral.neg_iff.mp h
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, y.natAbs + ∑ i, house ((y.natAbs : K) * x i), ?_,
    le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ house_nonneg _), fun i ↦ ⟨hint i, ?_⟩⟩
  · exact le_add_of_le_of_nonneg (by exact_mod_cast Int.natAbs_pos.mpr hy0)
      (sum_nonneg fun _ _ ↦ house_nonneg _)
  · exact le_add_of_nonneg_of_le (Nat.cast_nonneg _)
      (single_le_sum (fun j _ ↦ house_nonneg ((y.natAbs : K) * x j)) (mem_univ i))

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
