/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.BigOperators.Finset.PartialSum

/-!
# Additive valuations of finite products

An additive valuation turns products into sums. Mathlib records this for a product of two
elements (`AddValuation.map_mul`) and for powers (`AddValuation.map_pow`); this file records the
finite-product form, which is what a valuation computation on a factorised element such as
`f'(x) = ∏ (x - σ x)` uses, and that signs `(-1) ^ k`, as in determinant and coefficient
formulas, have valuation zero. For an additive valuation which is nonnegative on the whole ring,
such as the valuation of a discrete valuation ring, units have valuation zero and valuations
increase along divisibility. It also records that an additive valuation taking integer values on
nonzero elements, such as a discrete valuation normalised at a uniformiser, is infinite only at
zero.

## Main results

* `AddValuation.map_prod`: `v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i)`.
* `AddValuation.map_prod_castLE`: the valuation of the product of the first `k` entries of a
  tuple is the prefix sum of their valuations.
* `AddValuation.map_neg_one_pow`: `v ((-1) ^ k) = 0`.
* `AddValuation.map_eq_zero_of_isUnit`, `AddValuation.map_le_map_of_dvd`: for an additive valuation
  which is nonnegative on the whole ring, units have valuation `0` and divisors have smaller
  valuation.
* `AddValuation.eq_zero_of_eq_top_of_forall_ne_zero`: an additive valuation taking integer
  values on nonzero elements is infinite only at zero.
-/

public section

namespace AddValuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ₀]
  (v : AddValuation R Γ₀)

/-- An additive valuation of a finite product is the sum of the valuations of the factors. -/
@[simp]
theorem map_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [v.map_one]
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, v.map_mul, ih]

/-- The valuation of the product of the first `k` entries of `s : Fin n → R` is the prefix sum of
length `k` of their valuations. -/
theorem map_prod_castLE {n k : ℕ} (hk : k ≤ n) (s : Fin n → R) :
    v (∏ j : Fin k, s (Fin.castLE hk j)) = TauCeti.prefixSum k fun i ↦ v (s i) := by
  rw [map_prod, TauCeti.prefixSum_eq_sum_castLE hk]

/-- For an additive valuation which is nonnegative on the whole ring, units have valuation `0`. -/
theorem map_eq_zero_of_isUnit {v : AddValuation R Γ₀} (hv : ∀ x, 0 ≤ v x) {u : R} (hu : IsUnit u) :
    v u = 0 := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h := congrArg v hw
  rw [v.map_mul, v.map_one] at h
  exact le_antisymm (h ▸ le_add_of_nonneg_right (hv w)) (hv u)

/-- For an additive valuation which is nonnegative on the whole ring, a divisor has at most the
valuation of its multiples. -/
theorem map_le_map_of_dvd {v : AddValuation R Γ₀} (hv : ∀ x, 0 ≤ v x) {a b : R} (h : a ∣ b) :
    v a ≤ v b := by
  obtain ⟨c, rfl⟩ := h
  rw [v.map_mul]
  exact le_add_of_nonneg_right (hv c)

section Ring

/-- A sign `(-1) ^ k` has valuation zero. -/
theorem map_neg_one_pow {R : Type*} [Ring R] (v : AddValuation R Γ₀) (k : ℕ) :
    v ((-1) ^ k) = 0 := by
  rw [v.map_pow, v.map_neg, v.map_one, smul_zero]

variable {R Γ : Type*} [Ring R] [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [IntCast Γ] {v : AddValuation R (WithTop Γ)}

/-- An additive valuation with values in `WithTop Γ` taking integer values on nonzero elements is
infinite only at zero. -/
theorem eq_zero_of_eq_top_of_forall_ne_zero
    (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : Γ) : WithTop Γ)) (x : R) (hx : v x = ⊤) :
    x = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := hint x h
  exact WithTop.coe_ne_top (hn.symm.trans hx)

end Ring

end AddValuation
