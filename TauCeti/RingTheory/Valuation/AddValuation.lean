/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Additive valuations of finite products

An additive valuation turns products into sums. Mathlib records this for a product of two
elements (`AddValuation.map_mul`) and for powers (`AddValuation.map_pow`); this file records the
finite-product form, which is what a valuation computation on a factorised element such as
`f'(x) = ∏ (x - σ x)` uses. It also records that an additive valuation taking integer values on
nonzero elements, such as a discrete valuation normalised at a uniformiser, is infinite only at
zero.

## Main results

* `AddValuation.map_prod`: `v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i)`.
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

section Ring

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
