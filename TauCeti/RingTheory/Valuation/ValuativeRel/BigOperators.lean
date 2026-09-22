/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite products under a valuative relation

For a valuative relation on a commutative semiring, a finite product has positive value exactly
when every factor does, and finite products are monotone. When the other factors have positive
value, replacing one factor of a finite product moves the value of the product in the same
direction as the value of that factor.

## Main results

* `TauCeti.ValuativeRel.zero_vlt_prod_iff` : `0 <ᵥ ∏ i ∈ s, f i` exactly when `0 <ᵥ f i` for every
  `i ∈ s`.
* `TauCeti.ValuativeRel.prod_vle_prod` : finite products are monotone for `≤ᵥ`.
* `TauCeti.ValuativeRel.prod_update_vle_prod_iff` and
  `TauCeti.ValuativeRel.prod_vle_prod_update_iff` : if the factors other than `f j` have positive
  value, replacing `f j` by `x` compares with the original product exactly as `x` compares with
  `f j`.
* `TauCeti.ValuativeRel.prod_vle_prod_update` : replacing a factor by an element of at least its
  value does not decrease the value of the product.
-/

public section

namespace TauCeti.ValuativeRel

variable {R ι : Type*} [CommSemiring R] [ValuativeRel R] {s : Finset ι} {f g : ι → R}

/-- A finite product has positive value exactly when every factor does. This extends
`ValuativeRel.zero_vlt_mul` from two factors to finite products, and adds the converse. -/
@[simp]
theorem zero_vlt_prod_iff : 0 <ᵥ ∏ i ∈ s, f i ↔ ∀ i ∈ s, 0 <ᵥ f i := by
  simpa using (Ideal.IsPrime.prod_mem_iff (p := ValuativeRel.supp R)).not

/-- Finite products are monotone for a valuative relation. This is the analogue of
`Finset.prod_le_prod`, and extends `ValuativeRel.mul_vle_mul` from two factors to finite
products. -/
@[gcongr]
theorem prod_vle_prod (h : ∀ i ∈ s, f i ≤ᵥ g i) : ∏ i ∈ s, f i ≤ᵥ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction <;> simp_all [ValuativeRel.mul_vle_mul]

variable [DecidableEq ι] {j : ι} {x : R}

/-- If the factors of a finite product other than `f j` have positive value, replacing `f j` by `x`
does not increase the value of the product exactly when `x ≤ᵥ f j`. For the opposite comparison
see `prod_vle_prod_update_iff`. -/
@[simp]
theorem prod_update_vle_prod_iff (hf : ∀ i ∈ s, i ≠ j → 0 <ᵥ f i) (hj : j ∈ s) :
    ∏ i ∈ s, Function.update f j x i ≤ᵥ ∏ i ∈ s, f i ↔ x ≤ᵥ f j := by
  rw [Finset.prod_update_of_mem hj, Finset.sdiff_singleton_eq_erase,
    ← Finset.mul_prod_erase s f hj]
  exact ValuativeRel.mul_vle_mul_iff_left <| zero_vlt_prod_iff.mpr fun i hi ↦
    hf i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

/-- If the factors of a finite product other than `f j` have positive value, replacing `f j` by `x`
does not decrease the value of the product exactly when `f j ≤ᵥ x`. Without the positivity
hypothesis only the reverse implication holds; see `prod_vle_prod_update`. For the opposite
comparison see `prod_update_vle_prod_iff`. -/
@[simp]
theorem prod_vle_prod_update_iff (hf : ∀ i ∈ s, i ≠ j → 0 <ᵥ f i) (hj : j ∈ s) :
    ∏ i ∈ s, f i ≤ᵥ ∏ i ∈ s, Function.update f j x i ↔ f j ≤ᵥ x := by
  -- `f` is `Function.update f j x` with its `j`-th factor replaced by `f j`
  simpa using prod_update_vle_prod_iff (f := Function.update f j x) (x := f j)
    (fun i hi hij ↦ Function.update_of_ne hij x f ▸ hf i hi hij) hj

/-- Replacing a factor of a finite product by an element of at least its value does not decrease
the value of the product. Unlike `prod_vle_prod_update_iff`, no positivity hypothesis is needed. -/
theorem prod_vle_prod_update (h : f j ≤ᵥ x) : ∏ i ∈ s, f i ≤ᵥ ∏ i ∈ s, Function.update f j x i :=
  prod_vle_prod fun i _ ↦ by rcases eq_or_ne i j with rfl | hi <;> simp [*]

end TauCeti.ValuativeRel
