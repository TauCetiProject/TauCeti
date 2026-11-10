/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Comparing finite sums and products after removing one index

Two functions on a finite type that agree away from one index and have the same sum (or product)
agree everywhere. The result applies to any cancellative commutative monoid. Separately, dividing
the product with one factor removed by the full product leaves the inverse of that factor.

## Main results

* `TauCeti.eq_of_prod_eq_of_forall_ne`, `TauCeti.eq_of_sum_eq_of_forall_ne`: equality of functions
  from equality of their products (sums) and equality away from one index.
* `Finset.prod_erase_mul_units_inv`: `(∏_{j ∈ s, j ≠ a} f j) / ∏_{j ∈ s} f j = 1 / f a` in a
  commutative monoid, when the full product and `f a` are units.
-/

public section

namespace TauCeti

/-- **Two functions with equal products that agree away from one index are equal.** -/
@[to_additive /-- **Two functions with equal sums that agree away from one index are equal.** -/]
theorem eq_of_prod_eq_of_forall_ne {ι M : Type*} [Fintype ι] [CommMonoid M] [IsRightCancelMul M]
    {x y : ι → M} (hprod : ∏ R, x R = ∏ R, y R) {P : ι} (h : ∀ R ≠ P, x R = y R) : x = y := by
  funext R
  obtain rfl | hR := eq_or_ne R P
  · exact (Finset.prod_eq_prod_iff_single (Finset.mem_univ R) fun j _ ↦ h j).mp hprod
  · exact h R hR

end TauCeti

namespace Finset

/-- **Dividing a product with one factor removed by the full product.** If `u` is a unit with
value `∏ j ∈ s, f j` and `v` is a unit with value `f a` for some `a ∈ s`, then
`(∏ j ∈ s.erase a, f j) * u⁻¹ = v⁻¹`. -/
theorem prod_erase_mul_units_inv {ι M : Type*} [CommMonoid M] [DecidableEq ι] (s : Finset ι)
    (f : ι → M) {a : ι} (h : a ∈ s) {u v : Mˣ} (hu : (u : M) = ∏ j ∈ s, f j)
    (hv : (v : M) = f a) : (∏ j ∈ s.erase a, f j) * ↑u⁻¹ = ↑v⁻¹ := by
  rw [Units.mul_inv_eq_iff_eq_mul, hu, ← mul_prod_erase s f h, ← hv, Units.inv_mul_cancel_left]

end Finset
