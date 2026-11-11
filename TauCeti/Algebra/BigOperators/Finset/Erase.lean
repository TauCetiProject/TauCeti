/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Comparing finite sums after removing one index

Two functions on a finite type that agree away from one index and have the same sum agree
everywhere. The result applies to any additive cancellative commutative monoid. Dually, dividing
the product with one factor removed by the full product leaves the inverse of that factor.

## Main results

* `TauCeti.eq_of_sum_eq_of_forall_ne`: equality of functions from equality of their sums and
  equality away from one index.
* `Finset.sum_erase_merge`, `Finset.sum_erase_merge_mul`: after removing the index `t` and adding
  the value at `t` to the value at another index `t'`, the sum is unchanged, and so is the sum of
  the products with a second function once `f t` is replaced by `f t'`.
* `Finset.prod_erase_mul_units_inv`: `(∏_{j ∈ s, j ≠ a} f j) / ∏_{j ∈ s} f j = 1 / f a` in a
  commutative monoid, when the full product and `f a` are units.
-/

public section

namespace TauCeti

/-- **Two functions with equal sums that agree away from one index are equal.** -/
theorem eq_of_sum_eq_of_forall_ne {ι M : Type*} [Fintype ι] [AddCancelCommMonoid M]
    (x y : ι → M) (hsum : ∑ R, x R = ∑ R, y R) (P : ι)
    (h : ∀ R ≠ P, x R = y R) : x = y := by
  classical
  have herase : ∑ R ∈ Finset.univ.erase P, x R =
      ∑ R ∈ Finset.univ.erase P, y R :=
    Finset.sum_congr rfl fun R hR ↦ h R (Finset.mem_erase.mp hR).1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ P), herase] at hsum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ P)] at hsum
  have hP : x P = y P := add_left_cancel hsum
  funext R
  by_cases hR : R = P
  · simpa only [hR] using hP
  · exact h R hR

end TauCeti

namespace Finset

/-- **Dividing a product with one factor removed by the full product.** If `u` is a unit with
value `∏ j ∈ s, f j` and `v` is a unit with value `f a` for some `a ∈ s`, then
`(∏ j ∈ s.erase a, f j) * u⁻¹ = v⁻¹`. -/
theorem prod_erase_mul_units_inv {ι M : Type*} [CommMonoid M] [DecidableEq ι] (s : Finset ι)
    (f : ι → M) {a : ι} (h : a ∈ s) {u v : Mˣ} (hu : (u : M) = ∏ j ∈ s, f j)
    (hv : (v : M) = f a) : (∏ j ∈ s.erase a, f j) * ↑u⁻¹ = ↑v⁻¹ := by
  rw [Units.mul_inv_eq_iff_eq_mul, hu, ← mul_prod_erase s f h, ← hv, ← mul_assoc, Units.inv_mul,
    one_mul]

/-- Removing the index `t` and adding the value at `t` to the value at another index `t'` does not
change the sum. -/
theorem sum_erase_merge {ι M : Type*} [AddCommMonoid M] [DecidableEq ι] {A : Finset ι} {t t' : ι}
    (ht'A' : t' ∈ A.erase t) (htA : t ∈ A) (v : ι → M) :
    ∑ a ∈ A.erase t, (v a + if a = t' then v t else 0) = ∑ a ∈ A, v a := by
  rw [sum_add_distrib, ← sum_erase_add A v htA]
  simp [ht'A']

/-- Removing the index `t` and adding the coefficient at `t` to the coefficient at another index
`t'` does not change the combination of a function `f`, once `f t` is replaced by `f t'`. -/
theorem sum_erase_merge_mul {ι R : Type*} [NonUnitalNonAssocSemiring R] [DecidableEq ι]
    {A : Finset ι} {t t' : ι} (ht'A' : t' ∈ A.erase t) (v f : ι → R) :
    ∑ a ∈ A.erase t, (v a + if a = t' then v t else 0) * f a =
      ∑ a ∈ A.erase t, v a * f a + v t * f t' := by
  simp [add_mul, sum_add_distrib, ht'A']

end Finset
