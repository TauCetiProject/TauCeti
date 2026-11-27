/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Comparing finite sums and products after removing one index

Two functions on a finite type that agree away from one index and have the same sum (or product)
agree everywhere. The result applies to any cancellative commutative monoid. Separately, dividing
the product with one factor removed by the full product leaves the inverse of that factor. In a
linearly ordered ring, a sum of squares that is at most one of its terms has every other term
zero, as all the other squares are nonnegative; this is how a vector of integers of norm `1` is
seen to be `±` a basis vector.

## Main results

* `TauCeti.eq_of_prod_eq_of_forall_ne`, `TauCeti.eq_of_sum_eq_of_forall_ne`: equality of functions
  from equality of their products (sums) and equality away from one index.
* `TauCeti.eq_zero_of_sum_mul_self_le`: if `∑ᵢ cᵢ² ≤ c_{i₀}²`, then `cⱼ = 0` for every `j ≠ i₀`.
* `Finset.sum_erase_merge`, `Finset.sum_erase_merge_mul`: after removing the index `t` and adding
  the value at `t` to the value at another index `t'`, the sum is unchanged, and so is the sum of
  the products with a second function once `f t` is replaced by `f t'`.
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

/-- **A sum of squares at most one of its terms.** In a linearly ordered ring, if
`∑ᵢ cᵢ² ≤ c_{i₀}²`, then `cⱼ = 0` for every `j ≠ i₀`: the squares are nonnegative, so those other
than `c_{i₀}²` sum to at most `0`, hence all vanish. -/
theorem eq_zero_of_sum_mul_self_le {ι R : Type*} [Fintype ι] [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] {c : ι → R} {i₀ : ι} (h : ∑ i, c i * c i ≤ c i₀ * c i₀) {j : ι}
    (hj : j ≠ i₀) : c j = 0 := by
  classical
  have hnn : ∀ i ∈ Finset.univ.erase i₀, 0 ≤ c i * c i := fun i _ ↦ mul_self_nonneg _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), add_le_iff_nonpos_right] at h
  exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp
    (le_antisymm h (Finset.sum_nonneg hnn)) j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))

end TauCeti

namespace Finset

/-- **Dividing a product with one factor removed by the full product.** If `u` is a unit with
value `∏ j ∈ s, f j` and `v` is a unit with value `f a` for some `a ∈ s`, then
`(∏ j ∈ s.erase a, f j) * u⁻¹ = v⁻¹`. -/
theorem prod_erase_mul_units_inv {ι M : Type*} [CommMonoid M] [DecidableEq ι] (s : Finset ι)
    (f : ι → M) {a : ι} (h : a ∈ s) {u v : Mˣ} (hu : (u : M) = ∏ j ∈ s, f j)
    (hv : (v : M) = f a) : (∏ j ∈ s.erase a, f j) * ↑u⁻¹ = ↑v⁻¹ := by
  rw [Units.mul_inv_eq_iff_eq_mul, hu, ← mul_prod_erase s f h, ← hv, Units.inv_mul_cancel_left]

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
