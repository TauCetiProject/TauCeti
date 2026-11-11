/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Basic facts about subrings

The inclusion of a subring into itself is the identity homomorphism. In a field, a common
denominator `a` of an element and its inverse clears the denominators of all integer powers of the
element: `a ^ N xⁿ` lies in the subring whenever `|n| ≤ N`, and the same holds for finite
products of integer powers.

## Main results

* `Subring.inclusion_rfl`: the inclusion `R ⊆ R` is `RingHom.id R`.
* `Subring.pow_mul_zpow_mem`: if `a`, `a x` and `a x⁻¹` lie in a subring `A`, then
  `a ^ N xⁿ ∈ A` for every integer `n` with `|n| ≤ N`.
* `Subring.prod_pow_mul_prod_zpow_mem`: the same for a finite product `∏ⱼ xⱼ ^ nⱼ`, with the
  denominator `∏ⱼ aⱼ ^ Nⱼ`.
-/

public section

namespace Subring

/-- The inclusion of a subring into itself is the identity homomorphism. -/
@[simp]
theorem inclusion_rfl {A : Type*} [Ring A] (R : Subring A) :
    R.inclusion le_rfl = RingHom.id R :=
  rfl

/-- **Denominators of integer powers.** If `a ∈ A` is a common denominator of `x` and `x⁻¹`, that
is `a x ∈ A` and `a x⁻¹ ∈ A`, then `a ^ N xⁿ ∈ A` for every integer `n` with `|n| ≤ N`. -/
theorem pow_mul_zpow_mem {K : Type*} [Field K] (A : Subring K) {a x : K} (ha : a ∈ A)
    (hx : a * x ∈ A) (hx' : a * x⁻¹ ∈ A) {n : ℤ} {N : ℕ} (hn : n.natAbs ≤ N) :
    a ^ N * x ^ n ∈ A := by
  rcases Int.natAbs_eq n with h | h <;> rw [h, ← Nat.sub_add_cancel hn, pow_add, mul_assoc]
  · rw [zpow_natCast, ← mul_pow]
    exact mul_mem (pow_mem ha _) (pow_mem hx _)
  · rw [zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
    exact mul_mem (pow_mem ha _) (pow_mem hx' _)

/-- **Denominators of products of integer powers.** If `aⱼ ∈ A` is a common denominator of `xⱼ`
and `xⱼ⁻¹` and `|nⱼ| ≤ Nⱼ` for each `j ∈ s`, then `(∏ⱼ aⱼ ^ Nⱼ) ∏ⱼ xⱼ ^ nⱼ ∈ A`. -/
theorem prod_pow_mul_prod_zpow_mem {K ι : Type*} [Field K] (A : Subring K) {s : Finset ι}
    {a x : ι → K} {n : ι → ℤ} {N : ι → ℕ} (ha : ∀ j ∈ s, a j ∈ A) (hx : ∀ j ∈ s, a j * x j ∈ A)
    (hx' : ∀ j ∈ s, a j * (x j)⁻¹ ∈ A) (hn : ∀ j ∈ s, (n j).natAbs ≤ N j) :
    (∏ j ∈ s, a j ^ N j) * ∏ j ∈ s, x j ^ n j ∈ A := by
  rw [← Finset.prod_mul_distrib]
  exact prod_mem fun j hj ↦ A.pow_mul_zpow_mem (ha j hj) (hx j hj) (hx' j hj) (hn j hj)

end Subring
