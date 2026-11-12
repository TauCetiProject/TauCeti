/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card

/-!
# Collapsing an iterated product of powers into a single product of powers

`Finset.prod_pow_eq_pow_sum` collapses a product of natural powers of one fixed element into a
single power. This file records the analogue for integral powers, in a commutative group and at
a unit of a division commutative monoid (for instance a nonzero element of a commutative group with
zero), and the three substitution rules that follow from it: substituting a family of monomials
into a monomial multiplies the two exponent matrices.

These are the bookkeeping rules behind composing monomial maps in coordinates, where the exponent
matrices may carry natural or integral entries depending on whether the coordinate they act on is
allowed to vanish.

## Main results

* `Finset.prod_zpow_eq_zpow_sum` and `Finset.prod_zpow_eq_zpow_sum_of_isUnit`:
  `∏ i ∈ s, y ^ e i = y ^ ∑ i ∈ s, e i`, in a commutative group and, for a unit `y`, in a division
  commutative monoid.
* `Finset.prod_prod_pow`, `Finset.prod_prod_zpow` and `Finset.prod_prod_zpow_pow`: substituting
  monomials into a monomial multiplies the exponent matrices, for the three combinations of
  natural and integral exponents that make sense.
* `Fintype.sq_prod_pow_two_pow_card_pred`: the square of `∏ i, a i ^ 2 ^ (card α - 1)` is
  `∏ i, a i ^ 2 ^ card α`.
-/

public section

namespace Finset

variable {ι κ M G α : Type*}

/-- A product of integral powers of one fixed element of a commutative group collapses to a single
power. This is the integral-exponent analogue of `Finset.prod_pow_eq_pow_sum`. -/
theorem prod_zpow_eq_zpow_sum [CommGroup G] (s : Finset ι) (y : G) (e : ι → ℤ) :
    ∏ i ∈ s, y ^ e i = y ^ ∑ i ∈ s, e i := by
  induction s using Finset.cons_induction <;> simp [zpow_add, *]

/-- A product of integral powers of one fixed unit of a division commutative monoid collapses to a
single power. -/
theorem prod_zpow_eq_zpow_sum_of_isUnit [DivisionCommMonoid α] (s : Finset ι) {y : α}
    (hy : IsUnit y) (e : ι → ℤ) : ∏ i ∈ s, y ^ e i = y ^ ∑ i ∈ s, e i := by
  obtain ⟨u, rfl⟩ := hy
  simpa using congrArg Units.val (prod_zpow_eq_zpow_sum s u e)

/-- Substituting the monomials `∏ b ∈ t, x b ^ e a b` into the monomial with natural exponents
`g` produces the monomial whose exponent matrix is the product `∑ a ∈ s, g a * e a b`. -/
theorem prod_prod_pow [CommMonoid M] (s : Finset ι) (t : Finset κ) (x : κ → M) (e : ι → κ → ℕ)
    (g : ι → ℕ) :
    ∏ a ∈ s, (∏ b ∈ t, x b ^ e a b) ^ g a = ∏ b ∈ t, x b ^ ∑ a ∈ s, g a * e a b := by
  simp_rw [← prod_pow_eq_pow_sum, ← prod_pow, ← pow_mul, mul_comm (g _)]
  exact prod_comm

/-- Substituting the monomials `∏ b ∈ t, y b ^ e a b` in unit coordinates into the monomial
with integral exponents `g` produces the monomial whose exponent matrix is the product
`∑ a ∈ s, g a * e a b`. -/
theorem prod_prod_zpow [DivisionCommMonoid α] (s : Finset ι) (t : Finset κ) {y : κ → α}
    (hy : ∀ b ∈ t, IsUnit (y b)) (e : ι → κ → ℤ) (g : ι → ℤ) :
    ∏ a ∈ s, (∏ b ∈ t, y b ^ e a b) ^ g a = ∏ b ∈ t, y b ^ ∑ a ∈ s, g a * e a b := by
  rw [prod_congr rfl fun b hb ↦ (prod_zpow_eq_zpow_sum_of_isUnit s (hy b hb) _).symm]
  simp_rw [← prod_zpow, ← zpow_mul, mul_comm (g _)]
  exact prod_comm

/-- The mixed case of `Finset.prod_prod_zpow`: monomials with integral exponents in unit
coordinates, substituted into a monomial with natural exponents `g`. -/
theorem prod_prod_zpow_pow [DivisionCommMonoid α] (s : Finset ι) (t : Finset κ) {y : κ → α}
    (hy : ∀ b ∈ t, IsUnit (y b)) (e : ι → κ → ℤ) (g : ι → ℕ) :
    ∏ a ∈ s, (∏ b ∈ t, y b ^ e a b) ^ g a = ∏ b ∈ t, y b ^ ∑ a ∈ s, (g a : ℤ) * e a b := by
  simp_rw [← prod_prod_zpow s t hy e fun a ↦ (g a : ℤ), zpow_natCast]

end Finset

namespace Fintype

/-- The square of the product of the `2 ^ (card α - 1)`-th powers is the product of the
`2 ^ card α`-th powers. -/
theorem sq_prod_pow_two_pow_card_pred {α M : Type*} [Fintype α] [CommMonoid M] (a : α → M) :
    (∏ i, a i ^ (2 ^ (Fintype.card α - 1))) ^ 2 = ∏ i, a i ^ (2 ^ Fintype.card α) := by
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, ← pow_succ]
  congr 2
  exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨i⟩)

end Fintype
