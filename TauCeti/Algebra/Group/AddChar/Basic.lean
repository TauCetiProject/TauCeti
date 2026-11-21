/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Additive characters

## Main results

* `AddChar.map_sum_eq_prod`: an additive character turns finite sums into products.
* `AddChar.pow_char_eq_one`: every additive character on a ring of characteristic `p`, such as
  `ZMod p`, takes values in the `p`-th roots of unity.
* `AddChar.apply_mul_sum`: multiplying the sum of the values of a character by one value leaves
  it unchanged.
* `AddChar.sum_eq_zero_of_isLeftRegular_sub_one`: the values of an additive character of a finite
  group sum to zero once some `ψ b - 1` is left-regular, over any commutative ring.
-/

public section

/-- An additive character on a ring of characteristic `p` takes values in the `p`-th roots of
unity; for instance every additive character on `ZMod p` does. -/
@[simp]
theorem AddChar.pow_char_eq_one {R M : Type*} [NonAssocSemiring R] (p : ℕ) [CharP R p]
    [Monoid M] (ψ : AddChar R M) (x : R) : ψ x ^ p = 1 := by
  simp [← AddChar.map_nsmul_eq_pow]

/-- An additive character turns a finite sum into the product of its values. -/
theorem AddChar.map_sum_eq_prod {ι A M : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, map_add_eq_mul, ih, Finset.prod_cons]

/-- Multiplying the sum of the values of an additive character of a finite group by one of its
values leaves the sum unchanged: translation permutes the group. -/
theorem AddChar.apply_mul_sum {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R]
    (ψ : AddChar A R) (b : A) : ψ b * ∑ a, ψ a = ∑ a, ψ a := by
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft b) _ _ fun y ↦ (map_add_eq_mul ..).symm

/-- The values of an additive character of a finite group sum to zero as soon as `ψ b - 1` is
left-regular for some `b`, for instance a unit. This is `AddChar.sum_eq_zero_of_ne_one` without
the assumption that the target ring is a domain. -/
theorem AddChar.sum_eq_zero_of_isLeftRegular_sub_one {A R : Type*} [AddGroup A] [Fintype A]
    [CommRing R] {ψ : AddChar A R} {b : A} (hb : IsLeftRegular (ψ b - 1)) : ∑ a, ψ a = 0 :=
  hb (by simp only [sub_mul, ψ.apply_mul_sum, one_mul, sub_self, mul_zero])
