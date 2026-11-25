/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Additive characters

## Main results

* `AddChar.map_sum_eq_prod`: an additive character turns finite sums into products.
* `AddChar.apply_eq_prod_single`: an additive character of a finite product of additive monoids is
  the product of its values on the components.
* `AddChar.map_eq_one_of_add_eq_zero`: an additive character trivial at `x` is trivial at every
  additive left inverse of `x`, even over a monoid.
* `AddChar.pow_char_eq_one`: every additive character on a ring of characteristic `p`, such as
  `ZMod p`, takes values in the `p`-th roots of unity.
* `AddChar.apply_mul_sum`: multiplying the sum of the values of a character by one value leaves
  it unchanged.
* `AddChar.sum_eq_zero_of_isLeftRegular_sub_one`: the values of an additive character of a finite
  group sum to zero once some `ψ b - 1` is left-regular, over any commutative ring.
* `AddChar.isIntegral_apply`: the values of an additive character of a finite group are algebraic
  integers.
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

/-- An additive character of a finite product of additive monoids is the product of its values on
the components: `φ b = ∏ i, φ (Pi.single i (b i))`. -/
theorem AddChar.apply_eq_prod_single {ι : Type*} [DecidableEq ι] [Fintype ι] {A : ι → Type*}
    [∀ i, AddCommMonoid (A i)] {M : Type*} [CommMonoid M] (φ : AddChar (∀ i, A i) M)
    (b : ∀ i, A i) : φ b = ∏ i, φ (Pi.single i (b i)) := by
  have h : φ (∑ i, Pi.single i (b i)) = ∏ i, φ (Pi.single i (b i)) :=
    AddChar.map_sum_eq_prod φ Finset.univ _
  rwa [Finset.univ_sum_single b] at h

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

/-- The values of an additive character of a finite additive group are algebraic integers: each
is a root of unity of order dividing the order of the group. -/
theorem AddChar.isIntegral_apply {A R : Type*} [AddGroup A] [Finite A] [CommRing R]
    (ψ : AddChar A R) (a : A) : IsIntegral ℤ (ψ a) :=
  IsIntegral.of_pow Nat.card_pos <| by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
    exact isIntegral_one

/-- An additive character trivial at `x` is trivial at every `y` with `y + x = 0`. Over an
additive group this says `ψ (-x) = 1`; the statement needs neither negation in the domain nor
inverses in the codomain, so it also applies to characters of semirings with values in a
monoid. -/
theorem AddChar.map_eq_one_of_add_eq_zero {A M : Type*} [AddMonoid A] [Monoid M]
    (ψ : AddChar A M) {x y : A} (hx : ψ x = 1) (hxy : y + x = 0) : ψ y = 1 :=
  calc ψ y = ψ y * ψ x := by rw [hx, mul_one]
    _ = 1 := by rw [← AddChar.map_add_eq_mul, hxy, AddChar.map_zero_eq_one]
