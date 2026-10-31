/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Basic facts about multiplicative characters

To show that a multiplicative character takes values in a subset containing zero, it suffices
to check the values on units. This applies, for example, to subfields and subrings containing
the character values on units, since a multiplicative character vanishes on nonunits.

The trivial character takes only the values `0` and `1`, on nonunits and units respectively, so
it is unchanged by transport along an isomorphism of the domain and a homomorphism of the
coefficients (`MulChar.map_one_apply`). More generally, if a homomorphism `f` of the coefficients
carries `χ` to `χ'` along such an isomorphism `e`, that is `f (χ a) = χ' (e a)`, then it also
carries `χ⁻¹` to `χ'⁻¹` and every power `χ ^ n` to `χ' ^ n`. This is how Galois automorphisms of
a number field act on characters such as power residue symbols.
-/

public section

namespace MulChar

/-- A multiplicative character takes values in a subset containing `0` whenever all its values
on units lie there. -/
theorem apply_mem_of_forall_unit {R R' S : Type*} [CommMonoid R]
    [CommMonoidWithZero R'] [SetLike S R'] [ZeroMemClass S R'] (χ : MulChar R R') (s : S)
    (hχ : ∀ u : Rˣ, χ (u : R) ∈ s) (a : R) : χ a ∈ s := by
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec]
    exact hχ _
  · rw [MulChar.map_nonunit _ ha]
    exact zero_mem s

/-- The trivial character commutes with transport along a multiplicative isomorphism `e` of the
domain and a homomorphism `f` of the coefficients: both sides are `1` on units and `0` on
nonunits. -/
theorem map_one_apply {R S R' R'' F G : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero R'] [CommMonoidWithZero R''] [FunLike F R' R'']
    [MonoidWithZeroHomClass F R' R''] [EquivLike G R S] [MulEquivClass G R S] (f : F) (e : G)
    (a : R) : f ((1 : MulChar R R') a) = (1 : MulChar S R'') (e a) := by
  by_cases ha : IsUnit a
  · rw [one_apply ha, one_apply (ha.map e), map_one]
  · rw [map_nonunit _ ha, map_nonunit _ (by rwa [isUnit_map_iff]), map_zero]

section Transport

variable {R S R' R'' F G : Type*} [CommMonoid R] [CommMonoid S] [CommMonoidWithZero R']
  [CommMonoidWithZero R''] [FunLike F R' R''] [MonoidWithZeroHomClass F R' R''] [EquivLike G R S]
  [MulEquivClass G R S] {f : F} {e : G} {χ : MulChar R R'} {χ' : MulChar S R''}

/-- If a homomorphism `f` of the coefficients carries `χ` to `χ'` along a multiplicative
isomorphism `e` of the domain, then it carries `χ⁻¹` to `χ'⁻¹`. -/
theorem map_inv_apply_of_map_apply (h : ∀ a, f (χ a) = χ' (e a)) (a : R) :
    f (χ⁻¹ a) = χ'⁻¹ (e a) := by
  by_cases ha : IsUnit a
  · -- Both sides are inverse to `f (χ a) = χ' (e a)`, which is a unit.
    have hu : IsUnit (χ' (e a)) := (ha.map e).map χ'
    refine hu.mul_left_injective ?_
    dsimp only
    rw [← mul_apply χ'⁻¹, inv_mul, one_apply (ha.map e), ← h, ← map_mul, ← mul_apply, inv_mul,
      one_apply ha, map_one]
  · rw [map_nonunit _ ha, map_nonunit _ (by rwa [isUnit_map_iff]), map_zero]

/-- If a homomorphism `f` of the coefficients carries `χ` to `χ'` along a multiplicative
isomorphism `e` of the domain, then it carries `χ ^ n` to `χ' ^ n`. -/
theorem map_pow_apply_of_map_apply (h : ∀ a, f (χ a) = χ' (e a)) (n : ℕ) (a : R) :
    f ((χ ^ n) a) = (χ' ^ n) (e a) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, pow_zero, map_one_apply f e]
  · rw [pow_apply' _ hn, pow_apply' _ hn, map_pow, h]

end Transport

end MulChar
