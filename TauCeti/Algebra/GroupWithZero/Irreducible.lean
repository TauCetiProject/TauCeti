/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Irreducibility pulled back along divisibility-reflecting maps

Mathlib's `Irreducible.of_map` pulls irreducibility back along a local monoid homomorphism.
Comparison maps such as the inclusion of polynomials into restricted or overconvergent power
series are not local, but they reflect divisibility by a fixed nonzero element `x`. In a
commutative monoid with zero and left cancellation this already suffices: if `f x` is
irreducible, so is `x`.

## Main results

* `Irreducible.of_map_of_dvd`: irreducibility of `f x` implies irreducibility of a nonzero `x`
  when `f x ∣ f y` implies `x ∣ y`.
-/

public section

variable {M N F : Type*} [CommMonoidWithZero M] [IsLeftCancelMulZero M] [Monoid N]
  [FunLike F M N] [MonoidHomClass F M N]

/-- If a monoid homomorphism `f` reflects divisibility by a nonzero element `x`, then `x` is
irreducible whenever `f x` is. Unlike `Irreducible.of_map`, `f` need not be local. -/
theorem Irreducible.of_map_of_dvd {f : F} {x : M} (hx : x ≠ 0)
    (hdvd : ∀ y, f x ∣ f y → x ∣ y) (h : Irreducible (f x)) : Irreducible x := by
  -- If the image of a factor `a` of `x = a * b` is a unit, then `x` divides `b`; cancelling
  -- `b` shows that `a` is a unit.
  have key (a b : M) (hab : x = a * b) (ha : IsUnit (f a)) : IsUnit a := by
    have hb : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hx)
    obtain ⟨d, hd⟩ := hdvd b <| by
      rw [hab, mul_comm a b, map_mul]
      exact ha.mul_right_dvd.mpr dvd_rfl
    rw [hab] at hd
    refine IsUnit.of_mul_eq_one d (mul_left_cancel₀ hb ?_)
    rw [mul_one, ← mul_assoc, mul_comm b a]
    exact hd.symm
  refine ⟨fun hu ↦ h.not_isUnit (hu.map f), fun a b hab ↦ ?_⟩
  rcases h.isUnit_or_isUnit (by rw [hab, map_mul]) with ha | hb
  · exact Or.inl (key a b hab ha)
  · exact Or.inr (key b a (hab.trans (mul_comm a b)) hb)
