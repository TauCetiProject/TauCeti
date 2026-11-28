/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Hilbert's Theorem 90 for an involution of a commutative ring

Let `τ` be an involutive ring endomorphism of a commutative ring `R` that moves some element. If
`τ x * x = 1`, then `x * τ y = y` for some nonzero `y`; over a field this says `x = y / τ y`. This
is the elementary form of Hilbert's Theorem 90 for a quadratic extension, with explicit witnesses:
`y = 1 + x`, or `y = d - τ d` when `x = -1` and `τ d ≠ d`.

## Main results

* `TauCeti.exists_ne_zero_mul_apply_eq_of_apply_mul_self_eq_one`: if `τ x * x = 1`, then
  `x * τ y = y` for some `y ≠ 0`.

## References

* S. Lang, *Algebra*, third edition, Chapter VI, Theorem 6.3.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **Hilbert's Theorem 90 for an involution.** Let `τ` be an involutive ring endomorphism of a
commutative ring `R` that moves some element `d`. If `τ x * x = 1`, then `x * τ y = y` for some
nonzero `y`; over a field this says `x = y / τ y`. One can take `y = 1 + x`, or `y = d - τ d` when
`x = -1`. -/
theorem exists_ne_zero_mul_apply_eq_of_apply_mul_self_eq_one {τ : R →+* R}
    (hτ : ∀ z, τ (τ z) = z) {d : R} (hd : τ d ≠ d) {x : R} (hx : τ x * x = 1) :
    ∃ y ≠ 0, x * τ y = y := by
  by_cases hx₁ : x = -1
  · subst hx₁
    refine ⟨d - τ d, sub_ne_zero.2 hd.symm, ?_⟩
    rw [map_sub, hτ]
    ring
  · refine ⟨1 + x, fun h ↦ hx₁ (eq_neg_of_add_eq_zero_right h), ?_⟩
    rw [map_add, map_one]
    linear_combination hx

end TauCeti
