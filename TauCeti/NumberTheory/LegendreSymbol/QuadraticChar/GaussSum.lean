/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Twisting quadratic exponential sums by the quadratic character

Let `F` be a finite field of odd characteristic, `χ` its quadratic character and `ψ` a primitive
additive character of `F`. For `c ≠ 0`, the quadratic exponential sum `∑_x ψ(c x²)` is
`χ(c) ∑_x ψ(x²)`. Grouping the terms by `a = c x²`, which has `1 + χ(c a)` preimages `x`, turns
the sum into `∑_a χ(c a) ψ(a)`, since `ψ` sums to zero; multiplicativity of `χ` then extracts the
factor `χ(c)` from this Gauss sum of `χ`.

This is how the quadratic Gauss sums of a finite field with an arbitrary nonzero coefficient are
reduced to the one with coefficient `1`.

## Main results

* `TauCeti.sum_addChar_mul_sq`: `∑_x ψ(c x²) = χ(c) ∑_x ψ(x²)` for `c ≠ 0`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 6.
-/

public section

open Finset

namespace TauCeti

/-- **Twisting a quadratic exponential sum by the quadratic character**: for a primitive additive
character `ψ` of a finite field of odd characteristic and `c ≠ 0`,
`∑_x ψ(c x²) = χ(c) ∑_x ψ(x²)`. -/
theorem sum_addChar_mul_sq {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R]
    [IsDomain R] (hF : ringChar F ≠ 2) {ψ : AddChar F R} (hψ : ψ.IsPrimitive) {c : F}
    (hc : c ≠ 0) : ∑ x, ψ (c * x ^ 2) = quadraticChar F c * ∑ x, ψ (x ^ 2) := by
  have hsum : ∑ a, ψ a = 0 := by
    simpa using AddChar.sum_mulShift 1 hψ
  -- Grouping by the value `a = b x²` weights `ψ a` by `1 + χ (b * a)`.
  have htwist (b : F) (hb : b ≠ 0) :
      ∑ x, ψ (b * x ^ 2) = ∑ a, (quadraticChar F (b * a) : R) * ψ a := by
    simp only [sum_comp_mul_sq hF hb ψ, zsmul_eq_mul, Int.cast_add, Int.cast_one, add_mul, one_mul,
      sum_add_distrib, hsum, zero_add]
  have h1 := htwist 1 one_ne_zero
  simp only [one_mul] at h1
  rw [htwist c hc, h1, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [map_mul, Int.cast_mul, mul_assoc]

end TauCeti
