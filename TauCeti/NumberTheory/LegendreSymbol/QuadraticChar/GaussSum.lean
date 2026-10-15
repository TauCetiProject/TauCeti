/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Twisting quadratic exponential sums by the quadratic character

Let `F` be a finite field of odd characteristic, `χ` its quadratic character and `ψ` a primitive
additive character of `F`. For `c ≠ 0`, the quadratic exponential sum `∑_x ψ(c x²)` is
`χ(c) ∑_x ψ(x²)`. Grouping the terms by `a = x²`, whose number of square roots is `χ(a) + 1`,
turns the sum into `∑_a χ(a) ψ(c a)`, the Gauss sum of `χ` against the shifted character; the
substitution `a ↦ c a` then extracts the factor `χ(c)`.

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
  -- Grouping by the value `a = x²` weights `ψ (c * a)` by `#{x | x² = a} = χ a + 1`.
  have hfib (b : F) : ∑ x, ψ (b * x ^ 2) = ∑ a, (quadraticChar F a + 1 : ℤ) * ψ (b * a) := by
    rw [← sum_fiberwise univ (fun x : F ↦ x ^ 2) (fun x ↦ ψ (b * x ^ 2))]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [sum_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2], sum_const, nsmul_eq_mul,
      ← quadraticChar_card_sqrts hF a, Set.toFinset_ofPred]
    push_cast
    rfl
  have hsum (b : F) (hb : b ≠ 0) : ∑ a, ψ (b * a) = 0 := by
    simpa [mul_comm, hb] using AddChar.sum_mulShift b hψ
  have htwist (b : F) (hb : b ≠ 0) :
      ∑ x, ψ (b * x ^ 2) = ∑ a, (quadraticChar F a : R) * ψ (b * a) := by
    rw [hfib]
    simp only [Int.cast_add, Int.cast_one, add_mul, one_mul, sum_add_distrib, hsum b hb, add_zero]
  have h1 : ∑ x, ψ (x ^ 2) = ∑ a, (quadraticChar F a : R) * ψ a := by
    simpa only [one_mul] using htwist 1 one_ne_zero
  rw [htwist c hc, h1, mul_sum]
  -- Substitute `b = c * a`; then `χ c * χ b = χ c ^ 2 * χ a = χ a`.
  refine Fintype.sum_bijective (c * ·) (mulLeft_bijective₀ c hc) _ _ fun a ↦ ?_
  rw [map_mul (quadraticChar F) c a, Int.cast_mul, ← mul_assoc, ← mul_assoc, ← Int.cast_mul, ← sq,
    quadraticChar_sq_one hc, Int.cast_one, one_mul]

end TauCeti
