/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Quadratic exponential sums and the quadratic character

Let `F` be a finite field of odd characteristic with `q` elements, `χ` its quadratic character and
`ψ` a nontrivial additive character of `F`. For `c ≠ 0`, the quadratic exponential sum
`∑_x ψ(c x²)` is `χ(c) ∑_x ψ(x²)`. Grouping the terms by `a = c x²`, which has `1 + χ(c a)`
preimages `x`, turns the sum into `∑_a χ(c a) ψ(a)`, since `ψ` sums to zero; multiplicativity of
`χ` then extracts the factor `χ(c)` from this Gauss sum of `χ`.

This is how the quadratic Gauss sums of a finite field with an arbitrary nonzero coefficient are
reduced to the one with coefficient `1`, which is the Gauss sum `g(χ, ψ)`. Its square is
`χ(-1) q`. The file also records `∑_a χ(a) ψ(a b) = χ(b) ∑_x ψ(x²)` and the
character sum `∑_x χ(c - x²) = -χ(-1)` for `c ≠ 0`, the inputs of Ghosh and Sarnak's point
counts on Markoff surfaces over `𝔽_p`.

## Main results

* `TauCeti.sum_addChar_mul_sq`: `∑_x ψ(c x²) = χ(c) ∑_x ψ(x²)` for `c ≠ 0`.
* `TauCeti.sum_addChar_sq_eq_gaussSum`: `∑_x ψ(x²) = g(χ, ψ)`.
* `TauCeti.sum_addChar_sq_sq`: `(∑_x ψ(x²))² = χ(-1) q`.
* `TauCeti.sum_quadraticChar_mul_addChar_mul`: `∑_a χ(a) ψ(a b) = χ(b) ∑_x ψ(x²)`.
* `TauCeti.sum_quadraticChar_sub_sq`: `∑_x χ(c - x²) = -χ(-1)` for `c ≠ 0`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 6.
* A. Ghosh and P. Sarnak, *Integral points on Markoff type cubic surfaces*, §6, proof of
  Lemma 6.4.
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

variable {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R] [IsDomain R]

/-- **The quadratic exponential sum is a Gauss sum**: for a nontrivial additive character `ψ` of a
finite field of odd characteristic, `∑_x ψ(x²) = g(χ, ψ)`, with the quadratic character `χ` read
in `R`. -/
theorem sum_addChar_sq_eq_gaussSum (hF : ringChar F ≠ 2) {ψ : AddChar F R} (hψ : ψ ≠ 1) :
    ∑ x, ψ (x ^ 2) = gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom R)) ψ := by
  -- Group `x` by `a = x²`, which has `1 + χ(a)` preimages, and use `∑_a ψ(a) = 0`.
  have h := sum_comp_mul_sq hF one_ne_zero fun a ↦ ψ a
  simp only [one_mul, zsmul_eq_mul, Int.cast_add, Int.cast_one, add_mul, sum_add_distrib,
    AddChar.sum_eq_zero_of_ne_one hψ, zero_add] at h
  rw [h, gaussSum]
  simp only [MulChar.ringHomComp_apply, eq_intCast]

/-- **The square of the quadratic Gauss sum**: for a nontrivial additive character `ψ` of a
finite field of odd characteristic, `(∑_x ψ(x²))² = χ(-1) q`. -/
theorem sum_addChar_sq_sq (hF : ringChar F ≠ 2) {ψ : AddChar F R} (hψ : ψ ≠ 1) :
    (∑ x, ψ (x ^ 2)) ^ 2 = quadraticChar F (-1) * Fintype.card F := by
  rcases eq_or_ne (ringChar R) 2 with hR | hR
  · -- In characteristic `2`, `χ` reads as `1` off `0`, so both sides are `1`.
    have : CharP R 2 := ringChar.of_eq hR
    have hχ1 {a : F} (ha : a ≠ 0) : (quadraticChar F a : R) = 1 := by
      rcases quadraticChar_dichotomy ha with h | h <;> simp [h, CharTwo.neg_eq]
    have h0 := AddChar.sum_eq_zero_of_ne_one hψ
    rw [← add_sum_erase _ _ (mem_univ 0), AddChar.map_zero_eq_one, add_comm,
      ← eq_neg_iff_add_eq_zero] at h0
    have hS : ∑ x, ψ (x ^ 2) = -1 := by
      rw [sum_addChar_sq_eq_gaussSum hF hψ, gaussSum, ← add_sum_erase _ _ (mem_univ 0), ← h0]
      simp only [MulChar.ringHomComp_apply, eq_intCast, quadraticChar_zero, Int.cast_zero,
        zero_mul, zero_add]
      exact sum_congr rfl fun a ha ↦ by rw [hχ1 (ne_of_mem_erase ha), one_mul]
    obtain ⟨k, hk⟩ := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)
    rw [hS, hχ1 (neg_ne_zero.mpr one_ne_zero), hk]
    simp [CharTwo.two_eq_zero]
  have hχ : (quadraticChar F).ringHomComp (Int.castRingHom R) ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hF
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [MulChar.ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one] using
      Ring.neg_one_ne_one_of_char_ne_two hR
  rw [sum_addChar_sq_eq_gaussSum hF hψ, gaussSum_sq hχ ((quadraticChar_isQuadratic F).comp _)
    (AddChar.IsPrimitive.of_ne_one hψ), MulChar.ringHomComp_apply, eq_intCast]

/-- For a nontrivial additive character `ψ` of a finite field of odd characteristic and every
`b`, `∑_a χ(a) ψ(a b) = χ(b) ∑_x ψ(x²)`. -/
theorem sum_quadraticChar_mul_addChar_mul (hF : ringChar F ≠ 2) {ψ : AddChar F R} (hψ : ψ ≠ 1)
    (b : F) :
    ∑ a, (quadraticChar F a : R) * ψ (a * b) = quadraticChar F b * ∑ x, ψ (x ^ 2) := by
  rcases eq_or_ne b 0 with rfl | hb
  · -- Both sides vanish, since `∑_a χ(a) = 0` and `χ(0) = 0`.
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, quadraticChar_zero, Int.cast_zero,
      zero_mul]
    rw [← Int.cast_sum, quadraticChar_sum_zero hF, Int.cast_zero]
  -- `χ(b) g(χ, ψ_b) = g(χ, ψ)` for the shift `ψ_b(x) = ψ(b x)`, and `χ(b)² = 1`.
  have h := gaussSum_mulShift ((quadraticChar F).ringHomComp (Int.castRingHom R)) ψ
    (Units.mk0 b hb)
  simp only [Units.val_mk0, gaussSum, AddChar.mulShift_apply, MulChar.ringHomComp_apply,
    eq_intCast] at h
  have hb2 : (quadraticChar F b : R) * quadraticChar F b = 1 := by
    rw [← Int.cast_mul, ← sq, quadraticChar_sq_one hb, Int.cast_one]
  rw [sum_addChar_sq_eq_gaussSum hF hψ, gaussSum]
  simp only [MulChar.ringHomComp_apply, eq_intCast]
  rw [← h, ← mul_assoc, hb2, one_mul]
  simp_rw [mul_comm _ b]

omit [CommRing R] [IsDomain R] in
/-- For `c ≠ 0` in a finite field of odd characteristic, `∑_x χ(c - x²) = -χ(-1)`. -/
theorem sum_quadraticChar_sub_sq (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) :
    ∑ x : F, quadraticChar F (c - x ^ 2) = -quadraticChar F (-1) := by
  -- Group `x` by `u = x²`: the sum is `∑_u (1 + χ(u)) χ(c - u) = ∑_u χ(u (c - u))`.
  have h := sum_comp_mul_sq hF one_ne_zero fun u ↦ quadraticChar F (c - u)
  simp only [one_mul, smul_eq_mul, add_mul, sum_add_distrib] at h
  have h0 : ∑ u : F, quadraticChar F (c - u) = 0 :=
    (Equiv.sum_comp (Equiv.subLeft c) (quadraticChar F)).trans (quadraticChar_sum_zero hF)
  have h1 := sum_quadraticChar_mul_sub hF c
  rw [ite_eq_right hc] at h1
  simp_rw [h, h0, zero_add, ← map_mul, h1, mul_neg_one]

end TauCeti
