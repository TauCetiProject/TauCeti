/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Gauss and Jacobi sums of a cubic character

Let `χ` be a multiplicative character of order `3` on a finite field `F` with `q` elements, with
values in an integral domain, and let `ψ` be a primitive additive character of `F`. Then
`χ (-1) = 1`, since `-1` has order dividing `2`
(Mathlib's `MulChar.val_neg_one_eq_one_of_odd_order`), and Mathlib's
`gaussSum_pow_eq_prod_jacobiSum` specialises to `g(χ, ψ) ^ 3 = q * J(χ, χ)`. This
identity expresses the Jacobi sum `J(χ, χ)` through Gauss sums, and is the input both for the
congruence of `J(χ, χ)` modulo `3` and for the identification of `J(χ, χ)` with a primary prime of
`ℤ[ω]` used in cubic reciprocity.

## Main results

* `TauCeti.gaussSum_pow_three_eq_card_mul_jacobiSum`: `g(χ, ψ) ^ 3 = q * J(χ, χ)`.
* `TauCeti.three_dvd_jacobiSum_add_one`: `J(χ, χ) ≡ -1 (mod 3)`. Modulo `3` cubing is additive,
  so `g(χ, ψ) ^ 3 ≡ g(χ ^ 3, ψ ^ 3) = g(1, ψ ^ 3) = -1`; and `q ≡ 1 (mod 3)`, since the order
  of `χ` divides `q - 1`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §3,
  Propositions 8.3.3 and 8.3.4.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, Proposition 3.3
  and Lemma 3.2.
* N. Xu, *Reciprocity Laws*, Propositions 4.7 and 4.8.
-/

public section

namespace TauCeti

variable {F R : Type*} [Field F] [Fintype F] [CommRing R] [IsDomain R]

/-- **The cube of a cubic Gauss sum.** If `χ` is a multiplicative character of order `3` on a
finite field `F` and `ψ` is a primitive additive character of `F`, then
`g(χ, ψ) ^ 3 = #F * J(χ, χ)`. -/
theorem gaussSum_pow_three_eq_card_mul_jacobiSum {χ : MulChar F R} (hχ : orderOf χ = 3)
    {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = Fintype.card F * jacobiSum χ χ := by
  have h := gaussSum_pow_eq_prod_jacobiSum (hχ ▸ by norm_num : 2 ≤ orderOf χ) hψ
  have h₁ : χ (-1) = 1 :=
    χ.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (hχ ▸ pow_orderOf_eq_one χ)
  simpa [hχ, h₁] using h

/-- **The Jacobi sum of a cubic character is `-1` modulo `3`.** If `χ` is a multiplicative
character of order `3` on a finite field `F`, with values in an integral domain `R` that also
carries a primitive additive character of `F`, then `J(χ, χ) ≡ -1 (mod 3)` in `R`. -/
theorem three_dvd_jacobiSum_add_one {χ : MulChar F R} (hχ : orderOf χ = 3) {ψ : AddChar F R}
    (hψ : ψ.IsPrimitive) : (3 : R) ∣ jacobiSum χ χ + 1 := by
  have h33 : ((3 : ℕ) : R) = 3 := Nat.cast_ofNat
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact (h33 ▸ h3).dvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := CharP.quotient R 3 h3
  let mk := Ideal.Quotient.mk (Ideal.span {((3 : ℕ) : R)})
  have h3Q : (3 : R ⧸ Ideal.span {((3 : ℕ) : R)}) = 0 := by
    rw [← map_ofNat mk 3, Ideal.Quotient.eq_zero_iff_dvd, h33]
  -- The order of `χ` divides `q - 1`, so `q ≡ 1 (mod 3)` and `3` is invertible in `F`.
  have hq : 3 ∣ Fintype.card F - 1 := hχ ▸ χ.orderOf_dvd_card_sub_one
  have hqmk : mk (Fintype.card F : R) = 1 := by
    obtain ⟨k, hk⟩ := hq
    rw [map_natCast, ← Nat.sub_add_cancel (Fintype.card_pos (α := F)), hk]
    push_cast
    rw [h3Q, zero_mul, zero_add]
  have h3F : ((3 : ℕ) : F) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := hq
    have hk' : ((Fintype.card F - 1 : ℕ) : F) = 0 := by
      rw [hk, Nat.cast_mul, h, zero_mul]
    rw [Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub,
      neg_eq_zero] at hk'
    exact one_ne_zero hk'
  have hψ3 : ψ ^ 3 ≠ 1 := by
    rw [AddChar.pow_mulShift]
    exact hψ h3F
  -- Cubing is additive modulo `3`, so `q * J(χ, χ) = g(χ, ψ) ^ 3 ≡ g(χ ^ 3, ψ ^ 3) = -1`.
  have hfrob : mk (gaussSum χ ψ ^ 3) = mk (gaussSum (χ ^ 3) (ψ ^ 3)) := by
    rw [gaussSum, gaussSum, map_pow, map_sum, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← map_pow, mul_pow, MulChar.pow_apply' χ three_ne_zero, AddChar.pow_apply]
  have hχ3 : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  rw [hχ3, gaussSum_one_left hψ3,
    gaussSum_pow_three_eq_card_mul_jacobiSum hχ hψ, map_mul, hqmk, one_mul, map_neg,
    map_one] at hfrob
  rw [← h33, ← Ideal.Quotient.eq_zero_iff_dvd, map_add, hfrob, map_one, neg_add_cancel]

end TauCeti
