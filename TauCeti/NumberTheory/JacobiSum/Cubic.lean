/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Gauss and Jacobi sums of a cubic character

Let `χ` be a multiplicative character of order `3` on a finite field `F` with `q` elements, with
values in an integral domain, and let `ψ` be a primitive additive character of `F`. Then
`χ (-1) = 1`, since `-1` has order dividing `2`
(Mathlib's `MulChar.val_neg_one_eq_one_of_odd_order`), and Mathlib's
`gaussSum_pow_eq_prod_jacobiSum` specialises to `g(χ, ψ) ^ 3 = q * J(χ, χ)`. This
identity expresses the Jacobi sum `J(χ, χ)` through Gauss sums, and is an input for the
identification of `J(χ, χ)` with a primary prime of `ℤ[ω]` used in cubic reciprocity. Independently
of Gauss sums, `J(χ, χ)` is congruent to `-1` modulo `3`.

## Main results

* `TauCeti.gaussSum_pow_three_eq_card_mul_jacobiSum`: `g(χ, ψ) ^ 3 = q * J(χ, χ)`.
* `TauCeti.three_dvd_jacobiSum_add_one`: `J(χ, χ) ≡ -1 (mod 3)`. This is Mathlib's
  `exists_jacobiSum_eq_neg_one_add` for `n = 3`, which gives `J(χ, χ) ≡ -1 (mod (μ - 1) ^ 2)`
  for a primitive cube root of unity `μ`, here a value of `χ`; and `(μ - 1) ^ 2 = -3 μ`.

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
character of order `3` on a finite field `F`, with values in an integral domain `R`, then
`J(χ, χ) ≡ -1 (mod 3)` in `R`. -/
theorem three_dvd_jacobiSum_add_one {χ : MulChar F R} (hχ : orderOf χ = 3) :
    (3 : R) ∣ jacobiSum χ χ + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hχ3 : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  -- A value `μ = χ a ≠ 1` of `χ` is a primitive cube root of unity.
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    simp at hχ
  obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hχ1
  have hμ : IsPrimitiveRoot (χ a) 3 := by
    refine IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime ?_ ha)
    rw [← MulChar.pow_apply' χ three_ne_zero, hχ3, MulChar.one_apply_coe]
  obtain ⟨z, -, hz⟩ := exists_jacobiSum_eq_neg_one_add (by norm_num) hχ3 hχ3
    (hχ ▸ χ.orderOf_dvd_card_sub_one) hμ
  -- `μ ^ 2 + μ + 1 = 0`, so `J(χ, χ) + 1 = z * (μ - 1) ^ 2 = -3 * z * μ`.
  have h := hμ.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  exact ⟨-z * χ a, by rw [hz]; linear_combination z * h⟩

end TauCeti
