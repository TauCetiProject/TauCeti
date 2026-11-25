/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# The order of a finite field and the integers invertible in it

A finite field `K` has `q = p ^ k` elements, where `p` is its characteristic. An integer `n` is
nonzero in `K` exactly when `p ∤ n`, so `q` and `n` are then coprime. This is the form in which the
order `q` of a residue field enters arguments about torsion of order prime to the residue
characteristic: multiplication by `q` is injective on such torsion.

## Main results

* `TauCeti.FiniteField.natCard_coprime_of_natCast_ne_zero`: if `(n : K) ≠ 0`, then `Nat.card K`
  and `n` are coprime.
* `TauCeti.FiniteField.odd_card_of_not_isSquare`: a finite field with a nonsquare has odd order.
* `TauCeti.FiniteField.ringChar_ne_two_of_odd_card`: a finite field of odd order does not have
  characteristic two.
* `TauCeti.FiniteField.ne_zero_or_two_ne_zero_of_forall_sq_ne`: over a finite field, a quadratic
  `X² - t X - n` without roots is separable, that is `t ≠ 0` or `2 ≠ 0`.
* `TauCeti.FiniteField.card_sub_one_dvd_card_sub_one`: in a finite extension `F'/F` of finite
  fields, `#F - 1 ∣ #F' - 1`.
* `TauCeti.FiniteField.card_div_two_eq_mul_card_div_two`: in a finite extension `F'/F` of finite
  fields of odd order, `#F' / 2 = ((#F' - 1) / (#F - 1)) * (#F / 2)`.
-/

public section

namespace TauCeti.FiniteField

/-- **The order of a finite field is prime to every integer nonzero in it.** If `(n : K) ≠ 0` in a
finite field `K`, then `Nat.card K = p ^ k` and `n` are coprime, `p` being the characteristic. -/
theorem natCard_coprime_of_natCast_ne_zero {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hn : (n : K) ≠ 0) : (Nat.card K).Coprime n := by
  let := Fintype.ofFinite K
  obtain ⟨k, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard]
  exact Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.2 fun h ↦ hn ((ringChar.spec K n).2 h))

variable {F : Type*} [Field F] [Finite F]

/-- The cardinality of a finite field in which some element is not a square is odd, since in
characteristic two every element is a square. -/
theorem odd_card_of_not_isSquare {r : F} (hr : ¬IsSquare r) : Odd (Nat.card F) := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact FiniteField.odd_card_of_char_ne_two fun h ↦ hr (FiniteField.isSquare_of_char_two h r)

/-- In a finite field of odd cardinality the characteristic is not `2`. -/
theorem ringChar_ne_two_of_odd_card (hodd : Odd (Nat.card F)) : ringChar F ≠ 2 := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hodd
  intro h
  simp [FiniteField.even_card_of_char_two h] at hodd

/-- **An irreducible quadratic over a finite field is separable.** If `X² - t X - n` has no root
in the finite field `F`, then `t ≠ 0` or `2 ≠ 0`: in characteristic `2` every element is a square,
so `X² - n` has a root. -/
theorem ne_zero_or_two_ne_zero_of_forall_sq_ne {t n : F} (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) :
    t ≠ 0 ∨ (2 : F) ≠ 0 := by
  by_contra! h
  let := Fintype.ofFinite F
  have : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h.2
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨x, hx⟩ := FiniteField.isSquare_of_char_two hchar n
  exact hirr x (by rw [h.1, hx, sq]; ring)

/-! ### The order of a finite field extension -/

section Extension

variable {F F' : Type*} [Field F] [Field F'] [Finite F'] [Algebra F F']

variable (F F') in
/-- In a finite extension `F'/F` of finite fields, `#F - 1` divides `#F' - 1`, since
`#F' = #F ^ [F' : F]`. -/
theorem card_sub_one_dvd_card_sub_one : Nat.card F - 1 ∣ Nat.card F' - 1 := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  rw [Module.natCard_eq_pow_finrank (K := F) (V := F')]
  exact Nat.sub_one_dvd_pow_sub_one _ _

/-- In a finite extension `F'/F` of finite fields of odd order, the integer `#F' / 2` is
`((#F' - 1) / (#F - 1)) * (#F / 2)`: raising to the power `#F / 2` after the norm, which is the
power `(#F' - 1) / (#F - 1)`, is raising to the power `#F' / 2`. -/
theorem card_div_two_eq_mul_card_div_two (hF : Odd (Nat.card F)) :
    Nat.card F' / 2 = (Nat.card F' - 1) / (Nat.card F - 1) * (Nat.card F / 2) := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  have hF' : Odd (Nat.card F') := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := F')]
    exact hF.pow
  have hdiv2 {k : ℕ} (hk : Odd k) : k / 2 = (k - 1) / 2 := by obtain ⟨c, rfl⟩ := hk; omega
  rw [hdiv2 hF, hdiv2 hF', mul_comm, Nat.div_mul_right_comm (Nat.Odd.sub_odd hF odd_one).two_dvd,
    Nat.mul_div_cancel' (card_sub_one_dvd_card_sub_one F F')]

end Extension

end TauCeti.FiniteField
