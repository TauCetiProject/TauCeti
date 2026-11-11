/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.RingTheory.IntegralDomain
import TauCeti.FieldTheory.Finite.Card
import TauCeti.GroupTheory.SpecificGroups.Cyclic.PowMonoidHom

/-!
# Euler's criterion for `n`-th powers in a finite field

Let `F` be a finite field with `q` elements and `n ∣ q - 1`. A nonzero `a ∈ F` is an `n`-th power
exactly when `a ^ ((q - 1) / n) = 1`. At `n = 2` this is Mathlib's `FiniteField.isSquare_iff`
(in odd characteristic).

## Main results

* `TauCeti.FiniteField.exists_pow_eq_iff_pow_card_sub_one_div_eq_one`: Euler's criterion for
  `n`-th powers in a finite field.
* `TauCeti.FiniteField.pow_card_div_two_eq_neg_one`: a nonsquare `r` satisfies
  `r ^ (#F / 2) = -1`.
* `TauCeti.Int.dvd_pow_mul_pow_div_two_add`: for a prime `p` modulo which `r` is not a square and
  every integer `v`, `p ∣ v ^ p r ^ ((p - 1) / 2) + v`.
-/

public section

namespace TauCeti.FiniteField

/-- **Euler's criterion in a finite field.** If `n ∣ #F - 1`, then a nonzero `a ∈ F` is an `n`-th
power exactly when `a ^ ((#F - 1) / n) = 1`. -/
theorem exists_pow_eq_iff_pow_card_sub_one_div_eq_one {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : n ∣ Nat.card F - 1) {a : F} (ha : a ≠ 0) :
    (∃ b, b ^ n = a) ↔ a ^ ((Nat.card F - 1) / n) = 1 := by
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units _
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    have := Nat.eq_zero_of_zero_dvd hn
    omega
  -- Euler's criterion in the cyclic group `Fˣ` of order `#F - 1`.
  have h := IsCyclic.mem_range_powMonoidHom_iff n (Units.mk0 _ ha)
  rw [hcard, Nat.gcd_eq_right hn, ← Units.val_eq_one, Units.val_pow_eq_pow_val, Units.val_mk0] at h
  rw [← h]
  constructor
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact ha (by rw [← hb, zero_pow hn0])
    exact ⟨Units.mk0 b hb0, Units.ext (by simp [hb])⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa using congrArg Units.val hb⟩

/-- **Euler's criterion for a nonsquare.** In a finite field `F`, a nonsquare `r` satisfies
`r ^ (#F / 2) = -1`. -/
theorem pow_card_div_two_eq_neg_one {F : Type*} [Field F] [Finite F] {r : F}
    (hr : ¬IsSquare r) : r ^ (Nat.card F / 2) = -1 := by
  have := Fintype.ofFinite F
  have hF := ringChar_ne_two_of_odd_card (odd_card_of_not_isSquare hr)
  have hr0 : r ≠ 0 := by rintro rfl; exact hr .zero
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.pow_dichotomy hF hr0).resolve_left
    fun h ↦ hr ((FiniteField.isSquare_iff hF hr0).mpr h)

end TauCeti.FiniteField

namespace TauCeti.Int

/-- **Euler's criterion times `v`.** For a prime `p` modulo which the integer `r` is not a square
and every integer `v`, `p ∣ v ^ p r ^ ((p - 1) / 2) + v`: by Fermat `v ^ p ≡ v` and by Euler's
criterion `r ^ ((p - 1) / 2) ≡ -1`, the exponent being written `p / 2`. For `p ∤ v` this is Euler's
criterion for `r` itself. -/
theorem dvd_pow_mul_pow_div_two_add {p : ℕ} [Fact p.Prime] {r : ℤ}
    (hr : ¬IsSquare (r : ZMod p)) (v : ℤ) : (p : ℤ) ∣ v ^ p * r ^ (p / 2) + v := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := TauCeti.FiniteField.pow_card_div_two_eq_neg_one hr
  rw [Nat.card_zmod] at h
  push_cast
  rw [ZMod.pow_card, h, mul_neg_one, neg_add_cancel]

end TauCeti.Int
